"""OUR OWN CP-SAT deep-closure engine (runs on farm shards / locally).

Slim payload gives the derivations already known for each puzzle; this script
expands the universe LOCALLY:

  level 0 : bank derivations (union over all validated variants)
  level 1 : every value obtainable in one op from a level-0 value  (fresh packets)
  level 2 : target-anchored two-step routes  t = op(y, d)

CP-SAT then chooses a minimum-cardinality subset of values covering every
target, with acyclicity (level) constraints, and we schedule the result into
48 registers with a liveness-aware allocator. A candidate is kept only if it
is shorter than the incumbent AND passes an independent replay check.

This is the only mechanism we have that can reach values OUTSIDE the one-step
closure of the frontier's own value set — which our CP-SAT proof showed is the
only remaining degree of freedom.

Usage: python farm_cpsat.py --shard 0 --nshard 20 --secs 30 --out wins.json
"""
import argparse, gzip, json, os, sys, time

try:
    from ortools.sat.python import cp_model
except ModuleNotFoundError:
    print("ERROR: ortools not installed", file=sys.stderr)
    raise

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def load_puzzles(path):
    import csv
    out = {}
    for r in csv.DictReader(open(path, newline="")):
        out[r["id"]] = dict(
            sv=json.loads(r["starting_values"]),
            tg=json.loads(r["targets"]),
            L=int(r["value_limit"]),
            R=int(r["registers"]),
        )
    return out


def replay_ok(sv, tg, L, R, prog):
    regs = [None] * R
    regs[: len(sv)] = list(sv)
    need = set(tg) - set(sv)
    for op, i, j, d in prog:
        if not (0 <= i < R and 0 <= j < R and 0 <= d < R):
            return False
        a, b = regs[i], regs[j]
        if a is None or b is None:
            return False
        if op == "/" and (b == 0 or a % b):
            return False
        v = a + b if op == "+" else a - b if op == "-" else a * b if op == "*" else a // b
        if not 1 <= v <= L:
            return False
        regs[d] = v
        need.discard(v)
    return not need


def expand(puzzle, recs, extra_cap):
    """Backward, target-anchored construction universe with SHARED-VALUE DETECTION.

Why this shape: a CP-SAT run over the frontier's own value set (plus the full
one-step closure of it) returned OPTIMAL == the incumbent length on every
puzzle we measured, so nothing there can be improved. The only way out is a
value the frontier never produced. We therefore work backward from targets:

    t  =  y op d        (y intermediate, d any known value)

and we look for the case where ONE y serves SEVERAL targets:

    t1 = y + d1 ,  t2 = y + d2   =>  t1 - t2 = d1 - d2
    t1 = y * d1 ,  t2 = y * d2   =>  t1*d2 = t2*d1

Such a y is a genuinely new value with two consumers: it pays for itself only
if it is reachable in ONE step from known values, otherwise it costs as much as
it saves. We therefore require a one-step derivation for y and let CP-SAT trade
the whole thing off against the incumbent's per-target chains.

Returns a recipe list of (op, a, b, v).
"""
    sv = puzzle["sv"]
    L = puzzle["L"]
    svset = set(sv)
    values = set(sv)
    rec = []
    seen = set()
    for op, a, b, v in recs:
        values.add(v)
        r = (op, a, b, v)
        if r not in seen:
            seen.add(r)
            rec.append(r)
    V0 = sorted(values)
    vset = set(V0)

    def prod1(v):
        """one-step derivation of v from two known values, or None"""
        if v in vset:
            return None
        for a in V0:
            if a <= 0:
                continue
            if v - a in vset and v - a > 0:
                return ("+", a, v - a)
            if a <= v and v % a == 0 and a != v and (v // a) in vset:
                return ("*", a, v // a)
            if (v + a) in vset:
                return ("-", v + a, a)
            if a != 0 and (v * a) in vset:
                return ("/", v * a, a)
        return None

    def prod2(v):
        """two-step derivation: v = x op e, x produced in one step from known."""
        if v in vset:
            return None
        for x in made1c:
            for e in V0:
                if e <= 0:
                    continue
                if x + e == v:
                    return ("+", x, e)
                if x - e == v and x > e:
                    return ("-", x, e)
                if x * e == v and v <= L:
                    return ("*", x, e)
                if e and x % e == 0 and x // e == v:
                    return ("/", x, e)
        return None

    def prod_any(v):
        return prod1(v) or prod2(v)

    tgt = [t for t in puzzle["tg"] if t not in svset]
    tgt_set = set(tgt)
    n_new = 0
    budget = extra_cap

    def add_derivation(v, depth=0):
        """Ensure v has at least one recipe in `rec`.

        Recipes may reference operand values that were never themselves
        produced (that happened with shared intermediates whose partner d was
        only 'cheap to produce', not actually produced). The CP-SAT model then
        failed with KeyError on x[operand] -> the whole puzzle was silently
        dropped as 'no win'. This closure adds the missing derivations.
        """
        if depth > 3 or v in svset or v in vset:
            return
        pr = prod1(v) or prod2(v)
        if pr is None:
            return
        op, a, b = pr
        add_derivation(a, depth + 1)
        add_derivation(b, depth + 1)
        r = (op, a, b, v)
        if r not in seen:
            seen.add(r)
            rec.append(r)
        vset.add(v)

    # one-step values reachable from the frontier (used for two-step derivations)
    made1c = {}
    for i, a in enumerate(V0):
        for b in V0[i:]:
            for v, op in ((a + b, "+"), (a * b, "*"), (b - a if b > a else None, "-")):
                if v is None or v > L or v in vset:
                    continue
                made1c.setdefault(v, (op, a, b))
            if a and b % a == 0 and b != a:
                v = b // a
                if v not in vset:
                    made1c.setdefault(v, ("/", b, a))
        if len(made1c) > 40000:
            break

    # ---- SHARED INTERMEDIATE SEARCH (generalised) ---------------------------
    # A fresh value y that serves TWO OR MORE targets is the only structural
    # saving available: the incumbents pay one instruction per target, while a
    # shared y pays ~one instruction and serves many targets.
    #   t = y + d   =>  d = t - y        t = y - d  =>  d = y - t
    #   t = y * d   =>  d = t / y        t = y / d  =>  d = y / t
    # The partner d must itself be cheap to produce, otherwise sharing does not
    # pay: we accept d in V0 (free, already in the frontier) or d with a
    # two-step derivation, and we require y itself to have a <=2-step
    # derivation. CP-SAT then decides whether the trade is actually worth it.
    def partner_ok(d):
        if d in vset:
            return True
        return prod_any(d) is not None

    consumers = {}
    for t1 in tgt:
        for d in V0:
            if d <= 0:
                continue
            cands = []
            if t1 - d > 0:
                cands.append(t1 - d)
            if t1 + d <= L:
                cands.append(t1 + d)
            if t1 % d == 0:
                cands.append(t1 // d)
            if d % t1 == 0:
                cands.append(d // t1)
            for y in cands:
                if y <= 0 or y > L or y in vset or y in tgt_set:
                    continue
                consumers.setdefault(y, []).append((t1, d))
    shared = []
    for y, lst in consumers.items():
        ts = {}
        for t1, d in lst:
            if t1 in ts:
                continue
            d_add = t1 - y
            d_sub = y - t1
            d_mul = (t1 // y) if (y and t1 % y == 0) else None
            d_div = (y // t1) if (t1 and y % t1 == 0) else None
            legs = None
            if d_add > 0 and partner_ok(d_add):
                legs = [("+", y, d_add)]
            elif d_sub > 0 and partner_ok(d_sub):
                legs = [("-", y, d_sub)]
            elif d_mul is not None and d_mul > 0 and partner_ok(d_mul):
                legs = [("*", y, d_mul)]
            elif d_div is not None and d_div > 0 and partner_ok(d_div):
                legs = [("/", y, d_div)]
            if legs:
                ts[t1] = legs
        if len(ts) < 2:
            continue
        pr = prod_any(y)
        if pr is None:
            continue
        shared.append((y, ts, pr))
        budget -= 1
        if budget <= 0:
            break
    for y, ts, pr in shared:
        op, a, b = pr
        add_derivation(a)
        add_derivation(b)
        rec.append((op, a, b, y))
        for t1, legs in ts.items():
            for (lop, ly, ld) in legs:
                add_derivation(ld)
                rec.append((lop, ly, ld, t1))
        vset.add(y)
        n_new += 1

    # ---- full one-step closure of the frontier's values ----------------------
    # (kept: CP-SAT proved OPTIMAL==incumbent inside it, but it is still the
    #  cheapest source of candidate recipes and it costs nothing to keep)
    level1 = {}
    for i, a in enumerate(V0):
        for b in V0[i:]:
            s = a + b
            if s <= L and s not in level1 and s not in vset:
                level1[s] = ("+", a, b)
            m = a * b
            if m <= L and m not in level1 and m not in vset:
                level1[m] = ("*", a, b)
            if b > a and (b - a) not in level1 and (b - a) not in vset:
                level1[b - a] = ("-", b, a)
            if a and b % a == 0 and b != a and (b // a) not in level1 and (b // a) not in vset:
                level1[b // a] = ("/", b, a)
            if len(level1) >= extra_cap:
                break
        if len(level1) >= extra_cap:
            break
    for v, (op, a, b) in level1.items():
        rec.append((op, a, b, v))
        vset.add(v)
    V1 = sorted(vset)
    # two-step target anchors: t = y op d with y in the closed set
    for t in tgt:
        for d in V1:
            if d <= 0:
                continue
            opts = []
            if t > d and (t - d) in vset:
                opts.append(("+", t - d, d))
            if d > t and (d - t) in vset:
                opts.append(("-", d - t, d))
            if t % d == 0 and (t // d) in vset:
                opts.append(("*", t // d, d))
            if d % t == 0 and (d // t) in vset:
                opts.append(("/", d // t, d))
            for op, y, dd in opts:
                rec.append((op, y, dd, t))
                break

    # ---- shared intermediates ------------------------------------------------
    # map "value produced as t op d" so we can find a y used by >=2 targets
    # additive family: t1 = y + d1 and t2 = y + d2  => d1 - d2 = t1 - t2
    by_diff = {}
    for t1 in tgt:
        for d1 in V0:
            diff = t1 - d1
            by_diff.setdefault(diff, []).append((t1, d1))
    shared_add = []
    for diff, lst in by_diff.items():
        if len(lst) < 2 or budget <= 0:
            continue
        # need two entries with different targets and same diff structure:
        # t1 = y + d1, t2 = y + d2 -> (t1 - d1) == (t2 - d2)  and t1 != t2
        seen_t = set()
        for (t1, d1) in lst:
            if t1 in seen_t:
                continue
            for (t2, d2) in lst:
                if t2 == t1:
                    continue
                y = t1 - d1
                if y != t2 - d2:
                    continue
                if y <= 0 or y > L or y in vset or y in tgt_set:
                    continue
                pr = prod1(y)
                if pr is None:
                    continue
                shared_add.append((y, [(t1, d1), (t2, d2)], pr))
                seen_t.add(t1)
                budget -= 1
                break
    # multiplicative family: t1 = y * d1 and t2 = y * d2
    by_ratio = {}
    for t1 in tgt:
        for d1 in V0:
            r = t1 // d1 if d1 else 0
            if d1 and t1 % d1 == 0:
                by_ratio.setdefault(r, []).append((t1, d1))
    shared_mul = []
    for r, lst in by_ratio.items():
        if len(lst) < 2 or budget <= 0:
            continue
        seen_t = set()
        for (t1, d1) in lst:
            if t1 in seen_t:
                continue
            for (t2, d2) in lst:
                if t2 == t1:
                    continue
                y = t1 // d1
                if y != t2 // d2:
                    continue
                if y <= 0 or y > L or y in vset or y in tgt_set:
                    continue
                pr = prod1(y)
                if pr is None:
                    continue
                shared_mul.append((y, [(t1, d1), (t2, d2)], pr))
                seen_t.add(t1)
                budget -= 1
                break

    for y, legs, pr in shared_add:
        op, a, b = pr
        rec.append((op, a, b, y))
        for t, d in legs:
            rec.append(("+", y, d, t))
        vset.add(y)
        n_new += 1
    for y, legs, pr in shared_mul:
        op, a, b = pr
        rec.append((op, a, b, y))
        for t, d in legs:
            rec.append(("*", y, d, t))
        vset.add(y)
        n_new += 1

    # ---- single-target backward routes --------------------------------------
    # t = y op d, with y produced in one step from known values.
    # These are the depth-2 candidates that do not have a second consumer;
    # they let CP-SAT replace a long per-target chain with a short one.
    for t in tgt:
        if budget <= 0:
            break
        for d in V0:
            if d <= 0:
                break
            opts = []
            if t > d:
                opts.append(("+", t - d, d))
            if d > t:
                opts.append(("-", d - t, d))
            if t % d == 0:
                opts.append(("*", t // d, d))
            if d % t == 0:
                opts.append(("/", d // t, d))
            if t + d <= L:
                opts.append(("-", t + d, d))
            hit = None
            for op, y, dd in opts:
                if 0 < y <= L and y not in vset and y not in tgt_set:
                    pr = prod1(y)
                    if pr:
                        hit = (op, y, dd, pr)
                        break
            if hit:
                op, y, dd, pr = hit
                pop, pa, pb = pr
                add_derivation(pa)
                add_derivation(pb)
                rec.append((pop, pa, pb, y))
                rec.append((op, y, dd, t))
                vset.add(y)
                n_new += 1
                budget -= 1
                break
    return rec, n_new


def schedule(selected, sel_recipe, sv, R, tg):
    deps = {v: [u for u in sel_recipe[v][1:] if u in selected] for v in selected}
    users = {}
    for v, ds in deps.items():
        for u in ds:
            users.setdefault(u, []).append(v)
    indeg = {v: len(deps[v]) for v in selected}
    ready = [v for v in selected if indeg[v] == 0]
    topo = []
    while ready:
        v = ready.pop()
        topo.append(v)
        for u in users.get(v, []):
            indeg[u] -= 1
            if indeg[u] == 0:
                ready.append(u)
    if len(topo) != len(selected):
        return None
    lastpos = {}
    for pos, v in enumerate(topo):
        op, a, b = sel_recipe[v]
        lastpos[a] = max(lastpos.get(a, -1), pos)
        lastpos[b] = max(lastpos.get(b, -1), pos)
        lastpos[v] = pos
    tgt = set(tg)
    reg_of = {}
    for i, v in enumerate(sv):
        reg_of.setdefault(v, i)
    free = set(range(len(sv), R))
    prog = []
    for pos, v in enumerate(topo):
        op, a, b = sel_recipe[v]
        if a not in reg_of or b not in reg_of:
            return None
        ai, bi = reg_of[a], reg_of[b]
        for old in list(reg_of):
            if old in (a, b, v):
                continue
            if lastpos.get(old, -1) <= pos:
                free.add(reg_of.pop(old))
        if v in reg_of:
            d = reg_of[v]
        else:
            d = None
            if free:
                d = min(free)
            else:
                for cand in (a, b):
                    if lastpos.get(cand, -1) == pos and cand not in tgt:
                        d = reg_of.pop(cand)
                        break
            if d is None:
                return None
            free.discard(d)
            reg_of[v] = d
        prog.append([op, ai, bi, d])
    return prog


def solve(pid, puzzle, spec, secs, extra_cap, workers, hint=None):
    sv = puzzle["sv"]
    tg = puzzle["tg"]
    L = puzzle["L"]
    R = puzzle["R"]
    n0 = spec["n0"]
    svset = set(sv)
    recs, n_new = expand(puzzle, spec["rec"], extra_cap)
    by_value = {}
    for op, a, b, v in recs:
        if v in svset:
            continue
        if op == "/" and (b == 0 or a % b):
            continue
        by_value.setdefault(v, []).append((op, a, b))
    need = [t for t in tg if t not in svset]
    if not need:
        return None, None
    for t in need:
        if t not in by_value:
            return None, None
    # safety: drop recipes whose operands were never produced (would raise
    # KeyError in the model and silently lose the whole puzzle)
    for v in list(by_value):
        keep = []
        for r in by_value[v]:
            op, a, b = r
            if (a in svset or a in by_value) and (b in svset or b in by_value):
                keep.append(r)
        if keep:
            by_value[v] = keep
        else:
            del by_value[v]
    for t in need:
        if t not in by_value:
            return None, None
    m = cp_model.CpModel()
    values = sorted(by_value)
    if len(values) > 40000:
        return None, None
    x = {v: m.NewBoolVar(f"x{i}") for i, v in enumerate(values)}
    for t in need:
        m.Add(x[t] == 1)
    y = {}
    for v, lst in by_value.items():
        for k, (op, a, b) in enumerate(lst):
            yy = m.NewBoolVar(f"y{v}_{k}")
            y[(v, k)] = yy
            m.AddImplication(yy, x[v])
            if a not in svset:
                m.AddImplication(yy, x[a])
            if b not in svset:
                m.AddImplication(yy, x[b])
    for v, lst in by_value.items():
        m.Add(sum(y[(v, k)] for k in range(len(lst))) >= 1).OnlyEnforceIf(x[v])
        m.Add(sum(y[(v, k)] for k in range(len(lst))) == 0).OnlyEnforceIf(x[v].Not())
    lvl = {v: m.NewIntVar(0, len(values) + 1, f"l{i}") for i, v in enumerate(values)}
    for v, lst in by_value.items():
        for k, (op, a, b) in enumerate(lst):
            for p in (a, b):
                if p not in svset:
                    m.Add(lvl[v] >= lvl[p] + 1).OnlyEnforceIf(y[(v, k)])
    m.Minimize(sum(x.values()))
    if hint:
        # Warm start from the incumbent program: CP-SAT then begins with a
        # feasible n0-value solution instead of hunting for any feasible one.
        # Without this the solver often returns a WORSE feasible solution than
        # the incumbent (observed: proxy 79 vs incumbent 75) simply because it
        # ran out of time before improving.
        hv, hrec = hint
        for v in hv:
            if v in x:
                m.AddHint(x[v], 1)
        for (v, k) in y:
            want = hrec.get(v)
            if want is not None and by_value[v][k] == want:
                m.AddHint(y[(v, k)], 1)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(secs)
    solver.parameters.num_search_workers = workers
    st = solver.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None, None
    try:
        bound = solver.BestObjectiveBound()
    except Exception:
        bound = None
    chosen = [v for v in values if solver.Value(x[v])]
    proven = (st == cp_model.OPTIMAL) or (bound is not None and bound >= n0 - 1e-6)
    if len(chosen) >= n0:
        return None, {"status": solver.StatusName(st), "bound": bound, "obj": len(chosen),
                      "proven_optimal": bool(proven), "universe": len(values)}
    sel_recipe = {}
    for v in chosen:
        picked = None
        for k, (op, a, b) in enumerate(by_value[v]):
            if solver.Value(y[(v, k)]) == 1:
                picked = (op, a, b)
                break
        if picked is None:
            return None, None
        sel_recipe[v] = picked
    cert = {"status": solver.StatusName(st), "bound": bound, "obj": len(chosen),
            "proven_optimal": bool(proven), "universe": len(values)}
    prog = schedule(set(chosen), sel_recipe, sv, R, tg)
    if prog is None or len(prog) >= n0:
        cert["scheduled"] = None if prog is None else len(prog)
        return None, cert
    cert["scheduled"] = len(prog)
    if not replay_ok(sv, tg, L, R, prog):
        cert["replay_ok"] = False
        return None, cert
    cert["replay_ok"] = True
    return prog, cert


def best_program_hints(best, puzzles):
    """value -> recipe map from the incumbent programs (for CP-SAT warm start).

    The incumbent program already achieves n0 instructions, so hinting the
    model with its values lets the search start INSIDE the incumbent's cost
    instead of from scratch.
    """
    hints = {}
    for pid, prog in best.items():
        p = puzzles.get(pid)
        if not p:
            continue
        regs = list(p["sv"]) + [None] * (p["R"] - len(p["sv"]))
        vals = set()
        rec = {}
        for op, i, j, d in prog:
            a, b = regs[i], regs[j]
            if a is None or b is None:
                break
            if op == "/" and (b == 0 or a % b):
                break
            v = a + b if op == "+" else a - b if op == "-" else a * b if op == "*" else a // b
            regs[d] = v
            vals.add(v)
            rec.setdefault(v, (op, a, b))
        hints[pid] = (vals, rec)
    return hints


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default=os.path.join(HERE, "data", "cpsat_slim.json.gz"))
    ap.add_argument("--puzzles", default=os.path.join(HERE, "data", "puzzles.csv"))
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--nshard", type=int, default=1)
    ap.add_argument("--secs", type=int, default=30)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--extra", type=int, default=6000)
    ap.add_argument("--budget", type=int, default=1500, help="wall-clock seconds for this shard")
    ap.add_argument("--out", default="wins.json")
    args = ap.parse_args()
    with gzip.open(args.data, "rt", encoding="utf-8") as f:
        slim = json.load(f)
    puzzles = load_puzzles(args.puzzles)
    best = {}
    bpath = os.path.join(HERE, "data", "best.csv")
    if os.path.exists(bpath):
        import csv as _csv
        for r in _csv.DictReader(open(bpath, newline="")):
            best[r["id"]] = json.loads(r["program"])
    hints = best_program_hints(best, puzzles)
    items = sorted(slim.items(), key=lambda kv: -kv[1]["n0"])
    items = [kv for i, kv in enumerate(items) if i % args.nshard == args.shard]
    wins = {}
    certs = {}
    t0 = time.time()
    for pid, spec in items:
        if time.time() - t0 > args.budget:
            break
        try:
            prog, cert = solve(pid, puzzles[pid], spec, args.secs, args.extra, args.workers,
                               hint=hints.get(pid))
        except Exception as e:
            import traceback
            traceback.print_exc()
            prog, cert = None, {"status": "EXC:" + type(e).__name__ + ":" + str(e)[:120]}
        if cert:
            certs[pid] = cert
        if prog:
            wins[pid] = prog
            print(f"{pid} WIN {len(prog)} (was {spec['n0']})", flush=True)
            with open(args.out, "w") as f:
                json.dump(wins, f)
    with open(args.out, "w") as f:
        json.dump(wins, f)
    with open(args.out.replace(".json", "_certs.json"), "w") as f:
        json.dump(certs, f)
    nproven = sum(1 for c in certs.values() if c.get("proven_optimal"))
    print(f"shard {args.shard}: {len(wins)} wins, {nproven}/{len(certs)} PROVEN-OPTIMAL -> {args.out}",
          flush=True)


if __name__ == "__main__":
    main()
