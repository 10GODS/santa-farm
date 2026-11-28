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
    """Level-1 closure + level-2 target-anchored routes. Returns recipe list."""
    sv = puzzle["sv"]
    L = puzzle["L"]
    values = set(sv)
    rec = []
    seen = set()
    for op, a, b, v in recs:
        values.add(v)
        r = (op, a, b, v)
        if r not in seen:
            seen.add(r)
            rec.append(r)
    vals = sorted(values)
    # level 1: fresh one-op values from known values
    level1 = {}
    for i, a in enumerate(vals):
        for b in vals[i:]:
            s = a + b
            if s <= L and s not in level1:
                level1[s] = ("+", a, b)
            m = a * b
            if m <= L and m not in level1:
                level1[m] = ("*", a, b)
            if b > a and (b - a) not in level1:
                level1[b - a] = ("-", b, a)
            if a and b % a == 0 and b != a and (b // a) not in level1:
                level1[b // a] = ("/", b, a)
            if len(level1) >= extra_cap:
                break
        if len(level1) >= extra_cap:
            break
    for v, (op, a, b) in level1.items():
        r = (op, a, b, v)
        if r not in seen:
            seen.add(r)
            rec.append(r)
    values |= set(level1)
    # level 2: target-anchored 2-step routes
    uni = sorted(values)
    for t in puzzle["tg"]:
        if t in sv:
            continue
        for d in uni:
            if d <= 0:
                continue
            cands = []
            if t > d:
                cands.append(("+", t - d, d))
            if d > t and (d - t) in values:
                cands.append(("-", d - t, d))
            if t % d == 0:
                cands.append(("*", t // d, d))
            if d % t == 0:
                cands.append(("/", d // t, d))
            for op, y, dd in cands:
                if y > 0 and y in values:
                    r = (op, y, dd, t)
                    if r not in seen:
                        seen.add(r)
                        rec.append(r)
                    break
    return rec


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


def solve(pid, puzzle, spec, secs, extra_cap, workers):
    sv = puzzle["sv"]
    tg = puzzle["tg"]
    L = puzzle["L"]
    R = puzzle["R"]
    n0 = spec["n0"]
    svset = set(sv)
    recs = expand(puzzle, spec["rec"], extra_cap)
    by_value = {}
    for op, a, b, v in recs:
        if v in svset:
            continue
        if op == "/" and (b == 0 or a % b):
            continue
        by_value.setdefault(v, []).append((op, a, b))
    need = [t for t in tg if t not in svset]
    if not need:
        return None
    for t in need:
        if t not in by_value:
            return None
    m = cp_model.CpModel()
    values = sorted(by_value)
    if len(values) > 40000:
        return None
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
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(secs)
    solver.parameters.num_search_workers = workers
    st = solver.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None
    chosen = [v for v in values if solver.Value(x[v])]
    if len(chosen) >= n0:
        return None
    sel_recipe = {}
    for v in chosen:
        picked = None
        for k, (op, a, b) in enumerate(by_value[v]):
            if solver.Value(y[(v, k)]) == 1:
                picked = (op, a, b)
                break
        if picked is None:
            return None
        sel_recipe[v] = picked
    prog = schedule(set(chosen), sel_recipe, sv, R, tg)
    if prog is None or len(prog) >= n0:
        return None
    if not replay_ok(sv, tg, L, R, prog):
        return None
    return prog


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
    items = sorted(slim.items(), key=lambda kv: -kv[1]["n0"])
    items = [kv for i, kv in enumerate(items) if i % args.nshard == args.shard]
    wins = {}
    t0 = time.time()
    for pid, spec in items:
        if time.time() - t0 > args.budget:
            break
        try:
            prog = solve(pid, puzzles[pid], spec, args.secs, args.extra, args.workers)
        except Exception:
            prog = None
        if prog:
            wins[pid] = prog
            print(f"{pid} WIN {len(prog)} (was {spec['n0']})", flush=True)
            with open(args.out, "w") as f:
                json.dump(wins, f)
    with open(args.out, "w") as f:
        json.dump(wins, f)
    print(f"shard {args.shard}: {len(wins)} wins -> {args.out}", flush=True)


if __name__ == "__main__":
    main()
