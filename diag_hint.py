"""Diagnostic: with a warm start, what does CP-SAT actually PROVE?

Before the warm start the solver sometimes returned a FEASIBLE solution that
was WORSE than the incumbent (proxy 79 vs incumbent 75) simply because it ran
out of time. With hints we should now see either:
  OPTIMAL                 -> proven no shorter program inside the model, or
  FEASIBLE with bound==n0 -> still proven (lower bound equals incumbent)
which is the certificate we want per puzzle.
"""
import csv, gzip, json, sys, time, warnings

warnings.filterwarnings("ignore")
sys.path.insert(0, ".")
from ortools.sat.python import cp_model
from farm_cpsat import expand, load_puzzles, best_program_hints

slim = json.load(gzip.open("data/cpsat_slim.json.gz", "rt", encoding="utf-8"))
pz = load_puzzles("data/puzzles.csv")
best = {}
for r in csv.DictReader(open("data/best.csv", newline="")):
    best[r["id"]] = json.loads(r["program"])
hints = best_program_hints(best, pz)

pid = sys.argv[1]
secs = int(sys.argv[2]) if len(sys.argv) > 2 else 60
spec = dict(slim[pid])
spec["n0"] = len(best[pid])
p = pz[pid]
svset = set(p["sv"])
recs, nn = expand(p, spec["rec"], 6000)
by = {}
for op, a, b, v in recs:
    if v in svset:
        continue
    if op == "/" and (b == 0 or a % b):
        continue
    by.setdefault(v, []).append((op, a, b))
for v in list(by):
    keep = [r for r in by[v]
            if (r[1] in svset or r[1] in by) and (r[2] in svset or r[2] in by)]
    if keep:
        by[v] = keep
    else:
        del by[v]
need = [t for t in p["tg"] if t not in svset]
vals = sorted(by)
m = cp_model.CpModel()
x = {v: m.NewBoolVar(f"x{i}") for i, v in enumerate(vals)}
for t in need:
    m.Add(x[t] == 1)
y = {}
for v, lst in by.items():
    for k, (op, a, b) in enumerate(lst):
        yy = m.NewBoolVar(f"y{v}_{k}")
        y[(v, k)] = yy
        m.AddImplication(yy, x[v])
        if a not in svset:
            m.AddImplication(yy, x[a])
        if b not in svset:
            m.AddImplication(yy, x[b])
for v, lst in by.items():
    m.Add(sum(y[(v, k)] for k in range(len(lst))) >= 1).OnlyEnforceIf(x[v])
    m.Add(sum(y[(v, k)] for k in range(len(lst))) == 0).OnlyEnforceIf(x[v].Not())
lvl = {v: m.NewIntVar(0, len(vals) + 1, f"l{i}") for i, v in enumerate(vals)}
for v, lst in by.items():
    for k, (op, a, b) in enumerate(lst):
        for pp in (a, b):
            if pp not in svset:
                m.Add(lvl[v] >= lvl[pp] + 1).OnlyEnforceIf(y[(v, k)])
m.Minimize(sum(x.values()))
hv, hrec = hints[pid]
for v in hv:
    if v in x:
        m.AddHint(x[v], 1)
for (v, k) in y:
    w = hrec.get(v)
    if w is not None and by[v][k] == w:
        m.AddHint(y[(v, k)], 1)
s = cp_model.CpSolver()
s.parameters.max_time_in_seconds = float(secs)
s.parameters.num_search_workers = 4
t0 = time.time()
st = s.Solve(m)
obj = s.ObjectiveValue()
bnd = s.BestObjectiveBound()
cert = "PROVEN-OPTIMAL" if (st == cp_model.OPTIMAL or (st == cp_model.FEASIBLE and bnd >= spec["n0"] - 1e-6)) else "UNPROVEN"
print(f"{pid} n0={spec['n0']} status={s.StatusName(st)} obj={obj:.0f} bound={bnd:.0f} "
      f"universe={len(vals)} -> {cert}  t={time.time()-t0:.1f}s")
