"""Diagnostic: report CP-SAT objective vs incumbent for our engine (own method)."""
import gzip, json, sys, time
sys.path.insert(0, '/c/Users/saura/santa-farm'.replace('/c/', 'C:/', 1))
from ortools.sat.python import cp_model
from farm_cpsat import expand, load_puzzles

slim = json.load(gzip.open('C:/Users/saura/santa-farm/data/cpsat_slim.json.gz', 'rt', encoding='utf-8'))
pz = load_puzzles('C:/Users/saura/santa-farm/data/puzzles.csv')
pid = sys.argv[1]
extra = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
secs = int(sys.argv[3]) if len(sys.argv) > 3 else 60
spec = slim[pid]
p = pz[pid]
svset = set(p['sv'])
t0 = time.time()
rec, nn = expand(p, spec['rec'], extra)
by = {}
for op, a, b, v in rec:
    if v in svset:
        continue
    if op == '/' and (b == 0 or a % b):
        continue
    by.setdefault(v, []).append((op, a, b))
need = [t for t in p['tg'] if t not in svset]
m = cp_model.CpModel()
vals = sorted(by)
x = {v: m.NewBoolVar(f"x{i}") for i, v in enumerate(vals)}
for t in need:
    m.Add(x[t] == 1)
y = {}
for v, lst in by.items():
    for k, (op, a, b) in enumerate(lst):
        yy = m.NewBoolVar(f"y_{v}_{k}")
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
s = cp_model.CpSolver()
s.parameters.max_time_in_seconds = secs
s.parameters.num_search_workers = 4
st = s.Solve(m)
print(f"{pid} universe={len(vals)} new_shared={nn} status={s.StatusName(st)} "
      f"obj={s.ObjectiveValue():.0f} bound={s.BestObjectiveBound():.0f} incumbent={spec['n0']} "
      f"t={time.time()-t0:.1f}s")
