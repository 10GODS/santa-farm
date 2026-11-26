"""Santa farm worker: compile setwalk, run our shard, referee-gate wins, emit wins.json.
Env: SHARD (0..NSHARD-1), NSHARD, SECS per puzzle, SEED base.
"""
import csv, json, os, subprocess, sys, time, random

OPC = {"+": 0, "-": 1, "*": 2, "/": 3}
IOPS = {0: "+", 1: "-", 2: "*", 3: "/"}
SHARD = int(os.environ.get("SHARD", "0"))
NSHARD = int(os.environ.get("NSHARD", "10"))
SECS = float(os.environ.get("SECS", "30"))
SEED = int(os.environ.get("SEED", "12345")) + SHARD

PZ = {}
for r in csv.DictReader(open("data/puzzles.csv", newline="")):
    PZ[r["id"]] = (json.loads(r["starting_values"]), json.loads(r["targets"]), int(r["value_limit"]), int(r["registers"]))
BEST = {}
for r in csv.DictReader(open("data/best.csv", newline="")):
    BEST[r["id"]] = json.loads(r["program"])

def bank_write(path, ids):
    with open(path, "w") as f:
        for pid in ids:
            sv, tg, L, R = PZ[pid]
            prog = [[OPC[o], i, j, d] for (o, i, j, d) in BEST[pid]]
            f.write(f"P {pid} {L} {R}\nS {len(sv)} {' '.join(map(str, sv))}\n")
            f.write(f"T {len(tg)} {' '.join(map(str, tg))}\n")
            f.write(f"G {len(prog)} " + " ".join(" ".join(map(str, x)) for x in prog) + "\n")

ids = sorted(BEST, key=lambda k: -len(BEST[k]))
mine = [x for i, x in enumerate(ids) if i % NSHARD == SHARD]
bank_write("bank.txt", mine)
open("ids.txt", "w").write("\n".join(mine))

rc = subprocess.run(["g++", "-O3", "-march=native", "-o", "setwalk", "src/setwalk.cpp"], capture_output=True, text=True)
print("compile rc", rc.returncode, rc.stderr[:400], flush=True)
if rc.returncode != 0: sys.exit(1)

def replay_ok(pid, prog):
    sv, tg, L, R = PZ[pid]
    regs = [None]*R; regs[:len(sv)] = sv
    need = set(tg) - set(sv)
    for op, i, j, d in prog:
        if not (0 <= i < R and 0 <= j < R and 0 <= d < R): return False
        a, b = regs[i], regs[j]
        if a is None or b is None: return False
        if op == "/" and (b == 0 or a % b): return False
        v = {"+": lambda: a+b, "-": lambda: a-b, "*": lambda: a*b, "/": lambda: a//b}[op]()
        if not 1 <= v <= L: return False
        regs[d] = v; need.discard(v)
    return not need

env = dict(os.environ); env["SA_SEED"] = str(SEED); env["SW_VARIANTS"] = "data/variants.txt"
wins = {}
t0 = time.time()
CAP = float(os.environ.get("CAP", "1500"))
for rep in range(3):
    out = f"out_{rep}.txt"
    try:
        subprocess.run(["./setwalk", "bank.txt", out, str(SECS), str(rep), "3", "ids.txt", "2"], env=env,
                       timeout=max(50.0, CAP - (time.time()-t0)))
    except subprocess.TimeoutExpired:
        pass
    if not os.path.exists(out): continue
    for line in open(out):
        t = line.split()
        if t and t[0] == "R":
            pid = t[1]; nums = list(map(int, t[3:]))
            prog = [[IOPS[nums[i]], nums[i+1], nums[i+2], nums[i+3]] for i in range(0, len(nums), 4)]
            if len(prog) < len(BEST[pid]) and replay_ok(pid, prog):
                if pid not in wins or len(prog) < len(wins[pid]): wins[pid] = prog
    if time.time() - t0 > CAP: break
json.dump(wins, open("wins.json", "w"))
print("shard", SHARD, "wins", len(wins), "saved", sum(len(BEST[k])-len(v) for k, v in wins.items()), flush=True)
