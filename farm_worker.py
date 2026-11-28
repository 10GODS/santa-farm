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
rc2 = subprocess.run(["g++", "-O3", "-march=native", "-w", "-o", "triwalk", "src/triwalk.cpp"], capture_output=True, text=True)
HAVE_TW = rc2.returncode == 0
print("triwalk compile rc", rc2.returncode, flush=True)

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
if time.time() - t0 > CAP: pass

# ---- stage 2: TRIWALK (cfg rotates by shard) ----
CFGS = ["--cap 1 --T 0.2 --rb 0.6 --deep 0.1", "--cap 1 --T 0.2 --rb 0.85 --deep 0.4",
        "--cap 2 --T 0.2 --rb 0.6 --deep 0.1", "--cap 2 --T 0.2 --rb 0.85 --deep 0.4",
        "--cap 3 --T 0.2 --rb 0.85 --deep 0.2", "--cap 2 --T 0.2 --rb 0.85 --deep 0"]
if HAVE_TW:
    TWSECS = int(os.environ.get("TW_SECS", "22"))
    cfg = CFGS[SHARD % len(CFGS)]
    for pid in mine:
        if time.time() - t0 > CAP - 45: break
        sv, tg, L, R = PZ[pid]
        tg = sorted(set(tg))
        prog = BEST[pid]
        cf = f"tw_{pid}.txt"
        with open(cf, "w") as fh:
            fh.write("P %s %d %s %d %s %s %d %d\n" % (pid, len(sv), " ".join(map(str, sv)),
                     len(tg), " ".join(map(str, tg)), L, R, len(prog)))
            for (o, i, j, d) in prog:
                fh.write("%s %s %s %s\n" % (o, i, j, d))
        try:
            r = subprocess.run(["./triwalk", "--time", str(TWSECS), "--seed",
                                str(random.randrange(1, 10**9))] + cfg.split(),
                               stdin=open(cf), capture_output=True, text=True, timeout=TWSECS + 90, env=env)
            out = r.stdout or ""
        except Exception:
            continue
        lines = (r.stdout or "").splitlines()
        i = 0
        while i < len(lines):
            t = lines[i].split()
            if len(t) == 4 and t[0] == "V" and t[1] in BEST:
                q = t[1]; newn = int(t[3])
                if newn < len(BEST[q]) and i + 1 + newn <= len(lines):
                    po = []
                    okp = True
                    for k in range(i+1, i+1+newn):
                        u = lines[k].split()
                        if len(u) != 4 or u[0] not in OPC:
                            okp = False; break
                        po.append([u[0], int(u[1]), int(u[2]), int(u[3])])
                    if okp and replay_ok(q, po):
                        if q not in wins or len(po) < len(wins[q]):
                            wins[q] = po
                    i += newn
            elif len(t) >= 4 and t[0] == "R":
                nums = list(map(int, t[3:]))
                po = [[IOPS[nums[k]], nums[k+1], nums[k+2], nums[k+3]] for k in range(0, len(nums)-3, 4)]
                q = t[1]
                if q in BEST and len(po) < len(BEST[q]) and replay_ok(q, po):
                    if q not in wins or len(po) < len(wins[q]):
                        wins[q] = po
            i += 1
    print("triwalk stage done, total wins", len(wins), flush=True)

json.dump(wins, open("wins.json", "w"))
print("shard", SHARD, "wins", len(wins), "saved", sum(len(BEST[k])-len(v) for k, v in wins.items()), flush=True)
