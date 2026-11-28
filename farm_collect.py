#!/usr/bin/env python3
"""Merge per-shard wins from downloaded artifacts into farm_out/."""
import json, glob, os

os.makedirs("farm_out", exist_ok=True)

wins = {}
for d in sorted(glob.glob("all-wins*")):
    p = os.path.join(d, "wins.json")
    if os.path.exists(p):
        try:
            wins.update(json.load(open(p)))
        except Exception:
            pass
json.dump(wins, open("farm_out/wins.json", "w"), indent=1)
print("total winning puzzles:", len(wins))

# merge per-puzzle optimality certificates from our CP-SAT engine
certs = {}
for f in glob.glob("all-wins*/certs.json") + glob.glob("all-wins*/*/certs.json"):
    try:
        certs.update(json.load(open(f)))
    except Exception:
        pass
json.dump(certs, open("farm_out/certs.json", "w"), indent=1)
nproven = sum(1 for c in certs.values() if isinstance(c, dict) and c.get("proven_optimal"))
print(f"certificates: {len(certs)} puzzles, {nproven} PROVEN-OPTIMAL")

# merge R-line candidate files from all shards
with open("farm_out/cand_R.txt", "w") as out:
    for f in glob.glob("all-wins*/out_*.txt") + glob.glob("all-wins*/*/out_*.txt"):
        try:
            out.write(open(f).read())
        except Exception:
            pass

# wins.csv for the databank importer (program = JSON list, string ops)
with open("farm_out/wins.csv", "w") as f:
    f.write("id,length,program\n")
    for pid, prog in wins.items():
        js = json.dumps(prog, separators=(",", ":"))
        f.write('%s,%d,"%s"\n' % (pid, len(prog), js.replace('"', '""')))
print("wins.csv rows:", len(wins))

# flat certificate summary for the repo
with open("farm_out/certs.csv", "w") as f:
    f.write("id,proven_optimal,status,bound,obj,universe\n")
    for pid, c in sorted(certs.items()):
        if not isinstance(c, dict):
            continue
        f.write("%s,%s,%s,%s,%s,%s\n" % (
            pid, c.get("proven_optimal"), c.get("status"), c.get("bound"),
            c.get("obj"), c.get("universe")))
print("certs.csv rows:", len(certs))
