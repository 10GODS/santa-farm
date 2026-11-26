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

# merge R-line candidate files from all shards
with open("farm_out/cand_R.txt", "w") as out:
    for f in glob.glob("all-wins*/out_*.txt") + glob.glob("all-wins*/*/out_*.txt"):
        try:
            out.write(open(f).read())
        except Exception:
            pass

# wins.csv for the databank importer
with open("farm_out/wins.csv", "w") as f:
    f.write("id,length,program\n")
    for pid, rec in wins.items():
        prog = rec["program"].replace("\r", "").replace("\n", " ")
        f.write('%s,%s,"%s"\n' % (pid, rec["length"], prog))
print("wins.csv rows:", len(wins))
