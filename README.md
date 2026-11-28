# santa-farm — distributed value-set walk on GitHub Actions runners

20 parallel ubuntu runners (6 vCPU each) run Ross Wade's published value-set annealer
(`src/setwalk.cpp`, CC0, from his public Kaggle dataset) against a shared portfolio
(`data/best.csv`), seeded with equal-length variant value sets (`data/variants.txt`).

Every returned program is replay-validated by the Python referee in `farm_worker.py`
before it counts as a win. Outputs: `wins-{shard}` artifacts.

Method write-up: kaggle.com/code/saurabhkumar234/the-databank-method-santa-2026-research
Engine credit: Ross Wade (setwalk), goodpjw2008 (plateau-variant union idea), Atakan Aldemir.
