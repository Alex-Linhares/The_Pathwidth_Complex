"""Is pb bounded by a function of pw(G_u)?  Tabulates max pb at each value of pw(G_u) over
every labelled dag on <= 6 vertices and random dags on 7..11 vertices (sparse, so that G_u
stays narrow), and the smallest witnesses of each (pw(G_u), pb) record.

Regenerate: cd /home/al/dev/MOSP && python reports/scratch/ss7_register_sufficiency/pb_vs_pwgu.py
"""
import itertools, random, sys, time
sys.path.insert(0, "/home/al/dev/MOSP")
from paper1.ss7_register import pb_ideal, succ_of_arcs, lengauer_u
from fixed_parameter_algorithm.pathwidth import compute_pathwidth

t0 = time.time()
record = {}   # pw(G_u) -> (max pb, n, arcs)
def note(n, arcs):
    succ = succ_of_arcs(n, arcs)
    pb = pb_ideal(n, succ, 0)
    pw = compute_pathwidth(lengauer_u(n, arcs))[0]
    if pw not in record or pb > record[pw][0] or (pb == record[pw][0] and n < record[pw][1]):
        record[pw] = (pb, n, arcs)
for n in range(1, 7):
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        note(n, [p for i, p in enumerate(pairs) if mask >> i & 1])
print("exhaustive to 6 vertices:", {k: (v[0], v[1]) for k, v in sorted(record.items())}, f"[{time.time()-t0:.0f}s]", flush=True)
rng = random.Random(11)
for n in range(7, 12):
    for _ in range(6000 if n <= 9 else 2500):
        p = rng.choice([1.2, 1.6, 2.0, 2.5]) / n   # sparse: about 1.2-2.5 arcs per vertex
        arcs = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < p]
        note(n, arcs)
    print(f"after random dags on {n} vertices:", {k: (v[0], v[1]) for k, v in sorted(record.items())}, f"[{time.time()-t0:.0f}s]", flush=True)
print("records (pw(G_u): pb, n, arcs):")
for k, v in sorted(record.items()):
    print(f"  pw(G_u) = {k}: pb = {v[0]} (pbw = {k+1}, gap {v[0]-k-1}), n = {v[1]}, arcs = {v[2]}")
