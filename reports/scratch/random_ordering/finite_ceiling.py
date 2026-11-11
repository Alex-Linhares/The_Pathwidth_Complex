"""The finite theorem evaluated: the least w with sum_i P(Bin(n-i-1, 1-(1-p)^(i+1)) > w) <= 0.05
(a 95% ceiling on pw from `sum_gnpWeight_pathwidth_gt_le`), per middle-regime cell, beside the
identity widths and the proved pathwidths; and the same at c = 3, 6, 10 for n = 60, 120, 400, 1000."""
import csv, math
from collections import defaultdict
from scipy.stats import binom

def tail_sum(n, p, w):
    return sum(binom.sf(w, n - i - 1, 1 - (1 - p) ** (i + 1)) for i in range(n))

def ceiling(n, p, level=0.05):
    w = 0
    while tail_sum(n, p, w) > level:
        w += 1
    return w

rows = list(csv.DictReader(open("reports/scratch/random_ordering/middle_identity.csv")))
cells = defaultdict(list)
for r in rows:
    cells[(r["family"], int(r["n"]), float(r["p"]), float(r["c"]))].append((int(r["pw"]), int(r["identity_width"])))
print("cell n c | pw max | identity max | w_0.05 (finite theorem) | max_t E[k_t]")
order = {"c3": 0, "sqrtn": 1, "2lnn": 2, "n07": 3, "dense": 4}
for (fam, n, p, c), L in sorted(cells.items(), key=lambda kv: (kv[0][1], order.get(kv[0][0], 9))):
    w = ceiling(n, p)
    mb = max((n - t) * (1 - (1 - p) ** t) for t in range(1, n))
    print(f"{fam:6s} {n:3d} {c:6.2f} | {max(x[0] for x in L):3d} | {max(x[1] for x in L):3d} | {w:3d} | {mb:6.2f}")
print("\nsparse c fixed: w_0.05 / n against beta_typ(c)")
for c in [3, 6, 10, 20]:
    bt = max((1 - x / 2000) * (1 - math.exp(-c * x / 2000)) for x in range(2001))
    for n in [60, 120, 400, 1000]:
        w = ceiling(n, c / n)
        print(f"c={c:2d} n={n:5d}: w_0.05 = {w:4d}, w_0.05/n = {w/n:.3f}, beta_typ = {bt:.3f}")
