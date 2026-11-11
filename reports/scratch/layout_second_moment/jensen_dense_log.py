"""Dense case p = 1/2 at the widths that matter, w = n - round(a log_b n), a = 2, 3, 4."""
import csv, math, sys
sys.path.insert(0, "/home/al/dev/MOSP")
from learning.layout_moment import jensen_log_ratio, typical_width
OUT = "/home/al/dev/MOSP/reports/scratch/layout_second_moment/jensen_dense_log.csv"
rows = []
p = 0.5
for a in (2, 3, 4):
    for n in (30, 40, 60, 80, 100):
        s = round(a * math.log(n, 2))
        w = n - s
        r = jensen_log_ratio(n, p, w)
        rows.append([p, a, n, s, w, round(r["log_ratio_bound"], 4), round(r["log_expected"], 3),
                     round(r["planted_edges"], 3), round(r["typical_edges"], 3), round(n - typical_width(n, p)[1], 3)])
        print(*rows[-1], flush=True)
with open(OUT, "w", newline="") as fh:
    wr = csv.writer(fh)
    wr.writerow(["p", "a", "n", "s", "w", "log_ratio_bound", "log_E_X", "planted_edges", "typical_edges", "n_minus_typical"])
    wr.writerows(rows)
