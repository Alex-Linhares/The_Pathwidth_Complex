"""The Jensen lower bound on E[X_w^2]/E[X_w]^2 against n at fixed (c, beta), with the
binomial KL rate of the planted edge count as the predicted slope; and the dense case
p = 1/2 at w = n - s.  Output: jensen_sweep.csv, jensen_dense.csv."""
import csv, math, sys
sys.path.insert(0, "/home/al/dev/MOSP")
from learning.layout_moment import jensen_log_ratio, typical_width

OUT = "/home/al/dev/MOSP/reports/scratch/layout_second_moment/"

def kl(a, p):
    return a * math.log(a / p) + (1 - a) * math.log((1 - a) / (1 - p))

rows = []
cells = [(3, b) for b in (0.1, 0.15, 0.183, 0.25, 0.3, 0.35, 0.4)] + \
        [(6, b) for b in (0.2, 0.3, 0.4, 0.458, 0.5, 0.55)] + \
        [(10, b) for b in (0.35, 0.415, 0.5, 0.6, 0.656)]
for c, beta in cells:
    for n in (20, 30, 40, 50, 60, 70, 80, 100):
        w = round(beta * n)
        p = c / n
        r = jensen_log_ratio(n, p, w)
        C = n * (n - 1) // 2
        a = r["planted_edges"] / C
        rows.append([c, beta, n, w, round(r["log_ratio_bound"], 4), round(r["log_expected"], 3),
                     round(r["planted_edges"], 3), round(r["typical_edges"], 3),
                     round(C * kl(a, p) / n, 4), round(typical_width(n, p)[1] / n, 4)])
        print(*rows[-1], flush=True)
with open(OUT + "jensen_sweep.csv", "w", newline="") as fh:
    wr = csv.writer(fh)
    wr.writerow(["c", "beta", "n", "w", "log_ratio_bound", "log_E_X", "planted_edges", "typical_edges",
                 "kl_rate_per_n", "typical_over_n"])
    wr.writerows(rows)

rows = []
for p in (0.5,):
    for s in (2, 3, 4, 6, 8):
        for n in (20, 30, 40, 50, 60, 80):
            w = n - s
            r = jensen_log_ratio(n, p, w)
            C = n * (n - 1) // 2
            a = r["planted_edges"] / C
            rows.append([p, s, n, w, round(r["log_ratio_bound"], 4), round(r["log_expected"], 3),
                         round(r["planted_edges"], 3), round(r["typical_edges"], 3), round(C * kl(a, p), 4),
                         round(n - typical_width(n, p)[1], 3)])
            print("dense", *rows[-1], flush=True)
with open(OUT + "jensen_dense.csv", "w", newline="") as fh:
    wr = csv.writer(fh)
    wr.writerow(["p", "s", "n", "w", "log_ratio_bound", "log_E_X", "planted_edges", "typical_edges",
                 "kl_total", "n_minus_typical"])
    wr.writerows(rows)
