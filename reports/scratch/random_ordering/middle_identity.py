"""The identity-ordering width of every middle-regime graph (paper1/latex/data/random_graph_middle.csv
cells; graphs in reports/scratch/random_graph_middle/results.csv, g6 column) against the bound
max_t (n-t)(1-(1-p)^t), the proved pathwidth and the cell's other ceilings.  No solver."""
import csv, math, sys
from collections import defaultdict
import networkx as nx

rows = list(csv.DictReader(open("/home/al/dev/MOSP/reports/scratch/random_graph_middle/results.csv")))
cells = {(r["family"], int(r["n"])): r for r in csv.DictReader(open("/home/al/dev/MOSP/paper1/latex/data/random_graph_middle.csv"))}

def identity_width(G):
    n = G.number_of_nodes(); adj = {v: set(G[v]) for v in G}
    best = 0
    for t in range(1, n):
        prefix = set(range(t))
        k = sum(1 for v in range(t, n) if adj[v] & prefix)
        best = max(best, k)
    return best

agg = defaultdict(list)
out = open("/home/al/dev/MOSP/reports/scratch/random_ordering/middle_identity.csv", "w")
out.write("family,n,c,p,sample,pw,identity_width,mean_bound,beta_typ_n\n")
for r in rows:
    if r["status"] not in ("refutation", "minor"):
        continue
    G = nx.from_graph6_bytes(r["g6"].encode())
    n = int(r["n"]); p = float(r["p"]); c = float(r["c"])
    assert G.number_of_nodes() == n
    w_id = identity_width(G)
    mean_bound = max((n - t) * (1 - (1 - p) ** t) for t in range(1, n))
    bt = max((1 - x / 1000) * (1 - math.exp(-c * x / 1000)) for x in range(1001)) * n
    pw = int(r["width"])
    assert pw <= w_id
    out.write(f"{r['family']},{n},{c},{p},{r['sample']},{pw},{w_id},{mean_bound:.3f},{bt:.3f}\n")
    agg[(r["family"], n)].append((pw, w_id, mean_bound, bt))
out.close()
print("family n c | pw mean | identity width mean (min-max) | max_t E[k_t] | beta_typ n | n-alpha | EM hist | best ceiling")
order = {"c3": 0, "sqrtn": 1, "2lnn": 2, "n07": 3, "p05": 4}
for (fam, n), L in sorted(agg.items(), key=lambda kv: (kv[0][1], order.get(kv[0][0], 9))):
    cell = cells.get((fam, n))
    pws = [x[0] for x in L]; ids = [x[1] for x in L]
    mb = L[0][2]; bt = L[0][3]
    na = float(cell["n_minus_alpha_mean"]) if cell else float("nan")
    em = float(cell["em_hist_mean"]) if cell else float("nan")
    c = float(cell["c"]) if cell else float("nan")
    ceilings = {"n-alpha": na, "EM": em, "identity": sum(ids) / len(ids)}
    best = min(ceilings, key=ceilings.get)
    print(f"{fam:6s} {n:3d} {c:6.2f} | {sum(pws)/len(pws):6.2f} | {sum(ids)/len(ids):6.2f} ({min(ids)}-{max(ids)}) | {mb:7.2f} | {bt:7.2f} | {na:6.2f} | {em:6.2f} | {best}")
