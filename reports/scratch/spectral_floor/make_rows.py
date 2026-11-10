"""Evidence rows for the dataset's open-run channel: the spectral floor on the
nine open classes where it is the best floor on record
(`reports/layout_lp_literature.md` §8). One row per class in
`run_unlimited.py`'s FIELDS, `proof` empty (the class stays open), `width` the
recorded width, `order` the record's stored witness, `lower` the spectral floor
in pathwidth units, and the `minor` column carrying the floor certificate
(`spectral-prefix-1`): the eigenvalues, the prefix and separator sizes, the
per-theorem values and the command that regenerates the value from the edge
list. Nothing is solved. Output: results_spectral.csv beside this file.

    PYTHONPATH=. python3 reports/scratch/spectral_floor/make_rows.py
"""
import csv, gzip, json, sys, time
from pathlib import Path

import networkx as nx

sys.path.insert(0, ".")
from learning.spectral_bound import (TOL, laplacian_extremes, prefix_separator_bound, spectral_bounds,
                                     spectral_graph_bound)

HERE = Path(__file__).resolve().parent
NINE = {"pwc-16016": "NStarGraph_5 (the star graph S_5: 4-regular bipartite, mu2 = 1, mun = 8)",
        "pwc-16023": "OddGraph_5 (the Kneser graph K(9, 4): adjacency spectrum 5, -4, 3, -2, 1, so mu2 = 5 - 3 = 2, mun = 5 + 4 = 9)",
        "pwc-16064": "Tutte12Cage (adjacency spectrum +-3, +-sqrt 6, +-sqrt 2, 0, so mu2 = 3 - sqrt 6, mun = 6)",
        "pwc-15943": "CameronGraph (srg(231, 30, 9, 3); Helmberg et al. (20) does the work: |C| >= |A||B|/12)",
        "pwc-15995": "HyperStarGraph_10_5", "pwc-17488": "he048 (PACE 2017 heuristic)",
        "pwc-15892": "le450_5a (TreewidthLIB colouring)", "pwc-15893": "le450_5b (TreewidthLIB colouring)",
        "pwc-15944": "Cell120 (the 120-cell)"}
FIELDS = ["id", "collections", "names", "n", "m", "recorded", "started_from_layout", "width", "proof", "lower",
          "nodes", "seconds", "finished", "status", "order", "minor"]
THEOREMS = {
    "mp": "Theorem 1: Mohar & Poljak 1993 Thm 2.8 as Helmberg, Mohar, Poljak & Rendl 1995 eq. (21), with the "
          "top-c degree sum S(c) for Delta c: S(c) >= mu2 ((a + b) - (a - b)^2 / n)",
    "hmpr": "Theorem 2: Helmberg, Mohar, Poljak & Rendl 1995 Theorem 11 eq. (20): c >= 4 mun mu2 a b / (n (mun - mu2)^2)",
    "gl": "Theorem 3: Gu & Liu 2022 (Gima et al. 2025 Lemma 4.1): c >= 2 mu2 min(a, b) / (mun - mu2)",
    "prefix": "Theorem 4 (learning/spectral_bound.py): a layout of vertex separation w has, at every prefix size t, "
              "a separator triple (C_t, A_t = prefix, B_t = rest) with |C_t| <= w, so w >= c_t := min feasible c at t, "
              "and pw = vs >= max_t c_t (Kinnersley 1992; MOSP = pw + 1 by MOSPGraph.lean)",
}

recs = {}
for line in gzip.open("paper1/data/dataset/pathwidth_dataset.jsonl.gz", "rt"):
    r = json.loads(line)
    if r["id"] in NINE:
        recs[r["id"]] = r
assert len(recs) == len(NINE), sorted(set(NINE) - set(recs))
rows = []
for rid, r in sorted(recs.items(), key=lambda kv: kv[1]["n"]):
    G = nx.Graph(); G.add_nodes_from(range(r["n"])); G.add_edges_from(map(tuple, r["edges"]))
    assert nx.is_connected(G)
    t0 = time.time()
    mu2, mun = laplacian_extremes(G)
    degs = [d for _, d in G.degree()]
    value, info = spectral_graph_bound(G)
    per = {u: prefix_separator_bound(r["n"], mu2, mun, degs, use=(u,))[0] for u in ("mp", "hmpr", "gl")}
    fam = spectral_bounds(G) if r["n"] <= 260 else None
    best = value if fam is None else fam["best"]
    assert best == value, (rid, best, value)        # the whole graph attains it on all nine
    assert value < r["width"], (rid, value, r["width"])
    t = info["t_star"]; c = value
    cert = {
        "format": "spectral-prefix-1",
        "theorem": THEOREMS["prefix"],
        "inequalities": [THEOREMS["mp"], THEOREMS["hmpr"], THEOREMS["gl"]],
        "family": "graph",
        "n": r["n"], "m": r["m"], "connected": True,
        "mu2": mu2, "mun": mun, "delta": max(degs), "min_degree": min(degs),
        "tolerance": "mu2 lowered and mun raised by TOL * max(1, value), TOL = %g, before use; slack 1e-9 "
                     "on each inequality: rounding can only weaken the bound" % TOL,
        "prefix_t": t, "separator_c": c,
        "witness": f"at prefix size t = {t} no separator of size c - 1 = {c - 1} satisfies all three inequalities "
                   f"(a = {t}, b = {r['n'] - t - (c - 1)}), so every layout has vertex separation >= {c}",
        "per_inequality": {"theorem_1_mohar_poljak": per["mp"], "theorem_2_helmberg_eq20": per["hmpr"],
                           "theorem_3_gu_liu": per["gl"]},
        "families": None if fam is None else {k: fam[k] for k in ("graph", "peel", "minor")},
        "pathwidth_floor": c, "units": "pathwidth (vertex separation); MOSP floor = c + 1",
        "closed_form": NINE[rid],
        "command": "learning.spectral_bound.spectral_graph_bound(G) on the record's edge list "
                   "(python3 reports/scratch/spectral_floor/make_rows.py; 0 violations on 50,949 certified "
                   "instances and 274,048 small graphs, reports/spectral_bound.md)",
        "lean": "not formalised (paper1/todo.md, 'Formalise the spectral lower bound in Lean')",
        "checker": "paper1/dataset_check.py replays the prefix arithmetic from the stated eigenvalues and the "
                   "graph's degree sequence; the eigenvalues themselves are regenerated by the command",
    }
    rows.append(dict(id=rid, collections="", names=NINE[rid].split(" ")[0], n=r["n"], m=r["m"], recorded=r["width"],
                     started_from_layout=True, width=r["width"], proof="", lower=c, nodes=0,
                     seconds=round(time.time() - t0, 1), finished=time.strftime("%Y-%m-%dT%H:%M:%S"), status="ok",
                     order=json.dumps(r["layout"]), minor=json.dumps(cert)))
    print(rid, NINE[rid].split(" ")[0], "n", r["n"], "width", r["width"], "spectral", c, "t*", t, per,
          None if fam is None else {k: fam[k] for k in ("graph", "peel", "minor")}, flush=True)
with open(HERE / "results_spectral.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=FIELDS); w.writeheader(); w.writerows(rows)
print("wrote", len(rows), "rows")
