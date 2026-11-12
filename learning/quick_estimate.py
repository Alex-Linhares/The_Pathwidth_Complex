"""The quick estimate: pathwidth from an instance's parameters in milliseconds, no search (2026-11-12).

The question (`reports/quick_estimate.md`): given `n`, `m`, the density and the degree
sequence of an instance and nothing else, how well do the random-graph results on
record estimate its pathwidth (MOSP optimum minus one)?  Four numbers per instance,
then one estimate, measured against every optimum and pathwidth already proved on
record.  **Nothing here solves an instance**: every truth is read from `solutions/`
(through `learning/data/instances.csv`), the ensemble results, the random-graph
measurement CSVs or the paper's dataset, and only certified provenances count as
truth (`solution` records are kept, flagged `truth_is_upper`, and excluded from every
accuracy figure).

The four numbers, all in **pathwidth units** (optimum = pathwidth + 1 on a MOSP
instance, `MOSPGraph.lean`):

1. **floor** -- the first-moment floor at level 0.05: for a MOSP instance the
   clique-cover bound of `CliqueCoverMoment.lean` at the realised pattern sizes
   (`learning.first_moment.log_bound`, the "measured form" of
   `reports/random_graph_classes.md`), for a plain graph the empty-pair inequality
   of Theorem A at the realised edge density (`FirstMoment.lean`).  Both read the
   parameters only -- `n` and the size histogram, or `n` and `p` -- never the graph,
   so off the random model they are not bounds; where the floor exceeds a certified
   optimum it measures the instance's distance from a random one.  The solver's own
   `_lower_bound` (`lb_best`: trivial, clique, contraction degeneracy) is recorded
   beside it; that one reads the graph and is a theorem.
2. **ceiling** -- the smaller of the random-ordering width
   `max_t (n - t)(1 - (1 - p)^t)` (`reports/random_ordering_bound.md`, the expected
   open count of the identity ordering of `G(n, p)`, exact at finite `n`) and
   `n - alpha_greedy` (a minimum-degree greedy independent set;
   `pw <= n - alpha <= n - alpha_greedy`, `IndependenceBound.lean`, the one ceiling
   that is a bound); `ceiling_source` says which.  The Edwards--McDermid
   degree-histogram term `sum_v g(d(v))` (`learning.edwards_mcdermid`, Corollary 5.2's
   main term unreduced) is recorded as `ceil_em`, and `ceiling_em` is the minimum of
   all three: it omits the corollary's `tau(n) + O(log n)` and the record measured
   it below the pathwidth on 28% of proved graphs (`reports/edwards_mcdermid.md`),
   which the smoke test of 24 ensemble instances showed at once (1.1 against a
   pathwidth of 3 at n = 10), so it was kept out of the recipe's bracket *before*
   the measurement and the variant that uses it is reported as `recipe_em`.
3. **point estimate** -- min-fill treewidth (`networkx`'s `treewidth_min_fill_in`,
   the `tw_min_fill` of the record; `reports/ml_nature.md` section 4 and 14).
4. **dense regime** (`p >= DENSE_P = 0.3`) -- the corner-block finite threshold of
   `reports/dense_staircase.md` section 4: `n - s_block + 1`, `s_block` the largest `s`
   whose symmetric block count is at least one (`learning.staircase_moment.block_threshold`
   at level 1), the measured median `n - pw` plus one at `n = 30-60`, `p = 1/2`.

**The estimate, defined before measuring** (`RECIPE`): in the dense regime the block
value, otherwise min-fill treewidth, clipped into `[floor, ceiling]`; where the
bracket is inverted (`floor > ceiling`, which happens off the random model) the
rounded midpoint.  Alternatives recorded beside it: `tw` alone (the kill
criterion's baseline), `tw_floor = max(tw, floor)`, `midpoint`, `clip_tw` (min-fill
clipped, the recipe without the dense rule), `block` (the dense rule everywhere it
applies).  **Kill criterion, stated before measuring**: if the recipe does not beat
min-fill treewidth alone on MAE and on exact rate by size band, the answer is "use
treewidth".

Usage:
    nice -n 19 python3 -m learning.quick_estimate run --workers 8     # the per-instance table (about 20 min)
    nice -n 19 python3 -m learning.quick_estimate summarise           # the report tables and figure CSVs
    nice -n 19 python3 -m learning.quick_estimate timing              # the timing sample at 100-125 customers
    nice -n 19 python3 -m learning.quick_estimate extras              # the report's remaining numbers (extras.txt)
    python3 -m pytest tests/test_quick_estimate.py -q
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import math
import multiprocessing as mp
import re
import sys
import time
from pathlib import Path

import numpy as np

from learning.edwards_mcdermid import g_float
from learning.first_moment import log_bound, log_pairs
from learning.staircase_moment import block_threshold

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / "reports" / "scratch" / "quick_estimate"
ESTIMATES_CSV = SCRATCH / "estimates.csv"
INSTANCES_CSV = ROOT / "learning" / "data" / "instances.csv"
ENSEMBLE_DIR = ROOT / "learning" / "data" / "ensemble"
GNP_PILOT = ROOT / "reports" / "scratch" / "gnp_pilot" / "results.csv"
GNP_MIDDLE = ROOT / "reports" / "scratch" / "random_graph_middle" / "results.csv"
DATASET = ROOT / "paper1" / "data" / "dataset" / "pathwidth_dataset.jsonl.gz"
FIG_DATA = ROOT / "paper1" / "latex" / "data"

LEVEL = 0.05          # the floor's confidence level
DENSE_P = 0.3         # the dense regime
GRAPH_MAX_N = 1024    # the graph dataset above this is read by header only (the C engine's limit)
CERTIFIED = ("certified:refutation", "certified:bound", "certified:minor", "certified:theorem")
BANDS = ((0, 20), (21, 40), (41, 60), (61, 100), (101, 125), (126, 10 ** 9))
BAND_LABELS = {b: (f"{b[0]}-{b[1]}" if b[1] < 10 ** 9 else f"{b[0]}+") for b in BANDS}
ESTIMATORS = ("recipe", "recipe_em", "tw", "tw_floor", "midpoint", "clip_tw", "block")
RECIPE = ("dense: n - s_block + 1; sparse: min-fill treewidth; clipped into [floor, ceiling]; "
          "midpoint where floor > ceiling")
# generators of the MOSP corpus, in the fixed order the figures use
GENERATORS = ("Chu & Stuckey", "Faggioli-Bentivoglio", "Harvey", "Simonis", "Shaw", "Wilson", "Miller", "SCOOP")
DESIGNED = ("SCOOP", "Shaw", "Wilson", "Miller")
# the five open cubic cages (reports/gaspers_cages.md): records are upper bounds only
CAGES = {"pwc-15968": "Foster (90)", "pwc-15936": "Biggs-Smith (102)", "pwc-16006": "Ljubljana (112)",
         "pwc-15932": "Balaban 11-cage (112)", "pwc-16064": "Tutte 12-cage (126)"}
FIELDS = ["kind", "group", "subgroup", "name", "n", "m", "edges", "p", "truth", "truth_is_upper", "provenance",
          "floor", "floor_level1", "lb_best", "ceiling", "ceiling_source", "ceil_random_order", "ceil_em",
          "ceil_alpha", "ceiling_em", "tw", "tw_record", "block", "dense", "bracket_ok",
          "recipe", "recipe_em", "tw_floor", "midpoint", "clip_tw", "block_est",
          "t_floor", "t_ceiling", "t_tw", "t_block", "t_total"]


# ----------------------------------------------------------------------------
# graphs as bitmasks
# ----------------------------------------------------------------------------


def masks_from_edges(n: int, edges) -> list[int]:
    masks = [0] * n
    for u, v in edges:
        if u == v:
            continue
        masks[u] |= 1 << v
        masks[v] |= 1 << u
    return masks


def masks_from_matrix(matrix: np.ndarray) -> tuple[list[int], list[int]]:
    """The MOSP graph of a customers x patterns matrix (a clique per pattern) and the
    pattern sizes."""
    m = np.asarray(matrix) != 0
    n = m.shape[0]
    masks = [0] * n
    sizes = []
    for j in range(m.shape[1]):
        rows = np.flatnonzero(m[:, j])
        sizes.append(int(len(rows)))
        clique = 0
        for i in rows:
            clique |= 1 << int(i)
        for i in rows:
            masks[int(i)] |= clique & ~(1 << int(i))
    return masks, sizes


def degree_sequence(masks: list[int]) -> list[int]:
    return [bin(a).count("1") for a in masks]


def edge_count(masks: list[int]) -> int:
    return sum(degree_sequence(masks)) // 2


def edge_density(masks: list[int]) -> float:
    n = len(masks)
    return 2 * edge_count(masks) / (n * (n - 1)) if n > 1 else 0.0


# ----------------------------------------------------------------------------
# the four numbers
# ----------------------------------------------------------------------------


def gnp_log_bound(n: int, p: float, k: int) -> float:
    """`log [C(n,t) C(n-t,t-1) (1-p)^(t(t-1))]`, `t = ceil((n-k)/2)` (Theorem A's finite
    form, `weightedSum_graphsOfPathwidthLe_le`); `+inf` where the pair does not exist."""
    t = (n - k + 1) // 2
    if t < 1 or 2 * t - 1 > n:
        return math.inf
    if p >= 1.0:
        return -math.inf if t > 1 else log_pairs(n, t)
    return log_pairs(n, t) + t * (t - 1) * math.log1p(-p)


def union_floor(n: int, log_bound_fn, level: float = LEVEL) -> int:
    """The floor on the pathwidth: `k* + 1`, `k*` the largest `k` with
    `log P(pw <= k) < log level` (0 when no `k` qualifies)."""
    thr = math.log(level)
    best = -1
    for k in range(n):
        if log_bound_fn(k) < thr:
            best = k
    return best + 1


def cover_floor(n: int, sizes, level: float = LEVEL) -> int:
    """The clique-cover first-moment floor at the realised pattern sizes."""
    hist: dict[int, int] = {}
    for s in sizes:
        hist[int(s)] = hist.get(int(s), 0) + 1
    return union_floor(n, lambda k: log_bound(n, hist, k), level)


def gnp_floor(n: int, p: float, level: float = LEVEL) -> int:
    """The empty-pair first-moment floor of `G(n, p)` at the realised density."""
    return union_floor(n, lambda k: gnp_log_bound(n, p, k), level)


def random_ordering_width(n: int, p: float) -> float:
    """`max_t (n - t)(1 - (1 - p)^t)`: the largest expected open count along a fixed
    ordering of `G(n, p)` (`RandomOrdering.lean`; `reports/random_ordering_bound.md`)."""
    if n <= 1 or p <= 0:
        return 0.0
    return max((n - t) * (1 - (1 - p) ** t) for t in range(0, n + 1))


def em_histogram_term(degrees) -> float:
    """`sum_v g(d(v))`, the Edwards--McDermid degree-histogram term (Corollary 5.2,
    unreduced)."""
    return sum(g_float(int(d)) for d in degrees)


def greedy_alpha(masks: list[int]) -> int:
    """A minimum-degree greedy independent set, a lower bound on `alpha(G)`, so
    `n - greedy_alpha` is an upper bound on the pathwidth (`IndependenceBound.lean`)."""
    n = len(masks)
    alive = (1 << n) - 1
    count = 0
    while alive:
        best, best_deg = -1, n + 1
        rest = alive
        while rest:
            v = (rest & -rest).bit_length() - 1
            rest &= rest - 1
            d = bin(masks[v] & alive).count("1")
            if d < best_deg:
                best, best_deg = v, d
                if d == 0:
                    break
        count += 1
        alive &= ~((1 << best) | masks[best])
    return count


def min_fill_treewidth(masks: list[int]) -> int:
    """`networkx`'s min-fill-in treewidth heuristic, the `tw_min_fill` of the record."""
    import networkx as nx
    from networkx.algorithms.approximation import treewidth_min_fill_in
    n = len(masks)
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    for u in range(n):
        rest = masks[u] >> (u + 1)
        v = u + 1
        while rest:
            if rest & 1:
                graph.add_edge(u, v)
            rest >>= 1
            v += 1
    return int(treewidth_min_fill_in(graph)[0]) if graph.number_of_edges() else 0


def block_estimate(n: int, p: float) -> int:
    """`n - s_block + 1`: the dense-regime point estimate (`reports/dense_staircase.md`
    section 4, where the block's finite threshold was the median `n - pw` plus one)."""
    if p >= 1.0:
        return n - 1
    return n - block_threshold(n, 1.0 - p, 1.0, True) + 1


# ----------------------------------------------------------------------------
# one instance
# ----------------------------------------------------------------------------


def estimate(masks: list[int], sizes=None, lb_best=None, tw_record=None) -> dict:
    """The four numbers, the estimators and the timings of one graph (the MOSP graph
    when `sizes`, the pattern sizes, is given; a plain graph otherwise).  Every value in
    pathwidth units."""
    n = len(masks)
    out: dict = {"n": n, "edges": edge_count(masks)}
    p = edge_density(masks)
    out["p"] = p
    t0 = time.perf_counter()
    if sizes is not None:
        out["m"] = len(sizes)
        out["floor"] = cover_floor(n, sizes, LEVEL)
        out["floor_level1"] = cover_floor(n, sizes, 1.0)
    else:
        out["m"] = out["edges"]
        out["floor"] = gnp_floor(n, p, LEVEL)
        out["floor_level1"] = gnp_floor(n, p, 1.0)
    t1 = time.perf_counter()
    degrees = degree_sequence(masks)
    ro = random_ordering_width(n, p)
    em = em_histogram_term(degrees)
    al = n - greedy_alpha(masks)
    out.update(ceil_random_order=ro, ceil_em=em, ceil_alpha=al)
    cands = {"random_order": ro, "n_minus_alpha": al}
    src = min(cands, key=cands.get)
    out["ceiling_source"] = src
    out["ceiling"] = int(math.floor(cands[src] + 1e-9))
    out["ceiling_em"] = int(math.floor(min(cands[src], em) + 1e-9))
    t2 = time.perf_counter()
    out["tw"] = min_fill_treewidth(masks)
    t3 = time.perf_counter()
    out["dense"] = bool(p >= DENSE_P)
    out["block"] = block_estimate(n, p) if out["dense"] else ""
    t4 = time.perf_counter()
    out.update(t_floor=t1 - t0, t_ceiling=t2 - t1, t_tw=t3 - t2, t_block=t4 - t3, t_total=t4 - t0)
    out["lb_best"] = "" if lb_best is None else lb_best
    out["tw_record"] = "" if tw_record is None else tw_record
    out.update(estimators(out))
    return out


def _clip(x: float, lo: int, hi: int) -> int:
    return int(min(max(x, lo), hi))


def estimators(row: dict) -> dict:
    """The recipe and its alternatives from the four numbers (all pathwidth units)."""
    floor, ceiling, tw = int(row["floor"]), int(row["ceiling"]), int(row["tw"])
    ok = floor <= ceiling
    mid = int(round((floor + ceiling) / 2))
    point = int(row["block"]) if row["dense"] else tw
    ceiling_em = int(row["ceiling_em"])
    out = {
        "bracket_ok": ok,
        "recipe": _clip(point, floor, ceiling) if ok else mid,
        "recipe_em": (_clip(point, floor, ceiling_em) if floor <= ceiling_em
                      else int(round((floor + ceiling_em) / 2))),
        "tw_floor": max(tw, floor),
        "midpoint": mid,
        "clip_tw": _clip(tw, floor, ceiling) if ok else mid,
        "block_est": (_clip(int(row["block"]), floor, ceiling) if ok else mid) if row["dense"] else "",
    }
    return out


# ----------------------------------------------------------------------------
# the record: four sources of proved values
# ----------------------------------------------------------------------------


def generator_of(source_file: str) -> str:
    s = source_file.replace("\\", "/")
    for key, label in (("Chu_Stuckey", "Chu & Stuckey"), ("Faggioli_Bentivoglio", "Faggioli-Bentivoglio"),
                       ("Harvey", "Harvey"), ("Simonis", "Simonis"), ("Shaw", "Shaw"), ("Wilson", "Wilson"),
                       ("Miller", "Miller"), ("SCOOP", "SCOOP")):
        if f"/{key}/" in s:
            return label
    if "/Challenge/" in s:
        return "Challenge (MSW copy)"
    return "other"


def corpus_jobs() -> list[dict]:
    """Every certified corpus instance with its matrix (`learning/data/instances.csv`
    for the optimum, provenance and the record's `lb_best` / `tw_min_fill`)."""
    import pandas as pd
    from learning.dataset import enumerate_instances
    from satisfiability.mosp_solver import _solution_path
    table = pd.read_csv(INSTANCES_CSV, usecols=["instance_name", "source_file", "provenance", "optimum",
                                                "lb_best", "tw_min_fill"])
    rec = {(r.instance_name, r.source_file): r for r in table.itertuples(index=False)}
    jobs = []
    for path, inst in enumerate_instances(ROOT / "benchmarks" / "instances"):
        key = (inst.name, str(path.relative_to(ROOT)) if path.is_absolute() else str(path))
        r = rec.get(key)
        if r is None:
            continue
        # the record is the solution file: instances.csv's provenance column is stale for the
        # 125 x 125 instances closed in October (CLAUDE.md, "Stale")
        sol = json.load(open(_solution_path(inst, ROOT / "solutions")))
        prov, value = sol.get("provenance", "solution"), int(sol["mosp_value"])
        if value != int(r.optimum):
            raise RuntimeError(f"{inst.name}: instances.csv optimum {r.optimum} differs from the solution file {value}")
        jobs.append({"kind": "mosp", "group": generator_of(r.source_file), "subgroup": Path(r.source_file).stem,
                     "name": inst.name, "matrix": np.asarray(inst.matrix, dtype=np.uint8),
                     "truth": value - 1, "truth_is_upper": prov not in CERTIFIED,
                     "provenance": prov, "lb_best": int(r.lb_best) - 1, "tw_record": int(r.tw_min_fill)})
    return jobs


def ensemble_jobs() -> list[dict]:
    """The generated ensembles (`learning/data/ensemble/results.csv`, 37,800 at n <= 40, and
    `results_upward.csv`, the 50-100 campaign), certified rows only; matrices regenerate
    from their seeds inside the worker and are checked against the manifest digest."""
    import pandas as pd
    jobs = []
    for fname, group in (("results.csv", "ensemble n<=40"), ("results_upward.csv", "ensemble 50-100")):
        frame = pd.read_csv(ENSEMBLE_DIR / fname, usecols=["instance_name", "cell", "generator", "n", "m", "param",
                                                           "index", "optimum", "certified", "solve_proof",
                                                           "lb_best", "tw_min_fill", "matrix_digest"])
        frame = frame[frame.certified & frame.solve_proof.isin(("refutation", "bound"))]
        for r in frame.itertuples(index=False):
            jobs.append({"kind": "ensemble", "group": group, "subgroup": r.cell, "name": r.instance_name,
                         "cell": (r.generator, int(r.n), int(r.m), float(r.param), int(r.index)),
                         "digest": r.matrix_digest, "truth": int(r.optimum) - 1, "truth_is_upper": False,
                         "provenance": f"certified:{r.solve_proof}", "lb_best": int(r.lb_best) - 1,
                         "tw_record": int(r.tw_min_fill)})
    return jobs


def gnp_jobs() -> list[dict]:
    """The `G(n, c/n)` pilot (regenerated from its seeds, the edge count checked) and the
    middle-regime measurement (graph6 stored); proved widths only."""
    jobs = []
    with open(GNP_PILOT) as f:
        for r in csv.DictReader(f):
            if r["status"] not in ("bound", "minor", "refutation"):
                continue
            jobs.append({"kind": "gnp", "group": "G(n, c/n)", "subgroup": f"c={float(r['c']):g}",
                         "name": f"gnp_n{r['n']}_c{float(r['c']):g}_s{r['sample']}",
                         "gnp": (int(r["n"]), float(r["c"]) / int(r["n"]), int(r["seed"]), int(r["m"])),
                         "truth": int(r["width"]), "truth_is_upper": False, "provenance": f"certified:{r['status']}"})
    with open(GNP_MIDDLE) as f:
        for r in csv.DictReader(f):
            if r["status"] not in ("bound", "minor", "refutation"):
                continue
            fam = r["family"]
            jobs.append({"kind": "gnp", "group": "G(n, p) dense" if fam == "dense" else "G(n, c/n) middle",
                         "subgroup": fam, "name": f"middle_{fam}_n{r['n']}_s{r['sample']}", "g6": r["g6"],
                         "truth": int(r["width"]), "truth_is_upper": False, "provenance": f"certified:{r['status']}"})
    return jobs


def _first_collection(record: dict) -> str:
    return record["members"][0]["collection"]


def graph_jobs(max_n: int = GRAPH_MAX_N) -> list[dict]:
    """The paper's dataset outside the MOSP collections (those are the corpus above), at
    most `max_n` vertices; `solution` records are kept and flagged as upper bounds."""
    jobs = []
    with gzip.open(DATASET, "rt") as f:
        for line in f:
            r = json.loads(line)
            coll = _first_collection(r)
            if coll.startswith("MOSP") or r["n"] > max_n or r["n"] < 2:
                continue
            jobs.append({"kind": "graph", "group": coll, "subgroup": coll, "name": r["id"],
                         "edges": r["edges"], "n": r["n"], "member": r["members"][0]["name"],
                         "truth": int(r["width"]), "truth_is_upper": r["provenance"] not in CERTIFIED,
                         "provenance": r["provenance"]})
    return jobs


# ----------------------------------------------------------------------------
# the worker
# ----------------------------------------------------------------------------


def _masks_of(job: dict) -> tuple[list[int], list[int] | None]:
    if "matrix" in job:
        return masks_from_matrix(job["matrix"])
    if "cell" in job:
        from learning.canonical import matrix_digest
        from learning.ensemble import Cell, generate
        gen, n, m, param, index = job["cell"]
        inst = generate(Cell(gen, n, m, param), index)
        if matrix_digest(inst) != job["digest"]:
            raise RuntimeError(f"{job['name']}: regenerated matrix does not match the manifest digest")
        return masks_from_matrix(np.asarray(inst.matrix))
    if "gnp" in job:
        import networkx as nx
        n, p, seed, m = job["gnp"]
        graph = nx.gnp_random_graph(n, p, seed=seed)
        if graph.number_of_edges() != m:
            raise RuntimeError(f"{job['name']}: regenerated graph has {graph.number_of_edges()} edges, record {m}")
        return masks_from_edges(n, graph.edges()), None
    if "g6" in job:
        import networkx as nx
        graph = nx.from_graph6_bytes(job["g6"].encode())
        return masks_from_edges(graph.number_of_nodes(), graph.edges()), None
    return masks_from_edges(job["n"], job["edges"]), None


def _graph_lower_bound(masks: list[int], budget: float = 0.2) -> int:
    """The solver's `_lower_bound` on a plain graph (one customer per vertex, one pattern
    per edge), pathwidth units; clique search capped at `budget` seconds, no spectral."""
    from mosp.instance import MOSPInstance
    from satisfiability.mosp_solver import _lower_bound
    n = len(masks)
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if masks[u] >> v & 1]
    if not edges:
        return 0
    matrix = np.zeros((n, len(edges)), dtype=np.int8)
    for j, (u, v) in enumerate(edges):
        matrix[u, j] = matrix[v, j] = 1
    inst = MOSPInstance.from_matrix(matrix, name="graph")
    return _lower_bound(inst, clique_budget=budget, expansion_budget=budget, spectral_budget=None) - 1


def work(job: dict) -> dict:
    masks, sizes = _masks_of(job)
    lb = job.get("lb_best")
    if lb is None and job["kind"] in ("graph", "gnp"):
        lb = _graph_lower_bound(masks)
    row = estimate(masks, sizes, lb, job.get("tw_record"))
    row.update(kind=job["kind"], group=job["group"], subgroup=job["subgroup"], name=job["name"],
               truth=job["truth"], truth_is_upper=job["truth_is_upper"], provenance=job["provenance"])
    return {k: row.get(k, "") for k in FIELDS}


def run(workers: int = 8, out: Path = ESTIMATES_CSV, kinds=("mosp", "ensemble", "gnp", "graph"),
        limit: int | None = None, shuffle: bool = True) -> Path:
    jobs = []
    if "mosp" in kinds:
        jobs += corpus_jobs()
    if "ensemble" in kinds:
        jobs += ensemble_jobs()
    if "gnp" in kinds:
        jobs += gnp_jobs()
    if "graph" in kinds:
        jobs += graph_jobs()
    if shuffle:  # a fixed-seed shuffle: balances the workers, and makes a `limit` a sample
        import random
        random.Random(20261112).shuffle(jobs)
    if limit:
        jobs = jobs[:limit]
    print(f"{len(jobs)} instances", flush=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    with open(out, "w", newline="") as f, mp.get_context("spawn").Pool(workers) as pool:
        w = csv.DictWriter(f, FIELDS)
        w.writeheader()
        for i, row in enumerate(pool.imap_unordered(work, jobs, chunksize=16), 1):
            w.writerow(row)
            if i % 5000 == 0:
                print(f"{i} done, {time.time() - t0:.0f} s", flush=True)
    print(f"wrote {out} in {time.time() - t0:.0f} s", flush=True)
    return out


# ----------------------------------------------------------------------------
# the summary
# ----------------------------------------------------------------------------


def band_of(n: int) -> str:
    for lo, hi in BANDS:
        if lo <= n <= hi:
            return BAND_LABELS[(lo, hi)]
    return "?"


def load(path: Path = ESTIMATES_CSV):
    import pandas as pd
    frame = pd.read_csv(path)
    frame["band"] = frame.n.map(band_of)
    frame["certified"] = ~frame.truth_is_upper.astype(bool)
    for est in ESTIMATORS:
        col = "block_est" if est == "block" else est
        frame[f"err_{est}"] = frame[col] - frame.truth
    frame["err_lb"] = frame.lb_best - frame.truth
    frame["in_bracket"] = (frame.floor <= frame.truth) & (frame.truth <= frame.ceiling)
    frame["floor_above"] = frame.floor > frame.truth
    frame["ceiling_below"] = frame.ceiling < frame.truth
    return frame


def scores(frame, est: str) -> dict:
    e = frame[f"err_{est}"].dropna()
    if len(e) == 0:
        return {"count": 0}
    return {"count": int(len(e)), "mae": float(e.abs().mean()), "exact": float((e == 0).mean()),
            "bias": float(e.mean()), "within1": float((e.abs() <= 1).mean()), "max_abs": int(e.abs().max())}


def score_table(frame, by: list[str], ests=("recipe", "tw", "recipe_em", "clip_tw", "tw_floor", "midpoint")):
    """One row per group x estimator: MAE, exact rate, bias; and the bracket statistics."""
    import pandas as pd
    rows = []
    for key, g in frame.groupby(by, sort=False):
        key = key if isinstance(key, tuple) else (key,)
        base = dict(zip(by, key))
        base["count"] = len(g)
        base["n_median"] = float(g.n.median())
        base["in_bracket"] = float(g.in_bracket.mean())
        base["floor_above"] = float(g.floor_above.mean())
        base["ceiling_below"] = float(g.ceiling_below.mean())
        base["floor_tight"] = float((g.floor == g.truth).mean())
        base["lb_mae"] = float(g.err_lb.abs().mean()) if g.lb_best.notna().any() else float("nan")
        base["lb_exact"] = float((g.err_lb == 0).mean()) if g.lb_best.notna().any() else float("nan")
        for est in ests:
            s = scores(g, est)
            for k in ("mae", "exact", "bias"):
                base[f"{est}_{k}"] = s.get(k, float("nan"))
        rows.append(base)
    return pd.DataFrame(rows)


def kill_verdict(frame) -> dict:
    """The kill criterion by size band on the certified random-model instances:
    does the recipe beat min-fill treewidth on MAE *and* exact rate?"""
    out = {}
    for band, g in frame.groupby("band", sort=False):
        r, t = scores(g, "recipe"), scores(g, "tw")
        out[band] = {"count": r["count"], "recipe_mae": r["mae"], "tw_mae": t["mae"],
                     "recipe_exact": r["exact"], "tw_exact": t["exact"],
                     "beats": bool(r["mae"] < t["mae"] and r["exact"] > t["exact"])}
    return out


def _md(frame, floatfmt=".3f") -> str:
    cols = list(frame.columns)
    lines = ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
    for _, r in frame.iterrows():
        cells = []
        for c in cols:
            v = r[c]
            if isinstance(v, float):
                cells.append("" if math.isnan(v) else format(v, floatfmt))
            else:
                cells.append(str(v))
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines)


def summarise(path: Path = ESTIMATES_CSV, out_dir: Path = SCRATCH) -> str:
    """The report's tables (markdown, printed and written to `summary.md`) and the figure
    CSVs under `paper1/latex/data/`."""
    import pandas as pd
    frame = load(path)
    cert = frame[frame.certified]
    random_model = cert[cert.kind.isin(("ensemble", "gnp")) | cert.group.isin(("Chu & Stuckey", "Faggioli-Bentivoglio",
                                                                               "Harvey", "Simonis"))]
    parts = []
    parts.append("## Headline (certified truths, random-model generators: Chu & Stuckey, Faggioli-Bentivoglio, "
                 "Harvey, Simonis, the ensembles, G(n, p))\n")
    parts.append(_md(score_table(random_model.assign(all="all"), ["all"])))
    parts.append("\n## By size band (random-model generators)\n")
    parts.append(_md(score_table(random_model, ["band"])))
    parts.append("\n## Kill criterion by band\n")
    kv = kill_verdict(random_model)
    parts.append(_md(pd.DataFrame([{"band": b, **v} for b, v in kv.items()])))
    parts.append("\n## By generator / collection (certified truths)\n")
    parts.append(_md(score_table(cert, ["kind", "group"])))
    parts.append("\n## By generator and band\n")
    parts.append(_md(score_table(cert, ["group", "band"])))
    parts.append("\n## Dense regime (p >= 0.3), certified\n")
    dense = cert[cert.dense]
    parts.append(_md(score_table(dense, ["kind", "band"], ests=("recipe", "tw", "block", "clip_tw", "midpoint"))))
    parts.append("\n## Ceiling source shares (certified)\n")
    parts.append(_md(cert.groupby("kind").ceiling_source.value_counts(normalize=True).rename("share").reset_index()))
    parts.append("\n## Designed sets and non-random collections: signed error of the recipe and of the floor\n")
    des = frame[frame.group.isin(DESIGNED) | (frame.kind == "graph")]
    rows = []
    for grp, g in des.groupby("group", sort=False):
        rows.append({"group": grp, "count": len(g), "certified": int(g.certified.sum()),
                     "n_median": float(g.n.median()),
                     "recipe_bias": float(g.err_recipe.mean()), "recipe_mae": float(g.err_recipe.abs().mean()),
                     "floor_minus_truth": float((g.floor - g.truth).mean()),
                     "floor_above_share": float(g.floor_above.mean()),
                     "ceiling_below_share": float(g.ceiling_below.mean()),
                     "tw_bias": float(g.err_tw.mean())})
    parts.append(_md(pd.DataFrame(rows)))
    parts.append("\n## Timing (seconds per instance, median / p90 / max, by band; measured under load)\n")
    trows = []
    for band, g in frame.groupby("band", sort=False):
        trows.append({"band": band, "count": len(g), **{f"{c}_med": float(g[c].median()) for c in
                                                        ("t_floor", "t_ceiling", "t_tw", "t_block", "t_total")},
                      "t_total_p90": float(g.t_total.quantile(0.9)), "t_total_max": float(g.t_total.max())})
    parts.append(_md(pd.DataFrame(trows), ".4f"))
    text = "\n".join(parts)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "summary.md").write_text(text)
    write_figure_data(frame)
    return text


# ----------------------------------------------------------------------------
# the data behind the figures (committed under paper1/latex/data/)
# ----------------------------------------------------------------------------


def write_figure_data(frame, out_dir: Path = FIG_DATA) -> None:
    import pandas as pd
    out_dir.mkdir(parents=True, exist_ok=True)
    cert = frame[frame.certified]
    # (a) estimate against truth: every certified instance, one panel per regime
    panels = {"Chu & Stuckey": "Chu & Stuckey", "Harvey": "Harvey", "Faggioli-Bentivoglio": "Faggioli-Bentivoglio",
              "Simonis": "Simonis", "ensemble n<=40": "ensembles n <= 40", "ensemble 50-100": "ensembles 50-100",
              "G(n, c/n)": "G(n, c/n)", "G(n, p) dense": "G(n, p), p = 1/2", "Rome graphs": "Rome graphs"}
    a = cert[cert.group.isin(panels)].copy()
    a["panel"] = a.group.map(panels)
    counts = a.groupby(["panel", "truth", "recipe"]).size().rename("count").reset_index()
    counts.to_csv(out_dir / "quick_estimate_truth.csv", index=False)
    brackets = []
    for panel, g in a.groupby("panel"):
        g = g.sort_values(["n", "name"])
        for q in (0.25, 0.5, 0.75):
            r = g.iloc[min(len(g) - 1, int(q * len(g)))]
            brackets.append({"panel": panel, "name": r["name"], "n": int(r.n), "truth": int(r.truth),
                             "floor": int(r.floor), "ceiling": int(r.ceiling), "recipe": int(r.recipe),
                             "tw": int(r.tw)})
    pd.DataFrame(brackets).to_csv(out_dir / "quick_estimate_truth_brackets.csv", index=False)
    # (b) error against n: median and quartiles per band, recipe and tw
    rows = []
    for (grp, band), g in cert.groupby(["kind", "band"], sort=False):
        for est in ("recipe", "tw"):
            e = g[f"err_{est}"]
            rows.append({"kind": grp, "band": band, "n_median": float(g.n.median()), "estimator": est,
                         "count": len(g), "q25": float(e.quantile(0.25)), "median": float(e.median()),
                         "q75": float(e.quantile(0.75)), "mae": float(e.abs().mean()), "exact": float((e == 0).mean())})
    pd.DataFrame(rows).to_csv(out_dir / "quick_estimate_error.csv", index=False)
    # (c) the bracket on the G(n, c/n) cells at fixed c and the dense cells
    rows = []
    gnp = cert[cert.kind == "gnp"]
    for (sub, n), g in gnp.groupby(["subgroup", "n"]):
        rows.append({"cell": sub, "n": int(n), "count": len(g),
                     "truth_median": float(g.truth.median()), "truth_min": int(g.truth.min()), "truth_max": int(g.truth.max()),
                     "floor_median": float(g.floor.median()), "ceiling_median": float(g.ceiling.median()),
                     "recipe_median": float(g.recipe.median()), "tw_median": float(g.tw.median()),
                     "block_median": float(pd.to_numeric(g.block, errors="coerce").median()),
                     "p_mean": float(g.p.mean())})
    pd.DataFrame(rows).to_csv(out_dir / "quick_estimate_bracket.csv", index=False)
    # (d) distance from random: the designed sets and the graph collections
    rows = []
    des = frame[frame.group.isin(DESIGNED) | (frame.kind == "graph")]
    for grp, g in des.groupby("group", sort=False):
        rows.append({"group": grp, "count": len(g), "certified": int(g.certified.sum()), "n_median": float(g.n.median()),
                     "recipe_bias": float(g.err_recipe.mean()), "floor_minus_truth": float((g.floor - g.truth).mean()),
                     "q25": float(g.err_recipe.quantile(0.25)), "q75": float(g.err_recipe.quantile(0.75)),
                     "truth_is_upper": bool(g.truth_is_upper.all())})
    for pid, label in CAGES.items():
        g = frame[frame.name == pid]
        if len(g) == 1:
            r = g.iloc[0]
            rows.append({"group": label, "count": 1, "certified": 0, "n_median": float(r.n),
                         "recipe_bias": float(r.err_recipe), "floor_minus_truth": float(r.floor - r.truth),
                         "q25": float(r.err_recipe), "q75": float(r.err_recipe), "truth_is_upper": True})
    pd.DataFrame(rows).to_csv(out_dir / "quick_estimate_designed.csv", index=False)


# ----------------------------------------------------------------------------
# timing sample
# ----------------------------------------------------------------------------


def timing_sample(sizes=(100, 125), per: int = 5) -> list[dict]:
    """The four numbers and the solver's `_lower_bound` timed on corpus instances at
    100-125 customers (the record's largest), one process, under whatever load the
    machine carries."""
    from satisfiability.mosp_solver import _lower_bound
    rows = []
    jobs = [j for j in corpus_jobs() if j["matrix"].shape[0] in sizes and j["group"] == "Chu & Stuckey"]
    seen: dict[int, int] = {}
    for j in jobs:
        n = j["matrix"].shape[0]
        if seen.get(n, 0) >= per:
            continue
        seen[n] = seen.get(n, 0) + 1
        masks, sizes_ = masks_from_matrix(j["matrix"])
        row = estimate(masks, sizes_)
        from mosp.instance import MOSPInstance
        inst = MOSPInstance.from_matrix(j["matrix"], name=j["name"])
        t = time.perf_counter()
        lb = _lower_bound(inst, clique_budget=1.0, spectral_budget=None)
        row["t_lower_bound"] = time.perf_counter() - t
        row["lb_best_now"] = lb - 1
        row["name"] = j["name"]
        row["truth"] = j["truth"]
        rows.append(row)
    return rows


def extras(path: Path = ESTIMATES_CSV) -> str:
    """The numbers of `reports/quick_estimate.md` that are not in `summary.md`: where the
    bracket binds, the dense rule by realised density, the floor against `lb_best`, and
    the Chu & Stuckey classes by size."""
    frame = load(path)
    c = frame[frame.certified]
    rm = c[c.kind.isin(("ensemble", "gnp")) | c.group.isin(("Chu & Stuckey", "Faggioli-Bentivoglio",
                                                            "Harvey", "Simonis"))]
    lines = [f"random-model certified: {len(rm)}; dense share {rm.dense.mean():.3f}; in bracket {rm.in_bracket.mean():.4f}; "
             f"floor tight {(rm.floor == rm.truth).mean():.4f}; floor within 1 {((rm.truth - rm.floor) <= 1).mean():.3f}"]
    sp = rm[~rm.dense]
    ch = sp[sp.clip_tw != sp.tw]
    lines.append(f"sparse: clipping changes tw on {len(ch)} of {len(sp)} (tw < floor {int((sp.tw < sp.floor).sum())}, "
                 f"tw > ceiling {int((sp.tw > sp.ceiling).sum())}); where it binds tw MAE {ch.err_tw.abs().mean():.3f}, "
                 f"clipped MAE {ch.err_clip_tw.abs().mean():.3f}, median n {ch.n.median():.0f}")
    de = rm[rm.dense]
    for lo, hi in ((0.3, 0.4), (0.4, 0.5), (0.5, 0.6), (0.6, 1.01)):
        g = de[(de.p >= lo) & (de.p < hi)]
        lines.append(f"dense p in [{lo}, {hi}): {len(g)}; block MAE {g.err_block.abs().mean():.3f} bias "
                     f"{g.err_block.mean():+.3f}; tw MAE {g.err_tw.abs().mean():.3f} bias {g.err_tw.mean():+.3f}")
    gp = c[(c.kind == "gnp") & c.dense]
    lines.append(f"G(n, p) dense: {len(gp)}; block MAE {gp.err_block.abs().mean():.3f}; tw MAE {gp.err_tw.abs().mean():.3f}")
    lines.append(f"floor vs lb_best (random-model): floor > lb {int((rm.floor > rm.lb_best).sum())}, equal "
                 f"{int((rm.floor == rm.lb_best).sum())}, floor < lb {int((rm.floor < rm.lb_best).sum())}; "
                 f"mean truth - floor {(rm.truth - rm.floor).mean():.2f}, truth - lb {(rm.truth - rm.lb_best).mean():.2f}")
    for n, g in c[c.group == "Chu & Stuckey"].groupby("n"):
        lines.append(f"Chu & Stuckey n = {n}: {len(g)}; truth - floor {(g.truth - g.floor).mean():.1f}; truth - lb "
                     f"{(g.truth - g.lb_best).mean():.1f}; tw bias {g.err_tw.mean():+.2f}; recipe bias "
                     f"{g.err_recipe.mean():+.2f}; ceiling - truth {(g.ceiling - g.truth).mean():.1f}")
    for lo, hi in ((10, 20), (21, 30), (31, 40), (41, 50), (51, 60), (61, 75), (76, 100), (101, 125)):
        g = rm[(rm.n >= lo) & (rm.n <= hi)]
        if len(g):
            lines.append(f"n {lo}-{hi}: {len(g)}; tw MAE {g.err_tw.abs().mean():.2f} bias {g.err_tw.mean():+.2f} exact "
                         f"{(g.err_tw == 0).mean():.2f}; recipe MAE {g.err_recipe.abs().mean():.2f}")
    rec = c[c.tw_record.notna()]
    lines.append(f"ceiling_em below truth (certified): {(c.ceil_em < c.truth).mean():.3f}; our min-fill equals the "
                 f"record's on {(rec.tw == rec.tw_record).mean():.4f} of {len(rec)} (MAE {rec.err_tw.abs().mean():.3f} "
                 f"against {(rec.tw_record - rec.truth).abs().mean():.3f})")
    text = "\n".join(lines)
    (path.parent / "extras.txt").write_text(text + "\n")
    return text


def main(argv=None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("stage", choices=("run", "summarise", "timing", "extras"))
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--kinds", default="mosp,ensemble,gnp,graph")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--out", type=Path, default=ESTIMATES_CSV)
    a = ap.parse_args(argv)
    if a.stage == "run":
        run(a.workers, a.out, tuple(a.kinds.split(",")), a.limit)
    elif a.stage == "summarise":
        print(summarise(a.out))
    elif a.stage == "extras":
        print(extras(a.out))
    else:
        rows = timing_sample()
        keys = ("name", "n", "truth", "floor", "ceiling", "tw", "block", "recipe", "lb_best_now",
                "t_floor", "t_ceiling", "t_tw", "t_block", "t_total", "t_lower_bound")
        print(",".join(keys))
        for r in rows:
            print(",".join(f"{r[k]:.4f}" if isinstance(r[k], float) else str(r[k]) for k in keys))
        SCRATCH.mkdir(parents=True, exist_ok=True)
        with open(SCRATCH / "timing.csv", "w", newline="") as f:
            w = csv.DictWriter(f, keys, extrasaction="ignore")
            w.writeheader()
            w.writerows(rows)


if __name__ == "__main__":
    main()
