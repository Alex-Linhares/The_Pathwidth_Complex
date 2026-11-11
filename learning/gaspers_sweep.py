"""Gaspers' Gaussian sweep (arXiv 2611.05146, 3 November 2026) as a layout heuristic
for the open cubic cages (`reports/gaspers_cages.md`).

The paper proves `pw(G) <= c3 n + o(n)`, `c3 = (3 / 4 pi) arccos(5/6) = 0.13982`,
for every graph of maximum degree 3 (Theorem 8.1).  The object behind the proof
is a *random labelling* and a *deterministic layout rule*; this module builds
exactly those and measures them, with random restarts in place of the proof's
concentration step.  Nothing here is a bound: every width this module reports
is the vertex separation of a layout it has built, recomputed by code that
shares nothing with the construction (`vertex_separation`), and the brief's
rule is that a width below the record is *checked, never trusted*.

The construction, in the paper's words and numbering:

* **Labels** (Definition 5.2).  Independent standard normals `Z_w`, one per
  vertex; arc lengths `l(x -> y) > 0`; the directed distance `D(v, w)` is the
  shortest-path length under `l`; `X_v = sum_{D(v, w) <= Rhat} e^{-D(v, w)} Z_w`
  and `Y_v = X_v / sqrt(Var X_v)`.  *Padded* labels of degree `p`: every arc
  has length `(1/2) ln(p - 1)` and `Rhat = (R / 2) ln(p - 1)`, so the weight of
  `w` is `(p - 1)^{-dist(v, w) / 2}` on the ball of radius `R`; for `p = 3` these
  are the *geometric* labels `2^{-dist / 2}` of (2.1).  *Mixed* labels (graphs of
  minimum degree 3): `l(x -> y) = (1/2) ln(d(x) - 1)`, `Rhat = R`.  Lemma 3.4 /
  5.4: on a graph of maximum degree 3 every edge has label correlation at least
  `r_R = (2 sqrt 2 / 3)(1 - 1 / R)`; `label_correlation` lets a test confirm it.
* **Plain sweep** (Lemma 4.1).  Sort by label.  `pw <= max_t |outer frontier of
  S_t|` and `pw <= max_t |inner frontier of S_t|`, where `S_t = {v : y_v <= t}`,
  the outer frontier is the set of vertices above `t` with a neighbour at or
  below it and the inner frontier the set of vertices at or below `t` with a
  neighbour above it.  As layouts: the inner bound is the vertex separation of
  the label order, the outer bound that of its reverse.
* **Median-switched layout** (Lemma 8.4, maximum degree 3 only).  Inner frontiers
  while the threshold is negative, outer frontiers while it is positive, and a
  *connector* at zero: with `U = inner frontier of S_0`, `W = outer frontier of
  S_0`, `D` the degree-3 vertices all of whose neighbours lie across zero,
  `U' = U \\ D`, `W' = W \\ D`, the bags are `C_{-1} = U cup (D cap W)` and
  `C_j = D cup {u in U' : some neighbour of u in W' is not among q_1..q_{j-1}}
  cup {q_1..q_j}` for an order `q_1..q_k` of `W'` satisfying Lemma 8.3's
  inequality (8.3), `j - c(j) <= max(0, k - |P|) + 1`, which `connector_order`
  builds by the lemma's own proof (split at closed sets, else complete an
  item).  The width is `max(|inner| below 0, |outer| above 0, max(L0, L0') + 1)`
  with `L0 = |U'| + |D|`, `L0' = |W'| + |D|` (8.2).  The decomposition is turned
  into a layout by first-bag order (`decomposition_to_layout`), which never
  increases the width.  `switch` moves the threshold off the median; the paper
  switches at 0 by sign symmetry, and other quantiles are a heuristic of ours.

What is *not* here: the derandomisation of Section 10 (method of conditional
expectations over a finite rational distribution, `n^{2 + o(1)}`), and the
series-parallel reductions of Lemma 4.5 (the cages have minimum degree 3).

Usage:
    nice -n 19 python3 -m learning.gaspers_sweep --restarts 4000      # the five cages
    nice -n 19 python3 -m learning.gaspers_sweep --ids pwc-16021 --restarts 200
    python -m pytest tests/test_gaspers_sweep.py -q
"""
from __future__ import annotations

import argparse
import gzip
import heapq
import json
import math
import os
import subprocess
import sys
import time
from collections import deque
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATASET = ROOT / "paper1" / "data" / "dataset" / "pathwidth_dataset.jsonl.gz"
OUT = ROOT / "reports" / "scratch" / "gaspers_cages"
PATHWIDTH_C = ROOT / "pathwidth_solver" / "cli" / "pathwidth"

C3 = 3 / (4 * math.pi) * math.acos(5 / 6)            # Theorem 1.1(a), 0.13982
C_STAR = 3 / (2 * math.pi) * math.asin(1 / 3)        # Theorem 3.1, 0.16226 (cut sweep)
R_STAR = 2 * math.sqrt(2) / 3                        # the cubic edge correlation 0.9428

# the five open cubic cages (dataset ids), and the named 4-, 5-, 6-regular graphs the brief lists
CAGES = {
    "pwc-15968": "Foster (90)",
    "pwc-15936": "Biggs-Smith (102)",
    "pwc-16006": "Ljubljana (112)",
    "pwc-15932": "Balaban 11-cage (112)",
    "pwc-16064": "Tutte 12-cage (126)",
}
OTHERS = {
    "pwc-15953": "Dejter (112)",
    "pwc-15941": "BubbleSort_5 (120)",
    "pwc-16016": "NStar_5 (120)",
    "pwc-16023": "OddGraph_5 (126)",
}
# small cubic graphs with certified pathwidth, for the tests
CERTIFIED_CUBIC = {
    "pwc-16021": ("Petersen", 10, 5),
    "pwc-15984": ("Heawood", 14, 6),
    "pwc-16027": ("Pappus", 18, 7),
    "pwc-16010": ("McGee", 24, 8),
    "pwc-16065": ("Tutte-Coxeter", 30, 9),
    "pwc-15950": ("Coxeter", 28, 9),
    "pwc-15931": ("Balaban 10-cage", 70, 15),
}


# ------------------------------------------------------------------ graphs

def adjacency(n: int, edges) -> list[list[int]]:
    adj = [[] for _ in range(n)]
    for a, b in edges:
        if a == b:
            continue
        adj[a].append(b)
        adj[b].append(a)
    return [sorted(set(x)) for x in adj]


def degrees(adj) -> list[int]:
    return [len(x) for x in adj]


def load_record(record_id: str, dataset: Path = DATASET) -> dict:
    """One dataset record by id (edges, width, floor, layout, members)."""
    with gzip.open(dataset, "rt") as f:
        for line in f:
            r = json.loads(line)
            if r["id"] == record_id:
                return r
    raise KeyError(record_id)


def record_name(r: dict) -> str:
    m = r["members"][0]
    return m["name"] if isinstance(m, dict) else str(m)


# ------------------------------------------------------------------ the independent check

def vertex_separation(adj, layout) -> int:
    """Textbook vertex separation of `layout` (Kinnersley): the largest number of
    vertices at or before a position with a neighbour after it.  Checks that
    `layout` is a permutation.  Shares nothing with the constructions below."""
    n = len(adj)
    pos = [-1] * n
    for i, v in enumerate(layout):
        if not 0 <= v < n or pos[v] >= 0:
            raise ValueError("layout is not a permutation")
        pos[v] = i
    if any(p < 0 for p in pos):
        raise ValueError("layout is not a permutation")
    best = 0
    for i in range(n):
        count = 0
        for u in layout[: i + 1]:
            if any(pos[w] > i for w in adj[u]):
                count += 1
        best = max(best, count)
    return best


def vertex_separation_fast(adj, layout) -> int:
    """The same number, in O(n + m), used inside the restart loop; the reported
    width of every result is rechecked with `vertex_separation`."""
    n = len(adj)
    unplaced = [len(x) for x in adj]
    placed = [False] * n
    active = 0
    best = 0
    for v in layout:
        placed[v] = True
        for w in adj[v]:
            if placed[w]:
                unplaced[w] -= 1
                unplaced[v] -= 1
                if unplaced[w] == 0:
                    active -= 1
        if unplaced[v] > 0:
            active += 1
        if active > best:
            best = active
    return best


# ------------------------------------------------------------------ labels (Definition 5.2)

def weight_matrix(adj, R: float, kind: str = "padded", p: int | None = None) -> np.ndarray:
    """Rows `C[v, w] = e^{-D(v, w)} / sqrt(sum_w e^{-2 D(v, w)})` over the ball
    `D(v, w) <= Rhat`.  `kind = "padded"`: arc length `(1/2) ln(p - 1)`, `p` the
    maximum degree unless given, `Rhat = (R / 2) ln(p - 1)` (weight `(p - 1)^{-dist / 2}`
    on the ball of radius `R`).  `kind = "mixed"`: arc length `(1/2) ln(d(tail) - 1)`,
    `Rhat = R`; needs minimum degree 3.  `Y = C @ Z` then has unit variances."""
    n = len(adj)
    deg = degrees(adj)
    if kind == "padded":
        if p is None:
            p = max(3, max(deg) if n else 3)
        if p < 3:
            raise ValueError("padded labels need p >= 3")
        step = 0.5 * math.log(p - 1)
        length = [step] * n
        rhat = R * step + 1e-12
    elif kind == "mixed":
        if n and min(deg) < 3:
            raise ValueError("mixed labels need minimum degree 3")
        length = [0.5 * math.log(d - 1) for d in deg]
        rhat = R + 1e-12
    else:
        raise ValueError(kind)
    C = np.zeros((n, n))
    for v in range(n):
        dist = {v: 0.0}
        heap = [(0.0, v)]
        while heap:
            d, x = heapq.heappop(heap)
            if d > dist.get(x, math.inf):
                continue
            for y in adj[x]:
                nd = d + length[x]
                if nd <= rhat and nd < dist.get(y, math.inf):
                    dist[y] = nd
                    heapq.heappush(heap, (nd, y))
        for w, d in dist.items():
            C[v, w] = math.exp(-d)
        C[v] /= math.sqrt(float(np.dot(C[v], C[v])))
    return C


def label_correlation(C: np.ndarray, u: int, v: int) -> float:
    """`Corr(Y_u, Y_v) = sum_w C[u, w] C[v, w]` (the overlap of Lemma 3.4)."""
    return float(np.dot(C[u], C[v]))


def labels(C: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    return C @ rng.standard_normal(C.shape[0])


# ------------------------------------------------------------------ frontiers and sweeps

def frontiers(adj, y, t: float):
    """`(inner, outer)` frontier sets of `S_t = {v : y_v <= t}`."""
    below = [yv <= t for yv in y]
    inner = {u for u in range(len(adj)) if below[u] and any(not below[x] for x in adj[u])}
    outer = {v for v in range(len(adj)) if not below[v] and any(below[x] for x in adj[v])}
    return inner, outer


def plain_sweep(adj, y):
    """The two layouts of Lemma 4.1: the label order (width = max inner frontier)
    and its reverse (width = max outer frontier).  Returns `(order, reversed, inner_width, outer_width)`."""
    order = sorted(range(len(adj)), key=lambda v: (y[v], v))
    rev = order[::-1]
    return order, rev, vertex_separation_fast(adj, order), vertex_separation_fast(adj, rev)


def connector_order(Q: list[int], items: dict[int, frozenset]) -> list[int]:
    """Lemma 8.3: an order `q_1..q_k` of `Q` with `j - c(j) <= max(0, k - |P|) + 1`
    for all `j`, where `c(j)` counts the items whose endpoints all lie in
    `{q_1..q_j}`.  Built as in the lemma's proof: a closed set (a union of
    components of the graph whose edges are the 2-endpoint items) splits the
    instance, the part of smaller excess first; inside a component each new
    element completes an item with one endpoint already placed."""
    if not Q:
        return []
    qset = set(Q)
    # components of Q under the 2-endpoint items
    nbr = {q: set() for q in Q}
    for e in items.values():
        e = [x for x in e if x in qset]
        if len(e) == 2:
            nbr[e[0]].add(e[1])
            nbr[e[1]].add(e[0])
    seen = set()
    comps = []
    for q in Q:
        if q in seen:
            continue
        comp, stack = [], [q]
        seen.add(q)
        while stack:
            x = stack.pop()
            comp.append(x)
            for z in nbr[x]:
                if z not in seen:
                    seen.add(z)
                    stack.append(z)
        comps.append(comp)
    def excess(comp):
        cs = set(comp)
        return len(comp) - sum(1 for e in items.values() if e <= cs)
    comps.sort(key=excess)                       # Case 1, applied repeatedly: smaller excess first
    order = []
    for comp in comps:                           # Case 2 inside a component
        cs = set(comp)
        placed = set()
        start = comp[0]
        placed.add(start)
        order.append(start)
        frontier = deque([start])
        while len(placed) < len(comp):
            x = frontier.popleft()
            for z in sorted(nbr[x]):
                if z in cs and z not in placed:
                    placed.add(z)
                    order.append(z)
                    frontier.append(z)
    assert len(order) == len(Q)
    return order


def connector_counts(order: list[int], items: dict[int, frozenset]) -> list[int]:
    """`c(j)` for `0 <= j <= k` (used by the tests to check (8.3))."""
    out = [0]
    placed = set()
    for q in order:
        placed.add(q)
        out.append(sum(1 for e in items.values() if e <= placed))
    return out


def median_switched_decomposition(adj, y, switch: float = 0.0):
    """The bags of Lemma 8.5 for the threshold `switch` (the paper: 0).  Needs
    maximum degree 3.  Returns `(bags, width, details)` with `width = max |bag| - 1`."""
    n = len(adj)
    if n and max(degrees(adj)) > 3:
        raise ValueError("the median-switched layout is for maximum degree 3")
    order = sorted(range(n), key=lambda v: (y[v], v))
    below = [y[v] <= switch for v in range(n)]
    ell = sum(below)
    U, W = frontiers(adj, y, switch)
    D = {v for v in range(n) if len(adj[v]) == 3 and all(below[x] != below[v] for x in adj[v])}
    Uq, Wq = U - D, W - D
    items = {u: frozenset(x for x in adj[u] if x in Wq) for u in Uq}
    items = {u: e for u, e in items.items() if e}
    for u, e in items.items():
        assert len(e) <= 2
    q = connector_order(sorted(Wq), items)
    bags = []
    # inner bags A_i = {v_i} u inner(T_{i-1}), i <= ell
    placed = set()
    for i in range(ell):
        v = order[i]
        inner = {u for u in placed if any(x not in placed for x in adj[u])}
        bags.append(frozenset(inner | {v}))
        placed.add(v)
    # connector
    bags.append(frozenset(U | (D & W)))
    present = []
    for j in range(len(q) + 1):
        prev = set(q[:max(0, j - 1)])
        alive = {u for u, e in items.items() if not e <= prev}
        bags.append(frozenset(D | alive | set(q[:j])))
    # outer bags A_i = {v_i} u outer(T_i), i > ell
    placed = set(order[:ell])
    for i in range(ell, n):
        v = order[i]
        placed.add(v)
        outer = {w for w in range(n) if w not in placed and any(x in placed for x in adj[w])}
        bags.append(frozenset(outer | {v}))
    width = max((len(b) for b in bags), default=0) - 1
    L0, L0p = len(Uq) + len(D), len(Wq) + len(D)
    return bags, width, {"ell": ell, "L0": L0, "L0p": L0p, "D": len(D), "U": len(U), "W": len(W)}


def is_path_decomposition(adj, bags) -> bool:
    n = len(adj)
    first, last = [None] * n, [None] * n
    for i, b in enumerate(bags):
        for v in b:
            if first[v] is None:
                first[v] = i
            last[v] = i
    if any(f is None for f in first):
        return False
    for i, b in enumerate(bags):
        for v in range(n):
            if first[v] <= i <= last[v] and v not in b:
                return False
    for v in range(n):
        for w in adj[v]:
            if not any(v in b and w in b for b in bags):
                return False
    return True


def decomposition_to_layout(n: int, bags, tiebreak=None) -> list[int]:
    """Order the vertices by the first bag containing them (ties by `tiebreak`,
    a per-vertex key, default the vertex index).  The vertex separation of this
    layout is at most the width of the decomposition: for the prefix before `v`
    with first bag `f`, every prefix vertex with a later neighbour lies in bag `f`
    together with `v`."""
    first = [None] * n
    for i, b in enumerate(bags):
        for v in b:
            if first[v] is None:
                first[v] = i
    key = (lambda v: (first[v], tiebreak[v], v)) if tiebreak is not None else (lambda v: (first[v], v))
    return sorted(range(n), key=key)


def median_switched_layout(adj, y, switch: float = 0.0):
    """The median-switched decomposition as a layout.  Returns `(layout, width_of_layout, width_of_bags)`."""
    bags, w, _ = median_switched_decomposition(adj, y, switch)
    layout = decomposition_to_layout(len(adj), bags, tiebreak=list(y))
    return layout, vertex_separation_fast(adj, layout), w


# ------------------------------------------------------------------ restarts

def sweep(adj, restarts: int, seed: int = 0, radii=(1, 2, 3, 4, 5, 6), kinds=("padded",),
          switches=(0.5,), median=True, log_every: int = 0):
    """Random restarts of the sweep.  For each restart: labels at a radius drawn
    from `radii`, the two plain layouts, and (maximum degree 3) the
    median-switched layout at each quantile in `switches` (0.5 = the paper's
    median).  Returns the best layout found, its width (rechecked by
    `vertex_separation`), and per-rule statistics."""
    n = len(adj)
    cubic = n == 0 or max(degrees(adj)) <= 3
    rng = np.random.default_rng(seed)
    mats = {(k, R): weight_matrix(adj, R, kind=k) for k in kinds for R in radii}
    keys = list(mats)
    best = {"width": None, "layout": None, "rule": None, "R": None, "kind": None, "restart": None}
    stats = {}                                   # rule -> [count, sum, min, hist]
    def note(rule, w, layout, R, kind, i):
        s = stats.setdefault(rule, {"count": 0, "sum": 0, "min": None, "hist": {}})
        s["count"] += 1
        s["sum"] += w
        s["min"] = w if s["min"] is None else min(s["min"], w)
        s["hist"][w] = s["hist"].get(w, 0) + 1
        if best["width"] is None or w < best["width"]:
            best.update(width=w, layout=list(layout), rule=rule, R=R, kind=kind, restart=i)
    t0 = time.time()
    for i in range(restarts):
        kind, R = keys[i % len(keys)]
        y = labels(mats[(kind, R)], rng)
        order, rev, wi, wo = plain_sweep(adj, y)
        note("plain-inner", wi, order, R, kind, i)
        note("plain-outer", wo, rev, R, kind, i)
        if cubic and median:
            for qt in switches:
                t = float(np.quantile(y, qt)) if qt != 0.5 else float(np.median(y))
                layout, w, wb = median_switched_layout(adj, y, switch=t)
                note(f"switched@{qt:g}", w, layout, R, kind, i)
                assert w <= wb, (w, wb)      # first-bag order never widens the decomposition
        if log_every and (i + 1) % log_every == 0:
            print(f"  restart {i + 1}/{restarts}: best {best['width']} ({best['rule']}, R={best['R']}) {time.time() - t0:.1f}s",
                  file=sys.stderr, flush=True)
    if best["layout"] is not None:
        check = vertex_separation(adj, best["layout"])
        assert check == best["width"], (check, best["width"])
        best["checked_width"] = check
    for s in stats.values():
        s["mean"] = s["sum"] / s["count"]
        s["hist"] = dict(sorted(s["hist"].items()))
    return best, stats


# ------------------------------------------------------------------ the C program

def graph6(n: int, edges) -> str:
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from((a, b) for a, b in edges if a != b)
    return nx.to_graph6_bytes(G, nodes=range(n), header=False).decode().strip()


def write_closing_order(path: Path, layout) -> None:
    """The C program's `-u` file: a closing order, the vertex closed first first.
    A layout's closing order is its reverse (the suffix after position `i` is the
    closed set whose boundary is the layout's count at `i`)."""
    path.write_text(" ".join(str(v) for v in layout[::-1]) + "\n")


def run_c(n: int, edges, seed_layout, seconds: int, workdir: Path, tag: str, floor: int | None = None,
          nice: int = 19) -> dict:
    """`pathwidth -u <closing order> -t seconds -l -v` on the graph; returns the
    width, status, printed layout (rechecked here) and the stderr line."""
    workdir.mkdir(parents=True, exist_ok=True)
    seed_file = workdir / f"{tag}_seed.txt"
    write_closing_order(seed_file, seed_layout)
    cmd = ["nice", "-n", str(nice), str(PATHWIDTH_C), "-u", str(seed_file), "-t", str(seconds), "-l", "-v"]
    if floor is not None:
        cmd += ["-L", str(floor)]
    t0 = time.time()
    proc = subprocess.run(cmd, input=graph6(n, edges) + "\n", capture_output=True, text=True)
    out = {"cmd": " ".join(cmd), "stdout": proc.stdout, "stderr": proc.stderr, "seconds": time.time() - t0,
           "returncode": proc.returncode}
    for line in proc.stdout.splitlines():
        if line.startswith("pathwidth "):
            parts = line.split()
            out["width"], out["status"] = int(parts[1]), parts[2]
        elif line.startswith("layout "):
            out["layout"] = [int(x) for x in line.split()[1:]]
    if "layout" in out:
        out["checked_width"] = vertex_separation(adjacency(n, edges), out["layout"])
    (workdir / f"{tag}_c.log").write_text(json.dumps({k: v for k, v in out.items() if k != "layout"}, indent=1)
                                          + "\nlayout " + " ".join(map(str, out.get("layout", []))) + "\n")
    return out


# ------------------------------------------------------------------ driver

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ids", nargs="*", default=list(CAGES))
    ap.add_argument("--restarts", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--radii", type=int, nargs="*", default=[1, 2, 3, 4, 5, 6])
    ap.add_argument("--switches", type=float, nargs="*", default=[0.5])
    ap.add_argument("--c-seconds", type=int, default=0, help="run the C program from the best layout for this long (0: skip)")
    ap.add_argument("--out", default=str(OUT))
    args = ap.parse_args(argv)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for rid in args.ids:
        r = load_record(rid)
        n, edges = r["n"], [tuple(e) for e in r["edges"]]
        adj = adjacency(n, edges)
        deg = degrees(adj)
        name = CAGES.get(rid) or OTHERS.get(rid) or record_name(r)
        rec_w = vertex_separation(adj, r["layout"]) if r.get("layout") else None
        print(f"{rid} {name}: n={n} m={len(edges)} degrees {min(deg)}..{max(deg)} record width {r['width']}"
              f" (layout rechecked: {rec_w}) floor {r.get('floor')}", flush=True)
        t0 = time.time()
        best, stats = sweep(adj, args.restarts, seed=args.seed, radii=tuple(args.radii),
                            switches=tuple(args.switches), log_every=max(1, args.restarts // 10))
        row = {"id": rid, "name": name, "n": n, "m": len(edges), "record_width": r["width"], "floor": r.get("floor"),
               "restarts": args.restarts, "sweep_width": best["width"], "sweep_rule": best["rule"], "sweep_R": best["R"],
               "sweep_seconds": round(time.time() - t0, 1), "stats": stats}
        (out / f"{rid}_sweep_layout.txt").write_text(" ".join(map(str, best["layout"])) + "\n")
        print(f"  sweep best {best['width']} by {best['rule']} at R={best['R']} (restart {best['restart']}); "
              + "; ".join(f"{k}: min {v['min']} mean {v['mean']:.2f}" for k, v in stats.items()), flush=True)
        if args.c_seconds:
            c = run_c(n, edges, best["layout"], args.c_seconds, out, rid)
            row.update(c_width=c.get("width"), c_status=c.get("status"), c_checked=c.get("checked_width"),
                       c_seconds=round(c["seconds"], 1), c_stderr=c["stderr"].strip())
            print(f"  C program from the sweep layout: width {c.get('width')} {c.get('status')} "
                  f"(rechecked {c.get('checked_width')}) in {c['seconds']:.0f}s; {c['stderr'].strip()}", flush=True)
            if c.get("layout"):
                (out / f"{rid}_c_layout.txt").write_text(" ".join(map(str, c["layout"])) + "\n")
        rows.append(row)
        (out / f"{rid}_result.json").write_text(json.dumps(row, indent=1))
    (out / "results.json").write_text(json.dumps(rows, indent=1))
    return rows


if __name__ == "__main__":
    main()
