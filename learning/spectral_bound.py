"""Spectral (Laplacian eigenvalue) lower bounds on vertex separation = pathwidth,
measured on the corpus through the bound harness (2026-11-10).

**Question.** Every degree, clique and degeneracy bound the solver computes is
a bound on `treewidth + 1` and cannot see `pw > tw`, which holds on 131 of the
338 bound-gap instances (`reports/ml_nature.md` §6, §21). Eigenvalue bounds
are not of that kind a priori. This module states the spectral separator
inequalities as theorems, turns them into a bound on vertex separation by the
prefix-separator argument, checks them against exact pathwidth on every small
graph, and measures them on every certified instance. Nothing here reaches the
solver; nothing is re-solved.

**Notation.** `G` connected on `n` vertices, Laplacian `L = D − A` with
eigenvalues `0 = μ₁ < μ₂ ≤ … ≤ μₙ`, maximum degree `Δ`, and `S(c)` the sum of
the `c` largest degrees (so `S(c) ≤ Δ c`). A *separator triple* `(C, A, B)` is
a partition of `V` with no edge between `A` and `B`; write `a, b, c` for the
sizes. For a disconnected graph the bound is the maximum over components
(`pw` is), since `μ₂ = 0` says nothing.

**Theorem 1 (Mohar & Poljak 1993, Thm 2.8, as quoted by Helmberg, Mohar,
Poljak & Rendl 1995 eq. (21) and Díaz, Petit & Serna 2002 Thm 9.4; here with
`S(c)` in place of `Δ c`).** For every separator triple,

    S(c) ≥ μ₂ · ((a + b) − (a − b)² / n),       equivalently
    c ≥ 4 μ₂ a b / (Δ n − μ₂ (a + b))  when S(c) is replaced by Δ c.

*Proof.* `x = 1_A − 1_B` has `Σx = a − b`, so by Rayleigh on the projection
orthogonal to `1`: `xᵀLx ≥ μ₂ (xᵀx − (Σx)²/n) = μ₂ ((a+b) − (a−b)²/n)`. And
`xᵀLx = Σ_{uv∈E} (x_u − x_v)² = e(A, C) + e(B, C)` (no `A–B` edges; `A–A`,
`B–B`, `C–C` edges contribute 0) `≤ Σ_{v∈C} deg(v) ≤ S(c)`. Multiplying out
with `a + b + c = n` gives the quoted form. ∎

**Theorem 2 (Helmberg, Mohar, Poljak & Rendl 1995, Theorem 11, eq. (20);
their Theorem 1 at `cut(A, B) = 0`, i.e. Haemers' interlacing bound).** For
every separator triple of a graph that is not complete,

    c ≥ 4 μₙ μ₂ a b / (n (μₙ − μ₂)²).

**Theorem 3 (Gu & Liu 2022, as Lemma 4.1 of Gima, Hanaka, Noro, Ono & Otachi
2025).** For every separator triple of a non-complete graph with an edge,

    c ≥ 2 μ₂ · min(a, b) / (μₙ − μ₂).

Theorems 2 and 3 are cited, not re-proved here; both are checked on every
separator triple of every connected graph on at most 7 vertices
(`check_inequalities`, 0 violations required) before anything is stated on
them, and Theorem 1 with them.

**Theorem 4 (the prefix-separator bound on vertex separation).** Let `σ` be a
layout of `G` with vertex separation `w`, `V_t` its first `t` vertices,
`C_t = {v ∉ V_t : N(v) ∩ V_t ≠ ∅}` (so `|C_t| ≤ w` by definition of vertex
separation), `A_t = V_t`, `B_t = V ∖ (V_t ∪ C_t)`. Then `(C_t, A_t, B_t)` is a
separator triple with `a = t`, `b = n − t − c`, so with

    feasible(c, t) := Theorems 1–3 all hold at (c, a = t, b = n − t − c),
    c_t := min { c ∈ [0, n − t] : feasible(c, t) },         (c = n − t always is)
    spec(G) := max_{1 ≤ t ≤ n − 1} c_t,

we have `vs(G) = pw(G) ≥ spec(G)` and `MOSP ≥ spec(G) + 1`. *Proof.* `|C_t|`
is feasible at `t`, so `w ≥ |C_t| ≥ c_t` for every `t`. ∎  (Kinnersley 1992
for `vs = pw`, `lean/MOSPFormalization/VSEquivPW.lean`; `MOSP = pw + 1`,
`MOSPGraph.lean`.) The suffix-side and prefix-side conventions give the same
value because the three inequalities are symmetric in `a ↔ b`.

**Two consequences, stated before measuring.**

(i) *The spectral bound never exceeds Harper's exact bound.* For any `S` with
`|S| = t`, `(N(S) ∖ S, S, V ∖ N[S])` is a separator triple, so
`c_t ≤ |N(S) ∖ S|` and `c_t ≤ min_{|S| = t} |N(S) ∖ S| = f(t) − t` in the
notation of `satisfiability/expansion_bound.py`; hence
`spec(G) ≤ max_t (f(t) − t)`, Harper's bound (`exists_closedNbhd_card_le`).
The spectral bound is a *relaxation of the same minimum*: on the 320 gap
instances where Harper's ceiling is below the optimum
(`reports/obstruction_search.md` §0), the whole-graph spectral value cannot
reach the optimum either. What is left to measure is the slack, and the
bound on induced subgraphs and minors, where Harper was never searched.

(ii) *The Theorem-1 part is a treewidth bound.* `c_t^{(1)} ≤ c_bal :=
min{c : S(c) ≥ μ₂ (n − c)}` for every `t` (the balanced requirement is the
strongest instance of Theorem 1), and Gima et al. 2025 Theorem 3.4, whose
proof reads verbatim with `S(|S|)` for `Δ |S|`, gives `tw + 1 ≥ c_bal`. So
`spec₁(G) ≤ tw + 1` in pathwidth units: in optimum units the Theorem-1
spectral floor is at most `tw + 2`, one above the treewidth ceiling of
`reports/ml_nature.md` §24, and reaches `tw + 2` only where the Gima bound
is tight for treewidth. Theorems 2 and 3 are not covered by this argument
and are measured against `tw + 1` directly.

**Families.** `graph` (the theorem on `G`, per component); `peel` (every
induced subgraph along the degeneracy peeling: delete a minimum-degree
vertex, repeat — a subgraph, `pw` monotone); `minor` (every minor of the
contraction-degeneracy sequence, `learning.bound_harness.contraction_minors`;
`pw` is minor-monotone). The candidate the harness sees is the best of the
three plus one.

**Numerics.** `numpy.linalg.eigvalsh` on the dense Laplacian; `μ₂` is lowered
and `μₙ` raised by `TOL` before use, which weakens every inequality
(each right-hand side is increasing in `μ₂` and decreasing in `μₙ`), so
rounding can only lose a unit, never claim one.

**Kill criterion (written before measuring).** The family is dead if the best
spectral floor over the three families never exceeds the best floor on
record (`best` of `reports/scratch/obstruction_search/08_map/map.csv`, the
loop0013 result) on any of the 338 gap instances.

**In the solver since 2026-11-10** (the owner's decision, after the
measurement above): `satisfiability.mosp_solver._lower_bound` takes
`max(existing, spec + 1)` with `spec` the best of the three families under a
budget (`_spectral_floor`), and records `spectral` in `BOUND_SOURCES` when it
is the strict maximum. The component **rests on the cited theorems and on the
corpus validation, not on Lean**: Theorems 1–3 are not formalised
(`paper1/todo.md`, "Formalise the spectral lower bound in Lean"), as the
clique bound was not before 2026-09-27. The validation is `--stage solver`
below, re-run whenever the corpus grows, like the other components
(`reports/spectral_floor_integration.md`); the graph side is
`pathwidth_solver/bench/spectral_floor.py`, which passes the value to the C
program as `-L`.

Usage:
    nice -n 19 python3 -m learning.spectral_bound --stage check --workers 8     # small graphs vs exact pw, Harper
    nice -n 19 python3 -m learning.spectral_bound --stage validity --workers 8  # every certified instance (harness)
    nice -n 19 python3 -m learning.spectral_bound --stage tables                # reports/scratch/spectral_bound/tables.md
    nice -n 19 python3 -m learning.spectral_bound --stage solver --workers 8    # _lower_bound old vs new on every certified corpus instance
    python3 -m learning.spectral_bound --stage one --key <matrix key>
    python3 -m pytest tests/test_spectral_bound.py -q
"""

from __future__ import annotations

import argparse
import itertools
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "reports" / "scratch" / "spectral_bound"
VALUES_CSV = OUT / "values.csv.gz"
CHECK_CSV = OUT / "check_small.csv.gz"
INEQ_CSV = OUT / "check_inequalities.csv"
TABLES_MD = OUT / "tables.md"
MAP_CSV = ROOT / "reports" / "scratch" / "obstruction_search" / "08_map" / "map.csv"

TOL = 1e-7
SLACK = 1e-9
ALL = ("mp", "hmpr", "gl")
FAMILIES = ("graph", "peel", "minor")


# ----------------------------------------------------------------------------
# spectra
# ----------------------------------------------------------------------------


def laplacian_extremes(graph) -> tuple[float, float]:
    """`(μ₂, μₙ)` of the Laplacian of `graph` (0, 0 on fewer than 2 vertices)."""
    import networkx as nx

    n = graph.number_of_nodes()
    if n < 2:
        return 0.0, 0.0
    lap = nx.laplacian_matrix(graph, nodelist=list(graph.nodes)).toarray().astype(float)
    vals = np.linalg.eigvalsh(lap)
    return float(max(vals[1], 0.0)), float(vals[-1])


def top_degree_sums(degrees) -> np.ndarray:
    """`S(c)` for `c = 0..n`: the sum of the `c` largest degrees."""
    d = np.sort(np.asarray(list(degrees), dtype=float))[::-1]
    return np.concatenate([[0.0], np.cumsum(d)])


# ----------------------------------------------------------------------------
# the inequalities and the prefix bound
# ----------------------------------------------------------------------------


def mp_holds(c: int, a: int, b: int, n: int, mu2: float, S: np.ndarray) -> bool:
    """Theorem 1 at `(c, a, b)`: `S(c) ≥ μ₂ ((a + b) − (a − b)²/n)`."""
    return S[c] + SLACK >= mu2 * ((a + b) - (a - b) ** 2 / n)


def hmpr_holds(c: int, a: int, b: int, n: int, mu2: float, mun: float) -> bool:
    """Theorem 2 at `(c, a, b)`: `c ≥ 4 μₙ μ₂ a b / (n (μₙ − μ₂)²)`."""
    if mun - mu2 <= 0:
        return True  # complete graph: the theorem is not stated; no constraint
    return c + SLACK >= 4.0 * mun * mu2 * a * b / (n * (mun - mu2) ** 2)


def gl_holds(c: int, a: int, b: int, n: int, mu2: float, mun: float) -> bool:
    """Theorem 3 at `(c, a, b)`: `c ≥ 2 μ₂ min(a, b) / (μₙ − μ₂)`."""
    if mun - mu2 <= 0:
        return True
    return c + SLACK >= 2.0 * mu2 * min(a, b) / (mun - mu2)


def feasible(c: int, a: int, b: int, n: int, mu2: float, mun: float, S: np.ndarray,
             use=ALL) -> bool:
    if "mp" in use and not mp_holds(c, a, b, n, mu2, S):
        return False
    if "hmpr" in use and not hmpr_holds(c, a, b, n, mu2, mun):
        return False
    if "gl" in use and not gl_holds(c, a, b, n, mu2, mun):
        return False
    return True


def prefix_separator_bound(n: int, mu2: float, mun: float, degrees, use=ALL) -> tuple[int, int]:
    """Theorem 4: `spec = max_t c_t` on a connected graph with the given
    spectrum and degrees. Returns `(spec, t*)`, `t*` a prefix size attaining
    it. `μ₂` is lowered and `μₙ` raised by `TOL` (weakening every inequality)."""
    if n < 2:
        return 0, 0
    mu2 = max(mu2 - TOL * max(1.0, mu2), 0.0)
    mun = mun + TOL * max(1.0, mun)
    S = top_degree_sums(degrees)
    best, best_t = 0, 0
    for t in range(1, n):
        for c in range(0, n - t + 1):
            if feasible(c, t, n - t - c, n, mu2, mun, S, use):
                if c > best:
                    best, best_t = c, t
                break
    return best, best_t


def spectral_graph_bound(graph, use=ALL) -> tuple[int, dict]:
    """`spec(G)`: the maximum of Theorem 4 over the components. The dict
    carries the component's `n`, `μ₂`, `μₙ`, `Δ`, `t*` and the Gima values."""
    import networkx as nx

    best, info = 0, {"n": graph.number_of_nodes(), "mu2": 0.0, "mun": 0.0, "delta": 0,
                     "t_star": 0, "gima1": 0.0, "gima2": 0.0, "comp_n": 0}
    for comp in nx.connected_components(graph):
        if len(comp) < 2:
            continue
        sub = graph.subgraph(comp)
        mu2, mun = laplacian_extremes(sub)
        degs = [d for _, d in sub.degree()]
        value, t_star = prefix_separator_bound(len(comp), mu2, mun, degs, use)
        delta = max(degs)
        gima1 = len(comp) * mu2 / (delta + mu2) if delta + mu2 > 0 else 0.0
        gima2 = 2 * len(comp) * mu2 / (3 * mun - mu2) if 3 * mun - mu2 > 0 else 0.0
        if value > best or info["comp_n"] == 0:
            best = max(best, value)
            info.update(mu2=mu2, mun=mun, delta=delta, t_star=t_star, comp_n=len(comp),
                        gima1=max(info["gima1"], gima1), gima2=max(info["gima2"], gima2))
        else:
            info["gima1"] = max(info["gima1"], gima1)
            info["gima2"] = max(info["gima2"], gima2)
    return best, info


def peel_sequence(graph):
    """The induced subgraphs along the degeneracy peeling, the graph first:
    delete a minimum-degree vertex (lowest label on ties), repeat."""
    import networkx as nx

    working = nx.Graph(graph)
    yield working
    while working.number_of_nodes() > 2:
        vertex = min(working.nodes, key=lambda x: (working.degree(x), x))
        working = nx.Graph(working)
        working.remove_node(vertex)
        yield working


def spectral_bounds(graph, families=FAMILIES, use=ALL, deadline: float | None = None) -> dict:
    """Every family on one graph. Values are in pathwidth units; `best` is
    their maximum. `peel_n` / `minor_n` are the vertex counts of the subgraph
    / minor attaining the family's value; `censored` is set if the deadline
    cut a sequence short (what was seen is still valid)."""
    from learning.bound_harness import contraction_minors

    out: dict = {"censored": False}
    value, info = spectral_graph_bound(graph, use)
    out.update(graph=value, graph_t=info["t_star"], mu2=info["mu2"], mun=info["mun"],
               delta=info["delta"], gima1=info["gima1"], gima2=info["gima2"])
    best = value
    for family, seq in (("peel", peel_sequence), ("minor", contraction_minors)):
        if family not in families:
            continue
        fam_best, fam_n = value, graph.number_of_nodes()
        for i, h in enumerate(seq(graph)):
            if i == 0:
                continue
            if deadline is not None and time.monotonic() > deadline:
                out["censored"] = True
                break
            v, _ = spectral_graph_bound(h, use)
            if v > fam_best:
                fam_best, fam_n = v, h.number_of_nodes()
        out[family] = fam_best
        out[f"{family}_n"] = fam_n
        best = max(best, fam_best)
    out["best"] = best
    return out


# ----------------------------------------------------------------------------
# the harness candidate (optimum units)
# ----------------------------------------------------------------------------


def cand_spectral(graph, matrix, budget):
    """`learning.bound_harness` candidate: `spec + 1` over the three families,
    with the per-family values, the Theorem-1-only whole-graph value and the
    Gima treewidth values as diagnostics."""
    deadline = budget.started + budget.seconds if budget is not None else None
    res = spectral_bounds(graph, deadline=deadline)
    mp_only, _ = spectral_graph_bound(graph, use=("mp",))
    info = {"graph": res["graph"] + 1, "peel": res["peel"] + 1, "minor": res["minor"] + 1,
            "mp_graph": mp_only + 1, "peel_n": res["peel_n"], "minor_n": res["minor_n"],
            "mu2": round(res["mu2"], 6), "mun": round(res["mun"], 6), "delta": res["delta"],
            "gima1": round(res["gima1"], 4), "gima2": round(res["gima2"], 4),
            "seed": res["graph"] + 1}
    if res["censored"] and budget is not None:
        budget.exhausted = True
    return res["best"] + 1, info


CANDIDATE_NAME = "spectral"


def register() -> None:
    from learning import bound_harness

    bound_harness.CANDIDATES[CANDIDATE_NAME] = cand_spectral
    bound_harness.BUDGET_SECONDS[CANDIDATE_NAME] = 60.0
    bound_harness.BUDGET_SUBPROBLEMS[CANDIDATE_NAME] = 10 ** 9


# ----------------------------------------------------------------------------
# small-graph checks: the inequalities, exact pathwidth, exact Harper
# ----------------------------------------------------------------------------


def harper_exact(graph) -> int:
    """Harper's bound `max_t min_{|S|=t} |N(S) ∖ S|` by enumeration (pathwidth
    units), the maximum over components as `pw` is; components of ≤ 20 vertices."""
    import networkx as nx

    if graph.number_of_nodes() and nx.number_connected_components(graph) > 1:
        return max(_harper_connected(graph.subgraph(c)) for c in nx.connected_components(graph))
    return _harper_connected(graph)


def _harper_connected(graph) -> int:
    nodes = list(graph.nodes)
    n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    closed = [1 << i for i in range(n)]
    for u, v in graph.edges:
        closed[idx[u]] |= 1 << idx[v]
        closed[idx[v]] |= 1 << idx[u]
    best_per_t = [None] * (n + 1)
    for S in range(1 << n):
        nb = 0
        t = 0
        m = S
        while m:
            i = (m & -m).bit_length() - 1
            nb |= closed[i]
            t += 1
            m &= m - 1
        boundary = (nb & ~S).bit_count()
        if best_per_t[t] is None or boundary < best_per_t[t]:
            best_per_t[t] = boundary
    return max(b for b in best_per_t if b is not None)


def check_inequalities(max_n: int = 7) -> dict:
    """Theorems 1–3 on every separator triple `(C, A, B)` with `A, B ≠ ∅` of
    every connected graph on 2..`max_n` vertices (the atlas); returns counts and
    violations (must be empty)."""
    import networkx as nx

    checked, violations, graphs = 0, [], 0
    for g in nx.graph_atlas_g():
        n = g.number_of_nodes()
        if n < 2 or n > max_n or not nx.is_connected(g):
            continue
        graphs += 1
        complete = g.number_of_edges() == n * (n - 1) // 2
        mu2, mun = laplacian_extremes(g)
        mu2w = max(mu2 - TOL * max(1.0, mu2), 0.0)
        munw = mun + TOL * max(1.0, mun)
        S = top_degree_sums(d for _, d in g.degree())
        adj = {v: set(g[v]) for v in g}
        nodes = list(g.nodes)
        for assign in itertools.product((0, 1, 2), repeat=n):
            A = [v for v, k in zip(nodes, assign) if k == 1]
            B = [v for v, k in zip(nodes, assign) if k == 2]
            if not A or not B:
                continue
            if any(adj[u] & set(B) for u in A):
                continue
            a, b = len(A), len(B)
            c = n - a - b
            checked += 1
            if not mp_holds(c, a, b, n, mu2w, S):
                violations.append(("mp", nx.to_graph6_bytes(g, header=False).decode().strip(), assign))
            if not complete:
                if not hmpr_holds(c, a, b, n, mu2w, munw):
                    violations.append(("hmpr", nx.to_graph6_bytes(g, header=False).decode().strip(), assign))
                if not gl_holds(c, a, b, n, mu2w, munw):
                    violations.append(("gl", nx.to_graph6_bytes(g, header=False).decode().strip(), assign))
    return {"graphs": graphs, "triples": checked, "violations": violations}


def _check_one(graph6: str) -> dict:
    import networkx as nx

    from fixed_parameter_algorithm.pathwidth import compute_pathwidth

    g = nx.from_graph6_bytes(graph6.encode())
    n = g.number_of_nodes()
    pw, _ = compute_pathwidth(g)
    res = spectral_bounds(g)
    row = {"graph6": graph6, "n": n, "edges": g.number_of_edges(), "pw": pw,
           "spec_graph": res["graph"], "spec_peel": res["peel"], "spec_minor": res["minor"],
           "spec_best": res["best"], "mu2": round(res["mu2"], 6), "mun": round(res["mun"], 6),
           "delta": res["delta"], "gima1": round(res["gima1"], 4)}
    row["harper"] = harper_exact(g) if n <= 16 else -1
    mp_only, _ = spectral_graph_bound(g, use=("mp",))
    row["spec_mp_graph"] = mp_only
    return row


def small_graph_stream(sizes: tuple[int, ...], random_sizes: tuple[int, ...], per_size: int,
                       seed: int = 0):
    """graph6 strings: the atlas (every graph to 7 vertices), geng's connected
    graphs at the given sizes, and `per_size` random connected graphs per
    random size at three densities."""
    import networkx as nx

    for g in nx.graph_atlas_g():
        if g.number_of_nodes() >= 2:
            yield nx.to_graph6_bytes(g, header=False).decode().strip()
    for n in sizes:
        proc = subprocess.run(["nauty-geng", "-q", "-c", str(n)], capture_output=True, text=True,
                              check=True)
        for line in proc.stdout.splitlines():
            if line:
                yield line
    rng = np.random.default_rng(seed)
    for n in random_sizes:
        for p in (0.15, 0.3, 0.5):
            made = 0
            while made < per_size:
                g = nx.gnp_random_graph(n, p, seed=int(rng.integers(2 ** 31)))
                if nx.is_connected(g):
                    made += 1
                    yield nx.to_graph6_bytes(g, header=False).decode().strip()


def run_check(workers: int = 8, sizes=(8, 9), random_sizes=(10, 11, 12, 13, 14), per_size=40,
              out_csv: Path = CHECK_CSV) -> "pd.DataFrame":
    import pandas as pd

    OUT.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    ineq = check_inequalities(7)
    pd.DataFrame(ineq["violations"], columns=["theorem", "graph6", "assignment"]).to_csv(INEQ_CSV, index=False)
    print(f"[spectral] inequalities: {ineq['graphs']} graphs, {ineq['triples']} triples, "
          f"{len(ineq['violations'])} violations, {time.monotonic() - started:.0f}s", flush=True)
    if ineq["violations"]:
        raise SystemExit("Theorem 1–3 violated on a small graph; stop.")
    rows = []
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for i, row in enumerate(pool.map(_check_one, small_graph_stream(sizes, random_sizes, per_size),
                                         chunksize=64), start=1):
            rows.append(row)
            if i % 20000 == 0:
                print(f"[spectral] check {i} graphs in {time.monotonic() - started:.0f}s", flush=True)
    frame = pd.DataFrame(rows)
    frame.to_csv(out_csv, index=False)
    bad = frame[frame["spec_best"] > frame["pw"]]
    bad_h = frame[(frame["harper"] >= 0) & (frame["spec_graph"] > frame["harper"])]
    print(f"[spectral] {len(frame)} graphs, {len(bad)} above pw, {len(bad_h)} above Harper, "
          f"{time.monotonic() - started:.0f}s", flush=True)
    return frame


def check_summary(frame: "pd.DataFrame") -> "pd.DataFrame":
    import pandas as pd

    rows = []
    for n, part in frame.groupby("n"):
        h = part[part["harper"] >= 0]
        rows.append({
            "n": int(n), "graphs": len(part),
            "spec_best > pw (must be 0)": int((part["spec_best"] > part["pw"]).sum()),
            "spec_graph > Harper (must be 0)": int((h["spec_graph"] > h["harper"]).sum()),
            "graph tight": float((part["spec_graph"] == part["pw"]).mean()),
            "peel tight": float((part["spec_peel"] == part["pw"]).mean()),
            "minor tight": float((part["spec_minor"] == part["pw"]).mean()),
            "best tight": float((part["spec_best"] == part["pw"]).mean()),
            "Harper tight": float((h["harper"] == h["pw"]).mean()) if len(h) else np.nan,
            "mean pw − best": float((part["pw"] - part["spec_best"]).mean()),
            "max pw − best": int((part["pw"] - part["spec_best"]).max()),
            "mean Harper − graph": float((h["harper"] - h["spec_graph"]).mean()) if len(h) else np.nan,
            "mp_graph = graph": float((part["spec_mp_graph"] == part["spec_graph"]).mean()),
        })
    return pd.DataFrame(rows)


# ----------------------------------------------------------------------------
# the corpus: validity through the harness, then the gap analysis
# ----------------------------------------------------------------------------


def run_validity(workers: int = 8, sources=("corpus", "campaign", "upward"), limit=None,
                 wall=None, out_csv: Path = VALUES_CSV):
    from learning import bound_harness

    register()
    OUT.mkdir(parents=True, exist_ok=True)
    return bound_harness.run_validity(workers=workers, names=(CANDIDATE_NAME,), out_csv=out_csv,
                                      limit=limit, sources=tuple(sources), wall=wall)


def load_frame(values_csv: Path = VALUES_CSV) -> "pd.DataFrame":
    """The harness join (optimum, lb_best, tw1, reference, is_gap) plus the
    loop0013 map (best floor on record, floor0, Harper at cap 12, the
    expansion ceiling, exact treewidth flag) for corpus rows."""
    import pandas as pd

    from learning import bound_harness

    register()
    frame = bound_harness.load_values(values_csv)
    if MAP_CSV.exists():
        m = pd.read_csv(MAP_CSV)[["instance_name", "best", "best_family", "floor0", "harper12",
                                  "e_ceiling", "tw1_exact", "minor", "is_gap338", "collection",
                                  "cs_d", "gap_best"]]
        m = m.rename(columns={"best": "floor_record", "minor": "minor_record", "tw1_exact": "tw1_exact_map"})
        frame = frame.merge(m, on="instance_name", how="left")
        corpus = frame["source"] == "corpus"
        frame.loc[~corpus, ["floor_record", "floor0", "harper12", "e_ceiling", "is_gap338"]] = np.nan
    return frame


def gap_tables(frame: "pd.DataFrame") -> dict:
    import pandas as pd

    gap = frame[(frame["source"] == "corpus") & (frame["is_gap"])].copy()
    s = gap["spectral"].astype(float)
    out = {}
    cols = {"lb_best": gap["lb_best"], "reference max(lb_best, tw+1)": gap["reference"],
            "floor0 (loop0013 §1, on record before the search)": gap["floor0"],
            "best floor on record after loop0013": gap["floor_record"],
            "Harper at cap 12": gap["harper12"], "tw + 1 (tw_lo)": gap["tw1"]}
    rows = []
    for name, ref in cols.items():
        d = s - ref.astype(float)
        rows.append({"against": name, "gap instances": int(ref.notna().sum()),
                     "spectral above": int((d > 0).sum()), "equal": int((d == 0).sum()),
                     "below": int((d < 0).sum()), "max excess": float(d.max()),
                     "mean (spectral − ref)": float(d.mean())})
    out["against"] = pd.DataFrame(rows)
    fam = pd.DataFrame({
        "family": ["graph", "peel", "minor", "best", "Theorem 1 only, graph"],
        "mean optimum − value": [float((gap["optimum"] - gap[c]).mean())
                                 for c in ("spectral_graph", "spectral_peel", "spectral_minor",
                                           "spectral", "spectral_mp_graph")],
        "max optimum − value": [int((gap["optimum"] - gap[c]).max())
                                for c in ("spectral_graph", "spectral_peel", "spectral_minor",
                                          "spectral", "spectral_mp_graph")],
        "tight": [int((gap[c] == gap["optimum"]).sum())
                  for c in ("spectral_graph", "spectral_peel", "spectral_minor",
                            "spectral", "spectral_mp_graph")],
        "> lb_best": [int((gap[c] > gap["lb_best"]).sum())
                      for c in ("spectral_graph", "spectral_peel", "spectral_minor",
                                "spectral", "spectral_mp_graph")],
        "> tw + 1": [int((gap[c] > gap["tw1"]).sum())
                     for c in ("spectral_graph", "spectral_peel", "spectral_minor",
                               "spectral", "spectral_mp_graph")],
    })
    out["families"] = fam
    gap["band"] = pd.cut(gap["n_customers"], bins=[0, 20, 30, 40, 60, 75, 100, 134],
                         labels=["9–20", "21–30", "31–40", "41–60", "61–75", "76–100", "101–134"])
    out["bands"] = gap.groupby("band", observed=True).agg(
        instances=("optimum", "size"),
        mean_opt=("optimum", "mean"),
        mean_spectral=("spectral", "mean"),
        mean_floor_record=("floor_record", "mean"),
        mean_tw1=("tw1", "mean"),
        above_record=("spectral", lambda v: int((v > gap.loc[v.index, "floor_record"]).sum())),
        above_lb_best=("spectral", lambda v: int((v > gap.loc[v.index, "lb_best"]).sum())),
        mean_shortfall=("spectral", lambda v: float((gap.loc[v.index, "optimum"] - v).mean())),
    ).reset_index()
    resid = gap[gap["gap_best"] > 0].sort_values("instance_name")
    out["residual"] = resid[["instance_name", "n_customers", "optimum", "lb_best", "tw1", "floor_record",
                             "harper12", "e_ceiling", "spectral", "spectral_graph", "spectral_peel",
                             "spectral_minor", "spectral_mp_graph", "spectral_mu2", "spectral_delta",
                             "spectral_gima1", "spectral_minor_n", "spectral_seconds"]]
    exact = gap[gap["tw_exact"].astype(str).str.lower() == "true"]
    out["tw_ceiling"] = pd.DataFrame([{
        "gap instances with exact tw": len(exact),
        "pw > tw there (optimum > tw + 1)": int((exact["optimum"] > exact["tw1"]).sum()),
        "spectral > tw + 1": int((exact["spectral"] > exact["tw1"]).sum()),
        "spectral graph > tw + 1": int((exact["spectral_graph"] > exact["tw1"]).sum()),
        "Theorem-1 graph > tw + 1": int((exact["spectral_mp_graph"] > exact["tw1"]).sum()),
        "Theorem-1 graph > tw + 2 (must be 0)": int((exact["spectral_mp_graph"] > exact["tw1"] + 1).sum()),
        "max spectral − (tw + 1)": float((exact["spectral"] - exact["tw1"]).max()),
    }])
    # the whole corpus and the generated sources: spectral vs floors
    rows = []
    for src, part in frame.groupby("source"):
        v = part["spectral"].astype(float)
        rows.append({"source": src, "rows": len(part),
                     "above optimum (must be 0)": int((v > part["optimum"]).sum()),
                     "tight": float((v == part["optimum"]).mean()),
                     "> lb_best": float((v > part["lb_best"]).mean()),
                     "> reference": float((v > part["reference"]).mean()),
                     "> tw + 1": float((v > part["tw1"]).mean()),
                     "mean optimum − spectral": float((part["optimum"] - v).mean()),
                     "max optimum − spectral": float((part["optimum"] - v).max()),
                     "median s": float(part["spectral_seconds"].median()),
                     "max s": float(part["spectral_seconds"].max()),
                     "core-h": float(part["spectral_seconds"].sum() / 3600)})
    out["sources"] = pd.DataFrame(rows)
    return out


def write_tables(values_csv: Path = VALUES_CSV, check_csv: Path = CHECK_CSV,
                 tables_md: Path = TABLES_MD) -> dict:
    import pandas as pd

    from learning import bound_harness

    frame = load_frame(values_csv)
    tabs = gap_tables(frame)
    validity = bound_harness.validity_table(frame)
    parts = ["# Spectral bound: the tables\n",
             f"*Generated {time.strftime('%Y-%m-%d %H:%M')} from `{values_csv.relative_to(ROOT)}`"
             f" ({len(frame)} rows) by `python3 -m learning.spectral_bound --stage tables`.*\n",
             "## Harness validity table (optimum units; `spectral` = best of the three families + 1)\n",
             bound_harness._md(validity),
             "## Per source\n", bound_harness._md(tabs["sources"]),
             "## The 338 gap instances: spectral against every floor on record\n",
             bound_harness._md(tabs["against"]),
             "## The 338 gap instances: by family\n", bound_harness._md(tabs["families"]),
             "## The 338 gap instances: by size band\n", bound_harness._md(tabs["bands"]),
             "## The treewidth ceiling on the gap instances with exact treewidth\n",
             bound_harness._md(tabs["tw_ceiling"]),
             "## The residual dense instances (best floor on record below the optimum)\n",
             bound_harness._md(tabs["residual"])]
    if check_csv.exists():
        chk = pd.read_csv(check_csv)
        parts += ["## Small graphs against exact pathwidth and exact Harper (pathwidth units)\n",
                  bound_harness._md(check_summary(chk))]
    tables_md.parent.mkdir(parents=True, exist_ok=True)
    tables_md.write_text("\n\n".join(parts) + "\n")
    tabs["validity"] = validity
    return tabs


# ----------------------------------------------------------------------------
# the solver's floor, old against new, on every certified corpus instance
# ----------------------------------------------------------------------------

SOLVER_OUT = ROOT / "reports" / "scratch" / "spectral_floor"
SOLVER_CSV = SOLVER_OUT / "solver_floor.csv"


def _solver_job(args) -> dict:
    """`_lower_bound` without and with the spectral component on one certified
    instance, each timed, with the spectral floor's own seconds."""
    path, index, optimum, provenance = args
    from mosp.instance import MOSPInstance
    from satisfiability.mosp_solver import _lower_bound, _spectral_floor
    from customer_inter.customer_graph import build_customer_graph

    inst = MOSPInstance.from_benchmark_file(Path(path).resolve())[index]
    t0 = time.monotonic()
    old = _lower_bound(inst, spectral_budget=None)
    t1 = time.monotonic()
    info: dict = {}
    new = _lower_bound(inst, info=info)
    t2 = time.monotonic()
    graph = build_customer_graph(inst)
    t3 = time.monotonic()
    spectral = _spectral_floor(graph)
    t4 = time.monotonic()
    return {"instance_name": inst.name, "source_file": str(Path(path)),
            "n_customers": inst.n_customers, "n_patterns": inst.n_patterns,
            "optimum": optimum, "provenance": provenance,
            "lb_old": old, "lb_new": new, "spectral": spectral, "source": info.get("source", ""),
            "seconds_old": round(t1 - t0, 4), "seconds_new": round(t2 - t1, 4),
            "seconds_spectral": round(t4 - t3, 4)}


def run_solver(workers: int = 8, out_csv: Path = SOLVER_CSV, limit: int | None = None) -> "pd.DataFrame":
    """Every certified corpus instance (`solutions/*.json` with a `certified:*`
    provenance), largest first. The result CSV has `lb_old`, `lb_new`,
    `spectral` and the seconds; `summarise_solver` reads it."""
    import json

    import pandas as pd

    from learning.dataset import enumerate_instances
    from satisfiability.mosp_solver import _solution_path, SOLUTIONS_DIR

    SOLVER_OUT.mkdir(parents=True, exist_ok=True)
    jobs = []
    positions: dict[Path, int] = {}
    for path, inst in enumerate_instances():
        index = positions.get(path, 0)
        positions[path] = index + 1
        sp = _solution_path(inst, SOLUTIONS_DIR)
        if not sp.exists():
            continue
        sol = json.loads(sp.read_text())
        prov = sol.get("provenance", "solution")
        if not prov.startswith("certified:"):
            continue
        jobs.append((str(path), index, int(sol["mosp_value"]), prov, inst.n_customers))
    jobs.sort(key=lambda j: -j[4])
    if limit is not None:
        jobs = jobs[:limit]
    print(f"[spectral] solver floor on {len(jobs)} certified corpus instances", flush=True)
    started = time.monotonic()
    rows = []
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for i, row in enumerate(pool.map(_solver_job, [j[:4] for j in jobs], chunksize=4), start=1):
            rows.append(row)
            if i % 500 == 0:
                print(f"[spectral] solver {i}/{len(jobs)} in {time.monotonic() - started:.0f}s", flush=True)
    frame = pd.DataFrame(rows)
    frame.to_csv(out_csv, index=False)
    print(f"[spectral] wrote {out_csv.relative_to(ROOT)} ({len(frame)} rows, "
          f"{time.monotonic() - started:.0f}s)", flush=True)
    return frame


def summarise_solver(frame: "pd.DataFrame") -> str:
    """The validation numbers in one Markdown block: violations (must be 0),
    tightness, mean gap, where the component raised the floor, seconds."""
    import pandas as pd

    opt = frame["optimum"]
    lines = [f"instances: {len(frame)} (certified corpus)",
             f"lb_new above optimum (must be 0): {int((frame['lb_new'] > opt).sum())}",
             f"spectral above optimum (must be 0): {int((frame['spectral'] > opt).sum())}",
             f"lb_old above optimum (must be 0): {int((frame['lb_old'] > opt).sum())}",
             f"lb_new below lb_old (must be 0): {int((frame['lb_new'] < frame['lb_old']).sum())}",
             f"tight, old: {(frame['lb_old'] == opt).mean():.4f} ({int((frame['lb_old'] == opt).sum())})",
             f"tight, new: {(frame['lb_new'] == opt).mean():.4f} ({int((frame['lb_new'] == opt).sum())})",
             f"mean gap, old: {(opt - frame['lb_old']).mean():.4f}",
             f"mean gap, new: {(opt - frame['lb_new']).mean():.4f}",
             f"max gap, old: {int((opt - frame['lb_old']).max())}; new: {int((opt - frame['lb_new']).max())}",
             f"raised above the old floor: {int((frame['lb_new'] > frame['lb_old']).sum())} "
             f"(by {sorted(set((frame['lb_new'] - frame['lb_old'])[frame['lb_new'] > frame['lb_old']].tolist()))})",
             f"newly tight: {int(((frame['lb_new'] == opt) & (frame['lb_old'] < opt)).sum())}",
             f"source = spectral: {int((frame['source'] == 'spectral').sum())}",
             f"seconds per call, spectral alone: median {frame['seconds_spectral'].median():.3f}, "
             f"p90 {frame['seconds_spectral'].quantile(0.9):.3f}, max {frame['seconds_spectral'].max():.2f} "
             f"({frame.loc[frame['seconds_spectral'].idxmax(), 'instance_name']}), "
             f"total {frame['seconds_spectral'].sum() / 60:.1f} min",
             f"seconds per call, _lower_bound old: median {frame['seconds_old'].median():.3f}, max {frame['seconds_old'].max():.2f}; "
             f"new: median {frame['seconds_new'].median():.3f}, max {frame['seconds_new'].max():.2f}"]
    gap = frame[(opt - frame["lb_old"]) >= 2]
    lines.append(f"bound-gap instances (optimum - lb_old >= 2): {len(gap)}; raised there: "
                 f"{int((gap['lb_new'] > gap['lb_old']).sum())}")
    raised = frame[frame["lb_new"] > frame["lb_old"]].sort_values("instance_name")
    lines.append("")
    lines.append("| instance | n | optimum | lb_old | lb_new | spectral |")
    lines.append("|---|---:|---:|---:|---:|---:|")
    for r in raised.itertuples():
        lines.append(f"| {r.instance_name} | {r.n_customers} | {r.optimum} | {r.lb_old} | {r.lb_new} | {r.spectral} |")
    return "\n".join(lines)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--stage", choices=("check", "validity", "tables", "one", "solver"), required=True)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--sources", default="corpus,campaign,upward")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--wall", type=float, default=None)
    ap.add_argument("--sizes", default="8,9", help="geng sizes for the check")
    ap.add_argument("--key", default=None)
    args = ap.parse_args()
    if args.stage == "check":
        frame = run_check(args.workers, sizes=tuple(int(x) for x in args.sizes.split(",") if x))
        print(check_summary(frame).to_string())
    elif args.stage == "validity":
        frame = run_validity(args.workers, sources=tuple(args.sources.split(",")), limit=args.limit,
                             wall=args.wall)
        from learning import bound_harness

        print(bound_harness.validity_table(frame).to_string())
    elif args.stage == "tables":
        tabs = write_tables()
        for k, v in tabs.items():
            print(f"\n== {k}\n{v.to_string()}")
    elif args.stage == "solver":
        import pandas as pd

        frame = run_solver(args.workers, limit=args.limit) if not SOLVER_CSV.exists() or args.limit \
            else pd.read_csv(SOLVER_CSV)
        summary = summarise_solver(frame)
        (SOLVER_OUT / "solver_floor_summary.md").write_text(summary + "\n")
        print(summary)
    else:
        from learning.bound_harness import Budget, graph_from_matrix
        from learning.extremal import matrix_from_key

        matrix = matrix_from_key(args.key)
        value, info = cand_spectral(graph_from_matrix(matrix), matrix, Budget(seconds=60))
        print(value, info)


if __name__ == "__main__":
    main()
