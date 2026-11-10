"""An LP relaxation of the nested-chain encoding of vertex separation, with Harper's
inequalities, as a lower bound that rounds up — and the ceiling of that route.

**The integer program** (`build_model`, `relax=False`). For a graph `G` on `n`
vertices with adjacency masks `adj`, levels `t = 1 .. n - 1`:

    y[v,t] in {0,1}        v is in the prefix of size t
    s[v,t] in [0,1]        v is charged as a boundary vertex at level t
    b                      the width

    sum_v y[v,t] = t                                  (size)
    y[v,t] <= y[v,t+1]                                (nesting)
    s[v,t] >= y[u,t] - y[v,t]   for every edge uv     (boundary: v outside with u inside)
    sum_v s[v,t] <= b                                 (width)
    minimise b.

*Claim: its optimum is the vertex separation `vs(G)`.* A feasible point gives
nested sets `S_1 ⊂ … ⊂ S_{n-1}` with `|S_t| = t` (size and nesting; nesting
with equal cardinalities differing by one means each `S_{t+1}` adds exactly
one vertex), so `S_t` are the prefixes of a layout `σ`; at level `t` every
vertex `v ∉ S_t` with a neighbour `u ∈ S_t` has `s[v,t] ≥ 1`, so
`sum_v s[v,t] ≥ |N(S_t) ∖ S_t|` and `b ≥ max_t |N(S_t) ∖ S_t| = vs(σ) ≥ vs(G)`.
Conversely a layout of vertex separation `vs(G)` with `s` the exact boundary
indicator is feasible with `b = vs(G)`. Levels `0` and `n` have empty
boundary and are omitted. `stage atlas` checks this against the subset DP on
every graph of the networkx atlas (`n ≤ 7`).

**The LP relaxation** (`relax=True`) and why it is Harper's bound and no more.
The point `y[v,t] = t/n`, `s[v,t] = c(t)/n` satisfies size, nesting, every
edge inequality (right-hand side 0) and the Harper cuts `sum_v s[v,t] ≥ c(t)`
for any `c(t) ≤ Φ(t)`, with `b = max_t c(t)`; and every feasible point has
`b ≥ sum_v s[v,t] ≥ c(t)`. So **the LP with Harper cuts has optimum exactly
`max_t c(t)`** — Harper's integer bound when `c = Φ` — and without them 0.
The uniform point also satisfies every cut family below (each is proved
valid and shown satisfied by the uniform point in `reports/chain_lp.md`),
so every formulation here returns `max_t c(t)`; the measurement confirms it
to solver precision.

**The ceiling of the route** (`lagrangian_exact`, `mixture_upper`). The only
link between `b` and the chain is per level, `b ≥ sum_v s[v,t]`. For any
family of inequalities in `(y, s)` alone — up to the full integer hull
`conv{(y^σ, s^σ) : σ a layout}` — the LP is `min over mixtures λ of layouts
of max_t sum_σ λ_σ B_σ(t)`, where `B_σ(t)` is the boundary of `σ`'s
`t`-prefix; by LP duality for this finite zero-sum game that equals

    L(G) = max over μ in the simplex on levels of min over layouts σ of sum_t μ(t) B_σ(t),

the Lagrangian dual of `vs = min_σ max_t B_σ(t)`. `Harper ≤ L(G) ≤ vs(G)`
(a point mass on `t*` gives Harper; `B_σ ≤ vs` throughout). The route can
beat Harper on an instance only if `L(G) > Harper(G)` there. `L` is computed
exactly at `n ≤ 20` by cutting planes on `μ` with a subset DP as the oracle
(`min_σ sum_t μ(t) B_σ(t)` is a shortest path in the subset lattice), and
bounded above at any `n` by the mixture LP over a pool of layouts: a pool
whose best mixture has `max_t` average boundary `≤ Harper` proves
`L = Harper` and kills every `(y, s)`-cut on that instance.

Usage:
    python -m learning.chain_lp --stage atlas                    # exactness and cut validity, every atlas graph
    python -m learning.chain_lp --stage lp64 --workers 4         # the 64 gap instances at 30-50
    python -m learning.chain_lp --stage ceiling --workers 4      # L(G) exact at n <= 20, mixtures at 30-50
    python -m learning.chain_lp --stage cost                     # LP size and time at 100-125
    python -m learning.chain_lp --stage pairs --workers 4        # L >= Harper + 1/2 by a two-level SAT refutation, the 64
    python -m learning.chain_lp --stage residual --workers 4 --seconds 180   # the record's 11 open instances, floor-raising target
    python -m pytest tests/test_chain_lp.py -q
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np
import pandas as pd
import scipy.sparse as sp
from scipy.optimize import LinearConstraint, Bounds, linprog, milp

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "reports" / "scratch" / "chain_lp"
REFINE_CSV = ROOT / "reports" / "scratch" / "checkpoint" / "refine" / "refine.csv"
MAP_CSV = ROOT / "reports" / "scratch" / "obstruction_search" / "08_map" / "map.csv"
UNCOVERED_CSV = ROOT / "reports" / "scratch" / "obstruction_search" / "08_map" / "uncovered.csv"
LEVELS_CSV = ROOT / "reports" / "scratch" / "obstruction_search" / "03_sat" / "levels.csv"
SOLUTIONS_DIR = ROOT / "solutions"

DP_MAX_N = 20
CUT_FAMILIES = ("harper", "persist", "upper", "clique")

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# graphs
# ----------------------------------------------------------------------------


def edges_of(adj: list[int]) -> list[tuple[int, int]]:
    return [(u, v) for u in range(len(adj)) for v in range(u + 1, len(adj)) if adj[u] >> v & 1]


def adjacency_from_graph(graph) -> list[int]:
    nodes = sorted(graph.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [0] * len(nodes)
    for u, v in graph.edges():
        if u == v:
            continue
        adj[idx[u]] |= 1 << idx[v]
        adj[idx[v]] |= 1 << idx[u]
    return adj


def boundary_of(adj: list[int], S: int) -> int:
    """`|N(S) ∖ S|`, the outer boundary of the vertex set `S` (a mask)."""
    nb = 0
    m = S
    while m:
        bit = m & -m
        nb |= adj[bit.bit_length() - 1]
        m ^= bit
    return (nb & ~S).bit_count()


def profile_of(adj: list[int], order: list[int]) -> list[int]:
    """`B_σ(t)` for `t = 1 .. n - 1`: the outer boundary of every proper prefix."""
    out = []
    S = 0
    for v in order[:-1]:
        S |= 1 << v
        out.append(boundary_of(adj, S))
    return out


def vertex_separation_of(adj: list[int], order: list[int]) -> int:
    return max(profile_of(adj, order), default=0)


def maximal_cliques(adj: list[int]) -> list[list[int]]:
    import networkx as nx

    g = nx.Graph()
    g.add_nodes_from(range(len(adj)))
    g.add_edges_from(edges_of(adj))
    return [sorted(c) for c in nx.find_cliques(g) if len(c) >= 3]


# ----------------------------------------------------------------------------
# the model
# ----------------------------------------------------------------------------


class ChainModel:
    """The chain IP/LP in `scipy` form. Variables: `y[v,t]` at `(t-1)*n + v`,
    `s[v,t]` at `n(n-1) + (t-1)*n + v`, `b` last; levels `t = 1 .. n - 1`."""

    def __init__(self, adj: list[int], relax: bool, cuts: dict | None = None):
        self.adj = adj
        self.n = n = len(adj)
        self.relax = relax
        self.cuts = dict(cuts or {})
        self.L = n - 1
        self.ny = n * self.L
        self.nvar = 2 * self.ny + 1
        self.rows: list[tuple[list[int], list[float], float, float]] = []  # (idx, coef, lo, hi)
        self.families: dict[str, int] = {}
        self._build()

    # indices
    def y(self, v: int, t: int) -> int:
        return (t - 1) * self.n + v

    def s(self, v: int, t: int) -> int:
        return self.ny + (t - 1) * self.n + v

    @property
    def b(self) -> int:
        return 2 * self.ny

    def _add(self, family: str, idx, coef, lo, hi) -> None:
        self.rows.append((list(idx), list(coef), lo, hi))
        self.families[family] = self.families.get(family, 0) + 1

    def _build(self) -> None:
        n, L = self.n, self.L
        E = edges_of(self.adj)
        for t in range(1, L + 1):
            self._add("size", [self.y(v, t) for v in range(n)], [1.0] * n, t, t)
            if t < L:
                for v in range(n):
                    self._add("nesting", [self.y(v, t), self.y(v, t + 1)], [1.0, -1.0], -np.inf, 0.0)
            for u, v in E:
                self._add("edge", [self.y(u, t), self.y(v, t), self.s(v, t)], [1.0, -1.0, -1.0], -np.inf, 0.0)
                self._add("edge", [self.y(v, t), self.y(u, t), self.s(u, t)], [1.0, -1.0, -1.0], -np.inf, 0.0)
            self._add("width", [self.s(v, t) for v in range(n)] + [self.b], [1.0] * n + [-1.0], -np.inf, 0.0)
        harper = self.cuts.get("harper")
        if harper is not None:
            # harper[t] <= Φ(t) for t = 1 .. n - 1 (index t), a valid floor per level
            for t in range(1, L + 1):
                c = float(harper[t])
                if c > 0:
                    self._add("harper", [self.s(v, t) for v in range(n)], [1.0] * n, c, np.inf)
        if self.cuts.get("persist"):
            # s[v,t+1] >= s[v,t] - (y[v,t+1] - y[v,t]): a boundary vertex stays one unless it enters
            for t in range(1, L):
                for v in range(n):
                    self._add("persist", [self.s(v, t), self.s(v, t + 1), self.y(v, t + 1), self.y(v, t)],
                              [1.0, -1.0, -1.0, 1.0], -np.inf, 0.0)
        if self.cuts.get("upper"):
            # s[v,t] <= 1 - y[v,t]; s[v,t] <= sum_{u in N(v)} y[u,t]
            for t in range(1, L + 1):
                for v in range(n):
                    self._add("upper", [self.s(v, t), self.y(v, t)], [1.0, 1.0], -np.inf, 1.0)
                    nb = [u for u in range(n) if self.adj[v] >> u & 1]
                    self._add("upper", [self.s(v, t)] + [self.y(u, t) for u in nb], [1.0] + [-1.0] * len(nb),
                              -np.inf, 0.0)
        cliques = self.cuts.get("clique")
        if cliques:
            # k*y[u,t] - sum_{v in K} y[v,t] - sum_{v in K} s[v,t] <= 0 for every u in K
            for K in cliques:
                k = len(K)
                for t in range(1, L + 1):
                    for u in K:
                        idx = [self.y(u, t)] + [self.y(v, t) for v in K] + [self.s(v, t) for v in K]
                        coef = [float(k)] + [-1.0] * k + [-1.0] * k
                        self._add("clique", idx, coef, -np.inf, 0.0)

    def matrices(self):
        rows_i, cols_i, vals = [], [], []
        lo, hi = [], []
        for r, (idx, coef, a, c) in enumerate(self.rows):
            rows_i.extend([r] * len(idx))
            cols_i.extend(idx)
            vals.extend(coef)
            lo.append(a)
            hi.append(c)
        A = sp.csr_matrix((vals, (rows_i, cols_i)), shape=(len(self.rows), self.nvar))
        return A, np.array(lo), np.array(hi)

    def solve(self, time_limit: float | None = None) -> dict:
        """Minimise `b`. Returns `value`, `status`, `seconds`, `y`, `s`, sizes."""
        A, lo, hi = self.matrices()
        c = np.zeros(self.nvar)
        c[self.b] = 1.0
        lb = np.zeros(self.nvar)
        ub = np.ones(self.nvar)
        ub[self.b] = np.inf
        t0 = time.monotonic()
        if self.relax:
            res = linprog(c, bounds=list(zip(lb, ub)), method="highs",
                          options={"time_limit": time_limit} if time_limit else None,
                          **_linprog_constraints(A, lo, hi))
            status = "optimal" if res.status == 0 else f"status{res.status}:{res.message}"
            x = res.x
            value = float(res.fun) if res.status == 0 else float("nan")
        else:
            integrality = np.zeros(self.nvar)
            integrality[: self.ny] = 1
            opts = {"disp": False}
            if time_limit:
                opts["time_limit"] = time_limit
            res = milp(c, constraints=LinearConstraint(A, lo, hi), integrality=integrality,
                       bounds=Bounds(lb, ub), options=opts)
            status = "optimal" if res.status == 0 else f"status{res.status}:{res.message}"
            x = res.x
            value = float(res.fun) if res.x is not None else float("nan")
        seconds = time.monotonic() - t0
        out = {"value": value, "status": status, "seconds": seconds, "n_vars": self.nvar,
               "n_rows": len(self.rows), "families": dict(self.families)}
        if x is not None:
            out["y"] = x[: self.ny].reshape(self.L, self.n)
            out["s"] = x[self.ny: 2 * self.ny].reshape(self.L, self.n)
        return out


def _linprog_constraints(A, lo, hi) -> dict:
    """Split two-sided rows into `A_ub x <= b_ub` and `A_eq x = b_eq` for `linprog`."""
    eq = np.isfinite(lo) & np.isfinite(hi) & (lo == hi)
    up = np.isfinite(hi) & ~eq
    dn = np.isfinite(lo) & ~eq
    A_ub = sp.vstack([A[up], -A[dn]]) if (up.any() or dn.any()) else None
    b_ub = np.concatenate([hi[up], -lo[dn]]) if A_ub is not None else None
    out = {}
    if A_ub is not None:
        out["A_ub"], out["b_ub"] = A_ub, b_ub
    if eq.any():
        out["A_eq"], out["b_eq"] = A[eq], hi[eq]
    return out


def layout_point(adj: list[int], order: list[int]) -> tuple[np.ndarray, np.ndarray]:
    """The exact `(y, s)` of a layout: `y[t-1, v] = 1[v in prefix t]`, `s` the boundary indicator."""
    n = len(adj)
    y = np.zeros((n - 1, n))
    s = np.zeros((n - 1, n))
    S = 0
    for t, v in enumerate(order[:-1], start=1):
        S |= 1 << v
        nb = 0
        m = S
        while m:
            bit = m & -m
            nb |= adj[bit.bit_length() - 1]
            m ^= bit
        for w in range(n):
            y[t - 1, w] = (S >> w) & 1
            s[t - 1, w] = ((nb & ~S) >> w) & 1
    return y, s


def point_satisfies(model: ChainModel, y: np.ndarray, s: np.ndarray, b: float, tol: float = 1e-9) -> bool:
    x = np.concatenate([y.ravel(), s.ravel(), [b]])
    A, lo, hi = model.matrices()
    Ax = A @ x
    return bool(np.all(Ax >= lo - tol) and np.all(Ax <= hi + tol))


def solve_ip(adj: list[int], cuts: dict | None = None, time_limit: float | None = None) -> dict:
    return ChainModel(adj, relax=False, cuts=cuts).solve(time_limit)


def solve_lp(adj: list[int], cuts: dict | None = None, time_limit: float | None = None) -> dict:
    return ChainModel(adj, relax=True, cuts=cuts).solve(time_limit)


# ----------------------------------------------------------------------------
# Harper profiles
# ----------------------------------------------------------------------------


def _subset_tables(adj: list[int]) -> tuple[np.ndarray, np.ndarray]:
    """`pc[S] = |S|` and `bd[S] = |N(S) ∖ S|` for every mask `S`, `n ≤ 24`."""
    n = len(adj)
    N = 1 << n
    nb = np.zeros(N, dtype=np.int64)
    pc = np.zeros(N, dtype=np.int64)
    for v in range(n):
        lo, hi = 1 << v, 1 << (v + 1)
        nb[lo:hi] = nb[:lo] | adj[v]
        pc[lo:hi] = pc[:lo] + 1
    S = np.arange(N, dtype=np.int64)
    out = nb & ~S
    bd = _POP8[out.view(np.uint8).reshape(N, 8)].sum(axis=1)
    return pc, bd


def harper_profile_exact(adj: list[int]) -> list[int]:
    """`Φ(t) = min_{|S|=t} |N(S) ∖ S|` for `t = 0 .. n`, by subset enumeration."""
    n = len(adj)
    if n > 24:
        raise ValueError("exact profile by enumeration is for n <= 24")
    pc, bd = _subset_tables(adj)
    return [int(bd[pc == t].min()) for t in range(n + 1)]


def bb_levels(adj: list[int], cap: int = 12, budget: float | None = 60.0) -> list[int]:
    """`f(k) = min_{|C|=k} |N[C]|` exact by the branch and bound of
    `satisfiability.expansion_bound` for `k = 1 .. cap + 1`, stopping at the budget."""
    from satisfiability.expansion_bound import _f_exact

    n = len(adj)
    masks = [adj[v] | (1 << v) for v in range(n)]
    order = sorted(range(n), key=lambda v: masks[v].bit_count())
    deadline = None if budget is None else time.monotonic() + budget
    levels: list[int] = []
    for k in range(1, min(cap, n - 1) + 2):
        value = _f_exact(masks, n, k, order, deadline)
        if value is None:
            break
        levels.append(value)
    return levels


def floors_from_levels(n: int, levels: list[int], extra_levels: dict[int, int] | None = None) -> list[int]:
    """Valid per-level floors `c(t) ≤ Φ(t)`, `t = 0 .. n`, from exact levels
    `f(1..T)` and optional proved floors on deeper levels (`extra_levels[k] ≤ f(k)`,
    e.g. the record's SAT-settled levels). With `f_lb ≤ f` non-decreasing (monotone
    closure: a level with no floor inherits the largest floor below it, nothing
    more), `M(i) = max{k : f(k) ≤ i} ≤ max{k : f_lb(k) ≤ i} =: M_lb(i)`, so the
    inner-boundary minimum at size `i` is `≥ i − M_lb(i)`. The outer boundary of a
    `t`-set is the inner boundary of its complement, so `Φ(t) = Φ_in(n − t)`."""
    f_lb = {k + 1: v for k, v in enumerate(levels)}
    for k, v in (extra_levels or {}).items():
        if 1 <= k <= n:
            f_lb[k] = max(f_lb.get(k, 0), int(v))
    full = [0] * (n + 1)
    for k in range(1, n + 1):
        full[k] = max(full[k - 1], f_lb.get(k, 0))
    phi_in = [0] * (n + 1)
    for i in range(1, n + 1):
        m = max([k for k in range(1, n + 1) if full[k] <= i], default=0)
        phi_in[i] = max(0, i - m)
    return [phi_in[n - t] for t in range(n + 1)]


def harper_profile_floor(adj: list[int], cap: int = 12, budget: float | None = 60.0,
                         extra_levels: dict[int, int] | None = None) -> tuple[list[int], dict]:
    """`floors_from_levels` on `bb_levels`; returns the floors and the levels used."""
    levels = bb_levels(adj, cap, budget)
    floors = floors_from_levels(len(adj), levels, extra_levels)
    return floors, {"levels": levels, "cap_reached": len(levels) - 1, "extra": dict(extra_levels or {})}


def record_levels(name: str) -> dict[int, int]:
    """Proved floors `f(k) ≥ b + 1` from the record's SAT-settled levels
    (`reports/scratch/obstruction_search/03_sat/levels.csv`, status `unsat`)."""
    if not LEVELS_CSV.exists():
        return {}
    d = pd.read_csv(LEVELS_CSV)
    d = d[(d.instance_name == name) & (d.status == "unsat")]
    out: dict[int, int] = {}
    for r in d.itertuples():
        out[int(r.t)] = max(out.get(int(r.t), 0), int(r.b) + 1)
    return out


# ----------------------------------------------------------------------------
# the Lagrangian ceiling
# ----------------------------------------------------------------------------


def _layer_indices(pc: np.ndarray, n: int) -> list[np.ndarray]:
    order = np.argsort(pc, kind="stable")
    counts = np.bincount(pc, minlength=n + 1)
    bounds = np.concatenate([[0], np.cumsum(counts)])
    return [order[bounds[k]: bounds[k + 1]] for k in range(n + 1)]


def weighted_layout(adj: list[int], mu: np.ndarray, tables=None) -> tuple[float, list[int]]:
    """`min_σ sum_t μ(t) B_σ(t)` and a minimiser, by a subset DP (`n ≤ DP_MAX_N`).
    `mu[t]` for `t = 0 .. n` (ends ignored: levels 0 and n have no boundary)."""
    n = len(adj)
    if n > DP_MAX_N:
        raise ValueError(f"the subset DP is for n <= {DP_MAX_N}")
    pc, bd, layers = tables if tables is not None else _tables_with_layers(adj)
    mu = np.asarray(mu, dtype=float)
    w = mu[pc] * bd
    N = 1 << n
    cost = np.full(N, np.inf)
    cost[0] = 0.0
    for k in range(1, n + 1):
        idx = layers[k]
        best = np.full(len(idx), np.inf)
        for v in range(n):
            has = ((idx >> v) & 1).astype(bool)
            sub = idx[has] ^ (1 << v)
            best[has] = np.minimum(best[has], cost[sub])
        cost[idx] = best + w[idx]
    # backtrack
    full = N - 1
    S = full
    order_rev = []
    while S:
        target = cost[S] - w[S]
        choice = None
        for v in range(n):
            if S >> v & 1 and abs(cost[S ^ (1 << v)] - target) <= 1e-9 * max(1.0, abs(target)):
                choice = v
                break
        if choice is None:  # numerical slack: take the argmin
            cands = [(cost[S ^ (1 << v)], v) for v in range(n) if S >> v & 1]
            choice = min(cands)[1]
        order_rev.append(choice)
        S ^= 1 << choice
    order = order_rev[::-1]
    return float(cost[full]), order


def _tables_with_layers(adj):
    pc, bd = _subset_tables(adj)
    return pc, bd, _layer_indices(pc, len(adj))


def mixture_lp(profiles: list[list[int]]) -> tuple[float, np.ndarray, np.ndarray]:
    """`min_λ max_t sum_σ λ_σ B_σ(t)` over the pool and the dual `μ` (the LP's
    equilibrium: `max_μ min_{σ in pool} sum_t μ(t) B_σ(t)` has the same value)."""
    P = np.asarray(profiles, dtype=float)  # pool x levels
    k, L = P.shape
    # variables: lambda (k), z; minimise z; P^T lambda <= z; sum lambda = 1
    c = np.zeros(k + 1)
    c[-1] = 1.0
    A_ub = np.hstack([P.T, -np.ones((L, 1))])
    b_ub = np.zeros(L)
    A_eq = np.hstack([np.ones((1, k)), np.zeros((1, 1))])
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1.0],
                  bounds=[(0, None)] * k + [(None, None)], method="highs")
    if res.status != 0:
        raise RuntimeError(res.message)
    lam = res.x[:k]
    mu = -res.ineqlin.marginals if hasattr(res, "ineqlin") else np.full(L, 1.0 / L)
    mu = np.clip(mu, 0, None)
    if mu.sum() > 0:
        mu = mu / mu.sum()
    return float(res.fun), lam, mu


def greedy_layouts(adj: list[int], count: int = 64, seed: int = 0) -> list[list[int]]:
    """Layouts by the cheapest-boundary-next rule with random tie-breaks, each
    with its reversal, plus layouts that start from each vertex (`n` more)."""
    n = len(adj)
    rng = np.random.default_rng(seed)
    out: list[list[int]] = []

    def build(first: int | None, noise: float) -> list[int]:
        S = 0
        nb = 0
        order = []
        for step in range(n):
            if step == 0 and first is not None:
                v = first
            else:
                best, choice = None, None
                for v in range(n):
                    if S >> v & 1:
                        continue
                    S2 = S | (1 << v)
                    nb2 = nb | adj[v]
                    cost = (nb2 & ~S2).bit_count() + noise * rng.random()
                    if best is None or cost < best:
                        best, choice = cost, v
                v = choice
            order.append(v)
            S |= 1 << v
            nb |= adj[v]
        return order

    seen = set()
    cands = [build(f, 0.0) for f in range(n)] + [build(None, 0.999) for _ in range(count)]
    for o in cands:
        for lay in (o, o[::-1]):
            key = tuple(lay)
            if key not in seen:
                seen.add(key)
                out.append(lay)
    return out


def improve_layout(adj: list[int], order: list[int], rounds: int = 2) -> list[int]:
    """A cheap descent on `(max boundary, number of levels at the max)` by
    moving one vertex to another position; keeps the layout a layout."""
    n = len(adj)
    order = list(order)

    def score(o):
        p = profile_of(adj, o)
        m = max(p)
        return (m, sum(1 for x in p if x == m))

    cur = score(order)
    for _ in range(rounds):
        improved = False
        for i in range(n):
            v = order[i]
            for j in range(n):
                if j == i:
                    continue
                cand = order[:i] + order[i + 1:]
                cand.insert(j, v)
                sc = score(cand)
                if sc < cur:
                    order, cur, improved = cand, sc, True
                    break
            if improved:
                break
        if not improved:
            break
    return order


def lagrangian_exact(adj: list[int], tol: float = 1e-7, max_iter: int = 500) -> dict:
    """`L(G) = max_μ min_σ sum_t μ(t) B_σ(t)` exactly (`n ≤ DP_MAX_N`), by
    cutting planes: the restricted game on a pool of layouts gives `μ` and an
    upper bound `z`; the DP's best response gives a lower bound `v`; stop when
    `z − v ≤ tol`. Returns `L`, `mu`, the pool, Harper's profile and `vs`."""
    n = len(adj)
    tables = _tables_with_layers(adj)
    pc, bd, _ = tables
    phi = [int(bd[pc == t].min()) for t in range(n + 1)]
    harper = max(phi)
    pool = [o for o in greedy_layouts(adj, count=8)]
    profiles = [profile_of(adj, o) for o in pool]
    best_lower = -np.inf
    z = np.inf
    mu_full = None
    for it in range(max_iter):
        z, lam, mu = mixture_lp(profiles)
        mu_full = np.zeros(n + 1)
        mu_full[1:n] = mu
        v, order = weighted_layout(adj, mu_full, tables)
        best_lower = max(best_lower, v)
        if z - best_lower <= tol:
            break
        prof = profile_of(adj, order)
        if prof in profiles:  # degenerate dual; perturb towards uniform
            mu_full[1:n] = 0.5 * mu + 0.5 / (n - 1)
            v2, order2 = weighted_layout(adj, mu_full, tables)
            prof = profile_of(adj, order2)
            if prof in profiles:
                break
        pool.append(order)
        profiles.append(prof)
    vs = int(min(max(p) for p in profiles)) if profiles else 0
    # vs exactly: mu = point masses would be slow; the DP at k with 0/inf weights is vs itself
    vs = _vs_by_dp(adj, tables)
    return {"L": float(z), "lower": float(best_lower), "mu": mu_full, "pool": pool, "profiles": profiles,
            "phi": phi, "harper": harper, "vs": vs, "iterations": it + 1}


def _vs_by_dp(adj: list[int], tables) -> int:
    """Vertex separation by the same subset lattice: `cost[S] = max(bd[S], min_v cost[S − v])`."""
    n = len(adj)
    pc, bd, layers = tables
    N = 1 << n
    cost = np.full(N, np.inf)
    cost[0] = 0.0
    for k in range(1, n + 1):
        idx = layers[k]
        best = np.full(len(idx), np.inf)
        for v in range(n):
            has = ((idx >> v) & 1).astype(bool)
            best[has] = np.minimum(best[has], cost[idx[has] ^ (1 << v)])
        cost[idx] = np.maximum(best, bd[idx])
    return int(cost[N - 1])


def mixture_upper(adj: list[int], layouts: list[list[int]]) -> dict:
    """An upper bound on `L(G)` from a pool: `min_λ max_t` mixture boundary."""
    profiles = [profile_of(adj, o) for o in layouts]
    z, lam, mu = mixture_lp(profiles)
    support = int((lam > 1e-9).sum())
    return {"upper": z, "support": support, "pool": len(layouts), "best_single": int(min(max(p) for p in profiles)),
            "mu": mu}


# ----------------------------------------------------------------------------
# a lower bound on L at any n: the two-level sum, by SAT
# ----------------------------------------------------------------------------


def pair_sum_cnf(closed: list[int], sizes: list[int], weights: list[int], total: int):
    """CNF of: nested sets `S_1 ⊂ … ⊂ S_c` of the given sizes with
    `Σ_j w_j · (inner boundary of S_j) ≤ total`. Built on the checkpoint
    encoding (`learning.checkpoint_bound`: membership `s_j`, claimed interior
    `c_j`, `c_j[v] → s_j[u]` for `u ∈ N[v]`, nesting of both) with one totalizer
    over the interiors in place of one per level: `Σ_j w_j |C_j| ≥ Σ_j w_j i_j −
    total`, integer weights by repeating a level's interior literals.

    UNSAT proves that every layout `σ` has `Σ_j w_j B'_σ(i_j) > total`, where
    `B'_σ(i)` is the inner boundary of its `i`-prefix, i.e. the outer boundary
    of the suffix: `B'_σ(i) = B_{σ^rev}(n − i)`. So UNSAT at
    `total = ⌊H · Σ w⌋` gives `L(G) ≥ (total + 1) / Σ_j w_j > H` (take
    `μ ∝ w` on the levels `n − i_j`): a certified lower bound on the ceiling."""
    from learning.obstruction_expansion import _totalizer

    n = len(closed)
    c = len(sizes)
    s = [[1 + j * n + v for v in range(n)] for j in range(c)]
    cl = [[1 + c * n + j * n + v for v in range(n)] for j in range(c)]
    next_var = 2 * c * n + 1
    clauses: list[list[int]] = []
    for j in range(c):
        for v in range(n):
            m = closed[v]
            while m:
                bit = m & -m
                clauses.append([-cl[j][v], s[j][bit.bit_length() - 1]])
                m ^= bit
            if j + 1 < c:
                clauses.append([-s[j][v], s[j + 1][v]])
                clauses.append([-cl[j][v], cl[j + 1][v]])
    for j, i in enumerate(sizes):
        o, next_var = _totalizer(s[j], next_var, clauses)
        clauses.append([o[i - 1]])
        if i < n:
            clauses.append([-o[i]])
    lits = []
    for j, w in enumerate(weights):
        lits.extend(cl[j] * int(w))
    need = sum(w * i for w, i in zip(weights, sizes)) - total
    if need >= 1:
        oc, next_var = _totalizer(lits, next_var, clauses)
        clauses.append([oc[need - 1]])
    return clauses, next_var - 1, {"s": s, "c": cl}


def decide_pair_sum(closed: list[int], sizes: list[int], weights: list[int], total: int,
                    conflicts: int | None = None, seconds: float | None = None) -> dict:
    """One CaDiCaL call; `answer` False proves `L > total / Σw` (and, since both
    boundaries `≤ F` would sum to `≤ F·Σw`, `vs ≥ ⌊total / Σw⌋ + 1`); True comes
    with the sets, re-checked from the masks (`boundary` of `checkpoint_bound`);
    None is a conflict-budget censor. **`seconds` does not bind on CaDiCaL**: pysat's
    `interrupt()` is not honoured by `cadical195`, and the `--window high` residual
    pass ran two hours on calls "capped" at 180 s before the coordinator stopped
    it (`reports/chain_lp.md` §7). Use a conflict budget for a bound on work."""
    import threading
    from pysat.solvers import Solver
    from learning.checkpoint_bound import boundary, sets_from_model

    clauses, nv, var_map = pair_sum_cnf(closed, sizes, weights, total)
    solver = Solver(name="cadical195", bootstrap_with=clauses)
    t0 = time.monotonic()
    timer = None
    try:
        if seconds is not None:
            timer = threading.Timer(seconds, solver.interrupt)
            timer.start()
        if conflicts is not None:
            solver.conf_budget(int(conflicts))
        if conflicts is not None or seconds is not None:
            answer = solver.solve_limited(expect_interrupt=seconds is not None)
        else:
            answer = solver.solve()
        model = solver.get_model() if answer is True else None
        stats = solver.accum_stats() or {}
    finally:
        if timer is not None:
            timer.cancel()
        solver.delete()
    sets = None
    if answer is True:
        sets = sets_from_model(closed, model, sizes, var_map)
        tot = 0
        for j, (S, i) in enumerate(zip(sets, sizes)):
            assert bin(S).count("1") == i
            if j + 1 < len(sets):
                assert S & ~sets[j + 1] == 0
            tot += weights[j] * boundary(closed, S)
        assert tot <= total, (tot, total)
    return {"answer": answer, "seconds": time.monotonic() - t0, "conflicts": int(stats.get("conflicts", 0)),
            "sets": sets, "n_vars": nv, "n_clauses": len(clauses)}


def pair_candidates(n: int, max_gap: int = 3) -> list[tuple[int, int]]:
    """Pairs `(t1, t2)`, `1 ≤ t1 < t2 ≤ n − 1`, `t2 − t1 ≤ max_gap`, ordered by
    distance of their midpoint from `0.6 n` (where the compact certificates of
    `reports/checkpoint_relaxation.md` §5 sit, inner-boundary units)."""
    pairs = [(a, a + g) for g in range(1, max_gap + 1) for a in range(1, n - g)]
    return sorted(pairs, key=lambda p: (abs((p[0] + p[1]) / 2 - 0.6 * n), p[1] - p[0]))


def _pairs_job(args) -> dict:
    name, matrix, optimum, harper_vs, max_gap, conflicts, max_calls = args
    from learning.obstruction_expansion import closed_masks_from_matrix

    closed = closed_masks_from_matrix(matrix)
    n = len(closed)
    t0 = time.monotonic()
    calls = unsat_pair = None
    censored = 0
    confl = 0
    for k, (t1, t2) in enumerate(pair_candidates(n, max_gap)[:max_calls], start=1):
        r = decide_pair_sum(closed, [t1, t2], [1, 1], 2 * harper_vs, conflicts)
        confl += r["conflicts"]
        calls = k
        if r["answer"] is False:
            unsat_pair = (t1, t2)
            break
        if r["answer"] is None:
            censored += 1
    return {"instance_name": name, "n": n, "optimum": optimum, "harper_vs": harper_vs, "vs": optimum - 1,
            "L_lower": (harper_vs + 0.5) if unsat_pair else harper_vs, "alive": unsat_pair is not None,
            "pair": f"{unsat_pair[0]} {unsat_pair[1]}" if unsat_pair else "", "calls": calls, "censored": censored,
            "conflicts": confl, "seconds": round(time.monotonic() - t0, 1)}


def run_pairs(workers: int, out_dir: Path, max_gap: int, conflicts: int, max_calls: int, n_max: int) -> pd.DataFrame:
    from learning.obstruction_ledger import corpus_instances

    out_dir.mkdir(parents=True, exist_ok=True)
    pop = gap64()
    pop = pop[pop.n <= n_max]
    found = corpus_instances()
    jobs = [(r.instance_name, np.asarray(found[r.instance_name][1].matrix, dtype=int), int(r.optimum),
             int(r.harper_ref) - 1, max_gap, conflicts, max_calls) for r in pop.itertuples()]
    jobs.sort(key=lambda j: -j[1].shape[0])
    t0 = time.monotonic()
    path = out_dir / "pairs.csv"
    rows = []
    with Pool(workers, initializer=_init) as pool:
        for row in pool.imap_unordered(_pairs_job, jobs):
            rows.append(row)
            print(f"{time.strftime('%T')} {row['instance_name'][:28]:28} n={row['n']} H={row['harper_vs']} vs={row['vs']} "
                  f"{'ALIVE pair ' + row['pair'] if row['alive'] else 'no pair'} calls {row['calls']} censored {row['censored']} "
                  f"{row['seconds']}s", flush=True)
            pd.DataFrame(rows).sort_values(["n", "instance_name"]).to_csv(path, index=False)
    d = pd.DataFrame(rows).sort_values(["n", "instance_name"]).reset_index(drop=True)
    d.to_csv(path, index=False)
    msg = (f"pairs: {len(d)} instances in {time.monotonic() - t0:.0f} s; two-level sum UNSAT (L >= H + 1/2, ceiling alive) on "
           f"{int(d.alive.sum())}; no pair within gap {max_gap} and {max_calls} calls on {int((~d.alive).sum())} "
           f"(censored calls {int(d.censored.sum())}); by n: "
           + ", ".join(f"{n}: {int(g.alive.sum())}/{len(g)}" for n, g in d.groupby("n")))
    print(msg, flush=True)
    (out_dir / "pairs_summary.txt").write_text(msg + "\n")
    return d


# ----------------------------------------------------------------------------
# the record's 11 open residual instances (owner's follow-up, 2026-11-10)
# ----------------------------------------------------------------------------

RESIDUAL_11 = ("Random-100-100-4-1_0", "Random-100-100-4-3_0", "Random-125-125-2-2_0", "Random-125-125-4-1_0",
               "Random-125-125-4-2_0", "Random-125-125-4-3_0", "Random-125-125-4-4_0", "Random-125-125-6-2_0",
               "Random-125-125-6-3_0", "Random-125-125-6-4_0", "Random-125-125-6-5_0")
RESIDUAL_CSV = OUT / "residual" / "residual.csv"


def residual_record() -> pd.DataFrame:
    """The 11 instances `reports/obstruction_search.md` §0 leaves open, with the
    record's floors in optimum units: `floor0`, Harper's proved floor `e_floor`
    and ceiling `e_ceiling`, the minor floors, and `best` = their maximum."""
    u = pd.read_csv(UNCOVERED_CSV).set_index("instance_name")
    cols = [c for c in ("floor0", "e_floor", "m_floor", "m_search", "b_value") if c in u.columns]
    rows = []
    for nm in RESIDUAL_11:
        r = u.loc[nm]
        rows.append({"instance_name": nm, "n": int(r.n), "optimum": int(r.optimum), "floor0": r.floor0,
                     "e_floor": r.e_floor, "e_ceiling": r.e_ceiling, "m_floor": r.m_floor, "m_search": r.m_search,
                     "best": float(np.nanmax([r[c] for c in cols]))})
    return pd.DataFrame(rows)


def residual_pairs(n: int) -> list[tuple[list[int], list[int]]]:
    """Six calls per instance: adjacent pairs at `0.55 n`, `0.58 n`, `0.52 n`,
    `0.61 n` (inner-boundary units, the window of §5), a pair two apart at
    `0.56 n`, all with weights (1, 1); and the first pair with weights (1, 2)."""
    a = [round(0.55 * n), round(0.58 * n), round(0.52 * n), round(0.61 * n)]
    out = [([t, t + 1], [1, 1]) for t in a]
    out.append(([round(0.56 * n), round(0.56 * n) + 2], [1, 1]))
    out.append(([a[0], a[0] + 1], [1, 2]))
    return out


def residual_pairs_high(n: int, F: int) -> list[tuple[list[int], list[int]]]:
    """The second window: a two-level sum at sizes `t_1, t_2` with target `F·Σw`
    is vacuous unless `Σ w_j t_j > F·Σw` (the inner boundary of a `t`-set is at
    most `t`), which the first window missed on the density-6 instances
    (`F = 70–78`, sizes `65–77`). Adjacent pairs at `0.66 n`, `0.70 n`, `0.75 n`,
    `0.80 n`, and at `F + 2`, `F + 5`, `F + 9` where those are higher, weights (1, 1);
    pairs whose sum does not exceed `2F` are dropped."""
    starts = sorted({round(0.66 * n), round(0.70 * n), round(0.75 * n), round(0.80 * n), F + 2, F + 5, F + 9})
    out = []
    for t in starts:
        if t + 1 <= n - 1 and 2 * t + 1 > 2 * F:
            out.append(([t, t + 1], [1, 1]))
    return out


def _residual_job(args) -> dict:
    name, matrix, optimum, best, sizes, weights, seconds, conflicts = args
    from learning.obstruction_expansion import closed_masks_from_matrix
    from learning.extremal import matrix_key

    closed = closed_masks_from_matrix(matrix)
    F = int(best) - 1                      # best floor on record, vs units
    total = F * sum(weights)               # UNSAT proves vs >= F + 1, i.e. optimum >= best + 1
    r = decide_pair_sum(closed, sizes, weights, total, conflicts=conflicts, seconds=seconds)
    status = {False: "unsat", True: "sat", None: "censored"}[r["answer"]]
    return {"instance_name": name, "n": len(closed), "optimum": optimum, "best_record": best, "F_vs": F,
            "sizes": " ".join(map(str, sizes)), "weights": " ".join(map(str, weights)), "total": total,
            "status": status, "proves_optimum_ge": (best + 1) if status == "unsat" else None,
            "seconds": round(r["seconds"], 1), "conflicts": r["conflicts"], "n_vars": r["n_vars"],
            "n_clauses": r["n_clauses"], "matrix_key": matrix_key(matrix)}


def run_residual(workers: int, out_dir: Path, seconds: float, conflicts: int | None,
                 window: str = "mid") -> pd.DataFrame:
    from learning.obstruction_ledger import corpus_instances

    out_dir.mkdir(parents=True, exist_ok=True)
    rec = residual_record()
    found = corpus_instances()
    jobs = []
    for r in rec.itertuples():
        _, inst = found[r.instance_name]
        opt, prov, _ = certified_optimum(inst)
        assert opt == r.optimum and prov.startswith("certified"), (r.instance_name, opt, prov)
        pairs = residual_pairs(int(r.n)) if window == "mid" else residual_pairs_high(int(r.n), int(r.best) - 1)
        for sizes, weights in pairs:
            jobs.append((r.instance_name, np.asarray(inst.matrix, dtype=int), int(r.optimum), float(r.best),
                         sizes, weights, seconds, conflicts))
    t0 = time.monotonic()
    path = out_dir / ("residual.csv" if window == "mid" else f"residual_{window}.csv")
    rows = []
    with Pool(workers, initializer=_init) as pool:
        for row in pool.imap_unordered(_residual_job, jobs):
            rows.append(row)
            print(f"{time.strftime('%T')} {row['instance_name']:22} sizes {row['sizes']:8} w {row['weights']} total {row['total']:4} "
                  f"-> {row['status']:8} {row['seconds']:7.1f}s {row['conflicts']} conflicts", flush=True)
            pd.DataFrame(rows).to_csv(path, index=False)
    d = pd.DataFrame(rows).sort_values(["instance_name", "sizes", "weights"]).reset_index(drop=True)
    d.to_csv(path, index=False)
    bad = d[(d.status == "unsat") & (d.proves_optimum_ge > d.optimum)]
    if len(bad):
        raise SystemExit(f"VIOLATION: a refutation above the certified optimum on {bad.instance_name.tolist()}")
    msg = (f"residual: {len(d)} calls on {d.instance_name.nunique()} instances in {time.monotonic() - t0:.0f} s; "
           f"unsat {int((d.status == 'unsat').sum())}, sat {int((d.status == 'sat').sum())}, censored {int((d.status == 'censored').sum())}; "
           f"instances whose floor rises: {sorted(d[d.status == 'unsat'].instance_name.unique().tolist())}")
    print(msg, flush=True)
    (out_dir / ("residual_summary.txt" if window == "mid" else f"residual_{window}_summary.txt")).write_text(msg + "\n")
    return d


def pair_floor_candidate(graph, matrix, budget) -> int:
    """A `bound_harness` candidate: the best floor the residual run proved for
    this matrix (optimum units), read from `residual.csv` by matrix key; 0 where
    nothing was proved. For the harness's validity stage on the 11."""
    from learning.extremal import matrix_key

    files = [f for f in (RESIDUAL_CSV, RESIDUAL_CSV.with_name("residual_high.csv")) if f.exists()]
    if not files:
        return 0
    d = pd.concat([pd.read_csv(f) for f in files])
    d = d[(d.matrix_key == matrix_key(np.asarray(matrix, dtype=int))) & (d.status == "unsat")]
    return int(d.proves_optimum_ge.max()) if len(d) else 0


# ----------------------------------------------------------------------------
# population and record
# ----------------------------------------------------------------------------


def gap64() -> pd.DataFrame:
    """The 64 instances of the checkpoint study (`refine.csv`): corpus instances at
    30–50 customers whose exact Harper bound is below the certified optimum."""
    d = pd.read_csv(REFINE_CSV)[["instance_name", "n", "optimum", "harper_ref"]].drop_duplicates()
    return d.sort_values(["n", "instance_name"]).reset_index(drop=True)


def best_floor_on_record(names: list[str]) -> dict[str, float]:
    """The best floor on record per instance, optimum units: the ledger's `floor0`
    and the searched floors of `reports/obstruction_search.md` (`e_floor`,
    `m_floor`, `m_search`, `b_value` where present)."""
    out: dict[str, float] = {}
    m = pd.read_csv(MAP_CSV).set_index("instance_name")
    u = pd.read_csv(UNCOVERED_CSV).set_index("instance_name") if UNCOVERED_CSV.exists() else None
    for nm in names:
        vals = []
        if nm in m.index:
            for c in ("floor0", "e_floor"):
                if c in m.columns and pd.notna(m.at[nm, c]):
                    vals.append(float(m.at[nm, c]))
        if u is not None and nm in u.index:
            for c in ("floor0", "e_floor", "m_floor", "m_search", "b_value"):
                if c in u.columns and pd.notna(u.at[nm, c]):
                    vals.append(float(u.at[nm, c]))
        out[nm] = max(vals) if vals else float("nan")
    return out


def certified_optimum(instance) -> tuple[int, str, list[int]]:
    from satisfiability.mosp_solver import _solution_path

    rec = json.loads(_solution_path(instance, SOLUTIONS_DIR).read_text())
    return int(rec["mosp_value"]), rec.get("provenance", ""), list(rec["ordering"])


def witness_layouts(matrix, ordering) -> list[list[int]]:
    from learning.obstruction_expansion import witness_layouts as _wl

    opening, closing = _wl(matrix, ordering)
    return [opening, opening[::-1], closing, closing[::-1]]


# ----------------------------------------------------------------------------
# stages
# ----------------------------------------------------------------------------


def _init():
    os.nice(19)


def _all_layouts_satisfy(adj: list[int], cuts: dict) -> bool:
    """Every layout's exact `(y, s, vs(σ))` point satisfies every row (n ≤ 6: all n! layouts)."""
    model = ChainModel(adj, relax=False, cuts=cuts)
    n = len(adj)
    for order in itertools.permutations(range(n)):
        y, s = layout_point(adj, list(order))
        if not point_satisfies(model, y, s, float(vertex_separation_of(adj, list(order)))):
            return False
    return True


def _atlas_job(args) -> dict:
    gi, edges, n = args
    from fixed_parameter_algorithm.pathwidth import compute_pathwidth
    import networkx as nx

    g = nx.Graph()
    g.add_nodes_from(range(n))
    g.add_edges_from(edges)
    adj = adjacency_from_graph(g)
    pw = compute_pathwidth(g)[0] if n else 0
    row = {"atlas_index": gi, "n": n, "edges": len(edges), "pw_dp": pw}
    if n < 2:
        row.update(ip=pw, ip_cuts=pw, lp=0.0, lp_harper=0.0, lp_all=0.0, harper=0, vs_dp=pw, layouts_ok=True)
        return row
    phi = harper_profile_exact(adj)
    all_cuts = {"harper": phi, "persist": True, "upper": True, "clique": maximal_cliques(adj)}
    row["ip"] = round(solve_ip(adj)["value"])
    row["ip_cuts"] = round(solve_ip(adj, all_cuts)["value"])
    row["lp"] = solve_lp(adj)["value"]
    row["lp_harper"] = solve_lp(adj, {"harper": phi})["value"]
    row["lp_all"] = solve_lp(adj, all_cuts)["value"]
    row["harper"] = max(phi)
    row["layouts_ok"] = _all_layouts_satisfy(adj, all_cuts) if n <= 6 else None
    if n <= 10:
        row["L"] = lagrangian_exact(adj)["L"]
    return row


def run_atlas(workers: int, out_dir: Path) -> pd.DataFrame:
    from networkx.generators.atlas import graph_atlas_g

    out_dir.mkdir(parents=True, exist_ok=True)
    jobs = [(i, list(g.edges()), g.number_of_nodes()) for i, g in enumerate(graph_atlas_g())]
    t0 = time.monotonic()
    with Pool(workers, initializer=_init) as pool:
        rows = list(pool.imap_unordered(_atlas_job, jobs, chunksize=8))
    d = pd.DataFrame(rows).sort_values("atlas_index").reset_index(drop=True)
    d.to_csv(out_dir / "atlas.csv", index=False)
    bad_ip = d[d.ip != d.pw_dp]
    bad_cuts = d[d.ip_cuts != d.pw_dp]
    bad_lay = d[d.layouts_ok == False]  # noqa: E712
    msg = (f"atlas: {len(d)} graphs, {time.monotonic() - t0:.0f} s; IP != DP on {len(bad_ip)}; "
           f"IP with all cuts != DP on {len(bad_cuts)}; a layout violating a cut on {len(bad_lay)}; "
           f"LP (no cuts) max {d.lp.max():.3g}; |LP_harper - Harper| max {(d.lp_harper - d.harper).abs().max():.2e}; "
           f"|LP_all - Harper| max {(d.lp_all - d.harper).abs().max():.2e}")
    if "L" in d:
        g = d[d.L.notna()]
        msg += (f"; L exact on {len(g)}: L > Harper + 1e-6 on {(g.L > g.harper + 1e-6).sum()}, "
                f"ceil(L) > Harper on {(np.ceil(g.L - 1e-6) > g.harper).sum()}, "
                f"Harper < vs on {(g.harper < g.pw_dp).sum()}, L = vs on {(np.isclose(g.L, g.pw_dp)).sum()}")
    print(msg, flush=True)
    (out_dir / "atlas_summary.txt").write_text(msg + "\n")
    return d


def _lp64_job(args) -> dict:
    name, matrix, optimum, harper_ref, cap, budget = args
    from learning.obstruction_ledger import adjacency_from_matrix

    adj = adjacency_from_matrix(matrix)
    n = len(adj)
    levels = bb_levels(adj, cap=cap, budget=budget)
    info = {"cap_reached": len(levels) - 1}
    floors_bb = floors_from_levels(n, levels)
    floors = floors_from_levels(n, levels, record_levels(name))
    # harper_ref is in optimum units (vs + 1); the floors are in vs units
    row = {"instance_name": name, "n": n, "edges": len(edges_of(adj)), "optimum": optimum, "harper_ref": harper_ref,
           "harper_vs": harper_ref - 1, "floor_max_bb": max(floors_bb), "harper_floor_max": max(floors),
           "floor_cap": info["cap_reached"], "record_levels": len(record_levels(name))}
    r = solve_lp(adj)
    row.update(lp=r["value"], lp_seconds=r["seconds"], n_vars=r["n_vars"], n_rows_base=r["n_rows"])
    r = solve_lp(adj, {"harper": floors})
    row.update(lp_harper=r["value"], lp_harper_seconds=r["seconds"])
    r = solve_lp(adj, {"harper": floors, "persist": True, "upper": True})
    row.update(lp_harper_pu=r["value"], lp_harper_pu_seconds=r["seconds"])
    cl = maximal_cliques(adj)
    r = solve_lp(adj, {"harper": floors, "persist": True, "upper": True, "clique": cl})
    row.update(lp_all=r["value"], lp_all_seconds=r["seconds"], n_rows_all=r["n_rows"], cliques=len(cl))
    for k in ("lp", "lp_harper", "lp_harper_pu", "lp_all"):
        row[f"ceil_{k}"] = int(np.ceil(row[k] - 1e-6)) if np.isfinite(row[k]) else None
    return row


def run_lp64(workers: int, out_dir: Path, cap: int, budget: float) -> pd.DataFrame:
    from learning.obstruction_ledger import corpus_instances

    out_dir.mkdir(parents=True, exist_ok=True)
    pop = gap64()
    found = corpus_instances()
    floors = best_floor_on_record(pop.instance_name.tolist())
    jobs = []
    prov = {}
    for r in pop.itertuples():
        _, inst = found[r.instance_name]
        opt, p, _ = certified_optimum(inst)
        assert opt == r.optimum, (r.instance_name, opt, r.optimum)
        prov[r.instance_name] = p
        jobs.append((r.instance_name, np.asarray(inst.matrix, dtype=int), int(r.optimum), int(r.harper_ref), cap, budget))
    t0 = time.monotonic()
    with Pool(workers, initializer=_init) as pool:
        rows = list(pool.imap_unordered(_lp64_job, jobs))
    d = pd.DataFrame(rows)
    d["provenance"] = d.instance_name.map(prov)
    d["best_floor_record"] = d.instance_name.map(floors)
    d = d.sort_values(["n", "instance_name"]).reset_index(drop=True)
    d.to_csv(out_dir / "lp64.csv", index=False)
    # validity: a value above the certified optimum is a bug
    for k in ("ceil_lp", "ceil_lp_harper", "ceil_lp_harper_pu", "ceil_lp_all"):
        above = d[d[k] + 1 > d.optimum]
        if len(above):
            raise SystemExit(f"VIOLATION: {k} + 1 above the certified optimum on {above.instance_name.tolist()}")
    msg = (f"lp64: {len(d)} instances in {time.monotonic() - t0:.0f} s; provenance {d.provenance.value_counts().to_dict()}; "
           f"LP no cuts max {d.lp.max():.2e}; per-level floors reach Harper (max floor == harper_ref - 1) on "
           f"{(d.harper_floor_max == d.harper_vs).sum()} (branch and bound alone: {(d.floor_max_bb == d.harper_vs).sum()}); "
           f"above Harper (bug) on {(d.harper_floor_max > d.harper_vs).sum()}; |LP_harper - max floor| max "
           f"{(d.lp_harper - d.harper_floor_max).abs().max():.2e}; |LP_all - max floor| max "
           f"{(d.lp_all - d.harper_floor_max).abs().max():.2e}; ceil(LP_all) > Harper (vs units) on "
           f"{(d.ceil_lp_all > d.harper_vs).sum()}; reaches optimum on {(d.ceil_lp_all + 1 >= d.optimum).sum()}; "
           f"median LP_all seconds {d.lp_all_seconds.median():.2f}, max {d.lp_all_seconds.max():.1f}")
    print(msg, flush=True)
    (out_dir / "lp64_summary.txt").write_text(msg + "\n")
    return d


def _ceiling_job(args) -> dict:
    name, matrix, optimum, harper_ref, pool_size, seed = args
    from learning.obstruction_ledger import adjacency_from_matrix

    adj = adjacency_from_matrix(matrix)
    n = len(adj)
    t0 = time.monotonic()
    row = {"instance_name": name, "n": n, "optimum": optimum, "harper_ref": harper_ref}
    if n <= DP_MAX_N:
        r = lagrangian_exact(adj)
        row.update(kind="exact", harper=r["harper"], vs=r["vs"], L=r["L"], L_lower=r["lower"],
                   iterations=r["iterations"], pool=len(r["pool"]))
    else:
        layouts = greedy_layouts(adj, count=pool_size, seed=seed)
        layouts = [improve_layout(adj, o, rounds=3) for o in layouts[: min(len(layouts), 2 * n)]] + layouts
        r = mixture_upper(adj, layouts)
        row.update(kind="mixture", harper=harper_ref - 1, vs=optimum - 1, L=np.nan, L_upper=r["upper"],
                   support=r["support"], pool=r["pool"], best_single=r["best_single"])
    row["seconds"] = round(time.monotonic() - t0, 2)
    return row


def small_gap_population(n_max: int = DP_MAX_N) -> pd.DataFrame:
    """Corpus instances at `n ≤ n_max` with the recorded Harper value below the
    optimum (`harper12` of the ledger map; recomputed exactly in the job)."""
    m = pd.read_csv(MAP_CSV)
    d = m[(m.n <= n_max) & (m.harper12 < m.optimum)][["instance_name", "n", "optimum", "harper12"]]
    return d.rename(columns={"harper12": "harper_ref"}).sort_values(["n", "instance_name"]).reset_index(drop=True)


def run_ceiling(workers: int, out_dir: Path, small_limit: int | None, pool_size: int, witness: bool) -> pd.DataFrame:
    from learning.obstruction_ledger import corpus_instances

    out_dir.mkdir(parents=True, exist_ok=True)
    found = corpus_instances()
    small = small_gap_population()
    if small_limit:
        # a stratified cut: every size, cap per size
        small = small.groupby("n", group_keys=False).head(small_limit)
    big = gap64()
    jobs = []
    for r in small.itertuples():
        _, inst = found[r.instance_name]
        jobs.append((r.instance_name, np.asarray(inst.matrix, dtype=int), int(r.optimum), int(r.harper_ref), pool_size, 0))
    for r in big.itertuples():
        _, inst = found[r.instance_name]
        jobs.append((r.instance_name, np.asarray(inst.matrix, dtype=int), int(r.optimum), int(r.harper_ref), pool_size, 0))
    t0 = time.monotonic()
    with Pool(workers, initializer=_init) as pool:
        rows = list(pool.imap_unordered(_ceiling_job, jobs))
    d = pd.DataFrame(rows).sort_values(["n", "instance_name"]).reset_index(drop=True)
    if witness:
        # add the certified witnesses' layouts to the pools at 30-50 and re-solve the mixture
        ups = {}
        for r in big.itertuples():
            _, inst = found[r.instance_name]
            from learning.obstruction_ledger import adjacency_from_matrix
            adj = adjacency_from_matrix(np.asarray(inst.matrix, dtype=int))
            _, _, ordering = certified_optimum(inst)
            lays = witness_layouts(inst.matrix, ordering)
            lays = [improve_layout(adj, o, rounds=3) for o in lays] + lays
            lays += greedy_layouts(adj, count=pool_size, seed=1)
            ups[r.instance_name] = mixture_upper(adj, lays)["upper"]
        d["L_upper_witness"] = d.instance_name.map(ups)
        d["L_upper"] = np.where(d.kind == "mixture", np.fmin(d.L_upper, d.L_upper_witness), d.L_upper)
    d.to_csv(out_dir / "ceiling.csv", index=False)
    ex = d[d.kind == "exact"]
    mx = d[d.kind == "mixture"]
    msg = (f"ceiling: exact L on {len(ex)} instances at n <= {DP_MAX_N} (Harper < optimum on record): "
           f"recomputed Harper < vs on {(ex.harper < ex.vs).sum()}, L > Harper + 1e-6 on {(ex.L > ex.harper + 1e-6).sum()}, "
           f"ceil(L) > Harper on {(np.ceil(ex.L - 1e-6) > ex.harper).sum()}, L = vs on {np.isclose(ex.L, ex.vs).sum()}; "
           f"mean (L - Harper)/(vs - Harper) {((ex.L - ex.harper) / (ex.vs - ex.harper).replace(0, np.nan)).mean():.3f}. "
           f"mixture upper bound on {len(mx)} at 30-50: L_upper <= Harper (route dead for every (y,s) cut) on "
           f"{(mx.L_upper <= mx.harper + 1e-6).sum()}, inconclusive on {(mx.L_upper > mx.harper + 1e-6).sum()}; "
           f"median seconds {d.seconds.median():.1f}")
    print(msg, flush=True)
    (out_dir / "ceiling_summary.txt").write_text(msg + "\n")
    return d


def run_cost(out_dir: Path, names: tuple[str, ...], cap: int, budget: float) -> pd.DataFrame:
    from learning.obstruction_ledger import corpus_instances, adjacency_from_matrix

    out_dir.mkdir(parents=True, exist_ok=True)
    found = corpus_instances()
    rows = []
    for nm in names:
        _, inst = found[nm]
        adj = adjacency_from_matrix(np.asarray(inst.matrix, dtype=int))
        opt, prov, _ = certified_optimum(inst)
        floors, info = harper_profile_floor(adj, cap=cap, budget=budget)
        t0 = time.monotonic()
        r = solve_lp(adj, {"harper": floors})
        row = {"instance_name": nm, "n": len(adj), "edges": len(edges_of(adj)), "optimum": opt,
               "harper_floor_max": max(floors), "lp_harper": r["value"], "status": r["status"],
               "n_vars": r["n_vars"], "n_rows": r["n_rows"], "seconds": round(time.monotonic() - t0, 1)}
        print(row, flush=True)
        rows.append(row)
    d = pd.DataFrame(rows)
    d.to_csv(out_dir / "cost.csv", index=False)
    return d


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--stage", choices=("atlas", "lp64", "ceiling", "cost", "pairs", "residual"), required=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", type=Path, default=OUT)
    ap.add_argument("--cap", type=int, default=12)
    ap.add_argument("--budget", type=float, default=60.0)
    ap.add_argument("--small-limit", type=int, default=None, help="ceiling: at most this many small instances per size")
    ap.add_argument("--pool", type=int, default=200, help="ceiling: random greedy layouts per instance at 30-50")
    ap.add_argument("--no-witness", action="store_true")
    ap.add_argument("--max-gap", type=int, default=3, help="pairs: largest t2 - t1 tried")
    ap.add_argument("--conflicts", type=int, default=1_000_000, help="pairs: conflict budget per call")
    ap.add_argument("--max-calls", type=int, default=120, help="pairs: calls per instance")
    ap.add_argument("--n-max", type=int, default=50)
    ap.add_argument("--seconds", type=float, default=180.0, help="residual: wall cap per SAT call")
    ap.add_argument("--window", choices=("mid", "high"), default="mid", help="residual: 0.52-0.61 n, or above the floor")
    ap.add_argument("--names", nargs="*", default=("Random-100-100-4-1_0", "Random-100-100-4-2_0", "Random-125-125-4-1_0"))
    a = ap.parse_args()
    os.nice(19)
    if a.stage == "atlas":
        run_atlas(a.workers, a.out)
    elif a.stage == "lp64":
        run_lp64(a.workers, a.out, a.cap, a.budget)
    elif a.stage == "ceiling":
        run_ceiling(a.workers, a.out, a.small_limit, a.pool, not a.no_witness)
    elif a.stage == "pairs":
        run_pairs(a.workers, a.out, a.max_gap, a.conflicts, a.max_calls, a.n_max)
    elif a.stage == "residual":
        run_residual(a.workers, a.out / "residual", a.seconds, None, a.window)
    else:
        run_cost(a.out, tuple(a.names), a.cap, a.budget)


if __name__ == "__main__":
    main()
