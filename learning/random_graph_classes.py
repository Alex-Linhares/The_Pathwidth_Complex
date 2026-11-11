"""What the random-graph theorems say for well-studied graph classes (2026-11-11).

The empty-pair first moment (`FirstMoment.lean`, `EmptyPair.lean`) and the
clique-cover first moment (`CliqueCoverMoment.lean`) rest on one deterministic
lemma -- `pw <= k` forces an *empty pair* `(A, R)`, `|A| = t`, `|R| = t - 1`,
`t = ceil((n - k) / 2)`, with no edge between `A` and `R` -- and one union
bound over the `C(n, t) C(n - t, t - 1)` pairs.  Everything model-specific is
the probability that one fixed pair is empty.  This module evaluates that
probability, exactly and asymptotically, under the models the literature
studies and the generators the corpus uses, and reads the record for the
comparison (`reports/random_graph_classes.md`).  Nothing here solves an
instance, reads `solutions/` for anything but a provenance string, or writes
outside `reports/scratch/random_graph_classes/`.

Models:

* **`G_{n,d}`, the pairing (configuration) model** (`gnd_*`).  `dn` points in
  `n` bags of `d`, a uniform perfect matching.  For a pair `(A, R)` with `|A|
  = t`, `|R| = r`, the probability of no `A`--`R` pair is an exact sum over the
  numbers `j`, `l` of `A`--`A` and `R`--`R` pairs (`gnd_log_empty_pair`), and
  its exponent per vertex at `|A| = |R| = a n` is `gnd_rate` (the maximiser of
  the summand at a large `N`, error `O(log N / N)`).  The pairing model is
  vertex-transitive in law, so the union bound is the pair count times one
  probability.  The simple uniform `G_{n,d}` differs by the factor
  `1 / P(simple) -> exp((d^2 - 1) / 4)` (Bender--Canfield, Bollobas), which
  changes no exponent; `gnd_log_bound(..., simple=True)` applies that
  asymptotic factor and says so.
* **Harvey's three generators** (`rows_fixed_*`, `regular_bipartite_*`).
  `wbo_n_m`: every pattern has exactly `d` customers -- the uniform
  `d`-subset model of `CliqueCoverMoment.lean`, `learning.first_moment`.
  `wbp_n_m`: every customer has exactly `r` patterns, patterns free: the
  probability that no pattern meets both `A` and `R` is a sum over the size
  of the union of the `|A|` chosen `r`-sets (`rows_fixed_log_empty_pair`).
  `wbop_n_m`: both margins constant: the bipartite pairing model, where the
  probability is `alpha! rho! sigma! / N!` times the coefficient of
  `x^alpha y^rho z^sigma` in `((x + z)^d + (y + z)^d - z^d)^m`
  (`regular_bipartite_log_empty_pair`, exact in integers).
* **`G(n, p)` and `G(n, m)`** (`gnp_log_bound`, `gnm_log_bound`): the Lean
  inequality and its hypergeometric twin (`C(M - t(t-1), m) / C(M, m)`).
* **Hypercubes and grids** (`hypercube_pathwidth`, `simplicial_profile`,
  `harper_profile`): Harper's bound `pw >= max_t (f(t) - t)`, `f(t) = min_{|A|
  = t} |N[A]|`, computed exactly by the branch and bound of
  `satisfiability.expansion_bound` on small graphs and by Harper's theorem
  (initial segments of the simplicial order) on `Q_d`.

Usage:
    nice -n 19 python3 -m learning.random_graph_classes            # every table, ~3 min
    nice -n 19 python3 -m learning.random_graph_classes --stage gnd
    python -m pytest tests/test_random_graph_classes.py -q
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import re
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np
import pandas as pd

from learning.first_moment import beta_star, floors, lchoose, log_bound, log_pairs, phi
from learning.separator_moment import beta_star_gnp

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "reports" / "scratch" / "random_graph_classes"
INSTANCES_CSV = ROOT / "learning" / "data" / "instances.csv"
CHALLENGE = ROOT / "benchmarks" / "instances" / "ChallengeInstances2005"
MOSP_INSTANCES = ROOT / "benchmarks" / "instances" / "MOSP_Instances"
ENSEMBLE = ROOT / "learning" / "data" / "ensemble"
DATASET = ROOT / "paper1" / "data" / "dataset" / "pathwidth_dataset.jsonl.gz"
LEVELS = (1.0, 0.05, 0.01)

lg = math.lgamma


def _logsumexp(values) -> float:
    values = [v for v in values if v > -math.inf]
    if not values:
        return -math.inf
    m = max(values)
    return m + math.log(sum(math.exp(v - m) for v in values))


def entropy3(a: float, b: float) -> float:
    """`H(a, b, 1 - a - b)` in nats."""
    return phi(a) + phi(b) + phi(1 - a - b)


# ----------------------------------------------------------------------------
# G_{n,d}: the pairing model
# ----------------------------------------------------------------------------


def _ldf(k: int) -> float:
    """`log (k - 1)!!` for even `k >= 0`: the matchings of `k` points."""
    if k < 0 or k % 2:
        return -math.inf
    h = k // 2
    return lg(k + 1) - h * math.log(2) - lg(h + 1)


def _gnd_log_term(alpha: int, rho: int, sigma: int, j: int, l: int) -> float:
    """log of the number of matchings of `alpha + rho + sigma` points with `j`
    `A`--`A` pairs, `l` `R`--`R` pairs and no `A`--`R` pair."""
    k, q = alpha - 2 * j, rho - 2 * l
    if k < 0 or q < 0 or k + q > sigma or (sigma - k - q) % 2:
        return -math.inf
    return (lchoose(alpha, 2 * j) + _ldf(2 * j) + lchoose(sigma, k) + lg(k + 1)
            + lchoose(rho, 2 * l) + _ldf(2 * l) + lchoose(sigma - k, q) + lg(q + 1)
            + _ldf(sigma - k - q))


def gnd_log_empty_pair(n: int, d: int, t: int, r: int | None = None) -> float:
    """log P(no `A`--`R` pair) in the pairing model on `n` bags of `d`, for a
    fixed pair with `|A| = t`, `|R| = r` (default `t - 1`); exact."""
    r = t - 1 if r is None else r
    if t < 0 or r < 0 or t + r > n or (n * d) % 2:
        return -math.inf
    alpha, rho, sigma = d * t, d * r, d * (n - t - r)
    terms = [_gnd_log_term(alpha, rho, sigma, j, l)
             for j in range(alpha // 2 + 1) for l in range(rho // 2 + 1)]
    return _logsumexp(terms) - _ldf(n * d)


def _ternary_int(f, lo: int, hi: int) -> tuple[int, float]:
    """Maximum of a unimodal integer function on `[lo, hi]`."""
    while hi - lo > 2:
        m1 = lo + (hi - lo) // 3
        m2 = hi - (hi - lo) // 3
        if f(m1) < f(m2):
            lo = m1 + 1
        else:
            hi = m2
    best = max(range(lo, hi + 1), key=f)
    return best, f(best)


def _ldf_cont(x: float) -> float:
    """`log (x - 1)!!` continued to real `x` (`lgamma` form), for the rate."""
    return lg(x + 1) - (x / 2) * math.log(2) - lg(x / 2 + 1)


def _gnd_log_term_cont(alpha: int, rho: int, sigma: int, j: int, l: int) -> float:
    """The summand of `gnd_log_empty_pair` without the parity condition on the
    `S`--`S` pairs (continued by `_ldf_cont`); used only for the exponent."""
    k, q = alpha - 2 * j, rho - 2 * l
    if k < 0 or q < 0 or k + q > sigma:
        return -math.inf
    return (lchoose(alpha, 2 * j) + _ldf(2 * j) + lchoose(sigma, k) + lg(k + 1)
            + lchoose(rho, 2 * l) + _ldf(2 * l) + lchoose(sigma - k, q) + lg(q + 1)
            + _ldf_cont(sigma - k - q))


def _argmax_2d(f, j_max: int, l_max: int, cells: int = 48) -> float:
    """Maximum of `f(j, l)` on `[0, j_max] x [0, l_max]` by successive grid
    refinement (a coarse grid, then a finer grid in the window round the
    best cell, down to step 1); robust to `-inf` regions, which a coordinate
    ascent is not."""
    lo_j, hi_j, lo_l, hi_l = 0, j_max, 0, l_max
    best, arg = -math.inf, (0, 0)
    while True:
        sj = max(1, (hi_j - lo_j) // cells)
        sl = max(1, (hi_l - lo_l) // cells)
        for j in range(lo_j, hi_j + 1, sj):
            for l in range(lo_l, hi_l + 1, sl):
                v = f(j, l)
                if v > best:
                    best, arg = v, (j, l)
        if sj == 1 and sl == 1:
            return best
        lo_j, hi_j = max(0, arg[0] - 2 * sj), min(j_max, arg[0] + 2 * sj)
        lo_l, hi_l = max(0, arg[1] - 2 * sl), min(l_max, arg[1] + 2 * sl)


def gnd_rate(d: int, a: float, r: float | None = None, big_n: int = 200_000) -> float:
    """`(1/n) log P(no A--R pair)` at `|A| = a n`, `|R| = r n` (default `r = a`),
    `n -> oo`: the largest summand of `gnd_log_empty_pair` at `n = big_n`,
    divided by `big_n` (the sum has `O(n^2)` terms, so the error is
    `O(log n / n)`)."""
    r = a if r is None else r
    t, tr = int(round(a * big_n)), int(round(r * big_n))
    alpha, rho = d * t, d * tr
    sigma = d * (big_n - t - tr)
    if sigma < 0 or alpha < 0 or rho < 0:
        return -math.inf

    def term(j, l):
        return _gnd_log_term_cont(alpha, rho, sigma, j, l)

    value = _argmax_2d(term, alpha // 2, rho // 2)
    return (value - _ldf(big_n * d)) / big_n


def gnd_pair_rate(d: int, a: float, r: float | None = None) -> float:
    """`g_d(a, r) = H(a, r, 1 - a - r) + gnd_rate(d, a, r)`: the exponent per
    vertex of the expected number of empty pairs `(|A|, |R|) = (a n, r n)` in
    `G_{n,d}`."""
    r = a if r is None else r
    return entropy3(a, r) + gnd_rate(d, a, r)


def gnp_pair_rate2(c: float, a: float, r: float) -> float:
    """The same on `G(n, c/n)`: `H(a, r, 1 - a - r) - c a r`."""
    return entropy3(a, r) - c * a * r


def _min_over_split(rate_fn, beta: float, grid: int = 40) -> tuple[float, float]:
    """`min_a rate_fn(a, 1 - beta - a)` over a grid then a golden refinement:
    the best split of the empty pair at width `beta n` (`(value, a)`)."""
    s = 1 - beta
    xs = [s * (i + 0.5) / grid for i in range(grid)]
    vals = [rate_fn(a, s - a) for a in xs]
    i = int(np.argmin(vals))
    lo, hi = xs[max(i - 1, 0)], xs[min(i + 1, grid - 1)]
    for _ in range(30):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if rate_fn(m1, s - m1) < rate_fn(m2, s - m2):
            hi = m2
        else:
            lo = m1
    a = (lo + hi) / 2
    return rate_fn(a, s - a), a


def beta_star_split(rate_fn, step: float = 1e-3, tol: float = 1e-5) -> tuple[float, float]:
    """`sup {beta : min_a rate_fn(a, 1 - beta - a) < 0}` by a downward scan
    then bisection, and the split `a` at the root: the first-moment floor
    on `lim pw / n` when the pair's sizes are chosen freely (Harper's layout
    form gives, for every `j`, a pair of sizes `(j, n - j - pw)`)."""
    beta = step
    if _min_over_split(rate_fn, beta)[0] >= 0:
        return 0.0, 0.5
    while beta + step < 1 and _min_over_split(rate_fn, beta + step)[0] < 0:
        beta += step
    lo, hi = beta, min(beta + step, 1 - 1e-9)
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if _min_over_split(rate_fn, mid)[0] < 0:
            lo = mid
        else:
            hi = mid
    return lo, _min_over_split(rate_fn, lo)[1]


def beta_star_gnd(d: int, step: float = 1e-3) -> float:
    """`beta*_d = 1 - 2 a*` for balanced pairs, `a*` the point above which
    `g_d(a, a) < 0`: the first-moment floor on `lim pw(G_{n,d}) / n` in the
    Lean lemma's shape (`|A| = t`, `|R| = t - 1`).  Zero if `g_d >= 0` just
    below `a = 1/2`.  Scanned from `1/2` down in steps of `step`, as
    `learning.first_moment.beta_star` does, then bisected to `1e-5`."""
    a = 0.5 - step
    if gnd_pair_rate(d, a) >= 0:
        return 0.0
    while a - step > 0 and gnd_pair_rate(d, a - step) < 0:
        a -= step
    lo, hi = max(a - step, 1e-6), a
    while hi - lo > 1e-5:
        mid = (lo + hi) / 2
        if gnd_pair_rate(d, mid) < 0:
            hi = mid
        else:
            lo = mid
    return 1 - 2 * hi


def beta_star_gnd_split(d: int) -> tuple[float, float]:
    """The floor with the pair's split chosen freely (`beta_star_split` on
    `gnd_pair_rate`): `(beta, a)`."""
    return beta_star_split(lambda a, r: gnd_pair_rate(d, a, r), step=5e-3)


def simple_correction(d: int) -> float:
    """`log (1 / P(simple))` in the pairing model, asymptotically:
    `(d^2 - 1) / 4` (Bender & Canfield 1978; Bollobas 1980)."""
    return (d * d - 1) / 4


def gnd_log_bound(n: int, d: int, k: int, simple: bool = False) -> float:
    """log of the union bound on `P(pw(G_{n,d}) <= k)`; with `simple=True` the
    asymptotic factor `1 / P(simple)` is added (an asymptotic, not a finite,
    statement)."""
    t = (n - k + 1) // 2
    if t < 1 or 2 * t - 1 > n:
        return math.inf
    value = log_pairs(n, t) + gnd_log_empty_pair(n, d, t)
    return value + (simple_correction(d) if simple else 0.0)


def union_floors(n: int, log_bound_fn, levels=LEVELS) -> dict[float, int]:
    """For each confidence level: `k* + 1`, the floor on the *pathwidth*,
    where `k*` is the largest `k` with `log P(pw <= k) < log level`
    (`-1` when no `k` qualifies, giving floor 0)."""
    out = {}
    for level in levels:
        ks = [k for k in range(n) if log_bound_fn(k) < math.log(level)]
        out[level] = (max(ks) if ks else -1) + 1
    return out


def gnd_floors(n: int, d: int, simple: bool = False, levels=LEVELS) -> dict[float, int]:
    return union_floors(n, lambda k: gnd_log_bound(n, d, k, simple), levels)


# ----------------------------------------------------------------------------
# G(n, p) and G(n, m)
# ----------------------------------------------------------------------------


def gnp_log_bound(n: int, p: float, k: int) -> float:
    """The Lean inequality `weightedSum_graphsOfPathwidthLe_le`:
    `log [C(n,t) C(n-t,t-1) (1-p)^(t(t-1))]`."""
    t = (n - k + 1) // 2
    if t < 1 or 2 * t - 1 > n:
        return math.inf
    return log_pairs(n, t) + t * (t - 1) * math.log1p(-p)


def gnm_log_bound(n: int, m: int, k: int) -> float:
    """The same union bound on `G(n, m)`: one pair is empty with probability
    `C(M - t(t-1), m) / C(M, m)`, `M = C(n, 2)` (not a product law; the pair
    probability is uniform over pairs and explicit)."""
    t = (n - k + 1) // 2
    if t < 1 or 2 * t - 1 > n:
        return math.inf
    big_m = n * (n - 1) // 2
    return log_pairs(n, t) + lchoose(big_m - t * (t - 1), m) - lchoose(big_m, m)


def gnp_floors(n: int, p: float, levels=LEVELS) -> dict[float, int]:
    return union_floors(n, lambda k: gnp_log_bound(n, p, k), levels)


def gnm_floors(n: int, m: int, levels=LEVELS) -> dict[float, int]:
    return union_floors(n, lambda k: gnm_log_bound(n, m, k), levels)


def bipartite_pair_rate(c: float, a1: float, a2: float, r1: float, r2: float) -> float:
    """`G(n, n, p)` with `p = c/n` (mean degree `c`), `N = 2n` vertices: the
    exponent per vertex of the expected number of empty pairs with `a1 N`,
    `a2 N` vertices of `A` and `r1 N`, `r2 N` of `R` on the two sides:
    `(1/2) H(2a1, 2r1, .) + (1/2) H(2a2, 2r2, .) - 2c (a1 r2 + a2 r1)`."""
    if min(a1, a2, r1, r2) < 0 or 2 * (a1 + r1) > 1 or 2 * (a2 + r2) > 1:
        return math.inf
    return 0.5 * entropy3(2 * a1, 2 * r1) + 0.5 * entropy3(2 * a2, 2 * r2) - 2 * c * (a1 * r2 + a2 * r1)


def bipartite_shape_rate(c: float, a: float, r: float, grid: int = 48) -> float:
    """For sides `|A| = a N`, `|R| = r N`: the exponent of the union bound over
    the *splits* of the pair across the two colour classes, i.e. the maximum
    of `bipartite_pair_rate` over `a1 in [0, a]`, `r1 in [0, r]` (the pair the
    lemma produces has a split we do not choose, so the bound must sum over
    splits; a grid then Nelder--Mead from the best cell)."""
    from scipy.optimize import minimize
    best, arg = -math.inf, None
    for j in range(grid + 1):
        a1 = a * j / grid
        for k in range(grid + 1):
            r1 = r * k / grid
            v = bipartite_pair_rate(c, a1, a - a1, r1, r - r1)
            if v < math.inf and v > best:
                best, arg = v, (a1, r1)
    if arg is None:
        return -math.inf

    def obj(x):
        v = bipartite_pair_rate(c, x[0], a - x[0], x[1], r - x[1])
        return -v if v < math.inf else 1e9

    res = minimize(obj, arg, method="Nelder-Mead", options={"xatol": 1e-8, "fatol": 1e-11})
    return max(best, -float(res.fun))


def bipartite_min_rate(c: float, beta: float, grid: int = 24) -> float:
    """`min_{a + r = 1 - beta} bipartite_shape_rate(c, a, r)`: the best shape
    of the pair (each shape is a valid bound on its own, by Harper's layout
    form) at width `beta N`."""
    s = 1 - beta
    best = math.inf
    for i in range(1, grid):
        a = s * i / grid
        best = min(best, bipartite_shape_rate(c, a, s - a, grid=16))
    return best


def beta_star_bipartite(c: float, step: float = 1e-3) -> float:
    """The first-moment floor on `lim pw(G(n, n, c/n)) / (2n)`: the largest
    `beta` with `bipartite_min_rate(c, beta) < 0` (zero if none)."""
    if bipartite_min_rate(c, step) >= 0:
        return 0.0
    lo, hi = step, 1 - step
    while hi - lo > step:
        mid = (lo + hi) / 2
        if bipartite_min_rate(c, mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo


# ----------------------------------------------------------------------------
# Harvey's generators: rows fixed; both margins fixed
# ----------------------------------------------------------------------------


def rows_fixed_log_empty_pair(n: int, m: int, r: int, t: int, tr: int | None = None) -> float:
    """Every customer takes an independent uniform `r`-subset of the `m`
    patterns.  log P(no pattern meets both `A` and `R`), `|A| = t`, `|R| = tr`
    (default `t - 1`), by the distribution of `|Q_A|`, the union of `A`'s sets."""
    tr = t - 1 if tr is None else tr
    if t < 0 or tr < 0 or t + tr > n or r > m:
        return -math.inf
    dist = {0: 0.0}  # log P(|Q_A| = u)
    for _ in range(t):
        nxt: dict[int, list[float]] = {}
        for u, lp in dist.items():
            for x in range(0, r + 1):  # new patterns chosen outside Q_A
                if x > m - u or r - x > u:
                    continue
                w = lchoose(m - u, x) + lchoose(u, r - x) - lchoose(m, r)
                nxt.setdefault(u + x, []).append(lp + w)
        dist = {u: _logsumexp(v) for u, v in nxt.items()}
    terms = [lp + tr * (lchoose(m - u, r) - lchoose(m, r)) for u, lp in dist.items()]
    return _logsumexp(terms)


_BIP_CACHE: dict[tuple[int, int, int], np.ndarray] = {}


def regular_bipartite_log_coeffs(m: int, d: int, big_n: int) -> np.ndarray:
    """`L[a, b] = log [x^a y^b z^(N - a - b)] ((x+z)^d + (y+z)^d - z^d)^m`,
    `N = md`, by a log-space DP over the `m` patterns (cached)."""
    key = (m, d, big_n)
    if key in _BIP_CACHE:
        return _BIP_CACHE[key]
    moves = []
    for a in range(d + 1):
        for b in range(d + 1 - a):
            if a and b:
                continue
            w = math.lgamma(d + 1) - math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(d - a - b + 1)
            moves.append((a, b, w))
    state = np.full((big_n + 1, big_n + 1), -np.inf)
    state[0, 0] = 0.0
    for _ in range(m):
        nxt = np.full_like(state, -np.inf)
        for a, b, w in moves:
            if a:
                nxt[a:, :] = np.logaddexp(nxt[a:, :], state[:-a, :] + w)
            elif b:
                nxt[:, b:] = np.logaddexp(nxt[:, b:], state[:, :-b] + w)
            else:
                nxt = np.logaddexp(nxt, state + w)
        state = nxt
    _BIP_CACHE[key] = state
    return state


def regular_bipartite_log_empty_pair(n: int, m: int, r: int, d: int, t: int,
                                     tr: int | None = None) -> float:
    """The bipartite pairing model: `n` customers of degree `r`, `m` patterns
    of size `d`, `nr = md`, a uniform bijection of half-edges.  log P(no
    pattern meets both `A` and `R`): `alpha! rho! sigma! / N!` times the
    coefficient of `x^alpha y^rho z^sigma` in `((x+z)^d + (y+z)^d - z^d)^m`,
    `alpha = r|A|`, `rho = r|R|` (the DP in log space, to ~1e-12)."""
    tr = t - 1 if tr is None else tr
    if n * r != m * d or t < 0 or tr < 0 or t + tr > n:
        return -math.inf
    alpha, rho = r * t, r * tr
    big_n = n * r
    sigma = big_n - alpha - rho
    coeff = regular_bipartite_log_coeffs(m, d, big_n)[alpha, rho]
    if coeff == -np.inf:
        return -math.inf
    return float(coeff + lg(alpha + 1) + lg(rho + 1) + lg(sigma + 1) - lg(big_n + 1))


def harvey_family(name: str) -> tuple[str, int]:
    """`(family, parameter)` from a Harvey instance description:
    `balanced orders, 2 orders per product` -> ('wbo', 2);
    `balanced products, 3 products per order` -> ('wbp', 3);
    `balanced orders and products, 4 products per order` -> ('wbop', 4)."""
    text = name.lower()
    k = int(re.search(r"(\d+) (orders|products) per", text).group(1))
    if "orders and products" in text:
        return "wbop", k
    if "balanced orders" in text:
        return "wbo", k
    return "wbp", k


def _read_benchmark(path: Path) -> list[tuple[str, np.ndarray]]:
    """`(name, customers x patterns matrix)` per instance, through the
    project's own loader so that names match `learning/data/instances.csv`."""
    from mosp.instance import MOSPInstance
    return [(inst.name, np.asarray(inst.matrix)) for inst in MOSPInstance.from_benchmark_file(path)]


def harvey_rows(levels=LEVELS) -> pd.DataFrame:
    """One row per Harvey instance: family, `n`, `m`, parameter, optimum, and
    the floors (pathwidth units, i.e. optimum - 1) under the model that
    matches the family and under the uniform-size (measured) form."""
    table = pd.read_csv(INSTANCES_CSV, usecols=["instance_name", "source_file", "optimum", "provenance"])
    table = table[table.source_file.str.contains("Harvey")]
    opt = dict(zip(table.instance_name, table.optimum))
    prov = dict(zip(table.instance_name, table.provenance))
    rows = []
    for path in sorted((CHALLENGE / "Harvey").glob("*.txt")):
        for name, matrix in _read_benchmark(path):
            if name not in opt:
                continue
            n, m = matrix.shape
            fam, k = harvey_family(name)
            sizes = matrix.sum(0).tolist()
            uniform = union_floors(n, lambda kk: log_bound(n, sizes, kk), levels)
            if fam == "wbo":
                model = uniform
            elif fam == "wbp":
                model = union_floors(n, lambda kk: _pair_bound(n, kk, lambda t: rows_fixed_log_empty_pair(n, m, k, t)), levels)
            else:
                r = int(matrix.sum(1)[0])
                d = int(matrix.sum(0)[0])
                model = union_floors(n, lambda kk: _pair_bound(n, kk, lambda t: regular_bipartite_log_empty_pair(n, m, r, d, t)), levels)
            rows.append({"instance_name": name, "file": path.stem, "family": fam, "n": n, "m": m, "param": k,
                         "optimum": opt[name], "pw": opt[name] - 1, "provenance": prov[name],
                         **{f"model_floor_{lv}": model[lv] for lv in levels},
                         **{f"uniform_floor_{lv}": uniform[lv] for lv in levels}})
    return pd.DataFrame(rows)


def _pair_bound(n: int, k: int, log_pair) -> float:
    t = (n - k + 1) // 2
    if t < 1 or 2 * t - 1 > n:
        return math.inf
    return log_pairs(n, t) + log_pair(t)


# ----------------------------------------------------------------------------
# the MOSP collections under the uniform-size (measured) form
# ----------------------------------------------------------------------------


def collection_rows(levels=LEVELS) -> pd.DataFrame:
    """Every corpus instance outside Harvey: the floors of the uniform-size
    model at the realised pattern sizes (the measured form of
    `prob_coversOfMospValueLe_le`) against the certified optimum."""
    table = pd.read_csv(INSTANCES_CSV, usecols=["instance_name", "source_file", "optimum", "provenance",
                                                "n_customers", "n_patterns", "n_ones"])
    opt = dict(zip(table.instance_name, table.optimum))
    prov = dict(zip(table.instance_name, table.provenance))
    rows = []

    def add(name, matrix, collection, source):
        if name not in opt:
            return
        n, m = matrix.shape
        sizes = matrix.sum(0).tolist()
        fl = union_floors(n, lambda kk: log_bound(n, sizes, kk), levels)
        rows.append({"instance_name": name, "collection": collection, "source": source, "n": n, "m": m,
                     "n_ones": int(matrix.sum()), "excess": (matrix.sum() - m) / n,
                     "optimum": opt[name], "pw": opt[name] - 1, "provenance": prov[name],
                     "beta_star": beta_star(m / n, sizes),
                     **{f"floor_{lv}": fl[lv] for lv in levels}})

    for sub in ("Simonis", "Shaw", "Wilson", "Miller"):
        for path in sorted((CHALLENGE / sub).glob("*")):
            if path.suffix not in (".txt", ".dat"):
                continue
            for name, matrix in _read_benchmark(path):
                add(name, matrix, sub, path.stem)
    for sub in ("Chu_Stuckey", "Faggioli_Bentivoglio", "SCOOP", "Challenge"):
        for path in sorted((MOSP_INSTANCES / sub).glob("*.txt")):
            if path.name.startswith("Dataset"):
                continue
            for name, matrix in _read_benchmark(path):
                add(name, matrix, sub, path.stem)
    return pd.DataFrame(rows)


def chu_stuckey_cells(frame: pd.DataFrame, levels=LEVELS) -> pd.DataFrame:
    """Per Chu & Stuckey class `(n, m, d)`: mean `opt / n`, `beta*` at the
    empirical sizes and at fixed `d`, the mean floors, the minimum optimum,
    and the number of instances whose optimum is below the 0.01 floor + 1."""
    cs = frame[frame.collection == "Chu_Stuckey"].copy()
    cs["d"] = cs.instance_name.str.extract(r"Random-\d+-\d+-(\d+)-").astype(int)
    out = []
    for (n, m, d), g in cs.groupby(["n", "m", "d"]):
        row = {"n": n, "m": m, "d": d, "k": len(g), "excess": g.excess.mean(), "opt_over_n": g.optimum.mean() / n,
               "beta_star_sizes": g.beta_star.mean(), "beta_star_fixed": beta_star(m / n, [d]),
               "opt_min": g.optimum.min(), "opt_mean": g.optimum.mean()}
        for lv in levels:
            row[f"floor_{lv}_mean"] = g[f"floor_{lv}"].mean() + 1  # optimum units
        row["violations_0.01"] = int((g.optimum < g["floor_0.01"] + 1).sum())
        row["tight_0.01"] = int((g.optimum == g["floor_0.01"] + 1).sum())
        row["gap_0.01_mean"] = (g.optimum - g["floor_0.01"] - 1).mean()
        out.append(row)
    return pd.DataFrame(out)


def ensemble_cells(levels=LEVELS) -> pd.DataFrame:
    """The fixed-size ensembles (`learning/data/ensemble/results*.csv`): per
    cell `(n, m/n, d)` the mean `opt / n`, `beta*(d, mu)`, the finite floors at
    the nominal sizes, and the number of instances below the 0.01 floor."""
    frames = [pd.read_csv(ENSEMBLE / "results.csv")]
    upward = ENSEMBLE / "results_upward.csv"
    if upward.exists():
        frames.append(pd.read_csv(upward))
    r = pd.concat(frames, ignore_index=True)
    r = r[(r.certified == True) & (r.generator == "fixed")]  # noqa: E712
    out = []
    for (n, m, d), g in r.groupby(["n", "m", "param"]):
        n, m, d = int(n), int(m), int(d)
        fl = floors(n, [d] * m)  # optimum units, levels (1, 0.01)
        out.append({"n": n, "ratio": m / n, "d": d, "k": len(g), "excess": ((g.n_ones - g.m) / g.n).mean(),
                    "opt_over_n": g.optimum.mean() / n, "beta_star": beta_star(m / n, [d]),
                    "floor_1": fl[0], "floor_0.01": fl[1], "opt_min": int(g.optimum.min()),
                    "violations_0.01": int((g.optimum < fl[1]).sum()),
                    "nodes_median": float(g.nodes_csearch.median()) if "nodes_csearch" in g else float("nan")})
    return pd.DataFrame(out)


# ----------------------------------------------------------------------------
# hypercubes and grids: Harper's bound, exactly
# ----------------------------------------------------------------------------


def hypercube_pathwidth(d: int) -> int:
    """`pw(Q_d) = sum_{m=0}^{d-1} C(m, floor(m/2))` (Chandran & Kavitha 2006,
    Theorem 2, from Harper's theorem)."""
    return sum(math.comb(m, m // 2) for m in range(d))


def hypercube_masks(d: int) -> list[int]:
    n = 1 << d
    return [(1 << v) | sum(1 << (v ^ (1 << i)) for i in range(d)) for v in range(n)]


def grid_masks(h: int, w: int) -> list[int]:
    def idx(i, j):
        return i * w + j
    masks = []
    for i in range(h):
        for j in range(w):
            m = 1 << idx(i, j)
            for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                a, b = i + di, j + dj
                if 0 <= a < h and 0 <= b < w:
                    m |= 1 << idx(a, b)
            masks.append(m)
    return masks


def simplicial_order(d: int) -> list[int]:
    """Harper's simplicial order on `Q_d`: by weight, then by the position of
    the first 1 (vertices whose 1s sit at the lowest coordinates first)."""
    def key(v):
        bits = [(v >> i) & 1 for i in range(d)]
        return (sum(bits), [-b for b in bits])
    return sorted(range(1 << d), key=key)


def simplicial_profile(d: int) -> list[int]:
    """`|N[A_t]| - t` for the initial segments `A_t` of the simplicial order,
    `t = 1..2^d`; by Harper's theorem each is `f(t) - t`."""
    masks = hypercube_masks(d)
    order = simplicial_order(d)
    out, union = [], 0
    for t, v in enumerate(order, 1):
        union |= masks[v]
        out.append(union.bit_count() - t)
    return out


def harper_profile(masks: list[int], n: int, t_max: int | None = None,
                   budget: float | None = 60.0) -> list[int | None]:
    """`f(t) - t` for `t = 1..t_max` by the exact branch and bound of
    `satisfiability.expansion_bound._f_exact`; `None` where the budget ran out."""
    from satisfiability.expansion_bound import _f_exact
    order = sorted(range(n), key=lambda v: masks[v].bit_count())
    deadline = None if budget is None else time.monotonic() + budget
    t_max = n if t_max is None else t_max
    out = []
    for t in range(1, t_max + 1):
        f = _f_exact(masks, n, t, order, deadline)
        out.append(None if f is None else f - t)
        if f is None:
            break
    return out


def harper_value(profile) -> int:
    return max(v for v in profile if v is not None)


# ----------------------------------------------------------------------------
# the tables
# ----------------------------------------------------------------------------


def gnd_table(degrees=(3, 4, 5, 6, 8, 10)) -> pd.DataFrame:
    """`beta*_d` under the pairing model beside Kolesnik & Wormald's
    `A_d(1/2) / 2` (their Table 2) and Edwards & McDermid's `g(d)`."""
    kw = {3: 0.14420, 4: 0.28966, 5: 0.40859, 6: 0.50190, 7: 0.57466, 8: 0.63178, 9: 0.67716, 10: 0.71371}
    rows = []
    for d in degrees:
        b = beta_star_gnd(d)
        rows.append({"d": d, "beta_star_pairing": b, "kw_half": kw[d] / 2,
                     "beta_star_gnp_same_degree": beta_star_gnp(float(d))})
    return pd.DataFrame(rows)


CAGES = [("Foster", 90, 20, 15), ("Biggs-Smith", 102, 19, 16), ("Ljubljana", 112, 22, 16),
         ("Balaban 11-cage", 112, 24, 17), ("Tutte 12-cage", 126, 26, 20)]


def cages_table() -> pd.DataFrame:
    rows = []
    for name, n, width, floor in CAGES:
        fl = gnd_floors(n, 3)
        fls = gnd_floors(n, 3, simple=True)
        rows.append({"graph": name, "n": n, "width_on_record": width, "floor_on_record": floor,
                     "pairing_floor_1": fl[1.0], "pairing_floor_0.05": fl[0.05], "pairing_floor_0.01": fl[0.01],
                     "simple_floor_0.05": fls[0.05],
                     "beta_star_3_times_n": beta_star_gnd(3) * n, "kw_times_n": 0.14420 / 2 * n,
                     "lichev_mitsche_minus_2": 0.103295 * n - 2, "gaspers_c3_n": 0.139822 * n})
    return pd.DataFrame(rows)


DATASET_RANDOM = {  # id: (name, model, parameter)
    "pwc-17163": ("RandomGNM_100_100", "gnm", None),
    "pwc-17206": ("RandomGNM_250_1000", "gnm", None),
    "pwc-17207": ("RandomGNM_500_500", "gnm", None),
    "pwc-17194": ("random4reg", "gnd", 4),
    "pwc-17161": ("RandomBarabasiAlbert_100_2", "gnp-matched", None),
    "pwc-17205": ("RandomBarabasiAlbert_100_5", "gnp-matched", None),
    "pwc-17208": ("RandomHolmeKim_300_2_2", "gnp-matched", None),
    "pwc-17209": ("RandomHolmeKim_700_2_2", "gnp-matched", None),
    "pwc-17210": ("RandomNewmanWattsStrogatz_100_5_3", "gnp-matched", None),
    "pwc-17211": ("RandomNewmanWattsStrogatz_250_10_3", "gnp-matched", None),
    "pwc-17212": ("RandomTriangulation_800", "planar", None),
    "pwc-15951": ("CubeGraph_6", "hypercube", 6),
    "pwc-15966": ("FoldedCubeGraph_7", "none", None),
    "pwc-17192": ("RandomBoundedToleranceGraph_60", "cocomparability", None),
    "pwc-17193": ("RandomBoundedToleranceGraph_80", "cocomparability", None),
}


def dataset_records(ids) -> dict[str, dict]:
    import gzip
    want = set(ids)
    out = {}
    with gzip.open(DATASET, "rt") as f:
        for line in f:
            rec = json.loads(line)
            if rec["id"] in want:
                out[rec["id"]] = rec
                if len(out) == len(want):
                    break
    return out


def dataset_table() -> pd.DataFrame:
    recs = dataset_records(DATASET_RANDOM)
    rows = []
    for pid, (name, model, par) in DATASET_RANDOM.items():
        rec = recs.get(pid)
        if rec is None:
            continue
        n, m, width = rec["n"], rec["m"], rec.get("width")
        c = 2 * m / n
        row = {"id": pid, "graph": name, "n": n, "m": m, "mean_degree": c, "width": width,
               "provenance": rec.get("provenance"), "model": model,
               "floor_0.05": None, "beta_star": None, "note": ""}
        if model == "gnm":
            row["floor_0.05"] = gnm_floors(n, m)[0.05]
            row["beta_star"] = beta_star_gnp(c)
        elif model == "gnd":
            row["floor_0.05"] = gnd_floors(n, par)[0.05]
            row["beta_star"] = beta_star_gnd(par)
        elif model == "gnp-matched":
            row["floor_0.05"] = gnp_floors(n, c / (n - 1))[0.05]
            row["beta_star"] = beta_star_gnp(c)
            row["note"] = "G(n,p) at the same mean degree: a comparison, not a bound"
        elif model == "hypercube":
            row["floor_0.05"] = hypercube_pathwidth(par)
            row["note"] = "Harper's theorem: exact"
        rows.append(row)
    return pd.DataFrame(rows)


def harper_table(budget: float = 120.0) -> pd.DataFrame:
    rows = []
    for d in (3, 4, 5):
        prof = simplicial_profile(d)
        exact = harper_profile(hypercube_masks(d), 1 << d, budget=budget) if d <= 4 else None
        rows.append({"graph": f"Q_{d}", "n": 1 << d, "pw_exact": hypercube_pathwidth(d),
                     "harper_simplicial": max(prof),
                     "harper_bb": harper_value(exact) if exact else None,
                     "bb_complete": (exact is not None and exact[-1] is not None and len(exact) == (1 << d))})
    for d in (6,):
        prof = simplicial_profile(d)
        rows.append({"graph": f"Q_{d}", "n": 1 << d, "pw_exact": hypercube_pathwidth(d),
                     "harper_simplicial": max(prof), "harper_bb": None, "bb_complete": False})
    for h, w in ((3, 3), (4, 4), (4, 6), (5, 5), (6, 6)):
        n = h * w
        prof = harper_profile(grid_masks(h, w), n, t_max=n // 2 + 1, budget=budget)
        rows.append({"graph": f"grid {h}x{w}", "n": n, "pw_exact": min(h, w) if n > 1 else 0,
                     "harper_simplicial": None, "harper_bb": harper_value(prof),
                     "bb_complete": prof[-1] is not None and len(prof) == n // 2 + 1})
    return pd.DataFrame(rows)


def harvey_summary(frame: pd.DataFrame, levels=LEVELS) -> pd.DataFrame:
    out = []
    for (fam, n, m, k), g in frame.groupby(["family", "n", "m", "param"]):
        row = {"family": fam, "n": n, "m": m, "param": k, "count": len(g), "pw_mean": g.pw.mean(),
               "opt_over_n": g.optimum.mean() / n}
        for lv in levels:
            row[f"model_{lv}"] = g[f"model_floor_{lv}"].mean()
            row[f"uniform_{lv}"] = g[f"uniform_floor_{lv}"].mean()
        row["model_viol_0.01"] = int((g.pw < g["model_floor_0.01"]).sum())
        row["uniform_viol_0.01"] = int((g.pw < g["uniform_floor_0.01"]).sum())
        row["model_tight_0.01"] = int((g.pw == g["model_floor_0.01"]).sum())
        row["gap_0.01"] = (g.pw - g["model_floor_0.01"]).mean()
        out.append(row)
    return pd.DataFrame(out)


def collection_summary(frame: pd.DataFrame) -> pd.DataFrame:
    out = []
    for coll, g in frame.groupby("collection"):
        out.append({"collection": coll, "count": len(g), "n_min": g.n.min(), "n_max": g.n.max(),
                    "excess_median": g.excess.median(), "opt_over_n": (g.optimum / g.n).mean(),
                    "beta_star_mean": g.beta_star.mean(),
                    "floor_0.01_tight": int((g.pw == g["floor_0.01"]).sum()),
                    "floor_0.01_viol": int((g.pw < g["floor_0.01"]).sum()),
                    "gap_0.01_mean": (g.pw - g["floor_0.01"]).mean(),
                    "gap_0.01_max": (g.pw - g["floor_0.01"]).max(),
                    "gap_over_n": ((g.pw - g["floor_0.01"]) / g.n).mean()})
    return pd.DataFrame(out)


def _md(frame: pd.DataFrame, floatfmt: str = ".3f") -> str:
    return frame.to_markdown(index=False, floatfmt=floatfmt)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", default="all",
                    choices=["all", "gnd", "cages", "harvey", "collections", "ensemble", "harper", "dataset"])
    ap.add_argument("--budget", type=float, default=120.0)
    args = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    stages = [args.stage] if args.stage != "all" else ["gnd", "cages", "harvey", "collections", "ensemble", "harper", "dataset"]
    for stage in stages:
        t0 = time.time()
        if stage == "gnd":
            frame = gnd_table()
        elif stage == "cages":
            frame = cages_table()
        elif stage == "harvey":
            rows = harvey_rows()
            rows.to_csv(OUT / "harvey_rows.csv", index=False)
            frame = harvey_summary(rows)
        elif stage == "collections":
            rows = collection_rows()
            rows.to_csv(OUT / "collection_rows.csv", index=False)
            cells = chu_stuckey_cells(rows)
            cells.to_csv(OUT / "chu_stuckey_cells.csv", index=False)
            print("## Chu & Stuckey cells\n")
            print(_md(cells))
            frame = collection_summary(rows)
        elif stage == "ensemble":
            frame = ensemble_cells()
        elif stage == "harper":
            frame = harper_table(args.budget)
        else:
            frame = dataset_table()
        frame.to_csv(OUT / f"{stage}.csv", index=False)
        print(f"\n## {stage} ({time.time() - t0:.1f} s)\n")
        print(_md(frame))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
