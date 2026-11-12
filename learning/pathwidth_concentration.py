"""The standard deviation of the pathwidth of a random graph
(reports/pathwidth_concentration.md).

Three parts, each a measurement or a check on proved widths already on record;
nothing here solves a graph.

Part 1, the martingale ceiling.  Pathwidth is 1-Lipschitz under *vertex
exposure*: two graphs that agree on every pair avoiding `v` have pathwidths
within one (insert `v` into every bag of a decomposition of the other graph).
`check_lipschitz` brute-forces this on every graph with at most `max_n`
vertices (the networkx atlas, 1,253 graphs to 7 vertices), every vertex and
every replacement of its neighbourhood, with
`fixed_parameter_algorithm.pathwidth.compute_pathwidth` as the oracle; the Lean
proof is `lean/MOSPFormalization/Concentration.lean`.  McDiarmid's inequality
then gives `P(|pw - E pw| >= t) <= 2 exp(-2 t^2 / n)` and `Var(pw) <= n / 4`
(`mcdiarmid_tail`, `variance_ceiling`), for every `p`.

Part 2, the dense regime.  `dense_cells` tabulates the proved widths of the
`p = 1/2` cells of `reports/scratch/random_graph_middle/results.csv` (20 graphs
per cell at `n = 30, 40, 50, 60`): the distribution of `pw`, its standard
deviation, the mass on the two most frequent values, beside the corner-block
first-moment threshold `s*` of `learning.staircase_moment`.  The mathematics is
the second moment on staircases near its threshold.  Writing the ratio as a sum
over partial injections `tau` from the slots of a fixed staircase `S_0` to the
slots of a placement `S'` (`ratio_from_injections`, exact), the terms that
matter are the bijections of the corner block onto itself, and for those the
overlap lost against the aligned placement is at least the *floored depth*
`sum_i (pi(i) - max(i, F))^+` of either permutation (`check_loss_lemma`, brute
force; `depth_floor`).  Its generating function `Psi_{l,F}(x) = sum_pi
x^{depth_F(pi)}` has a transfer-matrix form (`depth_gf`, checked against
enumeration by `depth_gf_brute`) with growth rate `log rho(T(x))`
(`depth_rate`), so the family's slack is `exp(O(L))`, `L = log_b n`, and the
window of `n - pw` is `ceil(sigma + 1)` values with
`sigma = kappa / ((a* - 2) ln b)` (`window_estimate`): bounded, two-point iff
`sigma < 1`.

Part 3, the sparse regime.  `sparse_cells` tabulates mean, standard deviation
and coefficient of variation per cell of the proved `G(n, c/n)` graphs of
`reports/scratch/gnp_pilot/results.csv` (c fixed, `n = 20..120`), the
middle-regime cells (`c = 2 ln n, sqrt n, n^0.7`), and — labelled as a clique
cover model, not `G(n, p)` — the Bernoulli cells of `learning/data/ensemble/`
(`pw = optimum - 1` of the MOSP graph).  `fit_growth` fits `sd ~ n^gamma` at
fixed `c` with the standard error of `gamma`, against `gamma = 1/2` (the
martingale ceiling) and `gamma = 0` (bounded).

Usage:
    python -m learning.pathwidth_concentration lipschitz   # Part 1 brute force (about 3 min)
    python -m learning.pathwidth_concentration dense       # Part 2 tables
    python -m learning.pathwidth_concentration overlap     # Part 2 overlap analysis
    python -m learning.pathwidth_concentration sparse      # Part 3 tables and fits
    python -m pytest tests/test_pathwidth_concentration.py -q
"""
from __future__ import annotations

import csv
import itertools
import math
import statistics
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / "reports" / "scratch" / "pathwidth_concentration"
MIDDLE_CSV = ROOT / "reports" / "scratch" / "random_graph_middle" / "results.csv"
PILOT_CSV = ROOT / "reports" / "scratch" / "gnp_pilot" / "results.csv"
ENSEMBLE_CSV = ROOT / "learning" / "data" / "ensemble" / "results.csv"
UPWARD_CSV = ROOT / "learning" / "data" / "ensemble" / "results_upward.csv"
PROVED = {"refutation", "minor", "bound"}
A_STAR = 2 + math.sqrt(2)


# ---------------------------------------------------------------------------
# Part 1: the Lipschitz lemma, brute-forced
# ---------------------------------------------------------------------------

def _pw_oracle(edges: frozenset, n: int, memo: dict) -> int:
    """Exact pathwidth of the labelled graph on `0..n-1` with the given edges,
    by the subset DP of `fixed_parameter_algorithm.pathwidth` (memoised)."""
    key = (n, edges)
    if key not in memo:
        import networkx as nx
        from fixed_parameter_algorithm.pathwidth import compute_pathwidth
        G = nx.Graph()
        G.add_nodes_from(range(n))
        G.add_edges_from(edges)
        memo[key] = compute_pathwidth(G)[0]
    return memo[key]


def check_lipschitz(max_n: int = 7, log=None, cross_check: bool = True) -> dict:
    """Every graph on at most `max_n` vertices (networkx atlas), every vertex `v`,
    every subset `N'` of the other vertices as the new neighbourhood of `v`:
    `|pw(G) - pw(G')| <= 1`, and `pw(G - v) in {pw(G) - 1, pw(G)}`.  Returns the
    counts; `cross_check` also compares the oracle with the bitmask DP of
    `learning.staircase_moment.pathwidth_exact` on every graph met."""
    import networkx as nx
    from learning.staircase_moment import pathwidth_exact
    memo: dict = {}
    out = dict(graphs=0, pairs=0, violations=0, diff0=0, diff1=0,
               deletions=0, deletion_violations=0, deletion_drop=0,
               oracle_disagreements=0, max_n=max_n, seconds=0.0)
    t0 = time.time()
    for G in nx.graph_atlas_g():
        n = G.number_of_nodes()
        if n == 0 or n > max_n:
            continue
        out["graphs"] += 1
        edges = frozenset(frozenset(e) for e in G.edges())
        pw = _pw_oracle(edges, n, memo)
        if cross_check:
            adj = [0] * n
            for e in edges:
                a, b = tuple(e)
                adj[a] |= 1 << b
                adj[b] |= 1 << a
            if pathwidth_exact(adj, n) != pw:
                out["oracle_disagreements"] += 1
        for v in range(n):
            others = [u for u in range(n) if u != v]
            base = frozenset(e for e in edges if v not in e)
            # deletion: the graph G - v, relabelled to 0..n-2
            rel = {u: k for k, u in enumerate(others)}
            del_edges = frozenset(frozenset((rel[a], rel[b])) for a, b in (tuple(e) for e in base))
            pw_del = _pw_oracle(del_edges, n - 1, memo) if n > 1 else 0
            out["deletions"] += 1
            if not (pw_del <= pw <= pw_del + 1):
                out["deletion_violations"] += 1
            if pw_del == pw - 1:
                out["deletion_drop"] += 1
            for r in range(len(others) + 1):
                for nbrs in itertools.combinations(others, r):
                    new_edges = base | frozenset(frozenset((v, u)) for u in nbrs)
                    pw2 = _pw_oracle(new_edges, n, memo)
                    out["pairs"] += 1
                    d = abs(pw - pw2)
                    if d > 1:
                        out["violations"] += 1
                    elif d == 1:
                        out["diff1"] += 1
                    else:
                        out["diff0"] += 1
        if log is not None:
            print(f"n={n} graphs={out['graphs']} pairs={out['pairs']} violations={out['violations']}",
                  file=log, flush=True)
    out["seconds"] = round(time.time() - t0, 1)
    out["distinct_graphs_evaluated"] = len(memo)
    return out


def mcdiarmid_tail(n: int, t: float) -> float:
    """McDiarmid: `P(|pw - E pw| >= t) <= 2 exp(-2 t^2 / n)` (n vertex-exposure
    coordinates of difference at most one)."""
    return 2 * math.exp(-2 * t * t / n)


def variance_ceiling(n: int) -> float:
    """`Var(pw) <= n/4` by the bounded-differences (Efron-Stein) bound; the
    standard deviation is at most `sqrt(n)/2`."""
    return n / 4


def median_shift(n: int) -> float:
    """`|E pw - median pw| <= sqrt(n ln 2 / 2)`: the one-sided McDiarmid tail is
    below 1/2 beyond that distance, so the median lies within it of the mean."""
    return math.sqrt(n * math.log(2) / 2)


# ---------------------------------------------------------------------------
# Cell statistics
# ---------------------------------------------------------------------------

def cell_stats(values: list[int]) -> dict:
    """Mean, sample standard deviation, coefficient of variation, range, the
    histogram and the mass on the two most frequent values."""
    N = len(values)
    hist = Counter(values)
    top = sorted(hist.values(), reverse=True)
    mean = statistics.fmean(values)
    sd = statistics.stdev(values) if N > 1 else 0.0
    return dict(N=N, mean=mean, sd=sd, cv=(sd / mean if mean else float("nan")),
                min=min(values), max=max(values), spread=max(values) - min(values),
                hist=dict(sorted(hist.items())), top1=top[0] / N,
                top2=(top[0] + (top[1] if len(top) > 1 else 0)) / N,
                median=statistics.median(values),
                sd_se=(sd / math.sqrt(2 * (N - 1)) if N > 1 else float("nan")))


def _read_csv(path: Path) -> list[dict]:
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


# ---------------------------------------------------------------------------
# Part 2: the dense cells
# ---------------------------------------------------------------------------

def middle_rows(path: Path = MIDDLE_CSV) -> list[dict]:
    rows = [r for r in _read_csv(path) if r["status"] in PROVED]
    for r in rows:
        r["n"] = int(r["n"]); r["width"] = int(r["width"]); r["p"] = float(r["p"]); r["c"] = float(r["c"])
    return rows


def dense_cells(path: Path = MIDDLE_CSV) -> list[dict]:
    """Per `p = 1/2` cell: the statistics of `pw` and of `n - pw`, with the block
    first-moment threshold `s*` (symmetric count), the staircase threshold, and
    the measured drop of the block bound per unit of `s` at `s*`."""
    from learning.staircase_moment import block_floor_log, block_threshold, staircase_threshold
    cells = defaultdict(list)
    for r in middle_rows(path):
        if r["family"] == "dense":
            cells[r["n"]].append(r["width"])
    out = []
    for n in sorted(cells):
        vals = cells[n]
        st = cell_stats(vals)
        q = 0.5
        s_star = block_threshold(n, q, 1.0, True) + 1          # least s with block bound < 1
        drop = block_floor_log(n, q, s_star)[0] - block_floor_log(n, q, s_star - 1)[0]
        L = math.log(n) / math.log(1 / q)
        out.append(dict(n=n, p=0.5, L=L, s_star=s_star, s_staircase=staircase_threshold(n, q),
                        drop_per_step=drop, drop_predicted=-(A_STAR - 2) * math.log(n),
                        nminus=cell_stats([n - w for w in vals]), **st))
    return out


# ---------------------------------------------------------------------------
# Part 2: the overlap sum near the threshold
# ---------------------------------------------------------------------------

def forced_pairs_slots(s: int) -> list[tuple[int, int]]:
    """The forced pairs of a staircase of size `s` as slot pairs `(u_i, v_j)`,
    1-indexed, `i + j <= s`, `i, j <= s - 1`."""
    m = s - 1
    return [(i, j) for i in range(1, m + 1) for j in range(1, m + 1) if i + j <= s]


def overlap_perm(s: int, a: int, b: int, pi_u: tuple, pi_v: tuple) -> int:
    """Forced pairs `(u_i, v_j)`, `i <= b`, `j <= a`, `i + j <= s`, that stay forced
    when `u_i` goes to slot `u'_{pi_u[i]}` and `v_j` to `v'_{pi_v[j]}` (1-indexed
    tuples: `pi_u[i-1]`)."""
    return sum(1 for i in range(1, b + 1) for j in range(1, a + 1)
               if i + j <= s and pi_u[i - 1] + pi_v[j - 1] <= s)


def depth_floor(pi: tuple, F: int) -> int:
    """`sum_i (pi(i) - max(i, F))^+`, 1-indexed; `F <= 1` is the plain depth
    `sum_i (pi(i) - i)^+` (half the footrule)."""
    return sum(max(0, pi[i - 1] - max(i, F)) for i in range(1, len(pi) + 1))


def check_loss_lemma(s: int, a: int, b: int) -> dict:
    """Over every pair of permutations of the block's `u`'s and `v`'s: the loss
    `c(s, a, b) - overlap` is at least `max(depth_{s-a}(pi_u), depth_{s-b}(pi_v))`,
    and with `pi_v = id` it equals `depth_{s-a}(pi_u)` exactly."""
    from learning.staircase_moment import block_cost
    c = block_cost(s, a, b)
    out = dict(pairs=0, violations=0, equality_id=0, equality_id_violations=0, tight=0)
    ident_v = tuple(range(1, a + 1))
    for pi_u in itertools.permutations(range(1, b + 1)):
        du = depth_floor(pi_u, s - a)
        loss_id = c - overlap_perm(s, a, b, pi_u, ident_v)
        out["equality_id"] += 1
        if loss_id != du:
            out["equality_id_violations"] += 1
        for pi_v in itertools.permutations(range(1, a + 1)):
            dv = depth_floor(pi_v, s - b)
            loss = c - overlap_perm(s, a, b, pi_u, pi_v)
            out["pairs"] += 1
            if loss < max(du, dv):
                out["violations"] += 1
            if loss == max(du, dv):
                out["tight"] += 1
    return out


def depth_gf_brute(ell: int, F: int, x: float) -> float:
    """`Psi_{ell, F}(x) = sum_pi x^{depth_F(pi)}` by enumeration."""
    return sum(x ** depth_floor(pi, F) for pi in itertools.permutations(range(1, ell + 1)))


def depth_gf(ell: int, F: int, x, exact: bool = False):
    """`Psi_{ell, F}(x)` by the transfer matrix over the number `e` of open
    positions: scanning `k = 1..ell`, position `k` takes value `k` (1 way, `e`
    unchanged), an open value and value `k` closes an open position (`e^2` ways,
    `e - 1`), an open value with value `k` deferred or deferred with value `k`
    closing an open position (`e` ways each, `e` unchanged), or both deferred
    (1 way, `e + 1`); the weight `x^e` is charged after every step `k >= F`,
    since `depth_F(pi) = sum_{k >= F} #{i <= k : pi(i) > k}`.  `exact=True`
    works in `Fraction`; for large `ell` use `log_depth_gf`."""
    zero = Fraction(0) if exact else 0.0
    state = {0: Fraction(1) if exact else 1.0}
    for k in range(1, ell + 1):
        state = _depth_step(state, k, ell, F, x, zero)
    return state.get(0, zero)


def _depth_step(state: dict, k: int, ell: int, F: int, x, zero) -> dict:
    nxt: dict = defaultdict(lambda: zero)
    for e, w in state.items():
        if w == 0:
            continue
        nxt[e] += w * (1 + 2 * e)
        if e >= 1:
            nxt[e - 1] += w * e * e
        if k < ell:
            nxt[e + 1] += w
    if k >= F:
        return {e: w * (x ** e) for e, w in nxt.items()}
    return dict(nxt)


def log_depth_gf(ell: int, F: int, x: float) -> float:
    """`ln Psi_{ell, F}(x)` by the same transfer matrix, renormalised at every
    step so that `ell` in the thousands does not overflow."""
    state = {0: 1.0}
    acc = 0.0
    for k in range(1, ell + 1):
        state = _depth_step(state, k, ell, F, x, 0.0)
        mx = max(state.values())
        acc += math.log(mx)
        state = {e: w / mx for e, w in state.items()}
    return acc + math.log(state[0])


def depth_rate(x: float, emax: int = 80, iters: int = 4000) -> float:
    """`kappa_0(x) = lim (1/ell) ln Psi_ell(x)`: the log spectral radius of the
    transfer matrix `T[e][e'] = mult(e -> e') x^{e'}`, by power iteration on the
    states `0..emax` (the weights `x^e` make the tail negligible)."""
    import numpy as np
    T = np.zeros((emax + 1, emax + 1))
    for e in range(emax + 1):
        T[e, e] = (1 + 2 * e) * x ** e
        if e >= 1:
            T[e, e - 1] = e * e * x ** (e - 1)
        if e + 1 <= emax:
            T[e, e + 1] = x ** (e + 1)
    v = np.ones(emax + 1) / (emax + 1)
    lam = 1.0
    for _ in range(iters):
        w = v @ T
        lam = float(np.linalg.norm(w))
        v = w / lam
    return math.log(lam)


def log_factorial(k: int) -> float:
    return math.lgamma(k + 1)


def family_slack_log(q: float, s: int, a: int, b: int) -> dict:
    """The block-bijection family's slack against `1 / E_sym[B(s, a, b)]`:
    `ln(Psi_{b, s-a}(x) Psi_{a, s-b}(x) / ((s-a)! (s-b)!))` at `x = sqrt q`
    (the proved upper bracket: loss >= max of the two depths) and at `x = q`
    for one side only (the lower bracket: `pi_v = id`), plus the role swap."""
    xu = math.sqrt(q)
    hi = (log_depth_gf(b, s - a, xu) + log_depth_gf(a, s - b, xu)
          - log_factorial(s - a) - log_factorial(s - b) + math.log(2))
    lo = max(log_depth_gf(b, s - a, q) - log_factorial(s - a),
             log_depth_gf(a, s - b, q) - log_factorial(s - b))
    return dict(log_slack_hi=hi, log_slack_lo=lo)


def family_exact_log(q: float, s: int, a: int, b: int) -> float:
    """`ln sum_{pi_u, pi_v} q^{loss} / ((s-a)! (s-b)!)` by enumeration (small blocks)."""
    from learning.staircase_moment import block_cost
    c = block_cost(s, a, b)
    tot = 0.0
    for pi_u in itertools.permutations(range(1, b + 1)):
        for pi_v in itertools.permutations(range(1, a + 1)):
            tot += q ** (c - overlap_perm(s, a, b, pi_u, pi_v))
    return math.log(tot) - log_factorial(s - a) - log_factorial(s - b)


def window_estimate(p: float, Ls=(10, 20, 40, 80, 160, 320)) -> dict:
    """At `s = a* L`, `a = b = (a* - 1) L` (so the flat floor is `F = L` and the
    sloped length `(a* - 2) L`): the slack's growth rate per unit `L` from the
    finite sums (both brackets), the per-step gain `(a* - 2) ln b` of the block
    first moment, and `sigma = kappa / gain`: the window of `n - pw` has
    `ceil(sigma + 1)` values; two-point iff `sigma < 1`."""
    q = 1 - p
    lnb = math.log(1 / q)
    gain = (A_STAR - 2) * lnb
    rows = []
    for L in Ls:
        s = round(A_STAR * L)
        a = round((A_STAR - 1) * L)
        fs = family_slack_log(q, s, a, a)
        rows.append(dict(L=L, s=s, a=a, **fs))
    # slopes from the two largest L
    r1, r2 = rows[-2], rows[-1]
    kappa_hi = (r2["log_slack_hi"] - r1["log_slack_hi"]) / (r2["L"] - r1["L"])
    kappa_lo = (r2["log_slack_lo"] - r1["log_slack_lo"]) / (r2["L"] - r1["L"])
    return dict(p=p, gain_per_step=gain, rows=rows, kappa_hi=kappa_hi, kappa_lo=kappa_lo,
                sigma_hi=kappa_hi / gain, sigma_lo=kappa_lo / gain,
                window_hi=math.ceil(kappa_hi / gain + 1 - 1e-9), window_lo=math.ceil(kappa_lo / gain + 1 - 1e-9),
                rate_hi_asymptotic=2 * depth_rate(math.sqrt(q)) * (A_STAR - 2),
                rate_lo_asymptotic=depth_rate(q) * (A_STAR - 2))


def ratio_from_injections(n: int, q: Fraction, s: int) -> Fraction:
    """`E[X_s^2]/E[X_s]^2` written as a sum over partial injections `tau` from
    the `2m` slots of `S_0` to the `2m` slots of `S'`:
    `sum_tau (n-2m)_{2m-|tau|} / (n)_{2m} * b^{ov(tau)}`, `ov(tau)` the forced
    pairs of `S_0` inside `dom tau` whose images are forced in `S'`.  Exact;
    equals `learning.staircase_moment.exact_ratio_small`."""
    m = s - 1
    slots = list(range(2 * m))            # 0..m-1 the v's, m..2m-1 the u's
    forced = set()
    for i, j in forced_pairs_slots(s):   # (u_i, v_j) -> slots (m + i - 1, j - 1)
        forced.add(frozenset((m + i - 1, j - 1)))
    b = 1 / q

    def falling(x, k):
        r = 1
        for t in range(k):
            r *= x - t
        return r

    total = Fraction(0)
    denom = falling(n, 2 * m)
    for jsize in range(0, 2 * m + 1):
        weight = Fraction(falling(n - 2 * m, 2 * m - jsize), denom)
        if weight == 0:
            continue
        for dom in itertools.combinations(slots, jsize):
            for img in itertools.permutations(slots, jsize):
                tau = dict(zip(dom, img))
                ov = sum(1 for pr in forced
                         if all(x in tau for x in pr)
                         and frozenset(tau[x] for x in pr) in forced)
                total += weight * b ** ov
    return total


# ---------------------------------------------------------------------------
# Part 3: the sparse cells
# ---------------------------------------------------------------------------

def pilot_cells(path: Path = PILOT_CSV, min_proved: int = 10) -> list[dict]:
    """Per `(n, c)` cell of the `G(n, c/n)` pilot: proved widths only, with the
    censoring recorded (cells where some graph was not proved are flagged)."""
    rows = _read_csv(path)
    cells = defaultdict(list)
    totals = Counter()
    for r in rows:
        key = (int(r["n"]), float(r["c"]))
        totals[key] += 1
        if r["status"] in PROVED:
            cells[key].append(int(r["width"]))
    out = []
    for (n, c) in sorted(cells):
        vals = cells[(n, c)]
        if len(vals) < min_proved:
            continue
        st = cell_stats(vals)
        out.append(dict(model="G(n, c/n)", n=n, c=c, total=totals[(n, c)],
                        censored=totals[(n, c)] - len(vals), **st))
    return out


def middle_cells(path: Path = MIDDLE_CSV) -> list[dict]:
    cells = defaultdict(list)
    for r in middle_rows(path):
        cells[(r["family"], r["n"])].append((r["width"], r["c"], r["p"]))
    out = []
    for (fam, n) in sorted(cells):
        vals = [w for w, _, _ in cells[(fam, n)]]
        c = cells[(fam, n)][0][1]
        p = cells[(fam, n)][0][2]
        out.append(dict(model="G(n, p) middle", family=fam, n=n, c=c, p=p, censored=0, total=len(vals),
                        **cell_stats(vals)))
    return out


def ensemble_cells(paths=(ENSEMBLE_CSV, UPWARD_CSV)) -> list[dict]:
    """The Bernoulli clique-cover cells: `n` customers, `m` products, each entry
    `Bernoulli(p)`; `pw(MOSP graph) = optimum - 1`.  Not `G(n, p)`."""
    cells = defaultdict(list)
    totals = Counter()
    for path in paths:
        if not path.exists():
            continue
        for r in _read_csv(path):
            if r.get("generator") != "bernoulli":
                continue
            key = (int(r["n"]), int(r["m"]), float(r["param"]))
            totals[key] += 1
            if r.get("certified", "True") == "True":
                cells[key].append(int(r["optimum"]) - 1)
    out = []
    for (n, m, p) in sorted(cells):
        vals = cells[(n, m, p)]
        out.append(dict(model="Bernoulli cover", n=n, m=m, p=p, ratio=m / n, total=totals[(n, m, p)],
                        censored=totals[(n, m, p)] - len(vals), **cell_stats(vals)))
    return out


def fit_growth(points: list[tuple[int, float, int]]) -> dict:
    """Weighted least squares of `ln sd = alpha + gamma ln n` over `(n, sd, N)`,
    weights `2(N - 1)` (the inverse variance of `ln sd` for a normal sample);
    returns `gamma`, its standard error, and the chi-square of the fits with
    `gamma` fixed at `1/2` and at `0`."""
    pts = [(n, sd, N) for n, sd, N in points if sd > 0 and N > 2]
    if len(pts) < 3:
        return dict(points=len(pts), gamma=float("nan"), se=float("nan"))
    xs = [math.log(n) for n, _, _ in pts]
    ys = [math.log(sd) for _, sd, _ in pts]
    ws = [2.0 * (N - 1) for _, _, N in pts]
    W = sum(ws)
    xbar = sum(w * x for w, x in zip(ws, xs)) / W
    ybar = sum(w * y for w, y in zip(ws, ys)) / W
    sxx = sum(w * (x - xbar) ** 2 for w, x in zip(ws, xs))
    sxy = sum(w * (x - xbar) * (y - ybar) for w, x, y in zip(ws, xs, ys))
    gamma = sxy / sxx
    alpha = ybar - gamma * xbar
    se = math.sqrt(1 / sxx)
    chi_free = sum(w * (y - alpha - gamma * x) ** 2 for w, x, y in zip(ws, xs, ys))

    def chi_fixed(g):
        a = ybar - g * xbar
        return sum(w * (y - a - g * x) ** 2 for w, x, y in zip(ws, xs, ys))

    return dict(points=len(pts), gamma=gamma, se=se, alpha=alpha, chi2_free=chi_free,
                chi2_half=chi_fixed(0.5), chi2_zero=chi_fixed(0.0), dof=len(pts) - 2,
                half_within_2se=abs(gamma - 0.5) <= 2 * se, zero_within_2se=abs(gamma) <= 2 * se)


def sparse_fits(pilot: list[dict], uncensored_only: bool = True) -> list[dict]:
    """One fit per `c` over the pilot's cells."""
    byc = defaultdict(list)
    for r in pilot:
        if uncensored_only and r["censored"]:
            continue
        byc[r["c"]].append((r["n"], r["sd"], r["N"]))
    out = []
    for c in sorted(byc):
        f = fit_growth(byc[c])
        out.append(dict(c=c, ns=[n for n, _, _ in byc[c]], **f))
    return out


# ---------------------------------------------------------------------------
# Tables
# ---------------------------------------------------------------------------

def _write_csv(path: Path, rows: list[dict], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow({k: (f"{v:.4f}" if isinstance(v, float) else v) for k, v in r.items() if k in fields})


def main(argv=None) -> None:
    argv = sys.argv[1:] if argv is None else argv
    SCRATCH.mkdir(parents=True, exist_ok=True)
    what = argv[0] if argv else "all"
    if what in ("lipschitz", "all"):
        with open(SCRATCH / "lipschitz.log", "w") as log:
            out = check_lipschitz(7, log=log)
            print(out, file=log)
        print(out)
    if what in ("dense", "all"):
        rows = dense_cells()
        fields = ["n", "p", "L", "N", "mean", "sd", "sd_se", "cv", "median", "min", "max", "spread",
                  "top1", "top2", "s_star", "s_staircase", "drop_per_step", "drop_predicted", "hist"]
        _write_csv(SCRATCH / "dense_cells.csv", rows, fields)
        for r in rows:
            print({k: r[k] for k in fields})
    if what in ("overlap", "all"):
        with open(SCRATCH / "overlap.log", "w") as log:
            for s, a, b in [(4, 3, 3), (5, 3, 3), (5, 4, 4), (6, 4, 4), (6, 5, 5), (7, 5, 5), (7, 5, 4), (8, 6, 5)]:
                print("loss lemma", (s, a, b), check_loss_lemma(s, a, b), file=log, flush=True)
            for x in (0.5, 0.7071067811865476, 0.3, 0.8366600265340756):
                for F in (1, 3):
                    for ell in range(1, 9):
                        print("depth_gf", x, F, ell, depth_gf_brute(ell, F, x), depth_gf(ell, F, x), file=log)
                print("depth_rate", x, depth_rate(x), file=log, flush=True)
            for p in (0.3, 0.5, 0.7):
                w = window_estimate(p)
                print("window", p, {k: v for k, v in w.items() if k != "rows"}, file=log)
                for r in w["rows"]:
                    print("  ", r, file=log)
            for (s, a, b) in [(6, 4, 4), (7, 5, 5), (8, 6, 6)]:
                for q in (0.5, 0.7):
                    print("family exact", (s, a, b, q), family_exact_log(q, s, a, b), family_slack_log(q, s, a, b), file=log, flush=True)
        print((SCRATCH / "overlap.log").read_text())
    if what in ("sparse", "all"):
        pilot = pilot_cells()
        mid = middle_cells()
        ens = ensemble_cells()
        fields = ["model", "family", "n", "c", "p", "m", "ratio", "N", "total", "censored", "mean", "sd", "sd_se", "cv",
                  "min", "max", "spread", "top2", "hist"]
        _write_csv(SCRATCH / "sparse_cells.csv", pilot + mid + ens, fields)
        fits = sparse_fits(pilot)
        _write_csv(SCRATCH / "sparse_fits.csv", fits,
                   ["c", "ns", "points", "gamma", "se", "alpha", "chi2_free", "chi2_half", "chi2_zero", "dof",
                    "half_within_2se", "zero_within_2se"])
        for f in fits:
            print(f)
        # the cover cells at fixed (m/n, p) across n
        byk = defaultdict(list)
        for r in ens:
            if not r["censored"]:
                byk[(round(r["ratio"], 2), r["p"])].append((r["n"], r["sd"], r["N"]))
        cfits = [dict(ratio=k[0], p=k[1], ns=[n for n, _, _ in v], **fit_growth(v)) for k, v in sorted(byk.items())]
        _write_csv(SCRATCH / "cover_fits.csv", cfits,
                   ["ratio", "p", "ns", "points", "gamma", "se", "chi2_free", "chi2_half", "chi2_zero", "dof",
                    "half_within_2se", "zero_within_2se"])
        for f in cfits:
            print(f)


if __name__ == "__main__":
    main()
