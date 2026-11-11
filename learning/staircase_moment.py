"""Staircases in dense random graphs: the lemma, the moments, the corner block
(reports/dense_staircase.md).

A *staircase of size s* in a graph `G` on `n` vertices is a pair of sequences
`v_1 .. v_{s-1}`, `u_1 .. u_{s-1}` of vertices, all `2s - 2` distinct, with
`u_i` non-adjacent to `v_1, .., v_{s-i}` for every `i`.  The *generalised*
form drops the distinctness between the two sequences and asks only
`u_i not in {v_1 .. v_{s-i}}` (the `u`'s stay distinct among themselves, the
`v`'s too).

The lemma (`has_staircase`, checked against the subset-DP pathwidth on every
labelled graph with `n <= 6` and samples at `n = 7`):

    pw(G) <= n - s   <=>   a generalised staircase of size s exists;
    a staircase of size s exists   =>   pw(G) <= n - s.

Both directions are elementary (`reports/dense_staircase.md` section 1): order
`v_1 .. v_{s-1}` first; at prefix size `t < s` the vertices `u_1 .. u_{s-t}` are
outside the prefix with no neighbour in it, so at most `n - s` suffix vertices
are active.  Conversely a layout of width `<= n - s` has, at prefix size `t`,
at least `s - t` closed suffix vertices, and the closed sets are nested, so
distinct `u_i` can be drawn greedily.

The moments in `G(n, p)`, `q = 1 - p`, `b = 1/q`, `L = log_b n`:

* `E[X_s] = (n)_{2s-2} q^{s(s-1)/2}` for the ordered count of (strict)
  staircases (`log_first_moment`), threshold `s = (4 - o(1)) L`;
* the *corner block* `(a, b)` of a staircase, `v_1 .. v_a` and `u_1 .. u_b`
  with the `c(s, a, b) = sum_{i <= b} min(a, s - i)` forced non-edges among them
  (`block_cost`): every generalised staircase of size `s` contains one, and the
  union bound gives `P(pw <= n - s) <= (n)_a (n)_b q^{c} / ((s-a)! (s-b)!)`
  for `a + b >= s` (`log_block_moment`, `block_floor_log`), which at
  `a = b = (a* - 1) L` vanishes iff `s > (2 + sqrt 2) L`: the staircase's
  threshold is `(2 + sqrt 2) L`, not `4 L` (`A_STAR`);
* the second-moment ratio `E[X_s^2] / E[X_s]^2 = E_{S'}[b^{|F' ∩ F_0|}]`
  (`S'` a uniform ordered staircase placement, `F_0` the forced pairs of a
  fixed one) is bracketed by two finite double sums over the shared counts
  `(a, b)`: `ratio_log_lower` (same roles, prefix blocks) and
  `ratio_log_upper` (every placement, the overlap bounded by the prefix block),
  both `1 + o(1)` for `s < (2 + sqrt 2 - eps) L` and both exponential in
  `log^2 n` above (`exponent_overlap`); `exact_ratio_small` enumerates `S'`
  at `n <= 7` and `brute_moments` enumerates every labelled graph at `n <= 6`.

Usage:
    python -m learning.staircase_moment     # the report's tables into reports/scratch/dense_staircase/
    python -m pytest tests/test_staircase_moment.py -q
"""
from __future__ import annotations

import csv
import itertools
import math
import random
import sys
from fractions import Fraction
from pathlib import Path

SCRATCH = Path(__file__).resolve().parent.parent / "reports" / "scratch" / "dense_staircase"

#: The staircase threshold constant: `n - pw(G(n, p)) = (A_STAR + o(1)) log_b n`.
A_STAR = 2 + math.sqrt(2)


# ---------------------------------------------------------------------------
# Graphs: pathwidth by subset DP, staircases by search
# ---------------------------------------------------------------------------

def pathwidth_exact(adj: list[int], n: int) -> int:
    """Vertex separation (= pathwidth) of the graph with bitmask adjacency `adj`.

    `f(S)` = the least width of an ordering of `S` as a prefix:
    `f(S) = min_{v in S} max(f(S \\ v), |N(S) \\ S|)`, `f(empty) = 0`.
    """
    full = (1 << n) - 1
    f = [0] * (1 << n)
    for S in range(1, 1 << n):
        nb = 0
        T = S
        while T:
            v = (T & -T).bit_length() - 1
            nb |= adj[v]
            T &= T - 1
        opened = bin(nb & ~S & full).count("1")
        best = n
        T = S
        while T:
            v = (T & -T).bit_length() - 1
            best = min(best, max(f[S & ~(1 << v)], opened))
            T &= T - 1
        f[S] = best
    return f[full]


def has_staircase(adj: list[int], n: int, s: int, generalised: bool = False) -> bool:
    """Is there a staircase of size `s` (strict, or generalised)?

    For a fixed ordered `v_1 .. v_{s-1}` the closed sets
    `C_t = {w not in {v_1..v_t} : w ~/~ v_1 .. v_t}` (strict: `w` not any `v`)
    form a chain `C_{s-1} ⊆ .. ⊆ C_1`, so distinct `u_i ∈ C_{s-i}` exist iff
    `|C_{s-i}| >= i` for every `i` (Hall on a chain).
    """
    if s <= 1:
        return True
    if s > n:
        return False
    full = (1 << n) - 1
    for vs in itertools.permutations(range(n), s - 1):
        vmask_all = 0
        for v in vs:
            vmask_all |= 1 << v
        closed = full
        ok = True
        placed = 0
        for t, v in enumerate(vs, start=1):
            placed |= 1 << v
            closed &= ~adj[v] & ~placed
            c = closed & ~vmask_all if not generalised else closed
            if bin(c).count("1") < s - t:
                ok = False
                break
        if ok:
            return True
    return False


def random_graph(n: int, p: float, rng: random.Random) -> list[int]:
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return adj


def graph_from_edges(n: int, edge_bits: int) -> list[int]:
    """The labelled graph on `n` vertices whose edge set is the bit pattern
    `edge_bits` over the pairs `(i, j)`, `i < j`, in lexicographic order."""
    adj = [0] * n
    k = 0
    for i in range(n):
        for j in range(i + 1, n):
            if edge_bits >> k & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj


def check_lemma(n: int, graphs=None) -> dict:
    """The lemma on every labelled graph (`graphs=None`) or on the given ones:
    `pw <= n - s` iff a generalised staircase; strict => `pw <= n - s`.
    Returns counts, including how often the strict form fails where the
    generalised one holds (the coincidences)."""
    out = {"graphs": 0, "violations": 0, "strict_gap": 0, "pairs": 0}
    if graphs is None:
        graphs = (graph_from_edges(n, e) for e in range(1 << (n * (n - 1) // 2)))
    for adj in graphs:
        pw = pathwidth_exact(adj, n)
        out["graphs"] += 1
        for s in range(1, n + 1):
            gen = has_staircase(adj, n, s, generalised=True)
            strict = has_staircase(adj, n, s, generalised=False)
            out["pairs"] += 1
            if gen != (pw <= n - s):
                out["violations"] += 1
            if strict and not gen:
                out["violations"] += 1
            if gen and not strict:
                out["strict_gap"] += 1
    return out


# ---------------------------------------------------------------------------
# Moments: closed forms
# ---------------------------------------------------------------------------

def log_falling(n: float, k: int) -> float:
    """`ln (n)_k`; `-inf` if `k > n`."""
    if k > n:
        return -math.inf
    return math.lgamma(n + 1) - math.lgamma(n - k + 1)


def log_first_moment(n: int, q: float, s: int) -> float:
    """`ln E[X_s]`, `X_s` the ordered count of strict staircases of size `s`."""
    return log_falling(n, 2 * s - 2) + (s * (s - 1) // 2) * math.log(q)


def block_cost_sum(s: int, a: int, b: int) -> int:
    """`c(s, a, b)` as the sum it is defined by (the test oracle for `block_cost`)."""
    return sum(max(0, min(a, s - i)) for i in range(1, b + 1))


def block_cost(s: int, a: int, b: int) -> int:
    """`c(s, a, b) = #{(i, j) : 1 <= i <= b, 1 <= j <= a, i + j <= s}`, the forced
    non-edges of the corner block `v_1..v_a`, `u_1..u_b` of a staircase of size `s`:
    `a` for each `i <= s - a` and `s - i` for `s - a < i < s`, in closed form."""
    if a <= 0 or b <= 0 or s <= 1:
        return 0
    hi = min(b, s - 1)
    full = max(0, min(hi, s - a))
    total = a * full
    lo = max(1, s - a + 1)
    if hi >= lo:
        total += (2 * s - lo - hi) * (hi - lo + 1) // 2
    return total


def log_block_count(n: int, s: int, a: int, b: int, symmetric: bool = True) -> float:
    """`ln` of an upper bound on the number of distinct forced sets of corner blocks
    `(a, b)` of generalised staircases of size `s` on `n` labelled vertices.

    The *full* rows are `v_1 .. v_{f_v}`, `f_v = min(a, s - b)`, non-adjacent to every
    `u_i`, and the full columns `u_1 .. u_{f_u}`, `f_u = min(b, s - a)`, non-adjacent to
    every `v_j` and distinct from all of them; permuting the full rows among
    themselves, and the full columns, leaves the forced set unchanged, so the count
    is at most `C(n, f_v) (n - f_v)_{a - f_v} C(n - a, f_u) (n - f_v - f_u)_{b - f_u}`
    (`symmetric`), and `(n)_a (n)_b` without that division.  At `(a, b) = (t, t - 1)`,
    `2t - 1 <= s`, the symmetric count is the empty-pair count
    `C(n, t) C(n - t, t - 1)` of reports/random_graph_first_moment.md (0)."""
    if not symmetric:
        return log_falling(n, a) + log_falling(n, b)
    fv = max(0, min(a, s - b))
    fu = max(0, min(b, s - a))
    return (_log_comb(n, fv) + log_falling(n - fv, a - fv)
            + _log_comb(n - a, fu) + log_falling(n - fv - fu, b - fu))


def _log_comb(n: int, k: int) -> float:
    if k < 0 or k > n:
        return -math.inf
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def log_block_moment(n: int, q: float, s: int, a: int, b: int, symmetric: bool = True) -> float:
    """`ln` of the union-bound term for the corner block `(a, b)`:
    `count(n, s, a, b) * q^{c(s, a, b)}`; `P(pw <= n - s)` is at most its minimum
    over `1 <= a, b <= s - 1`."""
    return log_block_count(n, s, a, b, symmetric) + block_cost(s, a, b) * math.log(q)


def block_floor_log(n: int, q: float, s: int, symmetric: bool = True) -> tuple[float, int, int]:
    """`min_{a, b} ln(block term)` and its argmin: `ln P(pw <= n - s) <=` this."""
    best = (math.inf, 0, 0)
    for a in range(1, s):
        for b in range(1, s):
            val = log_block_moment(n, q, s, a, b, symmetric)
            if val < best[0]:
                best = (val, a, b)
    return best


def largest_s(n: int, q: float, f, level: float = 0.0) -> int:
    """The largest `s` with `f(n, q, s) >= ln level` (`level = 0` means `>= 0`,
    i.e. the moment at least one); `f` is decreasing in `s`."""
    thr = math.log(level) if level > 0 else 0.0
    s = 1
    while s + 1 <= n and f(n, q, s + 1) >= thr:
        s += 1
    return s


def staircase_threshold(n: int, q: float) -> int:
    """`s_0`: the largest `s` with `E[X_s] >= 1`."""
    return largest_s(n, q, log_first_moment)


def block_threshold(n: int, q: float, level: float = 1.0, symmetric: bool = True) -> int:
    """The largest `s` with `min_{a,b} block term >= level`; one more is the least
    `s` whose block bound is below `level`, so `pw >= n - s` with probability
    `>= 1 - level`."""
    return largest_s(n, q, lambda n_, q_, s_: block_floor_log(n_, q_, s_, symmetric)[0], level)


def empty_pair_log(n: int, q: float, k: int) -> float:
    """`ln` of inequality (0) of reports/random_graph_first_moment.md:
    `P(pw <= k) <= C(n,t) C(n-t,t-1) q^{t(t-1)}`, `t = ceil((n-k)/2)`."""
    t = (n - k + 1) // 2
    if t < 1 or t > n:
        return 0.0
    return (math.lgamma(n + 1) - math.lgamma(t + 1) - math.lgamma(n - t + 1)
            + math.lgamma(n - t + 1) - math.lgamma(t) - math.lgamma(n - 2 * t + 2)
            + t * (t - 1) * math.log(q))


def empty_pair_floor(n: int, q: float, level: float) -> int:
    """`k_level`: the largest `k` with the empty-pair bound `<= level`."""
    k = -1
    while k + 1 < n and empty_pair_log(n, q, k + 1) <= math.log(level):
        k += 1
    return k


# ---------------------------------------------------------------------------
# The second-moment ratio: finite brackets and the exponent
# ---------------------------------------------------------------------------

def _logsumexp(vals) -> float:
    vals = [v for v in vals if v > -math.inf]
    if not vals:
        return -math.inf
    m = max(vals)
    return m + math.log(sum(math.exp(v - m) for v in vals))


def ratio_log_lower(n: int, q: float, s: int) -> float:
    """`ln` of a lower bound on `E[X_s^2]/E[X_s]^2`: the placements `S'` that
    agree with `S_0` on `v_1..v_a` and `u_1..u_b` in the same roles and are
    disjoint from it elsewhere, overlap exactly `c(s, a, b)`."""
    m = s - 1
    logb = -math.log(q)
    terms = []
    for a in range(m + 1):
        for b in range(m + 1):
            terms.append(log_falling(n - 2 * m, 2 * m - a - b) - log_falling(n, 2 * m)
                         + block_cost(s, a, b) * logb)
    return _logsumexp(terms)


def ratio_log_upper(n: int, q: float, s: int) -> float:
    """`ln` of an upper bound on `E[X_s^2]/E[X_s]^2`: every placement `S'`
    sharing `a` of the `v`'s and `b` of the `u`'s of `S_0` (in any roles) has
    overlap at most `c(s, a, b)`, and there are
    `C(m,a) C(m,b) (2m)_{a+b} (n-2m)_{2m-a-b}` of them."""
    m = s - 1
    logb = -math.log(q)
    terms = []
    for a in range(m + 1):
        for b in range(m + 1):
            j = a + b
            if 2 * m - j > n - 2 * m:
                continue
            terms.append(math.log(math.comb(m, a)) + math.log(math.comb(m, b))
                         + log_falling(2 * m, j) + log_falling(n - 2 * m, 2 * m - j)
                         - log_falling(n, 2 * m) + block_cost(s, a, b) * logb)
    return _logsumexp(terms)


def exponent_overlap(a: float, x: float) -> float:
    """The limit exponent of the overlap term with `x L` shared vertices
    (`x/2 L` of each kind) in units of `L^2 ln b`, `s = a L`:
    `-x + x^2/4 - (x - a)^2/2 [x > a]`; the ratio is `1 + o(1)` iff this is
    negative on `(0, 2a]`, i.e. iff `a < 2 + sqrt 2`."""
    val = -x + x * x / 4
    if x > a:
        val -= (x - a) ** 2 / 2
    return val


def exponent_block(a: float, y: float) -> float:
    """`ln E[#corner blocks (yL, yL)] / (L^2 ln b)` in the limit, `s = a L`:
    `2y - y^2 + (2y - a)^2/2 [2y > a]`; minimised at `y = a - 1` with value
    `a^2/2 - 2a + 1`... with the sign: `-(a^2/2 - 2a + 1)`, zero at `a = 2 + sqrt 2`."""
    val = 2 * y - y * y
    if 2 * y > a:
        val += (2 * y - a) ** 2 / 2
    return val


def worst_overlap(a: float, grid: int = 4000) -> tuple[float, float]:
    """`max_x exponent_overlap(a, x)` over `x in (0, 2a]` and its argmax."""
    best = (-math.inf, 0.0)
    for i in range(1, grid + 1):
        x = 2 * a * i / grid
        v = exponent_overlap(a, x)
        if v > best[0]:
            best = (v, x)
    return best


# ---------------------------------------------------------------------------
# Exact checks at small n
# ---------------------------------------------------------------------------

def forced_pairs(vs: tuple, us: tuple, s: int) -> frozenset:
    return frozenset(frozenset((us[i - 1], vs[j - 1])) for i in range(1, s) for j in range(1, s - i + 1))


def exact_ratio_small(n: int, q: Fraction, s: int) -> Fraction:
    """`E[X_s^2]/E[X_s]^2 = (1/(n)_{2m}) sum_{S'} b^{|F' ∩ F_0|}` exactly, enumerating
    every ordered placement `S'` against the fixed `S_0 = (0..m-1; m..2m-1)`."""
    m = s - 1
    if 2 * m > n:
        return Fraction(0)
    v0 = tuple(range(m))
    u0 = tuple(range(m, 2 * m))
    F0 = forced_pairs(v0, u0, s)
    b = 1 / q
    total = Fraction(0)
    count = 0
    for tup in itertools.permutations(range(n), 2 * m):
        F = forced_pairs(tup[:m], tup[m:], s)
        total += b ** len(F & F0)
        count += 1
    return total / count


def brute_moments(n: int, p: Fraction, s: int) -> tuple[Fraction, Fraction]:
    """`E[X_s]` and `E[X_s^2]` over every labelled graph on `n` vertices, `X_s`
    the ordered count of strict staircases of size `s`."""
    m = s - 1
    placements = []
    for tup in itertools.permutations(range(n), 2 * m):
        F = forced_pairs(tup[:m], tup[m:], s)
        bits = 0
        for pair in F:
            i, j = sorted(pair)
            bits |= 1 << _pair_index(n, i, j)
        placements.append(bits)
    e1 = Fraction(0)
    e2 = Fraction(0)
    C = n * (n - 1) // 2
    for edges in range(1 << C):
        x = sum(1 for bits in placements if edges & bits == 0)
        w = p ** bin(edges).count("1") * (1 - p) ** (C - bin(edges).count("1"))
        e1 += x * w
        e2 += x * x * w
    return e1, e2


def _pair_index(n: int, i: int, j: int) -> int:
    k = 0
    for a in range(n):
        for b in range(a + 1, n):
            if (a, b) == (i, j):
                return k
            k += 1
    raise ValueError


def first_moment_exact(n: int, q: Fraction, s: int) -> Fraction:
    m = s - 1
    val = Fraction(1)
    for i in range(2 * m):
        val *= n - i
    return val * q ** (s * (s - 1) // 2)


# ---------------------------------------------------------------------------
# The report's tables
# ---------------------------------------------------------------------------

def table_thresholds(path: Path, ps=(0.5, 0.3)) -> None:
    """`s_0` (staircase first moment), the block threshold, `(2 + sqrt 2) L` and
    `4 L`, with the argmin block, for `n` up to `10^7`."""
    with path.open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["p", "n", "L", "s0_staircase", "s0_over_L", "s_block", "s_block_over_L",
                    "argmin_a", "argmin_b", "argmin_a_over_L", "astar_L", "four_L"])
        for p in ps:
            q = 1 - p
            L_of = lambda n_: math.log(n_) / math.log(1 / q)
            for n in (30, 40, 50, 60, 100, 200, 400, 1000, 10**4, 10**5, 10**6, 10**7):
                L = L_of(n)
                s0 = staircase_threshold(n, q)
                sb = block_threshold(n, q, 1.0, symmetric=False)
                _, a, b = block_floor_log(n, q, sb + 1, symmetric=False)
                w.writerow([p, n, f"{L:.3f}", s0, f"{s0 / L:.3f}", sb, f"{sb / L:.3f}",
                            a, b, f"{a / L:.3f}", f"{A_STAR * L:.2f}", f"{4 * L:.2f}"])


def table_data(path: Path) -> None:
    """The measured dense cells of reports/random_graph_middle.md section 4 against the
    empty-pair floor and the block floor at level 0.05, `p = 1/2`."""
    measured = {30: (16, 19, 20), 40: (26, 28, 29), 50: (36, 37, 38), 60: (45, 46, 47)}
    with path.open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["n", "L", "pw_min", "pw_median", "pw_max", "n_minus_pw_median",
                    "empty_pair_k005_plus1", "block_floor_005", "block_floor_005_a", "block_floor_005_b",
                    "s_block_E1", "s0_staircase", "astar_L", "four_L", "two_L"])
        q = 0.5
        for n, (lo, med, hi) in measured.items():
            L = math.log2(n)
            k05 = empty_pair_floor(n, q, 0.05)
            sb05 = block_threshold(n, q, 0.05) + 1   # least s with bound <= 0.05
            _, a, b = block_floor_log(n, q, sb05)
            w.writerow([n, f"{L:.3f}", lo, med, hi, n - med, k05 + 1, n - sb05 + 1, a, b,
                        block_threshold(n, q, 1.0), staircase_threshold(n, q),
                        f"{A_STAR * L:.2f}", f"{4 * L:.2f}", f"{2 * L:.2f}"])


def table_ratio(path: Path, ps=(0.5, 0.3), avals=(2.0, 2.5, 3.0, 3.3, 3.414, 3.5, 3.7, 3.9)) -> None:
    """The brackets on the second-moment ratio at `s = round(a L)`."""
    with path.open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["p", "a", "n", "L", "s", "log_ratio_lower", "log_ratio_upper",
                    "log_first_moment", "limit_exponent_times_L2lnb"])
        for p in ps:
            q = 1 - p
            lnb = -math.log(q)
            for a in avals:
                for n in (100, 300, 1000, 3000, 10**4, 10**5, 10**6, 10**7):
                    L = math.log(n) / lnb
                    s = max(2, round(a * L))
                    if 2 * (s - 1) > n:
                        continue
                    lo = ratio_log_lower(n, q, s)
                    up = ratio_log_upper(n, q, s)
                    w.writerow([p, a, n, f"{L:.3f}", s, f"{lo:.4f}", f"{up:.4f}",
                                f"{log_first_moment(n, q, s):.2f}",
                                f"{worst_overlap(a)[0] * L * L * lnb:.3f}"])


def main(argv=None) -> None:
    SCRATCH.mkdir(parents=True, exist_ok=True)
    table_thresholds(SCRATCH / "thresholds.csv")
    table_data(SCRATCH / "data_vs_floors.csv")
    table_ratio(SCRATCH / "ratio_brackets.csv")
    for name in ("thresholds.csv", "data_vs_floors.csv", "ratio_brackets.csv"):
        print(f"== {name}")
        print((SCRATCH / name).read_text())


if __name__ == "__main__":
    main(sys.argv[1:])


# ---------------------------------------------------------------------------
# Bandwidth: the strict staircase is the structure of `bw <= n - s`
# ---------------------------------------------------------------------------

def bandwidth_exact(adj: list[int], n: int) -> int:
    """`min_sigma max_{uv edge} |sigma(u) - sigma(v)|` by enumeration (`n <= 8`)."""
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if adj[i] >> j & 1]
    if not edges:
        return 0
    best = n
    for perm in itertools.permutations(range(n)):
        pos = [0] * n
        for k, x in enumerate(perm):
            pos[x] = k
        width = max(abs(pos[i] - pos[j]) for i, j in edges)
        if width < best:
            best = width
    return best


def check_bandwidth_lemma(n: int, graphs=None) -> dict:
    """For `2(s - 1) <= n`: `bw <= n - s` iff a strict staircase of size `s` exists. The
    first `s - 1` and the last `s - 1` positions of a layout of bandwidth `<= n - s` are a
    staircase (positions `i` from the front and `j` from the back are more than `n - s`
    apart iff `i + j <= s`), and conversely, since two front positions are at most
    `s - 2 <= n - s` apart and a front and a middle position at most `n - s`.  (Without
    the size condition the empty graph on 3 vertices has `bw = 0` and no staircase of
    size 3.)  Kuang & McDiarmid (1985) count this structure."""
    out = {"graphs": 0, "violations": 0, "pairs": 0}
    if graphs is None:
        graphs = (graph_from_edges(n, e) for e in range(1 << (n * (n - 1) // 2)))
    for adj in graphs:
        bw = bandwidth_exact(adj, n)
        out["graphs"] += 1
        for s in range(1, n // 2 + 2):
            out["pairs"] += 1
            if has_staircase(adj, n, s, generalised=False) != (bw <= n - s):
                out["violations"] += 1
    return out
