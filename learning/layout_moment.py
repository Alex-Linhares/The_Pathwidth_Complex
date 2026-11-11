"""The first and second moment of the number of narrow layouts of G(n, p)
(reports/layout_second_moment.md).

`X_w` is the number of vertex orderings of width at most `w` (vertex
separation: every prefix `S_t` has `|N(S_t) \\ S_t| <= w`).  Two readings:

* `P(pw <= w) <= E[X_w]` (a lower bound on the pathwidth, the first moment);
* `P(pw <= w) >= E[X_w]^2 / E[X_w^2]` (an upper bound, the second moment),
  useful only where the ratio `E[X_w^2] / E[X_w]^2` is bounded.

The first moment is exact, by a chain.  For a fixed ordering `v_1 .. v_n` of
`G(n, p)`, the open count `k_t = |N(S_t) \\ S_t|` is a Markov chain in `(t, k)`:
the vertex placed at step `t` is open with probability `k / (n - t + 1)` (the
suffix vertices are exchangeable given the history, which is a symmetric
function of their edge vectors into the prefix), and each still-closed suffix
vertex then opens with probability `p`, independently, through its fresh edge
to `v_t`.  The number of closed suffix vertices is `n - t - k`, so `(t, k)` is
the whole state.  `q(n, p, w) = P(the identity ordering has width <= w)` is the
DP `chain_log_q` (C, `learning/layout_moment.c`) and `chain_q_exact` (pure
Python, exact rationals); `E[X_w] = n! q(n, p, w)`.

Checked against brute force (`labelled_tables`: every labelled graph on
`n <= 7` vertices with the number of narrow orderings of each width by the
subset DP, no chain, no exchangeability; `tests/test_layout_moment.py`) and
against the isomorphism-class enumeration of `learning/layout_moment_enum.c`
(`nauty-geng` + `nauty-countg --a`, `n <= 10`), which also gives `E[X_w^2]`
exactly: `E[X_w^j] = sum_e p^e (1 - p)^(C - e) T_j[e][w]` with
`T_j[e][w] = sum_{G labelled, e(G) = e} X_w(G)^j`.

The second-moment ratio has a rigorous lower bound at any `n` from the same
chain carrying the edge count: with `Y = e(G)`,
`E[X^2] >= sum_e P(Y = e) E[X | Y = e]^2` (Jensen) and `E[X | Y = e] = n! q_e`
by symmetry, so `E[X^2]/E[X]^2 >= sum_e P(e) q_e^2 / (sum_e P(e) q_e)^2`
(`jensen_log_ratio`, from `chain_edge_profile`).  It is exponential in `n`
whenever the planted edge density (`E[e(G) | identity narrow]`) is below the
typical one, i.e. whenever `w` is below the width of a uniformly random
ordering, `max_t (n - t)(1 - (1 - p)^t)` (`typical_width`).

Usage:
    python -m learning.layout_moment            # the report's tables into reports/scratch/layout_second_moment/
    python -m pytest tests/test_layout_moment.py -q
"""
from __future__ import annotations

import ctypes
import csv
import math
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

_SOURCE = Path(__file__).with_name("layout_moment.c")
_LIBRARY = Path(__file__).with_name("_layout_moment.so")
_library: "ctypes.CDLL | None" = None
SCRATCH = Path(__file__).resolve().parent.parent / "reports" / "scratch" / "layout_second_moment"


def _build() -> None:
    subprocess.run(["gcc", "-O3", "-march=native", "-shared", "-fPIC", "-o", str(_LIBRARY), str(_SOURCE), "-lm"],
                   check=True)


def _load() -> ctypes.CDLL:
    global _library
    if _library is None:
        if not _LIBRARY.exists() or _LIBRARY.stat().st_mtime < _SOURCE.stat().st_mtime:
            _build()
        lib = ctypes.CDLL(str(_LIBRARY))
        lib.chain_log_q.restype = ctypes.c_double
        lib.chain_log_q.argtypes = [ctypes.c_int, ctypes.c_double, ctypes.c_int]
        lib.chain_edge_profile.restype = ctypes.c_int
        lib.chain_edge_profile.argtypes = [ctypes.c_int, ctypes.c_double, ctypes.c_int,
                                           ctypes.POINTER(ctypes.c_double)]
        _library = lib
    return _library


# ----------------------------------------------------------------------------
# the chain
# ----------------------------------------------------------------------------

def chain_log_q(n: int, p: float, w: int) -> float:
    """log P(the identity ordering of G(n, p) has width <= w), by the (t, k) chain in C."""
    if w >= n - 1:
        return 0.0
    return _load().chain_log_q(int(n), float(p), int(w))


def log_expected_layouts(n: int, p: float, w: int) -> float:
    """log E[X_w] = log n! + log q(n, p, w)."""
    return math.lgamma(n + 1) + chain_log_q(n, p, w)


def _binom_pmf_exact(m: int, p: Fraction) -> list[Fraction]:
    q = 1 - p
    return [Fraction(math.comb(m, j)) * p ** j * q ** (m - j) for j in range(m + 1)]


def chain_q_exact(n: int, p: Fraction, w: int):
    """The same chain in exact arithmetic (Fractions if `p` is one), for the tests.

    f[k] = P(k_t = k and every prefix so far has <= w open)."""
    if n <= 0:
        return Fraction(1)
    if w < 0:
        return Fraction(0)
    f = {0: Fraction(1)}
    for t in range(1, n + 1):
        suf = n - t + 1
        g: dict[int, Fraction] = {}
        for k, fk in f.items():
            a = Fraction(k, suf)
            if a < 1:
                m0 = n - t - k
                for j, pj in enumerate(_binom_pmf_exact(m0, p)):
                    if k + j > w:
                        break
                    g[k + j] = g.get(k + j, 0) + (1 - a) * fk * pj
            if a > 0:
                m1 = n - t - k + 1
                for j, pj in enumerate(_binom_pmf_exact(m1, p)):
                    if k - 1 + j > w:
                        break
                    g[k - 1 + j] = g.get(k - 1 + j, 0) + a * fk * pj
        f = g
    return f.get(0, Fraction(0))


def typical_width(n: int, p: float) -> tuple[int, float]:
    """max_t E[k_t] = max_t (n - t)(1 - (1 - p)^t): the mean width profile of a random
    ordering (each suffix vertex is open independently with probability 1 - (1-p)^t).
    Returns (argmax t, value)."""
    best = (0, 0.0)
    for t in range(1, n):
        v = (n - t) * (1 - (1 - p) ** t)
        if v > best[1]:
            best = (t, v)
    return best


def typical_width_limit(c: float) -> tuple[float, float]:
    """lim typical_width / n at p = c/n: max_x (1 - x)(1 - e^{-cx}); returns (x*, value)."""
    xs = np.linspace(0, 1, 200001)
    v = (1 - xs) * (1 - np.exp(-c * xs))
    i = int(np.argmax(v))
    return float(xs[i]), float(v[i])


def beta1(n: int, p: float) -> tuple[int, float]:
    """The least w with E[X_w] >= 1, and w / n.  (E[X_w] is monotone in w.)"""
    lo, hi = -1, n - 1          # E[X_{-1}] = 0 < 1 <= n! = E[X_{n-1}]
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if log_expected_layouts(n, p, mid) >= 0:
            hi = mid
        else:
            lo = mid
    return hi, hi / n


def largest_w_below(n: int, p: float, log_level: float = 0.0) -> int:
    """The largest w with n! q(n, p, w) < e^{log_level}: P(pw <= w) < level is proved.
    -1 if none (i.e. not even w = 0)."""
    w, _ = beta1(n, p) if log_level == 0.0 else (None, None)
    if w is not None:
        return w - 1
    lo, hi = -1, n - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if log_expected_layouts(n, p, mid) >= log_level:
            hi = mid
        else:
            lo = mid
    return lo


# ----------------------------------------------------------------------------
# the edge-marked chain and the Jensen bound on the second-moment ratio
# ----------------------------------------------------------------------------

def chain_edge_profile(n: int, p: float, w: int) -> np.ndarray:
    """log P(identity narrow at w and e(G) = e) for e = 0..C(n, 2); -inf where impossible."""
    C = n * (n - 1) // 2
    out = (ctypes.c_double * (C + 1))()
    rc = _load().chain_edge_profile(int(n), float(p), int(w), out)
    if rc != 0:
        raise MemoryError("chain_edge_profile")
    return np.array(list(out), dtype=float)


def log_binom_pmf(m: int, p: float, e: np.ndarray) -> np.ndarray:
    e = np.asarray(e, dtype=float)
    with np.errstate(divide="ignore"):
        lp = np.log(p) if p > 0 else -np.inf
        lq = np.log1p(-p) if p < 1 else -np.inf
    out = (np.array([math.lgamma(m + 1) - math.lgamma(x + 1) - math.lgamma(m - x + 1) for x in e])
           + np.where(e > 0, e * lp, 0.0) + np.where(m - e > 0, (m - e) * lq, 0.0))
    return out


def _logsumexp(a: np.ndarray) -> float:
    a = np.asarray(a, dtype=float)
    a = a[np.isfinite(a)]
    if a.size == 0:
        return -math.inf
    m = float(a.max())
    return m + math.log(float(np.exp(a - m).sum()))


def jensen_log_ratio(n: int, p: float, w: int) -> dict:
    """log of the rigorous lower bound sum_e P(e) q_e^2 / (sum_e P(e) q_e)^2 on
    E[X_w^2] / E[X_w]^2, with the planted and typical mean edge counts.

    Identity: with L_e = log P(narrow, e) and P_e = P(e(G) = e),
    the bound is sum_e exp(2 L_e - log P_e) / (sum_e exp L_e)^2."""
    C = n * (n - 1) // 2
    L = chain_edge_profile(n, p, w)
    es = np.arange(C + 1)
    logP = log_binom_pmf(C, p, es)
    log_q = _logsumexp(L)                       # log q = log P(narrow)
    finite = np.isfinite(L)
    num = _logsumexp(2 * L[finite] - logP[finite])
    planted_mean = float(np.exp(L[finite] - log_q) @ es[finite])
    return {"log_ratio_bound": num - 2 * log_q, "log_q": log_q,
            "planted_edges": planted_mean, "typical_edges": p * C,
            "log_expected": math.lgamma(n + 1) + log_q}


# ----------------------------------------------------------------------------
# brute force over labelled graphs (no chain, no nauty), n <= 7
# ----------------------------------------------------------------------------

def narrow_counts(adj: list[int], n: int) -> list[int]:
    """X_w(G) for w = 0..n-1 by the subset DP, pure Python (one graph)."""
    full = (1 << n) - 1
    N = [0] * (1 << n)
    for S in range(1, 1 << n):
        low = S & -S
        N[S] = N[S ^ low] | adj[low.bit_length() - 1]
    open_ = [bin(N[S] & ~S & full).count("1") for S in range(1 << n)]
    out = []
    for w in range(n):
        cnt = [0] * (1 << n)
        cnt[0] = 1
        for S in range(1, 1 << n):
            if open_[S] > w:
                continue
            c, T = 0, S
            while T:
                low = T & -T
                c += cnt[S ^ low]
                T ^= low
            cnt[S] = c
        out.append(cnt[full])
    return out


def labelled_tables(n: int, chunk: int = 1 << 16) -> tuple[np.ndarray, np.ndarray]:
    """T1[e][w] = sum over all labelled graphs with e edges of X_w(G), T2 of X_w(G)^2,
    every labelled graph on n vertices (2^C of them), vectorised over graphs."""
    C = n * (n - 1) // 2
    pairs = [(i, j) for j in range(n) for i in range(j)]
    T1 = np.zeros((C + 1, n), dtype=object)
    T2 = np.zeros((C + 1, n), dtype=object)
    popcnt = np.array([bin(x).count("1") for x in range(1 << n)], dtype=np.int8)
    full = (1 << n) - 1
    layers = [[S for S in range(1 << n) if bin(S).count("1") == s] for s in range(n + 1)]
    for start in range(0, 1 << C, chunk):
        ids = np.arange(start, min(start + chunk, 1 << C), dtype=np.int64)
        m = ids.size
        adj = np.zeros((n, m), dtype=np.int64)
        ecount = np.zeros(m, dtype=np.int64)
        for b, (i, j) in enumerate(pairs):
            bit = (ids >> b) & 1
            adj[i] |= bit << j
            adj[j] |= bit << i
            ecount += bit
        nb = np.zeros((1 << n, m), dtype=np.int64)
        for S in range(1, 1 << n):
            low = S & -S
            nb[S] = nb[S ^ low] | adj[low.bit_length() - 1]
        open_ = np.zeros((1 << n, m), dtype=np.int8)
        for S in range(1 << n):
            open_[S] = popcnt[nb[S] & ~S & full]
        X = np.zeros((n, m), dtype=np.int64)
        for w in range(n):
            cnt = {0: np.ones(m, dtype=np.int64)}
            for s in range(1, n + 1):
                new = {}
                for S in layers[s]:
                    c = np.zeros(m, dtype=np.int64)
                    T = S
                    while T:
                        low = T & -T
                        c += cnt[S ^ low]
                        T ^= low
                    c[open_[S] > w] = 0
                    new[S] = c
                cnt = new
            X[w] = cnt[full]
        for e in range(C + 1):
            sel = ecount == e
            if not sel.any():
                continue
            for w in range(n):
                xs = X[w][sel]
                T1[e][w] += int(xs.sum())
                T2[e][w] += int((xs.astype(object) ** 2).sum())
    return T1, T2


# ----------------------------------------------------------------------------
# the enumeration tables (isomorphism classes, n <= 10)
# ----------------------------------------------------------------------------

def enum_tables(n: int) -> tuple[np.ndarray, np.ndarray]:
    """T1, T2 from reports/scratch/layout_second_moment/enum_n{n}.csv (or its parts)."""
    C = n * (n - 1) // 2
    T1 = np.zeros((C + 1, n), dtype=object)
    T2 = np.zeros((C + 1, n), dtype=object)
    files = sorted(SCRATCH.glob(f"enum_n{n}.csv")) or sorted(SCRATCH.glob(f"enum_n{n}_part*.csv"))
    if not files:
        raise FileNotFoundError(f"no enumeration table for n = {n} under {SCRATCH}")
    for path in files:
        with path.open() as fh:
            for row in csv.DictReader(fh):
                e, w = int(row["e"]), int(row["w"])
                T1[e][w] += int(row["T1"])
                T2[e][w] += int(row["T2"])
    return T1, T2


def moments_from_tables(T1, T2, p, w: int):
    """(E[X_w], E[X_w^2]) for G(n, p) from the tables; exact if p is a Fraction."""
    C = T1.shape[0] - 1
    e1 = e2 = 0
    for e in range(C + 1):
        weight = p ** e * (1 - p) ** (C - e)
        e1 += weight * T1[e][w]
        e2 += weight * T2[e][w]
    return e1, e2


def second_moment_ratio(n: int, p, w: int, tables=None) -> float:
    T1, T2 = tables if tables is not None else enum_tables(n)
    e1, e2 = moments_from_tables(T1, T2, p, w)
    return float(e2) / float(e1) ** 2


# ----------------------------------------------------------------------------
# the report's tables
# ----------------------------------------------------------------------------

def _write(path: Path, header: list[str], rows: list[list]) -> None:
    with path.open("w", newline="") as fh:
        wr = csv.writer(fh)
        wr.writerow(header)
        wr.writerows(rows)


def table_beta1(cs=(3, 4, 6, 8, 10, 20), ns=(20, 30, 40, 60, 80, 120, 200, 400, 800, 1600, 3200),
                path: Path | None = None) -> list[list]:
    rows = []
    for c in cs:
        for n in ns:
            if c >= n:
                continue
            p = c / n
            w, b = beta1(n, p)
            t, typ = typical_width(n, p)
            rows.append([c, n, w, round(b, 4), round(typ / n, 4), round(log_expected_layouts(n, p, 0), 2)])
    if path:
        _write(path, ["c", "n", "w_beta1", "beta1", "typical_width_over_n", "log_E_X0"], rows)
    return rows


def table_beta1_dense(ps=(0.5, 0.25, 0.1), ns=(20, 30, 40, 60, 80, 120, 200, 400, 800), path=None) -> list[list]:
    rows = []
    for p in ps:
        b = 1 / (1 - p)
        for n in ns:
            w, beta = beta1(n, p)
            t, typ = typical_width(n, p)
            rows.append([p, n, w, n - w, round((n - w) / math.log(n, b), 3), round(n - typ, 3)])
    if path:
        _write(path, ["p", "n", "w_beta1", "n_minus_w", "(n-w)/log_b_n", "n_minus_typical"], rows)
    return rows


def main(argv: list[str]) -> None:
    SCRATCH.mkdir(parents=True, exist_ok=True)
    what = argv[1] if len(argv) > 1 else "all"
    if what in ("all", "beta1"):
        rows = table_beta1(path=SCRATCH / "beta1_sparse.csv")
        for r in rows:
            print("beta1", *r)
        rows = table_beta1_dense(path=SCRATCH / "beta1_dense.csv")
        for r in rows:
            print("beta1_dense", *r)
    if what in ("all", "jensen"):
        rows = []
        for c in (3, 6, 10):
            for beta in (0.1, 0.2, 0.3, 0.4, 0.5):
                for n in (20, 30, 40, 50, 60, 80):
                    w = round(beta * n)
                    r = jensen_log_ratio(n, c / n, w)
                    rows.append([c, beta, n, w, round(r["log_ratio_bound"], 4), round(r["log_expected"], 3),
                                 round(r["planted_edges"], 3), round(r["typical_edges"], 3)])
                    print("jensen", *rows[-1], flush=True)
        _write(SCRATCH / "jensen_ratio.csv",
               ["c", "beta", "n", "w", "log_ratio_bound", "log_E_X", "planted_edges", "typical_edges"], rows)


if __name__ == "__main__":
    main(sys.argv)
