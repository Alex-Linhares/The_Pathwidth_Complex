"""Brute-force check of the finite statement behind `RandomOrdering.lean`.

For every labelled graph on n <= NMAX vertices and the identity ordering 0 < 1 < ... < n-1,
the open count at position i (prefix {0..i}, prefix size t = i+1, suffix size m = n-i-1) is
    k_i = #{ v > i : v has an edge into {0..i} }.
Claim (exact, per position): the G(n,p) weight of {k_i > w} equals
    binomTail(m, q, w) = sum_{j > w} C(m,j) q^j (1-q)^(m-j),   q = 1 - (1-p)^t.
Claim (union bound): the weight of {max_i k_i > w} is at most sum_i binomTail(m_i, q_i, w).
Both checked in exact rational arithmetic: the graphs are counted by edge count per event,
and the weight is sum_e count_e p^e (1-p)^(C-e).
"""
import itertools, sys
from fractions import Fraction
from math import comb
import numpy as np

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
PS = [Fraction(1, 2), Fraction(1, 3), Fraction(3, 10), Fraction(9, 10)]

def binom_tail(m, q, w):
    return sum(comb(m, j) * q**j * (1 - q)**(m - j) for j in range(w + 1, m + 1))

def weight_from_counts(counts, p, C):
    return sum(Fraction(int(cnt)) * p**e * (1 - p)**(C - e) for e, cnt in enumerate(counts) if cnt)

total_checks = 0
for n in range(1, NMAX + 1):
    pairs = list(itertools.combinations(range(n), 2))
    C = len(pairs)
    bit = {pr: b for b, pr in enumerate(pairs)}
    graphs = np.arange(1 << C, dtype=np.uint64)
    # edge counts
    ecount = np.zeros(len(graphs), dtype=np.int64)
    for b in range(C):
        ecount += ((graphs >> np.uint64(b)) & np.uint64(1)).astype(np.int64)
    # open counts per position
    ks = []
    for i in range(n):
        k = np.zeros(len(graphs), dtype=np.int64)
        for v in range(i + 1, n):
            mask = 0
            for u in range(i + 1):
                mask |= 1 << bit[(u, v)]
            k += ((graphs & np.uint64(mask)) != 0).astype(np.int64)
        ks.append(k)
    kmax = np.max(np.stack(ks), axis=0) if n > 0 else None
    for w in range(0, n):
        per_pos = []
        for i in range(n):
            counts = np.bincount(ecount[ks[i] > w], minlength=C + 1)
            per_pos.append(counts)
        counts_max = np.bincount(ecount[kmax > w], minlength=C + 1)
        for p in PS:
            tails = []
            for i in range(n):
                t, m = i + 1, n - i - 1
                q = 1 - (1 - p)**t
                lhs = weight_from_counts(per_pos[i], p, C)
                rhs = binom_tail(m, q, w)
                assert lhs == rhs, (n, w, i, p, lhs, rhs)
                tails.append(rhs)
                total_checks += 1
            lhs = weight_from_counts(counts_max, p, C)
            assert lhs <= sum(tails), (n, w, p, lhs, sum(tails))
            total_checks += 1
    print(f"n={n}: {1 << C} graphs, all w in 0..{n-1}, {len(PS)} values of p: exact per position, union bound holds", flush=True)
print(f"total checks: {total_checks}, zero discrepancies")
