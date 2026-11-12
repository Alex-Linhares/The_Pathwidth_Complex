"""The witnesses of reports/ss7_register_sufficiency.md section 2: the dual pair (same
comparability graph and costs, different values); the antichain A_k and the matched pairs D_k
that defeat every pairwise-local derived graph; the series-parallel (N-free) MOSP instances.

Regenerate: cd /home/al/dev/MOSP && python reports/scratch/ss7_register_sufficiency/ss7_witnesses.py
"""
import itertools, sys
sys.path.insert(0, "/home/al/dev/MOSP")
from paper1.ss7_register import (ss7_value, ss7_values_by_extension, embed_mosp, is_series_parallel,
                                 transitive_closure, mosp_graph)
import networkx as nx

# dual pair on two tasks
print("a < b, cost(a)=+1, cost(b)=-1:", ss7_value(2, [0, 1], [1, -1]), " (values over extensions", ss7_values_by_extension(2, [0, 1], [1, -1]), ")")
print("b < a, cost(a)=+1, cost(b)=-1:", ss7_value(2, [2, 0], [1, -1]), " (values over extensions", ss7_values_by_extension(2, [2, 0], [1, -1]), ")")
# antichain of k tasks at +1, and k matched pairs a_i < b_i at (+1, -1)
for k in (1, 2, 3, 4):
    A = ss7_value(k, [0] * k, [1] * k)
    D = ss7_value(2 * k, [0] * k + [1 << i for i in range(k)], [1] * k + [-1] * k)
    print(f"k={k}: antichain A_k of +1 tasks: {A}; matched pairs D_k: {D}")
# chains: all +1 (value k); alternating (value 1)
print("chain of 5 tasks at +1:", ss7_value(5, [0, 1, 2, 4, 8], [1] * 5),
      "; alternating chain +1,-1,...:", ss7_value(6, [0, 1, 2, 4, 8, 16], [1, -1, 1, -1, 1, -1]))
# series-parallel MOSP-shaped instances: N-free iff customers sharing a pattern have equal pattern sets
cnt = bad = sp = 0
for n in range(1, 4):
    for m in range(1, 4):
        for bits in itertools.product([0, 1], repeat=n * m):
            M = [list(bits[i * m:(i + 1) * m]) for i in range(n)]
            if not any(any(r) for r in M):
                continue
            N, pred, cost = embed_mosp(M)
            lt = transitive_closure(N, pred)
            nfree = is_series_parallel(N, lt)
            rows = [tuple(r) for r in M]
            cliques = all(rows[c] == rows[d] for c in range(n) for d in range(n)
                          if c != d and any(M[c][p] and M[d][p] for p in range(m)))
            cnt += 1; sp += nfree
            if nfree != cliques:
                bad += 1; print("SP MISMATCH", M, nfree, cliques)
print(f"embedded order N-free  <=>  customers sharing a pattern have equal pattern sets: {cnt} matrices (<=3x3), "
      f"{sp} series-parallel, mismatches = {bad}")
