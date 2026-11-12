"""SS7(embedded MOSP) = MOSP optimum = pw(MOSP graph) + 1 on every 0/1 matrix with at most
3 customers and 3 patterns (rows may be empty), and the two edge cases.

Regenerate: cd /home/al/dev/MOSP && python reports/scratch/ss7_register_sufficiency/ss7_embed_exhaustive.py
"""
import itertools, sys
sys.path.insert(0, "/home/al/dev/MOSP")
from paper1.ss7_register import ss7_value, embed_mosp, mosp_bruteforce, mosp_graph
from fixed_parameter_algorithm.pathwidth import compute_pathwidth

count = bad = 0; edge = []
no_pair_fail = 0
for n in range(0, 4):
    for m in range(0, 4):
        for bits in itertools.product([0, 1], repeat=n * m):
            M = [list(bits[i * m:(i + 1) * m]) for i in range(n)]
            N, pred, cost = embed_mosp(M)
            a = ss7_value(N, pred, cost)
            b = mosp_bruteforce(M)
            hreq = any(any(r) for r in M)
            if hreq:
                c = compute_pathwidth(mosp_graph(M))[0] + 1
                count += 1
                if not (a == b == c):
                    bad += 1; print("MISMATCH", M, a, b, c)
                # without open(c) < close(c): customers with no pattern break the equality
                pred2 = list(pred)
                for cc in range(n):
                    pred2[n + cc] &= ~(1 << cc)
                if ss7_value(N, pred2, cost) != b:
                    no_pair_fail += 1
            else:
                edge.append((n, m, a, b))
print(f"SS7(embed M) = MOSP(M) = pw(G_M)+1 on all {count} matrices with <=3 customers, <=3 patterns "
      f"and some requirement: mismatches = {bad}")
print(f"without the pair open(c) < close(c) the equality fails on {no_pair_fail} of them "
      f"(every one with a customer requiring nothing)")
print("edge cases (no requirement): (n, m, SS7, MOSP) =", sorted(set(edge)))
