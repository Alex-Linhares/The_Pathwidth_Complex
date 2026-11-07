#!/usr/bin/env python3
"""Brute-force check, before stating it in Lean, of the weak half of Bienstock, Robertson,
Seymour & Thomas (1991) Theorem (2.1): a blockage of order n implies pathwidth >= n.

Definitions (Section 2 of the paper), on subsets X of V (bit masks):
  att(X)  = the vertices of X with a neighbour outside X;  alpha(X) = |att(X)|
  X^c     = (V - X) u att(X)
  (X1, X2) complementary  iff  X1 u X2 = V and att(X1) subset of X2
  B is a blockage of order n iff
    (i)   every X in B has alpha(X) <= n
    (ii)  X in B, Y subset of X, alpha(Y) <= n  ->  Y in B
    (iii) (X1, X2) complementary with |X1 n X2| <= n  ->  exactly one of X1, X2 is in B

Two checks.

(1) Exhaustive, on every graph of the atlas with at most 4 vertices and every n in 0..5:
    enumerate every family B of subsets of V and test the three axioms; record whether a
    blockage of order n exists; compare with pw >= n (pathwidth by vertex separation over
    all orderings). Both halves of (2.1) at these sizes -- a check that the axioms were
    transcribed correctly (the "exactly one", the direction of att, X^c).

(2) The proof's facts, on every graph of the atlas to 7 vertices and EVERY layout: with
    S_i the first i vertices (the prefix unions X_i of the bags W_i = att(S_{i-1}) u {v_i}
    of the layout's path decomposition, |W_i| <= vs + 1) and n = vs(sigma) + 1, every i
    satisfies
      (a) att(S_i) subset of W_i  and  att(S_i) subset of W_{i+1}; S_{i+1} - S_i subset of W_{i+1}
          -- so alpha(S_i) <= n and |(S_{i+1} - S_i) u att(S_i)| <= n, the two premises of
          Lemma (2.2) with X = S_i, Y = S_{i+1};
      (b) (S_i, S_i^c) is complementary with S_i n S_i^c = att(S_i);
      (c) (S_{i+1}, S_i^c) = (X u Y, X^c) is complementary with
          (X u Y) n X^c = (Y - X) u att(X), of size <= n;
    which are the sets the Lean proof hands to axiom (iii): with X_0 = {} in B and X_m = V
    not in B, the first i with S_{i+1} not in B makes (S_{i+1}, S_i^c) a complementary pair
    of small intersection with neither side in B (S_i^c is out because S_i is in).
    Also (d) the set identities used inside Lemma (2.2) on ALL pairs X, Y of subsets:
    (X u Y, X^c) complementary and (X u Y) n X^c = (Y - X) u att(X), (X, X^c) complementary,
    X n X^c = att(X), att(X) subset of X.

    python3 -I check_blockage.py
"""
import itertools, sys, time
import networkx as nx


def popcount(x):
    return bin(x).count("1")


def att(adj, X):
    r = 0
    for v in range(len(adj)):
        if (X >> v) & 1 and (adj[v] & ~X):
            r |= 1 << v
    return r


def vs_layout(adj, order):
    best = 0
    S = 0
    for v in order:
        S |= 1 << v
        best = max(best, popcount(att(adj, S)))
    return best


def pathwidth(adj):
    n = len(adj)
    if n == 0:
        return 0
    return min(vs_layout(adj, p) for p in itertools.permutations(range(n)))


def blockage_exists(adj, n):
    N = len(adj); full = (1 << N) - 1
    subsets = range(1 << N)
    alpha = [popcount(att(adj, X)) for X in subsets]
    # candidates for B: subsets with alpha <= n (axiom i)
    ok = [X for X in subsets if alpha[X] <= n]
    # axiom (ii): for each X the set of Y subset X with alpha(Y) <= n, as a family mask
    req = {}
    for X in ok:
        m = 0
        Y = X
        while True:
            if alpha[Y] <= n:
                m |= 1 << Y
            if Y == 0:
                break
            Y = (Y - 1) & X
        req[X] = m
    # axiom (iii): complementary pairs with small intersection
    pairs = []
    for X1 in subsets:
        a1 = att(adj, X1)
        for X2 in subsets:
            if (X1 | X2) == full and (a1 & ~X2) == 0 and popcount(X1 & X2) <= n:
                pairs.append((X1, X2))
    okmask = 0
    for X in ok:
        okmask |= 1 << X
    for B in range(1 << (1 << N)):
        if B & ~okmask:
            continue
        good = True
        for X in ok:
            if (B >> X) & 1 and (req[X] & ~B):
                good = False; break
        if not good:
            continue
        for (X1, X2) in pairs:
            if ((B >> X1) & 1) ^ ((B >> X2) & 1) != 1:
                good = False; break
        if good:
            return True
    return False


def main():
    t0 = time.time()
    graphs = [g for g in nx.graph_atlas_g() if 1 <= g.number_of_nodes() <= 7]
    # (1) exhaustive families to 4 vertices
    c1 = dict(graphs=0, cases=0, weak_viol=0, strong_viol=0, blockages=0)
    for g in graphs:
        N = g.number_of_nodes()
        if N > 4:
            continue
        adj = [sum(1 << u for u in g.neighbors(v)) for v in range(N)]
        pw = pathwidth(adj)
        c1["graphs"] += 1
        for n in range(0, 6):
            ex = blockage_exists(adj, n)
            c1["cases"] += 1
            c1["blockages"] += ex
            if ex and not (pw >= n):
                c1["weak_viol"] += 1
            if (pw >= n) and not ex:
                c1["strong_viol"] += 1
    print("(1) exhaustive families, graphs to 4 vertices: %s  (%.1f s)" % (c1, time.time() - t0))
    # (2) the proof's facts on every layout to 7 vertices
    c2 = dict(graphs=0, layouts=0, steps=0, a_viol=0, b_viol=0, c_viol=0, d_pairs=0, d_viol=0)
    for g in graphs:
        N = g.number_of_nodes()
        adj = [sum(1 << u for u in g.neighbors(v)) for v in range(N)]
        full = (1 << N) - 1
        c2["graphs"] += 1
        # (d) on all pairs
        A = [att(adj, X) for X in range(1 << N)]
        for X in range(1 << N):
            Xc = (full & ~X) | A[X]
            if (A[X] & ~X) or (X | Xc) != full or (A[X] & ~Xc) or (X & Xc) != A[X]:
                c2["d_viol"] += 1
            for Y in range(1 << N):
                c2["d_pairs"] += 1
                U = X | Y
                if (U | Xc) != full or (A[U] & ~Xc) or (U & Xc) != ((Y & ~X) | A[X]):
                    c2["d_viol"] += 1
        for order in itertools.permutations(range(N)):
            c2["layouts"] += 1
            k = vs_layout(adj, order)
            n = k + 1
            S = [0]
            for v in order:
                S.append(S[-1] | (1 << v))
            W = [None] + [A[S[i - 1]] | (1 << order[i - 1]) for i in range(1, N + 1)]
            for i in range(0, N):
                c2["steps"] += 1
                Si, Sn = S[i], S[i + 1]
                # (a)
                if i >= 1 and (A[Si] & ~W[i]):
                    c2["a_viol"] += 1
                if (A[Si] & ~W[i + 1]) or ((Sn & ~Si) & ~W[i + 1]):
                    c2["a_viol"] += 1
                if popcount(A[Si]) > n or popcount((Sn & ~Si) | A[Si]) > n or popcount(A[Sn]) > n:
                    c2["a_viol"] += 1
                # (b)
                Sic = (full & ~Si) | A[Si]
                if (Si | Sic) != full or (A[Si] & ~Sic) or (Si & Sic) != A[Si] or popcount(Si & Sic) > n:
                    c2["b_viol"] += 1
                # (c)
                if (Sn | Sic) != full or (A[Sn] & ~Sic) or (Sn & Sic) != ((Sn & ~Si) | A[Si]) or popcount(Sn & Sic) > n:
                    c2["c_viol"] += 1
    print("(2) the proof's facts on every layout to 7 vertices: %s  (%.1f s)" % (c2, time.time() - t0))
    bad = c1["weak_viol"] + c1["strong_viol"] + c2["a_viol"] + c2["b_viol"] + c2["c_viol"] + c2["d_viol"]
    print("VIOLATIONS: %d" % bad)
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
