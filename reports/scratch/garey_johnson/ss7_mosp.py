"""SS7 SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST contains MOSP and PO1.

SS7 (G&J p. 238): tasks T, partial order, cost c(t) in Z; is there a linear extension
whose every prefix sum is <= K?  Its optimum on a poset is computed here exactly by a
DP over order ideals.

Encoding of a MOSP instance (rows = customers, columns = products): tasks open(c)
(+1), close(c) (-1), product p (0); open(c) < p < close(c) for every p in P_c.
Claim checked: the SS7 optimum of the encoded poset equals the MOSP optimum, computed
independently by brute force over all product orderings (m <= 6) and as
pw(MOSP graph) + 1 by the exact subset DP (MOSPGraph.lean), on 300 random instances.

Encoding of a register-sufficiency instance (Abdel-Wahab 1976, as G&J cite it for
SS7): tasks compute(v) (+1), free(v) (-1); compute(u) < compute(v) for each arc
u -> v (u an operand of v); compute(v) < free(u) for each arc u -> v; compute(v) <
free(v).  Claim checked: SS7 optimum = black progressive pebble demand pb(D) on
every labelled dag with <= 5 vertices.

Regenerate:  cd /home/al/dev/MOSP && python reports/scratch/garey_johnson/ss7_mosp.py
"""
from __future__ import annotations
import itertools, random, sys
sys.path.insert(0, "/home/al/dev/MOSP")
sys.path.insert(0, "/home/al/dev/MOSP/reports/scratch/garey_johnson")
import networkx as nx
from fixed_parameter_algorithm.pathwidth import compute_pathwidth
from register_sufficiency import demand


def ss7_opt(n, pred, cost):
    """min over linear extensions of max prefix sum; pred[i] = bitmask of predecessors."""
    full = (1 << n) - 1
    best = {0: cost_of(0, cost, n)}
    # process ideals by size
    layers = [[0]]
    for size in range(n):
        nxt = {}
        for I in layers[-1]:
            fI = best[I]
            for v in range(n):
                b = 1 << v
                if not (I & b) and (pred[v] & I) == pred[v]:
                    J = I | b
                    val = max(fI, cost_of(J, cost, n))
                    if J not in best or val < best[J]:
                        best[J] = val
                    nxt[J] = True
        layers.append(list(nxt))
    return best[full]


def cost_of(I, cost, n):
    return sum(cost[v] for v in range(n) if I >> v & 1)


def mosp_bruteforce(M):
    n, m = len(M), len(M[0]); best = None
    for order in itertools.permutations(range(m)):
        first = {}; last = {}
        for t, p in enumerate(order):
            for c in range(n):
                if M[c][p]:
                    first.setdefault(c, t); last[c] = t
        width = max(sum(1 for c in first if first[c] <= t <= last[c]) for t in range(m))
        if best is None or width < best: best = width
    return best


def mosp_graph(M):
    n, m = len(M), len(M[0]); G = nx.Graph(); G.add_nodes_from(range(n))
    for p in range(m):
        cs = [c for c in range(n) if M[c][p]]
        G.add_edges_from(itertools.combinations(cs, 2))
    return G


def encode_mosp(M):
    n, m = len(M), len(M[0])
    # tasks: open c = c, close c = n + c, product p = 2n + p
    N = 2 * n + m; pred = [0] * N; cost = [0] * N
    for c in range(n):
        cost[c] = 1; cost[n + c] = -1
        for p in range(m):
            if M[c][p]:
                pred[2 * n + p] |= 1 << c
                pred[n + c] |= 1 << (2 * n + p)
    return N, pred, cost


def encode_rs(nv, arcs):
    # compute v = v, free v = nv + v
    N = 2 * nv; pred = [0] * N; cost = [1] * nv + [-1] * nv
    for v in range(nv):
        pred[nv + v] |= 1 << v
    for u, v in arcs:
        pred[v] |= 1 << u
        pred[nv + u] |= 1 << v
    return N, pred, cost


if __name__ == "__main__":
    rng = random.Random(1)
    bad = 0; count = 0
    while count < 300:
        n = rng.randint(1, 5); m = rng.randint(1, 6)
        M = [[1 if rng.random() < rng.choice([0.3, 0.5, 0.7]) else 0 for _ in range(m)] for _ in range(n)]
        if any(sum(r) == 0 for r in M):   # every customer needs a product
            continue
        count += 1
        a = ss7_opt(*encode_mosp(M)); b = mosp_bruteforce(M); c = compute_pathwidth(mosp_graph(M))[0] + 1
        if not (a == b == c):
            bad += 1; print("MISMATCH", M, a, b, c)
    print(f"MOSP: SS7(encoded poset) = brute-force MOSP = pw(MOSP graph)+1 on {count} random instances (n<=5, m<=6): mismatches = {bad}")
    bad = 0; count = 0
    for nv in range(1, 6):
        pairs = list(itertools.combinations(range(nv), 2))
        for mask in range(1 << len(pairs)):
            arcs = [p for i, p in enumerate(pairs) if mask >> i & 1]
            pred = [0] * nv
            for u, v in arcs: pred[v] |= 1 << u
            a = ss7_opt(*encode_rs(nv, arcs)); b = demand(nv, pred, 0)
            count += 1
            if a != b:
                bad += 1
                if bad <= 5: print("MISMATCH", nv, arcs, a, b)
    print(f"PO1: SS7(Abdel-Wahab encoding) = black progressive pebble demand on all {count} labelled dags with <= 5 vertices: mismatches = {bad}")
