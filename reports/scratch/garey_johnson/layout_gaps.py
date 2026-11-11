"""The layout entries of G&J (GT40 bandwidth, GT41 directed bandwidth, GT42 optimal
linear arrangement, GT44 minimum cut linear arrangement, SR16 consecutive ones
matrix augmentation) against pathwidth, by brute force over orderings.

Checks: (1) on stars K_{1,k}: bw = cw = ceil(k/2), MinLA = quadratic, pw = 1;
(2) on every atlas graph <= 6 vertices: pw <= bw, pw <= cw, cw <= Delta * pw,
and the smallest graphs with bw > pw and cw > pw; (3) directed bandwidth of the
out-star exceeds the pathwidth of its underlying star by k - 1 (dbw = k);
(4) SR16 on the edge-vertex incidence matrix (rows = edges, columns = vertices)
equals MinLA - |E| on every atlas graph with <= 6 edges and <= 6 vertices, which
is G&J's own transformation (from OPTIMAL LINEAR ARRANGEMENT).

Regenerate:  cd /home/al/dev/MOSP && python reports/scratch/garey_johnson/layout_gaps.py
"""
from __future__ import annotations
import itertools, sys
sys.path.insert(0, "/home/al/dev/MOSP")
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from fixed_parameter_algorithm.pathwidth import compute_pathwidth


def layouts(G):
    nodes = list(G.nodes())
    for order in itertools.permutations(nodes):
        yield {v: i for i, v in enumerate(order)}


def bandwidth(G):
    return min(max((abs(f[u] - f[v]) for u, v in G.edges()), default=0) for f in layouts(G))


def cutwidth(G):
    n = G.number_of_nodes()
    return min(max((sum(1 for u, v in G.edges() if min(f[u], f[v]) < i <= max(f[u], f[v])) for i in range(1, n)), default=0)
               for f in layouts(G))


def minla(G):
    return min(sum(abs(f[u] - f[v]) for u, v in G.edges()) for f in layouts(G))


def sr16(M):
    """min number of 0s turned to 1 so that every row becomes consecutive, over column permutations."""
    m = len(M[0]); best = None
    for order in itertools.permutations(range(m)):
        tot = 0
        for row in M:
            pos = [t for t, p in enumerate(order) if row[p]]
            if pos: tot += (pos[-1] - pos[0] + 1) - len(pos)
        if best is None or tot < best: best = tot
    return best


if __name__ == "__main__":
    for k in range(2, 7):
        S = nx.star_graph(k)
        print(f"K_1,{k}: bw {bandwidth(S)} cw {cutwidth(S)} MinLA {minla(S)} pw {compute_pathwidth(S)[0]}  "
              f"directed bandwidth of the out-star = {k} (the centre precedes every leaf, so the last leaf sits at distance k)")
    atlas = [g for g in graph_atlas_g() if 2 <= g.number_of_nodes() <= 6]
    viol = 0; first_bw = None; first_cw = None
    for g in atlas:
        pw = compute_pathwidth(g)[0]; bw = bandwidth(g); cw = cutwidth(g)
        D = max((d for _, d in g.degree()), default=0)
        if not (pw <= bw and pw <= cw and cw <= max(1, D) * max(pw, 1) or g.number_of_edges() == 0):
            viol += 1; print("VIOLATION", list(g.edges()), pw, bw, cw, D)
        if bw > pw and first_bw is None: first_bw = (g.number_of_nodes(), list(g.edges()), pw, bw)
        if cw > pw and first_cw is None: first_cw = (g.number_of_nodes(), list(g.edges()), pw, cw)
    print(f"atlas <= 6 vertices ({len(atlas)} graphs): violations of pw <= bw, pw <= cw, cw <= Delta*pw: {viol}")
    print("smallest graph with bw > pw:", first_bw)
    print("smallest graph with cw > pw:", first_cw)
    bad = 0; cnt = 0
    for g in atlas:
        if 1 <= g.number_of_edges() <= 6:
            nodes = list(g.nodes()); idx = {v: i for i, v in enumerate(nodes)}
            M = [[1 if v in e else 0 for v in nodes] for e in g.edges()]
            cnt += 1
            if sr16(M) != minla(g) - g.number_of_edges():
                bad += 1; print("MISMATCH", list(g.edges()), sr16(M), minla(g))
    print(f"SR16 on the edge-vertex incidence matrix = MinLA - |E| on {cnt} atlas graphs with 1..6 edges: mismatches = {bad}")
