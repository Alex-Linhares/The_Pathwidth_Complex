"""GT47 ELIMINATION DEGREE SEQUENCE, its min-max relaxation, degeneracy and pathwidth.

For an ordering f the forward degree of v is d_f(v) = |{u : f(u) > f(v), uv in E}|.
Claim checked: min_f max_v d_f(v) = degeneracy(G) on every atlas graph <= 7 vertices
(the reverse of a smallest-last ordering attains it).  Then the smallest graphs
with pw > degeneracy and the maximum gap at <= 7 vertices; degeneracy <= pw is
`degeneracy_le_pathwidth` (Sandwich.lean) and the gap is unbounded on trees.

Regenerate:  cd /home/al/dev/MOSP && python reports/scratch/garey_johnson/gt47_degeneracy.py
"""
from __future__ import annotations
import itertools, sys
sys.path.insert(0, "/home/al/dev/MOSP")
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from fixed_parameter_algorithm.pathwidth import compute_pathwidth


def minmax_forward_degree(G):
    nodes = list(G.nodes()); best = None
    for order in itertools.permutations(nodes):
        pos = {v: i for i, v in enumerate(order)}
        m = max(sum(1 for u in G[v] if pos[u] > pos[v]) for v in nodes)
        if best is None or m < best:
            best = m
            if best == 0: break
    return best


def degeneracy(G):
    return max(nx.core_number(G).values()) if G.number_of_edges() else 0


if __name__ == "__main__":
    atlas = [g for g in graph_atlas_g() if 2 <= g.number_of_nodes() <= 7]
    bad = 0; smallest = None; maxgap = (0, None)
    for g in atlas:
        a = minmax_forward_degree(g); d = degeneracy(g)
        if a != d:
            bad += 1; print("MISMATCH", list(g.edges()), a, d)
        pw = compute_pathwidth(g)[0]
        if pw > d and smallest is None:
            smallest = (g.number_of_nodes(), list(g.edges()), d, pw)
        if pw - d > maxgap[0]:
            maxgap = (pw - d, (g.number_of_nodes(), list(g.edges()), d, pw))
    print(f"min-max forward degree vs degeneracy on {len(atlas)} atlas graphs (2..7 vertices): mismatches = {bad}")
    print("smallest graph with pw > degeneracy (n, edges, degeneracy, pw):", smallest)
    print("largest pw - degeneracy at <= 7 vertices:", maxgap)
