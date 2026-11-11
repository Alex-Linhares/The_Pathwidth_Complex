"""GT35 INTERVAL GRAPH COMPLETION (edge count) against profile and pathwidth.

Claim checked: min |E' - E| over interval supergraphs G' = profile(G) - |E|, where
profile(G) = min over orderings f of sum_v (max_{u in N[v]} f(u) - f(v)).
(Billionnet 1986 / Lin & Yuan 1994; the one-line proof is in the report.)
Checked two ways: (a) by the ordering formula on every graph of the networkx atlas
with <= 6 vertices; (b) on every graph with <= 5 vertices by enumerating every
supergraph and testing intervality with Olariu's ordering characterisation
(G interval iff some order has u < v < w, uw in E  =>  uv in E).
Then the gap against pathwidth on cycles and complete graphs.

Regenerate:  cd /home/al/dev/MOSP && python reports/scratch/garey_johnson/interval_profile.py
"""
from __future__ import annotations
import itertools, sys
sys.path.insert(0, "/home/al/dev/MOSP")
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from fixed_parameter_algorithm.pathwidth import compute_pathwidth


def profile(G):
    nodes = list(G.nodes()); best = None
    for order in itertools.permutations(nodes):
        pos = {v: i for i, v in enumerate(order)}
        s = sum(max(pos[u] for u in list(G[v]) + [v]) - pos[v] for v in nodes)
        if best is None or s < best:
            best = s
    return best


def is_interval(G):
    nodes = list(G.nodes())
    for order in itertools.permutations(nodes):
        ok = True
        for i in range(len(order)):
            for k in range(i + 2, len(order)):
                if G.has_edge(order[i], order[k]):
                    for j in range(i + 1, k):
                        if not G.has_edge(order[i], order[j]):
                            ok = False; break
                if not ok: break
            if not ok: break
        if ok:
            return True
    return False


def min_interval_completion_enum(G):
    nodes = list(G.nodes())
    missing = [p for p in itertools.combinations(nodes, 2) if not G.has_edge(*p)]
    for k in range(len(missing) + 1):
        for add in itertools.combinations(missing, k):
            H = G.copy(); H.add_edges_from(add)
            if is_interval(H):
                return k
    raise AssertionError


if __name__ == "__main__":
    atlas = [g for g in graph_atlas_g() if 1 <= g.number_of_nodes() <= 6]
    bad = 0
    for g in atlas:
        if g.number_of_nodes() <= 5:
            a = min_interval_completion_enum(g); b = profile(g) - g.number_of_edges()
            if a != b:
                bad += 1; print("MISMATCH", g.edges(), a, b)
    print(f"(b) enumeration vs profile formula on all {sum(1 for g in atlas if g.number_of_nodes()<=5)} graphs <= 5 vertices: mismatches = {bad}")
    print(f"(a) profile formula evaluated on all {len(atlas)} atlas graphs <= 6 vertices (completion = profile - |E|):")
    rows = []
    maxgap = (0, None)
    for g in atlas:
        if g.number_of_nodes() < 2: continue
        comp = profile(g) - g.number_of_edges(); pw = compute_pathwidth(g)[0]
        rows.append((comp, pw))
        if comp - pw > maxgap[0]:
            maxgap = (comp - pw, (list(g.edges()), comp, pw))
    print("   max (completion - pw) on <= 6 vertices:", maxgap)
    print("   graphs with completion = 0 and pw >= 3:", [ (c,p) for c,p in rows if c == 0 and p >= 3][:5])
    for n in range(4, 9):
        C = nx.cycle_graph(n); K = nx.complete_graph(n)
        print(f"   C_{n}: completion {profile(C) - C.number_of_edges() if n <= 7 else 'n-3 (fan)'}, pw {compute_pathwidth(C)[0]};   "
              f"K_{n}: completion {0}, pw {compute_pathwidth(K)[0]}")
