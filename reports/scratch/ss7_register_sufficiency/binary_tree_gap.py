"""The complete binary out-tree T_h: pb = h + 1 while pbw = pw(T_h) + 1 = ceil(h/2) + 1, so
pb - pbw = floor(h/2); the out-tree recursion g(T) = max(g1, g2 + 1) checked on random
out-trees; the ternary out-tree has no gap.

Regenerate: cd /home/al/dev/MOSP && python reports/scratch/ss7_register_sufficiency/binary_tree_gap.py
"""
import random, re, sys, time
sys.path.insert(0, "/home/al/dev/MOSP")
from paper1.ss7_register import (pb_ideal, pb_game, succ_of_arcs, pred_of_succ, binary_out_tree,
                                 tree_g, random_out_tree, lengauer_u, underlying)
from fixed_parameter_algorithm.pathwidth import compute_pathwidth
import subprocess, networkx as nx


def pw_c(G):
    """Exact pathwidth by the C program (pathwidth_solver/cli/pathwidth, graph6 on stdin);
    compute_pathwidth_fpt returned 1 on T_4 and T_5 (a bug, recorded in the report)."""
    g6 = nx.to_graph6_bytes(G, header=False).decode().strip() + "\n"
    out = subprocess.run(["/home/al/dev/MOSP/pathwidth_solver/cli/pathwidth", "-t", "600"],
                         input=g6, capture_output=True, text=True).stdout
    m = re.search(r"pathwidth (\d+) (\w+)", out)
    assert m and m.group(2) == "refutation", out
    return int(m.group(1))

t0 = time.time()
print("h  n   pb(T_h out)  pw(T_h)  pbw  gap   (pb: ideal DP to h = 4, recursion g(T) above; pw exact: subset DP to 15 vertices, the C program with a refutation above)")
for h in range(0, 7):
    n, arcs = binary_out_tree(h)
    succ = succ_of_arcs(n, arcs)
    if h <= 4:
        pb = pb_ideal(n, succ, 0)          # exact: a DP over the 458,329 rooted subtrees at h = 4
    else:
        ch = [[] for _ in range(n)]
        for u, v in arcs: ch[u].append(v)
        pb = tree_g(ch) + 1                # the out-tree recursion (checked below to 14 vertices)
    G = lengauer_u(n, arcs)
    assert G.number_of_edges() == len(arcs)   # in-degrees <= 1: G_u = U
    pw = compute_pathwidth(G)[0] if n <= 18 else pw_c(G)
    print(f"{h}  {n:2d}  {pb:4d}         {pw:3d}     {pw+1:3d}  {pb-pw-1:3d}   [{time.time()-t0:.0f}s]")
# retention: the leaves of an out-tree are the outputs; retained they add up to 2^h
n, arcs = binary_out_tree(3); succ = succ_of_arcs(n, arcs)
R = sum(1 << v for v in range(n) if succ[v] == 0)
print(f"T_3 with its 8 leaves retained (G&J outputs): pb = {pb_ideal(n, succ, R)} vs {pb_ideal(n, succ, 0)} unretained")
# in-tree orientation (leaves -> root): G_u has cliques; no gap
rev = [(v, u) for u, v in arcs]; succ_r = succ_of_arcs(n, rev)
print(f"T_3 as an in-tree (arcs child -> parent): pb = {pb_ideal(n, succ_r, 0)}, "
      f"pw(G_u) + 1 = {compute_pathwidth(lengauer_u(n, rev))[0] + 1}")
# ternary out-tree of height h: pb = h + 1 = pw + 1 (TreeBound.lean: pw = h)
for h in (1, 2):
    nodes = [[]]; 
    def grow(v, d):
        for _ in range(3):
            nodes.append([]); c = len(nodes) - 1; nodes[v].append(c)
            if d > 1: grow(c, d - 1)
    grow(0, h)
    n3 = len(nodes); arcs3 = [(v, c) for v in range(n3) for c in nodes[v]]
    pw3 = compute_pathwidth(underlying(n3, arcs3))[0]
    print(f"ternary out-tree height {h} ({n3} vertices): pb = {pb_ideal(n3, succ_of_arcs(n3, arcs3), 0)}, pw + 1 = {pw3 + 1}")
# the recursion g(T) = max(g1, g2+1) on random out-trees, against the ideal DP
rng = random.Random(3); bad = 0; cnt = 0
for n in range(1, 15):
    for _ in range(300):
        ch = random_out_tree(n, rng)
        arcs = [(v, c) for v in range(n) for c in ch[v]]
        succ = succ_of_arcs(n, arcs)
        cnt += 1
        if pb_ideal(n, succ, 0) != tree_g(ch) + 1:
            bad += 1; print("RECURSION MISMATCH", ch)
print(f"out-tree recursion pb = g(T) + 1, g = max(g1, g2 + 1): {cnt} random out-trees on 1..14 vertices, mismatches = {bad}  [{time.time()-t0:.0f}s]")
