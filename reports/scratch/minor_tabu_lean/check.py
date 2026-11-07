#!/usr/bin/env python3
"""Brute-force check of every statement of `lean/MOSPFormalization/Search/MinorTabu.lean`
before it is written ("state before you prove, and check before you state").

Graphs: every graph of the networkx atlas on 1..7 vertices (1,253 graphs). For each graph
and a number of random edge subsets F of G -- spanning sub-forests (what the C program's
state always is) and arbitrary subsets, cyclic ones included (the Lean statements do not
need acyclicity, so they are checked without it) -- the union-find walk of
`pathwidth_solver/cli/minor_tabu.c::print_sequence` is replayed in the C's order (edge
index order) and in random orders, and the following are counted:

  (A) ufSeq_isContractionSeq: every emitted pair (a, b) = contract a into b is an edge of the
      current contracted graph under Minor.lean's `contractEdge` semantics (b keeps its
      label and gains a's neighbours; a is left isolated).
  (B) applySeq_ufSeq / removed_ufSeq (the exact identification): the replayed graph equals
      the quotient `quotient G R` (x ~ y iff x != y, both are representatives, and some
      G-edge joins their blocks), and the removed vertices are exactly the
      non-representatives; and the survivors' graph is isomorphic to the C's build_minor H.
  (C) pathwidth_tabuMinor_le / floor_sound_of_refutation: pw(minor) <= pw(G), both by
      vertex separation over ALL orderings (n <= 7: at most 5,040), so "w + 1 <= pw(G)"
      whenever "not pw(minor) <= w".
  (D) floor_sound_of_degeneracy: for random legal contraction/deletion sequences seq2 on the
      minor and for the C's MMD+ (`contraction_degeneracy`, reimplemented from pathwidth.c),
      minDegreeIn (applySeq minor seq2) S <= pw(G) for S = the alive set and random S; also
      degeneracy(minor) <= pw(minor).
  (E) tabu_output_le_pathwidth / tabu_output_ge_iff: on random simulated runs (lists of
      visited forests with claims of either kind, plus a given floor), the output
      max(given, max claim) is <= pw(G), and for w > given: w <= output iff some visited
      minor has pathwidth >= w.
  (F) the role of acyclicity (not a soundness premise): when F is acyclic the walk skips no
      edge, so the minor has n - |F| vertices; counted for the record.

    python3 -I check.py --forests 12 --seed 0
"""
import argparse, itertools, random, sys, time
import networkx as nx


# ---------------- Minor.lean semantics on adjacency sets ----------------

def contract_edge(adj, u, v):
    """contractEdge G u v: merge v into u, u keeps its label, v isolated."""
    n = len(adj)
    new = [set() for _ in range(n)]
    for x in range(n):
        for y in range(n):
            if x == y or x == v or y == v:
                continue
            if (y in adj[x]) or (x == u and y in adj[v]) or (y == u and x in adj[v]):
                new[x].add(y)
    return new


def isolate(adj, v):
    n = len(adj)
    return [set(y for y in adj[x] if x != v and y != v) for x in range(n)]


def apply_seq(adj, seq):
    ok = True
    for (v, u) in seq:
        if u is None:
            adj = isolate(adj, v)
        else:
            if v not in adj[u]:
                ok = False
            adj = contract_edge(adj, u, v)
    return adj, ok


def removed(seq):
    return set(v for (v, _) in seq)


# ---------------- the C program's union-find walk ----------------

def uf_find(rep, x):
    while rep[x] != x:
        rep[x] = rep[rep[x]]
        x = rep[x]
    return x


def uf_walk(n, edges):
    """print_sequence: emits (a, b) with a = rep(eu), b = rep(ev), merging a into b."""
    rep = list(range(n))
    seq = []
    for (p, q) in edges:
        a, b = uf_find(rep, p), uf_find(rep, q)
        if a == b:
            continue
        seq.append((a, b))
        rep[a] = b
    R = [uf_find(rep, x) for x in range(n)]
    return seq, R


def build_minor(adj, R):
    """build_minor: H on the representatives, x ~ y iff x != y and a G-edge joins the blocks."""
    n = len(adj)
    reps = sorted(set(R))
    H = {r: set() for r in reps}
    for x in range(n):
        for y in adj[x]:
            if R[x] != R[y]:
                H[R[x]].add(R[y])
    return H


def quotient(adj, R):
    n = len(adj)
    Q = [set() for _ in range(n)]
    for x in range(n):
        for y in range(n):
            if x != y and R[x] == x and R[y] == y and any(R[p] == x and R[q] == y for p in range(n) for q in adj[p]):
                Q[x].add(y)
    return Q


# ---------------- pathwidth by vertex separation over all orderings ----------------

def vs_of_layout(verts, adjmap, order):
    pos = {v: i for i, v in enumerate(order)}
    best = 0
    for i in range(len(order)):
        prefix = order[:i + 1]
        sep = set()
        for x in prefix:
            for y in adjmap[x]:
                if pos[y] > i:
                    sep.add(x)
                    break
        best = max(best, len(sep))
    return best


def pathwidth_all_orderings(adjmap):
    verts = list(adjmap)
    if not verts:
        return 0
    return min(vs_of_layout(verts, adjmap, p) for p in itertools.permutations(verts))


def degree_in(adjmap, S, v):
    return len([u for u in adjmap[v] if u in S])


def min_degree_in(adjmap, S):
    if not S:
        return 0
    return min(degree_in(adjmap, S, v) for v in S)


def degeneracy(adjmap):
    verts = list(adjmap)
    best = 0
    for r in range(1, len(verts) + 1):
        for S in itertools.combinations(verts, r):
            best = max(best, min_degree_in(adjmap, set(S)))
    return best


def contraction_degeneracy_c(adjmap):
    """pathwidth.c::contraction_degeneracy on a dict graph: MMD+ with the fewest-common
    neighbour tie-break; isolated vertices dropped; returns (best, the sequence of steps and
    the alive sets visited) so the visited minors can be checked as applySeq minors."""
    adj = {v: set(adjmap[v]) for v in adjmap}
    alive = set(v for v in adj if adj[v])
    best = 0
    steps = []   # (seq-step, alive set at the moment of reading the degree)
    visited = []
    seq = []
    while len(alive) > 1:
        v = min(alive, key=lambda x: (len(adj[x] & alive), x))
        d = len(adj[v] & alive)
        visited.append((list(seq), set(alive)))
        best = max(best, d)
        nbrs = adj[v] & alive
        if not nbrs:
            alive.discard(v)
            seq.append((v, None))
            continue
        u = min(nbrs, key=lambda c: (len(adj[c] & nbrs), c))
        adj[u] |= adj[v]
        adj[u].discard(u); adj[u].discard(v)
        for w in list(adj[u]):
            if w in alive:
                adj[w].add(u); adj[w].discard(v)
        alive.discard(v)
        seq.append((v, u))
    return best, visited


def random_forest(n, edges, rng):
    es = list(edges)
    rng.shuffle(es)
    rep = list(range(n))
    F = []
    for (p, q) in es:
        if uf_find(rep, p) != uf_find(rep, q):
            if rng.random() < 0.7:
                F.append((p, q))
                rep[uf_find(rep, p)] = uf_find(rep, q)
    return F


def random_subset(edges, rng):
    return [e for e in edges if rng.random() < 0.5]


def is_acyclic(n, F):
    g = nx.Graph(); g.add_nodes_from(range(n)); g.add_edges_from(F)
    return nx.is_forest(g)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--forests", type=int, default=12)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--max-n", type=int, default=7)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    t0 = time.time()
    graphs = [g for g in nx.graph_atlas_g() if 1 <= g.number_of_nodes() <= args.max_n]
    cnt = dict(graphs=0, forests=0, acyclic=0, cyclic=0, walks=0, pairs=0,
               A_viol=0, B_viol=0, B_iso_viol=0, C_viol=0, C_tight=0,
               D_seqs=0, D_viol=0, D_mmd_viol=0, D_degen_viol=0, D_mmd_ge_degen=0,
               E_runs=0, E_viol=0, F_skipped_acyclic=0, F_size_viol=0, F_cyclic_skipped=0)
    pw_cache = {}
    for g in graphs:
        n = g.number_of_nodes()
        adj = [set(g.neighbors(x)) for x in range(n)]
        edges = sorted((min(p, q), max(p, q)) for p, q in g.edges())
        adjmap = {x: adj[x] for x in range(n)}
        pwG = pathwidth_all_orderings(adjmap)
        cnt["graphs"] += 1
        run_claims = []
        for t in range(args.forests):
            F = random_forest(n, edges, rng) if t % 2 == 0 else random_subset(edges, rng)
            if t % 4 == 1:
                F = list(F); rng.shuffle(F)   # a random walk order too
            acyc = is_acyclic(n, F)
            cnt["forests"] += 1
            cnt["acyclic" if acyc else "cyclic"] += 1
            seq, R = uf_walk(n, F)
            cnt["walks"] += 1
            cnt["pairs"] += len(seq)
            # (A)
            H_full, ok = apply_seq(adj, [(a, b) for (a, b) in seq])
            if not ok:
                cnt["A_viol"] += 1
            # (B)
            Q = quotient(adj, R)
            if H_full != Q:
                cnt["B_viol"] += 1
            if removed(seq) != set(x for x in range(n) if R[x] != x):
                cnt["B_viol"] += 1
            surv = [x for x in range(n) if x not in removed(seq)]
            minor = {x: set(y for y in H_full[x] if y in surv) for x in surv}
            Hc = build_minor(adj, R)
            if minor != Hc:
                cnt["B_iso_viol"] += 1
            # (C)
            pwH = pathwidth_all_orderings(minor)
            if pwH > pwG:
                cnt["C_viol"] += 1
            if pwH == pwG:
                cnt["C_tight"] += 1
            # (D) degeneracy of the minor, MMD+ on the minor, random further sequences
            dg = degeneracy(minor)
            if dg > pwH:
                cnt["D_degen_viol"] += 1
            best, visited = contraction_degeneracy_c(minor)
            if best < dg:
                pass
            else:
                cnt["D_mmd_ge_degen"] += 1
            if best > pwG:
                cnt["D_mmd_viol"] += 1
            for (s2, alive) in visited:
                # replay s2 on the minor with Minor.lean semantics, S = alive
                idx = {v: i for i, v in enumerate(surv)}
                madj = [set(idx[y] for y in minor[v]) for v in surv]
                m2, ok2 = apply_seq(madj, [(idx[v], None if u is None else idx[u]) for (v, u) in s2])
                assert ok2
                S = set(idx[v] for v in alive)
                cnt["D_seqs"] += 1
                if min_degree_in({i: m2[i] for i in range(len(surv))}, S) > pwG:
                    cnt["D_viol"] += 1
            for _ in range(3):
                # a random legal sequence on the minor (contractions and deletions)
                idx = {v: i for i, v in enumerate(surv)}
                madj = [set(idx[y] for y in minor[v]) for v in surv]
                cur = madj; s2 = []; alive = set(range(len(surv)))
                for _k in range(rng.randrange(0, len(surv) + 1)):
                    if not alive:
                        break
                    v = rng.choice(sorted(alive))
                    nb = [u for u in cur[v] if u in alive]
                    if nb and rng.random() < 0.7:
                        u = rng.choice(nb); s2.append((v, u)); cur = contract_edge(cur, u, v)
                    else:
                        s2.append((v, None)); cur = isolate(cur, v)
                    alive.discard(v)
                m2 = {i: cur[i] for i in range(len(surv))}
                S = set(rng.sample(range(len(surv)), rng.randrange(0, len(surv) + 1)))
                cnt["D_seqs"] += 2
                if min_degree_in(m2, S) > pwG or min_degree_in(m2, alive) > pwG:
                    cnt["D_viol"] += 1
            # (F)
            if acyc:
                if len(seq) != len(F):
                    cnt["F_skipped_acyclic"] += 1
                if len(surv) != n - len(F):
                    cnt["F_size_viol"] += 1
            elif len(seq) != len(F):
                cnt["F_cyclic_skipped"] += 1
            # a claim for the run model (E): refutation kind at w = pwH - 1, or MMD+ kind
            if rng.random() < 0.5 and pwH >= 1:
                run_claims.append((F, pwH, "refutation", pwH))
            else:
                run_claims.append((F, best, "contraction_degeneracy", pwH))
        # (E) runs: random sublists of the claims, a given floor <= pwG
        for _ in range(3):
            k = rng.randrange(0, len(run_claims) + 1)
            run = rng.sample(run_claims, k)
            given = rng.randrange(0, pwG + 1)
            out = max([given] + [v for (_, v, _, _) in run])
            cnt["E_runs"] += 1
            if out > pwG:
                cnt["E_viol"] += 1
            for w in range(given + 1, pwG + 2):
                lhs = w <= out
                rhs = any(w <= pwH for (_, _, _, pwH) in run)
                # lhs -> rhs must hold (a reached floor above the given one is a visited minor with pw >= w);
                # rhs -> lhs need not: a visited minor can have pw >= w without the engine having claimed it
                if lhs and not rhs:
                    cnt["E_viol"] += 1
                # the exact iff is on claims: w <= out iff some claim >= w
                if lhs != any(w <= v for (_, v, _, _) in run):
                    cnt["E_viol"] += 1
    el = time.time() - t0
    print("minor_tabu_lean check: atlas graphs to %d vertices, seed %d, %.1f s" % (args.max_n, args.seed, el))
    for k, v in cnt.items():
        print("  %-20s %d" % (k, v))
    bad = cnt["A_viol"] + cnt["B_viol"] + cnt["B_iso_viol"] + cnt["C_viol"] + cnt["D_viol"] + cnt["D_mmd_viol"] + cnt["D_degen_viol"] + cnt["E_viol"] + cnt["F_skipped_acyclic"] + cnt["F_size_viol"]
    print("VIOLATIONS: %d" % bad)
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
