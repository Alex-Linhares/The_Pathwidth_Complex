"""SS7 (sequencing to minimise maximum cumulative cost) and PO1 (register sufficiency)
against MOSP and pathwidth: the exact computations behind
``reports/ss7_register_sufficiency.md``.

* ``ss7_value(n, pred, cost)`` — the SS7 optimum of a poset by a DP over order ideals
  (Garey & Johnson p. 238: a linear extension minimising the maximum prefix sum).
* ``embed_mosp(M)`` — the embedding of a 0/1 matrix (rows customers, columns patterns):
  open(c) at +1, close(c) at −1, pattern p at 0, open(c) ≺ p ≺ close(c) for p ∈ P_c and
  open(c) ≺ close(c) for every c (the pair is needed when a customer has no pattern: without
  it close(c) may precede open(c) and lower every prefix sum by one).
* ``mosp_bruteforce(M)`` — the MOSP optimum over all pattern orders.
* ``pb_game(n, pred, retain)`` — the one-shot black pebble demand by a search over positions
  (Sethi 1975 / G&J PO1 when ``retain`` is the set of outputs; Kirousis & Papadimitriou's
  progressive black game when ``retain = 0``).
* ``pb_ideal(n, succ, retain)`` — the layout formula: ``1 + min`` over maximal chains of order
  ideals (= topological layouts) of the maximum out-boundary ``|{w ∈ S : w ∈ R or succ(w) ⊄ S}|``
  of an ideal on the chain. The boundary depends on the ideal alone, so the minimum is a DP
  over ideals.
* ``binary_out_tree(h)`` — the complete binary out-tree of height ``h`` (root → leaves), the
  family with unbounded ``pb − pbw``; ``tree_g(children)`` the recursion
  ``g(T) = max(g₍₁₎, g₍₂₎ + 1, [T has a child])`` for the ideal-boundary value of an out-tree.
* ``lengauer_u(n, arcs)`` — Lengauer's ``G_u``; ``pbw = pw(G_u) + 1`` (PebblingGu.lean).

Regenerate the report's numbers: ``python reports/scratch/ss7_register_sufficiency/*.py``.
"""
from __future__ import annotations

import itertools
from typing import Iterable

import networkx as nx


# ----------------------------------------------------------------------------- SS7

def ss7_value(n: int, pred: list[int], cost: list[int]) -> int:
    """Minimum over linear extensions of the maximum prefix sum (the maximum over the
    ``n`` nonempty prefixes; ``0`` when ``n = 0``). ``pred[v]`` is the bitmask of the
    predecessors of ``v``; the relation need not be transitively closed."""
    full = (1 << n) - 1
    if n == 0:
        return 0
    total = [0] * (1 << n)
    for I in range(1, 1 << n):
        low = I & -I
        total[I] = total[I ^ low] + cost[low.bit_length() - 1]
    best = {0: None}  # best value of max prefix sum over chains reaching ideal I (None = -inf)
    frontier = [0]
    while frontier:
        nxt = {}
        for I in frontier:
            fI = best[I]
            for v in range(n):
                b = 1 << v
                if not (I & b) and (pred[v] & I) == pred[v]:
                    J = I | b
                    val = total[J] if fI is None else max(fI, total[J])
                    if J not in best or val < best[J]:
                        best[J] = val
                    nxt[J] = True
        frontier = list(nxt)
    return best[full]


def ss7_values_by_extension(n: int, pred: list[int], cost: list[int]) -> set[int]:
    """The set of values taken by max prefix sum over all linear extensions (brute force)."""
    vals = set()
    for order in itertools.permutations(range(n)):
        pos = {v: i for i, v in enumerate(order)}
        if any(pos[u] > pos[v] for v in range(n) for u in range(n) if pred[v] >> u & 1):
            continue
        s = 0; m = None
        for v in order:
            s += cost[v]
            m = s if m is None else max(m, s)
        vals.add(0 if m is None else m)
    return vals


def embed_mosp(M: list[list[int]]) -> tuple[int, list[int], list[int]]:
    """Tasks: open c = c, close c = n + c, pattern p = 2n + p."""
    n, m = len(M), (len(M[0]) if M else 0)
    N = 2 * n + m
    pred = [0] * N
    cost = [0] * N
    for c in range(n):
        cost[c] = 1
        cost[n + c] = -1
        pred[n + c] |= 1 << c
        for p in range(m):
            if M[c][p]:
                pred[2 * n + p] |= 1 << c
                pred[n + c] |= 1 << (2 * n + p)
    return N, pred, cost


def mosp_bruteforce(M: list[list[int]]) -> int:
    n, m = len(M), (len(M[0]) if M else 0)
    if m == 0:
        return 0
    best = None
    for order in itertools.permutations(range(m)):
        first = {}; last = {}
        for t, p in enumerate(order):
            for c in range(n):
                if M[c][p]:
                    first.setdefault(c, t); last[c] = t
        width = max(sum(1 for c in first if first[c] <= t <= last[c]) for t in range(m))
        if best is None or width < best:
            best = width
    return best


def mosp_graph(M: list[list[int]]) -> nx.Graph:
    n, m = len(M), (len(M[0]) if M else 0)
    G = nx.Graph(); G.add_nodes_from(range(n))
    for p in range(m):
        cs = [c for c in range(n) if M[c][p]]
        G.add_edges_from(itertools.combinations(cs, 2))
    return G


def is_series_parallel(n: int, lt: list[int]) -> bool:
    """N-free test on the transitive closure ``lt[v]`` = bitmask of elements below ``v``."""
    for a in range(n):
        for b in range(n):
            if a == b or lt[b] >> a & 1 or lt[a] >> b & 1:
                continue
            for c in range(n):
                if not (lt[c] >> a & 1 and lt[c] >> b & 1):
                    continue
                for d in range(n):
                    if d == c or lt[d] >> c & 1 or lt[c] >> d & 1:
                        continue
                    if lt[d] >> b & 1 and not (lt[d] >> a & 1) and not (lt[a] >> d & 1):
                        return False
    return True


def transitive_closure(n: int, pred: list[int]) -> list[int]:
    lt = list(pred)
    changed = True
    while changed:
        changed = False
        for v in range(n):
            new = lt[v]
            P = lt[v]
            while P:
                b = P & -P; P ^= b
                new |= lt[b.bit_length() - 1]
            if new != lt[v]:
                lt[v] = new; changed = True
    return lt


# ----------------------------------------------------------------------------- PO1

def pb_game(n: int, pred: list[int], retain: int) -> int:
    """One-shot black pebble demand: a pebble may be placed on a never-pebbled vertex whose
    predecessors all carry pebbles; a pebble not in ``retain`` may be removed; every vertex is
    pebbled exactly once. Smallest ``K`` admitting a play from nothing to everything done."""
    full = (1 << n) - 1
    for K in range(0, n + 1):
        if _pb_within(n, pred, retain, K, full):
            return K
    return n + 1


def _pb_within(n, pred, retain, K, full):
    start = (0, 0)
    seen = {start}; stack = [start]
    while stack:
        P, D = stack.pop()
        if D == full:
            return True
        if bin(P).count("1") < K:
            for v in range(n):
                b = 1 << v
                if not (D & b) and (pred[v] & P) == pred[v]:
                    s = (P | b, D | b)
                    if s not in seen:
                        seen.add(s); stack.append(s)
        R = P & ~retain
        while R:
            b = R & -R; R ^= b
            s = (P & ~b, D)
            if s not in seen:
                seen.add(s); stack.append(s)
    return False


def boundary(S: int, succ: list[int], retain: int) -> int:
    """``|{w ∈ S : w ∈ retain or succ(w) ⊄ S}|``, the out-boundary of the ideal ``S``."""
    cnt = 0; T = S
    while T:
        b = T & -T; T ^= b
        w = b.bit_length() - 1
        if (retain >> w & 1) or (succ[w] & ~S):
            cnt += 1
    return cnt


def pb_ideal(n: int, succ: list[int], retain: int = 0) -> int:
    """``1 + min`` over maximal chains of ideals of the maximum boundary (``0`` if ``n = 0``;
    ``0`` if the digraph has a cycle, i.e. no chain reaches the full set)."""
    if n == 0:
        return 0
    pred = [0] * n
    for w in range(n):
        S = succ[w]
        while S:
            b = S & -S; S ^= b
            pred[b.bit_length() - 1] |= 1 << w
    full = (1 << n) - 1
    best = {0: 0}
    frontier = [0]
    while frontier:
        nxt = {}
        for I in frontier:
            bI = max(best[I], boundary(I, succ, retain))
            for v in range(n):
                b = 1 << v
                if not (I & b) and (pred[v] & I) == pred[v]:
                    J = I | b
                    if J not in best or bI < best[J]:
                        best[J] = bI
                    nxt[J] = True
        frontier = list(nxt)
    return best[full] + 1 if full in best else 0


def pb_layouts(n: int, succ: list[int], retain: int = 0) -> int:
    """The same formula by brute force over topological orderings (small ``n`` only)."""
    pred = [0] * n
    for w in range(n):
        S = succ[w]
        while S:
            b = S & -S; S ^= b
            pred[b.bit_length() - 1] |= 1 << w
    best = None
    for order in itertools.permutations(range(n)):
        pos = {v: i for i, v in enumerate(order)}
        if any(pos[u] > pos[v] for v in range(n) for u in range(n) if pred[v] >> u & 1):
            continue
        S = 0; m = 0
        for v in order:
            m = max(m, boundary(S, succ, retain) + 1)
            S |= 1 << v
        if best is None or m < best:
            best = m
    return 0 if best is None else best


def succ_of_arcs(n: int, arcs: Iterable[tuple[int, int]]) -> list[int]:
    succ = [0] * n
    for u, v in arcs:
        succ[u] |= 1 << v
    return succ


def pred_of_succ(n: int, succ: list[int]) -> list[int]:
    pred = [0] * n
    for w in range(n):
        S = succ[w]
        while S:
            b = S & -S; S ^= b
            pred[b.bit_length() - 1] |= 1 << w
    return pred


def sinks(n: int, succ: list[int]) -> int:
    return sum(1 << v for v in range(n) if succ[v] == 0)


def lengauer_u(n: int, arcs: Iterable[tuple[int, int]]) -> nx.Graph:
    arcs = list(arcs)
    G = nx.Graph(); G.add_nodes_from(range(n))
    preds = [[] for _ in range(n)]
    for u, v in arcs:
        G.add_edge(u, v); preds[v].append(u)
    for x in range(n):
        G.add_edges_from(itertools.combinations(preds[x], 2))
    return G


def underlying(n: int, arcs: Iterable[tuple[int, int]]) -> nx.Graph:
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(arcs)
    return G


# ----------------------------------------------------------------------------- trees

def binary_out_tree(h: int) -> tuple[int, list[tuple[int, int]]]:
    """Vertices ``1 .. 2^(h+1) − 1`` in heap order, renumbered from ``0``; arcs parent → child."""
    n = 2 ** (h + 1) - 1
    arcs = [(v, 2 * v + 1) for v in range(n) if 2 * v + 1 < n] + \
           [(v, 2 * v + 2) for v in range(n) if 2 * v + 2 < n]
    return n, arcs


def tree_g(children: list[list[int]], root: int = 0) -> int:
    """``g(T) = max(g₍₁₎, g₍₂₎ + 1)`` with ``g = 1`` at a vertex with one child and ``0`` at a
    leaf (``g₍₁₎ ≥ g₍₂₎`` the two largest child values): the claimed ideal-boundary value of
    an out-tree, ``pb = g + 1``."""
    vals = sorted((tree_g(children, c) for c in children[root]), reverse=True)
    if not vals:
        return 0
    if len(vals) == 1:
        return max(1, vals[0])
    return max(vals[0], vals[1] + 1)


def random_out_tree(n: int, rng) -> list[list[int]]:
    children = [[] for _ in range(n)]
    for v in range(1, n):
        children[rng.randrange(v)].append(v)
    return children
