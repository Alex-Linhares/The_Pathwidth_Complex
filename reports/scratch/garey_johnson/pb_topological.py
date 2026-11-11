"""The black progressive pebble demand as a constrained vertex separation.

Claim checked: for every dag D (operand -> consumer orientation),
  pb(D) = min over topological orderings v_1..v_n of
          max_i ( |{ j < i : v_j has a successor among v_i..v_n }| + 1 ),
i.e. one more than the (left) vertex separation of the underlying graph, taken just
before each placement, over topological layouts (the operands of v_i are still
pebbled when v_i is placed; a first draft counted the boundary after the placement
and failed already on a single arc).  Checked against the game DP of register_sufficiency.py on
every labelled dag with <= 6 vertices.

Regenerate:  cd /home/al/dev/MOSP && python reports/scratch/garey_johnson/pb_topological.py
"""
from __future__ import annotations
import itertools, sys
sys.path.insert(0, "/home/al/dev/MOSP/reports/scratch/garey_johnson")
from register_sufficiency import demand


def pb_formula(n, arcs):
    succ = [set() for _ in range(n)]
    for u, v in arcs: succ[u].add(v)
    best = None
    for order in itertools.permutations(range(n)):
        pos = {v: i for i, v in enumerate(order)}
        if any(pos[u] > pos[v] for u, v in arcs): continue
        m = 0
        for i, v in enumerate(order):
            placed = set(order[:i])
            sep = sum(1 for j in range(i) if succ[order[j]] - placed)
            m = max(m, sep + 1)
        if best is None or m < best: best = m
    return best


if __name__ == "__main__":
    bad = 0; cnt = 0
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            arcs = [p for i, p in enumerate(pairs) if mask >> i & 1]
            pred = [0] * n
            for u, v in arcs: pred[v] |= 1 << u
            cnt += 1
            if pb_formula(n, arcs) != demand(n, pred, 0):
                bad += 1
                if bad < 5: print("MISMATCH", n, arcs)
    print(f"pb(D) = constrained vertex separation formula on all {cnt} labelled dags with <= 6 vertices: mismatches = {bad}")
