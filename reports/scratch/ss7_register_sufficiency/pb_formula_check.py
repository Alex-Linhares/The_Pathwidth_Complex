"""pb(D) = 1 + min over maximal chains of ideals of the maximum out-boundary, with and without
retained outputs: every labelled dag on <= 6 vertices (game DP vs ideal DP vs brute force over
topological orderings) and 2,000 random dags on 9 vertices (game DP vs ideal DP).

Regenerate: cd /home/al/dev/MOSP && python reports/scratch/ss7_register_sufficiency/pb_formula_check.py
"""
import itertools, random, sys, time
sys.path.insert(0, "/home/al/dev/MOSP")
from paper1.ss7_register import pb_game, pb_ideal, pb_layouts, succ_of_arcs, pred_of_succ, sinks

t0 = time.time(); cnt = 0; bad = [0, 0, 0, 0]
for n in range(1, 7):
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        arcs = [p for i, p in enumerate(pairs) if mask >> i & 1]
        succ = succ_of_arcs(n, arcs); pred = pred_of_succ(n, succ); R = sinks(n, succ)
        cnt += 1
        g0, i0, l0 = pb_game(n, pred, 0), pb_ideal(n, succ, 0), pb_layouts(n, succ, 0)
        gR, iR, lR = pb_game(n, pred, R), pb_ideal(n, succ, R), pb_layouts(n, succ, R)
        bad[0] += g0 != i0; bad[1] += i0 != l0; bad[2] += gR != iR; bad[3] += iR != lR
        if g0 != i0 or gR != iR:
            print("MISMATCH", n, arcs, g0, i0, gR, iR)
print(f"all {cnt} labelled dags on 1..6 vertices: game vs ideal formula mismatches = {bad[0]} (no retention), "
      f"{bad[2]} (outputs retained); ideal DP vs brute force over topological orderings: {bad[1]}, {bad[3]}  [{time.time()-t0:.0f}s]")

rng = random.Random(9); cnt = 0; bad = [0, 0]; maxpb = 0
for _ in range(2000):
    n = 9
    p = rng.choice([0.15, 0.25, 0.35, 0.5, 0.7])
    arcs = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < p]
    succ = succ_of_arcs(n, arcs); pred = pred_of_succ(n, succ); R = sinks(n, succ)
    cnt += 1
    g0, i0 = pb_game(n, pred, 0), pb_ideal(n, succ, 0)
    gR, iR = pb_game(n, pred, R), pb_ideal(n, succ, R)
    bad[0] += g0 != i0; bad[1] += gR != iR; maxpb = max(maxpb, g0)
    if g0 != i0 or gR != iR:
        print("MISMATCH", arcs, g0, i0, gR, iR)
print(f"{cnt} random dags on 9 vertices: mismatches = {bad[0]} (no retention), {bad[1]} (outputs retained); "
      f"max pb = {maxpb}  [{time.time()-t0:.0f}s]")
