"""Tests for paper1/ss7_register.py: SS7 against MOSP, the pebble layout formula, the binary
out-tree family (reports/ss7_register_sufficiency.md)."""
import itertools
import random

import pytest

from paper1.ss7_register import (binary_out_tree, boundary, embed_mosp, is_series_parallel,
                                 lengauer_u, mosp_bruteforce, mosp_graph, pb_game, pb_ideal,
                                 pb_layouts, pred_of_succ, random_out_tree, sinks, ss7_value,
                                 ss7_values_by_extension, succ_of_arcs, transitive_closure,
                                 tree_g, underlying)
from fixed_parameter_algorithm.pathwidth import compute_pathwidth


def all_matrices(n, m):
    for bits in itertools.product([0, 1], repeat=n * m):
        yield [list(bits[i * m:(i + 1) * m]) for i in range(n)]


def test_ss7_value_agrees_with_brute_force_over_extensions():
    rng = random.Random(0)
    for _ in range(200):
        n = rng.randint(1, 6)
        pred = [0] * n
        for v in range(n):
            for u in range(v):
                if rng.random() < 0.3:
                    pred[v] |= 1 << u
        cost = [rng.randint(-2, 2) for _ in range(n)]
        assert ss7_value(n, pred, cost) == min(ss7_values_by_extension(n, pred, cost))


def test_ss7_value_empty():
    assert ss7_value(0, [], []) == 0


def test_embedding_equals_mosp_and_pathwidth_on_small_matrices():
    for n in range(1, 4):
        for m in range(1, 4):
            for M in all_matrices(n, m):
                if not any(any(r) for r in M):
                    continue
                N, pred, cost = embed_mosp(M)
                a = ss7_value(N, pred, cost)
                assert a == mosp_bruteforce(M)
                assert a == compute_pathwidth(mosp_graph(M))[0] + 1


def test_embedding_costs_are_unit():
    N, pred, cost = embed_mosp([[1, 0], [1, 1]])
    assert set(cost) <= {-1, 0, 1}
    assert cost.count(1) == 2 and cost.count(-1) == 2 and cost.count(0) == 2


def test_embedding_edge_case_without_requirement():
    # a customer requiring nothing: SS7 gives 1 (open then close), MOSP gives 0
    N, pred, cost = embed_mosp([[0, 0]])
    assert ss7_value(N, pred, cost) == 1 and mosp_bruteforce([[0, 0]]) == 0


def test_open_before_close_pair_is_needed():
    M = [[1], [0]]        # customer 1 requires nothing
    N, pred, cost = embed_mosp(M)
    assert ss7_value(N, pred, cost) == 1
    pred2 = list(pred); pred2[2 + 1] &= ~(1 << 1)   # drop open(1) < close(1)
    assert ss7_value(N, pred2, cost) == 0


def test_dual_pair_witness():
    assert ss7_value(2, [0, 1], [1, -1]) == 1
    assert ss7_value(2, [2, 0], [1, -1]) == 0


def test_antichain_and_matched_pairs():
    for k in range(1, 5):
        assert ss7_value(k, [0] * k, [1] * k) == k
        assert ss7_value(2 * k, [0] * k + [1 << i for i in range(k)], [1] * k + [-1] * k) == 1


def test_series_parallel_iff_disjoint_cliques():
    for n in range(1, 4):
        for m in range(1, 4):
            for M in all_matrices(n, m):
                if not any(any(r) for r in M):
                    continue
                N, pred, cost = embed_mosp(M)
                nfree = is_series_parallel(N, transitive_closure(N, pred))
                rows = [tuple(r) for r in M]
                cliques = all(rows[c] == rows[d] for c in range(n) for d in range(n)
                              if c != d and any(M[c][p] and M[d][p] for p in range(m)))
                assert nfree == cliques


def test_pb_formula_on_all_dags_to_five_vertices():
    for n in range(1, 6):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            arcs = [p for i, p in enumerate(pairs) if mask >> i & 1]
            succ = succ_of_arcs(n, arcs); pred = pred_of_succ(n, succ); R = sinks(n, succ)
            assert pb_game(n, pred, 0) == pb_ideal(n, succ, 0) == pb_layouts(n, succ, 0)
            assert pb_game(n, pred, R) == pb_ideal(n, succ, R) == pb_layouts(n, succ, R)


def test_pb_formula_random_eight_vertices():
    rng = random.Random(8)
    for _ in range(60):
        n = 8
        arcs = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < 0.3]
        succ = succ_of_arcs(n, arcs); pred = pred_of_succ(n, succ); R = sinks(n, succ)
        assert pb_game(n, pred, 0) == pb_ideal(n, succ, 0)
        assert pb_game(n, pred, R) == pb_ideal(n, succ, R)


def test_pb_ideal_zero_on_cycle_and_empty():
    assert pb_ideal(0, [], 0) == 0
    assert pb_ideal(2, [2, 1], 0) == 0       # 0 -> 1 -> 0: no topological layout


def test_boundary_counts_retained_and_waiting():
    succ = succ_of_arcs(3, [(0, 1), (1, 2)])
    assert boundary(0b001, succ, 0) == 1     # 0 waits for 1
    assert boundary(0b011, succ, 0) == 1     # 1 waits for 2; 0 is finished
    assert boundary(0b011, succ, 0b001) == 2 # 0 retained


def test_binary_out_tree_demand_and_width():
    for h, pb, pw in ((0, 1, 0), (1, 2, 1), (2, 3, 1), (3, 4, 2)):
        n, arcs = binary_out_tree(h)
        succ = succ_of_arcs(n, arcs)
        assert pb_ideal(n, succ, 0) == pb == h + 1
        G = lengauer_u(n, arcs)
        assert G.number_of_edges() == len(arcs)          # G_u = the tree
        assert compute_pathwidth(G)[0] == pw == (h + 1) // 2


def test_out_tree_recursion():
    rng = random.Random(5)
    for n in range(1, 11):
        for _ in range(40):
            ch = random_out_tree(n, rng)
            arcs = [(v, c) for v in range(n) for c in ch[v]]
            assert pb_ideal(n, succ_of_arcs(n, arcs), 0) == tree_g(ch) + 1


def test_pb_at_least_pbw_on_small_dags():
    # pb(D) >= pw(G_u) + 1 (PebblingGu.lean) on every dag with <= 5 vertices
    for n in range(1, 6):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            arcs = [p for i, p in enumerate(pairs) if mask >> i & 1]
            succ = succ_of_arcs(n, arcs)
            assert pb_ideal(n, succ, 0) >= compute_pathwidth(lengauer_u(n, arcs))[0] + 1
            assert compute_pathwidth(lengauer_u(n, arcs))[0] >= compute_pathwidth(underlying(n, arcs))[0]
