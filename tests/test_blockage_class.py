"""Tests of `learning.blockage_class`: the operators are blockages (the statements
of `lean/MOSPFormalization/BlockageClass.lean`), the duality on tiny graphs, the
ceiling against pathwidth, and the two ceiling implementations against each other."""
from __future__ import annotations

import random

import networkx as nx
import pytest

from learning.blockage_class import (
    Ceiling, adj_from_edges, adj_from_nx, atlas, avoid, blockage_exists, branch_big,
    branch_excluded, ceiling_by_minor_closure, check_branch, check_clique, check_minor,
    clique_big, clique_number, counting_upper_bound, is_blockage_in, is_connected, linked,
    min_vertices, minor_big, pathwidth_exact, popcount,
)


def spider(legs: int = 3, length: int = 2) -> list[int]:
    edges = []
    v = 1
    for _ in range(legs):
        prev = 0
        for _ in range(length):
            edges.append((prev, v))
            prev = v
            v += 1
    return adj_from_edges(v, edges)


def test_pathwidth_exact_matches_known_values():
    assert pathwidth_exact(adj_from_edges(3, [(0, 1), (1, 2)])) == 1
    assert pathwidth_exact(adj_from_edges(4, [(i, j) for i in range(4) for j in range(i + 1, 4)])) == 3
    assert pathwidth_exact(spider()) == 2
    assert pathwidth_exact(adj_from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])) == 2


def test_duality_to_five_vertices():
    """A blockage of order n exists iff pw >= n (both halves of BRST (2.1))."""
    for adj in atlas(5):
        pw = pathwidth_exact(adj)
        V = (1 << len(adj)) - 1
        for n in range(len(adj) + 1):
            assert blockage_exists(adj, V, n) == (pw >= n)


def test_clique_frame_is_blockage():
    for adj in atlas(5):
        assert check_clique(adj) == []


def test_branch_and_minor_frames_are_blockages():
    rng = random.Random(1)
    for adj in atlas(6):
        assert check_branch(adj, rng, samples=12) == []
        assert check_minor(adj, rng, samples=8) == []


def test_unlinked_branches_fail_somewhere():
    """The linking hypothesis is load-bearing: the control counts failures."""
    rng = random.Random(2)
    stats: dict = {}
    for adj in atlas(6):
        check_branch(adj, rng, samples=12, stats=stats)
    assert stats.get("linked_fail", 0) == 0
    assert stats.get("unlinked_fail", 0) > 0


def test_spider_certified_by_branch_frame():
    adj = spider()
    V = (1 << 7) - 1
    legs = [0b110, 0b11000, 0b1100000]            # the three legs, each a K2
    bigs = [clique_big(L) for L in legs]
    big = branch_big(legs[0], legs[1], legs[2], *bigs)
    assert all(linked(adj, V, legs[i], legs[j], legs[k]) for i, j, k in ((0, 1, 2), (0, 2, 1), (1, 2, 0)))
    ok, why = is_blockage_in(adj, V, 2, avoid(adj, V, 2, big))
    assert ok, why


def test_minor_pullback_of_triangle_on_c6():
    adj = adj_from_edges(6, [(i, (i + 1) % 6) for i in range(6)])
    sets = [0b11, 0b1100, 0b110000]              # three paths of two, a triangle minor
    ok, why = is_blockage_in(adj, 0b111111, 2, avoid(adj, 0b111111, 2, minor_big(sets, clique_big(0b111))))
    assert ok, why


def test_ceiling_matches_closure_and_is_valid():
    ce = Ceiling()
    cache: dict = {}
    for adj in atlas(6):
        a = ce.ceiling(adj)
        assert a == ceiling_by_minor_closure(adj, cache)
        assert a <= pathwidth_exact(adj)


def test_ceiling_on_hand_instances():
    ce = Ceiling()
    assert ce.ceiling(spider()) == 2                       # three K2 branches at a hub
    k4 = adj_from_edges(4, [(i, j) for i in range(4) for j in range(i + 1, 4)])
    assert ce.ceiling(k4) == 3
    ears = adj_from_nx(nx.from_graph6_bytes(b"EElw"))      # triangle with three ears: pw 3, tw 2
    assert pathwidth_exact(ears) == 3
    assert ce.hadwiger(ears) == 3
    assert ce.ceiling(ears) == 2                           # the smallest graph the class misses
    tree = adj_from_edges(13, [(0, 1), (0, 2), (0, 3)] + [(i, 3 * i + j) for i in (1, 2, 3) for j in (1, 2, 3)])
    assert pathwidth_exact(tree) == 2 and ce.ceiling(tree) == 2


def test_counting_bounds():
    assert min_vertices(3, had=4) == 4
    assert min_vertices(4, had=4) == 12                    # three K4s
    assert min_vertices(5, had=4) == 36
    assert counting_upper_bound(n=20, had_upper=4, tau=8, edges=50) == 3
    assert counting_upper_bound(n=20, had_upper=4, tau=10, edges=50) == 4
    assert counting_upper_bound(n=40, had_upper=4, tau=30, edges=100) == 5    # three branches of three K4s fit in 40
    assert branch_excluded(t=5, n=20, had_upper=4, tau=15, edges=50)
    assert not branch_excluded(t=4, n=40, had_upper=4, tau=30, edges=100)


def test_connectivity_and_clique_helpers():
    adj = adj_from_edges(4, [(0, 1), (2, 3)])
    assert is_connected(adj, 0b11) and not is_connected(adj, 0b101) and not is_connected(adj, 0)
    assert clique_number(adj) == 2
    assert popcount(0b1011) == 3
