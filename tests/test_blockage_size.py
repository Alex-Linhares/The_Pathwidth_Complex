"""Tests of `learning.blockage_size`: the SAT model of the blockages of order k
against two brute-force enumerations and the all-pairs axiom checker, the
duality (a blockage exists iff pw >= k), the three size measures and a few
known values."""
from __future__ import annotations

import json

import networkx as nx
import pytest

from learning.blockage_class import atlas, is_connected
from learning.blockage_size import (
    BlockageCNF, adj_from_edges, adj_from_nx, alpha_table, bits, brute_force_min_frame_families,
    brute_force_min_frame_upsets, census_row, frame_of, full_mask, generators_cover, is_blockage,
    maximal_members, min_size, named_graphs, pathwidth_exact, popcount, ten_vertex_graph, upsets,
)


def test_upsets_are_dedekind_counts():
    assert [sum(1 for _ in upsets(n)) for n in range(5)] == [2, 3, 6, 20, 168]
    assert sum(1 for _ in upsets(5)) == 7581


def test_model_against_every_family_to_four_vertices():
    """Every family of subsets, every graph of the atlas on <= 4 vertices, every
    order 1..n: the SAT minimum equals the brute-force minimum (or both say no
    blockage)."""
    cases = 0
    for adj in atlas(4):
        for k in range(1, len(adj) + 1):
            r = min_size(adj, k, "frame")
            sat = r["value"] if r["status"] == "exact" else None
            assert r["status"] in ("exact", "none")
            bf = brute_force_min_frame_families(adj, k)
            assert sat == bf, (adj, k, sat, bf)
            cases += 1
    assert cases >= 40


def test_model_against_every_upset_to_five_vertices():
    """Every up-set of 2^V (7,581 at five vertices), every graph of the atlas on
    5 vertices, every order 1..5."""
    cases = 0
    for adj in atlas(5):
        if len(adj) != 5:
            continue
        for k in range(1, 6):
            r = min_size(adj, k, "frame")
            sat = r["value"] if r["status"] == "exact" else None
            bf = brute_force_min_frame_upsets(adj, k)
            assert sat == bf, (adj, k, sat, bf)
            cases += 1
    assert cases == 34 * 5


def test_duality_and_axioms_to_six_vertices():
    """A blockage exists iff pw >= k; every minimiser found passes the all-pairs
    axiom checker of `learning.blockage_class`; its recomputed frame has the
    size the model reports; size2 <= size1 and the generators found regenerate
    the blockage."""
    graphs = 0
    for adj in atlas(6):
        if not is_connected(adj, full_mask(adj)):
            continue
        graphs += 1
        pw = pathwidth_exact(adj)
        alpha = alpha_table(adj)
        for k in range(1, pw + 2):
            r = min_size(adj, k, "frame")
            if k > pw:
                assert r["status"] == "none"
                continue
            assert r["status"] == "exact"
            assert is_blockage(adj, k, r["members"])
            assert len(frame_of(adj, k, r["members"], alpha)) == r["value"]
            r2 = min_size(adj, k, "generators")
            assert r2["status"] == "exact" and r2["value"] <= r["value"]
            assert is_blockage(adj, k, r2["members"])
            assert generators_cover(adj, k, r2["members"], r2["generators"], alpha)
            r3 = min_size(adj, k, "maximal")
            assert r3["status"] == "exact"
            assert is_blockage(adj, k, r3["members"])
            assert len(maximal_members(adj, k, r3["members"], alpha)) == r3["value"]
    assert graphs == 112 + 21 + 6 + 2 + 1 + 1


def test_known_values():
    p3 = adj_from_edges(3, [(0, 1), (1, 2)])
    assert min_size(p3, 1, "frame")["value"] == 1
    assert min_size(p3, 2, "frame")["status"] == "none"
    k5 = adj_from_nx(nx.complete_graph(5))
    for k in range(1, 5):
        r = min_size(k5, k, "frame")
        assert r["value"] == 1 and r["frame"] == [31]
    spider = adj_from_edges(7, [(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)])
    assert min_size(spider, 2, "frame")["value"] == 3          # the three leg pairs
    c5 = adj_from_nx(nx.cycle_graph(5))
    assert min_size(c5, 2, "frame")["value"] == 2
    pet = adj_from_nx(nx.petersen_graph())
    assert pathwidth_exact(pet) == 5
    assert [min_size(pet, k, "frame")["value"] for k in (5, 4, 3)] == [15, 5, 2]
    assert min_size(pet, 5, "generators")["value"] == 8
    g10 = ten_vertex_graph()
    assert pathwidth_exact(g10) == 5


def test_timed_run_agrees_with_untimed():
    adj = adj_from_nx(nx.grid_2d_graph(3, 3))
    a = min_size(adj, 3, "frame")
    b = min_size(adj, 3, "frame", time_limit=60)
    assert a["status"] == b["status"] == "exact" and a["value"] == b["value"] == 4


def test_census_row_fields():
    row = census_row(adj_from_nx(nx.cycle_graph(5)), alt=True)
    assert row["pw"] == 2 and row["tw"] == 2
    assert json.loads(row["size1"]) == [1, 2]
    assert json.loads(row["size2"]) == [1, 2]
    assert len(json.loads(row["frame_pw"])) == 2


def test_named_graphs_build():
    names = [n for n, _ in named_graphs()]
    assert "Petersen" in names and "pwtw2_10" in names and any(n.startswith("cubic16") for n in names)
    for _, adj in named_graphs():
        assert is_connected(adj, full_mask(adj))
