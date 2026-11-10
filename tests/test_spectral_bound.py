"""Tests for `learning.spectral_bound`: the three separator inequalities, the
prefix bound against exact pathwidth and exact Harper on small graphs, the
named cases (complete bipartite graphs are tight, as Gima et al. 2025 Remark
3.5 predicts), the families' monotonicity and the harness candidate."""

from __future__ import annotations

import itertools

import networkx as nx
import numpy as np
import pytest

from fixed_parameter_algorithm.pathwidth import compute_pathwidth
from learning import spectral_bound as sb


def _pw(g):
    return compute_pathwidth(nx.convert_node_labels_to_integers(g))[0]


@pytest.mark.parametrize("p,q", [(1, 4), (2, 3), (3, 5), (4, 4), (2, 7)])
def test_complete_bipartite_is_tight(p, q):
    g = nx.complete_bipartite_graph(p, q)
    value, _ = sb.spectral_graph_bound(g)
    assert value == min(p, q) == _pw(g)


def test_complete_graph_and_path_and_cycle():
    assert sb.spectral_graph_bound(nx.complete_graph(6))[0] == 5
    assert sb.spectral_graph_bound(nx.path_graph(9))[0] == 1
    assert sb.spectral_graph_bound(nx.cycle_graph(9))[0] == 2
    assert sb.spectral_graph_bound(nx.empty_graph(5))[0] == 0
    assert sb.spectral_graph_bound(nx.Graph())[0] == 0


def test_inequalities_on_every_triple_to_six_vertices():
    res = sb.check_inequalities(6)
    assert res["graphs"] > 100 and res["triples"] > 5_000
    assert res["violations"] == []


def test_prefix_bound_never_above_pathwidth_or_harper_on_the_atlas():
    seen = 0
    for g in nx.graph_atlas_g():
        n = g.number_of_nodes()
        if n < 2 or n > 6:
            continue
        pw = _pw(g)
        res = sb.spectral_bounds(g)
        assert res["best"] <= pw, nx.to_graph6_bytes(g)
        assert res["graph"] <= sb.harper_exact(g) <= pw
        seen += 1
    assert seen > 100


def test_random_graphs_against_exact_pathwidth():
    rng = np.random.default_rng(3)
    for n in (8, 9, 10, 11):
        for p in (0.25, 0.5):
            for _ in range(6):
                g = nx.gnp_random_graph(n, p, seed=int(rng.integers(2 ** 31)))
                res = sb.spectral_bounds(g)
                assert res["best"] <= _pw(g)
                assert res["graph"] <= res["peel"] and res["graph"] <= res["minor"]


def test_harper_exact_matches_brute_force_definition():
    g = nx.petersen_graph()
    n = g.number_of_nodes()
    nodes = list(g.nodes)
    best = 0
    for t in range(1, n):
        m = min(len(set().union(*(set(g[v]) for v in S)) - set(S))
                for S in itertools.combinations(nodes, t))
        best = max(best, m)
    assert sb.harper_exact(g) == best == 5
    assert sb.spectral_graph_bound(g)[0] == 4   # the spectral relaxation loses one here


def test_theorem_one_alone_is_at_most_the_combined_value():
    for g in (nx.petersen_graph(), nx.grid_2d_graph(3, 4), nx.complete_bipartite_graph(3, 6)):
        g = nx.convert_node_labels_to_integers(g)
        mp, _ = sb.spectral_graph_bound(g, use=("mp",))
        allv, _ = sb.spectral_graph_bound(g)
        assert mp <= allv


def test_tolerance_direction_weakens_the_bound():
    # a slightly larger mu2 could only raise the value; the module lowers it
    g = nx.complete_bipartite_graph(3, 5)
    mu2, mun = sb.laplacian_extremes(g)
    degs = [d for _, d in g.degree()]
    v_mod, _ = sb.prefix_separator_bound(8, mu2, mun, degs)
    v_raw = 0
    S = sb.top_degree_sums(degs)
    for t in range(1, 8):
        for c in range(0, 8 - t + 1):
            if sb.feasible(c, t, 8 - t - c, 8, mu2 + 1e-3, mun - 1e-3, S):
                v_raw = max(v_raw, c)
                break
    assert v_mod <= v_raw


def test_candidate_signature_and_units():
    from learning.bound_harness import Budget, graph_from_matrix

    matrix = np.array([[1, 1, 0, 0], [1, 1, 1, 0], [0, 1, 1, 1], [0, 0, 1, 1]])
    g = graph_from_matrix(matrix)
    value, info = sb.cand_spectral(g, matrix, Budget(seconds=10))
    assert value == info["seed"] or value >= info["seed"]
    assert value == max(info["graph"], info["peel"], info["minor"])
    assert value <= _pw(g) + 1
    assert {"mu2", "mun", "delta", "gima1", "gima2", "mp_graph"} <= set(info)


def test_disconnected_graph_takes_the_maximum_over_components():
    g = nx.disjoint_union(nx.complete_graph(4), nx.path_graph(5))
    assert sb.spectral_graph_bound(g)[0] == 3


def test_register_adds_the_candidate_to_the_harness():
    from learning import bound_harness

    sb.register()
    assert bound_harness.CANDIDATES["spectral"] is sb.cand_spectral
