"""`learning.gaspers_sweep` (2026-11-11): the labels have unit variance and the
edge correlations Lemma 3.4 promises; the plain and median-switched layouts are
valid and their widths are the vertex separation of an independent check; the
connector order satisfies Lemma 8.3's inequality; on the five small cubic graphs
of known pathwidth the sweep never reports a width below the certified value;
the C program's `-u` file is the layout reversed."""

import itertools
import math

import numpy as np
import pytest

from learning.gaspers_sweep import (
    C3, C_STAR, CERTIFIED_CUBIC, R_STAR, adjacency, connector_counts, connector_order,
    decomposition_to_layout, frontiers, is_path_decomposition, label_correlation, labels, load_record,
    median_switched_decomposition, median_switched_layout, plain_sweep, sweep, vertex_separation,
    vertex_separation_fast, weight_matrix, write_closing_order)
from pathwidth_solver.bench.graph_split import vertex_separation as reference_vs


def _cycle(n):
    return adjacency(n, [(i, (i + 1) % n) for i in range(n)])


def _petersen():
    r = load_record("pwc-16021")
    return adjacency(r["n"], r["edges"])


def test_constants():
    assert C3 == pytest.approx(0.13982, abs=1e-5)
    assert C_STAR == pytest.approx(0.16226, abs=1e-5)
    assert R_STAR == pytest.approx(0.94281, abs=1e-5)
    assert C3 < C_STAR < 1 / 6


@pytest.mark.parametrize("seed", range(3))
def test_vertex_separation_agrees_with_reference_and_fast(seed):
    r = load_record("pwc-16010")                     # McGee, 24 vertices
    adj = adjacency(r["n"], r["edges"])
    rng = np.random.default_rng(seed)
    for _ in range(30):
        layout = [int(v) for v in rng.permutation(r["n"])]
        a = vertex_separation(adj, layout)
        assert a == vertex_separation_fast(adj, layout)
        assert a == reference_vs(r["n"], [tuple(e) for e in r["edges"]], layout)


def test_vertex_separation_rejects_non_permutations():
    adj = _cycle(4)
    with pytest.raises(ValueError):
        vertex_separation(adj, [0, 1, 2, 2])
    with pytest.raises(ValueError):
        vertex_separation(adj, [0, 1, 2])


def test_labels_unit_variance_and_edge_correlation_bound():
    """Lemma 3.4: on a graph of maximum degree 3 every edge has correlation at
    least (2 sqrt 2 / 3)(1 - 1 / R) under the geometric labels at radius R."""
    adj = _petersen()
    for R in (1, 2, 3, 4):
        C = weight_matrix(adj, R)
        for v in range(len(adj)):
            assert np.dot(C[v], C[v]) == pytest.approx(1.0)
        for u in range(len(adj)):
            for v in adj[u]:
                assert label_correlation(C, u, v) >= R_STAR * (1 - 1 / R) - 1e-12
    # the weights are 2^{-dist/2} on the ball: at R = 1 a neighbour has weight 1/sqrt 2 of the centre
    C = weight_matrix(adj, 1)
    assert C[0, adj[0][0]] / C[0, 0] == pytest.approx(2 ** -0.5)
    assert sum(1 for w in range(10) if C[0, w] > 0) == 4


def test_labels_are_gaussian_with_the_right_covariance():
    adj = _petersen()
    C = weight_matrix(adj, 2)
    rng = np.random.default_rng(0)
    Y = np.array([labels(C, rng) for _ in range(20000)])
    cov = np.cov(Y.T)
    assert np.allclose(np.diag(cov), 1.0, atol=0.05)
    u, v = 0, adj[0][0]
    assert cov[u, v] == pytest.approx(label_correlation(C, u, v), abs=0.05)


def test_mixed_labels_coincide_with_padded_on_cubic_graphs():
    adj = _petersen()
    assert np.allclose(weight_matrix(adj, 2, kind="padded"), weight_matrix(adj, 2, kind="mixed"))
    with pytest.raises(ValueError):
        weight_matrix(_cycle(5), 2, kind="mixed")


def test_frontiers_definitions():
    adj = _cycle(6)
    y = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0]
    inner, outer = frontiers(adj, y, 2.5)      # S = {0, 1, 2}
    assert inner == {0, 2} and outer == {3, 5}


def test_plain_sweep_widths_are_the_frontier_maxima():
    adj = _petersen()
    rng = np.random.default_rng(1)
    y = labels(weight_matrix(adj, 2), rng)
    order, rev, wi, wo = plain_sweep(adj, y)
    assert rev == order[::-1]
    thresholds = sorted(y)
    assert wi == max(len(frontiers(adj, y, t)[0]) for t in thresholds)
    assert wo == max(len(frontiers(adj, y, t)[1]) for t in thresholds)
    assert wi == vertex_separation(adj, order) and wo == vertex_separation(adj, rev)


def _random_connector_instance(rng, k, p):
    Q = list(range(k))
    items = {}
    for i in range(p):
        e = frozenset(rng.choice(k, size=min(k, int(rng.integers(1, 3))), replace=False).tolist())
        items[100 + i] = e
    return Q, items


@pytest.mark.parametrize("seed", range(40))
def test_connector_order_satisfies_lemma_8_3(seed):
    rng = np.random.default_rng(seed)
    k, p = int(rng.integers(1, 9)), int(rng.integers(0, 12))
    Q, items = _random_connector_instance(rng, k, p)
    order = connector_order(Q, items)
    assert sorted(order) == Q
    c = connector_counts(order, items)
    for j in range(k + 1):
        assert j - c[j] <= max(0, k - len(items)) + 1


def test_connector_order_beats_a_bad_order_when_it_matters():
    # a path of items: 0-1, 1-2, 2-3; k = 4, |P| = 3; a bad order 0, 2, 1, 3 has j - c(j) = 2 at j = 2
    items = {10: frozenset({0, 1}), 11: frozenset({1, 2}), 12: frozenset({2, 3})}
    bad = connector_counts([0, 2, 1, 3], items)
    assert max(j - bad[j] for j in range(5)) == 2
    good = connector_counts(connector_order([0, 1, 2, 3], items), items)
    assert max(j - good[j] for j in range(5)) <= 1


@pytest.mark.parametrize("seed", range(5))
def test_median_switched_decomposition_is_a_path_decomposition(seed):
    for rid in ("pwc-16021", "pwc-15984", "pwc-16027"):
        r = load_record(rid)
        adj = adjacency(r["n"], r["edges"])
        rng = np.random.default_rng(seed)
        y = labels(weight_matrix(adj, 2), rng)
        bags, w, d = median_switched_decomposition(adj, y, float(np.median(y)))
        assert is_path_decomposition(adj, bags)
        assert w == max(len(b) for b in bags) - 1
        # Lemma 8.4's three conditions bound the width
        inner_below = max((len(frontiers(adj, y, t)[0]) for t in y if t < np.median(y)), default=0)
        outer_above = max((len(frontiers(adj, y, t)[1]) for t in y if t > np.median(y)), default=0)
        assert w <= max(inner_below, outer_above, max(d["L0"], d["L0p"]) + 1)
        layout, wl, wb = median_switched_layout(adj, y, float(np.median(y)))
        assert wb == w and wl <= w
        assert wl == vertex_separation(adj, layout) == reference_vs(r["n"], [tuple(e) for e in r["edges"]], layout)


def test_median_switched_rejects_degree_four():
    adj = adjacency(5, list(itertools.combinations(range(5), 2)))      # K5, degree 4
    with pytest.raises(ValueError):
        median_switched_decomposition(adj, [0.1 * i for i in range(5)])


def test_decomposition_to_layout_never_widens():
    adj = _petersen()
    rng = np.random.default_rng(5)
    for _ in range(10):
        y = labels(weight_matrix(adj, 3), rng)
        bags, w, _ = median_switched_decomposition(adj, y, float(np.median(y)))
        layout = decomposition_to_layout(len(adj), bags)
        assert vertex_separation(adj, layout) <= w


def test_sweep_on_cycle_and_complete_graph():
    best, stats = sweep(_cycle(12), 20, seed=0, radii=(1, 2))
    assert best["width"] == 2 and best["checked_width"] == 2        # pw(C_12) = 2
    k4 = adjacency(4, list(itertools.combinations(range(4), 2)))
    best, _ = sweep(k4, 5, seed=0, radii=(1,))
    assert best["width"] == 3


@pytest.mark.parametrize("rid", ["pwc-16021", "pwc-15984", "pwc-16027", "pwc-16010", "pwc-16065"])
def test_sweep_never_below_the_certified_pathwidth(rid):
    """Petersen 5, Heawood 6, Pappus 7, McGee 8, Tutte-Coxeter 9: every width
    the sweep reports is the vertex separation of a layout, rechecked, so it
    is at least the pathwidth; the certified value is the dataset's."""
    name, n, pw = CERTIFIED_CUBIC[rid]
    r = load_record(rid)
    assert r["provenance"].startswith("certified") and r["width"] == pw and r["n"] == n
    adj = adjacency(r["n"], r["edges"])
    best, stats = sweep(adj, 120, seed=2, radii=(1, 2, 3))
    assert best["width"] >= pw
    assert best["checked_width"] == best["width"] == vertex_separation(adj, best["layout"])
    assert best["width"] == reference_vs(n, [tuple(e) for e in r["edges"]], best["layout"])
    for s in stats.values():
        assert s["min"] >= pw


def test_closing_order_file_is_the_layout_reversed(tmp_path):
    p = tmp_path / "seed.txt"
    write_closing_order(p, [3, 1, 0, 2])
    assert p.read_text().split() == ["2", "0", "1", "3"]
    # a closing order's prefix boundary is the layout's count at the matching position
    adj = _cycle(5)
    layout = [0, 1, 2, 3, 4]
    closing = layout[::-1]
    boundaries = []
    for i in range(1, 6):
        U = set(closing[:i])
        boundaries.append(len({w for u in U for w in adj[u]} - U))
    assert max(boundaries) == vertex_separation(adj, layout)
