"""`learning.quick_estimate`: the four numbers against brute force on small graphs, the
block rule against the table of `reports/dense_staircase.md` section 4, the estimators'
definitions, and the record readers' bookkeeping (certified truths only)."""

import itertools
import math
import random

import numpy as np
import pytest

from learning import quick_estimate as qe
from learning.first_moment import floors
from learning.random_graph_classes import gnp_floors


def _random_masks(n, p, seed):
    rng = random.Random(seed)
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < p]
    return qe.masks_from_edges(n, edges)


def _pathwidth_brute(masks):
    """Vertex separation by exhaustive subset DP (n <= 9)."""
    n = len(masks)
    full = (1 << n) - 1
    best = {0: 0}
    for size in range(1, n + 1):
        nxt = {}
        for S, w in best.items():
            for v in range(n):
                if S >> v & 1:
                    continue
                T = S | (1 << v)
                boundary = 0
                rest = T
                while rest:
                    u = (rest & -rest).bit_length() - 1
                    rest &= rest - 1
                    boundary |= masks[u] & ~T
                cost = max(w, bin(boundary).count("1"))
                if T not in nxt or cost < nxt[T]:
                    nxt[T] = cost
        best = nxt
    return best[full]


# -- the graph --------------------------------------------------------------------


def test_masks_from_matrix_is_a_clique_per_pattern():
    matrix = np.array([[1, 1, 0], [1, 0, 1], [0, 1, 1], [0, 0, 1]])
    masks, sizes = qe.masks_from_matrix(matrix)
    assert sizes == [2, 2, 3]
    assert masks == [0b0110, 0b1101, 0b1011, 0b0110]
    assert qe.edge_count(masks) == 5
    assert qe.degree_sequence(masks) == [2, 3, 3, 2]


# -- the floor --------------------------------------------------------------------


def test_cover_floor_matches_first_moment_floors():
    sizes = [2, 3, 3, 4, 2, 5, 3, 3, 4, 2, 2, 3, 6, 3, 2, 4, 3, 2, 3, 3]
    n = 20
    assert qe.cover_floor(n, sizes, 1.0) == floors(n, sizes)[0] - 1
    assert qe.cover_floor(n, sizes, 0.01) == floors(n, sizes)[1] - 1


def test_gnp_floor_matches_random_graph_classes():
    for n, p in ((30, 0.5), (40, 0.2), (60, 0.1), (25, 0.9)):
        ref = gnp_floors(n, p, levels=(1.0, 0.05))
        assert qe.gnp_floor(n, p, 1.0) == ref[1.0]
        assert qe.gnp_floor(n, p, 0.05) == ref[0.05]


def test_floor_level_monotone():
    sizes = [3] * 40
    assert qe.cover_floor(40, sizes, 0.01) <= qe.cover_floor(40, sizes, 0.05) <= qe.cover_floor(40, sizes, 1.0)
    assert qe.gnp_floor(40, 0.3, 0.01) <= qe.gnp_floor(40, 0.3, 0.05) <= qe.gnp_floor(40, 0.3, 1.0)


# -- the ceiling ------------------------------------------------------------------


def test_random_ordering_width_is_the_max_of_the_binomial_means():
    n, p = 30, 0.2
    means = [(n - t) * (1 - (1 - p) ** t) for t in range(n + 1)]
    assert qe.random_ordering_width(n, p) == pytest.approx(max(means))
    assert qe.random_ordering_width(n, 0.0) == 0.0
    assert qe.random_ordering_width(1, 0.5) == 0.0


def test_random_ordering_width_reproduces_beta_typ():
    # reports/random_ordering_bound.md: beta_typ(c) = 0.4227, 0.5858, 0.6936 at c = 3, 6, 10
    n = 20000
    for c, beta in ((3, 0.4227), (6, 0.5858), (10, 0.6936)):
        assert qe.random_ordering_width(n, c / n) / n == pytest.approx(beta, abs=2e-3)


def test_n_minus_greedy_alpha_is_an_upper_bound_on_pathwidth():
    for seed in range(40):
        n = 7 + seed % 3
        masks = _random_masks(n, 0.35, seed)
        assert n - qe.greedy_alpha(masks) >= _pathwidth_brute(masks)


def test_greedy_alpha_on_known_graphs():
    assert qe.greedy_alpha([0] * 5) == 5                       # empty graph
    full = [((1 << 5) - 1) & ~(1 << v) for v in range(5)]
    assert qe.greedy_alpha(full) == 1                          # K5
    path = qe.masks_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4)])
    assert qe.greedy_alpha(path) == 3


def test_em_histogram_term():
    assert qe.em_histogram_term([1, 2, 2]) == 0.0
    assert qe.em_histogram_term([3, 3, 3, 3]) == pytest.approx(4 / 6)


# -- the point estimates ----------------------------------------------------------


def test_min_fill_treewidth_is_at_least_pathwidth_free_check_on_trees_and_cliques():
    path = qe.masks_from_edges(6, [(i, i + 1) for i in range(5)])
    assert qe.min_fill_treewidth(path) == 1
    full = [((1 << 6) - 1) & ~(1 << v) for v in range(6)]
    assert qe.min_fill_treewidth(full) == 5
    assert qe.min_fill_treewidth([0, 0, 0]) == 0


def test_block_estimate_reproduces_dense_staircase_table():
    # reports/dense_staircase.md section 4, p = 1/2: block threshold 12, 13, 14, 15 at n = 30..60,
    # the median n - pw plus one, so the estimate n - s + 1 is the median pathwidth 19, 28, 37, 46
    for n, median_pw in ((30, 19), (40, 28), (50, 37), (60, 46)):
        assert qe.block_estimate(n, 0.5) == median_pw
    assert qe.block_estimate(10, 1.0) == 9


# -- the estimators ---------------------------------------------------------------


def _row(floor, ceiling, tw, dense=False, block="", ceiling_em=None):
    return {"floor": floor, "ceiling": ceiling, "tw": tw, "dense": dense, "block": block,
            "ceiling_em": ceiling if ceiling_em is None else ceiling_em}


def test_estimators_clip_and_midpoint():
    e = qe.estimators(_row(5, 12, 8))
    assert e["recipe"] == 8 and e["clip_tw"] == 8 and e["tw_floor"] == 8 and e["midpoint"] == 8 and e["bracket_ok"]
    e = qe.estimators(_row(5, 12, 3))
    assert e["recipe"] == 5 and e["tw_floor"] == 5
    e = qe.estimators(_row(5, 12, 20))
    assert e["recipe"] == 12 and e["tw_floor"] == 20
    e = qe.estimators(_row(10, 4, 7))         # inverted bracket: the midpoint
    assert not e["bracket_ok"] and e["recipe"] == 7 and e["clip_tw"] == 7
    e = qe.estimators(_row(5, 12, 3, dense=True, block=9))
    assert e["recipe"] == 9 and e["block_est"] == 9 and e["clip_tw"] == 5
    e = qe.estimators(_row(5, 12, 8, ceiling_em=6))
    assert e["recipe"] == 8 and e["recipe_em"] == 6


def test_estimate_end_to_end_on_a_small_graph():
    masks = _random_masks(9, 0.5, 3)
    row = qe.estimate(masks)
    truth = _pathwidth_brute(masks)
    assert row["n"] == 9 and row["ceil_alpha"] >= truth and row["ceiling"] >= 0
    assert row["floor"] <= row["floor_level1"]
    assert row["dense"] == (row["p"] >= qe.DENSE_P)
    assert row["t_total"] < 1.0
    for key in qe.FIELDS:
        if key not in ("kind", "group", "subgroup", "name", "truth", "truth_is_upper", "provenance"):
            assert key in row, key


def test_estimate_with_sizes_uses_the_cover_floor():
    matrix = (np.random.RandomState(1).random((20, 20)) < 0.3).astype(np.uint8)
    masks, sizes = qe.masks_from_matrix(matrix)
    row = qe.estimate(masks, sizes)
    assert row["m"] == 20
    assert row["floor"] == qe.cover_floor(20, sizes, qe.LEVEL)


# -- the record readers -----------------------------------------------------------


def test_band_of():
    assert [qe.band_of(n) for n in (5, 20, 21, 40, 41, 60, 61, 100, 101, 125, 126, 3000)] == \
        ["0-20", "0-20", "21-40", "21-40", "41-60", "41-60", "61-100", "61-100", "101-125", "101-125", "126+", "126+"]


def test_generator_of():
    assert qe.generator_of("benchmarks/instances/MOSP_Instances/Chu_Stuckey/x.txt") == "Chu & Stuckey"
    assert qe.generator_of("benchmarks/instances/ChallengeInstances2005/Harvey/wbo_10_10.txt") == "Harvey"
    assert qe.generator_of("benchmarks/instances/MOSP_Instances/SCOOP/x.txt") == "SCOOP"


@pytest.mark.skipif(not qe.GNP_PILOT.exists(), reason="pilot results not on disk")
def test_gnp_jobs_keep_only_proved_widths():
    jobs = qe.gnp_jobs()
    assert jobs and all(not j["truth_is_upper"] for j in jobs)
    assert all(j["provenance"] in ("certified:bound", "certified:minor", "certified:refutation") for j in jobs)


@pytest.mark.skipif(not qe.DATASET.exists(), reason="dataset not on disk")
def test_graph_jobs_flag_solution_records_as_upper_bounds():
    jobs = qe.graph_jobs()
    assert all(not j["group"].startswith("MOSP") for j in jobs)
    assert all(j["n"] <= qe.GRAPH_MAX_N for j in jobs)
    flagged = [j for j in jobs if j["truth_is_upper"]]
    assert flagged and all(j["provenance"] == "solution" for j in flagged)
    assert all(j["provenance"] in qe.CERTIFIED for j in jobs if not j["truth_is_upper"])
