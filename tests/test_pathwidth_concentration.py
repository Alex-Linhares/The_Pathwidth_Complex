"""The standard deviation of the pathwidth of a random graph
(`learning.pathwidth_concentration`, `reports/pathwidth_concentration.md`).

The Lipschitz lemma on every graph with at most 5 vertices (the 7-vertex sweep is
in the report's log); the second-moment ratio as a sum over partial injections
against the enumerated ratio; the loss lemma on small blocks; the transfer-matrix
generating function of the floored depth against enumeration; the growth-rate
limit; the cell statistics and the growth fit on synthetic data; the tables on
the record where the files are present."""

import math
from fractions import Fraction
from pathlib import Path

import pytest

from learning.pathwidth_concentration import (A_STAR, MIDDLE_CSV, PILOT_CSV, cell_stats, check_lipschitz,
                                    check_loss_lemma, dense_cells, depth_floor, depth_gf,
                                    depth_gf_brute, depth_rate, family_exact_log, family_slack_log,
                                    log_depth_gf,
                                    fit_growth, mcdiarmid_tail, median_shift, middle_cells,
                                    overlap_perm, pilot_cells, ratio_from_injections,
                                    variance_ceiling, window_estimate)
from learning.staircase_moment import block_cost, exact_ratio_small


# --- Part 1 -----------------------------------------------------------------

def test_lipschitz_every_graph_to_five_vertices():
    out = check_lipschitz(5)
    assert out["graphs"] == 1 + 2 + 4 + 11 + 34
    assert out["violations"] == 0
    assert out["deletion_violations"] == 0
    assert out["oracle_disagreements"] == 0
    assert out["diff1"] > 0 and out["diff0"] > 0


def test_mcdiarmid_numbers():
    assert mcdiarmid_tail(100, 10) == pytest.approx(2 * math.exp(-2))
    assert variance_ceiling(64) == 16
    assert median_shift(8) == pytest.approx(math.sqrt(4 * math.log(2)))


# --- Part 2: the overlap sum ------------------------------------------------

@pytest.mark.parametrize("n,s", [(4, 2), (5, 2), (5, 3), (6, 3)])
@pytest.mark.parametrize("q", [Fraction(1, 2), Fraction(1, 3)])
def test_ratio_as_injection_sum_is_exact(n, s, q):
    assert ratio_from_injections(n, q, s) == exact_ratio_small(n, q, s)


@pytest.mark.parametrize("s,a,b", [(4, 3, 3), (5, 3, 3), (5, 4, 4), (6, 4, 4), (6, 4, 3), (7, 5, 4)])
def test_loss_lemma_on_small_blocks(s, a, b):
    out = check_loss_lemma(s, a, b)
    assert out["pairs"] == math.factorial(a) * math.factorial(b)
    assert out["violations"] == 0
    assert out["equality_id_violations"] == 0


def test_overlap_aligned_is_block_cost():
    for s, a, b in [(5, 3, 3), (6, 4, 4), (7, 5, 3)]:
        assert overlap_perm(s, a, b, tuple(range(1, b + 1)), tuple(range(1, a + 1))) == block_cost(s, a, b)


def test_depth_floor_values():
    assert depth_floor((1, 2, 3), 1) == 0
    assert depth_floor((2, 1), 1) == 1
    assert depth_floor((3, 1, 2), 1) == 2
    assert depth_floor((3, 1, 2), 3) == 0      # below the floor nothing is charged
    assert depth_floor((2, 3, 1), 2) == 1


@pytest.mark.parametrize("F", [1, 2, 3])
@pytest.mark.parametrize("x", [0.5, 0.3])
def test_depth_gf_matches_enumeration(F, x):
    for ell in range(1, 7):
        assert depth_gf(ell, F, x) == pytest.approx(depth_gf_brute(ell, F, x), rel=1e-12)


def test_depth_gf_small_closed_forms():
    x = Fraction(1, 3)
    assert depth_gf(2, 1, x, exact=True) == 1 + x
    assert depth_gf(3, 1, x, exact=True) == 1 + 2 * x + 3 * x ** 2
    for ell in range(1, 7):
        assert depth_gf(ell, 1, Fraction(1), exact=True) == math.factorial(ell)


def test_depth_rate_is_the_limit_of_the_finite_ratio():
    x = 0.5
    r = math.log(depth_gf(201, 1, x)) - math.log(depth_gf(200, 1, x))
    assert abs(depth_rate(x) - r) < 2e-3
    assert depth_rate(0.3) < depth_rate(0.5) < depth_rate(0.7)


def test_family_brackets_contain_the_exact_sum():
    for s, a, b in [(6, 4, 4), (7, 5, 5)]:
        for q in (0.5, 0.7):
            ex = family_exact_log(q, s, a, b)
            br = family_slack_log(q, s, a, b)
            assert br["log_slack_lo"] <= ex + 1e-9
            assert ex <= br["log_slack_hi"] + 1e-9


def test_window_estimate_shape():
    w = window_estimate(0.5, Ls=(10, 20))
    assert w["gain_per_step"] == pytest.approx((A_STAR - 2) * math.log(2))
    assert 0 <= w["sigma_lo"] <= w["sigma_hi"]
    assert 1 <= w["window_lo"] <= w["window_hi"]


# --- Cell statistics and fits ----------------------------------------------

def test_cell_stats():
    st = cell_stats([3, 3, 4, 4, 4, 5])
    assert st["N"] == 6 and st["mean"] == pytest.approx(23 / 6)
    assert st["top1"] == pytest.approx(0.5) and st["top2"] == pytest.approx(5 / 6)
    assert st["spread"] == 2 and st["hist"] == {3: 2, 4: 3, 5: 1}


def test_fit_growth_recovers_the_exponent():
    pts = [(n, 0.3 * n ** 0.5, 100) for n in (20, 30, 40, 60, 80)]
    f = fit_growth(pts)
    assert f["gamma"] == pytest.approx(0.5, abs=1e-9)
    assert f["half_within_2se"] and not f["zero_within_2se"]
    pts = [(n, 1.7, 100) for n in (20, 30, 40, 60, 80)]
    assert fit_growth(pts)["gamma"] == pytest.approx(0.0, abs=1e-9)


# --- The record -------------------------------------------------------------

@pytest.mark.skipif(not Path(MIDDLE_CSV).exists(), reason="middle-regime results not present")
def test_dense_cells_on_record():
    rows = dense_cells()
    assert [r["n"] for r in rows] == [30, 40, 50, 60]
    for r in rows:
        assert r["N"] == 20 and r["p"] == 0.5
        assert r["s_star"] - 1 == r["nminus"]["median"] + 1  # the dense report's finite threshold
        assert r["top2"] >= 0.75
    assert len(middle_cells()) == 16


@pytest.mark.skipif(not Path(PILOT_CSV).exists(), reason="pilot results not present")
def test_pilot_cells_on_record():
    rows = pilot_cells()
    assert all(r["N"] >= 10 for r in rows)
    full = [r for r in rows if r["n"] <= 60]
    assert all(r["censored"] == 0 for r in full)
    assert all(r["sd"] <= math.sqrt(r["n"]) / 2 for r in rows)   # below the martingale ceiling


def test_log_depth_gf_matches_depth_gf():
    for ell, F, x in [(5, 1, 0.5), (8, 3, 0.5), (12, 4, 0.7), (30, 10, 0.3)]:
        assert log_depth_gf(ell, F, x) == pytest.approx(math.log(depth_gf(ell, F, x)), rel=1e-9)
