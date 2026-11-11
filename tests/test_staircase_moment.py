"""Staircases in dense random graphs (`learning.staircase_moment`,
`reports/dense_staircase.md`).

The staircase lemma is checked against the subset-DP pathwidth on every labelled
graph at `n <= 5` (the `n = 6` sweep and the `n = 7` samples are in the report's
log); the closed-form moments against enumeration over every labelled graph; the
two brackets on the second-moment ratio against its exact value by enumeration of
the placements; the closed-form block cost against the sum; the limit exponents
against their closed forms and the constant `2 + sqrt 2`."""

import math
from fractions import Fraction

import pytest

from learning.staircase_moment import (A_STAR, block_cost, block_cost_sum, block_floor_log,
                                       block_threshold, brute_moments, check_lemma,
                                       empty_pair_log, exact_ratio_small, exponent_block,
                                       exponent_overlap, first_moment_exact, has_staircase,
                                       log_block_moment, log_first_moment, pathwidth_exact,
                                       ratio_log_lower, ratio_log_upper, staircase_threshold,
                                       worst_overlap)


@pytest.mark.parametrize("n", [2, 3, 4, 5])
def test_lemma_on_every_labelled_graph(n):
    out = check_lemma(n)
    assert out["graphs"] == 2 ** (n * (n - 1) // 2)
    assert out["violations"] == 0


def test_lemma_small_cases():
    # the empty graph on 4 vertices: pw = 0 = n - 4, a staircase of size 4 (strict needs 6 vertices)
    assert pathwidth_exact([0, 0, 0, 0], 4) == 0
    assert has_staircase([0, 0, 0, 0], 4, 4, generalised=True)
    assert not has_staircase([0, 0, 0, 0], 4, 4, generalised=False)
    assert has_staircase([0, 0, 0, 0], 4, 3, generalised=False)
    # K4: pw = 3, only the trivial staircase of size 1
    k4 = [0b1110, 0b1101, 0b1011, 0b0111]
    assert pathwidth_exact(k4, 4) == 3
    assert has_staircase(k4, 4, 1) and not has_staircase(k4, 4, 2, generalised=True)
    # a path 0-1-2-3: pw = 1 = n - 3
    path = [0b0010, 0b0101, 0b1010, 0b0100]
    assert pathwidth_exact(path, 4) == 1
    assert has_staircase(path, 4, 3, generalised=True) and not has_staircase(path, 4, 4, generalised=True)


@pytest.mark.parametrize("s,a,b", [(s, a, b) for s in range(0, 9) for a in range(0, 9) for b in range(0, 9)])
def test_block_cost_closed_form(s, a, b):
    assert block_cost(s, a, b) == block_cost_sum(s, a, b)


def test_block_cost_is_the_lean_index_count():
    # `blockIndex s a b` in Staircase.lean: pairs (i, j) in Fin b x Fin a with i + j + 1 < s
    for s, a, b in [(7, 4, 4), (5, 4, 2), (6, 5, 5), (3, 1, 1), (4, 3, 3)]:
        assert block_cost(s, a, b) == sum(1 for i in range(b) for j in range(a) if i + j + 1 < s)
    assert block_cost(7, 4, 4) == 15 and block_cost(5, 4, 2) == 7 and block_cost(6, 5, 5) == 15


@pytest.mark.parametrize("n,s", [(4, 2), (5, 2), (5, 3), (6, 3)])
@pytest.mark.parametrize("p", [Fraction(1, 2), Fraction(3, 10)])
def test_moments_against_every_labelled_graph(n, s, p):
    q = 1 - p
    e1, e2 = brute_moments(n, p, s)
    assert e1 == first_moment_exact(n, q, s)
    assert e2 / e1 ** 2 == exact_ratio_small(n, q, s)
    assert math.isclose(math.log(float(e1)), log_first_moment(n, float(q), s), rel_tol=1e-9)
    lo, up = ratio_log_lower(n, float(q), s), ratio_log_upper(n, float(q), s)
    r = math.log(float(e2 / e1 ** 2))
    assert lo - 1e-9 <= r <= up + 1e-9


def test_brackets_at_n7():
    for s in (2, 3, 4):
        for q in (Fraction(1, 2), Fraction(7, 10)):
            r = math.log(float(exact_ratio_small(7, q, s)))
            assert ratio_log_lower(7, float(q), s) - 1e-9 <= r <= ratio_log_upper(7, float(q), s) + 1e-9


def test_block_family_contains_the_empty_pair():
    for n, k in ((30, 17), (60, 43), (100, 70), (45, 20)):
        s, t = n - k, (n - k + 1) // 2
        assert math.isclose(empty_pair_log(n, 0.5, k), log_block_moment(n, 0.5, s, t, t - 1), abs_tol=1e-9)
        assert block_floor_log(n, 0.5, s)[0] <= empty_pair_log(n, 0.5, k) + 1e-9


def test_limit_exponents():
    assert math.isclose(A_STAR, 2 + math.sqrt(2))
    for a in (2.0, 2.5, 3.0, 3.3, 3.5, 3.9):
        # the worst overlap and the best block are the same number with opposite signs
        val = a * a / 2 - 2 * a + 1
        if a >= 2:
            assert math.isclose(exponent_overlap(a, 2 * a - 2), val, abs_tol=1e-12)
            assert math.isclose(exponent_block(a, a - 1), -val, abs_tol=1e-12)
        w, x = worst_overlap(a)
        assert (w > 0) == (a > A_STAR)
    assert abs(worst_overlap(A_STAR)[0]) < 1e-3
    # the whole staircase is the (a, a) block: exponent 2a - a^2/2, zero at a = 4
    assert math.isclose(exponent_block(4.0, 4.0), 0.0, abs_tol=1e-12)
    assert math.isclose(exponent_block(2.0, 1.0), 1.0, abs_tol=1e-12)  # the empty pair at a = 2


def test_thresholds_scale():
    # the block threshold sits near (2 + sqrt 2) L and the staircase one near 4 L
    for n in (10 ** 4, 10 ** 6):
        L = math.log2(n)
        assert 3.3 * L <= block_threshold(n, 0.5, symmetric=False) <= 3.5 * L
        assert 3.9 * L <= staircase_threshold(n, 0.5) <= 4.05 * L


def test_ratio_brackets_split_at_a_star():
    q = 0.5
    for n in (10 ** 5, 10 ** 6):
        L = math.log2(n)
        assert ratio_log_lower(n, q, round(3.0 * L)) < 0.0    # tends to 1 from below
        assert ratio_log_lower(n, q, round(3.9 * L)) > 100.0  # exponential in log^2 n


@pytest.mark.parametrize("n", [3, 4, 5])
def test_strict_staircase_is_bandwidth(n):
    from learning.staircase_moment import check_bandwidth_lemma
    assert check_bandwidth_lemma(n)["violations"] == 0
