"""The first and second moment of narrow layouts (`learning.layout_moment`,
`reports/layout_second_moment.md`).

The chain `q(n, p, w)` is checked against brute force over every labelled graph
(no chain, no exchangeability: the subset DP counts the narrow orderings of each
graph), the enumeration tables against the labelled tables, the C chain against
the exact rational one, the Jensen bound against the exact second-moment ratio,
and the Lean definition `chainQ` (`LayoutMoment.lean`) against the Python chain on
the values `lake env lean` printed."""

import math
from fractions import Fraction

import pytest

from learning.layout_moment import (SCRATCH, beta1, chain_log_q, chain_q_exact, enum_tables,
                                    jensen_log_ratio, labelled_tables, moments_from_tables,
                                    narrow_counts, typical_width, typical_width_limit)

PS = (Fraction(1, 2), Fraction(3, 10), Fraction(1, 7))


@pytest.mark.parametrize("n", [3, 4, 5, 6])
def test_chain_equals_brute_force_over_every_labelled_graph(n):
    T1, T2 = labelled_tables(n)
    assert sum(int(x) for x in T1[:, n - 1]) == math.factorial(n) * 2 ** (n * (n - 1) // 2)
    for w in range(n):
        for p in PS:
            e1, _ = moments_from_tables(T1, T2, p, w)
            assert e1 == math.factorial(n) * chain_q_exact(n, p, w)


def test_narrow_counts_small_cases():
    # a path 0-1-2: every ordering has width <= 1 except none exceed 2; width 0 needs no edges
    adj = [0b010, 0b101, 0b010]
    assert narrow_counts(adj, 3) == [0, 4, 6]
    assert narrow_counts([0, 0, 0], 3) == [6, 6, 6]
    # the triangle: every prefix of size 1 or 2 has 2 or 1 open vertices
    assert narrow_counts([0b110, 0b101, 0b011], 3) == [0, 0, 6]


@pytest.mark.parametrize("n", [4, 5, 6, 7])
def test_c_chain_matches_exact_chain(n):
    for w in range(n):
        for p in (0.5, 0.3, 1 / 7, 2 / n):
            exact = chain_q_exact(n, Fraction(p).limit_denominator(10 ** 9), w)
            assert math.isclose(math.exp(chain_log_q(n, float(Fraction(p).limit_denominator(10 ** 9)), w)),
                                float(exact), rel_tol=1e-10, abs_tol=1e-300)


@pytest.mark.parametrize("n", [7, 8, 9, 10])
def test_enumeration_tables_agree_with_the_chain(n):
    if not (list(SCRATCH.glob(f"enum_n{n}.csv")) or list(SCRATCH.glob(f"enum_n{n}_part*.csv"))):
        pytest.skip("enumeration table not present")
    T1, T2 = enum_tables(n)
    assert sum(int(x) for x in T1[:, n - 1]) == math.factorial(n) * 2 ** (n * (n - 1) // 2)
    for w in range(n):
        for p in PS:
            e1, e2 = moments_from_tables(T1, T2, p, w)
            assert e1 == math.factorial(n) * chain_q_exact(n, p, w)
            assert e2 >= e1 ** 2 / math.factorial(n)   # X <= n! so E[X^2] >= E[X]^2 / n! trivially


def test_labelled_tables_equal_enumeration_tables_at_six():
    if not list(SCRATCH.glob("enum_n6.csv")):
        pytest.skip("enumeration table not present")
    T1, T2 = labelled_tables(6)
    E1, E2 = enum_tables(6)
    assert (T1 == E1).all() and (T2 == E2).all()


def test_jensen_bound_is_below_the_exact_ratio():
    if not list(SCRATCH.glob("enum_n8.csv")):
        pytest.skip("enumeration table not present")
    T1, T2 = enum_tables(8)
    for p in (0.5, 3 / 8, 6 / 8):
        for w in range(7):
            e1, e2 = moments_from_tables(T1, T2, p, w)
            exact = math.log(float(e2)) - 2 * math.log(float(e1))
            assert jensen_log_ratio(8, p, w)["log_ratio_bound"] <= exact + 1e-9


def test_jensen_bound_at_width_zero_is_one_over_prob_empty():
    # X_0 = n! 1[G empty]: E[X^2]/E[X]^2 = 1/P(empty) = (1-p)^(-C), and the Jensen bound is exact there
    n, p = 12, 0.3
    r = jensen_log_ratio(n, p, 0)
    C = n * (n - 1) // 2
    assert math.isclose(r["log_ratio_bound"], -C * math.log1p(-p), rel_tol=1e-9)
    assert math.isclose(r["log_q"], C * math.log1p(-p), rel_tol=1e-9)


def test_beta1_and_typical_width():
    w, b = beta1(60, 10 / 60)
    assert w == 8 and b == pytest.approx(8 / 60)          # beta1.log: c = 10, n = 60
    w, b = beta1(60, 3 / 60)
    assert w == 0                                          # E[X_0] >= 1 at c = 3, n = 60
    t, v = typical_width(60, 10 / 60)
    assert v / 60 == pytest.approx(0.7103, abs=1e-4)
    x, v = typical_width_limit(10)
    assert v == pytest.approx(0.6936, abs=1e-4) and x == pytest.approx(0.218, abs=1e-3)


def test_lean_chain_values():
    # lake env lean reports/scratch/layout_second_moment/lean_check.lean, four of its values
    assert chain_q_exact(4, Fraction(1, 2), 1) == Fraction(5, 16)
    assert chain_q_exact(5, Fraction(3, 10), 2) == Fraction(827659, 1000000)
    assert chain_q_exact(6, Fraction(1, 7), 1) == Fraction(7497805824, 13841287201)
    assert chain_q_exact(7, Fraction(1, 2), 3) == Fraction(943, 4096)
