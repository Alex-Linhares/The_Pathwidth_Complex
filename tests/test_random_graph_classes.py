"""`learning.random_graph_classes` (2026-11-11): the three pair probabilities
against brute force, the rate against the finite sum, Harper on hypercubes
and grids against the exact pathwidths, and the parsers."""

import itertools
import math

import pytest

from learning.random_graph_classes import (
    beta_star_gnd, beta_star_split, entropy3, gnd_floors, gnd_log_bound, gnd_log_empty_pair, gnd_pair_rate,
    gnd_rate, gnm_log_bound, gnp_log_bound, gnp_pair_rate2, grid_masks, harper_profile, harper_value,
    harvey_family, hypercube_masks, hypercube_pathwidth, regular_bipartite_log_empty_pair,
    rows_fixed_log_empty_pair, simplicial_profile, union_floors)
from learning.separator_moment import beta_star_gnp


def _matchings(points):
    if not points:
        yield []
        return
    a = points[0]
    for i in range(1, len(points)):
        rest = points[1:i] + points[i + 1:]
        for m in _matchings(rest):
            yield [(a, points[i])] + m


def _brute_gnd(n, d, t, r):
    pts = [(v, i) for v in range(n) for i in range(d)]
    A, R = set(range(t)), set(range(t, t + r))
    tot = ok = 0
    for m in _matchings(pts):
        tot += 1
        if all(not ((p[0] in A and q[0] in R) or (p[0] in R and q[0] in A)) for p, q in m):
            ok += 1
    return math.log(ok / tot)


@pytest.mark.parametrize("n,d,t,r", [(5, 2, 2, 1), (6, 2, 2, 2), (4, 3, 2, 1), (4, 3, 1, 1)])
def test_pairing_model_pair_probability_matches_brute_force(n, d, t, r):
    assert gnd_log_empty_pair(n, d, t, r) == pytest.approx(_brute_gnd(n, d, t, r), abs=1e-9)


def _brute_rows(n, m, r, t, tr):
    subsets = list(itertools.combinations(range(m), r))
    tot = ok = 0
    for choice in itertools.product(subsets, repeat=n):
        tot += 1
        qa = set().union(*[set(choice[i]) for i in range(t)])
        qr = set().union(*[set(choice[i]) for i in range(t, t + tr)])
        if not (qa & qr):
            ok += 1
    return math.log(ok / tot)


@pytest.mark.parametrize("n,m,r,t,tr", [(4, 4, 2, 2, 1), (4, 5, 2, 2, 2), (3, 4, 1, 1, 1)])
def test_rows_fixed_pair_probability_matches_brute_force(n, m, r, t, tr):
    assert rows_fixed_log_empty_pair(n, m, r, t, tr) == pytest.approx(_brute_rows(n, m, r, t, tr), abs=1e-9)


def _brute_bip(n, m, r, d, t, tr):
    big_n = n * r
    cust = [c for c in range(n) for _ in range(r)]
    pat = [p for p in range(m) for _ in range(d)]
    A, R = set(range(t)), set(range(t, t + tr))
    tot = ok = 0
    for perm in itertools.permutations(range(big_n)):
        tot += 1
        owners = [set() for _ in range(m)]
        for h, slot in enumerate(perm):
            owners[pat[slot]].add(cust[h])
        if all(not (o & A and o & R) for o in owners):
            ok += 1
    return math.log(ok / tot)


@pytest.mark.parametrize("n,m,r,d,t,tr", [(3, 3, 2, 2, 1, 1), (4, 2, 1, 2, 1, 1), (4, 4, 2, 2, 2, 1)])
def test_regular_bipartite_pair_probability_matches_brute_force(n, m, r, d, t, tr):
    assert regular_bipartite_log_empty_pair(n, m, r, d, t, tr) == pytest.approx(_brute_bip(n, m, r, d, t, tr), abs=1e-9)


def test_regular_bipartite_rejects_unbalanced_margins():
    assert regular_bipartite_log_empty_pair(4, 3, 2, 2, 1, 1) == -math.inf


@pytest.mark.parametrize("a", [0.1, 0.3, 0.45])
def test_pairing_rate_matches_the_finite_sum(a):
    n = 400
    finite = gnd_log_empty_pair(n, 3, int(a * n), int(a * n)) / n
    assert gnd_rate(3, a) == pytest.approx(finite, abs=5e-3)


def test_pairing_rate_free_split_reduces_to_balanced():
    assert gnd_rate(3, 0.3) == pytest.approx(gnd_rate(3, 0.3, 0.3), abs=1e-12)


def test_beta_star_cubic_is_near_kolesnik_wormald():
    # Kolesnik & Wormald 2014, Table 2: A_3(1/2) = 0.14420, i.e. pw >= 0.0721 n
    # at the balanced prefix; the balanced empty pair gives 0.070.
    b = beta_star_gnd(3)
    assert 0.065 < b < 0.075


def test_pair_rate_is_entropy_plus_rate():
    assert gnd_pair_rate(3, 0.3) == pytest.approx(entropy3(0.3, 0.3) + gnd_rate(3, 0.3))


def test_gnp_free_split_is_balanced():
    # on G(n, c/n) the best split of the empty pair is the balanced one
    c = 6.0
    free, a = beta_star_split(lambda a, r: gnp_pair_rate2(c, a, r))
    assert free == pytest.approx(beta_star_gnp(c), abs=2e-3)
    assert a / (1 - free) == pytest.approx(0.5, abs=1e-2)


def test_gnm_bound_is_below_and_near_the_gnp_bound():
    # sampling without replacement: C(M - F, m) / C(M, m) <= (1 - F/M)^m
    n, m = 60, 60
    p = m / (n * (n - 1) / 2)
    for k in (30, 40, 50):
        assert gnm_log_bound(n, m, k) <= gnp_log_bound(n, p, k) + 1e-9
        assert gnp_log_bound(n, p, k) - gnm_log_bound(n, m, k) < 2.0


def test_floors_are_monotone_in_the_level():
    fl = gnd_floors(60, 3)
    assert fl[1.0] >= fl[0.05] >= fl[0.01] >= 0
    assert gnd_log_bound(60, 3, 5, simple=True) == gnd_log_bound(60, 3, 5) + 2.0


def test_union_floors_handles_no_level():
    assert union_floors(5, lambda k: 0.0)[1.0] == 0


@pytest.mark.parametrize("d,expected", [(1, 1), (2, 2), (3, 4), (4, 7), (5, 13), (6, 23)])
def test_hypercube_pathwidth_formula(d, expected):
    assert hypercube_pathwidth(d) == expected


@pytest.mark.parametrize("d", [2, 3, 4, 5, 6])
def test_simplicial_order_attains_the_hypercube_pathwidth(d):
    assert max(simplicial_profile(d)) == hypercube_pathwidth(d)


def test_harper_branch_and_bound_is_exact_on_q4():
    prof = harper_profile(hypercube_masks(4), 16, budget=None)
    assert harper_value(prof) == 7
    assert prof == simplicial_profile(4)[: len(prof)] or harper_value(prof) == max(simplicial_profile(4))


@pytest.mark.parametrize("h,w", [(2, 2), (3, 3), (3, 4), (4, 4)])
def test_harper_is_exact_on_small_grids(h, w):
    n = h * w
    prof = harper_profile(grid_masks(h, w), n, budget=None)
    assert harper_value(prof) == min(h, w)


def test_harvey_family_parser():
    assert harvey_family("Warwick 1: balanced orders, 2 orders per product") == ("wbo", 2)
    assert harvey_family("Warwick 1000: balanced orders and products, 3 products per order") == ("wbop", 3)
    assert harvey_family("Warwick 5: balanced products, 4 products per order") == ("wbp", 4)


def test_bipartite_constant_is_near_the_gnp_constant_at_the_same_mean_degree():
    from learning.random_graph_classes import beta_star_bipartite, bipartite_pair_rate
    # the degenerate split (A and R on one side) has probability one and entropy > 0
    assert bipartite_pair_rate(6.0, 0.2, 0.0, 0.2, 0.0) > 0
    assert beta_star_bipartite(6.0, step=4e-3) == pytest.approx(beta_star_gnp(6.0), abs=6e-3)
