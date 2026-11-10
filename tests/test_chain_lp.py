"""The chain IP/LP of vertex separation and its Lagrangian ceiling (`learning.chain_lp`)."""
import itertools

import numpy as np
import pytest

from learning.chain_lp import (ChainModel, _all_layouts_satisfy, adjacency_from_graph, bb_levels, boundary_of,
                               floors_from_levels,
                               harper_profile_exact, harper_profile_floor, lagrangian_exact, layout_point,
                               maximal_cliques, mixture_lp, mixture_upper, point_satisfies, profile_of,
                               greedy_layouts, improve_layout, solve_ip, solve_lp, vertex_separation_of,
                               weighted_layout)
from learning.obstruction_ledger import adjacency_from_edges

GRAPHS = {
    "P5": (5, [(0, 1), (1, 2), (2, 3), (3, 4)]),
    "C5": (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    "K4": (4, [(a, b) for a in range(4) for b in range(a + 1, 4)]),
    "K23": (5, [(a, b) for a in range(2) for b in range(2, 5)]),
    "star+tri": (6, [(0, 1), (0, 2), (0, 3), (3, 4), (4, 5), (3, 5)]),
    "pet7": (7, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 3), (1, 4), (2, 5)]),
    "two+iso": (5, [(0, 1), (2, 3)]),
}


def _adj(name):
    n, E = GRAPHS[name]
    return adjacency_from_edges(n, E)


def _vs_brute(adj):
    n = len(adj)
    return min(vertex_separation_of(adj, list(o)) for o in itertools.permutations(range(n)))


def _all_cuts(adj):
    return {"harper": harper_profile_exact(adj), "persist": True, "upper": True, "clique": maximal_cliques(adj)}


@pytest.mark.parametrize("name", list(GRAPHS))
def test_ip_is_vertex_separation(name):
    adj = _adj(name)
    vs = _vs_brute(adj)
    assert round(solve_ip(adj)["value"]) == vs
    assert round(solve_ip(adj, _all_cuts(adj))["value"]) == vs


@pytest.mark.parametrize("name", list(GRAPHS))
def test_lp_without_cuts_is_zero_and_with_cuts_is_harper(name):
    adj = _adj(name)
    phi = harper_profile_exact(adj)
    assert abs(solve_lp(adj)["value"]) < 1e-7
    assert abs(solve_lp(adj, {"harper": phi})["value"] - max(phi)) < 1e-6
    assert abs(solve_lp(adj, _all_cuts(adj))["value"] - max(phi)) < 1e-6


def test_uniform_point_is_feasible_for_every_formulation():
    """The two-line proof, checked: y = t/n, s = Φ(t)/n, b = max Φ satisfies every row."""
    for name in GRAPHS:
        adj = _adj(name)
        n = len(adj)
        phi = harper_profile_exact(adj)
        model = ChainModel(adj, relax=True, cuts=_all_cuts(adj))
        y = np.array([[t / n] * n for t in range(1, n)])
        s = np.array([[phi[t] / n] * n for t in range(1, n)])
        assert point_satisfies(model, y, s, float(max(phi)))


@pytest.mark.parametrize("name", [k for k, (n, _) in GRAPHS.items() if n <= 6])
def test_every_layout_satisfies_every_cut(name):
    adj = _adj(name)
    assert _all_layouts_satisfy(adj, _all_cuts(adj))


def test_layout_point_matches_profile():
    adj = _adj("pet7")
    order = [3, 0, 1, 4, 2, 5, 6]
    y, s = layout_point(adj, order)
    assert list(s.sum(axis=1).astype(int)) == profile_of(adj, order)
    assert list(y.sum(axis=1).astype(int)) == list(range(1, 7))


def test_harper_profile_exact_against_brute_force():
    adj = _adj("star+tri")
    n = len(adj)
    phi = harper_profile_exact(adj)
    for t in range(n + 1):
        best = min(boundary_of(adj, S) for S in range(1 << n) if bin(S).count("1") == t)
        assert phi[t] == best


@pytest.mark.parametrize("name", list(GRAPHS))
def test_harper_floor_is_below_the_exact_profile_and_reaches_its_max(name):
    adj = _adj(name)
    phi = harper_profile_exact(adj)
    floors, info = harper_profile_floor(adj, cap=12, budget=None)
    assert all(f <= p for f, p in zip(floors, phi))
    assert max(floors) == max(phi)


def test_weighted_layout_against_enumeration():
    adj = _adj("pet7")
    n = len(adj)
    rng = np.random.default_rng(3)
    for _ in range(5):
        mu = np.zeros(n + 1)
        mu[1:n] = rng.random(n - 1)
        v, order = weighted_layout(adj, mu)
        brute = min(sum(m * b for m, b in zip(mu[1:n], profile_of(adj, list(o))))
                    for o in itertools.permutations(range(n)))
        assert abs(v - brute) < 1e-9
        assert abs(sum(m * b for m, b in zip(mu[1:n], profile_of(adj, order))) - v) < 1e-9


@pytest.mark.parametrize("name", list(GRAPHS))
def test_lagrangian_between_harper_and_vs(name):
    adj = _adj(name)
    r = lagrangian_exact(adj)
    assert r["vs"] == _vs_brute(adj)
    assert r["harper"] - 1e-9 <= r["L"] <= r["vs"] + 1e-9
    assert abs(r["L"] - r["lower"]) < 1e-6


def test_lagrangian_exceeds_harper_on_star_plus_triangle():
    """Harper 1, vs 2, L = 1.4: the ceiling of the route rounds up to vs here."""
    r = lagrangian_exact(_adj("star+tri"))
    assert r["harper"] == 1 and r["vs"] == 2
    assert abs(r["L"] - 1.4) < 1e-6


def test_lagrangian_by_brute_force_minimax():
    """L = min over mixtures of all layouts of max_t: the LP over every profile."""
    adj = _adj("star+tri")
    n = len(adj)
    profiles = [profile_of(adj, list(o)) for o in itertools.permutations(range(n))]
    z, lam, mu = mixture_lp(profiles)
    assert abs(z - lagrangian_exact(adj)["L"]) < 1e-6


def test_mixture_upper_bounds_L_and_pool_helpers():
    adj = _adj("pet7")
    pool = greedy_layouts(adj, count=10, seed=0)
    assert all(sorted(o) == list(range(7)) for o in pool)
    imp = improve_layout(adj, pool[0])
    assert sorted(imp) == list(range(7))
    assert vertex_separation_of(adj, imp) <= vertex_separation_of(adj, pool[0])
    up = mixture_upper(adj, pool + [imp])
    assert up["upper"] >= lagrangian_exact(adj)["L"] - 1e-9


def test_adjacency_from_graph_relabels():
    import networkx as nx

    g = nx.Graph([("b", "c"), ("a", "c")])
    adj = adjacency_from_graph(g)
    assert adj == [0b100, 0b100, 0b011]


def _f_brute(adj, k):
    n = len(adj)
    best = n + 1
    for C in itertools.combinations(range(n), k):
        N = 0
        for v in C:
            N |= adj[v] | (1 << v)
        best = min(best, bin(N).count("1"))
    return best


@pytest.mark.parametrize("name", list(GRAPHS))
def test_floors_from_all_exact_levels_equal_the_exact_profile(name):
    """With f(1..n) exact, i − M(i) is the inner minimum exactly, and the outer
    profile is its complement: the floors equal `harper_profile_exact`."""
    adj = _adj(name)
    n = len(adj)
    levels = [_f_brute(adj, k) for k in range(1, n + 1)]
    assert floors_from_levels(n, levels) == harper_profile_exact(adj)
    # a cap of 2 with the deeper levels merged as "record" floors gives the same
    merged = floors_from_levels(n, levels[:2], {k: levels[k - 1] for k in range(3, n + 1)})
    assert merged == harper_profile_exact(adj)
    # a partial merge never exceeds the exact profile
    partial = floors_from_levels(n, levels[:2], {n - 1: levels[n - 2]})
    assert all(a <= b for a, b in zip(partial, harper_profile_exact(adj)))
    assert bb_levels(adj, cap=12, budget=None) == levels[: min(12, n - 1) + 1]
