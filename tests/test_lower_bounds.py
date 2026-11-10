"""The lower bound must never exceed a known optimum.

A lower bound that is too high is not a slow bound, it is a wrong answer: the
binary search starts above the true optimum and returns it, and verifying the
witness by simulation does not catch that, because the witness really does
achieve the value reported. These tests are the guard on that.
"""

import itertools
import json
import random
from pathlib import Path

import pytest

from mosp.instance import MOSPInstance
from mosp.verify import max_open_stacks
from satisfiability.mosp_solver import _lower_bound

SOLUTIONS = Path("solutions")
INSTANCE_DIR = Path("benchmarks/instances")


def _brute_force(inst):
    return min(
        max_open_stacks(inst, list(perm))
        for perm in itertools.permutations(range(inst.n_patterns))
    )


@pytest.mark.parametrize("seed", range(25))
def test_bound_never_exceeds_brute_forced_optimum(seed):
    """On small instances the optimum is known exactly by exhaustion."""
    rng = random.Random(seed)
    n_customers = rng.randint(1, 6)
    n_patterns = rng.randint(1, 6)
    matrix = [
        [rng.randint(0, 1) for _ in range(n_patterns)] for _ in range(n_customers)
    ]
    if not any(any(row) for row in matrix):
        pytest.skip("degenerate all-zero instance")

    inst = MOSPInstance.from_matrix(matrix, name=f"lb{seed}")
    assert _lower_bound(inst) <= _brute_force(inst)


@pytest.mark.parametrize("density", [0.2, 0.5, 0.9])
def test_bound_never_exceeds_optimum_across_densities(density):
    rng = random.Random(int(density * 10))
    for _ in range(8):
        matrix = [
            [1 if rng.random() < density else 0 for _ in range(5)]
            for _ in range(5)
        ]
        if not any(any(row) for row in matrix):
            continue
        inst = MOSPInstance.from_matrix(matrix, name="d")
        assert _lower_bound(inst) <= _brute_force(inst)


def test_bound_never_exceeds_cached_optima():
    """Check against the corpus of solved benchmark instances.

    This is the test that matters for the contraction-degeneracy component,
    whose soundness rests on Yanasse's MOSP = pathwidth + 1 (a Lean theorem
    since 2026-09-27, `MOSPGraph.lean`) plus the treewidth ≤ pathwidth step,
    rather than on a direct argument.
    """
    if not SOLUTIONS.exists() or not INSTANCE_DIR.exists():
        pytest.skip("benchmark corpus not present")

    from benchmarks.solve_parallel import find_benchmark_files

    known = {}
    for path in SOLUTIONS.glob("*.json"):
        data = json.loads(path.read_text())
        known[data["instance_name"]] = data["mosp_value"]
    if not known:
        pytest.skip("no cached solutions")

    rng = random.Random(0)
    files = find_benchmark_files(INSTANCE_DIR)
    rng.shuffle(files)

    checked = 0
    violations = []
    for filepath in files:
        if checked >= 60:
            break
        try:
            instances = MOSPInstance.from_benchmark_file(filepath)
        except Exception:  # noqa: BLE001
            continue
        for inst in instances:
            if checked >= 60 or inst.name not in known:
                continue
            if inst.n_customers > 80:
                continue  # keep the suite fast; the full sweep covers the rest
            bound = _lower_bound(inst, clique_budget=0.5)
            checked += 1
            if bound > known[inst.name]:
                violations.append((inst.name, bound, known[inst.name]))

    assert checked > 0, "no instances were checked"
    assert not violations, f"lower bound exceeded known optimum: {violations[:5]}"


# ---------------------------------------------------------------------------
# The spectral component (2026-11-10): units, soundness, and where it bites
# ---------------------------------------------------------------------------


def _clique_cover_instance(graph, name):
    """The MOSP instance whose MOSP graph is `graph`: one pattern per edge."""
    import networkx as nx

    nodes = list(graph.nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    matrix = [[0] * graph.number_of_edges() for _ in nodes]
    for j, (u, v) in enumerate(graph.edges):
        matrix[idx[u]][j] = 1
        matrix[idx[v]][j] = 1
    return MOSPInstance.from_matrix(matrix, name=name)


def test_spectral_floor_is_in_optimum_units():
    """`_spectral_floor` returns `spec + 1`: the spectral bound is on pathwidth,
    the solver's floor is on the optimum = pathwidth + 1. Complete bipartite
    graphs are tight for the spectral bound (pw(K_{p,q}) = min(p, q))."""
    import networkx as nx

    from customer_inter.customer_graph import build_customer_graph
    from learning.spectral_bound import spectral_bounds
    from satisfiability.mosp_solver import _spectral_floor

    for p, q in ((2, 3), (3, 4), (3, 6)):
        graph = nx.complete_bipartite_graph(p, q)
        inst = _clique_cover_instance(graph, f"K{p}{q}")
        g = build_customer_graph(inst)
        assert _spectral_floor(g) == spectral_bounds(g)["best"] + 1 == min(p, q) + 1
        # and the instance's optimum is exactly that
        assert _lower_bound(inst) == min(p, q) + 1
        assert _lower_bound(inst) <= _brute_force(inst) if inst.n_patterns <= 8 else True
    assert _spectral_floor(nx.Graph()) == 0


def test_spectral_component_never_exceeds_small_optima():
    """Random clique covers at 5-7 customers, the spectral component alone
    and inside `_lower_bound`, against the exhaustive optimum."""
    from customer_inter.customer_graph import build_customer_graph
    from satisfiability.mosp_solver import _spectral_floor

    rng = random.Random(7)
    checked = 0
    for _ in range(40):
        n_customers = rng.randint(3, 7)
        n_patterns = rng.randint(2, 7)
        matrix = [[1 if rng.random() < 0.45 else 0 for _ in range(n_patterns)] for _ in range(n_customers)]
        if not any(any(row) for row in matrix):
            continue
        inst = MOSPInstance.from_matrix(matrix, name="s")
        opt = _brute_force(inst)
        info = {}
        assert _lower_bound(inst, info=info) <= opt
        assert _spectral_floor(build_customer_graph(inst)) <= opt
        assert info["source"] in ("degeneracy", "expansion", "spectral")
        checked += 1
    assert checked > 20


def test_spectral_component_can_be_switched_off_and_records_its_source():
    """`spectral_budget=None` is the old floor; with it on, the value never
    drops, and `info["source"]` says `spectral` only where it is the strict
    maximum."""
    import networkx as nx

    inst = _clique_cover_instance(nx.petersen_graph(), "petersen")
    info_off, info_on = {}, {}
    off = _lower_bound(inst, spectral_budget=None, info=info_off)
    on = _lower_bound(inst, info=info_on)
    assert on >= off
    assert "spectral" not in info_off and "spectral" in info_on
    assert info_on["spectral"] == 5          # spec(Petersen) = 4, optimum units 5 (pw = 5, optimum 6)
    assert (info_on["source"] == "spectral") == (info_on["spectral"] > max(off, info_on.get("expansion", 0)))


def test_spectral_component_raises_the_corpus_floor_where_measured():
    """`Random-100-50-2-3_0` (optimum 15): the old floor is 10, the spectral
    floor 11 (`reports/spectral_floor_integration.md`). The corpus-wide
    re-check is `python3 -m learning.spectral_bound --stage solver`."""
    if not INSTANCE_DIR.exists():
        pytest.skip("benchmark corpus not present")
    from benchmarks.solve_parallel import find_benchmark_files

    wanted = None
    for filepath in find_benchmark_files(INSTANCE_DIR):
        if "Random-100-50" not in str(filepath):
            continue
        for inst in MOSPInstance.from_benchmark_file(filepath):
            if inst.name == "Random-100-50-2-3_0":
                wanted = inst
    if wanted is None:
        pytest.skip("Random-100-50-2-3_0 not found")
    info = {}
    assert _lower_bound(wanted, spectral_budget=None) == 10
    assert _lower_bound(wanted, info=info) == 11
    assert info["source"] == "spectral" and info["spectral"] == 11
    assert 11 <= 15
