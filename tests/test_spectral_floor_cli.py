"""`pathwidth_solver/bench/spectral_floor.py`: the spectral floor of a graph in
pathwidth units, handed to the C program as `-L`. The floor must never exceed
the exact pathwidth; with `-L` the program's answer must not change."""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

import networkx as nx
import pytest

from fixed_parameter_algorithm.pathwidth import compute_pathwidth

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "pathwidth_solver" / "bench" / "spectral_floor.py"
CLI = ROOT / "pathwidth_solver" / "cli" / "pathwidth"


def _load():
    sys.path.insert(0, str(ROOT / "pathwidth_solver" / "bench"))
    spec = importlib.util.spec_from_file_location("spectral_floor", HELPER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _pw(g):
    return compute_pathwidth(nx.convert_node_labels_to_integers(g))[0]


@pytest.mark.parametrize("graph,pw", [
    (nx.petersen_graph(), 5),
    (nx.complete_bipartite_graph(3, 4), 3),
    (nx.cycle_graph(8), 2),
    (nx.complete_graph(5), 4),
    (nx.grid_2d_graph(3, 4), 3),
])
def test_floor_never_exceeds_exact_pathwidth(graph, pw):
    mod = _load()
    graph = nx.convert_node_labels_to_integers(graph)
    assert _pw(graph) == pw
    floor, family = mod.spectral_floor(graph)
    assert 0 <= floor <= pw
    assert family in ("graph", "peel", "minor")


def test_random_graphs_floor_at_most_pathwidth():
    mod = _load()
    for seed in range(8):
        g = nx.gnp_random_graph(9, 0.4, seed=seed)
        floor, _ = mod.spectral_floor(g)
        assert floor <= _pw(g)


def test_graph6_round_trip_keeps_the_graph():
    mod = _load()
    g = nx.petersen_graph()
    h = nx.from_graph6_bytes(mod.graph6_of(g).encode())
    assert nx.is_isomorphic(g, h)


@pytest.mark.skipif(not CLI.exists(), reason="cli/pathwidth not built")
def test_cli_with_the_floor_agrees_with_the_cli_without_it():
    mod = _load()
    for g in (nx.petersen_graph(), nx.complete_bipartite_graph(3, 5), nx.circular_ladder_graph(6)):
        floor, _ = mod.spectral_floor(g)
        with_floor = mod.run_cli(g, floor, ["-t", "20"]).split()
        plain = subprocess.run([str(CLI), "-t", "20"], input=mod.graph6_of(g) + "\n",
                               capture_output=True, text=True, check=True).stdout.split()
        assert with_floor[0] == plain[0] == "pathwidth"
        assert int(with_floor[1]) == int(plain[1]) == _pw(g)
        assert floor <= int(with_floor[1])


@pytest.mark.skipif(not CLI.exists(), reason="cli/pathwidth not built")
def test_command_line_on_a_named_instance(tmp_path):
    gr = tmp_path / "petersen.gr"
    g = nx.petersen_graph()
    gr.write_text(f"p tw {g.number_of_nodes()} {g.number_of_edges()}\n"
                  + "".join(f"{u + 1} {v + 1}\n" for u, v in g.edges))
    out = subprocess.run([sys.executable, str(HELPER), str(gr), "--run", "--", "-t", "20"],
                         capture_output=True, text=True, check=True).stdout
    assert "spectral_floor=4" in out
    assert "pathwidth 5" in out
