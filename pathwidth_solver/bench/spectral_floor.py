"""The spectral floor of a graph, for the C program's `-L`.

`pathwidth_solver/cli/pathwidth` computes its own floor in C (degeneracy and
contraction degeneracy) and takes `-L k` as a proved lower bound to start the
descent from. The spectral prefix-separator bound of `learning.spectral_bound`
(Mohar & Poljak; Helmberg, Mohar, Poljak & Rendl 1995 eq. (20); Gu & Liu 2022;
Theorem 4 of the module docstring) needs eigenvalues, which stay out of the C:
this helper computes it here and hands it over.

    python3 bench/spectral_floor.py GRAPH [GRAPH ...]     # one line per graph: name n m floor family seconds
    python3 bench/spectral_floor.py --graph6 < graphs.g6  # the same from graph6 on stdin
    python3 bench/spectral_floor.py GRAPH --run [-- extra C options]
                                                           # ./cli/pathwidth -L <floor> <extra> on the graph, output echoed

`GRAPH` is any file `bench/readers.py` reads (`.dgf`, `.gr`, `.graphml`,
VSPLIB). The value is in **pathwidth units** (vertex separation), the unit of
`-L`. The three families (`graph`, the degeneracy `peel`, the contraction
`minor`s) run on graphs to `--families-max` vertices (default 400), the whole
graph alone above; `--budget` seconds cut the peel and minor sequences short
(what was seen is still a bound). The C program's `-L` is trusted by it: pass
only what this helper prints, and never a value from a different graph (the
helper writes the graph it computed on as the graph6 the C reads, with
`networkx`'s relabelling to `0..n-1`, so `-L` and the input agree).

The bound is a theorem of the cited papers checked on every graph to 9
vertices and on every certified instance (`reports/spectral_bound.md`); it is
not formalised in Lean (`paper1/todo.md`).
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CLI = HERE.parent / "cli" / "pathwidth"
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))

FAMILIES_MAX = 400


def spectral_floor(G, families_max: int = FAMILIES_MAX, budget: float | None = 60.0) -> tuple[int, str]:
    """`(floor, family)` in pathwidth units: the best spectral family on `G`
    (components taken separately inside), and which family attained it."""
    from learning.spectral_bound import FAMILIES, spectral_bounds

    families = FAMILIES if G.number_of_nodes() <= families_max else ("graph",)
    deadline = None if budget is None else time.monotonic() + budget
    res = spectral_bounds(G, families=families, deadline=deadline)
    best = res["best"]
    family = next(f for f in ("graph", "peel", "minor") if f in res and res[f] == best)
    return int(best), family


def graph6_of(G) -> str:
    import networkx as nx

    H = nx.convert_node_labels_to_integers(G, ordering="sorted")
    return nx.to_graph6_bytes(H, header=False).decode().strip()


def run_cli(G, floor: int, extra: list[str], cli: Path = CLI) -> str:
    """`./cli/pathwidth -L floor extra...` on `G` (as graph6 on stdin); the
    program's stdout. The layout the C prints (with `-l`) is in the relabelled
    `0..n-1` order, `sorted(G.nodes)`."""
    if not cli.exists():
        raise FileNotFoundError(f"{cli} not built (make in pathwidth_solver/cli)")
    proc = subprocess.run([str(cli), "-L", str(floor), *extra], input=graph6_of(G) + "\n",
                          capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"pathwidth exited {proc.returncode}: {proc.stderr.strip()}")
    return proc.stdout


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("graphs", nargs="*", help="graph files (bench/readers.py formats)")
    ap.add_argument("--graph6", action="store_true", help="read graph6 lines from stdin instead")
    ap.add_argument("--families-max", type=int, default=FAMILIES_MAX)
    ap.add_argument("--budget", type=float, default=60.0, help="seconds for the peel and minor families")
    ap.add_argument("--run", action="store_true", help="run cli/pathwidth -L <floor> on each graph")
    ap.add_argument("extra", nargs="*", help="options after `--` go to cli/pathwidth")
    args, extra = ap.parse_known_args(argv)
    extra = [e for e in extra if e != "--"]
    import networkx as nx
    from readers import read_any

    inputs = []
    if args.graph6:
        for line in sys.stdin:
            line = line.strip()
            if line:
                inputs.append((line[:24], nx.from_graph6_bytes(line.encode())))
    for g in args.graphs:
        inputs.append((g, read_any(Path(g))))
    if not inputs:
        ap.error("no graphs given")
    for name, G in inputs:
        t = time.monotonic()
        floor, family = spectral_floor(G, args.families_max, args.budget)
        print(f"{name} n={G.number_of_nodes()} m={G.number_of_edges()} spectral_floor={floor} "
              f"family={family} seconds={time.monotonic() - t:.2f}", flush=True)
        if args.run:
            sys.stdout.write(run_cli(G, floor, extra))
            sys.stdout.flush()
    return 0


if __name__ == "__main__":
    sys.exit(main())
