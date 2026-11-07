#!/usr/bin/env python3
"""Recover and re-check the minors behind a tabu run's neighbour refutations.

`minor_tabu` appends one JSON line per neighbour refutation to its claims log
(`-log FILE`, by default `<seed file>.claims.jsonl` when seeded): the level
refuted, the step, the minor's size and the contraction sequence that produces
the minor, in the format of the final certificate.  This script replays each
sequence on the graph (every pair must be an edge of the current graph, as
Theorem thm:tabu-seq says it is), writes the minor as graph6, and, with
`--check`, re-proves its pathwidth with the C program and compares it with the
claimed level: a `floor` claim at level L says pathwidth(minor) >= L, a
`target` claim says >= L too and closes the class.  Nothing here shares code
with the search.

    python -m pathwidth_solver.bench.minor_tabu_claims reports/scratch/minor_tabu/pwc-17436.seed.claims.jsonl \
        --instance reports/scratch/obstruction_search/13_pass1/certificates_2/pwc-17436/instance.txt --check --best
"""
from __future__ import annotations

import argparse
import collections
import json
import subprocess
import sys
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parents[2]
CLI = ROOT / "pathwidth_solver" / "cli" / "pathwidth"


def read_instance(path: Path) -> nx.Graph:
    lines = path.read_text().split("\n")
    n = int(lines[0].split()[0])
    G = nx.Graph(); G.add_nodes_from(range(n))
    for line in lines[1:]:
        p = line.split()
        if len(p) == 2:
            G.add_edge(int(p[0]), int(p[1]))
    return G


def replay(G: nx.Graph, sequence) -> nx.Graph:
    H = G.copy()
    for a, b in sequence:
        if not H.has_edge(a, b):
            raise ValueError(f"({a},{b}) is not an edge of the current minor")
        H = nx.contracted_nodes(H, b, a, self_loops=False)
    return H


def prove(H: nx.Graph, seconds: float) -> tuple[int | None, str]:
    g6 = nx.to_graph6_bytes(nx.convert_node_labels_to_integers(H), header=False)
    out = subprocess.run([str(CLI), "-t", str(seconds)], input=g6, capture_output=True).stdout.decode().split()
    if len(out) >= 3 and out[0] == "pathwidth":
        return int(out[1]), out[2]
    return None, " ".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("claims", type=Path)
    ap.add_argument("--instance", type=Path, required=True, help="the graph as `n m` then edge lines (certificates_2/<id>/instance.txt)")
    ap.add_argument("--check", action="store_true", help="re-prove each selected minor's pathwidth with the C program")
    ap.add_argument("--best", action="store_true", help="only the highest level claimed, one minor per size")
    ap.add_argument("--seconds", type=float, default=120.0)
    ap.add_argument("--out", type=Path, default=None, help="write the selected minors as graph6, one per line, with a JSON header line each")
    a = ap.parse_args()
    G = read_instance(a.instance)
    claims = [json.loads(line) for line in open(a.claims) if line.strip()]
    tally = collections.Counter((c["kind"], c["level"], c["minor_vertices"]) for c in claims)
    print(f"{len(claims)} claims on {a.instance.name}: " + ", ".join(f"{k} level {l} at {v} vertices x{c}" for (k, l, v), c in sorted(tally.items(), key=lambda t: (-t[0][1], t[0][2]))[:12]))
    chosen = claims
    if a.best:
        top = max(c["level"] for c in claims)
        seen = set(); chosen = []
        for c in claims:
            if c["level"] == top and c["minor_vertices"] not in seen:
                seen.add(c["minor_vertices"]); chosen.append(c)
    fh = open(a.out, "w") if a.out else None
    bad = 0
    for c in chosen:
        H = replay(G, c["sequence"])
        assert H.number_of_nodes() == c["minor_vertices"], (H.number_of_nodes(), c["minor_vertices"])
        line = f"step {c['step']:>7} {c['kind']:6} level {c['level']:>3} minor {H.number_of_nodes():>4} v {H.number_of_edges():>5} e"
        if a.check:
            pw, how = prove(H, a.seconds)
            ok = pw is not None and pw >= c["level"]
            bad += not ok
            line += f"  -> C program: pathwidth {pw} ({how}) {'agrees' if ok else 'DISAGREES'}"
        print(line, flush=True)
        if fh:
            fh.write(json.dumps({k: c[k] for k in ("step", "kind", "level", "minor_vertices")}) + "\n")
            fh.write(nx.to_graph6_bytes(nx.convert_node_labels_to_integers(H), header=False).decode())
    if a.check:
        print(f"{len(chosen)} checked, {bad} disagreements")
        sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
