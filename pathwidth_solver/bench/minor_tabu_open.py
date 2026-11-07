#!/usr/bin/env python3
"""The seeded tabu search for a pathwidth lower bound, on the open dataset classes.

For every class of `reports/scratch/obstruction_search/13_pass1/pass2.csv` that
is not closed, the graph (its `certificates_2/<id>/instance.txt`) and the best
minor certificate on record (`minor.json`, a contraction sequence that refutes
`refuted_width`, so pathwidth >= refuted_width + 1) seed
`pathwidth_solver/cli/minor_tabu`: the walk starts at that minor, its floor is
the certified one, its target is the recorded width (an upper bound from a
layout), and each neighbour is tested by a bounded exact refutation of the one
level the ladder could not reach.  30 CPU minutes per class, `--procs` at a
time under nice 19, a JSON per class under `reports/scratch/minor_tabu/`, a
ledger CSV appended as classes finish (`--resume` skips ids already there).
A class whose target is reached is a new certificate: the ledger says so, and
the JSON holds the contraction sequence for the independent checker.
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parents[2]
CLI = ROOT / "pathwidth_solver" / "cli" / "minor_tabu"
PASS = ROOT / "reports" / "scratch" / "obstruction_search" / "13_pass1"
OUT = ROOT / "reports" / "scratch" / "minor_tabu"
FIELDS = ["id", "names", "n", "m", "width", "floor_before", "seed_minor", "floor_after", "kind", "minor_vertices",
          "reached_target", "steps", "exact_calls", "exact_nodes", "seconds", "status"]


def targets():
    rows = list(csv.DictReader(open(PASS / "pass2.csv")))
    out = []
    for r in rows:
        if r["closed"] == "True":
            continue
        cert = PASS / "certificates_2" / r["id"] / "minor.json"
        inst = PASS / "certificates_2" / r["id"] / "instance.txt"
        if not cert.exists() or not inst.exists():
            continue
        out.append(r)
    return out


def graph6_of(inst: Path) -> tuple[bytes, int, int]:
    lines = inst.read_text().split("\n")
    n, m = map(int, lines[0].split())
    G = nx.Graph(); G.add_nodes_from(range(n))
    for line in lines[1:]:
        p = line.split()
        if len(p) == 2:
            G.add_edge(int(p[0]), int(p[1]))
    return nx.to_graph6_bytes(G, header=False), n, G.number_of_edges()


def run_one(r: dict, seconds: float, seed: int) -> dict:
    cid = r["id"]
    cdir = PASS / "certificates_2" / cid
    cert = json.load(open(cdir / "minor.json"))
    g6, n, m = graph6_of(cdir / "instance.txt")
    OUT.mkdir(parents=True, exist_ok=True)
    seedfile = OUT / f"{cid}.seed"
    seedfile.write_text("".join(f"{v} {u}\n" for v, u in cert["sequence"] if u is not None and u >= 0))
    width = int(float(r["width"]))
    floor = int(cert.get("pathwidth_proved") or (int(cert["refuted_width"]) + 1))
    row = {k: "" for k in FIELDS}
    row.update(id=cid, names=r["names"], n=n, m=m, width=width, floor_before=floor, seed_minor=cert.get("m"))
    cmd = ["nice", "-n", "19", str(CLI), "-t", str(seconds), "-w", str(width), "-L", str(floor), "-seed", str(seedfile),
           "-S", "40", "-nb", "400000", "-nt", "1.5", "-b", "3000000", "-m", "120", "-lo", "0.3", "-hi", "0.95",
           "-c", "7", "-s", str(seed), "-p"]
    t0 = time.monotonic()
    try:
        proc = subprocess.run(cmd, input=g6, capture_output=True, timeout=seconds * 1.5 + 120)
        (OUT / f"{cid}.err").write_bytes(proc.stderr)
        out = proc.stdout.decode(errors="replace").strip().splitlines()
        d = json.loads(out[-1]) if out else {}
        (OUT / f"{cid}.json").write_text(json.dumps({"id": cid, "names": r["names"], "width": width, "floor_before": floor,
                                                     "seed_certificate": str(cdir / "minor.json"), "command": cmd, "result": d}, indent=1))
        row.update(floor_after=d.get("floor"), kind=d.get("kind"), minor_vertices=d.get("minor_vertices"),
                   reached_target=d.get("reached_target"), steps=d.get("steps"), exact_calls=d.get("exact_calls"),
                   exact_nodes=d.get("exact_nodes"), seconds=round(time.monotonic() - t0, 1),
                   status="CLOSED" if d.get("reached_target") else ("raised" if (d.get("floor") or 0) > floor else "ok"))
    except subprocess.TimeoutExpired:
        row.update(seconds=round(time.monotonic() - t0, 1), status="killed")
    except Exception as exc:  # noqa: BLE001
        row.update(seconds=round(time.monotonic() - t0, 1), status=f"error: {str(exc)[:100]}")
    return row


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--seconds", type=float, default=1800.0)
    ap.add_argument("--procs", type=int, default=8)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--only", nargs="*", default=None)
    ap.add_argument("--out", type=Path, default=OUT / "ledger.csv")
    ap.add_argument("--resume", action="store_true")
    a = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    rows = targets()
    if a.only:
        rows = [r for r in rows if r["id"] in a.only]
    done = set()
    if a.resume and a.out.exists():
        done = {r["id"] for r in csv.DictReader(open(a.out))}
    rows = [r for r in rows if r["id"] not in done]
    rows.sort(key=lambda r: (int(float(r["width"])) - int(float(r["m_pathwidth"] or 0)), int(r["n"])))  # smallest gap first
    print(f"{time.strftime('%F %T')} minor_tabu_open: {len(rows)} classes ({len(done)} done), {a.seconds:.0f} s each, {a.procs} at a time", flush=True)
    new = not a.out.exists() or a.out.stat().st_size == 0
    k = closed = 0
    with open(a.out, "a", newline="") as fh, ThreadPoolExecutor(a.procs) as pool:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        if new:
            w.writeheader()
        futs = {pool.submit(run_one, r, a.seconds, a.seed): r["id"] for r in rows}
        for fut in as_completed(futs):
            row = fut.result(); w.writerow(row); fh.flush(); k += 1; closed += row["status"] == "CLOSED"
            print(f"{time.strftime('%T')} {k}/{len(rows)} {row['id']} {str(row['names'])[:26]:26} n={row['n']:>4} width {row['width']} "
                  f"floor {row['floor_before']} -> {row['floor_after']} ({row['kind']}, {row['minor_vertices']} v) steps {row['steps']} "
                  f"exact {row['exact_calls']} {row['seconds']}s {row['status']}  closed so far {closed}", flush=True)
    print(f"{time.strftime('%F %T')} done: {k} classes, {closed} closed", flush=True)


if __name__ == "__main__":
    main()
