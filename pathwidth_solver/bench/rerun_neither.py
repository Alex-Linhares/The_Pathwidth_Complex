#!/usr/bin/env python3
"""Rerun, with the rebuilt program (memo table cap 2 GB, memo limit 64M), the graphs that neither
solver proved in the paired SageMath comparison (`results/sage_paired_600s.csv`), excluding the
grids certified by theorem and the two proved on record (Higman–Sims, BalancedTree_3_5):
70 open graphs, the same 600 s CPU cap, nice 19, N at a time. Ours only; no SageMath.

    python3 -m pathwidth_solver.bench.rerun_neither --cap 600 --procs 16 --out results/neither70_2gb.csv
"""
from __future__ import annotations
import argparse, csv, os, resource, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import networkx as nx
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from readers import HERE as INST, SETS, read_any  # noqa: E402
CLI = HERE.parent / "cli" / "pathwidth"
PAIRED = HERE / "results" / "sage_paired_600s.csv"
EXCLUDE_SETS = {"vsplib-grids"}
EXCLUDE_NAMES = {"HigmanSimsGraph.gr", "BalancedTree_3_5.gr"}
P = ("refutation", "bound", "minor")
FIELDS = ["set", "name", "n", "m", "old_width", "old_status", "width", "status", "lower", "nodes", "cpu_s", "wall_s", "peak_mb", "load1"]


def targets():
    rows = list(csv.DictReader(open(PAIRED)))
    out = []
    for x in rows:
        if x["ours_proof"] in P or x["sage_status"] == "ok" or x["set"] in EXCLUDE_SETS:
            continue
        if x["name"].split("/")[-1] in EXCLUDE_NAMES:
            continue
        out.append(x)
    return out


def path_of(setname: str, name: str) -> Path:
    for p in SETS[setname]():
        if str(p).endswith(name) or str(p.relative_to(INST)) == name or p.name == name.split("/")[-1]:
            return p
    raise FileNotFoundError(name)


def run_one(x, cap):
    G = read_any(path_of(x["set"], x["name"]))
    g6 = nx.to_graph6_bytes(G, header=False)
    def limits():
        os.nice(19); resource.setrlimit(resource.RLIMIT_CPU, (cap + 1, cap + 5))
    t0 = time.monotonic(); l1 = os.getloadavg()[0]
    p = subprocess.run([str(CLI), "-t", str(cap), "-v"], input=g6, capture_output=True, preexec_fn=limits, timeout=cap * 2 + 60)
    wall = time.monotonic() - t0
    out = p.stdout.decode().split(); err = p.stderr.decode()
    width = out[1] if len(out) >= 3 and out[0] == "pathwidth" else ""
    status = out[2] if len(out) >= 3 else "error"
    kv = dict(tok.split("=", 1) for tok in err.replace("line 1:", "").split() if "=" in tok)
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    return dict(set=x["set"], name=x["name"], n=x["n"], m=x["m"], old_width=x["ours_width"], old_status=x["ours_proof"],
                width=width, status=status, lower=kv.get("lower", ""), nodes=kv.get("nodes", ""), cpu_s=kv.get("seconds", ""),
                wall_s=round(wall, 1), peak_mb=round(ru.ru_maxrss / 1024), load1=round(l1, 1))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--cap", type=int, default=600); ap.add_argument("--procs", type=int, default=16)
    ap.add_argument("--out", type=Path, default=HERE / "results" / "neither70_2gb.csv")
    a = ap.parse_args()
    rows = targets()
    print(f"{time.strftime('%F %T')} rerun_neither: {len(rows)} graphs, cap {a.cap} s CPU, {a.procs} at a time", flush=True)
    with open(a.out, "w", newline="") as fh, ThreadPoolExecutor(a.procs) as pool:
        w = csv.DictWriter(fh, fieldnames=FIELDS); w.writeheader()
        futs = {pool.submit(run_one, x, a.cap): x for x in rows}
        k = proved = 0
        for f in as_completed(futs):
            r = f.result(); w.writerow(r); fh.flush(); k += 1; proved += r["status"] in P
            print(f"{time.strftime('%T')} {k}/{len(rows)} {r['name'].split('/')[-1]:34} n={r['n']:>4} w={r['width']:>4} {r['status']:10} "
                  f"(was {r['old_width']} {r['old_status']}) nodes {r['nodes']:>12} {r['cpu_s']} s  proved so far {proved}", flush=True)
    print(f"{time.strftime('%F %T')} done: {k} graphs, {proved} proved", flush=True)


if __name__ == "__main__":
    main()
