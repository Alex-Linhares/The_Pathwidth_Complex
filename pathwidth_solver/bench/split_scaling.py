#!/usr/bin/env python3
"""The speed-up of the root split: one refutation on 1, 2, 4, 8 and 16 workers.

For each graph (proved pathwidth w, from the dataset), the refutation of width w - 1
("MOSP <= w" on the one-pattern-per-edge instance, `graph_split.py`) is run

  * sequentially: the unchanged search from the root, memo on, one process (the
    baseline, the C engine through `native.split_decide`);
  * split into the same decomposition of the root (breadth first to >= TARGET
    tasks, cap CAP nodes per task, further splits over the cap) on p workers for
    each p in WORKERS. The decomposition does not depend on p, so every split run
    does the same work in nodes; only the scheduling differs. Wall time, summed
    task CPU time, nodes, waste and the one-minute load at start and end are
    recorded. Speed-up = wall(sequential) / wall(p); the split's overhead is
    nodes(split) / nodes(sequential) (memo hits lost across tasks).

    nice -n 19 python3 -m pathwidth_solver.bench.split_scaling --ids pwc-14619 pwc-06210 pwc-17699 pwc-03773

Output: `pathwidth_solver/bench/results/split_scaling.csv` (one row per run), task rows
under `reports/scratch/split_scaling/<id>_p<p>/tasks.csv`. Nothing is written to the
dataset or `solutions/`.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import gzip
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import pathwidth_solver.bench.graph_split as gs  # noqa: E402

OUT = ROOT / "pathwidth_solver" / "bench" / "results" / "split_scaling.csv"
SCRATCH = ROOT / "reports" / "scratch" / "split_scaling"
FIELDS = ["id", "name", "n", "m", "width", "k", "mode", "workers", "target", "cap", "answer", "nodes", "tasks", "expanded", "waste",
          "wall_s", "cpu_s", "load_start", "load_end", "started", "finished"]


def load(ids: list[str]) -> list[dict]:
    want = set(ids)
    out = {}
    for line in gzip.open(gs.DATASET, "rt"):
        d = json.loads(line)
        if d["id"] in want:
            assert d["provenance"].startswith("certified"), d["id"]
            out[d["id"]] = dict(id=d["id"], n=d["n"], m=d["m"], width=int(d["width"]), edges=[tuple(e) for e in d["edges"]],
                                layout=None, names=d["members"][0].get("name", ""))
    return [out[i] for i in ids]


def append(row: dict) -> None:
    new = not OUT.exists() or OUT.stat().st_size == 0
    with OUT.open("a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        if new:
            w.writeheader()
        w.writerow({f: row.get(f, "") for f in FIELDS})


def sequential(t: dict, k: int) -> dict:
    from paper1.solver_fix_split import root, run_task, csearch_flags
    inst = gs.graph_to_instance(t["n"], t["edges"], t["id"])
    flags = csearch_flags(inst)
    t0 = time.monotonic(); c0 = time.process_time()
    ans = run_task(inst, k, root(), flags, memo=True, max_nodes=None, seconds=None)
    return dict(answer=ans.status, nodes=ans.nodes, wall_s=time.monotonic() - t0, cpu_s=time.process_time() - c0)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--ids", nargs="+", required=True)
    ap.add_argument("--workers", default="16,8,4,2,1")
    ap.add_argument("--target", type=int, default=64)
    ap.add_argument("--cap", type=float, default=3e9)
    ap.add_argument("--skip-sequential", action="store_true")
    a = ap.parse_args()
    workers = [int(x) for x in a.workers.split(",")]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    for t in load(a.ids):
        k = t["width"]
        base = dict(id=t["id"], name=t["names"][:60], n=t["n"], m=t["m"], width=t["width"], k=k, target=a.target, cap=int(a.cap))
        print(f"{dt.datetime.now():%F %T} === {t['id']} {t['names'][:40]} n={t['n']} m={t['m']} width {t['width']}: refuting k={k}", flush=True)
        if not a.skip_sequential:
            l0 = os.getloadavg()[0]; started = dt.datetime.now()
            r = sequential(t, k)
            append(dict(base, mode="sequential", workers=1, answer=r["answer"], nodes=r["nodes"], tasks=1, expanded=0, waste=0,
                        wall_s=round(r["wall_s"], 1), cpu_s=round(r["cpu_s"], 1), load_start=l0, load_end=os.getloadavg()[0],
                        started=started.isoformat(timespec="seconds"), finished=dt.datetime.now().isoformat(timespec="seconds")))
            print(f"{dt.datetime.now():%F %T} sequential: {r['answer']} {r['nodes']:.4g} nodes, {r['wall_s']:.0f} s wall, {r['cpu_s']:.0f} s cpu", flush=True)
            assert r["answer"] == "unsat", (t["id"], r["answer"])
        for p in workers:
            d = SCRATCH / f"{t['id']}_p{p}"
            d.mkdir(exist_ok=True)
            gs.TASKS = d / "tasks.csv"
            if gs.TASKS.exists():
                gs.TASKS.unlink()
            l0 = os.getloadavg()[0]; started = dt.datetime.now(); t0 = time.monotonic()
            res = gs.split_decide_parallel(t, k, p, int(a.cap), a.target, None)
            wall = time.monotonic() - t0
            append(dict(base, mode="split", workers=p, answer=res["answer"], nodes=res["task_nodes"] + res["edges"], tasks=res["tasks"],
                        expanded=res["expanded"], waste=res["waste"], wall_s=round(wall, 1), cpu_s=round(res.get("cpu_seconds", 0.0), 1),
                        load_start=l0, load_end=os.getloadavg()[0], started=started.isoformat(timespec="seconds"),
                        finished=dt.datetime.now().isoformat(timespec="seconds")))
            print(f"{dt.datetime.now():%F %T} split p={p}: {res['answer']} {res['task_nodes']+res['edges']:.4g} nodes ({res['tasks']} tasks, "
                  f"waste {res['waste']:.3g}), {wall:.0f} s wall, {res.get('cpu_seconds', 0):.0f} s cpu", flush=True)
            assert res["answer"] == "unsat", (t["id"], p, res["answer"])
    print(f"{dt.datetime.now():%F %T} done", flush=True)


if __name__ == "__main__":
    main()
