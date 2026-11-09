#!/usr/bin/env python3
"""One open graph at a time under the root split: all workers on it for a fixed wall budget.

For each dataset class given (open, at most 128 vertices — the native split's reach), the
refutation of the recorded width is split at the root over `--workers` workers, each task
with the engine's default memo (64M since 2026-11-09), for `--minutes` of wall clock; a task
still running at the deadline is stopped and its nodes counted as waste. Closed means every
task answered unsat; a sat task is a better layout and the descent continues at width - 1
within the same budget. Rows to `results/split_budget.csv`, task rows under
`reports/scratch/split_budget/<id>/tasks.csv`.

    nice -n 19 python3 -m pathwidth_solver.bench.split_budget --ids pwc-15968 ... --workers 16 --minutes 10
"""
from __future__ import annotations
import argparse, csv, datetime as dt, gzip, json, os, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import pathwidth_solver.bench.graph_split as gs  # noqa: E402
OUT = ROOT / "pathwidth_solver" / "bench" / "results" / "split_budget.csv"
SCRATCH = ROOT / "reports" / "scratch" / "split_budget"
FIELDS = ["id", "name", "n", "m", "width", "k", "workers", "minutes", "answer", "new_width", "tasks_done", "tasks_left", "nodes", "waste",
          "cpu_s", "wall_s", "load_start", "load_end", "started", "finished"]


def load(ids):
    want = set(ids); out = {}
    for line in gzip.open(gs.DATASET, "rt"):
        d = json.loads(line)
        if d["id"] in want:
            out[d["id"]] = dict(id=d["id"], n=d["n"], m=d["m"], width=int(d["width"]), edges=[tuple(e) for e in d["edges"]],
                                layout=None, names=d["members"][0].get("name", ""), provenance=d["provenance"])
    return [out[i] for i in ids]


def append(row):
    new = not OUT.exists() or OUT.stat().st_size == 0
    with OUT.open("a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        if new: w.writeheader()
        w.writerow({f: row.get(f, "") for f in FIELDS})


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--ids", nargs="+", required=True); ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--minutes", type=float, default=10.0); ap.add_argument("--cap", type=float, default=3e9); ap.add_argument("--target", type=int, default=64)
    a = ap.parse_args()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    for t in load(a.ids):
        assert t["n"] <= gs.MAX_SPLIT_VERTICES, (t["id"], t["n"])
        k = t["width"]; deadline = dt.datetime.now() + dt.timedelta(minutes=a.minutes)
        print(f"{dt.datetime.now():%F %T} === {t['id']} {t['names'][:40]} n={t['n']} m={t['m']} width {t['width']} ({t['provenance']}): {a.minutes:g} min on {a.workers} workers", flush=True)
        while True:
            d = SCRATCH / t["id"]; d.mkdir(exist_ok=True); gs.TASKS = d / f"tasks_k{k}.csv"
            l0 = os.getloadavg()[0]; started = dt.datetime.now(); t0 = time.monotonic()
            res = gs.split_decide_parallel(t, k, a.workers, int(a.cap), a.target, deadline)
            wall = time.monotonic() - t0
            left = sum(1 for r in csv.DictReader(open(gs.TASKS)) if r["kind"] == "stopped") if gs.TASKS.exists() else ""
            row = dict(id=t["id"], name=t["names"][:60], n=t["n"], m=t["m"], width=t["width"], k=k, workers=a.workers, minutes=a.minutes,
                       answer=res["answer"], tasks_done=res["tasks"], tasks_left=left, nodes=res["task_nodes"] + res["edges"], waste=res["waste"],
                       cpu_s=round(res.get("cpu_seconds", 0.0), 1), wall_s=round(wall, 1), load_start=round(l0, 1), load_end=round(os.getloadavg()[0], 1),
                       started=started.isoformat(timespec="seconds"), finished=dt.datetime.now().isoformat(timespec="seconds"))
            if res["answer"] == "sat":
                w = gs.width_of_closing_order(t["n"], t["edges"], res["witness"]); row["new_width"] = w; append(row)
                (d / f"witness_k{k}.txt").write_text(" ".join(map(str, res["witness"])) + "\n")
                print(f"{dt.datetime.now():%F %T} NEW UPPER BOUND {t['id']}: width {w} (recorded {t['width']}); continuing at k={w}", flush=True)
                k = w
                if dt.datetime.now() >= deadline: break
                continue
            append(row)
            print(f"{dt.datetime.now():%F %T} {t['id']}: {res['answer'].upper()} at k={k} — {res['tasks']} tasks unsat, {left} stopped at the deadline, "
                  f"{res['task_nodes']:.3g} nodes, waste {res['waste']:.3g}, {res.get('cpu_seconds',0)/60:.0f} CPU-min in {wall/60:.1f} min", flush=True)
            break
    print(f"{dt.datetime.now():%F %T} done", flush=True)


if __name__ == "__main__":
    main()
