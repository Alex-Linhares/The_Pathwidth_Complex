#!/usr/bin/env python3
"""The root split on graphs: one pathwidth refutation spread over many cores.

The adapter. A graph `G` on `n` vertices with `m` edges becomes the MOSP instance
with one customer per vertex and one pattern per edge (the pattern of edge `uv`
is required by `u` and `v` alone). Its customer graph is `G` itself, so by
Theorem thm:mosp (`MOSPGraph.lean`) its optimum is `pw(G) + 1`, and a refutation of
"MOSP <= k" is a proof of `pw(G) >= k`. A closing order of the customers is a
layout: the width of the order is the largest outer boundary `|N(S) \\ S|` over its
prefixes `S`, which is the open-stack peak minus one, and the reversed order is a
path decomposition of that width.

The split is `paper1/solver_fix_split.py`'s (loop0007 item 10; `Search/Split.lean`
proves an all-unsat split is a refutation): the driver expands the top of the tree
with `native.split_expand`, every child is a task run by `native.split_decide`
from an empty memo with the old moves it inherits from its earlier siblings, a
task over its node cap is split further (its nodes counted as waste), and nothing
is claimed before every task has answered unsat. A task that answers sat yields a
closing order of width `k - 1`: the recorded width was not optimal, the order is
verified and recorded, and the descent continues at `k - 1`.

Targets: the dataset's open classes (`paper1/data/dataset/pathwidth_dataset.jsonl.gz`,
provenance not `certified:*`), one graph per class, **smallest first** (vertices,
then edges), each descended from `k = recorded width` until a refutation. No time
limit (`--until` for a stop). Resumable from the task rows.

    nice -n 19 python3 -m pathwidth_solver.bench.graph_split --workers 16
    python3 -m pathwidth_solver.bench.graph_split --summary

Output under `reports/scratch/graph_split/`: `tasks.csv` (every expansion and task),
`results.csv` (one row per decision settled), `witnesses/<id>_k<k>.txt` (new
layouts), `run.out`. Nothing here writes to `solutions/` or to the dataset.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import csv
import datetime as dt
import gzip
import json
import multiprocessing as mp
import os
import signal
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
OUT = ROOT / "reports" / "scratch" / "graph_split"
TASKS = OUT / "tasks.csv"
RESULTS = OUT / "results.csv"
DATASET = ROOT / "paper1" / "data" / "dataset" / "pathwidth_dataset.jsonl.gz"
TASK_FIELDS = ["id", "k", "kind", "key", "children", "cap", "status", "nodes", "seconds", "started", "finished", "witness"]
RESULT_FIELDS = ["id", "names", "n", "m", "width_recorded", "k", "answer", "pathwidth", "new_width", "tasks", "expanded",
                 "edges", "task_nodes", "waste", "core_seconds", "wall_seconds", "started", "finished"]


# ---------------------------------------------------------------- the adapter

def graph_to_instance(n: int, edges: list[tuple[int, int]], name: str):
    """One customer per vertex, one pattern per edge: the customer graph is G."""
    from mosp.instance import MOSPInstance
    matrix = np.zeros((n, len(edges)), dtype=np.int8)
    for j, (u, v) in enumerate(edges):
        matrix[u, j] = 1
        matrix[v, j] = 1
    return MOSPInstance(matrix=matrix, n_customers=n, n_patterns=len(edges), name=name)


def adjacency(n: int, edges) -> list[set[int]]:
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    return adj


def width_of_closing_order(n: int, edges, order: list[int]) -> int:
    """max over prefixes S of |N(S) \\ S|: the open-stack peak of the order minus one,
    and the vertex separation of the reversed order as a layout."""
    adj = adjacency(n, edges)
    in_s = [False] * n
    boundary: set[int] = set()
    best = 0
    for v in order:
        in_s[v] = True
        boundary.discard(v)
        for u in adj[v]:
            if not in_s[u]:
                boundary.add(u)
        best = max(best, len(boundary))
    return best


def vertex_separation(n: int, edges, layout: list[int]) -> int:
    """max over prefixes S of |{u in S with a neighbour outside S}| (Kinnersley)."""
    adj = adjacency(n, edges)
    pos = {v: i for i, v in enumerate(layout)}
    best = 0
    for i in range(n):
        left = sum(1 for u in layout[: i + 1] if any(pos[w] > i for w in adj[u]))
        best = max(best, left)
    return best


# ---------------------------------------------------------------- the targets

CLOSED_ON_RECORD = {
    # proved after the dataset was built; certificates in reports/scratch/obstruction_search/ (loop0013 and pass 2)
    "pwc-15933": "BalancedTree_3_5: branch lemma, loop0013 (reports/obstruction_search.md)",
    "pwc-17631": "NY_11 (pass 2)", "pwc-17668": "Promedas_59_10 (pass 2)", "pwc-17264": "ex017 (pass 2)",
    "pwc-17384": "ex142 (pass 2)",
}
# NY_13 (pwc id in 07_open/results_obstruction.csv) is also closed on record; it is excluded by name below.
CLOSED_NAMES = ("NY_13.gr",)


def law_log10_nodes(n: int, w: int) -> float:
    """Section 5's cost law on the Rome graphs: log10(nodes to refute w-1) ~ 1.75 + 0.00705 n w."""
    return 1.75 + 0.00705 * n * w


def targets(order: str = "size") -> list[dict]:
    rows = []
    for line in gzip.open(DATASET, "rt"):
        d = json.loads(line)
        if d["provenance"].startswith("certified"):
            continue
        if d["id"] in CLOSED_ON_RECORD or any(any(c in str(mm.get("name", "")) for c in CLOSED_NAMES) for mm in d["members"]):
            continue
        rows.append(dict(id=d["id"], n=d["n"], m=d["m"], width=int(d["width"]),
                         edges=[tuple(e) for e in d["edges"]], layout=d.get("layout"),
                         names="; ".join(str(mm.get("name", "")) for mm in d["members"])[:120]))
    if order == "law":
        rows.sort(key=lambda r: (law_log10_nodes(r["n"], r["width"]), r["n"], r["id"]))
    else:
        rows.sort(key=lambda r: (r["n"], r["m"], r["id"]))
    return rows


# ---------------------------------------------------------------- the split

_W: dict = {}


def _init(n, edges, name):
    os.nice(19)
    _W["inst"] = graph_to_instance(n, edges, name)


def _task(args):
    from paper1.solver_fix_split import Node, run_task
    k, key, closed, opened, seen, prefix, flags, cap = args
    started = dt.datetime.now().isoformat(timespec="seconds")
    t0 = time.monotonic()
    ans = run_task(_W["inst"], k, Node(key, closed, opened, seen, prefix), flags, max_nodes=cap, seconds=None)
    return dict(key=key, status=ans.status, nodes=ans.nodes, seconds=round(time.monotonic() - t0, 3),
                witness=ans.order, started=started, finished=dt.datetime.now().isoformat(timespec="seconds"))


def _append(path: Path, fields, row: dict) -> None:
    new = not path.exists() or path.stat().st_size == 0
    with path.open("a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        if new:
            w.writeheader()
        w.writerow({f: row.get(f, "") for f in fields})


def _rows(path: Path) -> list[dict]:
    return list(csv.DictReader(path.open())) if path.exists() else []


def split_decide_parallel(target: dict, k: int, workers: int, base_cap: int, task_target: int,
                          until: dt.datetime | None) -> dict:
    """All workers on one decision "MOSP(G) <= k?". Returns answer, counts and witness."""
    from paper1.solver_fix_split import Node, root, expand, csearch_flags
    from satisfiability.heuristics import _neighbour_masks
    n, edges, cid = target["n"], target["edges"], target["id"]
    inst = graph_to_instance(n, edges, cid)
    flags = csearch_flags(inst)
    masks = _neighbour_masks(inst)
    # resume state for (id, k)
    prior = [r for r in _rows(TASKS) if r["id"] == cid and int(r["k"]) == k]
    done = {r["key"]: int(r["nodes"]) for r in prior if r["kind"] == "task" and r["status"] == "unsat"}
    split_keys = {r["key"] for r in prior if r["kind"] == "task" and r["status"] == "split"}
    expanded_keys = {r["key"] for r in prior if r["kind"] == "expand"}
    prior_waste = sum(int(r["nodes"]) for r in prior if r["kind"] == "task" and r["status"] in ("split", "stopped"))
    prior_seconds = sum(float(r["seconds"] or 0) for r in prior)

    def key_of(node):
        return ".".join(map(str, node.key))

    counts = dict(edges=0, expanded=0, task_nodes=sum(done.values()), waste=prior_waste, tasks=len(done),
                  core_seconds=prior_seconds)

    def do_expand(node, record=True):
        witness, children = expand(inst, k, node, flags, masks)
        if children is None:
            return witness, None
        counts["expanded"] += 1
        counts["edges"] += len(children)
        if record and key_of(node) not in expanded_keys:
            _append(TASKS, TASK_FIELDS, dict(id=cid, k=k, kind="expand", key=key_of(node), children=len(children),
                                             started=dt.datetime.now().isoformat(timespec="seconds")))
            expanded_keys.add(key_of(node))
        return None, children

    def pieces_of(node):
        """Breadth-first into at least `workers` pieces (deterministic, so a resume reproduces it)."""
        pieces = [node]
        while pieces and len(pieces) < workers:
            w, kids = do_expand(pieces.pop(0))
            if kids is None:
                return w, None
            pieces.extend(kids)
        return None, pieces

    def cap_at(node):
        return base_cap * min(4, 2 ** max(0, len(node.key) - 1))

    # breadth-first expansion of the top to the task target, replaying recorded splits
    pending = [root()]
    while pending and len(pending) < task_target:
        node = pending.pop(0)
        w, kids = do_expand(node)
        if kids is None:
            return dict(answer="sat", witness=w, **counts)
        pending.extend(kids)
    # replay recorded splits (deterministic) and drop finished keys
    def settle(nodes):
        out = []
        for nd in nodes:
            kk = key_of(nd)
            if kk in done:
                continue
            if kk in split_keys:
                w, ps = pieces_of(nd)
                if ps is None:
                    return w, None
                sub, nothing = settle(ps)
                if nothing is None:
                    return sub, None
                out.extend(sub)
            else:
                out.append(nd)
        return out, True
    pending, ok = settle(pending)
    if ok is None:
        return dict(answer="sat", witness=pending, **counts)
    print(f"{dt.datetime.now():%F %T} {cid} k={k}: {len(pending)} tasks pending, {len(done)} done before, "
          f"{counts['expanded']} expansions", flush=True)

    ctx = mp.get_context("spawn")
    flying: dict = {}
    answer = None
    witness = None
    with cf.ProcessPoolExecutor(workers, mp_context=ctx, initializer=_init, initargs=(n, edges, cid)) as pool:
        def submit():
            while pending and len(flying) < workers:
                if until is not None and (until - dt.datetime.now()).total_seconds() < 60:
                    return
                node = pending.pop(0)
                fut = pool.submit(_task, (k, node.key, node.closed, node.opened, node.seen, node.prefix, flags, cap_at(node)))
                flying[fut] = node
        submit()
        while flying:
            finished, _ = cf.wait(list(flying), timeout=600, return_when=cf.FIRST_COMPLETED)
            for fut in finished:
                node = flying.pop(fut)
                out = fut.result()
                counts["core_seconds"] += out["seconds"]
                base = dict(id=cid, k=k, kind="task", key=key_of(node), cap=cap_at(node), status=out["status"],
                            nodes=out["nodes"], seconds=out["seconds"], started=out["started"], finished=out["finished"])
                if out["status"] == "unsat":
                    done[key_of(node)] = out["nodes"]
                    counts["task_nodes"] += out["nodes"]; counts["tasks"] += 1
                    _append(TASKS, TASK_FIELDS, base)
                elif out["status"] == "sat":
                    witness = out["witness"]
                    _append(TASKS, TASK_FIELDS, dict(base, witness=" ".join(map(str, witness))))
                    answer = "sat"
                    for f in flying:
                        f.cancel()
                    # running tasks keep their CPU until their cap: kill the workers
                    for p in list(getattr(pool, "_processes", {}).values()):
                        try:
                            os.kill(p.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                    flying.clear()
                    break
                elif out["nodes"] >= cap_at(node):
                    _append(TASKS, TASK_FIELDS, dict(base, status="split"))
                    split_keys.add(key_of(node))
                    counts["waste"] += out["nodes"]
                    w, ps = pieces_of(node)
                    if ps is None:
                        witness, answer = w, "sat"
                        flying.clear()
                        break
                    pending[:0] = ps
                else:
                    _append(TASKS, TASK_FIELDS, dict(base, kind="stopped"))
                    counts["waste"] += out["nodes"]
                print(f"{out['finished']} {cid} k={k} {key_of(node) or 'root'} {out['status']} {out['nodes']:.3g} nodes "
                      f"{out['seconds']:.0f} s; {len(pending)} queued, {len(flying)} flying, {len(done)} done", flush=True)
            if answer == "sat":
                break
            submit()
        if answer == "sat":
            pool.shutdown(wait=False, cancel_futures=True)
    if answer == "sat":
        return dict(answer="sat", witness=witness, **counts)
    if pending or (until is not None):
        if pending:
            return dict(answer="stopped", witness=None, **counts)
    return dict(answer="unsat", witness=None, **counts)


# ---------------------------------------------------------------- the driver

def drive(workers: int, base_cap: int, task_target: int, only: list[str] | None, until: dt.datetime | None,
          order: str = "size") -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "witnesses").mkdir(exist_ok=True)
    done_ids = {r["id"] for r in _rows(RESULTS) if r["answer"] == "unsat"}
    rows = targets(order)
    if only:
        rows = [r for r in rows if r["id"] in only]
    rows = [r for r in rows if r["id"] not in done_ids]
    print(f"{dt.datetime.now():%F %T} graph_split: {len(rows)} open classes ({len(done_ids)} closed before), "
          f"{workers} workers, cap {base_cap:.3g} nodes, {task_target} tasks to start", flush=True)
    for t in rows:
        n, edges = t["n"], t["edges"]
        # the recorded width must be a verified upper bound: check the dataset's layout
        width = t["width"]
        lay = t.get("layout")
        if lay:
            vs = vertex_separation(n, edges, list(lay))
            vs_rev = vertex_separation(n, edges, list(lay)[::-1])
            if min(vs, vs_rev) != width:
                print(f"!!! {t['id']}: the dataset layout has vertex separation {vs}/{vs_rev}, recorded width {width}; "
                      f"using min", flush=True)
                width = min(width, vs, vs_rev)
        # resume: a sat row at some k lowers the start
        prior_sat = [int(r["k"]) for r in _rows(RESULTS) if r["id"] == t["id"] and r["answer"] == "sat"]
        k = min([width] + [kk - 1 for kk in prior_sat])
        print(f"{dt.datetime.now():%F %T} === {t['id']} {t['names'][:60]} n={n} m={t['m']} width {width}: refuting k={k}", flush=True)
        while True:
            started = dt.datetime.now()
            res = split_decide_parallel(t, k, workers, base_cap, task_target, until)
            wall = (dt.datetime.now() - started).total_seconds()
            row = dict(id=t["id"], names=t["names"], n=n, m=t["m"], width_recorded=t["width"], k=k, answer=res["answer"],
                       tasks=res["tasks"], expanded=res["expanded"], edges=res["edges"], task_nodes=res["task_nodes"],
                       waste=res["waste"], core_seconds=round(res["core_seconds"], 1), wall_seconds=round(wall, 1),
                       started=started.isoformat(timespec="seconds"), finished=dt.datetime.now().isoformat(timespec="seconds"))
            if res["answer"] == "unsat":
                row["pathwidth"] = k
                _append(RESULTS, RESULT_FIELDS, row)
                print(f"{dt.datetime.now():%F %T} CLOSED {t['id']} {t['names'][:40]}: pathwidth = {k} "
                      f"(MOSP <= {k} refuted; {res['tasks']} tasks, {res['task_nodes']:.3g} nodes, waste {res['waste']:.3g}, "
                      f"{res['core_seconds']/3600:.2f} core-h, {wall/3600:.2f} h wall)", flush=True)
                break
            if res["answer"] == "sat":
                w = width_of_closing_order(n, edges, res["witness"])
                assert w <= k - 1, (w, k)
                row.update(new_width=w)
                _append(RESULTS, RESULT_FIELDS, row)
                (OUT / "witnesses" / f"{t['id']}_k{k}.txt").write_text(
                    f"# {t['id']} {t['names']}: closing order of width {w} (reverse it for a path decomposition); recorded width was {t['width']}\n"
                    + " ".join(map(str, res["witness"])) + "\n")
                print(f"{dt.datetime.now():%F %T} NEW UPPER BOUND {t['id']}: width {w} (recorded {t['width']}); continuing at k={w}", flush=True)
                k = w
                continue
            _append(RESULTS, RESULT_FIELDS, row)
            print(f"{dt.datetime.now():%F %T} stopped {t['id']} at k={k} (--until)", flush=True)
            return
    print(f"{dt.datetime.now():%F %T} done: no open class left in the list", flush=True)


def summary() -> None:
    rows = _rows(RESULTS)
    closed = [r for r in rows if r["answer"] == "unsat"]
    print(f"{len(rows)} decisions; {len(closed)} classes closed; {sum(r['answer']=='sat' for r in rows)} new upper bounds")
    for r in rows:
        print(f"  {r['id']} {r['names'][:36]:36} n={r['n']:>4} k={r['k']} {r['answer']:7} pw={r['pathwidth'] or '-'} new={r['new_width'] or '-'} "
              f"tasks {r['tasks']} nodes {float(r['task_nodes'] or 0):.3g} waste {float(r['waste'] or 0):.3g} {float(r['core_seconds'])/3600:.2f} core-h {float(r['wall_seconds'])/3600:.2f} h")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--cap", type=float, default=3e9, help="nodes before a task is split (doubling with depth to 4x)")
    ap.add_argument("--target", type=int, default=64, help="tasks to open before running (breadth first)")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--until", help="ISO time: submit nothing that cannot run a minute")
    ap.add_argument("--order", choices=["size", "law"], default="size",
                    help="size: vertices then edges; law: Section 5's cost law 1.75 + 0.00705 n w (predicted nodes), cheapest first")
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--list", action="store_true", help="print the queue in the chosen order with the law's prediction")
    a = ap.parse_args()
    if a.summary:
        summary(); return
    if a.list:
        for r in targets(a.order):
            lg = law_log10_nodes(r["n"], r["width"])
            print(f"{r['id']} {r['names'][:40]:40} n={r['n']:4} m={r['m']:5} w={r['width']:3} law log10 nodes {lg:5.1f} core-days {10**lg*0.65e-6/86400:9.3g}")
        return
    drive(a.workers, int(a.cap), a.target, a.only, dt.datetime.fromisoformat(a.until) if a.until else None, a.order)


if __name__ == "__main__":
    main()
