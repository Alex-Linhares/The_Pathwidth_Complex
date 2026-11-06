#!/usr/bin/env python3
"""Paired head-to-head against SageMath's exact vertex separation, under load.

For every graph the two solvers start at the same moment, each pinned to its own
physical core (hyperthread siblings left to the machine), both at `nice -n 19`,
each with the same **CPU-time** cap (`RLIMIT_CPU`) and a wall-clock hard kill at
four times the cap plus a minute. Whatever the machine's other load does, it does to
both; and CPU time, not the clock, is what is recorded and compared.

  * SageMath: `vertex_separation(G, algorithm="BAB")`, the branch and bound of
    Coudert, Mazauric & Nisse (2016), from the `sage` conda environment (10.8).
    Exact when it returns, so a returned value counts as proved.
  * Ours: the shipped C program `pathwidth_solver/cli/pathwidth -t CAP -l -v`
    (the minor step on, graph6 on stdin), never the Python solver (CLAUDE.md,
    2026-10-18). Its node count is recorded: a load-free unit for our side.

One CSV row per graph: both widths, both statuses, both CPU and wall times, our
nodes, the one-minute load at launch. Resumable (`--resume` skips names in --out).
`--sample N --seed S` draws N graphs of the chosen sets for a variance study:
run it twice, on a quiet and on a busy machine, into two files.

    python3 pathwidth_solver/bench/sage_paired.py --sets coloring named vsplib-tree vsplib-hb vsplib-grids \
        --rome-sample 500 --cap 600 --pairs 6 --out pathwidth_solver/bench/results/sage_paired_600s.csv --resume
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import random
import resource
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import networkx as nx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
from readers import HERE as INST, SETS, read_any  # noqa: E402

SAGE_PY = "/home/al/anaconda3/envs/sage/bin/python"
CLI = HERE.parent / "cli" / "pathwidth"
FIELDS = ["set", "name", "n", "m", "cap", "load1", "load1_end",
          "ours_width", "ours_status", "ours_proof", "ours_cpu", "ours_wall", "ours_nodes", "ours_core",
          "sage_width", "sage_status", "sage_cpu", "sage_wall", "sage_core", "sage_detail"]

SAGE_CODE = r"""
import json, sys, time, resource
from sage.all import Graph
from sage.graphs.graph_decompositions.vertex_separation import vertex_separation
n, edges = json.load(open(sys.argv[1]))
G = Graph(); G.add_vertices(range(n)); G.add_edges(edges)
t = time.time()
w, order = vertex_separation(G, algorithm="BAB")
ru = resource.getrusage(resource.RUSAGE_SELF)
print(json.dumps({"width": int(w), "wall": time.time() - t, "cpu": ru.ru_utime + ru.ru_stime}))
"""


def physical_cores() -> list[int]:
    """One CPU id per physical core, from lscpu; falls back to even ids."""
    try:
        out = subprocess.run(["lscpu", "-p=CPU,CORE"], capture_output=True, text=True).stdout
        first = {}
        for line in out.splitlines():
            if line.startswith("#"):
                continue
            cpu, core = map(int, line.split(","))
            first.setdefault(core, cpu)
        return [first[c] for c in sorted(first)]
    except Exception:  # noqa: BLE001
        return list(range(0, os.cpu_count() or 2, 2))


def _limit(cap: float):
    def pre():
        resource.setrlimit(resource.RLIMIT_CPU, (int(cap) + 1, int(cap) + 5))
        os.nice(19)
    return pre


def _run(cmd: list[str], stdin: bytes | None, cap: float, hard: float):
    """Run, return (stdout, stderr, returncode, cpu seconds, wall seconds, status)."""
    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE if stdin is not None else None,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=_limit(cap),
                            start_new_session=True)
    try:
        out, err = proc.communicate(stdin, timeout=hard)
        status = "ok" if proc.returncode == 0 else "timeout" if proc.returncode in (-24, 152, -9) else "error"
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, 9)
        except OSError:
            pass
        out, err = proc.communicate()
        status = "timeout"
    wall = time.monotonic() - t0
    return out, err, proc.returncode, wall, status


def run_pair(job) -> dict:
    setname, path, cap, core_ours, core_sage = job
    G = read_any(path)
    G = nx.convert_node_labels_to_integers(G)
    edges = [(int(u), int(v)) for u, v in G.edges()]
    row = {k: "" for k in FIELDS}
    row.update(set=setname, name=str(path.relative_to(INST)), n=G.number_of_nodes(), m=G.number_of_edges(),
               cap=cap, load1=round(os.getloadavg()[0], 1), ours_core=core_ours, sage_core=core_sage)
    g6 = nx.to_graph6_bytes(G, header=False)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump([G.number_of_nodes(), edges], f)
        gfile = f.name
    hard = 4 * cap + 60      # under heavy contention a pinned process may need several times the wall time to spend its CPU cap
    tfile = gfile + ".time"
    ours_cmd = ["taskset", "-c", str(core_ours), "/usr/bin/time", "-f", "%U %S", "-o", tfile,
                str(CLI), "-t", str(cap), "-l", "-v"]
    sage_cmd = ["taskset", "-c", str(core_sage), SAGE_PY, "-c", SAGE_CODE, gfile]
    with ThreadPoolExecutor(2) as pool:          # both start now
        fo = pool.submit(_run, ours_cmd, g6, cap, hard)
        fs = pool.submit(_run, sage_cmd, None, cap, hard)
        o_out, o_err, o_rc, o_wall, o_status = fo.result()
        s_out, s_err, s_rc, s_wall, s_status = fs.result()
    Path(gfile).unlink(missing_ok=True)
    row["load1_end"] = round(os.getloadavg()[0], 1)
    # ours: stdout "pathwidth w status" (+ layout); stderr -v line: n width status lower upper nodes minor_nodes calls seconds
    for line in o_out.decode(errors="replace").splitlines():
        if line.startswith("pathwidth "):
            _, w, st = line.split()[:3]
            row.update(ours_width=int(w), ours_proof=st)
    for line in o_err.decode(errors="replace").splitlines():   # "line 1: n=14 width=6 status=... nodes=119 ..."
        kv = dict(tok.split("=", 1) for tok in line.split() if "=" in tok)
        if "nodes" in kv:
            row["ours_nodes"] = kv["nodes"]
    row["ours_status"] = o_status if row["ours_proof"] in ("", "upper") else "ok"
    if o_status == "ok" and row["ours_proof"] == "upper":
        row["ours_status"] = "budget"
    row.update(ours_wall=round(o_wall, 2))
    try:                                       # GNU time: user + system seconds of the C process
        u, sy = Path(tfile).read_text().split()[-2:]
        row["ours_cpu"] = round(float(u) + float(sy), 2)
    except Exception:  # noqa: BLE001
        row["ours_cpu"] = ""
    Path(tfile).unlink(missing_ok=True)
    if s_status == "ok" and s_out.strip():
        try:
            r = json.loads(s_out.decode().strip().splitlines()[-1])
            row.update(sage_width=r["width"], sage_cpu=round(r["cpu"], 2), sage_wall=round(r["wall"], 2), sage_status="ok")
        except Exception as exc:  # noqa: BLE001
            row.update(sage_status="error", sage_detail=str(exc)[:120])
    else:
        row.update(sage_status=s_status, sage_wall=round(s_wall, 2),
                   sage_detail=s_err.decode(errors="replace").strip()[-160:].replace("\n", " "))
    return row


def graphs(sets, rome_sample, seed, sample):
    out = []
    for name in sets:
        for p in SETS[name]():
            out.append((name, p))
    if rome_sample:
        rome = list(SETS["rome"]())
        random.Random(seed).shuffle(rome)
        out += [("rome-sample", p) for p in sorted(rome[:rome_sample])]
    if sample:
        random.Random(seed + 1).shuffle(out)
        out = sorted(out[:sample])
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--sets", nargs="*", default=["coloring", "named", "vsplib-tree", "vsplib-hb", "vsplib-grids"])
    ap.add_argument("--rome-sample", type=int, default=500)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--sample", type=int, default=None, help="run only N graphs drawn from the chosen sets (variance study)")
    ap.add_argument("--cap", type=float, default=600.0, help="CPU seconds per solver per graph")
    ap.add_argument("--pairs", type=int, default=6, help="graphs run at once (two physical cores each)")
    ap.add_argument("--first-core", type=int, default=1, help="index into the physical-core list to start pinning from")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--resume", action="store_true")
    a = ap.parse_args()
    cores = physical_cores()
    need = a.first_core + 2 * a.pairs
    if need > len(cores):
        sys.exit(f"need {need} physical cores, have {len(cores)}")
    done = set()
    if a.resume and a.out.exists():
        done = {r["name"] for r in csv.DictReader(open(a.out))}
    todo = [(s, p) for s, p in graphs(a.sets, a.rome_sample, a.seed, a.sample) if str(p.relative_to(INST)) not in done]
    print(f"{time.strftime('%F %T')} sage_paired: {len(todo)} graphs ({len(done)} done), cap {a.cap:.0f} s CPU, "
          f"{a.pairs} pairs on physical cores {cores[a.first_core:need]}, load {os.getloadavg()[0]:.1f}", flush=True)
    new = not a.out.exists() or a.out.stat().st_size == 0
    slots = [(cores[a.first_core + 2 * i], cores[a.first_core + 2 * i + 1]) for i in range(a.pairs)]
    k = 0
    import queue, threading
    q: "queue.Queue" = queue.Queue()
    for item in todo:
        q.put(item)
    lock = threading.Lock()
    with open(a.out, "a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        if new:
            w.writeheader()

        def worker(slot):            # one worker per core pair; it owns its two cores for the whole run
            nonlocal k
            while True:
                try:
                    s_, p_ = q.get_nowait()
                except queue.Empty:
                    return
                row = run_pair((s_, p_, a.cap, slot[0], slot[1]))
                with lock:
                    w.writerow(row); fh.flush(); k += 1
                    print(f"{time.strftime('%T')} {k}/{len(todo)} {row['name'][:40]:40} n={row['n']:>4} | ours w={row['ours_width']} "
                          f"{row['ours_proof']:10} {row['ours_wall']}s nodes {row['ours_nodes']} | sage w={row['sage_width']} "
                          f"{row['sage_status']:7} cpu {row['sage_cpu']}s | load {row['load1']}", flush=True)

        threads = [threading.Thread(target=worker, args=(slots[i],)) for i in range(a.pairs)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
    print(f"{time.strftime('%F %T')} done: {k} graphs", flush=True)


if __name__ == "__main__":
    main()
