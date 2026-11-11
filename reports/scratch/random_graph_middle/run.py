"""The middle-regime measurement: exact pathwidth of G(n, p) with np growing (2026-11-11).

Cells: n in {30, 40, 50, 60}; c = np in {2 ln n, sqrt n, n^0.7} (the middle regime) and the
dense control p = 1/2. The sparse control c = 3 is NOT run here: the pilot
(reports/scratch/gnp_pilot/results.csv) already holds 136-137 proved graphs per n at c = 3,
and the owner's rule sends compute to unsolved instances; the report takes its first 20
samples per n from there. 20 graphs per cell, seeds recorded (distinct from the pilot's
scheme, so no graph is re-solved), each to the C program pathwidth_solver/cli/pathwidth
with -t 600 (a censored run is a bracket [lower, width], not a value).
    nice -n 19 python3 reports/scratch/random_graph_middle/run.py --procs 6
Output (resumable by key): results.csv with the graph6 string and the witness layout.
"""
import argparse, csv, math, subprocess, time, threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import networkx as nx

HERE = Path(__file__).resolve().parent
BIN = HERE.parents[2] / "pathwidth_solver/cli/pathwidth"
OUT = HERE / "results.csv"
NS = [30, 40, 50, 60]
FAMILIES = {"2lnn": lambda n: 2 * math.log(n), "sqrtn": lambda n: math.sqrt(n),
            "n07": lambda n: n ** 0.7, "dense": lambda n: 0.5 * n}
SAMPLES = 20
FIELDS = ["family", "n", "c", "p", "sample", "seed", "m", "components", "width", "status",
          "lower", "nodes", "seconds", "g6", "layout"]


def jobs():
    for s in range(SAMPLES):
        for n in NS:
            for fi, (fam, cf) in enumerate(FAMILIES.items()):
                c = cf(n)
                yield fam, n, c, s, 7_000_017 * n + 1_013 * (fi + 1) + 101 * s + 42


def one(fam, n, c, s, seed, cap):
    p = c / n
    G = nx.gnp_random_graph(n, p, seed=seed)
    g6 = nx.to_graph6_bytes(G, header=False)
    t = time.time()
    row = dict(family=fam, n=n, c=round(c, 6), p=round(p, 8), sample=s, seed=seed,
               m=G.number_of_edges(), components=nx.number_connected_components(G), width="",
               status="", lower="", nodes="", seconds="", g6=g6.decode().strip(), layout="")
    try:
        pr = subprocess.run([str(BIN), "-t", str(cap), "-l", "-v"], input=g6,
                            capture_output=True, timeout=cap + 60)
        out = pr.stdout.decode().split("\n")
        _, w, st = out[0].split()
        err = dict(kv.split("=") for kv in pr.stderr.decode().split() if "=" in kv)
        row.update(width=int(w), status=st, lower=err.get("lower", ""), nodes=err.get("nodes", ""),
                   seconds=round(time.time() - t, 3),
                   layout=out[1].split(" ", 1)[1] if len(out) > 1 and out[1] else "")
    except subprocess.TimeoutExpired:
        row.update(status="killed", seconds=round(time.time() - t, 3))
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--procs", type=int, default=6)
    ap.add_argument("--cap", type=float, default=600)
    a = ap.parse_args()
    done = ({(r["family"], int(r["n"]), int(r["sample"])) for r in csv.DictReader(open(OUT))}
            if OUT.exists() else set())
    new = not OUT.exists()
    f = open(OUT, "a", newline="")
    w = csv.DictWriter(f, FIELDS)
    if new:
        w.writeheader(); f.flush()
    lock = threading.Lock()
    it = (j for j in jobs() if (j[0], j[1], j[3]) not in done)

    def worker():
        while True:
            with lock:
                j = next(it, None)
            if j is None:
                return
            row = one(*j, a.cap)
            with lock:
                w.writerow(row); f.flush()

    with ThreadPoolExecutor(a.procs) as ex:
        for _ in range(a.procs):
            ex.submit(worker)
    f.close()


if __name__ == "__main__":
    main()
