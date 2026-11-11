"""The middle regime of G(n, p): exact pathwidth against the first-moment floors (2026-11-11).

    python3 paper1/latex/figures/random_graph_middle.py extract   # -> paper1/latex/data/random_graph_middle.csv
    python3 paper1/latex/figures/random_graph_middle.py draw      # -> paper1/figures/random_graph_middle.{pdf,png}
    python3 paper1/latex/figures/random_graph_middle.py           # both

`extract` reads the measurement `reports/scratch/random_graph_middle/results.csv` (n in
{30, 40, 50, 60}; c = np in {2 ln n, sqrt n, n^0.7} and the dense control p = 1/2; 20 graphs
per cell, every pathwidth proved by the C program) and the sparse control c = 3 from the
pilot `reports/scratch/gnp_pilot/results.csv` (its first 20 samples per n, proved there),
and writes one row per cell: the proved pathwidths (min, median, max; a censored graph
would contribute its bracket, none did), the floors -- Theorem M `(1 - 4 ln c / c) n`,
Theorem A's constant `beta*(c) n`, the finite inequality evaluated exactly (`k_05`, the
largest k with C(n,t) C(n-t,t-1) (1-p)^(t(t-1)) <= 0.05, so pw > k_05 with probability at
least 0.95), Theorem B's `n - 4 log_b n` where p is constant -- and the ceilings, the
independence bound `n - alpha(G)` (exact alpha by branch and bound) and the
Edwards-McDermid degree-sequence term (the histogram term of Corollary 5.2, per graph, and
its Poisson limit per vertex). `draw` reads that CSV and nothing else.
"""
from __future__ import annotations

import csv
import math
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
RESULTS = ROOT / "reports" / "scratch" / "random_graph_middle" / "results.csv"
PILOT = ROOT / "reports" / "scratch" / "gnp_pilot" / "results.csv"
DATA_CSV = ROOT / "paper1" / "latex" / "data" / "random_graph_middle.csv"
OUT_PDF = ROOT / "paper1" / "figures" / "random_graph_middle.pdf"
OUT_PNG = ROOT / "reports" / "figures" / "random_graph_middle.png"

# the reference palette: slot 1 (blue) for floors, slot 2 (orange) for ceilings, ink for the data
BLUE, ORANGE = "#2a78d6", "#eb6834"
INK, INK2, INK3, RULE = "#0b0b0b", "#52514e", "#9a9994", "#c3c2b7"

FIELDS = ["family", "n", "c", "p", "graphs", "proved", "pw_min", "pw_median", "pw_max", "pw_mean",
          "thmM", "thmM_prime", "beta_star", "k05", "thmB", "alpha_mean", "n_minus_alpha_mean",
          "em_hist_mean", "em_poisson", "seconds_total"]


# ----------------------------------------------------------------------------
# the floors
# ----------------------------------------------------------------------------

def phi(x: float) -> float:
    return 0.0 if x <= 0 else -x * math.log(x)


def beta_star(c: float) -> float:
    """Theorem A': the root in (0, 1) of -(1-b) ln((1-b)/2) - b ln b = c (1-b)^2 / 4; 0 below 4 ln 2."""
    if c <= 4 * math.log(2):
        return 0.0
    g = lambda a: 2 * phi(a) + phi(1 - 2 * a) - c * a * a
    lo, hi = 1e-12, 0.5          # g > 0 near 0, g(1/2) < 0, unique root (strict concavity)
    for _ in range(200):
        mid = (lo + hi) / 2
        if g(mid) > 0:
            lo = mid
        else:
            hi = mid
    return 1 - 2 * hi


def log_binom(n: int, k: int) -> float:
    if k < 0 or k > n:
        return -math.inf
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def log_rhs0(n: int, k: int, p: float) -> float:
    """ln of C(n,t) C(n-t,t-1) (1-p)^(t(t-1)), t = ceil((n-k)/2): the finite inequality (0)."""
    t = (n - k + 1) // 2
    m = t * (t - 1)
    lb = log_binom(n, t) + log_binom(n - t, t - 1)
    if p >= 1.0:
        return lb if m == 0 else -math.inf
    return lb + m * math.log1p(-p)


def k05(n: int, p: float, level: float = 0.05) -> int:
    """The largest k < n with the finite bound at most `level` (-1 if none)."""
    best = -1
    for k in range(n):
        if log_rhs0(n, k, p) <= math.log(level):
            best = k
    return best


def thm_m(n: int, c: float) -> float | None:
    """Theorem M's floor (1 - 4 ln c / c) n, where it is positive (c > 8.61)."""
    b = 1 - 4 * math.log(c) / c
    return b * n if b > 0 else None


def thm_m_prime(n: int, c: float) -> float | None:
    """The sharper on-paper form, the upper end of Theorem A'' (c >= 14):
    (1 - (4 ln c - 4 ln ln c + 4 ln 2 + 4) / c) n."""
    if c < 14:
        return None
    b = 1 - (4 * math.log(c) - 4 * math.log(math.log(c)) + 4 * math.log(2) + 4) / c
    return b * n if b > 0 else None


# ----------------------------------------------------------------------------
# the ceilings
# ----------------------------------------------------------------------------

def independence_number(adj: list[int], n: int) -> int:
    """Exact alpha(G) by branch and bound on bit masks (n <= 64): pendant and isolated
    vertices are taken, otherwise branch on a vertex of largest degree."""
    best = 0
    sys.setrecursionlimit(10000)

    def rec(rem: int, size: int) -> None:
        nonlocal best
        if rem == 0:
            best = max(best, size)
            return
        if size + bin(rem).count("1") <= best:
            return
        # isolated or pendant vertices in G[rem] go in
        r = rem
        while r:
            v = (r & -r).bit_length() - 1
            r &= r - 1
            d = bin(adj[v] & rem).count("1")
            if d <= 1:
                rec(rem & ~(adj[v] | (1 << v)), size + 1)
                return
        # branch on a vertex of largest degree
        r, vmax, dmax = rem, -1, -1
        while r:
            v = (r & -r).bit_length() - 1
            r &= r - 1
            d = bin(adj[v] & rem).count("1")
            if d > dmax:
                vmax, dmax = v, d
        rec(rem & ~(adj[vmax] | (1 << vmax)), size + 1)
        rec(rem & ~(1 << vmax), size)

    rec((1 << n) - 1, 0)
    return best


# ----------------------------------------------------------------------------
# extract
# ----------------------------------------------------------------------------

def _rows() -> list[dict]:
    from learning.edwards_mcdermid import histogram_term, parse_g6, poisson_value
    import networkx as nx
    rows: list[dict] = []
    for r in csv.DictReader(open(RESULTS)):
        n, adj = parse_g6(r["g6"])
        rows.append(dict(family=r["family"], n=int(r["n"]), c=float(r["c"]), p=float(r["p"]),
                         status=r["status"], width=int(r["width"]), lower=int(r["lower"] or 0),
                         seconds=float(r["seconds"]), adj=adj))
    # the sparse control from the pilot: samples 0-19 at c = 3, regenerated from the recorded seed
    for r in csv.DictReader(open(PILOT)):
        if r["c"] != "3" or int(r["n"]) not in (30, 40, 50, 60) or int(r["sample"]) >= 20:
            continue
        n = int(r["n"])
        G = nx.gnp_random_graph(n, 3 / n, seed=int(r["seed"]))
        assert G.number_of_edges() == int(r["m"]), "the pilot seed does not regenerate its graph"
        adj = [0] * n
        for u, v in G.edges():
            adj[u] |= 1 << v
            adj[v] |= 1 << u
        rows.append(dict(family="c3", n=n, c=3.0, p=3 / n, status=r["status"], width=int(r["width"]),
                         lower=int(r["lower"] or 0), seconds=float(r["seconds"]), adj=adj))
    for r in rows:
        r["alpha"] = independence_number(r["adj"], r["n"])
        r["em_hist"] = float(histogram_term(r["adj"]))
    return rows


def extract(out: Path = DATA_CSV) -> list[dict]:
    from learning.edwards_mcdermid import poisson_value
    rows = _rows()
    cells: dict[tuple, list[dict]] = {}
    for r in rows:
        cells.setdefault((r["family"], r["n"]), []).append(r)
    order = {"c3": 0, "2lnn": 1, "sqrtn": 2, "n07": 3, "dense": 4}
    table: list[dict] = []
    for (fam, n), rs in sorted(cells.items(), key=lambda kv: (kv[0][1], order[kv[0][0]])):
        c, p = rs[0]["c"], rs[0]["p"]
        proved = [r for r in rs if r["status"] in ("refutation", "bound", "minor")]
        # a censored graph is a bracket [lower, width]: min uses lower, max uses width
        lo = [r["width"] if r in proved else r["lower"] for r in rs]
        hi = [r["width"] for r in rs]
        med = sorted(hi)
        median = (med[len(med) // 2 - 1] + med[len(med) // 2]) / 2 if len(med) % 2 == 0 else med[len(med) // 2]
        b = 1 / (1 - p)
        table.append(dict(
            family=fam, n=n, c=round(c, 4), p=round(p, 6), graphs=len(rs), proved=len(proved),
            pw_min=min(lo), pw_median=median, pw_max=max(hi), pw_mean=round(sum(hi) / len(hi), 3),
            thmM=None if thm_m(n, c) is None else round(thm_m(n, c), 3),
            thmM_prime=None if thm_m_prime(n, c) is None else round(thm_m_prime(n, c), 3),
            beta_star=round(beta_star(c) * n, 3), k05=k05(n, p),
            thmB=round(n - 4 * math.log(n) / math.log(b), 3) if fam == "dense" else None,
            alpha_mean=round(sum(r["alpha"] for r in rs) / len(rs), 3),
            n_minus_alpha_mean=round(sum(n - r["alpha"] for r in rs) / len(rs), 3),
            em_hist_mean=round(sum(r["em_hist"] for r in rs) / len(rs), 3),
            em_poisson=round(poisson_value(c) * n, 3),
            seconds_total=round(sum(r["seconds"] for r in rs), 3)))
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, FIELDS)
        w.writeheader()
        for t in table:
            w.writerow({k: ("" if t[k] is None else t[k]) for k in FIELDS})
    return table


# ----------------------------------------------------------------------------
# draw
# ----------------------------------------------------------------------------

def draw(data: Path = DATA_CSV, out_pdf: Path = OUT_PDF, out_png: Path = OUT_PNG) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    table = list(csv.DictReader(open(data)))
    ns = sorted({int(t["n"]) for t in table})
    fig, axes = plt.subplots(1, len(ns), figsize=(11, 3.4), sharey=True)
    cs = np.exp(np.linspace(math.log(2.5), math.log(32), 400))
    for ax, n in zip(axes, ns):
        rows = [t for t in table if int(t["n"]) == n]
        # floors, blue: Theorem M (solid), beta*(c) (dashed), the finite inequality exactly (squares)
        ax.plot(cs, [max(0, 1 - 4 * math.log(c) / c) for c in cs], color=BLUE, lw=2, zorder=2)
        ax.plot(cs, [beta_star(c) for c in cs], color=BLUE, lw=1.4, ls=(0, (4, 2)), zorder=2)
        ax.plot([float(t["c"]) for t in rows], [int(t["k05"]) / n for t in rows], ls="none",
                marker="s", ms=5, mfc="white", mec=BLUE, mew=1.6, zorder=3)
        # ceilings, orange: n - alpha (triangles) and the degree-sequence term (diamonds)
        ax.plot([float(t["c"]) for t in rows], [float(t["n_minus_alpha_mean"]) / n for t in rows],
                ls="none", marker="^", ms=6, mfc="white", mec=ORANGE, mew=1.6, zorder=3)
        ax.plot([float(t["c"]) for t in rows], [float(t["em_hist_mean"]) / n for t in rows],
                ls="none", marker="D", ms=5, mfc="white", mec=ORANGE, mew=1.6, zorder=3)
        # the data, ink: median with the min-max whisker
        for t in rows:
            c = float(t["c"])
            ax.plot([c, c], [int(t["pw_min"]) / n, int(t["pw_max"]) / n], color=INK, lw=1.2, zorder=4)
            ax.plot([c], [float(t["pw_median"]) / n], marker="o", ms=5.5, color=INK, ls="none", zorder=5)
        ax.set_xscale("log")
        ax.set_xlim(2.5, 32)
        ax.set_ylim(0, 1)
        ax.set_xticks([3, 5, 10, 20, 30])
        ax.set_xticklabels(["3", "5", "10", "20", "30"])
        ax.set_title(f"n = {n}", fontsize=10, color=INK, loc="left")
        ax.set_xlabel("c = np", fontsize=9, color=INK2)
        ax.grid(axis="y", color=RULE, lw=0.5)
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        for s in ("left", "bottom"):
            ax.spines[s].set_color(RULE)
        ax.tick_params(colors=INK2, labelsize=8)
        # the cells, named once (sqrt n sits below its whisker: its c is next to 2 ln n)
        for t in rows:
            lab = {"c3": "c = 3", "2lnn": "2 ln n", "sqrtn": "√n", "n07": "n^0.7", "dense": "p = ½"}[t["family"]]
            if t["family"] == "sqrtn":
                ax.annotate(lab, (float(t["c"]), int(t["pw_min"]) / n), xytext=(0, -9),
                            textcoords="offset points", ha="center", fontsize=6.5, color=INK3)
            else:
                ax.annotate(lab, (float(t["c"]), int(t["pw_max"]) / n), xytext=(0, 5),
                            textcoords="offset points", ha="center", fontsize=6.5, color=INK3)
    axes[0].set_ylabel("value / n", fontsize=9, color=INK2)
    # the two curves, labelled directly in the first panel where the lower right is free
    ax = axes[0]
    ax.annotate("Theorem M: 1 − 4 ln c / c", (20, 1 - 4 * math.log(20) / 20), xytext=(2, -14),
                textcoords="offset points", ha="center", fontsize=7.5, color=BLUE)
    ax.annotate("β*(c), Theorem A", (6.5, beta_star(6.5)), xytext=(6, -10), textcoords="offset points",
                ha="left", fontsize=7.5, color=BLUE)
    # the marks, in a legend row under the title
    from matplotlib.lines import Line2D
    handles = [
        Line2D([], [], marker="o", color=INK, ls="none", ms=5.5, label="exact pathwidth: median, min–max"),
        Line2D([], [], marker="s", mfc="white", mec=BLUE, mew=1.6, ls="none", ms=5,
               label="finite inequality, exact: largest k with P(pw ≤ k) ≤ 0.05"),
        Line2D([], [], marker="^", mfc="white", mec=ORANGE, mew=1.6, ls="none", ms=6, label="n − α(G), mean"),
        Line2D([], [], marker="D", mfc="white", mec=ORANGE, mew=1.6, ls="none", ms=5,
               label="degree-sequence term, mean"),
    ]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.005, 0.95), ncol=4, frameon=False,
               fontsize=7.5, handletextpad=0.4, columnspacing=1.6, labelcolor=INK2)
    fig.suptitle("Pathwidth of G(n, c/n) with c growing: floors (blue), ceilings (orange), proved values (ink)",
                 fontsize=10, color=INK, x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.88))
    out_pdf.parent.mkdir(parents=True, exist_ok=True)
    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_pdf)
    fig.savefig(out_png, dpi=160)


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "both"
    if what in ("extract", "both"):
        t = extract()
        for r in t:
            print({k: r[k] for k in FIELDS if k not in ("seconds_total",)})
    if what in ("draw", "both"):
        draw()
