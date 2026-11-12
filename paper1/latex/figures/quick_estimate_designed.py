"""Figure (d) of reports/quick_estimate.md: distance from random, the designed sets and
the graph collections (2026-11-12).

    nice -n 19 python3 -m learning.quick_estimate summarise      # -> paper1/latex/data/quick_estimate_designed.csv
    python3 paper1/latex/figures/quick_estimate_designed.py       # -> paper1/figures/quick_estimate_designed.pdf

A labelled dot plot, one row per collection: the mean of `proved pathwidth - estimate`
(the owner's sign: the cages above, SCOOP below) as a dot with the interquartile bar,
sorted.  Above zero the graph has *more* pathwidth than the random model predicts
from its parameters (expansion beyond random: the cages); below zero it has *less*
(small separators the random model cannot see: grids, meshes, planar graphs, and the
SCOOP covers).  Collections whose record is an upper bound only (the five cages, the
`solution` records) are drawn hollow: their true distance is at most the one shown.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from quick_estimate_style import BLUE, DATA, INK, INK2, INK3, RULE, clean, save, setup  # noqa: E402

DATA_CSV = DATA / "quick_estimate_designed.csv"


def draw(data: Path = DATA_CSV):
    plt = setup()
    rows = list(csv.DictReader(open(data)))
    rows.sort(key=lambda r: -float(r["recipe_bias"]))
    fig, ax = plt.subplots(figsize=(7.2, 0.26 * len(rows) + 1.3))
    for i, r in enumerate(rows):
        # the table stores estimate - truth; the plot shows truth - estimate
        bias, q25, q75 = -float(r["recipe_bias"]), -float(r["q75"]), -float(r["q25"])
        upper = r["truth_is_upper"] == "True"
        ax.plot([q25, q75], [i, i], color=BLUE, lw=2, alpha=0.45, solid_capstyle="butt", zorder=2)
        ax.plot([bias], [i], marker="o", ms=6, mfc="white" if upper else BLUE, mec=BLUE, mew=1.5, ls="none", zorder=3)
        label = f"{r['group']}  (n = {float(r['n_median']):.0f}, {int(r['count'])})"
        ax.text(-0.3, i, label, ha="right", va="center", fontsize=7, color=INK2, transform=ax.get_yaxis_transform())
    ax.axvline(0, color=RULE, lw=0.9, zorder=1)
    ax.set_yticks([])
    ax.set_ylim(-0.8, len(rows) - 0.2)
    ax.set_xlabel("proved pathwidth − quick estimate (mean; bar: interquartile range)", color=INK2, fontsize=7.5)
    ax.set_xscale("symlog", linthresh=10)
    ax.set_xticks([-100, -50, -20, -10, -5, 0, 5, 10])
    ax.set_xticklabels(["−100", "−50", "−20", "−10", "−5", "0", "5", "10"])
    clean(ax, grid="x")
    ax.spines["left"].set_visible(False)
    xmin, xmax = ax.get_xlim()
    ax.text(xmax, -0.6, "more than random →", ha="right", va="bottom", fontsize=6.8, color=INK3)
    ax.text(xmin, -0.6, "← less pathwidth than random", ha="left", va="bottom", fontsize=6.8, color=INK3)
    fig.text(0.01, 0.985, "Distance from random: the designed sets and the graph collections (hollow: record is an "
             "upper bound only)", fontsize=9.5, color=INK, ha="left", va="top")
    fig.tight_layout(rect=(0.0, 0, 0.98, 0.95))
    return save(fig, "quick_estimate_designed")


if __name__ == "__main__":
    print(*draw())
