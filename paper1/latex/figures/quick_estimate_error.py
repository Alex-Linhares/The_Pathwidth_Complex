"""Figure (b) of reports/quick_estimate.md: the signed error against the size band, the
recipe beside min-fill treewidth (2026-11-12).

    nice -n 19 python3 -m learning.quick_estimate summarise      # -> paper1/latex/data/quick_estimate_error.csv
    python3 paper1/latex/figures/quick_estimate_error.py          # -> paper1/figures/quick_estimate_error.pdf

One panel per kind of record (the MOSP corpus, the generated ensembles, the random
graphs, the graph collections), the size band on the horizontal axis, the signed error
`estimate - proved pathwidth` on the vertical: the median as a dot and the interquartile
range as a bar, the recipe in blue and min-fill treewidth in orange, side by side.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from quick_estimate_style import BLUE, DATA, INK, INK2, INK3, ORANGE, RULE, clean, save, setup  # noqa: E402

DATA_CSV = DATA / "quick_estimate_error.csv"
KINDS = [("mosp", "MOSP corpus"), ("ensemble", "generated ensembles"), ("gnp", "random graphs G(n, p)"),
         ("graph", "graph collections")]
BANDS = ["0-20", "21-40", "41-60", "61-100", "101-125", "126+"]


def draw(data: Path = DATA_CSV):
    plt = setup()
    rows = list(csv.DictReader(open(data)))
    fig, axes = plt.subplots(2, 2, figsize=(7.2, 5.2))
    for ax, (kind, title) in zip(axes.flat, KINDS):
        sub = [r for r in rows if r["kind"] == kind]
        bands = [b for b in BANDS if any(r["band"] == b for r in sub)]
        for j, b in enumerate(bands):
            for est, color, dx in (("recipe", BLUE, -0.17), ("tw", ORANGE, 0.17)):
                r = next((r for r in sub if r["band"] == b and r["estimator"] == est), None)
                if r is None:
                    continue
                q25, med, q75 = float(r["q25"]), float(r["median"]), float(r["q75"])
                ax.plot([j + dx, j + dx], [q25, q75], color=color, lw=2.4, solid_capstyle="butt", zorder=2)
                ax.plot([j + dx], [med], marker="o", ms=4.5, color=color, ls="none", zorder=3)
        ax.axhline(0, color=RULE, lw=0.8, zorder=1)
        ax.set_xticks(range(len(bands)))
        counts = {b: next((int(r["count"]) for r in sub if r["band"] == b), 0) for b in bands}
        short = {"0-20": "≤20", "21-40": "21–40", "41-60": "41–60", "61-100": "61–100", "101-125": "101–125",
                 "126+": ">125"}
        ax.set_xticklabels([f"{short[b]}\n{counts[b]:,}" for b in bands], fontsize=6.8)
        ax.set_title(title, loc="left", color=INK)
        ax.set_xlabel("vertices; instances", color=INK2)
        lo = min(float(r["q25"]) for r in sub)
        hi = max(float(r["q75"]) for r in sub)
        cap = 10.0
        ax.set_ylim(min(lo, -1) - 0.5, min(max(hi, 1), cap) + 0.5)
        for r in sub:  # a whisker beyond the cap is clipped and labelled with its value
            if float(r["q75"]) > cap:
                j = bands.index(r["band"])
                dx = -0.17 if r["estimator"] == "recipe" else 0.17
                ax.annotate(f"q75 = {float(r['q75']):.0f}", (j + dx, cap), xytext=(-2, -2), textcoords="offset points",
                            ha="right", va="top", fontsize=6, color=INK2)
        clean(ax)
    for ax in axes[:, 0]:
        ax.set_ylabel("estimate − proved pathwidth", color=INK2)
    from matplotlib.lines import Line2D
    handles = [Line2D([], [], marker="o", color=BLUE, ls="none", ms=4.5, label="the recipe: median, interquartile range"),
               Line2D([], [], marker="o", color=ORANGE, ls="none", ms=4.5, label="min-fill treewidth alone")]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.005, 0.955), ncol=2, frameon=False,
               fontsize=7.5, handletextpad=0.4, columnspacing=1.6, labelcolor=INK2)
    fig.text(0.01, 0.985, "Signed error by size band: the recipe beside min-fill treewidth", fontsize=9.5,
             color=INK, ha="left", va="top")
    fig.tight_layout(rect=(0, 0, 1, 0.92))
    return save(fig, "quick_estimate_error")


if __name__ == "__main__":
    print(*draw())
