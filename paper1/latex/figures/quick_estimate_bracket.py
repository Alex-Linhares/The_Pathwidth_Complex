"""Figure (c) of reports/quick_estimate.md: the bracket on random graphs (2026-11-12).

    nice -n 19 python3 -m learning.quick_estimate summarise      # -> paper1/latex/data/quick_estimate_bracket.csv
    python3 paper1/latex/figures/quick_estimate_bracket.py        # -> paper1/figures/quick_estimate_bracket.pdf

Four panels on one axis (pathwidth against `n`): the `G(n, c/n)` pilot cells at `c = 3`,
`6` and `10` (`n = 20-120`, every width proved) and the dense cells `p = 1/2`
(`n = 30-60`).  Per cell the floor (first-moment inequality at level 0.05, blue) and the
ceiling (the smaller of the random-ordering width and `n - alpha_greedy`, orange) as
medians, the proved pathwidth as a median dot with its min-max whisker (ink), and the
recipe's point estimate as a blue hollow square (min-fill treewidth on the sparse cells,
the corner-block threshold `n - s_block + 1` on the dense ones).
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from quick_estimate_style import BLUE, DATA, INK, INK2, INK3, ORANGE, RULE, clean, save, setup  # noqa: E402

DATA_CSV = DATA / "quick_estimate_bracket.csv"
CELLS = [("c=3", "G(n, c/n), c = 3"), ("c=6", "G(n, c/n), c = 6"), ("c=10", "G(n, c/n), c = 10"),
         ("dense", "G(n, p), p = 1/2")]


def draw(data: Path = DATA_CSV):
    plt = setup()
    rows = list(csv.DictReader(open(data)))
    fig, axes = plt.subplots(1, 4, figsize=(7.2, 3.1))
    for ax, (cell, title) in zip(axes, CELLS):
        sub = sorted((r for r in rows if r["cell"] == cell), key=lambda r: int(r["n"]))
        ns = [int(r["n"]) for r in sub]
        ax.fill_between(ns, [float(r["floor_median"]) for r in sub], [float(r["ceiling_median"]) for r in sub],
                        color="#f1f0eb", lw=0, zorder=1)
        ax.plot(ns, [float(r["floor_median"]) for r in sub], color=BLUE, lw=1.8, zorder=2)
        ax.plot(ns, [float(r["ceiling_median"]) for r in sub], color=ORANGE, lw=1.8, zorder=2)
        ax.plot(ns, [float(r["recipe_median"]) for r in sub], ls="none", marker="s", ms=4.5, mfc="white", mec=BLUE,
                mew=1.4, zorder=4)
        for r in sub:
            n = int(r["n"])
            ax.plot([n, n], [int(r["truth_min"]), int(r["truth_max"])], color=INK, lw=1.1, zorder=3)
            ax.plot([n], [float(r["truth_median"])], marker="o", ms=4, color=INK, ls="none", zorder=5)
        ax.set_title(title, loc="left", color=INK)
        ax.set_xlabel("n", color=INK2)
        ax.set_ylim(0, None)
        clean(ax)
        last = sub[-1]
        ax.annotate("ceiling", (int(last["n"]), float(last["ceiling_median"])), xytext=(3, 0),
                    textcoords="offset points", fontsize=6.5, color=ORANGE, va="center")
        ax.annotate("floor", (int(last["n"]), float(last["floor_median"])), xytext=(3, 0),
                    textcoords="offset points", fontsize=6.5, color=BLUE, va="center")
        ax.set_xlim(ns[0] - 5, ns[-1] + 24)
    axes[0].set_ylabel("pathwidth", color=INK2)
    from matplotlib.lines import Line2D
    handles = [Line2D([], [], marker="o", color=INK, ls="none", ms=4, label="proved pathwidth: median, min–max"),
               Line2D([], [], marker="s", mfc="white", mec=BLUE, mew=1.4, ls="none", ms=4.5,
                      label="recipe (median): min-fill tw, or n − s_block + 1 at p = ½"),
               Line2D([], [], color=BLUE, lw=1.8, label="floor: first moment at 0.05"),
               Line2D([], [], color=ORANGE, lw=1.8, label="ceiling: min(random ordering, n − α_greedy)")]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.005, 0.94), ncol=2, frameon=False,
               fontsize=7, handletextpad=0.4, columnspacing=1.6, labelcolor=INK2)
    fig.text(0.01, 0.985, "The bracket on random graphs: the theorems' floor and ceiling against proved pathwidths",
             fontsize=9.5, color=INK, ha="left", va="top")
    fig.tight_layout(rect=(0, 0, 1, 0.82))
    return save(fig, "quick_estimate_bracket")


if __name__ == "__main__":
    print(*draw())
