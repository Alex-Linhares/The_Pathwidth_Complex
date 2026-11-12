"""Figure (a) of reports/quick_estimate.md: the quick estimate against the proved value,
one panel per regime (2026-11-12).

    nice -n 19 python3 -m learning.quick_estimate summarise      # -> paper1/latex/data/quick_estimate_truth.csv
    python3 paper1/latex/figures/quick_estimate_truth.py          # -> paper1/figures/quick_estimate_truth.pdf

One dot per occupied cell (proved pathwidth, estimate), its area proportional to the
number of certified instances in the cell; the identity line in the rule colour.  One panel per generator or
regime (identity is carried by the panel, not by hue: a scatter with more than three
hues fails the all-pairs colour gate).  Three instances per panel, at the quartiles of
`n`, show their bracket `[floor, ceiling]` as a vertical bar in orange.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from quick_estimate_style import BLUE, DATA, INK, INK2, INK3, ORANGE, RULE, clean, save, setup  # noqa: E402

DATA_CSV = DATA / "quick_estimate_truth.csv"
BRACKETS_CSV = DATA / "quick_estimate_truth_brackets.csv"
PANELS = ["Chu & Stuckey", "Harvey", "Faggioli-Bentivoglio", "Simonis", "ensembles n <= 40", "ensembles 50-100",
          "G(n, c/n)", "G(n, p), p = 1/2", "Rome graphs"]


def draw(data: Path = DATA_CSV, brackets: Path = BRACKETS_CSV):
    import numpy as np
    plt = setup()
    rows = list(csv.DictReader(open(data)))
    bracket_rows = list(csv.DictReader(open(brackets)))
    fig, axes = plt.subplots(3, 3, figsize=(7.2, 7.4))
    for ax, panel in zip(axes.flat, PANELS):
        sub = [r for r in rows if r["panel"] == panel]
        x = np.array([int(r["truth"]) for r in sub], dtype=float)
        y = np.array([int(r["recipe"]) for r in sub], dtype=float)
        w = np.array([int(r["count"]) for r in sub], dtype=float)
        total = int(w.sum())
        top = max(x.max(), y.max()) + 1 if len(sub) else 10
        ax.plot([0, top], [0, top], color=RULE, lw=1, zorder=1)
        ax.scatter(x, y, s=2.5 + 60 * w / w.max(), color=BLUE, alpha=0.55, lw=0, zorder=2)
        # three brackets at the quartiles of n
        for r in (b for b in bracket_rows if b["panel"] == panel):
            lo, hi, t = int(r["floor"]), int(r["ceiling"]), int(r["truth"])
            ax.plot([t, t], [lo, hi], color=ORANGE, lw=2.2, solid_capstyle="butt", zorder=3)
            ax.plot([t], [int(r["recipe"])], marker="o", ms=4, mfc="white", mec=ORANGE, mew=1.4, ls="none", zorder=4)
        exact = float(np.sum(w * (x == y)) / total) if total else 0.0
        mae = float(np.sum(w * np.abs(x - y)) / total) if total else 0.0
        ax.set_title(f"{panel}  ({total:,})", loc="left", color=INK)
        ax.text(0.97, 0.04, f"exact {exact:.0%}, MAE {mae:.2f}", transform=ax.transAxes, ha="right", va="bottom",
                fontsize=7, color=INK2)
        ax.set_xlim(-0.5, top)
        ax.set_ylim(-0.5, top)
        ax.set_aspect("equal")
        clean(ax, grid="")
    for ax in axes[-1]:
        ax.set_xlabel("proved pathwidth", color=INK2)
    for ax in axes[:, 0]:
        ax.set_ylabel("quick estimate", color=INK2)
    fig.text(0.01, 0.985, "The quick estimate against the proved value: every certified instance, one panel per regime",
             fontsize=9.5, color=INK, ha="left", va="top")
    fig.text(0.01, 0.962, "blue: dot area = number of instances in the cell (identity line in grey)\n"
             "orange bars: the bracket [floor, ceiling] of three instances per panel, at the quartiles of n",
             fontsize=7.5, color=INK3, ha="left", va="top", linespacing=1.3)
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    return save(fig, "quick_estimate_truth")


if __name__ == "__main__":
    print(*draw())
