"""Shared style of the four `quick_estimate_*` figures (2026-11-12): the reference
palette of the dataviz method (categorical slots 1-3, validated all-pairs; inks;
rule), the axis treatment, and the output paths.  Figures are drawn for print at
column width; PDFs go to `paper1/figures/` (where the LaTeX includes them) and PNGs to
`reports/figures/`."""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DATA = ROOT / "paper1" / "latex" / "data"
FIG_PDF = ROOT / "paper1" / "figures"
FIG_PNG = ROOT / "reports" / "figures"

BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"   # slots 1-3
INK, INK2, INK3, RULE = "#0b0b0b", "#52514e", "#9a9994", "#c3c2b7"
BAND = "#f1f0eb"


def setup():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size": 8, "axes.titlesize": 9, "axes.labelsize": 8.5,
                         "xtick.labelsize": 7.5, "ytick.labelsize": 7.5, "pdf.fonttype": 42})
    return plt


def clean(ax, grid: str = "y"):
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    for s in ("left", "bottom"):
        ax.spines[s].set_color(RULE)
    ax.tick_params(colors=INK2, length=3)
    if grid:
        ax.grid(axis=grid, color=RULE, lw=0.5)
        ax.set_axisbelow(True)


def save(fig, stem: str):
    FIG_PDF.mkdir(parents=True, exist_ok=True)
    FIG_PNG.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIG_PDF / f"{stem}.pdf")
    fig.savefig(FIG_PNG / f"{stem}.png", dpi=170)
    return FIG_PDF / f"{stem}.pdf", FIG_PNG / f"{stem}.png"
