"""Shared plotting style and DDPM helpers for the showcase figures (illustrations, not proofs).

Not imported by tests/: the showcase needs numpy and matplotlib, which CI does not install.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

FIG_DIR = Path(__file__).resolve().parent / "figures"

# Categorical slots in fixed order (validated reference palette), plus text/grid inks.
BLUE = "#2a78d6"
ORANGE = "#eb6834"
AQUA = "#1baf7a"
YELLOW = "#eda100"
MAGENTA = "#e87ba4"
GREEN = "#008300"
VIOLET = "#6250d6"
RED = "#e34948"
SERIES = [BLUE, ORANGE, AQUA, YELLOW, MAGENTA, GREEN, VIOLET, RED]
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#8a8984"
GRID = "#e4e3df"
SURFACE = "#fcfcfb"


def setup() -> None:
    plt.rcParams.update(
        {
            "figure.facecolor": SURFACE,
            "axes.facecolor": SURFACE,
            "savefig.facecolor": SURFACE,
            "axes.edgecolor": MUTED,
            "axes.labelcolor": INK2,
            "axes.titlecolor": INK,
            "axes.titlesize": 12,
            "axes.titleweight": "bold",
            "axes.labelsize": 10.5,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "grid.color": GRID,
            "grid.linewidth": 0.8,
            "xtick.color": INK2,
            "ytick.color": INK2,
            "xtick.labelsize": 9.5,
            "ytick.labelsize": 9.5,
            "legend.frameon": False,
            "legend.fontsize": 9.5,
            "lines.linewidth": 2.0,
            "font.size": 10.5,
            "figure.dpi": 110,
        }
    )


def save(fig, name: str) -> Path:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    path = FIG_DIR / name
    fig.savefig(path, dpi=160, bbox_inches="tight")
    plt.close(fig)
    print(f"saved {path.relative_to(FIG_DIR.parent.parent)}")
    return path


def geom_grid(delta: float, horizon: float, n_steps: int) -> np.ndarray:
    """Times t_0 = 0, t_1 = delta, ..., t_N = horizon with u_k = e^{2 t_k} - 1 = u_1 r^{k-1}.

    This is `DiffusionDiscretization.geomGrid u1 r` with u_1 = e^{2 delta} - 1 and r chosen so
    that t_N = horizon. Returns the array (t_0, ..., t_N) and is valid for n_steps >= 2.
    """
    u1 = np.expm1(2 * delta)
    un = np.expm1(2 * horizon)
    r = (un / u1) ** (1.0 / (n_steps - 1))
    u = u1 * r ** np.arange(n_steps)
    return np.concatenate([[0.0], 0.5 * np.log1p(u)])


def grid_ratio(delta: float, horizon: float, n_steps: int) -> float:
    return (np.expm1(2 * horizon) / np.expm1(2 * delta)) ** (1.0 / (n_steps - 1))
