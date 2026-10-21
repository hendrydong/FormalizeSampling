"""DF-1: theory vs reality for the DDPM KL bound (illustration, not a proof).

Gaussian data N(m, diag v) in dimension d, exact score, reverse variance beta_k / alpha_k^2
(`ddpmVar`, the variance of the bound), geometric grid. Everything is Gaussian, so the true
KL(p_1 || q_1) of the sampler output is computed in closed form and compared with the
right-hand side of `DiffusionDiscretization.klDiv_output_le_geomGrid` (score error 0):
    initBound_geomGrid + (r - 1) d / 2 (1 + (N - 1) log r).
"""

import numpy as np
from _gauss_ddpm import exact_kl, lean_bound
from _style import BLUE, INK2, MUTED, ORANGE, geom_grid, grid_ratio, plt, save, setup

DELTA = 0.01  # t_1: early-stopping time
SEED = 0


def data(d_max: int):
    rng = np.random.default_rng(SEED)
    m = rng.normal(size=d_max)
    v = np.exp(rng.uniform(np.log(0.05), np.log(2.0), size=d_max))
    return m, v


def truth_and_bound(m, v, horizon, n_steps):
    t = geom_grid(DELTA, horizon, n_steps)
    r = grid_ratio(DELTA, horizon, n_steps)
    init, disc = lean_bound(m, v, DELTA, r, n_steps)
    return exact_kl(m, v, t), init, disc


def main() -> None:
    setup()
    m_all, v_all = data(1000)
    fig, axes = plt.subplots(1, 2, figsize=(11.5, 4.3))

    # (i) versus dimension.
    ax = axes[0]
    dims = np.unique(np.round(np.logspace(0, 3, 25)).astype(int))
    print("== KL vs dimension (T = 5, delta = 0.01) ==")
    for n_steps, color in [(100, BLUE), (1000, ORANGE)]:
        rows = [truth_and_bound(m_all[:d], v_all[:d], 5.0, n_steps) for d in dims]
        kl = np.array([r[0] for r in rows])
        bd = np.array([r[1] + r[2] for r in rows])
        assert np.all(kl <= bd), "numerical KL exceeds the Lean bound"
        ax.loglog(dims, bd, "--", color=color, label=f"Lean bound, N = {n_steps}")
        ax.loglog(dims, kl, "-", color=color, label=f"exact KL, N = {n_steps}")
        slope_kl = np.polyfit(np.log(dims), np.log(kl), 1)[0]
        slope_bd = np.polyfit(np.log(dims), np.log(bd), 1)[0]
        print(
            f"N={n_steps:5d}: d=1000 exact KL={kl[-1]:.4g}  bound={bd[-1]:.4g}  "
            f"ratio={bd[-1] / kl[-1]:.0f}  log-log slopes {slope_kl:.3f} / {slope_bd:.3f}"
        )
    ax.set_xlabel("dimension d")
    ax.set_ylabel("KL(p₁ ‖ q₁)  (nats)")
    ax.set_title("Both grow linearly in the dimension")
    ax.legend(loc="upper left")

    # (ii) versus number of steps.
    ax = axes[1]
    d = 10
    m, v = m_all[:d], v_all[:d]
    ns = np.unique(np.round(np.logspace(np.log10(2), 4, 30)).astype(int))
    rows = np.array([truth_and_bound(m, v, 5.0, n) for n in ns])
    kl, init, disc = rows[:, 0], rows[:, 1], rows[:, 2]
    assert np.all(kl <= init + disc)
    ax.loglog(ns, init + disc, "--", color=BLUE, label="Lean bound (total)")
    ax.loglog(ns, disc, ":", color=INK2, lw=1.5, label="  discretisation term")
    ax.axhline(init[0], color=MUTED, lw=1.2, ls="-.", label="  initialisation term")
    ax.loglog(ns, kl, "-", color=ORANGE, label="exact KL of the sampler")
    ax.set_xlabel("number of steps N")
    ax.set_title(f"d = {d}: the bound is safe, the truth decays faster")
    ax.set_ylim(1e-7, 1e4)
    ax.legend(loc="lower left")
    print(f"== KL vs N (d = {d}, T = 5, delta = {DELTA}) ==")
    for n in [10, 100, 1000, 10000]:
        i = int(np.argmin(np.abs(ns - n)))
        print(
            f"N={ns[i]:6d}: exact KL={kl[i]:.3g}  bound={init[i] + disc[i]:.3g} "
            f"(init {init[i]:.2g}, disc {disc[i]:.3g})  ratio={(init[i] + disc[i]) / kl[i]:.0f}"
        )
    big = ns >= 300
    print(
        "fitted decay exponents for N >= 300: exact KL "
        f"{np.polyfit(np.log(ns[big]), np.log(kl[big]), 1)[0]:.2f}, discretisation term "
        f"{np.polyfit(np.log(ns[big]), np.log(disc[big]), 1)[0]:.2f}"
    )
    fig.suptitle(
        "DDPM with the exact score on Gaussian data: formal bound vs exact KL",
        fontsize=13,
        fontweight="bold",
        y=1.02,
    )
    fig.tight_layout()
    save(fig, "ddpm_bound.png")


if __name__ == "__main__":
    main()
