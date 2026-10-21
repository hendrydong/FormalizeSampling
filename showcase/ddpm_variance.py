"""DF-4: which reverse variance? (illustration, not a proof)

Same exact-score DDPM on Gaussian data as `ddpm_bound.py`, with three choices of the reverse
noise variance sigma_k^2:
    beta_k / alpha_k^2               (the variance of the DF-1 bound, `ddpmVar`)
    beta_k                           (one of Ho et al.'s two choices, the "upper" one)
    beta_k (1 - abar_{k-1}) / (1 - abar_k)   (the Gaussian posterior variance, Ho et al.'s
                                     other choice; abar_k = e^{-2 t_k})
The output KL(p_1 || q_1) is exact (all laws Gaussian). Bottom row: the path-space KL
KL(p_N || N(0, I)) + sum_k D_k (chain rule; D_k = E KL(exact reverse kernel || sampler kernel)),
the quantity that chain-rule/Girsanov proofs such as `klDiv_output_le_ddpm_grid` control, also
exact for Gaussian data.
"""

import numpy as np
from _gauss_ddpm import exact_kl, kappa_grid, path_terms
from _style import AQUA, BLUE, INK2, ORANGE, geom_grid, plt, save, setup

DELTA = 0.01
RULES = [
    ("ddpm", "σ² = β/α²  (Lean ddpmVar)", BLUE),
    ("beta", "σ² = β", ORANGE),
    ("posterior", "σ² = β̃ (posterior)", AQUA),
]


def main() -> None:
    setup()
    rng = np.random.default_rng(0)
    d = 10
    m = rng.normal(size=d)
    v = np.exp(rng.uniform(np.log(0.05), np.log(2.0), size=d))

    fig, axes2 = plt.subplots(2, 3, figsize=(15.5, 9.2))
    axes = axes2[0]

    ns = np.unique(np.round(np.logspace(np.log10(5), 4, 25)).astype(int))
    ax = axes[0]
    print(f"== exact KL vs N (d = {d}, T = 5) ==")
    res = {}
    for rule, label, color in RULES:
        res[rule] = np.array([exact_kl(m, v, geom_grid(DELTA, 5.0, n), rule) for n in ns])
        ax.loglog(ns, res[rule], color=color, label=label)
    for n in [10, 100, 1000, 10000]:
        i = int(np.argmin(np.abs(ns - n)))
        print(f"N={ns[i]:6d}: " + "  ".join(f"{r}={res[r][i]:.3g}" for r, _, _ in RULES))
    ax.set_xlabel("number of steps N")
    ax.set_ylabel("exact KL(p₁ ‖ q₁)  (nats)")
    ax.set_title("(a) output KL vs number of steps (T = 5)")
    ax.legend(loc="lower left")

    ax = axes[1]
    horizons = np.linspace(0.5, 12, 47)
    print(f"== exact KL vs horizon T (d = {d}, N = 100) ==")
    res_t = {}
    for rule, label, color in RULES:
        res_t[rule] = np.array([exact_kl(m, v, geom_grid(DELTA, h, 100), rule) for h in horizons])
        ax.semilogy(horizons, res_t[rule], color=color, label=label)
    for h in [1, 2, 3, 5, 8, 12]:
        i = int(np.argmin(np.abs(horizons - h)))
        print(f"T={horizons[i]:5.2f}: " + "  ".join(f"{r}={res_t[r][i]:.3g}" for r, _, _ in RULES))
    best = {r: horizons[np.argmin(res_t[r])] for r, _, _ in RULES}
    print("best horizon per rule:", {r: round(float(b), 2) for r, b in best.items()})
    ax.set_xlabel("horizon T")
    ax.set_title("(b) output KL vs horizon, N = 100 fixed")

    ax = axes[2]
    variances = np.logspace(-3, 1, 60)
    print("== exact KL vs data variance (d = 1, mean 0, N = 100, T = 5) ==")
    res_v = {}
    for rule, label, color in RULES:
        res_v[rule] = np.array(
            [exact_kl([0.0], [vv], geom_grid(DELTA, 5.0, 100), rule) for vv in variances]
        )
        ax.loglog(variances, np.maximum(res_v[rule], 1e-12), color=color, label=label)
    ax.axvline(1.0, color="#8a8984", lw=1, ls=":")
    ax.annotate(
        "data = N(0,1): σ² = β\nreverses OU exactly (KL = 0)",
        xy=(0.97, 3e-7),
        xytext=(0.012, 1e-8),
        color="#52514e",
        fontsize=9,
        arrowprops={"arrowstyle": "->", "color": "#8a8984"},
    )
    for vv in [1e-3, 1e-2, 0.1, 1.0, 10.0]:
        i = int(np.argmin(np.abs(np.log(variances / vv))))
        print(f"v={variances[i]:.3g}: " + "  ".join(f"{r}={res_v[r][i]:.3g}" for r, _, _ in RULES))
    ax.set_ylim(1e-10, 1e-1)
    ax.set_xlabel("data variance v  (d = 1)")
    ax.set_title("(c) output KL: the winner depends on the data")

    # --- bottom row: path-level vs output-level, versus the horizon ---
    kappa = 0.1
    horizons_b = np.linspace(1, 16, 31)
    for col, tail, title in [
        (0, False, f"(d) geometric grid (κ = {kappa}) up to T"),
        (1, True, "(e) same grid to t ≈ 1.2, then ONE step to T"),
    ]:
        ax = axes2[1, col]
        print(f"== path vs output KL vs T ({title}; d = {d}) ==")
        for rule, label, color in RULES:
            path, out = [], []
            for h in horizons_b:
                t = kappa_grid(DELTA, h, kappa, tail=tail)
                dk, init = path_terms(m, v, t, rule)
                path.append(init + dk.sum())
                out.append(exact_kl(m, v, t, rule))
            ax.semilogy(horizons_b, path, "--", color=color, lw=1.6)
            ax.semilogy(horizons_b, out, "-", color=color)
            print(
                f"  {rule:9s}: path KL T=2 {path[2]:.3g}, T=8 {path[14]:.3g}, T=16 {path[-1]:.3g};"
                f" output KL T=2 {out[2]:.3g}, T=8 {out[14]:.3g}, T=16 {out[-1]:.3g}"
            )
        ax.plot([], [], "--", color=INK2, lw=1.6, label="dashed: path-space KL")
        ax.plot([], [], "-", color=INK2, label="solid: output KL")
        ax.set_xlabel("horizon T")
        ax.set_title(title)
        n_lo = len(kappa_grid(DELTA, 1, kappa, tail)) - 1
        n_hi = len(kappa_grid(DELTA, 16, kappa, tail)) - 1
        ax.text(
            0.03,
            0.96,
            f"N = {n_lo} … {n_hi} steps",
            transform=ax.transAxes,
            va="top",
            color=INK2,
            fontsize=9,
        )
    axes2[1, 0].set_ylabel("KL  (nats)")
    axes2[1, 0].legend(loc="center right", bbox_to_anchor=(1.0, 0.38), fontsize=9)

    ax = axes2[1, 2]
    lam = 0.5
    t = kappa_grid(DELTA, 6.0, kappa)
    tk = t[2:][::-1]  # path_terms runs k = N, ..., 2
    print(f"== per-step D_k, data N(0, {lam} I), d = {d} (E|X|^2 = {lam * d:g} <= d) ==")
    per = {}
    for rule, label, color in RULES:
        dk, _ = path_terms(np.zeros(d), np.full(d, lam), t, rule)
        per[rule] = dk
        ax.loglog(tk, dk, color=color, label=label)
        print(f"  {rule:9s}: sum D_k = {dk.sum():.4g}")
    print(
        "  beta <= beta/alpha^2 at every step:",
        bool(np.all(per["beta"] <= per["ddpm"])),
        "| beta <= posterior at every step:",
        bool(np.all(per["beta"] <= per["posterior"])),
    )
    ax.set_xlabel("time t_k of the reverse step")
    ax.set_ylabel("per-step KL  D_k")
    ax.set_title(f"(f) per-step KL, data N(0, {lam}·I)")
    ax.legend(loc="lower left")
    fig.suptitle(
        "Reverse-noise variance of the exact-score DDPM sampler (Gaussian data, exact KL)",
        fontsize=13,
        fontweight="bold",
        y=1.0,
    )
    fig.tight_layout()
    save(fig, "ddpm_variance.png")


if __name__ == "__main__":
    main()
