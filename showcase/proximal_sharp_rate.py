"""PX-3 / PX-4: the sharp (1 + alpha eta)^{-2k} rate of the proximal sampler (illustration only).

One step of the exact proximal sampler of Lee, Shen and Tian (2021) (`Proximal.proxKernel f eta`):
y ~ N(x, eta), then x' ~ RGO(y) with density proportional to e^{-f(x') - (x' - y)^2 / (2 eta)}.
Two targets in 1D:

* Gaussian, f = gaussPotential alpha = alpha x^2 / 2 (PX-3,
  `ProximalGaussianUnconditional.toReal_klDiv_iterate_le_sq_of_ne_top`):
      KL(rho_k || pi) <= KL(rho_0 || pi) / (1 + alpha eta)^{2k}.
  Closed form: with c = 1/(1 + alpha eta) the chain is x' = c (x + sqrt(eta) xi) + sqrt(eta c) xi',
  so the mean contracts by c and the variance gap s - 1/alpha by c^2. A mean-shifted start
  N(m, 1/alpha) has KL_k = alpha c^{2k} m^2 / 2: the bound holds with EQUALITY at every k.
* Bounded perturbation, f = alpha x^2 / 2 + W with W(x) = B cos(3x), so a = -B <= W <= b = B
  (PX-4, `ProximalSharpPerturbedCold.toReal_klDiv_iterate_le_sq_perturbed_of_ne_top`):
      KL(rho_k || pi) <= KL(rho_0 || pi) / (1 + alpha e^{-(b - a)} eta)^{2k}.
  With alpha = 1 and B = 0.5 the potential is not convex (f'' = 1 - 4.5 cos 3x), so pi is not
  log-concave; the Holley-Stroock constant is alpha' = alpha e^{-1}.

Numerics: laws propagated exactly on a fine grid (Gaussian forward step as a matrix, RGO as the
normalised grid posterior); for the Gaussian target the grid is checked against the closed form.
"""

import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np  # noqa: E402
from _style import AQUA, BLUE, INK2, MUTED, ORANGE, VIOLET, plt, save, setup  # noqa: E402

ALPHA, ETA, B = 1.0, 0.5, 0.5
L, DX = 14.0, 0.01
K_MAX = 25
FLOOR = 1e-12  # grid KL values below this are rounding noise


def gauss_pdf(x, m, s):
    return np.exp(-((x - m) ** 2) / (2 * s)) / np.sqrt(2 * np.pi * s)


def kl_gauss(m, s):
    """KL(N(m, s) || N(0, 1/alpha))."""
    return 0.5 * (ALPHA * s - 1 - np.log(ALPHA * s) + ALPHA * m**2)


def run_chain(xs, pi, rho0, k_max):
    gauss = gauss_pdf(xs[:, None], xs[None, :], ETA)
    rgo = pi[None, :] * gauss
    rgo /= rgo.sum(axis=1, keepdims=True) * DX
    inv = ((pi * DX) @ gauss * DX) @ rgo
    assert np.max(np.abs(inv - pi)) < 1e-10, "grid kernel must leave pi invariant"
    rho, dens, kl = rho0 / (rho0.sum() * DX), [], []
    for _ in range(k_max + 1):
        dens.append(rho)
        m = rho > 1e-300
        kl.append(np.sum(rho[m] * np.log(rho[m] / pi[m])) * DX)
        rho = (((rho * DX) @ gauss) * DX) @ rgo
        rho /= rho.sum() * DX
    return np.array(dens), np.array(kl)


def main() -> None:
    setup()
    xs = np.arange(-L, L + DX / 2, DX)
    ks = np.arange(K_MAX + 1)
    c = 1 / (1 + ALPHA * ETA)
    alpha_hs = ALPHA * np.exp(-(B - (-B)))
    c_hs = 1 / (1 + alpha_hs * ETA)
    pi_g = gauss_pdf(xs, 0.0, 1 / ALPHA)
    pi_g /= pi_g.sum() * DX
    pi_p = np.exp(-ALPHA * xs**2 / 2 - B * np.cos(3 * xs))
    pi_p /= pi_p.sum() * DX
    print(f"alpha = {ALPHA}, eta = {ETA}: (1 + alpha eta)^-2 = {c**2:.4f}")
    print(
        f"W = {B} cos 3x, b - a = {2 * B}: alpha' = alpha e^-(b-a) = {alpha_hs:.4f},"
        f" (1 + alpha' eta)^-2 = {c_hs**2:.4f}"
    )

    starts = {
        "mean shift N(3, 1)": (3.0, 1.0),
        "narrow N(0, 0.05)": (0.0, 0.05),
        "narrow off-centre N(-2, 0.1)": (-2.0, 0.1),
    }
    runs = {}
    for name, (m0, s0) in starts.items():
        _, kl = run_chain(xs, pi_g, gauss_pdf(xs, m0, s0), K_MAX)
        exact = kl_gauss(c**ks * m0, 1 / ALPHA + c ** (2 * ks) * (s0 - 1 / ALPHA))
        err = np.max(np.abs(kl - exact) / np.maximum(exact, 1e-9))
        assert err < 1e-6, f"grid vs closed form ({name}): {err:.1e}"
        bound = exact[0] * c ** (2 * ks)
        assert np.all(exact <= bound * (1 + 1e-12)), f"PX-3 bound violated ({name})"
        runs[("gauss", name)] = (exact, bound)
        print(f"Gaussian target, {name}: KL0 = {exact[0]:.4f}, grid vs closed form {err:.1e}")
        print(
            "   KL_k / bound at k = 1, 5, 10: "
            + ", ".join(f"{exact[k] / bound[k]:.4g}" for k in (1, 5, 10))
        )
    exact, bound = runs[("gauss", "mean shift N(3, 1)")]
    assert np.allclose(exact, bound, rtol=1e-12), "mean-shift start must attain the PX-3 bound"

    for name, (m0, s0) in starts.items():
        dens, kl = run_chain(xs, pi_p, gauss_pdf(xs, m0, s0), K_MAX)
        bound = kl[0] * c_hs ** (2 * ks)
        assert np.all(kl <= bound + FLOOR), f"PX-4 bound violated ({name})"
        runs[("pert", name)] = (kl, bound)
        if name.startswith("mean"):
            dens_show = dens
        ok = kl > 1e-9
        rate = (kl[ok][-1] / kl[ok][-2]) if ok.sum() > 1 else np.nan
        print(
            f"perturbed target, {name}: KL0 = {kl[0]:.4f}; KL_k / bound at k = 1, 5, 10: "
            + ", ".join(f"{kl[k] / bound[k]:.3g}" for k in (1, 5, 10))
            + f"; late per-step factor {rate:.4f}"
        )

    fig, axes = plt.subplots(1, 3, figsize=(16, 4.6))
    ax = axes[0]
    ax.plot(xs, pi_g, color=MUTED, lw=1.6, ls="--", label="Gaussian target N(0, 1)")
    ax.plot(xs, pi_p, color=INK2, lw=2.4, label=r"perturbed $\pi \propto e^{-x^2/2 - 0.5\cos 3x}$")
    for k, alpha in zip((0, 1, 3), (0.3, 0.6, 1.0)):
        ax.plot(
            xs, dens_show[k], color=BLUE, alpha=alpha, lw=1.8, label=f"ρ_{k} (perturbed target)"
        )
    ax.set_xlim(-4.5, 6.5)
    ax.set_ylim(0, 0.85)
    ax.set_xlabel("x")
    ax.set_ylabel("density")
    ax.set_title("targets; chain from N(3, 1)")
    ax.legend(loc="upper right", fontsize=8.5)

    ax = axes[1]
    colors = {
        "mean shift N(3, 1)": BLUE,
        "narrow N(0, 0.05)": ORANGE,
        "narrow off-centre N(-2, 0.1)": AQUA,
    }
    ax.semilogy(
        ks, c ** (2 * ks), color=INK2, lw=2.6, ls="--", label=r"PX-3 bound $(1+\alpha\eta)^{-2k}$"
    )
    ax.semilogy(
        ks,
        c_hs ** (2 * ks),
        color=VIOLET,
        lw=2.6,
        ls="--",
        label=r"PX-4 bound $(1+\alpha e^{-(b-a)}\eta)^{-2k}$",
    )
    for name, col in colors.items():
        kl, _ = runs[("gauss", name)]
        ax.semilogy(ks, np.where(kl > FLOOR, kl / kl[0], np.nan), "o", color=col, ms=4)
        kl, _ = runs[("pert", name)]
        ax.semilogy(
            ks,
            np.where(kl > FLOOR, kl / kl[0], np.nan),
            "-",
            color=col,
            lw=1.8,
            label=f"ρ₀ = {name}",
        )
    ax.plot([], [], "o", color=MUTED, ms=4, label="dots: Gaussian target")
    ax.plot([], [], "-", color=MUTED, label="lines: perturbed target")
    ax.set_ylim(1e-12, 2)
    ax.set_xlabel("iteration k")
    ax.set_ylabel("KL(ρ_k ‖ π) / KL(ρ₀ ‖ π)")
    ax.set_title("relative KL vs the sharp-rate bounds")
    ax.legend(loc="lower left", fontsize=8)

    ax = axes[2]
    for name, col in colors.items():
        for key, style in (("gauss", "o"), ("pert", "-")):
            kl, _ = runs[(key, name)]
            ok = kl[:-1] > 1e-9
            ax.plot(ks[1:][ok], (kl[1:] / kl[:-1])[ok], style, color=col, ms=4, lw=1.8)
    ax.axhline(c**2, color=INK2, lw=2, ls="--")
    ax.axhline(c_hs**2, color=VIOLET, lw=2, ls="--")
    ax.axhline(c, color=MUTED, lw=1.2, ls=":")
    ax.text(K_MAX, c**2 - 0.04, r"$(1+\alpha\eta)^{-2}$ (PX-3)", color=INK2, ha="right")
    ax.text(
        K_MAX,
        c_hs**2 + 0.015,
        r"$(1+\alpha'\eta)^{-2}$, $\alpha' = \alpha e^{-(b-a)}$ (PX-4)",
        color=VIOLET,
        ha="right",
    )
    ax.text(
        K_MAX,
        c - 0.045,
        r"$(1+\alpha\eta)^{-1}$: forward step alone (PX-2)",
        color=INK2,
        ha="right",
    )
    ax.set_ylim(0, 0.8)
    ax.set_xlabel("iteration k")
    ax.set_ylabel(r"$KL_k \,/\, KL_{k-1}$")
    ax.set_title("per-step contraction factor")
    fig.suptitle(
        f"PX-3 / PX-4: sharp proximal-sampler rate (α = {ALPHA:g}, η = {ETA:g}); "
        "the Gaussian mean shift attains it exactly",
        fontsize=13,
    )
    fig.tight_layout()
    save(fig, "proximal_sharp_rate.png")


if __name__ == "__main__":
    main()
