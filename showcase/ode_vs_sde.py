"""DF-3: same score, stochastic sampler right, deterministic sampler wrong (illustration only).

Data N(0, 1) and the OU forward process, so p_t = N(0, 1) for every t and the exact score is
-x. Perturb it by a tiny, smooth, periodic error
    s(x) = -x + e(x),   e(x) = -(lam / omega) sin(omega x),   omega = 2 pi / h,
with sup |e| = lam h / (2 pi). Run, from N(0, 1) over reverse time T:
  (i)  the probability-flow ODE dY/dtau = Y + s(Y) = e(Y) (deterministic, DDIM-like). Its flow is
       explicit: tan(pi Phi_T(x) / h) = e^{-lam T} tan(pi x / h). Each cell of width h is squeezed
       onto the lattice point inside it, so the output is a comb.
  (ii) DDPM (stochastic) with the same score, Lean conventions (variance beta / alpha^2).
The displayed Girsanov + Pinsker bound controls the corresponding continuous-time SDE,
started from its exact terminal law N(0, 1). It does not certify the finite-step DDPM
simulation: a discrete bound must also account for discretisation, as in
`DiffusionDiscretization.tvSup_output_le_ddpm_grid`. The ODE output has
TV ~ 1 - (4/pi) arctan(e^{-lam T / 2}) in the limit of small h.
The discontinuous (floor-function) version, due to Li, Wei, Chen, Chi (arXiv:2306.09251),
is formalised as `DiffusionODESeparation.ddpm_ddim_separation` (DF-3); the smooth sine version
here is numerical only. A different construction, whose score error is an analytic function of
the exact update, is formalised as `DiffusionODESmooth.ddpm_ddim_smooth_separation` (DF-7; see
`ode_smooth.py`).
"""

from math import erf, sqrt

import numpy as np
from _style import BLUE, INK, INK2, MUTED, ORANGE, RED, plt, save, setup

H = 0.1
LAM = 3.0
T = 2.0
SEED = 0


def err(x, lam):
    omega = 2 * np.pi / H
    return -(lam / omega) * np.sin(omega * x)


def ode_flow(x, lam, horizon=T):
    """Closed-form time-`horizon` flow of dY/dtau = e(Y)."""
    r = np.exp(-lam * horizon)
    w = 2 * np.pi * x / H
    return x - (H / np.pi) * np.arctan((1 - r) * np.sin(w) / ((1 + r) + (1 - r) * np.cos(w)))


def ode_rk4(x, lam, horizon=T, n=4000):
    dt = horizon / n
    for _ in range(n):
        k1 = err(x, lam)
        k2 = err(x + 0.5 * dt * k1, lam)
        k3 = err(x + 0.5 * dt * k2, lam)
        k4 = err(x + dt * k3, lam)
        x = x + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return x


def ddpm(x, lam, rng, n_steps, horizon=T):
    """Uniform grid t_k = k T / N; x <- (x + beta s(x)) / alpha + (sqrt(beta) / alpha) xi."""
    dt = horizon / n_steps
    alpha = np.exp(-dt)
    beta = -np.expm1(-2 * dt)
    for _ in range(n_steps):
        s = -x + err(x, lam)
        x = (x + beta * s) / alpha + np.sqrt(beta) / alpha * rng.standard_normal(x.shape)
    return x


def gauss_cdf(x):
    return 0.5 * (1 + np.vectorize(erf)(x / sqrt(2)))


EDGES = np.arange(-5.0, 5.0 + 1e-9, H / 10)
P_BIN = np.diff(gauss_cdf(EDGES))


def hist_tv(x):
    counts, _ = np.histogram(x, bins=EDGES)
    tail = 1 - counts.sum() / len(x)
    return 0.5 * (np.abs(counts / len(x) - P_BIN).sum() + tail + (1 - P_BIN.sum()))


def tv_periodic(lam_t):
    """h -> 0 limit of TV(Phi_T # N(0,1), N(0,1)): 1 - (4/pi) arctan(e^{-lam T / 2})."""
    return 1 - (4 / np.pi) * np.arctan(np.exp(-lam_t / 2))


def tv_quadrature(lam, n=4_000_001):
    """TV by quadrature of the push-forward density on a fine grid (moderate lam T only)."""
    y = np.linspace(-7, 7, n)
    r = np.exp(-lam * T)
    x = ode_flow(y, -lam)  # inverse flow
    c2 = np.cos(np.pi * y / H) ** 2
    jac = r / (r**2 * c2 + (1 - c2))  # dx/dy for the inverse flow
    phi = np.exp(-0.5 * y**2) / np.sqrt(2 * np.pi)
    q = np.exp(-0.5 * x**2) / np.sqrt(2 * np.pi) * jac
    return 0.5 * np.sum(np.abs(q - phi)) * (y[1] - y[0])


def main() -> None:
    setup()
    rng = np.random.default_rng(SEED)
    n = 200_000
    x0 = rng.standard_normal(n)
    sup_err = LAM * H / (2 * np.pi)
    l2_err = sup_err * np.sqrt((1 - np.exp(-2 * (2 * np.pi / H) ** 2)) / 2)
    print(f"h={H}, lambda={LAM}, T={T}: sup|e| = {sup_err:.4f}, L2(N(0,1)) error = {l2_err:.4f}")

    y_ode = ode_flow(x0, LAM)
    y_rk4 = ode_rk4(x0[:20000].copy(), LAM)
    print(f"closed-form flow vs RK4: max |diff| = {np.max(np.abs(y_rk4 - y_ode[:20000])):.2e}")
    y_sde = ddpm(x0.copy(), LAM, np.random.default_rng(SEED + 1), n_steps=1000)
    ref = np.random.default_rng(SEED + 2).standard_normal(n)

    tv_ode, tv_sde, tv_ref = hist_tv(y_ode), hist_tv(y_sde), hist_tv(ref)
    print(
        f"histogram TV (bin h/10, n={n}): ODE {tv_ode:.3f}  DDPM {tv_sde:.3f}  "
        f"exact N(0,1) samples (noise floor) {tv_ref:.3f}"
    )
    print(
        f"ODE exact TV by quadrature {tv_quadrature(LAM):.4f}, "
        f"periodic limit {tv_periodic(LAM * T):.4f}, "
        f"unformalised lower bound {1 - 4 / np.pi * np.exp(-LAM * T / 2) - np.sqrt(2 / np.pi) * H:.4f}"
    )
    print(f"Continuous-time SDE Girsanov+Pinsker bound: TV <= {np.sqrt(T * l2_err**2 / 2):.4f}")

    fig, axs = plt.subplots(1, 4, figsize=(18, 4.6), gridspec_kw={"wspace": 0.3})
    xs = np.linspace(-3, 3, 4000)
    gauss = np.exp(-0.5 * xs**2) / np.sqrt(2 * np.pi)

    ax = axs[0]
    ax.plot(xs, -xs, color=INK2, lw=3.5, alpha=0.45, label="exact score  −x")
    ax.plot(xs, -xs + err(xs, LAM), color=RED, lw=1.2, label="perturbed score  −x + e(x)")
    ax.set_title("(a) the score is almost exact")
    ax.set_xlabel("x")
    ax.legend(loc="upper right")
    ax.text(
        0.04,
        0.06,
        f"max |error| = {sup_err:.3f}\nsmooth, Lipschitz {LAM:g}",
        transform=ax.transAxes,
        color=INK2,
        fontsize=9.5,
    )
    inset = ax.inset_axes([0.08, 0.26, 0.38, 0.22])
    inset.plot(xs, err(xs, LAM), color=RED, lw=1)
    inset.set_xlim(-0.5, 0.5)
    inset.set_xticks([])
    inset.set_yticks([])
    inset.set_title("error e(x), zoomed", fontsize=8, color=INK2)

    bins = np.arange(-3, 3 + 1e-9, H / 10)
    for ax, y, color, title in [
        (axs[1], y_sde, BLUE, "(b) DDPM (stochastic) output"),
        (axs[2], y_ode, ORANGE, "(c) probability-flow ODE output"),
    ]:
        ax.hist(y, bins=bins, density=True, color=color, alpha=0.85, lw=0)
        ax.plot(xs, gauss, color=INK, lw=1.4, label="target N(0, 1)")
        ax.set_xlim(-3, 3)
        ax.set_ylim(0, 0.62 if color == BLUE else 2.4)
        ax.set_xlabel("output sample")
        ax.set_title(title)
        ax.legend(loc="upper right" if color == BLUE else "center right")
    axs[1].set_ylabel("density")
    axs[1].text(
        0.03,
        0.95,
        f"continuous-time SDE:\nTV bound ≤ {np.sqrt(T * l2_err**2 / 2):.3f}\n"
        f"DDPM histogram: {tv_sde:.3f}\n"
        f"(noise floor {tv_ref:.3f})",
        transform=axs[1].transAxes,
        va="top",
        color=INK2,
        fontsize=9,
    )
    axs[2].text(
        0.03,
        0.95,
        f"same score, λT = {LAM * T:g}: TV = {tv_quadrature(LAM):.2f}\n"
        "mass piles up on the lattice hℤ",
        transform=axs[2].transAxes,
        va="top",
        color=INK2,
        fontsize=9,
    )

    ax = axs[3]
    lams = np.linspace(0, 5, 11)
    lam_t = np.linspace(0, 10, 200)
    ax.plot(lam_t, tv_periodic(lam_t), color=ORANGE, label="ODE: TV (h → 0 formula)")
    lb = 1 - 4 / np.pi * np.exp(-lam_t / 2) - np.sqrt(2 / np.pi) * H
    ax.plot(
        lam_t,
        np.maximum(lb, 0),
        ":",
        color=ORANGE,
        lw=1.6,
        label="ODE: lower bound",
    )
    q_pts = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]
    ax.plot(
        [2 * q for q in q_pts],
        [tv_quadrature(q) for q in q_pts],
        "o",
        color=ORANGE,
        ms=6,
        mec="white",
        label="ODE: TV, quadrature",
    )
    l2 = lam_t / T * H / (2 * np.pi) * np.sqrt(0.5)
    ax.plot(lam_t, np.sqrt(T * l2**2 / 2), color=BLUE, label="continuous-time SDE: TV bound")
    rng_s = np.random.default_rng(SEED + 3)
    tv_s = []
    for lam in lams:
        z = ddpm(rng_s.standard_normal(n), lam, rng_s, n_steps=200)
        tv_s.append(hist_tv(z))
    ax.plot(lams * T, tv_s, "s", color=BLUE, ms=5, mec="white", label="DDPM: histogram TV")
    ax.axhline(tv_ref, color=MUTED, lw=1, ls="--")
    ax.text(0.2, tv_ref + 0.02, "histogram noise floor", color=INK2, fontsize=8.5)
    ax.set_xlabel("λT  (integrated Lipschitz constant of the error)")
    ax.set_ylabel("total variation to N(0, 1)")
    ax.set_ylim(0, 1.02)
    ax.set_title("(d) error vs λT  (h = 0.1, T = 2)")
    ax.legend(loc="lower right", bbox_to_anchor=(1.0, 0.1), fontsize=8.5)
    print("lambda*T | ODE TV (h->0) | DDPM hist TV (N=200) | continuous-time SDE bound")
    for lam, tv in zip(lams, tv_s):
        bound = np.sqrt(T * (lam * H / (2 * np.pi)) ** 2 / 4)
        print(
            f"{lam * T:8.1f} | {tv_periodic(lam * T):.3f}         | {tv:.3f}"
            f"                | {bound:.4f}"
        )

    fig.suptitle(
        "Same nearly-exact score: the stochastic sampler is right, the deterministic one is not",
        fontsize=13,
        fontweight="bold",
        y=1.0,
    )
    save(fig, "ode_vs_sde.png")


if __name__ == "__main__":
    main()
