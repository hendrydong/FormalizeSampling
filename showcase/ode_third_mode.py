"""DF-3, numerically: a tiny score error between two modes, and the deterministic sampler
outputs a third mode (illustration only; this construction is not formalised).

Data (1/2) N(-2, 1/4) + (1/2) N(2, 1/4) and the OU forward process, so
    p_t = (1/2) N(-m_t, v_t) + (1/2) N(m_t, v_t),   m_t = 2 e^{-t},   v_t = 1 - (3/4) e^{-2t},
and the exact score is s_t(x) = (-x + m_t tanh(m_t x / v_t)) / v_t. At every noise level add
    e(x) = -(lam h / (2 pi)) sin(2 pi x / h) for |x| <= h / 2,   e(x) = 0 otherwise,
with h = 0.6 and lam = 0.7, so sup |e| = lam h / (2 pi) < 0.07. Both samplers start from
N(0, 1) at T = 10 and stop at delta = 0.01; the target is p_delta.
  (i)  Probability-flow ODE dY/dtau = Y + s(Y) (RK4). While p_t is close to N(0, 1) the exact
       velocity is tiny, and e pulls the samples that start in |x| < h/2 onto the midpoint 0.
       Near the end the exact flow pushes away from 0, but these samples are too close to it to
       reach either mode by time delta.
  (ii) DDPM with the same score and Lean conventions (variance beta / alpha^2). The injected
       noise moves samples off the midpoint, and the error is forgotten.
The ODE output is the push-forward of N(0, 1) by a monotone map, so its mass in the gap and its
TV to p_delta are computed by quadrature through that map. The DDPM numbers are Monte Carlo.
The displayed sqrt(int E_{p_t} e^2 dt / 2) is the continuous-time Girsanov + Pinsker
score-error term. Since the sampler starts from N(0, 1), not exactly p_T, an output-TV
guarantee also needs an initialisation term; finite-step DDPM needs discretisation control.
The formal results, with a uniformly small score error and deterministic-sampler TV close to 1,
are DF-3 (`DiffusionODESeparation.ddpm_ddim_separation`, after Li, Wei, Chen, Chi) and DF-7
(`DiffusionODESmooth.ddpm_ddim_smooth_separation`); both perturb the last step only.
"""

from math import erf, sqrt

import numpy as np
from _style import BLUE, INK, INK2, MUTED, ORANGE, RED, plt, save, setup

A = 2.0  # modes at +-A
V0 = 0.25  # variance of each mode
H = 0.6  # width of the region where the score is perturbed
LAM = 0.7  # Lipschitz constant of the error
T = 10.0
DELTA = 0.01
N_STEPS = 2000
SEED = 0
GAP = 1.0  # the gap between the modes is |x| < GAP

ncdf = np.vectorize(lambda z: 0.5 * (1 + erf(z / sqrt(2))))


def mean_var(t):
    return A * np.exp(-t), V0 * np.exp(-2 * t) + 1 - np.exp(-2 * t)


def score(x, t):
    m, v = mean_var(t)
    return (-x + m * np.tanh(m * x / v)) / v


def err(x):
    return np.where(np.abs(x) <= H / 2, -(LAM * H / (2 * np.pi)) * np.sin(2 * np.pi * x / H), 0.0)


def ode(x, perturbed=True, n_steps=N_STEPS, keep_path=False):
    """RK4 for dY/dtau = Y + s_t(Y) (+ e(Y)), from t = T down to t = DELTA."""
    ts = np.linspace(T, DELTA, n_steps + 1)

    def f(y, t):
        return y + score(y, t) + (err(y) if perturbed else 0.0)

    path = [x.copy()]
    for t0, t1 in zip(ts[:-1], ts[1:]):
        dt = t0 - t1
        k1 = f(x, t0)
        k2 = f(x + dt / 2 * k1, t0 - dt / 2)
        k3 = f(x + dt / 2 * k2, t0 - dt / 2)
        k4 = f(x + dt * k3, t1)
        x = x + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        if keep_path:
            path.append(x.copy())
    return (ts, np.array(path)) if keep_path else x


def ddpm(x, rng, n_steps=1000):
    """Uniform grid; x <- (x + beta s(x)) / alpha + (sqrt(beta) / alpha) xi."""
    ts = np.linspace(T, DELTA, n_steps + 1)
    for t0, t1 in zip(ts[:-1], ts[1:]):
        alpha = np.exp(-(t0 - t1))
        beta = -np.expm1(-2 * (t0 - t1))
        s = score(x, t0) + err(x)
        x = (x + beta * s) / alpha + np.sqrt(beta) / alpha * rng.standard_normal(x.shape)
    return x


def target_cdf(y):
    m, v = mean_var(DELTA)
    return 0.5 * (ncdf((y + m) / np.sqrt(v)) + ncdf((y - m) / np.sqrt(v)))


def target_pdf(y):
    m, v = mean_var(DELTA)
    g = np.exp(-((y + m) ** 2) / (2 * v)) + np.exp(-((y - m) ** 2) / (2 * v))
    return 0.5 * g / np.sqrt(2 * np.pi * v)


def push_forward(n_steps=N_STEPS, n_cells=10_000):
    """Cells of N(0, 1) on [-6, 6] and their images under the (monotone) ODE flow map."""
    x_edges = np.linspace(-6, 6, n_cells + 1)
    y_edges = ode(x_edges.copy(), n_steps=n_steps)
    assert np.all(np.diff(y_edges) > 0), "flow map not monotone: refine the time grid"
    mass = np.diff(ncdf(x_edges))
    return x_edges, y_edges, mass


def tv_and_gap(y_edges, mass):
    """TV(ODE output, p_delta) on the partition by the image cells (a lower bound that is
    accurate when the cells are fine), and the ODE output's mass in the gap."""
    f_mass = np.diff(target_cdf(y_edges))
    outside = 1 - f_mass.sum() + (1 - mass.sum())
    tv = 0.5 * (np.abs(mass - f_mass).sum() + outside)
    g = np.concatenate([[0.0], np.cumsum(mass)])
    gap = np.interp(GAP, y_edges, g) - np.interp(-GAP, y_edges, g)
    return tv, gap


def girsanov_tv():
    """Continuous-time score-error term; excludes initialisation and discretisation."""
    ts = np.linspace(DELTA, T, 2001)
    xs = np.linspace(-H / 2, H / 2, 2001)
    m_e2 = []
    for t in ts:
        m, v = mean_var(t)
        p = 0.5 * (np.exp(-((xs + m) ** 2) / (2 * v)) + np.exp(-((xs - m) ** 2) / (2 * v)))
        m_e2.append(np.trapezoid(err(xs) ** 2 * p / np.sqrt(2 * np.pi * v), xs))
    return sqrt(np.trapezoid(m_e2, ts) / 2)


def main() -> None:
    setup()
    sup_err = LAM * H / (2 * np.pi)
    target_gap = target_cdf(np.array(GAP)) - target_cdf(np.array(-GAP))
    print(f"h={H}, lambda={LAM}, T={T}, delta={DELTA}: sup|e| = {sup_err:.4f}")

    x_edges, y_edges, mass = push_forward()
    tv_ode, gap_ode = tv_and_gap(y_edges, mass)
    _, y_fine, mass_fine = push_forward(n_steps=2 * N_STEPS)
    tv_fine, gap_fine = tv_and_gap(y_fine, mass_fine)
    print(
        f"ODE output: TV to p_delta {tv_ode:.4f} ({2 * N_STEPS} steps: {tv_fine:.4f}), "
        f"mass in |x| < {GAP:g}: {gap_ode:.4f} ({gap_fine:.4f}); target {target_gap:.4f}"
    )

    rng = np.random.default_rng(SEED)
    n = 100_000
    y_sde = ddpm(rng.standard_normal(n), np.random.default_rng(SEED + 1))
    gap_sde = np.mean(np.abs(y_sde) < GAP)
    tv_bound = girsanov_tv()
    print(f"DDPM: mass in |x| < {GAP:g}: {gap_sde:.4f} (Monte Carlo, n = {n})")
    print(f"Continuous-time Girsanov+Pinsker score-error term: {tv_bound:.4f}")

    fig, axs = plt.subplots(1, 4, figsize=(19, 4.6), gridspec_kw={"wspace": 0.3})

    ax = axs[0]
    xs = np.linspace(-3, 3, 4000)
    ax.plot(xs, score(xs, 1.0), color=INK2, lw=3.5, alpha=0.45, label="exact score at t = 1")
    ax.plot(xs, score(xs, 1.0) + err(xs), color=RED, lw=1.2, label="perturbed score")
    ax.set_title("(a) the score is almost exact")
    ax.set_xlabel("x")
    ax.legend(loc="upper right")
    ax.text(
        0.04,
        0.06,
        f"max |error| = {sup_err:.3f}, at every noise level\nzero for |x| > {H / 2:g}",
        transform=ax.transAxes,
        color=INK2,
        fontsize=9.5,
    )
    inset = ax.inset_axes([0.08, 0.28, 0.38, 0.22])
    u = np.linspace(-0.6, 0.6, 1000)
    inset.plot(u, err(u), color=RED, lw=1)
    inset.axhline(0, color=MUTED, lw=0.6)
    inset.set_xticks([])
    inset.set_yticks([])
    inset.set_title("error e(x), zoomed", fontsize=8, color=INK2)

    bins = np.linspace(-4, 4, 161)
    ys = np.linspace(-4, 4, 2000)
    # ODE output histogram: its CDF through the flow map, linear within each image cell
    cum = np.concatenate([[0.0], np.cumsum(mass)])
    ode_bins = np.diff(np.interp(bins, y_edges, cum)) / np.diff(bins)
    for ax, color, title in [
        (axs[1], BLUE, "(b) DDPM (stochastic) output"),
        (axs[2], ORANGE, "(c) probability-flow ODE output"),
    ]:
        if color == BLUE:
            ax.hist(y_sde, bins=bins, density=True, color=color, alpha=0.85, lw=0)
        else:
            ax.stairs(ode_bins, bins, fill=True, color=color, alpha=0.85, lw=0)
        ax.plot(ys, target_pdf(ys), color=INK, lw=1.4, label="target")
        ax.axvspan(-GAP, GAP, color=MUTED, alpha=0.08, lw=0)
        ax.set_xlim(-4, 4)
        ax.set_ylim(0, 0.75)
        ax.set_xlabel("output sample")
        ax.set_title(title)
        ax.legend(loc="upper right")
    axs[1].set_ylabel("density")
    axs[1].text(
        0.03,
        0.95,
        f"mass in the gap |x| < {GAP:g}: {gap_sde:.1%}\n(target: {target_gap:.1%})\n"
        f"continuous-time score-error term:\n{tv_bound:.3f} (excludes init. / discretisation)",
        transform=axs[1].transAxes,
        va="top",
        color=INK2,
        fontsize=9,
    )
    axs[2].text(
        0.03,
        0.95,
        f"mass in the gap |x| < {GAP:g}: {gap_ode:.1%}\n(target: {target_gap:.1%})\n"
        f"TV = {tv_ode:.2f}",
        transform=axs[2].transAxes,
        va="top",
        color=INK2,
        fontsize=9,
    )

    ax = axs[3]
    starts = np.linspace(-1, 1, 21)
    ts, exact = ode(starts.copy(), perturbed=False, keep_path=True)
    _, pert = ode(starts.copy(), keep_path=True)
    for k in range(len(starts)):
        ax.plot(ts, exact[:, k], color=MUTED, lw=0.8, alpha=0.8)
        ax.plot(ts, pert[:, k], color=ORANGE, lw=1.1)
    ax.plot([], [], color=MUTED, lw=0.8, label="exact score")
    ax.plot([], [], color=ORANGE, lw=1.1, label="perturbed score")
    ax.set_xscale("log")
    ax.set_xlim(T, DELTA)
    ax.set_xlabel("noise level t  (sampling runs left to right)")
    ax.set_ylabel("sample")
    ax.set_title("(d) ODE paths from 21 starting points")
    ax.legend(loc="upper left")

    fig.suptitle(
        "A score error below 0.07 makes the deterministic sampler output a third mode",
        fontsize=13,
        fontweight="bold",
        y=1.0,
    )
    save(fig, "ode_third_mode.png")


if __name__ == "__main__":
    main()
