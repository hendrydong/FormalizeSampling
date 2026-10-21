"""DF-7: a SMOOTH, uniformly eps-accurate score that breaks the deterministic sampler.

Numerical companion of `Samplers/DiffusionODESmooth.lean` (illustration, not a proof). It runs the
exact Lean construction `smoothScore` in d = 1 on Gaussian data N(M0, V0):

  * deterministic sampler = exponential-integrator probability-flow step `pfMean`,
    y <- y / alpha_k + (1 / alpha_k - 1) s_k(y), k = N, ..., 2, on the geometric grid;
  * the learned score is exact except at k = 2, where s_2(y) = grad log p_2(y) + E(z(y)), z(y)
    the exact update and E(z) = (theta + h Phi_m((z - theta) / h) - z) / b_2, with
    Phi_m = psi^m, psi(u) = u - sin(2 pi u) / (2 pi), h = 2 |b_2| eps, b_2 = 1 / alpha_2 - 1;
  * the Lean proof picks theta (avoid atoms of the law of z: here z is Gaussian, theta = 0
    works), then r = 1 / (j + 1) with p_1(G_r) < eta / 2, G_r = {x : dist((x - theta)/h, Z) <= r},
    then m with nu{|Phi_m(v)| > r} < eta / 2 (v = cell coordinate of z), giving
    TV(p_1, q_1^det) >= q(G_r) - p_1(G_r) >= 1 - eta (`exists_tvSup_detOutput_smoothScore_ge`).
Here every probability in that chain is computed exactly (Gaussian CDF sums) and checked by
Monte Carlo; DDPM with the same score is simulated and compared with the Lean bound
sqrt((I + (r - 1)/2 (1 + (N - 1) log r) + beta_2 eps^2 / 2) / 2) (`pf_ddpm_smooth_separation_geomGrid`).
The Lipschitz constant of E is between (2^m - 1)/|b_2| and (2^m + 1)/|b_2|
(`le_of_lipschitzWith_errProfile`, `lipschitzWith_errProfile`); the sweep over eta shows it must
grow like 1/eta for this construction.
"""

from math import erf, sqrt

import numpy as np
from _gauss_ddpm import lean_bound
from _style import BLUE, INK, INK2, MUTED, ORANGE, RED, geom_grid, grid_ratio, plt, save, setup

M0, V0 = 0.5, 0.25  # data N(M0, V0)
DELTA, HORIZON, N_STEPS = 0.05, 4.0, 1000
EPS = 0.1
THETA = 0.0
SEED = 0
N_MC = 300_000
ETAS = [0.5, 0.3, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002, 0.001]
ETA_SHOW = 0.05

ncdf = np.vectorize(lambda x: 0.5 * (1 + erf(x / sqrt(2))))


def psi(u):
    return u - np.sin(2 * np.pi * u) / (2 * np.pi)


def cell_map(m, u):
    for _ in range(m):
        u = psi(u)
    return u


def cell_map_deriv(m, u):
    """d Phi_m / du by the chain rule (psi' = 1 - cos 2 pi u)."""
    g = np.ones_like(u)
    for _ in range(m):
        g = g * (1 - np.cos(2 * np.pi * u))
        u = psi(u)
    return g


def setting():
    t = geom_grid(DELTA, HORIZON, N_STEPS)
    alpha = np.exp(-np.diff(t))  # alpha[k - 1] = alpha_k
    beta = 1 - alpha**2
    return t, alpha, beta


def true_score(x, t, k):
    a = np.exp(-t[k])
    vk = V0 * a**2 + 1 - a**2
    return -(x - M0 * a) / vk


def det_affine(t, alpha, k):
    """Exact pf update y -> g y + c at step k (the true score is affine)."""
    a = np.exp(-t[k])
    vk = V0 * a**2 + 1 - a**2
    b = 1 / alpha[k - 1] - 1
    return 1 / alpha[k - 1] - b / vk, b * M0 * a / vk


def nu_law(t, alpha):
    """Law of z = exact update at k = 2 applied to rho = law of the det. sampler at index 2."""
    mean, var = 0.0, 1.0
    for k in range(N_STEPS, 1, -1):
        g, c = det_affine(t, alpha, k)
        mean, var = g * mean + c, g**2 * var
    return mean, var


def err_field(z, h, b2, m):
    return (THETA + h * cell_map(m, (z - THETA) / h) - z) / b2


def gauss_mass_bands(mean, var, h, lo, hi):
    """sum_n P(N(mean, var) in [theta + h (n + lo), theta + h (n + hi)]).

    Each band is much narrower than the standard deviation, so Simpson's rule per band is exact
    to ~1e-12 here (vectorised; avoids summing thousands of CDF differences).
    """
    sd = sqrt(var)
    n = np.arange(np.floor((mean - 9 * sd - THETA) / h) - 1, np.ceil((mean + 9 * sd) / h) + 2)
    a, b = THETA + h * (n + lo), THETA + h * (n + hi)

    def f(x):
        return np.exp(-((x - mean) ** 2) / (2 * var)) / (sd * sqrt(2 * np.pi))

    return float(np.sum((b - a) / 6 * (f(a) + 4 * f((a + b) / 2) + f(b))))


def p1_good(r, h, p1):
    return gauss_mass_bands(p1[0], p1[1], h, -r, r)


def threshold(m, r):
    """a with Phi_m(a) = r on [0, 1/2] (Phi_m increasing there); bad set is |v| > a."""
    lo, hi = 0.0, 0.5
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        lo, hi = (mid, hi) if cell_map(m, mid) < r else (lo, mid)
    return 0.5 * (lo + hi)


def nu_bad(m, r, h, nu):
    a = threshold(m, r)
    return gauss_mass_bands(nu[0], nu[1], h, a, 1 - a)


def lean_choice(eta, h, p1, nu):
    """The choices of the Lean proof: smallest j, then smallest m."""
    lo, hi = 0, 1
    while p1_good(1 / (hi + 1), h, p1) >= eta / 2:  # p1_good decreases in j
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if p1_good(1 / (mid + 1), h, p1) >= eta / 2 else (lo, mid)
    j = 0 if p1_good(1.0, h, p1) < eta / 2 else hi
    r = 1 / (j + 1)
    m = 0
    while nu_bad(m, r, h, nu) >= eta / 2:
        m += 1
    return j, r, m


def run_sampler(x, t, alpha, beta, h, b2, m, rng=None):
    """Deterministic pf sampler (rng None) or DDPM, with the Lean smooth score."""
    for k in range(N_STEPS, 1, -1):
        s = true_score(x, t, k)
        if k == 2:
            z = x / alpha[1] + b2 * s
            s = s + err_field(z, h, b2, m)
        a, bt = alpha[k - 1], beta[k - 1]
        if rng is None:
            x = x / a + (1 / a - 1) * s
        else:
            x = (x + bt * s) / a + np.sqrt(bt) / a * rng.standard_normal(x.shape)
    return x


def in_good(x, r, h):
    w = (x - THETA) / h
    return np.abs(w - np.round(w)) <= r


def hist_tv(x, p1, width):
    edges = np.arange(-5.0, 5.0 + 1e-9, width)
    p = np.diff(ncdf((edges - p1[0]) / sqrt(p1[1])))
    c, _ = np.histogram(x, bins=edges)
    q = c / len(x)
    return 0.5 * (np.abs(q - p).sum() + (1 - q.sum()) + (1 - p.sum()))


def main() -> None:
    setup()
    t, alpha, beta = setting()
    b2 = 1 / alpha[1] - 1
    h = 2 * abs(b2) * EPS
    a1 = np.exp(-t[1])
    p1 = (M0 * a1, V0 * a1**2 + 1 - a1**2)
    nu = nu_law(t, alpha)
    r_grid = grid_ratio(DELTA, HORIZON, N_STEPS)
    init, disc = lean_bound([M0], [V0], DELTA, r_grid, N_STEPS)
    ddpm_bound = np.sqrt((init + disc + beta[1] / 2 * EPS**2) / 2)
    print(f"grid N={N_STEPS}, t_1={DELTA}, t_2={t[2]:.4f}: b_2={b2:.4f}, h=2|b_2|eps={h:.5f}")
    print(f"law of z (= nu): N({nu[0]:.4f}, {nu[1]:.4f});  p_1 = N({p1[0]:.4f}, {p1[1]:.4f})")
    print(
        f"Lean DDPM bound (I={init:.4f}, disc={disc:.4f}, score term {beta[1] / 2 * EPS**2:.2e})"
        f": TV <= {ddpm_bound:.4f}"
    )

    rows = []
    for eta in ETAS:
        j, r, m = lean_choice(eta, h, p1, nu)
        pg, nb = p1_good(r, h, p1), nu_bad(m, r, h, nu)
        rows.append((eta, j, r, m, pg, nb, 1 - nb - pg))
    print("eta    | j  | r       | m  | p1(G_r) | q(G_r^c) | certified TV >= | 1-eta | Lip(E) in")
    for eta, j, r, m, pg, nb, lb in rows:
        lip = ((2**m - 1) / b2, (2**m + 1) / b2)
        ok = "ok" if lb >= 1 - eta else "VIOLATED"
        print(
            f"{eta:<6g} | {j:2d} | {r:.5f} | {m:2d} | {pg:.5f} | {nb:.5f}  | {lb:.5f}         "
            f"| {1 - eta:.3f} {ok} | [{lip[0]:.3g}, {lip[1]:.3g}]"
        )

    # the eta = ETA_SHOW run: Monte Carlo of both samplers with the same score
    j, r, m = lean_choice(ETA_SHOW, h, p1, nu)
    rng = np.random.default_rng(SEED)
    x0 = rng.standard_normal(N_MC)
    x_det = run_sampler(x0.copy(), t, alpha, beta, h, b2, m)
    x_ddpm = run_sampler(x0.copy(), t, alpha, beta, h, b2, m, rng=np.random.default_rng(SEED + 1))
    x_ref = p1[0] + sqrt(p1[1]) * np.random.default_rng(SEED + 2).standard_normal(N_MC)
    zs = np.linspace(-1, 1, 400_001)
    e = err_field(zs, h, b2, m)
    lip_num = np.max(np.abs(cell_map_deriv(m, (zs - THETA) / h) - 1)) / b2
    pg = p1_good(r, h, p1)
    q_det_g, q_ddpm_g, p_mc_g = (in_good(x, r, h).mean() for x in (x_det, x_ddpm, x_ref))
    print(f"\neta={ETA_SHOW}: j={j}, r={r:.4f}, m={m}")
    print(
        f"  sup|E| on [-1,1] = {np.max(np.abs(e)):.5f} (<= eps = {EPS}); numerical Lip(E) = "
        f"{lip_num:.4g}; Lean bounds [{(2**m - 1) / b2:.4g}, {(2**m + 1) / b2:.4g}]"
    )
    print(
        f"  test set G_r: p_1 exact {pg:.4f} (MC {p_mc_g:.4f}); det q MC {q_det_g:.4f} "
        f"(exact {1 - nu_bad(m, r, h, nu):.4f}); DDPM q MC {q_ddpm_g:.4f}"
    )
    print(f"  TV(p_1, q_det) >= {q_det_g - pg:.4f} (MC) >= 1 - eta = {1 - ETA_SHOW}")
    tv_d_c, tv_r_c = hist_tv(x_ddpm, p1, 0.05), hist_tv(x_ref, p1, 0.05)
    print(
        f"  DDPM: |p_1(G_r) - q(G_r)| = {abs(q_ddpm_g - pg):.4f}; histogram TV (bin 0.05) "
        f"{tv_d_c:.4f} (exact-sample noise floor {tv_r_c:.4f}); Lean bound {ddpm_bound:.4f}"
    )

    fig, axs = plt.subplots(1, 4, figsize=(19, 4.6), gridspec_kw={"wspace": 0.3})
    ax = axs[0]
    zz = np.linspace(-3 * h, 3 * h, 6001)
    for mm, col, lw in [(1, MUTED, 1.2), (3, BLUE, 1.2), (m, RED, 1.6)]:
        ax.plot(zz / h, err_field(zz, h, b2, mm), color=col, lw=lw, label=f"m = {mm}")
    ax.axhline(EPS, color=INK2, ls="--", lw=1)
    ax.axhline(-EPS, color=INK2, ls="--", lw=1)
    ax.text(-2.95, EPS * 1.04, "±ε", color=INK2, fontsize=9, va="bottom")
    ax.set_xlabel("exact update z, in units of h")
    ax.set_ylabel("score error E(z)")
    ax.set_title("(a) C^∞ score error, |E| ≤ ε")
    ax.set_ylim(-0.13, 0.15)
    ax.legend(loc="upper center", ncol=3, fontsize=8.5)
    ax.text(
        0.98,
        0.04,
        f"Lip(E) ≈ {lip_num:.3g}\n(2^m ± 1)/b₂",
        transform=ax.transAxes,
        ha="right",
        color=INK2,
        fontsize=9,
    )

    ax = axs[1]
    bins = np.linspace(-0.5, 0.5, 201)
    for x, col, lab, al in [
        (x_ref, INK2, "exact p₁ samples", 0.5),
        (x_ddpm, BLUE, "DDPM", 0.6),
        (x_det, ORANGE, "deterministic", 0.85),
    ]:
        w = (x - THETA) / h
        ax.hist(w - np.round(w), bins=bins, density=True, color=col, alpha=al, lw=0, label=lab)
    ax.set_yscale("log")
    ax.set_xlim(-0.5, 0.5)
    ax.set_xlabel("position of the output inside its lattice cell, (x − θ)/h mod 1")
    ax.set_ylabel("density (log)")
    ax.set_title(f"(b) where in the cell? (m = {m}, h = {h:.1e})")
    ax.legend(loc="upper right", fontsize=8.5)

    ax = axs[2]
    labels = ["p₁ (exact)", "DDPM", "deterministic"]
    vals = [pg, q_ddpm_g, q_det_g]
    ax.bar(labels, vals, color=[INK2, BLUE, ORANGE], width=0.6)
    for i, v in enumerate(vals):
        ax.text(i, v + 0.02, f"{v:.3f}", ha="center", color=INK, fontsize=10)
    ax.axhline(1 - ETA_SHOW / 2, color=ORANGE, ls=":", lw=1.2)
    ax.axhline(ETA_SHOW / 2, color=INK2, ls=":", lw=1.2)
    ax.set_ylim(0, 1.1)
    ax.set_ylabel(f"mass of G_r (r = {r:.3g}: within r·h of the lattice)")
    ax.set_title(f"(c) the Lean test set, η = {ETA_SHOW}")
    ax.text(
        0.5,
        0.55,
        f"TV(p₁, q_det) ≥ {q_det_g - pg:.3f}\nDDPM: Lean bound {ddpm_bound:.3f}",
        transform=ax.transAxes,
        ha="center",
        color=INK2,
        fontsize=9.5,
    )

    ax = axs[3]
    et = np.array([row[0] for row in rows])
    ms = np.array([row[3] for row in rows])
    ax.fill_between(1 / et, 2.0**ms - 1, 2.0**ms + 1, color=RED, alpha=0.25, lw=0)
    ax.loglog(1 / et, 2.0**ms, "o-", color=RED, ms=5, label="b₂·Lip(E) ∈ [2^m − 1, 2^m + 1]")
    ax.loglog(1 / et, 1 / et, ":", color=MUTED, label="1/η")
    ax.set_xlabel("1/η  (target: TV ≥ 1 − η)")
    ax.set_ylabel("Lipschitz const. of the update error b₂E")
    ax.set_title("(d) the price: Lip(E) grows like 1/η")
    ax.text(
        0.97,
        0.05,
        f"Lip(E) itself is this / b₂\n(b₂ = {b2:.2e})",
        transform=ax.transAxes,
        ha="right",
        color=INK2,
        fontsize=9,
    )
    ax.legend(loc="upper left", fontsize=8.5)

    fig.suptitle(
        "Smooth, uniformly ε-accurate score (Lean `smoothScore`): DDPM stays close, "
        "the deterministic sampler is TV-far",
        fontsize=13,
        fontweight="bold",
        y=1.0,
    )
    save(fig, "ode_smooth.png")


if __name__ == "__main__":
    main()
