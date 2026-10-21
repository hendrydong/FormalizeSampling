"""DF-9: deterministic samplers are stable in W2 / W_inf under uniform score error, not in TV.

Numerical companion of `Samplers/DiffusionODELipschitz.lean` (illustration, not a proof).

(a, b) The DF-7 construction (`showcase/ode_smooth.py`, Lean `smoothScore`), d = 1, data
N(M0, V0), exponential-integrator probability-flow sampler on the geometric grid. Only the last
step k = 2 is perturbed: z -> theta + h Phi_m((z - theta)/h), h = 2 |b_2| eps, with (r, m) chosen
as in the Lean proof for TV(p_1, q_1) >= 1 - eta. Lean (`smooth_separation_tv_far_w2_close`):
the same output is coupled with the exact-score deterministic output q*_1 within |b_2| eps a.s.
We compute W2(q_1, q*_1) both from the synchronous coupling and from the 1D quantile formula,
the certified TV lower bounds TV(p_1, q_1) >= q(G_r) - p_1(G_r) and
TV(q*_1, q_1) >= q(G_r) - q*(G_r) (exact Gaussian band sums), and TV(p_1, q*_1) (exact).

(c) Multi-step Gaussian example (`pf_isoGauss_coupling`): data N(0, V0), exact maps
y -> g_k y, learned score = exact + e_k(y) with |e_k| <= eps at every step, either constant
(e = eps, the worst case, where the bound is attained numerically; Lean does not prove this) or
oscillating (eps sin(omega y)). Lean bound:
W2 <= W_inf <= B = sum_{i=2}^N (prod_{1<j<i} |g_j|) |b_i| eps (`lipBound`).
"""

from math import sqrt

import numpy as np
import ode_smooth as df7
from _style import AQUA, BLUE, INK2, MUTED, ORANGE, geom_grid, plt, save, setup

SEED = 0
N_MC = 400_000
ETA = 0.05
EPS_A = [0.3, 0.1, 0.03, 0.01, 0.003]
V0_C = 0.25
N_C = 200
EPS_C = [0.3, 0.1, 0.03, 0.01, 0.003, 0.001]
OMEGA = 200.0


def gauss_tv(m1, v1, m2, v2):
    x = np.linspace(-8, 8, 400_001)

    def f(m, v):
        return np.exp(-((x - m) ** 2) / (2 * v)) / sqrt(2 * np.pi * v)

    return 0.5 * float(np.sum(np.abs(f(m1, v1) - f(m2, v2))) * (x[1] - x[0]))


def w2_quantile(a, b):
    return float(np.sqrt(np.mean((np.sort(a) - np.sort(b)) ** 2)))


def part_a(rng):
    t, alpha, _ = df7.setting()
    b2 = 1 / alpha[1] - 1
    a1 = np.exp(-t[1])
    p1 = (df7.M0 * a1, df7.V0 * a1**2 + 1 - a1**2)
    nu = df7.nu_law(t, alpha)  # law of the exact-score deterministic output q*_1
    tv_p_star = gauss_tv(p1[0], p1[1], nu[0], nu[1])
    print(f"(a) DF-7 setting: b_2 = {b2:.4e}, eta = {ETA}, q*_1 = N({nu[0]:.4f}, {nu[1]:.4f})")
    print(f"    TV(p_1, q*_1) = {tv_p_star:.4f} (exact-score deterministic sampler)")
    print("eps    | m  | Lean |b2|eps | sup|x-x*| | W2 sync  | W2 quant | TV(p1,q)>= | TV(q*,q)>=")
    z = nu[0] + sqrt(nu[1]) * rng.standard_normal(N_MC)
    rows = []
    for eps in EPS_A:
        h = 2 * abs(b2) * eps
        _, r, m = df7.lean_choice(ETA, h, p1, nu)
        x = df7.THETA + h * df7.cell_map(m, (z - df7.THETA) / h)
        bound = abs(b2) * eps
        sup = float(np.max(np.abs(x - z)))
        w2s = float(np.sqrt(np.mean((x - z) ** 2)))
        w2q = w2_quantile(x, z)
        nb = df7.nu_bad(m, r, h, nu)
        tv_p = 1 - nb - df7.p1_good(r, h, p1)
        tv_s = 1 - nb - df7.gauss_mass_bands(nu[0], nu[1], h, -r, r)
        assert sup <= bound * (1 + 1e-12), "Lean W_inf bound violated"
        assert w2q <= w2s * (1 + 1e-9) <= bound * (1 + 1e-9), "Lean W2 bound violated"
        assert tv_p >= 1 - ETA, "Lean TV lower bound violated"
        rows.append((eps, bound, sup, w2s, w2q, tv_p, tv_s))
        print(
            f"{eps:<6g} | {m:2d} | {bound:.4e}  | {sup:.4e} | {w2s:.3e} | {w2q:.3e} | "
            f"{tv_p:.4f}     | {tv_s:.4f}"
        )
    return np.array(rows), tv_p_star


def part_c(rng):
    t = geom_grid(df7.DELTA, df7.HORIZON, N_C)
    alpha = np.exp(-np.diff(t))  # alpha[k - 1] = alpha_k
    a = np.exp(-t)
    s = V0_C * a**2 + 1 - a**2  # forward variances s_k
    b = np.zeros(N_C + 1)
    g = np.zeros(N_C + 1)
    for k in range(1, N_C + 1):
        b[k] = 1 / alpha[k - 1] - 1
        g[k] = 1 / alpha[k - 1] - b[k] / s[k]
    # lipBound with delta_i = |b_i| eps: B_1 = sum_{i=2}^N (prod_{1<j<i} |g_j|) |b_i| eps
    amp = np.array([np.prod(np.abs(g[2:i])) * abs(b[i]) for i in range(2, N_C + 1)])
    unit_bound = float(amp.sum())
    x0 = rng.standard_normal(N_MC)
    x_star = x0 * np.prod(g[2:])
    w1 = float(np.prod(g[2:]) ** 2)
    print(f"\n(c) Gaussian data N(0, {V0_C}), N = {N_C}: exact output N(0, {w1:.4f}), ")
    print(f"    all g_k > 0: {bool(np.all(g[2:] > 0))}; Lean bound B = {unit_bound:.4f} * eps")
    print("eps    | Lean B    | const: sup, W2 quant   | sin: sup, W2 quant")
    rows = []
    for eps in EPS_C:
        out = []
        for kind in ("const", "sin"):
            x = x0.copy()
            for k in range(N_C, 1, -1):
                e = eps if kind == "const" else eps * np.sin(OMEGA * x)
                x = g[k] * x + b[k] * e
            sup = float(np.max(np.abs(x - x_star)))
            assert sup <= unit_bound * eps * (1 + 1e-9), "Lean bound violated"
            out += [sup, w2_quantile(x, x_star)]
        rows.append((eps, unit_bound * eps, *out))
        print(
            f"{eps:<6g} | {unit_bound * eps:.3e} | {out[0]:.3e}, {out[1]:.3e} | "
            f"{out[2]:.3e}, {out[3]:.3e}"
        )
    return np.array(rows)


def main() -> None:
    setup()
    rng = np.random.default_rng(SEED)
    ra, tv_p_star = part_a(rng)
    rc = part_c(rng)

    fig, axs = plt.subplots(1, 3, figsize=(16, 4.6), gridspec_kw={"wspace": 0.3})
    ax = axs[0]
    ax.loglog(ra[:, 0], ra[:, 1], "--", color=INK2, lw=1.5, label="Lean bound |b₂| ε")
    ax.loglog(ra[:, 0], ra[:, 2], "o-", color=BLUE, ms=6, label="sup |x − x*| (W∞ coupling)")
    ax.loglog(ra[:, 0], ra[:, 4], "s-", color=ORANGE, ms=6, label="W₂ (quantile formula)")
    ax.set_xlabel("uniform score accuracy ε")
    ax.set_ylabel("distance to exact-score output q*₁")
    ax.set_title("(a) DF-7 score: transport-close")
    ax.legend(loc="upper left", fontsize=8.5)

    ax = axs[1]
    ax.semilogx(ra[:, 0], ra[:, 5], "o-", color=BLUE, ms=6, label="TV(p₁, q₁) ≥ (certified)")
    ax.semilogx(ra[:, 0], ra[:, 6], "s-", color=ORANGE, ms=6, label="TV(q*₁, q₁) ≥ (certified)")
    ax.axhline(1 - ETA, color=INK2, ls="--", lw=1.2, label=f"Lean: 1 − η = {1 - ETA}")
    ax.axhline(tv_p_star, color=MUTED, ls=":", lw=1.5, label="TV(p₁, q*₁) exact score")
    ax.set_ylim(-0.02, 1.05)
    ax.text(
        0.97,
        0.88,
        "the two certified bounds coincide",
        transform=ax.transAxes,
        ha="right",
        color=INK2,
        fontsize=8.5,
    )
    ax.set_xlabel("uniform score accuracy ε")
    ax.set_ylabel("total variation")
    ax.set_title(f"(b) same samplers: TV-far (η = {ETA})")
    ax.legend(loc="center left", fontsize=8.5)

    ax = axs[2]
    ax.loglog(rc[:, 0], rc[:, 1], "--", color=INK2, lw=1.5, label="Lean lipBound B")
    ax.loglog(rc[:, 0], rc[:, 3], "o-", color=BLUE, ms=6, label="W₂, constant error ε")
    ax.loglog(rc[:, 0], rc[:, 5], "s-", color=AQUA, ms=6, label=f"W₂, error ε sin({OMEGA:g} y)")
    ax.set_xlabel("uniform score accuracy ε (every step)")
    ax.set_ylabel("W₂(q₁, exact output N(0, w₁))")
    ax.set_title(f"(c) Gaussian data, {N_C} pf steps")
    ax.legend(loc="upper left", fontsize=8.5)

    fig.suptitle(
        "Deterministic sampler: uniform score accuracy controls W₂ / W∞ (Lean DF-9), not TV",
        fontsize=13,
        fontweight="bold",
        y=1.0,
    )
    save(fig, "ode_lipschitz.png")


if __name__ == "__main__":
    main()
