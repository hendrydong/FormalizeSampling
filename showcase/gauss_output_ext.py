"""DF-8 extension: two-sided output KL for Gaussian data (illustration, not a proof).

Exact-score DDPM on N(0, v I_d), uniform grid t_k = t_1 + (k - 1) h, t_1 = DELTA, t_N = HORIZON,
closed form via `_gauss_ddpm.py`. Checks the Lean statements of
`Samplers/DiffusionGaussianOutputExt*.lean`:
  * `errWeight_lower_bound` (all k), `algVar_ddpm_ge_of_le_one`: w_1 >= s_1 (1 + rho),
    rho = (e^{2h} - 1)(1 - e^{-2(T - t_1)})   (v <= 1),
  * `klDiv_output_isoGauss_ddpm_ge`: KL >= d rho^2 / (2 (1 + rho)(2 + rho)),
  * `klDiv_output_isoGauss_ddpm_ge_sq`: KL >= d h^2 (1 - e^{-2(T - t_1)})^2 / 3 if e^{2h} <= 2,
  * `algVar_ddpm_sub_gaussVar_mem_of_one_le`, `klDiv_output_isoGauss_ddpm_le_of_one_le`,
    `klDiv_output_isoGauss_ddpm_ge_of_one_le`   (v >= 1),
  * `algVar_beta_sub_gaussVar_eq`, `klDiv_output_isoGauss_beta_le(_of_one_le)`,
    `klDiv_output_isoGauss_beta_one`   (sigma^2 = beta).
The v <= 1 upper bound is DF-8's `klDiv_output_isoGauss_ddpm_le`.
"""

import numpy as np
from _gauss_ddpm import exact_kl
from _style import BLUE, INK2, ORANGE, plt, save, setup

DELTA, HORIZON = 0.01, 5.0
VS = [0.5, 1.0, 2.0, 5.0]
D = 10
NS = [10, 20, 40, 80, 160, 320, 640, 1280]
TOL = 1e-10


def grid(n):
    return np.concatenate([[0.0], np.linspace(DELTA, HORIZON, n)])


def fwd_var(v, t):
    return np.exp(-2 * t) * v + 1 - np.exp(-2 * t)


def alg_vars(v, t, rule):
    """All sampler variances w_k (k = 1..N), w_N = 1, for the exact gain c_k."""
    n = len(t) - 1
    s = fwd_var(v, t)
    w = np.zeros(n + 1)
    w[n] = 1.0
    for k in range(n, 1, -1):
        h = t[k] - t[k - 1]
        alpha, beta = np.exp(-h), -np.expm1(-2 * h)
        gain = alpha * s[k - 1] / s[k]
        var = beta / alpha**2 if rule == "ddpm" else beta
        w[k - 1] = gain**2 * w[k] + var
    return w, s


def init_term(v, t):
    n = len(t) - 1
    s = fwd_var(v, t)
    return np.exp(-2 * t[n]) * (1 - s[n]) * s[1] ** 2 / (s[n] ** 2 * np.exp(-2 * t[1]))


def check_ddpm(v, n):
    """Returns (exact KL, Lean lower, Lean upper) for sigma^2 = beta/alpha^2; asserts all."""
    t = grid(n)
    h = t[2] - t[1]
    eta = np.expm1(2 * h)
    w, s = alg_vars(v, t, "ddpm")
    s1, w1 = s[1], w[1]
    kl = exact_kl(np.zeros(D), np.full(D, v), t)
    assert abs(kl - D * (s1 / w1 - 1 - np.log(s1 / w1)) / 2) <= 1e-9 * max(kl, 1e-300)
    # errWeight_lower_bound for every k with K' = min(1, 1/max_j s_j), h' = h
    phi = np.exp(-2 * t) / s**2
    g = np.exp(-2 * t) / s
    kp = 1 / max(1.0, s[1:n].max(initial=1.0))
    for k in range(1, n + 1):
        lhs = phi[n] * (1 - s[n]) + eta * kp * (g[k] - g[n])
        assert lhs <= phi[k] * (w[k] - s[k]) + TOL * phi[k], (v, n, k)
    gap = 1 - np.exp(-2 * (HORIZON - DELTA))
    if v <= 1:
        rho = eta * gap
        assert s1 * (1 + rho) <= w1 * (1 + TOL)
        lower = D * rho**2 / (2 * (1 + rho) * (2 + rho))
        if np.exp(2 * h) <= 2:
            clean = D * h**2 * gap**2 / 3
            assert clean <= lower * (1 + TOL)
        b = (1 - v) * np.exp(-2 * (2 * HORIZON - DELTA)) + eta
        upper = D * b**2 / (4 * s1**2)
    else:
        eps = (v - 1) * np.exp(-2 * (2 * HORIZON - DELTA)) * s1
        assert eps < 1
        err = w1 - s1
        assert -eps * s1 - TOL <= err <= eta * s1 + TOL
        upper = D * (eta**2 + (eps / (1 - eps)) ** 2) / 4
        rho = eta * (1 - np.exp(-2 * (HORIZON - DELTA)) * s1) / s1 - eps
        lower = D * rho**2 / (2 * (1 + rho) * (2 + rho)) if rho >= 0 else 0.0
    assert lower <= kl * (1 + TOL) and kl <= upper * (1 + TOL), (v, n, lower, kl, upper)
    return kl, lower, upper


def check_beta(v, n):
    """Exact KL and Lean upper bound for sigma^2 = beta; asserts the variance identity."""
    t = grid(n)
    h = t[2] - t[1]
    w, s = alg_vars(v, t, "beta")
    s1, w1 = s[1], w[1]
    kl = exact_kl(np.zeros(D), np.full(D, v), t, rule="beta")
    iota = init_term(v, t)
    dmax = -np.expm1(-2 * h) * np.exp(-2 * DELTA)
    if v == 1:
        assert abs(w1 - s1) <= 1e-12 and kl <= 1e-20
        return kl, 0.0
    dd = (w1 - s1 - iota) / (1 - v)
    assert -TOL <= dd <= dmax * (1 + TOL), (v, n, dd, dmax)
    if v <= 1:
        a = (1 - v) * (np.exp(-2 * (2 * HORIZON - DELTA)) + dmax)
        upper = D * a**2 / (4 * s1**2)
    else:
        eps = (v - 1) * (np.exp(-2 * (2 * HORIZON - DELTA)) * s1 + dmax / s1)
        assert eps < 1
        upper = D * (eps / (1 - eps)) ** 2 / 4
    assert kl <= upper * (1 + TOL), (v, n, kl, upper)
    return kl, upper


def main():
    setup()
    res = {}
    print(
        "v    N     h         KL ddpm    Lean LB    Lean UB    UB/KL  KL/LB  | KL beta    UB beta"
    )
    for v in VS:
        rows = []
        for n in NS:
            h = HORIZON - DELTA
            h /= n - 1
            kl, lo, up = check_ddpm(v, n)
            klb, upb = check_beta(v, n)
            rows.append((n, h, kl, lo, up, klb, upb))
            ratio_lo = kl / lo if lo > 0 else np.inf
            print(
                f"{v:<4} {n:<5} {h:.2e}  {kl:.3e}  {lo:.3e}  {up:.3e}  {up / kl:5.2f}  "
                f"{ratio_lo:5.2f}  | {klb:.3e}  {upb:.3e}"
            )
        res[v] = np.array(rows)
        arr = res[v]
        sl = np.polyfit(np.log(arr[-4:, 1]), np.log(arr[-4:, 2]), 1)[0]
        print(
            f"  slope of ddpm output KL in h (last 4): {sl:.2f}; KL/h^2 = {arr[-1, 2] / arr[-1, 1] ** 2:.3f}"
        )

    fig, axes = plt.subplots(1, 4, figsize=(16, 4.4), sharey=True)
    for ax, v in zip(axes, VS):
        arr = res[v]
        n = arr[:, 0]
        ax.loglog(n, arr[:, 2], color=BLUE, label="output KL, σ² = β/α²")
        ax.loglog(n, arr[:, 4], "--", color=BLUE, alpha=0.6, label="Lean upper bound")
        ok = arr[:, 3] > 0
        ax.loglog(n[ok], arr[ok, 3], ":", color=BLUE, alpha=0.8, label="Lean lower bound")
        if v != 1:
            ax.loglog(n, arr[:, 5], color=ORANGE, label="output KL, σ² = β")
            ax.loglog(n, arr[:, 6], "--", color=ORANGE, alpha=0.6, label="Lean upper bound (β)")
        else:
            ax.text(0.03, 0.04, "σ² = β: KL = 0 exactly", transform=ax.transAxes, color=INK2)
        ax.set_title(f"v = {v}")
        ax.set_xlabel("number of steps N")
    axes[0].set_ylabel(f"KL(p_1 ‖ q_1), d = {D}")
    axes[0].legend(loc="upper right")
    axes[2].legend(loc="upper right")
    fig.suptitle(
        "Gaussian data N(0, vI), exact score: output KL and Lean bounds (Θ(h²) proved for v = 1)",
        y=1.02,
    )
    fig.tight_layout()
    save(fig, "gauss_output_ext.png")


if __name__ == "__main__":
    main()
