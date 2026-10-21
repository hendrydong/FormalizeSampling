"""Path-space KL of the exact-score DDPM sampler on Gaussian data (illustration, not a proof).

Tests the Lean statements of `Samplers/DiffusionPath.lean` and
`Samplers/DiffusionVarianceMain.lean`:

* `klDiv_truePath_algPath` (chain-rule EQUALITY): the KL between the joint Gaussian laws of the
  true reverse path (x_N, ..., x_1) and the sampler path (y_N, ..., y_1), computed here directly
  from the two joint covariance matrices, equals KL(p_N || N(0, I)) + sum_{k=2}^N D_k with
  D_k = E KL(R_k(y) || Q_k(y)) (`_gauss_ddpm.path_terms`, closed form per step).
* `klDiv_truePath_ddpm_ge_uniform`: for sigma^2 = beta/alpha^2 and data with E|x|^2 <= d, on a
  uniform grid the path KL is >= (d/2)(t_N - t_1)(2 - (1 - e^{-2h})/h): linear in T.
* `klDiv_truePath_betaVar_le_explicit`: for sigma^2 = beta the path KL is bounded uniformly in
  N and T.
* `klDiv_output_le_path`: output KL(p_1 || q_1) <= path KL.

The true path law is the forward chain (x_1 ~ p_1, x_k = alpha_k x_{k-1} + sqrt(beta_k) xi),
which equals the posterior construction by `fwdPath_eq_truePath`.
"""

import numpy as np
from _gauss_ddpm import exact_kl, kappa_grid, path_terms, reverse_variance
from _style import BLUE, INK2, MUTED, ORANGE, geom_grid, plt, save, setup

DELTA = 0.01


def path_laws_1d(m: float, v: float, t):
    """Means and covariances of (x_N, ..., x_1) (forward chain) and (y_N, ..., y_1) per rule."""
    n = len(t) - 1
    ks = np.arange(n, 0, -1)  # path order x_N, ..., x_1
    a = np.exp(-t[ks])
    var = v * a**2 + (1 - a**2)
    mean_p = m * a
    tk = t[ks]
    # Cov(x_k, x_l) = e^{-|t_k - t_l|} V_{min(k, l)} (variance at the earlier time)
    early = np.where(tk[:, None] <= tk[None, :], var[:, None], var[None, :])
    cov_p = np.exp(-np.abs(tk[:, None] - tk[None, :])) * early
    laws_q = {}
    for rule in ("ddpm", "beta"):
        mu = np.zeros(n)
        cov = np.zeros((n, n))
        cov[0, 0] = 1.0
        for i, k in enumerate(range(n, 1, -1)):  # y_{k-1} = g y_k + shift + sigma xi
            alpha = np.exp(-(t[k] - t[k - 1]))
            beta = -np.expm1(-2 * (t[k] - t[k - 1]))
            ak = np.exp(-t[k])
            vk = v * ak**2 + (1 - ak**2)
            g = (1 - beta / vk) / alpha
            shift = beta * m * ak / (vk * alpha)
            s2 = reverse_variance(rule, alpha, beta, np.exp(-2 * t[k - 1]), ak**2)
            mu[i + 1] = g * mu[i] + shift
            cov[i + 1, : i + 1] = g * cov[i, : i + 1]
            cov[: i + 1, i + 1] = cov[i + 1, : i + 1]
            cov[i + 1, i + 1] = g**2 * cov[i, i] + s2
        laws_q[rule] = (mu, cov)
    return (mean_p, cov_p), laws_q


def kl_mvn(mp, cp, mq, cq) -> float:
    lq = np.linalg.cholesky(cq)
    lp = np.linalg.cholesky(cp)
    a = np.linalg.solve(lq, lp)
    b = np.linalg.solve(lq, mp - mq)
    logdet = 2 * (np.sum(np.log(np.diag(lq))) - np.sum(np.log(np.diag(lp))))
    return 0.5 * (np.sum(a**2) + b @ b - len(mp) + logdet)


def path_kl(m, v, t, rule: str) -> float:
    total = 0.0
    for mi, vi in zip(m, v, strict=True):
        (mp, cp), laws_q = path_laws_1d(mi, vi, t)
        mq, cq = laws_q[rule]
        total += kl_mvn(mp, cp, mq, cq)
    return total


def chain_sum(m, v, t, rule: str) -> float:
    steps, init = path_terms(m, v, t, rule)
    return init + float(np.sum(steps))


def uniform_grid(horizon: float, h: float) -> np.ndarray:
    n = int(round((horizon - DELTA) / h)) + 1
    return np.concatenate([[0.0], DELTA + h * np.arange(n)])


def beta_lean_bound(m, v, t) -> float:
    """initBound + min over valid (m, kappa) of the betaVar discretisation constant."""
    d = len(m)
    m2 = float(np.sum(np.asarray(m) ** 2 + np.asarray(v)))
    b1 = -np.expm1(-2 * t[1])
    init = np.exp(-2 * (t[-1] - t[1])) * (d * (b1 - 1 - np.log(b1)) + np.exp(-2 * t[1]) * m2) / 2
    u = np.expm1(2 * t)
    best = np.inf
    ratio = 0.0
    for mm in range(1, len(t)):
        if mm >= 2:
            ratio = max(ratio, (u[mm] - u[mm - 1]) / u[mm - 1])
        kappa = max(ratio, 1 / u[mm])
        if kappa * u[mm] <= 1 + kappa:
            disc = kappa / 2 * (d * (2 + np.log((1 + kappa) / (kappa * u[1]))) + 2 * max(m2 - d, 0))
            best = min(best, disc)
    return init + best


def main() -> None:
    setup()
    rng = np.random.default_rng(1)

    print("== chain-rule equality: direct joint-Gaussian path KL vs KL(p_N||N(0,I)) + sum D_k ==")
    d = 4
    m = rng.normal(size=d)
    v = np.exp(rng.uniform(np.log(0.1), np.log(2.0), size=d))
    grids = {
        "uniform h=0.1, T=4": uniform_grid(4.0, 0.1),
        "geometric N=60, T=6": geom_grid(DELTA, 6.0, 60),
        "kappa=0.3 + one tail step, T=8": kappa_grid(DELTA, 8.0, 0.3, tail=True),
    }
    worst = 0.0
    for name, t in grids.items():
        for rule in ("ddpm", "beta"):
            direct = path_kl(m, v, t, rule)
            chain = chain_sum(m, v, t, rule)
            rel = abs(direct - chain) / chain
            worst = max(worst, rel)
            print(
                f"{name:32s} {rule:5s} N={len(t) - 1:4d} path={direct:.10f} "
                f"chain={chain:.10f} rel.diff={rel:.1e}"
            )
    print(f"worst relative difference: {worst:.1e}")

    # Horizon sweep: d = 1, data N(0, 0.5) (E|x|^2 = 0.5 <= d), uniform step h.
    h = 0.05
    m1, v1 = [0.0], [0.5]
    horizons = np.linspace(1.0, 20.0, 39)
    res = {key: [] for key in ("path_ddpm", "out_ddpm", "path_beta", "out_beta", "lb", "ub")}
    for horizon in horizons:
        t = uniform_grid(horizon, h)
        res["path_ddpm"].append(chain_sum(m1, v1, t, "ddpm"))
        res["path_beta"].append(chain_sum(m1, v1, t, "beta"))
        res["out_ddpm"].append(exact_kl(m1, v1, t, "ddpm"))
        res["out_beta"].append(exact_kl(m1, v1, t, "beta"))
        res["lb"].append(0.5 * (t[-1] - t[1]) * (2 + np.expm1(-2 * h) / h))
        res["ub"].append(beta_lean_bound(m1, v1, t))
    res = {key: np.array(val) for key, val in res.items()}
    print(f"== horizon sweep (d = 1, data N(0, 0.5), uniform step h = {h}) ==")
    for horizon in (1.0, 5.0, 10.0, 20.0):
        i = int(np.argmin(np.abs(horizons - horizon)))
        print(
            f"T={horizons[i]:5.1f}: ddpm path={res['path_ddpm'][i]:.4f} "
            f"(Lean lower {res['lb'][i]:.4f}) output={res['out_ddpm'][i]:.2e} | "
            f"beta path={res['path_beta'][i]:.4f} (Lean upper {res['ub'][i]:.2f}) "
            f"output={res['out_beta'][i]:.2e}"
        )
    assert np.all(res["path_ddpm"] >= res["lb"] - 1e-12)
    assert np.all(res["path_beta"] <= res["ub"])
    assert np.all(res["out_ddpm"] <= res["path_ddpm"] + 1e-12)
    assert np.all(res["out_beta"] <= res["path_beta"] + 1e-12)
    slope = np.polyfit(horizons[10:], res["path_ddpm"][10:], 1)[0]
    print(
        f"ddpm path-KL slope in T: {slope:.5f}  (Lean lower-bound slope "
        f"{0.5 * (2 + np.expm1(-2 * h) / h):.5f})"
    )

    fig, axes = plt.subplots(1, 2, figsize=(12.5, 4.6))
    ax = axes[0]
    ax.plot(horizons, res["path_ddpm"], color=BLUE, label="path KL, σ² = β/α²")
    ax.plot(horizons, res["out_ddpm"], color=BLUE, ls="--", label="output KL, σ² = β/α²")
    ax.plot(horizons, res["path_beta"], color=ORANGE, label="path KL, σ² = β")
    ax.plot(horizons, res["out_beta"], color=ORANGE, ls="--", label="output KL, σ² = β")
    ax.plot(horizons, res["lb"], color=MUTED, ls=":", label="Lean lower bound (β/α²)")
    ax.set_xlabel("horizon T")
    ax.set_ylabel("KL (nats)")
    ax.set_title("(a) path KL grows with T for β/α², output stays flat")
    ax.legend(loc="upper left")

    ax = axes[1]
    ax.semilogy(horizons, res["path_beta"], color=ORANGE, label="path KL, σ² = β")
    ax.semilogy(horizons, res["ub"], color=MUTED, ls=":", label="Lean upper bound (β)")
    ax.semilogy(horizons, res["out_beta"], color=ORANGE, ls="--", label="output KL, σ² = β")
    ax.set_xlabel("horizon T")
    ax.set_title("(b) σ² = β: path KL bounded uniformly in T")
    ax.legend(loc="center right")
    fig.text(
        0.5,
        -0.03,
        f"exact-score DDPM, data N(0, 0.5) in d = 1, uniform step h = {h}, t₁ = {DELTA}; "
        f"chain-rule equality verified to rel. error {worst:.0e}",
        ha="center",
        color=INK2,
        fontsize=9.5,
    )
    save(fig, "path_kl.png")


if __name__ == "__main__":
    main()
