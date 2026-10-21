"""PX-5: proximal sampler on a non-smooth log-concave target from a cold start (illustration only).

Target pi(x) = e^{-|x|} / 2 (Laplace): f(x) = |x| is convex but not differentiable, and pi has
no log-Sobolev inequality. The chain starts from a point mass rho_0 = delta_{x0}, so
KL(rho_0 || pi) = infinity. One step of the exact proximal sampler of Lee, Shen and Tian (2021)
(`Proximal.proxKernel f eta`) is y ~ N(x, eta), then x' ~ RGO(y) with density proportional to
e^{-|x'| - (x' - y)^2 / (2 eta)}.

Lean (`ProximalLogConcaveRate.klDiv_iterate_le_div'`): for convex f with int e^{-f} < infinity,
every eta > 0, every coupling gamma_0 of (rho_0, pi) and every k >= 1,
    KL(rho_k || pi) <= int (x - y)^2 d gamma_0 / (2 k eta).
For rho_0 = delta_{x0} the only coupling is delta_{x0} x pi, so the right-hand side is
(x0^2 + E_pi[Y^2]) / (2 k eta) = (x0^2 + 2) / (2 k eta). The proof uses the shifted-composition
argument of Altschuler and Chewi (2023).

Numerics: the laws rho_k are propagated exactly on a fine grid (forward Gaussian step as a
matrix, RGO as the normalised grid posterior), and checked against an exact Monte Carlo sampler
of the RGO (rejection from N(y - s eta, eta), s = sign(y), using |x| >= s x).
"""

import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np  # noqa: E402
from _style import AQUA, BLUE, INK2, MUTED, ORANGE, SERIES, plt, save, setup  # noqa: E402

ETA = 1.0
STARTS = (3.0, 10.0, 25.0)
K_MAX = 200
L, DX = 42.0, 0.025
SNAP = (1, 2, 5, 10, 20)


def grid_chain(x0: float, xs: np.ndarray, gauss: np.ndarray, rgo: np.ndarray, k_max: int):
    """Densities of rho_1, ..., rho_kmax on the grid xs (rho_0 = delta_{x0})."""
    q = np.exp(-((xs - x0) ** 2) / (2 * ETA)) / np.sqrt(2 * np.pi * ETA)  # law of y_1, exact
    out = []
    for _ in range(k_max):
        rho = (q * DX) @ rgo  # x' ~ RGO(y)
        rho /= rho.sum() * DX
        out.append(rho)
        q = (rho * DX) @ gauss  # y ~ N(x, eta)
    return np.array(out)


def rgo_sample(y: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    """Exact draw from the density proportional to e^{-|x| - (x - y)^2 / (2 eta)}."""
    s = np.where(y >= 0, 1.0, -1.0)
    out = np.empty_like(y)
    todo = np.arange(y.size)
    while todo.size:
        x = y[todo] - s[todo] * ETA + np.sqrt(ETA) * rng.standard_normal(todo.size)
        ok = rng.random(todo.size) < np.exp(-np.abs(x) + s[todo] * x)
        out[todo[ok]] = x[ok]
        todo = todo[~ok]
    return out


def kl_grid(rho: np.ndarray, pi: np.ndarray) -> float:
    m = rho > 1e-300
    return float(np.sum(rho[m] * np.log(rho[m] / pi[m])) * DX)


def main() -> None:
    setup()
    xs = np.arange(-L, L + DX / 2, DX)
    pi = 0.5 * np.exp(-np.abs(xs))
    pi /= pi.sum() * DX
    gauss = np.exp(-((xs[:, None] - xs[None, :]) ** 2) / (2 * ETA)) / np.sqrt(2 * np.pi * ETA)
    rgo = pi[None, :] * gauss  # row y: unnormalised RGO(y) on the x grid
    rgo /= rgo.sum(axis=1, keepdims=True) * DX
    inv = ((pi * DX) @ gauss * DX) @ rgo
    print(f"grid invariance check: max |pi P - pi| = {np.max(np.abs(inv - pi)):.1e}")
    assert np.max(np.abs(inv - pi)) < 1e-10

    ks = np.arange(1, K_MAX + 1)
    res = {}
    for x0 in STARTS:
        dens = grid_chain(x0, xs, gauss, rgo, K_MAX)
        kl = np.array([kl_grid(r, pi) for r in dens])
        bound = (x0**2 + 2.0) / (2 * ks * ETA)
        assert np.all(kl <= bound), f"KL exceeds the PX-5 bound for x0 = {x0}"
        assert np.all(np.diff(kl) <= 1e-12), "KL must be nonincreasing (data processing)"
        res[x0] = (dens, kl, bound)
        print(f"x0 = {x0:4.1f}, eta = {ETA}: bound = (x0^2 + 2)/(2 k eta)")
        for k in (1, 2, 5, 10, 20, 50):
            print(
                f"   k = {k:3d}: KL = {kl[k - 1]:.4g}   bound = {bound[k - 1]:.4g}"
                f"   ratio = {kl[k - 1] / bound[k - 1]:.3f}"
            )
        j = int(np.argmax(kl / bound))
        print(f"   largest KL / bound = {kl[j] / bound[j]:.3f} at k = {j + 1}")

    # Monte Carlo with the exact RGO sampler, for the start x0 = 10.
    x0 = STARTS[1]
    rng = np.random.default_rng(0)
    n = 200_000
    x = np.full(n, x0)
    edges = np.arange(-L, L + 1e-9, 0.25)
    mc = {}
    for k in range(1, max(SNAP) + 1):
        x = rgo_sample(x + np.sqrt(ETA) * rng.standard_normal(n), rng)
        if k in SNAP:
            mc[k] = np.histogram(x, bins=edges)[0] / n
    dens = res[x0][0]
    for k in SNAP:
        cdf = np.concatenate([[0.0], np.cumsum(dens[k - 1] * DX)])
        grid_bins = np.diff(np.interp(edges, np.concatenate([xs - DX / 2, [xs[-1] + DX / 2]]), cdf))
        tv = 0.5 * np.abs(grid_bins - mc[k]).sum()
        print(f"MC (exact RGO, n = {n}) vs grid, k = {k:2d}: binned TV = {tv:.4f}")
        assert tv < 0.01, "grid propagation disagrees with the exact sampler"

    fig, axes = plt.subplots(1, 3, figsize=(16, 4.6), gridspec_kw={"width_ratios": [1.25, 1, 1]})
    ax = axes[0]
    ax.plot(xs, pi, color=INK2, lw=2.4, ls="--", label="target π ∝ e^{-|x|}")
    centers = 0.5 * (edges[1:] + edges[:-1])
    for i, k in enumerate(SNAP):
        c = SERIES[i]
        ax.plot(xs, dens[k - 1], color=c, label=f"ρ_{k}")
        ax.plot(centers, mc[k] / 0.25, ".", color=c, ms=3.5, alpha=0.8)
    ax.axvline(x0, color=MUTED, lw=1, ls=":")
    ax.text(x0 + 0.2, 0.47, f"ρ₀ = δ at x₀ = {x0:g}\n(KL = ∞)", color=INK2, fontsize=9)
    ax.set_xlim(-6, 13)
    ax.set_ylim(0, 0.55)
    ax.set_xlabel("x")
    ax.set_ylabel("density")
    ax.set_title(f"cold start, η = {ETA:g}: lines = exact grid, dots = exact RGO sampler")
    ax.legend(loc="upper left")

    ax = axes[1]
    for x0_, c in zip(STARTS, (BLUE, ORANGE, AQUA)):
        _, kl, bound = res[x0_]
        ax.loglog(ks, bound, "--", color=c, lw=1.6, label=f"Lean bound (x₀²+2)/(2kη), x₀ = {x0_:g}")
        ax.loglog(ks, kl, color=c, lw=2.4, label=f"KL(ρ_k ‖ π), x₀ = {x0_:g}")
    ax.set_ylim(1e-6, 600)
    ax.set_xlabel("iteration k")
    ax.set_ylabel("KL")
    ax.set_title("KL after k steps vs the 1/k bound")
    ax.legend(loc="lower left", fontsize=8.5)

    ax = axes[2]
    for x0_, c in zip(STARTS, (BLUE, ORANGE, AQUA)):
        _, kl, bound = res[x0_]
        ax.plot(ks * ETA / x0_, kl / bound, color=c, label=f"x₀ = {x0_:g}")
    ax.axhline(1.0, color=MUTED, lw=1, ls="--")
    ax.text(0.05, 1.03, "bound attained", color=INK2, fontsize=9)
    ax.set_ylim(0, 1.15)
    ax.set_xlim(0, 3)
    ax.set_xlabel("rescaled iteration k η / x₀")
    ax.set_ylabel("KL / bound")
    ax.set_title("fraction of the bound used")
    ax.legend(loc="upper right")
    fig.suptitle(
        "PX-5: proximal sampler on the non-smooth log-concave target e^{-|x|} from a point mass",
        fontsize=13,
    )
    fig.tight_layout()
    save(fig, "proximal_logconcave.png")


if __name__ == "__main__":
    main()
