"""FL-6 / Fokker-Planck uniqueness for a Lipschitz, unbounded drift (illustration only).

Lean: `FokkerPlanckUniqueness.eq_of_weakFokkerPlanck_lipschitzWith` says that for a globally
Lipschitz drift b (unbounded allowed) and D > 0 there is at most one curve of probability
measures solving the weak Fokker-Planck equation from a given initial law, with no moment
assumption; `tendsto_emCurveP_of_weakFokkerPlanck_lipschitz` then identifies every solution
with the weak limit of the dyadic Euler-Maruyama laws.

Test: d = 1, b(x) = -x + 2 sin(3x) (Lipschitz constant 7, unbounded), D = 1/2, initial law
Cauchy(1, 1/2) (no mean, no variance). Two independent constructions of "the" solution at
t = 1 are compared:
  (i)  Euler-Maruyama laws with step h = 2^-k, from 10^6 exact Cauchy samples;
  (ii) a conservative finite-volume solver (Scharfetter-Gummel fluxes) of
       d_t rho = -d_x(b rho) + D d_xx rho on [-40, 40], started from the Cauchy density.
Paths starting at |x| > 40 (0.8% of the mass) end near |x| ~ 40 e^{-1} ~ 15, so both are
compared on the window [-5, 5]: sup over x in the window of |mu_EM([-5, x]) - mu_PDE([-5, x])|.
If uniqueness failed, the EM limit and the PDE solution could differ; the distance should
instead decrease like O(h) to the Monte Carlo floor (~ 1e-3).
"""

import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np  # noqa: E402
from _style import BLUE, INK, INK2, MUTED, ORANGE, plt, save, setup  # noqa: E402

D = 0.5
T = 1.0
X = 40.0
WIN = 5.0
N_SAMPLES = 1_000_000
SEED = 0


def drift(x):
    return -x + 2.0 * np.sin(3.0 * x)


def bern(z):
    """Bernoulli function z / (e^z - 1), stable near 0."""
    out = np.ones_like(z)
    nz = np.abs(z) > 1e-8
    out[nz] = z[nz] / np.expm1(z[nz])
    return out


def cauchy_cdf(x):
    return 0.5 + np.arctan((x - 1.0) / 0.5) / np.pi


def pde_solution(dx):
    """Cell masses at time T on [-X, X] (zero-flux boundary) and the cell edges."""
    edges = np.arange(-X, X + dx / 2, dx)
    mass = np.diff(cauchy_cdf(edges))
    rho = mass / dx
    b_face = drift(edges[1:-1])
    pe = b_face * dx / D
    a_minus, a_plus = D / dx * bern(-pe), D / dx * bern(pe)
    dt0 = 0.4 * dx * dx / (2 * D + np.max(np.abs(b_face)) * dx)
    n = int(np.ceil(T / dt0))
    dt = T / n
    for _ in range(n):
        flux = a_minus * rho[:-1] - a_plus * rho[1:]
        rho[:-1] -= dt / dx * flux
        rho[1:] += dt / dx * flux
    return edges, rho * dx


def em_samples(k, rng):
    h = 2.0**-k
    x = 1.0 + 0.5 * np.tan(np.pi * (rng.random(N_SAMPLES) - 0.5))
    for _ in range(int(round(T / h))):
        x += h * drift(x) + np.sqrt(2 * D * h) * rng.standard_normal(N_SAMPLES)
    return x


def window_cdf_pde(edges, mass, grid):
    cum = np.concatenate([[0.0], np.cumsum(mass)])
    f = np.interp(grid, edges, cum)
    return f - f[0]


def window_cdf_em(x, grid):
    xs = np.sort(x)
    f = np.searchsorted(xs, grid, side="right") / x.size
    return f - f[0]


def main():
    setup()
    rng = np.random.default_rng(SEED)
    grid = np.linspace(-WIN, WIN, 2001)
    edges, mass = pde_solution(0.01)
    edges2, mass2 = pde_solution(0.02)
    f_pde = window_cdf_pde(edges, mass, grid)
    f_pde2 = window_cdf_pde(edges2, mass2, grid)
    pde_grid_gap = np.max(np.abs(f_pde - f_pde2))
    print(f"PDE dx=0.01 vs dx=0.02: window Kolmogorov distance {pde_grid_gap:.2e}")
    print(f"PDE mass in window: {f_pde[-1]:.4f}")
    ks = list(range(1, 8))
    dists, xs = [], {}
    for k in ks:
        x = em_samples(k, rng)
        dists.append(np.max(np.abs(window_cdf_em(x, grid) - f_pde)))
        xs[k] = x
        inside = np.mean(np.abs(x) <= WIN)
        print(
            f"h = 2^-{k}: window distance EM vs PDE {dists[-1]:.2e}, EM mass in window {inside:.4f}"
        )
    mc_floor = 1.0 / np.sqrt(N_SAMPLES)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.2))
    centers = 0.5 * (edges[1:] + edges[:-1])
    sel = np.abs(centers) <= WIN
    ax1.plot(centers[sel], mass[sel] / 0.01, color=INK, lw=2.2, label="finite-volume PDE")
    bins = np.linspace(-WIN, WIN, 121)
    for k, c in [(1, ORANGE), (7, BLUE)]:
        hist, _ = np.histogram(xs[k], bins=bins)
        dens = hist / (N_SAMPLES * np.diff(bins))
        ax1.step(bins[:-1], dens, where="post", color=c, lw=1.4, label=f"EM, h = 2^-{k}")
    ax1.set_title("law at t = 1 from a Cauchy initial law")
    ax1.set_xlabel("x")
    ax1.set_ylabel("density")
    ax1.legend()

    hs = 2.0 ** -np.array(ks)
    ax2.loglog(hs, dists, "o-", color=BLUE, label="EM vs PDE (window Kolmogorov)")
    ax2.loglog(hs, dists[0] * hs / hs[0], "--", color=MUTED, lw=1.2, label="slope 1")
    ax2.axhline(mc_floor, color=INK2, lw=1.0, ls=":", label="Monte Carlo scale 1/sqrt(M)")
    ax2.set_title("EM laws converge to the PDE solution")
    ax2.set_xlabel("step h")
    ax2.set_ylabel("distance at t = 1")
    ax2.legend()
    fig.suptitle("b(x) = -x + 2 sin 3x (Lipschitz, unbounded), D = 1/2", color=INK)
    save(fig, "fp_uniqueness.png")


if __name__ == "__main__":
    main()
