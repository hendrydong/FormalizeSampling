"""DF-6: is the O(1/N) discretisation rate sharp? (illustration, not a proof)

Exact-score DDPM with reverse variance beta_k / alpha_k^2 (`ddpmVar`) on the geometric grid
u_k = e^{2 t_k} - 1 = u_1 r^{k-1}, t_1 = DELTA, t_N = T, dimension d = 1. Three data laws:
a point mass at 0, N(0, 1), and the two-point law (delta_{-1} + delta_{+1}) / 2.

Path quantity D_N = sum_{k=2}^N E KL(R_k y || N(m*_k(y), sigma_k^2)) = sum entropyStep(u_{k-1}, u_k)
(Theorem A). Computed in closed form for Gaussian / point-mass data and by quadrature of
H(u) = int q_u log q_u, J(u) = int q_u'^2 / q_u for the two-point law. Compared with
  * the upper bound of `DiffusionMain` (r-1) d/2 (1 + (N-1) log r),
  * the exact point-mass value of `DiffusionRate` (d/2)(N-1)(log r - 1 + 1/r),
  * the universal lower bound `sum_lintegral_klDiv_revKernel_geomGrid_ge` (best m),
  * the output KL(p_1 || q_1) (closed form for Gaussian / point mass; 1-D density propagation on a
    grid for the two-point law).
Also: D_N with the per-step optimal isotropic variance (Analytic-DPM), and random grids with the
same endpoints u_1, u_N vs the geometric grid for the point mass
(`sum_lintegral_klDiv_revKernel_ddpm_dirac_ge`).
"""

import numpy as np
from _gauss_ddpm import exact_kl
from _style import AQUA, BLUE, INK2, MUTED, ORANGE, VIOLET, geom_grid, plt, save, setup

DELTA, HORIZON, D = 0.01, 5.0, 1
NS = [6, 10, 20, 40, 80, 160, 320]
U1, UN = np.expm1(2 * DELTA), np.expm1(2 * HORIZON)


def heat_grid(n):
    r = (UN / U1) ** (1 / (n - 1))
    return U1 * r ** np.arange(n), r


def gauss_path(s, u):
    """D_N for data N(0, s) in d = 1 (s = 0: point mass): (1/2) sum log((s+b)/(s+a)) - D/(s+b)."""
    a, b = u[:-1], u[1:]
    return 0.5 * np.sum(np.log((s + b) / (s + a)) - (b - a) / (s + b))


def two_point_hj(u):
    """H(u), J(u) of q_u = (N(-1, u) + N(1, u)) / 2 by quadrature."""
    z = np.linspace(-1 - 14 * np.sqrt(u), 1 + 14 * np.sqrt(u), 40001)
    dz = z[1] - z[0]
    e1, e2 = np.exp(-((z - 1) ** 2) / (2 * u)), np.exp(-((z + 1) ** 2) / (2 * u))
    c = 0.5 / np.sqrt(2 * np.pi * u)
    q = c * (e1 + e2)
    dq = -c * ((z - 1) * e1 + (z + 1) * e2) / u
    ok = q > 1e-300
    return np.sum(q[ok] * np.log(q[ok])) * dz, np.sum(dq[ok] ** 2 / q[ok]) * dz


def two_point_path(u):
    hj = np.array([two_point_hj(x) for x in u])
    h, j = hj[:, 0], hj[:, 1]
    delta = np.diff(u)
    steps = h[:-1] - h[1:] - delta * j[1:] / 2
    jj = delta * j[1:]  # = beta_k J^OU_k / d: the Analytic-DPM excess is (d/2) psi(jj)
    return steps.sum(), (steps - 0.5 * (-np.log1p(-jj) - jj)).sum()


def two_point_output(t, x=np.linspace(-5, 5, 1201)):
    """KL(p_1 || q_1) for the two-point law: propagate q on a grid with the exact score."""
    dx = x[1] - x[0]

    def density(tk):
        a, v = np.exp(-tk), -np.expm1(-2 * tk)
        g = np.exp(-((x - a) ** 2) / (2 * v)) + np.exp(-((x + a) ** 2) / (2 * v))
        return g / (2 * np.sqrt(2 * np.pi * v)), a, v

    def score(tk):
        _, a, v = density(tk)
        return (a * np.tanh(a * x / v) - x) / v

    q = np.exp(-(x**2) / 2) / np.sqrt(2 * np.pi)
    for k in range(len(t) - 1, 1, -1):
        h = t[k] - t[k - 1]
        alpha, beta = np.exp(-h), -np.expm1(-2 * h)
        mean = (x + beta * score(t[k])) / alpha
        s2 = beta / alpha**2
        kern = np.exp(-((x[:, None] - mean[None, :]) ** 2) / (2 * s2))
        kern /= kern.sum(axis=0, keepdims=True) * dx
        q = kern @ (q * dx)
    p = density(t[1])[0]
    ok = p > 1e-300
    return float(np.sum(p[ok] * np.log(p[ok] / np.maximum(q[ok], 1e-300))) * dx)


def lean_bounds(r, n, m2):
    upper = (r - 1) * D / 2 * (1 + (n - 1) * np.log(r))
    dirac = D / 2 * (n - 1) * (np.log(r) - 1 + 1 / r)
    best = max(
        D / 2 * ((n - m) * (np.log(r) - 1 + 1 / r) - np.log1p(m2 / (D * U1 * r ** (m - 1))))
        for m in range(1, n + 1)
    )
    return upper, dirac, max(best, 0.0)


def main() -> None:
    setup()
    rows = []
    for n in NS:
        u, r = heat_grid(n)
        t = geom_grid(DELTA, HORIZON, n)
        up, dirac_exact, _ = lean_bounds(r, n, 0.0)
        _, _, lb_m1 = lean_bounds(r, n, 1.0)  # both N(0,1) and the two-point law have M = 1
        p_dirac, p_gauss = gauss_path(0.0, u), gauss_path(1.0, u)
        p_two, p_two_opt = two_point_path(u)
        o_dirac, o_gauss = exact_kl([0.0], [0.0], t), exact_kl([0.0], [1.0], t)
        o_two = two_point_output(t)
        assert abs(p_dirac - dirac_exact) < 1e-9 * max(1, dirac_exact), "point-mass formula"
        for path, lb in [(p_dirac, dirac_exact), (p_gauss, lb_m1), (p_two, lb_m1)]:
            assert lb - 1e-9 <= path <= up, "Lean sandwich violated"
        assert up <= 2 * r * p_dirac + (r - 1) * D / 2 + 1e-12, "discBound_geomGrid_le_dirac"
        rows.append((n, r, up, p_dirac, p_gauss, lb_m1, p_two, p_two_opt, o_dirac, o_gauss, o_two))
    rows = np.array(rows)
    print(f"d = {D}, delta = {DELTA}, T = {HORIZON}, geometric grid")
    print(
        "    N    r-1   upper  dirac(=Lean)  gauss  LB(M=1)  2pt  2pt(opt var)"
        "  out:dirac  out:gauss  out:2pt"
    )
    for row in rows:
        n, r = int(row[0]), row[1]
        print(
            f"{n:5d} {r - 1:6.3f} {row[2]:7.4f} {row[3]:9.4f} {row[4]:9.4f} {row[5]:8.4f} "
            f"{row[6]:7.4f} {row[7]:9.5f} {row[8]:10.2e} {row[9]:10.2e} {row[10]:9.2e}"
        )
    big = rows[:, 0] >= 40
    names = ["dirac", "gauss", "2pt", "2pt optvar", "out dirac", "out gauss", "out 2pt"]
    for name, col in zip(names, [3, 4, 6, 7, 8, 9, 10], strict=True):
        slope = np.polyfit(np.log(rows[big, 0]), np.log(rows[big, col]), 1)[0]
        print(f"  decay exponent (N >= 40) {name:11s}: {slope:.2f}")
    print(f"  upper / dirac at N = {NS[-1]}: {rows[-1, 2] / rows[-1, 3]:.2f}")

    # Random grids vs the geometric grid for the point mass (Jensen bound).
    rng = np.random.default_rng(0)
    n = 40
    big_l = np.log(UN / U1)
    floor = D / 2 * (n - 1) * (big_l / (n - 1) - 1 + np.exp(-big_l / (n - 1)))
    rand = []
    for _ in range(2000):
        w = rng.dirichlet(np.full(n - 1, rng.choice([0.5, 2.0, 20.0])))
        u = U1 * np.exp(np.concatenate([[0.0], np.cumsum(w * big_l)]))
        rand.append(gauss_path(0.0, u))
    rand = np.array(rand)
    assert np.all(rand >= floor - 1e-12), "Jensen lower bound violated"
    print(
        f"random {n}-step grids, point mass: min D_N = {rand.min():.4f}, "
        f"geometric = {floor:.4f} (Lean floor), median ratio {np.median(rand) / floor:.2f}"
    )

    fig, axes = plt.subplots(1, 2, figsize=(12, 4.6))
    ax = axes[0]
    ns = rows[:, 0]
    ax.loglog(ns, rows[:, 2], "--", color=INK2, label="Lean upper bound (DiffusionMain)")
    ax.loglog(ns, rows[:, 3], "-", color=BLUE, label="path D_N, point mass (= Lean exact)")
    ax.loglog(ns, rows[:, 4], "-", color=ORANGE, label="path D_N, N(0,1)")
    ax.loglog(ns, rows[:, 5], ":", color=ORANGE, label="Lean universal lower bound, M = 1")
    ax.loglog(ns, rows[:, 6], "-", color=AQUA, label="path D_N, two-point ±1")
    ax.loglog(ns, rows[:, 7], "-.", color=AQUA, label="two-point, optimal variance")
    ax.loglog(ns, rows[:, 8], "-", color=VIOLET, lw=1.2, label="output KL, point mass")
    ax.loglog(ns, rows[:, 9], "--", color=VIOLET, lw=1.2, label="output KL, N(0,1)")
    ax.loglog(ns, rows[:, 10], ":", color=VIOLET, lw=1.6, label="output KL, two-point")
    ax.set_xlabel("number of steps N")
    ax.set_ylabel("nats")
    ax.set_title("Path D_N is Θ(1/N); output KL decays faster (numerical)")
    ax.legend(loc="lower left", fontsize=7.8)

    ax = axes[1]
    ax.hist(rand, bins=60, color=MUTED, alpha=0.8, label=f"random {n}-step grids")
    ax.axvline(floor, color=BLUE, lw=2, label="geometric grid = Lean floor")
    ax.set_xscale("log")
    ax.set_xlabel("path D_N for a point mass (nats)")
    ax.set_ylabel("count")
    ax.set_title("No grid beats the geometric one")
    ax.legend(loc="upper right")
    fig.suptitle(
        "DDPM discretisation error: sharp O(1/N) at path level (d = 1, T = 5, t₁ = 0.01)",
        fontsize=12.5,
        fontweight="bold",
        y=1.02,
    )
    fig.tight_layout()
    save(fig, "ddpm_rate.png")


if __name__ == "__main__":
    main()
