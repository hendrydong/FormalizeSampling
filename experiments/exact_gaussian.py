"""Exact Gaussian checks: ULA/SGLD variance recursions, OU/PFG moments, Gaussian Stein.

Conventions. The target is ``N(0, 1)`` with potential ``U(x) = x^2 / 2`` and score ``-x``.

* CE-03 (ULA bias). One ULA step ``X' = (1 - h) X + sqrt(2 h) xi`` started at the target has
  variance ``(1 - h)^2 + 2 h = 1 + h^2``, so the target is not invariant for any ``h > 0``. The
  ULA variance recursion ``v -> (1 - h)^2 v + 2 h`` has fixed point ``2 / (2 - h)`` for
  ``0 < h < 2``. SGLD replaces ``grad U(x) = x`` by ``x + tau * zeta`` with independent
  standard ``zeta``; its fixed point is ``(2 + h tau^2) / (2 - h)``. All in exact Fractions.
* EX-1 (Gaussian moments). ``dX = -a X dt + sqrt(2 a) dW`` and the probability-flow
  (PFG with ``A = a``) ODE ``y' = a (-y + (y - m_t) / v_t)`` both have Gaussian marginals with
  ``m_t = e^{-a t} m0`` and ``v_t = 1 + (v0 - 1) e^{-2 a t}``. The ODE is integrated with
  explicit Euler steps from the quantiles of ``N(m0, v0)`` and compared with the exact flow map
  ``y0 -> m_t + sqrt(v_t / v0) (y0 - m0)``.
* ID-1 (Gaussian Stein). ``E[Z phi(Z)] = E[phi'(Z)]`` for polynomial ``phi`` via the
  exact moments ``E Z^{2k} = (2k - 1)!!``, and ``E[(X - mu) phi(X)] = s^2 E[phi'(X)]`` for
  ``X ~ N(mu, s^2)``. CE-04: a Rademacher variable passes the Stein test for ``phi(z) = z`` but
  fails it for ``phi(z) = z^3``.

These are illustrations and exact arithmetic checks, never proofs.
"""

from __future__ import annotations

import math
import random
from collections.abc import Callable, Sequence
from fractions import Fraction
from statistics import NormalDist

from experiments._common import Check, print_report

H_VALUES: tuple[Fraction, ...] = (
    Fraction(1, 100),
    Fraction(1, 10),
    Fraction(1, 4),
    Fraction(1, 2),
    Fraction(1),
    Fraction(3, 2),
    Fraction(19, 10),
)
TAU2_VALUES: tuple[Fraction, ...] = (Fraction(0), Fraction(1, 2), Fraction(1), Fraction(4))

# ---------------------------------------------------------------------------------------------
# ULA and SGLD variance recursions (exact).
# ---------------------------------------------------------------------------------------------


def ula_variance_step(v: Fraction, h: Fraction) -> Fraction:
    """Variance of ``X' = X - h X + sqrt(2 h) xi`` when ``Var X = v`` and ``xi ~ N(0, 1)``."""
    return (1 - h) ** 2 * v + 2 * h


def ula_one_step_variance_from_target(h: Fraction) -> Fraction:
    """Variance after one ULA step started at the target ``N(0, 1)``: ``1 + h^2``."""
    return ula_variance_step(Fraction(1), h)


def ula_stationary_variance(h: Fraction) -> Fraction:
    """Fixed point ``2 / (2 - h)`` of the ULA variance recursion (requires ``0 < h < 2``)."""
    if not 0 < h < 2:
        raise ValueError("the ULA variance recursion has an attracting fixed point iff 0 < h < 2")
    return 2 / (2 - h)


def sgld_variance_step(v: Fraction, h: Fraction, tau2: Fraction) -> Fraction:
    """Variance of ``X' = X - h (X + tau zeta) + sqrt(2 h) xi`` given ``Var X = v``.

    ``tau2`` is the gradient-noise variance ``tau^2``.

    ``zeta`` and ``xi`` are independent standard normals, independent of ``X``.
    """
    return (1 - h) ** 2 * v + h**2 * tau2 + 2 * h


def sgld_stationary_variance(h: Fraction, tau2: Fraction) -> Fraction:
    """Fixed point ``(2 + h tau^2) / (2 - h)`` of the SGLD variance recursion (``0 < h < 2``)."""
    if not 0 < h < 2:
        raise ValueError("the SGLD variance recursion has an attracting fixed point iff 0 < h < 2")
    return (2 + h * tau2) / (2 - h)


def variance_iterates(
    step: Callable[[Fraction], Fraction], v0: Fraction, n_steps: int
) -> list[Fraction]:
    """``[v0, step(v0), step(step(v0)), ...]`` with ``n_steps`` applications of ``step``."""
    values = [v0]
    for _ in range(n_steps):
        values.append(step(values[-1]))
    return values


def ula_geometric_convergence_holds(h: Fraction, v0: Fraction, n_steps: int) -> bool:
    """Exact check of ``v_n - v_* = (1 - h)^{2 n} (v_0 - v_*)`` for ``n <= n_steps``."""
    v_star = ula_stationary_variance(h)
    iterates = variance_iterates(lambda v: ula_variance_step(v, h), v0, n_steps)
    return all(v - v_star == (1 - h) ** (2 * n) * (v0 - v_star) for n, v in enumerate(iterates))


# ---------------------------------------------------------------------------------------------
# OU and PFG Gaussian moments.
# ---------------------------------------------------------------------------------------------


def ou_gaussian_moments(t: float, a: float, m0: float, v0: float) -> tuple[float, float]:
    """``(m_t, v_t) = (e^{-a t} m0, 1 + (v0 - 1) e^{-2 a t})`` for ``dX = -aX dt + sqrt(2a) dW``."""
    decay = math.exp(-a * t)
    return decay * m0, 1.0 + (v0 - 1.0) * decay * decay


def pfg_velocity(y: float, m_t: float, v_t: float, a: float) -> float:
    """PFG velocity ``a (score_target(y) - score_t(y)) = a (-y + (y - m_t) / v_t)``."""
    return a * (-y + (y - m_t) / v_t)


def pfg_flow_map(y0: float, t: float, a: float, m0: float, v0: float) -> float:
    """Exact solution of the PFG ODE: the increasing affine map ``m_t + sqrt(v_t/v0)(y0 - m0)``."""
    m_t, v_t = ou_gaussian_moments(t, a, m0, v0)
    return m_t + math.sqrt(v_t / v0) * (y0 - m0)


def affine_field_moment_derivatives(
    m: Fraction, v: Fraction, a: Fraction
) -> tuple[Fraction, Fraction]:
    """``(m', v')`` induced on ``N(m, v)`` by the PFG field written as ``y' = alpha y + beta``.

    For an affine field ``y' = alpha y + beta`` the mean moves by ``alpha m + beta`` and the
    variance by ``2 alpha v``; here ``alpha = a (1 / v - 1)`` and ``beta = -a m / v``.
    """
    alpha = a * (1 / v - 1)
    beta = -a * m / v
    return alpha * m + beta, 2 * alpha * v


def ou_moment_derivatives(m: Fraction, v: Fraction, a: Fraction) -> tuple[Fraction, Fraction]:
    """``(m', v') = (-a m, -2 a v + 2 a)`` from the OU generator applied to ``x`` and ``x^2``."""
    return -a * m, -2 * a * v + 2 * a


def initial_quantiles(n: int, m0: float, v0: float) -> list[float]:
    """The ``(i + 1/2) / n`` quantiles of ``N(m0, v0)`` for ``i = 0, ..., n - 1``."""
    dist = NormalDist(m0, math.sqrt(v0))
    return [dist.inv_cdf((i + 0.5) / n) for i in range(n)]


def euler_pfg_particles(
    y0: Sequence[float], t_end: float, steps: int, a: float, m0: float, v0: float
) -> list[float]:
    """Explicit Euler integration of ``y' = a(-y + (y - m_t)/v_t)`` with exact ``(m_t, v_t)``."""
    dt = t_end / steps
    ys = list(y0)
    for k in range(steps):
        m_t, v_t = ou_gaussian_moments(k * dt, a, m0, v0)
        ys = [y + dt * pfg_velocity(y, m_t, v_t, a) for y in ys]
    return ys


def euler_quantile_error(n: int, t_end: float, steps: int, a: float, m0: float, v0: float) -> float:
    """Max distance between Euler particles and the quantiles of ``N(m_T, v_T)`` at ``t_end``."""
    y0 = initial_quantiles(n, m0, v0)
    m_t, v_t = ou_gaussian_moments(t_end, a, m0, v0)
    target = NormalDist(m_t, math.sqrt(v_t))
    ys = euler_pfg_particles(y0, t_end, steps, a, m0, v0)
    return max(abs(y - target.inv_cdf((i + 0.5) / n)) for i, y in enumerate(ys))


def flow_map_quantile_error(n: int, t: float, a: float, m0: float, v0: float) -> float:
    """Max distance between the exact flow map of the quantiles and the quantiles at time ``t``."""
    m_t, v_t = ou_gaussian_moments(t, a, m0, v0)
    target = NormalDist(m_t, math.sqrt(v_t))
    y0 = initial_quantiles(n, m0, v0)
    return max(
        abs(pfg_flow_map(y, t, a, m0, v0) - target.inv_cdf((i + 0.5) / n)) for i, y in enumerate(y0)
    )


# ---------------------------------------------------------------------------------------------
# Gaussian Stein identity with exact moments.
# ---------------------------------------------------------------------------------------------

Poly = Sequence[Fraction]  # coefficients c_0, c_1, ..., c_n of sum_j c_j x^j


def odd_double_factorial(n: int) -> int:
    """``n!!`` for odd ``n >= -1``, with ``(-1)!! = 1``."""
    if n < -1 or n % 2 == 0:
        raise ValueError("odd_double_factorial expects an odd n >= -1")
    result = 1
    for k in range(n, 0, -2):
        result *= k
    return result


def std_normal_moment(n: int) -> int:
    """``E Z^n`` for ``Z ~ N(0, 1)``: ``0`` for odd ``n`` and ``(n - 1)!!`` for even ``n``."""
    if n < 0:
        raise ValueError("moment order must be non-negative")
    return 0 if n % 2 else odd_double_factorial(n - 1)


def gaussian_moment(n: int, mean: Fraction, var: Fraction) -> Fraction:
    """``E X^n`` for ``X ~ N(mean, var)``, exactly, by expanding ``(mean + sqrt(var) Z)^n``."""
    return sum(
        (
            math.comb(n, k) * mean ** (n - k) * var ** (k // 2) * std_normal_moment(k)
            for k in range(0, n + 1, 2)
        ),
        Fraction(0),
    )


def rademacher_moment(n: int) -> int:
    """``E R^n`` for ``R`` uniform on ``{-1, 1}``."""
    return 1 if n % 2 == 0 else 0


def poly_expectation(coeffs: Poly, moment: Callable[[int], Fraction | int]) -> Fraction:
    """``E[phi(X)]`` from the moments of ``X``."""
    return sum((Fraction(c) * moment(j) for j, c in enumerate(coeffs)), Fraction(0))


def poly_derivative(coeffs: Poly) -> list[Fraction]:
    """Coefficients of ``phi'``."""
    return [j * Fraction(c) for j, c in enumerate(coeffs)][1:] or [Fraction(0)]


def poly_times_x_minus(coeffs: Poly, shift: Fraction) -> list[Fraction]:
    """Coefficients of ``(x - shift) phi(x)``."""
    out = [Fraction(0)] * (len(coeffs) + 1)
    for j, c in enumerate(coeffs):
        out[j + 1] += c
        out[j] -= shift * c
    return out


def stein_sides(
    coeffs: Poly, mean: Fraction = Fraction(0), var: Fraction = Fraction(1)
) -> tuple[Fraction, Fraction]:
    """``(E[(X - mean) phi(X)], var * E[phi'(X)])`` for ``X ~ N(mean, var)``, exactly."""

    def moment(n: int) -> Fraction:
        return gaussian_moment(n, mean, var)

    lhs = poly_expectation(poly_times_x_minus(coeffs, mean), moment)
    rhs = var * poly_expectation(poly_derivative(coeffs), moment)
    return lhs, rhs


def rademacher_stein_sides(coeffs: Poly) -> tuple[Fraction, Fraction]:
    """``(E[R phi(R)], E[phi'(R)])`` for a Rademacher ``R``; equal iff the Stein test passes."""
    lhs = poly_expectation(poly_times_x_minus(coeffs, Fraction(0)), rademacher_moment)
    rhs = poly_expectation(poly_derivative(coeffs), rademacher_moment)
    return lhs, rhs


def random_rational_poly(rng: random.Random, degree: int) -> list[Fraction]:
    """A polynomial with small random rational coefficients (deterministic given ``rng``)."""
    return [Fraction(rng.randint(-9, 9), rng.randint(1, 7)) for _ in range(degree + 1)]


# ---------------------------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------------------------


def run_checks(seed: int = 20251013) -> list[Check]:
    """Run every check in this module and return the results."""
    checks: list[Check] = []

    ula_ok = all(ula_one_step_variance_from_target(h) == 1 + h**2 for h in H_VALUES)
    sample = ", ".join(f"h={h}: {ula_one_step_variance_from_target(h)}" for h in H_VALUES[1:4])
    checks.append(Check("CE-03 ULA one step from N(0,1) has variance 1 + h^2", ula_ok, sample))

    fixed_ok = all(
        ula_variance_step(ula_stationary_variance(h), h) == ula_stationary_variance(h)
        and ula_stationary_variance(h) > 1
        for h in H_VALUES
    )
    checks.append(
        Check(
            "ULA stationary variance 2/(2-h) is the fixed point (and > 1)",
            fixed_ok,
            ", ".join(f"h={h}: {ula_stationary_variance(h)}" for h in H_VALUES[1:4]),
        )
    )

    geometric_ok = all(ula_geometric_convergence_holds(h, Fraction(1), 15) for h in H_VALUES)
    checks.append(
        Check("ULA variance iterates: v_n - v* = (1-h)^(2n) (v_0 - v*)", geometric_ok, "n <= 15")
    )

    sgld_ok = all(
        sgld_variance_step(sgld_stationary_variance(h, t2), h, t2)
        == sgld_stationary_variance(h, t2)
        and sgld_stationary_variance(h, t2) == (2 + h * t2) / (2 - h)
        for h in H_VALUES
        for t2 in TAU2_VALUES
    )
    sgld_reduces = all(
        sgld_stationary_variance(h, Fraction(0)) == ula_stationary_variance(h) for h in H_VALUES
    )
    checks.append(
        Check(
            "SGLD stationary variance (2 + h tau^2)/(2 - h); tau = 0 recovers ULA",
            sgld_ok and sgld_reduces,
            f"h=1/2, tau^2=1: {sgld_stationary_variance(Fraction(1, 2), Fraction(1))}",
        )
    )

    rng = random.Random(seed)
    moment_ode_ok = True
    for _ in range(50):
        m = Fraction(rng.randint(-20, 20), rng.randint(1, 9))
        v = Fraction(rng.randint(1, 30), rng.randint(1, 9))
        a = Fraction(rng.randint(1, 9), rng.randint(1, 5))
        moment_ode_ok &= affine_field_moment_derivatives(m, v, a) == ou_moment_derivatives(m, v, a)
    checks.append(
        Check(
            "PFG field and OU generator induce the same Gaussian moment ODE (Fractions)",
            moment_ode_ok,
            "m' = -a m, v' = 2a(1 - v) at 50 rational (m, v, a)",
        )
    )

    a, m0, v0, t_end, n = 1.0, 2.0, 0.25, 1.0, 101
    map_err = flow_map_quantile_error(n, t_end, a, m0, v0)
    checks.append(
        Check(
            "Exact PFG flow map sends N(m0,v0) quantiles to N(m_t,v_t) quantiles",
            map_err < 1e-9,
            f"max error {map_err:.1e}",
        )
    )
    err_coarse = euler_quantile_error(n, t_end, 500, a, m0, v0)
    err_fine = euler_quantile_error(n, t_end, 1000, a, m0, v0)
    ratio = err_coarse / err_fine
    checks.append(
        Check(
            "Euler-integrated PFG particles match OU moment formulas (first order in dt)",
            err_fine < 5e-3 and 1.8 < ratio < 2.2,
            f"max error {err_coarse:.2e} (dt=1/500), {err_fine:.2e} (dt=1/1000), ratio {ratio:.3f}",
        )
    )

    rng = random.Random(seed + 1)
    stein_ok = True
    for degree in range(0, 9):
        coeffs = random_rational_poly(rng, degree)
        lhs, rhs = stein_sides(coeffs)
        stein_ok &= lhs == rhs
    moments = [std_normal_moment(2 * k) for k in range(6)]
    checks.append(
        Check(
            "ID-1 Gaussian Stein E[Z phi(Z)] = E[phi'(Z)] for random polynomials (exact)",
            stein_ok,
            f"E Z^(2k), k=0..5: {moments}",
        )
    )

    shifted_ok = True
    for _ in range(20):
        coeffs = random_rational_poly(rng, rng.randint(0, 7))
        mean = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
        var = Fraction(rng.randint(1, 9), rng.randint(1, 5))
        lhs, rhs = stein_sides(coeffs, mean, var)
        shifted_ok &= lhs == rhs
    checks.append(
        Check(
            "ID-1 for N(mu, s^2): E[(X - mu) phi(X)] = s^2 E[phi'(X)] (exact)",
            shifted_ok,
            "20 random (phi, mu, s^2)",
        )
    )

    linear = rademacher_stein_sides([Fraction(0), Fraction(1)])
    cubic = rademacher_stein_sides([Fraction(0), Fraction(0), Fraction(0), Fraction(1)])
    checks.append(
        Check(
            "CE-04 Rademacher passes the Stein test for phi = z but fails for phi = z^3",
            linear[0] == linear[1] and cubic[0] != cubic[1],
            f"phi=z: {linear[0]} vs {linear[1]}; phi=z^3: {cubic[0]} vs {cubic[1]}",
        )
    )
    return checks


def main() -> int:
    return print_report("exact_gaussian: ULA/SGLD, OU/PFG moments, Gaussian Stein", run_checks())


if __name__ == "__main__":
    raise SystemExit(main())
