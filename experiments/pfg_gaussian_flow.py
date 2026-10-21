"""PFG for Gaussians in d = 2 and finite-feature SVGD in d = 1.

Part 1: population PFG moment dynamics (FL-1, FL-2, ID-3).
Target ``p_* = N(0, S*)``, particle law ``p = N(m, S)``, constant SPD preconditioner
``A = H^{-1}``. The PFG velocity ``v(x) = A (grad log p_*(x) - grad log p(x))`` equals

    v(x) = A (-S*^{-1} x + S^{-1} (x - m)) = A G x - A S^{-1} m,      G = S^{-1} - S*^{-1},

which is affine, so the Gaussian family is preserved and (with ``delta = x - m``,
``delta' = A G delta``)

    m' = E v(X) = A G m - A S^{-1} m = -A S*^{-1} m,
    S' = (A G) S + S (A G)^T = A (S^{-1} - S*^{-1}) S + S (S^{-1} - S*^{-1}) A.

Expanding, ``S' = 2A - M S - S M^T`` with ``M = A S*^{-1}``: the Lyapunov moment equation of the
preconditioned Langevin SDE ``dX = -A S*^{-1} X dt + sqrt(2A) dW``.
Exact Fraction checks: the two forms agree; the Gaussian ``p_t`` with these moments solves the
continuity equation ``d/dt log p = -div(p v) / p`` pointwise; and
``d/dt KL(p_t || p_*) = -E_p[(grad log(p/p_*))^T A grad log(p/p_*)]``.
The closed-form solution ``m_t = e^{-tM} m0``, ``S_t = S* + e^{-tM} (S0 - S*) e^{-tM^T}`` is
compared with RK4, and KL decay is compared for ``A = I`` and ``A = S*`` on an ill-conditioned
``S*`` with eigenvalues 100 and 1. Both choices have fastest rate ``lambda_max(M) = 1``; with
``A = S*`` every rate equals 1 (``M = I``), with ``A = I`` the slowest rate is 1/100.

Part 2: finite-feature SVGD (SE-2). Features ``psi(x) = (1, x)``, kernel
``k(x, y) = psi(x) . psi(y) = 1 + x y`` and ``f_W(x) = W . psi(x)``. On fixed particles
``y_1..y_n`` with target score ``s``, the regularised Stein objective

    L(W) = -(1/n) sum_j [f_W'(y_j) + f_W(y_j) s(y_j)] + (lambda/2) |W|^2

is minimised by ``W* = (1/(lambda n)) sum_j [s(y_j) psi(y_j) + psi'(y_j)]``, and
``W* . psi(x) = (1/(lambda n)) sum_j [k(y_j, x) s(y_j) + d/dy k(y, x)|_{y=y_j}]`` is the SVGD
direction. Replacing the fixed (RKHS) norm by PFG's distribution-weighted norm
``(1/2) E_p |f_W|^2`` gives a different minimiser; for a Gaussian ``p`` it is the ``L^2(p)``
projection of ``v* = s - grad log p`` onto ``span psi`` (by Stein's identity). Exact Fractions.

Illustrations and exact arithmetic checks; never proofs.
"""

from __future__ import annotations

import math
import random
from collections.abc import Callable, Sequence
from fractions import Fraction

from experiments._common import Check, print_report
from experiments.exact_gaussian import gaussian_moment, poly_expectation

Num = Fraction | float
Mat = list[list[Num]]
Vec = list[Num]
SEED = 20251013

# ---------------------------------------------------------------------------------------------
# 2 x 2 linear algebra over Fractions or floats.
# ---------------------------------------------------------------------------------------------


def mm(A: Mat, B: Mat) -> Mat:
    return [
        [sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
        for i in range(len(A))
    ]


def madd(A: Mat, B: Mat) -> Mat:
    return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def msub(A: Mat, B: Mat) -> Mat:
    return [[a - b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def mscale(c, A: Mat) -> Mat:
    return [[c * a for a in row] for row in A]


def transpose(A: Mat) -> Mat:
    return [list(col) for col in zip(*A)]


def mv(A: Mat, x: Vec) -> Vec:
    return [sum(a * b for a, b in zip(row, x)) for row in A]


def dot(x: Vec, y: Vec):
    return sum(a * b for a, b in zip(x, y))


def trace(A: Mat):
    return sum(A[i][i] for i in range(len(A)))


def det2(A: Mat):
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]


def inv2(A: Mat) -> Mat:
    d = det2(A)
    if d == 0:
        raise ZeroDivisionError("singular 2x2 matrix")
    return [[A[1][1] / d, -A[0][1] / d], [-A[1][0] / d, A[0][0] / d]]


def identity2(one=1.0) -> Mat:
    zero = one - one
    return [[one, zero], [zero, one]]


def to_float(A: Mat) -> list[list[float]]:
    return [[float(a) for a in row] for row in A]


def expm2(M: list[list[float]]) -> list[list[float]]:
    """Matrix exponential of a 2 x 2 float matrix by scaling and squaring a Taylor series."""
    norm = max(sum(abs(a) for a in row) for row in M)
    squarings = max(0, math.ceil(math.log2(norm)) + 4) if norm > 0 else 0
    X = mscale(1.0 / 2**squarings, M)
    result, term = identity2(), identity2()
    for k in range(1, 20):
        term = mscale(1.0 / k, mm(term, X))
        result = madd(result, term)
    for _ in range(squarings):
        result = mm(result, result)
    return result


def random_spd(rng: random.Random) -> Mat:
    """``L L^T`` for a random rational lower-triangular ``L`` with non-zero diagonal."""
    a = Fraction(rng.randint(1, 6), rng.randint(1, 4))
    c = Fraction(rng.randint(1, 6), rng.randint(1, 4))
    b = Fraction(rng.randint(-6, 6), rng.randint(1, 4))
    return [[a * a, a * b], [a * b, b * b + c * c]]


def random_vec(rng: random.Random) -> Vec:
    return [Fraction(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(2)]


# ---------------------------------------------------------------------------------------------
# Part 1: population PFG moment dynamics.
# ---------------------------------------------------------------------------------------------

#: Ill-conditioned target covariance: eigenvalue 100 along (1, 1), eigenvalue 1 along (1, -1).
SIGMA_STAR: Mat = [[Fraction(101, 2), Fraction(99, 2)], [Fraction(99, 2), Fraction(101, 2)]]


def pfg_velocity(x: Vec, m: Vec, S: Mat, A: Mat, S_star: Mat) -> Vec:
    """``A (grad log p_*(x) - grad log p(x)) = A (-S*^{-1} x + S^{-1} (x - m))``."""
    delta = [xi - mi for xi, mi in zip(x, m)]
    target_score = [-c for c in mv(inv2(S_star), x)]
    current_score = [-c for c in mv(inv2(S), delta)]
    return mv(A, [a - b for a, b in zip(target_score, current_score)])


def pfg_moment_derivatives(m: Vec, S: Mat, A: Mat, S_star: Mat) -> tuple[Vec, Mat]:
    """``m' = -A S*^{-1} m`` and ``S' = A G S + S G A`` with ``G = S^{-1} - S*^{-1}``."""
    G = msub(inv2(S), inv2(S_star))
    dm = [-c for c in mv(mm(A, inv2(S_star)), m)]
    dS = madd(mm(mm(A, G), S), mm(mm(S, G), A))
    return dm, dS


def langevin_moment_derivatives(m: Vec, S: Mat, A: Mat, S_star: Mat) -> tuple[Vec, Mat]:
    """Moment ODE of ``dX = -M X dt + sqrt(2A) dW``, ``M = A S*^{-1}``.

    ``m' = -M m`` and ``S' = 2A - M S - S M^T`` (Lyapunov equation).
    """
    M = mm(A, inv2(S_star))
    dm = [-c for c in mv(M, m)]
    dS = msub(msub(mscale(2, A), mm(M, S)), mm(S, transpose(M)))
    return dm, dS


def log_density_time_derivative(x: Vec, m: Vec, S: Mat, dm: Vec, dS: Mat):
    """``d/dt log N(x; m_t, S_t)`` given ``(m', S')`` (rational in all inputs):

    ``-(1/2) tr(S^{-1} S') + delta^T S^{-1} m' + (1/2) delta^T S^{-1} S' S^{-1} delta``.
    """
    Sinv = inv2(S)
    delta = [xi - mi for xi, mi in zip(x, m)]
    w = mv(Sinv, delta)
    return -trace(mm(Sinv, dS)) / 2 + dot(w, dm) + dot(w, mv(dS, w)) / 2


def continuity_rhs_over_density(x: Vec, m: Vec, S: Mat, A: Mat, S_star: Mat):
    """``-div(p v)(x) / p(x) = (S^{-1}(x - m)) . v(x) - tr(A G)`` for Gaussian ``p``."""
    G = msub(inv2(S), inv2(S_star))
    delta = [xi - mi for xi, mi in zip(x, m)]
    v = mv(A, [a - b for a, b in zip(mv(G, x), mv(inv2(S), m))])
    return dot(mv(inv2(S), delta), v) - trace(mm(A, G))


def kl_gaussian(m: Vec, S: Mat, S_star: Mat) -> float:
    """``KL(N(m, S) || N(0, S*))`` in nats."""
    Ssinv = inv2(S_star)
    quad = trace(mm(Ssinv, S)) + dot(m, mv(Ssinv, m)) - 2
    return 0.5 * (float(quad) + math.log(float(det2(S_star))) - math.log(float(det2(S))))


def kl_time_derivative(m: Vec, S: Mat, dm: Vec, dS: Mat, S_star: Mat):
    """``d/dt KL = m^T S*^{-1} m' + (1/2) tr((S*^{-1} - S^{-1}) S')`` (no logarithms: rational)."""
    Ssinv = inv2(S_star)
    return dot(m, mv(Ssinv, dm)) + trace(mm(msub(Ssinv, inv2(S)), dS)) / 2


def kl_dissipation(m: Vec, S: Mat, A: Mat, S_star: Mat):
    """``E_p[g^T A g]`` for ``g = grad log(p / p_*) = -G x + S^{-1} m``:
    ``tr(A G S G) + (S*^{-1} m)^T A (S*^{-1} m)``."""
    G = msub(inv2(S), inv2(S_star))
    mean_g = mv(inv2(S_star), m)
    return trace(mm(mm(mm(A, G), S), G)) + dot(mean_g, mv(A, mean_g))


def closed_form_moments(
    t: float, m0: Vec, S0: Mat, A: Mat, S_star: Mat
) -> tuple[list[float], list[list[float]]]:
    """``m_t = e^{-tM} m0``, ``S_t = S* + e^{-tM} (S0 - S*) e^{-tM^T}``, ``M = A S*^{-1}``."""
    M = to_float(mm(A, inv2(S_star)))
    E = expm2(mscale(-t, M))
    Sf, S0f = to_float(S_star), to_float(S0)
    m_t = mv(E, [float(c) for c in m0])
    S_t = madd(Sf, mm(mm(E, msub(S0f, Sf)), transpose(E)))
    return m_t, S_t


def rk4_moments(
    m0: Vec, S0: Mat, A: Mat, S_star: Mat, t_end: float, steps: int
) -> list[tuple[float, list[float], list[list[float]]]]:
    """RK4 for the PFG moment ODE in floats; returns ``(t, m, S)`` at every step."""
    Af, Sf = to_float(A), to_float(S_star)
    m, S = [float(c) for c in m0], to_float(S0)
    h = t_end / steps
    path = [(0.0, m, S)]

    def f(mm_: list[float], SS: list[list[float]]):
        return pfg_moment_derivatives(mm_, SS, Af, Sf)

    for k in range(steps):
        k1 = f(m, S)
        k2 = f([a + h / 2 * b for a, b in zip(m, k1[0])], madd(S, mscale(h / 2, k1[1])))
        k3 = f([a + h / 2 * b for a, b in zip(m, k2[0])], madd(S, mscale(h / 2, k2[1])))
        k4 = f([a + h * b for a, b in zip(m, k3[0])], madd(S, mscale(h, k3[1])))
        m = [
            a + h / 6 * (b1 + 2 * b2 + 2 * b3 + b4)
            for a, b1, b2, b3, b4 in zip(m, k1[0], k2[0], k3[0], k4[0])
        ]
        dS = madd(madd(k1[1], mscale(2.0, k2[1])), madd(mscale(2.0, k3[1]), k4[1]))
        S = madd(S, mscale(h / 6, dS))
        path.append(((k + 1) * h, m, S))
    return path


def time_to_kl(
    threshold: float, m0: Vec, S0: Mat, A: Mat, S_star: Mat, t_max: float = 1e4
) -> float:
    """Smallest ``t`` with ``KL(p_t || p_*) <= threshold`` (bisection; KL is non-increasing)."""

    def kl_at(t: float) -> float:
        m, S = closed_form_moments(t, m0, S0, A, S_star)
        return kl_gaussian(m, S, to_float(S_star))

    lo, hi = 0.0, t_max
    if kl_at(hi) > threshold:
        return math.inf
    for _ in range(80):
        mid = (lo + hi) / 2
        if kl_at(mid) <= threshold:
            hi = mid
        else:
            lo = mid
    return hi


# ---------------------------------------------------------------------------------------------
# Part 2: finite-feature SVGD and PFG's weighted norm in 1D, psi(x) = (1, x).
# ---------------------------------------------------------------------------------------------

#: Double-well target ``p_*(x) ~ exp(x^2/2 - x^4/4)`` with polynomial score ``x - x^3``.
SCORE_COEFFS: tuple[Fraction, ...] = (Fraction(0), Fraction(1), Fraction(0), Fraction(-1))
PARTICLES: tuple[Fraction, ...] = (
    Fraction(-3, 2),
    Fraction(-1, 3),
    Fraction(1, 4),
    Fraction(1),
    Fraction(2),
)
LAMBDA = Fraction(1, 2)


def poly_eval(coeffs: Sequence[Fraction], x: Fraction) -> Fraction:
    return sum((c * x**j for j, c in enumerate(coeffs)), Fraction(0))


def psi(x: Fraction) -> list[Fraction]:
    return [Fraction(1), x]


def dpsi(x: Fraction) -> list[Fraction]:
    return [Fraction(0), Fraction(1)]


def kernel(x: Fraction, y: Fraction) -> Fraction:
    """``k(x, y) = psi(x) . psi(y) = 1 + x y``."""
    return dot(psi(x), psi(y))


def kernel_dy(y: Fraction, x: Fraction) -> Fraction:
    """``d/dy k(y, x) = psi'(y) . psi(x)``."""
    return dot(dpsi(y), psi(x))


def svgd_direction(
    particles: Sequence[Fraction], score: Callable[[Fraction], Fraction], lam: Fraction, x
) -> Fraction:
    """``(1/(lambda n)) sum_j [k(y_j, x) s(y_j) + d/dy k(y, x)|_{y_j}]``."""
    n = len(particles)
    total = sum((kernel(y, x) * score(y) + kernel_dy(y, x) for y in particles), Fraction(0))
    return total / (lam * n)


def stein_term(W: Vec, particles: Sequence[Fraction], score) -> Fraction:
    """``(1/n) sum_j [f_W'(y_j) + f_W(y_j) s(y_j)]``."""
    n = len(particles)
    return sum((dot(W, dpsi(y)) + dot(W, psi(y)) * score(y) for y in particles), Fraction(0)) / n


def svgd_objective(W: Vec, particles, score, lam: Fraction) -> Fraction:
    """Stein objective with the fixed feature (RKHS) norm ``(lambda/2) |W|^2``."""
    return -stein_term(W, particles, score) + lam * dot(W, W) / 2


def svgd_weights(particles, score, lam: Fraction) -> Vec:
    """``W* = (1/(lambda n)) sum_j [s(y_j) psi(y_j) + psi'(y_j)]`` (stationarity of ``L``)."""
    n = len(particles)
    return [
        sum((score(y) * psi(y)[i] + dpsi(y)[i] for y in particles), Fraction(0)) / (lam * n)
        for i in range(2)
    ]


def empirical_gram(particles) -> Mat:
    n = len(particles)
    return [
        [sum((psi(y)[i] * psi(y)[j] for y in particles), Fraction(0)) / n for j in range(2)]
        for i in range(2)
    ]


def pfg_feature_objective(W: Vec, particles, score) -> Fraction:
    """Stein objective with PFG's weighted output norm ``(1/2) (1/n) sum_j f_W(y_j)^2``."""
    n = len(particles)
    weighted = sum((dot(W, psi(y)) ** 2 for y in particles), Fraction(0)) / n
    return -stein_term(W, particles, score) + weighted / 2


def pfg_feature_weights(particles, score) -> Vec:
    """Minimiser of the weighted objective: ``W G = b`` with Gram ``G`` and Stein vector ``b``."""
    n = len(particles)
    b = [
        sum((dpsi(y)[i] + score(y) * psi(y)[i] for y in particles), Fraction(0)) / n
        for i in range(2)
    ]
    return mv(transpose(inv2(empirical_gram(particles))), b)


def gaussian_pfg_projection(
    score_coeffs: Sequence[Fraction], mean: Fraction, var: Fraction
) -> tuple[Vec, list[Fraction]]:
    """Population PFG weights for ``p = N(mean, var)`` and the projection residual.

    ``W`` solves ``W G = b`` with ``G = E_p[psi psi^T]`` and ``b = E_p[psi' + s psi]`` (Stein
    form, no density of ``p`` needed). The residual is ``E_p[(v*(X) - W . psi(X)) psi(X)]`` for
    ``v* = s - grad log p = s(x) + (x - mean)/var``; it vanishes iff ``W . psi`` is the
    ``L^2(p)`` projection of ``v*``, which holds by the Gaussian Stein identity
    ``E[psi'(X)] = E[psi(X) (X - mean) / var]``.
    """

    def moment(n: int) -> Fraction:
        return gaussian_moment(n, mean, var)

    s = list(score_coeffs)
    x_s = [Fraction(0)] + s  # x * s(x)
    G = [[Fraction(1), mean], [mean, moment(2)]]
    b = [poly_expectation(s, moment), 1 + poly_expectation(x_s, moment)]
    W = mv(transpose(inv2(G)), b)
    v_star = list(s) + [Fraction(0)] * max(0, 2 - len(s))
    v_star[0] -= mean / var
    v_star[1] += 1 / var
    resid_poly = [c for c in v_star]
    resid_poly[0] -= W[0]
    resid_poly[1] -= W[1]
    residual = [
        poly_expectation(resid_poly, moment),
        poly_expectation([Fraction(0)] + resid_poly, moment),
    ]
    return W, residual


# ---------------------------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------------------------


def run_checks(seed: int = SEED) -> list[Check]:
    rng = random.Random(seed)
    checks: list[Check] = []

    forms_ok = continuity_ok = dissipation_ok = velocity_ok = True
    for _ in range(40):
        m, S, A, S_star = random_vec(rng), random_spd(rng), random_spd(rng), random_spd(rng)
        dm, dS = pfg_moment_derivatives(m, S, A, S_star)
        forms_ok &= (dm, dS) == langevin_moment_derivatives(m, S, A, S_star)
        x = random_vec(rng)
        continuity_ok &= log_density_time_derivative(
            x, m, S, dm, dS
        ) == continuity_rhs_over_density(x, m, S, A, S_star)
        diss = kl_dissipation(m, S, A, S_star)
        dissipation_ok &= kl_time_derivative(m, S, dm, dS, S_star) == -diss and diss >= 0
        v = pfg_velocity(x, m, S, A, S_star)
        G = msub(inv2(S), inv2(S_star))
        velocity_ok &= v == mv(A, [a - b for a, b in zip(mv(G, x), mv(inv2(S), m))])
    checks.append(
        Check(
            "PFG moment ODE A G S + S G A equals the Langevin Lyapunov form 2A - MS - SM^T",
            forms_ok and velocity_ok,
            "40 random rational (m, S, A, S*)",
        )
    )
    checks.append(
        Check(
            "Gaussian p_t with these moments solves d/dt log p = -div(p v)/p (exact)",
            continuity_ok,
            "40 random rational points",
        )
    )
    checks.append(
        Check(
            "FL-2 Gaussian case: d/dt KL = -E_p[g^T A g] <= 0, g = grad log(p/p*) (exact)",
            dissipation_ok,
            "40 random rational (m, S, A, S*)",
        )
    )

    one = Fraction(1)
    A_id, A_pre = identity2(one), [row[:] for row in SIGMA_STAR]
    M_id, M_pre = mm(A_id, inv2(SIGMA_STAR)), mm(A_pre, inv2(SIGMA_STAR))
    # Eigenvalues of M_id from its characteristic polynomial: trace 101/100 and det 1/100.
    rates_ok = (
        M_pre == identity2(one)
        and trace(M_id) == Fraction(101, 100)
        and det2(M_id) == Fraction(1, 100)
    )
    checks.append(
        Check(
            "Rates: M = A S*^{-1} has spectrum {1/100, 1} for A = I and {1, 1} for A = S*",
            rates_ok,
            "condition number 100 vs 1; both have lambda_max = 1",
        )
    )

    m0, S0 = [Fraction(4), Fraction(1)], identity2(one)
    rk_err = 0.0
    for A in (A_id, A_pre):
        for t, m, S in rk4_moments(m0, S0, A, SIGMA_STAR, 5.0, 1000)[::100]:
            mc, Sc = closed_form_moments(t, m0, S0, A, SIGMA_STAR)
            rk_err = max(rk_err, max(abs(a - b) for a, b in zip(m, mc)))
            rk_err = max(rk_err, max(abs(a - b) for ra, rb in zip(S, Sc) for a, b in zip(ra, rb)))
    checks.append(
        Check(
            "RK4 on the PFG moment ODE matches e^{-tM} m0 and S* + e^{-tM}(S0 - S*)e^{-tM'}",
            rk_err < 1e-8,
            f"max abs error {rk_err:.1e} on [0, 5]",
        )
    )

    S_star_f = to_float(SIGMA_STAR)
    monotone = True
    for A in (A_id, A_pre):
        kls = [
            kl_gaussian(m, S, S_star_f) for _, m, S in rk4_moments(m0, S0, A, SIGMA_STAR, 5.0, 500)
        ]
        monotone &= all(b <= a + 1e-12 for a, b in zip(kls, kls[1:]))
    times = (1.0, 2.0, 5.0, 10.0, 50.0)
    kl_id = [
        kl_gaussian(*closed_form_moments(t, m0, S0, A_id, SIGMA_STAR), S_star_f) for t in times
    ]
    kl_pre = [
        kl_gaussian(*closed_form_moments(t, m0, S0, A_pre, SIGMA_STAR), S_star_f) for t in times
    ]
    t_id = time_to_kl(1e-3, m0, S0, A_id, SIGMA_STAR)
    t_pre = time_to_kl(1e-3, m0, S0, A_pre, SIGMA_STAR)
    checks.append(
        Check(
            "KL decay: preconditioning A = S* removes the ill-conditioning of A = I",
            monotone and all(b < a for a, b in zip(kl_id, kl_pre)) and t_id > 20 * t_pre,
            f"KL0={kl_gaussian(m0, S0, SIGMA_STAR):.3f}; KL at t={times}: "
            + f"A=I {[f'{v:.2e}' for v in kl_id]}, A=S* {[f'{v:.2e}' for v in kl_pre]}; "
            + f"time to KL<=1e-3: A=I {t_id:.1f}, A=S* {t_pre:.2f}",
        )
    )

    def score(y: Fraction) -> Fraction:
        return poly_eval(SCORE_COEFFS, y)

    W_svgd = svgd_weights(PARTICLES, score, LAMBDA)
    xs = (Fraction(-2), Fraction(-1, 2), Fraction(0), Fraction(3, 7), Fraction(5, 3))
    direction_ok = all(
        svgd_direction(PARTICLES, score, LAMBDA, x) == dot(W_svgd, psi(x)) for x in xs
    )
    checks.append(
        Check(
            "SE-2 kernelised Stein direction equals W* psi(x) (exact)",
            direction_ok,
            f"W* = ({W_svgd[0]}, {W_svgd[1]}) on {len(PARTICLES)} particles, lambda = {LAMBDA}",
        )
    )

    rng2 = random.Random(seed + 2)
    W_pfg = pfg_feature_weights(PARTICLES, score)
    gram = empirical_gram(PARTICLES)
    squares_ok = True
    for _ in range(20):
        delta = random_vec(rng2)
        Wd = [a + b for a, b in zip(W_svgd, delta)]
        gap = svgd_objective(Wd, PARTICLES, score, LAMBDA) - svgd_objective(
            W_svgd, PARTICLES, score, LAMBDA
        )
        squares_ok &= gap == LAMBDA * dot(delta, delta) / 2
        Wp = [a + b for a, b in zip(W_pfg, delta)]
        gap_pfg = pfg_feature_objective(Wp, PARTICLES, score) - pfg_feature_objective(
            W_pfg, PARTICLES, score
        )
        squares_ok &= gap_pfg == dot(delta, mv(gram, delta)) / 2
    checks.append(
        Check(
            "Completion of squares: L(W* + D) - L(W*) = (lambda/2)|D|^2 (SVGD), D^T G D / 2 (PFG)",
            squares_ok,
            "20 random rational D",
        )
    )

    cross = W_svgd[0] * W_pfg[1] - W_svgd[1] * W_pfg[0]
    checks.append(
        Check(
            "Fixed RKHS norm (SVGD) and PFG's weighted norm give non-parallel directions",
            cross != 0,
            f"W_svgd = ({W_svgd[0]}, {W_svgd[1]}), W_pfg = ({W_pfg[0]}, {W_pfg[1]})",
        )
    )

    projection_ok = True
    exact_ok = True
    for _ in range(15):
        mean = Fraction(rng2.randint(-6, 6), rng2.randint(1, 4))
        var = Fraction(rng2.randint(1, 9), rng2.randint(1, 4))
        _, residual = gaussian_pfg_projection(SCORE_COEFFS, mean, var)
        projection_ok &= residual == [0, 0]
        W, residual = gaussian_pfg_projection((Fraction(0), Fraction(-1)), mean, var)
        exact_ok &= residual == [0, 0] and W == [-mean / var, -1 + 1 / var]
    checks.append(
        Check(
            "PFG weighted norm, p = N(m, v): W psi is the L2(p) projection of s - grad log p",
            projection_ok and exact_ok,
            "double-well s: zero residual; N(0,1) target: W psi = v* exactly (15 random (m, v))",
        )
    )
    return checks


def main() -> int:
    return print_report(
        "pfg_gaussian_flow: PFG moments, KL decay, finite-feature SVGD", run_checks()
    )


if __name__ == "__main__":
    raise SystemExit(main())
