"""Tweedie's identity for one-dimensional Gaussian mixtures and atomic priors.

Setting (SE-3). ``X ~ prior``, ``Z ~ N(0, 1)`` independent, ``Y = X + sigma Z``.
For the mixture prior ``sum_k w_k N(m_k, s_k^2)`` the law of ``Y`` has the closed-form density
``p_sigma(y) = sum_k w_k N(y; m_k, s_k^2 + sigma^2)``. Tweedie's identity reads

    d/dy log p_sigma(y) = (E[X | Y = y] - y) / sigma^2 = -E[Z | Y = y] / sigma.

Checks in this module:

* the closed-form convolution against Simpson quadrature of ``int prior(x) N(y; x, sigma^2) dx``;
* the score by five-point central finite differences of ``log p_sigma`` against the
  closed-form posterior mean (conjugate per-component update) and the posterior noise mean
  (per-component regression of ``Z`` on ``Y``), and the posterior mean against quadrature of
  Bayes' formula;
* a purely atomic prior ``sum_k w_k delta_{a_k}``: Tweedie still holds although ``X`` has no
  Lebesgue density (only ``Y`` needs one);
* ID-2: ``E[score(Y)] = 0`` by quadrature;
* SE-3 (OU posterior score, rdMC Lemma 1) as an affine corollary: for
  ``X_t = e^{-t} X_0 + sqrt(1 - e^{-2t}) Z`` the score is ``(a_t E[X_0 | X_t = y] - y)/sigma_t^2``;
* CE-02: ``Var(Z | Y = y) > 0``, so the noise ``Z`` is not a function of ``Y``; only its
  conditional mean is the (rescaled) score.

Floating-point illustrations with stated tolerances; never proofs.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence
from dataclasses import dataclass

from experiments._common import Check, print_report

SQRT_2PI = math.sqrt(2.0 * math.pi)


@dataclass(frozen=True)
class Mixture1D:
    """``sum_k weights[k] N(means[k], variances[k])``; a zero variance is an atom."""

    weights: tuple[float, ...]
    means: tuple[float, ...]
    variances: tuple[float, ...]

    def __post_init__(self) -> None:
        if not len(self.weights) == len(self.means) == len(self.variances):
            raise ValueError("weights, means and variances must have equal length")
        if any(w <= 0 for w in self.weights) or abs(sum(self.weights) - 1.0) > 1e-12:
            raise ValueError("weights must be positive and sum to 1")
        if any(s2 < 0 for s2 in self.variances):
            raise ValueError("variances must be non-negative")

    @property
    def is_atomic(self) -> bool:
        return all(s2 == 0 for s2 in self.variances)

    def prior_density(self, x: float) -> float:
        """Lebesgue density of the prior; only defined when every component has a density."""
        if any(s2 == 0 for s2 in self.variances):
            raise ValueError("a prior with atoms has no Lebesgue density")
        return sum(
            w * normal_pdf(x, m, s2)
            for w, m, s2 in zip(self.weights, self.means, self.variances, strict=True)
        )


EXAMPLE_MIXTURE = Mixture1D(
    weights=(0.3, 0.5, 0.2), means=(-2.0, 0.5, 3.0), variances=(0.25, 1.0, 0.04)
)
EXAMPLE_ATOMS = Mixture1D(
    weights=(0.2, 0.5, 0.3), means=(-1.5, 0.0, 2.0), variances=(0.0, 0.0, 0.0)
)
SIGMAS = (0.3, 1.0, 2.0)
Y_GRID = (-4.0, -2.5, -1.0, 0.0, 0.3, 1.7, 3.0, 5.0)


def normal_pdf(x: float, mean: float, var: float) -> float:
    """Density of ``N(mean, var)`` (``var`` is the variance, not the standard deviation)."""
    return math.exp(-((x - mean) ** 2) / (2.0 * var)) / (SQRT_2PI * math.sqrt(var))


def normal_logpdf(x: float, mean: float, var: float) -> float:
    return -((x - mean) ** 2) / (2.0 * var) - 0.5 * math.log(2.0 * math.pi * var)


def _logsumexp(values: Sequence[float]) -> float:
    top = max(values)
    return top + math.log(sum(math.exp(v - top) for v in values))


def _component_logs(prior: Mixture1D, sigma: float, y: float) -> list[float]:
    return [
        math.log(w) + normal_logpdf(y, m, s2 + sigma**2)
        for w, m, s2 in zip(prior.weights, prior.means, prior.variances, strict=True)
    ]


def smoothed_log_density(prior: Mixture1D, sigma: float, y: float) -> float:
    """``log p_sigma(y)`` with ``p_sigma = sum_k w_k N(m_k, s_k^2 + sigma^2)``."""
    return _logsumexp(_component_logs(prior, sigma, y))


def smoothed_density(prior: Mixture1D, sigma: float, y: float) -> float:
    return math.exp(smoothed_log_density(prior, sigma, y))


def responsibilities(prior: Mixture1D, sigma: float, y: float) -> list[float]:
    """Posterior component probabilities ``P(k | Y = y)``."""
    logs = _component_logs(prior, sigma, y)
    norm = _logsumexp(logs)
    return [math.exp(v - norm) for v in logs]


def posterior_mean_x(prior: Mixture1D, sigma: float, y: float) -> float:
    """``E[X | Y = y]`` by the conjugate update ``m_k + s_k^2/(s_k^2 + sigma^2) (y - m_k)``."""
    r = responsibilities(prior, sigma, y)
    return sum(
        rk * (m + s2 / (s2 + sigma**2) * (y - m))
        for rk, m, s2 in zip(r, prior.means, prior.variances, strict=True)
    )


def posterior_mean_z(prior: Mixture1D, sigma: float, y: float) -> float:
    """``E[Z | Y = y]`` by per-component regression: ``sigma (y - m_k) / (s_k^2 + sigma^2)``.

    Within component ``k``, ``(Z, Y)`` is Gaussian with ``Cov(Z, Y) = sigma`` and
    ``Var Y = s_k^2 + sigma^2``.
    """
    r = responsibilities(prior, sigma, y)
    return sum(
        rk * sigma * (y - m) / (s2 + sigma**2)
        for rk, m, s2 in zip(r, prior.means, prior.variances, strict=True)
    )


def posterior_var_z(prior: Mixture1D, sigma: float, y: float) -> float:
    """``Var(Z | Y = y)``; per component ``Var(Z | Y, k) = s_k^2 / (s_k^2 + sigma^2)``."""
    r = responsibilities(prior, sigma, y)
    second = sum(
        rk * (s2 / (s2 + sigma**2) + (sigma * (y - m) / (s2 + sigma**2)) ** 2)
        for rk, m, s2 in zip(r, prior.means, prior.variances, strict=True)
    )
    return second - posterior_mean_z(prior, sigma, y) ** 2


def closed_form_score(prior: Mixture1D, sigma: float, y: float) -> float:
    """Analytic derivative of ``log p_sigma``: ``sum_k r_k(y) (m_k - y)/(s_k^2 + sigma^2)``."""
    r = responsibilities(prior, sigma, y)
    return sum(
        rk * (m - y) / (s2 + sigma**2)
        for rk, m, s2 in zip(r, prior.means, prior.variances, strict=True)
    )


def finite_difference(f: Callable[[float], float], y: float, eta: float = 1e-3) -> float:
    """Five-point central difference for ``f'(y)``, truncation error ``O(eta^4)``."""
    return (f(y - 2 * eta) - 8 * f(y - eta) + 8 * f(y + eta) - f(y + 2 * eta)) / (12.0 * eta)


def fd_score(prior: Mixture1D, sigma: float, y: float) -> float:
    """``d/dy log p_sigma(y)`` by finite differences of the closed-form log-density."""
    return finite_difference(lambda u: smoothed_log_density(prior, sigma, u), y)


def simpson(f: Callable[[float], float], lo: float, hi: float, n: int = 4000) -> float:
    """Composite Simpson rule with ``n`` (even) sub-intervals."""
    if n % 2:
        n += 1
    step = (hi - lo) / n
    total = f(lo) + f(hi)
    total += 4.0 * sum(f(lo + (2 * i - 1) * step) for i in range(1, n // 2 + 1))
    total += 2.0 * sum(f(lo + 2 * i * step) for i in range(1, n // 2))
    return total * step / 3.0


def _prior_range(prior: Mixture1D, half_width: float = 12.0) -> tuple[float, float]:
    lo = min(m - half_width * math.sqrt(s2) for m, s2 in zip(prior.means, prior.variances))
    hi = max(m + half_width * math.sqrt(s2) for m, s2 in zip(prior.means, prior.variances))
    return lo, hi


def quadrature_density(prior: Mixture1D, sigma: float, y: float) -> float:
    """``int prior(x) N(y; x, sigma^2) dx`` by Simpson's rule (independent of the closed form)."""
    lo, hi = _prior_range(prior)
    return simpson(lambda x: prior.prior_density(x) * normal_pdf(y, x, sigma**2), lo, hi)


def quadrature_posterior_mean(prior: Mixture1D, sigma: float, y: float) -> float:
    """``E[X | Y = y]`` by quadrature of Bayes' formula (independent of the conjugate update)."""
    lo, hi = _prior_range(prior)
    num = simpson(lambda x: x * prior.prior_density(x) * normal_pdf(y, x, sigma**2), lo, hi)
    den = simpson(lambda x: prior.prior_density(x) * normal_pdf(y, x, sigma**2), lo, hi)
    return num / den


def atomic_posterior_mean(prior: Mixture1D, sigma: float, y: float) -> float:
    """Bayes' formula for an atomic prior: ``sum_k w_k a_k phi_sigma(y - a_k) / sum_k ...``."""
    num = sum(w * a * normal_pdf(y, a, sigma**2) for w, a in zip(prior.weights, prior.means))
    den = sum(w * normal_pdf(y, a, sigma**2) for w, a in zip(prior.weights, prior.means))
    return num / den


def tweedie_errors(prior: Mixture1D, sigma: float, ys: Sequence[float]) -> dict[str, float]:
    """Max absolute discrepancies of the three forms of Tweedie's identity over ``ys``."""
    mean_form = noise_form = analytic = 0.0
    for y in ys:
        fd = fd_score(prior, sigma, y)
        mean_form = max(mean_form, abs(fd - (posterior_mean_x(prior, sigma, y) - y) / sigma**2))
        noise_form = max(noise_form, abs(fd + posterior_mean_z(prior, sigma, y) / sigma))
        analytic = max(analytic, abs(fd - closed_form_score(prior, sigma, y)))
    return {"mean_form": mean_form, "noise_form": noise_form, "analytic": analytic}


def mean_score_quadrature(prior: Mixture1D, sigma: float) -> float:
    """``E[score(Y)] = int p_sigma'(y) dy`` by Simpson's rule (should vanish, ID-2)."""
    lo, hi = _prior_range(prior)
    lo, hi = lo - 12.0 * sigma, hi + 12.0 * sigma
    return simpson(
        lambda y: smoothed_density(prior, sigma, y) * closed_form_score(prior, sigma, y), lo, hi
    )


# ---------------------------------------------------------------------------------------------
# OU posterior score (SE-3) as an affine corollary of Tweedie.
# ---------------------------------------------------------------------------------------------


def ou_coefficients(t: float) -> tuple[float, float]:
    """``(a_t, sigma_t^2) = (e^{-t}, 1 - e^{-2t})`` for the unit OU process."""
    return math.exp(-t), -math.expm1(-2.0 * t)


def ou_marginal(prior: Mixture1D, t: float) -> Mixture1D:
    """Law of ``X_t = a_t X_0 + sigma_t Z``: ``sum_k w_k N(a_t m_k, a_t^2 s_k^2 + sigma_t^2)``."""
    a_t, s2_t = ou_coefficients(t)
    return Mixture1D(
        prior.weights,
        tuple(a_t * m for m in prior.means),
        tuple(a_t**2 * s2 + s2_t for s2 in prior.variances),
    )


def ou_log_density(prior: Mixture1D, t: float, y: float) -> float:
    marginal = ou_marginal(prior, t)
    return _logsumexp(
        [
            math.log(w) + normal_logpdf(y, m, s2)
            for w, m, s2 in zip(marginal.weights, marginal.means, marginal.variances)
        ]
    )


def ou_posterior_mean_x0(prior: Mixture1D, t: float, y: float) -> float:
    """``E[X_0 | X_t = y]`` via the rescaling ``X_t = a_t (X_0 + (sigma_t / a_t) Z)``."""
    a_t, s2_t = ou_coefficients(t)
    return posterior_mean_x(prior, math.sqrt(s2_t) / a_t, y / a_t)


def ou_score_errors(prior: Mixture1D, times: Sequence[float], ys: Sequence[float]) -> float:
    """Max ``|fd score - (a_t E[X_0 | X_t = y] - y) / sigma_t^2|`` over ``times x ys``."""
    worst = 0.0
    for t in times:
        a_t, s2_t = ou_coefficients(t)
        for y in ys:
            fd = finite_difference(lambda u: ou_log_density(prior, t, u), y)
            worst = max(worst, abs(fd - (a_t * ou_posterior_mean_x0(prior, t, y) - y) / s2_t))
    return worst


# ---------------------------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------------------------

FD_TOL = 1e-6
QUAD_TOL = 1e-9


def run_checks() -> list[Check]:
    checks: list[Check] = []
    prior = EXAMPLE_MIXTURE

    conv = max(
        abs(quadrature_density(prior, s, y) - smoothed_density(prior, s, y))
        for s in SIGMAS
        for y in Y_GRID
    )
    checks.append(
        Check(
            "Closed form p_sigma = sum_k w_k N(m_k, s_k^2 + sigma^2) matches quadrature",
            conv < QUAD_TOL,
            f"max abs error {conv:.1e}",
        )
    )

    post = max(
        abs(quadrature_posterior_mean(prior, s, y) - posterior_mean_x(prior, s, y))
        for s in SIGMAS
        for y in Y_GRID
    )
    checks.append(
        Check(
            "Conjugate posterior mean E[X|Y=y] matches quadrature of Bayes' formula",
            post < QUAD_TOL,
            f"max abs error {post:.1e}",
        )
    )

    for name, p in (("mixture", prior), ("atomic", EXAMPLE_ATOMS)):
        errs = [tweedie_errors(p, s, Y_GRID) for s in SIGMAS]
        worst_mean = max(e["mean_form"] for e in errs)
        worst_noise = max(e["noise_form"] for e in errs)
        checks.append(
            Check(
                f"SE-3 Tweedie ({name} prior): FD score = (E[X|y] - y)/sigma^2 = -E[Z|y]/sigma",
                worst_mean < FD_TOL and worst_noise < FD_TOL,
                f"max errors {worst_mean:.1e} (mean form), {worst_noise:.1e} (noise form)",
            )
        )

    atomic_bayes = max(
        abs(atomic_posterior_mean(EXAMPLE_ATOMS, s, y) - posterior_mean_x(EXAMPLE_ATOMS, s, y))
        for s in SIGMAS
        for y in Y_GRID
    )
    checks.append(
        Check(
            "Atomic prior (no Lebesgue density for X): posterior mean equals discrete Bayes",
            atomic_bayes < 1e-12,
            f"max abs error {atomic_bayes:.1e}",
        )
    )

    zero_mean = max(abs(mean_score_quadrature(p, s)) for p in (prior,) for s in SIGMAS)
    checks.append(
        Check(
            "ID-2 E[score(Y)] = int p_sigma'(y) dy = 0 (quadrature)",
            zero_mean < QUAD_TOL,
            f"max |E score| {zero_mean:.1e}",
        )
    )

    ou_err = max(ou_score_errors(p, (0.1, 0.5, 2.0), Y_GRID) for p in (prior, EXAMPLE_ATOMS))
    checks.append(
        Check(
            "SE-3 OU posterior score (a_t E[X_0|X_t=y] - y)/sigma_t^2 via rescaled Tweedie",
            ou_err < FD_TOL,
            f"max error {ou_err:.1e} at t in (0.1, 0.5, 2.0)",
        )
    )

    min_var = min(posterior_var_z(prior, s, y) for s in SIGMAS for y in Y_GRID)
    gauss = Mixture1D((1.0,), (0.0,), (2.0,))
    gauss_var = posterior_var_z(gauss, 1.0, 0.7)
    checks.append(
        Check(
            "CE-02 Var(Z | Y = y) > 0: noise is not a function of Y (Gaussian: s^2/(s^2+sigma^2))",
            min_var > 0 and abs(gauss_var - 2.0 / 3.0) < 1e-12,
            f"min over grid {min_var:.3f}; N(0,2) prior, sigma=1: {gauss_var:.6f} vs 2/3",
        )
    )
    return checks


def main() -> int:
    return print_report("gaussian_mixtures: Tweedie, OU posterior score", run_checks())


if __name__ == "__main__":
    raise SystemExit(main())
