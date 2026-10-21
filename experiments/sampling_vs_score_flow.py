"""Same one-time marginals, different processes: OU sampling versus the deterministic PFG flow.

Both processes start from the *same* samples ``X_0 ~ N(m0, v0)`` and target ``N(0, 1)``:

* OU (``dX = -a X dt + sqrt(2 a) dW``), simulated with exact Mehler transitions
  ``X_{t + dt} = e^{-a dt} X_t + sqrt(1 - e^{-2 a dt}) xi``;
* the probability-flow / PFG ODE ``y' = a (-y + (y - m_t) / v_t)`` with ``A = a``, applied through
  its exact flow map ``y0 -> m_t + sqrt(v_t / v0) (y0 - m0)`` (an increasing affine map).

Both have the one-time marginal ``N(m_t, v_t)`` with ``m_t = e^{-a t} m0`` and
``v_t = 1 + (v0 - 1) e^{-2 a t}`` (EX-1 and FL-5 in this Gaussian case), so sample means and
variances agree up to Monte Carlo error. The two-time laws differ (CE-01):

    corr(X_0, X_t) = e^{-a t} sqrt(v0 / v_t) < 1    for OU and t > 0,
    corr(Y_0, Y_t) = 1                               for the deterministic increasing flow.

Indeed ``sqrt(v0 v_t) - e^{-a t} v0 > 0`` because ``v_t - e^{-2 a t} v0 = 1 - e^{-2 a t} > 0``.
Monte Carlo illustrations with a fixed seed and stated tolerances; never proofs.
"""

from __future__ import annotations

import math
import random
import statistics
from collections.abc import Sequence
from dataclasses import dataclass

from experiments._common import Check, print_report

TIMES = (0.25, 0.5, 1.0, 2.0)
N_SAMPLES = 20000
SEED = 20251013
N_SE = 5.0  # tolerance in (approximate) standard errors


def ou_moments(t: float, a: float, m0: float, v0: float) -> tuple[float, float]:
    """``(m_t, v_t) = (e^{-a t} m0, 1 + (v0 - 1) e^{-2 a t})``."""
    decay = math.exp(-a * t)
    return decay * m0, 1.0 + (v0 - 1.0) * decay * decay


def ou_correlation(t: float, a: float, m0: float, v0: float) -> float:
    """``corr(X_0, X_t) = e^{-a t} sqrt(v0 / v_t)`` for the OU process started at ``N(m0, v0)``."""
    _, v_t = ou_moments(t, a, m0, v0)
    return math.exp(-a * t) * math.sqrt(v0 / v_t)


def flow_map(y0: float, t: float, a: float, m0: float, v0: float) -> float:
    """Exact PFG flow map ``m_t + sqrt(v_t / v0) (y0 - m0)``."""
    m_t, v_t = ou_moments(t, a, m0, v0)
    return m_t + math.sqrt(v_t / v0) * (y0 - m0)


def mehler_step(x: float, dt: float, a: float, xi: float) -> float:
    """Exact OU transition over ``dt``: ``e^{-a dt} x + sqrt(1 - e^{-2 a dt}) xi``."""
    return math.exp(-a * dt) * x + math.sqrt(-math.expm1(-2.0 * a * dt)) * xi


@dataclass(frozen=True)
class TimeStats:
    t: float
    exact_mean: float
    exact_var: float
    ou_mean: float
    ou_var: float
    flow_mean: float
    flow_var: float
    exact_ou_corr: float
    ou_corr: float
    flow_corr: float
    ou_msd: float  # sample E (X_t - X_0)^2
    flow_msd: float


def simulate(
    n: int = N_SAMPLES,
    times: Sequence[float] = TIMES,
    a: float = 1.0,
    m0: float = 2.0,
    v0: float = 0.25,
    seed: int = SEED,
) -> list[TimeStats]:
    """Run OU (exact Mehler steps between consecutive ``times``) and the flow on shared samples."""
    rng = random.Random(seed)
    x0 = [m0 + math.sqrt(v0) * rng.gauss(0.0, 1.0) for _ in range(n)]
    ou = list(x0)
    previous = 0.0
    out = []
    for t in times:
        dt = t - previous
        ou = [mehler_step(x, dt, a, rng.gauss(0.0, 1.0)) for x in ou]
        previous = t
        flow = [flow_map(y, t, a, m0, v0) for y in x0]
        m_t, v_t = ou_moments(t, a, m0, v0)
        out.append(
            TimeStats(
                t=t,
                exact_mean=m_t,
                exact_var=v_t,
                ou_mean=statistics.fmean(ou),
                ou_var=statistics.variance(ou),
                flow_mean=statistics.fmean(flow),
                flow_var=statistics.variance(flow),
                exact_ou_corr=ou_correlation(t, a, m0, v0),
                ou_corr=statistics.correlation(x0, ou),
                flow_corr=statistics.correlation(x0, flow),
                ou_msd=statistics.fmean((x - y) ** 2 for x, y in zip(x0, ou)),
                flow_msd=statistics.fmean((x - y) ** 2 for x, y in zip(x0, flow)),
            )
        )
    return out


def exact_covariance_gap(t: float, a: float, m0: float, v0: float) -> float:
    """``Cov_flow(Y_0, Y_t) - Cov_OU(X_0, X_t) = sqrt(v0 v_t) - e^{-a t} v0`` (> 0 for t > 0)."""
    _, v_t = ou_moments(t, a, m0, v0)
    return math.sqrt(v0 * v_t) - math.exp(-a * t) * v0


def exact_mean_square_displacement(t: float, a: float, m0: float, v0: float) -> tuple[float, float]:
    """Exact ``E (X_t - X_0)^2`` for OU and for the flow (same marginals, different values)."""
    m_t, v_t = ou_moments(t, a, m0, v0)
    drift = (m_t - m0) ** 2
    ou = v_t + v0 - 2.0 * math.exp(-a * t) * v0 + drift
    flow = (math.sqrt(v_t) - math.sqrt(v0)) ** 2 + drift
    return ou, flow


def marginal_agreement(stats: TimeStats, n: int) -> tuple[bool, str]:
    """Means within ``N_SE`` standard errors ``sqrt(v_t / n)``, variances within ``N_SE``
    standard errors ``v_t sqrt(2 / (n - 1))`` of the exact Gaussian marginal."""
    se_mean = math.sqrt(stats.exact_var / n)
    se_var = stats.exact_var * math.sqrt(2.0 / (n - 1))
    ok = all(
        (
            abs(stats.ou_mean - stats.exact_mean) < N_SE * se_mean,
            abs(stats.flow_mean - stats.exact_mean) < N_SE * se_mean,
            abs(stats.ou_var - stats.exact_var) < N_SE * se_var,
            abs(stats.flow_var - stats.exact_var) < N_SE * se_var,
        )
    )
    detail = (
        f"t={stats.t}: mean exact {stats.exact_mean:.4f} OU {stats.ou_mean:.4f} "
        f"flow {stats.flow_mean:.4f}; var exact {stats.exact_var:.4f} OU {stats.ou_var:.4f} "
        f"flow {stats.flow_var:.4f}"
    )
    return ok, detail


def correlation_contrast(
    stats: TimeStats, n: int, a: float, m0: float, v0: float
) -> tuple[bool, str]:
    """OU sample correlation within ``N_SE`` standard errors ``(1 - rho^2)/sqrt(n - 1)`` of
    ``e^{-a t} sqrt(v0/v_t)``; flow correlation equal to 1 up to rounding."""
    msd_ou, msd_flow = exact_mean_square_displacement(stats.t, a, m0, v0)
    rho = stats.exact_ou_corr
    se = (1.0 - rho**2) / math.sqrt(n - 1)
    ok = abs(stats.ou_corr - rho) < N_SE * se and abs(stats.flow_corr - 1.0) < 1e-9
    detail = (
        f"t={stats.t}: OU {stats.ou_corr:.4f} (exact {rho:.4f}), flow {stats.flow_corr:.12f}; "
        f"E(X_t-X_0)^2 OU {stats.ou_msd:.3f} vs flow {stats.flow_msd:.3f} "
        f"(exact {msd_ou:.3f} vs {msd_flow:.3f})"
    )
    return ok, detail


def run_checks(n: int = N_SAMPLES, seed: int = SEED) -> list[Check]:
    a, m0, v0 = 1.0, 2.0, 0.25
    results = simulate(n=n, a=a, m0=m0, v0=v0, seed=seed)
    checks: list[Check] = []
    for stats in results:
        ok, detail = marginal_agreement(stats, n)
        checks.append(Check("EX-1 one-time marginals agree (OU vs flow)", ok, detail))
    for stats in results:
        ok, detail = correlation_contrast(stats, n, a, m0, v0)
        checks.append(Check("CE-01 two-time correlations differ", ok, detail))
    gaps = [exact_covariance_gap(t, a, m0, v0) for t in TIMES]
    checks.append(
        Check(
            "CE-01 exact covariance gap sqrt(v0 v_t) - e^{-at} v0 > 0 for t > 0",
            all(g > 0 for g in gaps) and exact_covariance_gap(0.0, a, m0, v0) == 0.0,
            ", ".join(f"t={t}: {g:.4f}" for t, g in zip(TIMES, gaps)),
        )
    )
    return checks


def main() -> int:
    return print_report("sampling_vs_score_flow: same marginals, different paths", run_checks())


if __name__ == "__main__":
    raise SystemExit(main())
