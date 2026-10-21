"""Finite-state Markov kernels in exact Fractions: TV contraction, telescoping, Metropolis-Hastings.

TV is normalised as ``TV(mu, nu) = sup_A |mu(A) - nu(A)| = (1/2) sum_x |mu(x) - nu(x)|``; both
forms are computed and compared. Laws are row vectors and kernels act on the right
(``(mu P)(y) = sum_x mu(x) P(x, y)``).

* KR-1 (TV contraction). ``TV(mu P, nu P) <= delta(P) TV(mu, nu) <= TV(mu, nu)`` with the
  Dobrushin coefficient ``delta(P) = max_{x, x'} TV(P(x, .), P(x', .))``.
* KR-1 (telescoping, inexact kernels). Exact kernels ``P_1..P_K`` and inexact ``Q_1..Q_K``
  from the same initial law: ``mu_k = mu_0 P_1...P_k`` and ``nu_k = mu_0 Q_1...Q_k``. Then

      TV(mu_K, nu_K) <= sum_k E_{x ~ mu_{k-1}} TV(P_k(x, .), Q_k(x, .))   (law-averaged, exact law)
      TV(mu_K, nu_K) <= sum_k E_{x ~ nu_{k-1}} TV(P_k(x, .), Q_k(x, .))   (law-averaged, inexact)
      both <= sum_k max_x TV(P_k(x, .), Q_k(x, .))                          (uniform)

  The first telescopes ``mu_K - nu_K = sum_k (mu_{k-1} P_k - mu_{k-1} Q_k) Q_{k+1} ... Q_K`` and
  contracts under the ``Q``'s; the second swaps the roles. A hand-made example shows the
  law-averaged bound can be far smaller than the uniform one.
* MH-1 (Metropolis-Hastings). For a positive target ``pi`` and a proposal ``q`` with symmetric
  support, the Hastings kernel ``K(x, y) = q(x, y) alpha(x, y)`` (``y != x``) with
  ``alpha = min(1, pi(y) q(y, x) / (pi(x) q(x, y)))`` (or Barker's rule) satisfies detailed
  balance ``pi(x) K(x, y) = pi(y) K(y, x)`` and invariance ``pi K = pi``, exactly. Dropping the
  Hastings correction for an asymmetric proposal breaks invariance (exact counterexample).

Exact rational arithmetic; illustrations, never proofs.
"""

from __future__ import annotations

import itertools
import random
from collections.abc import Sequence
from fractions import Fraction

from experiments._common import Check, print_report

Law = list[Fraction]
Kernel = list[list[Fraction]]
SEED = 20251013

# ---------------------------------------------------------------------------------------------
# Basic operations.
# ---------------------------------------------------------------------------------------------


def random_law(rng: random.Random, n: int, zero_prob: float = 0.0) -> Law:
    """A random probability vector with rational entries (at least one positive entry)."""
    weights = [0 if rng.random() < zero_prob else rng.randint(1, 9) for _ in range(n)]
    if not any(weights):
        weights[rng.randrange(n)] = 1
    total = sum(weights)
    return [Fraction(w, total) for w in weights]


def random_kernel(rng: random.Random, n: int, zero_prob: float = 0.3) -> Kernel:
    """A random row-stochastic ``n x n`` matrix with rational entries."""
    return [random_law(rng, n, zero_prob) for _ in range(n)]


def is_law(mu: Sequence[Fraction]) -> bool:
    return all(p >= 0 for p in mu) and sum(mu) == 1


def is_kernel(P: Sequence[Sequence[Fraction]]) -> bool:
    return all(is_law(row) for row in P)


def push(mu: Sequence[Fraction], P: Sequence[Sequence[Fraction]]) -> Law:
    """``(mu P)(y) = sum_x mu(x) P(x, y)``."""
    n = len(P[0])
    return [sum((mu[x] * P[x][y] for x in range(len(mu))), Fraction(0)) for y in range(n)]


def compose(P: Kernel, Q: Kernel) -> Kernel:
    """``(P Q)(x, z) = sum_y P(x, y) Q(y, z)``."""
    return [push(row, Q) for row in P]


def tv(mu: Sequence[Fraction], nu: Sequence[Fraction]) -> Fraction:
    """``(1/2) sum_x |mu(x) - nu(x)|``."""
    return sum((abs(a - b) for a, b in zip(mu, nu, strict=True)), Fraction(0)) / 2


def tv_sup(mu: Sequence[Fraction], nu: Sequence[Fraction]) -> Fraction:
    """``max_A |mu(A) - nu(A)|`` by enumerating every subset ``A`` (small state spaces only)."""
    n = len(mu)
    best = Fraction(0)
    for mask in itertools.product((False, True), repeat=n):
        diff = sum((mu[i] - nu[i] for i in range(n) if mask[i]), Fraction(0))
        best = max(best, abs(diff))
    return best


def dobrushin(P: Kernel) -> Fraction:
    """``delta(P) = max_{x, x'} TV(P(x, .), P(x', .))``."""
    return max(tv(P[i], P[j]) for i in range(len(P)) for j in range(len(P)))


def chain_laws(mu0: Law, kernels: Sequence[Kernel]) -> list[Law]:
    """``[mu_0, mu_0 P_1, mu_0 P_1 P_2, ...]``."""
    laws = [list(mu0)]
    for P in kernels:
        laws.append(push(laws[-1], P))
    return laws


# ---------------------------------------------------------------------------------------------
# Telescoping bounds.
# ---------------------------------------------------------------------------------------------


def row_errors(P: Kernel, Q: Kernel) -> list[Fraction]:
    """``[TV(P(x, .), Q(x, .)) for x]``."""
    return [tv(p, q) for p, q in zip(P, Q, strict=True)]


def telescoping_bounds(
    mu0: Law, exact: Sequence[Kernel], inexact: Sequence[Kernel]
) -> dict[str, Fraction]:
    """The final TV error and the bounds of KR-1, all exact.

    ``step_exact_law`` is ``sum_k TV(mu_{k-1} P_k, mu_{k-1} Q_k)``, which sits between the final
    error and ``averaged_exact_law`` by convexity of TV.
    """
    mus = chain_laws(mu0, exact)
    nus = chain_laws(mu0, inexact)
    errs = [row_errors(P, Q) for P, Q in zip(exact, inexact, strict=True)]
    K = len(exact)
    return {
        "final_tv": tv(mus[-1], nus[-1]),
        "step_exact_law": sum(
            (tv(push(mus[k], exact[k]), push(mus[k], inexact[k])) for k in range(K)), Fraction(0)
        ),
        "averaged_exact_law": sum(
            (sum(m * e for m, e in zip(mus[k], errs[k])) for k in range(K)), Fraction(0)
        ),
        "averaged_inexact_law": sum(
            (sum(m * e for m, e in zip(nus[k], errs[k])) for k in range(K)), Fraction(0)
        ),
        "uniform": sum((max(e) for e in errs), Fraction(0)),
    }


def bounds_hold(b: dict[str, Fraction]) -> bool:
    """The chain of inequalities in KR-1."""
    return (
        b["final_tv"] <= b["step_exact_law"] <= b["averaged_exact_law"] <= b["uniform"]
        and b["final_tv"] <= b["averaged_inexact_law"] <= b["uniform"]
    )


def localized_error_example(steps: int = 10) -> dict[str, Fraction]:
    """Exact kernel = identity on 3 states; the inexact kernel moves state 2 to state 0.

    The initial law puts mass 1/100 on state 2, so each step's uniform error is 1 while the
    law-averaged error is at most 1/100: the averaged bounds are far tighter.
    """
    one, zero = Fraction(1), Fraction(0)
    identity = [[one, zero, zero], [zero, one, zero], [zero, zero, one]]
    broken = [[one, zero, zero], [zero, one, zero], [one, zero, zero]]
    mu0 = [Fraction(1, 2), Fraction(49, 100), Fraction(1, 100)]
    return telescoping_bounds(mu0, [identity] * steps, [broken] * steps)


# ---------------------------------------------------------------------------------------------
# Metropolis-Hastings.
# ---------------------------------------------------------------------------------------------


def random_positive_law(rng: random.Random, n: int) -> Law:
    weights = [rng.randint(1, 12) for _ in range(n)]
    total = sum(weights)
    return [Fraction(w, total) for w in weights]


def random_proposal(rng: random.Random, n: int, zero_prob: float = 0.3) -> Kernel:
    """A random proposal kernel whose support is symmetric: ``q(x, y) > 0 iff q(y, x) > 0``."""
    support = [[x == y for y in range(n)] for x in range(n)]
    for x in range(n):
        for y in range(x + 1, n):
            if rng.random() >= zero_prob:
                support[x][y] = support[y][x] = True
    rows = []
    for x in range(n):
        weights = [rng.randint(1, 9) if support[x][y] else 0 for y in range(n)]
        total = sum(weights)
        rows.append([Fraction(w, total) for w in weights])
    return rows


def acceptance(
    pi: Law, q: Kernel, x: int, y: int, rule: str = "metropolis", hastings: bool = True
) -> Fraction:
    """Acceptance probability of a proposed move ``x -> y`` (``q(x, y) > 0``).

    ``rule`` is ``"metropolis"`` (``min(1, r)``) or ``"barker"`` (``r / (1 + r)``) with the
    Hastings ratio ``r = pi(y) q(y, x) / (pi(x) q(x, y))``; ``hastings=False`` drops the proposal
    ratio, which is only valid for symmetric proposals.
    """
    r = pi[y] / pi[x]
    if hastings:
        r *= q[y][x] / q[x][y]
    if rule == "metropolis":
        return min(Fraction(1), r)
    if rule == "barker":
        return r / (1 + r)
    raise ValueError(f"unknown acceptance rule {rule!r}")


def mh_kernel(pi: Law, q: Kernel, rule: str = "metropolis", hastings: bool = True) -> Kernel:
    """Hastings kernel ``K(x, y) = q(x, y) alpha(x, y)`` (``y != x``); rejections stay at ``x``."""
    n = len(pi)
    K = [[Fraction(0)] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            if y != x and q[x][y] > 0:
                K[x][y] = q[x][y] * acceptance(pi, q, x, y, rule, hastings)
        K[x][x] = 1 - sum(K[x][y] for y in range(n) if y != x)
    return K


def detailed_balance(pi: Law, K: Kernel) -> bool:
    n = len(pi)
    return all(pi[x] * K[x][y] == pi[y] * K[y][x] for x in range(n) for y in range(n))


def is_invariant(pi: Law, K: Kernel) -> bool:
    return push(pi, K) == list(pi)


def missing_hastings_counterexample() -> tuple[Law, Law]:
    """Uniform target on 2 states, asymmetric proposal, Hastings ratio dropped.

    Every move is then accepted, ``K = q``, and ``pi q != pi`` because ``q`` is not doubly
    stochastic. Returns ``(pi, pi K)``.
    """
    pi = [Fraction(1, 2), Fraction(1, 2)]
    q = [[Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 4), Fraction(3, 4)]]
    return pi, push(pi, mh_kernel(pi, q, hastings=False))


# ---------------------------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------------------------


def run_checks(seed: int = SEED, trials: int = 60) -> list[Check]:
    rng = random.Random(seed)
    checks: list[Check] = []

    tv_ok = True
    for _ in range(trials):
        n = rng.randint(2, 6)
        mu, nu = random_law(rng, n, 0.2), random_law(rng, n, 0.2)
        tv_ok &= tv(mu, nu) == tv_sup(mu, nu)
    checks.append(
        Check("TV normalisation: sup_A |mu(A) - nu(A)| = (1/2) L1", tv_ok, f"{trials} random pairs")
    )

    contraction_ok = True
    strict = 0
    for _ in range(trials):
        n = rng.randint(2, 6)
        P = random_kernel(rng, n)
        mu, nu = random_law(rng, n, 0.2), random_law(rng, n, 0.2)
        lhs = tv(push(mu, P), push(nu, P))
        mid = dobrushin(P) * tv(mu, nu)
        contraction_ok &= is_kernel(P) and lhs <= mid <= tv(mu, nu)
        strict += lhs < tv(mu, nu)
    checks.append(
        Check(
            "KR-1 TV(mu P, nu P) <= delta(P) TV(mu, nu) <= TV(mu, nu)",
            contraction_ok,
            f"{trials} random kernels; strict contraction in {strict}",
        )
    )

    telescoping_ok = True
    example = None
    for _ in range(trials // 3):
        n, K = rng.randint(2, 5), rng.randint(1, 5)
        exact = [random_kernel(rng, n) for _ in range(K)]
        inexact = []
        for P in exact:
            eps = Fraction(rng.randint(0, 3), 10)
            noise = random_kernel(rng, n)
            inexact.append(
                [[(1 - eps) * p + eps * r for p, r in zip(Pr, Rr)] for Pr, Rr in zip(P, noise)]
            )
        b = telescoping_bounds(random_law(rng, n), exact, inexact)
        telescoping_ok &= bounds_hold(b)
        example = b
    assert example is not None
    checks.append(
        Check(
            "KR-1 telescoping: final TV <= law-averaged (exact / inexact law) <= uniform",
            telescoping_ok,
            "last instance: " + ", ".join(f"{k}={float(v):.4f}" for k, v in example.items()),
        )
    )

    local = localized_error_example()
    checks.append(
        Check(
            "KR-1 law-averaged bound can be far below the uniform bound",
            bounds_hold(local)
            and local["final_tv"] == Fraction(1, 100)
            and local["averaged_inexact_law"] == Fraction(1, 100)
            and local["averaged_exact_law"] == Fraction(1, 10)
            and local["uniform"] == 10,
            ", ".join(f"{k}={v}" for k, v in local.items()),
        )
    )

    mh_ok = True
    for _ in range(trials // 2):
        n = rng.randint(2, 6)
        pi = random_positive_law(rng, n)
        q = random_proposal(rng, n)
        for rule in ("metropolis", "barker"):
            K = mh_kernel(pi, q, rule)
            mh_ok &= is_kernel(K) and detailed_balance(pi, K) and is_invariant(pi, K)
    checks.append(
        Check(
            "MH-1 MH (Metropolis and Barker): detailed balance and pi K = pi, exactly",
            mh_ok,
            f"{trials // 2} random (pi, q) pairs with asymmetric proposals",
        )
    )

    rng_mix = random.Random(seed + 1)
    pi = random_positive_law(rng_mix, 5)
    K = mh_kernel(pi, random_proposal(rng_mix, 5, zero_prob=0.0))
    delta = dobrushin(K)
    mu = [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]
    mixing_ok = delta < 1
    law = mu
    for step in range(1, 9):
        law = push(law, K)
        mixing_ok &= tv(law, pi) <= delta**step * tv(mu, pi)
    checks.append(
        Check(
            "MH chain: TV(mu K^n, pi) <= delta(K)^n TV(mu, pi)",
            mixing_ok,
            f"delta(K) = {float(delta):.4f}, TV after 8 steps = {float(tv(law, pi)):.2e}",
        )
    )

    pi2, pushed = missing_hastings_counterexample()
    checks.append(
        Check(
            "Counterexample: dropping the Hastings ratio breaks invariance",
            pushed != pi2,
            f"pi = {[str(p) for p in pi2]}, pi K = {[str(p) for p in pushed]}",
        )
    )
    return checks


def main() -> int:
    return print_report("kernel_tv_checks: TV contraction, telescoping, MH", run_checks())


if __name__ == "__main__":
    raise SystemExit(main())
