"""Tests for experiments.kernel_tv_checks (exact Fraction checks; illustrations, not proofs)."""

import contextlib
import io
import random
import unittest
from fractions import Fraction

from experiments import kernel_tv_checks as kt

F = Fraction


class TotalVariationTests(unittest.TestCase):
    def test_tv_normalisation_and_basic_properties(self):
        rng = random.Random(1)
        for _ in range(40):
            n = rng.randint(1, 6)
            mu, nu = kt.random_law(rng, n, 0.3), kt.random_law(rng, n, 0.3)
            self.assertTrue(kt.is_law(mu) and kt.is_law(nu))
            self.assertEqual(kt.tv(mu, nu), kt.tv_sup(mu, nu))
            self.assertEqual(kt.tv(mu, nu), kt.tv(nu, mu))
            self.assertTrue(0 <= kt.tv(mu, nu) <= 1)
            self.assertEqual(kt.tv(mu, mu), 0)
        self.assertEqual(kt.tv([F(1), F(0)], [F(0), F(1)]), 1)

    def test_composition_is_consistent(self):
        rng = random.Random(2)
        P, Q = kt.random_kernel(rng, 4), kt.random_kernel(rng, 4)
        mu = kt.random_law(rng, 4)
        self.assertTrue(kt.is_kernel(kt.compose(P, Q)))
        self.assertEqual(kt.push(kt.push(mu, P), Q), kt.push(mu, kt.compose(P, Q)))

    def test_contraction(self):
        rng = random.Random(3)
        for _ in range(60):
            n = rng.randint(2, 6)
            P = kt.random_kernel(rng, n)
            mu, nu = kt.random_law(rng, n, 0.2), kt.random_law(rng, n, 0.2)
            delta = kt.dobrushin(P)
            self.assertTrue(0 <= delta <= 1)
            self.assertLessEqual(kt.tv(kt.push(mu, P), kt.push(nu, P)), delta * kt.tv(mu, nu))

    def test_dobrushin_extremes(self):
        identity = [[F(1), F(0)], [F(0), F(1)]]
        constant = [[F(1, 3), F(2, 3)], [F(1, 3), F(2, 3)]]
        self.assertEqual(kt.dobrushin(identity), 1)
        self.assertEqual(kt.dobrushin(constant), 0)


class TelescopingTests(unittest.TestCase):
    def test_random_instances(self):
        rng = random.Random(4)
        for _ in range(25):
            n, K = rng.randint(2, 5), rng.randint(1, 5)
            exact = [kt.random_kernel(rng, n) for _ in range(K)]
            inexact = [kt.random_kernel(rng, n) for _ in range(K)]
            bounds = kt.telescoping_bounds(kt.random_law(rng, n), exact, inexact)
            self.assertTrue(kt.bounds_hold(bounds), bounds)

    def test_exact_kernels_give_zero_error(self):
        rng = random.Random(5)
        exact = [kt.random_kernel(rng, 3) for _ in range(3)]
        bounds = kt.telescoping_bounds(kt.random_law(rng, 3), exact, exact)
        self.assertEqual(set(bounds.values()), {0})

    def test_localized_error_example(self):
        b = kt.localized_error_example(steps=10)
        self.assertEqual(b["final_tv"], F(1, 100))
        self.assertEqual(b["averaged_inexact_law"], F(1, 100))
        self.assertEqual(b["averaged_exact_law"], F(1, 10))
        self.assertEqual(b["uniform"], 10)
        self.assertTrue(kt.bounds_hold(b))


class MetropolisHastingsTests(unittest.TestCase):
    def test_detailed_balance_and_invariance(self):
        rng = random.Random(6)
        for _ in range(30):
            n = rng.randint(2, 6)
            pi, q = kt.random_positive_law(rng, n), kt.random_proposal(rng, n)
            for rule in ("metropolis", "barker"):
                with self.subTest(rule=rule):
                    K = kt.mh_kernel(pi, q, rule)
                    self.assertTrue(kt.is_kernel(K))
                    self.assertTrue(kt.detailed_balance(pi, K))
                    self.assertTrue(kt.is_invariant(pi, K))

    def test_unknown_rule_rejected(self):
        pi = [F(1, 2), F(1, 2)]
        q = [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]
        with self.assertRaises(ValueError):
            kt.mh_kernel(pi, q, rule="greedy")

    def test_symmetric_proposal_needs_no_hastings_ratio(self):
        pi = [F(1, 6), F(1, 3), F(1, 2)]
        q = [[F(0), F(1, 2), F(1, 2)], [F(1, 2), F(0), F(1, 2)], [F(1, 2), F(1, 2), F(0)]]
        K = kt.mh_kernel(pi, q, hastings=False)
        self.assertTrue(kt.detailed_balance(pi, K))
        self.assertTrue(kt.is_invariant(pi, K))

    def test_dropping_hastings_ratio_breaks_invariance(self):
        pi, pushed = kt.missing_hastings_counterexample()
        self.assertEqual(pushed, [F(3, 8), F(5, 8)])
        self.assertNotEqual(pushed, pi)

    def test_geometric_tv_convergence(self):
        rng = random.Random(7)
        pi = kt.random_positive_law(rng, 4)
        K = kt.mh_kernel(pi, kt.random_proposal(rng, 4, zero_prob=0.0))
        delta = kt.dobrushin(K)
        self.assertLess(delta, 1)
        mu = [F(0), F(0), F(0), F(1)]
        law = mu
        for step in range(1, 7):
            law = kt.push(law, K)
            self.assertLessEqual(kt.tv(law, pi), delta**step * kt.tv(mu, pi))


class ReportTests(unittest.TestCase):
    def test_all_checks_pass_and_main_succeeds(self):
        checks = kt.run_checks()
        self.assertEqual([c.name for c in checks if not c.ok], [])
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(kt.main(), 0)
        self.assertIn("not proofs", out.getvalue())


if __name__ == "__main__":
    unittest.main()
