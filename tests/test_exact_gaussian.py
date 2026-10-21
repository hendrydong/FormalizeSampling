"""Tests for experiments.exact_gaussian (exact checks; illustrations, not proofs)."""

import contextlib
import io
import random
import unittest
from fractions import Fraction

from experiments import exact_gaussian as eg


class UlaSgldTests(unittest.TestCase):
    def test_one_step_variance_is_one_plus_h_squared(self):
        for h in eg.H_VALUES:
            with self.subTest(h=h):
                self.assertEqual(eg.ula_one_step_variance_from_target(h), 1 + h**2)
                self.assertNotEqual(eg.ula_one_step_variance_from_target(h), 1)
        self.assertEqual(eg.ula_one_step_variance_from_target(Fraction(1, 2)), Fraction(5, 4))

    def test_target_is_invariant_only_without_step(self):
        self.assertEqual(eg.ula_one_step_variance_from_target(Fraction(0)), 1)

    def test_stationary_variance_is_fixed_point(self):
        for h in eg.H_VALUES:
            with self.subTest(h=h):
                v_star = eg.ula_stationary_variance(h)
                self.assertEqual(v_star, 2 / (2 - h))
                self.assertEqual(eg.ula_variance_step(v_star, h), v_star)
                self.assertGreater(v_star, 1)

    def test_stationary_variance_requires_step_in_range(self):
        for h in (Fraction(0), Fraction(2), Fraction(5, 2), Fraction(-1)):
            with self.subTest(h=h), self.assertRaises(ValueError):
                eg.ula_stationary_variance(h)

    def test_geometric_convergence(self):
        for h in eg.H_VALUES:
            for v0 in (Fraction(0), Fraction(1), Fraction(7, 3)):
                with self.subTest(h=h, v0=v0):
                    self.assertTrue(eg.ula_geometric_convergence_holds(h, v0, 12))

    def test_sgld_stationary_variance(self):
        for h in eg.H_VALUES:
            previous = None
            for tau2 in eg.TAU2_VALUES:
                with self.subTest(h=h, tau2=tau2):
                    v_star = eg.sgld_stationary_variance(h, tau2)
                    self.assertEqual(v_star, (2 + h * tau2) / (2 - h))
                    self.assertEqual(eg.sgld_variance_step(v_star, h, tau2), v_star)
                    if previous is not None:
                        self.assertGreater(v_star, previous)
                    previous = v_star
            self.assertEqual(
                eg.sgld_stationary_variance(h, Fraction(0)), eg.ula_stationary_variance(h)
            )

    def test_sgld_iterates_converge_geometrically(self):
        h, tau2 = Fraction(1, 3), Fraction(2)
        v_star = eg.sgld_stationary_variance(h, tau2)
        iterates = eg.variance_iterates(
            lambda v: eg.sgld_variance_step(v, h, tau2), Fraction(1), 10
        )
        for n, v in enumerate(iterates):
            self.assertEqual(v - v_star, (1 - h) ** (2 * n) * (1 - v_star))


class OuPfgMomentTests(unittest.TestCase):
    def test_moment_odes_agree(self):
        rng = random.Random(7)
        for _ in range(30):
            m = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
            v = Fraction(rng.randint(1, 9), rng.randint(1, 5))
            a = Fraction(rng.randint(1, 5), rng.randint(1, 3))
            dm, dv = eg.affine_field_moment_derivatives(m, v, a)
            self.assertEqual((dm, dv), eg.ou_moment_derivatives(m, v, a))
            self.assertEqual(dv, 2 * a * (1 - v))

    def test_moment_formula_limits(self):
        m, v = eg.ou_gaussian_moments(0.0, 1.3, 2.0, 0.25)
        self.assertEqual((m, v), (2.0, 0.25))
        m, v = eg.ou_gaussian_moments(50.0, 1.0, 2.0, 0.25)
        self.assertAlmostEqual(m, 0.0, places=12)
        self.assertAlmostEqual(v, 1.0, places=12)

    def test_flow_map_pushes_quantiles_to_quantiles(self):
        for v0 in (0.25, 1.0, 4.0):
            for t in (0.1, 1.0, 3.0):
                with self.subTest(v0=v0, t=t):
                    self.assertLess(eg.flow_map_quantile_error(51, t, 0.7, -1.0, v0), 1e-9)

    def test_flow_map_is_increasing(self):
        ys = eg.initial_quantiles(40, 2.0, 0.25)
        mapped = [eg.pfg_flow_map(y, 1.0, 1.0, 2.0, 0.25) for y in ys]
        self.assertTrue(all(b > a for a, b in zip(mapped, mapped[1:])))

    def test_euler_converges_at_first_order(self):
        coarse = eg.euler_quantile_error(41, 1.0, 400, 1.0, 2.0, 0.25)
        fine = eg.euler_quantile_error(41, 1.0, 800, 1.0, 2.0, 0.25)
        self.assertLess(fine, coarse)
        self.assertLess(fine, 1e-2)
        self.assertTrue(1.8 < coarse / fine < 2.2, coarse / fine)


class SteinTests(unittest.TestCase):
    def test_standard_normal_moments(self):
        self.assertEqual(
            [eg.std_normal_moment(n) for n in range(11)], [1, 0, 1, 0, 3, 0, 15, 0, 105, 0, 945]
        )

    def test_gaussian_moments(self):
        mu, var = Fraction(1, 2), Fraction(3)
        self.assertEqual(eg.gaussian_moment(1, mu, var), mu)
        self.assertEqual(eg.gaussian_moment(2, mu, var), var + mu**2)
        self.assertEqual(eg.gaussian_moment(4, mu, var), mu**4 + 6 * mu**2 * var + 3 * var**2)

    def test_stein_identity_random_polynomials(self):
        rng = random.Random(11)
        for degree in range(10):
            coeffs = eg.random_rational_poly(rng, degree)
            lhs, rhs = eg.stein_sides(coeffs)
            self.assertEqual(lhs, rhs)

    def test_density_stein_for_shifted_scaled_gaussian(self):
        rng = random.Random(12)
        for _ in range(20):
            coeffs = eg.random_rational_poly(rng, rng.randint(0, 6))
            mean = Fraction(rng.randint(-5, 5), rng.randint(1, 3))
            var = Fraction(rng.randint(1, 5), rng.randint(1, 3))
            lhs, rhs = eg.stein_sides(coeffs, mean, var)
            self.assertEqual(lhs, rhs)

    def test_variance_factor_is_needed(self):
        # For X ~ N(0, 2) and phi(x) = x: E[X phi(X)] = 2 = 2 E[phi'(X)], but E[phi'(X)] = 1.
        phi = [Fraction(0), Fraction(1)]
        lhs, rhs = eg.stein_sides(phi, var=Fraction(2))
        self.assertEqual((lhs, rhs), (2, 2))
        unscaled = eg.poly_expectation(
            eg.poly_derivative(phi), lambda n: eg.gaussian_moment(n, Fraction(0), Fraction(2))
        )
        self.assertEqual(unscaled, 1)
        self.assertNotEqual(lhs, unscaled)

    def test_rademacher_counterexample(self):
        self.assertEqual(eg.rademacher_stein_sides([Fraction(0), Fraction(1)]), (1, 1))
        cubic = eg.rademacher_stein_sides([Fraction(0)] * 3 + [Fraction(1)])
        self.assertEqual(cubic, (1, 3))


class ReportTests(unittest.TestCase):
    def test_all_checks_pass_and_main_succeeds(self):
        checks = eg.run_checks()
        self.assertTrue(checks)
        self.assertEqual([c.name for c in checks if not c.ok], [])
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(eg.main(), 0)
        self.assertIn("not proofs", out.getvalue())


if __name__ == "__main__":
    unittest.main()
