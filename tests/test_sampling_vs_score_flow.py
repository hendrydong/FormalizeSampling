"""Tests for experiments.sampling_vs_score_flow (Monte Carlo illustrations, not proofs)."""

import contextlib
import io
import math
import unittest

from experiments import sampling_vs_score_flow as sf

A, M0, V0 = 1.0, 2.0, 0.25


class SimulationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.results = sf.simulate(n=sf.N_SAMPLES, a=A, m0=M0, v0=V0, seed=sf.SEED)

    def test_marginals_agree_with_exact_gaussian(self):
        for stats in self.results:
            with self.subTest(t=stats.t):
                ok, detail = sf.marginal_agreement(stats, sf.N_SAMPLES)
                self.assertTrue(ok, detail)

    def test_two_time_correlations_differ(self):
        for stats in self.results:
            with self.subTest(t=stats.t):
                ok, detail = sf.correlation_contrast(stats, sf.N_SAMPLES, A, M0, V0)
                self.assertTrue(ok, detail)
                self.assertLess(stats.exact_ou_corr, 0.6)
                self.assertGreater(stats.flow_corr, 1 - 1e-9)

    def test_simulation_is_deterministic(self):
        first = sf.simulate(n=300, seed=5)
        second = sf.simulate(n=300, seed=5)
        self.assertEqual(first, second)
        self.assertNotEqual(first, sf.simulate(n=300, seed=6))


class ExactFormulaTests(unittest.TestCase):
    def test_covariance_gap_positive_after_time_zero(self):
        self.assertEqual(sf.exact_covariance_gap(0.0, A, M0, V0), 0.0)
        for v0 in (0.25, 1.0, 9.0):
            for t in (0.01, 0.5, 4.0):
                with self.subTest(v0=v0, t=t):
                    self.assertGreater(sf.exact_covariance_gap(t, A, M0, v0), 0.0)
                    self.assertLess(sf.ou_correlation(t, A, M0, v0), 1.0)

    def test_flow_has_smaller_mean_square_displacement(self):
        for t in (0.1, 1.0, 5.0):
            ou, flow = sf.exact_mean_square_displacement(t, A, M0, V0)
            self.assertGreater(ou, flow)

    def test_mehler_semigroup(self):
        # Two exact steps of sizes s and u compose to one step of size s + u.
        s, u, a = 0.3, 0.45, 1.7
        coef = math.exp(-a * s) * math.exp(-a * u)
        var = math.exp(-2 * a * u) * (1 - math.exp(-2 * a * s)) + (1 - math.exp(-2 * a * u))
        self.assertAlmostEqual(coef, math.exp(-a * (s + u)), places=14)
        self.assertAlmostEqual(var, 1 - math.exp(-2 * a * (s + u)), places=14)
        self.assertAlmostEqual(sf.mehler_step(1.0, s + u, a, 0.0), coef, places=14)

    def test_flow_map_is_increasing_affine(self):
        ys = [-1.0, 0.0, 0.5, 2.0, 3.5]
        mapped = [sf.flow_map(y, 0.8, A, M0, V0) for y in ys]
        self.assertTrue(all(b > a for a, b in zip(mapped, mapped[1:])))
        slope = (mapped[1] - mapped[0]) / (ys[1] - ys[0])
        _, v_t = sf.ou_moments(0.8, A, M0, V0)
        self.assertAlmostEqual(slope, math.sqrt(v_t / V0), places=12)


class ReportTests(unittest.TestCase):
    def test_all_checks_pass_and_main_succeeds(self):
        checks = sf.run_checks()
        self.assertEqual([c.name for c in checks if not c.ok], [])
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(sf.main(), 0)
        self.assertIn("not proofs", out.getvalue())


if __name__ == "__main__":
    unittest.main()
