"""Tests for experiments.gaussian_mixtures (floating-point illustrations, not proofs)."""

import contextlib
import io
import unittest

from experiments import gaussian_mixtures as gm

MIX = gm.EXAMPLE_MIXTURE
ATOMS = gm.EXAMPLE_ATOMS


class MixtureTests(unittest.TestCase):
    def test_invalid_mixtures_rejected(self):
        with self.assertRaises(ValueError):
            gm.Mixture1D((0.5, 0.6), (0.0, 1.0), (1.0, 1.0))
        with self.assertRaises(ValueError):
            gm.Mixture1D((1.0,), (0.0,), (-1.0,))
        with self.assertRaises(ValueError):
            gm.Mixture1D((0.5, 0.5), (0.0,), (1.0, 1.0))

    def test_atomic_prior_has_no_density(self):
        self.assertTrue(ATOMS.is_atomic)
        with self.assertRaises(ValueError):
            ATOMS.prior_density(0.0)

    def test_closed_form_convolution_matches_quadrature(self):
        for sigma in gm.SIGMAS:
            for y in gm.Y_GRID:
                with self.subTest(sigma=sigma, y=y):
                    self.assertAlmostEqual(
                        gm.quadrature_density(MIX, sigma, y),
                        gm.smoothed_density(MIX, sigma, y),
                        delta=1e-9,
                    )

    def test_posterior_mean_matches_quadrature(self):
        for sigma in gm.SIGMAS:
            for y in gm.Y_GRID:
                with self.subTest(sigma=sigma, y=y):
                    self.assertAlmostEqual(
                        gm.quadrature_posterior_mean(MIX, sigma, y),
                        gm.posterior_mean_x(MIX, sigma, y),
                        delta=1e-9,
                    )

    def test_responsibilities_are_a_distribution(self):
        r = gm.responsibilities(MIX, 0.5, 1.2)
        self.assertAlmostEqual(sum(r), 1.0, places=14)
        self.assertTrue(all(0 < rk < 1 for rk in r))


class TweedieTests(unittest.TestCase):
    def test_tweedie_mixture_and_atomic(self):
        for prior in (MIX, ATOMS):
            for sigma in gm.SIGMAS:
                with self.subTest(atomic=prior.is_atomic, sigma=sigma):
                    errors = gm.tweedie_errors(prior, sigma, gm.Y_GRID)
                    self.assertLess(errors["mean_form"], 1e-6)
                    self.assertLess(errors["noise_form"], 1e-6)
                    self.assertLess(errors["analytic"], 1e-6)

    def test_mean_and_noise_forms_are_consistent(self):
        # Y = X + sigma Z gives E[X | Y = y] + sigma E[Z | Y = y] = y.
        for prior in (MIX, ATOMS):
            for sigma in gm.SIGMAS:
                for y in gm.Y_GRID:
                    total = gm.posterior_mean_x(prior, sigma, y)
                    total += sigma * gm.posterior_mean_z(prior, sigma, y)
                    self.assertAlmostEqual(total, y, delta=1e-12)

    def test_check_detects_wrong_scaling(self):
        # Dividing by sigma instead of sigma^2 is a typical convention slip; it must be caught.
        sigma, y = 0.3, 1.7
        fd = gm.fd_score(MIX, sigma, y)
        wrong = (gm.posterior_mean_x(MIX, sigma, y) - y) / sigma
        self.assertGreater(abs(fd - wrong), 1e-2)

    def test_gaussian_prior_closed_form(self):
        prior = gm.Mixture1D((1.0,), (0.0,), (2.0,))
        sigma = 0.5
        for y in gm.Y_GRID:
            shrink = 2.0 / (2.0 + sigma**2)
            self.assertAlmostEqual(gm.posterior_mean_x(prior, sigma, y), shrink * y, delta=1e-12)
            self.assertAlmostEqual(gm.fd_score(prior, sigma, y), -y / (2.0 + sigma**2), delta=1e-8)

    def test_atomic_posterior_is_discrete_bayes(self):
        for sigma in gm.SIGMAS:
            for y in gm.Y_GRID:
                self.assertAlmostEqual(
                    gm.atomic_posterior_mean(ATOMS, sigma, y),
                    gm.posterior_mean_x(ATOMS, sigma, y),
                    delta=1e-12,
                )

    def test_mean_score_is_zero(self):
        for sigma in gm.SIGMAS:
            self.assertLess(abs(gm.mean_score_quadrature(MIX, sigma)), 1e-9)

    def test_ou_posterior_score(self):
        for prior in (MIX, ATOMS):
            self.assertLess(gm.ou_score_errors(prior, (0.05, 0.5, 3.0), gm.Y_GRID), 1e-6)

    def test_ou_marginal_coefficients(self):
        a_t, s2_t = gm.ou_coefficients(0.7)
        self.assertAlmostEqual(a_t**2 + s2_t, 1.0, places=14)
        marginal = gm.ou_marginal(MIX, 0.7)
        for m, s2, m0, s20 in zip(marginal.means, marginal.variances, MIX.means, MIX.variances):
            self.assertAlmostEqual(m, a_t * m0, places=14)
            self.assertAlmostEqual(s2, a_t**2 * s20 + s2_t, places=14)

    def test_noise_is_not_a_function_of_y(self):
        for sigma in gm.SIGMAS:
            for y in gm.Y_GRID:
                self.assertGreater(gm.posterior_var_z(MIX, sigma, y), 0.0)
        gauss = gm.Mixture1D((1.0,), (0.0,), (2.0,))
        self.assertAlmostEqual(gm.posterior_var_z(gauss, 1.0, -3.0), 2.0 / 3.0, places=12)
        # For an atomic prior the noise is a function of Y only when there is a single atom.
        point = gm.Mixture1D((1.0,), (1.0,), (0.0,))
        self.assertAlmostEqual(gm.posterior_var_z(point, 1.0, 0.4), 0.0, places=12)
        self.assertGreater(gm.posterior_var_z(ATOMS, 1.0, 0.4), 0.0)


class ReportTests(unittest.TestCase):
    def test_all_checks_pass_and_main_succeeds(self):
        checks = gm.run_checks()
        self.assertEqual([c.name for c in checks if not c.ok], [])
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(gm.main(), 0)
        self.assertIn("not proofs", out.getvalue())


if __name__ == "__main__":
    unittest.main()
