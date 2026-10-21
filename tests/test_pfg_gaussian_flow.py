"""Tests for experiments.pfg_gaussian_flow (exact checks and numerics; not proofs)."""

import contextlib
import io
import math
import random
import unittest
from fractions import Fraction

from experiments import pfg_gaussian_flow as pf

F = Fraction
S_STAR = pf.SIGMA_STAR
M0 = [F(4), F(1)]
S0 = pf.identity2(F(1))


def random_instance(rng):
    return pf.random_vec(rng), pf.random_spd(rng), pf.random_spd(rng), pf.random_spd(rng)


class MomentDynamicsTests(unittest.TestCase):
    def test_random_spd_is_spd(self):
        rng = random.Random(1)
        for _ in range(20):
            S = pf.random_spd(rng)
            self.assertEqual(S[0][1], S[1][0])
            self.assertGreater(S[0][0], 0)
            self.assertGreater(pf.det2(S), 0)

    def test_moments_follow_from_the_velocity_field(self):
        # Read off v(x) = B x + c from the velocity itself; then m' = B m + c, S' = B S + S B^T.
        rng = random.Random(2)
        zero, e0, e1 = [F(0), F(0)], [F(1), F(0)], [F(0), F(1)]
        for _ in range(25):
            m, S, A, S_star = random_instance(rng)
            c = pf.pfg_velocity(zero, m, S, A, S_star)
            cols = [
                [a - b for a, b in zip(pf.pfg_velocity(e, m, S, A, S_star), c)] for e in (e0, e1)
            ]
            B = pf.transpose(cols)
            dm, dS = pf.pfg_moment_derivatives(m, S, A, S_star)
            self.assertEqual(dm, [a + b for a, b in zip(pf.mv(B, m), c)])
            self.assertEqual(dS, pf.madd(pf.mm(B, S), pf.mm(S, pf.transpose(B))))

    def test_pfg_equals_langevin_lyapunov_form(self):
        rng = random.Random(3)
        for _ in range(25):
            m, S, A, S_star = random_instance(rng)
            self.assertEqual(
                pf.pfg_moment_derivatives(m, S, A, S_star),
                pf.langevin_moment_derivatives(m, S, A, S_star),
            )

    def test_continuity_equation(self):
        rng = random.Random(4)
        for _ in range(25):
            m, S, A, S_star = random_instance(rng)
            x = pf.random_vec(rng)
            dm, dS = pf.pfg_moment_derivatives(m, S, A, S_star)
            self.assertEqual(
                pf.log_density_time_derivative(x, m, S, dm, dS),
                pf.continuity_rhs_over_density(x, m, S, A, S_star),
            )

    def test_continuity_equation_detects_wrong_dynamics(self):
        rng = random.Random(5)
        m, S, A, S_star = random_instance(rng)
        x = pf.random_vec(rng)
        dm, dS = pf.pfg_moment_derivatives(m, S, A, S_star)
        wrong_dS = pf.mscale(2, dS)  # a factor-2 slip in the covariance equation
        self.assertNotEqual(
            pf.log_density_time_derivative(x, m, S, dm, wrong_dS),
            pf.continuity_rhs_over_density(x, m, S, A, S_star),
        )

    def test_kl_dissipation_identity(self):
        rng = random.Random(6)
        for _ in range(25):
            m, S, A, S_star = random_instance(rng)
            dm, dS = pf.pfg_moment_derivatives(m, S, A, S_star)
            diss = pf.kl_dissipation(m, S, A, S_star)
            self.assertGreaterEqual(diss, 0)
            self.assertEqual(pf.kl_time_derivative(m, S, dm, dS, S_star), -diss)

    def test_equilibrium(self):
        zero = [F(0), F(0)]
        for A in (pf.identity2(F(1)), S_STAR):
            dm, dS = pf.pfg_moment_derivatives(zero, S_STAR, A, S_STAR)
            self.assertEqual(dm, zero)
            self.assertEqual(dS, [[0, 0], [0, 0]])
            self.assertEqual(pf.kl_dissipation(zero, S_STAR, A, S_STAR), 0)
        self.assertAlmostEqual(pf.kl_gaussian(zero, S_STAR, S_STAR), 0.0, places=12)


class ClosedFormAndDecayTests(unittest.TestCase):
    def test_expm2(self):
        E = pf.expm2([[0.5, 0.0], [0.0, -2.0]])
        self.assertAlmostEqual(E[0][0], math.exp(0.5), places=12)
        self.assertAlmostEqual(E[1][1], math.exp(-2.0), places=12)
        self.assertAlmostEqual(E[0][1], 0.0, places=14)
        self.assertEqual(pf.expm2([[0.0, 0.0], [0.0, 0.0]]), [[1.0, 0.0], [0.0, 1.0]])
        R = pf.expm2([[0.0, -1.0], [1.0, 0.0]])  # rotation by one radian
        self.assertAlmostEqual(R[0][0], math.cos(1.0), places=12)
        self.assertAlmostEqual(R[1][0], math.sin(1.0), places=12)

    def test_rk4_matches_closed_form(self):
        for A in (pf.identity2(F(1)), S_STAR):
            path = pf.rk4_moments(M0, S0, A, S_STAR, 3.0, 600)
            t, m, S = path[-1]
            mc, Sc = pf.closed_form_moments(t, M0, S0, A, S_STAR)
            for a, b in zip(m, mc):
                self.assertAlmostEqual(a, b, delta=1e-8)
            for ra, rb in zip(S, Sc):
                for a, b in zip(ra, rb):
                    self.assertAlmostEqual(a, b, delta=1e-8)

    def test_preconditioned_closed_form(self):
        # With A = S*: m_t = e^{-t} m0 and S_t = S* + e^{-2t} (S0 - S*).
        t = 0.7
        m, S = pf.closed_form_moments(t, M0, S0, S_STAR, S_STAR)
        for a, b in zip(m, M0):
            self.assertAlmostEqual(a, math.exp(-t) * float(b), places=10)
        for i in range(2):
            for j in range(2):
                expected = float(S_STAR[i][j]) + math.exp(-2 * t) * float(S0[i][j] - S_STAR[i][j])
                self.assertAlmostEqual(S[i][j], expected, places=9)

    def test_rates(self):
        M_id = pf.mm(pf.identity2(F(1)), pf.inv2(S_STAR))
        self.assertEqual(pf.trace(M_id), F(101, 100))
        self.assertEqual(pf.det2(M_id), F(1, 100))
        self.assertEqual(pf.mm(S_STAR, pf.inv2(S_STAR)), pf.identity2(F(1)))

    def test_kl_decreases_and_preconditioning_is_faster(self):
        S_star_f = pf.to_float(S_STAR)
        for A in (pf.identity2(F(1)), S_STAR):
            kls = [
                pf.kl_gaussian(m, S, S_star_f)
                for _, m, S in pf.rk4_moments(M0, S0, A, S_STAR, 4.0, 400)
            ]
            self.assertTrue(all(b <= a + 1e-12 for a, b in zip(kls, kls[1:])))
        for t in (0.5, 1.0, 3.0, 8.0):
            kl_id = pf.kl_gaussian(
                *pf.closed_form_moments(t, M0, S0, pf.identity2(F(1)), S_STAR), S_star_f
            )
            kl_pre = pf.kl_gaussian(*pf.closed_form_moments(t, M0, S0, S_STAR, S_STAR), S_star_f)
            self.assertLess(kl_pre, kl_id)
        t_id = pf.time_to_kl(1e-3, M0, S0, pf.identity2(F(1)), S_STAR)
        t_pre = pf.time_to_kl(1e-3, M0, S0, S_STAR, S_STAR)
        self.assertLess(t_pre, 10.0)
        self.assertGreater(t_id, 100.0)


class FiniteFeatureTests(unittest.TestCase):
    @staticmethod
    def score(y):
        return pf.poly_eval(pf.SCORE_COEFFS, y)

    def test_kernel_derivative(self):
        # k(y, x) = 1 + x y is linear in y, so any difference quotient is the exact derivative.
        for x in (F(-2), F(1, 3), F(5)):
            for y in (F(-1), F(0), F(7, 2)):
                quotient = (pf.kernel(y + F(1, 10), x) - pf.kernel(y, x)) / F(1, 10)
                self.assertEqual(quotient, pf.kernel_dy(y, x))

    def test_svgd_direction_equals_feature_solution(self):
        W = pf.svgd_weights(pf.PARTICLES, self.score, pf.LAMBDA)
        for x in (F(-3), F(-1, 2), F(0), F(2, 9), F(4)):
            self.assertEqual(
                pf.svgd_direction(pf.PARTICLES, self.score, pf.LAMBDA, x), pf.dot(W, pf.psi(x))
            )

    def test_svgd_with_gaussian_score(self):
        particles = (F(-1), F(0), F(1, 2), F(3))
        lam = F(2)

        def gauss_score(y):
            return -(y - 1) / 2

        W = pf.svgd_weights(particles, gauss_score, lam)
        for x in (F(-1), F(1, 7)):
            self.assertEqual(
                pf.svgd_direction(particles, gauss_score, lam, x), pf.dot(W, pf.psi(x))
            )

    def test_completion_of_squares(self):
        rng = random.Random(8)
        W = pf.svgd_weights(pf.PARTICLES, self.score, pf.LAMBDA)
        Wp = pf.pfg_feature_weights(pf.PARTICLES, self.score)
        G = pf.empirical_gram(pf.PARTICLES)
        base = pf.svgd_objective(W, pf.PARTICLES, self.score, pf.LAMBDA)
        base_p = pf.pfg_feature_objective(Wp, pf.PARTICLES, self.score)
        for _ in range(20):
            d = pf.random_vec(rng)
            shifted = [a + b for a, b in zip(W, d)]
            gap = pf.svgd_objective(shifted, pf.PARTICLES, self.score, pf.LAMBDA) - base
            self.assertEqual(gap, pf.LAMBDA * pf.dot(d, d) / 2)
            shifted_p = [a + b for a, b in zip(Wp, d)]
            gap_p = pf.pfg_feature_objective(shifted_p, pf.PARTICLES, self.score) - base_p
            self.assertEqual(gap_p, pf.dot(d, pf.mv(G, d)) / 2)

    def test_rkhs_and_weighted_norms_differ(self):
        W = pf.svgd_weights(pf.PARTICLES, self.score, pf.LAMBDA)
        Wp = pf.pfg_feature_weights(pf.PARTICLES, self.score)
        self.assertNotEqual(W[0] * Wp[1] - W[1] * Wp[0], 0)

    def test_gaussian_projection(self):
        rng = random.Random(9)
        for _ in range(15):
            mean = F(rng.randint(-5, 5), rng.randint(1, 3))
            var = F(rng.randint(1, 7), rng.randint(1, 3))
            _, residual = pf.gaussian_pfg_projection(pf.SCORE_COEFFS, mean, var)
            self.assertEqual(residual, [0, 0])
            W, residual = pf.gaussian_pfg_projection((F(0), F(-1)), mean, var)
            self.assertEqual(residual, [0, 0])
            self.assertEqual(W, [-mean / var, -1 + 1 / var])


class ReportTests(unittest.TestCase):
    def test_all_checks_pass_and_main_succeeds(self):
        checks = pf.run_checks()
        self.assertEqual([c.name for c in checks if not c.ok], [])
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(pf.main(), 0)
        self.assertIn("not proofs", out.getvalue())


if __name__ == "__main__":
    unittest.main()
