"""Closed-form DDPM on Gaussian data N(m, diag(v)) (illustrations, not proofs).

Conventions of `FormalizeSampling/Samplers/DiffusionSetup.lean`: forward OU with
alpha_k = e^{-(t_k - t_{k-1})}, beta_k = 1 - alpha_k^2; the sampler starts at q_N = N(0, I) and
applies, for k = N, ..., 2, x <- (x + beta_k s_k(x)) / alpha_k + sigma_k xi. Its output is q_1,
compared with p_1, the data law smoothed to time t_1. With Gaussian data and the exact score
s_k(y) = -(y - m e^{-t_k}) / V_k every law stays Gaussian, so KL(p_1 || q_1) is exact.
"""

import numpy as np


def reverse_variance(rule: str, alpha: float, beta: float, abar_prev: float, abar: float):
    if rule == "ddpm":  # beta / alpha^2: the variance of the DF-1 bound (ddpmVar)
        return beta / alpha**2
    if rule == "beta":
        return beta
    if rule == "posterior":  # beta_tilde = beta (1 - abar_{k-1}) / (1 - abar_k)
        return beta * (1 - abar_prev) / (1 - abar)
    raise ValueError(rule)


def output_law(m, v, t, rule: str = "ddpm"):
    """Mean and variance (per coordinate) of q_1, and of p_1, for the exact-score sampler."""
    m = np.asarray(m, float)
    v = np.asarray(v, float)
    n = len(t) - 1
    mu = np.zeros_like(m)
    var = np.ones_like(v)
    for k in range(n, 1, -1):
        alpha = np.exp(-(t[k] - t[k - 1]))
        beta = -np.expm1(-2 * (t[k] - t[k - 1]))
        a = np.exp(-t[k])
        vk = v * a**2 + (1 - a**2)
        gain = (1 - beta / vk) / alpha
        shift = beta * m * a / (vk * alpha)
        s2 = reverse_variance(rule, alpha, beta, np.exp(-2 * t[k - 1]), np.exp(-2 * t[k]))
        mu = gain * mu + shift
        var = gain**2 * var + s2
    a1 = np.exp(-t[1])
    return mu, var, m * a1, v * a1**2 + (1 - a1**2)


def kl_gauss(mp, vp, mq, vq) -> float:
    """KL(N(mp, diag vp) || N(mq, diag vq))."""
    return float(np.sum(0.5 * (np.log(vq / vp) + (vp + (mp - mq) ** 2) / vq - 1)))


def exact_kl(m, v, t, rule: str = "ddpm") -> float:
    mq, vq, mp, vp = output_law(m, v, t, rule)
    return kl_gauss(mp, vp, mq, vq)


def lean_bound(m, v, delta: float, r: float, n_steps: int):
    """initBound_geomGrid + discretisation term of klDiv_output_le_geomGrid (zero score error)."""
    d = len(m)
    u1 = np.expm1(2 * delta)
    un = u1 * r ** (n_steps - 1)
    w = u1 / (1 + u1)
    m2 = float(np.sum(np.asarray(m) ** 2 + np.asarray(v)))
    init = (1 + u1) / (1 + un) * (d * (w - 1 - np.log(w)) + m2 / (1 + u1)) / 2
    disc = (r - 1) * d / 2 * (1 + (n_steps - 1) * np.log(r))
    return init, disc


def path_terms(m, v, t, rule: str = "ddpm"):
    """Per-step path-space terms D_k = E KL(R_k(y) || Q_k(y)) for k = N, ..., 2 (exact score).

    For Gaussian data the exact reverse kernel is R_k(y) = N(m*_k(y), tau_k) with the Tweedie mean
    m*_k (which is also the sampler's mean) and tau_k = beta_k V_{k-1} / V_k, so per coordinate
    D_k = (tau/sigma^2 - 1 - log(tau/sigma^2)) / 2, independent of y. Also returns
    KL(p_N || N(0, I)). Path KL = KL(p_N || N(0, I)) + sum_k D_k (chain rule).
    """
    v = np.asarray(v, float)
    m = np.asarray(m, float)
    n = len(t) - 1
    out = []
    for k in range(n, 1, -1):
        alpha = np.exp(-(t[k] - t[k - 1]))
        beta = -np.expm1(-2 * (t[k] - t[k - 1]))
        a_prev, a = np.exp(-t[k - 1]), np.exp(-t[k])
        v_prev = v * a_prev**2 + (1 - a_prev**2)
        vk = v * a**2 + (1 - a**2)
        tau = beta * v_prev / vk
        s2 = reverse_variance(rule, alpha, beta, a_prev**2, a**2)
        q = tau / s2
        out.append(float(np.sum(0.5 * (q - 1 - np.log(q)))))
    a_n = np.exp(-t[n])
    init = kl_gauss(m * a_n, v * a_n**2 + (1 - a_n**2), np.zeros_like(m), np.ones_like(v))
    return np.array(out), init


def kappa_grid(delta: float, horizon: float, kappa: float, tail: bool = False) -> np.ndarray:
    """Geometric grid u_k = u_1 (1 + kappa)^{k-1} from t_1 = delta up to t_N = horizon.

    With tail=True the geometric part stops once u >= 1/kappa (t ~ log(1/kappa)/2) and the
    remaining stretch up to `horizon` is covered by ONE long final step.
    """
    u_end = np.expm1(2 * horizon)
    u_stop = min(u_end, 1 / kappa) if tail else u_end
    u = [np.expm1(2 * delta)]
    while u[-1] * (1 + kappa) < u_stop:
        u.append(u[-1] * (1 + kappa))
    u.append(u_end)
    return np.concatenate([[0.0], 0.5 * np.log1p(np.array(u))])
