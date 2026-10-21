# Python illustrations and exact arithmetic checks

> **These scripts are illustrations and exact arithmetic checks, never proofs.** A passing
> check here is evidence that a formula, a sign or a constant is written down correctly in a
> particular instance. It does not prove the general statement, it does not discharge any
> hypothesis of a Lean theorem, and it never changes the status of an entry in
> `docs/theorem_registry.md`. The Lean library `FormalizeSampling/` is the only source of
> verified results.

Everything uses the Python standard library only (`fractions.Fraction`, `math`,
`statistics`, `random.Random(seed)`); no numpy or scipy. Every computation is deterministic,
and the whole test suite runs in a few seconds.

```bash
# from the repository root
python3 -m experiments.exact_gaussian
python3 -m experiments.gaussian_mixtures
python3 -m experiments.sampling_vs_score_flow
python3 -m experiments.kernel_tv_checks
python3 -m experiments.pfg_gaussian_flow
python3 -m unittest discover -s tests -v
```

Each script's `main()` prints one line per check, `[ok  ]` or `[FAIL]`, with the numbers behind
it, and exits with status 0 only when every check passes. `run_checks()` returns the same
checks as `Check(name, ok, detail)` records, and `tests/` asserts on them and on the
individual functions.

## Three kinds of check

| Kind | Arithmetic | What a pass means |
|---|---|---|
| Exact | `Fraction`; equality is `==` on rationals | the identity holds *exactly* at the rational instances tried |
| Numerical | floats: quadrature, finite differences, Euler/RK4, matrix exponential | agreement within a stated tolerance, chosen from the method's error order |
| Monte Carlo | floats with a fixed seed | agreement within 5 (approximate) standard errors for that seed |

Exact checks still only cover finitely many instances. Numerical and Monte Carlo checks can
also pass for the wrong reason if a tolerance is loose; the tests include a few *negative*
controls (a factor-2 slip in a covariance equation, dividing by $`\sigma`$ instead of $`\sigma^2`$,
dropping a variance factor or the Hastings ratio) to show that the checks can fail.

## Conventions

$`\mathcal{N}(m, v)`$ takes the **variance** $`v`$; TV is $`\sup_A \lvert \mu(A) - \nu(A) \rvert`$,
which equals $`\tfrac{1}{2} \sum_x \lvert \mu(x) - \nu(x) \rvert`$ on finite spaces (both are
computed and compared); scores are state scores $`\nabla_x \log p`$; and one-time marginal
equality, two-time (finite-dimensional) law equality and path-law equality are kept apart. PFG
is the preconditioned functional gradient flow of Dong–Wang–Lin–Zhang (2023).

## What each script illustrates

IDs are those of `docs/theorem_registry.md`, which gives the exact Lean statements and their
hypotheses. A listed module may prove a narrower or differently stated result than the
instance checked here.

| Script | Illustrates | IDs | Lean counterpart |
|---|---|---|---|
| `exact_gaussian.py` | ULA one-step bias and stationary variance; SGLD stationary variance; OU and PFG Gaussian moments; Gaussian Stein identity | CE-03, EX-1, ID-1, ID-2, CE-04 | `Counterexamples/ULADiscretization.lean`, `Kernels/GaussianKernels.lean`, `Examples/GaussianFlowVsOU.lean`, `Identities/GaussianStein.lean`, `Identities/DensityStein.lean`, `Counterexamples/SteinSingleTest.lean` |
| `gaussian_mixtures.py` | Tweedie's identity (mean and noise forms) for Gaussian mixtures and atomic priors; zero-mean score; OU posterior score; noise is not the score | SE-3, ID-2, CE-02 | `Identities/Tweedie.lean`, `Identities/OUPosteriorScore.lean`, `Identities/DensityStein.lean`, `Counterexamples/ScoreNotNoise.lean` |
| `sampling_vs_score_flow.py` | OU sampling and the deterministic PFG flow from the same samples: equal one-time marginals, different two-time laws | EX-1, FL-5, CE-01 | `Examples/GaussianFlowVsOU.lean`, `Kernels/GaussianKernels.lean`, `Counterexamples/MarginalsNotPaths.lean`, `Identities/ScoreFlowWeak.lean` |
| `kernel_tv_checks.py` | TV normalisation; TV contraction and Dobrushin coefficient; telescoping uniform and law-averaged bounds; Metropolis–Hastings detailed balance and invariance | KL-1, KR-1, MH-1 | `Foundations/TotalVariation.lean`, `Kernels/ErrorPropagation.lean`, `Samplers/MetropolisHastings.lean` |
| `pfg_gaussian_flow.py` | d = 2 Gaussian PFG moment dynamics, continuity equation, KL dissipation, preconditioned vs unpreconditioned KL decay; finite-feature SVGD vs PFG weighted norm | SE-1, SE-2, ID-3, FL-1, FL-2, FL-4, FL-5 | `ScoreEstimation/FeatureClass.lean`, `Foundations/SPDPreconditioner.lean`, `Identities/ScoreFlowWeak.lean`, `Identities/KLTransportVariation.lean`, `Flow/KLDecay.lean`, `Flow/ContinuityEquation.lean`; the scalar case of the moment dynamics is `Examples/GaussianFlowVsOU.lean` |

### `exact_gaussian.py`

Target $`\mathcal{N}(0, 1)`$ with $`U(x) = x^2/2`$.

* **CE-03, exact.** One ULA step $`X' = (1 - h) X + \sqrt{2h} \, \xi`$ from $`\mathcal{N}(0, 1)`$
  has variance $`(1 - h)^2 + 2h = 1 + h^2 \ne 1`$ for every $`h \gt 0`$. The variance recursion
  $`v \mapsto (1 - h)^2 v + 2h`$ has fixed point $`2/(2 - h) \gt 1`$ for $`0 \lt h \lt 2`$, and
  $`v_n - v_* = (1 - h)^{2n} (v_0 - v_*)`$ exactly.
* **SGLD, exact.** Toy model with additive gradient noise: $`\nabla U(x) = x`$ is replaced by
  $`x + \tau \zeta`$, $`\zeta \sim \mathcal{N}(0, 1)`$ independent. The stationary variance is
  $`(2 + h \tau^2)/(2 - h)`$ and reduces to ULA at $`\tau = 0`$. This is the idealised SGLD noise
  model, not minibatch gradient noise and not a specific paper's algorithm.
* **OU and PFG moments.** $`dX = -aX \, dt + \sqrt{2a} \, dW`$ and the PFG / probability-flow ODE
  $`y' = a(-y + (y - m_t)/v_t)`$ both have Gaussian marginals with $`m_t = e^{-at} m_0`$,
  $`v_t = 1 + (v_0 - 1) e^{-2at}`$. Exact: at rational $`(m, v, a)`$ both dynamics induce
  $`m' = -am`$, $`v' = 2a(1 - v)`$. Numerical: the exact flow map sends the quantiles of
  $`\mathcal{N}(m_0, v_0)`$ to the quantiles of $`\mathcal{N}(m_t, v_t)`$ (error about `1e-15`), and
  explicit Euler integration of the particle ODE from those quantiles converges to them at first
  order (error halves when $`dt`$ halves).
* **ID-1, exact.** $`\mathbb{E}[Z \varphi(Z)] = \mathbb{E}[\varphi'(Z)]`$ for random rational
  polynomials via $`\mathbb{E} Z^{2k} = (2k - 1)!!`$, and
  $`\mathbb{E}[(X - \mu) \varphi(X)] = s^2 \, \mathbb{E}[\varphi'(X)]`$ for
  $`X \sim \mathcal{N}(\mu, s^2)`$. Polynomials only: this says nothing about the regularity and
  integrability conditions of the general identity.
* **CE-04, exact.** A Rademacher variable passes the Stein test for $`\varphi(z) = z`$ ($`1 = 1`$)
  but fails it for $`\varphi(z) = z^3`$ ($`1 \ne 3`$).

### `gaussian_mixtures.py`

$`Y = X + \sigma Z`$ with $`X \sim \sum_k w_k \mathcal{N}(m_k, s_k^2)`$ (atoms allowed:
$`s_k = 0`$), so $`p_\sigma = \sum_k w_k \mathcal{N}(m_k, s_k^2 + \sigma^2)`$.

* The closed-form convolution and the conjugate posterior mean are checked against Simpson
  quadrature of $`\int \mathrm{prior}(x) \, \mathcal{N}(y; x, \sigma^2) \, dx`$ and of Bayes'
  formula.
* **SE-3 (Tweedie), numerical.** A five-point finite difference of $`\log p_\sigma`$ equals
  $`(\mathbb{E}[X \mid Y = y] - y)/\sigma^2`$ and $`-\mathbb{E}[Z \mid Y = y]/\sigma`$ (the latter
  computed by a separate per-component regression of $`Z`$ on $`Y`$) to within `1e-9`, on a grid
  of $`y`$ and $`\sigma \in \{0.3, 1, 2\}`$.
* **Atomic prior.** For $`X \sim \sum_k w_k \delta_{a_k}`$ Tweedie still holds although $`X`$ has
  no Lebesgue density: only $`Y`$ needs one.
* **ID-2.** $`\mathbb{E}[\mathrm{score}(Y)] = \int p_\sigma' = 0`$ by quadrature.
* **SE-3 (OU posterior score).** For $`X_t = e^{-t} X_0 + \sqrt{1 - e^{-2t}} \, Z`$ the score is
  $`(a_t \mathbb{E}[X_0 \mid X_t = y] - y)/\sigma_t^2`$ (Lemma 1 of reverse diffusion Monte Carlo,
  Huang–Dong–Hao–Ma–Zhang 2024), computed as an affine corollary of the Tweedie code (rescale
  $`X_t = a_t (X_0 + (\sigma_t/a_t) Z)`$).
* **CE-02.** $`\mathrm{Var}(Z \mid Y = y) \gt 0`$ (for a Gaussian prior it is
  $`s^2/(s^2 + \sigma^2)`$): the noise is not a function of $`Y`$; only its conditional mean is
  the rescaled score.

### `sampling_vs_score_flow.py`

From the same seeded samples $`X_0 \sim \mathcal{N}(2, 1/4)`$: OU with exact Mehler transitions
$`X_{t+dt} = e^{-a \, dt} X_t + \sqrt{1 - e^{-2a \, dt}} \, \xi`$ and the PFG flow map
$`y_0 \mapsto m_t + \sqrt{v_t/v_0} \, (y_0 - m_0)`$, at $`t \in \{0.25, 0.5, 1, 2\}`$.

* **One-time marginals agree** (Monte Carlo): sample means and variances of both clouds match
  $`\mathcal{N}(m_t, v_t)`$ within 5 standard errors.
* **Two-time laws differ** (CE-01): $`\mathrm{corr}(X_0, X_t) = e^{-at} \sqrt{v_0/v_t} \lt 1`$ for
  OU (Monte Carlo, within 5 standard errors) versus $`\mathrm{corr} = 1`$ for the increasing
  affine flow map; exactly,
  $`\mathrm{Cov}_{\mathrm{flow}} - \mathrm{Cov}_{\mathrm{OU}} = \sqrt{v_0 v_t} - e^{-at} v_0 \gt 0`$
  for $`t \gt 0`$ because $`v_t - e^{-2at} v_0 = 1 - e^{-2at} \gt 0`$. Mean-square displacements
  $`\mathbb{E}(X_t - X_0)^2`$ differ too.

This is the Gaussian case only; equality of marginals for general targets needs the PDE
uniqueness hypothesis of FL-5, which no simulation can supply.

### `kernel_tv_checks.py`

Random stochastic matrices with `Fraction` entries (seeded), all comparisons exact.

* $`\mathrm{TV} = \sup_A \lvert \mu(A) - \nu(A) \rvert`$ (all subsets enumerated) equals
  $`\tfrac{1}{2} L^1`$.
* **KR-1 (contraction).**
  $`\mathrm{TV}(\mu P, \nu P) \le \delta(P) \, \mathrm{TV}(\mu, \nu) \le \mathrm{TV}(\mu, \nu)`$
  with the Dobrushin coefficient
  $`\delta(P) = \max_{x, x'} \mathrm{TV}(P(x, \cdot), P(x', \cdot))`$.
* **KR-1 (telescoping).** With exact kernels $`P_k`$, inexact $`Q_k`$,
  $`\mu_k = \mu_0 P_1 \cdots P_k`$, $`\nu_k = \mu_0 Q_1 \cdots Q_k`$:
  $`\mathrm{TV}(\mu_K, \nu_K) \le \sum_k \mathrm{TV}(\mu_{k-1} P_k, \mu_{k-1} Q_k)`$
  $`\le \sum_k \mathbb{E}_{\mu_{k-1}} \mathrm{TV}(P_k(x, \cdot), Q_k(x, \cdot))`$
  $`\le \sum_k \max_x \mathrm{TV}(P_k(x, \cdot), Q_k(x, \cdot))`$, and the law-averaged bound
  under the inexact laws $`\nu_{k-1}`$ holds as well. A hand-made example (identity kernel, error
  localised on a state of mass 1/100) gives final TV $`1/100`$, law-averaged bounds $`1/100`$
  (inexact law) and $`1/10`$ (exact law), and uniform bound $`10`$.
* **MH-1.** Metropolis ($`\min(1, r)`$) and Barker ($`r/(1 + r)`$) acceptance with the Hastings
  ratio $`r = \pi(y) q(y, x)/(\pi(x) q(x, y))`$ give exact detailed balance and $`\pi K = \pi`$
  for random positive targets and asymmetric proposals with symmetric support;
  $`\mathrm{TV}(\mu K^n, \pi) \le \delta(K)^n \, \mathrm{TV}(\mu, \pi)`$. Dropping the Hastings
  ratio for an asymmetric proposal breaks invariance ($`\pi = (1/2, 1/2)`$,
  $`\pi K = (3/8, 5/8)`$).

### `pfg_gaussian_flow.py`

**Part 1: d = 2 Gaussian PFG.** Target $`\mathcal{N}(0, S_*)`$ with $`S_*`$ having eigenvalues 100
along $`(1, 1)`$ and 1 along $`(1, -1)`$; particle law $`\mathcal{N}(m, S)`$; constant SPD
$`A = H^{-1}`$. The PFG velocity
$`v(x) = A(\nabla \log p_*(x) - \nabla \log p(x)) = AGx - AS^{-1} m`$, with
$`G = S^{-1} - S_*^{-1}`$, is affine, so the Gaussian family is preserved with

```math
\begin{aligned}
m' &= -A S_*^{-1} m,
\\ S' &= A (S^{-1} - S_*^{-1}) S + S (S^{-1} - S_*^{-1}) A = 2A - MS - SM^\top, \qquad M = A S_*^{-1}.
\end{aligned}
```

The second form is the Lyapunov equation of preconditioned Langevin
$`dX = -A S_*^{-1} X \, dt + \sqrt{2A} \, dW`$. Exact checks at random rational $`(m, S, A, S_*)`$:
both forms agree; $`(m', S')`$ read off from the velocity function itself ($`v(x) = Bx + c`$,
$`m' = Bm + c`$, $`S' = BS + SB^\top`$) agree with the formulas; the Gaussian $`p_t`$ solves the
continuity equation $`\tfrac{d}{dt} \log p = -\mathrm{div}(pv)/p`$ pointwise; and
$`\tfrac{d}{dt} \mathrm{KL}(p_t \Vert p_*) = -\mathbb{E}_p[(\nabla \log(p/p_*))^\top A \, \nabla \log(p/p_*)] \le 0`$
(FL-2 in this Gaussian case; both sides are rational). Numerically, RK4 matches the closed form
$`m_t = e^{-tM} m_0`$, $`S_t = S_* + e^{-tM} (S_0 - S_*) e^{-tM^\top}`$, and KL decays
monotonically.

*Preconditioning.* $`M = A S_*^{-1}`$ has spectrum $`\{1/100, 1\}`$ for $`A = I`$ and
$`\{1, 1\}`$ (indeed $`M = I`$) for $`A = S_*`$; both have fastest rate 1, so the comparison is
not a time rescaling. From $`m_0 = (4, 1)`$, $`S_0 = I`$ (KL about 4.12), KL reaches `1e-3` at
$`t`$ about 210 for $`A = I`$ and about 3.9 for $`A = S_*`$.

**Part 2: finite-feature SVGD in 1D** (SVGD as a regularised functional gradient, as in
Dong–Wang–Lin–Zhang 2023, §3.2.1). Features $`\psi(x) = (1, x)`$, kernel $`k(x, y) = 1 + xy`$,
fixed rational particles, double-well score $`s(x) = x - x^3`$. Exact checks:
$`W^* = \frac{1}{\lambda n} \sum_j [s(y_j) \psi(y_j) + \psi'(y_j)]`$ minimises
$`-\frac{1}{n} \sum_j [f_W'(y_j) + f_W(y_j) s(y_j)] + \frac{\lambda}{2} \Vert W \Vert^2`$
(completion of squares), and
$`W^* \cdot \psi(x) = \frac{1}{\lambda n} \sum_j [k(y_j, x) s(y_j) + \tfrac{d}{dy} k(y, x) \big\vert_{y = y_j}]`$,
the SVGD direction. Replacing the fixed RKHS norm by PFG's distribution-weighted norm
$`\frac{1}{2} \cdot \frac{1}{n} \sum_j f_W(y_j)^2`$ gives the normal equations $`WG = b`$ and a
different (non-parallel) direction. For a Gaussian particle law $`\mathcal{N}(m, v)`$ (exact
moments), the weighted-norm solution is the $`L^2(p)`$ projection of $`s - \nabla \log p`$ onto
$`\mathrm{span} \, \psi`$; for the target $`\mathcal{N}(0, 1)`$ it recovers the exact PFG velocity
$`-x + (x - m)/v`$.

## What these scripts do not do

* They do not test well-posedness or uniqueness of any SDE, ODE or PDE; the Gaussian closed
  forms sidestep those questions.
* They do not cover finite-particle effects beyond fixed particle sets, nonlinear function
  classes, stochastic optimisation, or any quantitative convergence rate beyond the explicit
  Gaussian formulas.
* Agreement on the instances tried is not a proof of the general identity. Each Lean
  counterpart states its own hypotheses and scope.
