# Glossary and conventions

This page fixes the vocabulary used by the Lean library, the registry and the literature it
formalises.
When two notions below differ, the library names the one each theorem proves.

## Scores

| Term | Meaning | In Lean |
| --- | --- | --- |
| State (spatial) score | $`\nabla_x \log p(x)`$ of a density $`p`$ on the state space | `FormalizeSampling.score`, `FormalizeSampling.score1` |
| Parameter (policy) score | $`\nabla_\theta \log \pi_\theta(y)`$ of a parametric family | not used here |
| Target score | $`s_\star = \nabla \log p_\star`$ of the sampling target, supplied as a vector field | an explicit field argument such as `sStar` |
| Noise | the Gaussian variable $`Z`$ in $`Y = X + \sigma Z`$ | a random variable or a Gaussian law, never a score |

`score p x` is `grad (fun y => Real.log (p y)) x`. Where $`p`$ is positive and differentiable it
equals $`\nabla p(x) / p(x)`$ (`score_apply_of_pos`). An atomic (particle) measure has no Lebesgue
density and therefore no state score (CE-05).

## Five different notions of "the same dynamics"

1. **Pointwise generator equality**: $`L\varphi(x) = L'\varphi(x)`$ for every $`x`$. Langevin and
   its probability flow do **not** satisfy this (see the pointwise counterexample in
   `Identities/ScoreFlowWeak.lean`).
2. **Weak (expectation-level) equality at a fixed time**:
   $`\int L\varphi \, p = \int L'\varphi \, p`$ for test functions $`\varphi`$ under the *current*
   density $`p`$. No process is constructed.
3. **One-time marginal law equality**: $`\mathrm{Law}(X_t) = \mathrm{Law}(Y_t)`$ for each $`t`$.
   In general this needs well-posedness and uniqueness of the weak Fokker–Planck /
   continuity equation; the Gaussian/OU example discharges it by explicit computation.
4. **Finite-dimensional law equality**: equality of every joint law
   $`\mathrm{Law}(X_{t_1}, \ldots, X_{t_k})`$. Equal one-time marginals do not imply it (CE-01).
5. **Path-law equality**: equality of the laws on path space. Implies (4), which implies (3).

The statement "noise ≡ score in distribution" is shorthand for (2) and, under uniqueness, (3).
It never means that the noise and score *random variables* coincide (CE-02).

## Distances and divergences

| Term | Normalisation |
| --- | --- |
| Total variation $`\mathrm{TV}(\mu, \nu)`$ | $`\sup_A \lvert \mu(A) - \nu(A) \rvert`$ over measurable $`A`$ (`FormalizeSampling.TotalVariation.tvSup`); for probability measures this is half of Mathlib's `MeasureTheory.tvDist`, and on a finite space it equals $`\tfrac{1}{2} \sum_x \lvert \mu(x) - \nu(x) \rvert`$ |
| KL divergence $`\mathrm{KL}(p \Vert p_\star)`$ | $`\int p \log(p / p_\star)`$; Mathlib's `InformationTheory.klDiv` for measures |
| $`H`$-weighted norm | $`\Vert u \Vert_H^2 = u^\top H u`$ (`FormalizeSampling.sqNormH`) for a symmetric positive-definite $`H`$ |
| Relative Fisher information | $`\int \Vert \nabla \log(p / p_\star) \Vert^2 \, p`$ (with a matrix weight when preconditioned) |

## Gaussian and diffusion conventions

- Mathlib's `gaussianReal m v` is $`\mathcal{N}(m, v)`$ with **variance** `v : ℝ≥0`;
  `gaussianPDFReal m v` is its Lebesgue density. $`\sigma`$ always denotes a standard deviation,
  $`\sigma^2`$ a variance.
- Overdamped Langevin with preconditioner $`A`$:
  $`dX = A \nabla \log p_\star(X) \, dt + \sqrt{2A} \, dW`$. Its generator is
  $`L\varphi = (A \nabla \log p_\star) \cdot \nabla \varphi + \sum_{ij} A_{ij} \partial_i \partial_j \varphi`$
  (`weightedLaplacian`).
- Ornstein–Uhlenbeck with unit stationary variance and rate $`a`$:
  $`X_t \mid X_0 = x \sim \mathcal{N}(e^{-at} x, 1 - e^{-2at})`$ (Mehler form). With $`a = 1`$ this
  is the convention $`a_t = e^{-t}`$, $`\sigma_t^2 = 1 - e^{-2t}`$ of reverse diffusion Monte Carlo
  (rdMC; Huang–Dong–Hao–Ma–Zhang, 2024).
- Unadjusted Langevin step for $`\mathcal{N}(0, 1)`$ with step $`h`$:
  $`X' = (1 - h)X + \sqrt{2h} \, Z`$.
- Reverse time: $`s = T - t`$, $`q(s, x) = p(T - s, x)`$; the reverse drift is
  $`-b + g^2 \nabla \log p`$ for scalar diffusion $`g(t)`$.

## Statuses

| Status | Meaning |
| --- | --- |
| Verified | Proved in Lean; hypotheses are explicit, satisfiable regularity or modelling assumptions that do not encode the main step |
| Conditional | Proved in Lean from a named hypothesis that packages unproved mathematics (PDE uniqueness, Fokker–Planck for an SDE, a log-Sobolev inequality, an oracle error bound) |
| Counterexample | A Lean-verified refutation of a tempting claim |
| Planned | Statement and assumptions written down; no Lean proof yet |
| Open | Research question without a fixed formal statement |
