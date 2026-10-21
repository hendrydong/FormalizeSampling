# FormalizeSampling: blueprint

This document is the specification of the library: its scope, the organising picture, the
layout and the list of core theorems. The authoritative status of each theorem, with Lean
declaration names, is in [`theorem_registry.md`](theorem_registry.md).

## 1. Scope

The library formalises **general sampling algorithms and the theorems that carry their
analysis**, not individual papers. A result belongs here only if it is stated for a general
algorithm class (any drift, any target, any kernel), or is a counterexample that delimits such a
statement. Specific published algorithms appear, if at all, as short examples.

The analytic identities (Stein, Tweedie, weak generators) are standard. The delicate part of a
sampling analysis is the assembly of standard tools: KL direction, TV normalisation, the law
under which an error is averaged, probability quantifiers, the object that is output, and
side hypotheses such as $`\nabla f(0) = 0`$. The library makes those choices explicit in the
statements of a small number of general theorems.

## 2. The organising picture

The target is a probability density $`\pi \propto e^{-U}`$ on `Fin d → ℝ`. The common
continuous-time object is the KL gradient flow,
$`\partial_t \rho = \mathrm{div}(\rho A \nabla \log(\rho/\pi))`$ for a constant SPD matrix $`A`$. It
has two implementations.

| Layer | Stochastic implementation | Deterministic implementation |
|---|---|---|
| population flow | Langevin $`dX = A \nabla \log \pi \, dt + \sqrt{2A} \, dW`$ | transport $`\dot{Y} = A(\nabla \log \pi - \nabla \log \rho_t)(Y)`$ (probability flow, preconditioned functional gradient flow (PFG; Dong–Wang–Lin–Zhang, 2023), SVGD) |
| equivalence | same weak evolution; same one-time marginals under uniqueness; different path laws | (same) |
| approximation error | drift / score error of a Gaussian-increment chain | velocity error in $`L^2(\rho_t)`$ |
| where the score comes from | denoising / Tweedie for noised laws | Stein / Hyvärinen objective, feature classes, kernel smoothing |
| discretisation | Gaussian-increment (Euler–Maruyama) kernels | push-forward by $`\mathrm{id} + \eta v`$; stable step depends on the current law |
| exact correction | Metropolis–Hastings; proximal (Gibbs) sampler | — |
| particles | — | empirical measures have no score; empirical objectives can be unbounded |

## 3. Library layout

| Directory | Contents |
|---|---|
| `Foundations/` | vector calculus and scores; SPD weighted norms; TV and its bridge to Mathlib's normalisation; KL tools (Pinsker, chain rule, lower semicontinuity, tensorisation) and Gaussian KL formulas; Gibbs measures $`\pi \propto e^{-f}`$; heat kernels on `ℝ` and `Fin d → ℝ`; heat flow (de Bruijn, Gaussian LSI along the flow); functional log-Sobolev inequalities, Bakry–Émery, Holley–Stroock, Prékopa–Leindler; Grönwall; mollifiers and weak derivatives; the bridge to Mathlib's `EuclideanSpace ℝ (Fin d)` |
| `Identities/` | Stein identities; Tweedie and posterior scores; weak generator identities; KL first variation |
| `Flow/` | continuity and Fokker–Planck equations (existence, uniqueness, DiPerna–Lions); KL dissipation for exact and approximate velocities; LSI decay with error; OU flows; noise–score marginal equivalence; reverse time; deterministic steps |
| `ScoreEstimation/` | Stein/Hyvärinen objective and its minimiser; linear feature classes (SVGD as a case); Monte Carlo posterior-mean estimators; bias of inexact inner samplers |
| `Kernels/` | TV propagation (per-step errors in TV or KL) and error decomposition for inexact kernels; exact reverse (Bayes) kernels; Gaussian and OU kernels; finite products of kernels |
| `Samplers/` | Gaussian-increment chains (ULA/EM); random score oracles; Metropolis–Hastings and MALA; the proximal sampler (heat-flow and backward analysis; also on `EuclideanSpace ℝ (Fin d)`); diffusion models (DDPM/DDIM); particle push-forwards and Euler steps |
| `Examples/` | closed-form Gaussian instances (OU vs. deterministic flow, discrete Gaussian flow, noise–score equivalence for OU) and tightness examples |
| `Counterexamples/` | refutations of tempting general claims |
| `Audit/` | statement audit: Lean witnesses for every registry row ([`statement_audit.md`](statement_audit.md)) |

A module imports only modules of its own or a lower layer: `Foundations` < `Identities`,
`Kernels` < `Flow`, `ScoreEstimation` < `Samplers` < `Examples`, `Counterexamples` < `Audit`
(checked by `scripts/check_contracts.py`). `FormalizeSampling.Core` imports the three lowest
layers, which contain no sampler.

## 4. Core theorems

Status values are defined in the [README](../README.md#statuses). The authoritative
per-theorem status, with Lean declarations, is [`theorem_registry.md`](theorem_registry.md).

### Foundations
- **KL-1 Pinsker.** `tvSup μ ν` $`\le \sqrt{\mathrm{KL}(\mu \Vert \nu)/2}`$ for probability
  measures; bridge to Mathlib's $`L^1`$ normalisation. *Verified.*
- **KL-2 Chain rule for kernels.**
  $`\mathrm{KL}(\mu \otimes_m \kappa \Vert \nu \otimes_m \eta) = \mathrm{KL}(\mu \Vert \nu) + \int \mathrm{KL}(\kappa(x) \Vert \eta(x)) \, d\mu(x)`$,
  and data processing
  $`\mathrm{KL}(\kappa \circ_m \mu \Vert \kappa \circ_m \nu) \le \mathrm{KL}(\mu \Vert \nu)`$.
  *Verified (chain rule ported from the LeanMachineLearning library, LML).*
- **KL-3 Gaussian KL.**
  $`\mathrm{KL}(\mathcal{N}(m_1, v) \Vert \mathcal{N}(m_2, v)) = (m_1 - m_2)^2/(2v)`$, isotropic
  $`d`$-dimensional form. *Verified.*
- **KL-4 Tensorisation.**
  $`\mathrm{KL}(\bigotimes_i \mu_i \Vert \bigotimes_i \nu_i) = \sum_i \mathrm{KL}(\mu_i \Vert \nu_i)`$
  for finitely many probability measures. *Verified.*
- **KL-5 Gaussian log-Sobolev inequality.**
  $`\mathrm{KL}(\rho \Vert \mathcal{N}(0, vI)) \le (v/2) \, I(\rho \Vert \mathcal{N}(0, vI))`$,
  along the heat flow for every $`\rho`$ with finite second moment and at time 0 for differentiable
  positive densities with finite second moment and Fisher information, via de Bruijn and
  Fisher-information decay. *Verified (1D and `Fin d → ℝ`).*
- **KL-6 Functional log-Sobolev inequalities.** Entropy chain rule, tensorization, stability under
  convolution, Gross's inequality; hence
  $`\mathrm{LSI}(\pi, C) \Rightarrow \mathrm{LSI}(\pi * \mathcal{N}(0, t), C + t)`$. Extension to
  unbounded positive test functions; Holley–Stroock perturbation. *Verified (1D and `Fin d → ℝ`).*
  Bakry–Émery ($`f - \alpha \lvert x \rvert^2/2`$ convex ⇒ LSI with constant $`1/\alpha`$) via the
  1D Caffarelli contraction, and on `Fin d → ℝ` via Prékopa–Leindler (Bobkov–Ledoux). *Verified (1D
  and `Fin d → ℝ`).*

### Identities
- **ID-1 Gaussian Stein identity.**
  $`\mathbb{E}[(X - m) \varphi(X)] = v \, \mathbb{E}[\varphi'(X)]`$ for
  $`X \sim \mathcal{N}(m, v)`$; $`d`$-dimensional standard form. *Verified.*
- **ID-2 Density Stein identity and zero-mean score.**
  $`\int (\mathrm{div}\, f) \, p = -\int f \cdot \nabla \log p \cdot p`$;
  $`\int \nabla \log p \cdot p = 0`$. *Verified.*
- **ID-3 Weak generator identity.**
  $`\int (b \cdot \nabla \varphi + \sum_{i,j} A_{ij} \partial_i \partial_j \varphi) \, p = \int (b - A^\top \nabla \log p) \cdot \nabla \varphi \, p`$.
  *Verified.*
- **ID-4 Reverse-time Fokker–Planck rewriting.** Strong-form reverse drift and probability-flow velocity. *Verified.*

### Flow
- **FL-1 First variation.**
  $`\frac{d}{dt} \mathrm{KL}(\rho_t \Vert \pi) = \int v_t \cdot \nabla \log(\rho_t/\pi) \, d\rho_t`$
  under the continuity equation. *Verified.*
- **FL-2 Exact dissipation.** For $`v = A \nabla \log(\pi/\rho)`$:
  $`\frac{d}{dt} \mathrm{KL} = -\int \Vert \nabla \log(\rho/\pi) \Vert_A^2 \, d\rho`$. *Verified;
  this is the computation in the proof of Theorem 1 of PFG (Dong–Wang–Lin–Zhang, 2023, App. A.5)
  at the exact velocity.*
- **FL-3 Approximate velocity.** (a) relative error
  $`\Vert g - v_\star \Vert^2 \le \varepsilon \Vert v_\star \Vert^2`$ ⇒ rate
  $`\le -(1 - \sqrt{\varepsilon}) \, I_A`$; (b) absolute error ⇒
  $`\le -\tfrac{1}{2} I_A + \tfrac{1}{2} \int \Vert g - v_\star \Vert_{A^{-1}}^2 \, d\rho`$ (the
  bound in the proof of Theorem 1 of PFG); (c) $`g`$ a projection onto a scale-closed class ⇒
  $`= -\int \Vert g \Vert_{A^{-1}}^2 \, d\rho`$.
  *Verified; (a) is sharp, with equality for $`g = (1 - \sqrt{\varepsilon}) \, v_\star`$.*
- **FL-4 Decay.** LSI along the flow plus FL-2/FL-3 ⇒ exponential KL decay with an additive
  integrated error term. Under PFG's assumptions [A3] (relative velocity error) and [A4] (LSI)
  the decay is Theorem 1 of PFG (Dong–Wang–Lin–Zhang, 2023), with its constants. *Conditional
  (LSI); the Grönwall-with-source step is verified; for Gaussian targets the LSI along the flow is
  proved (KL-5). For the Langevin (OU) flow with Gaussian target $`\pi = \mathcal{N}(0, vI)`$,
  $`\mathrm{KL}(\rho_t \Vert \pi) \le e^{-2at} \, \mathrm{KL}(\rho_0 \Vert \pi)`$ is verified for
  every $`\rho_0`$ with finite KL and second moment, with equality for
  $`\rho_0 = \mathcal{N}(m, vI)`$ (1D and `Fin d → ℝ`); along its deterministic probability flow the
  continuity equation, density regularity and the KL derivative are proved for $`t \gt 0`$, and the
  FL-1/FL-2 regularity bundle for $`\rho_0`$ with bounded support and, more generally, a finite
  fourth moment (sharp on the polynomial moment scale).*
- **FL-5 Noise–score equivalence.** Weak generator identity; one-time marginal equality given two
  named hypotheses (the law curve solves weak Fokker–Planck, the Itô input; uniqueness for the
  continuity equation); different two-time laws. *Conditional; uniqueness is verified for velocities
  jointly continuous, locally Lipschitz in $`x`$ uniformly on each $`[0, T]`$, with linear growth
  (mollification and approximate duality), weak Fokker–Planck is verified for heat/OU law curves, so
  OU with an isotropic Gaussian initial law is unconditional; for drifts continuous and bounded in
  $`x`$ weak Fokker–Planck solutions are unique, and for Lipschitz drifts with linear growth (OU,
  Langevin) they exist as limits of Euler–Maruyama laws, so the Itô input is discharged for
  Langevin; uniqueness also for $`-a x`$ plus a bounded drift. DiPerna–Lions in any dimension for
  $`W^{1,1}_{\mathrm{loc}}`$ velocities with bounded divergence and linear growth (bounded
  densities), and for $`L^p`$ densities, $`p \gt 1`$.*
- **FL-6 Fokker–Planck well-posedness for Lipschitz drifts.** For $`D \gt 0`$ and a drift jointly
  continuous in $`(t, x)`$ and globally Lipschitz in $`x`$ uniformly on every $`[0, T]`$ (unbounded,
  linear growth), probability solutions of the weak Fokker–Planck equation with the same initial law
  coincide for all $`t \ge 0`$, with no moment or density assumption; with the existence results
  these drifts, and Langevin with Lipschitz $`\nabla U`$, are well-posed, and for autonomous drifts
  every solution is the weak limit of the dyadic Euler–Maruyama laws. Uniqueness for these drifts
  is a case of the classical theorem for drifts with
  $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$ (Bogachev–Krylov–Röckner–Shaposhnikov,
  2015, Ch. 9). *Verified, no SDE theory; dissipative drifts that are not globally Lipschitz
  (classical, as above) and matrix diffusions are not formalised.*

### Score estimation
- **SE-1 Stein/Hyvärinen objective.**
  $`J(f) = \int (\tfrac{1}{2} \Vert f \Vert_H^2 - f \cdot \nabla \log \pi - \mathrm{div}\, f) \, d\rho = \tfrac{1}{2} \int \Vert f - v_\star \Vert_H^2 \, d\rho - \tfrac{1}{2} \int \Vert \nabla \log(\rho/\pi) \Vert_{H^{-1}}^2 \, d\rho`$
  with $`v_\star = H^{-1} \nabla \log(\pi/\rho)`$; over any class of admissible fields, $`J`$ and
  $`\int \Vert f - v_\star \Vert_H^2 \, d\rho`$ have the same minimisers, and $`v_\star`$ is the
  a.e.-unique minimiser when it lies in the class. *Verified (Proposition 1 of PFG,
  Dong–Wang–Lin–Zhang, 2023, and the identity of its proof).*
- **SE-2 Linear feature classes.** Normal equations; fixed-RKHS vs. distribution-weighted
  regulariser; SVGD direction (finite-feature SVGD as in PFG, Dong–Wang–Lin–Zhang, 2023,
  §3.2.1). *Verified.*
- **SE-3 Denoising.** Tweedie and affine-Gaussian posterior scores; the OU posterior score is
  Lemma 1 of reverse diffusion Monte Carlo (rdMC; Huang–Dong–Hao–Ma–Zhang, 2024), here for any
  prior law. *Verified.*
- **SE-4 Monte Carlo posterior mean.** Unbiasedness, MSE $`= \text{variance}/n`$; applied, in one
  dimension, to the Monte Carlo score estimate of rdMC (half their $`v_k`$ of Eq. (5)) with exact
  posterior draws. *Verified.*

### Kernels and samplers
- **KR-1 TV propagation.** Contraction, telescoping with uniform / law-averaged errors,
  three-chain decomposition. *Verified.*
- **KR-2 Reverse kernels.** Bayes reverse kernel, composition, density form. *Verified.*
- **GI-1 Score-error theorem for Gaussian-increment chains.** For
  $`P_k(x) = \mathcal{N}(x + h \, b_k(x), 2hI)`$ and
  $`Q_k(x) = \mathcal{N}(x + h \, \hat{b}_k(x), 2hI)`$:
  $`\mathrm{KL}(\nu_K \Vert \mu_K) \le \mathrm{KL}(\nu_0 \Vert \mu_0) + (h/4) \sum_k \int \Vert b_k - \hat{b}_k \Vert^2 \, d\nu_k`$
  (errors under the algorithm's laws), and the same with the roles exchanged (errors under the exact
  chain's laws). One Pinsker at the end gives TV with no $`\sqrt{K}`$ loss; this is the standard
  route of diffusion-model analyses (Chen–Lee–Lu, 2023; Chen et al., 2023). *Verified (1D and
  `Fin d → ℝ`); the KL bound is attained (EX-3).*
- **GI-2 Random score oracle.** GI-1 with a drift re-estimated from fresh draws at each step; Monte
  Carlo instance `tvSup` $`\le \sqrt{\mathrm{KL}_0/2 + \sum_k h_k c_k^2/(8N) \int V_k \, d\nu_k}`$
  with $`N`$ exact posterior draws per step. With an inexact inner sampler of KL error $`\delta_k`$
  and a $`\sigma_k^2`$-sub-Gaussian posterior, the bias adds $`2 \sigma_k^2 \delta_k`$ to the
  per-step budget (constant sharp for Gaussians); $`\delta_k`$ bounds the KL averaged over the
  algorithm's law; a coupling version needs no sub-Gaussianity. This models the score oracle of
  rdMC (fresh posterior draws at each step from an inexact inner sampler); the bias–variance split
  and the coupling bound on the bias are in-expectation counterparts of the score-error step of
  their analysis (cf. their Eqs. (17)–(18)). *Verified.*
- **MH-1 Metropolis–Hastings.** Detailed balance and invariance for general densities; MALA. *Verified.*
- **PX-1 Proximal sampler** (Lee–Shen–Tian, 2021). Restricted Gaussian oracle (RGO) as Bayes
  reverse kernel; invariance. *Verified (1D and `Fin d → ℝ`).*
- **PX-2 Proximal contraction under LSI.** KL contracts by $`1/(1 + \alpha\eta)`$ per step, and by
  the sharp $`1/(1 + \alpha\eta)^2`$ when the backward step is also analysed. *Conditional: de
  Bruijn is proved; for a general target the $`1/(1 + \alpha\eta)`$ rate assumes a functional LSI of
  $`\pi`$ (1D and `Fin d → ℝ`) and the heat-flow regularity; in 1D the sharp rate follows from the
  same LSI plus explicit backward regularity (the backward marginals are
  $`\pi_{\eta - t} \cdot (\varphi_t * r)`$), likewise in `Fin d → ℝ`. Final form: LSI of $`\pi`$
  plus a Gaussian upper envelope (automatic for strongly convex potentials) give
  $`(1 + \alpha\eta)^{-2k}`$ for every $`\rho_0`$ with finite KL, with no regularity hypotheses.*
  Strongly log-concave targets (1D and `Fin d → ℝ`): sharp rate with no hypotheses. Any target:
  $`\mathrm{KL}(\rho P \Vert \pi) \le \int (x - y)^2 \, d\gamma/(2\eta)`$ for every coupling; merely
  log-concave: $`\mathrm{KL}(\rho_k \Vert \pi) \le \int (x - y)^2 \, d\gamma_0/(2k\eta)`$ for every
  convex $`f`$ on `Fin d → ℝ` (and in 1D), with no further hypotheses (shifted composition of
  Altschuler–Chewi (2023) with a weak contractive coupling of the RGO via synchronous Euler–Maruyama
  chains of the Langevin dynamics, smooth approximation, compactness). The rates are those of
  Chen–Chewi–Salim–Wibisono (2022): their Theorem 3 under an LSI, and the log-concave $`1/k`$ rate,
  for which they have the constant $`1/(k\eta)`$.
- **PX-3 Proximal sampler for Gaussian targets.** For $`\pi = \mathcal{N}(0, \alpha^{-1} I)`$ and
  every $`\rho_0`$ with finite KL,
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1 + \alpha\eta)^{2k}`$,
  attained (EX-3; observed by Chen–Chewi–Salim–Wibisono, 2022, §4.4); the case
  $`f = \alpha \Vert x \Vert^2/2`$ of PX-6. *Verified (1D and `Fin d → ℝ`), no named
  hypotheses.*
- **PX-4 Proximal sampler for perturbed Gaussians.** $`\pi \propto \exp(-\alpha x^2/2 - W)`$, $`W`$
  measurable, bounded: rate $`(1 + \alpha e^{-\mathrm{osc}\,W} \eta)^{-2}`$ per step (Holley–Stroock
  constant, not optimal in general), for all iterates, for every $`\rho_0`$ with finite KL (no
  moment, no warm start): Theorem 3 of Chen–Chewi–Salim–Wibisono (2022) with the Holley–Stroock
  perturbation lemma. *Verified (1D and `Fin d → ℝ`).*
- **PX-5 Proximal sampler for log-concave targets.** For every convex $`f`$ with
  $`\int e^{-f} \lt \infty`$ and every coupling $`\gamma_0`$ of $`(\rho_0, \pi)`$,
  $`\mathrm{KL}(\rho_{k+1} \Vert \pi) \le \int \Vert x - y \Vert^2 \, d\gamma_0/(2(k+1)\eta)`$, by
  the shifted-composition argument of Altschuler–Chewi (2023). This constant is stated for $`C^2`$
  potentials by Pedrotti (2026, Cor. 3.5); Chen–Chewi–Salim–Wibisono (2022) have $`1/(k\eta)`$.
  *Verified (`Fin d → ℝ`, every dimension), no named hypotheses.*
- **PX-6 Proximal sampler for strongly log-concave targets.** For $`f - \alpha \Vert x \Vert^2/2`$
  convex, $`\alpha \gt 0`$,
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1 + \alpha\eta)^{2k}`$ for
  every $`\rho_0`$ with finite KL (Theorem 3 of Chen–Chewi–Salim–Wibisono, 2022, with the LSI by
  Bakry–Émery). *Verified (1D, `Fin d → ℝ` and Mathlib's
  `EuclideanSpace ℝ (Fin d)`), no named hypotheses.*
- **DF-1 Diffusion models.** DDPM-type sampler (forward OU, reverse Gaussian steps from a learned
  score) with reverse variance $`\sigma_k^2 = \beta_k/\alpha_k^2`$:
  $`\mathrm{KL}(p_\delta \Vert q) \le \mathrm{KL}(p_T \Vert \mathcal{N}(0, I)) + \text{discretisation} + \sum_k (\beta_k/2) \, \mathbb{E}_{p_k} \Vert \hat{s}_k - \nabla \log p_k \Vert^2`$,
  with the discretisation term $`\le (\kappa d/2)(1 + \log(u_N/u_1))`$ on grids
  $`u_{k+1} \le (1 + \kappa) u_k`$, for every data law with finite second moment; $`p_\delta`$ is
  the data law noised to the early-stopping time $`\delta = t_1`$. This is the $`d`$-linear rate of
  Benton–De Bortoli–Doucet–Deligiannidis (2024). *Verified (`Fin d → ℝ`), no SDE theory.*
- **DF-2 Memorisation** (known for the continuous-time sampler: Pidstrigach, 2022, Cor. 1;
  Li–Chen–Li, 2024, Thm 4.3; see also Gu et al., 2023; here for the discretised sampler). With the
  exact score of the empirical measure of $`n`$ training points, for every
  $`\rho, \varepsilon \gt 0`$ there are sampler parameters (grid, early stopping) for which the
  output puts mass $`\ge 1 - \varepsilon`$ within distance $`\rho`$ of the training points.
  *Verified.*
- **DF-3 Deterministic versus stochastic samplers.** For every data law with finite second moment
  and every $`\varepsilon \gt 0`$ there is a uniformly $`\varepsilon`$-accurate learned score for
  which the deterministic sampler (probability-flow ODE / DDIM step) outputs a law at TV distance
  $`1`$ from $`p_\delta`$, while DDPM with the same score satisfies the DF-1 bound (construction of
  Li–Wei–Chen–Chi, 2023, §3.2). *Verified.*
- **DF-4 Reverse-noise variance.** Exact per-step identity for every reverse variance, minimised at
  the Analytic-DPM variance (Bao et al., 2022, whose data-free upper bound on it is
  $`\beta_k/\alpha_k^2`$). With $`\sigma_k^2 = \beta_k`$, on grids with
  $`u_{k+1} \le (1 + \kappa) u_k`$ up to an index $`m`$ with $`1 \le \kappa u_m \le 1 + \kappa`$
  (arbitrary afterwards), the discretisation term is bounded independently of $`N`$ and $`T`$ (the
  learned-score error remains); with $`\sigma_k^2 = \beta_k/\alpha_k^2`$ and second moment
  $`M \le d`$, the summed per-step discretisation KL has a lower bound linear in $`T`$ on a uniform
  grid of fixed step. Bounds with no term growing in $`T`$ are known for $`\sigma_k^2 = \beta_k`$
  (Koike, 2026, Thm 3.1; Conforti–Durmus–Gentiloni Silveri, 2023, Cor. 1). *Verified.*
- **DF-5 Path-space KL.** For any data law, grid, reverse variances and measurable means, the KL
  from the law of the forward chain $`(x_N, \ldots, x_1)`$ to the sampler's path law equals
  $`\mathrm{KL}(p_N \Vert \mathcal{N}(0, I)) + \sum_k \int \mathrm{KL}(R_k(y) \Vert Q_k(y)) \, dp_k(y)`$,
  and bounds the output KL. With $`\sigma^2 = \beta/\alpha^2`$ and $`M \le d`$ it has, for every
  mean map, a lower bound linear in $`T`$ on a uniform grid of fixed step; with
  $`\sigma^2 = \beta`$, the exact score and the DF-4 grids it is bounded uniformly in $`N`$ and
  $`T`$ at fixed $`t_1, \kappa, d, M`$. That the path KL is of the order of the step size in the
  worst case is noted by Benton et al. (2024, §4) and Li–Yan (2024, §3.1), after Chen et al. (2023,
  Thm 7); here the lower bound holds for every data law with $`M \le d`$ and every mean map.
  *Verified.*
- **DF-6 Sharpness of the discretisation rate.** For $`\sigma^2 = \beta/\alpha^2`$ and any data law
  with finite second moment $`M`$, the per-step discretisation sum of DF-1 is bounded below by a
  term of order $`1/N`$ per unit of log-time, the order of the DF-1 upper bound on geometric grids,
  minus a term $`(d/2) \log(1 + M/(d u_m))`$ that does not shrink with $`N`$. For the point mass
  $`\delta_0`$ the sum is computed exactly, and the geometric grid minimises it among grids
  $`t_1 \lt \cdots \lt t_N`$ with the same $`u_1, u_N`$ (cf. Chen–Lee–Lu, 2023, App. B, for
  geometric steps minimising an upper bound). This concerns the path-level sum (DF-5), not the
  output law. *Verified.*
- **DF-7 Smooth separation.** DF-3 with an analytic error: for every $`\varepsilon, \eta \gt 0`$
  there is a learned score whose error, at a single step, is an analytic function of the exact
  update with sup norm $`\le \varepsilon`$, such that the output $`q`$ of the deterministic sampler
  has $`\mathrm{TV}(p_\delta, q) \ge 1 - \eta`$ while DDPM with the same score keeps the DF-1 bound.
  Uniform score accuracy without Lipschitz control does not suffice for deterministic samplers.
  The closest earlier result is Li–Di–Gu (2024, Thm 3.1): a smooth uniformly
  $`\varepsilon`$-accurate score with TV $`\ge 1/(4\pi)`$ for the continuous-time probability-flow
  ODE and Gaussian data. *Verified.*
- **DF-8 Output versus path KL on Gaussian data.** For $`\mu = \mathcal{N}(0, vI)`$ with
  $`0 \lt v \le 1`$, the exact score, $`\sigma^2 = \beta/\alpha^2`$ and steps $`\le h`$, the output
  KL is at most $`d((1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1)^2/(4 s_1^2)`$ with
  $`s_1 = e^{-2t_1} v + 1 - e^{-2t_1}`$. On the uniform grid with $`e^{2h} \le 2`$ it is at least
  $`d h^2 (1 - e^{-2(t_N - t_1)})^2/3`$, while the path KL is at least $`d (t_N - t_1) h/(1 + h)`$.
  For $`v = 1`$ over a fixed interval the output KL is $`\Theta(d h^2)`$ and the path KL
  $`\Omega(h)`$. Jiao–Zhou–Li (2025, Thm 2) prove an output lower bound of the same order for
  $`\mathcal{N}(0, \lambda I)`$ data with $`\lambda \ge 2`$ on their schedule. *Verified.*
- **DF-9 Deterministic samplers in transport distance.** If the exact-score step maps are
  $`L_i`$-Lipschitz and the learned steps are uniformly within $`\delta_i`$ of them, the
  deterministic output and the exact-score deterministic output admit a coupling with
  $`\Vert x - x' \Vert \le \sum_i (\prod_{1 \lt j \lt i} L_j) \, \delta_i`$ almost surely
  ($`W_\infty`$ and $`W_2`$ bounds stated as explicit couplings). With DF-7: the deterministic
  output driven by the analytic score is TV-far from $`p_\delta`$, yet within
  $`\lvert b_2 \rvert \cdot \varepsilon`$ of the exact-score deterministic output almost surely;
  uniform score accuracy controls transport distance, not TV (the pairing is implicit in the example
  of Li–Wei–Chen–Chi, 2023, who suggest a Wasserstein metric). *Verified; the comparison is with the
  exact-score deterministic output, not the data.*
- **PT-1 Particles.** Empirical push-forward under flows and Euler steps. *Verified.*
- **DT-1 Deterministic step descent.**
  $`\mathrm{KL}((\mathrm{id} + \eta v)_\# \rho \Vert \pi) \le \mathrm{KL}(\rho \Vert \pi) - \eta \, (\text{dissipation}) + O(\eta^2)`$
  with constants in $`\mathrm{Lip}(v)`$. *Verified in dimension one, and on `Fin d → ℝ` for
  velocities with symmetric Jacobian; general Jacobians with constant 13 on $`\Vert Dv \Vert_F^2`$.
  For the ideal velocity (1D and `Fin d → ℝ`) the first-order term is the relative Fisher
  information, with step $`\eta \le 1/(2(L_U + L_p))`$ depending on the current law; no
  law-independent step exists (CE-08). The KL-level forms (except `klDiv_map_step_le_of_mul_dim_le`)
  also hold with integrability replaced by finite KL and a finite second moment, plus a two-sided
  Hessian bound on $`U`$ for the non-ideal versions.*

### Examples
- **EX-1** OU vs. deterministic Gaussian flow: equal one-time marginals, different two-time laws, exact KL dissipation.
- **EX-2** Discrete population Gaussian flow: closed-form recursions and contraction (PFG,
  Dong–Wang–Lin–Zhang, 2023, App. A.6).
- **EX-3** Tightness: GI-1's KL bound is attained by constant drifts (TV telescoping loses
  $`\sqrt{2n/\pi}`$); PX-2's $`(1 + \alpha\eta)^{-2}`$ rate is attained by Gaussians. Both also in
  `Fin d → ℝ`.

### Counterexamples (IDs CE-01 … CE-08)
Marginals do not determine paths (CE-01); noise is not the score (CE-02); ULA is biased (CE-03; for
Gaussian targets, Wibisono, 2018, Example 2); one Stein test does not identify a law (CE-04);
particles have no score (CE-05); empirical Stein objectives can be unbounded (CE-06; cf. Hyvärinen,
2005, §3.1, and Lin–Drton–Shojaie, 2016, for Gaussian score matching). CE-07: a contraction along
the chain does not imply a uniform one (reset kernels contract with $`\rho = 0`$ along chains
carried by a set $`A`$, but are not uniform TV contractions for any $`\rho \lt 1`$). CE-08: no fixed
step size makes the ideal-velocity deterministic step a KL descent for all laws (a consequence of
the Gaussian recursion in Wibisono, 2018, Example 4). CE-07 and CE-08 are proved next to the
theorems they delimit (`Kernels/ErrorDecomposition`, `Flow/IdealVelocityStep`).

## 5. Conventions

As in [CONTRIBUTING.md](../CONTRIBUTING.md#conventions). Every theorem names: the divergence and its direction; the law under which
an error is averaged; the quantifier (pointwise, almost everywhere, in expectation); and the
object certified (a law, a kernel, an empirical measure).
