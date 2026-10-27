# Results catalogue

One entry per row of the [theorem registry](theorem_registry.md), under the registry's sections, in
its order and with its short titles; the registry gives the exact hypotheses and the Lean
declarations of each row. All results are proved in Lean (status *Verified*) unless marked
otherwise. $`d`$ is arbitrary unless "1D" is stated. KL is Mathlib's `klDiv` and TV is
$`\sup_A \lvert \mu(A) - \nu(A) \rvert`$ (`TotalVariation.tvSup`); the [glossary](glossary.md) fixes
the vocabulary.

## Organising picture

The target is a probability density $`\pi \propto e^{-U}`$ on `Fin d → ℝ`. The common
continuous-time object is the KL gradient flow,
$`\partial_t \rho = \mathrm{div}(\rho A \nabla \log(\rho/\pi))`$ for a constant SPD matrix $`A`$. It
has two implementations.

| Layer | Stochastic implementation | Deterministic implementation |
|---|---|---|
| population flow | Langevin $`dX = A \nabla \log \pi \, dt + \sqrt{2A} \, dW`$ | transport $`\dot{Y} = A(\nabla \log \pi - \nabla \log \rho_t)(Y)`$ (probability flow, SVGD, preconditioned functional gradient flow (PFG; Dong–Wang–Lin–Zhang, 2023)) |
| equivalence | same weak evolution; same one-time marginals under uniqueness; different path laws | (same) |
| approximation error | drift / score error of a Gaussian-increment chain | velocity error in $`L^2(\rho_t)`$ |
| where the score comes from | denoising / Tweedie for noised laws | Stein / Hyvärinen objective, feature classes, kernel smoothing |
| discretisation | Gaussian-increment (Euler–Maruyama) kernels | push-forward by $`\mathrm{id} + \eta v`$; stable step depends on the current law |
| exact correction | Metropolis–Hastings; proximal (Gibbs) sampler | — |
| particles | — | empirical measures have no score; empirical objectives can be unbounded |

## Diffusion models (DDPM/DDIM, memorisation, variance, path vs output)

Here $`p_\delta`$ is the data law noised up to the early-stopping time $`\delta = t_1`$, and
$`u_k = e^{2t_k} - 1`$.

- **End-to-end guarantee (DF-1).** For DDPM-type samplers with reverse variance
  $`\sigma_k^2 = \beta_k/\alpha_k^2`$, for any data distribution with finite second moment $`M`$ (no
  density needed), on grids with $`u_{k+1} - u_k \le \kappa u_k`$:
  $`\mathrm{KL}(p_\delta \Vert \text{output}) \le I + (\kappa d/2)(1 + \log(u_N/u_1)) + \sum_k (\beta_k/2) \cdot \mathbb{E}_{p_k} \Vert \hat{s}_k - \nabla \log p_k \Vert^2`$,
  where the initialisation term
  $`I = e^{-2(T-\delta)} \cdot (d(\beta_1 - 1 - \log \beta_1) + \alpha_1^2 M)/2`$ grows like
  $`d \log(1/\delta)`$ as $`\delta \to 0`$. The three terms are the initialisation, discretisation
  and score errors; the discretisation term is linear in the dimension, as in Benton–De
  Bortoli–Doucet–Deligiannidis (2024). The proof uses Tweedie's formula, an exact entropy identity
  for each reverse step, de Bruijn's identity and the monotonicity of Fisher information. The number
  of steps is explicit: for every $`\varepsilon \gt 0`$ a geometric grid with
  $`N \le 2(d + 1)L(L + 2)/\varepsilon + 2L + 2`$ steps gives
  $`\mathrm{KL}(p_\delta \Vert \text{output}) \le \varepsilon`$ plus the score-error term, where
  $`L`$ depends on $`d`$, $`M`$, $`\varepsilon`$ and $`\delta`$ only through a logarithm.
- **Memorisation (DF-2).** With the exact score of its training set, a diffusion model reproduces
  the training points in the vanishing-noise limit: for every $`\rho, \varepsilon \gt 0`$ there are
  sampler parameters (early stopping, grid) giving output mass $`\ge 1 - \varepsilon`$ within
  distance $`\rho`$ of the training set. This is known for the continuous-time sampler (Pidstrigach
  2022, Cor. 1; Li–Chen–Li 2024, Thm 4.3; see also Gu et al. 2023); here it is proved for the
  discretised sampler.
- **Deterministic versus stochastic samplers (DF-3).** For every data law with finite second moment
  and every $`\varepsilon \gt 0`$ there is a uniformly $`\varepsilon`$-accurate score for which the
  deterministic sampler (probability-flow ODE / DDIM) is at TV distance 1 from $`p_\delta`$, while
  DDPM with $`\sigma_k^2 = \beta_k/\alpha_k^2`$ and the same score satisfies the DF-1 bound
  (construction of Li–Wei–Chen–Chi 2023, §3.2). $`L^2`$ score accuracy suffices for the stochastic
  sampler but not for the deterministic one.
- **Reverse-noise variance (DF-4).** With reverse variance $`\sigma_k^2 = \beta_k`$, on a grid that
  is geometric up to some index ($`u_{k+1} - u_k \le \kappa u_k`$,
  $`1 \le \kappa u_m \le 1 + \kappa`$) and arbitrary afterwards, the discretisation error is bounded
  by a constant depending on $`\kappa, u_1, d, M`$ only, not on $`N`$ or $`T`$; with
  $`\sigma_k^2 = \beta_k/\alpha_k^2`$ and data with $`M \le d`$ the summed per-step error has a
  lower bound linear in $`T`$ on a uniform grid of fixed step. Bounds with no term growing in $`T`$
  are known for $`\sigma_k^2 = \beta_k`$: Koike (2026, Thm 3.1 and Remark 3.2) for the DDPM sampler,
  as the Euler–Maruyama scheme of the Föllmer process, and Conforti–Durmus–Gentiloni Silveri (2023,
  Cor. 1) for an exponential-integrator scheme with step variance $`\beta_k`$. The per-step error
  has an exact expression for every reverse variance; the optimal per-step variance is the
  Analytic-DPM one (Bao et al. 2022), whose data-free upper bound is $`\beta_k/\alpha_k^2`$ (their
  App. D, Cor. 3).
- **Path-space KL (DF-5).** The KL between the reversed forward path and the sampler path equals the
  initial KL plus the sum of per-step errors, and bounds the output KL. With
  $`\sigma^2 = \beta/\alpha^2`$, data with $`M \le d`$ and a uniform grid of fixed step it has a
  lower bound linear in $`T`$ for every mean map. That the path KL is of order of the step size in
  the worst case is noted by Benton et al. (2024, §4; point-mass data) and Li–Yan (2024, §3.1),
  after Chen et al. (2023, Thm 7) for the critically damped Langevin sampler. With
  $`\sigma^2 = \beta`$, the exact posterior mean and the grid conditions of DF-4, it is bounded
  uniformly in $`N`$ and $`T`$ at fixed $`t_1, \kappa, d, M`$. Learned scores add
  $`\sum_k \beta_k/(2\alpha_k^2) \, \mathbb{E}_{p_k} \Vert \hat{s}_k - \nabla \log p_k \Vert^2`$,
  which also needs uniform control for a uniform total-error bound. For exact scores and Gaussian
  data $`\mathcal{N}(0, vI)`$ with $`\sigma^2 = \beta/\alpha^2`$, DF-8 bounds the output KL
  uniformly in $`T`$ at fixed $`t_1`$ and maximal step: for every $`T`$ when $`v \le 1`$, and once
  $`(v - 1)e^{-2(2T - t_1)}s_1 \lt 1`$ when $`v \gt 1`$.
- **Sharpness of the discretisation rate (DF-6).** With $`\sigma^2 = \beta/\alpha^2`$ and the exact
  posterior mean, the per-step error sum is bounded below by order $`1/N`$ per unit of log-time for
  every data law with finite second moment $`M`$, minus a term depending on $`M`$ that does not
  shrink as $`N`$ grows, so DF-1's discretisation term is sharp at path level over long horizons. On
  a uniform grid over a fixed interval, a lower bound of order $`1/N`$ is proved for data with
  $`M \le d`$ (DF-4, DF-5); for a point mass at the origin the sum is explicit and, among grids with
  the same $`N`$, $`u_1`$ and $`u_N`$, the geometric grid minimises it (Chen–Lee–Lu 2023, App. B,
  choose geometric steps by a convexity argument in log-time). Sun–Poor–Zhang (2026, Thm 3) give a
  lower bound on the path KL of a related continuous-time sampler, with Gaussian data as the
  extremal case. The faster decay of the output KL seen numerically (`../showcase/ddpm_rate.py`,
  data with $`M \le d`$) cannot be recovered by bounding the full KL along the true reverse chain
  and then applying data processing alone.
- **Smooth separation (DF-7).** The separation of DF-3 holds, with TV $`\ge 1 - \eta`$, for a
  learned score whose error, at a single step, is an analytic function of the exact update with sup
  norm $`\le \varepsilon`$, while DDPM with the same score keeps the DF-1 bound: uniform score
  accuracy without Lipschitz control does not suffice for deterministic samplers. Lean proves a
  lower bound $`(2^m - 1)/\lvert b_2 \rvert`$ on the Lipschitz constant of the error for the
  (non-explicit) $`m`$ used, and its growth as $`\eta \to 0`$ is numerical only. A related result
  is Li–Di–Gu (2024, Thm 3.1): a smooth score within $`\varepsilon`$ of the true score
  everywhere for which the continuous-time probability-flow ODE stays a fixed TV distance away from
  Gaussian data, however small $`\varepsilon`$ is.
- **Output versus path KL on Gaussian data (DF-8).** For standard Gaussian data
  $`\mathcal{N}(0, I)`$, the exact score, $`\sigma^2 = \beta/\alpha^2`$, a uniform grid with step
  $`h`$ ($`e^{2h} \le 2`$) over a fixed interval $`0 \lt t_1 \lt T`$, the output KL is
  $`\Theta(d h^2)`$ (upper and lower bounds of the same order, constants not matched), while the
  path KL is $`\ge d(T - t_1)h/(1+h)`$. For $`\mathcal{N}(0, vI)`$ with $`v \lt 1`$ the upper bound
  is $`O(d h^2)`$ plus an initialisation term driven by $`(1 - v)e^{-2(2T - t_1)}`$, exponentially
  small in $`T`$ but not vanishing as $`h \to 0`$ at fixed $`T`$. For $`v \gt 1`$ the bound is
  $`d((e^{2h} - 1)^2 + (\varepsilon/(1 - \varepsilon))^2)/4`$ whenever
  $`(v - 1)e^{-2(2T - t_1)}s_1 \le \varepsilon \lt 1`$; its $`\varepsilon^2`$ initialisation term
  likewise does not vanish as $`h \to 0`$ at fixed $`T`$. With $`\sigma^2 = \beta`$ the sampler is
  exact for $`v = 1`$. Jiao–Zhou–Li (2025, Thm 2) prove an output lower bound of order $`d/N^2`$ for
  Gaussian data on their schedule.
- **Deterministic samplers in transport distance (DF-9).** If the exact-score steps are Lipschitz, a
  uniformly $`\varepsilon`$-accurate score keeps the deterministic output within an explicit
  distance of the exact-score deterministic output under a coupling ($`W_\infty`$, $`W_2`$ bounds);
  comparison with the data itself is not proved. With DF-7, the deterministic output driven by the
  analytic score is TV-far from $`p_\delta`$, yet within $`\lvert b_2 \rvert \cdot \varepsilon`$ of
  the exact-score deterministic output almost surely. Li–Wei–Chen–Chi (2023) suggest a Wasserstein
  metric for their example (DF-3). Convolving both the learned output $`q_k`$ and the exact-score
  output $`q^*_k`$ with one Gaussian step $`\mathcal{N}(0, \tau I)`$ turns the coupling bound $`B`$
  into $`\mathrm{KL}(\mathcal{N}_\tau * q_k \Vert \mathcal{N}_\tau * q^*_k) \le B^2/(2\tau)`$ and,
  by Pinsker,
  $`\mathrm{TV}(\mathcal{N}_\tau * q_k, \mathcal{N}_\tau * q^*_k) \le B/(2\sqrt{\tau})`$; the
  learned score needs no regularity, and no bound against the data is proved. This is the standard
  Gaussian-regularisation bound (joint convexity of KL, as for the proximal sampler in PX-2); adding
  a little noise to pass from a Wasserstein bound for a deterministic sampler to KL or TV is the
  device of Chen–Chewi–Lee–Li–Lu–Salim (2023, §4) and Lyu–Chen–Feng (2023, Lemma 12).
- **Long horizon, small Lipschitz score error (DF-10).** A small Lipschitz constant does not rescue
  the deterministic sampler once the horizon is long. The error
  $`-(\varepsilon/R) \, \mathrm{clip}_R(y)`$ (in one coordinate) is at most $`\varepsilon`$ in sup
  norm and $`\varepsilon`$-Lipschitz; while the forward marginal is close to stationary the
  exact-score probability-flow step is close to the identity, so the error accumulates. For standard
  Gaussian data the deterministic sampler has $`\mathrm{TV}(p_\delta, q) \ge 1 - \eta`$ while DDPM
  with the same score has $`\mathrm{TV} \le \eta`$, on geometric grids with a horizon of at most
  $`A/\varepsilon`$ ($`A`$ depends on $`\eta`$, the dimension and the grid parameter $`u_1`$, not on
  $`\varepsilon`$). For two atoms $`(\delta_{-a} + \delta_a)/2`$ in dimension one, with the error
  switched on at high noise only, the deterministic output puts mass $`\ge 1 - \eta`$ on a slab
  around the midpoint where $`p_\delta`$ puts mass $`\le \eta`$ (it collapses onto the midpoint),
  while DDPM stays within TV $`\eta`$. Gaussian data, a stationary forward process whose exact
  probability-flow velocity vanishes, is the setting of Li–Di–Gu (2024, Thm 3.1); that the
  deterministic flow carries a mismatch forward while the stochastic sampler forgets it is described
  by Nie et al. (2024, Thms 3.1–3.2) and Cao et al. (2023, arXiv:2306.02063). No lower bound on the
  horizon a collapse needs is proved.

## Proximal sampler

- **Restricted Gaussian oracle and invariance (PX-1).** For the proximal sampler of Lee–Shen–Tian
  (2021), the restricted Gaussian oracle (RGO) is the Bayes reverse kernel of its Gaussian forward
  step, and the target is invariant, in 1D and on `Fin d → ℝ`. The invariance is also stated on
  Mathlib's `EuclideanSpace ℝ (Fin d)` (`Samplers/EuclideanTransfer`).
- **Proximal contraction under LSI (PX-2).** For a target with a functional log-Sobolev inequality
  $`\mathrm{LSI}(1/\alpha)`$ and a Gaussian upper envelope,
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1+\alpha\eta)^{2k}`$ (sharp
  rate; Chen–Chewi–Salim–Wibisono 2022, Thm 3) holds for every $`\rho_0`$ with finite KL, with no
  regularity hypotheses. The backward step is analysed explicitly. For any target,
  $`\mathrm{KL}(\rho P \Vert \pi) \le \int \Vert x-y \Vert^2 \, d\gamma/(2\eta)`$ for every coupling
  $`\gamma`$ of $`(\rho, \pi)`$. *Conditional* on the log-Sobolev inequality of the target, which is
  proved for the targets of PX-3, PX-4 and PX-6.
- **Proximal sampler for Gaussian targets (PX-3).** For $`\pi = \mathcal{N}(0, \alpha^{-1}I)`$ and
  every $`\rho_0`$ with finite KL,
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1+\alpha\eta)^{2k}`$ with no
  named hypotheses, in 1D and on `Fin d → ℝ`; this is the case $`f = \alpha \Vert x \Vert^2/2`$ of
  PX-6. The rate is attained exactly from starts $`\mathcal{N}(m, \alpha^{-1}I)`$ (EX-3). That the
  factor is sharp on Gaussian targets is observed by Chen–Chewi–Salim–Wibisono (2022, §4.4); see
  also Mitra–Wibisono (2025, App. G.2).
- **Proximal sampler for perturbed Gaussians (PX-4).** Bounded perturbations of Gaussians,
  $`\pi \propto e^{-\alpha \Vert x \Vert^2/2 - W}`$ with $`W`$ measurable and bounded (not
  log-concave in general), have rate $`(1+\alpha e^{-\mathrm{osc}\, W} \eta)^{-2k}`$ for every
  $`\rho_0`$ with finite KL; the LSI comes from Holley–Stroock, so this is the KL part of Theorem 3
  of Chen–Chewi–Salim–Wibisono (2022) combined with the Holley–Stroock perturbation lemma. On
  `Fin d → ℝ` the same holds for bounded perturbations $`\pi \propto e^{-f_0 - W}`$ of any
  $`\alpha`$-strongly log-concave $`e^{-f_0}`$, with rate
  $`(1+\alpha e^{-\mathrm{osc}\, W} \eta)^{-2k}`$ (`Samplers/ProximalPerturbedGeneralPi`).
- **Proximal sampler for log-concave targets (PX-5).** For every log-concave target
  $`\pi \propto e^{-f}`$ with $`f`$ finite and convex, in every dimension,
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \int \Vert x-y \Vert^2 \, d\gamma_0/(2k\eta)`$ for $`k \ge 1`$
  and every coupling $`\gamma_0`$ of $`(\rho_0, \pi)`$, assuming only $`\int e^{-f} \lt \infty`$,
  via shifted composition (Altschuler–Chewi, 2023) and a weak contractive coupling of the RGO. The
  coupling is built from synchronous Euler–Maruyama chains of the Langevin dynamics that leave the
  RGO invariant, with no SDE theory and no optimal transport, then extended to every convex
  potential by smooth approximation and compactness. The $`1/k`$ rate is that of
  Chen–Chewi–Salim–Wibisono (2022, Thm 2); the constant $`1/(2k\eta)`$ is the one the
  shifted-composition theorem of Altschuler–Chewi (2023, Thm 3.2) gives, as in the log-concave case
  of Pedrotti (2026, Cor. 3.5).
- **Proximal sampler for strongly log-concave targets (PX-6).** For $`\alpha`$-strongly log-concave
  targets ($`\alpha \gt 0`$) the rate $`(1+\alpha\eta)^{-2k}`$ of PX-2 holds for every $`\rho_0`$
  with finite KL and no further hypothesis: the LSI is proved via Bakry–Émery, so this is the KL
  part of Theorem 3 of Chen–Chewi–Salim–Wibisono (2022) with Bakry–Émery. It holds in 1D, on
  `Fin d → ℝ` and on Mathlib's `EuclideanSpace ℝ (Fin d)` (`Samplers/EuclideanTransfer`).

## KL toolkit and log-Sobolev inequalities

- **Pinsker (KL-1).** `tvSup μ ν` $`\le \sqrt{\mathrm{KL}(\mu \Vert \nu)/2}`$ for probability
  measures on any measurable space, and the bridge to Mathlib's normalisation:
  `MeasureTheory.tvDist` is twice `tvSup`, so
  $`\Vert \mu - \nu \Vert_1 \le \sqrt{2\,\mathrm{KL}(\mu \Vert \nu)}`$.
- **Chain rule for kernels (KL-2).**
  $`\mathrm{KL}(\mu \otimes \kappa \Vert \nu \otimes \eta) = \mathrm{KL}(\mu \Vert \nu) + \int \mathrm{KL}(\kappa(a) \Vert \eta(a)) \, d\mu`$
  and data processing for the second marginal (both ported from the Lean Machine Learning library,
  LML), and KL propagation along two Markov chains,
  $`\mathrm{KL}(\nu_n \Vert \mu_n) \le \mathrm{KL}(\nu_0 \Vert \mu_0) + \sum_k \int \mathrm{KL}(Q_k(x) \Vert P_k(x)) \, d\nu_k`$,
  with the errors averaged under the law of the chain in the first argument. Convexity of KL, joint
  convexity in kernel/coupling form, and lower semicontinuity (Donsker–Varadhan). The approximation
  principle "a contraction for warm starts implies one for all finite-KL starts".
- **Gaussian KL (KL-3).**
  $`\mathrm{KL}(\mathcal{N}(m_1, v) \Vert \mathcal{N}(m_2, v)) = (m_1 - m_2)^2/(2v)`$, its isotropic
  $`d`$-dimensional form $`\Vert m_1 - m_2 \Vert^2/(2v)`$, and the one-dimensional formula for
  unequal variances.
- **Tensorisation (KL-4).** The KL between finite products of probability measures is the sum of the
  KLs of the factors,
  $`\mathrm{KL}(\bigotimes_i \mu_i \Vert \bigotimes_i \nu_i) = \sum_i \mathrm{KL}(\mu_i \Vert \nu_i)`$,
  with no countability assumption; KL is invariant under measurable equivalences.
- **Gaussian log-Sobolev inequality (KL-5).**
  $`\mathrm{KL}(\rho \Vert \mathcal{N}(0, vI)) \le (v/2) \, I(\rho \Vert \mathcal{N}(0, vI))`$, with
  $`I`$ the relative Fisher information, in 1D and on `Fin d → ℝ`: along the heat flow for every
  $`\rho`$ with finite second moment, and at time 0 for positive differentiable densities with
  finite second moment and finite Fisher information. The proof uses de Bruijn's identity and the
  decay of Fisher information along the heat flow.
- **Functional log-Sobolev inequalities (KL-6).** Tensorisation, stability under convolution,
  Gross's inequality (hence
  $`\mathrm{LSI}(\pi, C) \Rightarrow \mathrm{LSI}(\pi * \mathcal{N}(0, t), C + t)`$), extension to
  unbounded positive test functions and Holley–Stroock, in 1D and on `Fin d → ℝ`, with the exact
  entropy chain rule in 1D. LSI transfers through 1D differentiable maps with
  $`\lvert T' \rvert \le K`$ (constant $`K^2 C`$) and through coordinatewise maps with
  $`\lvert T_i' \rvert \le 1`$; general Lipschitz push-forwards are not treated. Bakry–Émery: if
  $`f - \alpha \Vert x \Vert^2/2`$ is convex, then $`e^{-f}`$ satisfies $`\mathrm{LSI}(1/\alpha)`$.
  The 1D case uses the Caffarelli contraction. In dimension $`d`$ the proof goes through a
  formalisation of Prékopa–Leindler (Bobkov–Ledoux route).

## Flows, Fokker–Planck, continuity equation

- **First variation of KL (FL-1).** Along a continuity equation with velocity $`v_t`$,
  $`\frac{d}{dt} \mathrm{KL}(\rho_t \Vert \pi) = \int v_t \cdot \nabla \log(\rho_t/\pi) \, d\rho_t`$,
  for positive $`C^1`$ densities under explicit domination hypotheses.
- **Exact dissipation (FL-2).** For the ideal velocity
  $`v = H^{-1}(\nabla \log \pi - \nabla \log \rho)`$,
  $`\frac{d}{dt} \mathrm{KL} = -\int \Vert \nabla \log(\rho/\pi) \Vert_{H^{-1}}^2 \, d\rho`$. For
  the preconditioned functional gradient flow (PFG; Dong–Wang–Lin–Zhang 2023) this is the
  computation in the proof of their Theorem 1 (App. A.5) with no velocity error.
- **Approximate velocity (FL-3).** At one time, a velocity $`g`$ with relative error
  $`\int \Vert g - v_\star \Vert_H^2 \, d\rho \le \varepsilon I`$ gives
  $`\frac{d}{dt} \mathrm{KL} \le -(1 - \sqrt{\varepsilon}) \, I`$, with equality for
  $`g = (1 - \sqrt{\varepsilon}) \, v_\star`$; an absolute error
  $`E = \int \Vert g - v_\star \Vert_H^2 \, d\rho`$ gives
  $`\frac{d}{dt} \mathrm{KL} \le -\tfrac{1}{2} I + \tfrac{1}{2} E`$; a minimiser $`g`$ of the
  projection objective over a scale-closed class gives
  $`\frac{d}{dt} \mathrm{KL} = -\int \Vert g \Vert_H^2 \, d\rho`$. Here $`v_\star`$ is the ideal
  velocity of FL-2 and $`I`$ the $`H^{-1}`$-weighted relative Fisher information.
- **Decay (FL-4).** An LSI along the flow, with FL-2 and FL-3, gives exponential KL decay with an
  additive integrated error term; the Grönwall-with-source step is proved outright. *Conditional* on
  the LSI along the flow; for Gaussian targets the LSI along the flow is proved (KL-5), and the
  first-variation formula and the density regularity remain hypotheses. For the preconditioned
  functional gradient flow this includes Theorem 1 of Dong–Wang–Lin–Zhang (2023) with their
  constants, *Conditional* on their approximation condition [A3] and log-Sobolev assumption [A4].
  The OU/Langevin flow with Gaussian target $`\mathcal{N}(0, vI)`$ and rate $`a`$ has the sharp
  decay $`\mathrm{KL} \le e^{-2at} \mathrm{KL}_0`$ from every initial law with finite KL and finite
  second moment. Along the OU probability flow from any law with finite second moment,
  $`\frac{d}{dt} \mathrm{KL} = -av \cdot I`$ (relative Fisher information $`I`$) for $`t \gt 0`$ and
  the decay hold with every hypothesis discharged. The library's sufficient regularity bundle
  `TransportKLRegularity`, under which the generic decay theorem applies, is proved under a fourth
  moment; for that bundle the fourth moment is sharp on the polynomial scale (1D counterexamples
  with a finite third moment, and with a finite second moment).
- **Noise–score equivalence (FL-5).** Langevin and its probability-flow transport have the same
  one-time marginals (their two-time laws differ: EX-1, CE-01). *Conditional* on the law curve
  solving weak Fokker–Planck (the Itô input) and on continuity-equation uniqueness; unconditional
  for OU with an isotropic Gaussian initial law. The inputs, and the well-posedness of the
  Fokker–Planck equation, are proved in these cases, without SDE theory:
  - Continuity-equation uniqueness for jointly continuous velocities with linear growth that are
    locally Lipschitz in $`x`$ uniformly on each $`[0, T]`$, without flow maps, by approximate
    duality. DiPerna–Lions in every dimension for $`W^{1,1}_{\mathrm{loc}}`$ velocities with bounded
    divergence and linear growth, bounded densities, and for $`L^p`$ densities ($`p \gt 1`$) with
    $`W^{1,q}_{\mathrm{loc}}`$ velocities (commutator lemmas and renormalisation), for autonomous
    velocities and probability-density solutions.
  - Uniqueness of weak Fokker–Planck solutions for continuous bounded drifts, and for $`-a x`$ plus
    a bounded drift (so OU is well-posed), $`D \gt 0`$; Lipschitz drifts are FL-6.
  - Existence for Lipschitz drifts with linear growth (as weak limits of Euler–Maruyama laws), for
    locally Lipschitz dissipative drifts (by truncation), and for time-dependent drifts that are
    jointly continuous and Lipschitz in $`x`$ uniformly on each $`[0, T]`$; Langevin law curves,
    including quartic and double-well potentials.
- **Fokker–Planck well-posedness for Lipschitz drifts (FL-6).** Uniqueness of probability solutions
  of the weak Fokker–Planck equation for every drift jointly continuous in $`(t, x)`$ and globally
  Lipschitz in $`x`$ uniformly on each $`[0, T]`$ (unbounded allowed), $`D \gt 0`$, with no moment
  assumption: Lipschitz drifts and Langevin with Lipschitz $`\nabla U`$ are well-posed, and for
  autonomous drifts every solution is the limit of the Euler–Maruyama laws. Uniqueness for these
  drifts is a case of the classical theorem for drifts with
  $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$ (Bogachev–Krylov–Röckner–Shaposhnikov,
  *Fokker–Planck–Kolmogorov Equations*, 2015, Ch. 9).
- **Deterministic step descent (DT-1).**
  $`\mathrm{KL}((\mathrm{id}+\eta v)_\# \rho \Vert \pi) \le \mathrm{KL}(\rho \Vert \pi) - \eta \cdot (\text{dissipation}) + O(\eta^2)`$
  with constants in $`\mathrm{Lip}(v)`$, in 1D and on `Fin d → ℝ` for velocities with symmetric
  Jacobian (general Jacobians with the constant 13 on $`\Vert Dv \Vert_F^2`$). For the ideal
  velocity the first-order term is the relative Fisher information, with a step size
  $`\eta \le 1/(2(L_U + L_p))`$ that depends on the current law; no step size works for all laws
  (CE-08).

## Gaussian-increment chains (ULA / Euler–Maruyama)

- **Score-error theorem for Gaussian-increment chains (GI-1).** For chains
  $`x \mapsto \mathcal{N}(x + h \, b(x), 2hI)`$,
  $`\mathrm{KL}(\nu_K \Vert \mu_K) \le \mathrm{KL}(\nu_0 \Vert \mu_0) + (h/4) \sum_k \int \Vert b - \hat{b} \Vert^2 \, d\nu_k`$,
  with the error averaged under the algorithm's law (or, exchanging the chains, under the exact
  chain's law). One Pinsker at the end gives TV with no $`\sqrt{K}`$ loss. This is the standard
  route of diffusion-model analyses (Chen–Lee–Lu 2023; Chen et al. 2023), stated here for
  Gaussian-increment chains. The bound is attained (EX-3).
- **Random score oracle (GI-2).** The drift is re-estimated at every step from fresh posterior
  draws, possibly made by an inexact inner sampler, as in reverse diffusion Monte Carlo (rdMC;
  Huang–Dong–Hao–Ma–Zhang 2024); GI-1 holds with the errors averaged over the draws. With $`N`$
  exact posterior draws per step and the plug-in drift $`b + c_k(\hat{m} - m)`$, `tvSup`
  $`\le \sqrt{\mathrm{KL}_0/2 + \sum_k h_k c_k^2/(8N) \int V_k \, d\nu_k}`$, with $`V_k`$ the trace
  of the posterior covariance. The squared bias of the inner sampler's mean is bounded by a coupling
  or, for a $`\sigma^2`$-sub-Gaussian exact posterior, by $`2\sigma^2`$ times its KL error (cf.
  their Eqs. (17)–(18)). For a single Gaussian posterior draw $`y \sim \mathcal{N}(x, tI)`$, centred
  at the current state with known covariance, and plug-in drift $`b(x) + c(y - x)`$, the one-step
  law is $`\mathcal{N}(x + h b(x), (2h + (hc)^2 t) I)`$: the drift noise adds variance $`(hc)^2 t`$.
  If $`(hc)^2 t \le 2h`$, injecting variance $`2h - (hc)^2 t`$ instead of $`2h`$ makes the one-step
  law equal to the exact-drift EM step at every $`x`$ ($`\mathrm{KL} = \mathrm{TV} = 0`$). Without
  this correction, for $`h \gt 0`$, the KL from the random-oracle step to the EM step is
  $`d(u - \log(1 + u))/2 \le d u^2/2`$ with $`u = h c^2 t/2`$, i.e. $`O(d h^2)`$ for fixed $`c, t`$,
  against the conditional-KL bound $`d u/2 = d h c^2 t/4`$. Both are Gaussian instances of
  stochastic-gradient MCMC facts: zero-mean drift noise enters one step at second order in the step
  size (Welling–Teh 2011, §3), and subtracting its covariance from the injected noise makes the
  total noise exact (Ahn–Korattikara–Welling 2012; Chen–Fox–Guestrin 2014, Eq. (13); Ma–Chen–Fox
  2015, Eq. (9)).

## Identities, score estimation, kernels, MH, particles

- **Gaussian Stein identity (ID-1).** For $`X \sim \mathcal{N}(m, v)`$ and differentiable
  $`\varphi`$, $`\mathbb{E}[(X - m) \varphi(X)] = v \, \mathbb{E}[\varphi'(X)]`$ whenever
  $`(x - m) \varphi(x)`$ and $`\varphi'`$ are integrable (also for $`v = 0`$). On `Fin d → ℝ`,
  $`\mathbb{E}[Z_i \varphi(Z)] = \mathbb{E}[\partial_i \varphi(Z)]`$ for
  $`Z \sim \mathcal{N}(0, I_d)`$ and $`\varphi`$ of class $`C^1`$ with compact support.
- **Density Stein identity and zero-mean score (ID-2).** For a positive differentiable function
  $`p`$ on `Fin d → ℝ` and a differentiable vector field $`f`$,
  $`\int (\mathrm{div}\, f) \, p = -\int (f \cdot \nabla \log p) \, p`$ when $`(\partial_i f_i) p`$,
  $`f_i \, \partial_i p`$ and $`f_i p`$ are integrable, or with no integrability hypothesis when
  $`p`$ is $`C^1`$ and $`f`$ is $`C^1`$ with compact support. The score has mean zero,
  $`\int (\partial_i \log p) \, p = 0`$, when $`p`$ and $`\partial_i p`$ are integrable; $`p`$ need
  not be normalised.
- **Weak generator identity (ID-3).** For a continuous drift $`b`$, a positive $`C^1`$ function
  $`p`$ and a compactly supported $`C^2`$ test function $`\varphi`$,
  $`\int (b \cdot \nabla \varphi + D \Delta \varphi) \, p = \int ((b - D \nabla \log p) \cdot \nabla \varphi) \, p`$:
  the generator of $`dX = b(X) \, dt + \sqrt{2D} \, dW`$ and the generator of the probability-flow
  transport $`\dot{y} = b(y) - D \nabla \log p(y)`$ have equal integrals against $`p`$, while the
  integrands differ pointwise (explicit Gaussian instance). The same holds with a constant symmetric
  preconditioner $`A`$ and the transport velocity $`A(s_\star - \nabla \log p)`$, for a continuous
  target score field $`s_\star`$. This is an expectation-level equality; nothing is asserted about
  processes or laws.
- **Reverse-time Fokker–Planck rewriting (ID-4).** If positive densities $`p(t, \cdot)`$ of class
  $`C^2`$ and a differentiable drift $`b(t, \cdot)`$ solve
  $`\partial_t p = -\mathrm{div}(b p) + (g^2/2) \Delta p`$ strongly, then $`q(s, x) = p(T - s, x)`$
  solves the same equation with diffusion coefficient $`g(T - s)`$ and drift
  $`-b(T - s, x) + g(T - s)^2 \nabla \log p(T - s, x)`$; a pointwise form applies to solutions on
  $`[0, T]`$. The probability-flow rewriting
  $`-\mathrm{div}(b p) + (g^2/2) \Delta p = -\mathrm{div}((b - (g^2/2) \nabla \log p) \, p)`$ turns
  the Fokker–Planck right-hand side into a continuity equation with the probability-flow velocity.
  These are statements about densities; no SDE is constructed.
- **Stein/Hyvärinen objective (SE-1).** The objective
  $`J(f) = \int (\tfrac{1}{2} \Vert f \Vert_H^2 - f \cdot \nabla \log \pi - \mathrm{div}\, f) \, d\rho`$
  equals $`\tfrac{1}{2} \int \Vert f - v_\star \Vert_H^2 \, d\rho`$ minus half the
  $`H^{-1}`$-weighted relative Fisher information, with $`v_\star = H^{-1} \nabla \log(\pi/\rho)`$.
  Over any class of admissible fields its minimisers are those of the $`H`$-weighted $`L^2(\rho)`$
  distance to $`v_\star`$, and $`v_\star`$ is the a.e.-unique minimiser when it lies in the class:
  Proposition 1 of PFG (Dong–Wang–Lin–Zhang 2023) and the identity of its proof.
- **Linear feature classes (SE-2).** Over a finite feature dictionary, the minimisers of the Stein
  objective are the solutions of the normal equations (empirical and population), and over a linear
  class the minimiser is the weighted $`L^2(\rho)`$ projection of $`v_\star`$. With a fixed
  Frobenius penalty in place of the $`\rho`$-weighted one, the minimiser is finite-feature SVGD
  (PFG, §3.2.1); when the empirical feature second-moment matrix is the identity
  ($`\Sigma_\psi = I`$) and the preconditioner is $`H = \lambda I`$, the empirical Stein objective
  equals the SVGD objective.
- **Denoising (SE-3).** Tweedie's formula $`\nabla \log p_\sigma(y) = (m_\sigma(y) - y)/\sigma^2`$,
  with $`m_\sigma`$ the posterior mean of $`X`$ given $`Y = y`$, for any prior law; the OU posterior
  score $`\nabla \log p_t(y) = (e^{-t} \, \mathbb{E}[X_0 \mid X_t = y] - y)/(1 - e^{-2t})`$ for
  every law of $`X_0`$, Lemma 1 of reverse diffusion Monte Carlo (rdMC; Huang–Dong–Hao–Ma–Zhang
  2024); score propagation through Gaussian channels.
- **Monte Carlo posterior mean (SE-4).** The mean of $`n`$ pairwise independent samples with common
  mean and variance is unbiased, with mean-square error $`\text{variance}/n`$. For the Monte Carlo
  score estimate of rdMC (their Eq. (5), with exact posterior draws, in one dimension) this gives
  unbiasedness, mean-square error of order $`1/n`$ and a Chebyshev tail bound; the bias of an
  inexact inner sampler is treated in GI-2.
- **TV propagation (KR-1).** A Markov kernel does not increase TV. Along two chains, the TV at step
  $`n`$ is at most the initial TV plus the per-step kernel errors, either uniform or averaged under
  a named law (the algorithm's or the exact chain's); a three-chain decomposition averages the
  discretisation error along the ideal discretised chain and the oracle error along the implemented
  chain. TV between two chains also follows from per-step kernel errors in KL, either with one
  Pinsker step per kernel step or with the KL errors summed and a single Pinsker step at the end
  (`Kernels/ErrorPropagationKL`).
- **Reverse kernels (KR-2).** On standard Borel spaces the posterior is the a.e.-unique reverse
  (Bayes) kernel, the multi-step reverse chain recovers the initial marginal, and the posterior has
  an explicit density form.
- **Metropolis–Hastings (MH-1).** Detailed balance
  $`\pi(x) q(x, y) \alpha(x, y) = \pi(y) q(y, x) \alpha(y, x)`$ and invariance of the target for
  general densities with respect to an s-finite reference measure and general normalised proposals;
  MALA on `Fin d → ℝ` leaves the target invariant for every measurable density and every step
  $`h \gt 0`$.
- **Particles (PT-1).** The empirical measure of finitely many particles is pushed forward by a flow
  and by Euler steps, and solves the weak continuity equation; it has no score (CE-05).

## Exact examples (tightness)

- **OU versus the deterministic Gaussian flow (EX-1).** In 1D, from a Gaussian initial law, OU and
  the deterministic Gaussian flow have equal one-time marginals but different two-time laws, with
  closed-form KL dissipation.
- **Discrete population Gaussian flow (EX-2).** In 1D the discrete population Gaussian flow has
  closed-form mean and variance recursions, a contracting relative gap and a KL bound (the discrete
  Gaussian analysis of PFG, Dong–Wang–Lin–Zhang 2023, App. A.6).
- **Tightness (EX-3).** GI-1's KL bound and the sharp proximal rate of PX-2 are attained by explicit
  Gaussian instances, in 1D and on `Fin d → ℝ`, and summing one-step TV errors overshoots by a
  factor of at least $`\sqrt{2n/\pi}`$.

## Counterexamples

- **Marginals do not determine paths (CE-01).** For $`Z \sim \mathcal{N}(0, 1)`$, the pair
  $`(Z, Z)`$ and a pair of independent copies of $`Z`$ have the same one-time marginals and
  different two-time laws.
- **Noise is not the score (CE-02).** For $`Y = X + \sigma Z`$ with independent standard Gaussians
  $`X, Z`$ and $`\sigma \gt 0`$, the regression target $`-Z/\sigma`$ and the score of the law of
  $`Y`$ at $`Y`$ have different laws, so they are not almost surely equal; Tweedie's formula
  identifies them only after conditioning on $`Y`$.
- **ULA is biased (CE-03).** ULA started at its standard Gaussian target does not return it. Among
  centred Gaussians the ULA- and SGLD-invariant laws have variances $`2/(2 - h)`$ and
  $`(2 + h\tau^2)/(2 - h)`$, so SGLD gradient noise ($`\tau \ne 0`$) strictly enlarges the invariant
  variance (the ULA limit for Gaussian targets is Wibisono 2018, Example 2).
- **One Stein test does not identify a law (CE-04).** The Rademacher law satisfies the Stein
  identity of $`\mathcal{N}(0, 1)`$ for every affine test function, but not for
  $`\varphi(x) = x^3`$.
- **Particles have no score (CE-05).** An empirical measure of $`n \ge 1`$ particles on `Fin d → ℝ`,
  $`d \ge 1`$, has no Lebesgue density, hence no score.
- **Empirical Stein objectives can be unbounded (CE-06).** With $`n \le d`$ particles the empirical
  Stein objective over affine features can be unbounded below and have no minimiser (cf. the
  few-samples degeneracy of Gaussian score matching, Hyvärinen 2005, §3.1; Lin–Drton–Shojaie 2016).
- **A contraction along the chain does not imply a uniform one (CE-07).** Reset kernels contract the
  laws of chains carried by a set $`A`$, with rate $`\rho = 0`$, but are not uniform TV contractions
  for any $`\rho \lt 1`$.
- **No law-independent step size (CE-08).** No fixed step size makes the ideal-velocity
  deterministic step a KL descent for all laws, already for Gaussian laws in 1D and on `Fin d → ℝ`
  (a consequence of the Gaussian recursion in Wibisono 2018, Example 4).

## Still Conditional, or not yet proved here

- FL-4 / FL-5 for general (non-OU) flows: the KL first-variation regularity and the Itô input for
  drifts outside the proved classes.
- Fokker–Planck uniqueness for dissipative drifts that are not globally Lipschitz (e.g. quartic or
  double-well Langevin). It is classical under
  $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$ (Bogachev–Krylov–Röckner–Shaposhnikov
  2015, Ch. 9) but not formalised here; the globally Lipschitz case is (FL-6). Without such a growth
  condition uniqueness of probability solutions can fail in every dimension $`d \ge 2`$
  (Bogachev–Krasovitskii–Shaposhnikov 2021, whose Example 4.7 has a smooth drift in $`d = 2`$).
- DiPerna–Lions with merely $`L^1`$ densities.
- Diffusion models: an $`O(1/N^2)`$ (up to logarithmic factors) discretisation contribution to the
  output KL for general (non-Gaussian) data, proved on paper by
  [Jiao–Zhou–Li (2025)](https://arxiv.org/abs/2510.27562) through an auxiliary reverse chain with
  the forward marginals (a device used earlier by Li–Cai, 2024); for $`\sigma^2 = \beta/\alpha^2`$,
  data with $`M \le d`$ and uniform grids, DF-4 and DF-5 show that the chain rule along the true
  reverse chain cannot give it through a full path-KL upper bound and data processing alone. Also
  the $`T \to \infty`$ behaviour of the output (not path) KL for $`\sigma^2 = \beta/\alpha^2`$
  beyond centred isotropic Gaussian data (covered by DF-8).
- PX-2 for non-log-concave targets beyond bounded perturbations of Gaussians (PX-4), without an
  assumed log-Sobolev inequality.

See [`theorem_registry.md`](theorem_registry.md) for the exact remaining hypotheses of each row.
