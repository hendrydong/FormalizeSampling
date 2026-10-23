# Results catalogue

All results below are proved in Lean (status *Verified*) unless marked otherwise; the exact
hypotheses of each result are in [`theorem_registry.md`](theorem_registry.md). $`d`$ is arbitrary
unless "1D" is stated. KL is Mathlib's `klDiv`. TV is $`\sup_A \lvert \mu(A) - \nu(A) \rvert`$
(`TotalVariation.tvSup`).

**Proximal sampler (PX-1 … PX-6)**
- For the proximal sampler of Lee–Shen–Tian (2021), the restricted Gaussian oracle (RGO) is the
  Bayes reverse kernel of its Gaussian forward step, and the target is invariant (PX-1).
- For a target with a functional log-Sobolev inequality $`\mathrm{LSI}(1/\alpha)`$ and a Gaussian
  upper envelope,
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1+\alpha\eta)^{2k}`$ (sharp
  rate; Chen–Chewi–Salim–Wibisono 2022, Thm 3) holds for every $`\rho_0`$ with finite KL, with no
  regularity hypotheses. The backward step is analysed explicitly. *Conditional on the LSI (PX-2).*
- For $`\alpha`$-strongly log-concave targets ($`\alpha \gt 0`$) the same rate holds for every
  $`\rho_0`$ with finite KL and no further hypothesis: the LSI is proved via Bakry–Émery (PX-6).
  This rate, and the invariance of the target (PX-1), are also stated on Mathlib's
  `EuclideanSpace ℝ (Fin d)` (`Samplers/EuclideanTransfer`).
- The rate is attained exactly by isotropic Gaussian targets $`\mathcal{N}(0, \alpha^{-1}I)`$ from
  starts $`\mathcal{N}(m, \alpha^{-1}I)`$ (PX-3, EX-3). That the factor is sharp on Gaussian
  targets is observed by Chen–Chewi–Salim–Wibisono (2022, §4.4); see also Mitra–Wibisono (2025,
  App. G.2).
- Bounded perturbations of Gaussians, $`\pi \propto e^{-\alpha \Vert x \Vert^2/2 - W}`$ with $`W`$
  measurable and bounded (not log-concave in general), have rate
  $`(1+\alpha e^{-\mathrm{osc}\, W} \eta)^{-2k}`$ for every $`\rho_0`$ with finite KL; the LSI comes
  from Holley–Stroock (PX-4), so this is Theorem 3 of Chen–Chewi–Salim–Wibisono (2022) combined with
  the Holley–Stroock perturbation lemma. On `Fin d → ℝ` the same holds for bounded perturbations
  $`\pi \propto e^{-f_0 - W}`$ of any $`\alpha`$-strongly log-concave $`e^{-f_0}`$, with rate
  $`(1+\alpha e^{-\mathrm{osc}\, W} \eta)^{-2k}`$ (`Samplers/ProximalPerturbedGeneralPi`).
- For any target, $`\mathrm{KL}(\rho P \Vert \pi) \le \int \Vert x-y \Vert^2 \, d\gamma/(2\eta)`$
  for every coupling $`\gamma`$. For **every log-concave target $`\pi \propto e^{-f}`$ with $`f`$
  finite and convex, in every dimension** (PX-5),
  $`\mathrm{KL}(\rho_k \Vert \pi) \le \int \Vert x-y \Vert^2 \, d\gamma_0/(2k\eta)`$ for $`k \ge 1`$
  and every coupling $`\gamma_0`$ of $`(\rho_0, \pi)`$, assuming only $`\int e^{-f} \lt \infty`$,
  via shifted composition (Altschuler–Chewi, 2023) and a weak contractive coupling of the RGO. The
  coupling is built from synchronous Euler–Maruyama chains of the Langevin dynamics that leave the
  RGO invariant, with no SDE theory and no optimal transport, then extended to every convex
  potential by smooth approximation and compactness. Chen–Chewi–Salim–Wibisono (2022) state this
  rate with $`1/(k\eta)`$. The constant $`1/(2k\eta)`$ follows from the shifted-composition theorem
  of Altschuler–Chewi (2023, Thm 3.2) and is stated for $`C^2`$ potentials by Pedrotti (2026,
  Cor. 3.5); here $`f`$ need only be finite and convex.

**Diffusion models (DF-1 … DF-10)**

Here $`p_\delta`$ is the data law noised up to the early-stopping time $`\delta = t_1`$, and
$`u_k = e^{2t_k} - 1`$.
- **End-to-end guarantee (DF-1)** for DDPM-type samplers with reverse variance
  $`\sigma_k^2 = \beta_k/\alpha_k^2`$, for any data distribution with finite second moment $`M`$ (no
  density needed), on grids with $`u_{k+1} - u_k \le \kappa u_k`$:
  $`\mathrm{KL}(p_\delta \Vert \text{output}) \le I + (\kappa d/2)(1 + \log(u_N/u_1)) + \sum_k (\beta_k/2) \cdot \mathbb{E}_{p_k} \Vert \hat{s}_k - \nabla \log p_k \Vert^2`$,
  where the initialisation term
  $`I = e^{-2(T-\delta)} \cdot (d(\beta_1 - 1 - \log \beta_1) + \alpha_1^2 M)/2`$ grows like
  $`d \log(1/\delta)`$ as $`\delta \to 0`$. The three terms are the initialisation, discretisation
  and score errors; the discretisation term is linear in the dimension, as in Benton–De
  Bortoli–Doucet–Deligiannidis (2024). The proof uses no SDE theory: Tweedie's formula, an exact
  entropy identity for each reverse step, de Bruijn's identity and the monotonicity of Fisher
  information.
- **Memorisation (DF-2)**: with the exact score of its training set, a diffusion model reproduces
  the training points in the vanishing-noise limit: for every $`\rho, \varepsilon \gt 0`$ there are
  sampler parameters (early stopping, grid) giving output mass $`\ge 1 - \varepsilon`$ within
  distance $`\rho`$ of the training set. This is known for the continuous-time sampler (Pidstrigach
  2022, Cor. 1; Li–Chen–Li 2024, Thm 4.3; see also Gu et al. 2023); here it is proved for the
  discretised sampler.
- **Stochastic vs deterministic (DF-3, DF-7, DF-9)**: there are uniformly $`\varepsilon`$-accurate
  scores for which the deterministic sampler (probability-flow ODE / DDIM) is at TV distance 1 from
  $`p_\delta`$ while DDPM with $`\sigma_k^2 = \beta_k/\alpha_k^2`$ and the same score satisfies the
  DF-1 bound (construction of Li–Wei–Chen–Chi 2023, §3.2). The same holds, with TV
  $`\ge 1 - \eta`$, for an error that is an analytic function of the exact update (DF-7); Lean
  proves a lower bound $`(2^m - 1)/\lvert b_2 \rvert`$ on its Lipschitz constant for the
  (non-explicit) $`m`$ used, and its growth as $`\eta \to 0`$ is numerical only. The closest earlier
  result is Li–Di–Gu (2024, Thm 3.1): a smooth score within $`\varepsilon`$ of the true score
  everywhere for which the continuous-time probability-flow ODE stays a fixed TV distance away
  from Gaussian data, however small $`\varepsilon`$ is. Conversely (DF-9), if the exact-score steps
  are Lipschitz, a uniformly $`\varepsilon`$-accurate score keeps the deterministic output within an
  explicit distance of the exact-score deterministic output under a coupling ($`W_\infty`$, $`W_2`$
  bounds); comparison with the data itself is not proved. Li–Wei–Chen–Chi suggest a Wasserstein
  metric as a way around their example; DF-9 states the pairing of TV-far and transport-close as a
  theorem. Convolving both the learned output $`q_k`$ and the exact-score output $`q^*_k`$ with one
  Gaussian step $`\mathcal{N}(0, \tau I)`$ turns the coupling bound $`B`$ into
  $`\mathrm{KL}(\mathcal{N}_\tau * q_k \Vert \mathcal{N}_\tau * q^*_k) \le B^2/(2\tau)`$ and, by
  Pinsker, $`\mathrm{TV}(\mathcal{N}_\tau * q_k, \mathcal{N}_\tau * q^*_k) \le B/(2\sqrt{\tau})`$;
  the learned score needs no regularity, and no bound against the data is proved. This is the
  standard Gaussian-regularisation bound (joint convexity of KL, as for the proximal sampler in
  PX-2); adding a little noise to pass from a Wasserstein bound for a deterministic sampler to KL or
  TV is the device of Chen–Chewi–Lee–Li–Lu–Salim (2023, §4) and Lyu–Chen–Feng (2023, Lemma 12).
- **Long horizon, small Lipschitz error (DF-10)**: a small Lipschitz constant does not rescue the
  deterministic sampler once the horizon is long. The error
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
- **Reverse variance (DF-4)**: with reverse variance $`\sigma_k^2 = \beta_k`$, on a grid that is
  geometric up to some index ($`u_{k+1} - u_k \le \kappa u_k`$, $`1 \le \kappa u_m \le 1 + \kappa`$)
  and arbitrary afterwards, the discretisation error is bounded by a constant depending on
  $`\kappa, u_1, d, M`$ only, not on $`N`$ or $`T`$; with $`\sigma_k^2 = \beta_k/\alpha_k^2`$ and
  data with $`M \le d`$ the summed per-step error has a lower bound linear in $`T`$ on a uniform
  grid of fixed step. Bounds with no term growing in $`T`$ are known for $`\sigma_k^2 = \beta_k`$:
  Koike (2026, Thm 3.1 and Remark 3.2) for the DDPM sampler, as the Euler–Maruyama scheme of the
  Föllmer process, and Conforti–Durmus–Gentiloni Silveri (2023, Cor. 1) for an exponential-integrator
  scheme with step variance $`\beta_k`$. The optimal per-step variance is the Analytic-DPM one
  (Bao et al. 2022), whose data-free upper bound is $`\beta_k/\alpha_k^2`$ (their App. D,
  Cor. 3).
- **Path-space KL (DF-5)**: the KL between the reversed forward path and the sampler path equals the
  initial KL plus the sum of per-step errors. With $`\sigma^2 = \beta/\alpha^2`$, data with
  $`M \le d`$ and a uniform grid of fixed step it has a lower bound linear in $`T`$ for every mean
  map. That the path KL is of order of the step size in the worst case is noted by Benton et al.
  (2024, §4; point-mass data) and Li–Yan (2024, §3.1), after Chen et al. (2023, Thm 7) for the
  critically damped Langevin sampler; we have not found a non-asymptotic bound stated for every data
  law with $`M \le d`$ and every mean map. With $`\sigma^2 = \beta`$, the exact posterior mean and
  the grid conditions of DF-4, it is bounded uniformly in $`N`$ and $`T`$ at fixed
  $`t_1, \kappa, d, M`$. Learned scores add
  $`\sum_k \beta_k/(2\alpha_k^2) \, \mathbb{E}_{p_k} \Vert \hat{s}_k - \nabla \log p_k \Vert^2`$,
  which also needs uniform control for a uniform total-error bound. For exact scores and Gaussian
  data $`\mathcal{N}(0, vI)`$ with $`\sigma^2 = \beta/\alpha^2`$, DF-8 bounds the output KL
  uniformly in $`T`$ at fixed $`t_1`$ and maximal step: for every $`T`$ when $`v \le 1`$, and once
  $`(v - 1)e^{-2(2T - t_1)}s_1 \lt 1`$ when $`v \gt 1`$.
- **Sharpness (DF-6)**: with $`\sigma^2 = \beta/\alpha^2`$ and the exact posterior mean, the
  per-step error sum is bounded below by order $`1/N`$ per unit of log-time for every data law with
  finite second moment $`M`$, minus a term depending on $`M`$ that does not shrink as $`N`$ grows,
  so DF-1's discretisation term is sharp at path level over long horizons. On a uniform grid over a
  fixed interval, a lower bound of order $`1/N`$ is proved for data with $`M \le d`$ (DF-4, DF-5);
  for a point mass at the origin the sum is explicit and, among grids with the same $`N`$, $`u_1`$
  and $`u_N`$, the geometric grid minimises it (Chen–Lee–Lu 2023, App. B, show by a convexity
  argument in log-time that geometric steps minimise their upper bound). Sun–Poor–Zhang (2026,
  Thm 3) give an asymptotic, continuous-time lower bound on the path KL of a related sampler, with
  Gaussian data as the extremal case. The faster decay of the output KL seen numerically
  (`../showcase/ddpm_rate.py`, data with $`M \le d`$) cannot be recovered by bounding the full KL
  along the true reverse chain and then applying data processing alone.
- **Output vs path (DF-8)**: for standard Gaussian data $`\mathcal{N}(0, I)`$, the exact score,
  $`\sigma^2 = \beta/\alpha^2`$, a uniform grid with step $`h`$ ($`e^{2h} \le 2`$) over a fixed
  interval $`0 \lt t_1 \lt T`$, the output KL is $`\Theta(d h^2)`$ (upper and lower bounds of the
  same order, constants not matched), while the path KL is $`\ge d(T - t_1)h/(1+h)`$. For
  $`\mathcal{N}(0, vI)`$ with $`v \lt 1`$ the upper bound is $`O(d h^2)`$ plus an initialisation
  term driven by $`(1 - v)e^{-2(2T - t_1)}`$, exponentially small in $`T`$ but not vanishing as
  $`h \to 0`$ at fixed $`T`$. For $`v \gt 1`$ the bound is
  $`d((e^{2h} - 1)^2 + (\varepsilon/(1 - \varepsilon))^2)/4`$ whenever
  $`(v - 1)e^{-2(2T - t_1)}s_1 \le \varepsilon \lt 1`$; its $`\varepsilon^2`$ initialisation term
  likewise does not vanish as $`h \to 0`$ at fixed $`T`$. With $`\sigma^2 = \beta`$ the sampler is
  exact for $`v = 1`$. Jiao–Zhou–Li (2025, Thm 2) prove an output lower bound of order $`d/N^2`$
  for $`\mathcal{N}(0, \lambda I)`$ data with $`\lambda \ge 2`$ on their schedule; DF-8 covers
  $`v = 1`$ on a uniform grid over a fixed interval, with explicit constants on both sides.

**Log-Sobolev inequalities (KL-5, KL-6)**
- Gaussian LSI.
- Gross's inequality, tensorisation, stability under convolution, Holley–Stroock.
- LSI transfers through 1D differentiable maps with $`\lvert T' \rvert \le K`$ (constant $`K^2 C`$)
  and through coordinatewise maps with $`\lvert T_i' \rvert \le 1`$; general Lipschitz push-forwards
  are not treated.
- **Bakry–Émery**: if $`f - \alpha \Vert x \Vert^2/2`$ is convex, then $`e^{-f}`$ satisfies
  $`\mathrm{LSI}(1/\alpha)`$. The 1D case uses the Caffarelli contraction. In dimension $`d`$ the
  proof goes through a formalisation of Prékopa–Leindler (Bobkov–Ledoux route).

**KL toolkit (KL-1 … KL-4)**
- Pinsker; the chain rule and data processing for kernels; Gaussian KL; tensorisation.
- TV between two Markov chains from per-step kernel errors in KL, either with one Pinsker step per
  kernel step or with the KL errors summed and a single Pinsker step at the end
  (`Kernels/ErrorPropagationKL`).
- Convexity of KL, joint convexity in kernel/coupling form, and lower semicontinuity
  (Donsker–Varadhan).
- The approximation principle "a contraction for warm starts implies one for all finite-KL
  starts".

**Gaussian-increment chains (GI-1, GI-2)**
- KL accumulation
  $`\mathrm{KL}(\nu_K \Vert \mu_K) \le \mathrm{KL}(\nu_0 \Vert \mu_0) + (h/4) \sum_k \int \Vert b - \hat{b} \Vert^2 \, d\nu_k`$,
  with the error averaged under the algorithm's law. One Pinsker at the end gives TV with no
  $`\sqrt{K}`$ loss. This is the standard route of diffusion-model analyses (Chen–Lee–Lu 2023;
  Chen et al. 2023), stated here for Gaussian-increment chains.
- The bound is attained (EX-3).
- Random and inexact score oracles: the drift is re-estimated at every step from fresh posterior
  draws, possibly made by an inexact inner sampler, as in reverse diffusion Monte Carlo (rdMC;
  Huang–Dong–Hao–Ma–Zhang 2024). The squared bias of the inner sampler's mean is bounded by a
  coupling or, for a $`\sigma^2`$-sub-Gaussian exact posterior, by $`2\sigma^2`$ times its KL
  error (cf. their Eqs. (17)–(18)). For a single Gaussian posterior draw
  $`y \sim \mathcal{N}(x, tI)`$, centred at the current state with known covariance, and plug-in
  drift $`b(x) + c(y - x)`$, the one-step law is $`\mathcal{N}(x + h b(x), (2h + (hc)^2 t) I)`$: the
  drift noise adds variance $`(hc)^2 t`$. If $`(hc)^2 t \le 2h`$, injecting variance
  $`2h - (hc)^2 t`$ instead of $`2h`$ makes the one-step law equal to the exact-drift EM step at
  every $`x`$ ($`\mathrm{KL} = \mathrm{TV} = 0`$). Without this correction, for $`h \gt 0`$, the KL
  from the random-oracle step to the EM step is $`d(u - \log(1 + u))/2 \le d u^2/2`$ with
  $`u = h c^2 t/2`$, i.e. $`O(d h^2)`$ for fixed $`c, t`$, against the conditional-KL bound
  $`d u/2 = d h c^2 t/4`$. Both are Gaussian instances of stochastic-gradient MCMC facts: zero-mean
  drift noise enters one step at second order in the step size (Welling–Teh 2011, §3), and
  subtracting its covariance from the injected noise makes the total noise exact
  (Ahn–Korattikara–Welling 2012; Chen–Fox–Guestrin 2014, Eq. (13); Ma–Chen–Fox 2015, Eq. (9)).

**Flows (FL-1 … FL-6, DT-1)**
- KL first variation; exact and approximate dissipation; decay with additive error (FL-4,
  *Conditional* on an LSI along the flow; unconditional for the OU flow with Gaussian target).
  For the preconditioned functional gradient flow (PFG; Dong–Wang–Lin–Zhang 2023) this includes
  their Theorem 1 with their constants, *Conditional* on their approximation condition [A3] and
  log-Sobolev assumption [A4] (FL-3, FL-4); the dissipation identity for the exact velocity (FL-2)
  is the computation in the proof of that theorem (App. A.5) with no velocity error.
- The OU/Langevin flow with Gaussian target $`\mathcal{N}(0, vI)`$ and rate $`a`$ has the sharp
  decay $`\mathrm{KL} \le e^{-2at} \mathrm{KL}_0`$ from every initial law with finite KL and finite
  second moment. Along the OU probability flow from any law with finite second moment,
  $`\frac{d}{dt} \mathrm{KL} = -av \cdot I`$ (relative Fisher information $`I`$) for $`t \gt 0`$ and
  the decay hold with every hypothesis discharged. The library's sufficient regularity bundle
  `TransportKLRegularity`, under which the generic decay theorem applies, is proved under a fourth
  moment; for that bundle the fourth moment is sharp on the polynomial scale (1D counterexamples
  with a finite third moment, and with a finite second moment).
- Noise–score equivalence of one-time marginals (FL-5, *Conditional* on the law curve solving weak
  Fokker–Planck (the Itô input) and on continuity-equation uniqueness; unconditional for OU with an
  isotropic Gaussian initial law).
- **Fokker–Planck well-posedness without SDE theory**:
  - Uniqueness of weak solutions for continuous bounded drifts, and for $`-a x`$ plus a
    bounded drift (so OU is well-posed), $`D \gt 0`$.
  - Uniqueness for every drift jointly continuous in $`(t, x)`$ and globally Lipschitz in $`x`$
    uniformly on each $`[0, T]`$ (unbounded allowed), $`D \gt 0`$, with no moment assumption (FL-6):
    Lipschitz drifts and Langevin with Lipschitz $`\nabla U`$ are well-posed, and for autonomous
    drifts every solution is the limit of the Euler–Maruyama laws. Uniqueness for these drifts is
    a case of the classical theorem for drifts with
    $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$ (Bogachev–Krylov–Röckner–Shaposhnikov,
    *Fokker–Planck–Kolmogorov Equations*, 2015, Ch. 9).
  - Existence for Lipschitz drifts with linear growth (as weak limits of Euler–Maruyama laws),
    for locally Lipschitz dissipative drifts (by truncation), and for time-dependent drifts that are
    jointly continuous and Lipschitz in $`x`$ uniformly on each $`[0, T]`$.
  - Langevin law curves, including quartic and double-well potentials.
- **Continuity-equation uniqueness**: for jointly continuous velocities with linear growth that are
  locally Lipschitz in $`x`$ uniformly on each $`[0, T]`$, without flow maps, by approximate
  duality. **DiPerna–Lions** in every dimension for $`W^{1,1}_{\mathrm{loc}}`$ velocities with
  bounded divergence and linear growth, bounded densities, and for $`L^p`$ densities ($`p \gt 1`$)
  with $`W^{1,q}_{\mathrm{loc}}`$ velocities (commutator lemmas and renormalisation), for autonomous
  velocities and probability-density solutions.
- Deterministic-step descent
  $`\mathrm{KL}((\mathrm{id}+\eta v)_\# \rho \Vert \pi) \le \mathrm{KL}(\rho \Vert \pi) - \eta \cdot (\text{dissipation}) + O(\eta^2)`$.
  No step size works for all laws (CE-08).

**Identities, estimation, kernels and particles (ID, SE, KR, MH, PT)**
- Stein, Tweedie and weak generator identities; the OU posterior score
  $`\nabla \log p_t(y) = (e^{-t} \, \mathbb{E}[X_0 \mid X_t = y] - y)/(1 - e^{-2t})`$ for every law
  of $`X_0`$, which is Lemma 1 of rdMC, stated there for targets with a density (SE-3);
  reverse-time Fokker–Planck rewriting.
- The Stein/Hyvärinen objective of PFG: over any class of admissible fields its minimisers are
  those of the $`H`$-weighted $`L^2(\rho)`$ distance to $`H^{-1} \nabla \log(\pi/\rho)`$
  (Proposition 1 of Dong–Wang–Lin–Zhang 2023; SE-1). Linear feature classes: with a fixed
  Frobenius penalty in place of the $`\rho`$-weighted one, the minimiser is finite-feature SVGD
  (their §3.2.1); when the empirical feature second-moment matrix is the identity
  ($`\Sigma_\psi = I`$) and the preconditioner is $`H = \lambda I`$, the empirical Stein objective
  equals the SVGD objective.
- Monte Carlo posterior means: unbiased, with mean-square error $`\text{variance}/n`$; for the
  Monte Carlo score estimate of rdMC (their Eq. (5), with exact posterior draws, in one dimension)
  this gives unbiasedness and mean-square error of order $`1/n`$.
- TV propagation for inexact kernels.
- Reverse (Bayes) kernels: the posterior is the a.e.-unique reverse kernel, and the multi-step
  reverse chain recovers the initial marginal (KR-2).
- Metropolis–Hastings and MALA detailed balance.
- Particles: the empirical measure is pushed forward by a flow and by Euler steps, and solves
  the weak continuity equation (PT-1).

**Exact examples (EX-1 … EX-3)**
- 1D, from a Gaussian initial law: OU and the deterministic Gaussian flow have equal one-time
  marginals but different two-time laws, with closed-form KL dissipation (EX-1).
- The discrete population Gaussian flow (1D) has closed-form mean and variance recursions, a
  contracting relative gap and a KL bound (EX-2; the discrete Gaussian analysis of PFG,
  Dong–Wang–Lin–Zhang 2023, App. A.6).
- GI-1's KL bound and the sharp proximal rate are attained by explicit Gaussian instances, and
  summing one-step TV errors overshoots by a factor of at least $`\sqrt{2n/\pi}`$ (EX-3).

**Counterexamples (CE-01 … CE-08)**
- Marginals do not determine path laws.
- Noise is not the score.
- ULA is biased (for Gaussian targets: Wibisono 2018, Example 2).
- One Stein test does not identify a law.
- Particles have no score.
- Empirical Stein objectives can be unbounded (with $`n \le d`$ particles; cf. the few-samples
  degeneracy of Gaussian score matching, Hyvärinen 2005, §3.1; Lin–Drton–Shojaie 2016).
- Contraction along a chain does not give a uniform contraction: reset kernels contract the laws
  of chains carried by a set, but are not uniform TV contractions.
- No fixed step size makes the ideal-velocity deterministic step a KL descent for all laws (a
  consequence of the Gaussian recursion in Wibisono 2018, Example 4).

Still **Conditional**, or not yet proved here:
- FL-4 / FL-5 for general (non-OU) flows: the KL first-variation regularity and the Itô input
  for drifts outside the proved classes.
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
