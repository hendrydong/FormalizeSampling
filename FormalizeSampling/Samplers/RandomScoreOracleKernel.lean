module

public import FormalizeSampling.Samplers.RandomScoreOracle
public import FormalizeSampling.Kernels.KernelPi
public import FormalizeSampling.Foundations.HeatKernelPi

/-!
# GI-2 with a state-dependent posterior kernel

Status: **Verified**.

The Monte Carlo theorems of `Samplers/RandomScoreOracle.lean` take the draw kernel `R k` as a
parameter together with the hypothesis `hR : ∀ k x, R k x = (post k x)^{⊗N}`. Mathlib v4.35
has no product of kernels, so before `Kernels/KernelPi.lean` such an `R` could only be built for
state-independent `post`. With `R k := KernelPi.piConst N (post k)` the hypothesis `hR` holds by
definition (`KernelPi.piConst_apply`) for every Markov kernel `post k`, in particular for
state-dependent posteriors.

## Main results

* `tvSup_piConstMonteCarloChain_le_sqrt`: GI-2 Monte Carlo sample-size bound
  `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² /(8N) ∫ V_k dν_k)` for `N`
  i.i.d. draws from an arbitrary Markov kernel `post k` (no `hR` hypothesis).
* `tvSup_piConstBiasedMonteCarloChain_le_sqrt`: the inexact-inner-sampler version (squared
  bias plus variance over `N`), again with no `hR` hypothesis.
* Non-vacuity, state-dependent posterior `post k = heatKernelPi (t k)`, i.e.
  `post k x = N(x, t_k I)`:
  `memLp_coord_heatKernelPi`, `integral_coord_heatKernelPi`, `variance_coord_heatKernelPi`
  (square-integrable, mean `x`, coordinate variance `t_k`), `measurable_plugInDrift`, and
  `tvSup_heatKernelPiMonteCarloChain_le_sqrt`: with the plug-in drift
  `b̂ k (x, ω) = b k x + c k (m̂(ω) - x)` and all hypotheses discharged except the chain
  recursions and `KL(ν 0 ‖ μ 0) < ∞`,
  `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² d t_k /(8N))`.
* **Gaussian posterior draws and noise compensation**, the Gaussian case of two stochastic-gradient
  MCMC facts: zero-mean drift noise enters one step at second order in the step size
  (Welling–Teh 2011, §3), and subtracting its covariance from the injected noise makes the total
  noise exact (Ahn–Korattikara–Welling 2012, arXiv:1206.6380, §3.3; Chen–Fox–Guestrin 2014,
  arXiv:1402.4102, Eq. (13); Ma–Chen–Fox 2015, arXiv:1506.04696, Eq. (9)):
  - `bind_gaussianReal_affine_sub`, `bind_heatKernelPi_affine_sub`: mixing
    `N(m + α (y - x), s I)` over a Gaussian posterior draw `y ~ heatKernelPi t x = N(x, t I)`
    gives `N(m, (s + α² t) I)`;
  - `randomEmKernel_heatKernelPi_apply`: the one-step marginal of a single-draw Gaussian score
    oracle `b x + c (y - x)` with outer variance `2 h` is `N(x + h b x, (2 h + (h c)² t) I)`;
  - `bind_heatKernelPi_compensated_eq_emKernelPi`: when `(h c)² t ≤ 2 h`, injecting variance
    `2 h - (h c)² t` instead of `2 h` makes the one-step marginal law equal to
    `emKernelPi h b hb x` (`KL = 0`, `tvSup = 0`);
  - `klDiv_randomEmKernel_heatKernelPi_eq_and_le`,
    `klDiv_and_tvSup_heatKernelPiSingleDrawChain_le`: without the correction, for `h ≠ 0`,
    `KL(randomEmKernel x ‖ emKernelPi x) = d (u - log (1 + u)) / 2 ≤ d h² c⁴ t² / 8` with
    `u = h c² t / 2`, against the GI-2 conditional-KL bound `d h c² t / 4`; the quadratic bound
    is the smaller one when `u < 1`.

The KL, averaged and coupling corollaries in `Samplers/RandomScoreOracleInner.lean` take the same
`hR`; it is discharged for `R k := KernelPi.piConst N (post k)` by
`fun k x => KernelPi.piConst_apply N (post k) x`.

## Not proved here

* Draws that are not independent given the state (e.g. successive outputs of one inner MCMC
  run) are not covered: `R k x` is exactly the product `(post k x)^{⊗N}`.
* The Gaussian-draw results cover one draw from `N(x, t I)`, centred at the current state, with
  `t` known exactly; `N` draws, estimated or state-dependent covariances, and a chain built from
  the compensated step are not formalised.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.GaussianIncrement

open KernelPi

section MonteCarloKernel

variable {d N : ℕ} {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {post : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (post k)]
  {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {c : ℕ → ℝ}
  {bhat : ℕ → (Fin d → ℝ) × (Fin N → Fin d → ℝ) → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-2, Monte Carlo sample-size bound, state-dependent posterior.** Let `post k` be any
Markov kernel (the law of the draws may depend on the current state `x`), and let the
algorithm draw `ω ~ (post k x)^{⊗N}` through the product kernel `piConst N (post k)`. If
`post k x` is square-integrable with mean `m k x`, the drift is the plug-in
`b̂ k (x, ω) = b k x + c k (m̂(ω) - m k x)`, `KL(ν 0 ‖ μ 0) < ∞` and `V k` is `ν k`-integrable,
then `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h k c k² / (8N) ∫ V k dν_k)`, with
`V k x = ∑ᵢ Var_{post k x}(yᵢ)`. This is `tvSup_monteCarloChain_le_sqrt` with its product
hypothesis `hR` discharged. -/
theorem tvSup_piConstMonteCarloChain_le_sqrt (hN : 0 < N)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hm : ∀ k x i, ∫ y, y i ∂(post k x) = m k x i)
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) =
      randomEmKernel (h k) (piConst N (post k)) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / (8 * N) *
        ∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) :=
  tvSup_monteCarloChain_le_sqrt (hb := hb) (hbh := hbh)
    (R := fun k => piConst N (post k)) hN (fun k x => piConst_apply N (post k) x) hq hm hbhat
    hμ hν n hKL0 hV

/-- **GI-2 with an inexact inner sampler, state-dependent posterior.** As
`tvSup_biasedMonteCarloChain_le_sqrt`, with the draws `ω ~ (post k x)^{⊗N}` produced by the
product kernel `piConst N (post k)` of an arbitrary Markov kernel `post k` (whose mean need not
be `m k x`), so the product hypothesis `hR` is gone:
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k² / 8) ∫ B k dν_k)`, with
`B k x = ∑ᵢ ((mean of post k x)ᵢ - m k x i)² + ∑ᵢ Var_{post k x}(yᵢ) / N`. -/
theorem tvSup_piConstBiasedMonteCarloChain_le_sqrt (hN : 0 < N)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) =
      randomEmKernel (h k) (piConst N (post k)) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * ∫ x, ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
        variance (fun y : Fin d → ℝ => y i) (post k x) / N) ∂(ν k)) :=
  tvSup_biasedMonteCarloChain_le_sqrt (hb := hb) (hbh := hbh)
    (R := fun k => piConst N (post k)) hN (fun k x => piConst_apply N (post k) x) hq hbhat
    hμ hν n hKL0 hB

end MonteCarloKernel

section HeatPosterior

open HeatKernelPi

variable {d : ℕ}

/-- The coordinates of the Gaussian kernel `heatKernelPi t x = N(x, t I)` are
square-integrable. -/
theorem memLp_coord_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) (i : Fin d) :
    MemLp (fun y : Fin d → ℝ => y i) 2 (heatKernelPi t x) := by
  rw [heatKernelPi_apply]
  exact (memLp_id_gaussianReal 2).comp_measurePreserving
    (measurePreserving_eval (fun j => gaussianReal (x j) t) i)

/-- The mean of `heatKernelPi t x = N(x, t I)` is `x`: `∫ yᵢ d(heatKernelPi t x) = xᵢ`. -/
theorem integral_coord_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) (i : Fin d) :
    ∫ y, y i ∂(heatKernelPi t x) = x i := by
  have hmp := measurePreserving_eval (fun j => gaussianReal (x j) t) i
  have e := integral_map (f := id) (measurable_pi_apply i).aemeasurable
    aestronglyMeasurable_id (μ := Measure.pi fun j => gaussianReal (x j) t)
  have hm : (Measure.pi fun j => gaussianReal (x j) t).map (fun y : Fin d → ℝ => y i) =
      gaussianReal (x i) t := hmp.map_eq
  rw [hm] at e
  rw [heatKernelPi_apply]
  exact e.symm.trans integral_id_gaussianReal

/-- The coordinate variances of `heatKernelPi t x = N(x, t I)` are `t`. -/
theorem variance_coord_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) (i : Fin d) :
    variance (fun y : Fin d → ℝ => y i) (heatKernelPi t x) = t := by
  have hmp := measurePreserving_eval (fun j => gaussianReal (x j) t) i
  have := variance_map (X := id) (μ := Measure.pi fun j => gaussianReal (x j) t)
    (Y := fun y : Fin d → ℝ => y i) measurable_id.aemeasurable
    (measurable_pi_apply i).aemeasurable
  have hm : (Measure.pi fun j => gaussianReal (x j) t).map (fun y : Fin d → ℝ => y i) =
      gaussianReal (x i) t := hmp.map_eq
  rw [hm, variance_id_gaussianReal] at this
  rw [heatKernelPi_apply, this]
  rfl

/-- The plug-in drift `(x, ω) ↦ b x + c (m̂(ω) - x)` (empirical mean `m̂` of `N` draws, centred
at the state `x`) is measurable when `b` is. -/
theorem measurable_plugInDrift {N : ℕ} {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b)
    (c : ℝ) :
    Measurable fun p : (Fin d → ℝ) × (Fin N → Fin d → ℝ) => b p.1 + c • (empMean p.2 - p.1) := by
  unfold empMean
  fun_prop

/-- **GI-2 non-vacuity: Gaussian posterior centred at the state.** Take the state-dependent
posterior `post k x = heatKernelPi (t k) x = N(x, t_k I)`, `N > 0` i.i.d. draws
`ω ~ (post k x)^{⊗N}` via `piConst`, and the plug-in drift `b̂ k (x, ω) = b k x + c k (m̂(ω) - x)`
(centred at the exact posterior mean `x`). For any measurable exact drifts `b k`, the
exact-drift chain `μ` and the Monte Carlo chain `ν` started from probability measures with
`KL(ν 0 ‖ μ 0) < ∞` satisfy
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² d t_k / (8N))`.
All moment and integrability hypotheses of `tvSup_piConstMonteCarloChain_le_sqrt` are
discharged. -/
theorem tvSup_heatKernelPiMonteCarloChain_le_sqrt {N : ℕ} (hN : 0 < N) {h : ℕ → ℝ≥0}
    {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hb : ∀ k, Measurable (b k)) (c : ℕ → ℝ)
    (t : ℕ → ℝ≥0) {μ ν : ℕ → Measure (Fin d → ℝ)}
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (piConst N (heatKernelPi (t k)))
      (fun p : (Fin d → ℝ) × (Fin N → Fin d → ℝ) => b k p.1 + c k • (empMean p.2 - p.1))
      (measurable_plugInDrift (hb k) (c k)) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 * (d * t k) / (8 * N)) := by
  have hprob := ErrorPropagation.isProbabilityMeasure_of_comp_succ hν
  have hV : ∀ k, (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i)
      (heatKernelPi (t k) x)) = fun _ => (d : ℝ) * t k := fun k => by
    funext x
    simp [variance_coord_heatKernelPi]
  refine (tvSup_piConstMonteCarloChain_le_sqrt (hb := hb) (m := fun _ x => x)
    (post := fun k => heatKernelPi (t k)) hN (fun k x i => memLp_coord_heatKernelPi _ x i)
    (fun k x i => integral_coord_heatKernelPi _ x i) (fun _ _ _ => rfl) hμ hν n hKL0
    (fun k => by rw [hV k]; exact integrable_const _)).trans_eq ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hprob k
  rw [hV k, integral_const, probReal_univ, one_smul]
  ring

/-! ### Gaussian score oracles: variance absorption and noise compensation -/

/-- **One-dimensional affine Gaussian marginalisation.** Mixing `N(m + α (u - x), s)` over
`u ~ N(x, t)` absorbs the inner variance `t` into the outer variance `s`:
`(gaussianReal x t).bind (u ↦ gaussianReal (m + α (u - x)) s) = gaussianReal m (s + α² t)`. -/
theorem bind_gaussianReal_affine_sub (x m α : ℝ) (t s : ℝ≥0) :
    (gaussianReal x t).bind (fun u => gaussianReal (m + α * (u - x)) s) =
      gaussianReal m (s + NNReal.mk (α ^ 2) (sq_nonneg α) * t) := by
  have hm1 : Measurable (fun z : ℝ => gaussianReal z s) := by
    simpa [one_mul] using OU.measurable_gaussianReal_affine 1 s
  have hm2 : Measurable (fun v : ℝ => gaussianReal (m - α * x + v) s) :=
    hm1.comp (measurable_const_add (m - α * x))
  have h1 : (fun u : ℝ => gaussianReal (m + α * (u - x)) s) =
      fun u => gaussianReal (m - α * x + α * u) s := by
    funext u; congr 1; ring
  rw [h1, ← Measure.bind_map (f := fun u => α * u) (g := fun v => gaussianReal (m - α * x + v) s)
    (measurable_const_mul α).aemeasurable hm2.aemeasurable, gaussianReal_map_const_mul]
  have h3 : (fun v : ℝ => gaussianReal (m - α * x + v) s) =
      fun v => gaussianReal (v + (m - α * x)) s := by
    funext v; congr 1; ring
  rw [h3, ← Measure.bind_map (f := fun v => v + (m - α * x)) (g := fun z => gaussianReal z s)
    (measurable_add_const (m - α * x)).aemeasurable hm1.aemeasurable,
    gaussianReal_map_add_const, OU.bind_heat]
  congr 1
  · ring
  · exact add_comm _ s

/-- **Isotropic affine Gaussian marginalisation on `Fin d → ℝ`.** Mixing the product Gaussian
`N(m + α (y - x), s I)` over a single Gaussian posterior draw `y ~ heatKernelPi t x = N(x, t I)`
absorbs the posterior variance `t` into the step variance `s`:
`(heatKernelPi t x).bind (y ↦ N(m + α (y - x), s I)) = N(m, (s + α² t) I)`. -/
theorem bind_heatKernelPi_affine_sub (x m : Fin d → ℝ) (α : ℝ) (t s : ℝ≥0) :
    (heatKernelPi t x).bind
        (fun y : Fin d → ℝ => Measure.pi fun i => gaussianReal (m i + α * (y i - x i)) s) =
      Measure.pi fun i => gaussianReal (m i) (s + NNReal.mk (α ^ 2) (sq_nonneg α) * t) := by
  have hm : Measurable (fun y : Fin d → ℝ =>
      Measure.pi fun i => gaussianReal (m i + α * (y i - x i)) s) :=
    (measurable_heatKernelPi s).comp
      (by fun_prop : Measurable fun (y : Fin d → ℝ) i => m i + α * (y i - x i))
  have hm1 : Measurable (fun z : ℝ => gaussianReal z s) := by
    simpa [one_mul] using OU.measurable_gaussianReal_affine 1 s
  refine (Measure.pi_eq fun S hS => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hS) hm.aemeasurable]
  simp_rw [Measure.pi_pi]
  rw [heatKernelPi_apply t, MeasureHelpers.lintegral_pi_prod _
    (fun i u => gaussianReal (m i + α * (u - x i)) s (S i))
    (fun i => ((OU.heatKernel s).measurable_coe (hS i)).comp (by fun_prop))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := bind_gaussianReal_affine_sub (x i) (m i) α t s
  rw [← h, Measure.bind_apply (f := fun u => gaussianReal (m i + α * (u - x i)) s) (hS i)
    (hm1.comp (by fun_prop : Measurable fun u => m i + α * (u - x i))).aemeasurable]

/-- The single-draw plug-in drift `(x, y) ↦ b x + c (y - x)` is measurable when `b` is. -/
theorem measurable_singleDrawDrift {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b) (c : ℝ) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 + c • (p.2 - p.1) := by
  fun_prop

/-- **Exact marginal law of a random-oracle EM step with a Gaussian posterior draw.** Drawing
`y ~ heatKernelPi t x = N(x, t I)` and stepping to `N(x + h (b x + c (y - x)), 2 h I)` produces
the exact isotropic Gaussian marginal `N(x + h b x, (2 h + (h c)² t) I)`: the random-score
variance `(h c)² t` is absorbed into the outer Gaussian variance `2 h`. -/
theorem randomEmKernel_heatKernelPi_apply (h : ℝ≥0) {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : Measurable b) (c : ℝ) (t : ℝ≥0) (x : Fin d → ℝ) :
    randomEmKernel h (heatKernelPi t)
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 + c • (p.2 - p.1))
        (measurable_singleDrawDrift hb c) x =
      Measure.pi fun i =>
        gaussianReal (x i + h * b x i) (2 * h + NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t) := by
  rw [randomEmKernel_apply]
  have h1 : ( ⇑(Kernel.comap (randDriftKernel h
      (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 + c • (p.2 - p.1))
      (measurable_singleDrawDrift hb c)) (fun y => (x, y)) measurable_prodMk_left)) =
      fun y : Fin d → ℝ => Measure.pi fun i =>
        gaussianReal ((x i + h * b x i) + (h * c) * (y i - x i)) (2 * h) := by
    funext y
    rw [Kernel.comap_apply, randDriftKernel_apply, emKernelPi_apply]
    congr 1; funext i; congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [h1]
  exact bind_heatKernelPi_affine_sub x (fun i => x i + h * b x i) (h * c) t (2 * h)

/-- **Noise compensation for a Gaussian score oracle.** If the posterior draw
`y ~ heatKernelPi t x = N(x, t I)` satisfies `(h c)² t ≤ 2 h`, injecting variance
`s = 2 h - (h c)² t` instead of `2 h` makes the one-step marginal law equal to the exact-drift EM
step `emKernelPi h b hb x = N(x + h b x, 2 h I)`, so `KL` and `tvSup` between them vanish. This
is the Gaussian case of the stochastic-gradient MCMC noise correction (Chen–Fox–Guestrin 2014,
Eq. (13); Ma–Chen–Fox 2015, Eq. (9)). -/
theorem bind_heatKernelPi_compensated_eq_emKernelPi (h : ℝ≥0) {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : Measurable b) (c : ℝ) (t : ℝ≥0)
    (hcomp : NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t ≤ 2 * h) (x : Fin d → ℝ) :
    (heatKernelPi t x).bind
        (fun y : Fin d → ℝ => Measure.pi fun i =>
          gaussianReal ((x i + h * b x i) + (h * c) * (y i - x i))
            (2 * h - NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t)) =
      emKernelPi h b hb x ∧
    klDiv ((heatKernelPi t x).bind
        (fun y : Fin d → ℝ => Measure.pi fun i =>
          gaussianReal ((x i + h * b x i) + (h * c) * (y i - x i))
            (2 * h - NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t)))
        (emKernelPi h b hb x) = 0 ∧
    TotalVariation.tvSup ((heatKernelPi t x).bind
        (fun y : Fin d → ℝ => Measure.pi fun i =>
          gaussianReal ((x i + h * b x i) + (h * c) * (y i - x i))
            (2 * h - NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t)))
        (emKernelPi h b hb x) = 0 := by
  have heq : (heatKernelPi t x).bind
      (fun y : Fin d → ℝ => Measure.pi fun i =>
        gaussianReal ((x i + h * b x i) + (h * c) * (y i - x i))
          (2 * h - NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t)) =
      emKernelPi h b hb x := by
    rw [bind_heatKernelPi_affine_sub, tsub_add_cancel_of_le hcomp, emKernelPi_apply]
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, klDiv_self]
  · rw [heq, TotalVariation.tvSup_self]

/-- **Exact one-step marginal KL for an uncompensated Gaussian score oracle.** For `h ≠ 0`,
marginalising the draw `y ~ heatKernelPi t x` gives
`KL(randomEmKernel x ‖ emKernelPi x) = d (u - log (1 + u)) / 2` with `u = h c² t / 2`, which is at
most `d h² c⁴ t² / 8 = O(d h²)` per step. The GI-2 conditional-KL bound `klDiv_randomEmKernel_le`,
which treats the random drift as a mean shift before marginalising, gives `d h c² t / 4`. -/
theorem klDiv_randomEmKernel_heatKernelPi_eq_and_le {h : ℝ≥0} (hh : h ≠ 0)
    {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b) (c : ℝ) (t : ℝ≥0) (x : Fin d → ℝ) :
    klDiv (randomEmKernel h (heatKernelPi t)
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 + c • (p.2 - p.1))
        (measurable_singleDrawDrift hb c) x)
      (emKernelPi h b hb x) =
      ENNReal.ofReal (d * ((h * c ^ 2 * t / 2 - Real.log (1 + h * c ^ 2 * t / 2)) / 2)) ∧
    klDiv (randomEmKernel h (heatKernelPi t)
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 + c • (p.2 - p.1))
        (measurable_singleDrawDrift hb c) x)
      (emKernelPi h b hb x) ≤
      ENNReal.ofReal (d * (h : ℝ) ^ 2 * c ^ 4 * (t : ℝ) ^ 2 / 8) := by
  have hh' : (0 : ℝ) < h := by positivity
  have h2h : (2 * h : ℝ≥0) ≠ 0 := mul_ne_zero two_ne_zero hh
  have hv : (2 * h + NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t : ℝ≥0) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 h2h) le_self_add)
  have hratio : ((2 * h + NNReal.mk ((h * c) ^ 2) (sq_nonneg _) * t : ℝ≥0) : ℝ) / (2 * h : ℝ≥0) =
      1 + h * c ^ 2 * t / 2 := by
    push_cast
    change (2 * (h : ℝ) + ((h : ℝ) * c) ^ 2 * (t : ℝ)) / (2 * (h : ℝ)) = _
    field_simp
  have hnonneg : 0 ≤ (h : ℝ) * c ^ 2 * t / 2 := by positivity
  have hlog : 0 ≤ (h * c ^ 2 * t / 2 - Real.log (1 + h * c ^ 2 * t / 2)) / 2 := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (h : ℝ) * c ^ 2 * t / 2)
    linarith
  have heq : klDiv (randomEmKernel h (heatKernelPi t)
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 + c • (p.2 - p.1))
        (measurable_singleDrawDrift hb c) x)
      (emKernelPi h b hb x) =
      ENNReal.ofReal (d * ((h * c ^ 2 * t / 2 - Real.log (1 + h * c ^ 2 * t / 2)) / 2)) := by
    rw [randomEmKernel_heatKernelPi_apply h hb, emKernelPi_apply, klDiv_pi_pi]
    simp_rw [GaussianFlowVsOU.klDiv_gaussianReal_gaussianReal_of_ne_zero _ _ hv h2h,
      sub_self, zero_pow two_ne_zero, zero_div, add_zero, hratio]
    have h1 : (1 + (h : ℝ) * c ^ 2 * t / 2 - 1 - Real.log (1 + (h : ℝ) * c ^ 2 * t / 2)) / 2 =
        (h * c ^ 2 * t / 2 - Real.log (1 + h * c ^ 2 * t / 2)) / 2 := by ring
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  refine ⟨heq, heq.trans_le (ENNReal.ofReal_le_ofReal ?_)⟩
  set u := (h : ℝ) * c ^ 2 * t / 2
  have hu0 : 0 ≤ u := hnonneg
  have hu1 : 0 < 1 + u := by linarith
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.2 hu1)
  rw [Real.log_inv] at hinv
  have h2 : u / (1 + u) ≤ Real.log (1 + u) := by
    have e : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by field_simp; ring
    linarith
  have h3 : u - Real.log (1 + u) ≤ u ^ 2 := by
    have e : u - u / (1 + u) = u ^ 2 / (1 + u) := by field_simp; ring
    have h4 : u ^ 2 / (1 + u) ≤ u ^ 2 / 1 :=
      div_le_div_of_nonneg_left (sq_nonneg u) one_pos (by linarith)
    linarith [sq_nonneg u]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h5 : (d : ℝ) * ((u - Real.log (1 + u)) / 2) ≤ d * (u ^ 2 / 2) := by nlinarith
  refine h5.trans_eq ?_
  simp only [u]
  ring

/-- **Multi-step KL and TV bounds for the uncompensated single-draw Gaussian score oracle.** For
the exact-drift chain `μ (k+1) = emKernelPi (h k) (b k) ∘ₘ μ k` and the single-draw
Gaussian-oracle chain
`ν (k+1) = randomEmKernel (h k) (heatKernelPi (t k)) (b k + c k (y - x)) ∘ₘ ν k` with `h k ≠ 0`
and `KL(ν 0 ‖ μ 0) < ∞`, the `n`-step KL divergence is at most
`KL(ν 0 ‖ μ 0) + ∑_{k<n} d (h_k)² (c_k)⁴ (t_k)² / 8`, and
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} d (h_k)² (c_k)⁴ (t_k)² / 16)`. -/
theorem klDiv_and_tvSup_heatKernelPiSingleDrawChain_le {h : ℕ → ℝ≥0} (hh : ∀ k, h k ≠ 0)
    {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hb : ∀ k, Measurable (b k)) (c : ℕ → ℝ)
    (t : ℕ → ℝ≥0) {μ ν : ℕ → Measure (Fin d → ℝ)}
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (heatKernelPi (t k))
      (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b k p.1 + c k • (p.2 - p.1))
      (measurable_singleDrawDrift (hb k) (c k)) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ENNReal.ofReal (d * (h k : ℝ) ^ 2 * c k ^ 4 * (t k : ℝ) ^ 2 / 8) ∧
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, d * (h k : ℝ) ^ 2 * c k ^ 4 * (t k : ℝ) ^ 2 / 16) := by
  have hprobμ : ∀ k, IsProbabilityMeasure (μ k) :=
    ErrorPropagation.isProbabilityMeasure_of_comp_succ hμ
  have hprobν : ∀ k, IsProbabilityMeasure (ν k) :=
    ErrorPropagation.isProbabilityMeasure_of_comp_succ hν
  have : ∀ k, IsFiniteMeasure (μ k) := fun k =>
    have := hprobμ k; inferInstance
  have : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    have := hprobν k; inferInstance
  have hKL : klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ENNReal.ofReal (d * (h k : ℝ) ^ 2 * c k ^ 4 * (t k : ℝ) ^ 2 / 8) := by
    refine (KL.klDiv_chain_le_sum (fun k => emKernelPi (h k) (b k) (hb k))
      (fun k => randomEmKernel (h k) (heatKernelPi (t k))
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b k p.1 + c k • (p.2 - p.1))
        (measurable_singleDrawDrift (hb k) (c k))) μ ν hμ hν n).trans ?_
    gcongr with k _
    have := hprobν k
    refine (lintegral_mono fun x =>
      (klDiv_randomEmKernel_heatKernelPi_eq_and_le (hh k) (hb k) (c k) (t k) x).2).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  refine ⟨hKL, ?_⟩
  have := hprobμ n
  have := hprobν n
  refine (Pinsker.tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal hKL0
    (fun k => by positivity) hKL).trans_eq ?_
  congr 1
  rw [add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun k _ => by ring

end HeatPosterior

end FormalizeSampling.GaussianIncrement
