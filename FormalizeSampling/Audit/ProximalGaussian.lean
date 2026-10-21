module

public import FormalizeSampling.Samplers.ProximalGaussianUnconditional
public import FormalizeSampling.Samplers.ProximalPerturbedGaussian

/-!
# Audit (PX-1, PX-3, PX-4): non-vacuity witnesses for the proximal-sampler statements

This file applies the headline theorems of registry rows PX-1, PX-3 and PX-4 to concrete,
non-degenerate instances, discharging every hypothesis, and shows that the resulting bounds are
not trivially true (the initial KL is finite **and strictly positive**).

Instances.
* **Conditioned laws.** For a probability law `μ` and a measurable `s` with `μ s ≠ 0` and
  `μ sᶜ ≠ 0`, the conditional law `μ[|s]` is a probability law, `μ[|s] ≤ (μ s)⁻¹ • μ` (warm),
  and `0 < KL(μ[|s]‖μ) = -log μ(s) < ∞` (`cond_witness`).
* **Non-log-concave perturbation.** `W₁ = 1_{[0,∞)}` on `ℝ` and `W_d(x) = 1_{x₀ ≥ 0}` on
  `Fin d → ℝ` (`d ≥ 1`): measurable, `0 ≤ W ≤ 1`, and `α|x|²/2 + W` is not convex.
* **Gaussian start.** `ρ₀ = N(m, 1/α)` with `m ≠ 0` against `π = N(0, 1/α)`, for which the
  sharp PX-3 bound is attained with equality at every iterate (`px3_iterate_attained`).

## Main results

* `px1_reverseKernel_perturbed`, `px1_pi_perturbed`: PX-1 for a non-Gaussian target.
* `px3_iterate_attained`, `px3_tv_gaussian`, `px3_pi_cond`: PX-3, 1D (bound attained) and
  `Fin d → ℝ` (`d ≥ 1`, initial KL in `(0, ∞)`).
* `px4_oneD_cold`, `px4_pi_cold`: PX-4 (iterate and TV forms of the squared-exponent rate) for
  `W₁`, `W_d`.

## Not proved here

* No witness that the PX-4 rate `(1 + α e^{-(b-a)} η)⁻²` is attained (only that the
  hypotheses hold with `0 < KL(ρ₀‖π) < ∞`); for `W` constant the PX-3 witness shows it.
* No Lean statement that `α|x|²/2 + W₁` is non-convex (it is clear: `W₁` jumps up at `0`).
* No new mathematics: every witness is an application of existing repository theorems.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.Audit.ProximalGaussian

/-! ### Generic witnesses -/

/-- **Conditioned laws are warm with finite, positive KL.** For a probability law `μ` and a
measurable `s` with `μ s ≠ 0`, `μ sᶜ ≠ 0`: `μ[|s]` is a probability law,
`μ[|s] ≤ ofReal (μ.real s)⁻¹ • μ`, `KL(μ[|s]‖μ) ≠ ⊤` and `0 < KL(μ[|s]‖μ).toReal`. -/
theorem cond_witness {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) (h0 : μ s ≠ 0) (h1 : μ sᶜ ≠ 0) :
    IsProbabilityMeasure μ[|s] ∧ μ[|s] ≤ ENNReal.ofReal (μ.real s)⁻¹ • μ ∧
      klDiv μ[|s] μ ≠ ⊤ ∧ 0 < (klDiv μ[|s] μ).toReal := by
  have hp := cond_isProbabilityMeasure (μ := μ) h0
  have hint : Integrable (llr μ μ) μ := (integrable_zero _ _ μ).congr (llr_self μ).symm
  obtain ⟨hne, heq⟩ := KLWarmApprox.mul_toReal_klDiv_cond (ρ := μ) (π := μ)
    Measure.AbsolutelyContinuous.rfl hint hs h0
  have hI : ∫ x in s, llr μ μ x ∂μ = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae (llr_self μ))]; simp
  have hpos : 0 < μ.real s := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  have hlt : μ.real s < 1 := by
    have e := probReal_compl_eq_one_sub (μ := μ) hs
    have : 0 < μ.real sᶜ := ENNReal.toReal_pos h1 (measure_ne_top _ _)
    linarith
  have hlog : Real.log (μ.real s) < 0 := Real.log_neg hpos hlt
  refine ⟨hp, ?_, hne, ?_⟩
  · have hc : ENNReal.ofReal (μ.real s)⁻¹ = (μ s)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hc]
    refine Measure.le_intro fun t ht _ => ?_
    rw [ProbabilityTheory.cond, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul]
    gcongr
    exact Measure.le_iff'.2 fun t => Measure.restrict_le_self t
  · rw [hI] at heq
    by_contra hK
    push Not at hK
    nlinarith [mul_le_mul_of_nonneg_left hK hpos.le]

open FormalizeSampling.Proximal in
/-- A target `π ∝ e^{-f}` on `ℝ` (measurable `f`, integrable `e^{-f}`) charges every set that
contains a nonempty open set. -/
theorem target_ne_zero {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {U s : Set ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) (hUs : U ⊆ s) : target f s ≠ 0 := by
  have hac : (volume : Measure ℝ) ≪ target f :=
    withDensity_absolutelyContinuous' (measurable_targetDensity hf).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2
        (div_pos (Real.exp_pos _) (targetNormalizer_pos hint))).ne')
  intro h
  exact (hU.measure_pos volume hne).ne' (hac (measure_mono_null hUs h))

open FormalizeSampling.ProximalPi in
/-- A target `π ∝ e^{-f}` on `Fin d → ℝ` (measurable `f`, integrable `e^{-f}`) charges every
set that contains a nonempty open set. -/
theorem targetPi_ne_zero {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {U s : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) (hUs : U ⊆ s) : targetPi f s ≠ 0 := by
  have hac : (volume : Measure (Fin d → ℝ)) ≪ targetPi f :=
    withDensity_absolutelyContinuous'
      (measurable_targetDensityPi hf).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2
        (div_pos (Real.exp_pos _) (targetNormalizerPi_pos hint))).ne')
  intro h
  exact (hU.measure_pos volume hne).ne' (hac (measure_mono_null hUs h))

/-! ### The perturbations -/

/-- The one-dimensional perturbation `W₁ = 1_{[0, ∞)}` (bounded, discontinuous). -/
noncomputable def W1 : ℝ → ℝ := (Ici (0 : ℝ)).indicator fun _ => 1

/-- `W₁` is measurable. -/
theorem measurable_W1 : Measurable W1 := measurable_const.indicator measurableSet_Ici

/-- `0 ≤ W₁`. -/
theorem W1_nonneg (x : ℝ) : 0 ≤ W1 x := by
  unfold W1; by_cases h : x ∈ Ici (0 : ℝ) <;> simp [h]

/-- `W₁ ≤ 1`. -/
theorem W1_le_one (x : ℝ) : W1 x ≤ 1 := by
  unfold W1; by_cases h : x ∈ Ici (0 : ℝ) <;> simp [h]

/-- The half-space `{x | 0 ≤ x₀}` in `Fin d → ℝ`, `d ≥ 1`. -/
def halfSpace (d : ℕ) [NeZero d] : Set (Fin d → ℝ) := {x | 0 ≤ x 0}

/-- The half-space is measurable. -/
theorem measurableSet_halfSpace (d : ℕ) [NeZero d] : MeasurableSet (halfSpace d) :=
  measurableSet_le measurable_const (measurable_pi_apply 0)

/-- The `d`-dimensional perturbation `W_d = 1_{x₀ ≥ 0}`. -/
noncomputable def Wd (d : ℕ) [NeZero d] : (Fin d → ℝ) → ℝ := (halfSpace d).indicator fun _ => 1

/-- `W_d` is measurable. -/
theorem measurable_Wd (d : ℕ) [NeZero d] : Measurable (Wd d) :=
  measurable_const.indicator (measurableSet_halfSpace d)

/-- `0 ≤ W_d`. -/
theorem Wd_nonneg (d : ℕ) [NeZero d] (x : Fin d → ℝ) : 0 ≤ Wd d x := by
  unfold Wd; by_cases h : x ∈ halfSpace d <;> simp [h]

/-- `W_d ≤ 1`. -/
theorem Wd_le_one (d : ℕ) [NeZero d] (x : Fin d → ℝ) : Wd d x ≤ 1 := by
  unfold Wd; by_cases h : x ∈ halfSpace d <;> simp [h]

/-! ### PX-1 -/

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp in
/-- **PX-1 witness (1D, non-Gaussian target).** For `α, η > 0` and `f = α x²/2 + 1_{x ≥ 0}`, the
RGO is the Bayes reverse kernel of the forward step and `π ∝ e^{-f}` is invariant. -/
theorem px1_reverseKernel_perturbed {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ReverseKernel.IsReverseKernel (forwardKernel η) (target (gaussPotential α + W1))
        (rgoKernel (gaussPotential α + W1) η) ∧
      proxKernel (gaussPotential α + W1) η ∘ₘ target (gaussPotential α + W1)
        = target (gaussPotential α + W1) := by
  have hf := (measurable_gaussPotential α).add measurable_W1
  have hint := HeatFlowRegularityPerturbed.integrable_exp_neg_gaussPotential_add hα
    measurable_W1 W1_nonneg
  exact ⟨isReverseKernel_rgoKernel hf hint hη, proxKernel_comp_target hf hint hη⟩

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi in
/-- **PX-1 witness (`Fin d → ℝ`, `d ≥ 1`, non-Gaussian target).** For `α, η > 0` and
`f = α|x|²/2 + W_d`: Bayes reverse kernel, invariance, and the backward data-processing bound
applied to a law with `0 < KL(ρ‖π) < ∞`. -/
theorem px1_pi_perturbed {d : ℕ} [NeZero d] {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    let f := fun x : Fin d → ℝ => gaussPotentialPi α x + Wd d x
    let ρ := (targetPi f)[|halfSpace d]
    ReverseKernel.IsReverseKernel (forwardKernelPi η) (targetPi f) (rgoKernelPi f η) ∧
      proxKernelPi f η ∘ₘ targetPi f = targetPi f ∧
      klDiv ρ (targetPi f) ≠ ⊤ ∧ 0 < (klDiv ρ (targetPi f)).toReal ∧
      klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)
        ≤ klDiv (forwardKernelPi η ∘ₘ ρ) (forwardKernelPi η ∘ₘ targetPi f) := by
  intro f ρ
  have hf : Measurable f := (measurable_gaussPotentialPi α).add (measurable_Wd d)
  have hint := HeatFlowRegularityPerturbedPi.integrable_exp_neg_gaussPotentialPi_add hα
    (measurable_Wd d) (Wd_nonneg d)
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hp, -, hne, hpos⟩ := cond_witness (targetPi f) (measurableSet_halfSpace d)
    (targetPi_ne_zero hf hint (U := {x | 0 < x 0})
      (isOpen_lt continuous_const (continuous_apply 0)) ⟨fun _ => 1, by simp⟩
      fun x (hx : 0 < x 0) => show 0 ≤ x 0 from hx.le)
    (targetPi_ne_zero hf hint (U := {x | x 0 < 0})
      (isOpen_lt (continuous_apply 0) continuous_const) ⟨fun _ => -1, by simp⟩
      fun x hx => by simp [halfSpace]; exact hx)
  exact ⟨isReverseKernel_rgoKernelPi hf hint hη, proxKernelPi_comp_targetPi hf hint hη,
    hne, hpos, klDiv_proxKernelPi_comp_le_forward hf hint hη ρ⟩

/-! ### PX-3 -/

section PX3

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
  FormalizeSampling.ProximalGaussianUnconditional

/-- The proximal chain for the Gaussian target from `N(m, 1/α)`. -/
noncomputable def gaussChain (α η m : ℝ) (k : ℕ) : Measure ℝ :=
  (fun μ => proxKernel (gaussPotential α) η ∘ₘ μ)^[k] (gaussianReal m (α⁻¹).toNNReal)

/-- The Gaussian chain satisfies the recursion `ρ (k+1) = P ∘ₘ ρ k`. -/
theorem gaussChain_succ (α η m : ℝ) (k : ℕ) :
    gaussChain α η m (k + 1) = proxKernel (gaussPotential α) η ∘ₘ gaussChain α η m k :=
  Function.iterate_succ_apply' _ _ _

/-- The Gaussian chain starts at `N(m, 1/α)`. -/
instance (α η m : ℝ) : IsProbabilityMeasure (gaussChain α η m 0) := by
  unfold gaussChain; simp only [Function.iterate_zero, id]; infer_instance

/-- **PX-3 hypotheses are satisfiable non-trivially (1D).** For `α > 0` and `m ≠ 0`,
`ρ₀ = N(m, 1/α)` has `KL(ρ₀‖π) = α m²/2 ∈ (0, ∞)`. -/
theorem px3_hyps {α : ℝ} (hα : 0 < α) {m : ℝ} (hm : m ≠ 0) :
    klDiv (gaussianReal m (α⁻¹).toNNReal) (target (gaussPotential α)) ≠ ⊤ ∧
      0 < (klDiv (gaussianReal m (α⁻¹).toNNReal) (target (gaussPotential α))).toReal := by
  rw [klDiv_gaussianReal_gaussTarget hα]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal (by positivity)]; positivity

/-- **PX-3 witness, iterates, bound attained (1D).** For `α, η > 0`, `m ≠ 0` and the chain from
`N(m, 1/α)`: `toReal_klDiv_iterate_le_sq_of_ne_top` applies, its right-hand side is positive,
and it holds with **equality** for every `k` (via EX-3), so it is neither vacuous nor slack. -/
theorem px3_iterate_attained {α η : ℝ} (hα : 0 < α) (hη : 0 < η) {m : ℝ} (hm : m ≠ 0)
    (k : ℕ) :
    klDiv (gaussChain α η m k) (target (gaussPotential α)) ≠ ⊤ ∧
      (klDiv (gaussChain α η m k) (target (gaussPotential α))).toReal
        ≤ (klDiv (gaussChain α η m 0) (target (gaussPotential α))).toReal
          / (1 + α * η) ^ (2 * k) ∧
      (klDiv (gaussChain α η m k) (target (gaussPotential α))).toReal
        = (klDiv (gaussChain α η m 0) (target (gaussPotential α))).toReal
          / (1 + α * η) ^ (2 * k) ∧
      0 < (klDiv (gaussChain α η m 0) (target (gaussPotential α))).toReal := by
  have h0 : gaussChain α η m 0 = gaussianReal m (α⁻¹).toNNReal := rfl
  obtain ⟨hKL, hpos⟩ := px3_hyps hα hm
  rw [← h0] at hKL hpos
  obtain ⟨h1, h2⟩ := toReal_klDiv_iterate_le_sq_of_ne_top hα hη (gaussChain α η m)
    (gaussChain_succ α η m) hKL k
  exact ⟨h1, h2, (klDiv_iterate_gaussTarget hα hη m _ h0 (gaussChain_succ α η m) k).2, hpos⟩

/-- **PX-3 witness, TV form (1D).** The TV bound of the PX-6 theorem
`ProximalStronglyLogConcave.tvSup_iterate_le_sq_of_stronglyLogConcave` with `f = α x²/2`
applies to the Gaussian chain from `N(m, 1/α)`. -/
theorem px3_tv_gaussian {α η : ℝ} (hα : 0 < α) (hη : 0 < η) {m : ℝ} (hm : m ≠ 0) (k : ℕ) :
    TotalVariation.tvSup (gaussChain α η m k) (target (gaussPotential α))
      ≤ √((klDiv (gaussChain α η m 0) (target (gaussPotential α))).toReal
          / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨hKL, -⟩ := px3_hyps hα hm
  exact ProximalStronglyLogConcave.tvSup_iterate_le_sq_of_stronglyLogConcave hα hη
    (by simpa using convexOn_const (0 : ℝ) convex_univ) (gaussChain α η m)
    (gaussChain_succ α η m) hKL k

end PX3

section PX3Pi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
  FormalizeSampling.ProximalGaussianUnconditional

variable {d : ℕ} [NeZero d]

/-- **PX-3 hypotheses on `Fin d → ℝ` (`d ≥ 1`).** For `α > 0`, `ρ₀ = π[|{x₀ ≥ 0}]` with
`π = N(0, I/α)` is a probability law with `0 < KL(ρ₀‖π) < ∞`. -/
theorem px3_pi_hyps {α : ℝ} (hα : 0 < α) :
    let π := targetPi (gaussPotentialPi (d := d) α)
    IsProbabilityMeasure π[|halfSpace d] ∧ klDiv π[|halfSpace d] π ≠ ⊤ ∧
      0 < (klDiv π[|halfSpace d] π).toReal := by
  intro π
  have hf := measurable_gaussPotentialPi (d := d) α
  have hint := integrable_exp_neg_gaussPotentialPi (d := d) hα
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hp, -, hne, hpos⟩ := cond_witness π (measurableSet_halfSpace d)
    (targetPi_ne_zero hf hint (U := {x | 0 < x 0})
      (isOpen_lt continuous_const (continuous_apply 0)) ⟨fun _ => 1, by simp⟩
      fun x (hx : 0 < x 0) => show 0 ≤ x 0 from hx.le)
    (targetPi_ne_zero hf hint (U := {x | x 0 < 0})
      (isOpen_lt (continuous_apply 0) continuous_const) ⟨fun _ => -1, by simp⟩
      fun x hx => by simp [halfSpace]; exact hx)
  exact ⟨hp, hne, hpos⟩

/-- The proximal chain for the isotropic Gaussian target from `π[|{x₀ ≥ 0}]`. -/
noncomputable def gaussChainPi (α η : ℝ) (k : ℕ) : Measure (Fin d → ℝ) :=
  (fun μ => proxKernelPi (gaussPotentialPi α) η ∘ₘ μ)^[k]
    ((targetPi (gaussPotentialPi (d := d) α))[|halfSpace d])

/-- The chain satisfies the recursion `ρ (k+1) = P ∘ₘ ρ k`. -/
theorem gaussChainPi_succ (α η : ℝ) (k : ℕ) :
    gaussChainPi (d := d) α η (k + 1)
      = proxKernelPi (gaussPotentialPi α) η ∘ₘ gaussChainPi α η k :=
  Function.iterate_succ_apply' _ _ _

/-- **PX-3 witness on `Fin d → ℝ` (`d ≥ 1`).** For `α, η > 0` the one-step and TV forms (PX-6
with `f = α ‖x‖²/2`) and the iterate form `toReal_klDiv_iteratePi_le_sq_of_ne_top` apply to the
chain from `π[|{x₀ ≥ 0}]`, whose initial KL is finite and positive. -/
theorem px3_pi_cond {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (k : ℕ) :
    let π := targetPi (gaussPotentialPi (d := d) α)
    0 < (klDiv (gaussChainPi (d := d) α η 0) π).toReal ∧
      (klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ gaussChainPi α η 0) π).toReal
        ≤ (klDiv (gaussChainPi α η 0) π).toReal / (1 + α * η) ^ 2 ∧
      klDiv (gaussChainPi α η k) π ≠ ⊤ ∧
      (klDiv (gaussChainPi α η k) π).toReal
        ≤ (klDiv (gaussChainPi α η 0) π).toReal / (1 + α * η) ^ (2 * k) ∧
      TotalVariation.tvSup (gaussChainPi α η k) π
        ≤ √((klDiv (gaussChainPi α η 0) π).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  intro π
  obtain ⟨hp, hne, hpos⟩ := px3_pi_hyps (d := d) hα
  have : IsProbabilityMeasure (gaussChainPi (d := d) α η 0) := hp
  have hconv : ConvexOn ℝ univ fun x : Fin d → ℝ => gaussPotentialPi α x - gaussPotentialPi α x :=
    by simpa using convexOn_const (0 : ℝ) convex_univ
  obtain ⟨i1, i2⟩ := toReal_klDiv_iteratePi_le_sq_of_ne_top hα hη (gaussChainPi α η)
    (gaussChainPi_succ α η) hne k
  open ProximalStronglyLogConcaveGeneralPi in
  exact ⟨hpos, (toReal_klDiv_proxKernelPi_comp_le_sq_of_stronglyLogConcave hα hη hconv _ hne).2,
    i1, i2, tvSupPi_iterate_le_sq_of_stronglyLogConcave hα hη hconv (gaussChainPi α η)
      (gaussChainPi_succ α η) hne k⟩

end PX3Pi

/-! ### PX-4, dimension one -/

section PX4

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp

/-- The perturbed target `π_W ∝ exp(-α x²/2 - 1_{x ≥ 0})`. -/
noncomputable abbrev piW (α : ℝ) : Measure ℝ := target (gaussPotential α + W1)

/-- **PX-4 hypotheses (1D).** For `α > 0`, `ρ₀ = π_W[|[0,∞)]` is a probability law with
`0 < KL(ρ₀‖π_W) < ∞`. -/
theorem px4_hyps {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (piW α)[|Ici 0] ∧
      klDiv (piW α)[|Ici 0] (piW α) ≠ ⊤ ∧ 0 < (klDiv (piW α)[|Ici 0] (piW α)).toReal := by
  have hf := (measurable_gaussPotential α).add measurable_W1
  have hint := HeatFlowRegularityPerturbed.integrable_exp_neg_gaussPotential_add hα
    measurable_W1 W1_nonneg
  have := isProbabilityMeasure_target hint
  obtain ⟨hp, -, hne, hpos⟩ := cond_witness (piW α) measurableSet_Ici
    (target_ne_zero hf hint isOpen_Ioi ⟨1, show (0 : ℝ) < 1 by norm_num⟩ Ioi_subset_Ici_self)
    (target_ne_zero hf hint isOpen_Iio ⟨-1, show (-1 : ℝ) < 0 by norm_num⟩ fun x hx => by
      simp only [mem_compl_iff, mem_Ici, not_le]; exact hx)
  exact ⟨hp, hne, hpos⟩

/-- **PX-4 witness (1D).** The iterate and TV bounds of `ProximalSharpPerturbedCold`
(rate `(1 + α e^{-1} η)^{-2k}`, `a = 0`, `b = 1`) apply to the chain from
`ρ₀ = π_W[|[0,∞)]`. -/
theorem px4_oneD_cold {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (ρ : ℕ → Measure ℝ)
    (h0 : ρ 0 = (piW α)[|Ici 0])
    (hstep : ∀ k, ρ (k + 1) = proxKernel (gaussPotential α + W1) η ∘ₘ ρ k) (k : ℕ) :
    0 < (klDiv (ρ 0) (piW α)).toReal ∧
      (klDiv (ρ k) (piW α)).toReal
        ≤ (klDiv (ρ 0) (piW α)).toReal / (1 + α * Real.exp (-(1 - 0)) * η) ^ (2 * k) ∧
      TotalVariation.tvSup (ρ k) (piW α)
        ≤ √((klDiv (ρ 0) (piW α)).toReal / (2 * (1 + α * Real.exp (-(1 - 0)) * η) ^ (2 * k))) := by
  obtain ⟨hp, hne, hpos⟩ := px4_hyps hα
  rw [← h0] at hne hpos
  have : IsProbabilityMeasure (ρ 0) := h0 ▸ hp
  have hW := measurable_W1
  exact ⟨hpos,
    (ProximalSharpPerturbedCold.toReal_klDiv_iterate_le_sq_perturbed_of_ne_top hα hη hW
      W1_nonneg W1_le_one ρ hstep hne k).2.2,
    ProximalSharpPerturbedCold.tvSup_iterate_le_sq_perturbed_of_ne_top hα hη hW W1_nonneg
      W1_le_one ρ hstep hne k⟩

end PX4

/-! ### PX-4 on `Fin d → ℝ` -/

section PX4Pi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi

variable {d : ℕ} [NeZero d]

/-- The perturbed target `π_W ∝ exp(-α|x|²/2 - 1_{x₀ ≥ 0})` on `Fin d → ℝ`. -/
noncomputable abbrev piWd (d : ℕ) [NeZero d] (α : ℝ) : Measure (Fin d → ℝ) :=
  targetPi fun x => gaussPotentialPi α x + Wd d x

/-- **PX-4 hypotheses on `Fin d → ℝ` (`d ≥ 1`).** For `α > 0`, `ρ₀ = π_W[|{x₀ ≥ 0}]` is a
probability law with `0 < KL(ρ₀‖π_W) < ∞`. -/
theorem px4_pi_hyps {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (piWd d α)[|halfSpace d] ∧
      klDiv (piWd d α)[|halfSpace d] (piWd d α) ≠ ⊤ ∧
      0 < (klDiv (piWd d α)[|halfSpace d] (piWd d α)).toReal := by
  have hf : Measurable fun x : Fin d → ℝ => gaussPotentialPi α x + Wd d x :=
    (measurable_gaussPotentialPi α).add (measurable_Wd d)
  have hint := HeatFlowRegularityPerturbedPi.integrable_exp_neg_gaussPotentialPi_add hα
    (measurable_Wd d) (Wd_nonneg d)
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hp, -, hne, hpos⟩ := cond_witness (piWd d α) (measurableSet_halfSpace d)
    (targetPi_ne_zero hf hint (U := {x | 0 < x 0})
      (isOpen_lt continuous_const (continuous_apply 0)) ⟨fun _ => 1, by simp⟩
      fun x (hx : 0 < x 0) => show 0 ≤ x 0 from hx.le)
    (targetPi_ne_zero hf hint (U := {x | x 0 < 0})
      (isOpen_lt (continuous_apply 0) continuous_const) ⟨fun _ => -1, by simp⟩
      fun x hx => by simp [halfSpace]; exact hx)
  exact ⟨hp, hne, hpos⟩

/-- **PX-4 witness on `Fin d → ℝ`.** The iterate and TV bounds of
`ProximalSharpPerturbedPi` apply to the chain from `ρ₀ = π_W[|{x₀ ≥ 0}]`. -/
theorem px4_pi_cold {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (ρ : ℕ → Measure (Fin d → ℝ))
    (h0 : ρ 0 = (piWd d α)[|halfSpace d])
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (fun x => gaussPotentialPi α x + Wd d x) η ∘ₘ ρ k)
    (k : ℕ) :
    0 < (klDiv (ρ 0) (piWd d α)).toReal ∧
      (klDiv (ρ k) (piWd d α)).toReal
        ≤ (klDiv (ρ 0) (piWd d α)).toReal / (1 + α * Real.exp (-(1 - 0)) * η) ^ (2 * k) ∧
      TotalVariation.tvSup (ρ k) (piWd d α)
        ≤ √((klDiv (ρ 0) (piWd d α)).toReal
            / (2 * (1 + α * Real.exp (-(1 - 0)) * η) ^ (2 * k))) := by
  obtain ⟨hp, hne, hpos⟩ := px4_pi_hyps (d := d) hα
  rw [← h0] at hne hpos
  have : IsProbabilityMeasure (ρ 0) := h0 ▸ hp
  have hW := measurable_Wd d
  exact ⟨hpos,
    (ProximalSharpPerturbedPi.toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top hα hη hW
      (Wd_nonneg d) (Wd_le_one d) ρ hstep hne k).2.2,
    ProximalSharpPerturbedPi.tvSupPi_iterate_le_sq_perturbed_of_ne_top hα hη hW (Wd_nonneg d)
      (Wd_le_one d) ρ hstep hne k⟩

end PX4Pi

end FormalizeSampling.Audit.ProximalGaussian
