module

public import FormalizeSampling.Samplers.ProximalGeneralLSI
public import FormalizeSampling.Samplers.ProximalSharpLSI
public import FormalizeSampling.Foundations.GaussianLSI
public import FormalizeSampling.Foundations.KLWarmApprox
public import FormalizeSampling.Foundations.HolleyStroock
public import FormalizeSampling.Foundations.BakryEmery
public import FormalizeSampling.Samplers.BackwardHeatFlowRegularityWarm
public import FormalizeSampling.Samplers.HeatFlowRegularityWarm
public import FormalizeSampling.Samplers.ProximalStronglyLogConcave
public import FormalizeSampling.Foundations.LogSobolevExtension
public import FormalizeSampling.Samplers.ProximalGeneralLSIPi
public import FormalizeSampling.Samplers.ProximalStronglyLogConcaveGeneralPi
public import FormalizeSampling.Samplers.ProximalPerturbedGeneralPi
public import FormalizeSampling.Samplers.ProximalLSIPi
public import FormalizeSampling.Foundations.GaussianFunctionalLSIPi
public import FormalizeSampling.Samplers.ProximalRegularization
public import FormalizeSampling.Samplers.ProximalLogConcaveRate
public import FormalizeSampling.Samplers.RGOCouplingRotationPi
public import FormalizeSampling.Samplers.ProximalHeatFlow
public import FormalizeSampling.Samplers.EuclideanTransfer

/-!
# Statement audit: proximal sampler under an LSI, for log-concave and strongly log-concave targets

Rows: PX-2, PX-5, PX-6.

This file applies the theorems of these rows to concrete instances, discharging every hypothesis, to
check that the hypotheses are jointly satisfiable in non-degenerate situations (`η > 0`, `d ≥ 1`,
`0 < KL(ρ₀‖π) < ∞`). It proves nothing new about the sampler.

Instances used:
* Gaussian pair `ρ = N(m, 1)`, `π = target (gaussPotential 1) = N(0, 1)` (non-warm start);
* non-log-concave target `fStep(x) = x²/2 + 1_{x ≥ 0}` (and `fStepPi` on `Fin d → ℝ`), LSI by
  Holley–Stroock, Gaussian envelope from the quadratic lower bound;
* strongly convex non-Gaussian targets `fAbs(x) = x²/2 + |x|` and the non-separable
  `fNormPi(x) = |x|²/2 + ‖x‖_∞`;
* the bounded non-convex perturbation `fNormCosPi(x) = fNormPi(x) + cos(∑ᵢ xᵢ)` of `fNormPi`
  (not log-concave for `d ≥ 2`);
* warm starts `ρ₀ = π[|half-space]`, with `KL(ρ₀‖π) = -log π(half-space) ∈ (0, ∞)`;
* shift couplings `(X + c, X)` for the coupling / `1/k` forms;
* on `EuclideanSpace ℝ (Fin d)`: `g(x) = ‖x‖²/2` with Mathlib's Gaussian start
  `multivariateGaussian m 1`.

Main witnesses: `proximalContraction_gauss`, `proximalSharp_gauss`,
`proximalSharp_tv_iterate_gauss` (the conditional forms, with the *true* Fisher information),
`not_heatFlowLSI_heatFisher_gauss` (the `I = heatFisher` instance of `HeatFlowLSI` is false),
`general_iterate_step`, `sharpLSI_step`, `slc_iterate`, `generalPi_iterate`, `sharpLSIPi_step`,
`slcPi`, `slcCosPi_iterate`, `regularization_step`, `logConcave_iterate`, `logConcavePi`,
`slcEuclid` (the `EuclideanSpace` form of PX-6, from a Gaussian start with `0 < KL < ∞`).

## Not proved here

* Instances of `HasLipRep` beyond separable potentials, and of the rotation / quadratic
  reductions with `U ≠ 1`, `B ≠ 0`.
* Any statement about the tightness of the rates (that is EX-3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.Audit.ProximalGeneral

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
  FormalizeSampling.ProximalContraction

/-- `π = target (gaussPotential 1) = N(0, 1)`. -/
theorem target_one : target (gaussPotential 1) = gaussianReal 0 1 := by
  rw [target_gaussPotential one_pos]; simp

/-- Heat-flow KL of two unit Gaussians: `KL(N(m, 1+t)‖N(0, 1+t)) = m²/(2(1+t))`, `t ≥ 0`. -/
theorem heatKL_gauss (m : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    heatKL (gaussianReal m 1) (gaussianReal 0 1) t = m ^ 2 / 2 * (1 + t)⁻¹ := by
  have hc : ∀ x : ℝ, FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ gaussianReal x 1
      = gaussianReal x (1 + t.toNNReal) := fun x => by
    rw [← FormalizeSampling.OU.bind_heat]; rfl
  rw [heatKL, hc, hc, GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ (by positivity)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  push_cast
  rw [Real.coe_toNNReal _ ht]
  field_simp
  ring

/-- Closed form `g(t) = m²/2 · (1+t)⁻¹` has derivative `-m²/2 · (1+t)⁻²` for `t > -1`. -/
theorem hasDerivAt_gaussKL (m : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => m ^ 2 / 2 * (1 + s)⁻¹) (-(1 / 2) * (m ^ 2 / (1 + t) ^ 2)) t := by
  have h1 : (1 + t) ≠ 0 := by positivity
  have := (((hasDerivAt_id t).const_add 1).inv h1).const_mul (m ^ 2 / 2)
  refine this.congr_deriv ?_
  simp only [id]
  field_simp

/-- **Non-vacuity of `HeatFlowDissipation` (1D, Gaussian).** With `ρ = N(m,1)`, `π = N(0,1)` and
`I t = m²/(1+t)²` (the true relative Fisher information `I(ρ_t‖π_t)`), de Bruijn holds with
equality on `[0, η]`. -/
theorem heatFlowDissipation_gauss (m η : ℝ) :
    HeatFlowDissipation (gaussianReal m 1) (target (gaussPotential 1)) η
      (fun t => m ^ 2 / (1 + t) ^ 2) := by
  rw [target_one]
  refine ⟨?_, fun t ht => ⟨_, ?_, le_rfl⟩⟩
  · refine ContinuousOn.congr (f := fun s : ℝ => m ^ 2 / 2 * (1 + s)⁻¹) ?_
      fun s hs => heatKL_gauss m hs.1
    exact fun s hs => (hasDerivAt_gaussKL m hs.1).continuousAt.continuousWithinAt
  · exact (hasDerivAt_gaussKL m ht.1).hasDerivWithinAt.congr_of_mem
      (fun s hs => heatKL_gauss m (le_trans ht.1 hs)) (Set.mem_Ici.2 le_rfl)

/-- **Non-vacuity of `HeatFlowLSI` (1D, Gaussian), with the true Fisher information.** With
`ρ = N(m,1)`, `π = N(0,1)` (`α = 1`) and `I t = m²/(1+t)²`, the LSI along the flow holds with
equality, including `t = 0`. -/
theorem heatFlowLSI_gauss (m η : ℝ) :
    HeatFlowLSI (gaussianReal m 1) (target (gaussPotential 1)) 1 η
      (fun t => m ^ 2 / (1 + t) ^ 2) := by
  intro t ht
  rw [target_one, heatKL_gauss m ht.1]
  have : (1 + t) ≠ 0 := by linarith [ht.1]
  apply le_of_eq
  field_simp

/-- **The repo's `heatFisher` cannot be used in `HeatFlowLSI`.** For the same Gaussian pair with
`m ≠ 0`, `HeatFlowLSI ρ π 1 η (heatFisher ρ π)` is false for every `η > 0` (the `t = 0` slot
reads `2 KL(ρ‖π) ≤ heatFisher ρ π 0 = 0`, a junk value). -/
theorem not_heatFlowLSI_heatFisher_gauss {m η : ℝ} (hm : m ≠ 0) (hη : 0 < η) :
    ¬ HeatFlowLSI (gaussianReal m 1) (target (gaussPotential 1)) 1 η
      (HeatFlowDeBruijn.heatFisher (gaussianReal m 1) (target (gaussPotential 1))) := by
  intro h
  have h1 := GaussianLSI.toReal_klDiv_nonpos_of_heatFlowLSI one_pos hη h
  have h2 := heatKL_gauss m (le_refl 0)
  rw [heatKL_zero, ← target_one] at h2
  rw [h2] at h1
  have : 0 < m ^ 2 := by positivity
  norm_num at h1
  linarith

/-- `N(m, 1)` written with the variance `(1⁻¹).toNNReal` used by `ProximalSharp`. -/
theorem gauss_one (m : ℝ) : gaussianReal m 1 = gaussianReal m ((1 : ℝ)⁻¹).toNNReal := by simp

/-- `KL(N(m,1)‖N(0,1)) = m²/2` for the target `target (gaussPotential 1)`. -/
theorem klDiv_gauss (m : ℝ) :
    klDiv (gaussianReal m 1) (target (gaussPotential 1)) = ENNReal.ofReal (m ^ 2 / 2) := by
  rw [gauss_one, klDiv_gaussianReal_gaussTarget one_pos]; simp

/-- One exact proximal step on the Gaussian pair: KL becomes `m²/(2(1+η)²)` (real part). -/
theorem toReal_klDiv_prox_gauss (m : ℝ) {η : ℝ} (hη : 0 < η) :
    (klDiv (proxKernel (gaussPotential 1) η ∘ₘ gaussianReal m 1)
      (target (gaussPotential 1))).toReal = m ^ 2 / (2 * (1 + η) ^ 2) := by
  rw [gauss_one, (klDiv_proxKernel_comp_gaussTarget one_pos hη m).2.1,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **Non-vacuity of the backward named hypotheses (1D, Gaussian).** For `ρ = N(m,1)`,
`π = N(0,1)`, `η > 0` and `μ = forwardKernel η ∘ₘ ρ`, there are `Kb, Ib` with
`BackwardHeatFlowDissipation` and `BackwardHeatFlowLSI 1 η` (via the exact Gaussian RGO step
and `ProximalSharpLSI.exists_backwardHeatFlow_of_le`). -/
theorem exists_backward_gauss (m : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ Kb Ib : ℝ → ℝ, BackwardHeatFlowDissipation (gaussPotential 1) η
        (forwardKernel η ∘ₘ gaussianReal m 1) Kb Ib ∧ BackwardHeatFlowLSI 1 η Kb Ib := by
  refine ProximalSharpLSI.exists_backwardHeatFlow_of_le zero_le_one hη.le ?_
  rw [← proxKernel_comp_eq, toReal_klDiv_prox_gauss m hη, ← heatKL_eq_forwardKernel _ _ hη,
    target_one, heatKL_gauss m hη.le]
  have : (1 + η) ≠ 0 := by positivity
  apply le_of_eq
  field_simp

/-- **Old conditional forward form applied (1D, Gaussian, `m ≠ 0`).**
`ProximalContraction.toReal_klDiv_proxKernel_comp_le` applies to `ρ = N(m,1)`, `π = N(0,1)`,
`α = 1` with all named hypotheses discharged, and `KL(ρ‖π) = m²/2 > 0`. -/
theorem proximalContraction_gauss {m : ℝ} (hm : m ≠ 0) {η : ℝ} (hη : 0 < η) :
    0 < (klDiv (gaussianReal m 1) (target (gaussPotential 1))).toReal ∧
    klDiv (proxKernel (gaussPotential 1) η ∘ₘ gaussianReal m 1) (target (gaussPotential 1)) ≠ ∞ ∧
      (klDiv (proxKernel (gaussPotential 1) η ∘ₘ gaussianReal m 1)
        (target (gaussPotential 1))).toReal
        ≤ (klDiv (gaussianReal m 1) (target (gaussPotential 1))).toReal / (1 + 1 * η) := by
  refine ⟨?_, ProximalContraction.toReal_klDiv_proxKernel_comp_le (measurable_gaussPotential 1)
    (integrable_exp_neg_gaussPotential one_pos) hη zero_le_one _ (by simp [klDiv_gauss])
    (heatFlowDissipation_gauss m η) (heatFlowLSI_gauss m η)⟩
  rw [klDiv_gauss, ENNReal.toReal_ofReal (by positivity)]
  positivity

/-- **Old conditional sharp form applied (1D, Gaussian).** `ProximalSharp.toReal_klDiv_
proxKernel_comp_le_sq` applies to `ρ = N(m,1)`, `π = N(0,1)`, `α = 1`, all four named
hypotheses discharged (forward with the true Fisher information, backward via
`exists_backward_gauss`). -/
theorem proximalSharp_gauss (m : ℝ) {η : ℝ} (hη : 0 < η) :
    klDiv (proxKernel (gaussPotential 1) η ∘ₘ gaussianReal m 1) (target (gaussPotential 1)) ≠ ∞ ∧
      (klDiv (proxKernel (gaussPotential 1) η ∘ₘ gaussianReal m 1)
        (target (gaussPotential 1))).toReal
        ≤ (klDiv (gaussianReal m 1) (target (gaussPotential 1))).toReal / (1 + 1 * η) ^ 2 := by
  obtain ⟨Kb, Ib, hDb, hLb⟩ := exists_backward_gauss m hη
  exact ProximalSharp.toReal_klDiv_proxKernel_comp_le_sq (measurable_gaussPotential 1)
    (integrable_exp_neg_gaussPotential one_pos) hη zero_le_one _ (by simp [klDiv_gauss])
    (heatFlowDissipation_gauss m η) (heatFlowLSI_gauss m η) hDb hLb

/-- **Old conditional iterated sharp/TV forms applied (1D, Gaussian chain).** For the chain
`ρ k = N(m/(1+η)^k, 1)` (the exact proximal iterates from `N(m,1)`), all per-step named
hypotheses of `ProximalSharp.tvSup_iterate_le_sq` are discharged. -/
theorem proximalSharp_tv_iterate_gauss (m : ℝ) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    TotalVariation.tvSup (gaussianReal (m / (1 + 1 * η) ^ k) 1) (target (gaussPotential 1))
      ≤ √((klDiv (gaussianReal (m / (1 + 1 * η) ^ 0) 1) (target (gaussPotential 1))).toReal
        / (2 * (1 + 1 * η) ^ (2 * k))) := by
  have hstep : ∀ j, gaussianReal (m / (1 + 1 * η) ^ (j + 1)) 1
      = proxKernel (gaussPotential 1) η ∘ₘ gaussianReal (m / (1 + 1 * η) ^ j) 1 := fun j => by
    rw [gauss_one, gauss_one, (klDiv_proxKernel_comp_gaussTarget one_pos hη _).1, pow_succ,
      div_div]
  have hb := fun j => exists_backward_gauss (m / (1 + 1 * η) ^ j) hη
  choose Kb Ib hDb hLb using hb
  exact ProximalSharp.tvSup_iterate_le_sq (measurable_gaussPotential 1)
    (integrable_exp_neg_gaussPotential one_pos) hη zero_le_one
    (fun j => gaussianReal (m / (1 + 1 * η) ^ j) 1) hstep (by simp [klDiv_gauss])
    (fun j => heatFlowDissipation_gauss _ η) (fun j => heatFlowLSI_gauss _ η) hDb hLb k

/-! ### Conditioned laws: finite, nonzero KL without Gaussian algebra -/

/-- **KL of a conditioned law.** For a probability measure `π` and measurable `s` with
`0 < π s < 1`: `KL(π[|s]‖π) < ∞` and `KL(π[|s]‖π).toReal = -log π(s) > 0`. -/
theorem klDiv_cond_self {X : Type*} [MeasurableSpace X] (π : Measure X) [IsProbabilityMeasure π]
    {s : Set X} (hs : MeasurableSet s) (hs0 : π s ≠ 0) (hs1 : π s ≠ 1) :
    klDiv π[|s] π ≠ ⊤ ∧ 0 < (klDiv π[|s] π).toReal := by
  obtain ⟨hne, heq⟩ := KLWarmApprox.mul_toReal_klDiv_cond (ρ := π) (π := π)
    Measure.AbsolutelyContinuous.rfl (integrable_zero _ _ _ |>.congr (llr_self π).symm) hs hs0
  refine ⟨hne, ?_⟩
  have h0 : ∫ x in s, llr π π x ∂π = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae (llr_self π))]; simp
  have hp : 0 < π.real s := ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  have hp1 : π.real s < 1 := by
    have : π s < 1 := lt_of_le_of_ne prob_le_one hs1
    rw [measureReal_def]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 this |>.trans_eq
      ENNReal.toReal_one
  rw [h0, zero_sub] at heq
  have hlog : Real.log (π.real s) < 0 := Real.log_neg hp hp1
  nlinarith

/-- Every target `target f` charges every set of positive Lebesgue measure. -/
theorem target_ne_zero {f : ℝ → ℝ} (hf : Measurable f) (hint : Integrable fun x => Real.exp (-f x))
    {s : Set ℝ} (hs : volume s ≠ 0) : target f s ≠ 0 := by
  have hac : volume ≪ target f := by
    refine withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (measurable_targetDensity hf)).aemeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have := targetNormalizer_pos hint
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, targetDensity]
    positivity
  exact fun h => hs (hac h)

/-- For a target `π = target f`, the half-line law `π[|[0,∞)]` has finite, nonzero KL. -/
theorem klDiv_cond_Ici_target {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable fun x => Real.exp (-f x)) :
    klDiv (target f)[|Ici 0] (target f) ≠ ⊤ ∧ 0 < (klDiv (target f)[|Ici 0] (target f)).toReal := by
  have := isProbabilityMeasure_target hint
  refine klDiv_cond_self _ measurableSet_Ici (target_ne_zero hf hint (by simp)) fun h1 => ?_
  have h2 : target f (Ici 0)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Ici).2 h1
  rw [compl_Ici] at h2
  exact target_ne_zero hf hint (by simp) h2

/-! ### Final general forms (`ProximalGeneralLSI`), 1D -/

/-- A bounded, non-convex perturbation: `W = 1_{[0,∞)}`. -/
noncomputable def stepW (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

/-- The non-log-concave potential `f(x) = x²/2 + 1_{x ≥ 0}`. -/
noncomputable def fStep (x : ℝ) : ℝ := gaussPotential 1 x + stepW x

/-- `stepW` is measurable. -/
theorem measurable_stepW : Measurable stepW :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- `0 ≤ stepW ≤ 1`. -/
theorem stepW_bounds (x : ℝ) : 0 ≤ stepW x ∧ stepW x ≤ 1 := by
  unfold stepW; split_ifs <;> norm_num

/-- `fStep` is measurable. -/
theorem measurable_fStep : Measurable fStep :=
  (measurable_gaussPotential 1).add measurable_stepW

/-- `FunctionalLSI (target fStep) (1/α)` with `α = e^{-1}` (Holley–Stroock). -/
theorem functionalLSI_fStep : LogSobolev.FunctionalLSI (target fStep) (1 / Real.exp (-1)) := by
  have h := HolleyStroock.functionalLSI_target_gaussPotential_add one_pos measurable_stepW
    (fun x => (stepW_bounds x).1) (fun x => (stepW_bounds x).2)
  rw [show (1 : ℝ) / Real.exp (-1) = Real.exp (1 - 0) / 1 by
    rw [sub_zero, div_one, Real.exp_neg, one_div, inv_inv]]
  exact h

/-- **Non-vacuity of `ProximalGeneralLSI.toReal_klDiv_iterate_le_sq_general` /
`tvSup_iterate_le_sq_general` for a non-log-concave target.** For `π = target fStep`
(`f = x²/2 + 1_{x≥0}`, not convex), `α = e^{-1}`, any `η > 0`, the envelope is found by
`exists_envelope_of_lower_bound`, and `ρ₀ = π[|[0,∞)]` has `0 < KL(ρ₀‖π) < ∞`; the theorem
then gives finite KL and the rate for all iterates, and the TV bound. -/
theorem general_iterate_step {η : ℝ} (hη : 0 < η) (k : ℕ) :
    0 < (klDiv (target fStep)[|Ici 0] (target fStep)).toReal ∧
    klDiv ((fun ν => proxKernel fStep η ∘ₘ ν)^[k] ((target fStep)[|Ici 0])) (target fStep) ≠ ⊤ ∧
    (klDiv ((fun ν => proxKernel fStep η ∘ₘ ν)^[k] ((target fStep)[|Ici 0]))
        (target fStep)).toReal
      ≤ (klDiv (target fStep)[|Ici 0] (target fStep)).toReal
        / (1 + Real.exp (-1) * η) ^ (2 * k) ∧
    TotalVariation.tvSup ((fun ν => proxKernel fStep η ∘ₘ ν)^[k] ((target fStep)[|Ici 0]))
        (target fStep)
      ≤ √((klDiv (target fStep)[|Ici 0] (target fStep)).toReal
        / (2 * (1 + Real.exp (-1) * η) ^ (2 * k))) := by
  obtain ⟨hint, C₂, -, henv⟩ := ProximalGeneralLSI.exists_envelope_of_lower_bound
    measurable_fStep (a := 0) one_pos fun x => by
      simp [fStep, (stepW_bounds x).1]
  have := isProbabilityMeasure_target hint
  have hs0 : target fStep (Ici 0) ≠ 0 := target_ne_zero measurable_fStep hint (by simp)
  have : IsProbabilityMeasure ((target fStep)[|Ici 0]) := cond_isProbabilityMeasure hs0
  obtain ⟨hfin, hpos⟩ := klDiv_cond_Ici_target measurable_fStep hint
  set ρ : ℕ → Measure ℝ := fun j => (fun ν => proxKernel fStep η ∘ₘ ν)^[j] ((target fStep)[|Ici 0])
  have hstep : ∀ j, ρ (j + 1) = proxKernel fStep η ∘ₘ ρ j := fun j =>
    Function.iterate_succ_apply' _ _ _
  have : IsProbabilityMeasure (ρ 0) := by simpa [ρ]
  obtain ⟨-, h1, h2⟩ := ProximalGeneralLSI.toReal_klDiv_iterate_le_sq_general measurable_fStep
    (Real.exp_pos _) hη functionalLSI_fStep henv ρ hstep hfin k
  have h3 := ProximalGeneralLSI.tvSup_iterate_le_sq_general measurable_fStep
    (Real.exp_pos _) hη functionalLSI_fStep henv ρ hstep hfin k
  exact ⟨hpos, h1, h2, h3⟩

/-- A conditioned law is warm: `π[|s] ≤ (π.real s)⁻¹ • π` (as `ENNReal.ofReal`). -/
theorem cond_le_smul {X : Type*} [MeasurableSpace X] (π : Measure X) [IsFiniteMeasure π]
    {s : Set X} (hs0 : π s ≠ 0) : π[|s] ≤ ENNReal.ofReal (π.real s)⁻¹ • π := by
  have hp : 0 < π.real s := ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  rw [ENNReal.ofReal_inv_of_pos hp, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine Measure.le_iff'.2 fun t => ?_
  change ((π s)⁻¹ • π.restrict s) t ≤ ((π s)⁻¹ • π) t
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (Measure.restrict_apply_le _ _) _

/-- **Non-vacuity of the regularity route to the sharp rate (`ProximalSharpLSI`), non-Gaussian
target.** For `π = target fStep`, `α = e^{-1}`, `η > 0` and the warm law `ρ = π[|[0,∞)]`
(`0 < KL(ρ‖π) < ∞`), `HeatFlowRegular ρ π (Ioi 0)` and
`BackwardHeatFlowRegular π (forwardKernel η ∘ₘ ρ) η` are discharged (warmness lemmas), so
`toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI` and `exists_backwardHeatFlow_of_targetLSI`
apply; the forward-only `LogSobolevExtension.toReal_klDiv_proxKernel_comp_le_of_targetLSI_Ioi`
applies as well. -/
theorem sharpLSI_step {η : ℝ} (hη : 0 < η) :
    0 < (klDiv (target fStep)[|Ici 0] (target fStep)).toReal ∧
    (klDiv (proxKernel fStep η ∘ₘ (target fStep)[|Ici 0]) (target fStep)).toReal
      ≤ (klDiv (target fStep)[|Ici 0] (target fStep)).toReal
        / (1 + Real.exp (-1) * η) ^ 2 ∧
    (klDiv (proxKernel fStep η ∘ₘ (target fStep)[|Ici 0]) (target fStep)).toReal
      ≤ (klDiv (target fStep)[|Ici 0] (target fStep)).toReal / (1 + Real.exp (-1) * η) ∧
    ∃ Kb Ib : ℝ → ℝ, BackwardHeatFlowDissipation fStep η
        (forwardKernel η ∘ₘ (target fStep)[|Ici 0]) Kb Ib ∧
      BackwardHeatFlowLSI (Real.exp (-1)) η Kb Ib := by
  obtain ⟨hint, C₂, hC₂, henv⟩ := ProximalGeneralLSI.exists_envelope_of_lower_bound
    measurable_fStep (a := 0) one_pos fun x => by
      simp [fStep, (stepW_bounds x).1]
  have := isProbabilityMeasure_target hint
  have := isMarkovKernel_forwardKernel hη
  have hs0 : target fStep (Ici 0) ≠ 0 := target_ne_zero measurable_fStep hint (by simp)
  have : IsProbabilityMeasure ((target fStep)[|Ici 0]) := cond_isProbabilityMeasure hs0
  obtain ⟨hfin, hpos⟩ := klDiv_cond_Ici_target measurable_fStep hint
  have hwarm := cond_le_smul (target fStep) hs0
  have hC : 0 ≤ ((target fStep).real (Ici 0))⁻¹ := by positivity
  have hmom := ProximalGeneralLSI.integrable_sq_of_envelope henv
  have hreg := HeatFlowRegularityWarm.heatFlowRegular_of_warm _ _ hC hwarm hmom
  have hwarmY := ProximalSharpPerturbed.comp_le_smul_comp (forwardKernel η) hwarm
  have hfinY : klDiv (forwardKernel η ∘ₘ (target fStep)[|Ici 0])
      (forwardKernel η ∘ₘ target fStep) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_comp_right_le _ _ _)
  have hbreg := ProximalSharpPerturbed.backwardHeatFlowRegular_of_warm (target fStep)
    (forwardKernel η ∘ₘ (target fStep)[|Ici 0]) hη hC hwarmY one_pos hC₂ (by simpa using henv)
  refine ⟨hpos, (ProximalSharpLSI.toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI
    measurable_fStep hη (Real.exp_pos _) _ hfin hreg (fun t ht => ht.1) hbreg
    functionalLSI_fStep).2, (LogSobolevExtension.toReal_klDiv_proxKernel_comp_le_of_targetLSI_Ioi
    measurable_fStep hint hη (Real.exp_pos _) _ hfin hreg functionalLSI_fStep).2,
    ProximalSharpLSI.exists_backwardHeatFlow_of_targetLSI measurable_fStep hη
    (Real.exp_pos _) _ hfinY hbreg functionalLSI_fStep⟩

/-! ### Strongly log-concave forms, 1D -/

/-- The strongly log-concave, non-Gaussian potential `f(x) = x²/2 + |x|`. -/
noncomputable def fAbs (x : ℝ) : ℝ := gaussPotential 1 x + |x|

/-- `fAbs - x²/2 = |x|` is convex, so `fAbs` is `1`-strongly convex. -/
theorem convexOn_fAbs : ConvexOn ℝ univ fun x => fAbs x - gaussPotential 1 x := by
  have h : ConvexOn ℝ univ (fun x : ℝ => |x|) :=
    ⟨convex_univ, fun x _ y _ a b ha hb _ => by
      calc |a • x + b • y| ≤ |a • x| + |b • y| := abs_add_le _ _
        _ = a • |x| + b • |y| := by
          simp only [smul_eq_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]⟩
  simpa [fAbs] using h

/-- **Non-vacuity of `ProximalStronglyLogConcave.*_of_stronglyLogConcave` (1D), two starts.**
(i) Non-Gaussian target `target fAbs` (`α = 1`) from `ρ₀ = π[|[0,∞)]` with `0 < KL < ∞`;
(ii) Gaussian target `N(0,1)` from the non-warm `ρ₀ = N(m,1)`, `KL = m²/2`, where the bound is
attained (`klDiv_iterate_gaussTarget`). Both give the TV bound at every `k`. -/
theorem slc_iterate {η : ℝ} (hη : 0 < η) (m : ℝ) (k : ℕ) :
    (0 < (klDiv (target fAbs)[|Ici 0] (target fAbs)).toReal ∧
      TotalVariation.tvSup ((fun ν => proxKernel fAbs η ∘ₘ ν)^[k] ((target fAbs)[|Ici 0]))
        (target fAbs)
      ≤ √((klDiv (target fAbs)[|Ici 0] (target fAbs)).toReal / (2 * (1 + 1 * η) ^ (2 * k)))) ∧
    (klDiv ((fun ν => proxKernel (gaussPotential 1) η ∘ₘ ν)^[k] (gaussianReal m 1))
        (target (gaussPotential 1))).toReal
      ≤ (m ^ 2 / 2) / (1 + 1 * η) ^ (2 * k) := by
  have hf : Measurable fAbs :=
    ProximalStronglyLogConcave.measurable_of_convexOn_sub_gaussPotential convexOn_fAbs
  obtain ⟨hint, -⟩ := ProximalGeneralLSI.exists_envelope_of_strongConvex one_pos convexOn_fAbs
  have := isProbabilityMeasure_target hint
  have hs0 : target fAbs (Ici 0) ≠ 0 := target_ne_zero hf hint (by simp)
  have : IsProbabilityMeasure ((target fAbs)[|Ici 0]) := cond_isProbabilityMeasure hs0
  obtain ⟨hfin, hpos⟩ := klDiv_cond_Ici_target hf hint
  set ρ : ℕ → Measure ℝ := fun j => (fun ν => proxKernel fAbs η ∘ₘ ν)^[j] ((target fAbs)[|Ici 0])
  have : IsProbabilityMeasure (ρ 0) := by simpa [ρ]
  refine ⟨⟨hpos, ProximalStronglyLogConcave.tvSup_iterate_le_sq_of_stronglyLogConcave one_pos
    hη convexOn_fAbs ρ (fun j => Function.iterate_succ_apply' _ _ _) hfin k⟩, ?_⟩
  set σ : ℕ → Measure ℝ := fun j =>
    (fun ν => proxKernel (gaussPotential 1) η ∘ₘ ν)^[j] (gaussianReal m 1)
  have : IsProbabilityMeasure (σ 0) := by
    simp only [σ, Function.iterate_zero, id]; infer_instance
  have h := (ProximalStronglyLogConcave.toReal_klDiv_iterate_le_sq_of_stronglyLogConcave one_pos
    hη (by simpa using convexOn_const (0 : ℝ) convex_univ) σ
    (fun j => Function.iterate_succ_apply' _ _ _) (by simp [σ, klDiv_gauss]) k).2.2
  have e : (klDiv (σ 0) (target (gaussPotential 1))).toReal = m ^ 2 / 2 := by
    simp only [σ, Function.iterate_zero, id, klDiv_gauss]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [e] at h
  exact h

/-! ### Final forms on `Fin d → ℝ` -/

section Pi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi FormalizeSampling.LogSobolevPi

variable {d : ℕ}

/-- Every target `targetPi f` charges every set of positive Lebesgue measure. -/
theorem targetPi_ne_zero {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable fun x => Real.exp (-f x)) {s : Set (Fin d → ℝ)} (hs : volume s ≠ 0) :
    targetPi f s ≠ 0 := by
  have hac : volume ≪ targetPi f := by
    refine withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (measurable_targetDensityPi hf)).aemeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have := targetNormalizerPi_pos hint
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, targetDensityPi]
    positivity
  exact fun h => hs (hac h)

/-- The half-space `{x | 0 ≤ x i₀}`. -/
def halfSpace (i₀ : Fin d) : Set (Fin d → ℝ) := {x | 0 ≤ x i₀}

/-- The half-space is measurable. -/
theorem measurableSet_halfSpace (i₀ : Fin d) : MeasurableSet (halfSpace i₀) :=
  measurableSet_le measurable_const (measurable_pi_apply i₀)

/-- A box `∏ᵢ [aᵢ, aᵢ + 1]` has Lebesgue measure `≠ 0`. -/
theorem volume_box_ne_zero (a : Fin d → ℝ) :
    volume (Set.pi univ fun i => Icc (a i) (a i + 1)) ≠ 0 := by
  rw [volume_pi_pi]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by simp

/-- For `π = targetPi f` and `i₀ : Fin d`, `π[|{x | 0 ≤ x i₀}]` has finite, nonzero KL. -/
theorem klDiv_cond_halfSpace {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable fun x => Real.exp (-f x)) (i₀ : Fin d) :
    targetPi f (halfSpace i₀) ≠ 0 ∧ klDiv (targetPi f)[|halfSpace i₀] (targetPi f) ≠ ⊤ ∧
      0 < (klDiv (targetPi f)[|halfSpace i₀] (targetPi f)).toReal := by
  have := isProbabilityMeasure_targetPi hint
  have h0 : targetPi f (halfSpace i₀) ≠ 0 := by
    refine targetPi_ne_zero hf hint fun h => volume_box_ne_zero (d := d) (fun _ => 0) ?_
    refine measure_mono_null (fun x hx => ?_) h
    simpa [halfSpace] using (hx i₀ (mem_univ _)).1
  refine ⟨h0, klDiv_cond_self _ (measurableSet_halfSpace i₀) h0 fun h1 => ?_⟩
  have h2 : targetPi f (halfSpace i₀)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (measurableSet_halfSpace i₀)).2 h1
  refine targetPi_ne_zero hf hint (volume_box_ne_zero (d := d) (fun _ => -2)) (measure_mono_null
    (fun x hx => ?_) h2)
  have := (hx i₀ (mem_univ _)).2
  simp only [halfSpace, mem_compl_iff, mem_ofPred_eq, not_le]
  linarith

/-- The non-log-concave potential `f(x) = |x|²/2 + 1_{x_{i₀} ≥ 0}` on `Fin d → ℝ`. -/
noncomputable def fStepPi (i₀ : Fin d) (x : Fin d → ℝ) : ℝ :=
  gaussPotentialPi 1 x + stepW (x i₀)

/-- `fStepPi i₀` is measurable. -/
theorem measurable_fStepPi (i₀ : Fin d) : Measurable (fStepPi i₀) :=
  (measurable_gaussPotentialPi 1).add (measurable_stepW.comp (measurable_pi_apply i₀))

/-- `FunctionalLSIPi (targetPi (fStepPi i₀)) (1/α)` with `α = e^{-1}` (Holley–Stroock). -/
theorem functionalLSIPi_fStepPi (i₀ : Fin d) :
    FunctionalLSIPi (targetPi (fStepPi i₀)) (1 / Real.exp (-1)) := by
  have h := GaussianFunctionalLSIPi.functionalLSIPi_targetPi_gaussPotentialPi_add one_pos
    (measurable_stepW.comp (measurable_pi_apply i₀)) (fun x => (stepW_bounds (x i₀)).1)
    (fun x => (stepW_bounds (x i₀)).2)
  rw [show (1 : ℝ) / Real.exp (-1) = Real.exp (1 - 0) / 1 by
    rw [sub_zero, div_one, Real.exp_neg, one_div, inv_inv]]
  exact h

/-- `targetPi (fStepPi i₀)` has integrable `e^{-f}` and a Gaussian envelope `C₂ • N(0, I)`. -/
theorem envelope_fStepPi (i₀ : Fin d) :
    Integrable (fun x => Real.exp (-fStepPi i₀ x)) ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      targetPi (fStepPi i₀)
        ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 ((1 : ℝ)⁻¹).toNNReal :=
  ProximalGeneralLSIPi.exists_envelope_of_lower_boundPi (measurable_fStepPi i₀) (a := 0)
    one_pos fun x => by simp [fStepPi, (stepW_bounds (x i₀)).1]

/-- **Non-vacuity of `ProximalGeneralLSIPi.*_general` (iterate + TV) on `Fin d → ℝ`, `d ≥ 1`,
non-log-concave target** `targetPi (fStepPi i₀)`, `α = e^{-1}`, start `π[|{x_{i₀} ≥ 0}]` with
`0 < KL < ∞`. -/
theorem generalPi_iterate (i₀ : Fin d) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    0 < (klDiv (targetPi (fStepPi i₀))[|halfSpace i₀] (targetPi (fStepPi i₀))).toReal ∧
    (klDiv ((fun ν => proxKernelPi (fStepPi i₀) η ∘ₘ ν)^[k]
        ((targetPi (fStepPi i₀))[|halfSpace i₀])) (targetPi (fStepPi i₀))).toReal
      ≤ (klDiv (targetPi (fStepPi i₀))[|halfSpace i₀] (targetPi (fStepPi i₀))).toReal
        / (1 + Real.exp (-1) * η) ^ (2 * k) ∧
    TotalVariation.tvSup ((fun ν => proxKernelPi (fStepPi i₀) η ∘ₘ ν)^[k]
        ((targetPi (fStepPi i₀))[|halfSpace i₀])) (targetPi (fStepPi i₀))
      ≤ √((klDiv (targetPi (fStepPi i₀))[|halfSpace i₀] (targetPi (fStepPi i₀))).toReal
        / (2 * (1 + Real.exp (-1) * η) ^ (2 * k))) := by
  obtain ⟨hint, C₂, -, henv⟩ := envelope_fStepPi i₀
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hs0, hfin, hpos⟩ := klDiv_cond_halfSpace (measurable_fStepPi i₀) hint i₀
  have : IsProbabilityMeasure ((targetPi (fStepPi i₀))[|halfSpace i₀]) :=
    cond_isProbabilityMeasure hs0
  set ρ : ℕ → Measure (Fin d → ℝ) := fun j => (fun ν => proxKernelPi (fStepPi i₀) η ∘ₘ ν)^[j]
    ((targetPi (fStepPi i₀))[|halfSpace i₀])
  have : IsProbabilityMeasure (ρ 0) := by simpa [ρ]
  have hstep : ∀ j, ρ (j + 1) = proxKernelPi (fStepPi i₀) η ∘ₘ ρ j := fun j =>
    Function.iterate_succ_apply' _ _ _
  exact ⟨hpos, (ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general (measurable_fStepPi i₀)
    (Real.exp_pos _) hη (functionalLSIPi_fStepPi i₀) henv ρ hstep hfin k).2.2,
    ProximalGeneralLSIPi.tvSupPi_iterate_le_sq_general (measurable_fStepPi i₀)
    (Real.exp_pos _) hη (functionalLSIPi_fStepPi i₀) henv ρ hstep hfin k⟩

/-- **Non-vacuity of the `Fin d → ℝ` regularity routes** (`ProximalLSIPi`,
`ProximalSharpLSIPi`) for the warm start `ρ = π[|{x_{i₀} ≥ 0}]`, `π = targetPi (fStepPi i₀)`:
`HeatFlowRegularPi ρ π (Ioi 0)` and `BackwardHeatFlowRegularPi π (N_η ∘ₘ ρ) η` are discharged. -/
theorem sharpLSIPi_step (i₀ : Fin d) {η : ℝ} (hη : 0 < η) :
    (klDiv (proxKernelPi (fStepPi i₀) η ∘ₘ (targetPi (fStepPi i₀))[|halfSpace i₀])
        (targetPi (fStepPi i₀))).toReal
      ≤ (klDiv (targetPi (fStepPi i₀))[|halfSpace i₀] (targetPi (fStepPi i₀))).toReal
        / (1 + Real.exp (-1) * η) ^ 2 ∧
    (klDiv (proxKernelPi (fStepPi i₀) η ∘ₘ (targetPi (fStepPi i₀))[|halfSpace i₀])
        (targetPi (fStepPi i₀))).toReal
      ≤ (klDiv (targetPi (fStepPi i₀))[|halfSpace i₀] (targetPi (fStepPi i₀))).toReal
        / (1 + Real.exp (-1) * η) := by
  obtain ⟨hint, C₂, hC₂, henv⟩ := envelope_fStepPi i₀
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hs0, hfin, -⟩ := klDiv_cond_halfSpace (measurable_fStepPi i₀) hint i₀
  have : IsProbabilityMeasure ((targetPi (fStepPi i₀))[|halfSpace i₀]) :=
    cond_isProbabilityMeasure hs0
  have hwarm := cond_le_smul (targetPi (fStepPi i₀)) hs0
  have hC : 0 ≤ ((targetPi (fStepPi i₀)).real (halfSpace i₀))⁻¹ := by positivity
  have hmom := ProximalGeneralLSIPi.integrable_sum_sq_of_envelopePi henv
  have hreg := HeatFlowRegularityWarmPi.heatFlowRegularPi_of_warm _ _ hC hwarm hmom
  have hwarmY := ProximalSharpPerturbedPi.comp_le_smul_comp (forwardKernelPi η) hwarm
  have hbreg := ProximalSharpPerturbedPi.backwardHeatFlowRegularPi_of_warm _ _ hη hC hwarmY
    (by norm_num) hC₂ henv
  exact ⟨(ProximalSharpLSIPi.toReal_klDiv_proxKernelPi_comp_le_sq_of_targetLSIPi
    (measurable_fStepPi i₀) hη (Real.exp_pos _) _ hfin hreg (fun t ht => ht.1) hbreg
    (functionalLSIPi_fStepPi i₀)).2, (ProximalLSIPi.toReal_klDiv_proxKernelPi_comp_le_of_targetLSIPi
    (measurable_fStepPi i₀) hint hη (Real.exp_pos _) _ hfin hreg (functionalLSIPi_fStepPi i₀)).2⟩

end Pi

/-! ### Coupling / log-concave forms -/

/-- The shift coupling `(X + c, X)`, `X ~ π`, on `ℝ`. -/
noncomputable def shift1 (π : Measure ℝ) (c : ℝ) : Measure (ℝ × ℝ) := π.map fun x => (x + c, x)

/-- The shift coupling of a finite measure is finite. -/
instance (π : Measure ℝ) [IsFiniteMeasure π] (c : ℝ) : IsFiniteMeasure (shift1 π c) := by
  unfold shift1; infer_instance

/-- First marginal of the shift coupling: `π` shifted by `c`. -/
theorem shift1_fst (π : Measure ℝ) (c : ℝ) : (shift1 π c).map Prod.fst = π.map (· + c) := by
  rw [shift1, Measure.map_map measurable_fst (by fun_prop)]; rfl

/-- Second marginal of the shift coupling: `π`. -/
theorem shift1_snd (π : Measure ℝ) (c : ℝ) : (shift1 π c).map Prod.snd = π := by
  rw [shift1, Measure.map_map measurable_snd (by fun_prop)]; exact Measure.map_id

/-- Quadratic cost of the shift coupling: `∫⁻ (x - y)²/K = c²/K`. -/
theorem shift1_cost (π : Measure ℝ) [IsProbabilityMeasure π] (c K : ℝ) :
    ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / K) ∂(shift1 π c) = ENNReal.ofReal (c ^ 2 / K) := by
  rw [shift1, lintegral_map (by fun_prop) (by fun_prop)]; simp

/-- **Non-vacuity of `ProximalRegularization.klDiv_proxKernel_comp_le_coupling` (any target).**
For the non-log-concave `π = target fStep`, `ρ = π shifted by c` and the shift coupling:
`KL(proxKernel fStep η ∘ₘ ρ‖π) ≤ c²/(2η) < ∞`. -/
theorem regularization_step {η : ℝ} (hη : 0 < η) (c : ℝ) :
    klDiv (proxKernel fStep η ∘ₘ (target fStep).map (· + c)) (target fStep)
      ≤ ENNReal.ofReal (c ^ 2 / (2 * η)) := by
  obtain ⟨hint, -⟩ := ProximalGeneralLSI.exists_envelope_of_lower_bound measurable_fStep (a := 0)
    one_pos fun x => by simp [fStep, (stepW_bounds x).1]
  have := isProbabilityMeasure_target hint
  rw [← shift1_cost (target fStep) c]
  exact ProximalRegularization.klDiv_proxKernel_comp_le_coupling measurable_fStep hint hη _
    (shift1_fst _ c) (shift1_snd _ c)

/-- **Non-vacuity of `ProximalLogConcave.klDiv_iterate_le_coupling` and
`ProximalLogConcaveRate.klDiv_iterate_le_div` (1D, convex `f`).** For `π = target fAbs`,
`ρ₀ = π` shifted by `c`, and the shift coupling: `KL(ρ_{k+1}‖π) ≤ c²/(2η)` and
`KL(ρ_{k+1}‖π) ≤ c²/(2(k+1)η)`, both finite. -/
theorem logConcave_iterate {η : ℝ} (hη : 0 < η) (c : ℝ) (k : ℕ) :
    klDiv ((fun ν => proxKernel fAbs η ∘ₘ ν)^[k + 1] ((target fAbs).map (· + c))) (target fAbs)
      ≤ ENNReal.ofReal (c ^ 2 / (2 * η)) ∧
    klDiv ((fun ν => proxKernel fAbs η ∘ₘ ν)^[k + 1] ((target fAbs).map (· + c))) (target fAbs)
      ≤ ENNReal.ofReal (c ^ 2 / (2 * ((k : ℝ) + 1) * η)) := by
  obtain ⟨hint, -⟩ := ProximalGeneralLSI.exists_envelope_of_strongConvex one_pos convexOn_fAbs
  have := isProbabilityMeasure_target hint
  have hconv : ConvexOn ℝ univ fAbs := by
    have H := ((Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).smul (c := (1 / 2 : ℝ))
      (by norm_num)).add convexOn_fAbs
    exact H.congr fun x _ => by simp [fAbs, gaussPotential]; ring
  set ρ : ℕ → Measure ℝ := fun j => (fun ν => proxKernel fAbs η ∘ₘ ν)^[j]
    ((target fAbs).map (· + c))
  have hstep : ∀ j, ρ (j + 1) = proxKernel fAbs η ∘ₘ ρ j := fun j =>
    Function.iterate_succ_apply' _ _ _
  constructor
  · rw [← shift1_cost (target fAbs) c]
    exact ProximalLogConcave.klDiv_iterate_le_coupling hconv hint hη ρ hstep _
      (shift1_fst _ c) (shift1_snd _ c) k
  · rw [← shift1_cost (target fAbs) c]
    exact ProximalLogConcaveRate.klDiv_iterate_le_div hconv hint hη ρ hstep _
      (shift1_fst _ c) (shift1_snd _ c) k

/-! ### Strongly log-concave and coupling forms on `Fin d → ℝ` -/

section Pi2

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi FormalizeSampling.LogSobolevPi
open Matrix

variable {d : ℕ}

/-- The non-separable strongly convex potential `f(x) = |x|²/2 + ‖x‖_∞` on `Fin d → ℝ`. -/
noncomputable def fNormPi (x : Fin d → ℝ) : ℝ := gaussPotentialPi 1 x + ‖x‖

/-- `fNormPi - |x|²/2 = ‖x‖_∞` is convex. -/
theorem convexOn_fNormPi : ConvexOn ℝ univ fun x : Fin d → ℝ => fNormPi x - gaussPotentialPi 1 x :=
  (convexOn_norm convex_univ).congr fun x _ => by simp [fNormPi]

/-- **Non-vacuity of `ProximalStronglyLogConcaveGeneralPi` (no separability).** For the
non-separable `π = targetPi fNormPi` (`α = 1`, `d ≥ 1`) and `ρ₀ = π[|{x_{i₀} ≥ 0}]`
(`0 < KL < ∞`): the one-step and TV bounds hold;
for the Gaussian `N(0, I)` from the non-warm `ρ₀ = N(m, I)` (`KL = |m|²/2`) the one-step bound
holds. -/
theorem slcPi (i₀ : Fin d) {η : ℝ} (hη : 0 < η) (m : Fin d → ℝ) (k : ℕ) :
    (0 < (klDiv (targetPi fNormPi)[|halfSpace i₀] (targetPi (d := d) fNormPi)).toReal ∧
      TotalVariation.tvSup ((fun ν => proxKernelPi fNormPi η ∘ₘ ν)^[k]
        ((targetPi fNormPi)[|halfSpace i₀])) (targetPi (d := d) fNormPi)
        ≤ √((klDiv (targetPi fNormPi)[|halfSpace i₀] (targetPi (d := d) fNormPi)).toReal
          / (2 * (1 + 1 * η) ^ (2 * k))) ∧
      (klDiv (proxKernelPi fNormPi η ∘ₘ (targetPi fNormPi)[|halfSpace i₀])
          (targetPi (d := d) fNormPi)).toReal
        ≤ (klDiv (targetPi fNormPi)[|halfSpace i₀] (targetPi (d := d) fNormPi)).toReal
          / (1 + 1 * η) ^ 2) ∧
    (klDiv (proxKernelPi (gaussPotentialPi 1) η ∘ₘ
        Measure.pi fun i => gaussianReal (m i) ((1 : ℝ)⁻¹).toNNReal)
        (targetPi (gaussPotentialPi (d := d) 1))).toReal
      ≤ (∑ i, m i ^ 2) / 2 / (1 + 1 * η) ^ 2 := by
  have hf : Measurable (fNormPi (d := d)) :=
    ProximalStronglyLogConcaveGeneralPi.measurable_of_convexOn_sub_gaussPotentialPi
      convexOn_fNormPi
  obtain ⟨hint, -⟩ := ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi one_pos
    convexOn_fNormPi
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hs0, hfin, hpos⟩ := klDiv_cond_halfSpace hf hint i₀
  have : IsProbabilityMeasure ((targetPi fNormPi)[|halfSpace i₀]) := cond_isProbabilityMeasure hs0
  set ρ : ℕ → Measure (Fin d → ℝ) := fun j => (fun ν => proxKernelPi fNormPi η ∘ₘ ν)^[j]
    ((targetPi fNormPi)[|halfSpace i₀])
  have : IsProbabilityMeasure (ρ 0) := by simpa [ρ]
  refine ⟨⟨hpos, ProximalStronglyLogConcaveGeneralPi.tvSupPi_iterate_le_sq_of_stronglyLogConcave
    one_pos hη convexOn_fNormPi ρ (fun j => Function.iterate_succ_apply' _ _ _) hfin k,
    (ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_proxKernelPi_comp_le_sq_of_stronglyLogConcave
    one_pos hη convexOn_fNormPi _ hfin).2⟩, ?_⟩
  have hKL := klDiv_pi_gaussTarget (d := d) one_pos m
  have h :=
    (ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_proxKernelPi_comp_le_sq_of_stronglyLogConcave
      one_pos hη (f := gaussPotentialPi 1) (by simpa using convexOn_const (0 : ℝ) convex_univ)
    (Measure.pi fun i => gaussianReal (m i) ((1 : ℝ)⁻¹).toNNReal) (by rw [hKL]; simp)).2
  rw [hKL, ENNReal.toReal_ofReal (by positivity), one_mul] at h
  exact h

/-- The potential `f(x) = |x|²/2 + ‖x‖_∞ + cos(∑ᵢ xᵢ)` on `Fin d → ℝ`: the strongly convex,
non-separable `fNormPi` plus the bounded, non-convex perturbation `cos(∑ᵢ xᵢ) ∈ [-1, 1]`. For
`d ≥ 2` the target is not log-concave: on the diagonal `x = (t, …, t)`,
`f = d t²/2 + |t| + cos(d t)` has second derivative `d - d² cos(d t) < 0` for small `t > 0`. -/
noncomputable def fNormCosPi (x : Fin d → ℝ) : ℝ := fNormPi x + Real.cos (∑ i, x i)

/-- **Non-vacuity of `ProximalPerturbedGeneralPi` (bounded perturbation of a strongly
log-concave target).** For `π = targetPi fNormCosPi` (`α = 1`, `a = -1`, `b = 1`, `d ≥ 1`) and
`ρ₀ = π[|{x_{i₀} ≥ 0}]` (`0 < KL < ∞`), the iterates of the exact proximal sampler satisfy
`KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + e^{-2} η)^{2k}`. -/
theorem slcCosPi_iterate (i₀ : Fin d) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    0 < (klDiv (targetPi fNormCosPi)[|halfSpace i₀] (targetPi (d := d) fNormCosPi)).toReal ∧
    (klDiv ((fun ν => proxKernelPi fNormCosPi η ∘ₘ ν)^[k]
        ((targetPi fNormCosPi)[|halfSpace i₀])) (targetPi (d := d) fNormCosPi)).toReal
      ≤ (klDiv (targetPi fNormCosPi)[|halfSpace i₀] (targetPi (d := d) fNormCosPi)).toReal
        / (1 + Real.exp (-2) * η) ^ (2 * k) := by
  have hf : Measurable (fNormPi (d := d)) :=
    ProximalStronglyLogConcaveGeneralPi.measurable_of_convexOn_sub_gaussPotentialPi
      convexOn_fNormPi
  have hW : Measurable fun x : Fin d → ℝ => Real.cos (∑ i, x i) := by fun_prop
  obtain ⟨hint₀, -⟩ := ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi one_pos
    convexOn_fNormPi
  have hint : Integrable fun x => Real.exp (-fNormCosPi (d := d) x) :=
    HeatFlowRegularityPerturbedPi.integrable_exp_neg_add hf hint₀ hW
      fun x => Real.neg_one_le_cos _
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨hs0, hfin, hpos⟩ := klDiv_cond_halfSpace (hf.add hW) hint i₀
  have : IsProbabilityMeasure ((targetPi fNormCosPi)[|halfSpace i₀]) :=
    cond_isProbabilityMeasure hs0
  set ρ : ℕ → Measure (Fin d → ℝ) := fun j => (fun ν => proxKernelPi fNormCosPi η ∘ₘ ν)^[j]
    ((targetPi fNormCosPi)[|halfSpace i₀])
  have : IsProbabilityMeasure (ρ 0) := by simpa [ρ]
  have h := (ProximalPerturbedGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave_add
    (f₀ := fNormPi) (W := fun x => Real.cos (∑ i, x i)) one_pos hη convexOn_fNormPi hW
    (fun x => Real.neg_one_le_cos _) (fun x => Real.cos_le_one _) ρ
    (fun j => Function.iterate_succ_apply' _ _ _) hfin k).2.2
  refine ⟨hpos, h.trans_eq ?_⟩
  norm_num
  rfl

/-- The shift coupling `(X + c, X)`, `X ~ π`, on `Fin d → ℝ`. -/
noncomputable def shiftPi (π : Measure (Fin d → ℝ)) (c : Fin d → ℝ) :
    Measure ((Fin d → ℝ) × (Fin d → ℝ)) := π.map fun x => (x + c, x)

/-- The shift coupling of a finite measure is finite. -/
instance (π : Measure (Fin d → ℝ)) [IsFiniteMeasure π] (c : Fin d → ℝ) :
    IsFiniteMeasure (shiftPi π c) := by
  unfold shiftPi; infer_instance

/-- First marginal of the shift coupling on `Fin d → ℝ`. -/
theorem shiftPi_fst (π : Measure (Fin d → ℝ)) (c : Fin d → ℝ) :
    (shiftPi π c).map Prod.fst = π.map (· + c) := by
  rw [shiftPi, Measure.map_map measurable_fst (by fun_prop)]; rfl

/-- Second marginal of the shift coupling on `Fin d → ℝ`. -/
theorem shiftPi_snd (π : Measure (Fin d → ℝ)) (c : Fin d → ℝ) :
    (shiftPi π c).map Prod.snd = π := by
  rw [shiftPi, Measure.map_map measurable_snd (by fun_prop)]; exact Measure.map_id

/-- Quadratic cost of the shift coupling: `∫⁻ |x - y|²/K = |c|²/K`. -/
theorem shiftPi_cost (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] (c : Fin d → ℝ) (K : ℝ) :
    ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / K) ∂(shiftPi π c)
      = ENNReal.ofReal ((∑ i, c i ^ 2) / K) := by
  rw [shiftPi, lintegral_map (by unfold sqDist; fun_prop) (by fun_prop)]; simp [sqDist]

/-- The rotated-separable-plus-quadratic potential with `U = 1`, `B = 0`, `λ = 0`,
`gᵢ = fAbs`, written exactly in the form of `RGOCouplingRotationPi`. -/
noncomputable def fRot (x : Fin d → ℝ) : ℝ :=
  ∑ i, fAbs (((1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ x) i) + 0 / 2 * (x ⬝ᵥ x)
    - ((0 : Matrix (Fin 1) (Fin d) ℝ) *ᵥ x) ⬝ᵥ ((0 : Matrix (Fin 1) (Fin d) ℝ) *ᵥ x) / 2

/-- `fRot` is the separable potential `∑ᵢ fAbs(xᵢ)`. -/
theorem fRot_eq : (fRot (d := d)) = sepPotential fun _ => fAbs := by
  funext x; simp [fRot, sepPotential]

/-- **Non-vacuity of the `1/k` forms on `Fin d → ℝ`** (`ProximalRegularization.klDiv_proxKernelPi_
comp_le_coupling`, `ProximalLogConcaveRateGeneralPi.klDiv_iteratePi_le_div_of_hasLipRep` with
`HasLipRep` from `RGOCouplingPi.hasLipRep_rgoKernelPi_separable`, and
`RGOCouplingRotationPi.klDiv_iteratePi_le_div_rotated_separable_add_quadratic`): for the convex
`fRot = ∑ᵢ fAbs(xᵢ)`, `ρ₀ = π` shifted by `c`, the bounds `|c|²/(2η)` and `|c|²/(2(k+1)η)`
follow. -/
theorem logConcavePi (c : Fin d → ℝ) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    klDiv (proxKernelPi fRot η ∘ₘ (targetPi fRot).map (· + c)) (targetPi fRot)
      ≤ ENNReal.ofReal ((∑ i, c i ^ 2) / (2 * η)) ∧
    klDiv ((fun ν => proxKernelPi fRot η ∘ₘ ν)^[k + 1] ((targetPi fRot).map (· + c)))
        (targetPi (d := d) fRot)
      ≤ ENNReal.ofReal ((∑ i, c i ^ 2) / (2 * ((k : ℝ) + 1) * η)) ∧
    klDiv ((fun ν => proxKernelPi fRot η ∘ₘ ν)^[k + 1] ((targetPi fRot).map (· + c)))
        (targetPi (d := d) fRot)
      ≤ ENNReal.ofReal ((∑ i, c i ^ 2) / (2 * ((k : ℝ) + 1) * η)) := by
  have h1 : Measurable fAbs :=
    ProximalStronglyLogConcave.measurable_of_convexOn_sub_gaussPotential convexOn_fAbs
  obtain ⟨hint1, -⟩ := ProximalGeneralLSI.exists_envelope_of_strongConvex one_pos
    convexOn_fAbs
  have hconv : ConvexOn ℝ univ fAbs := by
    have H := ((Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).smul (c := (1 / 2 : ℝ))
      (by norm_num)).add convexOn_fAbs
    exact H.congr fun x _ => by simp [fAbs, gaussPotential]; ring
  have hint : Integrable fun x => Real.exp (-fRot (d := d) x) := by
    rw [fRot_eq]; exact integrable_exp_neg_sepPotential fun _ => hint1
  have hf : Measurable (fRot (d := d)) := by
    rw [fRot_eq]; exact measurable_sepPotential fun _ => h1
  have := isProbabilityMeasure_targetPi hint
  set ρ : ℕ → Measure (Fin d → ℝ) := fun j => (fun ν => proxKernelPi fRot η ∘ₘ ν)^[j]
    ((targetPi fRot).map (· + c))
  have hstep : ∀ j, ρ (j + 1) = proxKernelPi fRot η ∘ₘ ρ j := fun j =>
    Function.iterate_succ_apply' _ _ _
  have hrep := RGOCouplingPi.hasLipRep_rgoKernelPi_separable (f := fRot (d := d))
    (g := fun _ => fAbs) (fun x => by rw [fRot_eq]; rfl) (fun _ => hconv) (fun _ => hint1) hη
  refine ⟨?_, ?_, ?_⟩
  · rw [← shiftPi_cost (targetPi fRot) c]
    exact ProximalRegularization.klDiv_proxKernelPi_comp_le_coupling hf hint hη _
      (shiftPi_fst _ c) (shiftPi_snd _ c)
  · rw [← shiftPi_cost (targetPi fRot) c]
    exact ProximalLogConcaveRateGeneralPi.klDiv_iteratePi_le_div_of_hasLipRep hf hint hη hrep ρ
      hstep _ (shiftPi_fst _ c) (shiftPi_snd _ c) k
  · rw [← shiftPi_cost (targetPi fRot) c]
    exact RGOCouplingRotationPi.klDiv_iteratePi_le_div_rotated_separable_add_quadratic
      (U := 1) (B := 0) (lam := 0) (g := fun _ => fAbs) (by simp) (fun _ => hconv)
      (fun _ => hint1) (fun x => rfl) le_rfl (fun z => by simp) hη ρ hstep _
      (shiftPi_fst _ c) (shiftPi_snd _ c) k

end Pi2

/-! ### The strongly log-concave rate on `EuclideanSpace ℝ (Fin d)` -/

section Euclid

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.Euclidean FormalizeSampling.EuclideanTransfer WithLp

variable {d : ℕ}

/-- **Non-vacuity of the `EuclideanSpace` form of PX-6 (`EuclideanTransfer`).** For the potential
`g(x) = ‖x‖²/2` on `EuclideanSpace ℝ (Fin d)` (`α = 1`, `π = N(0, I)`) and Mathlib's Gaussian
start `ρ₀ = multivariateGaussian m 1 = N(m, I)`: `KL(ρ₀‖π) = ‖m‖²/2` (finite, and positive for
`m ≠ 0`), and the TV bound of `tvSup_iterateEuclid_le_sq_of_stronglyLogConcave` holds along the
Euclidean proximal sampler. -/
theorem slcEuclid {η : ℝ} (hη : 0 < η) (m : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    klDiv (multivariateGaussian m 1)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun x => -(‖x‖ ^ 2 / 2))
      = ENNReal.ofReal (‖m‖ ^ 2 / 2) ∧
    TotalVariation.tvSup ((fun ν => proxKernelEuclid (fun x => ‖x‖ ^ 2 / 2) η ∘ₘ ν)^[k]
        (multivariateGaussian m 1)) (volume.tilted fun x => -(‖x‖ ^ 2 / 2))
      ≤ √(‖m‖ ^ 2 / 2 / (2 * (1 + 1 * η) ^ (2 * k))) := by
  have hconv : ConvexOn ℝ univ fun x : EuclideanSpace ℝ (Fin d) =>
      ‖x‖ ^ 2 / 2 - 1 * ‖x‖ ^ 2 / 2 := by
    simpa using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)))
  have hg : (fun x : Fin d → ℝ => ‖toLp 2 x‖ ^ 2 / 2) = gaussPotentialPi 1 := by
    funext x
    rw [gaussPotentialPi_eq_norm_sq, one_mul]
  have hρ0 : (multivariateGaussian m (1 : Matrix (Fin d) (Fin d) ℝ)).map ofLp =
      Measure.pi fun i => gaussianReal (ofLp m i) ((1 : ℝ)⁻¹).toNNReal := by
    have h := map_ofLp_multivariateGaussian m 1
    rw [NNReal.coe_one, one_smul] at h
    rw [h, inv_one, Real.toNNReal_one]
  have hKL : klDiv (multivariateGaussian m 1)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun x => -(‖x‖ ^ 2 / 2)) =
        ENNReal.ofReal (‖m‖ ^ 2 / 2) := by
    rw [klDiv_tilted_eq_klDiv_targetPi (fun x => ‖x‖ ^ 2 / 2), hρ0, hg,
      klDiv_pi_gaussTarget one_pos, sum_sq_eq_norm_toLp_sq, one_mul]
  refine ⟨hKL, ?_⟩
  set ρ : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun j =>
    (fun ν => proxKernelEuclid (fun x => ‖x‖ ^ 2 / 2) η ∘ₘ ν)^[j] (multivariateGaussian m 1)
  have h0 : ρ 0 = multivariateGaussian m 1 := rfl
  have : IsProbabilityMeasure (ρ 0) := by rw [h0]; infer_instance
  have h := tvSup_iterateEuclid_le_sq_of_stronglyLogConcave one_pos hη hconv ρ
    (fun j => Function.iterate_succ_apply' _ _ _) (by rw [h0, hKL]; exact ENNReal.ofReal_ne_top) k
  rw [h0, hKL, ENNReal.toReal_ofReal (by positivity)] at h
  exact h

end Euclid

end FormalizeSampling.Audit.ProximalGeneral
