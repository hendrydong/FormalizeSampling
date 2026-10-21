module

public import FormalizeSampling.Samplers.BackwardHeatFlowRegularityWarmPi
public import FormalizeSampling.Samplers.HeatFlowRegularityWarmPi
public import FormalizeSampling.Samplers.ProximalGeneralLSI

/-!
# Sharp PX-2 on `Fin d → ℝ` for a general LSI target with a Gaussian upper envelope

Status: **Conditional** only on the functional LSI of the target (no regularity or other named
hypotheses). `d`-dimensional counterpart of `Samplers/ProximalGeneralLSI.lean`.

Let `f : (Fin d → ℝ) → ℝ` be measurable, `π = targetPi f`, `α, η > 0`, and assume
1. `FunctionalLSIPi π (1/α)`, and
2. a **Gaussian upper envelope** `π ≤ C₂ • N(0, v I)` (as measures; `C₂`, `v` any reals).

Then for every probability law `ρ` with `KL(ρ‖π) < ∞` the exact proximal sampler satisfies
`KL(ρ P_prox‖π) ≤ KL(ρ‖π) / (1 + α η)²`; along the chain
`KL(ρ_k‖π) ≤ KL(ρ_0‖π) / (1 + α η)^{2k}` and `TV(ρ_k, π) ≤ √(KL(ρ_0‖π) / (2 (1 + α η)^{2k}))`.

Route. For warm `ρ ≤ C • π`: backward regularity is
`ProximalSharpPerturbedPi.backwardHeatFlowRegularPi_of_warm`
(`Samplers/BackwardHeatFlowRegularityWarmPi.lean`; envelope of `π` + warmness of `ρ Q_η`);
forward regularity is `HeatFlowRegularityWarmPi.heatFlowRegularPi_of_warm`, which needs only
`∫ |x|² dπ < ∞` (implied by the envelope, `integrable_sum_sq_of_envelopePi`); then
`ProximalSharpLSIPi`. Warmness is removed by `KLWarmApprox.klDiv_comp_le_of_warm` and the chain
is handled by `KLWarmApprox.klDiv_iterate_le_of_forall`. No extra regularity hypothesis on `π`
is needed, and no integrability or sign hypotheses: `KL(ρ‖π) < ∞` forces `∫ e^{-f} < ∞`
(`ProximalSharpLSIPi.integrable_exp_neg_of_klDiv_targetPi_ne_top`), and `exists_pos_envelopePi`
replaces `(C₂, v)` by `(max C₂ 0, w)` with `w > 0` (for `d ≥ 1` and `v ≤ 0`, `N(0, v I)` is a
Dirac mass, below which no absolutely continuous law lies; for `d = 0` every law on the
one-point space is a Dirac mass and any `w` works).

Strong convexity. If `f - α₀ |x|²/2` is convex (`α₀ > 0`), then `π ≤ C₂ • N(0, (2/α₀) I)`
(`exists_envelope_of_strongConvexPi`, in `Foundations/GibbsMeasure.lean`); with Bakry–Émery this
gives the sharp rate for strongly log-concave targets (`ProximalStronglyLogConcaveGeneralPi`).

## Main results

* `integrable_sum_sq_of_envelopePi`, `exists_pos_envelopePi`.
* `toReal_klDiv_proxKernelPi_comp_le_sq_of_warm_general` (warm start, one step).
* `toReal_klDiv_proxKernelPi_comp_le_sq_general` (one step),
  `toReal_klDiv_iteratePi_le_sq_general` (iterates), `tvSupPi_iterate_le_sq_general` (TV):
  any finite-KL start.

## Not proved here

* The LSI `FunctionalLSIPi (targetPi f) (1/α)` is a hypothesis (Bakry–Émery for strongly convex
  `f`, Holley–Stroock for bounded perturbations are proved elsewhere).
* Targets without a Gaussian upper envelope.
* Starts with `KL(ρ‖π) = ∞` (vacuous).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalGeneralLSIPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.LogSobolevPi FormalizeSampling.ProximalSharpLSIPi
open FormalizeSampling.ProximalSharpPerturbedPi FormalizeSampling.KLWarmApprox
open FormalizeSampling.HeatFlowRegularityWarmPi

variable {d : ℕ}

/-- A measure with a Gaussian upper envelope `π ≤ C₂ • N(0, v I)` has a finite second moment
`∫ ∑ᵢ xᵢ² dπ < ∞`. -/
theorem integrable_sum_sq_of_envelopePi {π : Measure (Fin d → ℝ)} {C₂ v : ℝ}
    (henv : π ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) :
    Integrable (fun x => ∑ i, x i ^ 2) π :=
  ((GaussianLSIPi.integrable_sum_sq_pi_gaussianReal (d := d) v).smul_measure
    ENNReal.ofReal_ne_top).mono_measure henv

section General

variable {f : (Fin d → ℝ) → ℝ} {α η C₂ v : ℝ}

/-- **A Gaussian envelope can be taken with positive variance and nonnegative constant.** If
`∫ e^{-f} < ∞` and `targetPi f ≤ C₂ • N(0, v I)` for some real `C₂` and `v`, then
`targetPi f ≤ (max C₂ 0) • N(0, w I)` for some `w > 0`. For `d ≥ 1` this holds with `w = v`
(for `v ≤ 0`, `N(0, v I)` is the Dirac mass at `0`, and the absolutely continuous probability
law `targetPi f` cannot lie below a multiple of it); for `d = 0` the product measure does not
depend on the variance and `w = 1`. -/
theorem exists_pos_envelopePi (hint : Integrable (fun x => Real.exp (-f x)))
    (henv : targetPi f
      ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) :
    ∃ w : ℝ, 0 < w ∧ targetPi f
      ≤ ENNReal.ofReal (max C₂ 0) • Measure.pi fun _ : Fin d => gaussianReal 0 w.toNNReal := by
  have := isProbabilityMeasure_targetPi hint
  have henv' : targetPi f
      ≤ ENNReal.ofReal (max C₂ 0) • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal := by
    rwa [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  rcases lt_or_ge 0 v with hv | hv
  · exact ⟨v, hv, henv'⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, one_pos, ?_⟩
    rwa [Measure.pi_of_empty (x := fun i => Fin.elim0 i),
      ← Measure.pi_of_empty (μ := fun _ : Fin 0 => gaussianReal 0 v.toNNReal)
        (x := fun i => Fin.elim0 i)]
  exfalso
  rw [Real.toNNReal_eq_zero.2 hv, gaussianReal_zero_var,
    MeasureHelpers.pi_dirac (fun _ => (0 : ℝ))] at henv'
  have hvol : (volume : Measure (Fin d → ℝ)) {fun _ => (0 : ℝ)} = 0 := by
    have hs : ({fun _ => (0 : ℝ)} : Set (Fin d → ℝ)) = univ.pi fun _ => {(0 : ℝ)} := by
      ext x; simp [funext_iff]
    rw [hs, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd⟩) Real.volume_singleton
  have h1 : targetPi f {fun _ => (0 : ℝ)}ᶜ ≤ 0 := by simpa using henv' {fun _ => (0 : ℝ)}ᶜ
  have h2 : targetPi f {fun _ => (0 : ℝ)} = 0 := withDensity_absolutelyContinuous _ _ hvol
  have h3 : targetPi f univ ≤ 0 := by
    calc targetPi f univ = targetPi f ({fun _ => (0 : ℝ)} ∪ {fun _ => (0 : ℝ)}ᶜ) := by
          rw [union_compl_self]
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 := by rw [h2, zero_add]; exact h1
  simp at h3

/-- **Sharp PX-2 on `Fin d → ℝ` for an LSI target with a Gaussian envelope, one step, warm
start (Conditional only on the target LSI).** Let `f` be measurable, `π = targetPi f`,
`α, η > 0`, with `FunctionalLSIPi π (1/α)` and `π ≤ C₂ • N(0, v I)` (`C₂`, `v` any reals). For a
probability law `ρ ≤ C • π` (`C ≥ 0`) with `KL(ρ‖π) < ∞`: `KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelPi f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. (`∫ e^{-f} < ∞` follows
from `KL(ρ‖π) < ∞`, and the envelope is normalised by `exists_pos_envelopePi`.) -/
theorem toReal_klDiv_proxKernelPi_comp_le_sq_of_warm_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSIPi (targetPi f) (1 / α))
    (henv : targetPi f ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {C : ℝ} (hC : 0 ≤ C)
    (hwarm : ρ ≤ ENNReal.ofReal C • targetPi f) (hKL : klDiv ρ (targetPi f) ≠ ⊤) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) ^ 2 := by
  have hint := integrable_exp_neg_of_klDiv_targetPi_ne_top ρ hKL
  have := isProbabilityMeasure_targetPi hint
  obtain ⟨w, hw, henvw⟩ := exists_pos_envelopePi hint henv
  have hbreg := backwardHeatFlowRegularPi_of_warm (targetPi f) (forwardKernelPi η ∘ₘ ρ) hη hC
    (comp_le_smul_comp _ hwarm) hw (le_max_right _ _) henvw
  exact toReal_klDiv_proxKernelPi_comp_le_sq_of_targetLSIPi hf hη hα ρ hKL
    (heatFlowRegularPi_of_warm ρ (targetPi f) hC hwarm (integrable_sum_sq_of_envelopePi henv))
    (fun t ht => ht.1) hbreg hπ

/-- **Sharp PX-2 on `Fin d → ℝ` for an LSI target with a Gaussian envelope, one step, any
finite-KL start (Conditional only on the target LSI).** Let `f` be measurable,
`π = targetPi f`, `α, η > 0`, with `FunctionalLSIPi π (1/α)` and `π ≤ C₂ • N(0, v I)` (`C₂`, `v`
any reals). For every probability law `ρ` with `KL(ρ‖π) < ∞`:
`KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelPi f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_sq_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSIPi (targetPi f) (1 / α))
    (henv : targetPi f ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (targetPi f) ≠ ⊤) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) ^ 2 := by
  have hint := integrable_exp_neg_of_klDiv_targetPi_ne_top ρ hKL
  have := isProbabilityMeasure_targetPi hint
  have := isMarkovKernel_proxKernelPi hf hint hη
  have h := klDiv_comp_le_of_warm (targetPi f) (proxKernelPi f η)
    (proxKernelPi_comp_targetPi hf hint hη) ((1 + α * η) ^ 2)⁻¹
    (fun ρ' _ C hC hw hK => by
      have := (toReal_klDiv_proxKernelPi_comp_le_sq_of_warm_general hf hα hη hπ
        henv ρ' hC hw hK).2
      rwa [div_eq_inv_mul] at this) ρ hKL
  rw [div_eq_inv_mul]
  exact h

/-- **Sharp PX-2 on `Fin d → ℝ` for an LSI target with a Gaussian envelope, iterated
(Conditional only on the target LSI).** Under the hypotheses of
`toReal_klDiv_proxKernelPi_comp_le_sq_general`, let `ρ (k+1) = proxKernelPi f η ∘ₘ ρ k` from a
probability law `ρ 0` with `KL(ρ 0‖π) < ∞`. Then for every `k`, `ρ k` is a probability law,
`KL(ρ k‖π) < ∞` and `KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iteratePi_le_sq_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSIPi (targetPi f) (1 / α))
    (henv : targetPi f ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (targetPi f) ≠ ⊤)
    (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (targetPi f) ≠ ⊤ ∧
      (klDiv (ρ k) (targetPi f)).toReal
        ≤ (klDiv (ρ 0) (targetPi f)).toReal / (1 + α * η) ^ (2 * k) := by
  have := isMarkovKernel_proxKernelPi hf (integrable_exp_neg_of_klDiv_targetPi_ne_top (ρ 0) hKL)
    hη
  obtain ⟨hp, hfin, hle⟩ := klDiv_iterate_le_of_forall (targetPi f) (proxKernelPi f η)
    (c := ((1 + α * η) ^ 2)⁻¹) (by positivity)
    (fun ρ' _ hK => by
      have h := toReal_klDiv_proxKernelPi_comp_le_sq_general hf hα hη hπ henv ρ' hK
      rw [div_eq_inv_mul] at h
      exact h) ρ hstep hKL k
  refine ⟨hp, hfin, ?_⟩
  rwa [pow_mul, div_eq_inv_mul, ← inv_pow]

/-- **TV form of the sharp rate on `Fin d → ℝ` (Conditional only on the target LSI).** Under the
hypotheses of `toReal_klDiv_iteratePi_le_sq_general`:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^(2k)))`. -/
theorem tvSupPi_iterate_le_sq_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSIPi (targetPi f) (1 / α))
    (henv : targetPi f ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (targetPi f) ≠ ⊤)
    (k : ℕ) :
    TotalVariation.tvSup (ρ k) (targetPi f)
      ≤ √((klDiv (ρ 0) (targetPi f)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨hp, hfin, hle⟩ :=
    toReal_klDiv_iteratePi_le_sq_general hf hα hη hπ henv ρ hstep hKL k
  have := isProbabilityMeasure_targetPi (integrable_exp_neg_of_klDiv_targetPi_ne_top (ρ 0) hKL)
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans (Real.sqrt_le_sqrt ?_)
  rw [mul_comm 2, ← div_div]
  exact div_le_div_of_nonneg_right hle (by norm_num)

end General

end FormalizeSampling.ProximalGeneralLSIPi
