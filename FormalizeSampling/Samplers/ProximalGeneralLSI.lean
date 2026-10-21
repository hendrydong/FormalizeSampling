module

public import FormalizeSampling.Samplers.BackwardHeatFlowRegularityWarm
public import FormalizeSampling.Samplers.HeatFlowRegularityWarm
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.KLWarmApprox
public import FormalizeSampling.Foundations.Pinsker

/-!
# Sharp PX-2 for a general LSI target with a Gaussian upper envelope

Status: **Conditional** only on the functional LSI of the target (dimension one; no regularity
or other named hypotheses).

Let `f : ℝ → ℝ` be measurable, `π = target f`, `α, η > 0`, and assume
1. `FunctionalLSI π (1/α)` (log-Sobolev inequality with constant `1/α`), and
2. a **Gaussian upper envelope** `π ≤ C₂ • N(0, v)` (as measures; `C₂`, `v` any reals).

Then for **every** probability law `ρ` with `KL(ρ‖π) < ∞` (no warmness, no moments, no further
regularity), the exact proximal sampler satisfies
`KL(ρ P_prox‖π) ≤ KL(ρ‖π) / (1 + α η)²`, and along the chain `ρ_{k+1} = ρ_k P_prox`
`KL(ρ_k‖π) ≤ KL(ρ_0‖π) / (1 + α η)^{2k}` and `TV(ρ_k, π) ≤ √(KL(ρ_0‖π) / (2 (1 + α η)^{2k}))`.

Route.
* Warm start `ρ ≤ C • π`: the backward regularity `BackwardHeatFlowRegular π (ρ Q_η) η` is
  `ProximalSharpPerturbed.backwardHeatFlowRegular_of_warm`
  (`Samplers/BackwardHeatFlowRegularityWarm.lean`; it only uses the envelope of `π`
  and warmness of `ρ Q_η ≤ C • π Q_η`); the forward regularity `HeatFlowRegular ρ π (Ioi 0)` is
  `HeatFlowRegularityWarm.heatFlowRegular_of_warm`, which needs only `∫ x² dπ < ∞` — implied by
  the envelope (`integrable_sq_of_envelope`). Then `ProximalSharpLSI` gives the sharp rate.
* Arbitrary finite-KL start: `KLWarmApprox.klDiv_comp_le_of_warm` (truncation of `dρ/dπ`,
  convexity of KL, data processing, `π P_prox = π`) and `klDiv_iterate_le_of_forall`.

**No integrability or sign hypotheses are needed.** `KL(ρ‖π) < ∞` forces `∫ e^{-f} < ∞`
(`ProximalSharpLSI.integrable_exp_neg_of_klDiv_target_ne_top`); the envelope forces `v > 0`
(`pos_of_envelope`: for `v ≤ 0`, `N(0, v)` is the Dirac mass at `0`); and `C₂` may be replaced
by `max C₂ 0` since `ENNReal.ofReal` clips at `0`.

**No extra hypothesis is needed for the forward regularity.** For warm `ρ` the ratio
`p_t/q_t ≤ C` is bounded, so the `π`-dependent terms of the de Bruijn integrands are dominated by
`C` times heat-flow bounds valid for every `π` with a second moment; the posterior second-moment
bound of `HeatFlowRegularityPerturbed` is not needed.

Strong convexity. If `f - α₀ x²/2` is convex (`α₀ > 0`), then π has the Gaussian envelope
`π ≤ C₂ • N(0, 2/α₀)` (`exists_envelope_of_strongConvex`, in `Foundations/GibbsMeasure.lean`).
Combined with Bakry–Émery (`FunctionalLSI π (1/α₀)`) this gives the sharp rate for strongly
log-concave targets (`ProximalStronglyLogConcave`).

## Main results

* `integrable_sq_of_envelope`: the envelope gives `∫ x² dπ < ∞`.
* `pos_of_envelope`: an envelope `target f ≤ C₂ • N(0, v)` forces `v > 0`.
* `toReal_klDiv_proxKernel_comp_le_sq_of_warm_general` (one step, warm start).
* `toReal_klDiv_proxKernel_comp_le_sq_general` (one step, any finite-KL start).
* `toReal_klDiv_iterate_le_sq_general` (iterates), `tvSup_iterate_le_sq_general` (TV).

## Not proved here

* The LSI itself: it is a hypothesis (`FunctionalLSI (target f) (1/α)`); for strongly convex
  `f` it is the Bakry–Émery theorem (`ProximalStronglyLogConcave`), for bounded perturbations
  of a Gaussian it is Holley–Stroock (`ProximalPerturbedGaussian`).
* Targets without a Gaussian upper envelope (e.g. LSI targets given only through tail bounds):
  the envelope is used for the backward regularity (`w_s, |w_s'|, |w_s''| ≲ e^{-κ z²}`).
* Starts with `KL(ρ‖π) = ∞` (vacuous).
* Dimension `d`: see `ProximalGeneralLSIPi`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalGeneralLSI

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp FormalizeSampling.LogSobolev
open FormalizeSampling.ProximalSharpLSI FormalizeSampling.ProximalSharpPerturbed
open FormalizeSampling.KLWarmApprox FormalizeSampling.HeatFlowRegularityWarm

/-! ### The Gaussian envelope gives a second moment -/

/-- A measure with a Gaussian upper envelope `π ≤ C₂ • N(0, v)` has a finite second moment. -/
theorem integrable_sq_of_envelope {π : Measure ℝ} {C₂ v : ℝ}
    (henv : π ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) :
    Integrable (fun x => x ^ 2) π :=
  (((memLp_id_gaussianReal 2).integrable_sq).smul_measure ENNReal.ofReal_ne_top).mono_measure
    henv

/-! ### General targets: warm start -/

section General

variable {f : ℝ → ℝ} {α η C₂ v : ℝ}

/-- **A Gaussian envelope has positive variance.** If `∫ e^{-f} < ∞` and
`target f ≤ C₂ • N(0, v)` for some real `C₂` and `v`, then `v > 0`: for `v ≤ 0`, `N(0, v)` is
the Dirac mass at `0`, and the absolutely continuous probability law `target f` gives mass `0`
to `{0}` and so cannot lie below a multiple of `δ₀`. -/
theorem pos_of_envelope (hint : Integrable (fun x => Real.exp (-f x)))
    (henv : target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) : 0 < v := by
  have := isProbabilityMeasure_target hint
  by_contra hv
  rw [Real.toNNReal_eq_zero.2 (not_lt.1 hv), gaussianReal_zero_var] at henv
  have h1 : target f {0}ᶜ ≤ 0 := by simpa using henv {0}ᶜ
  have h2 : target f {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton (a := 0))
  have h3 : target f univ ≤ 0 := by
    calc target f univ = target f ({0} ∪ {0}ᶜ) := by rw [union_compl_self]
      _ ≤ target f {0} + target f {0}ᶜ := measure_union_le _ _
      _ ≤ 0 := by rw [h2, zero_add]; exact h1
  simp at h3

/-- **Sharp PX-2 for an LSI target with a Gaussian envelope, one step, warm start
(Conditional only on the target LSI).** Let `f` be measurable, `π = target f`, `α, η > 0`, with
`FunctionalLSI π (1/α)` and `π ≤ C₂ • N(0, v)` (`C₂`, `v` any reals). For a probability law
`ρ ≤ C • π` (`C ≥ 0`) with `KL(ρ‖π) < ∞`: `KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. (`∫ e^{-f} < ∞` follows
from `KL(ρ‖π) < ∞`, `v > 0` from the envelope, and `C₂` may be replaced by `max C₂ 0`.) -/
theorem toReal_klDiv_proxKernel_comp_le_sq_of_warm_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSI (target f) (1 / α))
    (henv : target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {C : ℝ} (hC : 0 ≤ C)
    (hwarm : ρ ≤ ENNReal.ofReal C • target f) (hKL : klDiv ρ (target f) ≠ ⊤) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) ^ 2 := by
  have hint := integrable_exp_neg_of_klDiv_target_ne_top ρ hKL
  have := isProbabilityMeasure_target hint
  have := isMarkovKernel_forwardKernel hη
  have henv' : target f ≤ ENNReal.ofReal (max C₂ 0) • gaussianReal 0 v.toNNReal := by
    rwa [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  have hbreg := backwardHeatFlowRegular_of_warm (target f) (forwardKernel η ∘ₘ ρ) hη hC
    (comp_le_smul_comp _ hwarm) (pos_of_envelope hint henv) (le_max_right _ _) henv'
  exact toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI hf hη hα ρ hKL
    (heatFlowRegular_of_warm ρ (target f) hC hwarm (integrable_sq_of_envelope henv))
    (fun t ht => ht.1) hbreg hπ

/-! ### General targets: every finite-KL start -/

/-- **Sharp PX-2 for an LSI target with a Gaussian envelope, one step, any finite-KL start
(Conditional only on the target LSI).** Let `f` be measurable, `π = target f`, `α, η > 0`, with
`FunctionalLSI π (1/α)` and `π ≤ C₂ • N(0, v)` (`C₂`, `v` any reals). For every probability law
`ρ` with `KL(ρ‖π) < ∞`: `KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernel_comp_le_sq_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSI (target f) (1 / α))
    (henv : target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target f) ≠ ⊤) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) ^ 2 := by
  have hint := integrable_exp_neg_of_klDiv_target_ne_top ρ hKL
  have := isProbabilityMeasure_target hint
  have := isMarkovKernel_proxKernel hf hint hη
  have h := klDiv_comp_le_of_warm (target f) (proxKernel f η) (proxKernel_comp_target hf hint hη)
    ((1 + α * η) ^ 2)⁻¹
    (fun ρ' _ C hC hw hK => by
      have := (toReal_klDiv_proxKernel_comp_le_sq_of_warm_general hf hα hη hπ henv
        ρ' hC hw hK).2
      rwa [div_eq_inv_mul] at this) ρ hKL
  rw [div_eq_inv_mul]
  exact h

/-- **Sharp PX-2 for an LSI target with a Gaussian envelope, iterated (Conditional only on the
target LSI).** Under the hypotheses of `toReal_klDiv_proxKernel_comp_le_sq_general`, let
`ρ : ℕ → Measure ℝ` be the proximal-sampler laws (`ρ (k+1) = proxKernel f η ∘ₘ ρ k`) from a
probability law `ρ 0` with `KL(ρ 0‖π) < ∞`. Then for every `k`, `ρ k` is a probability law,
`KL(ρ k‖π) < ∞` and `KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iterate_le_sq_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSI (target f) (1 / α))
    (henv : target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ⊤)
    (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (target f) ≠ ⊤ ∧
      (klDiv (ρ k) (target f)).toReal
        ≤ (klDiv (ρ 0) (target f)).toReal / (1 + α * η) ^ (2 * k) := by
  have := isMarkovKernel_proxKernel hf (integrable_exp_neg_of_klDiv_target_ne_top (ρ 0) hKL) hη
  obtain ⟨hp, hfin, hle⟩ := klDiv_iterate_le_of_forall (target f) (proxKernel f η)
    (c := ((1 + α * η) ^ 2)⁻¹) (by positivity)
    (fun ρ' _ hK => by
      have h := toReal_klDiv_proxKernel_comp_le_sq_general hf hα hη hπ henv ρ' hK
      rw [div_eq_inv_mul] at h
      exact h) ρ hstep hKL k
  refine ⟨hp, hfin, ?_⟩
  rwa [pow_mul, div_eq_inv_mul, ← inv_pow]

/-- **TV form of the sharp rate (Conditional only on the target LSI).** Under the hypotheses of
`toReal_klDiv_iterate_le_sq_general`, with TV normalised as `sup_A |μ A - ν A|`:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^(2k)))`. -/
theorem tvSup_iterate_le_sq_general (hf : Measurable f)
    (hα : 0 < α) (hη : 0 < η) (hπ : FunctionalLSI (target f) (1 / α))
    (henv : target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ⊤)
    (k : ℕ) :
    TotalVariation.tvSup (ρ k) (target f)
      ≤ √((klDiv (ρ 0) (target f)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨hp, hfin, hle⟩ :=
    toReal_klDiv_iterate_le_sq_general hf hα hη hπ henv ρ hstep hKL k
  have := isProbabilityMeasure_target (integrable_exp_neg_of_klDiv_target_ne_top (ρ 0) hKL)
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans (Real.sqrt_le_sqrt ?_)
  rw [mul_comm 2, ← div_div]
  exact div_le_div_of_nonneg_right hle (by norm_num)

end General

end FormalizeSampling.ProximalGeneralLSI
