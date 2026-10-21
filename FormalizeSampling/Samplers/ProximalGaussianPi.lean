module

public import FormalizeSampling.Samplers.ProximalSharpPi
public import FormalizeSampling.Foundations.GaussianLSIPi

/-!
# PX-2 in dimension `d` for isotropic Gaussian targets

Status: **Verified** for every probability law with finite KL and finite second moment (no
named functional inequality and no regularity hypothesis: `HeatFlowRegularPi` is derived from
the second moment by `Foundations/HeatFlowRegularityPerturbedPi.lean`).

The forward kernel of the proximal sampler, `ProximalPi.forwardKernelPi η`, is by definition the
heat kernel `HeatKernelPi.heatKernelPi η.toNNReal` (`forwardKernelPi_eq_heatKernelPi`). Combining
the backward-step bound `ProximalPi.klDiv_proxKernelPi_comp_le_forward` with the forward heat-step
contraction `GaussianLSIPi.toReal_klDiv_heatKernelPi_le_gaussian` (whose log-Sobolev input is the
Gaussian LSI along the heat flow, proved there) gives the PX-2 contraction for
`π = N(0, α⁻¹ I)` and every probability law `ρ` with finite KL and finite second moment.

## Main results

* `forwardKernelPi_eq_heatKernelPi`: the two Gaussian kernels coincide.
* `toReal_klDiv_proxKernelPi_comp_le_gaussPotentialPi`:
  `KL(proxKernelPi f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)` for `f(x) = α ‖x‖² / 2`; alias:
  `HeatFlowRegularityPi.toReal_klDiv_proxKernelPi_comp_le_gaussPotentialPi_of_moment`.
* `ProximalSharpGaussianPi.integrable_sum_sq_heatKernelPi_comp`: the heat kernel preserves a
  finite second moment (`heatKernelPi t ∘ₘ ρ` is `ρ` convolved with `N(0, t I)`,
  `ProximalSharpGaussianPi.heatKernelPi_comp_eq_map_prod`).

## Not proved here

* The sharp `(1 + α η)⁻²` rate: `ProximalStronglyLogConcaveGeneralPi` (with `f = α |x|²/2`);
  attained by Gaussian starts (`ProximalSharpPi.klDiv_iteratePi_gaussTarget`).
* Non-Gaussian targets in dimension `d`: see `ProximalLSIPi` (the LSI of `π * N(0, t I)` from
  a functional LSI of `π`) and `ProximalGeneralLSIPi`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalGaussianPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
  FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi

variable {d : ℕ}

/-- The forward kernel of the proximal sampler is the heat kernel with variance `η`
(no assumptions; `forwardKernelPi` is defined as this kernel `x ↦ ⊗ᵢ N(xᵢ, η)`). -/
theorem forwardKernelPi_eq_heatKernelPi (η : ℝ) :
    forwardKernelPi (d := d) η = heatKernelPi η.toNNReal := rfl

/-- **PX-2 in dimension `d` for the isotropic Gaussian target, with no named functional
inequality.** For `α, η > 0`, `f(x) = α (∑ᵢ xᵢ²) / 2` with target `π = targetPi f = N(0, α⁻¹ I)`,
and a probability law `ρ` on `Fin d → ℝ` with `KL(ρ‖π) < ∞` and finite second moment
`∫ ∑ᵢ xᵢ² dρ < ∞`:
`KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelPi f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_gaussPotentialPi {α η : ℝ} (hα : 0 < α)
    (hη : 0 < η) (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (targetPi (gaussPotentialPi (d := d) α)) ≠ ⊤)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ ρ) (targetPi (gaussPotentialPi α)) ≠ ⊤ ∧
      (klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ ρ)
          (targetPi (gaussPotentialPi α))).toReal
        ≤ (klDiv ρ (targetPi (gaussPotentialPi (d := d) α))).toReal / (1 + α * η) := by
  have hback := klDiv_proxKernelPi_comp_le_forward (measurable_gaussPotentialPi α)
    (integrable_exp_neg_gaussPotentialPi hα) hη ρ
  rw [forwardKernelPi_eq_heatKernelPi] at hback
  rw [targetPi_gaussPotentialPi hα] at hKL hback ⊢
  have hfwd : klDiv (heatKernelPi η.toNNReal ∘ₘ ρ)
      (heatKernelPi η.toNNReal ∘ₘ Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal)
      ≠ ⊤ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  exact ⟨ne_top_of_le_ne_top hfwd hback, (ENNReal.toReal_mono hfwd hback).trans
    (toReal_klDiv_heatKernelPi_le_gaussian hα hη ρ hKL hmom)⟩

end FormalizeSampling.ProximalGaussianPi

namespace FormalizeSampling.HeatFlowRegularityPi

/-- **PX-2 in dimension `d` for the isotropic Gaussian target.** Alias of
`ProximalGaussianPi.toReal_klDiv_proxKernelPi_comp_le_gaussPotentialPi`: the same statement
(`KL(ρ‖π) < ∞` and `∫ ∑ᵢ xᵢ² dρ < ∞` give `KL(proxKernelPi f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)`
for `f(x) = α (∑ᵢ xᵢ²) / 2`). -/
alias toReal_klDiv_proxKernelPi_comp_le_gaussPotentialPi_of_moment :=
  ProximalGaussianPi.toReal_klDiv_proxKernelPi_comp_le_gaussPotentialPi

end FormalizeSampling.HeatFlowRegularityPi

/-! ### Second moments along the heat kernel -/

namespace FormalizeSampling.ProximalSharpGaussianPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.GaussianLSIPi

variable {d : ℕ}

/-- The isotropic heat kernel is the convolution with `N(0, t I)`:
`heatKernelPi t ∘ₘ ρ = (ρ ⊗ N(0, t I)).map (x, z) ↦ z + x` (no assumptions beyond `ρ` being
s-finite). -/
theorem heatKernelPi_comp_eq_map_prod (ρ : Measure (Fin d → ℝ)) [SFinite ρ] (t : ℝ≥0) :
    heatKernelPi t ∘ₘ ρ =
      (ρ.prod (Measure.pi fun _ : Fin d => gaussianReal 0 t)).map (fun p => p.2 + p.1) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply ((by fun_prop : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      p.2 + p.1) hs)]
  refine lintegral_congr fun x => ?_
  rw [heatKernelPi_apply, GaussianIncrement.pi_gaussianReal_eq_map,
    Measure.map_apply (by fun_prop) hs]
  rfl

/-- The second moment is preserved by the heat kernel: if `∫ ∑ᵢ xᵢ² dρ < ∞` then
`∫ ∑ᵢ yᵢ² d(heatKernelPi t ∘ₘ ρ) < ∞`. -/
theorem integrable_sum_sq_heatKernelPi_comp (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x => ∑ i, x i ^ 2) ρ) (t : ℝ) :
    Integrable (fun x => ∑ i, x i ^ 2) (heatKernelPi t.toNNReal ∘ₘ ρ) := by
  rw [heatKernelPi_comp_eq_map_prod,
    integrable_map_measure (continuous_sum_sq (d := d)).aestronglyMeasurable (by fun_prop)]
  have hg := integrable_sum_sq_pi_gaussianReal (d := d) t
  show Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ∑ i, (p.2 i + p.1 i) ^ 2) _
  refine (((hρ.comp_fst _).const_mul 2).add ((hg.comp_snd ρ).const_mul 2)).mono'
    (by fun_prop : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ∑ i, (p.2 i + p.1 i) ^ 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (p.2 i - p.1 i)]

end FormalizeSampling.ProximalSharpGaussianPi
