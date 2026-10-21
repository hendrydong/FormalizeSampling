module

public import FormalizeSampling.Foundations.LogSobolevExtensionPi
public import FormalizeSampling.Foundations.LogSobolevTensorPi
public import FormalizeSampling.Foundations.GaussianFunctionalLSIPi
public import FormalizeSampling.Samplers.ProximalGaussianPi

/-!
# PX-2 on `Fin d → ℝ` from a functional LSI of the target

Status: **Conditional** only on the target's functional LSI and the de Bruijn regularity
`HeatFlowRegularPi`.

If `π = targetPi f` satisfies `FunctionalLSIPi π (1/α)`, then by convolution stability
(`LogSobolevTensorPi.functionalLSIPi_heatKernelPi_comp`) and Gross's inequality in dimension `d`
(`GaussianFunctionalLSIPi.functionalLSIPi_gaussian`), every heat-smoothed target
`π_t = π * N(0, t I)` satisfies the LSI with constant `1/α + t`. The bridge
`LogSobolevExtensionPi.toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI` then gives the
contraction of the proximal step by `1/(1 + α η)`.

## Main results

* `LogSobolevExtensionPi.toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI` (and `_Ioi`):
  `KL(proxKernelPi f η ∘ₘ ρ‖π) ≤ KL(ρ‖π)/(1 + α η)` for `π = targetPi f`, from
  `FunctionalLSIPi π_t (1/α + t)` for `t ∈ (0, η)`, `HeatFlowRegularPi` and `KL(ρ‖π) < ∞` (the
  extension of the LSI beyond `LSIClassPi` is `Foundations/LogSobolevExtensionPi.lean`).
* `functionalLSIPi_heatKernelPi_comp_targetPi`: `LSI(π, 1/α) ⇒ LSI(π_t, 1/α + t)`, `t > 0`.
* `toReal_klDiv_proxKernelPi_comp_le_of_targetLSIPi`: PX-2 in dimension `d`.

## Not proved here

* `HeatFlowRegularPi` for general targets (see `HeatFlowRegularityPerturbedPi` for Gaussians and
  their bounded perturbations).
* The sharp `(1 + α η)⁻²` rate is not proved here; see `ProximalSharpLSIPi` (under
  `BackwardHeatFlowRegularPi`), and `ProximalGeneralLSIPi` (no regularity hypotheses).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.LogSobolevExtensionPi

/-! ### PX-2 from the LSI of the smoothed targets -/

open FormalizeSampling.LogSobolevPi FormalizeSampling.HeatKernelPi
  FormalizeSampling.HeatFlowDeBruijnPi

variable {d : ℕ}

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalGaussianPi in
/-- **PX-2 on `Fin d → ℝ` for a general target (Conditional on the functional LSI of `π_t` and
`HeatFlowRegularPi`).** For measurable `f` with integrable `e^{-f}`, `π = targetPi f`,
`η, α > 0`, a probability law `ρ` with `KL(ρ‖π) < ∞`, `HeatFlowRegularPi ρ π s` with
`(0, η] ⊆ s`, and `FunctionalLSIPi (heatKernelPi t ∘ₘ π) (1/α + t)` for every `t ∈ (0, η)`
(which follows from `FunctionalLSIPi π (1/α)` by convolution stability, see
`ProximalLSIPi.toReal_klDiv_proxKernelPi_comp_le_of_targetLSIPi`):
`KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and `KL(proxKernelPi f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI {f : (Fin d → ℝ) → ℝ} {η α : ℝ}
    (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (hα : 0 < α) (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (targetPi f) ≠ ⊤) {s : Set ℝ} (hreg : HeatFlowRegularPi ρ (targetPi f) s)
    (hs : Ioc 0 η ⊆ s)
    (hπt : ∀ t ∈ Ioo 0 η,
      FunctionalLSIPi (heatKernelPi t.toNNReal ∘ₘ targetPi f) (1 / α + t)) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) := by
  have := isProbabilityMeasure_targetPi hint
  have hback := klDiv_proxKernelPi_comp_le_forward hf hint hη ρ
  rw [forwardKernelPi_eq_heatKernelPi] at hback
  have hfwd : klDiv (heatKernelPi η.toNNReal ∘ₘ ρ) (heatKernelPi η.toNNReal ∘ₘ targetPi f)
      ≠ ⊤ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  exact ⟨ne_top_of_le_ne_top hfwd hback, (ENNReal.toReal_mono hfwd hback).trans
    (toReal_klDiv_heatKernelPi_le_of_regular hα.le hη hKL hreg hs
      (heatFlowLSIPi_of_functionalLSIPi ρ (targetPi f) hα hπt hreg
        (Ioo_subset_Ioc_self.trans hs)))⟩

open FormalizeSampling.ProximalPi in
/-- PX-2 on `Fin d → ℝ` with regularity on all positive times: the special case `s = (0, ∞)` of
`toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI_Ioi {f : (Fin d → ℝ) → ℝ} {η α : ℝ}
    (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (hα : 0 < α) (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (targetPi f) ≠ ⊤) (hreg : HeatFlowRegularPi ρ (targetPi f) (Ioi 0))
    (hπt : ∀ t ∈ Ioo 0 η,
      FunctionalLSIPi (heatKernelPi t.toNNReal ∘ₘ targetPi f) (1 / α + t)) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) :=
  toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI hf hint hη hα ρ hKL hreg
    (fun _ ht => ht.1) hπt

end FormalizeSampling.LogSobolevExtensionPi

namespace FormalizeSampling.ProximalLSIPi

open FormalizeSampling.LogSobolevPi FormalizeSampling.ProximalPi FormalizeSampling.HeatKernelPi
  FormalizeSampling.HeatFlowDeBruijnPi

variable {d : ℕ}

/-- **LSI of the heat-smoothed target.** If `FunctionalLSIPi π C` for a probability measure `π`
on `Fin d → ℝ`, then for `t > 0`, `FunctionalLSIPi (heatKernelPi t ∘ₘ π) (C + t)`. -/
theorem functionalLSIPi_heatKernelPi_comp_targetPi {π : Measure (Fin d → ℝ)}
    [IsProbabilityMeasure π] {C t : ℝ} (ht : 0 < t) (hπ : FunctionalLSIPi π C) :
    FunctionalLSIPi (heatKernelPi t.toNNReal ∘ₘ π) (C + t) := by
  have hγ := GaussianFunctionalLSIPi.functionalLSIPi_gaussian (d := d) t ht
  have hγ' : FunctionalLSIPi (Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal)
      (t.toNNReal : ℝ) := by rwa [Real.coe_toNNReal _ ht.le]
  have h := LogSobolevTensorPi.functionalLSIPi_heatKernelPi_comp t.toNNReal hπ hγ'
  rwa [Real.coe_toNNReal _ ht.le] at h

/-- **PX-2 on `Fin d → ℝ` from a functional LSI of the target.** For measurable `f` with
integrable `e^{-f}`, `π = targetPi f` with `FunctionalLSIPi π (1/α)` (`α > 0`), `η > 0`, and a
probability law `ρ` with `KL(ρ‖π) < ∞` and `HeatFlowRegularPi ρ π (Ioi 0)`:
`KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelPi f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_of_targetLSIPi {f : (Fin d → ℝ) → ℝ} {η α : ℝ}
    (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (hα : 0 < α) (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (targetPi f) ≠ ⊤) (hreg : HeatFlowRegularPi ρ (targetPi f) (Ioi 0))
    (hπ : FunctionalLSIPi (targetPi f) (1 / α)) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) := by
  have := isProbabilityMeasure_targetPi hint
  exact LogSobolevExtensionPi.toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI_Ioi hf hint hη
    hα ρ hKL hreg fun t ht => functionalLSIPi_heatKernelPi_comp_targetPi ht.1 hπ

end FormalizeSampling.ProximalLSIPi
