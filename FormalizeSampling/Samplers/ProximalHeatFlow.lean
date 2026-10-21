module

public import FormalizeSampling.Foundations.GaussianLSI
public import FormalizeSampling.Foundations.LogSobolevExtension
public import FormalizeSampling.Samplers.ProximalContraction

/-!
# PX-2 forward step from the heat flow (1D)

Status: **Verified** for the reduction of the proximal step to the heat flow; the general
contraction is **Conditional** only on the log-Sobolev inequality of `π_t` along the flow at
positive times (or on `FunctionalLSI (target f) (1/α)`), on `HeatFlowRegular` and on
`KL(ρ‖π) < ∞`. The Gaussian instance needs only a finite second moment and `KL(ρ‖π) < ∞`.

The forward step of the proximal sampler is the heat kernel: `forwardKernel η ∘ₘ ρ = ρ_η` with
`ρ_t = heatKernel t ∘ₘ ρ` (`ProximalContraction.heatKL_eq_forwardKernel`), and the backward
(RGO) step does not increase KL to `π` (`ProximalContraction.klDiv_proxKernel_comp_le_forward`).
The heat-flow inputs (de Bruijn's identity, `HeatFlowRegular`, the Gaussian LSI along the flow
and the functional-LSI bridge) are in `Foundations/HeatFlowDeBruijn.lean`,
`Foundations/GaussianLSI.lean` and `Foundations/LogSobolevExtension.lean`; the declarations
below live in the namespaces of those developments.

## Main results

* `HeatFlowDeBruijn.toReal_klDiv_forwardKernel_le_of_regular`,
  `HeatFlowDeBruijn.toReal_klDiv_proxKernel_comp_le_of_regular`: PX-2 forward-step contraction
  `KL(proxKernel f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)` with `HeatFlowDissipation` replaced by
  `HeatFlowRegular` (only the LSI along the flow, for `t ∈ (0, η)`, remains assumed).
* `GaussianLSI.toReal_klDiv_nonpos_of_heatFlowLSI`: `HeatFlowLSI ρ π α η (heatFisher ρ π)`
  (which includes `t = 0`, where `heatFisher ρ π 0 = 0`) forces `KL(ρ‖π) = 0` when `α, η > 0`;
  so that named hypothesis is not dischargeable as stated with `I = heatFisher`, and the
  contractions here need the LSI only on `(0, η)`.
* `GaussianLSI.toReal_klDiv_proxKernel_comp_le_gaussPotential` (**PX-2, Gaussian target**) and
  its alias `HeatFlowRegularity.toReal_klDiv_proxKernel_comp_le_gaussPotential_of_moment`:
  `KL(proxKernel f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)` for `f = α x²/2`.
* `LogSobolevExtension.toReal_klDiv_proxKernel_comp_le_of_targetLSI` (and `_Ioi`)
  (**PX-2, non-Gaussian target**): the same bound from `FunctionalLSI (target f) (1/α)`,
  `HeatFlowRegular ρ (target f) s` (`(0, η] ⊆ s`) and `KL(ρ‖π) < ∞`.

## Not proved here

* `HeatFlowRegular ρ (target f) s` and `FunctionalLSI (target f) (1/α)` for non-Gaussian `f`.
* The sharp rate `(1 + α η)^{-2}`, which also uses the backward step (`ProximalSharpLSI`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped FormalizeSampling.OU

namespace FormalizeSampling.HeatFlowDeBruijn

/-! ### The forward step under `HeatFlowRegular` -/

open FormalizeSampling.ProximalContraction

variable {ρ π : Measure ℝ}

/-- Forward step of the proximal sampler, Conditional only on the LSI along the flow: under the
hypotheses of `heatKL_le_div_of_regular`,
`KL(forwardKernel η ∘ₘ ρ ‖ forwardKernel η ∘ₘ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_forwardKernel_le_of_regular [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) (hKL : klDiv ρ π ≠ ⊤)
    {s : Set ℝ} (hreg : HeatFlowRegular ρ π s) (hs : Ioc 0 η ⊆ s)
    (hL : ∀ t ∈ Ioo 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * heatFisher ρ π t) :
    (klDiv (FormalizeSampling.Proximal.forwardKernel η ∘ₘ ρ)
        (FormalizeSampling.Proximal.forwardKernel η ∘ₘ π)).toReal
      ≤ (klDiv ρ π).toReal / (1 + α * η) := by
  rw [← heatKL_eq_forwardKernel ρ π hη, ← heatKL_zero ρ π]
  exact heatKL_le_div_of_regular hα hη hKL hreg hs hL

open FormalizeSampling.Proximal in
/-- **PX-2 with de Bruijn discharged (Conditional only on the LSI along the flow).** For
measurable `f`
with integrable `exp ∘ (-f)`, `π = target f`, `η > 0`, `α ≥ 0`, a probability law `ρ` with
`KL(ρ‖π) < ∞`, regularity `HeatFlowRegular ρ π s` with `(0, η] ⊆ s`, and
`2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` for `t ∈ (0, η)`: `KL(proxKernel f η ∘ₘ ρ ‖ π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ ‖ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_proxKernel_comp_le_of_regular {f : ℝ → ℝ} {η : ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target f) ≠ ⊤) {s : Set ℝ}
    (hreg : HeatFlowRegular ρ (target f) s) (hs : Ioc 0 η ⊆ s)
    (hL : ∀ t ∈ Ioo 0 η,
      2 * α * heatKL ρ (target f) t ≤ (1 + α * t) * heatFisher ρ (target f) t) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) := by
  have := isMarkovKernel_forwardKernel hη
  have := isProbabilityMeasure_target hint
  have hfwd : klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target f) ≠ ⊤ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  have hback := klDiv_proxKernel_comp_le_forward hf hint hη ρ
  refine ⟨ne_top_of_le_ne_top hfwd hback, ?_⟩
  exact (ENNReal.toReal_mono hfwd hback).trans
    (toReal_klDiv_forwardKernel_le_of_regular hα hη hKL hreg hs hL)

end FormalizeSampling.HeatFlowDeBruijn

namespace FormalizeSampling.GaussianLSI

/-! ### The Gaussian target -/

open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction

/-- **`HeatFlowLSI ρ π α η (heatFisher ρ π)` forces `KL(ρ‖π) = 0`.** Since the time-`0` slot of
`HeatFlowLSI` is included (`t ∈ Ico 0 η`) and `heatFisher ρ π 0 = 0` (`heatDensity 0 ≡ 0`), for
`α, η > 0` the hypothesis implies `KL(ρ‖π).toReal ≤ 0`. Hence the named hypothesis `hL` of
`ProximalContraction.toReal_klDiv_proxKernel_comp_le` (and
`ProximalSharp.toReal_klDiv_proxKernel_comp_le_sq`) cannot be discharged with `I = heatFisher`
for `ρ ≠ π` (it can with the true Fisher information, e.g. for Gaussians).
`HeatFlowDeBruijn.toReal_klDiv_proxKernel_comp_le_of_regular` and
`toReal_klDiv_proxKernel_comp_le_gaussPotential` below use only `t ∈ (0, η)`. -/
theorem toReal_klDiv_nonpos_of_heatFlowLSI {ρ π : Measure ℝ} {α η : ℝ} (hα : 0 < α)
    (hη : 0 < η) (hL : HeatFlowLSI ρ π α η (heatFisher ρ π)) : (klDiv ρ π).toReal ≤ 0 := by
  have := hL 0 ⟨le_rfl, hη⟩
  rw [heatFisher_zero, heatKL_zero, mul_zero] at this
  nlinarith

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp in
/-- **PX-2 for the Gaussian target with no named functional inequality.** For `α, η > 0`, the
Gaussian potential `f(x) = α x² / 2` with target `π = target f = N(0, 1/α)`, and a probability
law `ρ` on `ℝ` with `KL(ρ‖π) < ∞` and finite second moment `∫ x² dρ < ∞`, the exact proximal
step contracts KL: `KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`.
The log-Sobolev input is proved (`heatFlowLSI_gaussPotential_of_pos`) and the de Bruijn
regularity is derived from the second moment (`HeatFlowRegularity.heatFlowRegular_gaussPotential`).
No regularity or functional-inequality hypothesis remains. -/
theorem toReal_klDiv_proxKernel_comp_le_gaussPotential {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target (gaussPotential α)) ≠ ⊤)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    klDiv (proxKernel (gaussPotential α) η ∘ₘ ρ) (target (gaussPotential α)) ≠ ⊤ ∧
      (klDiv (proxKernel (gaussPotential α) η ∘ₘ ρ) (target (gaussPotential α))).toReal
        ≤ (klDiv ρ (target (gaussPotential α))).toReal / (1 + α * η) := by
  have hreg := HeatFlowRegularity.heatFlowRegular_gaussPotential hα ρ hmom
  have hf := measurable_gaussPotential α
  have hint := integrable_exp_neg_gaussPotential hα
  have := isMarkovKernel_forwardKernel hη
  have := isProbabilityMeasure_target hint
  have hfwd : klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target (gaussPotential α)) ≠ ⊤ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  have hback := klDiv_proxKernel_comp_le_forward hf hint hη ρ
  refine ⟨ne_top_of_le_ne_top hfwd hback, (ENNReal.toReal_mono hfwd hback).trans ?_⟩
  rw [← heatKL_eq_forwardKernel _ _ hη, ← heatKL_zero]
  exact heatKL_le_div_of_regular hα.le hη hKL hreg (fun t ht => ht.1)
    fun t ht => heatFlowLSI_gaussPotential_of_pos hα ρ hmom ht.1

end FormalizeSampling.GaussianLSI

namespace FormalizeSampling.HeatFlowRegularity

/-- **PX-2 for the Gaussian target.** Alias of
`GaussianLSI.toReal_klDiv_proxKernel_comp_le_gaussPotential`: the same statement (`KL(ρ‖π) < ∞`
and `∫ x² dρ < ∞` give `KL(proxKernel f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)` for
`f(x) = α x² / 2`). -/
alias toReal_klDiv_proxKernel_comp_le_gaussPotential_of_moment :=
  GaussianLSI.toReal_klDiv_proxKernel_comp_le_gaussPotential

end FormalizeSampling.HeatFlowRegularity

namespace FormalizeSampling.LogSobolevExtension

/-! ### Non-Gaussian targets with a functional LSI -/

open FormalizeSampling.LogSobolev FormalizeSampling.HeatFlowDeBruijn
open FormalizeSampling.ProximalContraction FormalizeSampling.GaussianLSI

open FormalizeSampling.Proximal in
/-- **PX-2 forward step for a non-Gaussian target, without the class condition (Conditional on
the target LSI and `HeatFlowRegular`).** For measurable `f` with integrable `e^{-f}`,
`π = target f`, `η, α > 0`, a probability law `ρ` with `KL(ρ‖π) < ∞`, `HeatFlowRegular ρ π s`
with `(0, η] ⊆ s` and the functional LSI `FunctionalLSI π (1/α)`:
`KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and `KL(proxKernel f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)`. -/
theorem toReal_klDiv_proxKernel_comp_le_of_targetLSI {f : ℝ → ℝ} {η α : ℝ}
    (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (hα : 0 < α) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target f) ≠ ⊤)
    {s : Set ℝ} (hreg : HeatFlowRegular ρ (target f) s) (hs : Ioc 0 η ⊆ s)
    (hπ : FunctionalLSI (target f) (1 / α)) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) := by
  have := isProbabilityMeasure_target hint
  exact toReal_klDiv_proxKernel_comp_le_of_regular hf hint hη hα.le ρ hKL hreg hs
    (heatFlowLSI_of_targetLSI ρ (target f) hα hπ hreg (Ioo_subset_Ioc_self.trans hs))

open FormalizeSampling.Proximal in
/-- PX-2 for a non-Gaussian target with regularity on all positive times: the special case
`s = (0, ∞)` of `toReal_klDiv_proxKernel_comp_le_of_targetLSI`. Conditional only on
`FunctionalLSI (target f) (1/α)`, `HeatFlowRegular ρ (target f) (Ioi 0)` and `KL(ρ‖π) < ∞`. -/
theorem toReal_klDiv_proxKernel_comp_le_of_targetLSI_Ioi {f : ℝ → ℝ} {η α : ℝ}
    (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (hα : 0 < α) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target f) ≠ ⊤)
    (hreg : HeatFlowRegular ρ (target f) (Ioi 0)) (hπ : FunctionalLSI (target f) (1 / α)) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) :=
  toReal_klDiv_proxKernel_comp_le_of_targetLSI hf hint hη hα ρ hKL hreg
    (fun _ ht => ht.1) hπ

end FormalizeSampling.LogSobolevExtension
