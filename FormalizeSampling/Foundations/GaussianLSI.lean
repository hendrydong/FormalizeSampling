module

public import FormalizeSampling.Foundations.GaussianLSIBasics
public import FormalizeSampling.Foundations.HeatFlowRegularityPerturbed
public import FormalizeSampling.Foundations.HeatKernel

/-!
# The Gaussian log-Sobolev inequality along the heat flow

Status: **Verified** for every probability law `ρ` with a finite second moment; no named
functional-inequality or regularity hypothesis is used. The de Bruijn regularity
`HeatFlowRegular ρ π (Ioi 0)` is derived from the second moment by
`Foundations/HeatFlowRegularityPerturbed.lean`; the helper lemmas are in
`Foundations/GaussianLSIBasics.lean`.

Notation (as in `HeatFlowDeBruijn`): `φ_a = heatDensity a` is the `N(0, a)` density,
`p_t = heatFlowDensity ρ t = ρ * φ_t`, `π = N(0, v)` (`v > 0`), `π_t = π * N(0, t) = N(0, v + t)`,
`K(t) = heatKL ρ π t = KL(ρ_t‖π_t)` and `I(t) = heatFisher ρ π t = I(ρ_t‖π_t)`. The relative
score flux is `G_t = gaussRelFlux ρ v t = p_t' + y p_t / (v + t) = p_t ∂_y log(p_t / q_t)`.

## Main results

* `heatKL_le_heatFisher_gaussianReal`, `toReal_klDiv_heatKernel_comp_le` (**Gaussian LSI**):
  for `t > 0`, `KL(ρ_t‖N(0, v + t)) ≤ ((v + t)/2) I(ρ_t‖N(0, v + t))`.
* `heatFlowLSI_gaussPotential_of_pos`: the inequality of `HeatFlowLSI` for
  `π = target (gaussPotential α)` at every `t > 0`.
* `heatFisher_zero`: `heatFisher ρ π 0 = 0`.
* `HeatFlowRegularity.heatKL_le_heatFisher_gaussianReal_of_moment`: alias of
  `heatKL_le_heatFisher_gaussianReal` (the same statement).
* The PX-2 consequences for the Gaussian target (`toReal_klDiv_nonpos_of_heatFlowLSI`,
  `toReal_klDiv_proxKernel_comp_le_gaussPotential`) are in `Samplers/ProximalHeatFlow.lean`.

## Not proved here

* The LSI at time `0` for non-smoothed `ρ` with a differentiable density is in `GaussianLSIZero`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction
open scoped FormalizeSampling.OU

namespace FormalizeSampling.GaussianLSI

/-! ### The Gaussian log-Sobolev inequality along the heat flow -/

/-- **Gaussian log-Sobolev inequality along the heat flow.** Let `ρ` be a probability measure
on `ℝ` with finite second moment `∫ x² dρ < ∞` and `π = N(0, v)` (`v > 0`). Then for every
`t > 0`, `ρ_t = ρ * N(0, t)` satisfies the LSI of `π_t = N(0, v + t)`:
`KL(ρ_t‖π_t) ≤ ((v + t) / 2) · I(ρ_t‖π_t)` (`heatKL`, `heatFisher`).
`heatKL` is `KL(ρ_t‖π_t).toReal`; the divergence is finite, see
`HeatFlowRegularity.klDiv_heatKernel_comp_ne_top_of_moment`.

Proof: the de Bruijn hypotheses `HeatFlowRegular ρ π (Ioi 0)` hold by
`HeatFlowRegularity.heatFlowRegular_gaussianReal`. By `heatFisher_gaussianReal_le`,
`I(s) ≤ ((v + t)/(v + s))² I(t)` for `s ≥ t`; with de Bruijn `K' = -½ I`, the function
`s ↦ K(s) - ½ I(t) (v + t)² / (v + s)` is nondecreasing on `[t, ∞)`, so
`K(t) ≤ ½ (v + t) I(t) + K(T)`, and `K(T) ≤ C / (2T) → 0` (`heatKL_le_div_two_mul`); this
last step is `Gronwall.le_of_fisher_decay`. -/
theorem heatKL_le_heatFisher_gaussianReal (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {v : ℝ}
    (hv : 0 < v) (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    heatKL ρ (gaussianReal 0 v.toNNReal) t
      ≤ (v + t) / 2 * heatFisher ρ (gaussianReal 0 v.toNNReal) t := by
  have hreg := HeatFlowRegularity.heatFlowRegular_gaussianReal ρ hmom hv
  refine Gronwall.le_of_fisher_decay hv ht (fun s hs => hasDerivAt_heatKL hreg hs)
    (fun s hs => ?_) (heatFisher_nonneg ρ _ ht) fun T hT =>
      heatKL_le_div_two_mul ρ _ (integrable_sub_sq_prod hmom (integrable_sq_gaussianReal v))
        (ht.trans hT)
  have h := heatFisher_gaussianReal_le ρ hv ht (sub_pos.2 hs) (hreg.integrable_fisher t ht)
  rwa [add_sub_cancel, show v + t + (s - t) = v + s by ring] at h

/-- **LSI along the heat flow for the Gaussian potential (positive times).** For `α > 0`,
`π = target (gaussPotential α) = N(0, 1/α)` and a probability `ρ` with finite second moment
`∫ x² dρ < ∞`: for every `t > 0`,
`2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)`, which is the inequality of
`ProximalContraction.HeatFlowLSI ρ π α η (heatFisher ρ π)` at every `t ∈ (0, η)`. -/
theorem heatFlowLSI_gaussPotential_of_pos {α : ℝ} (hα : 0 < α) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    2 * α * heatKL ρ (Proximal.target (ProximalSharp.gaussPotential α)) t
      ≤ (1 + α * t) * heatFisher ρ (Proximal.target (ProximalSharp.gaussPotential α)) t := by
  rw [ProximalSharp.target_gaussPotential hα]
  have h := heatKL_le_heatFisher_gaussianReal ρ (inv_pos.2 hα) hmom ht
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * α)
  have e : 2 * α * ((α⁻¹ + t) / 2 * heatFisher ρ (gaussianReal 0 α⁻¹.toNNReal) t)
      = (1 + α * t) * heatFisher ρ (gaussianReal 0 α⁻¹.toNNReal) t := by
    field_simp
  linarith

/-- **Gaussian LSI for Gaussian-smoothed laws, explicit form.** For a probability `ρ` on `ℝ`
with `∫ x² dρ < ∞` and `v, t > 0`, the law `ρ_t = ρ * N(0, t)` with density `p_t` satisfies
`KL(ρ_t‖N(0, v + t)) ≤ ((v + t) / 2) ∫ p_t (p_t'/p_t + y/(v + t))² dy`.
The left side is `KL(ρ_t‖N(0, v + t)).toReal`; the divergence is finite, see
`klDiv_heatKernel_comp_gaussianReal_ne_top` with `HeatFlowRegularity.heatFlowRegular_gaussianReal`.
-/
theorem toReal_klDiv_heatKernel_comp_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {v : ℝ}
    (hv : 0 < v) (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    (klDiv (FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ ρ)
        (gaussianReal 0 (v + t).toNNReal)).toReal
      ≤ (v + t) / 2 * ∫ y, gaussRelFlux ρ v t y ^ 2 / heatFlowDensity ρ t y := by
  have h := heatKL_le_heatFisher_gaussianReal ρ hv hmom ht
  have hb : FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ gaussianReal 0 v.toNNReal =
      gaussianReal 0 (v + t).toNNReal := by
    rw [Real.toNNReal_add hv.le ht.le, ← FormalizeSampling.OU.bind_heat]
    rfl
  rw [heatKL, hb, heatFisher] at h
  simp_rw [fisherIntegrand_gaussianReal ρ hv ht] at h
  exact h

/-! ### The relative Fisher information at `t = 0` -/

/-- `heatDensity 0 = 0`, hence `heatFisher ρ π 0 = 0` for all `ρ, π`. -/
theorem heatFisher_zero (ρ π : Measure ℝ) : heatFisher ρ π 0 = 0 := by
  have h0 : ∀ y, heatFlowDensity ρ 0 y = 0 := fun y => by simp [heatFlowDensity, heatDensity]
  simp [heatFisher, fisherIntegrand, h0]

end FormalizeSampling.GaussianLSI

namespace FormalizeSampling.HeatFlowRegularity

/-- **Gaussian log-Sobolev inequality along the heat flow.** Alias of
`GaussianLSI.heatKL_le_heatFisher_gaussianReal`: the same statement (a probability `ρ` on `ℝ`
with `∫ x² dρ < ∞`, `v, t > 0`: `KL(ρ_t‖π_t) ≤ ((v + t) / 2) · I(ρ_t‖π_t)` for `π = N(0, v)`). -/
alias heatKL_le_heatFisher_gaussianReal_of_moment := GaussianLSI.heatKL_le_heatFisher_gaussianReal

end FormalizeSampling.HeatFlowRegularity
