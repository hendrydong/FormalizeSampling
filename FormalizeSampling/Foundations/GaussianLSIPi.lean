module

public import FormalizeSampling.Foundations.GaussianLSIBasicsPi
public import FormalizeSampling.Foundations.HeatFlowRegularityPerturbedPi

/-!
# The Gaussian log-Sobolev inequality along the isotropic heat flow on `Fin d → ℝ`

Status: **Verified** for every probability law `ρ` with a finite second moment
`∫ ∑ᵢ xᵢ² dρ < ∞` (and, for the contraction, `KL(ρ‖π) < ∞`); no named functional-inequality or
regularity hypothesis is used. The de Bruijn regularity `HeatFlowRegularPi ρ π (Ioi 0)` is derived
from the second moment by `Foundations/HeatFlowRegularityPerturbedPi.lean`; the helper lemmas are in
`Foundations/GaussianLSIBasicsPi.lean`. This is the `Fin d → ℝ` version of
`Foundations/GaussianLSI.lean`.

Notation (as in `HeatFlowDeBruijnPi`): `φ_a = heatDensityPi a` is the `N(0, a I)` density,
`p_t = heatFlowDensityPi ρ t = ρ * φ_t`, `π = N(0, v I) = ⊗ᵢ N(0, v)` (`v > 0`),
`π_t = heatKernelPi t ∘ₘ π = N(0, (v + t) I)`, `K(t) = heatKL ρ π t = KL(ρ_t‖π_t)` and
`I(t) = heatFisher ρ π t = I(ρ_t‖π_t)`. The relative score flux is
`G_t = gaussRelFluxPi ρ v t = ∇p_t + y p_t / (v + t) = p_t ∇ log(p_t / q_t)`.

## Main results

* `heatKL_le_heatFisher_gaussian`, `toReal_klDiv_heatKernelPi_comp_le` (**Gaussian LSI along the
  heat flow**): for `t > 0`, `KL(ρ_t‖N(0, (v + t) I)) ≤ ((v + t)/2) I(ρ_t‖N(0, (v + t) I))`.
* `heatFlowLSI_gaussian_of_pos`, `toReal_klDiv_heatKernelPi_le_gaussian`: for
  `π = N(0, α⁻¹ I)`, `2 α K(t) ≤ (1 + α t) I(t)` for `t > 0`, hence the forward heat-flow step
  contracts, `KL(ρ_η‖π_η) ≤ KL(ρ‖π) / (1 + α η)`, with no LSI hypothesis.
* `HeatFlowRegularityPi.heatKL_le_heatFisher_gaussian_of_moment`: an alias of
  `heatKL_le_heatFisher_gaussian` (the same statement).

## Not proved here

* The LSI at time `0` for non-smoothed `ρ` with a differentiable density is in
  `GaussianLSIZeroPi`.
* The backward (denoising) step of the proximal sampler is in `ProximalSharpLSIPi`; the sharp
  rate for Gaussian targets is `ProximalGaussianUnconditional`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.GaussianLSIPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi

variable {d : ℕ}

/-! ### The Gaussian log-Sobolev inequality along the heat flow -/

/-- **Gaussian log-Sobolev inequality along the isotropic heat flow.** Let `ρ` be a probability
measure on `Fin d → ℝ` with finite second moment (`∫ ∑ᵢ xᵢ² dρ < ∞`) and `π = N(0, v I)`
(`v > 0`). Then for every `t > 0`, `ρ_t = ρ * N(0, t I)` satisfies the LSI of
`π_t = N(0, (v + t) I)`: `KL(ρ_t‖π_t) ≤ ((v + t) / 2) · I(ρ_t‖π_t)` (`heatKL`, `heatFisher`).
`heatKL` is `KL(ρ_t‖π_t).toReal`; the divergence is finite, see
`HeatFlowRegularityPi.klDiv_heatKernelPi_comp_ne_top_of_moment`.

Proof: the de Bruijn hypotheses `HeatFlowRegularPi ρ π (Ioi 0)` hold by
`HeatFlowRegularityPi.heatFlowRegularPi_gaussian`. By `heatFisher_gaussian_le`,
`I(s) ≤ ((v + t)/(v + s))² I(t)` for `s ≥ t`; with de Bruijn `K' = -½ I`,
`s ↦ K(s) - ½ I(t) (v + t)² / (v + s)` is nondecreasing on `[t, ∞)`, so
`K(t) ≤ ½ (v + t) I(t) + K(T)`, and `K(T) ≤ E|x - u|² / (2T) → 0` (`heatKL_le_div_two_mul`);
this last step is `Gronwall.le_of_fisher_decay`. -/
theorem heatKL_le_heatFisher_gaussian (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    {v : ℝ} (hv : 0 < v) (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    heatKL ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t
      ≤ (v + t) / 2 * heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t := by
  have hreg := HeatFlowRegularityPi.heatFlowRegularPi_gaussian ρ hmom hv
  refine Gronwall.le_of_fisher_decay hv ht (fun s hs => hasDerivAt_heatKL hreg hs)
    (fun s hs => ?_) (heatFisher_nonneg ρ _ ht) fun T hT =>
      heatKL_le_div_two_mul ρ _
        (integrable_sum_sub_sq_prod hmom (integrable_sum_sq_pi_gaussianReal v)) (ht.trans hT)
  have h := heatFisher_gaussian_le ρ hv ht (sub_pos.2 hs) (hreg.integrable_fisher t ht)
  rwa [add_sub_cancel, show v + t + (s - t) = v + s by ring] at h

/-- **Gaussian LSI for Gaussian-smoothed laws on `Fin d → ℝ`, explicit form.** For a probability
`ρ` on `Fin d → ℝ` with `∫ ∑ᵢ xᵢ² dρ < ∞` and `v, t > 0`, the law `ρ_t = heatKernelPi t ∘ₘ ρ`
with density `p_t` satisfies
`KL(ρ_t‖N(0, (v + t) I)) ≤ ((v + t) / 2) ∫ |∇p_t + y p_t / (v + t)|² / p_t dy`.
The left side is `KL(ρ_t‖N(0, (v + t) I)).toReal`; the divergence is finite, see
`klDiv_heatKernelPi_comp_gaussian_ne_top` with `HeatFlowRegularityPi.heatFlowRegularPi_gaussian`.
-/
theorem toReal_klDiv_heatKernelPi_comp_le (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    {v : ℝ} (hv : 0 < v) (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    (klDiv (heatKernelPi t.toNNReal ∘ₘ ρ)
        (Measure.pi fun _ : Fin d => gaussianReal 0 (v + t).toNNReal)).toReal
      ≤ (v + t) / 2 *
        ∫ y, (∑ i, gaussRelFluxPi ρ v t y i ^ 2) / heatFlowDensityPi ρ t y := by
  have h := heatKL_le_heatFisher_gaussian ρ hv hmom ht
  rw [heatKL, heatKernelPi_comp_pi_gaussianReal hv.le ht.le, heatFisher] at h
  simp_rw [fisherIntegrand_gaussian ρ hv ht] at h
  exact h

/-- **LSI along the heat flow in contraction form.** For `α > 0`, `π = N(0, α⁻¹ I)` and a
probability `ρ` on `Fin d → ℝ` with finite second moment: for every `t > 0`,
`2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)`, the hypothesis `hL` of
`HeatFlowDeBruijnPi.heatKL_le_div_of_regular`. -/
theorem heatFlowLSI_gaussian_of_pos {α : ℝ} (hα : 0 < α) (ρ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    2 * α * heatKL ρ (Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal) t
      ≤ (1 + α * t) *
        heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal) t := by
  have h := heatKL_le_heatFisher_gaussian ρ (inv_pos.2 hα) hmom ht
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * α)
  have e : 2 * α * ((α⁻¹ + t) / 2 *
      heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal) t)
      = (1 + α * t) *
        heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal) t := by
    field_simp
  linarith

/-- **Heat-flow KL contraction for an isotropic Gaussian target, with no named functional
inequality.** For `α, η > 0`, `π = N(0, α⁻¹ I)` on `Fin d → ℝ`, and a probability law `ρ` with
`KL(ρ‖π) < ∞` and finite second moment:
`KL(heatKernelPi η ∘ₘ ρ ‖ heatKernelPi η ∘ₘ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`
(the forward step of the proximal sampler; the LSI input is `heatFlowLSI_gaussian_of_pos`). -/
theorem toReal_klDiv_heatKernelPi_le_gaussian {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal) ≠ ⊤)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    (klDiv (heatKernelPi η.toNNReal ∘ₘ ρ)
        (heatKernelPi η.toNNReal ∘ₘ Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal)).toReal
      ≤ (klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 α⁻¹.toNNReal)).toReal /
        (1 + α * η) :=
  toReal_klDiv_heatKernelPi_le_of_regular hα.le hη hKL
    (HeatFlowRegularityPi.heatFlowRegularPi_gaussian ρ hmom (inv_pos.2 hα)) (fun _ ht => ht.1)
    fun _ ht => heatFlowLSI_gaussian_of_pos hα ρ hmom ht.1

end FormalizeSampling.GaussianLSIPi

namespace FormalizeSampling.HeatFlowRegularityPi

/-- **Gaussian LSI along the isotropic heat flow.** Alias of
`GaussianLSIPi.heatKL_le_heatFisher_gaussian`: the same statement (a probability `ρ` on
`Fin d → ℝ` with `∫ ∑ᵢ xᵢ² dρ < ∞`, `v, t > 0`: `KL(ρ_t‖π_t) ≤ ((v + t) / 2) · I(ρ_t‖π_t)` for
`π = N(0, v I)`). -/
alias heatKL_le_heatFisher_gaussian_of_moment := GaussianLSIPi.heatKL_le_heatFisher_gaussian

end FormalizeSampling.HeatFlowRegularityPi
