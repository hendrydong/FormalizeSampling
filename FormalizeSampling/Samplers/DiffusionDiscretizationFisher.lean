module

public import FormalizeSampling.Foundations.HeatFlowRegularityPi
public import FormalizeSampling.Foundations.GaussianFunctionalLSIPi

/-!
# Fisher information of the isotropic heat flow: `J(ρ * N(0, t I)) ≤ d / t`

Status: **Verified**.

For a probability measure `ρ` on `Fin d → ℝ` and `t > 0`, `p_t = heatFlowDensityPi ρ t` is the
Lebesgue density of `ρ * N(0, t I)`. Its (absolute) Fisher information is
`heatFisherInfo ρ t = ∫ |∇p_t|² / p_t`. This file proves the dimension bound
`heatFisherInfo ρ t ≤ d / t` with **no assumption on `ρ`** (no density, no moment), and the
Gaussian moment identities used by the entropy computations of the diffusion discretisation
bound (`Samplers/DiffusionDiscretizationEntropy.lean`).

## Main results

* `integral_heatDensityPi_mul_quad`: `∫ φ_t(z) (a zᵢ² + b zᵢ + c) dz = a t + c`.
* `integral_heatDensityPi_mul_sumSq`: `∫ φ_t(z) |z|² dz = d t`.
* `integrable_heatFisherInfo_integrand`, `heatFisherInfo_le` (Verified, any probability `ρ`):
  `y ↦ |∇p_t(y)|²/p_t(y)` is Lebesgue integrable and `heatFisherInfo ρ t ≤ d / t`.
* `heatFisherInfo_nonneg`.

Proof of the bound: pointwise Cauchy–Schwarz
(`HeatFlowRegularityPi.sq_heatFlowGradPi_div_le`) gives
`|∇p_t(y)|²/p_t(y) ≤ ∫ |y - x|²/t² φ_t(y - x) dρ(x)`; integrate in `y` (Fubini) and use
`∫ |z|² φ_t(z) dz = d t`.

## Not proved here

* Monotonicity of `t ↦ heatFisherInfo ρ t` and de Bruijn's identity for the entropy (see
  `Samplers/DiffusionDiscretizationEntropy.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi FormalizeSampling.GaussianLSIPi
  FormalizeSampling.GaussianFunctionalLSIPi

variable {d : ℕ}

/-! ### Gaussian moments -/

/-- **Coordinate quadratic moments of `N(0, t I)`.** For `t > 0`, `a b c : ℝ` and a coordinate
`i`: `∫ φ_t(z) (a zᵢ² + b zᵢ + c) dz = a t + c` (`φ_t = heatDensityPi t`). -/
theorem integral_heatDensityPi_mul_quad {t : ℝ} (ht : 0 < t) (a b c : ℝ) (i : Fin d) :
    ∫ z : Fin d → ℝ, heatDensityPi t z * (a * z i ^ 2 + b * z i + c) = a * t + c := by
  rw [← integral_pi_gaussianReal_eq ht]
  have hmap : (Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal).map (fun z => z i) =
      gaussianReal 0 t.toNNReal :=
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 t.toNNReal) i).map_eq
  have h := FormalizeSampling.GaussianFlowVsOU.integral_quadratic_gaussianReal 0 t.toNNReal a b c
  simp only [sub_zero, Real.coe_toNNReal _ ht.le] at h
  have hm := integral_map (μ := Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal)
    (measurable_pi_apply i).aemeasurable
    (f := fun x : ℝ => a * x ^ 2 + b * x + c) (by fun_prop)
  rw [hmap] at hm
  rw [← h, hm]

/-- **Second moment of `N(0, t I)`.** For `t > 0`: `∫ φ_t(z) |z|² dz = d t`. -/
theorem integral_heatDensityPi_mul_sumSq {t : ℝ} (ht : 0 < t) :
    ∫ z : Fin d → ℝ, heatDensityPi t z * ∑ i, z i ^ 2 = d * t := by
  have hi : ∀ i : Fin d, Integrable fun z : Fin d → ℝ => heatDensityPi t z * z i ^ 2 := by
    intro i
    have hc := continuous_heatDensityPi (d := d) t
    refine (integrable_sumSq_mul_heatDensityPi (d := d) ht).mono'
      (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatDensityPi_pos ht z).le (sq_nonneg _)),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sum_sq z i) (heatDensityPi_pos ht z).le
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hi i]
  have h : ∀ i : Fin d, ∫ z : Fin d → ℝ, heatDensityPi t z * z i ^ 2 = t := by
    intro i
    have := integral_heatDensityPi_mul_quad (d := d) ht 1 0 0 i
    simpa using this
  simp [h]

/-! ### Fisher information of the heat flow -/

/-- The (absolute) Fisher information of the heat flow `p_t = ρ * N(0, t I)`:
`heatFisherInfo ρ t = ∫ ∑ᵢ (∂ᵢp_t(y))² / p_t(y) dy`, with the explicit Gaussian-convolution
derivatives `heatFlowGradPi`. -/
noncomputable def heatFisherInfo (ρ : Measure (Fin d → ℝ)) (t : ℝ) : ℝ :=
  ∫ y, (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y

section Fisher

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- The Fisher integrand is nonnegative. -/
theorem heatFisherInfo_integrand_nonneg {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    0 ≤ (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (heatFlowDensityPi_pos ρ ht y).le

/-- The Fisher information is nonnegative. -/
theorem heatFisherInfo_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ heatFisherInfo ρ t :=
  integral_nonneg fun y => heatFisherInfo_integrand_nonneg ρ ht y

/-- The Fisher integrand is continuous for `t > 0`. -/
theorem continuous_heatFisherInfo_integrand {t : ℝ} (ht : 0 < t) :
    Continuous fun y => (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y := by
  have hg := continuous_heatFlowGradPi ρ ht
  exact (continuous_finsetSum _ fun i _ => (hg i).pow 2).div
    (continuous_heatFlowDensityPi ρ ht) fun y => (heatFlowDensityPi_pos ρ ht y).ne'

/-- The Cauchy–Schwarz kernel `k_t(z) = |z|²/t² · φ_t(z)`. -/
private noncomputable def csKer (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  (∑ i, z i ^ 2) / t ^ 2 * heatDensityPi t z

private theorem continuous_csKer (t : ℝ) : Continuous (csKer (d := d) t) := by
  have := continuous_heatDensityPi (d := d) t
  unfold csKer; fun_prop

private theorem csKer_nonneg {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) : 0 ≤ csKer t z :=
  mul_nonneg (div_nonneg (sum_sq_nonneg z) (sq_nonneg _)) (heatDensityPi_pos ht z).le

private theorem integrable_csKer {t : ℝ} (ht : 0 < t) : Integrable (csKer (d := d) t) := by
  have h := (integrable_sumSq_mul_heatDensityPi (d := d) ht).div_const (t ^ 2)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [csKer]; ring

private theorem integral_csKer {t : ℝ} (ht : 0 < t) :
    ∫ z, csKer (d := d) t z = d / t := by
  have h := integral_heatDensityPi_mul_sumSq (d := d) ht
  have e : (fun z : Fin d → ℝ => csKer t z) =
      fun z => (heatDensityPi t z * ∑ i, z i ^ 2) / t ^ 2 := by
    funext z; simp only [csKer]; ring
  rw [e, integral_div, h]
  field_simp

private theorem csKer_bound {t : ℝ} (ht : 0 < t) :
    ∃ B, ∀ z : Fin d → ℝ, |csKer t z| ≤ B := by
  refine ⟨2 * t / t ^ 2 * gc d t, fun z => ?_⟩
  have hS := sum_sq_nonneg z
  have hE := mul_exp_neg_le ht hS
  have hg := gc_pos (d := d) ht
  rw [abs_of_nonneg (csKer_nonneg ht z), csKer, heatDensityPi_eq]
  calc (∑ i, z i ^ 2) / t ^ 2 * (gc d t * Real.exp (-(∑ i, z i ^ 2) / (2 * t)))
      = ((∑ i, z i ^ 2) * Real.exp (-(∑ i, z i ^ 2) / (2 * t))) / t ^ 2 * gc d t := by ring
    _ ≤ 2 * t / t ^ 2 * gc d t := by gcongr

/-- Pointwise Cauchy–Schwarz bound of the Fisher integrand:
`|∇p_t(y)|²/p_t(y) ≤ ∫ |y - x|²/t² φ_t(y - x) dρ(x)`. -/
private theorem fisher_integrand_le {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y ≤
      ∫ x, csKer t (y - x) ∂ρ := by
  have hφc := continuous_heatDensityPi (d := d) t
  have hi : ∀ i : Fin d,
      Integrable (fun x => ((y - x) i / t) ^ 2 * heatDensityPi t (y - x)) ρ := by
    intro i
    obtain ⟨B, hB⟩ := csKer_bound (d := d) ht
    refine integrable_comp_sub_of_bound ρ (k := fun z => (z i / t) ^ 2 * heatDensityPi t z)
      (by fun_prop) (B := B) (fun z => ?_) y
    refine le_trans ?_ (hB z)
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (heatDensityPi_pos ht z).le),
      abs_of_nonneg (csKer_nonneg ht z), csKer, div_pow]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (sq_le_sum_sq z i) (sq_nonneg _)) (heatDensityPi_pos ht z).le
  rw [Finset.sum_div]
  calc ∑ i, heatFlowGradPi ρ t y i ^ 2 / heatFlowDensityPi ρ t y
      ≤ ∑ i, ∫ x, ((y - x) i / t) ^ 2 * heatDensityPi t (y - x) ∂ρ :=
        Finset.sum_le_sum fun i _ => sq_heatFlowGradPi_div_le ht y i
    _ = ∫ x, ∑ i, ((y - x) i / t) ^ 2 * heatDensityPi t (y - x) ∂ρ :=
        (integral_finsetSum _ fun i _ => hi i).symm
    _ = ∫ x, csKer t (y - x) ∂ρ := by
        congr 1; funext x
        rw [csKer, ← Finset.sum_mul, Finset.sum_div]
        simp only [div_pow]

/-- The function `(y, x) ↦ k_t(y - x)` is integrable for `Lebesgue × ρ`. -/
private theorem integrable_csKer_prod {t : ℝ} (ht : 0 < t) :
    Integrable (Function.uncurry fun (y x : Fin d → ℝ) => csKer t (y - x))
      ((volume : Measure (Fin d → ℝ)).prod ρ) := by
  have hc := continuous_csKer (d := d) t
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (y x : Fin d → ℝ) => csKer t (y - x))
      ((volume : Measure (Fin d → ℝ)).prod ρ) :=
    (hc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · exact (integrable_csKer (d := d) ht).comp_sub_right x
  · simp only [Function.uncurry_apply_pair]
    have e : ∀ x : Fin d → ℝ, ∫ y, ‖csKer t (y - x)‖ = ∫ z, ‖csKer (d := d) t z‖ := fun x =>
      integral_sub_right_eq_self (fun z => ‖csKer (d := d) t z‖) x
    simp_rw [e]
    exact integrable_const _

/-- **Integrability of the Fisher integrand of the heat flow** (any probability `ρ`, `t > 0`). -/
theorem integrable_heatFisherInfo_integrand {t : ℝ} (ht : 0 < t) :
    Integrable fun y => (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y := by
  have hg : Integrable (fun y => ∫ x, csKer t (y - x) ∂ρ) :=
    (integrable_csKer_prod ρ ht).integral_prod_left
  refine hg.mono' (continuous_heatFisherInfo_integrand ρ ht).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (heatFisherInfo_integrand_nonneg ρ ht y)]
  exact fisher_integrand_le ρ ht y

/-- **Dimension bound for the Fisher information of the heat flow.** For every probability
measure `ρ` on `Fin d → ℝ` (no density or moment assumption) and `t > 0`:
`J(ρ * N(0, t I)) = ∫ |∇p_t|²/p_t ≤ d / t`, the Fisher information of `N(0, t I)` itself. -/
theorem heatFisherInfo_le {t : ℝ} (ht : 0 < t) : heatFisherInfo ρ t ≤ d / t := by
  have hprod := integrable_csKer_prod ρ ht
  have hg : Integrable (fun y => ∫ x, csKer t (y - x) ∂ρ) := hprod.integral_prod_left
  calc heatFisherInfo ρ t ≤ ∫ y, ∫ x, csKer t (y - x) ∂ρ :=
        integral_mono (integrable_heatFisherInfo_integrand ρ ht) hg
          fun y => fisher_integrand_le ρ ht y
    _ = ∫ x, (∫ y, csKer t (y - x)) ∂ρ :=
        integral_integral_swap (f := fun (y x : Fin d → ℝ) => csKer t (y - x)) hprod
    _ = ∫ _x, (d / t : ℝ) ∂ρ := by
        congr 1; funext x
        rw [integral_sub_right_eq_self (fun z => csKer (d := d) t z) x, integral_csKer ht]
    _ = d / t := by simp

end Fisher

end FormalizeSampling.DiffusionDiscretization
