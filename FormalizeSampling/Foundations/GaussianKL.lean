module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.KLProduct

/-!
# KL divergence between Gaussians

Status: **Verified** (nonzero variances where a density is used).

Closed forms of Mathlib's `klDiv` (valued in `ℝ≥0∞`) between one-dimensional Gaussians and
between isotropic Gaussians on `Fin d → ℝ`. Mathlib's `gaussianReal m v` is `N(m, v)` with
**variance** `v : ℝ≥0`; the isotropic Gaussian `N(m, v I)` is the product measure
`Measure.pi fun i => gaussianReal (m i) v`. The declarations live in the namespaces
`GaussianFlowVsOU`, `GaussianIncrement` and `DiscreteGaussianFlow` of the developments that
apply them.

## Main results

* `GaussianFlowVsOU.log_gaussianPDFReal`,
  `GaussianFlowVsOU.integral_quadratic_gaussianReal`,
  `GaussianFlowVsOU.integrable_quadratic_gaussianReal`: the log-density of `N(m, v)` and the
  integral of a quadratic polynomial against it,
  `∫ (α (x - m)² + β (x - m) + γ) dN(m, v) = α v + γ`.
* `GaussianFlowVsOU.klDiv_gaussianReal_gaussianReal_of_ne_zero`: for `v₁, v₂ ≠ 0`,
  `KL(N(m₁, v₁) ‖ N(m₂, v₂)) = (v₁/v₂ + (m₁ - m₂)²/v₂ - 1 - log(v₁/v₂)) / 2`, with the special
  cases `GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian` (reference `N(0, 1)`),
  `GaussianIncrement.klDiv_gaussianReal_gaussianReal` (equal variances) and
  `DiscreteGaussianFlow.klDiv_gaussianReal_gaussianReal` (the general formula in other notation).
* `GaussianIncrement.klDiv_pi_gaussianReal`:
  `KL(N(m₁, v I) ‖ N(m₂, v I)) = ∑ᵢ (m₁ i - m₂ i)² / (2v)` (tensorisation, `Foundations/KLProduct`).
* `GaussianIncrement.pi_gaussianReal_eq_map`: `N(m, v I) = (y ↦ y + m)₊ N(0, v I)`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling.GaussianFlowVsOU

/-! ### One-dimensional Gaussians -/

/-- Log of the Gaussian density: for variance `v ≠ 0`,
`log N(m, v)(x) = -log(2πv)/2 - (x - m)² / (2v)`. -/
theorem log_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x) =
      -Real.log (2 * Real.pi * v) / 2 - (x - m) ^ 2 / (2 * v) := by
  have hv' : 0 < (v : ℝ) := by positivity
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_inv, Real.log_sqrt (by positivity)]
  ring

/-- Integral of a quadratic polynomial (centred at the mean) against `N(m, v)`:
`∫ (α (x - m)² + β (x - m) + γ) dN(m, v)(x) = α v + γ` (no assumption; for `v = 0` it is the
Dirac mass at `m`). -/
theorem integral_quadratic_gaussianReal (m : ℝ) (v : ℝ≥0) (α β γ : ℝ) :
    ∫ x, (α * (x - m) ^ 2 + β * (x - m) + γ) ∂gaussianReal m v = α * v + γ := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable (by simp)
  have hint1 : Integrable (fun x : ℝ => x - m) (gaussianReal m v) := hid.sub (integrable_const m)
  have hint2 : Integrable (fun x : ℝ => (x - m) ^ 2) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 2).sub (memLp_const m)).integrable_sq
  have hvar : ∫ x, (x - m) ^ 2 ∂gaussianReal m v = v := by
    have := variance_fun_id_gaussianReal (μ := m) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa using this
  have hmean : ∫ x, (x - m) ∂gaussianReal m v = 0 := by
    rw [integral_sub hid (integrable_const m)]
    simp
  have h12 : Integrable (fun x : ℝ => α * (x - m) ^ 2 + β * (x - m)) (gaussianReal m v) :=
    (hint2.const_mul α).add (hint1.const_mul β)
  rw [integral_add h12 (integrable_const γ),
    integral_add (hint2.const_mul α) (hint1.const_mul β), integral_const_mul,
    integral_const_mul, hvar, hmean]
  simp

/-- Quadratic polynomials `x ↦ α (x - m)² + β (x - m) + γ` are integrable against `N(m, v)`. -/
theorem integrable_quadratic_gaussianReal (m : ℝ) (v : ℝ≥0) (α β γ : ℝ) :
    Integrable (fun x => α * (x - m) ^ 2 + β * (x - m) + γ) (gaussianReal m v) := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable (by simp)
  have hint1 : Integrable (fun x : ℝ => x - m) (gaussianReal m v) := hid.sub (integrable_const m)
  have hint2 : Integrable (fun x : ℝ => (x - m) ^ 2) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 2).sub (memLp_const m)).integrable_sq
  exact ((hint2.const_mul α).add (hint1.const_mul β)).add (integrable_const γ)

/-- **KL divergence between one-dimensional Gaussians.** For variances `v₁, v₂ ≠ 0`,
`KL(N(m₁, v₁) ‖ N(m₂, v₂)) = (v₁/v₂ + (m₁ - m₂)²/v₂ - 1 - log(v₁/v₂)) / 2` (Mathlib's `klDiv`,
valued in `ℝ≥0∞`). This is the general one-dimensional formula of the library; its special
cases are `GaussianIncrement.klDiv_gaussianReal_gaussianReal` (equal variances,
`(m₁ - m₂)² / (2v)`) and `DiscreteGaussianFlow.klDiv_gaussianReal_gaussianReal` (the same
statement in other notation). The isotropic mean shift on `Fin d → ℝ` is
`GaussianIncrement.klDiv_pi_gaussianReal`. -/
theorem klDiv_gaussianReal_gaussianReal_of_ne_zero (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (h₁ : v₁ ≠ 0)
    (h₂ : v₂ ≠ 0) :
    klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂) =
      ENNReal.ofReal
        (((v₁ : ℝ) / v₂ + (m₁ - m₂) ^ 2 / v₂ - 1 - Real.log ((v₁ : ℝ) / v₂)) / 2) := by
  have hv' : 0 < (v₁ : ℝ) := by positivity
  have hσ' : 0 < (v₂ : ℝ) := by positivity
  have hac : gaussianReal m₁ v₁ ≪ gaussianReal m₂ v₂ :=
    (gaussianReal_absolutelyContinuous m₁ h₁).trans
      (gaussianReal_absolutelyContinuous' m₂ h₂)
  have hμvol : gaussianReal m₁ v₁ ≪ volume := gaussianReal_absolutelyContinuous m₁ h₁
  have hrn : (gaussianReal m₁ v₁).rnDeriv (gaussianReal m₂ v₂) =ᵐ[volume]
      fun x => (gaussianPDF m₂ v₂ x)⁻¹ * gaussianPDF m₁ v₁ x := by
    have h1 := Measure.rnDeriv_withDensity_right (gaussianReal m₁ v₁) volume
      (f := gaussianPDF m₂ v₂) (measurable_gaussianPDF m₂ v₂).aemeasurable
      (ae_of_all _ fun x => (gaussianPDF_pos m₂ h₂ x).ne')
      (ae_of_all _ fun x => gaussianPDF_ne_top)
    rw [← gaussianReal_of_var_ne_zero m₂ h₂] at h1
    filter_upwards [h1, rnDeriv_gaussianReal m₁ v₁] with x hx1 hx2
    rw [hx1, hx2]
  have hllr : llr (gaussianReal m₁ v₁) (gaussianReal m₂ v₂) =ᵐ[gaussianReal m₁ v₁]
      fun x => (1 / (2 * v₂) - 1 / (2 * v₁)) * (x - m₁) ^ 2 + (m₁ - m₂) / v₂ * (x - m₁) +
        ((m₁ - m₂) ^ 2 / (2 * v₂) + (Real.log v₂ - Real.log v₁) / 2) := by
    filter_upwards [hμvol.ae_le hrn] with x hx
    rw [llr_def]
    simp only
    rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
      ← div_eq_inv_mul, Real.log_div (gaussianPDFReal_pos _ _ _ h₁).ne'
        (gaussianPDFReal_pos _ _ _ h₂).ne',
      log_gaussianPDFReal m₁ h₁, log_gaussianPDFReal m₂ h₂,
      Real.log_mul (by positivity) hv'.ne', Real.log_mul (by positivity) hσ'.ne']
    field_simp
    ring
  have hint : Integrable (llr (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)) (gaussianReal m₁ v₁) :=
    (integrable_quadratic_gaussianReal m₁ v₁ _ _ _).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr,
    integral_quadratic_gaussianReal]
  simp
  congr 1
  rw [Real.log_div hv'.ne' hσ'.ne']
  field_simp
  ring

/-- **KL divergence to the standard Gaussian.** For mean `m` and variance `v ≠ 0`,
`KL(N(m, v) ‖ N(0, 1)) = (v + m² - 1 - log v) / 2` (Mathlib's `klDiv`, valued in `ℝ≥0∞`;
the right-hand side is nonnegative, so `ENNReal.ofReal` does not truncate). -/
theorem klDiv_gaussianReal_stdGaussian (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal m v) (gaussianReal 0 1) =
      ENNReal.ofReal ((v + m ^ 2 - 1 - Real.log v) / 2) := by
  rw [klDiv_gaussianReal_gaussianReal_of_ne_zero m 0 hv one_ne_zero]
  simp

end FormalizeSampling.GaussianFlowVsOU

namespace FormalizeSampling.GaussianIncrement

/-- **KL divergence of a Gaussian mean shift.** For a variance `v ≠ 0`,
`KL(N(m₁, v) ‖ N(m₂, v)) = (m₁ - m₂)² / (2v)` (Mathlib's `klDiv`, valued in `ℝ≥0∞`; the
right-hand side is nonnegative, so `ENNReal.ofReal` does not truncate). This generalises the
mean part of `GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian` to a reference with arbitrary mean.
It is the equal-variance case of `GaussianFlowVsOU.klDiv_gaussianReal_gaussianReal_of_ne_zero`
(different variances); the isotropic `d`-dimensional form is `klDiv_pi_gaussianReal`. -/
theorem klDiv_gaussianReal_gaussianReal (m₁ m₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v) = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * v)) := by
  rw [GaussianFlowVsOU.klDiv_gaussianReal_gaussianReal_of_ne_zero m₁ m₂ hv hv]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  congr 1
  rw [div_self hv', Real.log_one]
  field_simp
  ring

/-! ### Isotropic Gaussians on `Fin d → ℝ` -/

variable {d : ℕ}

/-- **KL divergence of an isotropic Gaussian mean shift.** For a variance `v ≠ 0` and means
`m₁ m₂ : Fin d → ℝ`, `KL(N(m₁, v I) ‖ N(m₂, v I)) = ∑ᵢ (m₁ i - m₂ i)² / (2v)`, i.e.
`|m₁ - m₂|² / (2v)` with the Euclidean norm (Mathlib's `klDiv`, in `ℝ≥0∞`). The isotropic
Gaussian is the product `Measure.pi fun i => gaussianReal (m i) v`. -/
theorem klDiv_pi_gaussianReal (m₁ m₂ : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (Measure.pi fun i => gaussianReal (m₁ i) v)
        (Measure.pi fun i => gaussianReal (m₂ i) v) =
      ENNReal.ofReal ((∑ i, (m₁ i - m₂ i) ^ 2) / (2 * v)) := by
  rw [klDiv_pi_pi, sum_div, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  exact sum_congr rfl fun i _ => klDiv_gaussianReal_gaussianReal _ _ hv

/-- A product of Gaussians with a common variance is a translate of the centred one:
`N(m, v I) = (y ↦ y + m)₊ N(0, v I)` on `Fin d → ℝ`. -/
theorem pi_gaussianReal_eq_map (m : Fin d → ℝ) (v : ℝ≥0) :
    Measure.pi (fun i => gaussianReal (m i) v) =
      (Measure.pi fun _ : Fin d => gaussianReal 0 v).map (fun y i => y i + m i) := by
  rw [Measure.pi_map_pi (fun i => (measurable_add_const (m i)).aemeasurable)]
  simp_rw [gaussianReal_map_add_const, zero_add]

end FormalizeSampling.GaussianIncrement

namespace FormalizeSampling.DiscreteGaussianFlow

/-- **KL divergence between one-dimensional Gaussians.** For variances `v, σ⋆² ≠ 0`,
`KL(N(m, v) ‖ N(μ⋆, σ⋆²)) = (v/σ⋆² + (m - μ⋆)²/σ⋆² - 1 - log(v/σ⋆²)) / 2` (Mathlib's `klDiv`,
valued in `ℝ≥0∞`). This restates the general formula
`GaussianFlowVsOU.klDiv_gaussianReal_gaussianReal_of_ne_zero` in the notation of this file. -/
theorem klDiv_gaussianReal_gaussianReal (m μStar : ℝ) {v σ2 : ℝ≥0} (hv : v ≠ 0)
    (hσ : σ2 ≠ 0) :
    klDiv (gaussianReal m v) (gaussianReal μStar σ2) =
      ENNReal.ofReal
        (((v : ℝ) / σ2 + (m - μStar) ^ 2 / σ2 - 1 - Real.log ((v : ℝ) / σ2)) / 2) :=
  GaussianFlowVsOU.klDiv_gaussianReal_gaussianReal_of_ne_zero m μStar hv hσ

end FormalizeSampling.DiscreteGaussianFlow
