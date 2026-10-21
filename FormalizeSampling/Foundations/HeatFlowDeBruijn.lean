module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Order.CompletePartialOrder
public import FormalizeSampling.Foundations.Gronwall
public import FormalizeSampling.Foundations.HeatKernel
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# de Bruijn's identity along the heat flow (1D)

Status: **Verified** for the heat equation of Gaussian convolutions, the de Bruijn identity
for relative entropy and the derived KL contraction along the flow, under the explicit
regularity hypotheses `HeatFlowRegular`; the contraction is then **Conditional** only on the
log-Sobolev inequality of `π_t` along the flow at positive times (see `GaussianLSI` for Gaussian
`π`). Its application to the forward step of the proximal sampler is in
`Samplers/ProximalHeatFlow.lean`.

Notation: `φ_t = heatDensity t` is the `N(0, t)` density (`t` = variance). For a measure `ρ` on
`ℝ`, `p_t = heatFlowDensity ρ t = ρ * φ_t`; for a probability `ρ` and `t > 0` this is the
Lebesgue density of `ρ_t = heatKernel t ∘ₘ ρ` (`heatKernel_comp_eq_withDensity`). All
divergences are `KL(ρ_t‖π_t)` with the evolving law first and the evolving target second.

## Main results

* `hasDerivAt_heatDensity_t`, `hasDerivAt_heatFlowDensity_t` (Verified): the heat equation
  `∂_t p_t = ½ ∂_x² p_t`, for the kernel and for `ρ * φ_t` with `ρ` any finite measure.
* `integral_klRate_eq` (Verified): the integration-by-parts step
  `∫ ∂_t[p log(p/q)] = -½ ∫ p (∂_x log(p/q))²`, given vanishing boundary flux.
* `hasDerivAt_integral_klIntegrand` (Verified): abstract de Bruijn identity for two families
  of positive densities solving the heat equation, under domination / integrability /
  boundary hypotheses.
* `hasDerivAt_heatKL` (Verified under `HeatFlowRegular`): `d/dt KL(ρ_t‖π_t) = -½ I(ρ_t‖π_t)`
  for `t > 0`, with `I = heatFisher`.
* `heatKL_le_div_of_regular`: `KL(ρ_η‖π_η) ≤ KL(ρ‖π) / (1 + α η)` under `HeatFlowRegular` and
  the LSI along the flow for `t ∈ (0, η)` only. No regularity at `t = 0` is needed. The LSI is
  not required at `t = 0`: there `heatFisher ρ π 0 = 0`, so requiring it would force
  `KL(ρ‖π) = 0`. The PX-2 forms `toReal_klDiv_forwardKernel_le_of_regular` and
  `toReal_klDiv_proxKernel_comp_le_of_regular` are in `Samplers/ProximalHeatFlow.lean`.
* `heatFlowRegular_self`: `HeatFlowRegular ρ ρ (Ioi 0)` (non-vacuity).

## Not proved here

* The hypotheses packed in `HeatFlowRegular` (integrability of `p_t log(p_t/q_t)` and of the
  Fisher integrand, local-in-time domination of the KL time-derivative, vanishing boundary
  flux) are not derived here; `HeatFlowRegularityPerturbed` derives them from a finite second
  moment of `ρ` for Gaussian `π`, and `HeatFlowRegularityWarm` for warm `ρ` and `π` with a
  finite second moment.
* A `HeatFlowDissipation ρ π η I` instance for general `ρ, π`: it requires a right derivative
  of `KL(ρ_t‖π_t)` at `t = 0`, which is not established; the contraction theorems here avoid
  it instead.
* The LSI of `π * N(0, t)` for non-Gaussian `π` (the Gaussian case is in `GaussianLSI`; the
  convolution route from an LSI of `π` is in `LogSobolevExtension`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace FormalizeSampling.HeatFlowDeBruijn

/-! ### The Gaussian heat kernel and its heat equation -/

/-- The centred Gaussian density with variance `t` (the heat kernel at time `t`):
`heatDensity t z = (2π t)^{-1/2} exp(-z² / (2t))`. Only meaningful for `t > 0`; for `t > 0` it
equals `gaussianPDFReal 0 t.toNNReal z`. -/
noncomputable def heatDensity (t z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-z ^ 2 / (2 * t))

/-- For `t > 0` the Mathlib Gaussian density is the shifted heat kernel:
`N(y; z, t) = gaussianPDFReal z t y = heatDensity t (y - z)`. -/
theorem gaussianPDFReal_eq_heatDensity {t : ℝ} (ht : 0 < t) (z y : ℝ) :
    gaussianPDFReal z t.toNNReal y = heatDensity t (y - z) := by
  rw [gaussianPDFReal, heatDensity, Real.coe_toNNReal _ ht.le]

/-- The space derivative of the heat kernel: `∂_z heatDensity t z = -(z / t) heatDensity t z`
(`hasDerivAt_heatDensity_x`). -/
noncomputable def heatDensityD1 (t z : ℝ) : ℝ := -(z / t) * heatDensity t z

/-- The second space derivative of the heat kernel:
`∂_z² heatDensity t z = (z² / t² - 1 / t) heatDensity t z` (`hasDerivAt_heatDensityD1_x`). -/
noncomputable def heatDensityD2 (t z : ℝ) : ℝ := (z ^ 2 / t ^ 2 - 1 / t) * heatDensity t z

/-- First space derivative of the heat kernel: for all `t, z`,
`∂_z heatDensity t z = heatDensityD1 t z` (no assumptions; for `t = 0` both sides are `0`). -/
theorem hasDerivAt_heatDensity_x (t z : ℝ) :
    HasDerivAt (heatDensity t) (heatDensityD1 t z) z := by
  have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / (2 * t)) (-(2 * z) / (2 * t)) z := by
    simpa using ((hasDerivAt_pow 2 z).neg).div_const (2 * t)
  have := (h1.exp).const_mul (Real.sqrt (2 * Real.pi * t))⁻¹
  refine this.congr_deriv ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp [heatDensityD1, heatDensity]
  unfold heatDensityD1 heatDensity
  field_simp

/-- Second space derivative of the heat kernel: for `t ≠ 0` and all `z`,
`∂_z heatDensityD1 t z = heatDensityD2 t z`. -/
theorem hasDerivAt_heatDensityD1_x {t : ℝ} (ht : t ≠ 0) (z : ℝ) :
    HasDerivAt (heatDensityD1 t) (heatDensityD2 t z) z := by
  have := ((hasDerivAt_id z).div_const t).neg.mul (hasDerivAt_heatDensity_x t z)
  refine this.congr_deriv ?_
  unfold heatDensityD2 heatDensityD1
  simp only [Pi.neg_apply, id]
  field_simp
  ring

/-- **Heat equation for the Gaussian kernel.** For `t > 0` and every `z`, the time derivative
of the heat kernel is half its second space derivative:
`∂_t heatDensity t z = ½ ∂_z² heatDensity t z = heatDensityD2 t z / 2`. -/
theorem hasDerivAt_heatDensity_t {t : ℝ} (ht : 0 < t) (z : ℝ) :
    HasDerivAt (fun s => heatDensity s z) (heatDensityD2 t z / 2) t := by
  have hpos : 0 < 2 * Real.pi * t := by positivity
  have hsq : HasDerivAt (fun s : ℝ => Real.sqrt (2 * Real.pi * s))
      ((2 * Real.pi) / (2 * Real.sqrt (2 * Real.pi * t))) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).sqrt hpos.ne'
    simpa using this
  have hsq0 : Real.sqrt (2 * Real.pi * t) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hinv := hsq.inv hsq0
  have he : HasDerivAt (fun s : ℝ => -z ^ 2 / (2 * s)) (z ^ 2 / (2 * t ^ 2)) t := by
    have := ((hasDerivAt_id t).const_mul 2).inv (by positivity : (2 * t) ≠ 0)
    convert this.const_mul (-z ^ 2) using 1
    · ext s; simp [div_eq_mul_inv]
    · simp; field_simp
  have := hinv.mul he.exp
  refine this.congr_deriv ?_
  have hs2 : Real.sqrt (2 * Real.pi * t) ^ 2 = 2 * Real.pi * t := Real.sq_sqrt hpos.le
  unfold heatDensityD2 heatDensity
  simp only [Pi.inv_apply]
  field_simp
  linear_combination t * hs2

/-- The heat kernel is positive: `0 < heatDensity t z` for `t > 0`. -/
theorem heatDensity_pos {t : ℝ} (ht : 0 < t) (z : ℝ) : 0 < heatDensity t z := by
  unfold heatDensity
  have : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- Elementary Gaussian tail bound: `z² exp(-z² / (2t)) ≤ 2t` for `t > 0` (from
`u ≤ exp u`). -/
theorem sq_mul_exp_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    z ^ 2 * Real.exp (-z ^ 2 / (2 * t)) ≤ 2 * t := by
  have h1 := Real.add_one_le_exp (z ^ 2 / (2 * t))
  have h2 : Real.exp (-z ^ 2 / (2 * t)) * Real.exp (z ^ 2 / (2 * t)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have h3 : z ^ 2 = 2 * t * (z ^ 2 / (2 * t)) := by field_simp
  have h4 := Real.exp_pos (-z ^ 2 / (2 * t))
  have h5 : 0 ≤ z ^ 2 / (2 * t) := by positivity
  calc z ^ 2 * Real.exp (-z ^ 2 / (2 * t))
      = 2 * t * (z ^ 2 / (2 * t)) * Real.exp (-z ^ 2 / (2 * t)) := by rw [← h3]
    _ ≤ 2 * t * Real.exp (z ^ 2 / (2 * t)) * Real.exp (-z ^ 2 / (2 * t)) := by gcongr; linarith
    _ = 2 * t := by rw [mul_assoc, mul_comm (Real.exp _), h2, mul_one]

/-- Uniform bound on the heat kernel: `heatDensity t z ≤ (2π t)^{-1/2}` for `t > 0`. -/
theorem heatDensity_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    heatDensity t z ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ := by
  unfold heatDensity
  have : Real.exp (-z ^ 2 / (2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ z ^ 2 / (2 * t) := by positivity
    rw [neg_div]; linarith)
  have : 0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ := by positivity
  nlinarith

/-- Uniform bound on the first space derivative of the heat kernel, for `t > 0`:
`|heatDensityD1 t z| ≤ (1 + 2t) / t · (2π t)^{-1/2}`. -/
theorem abs_heatDensityD1_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    |heatDensityD1 t z| ≤ (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
  unfold heatDensityD1 heatDensity
  have he := Real.exp_pos (-z ^ 2 / (2 * t))
  have hle : Real.exp (-z ^ 2 / (2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ z ^ 2 / (2 * t) := by positivity
    rw [neg_div]; linarith)
  have hsq := sq_mul_exp_le ht z
  have hz : |z| ≤ 1 + z ^ 2 := by nlinarith [abs_nonneg z, sq_abs z]
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ := by positivity
  rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos ht, abs_of_nonneg hc, abs_of_pos he]
  have key : |z| * Real.exp (-z ^ 2 / (2 * t)) ≤ 1 + 2 * t := by nlinarith
  calc |z| / t * ((Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-z ^ 2 / (2 * t)))
      = (|z| * Real.exp (-z ^ 2 / (2 * t))) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ := by ring
    _ ≤ (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ := by gcongr

/-- Uniform bound on the second space derivative of the heat kernel, for `t > 0`:
`|heatDensityD2 t z| ≤ 3 / t · (2π t)^{-1/2}`. -/
theorem abs_heatDensityD2_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    |heatDensityD2 t z| ≤ 3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
  unfold heatDensityD2 heatDensity
  have he := Real.exp_pos (-z ^ 2 / (2 * t))
  have hle : Real.exp (-z ^ 2 / (2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ z ^ 2 / (2 * t) := by positivity
    rw [neg_div]; linarith)
  have hsq := sq_mul_exp_le ht z
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos he]
  have key : |z ^ 2 / t ^ 2 - 1 / t| * Real.exp (-z ^ 2 / (2 * t)) ≤ 3 / t := by
    have h1 : |z ^ 2 / t ^ 2 - 1 / t| ≤ z ^ 2 / t ^ 2 + 1 / t := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h2 : (z ^ 2 / t ^ 2 + 1 / t) * Real.exp (-z ^ 2 / (2 * t)) ≤ 3 / t := by
      have : z ^ 2 / t ^ 2 * Real.exp (-z ^ 2 / (2 * t)) ≤ 2 / t := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) ht]; nlinarith
      have : 1 / t * Real.exp (-z ^ 2 / (2 * t)) ≤ 1 / t := by
        have : 0 < 1 / t := by positivity
        nlinarith
      have : 3 / t = 2 / t + 1 / t := by ring
      nlinarith
    nlinarith
  calc |z ^ 2 / t ^ 2 - 1 / t| * ((Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-z ^ 2 / (2 * t)))
      = (|z ^ 2 / t ^ 2 - 1 / t| * Real.exp (-z ^ 2 / (2 * t))) *
          (Real.sqrt (2 * Real.pi * t))⁻¹ := by ring
    _ ≤ 3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹ := by gcongr

/-! ### Gaussian convolutions of a finite measure -/

/-- `z ↦ heatDensity t z` is continuous (every `t`). -/
theorem continuous_heatDensity (t : ℝ) : Continuous (heatDensity t) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_heatDensity_x t z).continuousAt

/-- `z ↦ heatDensityD1 t z` is continuous for `t > 0`. -/
theorem continuous_heatDensityD1 {t : ℝ} (ht : 0 < t) : Continuous (heatDensityD1 t) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_heatDensityD1_x ht.ne' z).continuousAt

/-- `z ↦ heatDensityD2 t z` is continuous (every `t`). -/
theorem continuous_heatDensityD2 (t : ℝ) : Continuous (heatDensityD2 t) := by
  unfold heatDensityD2
  exact (by fun_prop : Continuous fun z : ℝ => z ^ 2 / t ^ 2 - 1 / t).mul
    (continuous_heatDensity t)

/-- The heat-flow density of a measure `ρ` on `ℝ`: `heatFlowDensity ρ t y = ∫ φ_t(y - x) dρ(x)`
with `φ_t = heatDensity t`. For a probability `ρ` and `t > 0` it is the Lebesgue density of
`ρ * N(0, t) = heatKernel t ∘ₘ ρ` (`heatKernel_comp_eq_withDensity`). -/
noncomputable def heatFlowDensity (ρ : Measure ℝ) (t y : ℝ) : ℝ := ∫ x, heatDensity t (y - x) ∂ρ
/-- The space derivative of the heat-flow density, `∫ φ_t'(y - x) dρ(x)`
(`hasDerivAt_heatFlowDensity_x`). -/
noncomputable def heatFlowD1 (ρ : Measure ℝ) (t y : ℝ) : ℝ := ∫ x, heatDensityD1 t (y - x) ∂ρ
/-- The second space derivative of the heat-flow density, `∫ φ_t''(y - x) dρ(x)`
(`hasDerivAt_heatFlowD1_x`). -/
noncomputable def heatFlowD2 (ρ : Measure ℝ) (t y : ℝ) : ℝ := ∫ x, heatDensityD2 t (y - x) ∂ρ

section HF
variable (ρ : Measure ℝ) [IsFiniteMeasure ρ]

/-- For a finite measure `ρ` and `t > 0`, `y ↦ heatFlowDensity ρ t y` is differentiable with
derivative `heatFlowD1 ρ t y` (differentiation under the integral; the kernel derivative is
bounded uniformly in `y`, and `ρ` is finite). -/
theorem hasDerivAt_heatFlowDensity_x {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (heatFlowDensity ρ t) (heatFlowD1 ρ t y) y := by
  have hc := continuous_heatDensity t
  have hc1 := continuous_heatDensityD1 ht
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) univ_mem
    (F := fun y x => heatDensity t (y - x)) (F' := fun y x => heatDensityD1 t (y - x))
    (bound := fun _ => (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹)
    (Eventually.of_forall fun y => (hc.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hc.comp (by fun_prop)).aestronglyMeasurable
      (Real.sqrt (2 * Real.pi * t))⁻¹ (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _))
    (hc1.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x y _ => abs_heatDensityD1_le ht _) (integrable_const _)
    (Eventually.of_forall fun x y _ => ?_)).2
  exact (hasDerivAt_heatDensity_x t (y - x)).comp_sub_const y x

/-- For a finite measure `ρ` and `t > 0`, `y ↦ heatFlowD1 ρ t y` is differentiable with
derivative `heatFlowD2 ρ t y`. -/
theorem hasDerivAt_heatFlowD1_x {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (heatFlowD1 ρ t) (heatFlowD2 ρ t y) y := by
  have hc1 := continuous_heatDensityD1 ht
  have hc2 := continuous_heatDensityD2 t
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) univ_mem
    (F := fun y x => heatDensityD1 t (y - x)) (F' := fun y x => heatDensityD2 t (y - x))
    (bound := fun _ => 3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹)
    (Eventually.of_forall fun y => (hc1.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hc1.comp (by fun_prop)).aestronglyMeasurable
      _ (Eventually.of_forall fun x => abs_heatDensityD1_le ht _))
    (hc2.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x y _ => abs_heatDensityD2_le ht _) (integrable_const _)
    (Eventually.of_forall fun x y _ => ?_)).2
  exact (hasDerivAt_heatDensityD1_x ht.ne' (y - x)).comp_sub_const y x

/-- **Heat equation for the Gaussian convolution of a finite measure.** For a finite measure
`ρ` on `ℝ`, `t > 0` and every `y`, `p_t = ρ * φ_t` satisfies `∂_t p_t(y) = ½ ∂_y² p_t(y)`:
`HasDerivAt (fun r => heatFlowDensity ρ r y) (heatFlowD2 ρ t y / 2) t`. No density, moment or
integrability assumption on `ρ` is needed (the time derivative of the kernel is bounded
uniformly for times in `(t/2, 2t)`). -/
theorem hasDerivAt_heatFlowDensity_t {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun r => heatFlowDensity ρ r y) (heatFlowD2 ρ t y / 2) t := by
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hbd : ∀ r ∈ Ioo (t / 2) (2 * t), ∀ z,
      ‖heatDensityD2 r z / 2‖ ≤ 6 / t * (Real.sqrt (Real.pi * t))⁻¹ := by
    intro r hr z
    have hr0 : 0 < r := by linarith [hr.1]
    rw [Real.norm_eq_abs, abs_div, abs_two]
    have h1 := abs_heatDensityD2_le hr0 z
    have h2 : (Real.sqrt (2 * Real.pi * r))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ := by
      exact inv_anti₀ (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_le_sqrt (by nlinarith [hr.1, Real.pi_pos]))
    have h3 : 3 / r ≤ 6 / t := by
      rw [div_le_div_iff₀ hr0 ht]; linarith [hr.1]
    have : 0 ≤ (Real.sqrt (2 * Real.pi * r))⁻¹ := by positivity
    have : 0 ≤ 3 / r := by positivity
    calc |heatDensityD2 r z| / 2 ≤ |heatDensityD2 r z| := by
          linarith [abs_nonneg (heatDensityD2 r z)]
      _ ≤ 3 / r * (Real.sqrt (2 * Real.pi * r))⁻¹ := h1
      _ ≤ 6 / t * (Real.sqrt (Real.pi * t))⁻¹ := by gcongr
  have hmeas : ∀ r ∈ Ioo (t / 2) (2 * t),
      AEStronglyMeasurable (fun x => heatDensity r (y - x)) ρ := fun r hr =>
    ((continuous_heatDensity r).comp (by fun_prop)).aestronglyMeasurable
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) hs
    (F := fun r x => heatDensity r (y - x)) (F' := fun r x => heatDensityD2 r (y - x) / 2)
    (bound := fun _ => 6 / t * (Real.sqrt (Real.pi * t))⁻¹)
    (eventually_of_mem hs hmeas)
    (Integrable.of_bound (hmeas t ⟨by linarith, by linarith⟩) (Real.sqrt (2 * Real.pi * t))⁻¹
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _))
    (((continuous_heatDensityD2 t).comp (by fun_prop)).div_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x r hr => hbd r hr _) (integrable_const _)
    (Eventually.of_forall fun x r hr => hasDerivAt_heatDensity_t (by linarith [hr.1]) _)).2
  rwa [integral_div] at this

/-- For a nonzero finite measure `ρ` and `t > 0`, the heat-flow density is positive
everywhere: `0 < heatFlowDensity ρ t y`. -/
theorem heatFlowDensity_pos [NeZero ρ] {t : ℝ} (ht : 0 < t) (y : ℝ) :
    0 < heatFlowDensity ρ t y := by
  have hc := continuous_heatDensity t
  have hi : Integrable (fun x => heatDensity t (y - x)) ρ :=
    Integrable.of_bound (hc.comp (by fun_prop)).aestronglyMeasurable
      (Real.sqrt (2 * Real.pi * t))⁻¹ (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _)
  unfold heatFlowDensity
  rw [integral_pos_iff_support_of_nonneg (fun x => (heatDensity_pos ht _).le) hi]
  have : Function.support (fun x => heatDensity t (y - x)) = univ :=
    eq_univ_of_forall fun x => (heatDensity_pos ht _).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne ρ)

end HF

open scoped FormalizeSampling.OU

/-- **Law identification.** For a probability measure `ρ` on `ℝ` and `t > 0`,
`heatKernel t ∘ₘ ρ = ρ * N(0, t)` has Lebesgue density `heatFlowDensity ρ t`. -/
theorem heatKernel_comp_eq_withDensity (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {t : ℝ}
    (ht : 0 < t) :
    FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ ρ =
      volume.withDensity (fun y => ENNReal.ofReal (heatFlowDensity ρ t y)) := by
  have hσ : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have h := FormalizeSampling.OUPosterior.bind_gaussianReal_affine_eq_withDensity ρ 1 hσ
  have hv : (⟨Real.sqrt t ^ 2, sq_nonneg _⟩ : NNReal) = t.toNNReal := by
    ext; simp [Real.sq_sqrt ht.le, ht.le]
  simp only [one_mul, hv] at h
  have hd : FormalizeSampling.OUPosterior.affineDensity ρ 1 (Real.sqrt t) =
      heatFlowDensity ρ t := by
    funext y
    simp only [FormalizeSampling.OUPosterior.affineDensity, heatFlowDensity, one_mul,
      FormalizeSampling.Tweedie.gaussKernel]
    rw [hv]
    congr 1; funext x
    rw [gaussianPDFReal, heatDensity, Real.coe_toNNReal _ ht.le]
  rw [hd] at h
  rw [← h]
  rfl
/-! ### de Bruijn's identity for two families of densities -/

variable {P Q Px Qx Pxx Qxx : ℝ → ℝ → ℝ}

/-- The relative-entropy integrand `p_t log(p_t / q_t)` of two time-indexed densities
`P t x`, `Q t x`. -/
noncomputable def klIntegrand (P Q : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  P t x * Real.log (P t x / Q t x)

/-- The time derivative of `klIntegrand` along the heat equation `∂_t P = ½ P''`,
`∂_t Q = ½ Q''` (`hasDerivAt_klIntegrand_time`):
`(P'' (log(P/Q) + 1) - (P/Q) Q'') / 2`, with `P''`, `Q''` given as `Pxx`, `Qxx`. -/
noncomputable def klRate (P Q Pxx Qxx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (Pxx t x * (Real.log (P t x / Q t x) + 1) - P t x / Q t x * Qxx t x) / 2

/-- The relative score `∂_x log(P/Q) = P'/P - Q'/Q`, with `P'`, `Q'` given as `Px`, `Qx`. -/
noncomputable def relScore (P Q Px Qx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  Px t x / P t x - Qx t x / Q t x

/-- The relative Fisher information integrand `P (∂_x log(P/Q))²`. -/
noncomputable def fisherIntegrand (P Q Px Qx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  P t x * relScore P Q Px Qx t x ^ 2

/-- The boundary flux `P' (log(P/Q) + 1) - (P/Q) Q'` whose space derivative is
`2 · klRate + fisherIntegrand` (`hasDerivAt_klFlux_space`). -/
noncomputable def klFlux (P Q Px Qx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  Px t x * (Real.log (P t x / Q t x) + 1) - P t x / Q t x * Qx t x

/-- Pointwise time derivative of the KL integrand along the heat equation. If at `(t, x)`
`P, Q > 0` and `∂_t P = ½ Pxx`, `∂_t Q = ½ Qxx`, then
`∂_t [P log(P/Q)] = (Pxx (log(P/Q) + 1) - (P/Q) Qxx) / 2 = klRate`. -/
theorem hasDerivAt_klIntegrand_time {t x : ℝ} (hP : 0 < P t x) (hQ : 0 < Q t x)
    (hPt : HasDerivAt (fun r => P r x) (Pxx t x / 2) t)
    (hQt : HasDerivAt (fun r => Q r x) (Qxx t x / 2) t) :
    HasDerivAt (fun r => klIntegrand P Q r x) (klRate P Q Pxx Qxx t x) t := by
  have hdiv := hPt.div hQt hQ.ne'
  have hlog := hdiv.log (div_pos hP hQ).ne'
  have := hPt.mul hlog
  refine this.congr_deriv ?_
  unfold klRate
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Pointwise space derivative of the boundary flux (the integration-by-parts identity in
differential form). If at `(t, x)` `P, Q > 0`, `∂_x P = Px`, `∂_x Q = Qx`, `∂_x Px = Pxx`,
`∂_x Qx = Qxx`, then `∂_x klFlux = 2 · klRate + P (∂_x log(P/Q))²`. -/
theorem hasDerivAt_klFlux_space {t x : ℝ} (hP : 0 < P t x) (hQ : 0 < Q t x)
    (hPx : HasDerivAt (P t) (Px t x) x) (hQx : HasDerivAt (Q t) (Qx t x) x)
    (hPxx : HasDerivAt (Px t) (Pxx t x) x) (hQxx : HasDerivAt (Qx t) (Qxx t x) x) :
    HasDerivAt (klFlux P Q Px Qx t)
      (2 * klRate P Q Pxx Qxx t x + fisherIntegrand P Q Px Qx t x) x := by
  have hdiv := hPx.div hQx hQ.ne'
  have hlog := (hdiv.log (div_pos hP hQ).ne').add_const 1
  have := (hPxx.mul hlog).sub (hdiv.mul hQxx)
  refine this.congr_deriv ?_
  unfold klRate fisherIntegrand relScore
  simp only [Pi.div_apply]
  field_simp
  ring

/-- **Integration-by-parts step of de Bruijn's identity.** At a fixed time `t`, if `P t`,
`Q t` are positive and twice differentiable in `x` (derivatives `Px`, `Pxx`, `Qx`, `Qxx`), the
rate `klRate` and the Fisher integrand are Lebesgue integrable, and the boundary flux
`klFlux` tends to `0` at `±∞`, then `∫ klRate = -½ ∫ P (∂_x log(P/Q))²`. -/
theorem integral_klRate_eq {t : ℝ} (hP : ∀ x, 0 < P t x) (hQ : ∀ x, 0 < Q t x)
    (hPx : ∀ x, HasDerivAt (P t) (Px t x) x) (hQx : ∀ x, HasDerivAt (Q t) (Qx t x) x)
    (hPxx : ∀ x, HasDerivAt (Px t) (Pxx t x) x) (hQxx : ∀ x, HasDerivAt (Qx t) (Qxx t x) x)
    (hrate : Integrable (klRate P Q Pxx Qxx t)) (hfisher : Integrable (fisherIntegrand P Q Px Qx t))
    (hbot : Tendsto (klFlux P Q Px Qx t) atBot (𝓝 0))
    (htop : Tendsto (klFlux P Q Px Qx t) atTop (𝓝 0)) :
    ∫ x, klRate P Q Pxx Qxx t x = -(1 / 2) * ∫ x, fisherIntegrand P Q Px Qx t x := by
  have hd : ∀ x, HasDerivAt (klFlux P Q Px Qx t)
      (2 * klRate P Q Pxx Qxx t x + fisherIntegrand P Q Px Qx t x) x := fun x =>
    hasDerivAt_klFlux_space (hP x) (hQ x) (hPx x) (hQx x) (hPxx x) (hQxx x)
  have h0 := integral_of_hasDerivAt_of_tendsto hd ((hrate.const_mul 2).add hfisher) hbot htop
  rw [integral_add (hrate.const_mul 2) hfisher, integral_const_mul, sub_self] at h0
  linarith

/-- If `P t`, `Q t` are continuous and positive then `x ↦ P log(P/Q)` is continuous. -/
theorem continuous_klIntegrand {t : ℝ} (hP : ∀ x, 0 < P t x) (hQ : ∀ x, 0 < Q t x)
    (hPc : Continuous (P t)) (hQc : Continuous (Q t)) : Continuous (klIntegrand P Q t) :=
  hPc.mul ((hPc.div hQc fun x => (hQ x).ne').log fun x => (div_pos (hP x) (hQ x)).ne')

/-- **de Bruijn identity for relative entropy (abstract form).** Let `P, Q : ℝ → ℝ → ℝ`
(time, space) and `s ∈ 𝓝 t₀`. Assume, for all `t ∈ s` and all `x`: `P t x, Q t x > 0`; the heat
equations `∂_t P = ½ Pxx`, `∂_t Q = ½ Qxx`; `∂_x P = Px`, `∂_x Q = Qx`; and at `t₀`
`∂_x Px = Pxx`, `∂_x Qx = Qxx`. Assume further: `P t₀ log(P t₀ / Q t₀)` is integrable; the
rate `klRate` is dominated on `s` by an integrable `bound`; the relative Fisher integrand at
`t₀` is integrable; and the boundary flux at `t₀` vanishes at `±∞`. Then
`d/dt ∫ P_t log(P_t/Q_t) dx = -½ ∫ P_{t₀} (∂_x log(P_{t₀}/Q_{t₀}))² dx` at `t = t₀`. -/
theorem hasDerivAt_integral_klIntegrand {s : Set ℝ} {t₀ : ℝ} (hs : s ∈ 𝓝 t₀)
    (hP : ∀ t ∈ s, ∀ x, 0 < P t x) (hQ : ∀ t ∈ s, ∀ x, 0 < Q t x)
    (hPt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => P r x) (Pxx t x / 2) t)
    (hQt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => Q r x) (Qxx t x / 2) t)
    (hPx : ∀ t ∈ s, ∀ x, HasDerivAt (P t) (Px t x) x)
    (hQx : ∀ t ∈ s, ∀ x, HasDerivAt (Q t) (Qx t x) x)
    (hPxx : ∀ x, HasDerivAt (Px t₀) (Pxx t₀ x) x) (hQxx : ∀ x, HasDerivAt (Qx t₀) (Qxx t₀ x) x)
    (hint : Integrable (klIntegrand P Q t₀)) {bound : ℝ → ℝ} (hbound_int : Integrable bound)
    (hbound : ∀ t ∈ s, ∀ x, |klRate P Q Pxx Qxx t x| ≤ bound x)
    (hfisher : Integrable (fisherIntegrand P Q Px Qx t₀))
    (hbot : Tendsto (klFlux P Q Px Qx t₀) atBot (𝓝 0))
    (htop : Tendsto (klFlux P Q Px Qx t₀) atTop (𝓝 0)) :
    HasDerivAt (fun t => ∫ x, klIntegrand P Q t x)
      (-(1 / 2) * ∫ x, fisherIntegrand P Q Px Qx t₀ x) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (klIntegrand P Q t) volume := by
    filter_upwards [hs] with t ht
    exact (continuous_klIntegrand (hP t ht) (hQ t ht)
      (continuous_iff_continuousAt.2 fun x => (hPx t ht x).continuousAt)
      (continuous_iff_continuousAt.2 fun x => (hQx t ht x).continuousAt)).aestronglyMeasurable
  have hPxxm : Pxx t₀ = deriv (Px t₀) := funext fun x => (hPxx x).deriv.symm
  have hQxxm : Qxx t₀ = deriv (Qx t₀) := funext fun x => (hQxx x).deriv.symm
  have hPm : Measurable (P t₀) :=
    (continuous_iff_continuousAt.2 fun x => (hPx t₀ ht₀ x).continuousAt).measurable
  have hQm : Measurable (Q t₀) :=
    (continuous_iff_continuousAt.2 fun x => (hQx t₀ ht₀ x).continuousAt).measurable
  have hrate_meas : AEStronglyMeasurable (klRate P Q Pxx Qxx t₀) volume := by
    have h1 : Measurable (Pxx t₀) := hPxxm ▸ measurable_deriv _
    have h2 : Measurable (Qxx t₀) := hQxxm ▸ measurable_deriv _
    unfold klRate
    exact ((h1.mul (((hPm.div hQm).log).add_const 1)).sub
      ((hPm.div hQm).mul h2)).div_const 2 |>.aestronglyMeasurable
  obtain ⟨hrate_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint
    hrate_meas (Eventually.of_forall fun x t ht => by simpa using hbound t ht x) hbound_int
    (Eventually.of_forall fun x t ht =>
      hasDerivAt_klIntegrand_time (hP t ht x) (hQ t ht x) (hPt t ht x) (hQt t ht x))
  rwa [integral_klRate_eq (hP t₀ ht₀) (hQ t₀ ht₀) (hPx t₀ ht₀) (hQx t₀ ht₀) hPxx hQxx hrate_int
    hfisher hbot htop] at hderiv

/-! ### de Bruijn along the heat flow of two laws -/

open FormalizeSampling.ProximalContraction InformationTheory

/-- The relative Fisher information along the heat flow,
`heatFisher ρ π t = ∫ p_t (∂_x log(p_t / q_t))² dx` with `p_t = heatFlowDensity ρ t` and
`q_t = heatFlowDensity π t`, i.e. `I(ρ_t‖π_t)` for `t > 0`. -/
noncomputable def heatFisher (ρ π : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t x

/-- **Regularity hypotheses for de Bruijn's identity along the heat flow** on an open set `s`
of positive times, for the densities `p_t = heatFlowDensity ρ t`, `q_t = heatFlowDensity π t`
(all derivatives are the explicit Gaussian-convolution derivatives `heatFlowD1`, `heatFlowD2`).
These are standard integrability / boundary conditions; none of them is the identity itself. -/
structure HeatFlowRegular (ρ π : Measure ℝ) (s : Set ℝ) : Prop where
  /-- The time set is open. -/
  isOpen : IsOpen s
  /-- Only positive times. -/
  subset_Ioi : s ⊆ Ioi 0
  /-- `p_t log(p_t/q_t)` is Lebesgue integrable (finite KL along the flow). -/
  integrable_kl : ∀ t ∈ s, Integrable (klIntegrand (heatFlowDensity ρ) (heatFlowDensity π) t)
  /-- The time derivative `klRate` of the KL integrand is dominated, locally uniformly in time,
  by an integrable function of `x`. -/
  dominated : ∀ t ∈ s, ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ᶠ r in 𝓝 t, ∀ x,
    |klRate (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD2 ρ) (heatFlowD2 π) r x|
      ≤ bound x
  /-- The relative Fisher integrand `p_t (∂_x log(p_t/q_t))²` is integrable. -/
  integrable_fisher : ∀ t ∈ s, Integrable
    (fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t)
  /-- The boundary flux vanishes at `-∞`. -/
  tendsto_atBot : ∀ t ∈ s, Tendsto
    (klFlux (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t) atBot (𝓝 0)
  /-- The boundary flux vanishes at `+∞`. -/
  tendsto_atTop : ∀ t ∈ s, Tendsto
    (klFlux (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t) atTop (𝓝 0)

variable {ρ π : Measure ℝ}

/-- For probability measures `ρ, π`, `t > 0` and integrable `p_t log(p_t/q_t)`, the heat-flow KL
is the density integral: `heatKL ρ π t = ∫ p_t log(p_t / q_t) dx`. -/
theorem heatKL_eq_integral [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {t : ℝ}
    (ht : 0 < t) (hint : Integrable (klIntegrand (heatFlowDensity ρ) (heatFlowDensity π) t)) :
    heatKL ρ π t = ∫ x, klIntegrand (heatFlowDensity ρ) (heatFlowDensity π) t x := by
  have hρ := heatKernel_comp_eq_withDensity ρ ht
  have hπ := heatKernel_comp_eq_withDensity π ht
  have : IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensity ρ t y)) := by
    rw [← hρ]; infer_instance
  have : IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensity π t y)) := by
    rw [← hπ]; infer_instance
  have hmρ : Measurable (heatFlowDensity ρ t) := (continuous_iff_continuousAt.2 fun y =>
    (hasDerivAt_heatFlowDensity_x ρ ht y).continuousAt).measurable
  have hmπ : Measurable (heatFlowDensity π t) := (continuous_iff_continuousAt.2 fun y =>
    (hasDerivAt_heatFlowDensity_x π ht y).continuousAt).measurable
  rw [heatKL, hρ, hπ]
  exact (FormalizeSampling.DeterministicStep.klDiv_withDensity_real hmρ hmπ
    (fun y => (heatFlowDensity_pos ρ ht y).le) (heatFlowDensity_pos π ht) hint).2

/-- **de Bruijn identity along the heat flow (Verified under `HeatFlowRegular`).** For
probability measures `ρ, π` on `ℝ` and `t₀ ∈ s` with `HeatFlowRegular ρ π s`,
`t ↦ KL(ρ * N(0,t) ‖ π * N(0,t))` is differentiable at `t₀` with derivative
`-½ I(ρ_{t₀}‖π_{t₀}) = -(1/2) * heatFisher ρ π t₀`. -/
theorem hasDerivAt_heatKL [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {s : Set ℝ}
    (hreg : HeatFlowRegular ρ π s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    HasDerivAt (heatKL ρ π) (-(1 / 2) * heatFisher ρ π t₀) t₀ := by
  obtain ⟨bound, hb_int, hev⟩ := hreg.dominated t₀ ht₀
  obtain ⟨v, hv, hvb⟩ := hev.exists_mem
  have hs : s ∈ 𝓝 t₀ := hreg.isOpen.mem_nhds ht₀
  have hpos : ∀ t ∈ s, 0 < t := fun t ht => hreg.subset_Ioi ht
  have hd := hasDerivAt_integral_klIntegrand (s := v ∩ s) (inter_mem hv hs)
    (fun t ht x => heatFlowDensity_pos ρ (hpos t ht.2) x)
    (fun t ht x => heatFlowDensity_pos π (hpos t ht.2) x)
    (fun t ht x => hasDerivAt_heatFlowDensity_t ρ (hpos t ht.2) x)
    (fun t ht x => hasDerivAt_heatFlowDensity_t π (hpos t ht.2) x)
    (fun t ht x => hasDerivAt_heatFlowDensity_x ρ (hpos t ht.2) x)
    (fun t ht x => hasDerivAt_heatFlowDensity_x π (hpos t ht.2) x)
    (fun x => hasDerivAt_heatFlowD1_x ρ (hpos t₀ ht₀) x)
    (fun x => hasDerivAt_heatFlowD1_x π (hpos t₀ ht₀) x)
    (hreg.integrable_kl t₀ ht₀) hb_int (fun t ht => hvb t ht.1)
    (hreg.integrable_fisher t₀ ht₀) (hreg.tendsto_atBot t₀ ht₀) (hreg.tendsto_atTop t₀ ht₀)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact heatKL_eq_integral (hpos t ht) (hreg.integrable_kl t ht)

/-! ### Forward-step contraction with de Bruijn discharged -/

/-- Data processing along the heat flow: if `KL(ρ‖π) < ∞` then
`heatKL ρ π t ≤ heatKL ρ π 0 = KL(ρ‖π).toReal` for every `t`. -/
theorem heatKL_le_heatKL_zero [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (hKL : klDiv ρ π ≠ ⊤) (t : ℝ) : heatKL ρ π t ≤ heatKL ρ π 0 := by
  rw [heatKL_zero, heatKL]
  exact ENNReal.toReal_mono hKL (klDiv_comp_right_le _ _ _)

/-- **Forward-step contraction with de Bruijn discharged.** For probability measures `ρ, π`
with `KL(ρ‖π) < ∞`, `α ≥ 0`, `η > 0`, `HeatFlowRegular ρ π s` with `(0, η] ⊆ s`, and the named
LSI of `π_t` along the curve for `t ∈ (0, η)`, `2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)`:
`KL(ρ_η‖π_η) ≤ KL(ρ‖π) / (1 + α η)`. No regularity at `t = 0` is required: the Grönwall argument
runs on `[τ, η]` and `τ → 0⁺` is handled by data processing `KL(ρ_τ‖π_τ) ≤ KL(ρ‖π)`
(`Gronwall.le_div_of_hasDerivAt_Ioc`). -/
theorem heatKL_le_div_of_regular [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {α η : ℝ}
    (hα : 0 ≤ α) (hη : 0 < η) (hKL : klDiv ρ π ≠ ⊤) {s : Set ℝ} (hreg : HeatFlowRegular ρ π s)
    (hs : Ioc 0 η ⊆ s) (hL : ∀ t ∈ Ioo 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * heatFisher ρ π t) :
    heatKL ρ π η ≤ heatKL ρ π 0 / (1 + α * η) :=
  Gronwall.le_div_of_hasDerivAt_Ioc hα hη (fun _ ht => hasDerivAt_heatKL hreg (hs ht)) hL
    fun τ _ => heatKL_le_heatKL_zero hKL τ

/-- Non-vacuity of `HeatFlowRegular`: for every probability measure `ρ`,
`HeatFlowRegular ρ ρ (Ioi 0)` holds (all integrands vanish identically). -/
theorem heatFlowRegular_self (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    HeatFlowRegular ρ ρ (Ioi 0) := by
  have hdiv : ∀ t ∈ Ioi (0 : ℝ), ∀ x, heatFlowDensity ρ t x / heatFlowDensity ρ t x = 1 :=
    fun t ht x => div_self (heatFlowDensity_pos ρ ht x).ne'
  have hkl : ∀ t ∈ Ioi (0 : ℝ), klIntegrand (heatFlowDensity ρ) (heatFlowDensity ρ) t = 0 :=
    fun t ht => funext fun x => by simp [klIntegrand, hdiv t ht x]
  have hrate : ∀ t ∈ Ioi (0 : ℝ), ∀ x,
      klRate (heatFlowDensity ρ) (heatFlowDensity ρ) (heatFlowD2 ρ) (heatFlowD2 ρ) t x = 0 :=
    fun t ht x => by simp [klRate, hdiv t ht x]
  have hfis : ∀ t ∈ Ioi (0 : ℝ), fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity ρ)
      (heatFlowD1 ρ) (heatFlowD1 ρ) t = 0 :=
    fun t _ => funext fun x => by simp [fisherIntegrand, relScore]
  have hflux : ∀ t ∈ Ioi (0 : ℝ), klFlux (heatFlowDensity ρ) (heatFlowDensity ρ)
      (heatFlowD1 ρ) (heatFlowD1 ρ) t = 0 :=
    fun t ht => funext fun x => by simp [klFlux, hdiv t ht x]
  refine ⟨isOpen_Ioi, subset_rfl, fun t ht => by rw [hkl t ht]; exact integrable_zero _ _ _,
    fun t ht => ⟨0, integrable_zero _ _ _, ?_⟩, fun t ht => by
      rw [hfis t ht]; exact integrable_zero _ _ _, fun t ht => by rw [hflux t ht]; exact
      tendsto_const_nhds, fun t ht => by rw [hflux t ht]; exact tendsto_const_nhds⟩
  filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr x
  simp [hrate r hr x]

end FormalizeSampling.HeatFlowDeBruijn
