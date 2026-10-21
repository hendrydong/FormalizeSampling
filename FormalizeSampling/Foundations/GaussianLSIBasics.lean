module

public import FormalizeSampling.Foundations.HeatFlowDeBruijn
public import FormalizeSampling.Foundations.KLChainRule
public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.GaussianKL
public import FormalizeSampling.Foundations.HeatKernel

/-!
# Helpers for the Gaussian log-Sobolev inequality along the heat flow

Status: **Verified** (helper module; the hypotheses are stated in each theorem). This file holds
the parts of the Gaussian LSI along the heat flow that do not need the regularity theorem of
`Foundations/HeatFlowRegularityPerturbed.lean`; `Foundations/GaussianLSI.lean` (which imports that
regularity theorem) states the LSI itself. All declarations live in the namespace
`FormalizeSampling.GaussianLSI`.

Notation (as in `HeatFlowDeBruijn`): `φ_a = heatDensity a` is the `N(0, a)` density,
`p_t = heatFlowDensity ρ t = ρ * φ_t`, `π = N(0, v)` (`v > 0`), `π_t = π * N(0, t) = N(0, v + t)`,
`K(t) = heatKL ρ π t = KL(ρ_t‖π_t)` and `I(t) = heatFisher ρ π t = I(ρ_t‖π_t)`. The relative
score flux is `G_t = gaussRelFlux ρ v t = p_t' + y p_t / (v + t) = p_t ∂_y log(p_t / q_t)`.

## Main results

* `heatFlow_semigroup`: `p_{t+a} = p_t * φ_a` and `p_{t+a}' = p_t * φ_a'` pointwise.
* `heatFlowDensity_gaussianReal`: `heatFlowDensity N(0, v) t = heatDensity (v + t)`.
* `integral_heatDensity_mul_gaussRelFlux`: `G_{t+a} = c ∫ φ_a(· - z) G_t(z) dz`,
  `c = (v + t)/(v + t + a)` (integration by parts against the heat kernel).
* `heatFisher_gaussianReal_le` (Fisher decay): `I(t + a) ≤ ((v + t)/(v + t + a))² I(t)`.
* `heatKL_le_div_two_mul`: `KL(ρ_T‖π_T) ≤ (∫ (x - u)² d(ρ ⊗ π)) / (2T)` (chain rule).
* `klDiv_heatKernel_comp_ne_top_of_regular`, `klDiv_heatKernel_comp_gaussianReal_ne_top`:
  `KL(ρ_t‖π_t) < ∞` under `HeatFlowRegular` (no moment assumption).

## Not proved here

* The Gaussian LSI along the heat flow: `Foundations/GaussianLSI.lean`; PX-2 for Gaussian
  targets: `Samplers/ProximalHeatFlow.lean`.
* The fields of `HeatFlowRegular`: `Foundations/HeatFlowRegularityPerturbed.lean` derives them from
  a finite second moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction
open scoped FormalizeSampling.OU

namespace FormalizeSampling.GaussianLSI

/-! ### Elementary facts on the Gaussian kernel -/

/-- For `t > 0`, the heat kernel is the Mathlib Gaussian density:
`heatDensity t = gaussianPDFReal 0 t.toNNReal`. -/
theorem heatDensity_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) :
    heatDensity t = gaussianPDFReal 0 t.toNNReal := by
  funext z
  rw [gaussianPDFReal, heatDensity, Real.coe_toNNReal _ ht.le, sub_zero]

/-- For `t > 0` and every `z`, `y ↦ heatDensity t (y - z)` is Lebesgue integrable. -/
theorem integrable_heatDensity_sub {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Integrable (fun y => heatDensity t (y - z)) := by
  rw [heatDensity_eq_gaussianPDFReal ht]
  exact (integrable_gaussianPDFReal 0 _).comp_sub_right z

/-- For `t > 0` and every `z`, `∫ heatDensity t (y - z) dy = 1`. -/
theorem integral_heatDensity_sub {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ∫ y, heatDensity t (y - z) = 1 := by
  rw [integral_sub_right_eq_self (fun y => heatDensity t y), heatDensity_eq_gaussianPDFReal ht,
    integral_gaussianPDFReal_eq_one]
  rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact ht

/-- For `t > 0` and every `y`, `z ↦ heatDensity t (y - z)` is Lebesgue integrable. -/
theorem integrable_heatDensity_sub' {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun z => heatDensity t (y - z)) := by
  rw [heatDensity_eq_gaussianPDFReal ht]
  exact (integrable_gaussianPDFReal 0 _).comp_sub_left y

/-- For `t > 0` and every `y`, `heatDensity t (y - z) → 0` as `z → ±∞` (along `cocompact`). -/
theorem tendsto_heatDensity_sub {t : ℝ} (ht : 0 < t) (y : ℝ) {l : Filter ℝ}
    (hl : Tendsto (fun z => (y - z) ^ 2) l atTop) :
    Tendsto (fun z => heatDensity t (y - z)) l (𝓝 0) := by
  unfold heatDensity
  have h : Tendsto (fun z => -(y - z) ^ 2 / (2 * t)) l atBot := by
    simp_rw [neg_div]
    exact tendsto_neg_atTop_atBot.comp (hl.atTop_div_const (by positivity))
  simpa using (Real.tendsto_exp_atBot.comp h).const_mul (Real.sqrt (2 * Real.pi * t))⁻¹

/-- `(y - z)² → ∞` as `z → +∞`. -/
theorem tendsto_sub_sq_atTop (y : ℝ) : Tendsto (fun z : ℝ => (y - z) ^ 2) atTop atTop := by
  have : Tendsto (fun z : ℝ => z - y) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  refine ((tendsto_pow_atTop two_ne_zero).comp this).congr fun z => ?_
  simp only [Function.comp]; ring

/-- `(y - z)² → ∞` as `z → -∞`. -/
theorem tendsto_sub_sq_atBot (y : ℝ) : Tendsto (fun z : ℝ => (y - z) ^ 2) atBot atTop := by
  have : Tendsto (fun z : ℝ => y - z) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop
  exact (tendsto_pow_atTop two_ne_zero).comp this

/-! ### Uniqueness of continuous densities -/

/-- Two continuous nonnegative functions with the same finite density measure coincide. -/
theorem eq_of_withDensity_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    [IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (f x))]
    (h : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : f = g :=
  MeasureHelpers.eq_of_withDensity_eq hf hg hf0 hg0 h

/-! ### The heat-flow density of a probability measure -/

section HeatFlow

variable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- For a probability `ρ` and `t > 0`, `y ↦ heatFlowDensity ρ t y` is continuous. -/
theorem continuous_heatFlowDensity {t : ℝ} (ht : 0 < t) : Continuous (heatFlowDensity ρ t) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_heatFlowDensity_x ρ ht y).continuousAt

/-- For a probability `ρ` and `t > 0`, `y ↦ heatFlowD1 ρ t y` is continuous. -/
theorem continuous_heatFlowD1 {t : ℝ} (ht : 0 < t) : Continuous (heatFlowD1 ρ t) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_heatFlowD1_x ρ ht y).continuousAt

/-- For a probability `ρ` and `t > 0`, `0 ≤ heatFlowDensity ρ t y ≤ (2π t)^{-1/2}`. -/
theorem heatFlowDensity_le {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatFlowDensity ρ t y ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ := by
  unfold heatFlowDensity
  calc ∫ x, heatDensity t (y - x) ∂ρ ≤ ∫ _x, (Real.sqrt (2 * Real.pi * t))⁻¹ ∂ρ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => (heatDensity_pos ht _).le)
          (integrable_const _) (Eventually.of_forall fun x => heatDensity_le ht _)
    _ = _ := by simp

/-- For a probability `ρ` and `t > 0`, `|heatFlowD1 ρ t y| ≤ (1 + 2t)/t · (2π t)^{-1/2}`. -/
theorem abs_heatFlowD1_le {t : ℝ} (ht : 0 < t) (y : ℝ) :
    |heatFlowD1 ρ t y| ≤ (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ := by
  unfold heatFlowD1
  calc |∫ x, heatDensityD1 t (y - x) ∂ρ| ≤ ∫ x, |heatDensityD1 t (y - x)| ∂ρ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ∂ρ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun x => abs_heatDensityD1_le ht _)
    _ = _ := by simp

/-- For a probability `ρ` and `t > 0`, `ρ * N(0, t)` is a probability measure written as a
density measure. -/
theorem isProbabilityMeasure_withDensity_heatFlowDensity {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensity ρ t y)) := by
  rw [← heatKernel_comp_eq_withDensity ρ ht]; infer_instance

/-- For a probability `ρ` and `t > 0`, `heatFlowDensity ρ t` is Lebesgue integrable. -/
theorem integrable_heatFlowDensity {t : ℝ} (ht : 0 < t) : Integrable (heatFlowDensity ρ t) := by
  have := isProbabilityMeasure_withDensity_heatFlowDensity ρ ht
  refine ⟨(continuous_heatFlowDensity ρ ht).aestronglyMeasurable, ?_⟩
  have h1 := measure_univ (μ := volume.withDensity fun y => ENNReal.ofReal (heatFlowDensity ρ t y))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [HasFiniteIntegral]
  simp_rw [Real.enorm_eq_ofReal (heatFlowDensity_pos ρ ht _).le, h1]
  exact ENNReal.one_lt_top

/-- **Heat semigroup, density form.** For a probability `ρ` and `t, a > 0`,
`p_{t+a}(y) = ∫ p_t(z) φ_a(y - z) dz` and `p'_{t+a}(y) = ∫ p_t(z) φ_a'(y - z) dz`, where
`p_t = heatFlowDensity ρ t`, `φ_a = heatDensity a`, `φ_a' = heatDensityD1 a`. -/
theorem heatFlow_semigroup {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    (∀ y, heatFlowDensity ρ (t + a) y = ∫ z, heatFlowDensity ρ t z * heatDensity a (y - z)) ∧
    ∀ y, heatFlowD1 ρ (t + a) y = ∫ z, heatFlowDensity ρ t z * heatDensityD1 a (y - z) := by
  set μ := FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ ρ with hμ
  have hμd := heatKernel_comp_eq_withDensity ρ ht
  have hcomp : FormalizeSampling.OU.heatKernel a.toNNReal ∘ₘ μ =
      FormalizeSampling.OU.heatKernel (t + a).toNNReal ∘ₘ ρ := by
    rw [hμ, Measure.comp_assoc, FormalizeSampling.OU.heatKernel_comp_heatKernel,
      Real.toNNReal_add ht.le ha.le]
  have hd := heatKernel_comp_eq_withDensity μ ha
  rw [hcomp, heatKernel_comp_eq_withDensity ρ (by linarith)] at hd
  have := isProbabilityMeasure_withDensity_heatFlowDensity ρ (show 0 < t + a by linarith)
  have heq : heatFlowDensity ρ (t + a) = heatFlowDensity μ a :=
    eq_of_withDensity_eq (continuous_heatFlowDensity ρ (by linarith))
      (continuous_heatFlowDensity μ ha) (fun y => (heatFlowDensity_pos ρ (by linarith) y).le)
      (fun y => (heatFlowDensity_pos μ ha y).le) hd
  have hmeas : Measurable fun y => ENNReal.ofReal (heatFlowDensity ρ t y) :=
    ENNReal.measurable_ofReal.comp (continuous_heatFlowDensity ρ ht).measurable
  have hlt : ∀ᵐ y ∂(volume : Measure ℝ), ENNReal.ofReal (heatFlowDensity ρ t y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hint : ∀ g : ℝ → ℝ, ∫ z, g z ∂μ = ∫ z, heatFlowDensity ρ t z * g z := by
    intro g
    rw [hμ, hμd, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
    congr 1; funext z
    rw [ENNReal.toReal_ofReal (heatFlowDensity_pos ρ ht z).le, smul_eq_mul]
  refine ⟨fun y => by rw [heq]; exact hint _, fun y => ?_⟩
  have h1 := hasDerivAt_heatFlowDensity_x ρ (show 0 < t + a by linarith) y
  rw [heq] at h1
  rw [h1.unique (hasDerivAt_heatFlowDensity_x μ ha y)]
  exact hint _

end HeatFlow

/-! ### The heat flow of the Gaussian target -/

/-- For `v, t > 0`, the heat flow of `N(0, v)` is `N(0, v + t)`:
`heatFlowDensity (gaussianReal 0 v) t = heatDensity (v + t)`. -/
theorem heatFlowDensity_gaussianReal {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    heatFlowDensity (gaussianReal 0 v.toNNReal) t = heatDensity (v + t) := by
  have hd := heatKernel_comp_eq_withDensity (gaussianReal 0 v.toNNReal) ht
  have hb : FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ gaussianReal 0 v.toNNReal =
      gaussianReal 0 (v + t).toNNReal := by
    rw [Real.toNNReal_add hv.le ht.le, ← FormalizeSampling.OU.bind_heat]
    rfl
  have hvt : (v + t).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith
  rw [hb, gaussianReal_of_var_ne_zero _ hvt, gaussianPDF_def,
    ← heatDensity_eq_gaussianPDFReal (by linarith)] at hd
  have : IsProbabilityMeasure (volume.withDensity fun y => ENNReal.ofReal (heatDensity (v + t) y))
      := by
    rw [hd, ← heatKernel_comp_eq_withDensity _ ht]; infer_instance
  exact (eq_of_withDensity_eq (continuous_heatDensity _)
    (continuous_heatFlowDensity _ ht) (fun y => (heatDensity_pos (by linarith) y).le)
    (fun y => (heatFlowDensity_pos _ ht y).le) hd).symm

/-- For `v, t > 0`, `heatFlowD1 (gaussianReal 0 v) t = heatDensityD1 (v + t)`. -/
theorem heatFlowD1_gaussianReal {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    heatFlowD1 (gaussianReal 0 v.toNNReal) t = heatDensityD1 (v + t) := by
  funext y
  have h1 := hasDerivAt_heatFlowDensity_x (gaussianReal 0 v.toNNReal) ht y
  rw [heatFlowDensity_gaussianReal hv ht] at h1
  exact h1.unique (hasDerivAt_heatDensity_x _ y)

/-! ### The relative score of the heat flow against the Gaussian heat flow -/

/-- The relative score flux of the heat flow of `ρ` against the Gaussian `N(0, v + t)`:
`gaussRelFlux ρ v t y = p_t'(y) + y / (v + t) · p_t(y)`, i.e. `p_t (∂_y log(p_t / q_t))` with
`q_t = heatDensity (v + t)` (`fisherIntegrand_gaussianReal`). -/
noncomputable def gaussRelFlux (ρ : Measure ℝ) (v t y : ℝ) : ℝ :=
  heatFlowD1 ρ t y + y / (v + t) * heatFlowDensity ρ t y

section Score

variable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- **Integration by parts against the heat kernel.** For a probability `ρ`, `t, a > 0` and
every `y`: `∫ φ_a(y - z) p_t'(z) dz = ∫ p_t(z) φ_a'(y - z) dz`. -/
theorem integral_heatDensity_mul_heatFlowD1 {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (y : ℝ) :
    ∫ z, heatDensity a (y - z) * heatFlowD1 ρ t z
      = ∫ z, heatFlowDensity ρ t z * heatDensityD1 a (y - z) := by
  set C := (Real.sqrt (2 * Real.pi * t))⁻¹
  set C1 := (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹
  set Ca := (1 + 2 * a) / a * (Real.sqrt (2 * Real.pi * a))⁻¹
  have hd : ∀ z, HasDerivAt (fun z => heatDensity a (y - z) * heatFlowDensity ρ t z)
      (-heatDensityD1 a (y - z) * heatFlowDensity ρ t z
        + heatDensity a (y - z) * heatFlowD1 ρ t z) z := by
    intro z
    have h1 := (hasDerivAt_heatDensity_x a (y - z)).comp z ((hasDerivAt_id z).const_sub y)
    have := h1.mul (hasDerivAt_heatFlowDensity_x ρ ht z)
    convert this using 1
    · simp only [Function.comp_def]; rfl
    · simp only [Function.comp_apply]; ring
  have hA : Integrable fun z => -heatDensityD1 a (y - z) * heatFlowDensity ρ t z :=
    (integrable_heatFlowDensity ρ ht).bdd_mul (c := Ca)
      (((continuous_heatDensityD1 ha).comp (by fun_prop)).neg.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_neg]; exact abs_heatDensityD1_le ha _)
  have hB : Integrable fun z => heatDensity a (y - z) * heatFlowD1 ρ t z :=
    (integrable_heatDensity_sub' ha y).mul_bdd (c := C1)
      (continuous_heatFlowD1 ρ ht).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_heatFlowD1_le ρ ht z)
  have hlim : ∀ l : Filter ℝ, Tendsto (fun z => (y - z) ^ 2) l atTop →
      Tendsto (fun z => heatDensity a (y - z) * heatFlowDensity ρ t z) l (𝓝 0) := by
    intro l hl
    have h0 := (tendsto_heatDensity_sub ha y hl).mul_const C
    rw [zero_mul] at h0
    refine squeeze_zero_norm (fun z => ?_) h0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatDensity_pos ha _),
      abs_of_pos (heatFlowDensity_pos ρ ht _)]
    exact mul_le_mul_of_nonneg_left (heatFlowDensity_le ρ ht z) (heatDensity_pos ha _).le
  have h0 := integral_of_hasDerivAt_of_tendsto hd (hA.add hB) (hlim _ (tendsto_sub_sq_atBot y))
    (hlim _ (tendsto_sub_sq_atTop y))
  rw [integral_add hA hB, sub_self] at h0
  have : ∫ z, -heatDensityD1 a (y - z) * heatFlowDensity ρ t z
      = -∫ z, heatFlowDensity ρ t z * heatDensityD1 a (y - z) := by
    rw [← integral_neg]; congr 1; funext z; ring
  linarith

/-- **Relative score as a heat-kernel average.** For a probability `ρ`, `v, t, a > 0` and every
`y`, with `G_t = gaussRelFlux ρ v t`:
`∫ φ_a(y - z) G_t(z) dz = ((v + t + a) / (v + t)) · G_{t+a}(y)`, i.e.
`G_{t+a} = c ∫ φ_a(· - z) G_t(z) dz` with `c = (v + t) / (v + t + a) < 1`. -/
theorem integral_heatDensity_mul_gaussRelFlux {v t a : ℝ} (hv : 0 < v) (ht : 0 < t)
    (ha : 0 < a) (y : ℝ) :
    ∫ z, heatDensity a (y - z) * gaussRelFlux ρ v t z
      = (v + t + a) / (v + t) * gaussRelFlux ρ v (t + a) y := by
  obtain ⟨hP, hP1⟩ := heatFlow_semigroup ρ ht ha
  have hPi := integrable_heatFlowDensity ρ ht
  have hI1 : Integrable fun z => heatDensity a (y - z) * heatFlowD1 ρ t z :=
    (integrable_heatDensity_sub' ha y).mul_bdd
      (continuous_heatFlowD1 ρ ht).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_heatFlowD1_le ρ ht z)
  have hI2 : Integrable fun z => heatFlowDensity ρ t z * heatDensity a (y - z) :=
    hPi.mul_bdd ((continuous_heatDensity a).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatDensity_pos ha _).le]; exact heatDensity_le ha _)
  have hI3 : Integrable fun z => heatFlowDensity ρ t z * heatDensityD1 a (y - z) :=
    hPi.mul_bdd ((continuous_heatDensityD1 ha).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_heatDensityD1_le ha _)
  have hpt : ∀ z, heatDensity a (y - z) * gaussRelFlux ρ v t z
      = heatDensity a (y - z) * heatFlowD1 ρ t z + (1 / (v + t)) *
        (y * (heatFlowDensity ρ t z * heatDensity a (y - z))
          + a * (heatFlowDensity ρ t z * heatDensityD1 a (y - z))) := by
    intro z
    unfold gaussRelFlux heatDensityD1
    field_simp
    ring
  have hI23 : Integrable fun z => 1 / (v + t) *
      (y * (heatFlowDensity ρ t z * heatDensity a (y - z))
        + a * (heatFlowDensity ρ t z * heatDensityD1 a (y - z))) :=
    ((hI2.const_mul y).add (hI3.const_mul a)).const_mul _
  simp_rw [hpt]
  rw [integral_add hI1 hI23,
    integral_const_mul, integral_add (hI2.const_mul y) (hI3.const_mul a), integral_const_mul,
    integral_const_mul, integral_heatDensity_mul_heatFlowD1 ρ ht ha, ← hP, ← hP1]
  unfold gaussRelFlux
  have : v + t ≠ 0 := by linarith
  have : v + (t + a) ≠ 0 := by linarith
  field_simp
  ring

end Score

/-! ### Fisher information decay along the heat flow (Gaussian target) -/

/-- **Weighted Cauchy–Schwarz.** For `k ≥ 0`, `p > 0` and `g` with `k p`, `k g`, `k g² / p`
integrable and `∫ k p > 0`: `(∫ k g)² ≤ (∫ k p) (∫ k g² / p)`. -/
theorem sq_integral_mul_le {k p g : ℝ → ℝ} (hk : ∀ z, 0 ≤ k z) (hp : ∀ z, 0 < p z)
    (h1 : Integrable fun z => k z * p z) (h2 : Integrable fun z => k z * g z)
    (h3 : Integrable fun z => k z * (g z ^ 2 / p z)) (hC : 0 < ∫ z, k z * p z) :
    (∫ z, k z * g z) ^ 2 ≤ (∫ z, k z * p z) * ∫ z, k z * (g z ^ 2 / p z) :=
  MeasureHelpers.sq_integral_mul_le hk hp h1 h2 h3 hC

section Fisher

variable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- For a probability `ρ` and `v, t > 0`, the relative Fisher integrand of `ρ_t` against the
Gaussian heat flow `N(0, v + t)` is `G_t² / p_t` with `G_t = gaussRelFlux ρ v t`. -/
theorem fisherIntegrand_gaussianReal {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (y : ℝ) :
    fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity (gaussianReal 0 v.toNNReal))
        (heatFlowD1 ρ) (heatFlowD1 (gaussianReal 0 v.toNNReal)) t y
      = gaussRelFlux ρ v t y ^ 2 / heatFlowDensity ρ t y := by
  have hP := (heatFlowDensity_pos ρ ht y).ne'
  have hq := (heatDensity_pos (show 0 < v + t by linarith) y).ne'
  have hvt : v + t ≠ 0 := by linarith
  unfold fisherIntegrand relScore gaussRelFlux
  rw [heatFlowDensity_gaussianReal hv ht, heatFlowD1_gaussianReal hv ht]
  unfold heatDensityD1
  field_simp
  ring

/-- `y ↦ gaussRelFlux ρ v t y` is continuous for `t > 0`. -/
theorem continuous_gaussRelFlux {v t : ℝ} (ht : 0 < t) : Continuous (gaussRelFlux ρ v t) :=
  (continuous_heatFlowD1 ρ ht).add
    ((continuous_id.div_const _).mul (continuous_heatFlowDensity ρ ht))

/-- **Fisher information decay along the heat flow, Gaussian target.** For a probability `ρ`,
`π = N(0, v)` (`v > 0`), `t, a > 0` and integrable relative Fisher integrand at time `t`:
`I(ρ_{t+a}‖π_{t+a}) ≤ ((v + t) / (v + t + a))² · I(ρ_t‖π_t)` (`I = heatFisher`). -/
theorem heatFisher_gaussianReal_le {v t a : ℝ} (hv : 0 < v) (ht : 0 < t) (ha : 0 < a)
    (hint : Integrable (fisherIntegrand (heatFlowDensity ρ)
      (heatFlowDensity (gaussianReal 0 v.toNNReal)) (heatFlowD1 ρ)
      (heatFlowD1 (gaussianReal 0 v.toNNReal)) t)) :
    heatFisher ρ (gaussianReal 0 v.toNNReal) (t + a)
      ≤ ((v + t) / (v + t + a)) ^ 2 * heatFisher ρ (gaussianReal 0 v.toNNReal) t := by
  set F : ℝ → ℝ := fun z => gaussRelFlux ρ v t z ^ 2 / heatFlowDensity ρ t z with hF
  set c := (v + t) / (v + t + a) with hc
  have hFeq : fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity (gaussianReal 0 v.toNNReal))
      (heatFlowD1 ρ) (heatFlowD1 (gaussianReal 0 v.toNNReal)) t = F :=
    funext fun y => fisherIntegrand_gaussianReal ρ hv ht y
  rw [hFeq] at hint
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    div_nonneg (sq_nonneg _) (heatFlowDensity_pos ρ ht z).le
  have hFc : Continuous F := ((continuous_gaussRelFlux ρ ht).pow 2).div
    (continuous_heatFlowDensity ρ ht) fun z => (heatFlowDensity_pos ρ ht z).ne'
  have hPta : ∀ y, 0 < heatFlowDensity ρ (t + a) y :=
    heatFlowDensity_pos ρ (by linarith)
  -- pointwise bound
  have hpt : ∀ y, gaussRelFlux ρ v (t + a) y ^ 2 / heatFlowDensity ρ (t + a) y
      ≤ c ^ 2 * ∫ z, heatDensity a (y - z) * F z := by
    intro y
    have hk : ∀ z, 0 ≤ heatDensity a (y - z) := fun z => (heatDensity_pos ha _).le
    have h1 : Integrable fun z => heatDensity a (y - z) * heatFlowDensity ρ t z :=
      (integrable_heatFlowDensity ρ ht).bdd_mul (c := (Real.sqrt (2 * Real.pi * a))⁻¹)
        ((continuous_heatDensity a).comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (hk z)]; exact heatDensity_le ha _)
    have h3 : Integrable fun z => heatDensity a (y - z) * F z :=
      hint.bdd_mul (c := (Real.sqrt (2 * Real.pi * a))⁻¹)
        ((continuous_heatDensity a).comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (hk z)]; exact heatDensity_le ha _)
    have h13 : Integrable fun z => (heatDensity a (y - z) * heatFlowDensity ρ t z
        + heatDensity a (y - z) * F z) / 2 := (h1.add h3).div_const 2
    have h2 : Integrable fun z => heatDensity a (y - z) * gaussRelFlux ρ v t z := by
      refine h13.mono
        (((continuous_heatDensity a).comp (by fun_prop)).mul
          (continuous_gaussRelFlux ρ ht)).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      have hp := heatFlowDensity_pos ρ ht z
      have hamgm : |gaussRelFlux ρ v t z| ≤ (heatFlowDensity ρ t z + F z) / 2 := by
        rw [hF]
        simp only
        rw [abs_le]
        have e : gaussRelFlux ρ v t z ^ 2 / heatFlowDensity ρ t z * heatFlowDensity ρ t z
            = gaussRelFlux ρ v t z ^ 2 := div_mul_cancel₀ _ hp.ne'
        constructor <;> nlinarith [sq_nonneg (gaussRelFlux ρ v t z - heatFlowDensity ρ t z),
          sq_nonneg (gaussRelFlux ρ v t z + heatFlowDensity ρ t z)]
      have hF0z := hF0 z
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (div_nonneg (add_nonneg
        (mul_nonneg (hk z) hp.le) (mul_nonneg (hk z) hF0z)) two_pos.le), abs_mul,
        abs_of_nonneg (hk z)]
      calc heatDensity a (y - z) * |gaussRelFlux ρ v t z|
          ≤ heatDensity a (y - z) * ((heatFlowDensity ρ t z + F z) / 2) :=
            mul_le_mul_of_nonneg_left hamgm (hk z)
        _ = _ := by ring
    have hC : ∫ z, heatDensity a (y - z) * heatFlowDensity ρ t z
        = heatFlowDensity ρ (t + a) y := by
      rw [(heatFlow_semigroup ρ ht ha).1 y]; congr 1; funext z; ring
    have hCS := sq_integral_mul_le hk (heatFlowDensity_pos ρ ht) h1 h2 h3
      (by rw [hC]; exact hPta y)
    rw [hC, integral_heatDensity_mul_gaussRelFlux ρ hv ht ha y] at hCS
    have hca : (v + t + a) / (v + t) * c = 1 := by
      rw [hc]; field_simp
    rw [div_le_iff₀ (hPta y)]
    calc gaussRelFlux ρ v (t + a) y ^ 2
        = c ^ 2 * ((v + t + a) / (v + t) * gaussRelFlux ρ v (t + a) y) ^ 2 := by
          rw [mul_pow, ← mul_assoc, ← mul_pow, mul_comm c, hca, one_pow, one_mul]
      _ ≤ c ^ 2 * (heatFlowDensity ρ (t + a) y * ∫ z, heatDensity a (y - z) * F z) :=
          mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = _ := by ring
  -- integrate in `y`
  have hHm : AEStronglyMeasurable (fun q : ℝ × ℝ => heatDensity a (q.1 - q.2) * F q.2)
      (volume.prod volume) :=
    (((continuous_heatDensity a).comp (continuous_fst.sub continuous_snd)).mul
      (hFc.comp continuous_snd)).aestronglyMeasurable
  have hH : Integrable (fun q : ℝ × ℝ => heatDensity a (q.1 - q.2) * F q.2)
      (volume.prod volume) := by
    refine (integrable_prod_iff' hHm).2 ⟨Eventually.of_forall fun z => by
      simpa only using (integrable_heatDensity_sub ha z).mul_const (F z), ?_⟩
    refine hint.congr (Eventually.of_forall fun z => ?_)
    simp only
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatDensity_pos ha _), abs_of_nonneg (hF0 z)]
    rw [integral_mul_const, integral_heatDensity_sub ha, one_mul]
  have hswap := integral_integral_swap (f := fun y z => heatDensity a (y - z) * F z) hH
  have hinner : ∫ z, ∫ y, heatDensity a (y - z) * F z = ∫ z, F z := by
    congr 1; funext z
    rw [integral_mul_const, integral_heatDensity_sub ha, one_mul]
  unfold heatFisher
  rw [hFeq]
  have hFeq' : fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity (gaussianReal 0 v.toNNReal))
      (heatFlowD1 ρ) (heatFlowD1 (gaussianReal 0 v.toNNReal)) (t + a)
      = fun y => gaussRelFlux ρ v (t + a) y ^ 2 / heatFlowDensity ρ (t + a) y :=
    funext fun y => fisherIntegrand_gaussianReal ρ hv (by linarith) y
  rw [hFeq']
  calc ∫ y, gaussRelFlux ρ v (t + a) y ^ 2 / heatFlowDensity ρ (t + a) y
      ≤ ∫ y, c ^ 2 * ∫ z, heatDensity a (y - z) * F z :=
        integral_mono_of_nonneg (Eventually.of_forall fun y =>
          div_nonneg (sq_nonneg _) (hPta y).le) (hH.integral_prod_left.const_mul _)
          (Eventually.of_forall hpt)
    _ = c ^ 2 * ∫ z, F z := by rw [integral_const_mul, hswap, hinner]

end Fisher

/-! ### Vanishing of the heat-flow KL at large times -/

/-- If `ρ` and `π` have finite second moments, then `(x, u) ↦ (x - u)²` is integrable under
`ρ ⊗ π`. -/
theorem integrable_sub_sq_prod {ρ π : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] (hρ : Integrable (fun x => x ^ 2) ρ)
    (hπ : Integrable (fun x => x ^ 2) π) :
    Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (ρ.prod π) := by
  refine (((hρ.comp_fst π).const_mul 2).add ((hπ.comp_snd ρ).const_mul 2)).mono'
    (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1 - q.2) ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (q.1 + q.2)]

/-- **Large-time KL bound along the heat flow.** For probability measures `ρ, π` on `ℝ` with
`(x, u) ↦ (x - u)²` integrable under `ρ ⊗ π` and `T > 0`:
`KL(ρ_T‖π_T) ≤ (∫ (x - u)² d(ρ ⊗ π)) / (2T)`. Proof: `ρ_T`, `π_T` are the images of `ρ ⊗ π`
under the kernels `(x, u) ↦ N(x, T)`, `(x, u) ↦ N(u, T)`; apply the KL chain rule
(`klDiv_comp_comp_le`) and `KL(N(x,T)‖N(u,T)) = (x - u)² / (2T)`. -/
theorem heatKL_le_div_two_mul (ρ π : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] (hint : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (ρ.prod π))
    {T : ℝ} (hT : 0 < T) :
    heatKL ρ π T ≤ (∫ q, (q.1 - q.2) ^ 2 ∂(ρ.prod π)) / (2 * T) := by
  set κ := FormalizeSampling.OU.heatKernel T.toNNReal
  set Q : Kernel (ℝ × ℝ) ℝ := Kernel.prodMkRight ℝ κ
  set P : Kernel (ℝ × ℝ) ℝ := Kernel.prodMkLeft ℝ κ
  have hQ : Q ∘ₘ (ρ.prod π) = κ ∘ₘ ρ := by
    have : Q = κ ∘ₖ Kernel.deterministic Prod.fst measurable_fst :=
      (Kernel.comp_deterministic_eq_comap κ measurable_fst).symm
    rw [this, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, Measure.map_fst_prod]
    simp
  have hP : P ∘ₘ (ρ.prod π) = κ ∘ₘ π := by
    have : P = κ ∘ₖ Kernel.deterministic Prod.snd measurable_snd :=
      (Kernel.comp_deterministic_eq_comap κ measurable_snd).symm
    rw [this, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, Measure.map_snd_prod]
    simp
  have hT' : T.toNNReal ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hT
  have hkl : ∀ q : ℝ × ℝ, klDiv (Q q) (P q) = ENNReal.ofReal ((q.1 - q.2) ^ 2 / (2 * T)) := by
    intro q
    rw [Kernel.prodMkRight_apply, Kernel.prodMkLeft_apply, FormalizeSampling.OU.heatKernel_apply,
      FormalizeSampling.OU.heatKernel_apply,
      FormalizeSampling.GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ hT',
      Real.coe_toNNReal _ hT.le]
  have h := FormalizeSampling.KL.klDiv_comp_comp_le (ρ.prod π) (ρ.prod π) Q P
  rw [hQ, hP, klDiv_self, zero_add] at h
  simp_rw [hkl] at h
  have hint' : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (2 * T)) (ρ.prod π) :=
    hint.div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (Eventually.of_forall fun q => by positivity)] at h
  calc heatKL ρ π T ≤ (ENNReal.ofReal (∫ q, (q.1 - q.2) ^ 2 / (2 * T) ∂(ρ.prod π))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = _ := by
        rw [ENNReal.toReal_ofReal (integral_nonneg fun q => by positivity), integral_div]

/-! ### Finiteness of KL along a regular heat flow -/

/-- The relative Fisher information along the heat flow is nonnegative for `t > 0`. -/
theorem heatFisher_nonneg (ρ π : Measure ℝ) [IsProbabilityMeasure ρ] {t : ℝ} (ht : 0 < t) :
    0 ≤ heatFisher ρ π t :=
  integral_nonneg fun y => mul_nonneg (heatFlowDensity_pos ρ ht y).le (sq_nonneg _)

/-- `N(0, v)` has a finite second moment. -/
theorem integrable_sq_gaussianReal (v : ℝ) :
    Integrable (fun x => x ^ 2) (gaussianReal 0 v.toNNReal) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := v.toNNReal) 2).integrable_sq
  simpa using this

/-- **KL is finite along a regular heat flow.** For probability measures `ρ, π` on `ℝ` with
`HeatFlowRegular ρ π s` and `t ∈ s`, `KL(ρ_t‖π_t) = KL(heatKernel t ∘ₘ ρ‖heatKernel t ∘ₘ π) ≠ ∞`
(the integrability field `integrable_kl` gives a finite density integral). So the real number
`heatKL ρ π t = KL(ρ_t‖π_t).toReal` is the actual divergence, not the junk value of `∞`. -/
theorem klDiv_heatKernel_comp_ne_top_of_regular {ρ π : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {s : Set ℝ} (hreg : HeatFlowRegular ρ π s) {t : ℝ} (hts : t ∈ s) :
    klDiv (FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ ρ)
      (FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ π) ≠ ⊤ := by
  have ht : 0 < t := hreg.subset_Ioi hts
  have := isProbabilityMeasure_withDensity_heatFlowDensity ρ ht
  have := isProbabilityMeasure_withDensity_heatFlowDensity π ht
  rw [heatKernel_comp_eq_withDensity ρ ht, heatKernel_comp_eq_withDensity π ht]
  exact (FormalizeSampling.DeterministicStep.klDiv_withDensity_real
    (continuous_heatFlowDensity ρ ht).measurable (continuous_heatFlowDensity π ht).measurable
    (fun y => (heatFlowDensity_pos ρ ht y).le) (heatFlowDensity_pos π ht)
    (hreg.integrable_kl t hts)).1

/-- **KL to the smoothed Gaussian target is finite.** For a probability measure `ρ` on `ℝ`,
`v, t > 0` and `HeatFlowRegular ρ N(0, v) (Ioi 0)` (no moment assumption),
`KL(ρ_t‖N(0, v + t)) ≠ ∞` where `ρ_t = heatKernel t ∘ₘ ρ`. With a finite second moment instead
of `HeatFlowRegular`, see `HeatFlowRegularity.klDiv_heatKernel_comp_ne_top_of_moment`. -/
theorem klDiv_heatKernel_comp_gaussianReal_ne_top (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {v : ℝ} (hv : 0 < v) (hreg : HeatFlowRegular ρ (gaussianReal 0 v.toNNReal) (Ioi 0)) {t : ℝ}
    (ht : 0 < t) :
    klDiv (FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ ρ)
      (gaussianReal 0 (v + t).toNNReal) ≠ ⊤ := by
  have h := klDiv_heatKernel_comp_ne_top_of_regular hreg (show t ∈ Ioi 0 from ht)
  have hb : FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ gaussianReal 0 v.toNNReal =
      gaussianReal 0 (v + t).toNNReal := by
    rw [Real.toNNReal_add hv.le ht.le, ← FormalizeSampling.OU.bind_heat]
    rfl
  rwa [hb] at h

end FormalizeSampling.GaussianLSI
