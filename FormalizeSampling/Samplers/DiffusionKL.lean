module

public import FormalizeSampling.Samplers.DiffusionSetup

/-!
# KL to an isotropic Gaussian: the mean-shift (bias–variance) identity

For a probability measure `ν` on `Fin d → ℝ` with integrable coordinates and mean
`m* = meanPi ν`, and every `m : Fin d → ℝ`, `v ≠ 0`:
`KL(ν ‖ N(m, v I)) = KL(ν ‖ N(m*, v I)) + ∑ᵢ (m*ᵢ - mᵢ)² / (2v)`
(Mathlib's `klDiv`, valued in `ℝ≥0∞`; both sides may be `∞`, e.g. when `ν` has no Lebesgue
density). No density, no second moment and no other assumption on `ν`. This is the key step
that splits the per-step error of a Gaussian reverse kernel into a *discretisation* part (KL to
the best Gaussian with the same variance) and a *mean (score) error* part.

## Main results

* `pi_gaussianReal_eq_withDensity_prod`: `N(a, v I)` has Lebesgue density
  `y ↦ ∏ᵢ gaussianPDFReal (aᵢ) v (yᵢ)`.
* `llr_pi_gaussianReal_ae_eq`: for `ν ≪ volume`, the log-likelihood ratio
  `log dν/dN(a, v I)` is `ν`-a.e. `log dν/dλ + ∑ᵢ (log(2πv)/2 + (xᵢ - aᵢ)²/(2v))`.
* `klDiv_pi_gaussianReal_eq_add` (the identity above), and its corollary
  `klDiv_pi_gaussianReal_mean_le` (`KL(ν ‖ N(m*, vI)) ≤ KL(ν ‖ N(m, vI))`: among isotropic
  Gaussians of a fixed variance the mean of `ν` is KL-optimal).

## Not proved here

* The analogous identity for the variance (optimal `v`), which needs a second moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

namespace FormalizeSampling.Diffusion

variable {d : ℕ}

/-- The Lebesgue density of `N(a, v I)`: `gaussPiPDF a v y = ∏ᵢ gaussianPDFReal (aᵢ) v (yᵢ)`. -/
noncomputable def gaussPiPDF (a : Fin d → ℝ) (v : ℝ≥0) (y : Fin d → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal (a i) v (y i)

/-- The isotropic Gaussian density is positive for `v ≠ 0`. -/
theorem gaussPiPDF_pos (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : Fin d → ℝ) :
    0 < gaussPiPDF a v y :=
  Finset.prod_pos fun _ _ => gaussianPDFReal_pos _ _ _ hv

/-- The isotropic Gaussian density is measurable. -/
theorem measurable_gaussPiPDF (a : Fin d → ℝ) (v : ℝ≥0) : Measurable (gaussPiPDF a v) := by
  unfold gaussPiPDF
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal (a i) v).comp (measurable_pi_apply i)

/-- `log` of the isotropic Gaussian density:
`log gaussPiPDF a v y = -∑ᵢ (log(2πv)/2 + (yᵢ - aᵢ)²/(2v))`. -/
theorem log_gaussPiPDF (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : Fin d → ℝ) :
    Real.log (gaussPiPDF a v y) =
      -∑ i, (Real.log (2 * Real.pi * v) / 2 + (y i - a i) ^ 2 / (2 * v)) := by
  rw [gaussPiPDF, Real.log_prod (fun i _ => (gaussianPDFReal_pos _ _ _ hv).ne'),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GaussianFlowVsOU.log_gaussianPDFReal _ hv]
  ring

/-- **Density of the isotropic Gaussian.** For `v ≠ 0`,
`N(a, v I) = ⊗ᵢ N(aᵢ, v) = volume.withDensity (ofReal ∘ gaussPiPDF a v)`. -/
theorem pi_gaussianReal_eq_withDensity_prod (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.pi (fun i => gaussianReal (a i) v) =
      volume.withDensity fun y => ENNReal.ofReal (gaussPiPDF a v y) := by
  have hσ : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h := Tweedie.pi_gaussianReal_eq_withDensity hσ a
  have hv2 : (⟨Real.sqrt v ^ 2, sq_nonneg _⟩ : ℝ≥0) = v := by
    ext; simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  simp only [Tweedie.piGaussKernel, Tweedie.gaussKernel, hv2] at h
  exact h

/-- `N(a, v I)` and Lebesgue measure are mutually absolutely continuous (`v ≠ 0`); here the
direction `volume ≪ N(a, v I)`. -/
theorem volume_ac_pi_gaussianReal (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (volume : Measure (Fin d → ℝ)) ≪ Measure.pi (fun i => gaussianReal (a i) v) := by
  rw [pi_gaussianReal_eq_withDensity_prod a hv]
  exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp
    (measurable_gaussPiPDF a v)).aemeasurable
    (ae_of_all _ fun y => by simpa using gaussPiPDF_pos a hv y)

/-- `N(a, v I) ≪ volume`. -/
theorem pi_gaussianReal_ac_volume (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.pi (fun i => gaussianReal (a i) v) ≪ (volume : Measure (Fin d → ℝ)) := by
  rw [pi_gaussianReal_eq_withDensity_prod a hv]
  exact withDensity_absolutelyContinuous _ _

/-- **Log-likelihood ratio against an isotropic Gaussian.** If `ν` is a probability measure
with `ν ≪ volume` and `v ≠ 0`, then `ν`-almost everywhere
`log dν/dN(a, vI)(x) = log dν/dλ(x) + ∑ᵢ (log(2πv)/2 + (xᵢ - aᵢ)²/(2v))`. -/
theorem llr_pi_gaussianReal_ae_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    llr ν (Measure.pi fun i => gaussianReal (a i) v) =ᵐ[ν] fun x =>
      Real.log (ν.rnDeriv volume x).toReal +
        ∑ i, (Real.log (2 * Real.pi * v) / 2 + (x i - a i) ^ 2 / (2 * v)) := by
  rw [pi_gaussianReal_eq_withDensity_prod a hv]
  have hrn := Measure.rnDeriv_withDensity_right ν volume
    (f := fun y => ENNReal.ofReal (gaussPiPDF a v y))
    (ENNReal.measurable_ofReal.comp (measurable_gaussPiPDF a v)).aemeasurable
    (ae_of_all _ fun y => by simpa using gaussPiPDF_pos a hv y)
    (ae_of_all _ fun y => ENNReal.ofReal_ne_top)
  filter_upwards [hν.ae_le hrn, Measure.rnDeriv_pos hν, hν.ae_le (Measure.rnDeriv_lt_top ν volume)]
    with x hx hpos hlt
  rw [llr_def]
  simp only
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (gaussPiPDF_pos a hv x).le,
    Real.log_mul (inv_ne_zero (gaussPiPDF_pos a hv x).ne')
      (ENNReal.toReal_pos hpos.ne' hlt.ne).ne', Real.log_inv, log_gaussPiPDF a hv]
  ring

/-- The affine function `q(x) = ∑ᵢ (2 xᵢ (m*ᵢ - mᵢ) + mᵢ² - m*ᵢ²)/(2v)`, which is the
difference `∑ᵢ ((xᵢ - mᵢ)² - (xᵢ - m*ᵢ)²)/(2v)` of the two Gaussian log-densities. -/
noncomputable def meanShiftFun (mstar m : Fin d → ℝ) (v : ℝ≥0) (x : Fin d → ℝ) : ℝ :=
  ∑ i, (2 * x i * (mstar i - m i) + m i ^ 2 - mstar i ^ 2) / (2 * v)

/-- `meanShiftFun` is integrable under any finite `ν` with integrable coordinates. -/
theorem integrable_meanShiftFun {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (hν : ∀ i, Integrable (fun x => x i) ν) (mstar m : Fin d → ℝ) (v : ℝ≥0) :
    Integrable (meanShiftFun mstar m v) ν := by
  unfold meanShiftFun
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.div_const ?_ _
  refine Integrable.sub (Integrable.add ?_ (integrable_const _)) (integrable_const _)
  exact ((hν i).const_mul 2).mul_const _

/-- With `m* = meanPi ν`, `∫ meanShiftFun m* m v dν = ∑ᵢ (m*ᵢ - mᵢ)² / (2v)`. -/
theorem integral_meanShiftFun {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ i, Integrable (fun x => x i) ν) (m : Fin d → ℝ) (v : ℝ≥0) :
    ∫ x, meanShiftFun (meanPi ν) m v x ∂ν = (∑ i, (meanPi ν i - m i) ^ 2) / (2 * v) := by
  unfold meanShiftFun
  have hi : ∀ i, Integrable (fun x : Fin d → ℝ =>
      2 * x i * (meanPi ν i - m i) + m i ^ 2 - meanPi ν i ^ 2) ν := fun i =>
    Integrable.sub (Integrable.add (((hν i).const_mul 2).mul_const _)
      (integrable_const _)) (integrable_const _)
  rw [integral_finsetSum _ fun i _ => (hi i).div_const _, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∫ x, 2 * x i * (meanPi ν i - m i) ∂ν = 2 * meanPi ν i * (meanPi ν i - m i) := by
    rw [integral_mul_const, integral_const_mul]; rfl
  rw [integral_div, integral_sub (f := fun x : Fin d → ℝ => 2 * x i * (meanPi ν i - m i) + m i ^ 2)
    (g := fun _ => meanPi ν i ^ 2)
    (((hν i).const_mul 2 |>.mul_const _).add (integrable_const _)) (integrable_const _),
    integral_add (f := fun x : Fin d → ℝ => 2 * x i * (meanPi ν i - m i)) (g := fun _ => m i ^ 2)
      ((hν i).const_mul 2 |>.mul_const _) (integrable_const _), h1]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- **Gaussian mean-shift identity for KL.** Let `ν` be a probability measure on `Fin d → ℝ`
whose coordinates are integrable, with mean `m* = meanPi ν`. For every `m` and every variance
`v ≠ 0`,
`KL(ν ‖ N(m, v I)) = KL(ν ‖ N(m*, v I)) + ∑ᵢ (m*ᵢ - mᵢ)² / (2v)`,
as an identity in `ℝ≥0∞` (both sides are `∞` if `ν` has no Lebesgue density or the
log-likelihood ratio is not integrable). No density or second-moment assumption on `ν`. -/
theorem klDiv_pi_gaussianReal_eq_add (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ i, Integrable (fun x => x i) ν) (m : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv ν (Measure.pi fun i => gaussianReal (m i) v) =
      klDiv ν (Measure.pi fun i => gaussianReal (meanPi ν i) v) +
        ENNReal.ofReal ((∑ i, (meanPi ν i - m i) ^ 2) / (2 * v)) := by
  set mstar := meanPi ν
  by_cases hac : ν ≪ volume
  swap
  · have h1 : ¬ ν ≪ Measure.pi fun i => gaussianReal (m i) v :=
      fun h => hac (h.trans (pi_gaussianReal_ac_volume m hv))
    have h2 : ¬ ν ≪ Measure.pi fun i => gaussianReal (mstar i) v :=
      fun h => hac (h.trans (pi_gaussianReal_ac_volume mstar hv))
    rw [klDiv_of_not_ac h1, klDiv_of_not_ac h2, top_add]
  have hacm : ν ≪ Measure.pi fun i => gaussianReal (m i) v :=
    hac.trans (volume_ac_pi_gaussianReal m hv)
  have hacs : ν ≪ Measure.pi fun i => gaussianReal (mstar i) v :=
    hac.trans (volume_ac_pi_gaussianReal mstar hv)
  have hL : llr ν (Measure.pi fun i => gaussianReal (m i) v) =ᵐ[ν]
      llr ν (Measure.pi fun i => gaussianReal (mstar i) v) + meanShiftFun mstar m v := by
    filter_upwards [llr_pi_gaussianReal_ae_eq ν hac m hv,
      llr_pi_gaussianReal_ae_eq ν hac mstar hv] with x h1 h2
    rw [Pi.add_apply, h1, h2, meanShiftFun, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (2 * (v : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  have hq := integrable_meanShiftFun hν mstar m v
  by_cases hint : Integrable (llr ν (Measure.pi fun i => gaussianReal (mstar i) v)) ν
  · have hintm : Integrable (llr ν (Measure.pi fun i => gaussianReal (m i) v)) ν :=
      (hint.add hq).congr hL.symm
    rw [klDiv_of_ac_of_integrable hacm hintm, klDiv_of_ac_of_integrable hacs hint,
      integral_congr_ae hL, integral_add' hint hq, integral_meanShiftFun hν m v]
    have h0 := integral_llr_add_sub_measure_univ_nonneg hacs hint
    have hq0 : 0 ≤ (∑ i, (mstar i - m i) ^ 2) / (2 * (v : ℝ)) := by positivity
    rw [← ENNReal.ofReal_add h0 hq0]
    congr 1
    simp only [probReal_univ]
    ring
  · have hintm : ¬ Integrable (llr ν (Measure.pi fun i => gaussianReal (m i) v)) ν := by
      intro h
      refine hint ((h.sub hq).congr ?_)
      filter_upwards [hL] with x hx
      rw [Pi.sub_apply, hx, Pi.add_apply, add_sub_cancel_right]
    rw [klDiv_of_not_integrable hintm, klDiv_of_not_integrable hint, top_add]

/-- **The mean is KL-optimal among isotropic Gaussians of fixed variance.** Under the
hypotheses of `klDiv_pi_gaussianReal_eq_add`,
`KL(ν ‖ N(meanPi ν, v I)) ≤ KL(ν ‖ N(m, v I))` for every `m`. -/
theorem klDiv_pi_gaussianReal_mean_le (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ i, Integrable (fun x => x i) ν) (m : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv ν (Measure.pi fun i => gaussianReal (meanPi ν i) v) ≤
      klDiv ν (Measure.pi fun i => gaussianReal (m i) v) := by
  rw [klDiv_pi_gaussianReal_eq_add ν hν m hv]
  exact le_self_add

end FormalizeSampling.Diffusion
