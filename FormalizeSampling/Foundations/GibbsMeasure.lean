module

public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Gibbs measures, potentials, density comparisons and Gaussian envelopes

Status: **Verified** (elementary facts; no hypotheses beyond those stated).

The Gibbs measure `π ∝ e^{-f}` of a potential `f`, on `ℝ` (`Proximal.target f`, with
normaliser `Proximal.targetNormalizer f = ∫ e^{-f}` and density `Proximal.targetDensity f`) and
on `Fin d → ℝ` (`ProximalPi.targetPi f`), the basic potentials, and the comparison facts used to
control these measures, together with second-moment bounds under scaling. These are the targets
of the proximal sampler and the measures of the log-Sobolev, Bakry–Émery and Holley–Stroock
files. The declarations live in the namespaces `Proximal`, `ProximalPi`, `ProximalSharp`,
`ProximalSharpPi`, `HeatFlowRegularityPerturbed(Pi)`, `ProximalSharpPerturbed(Pi)`,
`ProximalGeneralLSI(Pi)` and `ProximalSharpGaussian(Pi)`. This module imports no sampler and no
heat-flow analysis.

## Main results

* `Proximal.isProbabilityMeasure_target`, `ProximalPi.isProbabilityMeasure_targetPi`: for
  integrable `e^{-f}`, `π ∝ e^{-f}` is a probability measure; `Proximal.target_eq_tilted`:
  `target f` is Mathlib's tilt `volume.tilted (-f)`.
* `ProximalSharp.gaussPotential α x = α x²/2` and `ProximalSharp.target_gaussPotential`:
  `target (gaussPotential α) = N(0, 1/α)` for `α > 0`.
* `ProximalSharpPi.sepPotential g x = ∑ᵢ gᵢ(xᵢ)`, `ProximalSharpPi.targetPi_sepPotential` (the
  target of a separable potential is a product), `ProximalSharpPi.gaussPotentialPi α x = α|x|²/2`
  and `ProximalSharpPi.targetPi_gaussPotentialPi`: `targetPi (gaussPotentialPi α) = N(0, I/α)`.
* `HeatFlowRegularityPerturbed.integrable_exp_neg_add`, `target_add_le_smul_target` (and the
  `Fin d → ℝ` forms in `HeatFlowRegularityPerturbedPi`): a perturbation `W ≥ a` keeps `e^{-f}`
  integrable and gives `target (f₀ + W) ≤ e^{-a} Z₀/Z · target f₀`.
* `ProximalSharpPerturbed.exists_envelope_perturbed`,
  `ProximalSharpPerturbedPi.exists_envelope_perturbedPi`: `π ∝ e^{-α|x|²/2 - W}` with `W ≥ a`
  has a Gaussian upper envelope `π ≤ C₂ • N(0, I/α)`.
* `ProximalSharpGaussian.integrable_sq_map_const_mul`,
  `ProximalSharpGaussianPi.integrable_sum_sq_map_scalePi`: a finite second moment is preserved
  by the scalings `x ↦ c x` and `x ↦ c • x` (`ProximalSharpGaussianPi.scalePi`).
* `ProximalGeneralLSI.exists_sub_mul_norm_le_of_convexOn` (a convex function is bounded below by
  a cone), `measurable_of_convexOn_sub` (a convex perturbation of a continuous function is
  measurable), `exists_envelope_of_lower_bound` and `exists_envelope_of_strongConvex` (if
  `f - α₀ x²/2` is convex, `α₀ > 0`, then `∫ e^{-f} < ∞` and `target f ≤ C₂ • N(0, 2/α₀)`);
  `ProximalGeneralLSIPi.exists_envelope_of_lower_boundPi`, `exists_envelope_of_strongConvexPi`
  on `Fin d → ℝ`.

## Not proved here

* Rates: see `ProximalGeneralLSI(Pi)` (LSI targets with a Gaussian envelope) and
  `ProximalStronglyLogConcave`, `ProximalStronglyLogConcaveGeneralPi` (strongly log-concave
  targets).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-! ### Gibbs measures on `ℝ` -/

namespace FormalizeSampling.Proximal

variable (f : ℝ → ℝ)

/-- The target normaliser `Z = ∫ exp(-f x) dx` (a real number; it is `0` by Mathlib's convention
if `exp ∘ (-f)` is not integrable). -/
noncomputable def targetNormalizer : ℝ := ∫ x, Real.exp (-f x)

/-- The target density `π(x) = exp(-f x) / Z` w.r.t. Lebesgue measure. -/
noncomputable def targetDensity (x : ℝ) : ℝ := Real.exp (-f x) / targetNormalizer f

/-- The target law `π = volume.withDensity (ofReal ∘ targetDensity f)`. -/
noncomputable def target : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (targetDensity f x))

/-- The target is Mathlib's exponential tilt of Lebesgue measure by `-f`:
`target f = volume.tilted (-f)` (`MeasureTheory.Measure.tilted`), i.e. `π ∝ e^{-f} dx`. -/
theorem target_eq_tilted : target f = volume.tilted fun x => -f x := rfl

variable {f}

/-- If `exp ∘ (-f)` is integrable, the target normaliser is positive: `0 < Z`. -/
theorem targetNormalizer_pos (hint : Integrable (fun x => Real.exp (-f x))) :
    0 < targetNormalizer f :=
  integral_exp_pos hint

/-- The target normaliser is nonnegative (no assumptions). -/
theorem targetNormalizer_nonneg : 0 ≤ targetNormalizer f :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- The target density is nonnegative (no assumptions). -/
theorem targetDensity_nonneg (x : ℝ) : 0 ≤ targetDensity f x :=
  div_nonneg (Real.exp_pos _).le targetNormalizer_nonneg

/-- The target density is measurable if `f` is. -/
theorem measurable_targetDensity (hf : Measurable f) : Measurable (targetDensity f) := by
  unfold targetDensity
  fun_prop

/-- If `exp ∘ (-f)` is integrable, the target density integrates to one:
`∫⁻ x, π(x) dx = 1`. -/
theorem lintegral_targetDensity (hint : Integrable (fun x => Real.exp (-f x))) :
    ∫⁻ x, ENNReal.ofReal (targetDensity f x) = 1 := by
  change ∫⁻ x, ENNReal.ofReal (Real.exp (-f x) / targetNormalizer f) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
    (Filter.Eventually.of_forall fun x => targetDensity_nonneg x)]
  rw [integral_div, ← targetNormalizer, div_self (targetNormalizer_pos hint).ne',
    ENNReal.ofReal_one]

/-- If `exp ∘ (-f)` is integrable, the target `π` is a probability measure. -/
theorem isProbabilityMeasure_target (hint : Integrable (fun x => Real.exp (-f x))) :
    IsProbabilityMeasure (target f) :=
  ⟨by rw [target, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_targetDensity hint]⟩

variable (f) in
/-- The target is always a finite measure (if `exp ∘ (-f)` is not integrable, `Z = 0` and the
target is the zero measure). -/
theorem isFiniteMeasure_target : IsFiniteMeasure (target f) := by
  by_cases hint : Integrable (fun x => Real.exp (-f x))
  · have := isProbabilityMeasure_target hint
    infer_instance
  · have hZ : targetNormalizer f = 0 := integral_undef hint
    have : target f = 0 := by
      rw [target]
      simp [targetDensity, hZ]
    rw [this]
    infer_instance

end FormalizeSampling.Proximal

/-! ### Gibbs measures on `Fin d → ℝ` -/

namespace FormalizeSampling.ProximalPi

variable {d : ℕ}

/-- The squared Euclidean distance `|x - y|² = ∑ᵢ (xᵢ - yᵢ)²` on `Fin d → ℝ`. -/
noncomputable def sqDist (x y : Fin d → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

/-- The squared Euclidean distance is nonnegative. -/
theorem sqDist_nonneg (x y : Fin d → ℝ) : 0 ≤ sqDist x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The squared Euclidean distance is continuous (hence measurable) in both arguments. -/
theorem continuous_sqDist : Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => sqDist p.1 p.2) := by
  unfold sqDist
  fun_prop

variable (f : (Fin d → ℝ) → ℝ)

/-- The target normaliser `Z = ∫ exp(-f x) dx` on `Fin d → ℝ` (`0` if not integrable). -/
noncomputable def targetNormalizerPi : ℝ := ∫ x, Real.exp (-f x)

/-- The target density `π(x) = exp(-f x) / Z` w.r.t. Lebesgue measure on `Fin d → ℝ`. -/
noncomputable def targetDensityPi (x : Fin d → ℝ) : ℝ := Real.exp (-f x) / targetNormalizerPi f

/-- The target law `π = volume.withDensity (ofReal ∘ targetDensityPi f)` on `Fin d → ℝ`. -/
noncomputable def targetPi : Measure (Fin d → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (targetDensityPi f x))

/-- The target is Mathlib's exponential tilt of Lebesgue measure on `Fin d → ℝ` by `-f`:
`targetPi f = volume.tilted (-f)` (`MeasureTheory.Measure.tilted`), i.e. `π ∝ e^{-f} dx`. -/
theorem targetPi_eq_tilted : targetPi f = (volume : Measure (Fin d → ℝ)).tilted fun x => -f x :=
  rfl

variable {f}

/-- If `exp ∘ (-f)` is integrable, the target normaliser is positive. -/
theorem targetNormalizerPi_pos (hint : Integrable (fun x => Real.exp (-f x))) :
    0 < targetNormalizerPi f :=
  integral_exp_pos hint

/-- The target normaliser is nonnegative (no assumptions). -/
theorem targetNormalizerPi_nonneg : 0 ≤ targetNormalizerPi f :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- The target density is nonnegative (no assumptions). -/
theorem targetDensityPi_nonneg (x : Fin d → ℝ) : 0 ≤ targetDensityPi f x :=
  div_nonneg (Real.exp_pos _).le targetNormalizerPi_nonneg

/-- The target density is measurable if `f` is. -/
theorem measurable_targetDensityPi (hf : Measurable f) : Measurable (targetDensityPi f) := by
  unfold targetDensityPi
  fun_prop

/-- If `exp ∘ (-f)` is integrable, the target density integrates to one. -/
theorem lintegral_targetDensityPi (hint : Integrable (fun x => Real.exp (-f x))) :
    ∫⁻ x, ENNReal.ofReal (targetDensityPi f x) = 1 := by
  change ∫⁻ x, ENNReal.ofReal (Real.exp (-f x) / targetNormalizerPi f) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
    (Filter.Eventually.of_forall fun x => targetDensityPi_nonneg x)]
  rw [integral_div, ← targetNormalizerPi, div_self (targetNormalizerPi_pos hint).ne',
    ENNReal.ofReal_one]

/-- If `exp ∘ (-f)` is integrable, the target `π` is a probability measure. -/
theorem isProbabilityMeasure_targetPi (hint : Integrable (fun x => Real.exp (-f x))) :
    IsProbabilityMeasure (targetPi f) :=
  ⟨by rw [targetPi, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_targetDensityPi hint]⟩

variable (f) in
/-- The target is always a finite measure (it is `0` if `exp ∘ (-f)` is not integrable). -/
theorem isFiniteMeasure_targetPi : IsFiniteMeasure (targetPi f) := by
  by_cases hint : Integrable (fun x => Real.exp (-f x))
  · have := isProbabilityMeasure_targetPi hint
    infer_instance
  · have hZ : targetNormalizerPi f = 0 := integral_undef hint
    have : targetPi f = 0 := by
      rw [targetPi]
      simp [targetDensityPi, hZ]
    rw [this]
    infer_instance

end FormalizeSampling.ProximalPi

/-! ### The Gaussian potential on `ℝ` -/

namespace FormalizeSampling.ProximalSharp

open FormalizeSampling.Proximal

/-- The Gaussian potential `f_α(x) = α x² / 2`, so `target (gaussPotential α) = N(0, 1/α)` for
`α > 0` (`target_gaussPotential`). -/
noncomputable def gaussPotential (α x : ℝ) : ℝ := α * x ^ 2 / 2

/-- `f_α` is measurable (no assumptions). -/
theorem measurable_gaussPotential (α : ℝ) : Measurable (gaussPotential α) := by
  unfold gaussPotential
  fun_prop

/-- For `α > 0` the variance parameter `(α⁻¹).toNNReal` coerces back to `α⁻¹`. -/
theorem coe_invVar {α : ℝ} (hα : 0 < α) : ((α⁻¹).toNNReal : ℝ) = α⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.2 hα.le)

/-- For `α > 0` the variance parameter `(α⁻¹).toNNReal` is nonzero. -/
theorem invVar_ne_zero {α : ℝ} (hα : 0 < α) : (α⁻¹).toNNReal ≠ 0 := by
  rw [ne_eq, Real.toNNReal_eq_zero, not_le]
  positivity

/-- For `α > 0`: `exp(-α x²/2) = √(2π/α) · N(x; 0, 1/α)` with `N(·; 0, 1/α)` the density
`gaussianPDFReal 0 (α⁻¹).toNNReal`. -/
theorem exp_neg_gaussPotential {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Real.exp (-gaussPotential α x) =
      Real.sqrt (2 * Real.pi * ((α⁻¹).toNNReal : ℝ)) * gaussianPDFReal 0 (α⁻¹).toNNReal x := by
  have hv : 0 < ((α⁻¹).toNNReal : ℝ) := by rw [coe_invVar hα]; positivity
  rw [gaussianPDFReal, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  congr 1
  rw [coe_invVar hα, gaussPotential]
  field_simp
  ring

/-- For `α > 0`, `exp ∘ (-f_α)` is Lebesgue integrable, so `f_α` is an admissible potential for
`Samplers/Proximal.lean`. -/
theorem integrable_exp_neg_gaussPotential {α : ℝ} (hα : 0 < α) :
    Integrable (fun x => Real.exp (-gaussPotential α x)) := by
  simp_rw [exp_neg_gaussPotential hα]
  exact (integrable_gaussianPDFReal 0 _).const_mul _

/-- **The Gaussian target.** For `α > 0`, `target (gaussPotential α) = N(0, 1/α)` (variance
argument `(α⁻¹).toNNReal`). -/
theorem target_gaussPotential {α : ℝ} (hα : 0 < α) :
    target (gaussPotential α) = gaussianReal 0 (α⁻¹).toNNReal := by
  have hv : 0 < ((α⁻¹).toNNReal : ℝ) := by rw [coe_invVar hα]; positivity
  have hd : ∀ x, targetDensity (gaussPotential α) x = gaussianPDFReal 0 (α⁻¹).toNNReal x :=
    MeasureHelpers.div_integral_eq_gaussianPDFReal (invVar_ne_zero hα) (by positivity)
      (exp_neg_gaussPotential hα)
  rw [target, gaussianReal_of_var_ne_zero _ (invVar_ne_zero hα), gaussianPDF_def]
  simp_rw [hd]

end FormalizeSampling.ProximalSharp

/-! ### Separable potentials and the isotropic Gaussian potential on `Fin d → ℝ` -/

namespace FormalizeSampling.ProximalSharpPi

open FormalizeSampling.ProximalPi

variable {d : ℕ}

/-- **Product densities.** For integrable nonnegative `g i : ℝ → ℝ`, the law on `Fin d → ℝ`
with Lebesgue density `x ↦ ∏ᵢ g i (x i)` is the product of the laws with densities `g i`:
`volume.withDensity (ofReal ∘ ∏ᵢ gᵢ) = ⊗ᵢ volume.withDensity (ofReal ∘ gᵢ)`. -/
theorem withDensity_prod_ofReal (g : Fin d → ℝ → ℝ) (hg : ∀ i, Integrable (g i))
    (hnn : ∀ i t, 0 ≤ g i t) :
    volume.withDensity (fun x : Fin d → ℝ => ENNReal.ofReal (∏ i, g i (x i))) =
      Measure.pi fun i => volume.withDensity fun t => ENNReal.ofReal (g i t) := by
  have : ∀ i, IsFiniteMeasure (volume.withDensity fun t => ENNReal.ofReal (g i t)) :=
    fun i => isFiniteMeasure_withDensity_ofReal (hg i).2
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : ∀ y : Fin d → ℝ,
      (univ.pi s).indicator (fun x : Fin d → ℝ => ENNReal.ofReal (∏ i, g i (x i))) y
        = ∏ i, ENNReal.ofReal ((s i).indicator (g i) (y i)) := by
    intro y
    by_cases hy : y ∈ univ.pi s
    · rw [indicator_of_mem hy, ENNReal.ofReal_prod_of_nonneg fun i _ => hnn _ _]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem (hy i (mem_univ i))]
    · rw [indicator_of_notMem hy]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [indicator_of_notMem hi])).symm
  simp_rw [hpt]
  rw [MALA.lintegral_prod_ofReal _ (fun i => (hg i).indicator (hs i))
    (fun i t => indicator_nonneg (fun t _ => hnn i t) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ s i
  · simp [indicator_of_mem ht]
  · simp [indicator_of_notMem ht]

/-- **Normalising a product.** For `h i : ℝ → ℝ`,
`(∏ᵢ hᵢ(xᵢ)) / ∫ ∏ᵢ hᵢ(yᵢ) dy = ∏ᵢ hᵢ(xᵢ) / ∫ hᵢ` (no assumptions; Fubini for products). -/
theorem prod_div_integral_prod (h : Fin d → ℝ → ℝ) (x : Fin d → ℝ) :
    (∏ i, h i (x i)) / (∫ y : Fin d → ℝ, ∏ i, h i (y i)) = ∏ i, h i (x i) / ∫ t, h i t := by
  rw [integral_fintype_prod_volume_eq_prod, Finset.prod_div_distrib]

variable {g : Fin d → ℝ → ℝ}

/-- The separable potential `f(x) = ∑ᵢ gᵢ(xᵢ)` on `Fin d → ℝ`. -/
noncomputable def sepPotential (g : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : ℝ := ∑ i, g i (x i)

/-- A separable potential with measurable summands is measurable. -/
theorem measurable_sepPotential (hg : ∀ i, Measurable (g i)) : Measurable (sepPotential g) :=
  Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)

/-- `exp(-∑ᵢ gᵢ(xᵢ)) = ∏ᵢ exp(-gᵢ(xᵢ))` (no assumptions). -/
theorem exp_neg_sepPotential (g : Fin d → ℝ → ℝ) (x : Fin d → ℝ) :
    Real.exp (-sepPotential g x) = ∏ i, Real.exp (-g i (x i)) := by
  rw [sepPotential, ← Finset.sum_neg_distrib, Real.exp_sum]

/-- If each `exp ∘ (-gᵢ)` is integrable, so is `exp ∘ (-∑ᵢ gᵢ)` on `Fin d → ℝ`. -/
theorem integrable_exp_neg_sepPotential (hint : ∀ i, Integrable (fun t => Real.exp (-g i t))) :
    Integrable (fun x => Real.exp (-sepPotential g x)) := by
  simp_rw [exp_neg_sepPotential]
  have := Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ)) hint
  rwa [← volume_pi] at this

/-- **The target of a separable potential is a product.** If each `exp ∘ (-gᵢ)` is
integrable: `targetPi (sepPotential g) = ⊗ᵢ Proximal.target (g i)`. -/
theorem targetPi_sepPotential (hint : ∀ i, Integrable (fun t => Real.exp (-g i t))) :
    targetPi (sepPotential g) = Measure.pi fun i => Proximal.target (g i) := by
  have hd : ∀ x, targetDensityPi (sepPotential g) x = ∏ i, Proximal.targetDensity (g i) (x i) := by
    intro x
    rw [targetDensityPi, targetNormalizerPi]
    simp_rw [exp_neg_sepPotential]
    exact prod_div_integral_prod (fun i t => Real.exp (-g i t)) x
  rw [targetPi]
  simp_rw [hd]
  exact withDensity_prod_ofReal _ (fun i => (hint i).div_const _)
    (fun i t => Proximal.targetDensity_nonneg t)

open FormalizeSampling.ProximalSharp

/-- The isotropic Gaussian potential `f_α(x) = ∑ᵢ α xᵢ²/2 = α |x|²/2` on `Fin d → ℝ`
(Euclidean norm), the separable potential with summands `ProximalSharp.gaussPotential α`. -/
noncomputable def gaussPotentialPi (α : ℝ) : (Fin d → ℝ) → ℝ :=
  sepPotential fun _ => gaussPotential α

/-- Explicitly, `gaussPotentialPi α x = α (∑ᵢ xᵢ²) / 2`. -/
theorem gaussPotentialPi_apply (α : ℝ) (x : Fin d → ℝ) :
    gaussPotentialPi α x = α * (∑ i, x i ^ 2) / 2 := by
  rw [gaussPotentialPi, sepPotential, Finset.mul_sum, Finset.sum_div]
  rfl

/-- The isotropic Gaussian potential `f_α` is measurable (no assumptions). -/
theorem measurable_gaussPotentialPi (α : ℝ) : Measurable (gaussPotentialPi (d := d) α) :=
  measurable_sepPotential fun _ => measurable_gaussPotential α

/-- For `α > 0`, `exp ∘ (-f_α)` is Lebesgue integrable on `Fin d → ℝ`. -/
theorem integrable_exp_neg_gaussPotentialPi {α : ℝ} (hα : 0 < α) :
    Integrable (fun x => Real.exp (-gaussPotentialPi (d := d) α x)) :=
  integrable_exp_neg_sepPotential fun _ => integrable_exp_neg_gaussPotential hα

/-- **The isotropic Gaussian target.** For `α > 0`, `targetPi f_α = N(0, I/α)`, i.e.
`Measure.pi fun _ => gaussianReal 0 (α⁻¹).toNNReal`. -/
theorem targetPi_gaussPotentialPi {α : ℝ} (hα : 0 < α) :
    targetPi (gaussPotentialPi (d := d) α)
      = Measure.pi fun _ : Fin d => gaussianReal 0 (α⁻¹).toNNReal := by
  rw [gaussPotentialPi, targetPi_sepPotential fun _ => integrable_exp_neg_gaussPotential hα]
  simp_rw [target_gaussPotential hα]

end FormalizeSampling.ProximalSharpPi

/-! ### Bounded-below perturbations -/

namespace FormalizeSampling.HeatFlowRegularityPerturbed

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp

variable {f₀ W : ℝ → ℝ} {a : ℝ}

/-- If `exp(-f₀)` is integrable, `W` is measurable and `W ≥ a`, then `exp(-(f₀ + W))` is
integrable. -/
theorem integrable_exp_neg_add (hf₀ : Measurable f₀) (hint : Integrable (fun x => Real.exp (-f₀ x)))
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) :
    Integrable (fun x => Real.exp (-(f₀ + W) x)) := by
  refine (hint.const_mul (Real.exp (-a))).mono'
    (by fun_prop : Measurable fun x => Real.exp (-(f₀ + W) x)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Pi.add_apply, neg_add, Real.exp_add]
  have h1 := Real.exp_le_exp.2 (show -W x ≤ -a by linarith [ha x])
  have h2 := (Real.exp_pos (-f₀ x)).le
  nlinarith

/-- Upper density comparison: with `Z₀, Z` the normalisers of `f₀, f₀ + W` and `W ≥ a`,
`target (f₀ + W) ≤ e^{-a} Z₀/Z · target f₀`. -/
theorem target_add_le_smul_target (hint : Integrable (fun x => Real.exp (-f₀ x)))
    (hint' : Integrable (fun x => Real.exp (-(f₀ + W) x))) (ha : ∀ x, a ≤ W x) :
    target (f₀ + W)
      ≤ ENNReal.ofReal (Real.exp (-a) * targetNormalizer f₀ / targetNormalizer (f₀ + W)) •
        target f₀ := by
  have hZ0 := targetNormalizer_pos hint
  have hZ := targetNormalizer_pos hint'
  unfold target
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold targetDensity
  have e : Real.exp (-a) * targetNormalizer f₀ / targetNormalizer (f₀ + W)
      * (Real.exp (-f₀ x) / targetNormalizer f₀)
      = Real.exp (-a) * Real.exp (-f₀ x) / targetNormalizer (f₀ + W) := by field_simp
  rw [e, Pi.add_apply, neg_add, Real.exp_add, mul_comm (Real.exp (-a))]
  gcongr
  linarith [ha x]

/-- The potential `α x²/2 + W(x)` (`α > 0`, `W` measurable and bounded below) is admissible:
`exp(-(gaussPotential α + W))` is Lebesgue integrable, so its target is a probability. -/
theorem integrable_exp_neg_gaussPotential_add {α a : ℝ} (hα : 0 < α) {W : ℝ → ℝ}
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) :
    Integrable (fun x => Real.exp (-(gaussPotential α + W) x)) :=
  integrable_exp_neg_add (measurable_gaussPotential α) (integrable_exp_neg_gaussPotential hα)
    hW ha

end FormalizeSampling.HeatFlowRegularityPerturbed

namespace FormalizeSampling.HeatFlowRegularityPerturbedPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi

variable {d : ℕ} {f₀ W : (Fin d → ℝ) → ℝ} {a : ℝ}

/-- If `exp(-f₀)` is integrable, `W` is measurable and `W ≥ a`, then `exp(-(f₀ + W))` is
integrable on `Fin d → ℝ`. -/
theorem integrable_exp_neg_add (hf₀ : Measurable f₀)
    (hint : Integrable (fun x => Real.exp (-f₀ x))) (hW : Measurable W) (ha : ∀ x, a ≤ W x) :
    Integrable (fun x => Real.exp (-(f₀ x + W x))) := by
  refine (hint.const_mul (Real.exp (-a))).mono'
    (by fun_prop : Measurable fun x => Real.exp (-(f₀ x + W x))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_add, Real.exp_add]
  have h1 := Real.exp_le_exp.2 (show -W x ≤ -a by linarith [ha x])
  have h2 := (Real.exp_pos (-f₀ x)).le
  nlinarith

/-- Upper density comparison: with `Z₀, Z` the normalisers of `f₀, f₀ + W` and `W ≥ a`,
`targetPi (f₀ + W) ≤ e^{-a} Z₀/Z · targetPi f₀`. -/
theorem targetPi_add_le_smul_targetPi (hint : Integrable (fun x => Real.exp (-f₀ x)))
    (hint' : Integrable (fun x => Real.exp (-(f₀ x + W x)))) (ha : ∀ x, a ≤ W x) :
    targetPi (fun x => f₀ x + W x)
      ≤ ENNReal.ofReal (Real.exp (-a) * targetNormalizerPi f₀ /
          targetNormalizerPi (fun x => f₀ x + W x)) • targetPi f₀ := by
  have hZ0 := targetNormalizerPi_pos hint
  have hZ := targetNormalizerPi_pos hint'
  unfold targetPi
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold targetDensityPi
  have e : Real.exp (-a) * targetNormalizerPi f₀ / targetNormalizerPi (fun x => f₀ x + W x)
      * (Real.exp (-f₀ x) / targetNormalizerPi f₀)
      = Real.exp (-a) * Real.exp (-f₀ x) / targetNormalizerPi (fun x => f₀ x + W x) := by
    field_simp
  rw [e, neg_add, Real.exp_add, mul_comm (Real.exp (-a))]
  gcongr
  linarith [ha x]

/-- For `α > 0` and `W` measurable and bounded below, `exp(-(α|x|²/2 + W(x)))` is Lebesgue
integrable on `Fin d → ℝ`, so its target is a probability. -/
theorem integrable_exp_neg_gaussPotentialPi_add {α a : ℝ} (hα : 0 < α)
    {W : (Fin d → ℝ) → ℝ} (hW : Measurable W) (ha : ∀ x, a ≤ W x) :
    Integrable (fun x => Real.exp (-(gaussPotentialPi α x + W x))) :=
  integrable_exp_neg_add (measurable_gaussPotentialPi α) (integrable_exp_neg_gaussPotentialPi hα)
    hW ha

end FormalizeSampling.HeatFlowRegularityPerturbedPi

namespace FormalizeSampling.ProximalSharpPerturbed

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
open FormalizeSampling.HeatFlowRegularityPerturbed

variable {α a : ℝ} {W : ℝ → ℝ}

/-- The perturbed Gaussian target has a Gaussian envelope:
`target (f_α + W) ≤ C₂ • N(0, 1/α)` with `C₂ ≥ 0`. -/
theorem exists_envelope_perturbed (hα : 0 < α) (hW : Measurable W) (ha : ∀ x, a ≤ W x) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      target (gaussPotential α + W) ≤ ENNReal.ofReal C₂ • gaussianReal 0 (α⁻¹).toNNReal := by
  have hint := integrable_exp_neg_gaussPotential (α := α) hα
  have hint' := integrable_exp_neg_gaussPotential_add hα hW ha
  refine ⟨_, ?_, (target_add_le_smul_target hint hint' ha).trans_eq (by
    rw [target_gaussPotential hα])⟩
  have := targetNormalizer_pos hint
  have := targetNormalizer_pos hint'
  positivity

end FormalizeSampling.ProximalSharpPerturbed

namespace FormalizeSampling.ProximalSharpPerturbedPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.HeatFlowRegularityPerturbedPi

variable {d : ℕ} {α a : ℝ} {W : (Fin d → ℝ) → ℝ}

/-- The perturbed Gaussian target has a Gaussian envelope:
`targetPi (f_α + W) ≤ C₂ • N(0, I/α)` with `C₂ ≥ 0` (`α > 0`, measurable `W ≥ a`). -/
theorem exists_envelope_perturbedPi (hα : 0 < α) (hW : Measurable W) (ha : ∀ x, a ≤ W x) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ (targetPi fun x => gaussPotentialPi α x + W x)
      ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 (α⁻¹).toNNReal := by
  have hint := integrable_exp_neg_gaussPotentialPi (d := d) hα
  have hint' := integrable_exp_neg_gaussPotentialPi_add hα hW ha
  refine ⟨_, ?_, (targetPi_add_le_smul_targetPi hint hint' ha).trans_eq (by
    rw [targetPi_gaussPotentialPi hα])⟩
  have := targetNormalizerPi_pos hint
  have := targetNormalizerPi_pos hint'
  positivity

end FormalizeSampling.ProximalSharpPerturbedPi

/-! ### Strong convexity gives a Gaussian envelope -/

namespace FormalizeSampling.ProximalGeneralLSI

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
open FormalizeSampling.HeatFlowRegularityPerturbed FormalizeSampling.ProximalSharpPerturbed

variable {f : ℝ → ℝ}

/-- **Convex functions are bounded below by a cone.** On a finite-dimensional real normed
space, a convex `g : E → ℝ` satisfies `c - M ‖x‖ ≤ g x` for all `x`, for some `c` and `M ≥ 0`
(here `c = g 0`, and `M = 1/δ` where `g ≤ g 0 + 1` on the ball of radius `δ`). -/
theorem exists_sub_mul_norm_le_of_convexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → ℝ} (hg : ConvexOn ℝ univ g) :
    ∃ c M : ℝ, 0 ≤ M ∧ ∀ x, c - M * ‖x‖ ≤ g x := by
  have hcont : Continuous g := hg.locallyLipschitz.continuous
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hcont 0 1 one_pos
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  refine ⟨g 0, 1 / δ', by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set s := ‖x‖ with hs
  have hs0 : 0 < s := norm_pos_iff.2 hx
  set u : E := -((δ' / s) • x) with hu
  have hun : ‖u‖ = δ' := by
    rw [hu, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity), ← hs]
    field_simp
  have hgu : g u ≤ g 0 + 1 := by
    have h := hball u (by rw [dist_zero_right, hun]; simp only [hδ']; linarith)
    rw [Real.dist_eq] at h
    linarith [le_abs_self (g u - g 0)]
  set l := δ' / (s + δ') with hl
  have hl0 : 0 < l := by positivity
  have hl1 : 0 < 1 - l := by
    rw [hl, sub_pos, div_lt_one (by positivity)]; linarith
  have hcomb : l • x + (1 - l) • u = 0 := by
    have e : (1 - l) * (δ' / s) = l := by
      rw [hl]; field_simp; ring
    rw [hu, smul_neg, smul_smul, e, add_neg_cancel]
  have hconv := hg.2 (mem_univ x) (mem_univ u) hl0.le hl1.le (by ring)
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
  -- `g 0 ≤ l g x + (1 - l) (g 0 + 1)`, so `g x ≥ g 0 - (1 - l)/l = g 0 - s/δ'`
  have h1 : l * (g 0 - g x) ≤ (1 - l) := by nlinarith
  have e2 : (1 - l) / l = s / δ' := by
    rw [hl]; field_simp; ring
  have h2 : g 0 - g x ≤ (1 - l) / l := by
    rw [le_div_iff₀ hl0]; linarith
  rw [e2] at h2
  have e3 : 1 / δ' * s = s / δ' := by ring
  rw [e3]
  linarith

/-- One-dimensional form: a convex `g : ℝ → ℝ` satisfies `c - M |x| ≤ g x` (`M ≥ 0`). -/
theorem exists_sub_mul_abs_le_of_convexOn {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) :
    ∃ c M : ℝ, 0 ≤ M ∧ ∀ x, c - M * |x| ≤ g x := by
  obtain ⟨c, M, hM, h⟩ := exists_sub_mul_norm_le_of_convexOn hg
  exact ⟨c, M, hM, fun x => by simpa [Real.norm_eq_abs] using h x⟩

/-- **A convex perturbation of a continuous function is continuous.** On a finite-dimensional
real normed space `E`, if `g : E → ℝ` is continuous and `f - g` is convex on all of `E`, then
`f` is continuous (a real-valued convex function on the whole of a finite-dimensional space is
continuous). -/
theorem continuous_of_convexOn_sub_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f g : E → ℝ} (hg : Continuous g)
    (hconv : ConvexOn ℝ univ fun x => f x - g x) : Continuous f :=
  (hconv.locallyLipschitz.continuous.add hg).congr fun x => by simp

/-- **A convex perturbation of a continuous function is measurable.** On a finite-dimensional
real normed space `E` with its Borel σ-algebra, if `g : E → ℝ` is continuous and `f - g` is
convex on all of `E`, then `f` is (Borel) measurable. In particular, a strong-convexity
hypothesis `ConvexOn ℝ univ (f - α‖·‖²/2)` already implies `Measurable f`. -/
theorem measurable_of_convexOn_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f g : E → ℝ}
    (hg : Continuous g) (hconv : ConvexOn ℝ univ fun x => f x - g x) : Measurable f :=
  (continuous_of_convexOn_sub_of_continuous hg hconv).measurable

/-- The one-dimensional Gaussian potential `x ↦ α x²/2` is continuous. -/
theorem continuous_gaussPotential (α : ℝ) : Continuous (gaussPotential α) := by
  unfold gaussPotential
  fun_prop

/-- **Envelope from a quadratic lower bound.** If `f` is measurable and
`a ≤ f x - β x²/2` for all `x` (`β > 0`), then `target f ≤ C₂ • N(0, 1/β)` for some `C₂ ≥ 0`
(and `∫ e^{-f} < ∞`). -/
theorem exists_envelope_of_lower_bound (hf : Measurable f) {β a : ℝ} (hβ : 0 < β)
    (ha : ∀ x, a ≤ f x - gaussPotential β x) :
    Integrable (fun x => Real.exp (-f x)) ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 (β⁻¹).toNNReal := by
  set W : ℝ → ℝ := fun x => f x - gaussPotential β x with hW
  have hWm : Measurable W := hf.sub (measurable_gaussPotential β)
  have hfW : f = gaussPotential β + W := by funext x; simp [hW]
  rw [hfW]
  exact ⟨integrable_exp_neg_gaussPotential_add hβ hWm ha,
    exists_envelope_perturbed hβ hWm ha⟩

/-- **Strong convexity gives a Gaussian envelope.** If `f - α₀ x²/2` is convex on `ℝ`
(`α₀ > 0`), then `∫ e^{-f} < ∞` and `target f ≤ C₂ • N(0, 2/α₀)` for some `C₂ ≥ 0` (precisely
`(α₀/2)⁻¹` is the variance). Measurability of `f` is not assumed: it follows from convexity
(`measurable_of_convexOn_sub`). -/
theorem exists_envelope_of_strongConvex {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotential α₀ x) :
    Integrable (fun x => Real.exp (-f x)) ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      target f ≤ ENNReal.ofReal C₂ • gaussianReal 0 ((α₀ / 2)⁻¹).toNNReal := by
  have hf : Measurable f := measurable_of_convexOn_sub (continuous_gaussPotential α₀) hconv
  obtain ⟨c, M, hM, hcM⟩ := exists_sub_mul_abs_le_of_convexOn hconv
  refine exists_envelope_of_lower_bound hf (β := α₀ / 2) (a := c - M ^ 2 / α₀)
    (by positivity) fun x => ?_
  have h := hcM x
  simp only [gaussPotential] at h ⊢
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  -- `M |x| ≤ α₀ x²/4 + M²/α₀`
  have key : M * |x| ≤ α₀ * x ^ 2 / 4 + M ^ 2 / α₀ := by
    have h0 : 0 ≤ (α₀ * |x| / 2 - M) ^ 2 := sq_nonneg _
    rw [← sub_nonneg]
    have e : α₀ * x ^ 2 / 4 + M ^ 2 / α₀ - M * |x| = (α₀ * |x| / 2 - M) ^ 2 / α₀ := by
      field_simp
      rw [← hx]
      ring
    rw [e]
    positivity
  linarith

end FormalizeSampling.ProximalGeneralLSI

namespace FormalizeSampling.ProximalGeneralLSIPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.HeatFlowRegularityPerturbedPi FormalizeSampling.ProximalSharpPerturbedPi

variable {d : ℕ} {f : (Fin d → ℝ) → ℝ}

/-- The isotropic Gaussian potential `x ↦ α |x|²/2` on `Fin d → ℝ` is continuous. -/
theorem continuous_gaussPotentialPi (α : ℝ) : Continuous (gaussPotentialPi (d := d) α) := by
  have : gaussPotentialPi (d := d) α = fun x => α * (∑ i, x i ^ 2) / 2 :=
    funext (gaussPotentialPi_apply α)
  rw [this]
  fun_prop

/-- **Envelope from a quadratic lower bound.** If `f` is measurable and
`a ≤ f x - β |x|²/2` for all `x` (`β > 0`), then `∫ e^{-f} < ∞` and
`targetPi f ≤ C₂ • N(0, β⁻¹ I)` for some `C₂ ≥ 0`. -/
theorem exists_envelope_of_lower_boundPi (hf : Measurable f) {β a : ℝ} (hβ : 0 < β)
    (ha : ∀ x, a ≤ f x - gaussPotentialPi β x) :
    Integrable (fun x => Real.exp (-f x)) ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      targetPi f ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 (β⁻¹).toNNReal
      := by
  set W : (Fin d → ℝ) → ℝ := fun x => f x - gaussPotentialPi β x with hW
  have hWm : Measurable W := hf.sub (measurable_gaussPotentialPi β)
  have hfW : f = fun x => gaussPotentialPi β x + W x := by funext x; simp [hW]
  rw [hfW]
  exact ⟨integrable_exp_neg_gaussPotentialPi_add hβ hWm ha,
    exists_envelope_perturbedPi hβ hWm ha⟩

/-- **Strong convexity gives a Gaussian envelope.** If `f - α₀ |x|²/2` is convex on
`Fin d → ℝ` (`α₀ > 0`), then `∫ e^{-f} < ∞` and `targetPi f ≤ C₂ • N(0, (α₀/2)⁻¹ I)` for some
`C₂ ≥ 0`. Measurability of `f` is not assumed: it follows from convexity
(`ProximalGeneralLSI.measurable_of_convexOn_sub`). -/
theorem exists_envelope_of_strongConvexPi {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α₀ x) :
    Integrable (fun x => Real.exp (-f x)) ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      targetPi f
        ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 ((α₀ / 2)⁻¹).toNNReal
      := by
  have hf : Measurable f :=
    ProximalGeneralLSI.measurable_of_convexOn_sub (continuous_gaussPotentialPi α₀) hconv
  obtain ⟨c, M, hM, hcM⟩ := ProximalGeneralLSI.exists_sub_mul_norm_le_of_convexOn hconv
  refine exists_envelope_of_lower_boundPi hf (β := α₀ / 2) (a := c - M ^ 2 / α₀)
    (by positivity) fun x => ?_
  have h := hcM x
  rw [gaussPotentialPi_apply] at h ⊢
  set S := ∑ i, x i ^ 2
  have hn := sq_norm_le_sum_sq x
  set n := ‖x‖
  -- `M n ≤ α₀ n²/4 + M²/α₀ ≤ α₀ S/4 + M²/α₀`
  have key : M * n ≤ α₀ * n ^ 2 / 4 + M ^ 2 / α₀ := by
    rw [← sub_nonneg]
    have e : α₀ * n ^ 2 / 4 + M ^ 2 / α₀ - M * n = (α₀ * n / 2 - M) ^ 2 / α₀ := by
      field_simp
      ring
    rw [e]
    positivity
  have h2 : α₀ * n ^ 2 / 4 ≤ α₀ * S / 4 := by
    have := mul_le_mul_of_nonneg_left hn hα₀.le
    linarith
  linarith

end FormalizeSampling.ProximalGeneralLSIPi

/-! ### Second moments under scaling -/

namespace FormalizeSampling.ProximalSharpGaussian

/-- The second moment is preserved by scaling: `∫ (c x)² dρ = c² ∫ x² dρ`. -/
theorem integrable_sq_map_const_mul (ρ : Measure ℝ) (hρ : Integrable (fun x => x ^ 2) ρ)
    (c : ℝ) : Integrable (fun x => x ^ 2) (ρ.map (c * ·)) := by
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def, mul_pow] using hρ.const_mul (c ^ 2)

end FormalizeSampling.ProximalSharpGaussian

namespace FormalizeSampling.ProximalSharpGaussianPi

variable {d : ℕ}

/-- Coordinatewise scaling `x ↦ c • x` on `Fin d → ℝ`. -/
noncomputable def scalePi (c : ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => c * x i

/-- The scaling map is measurable. -/
theorem measurable_scalePi (c : ℝ) : Measurable (scalePi (d := d) c) := by
  unfold scalePi; fun_prop

/-- `x ↦ ∑ᵢ xᵢ²` is continuous. -/
theorem continuous_sum_sq : Continuous fun x : Fin d → ℝ => ∑ i, x i ^ 2 := by
  fun_prop

/-- The second moment is preserved by scaling: `∫ ∑ᵢ (c xᵢ)² dρ = c² ∫ ∑ᵢ xᵢ² dρ`. -/
theorem integrable_sum_sq_map_scalePi (ρ : Measure (Fin d → ℝ))
    (hρ : Integrable (fun x => ∑ i, x i ^ 2) ρ) (c : ℝ) :
    Integrable (fun x => ∑ i, x i ^ 2) (ρ.map (scalePi c)) := by
  rw [integrable_map_measure (continuous_sum_sq (d := d)).aestronglyMeasurable
    (measurable_scalePi c).aemeasurable]
  simpa [Function.comp_def, scalePi, mul_pow, ← Finset.mul_sum] using hρ.const_mul (c ^ 2)

end FormalizeSampling.ProximalSharpGaussianPi
