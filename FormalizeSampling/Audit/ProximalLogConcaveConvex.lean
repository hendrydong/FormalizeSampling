module

public import FormalizeSampling.Samplers.ProximalLogConcaveRateConvexPi

/-!
# Statement audit of the `1/k` rate for convex potentials: a non-vacuity witness

This file instantiates `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn` for
the sup-norm potential `fSup x = ‖x‖_∞ = maxᵢ |xᵢ|` on `Fin d → ℝ`, i.e. the target
`π ∝ e^{-‖x‖_∞}`. This potential is convex but not strongly convex, not differentiable, not
quadratic, and for `d ≥ 2` not separable (nor separable plus a quadratic form), so it lies
outside the classes covered by `RGOCouplingPi.hasLipRep_rgoKernelPi_separable` and
`Samplers/RGOCouplingQuadraticPi.lean`. It proves nothing new about the sampler.

All hypotheses are discharged: convexity (`convexOn_fSup`), `∫ e^{-fSup} < ∞`
(`integrable_exp_neg_fSup`, from `t^p e^{-t} ≲ (1 + t)^{-(d + 1)}`), and a finite coupling
`δ_c ⊗ π` of a cold start `ρ 0 = δ_c` with `π`, whose cost is the finite second moment
`secondMoment c = ∫ |c - x|² dπ(x)` (`secondMoment_lt_top`).

## Main results

* `klDiv_iterate_dirac_le`: `KL(ρ (k + 1) ‖ π) ≤ M₂(c) / (2 (k + 1) η)` for `ρ 0 = δ_c`.
* `convex_rate_witness`: for `d ≥ 1`, `KL(ρ 0 ‖ π) = ∞` (so `ρ 0 ≠ π`) while
  `KL(ρ (k + 1) ‖ π) ≤ C / (k + 1)` for an explicit finite `C = M₂(c) / (2η) ≥ 0`.

## Not proved here

* That `fSup` is outside the classes covered by the results cited above is a remark, not a Lean
  statement.
* A closed form for `M₂(c)`, and any lower bound showing the rate is tight.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcaveRatePi
open scoped ENNReal NNReal Nat

namespace FormalizeSampling.Audit.ProximalLogConcaveConvex

variable {d : ℕ}

/-- The sup-norm potential `f x = ‖x‖_∞ = maxᵢ |xᵢ|` on `Fin d → ℝ`. -/
noncomputable def fSup (x : Fin d → ℝ) : ℝ := ‖x‖

/-- `fSup` is convex. -/
theorem convexOn_fSup : ConvexOn ℝ univ (fSup (d := d)) := convexOn_norm convex_univ

/-- `fSup` is continuous. -/
theorem continuous_fSup : Continuous (fSup (d := d)) := continuous_norm

/-- Polynomial against exponential: `t^p e^{-t} ≤ e · m! · (1 + t)^{-(d + 1)}` for `t ≥ 0`,
`m = p + d + 1`. -/
theorem pow_mul_exp_neg_le {t : ℝ} (ht : 0 ≤ t) (p : ℕ) :
    t ^ p * Real.exp (-t)
      ≤ Real.exp 1 * (p + d + 1).factorial * (1 + t) ^ (-((d : ℝ) + 1)) := by
  set m := p + d + 1
  have h1 : 0 < 1 + t := by linarith
  have hm := Real.pow_div_factorial_le_exp _ (le_of_lt h1) m
  rw [div_le_iff₀ (by positivity)] at hm
  have hsplit : (1 + t) ^ p = (1 + t) ^ m * (1 + t) ^ (-((d : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add h1]
    congr 1
    simp only [m]; push_cast; ring
  have he : Real.exp (-t) = Real.exp 1 * Real.exp (-(1 + t)) := by
    rw [← Real.exp_add]; ring_nf
  calc t ^ p * Real.exp (-t) ≤ (1 + t) ^ p * Real.exp (-t) := by
        gcongr; linarith
    _ = Real.exp 1 * ((1 + t) ^ m * Real.exp (-(1 + t))) * (1 + t) ^ (-((d : ℝ) + 1)) := by
        rw [hsplit, he]; ring
    _ ≤ Real.exp 1 * m.factorial * (1 + t) ^ (-((d : ℝ) + 1)) := by
        gcongr
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
        linarith

/-- `x ↦ ‖x‖^p e^{-‖x‖}` is Lebesgue integrable on `Fin d → ℝ`. -/
theorem integrable_pow_norm_mul_exp (p : ℕ) :
    Integrable (fun x : Fin d → ℝ => ‖x‖ ^ p * Real.exp (-‖x‖)) := by
  have hg : Integrable (fun x : Fin d → ℝ =>
      Real.exp 1 * (p + d + 1).factorial * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) :=
    (integrable_one_add_norm (by simp)).const_mul _
  refine hg.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_mul_exp_neg_le (norm_nonneg x) p

/-- `∫ e^{-fSup} < ∞`. -/
theorem integrable_exp_neg_fSup : Integrable fun x : Fin d → ℝ => Real.exp (-fSup x) := by
  simpa [fSup] using integrable_pow_norm_mul_exp (d := d) 0

/-- Coordinatewise bound: `|c - x|² ≤ d (‖c‖_∞ + ‖x‖_∞)²`. -/
theorem sqDist_le (c x : Fin d → ℝ) : sqDist c x ≤ d * (‖c‖ + ‖x‖) ^ 2 := by
  unfold sqDist
  calc ∑ i, (c i - x i) ^ 2 ≤ ∑ _i : Fin d, (‖c‖ + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : |c i - x i| ≤ ‖c‖ + ‖x‖ := (abs_sub _ _).trans (add_le_add
          ((Real.norm_eq_abs (c i)).symm.trans_le (norm_le_pi_norm c i))
          ((Real.norm_eq_abs (x i)).symm.trans_le (norm_le_pi_norm x i)))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = d * (‖c‖ + ‖x‖) ^ 2 := by simp

/-- The second moment of `π = targetPi fSup` around `c`: `M₂(c) = ∫⁻ |c - x|² dπ(x)`. -/
noncomputable def secondMoment (c : Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (sqDist c x) ∂(targetPi (fSup (d := d)))

/-- `x ↦ π-density(x) · |c - x|²` is Lebesgue integrable. -/
theorem integrable_targetDensityPi_mul_sqDist (c : Fin d → ℝ) :
    Integrable fun x => targetDensityPi fSup x * sqDist c x := by
  have hI : Integrable fun x : Fin d → ℝ =>
      d / targetNormalizerPi (fSup (d := d)) * (‖c‖ ^ 2 * (‖x‖ ^ 0 * Real.exp (-‖x‖))
        + 2 * ‖c‖ * (‖x‖ ^ 1 * Real.exp (-‖x‖)) + ‖x‖ ^ 2 * Real.exp (-‖x‖)) :=
    ((((integrable_pow_norm_mul_exp 0).const_mul _).add
      ((integrable_pow_norm_mul_exp 1).const_mul _)).add
      (integrable_pow_norm_mul_exp 2)).const_mul _
  refine hI.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((measurable_targetDensityPi continuous_fSup.measurable).mul
      (continuous_sqDist.comp
        (continuous_const.prodMk continuous_id)).measurable).aestronglyMeasurable
  · have hZ := targetNormalizerPi_pos (integrable_exp_neg_fSup (d := d))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (targetDensityPi_nonneg _)
      (sqDist_nonneg _ _)), targetDensityPi, fSup]
    have h := mul_le_mul_of_nonneg_left (sqDist_le c x)
      (div_nonneg (Real.exp_pos (-‖x‖)).le hZ.le)
    refine h.trans_eq ?_
    field_simp
    ring

/-- The second moment `M₂(c)` is finite. -/
theorem secondMoment_lt_top (c : Fin d → ℝ) : secondMoment c < ∞ := by
  have h1 : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (targetDensityPi fSup x) :=
    ENNReal.measurable_ofReal.comp (measurable_targetDensityPi continuous_fSup.measurable)
  have h2 : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (sqDist c x) :=
    ENNReal.measurable_ofReal.comp
      (continuous_sqDist.comp (continuous_const.prodMk continuous_id)).measurable
  unfold secondMoment targetPi
  rw [lintegral_withDensity_eq_lintegral_mul _ h1 h2]
  refine lt_of_le_of_lt (le_of_eq ?_) (integrable_targetDensityPi_mul_sqDist c).lintegral_lt_top
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (targetDensityPi_nonneg _)]

/-- **The `1/k` rate from a point mass, for the sup-norm potential.** Let `π = targetPi fSup`
(`π ∝ e^{-‖x‖_∞}`), `η > 0`, `ρ 0 = δ_c` and `ρ (k + 1) = proxKernelPi fSup η ∘ₘ ρ k`. Then
for every `k`: `KL(ρ (k + 1) ‖ π) ≤ M₂(c) / (2 (k + 1) η)` with `M₂(c) = ∫ |c - x|² dπ(x)`
(instance of `klDiv_iteratePi_le_div_of_convexOn` with the product coupling `δ_c ⊗ π`). -/
theorem klDiv_iterate_dirac_le (c : Fin d → ℝ) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi fSup η ∘ₘ ρ k)
    (h0 : ρ 0 = Measure.dirac c) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi fSup)
      ≤ ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * secondMoment c := by
  have := isProbabilityMeasure_targetPi (integrable_exp_neg_fSup (d := d))
  have hm : Measurable fun x : Fin d → ℝ => (c, x) := measurable_prodMk_left
  have h₁ : ((targetPi fSup).map fun x : Fin d → ℝ => (c, x)).map Prod.fst = ρ 0 := by
    rw [h0, Measure.map_map measurable_fst hm]
    simp [Function.comp_def, Measure.map_const]
  have h₂ : ((targetPi fSup).map fun x : Fin d → ℝ => (c, x)).map Prod.snd = targetPi fSup := by
    rw [Measure.map_map measurable_snd hm]
    simp [Function.comp_def]
  refine (ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn convexOn_fSup
    integrable_exp_neg_fSup hη ρ hstep _ h₁ h₂ k).trans_eq ?_
  have g1 : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ENNReal.ofReal (sqDist p.1 p.2 / (2 * ((k : ℝ) + 1) * η)) :=
    ENNReal.measurable_ofReal.comp (continuous_sqDist.measurable.div_const _)
  have g2 : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (sqDist c x) :=
    ENNReal.measurable_ofReal.comp
      (continuous_sqDist.comp (continuous_const.prodMk continuous_id)).measurable
  rw [lintegral_map g1 hm, secondMoment, ← lintegral_const_mul _ g2]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **Non-vacuity witness.** For `d ≥ 1`, `c : Fin d → ℝ`, `η > 0` and the proximal sampler
started at `ρ 0 = δ_c` for the merely convex, non-smooth, non-quadratic and (for `d ≥ 2`)
non-separable target `π ∝ e^{-‖x‖_∞}`: the start is cold (`KL(ρ 0 ‖ π) = ∞`, in particular
`ρ 0 ≠ π`), yet there is a finite `C ≥ 0` with `KL(ρ (k + 1) ‖ π) ≤ C / (k + 1)` for every
`k`. -/
theorem convex_rate_witness [NeZero d] (c : Fin d → ℝ) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi fSup η ∘ₘ ρ k)
    (h0 : ρ 0 = Measure.dirac c) :
    klDiv (ρ 0) (targetPi fSup) = ∞ ∧ ρ 0 ≠ targetPi fSup ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
        klDiv (ρ (k + 1)) (targetPi fSup) ≤ ENNReal.ofReal (C / ((k : ℝ) + 1)) := by
  have := isProbabilityMeasure_targetPi (integrable_exp_neg_fSup (d := d))
  have hKL : klDiv (ρ 0) (targetPi fSup) = ∞ := by
    refine klDiv_of_not_ac fun hac => ?_
    have hπ : targetPi (fSup (d := d)) {c} = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_singleton c)
    have := hac hπ
    rw [h0, Measure.dirac_apply_of_mem (mem_singleton c)] at this
    exact one_ne_zero this
  refine ⟨hKL, fun h => by rw [h, klDiv_self] at hKL; exact ENNReal.zero_ne_top hKL,
    (secondMoment c).toReal / (2 * η), by positivity, fun k => ?_⟩
  refine (klDiv_iterate_dirac_le c hη ρ hstep h0 k).trans_eq ?_
  rw [← ENNReal.ofReal_toReal (secondMoment_lt_top c).ne, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  field_simp

end FormalizeSampling.Audit.ProximalLogConcaveConvex
