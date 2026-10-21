module

public import FormalizeSampling.Flow.DiPernaLionsRenormalization

/-!
# DiPerna–Lions uniqueness: cut-offs and an integral Gronwall inequality

Status: **Verified.** Helpers for the DiPerna–Lions uniqueness theorems in every dimension
(`Flow/DiPernaLionsLinearGrowth.lean`, `Flow/DiPernaLionsLp.lean`): smooth cut-offs, the
integral Gronwall inequality and a measurability lemma. The renormalized energy identity
`∫ w_t² χ - ∫ w_0² χ = ∫₀ᵗ ∫ w_s² (v ⬝ᵥ ∇χ - (div v) χ)` for the difference `w = u - u'` of two
bounded solutions is `energy_identity_of_weakContinuityDensity`
(`Flow/DiPernaLionsRenormalization.lean`).

## Main results

* `dlCutoff`: cut-offs `χ_R(x) = χ(R⁻¹ x)` with `|v ⬝ᵥ ∇χ_R| ≤ d V D₁ / R`
  (`exists_abs_dotProduct_grad_dlCutoff_le`).
* `le_mul_exp_of_le_add_mul_integral`: an integral Gronwall inequality.
* `measurable_dotProduct_grad`: `x ↦ v(x) ⬝ᵥ ∇φ(x)` is measurable.

## Not proved here

* The uniqueness theorems themselves: for essentially bounded velocities and for velocities of
  linear growth they are `ae_eq_of_weakContinuityDensity_diPernaLions` and
  `ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth`
  (`Flow/DiPernaLionsLinearGrowth.lean`); for `L^p` densities
  `ae_eq_of_weakContinuityDensity_diPernaLions_Lp` (`Flow/DiPernaLionsLp.lean`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- The fixed smooth cut-off bump on `ℝᵈ`: a `ContDiffBump` centred at `0`, equal to `1` on
`closedBall 0 1` and vanishing outside `ball 0 2`, with values in `[0, 1]`. -/
noncomputable def dlCutoffBump (d : ℕ) : ContDiffBump (0 : Fin d → ℝ) :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cut-off `χ_R(x) = χ(R⁻¹ x)` built from `dlCutoffBump`: smooth, compactly
supported, `0 ≤ χ_R ≤ 1`, `χ_R = 1` on `closedBall 0 R`, `|∇χ_R| = O(1/R)`. -/
noncomputable def dlCutoff (d : ℕ) (R : ℝ) (x : Fin d → ℝ) : ℝ :=
  dlCutoffBump d (R⁻¹ • x)

/-- The cut-off `χ_R` is smooth (Verified). -/
theorem contDiff_dlCutoff (R : ℝ) : ContDiff ℝ ∞ (dlCutoff d R) :=
  (dlCutoffBump d).contDiff.comp (contDiff_const_smul _)

/-- The cut-off `χ_R` has compact support for `R > 0` (Verified). -/
theorem hasCompactSupport_dlCutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (dlCutoff d R) :=
  (dlCutoffBump d).hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

/-- The cut-off is nonnegative (Verified). -/
theorem dlCutoff_nonneg (R : ℝ) (x : Fin d → ℝ) : 0 ≤ dlCutoff d R x :=
  (dlCutoffBump d).nonneg

/-- The cut-off is at most `1` (Verified). -/
theorem dlCutoff_le_one (R : ℝ) (x : Fin d → ℝ) : dlCutoff d R x ≤ 1 :=
  (dlCutoffBump d).le_one

/-- The cut-off equals `1` on `closedBall 0 R` (Verified). -/
theorem dlCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Fin d → ℝ} (hx : ‖x‖ ≤ R) :
    dlCutoff d R x = 1 := by
  refine (dlCutoffBump d).one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR, mul_one]; exact hx

/-- **Gradient bound for the cut-offs (Verified).** There is `D₁ ≥ 0` such that for every
`R > 0`, every vector `y` with `‖y‖ ≤ V` and every `x`, `|y ⬝ᵥ ∇χ_R(x)| ≤ d V D₁ / R`. -/
theorem exists_abs_dotProduct_grad_dlCutoff_le (d : ℕ) : ∃ D₁ : ℝ, 0 ≤ D₁ ∧
    ∀ {R : ℝ}, 0 < R → ∀ {V : ℝ} (y x : Fin d → ℝ), ‖y‖ ≤ V →
      |y ⬝ᵥ grad (dlCutoff d R) x| ≤ d * V * D₁ / R := by
  set χ := dlCutoffBump d
  obtain ⟨D, hD⟩ :=
    ((χ.contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      (χ.hasCompactSupport.fderiv ℝ)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨D, hD0, fun {R} hR {V} y x hy => ?_⟩
  have hV : 0 ≤ V := (norm_nonneg _).trans hy
  have hfd : fderiv ℝ (dlCutoff d R) x =
      (fderiv ℝ χ (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) := by
    have h1 : HasFDerivAt (fun z : Fin d → ℝ => R⁻¹ • z)
        (R⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) x := (hasFDerivAt_id x).const_smul R⁻¹
    exact ((χ.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x h1 |>.fderiv
  have hnorm : ‖fderiv ℝ (dlCutoff d R) x‖ ≤ D * R⁻¹ := by
    rw [hfd]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hD _) ?_ (norm_nonneg _) hD0)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) ContinuousLinearMap.norm_id_le
  have hgi : ∀ i, |grad (dlCutoff d R) x i| ≤ D * R⁻¹ := by
    intro i
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ (dlCutoff d R) x).le_opNorm _).trans ?_
    refine (mul_le_mul hnorm ?_ (norm_nonneg _) (by positivity)).trans (le_of_eq (mul_one _))
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  rw [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |y i * grad (dlCutoff d R) x i| ≤ ∑ _i : Fin d, V * (D * R⁻¹) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul ((norm_le_pi_norm y i).trans hy) (hgi i) (abs_nonneg _) hV
    _ = d * V * D / R := by simp [div_eq_mul_inv]; ring

/-- **Integral Gronwall inequality (Verified).** If `f` is continuous and nonnegative on
`[0, T]`, `a, C ≥ 0`, and `f t ≤ a + C ∫₀ᵗ f` on `[0, T]`, then `f t ≤ a e^{C t}` on `[0, T]`. -/
theorem le_mul_exp_of_le_add_mul_integral {f : ℝ → ℝ} {a C T : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hle : ∀ t ∈ Icc 0 T, f t ≤ a + C * ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Icc 0 T, f t ≤ a * Real.exp (C * t) := by
  set g : ℝ → ℝ := fun s => f (projIcc 0 (max T 0) (le_max_right T 0) s) with hg
  have hTT : Icc (0 : ℝ) T = Icc 0 (max T 0) ∨ T < 0 := by
    rcases le_or_gt 0 T with h | h
    · left; rw [max_eq_left h]
    · right; exact h
  rcases hTT with hT | hT
  swap
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hT)
  have hgc : Continuous g := by
    rw [hT] at hf
    exact hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun s => (projIcc _ _ _ s).2
  have hgf : ∀ s ∈ Icc 0 T, g s = f s := by
    intro s hs
    rw [hT] at hs
    simp only [hg, projIcc_of_mem _ hs]
  have hint : ∀ t ∈ Icc 0 T, ∫ s in (0 : ℝ)..t, f s = ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    exact (hgf s ⟨hs.1, hs.2.trans ht.2⟩).symm
  set Φ : ℝ → ℝ := fun t => a + C * ∫ s in (0 : ℝ)..t, g s with hΦ
  have hΦd : ∀ t, HasDerivAt Φ (C * g t) t := fun t =>
    ((hgc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul C).const_add a
  have hfΦ : ∀ t ∈ Icc 0 T, f t ≤ Φ t := fun t ht => by
    rw [hΦ]; simp only; rw [← hint t ht]; exact hle t ht
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le (f := Φ) (f' := fun t => C * g t)
    (δ := a) (K := C) (ε := 0) (a := 0) (b := T)
    (fun t _ => (hΦd t).continuousAt.continuousWithinAt)
    (fun t _ => (hΦd t).hasDerivWithinAt)
    (by simp [hΦ, abs_of_nonneg ha])
    (fun t ht => by
      have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have h1 := hfΦ t ht'
      have h2 := hf0 t ht'
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (by
        rw [hgf t ht']; exact h2)), abs_of_nonneg (h2.trans h1), hgf t ht', add_zero]
      exact mul_le_mul_of_nonneg_left h1 hC)
  intro t ht
  have := hb t ht
  rw [gronwallBound_ε0, sub_zero] at this
  exact (hfΦ t ht).trans ((le_abs_self _).trans this)

/-- `x ↦ v(x) ⬝ᵥ ∇φ(x)` is measurable for measurable `v` and `C¹` `φ` (Verified). -/
theorem measurable_dotProduct_grad {v : (Fin d → ℝ) → Fin d → ℝ} (hvm : Measurable v)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) : Measurable fun x => v x ⬝ᵥ grad φ x := by
  have hgc : Continuous fun x => grad φ x :=
    continuous_pi fun i => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hvm).mul ((continuous_apply i).comp hgc).measurable

end NoiseScore
end FormalizeSampling
