module

public import FormalizeSampling.Flow.FokkerPlanckExistenceTight

/-!
# Gaussian smoothing and the heat equation for Fokker–Planck uniqueness

Status: **Verified.** Two facts about Gaussian expectations `E f(x + σ Z)`, `Z ∼ N(0, I_d)`
(`stdGauss`), used in the uniqueness proof for the weak Fokker–Planck equation:

* `abs_integral_partialDeriv_comp_le` (**smoothing estimate**): for `φ ∈ C¹_c` with `|φ| ≤ M`
  and `σ > 0`, `|E ∂ᵢφ(x + σ Z)| ≤ M / σ`. By Gaussian integration by parts
  (`WeakFokkerPlanckOU.integral_coord_mul_comp`), `E ∂ᵢφ(x + σ Z) = σ⁻¹ E[Zᵢ φ(x + σ Z)]`, and
  `E|Zᵢ| ≤ 1` (`integral_abs_coord_le_one`).
* `hasDerivWithinAt_integral_sqrt` (**heat equation**): for `φ ∈ C²_c` and `D > 0`,
  `τ ↦ E φ(x + √(2Dτ) Z)` has derivative `D E Δφ(x + √(2Dτ) Z)` within `[0, ∞)` at every
  `τ ≥ 0`. This is `WeakFokkerPlanckOU.weakFokkerPlanck_of_gaussPush` for the initial law
  `δ_x`, drift `0` and `σ_τ = √(2Dτ)`.

## Not proved here

* No smoothing estimate for merely bounded measurable `φ` (the bound is proved for `C¹_c`
  functions only, although the constant involves only `sup |φ|`); no higher-order smoothing.
* The heat equation is proved pointwise in `x`, for `C²_c` data only, and without uniformity
  in `x`; the right derivative at `τ = 0` is the only derivative claimed there.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-- `E|Zᵢ| ≤ 1` for `Z ∼ N(0, I_d)`. -/
theorem integral_abs_coord_le_one (i : Fin d) :
    ∫ z, |z i| ∂(stdGauss (d := d)) ≤ 1 := by
  have hmp := measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i
  have e : ∫ z, |z i| ∂(stdGauss (d := d)) = ∫ u, |u| ∂(gaussianReal 0 1) := by
    unfold stdGauss
    have := integral_map (μ := Measure.pi fun _ : Fin d => gaussianReal 0 1)
      (measurable_pi_apply i).aemeasurable (f := fun u : ℝ => |u|)
      continuous_abs.aestronglyMeasurable
    rw [hmp.map_eq] at this
    exact this.symm
  rw [e]
  have hid : MemLp (fun u : ℝ => u) 2 (gaussianReal 0 1) := by
    have := memLp_id_gaussianReal (μ := 0) (v := 1) 2; simp at this; exact this
  have hsq : Integrable (fun u : ℝ => u ^ 2) (gaussianReal 0 1) := hid.integrable_sq
  have hab : Integrable (fun u : ℝ => |u|) (gaussianReal 0 1) :=
    (hid.integrable one_le_two).abs
  have hb : Integrable (fun u : ℝ => (1 + u ^ 2) / 2) (gaussianReal 0 1) :=
    ((integrable_const 1).add hsq).div_const 2
  have h2 : ∫ u, u ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have := integral_sub_sq_gaussianReal 0 0 1
    simpa using this
  calc ∫ u, |u| ∂(gaussianReal 0 1) ≤ ∫ u, (1 + u ^ 2) / 2 ∂(gaussianReal 0 1) :=
        integral_mono hab hb fun u => by
          nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
    _ = 1 := by
        rw [integral_div, integral_add (integrable_const 1) hsq, h2]
        simp

/-- **Gaussian smoothing estimate (Verified).** For `φ ∈ C¹_c` with `|φ| ≤ M` and `σ > 0`,
`|E ∂ᵢφ(x + σ Z)| ≤ M / σ`, `Z ∼ N(0, I_d)`: by Gaussian integration by parts
`E ∂ᵢφ(x + σ Z) = σ⁻¹ E[Zᵢ φ(x + σ Z)]`, and `E|Zᵢ| ≤ 1`. -/
theorem abs_integral_partialDeriv_comp_le {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) {σ : ℝ} (hσ : 0 < σ)
    (i : Fin d) (x : Fin d → ℝ) :
    |∫ z, partialDeriv i φ (x + σ • z) ∂stdGauss| ≤ M / σ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hibp := integral_coord_mul_comp hφ hφc x hσ.ne' i
  have e : ∫ z, partialDeriv i φ (x + σ • z) ∂stdGauss =
      σ⁻¹ * ∫ z, z i * φ (x + σ • z) ∂stdGauss := by
    rw [hibp, ← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
  rw [e, abs_mul, abs_inv, abs_of_pos hσ, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hσ.le)
  have hint : Integrable (fun z : Fin d → ℝ => |z i| * M) stdGauss :=
    (integrable_coord i).abs.mul_const M
  calc |∫ z, z i * φ (x + σ • z) ∂stdGauss|
      ≤ ∫ z, |z i * φ (x + σ • z)| ∂stdGauss := abs_integral_le_integral_abs
    _ ≤ ∫ z, |z i| * M ∂stdGauss := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hint
          (ae_of_all _ fun z => ?_)
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    _ = (∫ z, |z i| ∂stdGauss) * M := integral_mul_const _ _
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right (integral_abs_coord_le_one i) hM0
    _ = M := one_mul M

/-- **Heat equation, variance parametrisation (Verified).** For `φ ∈ C²_c`, `D > 0`, `τ ≥ 0`
and `x : ℝᵈ`, the map `τ ↦ E φ(x + √(2Dτ) Z)` has derivative `D E Δφ(x + √(2Dτ) Z)` within
`[0, ∞)` at `τ` (`Z ∼ N(0, I_d)`). Obtained from `weakFokkerPlanck_of_gaussPush` with initial
law `δ_x`, drift `0` and `σ_τ = √(2Dτ)`. -/
theorem hasDerivWithinAt_integral_sqrt {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) {D : ℝ} (hD : 0 < D) {τ : ℝ} (hτ : 0 ≤ τ) (x : Fin d → ℝ) :
    HasDerivWithinAt (fun τ => ∫ z, φ (x + Real.sqrt (2 * D * τ) • z) ∂stdGauss)
      (D * ∫ z, laplacian φ (x + Real.sqrt (2 * D * τ) • z) ∂stdGauss) (Ici 0) τ := by
  set σ : ℝ → ℝ := fun t => Real.sqrt (2 * D * t) with hσdef
  set σ' : ℝ → ℝ := fun t => D / Real.sqrt (2 * D * t) with hσ'def
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < 2 * D * t := fun t ht => by
    have := mem_Ioi.1 ht; positivity
  have hσd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt σ (σ' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 2 * D * t) (2 * D) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * D)
    have := h1.sqrt (hpos t ht).ne'
    convert this using 1
    simp only [σ']
    have hs : 0 < Real.sqrt (2 * D * t) := Real.sqrt_pos.2 (hpos t ht)
    field_simp
  have hσ' : ContinuousOn σ' (Ioi 0) := by
    refine continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.mul continuousOn_id)) fun t ht => ?_
    exact (Real.sqrt_pos.2 (hpos t ht)).ne'
  have hσ0 : ∀ t ∈ Ioi (0 : ℝ), σ t ≠ 0 := fun t ht => (Real.sqrt_pos.2 (hpos t ht)).ne'
  have hDσ : ∀ t ∈ Ioi (0 : ℝ), σ t * σ' t + 0 * σ t ^ 2 = D := by
    intro t ht
    have hs : 0 < Real.sqrt (2 * D * t) := Real.sqrt_pos.2 (hpos t ht)
    simp only [σ, σ', zero_mul, add_zero]
    field_simp
  have hσc : ContinuousOn σ (Ici 0) :=
    (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).continuousOn
  have hfp := weakFokkerPlanck_of_gaussPush
    (ρ := fun t => gaussPush (Measure.dirac x) (Real.exp (-0 * t)) (σ t))
    (fun t _ => rfl) hσc hσd hσ' hσ0 hDσ φ ⟨hφ, hφc⟩ τ hτ
  have hrepr : ∀ (ψ : (Fin d → ℝ) → ℝ), Continuous ψ → ∀ t,
      ∫ y, ψ y ∂(gaussPush (Measure.dirac x) (Real.exp (-0 * t)) (σ t)) =
        ∫ z, ψ (x + σ t • z) ∂stdGauss := by
    intro ψ hψ t
    rw [integral_gaussPush hψ, Measure.dirac_prod, integral_map (by fun_prop)
      (f := fun q : (Fin d → ℝ) × (Fin d → ℝ) => ψ (Real.exp (-0 * t) • q.1 + σ t • q.2))
      (by fun_prop : Continuous _).aestronglyMeasurable]
    simp
  have hlap : Continuous (laplacian φ) := continuous_laplacian hφ
  have hgen : Continuous (fun y : Fin d → ℝ =>
      (fun (_ : ℝ) (y : Fin d → ℝ) => -(0 : ℝ) • y) τ y ⬝ᵥ grad φ y + D * laplacian φ y) := by
    have h : Continuous fun y => D * laplacian φ y := continuous_const.mul hlap
    simpa using h
  simp only [hrepr φ hφ.continuous, hrepr _ hgen] at hfp
  convert hfp using 1
  rw [← integral_const_mul]
  congr 1
  funext z
  simp [σ]
end FormalizeSampling.FokkerPlanckUniqueness
