module

public import FormalizeSampling.Flow.DeterministicStepMoments
public import FormalizeSampling.Flow.DeterministicStepGeneral
public import FormalizeSampling.Flow.IdealVelocityStepPi
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# DT-1 in dimension `d` with integrability from a finite second moment

Status: **Verified** (no named unproved hypothesis).

`d`-dimensional companion of `FormalizeSampling/Flow/DeterministicStepMoments.lean`, on
`Fin d → ℝ` with Lebesgue `volume`. As in `DeterministicStepPi`, `‖·‖` is Mathlib's sup norm,
so `‖Dv‖ ≤ Lv` and `‖D(∇U)‖ ≤ M` are operator-norm bounds `ℓ∞ → ℓ∞`; the second moment is
Euclidean, `∫ (x ⬝ᵥ x) p = ∫ ∑ᵢ xᵢ² p < ∞` (`‖x‖² ≤ x ⬝ᵥ x` is
`FormalizeSampling.norm_sq_le_dotProduct_self`).

## Main results

* `quadGrowth_dotProduct`, `linGrowth_apply` (via `|u ⬝ᵥ w| ≤ d ‖u‖ ‖w‖`,
  `FormalizeSampling.abs_dotProduct_le_norm`).
* `quadGrowth_comp_step_sub`: with the **two-sided** bound `‖D(∇U)‖ ≤ M` (which gives
  `D²U ≤ M` by `IdealVelocityStepPi.fderiv_fderiv_apply_le`, used at `x` and at `T x`) and `v`
  of linear growth, `U∘T - U` has quadratic growth.
* `integrable_of_moment`: `p log(p/π)`, `p (U∘T - U)`, `p ∇U ⬝ᵥ v`, `p ‖v‖²` are integrable
  from `KL(ρ ‖ π) < ∞`, `∫ ‖x‖₂² p < ∞`, `‖Dv‖ ≤ Lv`, `‖D(∇U)‖ ≤ M`.
* `klDiv_map_step_le` (symmetric Jacobian; restates `DeterministicStepPi.klDiv_map_step_le`)
  and `klDiv_map_step_le_general` (no symmetry, constant `13`; restates
  `DeterministicStepGeneral.klDiv_map_step_le`):
  - `p log(p/π) ∈ L¹` is **replaced** by `KL(ρ ‖ π) < ∞`;
  - `p (U∘T - U)`, `p ∇U ⬝ᵥ v`, `p ‖v‖² ∈ L¹` are **eliminated**;
  - **added**: `∫ ‖x‖₂² p < ∞` and `‖D(∇U)‖ ≤ M` (the originals only assume the one-sided
    `D²U(z)(h, h) ≤ L ‖h‖²`, kept for the constant).
* `klDiv_map_step_idealVel_le` (restates `IdealVelocityStepPi.klDiv_map_step_idealVel_le`,
  constant `d (L_U + L_p)²`):
  - `p log(p/π) ∈ L¹` is **replaced** by `KL(ρ ‖ π) < ∞`;
  - `p (U∘T - U)`, the Fisher integrand `‖∇log p + ∇U‖² p`, `vᵢ (∇log p)ᵢ p` and `p vᵢ ∈ L¹`
    (all `i`) are **eliminated** (finite Fisher information follows);
  - **added**: only `∫ ‖x‖₂² p < ∞` (`‖D(∇U)‖ ≤ L_U` is already two-sided).

## NOT proved here

* `DeterministicStepGeneral.klDiv_map_step_le_of_mul_dim_le` is not restated (combine
  `klDiv_map_step_le_general` with `DeterministicStepGeneral.sq_mul_frobSq_jacMat_le`).
* Density-level statements are not restated; finite KL is not derived.
-/

public section

open MeasureTheory Set Filter Matrix InformationTheory
open scoped ENNReal

namespace FormalizeSampling.DeterministicStepMomentsPi

open FormalizeSampling.MeasureHelpers (integrable_of_isProbabilityMeasure)

open DeterministicStepMoments DeterministicStepPi IdealVelocityStepPi

variable {d : ℕ}

/-! ### Growth lemmas on `Fin d → ℝ` -/

/-- A finite Euclidean second moment `∫ ‖x‖₂² p < ∞` (`‖x‖₂² = x ⬝ᵥ x = ∑ᵢ xᵢ²`) gives the
sup-norm moment `∫ ‖x‖² p < ∞` used by `QuadGrowth.integrable_mul`. -/
theorem integrable_norm_sq_mul_of_dotProduct {p : (Fin d → ℝ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp_meas : Measurable p) (hm : Integrable fun x => (x ⬝ᵥ x) * p x) :
    Integrable fun x => ‖x‖ ^ 2 * p x := by
  refine hm.mono' ((continuous_norm.pow 2).aestronglyMeasurable.mul
    hp_meas.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 x), abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (norm_sq_le_dotProduct_self x) (hp0 x)

/-- Dot products of vector fields of linear growth have quadratic growth. -/
theorem quadGrowth_dotProduct {u w : (Fin d → ℝ) → Fin d → ℝ} (hu : LinGrowth u)
    (hw : LinGrowth w) : QuadGrowth fun x => u x ⬝ᵥ w x := by
  have q : QuadGrowth fun x => ‖u x‖ * ‖w x‖ :=
    QuadGrowth.of_le_mul hu hw fun x => by rw [abs_of_nonneg (by positivity)]
  exact (q.const_mul d).mono fun x => abs_dotProduct_le_norm _ _

/-- Coordinates of a vector field of linear growth have linear growth. -/
theorem linGrowth_apply {u : (Fin d → ℝ) → Fin d → ℝ} (hu : LinGrowth u) (i : Fin d) :
    LinGrowth fun x => u x i := by
  obtain ⟨c, hc, h⟩ := hu
  exact ⟨c, hc, fun x => (norm_le_pi_norm (u x) i).trans (h x)⟩

/-- A velocity of linear growth gives a step `T = id + η v` of linear growth. -/
theorem linGrowth_step {η : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} (hv : LinGrowth v) :
    LinGrowth (step η v) :=
  LinGrowth.id.add (hv.const_smul η)

/-- **Quadratic growth of `U∘T - U`, dimension `d`.** If `U`, `DU` are differentiable with the
two-sided Hessian bound `‖D(∇U)‖ ≤ M` (operator norm for the sup norm) and `v` has linear
growth, then `U(T x) - U(x)` has quadratic growth, `T = id + η v`. -/
theorem quadGrowth_comp_step_sub {η M : ℝ} {U : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (fderiv ℝ U)) (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ M)
    (hv : LinGrowth v) : QuadGrowth fun x => U (step η v x) - U x := by
  have hU2 := fderiv_fderiv_apply_le hU hU' hUH
  have hgU : LinGrowth (grad U) := LinGrowth.of_norm_fderiv_le (differentiable_grad hU') hUH
  have hw : LinGrowth fun x => η • v x := hv.const_smul η
  have hg : QuadGrowth fun x => |grad U x ⬝ᵥ η • v x| +
      |grad U (step η v x) ⬝ᵥ η • v x| + M / 2 * (η • v x ⬝ᵥ η • v x) :=
    ((quadGrowth_dotProduct hgU hw).abs.add
      (quadGrowth_dotProduct (hgU.comp (linGrowth_step hv)) hw).abs).add
      ((quadGrowth_dotProduct hw hw).const_mul _)
  refine hg.mono fun x => ?_
  have h1 := le_quadratic_of_fderiv2_le hU hU' hU2 x (step η v x)
  have h2 := le_quadratic_of_fderiv2_le hU hU' hU2 (step η v x) x
  have e1 : step η v x - x = η • v x := by rw [step]; abel
  have e2 : x - step η v x = -(η • v x) := by rw [step]; abel
  rw [e1] at h1
  rw [e2, dotProduct_neg, neg_dotProduct, dotProduct_neg, neg_neg] at h2
  have a1 := neg_abs_le (grad U x ⬝ᵥ η • v x)
  have a2 := le_abs_self (grad U (step η v x) ⬝ᵥ η • v x)
  have a3 := abs_nonneg (grad U x ⬝ᵥ η • v x)
  have a4 := abs_nonneg (grad U (step η v x) ⬝ᵥ η • v x)
  have a5 := le_abs_self (grad U x ⬝ᵥ η • v x)
  have a6 := neg_abs_le (grad U (step η v x) ⬝ᵥ η • v x)
  rw [abs_le]
  constructor <;> nlinarith

/-- Continuity of `U∘T - U` for continuous `U` and differentiable `v`. -/
theorem continuous_comp_step_sub {η : ℝ} {U : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} (hU : Continuous U) (hv : Differentiable ℝ v) :
    Continuous fun x => U (step η v x) - U x :=
  (hU.comp (differentiable_step hv).continuous).sub hU

/-! ### DT-1 in dimension `d` from a finite second moment -/

section Descent

variable {η Lv L M Z : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- The four integrability facts used by the `d`-dimensional DT-1 theorems, derived from a
finite Euclidean second moment, `‖Dv‖ ≤ Lv`, `‖D(∇U)‖ ≤ M` and `KL(ρ ‖ π) < ∞`. -/
theorem integrable_of_moment (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hp : ∀ x, 0 < p x) (hp_meas : Measurable p) (hZ : 0 < Z) (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (fderiv ℝ U)) (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ M)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    (hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞)
    (hm : Integrable fun x => (x ⬝ᵥ x) * p x) :
    (Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x)) ∧
      (Integrable fun x => p x * (U (step η v x) - U x)) ∧
      (Integrable fun x => p x * (grad U x ⬝ᵥ v x)) ∧
      Integrable fun x => p x * (v x ⬝ᵥ v x) := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hp_int : Integrable p := integrable_of_isProbabilityMeasure hp_meas hp0
  have hm' := integrable_norm_sq_mul_of_dotProduct hp0 hp_meas hm
  have hπ_meas : Measurable (gibbsDensity U Z) :=
    (Real.measurable_exp.comp hU.continuous.measurable.neg).div_const Z
  have hvl : LinGrowth v := LinGrowth.of_norm_fderiv_le hv hv'
  have hgd := differentiable_grad hU'
  have hgU : LinGrowth (grad U) := LinGrowth.of_norm_fderiv_le hgd hUH
  refine ⟨integrable_klIntegrand_of_klDiv_ne_top hp_meas hπ_meas hp0
    (fun x => div_pos (Real.exp_pos _) hZ) hKL, ?_, ?_, ?_⟩
  · exact (quadGrowth_comp_step_sub hU hU' hUH hvl).integrable_mul
      (continuous_comp_step_sub hU.continuous hv).aestronglyMeasurable hp0 hp_int hm'
  · exact (quadGrowth_dotProduct hgU hvl).integrable_mul
      (hgd.continuous.dotProduct hv.continuous).aestronglyMeasurable hp0 hp_int hm'
  · exact (quadGrowth_dotProduct hvl hvl).integrable_mul
      (hv.continuous.dotProduct hv.continuous).aestronglyMeasurable hp0 hp_int hm'

/-- **DT-1 (Mathlib `klDiv`), dimension `d`, symmetric Jacobian, moment form.** Same
conclusion as `DeterministicStepPi.klDiv_map_step_le`, with its integrability hypotheses
replaced as follows: `p log(p/π)` integrable is replaced by `KL(ρ ‖ π) < ∞`; `p (U∘T - U)`,
`p ∇U ⬝ᵥ v` and `p ‖v‖²` integrable are **derived** from the finite second moment
`∫ ‖x‖₂² p < ∞` (`‖x‖₂² = x ⬝ᵥ x`) and the extra two-sided Hessian bound `‖D(∇U)‖ ≤ M`
(operator norm for the sup norm; the one-sided `D²U(z)(h, h) ≤ L ‖h‖²` is kept for the
constant of the descent bound). -/
theorem klDiv_map_step_le (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hsym : ∀ x, (jacMat v x).IsSymm)
    (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h))
    (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ M)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞)
    (hm : Integrable fun x => (x ⬝ᵥ x) * p x) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (∫ x, p x * (divergence v x - grad U x ⬝ᵥ v x)) +
        η ^ 2 * ∫ x, p x * (frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  obtain ⟨hKL', hUT, hUv, hv2⟩ :=
    integrable_of_moment (η := η) hv hv' hp hp_meas hZ hU hU' hUH hKL hm
  exact DeterministicStepPi.klDiv_map_step_le hv hv' hη hηL hsym hp hp_meas hZ hU hU' hU''
    hKL' hUT hUv hv2

/-- **DT-1 (Mathlib `klDiv`), dimension `d`, general Jacobian, moment form.** Same conclusion
as `DeterministicStepGeneral.klDiv_map_step_le` (constant `13`, Frobenius hypothesis
`η² ‖Dv‖_F² ≤ 1/4`, no symmetry), with the hypotheses on `p log(p/π)`, `p (U∘T - U)`,
`p ∇U ⬝ᵥ v`, `p ‖v‖²` replaced by `KL(ρ ‖ π) < ∞`, `∫ ‖x‖₂² p < ∞` and the extra two-sided
Hessian bound `‖D(∇U)‖ ≤ M`. -/
theorem klDiv_map_step_le_general (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4)
    (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h))
    (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ M)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞)
    (hm : Integrable fun x => (x ⬝ᵥ x) * p x) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (∫ x, p x * (divergence v x - grad U x ⬝ᵥ v x)) +
        η ^ 2 * ∫ x, p x * (13 * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  obtain ⟨hKL', hUT, hUv, hv2⟩ :=
    integrable_of_moment (η := η) hv hv' hp hp_meas hZ hU hU' hUH hKL hm
  exact DeterministicStepGeneral.klDiv_map_step_le hv hv' hη hηL hF hp hp_meas hZ hU hU' hU''
    hKL' hUT hUv hv2

end Descent

/-! ### The ideal velocity in dimension `d` from a finite second moment -/

section Ideal

variable {η LU Lp Z : ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- **DT-1 for the ideal velocity (Mathlib `klDiv`), dimension `d`, `d`-linear constant, moment
form.** Same conclusion as `IdealVelocityStepPi.klDiv_map_step_idealVel_le`, with its
integrability hypotheses replaced as follows: `p log(p/π)` integrable is replaced by
`KL(ρ ‖ π) < ∞`; the integrability of `p (U∘T - U)`, of the Fisher integrand
`‖∇log p + ∇U‖² p`, of `vᵢ (∇log p)ᵢ p` and of `p vᵢ` (every `i`) is **derived** from the
finite second moment `∫ ‖x‖₂² p < ∞`. No extra Hessian hypothesis is needed: `‖D(∇U)‖ ≤ L_U`
is already two-sided, and `‖D(∇log p)‖ ≤ L_p` makes `∇log p`, hence `v = -(∇U + ∇log p)`, of
linear growth; in particular `I(ρ‖π) < ∞` automatically.

Conclusion: `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η (1 - η L_U / 2) I(ρ‖π) + η² d (L_U + L_p)²`. -/
theorem klDiv_map_step_idealVel_le (hη : 0 ≤ η) (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ LU) (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hpd : Differentiable ℝ p) (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x)))
    (hsH : ∀ z, ‖fderiv ℝ (score p) z‖ ≤ Lp)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞)
    (hm : Integrable fun x => (x ⬝ᵥ x) * p x) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (1 - η * LU / 2) * relFisher U p + η ^ 2 * (d * (LU + Lp) ^ 2) := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hp_int : Integrable p := integrable_of_isProbabilityMeasure hp_meas hp0
  have hm' := integrable_norm_sq_mul_of_dotProduct hp0 hp_meas hm
  have hv := differentiable_idealVel hU' hℓ'
  have hv' := norm_fderiv_idealVel_le hU' hℓ' hUH hsH
  have hs : Differentiable ℝ (score p) := differentiable_grad hℓ'
  have hvl : LinGrowth (idealVel U p) := LinGrowth.of_norm_fderiv_le hv hv'
  have hsl : LinGrowth (score p) := LinGrowth.of_norm_fderiv_le hs hsH
  obtain ⟨hKL', hUT, -, hv2⟩ :=
    integrable_of_moment (η := η) hv hv' hp hp_meas hZ hU hU' hUH hKL hm
  have hF : Integrable fun x =>
      ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x :=
    hv2.congr (Eventually.of_forall fun x => by
      simp only
      rw [idealVel_dotProduct_self, mul_comm])
  have hvs : ∀ i, Integrable fun x => idealVel U p x i * score p x i * p x := fun i =>
    ((QuadGrowth.mul (linGrowth_apply hvl i) (linGrowth_apply hsl i)).integrable_mul
      (((continuous_apply i).comp hv.continuous).mul
        ((continuous_apply i).comp hs.continuous)).aestronglyMeasurable hp0 hp_int hm').congr
      (Eventually.of_forall fun x => mul_comm _ _)
  have hflux : ∀ i, Integrable fun x => p x * idealVel U p x i := fun i =>
    (QuadGrowth.of_linGrowth (linGrowth_apply hvl i)).integrable_mul
      ((continuous_apply i).comp hv.continuous).aestronglyMeasurable hp0 hp_int hm'
  exact IdealVelocityStepPi.klDiv_map_step_idealVel_le hη hηL hZ hU hU' hUH hp hp_meas hpd
    hℓ' hsH hKL' hUT hF hvs hflux

end Ideal

end FormalizeSampling.DeterministicStepMomentsPi
