module

public import FormalizeSampling.Identities.DensityStein
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# DT-1: descent lemma for one deterministic transport step (dimension one)

Registry ID: **DT-1** (`docs/theorem_registry.md`). Status: **Verified** (no named unproved
hypothesis; all hypotheses are regularity / integrability assumptions, satisfied e.g. by a
Gaussian current law `ρ`, a Gaussian target `π` and an affine velocity `v`).

## Setting

* Target `π = e^{-U}/Z` on `ℝ` (`gibbsDensity U Z`), with `Z > 0`, `U` twice differentiable
  and `U'' ≤ L` (for the descent bound).
* Current law `ρ = p dx` with `p > 0` a Lebesgue density (measurable, integrable).
* Velocity `v : ℝ → ℝ` differentiable with `|v'| ≤ Lv`, step `η ≥ 0` with `η Lv ≤ 1/2`.
* Deterministic step `T = id + η v` (`step η v`), Jacobian `T' = 1 + η v'` (`stepJac η v`),
  so `1/2 ≤ T' ≤ 3/2`.

## Results

1. `strictMono_step`, `surjective_step`, `bijective_step`: `T` is a strictly increasing
   bijection of `ℝ`; `measurable_stepInv`: its inverse `T⁻¹` (`stepInv`) is measurable.
2. `map_withDensity_step`: **push-forward density**, `T#(p dx) = q dy` with
   `q(T x) = p(x)/T'(x)` (`pushDensity η v p`, `pushDensity_step`).
3. `integral_pushDensity_klIntegrand`: **entropy identity**
   `∫ q log(q/π) = ∫ p log(p/π) - ∫ p log T' + ∫ p (U∘T - U)`.
4. Scalar inequalities: `sub_sq_le_log_one_add` (`t - t² ≤ log(1+t)` for `|t| ≤ 1/2`) and
   `le_quadratic_of_deriv2_le` (`U(y) ≤ U(x) + U'(x)(y-x) + L(y-x)²/2` when `U'' ≤ L`).
5. `integral_pushDensity_klIntegrand_le` (**DT-1, density level**):
   `∫ q log(q/π) ≤ ∫ p log(p/π) - η ∫ p (v' - U' v) + η² ∫ p (v'² + (L/2) v²)`.
6. `klDiv_map_step_le` (**DT-1, Mathlib `klDiv`**): with `ρ = p dx`, `π = e^{-U}/Z dx`
   probability measures, `KL(T#ρ ‖ π) < ∞` and
   `KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (v' - U' v) + η² ∫ p (v'² + (L/2) v²)`
   (KL direction: the pushed law in the first slot, the target in the second; real values via
   `ENNReal.toReal`).
7. `integral_pushDensity_klIntegrand_le_stein`: under the 1D density Stein identity (ID-2), the
   first-order term is `η ∫ v (log(p/π))' p` (the FL-1 rate), i.e.
   `∫ q log(q/π) ≤ ∫ p log(p/π) + η ∫ v ((log p)' + U') p + η² ∫ p (v'² + (L/2) v²)`.

## NOT proved here

* Only dimension one here. The `d`-dimensional versions are in `Flow/DeterministicStepPi.lean`
  / `Flow/DeterministicStepGeneral.lean`.
* No closed-form choice of `v` here. The ideal velocity `v = -(log(p/π))'` is treated in
  `Flow/IdealVelocityStep.lean`. The moment forms are in `Flow/DeterministicStepMoments.lean`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FormalizeSampling.DeterministicStep

/-! ### Definitions -/

/-- The deterministic transport step `T(x) = x + η v(x)` of step size `η` along the velocity
field `v : ℝ → ℝ`. -/
def step (η : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ := x + η * v x

/-- The Jacobian `T'(x) = 1 + η v'(x)` of the step `T = id + η v` (with Mathlib's `deriv`; it
is the derivative of `T` whenever `v` is differentiable, `hasDerivAt_step`). -/
noncomputable def stepJac (η : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ := 1 + η * deriv v x

/-- The inverse `T⁻¹` of the step, defined as `Function.invFun (step η v)`. It is a two-sided
inverse when `T` is bijective (`bijective_step`, under `|v'| ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`). -/
noncomputable def stepInv (η : ℝ) (v : ℝ → ℝ) : ℝ → ℝ := Function.invFun (step η v)

/-- The push-forward density `q(y) = p(T⁻¹ y) / T'(T⁻¹ y)` of `p dx` under `T = id + η v`.
It is the Lebesgue density of `T#(p dx)` under the hypotheses of `map_withDensity_step`. -/
noncomputable def pushDensity (η : ℝ) (v : ℝ → ℝ) (p : ℝ → ℝ) (y : ℝ) : ℝ :=
  p (stepInv η v y) / stepJac η v (stepInv η v y)

/-- The Gibbs density `π(x) = e^{-U(x)} / Z` of the potential `U` with normalising constant `Z`
(it is a probability density iff `Z = ∫ e^{-U}`; positivity holds for every `Z > 0`). -/
noncomputable def gibbsDensity (U : ℝ → ℝ) (Z : ℝ) (x : ℝ) : ℝ := Real.exp (-U x) / Z

/-! ### Scalar inequalities -/

/-- **Logarithm lower bound.** For `|t| ≤ 1/2`, `t - t² ≤ log(1 + t)`. -/
theorem sub_sq_le_log_one_add {t : ℝ} (ht : |t| ≤ 1 / 2) : t - t ^ 2 ≤ Real.log (1 + t) := by
  obtain ⟨htl, htu⟩ := abs_le.1 ht
  rcases le_or_gt 0 t with h0 | h0
  · have h1 : 0 < 1 + t := by linarith
    have h2 := Real.one_sub_inv_le_log_of_pos h1
    have h3 : t - t ^ 2 ≤ 1 - (1 + t)⁻¹ := by
      rw [show 1 - (1 + t)⁻¹ = t / (1 + t) by field_simp; ring, le_div_iff₀ h1]
      nlinarith [pow_nonneg h0 3]
    linarith
  · -- mean value theorem for `g s = log(1+s) - s + s²` on `[t, 0]`
    have hderiv : ∀ s ∈ Ioo t 0, HasDerivAt (fun s => Real.log (1 + s) - s + s ^ 2)
        ((1 + s)⁻¹ - 1 + 2 * s) s := by
      intro s hs
      have hs1 : 1 + s ≠ 0 := by linarith [hs.1]
      have h := ((((hasDerivAt_id' s).const_add 1).log hs1).sub (hasDerivAt_id' s)).add
        (hasDerivAt_pow 2 s)
      convert h using 1
      norm_num [one_div]
    have hcont : ContinuousOn (fun s => Real.log (1 + s) - s + s ^ 2) (Icc t 0) := by
      refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id) (continuousOn_id.pow 2)
      refine ContinuousOn.log (continuousOn_const.add continuousOn_id) fun s hs => ?_
      have := hs.1
      linarith
    obtain ⟨c, hc, hcg⟩ := exists_hasDerivAt_eq_slope _ _ h0 hcont hderiv
    have hc1 : 0 < 1 + c := by linarith [hc.1]
    have hgc : (1 + c)⁻¹ - 1 + 2 * c ≤ 0 := by
      have : (1 + c)⁻¹ ≤ 1 - 2 * c := by
        rw [inv_le_iff_one_le_mul₀ hc1]
        nlinarith [hc.1, hc.2]
      linarith
    simp only [add_zero, Real.log_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at hcg
    rw [eq_div_iff (by linarith)] at hcg
    nlinarith

/-- **Quadratic upper bound from `U'' ≤ L`.** If `U : ℝ → ℝ` is differentiable, `U'` is
differentiable and `U''(z) ≤ L` for every `z`, then for all `x y`,
`U(y) ≤ U(x) + U'(x)(y - x) + (L/2)(y - x)²`. -/
theorem le_quadratic_of_deriv2_le {U : ℝ → ℝ} {L : ℝ} (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (deriv U)) (hU'' : ∀ z, deriv (deriv U) z ≤ L) (x y : ℝ) :
    U y ≤ U x + deriv U x * (y - x) + L / 2 * (y - x) ^ 2 := by
  set f : ℝ → ℝ := fun z => U z - L / 2 * z ^ 2 with hf
  set fd : ℝ → ℝ := fun z => deriv U z - L * z with hfd
  have hfd_deriv : ∀ z, HasDerivAt fd (deriv (deriv U) z - L) z := by
    intro z
    have := (hU' z).hasDerivAt.sub ((hasDerivAt_id' z).const_mul L)
    convert this using 1
    ring
  have hf_deriv : ∀ z, HasDerivAt f (fd z) z := by
    intro z
    have := (hU z).hasDerivAt.sub ((hasDerivAt_pow 2 z).const_mul (L / 2))
    convert this using 1
    simp only [hfd]
    push_cast
    ring
  have hanti : Antitone fd := by
    refine antitone_of_deriv_nonpos (fun z => (hfd_deriv z).differentiableAt) fun z => ?_
    rw [(hfd_deriv z).deriv]
    linarith [hU'' z]
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun z =>
    (hf_deriv z).continuousAt
  have key : f y - f x ≤ fd x * (y - x) := by
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f fd hxy hfc.continuousOn
        fun z _ => hf_deriv z
      rw [eq_div_iff (by linarith)] at hcs
      rw [← hcs]
      exact mul_le_mul_of_nonneg_right (hanti hc.1.le) (by linarith)
    · subst hxy; simp
    · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f fd hxy hfc.continuousOn
        fun z _ => hf_deriv z
      rw [eq_div_iff (by linarith)] at hcs
      have : fd x * (x - y) ≤ fd c * (x - y) :=
        mul_le_mul_of_nonneg_right (hanti hc.2.le) (by linarith)
      nlinarith
  simp only [hf, hfd] at key
  nlinarith

/-! ### The step map -/

section Step

variable {η Lv : ℝ} {v : ℝ → ℝ}

/-- Derivative of the step: if `v` is differentiable, `T = id + η v` has derivative
`T'(x) = 1 + η v'(x)` at every `x`. -/
theorem hasDerivAt_step (hv : Differentiable ℝ v) (x : ℝ) :
    HasDerivAt (step η v) (stepJac η v x) x := by
  have := (hasDerivAt_id' x).add ((hv x).hasDerivAt.const_mul η)
  convert this using 1
  · funext y
    rfl
  · rfl

/-- If `|v'| ≤ Lv`, `η ≥ 0` and `η Lv ≤ 1/2`, then `|η v'(x)| ≤ 1/2` for every `x`. -/
theorem abs_mul_deriv_le (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (x : ℝ) : |η * deriv v x| ≤ 1 / 2 := by
  rw [abs_mul, abs_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left (hv' x) hη).trans hηL

/-- Jacobian bounds: if `|v'| ≤ Lv`, `η ≥ 0` and `η Lv ≤ 1/2`, then
`1/2 ≤ T'(x) = 1 + η v'(x) ≤ 3/2` for every `x`. -/
theorem stepJac_mem (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (x : ℝ) : 1 / 2 ≤ stepJac η v x ∧ stepJac η v x ≤ 3 / 2 := by
  have h := abs_le.1 (abs_mul_deriv_le hv' hη hηL x)
  exact ⟨by unfold stepJac; linarith [h.1], by unfold stepJac; linarith [h.2]⟩

/-- Positivity of the Jacobian, `T'(x) > 0`, under `|v'| ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`. -/
theorem stepJac_pos (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (x : ℝ) : 0 < stepJac η v x := by
  linarith [(stepJac_mem hv' hη hηL x).1]

/-- The step is continuous when `v` is differentiable. -/
theorem continuous_step (hv : Differentiable ℝ v) : Continuous (step η v) :=
  continuous_id.add (continuous_const.mul hv.continuous)

/-- **(1) Monotonicity.** If `v` is differentiable with `|v'| ≤ Lv`, `η ≥ 0` and
`η Lv ≤ 1/2`, then `T = id + η v` is strictly increasing. -/
theorem strictMono_step (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : StrictMono (step η v) :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_step hv x).deriv]
    exact stepJac_pos hv' hη hηL x

/-- `x ↦ T(x) - x/2` is monotone under the hypotheses of `strictMono_step` (since
`T' ≥ 1/2`); this gives the growth `T(x) ≥ T(0) + x/2` for `x ≥ 0` used for surjectivity. -/
private lemma monotone_step_sub_half (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Monotone fun x => step η v x - x / 2 := by
  have hd : ∀ x, HasDerivAt (fun x => step η v x - x / 2) (stepJac η v x - 1 / 2) x :=
    fun x => by
      have := (hasDerivAt_step (η := η) hv x).sub ((hasDerivAt_id' x).div_const 2)
      convert this using 1
  refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv]
  linarith [(stepJac_mem hv' hη hηL x).1]

/-- **(1) Surjectivity.** Under the hypotheses of `strictMono_step`, `T = id + η v` maps `ℝ`
onto `ℝ`. -/
theorem surjective_step (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Function.Surjective (step η v) := by
  intro y
  have hm := monotone_step_sub_half hv hv' hη hηL
  set r := |y - step η v 0|
  have hr : 0 ≤ r := abs_nonneg _
  have hle := le_abs_self (y - step η v 0)
  have hle' := neg_abs_le (y - step η v 0)
  refine mem_range_of_exists_le_of_exists_ge (continuous_step hv) ⟨-2 * r, ?_⟩ ⟨2 * r, ?_⟩
  · have := hm (show -2 * r ≤ 0 by linarith)
    simp only at this
    linarith
  · have := hm (show 0 ≤ 2 * r by linarith)
    simp only at this
    linarith

/-- **(1) Bijectivity.** Under the hypotheses of `strictMono_step`, `T = id + η v` is a
bijection of `ℝ`. -/
theorem bijective_step (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Function.Bijective (step η v) :=
  ⟨(strictMono_step hv hv' hη hηL).injective, surjective_step hv hv' hη hηL⟩

/-- `T⁻¹ (T x) = x` under the hypotheses of `strictMono_step`. -/
theorem stepInv_step (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (x : ℝ) : stepInv η v (step η v x) = x :=
  Function.leftInverse_invFun (strictMono_step hv hv' hη hηL).injective x

/-- `T (T⁻¹ y) = y` under the hypotheses of `strictMono_step`. -/
theorem step_stepInv (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (y : ℝ) : step η v (stepInv η v y) = y :=
  Function.rightInverse_invFun (surjective_step hv hv' hη hηL) y

/-- The inverse step `T⁻¹` is monotone, hence measurable, under the hypotheses of
`strictMono_step`. -/
theorem measurable_stepInv (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Measurable (stepInv η v) := by
  have hmono : Monotone (stepInv η v) := by
    intro a b hab
    rw [← (strictMono_step hv hv' hη hηL).le_iff_le, step_stepInv hv hv' hη hηL,
      step_stepInv hv hv' hη hηL]
    exact hab
  exact hmono.measurable

/-- **(2) Push-forward density, pointwise.** Under the hypotheses of `strictMono_step`,
`q(T x) = p(x) / T'(x)` for every `p` and `x`, where `q = pushDensity η v p`. -/
theorem pushDensity_step (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (p : ℝ → ℝ) (x : ℝ) :
    pushDensity η v p (step η v x) = p x / stepJac η v x := by
  simp only [pushDensity, stepInv_step hv hv' hη hηL]

/-- Measurability of the push-forward density: if `p` is measurable, so is `q`, under the
hypotheses of `strictMono_step`. -/
theorem measurable_pushDensity (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) {p : ℝ → ℝ} (hp : Measurable p) :
    Measurable (pushDensity η v p) := by
  have hi := measurable_stepInv hv hv' hη hηL
  exact (hp.comp hi).div
    ((measurable_const.add (measurable_const.mul (measurable_deriv v))).comp hi)

/-- **Change of variables along the step.** Under the hypotheses of `strictMono_step`, for every
`g : ℝ → ℝ`, `∫ g(y) dy = ∫ T'(x) g(T x) dx` (no integrability needed: both sides vanish
together otherwise). -/
theorem integral_eq_integral_stepJac_mul (hv : Differentiable ℝ v)
    (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (g : ℝ → ℝ) :
    ∫ y, g y = ∫ x, stepJac η v x * g (step η v x) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_step (η := η) hv x).hasDerivWithinAt)
    (strictMono_step hv hv' hη hηL).injective.injOn g
  rw [image_univ, (surjective_step hv hv' hη hηL).range_eq] at h
  simp only [Measure.restrict_univ] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [abs_of_pos (stepJac_pos hv' hη hηL x)]

/-- **Integrability along the step.** Under the hypotheses of `strictMono_step`, `g` is
Lebesgue integrable iff `x ↦ T'(x) g(T x)` is. -/
theorem integrable_iff_integrable_stepJac_mul (hv : Differentiable ℝ v)
    (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (g : ℝ → ℝ) :
    Integrable g ↔ Integrable fun x => stepJac η v x * g (step η v x) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_step (η := η) hv x).hasDerivWithinAt)
    (strictMono_step hv hv' hη hηL).injective.injOn g
  rw [image_univ, (surjective_step hv hv' hη hηL).range_eq] at h
  simp only [integrableOn_univ] at h
  rw [h]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp [abs_of_pos (stepJac_pos hv' hη hηL x)]

/-- **(2) Push-forward of the law.** Let `v` be differentiable with `|v'| ≤ Lv`, `η ≥ 0`,
`η Lv ≤ 1/2`, and `p : ℝ → ℝ` arbitrary (negative values are truncated by `ofReal` on both
sides, so the statement is meaningful for `p ≥ 0`). Then the image of `ρ = p dx` under
`T = id + η v` is `T#ρ = q dy` with `q = pushDensity η v p`, i.e. `q(T x) = p(x)/T'(x)`. -/
theorem map_withDensity_step (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (p : ℝ → ℝ) :
    (volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η v) =
      volume.withDensity fun y => ENNReal.ofReal (pushDensity η v p y) := by
  have hTm : Measurable (step η v) := (continuous_step hv).measurable
  ext s hs
  rw [Measure.map_apply hTm hs, withDensity_apply _ (hTm hs), withDensity_apply _ hs]
  conv_rhs => rw [← image_preimage_eq s (surjective_step hv hv' hη hηL)]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul (hTm hs)
    (fun x _ => (hasDerivAt_step (η := η) hv x).hasDerivWithinAt)
    (strictMono_step hv hv' hη hηL).injective.injOn]
  refine setLIntegral_congr_fun (hTm hs) fun x _ => ?_
  have hJ := stepJac_pos hv' hη hηL x
  rw [pushDensity_step hv hv' hη hηL, abs_of_pos hJ, ← ENNReal.ofReal_mul hJ.le]
  congr 1
  field_simp

end Step

/-! ### Entropy identity and descent inequality -/

section Descent

variable {η Lv L Z : ℝ} {v U p : ℝ → ℝ}

/-- Pointwise entropy identity: for `p(x) > 0`, `T'(x) > 0` and `Z > 0`,
`log(p/(T' π(T x))) = log(p/π) - log T' + (U(T x) - U(x))` with `π = e^{-U}/Z`. -/
theorem log_identity {px j Ux UTx Z : ℝ} (hpx : 0 < px) (hj : 0 < j) (hZ : 0 < Z) :
    Real.log (px / j / (Real.exp (-UTx) / Z)) =
      Real.log (px / (Real.exp (-Ux) / Z)) - Real.log j + (UTx - Ux) := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_div hpx.ne' hj.ne',
    Real.log_div (by positivity) (by positivity), Real.log_div hpx.ne' (by positivity),
    Real.log_div (by positivity) hZ.ne', Real.log_exp, Real.log_exp]
  ring

/-- `|log T'| ≤ 1` since `T' ∈ [1/2, 3/2]`. -/
private lemma abs_log_stepJac_le (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (x : ℝ) : |Real.log (stepJac η v x)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := stepJac_mem hv' hη hηL x
  have hpos : 0 < stepJac η v x := by linarith
  have hu := Real.log_le_sub_one_of_pos hpos
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (stepJac η v x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- `p log T'` is integrable for integrable `p` (since `|log T'| ≤ 1`). -/
private lemma integrable_mul_log_stepJac (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (hp_int : Integrable p) :
    Integrable fun x => p x * Real.log (stepJac η v x) := by
  refine hp_int.mul_bdd (c := 1) ?_ (Eventually.of_forall fun x => ?_)
  · exact (Real.measurable_log.comp
      (measurable_const.add (measurable_const.mul (measurable_deriv v)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_log_stepJac_le hv' hη hηL x

/-- `p v'` and `p v'²` are integrable for integrable `p` (since `|v'| ≤ Lv`). -/
theorem integrable_mul_deriv (hv' : ∀ x, |deriv v x| ≤ Lv) (hp_int : Integrable p) :
    Integrable (fun x => p x * deriv v x) ∧ Integrable (fun x => p x * deriv v x ^ 2) := by
  refine ⟨hp_int.mul_bdd (c := Lv) (measurable_deriv v).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hv' x), ?_⟩
  refine hp_int.mul_bdd (c := Lv ^ 2) ((measurable_deriv v).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hv' x) 2

/-- The pulled-back KL integrand `T'(x) · q(T x) log(q(T x)/π(T x))` equals
`p log(p/π) - p log T' + p (U∘T - U)` at every point (for `p > 0`, `Z > 0`, under the
hypotheses of `strictMono_step`). -/
private lemma pullback_klIntegrand (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hp : ∀ x, 0 < p x) (hZ : 0 < Z) (x : ℝ) :
    stepJac η v x * (pushDensity η v p (step η v x) *
        Real.log (pushDensity η v p (step η v x) / gibbsDensity U Z (step η v x))) =
      p x * Real.log (p x / gibbsDensity U Z x) - p x * Real.log (stepJac η v x) +
        p x * (U (step η v x) - U x) := by
  have hJ := stepJac_pos hv' hη hηL x
  rw [pushDensity_step hv hv' hη hηL, gibbsDensity, gibbsDensity,
    log_identity (Ux := U x) (UTx := U (step η v x)) (hp x) hJ hZ]
  field_simp

/-- **(3) Entropy identity (DT-1).** Let `π = e^{-U}/Z` with `Z > 0`; let `p > 0` be Lebesgue
integrable; let `v` be differentiable with `|v'| ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`, and let
`q = pushDensity η v p` be the density of `T#(p dx)`, `T = id + η v`. Assume
`p log(p/π)` and `p (U∘T - U)` are Lebesgue integrable. Then `q log(q/π)` is integrable and
`∫ q log(q/π) = ∫ p log(p/π) - ∫ p log T' + ∫ p (U∘T - U)`, i.e.
`KL(T#ρ ‖ π) = KL(ρ ‖ π) - ∫ p log T' + ∫ p (U∘T - U)` at the density level. -/
theorem integral_pushDensity_klIntegrand (hv : Differentiable ℝ v)
    (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hZ : 0 < Z)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x)) :
    Integrable (fun y => pushDensity η v p y *
        Real.log (pushDensity η v p y / gibbsDensity U Z y)) ∧
      ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) =
        (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
          (∫ x, p x * Real.log (stepJac η v x)) + ∫ x, p x * (U (step η v x) - U x) := by
  have hlog := integrable_mul_log_stepJac hv' hη hηL hp_int
  have hsum := (hKL.sub hlog).add hUT
  have hpb := pullback_klIntegrand (U := U) hv hv' hη hηL hp hZ
  constructor
  · rw [integrable_iff_integrable_stepJac_mul hv hv' hη hηL]
    simp_rw [hpb]
    exact hsum
  · rw [integral_eq_integral_stepJac_mul hv hv' hη hηL]
    simp_rw [hpb]
    have hKL' : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x) -
        p x * Real.log (stepJac η v x) := hKL.sub hlog
    rw [integral_add hKL' hUT, integral_sub hKL hlog]

/-- Pointwise descent inequality behind DT-1: under `|η v'| ≤ 1/2` and `U'' ≤ L`,
`-log T' + (U(T x) - U x) ≤ -η (v' - U' v) + η² (v'² + (L/2) v²)`. -/
private lemma pointwise_descent (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, deriv (deriv U) z ≤ L) (x : ℝ) :
    -Real.log (stepJac η v x) + (U (step η v x) - U x) ≤
      -η * (deriv v x - deriv U x * v x) + η ^ 2 * (deriv v x ^ 2 + L / 2 * v x ^ 2) := by
  have h1 := sub_sq_le_log_one_add (abs_mul_deriv_le hv' hη hηL x)
  have h2 := le_quadratic_of_deriv2_le hU hU' hU'' x (step η v x)
  simp only [stepJac, step, add_sub_cancel_left] at *
  nlinarith [h1, h2]

/-- **DT-1 (density level): deterministic-step descent lemma in dimension one.**
Target `π = e^{-U}/Z` (`Z > 0`) with `U` differentiable, `U'` differentiable and `U'' ≤ L`.
Current density `p > 0`, Lebesgue integrable. Velocity `v` differentiable with `|v'| ≤ Lv`;
step `η ≥ 0` with `η Lv ≤ 1/2`; `T = id + η v`, `q = pushDensity η v p` the density of
`T#(p dx)`. Assume `p log(p/π)`, `p (U∘T - U)`, `p U' v` and `p v²` are Lebesgue integrable.
Then, for KL in the direction (pushed law ‖ target),
`∫ q log(q/π) ≤ ∫ p log(p/π) - η ∫ p (v' - U' v) + η² ∫ p (v'² + (L/2) v²)`. -/
theorem integral_pushDensity_klIntegrand_le (hv : Differentiable ℝ v)
    (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, deriv (deriv U) z ≤ L)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (deriv U x * v x))
    (hv2 : Integrable fun x => p x * v x ^ 2) :
    ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
        η * (∫ x, p x * (deriv v x - deriv U x * v x)) +
        η ^ 2 * ∫ x, p x * (deriv v x ^ 2 + L / 2 * v x ^ 2) := by
  rw [(integral_pushDensity_klIntegrand hv hv' hη hηL hp hp_int hZ hKL hUT).2]
  have hlog := integrable_mul_log_stepJac hv' hη hηL hp_int
  obtain ⟨hdv, hdv2⟩ := integrable_mul_deriv hv' hp_int
  have hA : Integrable fun x => p x * (deriv v x - deriv U x * v x) := by
    simp_rw [mul_sub]; exact hdv.sub hUv
  have hB : Integrable fun x => p x * (deriv v x ^ 2 + L / 2 * v x ^ 2) := by
    simp_rw [mul_add]
    exact hdv2.add ((hv2.const_mul (L / 2)).congr (Eventually.of_forall fun x => by ring))
  have hmono : ∫ x, (-(p x * Real.log (stepJac η v x)) + p x * (U (step η v x) - U x)) ≤
      ∫ x, (-η * (p x * (deriv v x - deriv U x * v x)) +
        η ^ 2 * (p x * (deriv v x ^ 2 + L / 2 * v x ^ 2))) := by
    refine integral_mono (hlog.neg.add hUT) ((hA.const_mul _).add (hB.const_mul _))
      fun x => ?_
    have h := mul_le_mul_of_nonneg_left
      (pointwise_descent hv' hη hηL hU hU' hU'' x) (hp x).le
    simp only
    nlinarith
  have hlog' : Integrable fun x => -(p x * Real.log (stepJac η v x)) := hlog.neg
  have hA' : Integrable fun x => -η * (p x * (deriv v x - deriv U x * v x)) := hA.const_mul _
  have hB' : Integrable fun x => η ^ 2 * (p x * (deriv v x ^ 2 + L / 2 * v x ^ 2)) :=
    hB.const_mul _
  rw [integral_add hlog' hUT, integral_neg, integral_add hA' hB',
    integral_const_mul, integral_const_mul] at hmono
  linarith

/-- **DT-1, Stein form (FL-1 rate).** Under the hypotheses of
`integral_pushDensity_klIntegrand_le`, assume further that `p` is differentiable and that
`v p'` and `v p` are Lebesgue integrable (the 1D density Stein identity ID-2,
`∫ v' p = -∫ v (log p)' p`, then holds). Then
`∫ q log(q/π) ≤ ∫ p log(p/π) + η ∫ v ((log p)' + U') p + η² ∫ p (v'² + (L/2) v²)`;
the first-order term is `η ∫ v (log(p/π))' p` since `(log π)' = -U'`. For the ideal velocity
`v = -(log(p/π))'` (if it satisfies the hypotheses) it equals `-η I(ρ‖π)`, with `I` the
relative Fisher information. -/
theorem integral_pushDensity_klIntegrand_le_stein (hv : Differentiable ℝ v)
    (hv' : ∀ x, |deriv v x| ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hpd : Differentiable ℝ p) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, deriv (deriv U) z ≤ L)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (deriv U x * v x))
    (hv2 : Integrable fun x => p x * v x ^ 2)
    (hvp' : Integrable fun x => v x * deriv p x) (hvp : Integrable fun x => v x * p x) :
    ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) +
        η * (∫ x, v x * (score1 p x + deriv U x) * p x) +
        η ^ 2 * ∫ x, p x * (deriv v x ^ 2 + L / 2 * v x ^ 2) := by
  have h := integral_pushDensity_klIntegrand_le hv hv' hη hηL hp hp_int hZ hU hU' hU''
    hKL hUT hUv hv2
  obtain ⟨hdv, -⟩ := integrable_mul_deriv hv' hp_int
  have hstein := DensityStein.integral_deriv_mul_eq_neg_integral_mul_score1 hp
    (fun x => (hpd x).hasDerivAt) (fun x => (hv x).hasDerivAt)
    (hdv.congr (Eventually.of_forall fun x => mul_comm _ _)) hvp' hvp
  have hscore : Integrable fun x => v x * score1 p x * p x := by
    refine hvp'.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_assoc, DensityStein.score1_mul_eq_of_hasDerivAt (hpd x).hasDerivAt (hp x)]
  have e1 : ∫ x, p x * (deriv v x - deriv U x * v x) =
      (∫ x, deriv v x * p x) - ∫ x, p x * (deriv U x * v x) := by
    have hdv' : Integrable fun x => deriv v x * p x :=
      hdv.congr (Eventually.of_forall fun x => mul_comm _ _)
    rw [← integral_sub hdv' hUv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have e2 : ∫ x, v x * (score1 p x + deriv U x) * p x =
      (∫ x, v x * score1 p x * p x) + ∫ x, p x * (deriv U x * v x) := by
    rw [← integral_add hscore hUv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e1, hstein] at h
  rw [e2]
  linarith

end Descent

/-! ### Mathlib `klDiv` form -/

section KLDiv

variable {η Lv L Z : ℝ} {v U p : ℝ → ℝ}

/-- **DT-1 (Mathlib `klDiv`): deterministic-step descent lemma in dimension one.**
Let `ρ = p dx` and `π = e^{-U}/Z dx` be probability measures on `ℝ` (`Z > 0`), with `p > 0`
measurable and `U` differentiable, `U'` differentiable, `U'' ≤ L`. Let `v` be differentiable
with `|v'| ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`, and `T = id + η v`. Assume `p log(p/π)`,
`p (U∘T - U)`, `p U' v` and `p v²` are Lebesgue integrable. Then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (v' - U' v) + η² ∫ p (v'² + (L/2) v²)`
(`InformationTheory.klDiv`, real values via `ENNReal.toReal`; both KLs are finite). -/
theorem klDiv_map_step_le (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, deriv (deriv U) z ≤ L)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (deriv U x * v x))
    (hv2 : Integrable fun x => p x * v x ^ 2) :
    InformationTheory.klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (InformationTheory.klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (InformationTheory.klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (∫ x, p x * (deriv v x - deriv U x * v x)) +
        η ^ 2 * ∫ x, p x * (deriv v x ^ 2 + L / 2 * v x ^ 2) := by
  -- integrability of `p` from the probability-measure hypothesis
  have hp_int : Integrable p := by
    have h1 : ∫⁻ x, ENNReal.ofReal (p x) = 1 := by
      rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, measure_univ]
    refine ⟨hp_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (hp x).le), h1]
    exact ENNReal.one_lt_top
  have hπ_meas : Measurable (gibbsDensity U Z) :=
    (Real.measurable_exp.comp hU.continuous.measurable.neg).div_const Z
  have hπ_pos : ∀ x, 0 < gibbsDensity U Z x := fun x => div_pos (Real.exp_pos _) hZ
  have hmap := map_withDensity_step hv hv' hη hηL p
  have hq_meas := measurable_pushDensity hv hv' hη hηL hp_meas
  have hq_nonneg : ∀ y, 0 ≤ pushDensity η v p y := fun y =>
    div_nonneg (hp _).le (stepJac_pos hv' hη hηL _).le
  have : IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (pushDensity η v p y)) := by
    rw [← hmap]
    infer_instance
  obtain ⟨hqint, -⟩ := integral_pushDensity_klIntegrand hv hv' hη hηL hp hp_int hZ hKL hUT
  obtain ⟨hne, hq⟩ := klDiv_withDensity_real hq_meas hπ_meas hq_nonneg hπ_pos hqint
  obtain ⟨-, hpKL⟩ := klDiv_withDensity_real hp_meas hπ_meas (fun x => (hp x).le) hπ_pos hKL
  rw [hmap]
  refine ⟨hne, ?_⟩
  rw [hq, hpKL]
  exact integral_pushDensity_klIntegrand_le hv hv' hη hηL hp hp_int hZ hU hU' hU'' hKL hUT
    hUv hv2

end KLDiv

end FormalizeSampling.DeterministicStep
