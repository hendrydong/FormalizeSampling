module

public import FormalizeSampling.Flow.DeterministicStep
public import FormalizeSampling.Foundations.GaussianKL

/-!
# DT-1 for the ideal velocity: a law-dependent step size (dimension one)

The descent lemma DT-1 (`DeterministicStep.klDiv_map_step_le`) for `T = id + η v` assumes
`|v'| ≤ Lv` and `η Lv ≤ 1/2`. For the **ideal velocity**
`v = (log(π/ρ))' = -U' - (log p)'` (target `π = e^{-U}/Z`, current law `ρ = p dx`) the bound
`Lv` depends on the current density `p`. This file settles the question in dimension one.

## Positive result (bounded log-Hessians)

* `idealVel U p = -(U' + (log p)')`, `relFisher U p = ∫ ((log p)' + U')² p`
  (`idealVel_eq_neg_deriv_log`, `relFisher_eq`: these are `-(log(p/π))'` and the relative
  Fisher information `∫ ((log(p/π))')² p`).
* `differentiable_idealVel`, `abs_deriv_idealVel_le`: if `|U''| ≤ L_U` and
  `|(log p)''| ≤ L_p` (`p > 0`, `p` and `p'` differentiable) then `v` is differentiable and
  `|v'| ≤ L_U + L_p`.
* `integral_mul_sub_eq_relFisher`: via the density Stein identity (ID-2) the first-order term
  of DT-1 is the relative Fisher information, `∫ p (v' - U' v) = I(ρ‖π)`.
* `integral_pushDensity_klIntegrand_le_idealVel` (density level, from the Stein form
  `integral_pushDensity_klIntegrand_le_stein`), for `0 ≤ η`, `η (L_U + L_p) ≤ 1/2`:
  `∫ q log(q/π) ≤ ∫ p log(p/π) - η I(ρ‖π) + η² ∫ p (v'² + (L_U/2) v²)`.
* `integral_pushDensity_klIntegrand_le_idealVel'` and `klDiv_map_step_idealVel_le` (Mathlib
  `klDiv`): with `∫ p = 1`,
  `KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η (1 - η L_U / 2) I(ρ‖π) + η² (L_U + L_p)²`.

## Negative result (no uniform step size)

Target `π = N(0, 1)` (`U(x) = x²/2`, `gaussianPDFReal_zero_one_eq_gibbsDensity`), current law
`ρ = N(0, s)`.

* `idealVel_gaussian`: the ideal velocity is `v(x) = (1/s - 1) x`, so
  `Lip(v) = |1/s - 1|` (`deriv_idealVel_gaussian`), which is unbounded as `s → 0`
  (`exists_lipschitz_idealVel_gaussian_gt`).
* `exists_klDiv_map_step_idealVel_gt`: for **every** step `η > 0` there is a variance `s > 0`
  (with `η |1/s - 1| > 1/2`) such that one ideal-velocity step **increases** the KL:
  `KL(N(0, s) ‖ N(0, 1)) < KL(T#N(0, s) ‖ N(0, 1))`, `T = id + η v`. Hence no fixed step
  size gives one-step descent uniformly over current laws; the admissible step must depend on
  `ρ` (through `L_p` in the positive result). For Gaussian laws this step is the forward method
  of Wibisono (2018, arXiv:1802.08089, Example 4), whose covariance recursion
  `Σ⁺ = Σ (I + η (Σ⁻¹ - I))²` gives this KL increase directly.

## NOT proved here

* Only dimension one here. The `d`-dimensional version is `Flow/IdealVelocityStepPi.lean`
  (second-order constant `d (L_U + L_p)²`).
* The integrability hypotheses of the positive result (`p log(p/π)`, `p (U∘T - U)`, the
  Fisher integrand, `v p'`, `v p`) are assumed here. They are derived from a finite second
  moment in `DeterministicStepMoments.klDiv_map_step_idealVel_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped NNReal ENNReal

namespace FormalizeSampling.IdealVelocityStep

open DeterministicStep

/-! ### Definitions -/

/-- The **ideal velocity** `v = -(U' + (log p)')` for target `π = e^{-U}/Z` and current
density `p`; for `p > 0` it is `(log(π/p))' = -(log(p/π))'` (`idealVel_eq_neg_deriv_log`). -/
noncomputable def idealVel (U p : ℝ → ℝ) (x : ℝ) : ℝ := -(deriv U x + score1 p x)

/-- The **relative Fisher information** `I(ρ‖π) = ∫ ((log p)' + U')² p` of `ρ = p dx` with
respect to `π = e^{-U}/Z`; for `p > 0` the integrand is `((log(p/π))')² p` (`relFisher_eq`). -/
noncomputable def relFisher (U p : ℝ → ℝ) : ℝ := ∫ x, (score1 p x + deriv U x) ^ 2 * p x

section Positive

variable {η LU Lp Z : ℝ} {U p : ℝ → ℝ}

/-! ### The ideal velocity as a log-density-ratio gradient -/

/-- For `p > 0` and `Z > 0`, `log(p/π) = log p + U + log Z` with `π = e^{-U}/Z`. -/
theorem log_div_gibbsDensity (hp : ∀ x, 0 < p x) (hZ : 0 < Z) :
    (fun y => Real.log (p y / gibbsDensity U Z y)) =
      fun y => Real.log (p y) + U y + Real.log Z := by
  funext y
  rw [gibbsDensity, div_div_eq_mul_div,
    Real.log_div (mul_ne_zero (hp y).ne' hZ.ne') (Real.exp_ne_zero _),
    Real.log_mul (hp y).ne' hZ.ne', Real.log_exp]
  ring

/-- For `p > 0` differentiable, `U` differentiable and `Z > 0`,
`(log(p/π))' = (log p)' + U'` with `π = e^{-U}/Z`. -/
theorem deriv_log_div_gibbsDensity (hp : ∀ x, 0 < p x) (hpd : Differentiable ℝ p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (x : ℝ) :
    deriv (fun y => Real.log (p y / gibbsDensity U Z y)) x = score1 p x + deriv U x := by
  rw [log_div_gibbsDensity hp hZ]
  have h1 : HasDerivAt (fun y => Real.log (p y)) (score1 p x) x := by
    rw [score1_of_pos (hpd x) (hp x)]
    exact (hpd x).hasDerivAt.log (hp x).ne'
  exact ((h1.add (hU x).hasDerivAt).add_const _).deriv

/-- The ideal velocity is `-(log(p/π))'` (for `p > 0` differentiable, `U` differentiable,
`Z > 0`). -/
theorem idealVel_eq_neg_deriv_log (hp : ∀ x, 0 < p x) (hpd : Differentiable ℝ p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (x : ℝ) :
    idealVel U p x = -deriv (fun y => Real.log (p y / gibbsDensity U Z y)) x := by
  rw [deriv_log_div_gibbsDensity hp hpd hZ hU, idealVel, add_comm]

/-- `relFisher U p = ∫ ((log(p/π))')² p` (for `p > 0` differentiable, `U` differentiable,
`Z > 0`), i.e. it is the relative Fisher information of `p dx` with respect to
`π = e^{-U}/Z`. -/
theorem relFisher_eq (hp : ∀ x, 0 < p x) (hpd : Differentiable ℝ p) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) :
    relFisher U p =
      ∫ x, (deriv (fun y => Real.log (p y / gibbsDensity U Z y)) x) ^ 2 * p x := by
  simp_rw [deriv_log_div_gibbsDensity hp hpd hZ hU]
  rfl

/-! ### Regularity of the ideal velocity -/

/-- For `p > 0` differentiable, the score is `(log p)' = p'/p`. -/
theorem score1_eq_div (hp : ∀ x, 0 < p x) (hpd : Differentiable ℝ p) :
    score1 p = fun x => deriv p x / p x :=
  funext fun x => score1_of_pos (hpd x) (hp x)

/-- If `p > 0` is twice differentiable (`p` and `p'` differentiable), then the score
`(log p)' = p'/p` is differentiable. -/
theorem differentiable_score1 (hp : ∀ x, 0 < p x) (hpd : Differentiable ℝ p)
    (hpd2 : Differentiable ℝ (deriv p)) : Differentiable ℝ (score1 p) := by
  rw [score1_eq_div hp hpd]
  exact hpd2.div hpd fun x => (hp x).ne'

/-- If `U'` and the score `(log p)'` are differentiable, so is the ideal velocity. -/
theorem differentiable_idealVel (hU' : Differentiable ℝ (deriv U))
    (hs : Differentiable ℝ (score1 p)) : Differentiable ℝ (idealVel U p) :=
  fun x => ((hU' x).add (hs x)).neg

/-- Derivative of the ideal velocity: `v' = -(U'' + (log p)'')`. -/
theorem deriv_idealVel (hU' : Differentiable ℝ (deriv U)) (hs : Differentiable ℝ (score1 p))
    (x : ℝ) : deriv (idealVel U p) x = -(deriv (deriv U) x + deriv (score1 p) x) :=
  (((hU' x).hasDerivAt.add (hs x).hasDerivAt).neg).deriv

/-- **Lipschitz bound for the ideal velocity.** If `|U''| ≤ L_U` and `|(log p)''| ≤ L_p`
(with `U'`, `(log p)'` differentiable), then `|v'| ≤ L_U + L_p` for `v = -U' - (log p)'`. -/
theorem abs_deriv_idealVel_le (hU' : Differentiable ℝ (deriv U))
    (hs : Differentiable ℝ (score1 p)) (hU'' : ∀ z, |deriv (deriv U) z| ≤ LU)
    (hs' : ∀ z, |deriv (score1 p) z| ≤ Lp) (x : ℝ) :
    |deriv (idealVel U p) x| ≤ LU + Lp := by
  rw [deriv_idealVel hU' hs, abs_neg]
  exact (abs_add_le _ _).trans (add_le_add (hU'' x) (hs' x))

/-! ### Integrability bookkeeping -/

/-- `p v² = ((log p)' + U')² p` for the ideal velocity. -/
theorem mul_idealVel_sq (x : ℝ) :
    p x * idealVel U p x ^ 2 = (score1 p x + deriv U x) ^ 2 * p x := by
  rw [idealVel]; ring

/-- For the ideal velocity, `p U' v` is integrable as soon as the Fisher integrand
`((log p)' + U')² p` and `v p'` are (`p > 0` differentiable): pointwise
`p U' v = -((log p)' + U')² p - v p'`. -/
theorem integrable_mul_deriv_mul_idealVel (hp : ∀ x, 0 < p x) (hpd : Differentiable ℝ p)
    (hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x)
    (hvp' : Integrable fun x => idealVel U p x * deriv p x) :
    Integrable fun x => p x * (deriv U x * idealVel U p x) := by
  refine (hF.neg.sub hvp').congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, Pi.neg_apply]
  rw [← DensityStein.score1_mul_eq_of_hasDerivAt (hpd x).hasDerivAt (hp x), idealVel]
  ring

/-! ### First- and second-order terms for the ideal velocity -/

/-- **First-order term = relative Fisher information.** For `p > 0` integrable and
differentiable, `U'` and `(log p)'` differentiable, `|v'| ≤ Lv` for the ideal velocity
`v = -U' - (log p)'`, and `((log p)' + U')² p`, `v p'`, `v p` integrable, the density Stein
identity (ID-2) gives `∫ p (v' - U' v) = ∫ ((log p)' + U')² p = I(ρ‖π)`. -/
theorem integral_mul_sub_eq_relFisher {Lv : ℝ} (hp : ∀ x, 0 < p x) (hp_int : Integrable p)
    (hpd : Differentiable ℝ p) (hU' : Differentiable ℝ (deriv U))
    (hs : Differentiable ℝ (score1 p)) (hv' : ∀ x, |deriv (idealVel U p) x| ≤ Lv)
    (hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x)
    (hvp' : Integrable fun x => idealVel U p x * deriv p x)
    (hvp : Integrable fun x => idealVel U p x * p x) :
    ∫ x, p x * (deriv (idealVel U p) x - deriv U x * idealVel U p x) = relFisher U p := by
  set v := idealVel U p with hv_def
  have hvd : Differentiable ℝ v := differentiable_idealVel hU' hs
  have hdv : Integrable fun x => deriv v x * p x :=
    (integrable_mul_deriv hv' hp_int).1.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hstein := DensityStein.integral_deriv_mul_eq_neg_integral_mul_score1 hp
    (fun x => (hpd x).hasDerivAt) (fun x => (hvd x).hasDerivAt) hdv hvp' hvp
  have hvs : Integrable fun x => v x * score1 p x * p x := by
    refine hvp'.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_assoc, DensityStein.score1_mul_eq_of_hasDerivAt (hpd x).hasDerivAt (hp x)]
  have hUv := integrable_mul_deriv_mul_idealVel hp hpd hF hvp'
  rw [← hv_def] at hUv
  calc ∫ x, p x * (deriv v x - deriv U x * v x)
      = ∫ x, (deriv v x * p x - p x * (deriv U x * v x)) :=
        integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    _ = -((∫ x, v x * score1 p x * p x) + ∫ x, p x * (deriv U x * v x)) := by
        rw [integral_sub hdv hUv, hstein]; ring
    _ = -∫ x, (v x * score1 p x * p x + p x * (deriv U x * v x)) := by
        rw [integral_add hvs hUv]
    _ = relFisher U p := by
        rw [relFisher, ← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hv_def, idealVel]
        ring

/-- **Second-order term.** With `0 ≤ L_U`, `|v'| ≤ L_U + L_p` for the ideal velocity, `p ≥ 0`
integrable and the Fisher integrand integrable,
`∫ p (v'² + (L_U/2) v²) ≤ (L_U + L_p)² ∫ p + (L_U/2) I(ρ‖π)`. -/
theorem integral_secondOrder_le (hLU : 0 ≤ LU) (hp : ∀ x, 0 ≤ p x) (hp_int : Integrable p)
    (hv' : ∀ x, |deriv (idealVel U p) x| ≤ LU + Lp)
    (hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x) :
    ∫ x, p x * (deriv (idealVel U p) x ^ 2 + LU / 2 * idealVel U p x ^ 2) ≤
      (LU + Lp) ^ 2 * (∫ x, p x) + LU / 2 * relFisher U p := by
  obtain ⟨-, hdv2⟩ := integrable_mul_deriv hv' hp_int
  have hv2 : Integrable fun x => p x * idealVel U p x ^ 2 :=
    hF.congr (Eventually.of_forall fun x => (mul_idealVel_sq x).symm)
  have hL : Integrable fun x =>
      p x * (deriv (idealVel U p) x ^ 2 + LU / 2 * idealVel U p x ^ 2) :=
    (hdv2.add (hv2.const_mul (LU / 2))).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have hR : Integrable fun x =>
      (LU + Lp) ^ 2 * p x + LU / 2 * ((score1 p x + deriv U x) ^ 2 * p x) :=
    (hp_int.const_mul _).add (hF.const_mul _)
  refine (integral_mono hL hR fun x => ?_).trans_eq ?_
  · have hsq : deriv (idealVel U p) x ^ 2 ≤ (LU + Lp) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hv' x) 2
    have h1 := mul_le_mul_of_nonneg_left hsq (hp x)
    have h2 := mul_idealVel_sq (U := U) (p := p) x
    simp only
    nlinarith
  · rw [integral_add (hp_int.const_mul _) (hF.const_mul _), integral_const_mul,
      integral_const_mul, relFisher]

/-! ### Descent for the ideal velocity -/

/-- **DT-1 for the ideal velocity (density level, Stein form).** Let `π = e^{-U}/Z` (`Z > 0`)
with `U` and `U'` differentiable and `|U''| ≤ L_U`; let `p > 0` be integrable with `p` and `p'`
differentiable and `|(log p)''| ≤ L_p`. Let `v = -U' - (log p)'` be the ideal velocity, so
`|v'| ≤ L_U + L_p`; take `0 ≤ η` with `η (L_U + L_p) ≤ 1/2`, `T = id + η v` and
`q = pushDensity η v p`. Assume `p log(p/π)`, `p (U∘T - U)`, the Fisher integrand
`((log p)' + U')² p`, `v p'` and `v p` are integrable. Then
`∫ q log(q/π) ≤ ∫ p log(p/π) - η I(ρ‖π) + η² ∫ p (v'² + (L_U/2) v²)`,
`I(ρ‖π) = ∫ ((log(p/π))')² p` (`relFisher`, `relFisher_eq`). -/
theorem integral_pushDensity_klIntegrand_le_idealVel (hη : 0 ≤ η)
    (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z) (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (deriv U)) (hU'' : ∀ z, |deriv (deriv U) z| ≤ LU)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hpd : Differentiable ℝ p)
    (hpd2 : Differentiable ℝ (deriv p)) (hs' : ∀ z, |deriv (score1 p) z| ≤ Lp)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η (idealVel U p) x) - U x))
    (hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x)
    (hvp' : Integrable fun x => idealVel U p x * deriv p x)
    (hvp : Integrable fun x => idealVel U p x * p x) :
    ∫ y, pushDensity η (idealVel U p) p y *
        Real.log (pushDensity η (idealVel U p) p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) - η * relFisher U p +
        η ^ 2 * ∫ x, p x * (deriv (idealVel U p) x ^ 2 + LU / 2 * idealVel U p x ^ 2) := by
  have hs := differentiable_score1 hp hpd hpd2
  have hv' := abs_deriv_idealVel_le hU' hs hU'' hs'
  have h := integral_pushDensity_klIntegrand_le_stein (differentiable_idealVel hU' hs) hv'
    hη hηL hp hp_int hpd hZ hU hU' (fun z => (le_abs_self _).trans (hU'' z)) hKL hUT
    (integrable_mul_deriv_mul_idealVel hp hpd hF hvp')
    (hF.congr (Eventually.of_forall fun x => (mul_idealVel_sq x).symm)) hvp' hvp
  have e : ∫ x, idealVel U p x * (score1 p x + deriv U x) * p x = -relFisher U p := by
    rw [relFisher, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [idealVel]
    ring
  rw [e] at h
  linarith

/-- **DT-1 for the ideal velocity, explicit constants (density level).** Under the hypotheses
of `integral_pushDensity_klIntegrand_le_idealVel` and `∫ p = 1`,
`∫ q log(q/π) ≤ ∫ p log(p/π) - η (1 - η L_U / 2) I(ρ‖π) + η² (L_U + L_p)²`
for every `0 ≤ η ≤ 1/(2 (L_U + L_p))`. -/
theorem integral_pushDensity_klIntegrand_le_idealVel' (hη : 0 ≤ η)
    (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z) (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (deriv U)) (hU'' : ∀ z, |deriv (deriv U) z| ≤ LU)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hp_one : ∫ x, p x = 1)
    (hpd : Differentiable ℝ p)
    (hpd2 : Differentiable ℝ (deriv p)) (hs' : ∀ z, |deriv (score1 p) z| ≤ Lp)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η (idealVel U p) x) - U x))
    (hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x)
    (hvp' : Integrable fun x => idealVel U p x * deriv p x)
    (hvp : Integrable fun x => idealVel U p x * p x) :
    ∫ y, pushDensity η (idealVel U p) p y *
        Real.log (pushDensity η (idealVel U p) p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
        η * (1 - η * LU / 2) * relFisher U p + η ^ 2 * (LU + Lp) ^ 2 := by
  have h := integral_pushDensity_klIntegrand_le_idealVel hη hηL hZ hU hU' hU'' hp hp_int hpd
    hpd2 hs' hKL hUT hF hvp' hvp
  have hs := differentiable_score1 hp hpd hpd2
  have h2 := integral_secondOrder_le ((abs_nonneg _).trans (hU'' 0)) (fun x => (hp x).le)
    hp_int (abs_deriv_idealVel_le hU' hs hU'' hs') hF
  rw [hp_one, mul_one] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg η)
  nlinarith

/-- **DT-1 for the ideal velocity (Mathlib `klDiv`).** Let `ρ = p dx` and `π = e^{-U}/Z dx`
be probability measures on `ℝ` (`Z > 0`), `p > 0` measurable with `p`, `p'` differentiable
and `|(log p)''| ≤ L_p`, and `U`, `U'` differentiable with `|U''| ≤ L_U`. Let
`v = -U' - (log p)'` be the ideal velocity, `0 ≤ η` with `η (L_U + L_p) ≤ 1/2`, and
`T = id + η v`. Assume `p log(p/π)`, `p (U∘T - U)`, `((log p)' + U')² p`, `v p'` and `v p`
are integrable. Then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η (1 - η L_U / 2) I(ρ‖π) + η² (L_U + L_p)²`,
with `I(ρ‖π) = ∫ ((log(p/π))')² p` the relative Fisher information (`relFisher`). -/
theorem klDiv_map_step_idealVel_le (hη : 0 ≤ η) (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, |deriv (deriv U) z| ≤ LU) (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hpd : Differentiable ℝ p) (hpd2 : Differentiable ℝ (deriv p))
    (hs' : ∀ z, |deriv (score1 p) z| ≤ Lp)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η (idealVel U p) x) - U x))
    (hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x)
    (hvp' : Integrable fun x => idealVel U p x * deriv p x)
    (hvp : Integrable fun x => idealVel U p x * p x) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (1 - η * LU / 2) * relFisher U p + η ^ 2 * (LU + Lp) ^ 2 := by
  have h1 : ∫⁻ x, ENNReal.ofReal (p x) = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, measure_univ]
  have hp_int : Integrable p := by
    refine ⟨hp_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (hp x).le), h1]
    exact ENNReal.one_lt_top
  have hp_one : ∫ x, p x = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (hp x).le)
      hp_meas.aestronglyMeasurable, h1, ENNReal.toReal_one]
  have hs := differentiable_score1 hp hpd hpd2
  have hv' := abs_deriv_idealVel_le hU' hs hU'' hs'
  obtain ⟨hne, h⟩ := klDiv_map_step_le (differentiable_idealVel hU' hs) hv' hη hηL hp hp_meas
    hZ hU hU' (fun z => (le_abs_self _).trans (hU'' z)) hKL hUT
    (integrable_mul_deriv_mul_idealVel hp hpd hF hvp')
    (hF.congr (Eventually.of_forall fun x => (mul_idealVel_sq x).symm))
  refine ⟨hne, ?_⟩
  rw [integral_mul_sub_eq_relFisher hp hp_int hpd hU' hs hv' hF hvp' hvp] at h
  have h2 := integral_secondOrder_le ((abs_nonneg _).trans (hU'' 0)) (fun x => (hp x).le)
    hp_int hv' hF
  rw [hp_one, mul_one] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg η)
  nlinarith

end Positive

/-! ### Negative result: Gaussian current laws -/

section Gaussian

/-- The standard Gaussian density is the Gibbs density of `U(x) = x²/2` with `Z = √(2π)`. -/
theorem gaussianPDFReal_zero_one_eq_gibbsDensity :
    gaussianPDFReal 0 1 = gibbsDensity (fun x => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) := by
  funext x
  rw [gaussianPDFReal, gibbsDensity, NNReal.coe_one, mul_one, sub_zero, div_eq_mul_inv,
    mul_comm]
  congr 2
  ring

/-- `(x²/2)' = x`. -/
theorem deriv_half_sq (x : ℝ) : deriv (fun x : ℝ => x ^ 2 / 2) x = x := by
  have := ((hasDerivAt_pow 2 x).div_const 2)
  rw [this.deriv]
  push_cast
  ring

/-- **Ideal velocity between Gaussians.** For the target `N(0, 1)` (`U(x) = x²/2`) and the
current law `N(0, s)` with `s ≠ 0`, the ideal velocity is linear: `v(x) = (1/s - 1) x`. -/
theorem idealVel_gaussian {s : ℝ≥0} (hs : s ≠ 0) :
    idealVel (fun x => x ^ 2 / 2) (gaussianPDFReal 0 s) = fun x => (1 / (s : ℝ) - 1) * x := by
  funext x
  rw [idealVel, deriv_half_sq, score1_gaussianPDFReal 0 hs]
  ring

/-- The derivative (= Lipschitz constant) of the Gaussian ideal velocity is `1/s - 1`. -/
theorem deriv_idealVel_gaussian {s : ℝ≥0} (hs : s ≠ 0) (x : ℝ) :
    deriv (idealVel (fun x => x ^ 2 / 2) (gaussianPDFReal 0 s)) x = 1 / (s : ℝ) - 1 := by
  rw [idealVel_gaussian hs]
  exact ((hasDerivAt_id' x).const_mul _).deriv.trans (mul_one _)

/-- **No uniform Lipschitz bound.** For every `L` there is a variance `s > 0` such that the
ideal velocity from `N(0, s)` towards `N(0, 1)` has `|v'(x)| > L` at every `x`. -/
theorem exists_lipschitz_idealVel_gaussian_gt (L : ℝ) :
    ∃ s : ℝ≥0, s ≠ 0 ∧
      ∀ x, L < |deriv (idealVel (fun x => x ^ 2 / 2) (gaussianPDFReal 0 s)) x| := by
  have hpos : (0 : ℝ) < |L| + 2 := by positivity
  have hs0 : (1 / (|L| + 2)).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  refine ⟨(1 / (|L| + 2)).toNNReal, hs0, fun x => ?_⟩
  rw [deriv_idealVel_gaussian hs0, Real.coe_toNNReal _ (by positivity), one_div_one_div,
    abs_of_pos (by linarith [abs_nonneg L])]
  linarith [le_abs_self L]

/-- Scalar core of the negative result: for every `η > 0` there is `s ∈ (0, 1)` with
`η (1/s - 1) > 1/2`, `c = 1 + η (1/s - 1) > 0` and
`s - 1 - log s < s c² - 1 - log (s c²)`, i.e. the Gaussian KL `(V - 1 - log V)/2` to `N(0, 1)`
is larger at the pushed variance `V = s c²` than at `s`. -/
theorem exists_var_kl_increase {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ 1 / 2 < η * (1 / s - 1) ∧ 0 < 1 + η * (1 / s - 1) ∧
      s - 1 - Real.log s <
        s * (1 + η * (1 / s - 1)) ^ 2 - 1 - Real.log (s * (1 + η * (1 / s - 1)) ^ 2) := by
  set t : ℝ := 4 * (1 + η) / η with ht_def
  have ht : η * t = 4 * (1 + η) := by rw [ht_def]; field_simp
  have ht4 : 4 < t := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hη.le]
  have hD : 0 < t ^ 2 - 1 + η := by nlinarith
  set s : ℝ := η / (t ^ 2 - 1 + η) with hs_def
  have hs : 0 < s := div_pos hη hD
  have hs1 : s < 1 := by rw [hs_def, div_lt_one hD]; nlinarith
  have hc : 1 + η * (1 / s - 1) = t ^ 2 := by
    rw [hs_def]; field_simp; ring
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · have : η * (1 / s - 1) = t ^ 2 - 1 := by linarith
    rw [this]; nlinarith
  · rw [hc]; positivity
  · rw [hc, Real.log_mul hs.ne' (by positivity), ← pow_mul, Real.log_pow]
    have hlog : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
    -- `s t⁴ ≥ 4 t`
    have hst : 4 * t ≤ s * t ^ (2 * 2) := by
      rw [hs_def, div_mul_eq_mul_div, le_div_iff₀ hD]
      have : η * t ^ 4 = 4 * (1 + η) * t ^ 3 := by rw [← ht]; ring
      norm_num
      nlinarith
    have e1 : ((2 * 2 : ℕ) : ℝ) = 4 := by norm_num
    have e2 : t ^ (2 * 2) = t ^ 4 := by norm_num
    rw [e1, e2] at *
    linarith

/-- **A fixed step size cannot work uniformly over current laws.** Target `π = N(0, 1)`
(`U(x) = x²/2`). For **every** step size `η > 0` there is a variance `s > 0` such that, for the
current law `ρ = N(0, s)` and its ideal velocity `v(x) = (1/s - 1) x`, the hypothesis of DT-1
fails (`η |v'| = η |1/s - 1| > 1/2`) and the deterministic step `T = id + η v` strictly
**increases** the KL divergence: `KL(ρ ‖ π) < KL(T#ρ ‖ π)` (Mathlib `klDiv`). -/
theorem exists_klDiv_map_step_idealVel_gt {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ≥0, s ≠ 0 ∧ 1 / 2 < η * |1 / (s : ℝ) - 1| ∧
      klDiv (gaussianReal 0 s) (gaussianReal 0 1) <
        klDiv ((gaussianReal 0 s).map
            (step η (idealVel (fun x => x ^ 2 / 2) (gaussianPDFReal 0 s))))
          (gaussianReal 0 1) := by
  obtain ⟨s, hs, hηs, hc, hkl⟩ := exists_var_kl_increase hη
  have hs0 : s.toNNReal ≠ 0 := by rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hs
  have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.le
  refine ⟨s.toNNReal, hs0, ?_, ?_⟩
  · rw [hcoe]
    exact hηs.trans_le (mul_le_mul_of_nonneg_left (le_abs_self _) hη.le)
  set c := 1 + η * (1 / s - 1) with hc_def
  have hstep : step η (idealVel (fun x => x ^ 2 / 2) (gaussianPDFReal 0 s.toNNReal)) =
      fun x => c * x := by
    funext x
    rw [step, idealVel_gaussian hs0, hcoe, hc_def]
    ring
  rw [hstep, gaussianReal_map_const_mul, mul_zero]
  have hV : (NNReal.mk (c ^ 2) (sq_nonneg _) * s.toNNReal) ≠ 0 := by
    rw [Ne, ← NNReal.coe_eq_zero, NNReal.coe_mul, hcoe]
    exact (mul_pos (pow_pos hc 2) hs).ne'
  rw [GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian 0 hs0,
    GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian 0 hV, NNReal.coe_mul, hcoe]
  have h0 : 0 ≤ s - 1 - Real.log s := by linarith [Real.log_le_sub_one_of_pos hs]
  have hc2 : ((NNReal.mk (c ^ 2) (sq_nonneg _) : ℝ≥0) : ℝ) = c ^ 2 := rfl
  rw [hc2, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by nlinarith), mul_comm (c ^ 2)]
  nlinarith

end Gaussian

end FormalizeSampling.IdealVelocityStep
