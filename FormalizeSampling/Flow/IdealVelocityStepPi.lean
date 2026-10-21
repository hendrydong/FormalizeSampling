module

public import FormalizeSampling.Flow.DeterministicStepPi
public import FormalizeSampling.Flow.IdealVelocityStep

/-!
# DT-1 for the ideal velocity in dimension `d`: a law-dependent step size

Status: **Verified** (positive result, under explicit regularity and integrability hypotheses)
and **Counterexample** (negative result).

The `d`-dimensional analogue, on `Fin d → ℝ` with Lebesgue `volume`, of
`FormalizeSampling/Flow/IdealVelocityStep.lean`, built on the `d`-dimensional descent lemma
DT-1 of `FormalizeSampling/Flow/DeterministicStepPi.lean`. For the **ideal velocity**
`v = -∇U - ∇log p = -∇log(p/π)` (target `π = e^{-U}/Z`, current law `ρ = p dx`) the Lipschitz
constant of `v`, hence the admissible step size of DT-1, depends on the current density `p`.

## Conventions

* As in `DeterministicStepPi`, `‖·‖` on `Fin d → ℝ` is Mathlib's sup norm, so `‖D(∇U)‖ ≤ L_U`,
  `‖D(∇log p)‖ ≤ L_p` and `‖Dv‖ ≤ Lv` are operator-norm bounds `ℓ∞ → ℓ∞` (max absolute row sum
  of the Hessian matrix). Squared lengths `‖w‖²` of vectors are Euclidean, `w ⬝ᵥ w`.
* `score p = ∇log p` (`Foundations/VectorCalculus.lean`), `grad`, `divergence`, `frobSq`
  (squared Frobenius norm), `jacMat` (Jacobian matrix), `step η v = id + η v`, `pushDensity`
  and `gibbsDensity` are those of the library / `DeterministicStepPi`.

## Positive result (bounded Hessians)

* `idealVel U p = -(∇U + ∇log p)`, `relFisher U p = ∫ ‖∇log p + ∇U‖² p` (relative Fisher
  information of `p dx` w.r.t. `π`).
* `idealVel_eq_grad`, `isSymm_jacMat_idealVel`: `v = ∇(-(U + log p))` is a gradient field, so
  its Jacobian is symmetric (`DeterministicStepPi.isSymm_jacMat_grad`).
* `norm_fderiv_idealVel_le`: `‖D(∇U)‖ ≤ L_U` and `‖D(∇log p)‖ ≤ L_p` give `‖Dv‖ ≤ L_U + L_p`.
* `mulVec_dotProduct_le_of_isSymm` (Schur test) and `fderiv_fderiv_apply_le`: the operator-norm
  bound `‖D(∇U)‖ ≤ L_U` implies the Hessian upper bound `D²U(z)(h, h) ≤ L_U ‖h‖²` (Euclidean)
  required by `DeterministicStepPi.le_quadratic_of_fderiv2_le`; no separate hypothesis needed.
* `integral_pushDensity_klIntegrand_le_idealVel` (density level; first-order term via the
  `d`-dimensional Stein identity in `integral_pushDensity_klIntegrand_le_stein`), for `0 ≤ η`,
  `η (L_U + L_p) ≤ 1/2`:
  `∫ q log(q/π) ≤ ∫ p log(p/π) - η I(ρ‖π) + η² ∫ p (‖Dv‖_F² + (L_U/2) ‖v‖²)`.
* `integral_secondOrder_le`: `∫ p (‖Dv‖_F² + (L_U/2)‖v‖²) ≤ d (L_U + L_p)² ∫ p + (L_U/2) I`,
  linear in the dimension through `DeterministicStepPi.frobSq_le_mul_dim`
  (`‖A‖_F² ≤ d ‖A‖²` for the sup-norm operator norm).
* `integral_pushDensity_klIntegrand_le_idealVel'` and `klDiv_map_step_idealVel_le` (Mathlib
  `klDiv`): with `ρ`, `π` probability measures,
  `KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η (1 - η L_U / 2) I(ρ‖π) + η² d (L_U + L_p)²`.

## Negative result (no uniform step size), `d ≥ 1`

Target `π = N(0, I) = ⊗ᵢ N(0, 1)` (potential `stdPotential = ‖x‖²/2`,
`gaussianPDFPi_one_eq_gibbsDensity`), current law `ρ = N(0, s I)` with density
`gaussianPDFPi s = ∏ᵢ N(0, s)(xᵢ)`.

* `grad_sum_comp`, `idealVel_gaussianPi`, `idealVel_gaussianPi_eq`: the ideal velocity acts
  coordinatewise as the one-dimensional one and equals `v(x) = (1/s - 1) x`.
* `log_gaussianPDFPi`, `differentiable_log_gaussianPDFReal`, `score_gaussianPDFPi`: the score
  of `N(0, s I)` is `x ↦ -x/s`.
* `exists_klDiv_map_step_idealVel_gt`: for **every** `η > 0` there is `s > 0` (with
  `η |1/s - 1| > 1/2`) such that `KL(N(0, sI) ‖ N(0, I)) < KL(T#N(0, sI) ‖ N(0, I))`,
  `T = id + η v`. Proof: reduction to `IdealVelocityStep.exists_klDiv_map_step_idealVel_gt`
  through `Measure.pi_map_pi` and KL tensorisation `GaussianIncrement.klDiv_pi_pi`.

## NOT proved here

* The integrability hypotheses of the positive result (`p log(p/π)`, `p (U∘T - U)`, the
  Fisher integrand, `vᵢ (∇log p)ᵢ p`, `p vᵢ`) are assumed here, not derived from `L_U`, `L_p`;
  they are derived from a finite second moment in
  `DeterministicStepMomentsPi.klDiv_map_step_idealVel_le`.
* Optimality of the descent constant. (The matrix bound `‖A‖_F² ≤ d L²` itself is attained by
  `A = L I`, so under the sup-norm hypothesis the factor `d` cannot be removed from it; this
  is not formalised.)
* That `gaussianPDFPi s` is the Lebesgue density of `Measure.pi fun _ => gaussianReal 0 s` is
  not stated here (the negative result is stated with the product measure and the ideal
  velocity of the explicit product density); it is a short consequence of
  `MeasureHelpers.pi_withDensity_ofReal`.
* That `‖Dv‖` itself is unbounded over Gaussian current laws in dimension `d` (only the scalar
  condition `η |1/s - 1| > 1/2` is recorded).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Matrix
open scoped NNReal ENNReal

namespace FormalizeSampling.IdealVelocityStepPi

open DeterministicStepPi

variable {d : ℕ}

/-! ### Definitions -/

/-- The **ideal velocity** `v = -(∇U + ∇log p)` on `Fin d → ℝ` for target `π = e^{-U}/Z` and
current density `p`; for `p > 0` it is `-∇log(p/π)` (`idealVel_eq_grad`). -/
noncomputable def idealVel (U p : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  -(grad U x + score p x)

/-- The **relative Fisher information** `I(ρ‖π) = ∫ ‖∇log p + ∇U‖² p` (Euclidean norm, written
`w ⬝ᵥ w`) of `ρ = p dx` with respect to `π = e^{-U}/Z`; for `p > 0` the integrand is
`‖∇log(p/π)‖² p`. -/
noncomputable def relFisher (U p : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x

/-! ### Matrix and calculus lemmas -/

/-- **Quadratic-form bound from the `ℓ∞` operator norm (Schur test).** For a symmetric real
matrix `A` with `‖A w‖ ≤ L ‖w‖` for all `w` (sup norm) and `0 ≤ L`,
`(A h) ⬝ᵥ h ≤ L (h ⬝ᵥ h)` (Euclidean). Proof: `Aᵢⱼ hᵢ hⱼ ≤ |Aᵢⱼ| (hᵢ² + hⱼ²)/2`, symmetry, and
the row-sum bound `DeterministicStepPi.sum_abs_le_of_norm_mulVec_le`. -/
theorem mulVec_dotProduct_le_of_isSymm {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ L * ‖w‖) (h : Fin d → ℝ) :
    (A *ᵥ h) ⬝ᵥ h ≤ L * (h ⬝ᵥ h) := by
  have hR := sum_abs_le_of_norm_mulVec_le hL0 hL
  have hsym : ∀ i j, A i j = A j i := fun i j => by
    conv_rhs => rw [← hA]
    rfl
  have e1 : (A *ᵥ h) ⬝ᵥ h = ∑ i, ∑ j, A i j * h j * h i := by
    simp only [dotProduct, mulVec, Finset.sum_mul]
  have step : ∀ i j, A i j * h j * h i ≤ |A i j| * h i ^ 2 / 2 + |A j i| * h j ^ 2 / 2 :=
    fun i j => by
      rw [← hsym i j]
      have h1 : A i j * (h j * h i) ≤ |A i j| * |h j * h i| :=
        (le_abs_self _).trans (abs_mul _ _).le
      have h2 : |h j * h i| ≤ (h i ^ 2 + h j ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|h i| - |h j|), sq_abs (h i), sq_abs (h j)]
      nlinarith [abs_nonneg (A i j), mul_le_mul_of_nonneg_left h2 (abs_nonneg (A i j))]
  have e2 : ∑ i, ∑ j, (|A i j| * h i ^ 2 / 2 + |A j i| * h j ^ 2 / 2) =
      ∑ i, h i ^ 2 * ∑ j, |A i j| := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => |A j i| * h j ^ 2 / 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (A *ᵥ h) ⬝ᵥ h ≤ ∑ i, ∑ j, (|A i j| * h i ^ 2 / 2 + |A j i| * h j ^ 2 / 2) := by
        rw [e1]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => step i j
    _ = ∑ i, h i ^ 2 * ∑ j, |A i j| := e2
    _ ≤ ∑ i, h i ^ 2 * L :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hR i) (sq_nonneg _)
    _ = L * (h ⬝ᵥ h) := by
        rw [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- A continuous linear functional on `Fin d → ℝ` is determined by its values on the standard
basis: `ℓ h = ∑ᵢ ℓ(eᵢ) hᵢ`. -/
theorem clm_apply_eq_sum (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (h : Fin d → ℝ) :
    ℓ h = ∑ i, ℓ (Pi.single i 1) * h i := by
  conv_lhs => rw [← Finset.univ_sum_single h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (h i) = h i • (Pi.single i (1 : ℝ) : Fin d → ℝ) by
    rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

/-- **Derivative of a coordinate gradient.** If `Dφ` is differentiable at `x`, then `∇φ` has
Fréchet derivative `w ↦ (D²φ(x)(w)(eᵢ))ᵢ` at `x`. -/
theorem hasFDerivAt_grad {φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hφ' : DifferentiableAt ℝ (fderiv ℝ φ) x) :
    HasFDerivAt (grad φ)
      (ContinuousLinearMap.pi fun i => (fderiv ℝ (fderiv ℝ φ) x).flip (Pi.single i 1)) x := by
  refine hasFDerivAt_pi.2 fun i => ?_
  have := hφ'.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) x)
  simpa [grad, partialDeriv] using this

/-- The coordinate gradient `∇φ` is differentiable when `Dφ` is. -/
theorem differentiable_grad {φ : (Fin d → ℝ) → ℝ} (hφ' : Differentiable ℝ (fderiv ℝ φ)) :
    Differentiable ℝ (grad φ) := fun x => (hasFDerivAt_grad (hφ' x)).differentiableAt

/-- The second derivative as a quadratic form is the Jacobian of the gradient paired with the
direction: `D²U(z)(h, h) = (D(∇U)(z) h) ⬝ᵥ h` (for `DU` differentiable at `z`). -/
theorem fderiv_fderiv_apply_apply {U : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (hU' : DifferentiableAt ℝ (fderiv ℝ U) z) (h : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ U) z h h = fderiv ℝ (grad U) z h ⬝ᵥ h := by
  rw [(hasFDerivAt_grad hU').fderiv, clm_apply_eq_sum, dotProduct]
  rfl

/-- **Hessian upper bound from an operator-norm bound on `D(∇U)`.** If `U` and `DU` are
differentiable and `‖D(∇U)(z)‖ ≤ L` for all `z` (operator norm for the sup norm on
`Fin d → ℝ`), then `D²U(z)(h, h) ≤ L ‖h‖²` (Euclidean, `h ⬝ᵥ h`) for all `z h`, i.e.
`∇²U ≼ L I`: the hypothesis of `DeterministicStepPi.le_quadratic_of_fderiv2_le`. -/
theorem fderiv_fderiv_apply_le {U : (Fin d → ℝ) → ℝ} {L : ℝ} (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (fderiv ℝ U)) (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ L)
    (z h : Fin d → ℝ) : fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h) := by
  rw [fderiv_fderiv_apply_apply (hU' z), ← jacMat_mulVec]
  refine mulVec_dotProduct_le_of_isSymm (isSymm_jacMat_grad hU hU' z)
    ((norm_nonneg _).trans (hUH z)) (fun w => ?_) h
  rw [jacMat_mulVec]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hUH z) (norm_nonneg _))

/-! ### The ideal velocity as a gradient field -/

section Regularity

variable {U p : (Fin d → ℝ) → ℝ} {LU Lp : ℝ}

/-- The ideal velocity is a gradient: `v = ∇φ` with `φ = -(U + log p)` (for `U` and `log p`
differentiable). For `p > 0` and `π = e^{-U}/Z`, `φ = -log(p/π) + log Z`. -/
theorem idealVel_eq_grad (hU : Differentiable ℝ U)
    (hℓ : Differentiable ℝ fun x => Real.log (p x)) :
    idealVel U p = grad fun x => -(U x + Real.log (p x)) := by
  funext x
  have hf : fderiv ℝ (fun x => -(U x + Real.log (p x))) x =
      -(fderiv ℝ U x + fderiv ℝ (fun x => Real.log (p x)) x) :=
    (((hU x).hasFDerivAt.add (hℓ x).hasFDerivAt).neg).fderiv
  funext i
  show -(fderiv ℝ U x (Pi.single i 1) + fderiv ℝ (fun y => Real.log (p y)) x (Pi.single i 1)) =
    fderiv ℝ (fun x => -(U x + Real.log (p x))) x (Pi.single i 1)
  rw [hf]
  rfl

/-- The ideal velocity `v = -(∇U + ∇log p)` is differentiable when `DU` and `D log p` are. -/
theorem differentiable_idealVel (hU' : Differentiable ℝ (fderiv ℝ U))
    (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x))) :
    Differentiable ℝ (idealVel U p) := fun x =>
  ((differentiable_grad hU' x).add (differentiable_grad hℓ' x)).neg

/-- **Symmetric Jacobian.** If `U`, `DU`, `log p` and `D log p` are differentiable, the
Jacobian of the ideal velocity is symmetric at every point (it is a Hessian,
`isSymm_jacMat_grad`). -/
theorem isSymm_jacMat_idealVel (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hℓ : Differentiable ℝ fun x => Real.log (p x))
    (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x))) (x : Fin d → ℝ) :
    (jacMat (idealVel U p) x).IsSymm := by
  rw [idealVel_eq_grad hU hℓ]
  have hf : fderiv ℝ (fun x => -(U x + Real.log (p x))) =
      fun x => -(fderiv ℝ U x + fderiv ℝ (fun x => Real.log (p x)) x) :=
    funext fun x => (((hU x).hasFDerivAt.add (hℓ x).hasFDerivAt).neg).fderiv
  refine isSymm_jacMat_grad (φ := fun x => -(U x + Real.log (p x)))
    (fun x => ((hU x).add (hℓ x)).neg) ?_ x
  rw [hf]
  exact (hU'.add hℓ').neg

/-- **Lipschitz bound for the ideal velocity.** If `DU` and `D log p` are differentiable,
`‖D(∇U)‖ ≤ L_U` and `‖D(∇log p)‖ ≤ L_p` everywhere (operator norms for the sup norm on
`Fin d → ℝ`), then `‖Dv(x)‖ ≤ L_U + L_p` for `v = -(∇U + ∇log p)`: the hypothesis
`‖fderiv ℝ v x‖ ≤ Lv` of `DeterministicStepPi` with `Lv = L_U + L_p`. -/
theorem norm_fderiv_idealVel_le (hU' : Differentiable ℝ (fderiv ℝ U))
    (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x)))
    (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ LU) (hsH : ∀ z, ‖fderiv ℝ (score p) z‖ ≤ Lp)
    (x : Fin d → ℝ) : ‖fderiv ℝ (idealVel U p) x‖ ≤ LU + Lp := by
  have hs : Differentiable ℝ (score p) := differentiable_grad hℓ'
  have e : fderiv ℝ (idealVel U p) x = -(fderiv ℝ (grad U) x + fderiv ℝ (score p) x) :=
    (((differentiable_grad hU' x).hasFDerivAt.add (hs x).hasFDerivAt).neg).fderiv
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add (hUH x) (hsH x))

end Regularity

/-! ### First- and second-order terms -/

section Positive

variable {η LU Lp Z : ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- `‖v‖² p = ‖∇log p + ∇U‖² p` for the ideal velocity `v = -(∇U + ∇log p)`. -/
theorem idealVel_dotProduct_self (x : Fin d → ℝ) :
    idealVel U p x ⬝ᵥ idealVel U p x = (score p x + grad U x) ⬝ᵥ (score p x + grad U x) := by
  simp only [idealVel, neg_dotProduct, dotProduct_neg, neg_neg, add_comm (grad U x)]

/-- For the ideal velocity, `v ⬝ᵥ (∇log p + ∇U) = -‖∇log p + ∇U‖²`. -/
theorem idealVel_dotProduct_score_add (x : Fin d → ℝ) :
    idealVel U p x ⬝ᵥ (score p x + grad U x) =
      -((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) := by
  simp only [idealVel, neg_dotProduct, add_comm (grad U x)]

/-- For the ideal velocity, `p ∇U ⬝ᵥ v` is integrable as soon as the Fisher integrand
`‖∇log p + ∇U‖² p` and every `vᵢ (∇log p)ᵢ p` are: pointwise
`p ∇U ⬝ᵥ v = -‖∇log p + ∇U‖² p - ∑ᵢ vᵢ (∇log p)ᵢ p`. -/
theorem integrable_mul_grad_dotProduct_idealVel
    (hF : Integrable fun x => ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x)
    (hvs : ∀ i, Integrable fun x => idealVel U p x i * score p x i * p x) :
    Integrable fun x => p x * (grad U x ⬝ᵥ idealVel U p x) := by
  refine (hF.neg.sub (integrable_finsetSum Finset.univ fun i _ => hvs i)).congr
    (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, Pi.neg_apply]
  rw [← idealVel_dotProduct_self]
  simp only [idealVel, dotProduct, Pi.neg_apply, Pi.add_apply, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Second-order term, linear in `d`.** With `‖Dv‖ ≤ L_U + L_p` for the ideal velocity,
`p ≥ 0` integrable and the Fisher integrand integrable,
`∫ p (‖Dv‖_F² + (L_U/2) ‖v‖²) ≤ d (L_U + L_p)² ∫ p + (L_U/2) I(ρ‖π)`
(`‖Dv‖_F²` the squared Frobenius norm of the Jacobian, `‖v‖²` Euclidean; `‖Dv‖_F² ≤ d ‖Dv‖²`
by `DeterministicStepPi.frobSq_jacMat_le`). -/
theorem integral_secondOrder_le (hp : ∀ x, 0 ≤ p x) (hp_int : Integrable p)
    (hv' : ∀ x, ‖fderiv ℝ (idealVel U p) x‖ ≤ LU + Lp)
    (hF : Integrable fun x => ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x) :
    ∫ x, p x * (frobSq (jacMat (idealVel U p) x) +
        LU / 2 * (idealVel U p x ⬝ᵥ idealVel U p x)) ≤
      d * (LU + Lp) ^ 2 * (∫ x, p x) + LU / 2 * relFisher U p := by
  have hfrob : Integrable fun x => p x * frobSq (jacMat (idealVel U p) x) :=
    hp_int.mul_bdd (c := d * (LU + Lp) ^ 2)
      (measurable_frobSq_jacMat _).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (frobSq_nonneg _)]
        exact frobSq_jacMat_le hv' x)
  have hv2 : Integrable fun x => p x * (idealVel U p x ⬝ᵥ idealVel U p x) :=
    hF.congr (Eventually.of_forall fun x => by
      simp only
      rw [idealVel_dotProduct_self, mul_comm])
  have hL : Integrable fun x => p x * (frobSq (jacMat (idealVel U p) x) +
      LU / 2 * (idealVel U p x ⬝ᵥ idealVel U p x)) :=
    (hfrob.add (hv2.const_mul (LU / 2))).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have hR : Integrable fun x => d * (LU + Lp) ^ 2 * p x +
      LU / 2 * (((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x) :=
    (hp_int.const_mul _).add (hF.const_mul _)
  refine (integral_mono hL hR fun x => ?_).trans_eq ?_
  · have h1 := mul_le_mul_of_nonneg_left (frobSq_jacMat_le hv' x) (hp x)
    have h2 := idealVel_dotProduct_self (U := U) (p := p) x
    simp only
    rw [h2]
    nlinarith
  · rw [integral_add (hp_int.const_mul _) (hF.const_mul _), integral_const_mul,
      integral_const_mul, relFisher]

/-! ### Descent for the ideal velocity -/

/-- **DT-1 for the ideal velocity, dimension `d` (density level, Stein form).** Target
`π = e^{-U}/Z` on `Fin d → ℝ` (`Z > 0`) with `U`, `DU` differentiable and
`‖D(∇U)(z)‖ ≤ L_U`; current density `p > 0`, Lebesgue integrable, differentiable, with
`log p` and `D log p` differentiable and `‖D(∇log p)(z)‖ ≤ L_p` (operator norms for the sup
norm on `Fin d → ℝ`). Let `v = -(∇U + ∇log p)` be the ideal velocity, so `‖Dv‖ ≤ L_U + L_p`
and `Dv` is symmetric; take `0 ≤ η` with `η (L_U + L_p) ≤ 1/2`, `T = id + η v` and
`q = pushDensity η v p` (the density of `T#(p dx)`). Assume `p log(p/π)`, `p (U∘T - U)`, the
Fisher integrand `‖∇log p + ∇U‖² p`, and for every `i` `vᵢ (∇log p)ᵢ p` and `p vᵢ` are Lebesgue
integrable. Then
`∫ q log(q/π) ≤ ∫ p log(p/π) - η I(ρ‖π) + η² ∫ p (‖Dv‖_F² + (L_U/2) ‖v‖²)`,
`I(ρ‖π) = ∫ ‖∇log p + ∇U‖² p` (`relFisher`). -/
theorem integral_pushDensity_klIntegrand_le_idealVel (hη : 0 ≤ η)
    (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z) (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (fderiv ℝ U)) (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ LU)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hpd : Differentiable ℝ p)
    (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x)))
    (hsH : ∀ z, ‖fderiv ℝ (score p) z‖ ≤ Lp)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η (idealVel U p) x) - U x))
    (hF : Integrable fun x => ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x)
    (hvs : ∀ i, Integrable fun x => idealVel U p x i * score p x i * p x)
    (hflux : ∀ i, Integrable fun x => p x * idealVel U p x i) :
    ∫ y, pushDensity η (idealVel U p) p y *
        Real.log (pushDensity η (idealVel U p) p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) - η * relFisher U p +
        η ^ 2 * ∫ x, p x * (frobSq (jacMat (idealVel U p) x) +
          LU / 2 * (idealVel U p x ⬝ᵥ idealVel U p x)) := by
  have hℓ : Differentiable ℝ fun x => Real.log (p x) := fun x => (hpd x).log (hp x).ne'
  have h := integral_pushDensity_klIntegrand_le_stein (differentiable_idealVel hU' hℓ')
    (norm_fderiv_idealVel_le hU' hℓ' hUH hsH) hη hηL (isSymm_jacMat_idealVel hU hU' hℓ hℓ')
    hp hp_int hpd hZ hU hU' (fderiv_fderiv_apply_le hU hU' hUH) hKL hUT
    (integrable_mul_grad_dotProduct_idealVel hF hvs)
    (hF.congr (Eventually.of_forall fun x => by
      simp only
      rw [idealVel_dotProduct_self, mul_comm])) hvs hflux
  have e : ∫ x, (idealVel U p x ⬝ᵥ (score p x + grad U x)) * p x = -relFisher U p := by
    rw [relFisher, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [idealVel_dotProduct_score_add, neg_mul]
  rw [e] at h
  linarith

/-- **DT-1 for the ideal velocity, dimension `d`, explicit constants (density level).** Under
the hypotheses of `integral_pushDensity_klIntegrand_le_idealVel` and `∫ p = 1`,
`∫ q log(q/π) ≤ ∫ p log(p/π) - η (1 - η L_U / 2) I(ρ‖π) + η² d (L_U + L_p)²`
for every `0 ≤ η` with `η (L_U + L_p) ≤ 1/2` (second-order constant linear in `d`). -/
theorem integral_pushDensity_klIntegrand_le_idealVel' (hη : 0 ≤ η)
    (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z) (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (fderiv ℝ U)) (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ LU)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hp_one : ∫ x, p x = 1)
    (hpd : Differentiable ℝ p)
    (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x)))
    (hsH : ∀ z, ‖fderiv ℝ (score p) z‖ ≤ Lp)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η (idealVel U p) x) - U x))
    (hF : Integrable fun x => ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x)
    (hvs : ∀ i, Integrable fun x => idealVel U p x i * score p x i * p x)
    (hflux : ∀ i, Integrable fun x => p x * idealVel U p x i) :
    ∫ y, pushDensity η (idealVel U p) p y *
        Real.log (pushDensity η (idealVel U p) p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
        η * (1 - η * LU / 2) * relFisher U p + η ^ 2 * (d * (LU + Lp) ^ 2) := by
  have h := integral_pushDensity_klIntegrand_le_idealVel hη hηL hZ hU hU' hUH hp hp_int hpd
    hℓ' hsH hKL hUT hF hvs hflux
  have h2 := integral_secondOrder_le (fun x => (hp x).le)
    hp_int (norm_fderiv_idealVel_le hU' hℓ' hUH hsH) hF
  rw [hp_one, mul_one] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg η)
  nlinarith

/-- **DT-1 for the ideal velocity, dimension `d` (Mathlib `klDiv`).** Let `ρ = p dx` and
`π = e^{-U}/Z dx` be probability measures on `Fin d → ℝ` (`Z > 0`); `p > 0` measurable and
differentiable with `log p`, `D log p` differentiable and `‖D(∇log p)‖ ≤ L_p`; `U`, `DU`
differentiable with `‖D(∇U)‖ ≤ L_U` (operator norms for the sup norm). Let
`v = -(∇U + ∇log p)` be the ideal velocity, `0 ≤ η` with `η (L_U + L_p) ≤ 1/2`, and
`T = id + η v`. Assume `p log(p/π)`, `p (U∘T - U)`, `‖∇log p + ∇U‖² p`, and for every `i`
`vᵢ (∇log p)ᵢ p` and `p vᵢ` are Lebesgue integrable. Then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η (1 - η L_U / 2) I(ρ‖π) + η² d (L_U + L_p)²`,
with `I(ρ‖π) = ∫ ‖∇log p + ∇U‖² p` the relative Fisher information (`relFisher`); the
second-order constant is linear in the dimension (`‖Dv‖_F² ≤ d ‖Dv‖²`,
`DeterministicStepPi.frobSq_le_mul_dim`). -/
theorem klDiv_map_step_idealVel_le (hη : 0 ≤ η) (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hUH : ∀ z, ‖fderiv ℝ (grad U) z‖ ≤ LU) (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hpd : Differentiable ℝ p) (hℓ' : Differentiable ℝ (fderiv ℝ fun x => Real.log (p x)))
    (hsH : ∀ z, ‖fderiv ℝ (score p) z‖ ≤ Lp)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η (idealVel U p) x) - U x))
    (hF : Integrable fun x => ((score p x + grad U x) ⬝ᵥ (score p x + grad U x)) * p x)
    (hvs : ∀ i, Integrable fun x => idealVel U p x i * score p x i * p x)
    (hflux : ∀ i, Integrable fun x => p x * idealVel U p x i) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (1 - η * LU / 2) * relFisher U p + η ^ 2 * (d * (LU + Lp) ^ 2) := by
  have hp_int := MeasureHelpers.integrable_of_isProbabilityMeasure (μ := volume) hp_meas
    fun x => (hp x).le
  have hp_one : ∫ x, p x = 1 := by
    have h1 : ∫⁻ x, ENNReal.ofReal (p x) = 1 := by
      rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, measure_univ]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (hp x).le)
      hp_meas.aestronglyMeasurable, h1, ENNReal.toReal_one]
  have hℓ : Differentiable ℝ fun x => Real.log (p x) := fun x => (hpd x).log (hp x).ne'
  have hv := differentiable_idealVel hU' hℓ'
  have hv' := norm_fderiv_idealVel_le hU' hℓ' hUH hsH
  exact klDiv_map_step_le_of_integral_le hv hv' hη hηL hp hp_meas hZ hU.continuous hKL
    (integral_pushDensity_klIntegrand hv hv' hη hηL (isSymm_jacMat_idealVel hU hU' hℓ hℓ') hp
      hp_int hZ hKL hUT).1
    (integral_pushDensity_klIntegrand_le_idealVel' hη hηL hZ hU hU' hUH hp hp_int hp_one hpd
      hℓ' hsH hKL hUT hF hvs hflux)

end Positive

/-! ### Negative result: isotropic Gaussian current laws -/

section Gaussian

/-- The standard quadratic potential `U₀(x) = ‖x‖²/2 = ∑ᵢ xᵢ²/2` on `Fin d → ℝ`, whose Gibbs
measure is `N(0, I)` (`gaussianPDFPi_one_eq_gibbsDensity`). -/
noncomputable def stdPotential (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2 / 2

/-- The isotropic Gaussian density `x ↦ ∏ᵢ N(0, s)(xᵢ)` on `Fin d → ℝ` (variance `s`), the
product of the one-dimensional densities `gaussianPDFReal 0 s` of the factors of
`N(0, s I) = Measure.pi fun _ => gaussianReal 0 s`. -/
noncomputable def gaussianPDFPi (s : ℝ≥0) (x : Fin d → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 s (x i)

/-- **Gradient of a separable function.** For differentiable `f : ℝ → ℝ`,
`∇(x ↦ ∑ᵢ f(xᵢ))(x) = (f'(xᵢ))ᵢ`. -/
theorem grad_sum_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : Fin d → ℝ) :
    grad (fun y : Fin d → ℝ => ∑ i, f (y i)) x = fun i => deriv f (x i) := by
  have hF : HasFDerivAt (fun y : Fin d → ℝ => ∑ i, f (y i))
      (∑ i, deriv f (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x :=
    HasFDerivAt.fun_sum fun i _ =>
      (hf (x i)).hasDerivAt.hasFDerivAt.comp x (hasFDerivAt_apply i x) |>.congr_fderiv (by
        ext w; simp [mul_comm])
  funext i
  simp only [grad, partialDeriv, hF.fderiv]
  simp [Pi.single_apply]

/-- Separable `log` of the Gaussian product density. -/
theorem log_gaussianPDFPi {s : ℝ≥0} (hs : s ≠ 0) :
    (fun x => Real.log (gaussianPDFPi (d := d) s x)) = fun x =>
      ∑ i, Real.log (gaussianPDFReal 0 s (x i)) := by
  funext x
  rw [gaussianPDFPi, Real.log_prod (fun i _ => (gaussianPDFReal_pos 0 s (x i) hs).ne')]

/-- The log of the 1D Gaussian density is differentiable (it is a quadratic polynomial). -/
theorem differentiable_log_gaussianPDFReal {s : ℝ≥0} (hs : s ≠ 0) :
    Differentiable ℝ fun t => Real.log (gaussianPDFReal 0 s t) := by
  have : (fun t => Real.log (gaussianPDFReal 0 s t)) =
      fun t => -Real.log (2 * Real.pi * s) / 2 - (t - 0) ^ 2 / (2 * s) :=
    funext (GaussianFlowVsOU.log_gaussianPDFReal 0 hs)
  rw [this]
  fun_prop

/-- The score of `N(0, sI)` is `x ↦ -x/s`. -/
theorem score_gaussianPDFPi {s : ℝ≥0} (hs : s ≠ 0) :
    score (gaussianPDFPi (d := d) s) = fun x => (-(s : ℝ)⁻¹) • x := by
  funext x
  rw [score, log_gaussianPDFPi hs, grad_sum_comp (differentiable_log_gaussianPDFReal hs) x]
  funext i
  have h := score1_gaussianPDFReal 0 hs (x i)
  rw [score1] at h
  rw [h]
  simp only [sub_zero, Pi.smul_apply, smul_eq_mul]
  ring

/-- The standard Gaussian density on `Fin d → ℝ` is the Gibbs density of `U₀ = ‖x‖²/2` with
`Z = (√(2π))^d`: `∏ᵢ N(0, 1)(xᵢ) = e^{-U₀(x)} / (2π)^{d/2}`. -/
theorem gaussianPDFPi_one_eq_gibbsDensity :
    gaussianPDFPi (d := d) 1 = gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) := by
  funext x
  simp only [gaussianPDFPi, IdealVelocityStep.gaussianPDFReal_zero_one_eq_gibbsDensity,
    DeterministicStep.gibbsDensity, gibbsDensity, stdPotential]
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.sum_neg_distrib]

/-- **Ideal velocity between isotropic Gaussians.** For the target `N(0, I)` (`U₀ = ‖x‖²/2`)
and current density `∏ᵢ N(0, s)(xᵢ)` with `s ≠ 0`, the ideal velocity acts coordinatewise as
the one-dimensional one, `vᵢ(x) = v¹(xᵢ)` (`IdealVelocityStep.idealVel`), and is linear:
`v(x) = (1/s - 1) x`. -/
theorem idealVel_gaussianPi {s : ℝ≥0} (hs : s ≠ 0) (x : Fin d → ℝ) (i : Fin d) :
    idealVel stdPotential (gaussianPDFPi s) x i =
      IdealVelocityStep.idealVel (fun y => y ^ 2 / 2) (gaussianPDFReal 0 s) (x i) := by
  have hpos : ∀ y, 0 < gaussianPDFReal 0 s y := fun y => gaussianPDFReal_pos _ _ _ hs
  have hgd : Differentiable ℝ (gaussianPDFReal 0 s) := by
    intro y
    unfold gaussianPDFReal
    fun_prop
  have hlog : (fun y : Fin d → ℝ => Real.log (gaussianPDFPi s y)) =
      fun y => ∑ i, Real.log (gaussianPDFReal 0 s (y i)) := by
    funext y
    exact Real.log_prod fun i _ => (hpos (y i)).ne'
  have hscore : score (gaussianPDFPi s) x = fun i => score1 (gaussianPDFReal 0 s) (x i) := by
    rw [score, hlog, grad_sum_comp (fun y => (hgd y).log (hpos y).ne')]
    rfl
  have hU : grad stdPotential x = fun i => deriv (fun y : ℝ => y ^ 2 / 2) (x i) :=
    grad_sum_comp (f := fun y : ℝ => y ^ 2 / 2) (by fun_prop) x
  simp only [idealVel, IdealVelocityStep.idealVel, hscore, hU, Pi.neg_apply, Pi.add_apply]

/-- The Gaussian ideal velocity is linear: `v(x) = (1/s - 1) x` for `s ≠ 0`. -/
theorem idealVel_gaussianPi_eq {s : ℝ≥0} (hs : s ≠ 0) :
    idealVel stdPotential (gaussianPDFPi (d := d) s) = fun x => (1 / (s : ℝ) - 1) • x := by
  funext x i
  rw [idealVel_gaussianPi hs, IdealVelocityStep.idealVel_gaussian hs]
  rfl

/-- The `d`-dimensional Gaussian step acts coordinatewise as the one-dimensional one:
`(x + η v(x))ᵢ = T¹(xᵢ)` with `T¹ = DeterministicStep.step η v¹`. -/
theorem step_idealVel_gaussianPi {s : ℝ≥0} (hs : s ≠ 0) (η : ℝ) :
    step η (idealVel stdPotential (gaussianPDFPi (d := d) s)) = fun x i =>
      DeterministicStep.step η
        (IdealVelocityStep.idealVel (fun y => y ^ 2 / 2) (gaussianPDFReal 0 s)) (x i) := by
  funext x i
  simp only [step, DeterministicStep.step, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    idealVel_gaussianPi hs]

/-- **A fixed step size cannot work uniformly over current laws (dimension `d ≥ 1`).** Target
`π = N(0, I) = ⊗ᵢ N(0, 1)` on `Fin d → ℝ` (potential `U₀ = ‖x‖²/2`). For **every** step size
`η > 0` there is a variance `s > 0` such that, for the current law `ρ = N(0, s I)` with density
`∏ᵢ N(0, s)(xᵢ)` and its ideal velocity `v(x) = (1/s - 1) x` (`idealVel_gaussianPi_eq`), the
step-size condition of DT-1 fails (`η |1/s - 1| > 1/2`) and the deterministic step
`T = id + η v` strictly **increases** the KL divergence: `KL(ρ ‖ π) < KL(T#ρ ‖ π)` (Mathlib
`klDiv`). Proof: `T` acts coordinatewise, KL tensorises over the product
(`GaussianIncrement.klDiv_pi_pi`), so both sides are `d` times the one-dimensional KLs of
`IdealVelocityStep.exists_klDiv_map_step_idealVel_gt`. -/
theorem exists_klDiv_map_step_idealVel_gt (hd : 0 < d) {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ≥0, s ≠ 0 ∧ 1 / 2 < η * |1 / (s : ℝ) - 1| ∧
      klDiv (Measure.pi fun _ : Fin d => gaussianReal 0 s)
          (Measure.pi fun _ : Fin d => gaussianReal 0 1) <
        klDiv ((Measure.pi fun _ : Fin d => gaussianReal 0 s).map
            (step η (idealVel stdPotential (gaussianPDFPi s))))
          (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  obtain ⟨s, hs, hηs, hlt⟩ := IdealVelocityStep.exists_klDiv_map_step_idealVel_gt hη
  refine ⟨s, hs, hηs, ?_⟩
  set T := DeterministicStep.step η
    (IdealVelocityStep.idealVel (fun y => y ^ 2 / 2) (gaussianPDFReal 0 s)) with hT
  have hTm : Measurable T := by
    have e : T = fun x => (1 + η * (1 / (s : ℝ) - 1)) * x := by
      funext x
      rw [hT, DeterministicStep.step, IdealVelocityStep.idealVel_gaussian hs]
      ring
    rw [e]
    exact measurable_const.mul measurable_id
  have : IsProbabilityMeasure ((gaussianReal 0 s).map T) :=
    (Measure.isProbabilityMeasure_map_iff hTm.aemeasurable).2 inferInstance
  rw [step_idealVel_gaussianPi hs, ← hT,
    Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal 0 s) (fun _ => hTm.aemeasurable),
    GaussianIncrement.klDiv_pi_pi, GaussianIncrement.klDiv_pi_pi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (ENNReal.mul_lt_mul_iff_right (by exact_mod_cast hd.ne')
    (ENNReal.natCast_ne_top d)).2 hlt

end Gaussian

end FormalizeSampling.IdealVelocityStepPi
