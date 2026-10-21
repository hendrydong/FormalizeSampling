module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.Separation.CompletelyRegular
public import FormalizeSampling.Flow.DeterministicStep
public import FormalizeSampling.Identities.KLTransportVariation

/-!
# DT-1: descent lemma for one deterministic transport step (dimension `d`)

Registry ID: **DT-1** (`docs/blueprint.md`), `d`-dimensional form. The one-dimensional version
is `FormalizeSampling.Flow.DeterministicStep`; this file reuses its scalar inequalities
`sub_sq_le_log_one_add` and `le_quadratic_of_deriv2_le`.

## Setting

* State space `Fin d → ℝ` with Lebesgue `volume` (library convention). Mathlib's norm on it is
  the sup norm, so `‖Dv(x)‖` below is the operator norm `ℓ∞ → ℓ∞` (max absolute row sum of the
  Jacobian). Fréchet derivatives do not depend on this choice; the hypothesis `‖Dv‖ ≤ Lv` does.
  For a symmetric Jacobian it implies the Euclidean bound `‖Dv‖₂ ≤ Lv` (spectral radius ≤ any
  induced norm), which is all the log-determinant bound uses. `EuclideanSpace` was not needed:
  the change-of-variables and inverse-function APIs are norm-agnostic.
* Target `π = e^{-U}/Z` (`gibbsDensity U Z`), `Z > 0`, `U` and `DU` differentiable with
  `D²U(z)(h, h) ≤ L ‖h‖²` (Euclidean `h ⬝ᵥ h`), i.e. `∇²U ≼ L I`.
* Current law `ρ = p dx`, `p > 0`.
* Velocity `v` differentiable, `‖Dv(x)‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`; step `T = id + η v`
  (`step η v`), Jacobian matrix `Dv(x)` (`jacMat v x`, entries `∂ⱼ vᵢ`), Jacobian determinant
  `det(I + η Dv(x))` (`stepJac η v x`).
* For the entropy identity and the descent bound: **symmetric Jacobian**
  `(jacMat v x).IsSymm` for all `x`. This holds for gradient fields `v = ∇φ` with `φ`, `Dφ`
  differentiable (`isSymm_jacMat_grad`), e.g. the ideal velocity `-∇log(p/π)` (preconditioner
  `H = I`).

## Results

1. `injective_step`, `surjective_step`, `bijective_step`, `continuous_stepInv`: `T` is a bijection
   with continuous inverse (global inverse function theorem
   `ApproximatesLinearOn.toHomeomorph`, since `‖η Dv‖ ≤ 1/2`). No symmetry needed.
2. `map_withDensity_step`: **push-forward density** `T#(p dx) = q dy`,
   `q(T x) = p(x)/|det(I + η Dv(x))|`; `integral_eq_integral_abs_stepJac_mul` (change of
   variables). No symmetry needed.
3. `trace_sub_frobSq_le_log_det`: **log-determinant bound** `tr A - ‖A‖_F² ≤ log det(I + A)` for
   symmetric `A` with `‖A‖ ≤ 1/2` (spectral theorem + `t - t² ≤ log(1+t)`);
   `log_stepJac_ge`: `η div v - η² ‖Dv‖_F² ≤ log det(I + η Dv)`.
4. `le_quadratic_of_fderiv2_le`: `U(y) ≤ U(x) + ∇U(x) ⬝ᵥ (y-x) + (L/2)‖y-x‖²` from
   `D²U ≤ L` (derived, not assumed).
5. `integral_pushDensity_klIntegrand`: **entropy identity**
   `∫ q log(q/π) = ∫ p log(p/π) - ∫ p log det(I + η Dv) + ∫ p (U∘T - U)`; for any step with
   `det(I + η Dv) > 0` and bounded `log det(I + η Dv)` it is
   `integral_pushDensity_klIntegrand_of_stepJac`.
6. `integral_pushDensity_klIntegrand_le` (**DT-1, density level**):
   `∫ q log(q/π) ≤ ∫ p log(p/π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (‖Dv‖_F² + (L/2)‖v‖²)`,
   the case `c = 1` of `integral_pushDensity_klIntegrand_le_of_log_stepJac_ge`, which derives the
   bound with `c ‖Dv‖_F²` from any log-determinant bound
   `η div v - c η² ‖Dv‖_F² ≤ log det(I + η Dv)`;
   `integral_pushDensity_klIntegrand_le_stein`: Stein form with first-order term
   `η ∫ (v ⬝ᵥ (∇log p + ∇U)) p`.
7. `klDiv_map_step_le` (**DT-1, Mathlib `klDiv`**): `KL(T#ρ ‖ π) < ∞` and
   `KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (‖Dv‖_F² + (L/2)‖v‖²)`;
   `klDiv_map_step_le_of_integral_le` turns any density-level bound into this form.
8. `frobSq_le_mul_dim`, `frobSq_jacMat_le`: `‖A‖_F² ≤ d L²` when `‖A w‖ ≤ L ‖w‖` (sup norm),
   hence `‖Dv‖_F² ≤ d Lv²` (via the row-sum bound `sum_abs_le_of_norm_mulVec_le`).

## NOT proved here

* The log-determinant bound, entropy identity and descent bound assume a **symmetric**
  Jacobian. For general `A` with `‖A‖ ≤ 1/2`, `log det(I + A) ≥ tr A - ‖A‖_F²` is true (complex
  eigenvalues and Schur's inequality `∑ |λᵢ|² ≤ ‖A‖_F²`) but is not formalised here; a
  non-sharp version (constant 13) is `DeterministicStepGeneral.trace_sub_frobSq_le_log_det`.
* The ideal velocity is not treated here; for `‖Dv‖ ≤ Lv` see
  `IdealVelocityStepPi.norm_fderiv_idealVel_le`.
-/

@[expose] public section

open MeasureTheory Set Filter Matrix
open scoped ENNReal NNReal

namespace FormalizeSampling.DeterministicStepPi

variable {d : ℕ}

/-! ### Definitions and basic calculus -/

/-- The deterministic transport step `T(x) = x + η v(x)` on `Fin d → ℝ`, of step size `η`
along the vector field `v`. -/
def step (η : ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ := x + η • v x

/-- The Jacobian matrix `Dv(x)` of `v` at `x`: the matrix of the Fréchet derivative
`fderiv ℝ v x` in the standard basis, `jacMat v x i j = ∂ⱼ vᵢ(x)` (`jacMat_apply`). It is `0`
where `v` is not differentiable. -/
noncomputable def jacMat (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toMatrix' (fderiv ℝ v x : (Fin d → ℝ) →ₗ[ℝ] Fin d → ℝ)

/-- The Jacobian determinant `det(I + η Dv(x))` of the step `T = id + η v`. It is the
determinant of the Fréchet derivative of `T` when `v` is differentiable (`stepJac_eq_det`,
`hasFDerivAt_step`). -/
noncomputable def stepJac (η : ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  (1 + η • jacMat v x).det

/-- The inverse `T⁻¹` of the step, defined as `Function.invFun (step η v)`. It is a two-sided
inverse when `T` is bijective (`bijective_step`: `v` differentiable, `‖Dv‖ ≤ Lv`, `η ≥ 0`,
`η Lv ≤ 1/2`). -/
noncomputable def stepInv (η : ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) : (Fin d → ℝ) → Fin d → ℝ :=
  Function.invFun (step η v)

/-- The push-forward density `q(y) = p(T⁻¹ y) / |det(I + η Dv(T⁻¹ y))|` of `p dx` under
`T = id + η v`; it is the Lebesgue density of `T#(p dx)` under the hypotheses of
`map_withDensity_step`. -/
noncomputable def pushDensity (η : ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) (p : (Fin d → ℝ) → ℝ)
    (y : Fin d → ℝ) : ℝ :=
  p (stepInv η v y) / |stepJac η v (stepInv η v y)|

/-- The Gibbs density `π(x) = e^{-U(x)} / Z` on `Fin d → ℝ` (a probability density iff
`Z = ∫ e^{-U}`). -/
noncomputable def gibbsDensity (U : (Fin d → ℝ) → ℝ) (Z : ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (-U x) / Z

/-- The squared Frobenius norm `‖A‖_F² = ∑ᵢ ∑ⱼ Aᵢⱼ²` of a real square matrix. -/
def frobSq (A : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- Entries of the Jacobian matrix: `jacMat v x i j = (Dv(x) eⱼ)ᵢ = ∂ⱼ vᵢ(x)`. -/
theorem jacMat_apply (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) (i j : Fin d) :
    jacMat v x i j = fderiv ℝ v x (Pi.single j 1) i := by
  simp [jacMat, LinearMap.toMatrix'_apply]

/-- The Jacobian matrix acts as the Fréchet derivative: `Dv(x) *ᵥ w = fderiv ℝ v x w`. -/
theorem jacMat_mulVec (v : (Fin d → ℝ) → Fin d → ℝ) (x w : Fin d → ℝ) :
    jacMat v x *ᵥ w = fderiv ℝ v x w := by
  simp [jacMat, LinearMap.toMatrix'_mulVec]

/-- `stepJac η v x` is the determinant of the continuous linear map `id + η • Dv(x)`. -/
theorem stepJac_eq_det (η : ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    stepJac η v x = (ContinuousLinearMap.id ℝ (Fin d → ℝ) + η • fderiv ℝ v x).det := by
  rw [stepJac, ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1
  simp [jacMat, map_add, map_smul, LinearMap.toMatrix'_id]

/-- Derivative of the step: if `v` is differentiable, `T = id + η v` has Fréchet derivative
`id + η Dv(x)` at every `x`. -/
theorem hasFDerivAt_step {η : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} (hv : Differentiable ℝ v)
    (x : Fin d → ℝ) :
    HasFDerivAt (step η v) (ContinuousLinearMap.id ℝ (Fin d → ℝ) + η • fderiv ℝ v x) x :=
  (hasFDerivAt_id x).add ((hv x).hasFDerivAt.const_smul η)

/-- The step `T = id + η v` is differentiable when `v` is. -/
theorem differentiable_step {η : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} (hv : Differentiable ℝ v) :
    Differentiable ℝ (step η v) := fun x => (hasFDerivAt_step hv x).differentiableAt

/-- For differentiable `v`, the trace of the Jacobian matrix is the divergence:
`tr Dv(x) = div v(x)` (the library's `divergence`). -/
theorem trace_jacMat {v : (Fin d → ℝ) → Fin d → ℝ} (hv : Differentiable ℝ v)
    (x : Fin d → ℝ) : (jacMat v x).trace = divergence v x := by
  simp only [trace, diag_apply, jacMat_apply, divergence, partialDeriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hasFDerivAt_pi'.1 (hv x).hasFDerivAt i).fderiv]
  rfl

/-- Every Jacobian entry is bounded by the operator norm (for the sup norm on `Fin d → ℝ`):
`|∂ⱼ vᵢ(x)| ≤ ‖Dv(x)‖`. -/
theorem abs_jacMat_le {v : (Fin d → ℝ) → Fin d → ℝ} (x : Fin d → ℝ) (i j : Fin d) :
    |jacMat v x i j| ≤ ‖fderiv ℝ v x‖ := by
  rw [jacMat_apply, ← Real.norm_eq_abs]
  refine (norm_le_pi_norm _ i).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
  rw [Pi.norm_single, norm_one, mul_one]

/-- Each Jacobian entry `x ↦ ∂ⱼ vᵢ(x)` is measurable (for every `v`). -/
theorem measurable_jacMat_apply (v : (Fin d → ℝ) → Fin d → ℝ) (i j : Fin d) :
    Measurable fun x => jacMat v x i j := by
  simp_rw [jacMat_apply]
  exact measurable_pi_iff.1 (measurable_fderiv_apply_const ℝ v (Pi.single j 1)) i

/-- The Jacobian determinant `x ↦ det(I + η Dv(x))` is measurable (for every `v`). -/
theorem measurable_stepJac (η : ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) :
    Measurable (stepJac η v) := by
  have h : ∀ i j, Measurable fun x => (1 + η • jacMat v x) i j := fun i j => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.add (measurable_const.mul (measurable_jacMat_apply v i j))
  unfold stepJac
  simp_rw [det_apply']
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => h _ _)


/-! ### Spectral facts and the log-determinant inequality -/

/-- For a symmetric real matrix `A` with eigenvalues `λᵢ`, `det(I + A) = ∏ᵢ (1 + λᵢ)`
(spectral theorem). -/
theorem det_one_add_eq_prod {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    (1 + A).det = ∏ i, (1 + hA.eigenvalues i) := by
  set U : Matrix (Fin d) (Fin d) ℝ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self _
  have hA' := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hA'
  have h1 : 1 + A = U * (1 + diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * star U := by
    conv_lhs => rw [hA']
    rw [mul_add, add_mul, mul_one, hUU]
  rw [h1, det_mul_comm, ← mul_assoc, hUU', one_mul, ← diagonal_one, diagonal_add, det_diagonal]
  simp

/-- For a symmetric real matrix `A` with eigenvalues `λᵢ`, `‖A‖_F² = tr(A²) = ∑ᵢ λᵢ²`. -/
theorem frobSq_eq_sum_sq {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    frobSq A = ∑ i, hA.eigenvalues i ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℝ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self _
  have hA' := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hA'
  set D : Matrix (Fin d) (Fin d) ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have htr : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
    have : A * A = U * (D * D) * star U := by
      conv_lhs => rw [hA']
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hUU', one_mul]
    rw [this, trace_mul_cycle, hUU', one_mul, diagonal_mul_diagonal, trace_diagonal]
    simp [sq]
  rw [← htr, frobSq, trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : A j i = A i j := by
    have := congrFun (congrFun hA.eq i) j
    simpa using this
  rw [this, sq]

/-- If `‖A w‖ ≤ c ‖w‖` for all `w` (any norm; here the sup norm of `Fin d → ℝ`), then every
eigenvalue of the symmetric matrix `A` satisfies `|λᵢ| ≤ c`. -/
theorem abs_eigenvalues_le {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ c * ‖w‖) (i : Fin d) : |hA.eigenvalues i| ≤ c := by
  have hev := hA.mulVec_eigenvectorBasis i
  set w : Fin d → ℝ := ⇑(hA.eigenvectorBasis i)
  have hw : w ≠ 0 := by
    intro h
    have h1 := hA.eigenvectorBasis.orthonormal.1 i
    have : hA.eigenvectorBasis i = 0 := by
      ext j; simpa [w] using congrFun h j
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have := hc w
  rw [hev, norm_smul, Real.norm_eq_abs] at this
  exact le_of_mul_le_mul_right this hpos


/-- For `|t| ≤ 1/2`, `|log(1 + t)| ≤ 1`. -/
theorem abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t)| ≤ 1 := by
  have h1 := DeterministicStep.sub_sq_le_log_one_add ht
  obtain ⟨htl, htu⟩ := abs_le.1 ht
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
  rw [abs_le]
  constructor <;> nlinarith

section MatrixIneq

variable {A : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}

/-- For symmetric `A` with `‖A w‖ ≤ c ‖w‖` for all `w` and `c ≤ 1/2`, `det(I + A) > 0`. -/
theorem det_one_add_pos (hA : A.IsHermitian) (hc : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ c * ‖w‖)
    (hc2 : c ≤ 1 / 2) : 0 < (1 + A).det := by
  rw [det_one_add_eq_prod hA]
  refine Finset.prod_pos fun i _ => ?_
  have := abs_le.1 (abs_eigenvalues_le hA hc i)
  linarith [this.1]

/-- **Log-determinant lower bound (symmetric case).** For a symmetric real matrix `A` with
`‖A w‖ ≤ c ‖w‖` for all `w` (sup norm) and `c ≤ 1/2`,
`tr A - ‖A‖_F² ≤ log det(I + A)`. Proof: spectral theorem and the scalar bound
`t - t² ≤ log(1 + t)` for `|t| ≤ 1/2` applied to each eigenvalue. -/
theorem trace_sub_frobSq_le_log_det (hA : A.IsHermitian)
    (hc : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ c * ‖w‖) (hc2 : c ≤ 1 / 2) :
    A.trace - frobSq A ≤ Real.log (1 + A).det := by
  have hev : ∀ i, |hA.eigenvalues i| ≤ 1 / 2 := fun i => (abs_eigenvalues_le hA hc i).trans hc2
  rw [det_one_add_eq_prod hA, Real.log_prod (fun i _ => by
      have := abs_le.1 (hev i); linarith [this.1]),
    hA.trace_eq_sum_eigenvalues, frobSq_eq_sum_sq hA]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => DeterministicStep.sub_sq_le_log_one_add (hev i)

/-- For symmetric `A` with `‖A w‖ ≤ c ‖w‖` for all `w` and `c ≤ 1/2`,
`|log det(I + A)| ≤ d`. -/
theorem abs_log_det_one_add_le (hA : A.IsHermitian)
    (hc : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ c * ‖w‖) (hc2 : c ≤ 1 / 2) :
    |Real.log (1 + A).det| ≤ d := by
  have hev : ∀ i, |hA.eigenvalues i| ≤ 1 / 2 := fun i => (abs_eigenvalues_le hA hc i).trans hc2
  rw [det_one_add_eq_prod hA, Real.log_prod (fun i _ => by
      have := abs_le.1 (hev i); linarith [this.1])]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => abs_log_one_add_le (hev i)).trans ?_
  simp

end MatrixIneq

/-! ### The step map: bijectivity and push-forward density -/

section Step

variable {η Lv : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}

/-- If `‖Dv‖ ≤ Lv`, `η ≥ 0` and `η Lv ≤ 1/2`, then `‖η Dv(x)‖ ≤ 1/2`. -/
theorem norm_smul_fderiv_le (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (x : Fin d → ℝ) : ‖η • fderiv ℝ v x‖ ≤ 1 / 2 := by
  rw [norm_smul, Real.norm_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left (hv' x) hη).trans hηL

/-- Under `v` differentiable, `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`, the step `T = id + η v`
approximates the identity on all of `Fin d → ℝ` with constant `1/2`:
`‖T x - T y - (x - y)‖ ≤ ‖x - y‖/2` (mean value inequality). -/
theorem approximatesLinearOn_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) :
    ApproximatesLinearOn (step η v)
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ)) univ
      (1 / 2 : ℝ≥0) := by
  intro x _ y _
  have hlip : ‖η • v x - η • v y‖ ≤ 1 / 2 * ‖x - y‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := fun z => η • v z)
      (fun z _ => (hv z).const_smul η)
      (fun z _ => by rw [fderiv_fun_const_smul (hv z)]; exact norm_smul_fderiv_le hv' hη hηL z)
      (mem_univ y) (mem_univ x)
  have e : step η v x - step η v y -
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ)) (x - y) =
      η • v x - η • v y := by
    simp only [step, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.refl_apply]
    abel
  rw [e]
  simpa using hlip

/-- The non-degeneracy condition of `ApproximatesLinearOn.toHomeomorph` for the identity and
constant `1/2`: the space is trivial (`d = 0`) or `1/2 < ‖id‖₊⁻¹ = 1`. -/
theorem subsingleton_or_lt :
    Subsingleton (Fin d → ℝ) ∨ (1 / 2 : ℝ≥0) <
      ‖(((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)).symm : (Fin d → ℝ) ≃L[ℝ] Fin d → ℝ) :
        (Fin d → ℝ) →L[ℝ] Fin d → ℝ)‖₊⁻¹ := by
  rcases subsingleton_or_nontrivial (Fin d → ℝ) with h | h
  · exact Or.inl h
  · right
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id]
    norm_num


/-- **(1) Injectivity** of `T = id + η v` (`v` differentiable, `‖Dv‖ ≤ Lv`, `η ≥ 0`,
`η Lv ≤ 1/2`). -/
theorem injective_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Function.Injective (step η v) :=
  fun a b h => (approximatesLinearOn_step hv hv' hη hηL).injOn subsingleton_or_lt
    (mem_univ a) (mem_univ b) h

/-- **(1) Surjectivity** of `T = id + η v` under the hypotheses of `injective_step`
(global inverse function theorem `ApproximatesLinearOn.surjective`). -/
theorem surjective_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Function.Surjective (step η v) :=
  (approximatesLinearOn_step hv hv' hη hηL).surjective subsingleton_or_lt

/-- **(1) Bijectivity** of `T = id + η v` under the hypotheses of `injective_step`. -/
theorem bijective_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Function.Bijective (step η v) :=
  ⟨injective_step hv hv' hη hηL, surjective_step hv hv' hη hηL⟩

/-- `T⁻¹ (T x) = x` under the hypotheses of `injective_step`. -/
theorem stepInv_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (x : Fin d → ℝ) : stepInv η v (step η v x) = x :=
  Function.leftInverse_invFun (injective_step hv hv' hη hηL) x

/-- `T (T⁻¹ y) = y` under the hypotheses of `injective_step`. -/
theorem step_stepInv (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (y : Fin d → ℝ) : step η v (stepInv η v y) = y :=
  Function.rightInverse_invFun (surjective_step hv hv' hη hηL) y

/-- The inverse step `T⁻¹` is continuous (it is the inverse of the homeomorphism
`ApproximatesLinearOn.toHomeomorph`), under the hypotheses of `injective_step`. -/
theorem continuous_stepInv (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) : Continuous (stepInv η v) := by
  set e := (approximatesLinearOn_step hv hv' hη hηL).toHomeomorph (step η v)
    subsingleton_or_lt
  have h : stepInv η v = e.symm := funext fun y => injective_step hv hv' hη hηL <| by
    rw [step_stepInv hv hv' hη hηL]
    exact (e.apply_symm_apply y).symm
  rw [h]
  exact e.symm.continuous

/-- **(2) Push-forward density, pointwise:** `q(T x) = p(x) / |det(I + η Dv(x))|` under the
hypotheses of `injective_step`. -/
theorem pushDensity_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (p : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    pushDensity η v p (step η v x) = p x / |stepJac η v x| := by
  simp only [pushDensity, stepInv_step hv hv' hη hηL]

/-- The push-forward density is measurable when `p` is (hypotheses of `injective_step`). -/
theorem measurable_pushDensity (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) {p : (Fin d → ℝ) → ℝ} (hp : Measurable p) :
    Measurable (pushDensity η v p) := by
  have hi := (continuous_stepInv hv hv' hη hηL).measurable
  exact (hp.comp hi).div ((measurable_stepJac η v).abs.comp hi)

/-- **Change of variables along the step.** Under the hypotheses of `injective_step`, for every
`g`, `∫ g(y) dy = ∫ |det(I + η Dv(x))| g(T x) dx`. -/
theorem integral_eq_integral_abs_stepJac_mul (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (g : (Fin d → ℝ) → ℝ) :
    ∫ y, g y = ∫ x, |stepJac η v x| * g (step η v x) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_step (η := η) hv x).hasFDerivWithinAt)
    (injective_step hv hv' hη hηL).injOn g
  rw [image_univ, (surjective_step hv hv' hη hηL).range_eq] at h
  simp only [Measure.restrict_univ] at h
  rw [h]
  simp [← stepJac_eq_det]

/-- **Integrability along the step.** Under the hypotheses of `injective_step`, `g` is Lebesgue
integrable iff `x ↦ |det(I + η Dv(x))| g(T x)` is. -/
theorem integrable_iff_integrable_abs_stepJac_mul (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (g : (Fin d → ℝ) → ℝ) :
    Integrable g ↔ Integrable fun x => |stepJac η v x| * g (step η v x) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_step (η := η) hv x).hasFDerivWithinAt)
    (injective_step hv hv' hη hηL).injOn g
  rw [image_univ, (surjective_step hv hv' hη hηL).range_eq] at h
  simp only [integrableOn_univ] at h
  rw [h]
  simp [← stepJac_eq_det]

/-- `det(I + η Dv(x)) ≠ 0` whenever `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2` (no symmetry needed:
`I + η Dv(x)` is injective since `‖η Dv(x)‖ ≤ 1/2`). -/
theorem stepJac_ne_zero (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (x : Fin d → ℝ) : stepJac η v x ≠ 0 := by
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [add_mulVec, one_mulVec, smul_mulVec, jacMat_mulVec] at hw
  have h1 : w = -((η • fderiv ℝ v x) w) := by
    rw [_root_.smul_apply]
    exact eq_neg_of_add_eq_zero_left hw
  have h2 : ‖w‖ ≤ 1 / 2 * ‖w‖ := by
    conv_lhs => rw [h1, norm_neg]
    exact ((η • fderiv ℝ v x).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_smul_fderiv_le hv' hη hηL x) (norm_nonneg _))
  exact hw0 (norm_eq_zero.1 (le_antisymm (by linarith [norm_nonneg w]) (norm_nonneg w)))

/-- **(2) Push-forward of the law.** Let `v` be differentiable with `‖Dv‖ ≤ Lv`, `η ≥ 0`,
`η Lv ≤ 1/2` (no symmetry assumption). Then `T#(p dx) = q dy` with `q = pushDensity η v p`,
i.e. `q(T x) = p(x)/|det(I + η Dv(x))|` (negative values of `p` are truncated by `ofReal`). -/
theorem map_withDensity_step (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (p : (Fin d → ℝ) → ℝ) :
    (volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η v) =
      volume.withDensity fun y => ENNReal.ofReal (pushDensity η v p y) := by
  have hTm : Measurable (step η v) := (differentiable_step hv).continuous.measurable
  ext s hs
  rw [Measure.map_apply hTm hs, withDensity_apply _ (hTm hs), withDensity_apply _ hs]
  conv_rhs => rw [← image_preimage_eq s (surjective_step hv hv' hη hηL)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hTm hs)
    (fun x _ => (hasFDerivAt_step (η := η) hv x).hasFDerivWithinAt)
    (injective_step hv hv' hη hηL).injOn]
  refine setLIntegral_congr_fun (hTm hs) fun x _ => ?_
  have hJ : 0 < |stepJac η v x| := abs_pos.2 (stepJac_ne_zero hv' hη hηL x)
  rw [← stepJac_eq_det, pushDensity_step hv hv' hη hηL, ← ENNReal.ofReal_mul hJ.le]
  congr 1
  field_simp

end Step


/-! ### Symmetric Jacobians -/

section Symm

variable {η Lv : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}

/-- If the Jacobian matrix of `v` is symmetric, so is `η Dv(x)` (as a real Hermitian
matrix). -/
theorem isHermitian_smul_jacMat (hsym : ∀ x, (jacMat v x).IsSymm) (x : Fin d → ℝ) :
    (η • jacMat v x).IsHermitian := by
  have h : (η • jacMat v x).IsSymm := (hsym x).smul η
  show (η • jacMat v x)ᴴ = _
  rw [conjTranspose_eq_transpose_of_trivial]
  exact h

/-- Under `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`: `‖η Dv(x) w‖ ≤ ‖w‖/2` for all `w`. -/
theorem norm_smul_jacMat_mulVec_le (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (x w : Fin d → ℝ) :
    ‖(η • jacMat v x) *ᵥ w‖ ≤ 1 / 2 * ‖w‖ := by
  rw [smul_mulVec, jacMat_mulVec, ← _root_.smul_apply]
  exact ((η • fderiv ℝ v x).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (norm_smul_fderiv_le hv' hη hηL x) (norm_nonneg _))

/-- With symmetric Jacobian, `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`:
`det(I + η Dv(x)) > 0`. -/
theorem stepJac_pos (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hsym : ∀ x, (jacMat v x).IsSymm) (x : Fin d → ℝ) : 0 < stepJac η v x :=
  det_one_add_pos (isHermitian_smul_jacMat hsym x) (norm_smul_jacMat_mulVec_le hv' hη hηL x)
    le_rfl

/-- With symmetric Jacobian, `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`:
`|log det(I + η Dv(x))| ≤ d`. -/
theorem abs_log_stepJac_le (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (hsym : ∀ x, (jacMat v x).IsSymm) (x : Fin d → ℝ) :
    |Real.log (stepJac η v x)| ≤ d :=
  abs_log_det_one_add_le (isHermitian_smul_jacMat hsym x)
    (norm_smul_jacMat_mulVec_le hv' hη hηL x) le_rfl

/-- `‖a A‖_F² = a² ‖A‖_F²`. -/
theorem frobSq_smul (a : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    frobSq (a • A) = a ^ 2 * frobSq A := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Log-determinant bound for the step.** If `v` is differentiable with symmetric Jacobian,
`‖Dv‖ ≤ Lv`, `η ≥ 0` and `η Lv ≤ 1/2`, then
`η div v(x) - η² ‖Dv(x)‖_F² ≤ log det(I + η Dv(x))`. -/
theorem log_stepJac_ge (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hsym : ∀ x, (jacMat v x).IsSymm) (x : Fin d → ℝ) :
    η * divergence v x - η ^ 2 * frobSq (jacMat v x) ≤ Real.log (stepJac η v x) := by
  have h := trace_sub_frobSq_le_log_det (isHermitian_smul_jacMat (η := η) hsym x)
    (norm_smul_jacMat_mulVec_le hv' hη hηL x) le_rfl
  rwa [trace_smul, frobSq_smul, trace_jacMat hv, smul_eq_mul] at h

/-- **Gradient fields have symmetric Jacobians.** If `φ` is differentiable and `Dφ` is
differentiable, then `D(∇φ)(x)` is a symmetric matrix (Schwarz,
`second_derivative_symmetric`). So `v = ∇φ` satisfies the symmetry hypothesis below. -/
theorem isSymm_jacMat_grad {φ : (Fin d → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (fderiv ℝ φ)) (x : Fin d → ℝ) : (jacMat (grad φ) x).IsSymm := by
  set f'' := fderiv ℝ (fderiv ℝ φ) x
  have hc : ∀ i : Fin d, HasFDerivAt (fun z => grad φ z i)
      (f''.flip (Pi.single i 1)) x := fun i => by
    have := (hφ' x).hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) x)
    simpa [grad, partialDeriv] using this
  have hg : HasFDerivAt (grad φ)
      (ContinuousLinearMap.pi fun i => f''.flip (Pi.single i 1)) x :=
    hasFDerivAt_pi.2 hc
  refine IsSymm.ext fun i j => ?_
  rw [jacMat_apply, jacMat_apply, hg.fderiv]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.flip_apply]
  exact second_derivative_symmetric (fun y => (hφ y).hasFDerivAt) (hφ' x).hasFDerivAt _ _

end Symm

/-- **Quadratic upper bound from `∇²U ≼ L I`.** If `U` and `DU` are differentiable and
`D²U(z)(h, h) ≤ L ‖h‖²` (Euclidean, `h ⬝ᵥ h`) for all `z h`, then for all `x y`,
`U(y) ≤ U(x) + ∇U(x) ⬝ᵥ (y - x) + (L/2) ‖y - x‖²`. -/
theorem le_quadratic_of_fderiv2_le {U : (Fin d → ℝ) → ℝ} {L : ℝ} (hU : Differentiable ℝ U)
    (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h)) (x y : Fin d → ℝ) :
    U y ≤ U x + grad U x ⬝ᵥ (y - x) + L / 2 * ((y - x) ⬝ᵥ (y - x)) := by
  set h := y - x with hh
  set g : ℝ → ℝ := fun t => U (x + t • h) with hg_def
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • h) h t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hg : ∀ t, HasDerivAt g (fderiv ℝ U (x + t • h) h) t := fun t =>
    (hU _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hg' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ U (x + t • h) h)
      (fderiv ℝ (fderiv ℝ U) (x + t • h) h h) t := fun t => by
    have h1 := (hU' (x + t • h)).hasFDerivAt.clm_apply (hasFDerivAt_const h (x + t • h))
    convert h1.comp_hasDerivAt t (hline t) using 1
    · rfl
    · simp
  have hdg : deriv g = fun t => fderiv ℝ U (x + t • h) h := funext fun t => (hg t).deriv
  have key := DeterministicStep.le_quadratic_of_deriv2_le (U := g) (L := L * (h ⬝ᵥ h))
    (fun t => (hg t).differentiableAt)
    (by rw [hdg]; exact fun t => (hg' t).differentiableAt)
    (fun t => by rw [hdg, (hg' t).deriv]; exact hU'' _ _) 0 1
  rw [hdg] at key
  simp only [hg_def, zero_smul, add_zero, one_smul, sub_zero, mul_one, one_pow] at key
  rw [← fderiv_apply_eq_grad_dotProduct]
  have hy : x + h = y := by rw [hh]; abel
  rw [hy] at key
  linarith


/-! ### Entropy identity and descent inequality -/

section Descent

variable {η Lv L Z : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- The divergence of a differentiable field is measurable. -/
theorem measurable_divergence (hv : Differentiable ℝ v) : Measurable (divergence v) := by
  have h : divergence v = fun x => (jacMat v x).trace := funext fun x => (trace_jacMat hv x).symm
  rw [h]
  simp only [trace, diag_apply]
  exact Finset.measurable_sum _ fun i _ => measurable_jacMat_apply v i i

/-- `|div v(x)| ≤ d Lv` when `v` is differentiable with `‖Dv‖ ≤ Lv`. -/
theorem abs_divergence_le (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (x : Fin d → ℝ) : |divergence v x| ≤ d * Lv := by
  rw [← trace_jacMat hv, trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => (abs_jacMat_le x i i).trans (hv' x)).trans ?_
  simp

/-- `‖A‖_F² ≥ 0`. -/
theorem frobSq_nonneg (A : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Row sums bounded by the `ℓ∞` operator norm.** If `‖A w‖ ≤ L ‖w‖` for all `w` (sup norm on
`Fin d → ℝ`) and `0 ≤ L`, then every absolute row sum satisfies `∑ⱼ |Aᵢⱼ| ≤ L`. -/
theorem sum_abs_le_of_norm_mulVec_le {A : Matrix (Fin d) (Fin d) ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ L * ‖w‖) (i : Fin d) : ∑ j, |A i j| ≤ L := by
  set w : Fin d → ℝ := fun j => if 0 ≤ A i j then 1 else -1 with hw
  have hw1 : ‖w‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    simp only [hw]
    split_ifs <;> simp
  have hAw : (A *ᵥ w) i = ∑ j, |A i j| := by
    simp only [mulVec, dotProduct, hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (not_le.1 h)]
  rw [← hAw]
  calc (A *ᵥ w) i ≤ ‖(A *ᵥ w) i‖ := Real.le_norm_self _
    _ ≤ ‖A *ᵥ w‖ := norm_le_pi_norm _ i
    _ ≤ L * ‖w‖ := hL w
    _ ≤ L * 1 := mul_le_mul_of_nonneg_left hw1 hL0
    _ = L := mul_one L

/-- **Frobenius bound linear in the dimension.** If `‖A w‖ ≤ L ‖w‖` for all `w` (sup norm on
`Fin d → ℝ`), then `‖A‖_F² = ∑ᵢⱼ aᵢⱼ² ≤ d L²`. Each entry satisfies `|aᵢⱼ| ≤ L` and each
absolute row sum `∑ⱼ |aᵢⱼ| ≤ L`, so `∑ⱼ aᵢⱼ² ≤ L ∑ⱼ |aᵢⱼ| ≤ L²`. No symmetry is assumed. -/
theorem frobSq_le_mul_dim {A : Matrix (Fin d) (Fin d) ℝ} {L : ℝ}
    (hL : ∀ w : Fin d → ℝ, ‖A *ᵥ w‖ ≤ L * ‖w‖) : frobSq A ≤ d * L ^ 2 := by
  -- entry bound `|aᵢⱼ| ≤ L`, by testing on `eⱼ`
  have hent : ∀ i j, |A i j| ≤ L := fun i j => by
    have h := hL (Pi.single j 1)
    rw [mulVec_single_one, Pi.norm_single, norm_one, mul_one] at h
    exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm (A.col j) i).trans h
  have hrow : ∀ i, ∑ j, A i j ^ 2 ≤ L ^ 2 := fun i => by
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hent i i)
    calc ∑ j, A i j ^ 2 = ∑ j, |A i j| * |A i j| :=
          Finset.sum_congr rfl fun j _ => by rw [← sq, sq_abs]
      _ ≤ ∑ j, L * |A i j| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hent i j) (abs_nonneg _)
      _ = L * ∑ j, |A i j| := (Finset.mul_sum _ _ _).symm
      _ ≤ L * L := mul_le_mul_of_nonneg_left (sum_abs_le_of_norm_mulVec_le hL0 hL i) hL0
      _ = L ^ 2 := (sq L).symm
  refine (Finset.sum_le_sum fun i _ => hrow i).trans ?_
  simp

/-- **Jacobian Frobenius bound, linear in the dimension.** `‖Dv(x)‖_F² ≤ d Lv²` when
`‖Dv‖ ≤ Lv` (operator norm for the sup norm on `Fin d → ℝ`; `frobSq_le_mul_dim`). No symmetry
of `Dv(x)` is needed. -/
theorem frobSq_jacMat_le (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (x : Fin d → ℝ) :
    frobSq (jacMat v x) ≤ d * Lv ^ 2 :=
  frobSq_le_mul_dim fun w => by
    rw [jacMat_mulVec]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hv' x) (norm_nonneg _))

/-- `x ↦ ‖Dv(x)‖_F²` is measurable (for every `v`). -/
theorem measurable_frobSq_jacMat (v : (Fin d → ℝ) → Fin d → ℝ) :
    Measurable fun x => frobSq (jacMat v x) :=
  Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (measurable_jacMat_apply v i j).pow_const 2

/-- Integrability of `p log det(I + η Dv)`, `p div v` and `p ‖Dv‖_F²` for integrable `p`, given
`‖Dv‖ ≤ Lv` and a uniform bound `|log det(I + η Dv(x))| ≤ B`. -/
theorem integrable_stepTerms {B : ℝ} (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hJB : ∀ x, |Real.log (stepJac η v x)| ≤ B)
    (hp_int : Integrable p) :
    Integrable (fun x => p x * Real.log (stepJac η v x)) ∧
      Integrable (fun x => p x * divergence v x) ∧
      Integrable (fun x => p x * frobSq (jacMat v x)) := by
  refine ⟨hp_int.mul_bdd (c := B) (Real.measurable_log.comp
      (measurable_stepJac η v)).aestronglyMeasurable (Eventually.of_forall fun x => ?_),
    hp_int.mul_bdd (c := d * Lv) (measurable_divergence hv).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_),
    hp_int.mul_bdd (c := d * Lv ^ 2) (measurable_frobSq_jacMat v).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)⟩
  · rw [Real.norm_eq_abs]
    exact hJB x
  · rw [Real.norm_eq_abs]
    exact abs_divergence_le hv hv' x
  · rw [Real.norm_eq_abs, abs_of_nonneg (frobSq_nonneg _)]
    exact frobSq_jacMat_le hv' x

/-- Pulled-back KL integrand, for `J = det(I + η Dv) > 0`:
`|J| q(T x) log(q(T x)/π(T x)) = p log(p/π) - p log J + p (U∘T - U)`. -/
private lemma pullback_klIntegrand (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hJ : ∀ x, 0 < stepJac η v x) (hp : ∀ x, 0 < p x) (hZ : 0 < Z) (x : Fin d → ℝ) :
    |stepJac η v x| * (pushDensity η v p (step η v x) *
        Real.log (pushDensity η v p (step η v x) / gibbsDensity U Z (step η v x))) =
      p x * Real.log (p x / gibbsDensity U Z x) - p x * Real.log (stepJac η v x) +
        p x * (U (step η v x) - U x) := by
  have hJx := hJ x
  rw [pushDensity_step hv hv' hη hηL, abs_of_pos hJx, gibbsDensity, gibbsDensity,
    DeterministicStep.log_identity (Ux := U x) (UTx := U (step η v x)) (hp x) hJx hZ]
  field_simp

/-- **Entropy identity for a step with positive Jacobian determinant.** The conclusion of
`integral_pushDensity_klIntegrand`, with the symmetry hypothesis replaced by
`det(I + η Dv(x)) > 0` and `|log det(I + η Dv(x))| ≤ B` for all `x`. -/
theorem integral_pushDensity_klIntegrand_of_stepJac {B : ℝ} (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hJ : ∀ x, 0 < stepJac η v x) (hJB : ∀ x, |Real.log (stepJac η v x)| ≤ B)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hZ : 0 < Z)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x)) :
    Integrable (fun y => pushDensity η v p y *
        Real.log (pushDensity η v p y / gibbsDensity U Z y)) ∧
      ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) =
        (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
          (∫ x, p x * Real.log (stepJac η v x)) + ∫ x, p x * (U (step η v x) - U x) := by
  have hlog := (integrable_stepTerms hv hv' hJB hp_int).1
  have hsum := (hKL.sub hlog).add hUT
  have hpb := pullback_klIntegrand (U := U) hv hv' hη hηL hJ hp hZ
  constructor
  · rw [integrable_iff_integrable_abs_stepJac_mul hv hv' hη hηL]
    simp_rw [hpb]
    exact hsum
  · rw [integral_eq_integral_abs_stepJac_mul hv hv' hη hηL]
    simp_rw [hpb]
    have hKL' : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x) -
        p x * Real.log (stepJac η v x) := hKL.sub hlog
    rw [integral_add hKL' hUT, integral_sub hKL hlog]

/-- **(3) Entropy identity (DT-1, dimension `d`).** Let `π = e^{-U}/Z` with `Z > 0`; `p > 0`
Lebesgue integrable; `v` differentiable with symmetric Jacobian, `‖Dv‖ ≤ Lv`, `η ≥ 0`,
`η Lv ≤ 1/2`; `q = pushDensity η v p` the density of `T#(p dx)`, `T = id + η v`. Assume
`p log(p/π)` and `p (U∘T - U)` are Lebesgue integrable. Then `q log(q/π)` is integrable and
`∫ q log(q/π) = ∫ p log(p/π) - ∫ p log det(I + η Dv) + ∫ p (U∘T - U)`. -/
theorem integral_pushDensity_klIntegrand (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hsym : ∀ x, (jacMat v x).IsSymm)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hZ : 0 < Z)
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x)) :
    Integrable (fun y => pushDensity η v p y *
        Real.log (pushDensity η v p y / gibbsDensity U Z y)) ∧
      ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) =
        (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
          (∫ x, p x * Real.log (stepJac η v x)) + ∫ x, p x * (U (step η v x) - U x) :=
  integral_pushDensity_klIntegrand_of_stepJac hv hv' hη hηL (stepJac_pos hv' hη hηL hsym)
    (abs_log_stepJac_le hv' hη hηL hsym) hp hp_int hZ hKL hUT

/-- Pointwise descent inequality, from `η div v - c η² ‖Dv‖_F² ≤ log J`:
`-log J + (U(T x) - U x) ≤ -η (div v - ∇U ⬝ᵥ v) + η² (c ‖Dv‖_F² + (L/2) ‖v‖²)`. -/
private lemma pointwise_descent {c : ℝ}
    (hlogJ : ∀ x, η * divergence v x - c * (η ^ 2 * frobSq (jacMat v x)) ≤
      Real.log (stepJac η v x))
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h)) (x : Fin d → ℝ) :
    -Real.log (stepJac η v x) + (U (step η v x) - U x) ≤
      -η * (divergence v x - grad U x ⬝ᵥ v x) +
        η ^ 2 * (c * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  have h1 := hlogJ x
  have h2 := le_quadratic_of_fderiv2_le hU hU' hU'' x (step η v x)
  have e : step η v x - x = η • v x := by simp [step]
  rw [e, dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at h2
  nlinarith [h1, h2]

/-- **Descent inequality from a log-determinant bound (density level).** Under the hypotheses
of `integral_pushDensity_klIntegrand_of_stepJac`, assume moreover
`η div v(x) - c η² ‖Dv(x)‖_F² ≤ log det(I + η Dv(x))` for all `x`, `U` and `DU`
differentiable with `D²U(z)(h,h) ≤ L ‖h‖²`, and `p ∇U ⬝ᵥ v`, `p ‖v‖²` Lebesgue integrable.
Then `∫ q log(q/π) ≤ ∫ p log(p/π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (c ‖Dv‖_F² + (L/2)‖v‖²)`.
The symmetric case is `c = 1` (`integral_pushDensity_klIntegrand_le`), the general one `c = 13`
(`DeterministicStepGeneral.integral_pushDensity_klIntegrand_le`). -/
theorem integral_pushDensity_klIntegrand_le_of_log_stepJac_ge {B c : ℝ}
    (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η)
    (hηL : η * Lv ≤ 1 / 2) (hJ : ∀ x, 0 < stepJac η v x)
    (hJB : ∀ x, |Real.log (stepJac η v x)| ≤ B)
    (hlogJ : ∀ x, η * divergence v x - c * (η ^ 2 * frobSq (jacMat v x)) ≤
      Real.log (stepJac η v x))
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h))
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (grad U x ⬝ᵥ v x))
    (hv2 : Integrable fun x => p x * (v x ⬝ᵥ v x)) :
    ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
        η * (∫ x, p x * (divergence v x - grad U x ⬝ᵥ v x)) +
        η ^ 2 * ∫ x, p x * (c * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  rw [(integral_pushDensity_klIntegrand_of_stepJac hv hv' hη hηL hJ hJB hp hp_int hZ hKL
    hUT).2]
  obtain ⟨hlog, hdiv, hfrob⟩ := integrable_stepTerms hv hv' hJB hp_int
  have hA : Integrable fun x => p x * (divergence v x - grad U x ⬝ᵥ v x) := by
    simp_rw [mul_sub]; exact hdiv.sub hUv
  have hB : Integrable fun x =>
      p x * (c * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
    simp_rw [mul_add]
    exact ((hfrob.const_mul c).congr (Eventually.of_forall fun x => by ring)).add
      ((hv2.const_mul (L / 2)).congr (Eventually.of_forall fun x => by ring))
  have hmono : ∫ x, (-(p x * Real.log (stepJac η v x)) + p x * (U (step η v x) - U x)) ≤
      ∫ x, (-η * (p x * (divergence v x - grad U x ⬝ᵥ v x)) +
        η ^ 2 * (p x * (c * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)))) := by
    refine integral_mono (hlog.neg.add hUT) ((hA.const_mul _).add (hB.const_mul _))
      fun x => ?_
    have h := mul_le_mul_of_nonneg_left (pointwise_descent hlogJ hU hU' hU'' x) (hp x).le
    simp only
    nlinarith
  have hlog' : Integrable fun x => -(p x * Real.log (stepJac η v x)) := hlog.neg
  have hA' : Integrable fun x => -η * (p x * (divergence v x - grad U x ⬝ᵥ v x)) :=
    hA.const_mul _
  have hB' : Integrable fun x =>
      η ^ 2 * (p x * (c * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x))) := hB.const_mul _
  rw [integral_add hlog' hUT, integral_neg, integral_add hA' hB',
    integral_const_mul, integral_const_mul] at hmono
  linarith

/-- **DT-1 (density level), dimension `d`, symmetric Jacobian.** Target `π = e^{-U}/Z`
(`Z > 0`), `U` and `DU` differentiable with `D²U(z)(h,h) ≤ L ‖h‖²`. Current density `p > 0`,
Lebesgue integrable. Velocity `v` differentiable with symmetric Jacobian (e.g. `v = ∇φ`,
`isSymm_jacMat_grad`) and `‖Dv(x)‖ ≤ Lv` (operator norm for the sup norm); `η ≥ 0`,
`η Lv ≤ 1/2`; `T = id + η v`, `q` the density of `T#(p dx)`. Assume `p log(p/π)`,
`p (U∘T - U)`, `p ∇U ⬝ᵥ v` and `p ‖v‖²` are Lebesgue integrable. Then
`∫ q log(q/π) ≤ ∫ p log(p/π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (‖Dv‖_F² + (L/2) ‖v‖²)`. -/
theorem integral_pushDensity_klIntegrand_le (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hsym : ∀ x, (jacMat v x).IsSymm)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h))
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (grad U x ⬝ᵥ v x))
    (hv2 : Integrable fun x => p x * (v x ⬝ᵥ v x)) :
    ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) -
        η * (∫ x, p x * (divergence v x - grad U x ⬝ᵥ v x)) +
        η ^ 2 * ∫ x, p x * (frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  simpa only [one_mul] using integral_pushDensity_klIntegrand_le_of_log_stepJac_ge (c := 1) hv
    hv' hη hηL (stepJac_pos hv' hη hηL hsym) (abs_log_stepJac_le hv' hη hηL hsym)
    (fun x => by simpa only [one_mul] using log_stepJac_ge hv hv' hη hηL hsym x) hp hp_int hZ
    hU hU' hU'' hKL hUT hUv hv2

/-- **DT-1, Stein form (FL-1 rate), dimension `d`.** Under the hypotheses of
`integral_pushDensity_klIntegrand_le`, assume further `p` differentiable and, for every `i`,
`vᵢ (∇log p)ᵢ p` and `p vᵢ` Lebesgue integrable (the Stein identity
`∫ (v ⬝ᵥ ∇log p) p = -∫ (div v) p` then holds). Then
`∫ q log(q/π) ≤ ∫ p log(p/π) + η ∫ (v ⬝ᵥ (∇log p + ∇U)) p + η² ∫ p (‖Dv‖_F² + (L/2)‖v‖²)`;
the first-order term is `η ∫ v ⬝ᵥ ∇log(p/π) p`. -/
theorem integral_pushDensity_klIntegrand_le_stein (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hsym : ∀ x, (jacMat v x).IsSymm)
    (hp : ∀ x, 0 < p x) (hp_int : Integrable p) (hpd : Differentiable ℝ p) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h))
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (grad U x ⬝ᵥ v x))
    (hv2 : Integrable fun x => p x * (v x ⬝ᵥ v x))
    (hvs : ∀ i, Integrable fun x => v x i * score p x i * p x)
    (hflux : ∀ i, Integrable fun x => p x * v x i) :
    ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) +
        η * (∫ x, (v x ⬝ᵥ (score p x + grad U x)) * p x) +
        η ^ 2 * ∫ x, p x * (frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  have h := integral_pushDensity_klIntegrand_le hv hv' hη hηL hsym hp hp_int hZ hU hU' hU''
    hKL hUT hUv hv2
  obtain ⟨-, hdiv, -⟩ := integrable_stepTerms hv hv' (abs_log_stepJac_le hv' hη hηL hsym) hp_int
  have hcoord : ∀ i, Differentiable ℝ fun x => v x i := fun i x =>
    differentiableAt_pi.1 (hv x) i
  have hdv : ∀ i, Integrable fun x => partialDeriv i (fun y => v y i) x * p x := fun i => by
    have e : ∀ x, partialDeriv i (fun y => v y i) x = jacMat v x i i := fun x => by
      rw [jacMat_apply, partialDeriv, (hasFDerivAt_pi'.1 (hv x).hasFDerivAt i).fderiv]
      rfl
    simp_rw [e]
    refine (hp_int.mul_bdd (c := Lv) (measurable_jacMat_apply v i i).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)).congr (Eventually.of_forall fun x => mul_comm _ _)
    rw [Real.norm_eq_abs]
    exact (abs_jacMat_le x i i).trans (hv' x)
  have hstein := KLTransport.integral_dotProduct_score_mul_eq_neg hpd hp hcoord hdv hvs hflux
  have hscore : Integrable fun x => (v x ⬝ᵥ score p x) * p x := by
    have e : (fun x => (v x ⬝ᵥ score p x) * p x) =
        fun x => ∑ i, v x i * score p x i * p x := funext fun x => by
      simp only [dotProduct, Finset.sum_mul]
    rw [e]
    exact integrable_finsetSum _ fun i _ => hvs i
  have e1 : ∫ x, p x * (divergence v x - grad U x ⬝ᵥ v x) =
      (∫ x, divergence v x * p x) - ∫ x, p x * (grad U x ⬝ᵥ v x) := by
    have hdiv' : Integrable fun x => divergence v x * p x :=
      hdiv.congr (Eventually.of_forall fun x => mul_comm _ _)
    rw [← integral_sub hdiv' hUv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have e2 : ∫ x, (v x ⬝ᵥ (score p x + grad U x)) * p x =
      (∫ x, (v x ⬝ᵥ score p x) * p x) + ∫ x, p x * (grad U x ⬝ᵥ v x) := by
    rw [← integral_add hscore hUv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dotProduct_add, dotProduct_comm (grad U x)]
    ring
  rw [e2, hstein]
  rw [e1] at h
  linarith

end Descent

/-! ### Mathlib `klDiv` form -/

section KLDiv

variable {η Lv L Z : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- **From the density level to Mathlib's `klDiv`.** Let `ρ = p dx` and `π = e^{-U}/Z dx` be
probability measures on `Fin d → ℝ` (`p > 0` measurable, `U` continuous, `Z > 0`), let `v` be
differentiable with `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`, `T = id + η v` and
`q = pushDensity η v p` the density of `T#ρ`. If `p log(p/π)` and `q log(q/π)` are Lebesgue
integrable and `∫ q log(q/π) ≤ ∫ p log(p/π) - a + b`, then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - a + b` (real values via `ENNReal.toReal`). -/
theorem klDiv_map_step_le_of_integral_le {a b : ℝ} (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hp : ∀ x, 0 < p x) (hp_meas : Measurable p) (hZ : 0 < Z) (hU : Continuous U)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hqKL : Integrable fun y => pushDensity η v p y *
      Real.log (pushDensity η v p y / gibbsDensity U Z y))
    (hle : ∫ y, pushDensity η v p y * Real.log (pushDensity η v p y / gibbsDensity U Z y) ≤
      (∫ x, p x * Real.log (p x / gibbsDensity U Z x)) - a + b) :
    InformationTheory.klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (InformationTheory.klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (InformationTheory.klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal - a + b := by
  have hπ_meas : Measurable (gibbsDensity U Z) :=
    (Real.measurable_exp.comp hU.measurable.neg).div_const Z
  have hπ_pos : ∀ x, 0 < gibbsDensity U Z x := fun x => div_pos (Real.exp_pos _) hZ
  have hmap := map_withDensity_step hv hv' hη hηL p
  have : IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (pushDensity η v p y)) := by
    rw [← hmap]
    infer_instance
  obtain ⟨hne, hq⟩ := MeasureHelpers.klDiv_withDensity_ofReal
    (measurable_pushDensity hv hv' hη hηL hp_meas) hπ_meas
    (fun y => div_nonneg (hp _).le (abs_nonneg _)) hπ_pos hqKL
  obtain ⟨-, hpKL⟩ :=
    MeasureHelpers.klDiv_withDensity_ofReal hp_meas hπ_meas (fun x => (hp x).le) hπ_pos hKL
  rw [hmap]
  refine ⟨hne, ?_⟩
  rw [hq, hpKL]
  exact hle

/-- **DT-1 (Mathlib `klDiv`), dimension `d`, symmetric Jacobian.** Let `ρ = p dx` and
`π = e^{-U}/Z dx` be probability measures on `Fin d → ℝ` (`Z > 0`), `p > 0` measurable, `U`
and `DU` differentiable with `D²U(z)(h,h) ≤ L ‖h‖²`. Let `v` be differentiable with symmetric
Jacobian and `‖Dv‖ ≤ Lv`, `η ≥ 0`, `η Lv ≤ 1/2`, `T = id + η v`. Assume `p log(p/π)`,
`p (U∘T - U)`, `p ∇U ⬝ᵥ v`, `p ‖v‖²` Lebesgue integrable. Then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (‖Dv‖_F² + (L/2) ‖v‖²)`
(`InformationTheory.klDiv`, real values via `ENNReal.toReal`). -/
theorem klDiv_map_step_le (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hsym : ∀ x, (jacMat v x).IsSymm)
    (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (fderiv ℝ U))
    (hU'' : ∀ z h, fderiv ℝ (fderiv ℝ U) z h h ≤ L * (h ⬝ᵥ h))
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : Integrable fun x => p x * Real.log (p x / gibbsDensity U Z x))
    (hUT : Integrable fun x => p x * (U (step η v x) - U x))
    (hUv : Integrable fun x => p x * (grad U x ⬝ᵥ v x))
    (hv2 : Integrable fun x => p x * (v x ⬝ᵥ v x)) :
    InformationTheory.klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (InformationTheory.klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (InformationTheory.klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (∫ x, p x * (divergence v x - grad U x ⬝ᵥ v x)) +
        η ^ 2 * ∫ x, p x * (frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  have hp_int := MeasureHelpers.integrable_of_isProbabilityMeasure (μ := volume) hp_meas
    fun x => (hp x).le
  exact klDiv_map_step_le_of_integral_le hv hv' hη hηL hp hp_meas hZ hU.continuous hKL
    (integral_pushDensity_klIntegrand hv hv' hη hηL hsym hp hp_int hZ hKL hUT).1
    (integral_pushDensity_klIntegrand_le hv hv' hη hηL hsym hp hp_int hZ hU hU' hU'' hKL hUT
      hUv hv2)

end KLDiv

end FormalizeSampling.DeterministicStepPi
