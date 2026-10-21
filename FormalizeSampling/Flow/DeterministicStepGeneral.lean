module

public import FormalizeSampling.Flow.DeterministicStepPi

/-!
# DT-1 without symmetry: descent for one deterministic step with a general Jacobian

`FormalizeSampling.DeterministicStepPi` proves the `d`-dimensional deterministic step descent
only for velocities with a **symmetric** Jacobian, because its log-determinant bound
`trace_sub_frobSq_le_log_det` uses the spectral theorem for `Dv(x)`. The theorems here do not
need the symmetry hypothesis, at the price of the constant `13` in front of `η² ∫ p ‖Dv‖_F²`.

## Method (real arithmetic only, no complex eigenvalues)

For a real square matrix `A` put `S = A + Aᵀ + AᵀA` (`symPart A`), so that
`(I + A)ᵀ(I + A) = I + S` and hence `det(I + A)² = det(I + S)`, `S` symmetric.

* `mulVec_dotProduct_self_le`: `‖A w‖₂² ≤ ‖A‖_F² ‖w‖₂²` (Cauchy–Schwarz), so `‖A‖_F² ≤ 1/4`
  gives the Euclidean operator bound `‖A‖₂ ≤ 1/2`.
* `eigenvalues_symPart_ge`: every eigenvalue `μ` of `S` satisfies `μ ≥ -3/4`
  (`μ ‖w‖² = 2 w ⬝ᵥ A w + ‖A w‖²`).
* `det_one_add_pos`: `det(I + A) > 0` (`det(I + tA) ≠ 0` for `t ∈ [0, 1]`; intermediate value
  theorem).
* `sub_four_sq_le_log_one_add`: `t - 4t² ≤ log(1 + t)` for `t ≥ -3/4`.
* `trace_symPart`, `frobSq_symPart_le`: `tr S = 2 tr A + ‖A‖_F²`, `‖S‖_F² ≤ (27/4) ‖A‖_F²`.
* `trace_sub_frobSq_le_log_det`: **`tr A - 13 ‖A‖_F² ≤ log det(I + A)`** for every real `A`
  with `‖A‖_F² ≤ 1/4` (from `log det(I + A) = ½ log det(I + S)`); and
  `log_det_le_trace_add_frobSq`: `log det(I + A) ≤ tr A + ‖A‖_F²`.

## Assumptions of the descent bound

Same as `DeterministicStepPi.klDiv_map_step_le`, with the symmetry hypothesis `hsym` replaced
by the **Frobenius smallness** hypothesis

  `hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4`   (i.e. `η ‖Dv(x)‖_F ≤ 1/2`).

The sup-norm hypothesis `‖Dv(x)‖ ≤ Lv`, `η Lv ≤ 1/2` is kept: it gives bijectivity of
`T = id + η v`, the change of variables (all reused from `DeterministicStepPi`) and the bounds
used for integrability. It does not control the Euclidean norm of a non-symmetric `Dv`, hence
`hF`. `sq_mul_frobSq_jacMat_le` shows that `η² d Lv² ≤ 1/4` (i.e. `η √d Lv ≤ 1/2`) implies
`hF`, via `‖Dv‖_F² ≤ d ‖Dv‖²` (`DeterministicStepPi.frobSq_jacMat_le`);
`klDiv_map_step_le_of_mul_dim_le` uses this and needs no Frobenius hypothesis.

## Results

* `integral_pushDensity_klIntegrand_le` (density level) and `klDiv_map_step_le`
  (Mathlib `klDiv`):
  `KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (13 ‖Dv‖_F² + (L/2)‖v‖²)`,
  the case `c = 13` of the descent lemmas
  `DeterministicStepPi.integral_pushDensity_klIntegrand_le_of_log_stepJac_ge` and
  `DeterministicStepPi.klDiv_map_step_le_of_integral_le`, with `det(I + η Dv) > 0`
  (`stepJac_pos`), `|log det(I + η Dv)|` bounded (`abs_log_stepJac_le`) and
  `η div v - 13 η² ‖Dv‖_F² ≤ log det(I + η Dv)` (`log_stepJac_ge`). The entropy identity
  without symmetry is `DeterministicStepPi.integral_pushDensity_klIntegrand_of_stepJac`.

## NOT proved here

* The constant `13` is not optimal (`1` holds, via Schur's inequality, for `‖A‖₂ ≤ 1/2`).
* No Stein form of the general-Jacobian bound is stated here.
-/

@[expose] public section

open MeasureTheory Set Filter Matrix
open scoped ENNReal NNReal
open FormalizeSampling.DeterministicStepPi

namespace FormalizeSampling.DeterministicStepGeneral

variable {d : ℕ}

/-! ### Matrix inequalities without symmetry -/

/-- For `t ≥ -3/4`, `t - 4 t² ≤ log(1 + t)` (from `log(1 + t) ≥ t / (1 + t)` and
`1 / (1 + t) ≤ 4`). -/
theorem sub_four_sq_le_log_one_add {t : ℝ} (ht : -3 / 4 ≤ t) :
    t - 4 * t ^ 2 ≤ Real.log (1 + t) := by
  have h1 : 0 < 1 + t := by linarith
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at h2
  have hinv : (1 + t)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ h1 (by norm_num)]; linarith
  have he : (1 + t)⁻¹ * (1 + t) = 1 := inv_mul_cancel₀ h1.ne'
  nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg t)]

/-- **Euclidean bound by the Frobenius norm** (Cauchy–Schwarz, row by row):
`‖A w‖₂² ≤ ‖A‖_F² ‖w‖₂²`, written `(A w) ⬝ᵥ (A w) ≤ frobSq A * (w ⬝ᵥ w)`. -/
theorem mulVec_dotProduct_self_le (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ frobSq A * (w ⬝ᵥ w) := by
  simp only [dotProduct, mulVec, frobSq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) w
  simpa [sq, Finset.sum_mul] using h

/-- `‖Aᵀ‖_F² = ‖A‖_F²`. -/
theorem frobSq_transpose (A : Matrix (Fin d) (Fin d) ℝ) : frobSq Aᵀ = frobSq A := by
  simp only [frobSq, transpose_apply]
  exact Finset.sum_comm

/-- `tr(AᵀA) = ‖A‖_F²`. -/
theorem trace_transpose_mul_self (A : Matrix (Fin d) (Fin d) ℝ) :
    (Aᵀ * A).trace = frobSq A := by
  simp only [trace, diag_apply, mul_apply, transpose_apply, frobSq, sq]
  exact Finset.sum_comm

/-- Submultiplicativity for `AᵀA`: `‖AᵀA‖_F² ≤ (‖A‖_F²)²` (Cauchy–Schwarz entrywise). -/
theorem frobSq_transpose_mul_self_le (A : Matrix (Fin d) (Fin d) ℝ) :
    frobSq (Aᵀ * A) ≤ frobSq A ^ 2 := by
  have h : ∀ i j, (Aᵀ * A) i j ^ 2 ≤ (∑ k, A k i ^ 2) * ∑ k, A k j ^ 2 := fun i j => by
    simpa [mul_apply] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => A k i)
      (fun k => A k j)
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j).trans_eq ?_
  rw [sq, ← frobSq_transpose A]
  simp only [frobSq, transpose_apply, Finset.sum_mul_sum]

/-- `‖X + Y + W‖_F² ≤ 3 (‖X‖_F² + ‖Y‖_F² + ‖W‖_F²)` (entrywise `(a+b+c)² ≤ 3(a²+b²+c²)`). -/
theorem frobSq_add_add_le (X Y W : Matrix (Fin d) (Fin d) ℝ) :
    frobSq (X + Y + W) ≤ 3 * (frobSq X + frobSq Y + frobSq W) := by
  simp only [frobSq, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  nlinarith [sq_nonneg (X i j - Y i j), sq_nonneg (X i j - W i j), sq_nonneg (Y i j - W i j)]

/-- For any real `A` with `‖A‖_F² ≤ 1/4`, `det(I + A) ≠ 0`: if `(I + A) w = 0` then
`‖w‖₂² = ‖A w‖₂² ≤ ‖w‖₂²/4`, so `w = 0`. -/
theorem det_one_add_ne_zero {A : Matrix (Fin d) (Fin d) ℝ} (hA : frobSq A ≤ 1 / 4) :
    (1 + A).det ≠ 0 := by
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [add_mulVec, one_mulVec] at hw
  have h1 : A *ᵥ w = -w := eq_neg_of_add_eq_zero_right hw
  have h2 := mulVec_dotProduct_self_le A w
  rw [h1, neg_dotProduct, dotProduct_neg, neg_neg] at h2
  have h3 : 0 ≤ w ⬝ᵥ w := dotProduct_self_star_nonneg w
  have h4 : w ⬝ᵥ w = 0 := by nlinarith [frobSq_nonneg A]
  exact hw0 (dotProduct_self_eq_zero.1 h4)

/-- **Positivity of the determinant (no symmetry).** For any real `A` with `‖A‖_F² ≤ 1/4`,
`det(I + A) > 0`: `t ↦ det(I + tA)` is continuous, equals `1` at `t = 0` and never vanishes
on `[0, 1]` (`det_one_add_ne_zero`), so the intermediate value theorem applies. -/
theorem det_one_add_pos {A : Matrix (Fin d) (Fin d) ℝ} (hA : frobSq A ≤ 1 / 4) :
    0 < (1 + A).det := by
  by_contra hneg
  replace hneg := not_lt.1 hneg
  have hcont : ContinuousOn (fun t : ℝ => (1 + t • A).det) (Icc 0 1) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det.continuousOn
  have hmem : (0 : ℝ) ∈ Icc ((1 + (1 : ℝ) • A).det) ((1 + (0 : ℝ) • A).det) := by
    simp only [one_smul, zero_smul, add_zero, det_one]
    exact ⟨hneg, zero_le_one⟩
  obtain ⟨t, ⟨ht0, ht1⟩, hzero⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  refine det_one_add_ne_zero ?_ hzero
  rw [frobSq_smul]
  have : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [frobSq_nonneg A]


/-- The symmetric matrix `S = A + Aᵀ + AᵀA`, so that `(I + A)ᵀ(I + A) = I + S`
(`transpose_mul_eq`). -/
def symPart (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := A + Aᵀ + Aᵀ * A

/-- `(I + A)ᵀ (I + A) = I + S` with `S = symPart A = A + Aᵀ + AᵀA`. -/
theorem transpose_mul_eq (A : Matrix (Fin d) (Fin d) ℝ) :
    (1 + A)ᵀ * (1 + A) = 1 + symPart A := by
  rw [transpose_add, transpose_one, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, symPart]
  abel

/-- `S = A + Aᵀ + AᵀA` is symmetric (a real Hermitian matrix). -/
theorem isHermitian_symPart (A : Matrix (Fin d) (Fin d) ℝ) : (symPart A).IsHermitian := by
  show (symPart A)ᴴ = _
  rw [conjTranspose_eq_transpose_of_trivial, symPart, transpose_add, transpose_add,
    transpose_mul, transpose_transpose]
  abel

/-- Quadratic form of `S`: `w ⬝ᵥ S w = 2 (w ⬝ᵥ A w) + ‖A w‖₂²`. -/
theorem dotProduct_symPart_mulVec (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    w ⬝ᵥ (symPart A *ᵥ w) = 2 * (w ⬝ᵥ (A *ᵥ w)) + (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
  have h : ∀ u, w ⬝ᵥ (Aᵀ *ᵥ u) = (A *ᵥ w) ⬝ᵥ u := fun u => by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [symPart, add_mulVec, add_mulVec, ← mulVec_mulVec, dotProduct_add, dotProduct_add, h, h,
    dotProduct_comm (A *ᵥ w) w]
  ring

/-- **Spectral lower bound for `S`.** If `‖A‖_F² ≤ 1/4`, every eigenvalue `μ` of
`S = A + Aᵀ + AᵀA` satisfies `μ ≥ -3/4`. Proof: for an eigenvector `w`,
`μ ‖w‖² = 2 (w ⬝ᵥ A w) + ‖A w‖²` with `(w ⬝ᵥ A w)² ≤ ‖w‖² ‖A w‖²` and
`‖A w‖² ≤ ‖w‖²/4`. -/
theorem eigenvalues_symPart_ge {A : Matrix (Fin d) (Fin d) ℝ} (hA : frobSq A ≤ 1 / 4)
    (i : Fin d) : -3 / 4 ≤ (isHermitian_symPart A).eigenvalues i := by
  set hS := isHermitian_symPart A
  have hev := hS.mulVec_eigenvectorBasis i
  set w : Fin d → ℝ := ⇑(hS.eigenvectorBasis i)
  have hw : w ≠ 0 := by
    intro h
    have h1 := hS.eigenvectorBasis.orthonormal.1 i
    have : hS.eigenvectorBasis i = 0 := by
      ext j; simpa [w] using congrFun h j
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  have hW : 0 < w ⬝ᵥ w := by
    rcases (dotProduct_self_star_nonneg w).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hw
  have hq := dotProduct_symPart_mulVec A w
  rw [hev, dotProduct_smul, smul_eq_mul] at hq
  have ha := mulVec_dotProduct_self_le A w
  have hcs : (w ⬝ᵥ (A *ᵥ w)) ^ 2 ≤ (w ⬝ᵥ w) * ((A *ᵥ w) ⬝ᵥ (A *ᵥ w)) := by
    simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (A *ᵥ w)
  have ha0 : 0 ≤ (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := dotProduct_self_star_nonneg _
  have ha' : (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ 1 / 4 * (w ⬝ᵥ w) :=
    ha.trans (mul_le_mul_of_nonneg_right hA hW.le)
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hneg : 2 * (w ⬝ᵥ (A *ᵥ w)) + (A *ᵥ w) ⬝ᵥ (A *ᵥ w) + 3 / 4 * (w ⬝ᵥ w) < 0 := by
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 ha') (by nlinarith : (0:ℝ) ≤ 9 / 4 * (w ⬝ᵥ w) -
    (A *ᵥ w) ⬝ᵥ (A *ᵥ w))]

/-- `tr S = 2 tr A + ‖A‖_F²` for `S = A + Aᵀ + AᵀA`. -/
theorem trace_symPart (A : Matrix (Fin d) (Fin d) ℝ) :
    (symPart A).trace = 2 * A.trace + frobSq A := by
  rw [symPart, trace_add, trace_add, trace_transpose, trace_transpose_mul_self]
  ring

/-- If `‖A‖_F² ≤ 1/4`, then `‖S‖_F² ≤ (27/4) ‖A‖_F²` for `S = A + Aᵀ + AᵀA`. -/
theorem frobSq_symPart_le {A : Matrix (Fin d) (Fin d) ℝ} (hA : frobSq A ≤ 1 / 4) :
    frobSq (symPart A) ≤ 27 / 4 * frobSq A := by
  have h1 := frobSq_add_add_le A Aᵀ (Aᵀ * A)
  have h2 := frobSq_transpose_mul_self_le A
  have h0 := frobSq_nonneg A
  rw [frobSq_transpose] at h1
  rw [symPart]
  nlinarith

/-- `log det(I + A) = ½ log det(I + S)` for every real `A` (both sides use `Real.log`, which
is even; `det(I + S) = det(I + A)²`). -/
theorem log_det_one_add_eq_half (A : Matrix (Fin d) (Fin d) ℝ) :
    Real.log (1 + A).det = Real.log (1 + symPart A).det / 2 := by
  rw [← transpose_mul_eq, det_mul, det_transpose, ← sq, Real.log_pow]
  push_cast
  ring

/-- **Log-determinant lower bound, general (non-symmetric) case.** For every real square
matrix `A` with `‖A‖_F² ≤ 1/4`, `tr A - 13 ‖A‖_F² ≤ log det(I + A)`. Proof:
`log det(I + A) = ½ ∑ log(1 + μᵢ)` over the eigenvalues `μᵢ ≥ -3/4` of `S = A + Aᵀ + AᵀA`,
`log(1 + μ) ≥ μ - 4μ²`, `tr S = 2 tr A + ‖A‖_F²` and `‖S‖_F² ≤ (27/4) ‖A‖_F²`. -/
theorem trace_sub_frobSq_le_log_det {A : Matrix (Fin d) (Fin d) ℝ} (hA : frobSq A ≤ 1 / 4) :
    A.trace - 13 * frobSq A ≤ Real.log (1 + A).det := by
  set hS := isHermitian_symPart A
  have hev := eigenvalues_symPart_ge hA
  have hlog : (symPart A).trace - 4 * frobSq (symPart A) ≤ Real.log (1 + symPart A).det := by
    rw [det_one_add_eq_prod hS, Real.log_prod (fun i _ => by linarith [hev i]),
      hS.trace_eq_sum_eigenvalues, frobSq_eq_sum_sq hS]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => sub_four_sq_le_log_one_add (hev i)
  rw [log_det_one_add_eq_half A, trace_symPart] at *
  have := frobSq_symPart_le hA
  linarith

/-- **Log-determinant upper bound, general case.** For every real square matrix `A` with
`‖A‖_F² ≤ 1/4`, `log det(I + A) ≤ tr A + ‖A‖_F²` (`log(1 + μ) ≤ μ` for the eigenvalues of
`S = A + Aᵀ + AᵀA`). -/
theorem log_det_le_trace_add_frobSq {A : Matrix (Fin d) (Fin d) ℝ} (hA : frobSq A ≤ 1 / 4) :
    Real.log (1 + A).det ≤ A.trace + frobSq A := by
  set hS := isHermitian_symPart A
  have hev := eigenvalues_symPart_ge hA
  have hlog : Real.log (1 + symPart A).det ≤ (symPart A).trace := by
    rw [det_one_add_eq_prod hS, Real.log_prod (fun i _ => by linarith [hev i]),
      hS.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    exact Finset.sum_le_sum fun i _ => (Real.log_le_sub_one_of_pos (by linarith [hev i])).trans
      (le_of_eq (by ring))
  rw [log_det_one_add_eq_half A, trace_symPart] at *
  linarith [frobSq_nonneg A]


/-! ### The step with a general Jacobian -/

section Step

variable {η Lv L Z : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- Under `hF : η² ‖Dv(x)‖_F² ≤ 1/4` for all `x`, `‖η Dv(x)‖_F² ≤ 1/4`. -/
theorem frobSq_smul_jacMat_le (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4)
    (x : Fin d → ℝ) : frobSq (η • jacMat v x) ≤ 1 / 4 := by
  rw [frobSq_smul]; exact hF x

/-- **A sufficient condition for `hF`.** If `‖Dv(x)‖ ≤ Lv` (sup-norm operator norm) for all
`x` and `η² d Lv² ≤ 1/4` (i.e. `|η| √d Lv ≤ 1/2`), then `η² ‖Dv(x)‖_F² ≤ 1/4` for all `x`
(`‖Dv‖_F² ≤ d Lv²`, `frobSq_jacMat_le`). -/
theorem sq_mul_frobSq_jacMat_le (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hηdL : η ^ 2 * (d * Lv ^ 2) ≤ 1 / 4) (x : Fin d → ℝ) :
    η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4 :=
  (mul_le_mul_of_nonneg_left (frobSq_jacMat_le hv' x) (sq_nonneg η)).trans hηdL

/-- **No symmetry needed:** if `η² ‖Dv(x)‖_F² ≤ 1/4` for all `x`, then
`det(I + η Dv(x)) > 0`. -/
theorem stepJac_pos (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4) (x : Fin d → ℝ) :
    0 < stepJac η v x :=
  det_one_add_pos (frobSq_smul_jacMat_le hF x)

/-- **Log-determinant bound for the step, general Jacobian.** If `v` is differentiable and
`η² ‖Dv(x)‖_F² ≤ 1/4` for all `x`, then
`η div v(x) - 13 η² ‖Dv(x)‖_F² ≤ log det(I + η Dv(x))`. -/
theorem log_stepJac_ge (hv : Differentiable ℝ v)
    (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4) (x : Fin d → ℝ) :
    η * divergence v x - 13 * (η ^ 2 * frobSq (jacMat v x)) ≤ Real.log (stepJac η v x) := by
  have h := trace_sub_frobSq_le_log_det (frobSq_smul_jacMat_le hF x)
  rwa [trace_smul, frobSq_smul, trace_jacMat hv, smul_eq_mul] at h

/-- Upper log-determinant bound for the step: if `v` is differentiable and
`η² ‖Dv(x)‖_F² ≤ 1/4` for all `x`, then `log det(I + η Dv(x)) ≤ η div v(x) + η² ‖Dv(x)‖_F²`. -/
theorem log_stepJac_le (hv : Differentiable ℝ v)
    (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4) (x : Fin d → ℝ) :
    Real.log (stepJac η v x) ≤ η * divergence v x + η ^ 2 * frobSq (jacMat v x) := by
  have h := log_det_le_trace_add_frobSq (frobSq_smul_jacMat_le hF x)
  rwa [trace_smul, frobSq_smul, trace_jacMat hv, smul_eq_mul] at h

/-- Uniform bound on the log-Jacobian (general Jacobian): if `v` is differentiable,
`‖Dv‖ ≤ Lv` (sup norm), `η ≥ 0` and `η² ‖Dv‖_F² ≤ 1/4`, then
`|log det(I + η Dv(x))| ≤ η d Lv + 13 η² d Lv²`. -/
theorem abs_log_stepJac_le (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4) (x : Fin d → ℝ) :
    |Real.log (stepJac η v x)| ≤ η * (d * Lv) + 13 * (η ^ 2 * (d * Lv ^ 2)) := by
  have h1 := log_stepJac_ge hv hF x
  have h2 := log_stepJac_le hv hF x
  have h3 := abs_le.1 (abs_divergence_le hv hv' x)
  have h4 := mul_le_mul_of_nonneg_left (frobSq_jacMat_le hv' x) (sq_nonneg η)
  have h5 := mul_nonneg (sq_nonneg η) (frobSq_nonneg (jacMat v x))
  have h6 := mul_le_mul_of_nonneg_left h3.2 hη
  have h7 := mul_le_mul_of_nonneg_left h3.1 hη
  rw [abs_le]
  constructor <;> nlinarith

end Step

/-! ### Entropy identity and descent inequality -/

section Descent

variable {η Lv L Z : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- **DT-1 (density level), dimension `d`, general Jacobian.** Target `π = e^{-U}/Z`
(`Z > 0`), `U` and `DU` differentiable with `D²U(z)(h,h) ≤ L ‖h‖²`. Current density `p > 0`,
Lebesgue integrable. Velocity `v` differentiable with `‖Dv(x)‖ ≤ Lv` (sup-norm operator norm),
`η ≥ 0`, `η Lv ≤ 1/2`, and `η² ‖Dv(x)‖_F² ≤ 1/4` for all `x` (**no symmetry**);
`T = id + η v`, `q` the density of `T#(p dx)`. Assume `p log(p/π)`, `p (U∘T - U)`,
`p ∇U ⬝ᵥ v` and `p ‖v‖²` Lebesgue integrable. Then
`∫ q log(q/π) ≤ ∫ p log(p/π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (13 ‖Dv‖_F² + (L/2) ‖v‖²)`.
-/
theorem integral_pushDensity_klIntegrand_le (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4)
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
        η ^ 2 * ∫ x, p x * (13 * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) :=
  integral_pushDensity_klIntegrand_le_of_log_stepJac_ge hv hv' hη hηL (stepJac_pos hF)
    (abs_log_stepJac_le hv hv' hη hF) (log_stepJac_ge hv hF) hp hp_int hZ hU hU' hU'' hKL hUT
    hUv hv2

end Descent

/-! ### Mathlib `klDiv` form -/

section KLDiv

variable {η Lv L Z : ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} {U p : (Fin d → ℝ) → ℝ}

/-- **DT-1 (Mathlib `klDiv`), dimension `d`, general Jacobian.** Let `ρ = p dx` and
`π = e^{-U}/Z dx` be probability measures on `Fin d → ℝ` (`Z > 0`), `p > 0` measurable, `U`
and `DU` differentiable with `D²U(z)(h,h) ≤ L ‖h‖²`. Let `v` be differentiable with
`‖Dv‖ ≤ Lv` (sup norm), `η ≥ 0`, `η Lv ≤ 1/2` and `η² ‖Dv(x)‖_F² ≤ 1/4` for all `x`
(**no symmetry assumption**), `T = id + η v`. Assume `p log(p/π)`, `p (U∘T - U)`,
`p ∇U ⬝ᵥ v`, `p ‖v‖²` Lebesgue integrable. Then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (div v - ∇U ⬝ᵥ v) + η² ∫ p (13 ‖Dv‖_F² + (L/2) ‖v‖²)`
(`InformationTheory.klDiv`, real values via `ENNReal.toReal`). -/
theorem klDiv_map_step_le (hv : Differentiable ℝ v) (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hF : ∀ x, η ^ 2 * frobSq (jacMat v x) ≤ 1 / 4)
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
        η ^ 2 * ∫ x, p x * (13 * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) := by
  have hp_int := MeasureHelpers.integrable_of_isProbabilityMeasure (μ := volume) hp_meas
    fun x => (hp x).le
  exact klDiv_map_step_le_of_integral_le hv hv' hη hηL hp hp_meas hZ hU.continuous hKL
    (integral_pushDensity_klIntegrand_of_stepJac hv hv' hη hηL (stepJac_pos hF)
      (abs_log_stepJac_le hv hv' hη hF) hp hp_int hZ hKL hUT).1
    (integral_pushDensity_klIntegrand_le hv hv' hη hηL hF hp hp_int hZ hU hU' hU'' hKL hUT
      hUv hv2)

/-- **DT-1 (Mathlib `klDiv`), general Jacobian, sup-norm hypotheses only.** Same conclusion
as `klDiv_map_step_le`, with the Frobenius hypothesis replaced by the dimension-dependent
step-size condition `η² d Lv² ≤ 1/4`, i.e. `η √d Lv ≤ 1/2` (and `η Lv ≤ 1/2`), where
`‖Dv‖ ≤ Lv` is the sup-norm operator norm. -/
theorem klDiv_map_step_le_of_mul_dim_le (hv : Differentiable ℝ v)
    (hv' : ∀ x, ‖fderiv ℝ v x‖ ≤ Lv) (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2)
    (hηdL : η ^ 2 * (d * Lv ^ 2) ≤ 1 / 4)
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
        η ^ 2 * ∫ x, p x * (13 * frobSq (jacMat v x) + L / 2 * (v x ⬝ᵥ v x)) :=
  klDiv_map_step_le hv hv' hη hηL (sq_mul_frobSq_jacMat_le hv' hηdL) hp hp_meas hZ hU hU'
    hU'' hKL hUT hUv hv2

end KLDiv

end FormalizeSampling.DeterministicStepGeneral
