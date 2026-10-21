module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# SPD preconditioners: weighted norms, completion of squares and spectral comparison

Pointwise and integrated algebra for a constant symmetric positive-definite preconditioner
`H : Matrix (Fin d) (Fin d) ℝ` (`H.PosDef`), as used by preconditioned functional gradient flow
(PFG, Dong–Wang–Lin–Zhang, ICLR 2023). The squared weighted norm is the shared
`sqNormH H u = u ⬝ᵥ (H *ᵥ u)` from `FormalizeSampling.Foundations.VectorCalculus`.

## Conventions

* Vectors are `Fin d → ℝ`; inner products are `dotProduct` (`⬝ᵥ`), matrices act by
  `Matrix.mulVec` (`*ᵥ`), and `H⁻¹` is Mathlib's `Matrix.inv` (which is a genuine two-sided
  inverse here because a positive-definite matrix is invertible, `posDef_isUnit_det`).
* Real positive definiteness in Mathlib is `H.IsHermitian ∧ ∀ x ≠ 0, 0 < star x ⬝ᵥ (H *ᵥ x)`;
  over `ℝ` the `star` is trivial, so this is the usual `xᵀ H x > 0` together with `Hᵀ = H`.

## Contents

* SPD weighted norm and completion of squares (the algebra behind SE-1 and FL-3):
  * (a) `sqNormH_nonneg`, `sqNormH_eq_zero_iff`, `sqNormH_pos`, `posDef_isUnit_det`,
    `mul_inv_of_posDef`, `inv_mul_of_posDef`, `mulVec_inv_mulVec`, `inv_mulVec_mulVec`,
    `inv_posDef`, `transpose_eq_of_posDef`, `dotProduct_mulVec_comm`;
  * (b) pointwise completion of squares `completion_of_squares`, the value of the optimum
    `sqNormH_inv_mulVec`, minimality `quadratic_ge_min` and uniqueness of the minimiser
    `quadratic_eq_min_iff`;
  * (c) polarisation / Young-type identity `neg_dotProduct_mulVec_eq` and the inequality
    `neg_dotProduct_mulVec_le`;
  * (d) spectral comparison `inv_lower_bound_of_upper_bound`: `uᵀHu ≤ M |u|²` for all `u`
    implies `(1/M) |u|² ≤ uᵀH⁻¹u`; the hypothesis is discharged for every matrix by
    `exists_sqNormH_le` (with an explicit, non-sharp `M`) and for scalar preconditioners by
    `posDef_smul_one` and `sqNormH_smul_one`;
  * helpers: `sqNormH_sub` (expansion for symmetric `H`), `sqNormH_smul`, `sqNormH_neg`;
  * integrated completion of squares `integral_completion_of_squares`: with
    `J(f) = -∫ f ⬝ᵥ g dμ + ½ ∫ ‖f‖²_H dμ` and `v⋆ = H⁻¹ g`,
    `J(f) = ½ ∫ ‖f - v⋆‖²_H dμ - ½ ∫ ‖v⋆‖²_H dμ` under explicit integrability.

## What is NOT proved here

* No statement about the PFG objective with a divergence term: identifying
  `-𝔼_p[div f + f ⬝ᵥ ∇log p⋆]` with `-𝔼_p[f ⬝ᵥ ∇log(p⋆/p)]` needs Stein integration by parts
  (SE-1) and is not done in this file. Here `g` is an arbitrary vector field.
* No a.e.-uniqueness of the integrated minimiser over `L²(μ)` (SE-1) and no projection onto
  function classes.
* The spectral comparison (d) is proved by an elementary quadratic-form argument; no
  eigen-decomposition or matrix square root is constructed, and the constant `M` produced by
  `exists_sqNormH_le` is the crude bound `1 + ∑ᵢⱼ |Hᵢⱼ|`, not the largest eigenvalue.
-/

public section

open Matrix MeasureTheory

namespace FormalizeSampling
namespace SPD

variable {d : ℕ}

/-! ### (a) Basic facts about a positive-definite preconditioner -/

/-- For positive-definite `H`, the weighted squared norm is nonnegative: `0 ≤ uᵀ H u`. -/
theorem sqNormH_nonneg {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (u : Fin d → ℝ) :
    0 ≤ sqNormH H u := by
  have h := hH.posSemidef.dotProduct_mulVec_nonneg u
  simpa [sqNormH] using h

/-- For positive-definite `H` and `u ≠ 0`, the weighted squared norm is positive:
`0 < uᵀ H u`. -/
theorem sqNormH_pos {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {u : Fin d → ℝ}
    (hu : u ≠ 0) : 0 < sqNormH H u := by
  have h := hH.dotProduct_mulVec_pos hu
  simpa [sqNormH] using h

/-- For positive-definite `H`, `uᵀ H u = 0` if and only if `u = 0`. -/
theorem sqNormH_eq_zero_iff {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (u : Fin d → ℝ) : sqNormH H u = 0 ↔ u = 0 := by
  constructor
  · intro h
    by_contra hu
    exact (sqNormH_pos hH hu).ne' h
  · rintro rfl
    simp [sqNormH]

/-- A positive-definite matrix has a unit determinant, i.e. it is invertible. -/
theorem posDef_isUnit_det {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : IsUnit H.det :=
  (Matrix.isUnit_iff_isUnit_det H).1 hH.isUnit

/-- For positive-definite `H`, Mathlib's `H⁻¹` is a right inverse: `H * H⁻¹ = 1`. -/
theorem mul_inv_of_posDef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : H * H⁻¹ = 1 :=
  Matrix.mul_nonsing_inv H (posDef_isUnit_det hH)

/-- For positive-definite `H`, Mathlib's `H⁻¹` is a left inverse: `H⁻¹ * H = 1`. -/
theorem inv_mul_of_posDef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : H⁻¹ * H = 1 :=
  Matrix.nonsing_inv_mul H (posDef_isUnit_det hH)

/-- For positive-definite `H`, `H (H⁻¹ g) = g`. -/
theorem mulVec_inv_mulVec {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (g : Fin d → ℝ) :
    H *ᵥ (H⁻¹ *ᵥ g) = g := by
  rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hH, Matrix.one_mulVec]

/-- For positive-definite `H`, `H⁻¹ (H g) = g`. -/
theorem inv_mulVec_mulVec {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (g : Fin d → ℝ) :
    H⁻¹ *ᵥ (H *ᵥ g) = g := by
  rw [Matrix.mulVec_mulVec, inv_mul_of_posDef hH, Matrix.one_mulVec]

/-- The inverse of a positive-definite matrix is positive definite. -/
theorem inv_posDef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : H⁻¹.PosDef :=
  hH.inv

/-- A real positive-definite matrix is symmetric: `Hᵀ = H`. -/
theorem transpose_eq_of_posDef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) : Hᵀ = H := by
  have h : Hᴴ = H := hH.isHermitian
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- For a symmetric matrix `H` (`Hᵀ = H`), the bilinear form is symmetric:
`u ⬝ᵥ (H w) = w ⬝ᵥ (H u)`. -/
theorem dotProduct_mulVec_comm {H : Matrix (Fin d) (Fin d) ℝ} (hH : Hᵀ = H)
    (u w : Fin d → ℝ) : u ⬝ᵥ (H *ᵥ w) = w ⬝ᵥ (H *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH, dotProduct_comm]

/-- Expansion of the weighted norm of a difference for symmetric `H` (`Hᵀ = H`):
`‖u - w‖²_H = ‖u‖²_H - 2 uᵀ H w + ‖w‖²_H`. -/
theorem sqNormH_sub {H : Matrix (Fin d) (Fin d) ℝ} (hH : Hᵀ = H) (u w : Fin d → ℝ) :
    sqNormH H (u - w) = sqNormH H u - 2 * (u ⬝ᵥ (H *ᵥ w)) + sqNormH H w := by
  have hc := dotProduct_mulVec_comm hH u w
  simp only [sqNormH, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  linarith

/-- The weighted norm is quadratic: `‖t • u‖²_H = t² ‖u‖²_H` (any matrix `H`). -/
theorem sqNormH_smul (H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (u : Fin d → ℝ) :
    sqNormH H (t • u) = t ^ 2 * sqNormH H u := by
  simp only [sqNormH, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- The weighted norm is even: `‖-u‖²_H = ‖u‖²_H` (any matrix `H`). -/
theorem sqNormH_neg (H : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    sqNormH H (-u) = sqNormH H u := by
  simp [sqNormH, Matrix.mulVec_neg]

/-! ### (b) Completion of squares (pointwise) -/

/-- **Completion of squares, value of the optimum.** For positive-definite `H` and `v⋆ = H⁻¹ g`,
`‖v⋆‖²_H = gᵀ H⁻¹ g = ‖g‖²_{H⁻¹}` (the last equality is the definition of `sqNormH H⁻¹ g`). -/
theorem sqNormH_inv_mulVec {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (g : Fin d → ℝ) :
    sqNormH H (H⁻¹ *ᵥ g) = g ⬝ᵥ (H⁻¹ *ᵥ g) ∧ sqNormH H (H⁻¹ *ᵥ g) = sqNormH H⁻¹ g := by
  have h : sqNormH H (H⁻¹ *ᵥ g) = g ⬝ᵥ (H⁻¹ *ᵥ g) := by
    rw [sqNormH, mulVec_inv_mulVec hH, dotProduct_comm]
  exact ⟨h, h⟩

/-- **Pointwise completion of squares.** For positive-definite `H`, any `u, g` and
`v⋆ = H⁻¹ g`:
`-(u ⬝ᵥ g) + ½ ‖u‖²_H = ½ ‖u - v⋆‖²_H - ½ ‖v⋆‖²_H`. -/
theorem completion_of_squares {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (u g : Fin d → ℝ) :
    -(u ⬝ᵥ g) + (1 / 2) * sqNormH H u =
      (1 / 2) * sqNormH H (u - H⁻¹ *ᵥ g) - (1 / 2) * sqNormH H (H⁻¹ *ᵥ g) := by
  rw [sqNormH_sub (transpose_eq_of_posDef hH), mulVec_inv_mulVec hH]
  ring

/-- **Completion of squares, minimality.** For positive-definite `H`, the quadratic
`u ↦ -(u ⬝ᵥ g) + ½ ‖u‖²_H` is bounded below by its value `-½ gᵀ H⁻¹ g` at `v⋆ = H⁻¹ g`. -/
theorem quadratic_ge_min {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (u g : Fin d → ℝ) :
    -(1 / 2) * sqNormH H⁻¹ g ≤ -(u ⬝ᵥ g) + (1 / 2) * sqNormH H u := by
  rw [completion_of_squares hH, ← (sqNormH_inv_mulVec hH g).2]
  have := sqNormH_nonneg hH (u - H⁻¹ *ᵥ g)
  linarith

/-- **Completion of squares, unique minimiser.** For positive-definite `H`, the quadratic
`u ↦ -(u ⬝ᵥ g) + ½ ‖u‖²_H` attains its minimum value `-½ gᵀ H⁻¹ g` exactly at `u = H⁻¹ g`. -/
theorem quadratic_eq_min_iff {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (u g : Fin d → ℝ) :
    -(u ⬝ᵥ g) + (1 / 2) * sqNormH H u = -(1 / 2) * sqNormH H⁻¹ g ↔ u = H⁻¹ *ᵥ g := by
  rw [completion_of_squares hH, ← (sqNormH_inv_mulVec hH g).2]
  constructor
  · intro h
    have h0 : sqNormH H (u - H⁻¹ *ᵥ g) = 0 := by linarith
    exact sub_eq_zero.1 ((sqNormH_eq_zero_iff hH _).1 h0)
  · rintro rfl
    simp [sqNormH]

/-! ### (c) Young / approximation identity -/

/-- **Young-type identity.** For symmetric `H` (`Hᵀ = H`):
`-(uᵀ H w) = -½ ‖w‖²_H - ½ ‖u‖²_H + ½ ‖u - w‖²_H`. -/
theorem neg_dotProduct_mulVec_eq {H : Matrix (Fin d) (Fin d) ℝ} (hH : Hᵀ = H)
    (u w : Fin d → ℝ) :
    -(u ⬝ᵥ (H *ᵥ w)) =
      -(1 / 2) * sqNormH H w - (1 / 2) * sqNormH H u + (1 / 2) * sqNormH H (u - w) := by
  rw [sqNormH_sub hH]
  ring

/-- **Young-type inequality.** For positive-definite `H`:
`-(uᵀ H w) ≤ -½ ‖w‖²_H + ½ ‖u - w‖²_H`. -/
theorem neg_dotProduct_mulVec_le {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (u w : Fin d → ℝ) :
    -(u ⬝ᵥ (H *ᵥ w)) ≤ -(1 / 2) * sqNormH H w + (1 / 2) * sqNormH H (u - w) := by
  rw [neg_dotProduct_mulVec_eq (transpose_eq_of_posDef hH)]
  have := sqNormH_nonneg hH u
  linarith

/-! ### (d) Spectral comparison -/

/-- **Spectral comparison.** Let `H` be positive definite and `M > 0` with
`uᵀ H u ≤ M |u|²` for all `u` (i.e. `λ_max(H) ≤ M`). Then `(1/M) |u|² ≤ uᵀ H⁻¹ u` for all `u`
(i.e. `λ_min(H⁻¹) ≥ 1/M`). Here `|u|² = u ⬝ᵥ u`.

Proof: with `w = H⁻¹ u` and `t = 1/M`, expand `0 ≤ ‖w - t u‖²_H`. -/
theorem inv_lower_bound_of_upper_bound {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u))
    (u : Fin d → ℝ) : (1 / M) * (u ⬝ᵥ u) ≤ sqNormH H⁻¹ u := by
  have hsym := transpose_eq_of_posDef hH
  have h0 := sqNormH_nonneg hH (H⁻¹ *ᵥ u - (1 / M) • u)
  rw [sqNormH_sub hsym, sqNormH_smul, (sqNormH_inv_mulVec hH u).2, Matrix.mulVec_smul,
    dotProduct_smul, dotProduct_mulVec_comm hsym, mulVec_inv_mulVec hH, smul_eq_mul] at h0
  have hb := hbound u
  have hb' : (1 / M) ^ 2 * sqNormH H u ≤ (1 / M) * (u ⬝ᵥ u) := by
    have hM2 : 0 ≤ (1 / M) ^ 2 := sq_nonneg _
    calc (1 / M) ^ 2 * sqNormH H u ≤ (1 / M) ^ 2 * (M * (u ⬝ᵥ u)) :=
          mul_le_mul_of_nonneg_left hb hM2
      _ = (1 / M) * (u ⬝ᵥ u) := by field_simp
  linarith

/-- **Discharging the spectral hypothesis.** Every real matrix `H` has an explicit `M > 0`
with `uᵀ H u ≤ M |u|²` for all `u`, namely `M = 1 + ∑ᵢ ∑ⱼ |Hᵢⱼ|` (a crude upper bound for
`λ_max(H)`, not the sharp one). -/
theorem exists_sqNormH_le (H : Matrix (Fin d) (Fin d) ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u) := by
  refine ⟨1 + ∑ i, ∑ j, |H i j|, ?_, fun u => ?_⟩
  · have : 0 ≤ ∑ i, ∑ j, |H i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  · have huu : 0 ≤ u ⬝ᵥ u := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hsq : ∀ i, u i * u i ≤ u ⬝ᵥ u := fun i => by
      simp only [dotProduct]
      exact Finset.single_le_sum (f := fun k => u k * u k)
        (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
    have hterm : ∀ i j, u i * (H i j * u j) ≤ |H i j| * (u ⬝ᵥ u) := fun i j => by
      have h1 : u i * (H i j * u j) ≤ |H i j| * (|u i| * |u j|) := by
        calc u i * (H i j * u j) ≤ |u i * (H i j * u j)| := le_abs_self _
          _ = |H i j| * (|u i| * |u j|) := by rw [abs_mul, abs_mul]; ring
      have h2 : |u i| * |u j| ≤ u ⬝ᵥ u := by
        have := two_mul_le_add_sq |u i| |u j|
        have hi := hsq i
        have hj := hsq j
        have ei : |u i| ^ 2 = u i * u i := by rw [sq_abs, sq]
        have ej : |u j| ^ 2 = u j * u j := by rw [sq_abs, sq]
        nlinarith
      calc u i * (H i j * u j) ≤ |H i j| * (|u i| * |u j|) := h1
        _ ≤ |H i j| * (u ⬝ᵥ u) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have hsum : sqNormH H u ≤ (∑ i, ∑ j, |H i j|) * (u ⬝ᵥ u) := by
      calc sqNormH H u = ∑ i, ∑ j, u i * (H i j * u j) := by
            simp [sqNormH, dotProduct, Matrix.mulVec, Finset.mul_sum]
        _ ≤ ∑ i, ∑ j, |H i j| * (u ⬝ᵥ u) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = (∑ i, ∑ j, |H i j|) * (u ⬝ᵥ u) := by simp only [Finset.sum_mul]
    nlinarith

/-- **Scalar preconditioner, positivity.** For `a > 0`, `H = a • 1` is positive definite. -/
theorem posDef_smul_one {a : ℝ} (ha : 0 < a) :
    (a • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
  Matrix.PosDef.one.smul ha

/-- **Scalar preconditioner, weighted norm.** For `H = a • 1`, `‖u‖²_H = a |u|²`; in
particular the spectral hypothesis of `inv_lower_bound_of_upper_bound` holds with `M = a`
(with equality), and `H` is positive definite when `a > 0` (`posDef_smul_one`). -/
theorem sqNormH_smul_one (a : ℝ) (u : Fin d → ℝ) :
    sqNormH (a • (1 : Matrix (Fin d) (Fin d) ℝ)) u = a * (u ⬝ᵥ u) := by
  simp [sqNormH, Matrix.smul_mulVec, dotProduct_smul]

/-! ### Integrated completion of squares (with finite moments) -/

/-- **Integrated completion of squares.** Let `H` be positive definite, `μ` a measure
on `Fin d → ℝ`, `f, g` vector fields and `v⋆ = H⁻¹ g` pointwise. Assume `f ⬝ᵥ g`, `‖f‖²_H` and
`‖v⋆‖²_H` are `μ`-integrable. Then, for the quadratic objective
`J(f) = -∫ f ⬝ᵥ g dμ + ½ ∫ ‖f‖²_H dμ`,
`J(f) = ½ ∫ ‖f - v⋆‖²_H dμ - ½ ∫ ‖v⋆‖²_H dμ`.
(The integrability of `‖f - v⋆‖²_H` follows and is not assumed.) -/
theorem integral_completion_of_squares {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f g : (Fin d → ℝ) → Fin d → ℝ)
    (hfg : Integrable (fun x => f x ⬝ᵥ g x) μ) (hf : Integrable (fun x => sqNormH H (f x)) μ)
    (hv : Integrable (fun x => sqNormH H (H⁻¹ *ᵥ g x)) μ) :
    -(∫ x, f x ⬝ᵥ g x ∂μ) + (1 / 2) * ∫ x, sqNormH H (f x) ∂μ =
      (1 / 2) * ∫ x, sqNormH H (f x - H⁻¹ *ᵥ g x) ∂μ -
        (1 / 2) * ∫ x, sqNormH H (H⁻¹ *ᵥ g x) ∂μ := by
  have hpt : (fun x => sqNormH H (f x - H⁻¹ *ᵥ g x)) =
      fun x => (-2 * (f x ⬝ᵥ g x) + sqNormH H (f x)) + sqNormH H (H⁻¹ *ᵥ g x) := by
    funext x
    have := completion_of_squares hH (f x) (g x)
    linarith
  have h1 : Integrable (fun x => -2 * (f x ⬝ᵥ g x) + sqNormH H (f x)) μ :=
    (hfg.const_mul (-2)).add hf
  rw [hpt, integral_add h1 hv, integral_add (hfg.const_mul (-2)) hf, integral_const_mul]
  ring

end SPD
end FormalizeSampling
