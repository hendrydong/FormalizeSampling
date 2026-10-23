module

public import FormalizeSampling.Flow.KLDecay

/-!
# FL-3: KL dissipation along an approximate velocity (sharp and projection forms)

Registry row **FL-3** (`docs/theorem_registry.md`), stated at one time for a general measure `μ`
on `Fin d → ℝ` (standing for the law `ρ_t`), a constant positive-definite preconditioner `H`, a
velocity field `f`, a state-score field `s` (standing for `∇log ρ_t`) and a target score `sStar`
(`∇log p⋆`).

## Conventions

* `v⋆ = H⁻¹ (sStar - s)` is `KLDecay.idealVelocity H s sStar`.
* The KL rate along `f` (the first variation of `KL(ρ_t ‖ p⋆)` under transport by `f`, the
  FL-1 formula, which is *not* proved here) is the number `∫ f ⬝ᵥ (s - sStar) dμ`.
* The weighted relative Fisher information is
  `I = ∫ ‖s - sStar‖²_{H⁻¹} dμ = ∫ ‖v⋆‖²_H dμ`, and the velocity error is
  `E = ∫ ‖f - v⋆‖²_H dμ`, where `‖u‖²_A = sqNormH A u = u ⬝ᵥ A u`.
* The projection objective is `KLDecay.projectedObjective`,
  `J(g) = -∫ g ⬝ᵥ (sStar - s) dμ + ½ ∫ ‖g‖²_H dμ = -∫ ⟨g, v⋆⟩_H dμ + ½ ∫ ‖g‖²_H dμ`.

## Contents

* `abs_integral_dotProduct_mulVec_le`: Cauchy–Schwarz in `L²(μ)` for the `H`-inner product,
  `|∫ ⟨u, w⟩_H dμ| ≤ √(∫ ‖u‖²_H dμ) √(∫ ‖w‖²_H dμ)` (quadratic-in-`t` argument).
* FL-3(a), absolute form `transport_rate_le_sqrt`: rate `≤ -I + √E √I`.
* FL-3(a), sharp relative form `transport_rate_le_sharp`: if `E ≤ ε I`, `0 ≤ ε`, then
  rate `≤ -(1 - √ε) I`; `half_one_sub_le_one_sub_sqrt` and `sharp_bound_le_half_bound` show
  `(1 - ε)/2 ≤ 1 - √ε`, so this bound implies the conclusion of
  `KLDissipation.rate_le_of_approx`.
* Tightness `transport_rate_scaled_idealVelocity`: `f = (1 - √ε) v⋆` has `E = ε I` and rate
  exactly `-(1 - √ε) I`.
* FL-3(c), projection form `integral_dotProduct_eq_of_isMinOn` and
  `transport_rate_eq_of_isMinOn`: if `f` minimises `J` over a class closed under scaling
  (`c • f ∈ F` for all real `c`), then `∫ ⟨f, v⋆⟩_H dμ = ∫ ‖f‖²_H dμ` and the rate equals
  `-∫ ‖f‖²_H dμ` (an equality); `transport_rate_nonpos_of_isMinOn` gives rate `≤ 0`.
  FL-3(b) is `KLDecay.transport_rate_le`.

## What is NOT proved

* The KL first-variation formula itself (the rate is a number defined by its integral formula).
* In the projection form nothing is assumed about the minimiser beyond minimality along the ray
  `{c • f}`; existence of a minimiser over `F` is not addressed.
-/

public section

open Matrix MeasureTheory

namespace FormalizeSampling
namespace ApproximateVelocity

open SPD KLDecay

variable {d : ℕ}

/-! ### Real-variable lemmas -/

/-- **Discriminant inequality.** If `A ≥ 0` and the real quadratic `t ↦ t² A + 2 t B + C` is
nonnegative for every real `t`, then `B² ≤ A C`. -/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * A + 2 * t * B + C) : B ^ 2 ≤ A * C := by
  rcases hA.eq_or_lt with hA0 | hApos
  · subst hA0
    by_contra hcon
    have hB : B ≠ 0 := by
      intro hB
      apply hcon
      simp [hB]
    have := h (-(C + 1) / (2 * B))
    have e : (-(C + 1) / (2 * B)) ^ 2 * 0 + 2 * (-(C + 1) / (2 * B)) * B + C = -1 := by
      field_simp
      ring
    linarith
  · have := h (-B / A)
    have e : (-B / A) ^ 2 * A + 2 * (-B / A) * B + C = C - B ^ 2 / A := by
      field_simp
      ring
    rw [e, sub_nonneg, div_le_iff₀ hApos] at this
    linarith

/-- **Cauchy–Schwarz from a nonnegative quadratic.** If `A, C ≥ 0` and
`t² A + 2 t B + C ≥ 0` for every real `t`, then `|B| ≤ √A √C`. -/
theorem abs_le_sqrt_mul_sqrt_of_quadratic_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * A + 2 * t * B + C) : |B| ≤ √A * √C := by
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt (sq_le_mul_of_quadratic_nonneg hA h)

/-- **First-order condition along a line.** If `t k + t² a ≥ 0` for every real `t`, then
`k = 0`. -/
theorem eq_zero_of_forall_mul_add_sq_nonneg {k a : ℝ} (h : ∀ t : ℝ, 0 ≤ t * k + t ^ 2 * a) :
    k = 0 := by
  by_contra hk
  have hkpos : 0 < |k| := abs_pos.2 hk
  have ha1 : 0 < |a| + 1 := by positivity
  set δ := |k| / (2 * (|a| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have h1 := h δ
  have h2 := h (-δ)
  have hkd : δ * |k| ≤ δ * (δ * a) := by
    rcases abs_cases k with ⟨hk', _⟩ | ⟨hk', _⟩ <;> rw [hk'] <;> nlinarith
  have hk1 : |k| ≤ δ * a := le_of_mul_le_mul_left hkd hδpos
  have hk2 : δ * a ≤ δ * |a| := mul_le_mul_of_nonneg_left (le_abs_self a) hδpos.le
  have hk3 : δ * |a| < |k| := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg a]
  linarith

/-- **The sharp constant dominates the Young constant.** For every `ε ≥ 0`,
`(1 - ε)/2 ≤ 1 - √ε`, since the difference is `(1 - √ε)²/2`. -/
theorem half_one_sub_le_one_sub_sqrt {ε : ℝ} (hε : 0 ≤ ε) : (1 - ε) / 2 ≤ 1 - √ε := by
  have hs := Real.sq_sqrt hε
  nlinarith [sq_nonneg (1 - √ε)]

/-- **The sharp bound implies the Young bound.** For `ε ≥ 0` and `I ≥ 0`,
`-(1 - √ε) I ≤ -((1 - ε)/2) I`. Hence `transport_rate_le_sharp` implies the conclusion of
`KLDissipation.rate_le_of_approx` (with `I` the weighted relative Fisher information). -/
theorem sharp_bound_le_half_bound {ε I : ℝ} (hε : 0 ≤ ε) (hI : 0 ≤ I) :
    -(1 - √ε) * I ≤ -((1 - ε) / 2) * I := by
  have := half_one_sub_le_one_sub_sqrt hε
  nlinarith

/-! ### Cauchy–Schwarz in `L²(μ)` for the `H`-inner product -/

/-- Pointwise expansion `‖t u + w‖²_H = t² ‖u‖²_H + 2 t ⟨u, w⟩_H + ‖w‖²_H` for symmetric `H`
(`Hᵀ = H`). -/
theorem sqNormH_smul_add {H : Matrix (Fin d) (Fin d) ℝ} (hH : Hᵀ = H) (t : ℝ)
    (u w : Fin d → ℝ) :
    sqNormH H (t • u + w) =
      t ^ 2 * sqNormH H u + 2 * t * (u ⬝ᵥ (H *ᵥ w)) + sqNormH H w := by
  have hc := dotProduct_mulVec_comm hH w u
  simp only [sqNormH, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul] at hc ⊢
  rw [hc]
  ring

/-- **Cauchy–Schwarz in `L²(μ)` for the `H`-inner product.** Let `H` be positive definite, `μ`
a measure and `u, w` vector fields such that `⟨u, w⟩_H = u ⬝ᵥ H w`, `‖u‖²_H` and `‖w‖²_H` are
`μ`-integrable. Then
`|∫ u ⬝ᵥ H w dμ| ≤ √(∫ ‖u‖²_H dμ) · √(∫ ‖w‖²_H dμ)`.
Proof: `0 ≤ ∫ ‖t u + w‖²_H dμ` is a quadratic in `t`; its discriminant is nonpositive. -/
theorem abs_integral_dotProduct_mulVec_le {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (u w : (Fin d → ℝ) → Fin d → ℝ)
    (huw : Integrable (fun x => u x ⬝ᵥ (H *ᵥ w x)) μ)
    (hu : Integrable (fun x => sqNormH H (u x)) μ)
    (hw : Integrable (fun x => sqNormH H (w x)) μ) :
    |∫ x, u x ⬝ᵥ (H *ᵥ w x) ∂μ| ≤
      √(∫ x, sqNormH H (u x) ∂μ) * √(∫ x, sqNormH H (w x) ∂μ) := by
  refine abs_le_sqrt_mul_sqrt_of_quadratic_nonneg
    (integral_nonneg fun x => sqNormH_nonneg hH _) fun t => ?_
  have hpt : ∀ x, 0 ≤ t ^ 2 * sqNormH H (u x) + 2 * t * (u x ⬝ᵥ (H *ᵥ w x)) +
      sqNormH H (w x) := fun x => by
    rw [← sqNormH_smul_add (transpose_eq_of_posDef hH)]
    exact sqNormH_nonneg hH _
  have hint : 0 ≤ ∫ x, (t ^ 2 * sqNormH H (u x) + 2 * t * (u x ⬝ᵥ (H *ᵥ w x)) +
      sqNormH H (w x)) ∂μ := integral_nonneg fun x => hpt x
  have h1 : Integrable (fun x => t ^ 2 * sqNormH H (u x) + 2 * t * (u x ⬝ᵥ (H *ᵥ w x))) μ :=
    (hu.const_mul _).add (huw.const_mul _)
  rwa [integral_add h1 hw, integral_add (hu.const_mul _) (huw.const_mul _), integral_const_mul,
    integral_const_mul] at hint

/-! ### FL-3(a): absolute and sharp relative-error forms -/

/-- **FL-3(a), absolute form.** Let `H` be positive definite, `μ` a measure (the law `ρ_t`),
`f` a velocity field, `s, sStar` score fields and `v⋆ = H⁻¹ (sStar - s)`. Assume
`f ⬝ᵥ (s - sStar)`, `‖s - sStar‖²_{H⁻¹}` and `‖f - v⋆‖²_H` are `μ`-integrable. Then with
`I = ∫ ‖s - sStar‖²_{H⁻¹} dμ` and `E = ∫ ‖f - v⋆‖²_H dμ` the KL rate along `f` satisfies
`∫ f ⬝ᵥ (s - sStar) dμ ≤ -I + √E √I`.
Proof: rate `= -I - ∫ ⟨f - v⋆, v⋆⟩_H dμ` and Cauchy–Schwarz in `L²(μ)`. -/
theorem transport_rate_le_sqrt {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f s sStar : (Fin d → ℝ) → Fin d → ℝ)
    (hrate : Integrable (fun x => f x ⬝ᵥ (s x - sStar x)) μ)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (herr : Integrable (fun x => sqNormH H (f x - idealVelocity H s sStar x)) μ) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ ≤
      -∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ +
        √(∫ x, sqNormH H (f x - idealVelocity H s sStar x) ∂μ) *
          √(∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ) := by
  set w := idealVelocity H s sStar with hwdef
  have hI : ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ = ∫ x, sqNormH H (w x) ∂μ := by
    congr 1
    funext x
    rw [hwdef, sqNormH_idealVelocity hH]
  have hw : Integrable (fun x => sqNormH H (w x)) μ := by
    refine hdiss.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hwdef, sqNormH_idealVelocity hH]
  have hfw : Integrable (fun x => f x ⬝ᵥ (H *ᵥ w x)) μ := by
    refine hrate.neg.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, hwdef, dotProduct_score_diff_eq hH s sStar x, neg_neg]
  have hpt : ∀ x, (f x - w x) ⬝ᵥ (H *ᵥ w x) = f x ⬝ᵥ (H *ᵥ w x) - sqNormH H (w x) := by
    intro x
    rw [sub_dotProduct, sqNormH]
  have hew : Integrable (fun x => (f x - w x) ⬝ᵥ (H *ᵥ w x)) μ := by
    simp only [hpt]
    exact hfw.sub hw
  have hrate_eq : ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ =
      -(∫ x, (f x - w x) ⬝ᵥ (H *ᵥ w x) ∂μ) - ∫ x, sqNormH H (w x) ∂μ := by
    simp only [hpt]
    rw [integral_sub hfw hw]
    have : ∀ x, f x ⬝ᵥ (s x - sStar x) = -(f x ⬝ᵥ (H *ᵥ w x)) := fun x =>
      dotProduct_score_diff_eq hH s sStar x (f x)
    simp only [this]
    rw [integral_neg]
    ring
  have hcs := abs_integral_dotProduct_mulVec_le hH (fun x => f x - w x) w hew herr hw
  rw [hrate_eq, hI]
  have := neg_le_abs (∫ x, (f x - w x) ⬝ᵥ (H *ᵥ w x) ∂μ)
  linarith

/-- **FL-3(a), sharp relative-error form.** Under the hypotheses of `transport_rate_le_sqrt`,
if moreover `0 ≤ ε` and the velocity error is a fraction of the weighted Fisher information,
`∫ ‖f - v⋆‖²_H dμ ≤ ε ∫ ‖s - sStar‖²_{H⁻¹} dμ`, then the KL rate along `f` satisfies
`∫ f ⬝ᵥ (s - sStar) dμ ≤ -(1 - √ε) ∫ ‖s - sStar‖²_{H⁻¹} dμ`.
This is dissipative for `ε < 1`, is attained (`transport_rate_scaled_idealVelocity`) and
implies the bound with constant `(1 - ε)/2` (`sharp_bound_le_half_bound`). -/
theorem transport_rate_le_sharp {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f s sStar : (Fin d → ℝ) → Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hrate : Integrable (fun x => f x ⬝ᵥ (s x - sStar x)) μ)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (herr : Integrable (fun x => sqNormH H (f x - idealVelocity H s sStar x)) μ)
    (happrox : ∫ x, sqNormH H (f x - idealVelocity H s sStar x) ∂μ ≤
      ε * ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ ≤ -(1 - √ε) * ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ := by
  have h := transport_rate_le_sqrt hH f s sStar hrate hdiss herr
  set I := ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ
  set E := ∫ x, sqNormH H (f x - idealVelocity H s sStar x) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun x => sqNormH_nonneg (inv_posDef hH) _
  have hE : √E ≤ √ε * √I := by
    rw [← Real.sqrt_mul hε]
    exact Real.sqrt_le_sqrt happrox
  have hII : √I * √I = I := Real.mul_self_sqrt hI
  have : √E * √I ≤ √ε * I := by
    calc √E * √I ≤ √ε * √I * √I := mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg _)
      _ = √ε * I := by rw [mul_assoc, hII]
  linarith

/-- **FL-3(a) is tight.** For any matrix `H`, measure `μ`, score fields `s, sStar`, `ε ≥ 0` and
`v⋆ = H⁻¹ (sStar - s)`, the velocity `f = (1 - √ε) v⋆` has relative error exactly `ε`,
`∫ ‖f - v⋆‖²_H dμ = ε ∫ ‖v⋆‖²_H dμ`, and KL rate exactly
`∫ f ⬝ᵥ (s - sStar) dμ = -(1 - √ε) ∫ ‖s - sStar‖²_{H⁻¹} dμ`; for positive-definite `H`,
`‖v⋆‖²_H = ‖s - sStar‖²_{H⁻¹}` (`KLDecay.sqNormH_idealVelocity`), so the constant `1 - √ε` of
`transport_rate_le_sharp` cannot be improved. No integrability is needed (each identity is a
constant multiple of a pointwise one; e.g. if `∫ ‖v⋆‖²_H dμ` is infinite, both sides of the first
are the Bochner junk value `0`). -/
theorem transport_rate_scaled_idealVelocity (H : Matrix (Fin d) (Fin d) ℝ)
    (μ : Measure (Fin d → ℝ)) (s sStar : (Fin d → ℝ) → Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∫ x, sqNormH H ((1 - √ε) • idealVelocity H s sStar x - idealVelocity H s sStar x) ∂μ =
        ε * ∫ x, sqNormH H (idealVelocity H s sStar x) ∂μ ∧
      ∫ x, ((1 - √ε) • idealVelocity H s sStar x) ⬝ᵥ (s x - sStar x) ∂μ =
        -(1 - √ε) * ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ := by
  constructor
  · rw [← integral_const_mul]
    congr 1
    funext x
    have : (1 - √ε) • idealVelocity H s sStar x - idealVelocity H s sStar x =
        (-√ε) • idealVelocity H s sStar x := by
      rw [sub_smul, one_smul, sub_sub_cancel_left, neg_smul]
    rw [this, sqNormH_smul, neg_sq, Real.sq_sqrt hε]
  · have h := integral_idealVelocity_dotProduct H μ s sStar
    simp only [smul_dotProduct, smul_eq_mul]
    rw [integral_const_mul, h]
    ring

/-! ### FL-3(c): projection onto a scale-closed class -/

/-- **FL-3(c), first-order condition.** Let `μ` be a measure, `H` any matrix, `s, sStar` score
fields, `F` a set of velocity fields and `f` a field whose scalings stay in `F`
(`c • f ∈ F` for every real `c`). If `f` minimises the projected objective
`J(g) = -∫ g ⬝ᵥ (sStar - s) dμ + ½ ∫ ‖g‖²_H dμ` (`KLDecay.projectedObjective`) over `F`, then
`∫ f ⬝ᵥ (sStar - s) dμ = ∫ ‖f‖²_H dμ`, i.e. `∫ ⟨f, v⋆⟩_H dμ = ∫ ‖f‖²_H dμ` when
`v⋆ = H⁻¹ (sStar - s)` with `H` invertible.
Proof: `c ↦ J(c f) = -c B + (c²/2) A` is minimised at `c = 1`, forcing `A = B`. No integrability
is needed (both sides scale linearly/quadratically by `integral_const_mul`). -/
theorem integral_dotProduct_eq_of_isMinOn (H : Matrix (Fin d) (Fin d) ℝ)
    {μ : Measure (Fin d → ℝ)} {s sStar f : (Fin d → ℝ) → Fin d → ℝ}
    {F : Set ((Fin d → ℝ) → Fin d → ℝ)} (hscale : ∀ c : ℝ, c • f ∈ F)
    (hmin : IsMinOn (projectedObjective H μ s sStar) F f) :
    ∫ x, f x ⬝ᵥ (sStar x - s x) ∂μ = ∫ x, sqNormH H (f x) ∂μ := by
  set B := ∫ x, f x ⬝ᵥ (sStar x - s x) ∂μ
  set A := ∫ x, sqNormH H (f x) ∂μ
  have hJ : ∀ c : ℝ, projectedObjective H μ s sStar (c • f) = -(c * B) + (1 / 2) * (c ^ 2 * A) := by
    intro c
    simp only [projectedObjective, Pi.smul_apply, smul_dotProduct, smul_eq_mul, sqNormH_smul,
      integral_const_mul, B, A]
  have hJ1 : projectedObjective H μ s sStar f = -B + (1 / 2) * A := rfl
  have key : ∀ t : ℝ, 0 ≤ t * (A - B) + t ^ 2 * (A / 2) := by
    intro t
    have h := isMinOn_iff.1 hmin ((1 + t) • f) (hscale (1 + t))
    rw [hJ, hJ1] at h
    nlinarith
  have := eq_zero_of_forall_mul_add_sq_nonneg key
  linarith

/-- **FL-3(c), exact KL rate of a projection.** Under the hypotheses of
`integral_dotProduct_eq_of_isMinOn` (`f` minimises `KLDecay.projectedObjective` over a class `F`
with `c • f ∈ F` for all real `c`), the KL rate along `f` is exactly
`∫ f ⬝ᵥ (s - sStar) dμ = -∫ ‖f‖²_H dμ`. No integrability is needed. -/
theorem transport_rate_eq_of_isMinOn (H : Matrix (Fin d) (Fin d) ℝ)
    {μ : Measure (Fin d → ℝ)} {s sStar f : (Fin d → ℝ) → Fin d → ℝ}
    {F : Set ((Fin d → ℝ) → Fin d → ℝ)} (hscale : ∀ c : ℝ, c • f ∈ F)
    (hmin : IsMinOn (projectedObjective H μ s sStar) F f) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ = -∫ x, sqNormH H (f x) ∂μ := by
  rw [← integral_dotProduct_eq_of_isMinOn H hscale hmin, ← integral_neg]
  congr 1
  funext x
  rw [← dotProduct_neg, neg_sub]

/-- **FL-3(c), a projection dissipates.** If `H` is positive definite and `f` minimises
`KLDecay.projectedObjective` over a class `F` with `c • f ∈ F` for all real `c`, then the KL
rate along `f` is nonpositive: `∫ f ⬝ᵥ (s - sStar) dμ = -∫ ‖f‖²_H dμ ≤ 0`. -/
theorem transport_rate_nonpos_of_isMinOn {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} {s sStar f : (Fin d → ℝ) → Fin d → ℝ}
    {F : Set ((Fin d → ℝ) → Fin d → ℝ)} (hscale : ∀ c : ℝ, c • f ∈ F)
    (hmin : IsMinOn (projectedObjective H μ s sStar) F f) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ ≤ 0 := by
  rw [transport_rate_eq_of_isMinOn H hscale hmin, neg_nonpos]
  exact integral_nonneg fun x => sqNormH_nonneg hH _

end ApproximateVelocity
end FormalizeSampling
