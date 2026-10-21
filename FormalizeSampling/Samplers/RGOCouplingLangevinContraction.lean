module

public import FormalizeSampling.Samplers.RGOCouplingLangevinStationary

/-!
# Contraction of one synchronous Euler–Maruyama step of the RGO Langevin dynamics

Status: **Verified** (no named hypotheses).

For `g` convex and `C²` with `‖D²g‖ ≤ L` (sup operator norm) the gradient is co-coercive in the
Euclidean inner product, and the Euler–Maruyama drift maps `F_y(x) = x + h b_y(x)` of the RGO
Langevin drift `b_y = -∇g - (· - y)/η` contract: with common noise, one synchronous step
satisfies `|F_y(x) - F_{y'}(x')|² ≤ (1 - h/η) |x - x'|² + (h/η) |y - y'|²` for
`0 ≤ h ≤ η / 2`, `h L ≤ 1`. All squared distances are Euclidean (`sqDist`, dot products).

## Main results

* `le_of_convexOn`: first-order convexity inequality `g z ≥ g x + ∇g(x) ⬝ (z - x)`.
* `descent`: `g (z + v) ≤ g z + ∇g(z) ⬝ v + (L/2) v ⬝ v`.
* `grad_sub_dotProduct_le`: co-coercivity `|∇g x - ∇g x'|² ≤ L (x - x') ⬝ (∇g x - ∇g x')`.
* `sqDist_step_le`: the one-step contraction above.

## Not proved here

* Contraction for non-convex `g` or for step sizes beyond `min (η/2) (1/L)`.
-/

public section

open MeasureTheory Set Filter Topology
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingWeak
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingLangevin

variable {d : ℕ} {g : (Fin d → ℝ) → ℝ}

/-- **First-order convexity inequality**: `g z ≥ g x + ∇g(x) ⬝ (z - x)` for convex
differentiable `g`. -/
theorem le_of_convexOn (hc : ConvexOn ℝ univ g) (hd : Differentiable ℝ g) (x z : Fin d → ℝ) :
    g x + grad g x ⬝ᵥ (z - x) ≤ g z := by
  set ψ : ℝ → ℝ := g ∘ AffineMap.lineMap x z with hψ
  have hψc : ConvexOn ℝ univ ψ := by
    simpa using hc.comp_affineMap (AffineMap.lineMap x z)
  have hψd : HasDerivAt ψ (fderiv ℝ g x (z - x)) 0 := by
    have := (hd (AffineMap.lineMap x z (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := z) (x := (0 : ℝ)))
    simpa [hψ] using this
  have h := hψc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hψd
  rw [slope_def_field, hψ] at h
  simp only [Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at h
  rw [← fderiv_apply_eq_grad_dotProduct]
  linarith

/-- **Descent lemma**: if `‖D²g‖ ≤ L` (sup norms), then
`g (z + v) ≤ g z + ∇g(z) ⬝ v + (L / 2) v ⬝ v`. -/
theorem descent (hg : ContDiff ℝ 2 g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) (z v : Fin d → ℝ) :
    g (z + v) ≤ g z + grad g z ⬝ᵥ v + L / 2 * (v ⬝ᵥ v) := by
  have hd1 : Differentiable ℝ g := hg.differentiable two_ne_zero
  have hd2 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  -- `ψ t = g (z + t v)`, `ψ' t = Dg(z + t v) v`, `ψ'' t = D²g(z + t v) v v`
  have hψ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => g (z + s • v)) (fderiv ℝ g (z + t • v) v) t :=
    fun t => (hd1 _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hψ' : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ g (z + s • v) v)
      (fderiv ℝ (fderiv ℝ g) (z + t • v) v v) t := fun t => by
    have := ((hd2 _).hasFDerivAt.comp_hasDerivAt t (hline t)).clm_apply (hasDerivAt_const t v)
    simpa using this
  set Q := ‖v‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hψ'' : ∀ t : ℝ, fderiv ℝ (fderiv ℝ g) (z + t • v) v v ≤ L * Q := fun t => by
    calc fderiv ℝ (fderiv ℝ g) (z + t • v) v v ≤ ‖fderiv ℝ (fderiv ℝ g) (z + t • v) v v‖ :=
          le_abs_self _
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) (z + t • v) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) (z + t • v)‖ * ‖v‖ * ‖v‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖v‖ * ‖v‖ := by gcongr; exact hL _
      _ = L * Q := by rw [hQ]; ring
  -- `χ t = ψ t - t ψ'(0) - L Q t² / 2` is antitone on `[0, ∞)`
  set c := fderiv ℝ g z v with hc
  have hχ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => g (z + s • v) - s * c - L * Q / 2 * s ^ 2)
      (fderiv ℝ g (z + t • v) v - c - L * Q * t) t := fun t => by
    have := ((hψ t).sub ((hasDerivAt_id t).mul_const c)).sub
      (((hasDerivAt_id t).pow 2).const_mul (L * Q / 2))
    exact this.congr_deriv (by simp; ring)
  have hderiv_le : ∀ t ∈ interior (Ici (0 : ℝ)),
      deriv (fun s : ℝ => g (z + s • v) - s * c - L * Q / 2 * s ^ 2) t ≤ 0 := by
    intro t ht
    rw [interior_Ici] at ht
    rw [(hχ t).deriv]
    have h1 : fderiv ℝ g (z + t • v) v - fderiv ℝ g (z + (0 : ℝ) • v) v ≤ L * Q * (t - 0) :=
      image_sub_le_mul_sub_of_deriv_le (fun s => (hψ' s).differentiableAt)
        (fun s => (hψ' s).deriv ▸ hψ'' s) (le_of_lt ht)
    simp only [zero_smul, add_zero, sub_zero] at h1
    linarith
  have hmono := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hχ s).continuousAt.continuousWithinAt)
    (fun s _ => (hχ s).differentiableAt.differentiableWithinAt) hderiv_le 0 (mem_Ici.2 le_rfl) 1
    (mem_Ici.2 zero_le_one) zero_le_one
  simp only [zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul, mul_zero, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hmono
  have hQv : Q ≤ v ⬝ᵥ v := norm_sq_le_dotProduct_self v
  rw [hc, fderiv_apply_eq_grad_dotProduct] at hmono
  nlinarith

/-- Half of co-coercivity: `g x + ∇g(x) ⬝ (x' - x) + |∇g(x') - ∇g(x)|² / (2L) ≤ g x'` for convex
`g` with `‖D²g‖ ≤ L`, `L > 0`. -/
theorem le_of_convexOn_of_descent (hg : SmoothConvexBdd g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) (x x' : Fin d → ℝ) :
    g x + grad g x ⬝ᵥ (x' - x) +
      (grad g x' - grad g x) ⬝ᵥ (grad g x' - grad g x) / (2 * L) ≤ g x' := by
  set w := grad g x' - grad g x with hw
  have h1 := le_of_convexOn hg.1 (hg.2.1.differentiable two_ne_zero) x (x' + -(L⁻¹ • w))
  have h2 := descent hg.2.1 hL0.le hL x' (-(L⁻¹ • w))
  have e1 : grad g x ⬝ᵥ (x' + -(L⁻¹ • w) - x) =
      grad g x ⬝ᵥ (x' - x) - L⁻¹ * (grad g x ⬝ᵥ w) := by
    rw [show x' + -(L⁻¹ • w) - x = (x' - x) - L⁻¹ • w by abel, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  have e2 : grad g x' ⬝ᵥ (-(L⁻¹ • w)) = -(L⁻¹ * (grad g x' ⬝ᵥ w)) := by
    rw [dotProduct_neg, dotProduct_smul, smul_eq_mul]
  have e3 : (-(L⁻¹ • w)) ⬝ᵥ (-(L⁻¹ • w)) = L⁻¹ * (L⁻¹ * (w ⬝ᵥ w)) := by
    rw [neg_dotProduct, dotProduct_neg, neg_neg, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
  have e4 : grad g x' ⬝ᵥ w - grad g x ⬝ᵥ w = w ⬝ᵥ w := by
    rw [← sub_dotProduct]
  rw [e1] at h1
  rw [e2, e3] at h2
  have e5 : L / 2 * (L⁻¹ * (L⁻¹ * (w ⬝ᵥ w))) = w ⬝ᵥ w / (2 * L) := by
    field_simp
  have e6 : L⁻¹ * (grad g x' ⬝ᵥ w) - L⁻¹ * (grad g x ⬝ᵥ w) = w ⬝ᵥ w / L := by
    rw [← mul_sub, e4]; field_simp
  have e7 : w ⬝ᵥ w / L = 2 * (w ⬝ᵥ w / (2 * L)) := by field_simp
  linarith

/-- **Co-coercivity of the gradient** (Baillon–Haddad, via the descent lemma): for convex `C²`
`g` with `‖D²g‖ ≤ L` (sup operator norm), `L > 0`,
`|∇g(x) - ∇g(x')|² ≤ L (x - x') ⬝ (∇g(x) - ∇g(x'))` (Euclidean dot products). -/
theorem grad_sub_dotProduct_le (hg : SmoothConvexBdd g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) (x x' : Fin d → ℝ) :
    (grad g x - grad g x') ⬝ᵥ (grad g x - grad g x') ≤
      L * ((x - x') ⬝ᵥ (grad g x - grad g x')) := by
  have h1 := le_of_convexOn_of_descent hg hL0 hL x x'
  have h2 := le_of_convexOn_of_descent hg hL0 hL x' x
  set w := grad g x - grad g x' with hw
  have e1 : (grad g x' - grad g x) ⬝ᵥ (grad g x' - grad g x) = w ⬝ᵥ w := by
    rw [show grad g x' - grad g x = -w by rw [hw]; abel, neg_dotProduct, dotProduct_neg, neg_neg]
  have e2 : grad g x ⬝ᵥ (x' - x) + grad g x' ⬝ᵥ (x - x') = -((x - x') ⬝ᵥ w) := by
    rw [hw]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm x, dotProduct_comm x']
    ring
  rw [e1] at h1
  have e3 : w ⬝ᵥ w / (2 * L) + w ⬝ᵥ w / (2 * L) = w ⬝ᵥ w / L := by field_simp; ring
  have h3 : w ⬝ᵥ w / L ≤ (x - x') ⬝ᵥ w := by linarith
  rwa [div_le_iff₀ hL0, mul_comm] at h3

/-- The squared Euclidean distance as a dot product. -/
theorem sqDist_eq_dotProduct (x y : Fin d → ℝ) : sqDist x y = (x - y) ⬝ᵥ (x - y) := by
  simp [sqDist, dotProduct, sq]

/-- **One synchronous Euler–Maruyama step contracts.** Let `g` be smooth convex with
`‖D²g‖ ≤ L` (`L > 0`), `η > 0` and `0 ≤ h ≤ η / 2` with `h L ≤ 1`. The drift maps
`F_y(x) = x + h b_y(x)` satisfy, with `λ = 1 - h / η`,
`|F_y(x) - F_{y'}(x')|² ≤ λ |x - x'|² + (h / η) |y - y'|²` (Euclidean). -/
theorem sqDist_step_le (hg : SmoothConvexBdd g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) {η h : ℝ} (hη : 0 < η) (hh : 0 ≤ h)
    (hhη : h ≤ η / 2) (hhL : h * L ≤ 1) (y y' x x' : Fin d → ℝ) :
    sqDist (x + h • rgoDrift g η y x) (x' + h • rgoDrift g η y' x') ≤
      (1 - h / η) * sqDist x x' + h / η * sqDist y y' := by
  set a := 1 - h / η with ha
  set c := h / η with hc
  have hc0 : 0 ≤ c := div_nonneg hh hη.le
  have hca : c ≤ 1 / 2 := by rw [hc, div_le_iff₀ hη]; linarith
  have hac : a + c = 1 := by rw [ha]; ring
  have ha2 : 1 / 2 ≤ a := by linarith
  set u := x - x' with hu
  set w := grad g x - grad g x' with hw
  set q := y - y' with hq
  set p := a • u - h • w with hp
  have hdiff : x + h • rgoDrift g η y x - (x' + h • rgoDrift g η y' x') = p + c • q := by
    simp only [rgoDrift, hp, hu, hw, hq, ha, hc, smul_sub, sub_smul, one_smul, smul_neg,
      smul_smul]
    rw [show h * η⁻¹ = h / η by ring]
    abel
  rw [sqDist_eq_dotProduct, sqDist_eq_dotProduct, sqDist_eq_dotProduct, hdiff, ← hu, ← hq]
  have hco := grad_sub_dotProduct_le hg hL0 hL x x'
  rw [← hw, ← hu] at hco
  have hww : 0 ≤ w ⬝ᵥ w := RGOCouplingQuadraticPi.dot_self_nonneg _
  have huw : 0 ≤ u ⬝ᵥ w := by
    by_contra hneg; push Not at hneg; nlinarith
  have eP : p ⬝ᵥ p = a ^ 2 * (u ⬝ᵥ u) - 2 * a * h * (u ⬝ᵥ w) + h ^ 2 * (w ⬝ᵥ w) := by
    simp only [hp, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w u]
    ring
  have eD : (p + c • q) ⬝ᵥ (p + c • q) = p ⬝ᵥ p + 2 * c * (p ⬝ᵥ q) + c ^ 2 * (q ⬝ᵥ q) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm q p]
    ring
  have eA : (p - a • q) ⬝ᵥ (p - a • q) = p ⬝ᵥ p - 2 * a * (p ⬝ᵥ q) + a ^ 2 * (q ⬝ᵥ q) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm q p]
    ring
  have hA : 0 ≤ (p - a • q) ⬝ᵥ (p - a • q) := RGOCouplingQuadraticPi.dot_self_nonneg _
  have hP : p ⬝ᵥ p ≤ a ^ 2 * (u ⬝ᵥ u) := by
    rw [eP]
    have : h ^ 2 * (w ⬝ᵥ w) ≤ h * (h * L) * (u ⬝ᵥ w) := by
      rw [show h * (h * L) * (u ⬝ᵥ w) = h ^ 2 * (L * (u ⬝ᵥ w)) by ring]
      exact mul_le_mul_of_nonneg_left hco (by positivity)
    have h2 : h * (h * L) * (u ⬝ᵥ w) ≤ 2 * a * h * (u ⬝ᵥ w) := by
      rw [show 2 * a * h * (u ⬝ᵥ w) = h * (2 * a) * (u ⬝ᵥ w) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hh) huw
    linarith
  have hqq : 0 ≤ q ⬝ᵥ q := RGOCouplingQuadraticPi.dot_self_nonneg _
  rw [eD]
  -- `a (|p|² + 2c p⬝q + c²|q|²) ≤ |p|² + a c |q|²` since `c |p - a q|² ≥ 0`
  have key : a * (p ⬝ᵥ p + 2 * c * (p ⬝ᵥ q) + c ^ 2 * (q ⬝ᵥ q)) ≤
      a * (a * (u ⬝ᵥ u) + c * (q ⬝ᵥ q)) := by
    have hcA := mul_nonneg hc0 hA
    rw [eA] at hcA
    have hcsub : c = 1 - a := by linarith
    rw [hcsub] at hcA ⊢
    nlinarith
  exact le_of_mul_le_mul_left key (by linarith)

end FormalizeSampling.RGOCouplingLangevin
