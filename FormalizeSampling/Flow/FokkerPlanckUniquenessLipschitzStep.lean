module

public import FormalizeSampling.Flow.FokkerPlanckUniquenessLipschitzHeat
public import FormalizeSampling.Flow.FokkerPlanckUniquenessUnbounded

/-!
# One step of the approximate Kolmogorov dual for Lipschitz drifts

Status: **Verified.** The one-step dual test function used in
`Flow/FokkerPlanckUniquenessLipschitz.lean`: for a function `Θ ∈ BddC2`, a `C²` vector field `w`
(the frozen, smoothed drift) with `‖Dw‖ ≤ L` and `D²w` bounded, `D > 0` and a small `κ > 0`,

  `U(τ, x) = E Θ(Y),  Y = y + τ w(y),  y = x + S(τ) Z,  S(τ) = √(2D(τ + κ))`

(`stepDual`), i.e. a frozen Euler transport step of length `τ` followed by exact Gaussian
smoothing with variance `2D(τ + κ)`.

## Main results

* `hasDerivAt_stepDual`: `∂_τ U = V` (`stepDualDeriv`, differentiation under the Gaussian
  integral, for `τ + κ > 0`);
* `stepDualDeriv_eq`: `V = E[DΘ(Y) w(y)] + D ΔU` (the heat identity of
  `Flow/FokkerPlanckUniquenessLipschitzHeat`, `S S' = D`);
* `dotProduct_grad_stepDual`, `abs_transport_residual_le`: for every vector `β`,
  `|β ⬝ ∇U(x) - E[DΘ(Y) w(y)]| ≤ G (‖β - w(x)‖ + L S d + |τ| L ‖β‖)` where `‖DΘ‖ ≤ G`;
  so `-∂_τ U + β ⬝ ∇U + D ΔU` is small when `β ≈ w(x)`, `τ` and `S` small;
* `continuousAt_stepDualDeriv`: joint continuity of `V`;
* `abs_integral_step_le`: **the one-step estimate**. For a probability solution `ρ` of
  `WeakFokkerPlanck ρ b D` and a cutoff `χ`, with `ψ(s) = χ U(c - s)` on `[a, c]`,
  `|∫ χ U(0) dρ_c - ∫ χ U(c - a) dρ_a|` is at most `(c - a)` times
  `G (ε₁ + L S(c - a) d + (c - a) L B₁) + θ (M d B₁ g₁ + 2 D d g₁ G (1 + (c - a) L) + D M g₂)`,
  where `‖b_s - w‖ ≤ ε₁`, `‖b_s‖ ≤ B₁` on the support of `χ`, `‖∇χ‖ ≤ g₁`, `|Δχ| ≤ g₂`, the
  derivatives of `χ` vanish outside a set `T` with `ρ_s(T) ≤ θ`, and `|Θ| ≤ M`.

## Not proved here

* Nothing about iterating the step or about the choice of `w`, `κ`, `χ`; see
  `Flow/FokkerPlanckUniquenessLipschitz.lean`.
* The dual is only approximate (frozen drift, Euler transport); no exact Kolmogorov backward
  equation is solved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-- The noise scale `S(τ) = √(2D(τ + κ))` of the one-step dual. -/
noncomputable def stepSigma (D κ τ : ℝ) : ℝ := Real.sqrt (2 * D * (τ + κ))

/-- **The one-step dual.** `U(τ, x) = E Θ(y + τ w(y))`, `y = x + S(τ) Z`, `Z ∼ N(0, I_d)`:
Gaussian smoothing (variance `2D(τ + κ)`) of the frozen Euler transport `Θ ∘ (id + τ w)`. -/
noncomputable def stepDual (D κ : ℝ) (Θ : (Fin d → ℝ) → ℝ) (w : (Fin d → ℝ) → Fin d → ℝ)
    (τ : ℝ) : (Fin d → ℝ) → ℝ :=
  heatOp (stepSigma D κ τ) (fun y => Θ (y + τ • w y))

/-- The integrand of the `τ`-derivative of the one-step dual: the chain rule for
`τ ↦ Θ(y + τ w(y))`, `y = x + S(τ) z`. -/
noncomputable def stepDualIntegrand (D κ : ℝ) (Θ : (Fin d → ℝ) → ℝ)
    (w : (Fin d → ℝ) → Fin d → ℝ) (τ : ℝ) (x z : Fin d → ℝ) : ℝ :=
  fderiv ℝ Θ (x + stepSigma D κ τ • z + τ • w (x + stepSigma D κ τ • z))
    ((D / stepSigma D κ τ) • z + w (x + stepSigma D κ τ • z) +
      τ • fderiv ℝ w (x + stepSigma D κ τ • z) ((D / stepSigma D κ τ) • z))

/-- The `τ`-derivative of the one-step dual, `V(τ, x) = E[stepDualIntegrand]`. -/
noncomputable def stepDualDeriv (D κ : ℝ) (Θ : (Fin d → ℝ) → ℝ)
    (w : (Fin d → ℝ) → Fin d → ℝ) (τ : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ z, stepDualIntegrand D κ Θ w τ x z ∂stdGauss

/-- `S(τ) > 0` for `τ + κ > 0`, `D > 0`. -/
theorem stepSigma_pos {D κ τ : ℝ} (hD : 0 < D) (hτ : 0 < τ + κ) : 0 < stepSigma D κ τ :=
  Real.sqrt_pos.2 (by positivity)

/-- `S'(τ) = D / S(τ)` for `τ + κ > 0`. -/
theorem hasDerivAt_stepSigma {D κ τ : ℝ} (hD : 0 < D) (hτ : 0 < τ + κ) :
    HasDerivAt (stepSigma D κ) (D / stepSigma D κ τ) τ := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * D * (t + κ)) (2 * D) τ := by
    simpa using ((hasDerivAt_id τ).add_const κ).const_mul (2 * D)
  have := h1.sqrt (by positivity)
  show HasDerivAt (fun t => Real.sqrt (2 * D * (t + κ))) (D / Real.sqrt (2 * D * (τ + κ))) τ
  convert this using 1
  have hs : 0 < Real.sqrt (2 * D * (τ + κ)) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- `S` is continuous. -/
theorem continuous_stepSigma (D κ : ℝ) : Continuous (stepSigma D κ) :=
  Real.continuous_sqrt.comp (continuous_const.mul (continuous_id.add continuous_const))

/-- `‖w(y)‖ ≤ ‖w(0)‖ + L ‖y‖` if `‖Dw‖ ≤ L`. -/
theorem norm_le_of_fderiv_le {w : (Fin d → ℝ) → Fin d → ℝ} (hw : Differentiable ℝ w) {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (y : Fin d → ℝ) : ‖w y‖ ≤ ‖w 0‖ + L * ‖y‖ := by
  have := (convex_univ : Convex ℝ (univ : Set (Fin d → ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hw y) (fun y _ => hL y) (mem_univ 0) (mem_univ y)
  rw [sub_zero] at this
  have h2 := norm_sub_norm_le (w y) (w 0)
  linarith

/-- **Pointwise derivative of the integrand.** For fixed `x, z`, the map
`τ ↦ Θ(y + τ w(y))`, `y = x + S(τ) z`, has derivative `stepDualIntegrand` at `τ`
(`τ + κ > 0`). -/
theorem hasDerivAt_stepDual_integrand {D κ : ℝ} (hD : 0 < D) {Θ : (Fin d → ℝ) → ℝ}
    (hΘ : Differentiable ℝ Θ) {w : (Fin d → ℝ) → Fin d → ℝ} (hw : Differentiable ℝ w)
    {τ : ℝ} (hτ : 0 < τ + κ) (x z : Fin d → ℝ) :
    HasDerivAt (fun t => Θ (x + stepSigma D κ t • z + t • w (x + stepSigma D κ t • z)))
      (stepDualIntegrand D κ Θ w τ x z) τ := by
  have hS := hasDerivAt_stepSigma hD hτ
  have hy : HasDerivAt (fun t => x + stepSigma D κ t • z) ((D / stepSigma D κ τ) • z) τ :=
    (hS.smul_const z).const_add x
  have hwy : HasDerivAt (fun t => w (x + stepSigma D κ t • z))
      (fderiv ℝ w (x + stepSigma D κ τ • z) ((D / stepSigma D κ τ) • z)) τ :=
    (hw _).hasFDerivAt.comp_hasDerivAt τ hy
  have hY := hy.add ((hasDerivAt_id τ).smul hwy)
  have := (hΘ _).hasFDerivAt.comp_hasDerivAt τ hY
  unfold stepDualIntegrand
  convert this using 2
  all_goals try rfl
  rw [one_smul, id_eq]
  abel

/-- **Bound on the integrand.** If `‖DΘ‖ ≤ G`, `‖Dw‖ ≤ L`, `S(τ) ≤ Smax`, `D / S(τ) ≤ P` and
`|τ| ≤ tm` (all nonnegative), then `|stepDualIntegrand| ≤ G (‖w 0‖ + L ‖x‖ + c ‖z‖)` with
`c = P + L Smax + tm L P`. -/
theorem norm_stepDualIntegrand_le {D κ : ℝ} {Θ : (Fin d → ℝ) → ℝ} {G : ℝ}
    (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) {w : (Fin d → ℝ) → Fin d → ℝ} (hw : Differentiable ℝ w)
    {L : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) {τ Smax P tm : ℝ} (hS0 : 0 ≤ stepSigma D κ τ)
    (hS : stepSigma D κ τ ≤ Smax) (hP0 : 0 ≤ D / stepSigma D κ τ)
    (hP : D / stepSigma D κ τ ≤ P) (htm : |τ| ≤ tm) (x z : Fin d → ℝ) :
    ‖stepDualIntegrand D κ Θ w τ x z‖ ≤
      G * (‖w 0‖ + L * ‖x‖ + (P + L * Smax + tm * L * P) * ‖z‖) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  set S := stepSigma D κ τ
  set Q := D / stepSigma D κ τ
  set y := x + S • z
  have hy : ‖y‖ ≤ ‖x‖ + Smax * ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hS0]
    linarith [mul_le_mul_of_nonneg_right hS (norm_nonneg z)]
  have hwy := norm_le_of_fderiv_le hw hL y
  have hQz : ‖Q • z‖ ≤ P * ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg hP0]
    exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  have h3 : ‖τ • fderiv ℝ w y (Q • z)‖ ≤ tm * L * P * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |τ| * ‖fderiv ℝ w y (Q • z)‖ ≤ tm * (L * (P * ‖z‖)) := by
          refine mul_le_mul htm (((fderiv ℝ w y).le_opNorm _).trans ?_) (norm_nonneg _)
            ((abs_nonneg _).trans htm)
          exact mul_le_mul (hL y) hQz (norm_nonneg _) hL0
      _ = tm * L * P * ‖z‖ := by ring
  have hv : ‖Q • z + w y + τ • fderiv ℝ w y (Q • z)‖ ≤
      ‖w 0‖ + L * ‖x‖ + (P + L * Smax + tm * L * P) * ‖z‖ := by
    have := norm_add₃_le (a := Q • z) (b := w y) (c := τ • fderiv ℝ w y (Q • z))
    nlinarith [mul_le_mul_of_nonneg_left hy hL0]
  refine ((fderiv ℝ Θ _).le_opNorm _).trans ?_
  exact mul_le_mul (hG _) hv (norm_nonneg _) hG0

/-- Measurability (continuity in `z`) of the integrand. -/
theorem continuous_stepDualIntegrand {D κ : ℝ} {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ 1 Θ)
    {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 1 w) (τ : ℝ) (x : Fin d → ℝ) :
    Continuous (stepDualIntegrand D κ Θ w τ x) := by
  have hΘ' := hΘ.continuous_fderiv one_ne_zero
  have hw' := hw.continuous_fderiv one_ne_zero
  have hy : Continuous fun z : Fin d → ℝ => x + stepSigma D κ τ • z := by fun_prop
  have hQ : Continuous fun z : Fin d → ℝ => (D / stepSigma D κ τ) • z :=
    (continuous_const : Continuous fun _ : Fin d → ℝ => (D / stepSigma D κ τ)).smul
      continuous_id
  have hτw : Continuous fun z : Fin d → ℝ => τ • w (x + stepSigma D κ τ • z) :=
    (continuous_const : Continuous fun _ : Fin d → ℝ => τ).smul (hw.continuous.comp hy)
  unfold stepDualIntegrand
  refine (hΘ'.comp (hy.add hτw)).clm_apply ?_
  exact (hQ.add (hw.continuous.comp hy)).add
    ((continuous_const : Continuous fun _ : Fin d → ℝ => τ).smul
      ((hw'.comp hy).clm_apply hQ))

/-- **Differentiation of the one-step dual in `τ` (Verified).** For `D > 0`, `Θ` of class `C¹`
with `|Θ| ≤ M`, `‖DΘ‖ ≤ G`, `w` of class `C¹` with `‖Dw‖ ≤ L`, and `τ + κ > 0`:
`∂_τ U(τ, x) = V(τ, x)` (`stepDualDeriv`). -/
theorem hasDerivAt_stepDual {D κ : ℝ} (hD : 0 < D) {Θ : (Fin d → ℝ) → ℝ}
    (hΘ : ContDiff ℝ 1 Θ) {M G : ℝ} (hM : ∀ y, |Θ y| ≤ M) (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G)
    {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 1 w) {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) {τ : ℝ} (hτ : 0 < τ + κ) (x : Fin d → ℝ) :
    HasDerivAt (fun t => stepDual D κ Θ w t x) (stepDualDeriv D κ Θ w τ x) τ := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hΘd : Differentiable ℝ Θ := hΘ.differentiable one_ne_zero
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  set δ : ℝ := (τ + κ) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set Smax : ℝ := Real.sqrt (2 * D * (τ + κ + δ))
  set Smin : ℝ := Real.sqrt (2 * D * δ)
  have hSmin : 0 < Smin := Real.sqrt_pos.2 (by positivity)
  set P : ℝ := D / Smin
  set tm : ℝ := |τ| + δ
  have hball : ∀ t ∈ ball τ δ, 0 < t + κ ∧ stepSigma D κ t ≤ Smax ∧
      0 ≤ D / stepSigma D κ t ∧ D / stepSigma D κ t ≤ P ∧ |t| ≤ tm := by
    intro t ht
    rw [mem_ball, Real.dist_eq, abs_lt] at ht
    have htk : δ < t + κ := by linarith
    have hS1 : Smin ≤ stepSigma D κ t :=
      Real.sqrt_le_sqrt (by nlinarith)
    refine ⟨by linarith, Real.sqrt_le_sqrt (by nlinarith), div_nonneg hD.le (Real.sqrt_nonneg _),
      div_le_div_of_nonneg_left hD.le hSmin hS1, ?_⟩
    calc |t| = |τ + (t - τ)| := by ring_nf
      _ ≤ |τ| + |t - τ| := abs_add_le _ _
      _ ≤ tm := by have := abs_lt.2 ⟨ht.1, ht.2⟩; linarith
  set bound : (Fin d → ℝ) → ℝ :=
    fun z => G * (‖w 0‖ + L * ‖x‖ + (P + L * Smax + tm * L * P) * ‖z‖)
  have hbint : Integrable bound stdGauss :=
    ((integrable_const _).add (integrable_norm_stdGauss.const_mul _)).const_mul G
  have hcF : ∀ t, Continuous fun z : Fin d → ℝ =>
      Θ (x + stepSigma D κ t • z + t • w (x + stepSigma D κ t • z)) := fun t => by fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGauss)
    (F := fun t z => Θ (x + stepSigma D κ t • z + t • w (x + stepSigma D κ t • z)))
    (F' := fun t z => stepDualIntegrand D κ Θ w t x z) (bound := bound)
    (ball_mem_nhds τ hδ0) (Eventually.of_forall fun t => (hcF t).aestronglyMeasurable)
    (Integrable.of_bound (hcF τ).aestronglyMeasurable M
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM _))
    (continuous_stepDualIntegrand hΘ hw τ x).aestronglyMeasurable
    (ae_of_all _ fun z t ht => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hball t ht
      exact norm_stepDualIntegrand_le hG hwd hL (Real.sqrt_nonneg _) h2 h3 h4 h5 x z)
    hbint
    (ae_of_all _ fun z t ht => hasDerivAt_stepDual_integrand hD hΘd hwd (hball t ht).1 x z)
  exact key.2

/-! ### Regularity of the one-step dual and the heat identity -/

/-- Chain rule: `D(Θ ∘ (id + τ w))(y) v = DΘ(y + τ w(y)) (v + τ Dw(y) v)`. -/
theorem fderiv_comp_add_smul_apply {Θ : (Fin d → ℝ) → ℝ} (hΘ : Differentiable ℝ Θ)
    {w : (Fin d → ℝ) → Fin d → ℝ} (hw : Differentiable ℝ w) (τ : ℝ) (y v : Fin d → ℝ) :
    fderiv ℝ (fun y => Θ (y + τ • w y)) y v =
      fderiv ℝ Θ (y + τ • w y) (v + τ • fderiv ℝ w y v) := by
  have hF : HasFDerivAt (fun y => y + τ • w y)
      (ContinuousLinearMap.id ℝ (Fin d → ℝ) + τ • fderiv ℝ w y) y :=
    (hasFDerivAt_id y).add ((hw y).hasFDerivAt.const_smul τ)
  rw [show (fun y => Θ (y + τ • w y)) = Θ ∘ (fun y => y + τ • w y) from rfl,
    ((hΘ _).hasFDerivAt.comp y hF).fderiv]
  rfl

/-- The one-step dual is in `BddC2`. -/
theorem bddC2_stepDual {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ) {w : (Fin d → ℝ) → Fin d → ℝ}
    (hw : ContDiff ℝ 2 w) {L Mw : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L)
    (hMw : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ Mw) (D κ τ : ℝ) :
    BddC2 (stepDual D κ Θ w τ) :=
  bddC2_heatOp (bddC2_comp_add_smul hΘ hw hL hMw τ) _

/-- `|U(τ, x)| ≤ M` if `|Θ| ≤ M`. -/
theorem abs_stepDual_le {Θ : (Fin d → ℝ) → ℝ} {M : ℝ} (hM : ∀ y, |Θ y| ≤ M)
    (D κ : ℝ) (w : (Fin d → ℝ) → Fin d → ℝ) (τ : ℝ) (x : Fin d → ℝ) :
    |stepDual D κ Θ w τ x| ≤ M :=
  abs_heatOp_le (fun _ => hM _) _ x

/-- `‖DU(τ, x)‖ ≤ G (1 + |τ| L)` if `‖DΘ‖ ≤ G`, `‖Dw‖ ≤ L`. -/
theorem norm_fderiv_stepDual_le {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ) {G : ℝ}
    (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 2 w)
    {L Mw : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (hMw : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ Mw)
    (D κ τ : ℝ) (x : Fin d → ℝ) :
    ‖fderiv ℝ (stepDual D κ Θ w τ) x‖ ≤ G * (1 + |τ| * L) := by
  have hb := bddC2_comp_add_smul hΘ hw hL hMw τ
  unfold stepDual
  rw [fderiv_heatOp_of_bdd hb]
  exact norm_heatOp_le (norm_fderiv_comp_add_smul_le (hΘ.1.differentiable two_ne_zero) hG
    (hw.differentiable two_ne_zero) hL τ) _ x

/-- **Heat identity for the one-step dual (Verified).** For `D > 0`, `τ + κ > 0`, `Θ ∈ BddC2`
with `‖DΘ‖ ≤ G`, `w ∈ C²` with `‖Dw‖ ≤ L`, `‖D²w‖ ≤ Mw`:
`V(τ, x) = E[DΘ(Y) w(y)] + D ΔU(τ)(x)` (`y = x + S Z`, `Y = y + τ w(y)`). -/
theorem stepDualDeriv_eq {D κ : ℝ} (hD : 0 < D) {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ)
    {G : ℝ} (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) {w : (Fin d → ℝ) → Fin d → ℝ}
    (hw : ContDiff ℝ 2 w) {L Mw : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L)
    (hMw : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ Mw) {τ : ℝ} (hτ : 0 < τ + κ) (x : Fin d → ℝ) :
    stepDualDeriv D κ Θ w τ x =
      (∫ z, fderiv ℝ Θ (x + stepSigma D κ τ • z + τ • w (x + stepSigma D κ τ • z))
        (w (x + stepSigma D κ τ • z)) ∂stdGauss) +
      D * laplacian (stepDual D κ Θ w τ) x := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hΘd : Differentiable ℝ Θ := hΘ.1.differentiable two_ne_zero
  have hwd : Differentiable ℝ w := hw.differentiable two_ne_zero
  have hΘ' : Continuous (fderiv ℝ Θ) := hΘ.1.continuous_fderiv two_ne_zero
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  set S := stepSigma D κ τ with hSdef
  have hS : 0 < S := stepSigma_pos hD hτ
  set Φ : (Fin d → ℝ) → ℝ := fun y => Θ (y + τ • w y) with hΦ
  have hΦb : BddC2 Φ := bddC2_comp_add_smul hΘ hw hL hMw τ
  have hy : Continuous fun z : Fin d → ℝ => x + S • z := by fun_prop
  set A : (Fin d → ℝ) → ℝ := fun z => fderiv ℝ Θ (x + S • z + τ • w (x + S • z))
    (w (x + S • z)) with hA
  set B : (Fin d → ℝ) → ℝ := fun z => fderiv ℝ Φ (x + S • z) z with hB
  have hpt : ∀ z, stepDualIntegrand D κ Θ w τ x z = A z + D / S * B z := by
    intro z
    simp only [stepDualIntegrand, A, B, ← hSdef]
    have hv : (D / S) • z + w (x + S • z) + τ • fderiv ℝ w (x + S • z) ((D / S) • z) =
        w (x + S • z) + (D / S) • (z + τ • fderiv ℝ w (x + S • z) z) := by
      rw [map_smul, smul_add, smul_comm τ (D / S)]
      abel
    rw [fderiv_comp_add_smul_apply hΘd hwd, hv, map_add, map_smul, smul_eq_mul]
  have hAc : Continuous A :=
    (hΘ'.comp (hy.add ((continuous_const : Continuous fun _ : Fin d → ℝ => τ).smul
      (hw.continuous.comp hy)))).clm_apply (hw.continuous.comp hy)
  have hAi : Integrable A stdGauss := by
    refine ((integrable_const (G * (‖w 0‖ + L * ‖x‖))).add
      (integrable_norm_stdGauss.const_mul (G * L * S))).mono' hAc.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    refine ((fderiv ℝ Θ _).le_opNorm _).trans ?_
    have h1 := norm_le_of_fderiv_le hwd hL (x + S • z)
    have h2 : ‖x + S • z‖ ≤ ‖x‖ + S * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hS.le]
    calc ‖fderiv ℝ Θ _‖ * ‖w (x + S • z)‖ ≤ G * (‖w 0‖ + L * (‖x‖ + S * ‖z‖)) :=
          mul_le_mul (hG _) (h1.trans (by nlinarith)) (norm_nonneg _) hG0
      _ = G * (‖w 0‖ + L * ‖x‖) + G * L * S * ‖z‖ := by ring
  have hΦ' : Continuous (fderiv ℝ Φ) := hΦb.1.continuous_fderiv two_ne_zero
  obtain ⟨GΦ, hGΦ⟩ := hΦb.2.2.1
  have hBi : Integrable B stdGauss := by
    refine (integrable_norm_stdGauss.const_mul GΦ).mono'
      ((hΦ'.comp hy).clm_apply continuous_id).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    exact ((fderiv ℝ Φ _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hGΦ _) (norm_nonneg _))
  have hheat : ∫ z, B z ∂stdGauss = S * laplacian (stepDual D κ Θ w τ) x :=
    integral_fderiv_apply_eq_laplacian hΦb S x
  unfold stepDualDeriv
  simp_rw [hpt]
  rw [integral_add hAi (hBi.const_mul _), integral_const_mul, hheat]
  congr 1
  field_simp

/-- `β ⬝ ∇U(τ)(x) = E[DΘ(Y) (β + τ Dw(y) β)]` (`y = x + S Z`, `Y = y + τ w(y)`). -/
theorem dotProduct_grad_stepDual {D κ : ℝ} {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ)
    {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 2 w) {L Mw : ℝ}
    (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (hMw : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ Mw) (τ : ℝ)
    (x β : Fin d → ℝ) :
    β ⬝ᵥ grad (stepDual D κ Θ w τ) x =
      ∫ z, fderiv ℝ Θ (x + stepSigma D κ τ • z + τ • w (x + stepSigma D κ τ • z))
        (β + τ • fderiv ℝ w (x + stepSigma D κ τ • z) β) ∂stdGauss := by
  have hΦb := bddC2_comp_add_smul hΘ hw hL hMw τ
  obtain ⟨GΦ, hGΦ⟩ := hΦb.2.2.1
  have hΦ' : Continuous (fderiv ℝ (fun y => Θ (y + τ • w y))) :=
    hΦb.1.continuous_fderiv two_ne_zero
  rw [dotProduct_grad]
  unfold stepDual
  rw [fderiv_heatOp_of_bdd hΦb, heatOp,
    ContinuousLinearMap.integral_apply (integrable_comp_shift_of_bdd hΦ' hGΦ _ x)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact fderiv_comp_add_smul_apply (hΘ.1.differentiable two_ne_zero)
    (hw.differentiable two_ne_zero) τ _ β

/-- **Transport residual bound (Verified).** With `‖DΘ‖ ≤ G`, `‖Dw‖ ≤ L`, `S = S(τ) ≥ 0`:
`|β ⬝ ∇U(τ)(x) - E[DΘ(Y) w(y)]| ≤ G (‖β - w(x)‖ + L S d + |τ| L ‖β‖)` for every `β ∈ ℝᵈ`. -/
theorem abs_transport_residual_le {D κ : ℝ} {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ) {G : ℝ}
    (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 2 w)
    {L Mw : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (hMw : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ Mw)
    (τ : ℝ) (x β : Fin d → ℝ) :
    |β ⬝ᵥ grad (stepDual D κ Θ w τ) x -
        ∫ z, fderiv ℝ Θ (x + stepSigma D κ τ • z + τ • w (x + stepSigma D κ τ • z))
          (w (x + stepSigma D κ τ • z)) ∂stdGauss| ≤
      G * (‖β - w x‖ + L * stepSigma D κ τ * d + |τ| * L * ‖β‖) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hΘ' : Continuous (fderiv ℝ Θ) := hΘ.1.continuous_fderiv two_ne_zero
  have hwd : Differentiable ℝ w := hw.differentiable two_ne_zero
  have hw' : Continuous (fderiv ℝ w) := hw.continuous_fderiv two_ne_zero
  set S := stepSigma D κ τ with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hy : Continuous fun z : Fin d → ℝ => x + S • z := by fun_prop
  have hY : Continuous fun z : Fin d → ℝ => x + S • z + τ • w (x + S • z) :=
    hy.add ((continuous_const : Continuous fun _ : Fin d → ℝ => τ).smul
      (hw.continuous.comp hy))
  set F₁ : (Fin d → ℝ) → ℝ := fun z => fderiv ℝ Θ (x + S • z + τ • w (x + S • z))
    (β + τ • fderiv ℝ w (x + S • z) β)
  set F₂ : (Fin d → ℝ) → ℝ := fun z => fderiv ℝ Θ (x + S • z + τ • w (x + S • z))
    (w (x + S • z))
  have hwy : ∀ z, ‖w (x + S • z)‖ ≤ ‖w 0‖ + L * ‖x‖ + L * S * ‖z‖ := by
    intro z
    have h1 := norm_le_of_fderiv_le hwd hL (x + S • z)
    have h2 : ‖x + S • z‖ ≤ ‖x‖ + S * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hS0]
    nlinarith
  have hF₁ : Integrable F₁ stdGauss := by
    refine (integrable_const (G * (‖β‖ + |τ| * (L * ‖β‖)))).mono'
      ((hΘ'.comp hY).clm_apply (continuous_const.add
        ((continuous_const : Continuous fun _ : Fin d → ℝ => τ).smul
          ((hw'.comp hy).clm_apply continuous_const)))).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    refine ((fderiv ℝ Θ _).le_opNorm _).trans (mul_le_mul (hG _) ?_ (norm_nonneg _) hG0)
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (((fderiv ℝ w _).le_opNorm β).trans
      (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))) (abs_nonneg _)
  have hF₂ : Integrable F₂ stdGauss := by
    refine ((integrable_const (G * (‖w 0‖ + L * ‖x‖))).add
      (integrable_norm_stdGauss.const_mul (G * L * S))).mono'
      ((hΘ'.comp hY).clm_apply (hw.continuous.comp hy)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    refine ((fderiv ℝ Θ _).le_opNorm _).trans ?_
    calc ‖fderiv ℝ Θ _‖ * ‖w (x + S • z)‖ ≤ G * (‖w 0‖ + L * ‖x‖ + L * S * ‖z‖) :=
          mul_le_mul (hG _) (hwy z) (norm_nonneg _) hG0
      _ = G * (‖w 0‖ + L * ‖x‖) + G * L * S * ‖z‖ := by ring
  have hpt : ∀ z, |F₁ z - F₂ z| ≤ G * (‖β - w x‖ + |τ| * L * ‖β‖) + G * L * S * ‖z‖ := by
    intro z
    simp only [F₁, F₂]
    rw [← map_sub, ← Real.norm_eq_abs]
    refine ((fderiv ℝ Θ _).le_opNorm _).trans ?_
    have hlip : ‖w x - w (x + S • z)‖ ≤ L * (S * ‖z‖) := by
      have := (convex_univ : Convex ℝ (univ : Set (Fin d → ℝ))).norm_image_sub_le_of_norm_fderiv_le
        (fun y _ => hwd y) (fun y _ => hL y) (mem_univ (x + S • z)) (mem_univ x)
      rwa [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hS0] at this
    have hv : ‖β + τ • fderiv ℝ w (x + S • z) β - w (x + S • z)‖ ≤
        ‖β - w x‖ + |τ| * L * ‖β‖ + L * S * ‖z‖ := by
      have e : β + τ • fderiv ℝ w (x + S • z) β - w (x + S • z) =
          (β - w x) + τ • fderiv ℝ w (x + S • z) β + (w x - w (x + S • z)) := by abel
      rw [e]
      refine (norm_add₃_le).trans ?_
      have h3 : ‖τ • fderiv ℝ w (x + S • z) β‖ ≤ |τ| * L * ‖β‖ := by
        rw [norm_smul, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (((fderiv ℝ w _).le_opNorm β).trans
          (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))) (abs_nonneg _)
      linarith
    calc ‖fderiv ℝ Θ _‖ * ‖β + τ • fderiv ℝ w (x + S • z) β - w (x + S • z)‖
        ≤ G * (‖β - w x‖ + |τ| * L * ‖β‖ + L * S * ‖z‖) :=
          mul_le_mul (hG _) hv (norm_nonneg _) hG0
      _ = _ := by ring
  rw [dotProduct_grad_stepDual hΘ hw hL hMw, ← integral_sub hF₁ hF₂]
  calc |∫ z, (F₁ z - F₂ z) ∂stdGauss|
      ≤ ∫ z, (G * (‖β - w x‖ + |τ| * L * ‖β‖) + G * L * S * ‖z‖) ∂stdGauss := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le ((integrable_const _).add
          (integrable_norm_stdGauss.const_mul _))
          (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hpt z)
    _ = G * (‖β - w x‖ + |τ| * L * ‖β‖) + G * L * S * ∫ z, ‖z‖ ∂(stdGauss (d := d)) := by
        rw [integral_add (integrable_const _) (integrable_norm_stdGauss.const_mul _),
          integral_const, integral_const_mul (G * L * S)]
        simp
    _ ≤ G * (‖β - w x‖ + |τ| * L * ‖β‖) + G * L * S * d := by
        have : 0 ≤ G * L * S := by positivity
        nlinarith [integral_norm_stdGauss_le (d := d)]
    _ = _ := by ring

/-! ### Joint continuity of the `τ`-derivative -/

/-- **Joint continuity of `V` (Verified).** For `D > 0`, `Θ ∈ C¹` with `‖DΘ‖ ≤ G`, `w ∈ C¹`
with `‖Dw‖ ≤ L`, the map `(τ, x) ↦ V(τ, x)` is continuous at every `(τ₀, x₀)` with
`τ₀ + κ > 0` (dominated convergence). -/
theorem continuousAt_stepDualDeriv {D κ : ℝ} (hD : 0 < D) {Θ : (Fin d → ℝ) → ℝ}
    (hΘ : ContDiff ℝ 1 Θ) {G : ℝ} (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G)
    {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 1 w) {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) {τ₀ : ℝ} (hτ₀ : 0 < τ₀ + κ) (x₀ : Fin d → ℝ) :
    ContinuousAt (fun q : ℝ × (Fin d → ℝ) => stepDualDeriv D κ Θ w q.1 q.2) (τ₀, x₀) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hΘ' := hΘ.continuous_fderiv one_ne_zero
  have hw' := hw.continuous_fderiv one_ne_zero
  set δ : ℝ := (τ₀ + κ) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set Smax : ℝ := Real.sqrt (2 * D * (τ₀ + κ + δ))
  set Smin : ℝ := Real.sqrt (2 * D * δ)
  have hSmin : 0 < Smin := Real.sqrt_pos.2 (by positivity)
  set P : ℝ := D / Smin
  set tm : ℝ := |τ₀| + δ
  set c : ℝ := P + L * Smax + tm * L * P
  have hc0 : 0 ≤ c := by positivity
  set bound : (Fin d → ℝ) → ℝ := fun z => G * (‖w 0‖ + L * (‖x₀‖ + 1) + c * ‖z‖)
  have hbint : Integrable bound stdGauss :=
    ((integrable_const _).add (integrable_norm_stdGauss.const_mul _)).const_mul G
  have hnhds : ball (τ₀, x₀) (min δ 1) ∈ 𝓝 (τ₀, x₀) := ball_mem_nhds _ (by positivity)
  refine continuousAt_of_dominated (bound := bound)
    (Eventually.of_forall fun q => (continuous_stepDualIntegrand hΘ hw q.1 q.2
      ).aestronglyMeasurable) ?_ hbint (ae_of_all _ fun z => ?_)
  · filter_upwards [hnhds] with q hq
    refine ae_of_all _ fun z => ?_
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
    have h1 : dist q.1 τ₀ < δ := hq.1.trans_le (min_le_left _ _)
    have h2 : dist q.2 x₀ < 1 := hq.2.trans_le (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at h1
    rw [dist_eq_norm] at h2
    have htk : δ < q.1 + κ := by linarith
    have hS1 : Smin ≤ stepSigma D κ q.1 := Real.sqrt_le_sqrt (by nlinarith)
    have htm : |q.1| ≤ tm := by
      calc |q.1| = |τ₀ + (q.1 - τ₀)| := by ring_nf
        _ ≤ |τ₀| + |q.1 - τ₀| := abs_add_le _ _
        _ ≤ tm := by have := abs_lt.2 ⟨h1.1, h1.2⟩; linarith
    have hb := norm_stepDualIntegrand_le hG hwd hL (Real.sqrt_nonneg _)
      (Real.sqrt_le_sqrt (by nlinarith) : stepSigma D κ q.1 ≤ Smax)
      (div_nonneg hD.le (Real.sqrt_nonneg _)) (div_le_div_of_nonneg_left hD.le hSmin hS1) htm
      q.2 z
    have hx : ‖q.2‖ ≤ ‖x₀‖ + 1 := by
      have := norm_sub_norm_le q.2 x₀; linarith
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    nlinarith [mul_le_mul_of_nonneg_left hx hL0]
  · have hS : ContinuousAt (fun q : ℝ × (Fin d → ℝ) => stepSigma D κ q.1) (τ₀, x₀) :=
      ((continuous_stepSigma D κ).comp continuous_fst).continuousAt
    have hP : ContinuousAt (fun q : ℝ × (Fin d → ℝ) => D / stepSigma D κ q.1) (τ₀, x₀) :=
      continuousAt_const.div hS (stepSigma_pos hD hτ₀).ne'
    set Ψ : ℝ × ℝ × ℝ × (Fin d → ℝ) → ℝ := fun p =>
      fderiv ℝ Θ (p.2.2.2 + p.1 • z + p.2.2.1 • w (p.2.2.2 + p.1 • z))
        (p.2.1 • z + w (p.2.2.2 + p.1 • z) +
          p.2.2.1 • fderiv ℝ w (p.2.2.2 + p.1 • z) (p.2.1 • z)) with hΨ
    have hy : Continuous fun p : ℝ × ℝ × ℝ × (Fin d → ℝ) => p.2.2.2 + p.1 • z := by fun_prop
    have hΨc : Continuous Ψ := by
      refine (hΘ'.comp (hy.add (continuous_snd.comp continuous_snd |>.fst.smul
        (hw.continuous.comp hy)))).clm_apply ?_
      exact ((continuous_snd.fst.smul continuous_const).add (hw.continuous.comp hy)).add
        ((continuous_snd.comp continuous_snd |>.fst).smul
          ((hw'.comp hy).clm_apply (continuous_snd.fst.smul continuous_const)))
    have hin : ContinuousAt (fun q : ℝ × (Fin d → ℝ) =>
        (stepSigma D κ q.1, D / stepSigma D κ q.1, q.1, q.2)) (τ₀, x₀) :=
      hS.prodMk (hP.prodMk (continuous_fst.continuousAt.prodMk continuous_snd.continuousAt))
    exact hΨc.continuousAt.comp hin

/-! ### The one-step estimate -/

/-- `‖∇f(x)‖ ≤ ‖Df(x)‖` (sup norm of the coordinate gradient). -/
theorem norm_grad_le_norm_fderiv (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ‖grad f x‖ ≤ ‖fderiv ℝ f x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine ((fderiv ℝ f x).le_opNorm _).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (by rw [Pi.norm_single]; simp)

/-- **One-step estimate for the approximate dual (Verified).** Let `ρ` be a curve of
probability measures on `t ≥ 0` solving `WeakFokkerPlanck ρ b D` (`D > 0`), `0 ≤ a ≤ c`,
`b s` continuous for `s ∈ [a, c]`, `κ > 0`. Let `Θ ∈ BddC2` with `|Θ| ≤ M`, `‖DΘ‖ ≤ G`; `w ∈ C²`
with `‖Dw‖ ≤ L`, `‖D²w‖ ≤ Mw`; and `χ ∈ C²_c` with `|χ| ≤ 1`, `‖∇χ‖ ≤ g₁`, `|Δχ| ≤ g₂`, whose
gradient and Laplacian vanish outside a measurable set `T` with `ρ_s(T) ≤ θ` for
`s ∈ [a, c]`. If `‖b_s(x) - w(x)‖ ≤ ε₁` and `‖b_s(x)‖ ≤ B₁` (`ε₁, B₁ ≥ 0`) for `s ∈ [a, c]`,
`x ∈ tsupport χ`, then with `U = stepDual D κ Θ w`:

  `|∫ χ U(0) dρ_c - ∫ χ U(c - a) dρ_a| ≤ (c - a) (A + θ B)`,
  `A = G (ε₁ + L S(c - a) d + (c - a) L B₁)`,
  `B = M d B₁ g₁ + 2 D d g₁ G (1 + (c - a) L) + D M g₂`.

Proof: `ψ(s) = χ U(c - s)` is a `C²_c` test function with continuous time derivative
`-χ V(c - s)`; along the solution `d/ds ∫ ψ(s) dρ_s = ∫ r(s) dρ_s` with
`r = χ (b_s ⬝ ∇U - E[DΘ(Y) w(y)]) + U b_s ⬝ ∇χ + 2 D ∇χ ⬝ ∇U + D U Δχ` (heat identity), bounded
by `A + B 1_T`; then the mean value inequality. -/
theorem abs_integral_step_le {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D κ : ℝ} (hD : 0 < D) (hκ : 0 < κ)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hbc : ∀ s ∈ Icc a c, Continuous (b s))
    {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ) {M G : ℝ} (hM : ∀ y, |Θ y| ≤ M)
    (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 2 w)
    {L Mw : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (hMw : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ Mw)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ x, |χ x| ≤ 1) {g₁ g₂ : ℝ} (hg₁ : ∀ x, ‖grad χ x‖ ≤ g₁)
    (hg₂ : ∀ x, |laplacian χ x| ≤ g₂) {T : Set (Fin d → ℝ)} (hT : MeasurableSet T)
    (hTχ : ∀ x ∉ T, grad χ x = 0 ∧ laplacian χ x = 0) {θ : ℝ}
    (hθ : ∀ s ∈ Icc a c, (ρ s).real T ≤ θ) {ε₁ B₁ : ℝ} (hε₀ : 0 ≤ ε₁) (hB₀ : 0 ≤ B₁)
    (hε₁ : ∀ s ∈ Icc a c, ∀ x ∈ tsupport χ, ‖b s x - w x‖ ≤ ε₁)
    (hB₁ : ∀ s ∈ Icc a c, ∀ x ∈ tsupport χ, ‖b s x‖ ≤ B₁) :
    |∫ x, χ x * stepDual D κ Θ w 0 x ∂(ρ c) -
        ∫ x, χ x * stepDual D κ Θ w (c - a) x ∂(ρ a)| ≤
      (c - a) * (G * (ε₁ + L * stepSigma D κ (c - a) * d + (c - a) * L * B₁) +
        θ * (M * (d * B₁ * g₁) + 2 * D * (d * g₁ * (G * (1 + (c - a) * L))) + D * M * g₂)) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hg₁0 : 0 ≤ g₁ := (norm_nonneg _).trans (hg₁ 0)
  have hg₂0 : 0 ≤ g₂ := (abs_nonneg _).trans (hg₂ 0)
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.1.of_le (by norm_num)
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hχd : Differentiable ℝ χ := hχ.differentiable two_ne_zero
  set U := stepDual D κ Θ w with hUdef
  set V := stepDualDeriv D κ Θ w with hVdef
  have hUb : ∀ τ, BddC2 (U τ) := fun τ => bddC2_stepDual hΘ hw hL hMw D κ τ
  set ψ : ℝ → (Fin d → ℝ) → ℝ := fun s x => χ x * U (c - s) x with hψ
  set g : ℝ → (Fin d → ℝ) → ℝ := fun s x => -(χ x * V (max (c - s) 0) x) with hg
  have hψT : ∀ s, TestFunction2 (ψ s) := fun s =>
    ⟨hχ.mul (hUb (c - s)).1, hχc.mul_right⟩
  have hd : ∀ s ∈ Icc a c, ∀ x, HasDerivWithinAt (fun u => ψ u x) (g s x) (Icc a c) s := by
    intro s hs x
    have hτ : 0 < c - s + κ := by linarith [hs.2]
    have h1 := hasDerivAt_stepDual hD hΘ1 hM hG hw1 hL hτ x
    have h2 : HasDerivAt (fun u : ℝ => c - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub c
    have h3 := (h1.comp s h2).const_mul (χ x)
    have hmax : max (c - s) 0 = c - s := max_eq_left (by linarith [hs.2])
    refine (h3.hasDerivWithinAt).congr_deriv ?_
    simp only [g, hmax, hVdef]
    ring
  have hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) := by
    refine continuous_iff_continuousAt.2 fun q => ?_
    have hV := continuousAt_stepDualDeriv (κ := κ) hD hΘ1 hG hw1 hL
      (τ₀ := max (c - q.1) 0) (by linarith [le_max_right (c - q.1) 0]) q.2
    have hin : Continuous fun q : ℝ × (Fin d → ℝ) => (max (c - q.1) 0, q.2) :=
      ((continuous_const.sub continuous_fst).max continuous_const).prodMk continuous_snd
    have hc := ContinuousAt.comp (x := q)
      (f := fun q : ℝ × (Fin d → ℝ) => (max (c - q.1) 0, q.2)) hV hin.continuousAt
    exact ((hχ.continuous.comp continuous_snd).continuousAt.mul hc).neg
  have hgK : ∀ s ∈ Icc a c, ∀ x ∉ tsupport χ, g s x = 0 := fun s _ x hx => by
    simp [g, image_eq_zero_of_notMem_tsupport hx]
  -- the residual
  set r : ℝ → (Fin d → ℝ) → ℝ := fun s x =>
    g s x + (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) with hr
  set A : ℝ := G * (ε₁ + L * stepSigma D κ (c - a) * d + (c - a) * L * B₁) with hA
  set B : ℝ := M * (d * B₁ * g₁) + 2 * D * (d * g₁ * (G * (1 + (c - a) * L))) + D * M * g₂
    with hB
  have hca : 0 ≤ c - a := by linarith
  have hA0 : 0 ≤ A := by
    have := Real.sqrt_nonneg (2 * D * (c - a + κ))
    simp only [hA, stepSigma]; positivity
  have hB0 : 0 ≤ B := by simp only [hB]; positivity
  have hrb : ∀ s ∈ Icc a c, ∀ x, |r s x| ≤ A + B * T.indicator 1 x := by
    intro s hs x
    have hs0 : 0 ≤ c - s := by linarith [hs.2]
    have hτ : 0 < c - s + κ := by linarith
    have hmax : max (c - s) 0 = c - s := max_eq_left hs0
    have hUd : Differentiable ℝ (U (c - s)) := (hUb (c - s)).1.differentiable two_ne_zero
    have hgm := grad_mul hχd hUd x
    have hlm := laplacian_mul hχ (hUb (c - s)).1 x
    have hVe := stepDualDeriv_eq hD hΘ hG hw hL hMw hτ x
    set I := ∫ z, fderiv ℝ Θ (x + stepSigma D κ (c - s) • z +
      (c - s) • w (x + stepSigma D κ (c - s) • z)) (w (x + stepSigma D κ (c - s) • z))
      ∂stdGauss with hI
    have he : r s x = χ x * (b s x ⬝ᵥ grad (U (c - s)) x - I) +
        U (c - s) x * (b s x ⬝ᵥ grad χ x) + 2 * D * (grad χ x ⬝ᵥ grad (U (c - s)) x) +
        D * U (c - s) x * laplacian χ x := by
      simp only [hr, hg, hψ, hmax]
      rw [hgm, hlm, show V (c - s) x = I + D * laplacian (U (c - s)) x from hVe,
        dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [he]
    by_cases hx : x ∈ tsupport χ
    · have hSmono : stepSigma D κ (c - s) ≤ stepSigma D κ (c - a) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith [hs.1]) (by positivity))
      have h1 : |χ x * (b s x ⬝ᵥ grad (U (c - s)) x - I)| ≤ A := by
        rw [abs_mul]
        have hres := abs_transport_residual_le (D := D) (κ := κ) hΘ hG hw hL hMw (c - s) x
          (b s x)
        have hres' : |b s x ⬝ᵥ grad (U (c - s)) x - I| ≤ A := by
          refine hres.trans (mul_le_mul_of_nonneg_left ?_ hG0)
          rw [abs_of_nonneg hs0]
          have hε := hε₁ s hs x hx
          have hb := hB₁ s hs x hx
          have hm1 : L * stepSigma D κ (c - s) * d ≤ L * stepSigma D κ (c - a) * d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSmono hL0) (by positivity)
          have hm2 : (c - s) * L * ‖b s x‖ ≤ (c - a) * L * B₁ :=
            mul_le_mul (mul_le_mul_of_nonneg_right (by linarith [hs.1]) hL0) hb
              (norm_nonneg _) (mul_nonneg hca hL0)
          linarith
        calc |χ x| * |b s x ⬝ᵥ grad (U (c - s)) x - I| ≤ 1 * A :=
              mul_le_mul (hχ1 x) hres' (abs_nonneg _) zero_le_one
          _ = A := one_mul A
      by_cases hxT : x ∈ T
      · have hgU : ‖grad (U (c - s)) x‖ ≤ G * (1 + (c - a) * L) := by
          refine (norm_grad_le_norm_fderiv _ x).trans ?_
          refine (norm_fderiv_stepDual_le hΘ hG hw hL hMw D κ (c - s) x).trans ?_
          rw [abs_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left (by nlinarith [hs.1]) hG0
        have hUx := abs_stepDual_le hM D κ w (c - s) x
        have hbx := hB₁ s hs x hx
        have h2 : |U (c - s) x * (b s x ⬝ᵥ grad χ x)| ≤ M * (d * B₁ * g₁) := by
          rw [abs_mul]
          refine mul_le_mul hUx ((abs_dotProduct_le_norm _ _).trans ?_) (abs_nonneg _) hM0
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hbx (hg₁ x) (norm_nonneg _)
            ((norm_nonneg _).trans hbx)) (Nat.cast_nonneg _)
        have h3 : |2 * D * (grad χ x ⬝ᵥ grad (U (c - s)) x)| ≤
            2 * D * (d * g₁ * (G * (1 + (c - a) * L))) := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * D)]
          refine mul_le_mul_of_nonneg_left ((abs_dotProduct_le_norm _ _).trans ?_)
            (by positivity)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hg₁ x) hgU (norm_nonneg _) hg₁0)
            (Nat.cast_nonneg _)
        have h4 : |D * U (c - s) x * laplacian χ x| ≤ D * M * g₂ := by
          rw [abs_mul, abs_mul, abs_of_pos hD]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hUx hD.le) (hg₂ x) (abs_nonneg _)
            (by positivity)
        rw [Set.indicator_of_mem hxT, Pi.one_apply, mul_one]
        calc _ ≤ |χ x * (b s x ⬝ᵥ grad (U (c - s)) x - I)| +
              |U (c - s) x * (b s x ⬝ᵥ grad χ x)| +
              |2 * D * (grad χ x ⬝ᵥ grad (U (c - s)) x)| +
              |D * U (c - s) x * laplacian χ x| := by
              exact (abs_add_le _ _).trans (add_le_add (abs_add_three _ _ _) le_rfl)
          _ ≤ A + B := by rw [hB]; linarith
      · obtain ⟨hg0, hl0⟩ := hTχ x hxT
        rw [Set.indicator_of_notMem hxT, hg0, hl0]
        simpa using h1
    · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      obtain ⟨hg0, hl0⟩ := grad_laplacian_eq_zero_of_notMem_tsupport hx
      rw [hχx, hg0, hl0]
      have hBi : 0 ≤ B * T.indicator 1 x :=
        mul_nonneg hB0 (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      simp only [zero_mul, mul_zero, dotProduct_zero, zero_dotProduct, add_zero, abs_zero]
      linarith
  -- integrability and the derivative
  have hLc : ∀ s ∈ Icc a c, Continuous fun x => b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x :=
    fun s hs => ((hbc s hs).dotProduct (continuous_grad (hψT s).1)).add
      (continuous_const.mul (continuous_laplacian (hψT s).1))
  have hLK : ∀ s, HasCompactSupport fun x => b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x :=
    fun s => HasCompactSupport.intro hχc fun x hx => by
      have hx' : x ∉ tsupport (ψ s) := fun h => hx (tsupport_mul_subset_left h)
      obtain ⟨h1, h2⟩ := grad_laplacian_eq_zero_of_notMem_tsupport hx'
      simp [h1, h2]
  have hgs : ∀ s, Continuous (g s) := fun s => hgc.comp (continuous_const.prodMk continuous_id)
  have hgK' : ∀ s ∈ Icc a c, HasCompactSupport (g s) := fun s hs =>
    HasCompactSupport.intro hχc fun x hx => hgK s hs x hx
  have hderiv : ∀ s ∈ Icc a c, HasDerivWithinAt (fun u => ∫ x, ψ u x ∂(ρ u))
      (∫ x, r s x ∂(ρ s)) (Icc a c) s := by
    intro s hs
    have := hprob s (ha.trans hs.1)
    have h := hasDerivWithinAt_integral_fp_of_continuous hprob hρ ha (fun s _ => hψT s) hd hgc
      hχc hgK hs
    rwa [← integral_add ((hgs s).integrable_of_hasCompactSupport (hgK' s hs))
      ((hLc s hs).integrable_of_hasCompactSupport (hLK s))] at h
  have hbound : ∀ s ∈ Ico a c, ‖∫ x, r s x ∂(ρ s)‖ ≤ A + B * θ := by
    intro s hs
    have hs' : s ∈ Icc a c := Ico_subset_Icc_self hs
    have := hprob s (ha.trans hs'.1)
    have hI1 : Integrable (T.indicator (1 : (Fin d → ℝ) → ℝ)) (ρ s) :=
      (integrable_const (1 : ℝ)).indicator hT
    have hint : Integrable (fun x => A + B * T.indicator 1 x) (ρ s) :=
      (integrable_const A).add (hI1.const_mul B)
    calc ‖∫ x, r s x ∂(ρ s)‖ ≤ ∫ x, (A + B * T.indicator 1 x) ∂(ρ s) :=
          norm_integral_le_of_norm_le hint
            (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hrb s hs' x)
      _ = A + B * (ρ s).real T := by
          rw [integral_add (integrable_const A) (hI1.const_mul B), integral_const_mul B,
            integral_indicator_one hT]
          simp
      _ ≤ A + B * θ := by
          have := hθ s hs'
          nlinarith
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound c ⟨hac, le_rfl⟩
  simp only [hψ, sub_self, Real.norm_eq_abs] at hmv
  have e : (c - a) * (A + θ * B) = (A + B * θ) * (c - a) := by ring
  rw [e]
  exact hmv

end FormalizeSampling.FokkerPlanckUniqueness
