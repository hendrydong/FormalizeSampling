module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import FormalizeSampling.Flow.DiPernaLionsRenormalizationBeta

/-!
# DiPerna–Lions uniqueness for velocities of linear growth

Status: **Verified.** Uniqueness of probability-density solutions of the continuity equation
`WeakContinuityDensity u v` for `v ∈ W^{1,1}_loc` with `div v ∈ L^∞` and **linear growth**
`‖v(x)‖ ≤ M (1 + ‖x‖)`, in every dimension; essentially bounded velocities are the special case
`ae_eq_of_weakContinuityDensity_diPernaLions`.

## Method

The difference `w = u - u'` is renormalized with the bounded function
`β(s) = s² / (1 + s²)` (`dlBeta`) using `renormalized_identity_of_linearGrowth`
(`Flow/DiPernaLionsRenormalizationBeta.lean`); `|β(w) - w β'(w)| ≤ β(w)` gives the Gronwall
term `C ∫ β(w) χ_R`. The cut-off error `∫ β(w_s) v ⬝ ∇χ_R` is no longer `O(1/R)`; instead
`|v ⬝ ∇χ_R| ≤ 3 d M D₁ (1 - χ_{R/2})` (`exists_abs_dotProduct_grad_dlCutoff_le_tail`) and
`β(w_s) ≤ |w_s| ≤ u_s + u'_s`, so it is bounded by the **tail mass**
`τ_R(s) = 2 - ∫ u_s χ_{R/2} - ∫ u'_s χ_{R/2}`. Each `τ_R` is continuous in `s` (weak
continuity of the solutions, so no joint measurability in `(s, x)` is needed), `0 ≤ τ_R ≤ 2`,
and `τ_R(s) → 0` for every `s` because each `u_s` is a probability density; dominated
convergence in `s` gives `∫₀ᵀ τ_R → 0` (tightness in time).

The commutator lemma is isolated as a hypothesis (`ae_eq_of_weakContinuityDensity_of_commutator`)
and discharged here for bounded densities (`exists_commutator_bound_of_ae_bounded`) and in
`Flow/DiPernaLionsLp.lean` for `L^p` densities.

## Main results

* `dlBeta` and its properties; `exists_abs_dotProduct_grad_dlCutoff_le_tail`.
* `ae_eq_zero_of_renormalized_of_tail`: the Gronwall/tightness step.
* `WeakContinuityDensity.sub_of_linearGrowth`, `exists_measurable_representatives`.
* `ae_eq_of_weakContinuityDensity_of_commutator`: uniqueness from the commutator hypothesis.
* `ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth`: **DiPerna–Lions uniqueness with
  linear growth** (bounded densities); `ae_eq_of_weakContinuityDensity_diPernaLions`: the case of
  essentially bounded `v`.

## Not proved here

* The general DiPerna–Lions growth condition `v / (1 + |x|) ∈ L¹ + L^∞`; only pointwise
  (a.e.) linear growth is treated.
* Signed or non-probability solutions: the tail control uses that the compared solutions are
  probability densities (`|w| ≤ u + u'`).
* Time-dependent velocities `v ∈ L¹_t W^{1,1}_loc`, existence, and the Lagrangian flow.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- The bounded **renormalization function** `β(s) = s² / (1 + s²)` used for uniqueness:
smooth, `0 ≤ β ≤ 1`, `β(s) ≤ |s|`, `|β'| ≤ 1`, `|β(s) - s β'(s)| ≤ β(s)`, `β(s) = 0 ↔ s = 0`. -/
noncomputable def dlBeta (s : ℝ) : ℝ := s ^ 2 / (1 + s ^ 2)

/-- `β'(s) = 2 s / (1 + s²)²` (Verified). -/
theorem hasDerivAt_dlBeta (s : ℝ) : HasDerivAt dlBeta (2 * s / (1 + s ^ 2) ^ 2) s := by
  have h1 : (1 + s ^ 2) ≠ 0 := by positivity
  have h := ((hasDerivAt_pow 2 s).div ((hasDerivAt_pow 2 s).const_add 1) h1)
  convert h using 1
  · funext x; simp [dlBeta]
  · field_simp
    simp

/-- `deriv β s = 2 s / (1 + s²)²` (Verified). -/
theorem deriv_dlBeta (s : ℝ) : deriv dlBeta s = 2 * s / (1 + s ^ 2) ^ 2 :=
  (hasDerivAt_dlBeta s).deriv

/-- `β` is smooth (Verified). -/
theorem contDiff_dlBeta : ContDiff ℝ ∞ dlBeta :=
  (contDiff_id.pow 2).div (contDiff_const.add (contDiff_id.pow 2)) fun x => by positivity

/-- `0 ≤ β` (Verified). -/
theorem dlBeta_nonneg (s : ℝ) : 0 ≤ dlBeta s := by unfold dlBeta; positivity

/-- `β ≤ 1` (Verified). -/
theorem dlBeta_le_one (s : ℝ) : dlBeta s ≤ 1 := by
  unfold dlBeta
  rw [div_le_one (by positivity)]
  linarith

/-- `|β| ≤ 1` (Verified). -/
theorem abs_dlBeta_le (s : ℝ) : |dlBeta s| ≤ 1 := by
  rw [abs_of_nonneg (dlBeta_nonneg s)]; exact dlBeta_le_one s

/-- `β(s) ≤ |s|` (Verified). -/
theorem dlBeta_le_abs (s : ℝ) : dlBeta s ≤ |s| := by
  unfold dlBeta
  rw [div_le_iff₀ (by positivity)]
  have ha := abs_nonneg s
  have hs : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  rw [hs]
  nlinarith [sq_nonneg (|s| - 1), mul_nonneg ha (sq_nonneg (|s| - 1))]

/-- `|β'| ≤ 1` (Verified). -/
theorem abs_deriv_dlBeta_le (s : ℝ) : |deriv dlBeta s| ≤ 1 := by
  rw [deriv_dlBeta, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + s ^ 2) ^ 2),
    div_le_one (by positivity), abs_mul, abs_two]
  have hs : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  rw [hs]
  nlinarith [sq_nonneg (|s| - 1), abs_nonneg s, sq_nonneg (|s|)]

/-- `|β(s) - s β'(s)| ≤ β(s)` (Verified): the divergence source term of the renormalized
equation is controlled by `β` itself. -/
theorem abs_dlBeta_sub_mul_deriv_le (s : ℝ) :
    |dlBeta s - s * deriv dlBeta s| ≤ dlBeta s := by
  have e : dlBeta s - s * deriv dlBeta s = s ^ 2 * (s ^ 2 - 1) / (1 + s ^ 2) ^ 2 := by
    rw [deriv_dlBeta, dlBeta]
    field_simp
    ring
  have hp : (0 : ℝ) < 1 + s ^ 2 := by positivity
  rw [e, abs_div, abs_of_pos (pow_pos hp 2), div_le_iff₀ (pow_pos hp 2), dlBeta, abs_mul,
    abs_of_nonneg (sq_nonneg s)]
  have h1 : |s ^ 2 - 1| ≤ 1 + s ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]
  calc s ^ 2 * |s ^ 2 - 1| ≤ s ^ 2 * (1 + s ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    _ = s ^ 2 / (1 + s ^ 2) * (1 + s ^ 2) ^ 2 := by field_simp

/-- `β(s) = 0` forces `s = 0` (Verified). -/
theorem eq_zero_of_dlBeta_eq_zero {s : ℝ} (h : dlBeta s = 0) : s = 0 := by
  unfold dlBeta at h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  · nlinarith [sq_nonneg s]

/-! ### Cut-offs -/

/-- `∇χ_R = 0` on the open ball `‖x‖ < R` (Verified). -/
theorem grad_dlCutoff_eq_zero_of_lt {R : ℝ} (hR : 0 < R) {x : Fin d → ℝ} (hx : ‖x‖ < R) :
    grad (dlCutoff d R) x = 0 := by
  have h : dlCutoff d R =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact dlCutoff_eq_one hR (le_of_lt hy)
  funext i
  simp [grad, partialDeriv, h.fderiv_eq]

/-- `χ_R(x) = 0` for `‖x‖ ≥ 2R` (Verified). -/
theorem dlCutoff_eq_zero_of_le {R : ℝ} (hR : 0 < R) {x : Fin d → ℝ} (hx : 2 * R ≤ ‖x‖) :
    dlCutoff d R x = 0 := by
  have : R⁻¹ • x ∉ Function.support (dlCutoffBump d) := by
    rw [ContDiffBump.support_eq, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hR.le), not_lt]
    change (2 : ℝ) ≤ R⁻¹ * ‖x‖
    rw [le_inv_mul_iff₀ hR]; linarith
  exact Function.notMem_support.1 this

/-- `∇χ_R = 0` for `‖x‖ > 2R` (Verified). -/
theorem grad_dlCutoff_eq_zero_of_gt {R : ℝ} (hR : 0 < R) {x : Fin d → ℝ} (hx : 2 * R < ‖x‖) :
    grad (dlCutoff d R) x = 0 := by
  have h : dlCutoff d R =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact dlCutoff_eq_zero_of_le hR (le_of_lt hy)
  funext i
  simp [grad, partialDeriv, h.fderiv_eq]

/-- **Cut-off error under linear growth (Verified).** There is `D₁ ≥ 0` such that for `R ≥ 1`,
`M ≥ 0` and `‖y‖ ≤ M (1 + ‖x‖)`, `|y ⬝ᵥ ∇χ_R(x)| ≤ 3 d M D₁ (1 - χ_{R/2}(x))`: the error is
bounded uniformly in `R` and supported in the tail `‖x‖ ≥ R`. -/
theorem exists_abs_dotProduct_grad_dlCutoff_le_tail (d : ℕ) : ∃ D₁ : ℝ, 0 ≤ D₁ ∧
    ∀ {R : ℝ}, 1 ≤ R → ∀ {Mv : ℝ}, 0 ≤ Mv → ∀ (y x : Fin d → ℝ), ‖y‖ ≤ Mv * (1 + ‖x‖) →
      |y ⬝ᵥ grad (dlCutoff d R) x| ≤ 3 * d * Mv * D₁ * (1 - dlCutoff d (R / 2) x) := by
  obtain ⟨D₁, hD₁0, hD₁⟩ := exists_abs_dotProduct_grad_dlCutoff_le d
  refine ⟨D₁, hD₁0, fun {R} hR {Mv} hMv y x hy => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have h1 : 0 ≤ 1 - dlCutoff d (R / 2) x := sub_nonneg.2 (dlCutoff_le_one _ _)
  by_cases hx1 : ‖x‖ < R
  · rw [grad_dlCutoff_eq_zero_of_lt hR0 hx1, dotProduct_zero, abs_zero]
    positivity
  by_cases hx2 : 2 * R < ‖x‖
  · rw [grad_dlCutoff_eq_zero_of_gt hR0 hx2, dotProduct_zero, abs_zero]
    positivity
  push Not at hx1 hx2
  rw [dlCutoff_eq_zero_of_le (by positivity) (by linarith), sub_zero, mul_one]
  have hy' : ‖y‖ ≤ 3 * Mv * R := by
    refine hy.trans ?_
    nlinarith
  refine (hD₁ hR0 y x hy').trans (le_of_eq ?_)
  field_simp


/-- The **renormalized rate** of `dlBeta` against the cut-off `χ_R` at a slice `f`:
`∫ (β(f) v ⬝ᵥ ∇χ_R + (β(f) - f β'(f)) div v χ_R)`. -/
noncomputable def dlTailRate (v : (Fin d → ℝ) → Fin d → ℝ)
    (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) (R : ℝ) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, (dlBeta (f x) * (v x ⬝ᵥ grad (dlCutoff d R) x) +
    (dlBeta (f x) - f x * deriv dlBeta (f x)) * (weakDiv Dv x * dlCutoff d R x))

/-- Solutions of `WeakContinuityDensity` are weakly continuous on `[0, T]` (Verified). -/
theorem continuousOn_integral_mul_of_weakContinuityDensity {u : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} (h : WeakContinuityDensity u v) {φ : (Fin d → ℝ) → ℝ}
    (hφ : TestFunction2 φ) (T : ℝ) :
    ContinuousOn (fun s => ∫ x, u s x * φ x) (Icc 0 T) := fun s hs =>
  ((h φ hφ s hs.1).continuousWithinAt).mono fun _ hr => hr.1

/-- The cut-offs `χ_R`, `R > 0`, are `C²_c` test functions (Verified). -/
theorem testFunction2_dlCutoff {R : ℝ} (hR : 0 < R) : TestFunction2 (dlCutoff d R) :=
  ⟨(contDiff_dlCutoff R).of_le (by simp), hasCompactSupport_dlCutoff hR⟩

/-- `∫ f χ_R → ∫ f` as `R → ∞` for integrable `f` (Verified). -/
theorem tendsto_integral_mul_dlCutoff {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) :
    Tendsto (fun R => ∫ x, f x * dlCutoff d R x) atTop (𝓝 (∫ x, f x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |f x|)
    (Eventually.of_forall fun R => hf.aestronglyMeasurable.mul
      (contDiff_dlCutoff R).continuous.aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun x => ?_) hf.abs
    (Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dlCutoff_nonneg R x)]
    exact mul_le_of_le_one_right (abs_nonneg _) (dlCutoff_le_one R x)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
    rw [dlCutoff_eq_one (lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR))
      ((le_max_left _ _).trans hR), mul_one]

/-- **Uniqueness from the renormalized identity, tightness version (Verified).** Let `v` be
measurable with linear growth and `|div v| ≤ C` a.e. (for a measurable weak Jacobian `Dv`).
Let `w` be integrable on `t ≥ 0` and satisfy the renormalized identity for `β = dlBeta`
against every cut-off `χ_R`, `R ≥ 1`. Assume `|w_t| ≤ u_t + u'_t` a.e. for two probability
density solutions `u, u'` of `WeakContinuityDensity` with velocity `v`, and `w_0 = 0`. Then
`w_t = 0` a.e. for every `t ≥ 0`.

Proof: `∫ β(w_t) χ_R ≤ C ∫₀ᵗ ∫ β(w_s) χ_R + 3 d M D₁ ∫₀ᵗ τ_R(s) ds` with the tail mass
`τ_R(s) = ∫ (u_s + u'_s)(1 - χ_{R/2})`, which is continuous in `s` and tends to `0` for each
`s` (each `u_s` is a probability density); Gronwall, then `R → ∞` with dominated convergence
in `s` (`0 ≤ τ_R ≤ 2`). -/
theorem ae_eq_zero_of_renormalized_of_tail {w u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hvm : Measurable v) (hDm : Measurable Dv) {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) {C : ℝ} (hC : ∀ᵐ x, |weakDiv Dv x| ≤ C)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t))
    (hren : ∀ R, 1 ≤ R → ∀ t, 0 ≤ t →
      IntervalIntegrable (fun s => dlTailRate v Dv R (w s)) volume 0 t ∧
        (∫ x, dlBeta (w t x) * dlCutoff d R x) - ∫ x, dlBeta (w 0 x) * dlCutoff d R x =
          ∫ s in (0 : ℝ)..t, dlTailRate v Dv R (w s))
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (hwu : ∀ t, 0 ≤ t → ∀ᵐ x, |w t x| ≤ u t x + u' t x)
    (h0 : w 0 =ᵐ[volume] 0) : ∀ t, 0 ≤ t → w t =ᵐ[volume] 0 := by
  intro T hT
  obtain ⟨D₁, hD₁0, hD₁⟩ := exists_abs_dotProduct_grad_dlCutoff_le_tail d
  have hM0 : 0 ≤ Mv := by
    have := (norm_nonneg _).trans (hMv 0)
    simpa using this
  obtain ⟨x0, hx0⟩ := hC.exists
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hx0
  set K0 : ℝ := 3 * d * Mv * D₁ with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hdivm : Measurable (weakDiv Dv) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hDm)
  have hβm : ∀ s, 0 ≤ s → AEStronglyMeasurable (fun x => dlBeta (w s x)) volume := fun s hs =>
    contDiff_dlBeta.continuous.comp_aestronglyMeasurable (hwi s hs).aestronglyMeasurable
  have hβI : ∀ s, 0 ≤ s → Integrable (fun x => dlBeta (w s x)) := fun s hs =>
    (hwi s hs).abs.mono' (hβm s hs) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (dlBeta_nonneg _)]; exact dlBeta_le_abs _)
  have hβχI : ∀ s, 0 ≤ s → ∀ R, Integrable (fun x => dlBeta (w s x) * dlCutoff d R x) :=
    fun s hs R => (hβI s hs).mul_bdd (c := 1) (contDiff_dlCutoff R).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (dlCutoff_nonneg R x)]; exact dlCutoff_le_one R x)
  have hmass : ∀ {f : (Fin d → ℝ) → ℝ}, IsProbDensity f → ∀ R,
      ∫ x, f x * (1 - dlCutoff d R x) = 1 - ∫ x, f x * dlCutoff d R x := by
    intro f hf R
    have hi : Integrable fun x => f x * dlCutoff d R x :=
      hf.1.mul_bdd (c := 1) (contDiff_dlCutoff R).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (dlCutoff_nonneg R x)]; exact dlCutoff_le_one R x)
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hf.1 hi, hf.2.2]
  have hmass_le : ∀ {f : (Fin d → ℝ) → ℝ}, IsProbDensity f → ∀ R,
      ∫ x, f x * dlCutoff d R x ≤ 1 := by
    intro f hf R
    have hi : Integrable fun x => f x * dlCutoff d R x :=
      hf.1.mul_bdd (c := 1) (contDiff_dlCutoff R).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (dlCutoff_nonneg R x)]; exact dlCutoff_le_one R x)
    rw [← hf.2.2]
    refine integral_mono_ae hi hf.1 ?_
    filter_upwards [hf.2.1] with x hx
    exact mul_le_of_le_one_right hx (dlCutoff_le_one R x)
  have hmass_nn : ∀ {f : (Fin d → ℝ) → ℝ}, IsProbDensity f → ∀ R,
      0 ≤ ∫ x, f x * dlCutoff d R x := by
    intro f hf R
    refine integral_nonneg_of_ae ?_
    filter_upwards [hf.2.1] with x hx
    exact mul_nonneg hx (dlCutoff_nonneg R x)
  -- the tail functions
  set τ : ℝ → ℝ → ℝ := fun R s =>
    (1 - ∫ x, u s x * dlCutoff d (R / 2) x) + (1 - ∫ x, u' s x * dlCutoff d (R / 2) x) with hτ
  have hτc : ∀ R, 1 ≤ R → ContinuousOn (τ R) (Icc 0 T) := by
    intro R hR
    have hR2 : 0 < R / 2 := by linarith
    exact (continuousOn_const.sub (continuousOn_integral_mul_of_weakContinuityDensity h
      (testFunction2_dlCutoff hR2) T)).add (continuousOn_const.sub
        (continuousOn_integral_mul_of_weakContinuityDensity h'
          (testFunction2_dlCutoff hR2) T))
  have hτ0 : ∀ R s, 0 ≤ s → 0 ≤ τ R s := fun R s hs => by
    have := hmass_le (hu s hs) (R / 2)
    have := hmass_le (hu' s hs) (R / 2)
    simp only [hτ]; linarith
  have hτ2 : ∀ R s, 0 ≤ s → τ R s ≤ 2 := fun R s hs => by
    have := hmass_nn (hu s hs) (R / 2)
    have := hmass_nn (hu' s hs) (R / 2)
    simp only [hτ]; linarith
  -- the rate bound
  have hGle : ∀ R, 1 ≤ R → ∀ s, 0 ≤ s → dlTailRate v Dv R (w s) ≤
      C * (∫ x, dlBeta (w s x) * dlCutoff d R x) + K0 * τ R s := by
    intro R hR s hs
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    set χ := dlCutoff d R with hχ
    set χ' := dlCutoff d (R / 2) with hχ'
    have hgm : AEStronglyMeasurable (fun x => dlBeta (w s x) * (v x ⬝ᵥ grad χ x) +
        (dlBeta (w s x) - w s x * deriv dlBeta (w s x)) * (weakDiv Dv x * χ x)) volume := by
      refine ((hβm s hs).mul (measurable_dotProduct_grad hvm
        ((contDiff_dlCutoff R).of_le (by simp))).aestronglyMeasurable).add
        (((hβm s hs).sub ((hwi s hs).aestronglyMeasurable.mul
          ((contDiff_dlBeta.continuous_deriv (by simp)).comp_aestronglyMeasurable
            (hwi s hs).aestronglyMeasurable))).mul
          (hdivm.aestronglyMeasurable.mul (contDiff_dlCutoff R).continuous.aestronglyMeasurable))
    have hpt : ∀ᵐ x, dlBeta (w s x) * (v x ⬝ᵥ grad χ x) +
        (dlBeta (w s x) - w s x * deriv dlBeta (w s x)) * (weakDiv Dv x * χ x) ≤
        K0 * ((u s x + u' s x) * (1 - χ' x)) + C * (dlBeta (w s x) * χ x) := by
      filter_upwards [hC, hwu s hs] with x hx hwx
      have hb0 := dlBeta_nonneg (w s x)
      have hb1 := dlBeta_le_abs (w s x)
      have hg := hD₁ hR hM0 (v x) x (hMv x)
      have h1c : 0 ≤ 1 - χ' x := sub_nonneg.2 (dlCutoff_le_one _ _)
      have hχ0 : 0 ≤ χ x := dlCutoff_nonneg R x
      have e1 : dlBeta (w s x) * (v x ⬝ᵥ grad χ x) ≤ K0 * ((u s x + u' s x) * (1 - χ' x)) := by
        calc dlBeta (w s x) * (v x ⬝ᵥ grad χ x) ≤ dlBeta (w s x) * |v x ⬝ᵥ grad χ x| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hb0
          _ ≤ |w s x| * (K0 * (1 - χ' x)) := mul_le_mul hb1 hg (abs_nonneg _) (abs_nonneg _)
          _ ≤ (u s x + u' s x) * (K0 * (1 - χ' x)) :=
              mul_le_mul_of_nonneg_right hwx (by positivity)
          _ = K0 * ((u s x + u' s x) * (1 - χ' x)) := by ring
      have e2 : (dlBeta (w s x) - w s x * deriv dlBeta (w s x)) * (weakDiv Dv x * χ x) ≤
          C * (dlBeta (w s x) * χ x) := by
        calc (dlBeta (w s x) - w s x * deriv dlBeta (w s x)) * (weakDiv Dv x * χ x)
            ≤ |(dlBeta (w s x) - w s x * deriv dlBeta (w s x)) * (weakDiv Dv x * χ x)| :=
              le_abs_self _
          _ = |dlBeta (w s x) - w s x * deriv dlBeta (w s x)| * (|weakDiv Dv x| * χ x) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hχ0]
          _ ≤ dlBeta (w s x) * (C * χ x) :=
              mul_le_mul (abs_dlBeta_sub_mul_deriv_le _)
                (mul_le_mul_of_nonneg_right hx hχ0) (by positivity) hb0
          _ = C * (dlBeta (w s x) * χ x) := by ring
      linarith
    have hI1 : Integrable fun x => dlBeta (w s x) * (v x ⬝ᵥ grad χ x) +
        (dlBeta (w s x) - w s x * deriv dlBeta (w s x)) * (weakDiv Dv x * χ x) := by
      refine ((hwi s hs).abs.const_mul (K0 + C)).mono' hgm ?_
      filter_upwards [hC] with x hx
      have hb0 := dlBeta_nonneg (w s x)
      have hb1 := dlBeta_le_abs (w s x)
      have hg := hD₁ hR hM0 (v x) x (hMv x)
      have h1c : 1 - χ' x ≤ 1 := by linarith [dlCutoff_nonneg (d := d) (R / 2) x]
      have hχ0 : 0 ≤ χ x := dlCutoff_nonneg R x
      have hχ1 : χ x ≤ 1 := dlCutoff_le_one R x
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hχ0]
      have t1 : dlBeta (w s x) * |v x ⬝ᵥ grad χ x| ≤ |w s x| * K0 :=
        mul_le_mul hb1 (hg.trans (by nlinarith)) (abs_nonneg _) (abs_nonneg _)
      have t2 : |dlBeta (w s x) - w s x * deriv dlBeta (w s x)| * (|weakDiv Dv x| * χ x) ≤
          |w s x| * C :=
        mul_le_mul ((abs_dlBeta_sub_mul_deriv_le _).trans hb1)
          ((mul_le_mul hx hχ1 hχ0 hC0).trans (le_of_eq (mul_one C))) (by positivity)
          (abs_nonneg _)
      nlinarith
    have hI2 : Integrable fun x => K0 * ((u s x + u' s x) * (1 - χ' x)) +
        C * (dlBeta (w s x) * χ x) := by
      refine ((((hu s hs).1.add (hu' s hs).1).mul_bdd (c := 1)
        (continuous_const.sub (contDiff_dlCutoff (R / 2)).continuous).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)).const_mul K0).add ((hβχI s hs R).const_mul C)
      show |1 - dlCutoff d (R / 2) x| ≤ 1
      rw [ abs_of_nonneg (sub_nonneg.2 (dlCutoff_le_one _ _))]
      linarith [dlCutoff_nonneg (d := d) (R / 2) x]
    calc dlTailRate v Dv R (w s) ≤ ∫ x, (K0 * ((u s x + u' s x) * (1 - χ' x)) +
          C * (dlBeta (w s x) * χ x)) := integral_mono_ae hI1 hI2 hpt
      _ = C * (∫ x, dlBeta (w s x) * dlCutoff d R x) + K0 * τ R s := by
          have hu1 : Integrable fun x => u s x * (1 - χ' x) :=
            (hu s hs).1.mul_bdd (c := 1)
              (continuous_const.sub (contDiff_dlCutoff (R / 2)).continuous).aestronglyMeasurable
              (Eventually.of_forall fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (dlCutoff_le_one _ _))]
                linarith [dlCutoff_nonneg (d := d) (R / 2) x])
          have hu2 : Integrable fun x => u' s x * (1 - χ' x) :=
            (hu' s hs).1.mul_bdd (c := 1)
              (continuous_const.sub (contDiff_dlCutoff (R / 2)).continuous).aestronglyMeasurable
              (Eventually.of_forall fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (dlCutoff_le_one _ _))]
                linarith [dlCutoff_nonneg (d := d) (R / 2) x])
          have hfun : (fun x => K0 * ((u s x + u' s x) * (1 - χ' x)) +
              C * (dlBeta (w s x) * χ x)) = fun x => (K0 * (u s x * (1 - χ' x)) +
              K0 * (u' s x * (1 - χ' x))) + C * (dlBeta (w s x) * χ x) := by
            funext x; ring
          rw [hfun, integral_add (f := fun x => K0 * (u s x * (1 - χ' x)) +
              K0 * (u' s x * (1 - χ' x))) ((hu1.const_mul K0).add (hu2.const_mul K0))
            ((hβχI s hs R).const_mul C), integral_add (hu1.const_mul K0) (hu2.const_mul K0),
            integral_const_mul, integral_const_mul, integral_const_mul,
            hmass (hu s hs), hmass (hu' s hs)]
          simp only [hτ]
          ring
  -- the Gronwall estimate for each cut-off radius
  have hkey : ∀ R, 1 ≤ R → ∫ x, dlBeta (w T x) * dlCutoff d R x ≤
      K0 * (∫ s in (0 : ℝ)..T, τ R s) * Real.exp (C * T) := by
    intro R hR
    set E : ℝ → ℝ := fun s => ∫ x, dlBeta (w s x) * dlCutoff d R x with hE
    have hE0 : E 0 = 0 := by
      simp only [hE]
      rw [← integral_zero (Fin d → ℝ) ℝ]
      refine integral_congr_ae ?_
      filter_upwards [h0] with x hx
      simp [hx, dlBeta]
    have hEG : ∀ s, 0 ≤ s → E s = ∫ σ in (0 : ℝ)..s, dlTailRate v Dv R (w σ) := by
      intro s hs
      have h2 := (hren R hR s hs).2
      rw [show (∫ x, dlBeta (w 0 x) * dlCutoff d R x) = E 0 from rfl, hE0, sub_zero] at h2
      exact h2
    have hEcont : ContinuousOn E (Icc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval' (hren R hR T hT).1
        (left_mem_uIcc (a := (0 : ℝ)) (b := T))
      rw [uIcc_of_le hT] at this
      exact this.congr fun s hs => hEG s hs.1
    have hE0' : ∀ s ∈ Icc 0 T, 0 ≤ E s := fun s _ =>
      integral_nonneg fun x => mul_nonneg (dlBeta_nonneg _) (dlCutoff_nonneg R x)
    have hτI : ∀ s ∈ Icc 0 T, IntervalIntegrable (τ R) volume 0 s := fun s hs =>
      ((hτc R hR).mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    have hEI : ∀ s ∈ Icc 0 T, IntervalIntegrable E volume 0 s := fun s hs =>
      (hEcont.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    have ha : 0 ≤ K0 * ∫ s in (0 : ℝ)..T, τ R s :=
      mul_nonneg hK00 (intervalIntegral.integral_nonneg hT fun s hs => hτ0 R s hs.1)
    have hgr : ∀ s ∈ Icc 0 T, E s ≤ K0 * (∫ σ in (0 : ℝ)..T, τ R σ) +
        C * ∫ σ in (0 : ℝ)..s, E σ := by
      intro s hs
      rw [hEG s hs.1]
      have hmono : ∫ σ in (0 : ℝ)..s, τ R σ ≤ ∫ σ in (0 : ℝ)..T, τ R σ :=
        intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun σ hσ =>
            hτ0 R σ hσ.1.le)) (hτI T ⟨hT, le_rfl⟩)
      calc ∫ σ in (0 : ℝ)..s, dlTailRate v Dv R (w σ)
          ≤ ∫ σ in (0 : ℝ)..s, (C * E σ + K0 * τ R σ) := by
            refine intervalIntegral.integral_mono_on hs.1
              ((hren R hR s hs.1).1) (((hEI s hs).const_mul C).add ((hτI s hs).const_mul K0))
              fun σ hσ => hGle R hR σ hσ.1
        _ = C * (∫ σ in (0 : ℝ)..s, E σ) + K0 * ∫ σ in (0 : ℝ)..s, τ R σ := by
            rw [intervalIntegral.integral_add ((hEI s hs).const_mul C)
              ((hτI s hs).const_mul K0), intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
        _ ≤ K0 * (∫ σ in (0 : ℝ)..T, τ R σ) + C * ∫ σ in (0 : ℝ)..s, E σ := by
            have := mul_le_mul_of_nonneg_left hmono hK00
            linarith
    have := le_mul_exp_of_le_add_mul_integral ha hC0 hEcont hE0' hgr T ⟨hT, le_rfl⟩
    simpa only [hE] using this
  -- let the cut-off radius tend to infinity
  have hlimE : Tendsto (fun R => ∫ x, dlBeta (w T x) * dlCutoff d R x) atTop
      (𝓝 (∫ x, dlBeta (w T x))) := tendsto_integral_mul_dlCutoff (hβI T hT)
  have hlimτ : Tendsto (fun R => ∫ s in (0 : ℝ)..T, τ R s) atTop (𝓝 0) := by
    have h2 : Tendsto (fun R : ℝ => R / 2) atTop atTop := tendsto_id.atTop_div_const two_pos
    have H := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := T) (l := atTop) (F := τ) (f := fun _ => 0)
      (fun _ => (2 : ℝ)) ?_ ?_ intervalIntegrable_const ?_
    · simpa using H
    · filter_upwards [eventually_ge_atTop 1] with R hR
      refine ((hτc R hR).aestronglyMeasurable measurableSet_Icc).mono_set ?_
      rw [uIoc_of_le hT]; exact Ioc_subset_Icc_self
    · refine Eventually.of_forall fun R => Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hT] at hs
      rw [Real.norm_eq_abs, abs_of_nonneg (hτ0 R s hs.1.le)]
      exact hτ2 R s hs.1.le
    · refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hT] at hs
      have t1 := (tendsto_integral_mul_dlCutoff (hu s hs.1.le).1).comp h2
      have t2 := (tendsto_integral_mul_dlCutoff (hu' s hs.1.le).1).comp h2
      rw [(hu s hs.1.le).2.2] at t1
      rw [(hu' s hs.1.le).2.2] at t2
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub t1).add
        ((tendsto_const_nhds (x := (1 : ℝ))).sub t2)
      simpa using this
  have hbd : Tendsto (fun R => K0 * (∫ s in (0 : ℝ)..T, τ R s) * Real.exp (C * T)) atTop
      (𝓝 0) := by
    simpa using (hlimτ.const_mul K0).mul_const (Real.exp (C * T))
  have hle : ∫ x, dlBeta (w T x) ≤ 0 :=
    le_of_tendsto_of_tendsto hlimE hbd (by
      filter_upwards [eventually_ge_atTop 1] with R hR using hkey R hR)
  have hz : (fun x => dlBeta (w T x)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => dlBeta_nonneg _) (hβI T hT)).1
      (le_antisymm hle (integral_nonneg fun x => dlBeta_nonneg _))
  filter_upwards [hz] with x hx
  exact eq_zero_of_dlBeta_eq_zero hx


/-- `|a ⬝ᵥ b| ≤ ‖a‖ ∑ᵢ |bᵢ|` (Verified). -/
theorem abs_dotProduct_le_norm_mul_sum (a b : Fin d → ℝ) :
    |a ⬝ᵥ b| ≤ ‖a‖ * ∑ i, |b i| := by
  rw [dotProduct, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm a i) (abs_nonneg _)

/-- **The difference of two solutions solves the equation (Verified, linear growth).** For a
measurable velocity of linear growth and solutions with integrable slices, `u - u'` solves
`WeakContinuityDensity` with velocity `v`. -/
theorem WeakContinuityDensity.sub_of_linearGrowth {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} (hvm : Measurable v) {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (hu : ∀ t, 0 ≤ t → Integrable (u t)) (hu' : ∀ t, 0 ≤ t → Integrable (u' t)) :
    WeakContinuityDensity (fun t x => u t x - u' t x) v := by
  intro φ hφ t ht
  obtain ⟨Bφ, hBφ⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
  have hcont : ∀ i, Continuous fun x => grad φ x i := fun i =>
    (hφ.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs : ∀ i, HasCompactSupport fun x => grad φ x i := fun i =>
    (hφ.2.fderiv ℝ).mono' fun x hx => by
      contrapose! hx
      simp [grad, partialDeriv, image_eq_zero_of_notMem_tsupport hx]
  have hgc : Continuous fun x => (1 + ‖x‖) * ∑ i, |grad φ x i| :=
    (continuous_const.add continuous_norm).mul
      (continuous_finsetSum _ fun i _ => (hcont i).abs)
  have hgs : HasCompactSupport fun x => (1 + ‖x‖) * ∑ i, |grad φ x i| := by
    refine HasCompactSupport.mul_left ?_
    refine (HasCompactSupport.of_support_subset_isCompact hφ.2 ?_)
    intro x hx
    by_contra hxs
    apply hx
    simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [grad, partialDeriv, fderiv_of_notMem_tsupport ℝ hxs]
  obtain ⟨B, hB⟩ := hgc.bounded_above_of_compact_support hgs
  have hM0 : 0 ≤ Mv := by
    have := (norm_nonneg _).trans (hMv 0)
    simpa using this
  have hgm : AEStronglyMeasurable (fun x => v x ⬝ᵥ grad φ x) volume :=
    (measurable_dotProduct_grad hvm (hφ.1.of_le (by norm_num))).aestronglyMeasurable
  have hgb : ∀ᵐ x, ‖v x ⬝ᵥ grad φ x‖ ≤ Mv * B := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    refine (abs_dotProduct_le_norm_mul_sum _ _).trans ?_
    have hb := hB x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hb
    calc ‖v x‖ * ∑ i, |grad φ x i| ≤ Mv * (1 + ‖x‖) * ∑ i, |grad φ x i| :=
          mul_le_mul_of_nonneg_right (hMv x) (by positivity)
      _ = Mv * ((1 + ‖x‖) * ∑ i, |grad φ x i|) := by ring
      _ ≤ Mv * B := mul_le_mul_of_nonneg_left hb hM0
  have hi1 : ∀ s, 0 ≤ s → Integrable fun x => u s x * φ x := fun s hs =>
    (hu s hs).mul_bdd hφ.1.continuous.aestronglyMeasurable (Eventually.of_forall hBφ)
  have hi1' : ∀ s, 0 ≤ s → Integrable fun x => u' s x * φ x := fun s hs =>
    (hu' s hs).mul_bdd hφ.1.continuous.aestronglyMeasurable (Eventually.of_forall hBφ)
  have hfun : ∀ s ∈ Ici (0 : ℝ), (∫ x, (u s x - u' s x) * φ x) =
      (∫ x, u s x * φ x) - ∫ x, u' s x * φ x := by
    intro s hs
    simp_rw [sub_mul]
    exact integral_sub (hi1 s hs) (hi1' s hs)
  refine ((h φ hφ t ht).sub (h' φ hφ t ht)).congr hfun (hfun t ht) |>.congr_deriv ?_
  simp_rw [sub_mul]
  exact (integral_sub ((hu t ht).mul_bdd hgm hgb) ((hu' t ht).mul_bdd hgm hgb)).symm

/-- **DiPerna–Lions uniqueness from the commutator hypothesis (Verified).** Let `v` be
measurable, of linear growth, with a measurable weak Jacobian `Dv` and `|div v| ≤ C` a.e.
Let `u, u'` be probability density solutions of `WeakContinuityDensity` with velocity `v` and
`u_0 = u'_0` a.e. If the commutator lemma holds for the differences `u_s - u'_s` (on every
compact set, `L¹` convergence of `C_ε(u_s - u'_s, v) - (u_s - u'_s) div v` to `0` with a bound
uniform in `s > 0` and `ε < ε₀`), then `u_t = u'_t` a.e. for every `t ≥ 0`. No `L^∞` bound on
the densities is assumed. -/
theorem ae_eq_of_weakContinuityDensity_of_commutator {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) (hDm : Measurable Dv) {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) {C : ℝ} (hC : ∀ᵐ x, |weakDiv Dv x| ≤ C)
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (hcomm : ∀ K : Set (Fin d → ℝ), IsCompact K → ∃ ε₀ > 0, ∃ Bc : ℝ≥0∞, Bc ≠ ⊤ ∧
      ∀ s, 0 < s →
        Tendsto (fun ε => ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε)
          (fun y => u s y - u' s y) v x - (u s x - u' s x) * weakDiv Dv x‖ₑ) (𝓝[>] 0) (𝓝 0) ∧
        ∀ ε ∈ Ioo 0 ε₀, ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε)
          (fun y => u s y - u' s y) v x - (u s x - u' s x) * weakDiv Dv x‖ₑ ≤ Bc)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  set w : ℝ → (Fin d → ℝ) → ℝ := fun t x => u t x - u' t x with hw
  have hwc : WeakContinuityDensity w v :=
    WeakContinuityDensity.sub_of_linearGrowth hvm hMv h h' (fun t ht => (hu t ht).1)
      (fun t ht => (hu' t ht).1)
  have hwi : ∀ t, 0 ≤ t → Integrable (w t) := fun t ht => (hu t ht).1.sub (hu' t ht).1
  have habs : ∀ {f : (Fin d → ℝ) → ℝ}, IsProbDensity f → ∫ x, |f x| = 1 := by
    intro f hf
    rw [← hf.2.2]
    refine integral_congr_ae ?_
    filter_upwards [hf.2.1] with x hx
    exact abs_of_nonneg hx
  have hwM : ∀ t, 0 ≤ t → ∫ x, |w t x| ≤ 2 := by
    intro t ht
    calc ∫ x, |w t x| ≤ ∫ x, (|u t x| + |u' t x|) :=
          integral_mono (hwi t ht).abs ((hu t ht).1.abs.add (hu' t ht).1.abs)
            fun x => abs_sub _ _
      _ = 2 := by
          rw [integral_add (hu t ht).1.abs (hu' t ht).1.abs, habs (hu t ht), habs (hu' t ht)]
          norm_num
  have hwu : ∀ t, 0 ≤ t → ∀ᵐ x, |w t x| ≤ u t x + u' t x := by
    intro t ht
    filter_upwards [(hu t ht).2.1, (hu' t ht).2.1] with x h1 h2
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg h1, abs_of_nonneg h2])
  have hw0 : w 0 =ᵐ[volume] 0 := by
    filter_upwards [h0] with x hx
    simp [hw, hx]
  have hren : ∀ R, 1 ≤ R → ∀ t, 0 ≤ t →
      IntervalIntegrable (fun s => dlTailRate v Dv R (w s)) volume 0 t ∧
        (∫ x, dlBeta (w t x) * dlCutoff d R x) - ∫ x, dlBeta (w 0 x) * dlCutoff d R x =
          ∫ s in (0 : ℝ)..t, dlTailRate v Dv R (w s) := by
    intro R hR t ht
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    obtain ⟨ε₀, hε₀, Bc, hBc, hK⟩ := hcomm _ (hasCompactSupport_dlCutoff (d := d) hR0)
    exact renormalized_identity_of_linearGrowth hv hvm hDm hMv hC hwc hwi hwM contDiff_dlBeta
      abs_dlBeta_le abs_deriv_dlBeta_le (contDiff_dlCutoff R) (hasCompactSupport_dlCutoff hR0)
      hε₀ hBc hK ht
  intro t ht
  have := ae_eq_zero_of_renormalized_of_tail hvm hDm hMv hC hwi hren hu hu' h h' hwu hw0 t ht
  filter_upwards [this] with x hx
  exact sub_eq_zero.1 hx


/-- **Commutator hypothesis for bounded functions (Verified).** For `v ∈ W^{1,1}_loc` with
Borel representatives and compact `K`, there are `ε₀ > 0` and `Bc < ∞` such that every
a.e. strongly measurable `f` with `|f| ≤ U` a.e. satisfies `∫_K |C_ε(f, v) - f div v| → 0`
and `≤ Bc` for `ε < ε₀` (from `Flow/DiPernaLionsCommutatorL1.lean`). -/
theorem exists_commutator_bound_of_ae_bounded {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {K : Set (Fin d → ℝ)} (hK : IsCompact K) (U : ℝ) :
    ∃ ε₀ > 0, ∃ Bc : ℝ≥0∞, Bc ≠ ⊤ ∧ ∀ f : (Fin d → ℝ) → ℝ, AEStronglyMeasurable f volume →
      (∀ᵐ x, |f x| ≤ U) →
        Tendsto (fun ε => ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x -
          f x * weakDiv Dv x‖ₑ) (𝓝[>] 0) (𝓝 0) ∧
        ∀ ε ∈ Ioo 0 ε₀, ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x -
          f x * weakDiv Dv x‖ₑ ≤ Bc := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  obtain ⟨ε₀, hε₀, Bc, hBc, hB⟩ := exists_lintegral_dlCommutator_sub_le
    (hκ.of_le (by simp)) hκ1 hκint hv hvm hDm hK U
  refine ⟨ε₀, hε₀, Bc, hBc, fun f hf hU => ?_⟩
  obtain ⟨W, hWm, hWU, hWf⟩ := exists_measurable_abs_le_ae_eq hf hU
  have heq : ∀ ε, ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x -
      f x * weakDiv Dv x‖ₑ = ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) W v x -
      W x * weakDiv Dv x‖ₑ := by
    intro ε
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hWf] with x hx
    have hc : dlCommutator (scaledKernel (dlMollifier d) ε) f v x =
        dlCommutator (scaledKernel (dlMollifier d) ε) W v x := by
      refine integral_congr_ae ?_
      filter_upwards [hWf] with y hy
      rw [hy]
    rw [hc, hx]
  simp_rw [heq]
  exact ⟨tendsto_lintegral_dlCommutator_sub (hκ.of_le (by simp)) hκ1 hκint hv hvm hDm hWm hWU
    hK, fun ε hε => hB ε hε W hWm hWU⟩

/-- **Good representatives (Verified).** A field `v` with weak Jacobian `Dv`, `|div v| ≤ C`
a.e. and a.e. linear growth has Borel representatives `v' = v`, `Dv' = Dv` a.e. with
`HasWeakJacobian v' Dv'`, linear growth **everywhere** and `|div v'| ≤ max C 0` a.e. -/
theorem exists_measurable_representatives {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hDv : HasWeakJacobian v Dv) {C : ℝ}
    (hC : ∀ᵐ x, |weakDiv Dv x| ≤ C) {Mv : ℝ} (hMv : ∀ᵐ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) :
    ∃ v' : (Fin d → ℝ) → Fin d → ℝ, ∃ Dv' : (Fin d → ℝ) → Fin d → Fin d → ℝ,
      Measurable v' ∧ Measurable Dv' ∧ HasWeakJacobian v' Dv' ∧ (∀ᵐ x, v' x = v x) ∧
      (∀ᵐ x, Dv' x = Dv x) ∧ (∀ x, ‖v' x‖ ≤ max Mv 0 * (1 + ‖x‖)) ∧
      ∀ᵐ x, |weakDiv Dv' x| ≤ max C 0 := by
  have hvae : AEMeasurable v volume :=
    AEMeasurable.of_eval fun j => (hDv j j).1.aestronglyMeasurable.aemeasurable
  have hDae : AEMeasurable Dv volume :=
    AEMeasurable.of_eval fun j => AEMeasurable.of_eval fun i =>
      (hDv j i).2.1.aestronglyMeasurable.aemeasurable
  obtain ⟨v₀, hv₀m, hv₀e⟩ : ∃ v₀ : (Fin d → ℝ) → Fin d → ℝ, Measurable v₀ ∧ v =ᵐ[volume] v₀ :=
    ⟨_, hvae.measurable_mk, hvae.ae_eq_mk⟩
  set v' : (Fin d → ℝ) → Fin d → ℝ :=
    fun x => if ‖v₀ x‖ ≤ Mv * (1 + ‖x‖) then v₀ x else 0 with hv'
  have hv'm : Measurable v' :=
    Measurable.ite (measurableSet_le hv₀m.norm (measurable_const.mul
      (measurable_const.add measurable_norm))) hv₀m measurable_const
  have hv'V : ∀ x, ‖v' x‖ ≤ max Mv 0 * (1 + ‖x‖) := by
    intro x
    simp only [hv']
    split_ifs with hx
    · exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · simp only [norm_zero]; positivity
  have hv'e : ∀ᵐ x, v' x = v x := by
    filter_upwards [hv₀e, hMv] with x h1 h2
    have h3 : ‖v₀ x‖ ≤ Mv * (1 + ‖x‖) := by rw [← h1]; exact h2
    simp only [hv', h3, ↓reduceIte]
    exact h1.symm
  obtain ⟨Dv', hD'm, hD'e⟩ : ∃ Dv' : (Fin d → ℝ) → Fin d → Fin d → ℝ, Measurable Dv' ∧
      ∀ᵐ x, Dv' x = Dv x :=
    ⟨_, hDae.measurable_mk, hDae.ae_eq_mk.mono fun x hx => hx.symm⟩
  have hJ : HasWeakJacobian v' Dv' := by
    intro j i
    obtain ⟨h1, h2, h3⟩ := hDv j i
    refine ⟨h1.congr (hv'e.mono fun x hx => by simp only [hx]),
      h2.congr (hD'e.mono fun x hx => by simp only [hx]), fun φ hφ hφc => ?_⟩
    have e1 : ∫ x, v' x j * partialDeriv i φ x = ∫ x, v x j * partialDeriv i φ x :=
      integral_congr_ae (hv'e.mono fun x hx => by simp only [hx])
    have e2 : ∫ x, Dv' x j i * φ x = ∫ x, Dv x j i * φ x :=
      integral_congr_ae (hD'e.mono fun x hx => by simp only [hx])
    rw [e1, h3 φ hφ hφc, e2]
  have hC' : ∀ᵐ x, |weakDiv Dv' x| ≤ max C 0 := by
    filter_upwards [hC, hD'e] with x h1 h2
    simp only [weakDiv, h2]
    exact h1.trans (le_max_left _ _)
  exact ⟨v', Dv', hv'm, hD'm, hJ, hv'e, hD'e, hv'V, hC'⟩

/-- `WeakContinuityDensity` only depends on the a.e. class of the velocity (Verified). -/
theorem WeakContinuityDensity.congr_ae_velocity {u : ℝ → (Fin d → ℝ) → ℝ}
    {v v' : (Fin d → ℝ) → Fin d → ℝ} (hvv : ∀ᵐ x, v' x = v x)
    (h : WeakContinuityDensity u v) : WeakContinuityDensity u v' := by
  intro φ hφ t ht
  exact (h φ hφ t ht).congr_deriv (integral_congr_ae (hvv.mono fun x hx => by simp only [hx]))

/-- **DiPerna–Lions uniqueness with linear growth (Verified, any `d`).** Let `v` be in the
DiPerna–Lions class `MemW11locBddDiv v` (`v ∈ W^{1,1}_loc`, `div v ∈ L^∞`) with linear growth
`‖v(x)‖ ≤ M (1 + ‖x‖)` for a.e. `x`. Let `u, u'` be uniformly essentially bounded curves of
probability densities on `t ≥ 0` solving `WeakContinuityDensity` with velocity `v`, with
`u_0 = u'_0` a.e. Then `u_t = u'_t` a.e. for every `t ≥ 0`; for essentially bounded `v` this
is `ae_eq_of_weakContinuityDensity_diPernaLions`. -/
theorem ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth
    {u u' : ℝ → (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} (hv : MemW11locBddDiv v)
    {Mv : ℝ} (hMv : ∀ᵐ x, ‖v x‖ ≤ Mv * (1 + ‖x‖))
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    {U : ℝ} (hU : ∀ t, 0 ≤ t → ∀ᵐ x, |u t x| ≤ U) (hU' : ∀ t, 0 ≤ t → ∀ᵐ x, |u' t x| ≤ U)
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  obtain ⟨Dv, hDv, C, hC⟩ := hv
  obtain ⟨v', Dv', hv'm, hD'm, hJ, hv'e, -, hv'V, hC'⟩ :=
    exists_measurable_representatives hDv hC hMv
  refine ae_eq_of_weakContinuityDensity_of_commutator hJ hv'm hD'm hv'V hC' hu hu'
    (h.congr_ae_velocity hv'e) (h'.congr_ae_velocity hv'e) (fun K hK => ?_) h0
  obtain ⟨ε₀, hε₀, Bc, hBc, hB⟩ := exists_commutator_bound_of_ae_bounded hJ hv'm hD'm hK (2 * U)
  refine ⟨ε₀, hε₀, Bc, hBc, fun s hs => hB _ ?_ ?_⟩
  · exact ((hu s hs.le).1.sub (hu' s hs.le).1).aestronglyMeasurable
  · filter_upwards [hU s hs.le, hU' s hs.le] with x h1 h2
    refine (abs_sub _ _).trans ?_
    linarith

/-- **DiPerna–Lions uniqueness in every dimension, bounded version (Verified).** Let
`v : ℝᵈ → ℝᵈ` be in the DiPerna–Lions class `MemW11locBddDiv v` (`v ∈ W^{1,1}_loc` with
essentially bounded weak divergence) and essentially bounded, `‖v x‖ ≤ V` a.e. Let `u, u'`
be curves of probability densities on `t ≥ 0` that are uniformly essentially bounded
(`|u_t|, |u'_t| ≤ U` a.e.) and solve `WeakContinuityDensity` with velocity `v`, with
`u_0 = u'_0` a.e. Then `u_t = u'_t` a.e. for every `t ≥ 0`. No Lipschitz bound on `v` is
assumed: `Dv` is only locally integrable. The case `Mv = max V 0` of
`ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth`. -/
theorem ae_eq_of_weakContinuityDensity_diPernaLions {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} (hv : MemW11locBddDiv v) {V : ℝ} (hV : ∀ᵐ x, ‖v x‖ ≤ V)
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    {U : ℝ} (hU : ∀ t, 0 ≤ t → ∀ᵐ x, |u t x| ≤ U) (hU' : ∀ t, 0 ≤ t → ∀ᵐ x, |u' t x| ≤ U)
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t :=
  ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth hv (Mv := max V 0)
    (hV.mono fun x hx => by nlinarith [norm_nonneg x, le_max_left V 0, le_max_right V 0])
    hu hu' hU hU' h h' h0

end NoiseScore
end FormalizeSampling
