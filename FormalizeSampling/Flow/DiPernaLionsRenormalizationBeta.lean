module

public import FormalizeSampling.Flow.DiPernaLionsUniquenessGeneral

/-!
# Renormalization with bounded `β` for velocities of linear growth

Status: **Verified.** This file generalizes the renormalization step of
`Flow/DiPernaLionsRenormalization.lean` (which treats `β(s) = s²`, bounded `v` and bounded
solutions) in two directions needed for the full DiPerna–Lions uniqueness theorem:

* the velocity only has **linear growth** `‖v(x)‖ ≤ M (1 + ‖x‖)` (it is used through the local
  bound `‖v(y)‖ ≤ M (2 + ‖x‖)` for `‖x - y‖ ≤ 1`, so the mollified flux is dominated by
  `M (2 + ‖x‖)` times the `L¹` norm of the solution);
* the solution `w` is only assumed to be in `L^∞_t L¹_x`; the renormalization function `β` is
  smooth with `β, β'` bounded, so every term stays integrable without an `L^∞` bound on `w`.

The DiPerna–Lions commutator lemma enters only through an explicit **commutator hypothesis**
(`L¹(tsupport χ)` convergence of `C_ε(w_s, v) - w_s div v` to `0` with a bound uniform in `s`),
which is discharged elsewhere: for bounded `w` by `Flow/DiPernaLionsCommutatorL1.lean`, for
`w ∈ L^p` and `Dv ∈ L^q_loc` (`1/p + 1/q = 1`) by `Flow/DiPernaLionsCommutatorLp.lean`.

## Main results

* `integral_deriv_comp_mul_fderiv_apply_mul_eq`: `∫ β'(f) (Df · v) χ = -∫ β(f)(div v χ + v ⬝ ∇χ)`.
* `hasDerivAt_integral_beta_convolution`, `integral_beta_convolution_sub_eq_integral_deriv`.
* `dlBetaRate`, `dlBetaRate_spec`.
* `renormalized_identity_of_linearGrowth`: the weak renormalized identity
  `∫ β(w_t) χ - ∫ β(w_0) χ = ∫_0^t ∫ (β(w_s) v ⬝ ∇χ + (β(w_s) - w_s β'(w_s)) div v χ)`.

## Not proved here

* Renormalization for unbounded `β` (e.g. `β(s) = s²` with `w ∈ L²`) under linear growth;
  bounded `β` suffices for uniqueness (`Flow/DiPernaLionsLinearGrowth.lean`).
* The commutator lemma itself (it is a hypothesis here, see above), the growth condition
  `v / (1 + |x|) ∈ L¹ + L^∞` (only pointwise linear growth is treated), and time-dependent
  velocities.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **Derivative of a kernel supported in the unit ball (Verified).** If `k` vanishes outside
the closed unit ball, then `Dk(z) = 0` for `‖z‖ > 1`. -/
theorem fderiv_eq_zero_of_one_lt_norm {k : (Fin d → ℝ) → ℝ} (hk1 : ∀ z, 1 < ‖z‖ → k z = 0)
    {z : Fin d → ℝ} (hz : 1 < ‖z‖) : fderiv ℝ k z = 0 := by
  have h : k =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with y hy
    exact hk1 y hy
  rw [h.fderiv_eq]
  simp

/-- **Linear growth near a point (Verified).** If `‖v(x)‖ ≤ M (1 + ‖x‖)` everywhere and
`‖x - y‖ ≤ 1`, then `‖v(y)‖ ≤ M (2 + ‖x‖)`. -/
theorem norm_le_of_linearGrowth_of_dist_le {v : (Fin d → ℝ) → Fin d → ℝ} {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) {x y : Fin d → ℝ} (hxy : ‖x - y‖ ≤ 1) :
    ‖v y‖ ≤ Mv * (2 + ‖x‖) := by
  have hM0 : 0 ≤ Mv := by
    have := (norm_nonneg _).trans (hMv 0)
    simpa using this
  have hy : ‖y‖ ≤ ‖x‖ + 1 := by
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith
  calc ‖v y‖ ≤ Mv * (1 + ‖y‖) := hMv y
    _ ≤ Mv * (2 + ‖x‖) := mul_le_mul_of_nonneg_left (by linarith) hM0

/-- **Kernel applied to a velocity of linear growth (Verified).** If `Dk` vanishes outside the
unit ball and `‖Dk‖ ≤ D`, then `‖Dk(x - y) v(y)‖ ≤ D M (2 + ‖x‖)` for all `x, y`. -/
theorem norm_fderiv_apply_le_of_linearGrowth {k : (Fin d → ℝ) → ℝ}
    (hk1 : ∀ z, 1 < ‖z‖ → fderiv ℝ k z = 0) {Dk : ℝ} (hDk : ∀ z, ‖fderiv ℝ k z‖ ≤ Dk)
    {v : (Fin d → ℝ) → Fin d → ℝ} {Mv : ℝ} (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖))
    (x y : Fin d → ℝ) : ‖fderiv ℝ k (x - y) (v y)‖ ≤ Dk * (Mv * (2 + ‖x‖)) := by
  have hD0 : 0 ≤ Dk := (norm_nonneg _).trans (hDk 0)
  have hM0 : 0 ≤ Mv := by
    have := (norm_nonneg _).trans (hMv 0)
    simpa using this
  by_cases hxy : ‖x - y‖ ≤ 1
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hDk _) (norm_le_of_linearGrowth_of_dist_le hMv hxy) (norm_nonneg _) hD0)
  · rw [hk1 _ (not_le.1 hxy)]
    simp only [_root_.zero_apply, norm_zero]
    positivity

/-- **Mollified flux bound under linear growth (Verified).** With `Dk` vanishing outside the
unit ball, `‖Dk‖ ≤ D` and `‖v(x)‖ ≤ M (1 + ‖x‖)`, for integrable `u`,
`|∫ u(y) Dk(x - y) v(y) dy| ≤ D M (2 + ‖x‖) ∫ |u|`. Only an `L¹` bound on `u` is used. -/
theorem abs_mollDivFlux_le_of_linearGrowth {k : (Fin d → ℝ) → ℝ}
    (hk1 : ∀ z, 1 < ‖z‖ → fderiv ℝ k z = 0) {Dk : ℝ} (hDk : ∀ z, ‖fderiv ℝ k z‖ ≤ Dk)
    {v : (Fin d → ℝ) → Fin d → ℝ} {Mv : ℝ} (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖))
    {u : (Fin d → ℝ) → ℝ} (hu : Integrable u) (x : Fin d → ℝ) :
    |mollDivFlux k u v x| ≤ Dk * (Mv * (2 + ‖x‖)) * ∫ y, |u y| := by
  rw [← Real.norm_eq_abs, mollDivFlux, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hu.abs.const_mul _) (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_fderiv_apply_le_of_linearGrowth hk1 hDk hMv x y)
    (abs_nonneg _)

/-- **Integrability of the mollified flux integrand (Verified).** Under the hypotheses of
`abs_mollDivFlux_le_of_linearGrowth`, with `k ∈ C¹` and `v` measurable,
`y ↦ u(y) Dk(x - y) v(y)` is integrable for every `x`. -/
theorem integrable_mul_fderiv_apply_of_linearGrowth {k : (Fin d → ℝ) → ℝ}
    (hk : ContDiff ℝ 1 k) (hk1 : ∀ z, 1 < ‖z‖ → fderiv ℝ k z = 0) {Dk : ℝ}
    (hDk : ∀ z, ‖fderiv ℝ k z‖ ≤ Dk) {v : (Fin d → ℝ) → Fin d → ℝ} (hvm : Measurable v)
    {Mv : ℝ} (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) {u : (Fin d → ℝ) → ℝ} (hu : Integrable u)
    (x : Fin d → ℝ) : Integrable fun y => u y * fderiv ℝ k (x - y) (v y) := by
  refine hu.mul_bdd (c := Dk * (Mv * (2 + ‖x‖))) ?_
    (Eventually.of_forall fun y => norm_fderiv_apply_le_of_linearGrowth hk1 hDk hMv x y)
  have hgradc : ∀ i, Continuous fun z => fderiv ℝ k z (Pi.single i 1) := fun i =>
    (hk.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have e : (fun y => fderiv ℝ k (x - y) (v y)) =
      fun y => ∑ i, v y i * fderiv ℝ k (x - y) (Pi.single i 1) := by
    funext y
    rw [clm_apply_eq_sum]
  rw [e]
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    ((measurable_pi_apply i).comp hvm).mul
      ((hgradc i).measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable


/-- **Integration by parts for a renormalization (Verified).** For `β ∈ C^∞`, smooth `f`, a
smooth compactly supported `χ` and `v` with weak Jacobian `Dv`,
`∫ β'(f) (Df · v) χ = -∫ β(f) (div v · χ + v ⬝ ∇χ)`. -/
theorem integral_deriv_comp_mul_fderiv_apply_mul_eq {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {f χ : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∫ x, deriv β (f x) * fderiv ℝ f x (v x) * χ x =
      -∫ x, β (f x) * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) := by
  set ψ : (Fin d → ℝ) → ℝ := fun x => β (f x) * χ x with hψ
  have hψs : ContDiff ℝ ∞ ψ := (hβ.comp hf).mul hχ
  have hψc : HasCompactSupport ψ := hχc.mul_left
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hχ1 : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hβ1 : Differentiable ℝ β := hβ.differentiable (by simp)
  have hpd : ∀ j x, partialDeriv j ψ x =
      deriv β (f x) * partialDeriv j f x * χ x + β (f x) * partialDeriv j χ x := by
    intro j x
    have h1 : HasFDerivAt (fun y => β (f y) * χ y) _ x :=
      (((hβ1 (f x)).hasDerivAt.comp_hasFDerivAt x (hf1 x).hasFDerivAt).mul
        (hχ1 x).hasFDerivAt)
    rw [partialDeriv, show ψ = fun x => β (f x) * χ x from rfl, h1.fderiv]
    simp [partialDeriv]
    ring
  have hcont : ∀ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g → ∀ j, Continuous (partialDeriv j g) :=
    fun g hg j => (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : ∀ g : (Fin d → ℝ) → ℝ, HasCompactSupport g → ∀ j,
      HasCompactSupport (partialDeriv j g) := fun g hg j =>
    (hg.fderiv ℝ).mono' fun x hx => by
      contrapose! hx
      simp [partialDeriv, image_eq_zero_of_notMem_tsupport hx]
  have hLI : ∀ j, LocallyIntegrable fun x => v x j := fun j => (hv j j).1
  have hint1 : ∀ j, Integrable fun x => v x j * partialDeriv j ψ x := fun j => by
    simpa [smul_eq_mul, mul_comm] using
      (hLI j).integrable_smul_left_of_hasCompactSupport (hcont ψ hψs j) (hcs ψ hψc j)
  have hint2 : ∀ j, Integrable fun x => Dv x j j * ψ x := fun j => by
    simpa [smul_eq_mul, mul_comm] using
      (hv j j).2.1.integrable_smul_left_of_hasCompactSupport hψs.continuous hψc
  have hint3 : ∀ j, Integrable fun x => v x j * (β (f x) * partialDeriv j χ x) := fun j => by
    have hc : Continuous fun x => β (f x) * partialDeriv j χ x :=
      (hβ.continuous.comp hf.continuous).mul (hcont χ hχ j)
    simpa [smul_eq_mul, mul_comm] using
      (hLI j).integrable_smul_left_of_hasCompactSupport hc (hcs χ hχc j).mul_left
  have hsum := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => (hv j j).2.2 ψ hψs hψc
  rw [← integral_finsetSum _ fun j _ => hint1 j, Finset.sum_neg_distrib,
    ← integral_finsetSum _ fun j _ => hint2 j] at hsum
  have hA : ∀ x, ∑ j, v x j * partialDeriv j ψ x =
      deriv β (f x) * fderiv ℝ f x (v x) * χ x + β (f x) * (v x ⬝ᵥ grad χ x) := by
    intro x
    simp_rw [hpd]
    rw [fderiv_apply_eq_grad_dotProduct f x (v x), dotProduct, dotProduct,
      Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [grad]
    ring
  have hB : ∀ x, ∑ j, Dv x j j * ψ x = weakDiv Dv x * χ x * β (f x) := by
    intro x
    rw [← Finset.sum_mul, weakDiv, hψ]
    ring
  simp_rw [hA, hB] at hsum
  have hint4 : Integrable fun x => β (f x) * (v x ⬝ᵥ grad χ x) := by
    have : (fun x => β (f x) * (v x ⬝ᵥ grad χ x)) =
        fun x => ∑ j, v x j * (β (f x) * partialDeriv j χ x) := by
      funext x
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [grad]
      ring
    rw [this]
    exact integrable_finsetSum Finset.univ fun j _ => hint3 j
  have hint5 : Integrable fun x => deriv β (f x) * fderiv ℝ f x (v x) * χ x := by
    have h := (integrable_finsetSum Finset.univ fun j _ => hint1 j).sub hint4
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hA]
    ring
  have hint6 : Integrable fun x => weakDiv Dv x * χ x * β (f x) := by
    refine (integrable_finsetSum Finset.univ fun j _ => hint2 j).congr
      (Eventually.of_forall fun x => ?_)
    simp only
    rw [hB]
  rw [integral_add hint5 hint4] at hsum
  have e : ∫ x, β (f x) * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) =
      (∫ x, weakDiv Dv x * χ x * β (f x)) + ∫ x, β (f x) * (v x ⬝ᵥ grad χ x) := by
    rw [← integral_add hint6 hint4]
    congr 1; funext x; ring
  rw [e]
  linarith


/-- **Time derivative of the mollified renormalized energy (Verified).** Let `w` solve
`WeakContinuityDensity w v` with `w_t` integrable and `∫ |w_t| ≤ A` (`t ≥ 0`), let `v` have a
weak Jacobian and linear growth `‖v(x)‖ ≤ M (1 + ‖x‖)`, let `β ∈ C^∞` with `|β'| ≤ L`, and let
`k ∈ C_c^∞` with `Dk = 0` outside the unit ball and `‖Dk‖ ≤ D`. Then for `s > 0`,
`r ↦ ∫ β(k ⋆ w_r) χ` has derivative
`∫ β(k ⋆ w_s) (div v χ + v ⬝ ∇χ) - ∫ β'(k ⋆ w_s) C_k(w_s, v) χ` at `s`, the commutator
integrand is integrable, and the derivative is bounded by `L D M A ∫ (2 + ‖x‖) |χ|`. -/
theorem hasDerivAt_integral_beta_convolution {w : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) (hw : WeakContinuityDensity w v)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t)) {A : ℝ} (hA : ∀ t, 0 ≤ t → ∫ x, |w t x| ≤ A)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {L : ℝ} (hL : ∀ r, |deriv β r| ≤ L)
    {k : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hk1 : ∀ z, 1 < ‖z‖ → fderiv ℝ k z = 0) {Dk : ℝ} (hDk : ∀ z, ‖fderiv ℝ k z‖ ≤ Dk)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (fun r => ∫ x, β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r) x) * χ x)
      ((∫ x, β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x) *
          (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
        ∫ x, deriv β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x) *
          dlCommutator k (w s) v x * χ x) s ∧
      Integrable (fun x => deriv β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x) *
          dlCommutator k (w s) v x * χ x) ∧
      |(∫ x, β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x) *
          (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
        ∫ x, deriv β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x) *
          dlCommutator k (w s) v x * χ x| ≤
        L * (Dk * Mv * A) * ∫ x, (2 + ‖x‖) * |χ x| := by
  set m : ℝ → (Fin d → ℝ) → ℝ := fun r => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r
    with hm
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hD0 : 0 ≤ Dk := (norm_nonneg _).trans (hDk 0)
  have hM0 : 0 ≤ Mv := by
    have := (norm_nonneg _).trans (hMv 0)
    simpa using this
  have hA0 : 0 ≤ A := (integral_nonneg fun x => abs_nonneg _).trans (hA 0 le_rfl)
  have hmc : ∀ r, 0 ≤ r → ContDiff ℝ ∞ (m r) := fun r hr =>
    hkc.contDiff_convolution_left _ hk (hwi r hr).locallyIntegrable
  have hder' : ∀ r, 0 < r → ∀ x,
      HasDerivAt (fun q => m q x) (-mollDivFlux k (w r) v x) r := fun r hr x =>
    (hasDerivWithinAt_convolution_of_weakContinuityDensity hw (hk.of_le (by simp)) hkc x
      hr.le).hasDerivAt (Ici_mem_nhds hr)
  have hMb : ∀ r, 0 ≤ r → ∀ x, |mollDivFlux k (w r) v x| ≤ Dk * Mv * A * (2 + ‖x‖) := by
    intro r hr x
    refine (abs_mollDivFlux_le_of_linearGrowth hk1 hDk hMv (hwi r hr) x).trans ?_
    calc Dk * (Mv * (2 + ‖x‖)) * ∫ y, |w r y| ≤ Dk * (Mv * (2 + ‖x‖)) * A :=
          mul_le_mul_of_nonneg_left (hA r hr) (by positivity)
      _ = Dk * Mv * A * (2 + ‖x‖) := by ring
  have hχ2 : Continuous fun x => (2 + ‖x‖) * |χ x| :=
    (continuous_const.add continuous_norm).mul hχ.continuous.abs
  have hχ2I : Integrable fun x => (2 + ‖x‖) * |χ x| :=
    hχ2.integrable_of_hasCompactSupport (hχc.abs.mul_left)
  have hmeasF : AEStronglyMeasurable (fun x => -mollDivFlux k (w s) v x) volume :=
    aestronglyMeasurable_of_hasDerivAt (G := m)
      (fun n => (hmc _ (by positivity)).continuous.aestronglyMeasurable)
      (hmc s hs.le).continuous.aestronglyMeasurable (hder' s hs)
  have hβ1 : Differentiable ℝ β := hβ.differentiable (by simp)
  have hβ'c : Continuous (deriv β) := hβ.continuous_deriv (by simp)
  have hF'bd : ∀ r, 0 < r → ∀ x,
      |deriv β (m r x) * (-mollDivFlux k (w r) v x) * χ x| ≤
        L * (Dk * Mv * A) * ((2 + ‖x‖) * |χ x|) := by
    intro r hr x
    rw [abs_mul, abs_mul, abs_neg]
    calc |deriv β (m r x)| * |mollDivFlux k (w r) v x| * |χ x|
        ≤ L * (Dk * Mv * A * (2 + ‖x‖)) * |χ x| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hL _) (hMb r hr.le x) (abs_nonneg _) hL0)
            (abs_nonneg _)
      _ = L * (Dk * Mv * A) * ((2 + ‖x‖) * |χ x|) := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x => β (m r x) * χ x)
    (F' := fun r x => deriv β (m r x) * (-mollDivFlux k (w r) v x) * χ x)
    (bound := fun x => L * (Dk * Mv * A) * ((2 + ‖x‖) * |χ x|)) (Ioi_mem_nhds hs)
    (Filter.eventually_of_mem (Ioi_mem_nhds hs) fun r hr =>
      ((hβ.continuous.comp (hmc r (le_of_lt hr)).continuous).mul
        hχ.continuous).aestronglyMeasurable)
    (((hβ.continuous.comp (hmc s hs.le).continuous).mul
      hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left)
    (((hβ'c.comp (hmc s hs.le).continuous).aestronglyMeasurable.mul hmeasF).mul
      hχ.continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x r hr => by
      rw [Real.norm_eq_abs]; exact hF'bd r hr x)
    (hχ2I.const_mul _)
    (Eventually.of_forall fun x r hr => by
      have := ((hβ1 (m r x)).hasDerivAt.comp r (hder' r hr x)).mul_const (χ x)
      convert this using 1
      simp only [Function.comp_apply])
  obtain ⟨hF'int, hderF⟩ := key
  have hFbd : |∫ x, deriv β (m s x) * (-mollDivFlux k (w s) v x) * χ x| ≤
      L * (Dk * Mv * A) * ∫ x, (2 + ‖x‖) * |χ x| := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hχ2I.const_mul _) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hF'bd s hs x
  have hcomm : ∀ x, dlCommutator k (w s) v x =
      mollDivFlux k (w s) v x - fderiv ℝ (m s) x (v x) := fun x =>
    dlCommutator_eq (hwi s hs.le).locallyIntegrable (hk.of_le (by simp)) hkc
      (integrable_mul_fderiv_apply_of_linearGrowth (hk.of_le (by simp)) hk1 hDk hvm hMv
        (hwi s hs.le) x)
  have hT : Integrable fun x => deriv β (m s x) * fderiv ℝ (m s) x (v x) * χ x := by
    have := integrable_fderiv_apply_mul hv ((hmc s hs.le).of_le (by simp))
      ((hβ'c.comp (hmc s hs.le).continuous).mul hχ.continuous)
      (hχc.mul_left (f := fun x => deriv β (m s x)))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have hB : Integrable fun x => deriv β (m s x) * dlCommutator k (w s) v x * χ x := by
    refine (hF'int.neg.sub hT).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, Pi.sub_apply]
    rw [hcomm]
    ring
  have hval : ∫ x, deriv β (m s x) * (-mollDivFlux k (w s) v x) * χ x =
      -(∫ x, deriv β (m s x) * fderiv ℝ (m s) x (v x) * χ x) -
        ∫ x, deriv β (m s x) * dlCommutator k (w s) v x * χ x := by
    have e : ∫ x, deriv β (m s x) * (-mollDivFlux k (w s) v x) * χ x =
        ∫ x, (-(deriv β (m s x) * fderiv ℝ (m s) x (v x) * χ x) -
          deriv β (m s x) * dlCommutator k (w s) v x * χ x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hcomm]
      ring
    rw [e, integral_sub (f := fun x => -(deriv β (m s x) * fderiv ℝ (m s) x (v x) * χ x))
      hT.neg hB, integral_neg]
  have e2 := integral_deriv_comp_mul_fderiv_apply_mul_eq hv hβ (hmc s hs.le) hχ hχc
  refine ⟨?_, hB, ?_⟩
  · rw [hval, e2, neg_neg] at hderF
    exact hderF
  · rw [hval, e2, neg_neg] at hFbd
    exact hFbd


/-- **Fundamental theorem of calculus for the mollified renormalized energy (Verified).**
Under the hypotheses of `hasDerivAt_integral_beta_convolution` and `|β| ≤ B₀`, for `t ≥ 0`,
`∫ β(k ⋆ w_t) χ - ∫ β(k ⋆ w_0) χ = ∫_0^t (d/ds) ∫ β(k ⋆ w_s) χ ds`. -/
theorem integral_beta_convolution_sub_eq_integral_deriv {w : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) (hw : WeakContinuityDensity w v)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t)) {A : ℝ} (hA : ∀ t, 0 ≤ t → ∫ x, |w t x| ≤ A)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {B0 : ℝ} (hB0 : ∀ r, |β r| ≤ B0) {L : ℝ}
    (hL : ∀ r, |deriv β r| ≤ L)
    {k : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hk1 : ∀ z, 1 < ‖z‖ → fderiv ℝ k z = 0)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ x, β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w t) x) * χ x) -
        ∫ x, β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w 0) x) * χ x =
      ∫ s in (0 : ℝ)..t, deriv (fun r =>
        ∫ x, β ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r) x) * χ x) s := by
  set m : ℝ → (Fin d → ℝ) → ℝ := fun r => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r
    with hm
  set F : ℝ → ℝ := fun r => ∫ x, β (m r x) * χ x with hF
  obtain ⟨Dk, hDk⟩ := (hk.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hkc.fderiv ℝ)
  have hE := fun s (hs : 0 < s) =>
    hasDerivAt_integral_beta_convolution hv hvm hMv hw hwi hA hβ hL hk hkc hk1 hDk hχ hχc hs
  have hmc : ∀ r, 0 ≤ r → ContDiff ℝ ∞ (m r) := fun r hr =>
    hkc.contDiff_convolution_left _ hk (hwi r hr).locallyIntegrable
  have hχI : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hcont : ∀ r, 0 ≤ r → ContinuousWithinAt F (Ici 0) r := by
    intro r hr
    refine continuousWithinAt_of_dominated (bound := fun x => B0 * |χ x|)
      (eventually_nhdsWithin_of_forall fun r' hr' =>
        ((hβ.continuous.comp (hmc r' hr').continuous).mul hχ.continuous).aestronglyMeasurable)
      (eventually_nhdsWithin_of_forall fun r' hr' => Eventually.of_forall fun x => ?_)
      (hχI.abs.const_mul _) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB0 _) (abs_nonneg _)
    · exact (hβ.continuous.continuousAt.comp_continuousWithinAt
        (hasDerivWithinAt_convolution_of_weakContinuityDensity hw (hk.of_le (by simp))
          hkc x hr).continuousWithinAt).mul continuousWithinAt_const
  have hint : IntervalIntegrable (deriv F) volume 0 t := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
      (Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
        (measurable_deriv F).aestronglyMeasurable
        (M := L * (Dk * Mv * A) * ∫ x, (2 + ‖x‖) * |χ x|)
        ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun s hs => ?_)))
    rw [(hE s hs.1).1.deriv, Real.norm_eq_abs]
    exact (hE s hs.1).2.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (fun r hr => (hcont r hr.1).mono Icc_subset_Ici_self)
    (fun s hs => (hE s hs.1).1.differentiableAt.hasDerivAt) hint]

/-- **A weighted `L¹` bound (Verified).** If `|a| ≤ L` and `|χ| ≤ X` everywhere, then
`∫⁻ ‖a g χ‖ ≤ L X ∫⁻_{tsupport χ} ‖g‖`. -/
theorem lintegral_enorm_mul_mul_le {a g χ : (Fin d → ℝ) → ℝ} {L X : ℝ} (hL0 : 0 ≤ L)
    (hX0 : 0 ≤ X) (ha : ∀ x, |a x| ≤ L) (hχX : ∀ x, |χ x| ≤ X) :
    ∫⁻ x, ‖a x * g x * χ x‖ₑ ≤ ENNReal.ofReal (L * X) * ∫⁻ x in tsupport χ, ‖g x‖ₑ := by
  rw [← setLIntegral_eq_of_support_subset (s := tsupport χ)]
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_mul, abs_mul]
    calc |a x| * |g x| * |χ x| = |a x| * |χ x| * |g x| := by ring
      _ ≤ L * X * |g x| := by
          gcongr
          · exact ha x
          · exact hχX x
  · intro x hx
    by_contra h
    apply hx
    simp [image_eq_zero_of_notMem_tsupport h]

/-- The **mollified renormalized rate**
`∫ β(κ_ε ⋆ f) (div v χ + v ⬝ ∇χ) - ∫ β'(κ_ε ⋆ f) C_ε(f, v) χ`
(`κ_ε = scaledKernel (dlMollifier d) ε`): the time derivative of `∫ β(κ_ε ⋆ w_s) χ` at
`f = w_s`. -/
noncomputable def dlBetaRate (v : (Fin d → ℝ) → Fin d → ℝ)
    (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) (β : ℝ → ℝ) (χ f : (Fin d → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ x, β ((scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) *
      (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
    ∫ x, deriv β ((scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) *
      dlCommutator (scaledKernel (dlMollifier d) ε) f v x * χ x

/-- **Limit and uniform bound of the renormalized rate (Verified).** Let `f` be integrable,
`v` have a measurable weak Jacobian `Dv` with `|div v| ≤ C` a.e., `β ∈ C^∞` with `|β| ≤ B₀` and
`|β'| ≤ L`, and `χ ∈ C_c^∞` with `|χ| ≤ X`. Assume the commutator integrands are integrable
for `ε ∈ (0, 1)` and the **commutator hypothesis** `∫_{tsupport χ} |C_ε(f, v) - f div v| → 0`
with a bound `Bc` on `(0, ε₀)`. Then
`dlBetaRate → ∫ β(f) v ⬝ ∇χ + (β(f) - f β'(f)) div v χ` as `ε → 0⁺`, and the rate is bounded on
`(0, ε₀) ∩ (0, 1)` by `B₀ ∫|div v χ + v ⬝ ∇χ| + L X Bc + L C X ∫ |f|`. -/
theorem dlBetaRate_spec {f : (Fin d → ℝ) → ℝ} (hfi : Integrable f)
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hDm : Measurable Dv) {C : ℝ}
    (hC : ∀ᵐ x, |weakDiv Dv x| ≤ C) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {B0 : ℝ}
    (hB0 : ∀ r, |β r| ≤ B0) {L : ℝ} (hL : ∀ r, |deriv β r| ≤ L)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {X : ℝ} (hχX : ∀ x, |χ x| ≤ X)
    (hB : ∀ ε ∈ Ioo (0 : ℝ) 1, Integrable fun x =>
      deriv β ((scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) *
        dlCommutator (scaledKernel (dlMollifier d) ε) f v x * χ x)
    (hcl : Tendsto (fun ε => ∫⁻ x in tsupport χ,
        ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x - f x * weakDiv Dv x‖ₑ)
      (𝓝[>] 0) (𝓝 0))
    {ε₀ : ℝ} {Bc : ℝ≥0∞} (hBcne : Bc ≠ ⊤)
    (hBc : ∀ ε ∈ Ioo 0 ε₀, ∫⁻ x in tsupport χ,
        ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x - f x * weakDiv Dv x‖ₑ ≤ Bc) :
    Tendsto (fun ε => dlBetaRate v Dv β χ f ε) (𝓝[>] 0)
        (𝓝 (∫ x, (β (f x) * (v x ⬝ᵥ grad χ x) +
          (β (f x) - f x * deriv β (f x)) * (weakDiv Dv x * χ x)))) ∧
      ∀ ε ∈ Ioo 0 ε₀, ε < 1 → |dlBetaRate v Dv β χ f ε| ≤
        B0 * (∫ x, |weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x|) +
          (ENNReal.ofReal (L * X) * Bc).toReal + L * (C * X * ∫ x, |f x|) := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hX0 : 0 ≤ X := (abs_nonneg _).trans (hχX 0)
  obtain ⟨x0, hx0⟩ := hC.exists
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hx0
  obtain ⟨hdχ, hvχ⟩ := integrable_weakDiv_mul_and_dotProduct_grad hv hχ hχc
  have hφ := hdχ.add hvχ
  have hdivm : Measurable (weakDiv Dv) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hDm)
  have hβc : Continuous β := hβ.continuous
  have hβ'c : Continuous (deriv β) := hβ.continuous_deriv (by simp)
  set k : ℝ → (Fin d → ℝ) → ℝ := fun ε => scaledKernel (dlMollifier d) ε with hk
  set m : ℝ → (Fin d → ℝ) → ℝ := fun ε => k ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
    with hm
  have hmc : ∀ ε, 0 < ε → Continuous (m ε) := by
    intro ε hε
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    exact (h2.contDiff_convolution_left _ h1 hfi.locallyIntegrable).continuous
  -- the function `f div v χ`
  have hfd : Integrable fun x => f x * (weakDiv Dv x * χ x) := by
    refine (hfi.mul_bdd (c := C * X) (hdivm.aestronglyMeasurable.mul
      hχ.continuous.aestronglyMeasurable) ?_)
    filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hx (hχX x) (abs_nonneg _) hC0
  have hfdb : ∫ x, |f x * (weakDiv Dv x * χ x)| ≤ C * X * ∫ x, |f x| := by
    rw [← integral_const_mul]
    refine integral_mono_ae hfd.abs (hfi.abs.const_mul _) ?_
    filter_upwards [hC] with x hx
    rw [abs_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hx (hχX x) (abs_nonneg _) hC0)
      (abs_nonneg _)
  set P : ℝ → ℝ := fun ε =>
    ∫ x, deriv β (m ε x) * (dlCommutator (k ε) f v x - f x * weakDiv Dv x) * χ x with hP
  set Q : ℝ → ℝ := fun ε => ∫ x, deriv β (m ε x) * (f x * (weakDiv Dv x * χ x)) with hQ
  set Aε : ℝ → ℝ := fun ε => ∫ x, β (m ε x) * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)
    with hAε
  have hQi : ∀ ε, 0 < ε → Integrable fun x => deriv β (m ε x) * (f x * (weakDiv Dv x * χ x)) :=
    fun ε hε => hfd.bdd_mul (c := L) (hβ'c.comp (hmc ε hε)).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hL _)
  have hdecomp : ∀ ε ∈ Ioo (0 : ℝ) 1, dlBetaRate v Dv β χ f ε = Aε ε - P ε - Q ε := by
    intro ε hε1
    have hε : 0 < ε := hε1.1
    have hPi : Integrable fun x =>
        deriv β (m ε x) * (dlCommutator (k ε) f v x - f x * weakDiv Dv x) * χ x := by
      refine ((hB ε hε1).sub (hQi ε hε)).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      ring
    have e : ∫ x, deriv β (m ε x) * dlCommutator (k ε) f v x * χ x = P ε + Q ε := by
      rw [hP, hQ, ← integral_add hPi (hQi ε hε)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    simp only [dlBetaRate]
    rw [show (∫ x, deriv β ((scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] f) x) * dlCommutator (scaledKernel (dlMollifier d) ε) f v x * χ x) =
        ∫ x, deriv β (m ε x) * dlCommutator (k ε) f v x * χ x from rfl, e]
    ring
  have hPle : ∀ ε, ‖P ε‖ₑ ≤ ENNReal.ofReal (L * X) *
      ∫⁻ x in tsupport χ, ‖dlCommutator (k ε) f v x - f x * weakDiv Dv x‖ₑ := fun ε =>
    (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_enorm_mul_mul_le hL0 hX0 (fun x => hL _) hχX)
  have habs_enorm : ∀ r : ℝ, |r| = (‖r‖ₑ).toReal := fun r => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hconv := ae_tendsto_scaledKernel_convolution hκ.continuous hκ1 hκint
    hfi.locallyIntegrable
  constructor
  · have hAt : Tendsto Aε (𝓝[>] 0)
        (𝓝 (∫ x, β (f x) * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => B0 * |weakDiv Dv x *
          χ x + v x ⬝ᵥ grad χ x|)
        (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) =>
          (hβc.comp (hmc ε hε)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
        (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) =>
          Eventually.of_forall fun x => ?_) (hφ.abs.const_mul _) ?_
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hB0 _) (abs_nonneg _)
      · filter_upwards [hconv] with x hx
        exact ((hβc.tendsto _).comp hx).mul_const _
    have hPt : Tendsto P (𝓝[>] 0) (𝓝 0) := by
      have hL' := ENNReal.Tendsto.const_mul hcl (Or.inr ENNReal.ofReal_ne_top)
        (a := ENNReal.ofReal (L * X))
      rw [mul_zero] at hL'
      have hPe : Tendsto (fun ε => ‖P ε‖ₑ) (𝓝[>] 0) (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL'
          (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hPle)
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hPe
      refine this.congr fun ε => ?_
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [habs_enorm]
    have hQt : Tendsto Q (𝓝[>] 0)
        (𝓝 (∫ x, deriv β (f x) * (f x * (weakDiv Dv x * χ x)))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun x => L * |f x * (weakDiv Dv x * χ x)|)
        (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => (hQi ε hε).aestronglyMeasurable)
        (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) =>
          Eventually.of_forall fun x => ?_) (hfd.abs.const_mul _) ?_
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)
      · filter_upwards [hconv] with x hx
        exact ((hβ'c.tendsto _).comp hx).mul_const _
    have hlim := (hAt.sub hPt).sub hQt
    rw [sub_zero] at hlim
    have hval : (∫ x, β (f x) * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
        (∫ x, deriv β (f x) * (f x * (weakDiv Dv x * χ x))) =
        ∫ x, (β (f x) * (v x ⬝ᵥ grad χ x) +
          (β (f x) - f x * deriv β (f x)) * (weakDiv Dv x * χ x)) := by
      have h1 : Integrable fun x => β (f x) * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) :=
        hφ.bdd_mul (c := B0) (hβc.comp_aestronglyMeasurable hfi.aestronglyMeasurable)
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB0 _)
      have h2 : Integrable fun x => deriv β (f x) * (f x * (weakDiv Dv x * χ x)) :=
        hfd.bdd_mul (c := L) (hβ'c.comp_aestronglyMeasurable hfi.aestronglyMeasurable)
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hL _)
      rw [← integral_sub h1 h2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [← hval]
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact (hdecomp ε hε).symm
  · intro ε hε hε1
    have hε0 : 0 < ε := hε.1
    rw [hdecomp ε ⟨hε0, hε1⟩]
    have hAb : |Aε ε| ≤ B0 * ∫ x, |weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x| := by
      rw [← Real.norm_eq_abs, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hφ.abs.const_mul _) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB0 _) (abs_nonneg _)
    have hPb : |P ε| ≤ (ENNReal.ofReal (L * X) * Bc).toReal := by
      rw [habs_enorm]
      refine ENNReal.toReal_mono ?_ ((hPle ε).trans ?_)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBcne
      · gcongr
        exact hBc ε hε
    have hQb : |Q ε| ≤ L * (C * X * ∫ x, |f x|) := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      calc ∫ x, ‖deriv β (m ε x) * (f x * (weakDiv Dv x * χ x))‖
          ≤ ∫ x, L * |f x * (weakDiv Dv x * χ x)| := by
            refine integral_mono (hQi ε hε0).norm (hfd.abs.const_mul _) fun x => ?_
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)
        _ ≤ L * (C * X * ∫ x, |f x|) := by
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left hfdb hL0
    calc |Aε ε - P ε - Q ε| ≤ |Aε ε| + |P ε| + |Q ε| := by
          have h1 := abs_sub (Aε ε - P ε) (Q ε)
          have h2 := abs_sub (Aε ε) (P ε)
          linarith
      _ ≤ _ := by linarith


/-- **Renormalized identity with a bounded `β`, linear growth (Verified).** Let `v` be
measurable with a measurable weak Jacobian `Dv` (`v ∈ W^{1,1}_loc`), linear growth
`‖v(x)‖ ≤ M (1 + ‖x‖)` and `|div v| ≤ C` a.e. Let `w` solve `WeakContinuityDensity w v` with
`w_t` integrable and `∫ |w_t| ≤ A` for `t ≥ 0` (no `L^∞` bound). Let `β ∈ C^∞` with `|β| ≤ B₀`,
`|β'| ≤ L`, and `χ ∈ C_c^∞`. Assume the **commutator hypothesis**: for `s > 0`,
`∫_{tsupport χ} |C_ε(w_s, v) - w_s div v| → 0` as `ε → 0⁺`, bounded by `Bc` on `(0, ε₀)`
uniformly in `s`. Then for `t ≥ 0` the rate is interval integrable on `[0, t]` and

  `∫ β(w_t) χ - ∫ β(w_0) χ = ∫_0^t ∫ (β(w_s) v ⬝ ∇χ + (β(w_s) - w_s β'(w_s)) div v χ) dx ds`,

the weak form of `∂ₜ β(w) + div(β(w) v) = (β(w) - w β'(w)) div v`. The commutator hypothesis
holds for bounded `w` (`exists_commutator_bound_of_ae_bounded`) and for `w ∈ L^p`,
`Dv ∈ L^q_loc` (`Flow/DiPernaLionsCommutatorLp.lean`). -/
theorem renormalized_identity_of_linearGrowth {w : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) (hDm : Measurable Dv) {Mv : ℝ}
    (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) {C : ℝ} (hC : ∀ᵐ x, |weakDiv Dv x| ≤ C)
    (hw : WeakContinuityDensity w v) (hwi : ∀ t, 0 ≤ t → Integrable (w t)) {A : ℝ}
    (hA : ∀ t, 0 ≤ t → ∫ x, |w t x| ≤ A)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {B0 : ℝ} (hB0 : ∀ r, |β r| ≤ B0) {L : ℝ}
    (hL : ∀ r, |deriv β r| ≤ L)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {Bc : ℝ≥0∞} (hBcne : Bc ≠ ⊤)
    (hcomm : ∀ s, 0 < s →
      Tendsto (fun ε => ∫⁻ x in tsupport χ,
        ‖dlCommutator (scaledKernel (dlMollifier d) ε) (w s) v x - w s x * weakDiv Dv x‖ₑ)
        (𝓝[>] 0) (𝓝 0) ∧
      ∀ ε ∈ Ioo 0 ε₀, ∫⁻ x in tsupport χ,
        ‖dlCommutator (scaledKernel (dlMollifier d) ε) (w s) v x - w s x * weakDiv Dv x‖ₑ ≤ Bc)
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => ∫ x, (β (w s x) * (v x ⬝ᵥ grad χ x) +
        (β (w s x) - w s x * deriv β (w s x)) * (weakDiv Dv x * χ x))) volume 0 t ∧
      (∫ x, β (w t x) * χ x) - ∫ x, β (w 0 x) * χ x =
        ∫ s in (0 : ℝ)..t, ∫ x, (β (w s x) * (v x ⬝ᵥ grad χ x) +
          (β (w s x) - w s x * deriv β (w s x)) * (weakDiv Dv x * χ x)) := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  obtain ⟨X, hX⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hχX : ∀ x, |χ x| ≤ X := fun x => by simpa [Real.norm_eq_abs] using hX x
  have hχI : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  set G : ℝ → ℝ := fun s => ∫ x, (β (w s x) * (v x ⬝ᵥ grad χ x) +
      (β (w s x) - w s x * deriv β (w s x)) * (weakDiv Dv x * χ x)) with hG
  set M : ℝ := B0 * (∫ x, |weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x|) +
    (ENNReal.ofReal (L * X) * Bc).toReal + L * (C * X * A) with hM
  set Fe : ℝ → ℝ → ℝ := fun ε r =>
    ∫ x, β ((scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r) x) *
      χ x with hFe
  have hk1 : ∀ ε, 0 < ε → ε < 1 → ∀ z : Fin d → ℝ, 1 < ‖z‖ →
      fderiv ℝ (scaledKernel (dlMollifier d) ε) z = 0 := fun ε hε hε1 z hz =>
    fderiv_scaledKernel_eq_zero hκ1 hε (hε1.trans hz)
  have hE : ∀ ε, 0 < ε → ε < 1 → ∀ s, 0 < s →
      HasDerivAt (Fe ε) (dlBetaRate v Dv β χ (w s) ε) s ∧
      Integrable (fun x => deriv β ((scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul
        ℝ ℝ, volume] w s) x) * dlCommutator (scaledKernel (dlMollifier d) ε) (w s) v x * χ x) := by
    intro ε hε hε1 s hs
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    obtain ⟨Dk, hDk⟩ := (h1.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (h2.fderiv ℝ)
    have H := hasDerivAt_integral_beta_convolution hv hvm hMv hw hwi hA hβ hL h1 h2
      (hk1 ε hε hε1) hDk hχ hχc hs
    exact ⟨H.1, H.2.1⟩
  have hspec := fun s (hs : 0 < s) => dlBetaRate_spec (hwi s hs.le) hv hDm hC hβ hB0 hL
    hχ hχc hχX (fun ε hε => (hE ε hε.1 hε.2 s hs).2) (hcomm s hs).1 hBcne (hcomm s hs).2
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hX0 : 0 ≤ X := (abs_nonneg _).trans (hχX 0)
  obtain ⟨x0, hx0⟩ := hC.exists
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hx0
  have hbd : ∀ s, 0 < s → ∀ ε ∈ Ioo 0 ε₀, ε < 1 → |dlBetaRate v Dv β χ (w s) ε| ≤ M := by
    intro s hs ε hε hε1
    refine ((hspec s hs).2 ε hε hε1).trans ?_
    have := mul_le_mul_of_nonneg_left (hA s hs.le) (by positivity : 0 ≤ C * X)
    have := mul_le_mul_of_nonneg_left this hL0
    simp only [hM]
    linarith
  have hFTC : ∀ ε, 0 < ε → ε < 1 → Fe ε t - Fe ε 0 = ∫ s in (0 : ℝ)..t, deriv (Fe ε) s := by
    intro ε hε hε1
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    exact integral_beta_convolution_sub_eq_integral_deriv hv hvm hMv hw hwi hA hβ hB0 hL h1 h2
      (hk1 ε hε hε1) hχ hχc ht
  have hlimF : ∀ r, 0 ≤ r → Tendsto (fun ε => Fe ε r) (𝓝[>] 0) (𝓝 (∫ x, β (w r x) * χ x)) := by
    intro r hr
    refine tendsto_integral_filter_of_dominated_convergence (fun x => B0 * |χ x|)
      (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
      (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => Eventually.of_forall fun x => ?_)
      (hχI.abs.const_mul _) ?_
    · obtain ⟨h1, h2, _, _⟩ := dlMollifier_scaled_spec (d := d) hε
      exact (hβ.continuous.comp (h2.contDiff_convolution_left _ h1
        (hwi r hr).locallyIntegrable).continuous).aestronglyMeasurable.mul
        hχ.continuous.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB0 _) (abs_nonneg _)
    · filter_upwards [ae_tendsto_scaledKernel_convolution hκ.continuous hκ1 hκint
        (hwi r hr).locallyIntegrable] with x hx
      exact ((hβ.continuous.tendsto _).comp hx).mul_const _
  have hlimL : Tendsto (fun ε => Fe ε t - Fe ε 0) (𝓝[>] 0)
      (𝓝 ((∫ x, β (w t x) * χ x) - ∫ x, β (w 0 x) * χ x)) :=
    (hlimF t ht).sub (hlimF 0 le_rfl)
  have hlimS : ∀ s ∈ Ioc 0 t, Tendsto (fun ε => deriv (Fe ε) s) (𝓝[>] 0) (𝓝 (G s)) := by
    intro s hs
    refine (hspec s hs.1).1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact ((hE ε hε.1 hε.2 s hs.1).1.deriv).symm
  have hlimR : Tendsto (fun ε => ∫ s in (0 : ℝ)..t, deriv (Fe ε) s) (𝓝[>] 0)
      (𝓝 (∫ s in (0 : ℝ)..t, G s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun ε => (measurable_deriv _).aestronglyMeasurable) ?_
      intervalIntegrable_const ?_
    · filter_upwards [Ioo_mem_nhdsGT hε₀, Ioo_mem_nhdsGT one_pos] with ε hε hε1
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      rw [(hE ε hε.1 hε1.2 s hs.1).1.deriv, Real.norm_eq_abs]
      exact hbd s hs.1 ε hε hε1.2
    · refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      exact hlimS s hs
  have hlimL' : Tendsto (fun ε => ∫ s in (0 : ℝ)..t, deriv (Fe ε) s) (𝓝[>] 0)
      (𝓝 ((∫ x, β (w t x) * χ x) - ∫ x, β (w 0 x) * χ x)) := by
    refine hlimL.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact hFTC ε hε.1 hε.2
  have heq := tendsto_nhds_unique hlimL' hlimR
  refine ⟨?_, heq⟩
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 (Integrable.of_bound ?_ M ?_)
  · exact aestronglyMeasurable_of_tendsto_ae (μ := volume.restrict (Ioc 0 t)) (𝓝[>] (0 : ℝ))
      (f := fun ε => deriv (Fe ε))
      (fun ε => (measurable_deriv _).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hlimS))
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    refine le_of_tendsto (hspec s hs.1).1.norm ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀, Ioo_mem_nhdsGT one_pos] with ε hε hε1
    rw [Real.norm_eq_abs]
    exact hbd s hs.1 ε hε hε1.2

end NoiseScore
end FormalizeSampling
