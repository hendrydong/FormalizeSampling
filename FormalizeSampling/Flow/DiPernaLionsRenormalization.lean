module

public import FormalizeSampling.Flow.DiPernaLionsCommutatorL1
public import FormalizeSampling.Flow.DiPernaLionsUniqueness

/-!
# Renormalization for the continuity equation with a `W^{1,1}_loc` velocity

Status: **Verified.** This file carries out the renormalization step of the DiPerna–Lions
argument for `β(s) = s²`, for a **bounded** velocity `v ∈ W^{1,1}_loc(ℝᵈ; ℝᵈ)` (any `d`, no
bound on the weak Jacobian and none on `div v`). For a solution `w` of the linear continuity
equation `WeakContinuityDensity w v` with `w_t ∈ L¹ ∩ L^∞` uniformly in `t`, it proves the
weak renormalized equation in integrated form

  `∫ w_t² χ - ∫ w_0² χ = ∫_0^t ∫ w_s² (v ⬝ ∇χ - div v · χ) dx ds`   (`χ ∈ C_c^∞`),

the classical energy form of the renormalized equation. (The uniqueness theorems use the
bounded renormalization of `Flow/DiPernaLionsRenormalizationBeta.lean` instead.)

## Method

With `κ_ε = scaledKernel (dlMollifier d) ε` and `w_ε = κ_ε ⋆ w`:
1. `t ↦ ∫ w_ε(t)² χ` is differentiable for `t > 0` (differentiation under the integral,
   `hasDerivWithinAt_convolution_of_weakContinuityDensity`, bound `abs_mollDivFlux_le`) and
   continuous on `[0, ∞)`; FTC gives `integral_sq_convolution_sub_eq_integral_deriv`.
2. The derivative equals `∫ w_ε² (div v χ + v ⬝ ∇χ) - 2 ∫ w_ε C_ε χ`
   (`hasDerivAt_integral_sq_convolution`), using `dlCommutator_eq` and the integration by
   parts identity `integral_two_mul_fderiv_apply_mul_eq` against the weak Jacobian.
3. As `ε → 0⁺`, `C_ε(w_s) → w_s div v` in `L¹_loc` with a uniform bound
   (`Flow/DiPernaLionsCommutatorL1.lean`), and `w_ε → w` a.e.; so the rate converges to
   `∫ w_s² (v ⬝ ∇χ - div v χ)` and is uniformly bounded (`dlEnergyRate_spec`); dominated
   convergence in `s` gives `energy_identity_of_weakContinuityDensity`.

## Main results

* `integral_two_mul_fderiv_apply_mul_eq`: `∫ 2 f Df(v) χ = -∫ f² (div v χ + v ⬝ ∇χ)`.
* `hasDerivAt_integral_sq_convolution`, `integral_sq_convolution_sub_eq_integral_deriv`.
* `dlMollifier`, `dlEnergyRate`, `dlEnergyRate_spec`.
* `energy_identity_of_weakContinuityDensity`: the renormalized energy identity.

## Not proved here

* Renormalization for general `β ∈ C¹` (only `β(s) = s²` is treated here, which suffices for
  uniqueness of `L¹ ∩ L^∞` solutions), and for unbounded `w`. Smooth `β` with `β, β'` bounded
  and `w ∈ L^∞_t L¹_x` are treated in `Flow/DiPernaLionsRenormalizationBeta.lean`.
* Unbounded velocities (e.g. linear growth `‖v x‖ ≤ M (1 + ‖x‖)`): here the boundedness
  `‖v‖ ≤ V` is used to dominate the time derivative of `∫ (κ_ε ⋆ w_t)² χ`. The linear-growth
  version (with bounded `β`) is `renormalized_identity_of_linearGrowth`
  (`Flow/DiPernaLionsRenormalizationBeta.lean`).
* Time-dependent velocities.
* Uniqueness is not derived from this identity: the DiPerna–Lions uniqueness theorems
  (`Flow/DiPernaLionsLinearGrowth.lean`) use `renormalized_identity_of_linearGrowth`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **Integration by parts against a `W^{1,1}_loc` field.** For smooth `f` and a smooth
compactly supported cut-off `χ`, `∫ 2 f (Df · v) χ = -∫ f² (div v · χ + v ⬝ ∇χ)`, with
`div v` the weak divergence. -/
theorem integral_two_mul_fderiv_apply_mul_eq {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv)
    {f χ : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∫ x, 2 * f x * fderiv ℝ f x (v x) * χ x =
      -∫ x, f x ^ 2 * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) := by
  set ψ : (Fin d → ℝ) → ℝ := fun x => f x ^ 2 * χ x with hψ
  have hψs : ContDiff ℝ ∞ ψ := (hf.pow 2).mul hχ
  have hψc : HasCompactSupport ψ := hχc.mul_left
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hχ1 : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hpd : ∀ j x, partialDeriv j ψ x =
      2 * f x * partialDeriv j f x * χ x + f x ^ 2 * partialDeriv j χ x := by
    intro j x
    have h1 : HasFDerivAt (fun y => f y ^ 2 * χ y) _ x :=
      (((hf1 x).hasFDerivAt.pow 2).mul (hχ1 x).hasFDerivAt)
    rw [partialDeriv, show ψ = fun x => f x ^ 2 * χ x from rfl, h1.fderiv]
    simp [partialDeriv]
    ring
  -- continuity / compact support of the partial derivatives involved
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
  have hint3 : ∀ j, Integrable fun x => v x j * (f x ^ 2 * partialDeriv j χ x) := fun j => by
    have hc : Continuous fun x => f x ^ 2 * partialDeriv j χ x :=
      (hf.continuous.pow 2).mul (hcont χ hχ j)
    simpa [smul_eq_mul, mul_comm] using
      (hLI j).integrable_smul_left_of_hasCompactSupport hc (hcs χ hχc j).mul_left
  have hsum := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => (hv j j).2.2 ψ hψs hψc
  rw [← integral_finsetSum _ fun j _ => hint1 j, Finset.sum_neg_distrib,
    ← integral_finsetSum _ fun j _ => hint2 j] at hsum
  have hA : ∀ x, ∑ j, v x j * partialDeriv j ψ x =
      2 * f x * fderiv ℝ f x (v x) * χ x + f x ^ 2 * (v x ⬝ᵥ grad χ x) := by
    intro x
    simp_rw [hpd]
    rw [fderiv_apply_eq_grad_dotProduct f x (v x), dotProduct, dotProduct,
      Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [grad]
    ring
  have hB : ∀ x, ∑ j, Dv x j j * ψ x = weakDiv Dv x * χ x * f x ^ 2 := by
    intro x
    rw [← Finset.sum_mul, weakDiv, hψ]
    ring
  simp_rw [hA, hB] at hsum
  have hint4 : Integrable fun x => f x ^ 2 * (v x ⬝ᵥ grad χ x) := by
    have : (fun x => f x ^ 2 * (v x ⬝ᵥ grad χ x)) =
        fun x => ∑ j, v x j * (f x ^ 2 * partialDeriv j χ x) := by
      funext x
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [grad]
      ring
    rw [this]
    exact integrable_finsetSum Finset.univ fun j _ => hint3 j
  have hint5 : Integrable fun x => 2 * f x * fderiv ℝ f x (v x) * χ x := by
    have h := (integrable_finsetSum Finset.univ fun j _ => hint1 j).sub hint4
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hA]
    ring
  have hint6 : Integrable fun x => weakDiv Dv x * χ x * f x ^ 2 := by
    refine (integrable_finsetSum Finset.univ fun j _ => hint2 j).congr
      (Eventually.of_forall fun x => ?_)
    simp only
    rw [hB]
  rw [integral_add hint5 hint4] at hsum
  have e : ∫ x, f x ^ 2 * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) =
      (∫ x, weakDiv Dv x * χ x * f x ^ 2) + ∫ x, f x ^ 2 * (v x ⬝ᵥ grad χ x) := by
    rw [← integral_add hint6 hint4]
    congr 1; funext x; ring
  rw [e]
  linarith

/-- **Bounded measurable representatives (Verified).** An a.e. strongly measurable function
with `|f| ≤ U` a.e. agrees a.e. with a Borel measurable function bounded by `U` everywhere. -/
theorem exists_measurable_abs_le_ae_eq {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f volume) {U : ℝ} (hU : ∀ᵐ x, |f x| ≤ U) :
    ∃ g : (Fin d → ℝ) → ℝ, Measurable g ∧ (∀ x, |g x| ≤ U) ∧ g =ᵐ[volume] f := by
  obtain ⟨x0, hx0⟩ := hU.exists
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hx0
  refine ⟨fun x => max (-U) (min U (hf.mk f x)), ?_, fun x => ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min hf.stronglyMeasurable_mk.measurable)
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [hf.ae_eq_mk, hU] with x h1 h2
    rw [← h1]
    rw [abs_le] at h2
    simp [min_eq_right h2.2, max_eq_right h2.1]

/-- **Bound on the mollified flux divergence (Verified).** If `k` is `C¹` with compact
support, `|u| ≤ U` a.e. (`U ≥ 0`) and `‖v‖ ≤ V` everywhere, then
`|(div(u v)) ⋆ k (x)| ≤ U V ∫ ‖Dk‖` for every `x`. -/
theorem abs_mollDivFlux_le {k : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k) {u : (Fin d → ℝ) → ℝ} {U : ℝ} (hU0 : 0 ≤ U)
    (hu : ∀ᵐ y, |u y| ≤ U) {v : (Fin d → ℝ) → Fin d → ℝ} {V : ℝ} (hV : ∀ y, ‖v y‖ ≤ V)
    (x : Fin d → ℝ) : |mollDivFlux k u v x| ≤ U * V * ∫ z, ‖fderiv ℝ k z‖ := by
  have hint : Integrable fun z => ‖fderiv ℝ k z‖ :=
    ((hk.continuous_fderiv one_ne_zero).norm).integrable_of_hasCompactSupport
      (hkc.fderiv ℝ).norm
  have hint' : Integrable fun y => U * V * ‖fderiv ℝ k (x - y)‖ :=
    (hint.comp_sub_left x).const_mul _
  rw [← Real.norm_eq_abs, mollDivFlux]
  refine (norm_integral_le_of_norm_le hint' ?_).trans (le_of_eq ?_)
  · filter_upwards [hu] with y hy
    rw [norm_mul, Real.norm_eq_abs]
    have h1 : ‖fderiv ℝ k (x - y) (v y)‖ ≤ ‖fderiv ℝ k (x - y)‖ * V :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hV y) (norm_nonneg _))
    calc |u y| * ‖fderiv ℝ k (x - y) (v y)‖ ≤ U * (‖fderiv ℝ k (x - y)‖ * V) :=
          mul_le_mul hy h1 (norm_nonneg _) hU0
      _ = U * V * ‖fderiv ℝ k (x - y)‖ := by ring
  · rw [integral_const_mul, integral_sub_left_eq_self (fun z => ‖fderiv ℝ k z‖) volume x]

/-- **Measurability of a pointwise time derivative (Verified).** If `r ↦ G r x` has derivative
`g x` at `s` for every `x`, and the slices `G s`, `G (s + 1/(n+1))` are a.e. strongly
measurable, then `g` is a.e. strongly measurable (limit of difference quotients). -/
theorem aestronglyMeasurable_of_hasDerivAt {G : ℝ → (Fin d → ℝ) → ℝ}
    {g : (Fin d → ℝ) → ℝ} {s : ℝ}
    (hG : ∀ n : ℕ, AEStronglyMeasurable (G (s + 1 / ((n : ℝ) + 1))) volume)
    (hG0 : AEStronglyMeasurable (G s) volume) (hd : ∀ x, HasDerivAt (fun r => G r x) (g x) s) :
    AEStronglyMeasurable g volume := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n : ℕ => fun x => ((n : ℝ) + 1) * (G (s + 1 / ((n : ℝ) + 1)) x - G s x))
    (fun n => ((hG n).sub hG0).const_mul _) (Eventually.of_forall fun x => ?_)
  have h1 := (hd x).tendsto_slope
  have hseq : Tendsto (fun n : ℕ => s + 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] s) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => ?_)
    · simpa using (tendsto_const_nhds (x := s)).add tendsto_one_div_add_atTop_nhds_zero_nat
    · simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
      positivity
  refine (h1.comp hseq).congr fun n => ?_
  simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
  field_simp

/-- **Integrability of a transport term (Verified).** For `v` with a weak Jacobian (hence
locally integrable components), `f ∈ C¹` and `φ` continuous with compact support,
`x ↦ Df(x) v(x) · φ(x)` is integrable. -/
theorem integrable_fderiv_apply_mul {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv)
    {f φ : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Integrable fun x => fderiv ℝ f x (v x) * φ x := by
  have hc : ∀ j, Continuous fun x => partialDeriv j f x * φ x := fun j =>
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hφ
  have hi : ∀ j, Integrable fun x => v x j * (partialDeriv j f x * φ x) := fun j => by
    simpa [smul_eq_mul, mul_comm] using
      (hv j j).1.integrable_smul_left_of_hasCompactSupport (hc j) hφc.mul_left
  refine (integrable_finsetSum Finset.univ fun j _ => hi j).congr
    (Eventually.of_forall fun x => ?_)
  simp only
  rw [fderiv_apply_eq_grad_dotProduct f x (v x), dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [grad]
  ring

/-- **Time derivative of the mollified `L²` energy (Verified).** Let `w` solve
`WeakContinuityDensity w v` with `w_t` integrable and `|w_t| ≤ U` a.e. for `t ≥ 0`, let `v`
have a weak Jacobian `Dv` and `‖v‖ ≤ V`, let `k ≥ 0` be a smooth compactly supported kernel
with `∫ k = 1`, and let `χ ∈ C_c^∞`. Then at every `s > 0` the energy
`r ↦ ∫ (k ⋆ w_r)² χ` is differentiable with derivative
`∫ (k ⋆ w_s)² (div v χ + v ⬝ ∇χ) - ∫ 2 (k ⋆ w_s) C_k(w_s, v) χ`, and the commutator integrand
is integrable; moreover the derivative is bounded by `2 U (U V ∫ ‖Dk‖) ∫ |χ|`. -/
theorem hasDerivAt_integral_sq_convolution {w : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) {V : ℝ} (hV : ∀ x, ‖v x‖ ≤ V)
    (hw : WeakContinuityDensity w v) (hwi : ∀ t, 0 ≤ t → Integrable (w t)) {U : ℝ}
    (hU : ∀ t, 0 ≤ t → ∀ᵐ x, |w t x| ≤ U) {k : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hk0 : ∀ z, 0 ≤ k z) (hk1 : ∫ z, k z = 1)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (fun r => ∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r) x ^ 2 * χ x)
      ((∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x ^ 2 *
          (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
        ∫ x, 2 * (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x *
          dlCommutator k (w s) v x * χ x) s ∧
      Integrable (fun x => 2 * (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x *
          dlCommutator k (w s) v x * χ x) ∧
      |(∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x ^ 2 *
          (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
        ∫ x, 2 * (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w s) x *
          dlCommutator k (w s) v x * χ x| ≤
        2 * U * (U * V * ∫ z, ‖fderiv ℝ k z‖) * ∫ x, |χ x| := by
  set m : ℝ → (Fin d → ℝ) → ℝ := fun r => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r
    with hm
  obtain ⟨x0, hx0⟩ := (hU 0 le_rfl).exists
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hx0
  have hkI : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hmb : ∀ r, 0 ≤ r → ∀ x, |m r x| ≤ U := fun r hr x =>
    abs_convolution_le_of_ae_bound hk0 hkI hk1 (hU r hr) x
  have hmc : ∀ r, 0 ≤ r → ContDiff ℝ ∞ (m r) := fun r hr =>
    hkc.contDiff_convolution_left _ hk (hwi r hr).locallyIntegrable
  have hder' : ∀ r, 0 < r → ∀ x,
      HasDerivAt (fun q => m q x) (-mollDivFlux k (w r) v x) r := fun r hr x =>
    (hasDerivWithinAt_convolution_of_weakContinuityDensity hw (hk.of_le (by simp)) hkc x
      hr.le).hasDerivAt (Ici_mem_nhds hr)
  set Mk := U * V * ∫ z, ‖fderiv ℝ k z‖ with hMk
  have hMb : ∀ r, 0 ≤ r → ∀ x, |mollDivFlux k (w r) v x| ≤ Mk := fun r hr x =>
    abs_mollDivFlux_le (hk.of_le (by simp)) hkc hU0 (hU r hr) hV x
  have hχI : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hmeasF : AEStronglyMeasurable (fun x => -mollDivFlux k (w s) v x) volume :=
    aestronglyMeasurable_of_hasDerivAt (G := m)
      (fun n => (hmc _ (by positivity)).continuous.aestronglyMeasurable)
      (hmc s hs.le).continuous.aestronglyMeasurable (hder' s hs)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x => m r x ^ 2 * χ x)
    (F' := fun r x => 2 * m r x * (-mollDivFlux k (w r) v x) * χ x)
    (bound := fun x => 2 * U * Mk * |χ x|) (Ioi_mem_nhds hs)
    (Filter.eventually_of_mem (Ioi_mem_nhds hs) fun r hr =>
      (((hmc r (le_of_lt hr)).continuous.pow 2).mul hχ.continuous).aestronglyMeasurable)
    ((((hmc s hs.le).continuous.pow 2).mul hχ.continuous).integrable_of_hasCompactSupport
      hχc.mul_left)
    ((((hmc s hs.le).continuous.aestronglyMeasurable.const_mul 2).mul hmeasF).mul
      hχ.continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x r hr => by
      have h1 := hmb r (le_of_lt hr) x
      have h2 := hMb r (le_of_lt hr) x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul
        (mul_le_mul_of_nonneg_left h1 two_pos.le) h2 (abs_nonneg _)
        (mul_nonneg two_pos.le hU0)) (abs_nonneg _))
    (hχI.abs.const_mul (2 * U * Mk))
    (Eventually.of_forall fun x r hr => by
      have := ((hder' r hr x).pow 2).mul_const (χ x)
      convert this using 1
      norm_num)
  obtain ⟨hF'int, hderF⟩ := key
  have hFbd : |∫ x, 2 * m s x * (-mollDivFlux k (w s) v x) * χ x| ≤
      2 * U * Mk * ∫ x, |χ x| := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hχI.abs.const_mul _) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_left (hmb s hs.le x) two_pos.le) (hMb s hs.le x) (abs_nonneg _)
      (mul_nonneg two_pos.le hU0)) (abs_nonneg _)
  -- the commutator identity at every point
  obtain ⟨Dk, hDk⟩ := (hk.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hkc.fderiv ℝ)
  have hgradc : ∀ i, Continuous fun z => grad k z i := fun i =>
    (hk.continuous_fderiv (by simp)).clm_apply continuous_const
  have hintx : ∀ x, Integrable fun y => w s y * fderiv ℝ k (x - y) (v y) := by
    intro x
    refine (hwi s hs.le).mul_bdd (c := Dk * V) ?_ (Eventually.of_forall fun y => ?_)
    · have : (fun y => fderiv ℝ k (x - y) (v y)) =
          fun y => ∑ i, grad k (x - y) i * v y i := by
        funext y
        rw [fderiv_apply_eq_grad_dotProduct, dotProduct]
      rw [this]
      exact (Finset.measurable_sum Finset.univ fun i _ =>
        ((hgradc i).measurable.comp (measurable_const.sub measurable_id)).mul
          ((measurable_pi_apply i).comp hvm)).aestronglyMeasurable
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul (hDk _) (hV y) (norm_nonneg _) ((norm_nonneg _).trans (hDk 0))
  have hcomm : ∀ x, dlCommutator k (w s) v x =
      mollDivFlux k (w s) v x - fderiv ℝ (m s) x (v x) := fun x =>
    dlCommutator_eq (hwi s hs.le).locallyIntegrable (hk.of_le (by simp)) hkc (hintx x)
  have hT : Integrable fun x => 2 * m s x * fderiv ℝ (m s) x (v x) * χ x := by
    have := integrable_fderiv_apply_mul hv ((hmc s hs.le).of_le (by simp))
      ((continuous_const.mul (hmc s hs.le).continuous).mul hχ.continuous)
      (hχc.mul_left (f := fun x => 2 * m s x))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have hB : Integrable fun x => 2 * m s x * dlCommutator k (w s) v x * χ x := by
    refine (hF'int.neg.sub hT).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, Pi.sub_apply]
    rw [hcomm]
    ring
  have hval : ∫ x, 2 * m s x * (-mollDivFlux k (w s) v x) * χ x =
      -(∫ x, 2 * m s x * fderiv ℝ (m s) x (v x) * χ x) -
        ∫ x, 2 * m s x * dlCommutator k (w s) v x * χ x := by
    have e : ∫ x, 2 * m s x * (-mollDivFlux k (w s) v x) * χ x =
        ∫ x, (-(2 * m s x * fderiv ℝ (m s) x (v x) * χ x) -
          2 * m s x * dlCommutator k (w s) v x * χ x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hcomm]
      ring
    rw [e, integral_sub (f := fun x => -(2 * m s x * fderiv ℝ (m s) x (v x) * χ x)) hT.neg hB,
      integral_neg]
  have e2 := integral_two_mul_fderiv_apply_mul_eq hv (hmc s hs.le) hχ hχc
  refine ⟨?_, hB, ?_⟩
  · rw [hval, e2, neg_neg] at hderF
    exact hderF
  · rw [hval, e2, neg_neg] at hFbd
    exact hFbd

/-- **Fundamental theorem of calculus for the mollified energy (Verified).** Under the
hypotheses of `hasDerivAt_integral_sq_convolution`, for `t ≥ 0`,
`∫ (k ⋆ w_t)² χ - ∫ (k ⋆ w_0)² χ = ∫_0^t (d/ds) ∫ (k ⋆ w_s)² χ ds`. -/
theorem integral_sq_convolution_sub_eq_integral_deriv {w : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) {V : ℝ} (hV : ∀ x, ‖v x‖ ≤ V)
    (hw : WeakContinuityDensity w v) (hwi : ∀ t, 0 ≤ t → Integrable (w t)) {U : ℝ}
    (hU : ∀ t, 0 ≤ t → ∀ᵐ x, |w t x| ≤ U) {k : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hk0 : ∀ z, 0 ≤ k z) (hk1 : ∫ z, k z = 1)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w t) x ^ 2 * χ x) -
        ∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w 0) x ^ 2 * χ x =
      ∫ s in (0 : ℝ)..t,
        deriv (fun r => ∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r) x ^ 2 * χ x) s := by
  set m : ℝ → (Fin d → ℝ) → ℝ := fun r => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r
    with hm
  set F : ℝ → ℝ := fun r => ∫ x, m r x ^ 2 * χ x with hF
  have hE := fun s (hs : 0 < s) =>
    hasDerivAt_integral_sq_convolution hv hvm hV hw hwi hU hk hkc hk0 hk1 hχ hχc hs
  have hkI : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hmb : ∀ r, 0 ≤ r → ∀ x, |m r x| ≤ U := fun r hr x =>
    abs_convolution_le_of_ae_bound hk0 hkI hk1 (hU r hr) x
  have hmc : ∀ r, 0 ≤ r → ContDiff ℝ ∞ (m r) := fun r hr =>
    hkc.contDiff_convolution_left _ hk (hwi r hr).locallyIntegrable
  have hχI : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hcont : ∀ r, 0 ≤ r → ContinuousWithinAt F (Ici 0) r := by
    intro r hr
    refine continuousWithinAt_of_dominated (bound := fun x => U ^ 2 * |χ x|)
      (eventually_nhdsWithin_of_forall fun r' hr' =>
        (((hmc r' hr').continuous.pow 2).mul hχ.continuous).aestronglyMeasurable)
      (eventually_nhdsWithin_of_forall fun r' hr' => Eventually.of_forall fun x => ?_)
      (hχI.abs.const_mul _) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hmb r' hr' x) 2)
        (abs_nonneg _)
    · exact ((hasDerivWithinAt_convolution_of_weakContinuityDensity hw (hk.of_le (by simp))
        hkc x hr).continuousWithinAt.pow 2).mul continuousWithinAt_const
  have hint : IntervalIntegrable (deriv F) volume 0 t := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
      (Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
        (measurable_deriv F).aestronglyMeasurable
        (M := 2 * U * (U * V * ∫ z, ‖fderiv ℝ k z‖) * ∫ x, |χ x|)
        ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun s hs => ?_)))
    rw [(hE s hs.1).1.deriv, Real.norm_eq_abs]
    exact (hE s hs.1).2.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (fun r hr => (hcont r hr.1).mono Icc_subset_Ici_self)
    (fun s hs => (hE s hs.1).1.differentiableAt.hasDerivAt) hint]

/-- The fixed **mollifier profile** used in the renormalization argument: the normalized
smooth bump on `ℝᵈ` centred at `0` with inner radius `1/2` and outer radius `1`. -/
noncomputable def dlMollifier (d : ℕ) : (Fin d → ℝ) → ℝ :=
  (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : Fin d → ℝ)).normed volume

/-- **Properties of `dlMollifier` (Verified).** It is smooth, nonnegative, vanishes outside
the closed unit ball and has integral `1`. -/
theorem dlMollifier_spec :
    ContDiff ℝ ∞ (dlMollifier d) ∧ (∀ z, 0 ≤ dlMollifier d z) ∧
      (∀ z, 1 < ‖z‖ → dlMollifier d z = 0) ∧ ∫ z, dlMollifier d z = 1 := by
  set b : ContDiffBump (0 : Fin d → ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.contDiff_normed, b.nonneg_normed, fun z hz => ?_, b.integral_normed⟩
  have : z ∉ Function.support (b.normed volume) := by
    rw [b.support_normed_eq, mem_ball, dist_zero_right]
    exact fun h => absurd hz (not_lt.2 h.le)
  exact Function.notMem_support.1 this

/-- **Scaled kernels of `dlMollifier` (Verified).** For `ε > 0`, `κ_ε = scaledKernel κ ε` is
smooth, compactly supported, nonnegative and has integral `1`. -/
theorem dlMollifier_scaled_spec {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (scaledKernel (dlMollifier d) ε) ∧
      HasCompactSupport (scaledKernel (dlMollifier d) ε) ∧
      (∀ z, 0 ≤ scaledKernel (dlMollifier d) ε z) ∧ ∫ z, scaledKernel (dlMollifier d) ε z = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_spec (d := d)
  refine ⟨contDiff_scaledKernel h1 ε, hasCompactSupport_scaledKernel h3 hε, fun z => ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le d)) (h2 _)
  · rw [integral_scaledKernel _ hε, h4]

/-- **A weighted `L¹` bound (Verified).** If `|m| ≤ U` and `|χ| ≤ X` everywhere, then
`∫⁻ ‖2 m g χ‖ ≤ 2 U X ∫⁻_{tsupport χ} ‖g‖`. -/
theorem lintegral_enorm_two_mul_mul_le {m g χ : (Fin d → ℝ) → ℝ} {U X : ℝ} (hU0 : 0 ≤ U)
    (hX0 : 0 ≤ X) (hm : ∀ x, |m x| ≤ U) (hχX : ∀ x, |χ x| ≤ X) :
    ∫⁻ x, ‖2 * m x * g x * χ x‖ₑ ≤
      ENNReal.ofReal (2 * U * X) * ∫⁻ x in tsupport χ, ‖g x‖ₑ := by
  rw [← setLIntegral_eq_of_support_subset (s := tsupport χ)]
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc 2 * |m x| * |g x| * |χ x| = (2 * |m x|) * |χ x| * |g x| := by ring
      _ ≤ (2 * U) * X * |g x| := by
          gcongr
          · exact hm x
          · exact hχX x
  · intro x hx
    by_contra h
    apply hx
    simp [image_eq_zero_of_notMem_tsupport h]

/-- **Mollified energies converge (Verified).** For `f` integrable with `|f| ≤ U` a.e. and an
integrable weight `g`, `∫ (κ_ε ⋆ f)² g → ∫ f² g` as `ε → 0⁺`. -/
theorem tendsto_integral_sq_scaledKernel_convolution {f : (Fin d → ℝ) → ℝ}
    (hfi : Integrable f) {U : ℝ} (hU : ∀ᵐ x, |f x| ≤ U) {g : (Fin d → ℝ) → ℝ}
    (hg : Integrable g) :
    Tendsto (fun ε => ∫ x, (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] f) x ^ 2 * g x) (𝓝[>] 0) (𝓝 (∫ x, f x ^ 2 * g x)) := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  refine tendsto_integral_filter_of_dominated_convergence (fun x => U ^ 2 * |g x|)
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => Eventually.of_forall fun x => ?_)
    (hg.abs.const_mul _) ?_
  · obtain ⟨h1, h2, _, _⟩ := dlMollifier_scaled_spec (d := d) hε
    exact (((h2.contDiff_convolution_left _ h1 hfi.locallyIntegrable).continuous.pow 2)
      |>.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  · obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    have hb := abs_convolution_le_of_ae_bound h3
      (h1.continuous.integrable_of_hasCompactSupport h2) h4 hU x
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb 2) (abs_nonneg _)
  · filter_upwards [ae_tendsto_scaledKernel_convolution hκ.continuous hκ1 hκint
      hfi.locallyIntegrable] with x hx
    exact (hx.pow 2).mul_const _

/-- **Integrability of the weights (Verified).** For `v` with weak Jacobian `Dv` and
`χ ∈ C_c^∞`, the functions `div v · χ` and `v ⬝ ∇χ` are integrable. -/
theorem integrable_weakDiv_mul_and_dotProduct_grad {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => weakDiv Dv x * χ x) ∧ Integrable (fun x => v x ⬝ᵥ grad χ x) := by
  constructor
  · have h : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => Dv x i i * χ x) := fun i _ => by
      simpa [smul_eq_mul, mul_comm] using
        (hv i i).2.1.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
    refine (integrable_finsetSum Finset.univ h).congr (Eventually.of_forall fun x => ?_)
    simp [weakDiv, Finset.sum_mul]
  · have hcont : ∀ j, Continuous (partialDeriv j χ) := fun j =>
      (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : ∀ j, HasCompactSupport (partialDeriv j χ) := fun j =>
      (hχc.fderiv ℝ).mono' fun x hx => by
        contrapose! hx
        simp [partialDeriv, image_eq_zero_of_notMem_tsupport hx]
    have h : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => v x j * partialDeriv j χ x) := fun j _ => by
      simpa [smul_eq_mul, mul_comm] using
        (hv j j).1.integrable_smul_left_of_hasCompactSupport (hcont j) (hcs j)
    refine (integrable_finsetSum Finset.univ h).congr (Eventually.of_forall fun x => ?_)
    simp [dotProduct, grad]

/-- The **mollified energy rate** `∫ (κ_ε ⋆ f)² (div v χ + v ⬝ ∇χ) - ∫ 2 (κ_ε ⋆ f) C_ε(f, v) χ`
(with `κ_ε = scaledKernel (dlMollifier d) ε`): the time derivative of `∫ (κ_ε ⋆ w_s)² χ`
when `f = w_s`. -/
noncomputable def dlEnergyRate (v : (Fin d → ℝ) → Fin d → ℝ)
    (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) (χ f : (Fin d → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ x, (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x ^ 2 *
      (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
    ∫ x, 2 * (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x *
      dlCommutator (scaledKernel (dlMollifier d) ε) f v x * χ x

/-- **Limit and uniform bound of the energy rate (Verified).** Let `f` be integrable with
`|f| ≤ U` a.e., `v` measurable with measurable weak Jacobian `Dv`, `χ ∈ C_c^∞` with
`|χ| ≤ X`, and assume the commutator integrands are integrable. Then, as `ε → 0⁺`,
`dlEnergyRate v Dv χ f ε → ∫ f² (v ⬝ ∇χ - div v χ)` (the DiPerna–Lions commutator lemma
turns `-2 ∫ (κ_ε ⋆ f) C_ε χ` into `-2 ∫ f² div v χ`). Moreover, given a uniform commutator
bound `Bc` on `(0, ε₀)` (from `exists_lintegral_dlCommutator_sub_le`), the rate is bounded on
`(0, ε₀)` by an explicit constant independent of `f`. -/
theorem dlEnergyRate_spec {f : (Fin d → ℝ) → ℝ} (hfi : Integrable f) {U : ℝ}
    (hU : ∀ᵐ x, |f x| ≤ U) {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {X : ℝ} (hχX : ∀ x, |χ x| ≤ X)
    (hB : ∀ ε, 0 < ε → Integrable fun x =>
      2 * (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x *
        dlCommutator (scaledKernel (dlMollifier d) ε) f v x * χ x)
    {ε₀ : ℝ} {Bc : ℝ≥0∞} (hBcne : Bc ≠ ⊤)
    (hBc : ∀ ε ∈ Ioo 0 ε₀, ∀ w : (Fin d → ℝ) → ℝ, Measurable w →
      (∀ x, |w x| ≤ U) → ∫⁻ x in tsupport χ,
        ‖dlCommutator (scaledKernel (dlMollifier d) ε) w v x - w x * weakDiv Dv x‖ₑ ≤ Bc) :
    Tendsto (fun ε => dlEnergyRate v Dv χ f ε) (𝓝[>] 0)
        (𝓝 (∫ x, f x ^ 2 * (v x ⬝ᵥ grad χ x - weakDiv Dv x * χ x))) ∧
      ∀ ε ∈ Ioo 0 ε₀, |dlEnergyRate v Dv χ f ε| ≤
        U ^ 2 * (∫ x, |weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x|) +
          (ENNReal.ofReal (2 * U * X) * Bc).toReal +
          2 * U * U * ∫ x, |weakDiv Dv x * χ x| := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  obtain ⟨x0, hx0⟩ := hU.exists
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hx0
  have hX0 : 0 ≤ X := (abs_nonneg _).trans (hχX 0)
  obtain ⟨hdχ, hvχ⟩ := integrable_weakDiv_mul_and_dotProduct_grad hv hχ hχc
  have hφ := hdχ.add hvχ
  have hdivm : Measurable (weakDiv Dv) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hDm)
  obtain ⟨W, hWm, hWU, hWf⟩ := exists_measurable_abs_le_ae_eq hfi.aestronglyMeasurable hU
  set k : ℝ → (Fin d → ℝ) → ℝ := fun ε => scaledKernel (dlMollifier d) ε with hk
  set m : ℝ → (Fin d → ℝ) → ℝ := fun ε => k ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
    with hm
  have hmc : ∀ ε, 0 < ε → Continuous (m ε) ∧ ∀ x, |m ε x| ≤ U := by
    intro ε hε
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    exact ⟨(h2.contDiff_convolution_left _ h1 hfi.locallyIntegrable).continuous,
      fun x => abs_convolution_le_of_ae_bound h3
        (h1.continuous.integrable_of_hasCompactSupport h2) h4 hU x⟩
  have hCW : ∀ ε x, dlCommutator (k ε) f v x = dlCommutator (k ε) W v x := by
    intro ε x
    refine integral_congr_ae ?_
    filter_upwards [hWf] with y hy
    rw [hy]
  set P : ℝ → ℝ := fun ε =>
    ∫ x, 2 * m ε x * (dlCommutator (k ε) W v x - W x * weakDiv Dv x) * χ x with hP
  set Q : ℝ → ℝ := fun ε => ∫ x, 2 * m ε x * (W x * weakDiv Dv x) * χ x with hQ
  set A : ℝ → ℝ := fun ε => ∫ x, m ε x ^ 2 * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) with hA
  have hQi : ∀ ε, 0 < ε → Integrable fun x => 2 * m ε x * (W x * weakDiv Dv x) * χ x := by
    intro ε hε
    have h := hdχ.bdd_mul (f := fun x => 2 * m ε x * W x) (c := 2 * U * U)
      (((hmc ε hε).1.aestronglyMeasurable.const_mul 2).mul hWm.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
        exact mul_le_mul (mul_le_mul_of_nonneg_left ((hmc ε hε).2 x) two_pos.le) (hWU x)
          (abs_nonneg _) (by positivity))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hdecomp : ∀ ε, 0 < ε → dlEnergyRate v Dv χ f ε = A ε - P ε - Q ε := by
    intro ε hε
    have hPi : Integrable fun x =>
        2 * m ε x * (dlCommutator (k ε) W v x - W x * weakDiv Dv x) * χ x := by
      refine ((hB ε hε).sub (hQi ε hε)).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      rw [hCW]
      ring
    have e : ∫ x, 2 * m ε x * dlCommutator (k ε) f v x * χ x = P ε + Q ε := by
      rw [hP, hQ, ← integral_add hPi (hQi ε hε)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hCW]
      ring
    simp only [dlEnergyRate]
    rw [show (∫ x, 2 * (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] f) x * dlCommutator (scaledKernel (dlMollifier d) ε) f v x * χ x) =
        ∫ x, 2 * m ε x * dlCommutator (k ε) f v x * χ x from rfl, e]
    ring
  have hPle : ∀ ε, 0 < ε → ‖P ε‖ₑ ≤ ENNReal.ofReal (2 * U * X) *
      ∫⁻ x in tsupport χ, ‖dlCommutator (k ε) W v x - W x * weakDiv Dv x‖ₑ := fun ε hε =>
    (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_enorm_two_mul_mul_le hU0 hX0 (hmc ε hε).2 hχX)
  have habs_enorm : ∀ r : ℝ, |r| = (‖r‖ₑ).toReal := fun r => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
  constructor
  · -- the limit
    have hAt : Tendsto A (𝓝[>] 0) (𝓝 (∫ x, f x ^ 2 * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x))) :=
      tendsto_integral_sq_scaledKernel_convolution hfi hU hφ
    have hPt : Tendsto P (𝓝[>] 0) (𝓝 0) := by
      have hL := tendsto_lintegral_dlCommutator_sub (hκ.of_le (by simp)) hκ1 hκint hv hvm hDm
        hWm hWU hχc.isCompact
      have hL' := ENNReal.Tendsto.const_mul hL (Or.inr ENNReal.ofReal_ne_top)
        (a := ENNReal.ofReal (2 * U * X))
      rw [mul_zero] at hL'
      have hPe : Tendsto (fun ε => ‖P ε‖ₑ) (𝓝[>] 0) (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL'
          (Eventually.of_forall fun _ => bot_le)
          (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => hPle ε hε)
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hPe
      refine this.congr fun ε => ?_
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [habs_enorm]
    have hQt : Tendsto Q (𝓝[>] 0) (𝓝 (∫ x, 2 * f x * (W x * weakDiv Dv x) * χ x)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun x => 2 * U * U * |weakDiv Dv x * χ x|)
        (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => (hQi ε hε).aestronglyMeasurable)
        (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) =>
          Eventually.of_forall fun x => ?_) (hdχ.abs.const_mul _) ?_
      · rw [Real.norm_eq_abs, show 2 * m ε x * (W x * weakDiv Dv x) * χ x =
          2 * m ε x * W x * (weakDiv Dv x * χ x) by ring, abs_mul, abs_mul, abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left
          ((hmc ε hε).2 x) two_pos.le) (hWU x) (abs_nonneg _) (by positivity)) (abs_nonneg _)
      · filter_upwards [ae_tendsto_scaledKernel_convolution hκ.continuous hκ1 hκint
          hfi.locallyIntegrable] with x hx
        exact ((hx.const_mul 2).mul_const _).mul_const _
    have hlim := (hAt.sub hPt).sub hQt
    rw [sub_zero] at hlim
    have hval : (∫ x, f x ^ 2 * (weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x)) -
        (∫ x, 2 * f x * (W x * weakDiv Dv x) * χ x) =
        ∫ x, f x ^ 2 * (v x ⬝ᵥ grad χ x - weakDiv Dv x * χ x) := by
      have hf2 : ∀ g : (Fin d → ℝ) → ℝ, Integrable g → Integrable fun x => f x ^ 2 * g x :=
        fun g hg => hg.bdd_mul (c := U ^ 2)
          (hfi.aestronglyMeasurable.pow 2) (by
            filter_upwards [hU] with x hx
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
      have h1 : Integrable fun x => 2 * f x * (W x * weakDiv Dv x) * χ x := by
        refine ((hf2 _ hdχ).const_mul 2).congr ?_
        filter_upwards [hWf] with x hx
        rw [hx]
        ring
      rw [← integral_sub (hf2 (fun x => weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x) hφ) h1]
      refine integral_congr_ae ?_
      filter_upwards [hWf] with x hx
      rw [hx]
      ring
    rw [← hval]
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    exact (hdecomp ε hε).symm
  · -- the uniform bound
    intro ε hε
    have hε0 : 0 < ε := hε.1
    rw [hdecomp ε hε0]
    have hAb : |A ε| ≤ U ^ 2 * ∫ x, |weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x| := by
      rw [← Real.norm_eq_abs, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hφ.abs.const_mul _) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) ((hmc ε hε0).2 x) 2) (abs_nonneg _)
    have hPb : |P ε| ≤ (ENNReal.ofReal (2 * U * X) * Bc).toReal := by
      rw [habs_enorm]
      refine ENNReal.toReal_mono ?_ ((hPle ε hε0).trans ?_)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBcne
      · gcongr
        exact hBc ε hε W hWm hWU
    have hQb : |Q ε| ≤ 2 * U * U * ∫ x, |weakDiv Dv x * χ x| := by
      rw [← Real.norm_eq_abs, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hdχ.abs.const_mul _)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, show 2 * m ε x * (W x * weakDiv Dv x) * χ x =
        2 * m ε x * W x * (weakDiv Dv x * χ x) by ring, abs_mul, abs_mul, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left
        ((hmc ε hε0).2 x) two_pos.le) (hWU x) (abs_nonneg _) (by positivity)) (abs_nonneg _)
    calc |A ε - P ε - Q ε| ≤ |A ε| + |P ε| + |Q ε| := by
          have h1 := abs_sub (A ε - P ε) (Q ε)
          have h2 := abs_sub (A ε) (P ε)
          linarith
      _ ≤ _ := by linarith

/-- **Renormalized energy identity for the continuity equation (Verified).** Let
`v : ℝᵈ → ℝᵈ` be measurable and bounded, `‖v‖ ≤ V`, with a measurable weak Jacobian `Dv`
(`v ∈ W^{1,1}_loc`; no bound on `Dv` or on `div v` is needed here). Let `w` solve the linear
equation `WeakContinuityDensity w v` with `w_t` integrable and `|w_t| ≤ U` a.e. for `t ≥ 0`
(e.g. the difference of two bounded density solutions). Then for every `χ ∈ C_c^∞` and
`t ≥ 0`, `s ↦ ∫ w_s² (v ⬝ ∇χ - div v · χ)` is interval integrable on `[0, t]` and

  `∫ w_t² χ - ∫ w_0² χ = ∫_0^t ∫ w_s² (v ⬝ ∇χ - div v · χ) dx ds`,

i.e. `β(w) = w²` solves the renormalized equation `∂ₜ w² + div(w² v) + w² div v = 0` weakly.
Proof: mollify, `w_ε = κ_ε ⋆ w`; differentiate `∫ w_ε² χ` in time; integrate by parts against
`v` (`integral_two_mul_fderiv_apply_mul_eq`); the error is the DiPerna–Lions commutator,
which converges to `w div v` in `L¹_loc` (`tendsto_lintegral_dlCommutator_sub`) with a
uniform bound (`exists_lintegral_dlCommutator_sub_le`); pass to the limit `ε → 0` by
dominated convergence in `x` and then in `s`. -/
theorem energy_identity_of_weakContinuityDensity {w : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) (hDm : Measurable Dv) {V : ℝ}
    (hV : ∀ x, ‖v x‖ ≤ V) (hw : WeakContinuityDensity w v)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t)) {U : ℝ} (hU : ∀ t, 0 ≤ t → ∀ᵐ x, |w t x| ≤ U)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {t : ℝ}
    (ht : 0 ≤ t) :
    IntervalIntegrable
        (fun s => ∫ x, w s x ^ 2 * (v x ⬝ᵥ grad χ x - weakDiv Dv x * χ x)) volume 0 t ∧
      (∫ x, w t x ^ 2 * χ x) - ∫ x, w 0 x ^ 2 * χ x =
        ∫ s in (0 : ℝ)..t, ∫ x, w s x ^ 2 * (v x ⬝ᵥ grad χ x - weakDiv Dv x * χ x) := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  obtain ⟨ε₀, hε₀, Bc, hBcne, hBc⟩ := exists_lintegral_dlCommutator_sub_le
    (hκ.of_le (by simp)) hκ1 hκint hv hvm hDm hχc.isCompact U
  obtain ⟨X, hX⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hχX : ∀ x, |χ x| ≤ X := fun x => by simpa [Real.norm_eq_abs] using hX x
  have hχI : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  set G : ℝ → ℝ := fun s => ∫ x, w s x ^ 2 * (v x ⬝ᵥ grad χ x - weakDiv Dv x * χ x) with hG
  set M : ℝ := U ^ 2 * (∫ x, |weakDiv Dv x * χ x + v x ⬝ᵥ grad χ x|) +
    (ENNReal.ofReal (2 * U * X) * Bc).toReal + 2 * U * U * ∫ x, |weakDiv Dv x * χ x| with hM
  set Fe : ℝ → ℝ → ℝ := fun ε r =>
    ∫ x, (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w r) x ^ 2 *
      χ x with hFe
  have hE : ∀ ε, 0 < ε → ∀ s, 0 < s →
      HasDerivAt (Fe ε) (dlEnergyRate v Dv χ (w s) ε) s ∧
      Integrable (fun x => 2 * (scaledKernel (dlMollifier d) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] w s) x * dlCommutator (scaledKernel (dlMollifier d) ε) (w s) v x * χ x) := by
    intro ε hε s hs
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    have H := hasDerivAt_integral_sq_convolution hv hvm hV hw hwi hU h1 h2 h3 h4 hχ hχc hs
    exact ⟨H.1, H.2.1⟩
  have hspec := fun s (hs : 0 < s) => dlEnergyRate_spec (hwi s hs.le) (hU s hs.le) hv hvm hDm
    hχ hχc hχX (fun ε hε => (hE ε hε s hs).2) hBcne hBc
  have hFTC : ∀ ε, 0 < ε → Fe ε t - Fe ε 0 = ∫ s in (0 : ℝ)..t, deriv (Fe ε) s := by
    intro ε hε
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε
    exact integral_sq_convolution_sub_eq_integral_deriv hv hvm hV hw hwi hU h1 h2 h3 h4 hχ hχc ht
  have hlimL : Tendsto (fun ε => Fe ε t - Fe ε 0) (𝓝[>] 0)
      (𝓝 ((∫ x, w t x ^ 2 * χ x) - ∫ x, w 0 x ^ 2 * χ x)) :=
    (tendsto_integral_sq_scaledKernel_convolution (hwi t ht) (hU t ht) hχI).sub
      (tendsto_integral_sq_scaledKernel_convolution (hwi 0 le_rfl) (hU 0 le_rfl) hχI)
  have hlimS : ∀ s ∈ Ioc 0 t, Tendsto (fun ε => deriv (Fe ε) s) (𝓝[>] 0) (𝓝 (G s)) := by
    intro s hs
    refine (hspec s hs.1).1.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    exact ((hE ε hε s hs.1).1.deriv).symm
  have hlimR : Tendsto (fun ε => ∫ s in (0 : ℝ)..t, deriv (Fe ε) s) (𝓝[>] 0)
      (𝓝 (∫ s in (0 : ℝ)..t, G s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun ε => (measurable_deriv _).aestronglyMeasurable) ?_
      intervalIntegrable_const ?_
    · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      rw [(hE ε hε.1 s hs.1).1.deriv, Real.norm_eq_abs]
      exact (hspec s hs.1).2 ε hε
    · refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      exact hlimS s hs
  have hlimL' : Tendsto (fun ε => ∫ s in (0 : ℝ)..t, deriv (Fe ε) s) (𝓝[>] 0)
      (𝓝 ((∫ x, w t x ^ 2 * χ x) - ∫ x, w 0 x ^ 2 * χ x)) :=
    hlimL.congr' (eventually_nhdsWithin_of_forall fun ε (hε : ε ∈ Ioi 0) => hFTC ε hε)
  have heq := tendsto_nhds_unique hlimL' hlimR
  refine ⟨?_, heq⟩
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 (Integrable.of_bound ?_ M ?_)
  · exact aestronglyMeasurable_of_tendsto_ae (μ := volume.restrict (Ioc 0 t)) (𝓝[>] (0 : ℝ))
      (f := fun ε => deriv (Fe ε))
      (fun ε => (measurable_deriv _).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hlimS))
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    refine le_of_tendsto (hspec s hs.1).1.norm ?_
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    rw [Real.norm_eq_abs]
    exact (hspec s hs.1).2 ε hε

end NoiseScore
end FormalizeSampling
