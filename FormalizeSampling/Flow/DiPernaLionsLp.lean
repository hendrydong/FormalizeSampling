module

public import FormalizeSampling.Flow.DiPernaLionsLinearGrowth
public import FormalizeSampling.Flow.DiPernaLionsCommutatorLp

/-!
# DiPerna–Lions uniqueness for `L^p` densities

Status: **Verified.** Uniqueness of probability-density solutions of the continuity equation
`WeakContinuityDensity u v` in `L^∞_t L^p_x` (`1 < p < ∞`, **no `L^∞` bound**) for velocities
`v ∈ W^{1,q}_loc` with `1/p + 1/q = 1`, `div v ∈ L^∞` and linear growth, in every dimension.

The proof combines the renormalization with the bounded function `β(s) = s² / (1 + s²)`
(`Flow/DiPernaLionsRenormalizationBeta.lean`, which needs only `L¹` bounds on the solution),
the Gronwall/tightness argument of `Flow/DiPernaLionsLinearGrowth.lean`, and the `L^p`–`W^{1,q}`
commutator lemma of `Flow/DiPernaLionsCommutatorLp.lean`, applied to the difference
`w = u - u'`, whose `L^p` norm is controlled by `‖w‖_p^p ≤ 2^{p-1} (‖u‖_p^p + ‖u'‖_p^p)`.

## Main results

* `lintegral_enorm_sub_rpow_le`: `∫ |f - g|^p ≤ 2^{p-1} (∫ |f|^p + ∫ |g|^p)`.
* `ae_eq_of_weakContinuityDensity_diPernaLions_Lp`: **DiPerna–Lions uniqueness for `L^p`
  densities**.

## Not proved here

* Merely `L¹` densities (`p = 1`): the commutator lemma then needs `v ∈ W^{1,∞}_loc`, which is
  the locally Lipschitz case of `Flow/DiPernaLionsUniqueness.lean`; the genuinely
  DiPerna–Lions `L¹` theory (renormalized solutions without an `L^p` bound, `v ∈ W^{1,1}_loc`)
  is not formalized.
* The growth condition `v / (1 + |x|) ∈ L¹ + L^∞` (only a.e. linear growth is treated),
  signed solutions, time-dependent velocities, existence and the Lagrangian flow.
-/

public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **`L^p` norm of a difference (Verified).** For `p ≥ 1` and a.e. strongly measurable
`f, g`, `∫ |f - g|^p ≤ 2^{p-1} (∫ |f|^p + ∫ |g|^p)` (in `ℝ≥0∞`). -/
theorem lintegral_enorm_sub_rpow_le {f g : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f volume) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖f x - g x‖ₑ ^ p ≤ 2 ^ (p - 1) * ((∫⁻ x, ‖f x‖ₑ ^ p) + ∫⁻ x, ‖g x‖ₑ ^ p) := by
  calc ∫⁻ x, ‖f x - g x‖ₑ ^ p ≤ ∫⁻ x, 2 ^ (p - 1) * (‖f x‖ₑ ^ p + ‖g x‖ₑ ^ p) :=
        lintegral_mono fun x => (ENNReal.rpow_le_rpow (enorm_sub_le) (by linarith)).trans
          (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
    _ = 2 ^ (p - 1) * ((∫⁻ x, ‖f x‖ₑ ^ p) + ∫⁻ x, ‖g x‖ₑ ^ p) := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.rpow_eq_top_iff]),
          lintegral_add_left' (hf.enorm.pow_const p)]

/-- **The commutator only depends on the a.e. class of `f` (Verified).** -/
theorem lintegral_dlCommutator_sub_congr_ae {f g : (Fin d → ℝ) → ℝ} (hfg : f =ᵐ[volume] g)
    (κ : (Fin d → ℝ) → ℝ) (v : (Fin d → ℝ) → Fin d → ℝ)
    (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) (K : Set (Fin d → ℝ)) :
    ∫⁻ x in K, ‖dlCommutator κ f v x - f x * weakDiv Dv x‖ₑ =
      ∫⁻ x in K, ‖dlCommutator κ g v x - g x * weakDiv Dv x‖ₑ := by
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hfg] with x hx
  have hc : dlCommutator κ f v x = dlCommutator κ g v x := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with y hy
    rw [hy]
  rw [hc, hx]

/-- **Finiteness of the local `L^q` Jacobian size (Verified).** If every `∂ᵢvⱼ` is in
`L^q(B(0, R))` for every `R`, then `jacLqNorm Dv q K < ∞` for compact `K`. -/
theorem jacLqNorm_ne_top {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} {q : ℝ} (hq : 0 < q)
    (hDq : ∀ j i, ∀ R : ℝ, ∫⁻ x in closedBall 0 R, ‖Dv x j i‖ₑ ^ q ≠ ⊤)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) : jacLqNorm Dv q K ≠ ⊤ := by
  obtain ⟨R, hR⟩ := (hK.isBounded.cthickening (δ := 1)).subset_closedBall 0
  rw [jacLqNorm]
  refine ENNReal.sum_ne_top.2 fun j _ => ENNReal.sum_ne_top.2 fun i _ => ?_
  refine ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top (hDq j i R) ?_)
  exact lintegral_mono_set hR

/-- **DiPerna–Lions uniqueness for `L^p` densities (Verified, any `d`).** Let `1/p + 1/q = 1`
(`1 < p < ∞`). Let `v : ℝᵈ → ℝᵈ` have a weak Jacobian `Dv` with `∂ᵢvⱼ ∈ L^q_loc`
(`v ∈ W^{1,q}_loc`), essentially bounded weak divergence `|div v| ≤ C` a.e. and linear growth
`‖v(x)‖ ≤ M (1 + ‖x‖)` for a.e. `x`. Let `u, u'` be curves of probability densities on `t ≥ 0`
with `∫ |u_t|^p, ∫ |u'_t|^p ≤ P < ∞` (`u, u' ∈ L^∞_t L^p_x`; no `L^∞` bound), solving
`WeakContinuityDensity` with velocity `v`, with `u_0 = u'_0` a.e. Then `u_t = u'_t` a.e. for
every `t ≥ 0`. -/
theorem ae_eq_of_weakContinuityDensity_diPernaLions_Lp {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hDv : HasWeakJacobian v Dv) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hDq : ∀ j i, ∀ R : ℝ, ∫⁻ x in closedBall 0 R, ‖Dv x j i‖ₑ ^ q ≠ ⊤)
    {C : ℝ} (hC : ∀ᵐ x, |weakDiv Dv x| ≤ C) {Mv : ℝ} (hMv : ∀ᵐ x, ‖v x‖ ≤ Mv * (1 + ‖x‖))
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    {P : ℝ≥0∞} (hP : P ≠ ⊤) (hup : ∀ t, 0 ≤ t → ∫⁻ x, ‖u t x‖ₑ ^ p ≤ P)
    (hup' : ∀ t, 0 ≤ t → ∫⁻ x, ‖u' t x‖ₑ ^ p ≤ P)
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  obtain ⟨v', Dv', hv'm, hD'm, hJ, hv'e, hD'e, hv'V, hC'⟩ :=
    exists_measurable_representatives hDv hC hMv
  have hDq' : ∀ j i, ∀ R : ℝ, ∫⁻ x in closedBall 0 R, ‖Dv' x j i‖ₑ ^ q ≠ ⊤ := by
    intro j i R
    have e : ∫⁻ x in closedBall 0 R, ‖Dv' x j i‖ₑ ^ q =
        ∫⁻ x in closedBall 0 R, ‖Dv x j i‖ₑ ^ q :=
      lintegral_congr_ae (ae_restrict_of_ae (hD'e.mono fun x hx => by simp only [hx]))
    rw [e]
    exact hDq j i R
  refine ae_eq_of_weakContinuityDensity_of_commutator hJ hv'm hD'm hv'V hC' hu hu'
    (h.congr_ae_velocity hv'e) (h'.congr_ae_velocity hv'e) (fun K hK => ?_) h0
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  have hκc := hasCompactSupport_of_eq_zero_of_one_lt hκ1
  obtain ⟨D1, hD1⟩ :=
    ((hκ.of_le (by simp) : ContDiff ℝ 1 (dlMollifier d)).continuous_fderiv
      one_ne_zero).bounded_above_of_compact_support (hκc.fderiv ℝ)
  have hQ := jacLqNorm_ne_top hpq.symm.pos hDq' hK
  set Pw : ℝ≥0∞ := 2 ^ (p - 1) * (P + P) with hPw
  have hPw' : Pw ≠ ⊤ := ENNReal.mul_ne_top (by simp [ENNReal.rpow_eq_top_iff])
    (ENNReal.add_ne_top.2 ⟨hP, hP⟩)
  refine ⟨1, one_pos, (ENNReal.ofReal (D1 * 2 ^ d) + 1) * (Pw ^ (1 / p) * jacLqNorm Dv' q K),
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by have := hpq.pos; positivity)
        hPw') hQ), fun s hs => ?_⟩
  have hwi : Integrable (fun y => u s y - u' s y) := (hu s hs.le).1.sub (hu' s hs.le).1
  have hwp : ∫⁻ x, ‖u s x - u' s x‖ₑ ^ p ≤ Pw :=
    (lintegral_enorm_sub_rpow_le (hu s hs.le).1.aestronglyMeasurable hpq.lt.le).trans
      (mul_le_mul' le_rfl (add_le_add (hup s hs.le) (hup' s hs.le)))
  set W := hwi.aestronglyMeasurable.mk (fun y => u s y - u' s y) with hW
  have hWm : Measurable W := hwi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hWe : (fun y => u s y - u' s y) =ᵐ[volume] W := hwi.aestronglyMeasurable.ae_eq_mk
  have hWp : ∫⁻ x, ‖W x‖ₑ ^ p ≤ Pw := by
    have e : ∫⁻ x, ‖W x‖ₑ ^ p = ∫⁻ x, ‖u s x - u' s x‖ₑ ^ p :=
      lintegral_congr_ae (hWe.mono fun x hx => by simp only [hx])
    rw [e]
    exact hwp
  have hcong := fun ε => lintegral_dlCommutator_sub_congr_ae hWe
    (scaledKernel (dlMollifier d) ε) v' Dv' K
  simp_rw [hcong]
  refine ⟨tendsto_lintegral_dlCommutator_sub_Lp hJ hv'm hD'm hv'V hpq hWm
    (hwi.congr hWe) (ne_top_of_le_ne_top hPw' hWp) hK hQ, fun ε hε => ?_⟩
  refine (lintegral_enorm_dlCommutator_sub_le_Lp (hκ.of_le (by simp)) hκ1 hD1 hJ hv'm hD'm
    hpq hWm hK.measurableSet hε.1 hε.2.le).trans ?_
  exact mul_le_mul' le_rfl (mul_le_mul'
    (ENNReal.rpow_le_rpow hWp (one_div_nonneg.2 hpq.pos.le)) le_rfl)

end NoiseScore
end FormalizeSampling
