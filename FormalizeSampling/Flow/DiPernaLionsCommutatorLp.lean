module

public import FormalizeSampling.Flow.DiPernaLionsRenormalizationBeta

/-!
# The DiPerna–Lions commutator lemma for `L^p` functions and `W^{1,q}_loc` velocities

Status: **Verified.** For `1/p + 1/q = 1`, a velocity `v ∈ W^{1,q}_loc(ℝᵈ; ℝᵈ)` (Borel
representatives, linear growth) and `f ∈ L¹ ∩ L^p(ℝᵈ)`, the kernel-form commutator

  `C_ε(f, v)(x) = ∫ f(y) Dκ_ε(x - y) (v(y) - v(x)) dy`

converges to `f div v` in `L¹(K)` for every compact `K`, with the explicit uniform bound
`∫_K |C_ε(f, v) - f div v| ≤ (D₁ 2^d + 1) ‖f‖_{L^p} ‖Dv‖_{L^q(K₁)}` for `ε ≤ 1`
(`K₁ = cthickening 1 K`). This extends `Flow/DiPernaLionsCommutatorL1.lean` (`f ∈ L^∞`,
`v ∈ W^{1,1}_loc`) by Hölder's inequality.

## Method

* Pointwise, `|C_ε(f, v)(x)| ≤ ε^{-d-1} D₁ ∫_{B(0,ε)} |f(x+h)| ‖v(x+h) - v(x)‖ dh`
  (`enorm_dlCommutator_le_lintegral`), a measurable majorant (`dlCommMajorant`).
* The difference-quotient identity of `Foundations/WeakDifferenceQuotient.lean` gives
  `‖v(x+h) - v(x)‖ ≤ ∑_{j,i} |hᵢ| ∫₀¹ |∂ᵢvⱼ(x + s h)| ds` a.e.; Tonelli and Hölder (for each
  `h, s` separately, so no Jensen inequality is needed) bound the majorant's `L¹(K)` norm by
  `D₁ 2^d ‖f‖_{L^p} ‖Dv‖_{L^q(K₁)}` (`lintegral_dlCommMajorant_le`).
* Convergence: truncate `f = T_N f + (f - T_N f)`; the `L^∞` lemma handles `T_N f`, the uniform
  bound handles the remainder (`tendsto_lintegral_dlCommutator_sub_Lp`).

## Main results

* `lintegral_enorm_dlCommutator_sub_le_Lp`: the uniform `L^p`–`W^{1,q}` bound.
* `tendsto_lintegral_dlCommutator_sub_Lp`: the commutator lemma for `L^p` functions.

## Not proved here

* The endpoint cases `p = 1` (`v ∈ W^{1,∞}`, covered by Lipschitz theory) and `p = ∞`
  (`Flow/DiPernaLionsCommutatorL1.lean`); the lemma is stated for Hölder conjugate `1 < p, q`.
* Velocities without linear growth: the growth bound is only used for the integrability that
  makes `C_ε` linear in `f`; a version with `v ∈ L^q_loc` only is not formalized.
* Convergence rates; the lemma is qualitative.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **Pointwise commutator majorant (Verified).** For `κ ∈ C¹` vanishing outside the unit
ball with `‖Dκ‖ ≤ D₁` and `ε > 0`, without any integrability assumption,
`|C_{κ_ε}(f, v)(x)| ≤ ε^{-d-1} D₁ ∫_{B(0,ε)} |f(x+h)| ‖v(x+h) - v(x)‖ dh`. -/
theorem enorm_dlCommutator_le_lintegral {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) {D1 : ℝ} (hD1 : ∀ z, ‖fderiv ℝ κ z‖ ≤ D1) {ε : ℝ}
    (hε : 0 < ε) (f : (Fin d → ℝ) → ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    ‖dlCommutator (scaledKernel κ ε) f v x‖ₑ ≤ ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹ * D1) *
      ∫⁻ h in closedBall 0 ε, ‖f (x + h)‖ₑ * ‖v (x + h) - v x‖ₑ := by
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hLb : ∀ y, ‖fderiv ℝ (scaledKernel κ ε) (x - y)‖ ≤ (ε ^ d)⁻¹ * ε⁻¹ * D1 := by
    intro y
    rw [norm_fderiv_scaledKernel hκ hε]
    exact mul_le_mul_of_nonneg_left (hD1 _) (by positivity)
  have hL0 : ∀ y, y ∉ closedBall x ε → fderiv ℝ (scaledKernel κ ε) (x - y) = 0 := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    exact fderiv_scaledKernel_eq_zero hκ1 hε (by rwa [norm_sub_rev])
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have ht := setLIntegral_closedBall_eq_add (fun y => ‖f y‖ₑ * ‖v y - v x‖ₑ) x ε
  rw [← ht, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ closedBall x ε
  · rw [indicator_of_mem hy, enorm_mul]
    calc ‖f y‖ₑ * ‖fderiv ℝ (scaledKernel κ ε) (x - y) (v y - v x)‖ₑ
        ≤ ‖f y‖ₑ * (ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹ * D1) * ‖v y - v x‖ₑ) := by
          refine mul_le_mul' le_rfl ?_
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hLb y) (norm_nonneg _)))
      _ = ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹ * D1) * (‖f y‖ₑ * ‖v y - v x‖ₑ) := by ring
  · rw [indicator_of_notMem hy, hL0 y hy]
    simp

/-- **Weighted difference-quotient estimate (Verified).** For `v ∈ W^{1,1}_loc` (Borel
representatives), a measurable weight `F ≥ 0`, any set `K` and increment `h`,
`∫_K F(x) ‖v(x+h) - v(x)‖ ≤ ∑_{j,i} |hᵢ| ∫_{(0,1]} ∫_K F(x) |∂ᵢvⱼ(x + s h)| dx ds`. -/
theorem lintegral_mul_enorm_sub_le {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {F : (Fin d → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (K : Set (Fin d → ℝ)) (h : Fin d → ℝ) :
    ∫⁻ x in K, F x * ‖v (x + h) - v x‖ₑ ≤
      ∑ j, ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, F x * ‖Dv (x + s • h) j i‖ₑ := by
  have hDji : ∀ j i, Measurable fun x => Dv x j i := fun j i => (hDm.eval).eval
  have hae : ∀ᵐ x, ∀ j, v (x + h) j - v x j =
      ∑ i, h i * ∫ s in (0 : ℝ)..1, Dv (x + s • h) j i := by
    rw [ae_all_iff]
    intro j
    exact ae_sub_eq_sum_intervalIntegral_of_hasWeakPartialDeriv (f := fun x => v x j)
      (g := fun i x => Dv x j i) hvm.eval (fun i => hDji j i) (fun i => hv j i) h
  have hpt : ∀ᵐ x, F x * ‖v (x + h) - v x‖ₑ ≤
      ∑ j, ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, F x * ‖Dv (x + s • h) j i‖ₑ := by
    filter_upwards [hae] with x hx
    refine (mul_le_mul' le_rfl (enorm_le_sum_enorm _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [Pi.sub_apply]
    rw [hx j]
    refine (mul_le_mul' le_rfl (enorm_sum_le _ _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [enorm_mul, lintegral_const_mul'' _ ?_]
    · rw [mul_left_comm]
      refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact enorm_integral_le_lintegral_enorm _
    · exact ((hDji j i).comp (measurable_const.add (measurable_id.smul_const h))).enorm
        |>.aemeasurable
  have hm : ∀ j i, Measurable fun p : (Fin d → ℝ) × ℝ => F p.1 * ‖Dv (p.1 + p.2 • h) j i‖ₑ :=
    fun j i => (hF.comp measurable_fst).mul (((hDji j i).comp
      (by fun_prop : Measurable fun p : (Fin d → ℝ) × ℝ => p.1 + p.2 • h)).enorm)
  calc ∫⁻ x in K, F x * ‖v (x + h) - v x‖ₑ
      ≤ ∫⁻ x in K, ∑ j, ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, F x * ‖Dv (x + s • h) j i‖ₑ :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ∑ j, ∑ i, ‖h i‖ₑ * ∫⁻ x in K, ∫⁻ s in Ioc (0 : ℝ) 1, F x * ‖Dv (x + s • h) j i‖ₑ := by
        rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun i _ =>
          ((hm j i).lintegral_prod_right').const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ fun i _ => ((hm j i).lintegral_prod_right').const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul _ (hm j i).lintegral_prod_right']
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_lintegral_swap (hm j i).aemeasurable]


/-- **Hölder with translations (Verified).** For `1/p + 1/q = 1`, measurable `f, g`, a
measurable set `K` and `‖a‖ ≤ 1`,
`∫_K |f(x+h)| |g(x+a)| ≤ ‖f‖_{L^p(ℝᵈ)} ‖g‖_{L^q(K₁)}` with `K₁ = cthickening 1 K`. -/
theorem setLIntegral_enorm_mul_le_holder {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : (Fin d → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) {K : Set (Fin d → ℝ)}
    (hK : MeasurableSet K) (h a : Fin d → ℝ) (ha : ‖a‖ ≤ 1) :
    ∫⁻ x in K, ‖f (x + h)‖ₑ * ‖g (x + a)‖ₑ ≤
      (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) * (∫⁻ x in cthickening 1 K, ‖g x‖ₑ ^ q) ^ (1 / q) := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) hpq
    (f := fun x => ‖f (x + h)‖ₑ) (g := fun x => ‖g (x + a)‖ₑ)
    (hf.comp (measurable_id.add_const h)).enorm.aemeasurable
    (hg.comp (measurable_id.add_const a)).enorm.aemeasurable
  refine H.trans (mul_le_mul' (ENNReal.rpow_le_rpow ?_ (by have := hpq.pos; positivity))
    (ENNReal.rpow_le_rpow ?_ (by have := hpq.symm.pos; positivity)))
  · calc ∫⁻ x in K, ‖f (x + h)‖ₑ ^ p ≤ ∫⁻ x, ‖f (x + h)‖ₑ ^ p := setLIntegral_le_lintegral _ _
      _ = ∫⁻ x, ‖f x‖ₑ ^ p := lintegral_add_right_eq_self (fun x => ‖f x‖ₑ ^ p) h
  · have hK1 : MeasurableSet (cthickening 1 K) := isClosed_cthickening.measurableSet
    calc ∫⁻ x in K, ‖g (x + a)‖ₑ ^ q
        ≤ ∫⁻ x, (cthickening 1 K).indicator (fun y => ‖g y‖ₑ ^ q) (x + a) := by
          rw [← lintegral_indicator hK]
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ K
          · rw [indicator_of_mem hx, indicator_of_mem]
            exact mem_cthickening_of_dist_le _ x 1 K hx (by
              rw [dist_eq_norm, add_sub_cancel_left]; exact ha)
          · rw [indicator_of_notMem hx]; exact zero_le
      _ = ∫⁻ x in cthickening 1 K, ‖g x‖ₑ ^ q := by
          rw [lintegral_add_right_eq_self (fun y => (cthickening 1 K).indicator
            (fun y => ‖g y‖ₑ ^ q) y) a, lintegral_indicator hK1]

/-- The **local `L^q` size of a Jacobian** on the `1`-thickening of `K`:
`∑_{j,i} ‖∂ᵢvⱼ‖_{L^q(cthickening 1 K)}` (in `ℝ≥0∞`). -/
noncomputable def jacLqNorm (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) (q : ℝ)
    (K : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑ j, ∑ i, (∫⁻ x in cthickening 1 K, ‖Dv x j i‖ₑ ^ q) ^ (1 / q)

/-- The measurable majorant `ε^{-d-1} D₁ ∫_{B(0,ε)} |f(x+h)| |v(x+h) - v(x)| dh` of the
commutator. -/
noncomputable def dlCommMajorant (D1 ε : ℝ) (f : (Fin d → ℝ) → ℝ)
    (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹ * D1) *
    ∫⁻ h in closedBall 0 ε, ‖f (x + h)‖ₑ * ‖v (x + h) - v x‖ₑ

/-- The commutator majorant is measurable in `x` (Verified). -/
theorem measurable_dlCommMajorant {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    {v : (Fin d → ℝ) → Fin d → ℝ} (hvm : Measurable v) (D1 ε : ℝ) :
    Measurable (dlCommMajorant D1 ε f v) := by
  have hmeas : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ‖f (p.1 + p.2)‖ₑ * ‖v (p.1 + p.2) - v p.1‖ₑ :=
    (hf.comp (measurable_fst.add measurable_snd)).enorm.mul
      ((hvm.comp (measurable_fst.add measurable_snd)).sub (hvm.comp measurable_fst)).enorm
  exact measurable_const.mul hmeas.lintegral_prod_right'

/-- **`L¹(K)` bound for the commutator majorant (Verified).** For `v ∈ W^{1,1}_loc`,
`1/p + 1/q = 1`, measurable `f` and `0 < ε ≤ 1`,
`∫_K ε^{-d-1} D₁ ∫_{B(0,ε)} |f(x+h)| ‖v(x+h) - v(x)‖ dh dx ≤ D₁ 2^d ‖f‖_{L^p} ‖Dv‖_{L^q(K₁)}`
(difference quotients along segments, Tonelli and Hölder). -/
theorem lintegral_dlCommMajorant_le {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {D1 : ℝ} (hD10 : 0 ≤ D1)
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    {K : Set (Fin d → ℝ)} (hK : MeasurableSet K) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫⁻ x in K, dlCommMajorant D1 ε f v x ≤
      ENNReal.ofReal (D1 * 2 ^ d) * ((∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) * jacLqNorm Dv q K) := by
  set Fp := (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) with hFp
  set c := ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹ * D1) with hc
  have hDji : ∀ j i, Measurable fun x => Dv x j i := fun j i => (hDm.eval).eval
  have hmeas : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ‖f (p.1 + p.2)‖ₑ * ‖v (p.1 + p.2) - v p.1‖ₑ :=
    (hf.comp (measurable_fst.add measurable_snd)).enorm.mul
      ((hvm.comp (measurable_fst.add measurable_snd)).sub (hvm.comp measurable_fst)).enorm
  have hinner : ∀ h : Fin d → ℝ, ‖h‖ ≤ 1 →
      ∫⁻ x in K, ‖f (x + h)‖ₑ * ‖v (x + h) - v x‖ₑ ≤ ‖h‖ₑ * (Fp * jacLqNorm Dv q K) := by
    intro h hh
    refine (lintegral_mul_enorm_sub_le hv hvm hDm
      (hf.comp (measurable_id.add_const h)).enorm K h).trans ?_
    calc ∑ j, ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, ‖f (x + h)‖ₑ *
          ‖Dv (x + s • h) j i‖ₑ
        ≤ ∑ j, ∑ i, ‖h‖ₑ * (Fp * (∫⁻ x in cthickening 1 K, ‖Dv x j i‖ₑ ^ q) ^ (1 / q)) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul' (enorm_apply_le h i) ?_
          calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, ‖f (x + h)‖ₑ * ‖Dv (x + s • h) j i‖ₑ
              ≤ ∫⁻ _s in Ioc (0 : ℝ) 1,
                  Fp * (∫⁻ x in cthickening 1 K, ‖Dv x j i‖ₑ ^ q) ^ (1 / q) := by
                refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
                refine setLIntegral_enorm_mul_le_holder hpq hf (hDji j i) hK h (s • h) ?_
                rw [norm_smul, Real.norm_of_nonneg hs.1.le]
                nlinarith [hs.2, norm_nonneg h]
            _ = Fp * (∫⁻ x in cthickening 1 K, ‖Dv x j i‖ₑ ^ q) ^ (1 / q) := by simp
      _ = ‖h‖ₑ * (Fp * jacLqNorm Dv q K) := by
          rw [jacLqNorm, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
  calc ∫⁻ x in K, dlCommMajorant D1 ε f v x
      = c * ∫⁻ h in closedBall 0 ε, ∫⁻ x in K, ‖f (x + h)‖ₑ * ‖v (x + h) - v x‖ₑ := by
        simp only [dlCommMajorant]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_lintegral_swap hmeas.aemeasurable]
    _ ≤ c * ∫⁻ _h in closedBall (0 : Fin d → ℝ) ε,
          ENNReal.ofReal ε * (Fp * jacLqNorm Dv q K) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_closedBall fun h hh => ?_)
        have hh' : ‖h‖ ≤ ε := by rwa [mem_closedBall, dist_zero_right] at hh
        refine (hinner h (hh'.trans hε1)).trans (mul_le_mul' ?_ le_rfl)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hh'
    _ = ENNReal.ofReal (D1 * 2 ^ d) * (Fp * jacLqNorm Dv q K) := by
        rw [setLIntegral_const, hc]
        have e1 : ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹ * D1) = ENNReal.ofReal ((ε ^ d)⁻¹) *
            ENNReal.ofReal ε⁻¹ * ENNReal.ofReal D1 := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        have hεε : ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε = 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε.le), inv_mul_cancel₀ hε.ne',
            ENNReal.ofReal_one]
        have e2 : ENNReal.ofReal (D1 * 2 ^ d) = ENNReal.ofReal D1 * ENNReal.ofReal (2 ^ d) :=
          ENNReal.ofReal_mul hD10
        rw [e1, e2, ← ofReal_mul_volume_closedBall hε]
        calc ENNReal.ofReal (ε ^ d)⁻¹ * ENNReal.ofReal ε⁻¹ * ENNReal.ofReal D1 *
              (ENNReal.ofReal ε * (Fp * jacLqNorm Dv q K) * volume (closedBall (0 : Fin d → ℝ) ε))
            = ENNReal.ofReal D1 * (ENNReal.ofReal (ε ^ d)⁻¹ *
                volume (closedBall (0 : Fin d → ℝ) ε)) * (Fp * jacLqNorm Dv q K) *
                (ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε) := by ring
          _ = _ := by rw [hεε, mul_one]

/-- `∫_K |f div v| ≤ ‖f‖_{L^p} ‖Dv‖_{L^q(K₁)}` (Verified, Hölder). -/
theorem lintegral_enorm_mul_weakDiv_le {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hDm : Measurable Dv) {p q : ℝ} (hpq : p.HolderConjugate q) {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) {K : Set (Fin d → ℝ)} (hK : MeasurableSet K) :
    ∫⁻ x in K, ‖f x * weakDiv Dv x‖ₑ ≤ (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) * jacLqNorm Dv q K := by
  have hDji : ∀ j i, Measurable fun x => Dv x j i := fun j i => (hDm.eval).eval
  calc ∫⁻ x in K, ‖f x * weakDiv Dv x‖ₑ ≤ ∫⁻ x in K, ∑ i, ‖f (x + 0)‖ₑ * ‖Dv (x + 0) i i‖ₑ := by
        refine lintegral_mono fun x => ?_
        simp only [add_zero, weakDiv, Finset.mul_sum]
        refine (enorm_sum_le _ _).trans (le_of_eq ?_)
        simp [enorm_mul]
    _ = ∑ i, ∫⁻ x in K, ‖f (x + 0)‖ₑ * ‖Dv (x + 0) i i‖ₑ :=
        lintegral_finsetSum _ fun i _ =>
          ((hf.comp (measurable_id.add_const 0)).enorm).mul
            ((hDji i i).comp (measurable_id.add_const 0)).enorm
    _ ≤ ∑ i, (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) *
          (∫⁻ x in cthickening 1 K, ‖Dv x i i‖ₑ ^ q) ^ (1 / q) :=
        Finset.sum_le_sum fun i _ =>
          setLIntegral_enorm_mul_le_holder hpq hf (hDji i i) hK 0 0 (by simp)
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) * jacLqNorm Dv q K := by
        rw [jacLqNorm, Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl ?_
        exact Finset.single_le_sum (f := fun i => (∫⁻ x in cthickening 1 K,
          ‖Dv x j i‖ₑ ^ q) ^ (1 / q)) (fun i _ => zero_le) (Finset.mem_univ j)

/-- **Uniform `L^p`–`W^{1,q}` commutator bound (Verified).** For `0 < ε ≤ 1`,
`∫_K |C_{κ_ε}(f, v) - f div v| ≤ (D₁ 2^d + 1) ‖f‖_{L^p} ‖Dv‖_{L^q(K₁)}`, for every measurable
`f` (no integrability needed: the right side may be infinite). -/
theorem lintegral_enorm_dlCommutator_sub_le_Lp {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) {D1 : ℝ} (hD1 : ∀ z, ‖fderiv ℝ κ z‖ ≤ D1)
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) (hDm : Measurable Dv)
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    {K : Set (Fin d → ℝ)} (hK : MeasurableSet K) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫⁻ x in K, ‖dlCommutator (scaledKernel κ ε) f v x - f x * weakDiv Dv x‖ₑ ≤
      (ENNReal.ofReal (D1 * 2 ^ d) + 1) *
        ((∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) * jacLqNorm Dv q K) := by
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hdivm : Measurable (weakDiv Dv) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hDm)
  calc ∫⁻ x in K, ‖dlCommutator (scaledKernel κ ε) f v x - f x * weakDiv Dv x‖ₑ
      ≤ ∫⁻ x in K, (dlCommMajorant D1 ε f v x + ‖f x * weakDiv Dv x‖ₑ) :=
        lintegral_mono fun x => (enorm_sub_le).trans
          (add_le_add (enorm_dlCommutator_le_lintegral hκ hκ1 hD1 hε f v x) le_rfl)
    _ = (∫⁻ x in K, dlCommMajorant D1 ε f v x) + ∫⁻ x in K, ‖f x * weakDiv Dv x‖ₑ :=
        lintegral_add_left (measurable_dlCommMajorant hf hvm D1 ε) _
    _ ≤ _ := by
        rw [add_mul, one_mul]
        exact add_le_add (lintegral_dlCommMajorant_le hv hvm hDm hD10 hpq hf hK hε hε1)
          (lintegral_enorm_mul_weakDiv_le hDm hpq hf hK)


/-- The truncation `T_N a = max (-N) (min N a)` satisfies `|a - T_N a| ≤ |a|` (Verified). -/
theorem abs_sub_trunc_le {N : ℝ} (hN : 0 ≤ N) (a : ℝ) : |a - max (-N) (min N a)| ≤ |a| := by
  rcases le_or_gt 0 a with ha | ha
  · have h1 : min N a ≤ a := min_le_right _ _
    have h2 : 0 ≤ min N a := le_min hN ha
    rw [max_eq_right (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg ha]
    linarith
  · rw [min_eq_right (by linarith)]
    have h3 : a ≤ max (-N) a := le_max_right _ _
    have h4 : max (-N) a ≤ 0 := max_le (by linarith) ha.le
    rw [abs_of_nonpos (by linarith), abs_of_neg ha]
    linarith

/-- `T_N a = a` when `|a| ≤ N` (Verified). -/
theorem trunc_eq_self {N a : ℝ} (h : |a| ≤ N) : max (-N) (min N a) = a := by
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- **Integrability of the commutator integrand (Verified).** For `k ∈ C¹` with `Dk = 0`
outside the unit ball, `v` measurable of linear growth and `u` integrable,
`y ↦ u(y) Dk(x - y)(v(y) - v(x))` is integrable. -/
theorem integrable_mul_fderiv_apply_sub_of_linearGrowth {k : (Fin d → ℝ) → ℝ}
    (hk : ContDiff ℝ 1 k) (hk1 : ∀ z, 1 < ‖z‖ → fderiv ℝ k z = 0) {Dk : ℝ}
    (hDk : ∀ z, ‖fderiv ℝ k z‖ ≤ Dk) {v : (Fin d → ℝ) → Fin d → ℝ} (hvm : Measurable v)
    {Mv : ℝ} (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖)) {u : (Fin d → ℝ) → ℝ} (hu : Integrable u)
    (x : Fin d → ℝ) : Integrable fun y => u y * fderiv ℝ k (x - y) (v y - v x) := by
  have hc : Continuous fun y => fderiv ℝ k (x - y) (v x) :=
    ((hk.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const
  have h2 : Integrable fun y => u y * fderiv ℝ k (x - y) (v x) :=
    hu.mul_bdd (c := Dk * ‖v x‖) hc.aestronglyMeasurable (Eventually.of_forall fun y =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDk _) (norm_nonneg _)))
  refine ((integrable_mul_fderiv_apply_of_linearGrowth hk hk1 hDk hvm hMv hu x).sub h2).congr
    (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply, map_sub, mul_sub]

/-- **DiPerna–Lions commutator lemma for `L^p` functions (Verified).** Let `v` be measurable
with linear growth and a measurable weak Jacobian `Dv`, `1/p + 1/q = 1`, `K` compact with
`‖Dv‖_{L^q(cthickening 1 K)} < ∞`, and let `f` be measurable, integrable and in `L^p`. Then
`∫_K |C_ε(f, v) - f div v| → 0` as `ε → 0⁺` (`κ = dlMollifier d`).

Proof: split `f = T_N f + (f - T_N f)`; the bounded part converges by the `L^∞`–`W^{1,1}`
lemma `tendsto_lintegral_dlCommutator_sub`, and the remainder is bounded by
`lintegral_enorm_dlCommutator_sub_le_Lp`, uniformly in `ε`, by
`C ‖f - T_N f‖_{L^p} → 0` (dominated convergence). -/
theorem tendsto_lintegral_dlCommutator_sub_Lp {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {Mv : ℝ} (hMv : ∀ x, ‖v x‖ ≤ Mv * (1 + ‖x‖))
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : (Fin d → ℝ) → ℝ} (hfm : Measurable f)
    (hfi : Integrable f) (hfp : ∫⁻ x, ‖f x‖ₑ ^ p ≠ ⊤) {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hQ : jacLqNorm Dv q K ≠ ⊤) :
    Tendsto (fun ε => ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x -
      f x * weakDiv Dv x‖ₑ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hκ, hκ0, hκ1, hκint⟩ := dlMollifier_spec (d := d)
  have hκc := hasCompactSupport_of_eq_zero_of_one_lt hκ1
  obtain ⟨D1, hD1⟩ :=
    ((hκ.of_le (by simp) : ContDiff ℝ 1 (dlMollifier d)).continuous_fderiv
      one_ne_zero).bounded_above_of_compact_support (hκc.fderiv ℝ)
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hp0 : 0 < p := hpq.pos
  set T : ℕ → (Fin d → ℝ) → ℝ := fun N x => max (-(N : ℝ)) (min (N : ℝ) (f x)) with hT
  set g : ℕ → (Fin d → ℝ) → ℝ := fun N x => f x - T N x with hg
  have hTm : ∀ N, Measurable (T N) := fun N =>
    measurable_const.max (measurable_const.min hfm)
  have hTU : ∀ N x, |T N x| ≤ N := fun N x => by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) N])
      (min_le_left _ _)⟩
  have hgf : ∀ N x, |g N x| ≤ |f x| := fun N x => abs_sub_trunc_le (Nat.cast_nonneg N) _
  have hgm : ∀ N, Measurable (g N) := fun N => hfm.sub (hTm N)
  have hgi : ∀ N, Integrable (g N) := fun N =>
    hfi.mono (hgm N).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hgf N x)
  have hTi : ∀ N, Integrable (T N) := fun N => (hfi.sub (hgi N)).congr
    (Eventually.of_forall fun x => by simp [hg])
  -- the truncation error tends to zero in `L^p`
  have hG : Tendsto (fun N : ℕ => (∫⁻ x, ‖g N x‖ₑ ^ p) ^ (1 / p)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ∫⁻ x, ‖g N x‖ₑ ^ p) atTop (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence (fun x => ‖f x‖ₑ ^ p)
        (F := fun N x => ‖g N x‖ₑ ^ p) (f := fun _ => 0)
        (fun N => (hgm N).enorm.pow_const p)
        (fun N => Eventually.of_forall fun x => ENNReal.rpow_le_rpow (by
          rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hgf N x)) hp0.le) hfp
        (Eventually.of_forall fun x => ?_)
      · simpa using this
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈|f x|⌉₊] with N hN
        have : |f x| ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
        simp only [hg, hT, trunc_eq_self this, sub_self, enorm_zero]
        exact (ENNReal.zero_rpow_of_pos hp0).symm
    have h2 := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
    exact h2.comp h1
  set Cst := ENNReal.ofReal (D1 * 2 ^ d) + 1 with hCst
  have hCst' : Cst ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hG' : Tendsto (fun N : ℕ => Cst * ((∫⁻ x, ‖g N x‖ₑ ^ p) ^ (1 / p) * jacLqNorm Dv q K))
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const hG (Or.inr hQ)) (Or.inr hCst')
    simpa using this
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨N, hN⟩ := (hG'.eventually_lt_const he2).exists
  have hX := tendsto_lintegral_dlCommutator_sub (hκ.of_le (by simp)) hκ1 hκint hv hvm hDm
    (hTm N) (hTU N) hK
  filter_upwards [hX.eventually_lt_const he2, Ioo_mem_nhdsGT one_pos] with ε hε hε1
  have hlin : ∀ x, dlCommutator (scaledKernel (dlMollifier d) ε) f v x =
      dlCommutator (scaledKernel (dlMollifier d) ε) (T N) v x +
        dlCommutator (scaledKernel (dlMollifier d) ε) (g N) v x := by
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := dlMollifier_scaled_spec (d := d) hε1.1
    obtain ⟨Dk, hDk⟩ := (h1.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (h2.fderiv ℝ)
    have hk1 : ∀ z : Fin d → ℝ, 1 < ‖z‖ →
        fderiv ℝ (scaledKernel (dlMollifier d) ε) z = 0 := fun z hz =>
      fderiv_scaledKernel_eq_zero hκ1 hε1.1 (hε1.2.trans hz)
    simp only [dlCommutator]
    rw [← integral_add (integrable_mul_fderiv_apply_sub_of_linearGrowth (h1.of_le (by simp))
      hk1 hDk hvm hMv (hTi N) x) (integrable_mul_fderiv_apply_sub_of_linearGrowth
        (h1.of_le (by simp)) hk1 hDk hvm hMv (hgi N) x)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hg]
    ring
  have hdivm : Measurable (weakDiv Dv) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hDm)
  calc ∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) f v x -
        f x * weakDiv Dv x‖ₑ
      ≤ ∫⁻ x in K, (‖dlCommutator (scaledKernel (dlMollifier d) ε) (T N) v x -
          T N x * weakDiv Dv x‖ₑ + (dlCommMajorant D1 ε (g N) v x +
            ‖g N x * weakDiv Dv x‖ₑ)) := by
        refine lintegral_mono fun x => ?_
        have e : dlCommutator (scaledKernel (dlMollifier d) ε) f v x - f x * weakDiv Dv x =
            (dlCommutator (scaledKernel (dlMollifier d) ε) (T N) v x - T N x * weakDiv Dv x) +
            (dlCommutator (scaledKernel (dlMollifier d) ε) (g N) v x -
              g N x * weakDiv Dv x) := by
          rw [hlin]; simp only [hg]; ring
        rw [e]
        refine (enorm_add_le _ _).trans (add_le_add le_rfl ((enorm_sub_le).trans
          (add_le_add (enorm_dlCommutator_le_lintegral (hκ.of_le (by simp)) hκ1 hD1 hε1.1
            (g N) v x) le_rfl)))
    _ = (∫⁻ x in K, ‖dlCommutator (scaledKernel (dlMollifier d) ε) (T N) v x -
          T N x * weakDiv Dv x‖ₑ) + ∫⁻ x in K, (dlCommMajorant D1 ε (g N) v x +
            ‖g N x * weakDiv Dv x‖ₑ) :=
        lintegral_add_right' _ ((measurable_dlCommMajorant (hgm N) hvm D1 ε).add
          ((hgm N).mul hdivm).enorm).aemeasurable
    _ ≤ e / 2 + e / 2 := by
        refine add_le_add hε.le (le_trans ?_ hN.le)
        rw [lintegral_add_left (measurable_dlCommMajorant (hgm N) hvm D1 ε), hCst, add_mul,
          one_mul]
        exact add_le_add (lintegral_dlCommMajorant_le hv hvm hDm hD10 hpq (hgm N)
          hK.measurableSet hε1.1 hε1.2.le)
          (lintegral_enorm_mul_weakDiv_le hDm hpq (hgm N) hK.measurableSet)
    _ = e := ENNReal.add_halves e

end NoiseScore
end FormalizeSampling
