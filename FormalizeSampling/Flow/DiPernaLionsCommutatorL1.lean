module

public import FormalizeSampling.Foundations.MollifierL1
public import FormalizeSampling.Foundations.WeakDifferenceQuotient
public import FormalizeSampling.Flow.DiPernaLionsCommutator

/-!
# The DiPerna–Lions commutator lemma in `L¹_loc`

Status: **Verified.** For `v ∈ W^{1,1}_loc(ℝᵈ; ℝᵈ)` (weak Jacobian `Dv`, Borel
representatives) and a bounded measurable `w`, the kernel-form commutator of
`Flow/ContinuityUniquenessDiPernaLions.lean`

  `C_{κ_ε}(w, v)(x) = ∫ w(y) Dκ_ε(x - y) (v(y) - v(x)) dy`,   `κ_ε(z) = ε^{-d} κ(z / ε)`,

converges to `w div v` in `L¹(K)` for every compact `K` as `ε → 0⁺`, with an `L¹(K)` bound
that is uniform in `ε < ε₀` and in all `w` with `|w| ≤ U`. This is the key analytic input of
the DiPerna–Lions renormalization argument, valid in every dimension `d`.

## Proof

Write `A = Dv(x)`. The moment identity `∫ Dκ(z)(A z) dz = -(tr A) ∫ κ`
(`integral_fderiv_apply_mulVec`, integration by parts) gives
`w(x) div v(x) = ∫ w(x) Dκ_ε(x - y)(A (y - x)) dy`, hence
`C_ε - w div v = ∫ w(y) Dκ_ε(x-y) R(x,y) dy + ∫ (w(y) - w(x)) Dκ_ε(x-y) (A(y-x)) dy`
with the Taylor remainder `R(x,y) = v(y) - v(x) - A(y - x)` (`enorm_dlCommutator_sub_le`).

* The first term is bounded by `U ‖Dκ‖_∞ ε^{-d-1} ∫_{B(0,ε)} ‖R(x, x+h)‖ dh`; after Tonelli,
  the difference-quotient identity for Sobolev functions
  (`Foundations/WeakDifferenceQuotient.lean`) and continuity of translations in `L¹`
  (`Foundations/MollifierL1.lean`) give `∫_K ‖R(x, x+h)‖ dx ≤ ‖h‖ η` for small `h`
  (`exists_lintegral_taylor_remainder_le`), so the term is `≤ U ‖Dκ‖_∞ 2^d η`.
* The second term is bounded by `‖Dκ‖_∞ |Dv(x)| ε^{-d} ∫_{B(0,ε)} |w(x+h) - w(x)| dh`, which
  tends to `0` a.e. by the Lebesgue differentiation theorem and is dominated by
  `2 U 2^d ‖Dκ‖_∞ |Dv| ∈ L¹(K)` (`tendsto_lintegral_oscAvg_mul`).

## Main results

* `integral_fderiv_apply_mulVec`: `∫ Dκ(z)(A z) dz = -(tr A) ∫ κ`.
* `exists_lintegral_taylor_remainder_le`: `∫_K ‖v(x+h) - v(x) - Dv(x) h‖ ≤ ‖h‖ η`, `‖h‖ < δ`.
* `enorm_dlCommutator_sub_le`: the pointwise decomposition bound.
* `tendsto_lintegral_dlCommutator_sub`: `∫_K |C_{κ_ε}(w, v) - w div v| → 0`.
* `exists_lintegral_dlCommutator_sub_le`: uniform bound for `ε < ε₀`, `|w| ≤ U`.

## Not proved here

* Renormalization, the passage `ε → 0` in the mollified equation, cut-offs and the Gronwall
  step (see `Flow/DiPernaLionsRenormalization.lean` and the files built on it).
* `L^p`–`W^{1,p'}` versions of the commutator lemma (`w ∈ L^p_loc`, `v ∈ W^{1,p'}_loc`);
  only `w ∈ L^∞` with `v ∈ W^{1,1}_loc` is treated here. The version for `w ∈ L¹ ∩ L^p` and
  `v ∈ W^{1,q}_loc` of linear growth is `tendsto_lintegral_dlCommutator_sub_Lp`
  (`Flow/DiPernaLionsCommutatorLp.lean`).
* Convergence rates; the lemma is purely qualitative.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Matrix
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **Coordinate expansion of a linear form (Verified).**
`L h = ∑ᵢ hᵢ L(eᵢ)` on `Fin d → ℝ`. -/
theorem clm_apply_eq_sum (L : (Fin d → ℝ) →L[ℝ] ℝ) (h : Fin d → ℝ) :
    L h = ∑ i, h i * L (Pi.single i 1) := by
  have hsum : h = ∑ i, h i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum]
  simp [map_sum, map_smul, smul_eq_mul]

/-- **First moments of `∂ᵢκ` (Verified).** For `κ` `C¹` with compact support,
`∫ z_j ∂ᵢκ(z) dz = -δᵢⱼ ∫ κ` (integration by parts). -/
theorem integral_mul_fderiv_single {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκc : HasCompactSupport κ) (i j : Fin d) :
    ∫ z, z j * fderiv ℝ κ z (Pi.single i 1) = -((Pi.single i (1 : ℝ) : Fin d → ℝ) j) *
      ∫ z, κ z := by
  have hcj : Continuous fun z : Fin d → ℝ => z j := continuous_apply j
  have hDκ : Continuous fun z => fderiv ℝ κ z (Pi.single i 1) :=
    (hκ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : HasCompactSupport fun z => fderiv ℝ κ z (Pi.single i 1) :=
    (hκc.fderiv ℝ).mono' fun x hx => by
      contrapose! hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hfd : ∀ z : Fin d → ℝ, fderiv ℝ (fun z : Fin d → ℝ => z j) z (Pi.single i 1) =
      (Pi.single i (1 : ℝ) : Fin d → ℝ) j := by
    intro z
    have : HasFDerivAt (fun z : Fin d → ℝ => z j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) z :=
      hasFDerivAt_apply j z
    rw [this.fderiv]; rfl
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z : Fin d → ℝ => z j) (g := κ) (v := Pi.single i 1)
    (by
      simp_rw [hfd]
      exact (hκ.continuous.integrable_of_hasCompactSupport hκc).const_mul _)
    ((hcj.mul hDκ).integrable_of_hasCompactSupport hDc.mul_left)
    ((hcj.mul hκ.continuous).integrable_of_hasCompactSupport hκc.mul_left)
    (fun z _ => (differentiableAt_apply j z))
    (fun z _ => (hκ.differentiable one_ne_zero) z)
  rw [h]
  simp_rw [hfd]
  rw [integral_const_mul, neg_mul]

/-- **Moment identity (Verified).** For a `C¹` compactly supported `κ` and a matrix `A`,
`∫ Dκ(z) (A z) dz = -(tr A) ∫ κ`. -/
theorem integral_fderiv_apply_mulVec {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκc : HasCompactSupport κ) (A : Matrix (Fin d) (Fin d) ℝ) :
    ∫ z, fderiv ℝ κ z (A *ᵥ z) = -(Matrix.trace A) * ∫ z, κ z := by
  have hDκ : ∀ i, Continuous fun z => fderiv ℝ κ z (Pi.single i 1) := fun i =>
    (hκ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : ∀ i, HasCompactSupport fun z => fderiv ℝ κ z (Pi.single i 1) := fun i =>
    (hκc.fderiv ℝ).mono' fun x hx => by
      contrapose! hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hint : ∀ i j, Integrable fun z : Fin d → ℝ => A i j * (z j * fderiv ℝ κ z (Pi.single i 1)) :=
    fun i j => (((continuous_apply j).mul (hDκ i)).integrable_of_hasCompactSupport
      (hDc i).mul_left).const_mul _
  have e : ∀ z, fderiv ℝ κ z (A *ᵥ z) =
      ∑ i, ∑ j, A i j * (z j * fderiv ℝ κ z (Pi.single i 1)) := by
    intro z
    rw [clm_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, integral_const_mul,
    integral_mul_fderiv_single hκ hκc]
  simp only [Matrix.trace, Matrix.diag, Finset.sum_mul, neg_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- The extended norm of a vector in `Fin d → ℝ` (sup norm) is at most the sum of the
extended norms of its coordinates. -/
theorem enorm_le_sum_enorm (f : Fin d → ℝ) : ‖f‖ₑ ≤ ∑ i, ‖f i‖ₑ := by
  rw [← ofReal_norm]
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
  refine ENNReal.ofReal_le_ofReal ((pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_)
  exact Finset.single_le_sum (f := fun i => ‖f i‖) (fun i _ => norm_nonneg _)
    (Finset.mem_univ i)

/-- The extended norm of a coordinate is at most the extended (sup) norm. -/
theorem enorm_apply_le (f : Fin d → ℝ) (i : Fin d) : ‖f i‖ₑ ≤ ‖f‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm f i)

/-- **`L¹` modulus of the first-order Taylor remainder of a `W^{1,1}_loc` field (Verified).**
Let `v` have a weak Jacobian `Dv` (both Borel measurable) and `K` be compact. For every
`η > 0` there is `δ > 0` such that for `‖h‖ < δ`,
`∫_K ‖v(x + h) - v(x) - Dv(x) h‖ dx ≤ ‖h‖ η`. -/
theorem exists_lintegral_taylor_remainder_le {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {K : Set (Fin d → ℝ)} (hK : IsCompact K) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, ∀ h : Fin d → ℝ, ‖h‖ < δ →
      ∫⁻ x in K, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ ≤ ‖h‖ₑ * η := by
  set η' := η / ((d : ℝ≥0∞) * d) with hη'
  have hη'0 : 0 < η' := ENNReal.div_pos hη.ne' (ENNReal.mul_ne_top (by simp) (by simp))
  have hDji : ∀ j i, Measurable fun x => Dv x j i := fun j i => (hDm.eval).eval
  have hvj : ∀ j, Measurable fun x => v x j := fun j => hvm.eval
  have hev : ∀ᶠ h in 𝓝 (0 : Fin d → ℝ), ∀ j i,
      ∫⁻ x in K, ‖Dv (x + h) j i - Dv x j i‖ₑ < η' := by
    refine Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun i => ?_
    exact (tendsto_lintegral_comp_add_sub (hv j i).2.1 hK).eventually_lt_const hη'0
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have hcomp : ∀ j, ∫⁻ x in K, ‖v (x + h) j - v x j - ∑ i, h i * Dv x j i‖ₑ ≤
      (d : ℝ≥0∞) * (‖h‖ₑ * η') := by
    intro j
    refine (lintegral_sub_sub_le_of_hasWeakPartialDeriv (hvj j) (hDji j) (hv j) K h).trans ?_
    calc ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, ‖Dv (x + s • h) j i - Dv x j i‖ₑ
        ≤ ∑ _i : Fin d, ‖h‖ₑ * η' := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul' (enorm_apply_le h i) ?_
          calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, ‖Dv (x + s • h) j i - Dv x j i‖ₑ
              ≤ ∫⁻ _s in Ioc (0 : ℝ) 1, η' := by
                refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
                refine (hδP ?_ j i).le
                rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hs.1.le]
                calc s * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
                  _ < δ := by rw [one_mul]; exact hh
            _ = η' := by simp
      _ = (d : ℝ≥0∞) * (‖h‖ₑ * η') := by simp
  calc ∫⁻ x in K, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ
      ≤ ∫⁻ x in K, ∑ j, ‖v (x + h) j - v x j - ∑ i, h i * Dv x j i‖ₑ := by
        refine lintegral_mono fun x => (enorm_le_sum_enorm _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
        simp_rw [mul_comm (h _)]
    _ = ∑ j, ∫⁻ x in K, ‖v (x + h) j - v x j - ∑ i, h i * Dv x j i‖ₑ := by
        refine lintegral_finsetSum _ fun j _ => ?_
        refine Measurable.enorm ?_
        refine (((hvj j).comp (measurable_id.add_const h)).sub (hvj j)).sub ?_
        exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hDji j i)
    _ ≤ ∑ _j : Fin d, (d : ℝ≥0∞) * (‖h‖ₑ * η') := Finset.sum_le_sum fun j _ => hcomp j
    _ = ‖h‖ₑ * ((d * d) * η') := by simp; ring
    _ ≤ ‖h‖ₑ * η := mul_le_mul' le_rfl ENNReal.mul_div_le

/-- **Translation of a ball integral (Verified).**
`∫⁻_{B(x, ε)} G(y) dy = ∫⁻_{B(0, ε)} G(x + h) dh`. -/
theorem setLIntegral_closedBall_eq_add (G : (Fin d → ℝ) → ℝ≥0∞) (x : Fin d → ℝ) (ε : ℝ) :
    ∫⁻ y in closedBall x ε, G y = ∫⁻ h in closedBall 0 ε, G (x + h) := by
  rw [← lintegral_indicator measurableSet_closedBall,
    ← lintegral_indicator measurableSet_closedBall,
    ← lintegral_add_left_eq_self _ x]
  congr 1
  funext h
  simp only [indicator, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]

/-- **Matrix–vector bound (Verified).** `‖A h‖ ≤ (∑_{j,i} |A_{j i}|) ‖h‖` (sup norms). -/
theorem norm_mulVec_le (A : Matrix (Fin d) (Fin d) ℝ) (h : Fin d → ℝ) :
    ‖A *ᵥ h‖ ≤ (∑ j, ∑ i, |A j i|) * ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ i, A j i * h i| ≤ ∑ i, |A j i * h i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |A j i| * ‖h‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm h i) (abs_nonneg _)
    _ = (∑ i, |A j i|) * ‖h‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ i, |A j i|) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum
          (f := fun j => ∑ i, |A j i|) (fun j _ => by positivity) (Finset.mem_univ j))
          (norm_nonneg _)

/-- **Integrability of a kernel applied to a locally integrable field (Verified).** If
`L : ℝᵈ → (ℝᵈ →L ℝ)` is continuous with compact support and every coordinate of `F` is
locally integrable, then `y ↦ L(y) (F y)` is integrable. -/
theorem integrable_clm_apply_of_locallyIntegrable {L : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ}
    (hL : Continuous L) (hLc : HasCompactSupport L) {F : (Fin d → ℝ) → Fin d → ℝ}
    (hF : ∀ j, LocallyIntegrable fun y => F y j) :
    Integrable fun y => L y (F y) := by
  have e : (fun y => L y (F y)) = fun y => ∑ j, L y (Pi.single j 1) • F y j := by
    funext y
    rw [clm_apply_eq_sum]
    simp [smul_eq_mul, mul_comm]
  rw [e]
  refine integrable_finsetSum _ fun j _ => (hF j).integrable_smul_left_of_hasCompactSupport
    (hL.clm_apply continuous_const) ?_
  exact hLc.mono' fun y hy => by
    contrapose! hy
    simp [image_eq_zero_of_notMem_tsupport hy]

/-- A `C¹` kernel vanishing outside the closed unit ball has compact support. -/
theorem hasCompactSupport_of_eq_zero_of_one_lt {κ : (Fin d → ℝ) → ℝ}
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) : HasCompactSupport κ := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1) fun z hz => ?_
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (hκ1 z (not_le.1 h))

/-- **Pointwise decomposition of the commutator error (Verified).** Let `κ` be `C¹`, vanish
outside the closed unit ball, `∫ κ = 1` and `‖Dκ‖ ≤ D₁`; let `v` have a weak Jacobian `Dv`,
`w` be measurable with `|w| ≤ U`, and `ε > 0`. Then, with `κ_ε = scaledKernel κ ε`,
`|C_{κ_ε}(w, v)(x) - w(x) div v(x)|` is at most
`U D₁ ε^{-d-1} ∫_{B(0,ε)} ‖v(x+h) - v(x) - Dv(x) h‖ dh`
`+ D₁ (∑ |Dv(x)_{ji}|) ε^{-d} ∫_{B(0,ε)} |w(x+h) - w(x)| dh`.
The first term is the Taylor remainder of `v`, the second the oscillation of `w`. -/
theorem enorm_dlCommutator_sub_le {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) (hκint : ∫ z, κ z = 1) {D1 : ℝ}
    (hD1 : ∀ z, ‖fderiv ℝ κ z‖ ≤ D1) {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv)
    {w : (Fin d → ℝ) → ℝ} (hwm : Measurable w) {U : ℝ} (hU : ∀ x, |w x| ≤ U) {ε : ℝ}
    (hε : 0 < ε) (x : Fin d → ℝ) :
    ‖dlCommutator (scaledKernel κ ε) w v x - w x * weakDiv Dv x‖ₑ ≤
      ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
          (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ) +
        ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) *
          (ENNReal.ofReal ((ε ^ d)⁻¹) * (∫⁻ h in closedBall 0 ε, ‖w (x + h) - w x‖ₑ)) := by
  have hκε : ContDiff ℝ 1 (scaledKernel κ ε) := contDiff_scaledKernel hκ ε
  have hκεc : HasCompactSupport (scaledKernel κ ε) := hasCompactSupport_scaledKernel hκ1 hε
  have hL : Continuous fun y => fderiv ℝ (scaledKernel κ ε) (x - y) :=
    (hκε.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
  have hLc : HasCompactSupport fun y => fderiv ℝ (scaledKernel κ ε) (x - y) :=
    (hκεc.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hN0 : 0 ≤ ∑ j, ∑ i, |Dv x j i| := by positivity
  have hLb : ∀ y, ‖fderiv ℝ (scaledKernel κ ε) (x - y)‖ ≤ (ε ^ d)⁻¹ * ε⁻¹ * D1 := by
    intro y
    rw [norm_fderiv_scaledKernel hκ hε]
    exact mul_le_mul_of_nonneg_left (hD1 _) (by positivity)
  have hL0 : ∀ y, y ∉ closedBall x ε → fderiv ℝ (scaledKernel κ ε) (x - y) = 0 := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    exact fderiv_scaledKernel_eq_zero hκ1 hε (by rwa [norm_sub_rev])
  have hvj : ∀ j, LocallyIntegrable fun y => v y j := fun j => (hv j j).1
  have hAc : Continuous fun y : Fin d → ℝ => Matrix.of (Dv x) *ᵥ (y - x) := by
    refine continuous_pi fun j => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hwae : AEStronglyMeasurable w volume := hwm.aestronglyMeasurable
  have hwb : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), ‖w y‖ ≤ U :=
    ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hU y
  have j1 : Integrable fun y => fderiv ℝ (scaledKernel κ ε) (x - y) (v y - v x) :=
    integrable_clm_apply_of_locallyIntegrable hL hLc (F := fun y => v y - v x) fun j => by
      exact (hvj j).sub (locallyIntegrable_const (v x j))
  have j2 : Integrable fun y => fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) :=
    integrable_clm_apply_of_locallyIntegrable hL hLc
      (F := fun y => Matrix.of (Dv x) *ᵥ (y - x)) fun j =>
        ((continuous_apply j).comp hAc).locallyIntegrable
  have i1 := j1.bdd_mul hwae hwb
  have i2 := j2.bdd_mul hwae hwb
  have i3 := j2.const_mul (w x)
  have hmom : ∫ y, fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) =
      weakDiv Dv x := by
    have e : ∀ y, fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) =
        (fun z => -fderiv ℝ (scaledKernel κ ε) z (Matrix.of (Dv x) *ᵥ z)) (x - y) := by
      intro y
      simp only
      rw [← neg_sub x y, Matrix.mulVec_neg, map_neg]
    simp_rw [e]
    rw [integral_sub_left_eq_self
        (fun z => -fderiv ℝ (scaledKernel κ ε) z (Matrix.of (Dv x) *ᵥ z)) volume x,
      integral_neg, integral_fderiv_apply_mulVec hκε hκεc, integral_scaledKernel κ hε, hκint]
    simp [weakDiv, Matrix.trace, Matrix.of_apply]
  have hdec : dlCommutator (scaledKernel κ ε) w v x - w x * weakDiv Dv x =
      (∫ y, w y * fderiv ℝ (scaledKernel κ ε) (x - y)
        (v y - v x - Matrix.of (Dv x) *ᵥ (y - x))) +
        ∫ y, (w y - w x) * fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) := by
    have eT1 : (fun y => w y * fderiv ℝ (scaledKernel κ ε) (x - y)
        (v y - v x - Matrix.of (Dv x) *ᵥ (y - x))) = fun y =>
          w y * fderiv ℝ (scaledKernel κ ε) (x - y) (v y - v x) -
            w y * fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) := by
      funext y; rw [map_sub, mul_sub]
    have eT2 : (fun y => (w y - w x) * fderiv ℝ (scaledKernel κ ε) (x - y)
        (Matrix.of (Dv x) *ᵥ (y - x))) = fun y =>
          w y * fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) -
            w x * fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x)) := by
      funext y; rw [sub_mul]
    rw [eT1, eT2, integral_sub i1 i2, integral_sub i2 i3, ← hmom, ← integral_const_mul,
      dlCommutator]
    ring
  rw [hdec]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have ht := setLIntegral_closedBall_eq_add
      (fun y => ‖v y - v x - Matrix.of (Dv x) *ᵥ (y - x)‖ₑ) x ε
    simp only [add_sub_cancel_left] at ht
    rw [← ht, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ closedBall x ε
    · rw [indicator_of_mem hy, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, Real.norm_eq_abs]
      calc |w y| * ‖fderiv ℝ (scaledKernel κ ε) (x - y) (v y - v x - Matrix.of (Dv x) *ᵥ (y - x))‖
          ≤ U * ((ε ^ d)⁻¹ * ε⁻¹ * D1 * ‖v y - v x - Matrix.of (Dv x) *ᵥ (y - x)‖) :=
            mul_le_mul (hU y) ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hLb y) (norm_nonneg _))) (norm_nonneg _) hU0
        _ = U * D1 * ((ε ^ d)⁻¹ * ε⁻¹) * ‖v y - v x - Matrix.of (Dv x) *ᵥ (y - x)‖ := by ring
    · rw [indicator_of_notMem hy, hL0 y hy]
      simp
  · refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have ht := setLIntegral_closedBall_eq_add (fun y => ‖w y - w x‖ₑ) x ε
    rw [← ht, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ closedBall x ε
    · rw [indicator_of_mem hy, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hyε : ‖y - x‖ ≤ ε := by rwa [mem_closedBall, dist_eq_norm] at hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hεε : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
      calc |w y - w x| * ‖fderiv ℝ (scaledKernel κ ε) (x - y) (Matrix.of (Dv x) *ᵥ (y - x))‖
          ≤ |w y - w x| * ((ε ^ d)⁻¹ * ε⁻¹ * D1 * ((∑ j, ∑ i, |Dv x j i|) * ε)) := by
            refine mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul (hLb y) ((norm_mulVec_le _ _).trans
                (mul_le_mul_of_nonneg_left hyε hN0)) (norm_nonneg _) (by positivity)))
              (abs_nonneg _)
        _ = D1 * (∑ j, ∑ i, |Dv x j i|) * ((ε ^ d)⁻¹ * |w y - w x|) * (ε⁻¹ * ε) := by ring
        _ = D1 * (∑ j, ∑ i, |Dv x j i|) * ((ε ^ d)⁻¹ * |w y - w x|) := by
            rw [hεε, mul_one]
    · rw [indicator_of_notMem hy, hL0 y hy]
      simp

/-- Joint measurability of the Taylor remainder `(x, h) ↦ ‖v(x+h) - v(x) - Dv(x) h‖ₑ`. -/
theorem measurable_taylor_remainder {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hvm : Measurable v) (hDm : Measurable Dv) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ‖v (p.1 + p.2) - v p.1 - Matrix.of (Dv p.1) *ᵥ p.2‖ₑ := by
  refine Measurable.enorm (((hvm.comp (measurable_fst.add measurable_snd)).sub
    (hvm.comp measurable_fst)).sub (measurable_pi_iff.2 fun j => ?_))
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.measurable_sum _ fun i _ =>
    ((hDm.eval.eval).comp measurable_fst).mul (measurable_snd.eval)

/-- `ε^{-d-1} · ε · vol(B(0, ε)) = 2^d` for the sup-norm ball in `ℝᵈ`. -/
theorem ofReal_mul_volume_closedBall {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((ε ^ d)⁻¹) * volume (closedBall (0 : Fin d → ℝ) ε) =
      ENNReal.ofReal (2 ^ d) := by
  rw [Real.volume_pi_closedBall _ hε.le, Fintype.card_fin, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow]
  field_simp

/-- **Integrated Taylor remainder at scale `ε` (Verified).** For `v` with a weak Jacobian
(Borel measurable representatives), `K` compact and `η > 0`, there is `δ > 0` with
`∫_K ε^{-d-1} ∫_{B(0,ε)} ‖v(x+h) - v(x) - Dv(x) h‖ dh dx ≤ 2^d η` for `0 < ε < δ`. -/
theorem exists_lintegral_taylor_ball_le {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {K : Set (Fin d → ℝ)} (hK : IsCompact K) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ,
      ∫⁻ x in K, ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹) *
        ∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ ≤
        ENNReal.ofReal (2 ^ d) * η := by
  obtain ⟨δ, hδ, hM⟩ := exists_lintegral_taylor_remainder_le hv hvm hDm hK hη
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  have hmeas := measurable_taylor_remainder hvm hDm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap (f := fun x h => ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ)
      hmeas.aemeasurable]
  calc ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹) * ∫⁻ h in closedBall 0 ε, ∫⁻ x in K,
        ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ
      ≤ ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹) *
          ∫⁻ _h in closedBall (0 : Fin d → ℝ) ε, ENNReal.ofReal ε * η := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_closedBall fun h hh => ?_)
        have hh' : ‖h‖ ≤ ε := by rwa [mem_closedBall, dist_zero_right] at hh
        refine (hM h (hh'.trans_lt hε.2)).trans (mul_le_mul' ?_ le_rfl)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hh'
    _ = ENNReal.ofReal (2 ^ d) * η := by
        rw [setLIntegral_const, ENNReal.ofReal_mul (by positivity [hε.1]),
          ← ofReal_mul_volume_closedBall hε.1]
        have hεε : ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε = 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε.1.le), inv_mul_cancel₀ hε.1.ne',
            ENNReal.ofReal_one]
        calc ENNReal.ofReal (ε ^ d)⁻¹ * ENNReal.ofReal ε⁻¹ *
              (ENNReal.ofReal ε * η * volume (closedBall (0 : Fin d → ℝ) ε))
            = ENNReal.ofReal (ε ^ d)⁻¹ * volume (closedBall (0 : Fin d → ℝ) ε) * η *
                (ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε) := by ring
          _ = _ := by rw [hεε, mul_one]

/-- The oscillation average `ε^{-d} ∫_{B(0,ε)} |w(x+h) - w(x)| dh` of a measurable `w`. -/
noncomputable def oscAvg (w : (Fin d → ℝ) → ℝ) (ε : ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ h in closedBall 0 ε, ‖w (x + h) - w x‖ₑ

/-- `oscAvg w ε` is measurable for measurable `w`. -/
theorem measurable_oscAvg {w : (Fin d → ℝ) → ℝ} (hwm : Measurable w) (ε : ℝ) :
    Measurable (oscAvg w ε) := by
  refine measurable_const.mul ?_
  exact Measurable.lintegral_prod_right' (f := fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
    ‖w (p.1 + p.2) - w p.1‖ₑ)
    (((hwm.comp (measurable_fst.add measurable_snd)).sub (hwm.comp measurable_fst)).enorm)

/-- `oscAvg w ε x ≤ 2 U 2^d` when `|w| ≤ U`. -/
theorem oscAvg_le {w : (Fin d → ℝ) → ℝ} {U : ℝ} (hU : ∀ x, |w x| ≤ U) {ε : ℝ} (hε : 0 < ε)
    (x : Fin d → ℝ) : oscAvg w ε x ≤ ENNReal.ofReal (2 * U * 2 ^ d) := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  calc oscAvg w ε x ≤ ENNReal.ofReal ((ε ^ d)⁻¹) *
        ∫⁻ _h in closedBall (0 : Fin d → ℝ) ε, ENNReal.ofReal (2 * U) := by
        refine mul_le_mul' le_rfl (lintegral_mono fun h => ?_)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs]
        linarith [abs_sub (w (x + h)) (w x), hU (x + h), hU x]
    _ = ENNReal.ofReal (2 * U * 2 ^ d) := by
        rw [setLIntegral_const, mul_comm (ENNReal.ofReal (2 * U)), ← mul_assoc,
          ofReal_mul_volume_closedBall hε, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **Lebesgue differentiation for the oscillation (Verified).** For measurable bounded `w`,
`oscAvg w ε x → 0` as `ε → 0⁺` for a.e. `x`. -/
theorem ae_tendsto_oscAvg {w : (Fin d → ℝ) → ℝ} (hwm : Measurable w) {U : ℝ}
    (hU : ∀ x, |w x| ≤ U) : ∀ᵐ x, Tendsto (fun ε => oscAvg w ε x) (𝓝[>] 0) (𝓝 0) := by
  have hli : LocallyIntegrable w := by
    refine fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos, ?_⟩
    refine Measure.integrableOn_of_bounded (M := U) measure_closedBall_lt_top.ne
      hwm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]; exact hU y
  filter_upwards [ae_tendsto_lintegral_closedBall_sub hli] with x hx
  refine hx.congr fun ε => ?_
  rw [oscAvg, setLIntegral_closedBall_eq_add (fun y => ‖w y - w x‖ₑ) x ε]

/-- Measurability of `x ↦ ∑_{j,i} |Dv(x)_{ji}|`. -/
theorem measurable_sum_abs {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hDm : Measurable Dv) :
    Measurable fun x => ∑ j, ∑ i, |Dv x j i| :=
  Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
    continuous_abs.measurable.comp (hDm.eval.eval)

/-- `D₁ (∑_{j,i} |Dv_{ji}|) c` is integrable on a compact set for locally integrable `Dv`. -/
theorem integrableOn_sum_abs_mul {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hDi : ∀ j i, LocallyIntegrable fun x => Dv x j i) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (D1 c : ℝ) : IntegrableOn (fun x => D1 * (∑ j, ∑ i, |Dv x j i|) * c) K := by
  refine ((integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    ((hDi j i).integrableOn_isCompact hK).abs).const_mul D1).mul_const c

/-- **Upper bound for the oscillation term (Verified).** For `ε > 0` and `|w| ≤ U`,
`∫_K D₁ |Dv| oscAvg_ε(w) ≤ ∫_K D₁ |Dv| 2U 2^d`. -/
theorem lintegral_oscAvg_mul_le {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} {D1 : ℝ}
    (hD10 : 0 ≤ D1) {w : (Fin d → ℝ) → ℝ} {U : ℝ} (hU : ∀ x, |w x| ≤ U) {K : Set (Fin d → ℝ)}
    {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x in K, ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x ≤
      ∫⁻ x in K, ENNReal.ofReal (D1 * (∑ j, ∑ i, |Dv x j i|) * (2 * U * 2 ^ d)) := by
  refine lintegral_mono fun x => ?_
  rw [ENNReal.ofReal_mul (p := D1 * ∑ j, ∑ i, |Dv x j i|) (by positivity)]
  exact mul_le_mul' le_rfl (oscAvg_le hU hε x)

/-- **The oscillation term vanishes in `L¹(K)` (Verified).** For locally integrable `Dv`,
measurable `w` with `|w| ≤ U` and compact `K`,
`∫_K D₁ |Dv(x)| oscAvg_ε(w)(x) dx → 0` as `ε → 0⁺` (dominated convergence and the Lebesgue
differentiation theorem). -/
theorem tendsto_lintegral_oscAvg_mul {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hDi : ∀ j i, LocallyIntegrable fun x => Dv x j i) (hDm : Measurable Dv) {D1 : ℝ}
    (hD10 : 0 ≤ D1) {w : (Fin d → ℝ) → ℝ} (hwm : Measurable w) {U : ℝ} (hU : ∀ x, |w x| ≤ U)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    Tendsto (fun ε => ∫⁻ x in K, ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict K)
    (l := 𝓝[>] (0 : ℝ)) (f := fun _ => 0)
    (F := fun ε x => ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x)
    (fun x => ENNReal.ofReal (D1 * (∑ j, ∑ i, |Dv x j i|) * (2 * U * 2 ^ d)))
    (Eventually.of_forall fun ε =>
      ((measurable_const.mul (measurable_sum_abs hDm)).ennreal_ofReal).mul
        (measurable_oscAvg hwm ε))
    (eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => ae_of_all _ fun x => by
      rw [ENNReal.ofReal_mul (p := D1 * ∑ j, ∑ i, |Dv x j i|) (by positivity)]
      exact mul_le_mul' le_rfl (oscAvg_le hU hε x))
    (integrableOn_sum_abs_mul hDi hK D1 _).lintegral_lt_top.ne
    (ae_restrict_of_ae ((ae_tendsto_oscAvg hwm hU).mono fun x hx => by
      simpa using ENNReal.Tendsto.const_mul hx (Or.inr ENNReal.ofReal_ne_top)))
  simpa using h

/-- **Integrated Taylor term (Verified).** For every `η > 0` there is `δ > 0` such that for
`0 < ε < δ` and `U, D₁ ≥ 0`,
`∫_K U D₁ ε^{-d-1} ∫_{B(0,ε)} ‖v(x+h) - v(x) - Dv(x)h‖ ≤ U D₁ 2^d η`. -/
theorem exists_lintegral_taylor_term_le {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) (hvm : Measurable v)
    (hDm : Measurable Dv) {K : Set (Fin d → ℝ)} (hK : IsCompact K) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∀ U D1 : ℝ, 0 ≤ U → 0 ≤ D1 →
      ∫⁻ x in K, ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
        (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ) ≤
        ENNReal.ofReal (U * D1) * (ENNReal.ofReal (2 ^ d) * η) := by
  obtain ⟨δ, hδ, h⟩ := exists_lintegral_taylor_ball_le hv hvm hDm hK hη
  refine ⟨δ, hδ, fun ε hε U D1 hU0 hD10 => ?_⟩
  calc ∫⁻ x in K, ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
        (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ)
      = ∫⁻ x in K, ENNReal.ofReal (U * D1) * (ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹) *
          ∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ) :=
        lintegral_congr fun x => by rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (U * D1) * ∫⁻ x in K, ENNReal.ofReal ((ε ^ d)⁻¹ * ε⁻¹) *
          ∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (h ε hε)

/-- **DiPerna–Lions commutator lemma in `L¹_loc` (Verified).** Let `κ` be `C¹`, vanish outside
the closed unit ball, with `∫ κ = 1`, and `κ_ε = scaledKernel κ ε`. Let `v ∈ W^{1,1}_loc` with
weak Jacobian `Dv` (Borel representatives), `w` measurable with `|w| ≤ U`, and `K` compact.
Then `∫_K |C_{κ_ε}(w, v) - w div v| → 0` as `ε → 0⁺`, where
`C_{κ_ε}(w, v)(x) = ∫ w(y) Dκ_ε(x - y)(v(y) - v(x)) dy` is `dlCommutator`. -/
theorem tendsto_lintegral_dlCommutator_sub {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) (hκint : ∫ z, κ z = 1)
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) (hDm : Measurable Dv)
    {w : (Fin d → ℝ) → ℝ} (hwm : Measurable w) {U : ℝ} (hU : ∀ x, |w x| ≤ U)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    Tendsto (fun ε => ∫⁻ x in K, ‖dlCommutator (scaledKernel κ ε) w v x - w x * weakDiv Dv x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  have hκc := hasCompactSupport_of_eq_zero_of_one_lt hκ1
  obtain ⟨D1, hD1⟩ :=
    (hκ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hκc.fderiv ℝ)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hDi : ∀ j i, LocallyIntegrable fun x => Dv x j i := fun j i => (hv j i).2.1
  have hII := tendsto_lintegral_oscAvg_mul hDi hDm hD10 hwm hU hK
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  set Cst := ENNReal.ofReal (U * D1) * ENNReal.ofReal (2 ^ d) with hCst
  have hCst' : Cst ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  obtain ⟨δ, hδ, hI⟩ := exists_lintegral_taylor_term_le hv hvm hDm hK
    (ENNReal.div_pos he2.ne' hCst')
  filter_upwards [Ioo_mem_nhdsGT hδ, hII.eventually_lt_const he2] with ε hε hε2
  calc ∫⁻ x in K, ‖dlCommutator (scaledKernel κ ε) w v x - w x * weakDiv Dv x‖ₑ
      ≤ ∫⁻ x in K, (ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
          (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ) +
          ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x) :=
        lintegral_mono fun x => enorm_dlCommutator_sub_le hκ hκ1 hκint hD1 hv hwm hU hε.1 x
    _ = (∫⁻ x in K, ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
          (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ)) +
          ∫⁻ x in K, ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x :=
        lintegral_add_right' _
          ((((measurable_const.mul (measurable_sum_abs hDm)).ennreal_ofReal).mul
            (measurable_oscAvg hwm ε)).aemeasurable)
    _ ≤ Cst * (e / 2 / Cst) + e / 2 := by
        refine add_le_add ((hI ε hε U D1 hU0 hD10).trans (le_of_eq ?_)) hε2.le
        rw [hCst, mul_assoc]
    _ ≤ e / 2 + e / 2 := add_le_add ENNReal.mul_div_le le_rfl
    _ = e := ENNReal.add_halves e

/-- **Uniform `L¹(K)` bound for the commutator error (Verified).** Under the hypotheses of
`tendsto_lintegral_dlCommutator_sub` (without fixing `w`), there are `ε₀ > 0` and a finite
`B` such that `∫_K |C_{κ_ε}(w, v) - w div v| ≤ B` for all `0 < ε < ε₀` and **all** measurable
`w` with `|w| ≤ U`. -/
theorem exists_lintegral_dlCommutator_sub_le {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) (hκint : ∫ z, κ z = 1)
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) (hvm : Measurable v) (hDm : Measurable Dv)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (U : ℝ) :
    ∃ ε₀ > 0, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ w : (Fin d → ℝ) → ℝ, Measurable w →
      (∀ x, |w x| ≤ U) →
        ∫⁻ x in K, ‖dlCommutator (scaledKernel κ ε) w v x - w x * weakDiv Dv x‖ₑ ≤ B := by
  have hκc := hasCompactSupport_of_eq_zero_of_one_lt hκ1
  obtain ⟨D1, hD1⟩ :=
    (hκ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hκc.fderiv ℝ)
  have hD10 : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0)
  have hDi : ∀ j i, LocallyIntegrable fun x => Dv x j i := fun j i => (hv j i).2.1
  obtain ⟨δ, hδ, hI⟩ := exists_lintegral_taylor_term_le hv hvm hDm hK one_pos
  refine ⟨δ, hδ, ENNReal.ofReal (U * D1) * (ENNReal.ofReal (2 ^ d) * 1) +
    ∫⁻ x in K, ENNReal.ofReal (D1 * (∑ j, ∑ i, |Dv x j i|) * (2 * U * 2 ^ d)),
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.one_ne_top),
      (integrableOn_sum_abs_mul hDi hK D1 _).lintegral_lt_top.ne⟩, fun ε hε w hwm hU => ?_⟩
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  calc ∫⁻ x in K, ‖dlCommutator (scaledKernel κ ε) w v x - w x * weakDiv Dv x‖ₑ
      ≤ ∫⁻ x in K, (ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
          (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ) +
          ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x) :=
        lintegral_mono fun x => enorm_dlCommutator_sub_le hκ hκ1 hκint hD1 hv hwm hU hε.1 x
    _ = (∫⁻ x in K, ENNReal.ofReal (U * D1 * ((ε ^ d)⁻¹ * ε⁻¹)) *
          (∫⁻ h in closedBall 0 ε, ‖v (x + h) - v x - Matrix.of (Dv x) *ᵥ h‖ₑ)) +
          ∫⁻ x in K, ENNReal.ofReal (D1 * ∑ j, ∑ i, |Dv x j i|) * oscAvg w ε x :=
        lintegral_add_right' _
          ((((measurable_const.mul (measurable_sum_abs hDm)).ennreal_ofReal).mul
            (measurable_oscAvg hwm ε)).aemeasurable)
    _ ≤ _ := add_le_add (hI ε hε U D1 hU0 hD10) (lintegral_oscAvg_mul_le hD10 hU hε.1)

end NoiseScore
end FormalizeSampling
