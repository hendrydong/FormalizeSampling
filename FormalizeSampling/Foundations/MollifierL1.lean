module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.WeakDerivative

/-!
# Scaled mollifiers, Lebesgue differentiation and `L¹` continuity of translations

Status: **Verified.** Analytic infrastructure for the `d ≥ 2` DiPerna–Lions argument on the
state space `Fin d → ℝ` (sup norm, Lebesgue `volume`).

## Main results

* `scaledKernel κ ε z = ε^{-d} κ(ε⁻¹ z)`, the rescaled kernel, with its basic properties:
  `scaledKernel_eq_zero` (support in `closedBall 0 ε` when `κ` is supported in the unit ball),
  `contDiff_scaledKernel`, `hasCompactSupport_scaledKernel`, `integral_scaledKernel`
  (`∫ κ_ε = ∫ κ`), `norm_fderiv_scaledKernel` (`‖Dκ_ε(z)‖ = ε^{-d} ε⁻¹ ‖Dκ(ε⁻¹ z)‖`) and
  `fderiv_scaledKernel_eq_zero`.
* `tendsto_lintegral_comp_add_sub`: **continuity of translations in `L¹_loc`** — for a locally
  integrable `f` and a compact `K`, `∫⁻_K ‖f(x + h) - f(x)‖ → 0` as `h → 0`. Proved by
  approximation with continuous compactly supported functions
  (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`) and dominated convergence.
* `ae_tendsto_lintegral_closedBall_sub`: **Lebesgue differentiation** in the unnormalised form
  `ε^{-d} ∫⁻_{closedBall x ε} ‖f(y) - f(x)‖ → 0` for a.e. `x`
  (from `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`).
* `ae_tendsto_scaledKernel_convolution`: for a continuous kernel supported in the unit ball
  with `∫ κ = 1` and locally integrable `f`, `κ_ε ⋆ f → f` a.e. as `ε → 0⁺`.

## Not proved here

* `L¹_loc` convergence `κ_ε ⋆ f → f` (only a.e. convergence and continuity of translations
  are proved), and density of `C^∞` in `W^{1,1}_loc`.
* Any `L^p` statement for `p ≠ 1`, maximal-function estimates, or rates of convergence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff Convolution NNReal ENNReal

namespace FormalizeSampling

variable {d : ℕ}

/-- The **rescaled kernel** `κ_ε(z) = ε^{-d} κ(ε⁻¹ z)` on `ℝᵈ`. If `κ` is supported in the unit
ball and `∫ κ = 1`, then `κ_ε` is supported in `closedBall 0 ε` and `∫ κ_ε = 1`. -/
noncomputable def scaledKernel (κ : (Fin d → ℝ) → ℝ) (ε : ℝ) (z : Fin d → ℝ) : ℝ :=
  (ε ^ d)⁻¹ * κ (ε⁻¹ • z)

/-- **Support of the scaled kernel (Verified).** If `κ` vanishes outside the closed unit ball
and `ε > 0`, then `κ_ε` vanishes outside `closedBall 0 ε`. -/
theorem scaledKernel_eq_zero {κ : (Fin d → ℝ) → ℝ} (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) {ε : ℝ}
    (hε : 0 < ε) {z : Fin d → ℝ} (hz : ε < ‖z‖) : scaledKernel κ ε z = 0 := by
  rw [scaledKernel, hκ1, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le), inv_mul_eq_div, one_lt_div hε]
  exact hz

/-- **Smoothness of the scaled kernel (Verified).** -/
theorem contDiff_scaledKernel {κ : (Fin d → ℝ) → ℝ} {n : WithTop ℕ∞} (hκ : ContDiff ℝ n κ)
    (ε : ℝ) : ContDiff ℝ n (scaledKernel κ ε) :=
  contDiff_const.mul (hκ.comp (contDiff_const_smul _))

/-- The topological support of `κ_ε` lies in `closedBall 0 ε`. -/
theorem tsupport_scaledKernel_subset {κ : (Fin d → ℝ) → ℝ} (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0)
    {ε : ℝ} (hε : 0 < ε) : tsupport (scaledKernel κ ε) ⊆ closedBall 0 ε := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (scaledKernel_eq_zero hκ1 hε (not_le.1 h))

/-- **Compact support of the scaled kernel (Verified).** -/
theorem hasCompactSupport_scaledKernel {κ : (Fin d → ℝ) → ℝ} (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0)
    {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (scaledKernel κ ε) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ε)
    ((subset_tsupport _).trans (tsupport_scaledKernel_subset hκ1 hε))

/-- **Mass of the scaled kernel (Verified).** `∫ κ_ε = ∫ κ` for `ε > 0`. -/
theorem integral_scaledKernel (κ : (Fin d → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, scaledKernel κ ε z = ∫ z, κ z := by
  simp only [scaledKernel]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun z => κ z) hε.le,
    Module.finrank_fin_fun, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- **Derivative of the scaled kernel (Verified).** For `κ ∈ C¹` and `ε > 0`,
`‖Dκ_ε(z)‖ = ε^{-d} ε⁻¹ ‖Dκ(ε⁻¹ z)‖`. -/
theorem norm_fderiv_scaledKernel {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ) {ε : ℝ}
    (hε : 0 < ε) (z : Fin d → ℝ) :
    ‖fderiv ℝ (scaledKernel κ ε) z‖ = (ε ^ d)⁻¹ * ε⁻¹ * ‖fderiv ℝ κ (ε⁻¹ • z)‖ := by
  have hc0 : 0 ≤ (ε ^ d)⁻¹ := by positivity
  have h1 : HasFDerivAt (fun z : Fin d → ℝ => ε⁻¹ • z)
      (ε⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) z :=
    (hasFDerivAt_id z).const_smul ε⁻¹
  have h2 := ((hκ.differentiable one_ne_zero _).hasFDerivAt.comp z h1).const_mul (ε ^ d)⁻¹
  have hfd : fderiv ℝ (scaledKernel κ ε) z =
      (ε ^ d)⁻¹ • (fderiv ℝ κ (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) :=
    h2.fderiv
  rw [hfd, ContinuousLinearMap.comp_smul, norm_smul, norm_smul, Real.norm_of_nonneg hc0,
    Real.norm_of_nonneg (inv_nonneg.2 hε.le), ContinuousLinearMap.comp_id]
  ring

/-- **The derivative of the scaled kernel vanishes outside `closedBall 0 ε` (Verified).** -/
theorem fderiv_scaledKernel_eq_zero {κ : (Fin d → ℝ) → ℝ} (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0)
    {ε : ℝ} (hε : 0 < ε) {z : Fin d → ℝ} (hz : ε < ‖z‖) :
    fderiv ℝ (scaledKernel κ ε) z = 0 := by
  refine fderiv_of_notMem_tsupport ℝ fun hm => ?_
  have := tsupport_scaledKernel_subset hκ1 hε hm
  rw [mem_closedBall, dist_zero_right] at this
  linarith

/-! ### Lebesgue differentiation -/

/-- **Lebesgue differentiation, unnormalised (Verified).** For a locally integrable
`f : ℝᵈ → ℝ`, for almost every `x`, `ε^{-d} ∫⁻_{closedBall x ε} ‖f(y) - f(x)‖ dy → 0` as
`ε → 0⁺` (here `closedBall` is a sup-norm cube of volume `(2ε)^d`). -/
theorem ae_tendsto_lintegral_closedBall_sub {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun ε => ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ y in closedBall x ε, ‖f y - f x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume) hf 1]
    with x hx
  have hav := hx (fun _ => x) id tendsto_id
    (eventually_mem_nhdsWithin.mono fun ε hε => by
      rw [one_mul]; exact mem_closedBall_self (le_of_lt hε))
  have hlim : Tendsto (fun ε => ENNReal.ofReal (2 ^ d * ⨍ y in closedBall x ε, ‖f y - f x‖))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hav.const_mul (2 ^ d : ℝ))
    rw [mul_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  refine hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => ?_)
  have hε : 0 < ε := hε
  have hint : Integrable (fun y => f y - f x) (volume.restrict (closedBall x ε)) :=
    ((hf.integrableOn_isCompact (isCompact_closedBall x ε)).sub (integrableOn_const
      (measure_closedBall_lt_top (x := x) (r := ε)).ne))
  symm
  dsimp only
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint, ← ENNReal.ofReal_mul (by positivity),
    setAverage_eq, Measure.real, Real.volume_pi_closedBall x hε.le, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_pow]
  congr 1
  field_simp

/-- **A.e. convergence of scaled mollifications (Verified).** Let `κ` be continuous, vanish
outside the closed unit ball and satisfy `∫ κ = 1`. For locally integrable `f`, for almost
every `x`, `(κ_ε ⋆ f)(x) → f(x)` as `ε → 0⁺`, where `κ_ε = scaledKernel κ ε`. -/
theorem ae_tendsto_scaledKernel_convolution {κ : (Fin d → ℝ) → ℝ} (hκc : Continuous κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) (hκint : ∫ z, κ z = 1) {f : (Fin d → ℝ) → ℝ}
    (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun ε => (scaledKernel κ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)
      (𝓝[>] 0) (𝓝 (f x)) := by
  have hκcs : HasCompactSupport κ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1) fun z hz => by
      rw [mem_closedBall, dist_zero_right]
      by_contra h
      exact hz (hκ1 z (not_le.1 h))
  obtain ⟨M, hM⟩ := hκc.bounded_above_of_compact_support hκcs
  filter_upwards [ae_tendsto_lintegral_closedBall_sub hf] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := ENNReal.Tendsto.const_mul hx (Or.inr (ENNReal.ofReal_ne_top (r := M)))
  rw [mul_zero] at hlim
  have hlim' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  rw [ENNReal.toReal_zero] at hlim'
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  simp only [Function.comp_apply]
  set k := scaledKernel κ ε with hk
  have hkc : Continuous k := (contDiff_scaledKernel (n := 0) (contDiff_zero.2 hκc) ε).continuous
  have hkcs : HasCompactSupport k := hasCompactSupport_scaledKernel hκ1 hε
  have hkx : Continuous fun y => k (x - y) := hkc.comp (continuous_const.sub continuous_id)
  have hkxs : HasCompactSupport fun y => k (x - y) := hkcs.comp_homeomorph (Homeomorph.subLeft x)
  have hi1 : Integrable fun y => k (x - y) * f y := by
    simpa [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hkx hkxs
  have hi2 : Integrable fun y => k (x - y) * f x :=
    (hkx.integrable_of_hasCompactSupport hkxs).mul_const _
  have hmass : ∫ y, k (x - y) = 1 := by
    rw [integral_sub_left_eq_self (fun z => k z) volume x, hk, integral_scaledKernel κ hε, hκint]
  have hrepr : (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x =
      ∫ y, k (x - y) * (f y - f x) := by
    rw [convolution_lsmul_swap]
    simp_rw [smul_eq_mul, mul_sub]
    rw [integral_sub hi1 hi2, integral_mul_const, hmass, one_mul]
  rw [hrepr]
  -- pointwise bound of the integrand
  have hbd : ∀ y, ‖k (x - y) * (f y - f x)‖ₑ ≤ (closedBall x ε).indicator
      (fun y => ENNReal.ofReal M * ENNReal.ofReal ((ε ^ d)⁻¹) * ‖f y - f x‖ₑ) y := by
    intro y
    by_cases hy : y ∈ closedBall x ε
    · rw [indicator_of_mem hy, enorm_mul]
      gcongr
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      rw [hk, scaledKernel, ← ofReal_norm, norm_mul, ← ENNReal.ofReal_mul hM0,
        Real.norm_of_nonneg (by positivity), mul_comm M]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hM _) (by positivity))
    · rw [indicator_of_notMem hy]
      have : k (x - y) = 0 := by
        rw [mem_closedBall, dist_comm, dist_eq_norm] at hy
        exact scaledKernel_eq_zero hκ1 hε (not_le.1 hy)
      simp [this]
  have h1 : ‖∫ y, k (x - y) * (f y - f x)‖ₑ ≤
      ENNReal.ofReal M * (ENNReal.ofReal ((ε ^ d)⁻¹) *
        ∫⁻ y in closedBall x ε, ‖f y - f x‖ₑ) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono hbd).trans ?_)
    rw [lintegral_indicator measurableSet_closedBall]
    rw [← mul_assoc, lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  have hfin : ENNReal.ofReal M * (ENNReal.ofReal ((ε ^ d)⁻¹) *
        ∫⁻ y in closedBall x ε, ‖f y - f x‖ₑ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
    have hint : Integrable (fun y => f y - f x) (volume.restrict (closedBall x ε)) :=
      ((hf.integrableOn_isCompact (isCompact_closedBall x ε)).sub (integrableOn_const
        (measure_closedBall_lt_top (x := x) (r := ε)).ne))
    exact hint.2.ne
  rw [← ofReal_norm] at h1
  have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
  exact this

/-! ### Continuity of translations in `L¹_loc` -/

/-- **Translations of continuous compactly supported functions (Verified).** For a continuous
compactly supported `φ`, `∫⁻ ‖φ(x + h) - φ(x)‖ → 0` as `h → 0`. -/
theorem tendsto_lintegral_comp_add_sub_of_continuous {φ : (Fin d → ℝ) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun h => ∫⁻ x, ‖φ (x + h) - φ x‖ₑ) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  set S := cthickening 1 (tsupport φ) with hS
  have hSc : IsCompact S := hφc.isCompact.cthickening
  have h0 : ∫⁻ _ : Fin d → ℝ, (0 : ℝ≥0∞) = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (S.indicator fun _ => ENNReal.ofReal (2 * C)) (Eventually.of_forall fun h => ?_) ?_ ?_ ?_
  · exact ((hφ.comp (continuous_id.add continuous_const)).sub hφ).enorm.measurable
  · filter_upwards [closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
    refine Eventually.of_forall fun x => ?_
    rw [mem_closedBall, dist_zero_right] at hh
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans ?_)
      linarith [hC (x + h), hC x]
    · rw [indicator_of_notMem hx]
      have hx0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hm =>
        hx (self_subset_cthickening _ hm)
      have hxh : φ (x + h) = 0 := image_eq_zero_of_notMem_tsupport fun hm => by
        refine hx (mem_cthickening_of_dist_le x (x + h) 1 _ hm ?_)
        rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
        exact hh
      simp [hx0, hxh]
  · rw [lintegral_indicator_const hSc.measurableSet]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSc.measure_lt_top.ne
  · refine Eventually.of_forall fun x => ?_
    have hc : Continuous fun h : Fin d → ℝ => ‖φ (x + h) - φ x‖ₑ :=
      ((hφ.comp (continuous_const.add continuous_id)).sub continuous_const).enorm
    have := hc.tendsto 0
    simpa using this

/-- **Translations of integrable functions (Verified).** For integrable `g : ℝᵈ → ℝ`,
`∫⁻ ‖g(x + h) - g(x)‖ → 0` as `h → 0` (continuity of translations in `L¹`). -/
theorem tendsto_lintegral_comp_add_sub_of_integrable {g : (Fin d → ℝ) → ℝ}
    (hg : Integrable g) :
    Tendsto (fun h => ∫⁻ x, ‖g (x + h) - g x‖ₑ) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : η / 3 ≠ 0 := by
    rw [ne_eq, ENNReal.div_eq_zero_iff]; simp [hη.ne']
  obtain ⟨φ, hφc, hφn, hφ, -⟩ :=
    (memLp_one_iff_integrable.2 hg).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.one_ne_top
      hη3
  rw [eLpNorm_one_eq_lintegral_enorm (hg.aestronglyMeasurable.sub hφ.aestronglyMeasurable)]
    at hφn
  have hlim := tendsto_lintegral_comp_add_sub_of_continuous hφ hφc
  have hev := (ENNReal.tendsto_nhds_zero.1 hlim) (η / 3) (pos_iff_ne_zero.2 hη3)
  filter_upwards [hev] with h hh
  have hφm : Measurable φ := hφ.measurable
  have hgm := hg.aestronglyMeasurable.aemeasurable
  calc ∫⁻ x, ‖g (x + h) - g x‖ₑ
      ≤ ∫⁻ x, (‖(g - φ) (x + h)‖ₑ + ‖φ (x + h) - φ x‖ₑ + ‖(g - φ) x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        have : g (x + h) - g x =
            (g - φ) (x + h) + (φ (x + h) - φ x) - (g - φ) x := by
          simp only [Pi.sub_apply]; ring
        rw [this]
        exact (enorm_sub_le).trans (by gcongr; exact enorm_add_le _ _)
    _ = (∫⁻ x, ‖(g - φ) (x + h)‖ₑ) + (∫⁻ x, ‖φ (x + h) - φ x‖ₑ) +
          ∫⁻ x, ‖(g - φ) x‖ₑ := by
        rw [lintegral_add_right' _ (hgm.sub hφm.aemeasurable).enorm,
          lintegral_add_right' _
            (by fun_prop : AEMeasurable (fun a => ‖φ (a + h) - φ a‖ₑ) volume)]
    _ ≤ η / 3 + η / 3 + η / 3 := by
        have htr : ∫⁻ x, ‖(g - φ) (x + h)‖ₑ = ∫⁻ x, ‖(g - φ) x‖ₑ :=
          lintegral_add_right_eq_self (fun x => ‖(g - φ) x‖ₑ) h
        rw [htr]
        gcongr
    _ = η := ENNReal.add_thirds η

/-- **Continuity of translations in `L¹_loc` (Verified).** For a locally integrable
`f : ℝᵈ → ℝ` and a compact set `K`, `∫⁻_K ‖f(x + h) - f(x)‖ → 0` as `h → 0`. -/
theorem tendsto_lintegral_comp_add_sub {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    Tendsto (fun h => ∫⁻ x in K, ‖f (x + h) - f x‖ₑ) (𝓝 0) (𝓝 0) := by
  set K' := cthickening 1 K with hK'
  have hK'c : IsCompact K' := hK.cthickening
  set g := K'.indicator f with hg
  have hgi : Integrable g :=
    (integrable_indicator_iff hK'c.measurableSet).2 (hf.integrableOn_isCompact hK'c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_lintegral_comp_add_sub_of_integrable hgi) (Eventually.of_forall fun _ => bot_le)
    ?_
  filter_upwards [closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
  rw [mem_closedBall, dist_zero_right] at hh
  calc ∫⁻ x in K, ‖f (x + h) - f x‖ₑ = ∫⁻ x in K, ‖g (x + h) - g x‖ₑ := by
        refine setLIntegral_congr_fun_ae hK.measurableSet (Eventually.of_forall fun x hx => ?_)
        have hx' : x ∈ K' := self_subset_cthickening _ hx
        have hxh : x + h ∈ K' := by
          refine mem_cthickening_of_dist_le (x + h) x 1 K hx ?_
          rw [dist_eq_norm, add_sub_cancel_left]
          exact hh
        rw [hg, indicator_of_mem hx', indicator_of_mem hxh]
    _ ≤ ∫⁻ x, ‖g (x + h) - g x‖ₑ := setLIntegral_le_lintegral _ _

end FormalizeSampling
