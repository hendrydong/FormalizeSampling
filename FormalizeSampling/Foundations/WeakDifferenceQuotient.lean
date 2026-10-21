module

public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.WeakDerivative

/-!
# Difference quotients of `W^{1,1}_loc` functions

Status: **Verified.** For a function `f : ℝᵈ → ℝ` with locally integrable weak partial
derivatives `∂ᵢ f = gᵢ` (Borel measurable representatives), the **difference-quotient
identity** along a fixed increment `h`

  `f(x + h) - f(x) = ∑ᵢ hᵢ ∫₀¹ gᵢ(x + s h) ds`   for a.e. `x`,

and the resulting `L¹(K)` estimate of the first-order Taylor remainder

  `∫_K |f(x + h) - f(x) - ∑ᵢ hᵢ gᵢ(x)| dx ≤ ∑ᵢ |hᵢ| ∫₀¹ ∫_K |gᵢ(x + s h) - gᵢ(x)| dx ds`.

The identity is proved distributionally: tested against `φ ∈ C_c^∞`, the left side becomes
`∫ f(y) (φ(y - h) - φ(y)) dy`, the fundamental theorem of calculus along the segment writes
`φ(y - h) - φ(y) = -∑ᵢ hᵢ ∫₀¹ ∂ᵢφ(y - s h) ds`, Fubini exchanges the integrals, the weak
derivative is applied to the translated test functions `φ(· - s h)`, and uniqueness of
locally integrable functions with equal test integrals
(`ae_eq_of_integral_contDiff_smul_eq`) concludes.

## Main results

* `ae_sub_eq_sum_intervalIntegral_of_hasWeakPartialDeriv`: the a.e. identity above.
* `lintegral_sub_sub_le_of_hasWeakPartialDeriv`: the `L¹(K)` remainder estimate (in
  `ℝ≥0∞`, no integrability side conditions).

## Not proved here

* Absolute continuity on (almost every) line, i.e. a pointwise representative for which the
  identity holds for **all** `x` and all `h`; only the a.e.-in-`x` statement for each fixed
  `h` is proved.
* The convergence of the right-hand side of the estimate to `0` as `h → 0` (continuity of
  translations in `L¹`); this is combined with the estimate elsewhere.
-/

public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff NNReal ENNReal

namespace FormalizeSampling

variable {d : ℕ}

/-- The set swept by a compact set `K` translated along the segment `[0, 1] h`. -/
private def segSet (K : Set (Fin d → ℝ)) (h : Fin d → ℝ) : Set (Fin d → ℝ) :=
  (fun p : ℝ × (Fin d → ℝ) => p.2 + p.1 • h) '' (Icc (0 : ℝ) 1 ×ˢ K)

private theorem isCompact_segSet {K : Set (Fin d → ℝ)} (hK : IsCompact K) (h : Fin d → ℝ) :
    IsCompact (segSet K h) :=
  (isCompact_Icc.prod hK).image (by fun_prop)

private theorem add_smul_mem_segSet {K : Set (Fin d → ℝ)} {h : Fin d → ℝ} {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {x : Fin d → ℝ} (hx : x ∈ K) : x + s • h ∈ segSet K h :=
  ⟨(s, x), ⟨hs, hx⟩, rfl⟩

/-- Integrability on `(0, 1] × ℝᵈ` from a uniform bound on the inner `L¹` norms. -/
private theorem integrable_prod_Ioc_of_lintegral_le {F : ℝ × (Fin d → ℝ) → ℝ}
    (hF : AEStronglyMeasurable F ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume))
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hb : ∀ s ∈ Ioc (0 : ℝ) 1, ∫⁻ x, ‖F (s, x)‖ₑ ≤ C) :
    Integrable F ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
  refine ⟨hF, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hF.enorm]
  calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x, ‖F (s, x)‖ₑ ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, C :=
        setLIntegral_mono' measurableSet_Ioc hb
    _ < ⊤ := by
      rw [setLIntegral_const, Real.volume_Ioc]
      simpa using hC.lt_top

/-- Bound for integrands of the form `g(x + s h) ψ(x)` with `ψ` bounded and vanishing
outside `K`. -/
private theorem lintegral_comp_add_mul_le {g ψ : (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) {M : ℝ} (hψ : ∀ x, |ψ x| ≤ M) (hψK : ∀ x, x ∉ K → ψ x = 0)
    (h : Fin d → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫⁻ x, ‖g (x + s • h) * ψ x‖ₑ ≤ ENNReal.ofReal M * ∫⁻ y in segSet K h, ‖g y‖ₑ := by
  have hL := (isCompact_segSet hK h).measurableSet
  calc ∫⁻ x, ‖g (x + s • h) * ψ x‖ₑ
      ≤ ∫⁻ x, (segSet K h).indicator (fun y => ENNReal.ofReal M * ‖g y‖ₑ) (x + s • h) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · rw [indicator_of_mem (add_smul_mem_segSet hs hx), enorm_mul, mul_comm,
            Real.enorm_eq_ofReal_abs (ψ x)]
          gcongr
          exact hψ x
        · simp [hψK x hx]
    _ = ∫⁻ y, (segSet K h).indicator (fun y => ENNReal.ofReal M * ‖g y‖ₑ) y :=
        lintegral_add_right_eq_self _ (s • h)
    _ = ENNReal.ofReal M * ∫⁻ y in segSet K h, ‖g y‖ₑ := by
        rw [lintegral_indicator hL, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Bound for integrands of the form `ψ(y - s h) f(y)` with `ψ` bounded and vanishing
outside `K`. -/
private theorem lintegral_comp_sub_mul_le {f ψ : (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) {M : ℝ} (hψ : ∀ x, |ψ x| ≤ M) (hψK : ∀ x, x ∉ K → ψ x = 0)
    (h : Fin d → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫⁻ y, ‖ψ (y - s • h) * f y‖ₑ ≤ ENNReal.ofReal M * ∫⁻ y in segSet K h, ‖f y‖ₑ := by
  have hL := (isCompact_segSet hK h).measurableSet
  calc ∫⁻ y, ‖ψ (y - s • h) * f y‖ₑ
      ≤ ∫⁻ y, (segSet K h).indicator (fun y => ENNReal.ofReal M * ‖f y‖ₑ) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y - s • h ∈ K
        · have hyL : y ∈ segSet K h := by
            have := add_smul_mem_segSet (h := h) hs hy
            simpa using this
          rw [indicator_of_mem hyL, enorm_mul, Real.enorm_eq_ofReal_abs (ψ _)]
          gcongr
          exact hψ _
        · simp [hψK _ hy]
    _ = ENNReal.ofReal M * ∫⁻ y in segSet K h, ‖f y‖ₑ := by
        rw [lintegral_indicator hL, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Product integrability of `(s, x) ↦ g(x + s h) ψ(x)` on `(0, 1] × ℝᵈ`. -/
private theorem integrable_prod_comp_add_mul {g ψ : (Fin d → ℝ) → ℝ} (hg : Measurable g)
    (hgl : LocallyIntegrable g) (hψm : Measurable ψ) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    {M : ℝ} (hψ : ∀ x, |ψ x| ≤ M) (hψK : ∀ x, x ∉ K → ψ x = 0) (h : Fin d → ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (x : Fin d → ℝ) => g (x + s • h) * ψ x)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
  refine integrable_prod_Ioc_of_lintegral_le ?_ (C := ENNReal.ofReal M *
    ∫⁻ y in segSet K h, ‖g y‖ₑ) ?_ fun s hs =>
      lintegral_comp_add_mul_le hK hψ hψK h (Ioc_subset_Icc_self hs)
  · exact ((hg.comp (by fun_prop)).mul (hψm.comp measurable_snd)).aestronglyMeasurable
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hgl.integrableOn_isCompact (isCompact_segSet hK h)).2.ne

/-- The partial derivatives of a smooth compactly supported function: continuity, bound,
vanishing outside the topological support. -/
private theorem partialDeriv_props {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (i : Fin d) :
    Continuous (partialDeriv i φ) ∧ HasCompactSupport (partialDeriv i φ) ∧
      ∀ y, y ∉ tsupport φ → partialDeriv i φ y = 0 := by
  have hc : Continuous (partialDeriv i φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h0 : ∀ y, y ∉ tsupport φ → partialDeriv i φ y = 0 := fun y hy => by
    simp [partialDeriv, fderiv_of_notMem_tsupport ℝ hy]
  exact ⟨hc, HasCompactSupport.intro hφc h0, h0⟩

/-- Fundamental theorem of calculus along a segment for a smooth `φ`. -/
private theorem sub_eq_neg_sum_intervalIntegral {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (h y : Fin d → ℝ) :
    φ (y - h) - φ y = -∑ i, h i * ∫ s in (0 : ℝ)..1, partialDeriv i φ (y - s • h) := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => φ (y - s • h))
      (fderiv ℝ φ (y - s • h) (-h)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y - s • h) (-h) s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_sub y
    exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s h1
  have hcont : Continuous fun s : ℝ => fderiv ℝ φ (y - s • h) (-h) :=
    ((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, sub_zero] at hftc
  have hexp : ∀ z, fderiv ℝ φ z (-h) = -∑ i, h i * partialDeriv i φ z := by
    intro z
    have hsum : h = ∑ i, h i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hsum]
    simp [map_sum, map_smul, partialDeriv]
  rw [← hftc]
  simp_rw [hexp]
  have hci : ∀ i, Continuous fun s : ℝ => partialDeriv i φ (y - s • h) := fun i =>
    ((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum fun i _ =>
    ((hci i).const_mul (h i)).intervalIntegrable 0 1]
  simp_rw [intervalIntegral.integral_const_mul]

/-- **Difference-quotient identity for `W^{1,1}_loc` (Verified).** Let `f : ℝᵈ → ℝ` and
`gᵢ` be Borel measurable with `gᵢ` a weak `i`-th partial derivative of `f` for every `i`.
Then for every increment `h`, for almost every `x`,
`f(x + h) - f(x) = ∑ᵢ hᵢ ∫₀¹ gᵢ(x + s h) ds`. -/
theorem ae_sub_eq_sum_intervalIntegral_of_hasWeakPartialDeriv {f : (Fin d → ℝ) → ℝ}
    {g : Fin d → (Fin d → ℝ) → ℝ} (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, HasWeakPartialDeriv f i (g i)) (h : Fin d → ℝ) :
    ∀ᵐ x, f (x + h) - f x = ∑ i, h i * ∫ s in (0 : ℝ)..1, g i (x + s • h) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i₀⟩⟩
  · exact Eventually.of_forall fun x => by simp [Subsingleton.elim h 0]
  have hfl : LocallyIntegrable f := (hfg i₀).1
  have hgl : ∀ i, LocallyIntegrable (g i) := fun i => (hfg i).2.1
  set G : Fin d → (Fin d → ℝ) → ℝ := fun i x => ∫ s in (0 : ℝ)..1, g i (x + s • h) with hG
  have hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := Set.uIoc_of_le zero_le_one
  -- integrals in `s` of the product integrands
  have hGψ : ∀ i (ψ : (Fin d → ℝ) → ℝ), ∀ x,
      ∫ s, g i (x + s • h) * ψ x ∂(volume.restrict (Ioc (0 : ℝ) 1)) = G i x * ψ x := by
    intro i ψ x
    simp only [hG]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_mul_const]
  -- local integrability of `G i`
  have hGl : ∀ i, LocallyIntegrable (G i) := by
    intro i
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    have hint := (integrable_prod_comp_add_mul (hg i) (hgl i)
      (measurable_const.indicator hK.measurableSet) hK (M := 1)
      (ψ := K.indicator fun _ => (1 : ℝ))
      (fun x => by by_cases hx : x ∈ K <;> simp [hx])
      (fun x hx => by simp [hx]) h).integral_prod_right
    simp_rw [Function.uncurry_apply_pair, hGψ] at hint
    rw [← integrable_indicator_iff hK.measurableSet]
    refine hint.congr (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K <;> simp [hx]
  have hfh : LocallyIntegrable fun x => f (x + h) := by
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    have hK' : IsCompact ((fun x => x + h) '' K) := hK.image (by fun_prop)
    have hi : Integrable (((fun x => x + h) '' K).indicator f) :=
      (integrable_indicator_iff hK'.measurableSet).2 (hfl.integrableOn_isCompact hK')
    refine (hi.comp_add_right h).integrableOn.congr_fun (fun x hx => ?_) hK.measurableSet
    exact indicator_of_mem (mem_image_of_mem _ hx) f
  have hlhs : LocallyIntegrable fun x => f (x + h) - f x := hfh.sub hfl
  have hrhs : LocallyIntegrable fun x => ∑ i, h i * G i x := by
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    exact integrable_finsetSum _ fun i _ =>
      ((hGl i).integrableOn_isCompact hK).const_mul (h i)
  refine ae_eq_of_integral_contDiff_smul_eq hlhs hrhs fun φ hφ hφc => ?_
  simp only [smul_eq_mul]
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hφK : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  -- Step 1: change of variables on the left
  have hφh : Continuous fun y => φ (y - h) := hφ.continuous.comp (by fun_prop)
  have hφhc : HasCompactSupport fun y => φ (y - h) :=
    hφc.comp_homeomorph (Homeomorph.subRight h)
  have I0 : Integrable fun y => φ (y - h) * f y := by
    simpa [smul_eq_mul] using hfl.integrable_smul_left_of_hasCompactSupport hφh hφhc
  have I1 : Integrable fun x => φ x * f (x + h) := by
    simpa using I0.comp_add_right h
  have I2 : Integrable fun x => φ x * f x := by
    simpa [smul_eq_mul] using hfl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have step1 : ∫ x, φ x * (f (x + h) - f x) = ∫ y, (φ (y - h) - φ y) * f y := by
    simp_rw [mul_sub, sub_mul]
    rw [integral_sub I1 I2, integral_sub I0 I2]
    congr 1
    rw [← integral_add_right_eq_self (fun y => φ (y - h) * f y) h]
    simp
  -- Step 2: FTC along the segment and splitting the sum
  set I : Fin d → (Fin d → ℝ) → ℝ :=
    fun i y => ∫ s in (0 : ℝ)..1, partialDeriv i φ (y - s • h) with hI
  have hpd := partialDeriv_props hφ hφc
  have hIc : ∀ i, Continuous (I i) := fun i =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y s => partialDeriv i φ (y - s • h))
      ((hpd i).1.comp (by fun_prop)) 0 1
  have hIs : ∀ i, HasCompactSupport (I i) := by
    intro i
    refine HasCompactSupport.intro (isCompact_segSet hφc h) fun y hy => ?_
    rw [hI]
    simp only
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · simp
    · rw [uIcc_of_le zero_le_one] at hs
      refine (hpd i).2.2 _ fun hm => hy ?_
      simpa using add_smul_mem_segSet (h := h) hs hm
  have hIf : ∀ i, Integrable fun y => I i y * f y := fun i => by
    simpa [smul_eq_mul] using hfl.integrable_smul_left_of_hasCompactSupport (hIc i) (hIs i)
  have step2 : ∫ y, (φ (y - h) - φ y) * f y = -∑ i, h i * ∫ y, I i y * f y := by
    simp_rw [sub_eq_neg_sum_intervalIntegral hφ h]
    change ∫ y, (-∑ i, h i * I i y) * f y = _
    simp_rw [neg_mul, Finset.sum_mul, mul_assoc]
    rw [integral_neg, integral_finsetSum _ fun i _ => (hIf i).const_mul (h i)]
    simp_rw [integral_const_mul]
  -- Step 3: Fubini and the weak derivative for each `i`
  have step3 : ∀ i, ∫ y, I i y * f y = -∫ x, G i x * φ x := by
    intro i
    obtain ⟨Mi, hMi⟩ := (hpd i).1.bounded_above_of_compact_support (hpd i).2.1
    have hint1 : Integrable (Function.uncurry fun (s : ℝ) (y : Fin d → ℝ) =>
        partialDeriv i φ (y - s • h) * f y)
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
      rw [hIoc]
      refine integrable_prod_Ioc_of_lintegral_le ?_ (C := ENNReal.ofReal Mi *
        ∫⁻ y in segSet (tsupport φ) h, ‖f y‖ₑ) ?_ fun s hs =>
          lintegral_comp_sub_mul_le hφc (fun x => by simpa using hMi x) (hpd i).2.2 h
            (Ioc_subset_Icc_self hs)
      · exact (((hpd i).1.comp (by fun_prop)).measurable.mul
          (hf.comp measurable_snd)).aestronglyMeasurable
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (hfl.integrableOn_isCompact (isCompact_segSet hφc h)).2.ne
    have hint2 := integrable_prod_comp_add_mul (hg i) (hgl i) hφ.continuous.measurable hφc
      (fun x => by simpa using hM x) hφK h
    have e1 : ∫ y, I i y * f y = ∫ s in (0 : ℝ)..1, ∫ y, partialDeriv i φ (y - s • h) * f y := by
      rw [intervalIntegral_integral_swap hint1]
      simp_rw [hI, intervalIntegral.integral_mul_const]
    have e2 : ∀ s : ℝ, ∫ y, partialDeriv i φ (y - s • h) * f y =
        -∫ x, g i (x + s • h) * φ x := by
      intro s
      have hs1 : ContDiff ℝ ∞ fun y => φ (y - s • h) := hφ.comp (contDiff_id.sub contDiff_const)
      have hs2 : HasCompactSupport fun y => φ (y - s • h) :=
        hφc.comp_homeomorph (Homeomorph.subRight (s • h))
      have hw := (hfg i).2.2 _ hs1 hs2
      have hpd' : ∀ y, partialDeriv i (fun y => φ (y - s • h)) y =
          partialDeriv i φ (y - s • h) := fun y => by
        simp only [partialDeriv]
        rw [fderiv_comp_sub (f := φ) (s • h)]
      simp_rw [hpd'] at hw
      simp_rw [mul_comm (partialDeriv i φ _)]
      rw [hw, ← integral_add_right_eq_self (fun y => g i y * φ (y - s • h)) (s • h)]
      simp
    have e3 : ∫ s in (0 : ℝ)..1, ∫ x, g i (x + s • h) * φ x = ∫ x, G i x * φ x := by
      have hint2' : Integrable (Function.uncurry fun (s : ℝ) (x : Fin d → ℝ) =>
          g i (x + s • h) * φ x) ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
        rw [hIoc]; exact hint2
      rw [intervalIntegral_integral_swap hint2']
      simp_rw [hG, intervalIntegral.integral_mul_const]
    rw [e1]
    simp_rw [e2]
    rw [intervalIntegral.integral_neg, e3]
  have hGφ : ∀ i, Integrable fun x => G i x * φ x := by
    intro i
    have := (integrable_prod_comp_add_mul (hg i) (hgl i) hφ.continuous.measurable hφc
      (fun x => by simpa using hM x) hφK h).integral_prod_right
    simp_rw [Function.uncurry_apply_pair, hGψ] at this
    exact this
  rw [step1, step2]
  simp_rw [step3, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => by
    simpa [mul_comm, mul_left_comm] using (hGφ i).const_mul (h i)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_neg, neg_neg, ← integral_const_mul]
  congr 1
  ext x
  ring

/-- `‖∫₀¹ F - c‖ₑ ≤ ∫⁻_{(0,1]} ‖F - c‖ₑ`, with no integrability assumption on `F` (if `F`
is not integrable the right side is `∞`). -/
private theorem enorm_intervalIntegral_sub_le {F : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (Ioc (0 : ℝ) 1))) (c : ℝ) :
    ‖(∫ s in (0 : ℝ)..1, F s) - c‖ₑ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ‖F s - c‖ₑ := by
  have hc : IntegrableOn (fun _ : ℝ => c) (Ioc (0 : ℝ) 1) :=
    (continuous_const (y := c)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  by_cases hi : IntegrableOn F (Ioc (0 : ℝ) 1)
  · have e : (∫ s in (0 : ℝ)..1, F s) - c = ∫ s in Ioc (0 : ℝ) 1, (F s - c) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_sub hi hc, setIntegral_const]
      simp
    rw [e]
    exact enorm_integral_le_lintegral_enorm _
  · have hnf : ¬ HasFiniteIntegral (fun s => F s - c) (volume.restrict (Ioc (0 : ℝ) 1)) := by
      intro hfin
      apply hi
      have hI : Integrable (fun s => F s - c) (volume.restrict (Ioc (0 : ℝ) 1)) :=
        ⟨hF.sub aestronglyMeasurable_const, hfin⟩
      exact (hI.add hc).congr (Eventually.of_forall fun s => by simp)
    rw [HasFiniteIntegral, not_lt, top_le_iff] at hnf
    rw [hnf]
    exact le_top

/-- **`L¹(K)` estimate of the first-order remainder (Verified).** Let `f, gᵢ : ℝᵈ → ℝ` be
Borel measurable with `gᵢ` a weak `i`-th partial derivative of `f`. Then for every set `K`
and increment `h`,
`∫_K |f(x + h) - f(x) - ∑ᵢ hᵢ gᵢ(x)| dx ≤ ∑ᵢ |hᵢ| ∫_{(0,1]} ∫_K |gᵢ(x + s h) - gᵢ(x)| dx ds`
(lower Lebesgue integrals in `ℝ≥0∞`). -/
theorem lintegral_sub_sub_le_of_hasWeakPartialDeriv {f : (Fin d → ℝ) → ℝ}
    {g : Fin d → (Fin d → ℝ) → ℝ} (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, HasWeakPartialDeriv f i (g i)) (K : Set (Fin d → ℝ)) (h : Fin d → ℝ) :
    ∫⁻ x in K, ‖f (x + h) - f x - ∑ i, h i * g i x‖ₑ ≤
      ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, ‖g i (x + s • h) - g i x‖ₑ := by
  have hae := ae_sub_eq_sum_intervalIntegral_of_hasWeakPartialDeriv hf hg hfg h
  have hpt : ∀ᵐ x, ‖f (x + h) - f x - ∑ i, h i * g i x‖ₑ ≤
      ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ‖g i (x + s • h) - g i x‖ₑ := by
    filter_upwards [hae] with x hx
    rw [hx, ← Finset.sum_sub_distrib]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← mul_sub, enorm_mul]
    gcongr
    exact enorm_intervalIntegral_sub_le
      ((hg i).comp (by fun_prop : Measurable fun s : ℝ => x + s • h)).aestronglyMeasurable _
  have hm : ∀ i, Measurable fun p : (Fin d → ℝ) × ℝ => ‖g i (p.1 + p.2 • h) - g i p.1‖ₑ :=
    fun i => (((hg i).comp (by fun_prop : Measurable fun p : (Fin d → ℝ) × ℝ =>
      p.1 + p.2 • h)).sub ((hg i).comp measurable_fst)).enorm
  calc ∫⁻ x in K, ‖f (x + h) - f x - ∑ i, h i * g i x‖ₑ
      ≤ ∫⁻ x in K, ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ‖g i (x + s • h) - g i x‖ₑ :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ∑ i, ‖h i‖ₑ * ∫⁻ x in K, ∫⁻ s in Ioc (0 : ℝ) 1, ‖g i (x + s • h) - g i x‖ₑ := by
        rw [lintegral_finsetSum _ fun i _ => ((hm i).lintegral_prod_right').const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul _ (hm i).lintegral_prod_right']
    _ = ∑ i, ‖h i‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in K, ‖g i (x + s • h) - g i x‖ₑ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_lintegral_swap (hm i).aemeasurable]

end FormalizeSampling
