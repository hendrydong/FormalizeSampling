module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Prékopa–Leindler inequality on `Fin d → ℝ`

Status: **Verified** (no named hypothesis).

For `t ∈ (0, 1)` and measurable `u, v, w : (Fin d → ℝ) → ℝ≥0∞` with
`u(x)^t v(y)^{1-t} ≤ w(t x + (1 - t) y)` for all `x, y`, the Lebesgue integrals satisfy
`(∫u)^t (∫v)^{1-t} ≤ ∫w`. Mathlib (at the pinned version) has neither Prékopa–Leindler nor
Brunn–Minkowski, so both are proved here from scratch.

Route.
1. One-dimensional Brunn–Minkowski for compact sets: with `p = t sup K + (1-t) inf L`, the set
   `t K + (1-t) inf L ⊆ (-∞, p]` and `t sup K + (1-t) L ⊆ [p, ∞)` are translated dilates inside
   `S`, meeting in at most `{p}`. Inner regularity of Lebesgue measure extends this to
   measurable sets.
2. Normalised 1D Prékopa–Leindler (`u, v ≤ 1` with supremum `1`): layer-cake formula
   (`lintegral_eq_lintegral_meas_lt`) and Brunn–Minkowski on the superlevel sets
   `{u > r}, {v > r}` (nonempty for `r < 1`), whose combination lies in `{w > r}`.
3. General 1D case: divide by the suprema, weighted AM–GM, then truncate `u ⊓ n` and pass to the
   limit by monotone convergence.
4. `d` dimensions: induction on `d`, splitting off the first coordinate with
   `MeasurableEquiv.piFinSuccAbove` (measure preserving) and Tonelli; the slice integrals satisfy
   the 1D hypothesis by the induction hypothesis.

## Main results

* `brunnMinkowski_one`: `t |A| + (1 - t) |B| ≤ |S|` for nonempty measurable `A, B ⊆ ℝ` and
  `S ⊇ t A + (1 - t) B`.
* `prekopaLeindler_one`: Prékopa–Leindler on `ℝ` (`ℝ≥0∞`-valued functions).
* `prekopa_leindler`: Prékopa–Leindler on `Fin d → ℝ` (`ℝ≥0∞`-valued functions).
* `prekopa_leindler_real`: the same for nonnegative real functions and Bochner integrals.

## Not proved here

* Brunn–Minkowski in dimension `d ≥ 2` (it follows from `prekopa_leindler` with indicator
  functions, giving the multiplicative form `|t A + (1-t) B| ≥ |A|^t |B|^{1-t}` for measurable
  `t A + (1-t) B`, but this corollary is not stated).
* Versions with essential suprema or with `w` only satisfying the hypothesis almost everywhere.
* Log-concavity of marginals of log-concave densities (an immediate consequence, not stated).
* Equality cases and the reverse / functional Blaschke–Santaló forms.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace FormalizeSampling.PrekopaLeindler

/-- Volume of a translated dilate in `ℝ`: `|c + t • s| = t |s|` for `t ≥ 0`. -/
theorem volume_vadd_smul (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (s : Set ℝ) :
    volume (c +ᵥ t • s) = ENNReal.ofReal t * volume s := by
  rw [measure_vadd, Measure.addHaar_smul_of_nonneg _ ht]
  simp

/-- One-dimensional Brunn–Minkowski for nonempty compact sets. -/
theorem brunnMinkowski_one_compact {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {K L S : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hS : ∀ a ∈ K, ∀ b ∈ L, t * a + (1 - t) * b ∈ S) :
    ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L ≤ volume S := by
  set p := t * sSup K + (1 - t) * sInf L
  set X := (1 - t) * sInf L +ᵥ t • K
  set Y := t * sSup K +ᵥ (1 - t) • L
  have hX : X ⊆ Iic p := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have := le_csSup hK.bddAbove hk
    simp only [vadd_eq_add, smul_eq_mul, mem_Iic, p]
    nlinarith
  have hY : Y ⊆ Ici p := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have := csInf_le hL.bddBelow hl
    simp only [vadd_eq_add, smul_eq_mul, mem_Ici, p]
    nlinarith
  have hXS : X ⊆ S := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have := hS k hk _ (hL.sInf_mem hLne)
    simpa [add_comm] using this
  have hYS : Y ⊆ S := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    simpa using hS _ (hK.sSup_mem hKne) l hl
  have hYm : MeasurableSet Y := ((hL.smul (1 - t)).vadd _).measurableSet
  calc ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L
      = volume X + volume Y := by
        rw [volume_vadd_smul _ ht0, volume_vadd_smul _ (sub_nonneg.2 ht1)]
    _ = volume (X ∪ Y) + volume (X ∩ Y) := (measure_union_add_inter X hYm).symm
    _ = volume (X ∪ Y) := by
        have : X ∩ Y ⊆ {p} := fun z hz => le_antisymm (hX hz.1) (hY hz.2)
        rw [measure_mono_null this (measure_singleton p), add_zero]
    _ ≤ volume S := measure_mono (union_subset hXS hYS)

/-- Inner regularity in the form used below: a bound `c + a |K| ≤ M` for all compact `K ⊆ s`
gives `c + a |s| ≤ M`. -/
theorem add_mul_volume_le_of_compact {s : Set ℝ} (hs : MeasurableSet s) {c a M : ℝ≥0∞}
    (h : ∀ K ⊆ s, IsCompact K → c + a * volume K ≤ M) : c + a * volume s ≤ M := by
  rw [hs.measure_eq_iSup_isCompact]
  simp only [ENNReal.mul_iSup, ENNReal.add_iSup]
  refine iSup_le fun K => ?_
  by_cases hKs : K ⊆ s
  · by_cases hK : IsCompact K
    · simpa [hKs, hK] using h K hKs hK
    · simpa [hKs, hK] using h ∅ (empty_subset _) isCompact_empty
  · simpa [hKs] using h ∅ (empty_subset _) isCompact_empty

/-- **One-dimensional Brunn–Minkowski inequality.** For nonempty measurable `A, B ⊆ ℝ`,
`t ∈ [0, 1]`, and any set `S ⊇ t A + (1 - t) B`: `t |A| + (1 - t) |B| ≤ |S|`. -/
theorem brunnMinkowski_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A B S : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hS : ∀ a ∈ A, ∀ b ∈ B, t * a + (1 - t) * b ∈ S) :
    ENNReal.ofReal t * volume A + ENNReal.ofReal (1 - t) * volume B ≤ volume S := by
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  rw [add_comm]
  refine add_mul_volume_le_of_compact hA fun K hKA hK => ?_
  rw [add_comm]
  refine add_mul_volume_le_of_compact hB fun L hLB hL => ?_
  calc ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L
      ≤ ENNReal.ofReal t * volume (insert a₀ K)
          + ENNReal.ofReal (1 - t) * volume (insert b₀ L) := by
        gcongr <;> exact subset_insert _ _
    _ ≤ volume S := brunnMinkowski_one_compact ht0 ht1 (hK.insert a₀) (hL.insert b₀)
        (insert_nonempty _ _) (insert_nonempty _ _) fun a ha b hb =>
          hS a (insert_subset ha₀ hKA ha) b (insert_subset hb₀ hLB hb)

/-- Layer-cake form of `∫⁻ u` for `u ≤ 1`. -/
theorem lintegral_eq_layerCake {u : ℝ → ℝ≥0∞} (hu : Measurable u) (hu1 : ∀ x, u x ≤ 1) :
    ∫⁻ x, u x = ∫⁻ r in Ioi 0, volume {x | r < (u x).toReal} := by
  rw [← lintegral_eq_lintegral_meas_lt _ (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
    hu.ennreal_toReal.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hu1 x))]

/-- **Normalised one-dimensional Prékopa–Leindler.** If `u, v ≤ 1` have supremum `1`
(`∀ r < 1, ∃ x, r < u x`), `w` is measurable and `u(x)^t v(y)^{1-t} ≤ w(t x + (1-t) y)`,
then `t ∫u + (1-t) ∫v ≤ ∫w`. -/
theorem prekopaLeindler_one_normalized {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v w : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (hu1 : ∀ x, u x ≤ 1) (hv1 : ∀ x, v x ≤ 1) (husup : ∀ r < 1, ∃ x, r < u x)
    (hvsup : ∀ r < 1, ∃ x, r < v x)
    (h : ∀ x y, u x ^ t * v y ^ (1 - t) ≤ w (t * x + (1 - t) * y)) :
    ENNReal.ofReal t * (∫⁻ x, u x) + ENNReal.ofReal (1 - t) * (∫⁻ x, v x) ≤ ∫⁻ x, w x := by
  set w' : ℝ → ℝ≥0∞ := fun x => min (w x) 1
  have hw' : Measurable w' := hw.min measurable_const
  have hw'1 : ∀ x, w' x ≤ 1 := fun x => min_le_right _ _
  have hww : ∫⁻ x, w' x ≤ ∫⁻ x, w x := lintegral_mono fun x => min_le_left _ _
  refine le_trans ?_ hww
  have e1 := lintegral_eq_layerCake hu hu1
  have e2 := lintegral_eq_layerCake hv hv1
  have e3 := lintegral_eq_layerCake hw' hw'1
  rw [e1, e2, e3, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (le_lintegral_add _ _).trans (lintegral_mono_ae ?_)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r (hr : 0 < r) => ?_)
  have hmeas : ∀ f : ℝ → ℝ≥0∞, Measurable f → MeasurableSet {x | r < (f x).toReal} :=
    fun f hf => measurableSet_lt measurable_const hf.ennreal_toReal
  have hfin : ∀ f : ℝ → ℝ≥0∞, (∀ x, f x ≤ 1) → ∀ x, f x ≠ ⊤ :=
    fun f hf x => ne_top_of_le_ne_top ENNReal.one_ne_top (hf x)
  rcases lt_or_ge r 1 with hr1 | hr1
  · have hr1' : ENNReal.ofReal r < 1 := ENNReal.ofReal_lt_one.2 hr1
    have hne : ∀ f : ℝ → ℝ≥0∞, (∀ x, f x ≤ 1) → (∀ r < 1, ∃ x, r < f x) →
        {x | r < (f x).toReal}.Nonempty := fun f hf1 hfs => by
      obtain ⟨x, hx⟩ := hfs _ hr1'
      exact ⟨x, (ENNReal.ofReal_lt_iff_lt_toReal hr.le (hfin f hf1 x)).1 hx⟩
    refine brunnMinkowski_one ht0.le ht1.le (hmeas u hu) (hmeas v hv) (hne u hu1 husup)
      (hne v hv1 hvsup) fun a ha b hb => ?_
    have ha' := (ENNReal.ofReal_lt_iff_lt_toReal hr.le (hfin u hu1 a)).2 ha
    have hb' := (ENNReal.ofReal_lt_iff_lt_toReal hr.le (hfin v hv1 b)).2 hb
    have hr0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
    have hlt : ENNReal.ofReal r < w (t * a + (1 - t) * b) :=
      calc ENNReal.ofReal r = ENNReal.ofReal r ^ t * ENNReal.ofReal r ^ (1 - t) := by
            rw [← ENNReal.rpow_add _ _ hr0 ENNReal.ofReal_ne_top, add_sub_cancel,
              ENNReal.rpow_one]
        _ < u a ^ t * v b ^ (1 - t) :=
            ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow ha' ht0)
              (ENNReal.rpow_lt_rpow hb' (sub_pos.2 ht1))
        _ ≤ w (t * a + (1 - t) * b) := h a b
    exact (ENNReal.ofReal_lt_iff_lt_toReal hr.le (hfin w' hw'1 _)).1 (lt_min hlt hr1')
  · have hempty : ∀ f : ℝ → ℝ≥0∞, (∀ x, f x ≤ 1) → {x | r < (f x).toReal} = ∅ :=
      fun f hf1 => eq_empty_iff_forall_notMem.2 fun x hx =>
        absurd (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hf1 x))
          (not_le.2 (hr1.trans_lt hx))
    simp [hempty u hu1, hempty v hv1]

/-- Weighted AM–GM in `ℝ≥0∞`: `p^t q^{1-t} ≤ t p + (1-t) q` for `t ∈ (0, 1)`. -/
theorem rpow_mul_rpow_le_add {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (p q : ℝ≥0∞) :
    p ^ t * q ^ (1 - t) ≤ ENNReal.ofReal t * p + ENNReal.ofReal (1 - t) * q := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · simp [ENNReal.mul_top (ENNReal.ofReal_pos.2 ht0).ne']
  rcases eq_or_ne q ⊤ with rfl | hq
  · simp [ENNReal.mul_top (ENNReal.ofReal_pos.2 (sub_pos.2 ht1)).ne']
  rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_toReal hq,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ht0.le,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_pos.2 ht1).le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ht0.le,
    ← ENNReal.ofReal_mul (sub_pos.2 ht1).le, ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (sub_pos.2 ht1).le ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal (Real.geom_mean_le_arith_mean2_weighted ht0.le
    (sub_pos.2 ht1).le ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by ring))

/-- Rescaling identity: `(p/a)^t (q/b)^{1-t} = p^t q^{1-t} (a^t b^{1-t})⁻¹` for finite `b`. -/
theorem div_rpow_mul_div_rpow {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (p q a b : ℝ≥0∞)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (p / a) ^ t * (q / b) ^ (1 - t) = p ^ t * q ^ (1 - t) * (a ^ t * b ^ (1 - t))⁻¹ := by
  have hbt : b ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (sub_pos.2 ht1).le hb
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
    ENNReal.mul_rpow_of_nonneg _ _ (sub_pos.2 ht1).le, ENNReal.inv_rpow, ENNReal.inv_rpow,
    ENNReal.mul_inv (Or.inr hbt) (Or.inl (ENNReal.rpow_ne_top_of_nonneg ht0.le ha))]
  ring

/-- One-dimensional Prékopa–Leindler for functions with finite suprema. -/
theorem prekopaLeindler_one_of_iSup_ne_top {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v w : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (hua : (⨆ x, u x) ≠ ⊤) (hvb : (⨆ x, v x) ≠ ⊤)
    (h : ∀ x y, u x ^ t * v y ^ (1 - t) ≤ w (t * x + (1 - t) * y)) :
    (∫⁻ x, u x) ^ t * (∫⁻ x, v x) ^ (1 - t) ≤ ∫⁻ x, w x := by
  have ht1' : 0 < 1 - t := sub_pos.2 ht1
  set a := ⨆ x, u x
  set b := ⨆ x, v x
  have hzero : ∀ f : ℝ → ℝ≥0∞, (⨆ x, f x) = 0 → ∫⁻ x, f x = 0 := fun f hf => by
    simp [ENNReal.iSup_eq_zero.1 hf]
  rcases eq_or_ne a 0 with ha0 | ha0
  · rw [hzero u ha0, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le
  rcases eq_or_ne b 0 with hb0 | hb0
  · rw [hzero v hb0, ENNReal.zero_rpow_of_pos ht1', mul_zero]
    exact zero_le
  set c := a ^ t * b ^ (1 - t)
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hua).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hvb).ne'
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ht0.le hua)
    (ENNReal.rpow_ne_top_of_nonneg ht1'.le hvb)
  have hle1 : ∀ f : ℝ → ℝ≥0∞, ∀ x, f x / (⨆ y, f y) ≤ 1 := fun f x =>
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_iSup f x)
  have hsup : ∀ f : ℝ → ℝ≥0∞, (⨆ y, f y) ≠ 0 → (⨆ y, f y) ≠ ⊤ →
      ∀ r < 1, ∃ x, r < f x / (⨆ y, f y) := by
    intro f h0 htop r hr
    have hlt : (⨆ y, f y) * r < (⨆ y, f y) * 1 := ENNReal.mul_lt_mul_right h0 htop hr
    rw [mul_one, mul_comm] at hlt
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 hlt
    exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl htop)).2 hx⟩
  have key := prekopaLeindler_one_normalized ht0 ht1 (hu.div_const a) (hv.div_const b)
    (hw.div_const c) (hle1 u) (hle1 v) (hsup u ha0 hua) (hsup v hb0 hvb) fun x y => by
      rw [div_rpow_mul_div_rpow ht0 ht1 _ _ _ _ hua hvb, div_eq_mul_inv]
      exact mul_le_mul_left (h x y) _
  have hint : ∀ (f : ℝ → ℝ≥0∞) (s : ℝ≥0∞), s ≠ 0 → ∫⁻ x, f x / s = (∫⁻ x, f x) / s :=
    fun f s hs => by
      simp only [div_eq_mul_inv]
      exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hs)
  rw [hint u a ha0, hint v b hb0, hint w c hc0] at key
  have := (rpow_mul_rpow_le_add ht0 ht1 _ _).trans key
  rw [div_rpow_mul_div_rpow ht0 ht1 _ _ _ _ hua hvb, div_eq_mul_inv] at this
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hctop)
    (ENNReal.inv_ne_top.2 hc0)).1 this

/-- `(⨆ₙ aₙ)^s = ⨆ₙ aₙ^s` in `ℝ≥0∞` for `s > 0`. -/
theorem iSup_rpow_eq {ι : Sort*} {s : ℝ} (hs : 0 < s) (f : ι → ℝ≥0∞) :
    (⨆ i, f i) ^ s = ⨆ i, f i ^ s := by
  have := (ENNReal.orderIsoRpow s hs).map_iSup f
  simp only [ENNReal.orderIsoRpow_apply] at this
  exact this

/-- **One-dimensional Prékopa–Leindler inequality.** For `t ∈ (0, 1)` and measurable
`u, v, w : ℝ → ℝ≥0∞` with `u(x)^t v(y)^{1-t} ≤ w(t x + (1-t) y)`:
`(∫u)^t (∫v)^{1-t} ≤ ∫w`. -/
theorem prekopaLeindler_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v w : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (h : ∀ x y, u x ^ t * v y ^ (1 - t) ≤ w (t * x + (1 - t) * y)) :
    (∫⁻ x, u x) ^ t * (∫⁻ x, v x) ^ (1 - t) ≤ ∫⁻ x, w x := by
  have ht1' : 0 < 1 - t := sub_pos.2 ht1
  have hsup : ∀ f : ℝ → ℝ≥0∞, ∀ x, f x = ⨆ n : ℕ, f x ⊓ (n : ℝ≥0∞) := fun f x => by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hmono : ∀ f : ℝ → ℝ≥0∞, Monotone fun n : ℕ => ∫⁻ x, f x ⊓ (n : ℝ≥0∞) :=
    fun f m n hmn => lintegral_mono fun x => inf_le_inf_left _ (Nat.cast_le.2 hmn)
  have hlim : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x = ⨆ n : ℕ, ∫⁻ x, f x ⊓ (n : ℝ≥0∞) := fun f hf => by
    conv_lhs => enter [2, x]; rw [hsup f x]
    exact lintegral_iSup (fun n => hf.inf measurable_const)
      fun m n hmn x => inf_le_inf_left _ (Nat.cast_le.2 hmn)
  have hbdd : ∀ (f : ℝ → ℝ≥0∞) (n : ℕ), (⨆ x, f x ⊓ (n : ℝ≥0∞)) ≠ ⊤ := fun f n =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun x => inf_le_right)
  have hn : ∀ n : ℕ, (∫⁻ x, u x ⊓ (n : ℝ≥0∞)) ^ t * (∫⁻ x, v x ⊓ (n : ℝ≥0∞)) ^ (1 - t)
      ≤ ∫⁻ x, w x := fun n =>
    prekopaLeindler_one_of_iSup_ne_top ht0 ht1 (hu.inf measurable_const)
      (hv.inf measurable_const) hw (hbdd u n) (hbdd v n) fun x y =>
        (mul_le_mul' (ENNReal.rpow_le_rpow inf_le_left ht0.le)
          (ENNReal.rpow_le_rpow inf_le_left ht1'.le)).trans (h x y)
  rw [hlim u hu, hlim v hv, iSup_rpow_eq ht0, iSup_rpow_eq ht1', ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => le_trans ?_ (hn (max m n))
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hmono u (le_max_left m n)) ht0.le)
    (ENNReal.rpow_le_rpow (hmono v (le_max_right m n)) ht1'.le)

/-- `Fin.insertNth 0` is linear: it commutes with convex combinations. -/
theorem insertNth_zero_convex {n : ℕ} (t a b : ℝ) (y z : Fin n → ℝ) :
    (Fin.insertNth 0 (t * a + (1 - t) * b) (t • y + (1 - t) • z) : Fin (n + 1) → ℝ) =
      t • Fin.insertNth 0 a y + (1 - t) • Fin.insertNth 0 b z := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- Prékopa–Leindler on `Fin d → ℝ`, by induction on `d` (auxiliary form). -/
theorem prekopaLeindler_aux {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (d : ℕ) :
    ∀ u v w : (Fin d → ℝ) → ℝ≥0∞, Measurable u → Measurable v → Measurable w →
      (∀ x y, u x ^ t * v y ^ (1 - t) ≤ w (t • x + (1 - t) • y)) →
      (∫⁻ x, u x) ^ t * (∫⁻ x, v x) ^ (1 - t) ≤ ∫⁻ x, w x := by
  induction d with
  | zero =>
    intro u v w _ _ _ h
    have h1 : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
      rw [volume_pi, Measure.pi_univ]; simp
    simp only [lintegral_unique, h1, mul_one]
    have hx : ∀ x y : Fin 0 → ℝ, x = y := fun x y => Subsingleton.elim x y
    calc _ = u 0 ^ t * v 0 ^ (1 - t) := by
          rw [congrArg u (hx _ 0), congrArg v (hx _ 0)]
      _ ≤ w (t • 0 + (1 - t) • 0) := h 0 0
      _ = _ := congrArg w (hx _ _)
  | succ n ih =>
    intro u v w hu hv hw h
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth 0 p.1 p.2 := fun p => by
      funext j; simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    have key : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        ∫⁻ x, f x = ∫⁻ a : ℝ, ∫⁻ y : Fin n → ℝ, f (e.symm (a, y)) := fun f hf => by
      rw [← he.lintegral_comp hf]
      exact lintegral_prod _ (hf.comp e.symm.measurable).aemeasurable
    rw [key u hu, key v hv, key w hw]
    have hm : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        Measurable fun a : ℝ => ∫⁻ y : Fin n → ℝ, f (e.symm (a, y)) := fun f hf =>
      (hf.comp e.symm.measurable).lintegral_prod_right'
    refine prekopaLeindler_one ht0 ht1 (hm u hu) (hm v hv) (hm w hw) fun a b => ?_
    refine ih _ _ _ ((hu.comp e.symm.measurable).comp measurable_prodMk_left)
      ((hv.comp e.symm.measurable).comp measurable_prodMk_left)
      ((hw.comp e.symm.measurable).comp measurable_prodMk_left) fun y z => ?_
    simp only [hsymm]
    rw [insertNth_zero_convex]
    exact h _ _

/-- **Prékopa–Leindler inequality on `Fin d → ℝ`.** For `t ∈ (0, 1)` and measurable
`u, v, w : (Fin d → ℝ) → ℝ≥0∞` with `u(x)^t v(y)^{1-t} ≤ w(t x + (1-t) y)` for all `x, y`:
`(∫u)^t (∫v)^{1-t} ≤ ∫w` (Lebesgue measure). -/
theorem prekopa_leindler {d : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v w : (Fin d → ℝ) → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (h : ∀ x y, u x ^ t * v y ^ (1 - t) ≤ w (t • x + (1 - t) • y)) :
    (∫⁻ x, u x) ^ t * (∫⁻ x, v x) ^ (1 - t) ≤ ∫⁻ x, w x :=
  prekopaLeindler_aux ht0 ht1 d u v w hu hv hw h

/-- **Prékopa–Leindler, real-valued form.** For `t ∈ (0, 1)`, nonnegative measurable
`u, v, w : (Fin d → ℝ) → ℝ` with `w` integrable and `u(x)^t v(y)^{1-t} ≤ w(t x + (1-t) y)`:
`(∫u)^t (∫v)^{1-t} ≤ ∫w` (Bochner integrals; a non-integrable `u` or `v` has integral `0`). -/
theorem prekopa_leindler_real {d : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v w : (Fin d → ℝ) → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hw0 : ∀ x, 0 ≤ w x) (hu : Measurable u) (hv : Measurable v) (hwm : Measurable w)
    (hw : Integrable w)
    (h : ∀ x y, u x ^ t * v y ^ (1 - t) ≤ w (t • x + (1 - t) • y)) :
    (∫ x, u x) ^ t * (∫ x, v x) ^ (1 - t) ≤ ∫ x, w x := by
  have ht1' : 0 < 1 - t := sub_pos.2 ht1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hu0) hu.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hv0) hv.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hw0) hw.aestronglyMeasurable,
    ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono hw.lintegral_lt_top.ne ?_
  refine prekopa_leindler ht0 ht1 hu.ennreal_ofReal hv.ennreal_ofReal
    hwm.ennreal_ofReal fun x y => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (hu0 x) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (hv0 y) ht1'.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hu0 x) t)]
  exact ENNReal.ofReal_le_ofReal (h x y)
end FormalizeSampling.PrekopaLeindler
