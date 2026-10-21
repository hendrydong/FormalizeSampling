module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Order.CompletePartialOrder

/-!
# Lower semicontinuity of the KL divergence under weak convergence

Status: **Verified** (no named hypotheses).

Let `ρ, π` be probability laws and `μ_i` a family of probability laws on a pseudo-metric Borel
space `α`. If `∫ f dμ_i → ∫ f dρ` for every bounded continuous `f` (weak convergence), then
`KL(ρ‖π) ≤ liminf_i KL(μ_i‖π)` in `ℝ≥0∞`. The case `KL(ρ‖π) = ∞` is included.

## Route (Donsker–Varadhan)

Write `DV_μ(f) = ∫ f dμ - log ∫ e^f dπ` (`dvValue`).

* `ofReal_dvValue_le_klDiv` (the easy half of Donsker–Varadhan): `DV_μ(f) ≤ KL(μ‖π)` for every
  bounded measurable `f`. It is Gibbs' inequality against the tilted law `π.tilted f`.
* `exists_measurable_lt_dvValue`: if `b < KL(ρ‖π)`, then `b < DV_ρ(g)` for some bounded
  measurable `g`. If `ρ` is not `≪ π`, take `g = M 1_s` with `π(s) = 0 < ρ(s)`. Otherwise, with
  `r = dρ/dπ`, take `g = -n` on `{r ≤ e^{-n}}` and `g = min(log r, n)` elsewhere. Pointwise
  `r g ≥ 1_{r ≤ eⁿ} klFun(r) + r - 1` and `e^g ≤ r + e^{-n}`, and monotone convergence of
  `∫ 1_{r ≤ eⁿ} klFun(r) dπ` to `KL(ρ‖π)` concludes.
* `exists_continuous_lt_dvValue`: the same with `g` bounded **continuous**. A bounded
  continuous `L¹(ρ + π)` approximation of `g` (Mathlib's
  `Integrable.exists_boundedContinuous_integral_sub_le`), clamped to `[-N, N]`, changes
  `∫ g dρ` and `log ∫ e^g dπ` by little.
* `klDiv_le_liminf_of_tendsto_integral`: lower semicontinuity.

## Not proved here

* The full Donsker–Varadhan variational formula as an equality, and lower semicontinuity in
  the second argument (or joint lower semicontinuity).
* Weak convergence in the sense of `MeasureTheory.ProbabilityMeasure` is not used; the
  hypothesis is stated directly for bounded continuous test functions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.KLLowerSemicontinuity

variable {α : Type*} [MeasurableSpace α]

/-- The Donsker–Varadhan functional `DV_μ(f) = ∫ f dμ - log ∫ e^f dπ`. -/
noncomputable def dvValue (μ π : Measure α) (f : α → ℝ) : ℝ :=
  ∫ x, f x ∂μ - Real.log (∫ x, Real.exp (f x) ∂π)

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_abs_le {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {N : ℝ} (hN : ∀ x, |f x| ≤ N) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable N
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hN x)

/-- `e^f` is integrable against a finite measure when `f` is bounded and measurable. -/
theorem integrable_exp_of_abs_le {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {N : ℝ} (hN : ∀ x, |f x| ≤ N) :
    Integrable (fun x => Real.exp (f x)) μ :=
  Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp N)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (le_of_abs_le (hN x)))

/-- **Donsker–Varadhan, easy half.** For probability laws `μ, π` and a bounded measurable `f`:
`ofReal (∫ f dμ - log ∫ e^f dπ) ≤ KL(μ‖π)` (trivial when `KL(μ‖π) = ∞`). -/
theorem ofReal_dvValue_le_klDiv {μ π : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure π] {f : α → ℝ} (hf : Measurable f) {N : ℝ} (hN : ∀ x, |f x| ≤ N) :
    ENNReal.ofReal (dvValue μ π f) ≤ klDiv μ π := by
  by_cases hKL : klDiv μ π = ∞
  · rw [hKL]; exact le_top
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hKL
  have hfπ := integrable_exp_of_abs_le (μ := π) hf hN
  have hfμ := integrable_of_abs_le (μ := μ) hf hN
  have := isProbabilityMeasure_tilted hfπ
  have hac' : μ ≪ π.tilted f := hac.trans (absolutelyContinuous_tilted hfπ)
  have h0 : 0 ≤ (klDiv μ (π.tilted f)).toReal := ENNReal.toReal_nonneg
  rw [toReal_klDiv_of_measure_eq hac' (by simp), integral_llr_tilted_right hac hfμ hfπ hint]
    at h0
  rw [← ENNReal.ofReal_toReal hKL, toReal_klDiv_of_measure_eq hac (by simp)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold dvValue
  linarith

/-- Pointwise inequality behind the absolutely continuous case: for `r ≥ 0` and `n ≥ 1`, with
`g = -n` if `r ≤ e^{-n}` and `g = min(log r, n)` otherwise,
`r g ≥ 1_{r ≤ eⁿ} klFun(r) + r - 1`. -/
theorem mul_trunc_ge {r n : ℝ} (hr : 0 ≤ r) (hn : 1 ≤ n) :
    (if r ≤ Real.exp n then klFun r else 0) + r - 1 ≤
      r * (if r ≤ Real.exp (-n) then -n else min (Real.log r) n) := by
  rw [klFun_apply]
  split_ifs with h1 h2 h2
  · -- `r ≤ e^{-n}`: `r log r ≤ -n r`
    have : r * Real.log r ≤ r * (-n) := by
      rcases hr.eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · refine mul_le_mul_of_nonneg_left ?_ hr
        rw [← Real.log_exp (-n)]
        exact Real.log_le_log h0 h2
    linarith
  · have h0 : 0 < r := lt_of_lt_of_le (Real.exp_pos _) (not_le.1 h2).le
    have : Real.log r ≤ n := by
      rw [← Real.log_exp n]; exact Real.log_le_log h0 h1
    rw [min_eq_left this]
    linarith
  · exact absurd (h2.trans (Real.exp_le_exp.2 (by linarith))) h1
  · have h0 : 0 < r := lt_of_lt_of_le (Real.exp_pos _) (not_le.1 h1).le
    have : n ≤ Real.log r := by
      rw [← Real.log_exp n]; exact Real.log_le_log (Real.exp_pos _) (not_le.1 h1).le
    rw [min_eq_right this]
    nlinarith

/-- Pointwise inequality `e^g ≤ r + e^{-n}` for the truncation `g` of `log r`. -/
theorem exp_trunc_le {r n : ℝ} (hr : 0 ≤ r) :
    Real.exp (if r ≤ Real.exp (-n) then -n else min (Real.log r) n) ≤ r + Real.exp (-n) := by
  split_ifs with h
  · linarith
  · have h0 : 0 < r := lt_of_lt_of_le (Real.exp_pos _) (not_le.1 h).le
    calc Real.exp (min (Real.log r) n) ≤ Real.exp (Real.log r) :=
          Real.exp_le_exp.2 (min_le_left _ _)
      _ = r := Real.exp_log h0
      _ ≤ r + Real.exp (-n) := by linarith [Real.exp_pos (-n)]

/-- The truncation `g` of `log r` satisfies `|g| ≤ n` (`n ≥ 0`). -/
theorem abs_trunc_le {r n : ℝ} (hn : 0 ≤ n) :
    |(if r ≤ Real.exp (-n) then -n else min (Real.log r) n)| ≤ n := by
  split_ifs with h
  · rw [abs_neg, abs_of_nonneg hn]
  · have h0 : 0 < r := lt_of_lt_of_le (Real.exp_pos _) (not_le.1 h).le
    have : -n ≤ Real.log r := by
      rw [← Real.log_exp (-n)]; exact Real.log_le_log (Real.exp_pos _) (not_le.1 h).le
    rw [abs_le]
    exact ⟨le_min this (by linarith), min_le_right _ _⟩

variable {ρ π : Measure α} [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]

/-- **Absolutely continuous case.** If `ρ ≪ π` and `b < KL(ρ‖π)` (in `ℝ≥0∞`), some bounded
measurable `g` has `b < ∫ g dρ - log ∫ e^g dπ`. -/
theorem exists_measurable_lt_dvValue_of_ac (hac : ρ ≪ π) {b : ℝ}
    (hb : ENNReal.ofReal b < klDiv ρ π) :
    ∃ (g : α → ℝ) (N : ℝ), Measurable g ∧ 0 ≤ N ∧ (∀ x, |g x| ≤ N) ∧ b < dvValue ρ π g := by
  set r : α → ℝ := fun x => (ρ.rnDeriv π x).toReal with hr
  have hrm : Measurable r := (Measure.measurable_rnDeriv ρ π).ennreal_toReal
  have hr0 : ∀ x, 0 ≤ r x := fun x => ENNReal.toReal_nonneg
  have hri : Integrable r π := Measure.integrable_toReal_rnDeriv
  have hr1 : ∫ x, r x ∂π = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac]; simp
  set K : ℕ → α → ℝ := fun n x => if r x ≤ Real.exp n then klFun (r x) else 0 with hK
  have hKm : ∀ n, Measurable (K n) := fun n =>
    Measurable.ite (measurableSet_le hrm measurable_const)
      (InformationTheory.measurable_klFun.comp hrm) measurable_const
  have hK0 : ∀ n x, 0 ≤ K n x := fun n x => by
    simp only [hK]; split_ifs
    · exact klFun_nonneg (hr0 x)
    · exact le_rfl
  have hKmono : Monotone fun n x => ENNReal.ofReal (K n x) := by
    intro m n hmn x
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hK]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans (Real.exp_le_exp.2 (by exact_mod_cast hmn))) h2
    · exact klFun_nonneg (hr0 x)
    · exact le_rfl
  have hKsup : ∀ x, ⨆ n : ℕ, ENNReal.ofReal (K n x) = ENNReal.ofReal (klFun (r x)) := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (r x)
    refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_ofReal ?_) (le_iSup_of_le n ?_)
    · simp only [hK]; split_ifs
      · exact le_rfl
      · exact klFun_nonneg (hr0 x)
    · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      simp only [hK]
      have h1 := Real.add_one_le_exp (n : ℝ)
      have h2 : r x ≤ Real.exp n := by linarith
      simp only [h2, ↓reduceIte]
  have hKL : klDiv ρ π = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (K n x) ∂π := by
    rw [klDiv_eq_lintegral_klFun_of_ac hac,
      ← lintegral_iSup (fun n => (hKm n).ennreal_ofReal) hKmono]
    simp_rw [hKsup]
    rfl
  obtain ⟨q, hbq, hqK⟩ := exists_between hb
  have hq : q ≠ ∞ := ne_top_of_lt hqK
  rw [hKL] at hqK
  obtain ⟨n₁, hn₁⟩ := lt_iSup_iff.1 hqK
  set b' := q.toReal
  have hbb' : b < b' := by
    rcases le_or_gt b 0 with h | h
    · have : 0 < q := (zero_le).trans_lt hbq
      exact h.trans_lt (ENNReal.toReal_pos this.ne' hq)
    · exact (ENNReal.ofReal_lt_iff_lt_toReal h.le hq).1 hbq
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 ≤ n ∧ n₁ ≤ n) ∧ Real.exp (-(n : ℝ)) < b' - b := by
    have h1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ n₁ ≤ n :=
      (eventually_ge_atTop 1).and (eventually_ge_atTop n₁)
    have h2 : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < b' - b :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (by linarith))
    exact (h1.and h2).exists
  obtain ⟨⟨hn1, hnn₁⟩, hnexp⟩ := hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set g : α → ℝ := fun x =>
    if r x ≤ Real.exp (-(n : ℝ)) then -(n : ℝ) else min (Real.log (r x)) n with hg
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_le hrm measurable_const) measurable_const
      ((Real.measurable_log.comp hrm).min measurable_const)
  have hgN : ∀ x, |g x| ≤ n := fun x => abs_trunc_le (by positivity)
  refine ⟨g, n, hgm, by positivity, hgN, ?_⟩
  -- the bounded truncated `klFun`
  have hKb : ∀ x, K n x ≤ n * Real.exp n + 1 := by
    intro x
    simp only [hK]
    split_ifs with h
    · rw [klFun_apply]
      have hl : r x * Real.log (r x) ≤ r x * n := by
        rcases (hr0 x).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        · refine mul_le_mul_of_nonneg_left ?_ (hr0 x)
          rw [← Real.log_exp n]; exact Real.log_le_log h0 h
      nlinarith [hr0 x]
    · positivity
  have hKi : Integrable (K n) π :=
    Integrable.of_bound (hKm n).aestronglyMeasurable _
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hK0 n x)]; exact hKb x)
  -- `∫ K_n dπ > b'`
  have hKint : b' < ∫ x, K n x ∂π := by
    have h1 : ENNReal.ofReal (∫ x, K n x ∂π) = ∫⁻ x, ENNReal.ofReal (K n x) ∂π :=
      ofReal_integral_eq_lintegral_ofReal hKi (ae_of_all _ (hK0 n))
    have h2 : q < ENNReal.ofReal (∫ x, K n x ∂π) := by
      rw [h1]; exact hn₁.trans_le (lintegral_mono fun x => hKmono hnn₁ x)
    exact (ENNReal.lt_ofReal_iff_toReal_lt hq).1 h2
  -- `∫ g dρ ≥ ∫ K_n dπ`
  have hgi : Integrable (fun x => r x * g x) π := by
    refine (hri.mul_const (n : ℝ)).mono' (hrm.mul hgm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr0 x)]
    exact mul_le_mul_of_nonneg_left (hgN x) (hr0 x)
  have hgρ : ∫ x, g x ∂ρ = ∫ x, r x * g x ∂π := by
    rw [← integral_rnDeriv_smul hac]; rfl
  have hge : ∫ x, K n x ∂π ≤ ∫ x, g x ∂ρ := by
    have h := integral_mono (f := fun x => K n x + r x) (g := fun x => r x * g x + 1)
      (hKi.add hri) (hgi.add (integrable_const 1))
      (fun x => by have := mul_trunc_ge (hr0 x) hn1' (r := r x); simp only; linarith)
    rw [integral_add hKi hri, integral_add hgi (integrable_const 1), hr1] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    rw [hgρ]; linarith
  -- `log ∫ e^g dπ ≤ e^{-n}`
  have hexpi := integrable_exp_of_abs_le (μ := π) hgm hgN
  have hexp : ∫ x, Real.exp (g x) ∂π ≤ 1 + Real.exp (-(n : ℝ)) := by
    have h := integral_mono (g := fun x => r x + Real.exp (-(n : ℝ))) hexpi
      (hri.add (integrable_const _)) fun x => exp_trunc_le (hr0 x)
    rw [integral_add hri (integrable_const _), hr1] at h
    simpa using h
  have hpos : 0 < ∫ x, Real.exp (g x) ∂π :=
    integral_exp_pos hexpi
  have hlog : Real.log (∫ x, Real.exp (g x) ∂π) ≤ Real.exp (-(n : ℝ)) := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  unfold dvValue
  linarith

/-- **Donsker–Varadhan, approximate maximiser.** For probability laws `ρ, π` and a real `b`
with `b < KL(ρ‖π)` (in `ℝ≥0∞`, possibly `KL = ∞`), some bounded measurable `g` has
`b < ∫ g dρ - log ∫ e^g dπ`. -/
theorem exists_measurable_lt_dvValue {b : ℝ} (hb : ENNReal.ofReal b < klDiv ρ π) :
    ∃ (g : α → ℝ) (N : ℝ), Measurable g ∧ 0 ≤ N ∧ (∀ x, |g x| ≤ N) ∧ b < dvValue ρ π g := by
  by_cases hac : ρ ≪ π
  · exact exists_measurable_lt_dvValue_of_ac hac hb
  obtain ⟨s, hs, hπs, hρs⟩ : ∃ s, MeasurableSet s ∧ π s = 0 ∧ ρ s ≠ 0 := by
    by_contra h
    push Not at h
    exact hac (Measure.AbsolutelyContinuous.mk fun s hs h0 => h s hs h0)
  set m := ρ.real s
  have hm : 0 < m := ENNReal.toReal_pos hρs (measure_ne_top _ _)
  set M := (|b| + 1) / m
  have hM : 0 ≤ M := by positivity
  refine ⟨s.indicator fun _ => M, M, measurable_const.indicator hs, hM, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, abs_of_nonneg hM]
    · rw [indicator_of_notMem hx, abs_zero]; exact hM
  · have h1 : ∫ x, s.indicator (fun _ => M) x ∂ρ = |b| + 1 := by
      rw [integral_indicator_const _ hs, smul_eq_mul]
      change m * ((|b| + 1) / m) = _
      field_simp
    have h2 : ∫ x, Real.exp (s.indicator (fun _ => M) x) ∂π = 1 := by
      have : (fun x => Real.exp (s.indicator (fun _ => M) x)) =ᵐ[π] fun _ => 1 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hπs] with x hx
        simp [hx]
      rw [integral_congr_ae this]
      simp
    rw [dvValue, h1, h2, Real.log_one, sub_zero]
    linarith [le_abs_self b]

/-- Clamping to `[-N, N]` is `1`-Lipschitz and fixes points of `[-N, N]`. -/
theorem abs_sub_clamp_le {g h N : ℝ} (hg : |g| ≤ N) : |g - max (min h N) (-N)| ≤ |g - h| := by
  rw [abs_le] at hg
  obtain ⟨hg1, hg2⟩ := hg
  rcases le_total h N with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total h (-N) with h2 | h2
    · rw [max_eq_right h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [max_eq_left h2]
  · rw [min_eq_right h1, max_eq_left (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith

/-- `e^f - e^g ≤ e^N |g - f|` for `f ≤ N` (tangent line of `exp` at `f`). -/
theorem exp_sub_exp_le {f g N : ℝ} (hf : f ≤ N) :
    Real.exp f - Real.exp g ≤ Real.exp N * |g - f| := by
  have h1 := Real.add_one_le_exp (g - f)
  have h2 : Real.exp f * (g - f + 1) ≤ Real.exp g := by
    rw [show Real.exp g = Real.exp f * Real.exp (g - f) by rw [← Real.exp_add]; ring_nf]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have h3 : Real.exp f * (f - g) ≤ Real.exp N * |g - f| := by
    rw [abs_sub_comm]
    calc Real.exp f * (f - g) ≤ Real.exp f * |f - g| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
      _ ≤ Real.exp N * |f - g| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hf) (abs_nonneg _)
  nlinarith

section Topology

variable [PseudoMetricSpace α] [BorelSpace α]

/-- **Donsker–Varadhan with a continuous test function.** On a pseudo-metric Borel space, for
probability laws `ρ, π` and a real `b < KL(ρ‖π)` (in `ℝ≥0∞`, possibly `KL = ∞`), some bounded
continuous `f` has `b < ∫ f dρ - log ∫ e^f dπ`. -/
theorem exists_continuous_lt_dvValue {b : ℝ} (hb : ENNReal.ofReal b < klDiv ρ π) :
    ∃ (f : α → ℝ) (N : ℝ), Continuous f ∧ 0 ≤ N ∧ (∀ x, |f x| ≤ N) ∧ b < dvValue ρ π f := by
  obtain ⟨g, N, hgm, hN0, hgN, hlt⟩ := exists_measurable_lt_dvValue hb
  set ε := dvValue ρ π g - b with hε
  have hε0 : 0 < ε := by linarith
  set δ := ε / (2 * (1 + Real.exp N * Real.exp N)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ + Real.exp N * Real.exp N * δ < ε := by
    rw [hδ]; field_simp; nlinarith [Real.exp_pos N]
  have hgi : Integrable g (ρ + π) := integrable_of_abs_le hgm hgN
  obtain ⟨h, hh, -⟩ := hgi.exists_boundedContinuous_integral_sub_le hδ0
  set f : α → ℝ := fun x => max (min (h x) N) (-N) with hf
  have hfc : Continuous f := (h.continuous.min continuous_const).max continuous_const
  have hfN : ∀ x, |f x| ≤ N := fun x => by
    rw [abs_le]; exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
  have hfm : Measurable f := hfc.measurable
  have hfg : ∀ x, |g x - f x| ≤ |g x - h x| := fun x => abs_sub_clamp_le (hgN x)
  -- `L¹` bounds against `ρ` and `π`
  have hdm : Measurable fun x => |g x - h x| := (hgm.sub h.continuous.measurable).abs
  have hdN : ∀ x, |(fun x => |g x - h x|) x| ≤ N + ‖h‖ := fun x => by
    simp only [abs_abs]
    refine (abs_sub _ _).trans (add_le_add (hgN x) ?_)
    exact (Real.norm_eq_abs _ ▸ h.norm_coe_le_norm x)
  have hdρ : Integrable (fun x => |g x - h x|) ρ := integrable_of_abs_le hdm hdN
  have hdπ : Integrable (fun x => |g x - h x|) π := integrable_of_abs_le hdm hdN
  have hsum : ∫ x, |g x - h x| ∂ρ + ∫ x, |g x - h x| ∂π ≤ δ := by
    rw [← integral_add_measure hdρ hdπ]
    simpa [Real.norm_eq_abs] using hh
  have hρ0 : 0 ≤ ∫ x, |g x - h x| ∂ρ := integral_nonneg fun _ => abs_nonneg _
  have hπ0 : 0 ≤ ∫ x, |g x - h x| ∂π := integral_nonneg fun _ => abs_nonneg _
  -- the linear term
  have hlin : ∫ x, g x ∂ρ - δ ≤ ∫ x, f x ∂ρ := by
    have h1 := integral_mono (f := fun x => g x - f x) (g := fun x => |g x - h x|)
      ((integrable_of_abs_le hgm hgN).sub (integrable_of_abs_le hfm hfN)) hdρ
      (fun x => (le_abs_self _).trans (hfg x))
    rw [integral_sub (integrable_of_abs_le hgm hgN) (integrable_of_abs_le hfm hfN)] at h1
    linarith
  -- the exponential term
  have hgπ := integrable_exp_of_abs_le (μ := π) hgm hgN
  have hfπ := integrable_exp_of_abs_le (μ := π) hfm hfN
  set A := ∫ x, Real.exp (g x) ∂π
  set B := ∫ x, Real.exp (f x) ∂π
  have hA : Real.exp (-N) ≤ A := by
    have := integral_mono (integrable_const (Real.exp (-N))) hgπ
      (fun x => Real.exp_le_exp.2 (neg_le_of_abs_le (hgN x)))
    simpa using this
  have hApos : 0 < A := (Real.exp_pos _).trans_le hA
  have hBpos : 0 < B := integral_exp_pos hfπ
  have hBA : B - A ≤ Real.exp N * δ := by
    have h1 := integral_mono (f := fun x => Real.exp (f x) - Real.exp (g x))
      (g := fun x => Real.exp N * |g x - h x|) (hfπ.sub hgπ) (hdπ.const_mul _)
      (fun x => (exp_sub_exp_le (le_of_abs_le (hfN x))).trans
        (mul_le_mul_of_nonneg_left (hfg x) (Real.exp_pos _).le))
    rw [integral_sub hfπ hgπ, integral_const_mul] at h1
    have : Real.exp N * ∫ x, |g x - h x| ∂π ≤ Real.exp N * δ :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    linarith
  have hlog : Real.log B ≤ Real.log A + Real.exp N * Real.exp N * δ := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hBpos hApos)
    rw [Real.log_div hBpos.ne' hApos.ne'] at h1
    have h2 : B / A - 1 ≤ Real.exp N * Real.exp N * δ := by
      rw [div_sub_one hApos.ne', div_le_iff₀ hApos]
      have hAN : 1 ≤ Real.exp N * A := by
        have := mul_le_mul_of_nonneg_left hA (Real.exp_pos N).le
        rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      have h3 := mul_le_mul_of_nonneg_left hAN (mul_pos (Real.exp_pos N) hδ0).le
      nlinarith
    linarith
  refine ⟨f, N, hfc, hN0, hfN, ?_⟩
  unfold dvValue at hε ⊢
  linarith

/-- **Lower semicontinuity of KL under weak convergence.** On a pseudo-metric Borel space, let
`ρ, π` and `μ_i` be probability laws. If `∫ f dμ_i → ∫ f dρ` along a filter `l` for every bounded
continuous `f`, then `KL(ρ‖π) ≤ liminf_l KL(μ_i‖π)` in `ℝ≥0∞` (including `KL(ρ‖π) = ∞`). -/
theorem klDiv_le_liminf_of_tendsto_integral {ι : Type*} {l : Filter ι} {μ : ι → Measure α}
    [∀ i, IsProbabilityMeasure (μ i)]
    (h : ∀ f : α → ℝ, Continuous f → ∀ N : ℝ, (∀ x, |f x| ≤ N) →
      Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ρ))) :
    klDiv ρ π ≤ liminf (fun i => klDiv (μ i) π) l := by
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨q, hcq, hqK⟩ := exists_between hc
  have hq : q ≠ ∞ := ne_top_of_lt hqK
  have hb : ENNReal.ofReal q.toReal < klDiv ρ π := by rwa [ENNReal.ofReal_toReal hq]
  obtain ⟨f, N, hf, -, hfN, hlt⟩ := exists_continuous_lt_dvValue hb
  have hev : ∀ᶠ i in l, q.toReal < dvValue (μ i) π f :=
    ((h f hf N hfN).sub_const (Real.log (∫ x, Real.exp (f x) ∂π))).eventually
      (lt_mem_nhds hlt)
  refine hcq.trans_le (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [hev] with i hi
  rw [← ENNReal.ofReal_toReal hq]
  exact (ENNReal.ofReal_le_ofReal hi.le).trans (ofReal_dvValue_le_klDiv hf.measurable hfN)

end Topology

end FormalizeSampling.KLLowerSemicontinuity
