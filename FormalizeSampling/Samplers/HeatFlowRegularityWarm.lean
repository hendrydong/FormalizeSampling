module

public import FormalizeSampling.Foundations.HeatFlowRegularity

/-!
# Regularity of the heat flow for warm laws against a general target

Status: **Verified** (dimension one; no named hypotheses).

For probability measures `ρ, π` on `ℝ` with `ρ ≤ C • π` (a **warm** law, `dρ/dπ ≤ C`) and a
target `π` with finite second moment `∫ x² dπ < ∞`, every field of
`HeatFlowDeBruijn.HeatFlowRegular ρ π (Ioi 0)` is proved. No posterior second-moment bound, no
lower bound and no smoothness of `π` is needed.

Notation (as in `HeatFlowDeBruijn`, `HeatFlowRegularity`): `p_r = heatFlowDensity ρ r = ρ * φ_r`,
`q_r = heatFlowDensity π r = π * φ_r`, with space derivatives `p_r', p_r'', q_r', q_r''`.

Proof strategy. Warmness passes to the heat flow pointwise: `p_r ≤ C q_r`
(`heatFlowDensity_le_of_warm`), so the ratio `U = p_r / q_r` is bounded by `C`. The terms of
the de Bruijn integrands that involve `π` always appear as `U · q_r''`, `U · q_r'` or
`p_r (q_r'/q_r)² = U · q_r'²/q_r`, and are therefore bounded by `C` times the `π`-side heat-flow
bounds of `HeatFlowRegularity` (`|q_r'|, |q_r''| ≤ K q_{2b}`, `q_r'²/q_r ≤ K q_{2r}`), which are
valid for every probability `π`. The remaining terms only involve `ρ`, whose second moment is
inherited from `π` (`integrable_sq_of_warm`), and `|log(p_r/q_r)| ≤ A (1 + y²)`, which holds for
all probabilities. This replaces the posterior second-moment bound of
`HeatFlowRegularityPerturbed` (needed there because `p_r/q_r` is unbounded for non-warm `ρ`).

## Main results

* `heatFlowDensity_le_of_warm`: `ρ ≤ C • π` gives `p_r(y) ≤ C q_r(y)`.
* `integrable_sq_of_warm`: a warm law inherits the second moment of `π`.
* `heatFlowRegular_of_warm`: `HeatFlowRegular ρ π (Ioi 0)` for `ρ ≤ C • π`, `∫ x² dπ < ∞`.

## Not proved here

* Non-warm `ρ`: then `p_r/q_r` is unbounded and the `π`-terms need ratio bounds on
  `q_r'/q_r`, `q_r''/q_r` (`HeatFlowRegularityPerturbed.PosteriorSecondMomentBound`).
* Targets without a second moment (the boundary flux and the KL integrand are controlled with
  `∫ x² dπ < ∞`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.GaussianLSI
open FormalizeSampling.HeatFlowRegularity

namespace FormalizeSampling.HeatFlowRegularityWarm

section Warm

variable (ρ π : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {C : ℝ}

omit [IsProbabilityMeasure ρ] in
/-- **Warmness along the heat flow.** If `ρ ≤ C • π` (`C ≥ 0`), then for `t > 0`,
`p_t(y) ≤ C q_t(y)` for every `y`. -/
theorem heatFlowDensity_le_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π) {t : ℝ}
    (ht : 0 < t) (y : ℝ) : heatFlowDensity ρ t y ≤ C * heatFlowDensity π t y := by
  have hi := integrable_heatDensity_sub_left π ht y
  calc heatFlowDensity ρ t y = ∫ x, heatDensity t (y - x) ∂ρ := rfl
    _ ≤ ∫ x, heatDensity t (y - x) ∂(ENNReal.ofReal C • π) :=
        integral_mono_measure hwarm (Eventually.of_forall fun x => (heatDensity_pos ht _).le)
          (hi.smul_measure ENNReal.ofReal_ne_top)
    _ = C * heatFlowDensity π t y := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]; rfl

omit [IsProbabilityMeasure ρ] in
/-- The heat-flow ratio of a `C`-warm law is bounded: `p_t(y) / q_t(y) ≤ C` (`t > 0`). -/
theorem heatFlowDensity_div_le_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    {t : ℝ} (ht : 0 < t) (y : ℝ) : heatFlowDensity ρ t y / heatFlowDensity π t y ≤ C := by
  rw [div_le_iff₀ (heatFlowDensity_pos π ht y)]
  exact heatFlowDensity_le_of_warm ρ π hC hwarm ht y

omit [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] in
/-- A law that is `C`-warm for `π` inherits the second moment of `π`:
`ρ ≤ C • π` and `∫ x² dπ < ∞` give `∫ x² dρ < ∞`. -/
theorem integrable_sq_of_warm (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => x ^ 2) π) : Integrable (fun x => x ^ 2) ρ :=
  (hmom.smul_measure ENNReal.ofReal_ne_top).mono_measure hwarm

/-- Field `dominated` for warm laws: for `t > 0` the KL time derivative `klRate` is dominated,
uniformly for `r` near `t`, by `M (1 + y²) p_{4t}(y) + C K q_{4t}(y)`. -/
theorem dominated_klRate_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ᶠ r in 𝓝 t, ∀ y,
      |klRate (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD2 ρ) (heatFlowD2 π) r y|
        ≤ bound y := by
  set a := t / 2
  set b := 2 * t
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by simp only [a, b]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_heatFlow_le ρ ha hab
  obtain ⟨Kq, hKq0, hKq⟩ := exists_heatFlow_le π ha hab
  obtain ⟨Ap, hAp⟩ := exists_abs_log_heatFlowDensity_le ρ ha hab
  obtain ⟨Aq, hAq⟩ := exists_abs_log_heatFlowDensity_le π ha hab
  have hAp0 := nonneg_of_abs_log_le (hAp a ⟨le_rfl, hab⟩ 0)
  have hAq0 := nonneg_of_abs_log_le (hAq a ⟨le_rfl, hab⟩ 0)
  set M := K * (Ap + Aq + 1)
  refine ⟨fun y => M * ((1 + y ^ 2) * heatFlowDensity ρ (2 * b) y)
      + C * Kq * heatFlowDensity π (2 * b) y,
    ((integrable_one_add_sq_mul_heatFlowDensity ρ hmom (by positivity)).const_mul M).add
      ((integrable_heatFlowDensity π (by positivity)).const_mul (C * Kq)), ?_⟩
  filter_upwards [Icc_mem_nhds (show a < t by simp only [a]; linarith)
    (show t < b by simp only [b]; linarith)] with r hr y
  have hr0 : 0 < r := ha.trans_le hr.1
  have hp := heatFlowDensity_pos ρ hr0 y
  have hq := heatFlowDensity_pos π hr0 y
  have hU := heatFlowDensity_div_le_of_warm ρ π hC hwarm hr0 y
  have hU0 : 0 ≤ heatFlowDensity ρ r y / heatFlowDensity π r y := (div_pos hp hq).le
  obtain ⟨-, -, hK3⟩ := hK r hr y
  obtain ⟨-, -, hKq3⟩ := hKq r hr y
  have hL := abs_log_div_add_one_le hp hq (hAp r hr y) (hAq r hr y)
  set P4 := heatFlowDensity ρ (2 * b) y
  set Q4 := heatFlowDensity π (2 * b) y
  have hP4 : 0 ≤ P4 := (heatFlowDensity_pos ρ (by positivity) y).le
  have hQ4 : 0 ≤ Q4 := (heatFlowDensity_pos π (by positivity) y).le
  have T1 : |heatFlowD2 ρ r y * (Real.log (heatFlowDensity ρ r y / heatFlowDensity π r y) + 1)|
      ≤ K * P4 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul hK3 hL (abs_nonneg _) (by positivity)
  have T2 : |heatFlowDensity ρ r y / heatFlowDensity π r y * heatFlowD2 π r y|
      ≤ C * (Kq * Q4) := by
    rw [abs_mul, abs_of_nonneg hU0]
    exact mul_le_mul hU hKq3 (abs_nonneg _) hC
  unfold klRate
  rw [abs_div, abs_two]
  have := abs_sub (heatFlowD2 ρ r y * (Real.log (heatFlowDensity ρ r y /
    heatFlowDensity π r y) + 1)) (heatFlowDensity ρ r y / heatFlowDensity π r y *
    heatFlowD2 π r y)
  have e : M * ((1 + y ^ 2) * P4) = K * P4 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by
    simp only [M]; ring
  have : 0 ≤ K * P4 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by positivity
  have : 0 ≤ C * (Kq * Q4) := by positivity
  rw [e]
  have e2 : C * Kq * Q4 = C * (Kq * Q4) := by ring
  rw [e2]
  linarith

/-- Field `integrable_fisher` for warm laws: for `t > 0` the relative Fisher integrand
`p_t (p_t'/p_t - q_t'/q_t)²` is Lebesgue integrable. -/
theorem integrable_fisherIntegrand_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t) := by
  obtain ⟨K, hK0, hK⟩ := exists_sq_heatFlowD1_div_le ρ ht
  obtain ⟨Kq, hKq0, hKq⟩ := exists_sq_heatFlowD1_div_le π ht
  have hc : Continuous (fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t) := by
    unfold fisherIntegrand relScore
    exact (continuous_heatFlowDensity ρ ht).mul ((((continuous_heatFlowD1 ρ ht).div
      (continuous_heatFlowDensity ρ ht) fun y => (heatFlowDensity_pos ρ ht y).ne').sub
      ((continuous_heatFlowD1 π ht).div (continuous_heatFlowDensity π ht)
        fun y => (heatFlowDensity_pos π ht y).ne')).pow 2)
  refine (((integrable_heatFlowDensity ρ (show 0 < 2 * t by linarith)).const_mul (2 * K)).add
    ((integrable_heatFlowDensity π (show 0 < 2 * t by linarith)).const_mul (2 * (C * Kq)))).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hp := heatFlowDensity_pos ρ ht y
  have hq := heatFlowDensity_pos π ht y
  have hU := heatFlowDensity_div_le_of_warm ρ π hC hwarm ht y
  set p := heatFlowDensity ρ t y
  set q := heatFlowDensity π t y
  set d := heatFlowD1 ρ t y
  set e := heatFlowD1 π t y
  set w := e / q
  have hfe : fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t y = p * (d / p - w) ^ 2 := rfl
  rw [hfe, Real.norm_of_nonneg (mul_nonneg hp.le (sq_nonneg _))]
  simp only [Pi.add_apply]
  have h1 : p * (d / p - w) ^ 2 ≤ 2 * (d ^ 2 / p) + 2 * (p * w ^ 2) := by
    have e1 : p * (d / p) ^ 2 = d ^ 2 / p := by field_simp
    nlinarith [mul_nonneg hp.le (sq_nonneg (d / p + w))]
  have h2 : p * w ^ 2 ≤ C * (Kq * heatFlowDensity π (2 * t) y) := by
    have e2 : p * w ^ 2 = p / q * (e ^ 2 / q) := by simp only [w]; field_simp
    rw [e2]
    exact mul_le_mul hU (hKq y) (div_nonneg (sq_nonneg _) hq.le) hC
  have h3 := hK y
  have e3 : 2 * (C * Kq) * heatFlowDensity π (2 * t) y
      = 2 * (C * (Kq * heatFlowDensity π (2 * t) y)) := by ring
  rw [e3]
  linarith

/-- Fields `tendsto_atBot` / `tendsto_atTop` for warm laws: for `t > 0` the boundary flux
`p_t'(log(p_t/q_t) + 1) - (p_t/q_t) q_t'` tends to `0` along any filter on which
`(y - x)² → ∞` for every `x`. -/
theorem tendsto_klFlux_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => x ^ 2) ρ) (hmomπ : Integrable (fun x => x ^ 2) π) {t : ℝ}
    (ht : 0 < t) {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : ∀ x, Tendsto (fun y => (y - x) ^ 2) l atTop) :
    Tendsto (klFlux (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t) l
      (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_heatFlow_le ρ ht le_rfl
  obtain ⟨Kq, hKq0, hKq⟩ := exists_heatFlow_le π ht le_rfl
  obtain ⟨Ap, hAp⟩ := exists_abs_log_heatFlowDensity_le ρ ht le_rfl
  obtain ⟨Aq, hAq⟩ := exists_abs_log_heatFlowDensity_le π ht le_rfl
  have hAp0 := nonneg_of_abs_log_le (hAp t ⟨le_rfl, le_rfl⟩ 0)
  have hAq0 := nonneg_of_abs_log_le (hAq t ⟨le_rfl, le_rfl⟩ 0)
  set M := K * (Ap + Aq + 1)
  have hlim1 := (tendsto_one_add_sq_mul_heatFlowDensity ρ hmom (show 0 < 2 * t by linarith)
    hl).const_mul M
  have hlim2 := (tendsto_one_add_sq_mul_heatFlowDensity π hmomπ (show 0 < 2 * t by linarith)
    hl).const_mul (C * Kq)
  have hlim := hlim1.add hlim2
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine squeeze_zero_norm (fun y => ?_) hlim
  have hp := heatFlowDensity_pos ρ ht y
  have hq := heatFlowDensity_pos π ht y
  have hU := heatFlowDensity_div_le_of_warm ρ π hC hwarm ht y
  have hU0 : 0 ≤ heatFlowDensity ρ t y / heatFlowDensity π t y := (div_pos hp hq).le
  obtain ⟨-, hK2, -⟩ := hK t ⟨le_rfl, le_rfl⟩ y
  obtain ⟨-, hKq2, -⟩ := hKq t ⟨le_rfl, le_rfl⟩ y
  have hL := abs_log_div_add_one_le hp hq (hAp t ⟨le_rfl, le_rfl⟩ y) (hAq t ⟨le_rfl, le_rfl⟩ y)
  set P2 := heatFlowDensity ρ (2 * t) y
  set Q2 := heatFlowDensity π (2 * t) y
  have hP2 : 0 ≤ P2 := (heatFlowDensity_pos ρ (by positivity) y).le
  have hQ2 : 0 ≤ Q2 := (heatFlowDensity_pos π (by positivity) y).le
  have hy : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have T1 : |heatFlowD1 ρ t y * (Real.log (heatFlowDensity ρ t y / heatFlowDensity π t y) + 1)|
      ≤ K * P2 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul hK2 hL (abs_nonneg _) (by positivity)
  have T2 : |heatFlowDensity ρ t y / heatFlowDensity π t y * heatFlowD1 π t y|
      ≤ C * Kq * ((1 + y ^ 2) * Q2) := by
    rw [abs_mul, abs_of_nonneg hU0]
    calc heatFlowDensity ρ t y / heatFlowDensity π t y * |heatFlowD1 π t y|
        ≤ C * (Kq * Q2) := mul_le_mul hU hKq2 (abs_nonneg _) hC
      _ ≤ C * (Kq * ((1 + y ^ 2) * Q2)) := by
          gcongr
          nlinarith
      _ = _ := by ring
  rw [Real.norm_eq_abs]
  unfold klFlux
  have := abs_sub (heatFlowD1 ρ t y * (Real.log (heatFlowDensity ρ t y /
    heatFlowDensity π t y) + 1)) (heatFlowDensity ρ t y / heatFlowDensity π t y *
    heatFlowD1 π t y)
  have e : M * ((1 + y ^ 2) * P2) = K * P2 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by
    simp only [M]; ring
  rw [e]
  linarith

/-- **De Bruijn regularity for warm laws (Verified).** For probability measures `ρ, π` on `ℝ`
with `ρ ≤ C • π` (`C ≥ 0`) and `∫ x² dπ < ∞`, all hypotheses of `HeatFlowRegular` hold at every
positive time: `HeatFlowRegular ρ π (Ioi 0)`. -/
theorem heatFlowRegular_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmomπ : Integrable (fun x => x ^ 2) π) : HeatFlowRegular ρ π (Ioi 0) :=
  have hmom := integrable_sq_of_warm ρ π hwarm hmomπ
  { isOpen := isOpen_Ioi
    subset_Ioi := subset_rfl
    integrable_kl := fun _ ht => integrable_klIntegrand ρ π hmom ht
    dominated := fun _ ht => dominated_klRate_of_warm ρ π hC hwarm hmom ht
    integrable_fisher := fun _ ht => integrable_fisherIntegrand_of_warm ρ π hC hwarm ht
    tendsto_atBot := fun _ ht =>
      tendsto_klFlux_of_warm ρ π hC hwarm hmom hmomπ ht tendsto_sq_sub_atBot
    tendsto_atTop := fun _ ht =>
      tendsto_klFlux_of_warm ρ π hC hwarm hmom hmomπ ht tendsto_sq_sub_atTop }

end Warm

end FormalizeSampling.HeatFlowRegularityWarm
