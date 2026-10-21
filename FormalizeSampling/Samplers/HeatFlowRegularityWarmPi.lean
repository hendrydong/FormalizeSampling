module

public import FormalizeSampling.Foundations.HeatFlowRegularityPerturbedPi

/-!
# Regularity of the isotropic heat flow for warm laws against a general target

Status: **Verified** (no named hypotheses). `d`-dimensional counterpart of
`Samplers/HeatFlowRegularityWarm.lean`.

For probability measures `ρ, π` on `Fin d → ℝ` with `ρ ≤ C • π` (a **warm** law) and a target
with finite second moment `∫ ∑ᵢ xᵢ² dπ < ∞`, every field of
`HeatFlowDeBruijnPi.HeatFlowRegularPi ρ π (Ioi 0)` is proved; no posterior second-moment bound
on `π` is needed.

Notation (as in `HeatFlowRegularityPi`): `p_r = heatFlowDensityPi ρ r`,
`q_r = heatFlowDensityPi π r`, gradients `heatFlowGradPi`, Hessians `heatFlowHessPi`, and the
integrable envelopes `E^ρ_c = envBound ρ c`, `E^π_c = envBound π c`.

Proof strategy. Warmness gives `p_r ≤ C q_r` (`heatFlowDensityPi_le_of_warm`), so
`U = p_r/q_r ≤ C`. Every `π`-term of a de Bruijn integrand is `U · ∂ᵢq_r`, `U · ∂ᵢ²q_r`,
`U · Δq_r` or `p_r (∂ᵢq_r/q_r)² = U (∂ᵢq_r)²/q_r`, hence at most `C` times the `π`-side envelope
bounds of `HeatFlowRegularityPi` (`≤ K E^π_{2b}` on `[a, b]`, valid for every `π` with a second
moment). The `ρ`-terms are bounded as in `HeatFlowRegularityPerturbedPi`, with the second moment
of `ρ` inherited from `π`. Every integrand is thus `≤ A E^ρ_{2b} + B E^π_{2b}`.

## Main results

* `heatFlowDensityPi_le_of_warm`: `ρ ≤ C • π` gives `p_r(y) ≤ C q_r(y)`.
* `integrable_sum_sq_of_warm`: a warm law inherits the second moment of `π`.
* `heatFlowRegularPi_of_warm`: `HeatFlowRegularPi ρ π (Ioi 0)` for `ρ ≤ C • π` and
  `∫ ∑ᵢ xᵢ² dπ < ∞`.

## Not proved here

* Non-warm `ρ` (then `p_r/q_r` is unbounded and ratio bounds on `∇q_r/q_r`, `∇²q_r/q_r` are
  needed, cf. `HeatFlowRegularityPerturbedPi.PosteriorSecondMomentBoundPi`).
* Targets without a second moment.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.HeatFlowRegularityWarmPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi FormalizeSampling.HeatFlowRegularityPi
  FormalizeSampling.HeatFlowRegularityPerturbedPi

variable {d : ℕ}

section Warm

variable {ρ π : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {C : ℝ}

omit [IsProbabilityMeasure ρ] in
/-- **Warmness along the heat flow.** If `ρ ≤ C • π` (`C ≥ 0`), then for `t > 0`,
`p_t(y) ≤ C q_t(y)` for every `y`. -/
theorem heatFlowDensityPi_le_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π) {t : ℝ}
    (ht : 0 < t) (y : Fin d → ℝ) : heatFlowDensityPi ρ t y ≤ C * heatFlowDensityPi π t y := by
  have hi := integrable_heatDensityPi_comp_sub π ht y
  calc heatFlowDensityPi ρ t y = ∫ x, heatDensityPi t (y - x) ∂ρ := rfl
    _ ≤ ∫ x, heatDensityPi t (y - x) ∂(ENNReal.ofReal C • π) :=
        integral_mono_measure hwarm (Eventually.of_forall fun x => (heatDensityPi_pos ht _).le)
          (hi.smul_measure ENNReal.ofReal_ne_top)
    _ = C * heatFlowDensityPi π t y := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]; rfl

omit [IsProbabilityMeasure ρ] in
/-- The heat-flow ratio of a `C`-warm law is bounded: `0 ≤ p_t(y) / q_t(y) ≤ C` (`t > 0`). -/
theorem heatFlowDensityPi_div_le_of_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    heatFlowDensityPi ρ t y / heatFlowDensityPi π t y ≤ C := by
  rw [div_le_iff₀ (heatFlowDensityPi_pos π ht y)]
  exact heatFlowDensityPi_le_of_warm hC hwarm ht y

omit [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] in
/-- A law that is `C`-warm for `π` inherits the second moment of `π`. -/
theorem integrable_sum_sq_of_warm (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) π) : Integrable (fun x => ∑ i, x i ^ 2) ρ :=
  (hmom.smul_measure ENNReal.ofReal_ne_top).mono_measure hwarm

/-- **Time derivative of the KL integrand, warm case.** For `0 < a ≤ b`:
`|klRate r y| ≤ A E^ρ_{2b}(y) + B E^π_{2b}(y)` on `[a, b]`. -/
theorem exists_abs_klRate_le_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hmomπ : Integrable (fun x => ∑ i, x i ^ 2) π)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ A B, ∀ r ∈ Icc a b, ∀ y,
      |klRate (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowHessPi ρ)
        (heatFlowHessPi π) r y| ≤ A * envBound ρ (2 * b) y + B * envBound π (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  have hK0 := envK_nonneg (d := d) ha (ha.trans_le hab)
  refine ⟨L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b)),
    C * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b)), fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold klRate
  have hX := hL r hr y
  have hΔ := one_add_mul_abs_lap_le hmom ha hr.1 hr.2 y
  have hΔq := one_add_mul_abs_lap_le hmomπ ha hr.1 hr.2 y
  have hU := heatFlowDensityPi_div_le_of_warm hC hwarm hr0 y
  have hU0 : 0 ≤ heatFlowDensityPi ρ r y / heatFlowDensityPi π r y :=
    (div_pos (heatFlowDensityPi_pos ρ hr0 y) (heatFlowDensityPi_pos π hr0 y)).le
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  have hEρ := envBound_nonneg (ρ := ρ) hb2 y
  have hEπ := envBound_nonneg (ρ := π) hb2 y
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1
  set S := ∑ i, y i ^ 2
  set Eρ := envBound ρ (2 * b) y
  set Eπ := envBound π (2 * b) y
  set K := envK d a b
  set Δ := ∑ i, heatFlowHessPi ρ r y i i
  set Δq := ∑ i, heatFlowHessPi π r y i i
  set U := heatFlowDensityPi ρ r y / heatFlowDensityPi π r y
  have hS : 1 ≤ 1 + S := by linarith [sum_sq_nonneg y]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΔX : |Δ * X| ≤ L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * Eρ)) := by
    rw [abs_mul]
    calc |Δ| * |X| ≤ |Δ| * (L * (1 + S)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = L * ((1 + S) * |Δ|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hΔ hL0
  have hR : |U * Δq| ≤ C * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * Eπ)) := by
    rw [abs_mul, abs_of_nonneg hU0]
    calc U * |Δq| ≤ C * |Δq| := mul_le_mul_of_nonneg_right hU (abs_nonneg _)
      _ ≤ C * ((1 + S) * |Δq|) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hS) hC
      _ ≤ _ := mul_le_mul_of_nonneg_left hΔq hC
  have hB0 : 0 ≤ C * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * Eπ)) := by positivity
  have hA0 : 0 ≤ L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * Eρ)) := by positivity
  rw [abs_div, abs_two]
  have := abs_sub (Δ * X) (U * Δq)
  have e1 : L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K)) * Eρ
      = L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * Eρ)) := by ring
  have e2 : C * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K)) * Eπ
      = C * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * Eπ)) := by ring
  rw [e1, e2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Relative score, one coordinate, warm case.** For `0 < a ≤ b`:
`p_r (∂ᵢ log(p_r/q_r))² ≤ A E^ρ_{2b} + B E^π_{2b}` on `[a, b]`. -/
theorem exists_mul_relScore_sq_le_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hmomπ : Integrable (fun x => ∑ i, x i ^ 2) π)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ∃ A B, ∀ r ∈ Icc a b, ∀ y i,
      heatFlowDensityPi ρ r y * relScore (heatFlowDensityPi ρ) (heatFlowDensityPi π)
        (heatFlowGradPi ρ) (heatFlowGradPi π) r y i ^ 2
        ≤ A * envBound ρ (2 * b) y + B * envBound π (2 * b) y := by
  refine ⟨2 * (2 * a⁻¹ ^ 2 * envK d a b), 2 * C * (2 * a⁻¹ ^ 2 * envK d a b),
    fun r hr y i => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold relScore
  have hP := heatFlowDensityPi_pos ρ hr0 y
  have hQ := heatFlowDensityPi_pos π hr0 y
  have hG := sq_heatFlowGradPi_div_le_envBound hmom ha hr.1 hr.2 y i
  have hGq := sq_heatFlowGradPi_div_le_envBound hmomπ ha hr.1 hr.2 y i
  have hU := heatFlowDensityPi_div_le_of_warm hC hwarm hr0 y
  set A := heatFlowGradPi ρ r y i
  set P := heatFlowDensityPi ρ r y
  set Q := heatFlowDensityPi π r y
  set g := heatFlowGradPi π r y i
  set w := g / Q
  set Eρ := envBound ρ (2 * b) y
  set Eπ := envBound π (2 * b) y
  set K := envK d a b
  have hPA : P * (A / P) ^ 2 = A ^ 2 / P := by field_simp
  have hsq : (A / P - w) ^ 2 ≤ 2 * (A / P) ^ 2 + 2 * w ^ 2 := by
    nlinarith [sq_nonneg (A / P + w)]
  have hPw : P * w ^ 2 ≤ C * (2 * a⁻¹ ^ 2 * K * Eπ) := by
    have e : P * w ^ 2 = P / Q * (g ^ 2 / Q) := by simp only [w]; field_simp
    rw [e]
    exact mul_le_mul hU hGq (div_nonneg (sq_nonneg _) hQ.le) hC
  calc P * (A / P - w) ^ 2 ≤ P * (2 * (A / P) ^ 2 + 2 * w ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hP.le
    _ = 2 * (A ^ 2 / P) + 2 * (P * w ^ 2) := by rw [← hPA]; ring
    _ ≤ 2 * (2 * a⁻¹ ^ 2 * K * Eρ) + 2 * (C * (2 * a⁻¹ ^ 2 * K * Eπ)) := by linarith
    _ = _ := by ring

/-- **Relative Fisher integrand, warm case.** For `0 < a ≤ b`:
`|p_r |∇ log(p_r/q_r)|²| ≤ A E^ρ_{2b} + B E^π_{2b}` on `[a, b]`. -/
theorem exists_abs_fisherIntegrand_le_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hmomπ : Integrable (fun x => ∑ i, x i ^ 2) π)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ A B, ∀ r ∈ Icc a b, ∀ y,
      |fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
        (heatFlowGradPi ρ) (heatFlowGradPi π) r y|
        ≤ A * envBound ρ (2 * b) y + B * envBound π (2 * b) y := by
  obtain ⟨A, B, hAB⟩ := exists_mul_relScore_sq_le_warm hC hwarm hmom hmomπ ha hab
  refine ⟨d * A, d * B, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have e : fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
      (heatFlowGradPi ρ) (heatFlowGradPi π) r y = ∑ i, heatFlowDensityPi ρ r y *
        relScore (heatFlowDensityPi ρ) (heatFlowDensityPi π)
          (heatFlowGradPi ρ) (heatFlowGradPi π) r y i ^ 2 := by
    rw [fisherIntegrand, dotProduct, Finset.mul_sum]; simp only [sq]
  rw [e, abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg hP (sq_nonneg _))]
  calc _ ≤ ∑ _i : Fin d, (A * envBound ρ (2 * b) y + B * envBound π (2 * b) y) :=
        Finset.sum_le_sum fun i _ => hAB r hr y i
    _ = _ := by simp; ring

/-- **KL flux, warm case.** For `0 < a ≤ b`:
`|klFlux r i y| ≤ A E^ρ_{2b}(y) + B E^π_{2b}(y)` on `[a, b]`. -/
theorem exists_abs_klFlux_le_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hmomπ : Integrable (fun x => ∑ i, x i ^ 2) π)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ A B, ∀ r ∈ Icc a b, ∀ i y,
      |klFlux (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
        (heatFlowGradPi π) r i y| ≤ A * envBound ρ (2 * b) y + B * envBound π (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  refine ⟨L * (2 * a⁻¹ * envK d a b), C * (2 * a⁻¹ * envK d a b), fun r hr i y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold klFlux
  have hX := hL r hr y
  have hG := one_add_mul_abs_heatFlowGradPi_le hmom ha hr.1 hr.2 y i
  have hGq := one_add_mul_abs_heatFlowGradPi_le hmomπ ha hr.1 hr.2 y i
  have hU := heatFlowDensityPi_div_le_of_warm hC hwarm hr0 y
  have hU0 : 0 ≤ heatFlowDensityPi ρ r y / heatFlowDensityPi π r y :=
    (div_pos (heatFlowDensityPi_pos ρ hr0 y) (heatFlowDensityPi_pos π hr0 y)).le
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1
  set S := ∑ i, y i ^ 2
  set K := envK d a b
  set G := heatFlowGradPi ρ r y i
  set g := heatFlowGradPi π r y i
  set U := heatFlowDensityPi ρ r y / heatFlowDensityPi π r y
  have hS : 1 ≤ 1 + S := by linarith [sum_sq_nonneg y]
  have h1 : |G * X| ≤ L * (2 * a⁻¹ * K * envBound ρ (2 * b) y) := by
    rw [abs_mul]
    calc |G| * |X| ≤ |G| * (L * (1 + S)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = L * ((1 + S) * |G|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hG hL0
  have h2 : |U * g| ≤ C * (2 * a⁻¹ * K * envBound π (2 * b) y) := by
    rw [abs_mul, abs_of_nonneg hU0]
    calc U * |g| ≤ C * |g| := mul_le_mul_of_nonneg_right hU (abs_nonneg _)
      _ ≤ C * ((1 + S) * |g|) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hS) hC
      _ ≤ _ := mul_le_mul_of_nonneg_left hGq hC
  calc |G * X - U * g| ≤ |G * X| + |U * g| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **Divergence terms of the KL flux, warm case.** For `0 < a ≤ b`:
`|klFluxDeriv r i y| ≤ A E^ρ_{2b}(y) + B E^π_{2b}(y)` on `[a, b]`. -/
theorem exists_abs_klFluxDeriv_le_warm (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hmomπ : Integrable (fun x => ∑ i, x i ^ 2) π)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ A B, ∀ r ∈ Icc a b, ∀ i y,
      |klFluxDeriv (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
        (heatFlowGradPi π) (heatFlowHessPi ρ) (heatFlowHessPi π) r i y|
        ≤ A * envBound ρ (2 * b) y + B * envBound π (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  obtain ⟨A, B, hAB⟩ := exists_mul_relScore_sq_le_warm hC hwarm hmom hmomπ ha hab
  refine ⟨L * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b) + A,
    C * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b) + B, fun r hr i y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hRS := hAB r hr y i
  unfold klFluxDeriv
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have hX := hL r hr y
  have hH := one_add_mul_abs_heatFlowHessPi_le hmom ha hr.1 hr.2 y i
  have hHq := one_add_mul_abs_heatFlowHessPi_le hmomπ ha hr.1 hr.2 y i
  have hU := heatFlowDensityPi_div_le_of_warm hC hwarm hr0 y
  have hU0 : 0 ≤ heatFlowDensityPi ρ r y / heatFlowDensityPi π r y :=
    (div_pos (heatFlowDensityPi_pos ρ hr0 y) (heatFlowDensityPi_pos π hr0 y)).le
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1
  set S := ∑ i, y i ^ 2
  set K := envK d a b
  set H := heatFlowHessPi ρ r y i i
  set h := heatFlowHessPi π r y i i
  set P := heatFlowDensityPi ρ r y
  set U := heatFlowDensityPi ρ r y / heatFlowDensityPi π r y
  set R := relScore (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
    (heatFlowGradPi π) r y i
  have hS : 1 ≤ 1 + S := by linarith [sum_sq_nonneg y]
  have h1 : |H * X| ≤ L * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * envBound ρ (2 * b) y) := by
    rw [abs_mul]
    calc |H| * |X| ≤ |H| * (L * (1 + S)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = L * ((1 + S) * |H|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hH hL0
  have h2 : |U * h| ≤ C * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * envBound π (2 * b) y) := by
    rw [abs_mul, abs_of_nonneg hU0]
    calc U * |h| ≤ C * |h| := mul_le_mul_of_nonneg_right hU (abs_nonneg _)
      _ ≤ C * ((1 + S) * |h|) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hS) hC
      _ ≤ _ := mul_le_mul_of_nonneg_left hHq hC
  have h3 : |P * R ^ 2| ≤ A * envBound ρ (2 * b) y + B * envBound π (2 * b) y := by
    rw [abs_of_nonneg (mul_nonneg hP (sq_nonneg _))]; exact hRS
  calc |H * X - U * h + P * R ^ 2| ≤ |H * X| + |U * h| + |P * R ^ 2| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end Warm

/-- **De Bruijn regularity for warm laws (Verified).** For probability measures `ρ, π` on
`Fin d → ℝ` with `ρ ≤ C • π` (`C ≥ 0`) and `∫ ∑ᵢ xᵢ² dπ < ∞`, all hypotheses of
`HeatFlowRegularPi` hold at every positive time: `HeatFlowRegularPi ρ π (Ioi 0)`. -/
theorem heatFlowRegularPi_of_warm (ρ π : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {C : ℝ} (hC : 0 ≤ C) (hwarm : ρ ≤ ENNReal.ofReal C • π)
    (hmomπ : Integrable (fun x => ∑ i, x i ^ 2) π) : HeatFlowRegularPi ρ π (Ioi 0) := by
  have hmom := integrable_sum_sq_of_warm hwarm hmomπ
  have key : ∀ {t : ℝ}, 0 < t → ∀ {F : (Fin d → ℝ) → ℝ}, Measurable F →
      (∃ A B, ∀ y, |F y| ≤ A * envBound ρ (2 * t) y + B * envBound π (2 * t) y) →
      Integrable F := by
    intro t ht F hF ⟨A, B, hAB⟩
    exact (((integrable_envBound hmom (by positivity : 0 < 2 * t)).const_mul A).add
      ((integrable_envBound hmomπ (by positivity : 0 < 2 * t)).const_mul B)).mono'
      hF.aestronglyMeasurable (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hAB y)
  have mem : ∀ {t : ℝ}, t ∈ Icc t t := fun {t} => ⟨le_rfl, le_rfl⟩
  have hPm : ∀ (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ}, 0 < t →
      Measurable (heatFlowDensityPi μ t) := fun μ _ t ht =>
    (continuous_heatFlowDensityPi μ ht).measurable
  have hGm : ∀ (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ}, 0 < t →
      ∀ i, Measurable fun y => heatFlowGradPi μ t y i := fun μ _ t ht i =>
    (continuous_heatFlowGradPi μ ht i).measurable
  have hHm : ∀ (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ}, 0 < t →
      ∀ i j, Measurable fun y => heatFlowHessPi μ t y i j := fun μ _ t ht i j =>
    (continuous_heatFlowHessPi ht i j).measurable
  refine ⟨isOpen_Ioi, subset_rfl, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht i => ?_, fun t ht i => ?_⟩
  · obtain ⟨A, hA⟩ := exists_abs_klIntegrand_le_any (π := π) hmom ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    exact key ht (by unfold klIntegrand; fun_prop) ⟨A, 0, fun y => by
      rw [zero_mul, add_zero]; exact hA t mem y⟩
  · have ht0 : 0 < t := ht
    obtain ⟨A, B, hAB⟩ := exists_abs_klRate_le_warm hC hwarm hmom hmomπ (a := t / 2)
      (b := 2 * t) (by positivity) (by linarith)
    refine ⟨fun y => A * envBound ρ (2 * (2 * t)) y + B * envBound π (2 * (2 * t)) y,
      ((integrable_envBound hmom (by positivity)).const_mul A).add
        ((integrable_envBound hmomπ (by positivity)).const_mul B), ?_⟩
    filter_upwards [Ioo_mem_nhds (by linarith : t / 2 < t) (by linarith : t < 2 * t)] with r hr y
    exact hAB r ⟨hr.1.le, hr.2.le⟩ y
  · obtain ⟨A, B, hAB⟩ := exists_abs_fisherIntegrand_le_warm hC hwarm hmom hmomπ ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    have h3 := hGm ρ ht; have h4 := hGm π ht
    exact key ht (by unfold fisherIntegrand relScore; simp only [dotProduct]; fun_prop)
      ⟨A, B, hAB t mem⟩
  · obtain ⟨A, B, hAB⟩ := exists_abs_klFlux_le_warm hC hwarm hmom hmomπ ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    have h3 := hGm ρ ht; have h4 := hGm π ht
    exact key ht (by unfold klFlux; fun_prop) ⟨A, B, fun y => hAB t mem i y⟩
  · obtain ⟨A, B, hAB⟩ := exists_abs_klFluxDeriv_le_warm hC hwarm hmom hmomπ ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    have h3 := hGm ρ ht; have h4 := hGm π ht
    have h5 := hHm ρ ht; have h6 := hHm π ht
    exact key ht (by unfold klFluxDeriv relScore; fun_prop) ⟨A, B, fun y => hAB t mem i y⟩

end FormalizeSampling.HeatFlowRegularityWarmPi
