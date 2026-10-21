module

public import FormalizeSampling.Foundations.GaussianLSIBasics

/-!
# Pointwise bounds on the heat flow of a measure with finite second moment

Status: **Verified**. The `ρ`-side estimates behind the de Bruijn regularity hypotheses
`HeatFlowDeBruijn.HeatFlowRegular ρ π (Ioi 0)` for a probability measure `ρ` on `ℝ` with finite
second moment. They are combined with a bound on the target side in
`Foundations/HeatFlowRegularityPerturbed.lean` (targets with a posterior second-moment bound, among
them `N(0, v)`: `heatFlowRegular_gaussianReal`, stated there in this namespace) and
`Samplers/HeatFlowRegularityWarm.lean` (warm starts).

Notation (as in `HeatFlowDeBruijn`): `φ_t = heatDensity t`, `p_t = heatFlowDensity ρ t = ρ * φ_t`
with derivatives `p_t' = heatFlowD1 ρ t`, `p_t'' = heatFlowD2 ρ t`.

Proof strategy (all bounds are crude):
* `exists_heatDensity_le`: for `r ∈ [a, b] ⊂ (0, ∞)`, `(1 + z²) φ_r(z) ≤ K φ_{2b}(z)`; hence
  `p_r, |p_r'|, |p_r''| ≤ K p_{2b}` (`exists_heatFlow_le`).
* `integrable_one_add_sq_mul_heatFlowDensity`, `tendsto_one_add_sq_mul_heatFlowDensity`:
  `(1 + y²) p_B(y)` is integrable and tends to `0` at `±∞` (Fubini, resp. dominated convergence,
  using `∫ x² dρ < ∞`).
* `exists_abs_log_heatFlowDensity_le`: `|log p_r(y)| ≤ A (1 + y²)` uniformly for `r ∈ [a, b]`
  (upper bound `p_r ≤ (2πa)^{-1/2}`, lower bound from the mass of `ρ` on some `[-R, R]`).
* `sq_heatFlowD1_div_le`: Cauchy–Schwarz `p_t'² / p_t ≤ ∫ ((y - x)/t)² φ_t(y - x) dρ(x)`.

## Main results

* `exists_heatFlow_le`, `integrable_one_add_sq_mul_heatFlowDensity`,
  `tendsto_one_add_sq_mul_heatFlowDensity`, `exists_abs_log_heatFlowDensity_le`,
  `sq_heatFlowD1_div_le`, `exists_sq_heatFlowD1_div_le`: the bounds above.
* `integrable_klIntegrand`: the field `integrable_kl` of `HeatFlowRegular` for every probability
  target `π`.
* `heatFlowD2_gaussianReal`: `p_t'' = φ_{v+t}''` for `ρ = N(0, v)`.

## Not proved here

* The remaining fields of `HeatFlowRegular` (domination of the KL rate, Fisher integrability,
  vanishing flux) need a bound on the target side: `Foundations/HeatFlowRegularityPerturbed.lean`.
* The Gaussian LSI and PX-2 themselves: `Foundations/GaussianLSI.lean` (the LSI at time `0`:
  `Foundations/GaussianLSIZero.lean`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction
open FormalizeSampling.GaussianLSI

namespace FormalizeSampling.HeatFlowRegularity

/-! ### Pointwise bounds on the heat kernel -/

/-- Locally uniform Gaussian domination of the heat kernel: for `0 < a ≤ b` there is `K ≥ 0`
with `(1 + z²) φ_r(z) ≤ K φ_{2b}(z)` for all `r ∈ [a, b]` and all `z`. -/
theorem exists_heatDensity_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K, 0 ≤ K ∧ ∀ r ∈ Icc a b, ∀ z, (1 + z ^ 2) * heatDensity r z ≤ K * heatDensity (2 * b) z := by
  have hb : 0 < b := ha.trans_le hab
  have hsa : 0 < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
  have hsb : 0 < Real.sqrt (2 * Real.pi * (2 * b)) := Real.sqrt_pos.2 (by positivity)
  refine ⟨(Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 4 * b) * Real.sqrt (2 * Real.pi * (2 * b)),
    by positivity, fun r hr z => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  set E := Real.exp (-z ^ 2 / (2 * (2 * b))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ z ^ 2 / (2 * (2 * b)) := by positivity
    rw [neg_div]; linarith)
  have hzE : z ^ 2 * E ≤ 2 * (2 * b) := sq_mul_exp_le (by positivity) z
  have hexp : Real.exp (-z ^ 2 / (2 * r)) ≤ E * E := by
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : z ^ 2 / (2 * b) ≤ z ^ 2 / (2 * r) :=
      div_le_div_of_nonneg_left (sq_nonneg z) (by positivity) (by linarith [hr.2])
    have h2 : -z ^ 2 / (2 * (2 * b)) + -z ^ 2 / (2 * (2 * b)) = -(z ^ 2 / (2 * b)) := by
      field_simp; ring
    rw [h2, neg_div]; linarith
  have hsq : (Real.sqrt (2 * Real.pi * r))⁻¹ ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ :=
    inv_anti₀ hsa (Real.sqrt_le_sqrt (by nlinarith [hr.1, Real.pi_pos]))
  have hpoly : (1 + z ^ 2) * (E * E) ≤ (1 + 4 * b) * E := by nlinarith
  unfold heatDensity
  rw [← hE]
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi * r))⁻¹ := by positivity
  calc (1 + z ^ 2) * ((Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-z ^ 2 / (2 * r)))
      ≤ (1 + z ^ 2) * ((Real.sqrt (2 * Real.pi * a))⁻¹ * (E * E)) := by gcongr
    _ = (Real.sqrt (2 * Real.pi * a))⁻¹ * ((1 + z ^ 2) * (E * E)) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ * ((1 + 4 * b) * E) := by gcongr
    _ = _ := by field_simp

/-- Bounds on the heat kernel and its space derivatives by `(1 + z²) φ_r(z)`, for `r ≥ a > 0`:
`|φ_r'(z)| ≤ (1/a) (1 + z²) φ_r(z)` and `|φ_r''(z)| ≤ (1/a² + 1/a) (1 + z²) φ_r(z)`. -/
theorem abs_heatDensityD_le {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (z : ℝ) :
    |heatDensityD1 r z| ≤ 1 / a * ((1 + z ^ 2) * heatDensity r z) ∧
      |heatDensityD2 r z| ≤ (1 / a ^ 2 + 1 / a) * ((1 + z ^ 2) * heatDensity r z) := by
  have hr : 0 < r := ha.trans_le har
  have hφ := (heatDensity_pos hr z).le
  have hz : |z| ≤ 1 + z ^ 2 := by nlinarith [abs_nonneg z, sq_abs z]
  have h1r : 1 / r ≤ 1 / a := one_div_le_one_div_of_le ha har
  have h2r : 1 / r ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  constructor
  · unfold heatDensityD1
    rw [abs_mul, abs_neg, abs_div, abs_of_pos hr, abs_of_nonneg hφ]
    have : |z| / r ≤ 1 / a * (1 + z ^ 2) := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul h1r hz (abs_nonneg _) (by positivity)
    calc |z| / r * heatDensity r z ≤ 1 / a * (1 + z ^ 2) * heatDensity r z := by gcongr
      _ = _ := by ring
  · unfold heatDensityD2
    rw [abs_mul, abs_of_nonneg hφ]
    have : |z ^ 2 / r ^ 2 - 1 / r| ≤ (1 / a ^ 2 + 1 / a) * (1 + z ^ 2) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have e : z ^ 2 / r ^ 2 = z ^ 2 * (1 / r ^ 2) := by ring
      rw [e]
      have : z ^ 2 * (1 / r ^ 2) ≤ z ^ 2 * (1 / a ^ 2) :=
        mul_le_mul_of_nonneg_left h2r (sq_nonneg z)
      have : 0 ≤ z ^ 2 * (1 / a) := by positivity
      have : 0 ≤ 1 / a ^ 2 := by positivity
      nlinarith
    calc |z ^ 2 / r ^ 2 - 1 / r| * heatDensity r z
        ≤ (1 / a ^ 2 + 1 / a) * (1 + z ^ 2) * heatDensity r z := by gcongr
      _ = _ := by ring

/-- `y ↦ heatDensity t (f y)` tends to `0` along any filter on which `f y ^ 2 → ∞`. -/
theorem tendsto_heatDensity_comp {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {l : Filter ℝ}
    (hf : Tendsto (fun y => f y ^ 2) l atTop) :
    Tendsto (fun y => heatDensity t (f y)) l (𝓝 0) := by
  unfold heatDensity
  have h : Tendsto (fun y => -f y ^ 2 / (2 * t)) l atBot := by
    simp_rw [neg_div]
    exact tendsto_neg_atTop_atBot.comp (hf.atTop_div_const (by positivity))
  simpa using (Real.tendsto_exp_atBot.comp h).const_mul (Real.sqrt (2 * Real.pi * t))⁻¹

/-! ### Gaussian convolutions of a probability measure -/

section Conv

variable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ρ] in
/-- For `t > 0`, a fixed `y` and `w` continuous and `ρ`-integrable,
`x ↦ φ_t(y - x) w(x)` is `ρ`-integrable. -/
theorem integrable_heatDensity_mul {t : ℝ} (ht : 0 < t) (y : ℝ) {w : ℝ → ℝ} (hwc : Continuous w)
    (hw : Integrable w ρ) : Integrable (fun x => heatDensity t (y - x) * w x) ρ := by
  refine (hw.norm.const_mul (Real.sqrt (2 * Real.pi * t))⁻¹).mono'
    (((continuous_heatDensity t).comp (by fun_prop)).mul hwc).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (heatDensity_pos ht _).le]
  exact mul_le_mul_of_nonneg_right (heatDensity_le ht _) (norm_nonneg _)

/-- For `t > 0` and a fixed `y`, `x ↦ φ_t(y - x)` is `ρ`-integrable. -/
theorem integrable_heatDensity_sub_left {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun x => heatDensity t (y - x)) ρ := by
  simpa using integrable_heatDensity_mul ρ ht y continuous_const (integrable_const (1 : ℝ))

/-- If `|f z| ≤ K φ_B(z)` for all `z` (`B > 0`), then `|∫ f(y - x) dρ(x)| ≤ K p_B(y)`. -/
theorem abs_integral_le_heatFlowDensity {f : ℝ → ℝ} {K B : ℝ} (hB : 0 < B)
    (hf : ∀ z, |f z| ≤ K * heatDensity B z) (y : ℝ) :
    |∫ x, f (y - x) ∂ρ| ≤ K * heatFlowDensity ρ B y := by
  unfold heatFlowDensity
  rw [← integral_const_mul]
  exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => abs_nonneg _)
    ((integrable_heatDensity_sub_left ρ hB y).const_mul K) (Eventually.of_forall fun x => hf _))

/-- Locally uniform domination of the heat-flow density and its space derivatives: for
`0 < a ≤ b` there is `K ≥ 0` such that for all `r ∈ [a, b]` and `y`, each of `p_r(y)`,
`|p_r'(y)|`, `|p_r''(y)|` is at most `K p_{2b}(y)`. -/
theorem exists_heatFlow_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K, 0 ≤ K ∧ ∀ r ∈ Icc a b, ∀ y,
      heatFlowDensity ρ r y ≤ K * heatFlowDensity ρ (2 * b) y ∧
      |heatFlowD1 ρ r y| ≤ K * heatFlowDensity ρ (2 * b) y ∧
      |heatFlowD2 ρ r y| ≤ K * heatFlowDensity ρ (2 * b) y := by
  obtain ⟨K, hK, hKb⟩ := exists_heatDensity_le ha hab
  have hb : 0 < 2 * b := by linarith
  set K' := K * (1 + 1 / a + 1 / a ^ 2) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨K', hK'0, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hbase : ∀ z, (1 + z ^ 2) * heatDensity r z ≤ K * heatDensity (2 * b) z := hKb r hr
  have hφb : ∀ z, 0 ≤ heatDensity (2 * b) z := fun z => (heatDensity_pos hb z).le
  have hia : 0 ≤ 1 / a := by positivity
  have hia2 : 0 ≤ 1 / a ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := abs_integral_le_heatFlowDensity ρ (f := heatDensity r) (K := K') hb (fun z => by
      rw [abs_of_nonneg (heatDensity_pos hr0 z).le]
      have h1 : heatDensity r z ≤ (1 + z ^ 2) * heatDensity r z := by
        nlinarith [heatDensity_pos hr0 z, sq_nonneg z]
      have h2 : K * heatDensity (2 * b) z ≤ K' * heatDensity (2 * b) z := by
        rw [hK']; nlinarith [mul_nonneg (mul_nonneg hK (add_nonneg hia hia2)) (hφb z)]
      linarith [hbase z]) y
    exact (le_abs_self _).trans this
  · refine abs_integral_le_heatFlowDensity ρ (f := heatDensityD1 r) hb (fun z => ?_) y
    have h1 := (abs_heatDensityD_le ha hr.1 z).1
    have h2 : 1 / a * ((1 + z ^ 2) * heatDensity r z) ≤ 1 / a * (K * heatDensity (2 * b) z) :=
      mul_le_mul_of_nonneg_left (hbase z) hia
    have h3 : 1 / a * (K * heatDensity (2 * b) z) ≤ K' * heatDensity (2 * b) z := by
      rw [hK']; nlinarith [mul_nonneg (mul_nonneg hK (by positivity : (0 : ℝ) ≤ 1 + 1 / a ^ 2))
        (hφb z)]
    linarith
  · refine abs_integral_le_heatFlowDensity ρ (f := heatDensityD2 r) hb (fun z => ?_) y
    have h1 := (abs_heatDensityD_le ha hr.1 z).2
    have h2 : (1 / a ^ 2 + 1 / a) * ((1 + z ^ 2) * heatDensity r z)
        ≤ (1 / a ^ 2 + 1 / a) * (K * heatDensity (2 * b) z) :=
      mul_le_mul_of_nonneg_left (hbase z) (by positivity)
    have h3 : (1 / a ^ 2 + 1 / a) * (K * heatDensity (2 * b) z)
        ≤ K' * heatDensity (2 * b) z := by
      rw [hK']; nlinarith [mul_nonneg hK (hφb z)]
    linarith

/-- Lebesgue integrability of a convolution: for `k` continuous and Lebesgue integrable and `w`
continuous and `ρ`-integrable, `y ↦ ∫ k(y - x) w(x) dρ(x)` is Lebesgue integrable (Fubini). -/
theorem integrable_integral_conv {k w : ℝ → ℝ} (hkc : Continuous k) (hk : Integrable k)
    (hwc : Continuous w) (hw : Integrable w ρ) :
    Integrable (fun y => ∫ x, k (y - x) * w x ∂ρ) := by
  have hF : Integrable (fun q : ℝ × ℝ => k (q.1 - q.2) * w q.2) (volume.prod ρ) := by
    rw [integrable_prod_iff' (by fun_prop : Continuous fun q : ℝ × ℝ =>
      k (q.1 - q.2) * w q.2).aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x =>
      show Integrable (fun y => k (y - x) * w x) from (hk.comp_sub_right x).mul_const _, ?_⟩
    have : (fun x => ∫ y, ‖k (y - x) * w x‖) = fun x => (∫ y, ‖k y‖) * ‖w x‖ := by
      funext x
      simp_rw [norm_mul]
      rw [integral_mul_const, integral_sub_right_eq_self (fun y => ‖k y‖)]
    rw [this]
    exact hw.norm.const_mul _
  exact hF.integral_prod_left

omit [IsProbabilityMeasure ρ] in
/-- Dominated convergence for a Gaussian convolution: for `c > 0`, `w` continuous and
`ρ`-integrable and a filter `l` along which `(y - x)² → ∞` for every `x`,
`∫ φ_c(y - x) w(x) dρ(x) → 0` along `l`. -/
theorem tendsto_integral_heatDensity_mul {c : ℝ} (hc : 0 < c) {w : ℝ → ℝ} (hwc : Continuous w)
    (hw : Integrable w ρ) {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : ∀ x, Tendsto (fun y => (y - x) ^ 2) l atTop) :
    Tendsto (fun y => ∫ x, heatDensity c (y - x) * w x ∂ρ) l (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ρ) (l := l)
    (F := fun y x => heatDensity c (y - x) * w x) (f := fun _ => 0)
    (fun x => (Real.sqrt (2 * Real.pi * c))⁻¹ * ‖w x‖)
    (Eventually.of_forall fun y =>
      (((continuous_heatDensity c).comp (by fun_prop)).mul hwc).aestronglyMeasurable)
    (Eventually.of_forall fun y => Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_of_nonneg (heatDensity_pos hc _).le]
      exact mul_le_mul_of_nonneg_right (heatDensity_le hc _) (norm_nonneg _))
    (hw.norm.const_mul _)
    (Eventually.of_forall fun x => by
      simpa using (tendsto_heatDensity_comp hc (hl x)).mul_const (w x))
  simpa using h

/-- `(y - x)² → ∞` as `y → +∞`. -/
theorem tendsto_sq_sub_atTop (x : ℝ) : Tendsto (fun y : ℝ => (y - x) ^ 2) atTop atTop :=
  (tendsto_sub_sq_atTop x).congr fun y => by ring

/-- `(y - x)² → ∞` as `y → -∞`. -/
theorem tendsto_sq_sub_atBot (x : ℝ) : Tendsto (fun y : ℝ => (y - x) ^ 2) atBot atTop :=
  (tendsto_sub_sq_atBot x).congr fun y => by ring

/-- Second-moment bound for the heat-flow density: for `B > 0` there is `K ≥ 0` with
`(1 + y²) p_B(y) ≤ 2K p_{2B}(y) + ∫ φ_B(y - x) 2x² dρ(x)` for all `y`, provided
`∫ x² dρ < ∞`. -/
theorem exists_one_add_sq_mul_heatFlowDensity_le (hmom : Integrable (fun x => x ^ 2) ρ) {B : ℝ}
    (hB : 0 < B) : ∃ K, 0 ≤ K ∧ ∀ y, (1 + y ^ 2) * heatFlowDensity ρ B y
      ≤ 2 * K * heatFlowDensity ρ (2 * B) y + ∫ x, heatDensity B (y - x) * (2 * x ^ 2) ∂ρ := by
  obtain ⟨K, hK, hKb⟩ := exists_heatDensity_le hB le_rfl
  refine ⟨K, hK, fun y => ?_⟩
  have hi1 := integrable_heatDensity_sub_left ρ (show 0 < 2 * B by linarith) y
  have hi2 := integrable_heatDensity_mul ρ hB y (by fun_prop) (hmom.const_mul 2)
  unfold heatFlowDensity
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul _) hi2]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
    mul_nonneg (by positivity) (heatDensity_pos hB _).le) ((hi1.const_mul _).add hi2)
    (Eventually.of_forall fun x => ?_)
  have h1 := hKb B ⟨le_rfl, le_rfl⟩ (y - x)
  have hφ := (heatDensity_pos hB (y - x)).le
  have h2 : 1 + y ^ 2 ≤ 2 * (1 + (y - x) ^ 2) + 2 * x ^ 2 := by nlinarith [sq_nonneg (y - 2 * x)]
  simp only
  nlinarith

/-- For `B > 0` and `∫ x² dρ < ∞`, `y ↦ (1 + y²) p_B(y)` is Lebesgue integrable. -/
theorem integrable_one_add_sq_mul_heatFlowDensity (hmom : Integrable (fun x => x ^ 2) ρ) {B : ℝ}
    (hB : 0 < B) : Integrable (fun y => (1 + y ^ 2) * heatFlowDensity ρ B y) := by
  obtain ⟨K, -, hK⟩ := exists_one_add_sq_mul_heatFlowDensity_le ρ hmom hB
  have hg := integrable_integral_conv ρ (continuous_heatDensity B)
    (by simpa using integrable_heatDensity_sub hB 0) (by fun_prop : Continuous fun x : ℝ =>
      2 * x ^ 2) (hmom.const_mul 2)
  refine (((integrable_heatFlowDensity ρ (show 0 < 2 * B by linarith)).const_mul
    (2 * K)).add hg).mono' ((by fun_prop : Continuous fun y : ℝ => 1 + y ^ 2).mul
    (continuous_heatFlowDensity ρ hB)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (heatFlowDensity_pos ρ hB y).le)]
  exact hK y

/-- For `B > 0` and `∫ x² dρ < ∞`, `(1 + y²) p_B(y) → 0` along any filter on which
`(y - x)² → ∞` for every `x` (e.g. `y → ±∞`). -/
theorem tendsto_one_add_sq_mul_heatFlowDensity (hmom : Integrable (fun x => x ^ 2) ρ) {B : ℝ}
    (hB : 0 < B) {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : ∀ x, Tendsto (fun y => (y - x) ^ 2) l atTop) :
    Tendsto (fun y => (1 + y ^ 2) * heatFlowDensity ρ B y) l (𝓝 0) := by
  obtain ⟨K, -, hK⟩ := exists_one_add_sq_mul_heatFlowDensity_le ρ hmom hB
  have h1 := tendsto_integral_heatDensity_mul ρ (show 0 < 2 * B by linarith) continuous_const
    (integrable_const (1 : ℝ)) hl
  have h2 := tendsto_integral_heatDensity_mul ρ hB (by fun_prop : Continuous fun x : ℝ =>
    2 * x ^ 2) (hmom.const_mul 2) hl
  simp only [mul_one] at h1
  have h3 := (h1.const_mul (2 * K)).add h2
  rw [mul_zero, add_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun y => mul_nonneg (by positivity) (heatFlowDensity_pos ρ hB y).le) hK

end Conv

/-! ### Logarithmic bounds on the heat-flow density -/

section Log

variable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- A probability measure on `ℝ` gives positive mass to some interval `[-R, R]`. -/
theorem exists_measureReal_Icc_pos : ∃ R : ℝ, 0 ≤ R ∧ 0 < ρ.real (Icc (-R) R) := by
  have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := eq_univ_of_forall fun x =>
    mem_iUnion.2 ⟨⌈|x|⌉₊, abs_le.1 (Nat.le_ceil |x|)⟩
  have : ∃ n : ℕ, ρ (Icc (-(n : ℝ)) n) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 := measure_iUnion_null h
    rw [hU] at h0
    simp at h0
  obtain ⟨n, hn⟩ := this
  exact ⟨n, n.cast_nonneg, ENNReal.toReal_pos hn (measure_ne_top _ _)⟩

/-- Locally uniform quadratic bound on `|log p_r|`: for a probability `ρ` and `0 < a ≤ b`
there is `A` with `|log p_r(y)| ≤ A (1 + y²)` for all `r ∈ [a, b]` and `y`. The upper bound
is `p_r ≤ (2π a)^{-1/2}`; the lower bound is `p_r(y) ≥ ρ([-R, R]) (2π b)^{-1/2}
exp(-(y² + R²)/a)`. -/
theorem exists_abs_log_heatFlowDensity_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ A, ∀ r ∈ Icc a b, ∀ y, |Real.log (heatFlowDensity ρ r y)| ≤ A * (1 + y ^ 2) := by
  obtain ⟨R, hR, hm⟩ := exists_measureReal_Icc_pos ρ
  have hb : 0 < b := ha.trans_le hab
  set m := ρ.real (Icc (-R) R)
  set c := (Real.sqrt (2 * Real.pi * b))⁻¹ with hc
  set ca := (Real.sqrt (2 * Real.pi * a))⁻¹ with hca
  have hc0 : 0 < c := by positivity
  have hca0 : 0 < ca := by positivity
  set A := |Real.log ca| + |Real.log (c * m)| + R ^ 2 / a + 1 / a with hA
  refine ⟨A, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hp := heatFlowDensity_pos ρ hr0 y
  -- upper bound
  have hup : heatFlowDensity ρ r y ≤ ca :=
    (heatFlowDensity_le ρ hr0 y).trans (inv_anti₀ (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (by nlinarith [hr.1, Real.pi_pos])))
  have hlogup : Real.log (heatFlowDensity ρ r y) ≤ Real.log ca := Real.log_le_log hp hup
  -- lower bound
  set u := (y ^ 2 + R ^ 2) / a with hu
  have hpt : ∀ x ∈ Icc (-R) R, c * Real.exp (-u) ≤ heatDensity r (y - x) := by
    intro x hx
    unfold heatDensity
    have hx2 : x ^ 2 ≤ R ^ 2 := sq_le_sq' hx.1 hx.2
    have h1 : c ≤ (Real.sqrt (2 * Real.pi * r))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_le_sqrt (by nlinarith [hr.2, Real.pi_pos]))
    have h2 : Real.exp (-u) ≤ Real.exp (-(y - x) ^ 2 / (2 * r)) := by
      apply Real.exp_le_exp.2
      have e1 : (y - x) ^ 2 / (2 * r) ≤ (y - x) ^ 2 / (2 * a) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hr.1])
      have e2 : (y - x) ^ 2 / (2 * a) ≤ u := by
        rw [hu, div_le_div_iff₀ (by positivity) ha]
        nlinarith [sq_nonneg (y + x)]
      rw [neg_div]; linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  have hlow : c * Real.exp (-u) * m ≤ heatFlowDensity ρ r y := by
    have hi := integrable_heatDensity_sub_left ρ hr0 y
    calc c * Real.exp (-u) * m ≤ ∫ x in Icc (-R) R, heatDensity r (y - x) ∂ρ :=
          setIntegral_ge_of_const_le_real measurableSet_Icc (measure_ne_top _ _) hpt
            hi.integrableOn
      _ ≤ _ := setIntegral_le_integral hi
          (Eventually.of_forall fun x => (heatDensity_pos hr0 _).le)
  have hlogl : Real.log (c * m) - u ≤ Real.log (heatFlowDensity ρ r y) := by
    have := Real.log_le_log (by positivity) hlow
    rw [mul_comm c, mul_assoc, Real.log_mul (Real.exp_pos _).ne' (by positivity),
      Real.log_exp] at this
    linarith
  have hA1 : 1 / a ≤ A := by
    have : 0 ≤ R ^ 2 / a := by positivity
    linarith [abs_nonneg (Real.log ca), abs_nonneg (Real.log (c * m))]
  have hA2 : -Real.log (c * m) + R ^ 2 / a ≤ A := by
    have : 0 ≤ 1 / a := by positivity
    linarith [abs_nonneg (Real.log ca), neg_le_abs (Real.log (c * m))]
  have hA3 : Real.log ca ≤ A := by
    have : 0 ≤ 1 / a := by positivity
    have : 0 ≤ R ^ 2 / a := by positivity
    linarith [le_abs_self (Real.log ca), abs_nonneg (Real.log (c * m))]
  have hA0 : 0 ≤ A := (by positivity : (0 : ℝ) ≤ 1 / a).trans hA1
  have hyA : y ^ 2 / a ≤ A * y ^ 2 := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hA1 (sq_nonneg y)
  have hu' : u = R ^ 2 / a + y ^ 2 / a := by rw [hu]; ring
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hA0 (sq_nonneg y)]

end Log

/-! ### Cauchy–Schwarz bound for the score of the heat flow -/

section Score

variable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- For `t > 0` and fixed `y`, `x ↦ (1 + (y - x)²) φ_t(y - x)` is `ρ`-integrable. -/
theorem integrable_one_add_sq_mul_heatDensity {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun x => (1 + (y - x) ^ 2) * heatDensity t (y - x)) ρ := by
  obtain ⟨K, -, hK⟩ := exists_heatDensity_le ht le_rfl
  refine ((integrable_heatDensity_sub_left ρ (show 0 < 2 * t by linarith) y).const_mul K).mono'
    ((by fun_prop : Continuous fun x : ℝ => 1 + (y - x) ^ 2).mul
      ((continuous_heatDensity t).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (heatDensity_pos ht _).le)]
  exact hK t ⟨le_rfl, le_rfl⟩ _

/-- **Cauchy–Schwarz for the heat-flow score.** For `t > 0`,
`p_t'(y)² / p_t(y) ≤ ∫ ((y - x)/t)² φ_t(y - x) dρ(x)`. -/
theorem sq_heatFlowD1_div_le {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatFlowD1 ρ t y ^ 2 / heatFlowDensity ρ t y
      ≤ ∫ x, ((y - x) / t) ^ 2 * heatDensity t (y - x) ∂ρ := by
  set p := heatFlowDensity ρ t y with hpdef
  set d := heatFlowD1 ρ t y with hddef
  have hp : 0 < p := heatFlowDensity_pos ρ ht y
  set l := d / p with hl
  have i1 := integrable_heatDensity_sub_left ρ ht y
  have i2 : Integrable (fun x => heatDensityD1 t (y - x)) ρ :=
    Integrable.of_bound (((continuous_heatDensityD1 ht).comp (by fun_prop)).aestronglyMeasurable)
      _ (Eventually.of_forall fun x => abs_heatDensityD1_le ht _)
  have i3 : Integrable (fun x => ((y - x) / t) ^ 2 * heatDensity t (y - x)) ρ := by
    refine ((integrable_one_add_sq_mul_heatDensity ρ ht y).const_mul (1 / t ^ 2)).mono'
      ((by fun_prop : Continuous fun x : ℝ => ((y - x) / t) ^ 2).mul
        ((continuous_heatDensity t).comp (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hφ := (heatDensity_pos ht (y - x)).le
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hφ), div_pow]
    have : (y - x) ^ 2 / t ^ 2 = 1 / t ^ 2 * (y - x) ^ 2 := by ring
    rw [this]
    have : 0 ≤ 1 / t ^ 2 := by positivity
    nlinarith
  have h0 : 0 ≤ ∫ x, (l ^ 2 * heatDensity t (y - x) - 2 * l * heatDensityD1 t (y - x)
      + ((y - x) / t) ^ 2 * heatDensity t (y - x)) ∂ρ := by
    refine integral_nonneg fun x => ?_
    have e : l ^ 2 * heatDensity t (y - x) - 2 * l * heatDensityD1 t (y - x)
        + ((y - x) / t) ^ 2 * heatDensity t (y - x)
        = (l + (y - x) / t) ^ 2 * heatDensity t (y - x) := by
      unfold heatDensityD1; ring
    rw [e]
    exact mul_nonneg (sq_nonneg _) (heatDensity_pos ht _).le
  have i12 : Integrable (fun x => l ^ 2 * heatDensity t (y - x)
      - 2 * l * heatDensityD1 t (y - x)) ρ := (i1.const_mul _).sub (i2.const_mul _)
  rw [integral_add i12 i3, integral_sub (i1.const_mul (l ^ 2)) (i2.const_mul (2 * l)),
    integral_const_mul, integral_const_mul] at h0
  change 0 ≤ l ^ 2 * p - 2 * l * d + _ at h0
  have e1 : l ^ 2 * p = d ^ 2 / p := by rw [hl]; field_simp
  have e2 : 2 * l * d = 2 * (d ^ 2 / p) := by rw [hl]; ring
  linarith

/-- For `t > 0` there is `K ≥ 0` with `p_t'(y)² / p_t(y) ≤ K p_{2t}(y)` for all `y`. -/
theorem exists_sq_heatFlowD1_div_le {t : ℝ} (ht : 0 < t) :
    ∃ K, 0 ≤ K ∧ ∀ y, heatFlowD1 ρ t y ^ 2 / heatFlowDensity ρ t y
      ≤ K * heatFlowDensity ρ (2 * t) y := by
  obtain ⟨K, hK0, hK⟩ := exists_heatDensity_le ht le_rfl
  refine ⟨1 / t ^ 2 * K, by positivity, fun y => (sq_heatFlowD1_div_le ρ ht y).trans ?_⟩
  refine (le_abs_self _).trans (abs_integral_le_heatFlowDensity ρ (by linarith)
    (f := fun z => (z / t) ^ 2 * heatDensity t z) (fun z => ?_) y)
  have hφ := (heatDensity_pos ht z).le
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hφ), div_pow, mul_assoc]
  have h1 : z ^ 2 / t ^ 2 * heatDensity t z ≤ 1 / t ^ 2 * ((1 + z ^ 2) * heatDensity t z) := by
    have : z ^ 2 / t ^ 2 = 1 / t ^ 2 * z ^ 2 := by ring
    rw [this]
    have : 0 ≤ 1 / t ^ 2 := by positivity
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left (hK t ⟨le_rfl, le_rfl⟩ z) (by positivity))

end Score

/-! ### The Gaussian second derivative and the KL integrand -/

/-- For `v, t > 0`, `heatFlowD2 (gaussianReal 0 v) t = heatDensityD2 (v + t)`. -/
theorem heatFlowD2_gaussianReal {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    heatFlowD2 (gaussianReal 0 v.toNNReal) t = heatDensityD2 (v + t) := by
  funext y
  have h1 := hasDerivAt_heatFlowD1_x (gaussianReal 0 v.toNNReal) ht y
  rw [heatFlowD1_gaussianReal hv ht] at h1
  exact h1.unique (hasDerivAt_heatDensityD1_x (by linarith) y)

/-- Elementary: from `|log p| ≤ A (1 + y²)` and `|log q| ≤ A' (1 + y²)` (`p, q > 0`),
`|log(p/q) + 1| ≤ (A + A' + 1)(1 + y²)`. -/
theorem abs_log_div_add_one_le {p q A A' y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hA : |Real.log p| ≤ A * (1 + y ^ 2)) (hA' : |Real.log q| ≤ A' * (1 + y ^ 2)) :
    |Real.log (p / q) + 1| ≤ (A + A' + 1) * (1 + y ^ 2) := by
  rw [Real.log_div hp.ne' hq.ne']
  have : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  calc |Real.log p - Real.log q + 1| ≤ |Real.log p| + |Real.log q| + 1 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_one]
        linarith [abs_sub (Real.log p) (Real.log q)]
    _ ≤ _ := by nlinarith

/-- A quadratic bound `|log p| ≤ A (1 + y²)` forces `A ≥ 0`. -/
theorem nonneg_of_abs_log_le {A : ℝ} {f : ℝ → ℝ} (h : |Real.log (f 0)| ≤ A * (1 + 0 ^ 2)) :
    0 ≤ A := by
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one] at h
  exact (abs_nonneg _).trans h

/-- Field `integrable_kl`: for probability measures `ρ, π` with `∫ x² dρ < ∞` and `t > 0`,
`p_t log(p_t/q_t)` is Lebesgue integrable. (No condition on `π` beyond being a probability.) -/
theorem integrable_klIntegrand (ρ π : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    Integrable (klIntegrand (heatFlowDensity ρ) (heatFlowDensity π) t) := by
  obtain ⟨Ap, hAp⟩ := exists_abs_log_heatFlowDensity_le ρ ht le_rfl
  obtain ⟨Aq, hAq⟩ := exists_abs_log_heatFlowDensity_le π ht le_rfl
  refine ((integrable_one_add_sq_mul_heatFlowDensity ρ hmom ht).const_mul (Ap + Aq)).mono'
    (continuous_klIntegrand (fun y => heatFlowDensity_pos ρ ht y)
      (fun y => heatFlowDensity_pos π ht y) (continuous_heatFlowDensity ρ ht)
      (continuous_heatFlowDensity π ht)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hp := heatFlowDensity_pos ρ ht y
  have hq := heatFlowDensity_pos π ht y
  have h1 := hAp t ⟨le_rfl, le_rfl⟩ y
  have h2 := hAq t ⟨le_rfl, le_rfl⟩ y
  rw [Real.norm_eq_abs, klIntegrand, abs_mul, abs_of_pos hp, Real.log_div hp.ne' hq.ne']
  have h3 : |Real.log (heatFlowDensity ρ t y) - Real.log (heatFlowDensity π t y)|
      ≤ (Ap + Aq) * (1 + y ^ 2) := by
    refine (abs_sub _ _).trans ?_
    linarith
  calc heatFlowDensity ρ t y * |Real.log (heatFlowDensity ρ t y)
        - Real.log (heatFlowDensity π t y)|
      ≤ heatFlowDensity ρ t y * ((Ap + Aq) * (1 + y ^ 2)) := by gcongr
    _ = _ := by ring

end FormalizeSampling.HeatFlowRegularity
