module

public import FormalizeSampling.Samplers.ProximalSharpLSI
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Backward heat-flow regularity of the RGO step for warm laws

Status: **Verified** (dimension one; no named hypotheses).

`ProximalSharpLSI` proves the sharp backward step of the proximal sampler under the explicit
regularity hypothesis `BackwardHeatFlowRegular π μ η` (integrability and vanishing boundary flux
of the backward de Bruijn integrands on `(0, η)`). This file derives it
(`backwardHeatFlowRegular_of_warm`) for every probability target `π` with a Gaussian upper
envelope `π ≤ C₂ • N(0, v)` and every input law that is warm with respect to
`π^Y = forwardKernel η ∘ₘ π`, `μ ≤ C • π^Y`. In the sampler `μ = forwardKernel η ∘ₘ ρ`, and
`ρ ≤ C • π` gives `μ ≤ C • π^Y` (`comp_le_smul_comp`). The declarations live in the namespace
`ProximalSharpPerturbed`.

The backward estimates (for `t` in a compact subinterval of `(0, η)`, with
`U = bwdRatio π μ η t`, `w = w_{η-t}`):
* `U ≤ C` and `|U'|, |U''| ≤ M` (warmness: `∫ k(z - y)/w_η(y) dμ ≤ C ∫ k`);
* `(U')² / U ≤ M` (Cauchy–Schwarz against `φ_t(z - y)/w_η(y) dμ(y)`);
* `U(z) ≥ c e^{-(|z| + R)²/(2a)}` (Gaussian lower bound of `μ * N(0, t)`), so
  `|log U| ≤ K (1 + z²)`;
* `w, |w'|, |w''| ≤ N e^{-κ z²}` (envelope `π ≤ C₂ • N(0, v)` and `|φ_s'|, |φ_s''| ≲ φ_{2s}`).
Hence the KL integrand, its time derivative, the Fisher integrand and the boundary flux are all
bounded by `P (1 + z²) e^{-κ z²}` uniformly for times near `t` (`exists_bwd_envelope`).

## Main results

* `backwardHeatFlowRegular_of_warm`: `BackwardHeatFlowRegular π μ η` for warm `μ` and any
  probability target with a Gaussian envelope.
* `comp_le_smul_comp`: kernel composition preserves warmness.

## Not proved here

* Non-warm input laws (e.g. Dirac or heavy-tailed `ρ`): the termwise domination used here
  needs `U = dp_t/dw_{η-t}` bounded; for general `ρ` with only moment bounds the individual terms
  of the time derivative of the backward KL are not integrable and only their sum is (a
  cancellation not exploited here). The rate itself is extended from warm to every finite-KL
  start by `KLWarmApprox` in `ProximalGeneralLSI`.
* Dimension `d`: `BackwardHeatFlowRegularityWarmPi`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.BackwardHeatFlow
open FormalizeSampling.GaussianLSI FormalizeSampling.ProximalSharpLSI
open scoped ENNReal NNReal FormalizeSampling.OU

namespace FormalizeSampling.ProximalSharpPerturbed

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_withDensity_ofReal_iff)

/-! ### Elementary Gaussian bounds -/

/-- `(1 + v²) e^{-c v²} ≤ (1 + 2/c) e^{-c v²/2}` for `c > 0`. -/
theorem one_add_sq_mul_exp_le {c : ℝ} (hc : 0 < c) (v : ℝ) :
    (1 + v ^ 2) * Real.exp (-(c * v ^ 2)) ≤ (1 + 2 / c) * Real.exp (-(c / 2 * v ^ 2)) := by
  have h1 := sq_mul_exp_neg_le (κ := c / 2) (by positivity) v
  have e : Real.exp (-(c * v ^ 2)) = Real.exp (-(c / 2 * v ^ 2)) * Real.exp (-(c / 2 * v ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(c / 2 * v ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ c / 2 * v ^ 2 := by positivity
    linarith)
  have h3 := Real.exp_pos (-(c / 2 * v ^ 2))
  rw [e]
  have e2 : 1 / (c / 2) = 2 / c := by field_simp
  rw [e2] at h1
  nlinarith

/-- `(1 + v²) e^{-c v²}` is integrable for `c > 0`. -/
theorem integrable_one_add_sq_mul_exp {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : ℝ => (1 + v ^ 2) * Real.exp (-(c * v ^ 2))) := by
  refine ((integrable_exp_neg_mul_sq (b := c / 2) (by positivity)).const_mul (1 + 2 / c)).mono'
    (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have := one_add_sq_mul_exp_le hc v
  simpa [neg_mul] using this

/-! ### Lower bound for the heat flow of a probability law -/

/-- **Gaussian lower bound, uniform in time.** For a probability `μ` there are `R ≥ 0`, `m > 0`
with `m (2π r)^{-1/2} e^{-(|z| + R)²/(2r)} ≤ (μ * φ_r)(z)` for all `r > 0` and `z`. -/
theorem exists_lower_heatFlowDensity (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ R m : ℝ, 0 ≤ R ∧ 0 < m ∧ ∀ r, 0 < r → ∀ z,
      m * ((Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-(|z| + R) ^ 2 / (2 * r)))
        ≤ heatFlowDensity μ r z := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, μ (Icc (-(n : ℝ)) n) ≠ 0 := by
    by_contra! h
    have hU : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) n := by
      ext x
      simp only [mem_univ, mem_iUnion, mem_Icc, true_iff]
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have : μ univ = 0 := by rw [hU]; exact measure_iUnion_null h
    simp at this
  set R : ℝ := (n : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg n
  refine ⟨R, (μ (Icc (-R) R)).toReal, hR0, ENNReal.toReal_pos hn (measure_ne_top _ _),
    fun r hr z => ?_⟩
  have hint : Integrable (fun x => heatDensity r (z - x)) μ :=
    Integrable.of_bound ((continuous_heatDensity r).comp (by fun_prop)).aestronglyMeasurable
      (Real.sqrt (2 * Real.pi * r))⁻¹ (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensity_pos hr _).le]; exact heatDensity_le hr _)
  have h1 : ∫ x in Icc (-R) R, heatDensity r (z - x) ∂μ ≤ heatFlowDensity μ r z :=
    setIntegral_le_integral hint (Eventually.of_forall fun x => (heatDensity_pos hr _).le)
  have h2 : ∀ x ∈ Icc (-R) R, (Real.sqrt (2 * Real.pi * r))⁻¹
      * Real.exp (-(|z| + R) ^ 2 / (2 * r)) ≤ heatDensity r (z - x) := by
    intro x hx
    have hx' : |x| ≤ R := abs_le.2 hx
    have hzx : (z - x) ^ 2 ≤ (|z| + R) ^ 2 := by
      rw [← sq_abs (z - x)]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub z x).trans (by linarith)) 2
    unfold heatDensity
    gcongr
  have h3 := setIntegral_mono_on (integrable_const ((Real.sqrt (2 * Real.pi * r))⁻¹
    * Real.exp (-(|z| + R) ^ 2 / (2 * r)))) hint.integrableOn measurableSet_Icc h2
  rw [setIntegral_const, smul_eq_mul] at h3
  exact h3.trans h1

/-! ### Warm laws -/

/-- A two-sided bound `c₀ e^{-(|z|+R)²/(2a)} ≤ u ≤ C` gives a quadratic bound on `|log u|`. -/
theorem abs_log_le_of_two_sided {u C c₀ R a z : ℝ} (hu : 0 < u) (huC : u ≤ C) (hc₀ : 0 < c₀)
    (ha : 0 < a) (hlow : c₀ * Real.exp (-(|z| + R) ^ 2 / (2 * a)) ≤ u) :
    |Real.log u| ≤ (|Real.log C| + |Real.log c₀| + R ^ 2 / a + 1 / a) * (1 + z ^ 2) := by
  have hup : Real.log u ≤ |Real.log C| := (Real.log_le_log hu huC).trans (le_abs_self _)
  have h1 := Real.log_le_log (mul_pos hc₀ (Real.exp_pos _)) hlow
  rw [Real.log_mul hc₀.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
  have h2 : (|z| + R) ^ 2 ≤ 2 * (z ^ 2 + R ^ 2) := by
    have := sq_nonneg (|z| - R)
    have e : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith
  have h3 : (|z| + R) ^ 2 / (2 * a) ≤ z ^ 2 * (1 / a) + R ^ 2 / a := by
    rw [div_le_iff₀ (by positivity)]
    have e : (z ^ 2 * (1 / a) + R ^ 2 / a) * (2 * a) = 2 * (z ^ 2 + R ^ 2) := by
      field_simp
    rw [e]; exact h2
  rw [neg_div] at h1
  set S := |Real.log C| + |Real.log c₀| + R ^ 2 / a + 1 / a
  have hz : 0 ≤ z ^ 2 := sq_nonneg z
  have hR : 0 ≤ R ^ 2 / a := by positivity
  have ha' : 0 ≤ 1 / a := by positivity
  have hS1 : 1 / a ≤ S := by
    have := abs_nonneg (Real.log C); have := abs_nonneg (Real.log c₀); simp only [S]; linarith
  have hSz : z ^ 2 * (1 / a) ≤ S * z ^ 2 := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hS1 hz
  have hS0 : 0 ≤ S * z ^ 2 := le_trans (mul_nonneg hz ha') hSz
  have e : S * (1 + z ^ 2) = S + S * z ^ 2 := by ring
  rw [abs_le, e]
  have := neg_abs_le (Real.log c₀)
  have := abs_nonneg (Real.log c₀)
  have := abs_nonneg (Real.log C)
  constructor
  · simp only [S]; linarith
  · simp only [S] at hS0 ⊢; linarith

section Warm

variable (π μ : Measure ℝ) [IsProbabilityMeasure π] [IsProbabilityMeasure μ] {η C : ℝ}

open FormalizeSampling.Proximal

omit [IsProbabilityMeasure μ] in
/-- **Warm integral bound.** If `μ ≤ C • π^Y` (`C ≥ 0`, `π^Y = forwardKernel η ∘ₘ π`, `η > 0`)
and `k ≥ 0` is integrable, then `∫ k(z - y) / w_η(y) dμ(y) ≤ C ∫ k`. -/
theorem integral_div_le_of_warm (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernel η ∘ₘ π)) {k : ℝ → ℝ} (hk0 : ∀ v, 0 ≤ k v)
    (hki : Integrable k) (z : ℝ) :
    ∫ y, k (z - y) / heatFlowDensity π η y ∂μ ≤ C * ∫ v, k v := by
  have hw := heatFlowDensity_pos π hη
  have hwc := continuous_heatFlowDensity π hη
  have hpY := forwardKernel_comp_eq_withDensity π hη
  set g : ℝ → ℝ := fun y => k (z - y) / heatFlowDensity π η y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => div_nonneg (hk0 _) (hw y).le
  have hwg : (fun y => heatFlowDensity π η y * g y) = fun y => k (z - y) := by
    funext y; simp only [hg]; field_simp [(hw y).ne']
  have hgi : Integrable g (forwardKernel η ∘ₘ π) := by
    rw [hpY, integrable_withDensity_ofReal_iff hwc.measurable fun y => (hw y).le, hwg]
    exact hki.comp_sub_left z
  calc ∫ y, g y ∂μ ≤ ∫ y, g y ∂(ENNReal.ofReal C • (forwardKernel η ∘ₘ π)) :=
        integral_mono_measure hwarm (Eventually.of_forall hg0)
          (hgi.smul_measure ENNReal.ofReal_ne_top)
    _ = C * ∫ y, g y ∂(forwardKernel η ∘ₘ π) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]
    _ = C * ∫ v, k v := by
        rw [hpY, integral_withDensity_ofReal hwc.measurable fun y => (hw y).le, hwg,
          integral_sub_left_eq_self]

/-- `(1 + v²) φ_b(v)` is integrable (`b > 0`). -/
theorem integrable_one_add_sq_mul_heatDensity' {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℝ => (1 + v ^ 2) * heatDensity b v) := by
  refine ((integrable_one_add_sq_mul_exp (c := 1 / (2 * b)) (by positivity)).const_mul
    (Real.sqrt (2 * Real.pi * b))⁻¹).congr (Eventually.of_forall fun v => ?_)
  simp only [heatDensity]
  have : -(1 / (2 * b) * v ^ 2) = -v ^ 2 / (2 * b) := by ring
  rw [this]; ring

/-- **Bounds on the backward ratio for warm laws.** Let `π, μ` be probability laws with
`μ ≤ C • π^Y` (`C ≥ 0`, `η > 0`) and `0 < a ≤ b < η`. There are `M, K ≥ 0` such that for all
`r ∈ [a, b]` and `z`: `U_r(z) ≤ C`, `|U_r'(z)| ≤ M`, `|U_r''(z)| ≤ M`, `U_r'(z)² / U_r(z) ≤ M`
and `|log U_r(z)| ≤ K (1 + z²)`, with `U_r = bwdRatio π μ η r`. -/
theorem exists_bwdRatio_bounds (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernel η ∘ₘ π)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbη : b < η) :
    ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ ∀ r ∈ Icc a b, ∀ z,
      bwdRatio π μ η r z ≤ C ∧ |bwdRatioD1 π μ η r z| ≤ M ∧ |bwdRatioD2 π μ η r z| ≤ M ∧
      bwdRatioD1 π μ η r z ^ 2 / bwdRatio π μ η r z ≤ M ∧
      |Real.log (bwdRatio π μ η r z)| ≤ K * (1 + z ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  have hw := heatFlowDensity_pos π hη
  set A₀ : ℝ := Real.sqrt (2 * Real.pi * b) / Real.sqrt (2 * Real.pi * a) with hA₀
  have hA₀0 : 0 < A₀ := by positivity
  set kb : ℝ → ℝ := fun v => A₀ * ((1 + v ^ 2) * heatDensity b v) with hkb
  have hkb0 : ∀ v, 0 ≤ kb v := fun v => by have := heatDensity_pos hb v; positivity
  have hkbc : Continuous kb := by
    simp only [hkb]; exact continuous_const.mul ((by fun_prop : Continuous fun v : ℝ =>
      1 + v ^ 2).mul (continuous_heatDensity b))
  have hkbi : Integrable kb := (integrable_one_add_sq_mul_heatDensity' hb).const_mul A₀
  have hkb_ge : ∀ r ∈ Icc a b, ∀ v, (1 + v ^ 2) * heatDensity r v ≤ kb v := by
    intro r hr v
    have h1 := heatDensity_le_exp ha hr.1 hr.2 v
    have e : (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (-v ^ 2 / (2 * b))
        = A₀ * heatDensity b v := by
      simp only [hA₀, heatDensity]
      have : 0 < Real.sqrt (2 * Real.pi * b) := Real.sqrt_pos.2 (by positivity)
      field_simp
    rw [e] at h1
    simp only [hkb]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + v ^ 2)
    linarith
  -- boundedness in `y` of the integrands, for a fixed `z`
  obtain ⟨Kb, Lb, hKb, hLb, hbb⟩ := exists_bwd_bound π hb le_rfl hbη
  have hkb_div : ∀ z y, kb (z - y) / heatFlowDensity π η y ≤ A₀ * (Kb * Real.exp (Lb * z ^ 2)) :=
    fun z y => by
      have := hbb b ⟨le_rfl, le_rfl⟩ z y
      simp only [hkb]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this hA₀0.le
  have hkb_int : ∀ z, Integrable (fun y => kb (z - y) / heatFlowDensity π η y) μ := fun z =>
    Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη hkbc z) _
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (div_nonneg (hkb0 _) (hw y).le)]; exact hkb_div z y)
  have hwarmk : ∀ z, ∫ y, kb (z - y) / heatFlowDensity π η y ∂μ ≤ C * ∫ v, kb v := fun z =>
    integral_div_le_of_warm π μ hη hC hwarm hkb0 hkbi z
  set D : ℝ := (1 + 1 / a) ^ 2 with hD
  have hD1 : 1 ≤ D := by have : 0 < 1 / a := by positivity
                         exact one_le_pow₀ (by linarith)
  have hDa : 1 / a ^ 2 ≤ D := by
    have : 0 < 1 / a := by positivity
    rw [hD, show 1 / a ^ 2 = (1 / a) ^ 2 by ring]
    exact pow_le_pow_left₀ this.le (by linarith) 2
  set M : ℝ := D * (C * ∫ v, kb v) with hM
  have hIk : 0 ≤ ∫ v, kb v := integral_nonneg hkb0
  -- lower bound
  obtain ⟨R, m, hR, hm, hlow⟩ := exists_lower_heatFlowDensity μ
  set c₀ : ℝ := Real.sqrt (2 * Real.pi * η) * (m * (Real.sqrt (2 * Real.pi * b))⁻¹) with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set K : ℝ := |Real.log C| + |Real.log c₀| + R ^ 2 / a + 1 / a with hK
  refine ⟨M, K, by positivity, by positivity, fun r hr z => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrη : r < η := hr.2.trans_lt hbη
  obtain ⟨K₁, L₁, hK₁, hL₁, hb₁⟩ := bwd_integrand_bound π hr0 le_rfl hrη
  have hr' : r ∈ Icc r r := ⟨le_rfl, le_rfl⟩
  have hφint : Integrable (fun y => heatDensity r (z - y) / heatFlowDensity π η y) μ :=
    Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
      (continuous_heatDensity r) z) _ (Eventually.of_forall fun y => (hb₁ r hr' z y).1)
  have hU0 := bwdRatio_pos π μ hr0 hrη z
  -- (1) `U ≤ C`
  have hU : bwdRatio π μ η r z ≤ C := by
    have := integral_div_le_of_warm π μ hη hC hwarm (fun v => (heatDensity_pos hr0 v).le)
      (GaussianFunctionalLSI.integrable_heatDensity hr0) z
    rwa [GaussianFunctionalLSI.integral_heatDensity hr0, mul_one] at this
  -- domination of `|φ'|, |φ''|` by `D kb`
  have hdom : ∀ {g : ℝ → ℝ}, Continuous g → (∀ v, |g v| ≤ D * ((1 + v ^ 2) * heatDensity r v)) →
      |∫ y, g (z - y) / heatFlowDensity π η y ∂μ| ≤ M := by
    intro g hg hgle
    have hgi : Integrable (fun y => g (z - y) / heatFlowDensity π η y) μ := by
      refine (hkb_int z).const_mul D |>.mono' (aestronglyMeasurable_div_heatFlowDensity π μ hη
        hg z) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hw y), mul_div_assoc']
      exact div_le_div_of_nonneg_right ((hgle _).trans
        (mul_le_mul_of_nonneg_left (hkb_ge r hr _) (by positivity))) (hw y).le
    calc |∫ y, g (z - y) / heatFlowDensity π η y ∂μ|
        ≤ ∫ y, |g (z - y) / heatFlowDensity π η y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ y, D * (kb (z - y) / heatFlowDensity π η y) ∂μ := by
          refine integral_mono hgi.abs ((hkb_int z).const_mul D) fun y => ?_
          rw [abs_div, abs_of_pos (hw y), mul_div_assoc']
          exact div_le_div_of_nonneg_right ((hgle _).trans
            (mul_le_mul_of_nonneg_left (hkb_ge r hr _) (by positivity))) (hw y).le
      _ ≤ M := by
          rw [integral_const_mul, hM]
          exact mul_le_mul_of_nonneg_left (hwarmk z) (by positivity)
  have hU1 : |bwdRatioD1 π μ η r z| ≤ M := hdom (continuous_heatDensityD1 hr0)
    (abs_heatDensityD1_le_mul ha hr.1)
  have hU2 : |bwdRatioD2 π μ η r z| ≤ M := hdom (continuous_heatDensityD2 r)
    (abs_heatDensityD2_le_mul ha hr.1)
  -- Cauchy–Schwarz for the Fisher ratio
  have hU3 : bwdRatioD1 π μ η r z ^ 2 / bwdRatio π μ η r z ≤ M := by
    set A : ℝ → ℝ := fun y => Real.sqrt (heatDensity r (z - y) / heatFlowDensity π η y)
    set B : ℝ → ℝ := fun y => -((z - y) / r) * A y
    have hA2 : ∀ y, A y ^ 2 = heatDensity r (z - y) / heatFlowDensity π η y := fun y =>
      Real.sq_sqrt (div_nonneg (heatDensity_pos hr0 _).le (hw y).le)
    have hAB : (fun y => A y * B y) = fun y => heatDensityD1 r (z - y) / heatFlowDensity π η y := by
      funext y
      simp only [B, heatDensityD1]
      have := hA2 y
      rw [show A y * (-((z - y) / r) * A y) = -((z - y) / r) * A y ^ 2 by ring, this]
      ring
    have hB2 : ∀ y, B y ^ 2 = ((z - y) / r) ^ 2 * (heatDensity r (z - y) / heatFlowDensity π η y) :=
      fun y => by simp only [B]; rw [mul_pow, neg_sq, hA2]
    have hB2le : ∀ y, B y ^ 2 ≤ D * (kb (z - y) / heatFlowDensity π η y) := by
      intro y
      rw [hB2, mul_div_assoc', mul_div_assoc']
      have h1 : ((z - y) / r) ^ 2 ≤ 1 / a ^ 2 * (1 + (z - y) ^ 2) := by
        rw [div_pow]
        have : 1 / r ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ ha.le hr.1 2)
        calc (z - y) ^ 2 / r ^ 2 = (z - y) ^ 2 * (1 / r ^ 2) := by ring
          _ ≤ (1 + (z - y) ^ 2) * (1 / a ^ 2) := by
              gcongr; linarith
          _ = _ := by ring
      have h2 : ((z - y) / r) ^ 2 * heatDensity r (z - y) ≤ D * kb (z - y) := by
        calc ((z - y) / r) ^ 2 * heatDensity r (z - y)
            ≤ 1 / a ^ 2 * (1 + (z - y) ^ 2) * heatDensity r (z - y) := by
              gcongr; exact (heatDensity_pos hr0 _).le
          _ = 1 / a ^ 2 * ((1 + (z - y) ^ 2) * heatDensity r (z - y)) := by ring
          _ ≤ D * kb (z - y) := mul_le_mul hDa (hkb_ge r hr _)
              (mul_nonneg (by positivity) (heatDensity_pos hr0 _).le) (by linarith)
      exact div_le_div_of_nonneg_right h2 (hw y).le
    have hAi : Integrable (fun y => A y ^ 2) μ := by simp_rw [hA2]; exact hφint
    have hBm : AEStronglyMeasurable (fun y => B y ^ 2) μ := by
      simp_rw [hB2]
      exact ((by fun_prop : Continuous fun y : ℝ => ((z - y) / r) ^ 2).mul
        (continuous_div_heatFlowDensity π hη (continuous_heatDensity r) z)).aestronglyMeasurable
    have hBi : Integrable (fun y => B y ^ 2) μ :=
      ((hkb_int z).const_mul D).mono' hBm (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hB2le y)
    have hABi : Integrable (fun y => A y * B y) μ := by
      rw [hAB]
      exact Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
        (continuous_heatDensityD1 hr0) z) _ (Eventually.of_forall fun y => (hb₁ r hr' z y).2.1)
    have hUA : bwdRatio π μ η r z = ∫ y, A y ^ 2 ∂μ := by
      simp_rw [hA2]; rfl
    have hU1A : bwdRatioD1 π μ η r z = ∫ y, A y * B y ∂μ := by rw [hAB]; rfl
    have hcs := LogSobolev.sq_integral_mul_le_of_pos hAi hBi hABi (by rw [← hUA]; exact hU0)
    rw [← hUA, ← hU1A] at hcs
    have hBint : ∫ y, B y ^ 2 ∂μ ≤ M := by
      calc ∫ y, B y ^ 2 ∂μ ≤ ∫ y, D * (kb (z - y) / heatFlowDensity π η y) ∂μ :=
            integral_mono hBi ((hkb_int z).const_mul D) hB2le
        _ ≤ M := by
            rw [integral_const_mul, hM]
            exact mul_le_mul_of_nonneg_left (hwarmk z) (by positivity)
    rw [div_le_iff₀ hU0]
    linarith [mul_le_mul_of_nonneg_left hBint hU0.le]
  -- the logarithm
  have hUlow : c₀ * Real.exp (-(|z| + R) ^ 2 / (2 * a)) ≤ bwdRatio π μ η r z := by
    have hwle : ∀ y, Real.sqrt (2 * Real.pi * η) * heatDensity r (z - y)
        ≤ heatDensity r (z - y) / heatFlowDensity π η y := by
      intro y
      rw [le_div_iff₀ (hw y)]
      have h1 := heatFlowDensity_le π hη y
      have h2 : Real.sqrt (2 * Real.pi * η) * heatFlowDensity π η y ≤ 1 := by
        have hs : 0 < Real.sqrt (2 * Real.pi * η) := Real.sqrt_pos.2 (by positivity)
        calc Real.sqrt (2 * Real.pi * η) * heatFlowDensity π η y
            ≤ Real.sqrt (2 * Real.pi * η) * (Real.sqrt (2 * Real.pi * η))⁻¹ := by gcongr
          _ = 1 := mul_inv_cancel₀ hs.ne'
      have := (heatDensity_pos hr0 (z - y)).le
      linarith [mul_le_mul_of_nonneg_left h2 this]
    have hφμ : Integrable (fun y => heatDensity r (z - y)) μ :=
      Integrable.of_bound ((continuous_heatDensity r).comp (by fun_prop)).aestronglyMeasurable
        (Real.sqrt (2 * Real.pi * r))⁻¹ (Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (heatDensity_pos hr0 _).le]; exact heatDensity_le hr0 _)
    have h1 : Real.sqrt (2 * Real.pi * η) * heatFlowDensity μ r z ≤ bwdRatio π μ η r z := by
      unfold heatFlowDensity bwdRatio
      rw [← integral_const_mul]
      exact integral_mono (hφμ.const_mul _) hφint hwle
    have h2 := hlow r hr0 z
    have h3 : m * ((Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(|z| + R) ^ 2 / (2 * a)))
        ≤ m * ((Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-(|z| + R) ^ 2 / (2 * r))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (Real.exp_pos _).le
        (inv_nonneg.2 (Real.sqrt_nonneg _))) hm.le
      · exact inv_anti₀ (Real.sqrt_pos.2 (by positivity))
          (Real.sqrt_le_sqrt (by gcongr; exact hr.2))
      · refine Real.exp_le_exp.2 ?_
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hr.1])
    calc c₀ * Real.exp (-(|z| + R) ^ 2 / (2 * a))
        = Real.sqrt (2 * Real.pi * η) * (m * ((Real.sqrt (2 * Real.pi * b))⁻¹
            * Real.exp (-(|z| + R) ^ 2 / (2 * a)))) := by rw [hc₀]; ring
      _ ≤ Real.sqrt (2 * Real.pi * η) * heatFlowDensity μ r z := by gcongr; exact h3.trans h2
      _ ≤ _ := h1
  have hlog : |Real.log (bwdRatio π μ η r z)| ≤ K * (1 + z ^ 2) :=
    abs_log_le_of_two_sided hU0 hU hc₀0 ha hUlow
  exact ⟨hU, hU1, hU2, hU3, hlog⟩

end Warm

/-! ### Gaussian envelope of the reference family -/

/-- `(1 + v²) φ_t(v) ≤ 2 (1 + 4t) φ_{2t}(v)` for `t > 0`. -/
theorem one_add_sq_mul_heatDensity_le {t : ℝ} (ht : 0 < t) (v : ℝ) :
    (1 + v ^ 2) * heatDensity t v ≤ 2 * (1 + 4 * t) * heatDensity (2 * t) v := by
  have h1 := one_add_sq_mul_exp_le (c := 1 / (2 * t)) (by positivity) v
  have e1 : -(1 / (2 * t) * v ^ 2) = -v ^ 2 / (2 * t) := by ring
  have e2 : -(1 / (2 * t) / 2 * v ^ 2) = -v ^ 2 / (2 * (2 * t)) := by ring
  have e3 : 2 / (1 / (2 * t)) = 4 * t := by field_simp; ring
  rw [e1, e2, e3] at h1
  have hs : Real.sqrt (2 * Real.pi * (2 * t)) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * t) := by
    rw [← Real.sqrt_mul (by norm_num)]; ring_nf
  have hq : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt 2 := by positivity
  have h22 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  simp only [heatDensity]
  rw [hs]
  set E1 := Real.exp (-v ^ 2 / (2 * t))
  set E2 := Real.exp (-v ^ 2 / (2 * (2 * t)))
  have hE2 : 0 < E2 := Real.exp_pos _
  have key : (Real.sqrt (2 * Real.pi * t))⁻¹
      ≤ 2 * (Real.sqrt 2 * Real.sqrt (2 * Real.pi * t))⁻¹ := by
    rw [mul_inv, ← mul_assoc]
    refine le_mul_of_one_le_left (inv_nonneg.2 hq.le) ?_
    rw [le_mul_inv_iff₀ h2]; linarith
  calc (1 + v ^ 2) * ((Real.sqrt (2 * Real.pi * t))⁻¹ * E1)
      = (Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + v ^ 2) * E1) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + 4 * t) * E2) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hq.le)
    _ ≤ 2 * (Real.sqrt 2 * Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + 4 * t) * E2) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = _ := by ring

/-- `φ_t(z - ·)` is integrable for a finite measure (`t > 0`). -/
theorem integrable_heatDensity_sub_of_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ] {t : ℝ}
    (ht : 0 < t) (z : ℝ) : Integrable (fun x => heatDensity t (z - x)) ρ :=
  Integrable.of_bound ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
    (Real.sqrt (2 * Real.pi * t))⁻¹ (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _)

section Envelope

variable (π : Measure ℝ) [IsProbabilityMeasure π] {C₂ v : ℝ}

omit [IsProbabilityMeasure π] in
/-- **Gaussian envelope.** If `π ≤ C₂ • N(0, v)` (`v > 0`), then
`w_s(z) ≤ C₂ φ_{v + s}(z)` for `s > 0`. -/
theorem heatFlowDensity_le_of_envelope (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) {s : ℝ} (hs : 0 < s) (z : ℝ) :
    heatFlowDensity π s z ≤ C₂ * heatDensity (v + s) z := by
  have hi := integrable_heatDensity_sub_of_finite (gaussianReal 0 v.toNNReal) hs z
  have h1 : heatFlowDensity π s z ≤ ∫ x, heatDensity s (z - x)
      ∂(ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) :=
    integral_mono_measure henv (Eventually.of_forall fun x => (heatDensity_pos hs _).le)
      (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hC₂, smul_eq_mul] at h1
  have h2 : ∫ x, heatDensity s (z - x) ∂(gaussianReal 0 v.toNNReal) = heatDensity (v + s) z := by
    rw [← heatFlowDensity_gaussianReal hv hs]; rfl
  rwa [h2] at h1

/-- **Uniform Gaussian bounds on `w_s, w_s', w_s''`.** If `π ≤ C₂ • N(0, v)` and
`0 < s₀ ≤ s₁`, there is `N ≥ 0` with `w_s(z), |w_s'(z)|, |w_s''(z)| ≤ N e^{-κ z²}` for all
`s ∈ [s₀, s₁]` and `z`, where `κ = 1 / (2 (v + 2 s₁))`. -/
theorem exists_heatFlow_envelope (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) {s₀ s₁ : ℝ} (hs₀ : 0 < s₀)
    (hs : s₀ ≤ s₁) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ s ∈ Icc s₀ s₁, ∀ z,
      heatFlowDensity π s z ≤ N * Real.exp (-(1 / (2 * (v + 2 * s₁)) * z ^ 2)) ∧
      |heatFlowD1 π s z| ≤ N * Real.exp (-(1 / (2 * (v + 2 * s₁)) * z ^ 2)) ∧
      |heatFlowD2 π s z| ≤ N * Real.exp (-(1 / (2 * (v + 2 * s₁)) * z ^ 2)) := by
  set D : ℝ := (1 + 1 / s₀) ^ 2 * (2 * (1 + 4 * s₁)) with hD
  have hD1 : 1 ≤ D := by
    have : 1 ≤ (1 + 1 / s₀) ^ 2 := by
      have : 0 < 1 / s₀ := by positivity
      nlinarith
    have : 1 ≤ 2 * (1 + 4 * s₁) := by linarith
    nlinarith
  set G : ℝ := C₂ * (Real.sqrt (2 * Real.pi * v))⁻¹ with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨D * G, by positivity, fun s hsI z => ?_⟩
  have hs0 : 0 < s := hs₀.trans_le hsI.1
  -- envelope at any time `σ ∈ (0, 2 s₁]`
  have henvσ : ∀ σ, 0 < σ → σ ≤ 2 * s₁ →
      heatFlowDensity π σ z ≤ G * Real.exp (-(1 / (2 * (v + 2 * s₁)) * z ^ 2)) := by
    intro σ hσ hσ1
    have h1 := heatFlowDensity_le_of_envelope π hv hC₂ henv hσ z
    have h2 := heatDensity_le_exp (a := v) (b := v + 2 * s₁) (t := v + σ) hv (by linarith)
      (by linarith) z
    have e : -z ^ 2 / (2 * (v + 2 * s₁)) = -(1 / (2 * (v + 2 * s₁)) * z ^ 2) := by ring
    rw [e] at h2
    calc heatFlowDensity π σ z ≤ C₂ * heatDensity (v + σ) z := h1
      _ ≤ C₂ * ((Real.sqrt (2 * Real.pi * v))⁻¹
            * Real.exp (-(1 / (2 * (v + 2 * s₁)) * z ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 hC₂
      _ = _ := by rw [hG]; ring
  set E := Real.exp (-(1 / (2 * (v + 2 * s₁)) * z ^ 2))
  have hE : 0 < E := Real.exp_pos _
  -- derivatives: `|g(z - x)| ≤ D φ_{2s}(z - x)`
  have hder : ∀ {g : ℝ → ℝ}, Continuous g →
      (∀ u, |g u| ≤ (1 + 1 / s₀) ^ 2 * ((1 + u ^ 2) * heatDensity s u)) →
      |∫ x, g (z - x) ∂π| ≤ D * G * E := by
    intro g hg hgle
    have hb : ∀ u, |g u| ≤ D * heatDensity (2 * s) u := by
      intro u
      refine (hgle u).trans ?_
      have h1 := one_add_sq_mul_heatDensity_le hs0 u
      have h2 : 2 * (1 + 4 * s) * heatDensity (2 * s) u
          ≤ 2 * (1 + 4 * s₁) * heatDensity (2 * s) u := by
        have := (heatDensity_pos (by positivity : (0 : ℝ) < 2 * s) u).le
        have := hsI.2
        nlinarith
      calc (1 + 1 / s₀) ^ 2 * ((1 + u ^ 2) * heatDensity s u)
          ≤ (1 + 1 / s₀) ^ 2 * (2 * (1 + 4 * s₁) * heatDensity (2 * s) u) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = _ := by rw [hD]; ring
    have hi2 := integrable_heatDensity_sub_of_finite π (by positivity : (0 : ℝ) < 2 * s) z
    calc |∫ x, g (z - x) ∂π| ≤ ∫ x, |g (z - x)| ∂π := abs_integral_le_integral_abs
      _ ≤ ∫ x, D * heatDensity (2 * s) (z - x) ∂π :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (hi2.const_mul D) (Eventually.of_forall fun x => hb _)
      _ = D * heatFlowDensity π (2 * s) z := by rw [integral_const_mul]; rfl
      _ ≤ D * (G * E) := mul_le_mul_of_nonneg_left (henvσ _ (by positivity)
          (by linarith [hsI.2])) (by positivity)
      _ = D * G * E := by ring
  refine ⟨?_, hder (continuous_heatDensityD1 hs0) (abs_heatDensityD1_le_mul hs₀ hsI.1),
    hder (continuous_heatDensityD2 s) (abs_heatDensityD2_le_mul hs₀ hsI.1)⟩
  calc heatFlowDensity π s z ≤ G * E := henvσ s hs0 (by linarith [hsI.2])
    _ ≤ D * G * E := by
        have := mul_le_mul_of_nonneg_right hD1 (mul_nonneg hG0 hE.le)
        nlinarith

end Envelope

/-! ### Backward regularity for warm laws -/

/-- Pointwise bounds for the integrands of the backward flow from bounds on
`W, W', W''` (by `Ne`) and on `U, U', U''`, `(U')²/U`, `log U`. -/
theorem bwd_pointwise {w w1 w2 u u1 u2 Ne M C K Q : ℝ} (hw0 : 0 < w) (hw : w ≤ Ne)
    (hw1 : |w1| ≤ Ne) (hw2 : |w2| ≤ Ne) (hu0 : 0 < u) (hu : u ≤ C) (hu1 : |u1| ≤ M)
    (hu2 : |u2| ≤ M) (hf : u1 ^ 2 / u ≤ M) (hl : |Real.log u| ≤ K * Q) (hQ : 1 ≤ Q)
    (hK : 0 ≤ K) :
    |w * (u * Real.log u)| ≤ (M * (K + 1) + C * K + M) * (Ne * Q) ∧
    |(w * u2 * (Real.log u + 1) - w2 * (u * Real.log u)) / 2|
      ≤ (M * (K + 1) + C * K + M) * (Ne * Q) ∧
    |w * u1 ^ 2 / u| ≤ (M * (K + 1) + C * K + M) * (Ne * Q) ∧
    |w * u1 * (Real.log u + 1) - w1 * (u * Real.log u)|
      ≤ (M * (K + 1) + C * K + M) * (Ne * Q) := by
  have hNe : 0 ≤ Ne := hw0.le.trans hw
  have hM : 0 ≤ M := (abs_nonneg _).trans hu1
  have hC : 0 ≤ C := hu0.le.trans hu
  have hQ0 : 0 ≤ Q := by linarith
  have hl1 : |Real.log u + 1| ≤ (K + 1) * Q := by
    calc |Real.log u + 1| ≤ |Real.log u| + 1 := by
          simpa using abs_add_le (Real.log u) 1
      _ ≤ K * Q + Q := by linarith
      _ = (K + 1) * Q := by ring
  have hul : |u * Real.log u| ≤ C * (K * Q) := by
    rw [abs_mul, abs_of_pos hu0]
    exact mul_le_mul hu hl (abs_nonneg _) hC
  have hKQ : 0 ≤ K * Q := mul_nonneg hK hQ0
  have hK1Q : 0 ≤ (K + 1) * Q := by positivity
  -- the three basic products
  have A1 : |w * u2 * (Real.log u + 1)| ≤ Ne * M * ((K + 1) * Q) := by
    rw [abs_mul, abs_mul, abs_of_pos hw0]
    exact mul_le_mul (mul_le_mul hw hu2 (abs_nonneg _) hNe) hl1 (abs_nonneg _)
      (mul_nonneg hNe hM)
  have A1' : |w * u1 * (Real.log u + 1)| ≤ Ne * M * ((K + 1) * Q) := by
    rw [abs_mul, abs_mul, abs_of_pos hw0]
    exact mul_le_mul (mul_le_mul hw hu1 (abs_nonneg _) hNe) hl1 (abs_nonneg _)
      (mul_nonneg hNe hM)
  have A2 : ∀ {w' : ℝ}, |w'| ≤ Ne → |w' * (u * Real.log u)| ≤ Ne * (C * (K * Q)) := by
    intro w' hw'
    rw [abs_mul]; exact mul_le_mul hw' hul (abs_nonneg _) hNe
  have A3 : |w * u1 ^ 2 / u| ≤ Ne * M := by
    rw [mul_div_assoc, abs_mul, abs_of_pos hw0,
      abs_of_nonneg (div_nonneg (sq_nonneg _) hu0.le)]
    exact mul_le_mul hw hf (div_nonneg (sq_nonneg _) hu0.le) hNe
  have e : (M * (K + 1) + C * K + M) * (Ne * Q)
      = Ne * M * ((K + 1) * Q) + Ne * (C * (K * Q)) + Ne * M * Q := by ring
  have hNMQ : Ne * M ≤ Ne * M * Q := le_mul_of_one_le_right (mul_nonneg hNe hM) hQ
  have h1 : 0 ≤ Ne * M * ((K + 1) * Q) := by positivity
  have h2 : 0 ≤ Ne * (C * (K * Q)) := by positivity
  have h3 : 0 ≤ Ne * M * Q := by positivity
  rw [e]
  refine ⟨by linarith [A2 (w' := w) (by rw [abs_of_pos hw0]; exact hw)], ?_, by linarith, ?_⟩
  · rw [abs_div, abs_two]
    have := (abs_sub _ _).trans (add_le_add A1 (A2 hw2))
    linarith
  · have := (abs_sub _ _).trans (add_le_add A1' (A2 hw1))
    linarith

/-- `(1 + z²) e^{-κ z²} → 0` as `z → ±∞` (`κ > 0`). -/
theorem tendsto_one_add_sq_mul_exp {κ : ℝ} (hκ : 0 < κ) (l : Filter ℝ)
    (hl : Tendsto (fun z : ℝ => z ^ 2) l atTop) :
    Tendsto (fun z : ℝ => (1 + z ^ 2) * Real.exp (-(κ * z ^ 2))) l (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => Real.exp (-(κ / 2 * z ^ 2))) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (by positivity) hl))
  have h2 := h1.const_mul (1 + 2 / κ)
  rw [mul_zero] at h2
  refine squeeze_zero (fun z => by positivity) (fun z => one_add_sq_mul_exp_le hκ z) h2

/-- `z² → ∞` as `z → +∞`. -/
theorem tendsto_sq_atTop : Tendsto (fun z : ℝ => z ^ 2) atTop atTop :=
  tendsto_pow_atTop two_ne_zero

/-- `z² → ∞` as `z → -∞`. -/
theorem tendsto_sq_atBot : Tendsto (fun z : ℝ => z ^ 2) atBot atTop := by
  have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_neg_atBot_atTop
  refine this.congr fun z => ?_
  simp

section Regular

open FormalizeSampling.Proximal

variable (π μ : Measure ℝ) [IsProbabilityMeasure π] [IsProbabilityMeasure μ] {η C C₂ v : ℝ}

/-- **Uniform Gaussian envelope of the backward integrands.** For a warm law
`μ ≤ C • π^Y` and a target with `π ≤ C₂ • N(0, v)`, every `t ∈ (0, η)` has a neighbourhood
on which the KL integrand, its time derivative, the Fisher integrand and the boundary flux are
bounded by `P (1 + z²) e^{-κ z²}` (`κ > 0`). -/
theorem exists_bwd_envelope (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernel η ∘ₘ π)) (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) {t : ℝ} (ht : t ∈ Ioo 0 η) :
    ∃ P κ : ℝ, 0 ≤ P ∧ 0 < κ ∧ ∀ᶠ r in 𝓝 t, ∀ z,
      |bklIntegrand (bwdRef π η) (bwdRatio π μ η) r z|
        ≤ P * ((1 + z ^ 2) * Real.exp (-(κ * z ^ 2))) ∧
      |bklRate (bwdRef π η) (bwdRatio π μ η) (bwdRefD2 π η) (bwdRatioD2 π μ η) r z|
        ≤ P * ((1 + z ^ 2) * Real.exp (-(κ * z ^ 2))) ∧
      |bFisherIntegrand (bwdRef π η) (bwdRatio π μ η) (bwdRatioD1 π μ η) r z|
        ≤ P * ((1 + z ^ 2) * Real.exp (-(κ * z ^ 2))) ∧
      |bklFlux (bwdRef π η) (bwdRatio π μ η) (bwdRefD1 π η) (bwdRatioD1 π μ η) r z|
        ≤ P * ((1 + z ^ 2) * Real.exp (-(κ * z ^ 2))) := by
  obtain ⟨ht0, htη⟩ := ht
  set a := t / 2
  set b := (t + η) / 2
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hbη : b < η := by simp only [b]; linarith
  obtain ⟨M, K, hM, hK, hU⟩ := exists_bwdRatio_bounds π μ hη hC hwarm ha hab hbη
  obtain ⟨N, hN, hW⟩ := exists_heatFlow_envelope π hv hC₂ henv (s₀ := η - b) (s₁ := η - a)
    (by linarith) (by linarith)
  refine ⟨(M * (K + 1) + C * K + M) * N, 1 / (2 * (v + 2 * (η - a))), by positivity,
    by have : 0 < η - a := by simp only [a]; linarith
       positivity, ?_⟩
  have hI : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds (by simp only [a]; linarith)
    (by simp only [b]; linarith)
  filter_upwards [hI] with r hr z
  have hrI : r ∈ Icc a b := Ioo_subset_Icc_self hr
  have hsI : η - r ∈ Icc (η - b) (η - a) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨hu, hu1, hu2, hf, hl⟩ := hU r hrI z
  obtain ⟨hw, hw1, hw2⟩ := hW (η - r) hsI z
  have hu0 := bwdRatio_pos π μ (ha.trans hr.1) (hr.2.trans hbη) z
  have hw0 := heatFlowDensity_pos π (by linarith [hr.2] : (0 : ℝ) < η - r) z
  have key := bwd_pointwise hw0 hw hw1 hw2 hu0 hu hu1 hu2 hf hl
    (le_add_of_nonneg_right (sq_nonneg z)) hK
  have e : ∀ X : ℝ, X * (N * Real.exp (-(1 / (2 * (v + 2 * (η - a))) * z ^ 2)) * (1 + z ^ 2))
      = X * N * ((1 + z ^ 2) * Real.exp (-(1 / (2 * (v + 2 * (η - a))) * z ^ 2))) :=
    fun X => by ring
  rw [e] at key
  exact key

/-- **Backward regularity for warm laws (Verified).** If `π ≤ C₂ • N(0, v)` (`v > 0`) and
`μ ≤ C • π^Y` with `π^Y = forwardKernel η ∘ₘ π`, `η > 0`, then
`BackwardHeatFlowRegular π μ η`. -/
theorem backwardHeatFlowRegular_of_warm (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernel η ∘ₘ π)) (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • gaussianReal 0 v.toNNReal) :
    BackwardHeatFlowRegular π μ η := by
  have env := fun {t : ℝ} (ht : t ∈ Ioo 0 η) =>
    exists_bwd_envelope π μ hη hC hwarm hv hC₂ henv ht
  have hWc : ∀ {t : ℝ}, t ∈ Ioo 0 η → Continuous (bwdRef π η t) := fun ht =>
    continuous_heatFlowDensity π (sub_pos.2 ht.2)
  have hUc : ∀ {t : ℝ}, t ∈ Ioo 0 η → Continuous (bwdRatio π μ η t) := fun ht =>
    continuous_bwdRatio π μ ht.1 ht.2
  have hU0 : ∀ {t : ℝ}, t ∈ Ioo 0 η → ∀ z, bwdRatio π μ η t z ≠ 0 := fun ht z =>
    (bwdRatio_pos π μ ht.1 ht.2 z).ne'
  have hint : ∀ {P κ : ℝ}, 0 < κ →
      Integrable (fun z : ℝ => P * ((1 + z ^ 2) * Real.exp (-(κ * z ^ 2)))) :=
    fun hκ => (integrable_one_add_sq_mul_exp hκ).const_mul _
  have hflux : ∀ {t : ℝ} (ht : t ∈ Ioo 0 η) (l : Filter ℝ),
      Tendsto (fun z : ℝ => z ^ 2) l atTop → Tendsto
        (bklFlux (bwdRef π η) (bwdRatio π μ η) (bwdRefD1 π η) (bwdRatioD1 π μ η) t) l (𝓝 0) := by
    intro t ht l hl
    obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    have h := (tendsto_one_add_sq_mul_exp hκ l hl).const_mul P
    rw [mul_zero] at h
    refine squeeze_zero_norm (fun z => ?_) h
    rw [Real.norm_eq_abs]
    exact (hev.self_of_nhds z).2.2.2
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => hflux ht atBot
    tendsto_sq_atBot, fun t ht => hflux ht atTop tendsto_sq_atTop⟩
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    refine (hint (P := P) hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · unfold bklIntegrand
      exact ((hWc ht).mul ((hUc ht).mul ((hUc ht).log (hU0 ht)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact (hev.self_of_nhds z).1
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    exact ⟨_, hint (P := P) hκ, hev.mono fun r hr z => (hr z).2.1⟩
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    refine (hint (P := P) hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · unfold bFisherIntegrand
      exact (((hWc ht).mul ((continuous_bwdRatioD1 π μ ht.1 ht.2).pow 2)).div (hUc ht)
        (hU0 ht)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact (hev.self_of_nhds z).2.2.1

end Regular

/-! ### Warmness along the chain -/

/-- Kernel composition preserves warmness: `ρ ≤ c • π` gives `κ ∘ₘ ρ ≤ c • (κ ∘ₘ π)`. -/
theorem comp_le_smul_comp (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ] {ρ π : Measure ℝ} {c : ℝ≥0∞}
    (h : ρ ≤ c • π) : κ ∘ₘ ρ ≤ c • (κ ∘ₘ π) :=
  MeasureHelpers.comp_le_smul_comp κ h

end FormalizeSampling.ProximalSharpPerturbed
