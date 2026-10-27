module

public import FormalizeSampling.Samplers.ProximalSharpLSIPi
public import FormalizeSampling.Samplers.BackwardHeatFlowRegularityWarm
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Backward heat-flow regularity of the RGO step on `Fin d → ℝ` for warm laws

Status: **Verified** (no named hypotheses).

`ProximalSharpLSIPi` proves the sharp backward step of the proximal sampler on `Fin d → ℝ`
under `BackwardHeatFlowRegularPi π (forwardKernelPi η ∘ₘ ρ) η`. This file derives it for every
probability target with a Gaussian upper envelope `π ≤ C₂ • N(0, v I)` and every warm input law
`μ ≤ C • (forwardKernelPi η ∘ₘ π)` (`backwardHeatFlowRegularPi_of_warm`):

* the warm bound `μ ≤ C • π^Y` controls the backward ratio `U_r = ∫ φ_r(· - y)/w_η(y) dμ` and
  its first two derivatives uniformly, `(∂ᵢU)²/U` by Cauchy–Schwarz, and `|log U|` by
  `K (1 + |z|²)` (`exists_bwdRatioPi_bounds`);
* the Gaussian envelope `π ≤ C₂ • N(0, v I)` gives `w_s, |∇w_s|, |∇²w_s| ≤ N e^{-κ|z|²}`
  (`exists_heatFlowPi_envelope`);
* the one-dimensional pointwise algebra `ProximalSharpPerturbed.bwd_pointwise` then bounds
  every backward integrand by `P (1 + |z|²) e^{-κ|z|²}` (`exists_bwd_envelopePi`), which is
  Lebesgue integrable.

The declarations live in the namespace `ProximalSharpPerturbedPi`.

## Main results

* `backwardHeatFlowRegularPi_of_warm`: `BackwardHeatFlowRegularPi π μ η` for
  `π ≤ C₂ • N(0, v I)` and `μ ≤ C • (forwardKernelPi η ∘ₘ π)`.
* `comp_le_smul_comp`: kernel composition preserves warmness.

## Not proved here

* Non-warm input laws; the rate is extended to every finite-KL start by `KLWarmApprox` in
  `ProximalGeneralLSIPi`.
* Dimension-explicit constants: the envelope constants `M, K, N, P` are existential and depend
  on `d`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
open FormalizeSampling.BackwardHeatFlowPi FormalizeSampling.GaussianLSIPi
open FormalizeSampling.ProximalSharpLSIPi
open FormalizeSampling.HeatFlowRegularityPi (gc gc_pos gc_anti heatDensityPi_eq sum_sq_nonneg
  sq_le_sum_sq)
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalSharpPerturbedPi

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_withDensity_ofReal_iff)

variable {d : ℕ}

/-! ### Elementary Gaussian bounds -/

/-- `(1 + |v|²) φ_t(v)` is Lebesgue integrable (`t > 0`). -/
theorem integrable_one_add_sum_sq_mul_heatDensityPi {t : ℝ} (ht : 0 < t) :
    Integrable fun v : Fin d → ℝ => (1 + ∑ i, v i ^ 2) * heatDensityPi t v := by
  refine ((GaussianFunctionalLSIPi.integrable_heatDensityPi ht).add
    (GaussianFunctionalLSIPi.integrable_sumSq_mul_heatDensityPi ht)).congr
    (Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply]
  ring

/-- `(1 + |z|²) e^{-κ |z|²}` is Lebesgue integrable on `Fin d → ℝ` (`κ > 0`). -/
theorem integrable_one_add_sum_sq_mul_exp {κ : ℝ} (hκ : 0 < κ) :
    Integrable fun z : Fin d → ℝ => (1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2)) := by
  have hs : 0 < 1 / (2 * κ) := by positivity
  refine ((integrable_one_add_sum_sq_mul_heatDensityPi (d := d) hs).const_mul
    (gc d (1 / (2 * κ)))⁻¹).congr (Eventually.of_forall fun z => ?_)
  have hg := gc_pos (d := d) hs
  have e : -(∑ i, z i ^ 2) / (2 * (1 / (2 * κ))) = -(κ * ∑ i, z i ^ 2) := by
    field_simp
  simp only
  rw [heatDensityPi_eq, e]
  field_simp

/-- For `0 < a ≤ r ≤ b`: `(1 + |v|²) φ_r(v) ≤ (gc a / gc b) (1 + |v|²) φ_b(v)`. -/
theorem one_add_sum_sq_mul_heatDensityPi_le_of_mem {a b r : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hrb : r ≤ b) (v : Fin d → ℝ) :
    (1 + ∑ i, v i ^ 2) * heatDensityPi r v
      ≤ gc d a / gc d b * ((1 + ∑ i, v i ^ 2) * heatDensityPi b v) := by
  have hb : 0 < b := ha.trans_le (har.trans hrb)
  have h1 := heatDensityPi_le_exp (d := d) ha har hrb v
  have e : (Real.sqrt (2 * Real.pi * a))⁻¹ ^ d * Real.exp (-(∑ i, v i ^ 2) / (2 * b))
      = gc d a / gc d b * heatDensityPi b v := by
    rw [heatDensityPi_eq]
    have := gc_pos (d := d) hb
    unfold gc at this ⊢
    field_simp
  rw [e] at h1
  have := sum_sq_nonneg v
  have hS : 0 ≤ 1 + ∑ i, v i ^ 2 := by linarith
  calc (1 + ∑ i, v i ^ 2) * heatDensityPi r v
      ≤ (1 + ∑ i, v i ^ 2) * (gc d a / gc d b * heatDensityPi b v) :=
        mul_le_mul_of_nonneg_left h1 hS
    _ = _ := by ring

/-- For `0 < s₀ ≤ s ≤ s₁`: `(1 + |v|²) φ_s(v) ≤ E φ_{2s}(v)` with
`E = gc s₀ (1 + 4 s₁) / gc (2 s₁)`. -/
theorem one_add_sum_sq_mul_heatDensityPi_le_two {s₀ s₁ s : ℝ} (hs₀ : 0 < s₀) (h1 : s₀ ≤ s)
    (h2 : s ≤ s₁) (v : Fin d → ℝ) :
    (1 + ∑ i, v i ^ 2) * heatDensityPi s v
      ≤ gc d s₀ * (1 + 4 * s₁) / gc d (2 * s₁) * heatDensityPi (2 * s) v := by
  have hs : 0 < s := hs₀.trans_le h1
  set S := ∑ i, v i ^ 2 with hSdef
  have hS : 0 ≤ S := sum_sq_nonneg v
  have hg2 := gc_pos (d := d) (show 0 < 2 * s₁ by linarith)
  have hgs : gc d s ≤ gc d s₀ := gc_anti hs₀ h1
  have hg2s : gc d (2 * s₁) ≤ gc d (2 * s) := gc_anti (by linarith) (by linarith)
  have hE1 := ProximalSharpLSIPi.mul_exp_neg_le_inv (κ := 1 / (4 * s)) (by positivity) S
  have hE2 : Real.exp (-(1 / (4 * s) * S)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ 1 / (4 * s) * S := by positivity
    linarith)
  have hsplit : Real.exp (-S / (2 * s))
      = Real.exp (-(1 / (4 * s) * S)) * Real.exp (-S / (2 * (2 * s))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hpoly : (1 + S) * Real.exp (-(1 / (4 * s) * S)) ≤ 1 + 4 * s₁ := by
    have : 1 / (1 / (4 * s)) = 4 * s := by field_simp
    rw [this] at hE1
    nlinarith
  rw [heatDensityPi_eq, heatDensityPi_eq, hsplit]
  have hEx := Real.exp_pos (-S / (2 * (2 * s)))
  have hg0 := gc_pos (d := d) hs
  have hgs₀ := gc_pos (d := d) hs₀
  have hs₁ : 0 ≤ 1 + 4 * s₁ := by linarith
  have hE0 : 0 ≤ gc d s₀ * (1 + 4 * s₁) / gc d (2 * s₁) := by positivity
  calc (1 + S) * (gc d s * (Real.exp (-(1 / (4 * s) * S)) * Real.exp (-S / (2 * (2 * s)))))
      = gc d s * ((1 + S) * Real.exp (-(1 / (4 * s) * S))) * Real.exp (-S / (2 * (2 * s))) := by
        ring
    _ ≤ gc d s₀ * (1 + 4 * s₁) * Real.exp (-S / (2 * (2 * s))) := by gcongr
    _ = gc d s₀ * (1 + 4 * s₁) / gc d (2 * s₁) * (gc d (2 * s₁)
          * Real.exp (-S / (2 * (2 * s)))) := by
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc,
          mul_div_cancel₀ _ hg2.ne']
    _ ≤ _ := by gcongr

/-! ### Bounds on the backward ratio for warm input laws -/

section Warm

open FormalizeSampling.ProximalPi

variable (π μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
  {η C : ℝ}

omit [IsProbabilityMeasure μ] in
/-- **Warm integral bound.** If `μ ≤ C • π^Y` (`C ≥ 0`, `π^Y = forwardKernelPi η ∘ₘ π`, `η > 0`)
and `k ≥ 0` is Lebesgue integrable, then `∫ k(z - y) / w_η(y) dμ(y) ≤ C ∫ k`. -/
theorem integral_div_le_of_warmPi (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernelPi η ∘ₘ π)) {k : (Fin d → ℝ) → ℝ}
    (hk0 : ∀ v, 0 ≤ k v) (hki : Integrable k) (z : Fin d → ℝ) :
    ∫ y, k (z - y) / heatFlowDensityPi π η y ∂μ ≤ C * ∫ v, k v := by
  have hw := heatFlowDensityPi_pos π hη
  have hwc := continuous_heatFlowDensityPi π hη
  have hpY := forwardKernelPi_comp_eq_withDensity π hη
  set g : (Fin d → ℝ) → ℝ := fun y => k (z - y) / heatFlowDensityPi π η y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => div_nonneg (hk0 _) (hw y).le
  have hwg : (fun y => heatFlowDensityPi π η y * g y) = fun y => k (z - y) := by
    funext y; simp only [hg]; field_simp [(hw y).ne']
  have hgi : Integrable g (forwardKernelPi η ∘ₘ π) := by
    rw [hpY, integrable_withDensity_ofReal_iff hwc.measurable fun y => (hw y).le, hwg]
    exact hki.comp_sub_left z
  calc ∫ y, g y ∂μ ≤ ∫ y, g y ∂(ENNReal.ofReal C • (forwardKernelPi η ∘ₘ π)) :=
        integral_mono_measure hwarm (Eventually.of_forall hg0)
          (hgi.smul_measure ENNReal.ofReal_ne_top)
    _ = C * ∫ y, g y ∂(forwardKernelPi η ∘ₘ π) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]
    _ = C * ∫ v, k v := by
        rw [hpY, integral_withDensity_ofReal hwc.measurable fun y => (hw y).le, hwg,
          integral_sub_left_eq_self]

/-- **Bounds on the backward ratio for warm laws.** Let `π, μ` be probability laws on
`Fin d → ℝ` with `μ ≤ C • π^Y` (`C ≥ 0`, `η > 0`) and `0 < a ≤ b < η`. There are `M, K ≥ 0`
such that for all `r ∈ [a, b]`, `z` and coordinates `i, j`: `U_r(z) ≤ C`, `|∂ᵢU_r(z)| ≤ M`,
`|∂ᵢ∂ⱼU_r(z)| ≤ M`, `(∂ᵢU_r(z))² / U_r(z) ≤ M` and `|log U_r(z)| ≤ K (1 + |z|²)`, with
`U_r = bwdRatioPi π μ η r`. -/
theorem exists_bwdRatioPi_bounds (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernelPi η ∘ₘ π)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbη : b < η) :
    ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ ∀ r ∈ Icc a b, ∀ z,
      bwdRatioPi π μ η r z ≤ C ∧ (∀ i, |bwdRatioGradPi π μ η r z i| ≤ M) ∧
      (∀ i j, |bwdRatioHessPi π μ η r z i j| ≤ M) ∧
      (∀ i, bwdRatioGradPi π μ η r z i ^ 2 / bwdRatioPi π μ η r z ≤ M) ∧
      |Real.log (bwdRatioPi π μ η r z)| ≤ K * (1 + ∑ i, z i ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  have hw := heatFlowDensityPi_pos π hη
  set A₀ : ℝ := gc d a / gc d b with hA₀
  have hA₀0 : 0 < A₀ := div_pos (gc_pos ha) (gc_pos hb)
  set kb : (Fin d → ℝ) → ℝ := fun v => A₀ * ((1 + ∑ i, v i ^ 2) * heatDensityPi b v) with hkb
  have hkb0 : ∀ v, 0 ≤ kb v := fun v => by
    have := heatDensityPi_pos hb v; have := sum_sq_nonneg v; simp only [hkb]; positivity
  have hkbc : Continuous kb := by
    simp only [hkb]
    exact continuous_const.mul ((by fun_prop : Continuous fun v : Fin d → ℝ =>
      1 + ∑ i, v i ^ 2).mul (continuous_heatDensityPi b))
  have hkbi : Integrable kb := (integrable_one_add_sum_sq_mul_heatDensityPi hb).const_mul A₀
  have hkb_ge : ∀ r ∈ Icc a b, ∀ v, (1 + ∑ i, v i ^ 2) * heatDensityPi r v ≤ kb v :=
    fun r hr v => one_add_sum_sq_mul_heatDensityPi_le_of_mem ha hr.1 hr.2 v
  obtain ⟨Kb, Lb, hKb, hLb, hbb⟩ := exists_bwd_boundPi π hb le_rfl hbη
  have hkb_div : ∀ z y, kb (z - y) / heatFlowDensityPi π η y
      ≤ A₀ * (Kb * Real.exp (Lb * ∑ i, z i ^ 2)) := fun z y => by
    have := hbb b ⟨le_rfl, le_rfl⟩ z y
    simp only [hkb]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hA₀0.le
  have hkb_int : ∀ z, Integrable (fun y => kb (z - y) / heatFlowDensityPi π η y) μ := fun z =>
    Integrable.of_bound (continuous_div_heatFlowDensityPi π hη hkbc z).aestronglyMeasurable _
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (div_nonneg (hkb0 _) (hw y).le)]; exact hkb_div z y)
  have hwarmk : ∀ z, ∫ y, kb (z - y) / heatFlowDensityPi π η y ∂μ ≤ C * ∫ v, kb v := fun z =>
    integral_div_le_of_warmPi π μ hη hC hwarm hkb0 hkbi z
  set D : ℝ := (1 + 1 / a) ^ 2 with hD
  have hD1 : 1 ≤ D := by
    have : 0 < 1 / a := by positivity
    nlinarith
  have hDa : 1 / a ^ 2 ≤ D := by
    have : 0 < 1 / a := by positivity
    rw [hD, show 1 / a ^ 2 = (1 / a) ^ 2 by ring]; nlinarith
  set M : ℝ := D * (C * ∫ v, kb v) with hM
  have hIk : 0 ≤ ∫ v, kb v := integral_nonneg hkb0
  have hgη := gc_pos (d := d) hη
  obtain ⟨L, hL, hlogq⟩ :=
    HeatFlowRegularityPerturbedPi.exists_abs_log_heatFlowDensityPi_le μ ha hab
  set K : ℝ := |Real.log C| + |Real.log (gc d η)⁻¹| + L with hK
  refine ⟨M, K, by positivity, by positivity, fun r hr z => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrη : r < η := hr.2.trans_lt hbη
  obtain ⟨K₁, L₁, hK₁, hL₁, hb₁⟩ := bwd_integrand_boundPi π hr0 le_rfl hrη
  have hr' : r ∈ Icc r r := ⟨le_rfl, le_rfl⟩
  have hφint : Integrable (fun y => heatDensityPi r (z - y) / heatFlowDensityPi π η y) μ :=
    Integrable.of_bound (continuous_div_heatFlowDensityPi π hη (continuous_heatDensityPi r)
      z).aestronglyMeasurable _ (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hb₁ r hr' z y).1)
  have hU0 := bwdRatioPi_pos π μ hr0 hrη z
  -- (1) `U ≤ C`
  have hU : bwdRatioPi π μ η r z ≤ C := by
    have := integral_div_le_of_warmPi π μ hη hC hwarm (fun v => (heatDensityPi_pos hr0 v).le)
      (GaussianFunctionalLSIPi.integrable_heatDensityPi hr0) z
    rwa [GaussianFunctionalLSIPi.integral_heatDensityPi hr0, mul_one] at this
  -- domination of the derivatives of `φ_r` by `D kb`
  have hdom : ∀ {g : (Fin d → ℝ) → ℝ}, Continuous g →
      (∀ v, |g v| ≤ D * ((1 + ∑ i, v i ^ 2) * heatDensityPi r v)) →
      |∫ y, g (z - y) / heatFlowDensityPi π η y ∂μ| ≤ M := by
    intro g hg hgle
    have hpt : ∀ y, |g (z - y) / heatFlowDensityPi π η y|
        ≤ D * (kb (z - y) / heatFlowDensityPi π η y) := by
      intro y
      rw [abs_div, abs_of_pos (hw y), mul_div_assoc']
      exact div_le_div_of_nonneg_right ((hgle _).trans
        (mul_le_mul_of_nonneg_left (hkb_ge r hr _) (by positivity))) (hw y).le
    have hgi : Integrable (fun y => g (z - y) / heatFlowDensityPi π η y) μ :=
      ((hkb_int z).const_mul D).mono' (continuous_div_heatFlowDensityPi π hη hg
        z).aestronglyMeasurable (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hpt y)
    calc |∫ y, g (z - y) / heatFlowDensityPi π η y ∂μ|
        ≤ ∫ y, |g (z - y) / heatFlowDensityPi π η y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ y, D * (kb (z - y) / heatFlowDensityPi π η y) ∂μ :=
          integral_mono hgi.abs ((hkb_int z).const_mul D) hpt
      _ ≤ M := by
          rw [integral_const_mul, hM]
          exact mul_le_mul_of_nonneg_left (hwarmk z) (by positivity)
  have hU1 : ∀ i, |bwdRatioGradPi π μ η r z i| ≤ M := fun i =>
    hdom ((continuous_apply i).comp (continuous_heatGradPi r))
      (fun v => abs_heatGradPi_le_mul ha hr.1 v i)
  have hU2 : ∀ i j, |bwdRatioHessPi π μ η r z i j| ≤ M := fun i j =>
    hdom (continuous_heatHessPi r i j) (fun v => abs_heatHessPi_le_mul ha hr.1 v i j)
  -- Cauchy–Schwarz for the Fisher ratio
  have hU3 : ∀ i, bwdRatioGradPi π μ η r z i ^ 2 / bwdRatioPi π μ η r z ≤ M := by
    intro i
    set A : (Fin d → ℝ) → ℝ := fun y =>
      Real.sqrt (heatDensityPi r (z - y) / heatFlowDensityPi π η y)
    set B : (Fin d → ℝ) → ℝ := fun y => -((z - y) i / r) * A y
    have hA2 : ∀ y, A y ^ 2 = heatDensityPi r (z - y) / heatFlowDensityPi π η y := fun y =>
      Real.sq_sqrt (div_nonneg (heatDensityPi_pos hr0 _).le (hw y).le)
    have hAB : (fun y => A y * B y)
        = fun y => heatGradPi r (z - y) i / heatFlowDensityPi π η y := by
      funext y
      simp only [B, heatGradPi]
      have := hA2 y
      rw [show A y * (-((z - y) i / r) * A y) = -((z - y) i / r) * A y ^ 2 by ring, this]
      ring
    have hB2 : ∀ y, B y ^ 2
        = ((z - y) i / r) ^ 2 * (heatDensityPi r (z - y) / heatFlowDensityPi π η y) :=
      fun y => by simp only [B]; rw [mul_pow, neg_sq, hA2]
    have hB2le : ∀ y, B y ^ 2 ≤ D * (kb (z - y) / heatFlowDensityPi π η y) := by
      intro y
      rw [hB2, mul_div_assoc', mul_div_assoc']
      have hsq := sq_le_sum_sq (z - y) i
      have hS := sum_sq_nonneg (z - y)
      have h1 : ((z - y) i / r) ^ 2 ≤ 1 / a ^ 2 * (1 + ∑ k, (z - y) k ^ 2) := by
        rw [div_pow]
        have : 1 / r ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ ha.le hr.1 2)
        calc (z - y) i ^ 2 / r ^ 2 = (z - y) i ^ 2 * (1 / r ^ 2) := by ring
          _ ≤ (1 + ∑ k, (z - y) k ^ 2) * (1 / a ^ 2) := by
              gcongr; linarith
          _ = _ := by ring
      have h2 : ((z - y) i / r) ^ 2 * heatDensityPi r (z - y) ≤ D * kb (z - y) := by
        calc ((z - y) i / r) ^ 2 * heatDensityPi r (z - y)
            ≤ 1 / a ^ 2 * (1 + ∑ k, (z - y) k ^ 2) * heatDensityPi r (z - y) := by
              gcongr; exact (heatDensityPi_pos hr0 _).le
          _ = 1 / a ^ 2 * ((1 + ∑ k, (z - y) k ^ 2) * heatDensityPi r (z - y)) := by ring
          _ ≤ D * kb (z - y) := mul_le_mul hDa (hkb_ge r hr _)
              (mul_nonneg (by linarith) (heatDensityPi_pos hr0 _).le) (by linarith)
      exact div_le_div_of_nonneg_right h2 (hw y).le
    have hAi : Integrable (fun y => A y ^ 2) μ := by simp_rw [hA2]; exact hφint
    have hBm : AEStronglyMeasurable (fun y => B y ^ 2) μ := by
      simp_rw [hB2]
      exact ((by fun_prop : Continuous fun y : Fin d → ℝ => ((z - y) i / r) ^ 2).mul
        (continuous_div_heatFlowDensityPi π hη (continuous_heatDensityPi r)
          z)).aestronglyMeasurable
    have hBi : Integrable (fun y => B y ^ 2) μ :=
      ((hkb_int z).const_mul D).mono' hBm (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hB2le y)
    have hABi : Integrable (fun y => A y * B y) μ := by
      rw [hAB]
      exact Integrable.of_bound (continuous_div_heatFlowDensityPi π hη
        ((continuous_apply i).comp (continuous_heatGradPi r)) z).aestronglyMeasurable _
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact (hb₁ r hr' z y).2.1 i)
    have hUA : bwdRatioPi π μ η r z = ∫ y, A y ^ 2 ∂μ := by
      simp_rw [hA2]; rfl
    have hU1A : bwdRatioGradPi π μ η r z i = ∫ y, A y * B y ∂μ := by rw [hAB]; rfl
    have hcs := LogSobolev.sq_integral_mul_le_of_pos hAi hBi hABi (by rw [← hUA]; exact hU0)
    rw [← hUA, ← hU1A] at hcs
    have hBint : ∫ y, B y ^ 2 ∂μ ≤ M := by
      calc ∫ y, B y ^ 2 ∂μ ≤ ∫ y, D * (kb (z - y) / heatFlowDensityPi π η y) ∂μ :=
            integral_mono hBi ((hkb_int z).const_mul D) hB2le
        _ ≤ M := by
            rw [integral_const_mul, hM]
            exact mul_le_mul_of_nonneg_left (hwarmk z) (by positivity)
    rw [div_le_iff₀ hU0]
    have hB0 : 0 ≤ ∫ y, B y ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg (B y)
    nlinarith
  -- the logarithm
  have hUlow : (gc d η)⁻¹ * heatFlowDensityPi μ r z ≤ bwdRatioPi π μ η r z := by
    have hwle : ∀ y, (gc d η)⁻¹ * heatDensityPi r (z - y)
        ≤ heatDensityPi r (z - y) / heatFlowDensityPi π η y := by
      intro y
      have h1 := heatFlowDensityPi_le π hη y
      have h0 := (heatDensityPi_pos hr0 (z - y)).le
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_left h0 (hw y) h1
    have hφμ : Integrable (fun y => heatDensityPi r (z - y)) μ :=
      Integrable.of_bound ((continuous_heatDensityPi r).comp (by fun_prop)).aestronglyMeasurable
        (gc d r) (Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (heatDensityPi_pos hr0 _).le]; exact heatDensityPi_le hr0 _)
    unfold heatFlowDensityPi bwdRatioPi
    rw [← integral_const_mul]
    exact integral_mono (hφμ.const_mul _) hφint hwle
  have hq0 := heatFlowDensityPi_pos μ hr0 z
  have hlog : |Real.log (bwdRatioPi π μ η r z)| ≤ K * (1 + ∑ i, z i ^ 2) := by
    have hS := sum_sq_nonneg z
    have hup : Real.log (bwdRatioPi π μ η r z) ≤ |Real.log C| :=
      (Real.log_le_log hU0 hU).trans (le_abs_self _)
    have hdown : -(|Real.log (gc d η)⁻¹| + L * (1 + ∑ i, z i ^ 2))
        ≤ Real.log (bwdRatioPi π μ η r z) := by
      have h1 := Real.log_le_log (by positivity) hUlow
      rw [Real.log_mul (by positivity) hq0.ne'] at h1
      have h2 := hlogq r hr z
      have h3 := neg_abs_le (Real.log (gc d η)⁻¹)
      have h4 := neg_abs_le (Real.log (heatFlowDensityPi μ r z))
      linarith
    have hKS : K * (1 + ∑ i, z i ^ 2)
        = (|Real.log C| + |Real.log (gc d η)⁻¹|) * (1 + ∑ i, z i ^ 2)
          + L * (1 + ∑ i, z i ^ 2) := by rw [hK]; ring
    have h5 : |Real.log C| + |Real.log (gc d η)⁻¹|
        ≤ (|Real.log C| + |Real.log (gc d η)⁻¹|) * (1 + ∑ i, z i ^ 2) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    rw [abs_le]
    constructor
    · have := abs_nonneg (Real.log C); linarith
    · have := abs_nonneg (Real.log (gc d η)⁻¹)
      have : 0 ≤ L * (1 + ∑ i, z i ^ 2) := by positivity
      linarith
  exact ⟨hU, hU1, hU2, hU3, hlog⟩

end Warm

/-! ### Gaussian envelope of the reference heat flow -/

section Envelope

variable (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] {v C₂ : ℝ}

omit [IsProbabilityMeasure π] in
/-- If `π ≤ C₂ • N(0, v I)` (`v > 0`, `C₂ ≥ 0`) then `w_r(z) ≤ C₂ φ_{v + r}(z)` for `r > 0`. -/
theorem heatFlowDensityPi_le_of_envelope (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    {r : ℝ} (hr : 0 < r) (z : Fin d → ℝ) :
    heatFlowDensityPi π r z ≤ C₂ * heatDensityPi (v + r) z := by
  set G : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal
  have hc : Continuous fun x : Fin d → ℝ => heatDensityPi r (z - x) :=
    (continuous_heatDensityPi r).comp (by fun_prop)
  have hiG : Integrable (fun x => heatDensityPi r (z - x)) G :=
    Integrable.of_bound hc.aestronglyMeasurable ((Real.sqrt (2 * Real.pi * r))⁻¹ ^ d)
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensityPi_pos hr _).le]; exact heatDensityPi_le hr _)
  calc heatFlowDensityPi π r z = ∫ x, heatDensityPi r (z - x) ∂π := rfl
    _ ≤ ∫ x, heatDensityPi r (z - x) ∂(ENNReal.ofReal C₂ • G) :=
        integral_mono_measure henv (Eventually.of_forall fun x => (heatDensityPi_pos hr _).le)
          (hiG.smul_measure ENNReal.ofReal_ne_top)
    _ = C₂ * heatFlowDensityPi G r z := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC₂, smul_eq_mul]; rfl
    _ = C₂ * heatDensityPi (v + r) z := by rw [heatFlowDensityPi_gaussian hv hr]

/-- **Gaussian envelope of the heat flow of an enveloped law.** If `π ≤ C₂ • N(0, v I)`
(`v > 0`, `C₂ ≥ 0`) and `0 < s₀ ≤ s₁`, there is `N ≥ 0` such that for `s ∈ [s₀, s₁]` the
density `w_s`, its gradient and its Hessian are bounded by `N e^{-|z|²/(2(v + 2 s₁))}`. -/
theorem exists_heatFlowPi_envelope (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s₁) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ s ∈ Icc s₀ s₁, ∀ z : Fin d → ℝ,
      heatFlowDensityPi π s z ≤ N * Real.exp (-(1 / (2 * (v + 2 * s₁)) * ∑ i, z i ^ 2)) ∧
      (∀ i, |heatFlowGradPi π s z i|
        ≤ N * Real.exp (-(1 / (2 * (v + 2 * s₁)) * ∑ i, z i ^ 2))) ∧
      (∀ i j, |heatFlowHessPi π s z i j|
        ≤ N * Real.exp (-(1 / (2 * (v + 2 * s₁)) * ∑ i, z i ^ 2))) := by
  set D : ℝ := (1 + 1 / s₀) ^ 2 with hDdef
  set E : ℝ := gc d s₀ * (1 + 4 * s₁) / gc d (2 * s₁) with hEdef
  set G0 : ℝ := (Real.sqrt (2 * Real.pi * (v + s₀)))⁻¹ ^ d with hG0def
  have hD : 0 ≤ D := by positivity
  have hE : 0 ≤ E := by
    have := gc_pos (d := d) hs₀
    have := gc_pos (d := d) (show 0 < 2 * s₁ by linarith)
    have : 0 ≤ 1 + 4 * s₁ := by linarith
    positivity
  have hG0 : 0 ≤ G0 := by positivity
  refine ⟨(1 + D * E) * C₂ * G0, by positivity, fun s hs z => ?_⟩
  set e := Real.exp (-(1 / (2 * (v + 2 * s₁)) * ∑ i, z i ^ 2)) with hedef
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hφe : ∀ r, s₀ ≤ r → r ≤ 2 * s₁ → heatDensityPi (v + r) z ≤ G0 * e := by
    intro r h1 h2
    have := heatDensityPi_le_exp (d := d) (a := v + s₀) (t := v + r) (b := v + 2 * s₁)
      (by linarith)
      (by linarith) (by linarith) z
    have e' : -(∑ i, z i ^ 2) / (2 * (v + 2 * s₁))
        = -(1 / (2 * (v + 2 * s₁)) * ∑ i, z i ^ 2) := by ring
    rwa [e'] at this
  have hbase : ∀ r, s₀ ≤ r → r ≤ 2 * s₁ → heatFlowDensityPi π r z ≤ C₂ * G0 * e := by
    intro r h1 h2
    calc _ ≤ C₂ * heatDensityPi (v + r) z :=
          heatFlowDensityPi_le_of_envelope π hv hC₂ henv (by linarith) z
      _ ≤ C₂ * (G0 * e) := mul_le_mul_of_nonneg_left (hφe r h1 h2) hC₂
      _ = _ := by ring
  have hCGe : 0 ≤ C₂ * G0 * e := by positivity
  have hDE : 0 ≤ D * E := by positivity
  have hgen : ∀ g : (Fin d → ℝ) → ℝ,
      (∀ u, |g u| ≤ D * ((1 + ∑ i, u i ^ 2) * heatDensityPi s u)) →
      |∫ x, g (z - x) ∂π| ≤ (1 + D * E) * C₂ * G0 * e := by
    intro g hg
    have h2s : 0 < 2 * s := by linarith [hs.1]
    have hi : Integrable (fun x => D * E * heatDensityPi (2 * s) (z - x)) π :=
      (Integrable.of_bound ((continuous_heatDensityPi (2 * s)).comp
        (by fun_prop)).aestronglyMeasurable ((Real.sqrt (2 * Real.pi * (2 * s)))⁻¹ ^ d)
        (Eventually.of_forall fun x => by
          rw [Function.comp_apply, Real.norm_of_nonneg (heatDensityPi_pos h2s _).le]
          exact heatDensityPi_le h2s _)).const_mul _
    have hpt : ∀ u, |g u| ≤ D * E * heatDensityPi (2 * s) u := fun u => by
      calc |g u| ≤ D * ((1 + ∑ i, u i ^ 2) * heatDensityPi s u) := hg u
        _ ≤ D * (E * heatDensityPi (2 * s) u) := mul_le_mul_of_nonneg_left
            (one_add_sum_sq_mul_heatDensityPi_le_two hs₀ hs.1 hs.2 u) hD
        _ = _ := by ring
    calc |∫ x, g (z - x) ∂π| ≤ ∫ x, |g (z - x)| ∂π := abs_integral_le_integral_abs
      _ ≤ ∫ x, D * E * heatDensityPi (2 * s) (z - x) ∂π :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hi
            (Eventually.of_forall fun x => hpt _)
      _ = D * E * heatFlowDensityPi π (2 * s) z := by rw [integral_const_mul]; rfl
      _ ≤ D * E * (C₂ * G0 * e) := mul_le_mul_of_nonneg_left
          (hbase (2 * s) (by linarith [hs.1]) (by linarith [hs.2])) hDE
      _ ≤ (1 + D * E) * C₂ * G0 * e := by nlinarith
  refine ⟨?_, fun i => hgen (fun u => heatGradPi s u i)
      fun u => abs_heatGradPi_le_mul hs₀ hs.1 u i,
    fun i j => hgen (fun u => heatHessPi s u i j) fun u => abs_heatHessPi_le_mul hs₀ hs.1 u i j⟩
  calc heatFlowDensityPi π s z ≤ C₂ * G0 * e := hbase s hs.1 (by linarith [hs.2])
    _ ≤ (1 + D * E) * C₂ * G0 * e := by nlinarith

end Envelope

/-- `|∑ᵢ fᵢ| ≤ d X` when every `|fᵢ| ≤ X`. -/
theorem abs_sum_le_card_mul {f : Fin d → ℝ} {X : ℝ} (h : ∀ i, |f i| ≤ X) :
    |∑ i, f i| ≤ d * X := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, X := Finset.sum_le_sum fun i _ => h i
    _ = d * X := by simp

/-! ### Backward regularity for warm laws -/

section Regular

open FormalizeSampling.ProximalPi

variable (π μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
  {η C C₂ v : ℝ}

/-- **Uniform Gaussian envelope of the backward integrands.** For a warm law
`μ ≤ C • π^Y` and a target with `π ≤ C₂ • N(0, v I)`, every `t ∈ (0, η)` has a neighbourhood
on which the KL integrand, its time derivative, the Fisher integrand, the flux coordinates and
their derivatives are bounded by `P (1 + |z|²) e^{-κ |z|²}` (`κ > 0`). -/
theorem exists_bwd_envelopePi (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernelPi η ∘ₘ π)) (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    {t : ℝ} (ht : t ∈ Ioo 0 η) :
    ∃ P κ : ℝ, 0 ≤ P ∧ 0 < κ ∧ ∀ᶠ r in 𝓝 t, ∀ z,
      |bklIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) r z|
        ≤ P * ((1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2))) ∧
      |bklRatePi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRefHessPi π η) (bwdRatioHessPi π μ η)
          r z| ≤ P * ((1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2))) ∧
      |bFisherIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRatioGradPi π μ η) r z|
        ≤ P * ((1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2))) ∧
      (∀ i, |bklFluxPi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRefGradPi π η)
          (bwdRatioGradPi π μ η) r i z|
        ≤ P * ((1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2)))) ∧
      (∀ i, |bklFluxDerivPi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRatioGradPi π μ η)
          (bwdRefHessPi π η) (bwdRatioHessPi π μ η) r i z|
        ≤ P * ((1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2)))) := by
  obtain ⟨ht0, htη⟩ := ht
  set a := t / 2 with hadef
  set b := (t + η) / 2 with hbdef
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hbη : b < η := by simp only [b]; linarith
  obtain ⟨M, K, hM, hK, hU⟩ := exists_bwdRatioPi_bounds π μ hη hC hwarm ha hab hbη
  obtain ⟨N, hN, hW⟩ := exists_heatFlowPi_envelope π hv hC₂ henv (s₀ := η - b) (s₁ := η - a)
    (by linarith) (by linarith)
  set n : ℝ := (d : ℝ) + 1 with hndef
  have hn : 1 ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hdn : (d : ℝ) ≤ n := by simp only [n]; linarith
  set B₀ : ℝ := n * M * (K + 1) + C * K + n * M with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    have : 0 ≤ n := by linarith
    positivity
  have hκ : 0 < 1 / (2 * (v + 2 * (η - a))) := by
    have : 0 < η - a := by simp only [a]; linarith
    positivity
  refine ⟨((d : ℝ) + 3) * B₀ * (n * N), 1 / (2 * (v + 2 * (η - a))), by
    have : 0 ≤ n := by linarith
    positivity, hκ, ?_⟩
  have hI : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds (by simp only [a]; linarith)
    (by simp only [b]; linarith)
  filter_upwards [hI] with r hr z
  simp only [bklIntegrandPi, bklRatePi, bFisherIntegrandPi, bklFluxPi, bklFluxDerivPi,
    bwdRefPi, bwdRefGradPi, bwdRefHessPi]
  have hrI : r ∈ Icc a b := Ioo_subset_Icc_self hr
  have hsI : η - r ∈ Icc (η - b) (η - a) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨hu, hu1, hu2, hf, hl⟩ := hU r hrI z
  obtain ⟨hw, hw1, hw2⟩ := hW (η - r) hsI z
  have hu0 := bwdRatioPi_pos π μ (ha.trans hr.1) (hr.2.trans hbη) z
  have hw0 := heatFlowDensityPi_pos π (by linarith [hr.2] : (0 : ℝ) < η - r) z
  set e := Real.exp (-(1 / (2 * (v + 2 * (η - a))) * ∑ i, z i ^ 2)) with hedef
  set Q : ℝ := 1 + ∑ i, z i ^ 2 with hQdef
  have hQ : 1 ≤ Q := by have := sum_sq_nonneg z; simp only [Q]; linarith
  have hn0 : 0 ≤ n := by linarith
  have hNe : 0 ≤ N * e := by positivity
  have hle_n : ∀ {X : ℝ}, 0 ≤ X → X ≤ n * X := fun hX => le_mul_of_one_le_left hX hn
  have hdle_n : ∀ {X : ℝ}, 0 ≤ X → (d : ℝ) * X ≤ n * X := fun hX =>
    mul_le_mul_of_nonneg_right hdn hX
  set w := heatFlowDensityPi π (η - r) z with hwdef
  set u := bwdRatioPi π μ η r z with hudef
  set Bnd : ℝ := B₀ * (n * (N * e) * Q) with hBnd
  have hBnd0 : 0 ≤ Bnd := by
    have : 0 ≤ Q := by linarith
    positivity
  have hfin : ((d : ℝ) + 3) * B₀ * (n * N) * (Q * e) = ((d : ℝ) + 3) * Bnd := by
    simp only [Bnd]; ring
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1B : Bnd ≤ ((d : ℝ) + 3) * Bnd := le_mul_of_one_le_left hBnd0 (by linarith)
  have h3B : 3 * Bnd ≤ ((d : ℝ) + 3) * Bnd := mul_le_mul_of_nonneg_right (by linarith) hBnd0
  have hdB : (d : ℝ) * Bnd ≤ ((d : ℝ) + 3) * Bnd := mul_le_mul_of_nonneg_right (by linarith) hBnd0
  have bp : ∀ {w1 w2 u1 u2 : ℝ}, |w1| ≤ n * (N * e) → |w2| ≤ n * (N * e) → |u1| ≤ n * M →
      |u2| ≤ n * M → u1 ^ 2 / u ≤ n * M →
      |w * (u * Real.log u)| ≤ Bnd ∧
      |(w * u2 * (Real.log u + 1) - w2 * (u * Real.log u)) / 2| ≤ Bnd ∧
      |w * u1 ^ 2 / u| ≤ Bnd ∧
      |w * u1 * (Real.log u + 1) - w1 * (u * Real.log u)| ≤ Bnd :=
    fun h1 h2 h3 h4 h5 => by
      have := ProximalSharpPerturbed.bwd_pointwise hw0 (hw.trans (hle_n hNe)) h1 h2 hu0 hu h3
        h4 h5 hl hQ hK
      simpa only [hBnd, hB₀, mul_assoc] using this
  have hz1 : |(0 : ℝ)| ≤ n * (N * e) := by rw [abs_zero]; positivity
  have hz2 : |(0 : ℝ)| ≤ n * M := by rw [abs_zero]; positivity
  have hz3 : (0 : ℝ) ^ 2 / u ≤ n * M := by
    rw [zero_pow two_ne_zero, zero_div]; positivity
  have hWH : |∑ i, heatFlowHessPi π (η - r) z i i| ≤ n * (N * e) :=
    (abs_sum_le_card_mul fun i => hw2 i i).trans (hdle_n hNe)
  have hUH : |∑ i, bwdRatioHessPi π μ η r z i i| ≤ n * M :=
    (abs_sum_le_card_mul fun i => hu2 i i).trans (hdle_n hM)
  have hu1' : ∀ i, |bwdRatioGradPi π μ η r z i| ≤ n * M := fun i => (hu1 i).trans (hle_n hM)
  have hu2' : ∀ i j, |bwdRatioHessPi π μ η r z i j| ≤ n * M := fun i j =>
    (hu2 i j).trans (hle_n hM)
  have hf' : ∀ i, bwdRatioGradPi π μ η r z i ^ 2 / u ≤ n * M := fun i =>
    (hf i).trans (hle_n hM)
  have hw1' : ∀ i, |heatFlowGradPi π (η - r) z i| ≤ n * (N * e) := fun i =>
    (hw1 i).trans (hle_n hNe)
  have hw2' : ∀ i j, |heatFlowHessPi π (η - r) z i j| ≤ n * (N * e) := fun i j =>
    (hw2 i j).trans (hle_n hNe)
  rw [hfin]
  refine ⟨(bp hz1 hz1 hz2 hz2 hz3).1.trans h1B, (bp hz1 hWH hz2 hUH hz3).2.1.trans h1B, ?_,
    fun i => (bp (hw1' i) hz1 (hu1' i) hz2 (hf' i)).2.2.2.trans h1B, fun i => ?_⟩
  · have hdot : w * (bwdRatioGradPi π μ η r z ⬝ᵥ bwdRatioGradPi π μ η r z) / u
        = ∑ i, w * bwdRatioGradPi π μ η r z i ^ 2 / u := by
      simp only [dotProduct, Finset.mul_sum, Finset.sum_div, sq]
    rw [hdot]
    exact (abs_sum_le_card_mul fun i => (bp hz1 hz1 (hu1' i) hz2 (hf' i)).2.2.1).trans hdB
  · have h1 := bp hz1 (hw2' i i) (hu1' i) (hu2' i i) (hf' i)
    obtain ⟨y1, y2⟩ := abs_le.mp h1.2.1
    obtain ⟨z1, z2⟩ := abs_le.mp h1.2.2.1
    rw [abs_le]
    constructor <;> linarith

/-- **Backward regularity for warm laws (Verified).** If `π ≤ C₂ • N(0, v I)` (`v > 0`,
`C₂ ≥ 0`) and `μ ≤ C • π^Y` with `π^Y = forwardKernelPi η ∘ₘ π`, `η > 0`, `C ≥ 0`, then
`BackwardHeatFlowRegularPi π μ η`. -/
theorem backwardHeatFlowRegularPi_of_warm (hη : 0 < η) (hC : 0 ≤ C)
    (hwarm : μ ≤ ENNReal.ofReal C • (forwardKernelPi η ∘ₘ π)) (hv : 0 < v) (hC₂ : 0 ≤ C₂)
    (henv : π ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) :
    BackwardHeatFlowRegularPi π μ η := by
  have env := fun {t : ℝ} (ht : t ∈ Ioo 0 η) =>
    exists_bwd_envelopePi π μ hη hC hwarm hv hC₂ henv ht
  have hint : ∀ {P κ : ℝ}, 0 < κ → Integrable (fun z : Fin d → ℝ =>
      P * ((1 + ∑ i, z i ^ 2) * Real.exp (-(κ * ∑ i, z i ^ 2)))) :=
    fun hκ => (integrable_one_add_sum_sq_mul_exp hκ).const_mul _
  -- measurability of the ingredients
  have hW : ∀ {t : ℝ}, t ∈ Ioo 0 η → Measurable (bwdRefPi π η t) := fun ht =>
    (continuous_heatFlowDensityPi π (sub_pos.2 ht.2)).measurable
  have hWG : ∀ {t : ℝ}, t ∈ Ioo 0 η → ∀ i, Measurable fun z => bwdRefGradPi π η t z i :=
    fun ht i => (continuous_iff_continuousAt.2 fun z =>
      (hasFDerivAt_heatFlowGradPi π (sub_pos.2 ht.2) i z).continuousAt).measurable
  have hWH : ∀ {t : ℝ}, t ∈ Ioo 0 η → ∀ i j, Measurable fun z => bwdRefHessPi π η t z i j :=
    fun ht i j => (HeatFlowRegularityPi.continuous_heatFlowHessPi (ρ := π) (sub_pos.2 ht.2) i
      j).measurable
  have hU : ∀ {t : ℝ}, t ∈ Ioo 0 η → Measurable (bwdRatioPi π μ η t) := fun ht =>
    (continuous_bwdRatioPi π μ ht.1 ht.2).measurable
  have hUG : ∀ {t : ℝ}, t ∈ Ioo 0 η → ∀ i, Measurable fun z => bwdRatioGradPi π μ η t z i :=
    fun ht i => (continuous_bwdRatioGradPi π μ ht.1 ht.2 i).measurable
  have hUH : ∀ {t : ℝ}, t ∈ Ioo 0 η → ∀ i j,
      Measurable fun z => bwdRatioHessPi π μ η t z i j := by
    intro t ht i j
    have e : (fun z => bwdRatioHessPi π μ η t z i j)
        = fun z => fderiv ℝ (fun z => bwdRatioGradPi π μ η t z i) z (Pi.single j 1) := by
      funext z
      rw [(hasFDerivAt_bwdRatioGradPi_x π μ ht.1 ht.2 i z).fderiv, dotCLM_single]
    rw [e]
    exact measurable_fderiv_apply_const ℝ _ _
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht i => ?_, fun t ht i => ?_⟩
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    refine (hint (P := P) hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · unfold bklIntegrandPi
      exact ((hW ht).mul ((hU ht).mul (hU ht).log)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact (hev.self_of_nhds z).1
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    exact ⟨_, hint (P := P) hκ, hev.mono fun r hr z => (hr z).2.1⟩
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    refine (hint (P := P) hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · unfold bFisherIntegrandPi
      have hdot : Measurable fun z =>
          bwdRatioGradPi π μ η t z ⬝ᵥ bwdRatioGradPi π μ η t z := by
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun i _ => (hUG ht i).mul (hUG ht i)
      exact (((hW ht).mul hdot).div (hU ht)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact (hev.self_of_nhds z).2.2.1
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    refine (hint (P := P) hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · unfold bklFluxPi
      exact ((((hW ht).mul (hUG ht i)).mul ((hU ht).log.add measurable_const)).sub
        ((hWG ht i).mul ((hU ht).mul (hU ht).log))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact (hev.self_of_nhds z).2.2.2.1 i
  · obtain ⟨P, κ, _, hκ, hev⟩ := env ht
    refine (hint (P := P) hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · unfold bklFluxDerivPi
      exact (((((hW ht).mul (hUH ht i i)).mul ((hU ht).log.add measurable_const)).sub
        ((hWH ht i i).mul ((hU ht).mul (hU ht).log))).add
        (((hW ht).mul ((hUG ht i).pow_const 2)).div (hU ht))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact (hev.self_of_nhds z).2.2.2.2 i

end Regular

/-! ### Warmness along the chain -/

/-- Kernel composition preserves warmness: `ρ ≤ c • π` gives `κ ∘ₘ ρ ≤ c • (κ ∘ₘ π)`. -/
theorem comp_le_smul_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsSFiniteKernel κ] {ρ π : Measure X} {c : ℝ≥0∞} (h : ρ ≤ c • π) :
    κ ∘ₘ ρ ≤ c • (κ ∘ₘ π) :=
  MeasureHelpers.comp_le_smul_comp κ h

end FormalizeSampling.ProximalSharpPerturbedPi
