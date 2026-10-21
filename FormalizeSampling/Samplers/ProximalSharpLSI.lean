module

public import FormalizeSampling.Samplers.BackwardHeatFlow
public import FormalizeSampling.Samplers.ProximalSharp
public import FormalizeSampling.Samplers.ProximalHeatFlow

/-!
# PX-2, sharp form, from a functional LSI of the target: the backward step

Status: **Verified** for the construction of the backward heat flow of the RGO step, its
identification with the RGO through posterior kernels, and the backward strong data-processing
inequality under the explicit regularity hypotheses `BackwardHeatFlowRegular` (integrability /
domination / vanishing boundary flux on the open time interval `(0, η)`). The resulting sharp
PX-2 rate is **Conditional** only on `FunctionalLSI (target f) (1/α)` and these regularity
hypotheses (plus `HeatFlowRegular` for the forward step).

Setting (dimension one, as in `Samplers/Proximal.lean`): `π = target f`, step `η > 0`,
`π^Y = forwardKernel η ∘ₘ π`, `φ_t = heatDensity t`, `w_s = heatFlowDensity π s` (the density of
`π * N(0, s)`, `s > 0`), and an input law `μ` of the RGO step (in the sampler,
`μ = forwardKernel η ∘ₘ ρ`). For `t ∈ (0, η)` put
* `U t z = bwdRatio π μ η t z = ∫ φ_t(z - y) / w_η(y) dμ(y)` (the heat semigroup `N(0, t) * r`
  applied to `r = dμ/dπ^Y`, written without `r`);
* `W t z = w_{η - t}(z)`;
* the backward kernel `bwdKernel π η t y = w_{η-t}(z) φ_t(z - y) / w_η(y) dz`, the Bayes
  posterior of the Gaussian channel `forwardKernel t` for the prior `π * N(0, η - t)`.

Then `bwdKernel π η t ∘ₘ μ` has density `W t · U t` (`bwdKernel_comp_eq_withDensity`),
`bwdKernel π η t ∘ₘ π^Y = π * N(0, η - t)`, and the RGO factors through it
(`posterior_comp` in Mathlib): `rgoKernel f η =ᵐ (forwardKernel (η - t))†π ∘ₖ bwdKernel π η t`.
Data processing therefore gives, for every `t ∈ (0, η)`,
`KL(rgoKernel f η ∘ₘ μ‖π) ≤ Kb t ≤ KL(μ‖π^Y)` with `Kb t = KL(W_t U_t‖W_t) = ∫ W U log U`
(`klDiv_rgoKernel_comp_le_bwd`, `klDiv_bwd_le`; the integral form of the middle term, when
`W U log U` is integrable, is `toReal_klDiv_bwdKernel_comp_eq`). Inside `(0, η)`, `U` solves
the heat equation and `W` the backward heat equation (no hypothesis: the Gaussian factors
dominate the growth of `1 / w_η`, `exists_bwd_bound`), so the abstract backward de Bruijn
identity of `BackwardHeatFlow` gives `Kb' = -½ Ib`, `Ib = ∫ W (U')² / U`, and the functional
LSI of `π * N(0, η - t)` (constant `1/α + η - t`, from `FunctionalLSI π (1/α)` by convolution)
gives `2 α Kb ≤ (1 + α (η - t)) Ib`. The interior Grönwall comparison closes the step.

## Main results

* `toReal_klDiv_rgoKernel_comp_le_of_targetLSI` (**backward SDPI**): for a probability law `μ`
  with `KL(μ‖π^Y) < ∞`, `BackwardHeatFlowRegular π μ η` and `FunctionalLSI π (1/α)`:
  `KL(rgoKernel f η ∘ₘ μ‖π) < ∞` and
  `KL(rgoKernel f η ∘ₘ μ‖π) ≤ KL(μ‖π^Y) / (1 + α η)`.
* `toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI` (**sharp PX-2, one step**):
  `KL(proxKernel f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)²` under `FunctionalLSI π (1/α)`,
  `HeatFlowRegular ρ π s` (`(0, η] ⊆ s`) and `BackwardHeatFlowRegular π (forwardKernel η ∘ₘ ρ) η`.
* `toReal_klDiv_iterate_le_sq_of_targetLSI`: `k` steps, factor `(1 + α η)^{-2k}`.
* `integrable_exp_neg_of_klDiv_target_ne_top`, `integrable_exp_neg_of_klDiv_comp_target_ne_top`:
  finite KL against `π` (or against `κ ∘ₘ π`) already forces `∫ e^{-f} < ∞`, so the theorems
  above do not assume it.
* `exists_backwardHeatFlow_of_le`: the named hypotheses `BackwardHeatFlowDissipation` and
  `BackwardHeatFlowLSI` of `ProximalSharp` hold (for an explicit affine curve) whenever the
  backward SDPI holds; hence they are discharged under the hypotheses above
  (`exists_backwardHeatFlow_of_targetLSI`).

## Not proved here

* The fields of `BackwardHeatFlowRegular` are assumed here; they are proved for warm initial
  laws (`ρ ≤ C • π`) and targets with a Gaussian upper envelope in
  `Samplers/BackwardHeatFlowRegularityWarm.lean` (`backwardHeatFlowRegular_of_warm`). For
  non-warm laws they are not proved, but the warm-start rate is extended to every finite-KL start
  by `KLWarmApprox` (`Samplers/ProximalGeneralLSI.lean`).
* The curve `Kb` of `ProximalSharp.BackwardHeatFlowDissipation` produced here is an explicit
  affine majorant, not the KL along the backward flow: the latter need not have a right
  derivative at `t = 0`, and the contraction is proved without it (endpoints by data
  processing).
* Dimension `d`: see `Samplers/ProximalSharpLSIPi.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.BackwardHeatFlow
open FormalizeSampling.GaussianLSI
open scoped ENNReal NNReal FormalizeSampling.OU

namespace FormalizeSampling.ProximalSharpLSI

/-! ### Gaussian bounds -/

/-- `v² e^{-κ v²} ≤ 1/κ` for `κ > 0`. -/
theorem sq_mul_exp_neg_le {κ : ℝ} (hκ : 0 < κ) (v : ℝ) :
    v ^ 2 * Real.exp (-(κ * v ^ 2)) ≤ 1 / κ := by
  have h1 := Real.add_one_le_exp (κ * v ^ 2)
  have h2 : Real.exp (-(κ * v ^ 2)) * Real.exp (κ * v ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-(κ * v ^ 2))
  rw [le_div_iff₀ hκ]
  nlinarith [sq_nonneg v]

/-- For `0 < a ≤ t ≤ b`: `φ_t(v) ≤ (2π a)^{-1/2} e^{-v²/(2b)}`. -/
theorem heatDensity_le_exp {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) (v : ℝ) :
    heatDensity t v ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (-v ^ 2 / (2 * b)) := by
  have ht : 0 < t := ha.trans_le hat
  have h : -v ^ 2 / (2 * t) ≤ -v ^ 2 / (2 * b) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg v) (by positivity) (by linarith)
  unfold heatDensity
  exact mul_le_mul (inv_anti₀ (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))) (Real.exp_le_exp.2 h)
    (Real.exp_pos _).le (by positivity)

/-- For `0 < a ≤ t`: `|φ_t'(v)| ≤ (1 + 1/a)² (1 + v²) φ_t(v)`. -/
theorem abs_heatDensityD1_le_mul {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (v : ℝ) :
    |heatDensityD1 t v| ≤ (1 + 1 / a) ^ 2 * ((1 + v ^ 2) * heatDensity t v) := by
  have ht : 0 < t := ha.trans_le hat
  have hφ := heatDensity_pos ht v
  unfold heatDensityD1
  rw [abs_mul, abs_neg, abs_div, abs_of_pos ht, abs_of_pos hφ]
  have h1 : |v| ≤ 1 + v ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
  have h2 : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha hat
  have h3 : 1 / a ≤ (1 + 1 / a) ^ 2 := by
    have : 0 < 1 / a := by positivity
    nlinarith
  calc |v| / t * heatDensity t v = |v| * (1 / t) * heatDensity t v := by ring
    _ ≤ (1 + v ^ 2) * (1 / a) * heatDensity t v := by gcongr
    _ ≤ (1 + v ^ 2) * (1 + 1 / a) ^ 2 * heatDensity t v := by gcongr
    _ = _ := by ring

/-- For `0 < a ≤ t`: `|φ_t''(v)| ≤ (1 + 1/a)² (1 + v²) φ_t(v)`. -/
theorem abs_heatDensityD2_le_mul {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (v : ℝ) :
    |heatDensityD2 t v| ≤ (1 + 1 / a) ^ 2 * ((1 + v ^ 2) * heatDensity t v) := by
  have ht : 0 < t := ha.trans_le hat
  have hφ := heatDensity_pos ht v
  unfold heatDensityD2
  rw [abs_mul, abs_of_pos hφ]
  have h2 : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha hat
  have h2' : 1 / t ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ ha.le hat 2)
  have h1 : |v ^ 2 / t ^ 2 - 1 / t| ≤ v ^ 2 * (1 / t ^ 2) + 1 / t := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_one_div]
  have h3 : v ^ 2 * (1 / t ^ 2) + 1 / t ≤ (1 + 1 / a) ^ 2 * (1 + v ^ 2) := by
    have e : (1 + 1 / a) ^ 2 * (1 + v ^ 2) = (1 + 2 * (1 / a) + (1 / a) ^ 2) * (1 + v ^ 2) := by
      ring
    have ha' : 0 < 1 / a := by positivity
    have : 1 / a ^ 2 = (1 / a) ^ 2 := by rw [one_div_pow]
    rw [e]
    nlinarith [sq_nonneg v, mul_le_mul_of_nonneg_left h2' (sq_nonneg v)]
  calc |v ^ 2 / t ^ 2 - 1 / t| * heatDensity t v
      ≤ (1 + 1 / a) ^ 2 * (1 + v ^ 2) * heatDensity t v := by gcongr; exact h1.trans h3
    _ = _ := by ring

/-- `-A (z - y)² + β y² ≤ (A β / (A - β)) z²` for `β < A`. -/
theorem neg_mul_sq_add_le {A β : ℝ} (hAβ : β < A) (z y : ℝ) :
    -(A * (z - y) ^ 2) + β * y ^ 2 ≤ A * β / (A - β) * z ^ 2 := by
  have h : 0 < A - β := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h]
  nlinarith [sq_nonneg (A * z - (A - β) * y)]

section Lower

variable (π : Measure ℝ) [IsProbabilityMeasure π]

/-- `(y - x)²/(2η) ≤ y²/(2b) + R²/(2(η - b))` for `|x| ≤ R`, `0 < b < η`. -/
theorem sq_div_le_of_abs_le {b η R x y : ℝ} (hb : 0 < b) (hbη : b < η) (hx : |x| ≤ R) :
    (y - x) ^ 2 / (2 * η) ≤ y ^ 2 / (2 * b) + R ^ 2 / (2 * (η - b)) := by
  have hη : 0 < η := hb.trans hbη
  have hηb : 0 < η - b := by linarith
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have hyx : (y - x) ^ 2 ≤ (|y| + R) ^ 2 := by
    rw [← sq_abs (y - x)]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub y x).trans (by linarith)) 2
  have key : (|y| + R) ^ 2 / (2 * η) = y ^ 2 / (2 * b) + R ^ 2 / (2 * (η - b))
      - ((η - b) * |y| - b * R) ^ 2 / (2 * η * b * (η - b)) := by
    rw [← sq_abs y]
    field_simp
    ring
  have h2 : 0 ≤ ((η - b) * |y| - b * R) ^ 2 / (2 * η * b * (η - b)) := by positivity
  calc (y - x) ^ 2 / (2 * η) ≤ (|y| + R) ^ 2 / (2 * η) := by gcongr
    _ ≤ _ := by rw [key]; linarith

/-- **Gaussian lower bound for `π * N(0, η)`.** For a probability `π` and `0 < b < η` there is
`c > 0` with `c e^{-y²/(2b)} ≤ w_η(y) = heatFlowDensity π η y` for all `y`. -/
theorem exists_mul_exp_le_heatFlowDensity {b η : ℝ} (hb : 0 < b) (hbη : b < η) :
    ∃ c > 0, ∀ y, c * Real.exp (-y ^ 2 / (2 * b)) ≤ heatFlowDensity π η y := by
  have hη : 0 < η := hb.trans hbη
  obtain ⟨n, hn⟩ : ∃ n : ℕ, π (Icc (-(n : ℝ)) n) ≠ 0 := by
    by_contra! h
    have hU : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) n := by
      ext x
      simp only [mem_univ, mem_iUnion, mem_Icc, true_iff]
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have : π univ = 0 := by rw [hU]; exact measure_iUnion_null h
    simp at this
  set R : ℝ := (n : ℝ) with hR
  set m : ℝ := (π (Icc (-R) R)).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hn (measure_ne_top _ _)
  set c₀ : ℝ := (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(R ^ 2 / (2 * (η - b))))
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨m * c₀, by positivity, fun y => ?_⟩
  have hint : Integrable (fun x => heatDensity η (y - x)) π :=
    Integrable.of_bound ((continuous_heatDensity η).comp (by fun_prop)).aestronglyMeasurable
      (Real.sqrt (2 * Real.pi * η))⁻¹ (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensity_pos hη _).le]; exact heatDensity_le hη _)
  have h1 : ∫ x in Icc (-R) R, heatDensity η (y - x) ∂π ≤ heatFlowDensity π η y :=
    setIntegral_le_integral hint (Eventually.of_forall fun x => (heatDensity_pos hη _).le)
  have h2 : ∀ x ∈ Icc (-R) R, c₀ * Real.exp (-y ^ 2 / (2 * b)) ≤ heatDensity η (y - x) := by
    intro x hx
    have hx' : |x| ≤ R := abs_le.2 hx
    unfold heatDensity
    rw [mul_assoc, ← Real.exp_add]
    gcongr
    have := sq_div_le_of_abs_le (y := y) hb hbη hx'
    rw [neg_div, neg_div]
    linarith
  have h3 := setIntegral_mono_on (integrable_const (c₀ * Real.exp (-y ^ 2 / (2 * b))))
    hint.integrableOn measurableSet_Icc h2
  rw [setIntegral_const, smul_eq_mul] at h3
  have hreal : π.real (Icc (-R) R) = m := rfl
  rw [hreal] at h3
  linarith

/-- **Domination of the backward kernel.** For a probability `π`, `0 < a ≤ b < η`, there are
`K ≥ 0`, `L ≥ 0` such that for all `t ∈ [a, b]` and all `z, y`:
`(1 + (z - y)²) φ_t(z - y) / w_η(y) ≤ K e^{L z²}`. (The Gaussian decay of `φ_t`, `t < η`, beats
the at most Gaussian growth `e^{y²/(2b')}`, `b' < η`, of `1/w_η`.) -/
theorem exists_bwd_bound {η a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbη : b < η) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ z y : ℝ,
      (1 + (z - y) ^ 2) * heatDensity t (z - y) / heatFlowDensity π η y
        ≤ K * Real.exp (L * z ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  set b₁ := (2 * b + η) / 3 with hb₁
  set b₂ := (b + 2 * η) / 3 with hb₂
  have hbb₁ : b < b₁ := by rw [hb₁]; linarith
  have hb₁b₂ : b₁ < b₂ := by rw [hb₁, hb₂]; linarith
  have hb₂η : b₂ < η := by rw [hb₂]; linarith
  have hb₁0 : 0 < b₁ := hb.trans hbb₁
  have hb₂0 : 0 < b₂ := hb₁0.trans hb₁b₂
  obtain ⟨c, hc, hlow⟩ := exists_mul_exp_le_heatFlowDensity π hb₂0 hb₂η
  set κ := 1 / (2 * b) - 1 / (2 * b₁) with hκ
  have hκ0 : 0 < κ := by
    rw [hκ, sub_pos]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set A := 1 / (2 * b₁) with hA
  set β := 1 / (2 * b₂) with hβ
  have hβ0 : 0 < β := by positivity
  have hAβ : β < A := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set C₀ := (Real.sqrt (2 * Real.pi * a))⁻¹ with hC₀
  refine ⟨C₀ * (1 + 1 / κ) / c, A * β / (A - β), by positivity,
    div_nonneg (by positivity) (by linarith), fun t ht z y => ?_⟩
  set v := z - y
  have hw := hlow y
  have hw0 : 0 < heatFlowDensity π η y := lt_of_lt_of_le (by positivity) hw
  rw [div_le_iff₀ hw0]
  have hφ := heatDensity_le_exp ha ht.1 ht.2 v
  have hsplit : Real.exp (-v ^ 2 / (2 * b))
      = Real.exp (-(κ * v ^ 2)) * Real.exp (-(A * v ^ 2)) := by
    rw [← Real.exp_add]; congr 1; rw [hκ, hA]; field_simp; ring
  have hpoly : (1 + v ^ 2) * Real.exp (-(κ * v ^ 2)) ≤ 1 + 1 / κ := by
    have := sq_mul_exp_neg_le hκ0 v
    have : Real.exp (-(κ * v ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ κ * v ^ 2 := by positivity
      linarith)
    nlinarith
  have hquad := neg_mul_sq_add_le hAβ z y
  have hexp : Real.exp (-(A * v ^ 2)) ≤ Real.exp (A * β / (A - β) * z ^ 2)
      * Real.exp (-y ^ 2 / (2 * b₂)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : -y ^ 2 / (2 * b₂) = -(β * y ^ 2) := by rw [hβ]; ring
    rw [this]
    linarith
  have hφ0 := (heatDensity_pos (ha.trans_le ht.1) v).le
  calc (1 + v ^ 2) * heatDensity t v
      ≤ (1 + v ^ 2) * (C₀ * (Real.exp (-(κ * v ^ 2)) * Real.exp (-(A * v ^ 2)))) := by
        rw [← hsplit]; gcongr
    _ = C₀ * ((1 + v ^ 2) * Real.exp (-(κ * v ^ 2))) * Real.exp (-(A * v ^ 2)) := by ring
    _ ≤ C₀ * (1 + 1 / κ) * (Real.exp (A * β / (A - β) * z ^ 2)
          * Real.exp (-y ^ 2 / (2 * b₂))) := by gcongr
    _ = C₀ * (1 + 1 / κ) / c * Real.exp (A * β / (A - β) * z ^ 2)
          * (c * Real.exp (-y ^ 2 / (2 * b₂))) := by field_simp
    _ ≤ _ := by gcongr

end Lower

/-! ### The backward ratio `U` and the reference `W` -/

/-- The backward ratio `U t z = ∫ φ_t(z - y) / w_η(y) dμ(y)` with `w_η = heatFlowDensity π η`:
for `μ ≪ π^Y` it is the heat semigroup `N(0, t) * r` applied to `r = dμ/dπ^Y`. -/
noncomputable def bwdRatio (π μ : Measure ℝ) (η t z : ℝ) : ℝ :=
  ∫ y, heatDensity t (z - y) / heatFlowDensity π η y ∂μ

/-- The space derivative of `bwdRatio`: `∫ φ_t'(z - y) / w_η(y) dμ(y)`
(`hasDerivAt_bwdRatio_x`). -/
noncomputable def bwdRatioD1 (π μ : Measure ℝ) (η t z : ℝ) : ℝ :=
  ∫ y, heatDensityD1 t (z - y) / heatFlowDensity π η y ∂μ

/-- The second space derivative of `bwdRatio`: `∫ φ_t''(z - y) / w_η(y) dμ(y)`
(`hasDerivAt_bwdRatioD1_x`). -/
noncomputable def bwdRatioD2 (π μ : Measure ℝ) (η t z : ℝ) : ℝ :=
  ∫ y, heatDensityD2 t (z - y) / heatFlowDensity π η y ∂μ

section Ratio

variable (π μ : Measure ℝ) [IsProbabilityMeasure π] [IsFiniteMeasure μ] {η : ℝ}

/-- Pointwise domination of the three integrands of `bwdRatio`, `bwdRatioD1`, `bwdRatioD2`:
for `0 < a ≤ b < η` there are `K, L ≥ 0` with `|φ_t^{(k)}(z - y)| / w_η(y) ≤ K e^{L z²}`
(`k = 0, 1, 2`) for `t ∈ [a, b]` and all `z, y`. -/
theorem bwd_integrand_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbη : b < η) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ z y : ℝ,
      |heatDensity t (z - y) / heatFlowDensity π η y| ≤ K * Real.exp (L * z ^ 2) ∧
      |heatDensityD1 t (z - y) / heatFlowDensity π η y| ≤ K * Real.exp (L * z ^ 2) ∧
      |heatDensityD2 t (z - y) / heatFlowDensity π η y| ≤ K * Real.exp (L * z ^ 2) := by
  have hη : 0 < η := ha.trans_le hab |>.trans hbη
  obtain ⟨K₀, L, hK₀, hL, hb⟩ := exists_bwd_bound π ha hab hbη
  have hD : 1 ≤ (1 + 1 / a) ^ 2 := by
    have : 0 < 1 / a := by positivity
    nlinarith
  refine ⟨(1 + 1 / a) ^ 2 * K₀, L, by positivity, hL, fun t ht z y => ?_⟩
  have hw := heatFlowDensity_pos π hη y
  have ht0 : 0 < t := ha.trans_le ht.1
  have hφ := heatDensity_pos ht0 (z - y)
  have hb' := hb t ht z y
  have hE : 0 ≤ K₀ * Real.exp (L * z ^ 2) := by positivity
  have hmain : (1 + (z - y) ^ 2) * heatDensity t (z - y) / heatFlowDensity π η y
      ≤ K₀ * Real.exp (L * z ^ 2) := hb'
  have h0 : heatDensity t (z - y) / heatFlowDensity π η y
      ≤ (1 + (z - y) ^ 2) * heatDensity t (z - y) / heatFlowDensity π η y := by
    gcongr
    nlinarith [sq_nonneg (z - y)]
  rw [abs_div, abs_div, abs_div, abs_of_pos hw, abs_of_pos hφ]
  refine ⟨?_, ?_, ?_⟩
  · calc heatDensity t (z - y) / heatFlowDensity π η y ≤ K₀ * Real.exp (L * z ^ 2) :=
          h0.trans hmain
      _ ≤ _ := by rw [mul_assoc]; exact le_mul_of_one_le_left hE hD
  · calc |heatDensityD1 t (z - y)| / heatFlowDensity π η y
        ≤ (1 + 1 / a) ^ 2 * ((1 + (z - y) ^ 2) * heatDensity t (z - y))
            / heatFlowDensity π η y := by
          gcongr; exact abs_heatDensityD1_le_mul ha ht.1 _
      _ = (1 + 1 / a) ^ 2 * ((1 + (z - y) ^ 2) * heatDensity t (z - y)
            / heatFlowDensity π η y) := by ring
      _ ≤ _ := by rw [mul_assoc]; gcongr
  · calc |heatDensityD2 t (z - y)| / heatFlowDensity π η y
        ≤ (1 + 1 / a) ^ 2 * ((1 + (z - y) ^ 2) * heatDensity t (z - y))
            / heatFlowDensity π η y := by
          gcongr; exact abs_heatDensityD2_le_mul ha ht.1 _
      _ = (1 + 1 / a) ^ 2 * ((1 + (z - y) ^ 2) * heatDensity t (z - y)
            / heatFlowDensity π η y) := by ring
      _ ≤ _ := by rw [mul_assoc]; gcongr

omit [IsFiniteMeasure μ] in
/-- Continuity of `y ↦ g(z - y) / w_η(y)` for continuous `g`. -/
theorem continuous_div_heatFlowDensity (hη : 0 < η) {g : ℝ → ℝ} (hg : Continuous g)
    (z : ℝ) : Continuous (fun y => g (z - y) / heatFlowDensity π η y) :=
  (hg.comp (by fun_prop)).div (continuous_heatFlowDensity π hη)
    fun y => (heatFlowDensity_pos π hη y).ne'

omit [IsFiniteMeasure μ] in
/-- Measurability of `y ↦ g(z - y) / w_η(y)` for continuous `g`. -/
theorem aestronglyMeasurable_div_heatFlowDensity (hη : 0 < η) {g : ℝ → ℝ} (hg : Continuous g)
    (z : ℝ) : AEStronglyMeasurable (fun y => g (z - y) / heatFlowDensity π η y) μ :=
  (continuous_div_heatFlowDensity π hη hg z).aestronglyMeasurable

/-- `z ↦ U t z` has derivative `bwdRatioD1` (for `0 < t < η`, any finite `μ`). -/
theorem hasDerivAt_bwdRatio_x {t : ℝ} (ht : 0 < t) (htη : t < η) (z₀ : ℝ) :
    HasDerivAt (bwdRatio π μ η t) (bwdRatioD1 π μ η t z₀) z₀ := by
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_bound π ht le_rfl htη
  have hz : ∀ z ∈ Metric.ball z₀ 1, K * Real.exp (L * z ^ 2)
      ≤ K * Real.exp (L * (|z₀| + 1) ^ 2) := by
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have h1 : |z| ≤ |z₀| + 1 := by
      have := abs_sub_abs_le_abs_sub z z₀; linarith
    have h2 : z ^ 2 ≤ (|z₀| + 1) ^ 2 := by
      rw [← sq_abs z]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    gcongr
  have ht' : t ∈ Icc t t := ⟨le_rfl, le_rfl⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (Metric.ball_mem_nhds z₀ one_pos)
    (F := fun z y => heatDensity t (z - y) / heatFlowDensity π η y)
    (F' := fun z y => heatDensityD1 t (z - y) / heatFlowDensity π η y)
    (bound := fun _ => K * Real.exp (L * (|z₀| + 1) ^ 2))
    (Eventually.of_forall fun z =>
      aestronglyMeasurable_div_heatFlowDensity π μ hη (continuous_heatDensity t) z)
    (Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
      (continuous_heatDensity t) z₀) _ (Eventually.of_forall fun y => (hb t ht' z₀ y).1))
    (aestronglyMeasurable_div_heatFlowDensity π μ hη (continuous_heatDensityD1 ht) z₀)
    (Eventually.of_forall fun y z hz' => ((hb t ht' z y).2.1).trans (hz z hz'))
    (integrable_const _) (Eventually.of_forall fun y z _ => ?_)).2
  exact ((hasDerivAt_heatDensity_x t (z - y)).comp_sub_const z y).div_const _

/-- `z ↦ bwdRatioD1 t z` has derivative `bwdRatioD2` (for `0 < t < η`, any finite `μ`). -/
theorem hasDerivAt_bwdRatioD1_x {t : ℝ} (ht : 0 < t) (htη : t < η) (z₀ : ℝ) :
    HasDerivAt (bwdRatioD1 π μ η t) (bwdRatioD2 π μ η t z₀) z₀ := by
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_bound π ht le_rfl htη
  have hz : ∀ z ∈ Metric.ball z₀ 1, K * Real.exp (L * z ^ 2)
      ≤ K * Real.exp (L * (|z₀| + 1) ^ 2) := by
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have h1 : |z| ≤ |z₀| + 1 := by
      have := abs_sub_abs_le_abs_sub z z₀; linarith
    have h2 : z ^ 2 ≤ (|z₀| + 1) ^ 2 := by
      rw [← sq_abs z]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    gcongr
  have ht' : t ∈ Icc t t := ⟨le_rfl, le_rfl⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (Metric.ball_mem_nhds z₀ one_pos)
    (F := fun z y => heatDensityD1 t (z - y) / heatFlowDensity π η y)
    (F' := fun z y => heatDensityD2 t (z - y) / heatFlowDensity π η y)
    (bound := fun _ => K * Real.exp (L * (|z₀| + 1) ^ 2))
    (Eventually.of_forall fun z =>
      aestronglyMeasurable_div_heatFlowDensity π μ hη (continuous_heatDensityD1 ht) z)
    (Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
      (continuous_heatDensityD1 ht) z₀) _ (Eventually.of_forall fun y => (hb t ht' z₀ y).2.1))
    (aestronglyMeasurable_div_heatFlowDensity π μ hη (continuous_heatDensityD2 t) z₀)
    (Eventually.of_forall fun y z hz' => ((hb t ht' z y).2.2).trans (hz z hz'))
    (integrable_const _) (Eventually.of_forall fun y z _ => ?_)).2
  exact ((hasDerivAt_heatDensityD1_x ht.ne' (z - y)).comp_sub_const z y).div_const _

/-- **Heat equation for `U`.** For `0 < t < η` and every `z`, `∂_t U(t, z) = ½ ∂_z² U(t, z)`:
`HasDerivAt (fun r => bwdRatio π μ η r z) (bwdRatioD2 π μ η t z / 2) t` (any finite `μ`). -/
theorem hasDerivAt_bwdRatio_t {t : ℝ} (ht : 0 < t) (htη : t < η) (z : ℝ) :
    HasDerivAt (fun r => bwdRatio π μ η r z) (bwdRatioD2 π μ η t z / 2) t := by
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_bound π (η := η) (a := t / 2) (b := (t + η) / 2)
    (by linarith) (by linarith) (by linarith)
  have hs : Ioo (t / 2) ((t + η) / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hmem : ∀ r ∈ Ioo (t / 2) ((t + η) / 2), r ∈ Icc (t / 2) ((t + η) / 2) :=
    fun r hr => Ioo_subset_Icc_self hr
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hs
    (F := fun r y => heatDensity r (z - y) / heatFlowDensity π η y)
    (F' := fun r y => heatDensityD2 r (z - y) / heatFlowDensity π η y / 2)
    (bound := fun _ => K * Real.exp (L * z ^ 2))
    (Eventually.of_forall fun r =>
      aestronglyMeasurable_div_heatFlowDensity π μ hη (continuous_heatDensity r) z)
    (Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
      (continuous_heatDensity t) z) _ (Eventually.of_forall fun y =>
        (hb t ⟨by linarith, by linarith⟩ z y).1))
    ((continuous_div_heatFlowDensity π hη (continuous_heatDensityD2 t) z).div_const
      2).aestronglyMeasurable
    (Eventually.of_forall fun y r hr => by
      rw [Real.norm_eq_abs, abs_div, abs_two]
      have := (hb r (hmem r hr) z y).2.2
      have h0 : 0 ≤ |heatDensityD2 r (z - y) / heatFlowDensity π η y| := abs_nonneg _
      linarith)
    (integrable_const _) (Eventually.of_forall fun y r hr => ?_)).2
  · rw [integral_div] at hd
    exact hd
  · have hr0 : 0 < r := by linarith [hr.1]
    exact ((hasDerivAt_heatDensity_t hr0 (z - y)).div_const _).congr_deriv (by ring)

/-- `U t z > 0` for `0 < t < η` and a nonzero finite `μ`. -/
theorem bwdRatio_pos [NeZero μ] {t : ℝ} (ht : 0 < t) (htη : t < η) (z : ℝ) :
    0 < bwdRatio π μ η t z := by
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_bound π ht le_rfl htη
  have hi : Integrable (fun y => heatDensity t (z - y) / heatFlowDensity π η y) μ :=
    Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
      (continuous_heatDensity t) z) _ (Eventually.of_forall fun y =>
        (hb t ⟨le_rfl, le_rfl⟩ z y).1)
  have hpos : ∀ y, 0 < heatDensity t (z - y) / heatFlowDensity π η y := fun y =>
    div_pos (heatDensity_pos ht _) (heatFlowDensity_pos π hη y)
  unfold bwdRatio
  rw [integral_pos_iff_support_of_nonneg (fun y => (hpos y).le) hi]
  have : Function.support (fun y => heatDensity t (z - y) / heatFlowDensity π η y) = univ :=
    eq_univ_of_forall fun y => (hpos y).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne μ)

/-- `U t` is continuous (`0 < t < η`). -/
theorem continuous_bwdRatio {t : ℝ} (ht : 0 < t) (htη : t < η) :
    Continuous (bwdRatio π μ η t) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_bwdRatio_x π μ ht htη z).continuousAt

/-- `U t'` is continuous (`0 < t < η`). -/
theorem continuous_bwdRatioD1 {t : ℝ} (ht : 0 < t) (htη : t < η) :
    Continuous (bwdRatioD1 π μ η t) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_bwdRatioD1_x π μ ht htη z).continuousAt

end Ratio

/-- **Backward heat equation for `W`.** For a finite `π`, `t < η` and every `z`,
`∂_t w_{η - t}(z) = -½ ∂_z² w_{η - t}(z)`. -/
theorem hasDerivAt_bwdRef_t (π : Measure ℝ) [IsFiniteMeasure π] {η t : ℝ} (htη : t < η)
    (z : ℝ) :
    HasDerivAt (fun r => heatFlowDensity π (η - r) z) (-(heatFlowD2 π (η - t) z / 2)) t := by
  have h := (hasDerivAt_heatFlowDensity_t π (sub_pos.2 htη) z).comp t
    ((hasDerivAt_id t).const_sub η)
  convert h using 1
  · rfl
  · ring

/-- The reference family of the backward flow, `W t z = w_{η - t}(z) = heatFlowDensity π (η - t) z`.
-/
noncomputable def bwdRef (π : Measure ℝ) (η : ℝ) : ℝ → ℝ → ℝ :=
  fun t z => heatFlowDensity π (η - t) z

/-- The space derivative of `bwdRef`: `heatFlowD1 π (η - t) z`. -/
noncomputable def bwdRefD1 (π : Measure ℝ) (η : ℝ) : ℝ → ℝ → ℝ :=
  fun t z => heatFlowD1 π (η - t) z

/-- The second space derivative of `bwdRef`: `heatFlowD2 π (η - t) z`. -/
noncomputable def bwdRefD2 (π : Measure ℝ) (η : ℝ) : ℝ → ℝ → ℝ :=
  fun t z => heatFlowD2 π (η - t) z

/-- The KL curve along the backward flow, `Kb t = ∫ W_t U_t log U_t`
(`= KL(bwdKernel π η t ∘ₘ μ‖π * N(0, η - t))` under integrability,
`toReal_klDiv_bwdKernel_comp_eq`). -/
noncomputable def bwdKL (π μ : Measure ℝ) (η t : ℝ) : ℝ :=
  ∫ z, bklIntegrand (bwdRef π η) (bwdRatio π μ η) t z

/-- The relative Fisher information along the backward flow, `Ib t = ∫ W_t (U_t')² / U_t`. -/
noncomputable def bwdFisher (π μ : Measure ℝ) (η t : ℝ) : ℝ :=
  ∫ z, bFisherIntegrand (bwdRef π η) (bwdRatio π μ η) (bwdRatioD1 π μ η) t z

/-! ### The backward kernel and the factorisation of the RGO -/

section Kernel

open FormalizeSampling.Proximal FormalizeSampling.ReverseKernel
open FormalizeSampling.ProximalContraction

attribute [local instance] isFiniteKernel_forwardKernel

/-- The backward kernel from time `0` to time `t` of the backward flow:
`bwdKernel π η t y = w_{η-t}(z) φ_t(y - z) / m(y) dz` with `m` the marginal density
(`= w_η(y)`, `marginalDensity_bwd`), i.e. the Bayes reverse kernel of the Gaussian channel
`forwardKernel t` for the prior `π * N(0, η - t)` (`isReverseKernel_bwdKernel`). -/
noncomputable def bwdKernel (π : Measure ℝ) (η t : ℝ) : Kernel ℝ ℝ :=
  densityKernel volume (reverseDensity volume
    (fun z => ENNReal.ofReal (heatFlowDensity π (η - t) z)) (forwardDensity t))

/-- The heat kernel is even. -/
theorem heatDensity_neg (t v : ℝ) : heatDensity t (-v) = heatDensity t v := by
  simp [heatDensity]

/-- For `0 < s, t` with `s + t = η`: `forwardKernel t ∘ₖ forwardKernel s = forwardKernel η`. -/
theorem forwardKernel_comp_forwardKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    forwardKernel t ∘ₖ forwardKernel s = forwardKernel (s + t) := by
  rw [← heatKernel_toNNReal_eq_forwardKernel hs, ← heatKernel_toNNReal_eq_forwardKernel ht,
    ← heatKernel_toNNReal_eq_forwardKernel (add_pos hs ht), OU.heatKernel_comp_heatKernel,
    Real.toNNReal_add hs.le ht.le]

variable (π : Measure ℝ) [IsProbabilityMeasure π] {η : ℝ}

/-- The density of the backward reference marginal `π * N(0, η - t)` is measurable. -/
theorem measurable_bwdPrior {t : ℝ} (htη : t < η) :
    Measurable (fun z => ENNReal.ofReal (heatFlowDensity π (η - t) z)) :=
  (continuous_heatFlowDensity π (sub_pos.2 htη)).measurable.ennreal_ofReal

/-- **Marginal of the backward prior.** For `0 < t < η`:
`∫ w_{η-t}(z) N(y; z, t) dz = w_η(y)` (heat semigroup). -/
theorem marginalDensity_bwd {t : ℝ} (ht : 0 < t) (htη : t < η) (y : ℝ) :
    marginalDensity volume (fun z => ENNReal.ofReal (heatFlowDensity π (η - t) z))
      (forwardDensity t) y = ENNReal.ofReal (heatFlowDensity π η y) := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hint : Integrable (fun z => heatFlowDensity π (η - t) z * heatDensity t (y - z)) := by
    refine (integrable_heatFlowDensity π hs).mul_bdd (c := (Real.sqrt (2 * Real.pi * t))⁻¹)
      ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]
    exact heatDensity_le ht _
  unfold marginalDensity
  have e : ∀ z, ENNReal.ofReal (heatFlowDensity π (η - t) z) * forwardDensity t z y
      = ENNReal.ofReal (heatFlowDensity π (η - t) z * heatDensity t (y - z)) := by
    intro z
    rw [forwardDensity, gaussianPDF, gaussianPDFReal_eq_heatDensity ht,
      ← ENNReal.ofReal_mul (heatFlowDensity_pos π hs z).le]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z =>
    mul_nonneg (heatFlowDensity_pos π hs z).le (heatDensity_pos ht _).le)]
  congr 1
  have := (heatFlow_semigroup π hs ht).1 y
  rw [sub_add_cancel] at this
  exact this.symm

/-- The backward reverse density, explicitly: `w_{η-t}(z) φ_t(z - y) / w_η(y)`. -/
theorem reverseDensity_bwd {t : ℝ} (ht : 0 < t) (htη : t < η) (y z : ℝ) :
    reverseDensity volume (fun z => ENNReal.ofReal (heatFlowDensity π (η - t) z))
      (forwardDensity t) y z = ENNReal.ofReal (heatFlowDensity π (η - t) z
        * (heatDensity t (z - y) / heatFlowDensity π η y)) := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hη : 0 < η := ht.trans htη
  rw [reverseDensity, marginalDensity_bwd π ht htη, forwardDensity, gaussianPDF,
    gaussianPDFReal_eq_heatDensity ht, ← ENNReal.ofReal_mul (heatFlowDensity_pos π hs z).le,
    ← ENNReal.ofReal_div_of_pos (heatFlowDensity_pos π hη y), ← neg_sub z y, heatDensity_neg,
    mul_div_assoc]

/-- The backward kernel is a Markov kernel (`0 < t < η`). -/
theorem isMarkovKernel_bwdKernel {t : ℝ} (ht : 0 < t) (htη : t < η) :
    IsMarkovKernel (bwdKernel π η t) := by
  have hη : 0 < η := ht.trans htη
  refine isMarkovKernel_densityKernel (measurable_reverseDensity (measurable_bwdPrior π htη)
    (measurable_forwardDensity t)) fun y => ?_
  refine lintegral_reverseDensity_eq_one (measurable_bwdPrior π htη)
    (measurable_forwardDensity t) y ?_ ?_
  · rw [marginalDensity_bwd π ht htη, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact heatFlowDensity_pos π hη y
  · rw [marginalDensity_bwd π ht htη]; exact ENNReal.ofReal_ne_top

/-- `forwardKernel s ∘ₘ π = w_s dz` for `s > 0`. -/
theorem forwardKernel_comp_eq_withDensity {s : ℝ} (hs : 0 < s) :
    forwardKernel s ∘ₘ π = volume.withDensity fun z => ENNReal.ofReal (heatFlowDensity π s z) := by
  rw [← heatKernel_toNNReal_eq_forwardKernel hs, heatKernel_comp_eq_withDensity π hs]

/-- **The backward kernel is a reverse kernel** of `forwardKernel t` for the prior
`forwardKernel (η - t) ∘ₘ π = π * N(0, η - t)` (`0 < t < η`). -/
theorem isReverseKernel_bwdKernel {t : ℝ} (ht : 0 < t) (htη : t < η) :
    IsReverseKernel (forwardKernel t) (forwardKernel (η - t) ∘ₘ π) (bwdKernel π η t) := by
  have hs : 0 < η - t := sub_pos.2 htη
  rw [forwardKernel_comp_eq_withDensity π hs]
  refine isReverseKernel_densityKernel (measurable_bwdPrior π htη) (measurable_forwardDensity t)
    (lintegral_forwardDensity ht) ?_
  have := isProbabilityMeasure_withDensity_heatFlowDensity π hs
  have h := measure_univ (μ := volume.withDensity fun z =>
    ENNReal.ofReal (heatFlowDensity π (η - t) z))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [h]; exact ENNReal.one_ne_top

/-- The backward kernel maps `π^Y` to `π * N(0, η - t)`:
`bwdKernel π η t ∘ₘ (forwardKernel η ∘ₘ π) = forwardKernel (η - t) ∘ₘ π`. -/
theorem bwdKernel_comp_forward {t : ℝ} (ht : 0 < t) (htη : t < η) :
    bwdKernel π η t ∘ₘ (forwardKernel η ∘ₘ π) = forwardKernel (η - t) ∘ₘ π := by
  have hs : 0 < η - t := sub_pos.2 htη
  have := isMarkovKernel_forwardKernel ht
  have := isMarkovKernel_bwdKernel π ht htη
  have h := (isReverseKernel_bwdKernel π ht htη).comp_marginal
  have e : forwardKernel η ∘ₘ π = forwardKernel t ∘ₘ (forwardKernel (η - t) ∘ₘ π) := by
    rw [Measure.comp_assoc, forwardKernel_comp_forwardKernel hs ht, sub_add_cancel]
  rw [e]
  exact h

/-- **Factorisation of the RGO through the backward kernel.** For measurable `f` with integrable
`e^{-f}`, `π = target f`, `0 < t < η`, and every law `μ ≪ π^Y = forwardKernel η ∘ₘ π`:
`rgoKernel f η ∘ₘ μ = (forwardKernel (η - t))†π ∘ₘ (bwdKernel π η t ∘ₘ μ)`. -/
theorem rgoKernel_comp_eq_posterior_comp {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {t : ℝ} (ht : 0 < t) (htη : t < η)
    (μ : Measure ℝ) (hμ : μ ≪ forwardKernel η ∘ₘ target f) :
    haveI := isProbabilityMeasure_target hint
    rgoKernel f η ∘ₘ μ =
      (forwardKernel (η - t))†(target f) ∘ₘ (bwdKernel (target f) η t ∘ₘ μ) := by
  have := isProbabilityMeasure_target hint
  have hs : 0 < η - t := sub_pos.2 htη
  have hη : 0 < η := ht.trans htη
  have := isMarkovKernel_forwardKernel ht
  have := isMarkovKernel_forwardKernel hs
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_bwdKernel (target f) ht htη
  have hfac : forwardKernel η = forwardKernel t ∘ₖ forwardKernel (η - t) := by
    rw [forwardKernel_comp_forwardKernel hs ht, sub_add_cancel]
  have hmeas : forwardKernel t ∘ₘ (forwardKernel (η - t) ∘ₘ target f)
      = forwardKernel η ∘ₘ target f := by
    rw [Measure.comp_assoc, ← hfac]
  have h1 := rgoKernel_ae_eq_posterior hf hint hη
  have h2' : ∀ (κ : Kernel ℝ ℝ) [IsFiniteKernel κ],
      κ = forwardKernel t ∘ₖ forwardKernel (η - t) →
      κ†(target f) =ᵐ[forwardKernel t ∘ₘ (forwardKernel (η - t) ∘ₘ target f)]
        (forwardKernel (η - t))†(target f) ∘ₖ
          (forwardKernel t)†(forwardKernel (η - t) ∘ₘ target f) := by
    intro κ _ hκ
    subst hκ
    exact posterior_comp
  have h2 := h2' (forwardKernel η) hfac
  rw [hmeas] at h2
  have h3 : bwdKernel (target f) η t =ᵐ[forwardKernel η ∘ₘ target f]
      (forwardKernel t)†(forwardKernel (η - t) ∘ₘ target f) := by
    have := (isReverseKernel_bwdKernel (target f) ht htη).ae_eq_posterior
    rwa [hmeas] at this
  have h4 : ∀ᵐ y ∂(forwardKernel η ∘ₘ target f), rgoKernel f η y =
      ((forwardKernel (η - t))†(target f) ∘ₖ bwdKernel (target f) η t) y := by
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [hy1, hy2, Kernel.comp_apply, Kernel.comp_apply, hy3]
  rw [Measure.comp_assoc]
  exact Measure.comp_congr (hμ.ae_le h4)

/-- The target is recovered from `π * N(0, η - t)` by the posterior:
`(forwardKernel (η - t))†π ∘ₘ (forwardKernel (η - t) ∘ₘ π) = π`. -/
theorem posterior_comp_forward {s : ℝ} (hs : 0 < s) :
    (forwardKernel s)†π ∘ₘ (forwardKernel s ∘ₘ π) = π := by
  have := isMarkovKernel_forwardKernel hs
  exact posterior_comp_self (κ := forwardKernel s) (μ := π)

/-- **Endpoint `t = η` by data processing.** For measurable `f` with integrable `e^{-f}`,
`π = target f`, `0 < t < η` and `μ ≪ π^Y`:
`KL(rgoKernel f η ∘ₘ μ‖π) ≤ KL(bwdKernel π η t ∘ₘ μ‖π * N(0, η - t))`. -/
theorem klDiv_rgoKernel_comp_le_bwd {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {t : ℝ} (ht : 0 < t) (htη : t < η)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≪ forwardKernel η ∘ₘ target f) :
    klDiv (rgoKernel f η ∘ₘ μ) (target f)
      ≤ klDiv (bwdKernel (target f) η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ target f) := by
  have := isProbabilityMeasure_target hint
  have hs : 0 < η - t := sub_pos.2 htη
  have := isMarkovKernel_bwdKernel (target f) ht htη
  rw [rgoKernel_comp_eq_posterior_comp hf hint ht htη μ hμ]
  have e := posterior_comp_forward (target f) hs
  calc _ = klDiv ((forwardKernel (η - t))†(target f) ∘ₘ (bwdKernel (target f) η t ∘ₘ μ))
        ((forwardKernel (η - t))†(target f) ∘ₘ (forwardKernel (η - t) ∘ₘ target f)) := by
          rw [e]
    _ ≤ _ := klDiv_comp_right_le _ _ _

/-- **Endpoint `t = 0` by data processing.** For `0 < t < η` and any law `μ`:
`KL(bwdKernel π η t ∘ₘ μ‖π * N(0, η - t)) ≤ KL(μ‖π^Y)`. -/
theorem klDiv_bwd_le {t : ℝ} (ht : 0 < t) (htη : t < η) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    klDiv (bwdKernel π η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ π)
      ≤ klDiv μ (forwardKernel η ∘ₘ π) := by
  have := isMarkovKernel_bwdKernel π ht htη
  rw [← bwdKernel_comp_forward π ht htη]
  exact klDiv_comp_right_le _ _ _

/-- **Density of the backward marginal.** For `0 < t < η` and a finite law `μ`:
`bwdKernel π η t ∘ₘ μ = (W_t U_t) dz` with `W_t = w_{η-t}` and `U_t = bwdRatio π μ η t`. -/
theorem bwdKernel_comp_eq_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (htη : t < η) :
    bwdKernel π η t ∘ₘ μ = volume.withDensity fun z =>
      ENNReal.ofReal (heatFlowDensity π (η - t) z * bwdRatio π μ η t z) := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_bound π ht le_rfl htη
  have hjm : Measurable (Function.uncurry fun y z => ENNReal.ofReal (heatFlowDensity π (η - t) z
      * (heatDensity t (z - y) / heatFlowDensity π η y))) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine ((continuous_heatFlowDensity π hs).comp continuous_snd).mul
      (((continuous_heatDensity t).comp (by fun_prop)).div
        ((continuous_heatFlowDensity π hη).comp continuous_fst) fun p =>
          (heatFlowDensity_pos π hη _).ne')
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), withDensity_apply _ hA]
  have e1 : ∀ y, bwdKernel π η t y A = ∫⁻ z in A, ENNReal.ofReal (heatFlowDensity π (η - t) z
      * (heatDensity t (z - y) / heatFlowDensity π η y)) := by
    intro y
    rw [bwdKernel, densityKernel_apply (measurable_reverseDensity (measurable_bwdPrior π htη)
      (measurable_forwardDensity t)), withDensity_apply _ hA]
    exact setLIntegral_congr_fun hA fun z _ => reverseDensity_bwd π ht htη y z
  simp_rw [e1]
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  refine setLIntegral_congr_fun hA fun z _ => ?_
  have hi : Integrable (fun y => heatDensity t (z - y) / heatFlowDensity π η y) μ :=
    Integrable.of_bound (aestronglyMeasurable_div_heatFlowDensity π μ hη
      (continuous_heatDensity t) z) _ (Eventually.of_forall fun y =>
        (hb t ⟨le_rfl, le_rfl⟩ z y).1)
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (Eventually.of_forall fun y =>
    mul_nonneg (heatFlowDensity_pos π hs z).le
      (div_nonneg (heatDensity_pos ht _).le (heatFlowDensity_pos π hη y).le)),
    integral_const_mul]
  rfl

end Kernel

/-! ### Regularity hypotheses, de Bruijn and LSI along the backward flow -/

/-- **Regularity hypotheses for the backward de Bruijn identity** on the open time interval
`(0, η)`, for `W t = w_{η-t}` (`bwdRef`) and `U t = bwdRatio π μ η t` with their explicit
derivatives. As for `HeatFlowDeBruijn.HeatFlowRegular`, these are integrability, local
domination and boundary conditions; none of them is the identity or the inequality proved from
them. Nothing is required at `t = 0` or `t = η`. -/
structure BackwardHeatFlowRegular (π μ : Measure ℝ) (η : ℝ) : Prop where
  /-- `W U log U` (`= p log(p/W)`, `p = W U`) is Lebesgue integrable. -/
  integrable_kl : ∀ t ∈ Ioo 0 η, Integrable (bklIntegrand (bwdRef π η) (bwdRatio π μ η) t)
  /-- The time derivative `bklRate` of the integrand is dominated, locally uniformly in time,
  by an integrable function. -/
  dominated : ∀ t ∈ Ioo 0 η, ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ᶠ r in 𝓝 t, ∀ z,
    |bklRate (bwdRef π η) (bwdRatio π μ η) (bwdRefD2 π η) (bwdRatioD2 π μ η) r z| ≤ bound z
  /-- The relative Fisher integrand `W (U')² / U` is integrable. -/
  integrable_fisher : ∀ t ∈ Ioo 0 η,
    Integrable (bFisherIntegrand (bwdRef π η) (bwdRatio π μ η) (bwdRatioD1 π μ η) t)
  /-- The boundary flux vanishes at `-∞`. -/
  tendsto_atBot : ∀ t ∈ Ioo 0 η, Tendsto
    (bklFlux (bwdRef π η) (bwdRatio π μ η) (bwdRefD1 π η) (bwdRatioD1 π μ η) t) atBot (𝓝 0)
  /-- The boundary flux vanishes at `+∞`. -/
  tendsto_atTop : ∀ t ∈ Ioo 0 η, Tendsto
    (bklFlux (bwdRef π η) (bwdRatio π μ η) (bwdRefD1 π η) (bwdRatioD1 π μ η) t) atTop (𝓝 0)

section Main

open FormalizeSampling.Proximal FormalizeSampling.ProximalContraction FormalizeSampling.LogSobolev

variable (π μ : Measure ℝ) [IsProbabilityMeasure π] [IsProbabilityMeasure μ] {η : ℝ}

/-- **Backward de Bruijn identity (Verified under `BackwardHeatFlowRegular`).** For
probability laws `π, μ` and `t₀ ∈ (0, η)`:
`d/dt ∫ W_t U_t log U_t = -½ ∫ W_t (U_t')² / U_t` at `t₀`. -/
theorem hasDerivAt_bwdKL (hreg : BackwardHeatFlowRegular π μ η) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 η) :
    HasDerivAt (bwdKL π μ η) (-(1 / 2) * bwdFisher π μ η t₀) t₀ := by
  obtain ⟨bound, hb_int, hev⟩ := hreg.dominated t₀ ht₀
  obtain ⟨v, hv, hvb⟩ := hev.exists_mem
  have hs : Ioo 0 η ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀
  exact hasDerivAt_integral_bklIntegrand (s := v ∩ Ioo 0 η) (inter_mem hv hs)
    (fun t ht z => bwdRatio_pos π μ ht.2.1 ht.2.2 z)
    (fun t ht z => hasDerivAt_bwdRef_t π ht.2.2 z)
    (fun t ht z => hasDerivAt_bwdRatio_t π μ ht.2.1 ht.2.2 z)
    (fun t ht z => hasDerivAt_heatFlowDensity_x π (sub_pos.2 ht.2.2) z)
    (fun t ht z => hasDerivAt_bwdRatio_x π μ ht.2.1 ht.2.2 z)
    (fun z => hasDerivAt_heatFlowD1_x π (sub_pos.2 ht₀.2) z)
    (fun z => hasDerivAt_bwdRatioD1_x π μ ht₀.1 ht₀.2 z)
    (hreg.integrable_kl t₀ ht₀) hb_int (fun t ht => hvb t ht.1)
    (hreg.integrable_fisher t₀ ht₀) (hreg.tendsto_atBot t₀ ht₀) (hreg.tendsto_atTop t₀ ht₀)

/-- The backward marginal `W_t U_t` is a probability density (`0 < t < η`). -/
theorem isProbabilityMeasure_withDensity_bwd {t : ℝ} (ht : 0 < t) (htη : t < η) :
    IsProbabilityMeasure (volume.withDensity fun z =>
      ENNReal.ofReal (heatFlowDensity π (η - t) z * bwdRatio π μ η t z)) := by
  have := isMarkovKernel_bwdKernel π ht htη
  rw [← bwdKernel_comp_eq_withDensity π μ ht htη]
  infer_instance

/-- A continuous `p ≥ 0` whose density measure is a probability is integrable with `∫ p = 1`. -/
theorem integrable_and_integral_eq_one {p : ℝ → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))] :
    Integrable p ∧ ∫ x, p x = 1 := by
  have h1 := measure_univ (μ := volume.withDensity fun x => ENNReal.ofReal (p x))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [HasFiniteIntegral]
    simp_rw [Real.enorm_eq_ofReal (h0 _), h1]
    exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hm.aestronglyMeasurable, h1]
    simp

/-- **KL along the backward flow.** For `0 < t < η` and integrable `W_t U_t log U_t`:
`KL(bwdKernel π η t ∘ₘ μ‖π * N(0, η - t)) < ∞` and its real value is `bwdKL π μ η t`. -/
theorem toReal_klDiv_bwdKernel_comp_eq {t : ℝ} (ht : 0 < t) (htη : t < η)
    (hint : Integrable (bklIntegrand (bwdRef π η) (bwdRatio π μ η) t)) :
    klDiv (bwdKernel π η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ π) ≠ ⊤ ∧
      (klDiv (bwdKernel π η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ π)).toReal = bwdKL π μ η t := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hq := heatFlowDensity_pos π hs
  have hU := bwdRatio_pos π μ ht htη
  have := isProbabilityMeasure_withDensity_bwd π μ ht htη
  have := isProbabilityMeasure_withDensity_heatFlowDensity π hs
  have hqc := continuous_heatFlowDensity π hs
  have hpm : Measurable fun z => heatFlowDensity π (η - t) z * bwdRatio π μ η t z :=
    (hqc.mul (continuous_bwdRatio π μ ht htη)).measurable
  have e : ∀ z, heatFlowDensity π (η - t) z * bwdRatio π μ η t z
      * Real.log (heatFlowDensity π (η - t) z * bwdRatio π μ η t z / heatFlowDensity π (η - t) z)
      = bklIntegrand (bwdRef π η) (bwdRatio π μ η) t z := by
    intro z
    rw [mul_div_cancel_left₀ _ (hq z).ne', bklIntegrand, bwdRef, mul_assoc]
  have hint' : Integrable fun z => heatFlowDensity π (η - t) z * bwdRatio π μ η t z
      * Real.log (heatFlowDensity π (η - t) z * bwdRatio π μ η t z
        / heatFlowDensity π (η - t) z) := by
    simp_rw [e]; exact hint
  have h := FormalizeSampling.DeterministicStep.klDiv_withDensity_real hpm hqc.measurable
    (fun z => (mul_pos (hq z) (hU z)).le) hq hint'
  rw [bwdKernel_comp_eq_withDensity π μ ht htη, forwardKernel_comp_eq_withDensity π hs]
  refine ⟨h.1, h.2.trans ?_⟩
  exact integral_congr_ae (Eventually.of_forall e)

/-- **LSI along the backward flow.** If `FunctionalLSI π (1/α)` (`α > 0`) and the regularity
fields hold at `t ∈ (0, η)`, then `2 α Kb(t) ≤ (1 + α (η - t)) Ib(t)` with
`Kb = bwdKL`, `Ib = bwdFisher` (LSI of `π * N(0, η - t)` with constant `1/α + η - t`, applied
to `√U_t`). -/
theorem bwdKL_le_of_targetLSI {α : ℝ} (hα : 0 < α) (hπ : FunctionalLSI π (1 / α)) {t : ℝ}
    (ht : 0 < t) (htη : t < η)
    (hkl : Integrable (bklIntegrand (bwdRef π η) (bwdRatio π μ η) t))
    (hfi : Integrable (bFisherIntegrand (bwdRef π η) (bwdRatio π μ η) (bwdRatioD1 π μ η) t)) :
    2 * α * bwdKL π μ η t ≤ (1 + α * (η - t)) * bwdFisher π μ η t := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hq := heatFlowDensity_pos π hs
  have hqc := continuous_heatFlowDensity π hs
  have := isProbabilityMeasure_withDensity_heatFlowDensity π hs
  have := isProbabilityMeasure_withDensity_bwd π μ ht htη
  have hL := GaussianFunctionalLSI.functionalLSI_heatKernel_comp_of_targetLSI π hs.le hπ
  rw [heatKernel_comp_eq_withDensity π hs] at hL
  have hC : 0 ≤ 1 / α + (η - t) := by positivity
  obtain ⟨hmass, hone⟩ := integrable_and_integral_eq_one
    (hqc.mul (continuous_bwdRatio π μ ht htη)).measurable
    (fun z => (mul_pos (hq z) (bwdRatio_pos π μ ht htη z)).le)
  have h := integral_mul_log_le_of_functionalLSI hqc.measurable (fun z => (hq z).le) hC hL
    (bwdRatio_pos π μ ht htη) (hasDerivAt_bwdRatio_x π μ ht htη)
    (continuous_bwdRatioD1 π μ ht htη) hmass hone hkl hfi
  have e1 : bwdKL π μ η t = ∫ z, heatFlowDensity π (η - t) z
      * (bwdRatio π μ η t z * Real.log (bwdRatio π μ η t z)) := rfl
  have e2 : bwdFisher π μ η t = ∫ z, heatFlowDensity π (η - t) z
      * bwdRatioD1 π μ η t z ^ 2 / bwdRatio π μ η t z := rfl
  rw [e1, e2]
  have h2 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * α)
  have e3 : 2 * α * ((1 / α + (η - t)) / 2 * ∫ z, heatFlowDensity π (η - t) z
      * bwdRatioD1 π μ η t z ^ 2 / bwdRatio π μ η t z) = (1 + α * (η - t)) * ∫ z,
      heatFlowDensity π (η - t) z * bwdRatioD1 π μ η t z ^ 2 / bwdRatio π μ η t z := by
    field_simp
  linarith

end Main

/-! ### The backward step and the sharp PX-2 rate -/

section Rate

open FormalizeSampling.Proximal FormalizeSampling.ProximalContraction FormalizeSampling.LogSobolev

variable {f : ℝ → ℝ} {η : ℝ}

/-- **Finite KL forces `∫ e^{-f} < ∞`.** For every kernel `κ` and probability law `μ`, if
`KL(μ‖κ ∘ₘ target f) < ∞` then `e^{-f}` is Lebesgue integrable: otherwise
`targetNormalizer f = 0`, so `target f = 0`, `κ ∘ₘ target f = 0` and `KL(μ‖0) = ∞`. -/
theorem integrable_exp_neg_of_klDiv_comp_target_ne_top (κ : Kernel ℝ ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hKL : klDiv μ (κ ∘ₘ target f) ≠ ⊤) :
    Integrable (fun x => Real.exp (-f x)) := by
  by_contra h
  have h0 : target f = 0 := by
    simp [target, targetDensity, targetNormalizer, integral_undef h]
  rw [h0, Measure.bind_zero_left, klDiv_zero_right] at hKL
  exact hKL rfl

/-- **Finite KL forces `∫ e^{-f} < ∞`.** If a probability law `μ` has `KL(μ‖target f) < ∞`,
then `e^{-f}` is Lebesgue integrable (`κ = id` in
`integrable_exp_neg_of_klDiv_comp_target_ne_top`). -/
theorem integrable_exp_neg_of_klDiv_target_ne_top (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hKL : klDiv μ (target f) ≠ ⊤) : Integrable (fun x => Real.exp (-f x)) :=
  integrable_exp_neg_of_klDiv_comp_target_ne_top Kernel.id μ (by rwa [Measure.id_comp])

/-- **Backward strong data processing from a functional LSI (Conditional on
`BackwardHeatFlowRegular`).** Let `f` be measurable, `π = target f`, `η > 0`, `α > 0` with
`FunctionalLSI π (1/α)`, and `μ` a probability law with `KL(μ‖π^Y) < ∞`,
`π^Y = forwardKernel η ∘ₘ π`, and `BackwardHeatFlowRegular π μ η` (integrability of `e^{-f}`
is not assumed: it follows from `KL(μ‖π^Y) < ∞`). Then `KL(rgoKernel f η ∘ₘ μ‖π) < ∞` and
`KL(rgoKernel f η ∘ₘ μ‖π).toReal ≤ KL(μ‖π^Y).toReal / (1 + α η)`. -/
theorem toReal_klDiv_rgoKernel_comp_le_of_targetLSI (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hKL : klDiv μ (forwardKernel η ∘ₘ target f) ≠ ⊤)
    (hreg : BackwardHeatFlowRegular (target f) μ η) (hπ : FunctionalLSI (target f) (1 / α)) :
    klDiv (rgoKernel f η ∘ₘ μ) (target f) ≠ ⊤ ∧
      (klDiv (rgoKernel f η ∘ₘ μ) (target f)).toReal
        ≤ (klDiv μ (forwardKernel η ∘ₘ target f)).toReal / (1 + α * η) := by
  have hint := integrable_exp_neg_of_klDiv_comp_target_ne_top (forwardKernel η) μ hKL
  have := isProbabilityMeasure_target hint
  have hμ : μ ≪ forwardKernel η ∘ₘ target f := (klDiv_ne_top_iff.1 hKL).1
  have hend : ∀ t ∈ Ioo 0 η, klDiv (rgoKernel f η ∘ₘ μ) (target f)
      ≤ klDiv (bwdKernel (target f) η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ target f) :=
    fun t ht => klDiv_rgoKernel_comp_le_bwd hf hint ht.1 ht.2 μ hμ
  have hstart : ∀ t ∈ Ioo 0 η,
      klDiv (bwdKernel (target f) η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ target f)
        ≤ klDiv μ (forwardKernel η ∘ₘ target f) :=
    fun t ht => klDiv_bwd_le (target f) ht.1 ht.2 μ
  have hmid : η / 2 ∈ Ioo 0 η := ⟨by linarith, by linarith⟩
  have hfin : klDiv (rgoKernel f η ∘ₘ μ) (target f) ≠ ⊤ :=
    ne_top_of_le_ne_top hKL ((hend _ hmid).trans (hstart _ hmid))
  refine ⟨hfin, ?_⟩
  have hKb : ∀ t ∈ Ioo 0 η,
      (klDiv (bwdKernel (target f) η t ∘ₘ μ) (forwardKernel (η - t) ∘ₘ target f)).toReal
        = bwdKL (target f) μ η t := fun t ht =>
    (toReal_klDiv_bwdKernel_comp_eq (target f) μ ht.1 ht.2 (hreg.integrable_kl t ht)).2
  refine le_div_of_hasDerivAt_interior hα.le hη (I := bwdFisher (target f) μ η)
    (fun t ht => hasDerivAt_bwdKL (target f) μ hreg ht)
    (fun t ht => bwdKL_le_of_targetLSI (target f) μ hα hπ ht.1 ht.2 (hreg.integrable_kl t ht)
      (hreg.integrable_fisher t ht)) (fun t ht => ?_) (fun t ht => ?_)
  · rw [← hKb t ht]
    exact ENNReal.toReal_mono hKL (hstart t ht)
  · rw [← hKb t ht]
    exact ENNReal.toReal_mono (toReal_klDiv_bwdKernel_comp_eq (target f) μ ht.1 ht.2
      (hreg.integrable_kl t ht)).1 (hend t ht)

/-- **Sharp PX-2, one step, from a functional LSI (Conditional on the regularity hypotheses).**
Let `f` be measurable, `π = target f`, `η, α > 0` with `FunctionalLSI π (1/α)`, and `ρ` a
probability law with `KL(ρ‖π) < ∞` (this forces `∫ e^{-f} < ∞`). Assume the forward
regularity `HeatFlowRegular ρ π s` with `(0, η] ⊆ s` and the backward regularity
`BackwardHeatFlowRegular π (forwardKernel η ∘ₘ ρ) η`. Then `KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target f) ≠ ⊤) {s : Set ℝ}
    (hreg : HeatFlowRegular ρ (target f) s) (hs : Ioc 0 η ⊆ s)
    (hbreg : BackwardHeatFlowRegular (target f) (forwardKernel η ∘ₘ ρ) η)
    (hπ : FunctionalLSI (target f) (1 / α)) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) ^ 2 := by
  have := isProbabilityMeasure_target (integrable_exp_neg_of_klDiv_target_ne_top ρ hKL)
  have := isMarkovKernel_forwardKernel hη
  have hpos : 0 < 1 + α * η := by positivity
  have hfwd : klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target f) ≠ ⊤ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  have hF := toReal_klDiv_forwardKernel_le_of_regular hα.le hη hKL hreg hs
    (LogSobolevExtension.heatFlowLSI_of_targetLSI ρ (target f) hα hπ hreg
      (Ioo_subset_Ioc_self.trans hs))
  obtain ⟨hfin, hB⟩ := toReal_klDiv_rgoKernel_comp_le_of_targetLSI hf hη hα
    (forwardKernel η ∘ₘ ρ) hfwd hbreg hπ
  rw [ProximalSharp.proxKernel_comp_eq]
  refine ⟨hfin, hB.trans ?_⟩
  calc (klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target f)).toReal / (1 + α * η)
      ≤ (klDiv ρ (target f)).toReal / (1 + α * η) / (1 + α * η) :=
        div_le_div_of_nonneg_right hF hpos.le
    _ = _ := by rw [div_div, sq]

/-- **Sharp PX-2, iterated (Conditional on the regularity hypotheses).** Let `f` be measurable,
`π = target f`, `η, α > 0` with `FunctionalLSI π (1/α)`, and `ρ : ℕ → Measure ℝ` the
proximal-sampler laws: `ρ 0` a probability law with `KL(ρ 0‖π) < ∞` (so `∫ e^{-f} < ∞`),
`ρ (k+1) = proxKernel f η ∘ₘ ρ k`. Assume at every step `HeatFlowRegular (ρ k) π (s k)` with
`(0, η] ⊆ s k` and `BackwardHeatFlowRegular π (forwardKernel η ∘ₘ ρ k) η`. Then for every `k`,
`ρ k` is a probability law, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iterate_le_sq_of_targetLSI (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ⊤)
    {s : ℕ → Set ℝ} (hreg : ∀ k, HeatFlowRegular (ρ k) (target f) (s k))
    (hs : ∀ k, Ioc 0 η ⊆ s k)
    (hbreg : ∀ k, BackwardHeatFlowRegular (target f) (forwardKernel η ∘ₘ ρ k) η)
    (hπ : FunctionalLSI (target f) (1 / α)) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (target f) ≠ ⊤ ∧
      (klDiv (ρ k) (target f)).toReal
        ≤ (klDiv (ρ 0) (target f)).toReal / (1 + α * η) ^ (2 * k) := by
  have hint := integrable_exp_neg_of_klDiv_target_ne_top (ρ 0) hKL
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_rgoKernel hf hint hη
  have hpos : 0 < 1 + α * η := by positivity
  induction k with
  | zero => exact ⟨inferInstance, hKL, by simp⟩
  | succ k ih =>
    obtain ⟨hprob, hfin, hle⟩ := ih
    have := hprob
    obtain ⟨hfin', hle'⟩ := toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI hf hη hα
      (ρ k) hfin (hreg k) (hs k) (hbreg k) hπ
    rw [hstep k]
    refine ⟨by unfold proxKernel; infer_instance, hfin', hle'.trans ?_⟩
    rw [mul_add, mul_one, pow_add, ← div_div]
    exact div_le_div_of_nonneg_right hle (by positivity)

/-! ### The named hypotheses of `ProximalSharp` -/

/-- **The named backward hypotheses follow from the backward SDPI.** For `α ≥ 0`, `η ≥ 0`, a
potential `f`, a law `μ`, if
`KL(rgoKernel f η ∘ₘ μ‖π).toReal ≤ KL(μ‖π^Y).toReal / (1 + α η)`, then the affine curve
`Kb t = c (1 + α (η - t))`, `c = KL(μ‖π^Y).toReal / (1 + α η)`, with `Ib ≡ 2 α c` satisfies
`ProximalSharp.BackwardHeatFlowDissipation f η μ Kb Ib` and
`ProximalSharp.BackwardHeatFlowLSI α η Kb Ib`. (This curve is a majorant, not the KL along the
backward flow; the converse direction is `ProximalSharp.toReal_klDiv_rgoKernel_comp_le`.) -/
theorem exists_backwardHeatFlow_of_le {α : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η) {μ : Measure ℝ}
    (h : (klDiv (rgoKernel f η ∘ₘ μ) (target f)).toReal
      ≤ (klDiv μ (forwardKernel η ∘ₘ target f)).toReal / (1 + α * η)) :
    ∃ Kb Ib : ℝ → ℝ, ProximalSharp.BackwardHeatFlowDissipation f η μ Kb Ib ∧
      ProximalSharp.BackwardHeatFlowLSI α η Kb Ib := by
  have hpos : 0 < 1 + α * η := by positivity
  set c := (klDiv μ (forwardKernel η ∘ₘ target f)).toReal / (1 + α * η) with hc
  refine ⟨fun t => c * (1 + α * (η - t)), fun _ => 2 * α * c, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [sub_zero]
    rw [hc, div_mul_cancel₀ _ hpos.ne']
  · simpa using h
  · fun_prop
  · intro t _
    refine ⟨c * (-α), ?_, by linarith⟩
    have h1 : HasDerivAt (fun t : ℝ => 1 + α * (η - t)) (-α) t := by
      simpa using (((hasDerivAt_id t).const_sub η).const_mul α).const_add 1
    exact (h1.const_mul c).hasDerivWithinAt
  · intro t _
    linarith [show 2 * α * (c * (1 + α * (η - t))) = (1 + α * (η - t)) * (2 * α * c) by ring]

/-- **The named backward hypotheses are discharged** (Conditional only on the target LSI and
`BackwardHeatFlowRegular`): under the hypotheses of
`toReal_klDiv_rgoKernel_comp_le_of_targetLSI` there are `Kb, Ib` with
`ProximalSharp.BackwardHeatFlowDissipation f η μ Kb Ib` and
`ProximalSharp.BackwardHeatFlowLSI α η Kb Ib`. -/
theorem exists_backwardHeatFlow_of_targetLSI (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hKL : klDiv μ (forwardKernel η ∘ₘ target f) ≠ ⊤)
    (hreg : BackwardHeatFlowRegular (target f) μ η) (hπ : FunctionalLSI (target f) (1 / α)) :
    ∃ Kb Ib : ℝ → ℝ, ProximalSharp.BackwardHeatFlowDissipation f η μ Kb Ib ∧
      ProximalSharp.BackwardHeatFlowLSI α η Kb Ib :=
  exists_backwardHeatFlow_of_le hα.le hη.le
    (toReal_klDiv_rgoKernel_comp_le_of_targetLSI hf hη hα μ hKL hreg hπ).2

end Rate

end FormalizeSampling.ProximalSharpLSI
