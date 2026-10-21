module

public import FormalizeSampling.Samplers.BackwardHeatFlowPi
public import FormalizeSampling.Samplers.ProximalSharpLSI
public import FormalizeSampling.Samplers.ProximalLSIPi
public import FormalizeSampling.Foundations.HeatFlowRegularityPerturbedPi

/-!
# PX-2 on `Fin d → ℝ`, sharp form, from a functional LSI of the target: the backward step

Status: **Verified** for the construction of the backward heat flow of the RGO step on
`Fin d → ℝ`, its identification with the RGO through posterior kernels, and the backward strong
data-processing inequality under the explicit regularity hypotheses `BackwardHeatFlowRegularPi`
(integrability / local domination of the backward de Bruijn integrands on the open time interval
`(0, η)`). The resulting sharp PX-2 rate is **Conditional** only on
`FunctionalLSIPi (targetPi f) (1/α)` and these regularity hypotheses (plus `HeatFlowRegularPi`
for the forward step). This is the `Fin d → ℝ` version of `Samplers/ProximalSharpLSI.lean`.

Setting (as in `Samplers/ProximalPi.lean`): `π = targetPi f`, step `η > 0` (per-coordinate
variance), `π^Y = forwardKernelPi η ∘ₘ π`, `φ_t = heatDensityPi t`,
`w_s = heatFlowDensityPi π s` (the density of `π * N(0, s I)`, `s > 0`), and an input law `μ` of
the RGO step (in the sampler, `μ = forwardKernelPi η ∘ₘ ρ`). For `t ∈ (0, η)` put
* `U t z = bwdRatioPi π μ η t z = ∫ φ_t(z - y) / w_η(y) dμ(y)` (the heat semigroup
  `N(0, t I) * r` applied to `r = dμ/dπ^Y`), with gradient `bwdRatioGradPi` and Hessian
  `bwdRatioHessPi`;
* `W t z = w_{η - t}(z)` (`bwdRefPi`), with gradient `bwdRefGradPi` and Hessian `bwdRefHessPi`;
* the backward kernel `bwdKernelPi π η t y = w_{η-t}(z) φ_t(z - y) / w_η(y) dz`, the Bayes
  posterior of the Gaussian channel `forwardKernelPi t` for the prior `π * N(0, (η - t) I)`.

Then `bwdKernelPi π η t ∘ₘ μ` has density `W t · U t` (`bwdKernelPi_comp_eq_withDensity`),
`bwdKernelPi π η t ∘ₘ π^Y = π * N(0, (η - t) I)`, and the RGO factors through it
(`posterior_comp` in Mathlib):
`rgoKernelPi f η ∘ₘ μ = (forwardKernelPi (η - t))†π ∘ₘ (bwdKernelPi π η t ∘ₘ μ)`. Data processing
gives, for every `t ∈ (0, η)`, `KL(rgoKernelPi f η ∘ₘ μ‖π) ≤ Kb t ≤ KL(μ‖π^Y)` with
`Kb t = KL(W_t U_t‖W_t) = ∫ W U log U` (`klDiv_rgoKernelPi_comp_le_bwd`, `klDiv_bwdPi_le`,
`toReal_klDiv_bwdKernelPi_comp_eq`). Inside `(0, η)`, `U` solves the heat equation and `W` the
backward heat equation with no hypothesis (the Gaussian factors dominate the at most Gaussian
growth of `1 / w_η`, `exists_bwd_boundPi`), so the abstract backward de Bruijn identity of
`BackwardHeatFlowPi` gives `Kb' = -½ Ib`, `Ib = ∫ W |∇U|² / U`, and the functional LSI of
`π * N(0, (η - t) I)` (constant `1/α + η - t`, `ProximalLSIPi`) gives
`2 α Kb ≤ (1 + α (η - t)) Ib`. The interior Grönwall comparison
`BackwardHeatFlow.le_div_of_hasDerivAt_interior` closes the step.

## Main results

* `toReal_klDiv_rgoKernelPi_comp_le_of_targetLSIPi` (**backward SDPI**, RGO step contracts by
  `1/(1 + α η)`): for a probability law `μ` with `KL(μ‖π^Y) < ∞`,
  `BackwardHeatFlowRegularPi π μ η` and `FunctionalLSIPi π (1/α)`:
  `KL(rgoKernelPi f η ∘ₘ μ‖π) ≤ KL(μ‖π^Y) / (1 + α η)`.
* `toReal_klDiv_proxKernelPi_comp_le_sq_of_targetLSIPi` (**sharp PX-2, one step**):
  `KL(proxKernelPi f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)²` under `FunctionalLSIPi π (1/α)`,
  `HeatFlowRegularPi ρ π s` (`(0, η] ⊆ s`) and
  `BackwardHeatFlowRegularPi π (forwardKernelPi η ∘ₘ ρ) η`.
* `toReal_klDiv_iteratePi_le_sq_of_targetLSIPi`, `tvSupPi_iterate_le_sq_of_targetLSIPi`:
  `k` steps, factor `(1 + α η)^{-2k}`, and the TV bound by Pinsker.
* `integrable_exp_neg_of_klDiv_targetPi_ne_top`,
  `integrable_exp_neg_of_klDiv_comp_targetPi_ne_top`: finite KL against `π` (or `κ ∘ₘ π`)
  already forces `∫ e^{-f} < ∞`, so the theorems above do not assume it.

## Not proved here

* The fields of `BackwardHeatFlowRegularPi` are assumed here; they are proved for warm input
  laws and targets with a Gaussian upper envelope in
  `Samplers/BackwardHeatFlowRegularityWarmPi.lean` (`backwardHeatFlowRegularPi_of_warm`). For
  non-warm laws they are not proved, but the warm-start rate is extended to every finite-KL start
  by `KLWarmApprox` (`Samplers/ProximalGeneralLSIPi.lean`).
* That the `d = 1` case agrees with the one-dimensional `Samplers/ProximalSharpLSI.lean` (the
  two developments are separate).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
open FormalizeSampling.BackwardHeatFlowPi FormalizeSampling.GaussianLSIPi
open FormalizeSampling.HeatFlowRegularityPi (abs_le_one_add_sum_sq sum_sq_nonneg sq_le_sum_sq)
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalSharpLSIPi

variable {d : ℕ}

/-! ### Gaussian bounds -/

/-- `u e^{-κ u} ≤ 1/κ` for `κ > 0` (every real `u`). -/
theorem mul_exp_neg_le_inv {κ : ℝ} (hκ : 0 < κ) (u : ℝ) :
    u * Real.exp (-(κ * u)) ≤ 1 / κ := by
  have h1 := Real.add_one_le_exp (κ * u)
  have h2 : Real.exp (-(κ * u)) * Real.exp (κ * u) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-(κ * u))
  rw [le_div_iff₀ hκ]
  nlinarith

/-- For `0 < a ≤ t ≤ b`: `φ_t(v) ≤ (2π a)^{-d/2} e^{-|v|²/(2b)}`, `φ_t = heatDensityPi t`. -/
theorem heatDensityPi_le_exp {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (v : Fin d → ℝ) :
    heatDensityPi t v
      ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ ^ d * Real.exp (-(∑ i, v i ^ 2) / (2 * b)) := by
  have ht : 0 < t := ha.trans_le hat
  have h : -(∑ i, v i ^ 2) / (2 * t) ≤ -(∑ i, v i ^ 2) / (2 * b) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sum_sq_nonneg v) (by positivity) (by linarith)
  rw [heatDensityPi_eq_exp]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) (inv_anti₀ (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))) d) (Real.exp_le_exp.2 h)
    (Real.exp_pos _).le (by positivity)

/-- For `0 < a ≤ t`: `|∂ᵢ φ_t(v)| ≤ (1 + 1/a)² (1 + |v|²) φ_t(v)`. -/
theorem abs_heatGradPi_le_mul {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (v : Fin d → ℝ)
    (i : Fin d) :
    |heatGradPi t v i| ≤ (1 + 1 / a) ^ 2 * ((1 + ∑ j, v j ^ 2) * heatDensityPi t v) := by
  have ht : 0 < t := ha.trans_le hat
  have hφ := heatDensityPi_pos ht v
  unfold heatGradPi
  rw [abs_mul, abs_neg, abs_div, abs_of_pos ht, abs_of_pos hφ]
  have h1 := abs_le_one_add_sum_sq v i
  have h2 : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha hat
  have h3 : 1 / a ≤ (1 + 1 / a) ^ 2 := by
    have : 0 < 1 / a := by positivity
    nlinarith
  have hS := sum_sq_nonneg v
  calc |v i| / t * heatDensityPi t v = |v i| * (1 / t) * heatDensityPi t v := by ring
    _ ≤ (1 + ∑ j, v j ^ 2) * (1 / a) * heatDensityPi t v := by gcongr
    _ ≤ (1 + ∑ j, v j ^ 2) * (1 + 1 / a) ^ 2 * heatDensityPi t v := by gcongr
    _ = _ := by ring

/-- For `0 < a ≤ t`: `|∂ᵢ∂ⱼ φ_t(v)| ≤ (1 + 1/a)² (1 + |v|²) φ_t(v)`. -/
theorem abs_heatHessPi_le_mul {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (v : Fin d → ℝ)
    (i j : Fin d) :
    |heatHessPi t v i j| ≤ (1 + 1 / a) ^ 2 * ((1 + ∑ k, v k ^ 2) * heatDensityPi t v) := by
  have ht : 0 < t := ha.trans_le hat
  have hφ := heatDensityPi_pos ht v
  set S := ∑ k, v k ^ 2 with hSdef
  have hS : 0 ≤ S := sum_sq_nonneg v
  have hzi := sq_le_sum_sq v i
  have hzj := sq_le_sum_sq v j
  have hzz : |v i * v j| ≤ S := by
    rw [abs_mul]
    nlinarith [sq_abs (v i), sq_abs (v j), sq_nonneg (|v i| - |v j|)]
  have h2 : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha hat
  have h2' : 1 / t ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ ha.le hat 2)
  have hq : |v i * v j / t ^ 2 - (if i = j then 1 / t else 0)| ≤ S * (1 / t ^ 2) + 1 / t := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_eq_mul_one_div]
      gcongr
    · split_ifs <;> simp [abs_of_pos ht, ht.le]
  have h3 : S * (1 / t ^ 2) + 1 / t ≤ (1 + 1 / a) ^ 2 * (1 + S) := by
    have e : (1 + 1 / a) ^ 2 * (1 + S) = (1 + 2 * (1 / a) + (1 / a) ^ 2) * (1 + S) := by ring
    have ha' : 0 < 1 / a := by positivity
    have : 1 / a ^ 2 = (1 / a) ^ 2 := by rw [one_div_pow]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h2' hS]
  unfold heatHessPi
  rw [abs_mul, abs_of_pos hφ]
  calc |v i * v j / t ^ 2 - (if i = j then 1 / t else 0)| * heatDensityPi t v
      ≤ (1 + 1 / a) ^ 2 * (1 + S) * heatDensityPi t v := by gcongr; exact hq.trans h3
    _ = _ := by ring

/-- `|y - x|² ≤ (1 + ε) |y|² + (1 + 1/ε) |x|²` for `ε > 0`. -/
theorem sum_sq_sub_le_mul {ε : ℝ} (hε : 0 < ε) (y x : Fin d → ℝ) :
    ∑ i, (y - x) i ^ 2 ≤ (1 + ε) * ∑ i, y i ^ 2 + (1 + 1 / ε) * ∑ i, x i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  have key : (1 + ε) * y i ^ 2 + (1 + 1 / ε) * x i ^ 2 - (y i - x i) ^ 2
      = (ε * y i + x i) ^ 2 / ε := by
    field_simp
    ring
  have : 0 ≤ (ε * y i + x i) ^ 2 / ε := by positivity
  linarith

/-- `-A |z - y|² + β |y|² ≤ (A β / (A - β)) |z|²` for `β < A` (coordinatewise
`ProximalSharpLSI.neg_mul_sq_add_le`). -/
theorem neg_mul_sum_sq_add_le {A β : ℝ} (hAβ : β < A) (z y : Fin d → ℝ) :
    -(A * ∑ i, (z - y) i ^ 2) + β * ∑ i, y i ^ 2 ≤ A * β / (A - β) * ∑ i, z i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa using ProximalSharpLSI.neg_mul_sq_add_le hAβ (z i) (y i)

section Lower

variable (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]

/-- **Gaussian lower bound for `π * N(0, η I)`.** For a probability `π` on `Fin d → ℝ` and
`0 < b < η` there is `c > 0` with `c e^{-|y|²/(2b)} ≤ heatFlowDensityPi π η y` for all `y`. -/
theorem exists_mul_exp_le_heatFlowDensityPi {b η : ℝ} (hb : 0 < b) (hbη : b < η) :
    ∃ c > 0, ∀ y, c * Real.exp (-(∑ i, y i ^ 2) / (2 * b)) ≤ heatFlowDensityPi π η y := by
  have hη : 0 < η := hb.trans hbη
  obtain ⟨R, hR, hm⟩ := HeatFlowRegularityPerturbedPi.exists_measureReal_ball_pos π
  set B := {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ R} with hB
  have hBm : MeasurableSet B := measurableSet_le (by fun_prop) measurable_const
  set ε := η / b - 1 with hε
  have hε0 : 0 < ε := by rw [hε, sub_pos, one_lt_div hb]; exact hbη
  have hεb : (1 + ε) / (2 * η) = 1 / (2 * b) := by rw [hε]; field_simp; ring
  set c₀ : ℝ := (Real.sqrt (2 * Real.pi * η))⁻¹ ^ d
    * Real.exp (-((1 + 1 / ε) * R / (2 * η))) with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  refine ⟨π.real B * c₀, by positivity, fun y => ?_⟩
  have hint : Integrable (fun x => heatDensityPi η (y - x)) π :=
    Integrable.of_bound ((continuous_heatDensityPi η).comp (by fun_prop)).aestronglyMeasurable
      ((Real.sqrt (2 * Real.pi * η))⁻¹ ^ d) (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensityPi_pos hη _).le]; exact heatDensityPi_le hη _)
  have h1 : ∫ x in B, heatDensityPi η (y - x) ∂π ≤ heatFlowDensityPi π η y :=
    setIntegral_le_integral hint (Eventually.of_forall fun x => (heatDensityPi_pos hη _).le)
  have h2 : ∀ x ∈ B, c₀ * Real.exp (-(∑ i, y i ^ 2) / (2 * b)) ≤ heatDensityPi η (y - x) := by
    intro x hx
    have hx' : ∑ i, x i ^ 2 ≤ R := hx
    rw [heatDensityPi_eq_exp, hc₀, mul_assoc, ← Real.exp_add]
    gcongr
    have h3 := sum_sq_sub_le_mul hε0 y x
    have h5 : (1 + 1 / ε) * ∑ i, x i ^ 2 ≤ (1 + 1 / ε) * R :=
      mul_le_mul_of_nonneg_left hx' (by positivity)
    have h6 : (∑ i, (y - x) i ^ 2) / (2 * η)
        ≤ ((1 + ε) * (∑ i, y i ^ 2) + (1 + 1 / ε) * R) / (2 * η) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e : ((1 + ε) * (∑ i, y i ^ 2) + (1 + 1 / ε) * R) / (2 * η)
        = (∑ i, y i ^ 2) / (2 * b) + (1 + 1 / ε) * R / (2 * η) := by
      rw [hε]; field_simp; ring
    rw [e] at h6
    rw [neg_div, neg_div]
    linarith
  have h3 := setIntegral_mono_on (integrable_const (c₀ * Real.exp (-(∑ i, y i ^ 2) / (2 * b))))
    hint.integrableOn hBm h2
  rw [setIntegral_const, smul_eq_mul] at h3
  linarith

/-- **Domination of the backward kernel on `Fin d → ℝ`.** For a probability `π`, `0 < a ≤ b < η`,
there are `K, L ≥ 0` such that for all `t ∈ [a, b]` and all `z, y`:
`(1 + |z - y|²) φ_t(z - y) / w_η(y) ≤ K e^{L |z|²}`, `w_η = heatFlowDensityPi π η`. -/
theorem exists_bwd_boundPi {η a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbη : b < η) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ z y : Fin d → ℝ,
      (1 + ∑ i, (z - y) i ^ 2) * heatDensityPi t (z - y) / heatFlowDensityPi π η y
        ≤ K * Real.exp (L * ∑ i, z i ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  set b₁ := (2 * b + η) / 3 with hb₁
  set b₂ := (b + 2 * η) / 3 with hb₂
  have hbb₁ : b < b₁ := by rw [hb₁]; linarith
  have hb₁b₂ : b₁ < b₂ := by rw [hb₁, hb₂]; linarith
  have hb₂η : b₂ < η := by rw [hb₂]; linarith
  have hb₁0 : 0 < b₁ := hb.trans hbb₁
  have hb₂0 : 0 < b₂ := hb₁0.trans hb₁b₂
  obtain ⟨c, hc, hlow⟩ := exists_mul_exp_le_heatFlowDensityPi π hb₂0 hb₂η
  set κ := 1 / (2 * b) - 1 / (2 * b₁) with hκ
  have hκ0 : 0 < κ := by
    rw [hκ, sub_pos]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set A := 1 / (2 * b₁) with hA
  set β := 1 / (2 * b₂) with hβ
  have hβ0 : 0 < β := by positivity
  have hAβ : β < A := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set C₀ := (Real.sqrt (2 * Real.pi * a))⁻¹ ^ d with hC₀
  refine ⟨C₀ * (1 + 1 / κ) / c, A * β / (A - β), by positivity,
    div_nonneg (by positivity) (by linarith), fun t ht z y => ?_⟩
  set S := ∑ i, (z - y) i ^ 2 with hS
  have hS0 : 0 ≤ S := sum_sq_nonneg _
  have hw := hlow y
  have hw0 : 0 < heatFlowDensityPi π η y := lt_of_lt_of_le (by positivity) hw
  rw [div_le_iff₀ hw0]
  have hφ := heatDensityPi_le_exp ha ht.1 ht.2 (z - y)
  have hsplit : Real.exp (-S / (2 * b)) = Real.exp (-(κ * S)) * Real.exp (-(A * S)) := by
    rw [← Real.exp_add]; congr 1; rw [hκ, hA]; field_simp; ring
  have hpoly : (1 + S) * Real.exp (-(κ * S)) ≤ 1 + 1 / κ := by
    have := mul_exp_neg_le_inv hκ0 S
    have : Real.exp (-(κ * S)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ κ * S := by positivity
      linarith)
    nlinarith
  have hquad := neg_mul_sum_sq_add_le hAβ z y
  have hexp : Real.exp (-(A * S)) ≤ Real.exp (A * β / (A - β) * ∑ i, z i ^ 2)
      * Real.exp (-(∑ i, y i ^ 2) / (2 * b₂)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : -(∑ i, y i ^ 2) / (2 * b₂) = -(β * ∑ i, y i ^ 2) := by rw [hβ]; ring
    rw [this]
    linarith
  have hφ0 := (heatDensityPi_pos (ha.trans_le ht.1) (z - y)).le
  calc (1 + S) * heatDensityPi t (z - y)
      ≤ (1 + S) * (C₀ * (Real.exp (-(κ * S)) * Real.exp (-(A * S)))) := by
        rw [← hsplit]; gcongr
    _ = C₀ * ((1 + S) * Real.exp (-(κ * S))) * Real.exp (-(A * S)) := by ring
    _ ≤ C₀ * (1 + 1 / κ) * (Real.exp (A * β / (A - β) * ∑ i, z i ^ 2)
          * Real.exp (-(∑ i, y i ^ 2) / (2 * b₂))) := by gcongr
    _ = C₀ * (1 + 1 / κ) / c * Real.exp (A * β / (A - β) * ∑ i, z i ^ 2)
          * (c * Real.exp (-(∑ i, y i ^ 2) / (2 * b₂))) := by field_simp
    _ ≤ _ := by gcongr

end Lower

/-! ### The backward ratio `U` -/

/-- The backward ratio `U t z = ∫ φ_t(z - y) / w_η(y) dμ(y)` with `φ_t = heatDensityPi t` and
`w_η = heatFlowDensityPi π η`: for `μ ≪ π^Y` it is the heat semigroup `N(0, t I) * r` applied to
`r = dμ/dπ^Y`. -/
noncomputable def bwdRatioPi (π μ : Measure (Fin d → ℝ)) (η t : ℝ) (z : Fin d → ℝ) : ℝ :=
  ∫ y, heatDensityPi t (z - y) / heatFlowDensityPi π η y ∂μ

/-- The gradient of `bwdRatioPi`: `∫ ∇φ_t(z - y) / w_η(y) dμ(y)` (`hasFDerivAt_bwdRatioPi_x`). -/
noncomputable def bwdRatioGradPi (π μ : Measure (Fin d → ℝ)) (η t : ℝ) (z : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => ∫ y, heatGradPi t (z - y) i / heatFlowDensityPi π η y ∂μ

/-- The Hessian of `bwdRatioPi`: `∫ ∂ᵢ∂ⱼφ_t(z - y) / w_η(y) dμ(y)`
(`hasFDerivAt_bwdRatioGradPi_x`). -/
noncomputable def bwdRatioHessPi (π μ : Measure (Fin d → ℝ)) (η t : ℝ) (z : Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  ∫ y, heatHessPi t (z - y) i j / heatFlowDensityPi π η y ∂μ

section Ratio

variable (π μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] [IsFiniteMeasure μ] {η : ℝ}

omit [IsFiniteMeasure μ] in
/-- Pointwise domination of the integrands of `bwdRatioPi`, `bwdRatioGradPi`, `bwdRatioHessPi`:
for `0 < a ≤ b < η` there are `K, L ≥ 0` with `|∂^k φ_t(z - y)| / w_η(y) ≤ K e^{L |z|²}`
(`k = 0, 1, 2`, every coordinate) for `t ∈ [a, b]` and all `z, y`. -/
theorem bwd_integrand_boundPi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbη : b < η) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ z y : Fin d → ℝ,
      |heatDensityPi t (z - y) / heatFlowDensityPi π η y|
          ≤ K * Real.exp (L * ∑ i, z i ^ 2) ∧
      (∀ i, |heatGradPi t (z - y) i / heatFlowDensityPi π η y|
          ≤ K * Real.exp (L * ∑ i, z i ^ 2)) ∧
      (∀ i j, |heatHessPi t (z - y) i j / heatFlowDensityPi π η y|
          ≤ K * Real.exp (L * ∑ i, z i ^ 2)) := by
  have hη : 0 < η := ha.trans_le hab |>.trans hbη
  obtain ⟨K₀, L, hK₀, hL, hb⟩ := exists_bwd_boundPi π ha hab hbη
  have hD : 1 ≤ (1 + 1 / a) ^ 2 := by
    have : 0 < 1 / a := by positivity
    nlinarith
  refine ⟨(1 + 1 / a) ^ 2 * K₀, L, by positivity, hL, fun t ht z y => ?_⟩
  have hw := heatFlowDensityPi_pos π hη y
  have ht0 : 0 < t := ha.trans_le ht.1
  have hφ := heatDensityPi_pos ht0 (z - y)
  have hmain := hb t ht z y
  have hE : 0 ≤ K₀ * Real.exp (L * ∑ i, z i ^ 2) := by positivity
  have hS := sum_sq_nonneg (z - y)
  have h0 : heatDensityPi t (z - y) / heatFlowDensityPi π η y
      ≤ (1 + ∑ i, (z - y) i ^ 2) * heatDensityPi t (z - y) / heatFlowDensityPi π η y :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hφ.le (by linarith)) hw.le
  have hgen : ∀ X : ℝ, |X| ≤ (1 + 1 / a) ^ 2 * ((1 + ∑ i, (z - y) i ^ 2) * heatDensityPi t (z - y))
      → |X / heatFlowDensityPi π η y| ≤ (1 + 1 / a) ^ 2 * K₀ * Real.exp (L * ∑ i, z i ^ 2) := by
    intro X hX
    rw [abs_div, abs_of_pos hw]
    calc |X| / heatFlowDensityPi π η y
        ≤ (1 + 1 / a) ^ 2 * ((1 + ∑ i, (z - y) i ^ 2) * heatDensityPi t (z - y))
            / heatFlowDensityPi π η y := by gcongr
      _ = (1 + 1 / a) ^ 2 * ((1 + ∑ i, (z - y) i ^ 2) * heatDensityPi t (z - y)
            / heatFlowDensityPi π η y) := by ring
      _ ≤ _ := by rw [mul_assoc]; gcongr
  refine ⟨?_, fun i => hgen _ (abs_heatGradPi_le_mul ha ht.1 _ i),
    fun i j => hgen _ (abs_heatHessPi_le_mul ha ht.1 _ i j)⟩
  rw [abs_of_pos (div_pos hφ hw)]
  calc heatDensityPi t (z - y) / heatFlowDensityPi π η y ≤ K₀ * Real.exp (L * ∑ i, z i ^ 2) :=
        h0.trans hmain
    _ ≤ _ := by rw [mul_assoc]; exact le_mul_of_one_le_left hE hD

omit [IsFiniteMeasure μ] in
/-- Continuity of `y ↦ g(z - y) / w_η(y)` for continuous `g`. -/
theorem continuous_div_heatFlowDensityPi (hη : 0 < η) {g : (Fin d → ℝ) → ℝ}
    (hg : Continuous g) (z : Fin d → ℝ) :
    Continuous (fun y => g (z - y) / heatFlowDensityPi π η y) :=
  (hg.comp (by fun_prop)).div (continuous_heatFlowDensityPi π hη)
    fun y => (heatFlowDensityPi_pos π hη y).ne'

/-- `|z|² ≤ ∑ᵢ (|z₀ᵢ| + 1)²` on the (sup-norm) unit ball around `z₀`. -/
theorem sum_sq_le_of_mem_ball {z z₀ : Fin d → ℝ} (hz : z ∈ Metric.ball z₀ 1) :
    ∑ i, z i ^ 2 ≤ ∑ i, (|z₀ i| + 1) ^ 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : |z i - z₀ i| ≤ ‖z - z₀‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (z - z₀) i
  have h2 : |z i| ≤ |z₀ i| + 1 := by
    have := abs_sub_abs_le_abs_sub (z i) (z₀ i); linarith
  rw [← sq_abs (z i)]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-- **Differentiation under the integral against `μ`.** Let `k` be differentiable on
`Fin d → ℝ` with gradient `g` (continuous coordinates), and assume
`|k(z - y)| / w_η(y)`, `|gᵢ(z - y)| / w_η(y) ≤ K e^{L |z|²}` for all `z, y, i`. Then for a finite
`μ`, `z ↦ ∫ k(z - y) / w_η(y) dμ(y)` has gradient `∫ g(z - y) / w_η(y) dμ(y)`. -/
theorem hasFDerivAt_integral_div (hη : 0 < η) {k : (Fin d → ℝ) → ℝ}
    {g : (Fin d → ℝ) → Fin d → ℝ} (hk : ∀ v, HasFDerivAt k (dotCLM (g v)) v)
    (hg : ∀ i, Continuous fun v => g v i) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hkb : ∀ z y, |k (z - y) / heatFlowDensityPi π η y| ≤ K * Real.exp (L * ∑ i, z i ^ 2))
    (hgb : ∀ z y i,
      |g (z - y) i / heatFlowDensityPi π η y| ≤ K * Real.exp (L * ∑ i, z i ^ 2))
    (z₀ : Fin d → ℝ) :
    HasFDerivAt (fun z => ∫ y, k (z - y) / heatFlowDensityPi π η y ∂μ)
      (dotCLM fun i => ∫ y, g (z₀ - y) i / heatFlowDensityPi π η y ∂μ) z₀ := by
  set w := heatFlowDensityPi π η with hwdef
  have hw := heatFlowDensityPi_pos π hη
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun v => (hk v).continuousAt
  set B : ℝ := ∑ i, (|z₀ i| + 1) ^ 2 with hB
  set M : ℝ := K * Real.exp (L * B) with hM
  have hzM : ∀ z ∈ Metric.ball z₀ 1, K * Real.exp (L * ∑ i, z i ^ 2) ≤ M := fun z hz => by
    have := sum_sq_le_of_mem_ball hz
    rw [hM]; gcongr
  have hz₀ : z₀ ∈ Metric.ball z₀ 1 := Metric.mem_ball_self one_pos
  have hgi : ∀ z i, Continuous fun y => g (z - y) i / w y := fun z i =>
    continuous_div_heatFlowDensityPi π hη (hg i) z
  have hF' : ∀ z, Continuous fun y => dotCLM fun i => g (z - y) i / w y := fun z =>
    continuous_dotCLM (continuous_pi fun i => hgi z i)
  have hbd : ∀ z ∈ Metric.ball z₀ 1, ∀ y, ‖dotCLM fun i => g (z - y) i / w y‖ ≤ d * M :=
    fun z hz y => (norm_dotCLM_le _).trans (by
      calc ∑ i, |g (z - y) i / w y| ≤ ∑ _i : Fin d, M :=
            Finset.sum_le_sum fun i _ => (hgb z y i).trans (hzM z hz)
        _ = d * M := by simp)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (Metric.ball_mem_nhds z₀ one_pos)
    (F := fun z y => k (z - y) / w y) (F' := fun z y => dotCLM fun i => g (z - y) i / w y)
    (bound := fun _ => d * M)
    (Eventually.of_forall fun z =>
      (continuous_div_heatFlowDensityPi π hη hkc z).aestronglyMeasurable)
    (Integrable.of_bound (continuous_div_heatFlowDensityPi π hη hkc z₀).aestronglyMeasurable
      _ (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hkb z₀ y))
    (hF' z₀).aestronglyMeasurable
    (Eventually.of_forall fun y z hz => hbd z hz y) (integrable_const _)
    (Eventually.of_forall fun y z _ => by
      have h1 : HasFDerivAt (fun z => k (z - y)) (dotCLM (g (z - y))) z := by
        have := (hk (z - y)).comp z ((hasFDerivAt_id z).sub_const y)
        simpa [Function.comp_def] using this
      have e : (fun z => k (z - y) / w y) = fun z => (w y)⁻¹ * k (z - y) :=
        funext fun z => by ring
      rw [e]
      refine (h1.const_mul (w y)⁻¹).congr_fderiv (eq_dotCLM_of_apply fun v => ?_)
      simp only [smul_apply, dotCLM_apply, dotProduct, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  refine h.congr_fderiv (eq_dotCLM_of_apply fun v => ?_)
  rw [ContinuousLinearMap.integral_apply (Integrable.of_bound (hF' z₀).aestronglyMeasurable _
    (Eventually.of_forall fun y => hbd z₀ hz₀ y)) v]
  have hgi' : ∀ i, Integrable (fun y => g (z₀ - y) i / w y) μ := fun i =>
    Integrable.of_bound (hgi z₀ i).aestronglyMeasurable _
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb z₀ y i)
  simp_rw [dotCLM_apply, dotProduct]
  rw [integral_finsetSum _ fun i _ => (hgi' i).mul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _

/-- `z ↦ U t z` has gradient `bwdRatioGradPi` (for `0 < t < η`, any finite `μ`). -/
theorem hasFDerivAt_bwdRatioPi_x {t : ℝ} (ht : 0 < t) (htη : t < η) (z₀ : Fin d → ℝ) :
    HasFDerivAt (bwdRatioPi π μ η t) (dotCLM (bwdRatioGradPi π μ η t z₀)) z₀ := by
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_boundPi π ht le_rfl htη
  have ht' : t ∈ Icc t t := ⟨le_rfl, le_rfl⟩
  exact hasFDerivAt_integral_div π μ (ht.trans htη) (hasFDerivAt_heatDensityPi t)
    (fun i => (continuous_apply i).comp (continuous_heatGradPi t)) hK hL
    (fun z y => (hb t ht' z y).1) (fun z y i => (hb t ht' z y).2.1 i) z₀

/-- `z ↦ ∂ᵢ U t z` has gradient `(bwdRatioHessPi t z i j)ⱼ` (for `0 < t < η`, finite `μ`). -/
theorem hasFDerivAt_bwdRatioGradPi_x {t : ℝ} (ht : 0 < t) (htη : t < η) (i : Fin d)
    (z₀ : Fin d → ℝ) :
    HasFDerivAt (fun z => bwdRatioGradPi π μ η t z i)
      (dotCLM fun j => bwdRatioHessPi π μ η t z₀ i j) z₀ := by
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_boundPi π ht le_rfl htη
  have ht' : t ∈ Icc t t := ⟨le_rfl, le_rfl⟩
  exact hasFDerivAt_integral_div π μ (ht.trans htη) (k := fun v => heatGradPi t v i)
    (g := fun v j => heatHessPi t v i j) (hasFDerivAt_heatGradPi t i)
    (fun j => continuous_heatHessPi t i j) hK hL
    (fun z y => (hb t ht' z y).2.1 i) (fun z y j => (hb t ht' z y).2.2 i j) z₀

/-- **Heat equation for `U`.** For `0 < t < η` and every `z`,
`∂_t U(t, z) = ½ ΔU(t, z) = ½ ∑ᵢ bwdRatioHessPi t z i i` (any finite `μ`). -/
theorem hasDerivAt_bwdRatioPi_t {t : ℝ} (ht : 0 < t) (htη : t < η) (z : Fin d → ℝ) :
    HasDerivAt (fun r => bwdRatioPi π μ η r z) ((∑ i, bwdRatioHessPi π μ η t z i i) / 2) t := by
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_boundPi π (η := η) (a := t / 2)
    (b := (t + η) / 2) (by linarith) (by linarith) (by linarith)
  have hs : Ioo (t / 2) ((t + η) / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hmem : ∀ r ∈ Ioo (t / 2) ((t + η) / 2), r ∈ Icc (t / 2) ((t + η) / 2) :=
    fun r hr => Ioo_subset_Icc_self hr
  set w := heatFlowDensityPi π η
  have hlap : ∀ (r : ℝ) (v y : Fin d → ℝ),
      heatLapPi r v / 2 / w y = (∑ i, heatHessPi r v i i / w y) / 2 := by
    intro r v y; unfold heatLapPi; rw [← Finset.sum_div]; ring
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hs
    (F := fun r y => heatDensityPi r (z - y) / w y)
    (F' := fun r y => heatLapPi r (z - y) / 2 / w y)
    (bound := fun _ => d * (K * Real.exp (L * ∑ i, z i ^ 2)))
    (Eventually.of_forall fun r =>
      (continuous_div_heatFlowDensityPi π hη (continuous_heatDensityPi r)
        z).aestronglyMeasurable)
    (Integrable.of_bound (continuous_div_heatFlowDensityPi π hη
      (continuous_heatDensityPi t) z).aestronglyMeasurable _ (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hb t ⟨by linarith, by linarith⟩ z y).1))
    ((continuous_div_heatFlowDensityPi π hη ((continuous_heatLapPi t).div_const 2)
      z).aestronglyMeasurable)
    (Eventually.of_forall fun y r hr => by
      rw [Real.norm_eq_abs, hlap, abs_div, abs_two]
      have h1 : |∑ i, heatHessPi r (z - y) i i / w y| ≤ d * (K * Real.exp (L * ∑ i, z i ^ 2)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (by
          calc ∑ i, |heatHessPi r (z - y) i i / w y|
              ≤ ∑ _i : Fin d, K * Real.exp (L * ∑ i, z i ^ 2) :=
                Finset.sum_le_sum fun i _ => (hb r (hmem r hr) z y).2.2 i i
            _ = _ := by simp)
      have h0 : 0 ≤ |∑ i, heatHessPi r (z - y) i i / w y| := abs_nonneg _
      linarith)
    (integrable_const _) (Eventually.of_forall fun y r hr =>
      (hasDerivAt_heatDensityPi_t (by linarith [hr.1]) (z - y)).div_const _)).2
  convert hd using 1
  · rfl
  have hI : ∀ i, Integrable (fun y => heatHessPi t (z - y) i i / w y) μ := fun i =>
    Integrable.of_bound (continuous_div_heatFlowDensityPi π hη (continuous_heatHessPi t i i)
      z).aestronglyMeasurable _ (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hb t ⟨by linarith, by linarith⟩ z y).2.2 i i)
  simp_rw [hlap]
  rw [integral_div, integral_finsetSum _ fun i _ => hI i]
  rfl

/-- `U t z > 0` for `0 < t < η` and a nonzero finite `μ`. -/
theorem bwdRatioPi_pos [NeZero μ] {t : ℝ} (ht : 0 < t) (htη : t < η) (z : Fin d → ℝ) :
    0 < bwdRatioPi π μ η t z := by
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_boundPi π ht le_rfl htη
  have hi : Integrable (fun y => heatDensityPi t (z - y) / heatFlowDensityPi π η y) μ :=
    Integrable.of_bound (continuous_div_heatFlowDensityPi π hη (continuous_heatDensityPi t)
      z).aestronglyMeasurable _ (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hb t ⟨le_rfl, le_rfl⟩ z y).1)
  have hpos : ∀ y, 0 < heatDensityPi t (z - y) / heatFlowDensityPi π η y := fun y =>
    div_pos (heatDensityPi_pos ht _) (heatFlowDensityPi_pos π hη y)
  unfold bwdRatioPi
  rw [integral_pos_iff_support_of_nonneg (fun y => (hpos y).le) hi]
  have : Function.support (fun y => heatDensityPi t (z - y) / heatFlowDensityPi π η y) = univ :=
    eq_univ_of_forall fun y => (hpos y).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne μ)

/-- `U t` is continuous (`0 < t < η`). -/
theorem continuous_bwdRatioPi {t : ℝ} (ht : 0 < t) (htη : t < η) :
    Continuous (bwdRatioPi π μ η t) :=
  continuous_iff_continuousAt.2 fun z => (hasFDerivAt_bwdRatioPi_x π μ ht htη z).continuousAt

/-- Each coordinate of `∇U t` is continuous (`0 < t < η`). -/
theorem continuous_bwdRatioGradPi {t : ℝ} (ht : 0 < t) (htη : t < η) (i : Fin d) :
    Continuous fun z => bwdRatioGradPi π μ η t z i :=
  continuous_iff_continuousAt.2 fun z =>
    (hasFDerivAt_bwdRatioGradPi_x π μ ht htη i z).continuousAt

end Ratio

/-! ### The reference family `W` -/

/-- **Backward heat equation for `W`.** For a finite `π`, `t < η` and every `z`,
`∂_t w_{η - t}(z) = -½ Δw_{η - t}(z)`, `w_s = heatFlowDensityPi π s`. -/
theorem hasDerivAt_bwdRefPi_t (π : Measure (Fin d → ℝ)) [IsFiniteMeasure π] {η t : ℝ}
    (htη : t < η) (z : Fin d → ℝ) :
    HasDerivAt (fun r => heatFlowDensityPi π (η - r) z)
      (-((∑ i, heatFlowHessPi π (η - t) z i i) / 2)) t := by
  have h := (hasDerivAt_heatFlowDensityPi_t π (sub_pos.2 htη) z).comp t
    ((hasDerivAt_id t).const_sub η)
  convert h using 1
  · rfl
  · simp only [heatFlowLapPi]; ring

/-- The reference family of the backward flow, `W t z = w_{η - t}(z)`. -/
noncomputable def bwdRefPi (π : Measure (Fin d → ℝ)) (η : ℝ) : ℝ → (Fin d → ℝ) → ℝ :=
  fun t z => heatFlowDensityPi π (η - t) z

/-- The gradient of `bwdRefPi`: `heatFlowGradPi π (η - t) z`. -/
noncomputable def bwdRefGradPi (π : Measure (Fin d → ℝ)) (η : ℝ) :
    ℝ → (Fin d → ℝ) → Fin d → ℝ :=
  fun t z => heatFlowGradPi π (η - t) z

/-- The Hessian of `bwdRefPi`: `heatFlowHessPi π (η - t) z`. -/
noncomputable def bwdRefHessPi (π : Measure (Fin d → ℝ)) (η : ℝ) :
    ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ :=
  fun t z => heatFlowHessPi π (η - t) z

/-- The KL curve along the backward flow, `Kb t = ∫ W_t U_t log U_t`
(`= KL(bwdKernelPi π η t ∘ₘ μ‖π * N(0, (η - t) I))` under integrability,
`toReal_klDiv_bwdKernelPi_comp_eq`). -/
noncomputable def bwdKLPi (π μ : Measure (Fin d → ℝ)) (η t : ℝ) : ℝ :=
  ∫ z, bklIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) t z

/-- The relative Fisher information along the backward flow, `Ib t = ∫ W_t |∇U_t|² / U_t`. -/
noncomputable def bwdFisherPi (π μ : Measure (Fin d → ℝ)) (η t : ℝ) : ℝ :=
  ∫ z, bFisherIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRatioGradPi π μ η) t z

/-! ### The backward kernel and the factorisation of the RGO -/

section Kernel

open FormalizeSampling.ProximalPi FormalizeSampling.ReverseKernel
open FormalizeSampling.ProximalGaussianPi (forwardKernelPi_eq_heatKernelPi)

/-- The forward density is the shifted heat kernel: `forwardDensityPi t x y = φ_t(y - x)` for
`t > 0`. -/
theorem forwardDensityPi_eq_ofReal {t : ℝ} (ht : 0 < t) (x y : Fin d → ℝ) :
    forwardDensityPi t x y = ENNReal.ofReal (heatDensityPi t (y - x)) := by
  rw [forwardDensityPi, MALA.prodGaussianPDF, heatDensityPi, ENNReal.ofReal_prod_of_nonneg
    fun i _ => (FormalizeSampling.HeatFlowDeBruijn.heatDensity_pos ht _).le]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianPDF, HeatFlowDeBruijn.gaussianPDFReal_eq_heatDensity ht]
  rfl

/-- `forwardKernelPi s ∘ₘ π = w_s dz` for a finite `π` and `s > 0`,
`w_s = heatFlowDensityPi π s`. -/
theorem forwardKernelPi_comp_eq_withDensity (π : Measure (Fin d → ℝ)) [IsFiniteMeasure π]
    {s : ℝ} (hs : 0 < s) :
    forwardKernelPi s ∘ₘ π =
      volume.withDensity fun z => ENNReal.ofReal (heatFlowDensityPi π s z) := by
  rw [forwardKernelPi_eq_heatKernelPi, heatKernelPi_comp_eq_withDensity π hs]

/-- For `s, t ≥ 0`: `forwardKernelPi t ∘ₖ forwardKernelPi s = forwardKernelPi (s + t)`. -/
theorem forwardKernelPi_comp_forwardKernelPi {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    forwardKernelPi (d := d) t ∘ₖ forwardKernelPi s = forwardKernelPi (s + t) := by
  rw [forwardKernelPi_eq_heatKernelPi, forwardKernelPi_eq_heatKernelPi,
    forwardKernelPi_eq_heatKernelPi, heatKernelPi_comp_heatKernelPi, Real.toNNReal_add hs ht,
    add_comm]

/-- The backward kernel from time `0` to time `t` of the backward flow:
`bwdKernelPi π η t y = w_{η-t}(z) φ_t(y - z) / m(y) dz` with `m` the marginal density
(`= w_η(y)`, `marginalDensity_bwdPi`), i.e. the Bayes reverse kernel of the Gaussian channel
`forwardKernelPi t` for the prior `π * N(0, (η - t) I)` (`isReverseKernel_bwdKernelPi`). -/
noncomputable def bwdKernelPi (π : Measure (Fin d → ℝ)) (η t : ℝ) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  densityKernel volume (reverseDensity volume
    (fun z => ENNReal.ofReal (heatFlowDensityPi π (η - t) z)) (forwardDensityPi t))

variable (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] {η : ℝ}

/-- The density of the backward reference marginal `π * N(0, (η - t) I)` is measurable. -/
theorem measurable_bwdPriorPi {t : ℝ} (htη : t < η) :
    Measurable (fun z => ENNReal.ofReal (heatFlowDensityPi π (η - t) z)) :=
  (continuous_heatFlowDensityPi π (sub_pos.2 htη)).measurable.ennreal_ofReal

/-- **Marginal of the backward prior.** For `0 < t < η`:
`∫ w_{η-t}(z) N(y; z, t I) dz = w_η(y)` (heat semigroup). -/
theorem marginalDensity_bwdPi {t : ℝ} (ht : 0 < t) (htη : t < η) (y : Fin d → ℝ) :
    marginalDensity volume (fun z => ENNReal.ofReal (heatFlowDensityPi π (η - t) z))
      (forwardDensityPi t) y = ENNReal.ofReal (heatFlowDensityPi π η y) := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hint : Integrable (fun z => heatFlowDensityPi π (η - t) z * heatDensityPi t (y - z)) := by
    refine (integrable_heatFlowDensityPi π hs).1.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d)
      ((continuous_heatDensityPi t).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (heatDensityPi_pos ht _).le]
    exact heatDensityPi_le ht _
  unfold marginalDensity
  have e : ∀ z, ENNReal.ofReal (heatFlowDensityPi π (η - t) z) * forwardDensityPi t z y
      = ENNReal.ofReal (heatFlowDensityPi π (η - t) z * heatDensityPi t (y - z)) := by
    intro z
    rw [forwardDensityPi_eq_ofReal ht, ← ENNReal.ofReal_mul (heatFlowDensityPi_pos π hs z).le]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z =>
    mul_nonneg (heatFlowDensityPi_pos π hs z).le (heatDensityPi_pos ht _).le)]
  congr 1
  have := (heatFlow_semigroup π hs ht).1 y
  rw [sub_add_cancel] at this
  exact this.symm

/-- The backward reverse density, explicitly: `w_{η-t}(z) φ_t(z - y) / w_η(y)`. -/
theorem reverseDensity_bwdPi {t : ℝ} (ht : 0 < t) (htη : t < η) (y z : Fin d → ℝ) :
    reverseDensity volume (fun z => ENNReal.ofReal (heatFlowDensityPi π (η - t) z))
      (forwardDensityPi t) y z = ENNReal.ofReal (heatFlowDensityPi π (η - t) z
        * (heatDensityPi t (z - y) / heatFlowDensityPi π η y)) := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hη : 0 < η := ht.trans htη
  rw [reverseDensity, marginalDensity_bwdPi π ht htη, forwardDensityPi_eq_ofReal ht,
    ← ENNReal.ofReal_mul (heatFlowDensityPi_pos π hs z).le,
    ← ENNReal.ofReal_div_of_pos (heatFlowDensityPi_pos π hη y), ← neg_sub z y,
    heatDensityPi_neg, mul_div_assoc]

/-- The backward kernel is a Markov kernel (`0 < t < η`). -/
theorem isMarkovKernel_bwdKernelPi {t : ℝ} (ht : 0 < t) (htη : t < η) :
    IsMarkovKernel (bwdKernelPi π η t) := by
  have hη : 0 < η := ht.trans htη
  refine isMarkovKernel_densityKernel (measurable_reverseDensity (measurable_bwdPriorPi π htη)
    (measurable_forwardDensityPi t)) fun y => ?_
  refine lintegral_reverseDensity_eq_one (measurable_bwdPriorPi π htη)
    (measurable_forwardDensityPi t) y ?_ ?_
  · rw [marginalDensity_bwdPi π ht htη, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact heatFlowDensityPi_pos π hη y
  · rw [marginalDensity_bwdPi π ht htη]; exact ENNReal.ofReal_ne_top

/-- **The backward kernel is a reverse kernel** of `forwardKernelPi t` for the prior
`forwardKernelPi (η - t) ∘ₘ π = π * N(0, (η - t) I)` (`0 < t < η`). -/
theorem isReverseKernel_bwdKernelPi {t : ℝ} (ht : 0 < t) (htη : t < η) :
    IsReverseKernel (forwardKernelPi t) (forwardKernelPi (η - t) ∘ₘ π) (bwdKernelPi π η t) := by
  have hs : 0 < η - t := sub_pos.2 htη
  rw [forwardKernelPi_comp_eq_withDensity π hs, forwardKernelPi_eq_densityKernel ht]
  refine isReverseKernel_densityKernel (measurable_bwdPriorPi π htη)
    (measurable_forwardDensityPi t) (lintegral_forwardDensityPi ht) ?_
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi π hs
  have h := measure_univ (μ := volume.withDensity fun z =>
    ENNReal.ofReal (heatFlowDensityPi π (η - t) z))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [h]; exact ENNReal.one_ne_top

/-- The backward kernel maps `π^Y` to `π * N(0, (η - t) I)`:
`bwdKernelPi π η t ∘ₘ (forwardKernelPi η ∘ₘ π) = forwardKernelPi (η - t) ∘ₘ π`. -/
theorem bwdKernelPi_comp_forward {t : ℝ} (ht : 0 < t) (htη : t < η) :
    bwdKernelPi π η t ∘ₘ (forwardKernelPi η ∘ₘ π) = forwardKernelPi (η - t) ∘ₘ π := by
  have hs : 0 < η - t := sub_pos.2 htη
  have := isMarkovKernel_bwdKernelPi π ht htη
  have h := (isReverseKernel_bwdKernelPi π ht htη).comp_marginal
  have e : forwardKernelPi η ∘ₘ π = forwardKernelPi t ∘ₘ (forwardKernelPi (η - t) ∘ₘ π) := by
    rw [Measure.comp_assoc, forwardKernelPi_comp_forwardKernelPi hs.le ht.le, sub_add_cancel]
  rw [e]
  exact h

omit [IsProbabilityMeasure π] in
/-- **Factorisation of the RGO through the backward kernel.** For measurable `f` with integrable
`e^{-f}`, `π = targetPi f`, `0 < t < η`, and every law `μ ≪ π^Y = forwardKernelPi η ∘ₘ π`:
`rgoKernelPi f η ∘ₘ μ = (forwardKernelPi (η - t))†π ∘ₘ (bwdKernelPi π η t ∘ₘ μ)`. -/
theorem rgoKernelPi_comp_eq_posterior_comp {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {t : ℝ} (ht : 0 < t) (htη : t < η)
    (μ : Measure (Fin d → ℝ)) (hμ : μ ≪ forwardKernelPi η ∘ₘ targetPi f) :
    haveI := isFiniteMeasure_targetPi f
    rgoKernelPi f η ∘ₘ μ =
      (forwardKernelPi (η - t))†(targetPi f) ∘ₘ (bwdKernelPi (targetPi f) η t ∘ₘ μ) := by
  have := isProbabilityMeasure_targetPi hint
  have hs : 0 < η - t := sub_pos.2 htη
  have hη : 0 < η := ht.trans htη
  have := isMarkovKernel_bwdKernelPi (targetPi f) ht htη
  have hfac : forwardKernelPi (d := d) η = forwardKernelPi t ∘ₖ forwardKernelPi (η - t) := by
    rw [forwardKernelPi_comp_forwardKernelPi hs.le ht.le, sub_add_cancel]
  have hmeas : forwardKernelPi t ∘ₘ (forwardKernelPi (η - t) ∘ₘ targetPi f)
      = forwardKernelPi η ∘ₘ targetPi f := by
    rw [Measure.comp_assoc, ← hfac]
  have h1 := rgoKernelPi_ae_eq_posterior hf hint hη
  have h2' : ∀ (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsFiniteKernel κ],
      κ = forwardKernelPi t ∘ₖ forwardKernelPi (η - t) →
      κ†(targetPi f) =ᵐ[forwardKernelPi t ∘ₘ (forwardKernelPi (η - t) ∘ₘ targetPi f)]
        (forwardKernelPi (η - t))†(targetPi f) ∘ₖ
          (forwardKernelPi t)†(forwardKernelPi (η - t) ∘ₘ targetPi f) := by
    intro κ _ hκ
    subst hκ
    exact posterior_comp
  have h2 := h2' (forwardKernelPi η) hfac
  rw [hmeas] at h2
  have h3 : bwdKernelPi (targetPi f) η t =ᵐ[forwardKernelPi η ∘ₘ targetPi f]
      (forwardKernelPi t)†(forwardKernelPi (η - t) ∘ₘ targetPi f) := by
    have := (isReverseKernel_bwdKernelPi (targetPi f) ht htη).ae_eq_posterior
    rwa [hmeas] at this
  have h4 : ∀ᵐ y ∂(forwardKernelPi η ∘ₘ targetPi f), rgoKernelPi f η y =
      ((forwardKernelPi (η - t))†(targetPi f) ∘ₖ bwdKernelPi (targetPi f) η t) y := by
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [hy1, hy2, Kernel.comp_apply, Kernel.comp_apply, hy3]
  rw [Measure.comp_assoc]
  exact Measure.comp_congr (hμ.ae_le h4)

/-- The target is recovered from `π * N(0, s I)` by the posterior:
`(forwardKernelPi s)†π ∘ₘ (forwardKernelPi s ∘ₘ π) = π`. -/
theorem posterior_comp_forwardPi (s : ℝ) :
    (forwardKernelPi s)†π ∘ₘ (forwardKernelPi s ∘ₘ π) = π :=
  posterior_comp_self (κ := forwardKernelPi s) (μ := π)

omit [IsProbabilityMeasure π] in
/-- **Endpoint `t = η` by data processing.** For measurable `f` with integrable `e^{-f}`,
`π = targetPi f`, `0 < t < η` and `μ ≪ π^Y`:
`KL(rgoKernelPi f η ∘ₘ μ‖π) ≤ KL(bwdKernelPi π η t ∘ₘ μ‖π * N(0, (η - t) I))`. -/
theorem klDiv_rgoKernelPi_comp_le_bwd {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {t : ℝ} (ht : 0 < t) (htη : t < η)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] (hμ : μ ≪ forwardKernelPi η ∘ₘ targetPi f) :
    klDiv (rgoKernelPi f η ∘ₘ μ) (targetPi f)
      ≤ klDiv (bwdKernelPi (targetPi f) η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ targetPi f) := by
  have := isProbabilityMeasure_targetPi hint
  have := isMarkovKernel_bwdKernelPi (targetPi f) ht htη
  rw [rgoKernelPi_comp_eq_posterior_comp hf hint ht htη μ hμ]
  have e := posterior_comp_forwardPi (targetPi f) (η - t)
  calc _ = klDiv ((forwardKernelPi (η - t))†(targetPi f) ∘ₘ
          (bwdKernelPi (targetPi f) η t ∘ₘ μ))
        ((forwardKernelPi (η - t))†(targetPi f) ∘ₘ
          (forwardKernelPi (η - t) ∘ₘ targetPi f)) := by rw [e]
    _ ≤ _ := klDiv_comp_right_le _ _ _

/-- **Endpoint `t = 0` by data processing.** For `0 < t < η` and any finite law `μ`:
`KL(bwdKernelPi π η t ∘ₘ μ‖π * N(0, (η - t) I)) ≤ KL(μ‖π^Y)`. -/
theorem klDiv_bwdPi_le {t : ℝ} (ht : 0 < t) (htη : t < η) (μ : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ] :
    klDiv (bwdKernelPi π η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ π)
      ≤ klDiv μ (forwardKernelPi η ∘ₘ π) := by
  have := isMarkovKernel_bwdKernelPi π ht htη
  rw [← bwdKernelPi_comp_forward π ht htη]
  exact klDiv_comp_right_le _ _ _

/-- **Density of the backward marginal.** For `0 < t < η` and a finite law `μ`:
`bwdKernelPi π η t ∘ₘ μ = (W_t U_t) dz` with `W_t = w_{η-t}` and `U_t = bwdRatioPi π μ η t`. -/
theorem bwdKernelPi_comp_eq_withDensity (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] {t : ℝ}
    (ht : 0 < t) (htη : t < η) :
    bwdKernelPi π η t ∘ₘ μ = volume.withDensity fun z =>
      ENNReal.ofReal (heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z) := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hη : 0 < η := ht.trans htη
  obtain ⟨K, L, hK, hL, hb⟩ := bwd_integrand_boundPi π ht le_rfl htη
  have hjm : Measurable (Function.uncurry fun y z =>
      ENNReal.ofReal (heatFlowDensityPi π (η - t) z
        * (heatDensityPi t (z - y) / heatFlowDensityPi π η y))) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine ((continuous_heatFlowDensityPi π hs).comp continuous_snd).mul
      (((continuous_heatDensityPi t).comp (by fun_prop)).div
        ((continuous_heatFlowDensityPi π hη).comp continuous_fst) fun p =>
          (heatFlowDensityPi_pos π hη _).ne')
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), withDensity_apply _ hA]
  have e1 : ∀ y, bwdKernelPi π η t y A = ∫⁻ z in A, ENNReal.ofReal
      (heatFlowDensityPi π (η - t) z * (heatDensityPi t (z - y) / heatFlowDensityPi π η y)) := by
    intro y
    rw [bwdKernelPi, densityKernel_apply (measurable_reverseDensity (measurable_bwdPriorPi π htη)
      (measurable_forwardDensityPi t)), withDensity_apply _ hA]
    exact setLIntegral_congr_fun hA fun z _ => reverseDensity_bwdPi π ht htη y z
  simp_rw [e1]
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  refine setLIntegral_congr_fun hA fun z _ => ?_
  have hi : Integrable (fun y => heatDensityPi t (z - y) / heatFlowDensityPi π η y) μ :=
    Integrable.of_bound (continuous_div_heatFlowDensityPi π hη (continuous_heatDensityPi t)
      z).aestronglyMeasurable _ (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact (hb t ⟨le_rfl, le_rfl⟩ z y).1)
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (Eventually.of_forall fun y =>
    mul_nonneg (heatFlowDensityPi_pos π hs z).le
      (div_nonneg (heatDensityPi_pos ht _).le (heatFlowDensityPi_pos π hη y).le)),
    integral_const_mul]
  rfl

end Kernel

/-! ### Regularity hypotheses, de Bruijn and LSI along the backward flow -/

/-- **Regularity hypotheses for the backward de Bruijn identity on `Fin d → ℝ`** on the open time
interval `(0, η)`, for `W t = w_{η-t}` (`bwdRefPi`) and `U t = bwdRatioPi π μ η t` with their
explicit gradients and Hessians. As for `HeatFlowDeBruijnPi.HeatFlowRegularPi`, these are
integrability and local domination conditions (the boundary terms of the integration by parts
are controlled by integrability of each flux coordinate and of its partial derivative); none
of them is the identity or the inequality proved from them. Nothing is required at `t = 0` or
`t = η`. -/
structure BackwardHeatFlowRegularPi (π μ : Measure (Fin d → ℝ)) (η : ℝ) : Prop where
  /-- `W U log U` (`= p log(p/W)`, `p = W U`) is Lebesgue integrable. -/
  integrable_kl : ∀ t ∈ Ioo 0 η,
    Integrable (bklIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) t)
  /-- The time derivative `bklRatePi` of the integrand is dominated, locally uniformly in time,
  by an integrable function. -/
  dominated : ∀ t ∈ Ioo 0 η, ∃ bound : (Fin d → ℝ) → ℝ, Integrable bound ∧ ∀ᶠ r in 𝓝 t, ∀ z,
    |bklRatePi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRefHessPi π η) (bwdRatioHessPi π μ η) r z|
      ≤ bound z
  /-- The relative Fisher integrand `W |∇U|² / U` is integrable. -/
  integrable_fisher : ∀ t ∈ Ioo 0 η,
    Integrable (bFisherIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRatioGradPi π μ η) t)
  /-- Each coordinate of the backward flux is integrable. -/
  integrable_flux : ∀ t ∈ Ioo 0 η, ∀ i, Integrable (bklFluxPi (bwdRefPi π η) (bwdRatioPi π μ η)
    (bwdRefGradPi π η) (bwdRatioGradPi π μ η) t i)
  /-- The `i`-th partial derivative of the `i`-th flux coordinate is integrable. -/
  integrable_fluxDeriv : ∀ t ∈ Ioo 0 η, ∀ i, Integrable (bklFluxDerivPi (bwdRefPi π η)
    (bwdRatioPi π μ η) (bwdRatioGradPi π μ η) (bwdRefHessPi π η) (bwdRatioHessPi π μ η) t i)

section Main

open FormalizeSampling.ProximalPi FormalizeSampling.LogSobolevPi

variable (π μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] [IsProbabilityMeasure μ] {η : ℝ}

/-- **Backward de Bruijn identity on `Fin d → ℝ` (Verified under `BackwardHeatFlowRegularPi`).**
For probability laws `π, μ` and `t₀ ∈ (0, η)`:
`d/dt ∫ W_t U_t log U_t = -½ ∫ W_t |∇U_t|² / U_t` at `t₀`. -/
theorem hasDerivAt_bwdKLPi (hreg : BackwardHeatFlowRegularPi π μ η) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo 0 η) :
    HasDerivAt (bwdKLPi π μ η) (-(1 / 2) * bwdFisherPi π μ η t₀) t₀ := by
  obtain ⟨bound, hb_int, hev⟩ := hreg.dominated t₀ ht₀
  obtain ⟨v, hv, hvb⟩ := hev.exists_mem
  have hs : Ioo 0 η ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀
  exact hasDerivAt_integral_bklIntegrandPi (s := v ∩ Ioo 0 η) (inter_mem hv hs)
    (fun t ht z => bwdRatioPi_pos π μ ht.2.1 ht.2.2 z)
    (fun t ht z => hasDerivAt_bwdRefPi_t π ht.2.2 z)
    (fun t ht z => hasDerivAt_bwdRatioPi_t π μ ht.2.1 ht.2.2 z)
    (fun t ht z => hasFDerivAt_heatFlowDensityPi π (sub_pos.2 ht.2.2) z)
    (fun t ht z => hasFDerivAt_bwdRatioPi_x π μ ht.2.1 ht.2.2 z)
    (fun i z => hasFDerivAt_heatFlowGradPi π (sub_pos.2 ht₀.2) i z)
    (fun i z => hasFDerivAt_bwdRatioGradPi_x π μ ht₀.1 ht₀.2 i z)
    (hreg.integrable_kl t₀ ht₀) hb_int (fun t ht => hvb t ht.1)
    (hreg.integrable_fisher t₀ ht₀) (hreg.integrable_flux t₀ ht₀)
    (hreg.integrable_fluxDeriv t₀ ht₀)

/-- The backward marginal `W_t U_t` is a probability density (`0 < t < η`). -/
theorem isProbabilityMeasure_withDensity_bwdPi {t : ℝ} (ht : 0 < t) (htη : t < η) :
    IsProbabilityMeasure (volume.withDensity fun z =>
      ENNReal.ofReal (heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z)) := by
  have := isMarkovKernel_bwdKernelPi π ht htη
  rw [← bwdKernelPi_comp_eq_withDensity π μ ht htη]
  infer_instance

/-- **KL along the backward flow.** For `0 < t < η` and integrable `W_t U_t log U_t`:
`KL(bwdKernelPi π η t ∘ₘ μ‖π * N(0, (η - t) I)) < ∞` and its real value is `bwdKLPi π μ η t`. -/
theorem toReal_klDiv_bwdKernelPi_comp_eq {t : ℝ} (ht : 0 < t) (htη : t < η)
    (hint : Integrable (bklIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) t)) :
    klDiv (bwdKernelPi π η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ π) ≠ ⊤ ∧
      (klDiv (bwdKernelPi π η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ π)).toReal
        = bwdKLPi π μ η t := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hq := heatFlowDensityPi_pos π hs
  have hU := bwdRatioPi_pos π μ ht htη
  have := isProbabilityMeasure_withDensity_bwdPi π μ ht htη
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi π hs
  have hqc := continuous_heatFlowDensityPi π hs
  have hpm : Measurable fun z => heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z :=
    (hqc.mul (continuous_bwdRatioPi π μ ht htη)).measurable
  have e : ∀ z, heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z
      * Real.log (heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z
        / heatFlowDensityPi π (η - t) z)
      = bklIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) t z := by
    intro z
    rw [mul_div_cancel_left₀ _ (hq z).ne', bklIntegrandPi, bwdRefPi, mul_assoc]
  have hint' : Integrable fun z => heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z
      * Real.log (heatFlowDensityPi π (η - t) z * bwdRatioPi π μ η t z
        / heatFlowDensityPi π (η - t) z) := by
    simp_rw [e]; exact hint
  have hKL := KLTransport.klDiv_withDensity_eq_integral hpm hqc.measurable
    (fun z => (mul_pos (hq z) (hU z)).le) hq hint'
  have hKL' := toReal_klDiv_withDensity_eq_integral hpm hqc.measurable
    (fun z => mul_pos (hq z) (hU z)) hq hint'
  rw [bwdKernelPi_comp_eq_withDensity π μ ht htη, forwardKernelPi_comp_eq_withDensity π hs]
  refine ⟨by rw [hKL]; exact ENNReal.ofReal_ne_top, hKL'.trans ?_⟩
  exact integral_congr_ae (Eventually.of_forall e)

/-- **LSI along the backward flow on `Fin d → ℝ`.** If `FunctionalLSIPi π (1/α)` (`α > 0`) and
the KL and Fisher integrands are integrable at `t ∈ (0, η)`, then
`2 α Kb(t) ≤ (1 + α (η - t)) Ib(t)` with `Kb = bwdKLPi`, `Ib = bwdFisherPi` (LSI of
`π * N(0, (η - t) I)` with constant `1/α + η - t`, applied to `√U_t`). -/
theorem bwdKLPi_le_of_targetLSIPi {α : ℝ} (hα : 0 < α) (hπ : FunctionalLSIPi π (1 / α)) {t : ℝ}
    (ht : 0 < t) (htη : t < η)
    (hkl : Integrable (bklIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) t))
    (hfi : Integrable
      (bFisherIntegrandPi (bwdRefPi π η) (bwdRatioPi π μ η) (bwdRatioGradPi π μ η) t)) :
    2 * α * bwdKLPi π μ η t ≤ (1 + α * (η - t)) * bwdFisherPi π μ η t := by
  have hs : 0 < η - t := sub_pos.2 htη
  have hq := heatFlowDensityPi_pos π hs
  have hqc := continuous_heatFlowDensityPi π hs
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi π hs
  have := isProbabilityMeasure_withDensity_bwdPi π μ ht htη
  have hL := ProximalLSIPi.functionalLSIPi_heatKernelPi_comp_targetPi hs hπ
  rw [heatKernelPi_comp_eq_withDensity π hs] at hL
  have hC : 0 ≤ 1 / α + (η - t) := by positivity
  obtain ⟨hmass, hone⟩ := integrable_and_integral_eq_one
    (hqc.mul (continuous_bwdRatioPi π μ ht htη)).measurable
    (fun z => (mul_pos (hq z) (bwdRatioPi_pos π μ ht htη z)).le)
  have h := integral_mul_log_le_of_functionalLSIPi hqc.measurable (fun z => (hq z).le) hC hL
    (bwdRatioPi_pos π μ ht htη) (hasFDerivAt_bwdRatioPi_x π μ ht htη)
    (continuous_bwdRatioGradPi π μ ht htη) hmass hone hkl hfi
  have e1 : bwdKLPi π μ η t = ∫ z, heatFlowDensityPi π (η - t) z
      * (bwdRatioPi π μ η t z * Real.log (bwdRatioPi π μ η t z)) := rfl
  have e2 : bwdFisherPi π μ η t = ∫ z, heatFlowDensityPi π (η - t) z
      * (bwdRatioGradPi π μ η t z ⬝ᵥ bwdRatioGradPi π μ η t z) / bwdRatioPi π μ η t z := rfl
  rw [e1, e2]
  have h2 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * α)
  have e3 : 2 * α * ((1 / α + (η - t)) / 2 * ∫ z, heatFlowDensityPi π (η - t) z
      * (bwdRatioGradPi π μ η t z ⬝ᵥ bwdRatioGradPi π μ η t z) / bwdRatioPi π μ η t z)
      = (1 + α * (η - t)) * ∫ z, heatFlowDensityPi π (η - t) z
      * (bwdRatioGradPi π μ η t z ⬝ᵥ bwdRatioGradPi π μ η t z) / bwdRatioPi π μ η t z := by
    field_simp
  linarith

end Main

/-! ### The backward step and the sharp PX-2 rate on `Fin d → ℝ` -/

section Rate

open FormalizeSampling.ProximalPi
open FormalizeSampling.LogSobolevPi
open FormalizeSampling.ProximalGaussianPi (forwardKernelPi_eq_heatKernelPi)

variable {f : (Fin d → ℝ) → ℝ} {η : ℝ}

/-- **Finite KL forces `∫ e^{-f} < ∞` on `Fin d → ℝ`.** For every kernel `κ` and probability
law `μ`, if `KL(μ‖κ ∘ₘ targetPi f) < ∞` then `e^{-f}` is Lebesgue integrable: otherwise
`targetNormalizerPi f = 0`, so `targetPi f = 0`, `κ ∘ₘ targetPi f = 0` and `KL(μ‖0) = ∞`. -/
theorem integrable_exp_neg_of_klDiv_comp_targetPi_ne_top
    (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hKL : klDiv μ (κ ∘ₘ targetPi f) ≠ ⊤) : Integrable (fun x => Real.exp (-f x)) := by
  by_contra h
  have h0 : targetPi f = 0 := by
    simp [targetPi, targetDensityPi, targetNormalizerPi, integral_undef h]
  rw [h0, Measure.bind_zero_left, klDiv_zero_right] at hKL
  exact hKL rfl

/-- **Finite KL forces `∫ e^{-f} < ∞` on `Fin d → ℝ`.** If a probability law `μ` has
`KL(μ‖targetPi f) < ∞`, then `e^{-f}` is Lebesgue integrable (`κ = id` in
`integrable_exp_neg_of_klDiv_comp_targetPi_ne_top`). -/
theorem integrable_exp_neg_of_klDiv_targetPi_ne_top (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (hKL : klDiv μ (targetPi f) ≠ ⊤) :
    Integrable (fun x => Real.exp (-f x)) :=
  integrable_exp_neg_of_klDiv_comp_targetPi_ne_top Kernel.id μ (by rwa [Measure.id_comp])

/-- **Backward strong data processing from a functional LSI on `Fin d → ℝ` (Conditional on
`BackwardHeatFlowRegularPi`).** Let `f` be measurable, `π = targetPi f`, `η > 0`, `α > 0` with
`FunctionalLSIPi π (1/α)`, and `μ` a probability law with `KL(μ‖π^Y) < ∞`,
`π^Y = forwardKernelPi η ∘ₘ π`, and `BackwardHeatFlowRegularPi π μ η` (integrability of
`e^{-f}` is not assumed: it follows from `KL(μ‖π^Y) < ∞`). Then
`KL(rgoKernelPi f η ∘ₘ μ‖π) < ∞` and
`KL(rgoKernelPi f η ∘ₘ μ‖π).toReal ≤ KL(μ‖π^Y).toReal / (1 + α η)`. -/
theorem toReal_klDiv_rgoKernelPi_comp_le_of_targetLSIPi (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hKL : klDiv μ (forwardKernelPi η ∘ₘ targetPi f) ≠ ⊤)
    (hreg : BackwardHeatFlowRegularPi (targetPi f) μ η)
    (hπ : FunctionalLSIPi (targetPi f) (1 / α)) :
    klDiv (rgoKernelPi f η ∘ₘ μ) (targetPi f) ≠ ⊤ ∧
      (klDiv (rgoKernelPi f η ∘ₘ μ) (targetPi f)).toReal
        ≤ (klDiv μ (forwardKernelPi η ∘ₘ targetPi f)).toReal / (1 + α * η) := by
  have hint := integrable_exp_neg_of_klDiv_comp_targetPi_ne_top (forwardKernelPi η) μ hKL
  have := isProbabilityMeasure_targetPi hint
  have hμ : μ ≪ forwardKernelPi η ∘ₘ targetPi f := (klDiv_ne_top_iff.1 hKL).1
  have hend : ∀ t ∈ Ioo 0 η, klDiv (rgoKernelPi f η ∘ₘ μ) (targetPi f)
      ≤ klDiv (bwdKernelPi (targetPi f) η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ targetPi f) :=
    fun t ht => klDiv_rgoKernelPi_comp_le_bwd hf hint ht.1 ht.2 μ hμ
  have hstart : ∀ t ∈ Ioo 0 η,
      klDiv (bwdKernelPi (targetPi f) η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ targetPi f)
        ≤ klDiv μ (forwardKernelPi η ∘ₘ targetPi f) :=
    fun t ht => klDiv_bwdPi_le (targetPi f) ht.1 ht.2 μ
  have hmid : η / 2 ∈ Ioo 0 η := ⟨by linarith, by linarith⟩
  have hfin : klDiv (rgoKernelPi f η ∘ₘ μ) (targetPi f) ≠ ⊤ :=
    ne_top_of_le_ne_top hKL ((hend _ hmid).trans (hstart _ hmid))
  refine ⟨hfin, ?_⟩
  have hKb : ∀ t ∈ Ioo 0 η,
      (klDiv (bwdKernelPi (targetPi f) η t ∘ₘ μ) (forwardKernelPi (η - t) ∘ₘ targetPi f)).toReal
        = bwdKLPi (targetPi f) μ η t := fun t ht =>
    (toReal_klDiv_bwdKernelPi_comp_eq (targetPi f) μ ht.1 ht.2 (hreg.integrable_kl t ht)).2
  refine BackwardHeatFlow.le_div_of_hasDerivAt_interior hα.le hη
    (I := bwdFisherPi (targetPi f) μ η)
    (fun t ht => hasDerivAt_bwdKLPi (targetPi f) μ hreg ht)
    (fun t ht => bwdKLPi_le_of_targetLSIPi (targetPi f) μ hα hπ ht.1 ht.2
      (hreg.integrable_kl t ht) (hreg.integrable_fisher t ht)) (fun t ht => ?_) (fun t ht => ?_)
  · rw [← hKb t ht]
    exact ENNReal.toReal_mono hKL (hstart t ht)
  · rw [← hKb t ht]
    exact ENNReal.toReal_mono (toReal_klDiv_bwdKernelPi_comp_eq (targetPi f) μ ht.1 ht.2
      (hreg.integrable_kl t ht)).1 (hend t ht)

/-- **Forward step from a functional LSI on `Fin d → ℝ` (Conditional on `HeatFlowRegularPi`).**
For a probability `π` with `FunctionalLSIPi π (1/α)` (`α > 0`), `η > 0`, a probability `ρ` with
`KL(ρ‖π) < ∞` and `HeatFlowRegularPi ρ π s` with `(0, η] ⊆ s`:
`KL(ρ^Y‖π^Y).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`, `ρ^Y = forwardKernelPi η ∘ₘ ρ`. -/
theorem toReal_klDiv_forwardKernelPi_le_of_targetLSIPi {π ρ : Measure (Fin d → ℝ)}
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (hKL : klDiv ρ π ≠ ⊤) {s : Set ℝ} (hreg : HeatFlowRegularPi ρ π s) (hs : Ioc 0 η ⊆ s)
    (hπ : FunctionalLSIPi π (1 / α)) :
    (klDiv (forwardKernelPi η ∘ₘ ρ) (forwardKernelPi η ∘ₘ π)).toReal
      ≤ (klDiv ρ π).toReal / (1 + α * η) := by
  rw [forwardKernelPi_eq_heatKernelPi]
  exact toReal_klDiv_heatKernelPi_le_of_regular hα.le hη hKL hreg hs
    (LogSobolevExtensionPi.heatFlowLSIPi_of_functionalLSIPi ρ π hα
      (fun t ht => ProximalLSIPi.functionalLSIPi_heatKernelPi_comp_targetPi ht.1 hπ) hreg
      (Ioo_subset_Ioc_self.trans hs))

/-- **Sharp PX-2 on `Fin d → ℝ`, one step, from a functional LSI (Conditional on the regularity
hypotheses).** Let `f` be measurable, `π = targetPi f`, `η, α > 0` with
`FunctionalLSIPi π (1/α)`, and `ρ` a probability law with `KL(ρ‖π) < ∞` (this forces
`∫ e^{-f} < ∞`). Assume the
forward regularity `HeatFlowRegularPi ρ π s` with `(0, η] ⊆ s` and the backward regularity
`BackwardHeatFlowRegularPi π (forwardKernelPi η ∘ₘ ρ) η`. Then
`KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelPi f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_sq_of_targetLSIPi (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (targetPi f) ≠ ⊤)
    {s : Set ℝ} (hreg : HeatFlowRegularPi ρ (targetPi f) s) (hs : Ioc 0 η ⊆ s)
    (hbreg : BackwardHeatFlowRegularPi (targetPi f) (forwardKernelPi η ∘ₘ ρ) η)
    (hπ : FunctionalLSIPi (targetPi f) (1 / α)) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) ^ 2 := by
  have := isProbabilityMeasure_targetPi (integrable_exp_neg_of_klDiv_targetPi_ne_top ρ hKL)
  have hpos : 0 < 1 + α * η := by positivity
  have hfwd : klDiv (forwardKernelPi η ∘ₘ ρ) (forwardKernelPi η ∘ₘ targetPi f) ≠ ⊤ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  have hF := toReal_klDiv_forwardKernelPi_le_of_targetLSIPi hη hα hKL hreg hs hπ
  obtain ⟨hfin, hB⟩ := toReal_klDiv_rgoKernelPi_comp_le_of_targetLSIPi hf hη hα
    (forwardKernelPi η ∘ₘ ρ) hfwd hbreg hπ
  rw [proxKernelPi_comp_eq]
  refine ⟨hfin, hB.trans ?_⟩
  calc (klDiv (forwardKernelPi η ∘ₘ ρ) (forwardKernelPi η ∘ₘ targetPi f)).toReal / (1 + α * η)
      ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) / (1 + α * η) :=
        div_le_div_of_nonneg_right hF hpos.le
    _ = _ := by rw [div_div, sq]

/-- **Sharp PX-2 on `Fin d → ℝ`, iterated (Conditional on the regularity hypotheses).** Let `f`
be measurable, `π = targetPi f`, `η, α > 0` with `FunctionalLSIPi π (1/α)`, and
`ρ : ℕ → Measure (Fin d → ℝ)` the proximal-sampler laws: `ρ 0` a probability law with
`KL(ρ 0‖π) < ∞` (so `∫ e^{-f} < ∞`), `ρ (k+1) = proxKernelPi f η ∘ₘ ρ k`. Assume at every step
`HeatFlowRegularPi (ρ k) π (s k)` with `(0, η] ⊆ s k` and
`BackwardHeatFlowRegularPi π (forwardKernelPi η ∘ₘ ρ k) η`. Then for every `k`, `ρ k` is a
probability law, `KL(ρ k‖π) < ∞` and `KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iteratePi_le_sq_of_targetLSIPi (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (targetPi f) ≠ ⊤)
    {s : ℕ → Set ℝ} (hreg : ∀ k, HeatFlowRegularPi (ρ k) (targetPi f) (s k))
    (hs : ∀ k, Ioc 0 η ⊆ s k)
    (hbreg : ∀ k, BackwardHeatFlowRegularPi (targetPi f) (forwardKernelPi η ∘ₘ ρ k) η)
    (hπ : FunctionalLSIPi (targetPi f) (1 / α)) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (targetPi f) ≠ ⊤ ∧
      (klDiv (ρ k) (targetPi f)).toReal
        ≤ (klDiv (ρ 0) (targetPi f)).toReal / (1 + α * η) ^ (2 * k) := by
  have := isMarkovKernel_proxKernelPi hf (integrable_exp_neg_of_klDiv_targetPi_ne_top (ρ 0) hKL)
    hη
  have hpos : 0 < 1 + α * η := by positivity
  induction k with
  | zero => exact ⟨inferInstance, hKL, by simp⟩
  | succ k ih =>
    obtain ⟨hprob, hfin, hle⟩ := ih
    have := hprob
    obtain ⟨hfin', hle'⟩ := toReal_klDiv_proxKernelPi_comp_le_sq_of_targetLSIPi hf hη hα
      (ρ k) hfin (hreg k) (hs k) (hbreg k) hπ
    rw [hstep k]
    refine ⟨inferInstance, hfin', hle'.trans ?_⟩
    rw [mul_add, mul_one, pow_add, ← div_div]
    exact div_le_div_of_nonneg_right hle (by positivity)

/-- **Sharp PX-2 on `Fin d → ℝ` in total variation (Conditional on the regularity
hypotheses).** Under the hypotheses of `toReal_klDiv_iteratePi_le_sq_of_targetLSIPi`, by
Pinsker: `tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^(2k)))` for every `k`. -/
theorem tvSupPi_iterate_le_sq_of_targetLSIPi (hf : Measurable f)
    (hη : 0 < η) {α : ℝ} (hα : 0 < α)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (targetPi f) ≠ ⊤)
    {s : ℕ → Set ℝ} (hreg : ∀ k, HeatFlowRegularPi (ρ k) (targetPi f) (s k))
    (hs : ∀ k, Ioc 0 η ⊆ s k)
    (hbreg : ∀ k, BackwardHeatFlowRegularPi (targetPi f) (forwardKernelPi η ∘ₘ ρ k) η)
    (hπ : FunctionalLSIPi (targetPi f) (1 / α)) (k : ℕ) :
    TotalVariation.tvSup (ρ k) (targetPi f)
      ≤ √((klDiv (ρ 0) (targetPi f)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨hprob, hfin, hle⟩ := toReal_klDiv_iteratePi_le_sq_of_targetLSIPi hf hη hα ρ
    hstep hKL hreg hs hbreg hπ k
  have := hprob
  have := isProbabilityMeasure_targetPi (integrable_exp_neg_of_klDiv_targetPi_ne_top (ρ 0) hKL)
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans (Real.sqrt_le_sqrt ?_)
  rw [mul_comm 2, ← div_div]
  exact div_le_div_of_nonneg_right hle zero_le_two

end Rate

end FormalizeSampling.ProximalSharpLSIPi
