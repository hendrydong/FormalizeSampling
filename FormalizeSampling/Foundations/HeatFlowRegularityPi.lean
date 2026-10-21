module

public import Mathlib.Dynamics.Flow
public import FormalizeSampling.Foundations.GaussianLSIBasicsPi

/-!
# Envelope bounds for the isotropic heat flow of a measure with finite second moment

Status: **Verified**. The `ρ`-side estimates behind the de Bruijn regularity hypotheses
`HeatFlowRegularPi ρ π (Ioi 0)` of `Foundations/HeatFlowDeBruijnPi.lean` for a probability measure
`ρ` on `Fin d → ℝ` with finite second moment `∫ ∑ᵢ xᵢ² dρ < ∞`. They are combined with a bound
on the target side in `Foundations/HeatFlowRegularityPerturbedPi.lean` (targets with a posterior
second-moment bound, among them `N(0, v I)`: `heatFlowRegularPi_gaussian` and
`klDiv_heatKernelPi_comp_ne_top_of_moment`, stated there in this namespace) and
`Samplers/HeatFlowRegularityWarmPi.lean` (warm starts).

Notation: `|z|² = ∑ᵢ zᵢ²`, `φ_r = heatDensityPi r = gc d r · exp(-|z|²/(2r))` with
`gc d r = (2π r)^{-d/2}`, and `p_r = heatFlowDensityPi ρ r = ρ * φ_r`.

Method (crude bounds): for `0 < a ≤ r ≤ b`,
* `(1 + |z|²)² φ_r(z) ≤ K φ_{2b}(z)` (`envelope`) and `1 + |y|² ≤ 2 (1 + |y - x|²)(1 + |x|²)`, so
  `(1 + |y|²) ∫ g(y - x) dρ(x) ≤ 2 A K E_{2b}(y)` whenever `0 ≤ g ≤ A (1 + |·|²) φ_r`
  (`one_add_mul_integral_le`), where `E_c(y) = ∫ (1 + |x|²) φ_c(y - x) dρ(x)` is Lebesgue
  integrable by Tonelli (`integrable_envBound`);
* this bounds `(1 + |y|²)` times `p_r`, `|∂ᵢp_r|`, `|∂ᵢ²p_r|`, `|Δp_r|`, and (by Cauchy–Schwarz)
  `(∂ᵢp_r)² / p_r`;
* `|log p_r(y)| ≤ |log gc d r| + (|y|² + ∫ |x|² dρ) / r` (upper bound `p_r ≤ gc d r`, lower bound
  by Jensen).

## Main results

* `envelope`, `integrable_envBound`, `one_add_mul_integral_le`: the integrable envelope.
* `one_add_mul_heatFlowDensityPi_le`, `one_add_mul_abs_heatFlowGradPi_le`,
  `one_add_mul_abs_heatFlowHessPi_le`, `one_add_mul_abs_lap_le`,
  `sq_heatFlowGradPi_div_le` (Cauchy–Schwarz), `sq_heatFlowGradPi_div_le_envBound`: pointwise
  bounds by `C E_{2b}`.
* `abs_log_heatFlowDensityPi_le` (Jensen), `abs_log_heatDensityPi_le`.
* Gaussian side: `heatFlowHessPi_gaussian` (`∂ᵢ∂ⱼq_t = ∂ᵢ∂ⱼφ_{v+t}` for `π = N(0, v I)`),
  `heatGradPi_div`; and `continuous_heatFlowHessPi`.

## Not proved here

* The fields of `HeatFlowRegularPi` themselves; they need a bound on the target side:
  `Foundations/HeatFlowRegularityPerturbedPi.lean`, `Samplers/HeatFlowRegularityWarmPi.lean`.
* Bounds without a finite second moment of `ρ`, or at time `t = 0`.
* The one-dimensional analogue (treated separately, not in this file).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.HeatFlowRegularityPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi

variable {d : ℕ}

/-! ### Elementary inequalities -/

/-- `0 ≤ ∑ᵢ zᵢ²`. -/
theorem sum_sq_nonneg (z : Fin d → ℝ) : 0 ≤ ∑ i, z i ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `zᵢ² ≤ ∑ⱼ zⱼ²`. -/
theorem sq_le_sum_sq (z : Fin d → ℝ) (i : Fin d) : z i ^ 2 ≤ ∑ j, z j ^ 2 :=
  Finset.single_le_sum (f := fun j => z j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- `|zᵢ| ≤ 1 + ∑ⱼ zⱼ²`. -/
theorem abs_le_one_add_sum_sq (z : Fin d → ℝ) (i : Fin d) : |z i| ≤ 1 + ∑ j, z j ^ 2 := by
  have := sq_le_sum_sq z i
  nlinarith [sq_abs (z i), abs_nonneg (z i), sq_nonneg (|z i| - 1)]

/-- `∑ᵢ (yᵢ - xᵢ)² ≤ 2 ∑ᵢ yᵢ² + 2 ∑ᵢ xᵢ²`. -/
theorem sum_sq_sub_le (y x : Fin d → ℝ) :
    ∑ i, (y - x) i ^ 2 ≤ 2 * ∑ i, y i ^ 2 + 2 * ∑ i, x i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simp only [Pi.sub_apply]; nlinarith [sq_nonneg (y i + x i)]

/-- `1 + |y|² ≤ 2 (1 + |y - x|²)(1 + |x|²)`. -/
theorem one_add_sum_sq_le (y x : Fin d → ℝ) :
    1 + ∑ i, y i ^ 2 ≤ 2 * (1 + ∑ i, (y - x) i ^ 2) * (1 + ∑ i, x i ^ 2) := by
  have h : ∑ i, y i ^ 2 ≤ 2 * ∑ i, (y - x) i ^ 2 + 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      simp only [Pi.sub_apply]; nlinarith [sq_nonneg (y i - x i - x i)]
  nlinarith [sum_sq_nonneg (y - x), sum_sq_nonneg x,
    mul_nonneg (sum_sq_nonneg (y - x)) (sum_sq_nonneg x)]

/-- The normalising constant `(2π t)^{-d/2}` of `heatDensityPi t`. -/
noncomputable def gc (d : ℕ) (t : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d

/-- `gc d t > 0` for `t > 0`. -/
theorem gc_pos {t : ℝ} (ht : 0 < t) : 0 < gc d t := by unfold gc; positivity

/-- `gc d` is antitone on `(0, ∞)`. -/
theorem gc_anti {a r : ℝ} (ha : 0 < a) (har : a ≤ r) : gc d r ≤ gc d a := by
  unfold gc
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))) d

/-- `heatDensityPi t z = gc d t · exp(-|z|² / (2t))`. -/
theorem heatDensityPi_eq (t : ℝ) (z : Fin d → ℝ) :
    heatDensityPi t z = gc d t * Real.exp (-(∑ i, z i ^ 2) / (2 * t)) :=
  heatDensityPi_eq_exp t z

/-- `|log (gc d r)| ≤ d (|log (2π a)| + |log (2π b)|)` for `0 < a ≤ r ≤ b`. -/
theorem abs_log_gc_le {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) :
    |Real.log (gc d r)| ≤ d * (|Real.log (2 * Real.pi * a)| + |Real.log (2 * Real.pi * b)|) := by
  have hr : 0 < r := ha.trans_le har
  have e : Real.log (gc d r) = -(d / 2 * Real.log (2 * Real.pi * r)) := by
    unfold gc
    rw [Real.log_pow, Real.log_inv, Real.log_sqrt (by positivity)]
    ring
  have h1 : Real.log (2 * Real.pi * a) ≤ Real.log (2 * Real.pi * r) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.pi_pos])
  have h2 : Real.log (2 * Real.pi * r) ≤ Real.log (2 * Real.pi * b) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.pi_pos])
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d / 2)]
  have : |Real.log (2 * Real.pi * r)| ≤
      |Real.log (2 * Real.pi * a)| + |Real.log (2 * Real.pi * b)| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log (2 * Real.pi * a)), abs_nonneg (Real.log (2 * Real.pi * b))]
    · linarith [le_abs_self (Real.log (2 * Real.pi * b)), abs_nonneg (Real.log (2 * Real.pi * a))]
  have h0 : 0 ≤ |Real.log (2 * Real.pi * a)| + |Real.log (2 * Real.pi * b)| := by positivity
  nlinarith

/-- **Gaussian envelope.** For `0 < a ≤ r ≤ b` and every `z`,
`(1 + |z|²)² φ_r(z) ≤ K φ_{2b}(z)` with `K = gc d a (1 + 8b)² / gc d (2b)`. -/
theorem envelope {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (z : Fin d → ℝ) :
    (1 + ∑ i, z i ^ 2) ^ 2 * heatDensityPi r z ≤
      gc d a * (1 + 8 * b) ^ 2 / gc d (2 * b) * heatDensityPi (2 * b) z := by
  have hr : 0 < r := ha.trans_le har
  have hb : 0 < b := hr.trans_le hrb
  rw [heatDensityPi_eq, heatDensityPi_eq]
  set u := ∑ i, z i ^ 2
  have hu : 0 ≤ u := sum_sq_nonneg z
  have hga := gc_anti (d := d) ha har
  have hg2 : 0 < gc d (2 * b) := gc_pos (by linarith)
  have hgr : 0 < gc d r := gc_pos hr
  have hga0 : 0 < gc d a := gc_pos ha
  have hE1 : Real.exp (-u / (2 * r)) ≤ Real.exp (-u / (2 * b)) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hu (by positivity) (by linarith)
  set e := Real.exp (-u / (2 * (4 * b)))
  have he1 : e ≤ 1 := exp_neg_le_one (by positivity) hu
  have he0 : 0 < e := Real.exp_pos _
  have hue : u * e ≤ 2 * (4 * b) := mul_exp_neg_le (by positivity) hu
  have hsplit : Real.exp (-u / (2 * b)) = e ^ 2 * Real.exp (-u / (2 * (2 * b))) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
  have hk : (1 + u) * e ≤ 1 + 8 * b := by nlinarith
  have hk2 : (1 + u) ^ 2 * e ^ 2 ≤ (1 + 8 * b) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hk 2
  have hE2 := Real.exp_pos (-u / (2 * (2 * b)))
  calc (1 + u) ^ 2 * (gc d r * Real.exp (-u / (2 * r)))
      ≤ (1 + u) ^ 2 * (gc d a * (e ^ 2 * Real.exp (-u / (2 * (2 * b))))) := by
        rw [← hsplit]; gcongr
    _ = gc d a * ((1 + u) ^ 2 * e ^ 2) * Real.exp (-u / (2 * (2 * b))) := by ring
    _ ≤ gc d a * (1 + 8 * b) ^ 2 * Real.exp (-u / (2 * (2 * b))) := by
        gcongr
    _ = _ := by generalize gc d (2 * b) = g at hg2 ⊢; field_simp

/-- The constant `K = gc d a (1 + 8b)² / gc d (2b)` of `envelope`. -/
noncomputable def envK (d : ℕ) (a b : ℝ) : ℝ := gc d a * (1 + 8 * b) ^ 2 / gc d (2 * b)

/-- `envK d a b ≥ 0` for `0 < a`, `0 < b`. -/
theorem envK_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ envK d a b := by
  unfold envK; have := gc_pos (d := d) ha; have := gc_pos (d := d) (by linarith : 0 < 2 * b)
  positivity

/-- A continuous function `k` bounded by `B` gives `x ↦ k (y - x)` integrable under a finite
measure. -/
theorem integrable_comp_sub_of_bound (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ]
    {k : (Fin d → ℝ) → ℝ} (hk : Continuous k) {B : ℝ} (hB : ∀ z, |k z| ≤ B) (y : Fin d → ℝ) :
    Integrable (fun x => k (y - x)) ρ :=
  Integrable.of_bound (hk.comp (by fun_prop)).aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB _)

/-! ### The integrable envelope -/

/-- The envelope `E_c(y) = ∫ (1 + |x|²) φ_c(y - x) dρ(x)`, which dominates all the heat-flow
integrands (`one_add_mul_integral_le`). -/
noncomputable def envBound (ρ : Measure (Fin d → ℝ)) (c : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ x, (1 + ∑ i, x i ^ 2) * heatDensityPi c (y - x) ∂ρ

section Envelope

variable {ρ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ]

/-- For `∫ |x|² dρ < ∞` and `c > 0`, `x ↦ (1 + |x|²) φ_c(y - x)` is `ρ`-integrable. -/
theorem integrable_envBound_integrand (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {c : ℝ}
    (hc : 0 < c) (y : Fin d → ℝ) :
    Integrable (fun x => (1 + ∑ i, x i ^ 2) * heatDensityPi c (y - x)) ρ := by
  have hφc := continuous_heatDensityPi (d := d) c
  refine (((integrable_const (1 : ℝ)).add hmom).mul_const (gc d c)).mono'
    (by fun_prop : Continuous fun x : Fin d → ℝ =>
      (1 + ∑ i, x i ^ 2) * heatDensityPi c (y - x)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  have h1 : 0 ≤ 1 + ∑ i, x i ^ 2 := by linarith [sum_sq_nonneg x]
  rw [Real.norm_of_nonneg (mul_nonneg h1 (heatDensityPi_pos hc _).le)]
  exact mul_le_mul_of_nonneg_left (heatDensityPi_le hc _) h1

/-- **The envelope is Lebesgue integrable** (Tonelli): for `∫ |x|² dρ < ∞` and `c > 0`,
`y ↦ ∫ (1 + |x|²) φ_c(y - x) dρ(x)` is integrable. -/
theorem integrable_envBound (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {c : ℝ}
    (hc : 0 < c) : Integrable (envBound ρ c) := by
  set f : (Fin d → ℝ) × (Fin d → ℝ) → ℝ :=
    fun q => (1 + ∑ i, q.1 i ^ 2) * heatDensityPi c (q.2 - q.1)
  have hφc := continuous_heatDensityPi (d := d) c
  have hfc : Continuous f := by fun_prop
  have hf : Integrable f (ρ.prod volume) := by
    refine (integrable_prod_iff hfc.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x =>
      (integrable_heatDensityPi_sub hc x).1.const_mul (1 + ∑ i, x i ^ 2), ?_⟩
    have e : (fun x => ∫ y, ‖f (x, y)‖) = fun x => 1 + ∑ i, x i ^ 2 := by
      funext x
      have h1 : 0 ≤ 1 + ∑ i, x i ^ 2 := by linarith [sum_sq_nonneg x]
      simp_rw [f, Real.norm_of_nonneg (mul_nonneg h1 (heatDensityPi_pos hc _).le)]
      rw [integral_const_mul, (integrable_heatDensityPi_sub hc x).2, mul_one]
    rw [e]; exact (integrable_const _).add hmom
  exact hf.integral_prod_right

/-- **Master domination.** For `0 < a ≤ r ≤ b`, `A ≥ 0`, `y`, and `0 ≤ g(x) ≤ A (1 + |y - x|²)
φ_r(y - x)`: `(1 + |y|²) ∫ g dρ ≤ 2 A K E_{2b}(y)` with `K = envK d a b`. -/
theorem one_add_mul_integral_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b r A : ℝ}
    (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (hA : 0 ≤ A) (y : Fin d → ℝ)
    {g : (Fin d → ℝ) → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : ∀ x, g x ≤ A * (1 + ∑ i, (y - x) i ^ 2) * heatDensityPi r (y - x)) :
    (1 + ∑ i, y i ^ 2) * ∫ x, g x ∂ρ ≤ 2 * A * envK d a b * envBound ρ (2 * b) y := by
  have hb : 0 < b := by linarith
  rw [← integral_const_mul, envBound, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
      mul_nonneg (by linarith [sum_sq_nonneg y]) (hg0 x))
    ((integrable_envBound_integrand hmom (by linarith) y).const_mul _)
    (Eventually.of_forall fun x => ?_)
  have h1 := one_add_sum_sq_le y x
  have h2 := envelope (d := d) ha har hrb (y - x)
  have hr : 0 < r := by linarith
  have hφ := (heatDensityPi_pos hr (y - x)).le
  have hz := sum_sq_nonneg (y - x)
  have hx := sum_sq_nonneg x
  have hK := envK_nonneg (d := d) ha hb
  unfold envK at hK
  calc (1 + ∑ i, y i ^ 2) * g x
      ≤ (2 * (1 + ∑ i, (y - x) i ^ 2) * (1 + ∑ i, x i ^ 2)) *
          (A * (1 + ∑ i, (y - x) i ^ 2) * heatDensityPi r (y - x)) :=
        mul_le_mul h1 (hg x) (hg0 x) (by positivity)
    _ = 2 * A * (1 + ∑ i, x i ^ 2) *
          ((1 + ∑ i, (y - x) i ^ 2) ^ 2 * heatDensityPi r (y - x)) := by ring
    _ ≤ 2 * A * (1 + ∑ i, x i ^ 2) *
          (gc d a * (1 + 8 * b) ^ 2 / gc d (2 * b) * heatDensityPi (2 * b) (y - x)) := by
        gcongr
    _ = 2 * A * envK d a b * ((1 + ∑ i, x i ^ 2) * heatDensityPi (2 * b) (y - x)) := by
        unfold envK; ring

end Envelope

/-! ### Weighted Cauchy–Schwarz against `ρ` -/

/-- For `w ≥ 0` with `w`, `α w`, `α² w` integrable and `∫ w > 0`:
`(∫ α w)² / ∫ w ≤ ∫ α² w`. -/
theorem sq_integral_div_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {w α : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) (h1 : Integrable w μ) (h2 : Integrable (fun x => α x * w x) μ)
    (h3 : Integrable (fun x => α x ^ 2 * w x) μ) (hC : 0 < ∫ x, w x ∂μ) :
    (∫ x, α x * w x ∂μ) ^ 2 / ∫ x, w x ∂μ ≤ ∫ x, α x ^ 2 * w x ∂μ := by
  set A := ∫ x, α x ^ 2 * w x ∂μ
  set B := ∫ x, α x * w x ∂μ
  set C := ∫ x, w x ∂μ
  set m := B / C
  have hpt : ∀ x, (α x - m) ^ 2 * w x = α x ^ 2 * w x - 2 * m * (α x * w x) + m ^ 2 * w x :=
    fun x => by ring
  have h0 : 0 ≤ ∫ x, (α x - m) ^ 2 * w x ∂μ :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)
  simp_rw [hpt] at h0
  rw [integral_add (by exact h3.sub (h2.const_mul (2 * m))) (h1.const_mul _),
    integral_sub h3 (h2.const_mul _), integral_const_mul, integral_const_mul] at h0
  have hm : m * C = B := div_mul_cancel₀ B hC.ne'
  rw [div_le_iff₀ hC]
  nlinarith

/-! ### Pointwise bounds on the heat flow of `ρ` -/

section Flow

variable {ρ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ]

/-- For `t > 0`, `y ↦ ∂ᵢ∂ⱼ p_t(y)` is continuous. -/
theorem continuous_heatFlowHessPi {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    Continuous fun y => heatFlowHessPi ρ t y i j := by
  unfold heatFlowHessPi
  have hc := continuous_heatHessPi (d := d) t i j
  exact continuous_of_dominated (bound := fun _ => 3 / t * gc d t)
    (fun y => (hc.comp (by fun_prop : Continuous fun x : Fin d → ℝ => y - x)).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_heatHessPi_le ht _ i j)
    (integrable_const _)
    (Eventually.of_forall fun x => hc.comp (by fun_prop))

/-- `(1 + |y|²) p_r(y) ≤ 2 K E_{2b}(y)` for `0 < a ≤ r ≤ b`. -/
theorem one_add_mul_heatFlowDensityPi_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (y : Fin d → ℝ) :
    (1 + ∑ i, y i ^ 2) * heatFlowDensityPi ρ r y ≤ 2 * 1 * envK d a b * envBound ρ (2 * b) y := by
  have hr : 0 < r := by linarith
  refine one_add_mul_integral_le hmom ha har hrb zero_le_one y
    (fun x => (heatDensityPi_pos hr _).le) fun x => ?_
  have := (heatDensityPi_pos hr (y - x)).le
  nlinarith [sum_sq_nonneg (y - x)]

/-- `(1 + |y|²) |∂ᵢ p_r(y)| ≤ 2 a⁻¹ K E_{2b}(y)` for `0 < a ≤ r ≤ b`. -/
theorem one_add_mul_abs_heatFlowGradPi_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (y : Fin d → ℝ) (i : Fin d) :
    (1 + ∑ i, y i ^ 2) * |heatFlowGradPi ρ r y i| ≤
      2 * a⁻¹ * envK d a b * envBound ρ (2 * b) y := by
  have hr : 0 < r := by linarith
  refine (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
    (by linarith [sum_sq_nonneg y])).trans ?_
  refine one_add_mul_integral_le hmom ha har hrb (by positivity) y
    (fun x => abs_nonneg _) fun x => ?_
  set z := y - x
  have hφ := (heatDensityPi_pos hr z).le
  have hzi := abs_le_one_add_sum_sq z i
  rw [heatGradPi, abs_mul, abs_neg, abs_div, abs_of_pos hr, abs_of_nonneg hφ]
  have h1 : |z i| / r ≤ a⁻¹ * (1 + ∑ i, z i ^ 2) := by
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul (inv_anti₀ ha har) hzi (abs_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_right h1 hφ

/-- `(1 + |y|²) |∂ᵢ² p_r(y)| ≤ 2 (a⁻² + a⁻¹) K E_{2b}(y)` for `0 < a ≤ r ≤ b`. -/
theorem one_add_mul_abs_heatFlowHessPi_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (y : Fin d → ℝ) (i : Fin d) :
    (1 + ∑ i, y i ^ 2) * |heatFlowHessPi ρ r y i i| ≤
      2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b * envBound ρ (2 * b) y := by
  have hr : 0 < r := by linarith
  refine (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
    (by linarith [sum_sq_nonneg y])).trans ?_
  refine one_add_mul_integral_le hmom ha har hrb (by positivity) y
    (fun x => abs_nonneg _) fun x => ?_
  set z := y - x
  have hφ := (heatDensityPi_pos hr z).le
  have hzi := sq_le_sum_sq z i
  have hS := sum_sq_nonneg z
  simp only [heatHessPi, ↓reduceIte]
  rw [abs_mul, abs_of_nonneg hφ]
  have hinv : r⁻¹ ≤ a⁻¹ := inv_anti₀ ha har
  have hinv2 : r⁻¹ ^ 2 ≤ a⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2
  have h1 : |z i * z i / r ^ 2 - 1 / r| ≤ (a⁻¹ ^ 2 + a⁻¹) * (1 + ∑ i, z i ^ 2) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2), abs_of_pos (by positivity :
      (0 : ℝ) < 1 / r), abs_mul_self, ← sq, div_eq_mul_inv, ← inv_pow, one_div]
    have : z i ^ 2 * r⁻¹ ^ 2 ≤ (∑ i, z i ^ 2) * a⁻¹ ^ 2 :=
      mul_le_mul hzi hinv2 (by positivity) hS
    nlinarith [inv_pos.2 ha]
  exact mul_le_mul_of_nonneg_right h1 hφ

/-- **Score bound by Cauchy–Schwarz.** For `r > 0`:
`(∂ᵢ p_r(y))² / p_r(y) ≤ ∫ ((y - x)ᵢ / r)² φ_r(y - x) dρ(x)`. -/
theorem sq_heatFlowGradPi_div_le {r : ℝ} (hr : 0 < r) (y : Fin d → ℝ) (i : Fin d) :
    heatFlowGradPi ρ r y i ^ 2 / heatFlowDensityPi ρ r y ≤
      ∫ x, ((y - x) i / r) ^ 2 * heatDensityPi r (y - x) ∂ρ := by
  have hφc := continuous_heatDensityPi (d := d) r
  have hw : Integrable (fun x => heatDensityPi r (y - x)) ρ :=
    integrable_comp_sub_of_bound ρ hφc (B := gc d r)
      (fun z => by rw [abs_of_pos (heatDensityPi_pos hr z)]; exact heatDensityPi_le hr z) y
  have h2 : Integrable (fun x => -((y - x) i / r) * heatDensityPi r (y - x)) ρ :=
    integrable_comp_sub_of_bound ρ (k := fun z => heatGradPi r z i)
      ((continuous_apply i).comp (continuous_heatGradPi r)) (abs_heatGradPi_le hr · i) y
  have h3 : Integrable (fun x => (-((y - x) i / r)) ^ 2 * heatDensityPi r (y - x)) ρ := by
    refine integrable_comp_sub_of_bound ρ (k := fun z => (-(z i / r)) ^ 2 * heatDensityPi r z)
      (by fun_prop) (B := 2 * r / r ^ 2 * gc d r) (fun z => ?_) y
    have hS := sum_sq_nonneg z
    have hE := mul_exp_neg_le hr hS
    have hg := gc_pos (d := d) hr
    have hzi := sq_le_sum_sq z i
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (heatDensityPi_pos hr z).le), heatDensityPi_eq,
      neg_sq, div_pow]
    have hE0 := Real.exp_pos (-(∑ i, z i ^ 2) / (2 * r))
    calc z i ^ 2 / r ^ 2 * (gc d r * Real.exp (-(∑ i, z i ^ 2) / (2 * r)))
        = (z i ^ 2 * Real.exp (-(∑ i, z i ^ 2) / (2 * r))) / r ^ 2 * gc d r := by ring
      _ ≤ ((∑ i, z i ^ 2) * Real.exp (-(∑ i, z i ^ 2) / (2 * r))) / r ^ 2 * gc d r := by
          gcongr
      _ ≤ 2 * r / r ^ 2 * gc d r := by gcongr
  have h := sq_integral_div_le (μ := ρ) (w := fun x => heatDensityPi r (y - x))
    (α := fun x => -((y - x) i / r)) (fun x => (heatDensityPi_pos hr _).le) hw h2 h3
    (heatFlowDensityPi_pos ρ hr y)
  have e : heatFlowGradPi ρ r y i = ∫ x, -((y - x) i / r) * heatDensityPi r (y - x) ∂ρ := rfl
  rw [e, heatFlowDensityPi]
  simpa only [neg_sq] using h

/-- `(∂ᵢ p_r(y))² / p_r(y) ≤ 2 a⁻² K E_{2b}(y)` for `0 < a ≤ r ≤ b`. -/
theorem sq_heatFlowGradPi_div_le_envBound (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (y : Fin d → ℝ) (i : Fin d) :
    heatFlowGradPi ρ r y i ^ 2 / heatFlowDensityPi ρ r y ≤
      2 * a⁻¹ ^ 2 * envK d a b * envBound ρ (2 * b) y := by
  have hr : 0 < r := by linarith
  have hI : 0 ≤ ∫ x, ((y - x) i / r) ^ 2 * heatDensityPi r (y - x) ∂ρ :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (heatDensityPi_pos hr _).le
  refine (sq_heatFlowGradPi_div_le hr y i).trans ?_
  refine le_trans (le_mul_of_one_le_left hI
    (show (1 : ℝ) ≤ 1 + ∑ i, y i ^ 2 by linarith [sum_sq_nonneg y])) ?_
  refine one_add_mul_integral_le hmom ha har hrb (by positivity) y
    (fun x => mul_nonneg (sq_nonneg _) (heatDensityPi_pos hr _).le) fun x => ?_
  set z := y - x
  have hφ := (heatDensityPi_pos hr z).le
  have hzi := sq_le_sum_sq z i
  have hinv2 : r⁻¹ ^ 2 ≤ a⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) (inv_anti₀ ha har) 2
  have h1 : (z i / r) ^ 2 ≤ a⁻¹ ^ 2 * (1 + ∑ i, z i ^ 2) := by
    rw [div_pow, div_eq_mul_inv, ← inv_pow, mul_comm]
    exact mul_le_mul hinv2 (by linarith) (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_right h1 hφ

end Flow

/-! ### Logarithmic bounds -/

section Log

variable {ρ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ]

/-- **Two-sided bound on `log p_r` (Jensen).** For `∫ |x|² dρ < ∞`, `r > 0` and every `y`,
`|log p_r(y)| ≤ |log gc d r| + (|y|² + ∫ |x|² dρ) / r`: the upper bound is `p_r ≤ gc d r`, the
lower bound is Jensen's inequality `exp(∫ f dρ) ≤ ∫ exp f dρ` for `f(x) = -|y - x|² / (2r)`. -/
theorem abs_log_heatFlowDensityPi_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {r : ℝ}
    (hr : 0 < r) (y : Fin d → ℝ) :
    |Real.log (heatFlowDensityPi ρ r y)| ≤
      |Real.log (gc d r)| + (∑ i, y i ^ 2 + ∫ x, ∑ i, x i ^ 2 ∂ρ) / r := by
  set M := ∫ x, ∑ i, x i ^ 2 ∂ρ
  set f : (Fin d → ℝ) → ℝ := fun x => -(∑ i, (y - x) i ^ 2) / (2 * r) with hf
  have hP := heatFlowDensityPi_pos ρ hr y
  have hg := gc_pos (d := d) hr
  have hfc : Continuous f := by fun_prop
  have hSi : Integrable (fun x => ∑ i, (y - x) i ^ 2) ρ := by
    refine ((integrable_const (2 * ∑ i, y i ^ 2)).add (hmom.const_mul 2)).mono'
      (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sum_sq_nonneg _)]
    exact sum_sq_sub_le y x
  have hfi : Integrable f ρ := (hSi.neg.div_const (2 * r)).congr
    (Eventually.of_forall fun x => by simp [hf, neg_div])
  have hexp : Integrable (Real.exp ∘ f) ρ :=
    Integrable.of_bound (Real.continuous_exp.comp hfc).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact exp_neg_le_one hr (sum_sq_nonneg _))
  have hJ := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (Eventually.of_forall fun x => mem_univ (f x)) hfi hexp
  have hPe : heatFlowDensityPi ρ r y = gc d r * ∫ x, Real.exp (f x) ∂ρ := by
    unfold heatFlowDensityPi; simp_rw [heatDensityPi_eq]; rw [integral_const_mul]
  have hI : 0 < ∫ x, Real.exp (f x) ∂ρ := by
    rw [hPe] at hP; exact pos_of_mul_pos_right hP hg.le
  have hM : 0 ≤ M := integral_nonneg fun x => sum_sq_nonneg x
  have hfint : -(∑ i, y i ^ 2 + M) / r ≤ ∫ x, f x ∂ρ := by
    have h1 : ∫ x, f x ∂ρ = -(∫ x, ∑ i, (y - x) i ^ 2 ∂ρ) / (2 * r) := by
      rw [hf, integral_div, integral_neg]
    have h2 : ∫ x, ∑ i, (y - x) i ^ 2 ∂ρ ≤ 2 * ∑ i, y i ^ 2 + 2 * M := by
      calc ∫ x, ∑ i, (y - x) i ^ 2 ∂ρ ≤ ∫ x, (2 * ∑ i, y i ^ 2 + 2 * ∑ i, x i ^ 2) ∂ρ :=
            integral_mono hSi ((integrable_const _).add (hmom.const_mul 2))
              fun x => sum_sq_sub_le y x
        _ = _ := by rw [integral_add (integrable_const _) (hmom.const_mul 2),
            integral_const_mul]; simp [M, integral_const_mul]
    rw [h1, div_le_div_iff₀ hr (by positivity)]
    nlinarith
  have hlow : Real.log (gc d r) - (∑ i, y i ^ 2 + M) / r ≤ Real.log (heatFlowDensityPi ρ r y) := by
    rw [hPe, Real.log_mul hg.ne' hI.ne']
    have : ∫ x, f x ∂ρ ≤ Real.log (∫ x, Real.exp (f x) ∂ρ) := by
      rw [← Real.exp_le_exp, Real.exp_log hI]; exact hJ
    rw [neg_div] at hfint
    linarith
  have hup : Real.log (heatFlowDensityPi ρ r y) ≤ Real.log (gc d r) :=
    Real.log_le_log hP (heatFlowDensityPi_le ρ hr y)
  have hq : 0 ≤ (∑ i, y i ^ 2 + M) / r := div_nonneg (by linarith [sum_sq_nonneg y]) hr.le
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log (gc d r)), le_abs_self (Real.log (gc d r))]

/-- `|log φ_c(y)| ≤ |log gc d c| + |y|² / (2c)` for `c > 0`. -/
theorem abs_log_heatDensityPi_le {c : ℝ} (hc : 0 < c) (y : Fin d → ℝ) :
    |Real.log (heatDensityPi c y)| ≤ |Real.log (gc d c)| + (∑ i, y i ^ 2) / (2 * c) := by
  rw [heatDensityPi_eq, Real.log_mul (gc_pos hc).ne' (Real.exp_pos _).ne', Real.log_exp]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_neg, abs_of_nonneg (sum_sq_nonneg y), abs_of_pos (by positivity : 0 < 2 * c)]

end Log

/-! ### The Gaussian side -/

/-- The isotropic Gaussian `N(0, v I) = ⊗ᵢ N(0, v)` on `Fin d → ℝ`. -/
noncomputable abbrev gaussPi (d : ℕ) (v : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal

/-- For `v, t > 0`, `heatFlowHessPi N(0, v I) t = heatHessPi (v + t)`. -/
theorem heatFlowHessPi_gaussian {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    heatFlowHessPi (gaussPi d v) t = heatHessPi (v + t) := by
  funext y i j
  have h1 := hasFDerivAt_heatFlowGradPi (gaussPi d v) ht i y
  rw [heatFlowGradPi_gaussian hv ht] at h1
  have h2 := congrArg (fun L => L (Pi.single j 1)) (h1.unique (hasFDerivAt_heatGradPi _ i y))
  simpa only [dotCLM_single] using h2

/-- `∂ᵢφ_c(y) / φ_c(y) = -yᵢ / c`. -/
theorem heatGradPi_div {c : ℝ} (hc : 0 < c) (y : Fin d → ℝ) (i : Fin d) :
    heatGradPi c y i / heatDensityPi c y = -(y i / c) := by
  rw [heatGradPi, mul_div_assoc, div_self (heatDensityPi_pos hc y).ne', mul_one]

/-! ### Nonnegativity of the envelope and the Laplacian bound -/

section Integrands

variable {ρ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ρ] in
/-- `E_c(y) ≥ 0`. -/
theorem envBound_nonneg {c : ℝ} (hc : 0 < c) (y : Fin d → ℝ) : 0 ≤ envBound ρ c y :=
  integral_nonneg fun x => mul_nonneg (by linarith [sum_sq_nonneg x])
    (heatDensityPi_pos hc _).le

/-- `(1 + |y|²) |Δp_r(y)| ≤ d · 2 (a⁻² + a⁻¹) K E_{2b}(y)` for `0 < a ≤ r ≤ b`. -/
theorem one_add_mul_abs_lap_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (y : Fin d → ℝ) :
    (1 + ∑ i, y i ^ 2) * |∑ i, heatFlowHessPi ρ r y i i| ≤
      d * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b * envBound ρ (2 * b) y) := by
  have h1 : 0 ≤ 1 + ∑ i, y i ^ 2 := by linarith [sum_sq_nonneg y]
  calc (1 + ∑ i, y i ^ 2) * |∑ i, heatFlowHessPi ρ r y i i|
      ≤ (1 + ∑ i, y i ^ 2) * ∑ i, |heatFlowHessPi ρ r y i i| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) h1
    _ = ∑ i, (1 + ∑ i, y i ^ 2) * |heatFlowHessPi ρ r y i i| := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin d, 2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b * envBound ρ (2 * b) y :=
        Finset.sum_le_sum fun i _ => one_add_mul_abs_heatFlowHessPi_le hmom ha har hrb y i
    _ = _ := by simp

end Integrands

end FormalizeSampling.HeatFlowRegularityPi
