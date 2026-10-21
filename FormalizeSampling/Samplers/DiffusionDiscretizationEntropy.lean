module

public import FormalizeSampling.Samplers.DiffusionDiscretizationFisher
public import FormalizeSampling.Samplers.DiffusionDiscretizationSum

/-!
# Entropy production along the heat flow and the discretisation bound (heat-flow coordinates)

Status: **Verified** for every probability measure `ρ` on `Fin d → ℝ` with finite second moment
`M = ∫ |x|² dρ` (no density of `ρ` is assumed).

Notation: `p_t = heatFlowDensityPi ρ t` (density of `ρ * N(0, t I)`, `t > 0`),
`H(t) = heatNegEntropy ρ t = ∫ p_t log p_t` (negative differential entropy),
`J(t) = heatFisherInfo ρ t = ∫ |∇p_t|² / p_t` (Fisher information).

This file is the analytic core ("Theorem B") of the `d`-linear bound on the discretisation
error of DDPM-type samplers. In heat-flow coordinates the exact per-step error of the Gaussian
reverse step is `H(u_k) - H(u_{k+1}) - ½ (u_{k+1} - u_k) J(u_{k+1})` (Theorem A,
`Samplers/DiffusionDiscretizationStep.lean`); this file bounds the sum of these quantities.

## Main results

* `integral_heatFlowDensityPi_mul_sumSq`: `∫ p_t |y|² = M + d t`.
* `integral_mul_heatFlowGradPi`: Stein's identity `∫ yᵢ ∂ᵢp_t(y) dy = -1`.
* `heatFisher_gaussian_eq`: the relative Fisher information against `N(0, (v + t) I)` is
  `J(t) - 2d/(v + t) + (M + d t)/(v + t)²`.
* `heatKL_gaussian_eq`: `KL(ρ_t‖N(0,(v+t)I)) = H(t) - log((2π(v+t))^{-d/2}) + (M + d t)/(2(v+t))`.
* `hasDerivAt_heatNegEntropy` (de Bruijn): `H'(t) = -J(t)/2` for `t > 0`.
* `heatFisherInfo_anti`: `J` is non-increasing on `(0, ∞)`.
* `heatNegEntropy_sub_le`, `le_heatNegEntropy_sub`:
  `½ (b - a) J(b) ≤ H(a) - H(b) ≤ ½ (b - a) J(a)` for `0 < a ≤ b`.
* `sum_entropyStep_le` (**Theorem B**): for a grid `0 < u_0 ≤ u_1 ≤ … ≤ u_n` with
  `u_{k+1} - u_k ≤ κ u_k`,
  `∑_{k<n} (H(u_k) - H(u_{k+1}) - ½ (u_{k+1} - u_k) J(u_{k+1})) ≤ (κ d / 2)(1 + log(u_n/u_0))`.
* `entropyStep_nonneg`: each summand is nonnegative.

## Not proved here

* Theorem A (the per-step identity relating the summand to the averaged KL between the exact
  reverse kernel and its Gaussian approximation) and the translation from heat-flow to OU
  coordinates; these are in `Samplers/DiffusionDiscretizationStep.lean` and
  `Samplers/DiffusionMain.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi FormalizeSampling.GaussianLSIPi
  FormalizeSampling.GaussianFunctionalLSIPi

variable {d : ℕ}

/-- The second moment `∫ |x|² dρ = ∫ ∑ᵢ xᵢ² dρ` of a measure on `Fin d → ℝ`. -/
noncomputable def secondMoment (ρ : Measure (Fin d → ℝ)) : ℝ := ∫ x, ∑ i, x i ^ 2 ∂ρ

/-- The negative differential entropy of the heat flow,
`heatNegEntropy ρ t = ∫ p_t log p_t` with `p_t = heatFlowDensityPi ρ t`. -/
noncomputable def heatNegEntropy (ρ : Measure (Fin d → ℝ)) (t : ℝ) : ℝ :=
  ∫ y, heatFlowDensityPi ρ t y * Real.log (heatFlowDensityPi ρ t y)

/-! ### Gaussian quadratic integrands -/

/-- For `t > 0`, `z ↦ φ_t(z) zᵢ²` is Lebesgue integrable. -/
theorem integrable_heatDensityPi_mul_sq {t : ℝ} (ht : 0 < t) (i : Fin d) :
    Integrable fun z : Fin d → ℝ => heatDensityPi t z * z i ^ 2 := by
  have hc := continuous_heatDensityPi (d := d) t
  refine (integrable_sumSq_mul_heatDensityPi (d := d) ht).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatDensityPi_pos ht z).le (sq_nonneg _)),
    mul_comm]
  exact mul_le_mul_of_nonneg_right (sq_le_sum_sq z i) (heatDensityPi_pos ht z).le

/-- For `t > 0`, `z ↦ φ_t(z) (a zᵢ² + b zᵢ + c)` is Lebesgue integrable. -/
theorem integrable_heatDensityPi_mul_quad {t : ℝ} (ht : 0 < t) (a b c : ℝ) (i : Fin d) :
    Integrable fun z : Fin d → ℝ => heatDensityPi t z * (a * z i ^ 2 + b * z i + c) := by
  have hc := continuous_heatDensityPi (d := d) t
  have h1 : Integrable fun z : Fin d → ℝ => heatDensityPi t z * z i := by
    refine ((integrable_heatDensityPi_mul_sq ht i).add (integrable_heatDensityPi ht)).mono'
      (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
    have hp := (heatDensityPi_pos ht z).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, Pi.add_apply]
    have h1 : |z i| ≤ z i ^ 2 + 1 := by
      nlinarith [abs_nonneg (z i), sq_abs (z i), sq_nonneg (|z i| - 1)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  have e : (fun z : Fin d → ℝ => heatDensityPi t z * (a * z i ^ 2 + b * z i + c)) =
      fun z => a * (heatDensityPi t z * z i ^ 2) + b * (heatDensityPi t z * z i) +
        c * heatDensityPi t z := by
    funext z; ring
  rw [e]
  exact (((integrable_heatDensityPi_mul_sq ht i).const_mul a).add (h1.const_mul b)).add
    ((integrable_heatDensityPi ht).const_mul c)

/-! ### Fubini against `Lebesgue × ρ` -/

section Moments

variable {ρ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ]

/-- **Integrability on `Lebesgue × ρ` from a Gaussian quadratic envelope.** If
`|F(y, x)| ≤ (A |y - x|² + B + C |x|²) φ_t(y - x)` with `A, B, C ≥ 0`, `t > 0` and
`∫ |x|² dρ < ∞`, then `(y, x) ↦ F(y, x)` is integrable for `volume.prod ρ`. -/
theorem integrable_prod_of_abs_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ}
    (ht : 0 < t) {F : (Fin d → ℝ) → (Fin d → ℝ) → ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) ((volume : Measure (Fin d → ℝ)).prod ρ))
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hle : ∀ y x, |F y x| ≤
      (A * ∑ i, (y - x) i ^ 2 + B + C * ∑ i, x i ^ 2) * heatDensityPi t (y - x)) :
    Integrable (Function.uncurry F) ((volume : Measure (Fin d → ℝ)).prod ρ) := by
  have hc := continuous_heatDensityPi (d := d) t
  set k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
    fun x z => (A * ∑ i, z i ^ 2 + B + C * ∑ i, x i ^ 2) * heatDensityPi t z with hk
  have hk0 : ∀ x z, 0 ≤ k x z := fun x z =>
    mul_nonneg (by have := sum_sq_nonneg z; have := sum_sq_nonneg x; positivity)
      (heatDensityPi_pos ht z).le
  have hkint : ∀ x, Integrable (k x) := by
    intro x
    have e : k x = fun z => A * ((∑ i, z i ^ 2) * heatDensityPi t z) +
        (B + C * ∑ i, x i ^ 2) * heatDensityPi t z := by
      funext z; simp only [hk]; ring
    rw [e]
    exact ((integrable_sumSq_mul_heatDensityPi ht).const_mul A).add
      ((integrable_heatDensityPi ht).const_mul _)
  have hkval : ∀ x, ∫ z, k x z = A * (d * t) + (B + C * ∑ i, x i ^ 2) := by
    intro x
    have e : k x = fun z => A * (heatDensityPi t z * ∑ i, z i ^ 2) +
        (B + C * ∑ i, x i ^ 2) * heatDensityPi t z := by
      funext z; simp only [hk]; ring
    rw [e, integral_add (((integrable_sumSq_mul_heatDensityPi ht).congr
      (Eventually.of_forall fun z => mul_comm _ _)).const_mul A)
      ((integrable_heatDensityPi ht).const_mul _), integral_const_mul, integral_const_mul,
      integral_heatDensityPi_mul_sumSq ht, integral_heatDensityPi ht, mul_one]
  have hG : Integrable (Function.uncurry fun y x => k x (y - x))
      ((volume : Measure (Fin d → ℝ)).prod ρ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry fun y x => k x (y - x))
        ((volume : Measure (Fin d → ℝ)).prod ρ) := by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hk, Function.uncurry_def]
      fun_prop
    refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact (hkint x).comp_sub_right x
    · simp only [Function.uncurry_apply_pair]
      have e : ∀ x : Fin d → ℝ, ∫ y, ‖k x (y - x)‖ = A * (d * t) + (B + C * ∑ i, x i ^ 2) :=
        fun x => by
          rw [integral_sub_right_eq_self (fun z => ‖k x z‖) x]
          simp_rw [Real.norm_of_nonneg (hk0 x _)]
          exact hkval x
      simp_rw [e]
      exact (integrable_const _).add ((integrable_const _).add (hmom.const_mul C))
  refine hG.mono' hF (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  exact hle p.1 p.2

/-- `∫ φ_t(y - x) |y|² dy = |x|² + d t`. -/
theorem integral_heatDensityPi_sub_mul_sumSq {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    ∫ y, heatDensityPi t (y - x) * ∑ i, y i ^ 2 = ∑ i, x i ^ 2 + d * t := by
  have e := integral_sub_right_eq_self (μ := (volume : Measure (Fin d → ℝ)))
    (fun z : Fin d → ℝ => heatDensityPi t z * ∑ i, (z + x) i ^ 2) x
  simp only [sub_add_cancel] at e
  rw [e]
  have e2 : (fun z : Fin d → ℝ => heatDensityPi t z * ∑ i, (z + x) i ^ 2) =
      fun z => ∑ i, heatDensityPi t z * (1 * z i ^ 2 + (2 * x i) * z i + x i ^ 2) := by
    funext z; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]; ring
  rw [e2, integral_finsetSum _ fun i _ => integrable_heatDensityPi_mul_quad ht _ _ _ i]
  simp_rw [integral_heatDensityPi_mul_quad ht]
  rw [Finset.sum_add_distrib]
  simp [add_comm]

/-- `(y, x) ↦ φ_t(y - x) |y|²` is integrable for `volume.prod ρ`. -/
theorem integrable_prod_heatDensityPi_mul_sumSq (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (Function.uncurry fun (y x : Fin d → ℝ) => heatDensityPi t (y - x) *
      ∑ i, y i ^ 2) ((volume : Measure (Fin d → ℝ)).prod ρ) := by
  have hc := continuous_heatDensityPi (d := d) t
  refine integrable_prod_of_abs_le hmom ht
    (Continuous.aestronglyMeasurable (by simp only [Function.uncurry_def]; fun_prop))
    (A := 2) (B := 0) (C := 2) (by norm_num) le_rfl (by norm_num) fun y x => ?_
  have hp := (heatDensityPi_pos ht (y - x)).le
  rw [abs_of_nonneg (mul_nonneg hp (sum_sq_nonneg y)), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hp
  have := sum_sq_sub_le (y - x) (-x)
  simp only [sub_neg_eq_add, sub_add_cancel] at this
  have e : ∑ i, (-x) i ^ 2 = ∑ i, x i ^ 2 := by simp
  linarith

/-- **Second moment along the heat flow.** For a probability `ρ` with finite second moment and
`t > 0`: `y ↦ p_t(y) |y|²` is integrable and `∫ p_t |y|² = M + d t`, `M = secondMoment ρ`. -/
theorem integral_heatFlowDensityPi_mul_sumSq (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => heatFlowDensityPi ρ t y * ∑ i, y i ^ 2) ∧
      ∫ y, heatFlowDensityPi ρ t y * ∑ i, y i ^ 2 = secondMoment ρ + d * t := by
  have hP := integrable_prod_heatDensityPi_mul_sumSq hmom ht
  have e : (fun y => heatFlowDensityPi ρ t y * ∑ i, y i ^ 2) =
      fun y => ∫ x, heatDensityPi t (y - x) * ∑ i, y i ^ 2 ∂ρ := by
    funext y; rw [heatFlowDensityPi, integral_mul_const]
  rw [e]
  refine ⟨hP.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun (y x : Fin d → ℝ) =>
    heatDensityPi t (y - x) * ∑ i, y i ^ 2) hP]
  simp_rw [integral_heatDensityPi_sub_mul_sumSq ht]
  rw [integral_add hmom (integrable_const _), integral_const]
  simp [secondMoment]

/-- **Stein's identity along the heat flow.** For a probability `ρ` with finite second moment,
`t > 0` and a coordinate `i`: `y ↦ yᵢ ∂ᵢp_t(y)` is integrable and `∫ yᵢ ∂ᵢp_t(y) dy = -1`. -/
theorem integral_mul_heatFlowGradPi (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ}
    (ht : 0 < t) (i : Fin d) :
    Integrable (fun y => y i * heatFlowGradPi ρ t y i) ∧
      ∫ y, y i * heatFlowGradPi ρ t y i = -1 := by
  have hc := continuous_heatDensityPi (d := d) t
  set F : (Fin d → ℝ) → (Fin d → ℝ) → ℝ := fun y x => y i * heatGradPi t (y - x) i with hF
  have hP : Integrable (Function.uncurry F) ((volume : Measure (Fin d → ℝ)).prod ρ) := by
    have hFc : Continuous (Function.uncurry F) := by
      simp only [hF, heatGradPi, Function.uncurry_def]
      fun_prop
    refine integrable_prod_of_abs_le hmom ht hFc.aestronglyMeasurable
      (A := 3 / (2 * t)) (B := 0) (C := 1 / (2 * t)) (by positivity) le_rfl (by positivity)
      fun y x => ?_
    have hp := (heatDensityPi_pos ht (y - x)).le
    simp only [hF, heatGradPi]
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos ht, abs_of_nonneg hp]
    have hz := sq_le_sum_sq (y - x) i
    have hx := sq_le_sum_sq x i
    have hyi : y i = (y - x) i + x i := by simp
    have key : |y i| * (|(y - x) i| / t) ≤
        3 / (2 * t) * ∑ j, (y - x) j ^ 2 + 0 + 1 / (2 * t) * ∑ j, x j ^ 2 := by
      have h1 : |y i| * |(y - x) i| ≤ (3 / 2) * (y - x) i ^ 2 + (1 / 2) * x i ^ 2 := by
        rw [hyi]
        have := abs_add_le ((y - x) i) (x i)
        nlinarith [abs_nonneg ((y - x) i), abs_nonneg (x i), sq_abs ((y - x) i), sq_abs (x i),
          sq_nonneg (|(y - x) i| - |x i|), abs_nonneg ((y - x) i + x i)]
      have h2 : |y i| * (|(y - x) i| / t) = (|y i| * |(y - x) i|) / t := by ring
      rw [h2, div_le_iff₀ ht]
      have e3 : (3 / (2 * t) * ∑ j, (y - x) j ^ 2 + 0 + 1 / (2 * t) * ∑ j, x j ^ 2) * t =
          (3 / 2) * ∑ j, (y - x) j ^ 2 + (1 / 2) * ∑ j, x j ^ 2 := by
        field_simp; ring
      rw [e3]; nlinarith
    calc |y i| * (|(y - x) i| / t * heatDensityPi t (y - x))
        = |y i| * (|(y - x) i| / t) * heatDensityPi t (y - x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key hp
  have e : (fun y => y i * heatFlowGradPi ρ t y i) = fun y => ∫ x, F y x ∂ρ := by
    funext y; simp only [hF, heatFlowGradPi]; rw [integral_const_mul]
  rw [e]
  refine ⟨hP.integral_prod_left, ?_⟩
  rw [integral_integral_swap hP]
  have hin : ∀ x : Fin d → ℝ, ∫ y, F y x = -1 := by
    intro x
    have e1 := integral_sub_right_eq_self (μ := (volume : Measure (Fin d → ℝ)))
      (fun z : Fin d → ℝ => (z + x) i * heatGradPi t z i) x
    simp only [sub_add_cancel] at e1
    simp only [hF]
    rw [e1]
    have e2 : (fun z : Fin d → ℝ => (z + x) i * heatGradPi t z i) =
        fun z => heatDensityPi t z * ((-1 / t) * z i ^ 2 + (-x i / t) * z i + 0) := by
      funext z; simp only [heatGradPi, Pi.add_apply]; ring
    rw [e2, integral_heatDensityPi_mul_quad ht, div_mul_cancel₀ _ ht.ne', add_zero]
  simp_rw [hin]
  simp

end Moments

/-! ### Relative Fisher information and relative entropy against a Gaussian -/

section Relative

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- **Relative vs absolute Fisher information.** For a probability `ρ` with finite second
moment `M`, `v, t > 0`, `c = v + t`:
`I(ρ_t‖N(0, c I)) = heatFisher ρ N(0, v I) t = J(t) - 2d/c + (M + d t)/c²`. -/
theorem heatFisher_gaussian_eq (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {v t : ℝ}
    (hv : 0 < v) (ht : 0 < t) :
    heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t =
      heatFisherInfo ρ t - 2 * d / (v + t) + (secondMoment ρ + d * t) / (v + t) ^ 2 := by
  have hc : 0 < v + t := by linarith
  have hS := fun i => integral_mul_heatFlowGradPi (ρ := ρ) hmom ht i
  obtain ⟨hMi, hM⟩ := integral_heatFlowDensityPi_mul_sumSq (ρ := ρ) hmom ht
  have hJ := integrable_heatFisherInfo_integrand ρ ht
  have hpt : ∀ y, fisherIntegrand (heatFlowDensityPi ρ)
      (heatFlowDensityPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal))
      (heatFlowGradPi ρ)
      (heatFlowGradPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)) t y =
      (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y +
        2 / (v + t) * ∑ i, y i * heatFlowGradPi ρ t y i +
        1 / (v + t) ^ 2 * (heatFlowDensityPi ρ t y * ∑ i, y i ^ 2) := by
    intro y
    rw [fisherIntegrand_gaussian ρ hv ht y]
    have hp := (heatFlowDensityPi_pos ρ ht y).ne'
    unfold gaussRelFluxPi
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hsum : Integrable fun y => ∑ i, y i * heatFlowGradPi ρ t y i :=
    integrable_finsetSum _ fun i _ => (hS i).1
  have h12 : Integrable fun y => (∑ i, heatFlowGradPi ρ t y i ^ 2) / heatFlowDensityPi ρ t y +
      2 / (v + t) * ∑ i, y i * heatFlowGradPi ρ t y i := hJ.add (hsum.const_mul _)
  have h3 : Integrable fun y => 1 / (v + t) ^ 2 * (heatFlowDensityPi ρ t y * ∑ i, y i ^ 2) :=
    hMi.const_mul _
  have h2 : Integrable fun y => 2 / (v + t) * ∑ i, y i * heatFlowGradPi ρ t y i :=
    hsum.const_mul _
  rw [heatFisher]
  simp_rw [hpt]
  rw [integral_add h12 h3, integral_add hJ h2, integral_const_mul, integral_const_mul, hM,
    integral_finsetSum _ fun i _ => (hS i).1]
  simp_rw [fun i => (hS i).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [heatFisherInfo]
  field_simp
  ring

/-- `log((2π c)^{-d/2}) = -(d/2) log(2π c)` for `c > 0`. -/
theorem log_gc {c : ℝ} (hc : 0 < c) :
    Real.log (gc d c) = -(d / 2) * Real.log (2 * Real.pi * c) := by
  unfold gc
  rw [Real.log_pow, Real.log_inv, Real.log_sqrt (by positivity)]
  ring

/-- **Relative entropy against the Gaussian heat flow.** For a probability `ρ` with finite
second moment `M`, `v, t > 0`, `c = v + t`: `p_t log p_t` is integrable and
`KL(ρ_t‖N(0, c I)) = heatKL ρ N(0, v I) t = H(t) - log((2π c)^{-d/2}) + (M + d t)/(2c)`. -/
theorem heatKL_gaussian_eq (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {v t : ℝ}
    (hv : 0 < v) (ht : 0 < t) :
    Integrable (fun y => heatFlowDensityPi ρ t y * Real.log (heatFlowDensityPi ρ t y)) ∧
    heatKL ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t =
      heatNegEntropy ρ t - Real.log (gc d (v + t)) + (secondMoment ρ + d * t) / (2 * (v + t)) := by
  have hc : 0 < v + t := by linarith
  have hreg := heatFlowRegularPi_gaussian ρ hmom hv
  have hkl := hreg.integrable_kl t ht
  obtain ⟨hMi, hM⟩ := integral_heatFlowDensityPi_mul_sumSq (ρ := ρ) hmom ht
  have hPi := (integrable_heatFlowDensityPi ρ ht).1
  have hP1 := (integrable_heatFlowDensityPi ρ ht).2
  have hpt : ∀ y, klIntegrand (heatFlowDensityPi ρ)
      (heatFlowDensityPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)) t y =
      heatFlowDensityPi ρ t y * Real.log (heatFlowDensityPi ρ t y) -
        Real.log (gc d (v + t)) * heatFlowDensityPi ρ t y +
        1 / (2 * (v + t)) * (heatFlowDensityPi ρ t y * ∑ i, y i ^ 2) := by
    intro y
    have hp := (heatFlowDensityPi_pos ρ ht y).ne'
    unfold klIntegrand
    rw [heatFlowDensityPi_gaussian hv ht, heatDensityPi_eq,
      Real.log_div hp (mul_pos (gc_pos hc) (Real.exp_pos _)).ne',
      Real.log_mul (gc_pos hc).ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  have hent : Integrable fun y =>
      heatFlowDensityPi ρ t y * Real.log (heatFlowDensityPi ρ t y) := by
    have h := (hkl.add (hPi.const_mul (Real.log (gc d (v + t))))).sub
      (hMi.const_mul (1 / (2 * (v + t))))
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hpt y]; ring
  refine ⟨hent, ?_⟩
  rw [heatKL_eq_integral ht hkl]
  simp_rw [hpt]
  have h12 : Integrable fun y => heatFlowDensityPi ρ t y * Real.log (heatFlowDensityPi ρ t y) -
      Real.log (gc d (v + t)) * heatFlowDensityPi ρ t y := hent.sub (hPi.const_mul _)
  have h3 : Integrable fun y => 1 / (2 * (v + t)) * (heatFlowDensityPi ρ t y * ∑ i, y i ^ 2) :=
    hMi.const_mul _
  have h2 : Integrable fun y => Real.log (gc d (v + t)) * heatFlowDensityPi ρ t y :=
    hPi.const_mul _
  rw [integral_add h12 h3, integral_sub hent h2, integral_const_mul, integral_const_mul, hP1, hM,
    heatNegEntropy]
  field_simp

/-! ### de Bruijn's identity for the entropy, and monotonicity of the Fisher information -/

/-- **de Bruijn's identity for the differential entropy.** For a probability `ρ` on
`Fin d → ℝ` with finite second moment and `t > 0`, `H(s) = ∫ p_s log p_s` is differentiable at
`t` with `H'(t) = -J(t)/2` (`J = heatFisherInfo`). Proved from the relative-entropy de Bruijn
identity `HeatFlowDeBruijnPi.hasDerivAt_heatKL` against `N(0, (1 + s) I)`. -/
theorem hasDerivAt_heatNegEntropy (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (heatNegEntropy ρ) (-(1 / 2) * heatFisherInfo ρ t) t := by
  set M := secondMoment ρ
  set γ := Measure.pi fun _ : Fin d => gaussianReal 0 (1 : ℝ).toNNReal
  have hreg := heatFlowRegularPi_gaussian ρ hmom (v := 1) one_pos
  have hK := hasDerivAt_heatKL hreg (show t ∈ Ioi 0 from ht)
  rw [heatFisher_gaussian_eq ρ hmom one_pos ht] at hK
  -- `H(s) = heatKL(s) - (d/2) log(2π(1+s)) - (M + d s)/(2(1+s))` for `s > 0`
  have hc : 0 < 1 + t := by linarith
  have hL1 : HasDerivAt (fun s : ℝ => Real.log (2 * Real.pi * (1 + s)))
      (2 * Real.pi / (2 * Real.pi * (1 + t))) t := by
    have h : HasDerivAt (fun s : ℝ => 2 * Real.pi * (1 + s)) (2 * Real.pi) t := by
      simpa using ((hasDerivAt_id t).const_add 1).const_mul (2 * Real.pi)
    exact h.log (by positivity)
  have hL2 : HasDerivAt (fun s : ℝ => (M + d * s) / (2 * (1 + s)))
      ((d * (2 * (1 + t)) - (M + d * t) * 2) / (2 * (1 + t)) ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => M + d * s) d t := by
      simpa using ((hasDerivAt_id t).const_mul (d : ℝ)).const_add M
    have h2 : HasDerivAt (fun s : ℝ => 2 * (1 + s)) 2 t := by
      simpa using ((hasDerivAt_id t).const_add 1).const_mul (2 : ℝ)
    exact h1.div h2 (by positivity)
  have hsum := (hK.add (hL1.const_mul (-(d / 2 : ℝ)))).sub hL2
  have heq : (fun s => heatKL ρ γ s + -(d / 2 : ℝ) * Real.log (2 * Real.pi * (1 + s)) -
      (M + d * s) / (2 * (1 + s))) =ᶠ[𝓝 t] heatNegEntropy ρ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : (0 : ℝ) < s := hs
    have h := (heatKL_gaussian_eq ρ hmom one_pos hs').2
    rw [log_gc (by linarith : (0 : ℝ) < 1 + s)] at h
    change heatKL ρ γ s = _ at h
    rw [h]; ring
  refine (hsum.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  field_simp
  ring

/-- **The Fisher information of the heat flow is non-increasing.** For a probability `ρ` with
finite second moment and `0 < a ≤ b`: `J(b) ≤ J(a)`. Proved from the Verified decay
`GaussianLSIPi.heatFisher_gaussian_le` of the relative Fisher information against
`N(0, (v + t) I)` with `v = M + 1`, and `heatFisher_gaussian_eq`. -/
theorem heatFisherInfo_anti (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : heatFisherInfo ρ b ≤ heatFisherInfo ρ a := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  set M := secondMoment ρ with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun x => sum_sq_nonneg x
  set v := M + 1 with hvdef
  have hv : 0 < v := by linarith
  have hdv : 0 ≤ (d : ℝ) * v - M := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have : M = 0 := by simp [hMdef, secondMoment]
      simp [this]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
  have hb : 0 < b := ha.trans h
  have hreg := heatFlowRegularPi_gaussian ρ hmom hv
  have hdec := heatFisher_gaussian_le ρ hv ha (sub_pos.2 h) (hreg.integrable_fisher a ha)
  rw [add_sub_cancel] at hdec
  rw [heatFisher_gaussian_eq ρ hmom hv hb, heatFisher_gaussian_eq ρ hmom hv ha] at hdec
  have hI0 : 0 ≤ heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) a :=
    heatFisher_nonneg ρ _ ha
  rw [heatFisher_gaussian_eq ρ hmom hv ha] at hI0
  set Ia := heatFisherInfo ρ a - 2 * d / (v + a) + (M + d * a) / (v + a) ^ 2 with hIa
  have hr : ((v + a) / (v + a + (b - a))) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  have hIb : heatFisherInfo ρ b - 2 * d / (v + b) + (M + d * b) / (v + b) ^ 2 ≤ Ia :=
    hdec.trans (by nlinarith)
  -- `ψ(t) = 2d/(v+t) - (M + d t)/(v+t)² = d/(v+t) + (d v - M)/(v+t)²` is non-increasing
  have hψ : ∀ s, 0 < s → 2 * d / (v + s) - (M + d * s) / (v + s) ^ 2 =
      d / (v + s) + (d * v - M) / (v + s) ^ 2 := by
    intro s hs
    have : 0 < v + s := by linarith
    field_simp; ring
  have hmono : (d : ℝ) / (v + b) + (d * v - M) / (v + b) ^ 2 ≤
      d / (v + a) + (d * v - M) / (v + a) ^ 2 := by
    have h1 : (d : ℝ) / (v + b) ≤ d / (v + a) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    have h2 : (d * v - M) / (v + b) ^ 2 ≤ (d * v - M) / (v + a) ^ 2 :=
      div_le_div_of_nonneg_left hdv (by positivity) (by nlinarith)
    linarith
  have ea := hψ a ha
  have eb := hψ b hb
  linarith

/-! ### Entropy production on one step -/

/-- **Upper bound on the entropy production over `[a, b]`.** For a probability `ρ` with finite
second moment and `0 < a ≤ b`: `H(a) - H(b) ≤ ½ (b - a) J(a)`. -/
theorem heatNegEntropy_sub_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    heatNegEntropy ρ a - heatNegEntropy ρ b ≤ (b - a) / 2 * heatFisherInfo ρ a := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (heatNegEntropy ρ) (-(1 / 2) * heatFisherInfo ρ s) s :=
    fun s hs => hasDerivAt_heatNegEntropy ρ hmom (ha.trans_le hs.1)
  have := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (C := -(1 / 2) * heatFisherInfo ρ a) (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s (Ioo_subset_Icc_self hs)).deriv]
      have := heatFisherInfo_anti ρ hmom ha hs.1.le
      linarith) a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab
  linarith

/-- **Lower bound on the entropy production over `[a, b]`.** For a probability `ρ` with finite
second moment and `0 < a ≤ b`: `½ (b - a) J(b) ≤ H(a) - H(b)`. -/
theorem le_heatNegEntropy_sub (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / 2 * heatFisherInfo ρ b ≤ heatNegEntropy ρ a - heatNegEntropy ρ b := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (heatNegEntropy ρ) (-(1 / 2) * heatFisherInfo ρ s) s :=
    fun s hs => hasDerivAt_heatNegEntropy ρ hmom (ha.trans_le hs.1)
  have := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (C := -(1 / 2) * heatFisherInfo ρ b) (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s (Ioo_subset_Icc_self hs)).deriv]
      have := heatFisherInfo_anti ρ hmom (ha.trans hs.1) hs.2.le
      linarith) a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab
  linarith

/-! ### Theorem B: the discretisation sum -/

/-- The exact discretisation error of the Gaussian reverse step from `b` to `a` in heat-flow
coordinates: `H(a) - H(b) - ½ (b - a) J(b)` (Theorem A identifies it with the averaged KL
between the exact reverse kernel and `N(E[Y_a | Y_b], (b - a) I)`). -/
noncomputable def entropyStep (ρ : Measure (Fin d → ℝ)) (a b : ℝ) : ℝ :=
  heatNegEntropy ρ a - heatNegEntropy ρ b - (b - a) / 2 * heatFisherInfo ρ b

/-- Each step error is nonnegative (`le_heatNegEntropy_sub`). -/
theorem entropyStep_nonneg (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : 0 ≤ entropyStep ρ a b := by
  have := le_heatNegEntropy_sub ρ hmom ha hab
  unfold entropyStep; linarith

/-- One step: `entropyStep ρ a b ≤ ½ (b - a) (J(a) - J(b))`. -/
theorem entropyStep_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    entropyStep ρ a b ≤ (b - a) / 2 * (heatFisherInfo ρ a - heatFisherInfo ρ b) := by
  have := heatNegEntropy_sub_le ρ hmom ha hab
  unfold entropyStep; linarith

/-- **Theorem B (d-linear discretisation bound, heat-flow coordinates).** Let `ρ` be a
probability measure on `Fin d → ℝ` with finite second moment, `κ ≥ 0`, and a grid
`0 < u 0 ≤ u 1 ≤ … ≤ u n` with `u (k+1) - u k ≤ κ u k`. Then
`∑_{k<n} (H(u_k) - H(u_{k+1}) - ½ (u_{k+1} - u_k) J(u_{k+1})) ≤ (κ d / 2)(1 + log(u_n / u_0))`.
No density, smoothness or log-concavity of `ρ` is assumed. -/
theorem sum_entropyStep_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {u : ℕ → ℝ}
    {κ : ℝ} (n : ℕ) (hκ : 0 ≤ κ) (h0 : 0 < u 0) (hmono : ∀ k < n, u k ≤ u (k + 1))
    (hu : ∀ k < n, u (k + 1) - u k ≤ κ * u k) :
    ∑ k ∈ Finset.range n, entropyStep ρ (u k) (u (k + 1)) ≤
      κ * d / 2 * (1 + Real.log (u n / u 0)) := by
  have hpos : ∀ k ≤ n, 0 < u k := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact (ih (by omega)).trans_le (hmono k (by omega))
  have hR := sum_riemannError_le (J := fun k => heatFisherInfo ρ (u k)) (D := d) n hκ h0 hmono
    hu (fun k hk => heatFisherInfo_anti ρ hmom (hpos k hk.le) (hmono k hk))
    (fun k hk => heatFisherInfo_nonneg ρ (hpos k hk))
    (fun k hk => by
      have h := heatFisherInfo_le ρ (hpos k hk)
      rw [le_div_iff₀ (hpos k hk)] at h
      linarith [mul_comm (u k) (heatFisherInfo ρ (u k))])
  calc ∑ k ∈ Finset.range n, entropyStep ρ (u k) (u (k + 1))
      ≤ ∑ k ∈ Finset.range n, (u (k + 1) - u k) / 2 *
          (heatFisherInfo ρ (u k) - heatFisherInfo ρ (u (k + 1))) :=
        Finset.sum_le_sum fun k hk =>
          entropyStep_le ρ hmom (hpos k (Finset.mem_range.1 hk).le)
            (hmono k (Finset.mem_range.1 hk))
    _ = (1 / 2) * ∑ k ∈ Finset.range n, (u (k + 1) - u k) *
          (heatFisherInfo ρ (u k) - heatFisherInfo ρ (u (k + 1))) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (1 / 2) * (κ * d * (1 + Real.log (u n / u 0))) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = κ * d / 2 * (1 + Real.log (u n / u 0)) := by ring

end Relative

end FormalizeSampling.DiffusionDiscretization
