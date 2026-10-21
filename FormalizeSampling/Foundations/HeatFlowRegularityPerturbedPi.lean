module

public import FormalizeSampling.Foundations.HeatFlowRegularityPi
public import FormalizeSampling.Foundations.GibbsMeasure

/-!
# Regularity of the isotropic heat flow from a posterior second-moment bound

Status: **Verified** (no named hypotheses). `d`-dimensional counterpart of
`Foundations/HeatFlowRegularityPerturbed.lean`.
For a probability measure `ρ` on `Fin d → ℝ` with finite second moment `∫ ∑ᵢ xᵢ² dρ < ∞` and a
target `π` satisfying a *posterior second-moment bound* (`PosteriorSecondMomentBoundPi`), every
field of `HeatFlowDeBruijnPi.HeatFlowRegularPi ρ π (Ioi 0)` is proved. The bound holds for
isotropic Gaussians.

Notation (as in `HeatFlowDeBruijnPi`, `HeatFlowRegularityPi`): `|z|² = ∑ᵢ zᵢ²`,
`φ_r = heatDensityPi r`, `p_r = heatFlowDensityPi ρ r = ρ * φ_r`, `q_r = heatFlowDensityPi π r`
with gradient `∂ᵢq_r = heatFlowGradPi π r · i` and Hessian `∂ᵢ∂ⱼq_r = heatFlowHessPi π r · i j`,
and `M_r(y) = heatFlowM2Pi π r y = ∫ |y - x|² φ_r(y - x) dπ(x)`, so that `M_r(y) / q_r(y)` is
the posterior second moment `E[|X - y|² | X + √r Z = y]` of the noise.

Proof strategy:
* `PosteriorSecondMomentBoundPi π`: for `0 < a ≤ b` there is `A` with
  `M_r(y) ≤ A (1 + |y|²) q_r(y)` for `r ∈ [a, b]`.
* Cauchy–Schwarz `(∂ᵢq_r)² / q_r ≤ M_r / r²` and `|∂ᵢ²q_r| ≤ M_r / r² + q_r / r` give the ratio
  bounds `(∂ᵢq_r/q_r)², |∂ᵢq_r/q_r|, |∂ᵢ²q_r/q_r| ≤ B (1 + |y|²)` (`exists_ratio_le_post`).
* `|log q_r(y)| ≤ L (1 + |y|²)` holds for **every** probability `π` (lower bound from the mass
  of `π` on a ball, `exists_abs_log_heatFlowDensityPi_le`).
* With these bounds and the `ρ`-side envelope of `HeatFlowRegularityPi` (`envBound`,
  `one_add_mul_integral_le`), every de Bruijn integrand is `≤ C E_{2b}` uniformly on `[a, b]`.
* For `π₀ = N(0, v I)`: `Δq_r = M_r / r² - d q_r / r` (`sum_heatFlowHessPi_eq`) and
  `q_r = φ_{v + r}` give `M_r ≤ (1 + d b)(1 + |y|²) q_r`.

## Main results

* `heatFlowRegularPi_of_posteriorSecondMomentBoundPi`: `HeatFlowRegularPi ρ π (Ioi 0)` for
  probabilities `ρ, π` with `∫ ∑ᵢ xᵢ² dρ < ∞` and `PosteriorSecondMomentBoundPi π`.
* `posteriorSecondMomentBoundPi_gaussian`: the bound for `N(0, v I)`, `v > 0`.
* Isotropic Gaussian targets (in the namespace `HeatFlowRegularityPi`):
  `heatFlowRegularPi_gaussian` (`HeatFlowRegularPi ρ N(0, v I) (Ioi 0)` for `v > 0` and
  `∫ ∑ᵢ xᵢ² dρ < ∞`) and `klDiv_heatKernelPi_comp_ne_top_of_moment` (`KL(ρ_t‖π_t) < ∞`, `t > 0`).

## Not proved here

* Targets whose posterior second moment grows faster than `1 + |y|²` (e.g. heavy tails); the
  posterior bound is only verified for isotropic Gaussians. The proximal sampler for bounded
  perturbations of a Gaussian (PX-4, `Samplers/ProximalPerturbedGaussian.lean`) needs no
  forward regularity of this kind: it uses the final form of PX-2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.HeatFlowRegularityPerturbedPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi FormalizeSampling.HeatFlowRegularityPi

variable {d : ℕ}

/-- The unnormalised posterior second moment of the noise,
`M_t(y) = ∫ |y - x|² φ_t(y - x) dπ(x)` with `|z|² = ∑ᵢ zᵢ²`; `M_t(y) / q_t(y)` is the posterior
mean of `|X - y|²` given `X + √t Z = y` (`X ~ π`, `Z ~ N(0, I)`). -/
noncomputable def heatFlowM2Pi (π : Measure (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ x, (∑ i, (y - x) i ^ 2) * heatDensityPi t (y - x) ∂π

/-- **Posterior second-moment bound** on `Fin d → ℝ`. For every `0 < a ≤ b` there is `A` with
`M_r(y) ≤ A (1 + |y|²) q_r(y)` for all `r ∈ [a, b]` and `y`, i.e. the posterior second moment
`E[|X - y|² | X + √r Z = y]` grows at most quadratically in `y`, locally uniformly in `r`. -/
def PosteriorSecondMomentBoundPi (π : Measure (Fin d → ℝ)) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∃ A, ∀ r ∈ Icc a b, ∀ y,
    heatFlowM2Pi π r y ≤ A * (1 + ∑ i, y i ^ 2) * heatFlowDensityPi π r y

/-! ### The posterior second moment -/

section Posterior

variable (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]

/-- For `t > 0` and fixed `y`, `x ↦ |y - x|² φ_t(y - x)` is `π`-integrable (it is bounded by
`2t · gc d t`). -/
theorem integrable_sum_sq_mul_heatDensityPi {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    Integrable (fun x => (∑ i, (y - x) i ^ 2) * heatDensityPi t (y - x)) π := by
  refine integrable_comp_sub_of_bound π (k := fun z => (∑ i, z i ^ 2) * heatDensityPi t z)
    (by have := continuous_heatDensityPi (d := d) t; fun_prop) (B := 2 * t * gc d t)
    (fun z => ?_) y
  have hS := sum_sq_nonneg z
  have hE := mul_exp_neg_le ht hS
  have hg := gc_pos (d := d) ht
  rw [abs_of_nonneg (mul_nonneg hS (heatDensityPi_pos ht z).le), heatDensityPi_eq]
  calc (∑ i, z i ^ 2) * (gc d t * Real.exp (-(∑ i, z i ^ 2) / (2 * t)))
      = ((∑ i, z i ^ 2) * Real.exp (-(∑ i, z i ^ 2) / (2 * t))) * gc d t := by ring
    _ ≤ 2 * t * gc d t := by gcongr

omit [IsProbabilityMeasure π] in
/-- `M_t(y) ≥ 0` for `t > 0`. -/
theorem heatFlowM2Pi_nonneg {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) : 0 ≤ heatFlowM2Pi π t y :=
  integral_nonneg fun _ => mul_nonneg (sum_sq_nonneg _) (heatDensityPi_pos ht _).le

/-- For `t > 0` and fixed `y`, `x ↦ φ_t(y - x)` is `π`-integrable. -/
theorem integrable_heatDensityPi_comp_sub {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    Integrable (fun x => heatDensityPi t (y - x)) π :=
  integrable_comp_sub_of_bound π (continuous_heatDensityPi t) (B := gc d t)
    (fun z => by rw [abs_of_pos (heatDensityPi_pos ht z)]; exact heatDensityPi_le ht z) y

/-- Cauchy–Schwarz: `(∂ᵢq_t(y))² / q_t(y) ≤ M_t(y) / t²` for `t > 0`. -/
theorem sq_heatFlowGradPi_div_le_heatFlowM2Pi {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ)
    (i : Fin d) :
    heatFlowGradPi π t y i ^ 2 / heatFlowDensityPi π t y ≤ heatFlowM2Pi π t y / t ^ 2 := by
  refine (sq_heatFlowGradPi_div_le ht y i).trans ?_
  unfold heatFlowM2Pi
  rw [← integral_div]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ =>
    mul_nonneg (sq_nonneg _) (heatDensityPi_pos ht _).le)
    ((integrable_sum_sq_mul_heatDensityPi π ht y).div_const _)
    (Eventually.of_forall fun x => ?_)
  have h1 := sq_le_sum_sq (y - x) i
  have hφ := (heatDensityPi_pos ht (y - x)).le
  simp only
  rw [div_pow, div_mul_eq_mul_div]
  gcongr

/-- `|∂ᵢ²q_t(y)| ≤ M_t(y) / t² + q_t(y) / t` for `t > 0`. -/
theorem abs_heatFlowHessPi_le_heatFlowM2Pi {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ)
    (i : Fin d) :
    |heatFlowHessPi π t y i i| ≤ heatFlowM2Pi π t y / t ^ 2 + heatFlowDensityPi π t y / t := by
  have hI : Integrable (fun x => heatHessPi t (y - x) i i) π :=
    integrable_comp_sub_of_bound π (k := fun z => heatHessPi t z i i)
      (continuous_heatHessPi t i i) (abs_heatHessPi_le ht · i i) y
  unfold heatFlowHessPi heatFlowM2Pi heatFlowDensityPi
  rw [← integral_div, ← integral_div, ← integral_add
    ((integrable_sum_sq_mul_heatDensityPi π ht y).div_const _)
    ((integrable_heatDensityPi_comp_sub π ht y).div_const _)]
  refine abs_integral_le_integral_abs.trans (integral_mono hI.abs
    (((integrable_sum_sq_mul_heatDensityPi π ht y).div_const _).add
      ((integrable_heatDensityPi_comp_sub π ht y).div_const _)) fun x => ?_)
  set z := y - x
  have hφ := (heatDensityPi_pos ht z).le
  have hzi := sq_le_sum_sq z i
  simp only [heatHessPi, ↓reduceIte]
  rw [abs_mul, abs_of_nonneg hφ]
  have h1 : |z i * z i / t ^ 2 - 1 / t| ≤ (∑ i, z i ^ 2) / t ^ 2 + 1 / t := by
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), abs_of_pos (by positivity :
      (0 : ℝ) < 1 / t), abs_mul_self, ← sq]
    gcongr
  calc |z i * z i / t ^ 2 - 1 / t| * heatDensityPi t z
      ≤ ((∑ i, z i ^ 2) / t ^ 2 + 1 / t) * heatDensityPi t z := by gcongr
    _ = _ := by ring

end Posterior
/-! ### Ratio and logarithmic bounds -/

section Ratio

variable (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]

/-- The constant of a posterior second-moment bound at one point is nonnegative. -/
theorem nonneg_of_heatFlowM2Pi_le {r A : ℝ} (hr : 0 < r) (y : Fin d → ℝ)
    (h : heatFlowM2Pi π r y ≤ A * (1 + ∑ i, y i ^ 2) * heatFlowDensityPi π r y) : 0 ≤ A := by
  have hM := heatFlowM2Pi_nonneg π hr y
  have hq := heatFlowDensityPi_pos π hr y
  have hS : 0 < 1 + ∑ i, y i ^ 2 := by linarith [sum_sq_nonneg y]
  by_contra hneg
  push Not at hneg
  have : A * (1 + ∑ i, y i ^ 2) * heatFlowDensityPi π r y < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hS) hq
  linarith

/-- **Ratio bounds from the posterior bound.** If `PosteriorSecondMomentBoundPi π`, then for
`0 < a ≤ b` there is `B ≥ 0` with `(∂ᵢq_r/q_r)² ≤ B (1 + |y|²)`, `|∂ᵢq_r/q_r| ≤ B (1 + |y|²)`
and `|∂ᵢ²q_r/q_r| ≤ B (1 + |y|²)` for all `r ∈ [a, b]`, `y` and `i`. -/
theorem exists_ratio_le_post (hπ : PosteriorSecondMomentBoundPi π) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : ∃ B, 0 ≤ B ∧ ∀ r ∈ Icc a b, ∀ y i,
      (heatFlowGradPi π r y i / heatFlowDensityPi π r y) ^ 2 ≤ B * (1 + ∑ i, y i ^ 2) ∧
      |heatFlowGradPi π r y i / heatFlowDensityPi π r y| ≤ B * (1 + ∑ i, y i ^ 2) ∧
      |heatFlowHessPi π r y i i / heatFlowDensityPi π r y| ≤ B * (1 + ∑ i, y i ^ 2) := by
  obtain ⟨A, hA⟩ := hπ a b ha hab
  have hA0 := nonneg_of_heatFlowM2Pi_le π ha 0 (hA a ⟨le_rfl, hab⟩ 0)
  refine ⟨A / a ^ 2 + 1 / a + 1, by positivity, fun r hr y i => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hq := heatFlowDensityPi_pos π hr0 y
  set q := heatFlowDensityPi π r y
  set M := heatFlowM2Pi π r y
  set S := ∑ i, y i ^ 2
  set m := M / q with hm
  have hS : 1 ≤ 1 + S := by linarith [sum_sq_nonneg y]
  have hm0 : 0 ≤ m := div_nonneg (heatFlowM2Pi_nonneg π hr0 y) hq.le
  have hmA : m ≤ A * (1 + S) := by
    rw [hm, div_le_iff₀ hq]; exact hA r hr y
  have hmr : m / r ^ 2 ≤ A / a ^ 2 * (1 + S) := by
    calc m / r ^ 2 ≤ m / a ^ 2 :=
          div_le_div_of_nonneg_left hm0 (by positivity) (by nlinarith [hr.1])
      _ ≤ A * (1 + S) / a ^ 2 := by gcongr
      _ = _ := by ring
  have h1r : 1 / r ≤ 1 / a := one_div_le_one_div_of_le ha hr.1
  have hia : 0 ≤ 1 / a := by positivity
  have hAa : 0 ≤ A / a ^ 2 := by positivity
  have hw : (heatFlowGradPi π r y i / q) ^ 2 ≤ A / a ^ 2 * (1 + S) := by
    have hcs := sq_heatFlowGradPi_div_le_heatFlowM2Pi π hr0 y i
    have e : (heatFlowGradPi π r y i / q) ^ 2 = heatFlowGradPi π r y i ^ 2 / q / q := by
      field_simp
    have h2 : heatFlowGradPi π r y i ^ 2 / q / q ≤ M / r ^ 2 / q := by gcongr
    have e2 : M / r ^ 2 / q = m / r ^ 2 := by rw [hm]; ring
    rw [e]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · set w := heatFlowGradPi π r y i / q
    have : |w| ≤ 1 + w ^ 2 := by nlinarith [abs_nonneg w, sq_abs w, sq_nonneg (|w| - 1)]
    nlinarith
  · have hH := abs_heatFlowHessPi_le_heatFlowM2Pi π hr0 y i
    have e : M / r ^ 2 + q / r = (m / r ^ 2 + 1 / r) * q := by rw [hm]; field_simp
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    rw [e] at hH
    refine hH.trans (mul_le_mul_of_nonneg_right ?_ hq.le)
    nlinarith

/-- A probability measure on `Fin d → ℝ` gives positive mass to some ball
`{x | ∑ᵢ xᵢ² ≤ R}`. -/
theorem exists_measureReal_ball_pos : ∃ R : ℝ, 0 ≤ R ∧ 0 < π.real {x | ∑ i, x i ^ 2 ≤ R} := by
  have hU : (⋃ n : ℕ, {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ n}) = univ := eq_univ_of_forall fun x =>
    mem_iUnion.2 ⟨⌈∑ i, x i ^ 2⌉₊, Nat.le_ceil (∑ i, x i ^ 2)⟩
  have : ∃ n : ℕ, π {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ n} ≠ 0 := by
    by_contra h
    push Not at h
    have h0 := measure_iUnion_null h
    rw [hU] at h0
    simp at h0
  obtain ⟨n, hn⟩ := this
  exact ⟨n, n.cast_nonneg, ENNReal.toReal_pos hn (measure_ne_top _ _)⟩

/-- Locally uniform quadratic bound on `|log q_r|` for **every** probability `π`: for
`0 < a ≤ b` there is `L` with `|log q_r(y)| ≤ L (1 + |y|²)` for `r ∈ [a, b]`. The upper bound is
`q_r ≤ gc d a`; the lower bound is `q_r(y) ≥ π(B_R) gc d b exp(-(|y|² + R)/a)`. -/
theorem exists_abs_log_heatFlowDensityPi_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L, 0 ≤ L ∧ ∀ r ∈ Icc a b, ∀ y,
      |Real.log (heatFlowDensityPi π r y)| ≤ L * (1 + ∑ i, y i ^ 2) := by
  obtain ⟨R, hR, hm⟩ := exists_measureReal_ball_pos π
  have hb : 0 < b := ha.trans_le hab
  set B := {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ R}
  have hBm : MeasurableSet B :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  set m := π.real B
  set c := gc d b
  set ca := gc d a
  have hc0 : 0 < c := gc_pos hb
  have hca0 : 0 < ca := gc_pos ha
  set L := |Real.log ca| + |Real.log (c * m)| + R / a + 1 / a with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨L, hL0, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hp := heatFlowDensityPi_pos π hr0 y
  set S := ∑ i, y i ^ 2
  have hS := sum_sq_nonneg y
  -- upper bound
  have hup : heatFlowDensityPi π r y ≤ ca :=
    (heatFlowDensityPi_le π hr0 y).trans (gc_anti ha hr.1)
  have hlogup : Real.log (heatFlowDensityPi π r y) ≤ Real.log ca := Real.log_le_log hp hup
  -- lower bound
  set u := (S + R) / a with hu
  have hpt : ∀ x ∈ B, c * Real.exp (-u) ≤ heatDensityPi r (y - x) := by
    intro x hx
    rw [heatDensityPi_eq]
    have h2 : Real.exp (-u) ≤ Real.exp (-(∑ i, (y - x) i ^ 2) / (2 * r)) := by
      apply Real.exp_le_exp.2
      have hz := sum_sq_sub_le y x
      have hz0 := sum_sq_nonneg (y - x)
      have hx' : ∑ i, x i ^ 2 ≤ R := hx
      have e1 : (∑ i, (y - x) i ^ 2) / (2 * r) ≤ (∑ i, (y - x) i ^ 2) / (2 * a) :=
        div_le_div_of_nonneg_left hz0 (by positivity) (by linarith [hr.1])
      have e2 : (∑ i, (y - x) i ^ 2) / (2 * a) ≤ u := by
        rw [hu, div_le_div_iff₀ (by positivity) ha]
        nlinarith
      rw [neg_div]; linarith
    exact mul_le_mul (gc_anti hr0 hr.2) h2 (Real.exp_pos _).le (gc_pos hr0).le
  have hlow : c * Real.exp (-u) * m ≤ heatFlowDensityPi π r y := by
    have hi := integrable_heatDensityPi_comp_sub π hr0 y
    calc c * Real.exp (-u) * m ≤ ∫ x in B, heatDensityPi r (y - x) ∂π :=
          setIntegral_ge_of_const_le_real hBm (measure_ne_top _ _) hpt hi.integrableOn
      _ ≤ _ := setIntegral_le_integral hi
          (Eventually.of_forall fun x => (heatDensityPi_pos hr0 _).le)
  have hlogl : Real.log (c * m) - u ≤ Real.log (heatFlowDensityPi π r y) := by
    have := Real.log_le_log (by positivity) hlow
    rw [mul_comm c, mul_assoc, Real.log_mul (Real.exp_pos _).ne' (by positivity),
      Real.log_exp] at this
    linarith
  have hu' : u = R / a + 1 / a * S := by rw [hu]; ring
  have hA1 : 1 / a ≤ L := by
    have : 0 ≤ R / a := by positivity
    linarith [abs_nonneg (Real.log ca), abs_nonneg (Real.log (c * m))]
  have hyA : 1 / a * S ≤ L * S := mul_le_mul_of_nonneg_right hA1 hS
  have hLS : 0 ≤ L * S := mul_nonneg hL0 hS
  have hia : 0 ≤ 1 / a := by positivity
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (c * m)), abs_nonneg (Real.log ca)]
  · linarith [le_abs_self (Real.log ca), abs_nonneg (Real.log (c * m)),
      (by positivity : 0 ≤ R / a)]

end Ratio
/-! ### Pointwise domination of the de Bruijn integrands -/

section Integrands

variable {ρ π : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]

/-- **Log-ratio bound.** For probabilities `ρ, π` and `0 < a ≤ b` there is `L ≥ 0` with
`|log(p_r(y) / q_r(y)) + 1| ≤ L (1 + |y|²)` for all `r ∈ [a, b]` and `y`. -/
theorem exists_abs_log_div_add_one_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L, 0 ≤ L ∧ ∀ r ∈ Icc a b, ∀ y,
      |Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1| ≤
        L * (1 + ∑ i, y i ^ 2) := by
  obtain ⟨Lp, hLp0, hLp⟩ := exists_abs_log_heatFlowDensityPi_le ρ ha hab
  obtain ⟨Lq, hLq0, hLq⟩ := exists_abs_log_heatFlowDensityPi_le π ha hab
  refine ⟨Lp + Lq + 1, by positivity, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  rw [Real.log_div (heatFlowDensityPi_pos ρ hr0 y).ne' (heatFlowDensityPi_pos π hr0 y).ne']
  have h1 := hLp r hr y
  have h2 := hLq r hr y
  have hS : 1 ≤ 1 + ∑ i, y i ^ 2 := by linarith [sum_sq_nonneg y]
  calc _ ≤ |Real.log (heatFlowDensityPi ρ r y)| + |Real.log (heatFlowDensityPi π r y)| + 1 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_one]; linarith [abs_sub (Real.log (heatFlowDensityPi ρ r y))
          (Real.log (heatFlowDensityPi π r y))]
    _ ≤ Lp * (1 + ∑ i, y i ^ 2) + Lq * (1 + ∑ i, y i ^ 2) + 1 * (1 + ∑ i, y i ^ 2) := by
        linarith
    _ = _ := by ring

/-- **KL integrand.** For probabilities `ρ, π` with `∫ ∑ᵢ xᵢ² dρ < ∞` (no assumption on `π`
beyond being a probability) and `0 < a ≤ b`: `|p_r log(p_r/q_r)| ≤ C E_{2b}` on `[a, b]`. -/
theorem exists_abs_klIntegrand_le_any (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : ∃ C, ∀ r ∈ Icc a b, ∀ y,
      |klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) r y| ≤
        C * envBound ρ (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  refine ⟨(L + 1) * (2 * 1 * envK d a b), fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold klIntegrand
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have hX := hL r hr y
  have hP1 := one_add_mul_heatFlowDensityPi_le hmom ha hr.1 hr.2 y
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y)
  have hS := sum_sq_nonneg y
  have hX' : |X| ≤ (L + 1) * (1 + ∑ i, y i ^ 2) := by
    have := abs_sub (X + 1) 1
    rw [add_sub_cancel_right, abs_one] at this
    nlinarith
  rw [abs_mul, abs_of_nonneg hP]
  calc heatFlowDensityPi ρ r y * |X|
      ≤ heatFlowDensityPi ρ r y * ((L + 1) * (1 + ∑ i, y i ^ 2)) :=
        mul_le_mul_of_nonneg_left hX' hP
    _ = (L + 1) * ((1 + ∑ i, y i ^ 2) * heatFlowDensityPi ρ r y) := by ring
    _ ≤ (L + 1) * (2 * 1 * envK d a b * envBound ρ (2 * b) y) := by gcongr
    _ = _ := by ring

/-- **Time derivative of the KL integrand.** Under `PosteriorSecondMomentBoundPi π` and a finite
second moment of `ρ`: for `0 < a ≤ b`, `|klRate r y| ≤ C E_{2b}(y)` on `[a, b]`. -/
theorem exists_abs_klRate_le_post (hπ : PosteriorSecondMomentBoundPi π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C, ∀ r ∈ Icc a b, ∀ y,
      |klRate (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowHessPi ρ)
        (heatFlowHessPi π) r y| ≤ C * envBound ρ (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le_post π hπ ha hab
  refine ⟨(L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b)) +
    d * B * (2 * 1 * envK d a b)) / 2, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold klRate
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have hX := hL r hr y
  have hP1 := one_add_mul_heatFlowDensityPi_le hmom ha hr.1 hr.2 y
  have hΔ := one_add_mul_abs_lap_le hmom ha hr.1 hr.2 y
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1
  set S := ∑ i, y i ^ 2
  set E := envBound ρ (2 * b) y
  set K := envK d a b
  set Δ := ∑ i, heatFlowHessPi ρ r y i i
  have hS : 0 ≤ S := sum_sq_nonneg y
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hR : |heatFlowDensityPi ρ r y / heatFlowDensityPi π r y * ∑ i, heatFlowHessPi π r y i i|
      ≤ d * B * ((1 + S) * heatFlowDensityPi ρ r y) := by
    rw [mul_comm, mul_div_assoc', mul_comm, mul_div_assoc, Finset.sum_div, abs_mul,
      abs_of_nonneg hP]
    have : |∑ i, heatFlowHessPi π r y i i / heatFlowDensityPi π r y| ≤ d * (B * (1 + S)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (hB r hr y i).2.2).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_rfl
    calc heatFlowDensityPi ρ r y *
          |∑ i, heatFlowHessPi π r y i i / heatFlowDensityPi π r y|
        ≤ heatFlowDensityPi ρ r y * (d * (B * (1 + S))) := mul_le_mul_of_nonneg_left this hP
      _ = _ := by ring
  have hΔX : |Δ * X| ≤ L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * E)) := by
    rw [abs_mul]
    calc |Δ| * |X| ≤ |Δ| * (L * (1 + S)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = L * ((1 + S) * |Δ|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hΔ hL0
  have hR' : d * B * ((1 + S) * heatFlowDensityPi ρ r y) ≤ d * B * (2 * 1 * K * E) := by
    gcongr
  rw [abs_div, abs_two]
  have := abs_sub (Δ * X)
    (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y * ∑ i, heatFlowHessPi π r y i i)
  have e : (L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K)) + d * B * (2 * 1 * K)) / 2 * E =
      (L * (d * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * E)) + d * B * (2 * 1 * K * E)) / 2 := by
    ring
  rw [e]
  gcongr
  linarith

/-- **Relative score, one coordinate.** Under `PosteriorSecondMomentBoundPi π` and a finite
second moment of `ρ`: for `0 < a ≤ b`, `p_r (∂ᵢ log(p_r/q_r))² ≤ C E_{2b}` on `[a, b]`. -/
theorem exists_mul_relScore_sq_le_post (hπ : PosteriorSecondMomentBoundPi π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C, ∀ r ∈ Icc a b, ∀ y i,
      heatFlowDensityPi ρ r y * relScore (heatFlowDensityPi ρ) (heatFlowDensityPi π)
        (heatFlowGradPi ρ) (heatFlowGradPi π) r y i ^ 2 ≤ C * envBound ρ (2 * b) y := by
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le_post π hπ ha hab
  refine ⟨2 * (2 * a⁻¹ ^ 2 * envK d a b) + 2 * B * (2 * 1 * envK d a b),
    fun r hr y i => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold relScore
  have hP := heatFlowDensityPi_pos ρ hr0 y
  have hG := sq_heatFlowGradPi_div_le_envBound hmom ha hr.1 hr.2 y i
  have hP1 := one_add_mul_heatFlowDensityPi_le hmom ha hr.1 hr.2 y
  have hw := (hB r hr y i).1
  set A := heatFlowGradPi ρ r y i
  set P := heatFlowDensityPi ρ r y
  set w := heatFlowGradPi π r y i / heatFlowDensityPi π r y
  set E := envBound ρ (2 * b) y
  set K := envK d a b
  have hPA : P * (A / P) ^ 2 = A ^ 2 / P := by field_simp
  have hsq : (A / P - w) ^ 2 ≤ 2 * (A / P) ^ 2 + 2 * w ^ 2 := by
    nlinarith [sq_nonneg (A / P + w)]
  have hPw : P * w ^ 2 ≤ B * (2 * 1 * K * E) :=
    calc P * w ^ 2 ≤ P * (B * (1 + ∑ i, y i ^ 2)) := mul_le_mul_of_nonneg_left hw hP.le
      _ = B * ((1 + ∑ i, y i ^ 2) * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 hB0
  calc P * (A / P - w) ^ 2 ≤ P * (2 * (A / P) ^ 2 + 2 * w ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hP.le
    _ = 2 * (A ^ 2 / P) + 2 * (P * w ^ 2) := by rw [← hPA]; ring
    _ ≤ 2 * (2 * a⁻¹ ^ 2 * K * E) + 2 * (B * (2 * 1 * K * E)) := by linarith
    _ = _ := by ring

/-- **Relative Fisher integrand.** Under `PosteriorSecondMomentBoundPi π` and a finite second
moment of `ρ`: for `0 < a ≤ b`, `|p_r |∇ log(p_r/q_r)|²| ≤ C E_{2b}` on `[a, b]`. -/
theorem exists_abs_fisherIntegrand_le_post (hπ : PosteriorSecondMomentBoundPi π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C, ∀ r ∈ Icc a b, ∀ y,
      |fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
        (heatFlowGradPi ρ) (heatFlowGradPi π) r y| ≤ C * envBound ρ (2 * b) y := by
  obtain ⟨C, hC⟩ := exists_mul_relScore_sq_le_post hπ hmom ha hab
  refine ⟨d * C, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have e : fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
      (heatFlowGradPi ρ) (heatFlowGradPi π) r y = ∑ i, heatFlowDensityPi ρ r y *
        relScore (heatFlowDensityPi ρ) (heatFlowDensityPi π)
          (heatFlowGradPi ρ) (heatFlowGradPi π) r y i ^ 2 := by
    rw [fisherIntegrand, dotProduct, Finset.mul_sum]; simp only [sq]
  rw [e, abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg hP (sq_nonneg _))]
  calc _ ≤ ∑ _i : Fin d, C * envBound ρ (2 * b) y := Finset.sum_le_sum fun i _ => hC r hr y i
    _ = _ := by simp [mul_assoc]

/-- **KL flux.** Under `PosteriorSecondMomentBoundPi π` and a finite second moment of `ρ`: for
`0 < a ≤ b`, `|klFlux r i y| ≤ C E_{2b}(y)` on `[a, b]`. -/
theorem exists_abs_klFlux_le_post (hπ : PosteriorSecondMomentBoundPi π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C, ∀ r ∈ Icc a b, ∀ i y,
      |klFlux (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
        (heatFlowGradPi π) r i y| ≤ C * envBound ρ (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le_post π hπ ha hab
  refine ⟨L * (2 * a⁻¹ * envK d a b) + B * (2 * 1 * envK d a b), fun r hr i y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  unfold klFlux
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have hX := hL r hr y
  have hP1 := one_add_mul_heatFlowDensityPi_le hmom ha hr.1 hr.2 y
  have hG := one_add_mul_abs_heatFlowGradPi_le hmom ha hr.1 hr.2 y i
  have hw := (hB r hr y i).2.1
  have e : heatFlowDensityPi ρ r y / heatFlowDensityPi π r y * heatFlowGradPi π r y i =
      heatFlowDensityPi ρ r y * (heatFlowGradPi π r y i / heatFlowDensityPi π r y) := by ring
  rw [e]
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1
  set S := ∑ i, y i ^ 2
  set E := envBound ρ (2 * b) y
  set K := envK d a b
  set G := heatFlowGradPi ρ r y i
  set P := heatFlowDensityPi ρ r y
  set w := heatFlowGradPi π r y i / heatFlowDensityPi π r y
  have h1 : |G * X| ≤ L * (2 * a⁻¹ * K * E) := by
    rw [abs_mul]
    calc |G| * |X| ≤ |G| * (L * (1 + S)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = L * ((1 + S) * |G|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hG hL0
  have h2 : |P * w| ≤ B * (2 * 1 * K * E) := by
    rw [abs_mul, abs_of_nonneg hP]
    calc P * |w| ≤ P * (B * (1 + S)) := mul_le_mul_of_nonneg_left hw hP
      _ = B * ((1 + S) * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 hB0
  calc |G * X - P * w| ≤ |G * X| + |P * w| := abs_sub _ _
    _ ≤ L * (2 * a⁻¹ * K * E) + B * (2 * 1 * K * E) := add_le_add h1 h2
    _ = _ := by ring

/-- **Divergence terms of the KL flux.** Under `PosteriorSecondMomentBoundPi π` and a finite
second moment of `ρ`: for `0 < a ≤ b`, `|klFluxDeriv r i y| ≤ C E_{2b}(y)` on `[a, b]`. -/
theorem exists_abs_klFluxDeriv_le_post (hπ : PosteriorSecondMomentBoundPi π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C, ∀ r ∈ Icc a b, ∀ i y,
      |klFluxDeriv (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
        (heatFlowGradPi π) (heatFlowHessPi ρ) (heatFlowHessPi π) r i y|
        ≤ C * envBound ρ (2 * b) y := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_div_add_one_le (ρ := ρ) (π := π) ha hab
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le_post π hπ ha hab
  obtain ⟨C, hC⟩ := exists_mul_relScore_sq_le_post hπ hmom ha hab
  refine ⟨L * (2 * (a⁻¹ ^ 2 + a⁻¹) * envK d a b) + B * (2 * 1 * envK d a b) + C,
    fun r hr i y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hRS := hC r hr y i
  unfold klFluxDeriv
  have hP := (heatFlowDensityPi_pos ρ hr0 y).le
  have hX := hL r hr y
  have hP1 := one_add_mul_heatFlowDensityPi_le hmom ha hr.1 hr.2 y
  have hH := one_add_mul_abs_heatFlowHessPi_le hmom ha hr.1 hr.2 y i
  have hQH := (hB r hr y i).2.2
  have e : heatFlowDensityPi ρ r y / heatFlowDensityPi π r y * heatFlowHessPi π r y i i =
      heatFlowDensityPi ρ r y * (heatFlowHessPi π r y i i / heatFlowDensityPi π r y) := by
    ring
  rw [e]
  set X := Real.log (heatFlowDensityPi ρ r y / heatFlowDensityPi π r y) + 1
  set S := ∑ i, y i ^ 2
  set E := envBound ρ (2 * b) y
  set K := envK d a b
  set H := heatFlowHessPi ρ r y i i
  set P := heatFlowDensityPi ρ r y
  set h := heatFlowHessPi π r y i i / heatFlowDensityPi π r y
  set R := relScore (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
    (heatFlowGradPi π) r y i
  have h1 : |H * X| ≤ L * (2 * (a⁻¹ ^ 2 + a⁻¹) * K * E) := by
    rw [abs_mul]
    calc |H| * |X| ≤ |H| * (L * (1 + S)) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = L * ((1 + S) * |H|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hH hL0
  have h2 : |P * h| ≤ B * (2 * 1 * K * E) := by
    rw [abs_mul, abs_of_nonneg hP]
    calc P * |h| ≤ P * (B * (1 + S)) := mul_le_mul_of_nonneg_left hQH hP
      _ = B * ((1 + S) * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 hB0
  have h3 : |P * R ^ 2| ≤ C * E := by
    rw [abs_of_nonneg (mul_nonneg hP (sq_nonneg _))]; exact hRS
  calc |H * X - P * h + P * R ^ 2| ≤ |H * X| + |P * h| + |P * R ^ 2| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end Integrands
/-! ### De Bruijn regularity under the posterior bound -/

/-- **De Bruijn regularity under a posterior second-moment bound (Verified).** For probability
measures `ρ, π` on `Fin d → ℝ` with `∫ ∑ᵢ xᵢ² dρ < ∞` and `PosteriorSecondMomentBoundPi π`, all
hypotheses of `HeatFlowRegularPi` hold at every positive time: `HeatFlowRegularPi ρ π (Ioi 0)`.
Every integrand at times `r ∈ [a, b] ⊂ (0, ∞)` is bounded by `C E_{2b}` with `E_c` the Lebesgue
integrable envelope `HeatFlowRegularityPi.envBound ρ c`; the `klRate` domination near `t` uses
`[a, b] = [t/2, 2t]`. -/
theorem heatFlowRegularPi_of_posteriorSecondMomentBoundPi (ρ π : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] (hπ : PosteriorSecondMomentBoundPi π)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) : HeatFlowRegularPi ρ π (Ioi 0) := by
  have key : ∀ {t : ℝ}, 0 < t → ∀ {F : (Fin d → ℝ) → ℝ}, Measurable F →
      (∃ C, ∀ y, |F y| ≤ C * envBound ρ (2 * t) y) → Integrable F := by
    intro t ht F hF ⟨C, hC⟩
    exact ((integrable_envBound hmom (by positivity : 0 < 2 * t)).const_mul C).mono'
      hF.aestronglyMeasurable (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hC y)
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
  · obtain ⟨C, hC⟩ := exists_abs_klIntegrand_le_any (π := π) hmom ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    exact key ht (by unfold klIntegrand; fun_prop) ⟨C, hC t mem⟩
  · have ht0 : 0 < t := ht
    obtain ⟨C, hC⟩ := exists_abs_klRate_le_post hπ hmom (a := t / 2) (b := 2 * t)
      (by positivity) (by linarith)
    refine ⟨fun y => C * envBound ρ (2 * (2 * t)) y,
      (integrable_envBound hmom (by positivity)).const_mul C, ?_⟩
    filter_upwards [Ioo_mem_nhds (by linarith : t / 2 < t) (by linarith : t < 2 * t)] with r hr y
    exact hC r ⟨hr.1.le, hr.2.le⟩ y
  · obtain ⟨C, hC⟩ := exists_abs_fisherIntegrand_le_post hπ hmom ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    have h3 := hGm ρ ht; have h4 := hGm π ht
    exact key ht (by unfold fisherIntegrand relScore; simp only [dotProduct]; fun_prop)
      ⟨C, hC t mem⟩
  · obtain ⟨C, hC⟩ := exists_abs_klFlux_le_post hπ hmom ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    have h3 := hGm ρ ht; have h4 := hGm π ht
    exact key ht (by unfold klFlux; fun_prop) ⟨C, fun y => hC t mem i y⟩
  · obtain ⟨C, hC⟩ := exists_abs_klFluxDeriv_le_post hπ hmom ht (le_refl t)
    have h1 := hPm ρ ht; have h2 := hPm π ht
    have h3 := hGm ρ ht; have h4 := hGm π ht
    have h5 := hHm ρ ht; have h6 := hHm π ht
    exact key ht (by unfold klFluxDeriv relScore; fun_prop) ⟨C, fun y => hC t mem i y⟩

/-! ### Gaussian targets and two-sided comparison -/

/-- `Δq_t = M_t / t² - d q_t / t` for a probability `π` and `t > 0`. -/
theorem sum_heatFlowHessPi_eq (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] {t : ℝ}
    (ht : 0 < t) (y : Fin d → ℝ) :
    ∑ i, heatFlowHessPi π t y i i = heatFlowM2Pi π t y / t ^ 2 - d * heatFlowDensityPi π t y / t
    := by
  have hI : ∀ i, Integrable (fun x => heatHessPi t (y - x) i i) π := fun i =>
    integrable_comp_sub_of_bound π (k := fun z => heatHessPi t z i i)
      (continuous_heatHessPi t i i) (abs_heatHessPi_le ht · i i) y
  unfold heatFlowHessPi heatFlowM2Pi heatFlowDensityPi
  rw [← integral_finsetSum _ fun i _ => hI i, ← integral_div, ← integral_const_mul,
    ← integral_div, ← integral_sub ((integrable_sum_sq_mul_heatDensityPi π ht y).div_const _)
      (((integrable_heatDensityPi_comp_sub π ht y).const_mul _).div_const _)]
  congr 1
  funext x
  simp only [heatHessPi, ↓reduceIte, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div,
    ← pow_two]
  ring

/-- **Isotropic Gaussian targets satisfy the posterior bound.** For `v > 0`, `N(0, v I)` satisfies
`PosteriorSecondMomentBoundPi` with `A = 1 + d b` on `[a, b]`: explicitly
`M_r(y) = (r² |y|²/(v + r)² - r² d/(v + r) + d r) φ_{v + r}(y)`. -/
theorem posteriorSecondMomentBoundPi_gaussian {v : ℝ} (hv : 0 < v) :
    PosteriorSecondMomentBoundPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) := by
  intro a b ha hab
  have hb : 0 < b := ha.trans_le hab
  refine ⟨1 + d * b, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hc : 0 < v + r := by linarith
  have hD := sum_heatFlowHessPi_eq (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) hr0 y
  rw [heatFlowHessPi_gaussian hv hr0, heatFlowDensityPi_gaussian hv hr0] at hD
  rw [heatFlowDensityPi_gaussian hv hr0]
  set M := heatFlowM2Pi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) r y
  set φ := heatDensityPi (v + r) y
  set S := ∑ i, y i ^ 2
  have hφ : 0 < φ := heatDensityPi_pos hc y
  have hS : 0 ≤ S := sum_sq_nonneg y
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL : ∑ i, heatHessPi (v + r) y i i = (S / (v + r) ^ 2 - d / (v + r)) * φ := by
    simp only [heatHessPi, ↓reduceIte, ← Finset.sum_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, S,
      φ, ← pow_two]
    ring
  rw [hL] at hD
  have hM : M = (r ^ 2 * (S / (v + r) ^ 2) - r ^ 2 * (d / (v + r)) + d * r) * φ := by
    have : M / r ^ 2 = (S / (v + r) ^ 2 - d / (v + r)) * φ + d * φ / r := by linarith
    field_simp at this ⊢
    linarith
  have h1 : r ^ 2 * (S / (v + r) ^ 2) ≤ S := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : r ^ 2 ≤ (v + r) ^ 2 := by nlinarith
    nlinarith
  have h2 : 0 ≤ r ^ 2 * (d / (v + r)) := by positivity
  have h3 : d * r ≤ d * b := mul_le_mul_of_nonneg_left hr.2 hd
  have hpoly : r ^ 2 * (S / (v + r) ^ 2) - r ^ 2 * (d / (v + r)) + d * r ≤
      (1 + d * b) * (1 + S) := by
    nlinarith [mul_nonneg (mul_nonneg hd hb.le) hS]
  rw [hM]
  exact mul_le_mul_of_nonneg_right hpoly hφ.le

end FormalizeSampling.HeatFlowRegularityPerturbedPi

/-! ### The isotropic Gaussian target (statements in the namespace `HeatFlowRegularityPi`) -/

namespace FormalizeSampling.HeatFlowRegularityPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi FormalizeSampling.HeatFlowRegularityPerturbedPi

variable {d : ℕ}

/-- **`HeatFlowRegularPi` for an isotropic Gaussian target (Verified).** For every probability
measure `ρ` on `Fin d → ℝ` with finite second moment `∫ ∑ᵢ xᵢ² dρ < ∞` and every `v > 0`, the de
Bruijn regularity hypotheses hold for `π = N(0, v I)` at all positive times:
`HeatFlowRegularPi ρ N(0, v I) (Ioi 0)`. No density, smoothness or KL assumption on `ρ` is used.
This is `heatFlowRegularPi_of_posteriorSecondMomentBoundPi` with
`posteriorSecondMomentBoundPi_gaussian`. -/
theorem heatFlowRegularPi_gaussian (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {v : ℝ} (hv : 0 < v) :
    HeatFlowRegularPi ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) (Ioi 0) :=
  heatFlowRegularPi_of_posteriorSecondMomentBoundPi ρ _
    (posteriorSecondMomentBoundPi_gaussian hv) hmom

/-- **KL is finite along the isotropic heat flow for a Gaussian target.** For a probability
measure `ρ` on `Fin d → ℝ` with finite second moment, `π = N(0, v I)` (`v > 0`) and `t > 0`,
`KL(ρ_t‖π_t) = KL(heatKernelPi t ∘ₘ ρ‖heatKernelPi t ∘ₘ N(0, v I)) ≠ ∞`. Hence `heatKL ρ π t` is
the real value of a finite divergence. -/
theorem klDiv_heatKernelPi_comp_ne_top_of_moment (ρ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] {v : ℝ} (hv : 0 < v) (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {t : ℝ} (ht : 0 < t) :
    klDiv (heatKernelPi t.toNNReal ∘ₘ ρ)
      (heatKernelPi t.toNNReal ∘ₘ Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ≠ ⊤ :=
  klDiv_heatKernelPi_comp_ne_top_of_regular (heatFlowRegularPi_gaussian ρ hmom hv)
    (show t ∈ Ioi 0 from ht)

end FormalizeSampling.HeatFlowRegularityPi
