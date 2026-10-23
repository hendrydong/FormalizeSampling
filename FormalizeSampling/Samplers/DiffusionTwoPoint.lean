module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import FormalizeSampling.Samplers.DiffusionDiscretizationOU
public import FormalizeSampling.Samplers.DiffusionODELipschitz
public import FormalizeSampling.Samplers.DiffusionODESeparation
public import FormalizeSampling.Samplers.ShiftedCompositionPi

/-!
# Diffusion samplers on symmetric two-point data: forward marginals, score, probability-flow step

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean` with the symmetric two-point data law
`μ = (δ_{-a} + δ_a)/2` on `Fin d → ℝ` (`symTwoPoint a`) and a time grid with `t_0 = 0`. Write
`ᾱ_k = e^{-t_k}` (`cumScale`) and `v_k = 1 - e^{-2 t_k}` (`cumVar`) for the cumulative
contraction factor and noise variance of the forward OU chain (`ᾱ_k² + v_k = 1`; one forward step
multiplies `ᾱ` by `α_k` and maps `v` to `α_k² v + β_k`), and `φ_v = heatDensityPi v` for the
density of `N(0, v I)`.

* **Forward marginals.** On a monotone grid, `p_k = (N(-ᾱ_k a, v_k I) + N(ᾱ_k a, v_k I))/2` for
  every `k` (law equality), through the OU form of the forward chain
  (`DiffusionDiscretization.fwdLaw_eq_ouKernelVarPi_comp`).
* **Density.** On a strictly increasing grid and for `k ≥ 1`, the forward density `fwdDensity`
  (the continuous Lebesgue density of `p_k`) is, pointwise,
  `p_k(y) = (φ_{v_k}(y + ᾱ_k a) + φ_{v_k}(y - ᾱ_k a))/2
    = φ_{v_k}(y) e^{-ᾱ_k² |a|²/(2 v_k)} cosh(ᾱ_k ⟨a, y⟩ / v_k)`.
* **Score.** `∇ log p_k(y) = (-y + ᾱ_k a tanh(ᾱ_k ⟨a, y⟩ / v_k)) / v_k` for every `y`.
* **Probability-flow step, `d = 1`.** For `a : ℝ` and data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`,
  the exponential-integrator step `pfMean` driven by the exact score acts on the coordinate as
  the scalar map `x ↦ A x + b (-x + m tanh(m x / v)) / v` (`mixMap`, `pfTwoPoint`) with
  `A = α_k⁻¹`, `b = b_k = α_k⁻¹ - 1` (`pfCoeff`), `m = ᾱ_k a`, `v = v_k`. This is one step
  of the exponential integrator, not the flow map of the probability-flow ODE. On a strictly
  increasing grid with `t_0 = 0` and for `k ≥ 1`, the map is odd and strictly increasing: its
  lower slope is `A - b/v = (1 - e^{-(t_k + t_{k-1})})/v_k > 0` (in particular `b/v ≤ A`, which
  reduces to `ᾱ_k² ≤ α_k`). It has increments between `(A - b/v)(y - x)` and
  `(A - b/v + b m²/v²)(y - x)` for `x ≤ y`, hence slopes between `A - b/v` and
  `A + b (m²/v - 1)/v` on `x ≥ 0`, and is Lipschitz with constant `A - b/v + b m²/v²`.
* **Composition of the exact-score steps, `d = 1`.** Write `L_k = A - b/v + b m²/v²`
  (`lipTwoPoint`) for the Lipschitz constant of step `k` and `f(s) = e^{2s}/(e^{2s} - 1)²`, so
  that `ᾱ_k²/v_k² = f(t_k)`. The lower slope `A - b/v` is at most `1`, hence
  `0 ≤ L_k ≤ 1 + b_k a² f(t_k)`. If every step `t_k - t_{k-1}`, `1 < k ≤ K`, is at most `log 2`,
  then `b_k ≤ 2 (t_k - t_{k-1})`; since `f` is decreasing with antiderivative
  `F(s) = -1/(2 (e^{2s} - 1))`, `(t_k - t_{k-1}) f(t_k) ≤ F(t_k) - F(t_{k-1})` and the sum
  telescopes: `∑_{1 < k ≤ K} b_k a² f(t_k) ≤ a²/(e^{2 t_1} - 1)`. So the composed exact-score
  flow `Φ = m_2 ∘ ⋯ ∘ m_K` (`detFlow` from index `K` to index `1`) is odd, fixes `0` and is
  Lipschitz with constant `∏_{1 < k ≤ K} L_k ≤ exp(a²/(e^{2 t_1} - 1))`, for every `K` and every
  such grid: the constant depends on `a` and `t_1` only.

The scalar statements are proved for the general map `mixMap A b m v` (any `A`, `b ≥ 0`,
`v > 0`, any `m`) and then specialised to the grid (`pfTwoPoint_*`). The facts about
`Real.tanh` used here (derivative `1/cosh²`, strict monotonicity, `0 ≤ tanh x ≤ x` for `x ≥ 0`,
`1`-Lipschitz) are proved in the first section.

## Main results

* `tanh`: `hasDerivAt_tanh`, `strictMono_tanh`, `tanh_nonneg`, `tanh_le_self`,
  `tanh_sub_tanh_le`, `lipschitzWith_tanh`.
* Grid quantities: `cumScale`, `cumVar`, `cumScale_sq_add_cumVar`, `cumScale_succ`,
  `cumVar_succ`, `cumScale_one`, `cumVar_one`, `cumVar_pos`.
* Data law: `symTwoPoint`, `integral_symTwoPoint`, `comp_symTwoPoint`,
  `map_scalePi_symTwoPoint`, `integrable_sum_sq_symTwoPoint`, `symTwoPoint_not_ac`.
* Forward marginals: `fwdLaw_symTwoPoint`, `fwdLaw_symTwoPoint_ac`.
* Density: `fwdDensity_symTwoPoint`, `fwdDensity_symTwoPoint_eq_cosh`,
  `fwdDensity_symTwoPoint_one` (`d = 1`, with `gaussianPDFReal`); positivity is the general
  `DiffusionDiscretization.fwdDensity_pos_of_one_le`.
* Score: `score_fwdDensity_symTwoPoint`, `score_fwdDensity_symTwoPoint_one`,
  `exactScore_symTwoPoint_one` (`= mixScore (ᾱ_k a) v_k`).
* Scalar map: `mixMap_eq`, `abs_mixMap_sub_linear_le`, `mixMap_neg`, `mixMap_sub_bounds`,
  `monotone_mixMap`, `strictMono_mixMap`, `lipschitzWith_mixMap`, `lipschitzWith_mixMap_of_le`,
  `mixMap_bounds_of_nonneg`, `continuous_mixMap`.
* Probability-flow step: `pfMean_exactScore_symTwoPoint`,
  `pfMean_exactScore_symTwoPoint_apply`, `pfMean_exactScore_symTwoPoint_neg`, `pfTwoPoint_eq`,
  `pfCoeff_nonneg`, `pfCoeff_div_cumVar_le`, `pfCoeff_div_cumVar_lt`,
  `inv_fwdScale_sub_pfCoeff_div_cumVar`, `inv_fwdScale_sub_pfCoeff_div_cumVar_pos`,
  `pfTwoPoint_neg`, `pfTwoPoint_sub_bounds`, `monotone_pfTwoPoint`, `strictMono_pfTwoPoint`,
  `lipschitzWith_pfTwoPoint`, `pfTwoPoint_bounds_of_nonneg`,
  `pfMean_exactScore_symTwoPoint_bounds`,
  `eDist_pfMean_exactScore_symTwoPoint_le` (Euclidean form on `Fin 1 → ℝ`).
* Step constants: `lipTwoPoint`, `inv_fwdScale_sub_pfCoeff_div_cumVar_le_one`,
  `lipTwoPoint_bounds`, `pfCoeff_le_two_mul_sub`, `sub_mul_exp_div_sq_le`,
  `cumScale_sq_div_cumVar_sq`, `sum_pfCoeff_mul_sq_div_le`, `prod_lipTwoPoint_le`.
* Composed flows: `detFlow_apply_neg` and `eDist_detFlow_apply_le` (any reverse maps: odd steps
  give an odd flow, `L_i`-Lipschitz steps a `∏ L_i`-Lipschitz flow);
  `detFlow_pfMean_exactScore_symTwoPoint_neg`, `detFlow_pfMean_exactScore_symTwoPoint_zero`,
  `eDist_detFlow_pfMean_exactScore_symTwoPoint_le`,
  `eDist_detFlow_pfMean_exactScore_symTwoPoint_le_exp`,
  `abs_detFlow_pfMean_exactScore_symTwoPoint_le` (`|Φ(y)_0| ≤ exp(a²/(e^{2 t_1} - 1)) |y_0|`).

## Not proved here

* Nothing about the output law of a sampler: the perturbation of the steps by a learned score
  and comparisons with `p_1` are not formalised here (for a clamp error switched on at high
  noise, see `Samplers/DiffusionODEMidpoint.lean`). Of the composition of the exact-score
  steps over the grid, only oddness and the Lipschitz bound are proved; the bound
  `exp(a²/(e^{2 t_1} - 1))` is an upper bound, not shown to be attained.
* Asymmetric or weighted two-point data and data with more than two atoms.
* The probability-flow statements for `d ≥ 2` (the forward law, density and score are proved
  for every `d`; the scalar reduction uses `d = 1`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionTwoPoint

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
  FormalizeSampling.DiffusionODESeparation FormalizeSampling.HeatKernelPi
  FormalizeSampling.HeatFlowDeBruijnPi FormalizeSampling.OULangevinDecayPi
open FormalizeSampling.ProbabilityFlowOU (ouDensity ouGrad ouLaw ouS ouC score_ouDensity)

variable {d : ℕ}

/-! ### Elementary facts about `tanh` -/

/-- The derivative of `tanh`: `tanh'(x) = 1 / cosh² x`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh ((Real.cosh x ^ 2)⁻¹) x := by
  have e : Real.tanh = fun y => Real.sinh y / Real.cosh y :=
    funext fun y => Real.tanh_eq_sinh_div_cosh y
  rw [e]
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne' using 1
  rw [← sq, ← sq, Real.cosh_sq x]
  ring

/-- `tanh` is differentiable. -/
theorem differentiable_tanh : Differentiable ℝ Real.tanh := fun x =>
  (hasDerivAt_tanh x).differentiableAt

/-- `tanh` is continuous. -/
theorem continuous_tanh : Continuous Real.tanh := differentiable_tanh.continuous

/-- `tanh` is strictly increasing. -/
theorem strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_tanh x).deriv]
    exact inv_pos.2 (pow_pos (Real.cosh_pos x) 2)

/-- `tanh x ≥ 0` for `x ≥ 0`. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa [Real.tanh_zero] using strictMono_tanh.monotone hx

/-- Increments of `tanh` are at most the increments of the argument: for `x ≤ y`,
`tanh y - tanh x ≤ y - x`. -/
theorem tanh_sub_tanh_le {x y : ℝ} (hxy : x ≤ y) : Real.tanh y - Real.tanh x ≤ y - x := by
  have hm : Monotone fun z => z - Real.tanh z := by
    refine monotone_of_deriv_nonneg (differentiable_id.sub differentiable_tanh) fun z => ?_
    have hd : HasDerivAt (fun z => z - Real.tanh z) (1 - (Real.cosh z ^ 2)⁻¹) z :=
      (hasDerivAt_id' z).sub (hasDerivAt_tanh z)
    rw [hd.deriv]
    have h1 : 1 ≤ Real.cosh z ^ 2 := by nlinarith [Real.one_le_cosh z]
    have h2 : (Real.cosh z ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    linarith
  have := hm hxy
  simp only at this
  linarith

/-- `tanh x ≤ x` for `x ≥ 0`. -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  simpa [Real.tanh_zero] using tanh_sub_tanh_le hx

/-- `tanh` is `1`-Lipschitz: `|tanh x - tanh y| ≤ |x - y|`. -/
theorem abs_tanh_sub_tanh_le (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_sub_comm x, abs_of_nonneg (sub_nonneg.2 h),
      abs_of_nonneg (sub_nonneg.2 (strictMono_tanh.monotone h))]
    exact tanh_sub_tanh_le h
  · rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg (sub_nonneg.2 (strictMono_tanh.monotone h))]
    exact tanh_sub_tanh_le h

/-- `tanh` is `1`-Lipschitz. -/
theorem lipschitzWith_tanh : LipschitzWith 1 Real.tanh :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Real.dist_eq] using abs_tanh_sub_tanh_le x y

/-! ### Cumulative scale and variance -/

/-- The cumulative OU contraction factor at time `t_k`: `ᾱ_k = e^{-t_k}`. -/
noncomputable def cumScale (t : ℕ → ℝ) (k : ℕ) : ℝ := Real.exp (-t k)

/-- The cumulative OU noise variance at time `t_k`: `v_k = 1 - e^{-2 t_k}`. -/
noncomputable def cumVar (t : ℕ → ℝ) (k : ℕ) : ℝ := 1 - Real.exp (-2 * t k)

/-- `ᾱ_k > 0`. -/
theorem cumScale_pos (t : ℕ → ℝ) (k : ℕ) : 0 < cumScale t k := Real.exp_pos _

/-- `ᾱ_k ≤ 1` when `t_k ≥ 0`. -/
theorem cumScale_le_one {t : ℕ → ℝ} {k : ℕ} (htk : 0 ≤ t k) : cumScale t k ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

/-- `v_k > 0` when `t_k > 0`. -/
theorem cumVar_pos {t : ℕ → ℝ} {k : ℕ} (htk : 0 < t k) : 0 < cumVar t k := by
  rw [cumVar, sub_pos, Real.exp_lt_one_iff]
  linarith

/-- `v_k ≥ 0` when `t_k ≥ 0`. -/
theorem cumVar_nonneg {t : ℕ → ℝ} {k : ℕ} (htk : 0 ≤ t k) : 0 ≤ cumVar t k := by
  rw [cumVar, sub_nonneg, Real.exp_le_one_iff]
  linarith

/-- `v_k < 1`. -/
theorem cumVar_lt_one (t : ℕ → ℝ) (k : ℕ) : cumVar t k < 1 := by
  rw [cumVar]
  linarith [Real.exp_pos (-2 * t k)]

/-- `ᾱ_k² + v_k = 1`. -/
theorem cumScale_sq_add_cumVar (t : ℕ → ℝ) (k : ℕ) : cumScale t k ^ 2 + cumVar t k = 1 := by
  rw [cumScale, cumVar, ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- One forward step: `ᾱ_{k+1} = α_{k+1} ᾱ_k`. -/
theorem cumScale_succ (t : ℕ → ℝ) (k : ℕ) :
    cumScale t (k + 1) = fwdScale t (k + 1) * cumScale t k := by
  rw [cumScale, cumScale, fwdScale, ← Real.exp_add, Nat.add_sub_cancel]
  ring_nf

/-- One forward step: `v_{k+1} = α_{k+1}² v_k + β_{k+1}`. -/
theorem cumVar_succ (t : ℕ → ℝ) (k : ℕ) :
    cumVar t (k + 1) = fwdScale t (k + 1) ^ 2 * cumVar t k + fwdVar t (k + 1) := by
  have h1 := cumScale_sq_add_cumVar t (k + 1)
  have h2 := cumScale_sq_add_cumVar t k
  rw [cumScale_succ] at h1
  rw [fwdVar]
  linear_combination h1 - fwdScale t (k + 1) ^ 2 * h2

/-- At the first grid point (`t_0 = 0`): `ᾱ_1 = α_1`. -/
theorem cumScale_one {t : ℕ → ℝ} (h0 : t 0 = 0) : cumScale t 1 = fwdScale t 1 := by
  rw [cumScale, fwdScale, Nat.sub_self, h0, sub_zero]

/-- At the first grid point (`t_0 = 0`): `v_1 = β_1`. -/
theorem cumVar_one {t : ℕ → ℝ} (h0 : t 0 = 0) : cumVar t 1 = fwdVar t 1 := by
  rw [fwdVar, ← cumScale_one h0, ← cumScale_sq_add_cumVar t 1]
  ring

/-- `ouC 1 (t_k) = ᾱ_k`. -/
theorem ouC_eq_cumScale (t : ℕ → ℝ) (k : ℕ) : ouC 1 (t k) = cumScale t k := by
  simp [ouC, cumScale]

/-- `ouS 1 1 (t_k) = v_k`. -/
theorem ouS_eq_cumVar (t : ℕ → ℝ) (k : ℕ) : ouS 1 1 (t k) = cumVar t k := by
  simp [ouS, cumVar]

/-! ### The symmetric two-point data law -/

/-- The symmetric two-point law `(δ_{-a} + δ_a) / 2` on `Fin d → ℝ`. -/
noncomputable def symTwoPoint (a : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (-a) + (2⁻¹ : ℝ≥0∞) • Measure.dirac a

/-- The symmetric two-point law is a probability measure. -/
instance isProbabilityMeasure_symTwoPoint (a : Fin d → ℝ) :
    IsProbabilityMeasure (symTwoPoint a) :=
  ⟨by simp [symTwoPoint, ENNReal.inv_two_add_inv_two]⟩

/-- The symmetric two-point law has a finite second moment. -/
theorem integrable_sum_sq_symTwoPoint (a : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ => ∑ i, x i ^ 2) (symTwoPoint a) :=
  ((integrable_dirac enorm_lt_top).smul_measure (by simp)).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure (by simp))

/-- Integrals against the two-point law: `∫ f d((δ_{-a} + δ_a)/2) = (f(-a) + f(a))/2`. -/
theorem integral_symTwoPoint (a : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) :
    ∫ x, f x ∂(symTwoPoint a) = 2⁻¹ * f (-a) + 2⁻¹ * f a := by
  have hi : ∀ x : Fin d → ℝ, Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac x) := fun x =>
    (integrable_dirac enorm_lt_top).smul_measure (by simp)
  rw [symTwoPoint, integral_add_measure (hi _) (hi _), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp

/-- Kernels against the two-point law: `κ ∘ₘ ((δ_{-a} + δ_a)/2) = (κ(-a) + κ(a))/2`. -/
theorem comp_symTwoPoint (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) (a : Fin d → ℝ) :
    κ ∘ₘ symTwoPoint a = (2⁻¹ : ℝ≥0∞) • κ (-a) + (2⁻¹ : ℝ≥0∞) • κ a := by
  rw [symTwoPoint, Measure.comp_add, Measure.comp_smul, Measure.comp_smul,
    Measure.dirac_bind κ.measurable, Measure.dirac_bind κ.measurable]

/-- Scaling maps a two-point law to a two-point law: `(c ·)_# μ_a = μ_{c a}`. -/
theorem map_scalePi_symTwoPoint (c : ℝ) (a : Fin d → ℝ) :
    (symTwoPoint a).map (ProximalSharpGaussianPi.scalePi c) = symTwoPoint (c • a) := by
  have hm := ProximalSharpGaussianPi.measurable_scalePi (d := d) c
  rw [symTwoPoint, symTwoPoint, Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
    Measure.map_smul _ hm.aemeasurable, Measure.map_dirac' hm, Measure.map_dirac' hm,
    scalePi_eq_smul, scalePi_eq_smul, smul_neg]

/-! ### Forward marginals -/

/-- **Forward marginals of two-point data.** If `t_0 = 0` and `t` is monotone, then for every `k`
the forward marginal of `(δ_{-a} + δ_a)/2` is the Gaussian mixture
`p_k = (N(-ᾱ_k a, v_k I) + N(ᾱ_k a, v_k I))/2` (law equality), with `ᾱ_k = e^{-t_k}`,
`v_k = 1 - e^{-2 t_k}`. At `k = 0` the variance is `0` and both sides are the data law. -/
theorem fwdLaw_symTwoPoint (a : Fin d → ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : Monotone t)
    (k : ℕ) :
    fwdLaw (symTwoPoint a) t k =
      (2⁻¹ : ℝ≥0∞) • Measure.pi (fun i => gaussianReal (-(cumScale t k * a i))
        (cumVar t k).toNNReal) +
      (2⁻¹ : ℝ≥0∞) • Measure.pi (fun i => gaussianReal (cumScale t k * a i)
        (cumVar t k).toNNReal) := by
  rw [fwdLaw_eq_ouKernelVarPi_comp _ h0 ht, comp_symTwoPoint, ouKernelVarPi_apply,
    ouKernelVarPi_apply]
  simp [cumScale, cumVar]

/-- On `Fin (d + 1) → ℝ` the two-point law has no Lebesgue density: `¬ μ ≪ volume`. -/
theorem symTwoPoint_not_ac (a : Fin (d + 1) → ℝ) :
    ¬ symTwoPoint a ≪ (volume : Measure (Fin (d + 1) → ℝ)) := fun h => by
  have := h (measure_singleton a)
  simp [symTwoPoint] at this

/-- For `k ≥ 1` on a strictly increasing grid, the forward marginal of two-point data has a
Lebesgue density: `p_k ≪ volume` (in contrast with `symTwoPoint_not_ac` for `k = 0`). -/
theorem fwdLaw_symTwoPoint_ac (a : Fin d → ℝ) {t : ℕ → ℝ} (ht : StrictMono t) {k : ℕ}
    (hk : 1 ≤ k) : fwdLaw (symTwoPoint a) t k ≪ volume := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [fwdLaw_eq_withDensity _ (ht (Nat.lt_succ_self j))]
  exact withDensity_absolutelyContinuous _ _

/-! ### Density and score of the forward marginals -/

/-- The heat-flow density of the two-point law, with `φ_s = heatDensityPi s`:
`heatFlowDensityPi ((δ_{-b} + δ_b)/2) s y = (φ_s(y + b) + φ_s(y - b))/2`. -/
theorem heatFlowDensityPi_symTwoPoint (b : Fin d → ℝ) (s : ℝ) (y : Fin d → ℝ) :
    heatFlowDensityPi (symTwoPoint b) s y =
      2⁻¹ * heatDensityPi s (y + b) + 2⁻¹ * heatDensityPi s (y - b) := by
  rw [heatFlowDensityPi, integral_symTwoPoint, sub_neg_eq_add]

/-- The gradient of the heat-flow density of the two-point law:
`heatFlowGradPi ((δ_{-b} + δ_b)/2) s y = (∇φ_s(y + b) + ∇φ_s(y - b))/2` coordinatewise. -/
theorem heatFlowGradPi_symTwoPoint (b : Fin d → ℝ) (s : ℝ) (y : Fin d → ℝ) (i : Fin d) :
    heatFlowGradPi (symTwoPoint b) s y i =
      2⁻¹ * heatGradPi s (y + b) i + 2⁻¹ * heatGradPi s (y - b) i := by
  change ∫ x, heatGradPi s (y - x) i ∂(symTwoPoint b) = _
  rw [integral_symTwoPoint, sub_neg_eq_add]

/-- The Gaussian kernel at a shifted point, factored:
`φ_v(y + c a) = φ_v(y) e^{-c² |a|²/(2v)} e^{-c ⟨a, y⟩/v}` (no assumption on `v`). -/
theorem heatDensityPi_add_smul (v c : ℝ) (a y : Fin d → ℝ) :
    heatDensityPi v (y + c • a) = heatDensityPi v y *
      Real.exp (-(c ^ 2 * ∑ i, a i ^ 2) / (2 * v)) * Real.exp (-(c * (a ⬝ᵥ y) / v)) := by
  rw [heatDensityPi_eq_exp, heatDensityPi_eq_exp]
  simp only [mul_assoc, ← Real.exp_add]
  congr 2
  have e : ∑ i, (y + c • a) i ^ 2 =
      ∑ i, y i ^ 2 + c ^ 2 * ∑ i, a i ^ 2 + 2 * c * (a ⬝ᵥ y) := by
    rw [dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  ring

/-- The Gaussian kernel at a shifted point, factored:
`φ_v(y - c a) = φ_v(y) e^{-c² |a|²/(2v)} e^{c ⟨a, y⟩/v}` (no assumption on `v`). -/
theorem heatDensityPi_sub_smul (v c : ℝ) (a y : Fin d → ℝ) :
    heatDensityPi v (y - c • a) = heatDensityPi v y *
      Real.exp (-(c ^ 2 * ∑ i, a i ^ 2) / (2 * v)) * Real.exp (c * (a ⬝ᵥ y) / v) := by
  have h := heatDensityPi_add_smul v (-c) a y
  rw [neg_smul, ← sub_eq_add_neg] at h
  rw [h]
  ring_nf

/-- **Density of the forward marginals of two-point data.** If `t_0 = 0`, `t` is strictly
increasing and `k ≥ 1`, then for every `y` the forward density (`fwdDensity`, the continuous
Lebesgue density of `p_k`) is the Gaussian mixture density
`p_k(y) = (φ_{v_k}(y + ᾱ_k a) + φ_{v_k}(y - ᾱ_k a))/2`, with `φ_v = heatDensityPi v` the density
of `N(0, v I)`, `ᾱ_k = e^{-t_k}` and `v_k = 1 - e^{-2 t_k}`. -/
theorem fwdDensity_symTwoPoint (a : Fin d → ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) (y : Fin d → ℝ) :
    fwdDensity (symTwoPoint a) t k y =
      2⁻¹ * heatDensityPi (cumVar t k) (y + cumScale t k • a) +
      2⁻¹ * heatDensityPi (cumVar t k) (y - cumScale t k • a) := by
  rw [fwdDensity_eq_ouDensity _ h0 ht hk, ouDensity, ouLaw, map_scalePi_symTwoPoint,
    heatFlowDensityPi_symTwoPoint, ouC_eq_cumScale, ouS_eq_cumVar]

/-- **Density of the forward marginals, `cosh` form.** Under the hypotheses of
`fwdDensity_symTwoPoint`,
`p_k(y) = φ_{v_k}(y) e^{-ᾱ_k² |a|²/(2 v_k)} cosh(ᾱ_k ⟨a, y⟩ / v_k)`. -/
theorem fwdDensity_symTwoPoint_eq_cosh (a : Fin d → ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) (y : Fin d → ℝ) :
    fwdDensity (symTwoPoint a) t k y = heatDensityPi (cumVar t k) y *
      Real.exp (-(cumScale t k ^ 2 * ∑ i, a i ^ 2) / (2 * cumVar t k)) *
      Real.cosh (cumScale t k * (a ⬝ᵥ y) / cumVar t k) := by
  rw [fwdDensity_symTwoPoint a h0 ht hk, heatDensityPi_add_smul, heatDensityPi_sub_smul,
    Real.cosh_eq]
  ring

/-- **Exact score of two-point data.** If `t_0 = 0`, `t` is strictly increasing and `k ≥ 1`,
then the score of the forward density `p_k` (Fréchet gradient of `log p_k`) is, for every `y`,
`∇ log p_k(y) = (-y + ᾱ_k a tanh(ᾱ_k ⟨a, y⟩ / v_k)) / v_k`, with `ᾱ_k = e^{-t_k}` and
`v_k = 1 - e^{-2 t_k}`. -/
theorem score_fwdDensity_symTwoPoint (a : Fin d → ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) (y : Fin d → ℝ) :
    score (fwdDensity (symTwoPoint a) t k) y = fun i =>
      (-(y i) + cumScale t k * a i * Real.tanh (cumScale t k * (a ⬝ᵥ y) / cumVar t k)) /
        cumVar t k := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hv := cumVar_pos htk
  funext i
  rw [fwdDensity_eq_ouDensity _ h0 ht hk, score_ouDensity _ one_pos one_pos htk, ouGrad,
    ouDensity, ouLaw, map_scalePi_symTwoPoint, heatFlowGradPi_symTwoPoint,
    heatFlowDensityPi_symTwoPoint, ouC_eq_cumScale, ouS_eq_cumVar]
  simp only [heatGradPi]
  rw [heatDensityPi_add_smul, heatDensityPi_sub_smul, Real.tanh_eq]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hP := heatDensityPi_pos hv y
  set c := cumScale t k
  set v := cumVar t k
  set P := heatDensityPi v y
  set E := Real.exp (-(c ^ 2 * ∑ i, a i ^ 2) / (2 * v))
  set u := c * (a ⬝ᵥ y) / v
  have hE : 0 < E := Real.exp_pos _
  have hp := Real.exp_pos u
  have hq := Real.exp_pos (-u)
  have hden : 2⁻¹ * (P * E * Real.exp (-u)) + 2⁻¹ * (P * E * Real.exp u) ≠ 0 := by positivity
  rw [div_eq_div_iff hden hv.ne']
  field_simp
  ring

/-! ### Dimension one -/

/-- **Density in dimension one.** For `a : ℝ`, data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`,
`t` strictly increasing and `k ≥ 1`:
`p_k(y) = (N(-ᾱ_k a, v_k)(y_0) + N(ᾱ_k a, v_k)(y_0))/2`, with Mathlib's Gaussian density
`gaussianPDFReal`. -/
theorem fwdDensity_symTwoPoint_one (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    fwdDensity (symTwoPoint fun _ : Fin 1 => a) t k y =
      2⁻¹ * gaussianPDFReal (-(cumScale t k * a)) (cumVar t k).toNNReal (y 0) +
      2⁻¹ * gaussianPDFReal (cumScale t k * a) (cumVar t k).toNNReal (y 0) := by
  have hv := cumVar_pos (h0 ▸ ht (by omega : 0 < k) : 0 < t k)
  rw [fwdDensity_symTwoPoint _ h0 ht hk, HeatFlowDeBruijn.gaussianPDFReal_eq_heatDensity hv,
    HeatFlowDeBruijn.gaussianPDFReal_eq_heatDensity hv]
  simp [heatDensityPi]

/-- The score of the one-dimensional symmetric Gaussian mixture `(N(-m, v) + N(m, v))/2`:
`mixScore m v x = (-x + m tanh(m x / v)) / v`. -/
noncomputable def mixScore (m v x : ℝ) : ℝ := (-x + m * Real.tanh (m * x / v)) / v

/-- **Exact score of two-point data in dimension one.** For `a : ℝ`, data `(δ_{-a} + δ_a)/2` on
`Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing and `k ≥ 1`, the score of the forward density is
`∇ log p_k(y) = (-y_0 + ᾱ_k a tanh(ᾱ_k a y_0 / v_k)) / v_k` (the only coordinate). -/
theorem score_fwdDensity_symTwoPoint_one (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    score (fwdDensity (symTwoPoint fun _ : Fin 1 => a) t k) y = fun _ =>
      (-(y 0) + cumScale t k * a * Real.tanh (cumScale t k * a * y 0 / cumVar t k)) /
        cumVar t k := by
  rw [score_fwdDensity_symTwoPoint _ h0 ht hk]
  funext i
  rw [Subsingleton.elim i 0]
  simp [dotProduct, mul_assoc]

/-- The exact score (`DiffusionDiscretization.exactScore`) of two-point data in dimension one is
the mixture score: `s_k(y) = mixScore (ᾱ_k a) v_k y_0` (hypotheses of
`score_fwdDensity_symTwoPoint_one`). -/
theorem exactScore_symTwoPoint_one (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    exactScore (symTwoPoint fun _ : Fin 1 => a) t k y =
      fun _ => mixScore (cumScale t k * a) (cumVar t k) (y 0) :=
  score_fwdDensity_symTwoPoint_one a h0 ht hk y

/-! ### The scalar score-affine map -/

/-- A reverse update that is affine in the mixture score:
`mixMap A b m v x = A x + b mixScore m v x = A x + b (-x + m tanh(m x / v)) / v`. -/
noncomputable def mixMap (A b m v x : ℝ) : ℝ := A * x + b * mixScore m v x

/-- The mixture score is odd: `mixScore m v (-x) = -mixScore m v x`. -/
theorem mixScore_neg (m v x : ℝ) : mixScore m v (-x) = -mixScore m v x := by
  simp only [mixScore, mul_neg, neg_div, Real.tanh_neg]
  ring

/-- `mixScore m v 0 = 0`. -/
theorem mixScore_zero (m v : ℝ) : mixScore m v 0 = 0 := by
  simp [mixScore]

/-- The mixture score is continuous in `x`. -/
theorem continuous_mixScore (m v : ℝ) : Continuous (mixScore m v) := by
  unfold mixScore
  have := continuous_tanh
  fun_prop

/-- The score-affine map is odd: `mixMap A b m v (-x) = -mixMap A b m v x`. -/
theorem mixMap_neg (A b m v x : ℝ) : mixMap A b m v (-x) = -mixMap A b m v x := by
  rw [mixMap, mixMap, mixScore_neg]
  ring

/-- `mixMap A b m v 0 = 0`. -/
theorem mixMap_zero (A b m v : ℝ) : mixMap A b m v 0 = 0 := by
  simp [mixMap, mixScore_zero]

/-- Linear part plus bounded part:
`mixMap A b m v x = (A - b/v) x + (b m / v) tanh(m x / v)`. -/
theorem mixMap_eq (A b m v x : ℝ) :
    mixMap A b m v x = (A - b / v) * x + b * m / v * Real.tanh (m * x / v) := by
  rw [mixMap, mixScore]
  ring

/-- The score-affine map is within `|b m / v|` of its linear part:
`|mixMap A b m v x - (A - b/v) x| ≤ |b m / v|` (from `|tanh| < 1`). -/
theorem abs_mixMap_sub_linear_le (A b m v x : ℝ) :
    |mixMap A b m v x - (A - b / v) * x| ≤ |b * m / v| := by
  rw [mixMap_eq, add_sub_cancel_left, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_tanh_lt_one _).le

/-- The score-affine map is continuous. -/
theorem continuous_mixMap (A b m v : ℝ) : Continuous (mixMap A b m v) := by
  unfold mixMap
  have := continuous_mixScore m v
  fun_prop

/-- The score-affine map is measurable. -/
theorem measurable_mixMap (A b m v : ℝ) : Measurable (mixMap A b m v) :=
  (continuous_mixMap A b m v).measurable

/-- For `x ≤ y` and `v > 0`: `0 ≤ m (tanh(m y / v) - tanh(m x / v)) ≤ m² (y - x) / v` (any sign
of `m`). -/
theorem mul_tanh_sub_bounds (m : ℝ) {v x y : ℝ} (hv : 0 < v) (hxy : x ≤ y) :
    0 ≤ m * (Real.tanh (m * y / v) - Real.tanh (m * x / v)) ∧
      m * (Real.tanh (m * y / v) - Real.tanh (m * x / v)) ≤ m ^ 2 * (y - x) / v := by
  have e : m ^ 2 * (y - x) / v = m * (m * y / v - m * x / v) := by ring
  rw [e]
  rcases le_total 0 m with hm | hm
  · have h : m * x / v ≤ m * y / v :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hm) hv.le
    exact ⟨mul_nonneg hm (sub_nonneg.2 (strictMono_tanh.monotone h)),
      mul_le_mul_of_nonneg_left (tanh_sub_tanh_le h) hm⟩
  · have h : m * y / v ≤ m * x / v :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hxy hm) hv.le
    have h1 := strictMono_tanh.monotone h
    have h2 := tanh_sub_tanh_le h
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos hm (by linarith)
    · nlinarith

/-- **Increment bounds for the score-affine map.** If `b ≥ 0`, `v > 0` and `x ≤ y`, then
`(A - b/v)(y - x) ≤ mixMap A b m v y - mixMap A b m v x ≤ (A - b/v + b m²/v²)(y - x)`. -/
theorem mixMap_sub_bounds (A : ℝ) {b : ℝ} (m : ℝ) {v x y : ℝ} (hb : 0 ≤ b) (hv : 0 < v)
    (hxy : x ≤ y) :
    (A - b / v) * (y - x) ≤ mixMap A b m v y - mixMap A b m v x ∧
      mixMap A b m v y - mixMap A b m v x ≤ (A - b / v + b * m ^ 2 / v ^ 2) * (y - x) := by
  have e : mixMap A b m v y - mixMap A b m v x = (A - b / v) * (y - x) +
      b / v * (m * (Real.tanh (m * y / v) - Real.tanh (m * x / v))) := by
    simp only [mixMap, mixScore]
    field_simp
    ring
  obtain ⟨h1, h2⟩ := mul_tanh_sub_bounds m hv hxy
  have hbv : 0 ≤ b / v := div_nonneg hb hv.le
  rw [e]
  constructor
  · nlinarith
  · have h3 : b / v * (m * (Real.tanh (m * y / v) - Real.tanh (m * x / v))) ≤
        b / v * (m ^ 2 * (y - x) / v) := mul_le_mul_of_nonneg_left h2 hbv
    have e2 : b / v * (m ^ 2 * (y - x) / v) = b * m ^ 2 / v ^ 2 * (y - x) := by
      field_simp
    nlinarith

/-- **Monotonicity of the score-affine map.** If `b ≥ 0`, `v > 0` and `b / v ≤ A`, then
`x ↦ mixMap A b m v x` is monotone. -/
theorem monotone_mixMap {A b : ℝ} (m : ℝ) {v : ℝ} (hb : 0 ≤ b) (hv : 0 < v) (hA : b / v ≤ A) :
    Monotone (mixMap A b m v) := fun x y hxy => by
  have := (mixMap_sub_bounds A m hb hv hxy).1
  nlinarith [sub_nonneg.2 hxy, sub_nonneg.2 hA]

/-- **Strict monotonicity of the score-affine map.** If `b ≥ 0`, `v > 0` and `b / v < A`, then
`x ↦ mixMap A b m v x` is strictly increasing. -/
theorem strictMono_mixMap {A b : ℝ} (m : ℝ) {v : ℝ} (hb : 0 ≤ b) (hv : 0 < v) (hA : b / v < A) :
    StrictMono (mixMap A b m v) := fun x y hxy => by
  have h1 := (mixMap_sub_bounds A m hb hv hxy.le).1
  have h2 := mul_pos (sub_pos.2 hA) (sub_pos.2 hxy)
  linarith

/-- **Lipschitz bound for the score-affine map.** If `b ≥ 0` and `v > 0`, then
`x ↦ mixMap A b m v x` is Lipschitz with constant `|A - b/v| + b m²/v²` (from `tanh` being
`1`-Lipschitz). -/
theorem lipschitzWith_mixMap (A : ℝ) {b : ℝ} (m : ℝ) {v : ℝ} (hb : 0 ≤ b) (hv : 0 < v) :
    LipschitzWith (|A - b / v| + b * m ^ 2 / v ^ 2).toNNReal (mixMap A b m v) := by
  have hK : 0 ≤ b * m ^ 2 / v ^ 2 := by positivity
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
  have key : ∀ x y : ℝ, x ≤ y → |mixMap A b m v y - mixMap A b m v x| ≤
      (|A - b / v| + b * m ^ 2 / v ^ 2) * (y - x) := fun x y hxy => by
    obtain ⟨h1, h2⟩ := mixMap_sub_bounds A m hb hv hxy
    have hd := sub_nonneg.2 hxy
    have ha1 := le_abs_self (A - b / v)
    have ha2 := neg_abs_le (A - b / v)
    rw [abs_le]
    constructor <;> nlinarith
  rcases le_total x y with h | h
  · rw [abs_sub_comm (mixMap A b m v x), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 h)]
    exact key x y h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact key y x h

/-- **Sharp Lipschitz bound in the monotone regime.** If `b ≥ 0`, `v > 0` and `b / v ≤ A`, then
`x ↦ mixMap A b m v x` is Lipschitz with constant `A - b/v + b m²/v²`. -/
theorem lipschitzWith_mixMap_of_le {A b : ℝ} (m : ℝ) {v : ℝ} (hb : 0 ≤ b) (hv : 0 < v)
    (hA : b / v ≤ A) :
    LipschitzWith (A - b / v + b * m ^ 2 / v ^ 2).toNNReal (mixMap A b m v) := by
  have hK : 0 ≤ b * m ^ 2 / v ^ 2 := by positivity
  have hA' := sub_nonneg.2 hA
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
  have key : ∀ x y : ℝ, x ≤ y → |mixMap A b m v y - mixMap A b m v x| ≤
      (A - b / v + b * m ^ 2 / v ^ 2) * (y - x) := fun x y hxy => by
    obtain ⟨h1, h2⟩ := mixMap_sub_bounds A m hb hv hxy
    have hd := sub_nonneg.2 hxy
    rw [abs_le]
    constructor <;> nlinarith
  rcases le_total x y with h | h
  · rw [abs_sub_comm (mixMap A b m v x), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 h)]
    exact key x y h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact key y x h

/-- **Slope bounds for the score-affine map.** If `b ≥ 0`, `v > 0` and `x ≥ 0`, then
`(A - b/v) x ≤ mixMap A b m v x ≤ (A + b (m²/v - 1)/v) x` (from `0 ≤ tanh z ≤ z` for `z ≥ 0`). -/
theorem mixMap_bounds_of_nonneg (A : ℝ) {b : ℝ} (m : ℝ) {v x : ℝ} (hb : 0 ≤ b) (hv : 0 < v)
    (hx : 0 ≤ x) :
    (A - b / v) * x ≤ mixMap A b m v x ∧ mixMap A b m v x ≤ (A + b * (m ^ 2 / v - 1) / v) * x := by
  have h := mixMap_sub_bounds A m hb hv hx
  rw [mixMap_zero, sub_zero, sub_zero] at h
  have e : A - b / v + b * m ^ 2 / v ^ 2 = A + b * (m ^ 2 / v - 1) / v := by
    field_simp
    ring
  rw [e] at h
  exact h

/-! ### The exact-score probability-flow step of two-point data -/

/-- The probability-flow score coefficient is nonnegative on a nondecreasing step:
`b_k = α_k⁻¹ - 1 ≥ 0` when `t_{k-1} ≤ t_k`. -/
theorem pfCoeff_nonneg {t : ℕ → ℝ} {k : ℕ} (hk : t (k - 1) ≤ t k) : 0 ≤ pfCoeff t k := by
  have h1 : fwdScale t k ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [pfCoeff, sub_nonneg]
  exact one_le_inv₀ (fwdScale_pos t k) |>.2 h1

/-- **The monotonicity condition holds on every nonnegative grid.** If `t_k > 0` and
`t_{k-1} + t_k ≥ 0`, then `b_k / v_k ≤ α_k⁻¹` (equivalently `ᾱ_k² ≤ α_k`). -/
theorem pfCoeff_div_cumVar_le {t : ℕ → ℝ} {k : ℕ} (htk : 0 < t k) (h : 0 ≤ t (k - 1) + t k) :
    pfCoeff t k / cumVar t k ≤ (fwdScale t k)⁻¹ := by
  have hv := cumVar_pos htk
  have hα := fwdScale_pos t k
  have h1 : cumScale t k ^ 2 ≤ fwdScale t k := by
    rw [cumScale, fwdScale, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    linarith
  have h2 : (fwdScale t k)⁻¹ * cumScale t k ^ 2 ≤ 1 := by
    rw [inv_mul_le_iff₀ hα, mul_one]
    exact h1
  have h3 : cumVar t k = 1 - cumScale t k ^ 2 := by linarith [cumScale_sq_add_cumVar t k]
  rw [div_le_iff₀ hv, pfCoeff, h3, mul_sub, mul_one]
  linarith

/-- **Closed form of the lower slope.** If `t_k > 0`, then
`α_k⁻¹ - b_k / v_k = (1 - e^{-(t_k + t_{k-1})}) / v_k`. -/
theorem inv_fwdScale_sub_pfCoeff_div_cumVar {t : ℕ → ℝ} {k : ℕ} (htk : 0 < t k) :
    (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k =
      (1 - Real.exp (-(t k + t (k - 1)))) / cumVar t k := by
  have hv := (cumVar_pos htk).ne'
  have h3 : cumVar t k = 1 - cumScale t k ^ 2 := by linarith [cumScale_sq_add_cumVar t k]
  have e : (fwdScale t k)⁻¹ * cumScale t k ^ 2 = Real.exp (-(t k + t (k - 1))) := by
    rw [fwdScale, cumScale, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [eq_div_iff hv, sub_mul, div_mul_cancel₀ _ hv, pfCoeff, ← e, h3]
  ring

/-- **The monotonicity condition holds strictly.** If `t_k > 0` and `t_{k-1} + t_k > 0`, then
`b_k / v_k < α_k⁻¹`. -/
theorem pfCoeff_div_cumVar_lt {t : ℕ → ℝ} {k : ℕ} (htk : 0 < t k) (h : 0 < t (k - 1) + t k) :
    pfCoeff t k / cumVar t k < (fwdScale t k)⁻¹ := by
  have hpos : 0 < (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k := by
    rw [inv_fwdScale_sub_pfCoeff_div_cumVar htk]
    refine div_pos ?_ (cumVar_pos htk)
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  linarith

/-- **The lower slope is positive on the grid.** If `t_0 = 0`, `t` is strictly increasing and
`k ≥ 1`, then `0 < α_k⁻¹ - b_k / v_k` (its value is `(1 - e^{-(t_k + t_{k-1})}) / v_k`, by
`inv_fwdScale_sub_pfCoeff_div_cumVar`). -/
theorem inv_fwdScale_sub_pfCoeff_div_cumVar_pos {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) : 0 < (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hprev : 0 ≤ t (k - 1) := h0 ▸ ht.monotone (Nat.zero_le _)
  exact sub_pos.2 (pfCoeff_div_cumVar_lt htk (by linarith))

/-- The probability-flow step with the exact score for two-point data in dimension one, as a
scalar map (one exponential-integrator step `pfMean`, not the flow map of the probability-flow
ODE from `t_k` to `t_{k-1}`):
`pfTwoPoint t a k x = α_k⁻¹ x + b_k (-x + ᾱ_k a tanh(ᾱ_k a x / v_k)) / v_k`, with
`b_k = pfCoeff t k = α_k⁻¹ - 1`, `ᾱ_k = e^{-t_k}`, `v_k = 1 - e^{-2 t_k}`. -/
noncomputable def pfTwoPoint (t : ℕ → ℝ) (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  mixMap (fwdScale t k)⁻¹ (pfCoeff t k) (cumScale t k * a) (cumVar t k) x

/-- Unfolded form of the scalar map:
`pfTwoPoint t a k x = α_k⁻¹ x + b_k (-x + ᾱ_k a tanh(ᾱ_k a x / v_k)) / v_k`. -/
theorem pfTwoPoint_eq (t : ℕ → ℝ) (a : ℝ) (k : ℕ) (x : ℝ) :
    pfTwoPoint t a k x = (fwdScale t k)⁻¹ * x + pfCoeff t k *
      (-x + cumScale t k * a * Real.tanh (cumScale t k * a * x / cumVar t k)) / cumVar t k := by
  rw [pfTwoPoint, mixMap, mixScore]
  ring

/-- **The exact-score probability-flow step of two-point data.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing and `k ≥ 1`, the
exponential-integrator probability-flow step with the exact score (`pfMean t (exactScore μ t) k`)
is the scalar map `pfTwoPoint t a k` applied to the coordinate:
`m_k(y) = pfTwoPoint t a k (y_0)`. -/
theorem pfMean_exactScore_symTwoPoint (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k y =
      fun _ => pfTwoPoint t a k (y 0) := by
  funext i
  rw [Subsingleton.elim i 0]
  simp only [pfMean, detMean, pfLin, exactScore_symTwoPoint_one a h0 ht hk, pfTwoPoint, mixMap]

/-- **The exact-score probability-flow step of two-point data, explicit form.** Under the
hypotheses of `pfMean_exactScore_symTwoPoint`,
`m_k(y)_0 = α_k⁻¹ y_0 + b_k (-y_0 + ᾱ_k a tanh(ᾱ_k a y_0 / v_k)) / v_k`. -/
theorem pfMean_exactScore_symTwoPoint_apply (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k y 0 =
      (fwdScale t k)⁻¹ * y 0 + pfCoeff t k *
        (-(y 0) + cumScale t k * a * Real.tanh (cumScale t k * a * y 0 / cumVar t k)) /
          cumVar t k := by
  rw [pfMean_exactScore_symTwoPoint a h0 ht hk]
  exact pfTwoPoint_eq t a k (y 0)

/-- The exact-score probability-flow step of two-point data is odd on `Fin 1 → ℝ`:
`m_k(-y) = -m_k(y)` (hypotheses of `pfMean_exactScore_symTwoPoint`). -/
theorem pfMean_exactScore_symTwoPoint_neg (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k (-y) =
      -pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k y := by
  rw [pfMean_exactScore_symTwoPoint a h0 ht hk, pfMean_exactScore_symTwoPoint a h0 ht hk]
  funext i
  simp only [Pi.neg_apply]
  exact mixMap_neg _ _ _ _ _

/-- The scalar exact-score probability-flow step of two-point data is odd:
`pfTwoPoint t a k (-x) = -pfTwoPoint t a k x`. -/
theorem pfTwoPoint_neg (t : ℕ → ℝ) (a : ℝ) (k : ℕ) (x : ℝ) :
    pfTwoPoint t a k (-x) = -pfTwoPoint t a k x :=
  mixMap_neg _ _ _ _ x

/-- `pfTwoPoint t a k 0 = 0`. -/
theorem pfTwoPoint_zero (t : ℕ → ℝ) (a : ℝ) (k : ℕ) : pfTwoPoint t a k 0 = 0 :=
  mixMap_zero _ _ _ _

/-- The scalar exact-score probability-flow step `pfTwoPoint t a k` is continuous. -/
theorem continuous_pfTwoPoint (t : ℕ → ℝ) (a : ℝ) (k : ℕ) : Continuous (pfTwoPoint t a k) :=
  continuous_mixMap _ _ _ _

/-- The scalar exact-score probability-flow step `pfTwoPoint t a k` is measurable. -/
theorem measurable_pfTwoPoint (t : ℕ → ℝ) (a : ℝ) (k : ℕ) : Measurable (pfTwoPoint t a k) :=
  (continuous_pfTwoPoint t a k).measurable

/-- **Increment bounds for the exact-score probability-flow step.** If `t_0 = 0`, `t` is
strictly increasing, `k ≥ 1` and `x ≤ y`, then with `A = α_k⁻¹`, `b = b_k = pfCoeff t k`,
`c = ᾱ_k a` and `f = pfTwoPoint t a k`:
`0 ≤ (A - b/v_k)(y - x) ≤ f(y) - f(x) ≤ (A - b/v_k + b c²/v_k²)(y - x)`. The lower slope
`A - b/v_k` is positive (`inv_fwdScale_sub_pfCoeff_div_cumVar_pos`). -/
theorem pfTwoPoint_sub_bounds (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {k : ℕ}
    (hk : 1 ≤ k) {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k) * (y - x) ∧
      ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k) * (y - x) ≤
        pfTwoPoint t a k y - pfTwoPoint t a k x ∧
      pfTwoPoint t a k y - pfTwoPoint t a k x ≤
        ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k +
          pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2) * (y - x) := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hmono : t (k - 1) ≤ t k := ht.monotone (Nat.sub_le k 1)
  have hprev : 0 ≤ t (k - 1) := h0 ▸ ht.monotone (Nat.zero_le _)
  have hA := pfCoeff_div_cumVar_le htk (by linarith)
  have h := mixMap_sub_bounds (fwdScale t k)⁻¹ (cumScale t k * a) (pfCoeff_nonneg hmono)
    (cumVar_pos htk) hxy
  exact ⟨mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 hxy), h⟩

/-- **The exact-score probability-flow step of two-point data is monotone** (`t_0 = 0`, `t`
strictly increasing, `k ≥ 1`); the condition `b_k / v_k ≤ α_k⁻¹` of `monotone_mixMap` holds
(`pfCoeff_div_cumVar_le`). See `strictMono_pfTwoPoint` for strict monotonicity. -/
theorem monotone_pfTwoPoint (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {k : ℕ}
    (hk : 1 ≤ k) : Monotone (pfTwoPoint t a k) := fun x y hxy => by
  have h := pfTwoPoint_sub_bounds a h0 ht hk hxy
  linarith [h.1, h.2.1]

/-- **The exact-score probability-flow step of two-point data is strictly increasing**
(`t_0 = 0`, `t` strictly increasing, `k ≥ 1`), since its lower slope `α_k⁻¹ - b_k / v_k` is
positive (`inv_fwdScale_sub_pfCoeff_div_cumVar_pos`). -/
theorem strictMono_pfTwoPoint (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {k : ℕ}
    (hk : 1 ≤ k) : StrictMono (pfTwoPoint t a k) := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hmono : t (k - 1) ≤ t k := ht.monotone (Nat.sub_le k 1)
  exact strictMono_mixMap _ (pfCoeff_nonneg hmono) (cumVar_pos htk)
    (sub_pos.1 (inv_fwdScale_sub_pfCoeff_div_cumVar_pos h0 ht hk))

/-- **Lipschitz constant of the exact-score probability-flow step of two-point data.** Under
`t_0 = 0`, `t` strictly increasing and `k ≥ 1`, `x ↦ pfTwoPoint t a k x` is Lipschitz with
constant `α_k⁻¹ - b_k/v_k + b_k (ᾱ_k a)²/v_k² = α_k⁻¹ + b_k ((ᾱ_k a)²/v_k - 1)/v_k`. -/
theorem lipschitzWith_pfTwoPoint (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) :
    LipschitzWith ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k +
      pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2).toNNReal (pfTwoPoint t a k) := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hmono : t (k - 1) ≤ t k := ht.monotone (Nat.sub_le k 1)
  have hprev : 0 ≤ t (k - 1) := h0 ▸ ht.monotone (Nat.zero_le _)
  exact lipschitzWith_mixMap_of_le _ (pfCoeff_nonneg hmono) (cumVar_pos htk)
    (pfCoeff_div_cumVar_le htk (by linarith))

/-- **Slope bounds for the exact-score probability-flow step of two-point data.** Under
`t_0 = 0`, `t` strictly increasing and `k ≥ 1`, for `x ≥ 0`, with `A = α_k⁻¹` and
`b = b_k = pfCoeff t k`:
`(A - b/v_k) x ≤ pfTwoPoint t a k x ≤ (A + b ((ᾱ_k a)²/v_k - 1)/v_k) x`. -/
theorem pfTwoPoint_bounds_of_nonneg (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k) * x ≤ pfTwoPoint t a k x ∧
      pfTwoPoint t a k x ≤ ((fwdScale t k)⁻¹ +
        pfCoeff t k * ((cumScale t k * a) ^ 2 / cumVar t k - 1) / cumVar t k) * x := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hmono : t (k - 1) ≤ t k := ht.monotone (Nat.sub_le k 1)
  exact mixMap_bounds_of_nonneg _ _ (pfCoeff_nonneg hmono) (cumVar_pos htk) hx

/-- **Slope bounds for the exact-score probability-flow step, on `Fin 1 → ℝ`.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2`, `t_0 = 0`, `t` strictly increasing, `k ≥ 1` and `y_0 ≥ 0`, the step
`m_k = pfMean t (exactScore μ t) k` satisfies, with `A = α_k⁻¹` and `b = b_k`,
`(A - b/v_k) y_0 ≤ m_k(y)_0 ≤ (A + b ((ᾱ_k a)²/v_k - 1)/v_k) y_0`. -/
theorem pfMean_exactScore_symTwoPoint_bounds (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) {y : Fin 1 → ℝ} (hy : 0 ≤ y 0) :
    ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k) * y 0 ≤
        pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k y 0 ∧
      pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k y 0 ≤ ((fwdScale t k)⁻¹ +
        pfCoeff t k * ((cumScale t k * a) ^ 2 / cumVar t k - 1) / cumVar t k) * y 0 := by
  rw [pfMean_exactScore_symTwoPoint a h0 ht hk]
  exact pfTwoPoint_bounds_of_nonneg a h0 ht hk hy

/-- On `Fin 1 → ℝ` the Euclidean distance is the distance of the coordinates:
`eDist x y = |x_0 - y_0|`. -/
theorem eDist_fin_one (x y : Fin 1 → ℝ) : RGOCouplingChainPi.eDist x y = |x 0 - y 0| := by
  rw [RGOCouplingChainPi.eDist, ProximalPi.sqDist, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

/-- **Euclidean Lipschitz bound of the exact-score probability-flow step** (the form of the
Lipschitz hypothesis of `DiffusionODELipschitz.eDist_detFlow_le`). For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing and `k ≥ 1`, the step
`m_k = pfMean t (exactScore μ t) k` satisfies
`|m_k(x) - m_k(y)| ≤ (α_k⁻¹ - b_k/v_k + b_k (ᾱ_k a)²/v_k²) |x - y|`, and the constant is
nonnegative. -/
theorem eDist_pfMean_exactScore_symTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) (x y : Fin 1 → ℝ) :
    0 ≤ (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k +
        pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ∧
      RGOCouplingChainPi.eDist (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k x)
        (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t) k y) ≤
      ((fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k +
        pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2) *
        RGOCouplingChainPi.eDist x y := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hmono : t (k - 1) ≤ t k := ht.monotone (Nat.sub_le k 1)
  have hprev : 0 ≤ t (k - 1) := h0 ▸ ht.monotone (Nat.zero_le _)
  have hA := sub_nonneg.2 (pfCoeff_div_cumVar_le htk (by linarith))
  have hb := pfCoeff_nonneg hmono
  have hK : 0 ≤ (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k +
      pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2 := by positivity
  refine ⟨hK, ?_⟩
  have h := (lipschitzWith_pfTwoPoint a h0 ht hk).dist_le_mul (x 0) (y 0)
  rw [Real.coe_toNNReal _ hK, Real.dist_eq, Real.dist_eq] at h
  rw [pfMean_exactScore_symTwoPoint a h0 ht hk, pfMean_exactScore_symTwoPoint a h0 ht hk,
    eDist_fin_one, eDist_fin_one]
  exact h

/-! ### Composition of the exact-score steps: Lipschitz constant over the late phase

A reverse run from index `N ≥ K` applies the steps `K, K - 1, …, 2` last; their composition is
the flow `Φ = m_2 ∘ ⋯ ∘ m_K` (`detFlow m K 1`). -/

open FormalizeSampling.DiffusionODELipschitz (detFlow detFlow_of_lt)

/-- The Lipschitz constant of the exact-score probability-flow step of two-point data in
dimension one (`lipschitzWith_pfTwoPoint`, `eDist_pfMean_exactScore_symTwoPoint_le`):
`L_k = α_k⁻¹ - b_k/v_k + b_k (ᾱ_k a)²/v_k²`, with `b_k = pfCoeff t k`. -/
noncomputable def lipTwoPoint (t : ℕ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k +
    pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2

/-- **The lower slope is at most one.** If `t_k > 0` and `t_{k-1} ≤ t_k`, then
`α_k⁻¹ - b_k / v_k ≤ 1`: its value is `(1 - e^{-(t_k + t_{k-1})}) / v_k`
(`inv_fwdScale_sub_pfCoeff_div_cumVar`) and `e^{-(t_k + t_{k-1})} ≥ e^{-2 t_k} = 1 - v_k`. -/
theorem inv_fwdScale_sub_pfCoeff_div_cumVar_le_one {t : ℕ → ℝ} {k : ℕ} (htk : 0 < t k)
    (hmono : t (k - 1) ≤ t k) : (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k ≤ 1 := by
  rw [inv_fwdScale_sub_pfCoeff_div_cumVar htk, div_le_one (cumVar_pos htk), cumVar]
  have : Real.exp (-2 * t k) ≤ Real.exp (-(t k + t (k - 1))) := Real.exp_le_exp.2 (by linarith)
  linarith

/-- **Bounds on the step Lipschitz constant.** If `t_0 = 0`, `t` is strictly increasing and
`k ≥ 1`, then `L_k = lipTwoPoint t a k` satisfies `0 ≤ L_k ≤ 1 + b_k a² ᾱ_k² / v_k²`, since the
lower slope `α_k⁻¹ - b_k / v_k` lies in `(0, 1]` (`inv_fwdScale_sub_pfCoeff_div_cumVar_pos`,
`inv_fwdScale_sub_pfCoeff_div_cumVar_le_one`). -/
theorem lipTwoPoint_bounds (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {k : ℕ}
    (hk : 1 ≤ k) :
    0 ≤ lipTwoPoint t a k ∧
      lipTwoPoint t a k ≤ 1 + pfCoeff t k * a ^ 2 * cumScale t k ^ 2 / cumVar t k ^ 2 := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have h1 := inv_fwdScale_sub_pfCoeff_div_cumVar_le_one htk (ht.monotone (Nat.sub_le k 1))
  refine ⟨(eDist_pfMean_exactScore_symTwoPoint_le a h0 ht hk 0 0).1, ?_⟩
  have e : pfCoeff t k * (cumScale t k * a) ^ 2 / cumVar t k ^ 2 =
      pfCoeff t k * a ^ 2 * cumScale t k ^ 2 / cumVar t k ^ 2 := by ring
  rw [lipTwoPoint, e]
  linarith

/-- **Short steps.** If `t_{k-1} ≤ t_k` and `t_k - t_{k-1} ≤ log 2`, then
`b_k = e^{t_k - t_{k-1}} - 1 ≤ 2 (t_k - t_{k-1})`. -/
theorem pfCoeff_le_two_mul_sub {t : ℕ → ℝ} {k : ℕ} (hmono : t (k - 1) ≤ t k)
    (hstep : t k - t (k - 1) ≤ Real.log 2) : pfCoeff t k ≤ 2 * (t k - t (k - 1)) := by
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  have hΔ : 0 ≤ t k - t (k - 1) := sub_nonneg.2 hmono
  have h := Real.abs_exp_sub_one_le (x := t k - t (k - 1)) (by rw [abs_of_nonneg hΔ]; linarith)
  rw [abs_of_nonneg hΔ] at h
  rw [pfCoeff, fwdScale, Real.exp_neg, inv_inv]
  exact (le_abs_self _).trans h

/-- **A telescoping bound for `f(s) = e^{2s} / (e^{2s} - 1)²`.** With
`F(s) = -1 / (2 (e^{2s} - 1))` (so `F' = f`, and `f` is decreasing on `(0, ∞)`): for
`0 < s ≤ u`, `(u - s) f(u) ≤ F(u) - F(s) = (1/(e^{2s} - 1) - 1/(e^{2u} - 1)) / 2`. Elementary
proof: with `x = e^{2u} ≥ y = e^{2s} > 1`, `2 (u - s) = log(x/y) ≤ x/y - 1` and
`x (y - 1) ≤ y (x - 1)`. -/
theorem sub_mul_exp_div_sq_le {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    (u - s) * (Real.exp (2 * u) / (Real.exp (2 * u) - 1) ^ 2) ≤
      (1 / (Real.exp (2 * s) - 1) - 1 / (Real.exp (2 * u) - 1)) / 2 := by
  have hy1 : 1 < Real.exp (2 * s) := by linarith [Real.add_one_le_exp (2 * s)]
  have hyx : Real.exp (2 * s) ≤ Real.exp (2 * u) := Real.exp_le_exp.2 (by linarith)
  have hlog : 2 * (u - s) ≤ Real.exp (2 * u) / Real.exp (2 * s) - 1 := by
    rw [← Real.exp_sub]
    linarith [Real.add_one_le_exp (2 * u - 2 * s)]
  set x := Real.exp (2 * u)
  set y := Real.exp (2 * s)
  have hy0 : 0 < y := by linarith
  have hy1' : 0 < y - 1 := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hf : 0 ≤ x / (x - 1) ^ 2 := by positivity
  have e : (1 / (y - 1) - 1 / (x - 1)) / 2 - (x / y - 1) / 2 * (x / (x - 1) ^ 2) =
      (x - y) ^ 2 / (2 * y * (y - 1) * (x - 1) ^ 2) := by
    field_simp
    ring
  have hpos : 0 ≤ (x - y) ^ 2 / (2 * y * (y - 1) * (x - 1) ^ 2) := by positivity
  calc (u - s) * (x / (x - 1) ^ 2) ≤ (x / y - 1) / 2 * (x / (x - 1) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hf
    _ ≤ (1 / (y - 1) - 1 / (x - 1)) / 2 := by linarith

/-- `ᾱ_k² / v_k² = e^{2 t_k} / (e^{2 t_k} - 1)²`. -/
theorem cumScale_sq_div_cumVar_sq (t : ℕ → ℝ) (k : ℕ) :
    cumScale t k ^ 2 / cumVar t k ^ 2 = Real.exp (2 * t k) / (Real.exp (2 * t k) - 1) ^ 2 := by
  have hE := Real.exp_pos (2 * t k)
  have h1 : cumScale t k ^ 2 = (Real.exp (2 * t k))⁻¹ := by
    rw [cumScale, ← Real.exp_nat_mul, ← Real.exp_neg]
    push_cast
    ring_nf
  have h2 : cumVar t k = (Real.exp (2 * t k) - 1) / Real.exp (2 * t k) := by
    rw [cumVar, sub_div, div_self hE.ne', one_div, ← Real.exp_neg]
    ring_nf
  rw [h1, h2, div_pow, div_div_eq_mul_div]
  congr 1
  field_simp

/-- **Telescoping over the late steps.** If `t_0 = 0`, `t` is strictly increasing and every step
`t_k - t_{k-1}`, `1 < k ≤ K`, is at most `log 2`, then
`∑_{1 < k ≤ K} b_k a² ᾱ_k² / v_k² ≤ a² / (e^{2 t_1} - 1)`, for every `K`. Each term is at most
`2 (t_k - t_{k-1}) a² f(t_k) ≤ a² (1/(e^{2 t_{k-1}} - 1) - 1/(e^{2 t_k} - 1))`
(`pfCoeff_le_two_mul_sub`, `sub_mul_exp_div_sq_le`), and the sum telescopes. -/
theorem sum_pfCoeff_mul_sq_div_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {K : ℕ} (hstep : ∀ k ∈ Finset.Ioc 1 K, t k - t (k - 1) ≤ Real.log 2) :
    ∑ k ∈ Finset.Ioc 1 K, pfCoeff t k * a ^ 2 * cumScale t k ^ 2 / cumVar t k ^ 2 ≤
      a ^ 2 / (Real.exp (2 * t 1) - 1) := by
  set g : ℕ → ℝ := fun k => 1 / (Real.exp (2 * t k) - 1) with hg
  have hpos : ∀ k, 1 ≤ k → 0 ≤ g k := fun k hk => by
    have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
    have : 1 < Real.exp (2 * t k) := by linarith [Real.add_one_le_exp (2 * t k)]
    simp only [hg]
    exact div_nonneg zero_le_one (by linarith)
  have hterm : ∀ k ∈ Finset.Ioc 1 K,
      pfCoeff t k * a ^ 2 * cumScale t k ^ 2 / cumVar t k ^ 2 ≤ a ^ 2 * (g (k - 1) - g k) := by
    intro k hk
    have hk' := Finset.mem_Ioc.1 hk
    have hprev : 0 < t (k - 1) := h0 ▸ ht (by omega : 0 < k - 1)
    have hmono : t (k - 1) ≤ t k := ht.monotone (Nat.sub_le k 1)
    have hb := pfCoeff_le_two_mul_sub hmono (hstep k hk)
    have hc := sub_mul_exp_div_sq_le hprev hmono
    have hf : 0 ≤ Real.exp (2 * t k) / (Real.exp (2 * t k) - 1) ^ 2 :=
      div_nonneg (Real.exp_pos _).le (sq_nonneg _)
    rw [mul_div_assoc, cumScale_sq_div_cumVar_sq]
    calc pfCoeff t k * a ^ 2 * (Real.exp (2 * t k) / (Real.exp (2 * t k) - 1) ^ 2)
        ≤ 2 * (t k - t (k - 1)) * a ^ 2 *
            (Real.exp (2 * t k) / (Real.exp (2 * t k) - 1) ^ 2) := by gcongr
      _ = a ^ 2 * (2 * ((t k - t (k - 1)) *
            (Real.exp (2 * t k) / (Real.exp (2 * t k) - 1) ^ 2))) := by ring
      _ ≤ a ^ 2 * (2 * ((1 / (Real.exp (2 * t (k - 1)) - 1) -
            1 / (Real.exp (2 * t k) - 1)) / 2)) := by gcongr
      _ = a ^ 2 * (g (k - 1) - g k) := by simp only [hg]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have e : a ^ 2 * g 1 = a ^ 2 / (Real.exp (2 * t 1) - 1) := by simp only [hg]; ring
  have h1 := mul_nonneg (sq_nonneg a) (hpos 1 le_rfl)
  rcases Nat.lt_or_ge K 1 with hK | hK
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    linarith
  · have hsum : ∑ k ∈ Finset.Ioc 1 K, (g (k - 1) - g k) = g 1 - g K := by
      rw [← neg_sub (g K) (g 1), ← sum_Ioc_sub_pred g hK, ← Finset.sum_neg_distrib]
      simp only [neg_sub]
    rw [← Finset.mul_sum, hsum, mul_sub]
    linarith [mul_nonneg (sq_nonneg a) (hpos K hK)]

/-- **Late-phase Lipschitz product.** If `t_0 = 0`, `t` is strictly increasing and every step
`t_k - t_{k-1}`, `1 < k ≤ K`, is at most `log 2`, then the step Lipschitz constants
`L_k = lipTwoPoint t a k` satisfy `∏_{1 < k ≤ K} L_k ≤ exp(a² / (e^{2 t_1} - 1))`, for every
`K`: by `lipTwoPoint_bounds`, `L_k ≤ 1 + b_k a² ᾱ_k² / v_k² ≤ exp(b_k a² ᾱ_k² / v_k²)`, and the
exponents sum to at most `a² / (e^{2 t_1} - 1)` (`sum_pfCoeff_mul_sq_div_le`). -/
theorem prod_lipTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {K : ℕ}
    (hstep : ∀ k ∈ Finset.Ioc 1 K, t k - t (k - 1) ≤ Real.log 2) :
    ∏ k ∈ Finset.Ioc 1 K, lipTwoPoint t a k ≤ Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) := by
  calc ∏ k ∈ Finset.Ioc 1 K, lipTwoPoint t a k
      ≤ ∏ k ∈ Finset.Ioc 1 K,
          Real.exp (pfCoeff t k * a ^ 2 * cumScale t k ^ 2 / cumVar t k ^ 2) := by
        refine Finset.prod_le_prod₀ (fun k hk => ?_) fun k hk => ?_
        · exact (lipTwoPoint_bounds a h0 ht (k := k) (by have := Finset.mem_Ioc.1 hk; omega)).1
        · have := (lipTwoPoint_bounds a h0 ht (k := k)
            (by have := Finset.mem_Ioc.1 hk; omega)).2
          linarith [Real.add_one_le_exp (pfCoeff t k * a ^ 2 * cumScale t k ^ 2 /
            cumVar t k ^ 2)]
    _ = Real.exp (∑ k ∈ Finset.Ioc 1 K,
          pfCoeff t k * a ^ 2 * cumScale t k ^ 2 / cumVar t k ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) :=
        Real.exp_le_exp.2 (sum_pfCoeff_mul_sq_div_le a h0 ht hstep)

/-- **A composition of odd maps is odd.** If `m_i(-y) = -m_i(y)` for `k < i ≤ N` and all `y`,
then the deterministic flow `Φ_k = m_{k+1} ∘ ⋯ ∘ m_N` (`detFlow`) satisfies
`Φ_k(-y) = -Φ_k(y)` (for `k ≥ N`, `Φ_k` is the identity). -/
theorem detFlow_apply_neg {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {N k : ℕ}
    (hodd : ∀ i ∈ Finset.Ioc k N, ∀ y, m i (-y) = -m i y) (y : Fin d → ℝ) :
    detFlow m N k (-y) = -detFlow m N k y := by
  induction hn : N - k generalizing k with
  | zero =>
    have hid : detFlow m N k = id := by rw [DiffusionODELipschitz.detFlow, hn]; rfl
    rw [hid, id, id]
  | succ n ih =>
    have hlt : k < N := by omega
    have hsub : Finset.Ioc (k + 1) N ⊆ Finset.Ioc k N := Finset.Ioc_subset_Ioc_left (by omega)
    have hk1 : k + 1 ∈ Finset.Ioc k N := by simp only [Finset.mem_Ioc]; omega
    rw [detFlow_of_lt m hlt, Function.comp_apply, Function.comp_apply,
      ih (fun i hi => hodd i (hsub hi)) (by omega), hodd _ hk1]

/-- **Lipschitz constant of a composition of reverse maps.** If for `k < i ≤ N` the map `m_i`
is `L_i`-Lipschitz for the Euclidean distance with `L_i ≥ 0`, then the deterministic flow
`Φ_k = m_{k+1} ∘ ⋯ ∘ m_N` (`detFlow`) is `(∏_{k < i ≤ N} L_i)`-Lipschitz:
`|Φ_k(x) - Φ_k(y)| ≤ (∏_{k < i ≤ N} L_i) |x - y|` (for `k ≥ N` the product is empty and
`Φ_k` is the identity). -/
theorem eDist_detFlow_apply_le {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {L : ℕ → ℝ} {N k : ℕ}
    (hL0 : ∀ i ∈ Finset.Ioc k N, 0 ≤ L i)
    (hLip : ∀ i ∈ Finset.Ioc k N, ∀ x y,
      RGOCouplingChainPi.eDist (m i x) (m i y) ≤ L i * RGOCouplingChainPi.eDist x y)
    (x y : Fin d → ℝ) :
    RGOCouplingChainPi.eDist (detFlow m N k x) (detFlow m N k y) ≤
      (∏ i ∈ Finset.Ioc k N, L i) * RGOCouplingChainPi.eDist x y := by
  induction hn : N - k generalizing k with
  | zero =>
    have hid : detFlow m N k = id := by rw [DiffusionODELipschitz.detFlow, hn]; rfl
    rw [hid, Finset.Ioc_eq_empty (by omega), Finset.prod_empty, one_mul, id, id]
  | succ n ih =>
    have hlt : k < N := by omega
    have hsub : Finset.Ioc (k + 1) N ⊆ Finset.Ioc k N := Finset.Ioc_subset_Ioc_left (by omega)
    have hk1 : k + 1 ∈ Finset.Ioc k N := by simp only [Finset.mem_Ioc]; omega
    have ih' := ih (fun i hi => hL0 i (hsub hi)) (fun i hi => hLip i (hsub hi)) (by omega)
    have hprod : ∏ i ∈ Finset.Ioc k N, L i = L (k + 1) * ∏ i ∈ Finset.Ioc (k + 1) N, L i := by
      rw [← Finset.Icc_add_one_left_eq_Ioc, ← Finset.Ioc_insert_left (by omega : k + 1 ≤ N),
        Finset.prod_insert (by simp)]
    rw [detFlow_of_lt m hlt, Function.comp_apply, Function.comp_apply, hprod, mul_assoc]
    exact (hLip _ hk1 _ _).trans (mul_le_mul_of_nonneg_left ih' (hL0 _ hk1))

/-- **The late-phase exact-score flow of two-point data is odd.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0` and `t` strictly increasing, the deterministic flow
`Φ = m_2 ∘ ⋯ ∘ m_K` (`detFlow` from index `K` to index `1`) of the exact-score steps
`m_k = pfMean t (exactScore μ t) k` satisfies `Φ(-y) = -Φ(y)`, for every `K`. -/
theorem detFlow_pfMean_exactScore_symTwoPoint_neg (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (K : ℕ) (y : Fin 1 → ℝ) :
    detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 (-y) =
      -detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 y :=
  detFlow_apply_neg (fun i hi z => pfMean_exactScore_symTwoPoint_neg a h0 ht
    (by have := Finset.mem_Ioc.1 hi; omega) z) y

/-- **The late-phase exact-score flow of two-point data fixes the origin.** Under the hypotheses
of `detFlow_pfMean_exactScore_symTwoPoint_neg`, `Φ(0) = 0` for `Φ = m_2 ∘ ⋯ ∘ m_K`. -/
theorem detFlow_pfMean_exactScore_symTwoPoint_zero (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (K : ℕ) :
    detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 0 = 0 := by
  have h := detFlow_pfMean_exactScore_symTwoPoint_neg a h0 ht K 0
  rw [neg_zero] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply] at hi
  simp only [Pi.zero_apply]
  linarith

/-- **Lipschitz bound for the late-phase exact-score flow of two-point data.** Under the
hypotheses of `detFlow_pfMean_exactScore_symTwoPoint_neg`, the flow `Φ = m_2 ∘ ⋯ ∘ m_K` is
`(∏_{1 < k ≤ K} L_k)`-Lipschitz for the Euclidean distance, `L_k = lipTwoPoint t a k`:
`|Φ(x) - Φ(y)| ≤ (∏_{1 < k ≤ K} L_k) |x - y|`, for every `K`. -/
theorem eDist_detFlow_pfMean_exactScore_symTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (K : ℕ) (x y : Fin 1 → ℝ) :
    RGOCouplingChainPi.eDist
        (detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x)
        (detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 y) ≤
      (∏ k ∈ Finset.Ioc 1 K, lipTwoPoint t a k) * RGOCouplingChainPi.eDist x y :=
  eDist_detFlow_apply_le
    (fun i hi => (lipTwoPoint_bounds a h0 ht (k := i) (by have := Finset.mem_Ioc.1 hi; omega)).1)
    (fun i hi u v => (eDist_pfMean_exactScore_symTwoPoint_le a h0 ht (k := i)
      (by have := Finset.mem_Ioc.1 hi; omega) u v).2) x y

/-- **Grid-uniform Lipschitz bound for the late-phase exact-score flow of two-point data.** For
`a : ℝ`, data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing and every
step `t_k - t_{k-1}`, `1 < k ≤ K`, at most `log 2`, the flow `Φ = m_2 ∘ ⋯ ∘ m_K` of the
exact-score steps satisfies `|Φ(x) - Φ(y)| ≤ exp(a² / (e^{2 t_1} - 1)) |x - y|`; the constant
depends on `a` and `t_1` only, not on `K` or the other grid points (`prod_lipTwoPoint_le`). -/
theorem eDist_detFlow_pfMean_exactScore_symTwoPoint_le_exp (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {K : ℕ} (hstep : ∀ k ∈ Finset.Ioc 1 K, t k - t (k - 1) ≤ Real.log 2)
    (x y : Fin 1 → ℝ) :
    RGOCouplingChainPi.eDist
        (detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x)
        (detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 y) ≤
      Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) * RGOCouplingChainPi.eDist x y :=
  (eDist_detFlow_pfMean_exactScore_symTwoPoint_le a h0 ht K x y).trans
    (mul_le_mul_of_nonneg_right (prod_lipTwoPoint_le a h0 ht hstep)
      (RGOCouplingChainPi.eDist_nonneg x y))

/-- **The late-phase exact-score flow of two-point data expands by a bounded factor.** Under
the hypotheses of `eDist_detFlow_pfMean_exactScore_symTwoPoint_le_exp`, for every `y`,
`|Φ(y)_0| ≤ exp(a² / (e^{2 t_1} - 1)) |y_0|` (since `Φ(0) = 0`). -/
theorem abs_detFlow_pfMean_exactScore_symTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {K : ℕ} (hstep : ∀ k ∈ Finset.Ioc 1 K, t k - t (k - 1) ≤ Real.log 2)
    (y : Fin 1 → ℝ) :
    |detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 y 0| ≤
      Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) * |y 0| := by
  have h := eDist_detFlow_pfMean_exactScore_symTwoPoint_le_exp a h0 ht hstep y 0
  rw [detFlow_pfMean_exactScore_symTwoPoint_zero a h0 ht K, eDist_fin_one, eDist_fin_one] at h
  simpa using h

end FormalizeSampling.DiffusionTwoPoint
