module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import FormalizeSampling.Foundations.VectorCalculus
public import FormalizeSampling.Foundations.HeatKernel

/-!
# Tweedie's formula: the Gaussian-convolution score identity (SE-3)

Registry ID covered: **SE-3** (Gaussian convolution score identity, with the
differentiation under the integral sign and the posterior / conditional-expectation version).

## Setting and conventions

Let `μ` be a probability measure on `ℝ` (the prior law of `X`), let `Z ~ N(0,1)` be independent
of `X`, let `σ ≠ 0` and `Y = X + σ Z`. Throughout, `gaussianReal m v` is Mathlib's Gaussian law
with mean `m` and **variance** `v : ℝ≥0`, and `gaussianPDFReal m v` is its Lebesgue density.
We write the variance `σ²` as the `ℝ≥0` element `⟨σ ^ 2, sq_nonneg σ⟩` (no truncation is
involved, since `σ ^ 2 ≥ 0`).

* `gaussKernel σ x y = gaussianPDFReal x ⟨σ², _⟩ y`, the density at `y` of `N(x, σ²)`;
* `smoothedDensity μ σ y = ∫ gaussKernel σ x y dμ(x)`, the density of `Y`;
* `posteriorMean μ σ y = (∫ x · gaussKernel σ x y dμ(x)) / smoothedDensity μ σ y`;
* `posteriorNoiseMean μ σ y = (∫ ((y - x)/σ) · gaussKernel σ x y dμ(x)) / smoothedDensity μ σ y`.

`gaussKernel` and `smoothedDensity` are defined, with their elementary bounds and the law
identification, in `Foundations/HeatKernel.lean`.

The denominators are strictly positive (`smoothedDensity_pos`), and both numerators are
integrals of bounded continuous functions of `x`, so all four objects are honest real numbers
for an **arbitrary** prior probability measure: no moment assumption on `μ` is needed for the
score identity. Scores are state scores `(log p)'` (`FormalizeSampling.score1`).

## Main results

* (a) `integrable_mul_gaussKernel`, `smoothedDensity_pos` (with `integrable_gaussKernel`).
* (b) `hasDerivAt_smoothedDensity`: differentiation under the integral sign with a constant
  dominating function.
* (c) `tweedie`: `(log p_σ)'(y) = (posteriorMean μ σ y - y) / σ²`, for every probability `μ`.
* (d) `tweedie_noise`, `posteriorNoiseMean_eq`: the noise form `-(posteriorNoiseMean)/σ` and
  the identity `posteriorNoiseMean = (y - posteriorMean) / σ`.
* (e) `map_add_mul_eq_withDensity`: the law of `X + σZ` has Lebesgue density
  `smoothedDensity μ σ` (random-variable form of `conv_gaussianReal_eq_withDensity`).
* (f) `integral_integral_mul_gaussKernel_eq_posteriorMean` and its noise analogue
  (density form of `E[g(Y) X] = E[g(Y) m(Y)]`), the law-level versions
  `integral_prod_mul_fst_eq_integral_posteriorMean`, `integral_mul_eq_integral_posteriorMean`,
  and the conditional-expectation statements `condExp_eq_posteriorMean`,
  `condExp_noise_eq_posteriorNoiseMean`, `tweedie_condExp`, `tweedie_noise_condExp`.
* (g) Isotropic `d`-dimensional version on `Fin d → ℝ` (state score `FormalizeSampling.score`):
  `piGaussKernel` (product of the 1D kernels, the density of `N(x, σ² I_d)`, see
  `pi_gaussianReal_eq_withDensity`), `hasFDerivAt_piSmoothedDensity`, `tweedie_pi`,
  `tweedie_noise_pi`, `piPosteriorNoiseMean_eq`, `conv_pi_gaussianReal_eq_withDensity`
  (law identification with `N(0, σ² I_d) = ⊗ᵢ N(0, σ²)`), and the density-form
  posterior-mean characterisation
  `integral_integral_apply_mul_piGaussKernel_eq_piPosteriorMean`.

Conditional expectations are only determined up to null sets: the theorems say that
`posteriorMean μ σ ∘ Y` is *a version* of `E[X | σ(Y)]` (an `=ᵐ` statement). No regular
conditional distribution of `X` given `Y` is constructed or chosen.

## Not proved here

* In dimension `d` only the analytic score identity, the law identification and the
  density-form posterior-mean characterisation are proved. The `d`-dimensional noise-mean
  characterisation and the random-variable / conditional-expectation forms
  (`E[X | σ(Y)] = m(Y)` a.s.) are proved only in dimension one.
* The posterior-mean characterisation requires a finite first moment (`Integrable id μ`, resp.
  integrability of the coordinate in dimension `d`), which is needed for `E[X | Y]` to exist;
  the score identities themselves and all one-dimensional noise-mean statements do not need it.
* Nothing is proved about higher derivatives (e.g. the second-order Tweedie / posterior
  covariance formula), about `σ = 0`, or about anisotropic noise; affine (OU) noise is the
  corollary in `Identities/OUPosteriorScore` (also SE-3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.Tweedie

/-! ### Definitions -/

/-- The posterior mean `m(y) = (∫ x · gaussKernel σ x y dμ(x)) / p_σ(y)`, i.e. the mean of the
posterior `μ(dx | y) ∝ gaussKernel σ x y μ(dx)`. It is a version of `E[X | Y = y]`
(`condExp_eq_posteriorMean`). -/
noncomputable def posteriorMean (μ : Measure ℝ) (σ y : ℝ) : ℝ :=
  (∫ x, x * gaussKernel σ x y ∂μ) / smoothedDensity μ σ y

/-- The posterior noise mean `(∫ ((y - x)/σ) · gaussKernel σ x y dμ(x)) / p_σ(y)`. It is a
version of `E[Z | Y = y]` for `Y = X + σZ` (`condExp_noise_eq_posteriorNoiseMean`). -/
noncomputable def posteriorNoiseMean (μ : Measure ℝ) (σ y : ℝ) : ℝ :=
  (∫ x, ((y - x) / σ) * gaussKernel σ x y ∂μ) / smoothedDensity μ σ y

/-! ### Elementary properties of the Gaussian kernel -/

/-- For `σ ≠ 0` the Gaussian kernel is strictly positive. -/
lemma gaussKernel_pos {σ : ℝ} (hσ : σ ≠ 0) (x y : ℝ) : 0 < gaussKernel σ x y :=
  gaussianPDFReal_pos _ _ _ (var_ne_zero hσ)

/-- Translation invariance: `gaussKernel σ x y = gaussKernel σ 0 (y - x)`. -/
lemma gaussKernel_eq_sub (σ x y : ℝ) : gaussKernel σ x y = gaussKernel σ 0 (y - x) := by
  simp [gaussKernel_eq]

/-- Elementary inequality: for `a > 0` and all real `t`, `|t| * exp(-t² / a) ≤ a + 1`. -/
lemma abs_mul_exp_neg_sq_div_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| * rexp (-t ^ 2 / a) ≤ a + 1 := by
  have hexp : t ^ 2 / a + 1 ≤ rexp (t ^ 2 / a) := Real.add_one_le_exp _
  have hq : 0 ≤ t ^ 2 / a := by positivity
  have habs : |t| ≤ 1 + t ^ 2 := by
    nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]
  have hpoly : 1 + t ^ 2 ≤ (a + 1) * (t ^ 2 / a + 1) := by
    have : (a + 1) * (t ^ 2 / a + 1) = a + 1 + t ^ 2 + t ^ 2 / a := by
      field_simp
      ring
    rw [this]
    linarith
  have key : |t| ≤ (a + 1) * rexp (t ^ 2 / a) :=
    habs.trans (hpoly.trans (mul_le_mul_of_nonneg_left hexp (by linarith)))
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact key

/-- For `σ ≠ 0`, `∂_y gaussKernel σ x y = ((x - y) / σ²) * gaussKernel σ x y`. -/
lemma hasDerivAt_gaussKernel {σ : ℝ} (hσ : σ ≠ 0) (x y : ℝ) :
    HasDerivAt (fun y => gaussKernel σ x y) (((x - y) / σ ^ 2) * gaussKernel σ x y) y := by
  have h1 : HasDerivAt (fun y => -(y - x) ^ 2 / (2 * σ ^ 2)) ((x - y) / σ ^ 2) y := by
    have h0 : HasDerivAt (fun y => (y - x) ^ 2) (2 * (y - x)) y := by
      simpa using ((hasDerivAt_id y).sub_const x).fun_pow 2
    convert h0.neg.div_const (2 * σ ^ 2) using 1
    field_simp
    ring
  have h := h1.exp.const_mul (√(2 * π * σ ^ 2))⁻¹
  simp_rw [gaussKernel_eq]
  convert h using 1
  ring

/-- Uniform bound on the score of the kernel: for `σ ≠ 0` and all `x, y`,
`|x - y| * gaussKernel σ x y ≤ (2σ² + 1) (√(2πσ²))⁻¹`. -/
lemma abs_sub_mul_gaussKernel_le {σ : ℝ} (hσ : σ ≠ 0) (x y : ℝ) :
    |x - y| * gaussKernel σ x y ≤ (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ := by
  have ha : 0 < 2 * σ ^ 2 := by positivity
  have h := abs_mul_exp_neg_sq_div_le ha (y - x)
  rw [gaussKernel_eq, abs_sub_comm, mul_left_comm, mul_comm (2 * σ ^ 2 + 1)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- For fixed `y` and `σ ≠ 0`, `x ↦ |x| * gaussKernel σ x y` is bounded by
`(|y| + 2σ² + 1) (√(2πσ²))⁻¹`. -/
lemma abs_mul_gaussKernel_le {σ : ℝ} (hσ : σ ≠ 0) (x y : ℝ) :
    |x| * gaussKernel σ x y ≤ (|y| + 2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ := by
  have h1 := abs_sub_mul_gaussKernel_le hσ x y
  have h2 := gaussKernel_le σ x y
  have h3 : |x| ≤ |y| + |x - y| := by
    calc |x| = |y + (x - y)| := by ring_nf
      _ ≤ |y| + |x - y| := abs_add_le _ _
  have hK := gaussKernel_nonneg σ x y
  calc |x| * gaussKernel σ x y ≤ (|y| + |x - y|) * gaussKernel σ x y :=
        mul_le_mul_of_nonneg_right h3 hK
    _ = |y| * gaussKernel σ x y + |x - y| * gaussKernel σ x y := by ring
    _ ≤ |y| * (√(2 * π * σ ^ 2))⁻¹ + (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ := by
        gcongr
    _ = _ := by ring

/-- For every `x`, `y ↦ gaussKernel σ x y` is Lebesgue integrable. -/
lemma integrable_gaussKernel_right (σ x : ℝ) : Integrable (fun y => gaussKernel σ x y) :=
  integrable_gaussianPDFReal _ _

/-- For `σ ≠ 0`, `∫ gaussKernel σ x y dy = 1`. -/
lemma integral_gaussKernel_right {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    ∫ y, gaussKernel σ x y = 1 :=
  integral_gaussianPDFReal_eq_one _ (var_ne_zero hσ)

/-- For `σ ≠ 0`, `t ↦ |t| * gaussKernel σ 0 t` is Lebesgue integrable (first absolute moment
of `N(0, σ²)`). -/
lemma integrable_abs_mul_gaussKernel_zero {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable (fun t => |t| * gaussKernel σ 0 t) := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  have h := (integrable_mul_exp_neg_mul_sq hb).norm.const_mul (√(2 * π * σ ^ 2))⁻¹
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [gaussKernel_eq, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), sub_zero]
  rw [mul_left_comm]
  congr 3
  ring

/-- For `σ ≠ 0` and every `x`, `y ↦ |y - x| * gaussKernel σ x y` is Lebesgue integrable. -/
lemma integrable_abs_sub_mul_gaussKernel_right {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    Integrable (fun y => |y - x| * gaussKernel σ x y) := by
  simp_rw [gaussKernel_eq_sub σ x]
  exact (integrable_abs_mul_gaussKernel_zero hσ).comp_sub_right x

/-- `∫ |y - x| gaussKernel σ x y dy` does not depend on `x`: it equals
`∫ |t| gaussKernel σ 0 t dt`. -/
lemma integral_abs_sub_mul_gaussKernel_right (σ x : ℝ) :
    ∫ y, |y - x| * gaussKernel σ x y = ∫ t, |t| * gaussKernel σ 0 t := by
  simp_rw [gaussKernel_eq_sub σ x]
  exact integral_sub_right_eq_self (fun t => |t| * gaussKernel σ 0 t) x

/-! ### (a) Integrability and positivity under an arbitrary finite prior -/

/-- (a) For any finite measure `μ`, `σ ≠ 0` and `y`, `x ↦ x * gaussKernel σ x y` is
`μ`-integrable (it is bounded and continuous); no moment assumption on `μ` is needed. -/
theorem integrable_mul_gaussKernel (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (y : ℝ) : Integrable (fun x => x * gaussKernel σ x y) μ := by
  refine Integrable.of_bound
    (continuous_id.mul (continuous_gaussKernel_left σ y)).aestronglyMeasurable
    ((|y| + 2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_nonneg _ _ _)]
  exact abs_mul_gaussKernel_le hσ x y

/-- For any finite measure `μ`, `σ ≠ 0`, `y` and `c`, `x ↦ ((x - y) / c) * gaussKernel σ x y`
is `μ`-integrable (it is bounded and continuous). -/
theorem integrable_sub_div_mul_gaussKernel (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y c : ℝ) : Integrable (fun x => ((x - y) / c) * gaussKernel σ x y) μ := by
  refine Integrable.of_bound
    (((continuous_id.sub continuous_const).div_const c).mul
      (continuous_gaussKernel_left σ y)).aestronglyMeasurable
    ((2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ / |c|) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_nonneg _ _ _), abs_div,
    div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (abs_sub_mul_gaussKernel_le hσ x y) (abs_nonneg c)

/-- The smoothed density is nonnegative for every finite measure `μ`. -/
theorem smoothedDensity_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (σ y : ℝ) :
    0 ≤ smoothedDensity μ σ y :=
  integral_nonneg fun x => gaussKernel_nonneg σ x y

/-- (a) For a probability measure `μ` and `σ ≠ 0`, the smoothed density is strictly positive
everywhere: `0 < p_σ(y)`. -/
theorem smoothedDensity_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (y : ℝ) : 0 < smoothedDensity μ σ y := by
  unfold smoothedDensity
  rw [integral_pos_iff_support_of_nonneg (fun x => gaussKernel_nonneg σ x y)
    (integrable_gaussKernel μ σ y)]
  have : Function.support (fun x => gaussKernel σ x y) = Set.univ :=
    Set.eq_univ_of_forall fun x => (gaussKernel_pos hσ x y).ne'
  rw [this, measure_univ]
  exact one_pos

/-! ### (b) Differentiation under the integral sign -/

/-- (b) For any finite measure `μ` and `σ ≠ 0`, the smoothed density is differentiable with
`p_σ'(y) = ∫ ((x - y) / σ²) gaussKernel σ x y dμ(x)`. Proof: dominated differentiation
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with the *constant* dominating function
`(2σ² + 1)(√(2πσ²))⁻¹ / σ²`, integrable because `μ` is finite. -/
theorem hasDerivAt_smoothedDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (y : ℝ) :
    HasDerivAt (smoothedDensity μ σ) (∫ x, ((x - y) / σ ^ 2) * gaussKernel σ x y ∂μ) y := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun y x => gaussKernel σ x y) (F' := fun y x => ((x - y) / σ ^ 2) * gaussKernel σ x y)
    (x₀ := y) (bound := fun _ => (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ / σ ^ 2)
    Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_gaussKernel_left σ y').aestronglyMeasurable)
    (integrable_gaussKernel μ σ y)
    (integrable_sub_div_mul_gaussKernel μ hσ y (σ ^ 2)).aestronglyMeasurable
    (ae_of_all _ fun x y' _ => ?_) (integrable_const _)
    (ae_of_all _ fun x y' _ => hasDerivAt_gaussKernel hσ x y')
  · exact key.2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_nonneg _ _ _), abs_div,
      div_mul_eq_mul_div, abs_of_nonneg (sq_nonneg σ)]
    exact div_le_div_of_nonneg_right (abs_sub_mul_gaussKernel_le hσ x y') (sq_nonneg σ)

/-- For a finite measure `μ` and `σ ≠ 0`, `deriv p_σ y = ∫ ((x - y) / σ²) gaussKernel σ x y dμ`. -/
theorem deriv_smoothedDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (y : ℝ) :
    deriv (smoothedDensity μ σ) y = ∫ x, ((x - y) / σ ^ 2) * gaussKernel σ x y ∂μ :=
  (hasDerivAt_smoothedDensity μ hσ y).deriv

/-- For a finite measure `μ` and `σ ≠ 0`, the smoothed density is differentiable on `ℝ`. -/
theorem differentiable_smoothedDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) : Differentiable ℝ (smoothedDensity μ σ) :=
  fun y => (hasDerivAt_smoothedDensity μ hσ y).differentiableAt

/-- For a finite measure `μ` and `σ ≠ 0`, the smoothed density is continuous. -/
theorem continuous_smoothedDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) :
    Continuous (smoothedDensity μ σ) :=
  (differentiable_smoothedDensity μ hσ).continuous

/-! ### (c), (d) Tweedie's formula -/

/-- Algebraic rewriting of the derivative integral: for a finite measure `μ` and `σ ≠ 0`,
`∫ ((x - y)/c) K dμ = (∫ x K dμ - y p_σ(y)) / c`. -/
theorem integral_sub_div_mul_gaussKernel (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y c : ℝ) :
    ∫ x, ((x - y) / c) * gaussKernel σ x y ∂μ =
      ((∫ x, x * gaussKernel σ x y ∂μ) - y * smoothedDensity μ σ y) / c := by
  unfold smoothedDensity
  rw [← integral_const_mul, ← integral_sub (integrable_mul_gaussKernel μ hσ y)
    ((integrable_gaussKernel μ σ y).const_mul y), ← integral_div]
  congr 1
  ext x
  ring

/-- For a probability measure `μ` and `σ ≠ 0`: `m(y) p_σ(y) = ∫ x gaussKernel σ x y dμ(x)`
(the division in `posteriorMean` is by a strictly positive number). -/
theorem posteriorMean_mul_smoothedDensity (μ : Measure ℝ) [IsProbabilityMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y : ℝ) :
    posteriorMean μ σ y * smoothedDensity μ σ y = ∫ x, x * gaussKernel σ x y ∂μ := by
  unfold posteriorMean
  exact div_mul_cancel₀ _ (smoothedDensity_pos μ hσ y).ne'

/-- For a probability measure `μ` and `σ ≠ 0`:
`posteriorNoiseMean μ σ y * p_σ(y) = ∫ ((y - x)/σ) gaussKernel σ x y dμ(x)`. -/
theorem posteriorNoiseMean_mul_smoothedDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    posteriorNoiseMean μ σ y * smoothedDensity μ σ y =
      ∫ x, ((y - x) / σ) * gaussKernel σ x y ∂μ := by
  unfold posteriorNoiseMean
  exact div_mul_cancel₀ _ (smoothedDensity_pos μ hσ y).ne'

/-- (d) Mean / noise equivalence: for any probability measure `μ`, `σ ≠ 0` and `y`,
`posteriorNoiseMean μ σ y = (y - posteriorMean μ σ y) / σ` ("`E[Z | Y] = (Y - E[X | Y])/σ`"). -/
theorem posteriorNoiseMean_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (y : ℝ) : posteriorNoiseMean μ σ y = (y - posteriorMean μ σ y) / σ := by
  have hp := (smoothedDensity_pos μ hσ y).ne'
  have h : ∫ x, ((y - x) / σ) * gaussKernel σ x y ∂μ =
      -∫ x, ((x - y) / σ) * gaussKernel σ x y ∂μ := by
    rw [← integral_neg]
    congr 1
    ext x
    ring
  unfold posteriorNoiseMean posteriorMean
  rw [h, integral_sub_div_mul_gaussKernel μ hσ y σ]
  field_simp
  ring

/-- (c) **Tweedie's formula.** For an *arbitrary* probability measure `μ` on `ℝ` (no moment
assumption) and `σ ≠ 0`, the score of the Gaussian-smoothed density `p_σ = μ ∗ N(0, σ²)` is
`(log p_σ)'(y) = (posteriorMean μ σ y - y) / σ²` at every `y ∈ ℝ`. -/
theorem tweedie (μ : Measure ℝ) [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    score1 (smoothedDensity μ σ) y = (posteriorMean μ σ y - y) / σ ^ 2 := by
  have hd := hasDerivAt_smoothedDensity μ hσ y
  have hp := (smoothedDensity_pos μ hσ y)
  rw [score1_of_pos hd.differentiableAt hp, hd.deriv,
    integral_sub_div_mul_gaussKernel μ hσ y (σ ^ 2)]
  unfold posteriorMean
  field_simp

/-- (d) **Tweedie's formula, noise form.** For an arbitrary probability measure `μ` and
`σ ≠ 0`, `(log p_σ)'(y) = -(posteriorNoiseMean μ σ y) / σ` ("`∇ log p_σ = -E[Z | Y]/σ`"). -/
theorem tweedie_noise (μ : Measure ℝ) [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    score1 (smoothedDensity μ σ) y = -posteriorNoiseMean μ σ y / σ := by
  rw [tweedie μ hσ y, posteriorNoiseMean_eq μ hσ y]
  field_simp
  ring

/-! ### (e) Law identification: `smoothedDensity` is the density of `X + σZ` -/

/-- Integrals against `μ ∗ N(0, σ²)` are Lebesgue integrals against `smoothedDensity μ σ`:
`∫ f d(μ ∗ N(0, σ²)) = ∫ f(y) p_σ(y) dy`, for any finite `μ`, `σ ≠ 0` and any `f : ℝ → ℝ`
(both sides use the Bochner convention, and the identity holds regardless of integrability). -/
theorem integral_conv_gaussianReal (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂(μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) = ∫ y, f y * smoothedDensity μ σ y := by
  rw [conv_gaussianReal_eq_withDensity μ hσ, integral_withDensity_eq_integral_toReal_smul
    (continuous_smoothedDensity μ hσ).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (smoothedDensity_nonneg μ σ y), mul_comm]

/-- Integrating `f(x + w)` against `N(0, σ²)` in `w` equals integrating `f` against the kernel
`gaussKernel σ x ·`, for `σ ≠ 0` and measurable `f` (Bochner convention on both sides). -/
theorem integral_gaussianReal_const_add {σ : ℝ} (hσ : σ ≠ 0) {f : ℝ → ℝ} (hf : Measurable f)
    (x : ℝ) :
    ∫ w, f (x + w) ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) = ∫ y, f y * gaussKernel σ x y := by
  have hmap : (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩).map (x + ·) =
      gaussianReal x ⟨σ ^ 2, sq_nonneg σ⟩ := by
    rw [var_eq_mk, gaussianReal_map_const_add, zero_add]
  rw [← integral_map (measurable_const_add x).aemeasurable hf.aestronglyMeasurable, hmap,
    integral_gaussianReal_eq_integral_smul (var_ne_zero hσ)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, gaussKernel]
  ring

/-! ### (f) Posterior-mean characterisation (density form of the conditional expectation) -/

/-- For a finite measure `μ` and `σ ≠ 0`, `posteriorMean μ σ` is Borel measurable. -/
theorem measurable_posteriorMean (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) :
    Measurable (posteriorMean μ σ) := by
  have h : StronglyMeasurable (Function.uncurry fun x y => x * gaussKernel σ x y) :=
    (continuous_fst.mul (continuous_gaussKernel_uncurry σ)).stronglyMeasurable
  exact h.integral_prod_left.measurable.div (continuous_smoothedDensity μ hσ).measurable

/-- For a finite measure `μ` and `σ ≠ 0`, `posteriorNoiseMean μ σ` is Borel measurable. -/
theorem measurable_posteriorNoiseMean (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) : Measurable (posteriorNoiseMean μ σ) := by
  have h : StronglyMeasurable
      (Function.uncurry fun x y => ((y - x) / σ) * gaussKernel σ x y) :=
    (((continuous_snd.sub continuous_fst).div_const σ).mul
      (continuous_gaussKernel_uncurry σ)).stronglyMeasurable
  exact h.integral_prod_left.measurable.div (continuous_smoothedDensity μ hσ).measurable

/-- If `μ` is finite with `Integrable id μ` and `σ ≠ 0`, then `(x, y) ↦ x * gaussKernel σ x y`
is integrable for `μ ⊗ Lebesgue` (Fubini–Tonelli: its absolute integral is `∫ |x| dμ`). -/
theorem integrable_prod_mul_gaussKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : Integrable id μ) {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable (Function.uncurry fun x y => x * gaussKernel σ x y) (μ.prod volume) := by
  have hmeas : Measurable (Function.uncurry fun x y => x * gaussKernel σ x y) :=
    measurable_fst.mul (continuous_gaussKernel_uncurry σ).measurable
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x => (integrable_gaussKernel_right σ x).const_mul x, ?_⟩
  refine hμ.norm.congr (ae_of_all _ fun x => ?_)
  simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (gaussKernel_nonneg σ x _), id]
  rw [integral_const_mul, integral_gaussKernel_right hσ, mul_one]

/-- For any finite `μ` and `σ ≠ 0`, `(x, y) ↦ ((y - x)/σ) * gaussKernel σ x y` is integrable
for `μ ⊗ Lebesgue`; no moment assumption on `μ` is needed. -/
theorem integrable_prod_noise_mul_gaussKernel (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) :
    Integrable (Function.uncurry fun x y => ((y - x) / σ) * gaussKernel σ x y)
      (μ.prod volume) := by
  have hmeas : Measurable (Function.uncurry fun x y => ((y - x) / σ) * gaussKernel σ x y) :=
    ((measurable_snd.sub measurable_fst).div_const σ).mul
      (continuous_gaussKernel_uncurry σ).measurable
  have hnorm : ∀ x y, ‖((y - x) / σ) * gaussKernel σ x y‖ =
      |y - x| * gaussKernel σ x y / |σ| := fun x y => by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (gaussKernel_nonneg σ x y)]
    ring
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x => ?_, ?_⟩
  · exact ((integrable_abs_sub_mul_gaussKernel_right hσ x).div_const |σ|).mono'
      (hmeas.comp measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ fun y => (hnorm x y).le)
  · refine (integrable_const ((∫ t, |t| * gaussKernel σ 0 t) / |σ|)).congr
      (ae_of_all _ fun x => ?_)
    simp only [Function.uncurry_apply_pair, hnorm]
    rw [integral_div, integral_abs_sub_mul_gaussKernel_right]

/-- (f) **Posterior-mean characterisation, density form.** Let `μ` be a probability measure
with finite first moment (`Integrable id μ`), `σ ≠ 0`, and `g : ℝ → ℝ` measurable with
`|g| ≤ M`. Then
`∫ (∫ g(y) x gaussKernel σ x y dy) dμ(x) = ∫ g(y) m(y) p_σ(y) dy`, `m = posteriorMean μ σ`,
i.e. `E[g(Y) X] = E[g(Y) m(Y)]` for `Y = X + σZ`. Hence `m(Y)` is a version of `E[X | Y]`;
it is determined only up to `Law(Y)`-null sets and no regular conditional version is chosen
(see `condExp_eq_posteriorMean` for the conditional-expectation statement). -/
theorem integral_integral_mul_gaussKernel_eq_posteriorMean (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable id μ) {σ : ℝ} (hσ : σ ≠ 0) {g : ℝ → ℝ}
    (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ x, (∫ y, g y * x * gaussKernel σ x y) ∂μ =
      ∫ y, g y * posteriorMean μ σ y * smoothedDensity μ σ y := by
  have hint : Integrable (Function.uncurry fun x y => g y * x * gaussKernel σ x y)
      (μ.prod volume) := by
    refine ((integrable_prod_mul_gaussKernel μ hμ hσ).bdd_mul (c := M)
      (hg.comp measurable_snd).aestronglyMeasurable (ae_of_all _ fun p => ?_)).congr
      (ae_of_all _ fun ⟨x, y⟩ => ?_)
    · rw [Real.norm_eq_abs]
      exact hM _
    · simp only [Function.comp_apply, Function.uncurry_apply_pair]
      ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [mul_assoc, posteriorMean_mul_smoothedDensity μ hσ y, ← integral_const_mul]
  congr 1
  ext x
  ring

/-- (f) **Posterior noise-mean characterisation, density form.** For any probability measure
`μ` (no moment assumption), `σ ≠ 0` and measurable `g` with `|g| ≤ M`,
`∫ (∫ g(y) ((y - x)/σ) gaussKernel σ x y dy) dμ(x) = ∫ g(y) n(y) p_σ(y) dy` with
`n = posteriorNoiseMean μ σ`, i.e. `E[g(Y) Z] = E[g(Y) n(Y)]`: `n(Y)` is a version of
`E[Z | Y]`, determined only up to null sets. -/
theorem integral_integral_noise_mul_gaussKernel_eq_posteriorNoiseMean (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) {g : ℝ → ℝ} (hg : Measurable g) (M : ℝ)
    (hM : ∀ y, |g y| ≤ M) :
    ∫ x, (∫ y, g y * ((y - x) / σ) * gaussKernel σ x y) ∂μ =
      ∫ y, g y * posteriorNoiseMean μ σ y * smoothedDensity μ σ y := by
  have hint : Integrable (Function.uncurry fun x y => g y * ((y - x) / σ) * gaussKernel σ x y)
      (μ.prod volume) := by
    refine ((integrable_prod_noise_mul_gaussKernel μ hσ).bdd_mul (c := M)
      (hg.comp measurable_snd).aestronglyMeasurable (ae_of_all _ fun p => ?_)).congr
      (ae_of_all _ fun ⟨x, y⟩ => ?_)
    · rw [Real.norm_eq_abs]
      exact hM _
    · simp only [Function.comp_apply, Function.uncurry_apply_pair]
      ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [mul_assoc, posteriorNoiseMean_mul_smoothedDensity μ hσ y, ← integral_const_mul]
  congr 1
  ext x
  ring

/-- If `μ` is a probability measure with `Integrable id μ` and `σ ≠ 0`, the posterior mean is
integrable with respect to `Law(Y) = μ ∗ N(0, σ²)`. -/
theorem integrable_posteriorMean_conv (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable (posteriorMean μ σ) (μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
  rw [conv_gaussianReal_eq_withDensity μ hσ, integrable_withDensity_iff_integrable_smul'
    (continuous_smoothedDensity μ hσ).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_prod_mul_gaussKernel μ hμ hσ).integral_prod_right.congr
    (ae_of_all _ fun y => ?_)
  simp only [Function.uncurry_apply_pair, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (smoothedDensity_nonneg μ σ y), mul_comm,
    posteriorMean_mul_smoothedDensity μ hσ y]

/-- For any probability measure `μ` and `σ ≠ 0`, the posterior noise mean is integrable with
respect to `Law(Y) = μ ∗ N(0, σ²)` (no moment assumption on `μ`). -/
theorem integrable_posteriorNoiseMean_conv (μ : Measure ℝ) [IsProbabilityMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) :
    Integrable (posteriorNoiseMean μ σ) (μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
  rw [conv_gaussianReal_eq_withDensity μ hσ, integrable_withDensity_iff_integrable_smul'
    (continuous_smoothedDensity μ hσ).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_prod_noise_mul_gaussKernel μ hσ).integral_prod_right.congr
    (ae_of_all _ fun y => ?_)
  simp only [Function.uncurry_apply_pair, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (smoothedDensity_nonneg μ σ y), mul_comm,
    posteriorNoiseMean_mul_smoothedDensity μ hσ y]

/-- (f), law level. For a probability measure `μ` with `Integrable id μ`, `σ ≠ 0` and
measurable `g` with `|g| ≤ M`: with `(X, W) ~ μ ⊗ N(0, σ²)` and `Y = X + W`,
`E[g(Y) X] = ∫ g(y) posteriorMean μ σ y d Law(Y)(y)`, where `Law(Y) = μ ∗ N(0, σ²)`. -/
theorem integral_prod_mul_fst_eq_integral_posteriorMean (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable id μ) {σ : ℝ} (hσ : σ ≠ 0) {g : ℝ → ℝ}
    (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ p, g (p.1 + p.2) * p.1 ∂(μ.prod (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) =
      ∫ y, g y * posteriorMean μ σ y ∂(μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
  have hint : Integrable (fun p : ℝ × ℝ => g (p.1 + p.2) * p.1)
      (μ.prod (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) := by
    refine ((hμ.norm.const_mul M).comp_fst _).mono'
      ((hg.comp measurable_add).mul measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, id, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  rw [integral_prod _ hint, integral_conv_gaussianReal μ hσ,
    ← integral_integral_mul_gaussKernel_eq_posteriorMean μ hμ hσ hg M hM]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  exact integral_gaussianReal_const_add hσ (f := fun y => g y * x) (hg.mul_const x) x

/-- (f), law level, noise form. For any probability measure `μ`, `σ ≠ 0` and measurable `g`
with `|g| ≤ M`: with `(X, W) ~ μ ⊗ N(0, σ²)`, `Y = X + W` and `Z = W/σ`,
`E[g(Y) Z] = ∫ g(y) posteriorNoiseMean μ σ y d Law(Y)(y)`. -/
theorem integral_prod_mul_snd_eq_integral_posteriorNoiseMean (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) {g : ℝ → ℝ}
    (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ p, g (p.1 + p.2) * (p.2 / σ) ∂(μ.prod (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) =
      ∫ y, g y * posteriorNoiseMean μ σ y ∂(μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
  have hint : Integrable (fun p : ℝ × ℝ => g (p.1 + p.2) * (p.2 / σ))
      (μ.prod (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) := by
    refine (((IsGaussian.integrable_id (μ := gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)).norm.const_mul
      (M / |σ|)).comp_snd μ).mono'
      ((hg.comp measurable_add).mul (measurable_snd.div_const σ)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, id, Real.norm_eq_abs, abs_div]
    calc |g (p.1 + p.2)| * (|p.2| / |σ|) ≤ M * (|p.2| / |σ|) :=
          mul_le_mul_of_nonneg_right (hM _) (by positivity)
      _ = M / |σ| * |p.2| := by ring
  rw [integral_prod _ hint, integral_conv_gaussianReal μ hσ,
    ← integral_integral_noise_mul_gaussKernel_eq_posteriorNoiseMean μ hσ hg M hM]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have h := integral_gaussianReal_const_add hσ (f := fun y => g y * ((y - x) / σ))
    (hg.mul ((measurable_id.sub_const x).div_const σ)) x
  simp only [add_sub_cancel_left] at h
  simp only
  rw [h]

/-! ### Random-variable form: `X ~ μ`, `Z ~ N(0,1)` independent, `Y = X + σZ` -/

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Z : Ω → ℝ}

/-- If `Z ~ N(0,1)` under `P`, then `σZ ~ N(0, σ²)` (variance `σ ^ 2` as an `ℝ≥0`). -/
theorem map_mul_eq_gaussianReal (hZ : Measurable Z) (hZlaw : P.map Z = gaussianReal 0 1)
    (σ : ℝ) : P.map (fun ω => σ * Z ω) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
  rw [show (fun ω => σ * Z ω) = (σ * ·) ∘ Z from rfl,
    ← Measure.map_map (measurable_const_mul σ) hZ, hZlaw, gaussianReal_map_const_mul]
  congr 1
  · ring
  · ext; simp [var_eq_mk]

/-- For measurable, `P`-independent `X ~ μ` and `Z ~ N(0,1)` on a probability space, the pair
`(X, σZ)` has law `μ ⊗ N(0, σ²)`. -/
theorem map_prod_eq_prod [IsProbabilityMeasure P] (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) {μ : Measure ℝ} (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) (σ : ℝ) :
    P.map (fun ω => (X ω, σ * Z ω)) = μ.prod (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
  have hind : IndepFun X (fun ω => σ * Z ω) P :=
    hXZ.comp (φ := id) (ψ := (σ * ·)) measurable_id (measurable_const_mul σ)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
    (hZ.const_mul σ).aemeasurable).mp hind, hXlaw, map_mul_eq_gaussianReal hZ hZlaw σ]

/-- For measurable, `P`-independent `X ~ μ` and `Z ~ N(0,1)` on a probability space,
`Law(X + σZ) = μ ∗ N(0, σ²)`. -/
theorem map_add_mul_eq_conv [IsProbabilityMeasure P] (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) {μ : Measure ℝ} (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) (σ : ℝ) :
    P.map (fun ω => X ω + σ * Z ω) = μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
  rw [Measure.conv, ← map_prod_eq_prod hX hZ hXZ hXlaw hZlaw σ,
    Measure.map_map measurable_add (hX.prodMk (hZ.const_mul σ))]
  rfl

/-- (e), random-variable form. For measurable, `P`-independent `X ~ μ` and `Z ~ N(0,1)` on a
probability space and `σ ≠ 0`, `Law(X + σZ)` has Lebesgue density `smoothedDensity μ σ`. -/
theorem map_add_mul_eq_withDensity [IsProbabilityMeasure P] (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ} (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) {σ : ℝ} (hσ : σ ≠ 0) :
    P.map (fun ω => X ω + σ * Z ω) =
      volume.withDensity (fun y => ENNReal.ofReal (smoothedDensity μ σ y)) := by
  have : IsFiniteMeasure μ := hXlaw ▸ inferInstance
  rw [map_add_mul_eq_conv hX hZ hXZ hXlaw hZlaw σ, conv_gaussianReal_eq_withDensity μ hσ]

/-- (f), random-variable form. For measurable, `P`-independent `X ~ μ` (with
`Integrable id μ`) and `Z ~ N(0,1)`, `σ ≠ 0`, `Y = X + σZ`, and measurable `g` with `|g| ≤ M`:
`E[g(Y) X] = E[g(Y) posteriorMean μ σ (Y)]`. -/
theorem integral_mul_eq_integral_posteriorMean [IsProbabilityMeasure P] (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hXlaw : P.map X = μ) (hZlaw : P.map Z = gaussianReal 0 1) (hμ : Integrable id μ)
    {σ : ℝ} (hσ : σ ≠ 0) {g : ℝ → ℝ} (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ ω, g (X ω + σ * Z ω) * X ω ∂P =
      ∫ ω, g (X ω + σ * Z ω) * posteriorMean μ σ (X ω + σ * Z ω) ∂P := by
  have hXW : Measurable fun ω => (X ω, σ * Z ω) := hX.prodMk (hZ.const_mul σ)
  have hY : Measurable fun ω => X ω + σ * Z ω := hX.add (hZ.const_mul σ)
  have h1 := integral_map (μ := P) hXW.aemeasurable
    (f := fun q : ℝ × ℝ => g (q.1 + q.2) * q.1)
    ((hg.comp measurable_add).mul measurable_fst).aestronglyMeasurable
  have h2 := integral_map (μ := P) hY.aemeasurable
    (f := fun y => g y * posteriorMean μ σ y)
    (hg.mul (measurable_posteriorMean μ hσ)).aestronglyMeasurable
  simp only at h1 h2
  rw [← h1, ← h2, map_prod_eq_prod hX hZ hXZ hXlaw hZlaw σ,
    map_add_mul_eq_conv hX hZ hXZ hXlaw hZlaw σ,
    integral_prod_mul_fst_eq_integral_posteriorMean μ hμ hσ hg M hM]

/-- (f), random-variable noise form. For measurable, `P`-independent `X ~ μ` and `Z ~ N(0,1)`
(no moment assumption on `μ`), `σ ≠ 0`, `Y = X + σZ`, and measurable `g` with `|g| ≤ M`:
`E[g(Y) Z] = E[g(Y) posteriorNoiseMean μ σ (Y)]`. -/
theorem integral_mul_noise_eq_integral_posteriorNoiseMean [IsProbabilityMeasure P]
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hXlaw : P.map X = μ) (hZlaw : P.map Z = gaussianReal 0 1)
    {σ : ℝ} (hσ : σ ≠ 0) {g : ℝ → ℝ} (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ ω, g (X ω + σ * Z ω) * Z ω ∂P =
      ∫ ω, g (X ω + σ * Z ω) * posteriorNoiseMean μ σ (X ω + σ * Z ω) ∂P := by
  have hXW : Measurable fun ω => (X ω, σ * Z ω) := hX.prodMk (hZ.const_mul σ)
  have hY : Measurable fun ω => X ω + σ * Z ω := hX.add (hZ.const_mul σ)
  have h1 := integral_map (μ := P) hXW.aemeasurable
    (f := fun q : ℝ × ℝ => g (q.1 + q.2) * (q.2 / σ))
    ((hg.comp measurable_add).mul (measurable_snd.div_const σ)).aestronglyMeasurable
  have h2 := integral_map (μ := P) hY.aemeasurable
    (f := fun y => g y * posteriorNoiseMean μ σ y)
    (hg.mul (measurable_posteriorNoiseMean μ hσ)).aestronglyMeasurable
  simp only [mul_div_cancel_left₀ _ hσ] at h1 h2
  rw [← h1, ← h2, map_prod_eq_prod hX hZ hXZ hXlaw hZlaw σ,
    map_add_mul_eq_conv hX hZ hXZ hXlaw hZlaw σ,
    integral_prod_mul_snd_eq_integral_posteriorNoiseMean μ hσ hg M hM]

/-- From `E[g(Y) V] = E[g(Y) m(Y)]` for all measurable `g` with `|g| ≤ 1` to equality of the
set integrals of `V` and `m ∘ Y` over every `σ(Y)`-measurable set. -/
lemma setIntegral_comap_eq {Y V : Ω → ℝ} (hY : Measurable Y) {m : ℝ → ℝ}
    (h : ∀ g : ℝ → ℝ, Measurable g → (∀ y, |g y| ≤ 1) →
      ∫ ω, g (Y ω) * V ω ∂P = ∫ ω, g (Y ω) * m (Y ω) ∂P) :
    ∀ s, MeasurableSet[MeasurableSpace.comap Y inferInstance] s →
      ∫ ω in s, m (Y ω) ∂P = ∫ ω in s, V ω ∂P := by
  intro s hs
  obtain ⟨B, hB, rfl⟩ := hs
  have hg : Measurable (B.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hB
  have hgb : ∀ y, |B.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := fun y => by
    by_cases hy : y ∈ B <;> simp [hy]
  have hind : ∀ f : Ω → ℝ, (Y ⁻¹' B).indicator f =
      fun ω => B.indicator (fun _ => (1 : ℝ)) (Y ω) * f ω := fun f => by
    ext ω
    by_cases hω : Y ω ∈ B <;> simp [Set.indicator, hω]
  rw [← integral_indicator (hY hB), ← integral_indicator (hY hB), hind, hind,
    h _ hg hgb]

/-- (f) **Posterior mean = conditional expectation.** For measurable, `P`-independent `X ~ μ`
with `Integrable id μ` and `Z ~ N(0,1)` on a probability space, and `σ ≠ 0`, with
`Y = X + σZ`: `E[X | σ(Y)] = posteriorMean μ σ ∘ Y` `P`-almost surely. Conditional
expectations are defined only up to null sets; this states that `posteriorMean μ σ ∘ Y` is a
version of `E[X | Y]`. No regular conditional distribution is chosen. -/
theorem condExp_eq_posteriorMean [IsProbabilityMeasure P] (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hXlaw : P.map X = μ) (hZlaw : P.map Z = gaussianReal 0 1) (hμ : Integrable id μ)
    {σ : ℝ} (hσ : σ ≠ 0) :
    P[X | MeasurableSpace.comap (fun ω => X ω + σ * Z ω) inferInstance] =ᵐ[P]
      fun ω => posteriorMean μ σ (X ω + σ * Z ω) := by
  have hY : Measurable fun ω => X ω + σ * Z ω := hX.add (hZ.const_mul σ)
  have hm := measurable_posteriorMean μ hσ
  have hXint : Integrable X P := by
    rw [← hXlaw] at hμ
    exact (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).mp hμ
  have hmint : Integrable (fun ω => posteriorMean μ σ (X ω + σ * Z ω)) P := by
    have h := integrable_posteriorMean_conv μ hμ hσ
    rw [← map_add_mul_eq_conv hX hZ hXZ hXlaw hZlaw σ] at h
    exact (integrable_map_measure hm.aestronglyMeasurable hY.aemeasurable).mp h
  refine (ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le hXint
    (fun s _ _ => hmint.integrableOn) (fun s hs _ => ?_)
    (hm.comp (comap_measurable _)).aestronglyMeasurable).symm
  exact setIntegral_comap_eq hY (fun g hg hgb =>
    integral_mul_eq_integral_posteriorMean hX hZ hXZ hXlaw hZlaw hμ hσ hg 1 hgb) s hs

/-- (f) **Posterior noise mean = conditional expectation of the noise.** For measurable,
`P`-independent `X ~ μ` (no moment assumption) and `Z ~ N(0,1)` on a probability space, and
`σ ≠ 0`, with `Y = X + σZ`: `E[Z | σ(Y)] = posteriorNoiseMean μ σ ∘ Y` `P`-almost surely
(a version of the conditional expectation, determined up to null sets). -/
theorem condExp_noise_eq_posteriorNoiseMean [IsProbabilityMeasure P] (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hXlaw : P.map X = μ) (hZlaw : P.map Z = gaussianReal 0 1) {σ : ℝ} (hσ : σ ≠ 0) :
    P[Z | MeasurableSpace.comap (fun ω => X ω + σ * Z ω) inferInstance] =ᵐ[P]
      fun ω => posteriorNoiseMean μ σ (X ω + σ * Z ω) := by
  have hY : Measurable fun ω => X ω + σ * Z ω := hX.add (hZ.const_mul σ)
  have hm := measurable_posteriorNoiseMean μ hσ
  have hZint : Integrable Z P := by
    have h : Integrable id (gaussianReal 0 1) := IsGaussian.integrable_id
    rw [← hZlaw] at h
    exact (integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).mp h
  have hmint : Integrable (fun ω => posteriorNoiseMean μ σ (X ω + σ * Z ω)) P := by
    have h := integrable_posteriorNoiseMean_conv μ hσ
    rw [← map_add_mul_eq_conv hX hZ hXZ hXlaw hZlaw σ] at h
    exact (integrable_map_measure hm.aestronglyMeasurable hY.aemeasurable).mp h
  refine (ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le hZint
    (fun s _ _ => hmint.integrableOn) (fun s hs _ => ?_)
    (hm.comp (comap_measurable _)).aestronglyMeasurable).symm
  exact setIntegral_comap_eq hY (fun g hg hgb =>
    integral_mul_noise_eq_integral_posteriorNoiseMean hX hZ hXZ hXlaw hZlaw hσ hg 1 hgb) s hs

/-- **Tweedie's formula with conditional expectations.** For measurable, `P`-independent
`X ~ μ` with `Integrable id μ` and `Z ~ N(0,1)`, `σ ≠ 0` and `Y = X + σZ`, almost surely
`(log p_σ)'(Y) = (E[X | σ(Y)] - Y) / σ²`, where `p_σ = smoothedDensity μ σ` is the density
of `Y`. (The moment assumption is needed only for `E[X | σ(Y)]` to be defined.) -/
theorem tweedie_condExp [IsProbabilityMeasure P] (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ] (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) (hμ : Integrable id μ) {σ : ℝ} (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂P, score1 (smoothedDensity μ σ) (X ω + σ * Z ω) =
      ((P[X | MeasurableSpace.comap (fun ω => X ω + σ * Z ω) inferInstance]) ω -
        (X ω + σ * Z ω)) / σ ^ 2 := by
  filter_upwards [condExp_eq_posteriorMean hX hZ hXZ hXlaw hZlaw hμ hσ] with ω hω
  rw [hω, tweedie μ hσ]

/-- **Tweedie's formula, noise form, with conditional expectations.** For measurable,
`P`-independent `X ~ μ` (no moment assumption) and `Z ~ N(0,1)`, `σ ≠ 0` and `Y = X + σZ`,
almost surely `(log p_σ)'(Y) = -E[Z | σ(Y)] / σ`. -/
theorem tweedie_noise_condExp [IsProbabilityMeasure P] (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ] (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) {σ : ℝ} (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂P, score1 (smoothedDensity μ σ) (X ω + σ * Z ω) =
      -((P[Z | MeasurableSpace.comap (fun ω => X ω + σ * Z ω) inferInstance]) ω) / σ := by
  filter_upwards [condExp_noise_eq_posteriorNoiseMean hX hZ hXZ hXlaw hZlaw hσ] with ω hω
  rw [hω, tweedie_noise μ hσ]

end RandomVariables

/-! ### (g) The `d`-dimensional isotropic version on `Fin d → ℝ` -/

section Isotropic

variable {d : ℕ}

/-- The isotropic Gaussian kernel on `Fin d → ℝ`:
`piGaussKernel σ x y = ∏ᵢ gaussKernel σ (x i) (y i) = (2πσ²)^{-d/2} exp(-∑ᵢ (yᵢ - xᵢ)² / (2σ²))`,
the Lebesgue density at `y` of `N(x, σ² I_d)` (`pi_gaussianReal_eq_withDensity`). -/
noncomputable def piGaussKernel (σ : ℝ) (x y : Fin d → ℝ) : ℝ :=
  ∏ i, gaussKernel σ (x i) (y i)

/-- The `d`-dimensional smoothed density `p_σ(y) = ∫ piGaussKernel σ x y dμ(x)`; for finite `μ`
and `σ ≠ 0` it is the Lebesgue density of `μ ∗ N(0, σ² I_d)`
(`conv_pi_gaussianReal_eq_withDensity`). -/
noncomputable def piSmoothedDensity (μ : Measure (Fin d → ℝ)) (σ : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ x, piGaussKernel σ x y ∂μ

/-- The `d`-dimensional posterior mean, coordinatewise
`m(y)ᵢ = (∫ xᵢ piGaussKernel σ x y dμ(x)) / p_σ(y)`. -/
noncomputable def piPosteriorMean (μ : Measure (Fin d → ℝ)) (σ : ℝ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => (∫ x, x i * piGaussKernel σ x y ∂μ) / piSmoothedDensity μ σ y

/-- The `d`-dimensional posterior noise mean, coordinatewise
`(∫ ((yᵢ - xᵢ)/σ) piGaussKernel σ x y dμ(x)) / p_σ(y)`. -/
noncomputable def piPosteriorNoiseMean (μ : Measure (Fin d → ℝ)) (σ : ℝ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => (∫ x, ((y i - x i) / σ) * piGaussKernel σ x y ∂μ) / piSmoothedDensity μ σ y

/-- The isotropic kernel is nonnegative. -/
lemma piGaussKernel_nonneg (σ : ℝ) (x y : Fin d → ℝ) : 0 ≤ piGaussKernel σ x y :=
  Finset.prod_nonneg fun i _ => gaussKernel_nonneg σ (x i) (y i)

/-- For `σ ≠ 0` the isotropic kernel is strictly positive. -/
lemma piGaussKernel_pos {σ : ℝ} (hσ : σ ≠ 0) (x y : Fin d → ℝ) : 0 < piGaussKernel σ x y :=
  Finset.prod_pos fun i _ => gaussKernel_pos hσ (x i) (y i)

/-- Uniform bound: `piGaussKernel σ x y ≤ ((√(2πσ²))⁻¹)^d` (written as a product). -/
lemma piGaussKernel_le (σ : ℝ) (x y : Fin d → ℝ) :
    piGaussKernel σ x y ≤ ∏ _i : Fin d, (√(2 * π * σ ^ 2))⁻¹ :=
  Finset.prod_le_prod₀ (fun i _ => gaussKernel_nonneg σ (x i) (y i))
    (fun i _ => gaussKernel_le σ (x i) (y i))

/-- Splitting off the `i`-th factor of the isotropic kernel. -/
lemma piGaussKernel_eq_mul_prod_erase (σ : ℝ) (x y : Fin d → ℝ) (i : Fin d) :
    piGaussKernel σ x y =
      gaussKernel σ (x i) (y i) * ∏ j ∈ Finset.univ.erase i, gaussKernel σ (x j) (y j) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

/-- Uniform bound, for `σ ≠ 0`: `|xᵢ - yᵢ| piGaussKernel σ x y` is bounded by a constant
independent of `x` and `y`. -/
lemma abs_sub_mul_piGaussKernel_le {σ : ℝ} (hσ : σ ≠ 0) (x y : Fin d → ℝ) (i : Fin d) :
    |x i - y i| * piGaussKernel σ x y ≤
      (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ *
        ∏ _j ∈ Finset.univ.erase i, (√(2 * π * σ ^ 2))⁻¹ := by
  rw [piGaussKernel_eq_mul_prod_erase σ x y i, ← mul_assoc]
  exact mul_le_mul (abs_sub_mul_gaussKernel_le hσ (x i) (y i))
    (Finset.prod_le_prod₀ (fun j _ => gaussKernel_nonneg σ (x j) (y j))
      (fun j _ => gaussKernel_le σ (x j) (y j)))
    (Finset.prod_nonneg fun j _ => gaussKernel_nonneg σ (x j) (y j)) (by positivity)

/-- `a ↦ gaussKernel σ (f a) (g a)` is continuous when `f` and `g` are. -/
lemma continuous_gaussKernel_comp {α : Type*} [TopologicalSpace α] (σ : ℝ) {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => gaussKernel σ (f a) (g a)) := by
  simp_rw [gaussKernel_eq]
  fun_prop

/-- Joint continuity of `(x, y) ↦ piGaussKernel σ x y`. -/
lemma continuous_piGaussKernel_uncurry (σ : ℝ) :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => piGaussKernel σ p.1 p.2) := by
  unfold piGaussKernel
  exact continuous_finsetProd _ fun i _ => continuous_gaussKernel_comp σ
    ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd)

/-- Continuity of `x ↦ piGaussKernel σ x y`. -/
lemma continuous_piGaussKernel_left (σ : ℝ) (y : Fin d → ℝ) :
    Continuous (fun x => piGaussKernel σ x y) := by
  unfold piGaussKernel
  exact continuous_finsetProd _ fun i _ => continuous_gaussKernel_comp σ
    (continuous_apply i) continuous_const

/-- For any finite measure `μ` on `Fin d → ℝ`, `x ↦ piGaussKernel σ x y` is `μ`-integrable
(bounded and continuous). -/
theorem integrable_piGaussKernel (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] (σ : ℝ)
    (y : Fin d → ℝ) : Integrable (fun x => piGaussKernel σ x y) μ := by
  refine Integrable.of_bound (continuous_piGaussKernel_left σ y).aestronglyMeasurable
    (∏ _i : Fin d, (√(2 * π * σ ^ 2))⁻¹) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (piGaussKernel_nonneg _ _ _)]
  exact piGaussKernel_le σ x y

/-- For finite `μ` and `σ ≠ 0`, `x ↦ ((xᵢ - yᵢ)/c) piGaussKernel σ x y` is `μ`-integrable
(bounded and continuous). -/
theorem integrable_sub_div_mul_piGaussKernel (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : σ ≠ 0) (y : Fin d → ℝ) (i : Fin d) (c : ℝ) :
    Integrable (fun x => ((x i - y i) / c) * piGaussKernel σ x y) μ := by
  refine Integrable.of_bound
    ((((continuous_apply i).sub continuous_const).div_const c).mul
      (continuous_piGaussKernel_left σ y)).aestronglyMeasurable
    ((2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ *
        (∏ _j ∈ Finset.univ.erase i, (√(2 * π * σ ^ 2))⁻¹) / |c|) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (piGaussKernel_nonneg _ _ _), abs_div,
    div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (abs_sub_mul_piGaussKernel_le hσ x y i) (abs_nonneg c)

/-- For finite `μ` and `σ ≠ 0`, `x ↦ xᵢ piGaussKernel σ x y` is `μ`-integrable (bounded and
continuous); no moment assumption on `μ`. -/
theorem integrable_apply_mul_piGaussKernel (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : σ ≠ 0) (y : Fin d → ℝ) (i : Fin d) :
    Integrable (fun x => x i * piGaussKernel σ x y) μ := by
  refine ((integrable_sub_div_mul_piGaussKernel μ hσ y i 1).add
    ((integrable_piGaussKernel μ σ y).const_mul (y i))).congr (ae_of_all _ fun x => ?_)
  simp only [div_one, Pi.add_apply]
  ring

/-- For a probability measure `μ` on `Fin d → ℝ` and `σ ≠ 0`, `0 < p_σ(y)` for every `y`. -/
theorem piSmoothedDensity_pos (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y : Fin d → ℝ) : 0 < piSmoothedDensity μ σ y := by
  unfold piSmoothedDensity
  rw [integral_pos_iff_support_of_nonneg (fun x => piGaussKernel_nonneg σ x y)
    (integrable_piGaussKernel μ σ y)]
  have : Function.support (fun x => piGaussKernel σ x y) = Set.univ :=
    Set.eq_univ_of_forall fun x => (piGaussKernel_pos hσ x y).ne'
  rw [this, measure_univ]
  exact one_pos

/-- For `σ ≠ 0`, the Fréchet derivative of `y ↦ piGaussKernel σ x y` is
`v ↦ ∑ᵢ ((xᵢ - yᵢ)/σ²) piGaussKernel σ x y · vᵢ`. -/
lemma hasFDerivAt_piGaussKernel {σ : ℝ} (hσ : σ ≠ 0) (x y : Fin d → ℝ) :
    HasFDerivAt (fun y => piGaussKernel σ x y)
      (∑ i, (((x i - y i) / σ ^ 2) * piGaussKernel σ x y) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) y := by
  have h := HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun i (y : Fin d → ℝ) => gaussKernel σ (x i) (y i))
    (g' := fun i => (((x i - y i) / σ ^ 2) * gaussKernel σ (x i) (y i)) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
    (x := y) (fun i _ => (hasDerivAt_gaussKernel hσ (x i) (y i)).comp_hasFDerivAt y
      (hasFDerivAt_apply i y))
  refine h.congr_fderiv (Eq.symm ?_)
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [piGaussKernel_eq_mul_prod_erase σ x y i]
  ring

/-- The coordinate projection `Fin d → ℝ → ℝ` has operator norm at most `1` (sup norm). -/
lemma norm_proj_le_one (i : Fin d) :
    ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [ContinuousLinearMap.proj_apply, one_mul]
    exact norm_le_pi_norm v i

/-- `‖∑ᵢ aᵢ • projᵢ‖ ≤ ∑ᵢ |aᵢ|` for the coordinate projections of `Fin d → ℝ`. -/
lemma norm_sum_smul_proj_le (a : Fin d → ℝ) :
    ‖∑ i, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i‖ ≤
      ∑ i, |a i| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |a i| * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i‖
      ≤ |a i| * 1 := mul_le_mul_of_nonneg_left (norm_proj_le_one i) (abs_nonneg _)
    _ = |a i| := mul_one _

/-- For `σ ≠ 0`, the derivative of the isotropic kernel in `y` is bounded in operator norm by
a constant independent of `x` and `y` (the dominating function of the `d`-dim proof). -/
lemma norm_piKernelFDeriv_le {σ : ℝ} (hσ : σ ≠ 0) (x y : Fin d → ℝ) :
    ‖∑ i, (((x i - y i) / σ ^ 2) * piGaussKernel σ x y) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i‖ ≤
      ∑ i : Fin d, (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ *
        (∏ _j ∈ Finset.univ.erase i, (√(2 * π * σ ^ 2))⁻¹) / σ ^ 2 := by
  refine (norm_sum_smul_proj_le _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (piGaussKernel_nonneg _ _ _), abs_div,
    abs_of_nonneg (sq_nonneg σ), div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (abs_sub_mul_piGaussKernel_le hσ x y i) (sq_nonneg σ)

/-- Continuity in `x` of the derivative of the isotropic kernel in `y`. -/
lemma continuous_piKernelFDeriv (σ : ℝ) (y : Fin d → ℝ) :
    Continuous (fun x : Fin d → ℝ => ∑ i, (((x i - y i) / σ ^ 2) * piGaussKernel σ x y) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) :=
  continuous_finsetSum _ fun i _ =>
    ((((continuous_apply i).sub continuous_const).div_const _).mul
      (continuous_piGaussKernel_left σ y)).smul continuous_const

/-- (g) For a finite measure `μ` on `Fin d → ℝ` and `σ ≠ 0`, `p_σ` is Fréchet
differentiable with derivative `∫ ∑ᵢ ((xᵢ - yᵢ)/σ²) piGaussKernel σ x y • projᵢ dμ(x)`
(dominated differentiation with a constant bound). -/
theorem hasFDerivAt_piSmoothedDensity (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y : Fin d → ℝ) :
    HasFDerivAt (piSmoothedDensity μ σ)
      (∫ x, ∑ i, (((x i - y i) / σ ^ 2) * piGaussKernel σ x y) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i ∂μ) y :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun y x => piGaussKernel σ x y)
    (F' := fun y x => ∑ i, (((x i - y i) / σ ^ 2) * piGaussKernel σ x y) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
    (x₀ := y) Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_piGaussKernel_left σ y').aestronglyMeasurable)
    (integrable_piGaussKernel μ σ y)
    (continuous_piKernelFDeriv σ y).aestronglyMeasurable
    (ae_of_all _ fun x y' _ => norm_piKernelFDeriv_le hσ x y') (integrable_const _)
    (ae_of_all _ fun x y' _ => hasFDerivAt_piGaussKernel hσ x y')

/-- (g) For a finite measure `μ` and `σ ≠ 0`,
`∂ᵢ p_σ(y) = ∫ ((xᵢ - yᵢ)/σ²) piGaussKernel σ x y dμ(x)`. -/
theorem partialDeriv_piSmoothedDensity (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y : Fin d → ℝ) (i : Fin d) :
    partialDeriv i (piSmoothedDensity μ σ) y =
      ∫ x, ((x i - y i) / σ ^ 2) * piGaussKernel σ x y ∂μ := by
  have hint : Integrable (fun x : Fin d → ℝ => ∑ j, (((x j - y j) / σ ^ 2) *
      piGaussKernel σ x y) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) μ :=
    Integrable.of_bound (continuous_piKernelFDeriv σ y).aestronglyMeasurable _
      (ae_of_all _ fun x => norm_piKernelFDeriv_le hσ x y)
  unfold partialDeriv
  rw [(hasFDerivAt_piSmoothedDensity μ hσ y).fderiv, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Pi.single_apply]

/-- For finite `μ` and `σ ≠ 0`:
`∫ ((xᵢ - yᵢ)/c) K dμ = (∫ xᵢ K dμ - yᵢ p_σ(y)) / c`, `K = piGaussKernel σ · y`. -/
theorem integral_sub_div_mul_piGaussKernel (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : σ ≠ 0) (y : Fin d → ℝ) (i : Fin d) (c : ℝ) :
    ∫ x, ((x i - y i) / c) * piGaussKernel σ x y ∂μ =
      ((∫ x, x i * piGaussKernel σ x y ∂μ) - y i * piSmoothedDensity μ σ y) / c := by
  unfold piSmoothedDensity
  rw [← integral_const_mul, ← integral_sub (integrable_apply_mul_piGaussKernel μ hσ y i)
    ((integrable_piGaussKernel μ σ y).const_mul (y i)), ← integral_div]
  congr 1
  ext x
  ring

/-- (g) **Tweedie's formula on `Fin d → ℝ`** (isotropic noise). For an arbitrary probability
measure `μ` on `Fin d → ℝ` (no moment assumption) and `σ ≠ 0`, the state score of
`p_σ = μ ∗ N(0, σ² I_d)` is `∇ log p_σ(y) = (piPosteriorMean μ σ y - y) / σ²` for every `y`. -/
theorem tweedie_pi (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0)
    (y : Fin d → ℝ) :
    score (piSmoothedDensity μ σ) y = fun i => (piPosteriorMean μ σ y i - y i) / σ ^ 2 := by
  funext i
  have hd := hasFDerivAt_piSmoothedDensity μ hσ y
  have hp := piSmoothedDensity_pos μ hσ y
  rw [score_apply_of_pos hd.differentiableAt hp i, partialDeriv_piSmoothedDensity μ hσ y i,
    integral_sub_div_mul_piGaussKernel μ hσ y i (σ ^ 2)]
  unfold piPosteriorMean
  field_simp

/-- (g) Mean / noise equivalence in `d` dimensions, coordinatewise:
`piPosteriorNoiseMean μ σ y i = (yᵢ - piPosteriorMean μ σ y i) / σ`, for probability `μ`,
`σ ≠ 0`. -/
theorem piPosteriorNoiseMean_eq (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y : Fin d → ℝ) (i : Fin d) :
    piPosteriorNoiseMean μ σ y i = (y i - piPosteriorMean μ σ y i) / σ := by
  have hp := (piSmoothedDensity_pos μ hσ y).ne'
  have h : ∫ x, ((y i - x i) / σ) * piGaussKernel σ x y ∂μ =
      -∫ x, ((x i - y i) / σ) * piGaussKernel σ x y ∂μ := by
    rw [← integral_neg]
    congr 1
    ext x
    ring
  unfold piPosteriorNoiseMean piPosteriorMean
  rw [h, integral_sub_div_mul_piGaussKernel μ hσ y i σ]
  field_simp
  ring

/-- (g) **Tweedie's formula on `Fin d → ℝ`, noise form.** For an arbitrary probability
measure `μ` and `σ ≠ 0`, `∇ log p_σ(y) = -(piPosteriorNoiseMean μ σ y) / σ`. -/
theorem tweedie_noise_pi (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) (y : Fin d → ℝ) :
    score (piSmoothedDensity μ σ) y = fun i => -piPosteriorNoiseMean μ σ y i / σ := by
  rw [tweedie_pi μ hσ y]
  funext i
  rw [piPosteriorNoiseMean_eq μ hσ y i]
  field_simp
  ring

/-- For `σ ≠ 0`, the product law `⊗ᵢ N(xᵢ, σ²)` (i.e. `N(x, σ² I_d)`) on `Fin d → ℝ` has
Lebesgue density `piGaussKernel σ x`. -/
theorem pi_gaussianReal_eq_withDensity {σ : ℝ} (hσ : σ ≠ 0) (x : Fin d → ℝ) :
    Measure.pi (fun i => gaussianReal (x i) ⟨σ ^ 2, sq_nonneg σ⟩) =
      volume.withDensity (fun y => ENNReal.ofReal (piGaussKernel σ x y)) := by
  refine Measure.pi_eq fun s hs => ?_
  have hind : (Set.univ.pi s).indicator (fun y => ENNReal.ofReal (piGaussKernel σ x y)) =
      fun y => ENNReal.ofReal (∏ i, (s i).indicator (fun t => gaussKernel σ (x i) t) (y i)) := by
    ext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hy i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by
        simpa [Set.mem_univ_pi] using hy
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  have hint : ∀ i, Integrable ((s i).indicator fun t => gaussKernel σ (x i) t) :=
    fun i => (integrable_gaussKernel_right σ (x i)).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs), hind, ← ofReal_integral_eq_lintegral_ofReal
    (by rw [volume_pi]; exact Integrable.fintype_prod hint)
    (ae_of_all _ fun y => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun t _ => gaussKernel_nonneg σ (x i) t) _),
    volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun t =>
      Set.indicator_nonneg (fun t _ => gaussKernel_nonneg σ (x i) t) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral _ (var_ne_zero hσ), integral_indicator (hs i)]
  rfl

/-- Translating `N(0, σ² I_d)` by `x` gives `⊗ᵢ N(xᵢ, σ²)`. -/
theorem pi_gaussianReal_map_const_add (σ : ℝ) (x : Fin d → ℝ) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩).map (x + ·) =
      Measure.pi (fun i => gaussianReal (x i) ⟨σ ^ 2, sq_nonneg σ⟩) := by
  have : ∀ i, SigmaFinite ((gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩).map (x i + ·)) := fun i => by
    rw [var_eq_mk, gaussianReal_map_const_add]
    infer_instance
  have h := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)
    (f := fun i t => x i + t) (fun i => (measurable_const_add (x i)).aemeasurable)
  simp only [var_eq_mk, gaussianReal_map_const_add, zero_add] at h
  exact h

/-- (g) **Law identification in `d` dimensions.** For any finite measure `μ` on `Fin d → ℝ`
and `σ ≠ 0`, `μ ∗ N(0, σ² I_d) = volume.withDensity (ofReal ∘ piSmoothedDensity μ σ)`, where
`N(0, σ² I_d)` is the product measure `⊗ᵢ N(0, σ²)`. For a probability measure `μ` this says
that `piSmoothedDensity μ σ` is the density of `X + σZ`, `X ~ μ` independent of
`Z ~ N(0, I_d)`. -/
theorem conv_pi_gaussianReal_eq_withDensity (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : σ ≠ 0) :
    μ ∗ Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
      volume.withDensity (fun y => ENNReal.ofReal (piSmoothedDensity μ σ y)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator_one hs,
    Measure.lintegral_conv (measurable_one.indicator hs)]
  have hx : ∀ x : Fin d → ℝ, ∫⁻ z, s.indicator 1 (x + z)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
      ∫⁻ y in s, ENNReal.ofReal (piGaussKernel σ x y) := fun x => by
    have h := lintegral_map
      (μ := Measure.pi fun _ : Fin d => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)
      (f := s.indicator 1) (g := (x + ·)) (measurable_one.indicator hs) (measurable_const_add x)
    rw [← h, pi_gaussianReal_map_const_add, pi_gaussianReal_eq_withDensity hσ,
      lintegral_indicator_one hs, withDensity_apply _ hs]
  simp_rw [hx]
  rw [lintegral_lintegral_swap
    (continuous_piGaussKernel_uncurry σ).measurable.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [piSmoothedDensity, ofReal_integral_eq_lintegral_ofReal (integrable_piGaussKernel μ σ y)
    (ae_of_all _ fun x => piGaussKernel_nonneg σ x y)]

/-- For every `x`, `y ↦ piGaussKernel σ x y` is Lebesgue integrable on `Fin d → ℝ`. -/
lemma integrable_piGaussKernel_right (σ : ℝ) (x : Fin d → ℝ) :
    Integrable (fun y => piGaussKernel σ x y) := by
  unfold piGaussKernel
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun i t => gaussKernel σ (x i) t)
    fun i => integrable_gaussKernel_right σ (x i)

/-- For `σ ≠ 0`, `∫ piGaussKernel σ x y dy = 1`. -/
lemma integral_piGaussKernel_right {σ : ℝ} (hσ : σ ≠ 0) (x : Fin d → ℝ) :
    ∫ y, piGaussKernel σ x y = 1 := by
  unfold piGaussKernel
  rw [volume_pi, integral_fintype_prod_eq_prod (f := fun i t => gaussKernel σ (x i) t)]
  simp [integral_gaussKernel_right hσ]

/-- For probability `μ` and `σ ≠ 0`: `m(y)ᵢ p_σ(y) = ∫ xᵢ piGaussKernel σ x y dμ(x)`. -/
theorem piPosteriorMean_mul_piSmoothedDensity (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) (y : Fin d → ℝ) (i : Fin d) :
    piPosteriorMean μ σ y i * piSmoothedDensity μ σ y = ∫ x, x i * piGaussKernel σ x y ∂μ := by
  unfold piPosteriorMean
  exact div_mul_cancel₀ _ (piSmoothedDensity_pos μ hσ y).ne'

/-- If `μ` is finite, `σ ≠ 0` and `x ↦ xᵢ` is `μ`-integrable, then
`(x, y) ↦ xᵢ piGaussKernel σ x y` is integrable for `μ ⊗ Lebesgue`. -/
theorem integrable_prod_apply_mul_piGaussKernel (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : σ ≠ 0) (i : Fin d) (hμ : Integrable (fun x => x i) μ) :
    Integrable (Function.uncurry fun x y => x i * piGaussKernel σ x y) (μ.prod volume) := by
  have hmeas : Measurable (Function.uncurry fun x y => x i * piGaussKernel σ x y) :=
    ((measurable_pi_apply i).comp measurable_fst).mul
      (continuous_piGaussKernel_uncurry σ).measurable
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x => (integrable_piGaussKernel_right σ x).const_mul (x i), ?_⟩
  refine hμ.norm.congr (ae_of_all _ fun x => ?_)
  simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (piGaussKernel_nonneg σ x _)]
  rw [integral_const_mul, integral_piGaussKernel_right hσ, mul_one]

/-- (g) **Posterior-mean characterisation in `d` dimensions, density form.** For a probability
measure `μ` on `Fin d → ℝ` with `x ↦ xᵢ` integrable, `σ ≠ 0` and measurable `g` with
`|g| ≤ M`: `∫ (∫ g(y) xᵢ K(x, y) dy) dμ(x) = ∫ g(y) m(y)ᵢ p_σ(y) dy`, i.e.
`E[g(Y) Xᵢ] = E[g(Y) m(Y)ᵢ]`, so `m(Y)ᵢ` is a version of `E[Xᵢ | Y]` (up to null sets; no
regular conditional version is chosen). -/
theorem integral_integral_apply_mul_piGaussKernel_eq_piPosteriorMean
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {σ : ℝ} (hσ : σ ≠ 0) (i : Fin d)
    (hμ : Integrable (fun x => x i) μ) {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) (M : ℝ)
    (hM : ∀ y, |g y| ≤ M) :
    ∫ x, (∫ y, g y * x i * piGaussKernel σ x y) ∂μ =
      ∫ y, g y * piPosteriorMean μ σ y i * piSmoothedDensity μ σ y := by
  have hint : Integrable (Function.uncurry fun x y => g y * x i * piGaussKernel σ x y)
      (μ.prod volume) := by
    refine ((integrable_prod_apply_mul_piGaussKernel μ hσ i hμ).bdd_mul (c := M)
      (hg.comp measurable_snd).aestronglyMeasurable (ae_of_all _ fun p => ?_)).congr
      (ae_of_all _ fun ⟨x, y⟩ => ?_)
    · rw [Real.norm_eq_abs]
      exact hM _
    · simp only [Function.comp_apply, Function.uncurry_apply_pair]
      ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [mul_assoc, piPosteriorMean_mul_piSmoothedDensity μ hσ y i, ← integral_const_mul]
  congr 1
  ext x
  ring

end Isotropic

end FormalizeSampling.Tweedie
