module

public import FormalizeSampling.Identities.Tweedie
public import FormalizeSampling.Kernels.GaussianKernels

/-!
# Affine-Gaussian posterior score and the OU posterior score (rdMC Lemma 1, SE-3)

Registry ID covered: **SE-3** (Ornstein–Uhlenbeck posterior score identity, *Reverse
Diffusion Monte Carlo* (rdMC, Huang, Dong, Hao, Ma, Zhang, ICLR 2024, arXiv:2307.02037 v3),
§3.1, **Lemma 1**, Eq. (4), proof App. C.1, Eq. (13)). Everything is derived as a corollary
of Tweedie's formula (SE-3, `FormalizeSampling.Tweedie`) applied to the image law
`μ.map (a * ·)` (resp. `μ.map (a • ·)` on `Fin d → ℝ`); the Tweedie proof is not repeated.

Paper statement (rdMC Lemma 1, §3.1, reverse-time index `t`):
"Assume that Eq. (1) defines the forward process. The score function can be rewritten as
`∇ₓ ln p_{T-t}(x) = E_{x₀ ∼ q_{T-t}(· | x)} (e^{-(T-t)} x₀ - x) / (1 - e^{-2(T-t)})`,
`q_{T-t}(x₀ | x) ∝ exp(-f_*(x₀) - ‖x - e^{-(T-t)} x₀‖² / (2(1 - e^{-2(T-t)})))`."
In forward time `s = T - t > 0`: `∇ ln p_s(x) = (e^{-s} E[X₀ | Xₛ = x] - x) / (1 - e^{-2s})`.
Here it is proved for an arbitrary prior law `μ` of `X₀` with no moment assumption (the density
case `p_* ∝ e^{-f_*}` is `ouPosteriorScore_density`), and the hypothesis `s > 0` (`t < T`) is
explicit.

## Setting and conventions

* `μ` is the law of `X` (a probability measure on `ℝ`; no density and no moment assumption),
  `Z ∼ N(0, 1)` is independent of `X`, `a : ℝ`, `σ ≠ 0`, and `Y = a X + σ Z` (the *affine
  Gaussian channel*). Mathlib's `gaussianReal m v` takes the **variance** `v : ℝ≥0`; the
  variance `σ²` is written `⟨σ ^ 2, sq_nonneg σ⟩`. `gaussKernel σ m y` is the density at `y`
  of `N(m, σ²)` (from `Foundations/HeatKernel.lean`).
* `affineDensity μ a σ y = ∫ gaussKernel σ (a x) y dμ(x)` is the Lebesgue density of `Y`
  (`map_conv_gaussianReal_eq_withDensity`, `map_affine_add_mul_eq_withDensity`).
  `affineDensity`, `affineDensity_eq_smoothedDensity` and the law identifications
  `map_conv_gaussianReal_eq_withDensity`, `bind_gaussianReal_affine_eq_withDensity` are in
  `Foundations/HeatKernel.lean`.
* `affinePosteriorMean μ a σ y = (∫ x gaussKernel σ (a x) y dμ(x)) / affineDensity μ a σ y` is
  the explicit Bayes ratio, defined for **every** `y`; it is a version of `E[X | Y = y]`
  (`condExp_eq_affinePosteriorMean`). `affinePosterior μ a σ y` is the posterior *law*
  `μ(dx | y) ∝ gaussKernel σ (a x) y μ(dx)` (a probability measure, `withDensity` form), whose
  mean is `affinePosteriorMean μ a σ y`.
* **OU convention (rdMC Eq. (1)).** The forward process is `dXₛ = -Xₛ ds + √2 dBₛ`, i.e. the
  rate-`1` instance of `FormalizeSampling.OU.ouKernel a s x = N(e^{-as} x, 1 - e^{-2as})`
  (variance, *not* standard deviation). With `a_s = e^{-s}` and `σ_s² = 1 - e^{-2s}` one has
  `Xₛ = a_s X₀ + σ_s Z`. `ouDensity μ s = affineDensity μ (e^{-s}) (√(1 - e^{-2s}))` is the
  Lebesgue density of `Law(Xₛ) = μ.bind (ouKernel 1 s)` (`bind_ouKernel_one_eq_withDensity`);
  `ouDensityRate μ a s` is the rate-`a` analogue.
* Time index: rdMC's Lemma 1 is written with the *reverse-time* index, for
  `∇ ln p_{T-t}`; every statement below uses the forward time `s` (`= T - t` in the paper),
  for which the identities agree verbatim after the substitution `s = T - t`. The OU time
  must be strictly positive: at `s = 0` the noise level `σ₀ = 0` and `Law(X₀) = μ` need not
  have a density.
* Scores are one-dimensional state scores `score1 p y = (log p)'(y)` on `ℝ`, and state
  scores `score p y = ∇ log p(y)` (`Foundations/VectorCalculus.lean`) on `Fin d → ℝ`, where
  the noise is isotropic, `Z ∼ N(0, I_d) = ⊗ᵢ N(0, 1)`, and `piGaussKernel` is the density of
  `N(m, σ² I_d)`.

## Main results

* (a) `affineDensity_eq_smoothedDensity`, `mul_affinePosteriorMean`,
  `affinePosteriorNoiseMean_eq_posteriorNoiseMean`: reduction to Tweedie for `μ.map (a * ·)`.
* (b) `score1_affineDensity` (affine Tweedie):
  `(log p)'(y) = (a * affinePosteriorMean μ a σ y - y) / σ²`, and the noise forms
  `score1_affineDensity_noise`, `affinePosteriorNoiseMean_eq`. No moment assumption on `μ`.
* (c) `map_conv_gaussianReal_eq_withDensity`, `bind_gaussianReal_affine_eq_withDensity`,
  `map_affine_add_mul_eq_withDensity` (law identification), `bind_ouKernel_eq_withDensity`
  and `bind_ouKernel_one_eq_withDensity` (the OU marginal `μ.bind (ouKernel a s)` has
  Lebesgue density `ouDensityRate μ a s`, resp. `ouDensity μ s`, for `a, s > 0`).
* (d) **rdMC Lemma 1** (`ouPosteriorScore`, SE-3): for `s > 0`,
  `(log p_s)'(y) = (e^{-s} E[X₀ | Xₛ = y] - y) / (1 - e^{-2s})`; the general-rate version
  `score1_ouDensityRate`; the paper's own ratio form with the unnormalised posterior weight
  `exp(-(y - e^{-s} x₀)² / (2(1 - e^{-2s})))` (`ouPosteriorScore_ratio`) and, for a prior with a
  Lebesgue density `p₀`, the form `E_{x₀ ∼ q_s(· | y)}[(e^{-s} x₀ - y)/(1 - e^{-2s})]` with
  `q_s(x₀ | y) ∝ p₀(x₀) exp(-(y - e^{-s} x₀)² / (2(1 - e^{-2s})))` (`ouPosteriorScore_density`).
* (e) Conditional-expectation reading: `integral_integral_mul_gaussKernel_affine_eq`
  (density form `E[g(Y) X] = E[g(Y) m(Y)]`, from Tweedie's
  `integral_integral_mul_gaussKernel_eq_posteriorMean`), `condExp_eq_affinePosteriorMean`
  (`E[X | σ(Y)] = affinePosteriorMean μ a σ ∘ Y` a.s., for `a ≠ 0` and `Integrable id μ`,
  from Tweedie's `condExp_eq_posteriorMean`) and `ouPosteriorScore_condExp`
  (`(log p_s)'(Xₛ) = (e^{-s} E[X₀ | σ(Xₛ)] - Xₛ)/(1 - e^{-2s})` almost surely).
* Posterior law: `isProbabilityMeasure_affinePosterior`, `integral_affinePosterior`,
  `integral_id_affinePosterior`, and `memLp_id_affinePosterior` (for `a ≠ 0` the posterior
  always has a finite second moment), used by Monte Carlo score
  oracles (`ScoreEstimation/MonteCarlo.lean`).
* Dimension `d` (rdMC's own setting, isotropic noise): `piAffineDensity_eq_piSmoothedDensity`,
  `mul_piAffinePosteriorMean`, `score_piAffineDensity` (affine Tweedie),
  `map_conv_pi_gaussianReal_eq_withDensity` and `map_conv_pi_ouVar_eq_withDensity` (law
  identification), **`ouPosteriorScore_pi`**
  (`∇ ln p_s(y) = (1 - e^{-2s})⁻¹ • (e^{-s} • E[X₀ | Xₛ = y] - y)` for `s > 0`), and the
  density-form posterior characterisation `integral_integral_apply_mul_piGaussKernel_affine_eq`.

## What is NOT proved here

* In dimension `d` only the score identity, the law identification (in convolution form here;
  the `d`-dimensional OU kernel is `OULangevinDecayPi.ouKernelPi`) and the density-form posterior
  characterisation are proved. The random-variable / conditional-expectation form
  (`E[X₀ | σ(Xₛ)]`), the noise form, the ratio / density forms with unnormalised weights and
  the posterior law are proved only in dimension one. Anisotropic or matrix-preconditioned
  noise is not covered.
* No SDE is formalised: `Xₛ = e^{-s} X₀ + σₛ Z` (equivalently `ouKernel 1 s`) is taken as the
  definition of the forward OU marginal, as in `Kernels/GaussianKernels.lean`; that it is
  the law of a solution of rdMC's Eq. (1) is a modelling input.
* `s = 0` is excluded (the rate version assumes `0 < a` and `0 < s`). The conditional-expectation
  statements need `a ≠ 0` (automatic for OU) and `Integrable id μ` (needed for `E[X₀ | ·]` to
  be defined in Mathlib); they hold only up to null sets, and no regular conditional
  distribution is constructed or chosen (the posterior law `affinePosterior` is the canonical
  Bayes version for every `y`, but its identification as a regular conditional distribution
  is not proved).
* The paper's posterior written with `p₀ ∝ e^{-f₀}` is covered through a general density
  `p₀` (`ouPosteriorScore_density`); the constant `Z` of `e^{-f₀} / Z` is not separately
  formalised.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace FormalizeSampling.OUPosterior

open FormalizeSampling.Tweedie FormalizeSampling.OU

/-! ### Definitions -/

/-- The explicit Bayes posterior mean of `X` given `Y = a X + σ Z = y`:
`affinePosteriorMean μ a σ y = (∫ x gaussKernel σ (a x) y dμ(x)) / affineDensity μ a σ y`.
It is defined for every `y` (for a probability `μ` and `σ ≠ 0` the denominator is positive,
`affineDensity_pos`), and it is a version of `E[X | Y = y]`
(`condExp_eq_affinePosteriorMean`). -/
noncomputable def affinePosteriorMean (μ : Measure ℝ) (a σ y : ℝ) : ℝ :=
  (∫ x, x * gaussKernel σ (a * x) y ∂μ) / affineDensity μ a σ y

/-- The explicit Bayes posterior mean of the noise `Z = (Y - a X)/σ` given `Y = y`:
`(∫ ((y - a x)/σ) gaussKernel σ (a x) y dμ(x)) / affineDensity μ a σ y`. -/
noncomputable def affinePosteriorNoiseMean (μ : Measure ℝ) (a σ y : ℝ) : ℝ :=
  (∫ x, ((y - a * x) / σ) * gaussKernel σ (a * x) y ∂μ) / affineDensity μ a σ y

/-- The Bayes posterior law of `X` given `Y = a X + σ Z = y`:
`μ(dx | y) = gaussKernel σ (a x) y / affineDensity μ a σ y · μ(dx)`. For a probability `μ`
and `σ ≠ 0` it is a probability measure (`isProbabilityMeasure_affinePosterior`) with mean
`affinePosteriorMean μ a σ y` (`integral_id_affinePosterior`). In rdMC notation (forward
time `s`, `a = e^{-s}`, `σ² = 1 - e^{-2s}`) this is the posterior `q_s(· | y)` of Eq. (4). -/
noncomputable def affinePosterior (μ : Measure ℝ) (a σ y : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ENNReal.ofReal (gaussKernel σ (a * x) y / affineDensity μ a σ y)

/-- The Lebesgue density of the OU marginal `Law(Xₛ)` for rdMC's forward process
`dXₛ = -Xₛ ds + √2 dBₛ`, `X₀ ∼ μ`: `Xₛ = e^{-s} X₀ + √(1 - e^{-2s}) Z`, so
`ouDensity μ s = affineDensity μ (e^{-s}) (√(1 - e^{-2s}))`
(`bind_ouKernel_one_eq_withDensity`, for `s > 0`). -/
noncomputable def ouDensity (μ : Measure ℝ) (s : ℝ) : ℝ → ℝ :=
  affineDensity μ (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))

/-- The Lebesgue density of the rate-`a` OU marginal `μ.bind (ouKernel a s)`
(`dXₛ = -a Xₛ ds + √(2a) dBₛ`): `affineDensity μ (e^{-as}) (√(1 - e^{-2as}))`
(`bind_ouKernel_eq_withDensity`, for `a, s > 0`). -/
noncomputable def ouDensityRate (μ : Measure ℝ) (a s : ℝ) : ℝ → ℝ :=
  affineDensity μ (Real.exp (-a * s)) (Real.sqrt (1 - Real.exp (-2 * a * s)))

/-- The rate-`1` OU density is `ouDensity`: `ouDensityRate μ 1 s = ouDensity μ s`. -/
theorem ouDensityRate_one (μ : Measure ℝ) (s : ℝ) : ouDensityRate μ 1 s = ouDensity μ s := by
  simp [ouDensityRate, ouDensity]

/-! ### (a) Reduction to Tweedie for the image law `μ.map (a * ·)` -/

/-- Change of variables in the posterior numerator: for every measure `μ` and all `a, σ, y`,
`∫ x' gaussKernel σ x' y d(μ.map (a * ·))(x') = a * ∫ x gaussKernel σ (a x) y dμ(x)`. -/
theorem integral_mul_gaussKernel_map (μ : Measure ℝ) (a σ y : ℝ) :
    ∫ x, x * gaussKernel σ x y ∂(μ.map (fun x => a * x)) =
      a * ∫ x, x * gaussKernel σ (a * x) y ∂μ := by
  rw [integral_map (f := fun x => x * gaussKernel σ x y) (measurable_const_mul a).aemeasurable
    (continuous_id.mul (continuous_gaussKernel_left σ y)).aestronglyMeasurable,
    ← integral_const_mul]
  simp_rw [mul_assoc]

/-- (a) For every measure `μ` and all `a, σ, y`: the posterior mean of `a X` given `Y = y`
(Tweedie's `posteriorMean` for the image law `μ.map (a * ·)`) is `a` times the posterior mean
of `X`: `a * affinePosteriorMean μ a σ y = posteriorMean (μ.map (a * ·)) σ y`. -/
theorem mul_affinePosteriorMean (μ : Measure ℝ) (a σ y : ℝ) :
    a * affinePosteriorMean μ a σ y = posteriorMean (μ.map (fun x => a * x)) σ y := by
  rw [posteriorMean, integral_mul_gaussKernel_map, ← affineDensity_eq_smoothedDensity,
    affinePosteriorMean, mul_div_assoc]

/-- (a) For every measure `μ` and all `a, σ, y`, the affine posterior noise mean is Tweedie's
posterior noise mean for the image law:
`affinePosteriorNoiseMean μ a σ y = posteriorNoiseMean (μ.map (a * ·)) σ y`. -/
theorem affinePosteriorNoiseMean_eq_posteriorNoiseMean (μ : Measure ℝ) (a σ y : ℝ) :
    affinePosteriorNoiseMean μ a σ y = posteriorNoiseMean (μ.map (fun x => a * x)) σ y := by
  rw [posteriorNoiseMean, integral_map (f := fun x => ((y - x) / σ) * gaussKernel σ x y)
    (measurable_const_mul a).aemeasurable (((continuous_const.sub continuous_id).div_const σ).mul
      (continuous_gaussKernel_left σ y)).aestronglyMeasurable,
    ← affineDensity_eq_smoothedDensity, affinePosteriorNoiseMean]

/-- The image of a probability measure under `x ↦ a x` is a probability measure. -/
private lemma isProbabilityMeasure_map_mul (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    IsProbabilityMeasure (μ.map (fun x => a * x)) :=
  inferInstance

/-- The affine channel density is nonnegative, for every measure `μ` and all `a, σ, y`. -/
theorem affineDensity_nonneg (μ : Measure ℝ) (a σ y : ℝ) : 0 ≤ affineDensity μ a σ y :=
  integral_nonneg fun x => gaussKernel_nonneg σ (a * x) y

/-- For a probability measure `μ`, any `a` and `σ ≠ 0`, the affine channel density is
strictly positive everywhere. -/
theorem affineDensity_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) (y : ℝ) : 0 < affineDensity μ a σ y := by
  have := isProbabilityMeasure_map_mul μ a
  rw [affineDensity_eq_smoothedDensity]
  exact smoothedDensity_pos _ hσ y

/-- For a finite measure `μ`, any `a` and `σ ≠ 0`, the affine channel density is
differentiable, with `p'(y) = ∫ ((a x - y)/σ²) gaussKernel σ (a x) y dμ(x)`. -/
theorem hasDerivAt_affineDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) (y : ℝ) :
    HasDerivAt (affineDensity μ a σ)
      (∫ x, ((a * x - y) / σ ^ 2) * gaussKernel σ (a * x) y ∂μ) y := by
  have h := hasDerivAt_smoothedDensity (μ.map (fun x => a * x)) hσ y
  rw [integral_map (f := fun x => ((x - y) / σ ^ 2) * gaussKernel σ x y)
    (measurable_const_mul a).aemeasurable ((((continuous_id.sub continuous_const).div_const
      (σ ^ 2)).mul
      (continuous_gaussKernel_left σ y))).aestronglyMeasurable,
    ← affineDensity_eq_smoothedDensity] at h
  exact h

/-- For a finite measure `μ`, any `a` and `σ ≠ 0`, the affine channel density is continuous. -/
theorem continuous_affineDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) : Continuous (affineDensity μ a σ) := by
  rw [affineDensity_eq_smoothedDensity]
  exact continuous_smoothedDensity _ hσ

/-! ### (b) Affine Tweedie formula -/

/-- (b) **Affine Tweedie formula.** For an *arbitrary* probability measure `μ` on `ℝ` (no
moment assumption), any `a : ℝ`, `σ ≠ 0` and every `y`, the score of the density of
`Y = a X + σ Z` is
`(log p)'(y) = (a * affinePosteriorMean μ a σ y - y) / σ²`, i.e.
`∇ log p(y) = (a E[X | Y = y] - y) / σ²`. Proof: Tweedie (`Tweedie.tweedie`) for the image
law `μ.map (a * ·)`, plus `mul_affinePosteriorMean`. -/
theorem score1_affineDensity (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) (y : ℝ) :
    score1 (affineDensity μ a σ) y = (a * affinePosteriorMean μ a σ y - y) / σ ^ 2 := by
  have := isProbabilityMeasure_map_mul μ a
  rw [affineDensity_eq_smoothedDensity, tweedie _ hσ, mul_affinePosteriorMean]

/-- (b) Noise form of the affine Tweedie formula: for any probability measure `μ`, any `a`,
`σ ≠ 0` and `y`, `(log p)'(y) = -affinePosteriorNoiseMean μ a σ y / σ`
("`∇ log p = -E[Z | Y]/σ`"). -/
theorem score1_affineDensity_noise (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) (y : ℝ) :
    score1 (affineDensity μ a σ) y = -affinePosteriorNoiseMean μ a σ y / σ := by
  have := isProbabilityMeasure_map_mul μ a
  rw [affineDensity_eq_smoothedDensity, tweedie_noise _ hσ,
    affinePosteriorNoiseMean_eq_posteriorNoiseMean]

/-- (b) Mean / noise equivalence for the affine channel: for any probability measure `μ`, any
`a`, `σ ≠ 0` and `y`,
`affinePosteriorNoiseMean μ a σ y = (y - a * affinePosteriorMean μ a σ y) / σ`
("`E[Z | Y] = (Y - a E[X | Y])/σ`"). -/
theorem affinePosteriorNoiseMean_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) (y : ℝ) :
    affinePosteriorNoiseMean μ a σ y = (y - a * affinePosteriorMean μ a σ y) / σ := by
  have := isProbabilityMeasure_map_mul μ a
  rw [affinePosteriorNoiseMean_eq_posteriorNoiseMean, posteriorNoiseMean_eq _ hσ,
    mul_affinePosteriorMean]

/-! ### (c) Law identification -/

/-- (c) Random-variable form: for measurable, `P`-independent `X ∼ μ` and `Z ∼ N(0, 1)` on a
probability space, any `a` and `σ ≠ 0`, `Law(a X + σ Z)` has Lebesgue density
`affineDensity μ a σ`. -/
theorem map_affine_add_mul_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) {μ : Measure ℝ} (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    P.map (fun ω => a * X ω + σ * Z ω) =
      volume.withDensity (fun y => ENNReal.ofReal (affineDensity μ a σ y)) := by
  have hX' : Measurable fun ω => a * X ω := hX.const_mul a
  have hXZ' : IndepFun (fun ω => a * X ω) Z P := hXZ.comp (measurable_const_mul a) measurable_id
  have hlaw : P.map (fun ω => a * X ω) = μ.map (fun x => a * x) := by
    rw [← hXlaw, Measure.map_map (measurable_const_mul a) hX]
    rfl
  rw [map_add_mul_eq_withDensity hX' hZ hXZ' hlaw hZlaw hσ, ← affineDensity_eq_smoothedDensity]

/-- For `0 < a` and `0 < s`, the OU variance is positive: `0 < 1 - e^{-2as}`. -/
theorem one_sub_exp_pos {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    0 < 1 - Real.exp (-2 * a * s) := by
  rw [sub_pos, Real.exp_lt_one_iff]
  nlinarith [mul_pos ha hs]

/-- For `0 < a` and `0 < s`, the OU transition variance `ouVar a s` is `σ²` with
`σ = √(1 - e^{-2as})`, as an element of `ℝ≥0`. -/
theorem ouVar_eq_sq_sqrt {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ouVar a s = ⟨Real.sqrt (1 - Real.exp (-2 * a * s)) ^ 2, sq_nonneg _⟩ := by
  ext
  rw [coe_ouVar ha.le hs.le]
  exact (Real.sq_sqrt (one_sub_exp_pos ha hs).le).symm

/-- (c) **OU marginal, general rate.** For a probability measure `μ` and `0 < a`, `0 < s`,
the OU marginal `μ.bind (ouKernel a s)` (the law of `Xₛ` for `X₀ ∼ μ`, with
`ouKernel a s x = N(e^{-as} x, 1 - e^{-2as})`) has Lebesgue density `ouDensityRate μ a s`. -/
theorem bind_ouKernel_eq_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ] {a s : ℝ}
    (ha : 0 < a) (hs : 0 < s) :
    μ.bind (ouKernel a s) =
      volume.withDensity (fun y => ENNReal.ofReal (ouDensityRate μ a s y)) := by
  have hσ : Real.sqrt (1 - Real.exp (-2 * a * s)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (one_sub_exp_pos ha hs)
  have hk : (ouKernel a s : ℝ → Measure ℝ) = fun x => gaussianReal (Real.exp (-a * s) * x)
      ⟨Real.sqrt (1 - Real.exp (-2 * a * s)) ^ 2, sq_nonneg _⟩ := by
    funext x
    rw [ouKernel_apply, ouVar_eq_sq_sqrt ha hs]
  rw [hk, bind_gaussianReal_affine_eq_withDensity μ _ hσ]
  rfl

/-- (c) **OU marginal (rdMC Eq. (1)).** For a probability measure `μ` and `0 < s`, the law of
`Xₛ` for rdMC's forward OU process started at `X₀ ∼ μ`, namely `μ.bind (ouKernel 1 s)` with
`ouKernel 1 s x = N(e^{-s} x, 1 - e^{-2s})`, has Lebesgue density `ouDensity μ s`. -/
theorem bind_ouKernel_one_eq_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ}
    (hs : 0 < s) :
    μ.bind (ouKernel 1 s) = volume.withDensity (fun y => ENNReal.ofReal (ouDensity μ s y)) := by
  rw [bind_ouKernel_eq_withDensity μ one_pos hs, ouDensityRate_one]

/-! ### (d) rdMC Lemma 1 (SE-3) -/

/-- For `0 < s`, `σₛ = √(1 - e^{-2s}) ≠ 0`. -/
theorem sqrt_one_sub_exp_ne_zero {s : ℝ} (hs : 0 < s) :
    Real.sqrt (1 - Real.exp (-2 * s)) ≠ 0 := by
  have h := one_sub_exp_pos one_pos hs
  rw [mul_one] at h
  exact Real.sqrt_ne_zero'.mpr h

/-- (d) **rdMC Lemma 1 (SE-3), forward time.** Let `μ` be any probability measure on `ℝ`
(the law of `X₀`; no density and no moment assumption) and `s > 0`. With `a_s = e^{-s}`,
`σ_s² = 1 - e^{-2s}` and `p_s = ouDensity μ s` the density of `Xₛ = a_s X₀ + σ_s Z`
(`bind_ouKernel_one_eq_withDensity`), for every `y`
`(log p_s)'(y) = (e^{-s} E[X₀ | Xₛ = y] - y) / (1 - e^{-2s})`,
where `E[X₀ | Xₛ = y]` is the explicit Bayes posterior mean
`affinePosteriorMean μ (e^{-s}) (√(1 - e^{-2s})) y` (a version of the conditional
expectation, `ouPosteriorScore_condExp`). rdMC states Lemma 1 for `∇ ln p_{T-t}` in reverse time;
the identity is the same after `s = T - t`. The hypothesis `s > 0` is kept explicit: at
`s = 0` there is no noise, `Law(X₀) = μ` need not have a density, and the Lean objects
degenerate to junk values (`gaussKernel 0 = 0`). -/
theorem ouPosteriorScore (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) (y : ℝ) :
    score1 (ouDensity μ s) y =
      (Real.exp (-s) * affinePosteriorMean μ (Real.exp (-s))
          (Real.sqrt (1 - Real.exp (-2 * s))) y - y) / (1 - Real.exp (-2 * s)) := by
  have h := one_sub_exp_pos one_pos hs
  rw [mul_one] at h
  rw [ouDensity, score1_affineDensity μ _ (sqrt_one_sub_exp_ne_zero hs), Real.sq_sqrt h.le]

/-- (d) **rdMC Lemma 1, general rate.** For any probability measure `μ`, `0 < a` and `0 < s`,
the density `ouDensityRate μ a s` of `μ.bind (ouKernel a s)` (OU with rate `a`) satisfies
`(log p_s)'(y) = (e^{-as} E[X₀ | Xₛ = y] - y) / (1 - e^{-2as})`, with the Bayes posterior mean
`E[X₀ | Xₛ = y] = affinePosteriorMean μ (e^{-as}) (√(1 - e^{-2as})) y`. -/
theorem score1_ouDensityRate (μ : Measure ℝ) [IsProbabilityMeasure μ] {a s : ℝ}
    (ha : 0 < a) (hs : 0 < s) (y : ℝ) :
    score1 (ouDensityRate μ a s) y =
      (Real.exp (-a * s) * affinePosteriorMean μ (Real.exp (-a * s))
          (Real.sqrt (1 - Real.exp (-2 * a * s))) y - y) / (1 - Real.exp (-2 * a * s)) := by
  have h := one_sub_exp_pos ha hs
  rw [ouDensityRate, score1_affineDensity μ _ (Real.sqrt_ne_zero'.mpr h), Real.sq_sqrt h.le]

/-- (d) **rdMC Lemma 1, noise form.** For any probability measure `μ` and `0 < s`,
`(log p_s)'(y) = -E[Z | Xₛ = y] / √(1 - e^{-2s})`, with the Bayes posterior noise mean
`E[Z | Xₛ = y] = affinePosteriorNoiseMean μ (e^{-s}) (√(1 - e^{-2s})) y`. -/
theorem ouPosteriorScore_noise (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (y : ℝ) :
    score1 (ouDensity μ s) y =
      -affinePosteriorNoiseMean μ (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) y /
        Real.sqrt (1 - Real.exp (-2 * s)) :=
  score1_affineDensity_noise μ _ (sqrt_one_sub_exp_ne_zero hs) y

/-! ### The paper's ratio form with unnormalised posterior weights -/

/-- Ratio of kernel integrals equals the ratio of integrals of the unnormalised weight
`w(x) = exp(-(y - a x)² / (2σ²))`: the normalising constant `(2πσ²)^{-1/2}` cancels. Holds for
every measure `μ`, every `F`, and `σ ≠ 0`. -/
private lemma ratio_gaussKernel_eq (μ : Measure ℝ) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ)
    (F : ℝ → ℝ) :
    (∫ x, F x * gaussKernel σ (a * x) y ∂μ) / ∫ x, gaussKernel σ (a * x) y ∂μ =
      (∫ x, F x * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) ∂μ) /
        ∫ x, Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) ∂μ := by
  have hc : (√(2 * π * σ ^ 2))⁻¹ ≠ 0 := by
    have : 0 < 2 * π * σ ^ 2 := by positivity
    positivity
  simp_rw [gaussKernel_eq, mul_left_comm (F _)]
  rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hc]

/-- **Bayes ratio with unnormalised weights.** For every measure `μ`, any `a`, `σ ≠ 0` and `y`,
`affinePosteriorMean μ a σ y = (∫ x w(x) dμ) / (∫ w dμ)` with the unnormalised Gaussian
likelihood `w(x) = exp(-(y - a x)² / (2σ²))`; this is the mean of the posterior
`q(x | y) ∝ w(x) μ(dx)` as written in rdMC Eq. (4). -/
theorem affinePosteriorMean_eq_ratio (μ : Measure ℝ) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    affinePosteriorMean μ a σ y =
      (∫ x, x * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) ∂μ) /
        ∫ x, Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) ∂μ :=
  ratio_gaussKernel_eq μ a hσ y id

/-- For a finite measure `μ` and all `a, σ, y`, `x ↦ gaussKernel σ (a x) y` is `μ`-integrable
(it is bounded and continuous). -/
theorem integrable_gaussKernel_affine (μ : Measure ℝ) [IsFiniteMeasure μ] (a σ y : ℝ) :
    Integrable (fun x => gaussKernel σ (a * x) y) μ := by
  refine Integrable.of_bound
    ((continuous_gaussKernel_left σ y).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
    (√(2 * π * σ ^ 2))⁻¹ (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (gaussKernel_nonneg _ _ _)]
  exact gaussKernel_le σ (a * x) y

/-- For a finite measure `μ`, `a ≠ 0` and `σ ≠ 0`, `x ↦ x * gaussKernel σ (a x) y` is
`μ`-integrable (no moment assumption: the Gaussian factor decays in `x` because `a ≠ 0`). -/
theorem integrable_mul_gaussKernel_affine (μ : Measure ℝ) [IsFiniteMeasure μ] {a σ : ℝ}
    (ha : a ≠ 0) (hσ : σ ≠ 0) (y : ℝ) :
    Integrable (fun x => x * gaussKernel σ (a * x) y) μ := by
  have h := integrable_mul_gaussKernel (μ.map (fun x => a * x)) hσ y
  rw [integrable_map_measure (g := fun x => x * gaussKernel σ x y)
    (continuous_id.mul (continuous_gaussKernel_left σ y)).aestronglyMeasurable
    (measurable_const_mul a).aemeasurable] at h
  refine (h.const_mul a⁻¹).congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply]
  field_simp

/-- **rdMC Lemma 1, ratio form (Eq. (4) for a general prior).** For any probability measure
`μ` (law of `X₀`), `s > 0` and `y`, with `a_s = e^{-s}`, `σ_s² = 1 - e^{-2s}` and the
unnormalised posterior weight `w(x₀) = exp(-(y - a_s x₀)² / (2σ_s²))`,
`(log p_s)'(y) = (∫ ((a_s x₀ - y)/σ_s²) w(x₀) dμ(x₀)) / (∫ w dμ)`,
i.e. `∇ ln p_s(y) = E_{x₀ ∼ q_s(· | y)}[(e^{-s} x₀ - y)/(1 - e^{-2s})]` with
`q_s(dx₀ | y) ∝ w(x₀) μ(dx₀)`. -/
theorem ouPosteriorScore_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (y : ℝ) :
    score1 (ouDensity μ s) y =
      (∫ x₀, ((Real.exp (-s) * x₀ - y) / (1 - Real.exp (-2 * s))) *
          Real.exp (-(y - Real.exp (-s) * x₀) ^ 2 / (2 * (1 - Real.exp (-2 * s)))) ∂μ) /
        ∫ x₀, Real.exp (-(y - Real.exp (-s) * x₀) ^ 2 / (2 * (1 - Real.exp (-2 * s)))) ∂μ := by
  set a := Real.exp (-s) with ha_def
  set σ := Real.sqrt (1 - Real.exp (-2 * s)) with hσ_def
  have hσ : σ ≠ 0 := sqrt_one_sub_exp_ne_zero hs
  have h1 := one_sub_exp_pos one_pos hs
  rw [mul_one] at h1
  have hσ2 : σ ^ 2 = 1 - Real.exp (-2 * s) := Real.sq_sqrt h1.le
  have ha : a ≠ 0 := (Real.exp_pos _).ne'
  rw [← hσ2, ← ratio_gaussKernel_eq μ a hσ y, ouPosteriorScore μ hs y, ← ha_def, ← hσ_def, hσ2]
  have hp := affineDensity_pos μ a hσ y
  have hnum : ∫ x, ((a * x - y) / (1 - Real.exp (-2 * s))) * gaussKernel σ (a * x) y ∂μ =
      (a * ∫ x, x * gaussKernel σ (a * x) y ∂μ - y * affineDensity μ a σ y) /
        (1 - Real.exp (-2 * s)) := by
    unfold affineDensity
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
      ((integrable_mul_gaussKernel_affine μ ha hσ y).const_mul a)
      ((integrable_gaussKernel_affine μ a σ y).const_mul y), ← integral_div]
    congr 1
    ext x
    ring
  rw [hnum, affinePosteriorMean]
  change _ = _ / affineDensity μ a σ y
  field_simp

/-- **rdMC Lemma 1, density form (the paper's Eq. (4)).** Let the law of `X₀` have a Lebesgue
probability density `p₀` (`p₀` measurable, nonnegative, `∫⁻ ofReal ∘ p₀ = 1`; rdMC writes
`p₀ = p_* ∝ e^{-f_*}`). For `s > 0` and every `y`, with `a_s = e^{-s}` and
`σ_s² = 1 - e^{-2s}`,
`(log p_s)'(y) = (∫ ((a_s x₀ - y)/σ_s²) p₀(x₀) w(x₀) dx₀) / (∫ p₀(x₀) w(x₀) dx₀)`,
`w(x₀) = exp(-(y - a_s x₀)² / (2σ_s²))`, i.e.
`∇ ln p_s(y) = E_{x₀ ∼ q_s(· | y)}[(e^{-s} x₀ - y)/(1 - e^{-2s})]` with
`q_s(x₀ | y) ∝ p₀(x₀) exp(-(y - e^{-s} x₀)² / (2(1 - e^{-2s})))`. (rdMC states this for
`∇ ln p_{T-t}`; set `s = T - t`. The statement here uses the forward-time factor
`e^{-s} x₀`.) -/
theorem ouPosteriorScore_density {p₀ : ℝ → ℝ} (hp₀ : Measurable p₀) (hp₀_nonneg : ∀ x, 0 ≤ p₀ x)
    (hp₀_one : ∫⁻ x, ENNReal.ofReal (p₀ x) = 1) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    score1 (ouDensity (volume.withDensity fun x => ENNReal.ofReal (p₀ x)) s) y =
      (∫ x₀, ((Real.exp (-s) * x₀ - y) / (1 - Real.exp (-2 * s))) *
          (p₀ x₀ * Real.exp (-(y - Real.exp (-s) * x₀) ^ 2 / (2 * (1 - Real.exp (-2 * s)))))) /
        ∫ x₀, p₀ x₀ *
          Real.exp (-(y - Real.exp (-s) * x₀) ^ 2 / (2 * (1 - Real.exp (-2 * s)))) := by
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p₀ x)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hp₀_one⟩
  have hw : ∀ g : ℝ → ℝ, ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (p₀ x)) =
      ∫ x, p₀ x * g x := fun g => by
    rw [integral_withDensity_eq_integral_toReal_smul hp₀.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hp₀_nonneg x)]
  rw [ouPosteriorScore_ratio _ hs y, hw, hw]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring

/- Nonvacuity of `ouPosteriorScore_density`: its hypotheses hold for the standard Gaussian density
`p₀ = gaussianPDFReal 0 1` (instance at `s = 1`, `y = 0`). -/
example := ouPosteriorScore_density (p₀ := gaussianPDFReal 0 1) (measurable_gaussianPDFReal 0 1)
  (gaussianPDFReal_nonneg 0 1) (lintegral_gaussianPDFReal_eq_one 0 one_ne_zero) one_pos 0

/-! ### (e) Conditional-expectation reading -/

/-- If `μ` has a finite first moment, so does its image under `x ↦ a x`. -/
private lemma integrable_id_map_mul (μ : Measure ℝ) (hμ : Integrable id μ) (a : ℝ) :
    Integrable id (μ.map (fun x => a * x)) :=
  (integrable_map_measure aestronglyMeasurable_id (measurable_const_mul a).aemeasurable).mpr
    (hμ.const_mul a)

/-- (e) **Posterior-mean characterisation, density form.** Let `μ` be a probability measure
with finite first moment (`Integrable id μ`), `a ≠ 0`, `σ ≠ 0`, and `g : ℝ → ℝ` measurable
with `|g| ≤ M`. Then
`∫ (∫ g(y) x gaussKernel σ (a x) y dy) dμ(x) = ∫ g(y) m(y) p(y) dy` with
`m = affinePosteriorMean μ a σ` and `p = affineDensity μ a σ`, i.e. `E[g(Y) X] = E[g(Y) m(Y)]`
for `Y = a X + σ Z`. Hence `m(Y)` is a version of `E[X | Y]` (determined only up to
`Law(Y)`-null sets). Derived from Tweedie's
`integral_integral_mul_gaussKernel_eq_posteriorMean` for `μ.map (a * ·)`. -/
theorem integral_integral_mul_gaussKernel_affine_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) {g : ℝ → ℝ}
    (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ x, (∫ y, g y * x * gaussKernel σ (a * x) y) ∂μ =
      ∫ y, g y * affinePosteriorMean μ a σ y * affineDensity μ a σ y := by
  have := isProbabilityMeasure_map_mul μ a
  have h := integral_integral_mul_gaussKernel_eq_posteriorMean _
    (integrable_id_map_mul μ hμ a) hσ hg M hM
  have hmeas : StronglyMeasurable (fun x => ∫ y, g y * x * gaussKernel σ x y) :=
    StronglyMeasurable.integral_prod_right (f := fun x y => g y * x * gaussKernel σ x y)
      (((hg.comp measurable_snd).mul measurable_fst).mul
        (continuous_gaussKernel_uncurry σ).measurable).stronglyMeasurable
  rw [integral_map (measurable_const_mul a).aemeasurable hmeas.aestronglyMeasurable,
    ← affineDensity_eq_smoothedDensity] at h
  simp_rw [← mul_affinePosteriorMean] at h
  have hl : ∀ x, ∫ y, g y * (a * x) * gaussKernel σ (a * x) y =
      a * ∫ y, g y * x * gaussKernel σ (a * x) y := fun x => by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  have hr : ∀ y, g y * (a * affinePosteriorMean μ a σ y) * affineDensity μ a σ y =
      a * (g y * affinePosteriorMean μ a σ y * affineDensity μ a σ y) := fun y => by ring
  simp_rw [hl, hr, integral_const_mul] at h
  exact mul_left_cancel₀ ha h

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Z : Ω → ℝ}

/-- (e) **Affine posterior mean = conditional expectation.** For measurable, `P`-independent
`X ∼ μ` with `Integrable id μ` and `Z ∼ N(0, 1)` on a probability space, `a ≠ 0`, `σ ≠ 0`
and `Y = a X + σ Z`: `E[X | σ(Y)] = affinePosteriorMean μ a σ ∘ Y` `P`-almost surely, i.e. the
explicit Bayes ratio is *a version* of `E[X | Y]` (conditional expectations are defined only up
to null sets; no regular conditional distribution is chosen). Derived from Tweedie's
`condExp_eq_posteriorMean` applied to `a X` and `condExp_smul`. -/
theorem condExp_eq_affinePosteriorMean [IsProbabilityMeasure P] (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hXlaw : P.map X = μ) (hZlaw : P.map Z = gaussianReal 0 1) (hμ : Integrable id μ)
    {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) :
    P[X | MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance] =ᵐ[P]
      fun ω => affinePosteriorMean μ a σ (a * X ω + σ * Z ω) := by
  have := isProbabilityMeasure_map_mul μ a
  have hX' : Measurable fun ω => a * X ω := hX.const_mul a
  have hXZ' : IndepFun (fun ω => a * X ω) Z P := hXZ.comp (measurable_const_mul a) measurable_id
  have hlaw : P.map (fun ω => a * X ω) = μ.map (fun x => a * x) := by
    rw [← hXlaw, Measure.map_map (measurable_const_mul a) hX]
    rfl
  have h : P[a • X | MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance] =ᵐ[P]
      fun ω => posteriorMean (μ.map (fun x => a * x)) σ (a * X ω + σ * Z ω) :=
    condExp_eq_posteriorMean hX' hZ hXZ' hlaw hZlaw (integrable_id_map_mul μ hμ a) hσ
  have hsmul := condExp_smul (μ := P) a X
    (MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance)
  filter_upwards [h, hsmul] with ω h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul, ← mul_affinePosteriorMean] at h1
  exact mul_left_cancel₀ ha h1

/-- (c) **OU marginal, random-variable form.** For measurable, `P`-independent `X₀ ∼ μ` and
`Z ∼ N(0, 1)` on a probability space and `s > 0`, the OU state
`Xₛ = e^{-s} X₀ + √(1 - e^{-2s}) Z` has Lebesgue density `ouDensity μ s`. -/
theorem map_ouState_eq_withDensity [IsProbabilityMeasure P] (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z P) {μ : Measure ℝ} (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) {s : ℝ} (hs : 0 < s) :
    P.map (fun ω => Real.exp (-s) * X ω + Real.sqrt (1 - Real.exp (-2 * s)) * Z ω) =
      volume.withDensity (fun y => ENNReal.ofReal (ouDensity μ s y)) :=
  map_affine_add_mul_eq_withDensity hX hZ hXZ hXlaw hZlaw _ (sqrt_one_sub_exp_ne_zero hs)

/-- (d)+(e) **rdMC Lemma 1 with conditional expectations.** For measurable, `P`-independent
`X₀ ∼ μ` with `Integrable id μ` and `Z ∼ N(0, 1)` on a probability space, `s > 0` and the OU
state `Xₛ = e^{-s} X₀ + √(1 - e^{-2s}) Z` (hypothesis `hXs`), almost surely
`(log p_s)'(Xₛ) = (e^{-s} E[X₀ | σ(Xₛ)] - Xₛ) / (1 - e^{-2s})`,
where `p_s = ouDensity μ s` is the density of `Xₛ` (`map_ouState_eq_withDensity`). The moment
assumption is needed only for `E[X₀ | σ(Xₛ)]` to be defined; the identity holds up to null
sets. -/
theorem ouPosteriorScore_condExp [IsProbabilityMeasure P] (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) {μ : Measure ℝ} [IsProbabilityMeasure μ] (hXlaw : P.map X = μ)
    (hZlaw : P.map Z = gaussianReal 0 1) (hμ : Integrable id μ) {s : ℝ} (hs : 0 < s)
    {Xs : Ω → ℝ}
    (hXs : Xs = fun ω => Real.exp (-s) * X ω + Real.sqrt (1 - Real.exp (-2 * s)) * Z ω) :
    ∀ᵐ ω ∂P, score1 (ouDensity μ s) (Xs ω) =
      (Real.exp (-s) * (P[X | MeasurableSpace.comap Xs inferInstance]) ω - Xs ω) /
        (1 - Real.exp (-2 * s)) := by
  subst hXs
  filter_upwards [condExp_eq_affinePosteriorMean hX hZ hXZ hXlaw hZlaw hμ
    (Real.exp_pos (-s)).ne' (sqrt_one_sub_exp_ne_zero hs)] with ω hω
  rw [hω, ouPosteriorScore μ hs]

end RandomVariables

/-! ### The posterior law `q(· | y)` -/

/-- The density `x ↦ ofReal (gaussKernel σ (a x) y / affineDensity μ a σ y)` of the posterior
with respect to the prior is measurable (for every measure `μ` and all `a, σ, y`). -/
theorem measurable_affinePosteriorDensity (μ : Measure ℝ) (a σ y : ℝ) :
    Measurable fun x => ENNReal.ofReal (gaussKernel σ (a * x) y / affineDensity μ a σ y) :=
  (((continuous_gaussKernel_left σ y).comp (continuous_const.mul continuous_id)).div_const
    _).measurable.ennreal_ofReal

/-- Integrals against the posterior law: for every measure `μ`, all `a, σ, y` and every
`g : ℝ → ℝ` (Bochner convention on both sides),
`∫ g d(affinePosterior μ a σ y) = (∫ g(x) gaussKernel σ (a x) y dμ(x)) / affineDensity μ a σ y`. -/
theorem integral_affinePosterior (μ : Measure ℝ) (a σ y : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂(affinePosterior μ a σ y) =
      (∫ x, g x * gaussKernel σ (a * x) y ∂μ) / affineDensity μ a σ y := by
  rw [affinePosterior, integral_withDensity_eq_integral_toReal_smul
    (measurable_affinePosteriorDensity μ a σ y) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (gaussKernel_nonneg _ _ _)
    (affineDensity_nonneg μ a σ y))]
  ring

/-- The mean of the posterior law is the Bayes posterior mean: for every measure `μ` and all
`a, σ, y`, `∫ x d(affinePosterior μ a σ y)(x) = affinePosteriorMean μ a σ y`. -/
theorem integral_id_affinePosterior (μ : Measure ℝ) (a σ y : ℝ) :
    ∫ x, x ∂(affinePosterior μ a σ y) = affinePosteriorMean μ a σ y :=
  integral_affinePosterior μ a σ y id

/-- For a probability measure `μ`, any `a`, `σ ≠ 0` and `y`, the posterior
`affinePosterior μ a σ y` is a probability measure (its normaliser is
`affineDensity μ a σ y > 0`). -/
theorem isProbabilityMeasure_affinePosterior (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) : IsProbabilityMeasure (affinePosterior μ a σ y) := by
  have hp : ∫ x, gaussKernel σ (a * x) y ∂μ = affineDensity μ a σ y := rfl
  constructor
  rw [affinePosterior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_gaussKernel_affine μ a σ y).div_const _)
      (ae_of_all _ fun x => div_nonneg (gaussKernel_nonneg _ _ _)
        (affineDensity_nonneg μ a σ y)),
    integral_div, hp, div_self (affineDensity_pos μ a hσ y).ne', ENNReal.ofReal_one]

/-- Elementary bound: for `c > 0` and all real `u`, `u² exp(-u² / c) ≤ c`. -/
private lemma sq_mul_exp_neg_sq_div_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    u ^ 2 * Real.exp (-u ^ 2 / c) ≤ c := by
  have hexp : u ^ 2 / c + 1 ≤ Real.exp (u ^ 2 / c) := Real.add_one_le_exp _
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc u ^ 2 ≤ u ^ 2 + c := by linarith
    _ = c * (u ^ 2 / c + 1) := by field_simp
    _ ≤ c * Real.exp (u ^ 2 / c) := mul_le_mul_of_nonneg_left hexp hc.le

/-- Second-moment bound for the affine kernel: for `a ≠ 0`, `σ ≠ 0` and all `x, y`,
`x² gaussKernel σ (a x) y ≤ (2y² + 4σ²)/a² · (√(2πσ²))⁻¹`. -/
theorem sq_mul_gaussKernel_affine_le {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) (x y : ℝ) :
    x ^ 2 * gaussKernel σ (a * x) y ≤
      (2 * y ^ 2 + 4 * σ ^ 2) / a ^ 2 * (√(2 * π * σ ^ 2))⁻¹ := by
  rw [gaussKernel_eq]
  have hc : 0 ≤ (√(2 * π * σ ^ 2))⁻¹ := by positivity
  have hE0 : 0 ≤ Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (y - a * x)]
    · positivity
  have hu := sq_mul_exp_neg_sq_div_le (c := 2 * σ ^ 2) (by positivity) (y - a * x)
  have hax : (a * x) ^ 2 ≤ 2 * y ^ 2 + 2 * (y - a * x) ^ 2 := by
    nlinarith [sq_nonneg (y + (y - a * x))]
  have ha2 : 0 < a ^ 2 := by positivity
  have key : x ^ 2 * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) ≤
      (2 * y ^ 2 + 4 * σ ^ 2) / a ^ 2 := by
    rw [le_div_iff₀ ha2]
    calc x ^ 2 * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) * a ^ 2
        = (a * x) ^ 2 * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) := by ring
      _ ≤ (2 * y ^ 2 + 2 * (y - a * x) ^ 2) * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) :=
          mul_le_mul_of_nonneg_right hax hE0
      _ = 2 * y ^ 2 * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)) +
            2 * ((y - a * x) ^ 2 * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2))) := by ring
      _ ≤ 2 * y ^ 2 * 1 + 2 * (2 * σ ^ 2) := by
          gcongr
      _ = 2 * y ^ 2 + 4 * σ ^ 2 := by ring
  calc x ^ 2 * ((√(2 * π * σ ^ 2))⁻¹ * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2)))
      = (√(2 * π * σ ^ 2))⁻¹ * (x ^ 2 * Real.exp (-(y - a * x) ^ 2 / (2 * σ ^ 2))) := by ring
    _ ≤ (√(2 * π * σ ^ 2))⁻¹ * ((2 * y ^ 2 + 4 * σ ^ 2) / a ^ 2) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

/-- **The posterior has a finite second moment.** For a finite measure `μ` (no moment
assumption), `a ≠ 0`, `σ ≠ 0` and every `y`, `MemLp id 2 (affinePosterior μ a σ y)`: the
Gaussian likelihood `exp(-(y - a x)²/(2σ²))` makes `x² q(x | y)` bounded. In particular exact
posterior draws in a Monte Carlo score oracle always have finite variance
(`ScoreEstimation/MonteCarlo.lean`). -/
theorem memLp_id_affinePosterior (μ : Measure ℝ) [IsFiniteMeasure μ] {a σ : ℝ} (ha : a ≠ 0)
    (hσ : σ ≠ 0) (y : ℝ) : MemLp id 2 (affinePosterior μ a σ y) := by
  rw [memLp_two_iff_integrable_sq aestronglyMeasurable_id, affinePosterior,
    integrable_withDensity_iff_integrable_smul' (measurable_affinePosteriorDensity μ a σ y)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hK : ∀ x, 0 ≤ gaussKernel σ (a * x) y / affineDensity μ a σ y := fun x =>
    div_nonneg (gaussKernel_nonneg _ _ _) (affineDensity_nonneg μ a σ y)
  refine Integrable.of_bound
    ((measurable_affinePosteriorDensity μ a σ y).ennreal_toReal.smul
      (measurable_id.pow_const 2)).aestronglyMeasurable
    ((2 * y ^ 2 + 4 * σ ^ 2) / a ^ 2 * (√(2 * π * σ ^ 2))⁻¹ / affineDensity μ a σ y)
    (ae_of_all _ fun x => ?_)
  simp only [id, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hK x), Real.norm_of_nonneg (mul_nonneg (hK x) (sq_nonneg x)),
    div_mul_eq_mul_div, mul_comm]
  exact div_le_div_of_nonneg_right (sq_mul_gaussKernel_affine_le ha hσ x y)
    (affineDensity_nonneg μ a σ y)

/-! ### `d`-dimensional isotropic version on `Fin d → ℝ` -/

section Isotropic

variable {d : ℕ}

/-- The density of `Y = a X + σ Z` on `Fin d → ℝ` with `X ∼ μ`, `Z ∼ N(0, I_d)` independent:
`piAffineDensity μ a σ y = ∫ piGaussKernel σ (a • x) y dμ(x)`, where `piGaussKernel σ m` is the
density of `N(m, σ² I_d)`. -/
noncomputable def piAffineDensity (μ : Measure (Fin d → ℝ)) (a σ : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ x, piGaussKernel σ (a • x) y ∂μ

/-- The explicit Bayes posterior mean of `X` given `a X + σ Z = y` on `Fin d → ℝ`,
coordinatewise `(∫ xᵢ piGaussKernel σ (a • x) y dμ(x)) / piAffineDensity μ a σ y`, defined for
every `y`. -/
noncomputable def piAffinePosteriorMean (μ : Measure (Fin d → ℝ)) (a σ : ℝ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => (∫ x, x i * piGaussKernel σ (a • x) y ∂μ) / piAffineDensity μ a σ y

/-- The density of rdMC's `d`-dimensional OU marginal `Xₛ = e^{-s} X₀ + √(1 - e^{-2s}) Z`,
`X₀ ∼ μ`, `Z ∼ N(0, I_d)` (`map_conv_pi_ouVar_eq_withDensity`, for `s > 0`). -/
noncomputable def piOUDensity (μ : Measure (Fin d → ℝ)) (s : ℝ) : (Fin d → ℝ) → ℝ :=
  piAffineDensity μ (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))

/-- Change of variables on `Fin d → ℝ`: for every measure `μ` and all `a, σ`,
`piAffineDensity μ a σ = piSmoothedDensity (μ.map (a • ·)) σ`. -/
theorem piAffineDensity_eq_piSmoothedDensity (μ : Measure (Fin d → ℝ)) (a σ : ℝ) :
    piAffineDensity μ a σ = piSmoothedDensity (μ.map (fun x => a • x)) σ := by
  funext y
  unfold piAffineDensity piSmoothedDensity
  rw [integral_map (measurable_const_smul a).aemeasurable
    (continuous_piGaussKernel_left σ y).aestronglyMeasurable]

/-- For every measure `μ` on `Fin d → ℝ`, all `a, σ, y` and every coordinate `i`:
`a * piAffinePosteriorMean μ a σ y i = piPosteriorMean (μ.map (a • ·)) σ y i`. -/
theorem mul_piAffinePosteriorMean (μ : Measure (Fin d → ℝ)) (a σ : ℝ) (y : Fin d → ℝ)
    (i : Fin d) :
    a * piAffinePosteriorMean μ a σ y i = piPosteriorMean (μ.map (fun x => a • x)) σ y i := by
  rw [piPosteriorMean, integral_map (f := fun x => x i * piGaussKernel σ x y)
    (measurable_const_smul a).aemeasurable
    ((continuous_apply i).mul (continuous_piGaussKernel_left σ y)).aestronglyMeasurable,
    ← piAffineDensity_eq_piSmoothedDensity, piAffinePosteriorMean, ← mul_div_assoc,
    ← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **Affine Tweedie formula on `Fin d → ℝ`.** For an arbitrary probability measure `μ` on
`Fin d → ℝ` (no moment assumption), any `a`, `σ ≠ 0` and every `y`, the state score of the
density of `a X + σ Z` (`Z ∼ N(0, I_d)`) is
`∇ log p(y) = (a * piAffinePosteriorMean μ a σ y - y) / σ²` (coordinatewise). Derived from
`Tweedie.tweedie_pi` for `μ.map (a • ·)`. -/
theorem score_piAffineDensity (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (a : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) (y : Fin d → ℝ) :
    score (piAffineDensity μ a σ) y =
      fun i => (a * piAffinePosteriorMean μ a σ y i - y i) / σ ^ 2 := by
  have : IsProbabilityMeasure (μ.map (fun x : Fin d → ℝ => a • x)) :=
    inferInstance
  rw [piAffineDensity_eq_piSmoothedDensity, tweedie_pi _ hσ]
  funext i
  rw [mul_piAffinePosteriorMean]

/-- **Law identification on `Fin d → ℝ`.** For any finite measure `μ`, any `a` and `σ ≠ 0`,
`(μ.map (a • ·)) ∗ N(0, σ² I_d) = volume.withDensity (ofReal ∘ piAffineDensity μ a σ)`, with
`N(0, σ² I_d) = ⊗ᵢ N(0, σ²)`. -/
theorem map_conv_pi_gaussianReal_eq_withDensity (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    (μ.map (fun x => a • x)) ∗
        Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
      volume.withDensity (fun y => ENNReal.ofReal (piAffineDensity μ a σ y)) := by
  rw [piAffineDensity_eq_piSmoothedDensity]
  exact conv_pi_gaussianReal_eq_withDensity _ hσ

/-- **`d`-dimensional OU marginal.** For a finite measure `μ` on `Fin d → ℝ` and `s > 0`, the
law of `Xₛ = e^{-s} X₀ + σₛ Z` (`X₀ ∼ μ`, `Z ∼ N(0, I_d)`, `σₛ² = ouVar 1 s = 1 - e^{-2s}`, i.e.
`ouKernel 1 s` in every coordinate) has Lebesgue density `piOUDensity μ s`:
`(μ.map (e^{-s} • ·)) ∗ ⊗ᵢ N(0, ouVar 1 s) = volume.withDensity (ofReal ∘ piOUDensity μ s)`. -/
theorem map_conv_pi_ouVar_eq_withDensity (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] {s : ℝ}
    (hs : 0 < s) :
    (μ.map (fun x => Real.exp (-s) • x)) ∗
        Measure.pi (fun _ : Fin d => gaussianReal 0 (ouVar 1 s)) =
      volume.withDensity (fun y => ENNReal.ofReal (piOUDensity μ s y)) := by
  have hv : ouVar 1 s = ⟨Real.sqrt (1 - Real.exp (-2 * s)) ^ 2, sq_nonneg _⟩ := by
    rw [ouVar_eq_sq_sqrt one_pos hs, mul_one]
  rw [hv]
  exact map_conv_pi_gaussianReal_eq_withDensity μ _ (sqrt_one_sub_exp_ne_zero hs)

/-- **rdMC Lemma 1 on `Fin d → ℝ` (SE-3, the paper's dimension).** For any probability
measure `μ` on `Fin d → ℝ` (law of `X₀`; no density, no moment assumption), `s > 0` and every
`y`, the state score of the density `p_s = piOUDensity μ s` of `Xₛ` satisfies
`∇ ln p_s(y) = (1 - e^{-2s})⁻¹ • (e^{-s} • E[X₀ | Xₛ = y] - y)`, with the Bayes posterior mean
`E[X₀ | Xₛ = y] = piAffinePosteriorMean μ (e^{-s}) (√(1 - e^{-2s})) y`. rdMC writes it for
`∇ ln p_{T-t}`; set `s = T - t`. -/
theorem ouPosteriorScore_pi (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {s : ℝ}
    (hs : 0 < s) (y : Fin d → ℝ) :
    score (piOUDensity μ s) y =
      (1 - Real.exp (-2 * s))⁻¹ • (Real.exp (-s) • piAffinePosteriorMean μ (Real.exp (-s))
        (Real.sqrt (1 - Real.exp (-2 * s))) y - y) := by
  have h := one_sub_exp_pos one_pos hs
  rw [mul_one] at h
  rw [piOUDensity, score_piAffineDensity μ _ (sqrt_one_sub_exp_ne_zero hs), Real.sq_sqrt h.le]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- **Posterior-mean characterisation on `Fin d → ℝ`, density form.** Let `μ` be a probability
measure on `Fin d → ℝ`, `a ≠ 0`, `σ ≠ 0`, `i` a coordinate with `x ↦ xᵢ` integrable, and
`g` measurable with `|g| ≤ M`. Then
`∫ (∫ g(y) xᵢ piGaussKernel σ (a • x) y dy) dμ(x) = ∫ g(y) m(y)ᵢ p(y) dy` with
`m = piAffinePosteriorMean μ a σ`, `p = piAffineDensity μ a σ`, i.e. `E[g(Y) Xᵢ] = E[g(Y) m(Y)ᵢ]`
for `Y = a X + σ Z`: `m(Y)ᵢ` is a version of `E[Xᵢ | Y]` (up to null sets). Derived from
`Tweedie.integral_integral_apply_mul_piGaussKernel_eq_piPosteriorMean`. -/
theorem integral_integral_apply_mul_piGaussKernel_affine_eq (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) (i : Fin d)
    (hμ : Integrable (fun x => x i) μ) {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) (M : ℝ)
    (hM : ∀ y, |g y| ≤ M) :
    ∫ x, (∫ y, g y * x i * piGaussKernel σ (a • x) y) ∂μ =
      ∫ y, g y * piAffinePosteriorMean μ a σ y i * piAffineDensity μ a σ y := by
  have : IsProbabilityMeasure (μ.map (fun x : Fin d → ℝ => a • x)) :=
    inferInstance
  have hμ' : Integrable (fun x : Fin d → ℝ => x i) (μ.map (fun x => a • x)) := by
    rw [integrable_map_measure (g := fun x : Fin d → ℝ => x i)
      (continuous_apply i).aestronglyMeasurable (measurable_const_smul a).aemeasurable]
    exact (hμ.const_mul a).congr (ae_of_all _ fun x => by simp)
  have h := integral_integral_apply_mul_piGaussKernel_eq_piPosteriorMean _ hσ i hμ' hg M hM
  have hmeas : StronglyMeasurable (fun x : Fin d → ℝ => ∫ y, g y * x i * piGaussKernel σ x y) :=
    StronglyMeasurable.integral_prod_right (f := fun x y => g y * x i * piGaussKernel σ x y)
      (((hg.comp measurable_snd).mul ((measurable_pi_apply i).comp measurable_fst)).mul
        (continuous_piGaussKernel_uncurry σ).measurable).stronglyMeasurable
  rw [integral_map (measurable_const_smul a).aemeasurable hmeas.aestronglyMeasurable,
    ← piAffineDensity_eq_piSmoothedDensity] at h
  simp_rw [← mul_piAffinePosteriorMean, Pi.smul_apply, smul_eq_mul] at h
  have hl : ∀ x : Fin d → ℝ, ∫ y, g y * (a * x i) * piGaussKernel σ (a • x) y =
      a * ∫ y, g y * x i * piGaussKernel σ (a • x) y := fun x => by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  have hr : ∀ y, g y * (a * piAffinePosteriorMean μ a σ y i) * piAffineDensity μ a σ y =
      a * (g y * piAffinePosteriorMean μ a σ y i * piAffineDensity μ a σ y) := fun y => by ring
  simp_rw [hl, hr, integral_const_mul] at h
  exact mul_left_cancel₀ ha h

end Isotropic

end FormalizeSampling.OUPosterior
