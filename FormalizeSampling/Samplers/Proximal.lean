module

public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Kernels.ReverseKernel
public import FormalizeSampling.Foundations.GibbsMeasure

/-!
# The exact proximal sampler on `ℝ`: restricted Gaussian oracle and invariance

Target `π(x) = exp(-f x) / Z` on `ℝ` (Lebesgue measure), with a potential `f : ℝ → ℝ`, and step
size `η > 0`. The exact *proximal sampler* (Lee–Shen–Tian 2021) considered here alternates two
exact Gibbs steps on the augmented law `π(x) N(y; x, η)` (this is the exact parent kernel that
the stochastic proximal sampler SPS approximates; no other variant or constant of a specific
paper is claimed beyond the variance convention `η`):

1. forward step `y ~ N(x, η)` (`forwardKernel η`, Mathlib's `gaussianReal x η.toNNReal`;
   `η` is the **variance**);
2. backward step `x' ~ RGO(y)` (`rgoKernel f η`), the *restricted Gaussian oracle* with density
   `x ↦ exp(-f x - (x - y)² / (2η)) / Z_η(y)`, `Z_η(y) = ∫ exp(-f x - (x - y)² / (2η)) dx`.

## Main results

* The target `target f` (with `target_eq_tilted`: it is Mathlib's `volume.tilted (-f)`) is
  defined in `Foundations/GibbsMeasure.lean`.
* (e) `integrable_rgo`, `rgoNormalizer_pos`, `rgoNormalizer_le`: the RGO normaliser is finite
  (`≤ Z`) and positive for every `y`, assuming only `Integrable (fun x => exp (-f x))`; hence
  `isMarkovKernel_rgoKernel` and `isMarkovKernel_proxKernel`.
* (f) **PX-1** `reverseDensity_eq_rgoDensity`: the Bayes reverse density of
  `FormalizeSampling.ReverseKernel` for the prior `π` and the Gaussian forward density is exactly
  the RGO density, for **every** `(y, x)` (the marginal density is positive and finite
  everywhere, `marginalDensity_eq`). Hence `rgoKernel_ae_eq_posterior`: the RGO kernel is a.e.
  Mathlib's posterior `(forwardKernel η)†(target f)`.
* (g) **PX-1** invariance: `lintegral_proximal_invariance` (pure lintegral form),
  `lintegral_target_proxStep` (`∫ π(x) [∫ N(x, η)(dy) RGO(y, A)] dx = π(A)`), and
  `proxKernel_comp_target` (`proxKernel f η ∘ₘ target f = target f`). The augmented joint law
  `augmentedJoint f η` (density `π(x) N(y; x, η)` w.r.t. Lebesgue on `ℝ × ℝ`) satisfies
  `target_compProd_forwardKernel` (its `y | x` conditional is `N(x, η)`),
  `augmentedJoint_map_swap` (its `x | y` conditional is `RGO(y)`), and the disintegration
  statements `ae_forwardKernel_eq_condKernel` and `ae_rgoKernel_eq_condKernel_swap`.

## Conventions

`gaussianReal m v` and `gaussianPDFReal m v` take the variance `v : ℝ≥0`; we use
`v = η.toNNReal`, which equals `η` for `η > 0`. Densities are converted to `ℝ≥0∞` with
`ENNReal.ofReal`. The hypotheses used are: `Measurable f` (only where measurability of the
prior density is needed), `Integrable (fun x => Real.exp (-f x))` (so `Z ∈ (0, ∞)`), and
`0 < η`.

## Exact parent kernel versus inexact inner sampler

Everything here concerns the **exact** parent kernel: the RGO step is assumed to be sampled exactly.
Practical samplers (SPS-SGLD, SPS-MALA, rejection-sampling RGO implementations) replace the RGO step
by an inexact inner sampler; the resulting approximation error is **not** treated here (see the TV
error certificates of KR-1 in `Kernels/ErrorDecomposition.lean` and the conditional SPS-type bound
in `Samplers/ProximalInexact.lean`).

## Not proved here

* No mixing or convergence rate of the proximal sampler in this file; KL rates are in
  `Samplers/ProximalContraction.lean`, `Samplers/ProximalSharpLSI.lean`,
  `Samplers/ProximalGeneralLSI.lean` (log-Sobolev targets) and
  `Samplers/ProximalLogConcaveRate.lean` (log-concave targets).
* No statement for approximate RGO oracles or stochastic gradients (see
  `Samplers/ProximalInexact.lean` for the inexact-RGO TV bound).
* The `d`-dimensional version is in `Samplers/ProximalPi.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory FormalizeSampling.ReverseKernel
open scoped ENNReal NNReal

namespace FormalizeSampling.Proximal

variable (f : ℝ → ℝ) (η : ℝ)

/-- The RGO normaliser `Z_η(y) = ∫ exp(-f x - (x - y)² / (2η)) dx`. -/
noncomputable def rgoNormalizer (y : ℝ) : ℝ :=
  ∫ x, Real.exp (-f x - (x - y) ^ 2 / (2 * η))

/-- The restricted Gaussian oracle density `x ↦ exp(-f x - (x - y)² / (2η)) / Z_η(y)`. -/
noncomputable def rgoDensity (y x : ℝ) : ℝ :=
  Real.exp (-f x - (x - y) ^ 2 / (2 * η)) / rgoNormalizer f η y

/-- The forward (Gaussian) density `y ↦ N(y; x, η)` as an `ℝ≥0∞`-valued function
(`gaussianPDF x η.toNNReal y = ofReal (gaussianPDFReal x η.toNNReal y)`; variance `η`). -/
noncomputable def forwardDensity (x y : ℝ) : ℝ≥0∞ := gaussianPDF x η.toNNReal y

/-- The forward kernel `x ↦ N(x, η)`, as the density kernel of `forwardDensity η` w.r.t.
Lebesgue measure; it equals `gaussianReal x η.toNNReal` (`forwardKernel_apply`). -/
noncomputable def forwardKernel : Kernel ℝ ℝ := densityKernel volume (forwardDensity η)

/-- The RGO kernel `y ↦ RGO(y)` with density `rgoDensity f η y` w.r.t. Lebesgue measure. -/
noncomputable def rgoKernel : Kernel ℝ ℝ :=
  densityKernel volume (fun y x => ENNReal.ofReal (rgoDensity f η y x))

/-- One step of the exact proximal sampler: `y ~ N(x, η)`, then `x' ~ RGO(y)`. -/
noncomputable def proxKernel : Kernel ℝ ℝ := rgoKernel f η ∘ₖ forwardKernel η

/-- The augmented joint law with density `π(x) N(y; x, η)` w.r.t. Lebesgue measure on `ℝ × ℝ`.
-/
noncomputable def augmentedJoint : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity
    (fun z => ENNReal.ofReal (targetDensity f z.1) * forwardDensity η z.1 z.2)

/-! ### Forward kernel -/

/-- The forward density is jointly measurable in `(x, y)` (no assumptions). -/
theorem measurable_forwardDensity : Measurable (Function.uncurry (forwardDensity η)) := by
  unfold forwardDensity gaussianPDF gaussianPDFReal
  fun_prop

/-- For `η > 0`, the forward density integrates to one: `∫⁻ y, N(y; x, η) dy = 1`. -/
theorem lintegral_forwardDensity {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ∫⁻ y, forwardDensity η x y = 1 :=
  lintegral_gaussianPDF_eq_one x (by simpa using hη)

/-- For `η > 0`, the forward kernel is Mathlib's Gaussian with mean `x` and variance `η`:
`forwardKernel η x = gaussianReal x η.toNNReal`. -/
theorem forwardKernel_apply {η : ℝ} (hη : 0 < η) (x : ℝ) :
    forwardKernel η x = gaussianReal x η.toNNReal := by
  rw [forwardKernel, densityKernel_apply (measurable_forwardDensity η),
    gaussianReal_of_var_ne_zero _ (by simpa using hη)]
  rfl

/-- For `η > 0`, the forward kernel is a Markov kernel. -/
theorem isMarkovKernel_forwardKernel {η : ℝ} (hη : 0 < η) : IsMarkovKernel (forwardKernel η) :=
  isMarkovKernel_densityKernel (measurable_forwardDensity η) (lintegral_forwardDensity hη)

/-- The forward kernel is a finite kernel for every `η` (it is the zero kernel if `η ≤ 0`). -/
theorem isFiniteKernel_forwardKernel : IsFiniteKernel (forwardKernel η) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun x => ?_⟩⟩
  rw [forwardKernel, densityKernel_apply (measurable_forwardDensity η),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  by_cases hη : η.toNNReal = 0
  · simp [forwardDensity, hη]
  · exact (lintegral_gaussianPDF_eq_one x hη).le

/-! ### Target -/

variable {f η}

attribute [local instance] isFiniteMeasure_target

/-! ### (e) The RGO normaliser -/

/-- **(e) Integrability of the RGO integrand.** If `exp ∘ (-f)` is integrable and `η > 0`, then
`x ↦ exp(-f x - (x - y)² / (2η))` is integrable for every `y`. -/
theorem integrable_rgo (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (y : ℝ) :
    Integrable (fun x => Real.exp (-f x - (x - y) ^ 2 / (2 * η))) := by
  have h := hint.bdd_mul (f := fun x => Real.exp (-((x - y) ^ 2 / (2 * η))))
    (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  · refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    positivity

/-- **(e) Positivity of the RGO normaliser.** If `exp ∘ (-f)` is integrable and `η > 0`, then
`0 < Z_η(y)` for every `y`. -/
theorem rgoNormalizer_pos (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : ℝ) : 0 < rgoNormalizer f η y :=
  integral_exp_pos (integrable_rgo hint hη y)

/-- **(e) Finiteness of the RGO normaliser.** If `exp ∘ (-f)` is integrable and `η > 0`, then
`Z_η(y) ≤ Z` for every `y`. -/
theorem rgoNormalizer_le (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : ℝ) : rgoNormalizer f η y ≤ targetNormalizer f := by
  refine integral_mono (integrable_rgo hint hη y) hint fun x => ?_
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ (x - y) ^ 2 / (2 * η) := by positivity
  linarith

/-- **(e) in `ℝ≥0∞`.** If `exp ∘ (-f)` is integrable and `η > 0`, then
`∫⁻ x, ofReal (exp(-f x - (x - y)² / (2η))) = ofReal (Z_η(y))`, which is positive and finite. -/
theorem lintegral_rgo (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (y : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-f x - (x - y) ^ 2 / (2 * η)))
      = ENNReal.ofReal (rgoNormalizer f η y) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_rgo hint hη y)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- The RGO density is nonnegative (no assumptions: the normaliser is an integral of a positive
function, hence nonnegative). -/
theorem rgoDensity_nonneg (y x : ℝ) : 0 ≤ rgoDensity f η y x :=
  div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)

/-- If `exp ∘ (-f)` is integrable and `η > 0`, the RGO density is a probability density:
`∫ x, rgoDensity f η y x = 1`. -/
theorem integral_rgoDensity (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : ℝ) : ∫ x, rgoDensity f η y x = 1 := by
  unfold rgoDensity
  rw [integral_div, ← rgoNormalizer, div_self (rgoNormalizer_pos hint hη y).ne']

/-! ### (f) PX-1: the Bayes posterior is the RGO -/

/-- Prior times forward density, explicitly: for `η > 0`,
`π(x) N(y; x, η) = ofReal((2πη)^{-1/2} / Z) * ofReal(exp(-f x - (x - y)² / (2η)))`. -/
theorem prior_mul_forwardDensity (hη : 0 < η) (x y : ℝ) :
    ENNReal.ofReal (targetDensity f x) * forwardDensity η x y
      = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * η))⁻¹ / targetNormalizer f)
        * ENNReal.ofReal (Real.exp (-f x - (x - y) ^ 2 / (2 * η))) := by
  have hZ := targetNormalizer_nonneg (f := f)
  rw [forwardDensity, gaussianPDF, ← ENNReal.ofReal_mul (targetDensity_nonneg x),
    ← ENNReal.ofReal_mul (by positivity), gaussianPDFReal, Real.coe_toNNReal _ hη.le]
  congr 1
  unfold targetDensity
  have : -f x - (x - y) ^ 2 / (2 * η) = -f x + -(y - x) ^ 2 / (2 * η) := by ring
  rw [this, Real.exp_add]
  ring

/-- **Marginal density of the forward step.** If `exp ∘ (-f)` is integrable and `η > 0`, the
density of `y` under `π(x) N(y; x, η)` is `m(y) = ofReal((2πη)^{-1/2} / Z * Z_η(y))`. -/
theorem marginalDensity_eq (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : ℝ) :
    marginalDensity volume (fun x => ENNReal.ofReal (targetDensity f x)) (forwardDensity η) y
      = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * η))⁻¹ / targetNormalizer f
          * rgoNormalizer f η y) := by
  unfold marginalDensity
  simp_rw [prior_mul_forwardDensity hη]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rgo hint hη,
    ← ENNReal.ofReal_mul (div_nonneg (by positivity) targetNormalizer_nonneg)]

/-- The marginal density is positive and finite at **every** `y` (integrable `exp ∘ (-f)`,
`η > 0`), so the Bayes reverse density has no exceptional set here. -/
theorem marginalDensity_pos_ne_top (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : ℝ) :
    marginalDensity volume (fun x => ENNReal.ofReal (targetDensity f x)) (forwardDensity η) y
        ≠ 0 ∧
      marginalDensity volume (fun x => ENNReal.ofReal (targetDensity f x)) (forwardDensity η) y
        ≠ ⊤ := by
  rw [marginalDensity_eq hint hη]
  refine ⟨?_, ENNReal.ofReal_ne_top⟩
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have := targetNormalizer_pos hint
  have := rgoNormalizer_pos hint hη y
  positivity

/-- **PX-1: RGO formula.** If `exp ∘ (-f)` is integrable and `η > 0`, the Bayes reverse
density of `FormalizeSampling.ReverseKernel` for the prior `π = exp(-f)/Z` and the forward
kernel `N(x, η)` is the restricted Gaussian oracle density at every point:
`reverseDensity volume π N y x = ofReal (exp(-f x - (x - y)² / (2η)) / Z_η(y))`. -/
theorem reverseDensity_eq_rgoDensity (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) (y x : ℝ) :
    reverseDensity volume (fun x => ENNReal.ofReal (targetDensity f x)) (forwardDensity η) y x
      = ENNReal.ofReal (rgoDensity f η y x) := by
  have hc : 0 < (Real.sqrt (2 * Real.pi * η))⁻¹ / targetNormalizer f := by
    have := targetNormalizer_pos hint
    positivity
  unfold reverseDensity
  rw [prior_mul_forwardDensity hη, marginalDensity_eq hint hη, ENNReal.ofReal_mul hc.le,
    ENNReal.mul_div_mul_left _ _ (by simpa using hc) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_div_of_pos (rgoNormalizer_pos hint hη y)]
  rfl

/-- The RGO density function equals the Bayes reverse density as a function of `(y, x)`
(integrable `exp ∘ (-f)`, `η > 0`). -/
theorem rgoDensity_eq_reverseDensity (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) :
    (fun y x => ENNReal.ofReal (rgoDensity f η y x))
      = reverseDensity volume (fun x => ENNReal.ofReal (targetDensity f x)) (forwardDensity η) :=
  funext fun y => funext fun x => (reverseDensity_eq_rgoDensity hint hη y x).symm

/-- The RGO kernel is the density-form reverse kernel of the forward step
(integrable `exp ∘ (-f)`, `η > 0`). -/
theorem rgoKernel_eq_densityKernel (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) :
    rgoKernel f η = densityKernel volume
      (reverseDensity volume (fun x => ENNReal.ofReal (targetDensity f x))
        (forwardDensity η)) := by
  rw [rgoKernel, rgoDensity_eq_reverseDensity hint hη]

/-- The RGO density is jointly measurable in `(y, x)` (measurable `f`, integrable `exp ∘ (-f)`,
`η > 0`). -/
theorem measurable_rgoDensity (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) :
    Measurable (Function.uncurry fun y x => ENNReal.ofReal (rgoDensity f η y x)) := by
  rw [rgoDensity_eq_reverseDensity hint hη]
  exact measurable_reverseDensity (measurable_targetDensity hf).ennreal_ofReal
    (measurable_forwardDensity η)

/-- The RGO kernel at `y` is `volume.withDensity (ofReal ∘ rgoDensity f η y)` (measurable `f`,
integrable `exp ∘ (-f)`, `η > 0`). -/
theorem rgoKernel_apply (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) (y : ℝ) :
    rgoKernel f η y = volume.withDensity (fun x => ENNReal.ofReal (rgoDensity f η y x)) :=
  densityKernel_apply (measurable_rgoDensity hf hint hη) y

/-- The RGO kernel is a Markov kernel (measurable `f`, integrable `exp ∘ (-f)`, `η > 0`). -/
theorem isMarkovKernel_rgoKernel (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsMarkovKernel (rgoKernel f η) := by
  refine isMarkovKernel_densityKernel (measurable_rgoDensity hf hint hη) fun y => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal ?_
    (Filter.Eventually.of_forall fun x => rgoDensity_nonneg y x),
    integral_rgoDensity hint hη, ENNReal.ofReal_one]
  exact (integrable_rgo hint hη y).div_const _

/-- The proximal kernel `proxKernel f η = rgoKernel f η ∘ₖ forwardKernel η` is a Markov kernel
(measurable `f`, integrable `exp ∘ (-f)`, `η > 0`). -/
theorem isMarkovKernel_proxKernel (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsMarkovKernel (proxKernel f η) := by
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_rgoKernel hf hint hη
  unfold proxKernel; infer_instance

/-! ### (g) PX-1: augmentation and invariance -/

/-- **PX-1: the RGO kernel is an exact reverse kernel of the Gaussian forward step.** For
measurable `f` with integrable `exp ∘ (-f)` and `η > 0`:
`(N ∘ₘ π) ⊗ₘ RGO = (π ⊗ₘ N).map Prod.swap`. -/
theorem isReverseKernel_rgoKernel (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsReverseKernel (forwardKernel η) (target f) (rgoKernel f η) := by
  rw [rgoKernel_eq_densityKernel hint hη, forwardKernel, target]
  refine isReverseKernel_densityKernel (measurable_targetDensity hf).ennreal_ofReal
    (measurable_forwardDensity η) (lintegral_forwardDensity hη) ?_
  rw [lintegral_targetDensity hint]
  exact ENNReal.one_ne_top

/-- **PX-1: the `y | x` conditional of the augmented law is `N(x, η)`.** For measurable `f`
and `η > 0`: `π ⊗ₘ N(·, η) = augmentedJoint f η` (density `π(x) N(y; x, η)`). -/
theorem target_compProd_forwardKernel (hf : Measurable f) (hη : 0 < η) :
    target f ⊗ₘ forwardKernel η = augmentedJoint f η := by
  have : IsMarkovKernel (densityKernel volume (forwardDensity η)) :=
    isMarkovKernel_forwardKernel hη
  exact withDensity_compProd_densityKernel (measurable_targetDensity hf).ennreal_ofReal
    (measurable_forwardDensity η)

/-- **PX-1: the `x | y` conditional of the augmented law is `RGO(y)`.** For measurable `f`
with integrable `exp ∘ (-f)` and `η > 0`, the augmented law with coordinates swapped is
`(N ∘ₘ π) ⊗ₘ RGO`. -/
theorem augmentedJoint_map_swap (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    (augmentedJoint f η).map Prod.swap = (forwardKernel η ∘ₘ target f) ⊗ₘ rgoKernel f η := by
  rw [← target_compProd_forwardKernel hf hη]
  exact (isReverseKernel_rgoKernel hf hint hη).symm

/-- The augmented joint law is a probability measure (measurable `f`, integrable `exp ∘ (-f)`,
`η > 0`). -/
theorem isProbabilityMeasure_augmentedJoint (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsProbabilityMeasure (augmentedJoint f η) := by
  have := isProbabilityMeasure_target hint
  have := isMarkovKernel_forwardKernel hη
  rw [← target_compProd_forwardKernel hf hη]
  infer_instance

/-- The `x`-marginal of the augmented law is the target `π` (measurable `f`, `η > 0`). -/
theorem augmentedJoint_fst (hf : Measurable f) (hη : 0 < η) :
    (augmentedJoint f η).fst = target f := by
  have := isMarkovKernel_forwardKernel hη
  rw [← target_compProd_forwardKernel hf hη, Measure.fst_compProd]

attribute [local instance] isFiniteKernel_forwardKernel

/-- **PX-1: the RGO is a.e. Mathlib's posterior.** For measurable `f` with integrable
`exp ∘ (-f)` and `η > 0`, `RGO = N(·, η)†π` almost everywhere under the `y`-marginal
`N ∘ₘ π`. -/
theorem rgoKernel_ae_eq_posterior (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    rgoKernel f η =ᵐ[forwardKernel η ∘ₘ target f] (forwardKernel η)†(target f) := by
  have := isMarkovKernel_rgoKernel hf hint hη
  exact (isReverseKernel_rgoKernel hf hint hη).ae_eq_posterior

/-- **PX-1: disintegration of the augmented law in `x`.** For measurable `f` with integrable
`exp ∘ (-f)` and `η > 0`, the conditional kernel (`Measure.condKernel`) of `augmentedJoint f η`
is `N(x, η)` for `π`-a.e. `x`. -/
theorem ae_forwardKernel_eq_condKernel (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    haveI := isProbabilityMeasure_augmentedJoint hf hint hη
    ∀ᵐ x ∂target f, forwardKernel η x = (augmentedJoint f η).condKernel x := by
  have := isProbabilityMeasure_augmentedJoint hf hint hη
  have h := eq_condKernel_of_measure_eq_compProd (ρ := augmentedJoint f η) (forwardKernel η)
    (by rw [augmentedJoint_fst hf hη, target_compProd_forwardKernel hf hη])
  rwa [augmentedJoint_fst hf hη] at h

/-- **PX-1: disintegration of the augmented law in `y`.** For measurable `f` with integrable
`exp ∘ (-f)` and `η > 0`, the conditional kernel of the swapped augmented law is `RGO(y)` for
`(N ∘ₘ π)`-a.e. `y`. -/
theorem ae_rgoKernel_eq_condKernel_swap (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    haveI := isProbabilityMeasure_augmentedJoint hf hint hη
    ∀ᵐ y ∂(forwardKernel η ∘ₘ target f),
      rgoKernel f η y = ((augmentedJoint f η).map Prod.swap).condKernel y := by
  have := isProbabilityMeasure_augmentedJoint hf hint hη
  have := isMarkovKernel_rgoKernel hf hint hη
  have := isMarkovKernel_forwardKernel hη
  have hfst : ((augmentedJoint f η).map Prod.swap).fst = forwardKernel η ∘ₘ target f := by
    rw [Measure.fst_map_swap, ← target_compProd_forwardKernel hf hη, Measure.snd_compProd]
  have h := eq_condKernel_of_measure_eq_compProd (ρ := (augmentedJoint f η).map Prod.swap)
    (rgoKernel f η) (by rw [hfst, augmentedJoint_map_swap hf hint hη])
  rwa [hfst] at h

/-- **PX-1: invariance of `π` under the exact proximal step (measure form).** For measurable
`f` with integrable `exp ∘ (-f)` and `η > 0`: `proxKernel f η ∘ₘ π = π`. -/
theorem proxKernel_comp_target (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    proxKernel f η ∘ₘ target f = target f := by
  have := isMarkovKernel_rgoKernel hf hint hη
  have := isMarkovKernel_forwardKernel hη
  rw [proxKernel, ← Measure.comp_assoc]
  exact (isReverseKernel_rgoKernel hf hint hη).comp_marginal

/-- **PX-1: invariance of `π` (integral form).** For measurable `f` with integrable
`exp ∘ (-f)`, `η > 0` and a measurable set `A`:
`∫ π(x) [∫ RGO(y, A) N(x, η)(dy)] dx = π(A)`, with `N(x, η) = gaussianReal x η.toNNReal`. -/
theorem lintegral_target_proxStep (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ x, ENNReal.ofReal (targetDensity f x)
        * (∫⁻ y, rgoKernel f η y A ∂(gaussianReal x η.toNNReal)) = target f A := by
  have h := congrArg (fun μ : Measure ℝ => μ A) (proxKernel_comp_target hf hint hη)
  rw [← h, Measure.bind_apply hA (Kernel.aemeasurable _), target,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_targetDensity hf).ennreal_ofReal
      ((proxKernel f η).measurable_coe hA)]
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply, proxKernel, Kernel.comp_apply' _ _ _ hA, forwardKernel_apply hη]

/-- **PX-1: invariance of `π` (pure density form).** For measurable `f` with integrable
`exp ∘ (-f)`, `η > 0` and **any** set `A`:
`∫⁻ x, π(x) ∫⁻ y, N(y; x, η) (∫⁻ x' in A, RGO_y(x') dx') dy dx = ∫⁻ x in A, π(x) dx`. -/
theorem lintegral_proximal_invariance (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (A : Set ℝ) :
    ∫⁻ x, ENNReal.ofReal (targetDensity f x)
        * (∫⁻ y, ENNReal.ofReal (gaussianPDFReal x η.toNNReal y)
          * (∫⁻ x' in A, ENNReal.ofReal (rgoDensity f η y x'))) =
      ∫⁻ x in A, ENNReal.ofReal (targetDensity f x) := by
  have h := lintegral_forward_reverse_setLIntegral (ν := volume) (ρ := volume)
    (measurable_targetDensity hf).ennreal_ofReal (measurable_forwardDensity η)
    (lintegral_forwardDensity hη)
    (Filter.Eventually.of_forall fun y => (marginalDensity_pos_ne_top hint hη y).2) A
  rw [← rgoDensity_eq_reverseDensity hint hη] at h
  exact h

end FormalizeSampling.Proximal
