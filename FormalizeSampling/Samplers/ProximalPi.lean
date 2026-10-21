module

public import FormalizeSampling.Kernels.ReverseKernel
public import FormalizeSampling.Samplers.MALA
public import FormalizeSampling.Samplers.GaussianIncrementPi
public import FormalizeSampling.Foundations.GibbsMeasure

/-!
# The exact proximal sampler on `Fin d → ℝ`: restricted Gaussian oracle and invariance

Status: **Verified** (no named hypotheses). This is the `d`-dimensional, isotropic-noise version
of `Samplers/Proximal.lean` (PX-1) and of the unconditional backward-step data processing of
`Samplers/ProximalContraction.lean`.

Target `π(x) = exp(-f x) / Z` on `Fin d → ℝ` (Lebesgue measure `volume`), with a potential
`f : (Fin d → ℝ) → ℝ`, and step size `η > 0` (the **variance** of each coordinate of the
forward Gaussian). The exact proximal sampler alternates

1. forward step `y ~ N(x, η I)` (`forwardKernelPi η`, defined as the heat kernel
   `heatKernelPi η.toNNReal`, the product measure `Measure.pi fun i => gaussianReal (x i)
   η.toNNReal`, so `forwardKernelPi_apply` is `rfl`);
2. backward step `x' ~ RGO(y)` (`rgoKernelPi f η`), the restricted Gaussian oracle with density
   `x ↦ exp(-f x - |x - y|² / (2η)) / Z_η(y)`, where `|x - y|² = sqDist x y = ∑ᵢ (xᵢ - yᵢ)²` is
   the squared **Euclidean** distance.

## Main results

* The target `targetPi f` (with `targetPi_eq_tilted`: it is Mathlib's `volume.tilted (-f)`)
  and the squared distance `sqDist` are defined in `Foundations/GibbsMeasure.lean`.
* `forwardKernelPi_apply` (`rfl`): `forwardKernelPi η x = Measure.pi fun i =>
  gaussianReal (x i) η.toNNReal`; `forwardKernelPi_eq_densityKernel`: for `η > 0` this is the
  density kernel of `forwardDensityPi η x y = ∏ᵢ N(yᵢ; xᵢ, η)` w.r.t. Lebesgue measure.
* `integrable_rgoPi`, `rgoNormalizerPi_pos`, `rgoNormalizerPi_le`: the RGO normaliser is
  positive and `≤ Z`.
* `reverseDensity_eq_rgoDensityPi`: the Bayes reverse density of the prior `π` and the Gaussian
  forward density is the RGO density at **every** point.
* `isReverseKernel_rgoKernelPi` (Bayes reverse kernel), `rgoKernelPi_ae_eq_posterior`,
  `forwardKernelPi_comp_targetPi` (density of the `y`-marginal), and the invariance
  `proxKernelPi_comp_targetPi : proxKernelPi f η ∘ₘ targetPi f = targetPi f`.
* `klDiv_proxKernelPi_comp_le_forward`: the backward step never increases KL,
  `KL(proxKernelPi f η ∘ₘ ρ ‖ π) ≤ KL(forwardKernelPi η ∘ₘ ρ ‖ forwardKernelPi η ∘ₘ π)`, and
  `klDiv_proxKernelPi_comp_le`: `KL(proxKernelPi f η ∘ₘ ρ ‖ π) ≤ KL(ρ ‖ π)`.

## Conventions

As in the one-dimensional file: `gaussianReal m v` takes the variance `v : ℝ≥0`, we use
`v = η.toNNReal`; densities are converted to `ℝ≥0∞` with `ENNReal.ofReal`. Hypotheses used:
`Measurable f` (where measurability of the prior density is needed),
`Integrable (fun x => Real.exp (-f x))` (so `Z ∈ (0, ∞)`) and `0 < η`. The norm Mathlib puts on
`Fin d → ℝ` is the sup norm and is **not** used; all squared distances are coordinate sums.

## Not proved here

* No mixing rate in this file (see `Samplers/ProximalLSIPi.lean` for the forward-step
  contraction, and `Samplers/ProximalGeneralLSIPi.lean`,
  `Samplers/ProximalStronglyLogConcaveGeneralPi.lean`, `Samplers/ProximalLogConcaveRatePi.lean`
  for unconditional rates).
* Inexact RGO oracles, anisotropic or state-dependent noise.
* That the one-dimensional file is the case `d = 1` (the two developments are separate).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory FormalizeSampling.ReverseKernel
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalPi

variable {d : ℕ}

variable (f : (Fin d → ℝ) → ℝ) (η : ℝ)

/-- The RGO normaliser `Z_η(y) = ∫ exp(-f x - |x - y|² / (2η)) dx`. -/
noncomputable def rgoNormalizerPi (y : Fin d → ℝ) : ℝ :=
  ∫ x, Real.exp (-f x - sqDist x y / (2 * η))

/-- The restricted Gaussian oracle density `x ↦ exp(-f x - |x - y|² / (2η)) / Z_η(y)`. -/
noncomputable def rgoDensityPi (y x : Fin d → ℝ) : ℝ :=
  Real.exp (-f x - sqDist x y / (2 * η)) / rgoNormalizerPi f η y

/-- The forward density `y ↦ N(y; x, η I) = ∏ᵢ N(yᵢ; xᵢ, η)` (MALA's `prodGaussianPDF`). -/
noncomputable def forwardDensityPi (x y : Fin d → ℝ) : ℝ≥0∞ :=
  MALA.prodGaussianPDF x η.toNNReal y

/-- The forward kernel `x ↦ N(x, η I)`: the isotropic heat kernel
`HeatKernelPi.heatKernelPi η.toNNReal`, i.e. the product measure
`Measure.pi fun i => gaussianReal (x i) η.toNNReal` (for `η ≤ 0` this is `δₓ`). -/
noncomputable def forwardKernelPi : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  HeatKernelPi.heatKernelPi η.toNNReal

/-- The RGO kernel `y ↦ RGO(y)` with density `rgoDensityPi f η y` w.r.t. Lebesgue measure. -/
noncomputable def rgoKernelPi : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  densityKernel volume (fun y x => ENNReal.ofReal (rgoDensityPi f η y x))

/-- One step of the exact proximal sampler on `Fin d → ℝ`: `y ~ N(x, η I)`, `x' ~ RGO(y)`. -/
noncomputable def proxKernelPi : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  rgoKernelPi f η ∘ₖ forwardKernelPi η

/-! ### Forward kernel -/

/-- The forward kernel is the isotropic product Gaussian, by definition (no assumptions):
`forwardKernelPi η x = Measure.pi fun i => gaussianReal (x i) η.toNNReal`. -/
theorem forwardKernelPi_apply (x : Fin d → ℝ) :
    forwardKernelPi η x = Measure.pi fun i => gaussianReal (x i) η.toNNReal := rfl

/-- The forward kernel is a Markov kernel for every `η` (a product of Gaussian probability
measures; for `η ≤ 0` it is `x ↦ δₓ`). -/
instance isMarkovKernel_forwardKernelPi : IsMarkovKernel (forwardKernelPi (d := d) η) :=
  ⟨fun x => by rw [forwardKernelPi_apply]; infer_instance⟩

/-- The forward density is jointly measurable in `(x, y)` (no assumptions). -/
theorem measurable_forwardDensityPi :
    Measurable (Function.uncurry (forwardDensityPi (d := d) η)) := by
  unfold forwardDensityPi MALA.prodGaussianPDF
  refine Finset.measurable_prod _ fun i _ => ?_
  unfold gaussianPDF gaussianPDFReal
  fun_prop

/-- For `η > 0`, the forward density integrates to one: `∫⁻ y, N(y; x, η I) dy = 1`. -/
theorem lintegral_forwardDensityPi {η : ℝ} (hη : 0 < η) (x : Fin d → ℝ) :
    ∫⁻ y, forwardDensityPi η x y = 1 :=
  MALA.lintegral_prodGaussianPDF x (by simpa using hη)

/-- For `η > 0`, the forward kernel is the density kernel of `forwardDensityPi η` w.r.t.
Lebesgue measure on `Fin d → ℝ`. -/
theorem forwardKernelPi_eq_densityKernel {η : ℝ} (hη : 0 < η) :
    forwardKernelPi (d := d) η = densityKernel volume (forwardDensityPi η) := by
  ext x : 1
  rw [densityKernel_apply (measurable_forwardDensityPi η), forwardKernelPi_apply,
    ← MALA.withDensity_prodGaussianPDF x (by simpa using hη)]
  rfl

/-- **Product form of the forward density.** For `η > 0`:
`∏ᵢ N(yᵢ; xᵢ, η) = (2πη)^{-d/2} exp(-|x - y|² / (2η))` (real-valued densities). -/
theorem prod_gaussianPDFReal {η : ℝ} (hη : 0 < η) (x y : Fin d → ℝ) :
    ∏ i, gaussianPDFReal (x i) η.toNNReal (y i)
      = (Real.sqrt (2 * Real.pi * η))⁻¹ ^ d * Real.exp (-(sqDist x y) / (2 * η)) := by
  simp only [gaussianPDFReal, Real.coe_toNNReal _ hη.le]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  unfold sqDist
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Target -/

variable {f η}

attribute [local instance] isFiniteMeasure_targetPi

/-! ### The RGO normaliser -/

/-- **Integrability of the RGO integrand.** If `exp ∘ (-f)` is integrable and `η > 0`, then
`x ↦ exp(-f x - |x - y|² / (2η))` is integrable for every `y`. -/
theorem integrable_rgoPi (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : Fin d → ℝ) : Integrable (fun x => Real.exp (-f x - sqDist x y / (2 * η))) := by
  have hc : Continuous fun x : Fin d → ℝ => Real.exp (-(sqDist x y / (2 * η))) := by
    have : Continuous fun x : Fin d → ℝ => sqDist x y :=
      continuous_sqDist.comp (continuous_id.prodMk continuous_const)
    fun_prop
  have h := hint.bdd_mul (f := fun x => Real.exp (-(sqDist x y / (2 * η))))
    (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  · refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    have := sqDist_nonneg x y
    positivity

/-- **Positivity of the RGO normaliser** (integrable `exp ∘ (-f)`, `η > 0`). -/
theorem rgoNormalizerPi_pos (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : Fin d → ℝ) : 0 < rgoNormalizerPi f η y :=
  integral_exp_pos (integrable_rgoPi hint hη y)

/-- **Finiteness of the RGO normaliser:** `Z_η(y) ≤ Z` (integrable `exp ∘ (-f)`, `η > 0`). -/
theorem rgoNormalizerPi_le (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : Fin d → ℝ) : rgoNormalizerPi f η y ≤ targetNormalizerPi f := by
  refine integral_mono (integrable_rgoPi hint hη y) hint fun x => ?_
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ sqDist x y / (2 * η) := div_nonneg (sqDist_nonneg x y) (by positivity)
  linarith

/-- The RGO integral in `ℝ≥0∞`: `∫⁻ x, ofReal (exp(-f x - |x - y|²/(2η))) = ofReal (Z_η(y))`
(integrable `exp ∘ (-f)`, `η > 0`). -/
theorem lintegral_rgoPi (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : Fin d → ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-f x - sqDist x y / (2 * η)))
      = ENNReal.ofReal (rgoNormalizerPi f η y) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_rgoPi hint hη y)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- The RGO density is nonnegative (no assumptions). -/
theorem rgoDensityPi_nonneg (y x : Fin d → ℝ) : 0 ≤ rgoDensityPi f η y x :=
  div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)

/-- The RGO density is a probability density (integrable `exp ∘ (-f)`, `η > 0`). -/
theorem integral_rgoDensityPi (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : Fin d → ℝ) : ∫ x, rgoDensityPi f η y x = 1 := by
  unfold rgoDensityPi
  rw [integral_div, ← rgoNormalizerPi, div_self (rgoNormalizerPi_pos hint hη y).ne']

/-! ### Bayes: the posterior is the RGO -/

/-- Prior times forward density, explicitly: for `η > 0`,
`π(x) N(y; x, η I) = ofReal((2πη)^{-d/2} / Z) * ofReal(exp(-f x - |x - y|² / (2η)))`. -/
theorem prior_mul_forwardDensityPi (hη : 0 < η) (x y : Fin d → ℝ) :
    ENNReal.ofReal (targetDensityPi f x) * forwardDensityPi η x y
      = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * η))⁻¹ ^ d / targetNormalizerPi f)
        * ENNReal.ofReal (Real.exp (-f x - sqDist x y / (2 * η))) := by
  have hZ := targetNormalizerPi_nonneg (f := f)
  have hfd : forwardDensityPi η x y = ENNReal.ofReal (∏ i, gaussianPDFReal (x i) η.toNNReal (y i))
      := by
    rw [forwardDensityPi, MALA.prodGaussianPDF, ENNReal.ofReal_prod_of_nonneg
      fun i _ => gaussianPDFReal_nonneg _ _ _]
    rfl
  rw [hfd, ← ENNReal.ofReal_mul (targetDensityPi_nonneg x),
    ← ENNReal.ofReal_mul (by positivity), prod_gaussianPDFReal hη]
  congr 1
  unfold targetDensityPi
  have : -f x - sqDist x y / (2 * η) = -f x + -sqDist x y / (2 * η) := by ring
  rw [this, Real.exp_add]
  ring

/-- **Marginal density of the forward step.** If `exp ∘ (-f)` is integrable and `η > 0`, the
density of `y` under `π(x) N(y; x, η I)` is `m(y) = ofReal((2πη)^{-d/2} / Z * Z_η(y))`. -/
theorem marginalDensityPi_eq (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η)
    (y : Fin d → ℝ) :
    marginalDensity volume (fun x => ENNReal.ofReal (targetDensityPi f x)) (forwardDensityPi η) y
      = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * η))⁻¹ ^ d / targetNormalizerPi f
          * rgoNormalizerPi f η y) := by
  unfold marginalDensity
  simp_rw [prior_mul_forwardDensityPi hη]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rgoPi hint hη,
    ← ENNReal.ofReal_mul (div_nonneg (by positivity) targetNormalizerPi_nonneg)]

/-- **RGO formula (Bayes).** If `exp ∘ (-f)` is integrable and `η > 0`, the Bayes reverse
density for the prior `π = exp(-f)/Z` on `Fin d → ℝ` and the forward kernel `N(x, η I)` is the
RGO density at every point: `reverseDensity volume π N y x = ofReal (rgoDensityPi f η y x)`. -/
theorem reverseDensity_eq_rgoDensityPi (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) (y x : Fin d → ℝ) :
    reverseDensity volume (fun x => ENNReal.ofReal (targetDensityPi f x)) (forwardDensityPi η)
        y x = ENNReal.ofReal (rgoDensityPi f η y x) := by
  have hc : 0 < (Real.sqrt (2 * Real.pi * η))⁻¹ ^ d / targetNormalizerPi f := by
    have := targetNormalizerPi_pos hint
    positivity
  unfold reverseDensity
  rw [prior_mul_forwardDensityPi hη, marginalDensityPi_eq hint hη, ENNReal.ofReal_mul hc.le,
    ENNReal.mul_div_mul_left _ _ (by simpa using hc) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_div_of_pos (rgoNormalizerPi_pos hint hη y)]
  rfl

/-- The RGO density equals the Bayes reverse density as a function of `(y, x)` (integrable
`exp ∘ (-f)`, `η > 0`). -/
theorem rgoDensityPi_eq_reverseDensity (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) :
    (fun y x => ENNReal.ofReal (rgoDensityPi f η y x))
      = reverseDensity volume (fun x => ENNReal.ofReal (targetDensityPi f x))
          (forwardDensityPi η) :=
  funext fun y => funext fun x => (reverseDensity_eq_rgoDensityPi hint hη y x).symm

/-- The RGO kernel is the density-form reverse kernel of the forward step (integrable
`exp ∘ (-f)`, `η > 0`). -/
theorem rgoKernelPi_eq_densityKernel (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) :
    rgoKernelPi f η = densityKernel volume
      (reverseDensity volume (fun x => ENNReal.ofReal (targetDensityPi f x))
        (forwardDensityPi η)) := by
  rw [rgoKernelPi, rgoDensityPi_eq_reverseDensity hint hη]

/-- The RGO density is jointly measurable in `(y, x)` (measurable `f`, integrable
`exp ∘ (-f)`, `η > 0`). -/
theorem measurable_rgoDensityPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    Measurable (Function.uncurry fun y x => ENNReal.ofReal (rgoDensityPi f η y x)) := by
  rw [rgoDensityPi_eq_reverseDensity hint hη]
  exact measurable_reverseDensity (measurable_targetDensityPi hf).ennreal_ofReal
    (measurable_forwardDensityPi η)

/-- The RGO kernel at `y` is `volume.withDensity (ofReal ∘ rgoDensityPi f η y)` (measurable
`f`, integrable `exp ∘ (-f)`, `η > 0`). -/
theorem rgoKernelPi_apply (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-f x)))
    (hη : 0 < η) (y : Fin d → ℝ) :
    rgoKernelPi f η y = volume.withDensity (fun x => ENNReal.ofReal (rgoDensityPi f η y x)) :=
  densityKernel_apply (measurable_rgoDensityPi hf hint hη) y

/-- The RGO kernel is a Markov kernel (measurable `f`, integrable `exp ∘ (-f)`, `η > 0`). -/
theorem isMarkovKernel_rgoKernelPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsMarkovKernel (rgoKernelPi f η) := by
  refine isMarkovKernel_densityKernel (measurable_rgoDensityPi hf hint hη) fun y => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal ?_
    (Filter.Eventually.of_forall fun x => rgoDensityPi_nonneg y x),
    integral_rgoDensityPi hint hη, ENNReal.ofReal_one]
  exact (integrable_rgoPi hint hη y).div_const _

/-! ### Reverse kernel and invariance -/

/-- **The RGO kernel is an exact (Bayes) reverse kernel of the Gaussian forward step.** For
measurable `f` with integrable `exp ∘ (-f)` and `η > 0`:
`(N ∘ₘ π) ⊗ₘ RGO = (π ⊗ₘ N).map Prod.swap` on `(Fin d → ℝ) × (Fin d → ℝ)`. -/
theorem isReverseKernel_rgoKernelPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsReverseKernel (forwardKernelPi η) (targetPi f) (rgoKernelPi f η) := by
  rw [rgoKernelPi_eq_densityKernel hint hη, forwardKernelPi_eq_densityKernel hη, targetPi]
  refine isReverseKernel_densityKernel (measurable_targetDensityPi hf).ennreal_ofReal
    (measurable_forwardDensityPi η) (lintegral_forwardDensityPi hη) ?_
  rw [lintegral_targetDensityPi hint]
  exact ENNReal.one_ne_top

/-- The `y`-marginal `N ∘ₘ π` has Lebesgue density `(2πη)^{-d/2} Z_η(y) / Z` (measurable `f`,
integrable `exp ∘ (-f)`, `η > 0`). -/
theorem forwardKernelPi_comp_targetPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    forwardKernelPi η ∘ₘ targetPi f = volume.withDensity
      (fun y => ENNReal.ofReal ((Real.sqrt (2 * Real.pi * η))⁻¹ ^ d / targetNormalizerPi f
        * rgoNormalizerPi f η y)) := by
  rw [forwardKernelPi_eq_densityKernel hη, targetPi, densityKernel_comp_withDensity
    (measurable_targetDensityPi hf).ennreal_ofReal (measurable_forwardDensityPi η)]
  congr 1
  exact funext fun y => marginalDensityPi_eq hint hη y

/-- **The RGO is a.e. Mathlib's posterior.** For measurable `f` with integrable `exp ∘ (-f)`
and `η > 0`, `RGO = N(·, η I)†π` almost everywhere under `N ∘ₘ π`. -/
theorem rgoKernelPi_ae_eq_posterior (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    rgoKernelPi f η =ᵐ[forwardKernelPi η ∘ₘ targetPi f] (forwardKernelPi η)†(targetPi f) := by
  have := isMarkovKernel_rgoKernelPi hf hint hη
  exact (isReverseKernel_rgoKernelPi hf hint hη).ae_eq_posterior

/-- The RGO step returns the forward image of `π` to `π`:
`rgoKernelPi f η ∘ₘ (forwardKernelPi η ∘ₘ π) = π` (measurable `f`, integrable `exp ∘ (-f)`,
`η > 0`). -/
theorem rgoKernelPi_comp_forward_targetPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    rgoKernelPi f η ∘ₘ (forwardKernelPi η ∘ₘ targetPi f) = targetPi f := by
  have := isMarkovKernel_rgoKernelPi hf hint hη
  exact (isReverseKernel_rgoKernelPi hf hint hη).comp_marginal

/-- **Invariance of `π` under the exact proximal step.** For measurable `f` with integrable
`exp ∘ (-f)` and `η > 0`: `proxKernelPi f η ∘ₘ targetPi f = targetPi f`. -/
theorem proxKernelPi_comp_targetPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    proxKernelPi f η ∘ₘ targetPi f = targetPi f := by
  have := isMarkovKernel_rgoKernelPi hf hint hη
  rw [proxKernelPi, ← Measure.comp_assoc]
  exact rgoKernelPi_comp_forward_targetPi hf hint hη

/-- The proximal kernel is a Markov kernel (measurable `f`, integrable `exp ∘ (-f)`,
`η > 0`). -/
theorem isMarkovKernel_proxKernelPi (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    IsMarkovKernel (proxKernelPi f η) := by
  have := isMarkovKernel_rgoKernelPi hf hint hη
  unfold proxKernelPi
  infer_instance

/-- The proximal output is the RGO image of the forward image:
`proxKernelPi f η ∘ₘ ρ = rgoKernelPi f η ∘ₘ (forwardKernelPi η ∘ₘ ρ)` (no assumptions). -/
theorem proxKernelPi_comp_eq (f : (Fin d → ℝ) → ℝ) (η : ℝ) (ρ : Measure (Fin d → ℝ)) :
    proxKernelPi f η ∘ₘ ρ = rgoKernelPi f η ∘ₘ (forwardKernelPi η ∘ₘ ρ) := by
  rw [proxKernelPi, Measure.comp_assoc]

/-! ### The backward step never increases KL -/

/-- **Backward step (data processing, unconditional).** For measurable `f` with integrable
`exp ∘ (-f)`, `η > 0` and any finite law `ρ` on `Fin d → ℝ`, with `π = targetPi f`:
`KL(proxKernelPi f η ∘ₘ ρ ‖ π) ≤ KL(forwardKernelPi η ∘ₘ ρ ‖ forwardKernelPi η ∘ₘ π)`.
Proof: `π = rgoKernelPi f η ∘ₘ (forwardKernelPi η ∘ₘ π)` and KL data processing for the
Markov kernel `rgoKernelPi f η`. -/
theorem klDiv_proxKernelPi_comp_le_forward (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (ρ : Measure (Fin d → ℝ))
    [IsFiniteMeasure ρ] :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)
      ≤ klDiv (forwardKernelPi η ∘ₘ ρ) (forwardKernelPi η ∘ₘ targetPi f) := by
  have := isMarkovKernel_rgoKernelPi hf hint hη
  conv_lhs => rw [← rgoKernelPi_comp_forward_targetPi hf hint hη, proxKernelPi,
    ← Measure.comp_assoc]
  exact klDiv_comp_right_le _ _ _

/-- **Non-expansiveness of the proximal step (unconditional).** For measurable `f` with
integrable `exp ∘ (-f)`, `η > 0` and any finite law `ρ`:
`KL(proxKernelPi f η ∘ₘ ρ ‖ π) ≤ KL(ρ ‖ π)` with `π = targetPi f`. -/
theorem klDiv_proxKernelPi_comp_le (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (ρ : Measure (Fin d → ℝ))
    [IsFiniteMeasure ρ] :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≤ klDiv ρ (targetPi f) :=
  (klDiv_proxKernelPi_comp_le_forward hf hint hη ρ).trans (klDiv_comp_right_le _ _ _)

end FormalizeSampling.ProximalPi
