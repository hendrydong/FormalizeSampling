module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The heat kernel on `ℝ` and Gaussian smoothing

Status: **Verified** (no named hypotheses).

The Gaussian objects shared by the heat-flow, Tweedie and proximal-sampler developments on `ℝ`.
Mathlib's `gaussianReal m v` takes the **variance** `v : ℝ≥0`.

* `OU.heatKernel s x = N(x, s)`, the heat semigroup with added variance `s`, and the mixing law
  `OU.bind_affineGaussian`: `μ.bind (x ↦ N(c x, w)) = (c · μ) ∗ N(0, w)`. The `IsMarkovKernel`
  instance of `heatKernel` is scoped to `FormalizeSampling.OU`.
* `Tweedie.gaussKernel σ x y`, the density at `y` of `N(x, σ²)`, and the smoothed density
  `Tweedie.smoothedDensity μ σ y = ∫ gaussKernel σ x y dμ(x)`.
* `OUPosterior.affineDensity μ a σ y = ∫ gaussKernel σ (a x) y dμ(x)`, the density of the affine
  Gaussian channel `a X + σ Z`.
* `ProximalContraction.heatKL ρ π t = KL(ρ_t‖π_t).toReal` with `ρ_t = heatKernel t ∘ₘ ρ`.

## Main results

* `OU.bind_heat`, `OU.heatKernel_comp_heatKernel`: the heat semigroup law
  `N(x, s).bind (y ↦ N(y, t)) = N(x, s + t)`.
* `Tweedie.conv_gaussianReal_eq_withDensity`: `μ ∗ N(0, σ²)` has Lebesgue density
  `smoothedDensity μ σ` for every finite `μ` and `σ ≠ 0`.
* `OUPosterior.map_conv_gaussianReal_eq_withDensity`,
  `OUPosterior.bind_gaussianReal_affine_eq_withDensity`: `affineDensity μ a σ` is the Lebesgue
  density of `(a · μ) ∗ N(0, σ²) = μ.bind (x ↦ N(a x, σ²))`.
* `ProximalContraction.heatKL_zero`: `heatKL ρ π 0 = KL(ρ‖π).toReal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.OU

/-! ### Affine Gaussian mixtures and the heat kernel -/

/-- Auxiliary formula: `N(c x, w)(s) = ∫⁻ z, 1_s(c x + z) dN(0, w)(z)` for measurable `s`. -/
private theorem gaussianReal_affine_apply (c : ℝ) (w : ℝ≥0) (x : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    gaussianReal (c * x) w s = ∫⁻ z, s.indicator 1 (c * x + z) ∂gaussianReal 0 w := by
  have h := gaussianReal_map_const_add (μ := 0) (v := w) (c * x)
  rw [zero_add] at h
  rw [← h, Measure.map_apply (measurable_const_add _) hs,
    ← lintegral_indicator_one ((measurable_const_add _) hs)]
  rfl

/-- Measurability of the Gaussian family `x ↦ N(c x, w)` as a map `ℝ → Measure ℝ`
(for every `c : ℝ` and variance `w : ℝ≥0`). -/
theorem measurable_gaussianReal_affine (c : ℝ) (w : ℝ≥0) :
    Measurable (fun x : ℝ => gaussianReal (c * x) w) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [gaussianReal_affine_apply c w _ hs]
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => s.indicator 1 (c * p.1 + p.2))
    ((measurable_one.indicator hs).comp (by fun_prop))

/-- **Key lemma.** For every probability measure `μ` on `ℝ`, `c : ℝ` and variance `w : ℝ≥0`,
mixing the Gaussians `N(c x, w)` over `x ∼ μ` gives the convolution of the image of `μ` under
`x ↦ c x` with `N(0, w)`:
`μ.bind (x ↦ N(c x, w)) = (μ.map (c * ·)) ∗ N(0, w)`. -/
theorem bind_affineGaussian (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) (w : ℝ≥0) :
    μ.bind (fun x => gaussianReal (c * x) w) = (μ.map (fun x => c * x)) ∗ gaussianReal 0 w := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_gaussianReal_affine c w).aemeasurable,
    ← lintegral_indicator_one hs, Measure.lintegral_conv (measurable_one.indicator hs),
    lintegral_map _ (measurable_const_mul c)]
  · simp_rw [gaussianReal_affine_apply c w _ hs]
  · exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => s.indicator 1 (p.1 + p.2))
      ((measurable_one.indicator hs).comp (by fun_prop))

/-- The heat kernel with variance `s`: `heatKernel s x = N(x, s)` (the law of `x + √s Z`). -/
noncomputable def heatKernel (s : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := gaussianReal x s
  measurable' := by simpa using measurable_gaussianReal_affine 1 s

/-- Evaluation of the heat kernel: `heatKernel s x = N(x, s)`. -/
theorem heatKernel_apply (s : ℝ≥0) (x : ℝ) : heatKernel s x = gaussianReal x s := rfl

/-- `heatKernel s` is a Markov kernel. Scoped to `FormalizeSampling.OU`. -/
scoped instance isMarkovKernel_heatKernel (s : ℝ≥0) : IsMarkovKernel (heatKernel s) :=
  ⟨fun x => by rw [heatKernel_apply]; infer_instance⟩

/-- **Heat semigroup law, pointwise form.** For variances `s t : ℝ≥0` and `x : ℝ`,
`N(x, s).bind (y ↦ N(y, t)) = N(x, s + t)`. -/
theorem bind_heat (s t : ℝ≥0) (x : ℝ) :
    (gaussianReal x s).bind (fun y => gaussianReal y t) = gaussianReal x (s + t) := by
  have h := bind_affineGaussian (gaussianReal x s) 1 t
  simp only [one_mul] at h
  rw [h, Measure.map_id', gaussianReal_conv_gaussianReal, add_zero]

/-- **Heat semigroup law, kernel form**: `heatKernel t ∘ₖ heatKernel s =
heatKernel (s + t)` for variances `s t : ℝ≥0`. -/
theorem heatKernel_comp_heatKernel (s t : ℝ≥0) :
    heatKernel t ∘ₖ heatKernel s = heatKernel (s + t) := by
  ext1 x
  exact bind_heat s t x

end FormalizeSampling.OU

namespace FormalizeSampling.Tweedie

open Real

/-! ### The Gaussian kernel and the smoothed density -/

/-- The Gaussian kernel `gaussKernel σ x y = (2πσ²)^{-1/2} exp(-(y - x)² / (2σ²))`: the
Lebesgue density at `y` of `N(x, σ²)`, written with Mathlib's `gaussianPDFReal`, whose second
argument is the variance `σ ^ 2` as an element of `ℝ≥0`. For `σ = 0` Mathlib's convention makes
it identically `0`; all main results assume `σ ≠ 0`. -/
noncomputable def gaussKernel (σ x y : ℝ) : ℝ :=
  gaussianPDFReal x ⟨σ ^ 2, sq_nonneg σ⟩ y

/-- The smoothed (noised) density `p_σ(y) = ∫ gaussKernel σ x y dμ(x)`; for a probability
measure `μ` and `σ ≠ 0` it is the Lebesgue density of `Law(X + σZ)`, `X ~ μ ⊥ Z ~ N(0,1)`
(`conv_gaussianReal_eq_withDensity`). -/
noncomputable def smoothedDensity (μ : Measure ℝ) (σ y : ℝ) : ℝ :=
  ∫ x, gaussKernel σ x y ∂μ

/-- Instance search does not see through the anonymous-constructor variance `⟨σ ^ 2, _⟩`
(`ℝ≥0` is not reducibly a subtype), so the needed instances are registered directly. -/
instance (m σ : ℝ) : IsProbabilityMeasure (gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩) :=
  instIsProbabilityMeasureGaussianReal m (.mk (σ ^ 2) (sq_nonneg σ))

instance (m σ : ℝ) : IsGaussian (gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩) :=
  isGaussian_gaussianReal m (.mk (σ ^ 2) (sq_nonneg σ))

/-- `⟨σ ^ 2, _⟩` and `NNReal.mk (σ ^ 2) _` are the same element of `ℝ≥0`. -/
lemma var_eq_mk (σ : ℝ) :
    (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) = NNReal.mk (σ ^ 2) (sq_nonneg σ) := rfl
/-- Explicit formula: `gaussKernel σ x y = (√(2πσ²))⁻¹ * exp(-(y - x)² / (2σ²))`. -/
lemma gaussKernel_eq (σ x y : ℝ) :
    gaussKernel σ x y = (√(2 * π * σ ^ 2))⁻¹ * rexp (-(y - x) ^ 2 / (2 * σ ^ 2)) := by
  simp [gaussKernel, gaussianPDFReal, var_eq_mk]
/-- For `σ ≠ 0`, the variance `σ²`, viewed in `ℝ≥0`, is nonzero. -/
lemma var_ne_zero {σ : ℝ} (hσ : σ ≠ 0) : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
  intro h
  have : σ ^ 2 = 0 := congrArg NNReal.toReal h
  exact hσ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
/-- The Gaussian kernel is nonnegative (for every `σ`). -/
lemma gaussKernel_nonneg (σ x y : ℝ) : 0 ≤ gaussKernel σ x y :=
  gaussianPDFReal_nonneg _ _ _
/-- Uniform bound: `gaussKernel σ x y ≤ (√(2πσ²))⁻¹` for all `σ, x, y`. -/
lemma gaussKernel_le (σ x y : ℝ) : gaussKernel σ x y ≤ (√(2 * π * σ ^ 2))⁻¹ := by
  rw [gaussKernel_eq]
  have h1 : rexp (-(y - x) ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (y - x)]
    · positivity
  calc _ ≤ (√(2 * π * σ ^ 2))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _
/-- Joint continuity of `(x, y) ↦ gaussKernel σ x y`. -/
lemma continuous_gaussKernel_uncurry (σ : ℝ) :
    Continuous (fun p : ℝ × ℝ => gaussKernel σ p.1 p.2) := by
  simp_rw [gaussKernel_eq]
  fun_prop
/-- Continuity of `x ↦ gaussKernel σ x y` (the kernel as a function of the prior variable). -/
lemma continuous_gaussKernel_left (σ y : ℝ) : Continuous (fun x => gaussKernel σ x y) := by
  simp_rw [gaussKernel_eq]
  fun_prop
/-- For any finite measure `μ` (in particular any probability measure), any `σ` and `y`,
`x ↦ gaussKernel σ x y` is `μ`-integrable (it is bounded and continuous). -/
theorem integrable_gaussKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (σ y : ℝ) :
    Integrable (fun x => gaussKernel σ x y) μ := by
  refine Integrable.of_bound (continuous_gaussKernel_left σ y).aestronglyMeasurable
    (√(2 * π * σ ^ 2))⁻¹ (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (gaussKernel_nonneg _ _ _)]
  exact gaussKernel_le σ x y
/-- Auxiliary computation: `∫⁻ 1_s(x + w) dN(0, σ²)(w) = ∫⁻_{y ∈ s} gaussKernel σ x y dy`. -/
lemma lintegral_indicator_const_add_gaussianReal {σ : ℝ} (hσ : σ ≠ 0) {s : Set ℝ}
    (hs : MeasurableSet s) (x : ℝ) :
    ∫⁻ z, s.indicator 1 (x + z) ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
      ∫⁻ y in s, ENNReal.ofReal (gaussKernel σ x y) := by
  have h := lintegral_map (μ := gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) (f := s.indicator 1)
    (g := (x + ·)) (measurable_one.indicator hs) (measurable_const_add x)
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) ≠ 0 := var_ne_zero hσ
  rw [var_eq_mk] at h ⊢
  rw [← h, gaussianReal_map_const_add, lintegral_indicator_one hs,
    gaussianReal_apply _ hv, zero_add]
  rfl
/-- **Law identification.** For any finite measure `μ` on `ℝ` and `σ ≠ 0`, the additive
convolution `μ ∗ N(0, σ²)` equals `volume.withDensity (ofReal ∘ smoothedDensity μ σ)`. For a
probability measure `μ`, this says that `smoothedDensity μ σ` is the Lebesgue density of
`Law(X + σZ)` with `X ~ μ` independent of `Z ~ N(0,1)` (see `map_add_mul_eq_withDensity`). -/
theorem conv_gaussianReal_eq_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {σ : ℝ}
    (hσ : σ ≠ 0) :
    μ ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ =
      volume.withDensity (fun y => ENNReal.ofReal (smoothedDensity μ σ y)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator_one hs,
    Measure.lintegral_conv (measurable_one.indicator hs)]
  simp_rw [lintegral_indicator_const_add_gaussianReal hσ hs]
  rw [lintegral_lintegral_swap
    (continuous_gaussKernel_uncurry σ).measurable.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [smoothedDensity, ofReal_integral_eq_lintegral_ofReal (integrable_gaussKernel μ σ y)
    (ae_of_all _ fun x => gaussKernel_nonneg σ x y)]

end FormalizeSampling.Tweedie

namespace FormalizeSampling.OUPosterior

open Real FormalizeSampling.Tweedie FormalizeSampling.OU

/-! ### The affine Gaussian channel density -/

/-- The density of the affine Gaussian channel `Y = a X + σ Z` with `X ∼ μ`, `Z ∼ N(0, 1)`
independent: `affineDensity μ a σ y = ∫ gaussKernel σ (a x) y dμ(x)`, where
`gaussKernel σ m y` is the density at `y` of `N(m, σ²)`. For a finite `μ` and `σ ≠ 0` it is
the Lebesgue density of `(μ.map (a * ·)) ∗ N(0, σ²)`
(`map_conv_gaussianReal_eq_withDensity`). -/
noncomputable def affineDensity (μ : Measure ℝ) (a σ y : ℝ) : ℝ :=
  ∫ x, gaussKernel σ (a * x) y ∂μ

/-- Change of variables: for every measure `μ` and all `a, σ`,
`affineDensity μ a σ = smoothedDensity (μ.map (a * ·)) σ`, i.e. the affine channel density is
the Gaussian-smoothed density of the law of `a X`. -/
theorem affineDensity_eq_smoothedDensity (μ : Measure ℝ) (a σ : ℝ) :
    affineDensity μ a σ = smoothedDensity (μ.map (fun x => a * x)) σ := by
  funext y
  unfold affineDensity smoothedDensity
  rw [integral_map (measurable_const_mul a).aemeasurable
    (continuous_gaussKernel_left σ y).aestronglyMeasurable]

/-- **Law identification.** For any finite measure `μ`, any `a` and `σ ≠ 0`,
`(μ.map (a * ·)) ∗ N(0, σ²) = volume.withDensity (ofReal ∘ affineDensity μ a σ)`: for a
probability `μ`, `affineDensity μ a σ` is the Lebesgue density of `Law(a X + σ Z)`. -/
theorem map_conv_gaussianReal_eq_withDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (μ.map (fun x => a * x)) ∗ gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ =
      volume.withDensity (fun y => ENNReal.ofReal (affineDensity μ a σ y)) := by
  rw [affineDensity_eq_smoothedDensity]
  exact conv_gaussianReal_eq_withDensity _ hσ

/-- Kernel-mixture form: for any probability measure `μ`, any `a` and `σ ≠ 0`, mixing
`N(a x, σ²)` over `x ∼ μ` gives the law with Lebesgue density `affineDensity μ a σ`:
`μ.bind (x ↦ N(a x, σ²)) = volume.withDensity (ofReal ∘ affineDensity μ a σ)`. -/
theorem bind_gaussianReal_affine_eq_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    μ.bind (fun x => gaussianReal (a * x) ⟨σ ^ 2, sq_nonneg σ⟩) =
      volume.withDensity (fun y => ENNReal.ofReal (affineDensity μ a σ y)) := by
  exact (bind_affineGaussian _ a _).trans (map_conv_gaussianReal_eq_withDensity μ a hσ)

end FormalizeSampling.OUPosterior

namespace FormalizeSampling.ProximalContraction

open InformationTheory
open scoped FormalizeSampling.OU

/-! ### The KL divergence along the heat flow -/

/-- The KL divergence along the heat flow, as a real number:
`heatKL ρ π t = KL(ρ_t‖π_t).toReal` with `ρ_t = heatKernel t ∘ₘ ρ = ρ * N(0, t)` and
`π_t = heatKernel t ∘ₘ π` (`t` is the added **variance**; negative `t` is truncated to `0`).
The first argument is the evolving law, the second the evolving target. -/
noncomputable def heatKL (ρ π : Measure ℝ) (t : ℝ) : ℝ :=
  (klDiv (OU.heatKernel t.toNNReal ∘ₘ ρ) (OU.heatKernel t.toNNReal ∘ₘ π)).toReal

/-- The heat kernel with zero variance is the identity kernel. -/
theorem heatKernel_zero : OU.heatKernel 0 = Kernel.id := by
  ext x : 1
  rw [OU.heatKernel_apply, gaussianReal_zero_var, Kernel.id_apply]

/-- At time `0` the heat-flow KL is the KL of the original laws:
`heatKL ρ π 0 = KL(ρ‖π).toReal` (no assumptions). -/
theorem heatKL_zero (ρ π : Measure ℝ) : heatKL ρ π 0 = (klDiv ρ π).toReal := by
  simp [heatKL, heatKernel_zero, Measure.id_comp]

end FormalizeSampling.ProximalContraction
