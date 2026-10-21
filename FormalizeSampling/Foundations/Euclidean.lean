module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.HeatKernelPi
public import FormalizeSampling.Foundations.KLProduct
public import FormalizeSampling.Foundations.LogSobolevPi
public import FormalizeSampling.Foundations.TotalVariation

/-!
# Transfer between `Fin d → ℝ` and `EuclideanSpace ℝ (Fin d)`

Status: **Verified** (no named hypotheses).

The library works on the product space `Fin d → ℝ`, whose Mathlib norm is the sup norm, and
writes every Euclidean quantity in coordinates: `ProximalPi.sqDist x y = ∑ᵢ (xᵢ - yᵢ)²`,
`dotProduct`, `grad`, `laplacian`, `LogSobolevPi.gradSq`, Gaussians as `Measure.pi` of
`gaussianReal`, Gibbs measures `ProximalPi.targetPi f ∝ e^{-f}`. Mathlib's Euclidean space
`EuclideanSpace ℝ (Fin d)` carries the same coordinates with the `L²` norm and inner product.
The two spaces are identified by `WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)` and
its inverse `WithLp.ofLp`, packaged by Mathlib as the measurable equivalence
`MeasurableEquiv.toLp 2 (Fin d → ℝ)` (with `⇑(MeasurableEquiv.toLp 2 _) = WithLp.toLp 2` by
definition). This module shows that every object above corresponds to its Mathlib counterpart on
`EuclideanSpace ℝ (Fin d)`, so results of the library apply to laws, potentials and test
functions given on the Euclidean space: push laws forward by `WithLp.ofLp`, precompose functions
with `WithLp.toLp 2`, apply the theorem on `Fin d → ℝ`, and transfer back.

## Main results

* Measure: `measurePreserving_toLp`, `measurePreserving_ofLp` (Lebesgue measure is preserved),
  `map_ofLp_map_toLp`, `map_toLp_map_ofLp`, `integral_comp_toLp`, `integral_map_toLp`,
  `lintegral_comp_toLp` and their Euclidean-side forms `integral_comp_ofLp`, `integral_map_ofLp`,
  `lintegral_comp_ofLp`; `integrable_comp_toLp_iff`, `measurable_comp_toLp_iff`;
  `map_toLp_withDensity`, `map_ofLp_withDensity` (densities transfer by composition),
  `map_toLp_tilted`, `map_toLp_targetPi`, `map_ofLp_tilted` (the Gibbs measure
  `targetPi (g ∘ toLp)` is Mathlib's `volume.tilted (-g)` on the Euclidean space).
* Divergences: `klDiv_map_toLp`, `klDiv_map_ofLp`, `tvSup_map_toLp`, `tvSup_map_ofLp` (KL and
  `tvSup` are unchanged when both laws are transferred), `klDiv_tilted_eq_klDiv_targetPi`,
  `tvSup_tilted_eq_tvSup_targetPi` (divergences to a Gibbs measure on the Euclidean space).
* Gaussians: `map_toLp_pi_gaussianReal` (`⊗ᵢ N(mᵢ, v)` is Mathlib's
  `multivariateGaussian m (v • 1)`), `map_ofLp_multivariateGaussian`, `map_toLp_heatKernelPi`,
  `map_toLp_pi_gaussianReal_zero_one`, `map_ofLp_stdGaussian` (the product of standard normals
  is Mathlib's `stdGaussian`), `map_toLp_targetPi_gaussPotentialPi`.
* Geometry: `sum_sq_eq_norm_toLp_sq`, `sqDist_eq_dist_sq`, `sqDist_eq_norm_sub_sq`,
  `sqDist_ofLp`, `dotProduct_eq_inner`, `sqNormH_eq_inner`, `gaussPotentialPi_eq_norm_sq`,
  `norm_le_norm_toLp`, `norm_toLp_le` (`‖x‖_∞ ≤ ‖x‖₂ ≤ √d ‖x‖_∞`).
* Calculus: `fderiv_comp_toLp`, `partialDeriv_comp_toLp`, `grad_comp_toLp` (the coordinate
  gradient of `g ∘ toLp` is Mathlib's `gradient g`, with no differentiability assumption),
  `grad_eq_ofLp_gradient`, `gradSq_comp_toLp`, `grad_dotProduct_grad_comp_toLp`
  (`|∇(g ∘ toLp)|² = ‖gradient g‖²`), `score_comp_toLp`, `differentiable_comp_toLp_iff`,
  `laplacian_comp_toLp`, `laplacian_comp_toLp_of_contDiffAt` (the coordinate Laplacian is
  Mathlib's `Δ` where `g` is twice differentiable, in particular for `C²` functions).
* Log-Sobolev inequalities: `ent_sq_le_of_functionalLSIPi` (a functional LSI for `ofLp₊ν`
  gives `Ent_ν(φ²) ≤ 2 C ∫ ‖∇φ‖² dν` with Mathlib's `gradient`).

## Not proved here

* Divergences of vector fields: Mathlib has no divergence operator on `EuclideanSpace`.
* Sampler-level statements: `Samplers/EuclideanTransfer.lean` transfers the invariance of the
  target under the proximal sampler (PX-1), the strongly log-concave proximal-sampler rate (PX-6)
  and the Bakry–Émery inequality.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace FormalizeSampling.Euclidean

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi

variable {d : ℕ}

/-! ### The measurable equivalence and Lebesgue measure -/

/-- `WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)` maps Lebesgue measure to Lebesgue
measure (Mathlib's `PiLp.volume_preserving_toLp`). -/
theorem measurePreserving_toLp :
    MeasurePreserving (toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) volume volume :=
  PiLp.volume_preserving_toLp (Fin d)

/-- `WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)` maps Lebesgue measure to Lebesgue
measure (Mathlib's `PiLp.volume_preserving_ofLp`). -/
theorem measurePreserving_ofLp :
    MeasurePreserving (ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) volume volume :=
  PiLp.volume_preserving_ofLp (Fin d)

/-- Transferring a measure on `Fin d → ℝ` to the Euclidean space and back returns it:
`(μ.map toLp).map ofLp = μ` (any measure). -/
theorem map_ofLp_map_toLp (μ : Measure (Fin d → ℝ)) : (μ.map (toLp 2)).map ofLp = μ :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).map_symm_map

/-- Transferring a measure on the Euclidean space to `Fin d → ℝ` and back returns it:
`(ν.map ofLp).map toLp = ν` (any measure). -/
theorem map_toLp_map_ofLp (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    (ν.map ofLp).map (toLp 2) = ν :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).map_map_symm

/-- Change of variables: `∫ h(toLp x) dx = ∫ h(y) dy` for every `h` on the Euclidean space with
values in a real normed space (both sides are `0` when `h` is not integrable). -/
theorem integral_comp_toLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : EuclideanSpace ℝ (Fin d) → G) : ∫ x, h (toLp 2 x) = ∫ y, h y :=
  MeasurePreserving.integral_comp' (f := MeasurableEquiv.toLp 2 (Fin d → ℝ))
    measurePreserving_toLp h

/-- Integrals against a transferred law: `∫ h d(toLp₊μ) = ∫ h(toLp x) dμ(x)` for every measure
`μ` on `Fin d → ℝ` and every `h` with values in a real normed space. -/
theorem integral_map_toLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure (Fin d → ℝ)) (h : EuclideanSpace ℝ (Fin d) → G) :
    ∫ y, h y ∂(μ.map (toLp 2)) = ∫ x, h (toLp 2 x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.toLp 2 (Fin d → ℝ)) h

/-- Change of variables for lower Lebesgue integrals: `∫⁻ h(toLp x) dx = ∫⁻ h(y) dy` for every
`h` on the Euclidean space (no measurability needed). -/
theorem lintegral_comp_toLp (h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x, h (toLp 2 x) = ∫⁻ y, h y :=
  MeasurePreserving.lintegral_comp_emb measurePreserving_toLp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding h

/-- Change of variables, Euclidean side: `∫ h(ofLp y) dy = ∫ h(x) dx` for every `h` on
`Fin d → ℝ` with values in a real normed space (both sides are `0` when `h` is not integrable). -/
theorem integral_comp_ofLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : (Fin d → ℝ) → G) : ∫ y : EuclideanSpace ℝ (Fin d), h (ofLp y) = ∫ x, h x :=
  MeasurePreserving.integral_comp' (f := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
    measurePreserving_ofLp h

/-- Integrals against a law transferred to `Fin d → ℝ`: `∫ h d(ofLp₊ν) = ∫ h(ofLp y) dν(y)` for
every measure `ν` on the Euclidean space and every `h` with values in a real normed space. -/
theorem integral_map_ofLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (h : (Fin d → ℝ) → G) :
    ∫ x, h x ∂(ν.map ofLp) = ∫ y, h (ofLp y) ∂ν :=
  integral_map_equiv (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm h

/-- Change of variables for lower Lebesgue integrals, Euclidean side:
`∫⁻ h(ofLp y) dy = ∫⁻ h(x) dx` for every `h` on `Fin d → ℝ` (no measurability needed). -/
theorem lintegral_comp_ofLp (h : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ y : EuclideanSpace ℝ (Fin d), h (ofLp y) = ∫⁻ x, h x :=
  MeasurePreserving.lintegral_comp_emb measurePreserving_ofLp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding h

/-- `h ∘ toLp` is Lebesgue integrable on `Fin d → ℝ` iff `h` is Lebesgue integrable on the
Euclidean space (any `h` with values in a normed group). -/
theorem integrable_comp_toLp_iff {G : Type*} [NormedAddCommGroup G]
    {h : EuclideanSpace ℝ (Fin d) → G} :
    Integrable (fun x : Fin d → ℝ => h (toLp 2 x)) ↔ Integrable h :=
  measurePreserving_toLp.integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding

/-- `h ∘ toLp` is measurable on `Fin d → ℝ` iff `h` is measurable on the Euclidean space (any
measurable codomain). -/
theorem measurable_comp_toLp_iff {β : Type*} [MeasurableSpace β]
    {h : EuclideanSpace ℝ (Fin d) → β} :
    Measurable (fun x : Fin d → ℝ => h (toLp 2 x)) ↔ Measurable h :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable_comp_iff

/-- **Densities transfer by composition.** For every `p : (Fin d → ℝ) → ℝ≥0∞`, the law with
Lebesgue density `p` is carried by `toLp` to the law with Lebesgue density `p ∘ ofLp`. -/
theorem map_toLp_withDensity (p : (Fin d → ℝ) → ℝ≥0∞) :
    ((volume : Measure (Fin d → ℝ)).withDensity p).map (toLp 2) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity fun y => p (ofLp y) := by
  ext s hs
  rw [Measure.map_apply (measurable_toLp 2 _) hs, withDensity_apply _ (hs.preimage
    (measurable_toLp 2 _)), withDensity_apply _ hs]
  exact measurePreserving_toLp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding (fun y => p (ofLp y)) s

/-- **Densities transfer by composition**, Euclidean side. For every
`p : EuclideanSpace ℝ (Fin d) → ℝ≥0∞`, the law with Lebesgue density `p` is carried by `ofLp`
to the law with Lebesgue density `p ∘ toLp` on `Fin d → ℝ`. -/
theorem map_ofLp_withDensity (p : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity p).map ofLp =
      (volume : Measure (Fin d → ℝ)).withDensity fun x => p (toLp 2 x) := by
  rw [← map_ofLp_map_toLp ((volume : Measure (Fin d → ℝ)).withDensity fun x => p (toLp 2 x)),
    map_toLp_withDensity]

/-- **Tilted measures transfer.** For every `h : (Fin d → ℝ) → ℝ`, Mathlib's exponential tilt
of Lebesgue measure on `Fin d → ℝ` by `h` is carried by `toLp` to the tilt of Lebesgue measure
on the Euclidean space by `h ∘ ofLp` (both are `0` when `e^h` is not integrable). -/
theorem map_toLp_tilted (h : (Fin d → ℝ) → ℝ) :
    ((volume : Measure (Fin d → ℝ)).tilted h).map (toLp 2) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => h (ofLp y) := by
  rw [Measure.tilted, Measure.tilted, map_toLp_withDensity]
  congr 2
  funext y
  rw [← integral_comp_toLp fun y : EuclideanSpace ℝ (Fin d) => Real.exp (h (ofLp y))]

/-- **The library's Gibbs measure is Mathlib's tilted measure.** For every potential
`g : EuclideanSpace ℝ (Fin d) → ℝ`, the target `targetPi (g ∘ toLp) ∝ e^{-g(toLp x)} dx` on
`Fin d → ℝ` is carried by `toLp` to `volume.tilted (-g)`, the law `∝ e^{-g(y)} dy` on the
Euclidean space (both are `0` when `e^{-g}` is not integrable). -/
theorem map_toLp_targetPi (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    (targetPi fun x => g (toLp 2 x)).map (toLp 2) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => -g y := by
  rw [targetPi_eq_tilted, map_toLp_tilted]

/-- The Gibbs measure `volume.tilted (-g) ∝ e^{-g}` on the Euclidean space is carried by `ofLp`
to the library's target `targetPi (g ∘ toLp)` on `Fin d → ℝ` (any `g`). -/
theorem map_ofLp_tilted (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => -g y).map ofLp =
      targetPi fun x => g (toLp 2 x) := by
  rw [← map_toLp_targetPi, map_ofLp_map_toLp]

/-! ### KL divergence and total variation -/

/-- **KL is invariant under the transfer.** For finite measures `μ ν` on `Fin d → ℝ`,
`KL(toLp₊μ ‖ toLp₊ν) = KL(μ ‖ ν)` (in `ℝ≥0∞`; both sides may be `∞`). -/
theorem klDiv_map_toLp (μ ν : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map (toLp 2)) (ν.map (toLp 2)) = klDiv μ ν :=
  GaussianIncrement.klDiv_map_measurableEquiv μ ν (MeasurableEquiv.toLp 2 (Fin d → ℝ))

/-- **KL is invariant under the transfer**, Euclidean side. For finite measures `μ ν` on
`EuclideanSpace ℝ (Fin d)`, `KL(ofLp₊μ ‖ ofLp₊ν) = KL(μ ‖ ν)` (in `ℝ≥0∞`). -/
theorem klDiv_map_ofLp (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : klDiv (μ.map ofLp) (ν.map ofLp) = klDiv μ ν :=
  GaussianIncrement.klDiv_map_measurableEquiv μ ν (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm

/-- **TV is invariant under the transfer.** For all measures `μ ν` on `Fin d → ℝ`,
`tvSup (toLp₊μ) (toLp₊ν) = tvSup μ ν`. -/
theorem tvSup_map_toLp (μ ν : Measure (Fin d → ℝ)) :
    TotalVariation.tvSup (μ.map (toLp 2)) (ν.map (toLp 2)) = TotalVariation.tvSup μ ν :=
  TotalVariation.tvSup_map_measurableEquiv μ ν (MeasurableEquiv.toLp 2 (Fin d → ℝ))

/-- **TV is invariant under the transfer**, Euclidean side. For all measures `μ ν` on
`EuclideanSpace ℝ (Fin d)`, `tvSup (ofLp₊μ) (ofLp₊ν) = tvSup μ ν`. -/
theorem tvSup_map_ofLp (μ ν : Measure (EuclideanSpace ℝ (Fin d))) :
    TotalVariation.tvSup (μ.map ofLp) (ν.map ofLp) = TotalVariation.tvSup μ ν :=
  TotalVariation.tvSup_map_measurableEquiv μ ν (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm

/-- **KL to a Euclidean Gibbs measure.** For every potential `g` on the Euclidean space and
every finite measure `μ` there, `KL(μ ‖ volume.tilted (-g)) = KL(ofLp₊μ ‖ targetPi (g ∘ toLp))`
(in `ℝ≥0∞`; both sides may be `∞`). -/
theorem klDiv_tilted_eq_klDiv_targetPi (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] :
    klDiv μ ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => -g y) =
      klDiv (μ.map ofLp) (targetPi fun x => g (toLp 2 x)) := by
  have := isFiniteMeasure_targetPi fun x => g (toLp 2 x)
  calc klDiv μ ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => -g y)
      = klDiv ((μ.map ofLp).map (toLp 2)) ((targetPi fun x => g (toLp 2 x)).map (toLp 2)) := by
        rw [map_toLp_map_ofLp, map_toLp_targetPi]
    _ = klDiv (μ.map ofLp) (targetPi fun x => g (toLp 2 x)) := klDiv_map_toLp _ _

/-- **TV to a Euclidean Gibbs measure.** For every potential `g` on the Euclidean space and
every measure `μ` there, `tvSup μ (volume.tilted (-g)) = tvSup (ofLp₊μ) (targetPi (g ∘ toLp))`. -/
theorem tvSup_tilted_eq_tvSup_targetPi (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    TotalVariation.tvSup μ ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => -g y) =
      TotalVariation.tvSup (μ.map ofLp) (targetPi fun x => g (toLp 2 x)) := by
  calc TotalVariation.tvSup μ
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun y => -g y)
      = TotalVariation.tvSup ((μ.map ofLp).map (toLp 2))
          ((targetPi fun x => g (toLp 2 x)).map (toLp 2)) := by
        rw [map_toLp_map_ofLp, map_toLp_targetPi]
    _ = TotalVariation.tvSup (μ.map ofLp) (targetPi fun x => g (toLp 2 x)) :=
        tvSup_map_toLp _ _

/-! ### Gaussians -/

/-- **Isotropic Gaussians.** For a mean `m : Fin d → ℝ` and a variance `v : ℝ≥0`, the product
`⊗ᵢ N(mᵢ, v)` used throughout the library is carried by `toLp` to Mathlib's
`multivariateGaussian (toLp m) (v • 1)`, the Gaussian with mean `m` and covariance `v I`
(for `v = 0` both are the point mass at `m`). -/
theorem map_toLp_pi_gaussianReal (m : Fin d → ℝ) (v : ℝ≥0) :
    (Measure.pi fun i => gaussianReal (m i) v).map (toLp 2) =
      multivariateGaussian (toLp 2 m) ((v : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  have hS : ((v : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul v.2
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_pi, charFun_multivariateGaussian hS]
  simp only [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Isotropic Gaussians**, Euclidean side. For `m : EuclideanSpace ℝ (Fin d)` and `v : ℝ≥0`,
Mathlib's `multivariateGaussian m (v • 1)` is carried by `ofLp` to `⊗ᵢ N(mᵢ, v)`. -/
theorem map_ofLp_multivariateGaussian (m : EuclideanSpace ℝ (Fin d)) (v : ℝ≥0) :
    (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))).map ofLp =
      Measure.pi fun i => gaussianReal (m i) v := by
  rw [← map_ofLp_map_toLp (Measure.pi fun i => gaussianReal (m i) v), map_toLp_pi_gaussianReal]

/-- **The heat kernel is Mathlib's isotropic Gaussian.** For `t : ℝ≥0` and `x : Fin d → ℝ`,
`heatKernelPi t x = N(x, t I)` is carried by `toLp` to `multivariateGaussian (toLp x) (t • 1)`. -/
theorem map_toLp_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) :
    (HeatKernelPi.heatKernelPi t x).map (toLp 2) =
      multivariateGaussian (toLp 2 x) ((t : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) :=
  map_toLp_pi_gaussianReal x t

/-- **Standard Gaussian.** The product `⊗ᵢ N(0, 1)` on `Fin d → ℝ` is carried by `toLp` to
Mathlib's standard Gaussian `stdGaussian (EuclideanSpace ℝ (Fin d))` (Mathlib's
`map_pi_eq_stdGaussian`). -/
theorem map_toLp_pi_gaussianReal_zero_one :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).map (toLp 2) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) :=
  map_pi_eq_stdGaussian

/-- **Standard Gaussian**, Euclidean side. Mathlib's `stdGaussian (EuclideanSpace ℝ (Fin d))`
is carried by `ofLp` to the product `⊗ᵢ N(0, 1)` on `Fin d → ℝ`. -/
theorem map_ofLp_stdGaussian :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map ofLp =
      Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  rw [← map_toLp_pi_gaussianReal_zero_one, map_ofLp_map_toLp]

/-- **The Gaussian target.** For `α > 0`, the library's Gibbs measure of the potential
`α|x|²/2` (`targetPi (gaussPotentialPi α) = N(0, I/α)`) is carried by `toLp` to Mathlib's
`multivariateGaussian 0 (α⁻¹ • 1)`. -/
theorem map_toLp_targetPi_gaussPotentialPi {α : ℝ} (hα : 0 < α) :
    (targetPi (gaussPotentialPi (d := d) α)).map (toLp 2) =
      multivariateGaussian 0 (α⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  rw [targetPi_gaussPotentialPi hα, map_toLp_pi_gaussianReal (fun _ => 0),
    Real.coe_toNNReal _ (inv_nonneg.2 hα.le)]
  rfl

/-! ### Distances, norms and inner products -/

/-- The coordinate sum of squares is the squared Euclidean norm:
`∑ᵢ xᵢ² = ‖toLp x‖²`. -/
theorem sum_sq_eq_norm_toLp_sq (x : Fin d → ℝ) : ∑ i, x i ^ 2 = ‖toLp 2 x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- The library's squared distance is the squared Euclidean distance:
`sqDist x y = dist (toLp x) (toLp y)²`. -/
theorem sqDist_eq_dist_sq (x y : Fin d → ℝ) :
    sqDist x y = dist (toLp 2 x) (toLp 2 y) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, sqDist]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.toLp_apply, PiLp.toLp_apply, Real.dist_eq, sq_abs]

/-- The library's squared distance is the squared Euclidean norm of the difference:
`sqDist x y = ‖toLp x - toLp y‖²`. -/
theorem sqDist_eq_norm_sub_sq (x y : Fin d → ℝ) :
    sqDist x y = ‖toLp 2 x - toLp 2 y‖ ^ 2 := by
  rw [sqDist_eq_dist_sq, dist_eq_norm]

/-- For points of the Euclidean space, `sqDist (ofLp x) (ofLp y) = ‖x - y‖²`. -/
theorem sqDist_ofLp (x y : EuclideanSpace ℝ (Fin d)) : sqDist (ofLp x) (ofLp y) = ‖x - y‖ ^ 2 :=
  sqDist_eq_norm_sub_sq (ofLp x) (ofLp y)

/-- `dotProduct` is the Euclidean inner product: `x ⬝ᵥ y = ⟪toLp x, toLp y⟫`. -/
theorem dotProduct_eq_inner (x y : Fin d → ℝ) : x ⬝ᵥ y = ⟪toLp 2 x, toLp 2 y⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- The weighted squared norm `sqNormH H u = uᵀ H u` is `⟪toLp u, toLp (H u)⟫` (any square
matrix `H`). -/
theorem sqNormH_eq_inner (H : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    sqNormH H u = ⟪toLp 2 u, toLp 2 (H *ᵥ u)⟫ := by
  rw [sqNormH, dotProduct_eq_inner]

/-- The isotropic Gaussian potential is `gaussPotentialPi α x = α ‖toLp x‖² / 2`. -/
theorem gaussPotentialPi_eq_norm_sq (α : ℝ) (x : Fin d → ℝ) :
    gaussPotentialPi α x = α * ‖toLp 2 x‖ ^ 2 / 2 := by
  rw [gaussPotentialPi_apply, sum_sq_eq_norm_toLp_sq]

/-- The sup norm of `Fin d → ℝ` is at most the Euclidean norm: `‖x‖ ≤ ‖toLp x‖`. -/
theorem norm_le_norm_toLp (x : Fin d → ℝ) : ‖x‖ ≤ ‖toLp 2 x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← sum_sq_eq_norm_toLp_sq]
  exact sq_norm_le_sum_sq x

/-- The Euclidean norm is at most `√d` times the sup norm: `‖toLp x‖ ≤ √d ‖x‖`. -/
theorem norm_toLp_le (x : Fin d → ℝ) : ‖toLp 2 x‖ ≤ √d * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), ← sum_sq_eq_norm_toLp_sq, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
    _ = d * ‖x‖ ^ 2 := by simp

/-! ### Derivatives -/

/-- **Chain rule for the transfer.** For every `g : EuclideanSpace ℝ (Fin d) → ℝ`, every point
`x` and direction `v` of `Fin d → ℝ`, `D(g ∘ toLp)(x) v = Dg(toLp x)(toLp v)`. No
differentiability is needed: `toLp` is a continuous linear equivalence, so both sides vanish
when `g` is not differentiable at `toLp x`. -/
theorem fderiv_comp_toLp (g : EuclideanSpace ℝ (Fin d) → ℝ) (x v : Fin d → ℝ) :
    fderiv ℝ (fun x => g (toLp 2 x)) x v = fderiv ℝ g (toLp 2 x) (toLp 2 v) := by
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.comp_right_fderiv
    (f := g) (x := x)
  rw [PiLp.coe_symm_continuousLinearEquiv] at h
  exact congrArg (fun L => L v) h

/-- The `i`-th partial derivative of `g ∘ toLp` is the derivative of `g` in the direction of
the `i`-th standard basis vector `EuclideanSpace.single i 1` (any `g`). -/
theorem partialDeriv_comp_toLp (g : EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin d)
    (x : Fin d → ℝ) :
    partialDeriv i (fun x => g (toLp 2 x)) x =
      fderiv ℝ g (toLp 2 x) (EuclideanSpace.single i 1) := by
  rw [partialDeriv, fderiv_comp_toLp]
  rfl

/-- **The coordinate gradient is Mathlib's gradient.** For every
`g : EuclideanSpace ℝ (Fin d) → ℝ` and `x : Fin d → ℝ`,
`grad (g ∘ toLp) x = ofLp (gradient g (toLp x))` (no differentiability assumption: both sides
are `0` where `g` is not differentiable). -/
theorem grad_comp_toLp (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin d → ℝ) :
    grad (fun x => g (toLp 2 x)) x = ofLp (gradient g (toLp 2 x)) := by
  funext i
  rw [grad, partialDeriv_comp_toLp, gradient, ← InnerProductSpace.toDual_symm_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]

/-- **The coordinate gradient is Mathlib's gradient**, for functions on `Fin d → ℝ`: for every
`f : (Fin d → ℝ) → ℝ`, `grad f x = ofLp (gradient (f ∘ ofLp) (toLp x))`. -/
theorem grad_eq_ofLp_gradient (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    grad f x = ofLp (gradient (fun y => f (ofLp y)) (toLp 2 x)) :=
  grad_comp_toLp (fun y => f (ofLp y)) x

/-- **Squared gradient norm.** For every `g : EuclideanSpace ℝ (Fin d) → ℝ`, the library's
`gradSq (g ∘ toLp) x = ∑ᵢ (∂ᵢ (g ∘ toLp)(x))²` is `‖gradient g (toLp x)‖²`. -/
theorem gradSq_comp_toLp (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin d → ℝ) :
    LogSobolevPi.gradSq (fun x => g (toLp 2 x)) x = ‖gradient g (toLp 2 x)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, LogSobolevPi.gradSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrFun (grad_comp_toLp g x) i
  rw [grad] at h
  rw [← h]
  rfl

/-- **Squared gradient norm**, `dotProduct` form: for every `g : EuclideanSpace ℝ (Fin d) → ℝ`,
`∇(g ∘ toLp)(x) ⬝ᵥ ∇(g ∘ toLp)(x) = ‖gradient g (toLp x)‖²`. -/
theorem grad_dotProduct_grad_comp_toLp (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin d → ℝ) :
    grad (fun x => g (toLp 2 x)) x ⬝ᵥ grad (fun x => g (toLp 2 x)) x =
      ‖gradient g (toLp 2 x)‖ ^ 2 := by
  rw [grad_comp_toLp, dotProduct_eq_inner, real_inner_self_eq_norm_sq]

/-- **Scores transfer.** For every `p : EuclideanSpace ℝ (Fin d) → ℝ`, the state score of
`p ∘ toLp` is the Mathlib gradient of `log p`: `score (p ∘ toLp) x = ofLp (∇ log p (toLp x))`. -/
theorem score_comp_toLp (p : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin d → ℝ) :
    score (fun x => p (toLp 2 x)) x = ofLp (gradient (fun y => Real.log (p y)) (toLp 2 x)) :=
  grad_comp_toLp (fun y => Real.log (p y)) x

/-- `g ∘ toLp` is differentiable on `Fin d → ℝ` iff `g` is differentiable on the Euclidean
space. -/
theorem differentiable_comp_toLp_iff {g : EuclideanSpace ℝ (Fin d) → ℝ} :
    Differentiable ℝ (fun x => g (toLp 2 x)) ↔ Differentiable ℝ g := by
  have h :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.comp_right_differentiable_iff
      (f := g)
  rw [PiLp.coe_symm_continuousLinearEquiv] at h
  exact h

/-- **The coordinate Laplacian is Mathlib's Laplacian.** If
`g : EuclideanSpace ℝ (Fin d) → ℝ` is twice differentiable at `toLp x` (`fderiv g` is
differentiable there), then `laplacian (g ∘ toLp) x = ∑ᵢ ∂ᵢ∂ᵢ (g ∘ toLp)(x)` equals Mathlib's
`Δ g (toLp x)` (the trace of the Hessian in any orthonormal basis). -/
theorem laplacian_comp_toLp {g : EuclideanSpace ℝ (Fin d) → ℝ} {x : Fin d → ℝ}
    (hd : DifferentiableAt ℝ (fderiv ℝ g) (toLp 2 x)) :
    laplacian (fun x => g (toLp 2 x)) x = Laplacian.laplacian g (toLp 2 x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin d) ℝ), laplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : partialDeriv i (fun x => g (toLp 2 x)) =
      fun z => fderiv ℝ g (toLp 2 z) (EuclideanSpace.single i 1) :=
    funext fun z => partialDeriv_comp_toLp g i z
  rw [h1, partialDeriv_comp_toLp (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)),
    iteratedFDeriv_two_apply, fderiv_clm_apply (c := fderiv ℝ g)
      (u := fun _ => EuclideanSpace.single i 1) hd (differentiableAt_const _)]
  simp

/-- **The coordinate Laplacian is Mathlib's Laplacian**, for `C²` functions: if
`g : EuclideanSpace ℝ (Fin d) → ℝ` is `C²` near `toLp x`, then
`laplacian (g ∘ toLp) x = Δ g (toLp x)`. -/
theorem laplacian_comp_toLp_of_contDiffAt {g : EuclideanSpace ℝ (Fin d) → ℝ} {x : Fin d → ℝ}
    (hg : ContDiffAt ℝ 2 g (toLp 2 x)) :
    laplacian (fun x => g (toLp 2 x)) x = Laplacian.laplacian g (toLp 2 x) :=
  laplacian_comp_toLp ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-! ### Log-Sobolev inequalities -/

/-- **Log-Sobolev inequalities transfer.** Let `ν` be a measure on `EuclideanSpace ℝ (Fin d)`
whose transfer `ofLp₊ν` satisfies the library's functional log-Sobolev inequality with constant
`C` (`LogSobolevPi.FunctionalLSIPi`). Then `Ent_ν(φ²) ≤ 2 C ∫ ‖∇φ‖² dν`, with Mathlib's
`gradient`, for every differentiable `φ` on the Euclidean space that is bounded, has bounded
gradient and is bounded below by a positive constant (`φ ∘ toLp` is then in `LSIClassPi`). -/
theorem ent_sq_le_of_functionalLSIPi {ν : Measure (EuclideanSpace ℝ (Fin d))} {C : ℝ}
    (hLSI : LogSobolevPi.FunctionalLSIPi (ν.map ofLp) C) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφd : Differentiable ℝ φ) (hφb : ∃ M, ∀ x, |φ x| ≤ M)
    (hφg : ∃ K, ∀ x, ‖gradient φ x‖ ≤ K) (hφc : ∃ c > 0, ∀ x, c ≤ φ x) :
    LogSobolev.ent ν (fun x => φ x ^ 2) ≤ 2 * C * ∫ x, ‖gradient φ x‖ ^ 2 ∂ν := by
  obtain ⟨M, hM⟩ := hφb
  obtain ⟨K, hK⟩ := hφg
  obtain ⟨c, hc, hcφ⟩ := hφc
  have hclass : LogSobolevPi.LSIClassPi fun x => φ (toLp 2 x) := by
    refine ⟨differentiable_comp_toLp_iff.2 hφd, ⟨M, fun x => hM _⟩, ⟨K ^ 2, fun x => ?_⟩,
      c, hc, fun x => hcφ _⟩
    rw [gradSq_comp_toLp]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK _) 2
  have h := hLSI _ hclass
  rw [← map_toLp_map_ofLp ν]
  simp only [LogSobolev.ent, integral_map_toLp, ← gradSq_comp_toLp]
  exact h

end FormalizeSampling.Euclidean
