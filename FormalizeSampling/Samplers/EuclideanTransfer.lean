module

public import FormalizeSampling.Foundations.Euclidean
public import FormalizeSampling.Samplers.DiffusionSetup
public import FormalizeSampling.Samplers.ProximalStronglyLogConcaveGeneralPi

/-!
# Worked transfers to `EuclideanSpace ℝ (Fin d)`: Bakry–Émery and the proximal sampler

Status: **Verified** (no named hypotheses).

The bridge `Foundations/Euclidean.lean` identifies `Fin d → ℝ` with Mathlib's Euclidean space
`E = EuclideanSpace ℝ (Fin d)` through `WithLp.toLp 2` and `WithLp.ofLp`. This module uses it to
state results of the library with every object and hypothesis native to `E`: Mathlib's
norm `‖x‖`, Mathlib's `gradient`, Mathlib's isotropic Gaussian `multivariateGaussian x (η • 1)`
and the Gibbs measure `π = volume.tilted (-g) ∝ e^{-g}` of a potential `g : E → ℝ`.

The exact proximal sampler on `E` (`proxKernelEuclid g η`) draws `y ~ N(x, η I)`
(`forwardKernelEuclid η`) and then `x' ~ RGO(y)` (`rgoKernelEuclid g η`), the law with Lebesgue
density `x ↦ exp(-g x - ‖x - y‖² / (2η)) / Z_η(y)`. It is conjugate to the library's
`ProximalPi.proxKernelPi (g ∘ toLp) η` (`map_ofLp_proxKernelEuclid_comp`).

## Main results

* `map_toLp_stdGaussianPi`: the library's standard Gaussian `Diffusion.stdGaussianPi d` is
  Mathlib's `stdGaussian E`.
* `rgoNormalizerEuclid_eq`, `rgoDensityEuclid_eq`, `map_ofLp_forwardKernelEuclid`,
  `map_ofLp_rgoKernelEuclid`, `map_ofLp_proxKernelEuclid`, `map_ofLp_proxKernelEuclid_comp`: the
  Euclidean proximal sampler is conjugate to `proxKernelPi` (every `g` and `η`).
* `isMarkovKernel_proxKernelEuclid`, `proxKernelEuclid_comp_tilted` (PX-1 on `E`): for
  measurable `g` with `e^{-g}` integrable and `η > 0`, `proxKernelEuclid g η` is a Markov kernel
  and leaves `π = volume.tilted (-g)` invariant.
* `convexOn_comp_toLp_sub_gaussPotentialPi`: if `g - α‖x‖²/2` is convex on `E`, then
  `g ∘ toLp - gaussPotentialPi α` is convex on `Fin d → ℝ`.
* `isProbabilityMeasure_tilted_of_stronglyLogConcave`,
  `isMarkovKernel_proxKernelEuclid_of_stronglyLogConcave`: then `π = volume.tilted (-g)` is a
  probability measure and `proxKernelEuclid g η` is a Markov kernel.
* **Bakry–Émery on `E`** (`ent_sq_le_of_stronglyLogConcave`): if `α > 0` and `g - α‖x‖²/2` is
  convex, then `Ent_π(φ²) ≤ (2/α) ∫ ‖∇φ‖² dπ` for every differentiable, bounded `φ` with bounded
  gradient and a positive lower bound.
* **PX-6 on `E`**: for `α, η > 0` and `g - α‖x‖²/2` convex, along `ρ (k+1) = proxKernelEuclid g η
  ∘ₘ ρ k` from a probability law `ρ 0` with `KL(ρ 0‖π) < ∞`:
  `KL(ρ k‖π) ≤ KL(ρ 0‖π) / (1 + α η)^{2k}` and
  `tvSup (ρ k) π ≤ √(KL(ρ 0‖π) / (2 (1 + α η)^{2k}))`
  (`toReal_klDiv_proxKernelEuclid_comp_le_sq_of_stronglyLogConcave`,
  `toReal_klDiv_iterateEuclid_le_sq_of_stronglyLogConcave`,
  `tvSup_iterateEuclid_le_sq_of_stronglyLogConcave`).

## Not proved here

* Euclidean forms of the other sampler results (GI-1, DF-1, …). They follow the same pattern:
  push the laws forward by `ofLp`, precompose potentials, drifts and scores with `toLp`, and use
  the invariance of KL and `tvSup` from `Foundations/Euclidean.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set WithLp
open scoped ENNReal NNReal

namespace FormalizeSampling.EuclideanTransfer

open FormalizeSampling.Euclidean FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.ReverseKernel FormalizeSampling.ProximalStronglyLogConcaveGeneralPi

variable {d : ℕ}

/-! ### The standard Gaussian -/

/-- The library's standard Gaussian `stdGaussianPi d = ⊗ᵢ N(0, 1)` on `Fin d → ℝ` (the initial
law of the diffusion samplers) is carried by `toLp` to Mathlib's standard Gaussian
`stdGaussian (EuclideanSpace ℝ (Fin d))`. -/
theorem map_toLp_stdGaussianPi :
    (Diffusion.stdGaussianPi d).map (toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin d)) :=
  map_toLp_pi_gaussianReal_zero_one

/-! ### The proximal sampler on the Euclidean space -/

/-- The forward step of the proximal sampler on the Euclidean space: `x ↦ N(x, η I)`, Mathlib's
`multivariateGaussian x (η • 1)` (for `η ≤ 0` this is the point mass at `x`). -/
noncomputable def forwardKernelEuclid (η : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) where
  toFun x := multivariateGaussian x (η • (1 : Matrix (Fin d) (Fin d) ℝ))
  measurable' := measurable_multivariateGaussian.comp (measurable_id.prodMk measurable_const)

/-- Evaluation of the forward kernel: `forwardKernelEuclid η x = multivariateGaussian x (η • 1)`
(by definition). -/
theorem forwardKernelEuclid_apply (η : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    forwardKernelEuclid η x = multivariateGaussian x (η • (1 : Matrix (Fin d) (Fin d) ℝ)) :=
  rfl

/-- The forward kernel is a Markov kernel (every `multivariateGaussian` is a probability
measure). -/
instance isMarkovKernel_forwardKernelEuclid (η : ℝ) :
    IsMarkovKernel (forwardKernelEuclid (d := d) η) :=
  ⟨fun x => by rw [forwardKernelEuclid_apply]; infer_instance⟩

/-- The RGO normaliser on the Euclidean space,
`Z_η(y) = ∫ exp(-g x - ‖x - y‖² / (2η)) dx`. -/
noncomputable def rgoNormalizerEuclid (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ x, Real.exp (-g x - ‖x - y‖ ^ 2 / (2 * η))

/-- The restricted Gaussian oracle density on the Euclidean space,
`x ↦ exp(-g x - ‖x - y‖² / (2η)) / Z_η(y)`. -/
noncomputable def rgoDensityEuclid (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (y x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-g x - ‖x - y‖ ^ 2 / (2 * η)) / rgoNormalizerEuclid g η y

/-- The restricted Gaussian oracle on the Euclidean space: `y ↦ RGO(y)`, the law with Lebesgue
density `rgoDensityEuclid g η y`. -/
noncomputable def rgoKernelEuclid (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) :=
  densityKernel volume fun y x => ENNReal.ofReal (rgoDensityEuclid g η y x)

/-- One step of the exact proximal sampler on the Euclidean space: `y ~ N(x, η I)`, then
`x' ~ RGO(y)`. -/
noncomputable def proxKernelEuclid (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) :=
  rgoKernelEuclid g η ∘ₖ forwardKernelEuclid η

/-- The Euclidean RGO normaliser is the library's: `Z_η(y) = rgoNormalizerPi (g ∘ toLp) η
(ofLp y)` (any `g`, `η`; change of variables). -/
theorem rgoNormalizerEuclid_eq (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    rgoNormalizerEuclid g η y = rgoNormalizerPi (fun x => g (toLp 2 x)) η (ofLp y) := by
  rw [rgoNormalizerPi, rgoNormalizerEuclid]
  simp_rw [sqDist_eq_norm_sub_sq]
  exact (integral_comp_toLp fun x => Real.exp (-g x - ‖x - y‖ ^ 2 / (2 * η))).symm

/-- The Euclidean RGO density is the library's: `rgoDensityEuclid g η y x =
rgoDensityPi (g ∘ toLp) η (ofLp y) (ofLp x)` (any `g`, `η`). -/
theorem rgoDensityEuclid_eq (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (y x : EuclideanSpace ℝ (Fin d)) :
    rgoDensityEuclid g η y x = rgoDensityPi (fun x => g (toLp 2 x)) η (ofLp y) (ofLp x) := by
  rw [rgoDensityEuclid, rgoDensityPi, rgoNormalizerEuclid_eq, sqDist_ofLp]

/-- **The forward step is conjugate to `forwardKernelPi`.** For every `η`,
`ofLp₊ N(x, η I) = forwardKernelPi η (ofLp x)` (for `η ≤ 0` both are point masses). -/
theorem map_ofLp_forwardKernelEuclid (η : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (forwardKernelEuclid η x).map ofLp = forwardKernelPi η (ofLp x) := by
  have key : ∀ η' : ℝ, 0 ≤ η' →
      (forwardKernelEuclid η' x).map ofLp = forwardKernelPi η' (ofLp x) := fun η' hη' => by
    rw [forwardKernelPi_apply, forwardKernelEuclid_apply, ← map_ofLp_multivariateGaussian,
      Real.coe_toNNReal _ hη']
  rcases le_or_gt 0 η with hη | hη
  · exact key η hη
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- in dimension zero all covariance matrices coincide
    have hPi : forwardKernelPi η (ofLp x) = forwardKernelPi 0 (ofLp x) := by
      rw [forwardKernelPi_apply, forwardKernelPi_apply, Real.toNNReal_of_nonpos hη.le,
        Real.toNNReal_zero]
    rw [hPi, ← key 0 le_rfl, forwardKernelEuclid_apply, forwardKernelEuclid_apply]
    exact congrArg (fun S => (multivariateGaussian x S).map ofLp) (Subsingleton.elim _ _)
  -- for `d ≥ 1` the matrix `η • 1` is not positive semidefinite: both sides are point masses
  have hS : ¬ (η • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := fun hS => by
    have h := hS.diag_nonneg (i := ⟨0, hd⟩)
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    linarith
  change _ = HeatKernelPi.heatKernelPi η.toNNReal (ofLp x)
  rw [forwardKernelEuclid_apply, multivariateGaussian_of_not_posSemidef x hS,
    Measure.map_dirac' (measurable_ofLp 2 _), Real.toNNReal_of_nonpos hη.le,
    HeatKernelPi.heatKernelPi_zero, Kernel.id_apply]

/-- **The RGO step is conjugate to `rgoKernelPi`.** For every `g` and `η`,
`ofLp₊ RGO(y) = rgoKernelPi (g ∘ toLp) η (ofLp y)` (both are `0` when the density is not
jointly measurable). -/
theorem map_ofLp_rgoKernelEuclid (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    (rgoKernelEuclid g η y).map ofLp = rgoKernelPi (fun x => g (toLp 2 x)) η (ofLp y) := by
  set f : (Fin d → ℝ) → ℝ := fun x => g (toLp 2 x)
  have hk : (Function.uncurry fun y x => ENNReal.ofReal (rgoDensityEuclid g η y x)) =
      (Function.uncurry fun y x => ENNReal.ofReal (rgoDensityPi f η y x)) ∘
        Prod.map ofLp ofLp := by
    funext p
    simp only [rgoDensityEuclid_eq]
    rfl
  by_cases hm : Measurable (Function.uncurry fun y x => ENNReal.ofReal (rgoDensityPi f η y x))
  · have hmE : Measurable (Function.uncurry fun y x =>
        ENNReal.ofReal (rgoDensityEuclid g η y x)) := by
      rw [hk]
      exact hm.comp ((measurable_ofLp 2 _).prodMap (measurable_ofLp 2 _))
    rw [rgoKernelEuclid, rgoKernelPi, densityKernel_apply hmE, densityKernel_apply hm,
      map_ofLp_withDensity]
    simp_rw [rgoDensityEuclid_eq]
    rfl
  · have hmE : ¬ Measurable (Function.uncurry fun y x =>
        ENNReal.ofReal (rgoDensityEuclid g η y x)) := fun h => hm (by
      have h' := h.comp ((measurable_toLp 2 _).prodMap (measurable_toLp 2 _))
      rw [hk] at h'
      exact h')
    rw [rgoKernelEuclid, rgoKernelPi, densityKernel, densityKernel,
      Kernel.withDensity_of_not_measurable _ hmE, Kernel.withDensity_of_not_measurable _ hm]
    simp

/-- **The proximal step is conjugate to `proxKernelPi`.** For every `g` and `η`,
`ofLp₊ (proxKernelEuclid g η x) = proxKernelPi (g ∘ toLp) η (ofLp x)`. -/
theorem map_ofLp_proxKernelEuclid (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (proxKernelEuclid g η x).map ofLp = proxKernelPi (fun x => g (toLp 2 x)) η (ofLp x) := by
  rw [proxKernelEuclid, proxKernelPi, Kernel.comp_apply, Kernel.comp_apply,
    Measure.map_bind (rgoKernelEuclid g η).measurable.aemeasurable
      (measurable_ofLp 2 _).aemeasurable, ← map_ofLp_forwardKernelEuclid η,
    Measure.bind_map (measurable_ofLp 2 _).aemeasurable
      (rgoKernelPi _ η).measurable.aemeasurable]
  simp_rw [map_ofLp_rgoKernelEuclid]

/-- **The proximal sampler is conjugate to `proxKernelPi`, on laws.** For every `g`, `η` and
every measure `ρ` on the Euclidean space,
`ofLp₊ (proxKernelEuclid g η ∘ₘ ρ) = proxKernelPi (g ∘ toLp) η ∘ₘ ofLp₊ ρ`. -/
theorem map_ofLp_proxKernelEuclid_comp (g : EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) :
    (proxKernelEuclid g η ∘ₘ ρ).map ofLp =
      proxKernelPi (fun x => g (toLp 2 x)) η ∘ₘ ρ.map ofLp := by
  rw [Measure.map_bind (proxKernelEuclid g η).measurable.aemeasurable
      (measurable_ofLp 2 _).aemeasurable,
    Measure.bind_map (measurable_ofLp 2 _).aemeasurable
      (proxKernelPi _ η).measurable.aemeasurable]
  simp_rw [map_ofLp_proxKernelEuclid g η]

variable {g : EuclideanSpace ℝ (Fin d) → ℝ} {α η : ℝ}

/-! ### Markov property and invariance of the target -/

/-- **The Euclidean proximal sampler is a Markov kernel.** For measurable `g` with `e^{-g}`
Lebesgue integrable on the Euclidean space and `η > 0`, `proxKernelEuclid g η` is a Markov
kernel. -/
theorem isMarkovKernel_proxKernelEuclid (hg : Measurable g)
    (hint : Integrable fun x => Real.exp (-g x)) (hη : 0 < η) :
    IsMarkovKernel (proxKernelEuclid g η) := by
  have := isMarkovKernel_proxKernelPi ((measurable_comp_toLp_iff (h := g)).2 hg)
    ((integrable_comp_toLp_iff (h := fun x => Real.exp (-g x))).2 hint) hη
  refine ⟨fun x => ?_⟩
  have h : IsProbabilityMeasure ((proxKernelEuclid g η x).map ofLp) := by
    rw [map_ofLp_proxKernelEuclid g η x]
    infer_instance
  rw [← map_toLp_map_ofLp (proxKernelEuclid g η x)]
  infer_instance

/-- **Invariance of the Gibbs measure under the Euclidean proximal step (PX-1).** For
measurable `g` with `e^{-g}` Lebesgue integrable on the Euclidean space and `η > 0`, the Gibbs
measure `π = volume.tilted (-g) ∝ e^{-g}` is invariant: `proxKernelEuclid g η ∘ₘ π = π`. -/
theorem proxKernelEuclid_comp_tilted (hg : Measurable g)
    (hint : Integrable fun x => Real.exp (-g x)) (hη : 0 < η) :
    proxKernelEuclid g η ∘ₘ (volume.tilted fun x => -g x) = volume.tilted fun x => -g x := by
  rw [← map_toLp_map_ofLp (proxKernelEuclid g η ∘ₘ _), map_ofLp_proxKernelEuclid_comp,
    map_ofLp_tilted, proxKernelPi_comp_targetPi ((measurable_comp_toLp_iff (h := g)).2 hg)
      ((integrable_comp_toLp_iff (h := fun x => Real.exp (-g x))).2 hint) hη,
    map_toLp_targetPi]

/-! ### Strongly log-concave targets -/

/-- **Strong convexity transfers.** If `g - α‖x‖²/2` is convex on the Euclidean space, then
`g ∘ toLp - gaussPotentialPi α` is convex on `Fin d → ℝ`. -/
theorem convexOn_comp_toLp_sub_gaussPotentialPi
    (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2) :
    ConvexOn ℝ univ fun x : Fin d → ℝ => g (toLp 2 x) - gaussPotentialPi α x := by
  have h := hconv.comp_linearMap (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap
  simp only [preimage_univ] at h
  convert h using 1
  funext x
  simp [gaussPotentialPi_eq_norm_sq, WithLp.coe_symm_linearEquiv]

/-- If `α > 0` and `g - α‖x‖²/2` is convex on the Euclidean space, the Gibbs measure
`volume.tilted (-g) ∝ e^{-g}` is a probability measure (`e^{-g}` is integrable). -/
theorem isProbabilityMeasure_tilted_of_stronglyLogConcave (hα : 0 < α)
    (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2) :
    IsProbabilityMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun x => -g x) := by
  have hint := (ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi hα
    (convexOn_comp_toLp_sub_gaussPotentialPi hconv)).1
  have := isProbabilityMeasure_targetPi hint
  rw [← map_toLp_targetPi]
  infer_instance

/-- **Bakry–Émery on the Euclidean space (Verified).** If `α > 0` and `g - α‖x‖²/2` is convex
on `EuclideanSpace ℝ (Fin d)`, then `π = volume.tilted (-g) ∝ e^{-g}` satisfies the log-Sobolev
inequality `Ent_π(φ²) ≤ (2/α) ∫ ‖∇φ‖² dπ` for every differentiable `φ` that is bounded, has
bounded Mathlib `gradient` and is bounded below by a positive constant. Proof: transfer to
`Fin d → ℝ` and apply `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`. -/
theorem ent_sq_le_of_stronglyLogConcave (hα : 0 < α)
    (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφd : Differentiable ℝ φ) (hφb : ∃ M, ∀ x, |φ x| ≤ M)
    (hφg : ∃ K, ∀ x, ‖gradient φ x‖ ≤ K) (hφc : ∃ c > 0, ∀ x, c ≤ φ x) :
    LogSobolev.ent ((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted fun x => -g x)
        (fun x => φ x ^ 2)
      ≤ 2 / α * ∫ x, ‖gradient φ x‖ ^ 2 ∂(volume.tilted fun x => -g x) := by
  have hLSI := BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn hα
    (convexOn_comp_toLp_sub_gaussPotentialPi hconv)
  rw [← map_ofLp_tilted g] at hLSI
  rw [div_eq_mul_one_div 2 α]
  exact ent_sq_le_of_functionalLSIPi hLSI hφd hφb hφg hφc

/-- If `α > 0` and `g - α‖x‖²/2` is convex on the Euclidean space, the proximal sampler
`proxKernelEuclid g η` is a Markov kernel for every `η > 0`. -/
theorem isMarkovKernel_proxKernelEuclid_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2) :
    IsMarkovKernel (proxKernelEuclid g η) := by
  have hconv' := convexOn_comp_toLp_sub_gaussPotentialPi hconv
  exact isMarkovKernel_proxKernelEuclid
    (measurable_comp_toLp_iff.1 (measurable_of_convexOn_sub_gaussPotentialPi hconv'))
    (integrable_comp_toLp_iff.1
      (ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi hα hconv').1) hη

/-- **PX-6 on the Euclidean space, one step (Verified).** If `α, η > 0` and `g - α‖x‖²/2` is
convex on `EuclideanSpace ℝ (Fin d)`, then for `π = volume.tilted (-g) ∝ e^{-g}` and every
probability law `ρ` with `KL(ρ‖π) < ∞`: `KL(proxKernelEuclid g η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelEuclid g η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernelEuclid_comp_le_sq_of_stronglyLogConcave (hα : 0 < α)
    (hη : 0 < η) (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (volume.tilted fun x => -g x) ≠ ⊤) :
    klDiv (proxKernelEuclid g η ∘ₘ ρ) (volume.tilted fun x => -g x) ≠ ⊤ ∧
      (klDiv (proxKernelEuclid g η ∘ₘ ρ) (volume.tilted fun x => -g x)).toReal
        ≤ (klDiv ρ (volume.tilted fun x => -g x)).toReal / (1 + α * η) ^ 2 := by
  have := isMarkovKernel_proxKernelEuclid_of_stronglyLogConcave hα hη hconv
  rw [klDiv_tilted_eq_klDiv_targetPi] at hKL ⊢
  rw [klDiv_tilted_eq_klDiv_targetPi, map_ofLp_proxKernelEuclid_comp g η]
  exact toReal_klDiv_proxKernelPi_comp_le_sq_of_stronglyLogConcave hα hη
    (convexOn_comp_toLp_sub_gaussPotentialPi hconv) (ρ.map ofLp) hKL

/-- **PX-6 on the Euclidean space, iterated (Verified).** If `α, η > 0`, `g - α‖x‖²/2` is
convex on `EuclideanSpace ℝ (Fin d)`, `π = volume.tilted (-g)` and
`ρ (k+1) = proxKernelEuclid g η ∘ₘ ρ k` from a probability law `ρ 0` with `KL(ρ 0‖π) < ∞`, then
every `ρ k` is a probability law, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iterateEuclid_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2)
    (ρ : ℕ → Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelEuclid g η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (volume.tilted fun x => -g x) ≠ ⊤) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (volume.tilted fun x => -g x) ≠ ⊤ ∧
      (klDiv (ρ k) (volume.tilted fun x => -g x)).toReal
        ≤ (klDiv (ρ 0) (volume.tilted fun x => -g x)).toReal / (1 + α * η) ^ (2 * k) := by
  have := isMarkovKernel_proxKernelEuclid_of_stronglyLogConcave hα hη hconv
  have hP : ∀ k, IsProbabilityMeasure (ρ k) := fun k => by
    induction k with
    | zero => infer_instance
    | succ k ih => rw [hstep k]; infer_instance
  have hstep' : ∀ k, (ρ (k + 1)).map ofLp =
      proxKernelPi (fun x => g (toLp 2 x)) η ∘ₘ (ρ k).map ofLp := fun k => by
    rw [hstep k, map_ofLp_proxKernelEuclid_comp g η]
  rw [klDiv_tilted_eq_klDiv_targetPi] at hKL
  obtain ⟨-, hne, hle⟩ :=
    toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave hα hη
      (convexOn_comp_toLp_sub_gaussPotentialPi hconv) (fun k => (ρ k).map ofLp) hstep' hKL k
  rw [klDiv_tilted_eq_klDiv_targetPi, klDiv_tilted_eq_klDiv_targetPi]
  exact ⟨hP k, hne, hle⟩

/-- **PX-6 on the Euclidean space, total variation (Verified).** Under the hypotheses of
`toReal_klDiv_iterateEuclid_le_sq_of_stronglyLogConcave`:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^(2k)))` for `π = volume.tilted (-g)`. -/
theorem tvSup_iterateEuclid_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => g x - α * ‖x‖ ^ 2 / 2)
    (ρ : ℕ → Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelEuclid g η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (volume.tilted fun x => -g x) ≠ ⊤) (k : ℕ) :
    TotalVariation.tvSup (ρ k) (volume.tilted fun x => -g x)
      ≤ √((klDiv (ρ 0) (volume.tilted fun x => -g x)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  have hstep' : ∀ k, (ρ (k + 1)).map ofLp =
      proxKernelPi (fun x => g (toLp 2 x)) η ∘ₘ (ρ k).map ofLp := fun k => by
    rw [hstep k, map_ofLp_proxKernelEuclid_comp g η]
  rw [klDiv_tilted_eq_klDiv_targetPi] at hKL ⊢
  rw [tvSup_tilted_eq_tvSup_targetPi]
  exact tvSupPi_iterate_le_sq_of_stronglyLogConcave hα hη
    (convexOn_comp_toLp_sub_gaussPotentialPi hconv) (fun k => (ρ k).map ofLp) hstep' hKL k

end FormalizeSampling.EuclideanTransfer
