module

public import FormalizeSampling.Samplers.RGOCouplingQuadraticPi
public import FormalizeSampling.Samplers.RGOCouplingWeak

/-!
# The `1/k` KL rate of the proximal sampler from a pathwise Lipschitz RGO representation

Status: **Verified** (no named hypotheses).

Setting: target `π = targetPi f ∝ e^{-f}` on `Fin d → ℝ` (`f` measurable, `∫ e^{-f} < ∞`),
step `η > 0` (variance of the forward Gaussian), iterates `ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k`
and a finite coupling `γ₀` of `(ρ 0, π)`.

## Main results

* `repCoupling`, `map_comp_repCoupling`: the synchronous coupling kernel
  `(a, b) ↦ law of (G(a, ω), G(b, ω))` of a representation `(Ω, P, G)` and its marginals.
* `RGOCouplingWeak.hasWeakCoupling_of_hasLipRep`: a pathwise `1`-Lipschitz representation
  (`RGOCouplingPi.HasLipRep`) gives a weak contractive coupling (`RGOCouplingWeak.HasWeakCoupling`).
* `klDiv_iteratePi_le_div_of_hasLipRep` (**main theorem**): if the RGO kernel
  `rgoKernelPi f η` has a pathwise `1`-Lipschitz representation, then for every `k`:
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`. No convexity is assumed beyond
  what is needed for `HasLipRep`. It is the weak-coupling theorem
  `RGOCouplingWeak.klDiv_iteratePi_le_div_of_hasWeakCoupling` applied to the synchronous coupling.

Instances of `HasLipRep` for RGO kernels: separable convex potentials
(`RGOCouplingPi.hasLipRep_rgoKernelPi_separable`) and separable plus positive semidefinite
quadratic potentials (`Samplers/RGOCouplingQuadraticPi.lean`).

## Not proved here

* `HasLipRep (rgoKernelPi f η)` for a **general** convex `f` on `Fin d → ℝ`. It is not needed:
  the shifted-composition argument only uses a weak contractive coupling
  (`RGOCouplingWeak.HasWeakCoupling`), which holds for every convex `f`; the `1/k` rate for
  every log-concave target is `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn`.
* Statements about the Wasserstein distance as an infimum over couplings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix
open FormalizeSampling.Proximal FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcave
open FormalizeSampling.ProximalLogConcavePi FormalizeSampling.ProximalLogConcaveRatePi
open FormalizeSampling.RGOCouplingPi FormalizeSampling.RGOCouplingQuadraticPi
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcaveRateGeneralPi

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- For jointly measurable `G`, each section `G y` is measurable. -/
theorem measurable_section {G : (Fin d → ℝ) → Ω → Fin d → ℝ}
    (hG : Measurable (Function.uncurry G)) (y : Fin d → ℝ) : Measurable (G y) :=
  hG.comp measurable_prodMk_left

/-- For jointly measurable `G`, `ω ↦ (G a ω, G b ω)` is measurable. -/
theorem measurable_pairSection {G : (Fin d → ℝ) → Ω → Fin d → ℝ}
    (hG : Measurable (Function.uncurry G)) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    Measurable fun ω => (G p.1 ω, G p.2 ω) :=
  (measurable_section hG p.1).prodMk (measurable_section hG p.2)

/-- The synchronous coupling kernel of a representation `(Ω, P, G)`:
`(a, b) ↦ law of (G(a, ω), G(b, ω))`, `ω ∼ P`. -/
noncomputable def repCoupling (P : Measure Ω) [IsProbabilityMeasure P]
    {G : (Fin d → ℝ) → Ω → Fin d → ℝ}
    (hG : Measurable (Function.uncurry G)) :
    Kernel ((Fin d → ℝ) × (Fin d → ℝ)) ((Fin d → ℝ) × (Fin d → ℝ)) where
  toFun p := P.map fun ω => (G p.1 ω, G p.2 ω)
  measurable' := by
    have hg : Measurable fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × Ω =>
        (G q.1.1 q.2, G q.1.2 q.2) :=
      (hG.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
        (hG.comp (measurable_fst.snd.prodMk measurable_snd))
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have := measurable_measure_prodMk_left (ν := P) (hg hs)
    convert this using 1
    funext p
    rw [Measure.map_apply (measurable_pairSection hG p) hs]
    rfl

/-- Evaluation of the synchronous coupling kernel. -/
theorem repCoupling_apply (P : Measure Ω) [IsProbabilityMeasure P] {G : (Fin d → ℝ) → Ω → Fin d → ℝ}
    (hG : Measurable (Function.uncurry G)) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    repCoupling P hG p = P.map fun ω => (G p.1 ω, G p.2 ω) := rfl

/-- The synchronous coupling kernel is a Markov kernel. -/
instance isMarkovKernel_repCoupling (P : Measure Ω) [IsProbabilityMeasure P]
    {G : (Fin d → ℝ) → Ω → Fin d → ℝ} (hG : Measurable (Function.uncurry G)) :
    IsMarkovKernel (repCoupling P hG) :=
  ⟨fun p => by
    rw [repCoupling_apply]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pairSection hG p).aemeasurable).2
      inferInstance⟩

/-- **Marginals of the synchronous coupling.** If `G(y, ·)_# P = K y`, then for every finite
`μ` on `(Fin d → ℝ)²`: `(repCoupling ∘ₘ μ).map fst = K ∘ₘ μ.map fst` and similarly for
`snd`. -/
theorem map_comp_repCoupling (P : Measure Ω) [IsProbabilityMeasure P]
    {G : (Fin d → ℝ) → Ω → Fin d → ℝ} (hG : Measurable (Function.uncurry G))
    (K : Kernel (Fin d → ℝ) (Fin d → ℝ)) (hK : ∀ y, P.map (G y) = K y)
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) :
    (repCoupling P hG ∘ₘ μ).map Prod.fst = K ∘ₘ μ.map Prod.fst ∧
      (repCoupling P hG ∘ₘ μ).map Prod.snd = K ∘ₘ μ.map Prod.snd := by
  constructor
  · ext s hs
    rw [Measure.map_apply measurable_fst hs, Measure.bind_apply (measurable_fst hs)
      (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_map (K.measurable_coe hs) measurable_fst]
    refine lintegral_congr fun p => ?_
    rw [repCoupling_apply, Measure.map_apply (measurable_pairSection hG p) (measurable_fst hs),
      ← hK, Measure.map_apply (measurable_section hG _) hs]
    rfl
  · ext s hs
    rw [Measure.map_apply measurable_snd hs, Measure.bind_apply (measurable_snd hs)
      (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_map (K.measurable_coe hs) measurable_snd]
    refine lintegral_congr fun p => ?_
    rw [repCoupling_apply, Measure.map_apply (measurable_pairSection hG p) (measurable_snd hs),
      ← hK, Measure.map_apply (measurable_section hG _) hs]
    rfl

end FormalizeSampling.ProximalLogConcaveRateGeneralPi

namespace FormalizeSampling.RGOCouplingWeak

open FormalizeSampling.ProximalLogConcaveRateGeneralPi

variable {d : ℕ}

/-- **Pathwise representations give weak couplings.** If the kernel `K` on `Fin d → ℝ` has a
pathwise `1`-Lipschitz representation (`RGOCouplingPi.HasLipRep`), then `HasWeakCoupling K`
(push `μ, ν` through the synchronous coupling kernel). -/
theorem hasWeakCoupling_of_hasLipRep {K : Kernel (Fin d → ℝ) (Fin d → ℝ)}
    (h : HasLipRep K) : HasWeakCoupling K := by
  obtain ⟨Ω, _, P, G, hP, hG, hK, hlip⟩ := h
  intro μ ν _ _
  refine ⟨repCoupling P hG ∘ₘ μ, repCoupling P hG ∘ₘ ν, inferInstance, inferInstance,
    (map_comp_repCoupling P hG K hK μ).1, (map_comp_repCoupling P hG K hK μ).2,
    (map_comp_repCoupling P hG K hK ν).1, (map_comp_repCoupling P hG K hK ν).2,
    klDiv_comp_right_le _ _ _, ?_⟩
  unfold sqCostPi
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) measurable_ofReal_sqDist.aemeasurable]
  refine lintegral_mono fun p => ?_
  rw [repCoupling_apply, lintegral_map measurable_ofReal_sqDist (measurable_pairSection hG _)]
  calc ∫⁻ ω, ENNReal.ofReal (sqDist (G p.1 ω) (G p.2 ω)) ∂P
      ≤ ∫⁻ _ω, ENNReal.ofReal (sqDist p.1 p.2) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hlip _ _ ω)
    _ = ENNReal.ofReal (sqDist p.1 p.2) := by rw [lintegral_const, measure_univ, mul_one]

end FormalizeSampling.RGOCouplingWeak

namespace FormalizeSampling.ProximalLogConcaveRateGeneralPi

variable {d : ℕ}

/-- **`1/k` KL rate of the proximal sampler from a pathwise Lipschitz RGO.** Let
`f : (Fin d → ℝ) → ℝ` be measurable with `∫ e^{-f} < ∞`, `π = targetPi f`, `η > 0`, and assume
the RGO kernel `rgoKernelPi f η` has a pathwise `1`-Lipschitz representation. Let
`ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k` and `γ₀` be any finite coupling of `(ρ 0, π)`. Then for
every `k`: `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`. This is
`RGOCouplingWeak.klDiv_iteratePi_le_div_of_hasWeakCoupling` with the weak coupling of
`RGOCouplingWeak.hasWeakCoupling_of_hasLipRep`. -/
theorem klDiv_iteratePi_le_div_of_hasLipRep {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable fun x => Real.exp (-f x)) {η : ℝ} (hη : 0 < η)
    (hrep : HasLipRep (rgoKernelPi f η))
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi f)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * ((k : ℝ) + 1) * η)) ∂γ₀ :=
  RGOCouplingWeak.klDiv_iteratePi_le_div_of_hasWeakCoupling hf hint hη
    (RGOCouplingWeak.hasWeakCoupling_of_hasLipRep hrep) ρ hstep γ₀ h₁ h₂ k

end FormalizeSampling.ProximalLogConcaveRateGeneralPi
