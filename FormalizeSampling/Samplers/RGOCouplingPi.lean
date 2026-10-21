module

public import FormalizeSampling.Samplers.ProximalLogConcavePi

/-!
# Pathwise `1`-Lipschitz representations of kernels on `Fin d → ℝ`

Status: **Verified** (no named hypotheses).

A pathwise proof of the `1/k` KL rate of the proximal sampler
(`Samplers/ProximalLogConcaveRateGeneralPi.lean`) only uses one property of the restricted
Gaussian oracle `y ↦ RGO(y)`: it admits a **pathwise `1`-Lipschitz representation**, i.e. a
probability space `(Ω, P)` and a jointly measurable `G : (Fin d → ℝ) → Ω → Fin d → ℝ` with
`G(y, ·)_# P = RGO(y)` for every `y` and `|G(y, ω) - G(y', ω)| ≤ |y - y'|` (Euclidean) for all
`y, y', ω`. This file isolates that interface (`HasLipRep`).

## Main results

* `HasLipRep`: the interface above, for a kernel `K` on `Fin d → ℝ`.
* `hasLipRep_pi`: product kernels `K y = ⊗ᵢ κᵢ (yᵢ)` with CDF-shift-monotone `κᵢ` (the
  coordinatewise quantile map with a common uniform vector).
* `hasLipRep_rgoKernelPi_separable`: the RGO kernel of a separable convex potential
  `f x = ∑ᵢ gᵢ(xᵢ)` (`∫ e^{-gᵢ} < ∞`).

## Not proved here

* A pathwise representation for the RGO kernel of a **general** convex potential; see
  `Samplers/RGOCouplingQuadraticPi.lean` for separable potentials plus a positive semidefinite
  quadratic form, and the weak coupling
  `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn`, which suffices for the
  `1/k` rate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open FormalizeSampling.Proximal FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcave
open FormalizeSampling.ProximalLogConcavePi
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingPi

variable {d : ℕ}

/-- **Pathwise `1`-Lipschitz representation.** A kernel `K` on `Fin d → ℝ` has a pathwise
`1`-Lipschitz representation if there are a probability space `(Ω, P)` and a jointly measurable
`G : (Fin d → ℝ) → Ω → Fin d → ℝ` such that `G(y, ·)_# P = K y` for every `y` and
`|G(y, ω) - G(y', ω)|² ≤ |y - y'|²` (Euclidean) for all `y, y', ω`. -/
def HasLipRep (K : Kernel (Fin d → ℝ) (Fin d → ℝ)) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (G : (Fin d → ℝ) → Ω → Fin d → ℝ),
    IsProbabilityMeasure P ∧ Measurable (Function.uncurry G) ∧ (∀ y, P.map (G y) = K y) ∧
      ∀ y y' ω, sqDist (G y ω) (G y' ω) ≤ sqDist y y'

/-- **Product kernels.** If `K y = ⊗ᵢ κᵢ (yᵢ)` with each `κᵢ` a CDF-shift-monotone Markov
kernel on `ℝ`, then `K` has a pathwise `1`-Lipschitz representation (the coordinatewise
quantile map `qfPi κ` with a common uniform vector). -/
theorem hasLipRep_pi (κ : Fin d → Kernel ℝ ℝ) [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, CDFShiftMonotone (κ i)) (K : Kernel (Fin d → ℝ) (Fin d → ℝ))
    (hK : ∀ y, K y = Measure.pi fun i => κ i (y i)) : HasLipRep K :=
  ⟨Fin d → ℝ, inferInstance, unifPi, qfPi κ, inferInstance, measurable_qfPi κ,
    fun y => by rw [map_qfPi, hK], fun y y' u => sqDist_qfPi_le hκ y y' u⟩

/-- **Separable convex potentials.** If `f x = ∑ᵢ gᵢ(xᵢ)` with each `gᵢ` convex on `ℝ` and
`∫ e^{-gᵢ} < ∞`, and `η > 0`, then the RGO kernel `rgoKernelPi f η` has a pathwise
`1`-Lipschitz representation. -/
theorem hasLipRep_rgoKernelPi_separable {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, MeasureTheory.Integrable fun x => Real.exp (-g i x)) {η : ℝ} (hη : 0 < η) :
    HasLipRep (rgoKernelPi f η) := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have := fun i => isMarkovKernel_rgoKernel (hg i) (hint i) hη
  exact hasLipRep_pi (fun i => rgoKernel (g i) η)
    (fun i => cdfShiftMonotone_rgoKernel (hconv i) (hint i) hη) _
    (rgoKernelPi_eq_pi hfg hg hint hη)

end FormalizeSampling.RGOCouplingPi
