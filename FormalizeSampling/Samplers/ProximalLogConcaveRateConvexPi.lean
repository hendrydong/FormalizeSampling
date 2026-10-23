module

public import FormalizeSampling.Samplers.RGOCouplingLangevin
public import FormalizeSampling.Samplers.RGOCouplingApprox

/-!
# The `1/k` KL rate of the proximal sampler for every log-concave target on `Fin d → ℝ`

Status: **Verified** (no named hypotheses).

Setting: target `π = targetPi f ∝ e^{-f}` on `Fin d → ℝ` with `f` convex and `∫ e^{-f} < ∞`,
step `η > 0` (variance of the forward Gaussian), iterates `ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k`
and a finite coupling `γ₀` of `(ρ 0, π)`.

## Main results

* `hasWeakCoupling_rgoKernelPi_of_convexOn`: for convex `f` and `η > 0` the RGO kernel has a
  weak contractive coupling (`RGOCouplingWeak.HasWeakCoupling`). Proof: approximate `f` by
  smooth convex potentials with bounded derivatives (`Samplers/RGOCouplingApprox`), couple
  their RGO kernels through synchronous Euler–Maruyama chains of the Langevin dynamics that
  leave them invariant (`Samplers/RGOCouplingLangevin`), and pass to the limit
  (`RGOCouplingWeak.hasWeakCoupling_of_tendsto`).
* `klDiv_iteratePi_le_div_of_convexOn` (**main theorem**): for every `k`,
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`.

The `1/k` rate is that of Chen–Chewi–Salim–Wibisono (2022, Thm 2); the constant `1/(2(k+1)η)`
is the one the shifted-composition argument of Altschuler–Chewi (2023, Thm 3.2) gives
(`RGOCouplingWeak.klDiv_iterate_le_shifted_of_weak`), as in the log-concave case of Pedrotti
(2026, arXiv:2601.13259, Cor. 3.5).

## Not proved here

* The infimum over couplings (the Wasserstein distance itself) is not formed.
* Non-convex targets.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcaveRatePi
open FormalizeSampling.RGOCouplingWeak
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcaveRateConvexPi

variable {d : ℕ}

/-- **Weak contractive coupling of the RGO for convex potentials.** For `f` convex on
`Fin d → ℝ` and `η > 0`, the RGO kernel `rgoKernelPi f η` has a weak contractive coupling. -/
theorem hasWeakCoupling_rgoKernelPi_of_convexOn {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ univ f) {η : ℝ} (hη : 0 < η) : HasWeakCoupling (rgoKernelPi f η) := by
  obtain ⟨g, hg, hlim⟩ := exists_smoothConvexBdd_tendsto_rgoKernelPi hf hη
  have : ∀ n, IsMarkovKernel (rgoKernelPi (g n) η) := fun n =>
    isMarkovKernel_rgoKernelPi_of_convexOn (hg n).1 hη
  have := isMarkovKernel_rgoKernelPi_of_convexOn hf hη
  exact hasWeakCoupling_of_tendsto
    (fun n => hasWeakCoupling_rgoKernelPi_of_smoothConvexBdd (hg n) hη) hlim

/-- **`1/k` KL rate of the proximal sampler for log-concave targets on `Fin d → ℝ`.** Let
`f : (Fin d → ℝ) → ℝ` be convex with `∫ e^{-f} < ∞`, `π = targetPi f`, `η > 0`,
`ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k`, and `γ₀` a finite coupling of `(ρ 0, π)`. Then for
every `k`: `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)` (Euclidean
distance). -/
theorem klDiv_iteratePi_le_div_of_convexOn {f : (Fin d → ℝ) → ℝ} (hf : ConvexOn ℝ univ f)
    (hint : Integrable fun x => Real.exp (-f x)) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi f)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * ((k : ℝ) + 1) * η)) ∂γ₀ :=
  klDiv_iteratePi_le_div_of_hasWeakCoupling
    (ConvexSmoothing.continuous_of_convexOn hf).measurable hint hη
    (hasWeakCoupling_rgoKernelPi_of_convexOn hf hη) ρ hstep γ₀ h₁ h₂ k

end FormalizeSampling.ProximalLogConcaveRateConvexPi
