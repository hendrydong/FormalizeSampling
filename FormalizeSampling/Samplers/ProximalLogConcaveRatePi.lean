module

public import FormalizeSampling.Samplers.ProximalLogConcavePi
public import FormalizeSampling.Samplers.ProximalLogConcaveRateConvexPi

/-!
# The `1/k` KL rate of the proximal sampler on `Fin d → ℝ` for separable log-concave targets

Status: **Verified** (no named hypotheses).

Setting (as in `Samplers/ProximalLogConcavePi.lean`): target `π = targetPi f ∝ e^{-f}` on
`Fin d → ℝ` with a **separable convex** potential `f x = ∑ᵢ gᵢ(xᵢ)` (`gᵢ` convex on `ℝ`,
`∫ e^{-gᵢ} < ∞`), step `η > 0` (the **variance** of the forward Gaussian), iterates
`ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k`, and a finite coupling `γ₀` of `(ρ 0, π)`.

## Main results

* `klDiv_iteratePi_le_div` (**main theorem**): for every `k`,
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`.

A separable sum of convex functions is convex and `∫ e^{-f} < ∞`
(`ProximalLogConcavePi.integrable_exp_neg_sum`), so this is the case `f = ∑ᵢ gᵢ(xᵢ)` of the
rate for every log-concave target,
`ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn`.
The quadratic transport cost `sqCostPi` used throughout the `Fin d → ℝ` development is in
`Samplers/ShiftedCompositionPi.lean`.

## Not proved here

* Statements about the Wasserstein distance as an infimum over couplings.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.ProximalPi
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcaveRatePi

variable {d : ℕ}

/-- **`1/k` KL rate of the proximal sampler for a separable log-concave target on `Fin d → ℝ`.**
Let `f x = ∑ᵢ gᵢ(xᵢ)` with each `gᵢ` convex on `ℝ` and `∫ e^{-gᵢ} < ∞`, `π = targetPi f`,
`η > 0`, `ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k`, and `γ₀` any finite coupling of `(ρ 0, π)`.
Then for every `k`: `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`. -/
theorem klDiv_iteratePi_le_div {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x)) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi f)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * ((k : ℝ) + 1) * η)) ∂γ₀ := by
  have hf : ConvexOn ℝ univ f := by
    rw [show f = fun x => ∑ i, g i (x i) from funext hfg]
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => (hconv i).2 (mem_univ _) (mem_univ _) ha hb hab
  exact ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn hf
    (ProximalLogConcavePi.integrable_exp_neg_sum hfg hint) hη ρ hstep γ₀ h₁ h₂ k

end FormalizeSampling.ProximalLogConcaveRatePi
