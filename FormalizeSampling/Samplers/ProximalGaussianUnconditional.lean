module

public import FormalizeSampling.Samplers.ProximalStronglyLogConcave
public import FormalizeSampling.Samplers.ProximalStronglyLogConcaveGeneralPi

/-!
# PX-3: sharp PX-2 rate for Gaussian targets

Status: **Verified**.

The isotropic Gaussian target `π = N(0, α⁻¹ I)`, i.e. `f(x) = α ‖x‖²/2`, is the case
`f - α ‖x‖²/2 ≡ 0` of the strongly log-concave theorems (PX-6, `ProximalStronglyLogConcave` and
`ProximalStronglyLogConcaveGeneralPi`). For every initial law `ρ₀` with `KL(ρ₀‖π) < ∞` (no
moment hypothesis) the exact proximal chain satisfies
`KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + α η)^{2k}`, in dimension one and on `Fin d → ℝ`. No smaller rate
holds (EX-3: `ProximalSharp.not_exists_rate_lt`, `ProximalSharpPi.not_exists_rate_lt_pi`).

## Main results

* `toReal_klDiv_iterate_le_sq_of_ne_top` (dimension one) and
  `toReal_klDiv_iteratePi_le_sq_of_ne_top` (`Fin d → ℝ`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalGaussianUnconditional

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp

/-! ### Dimension one -/

/-- **PX-3 (sharp PX-2 rate for the Gaussian target), all iterates (dimension one).** For
`α, η > 0`, `f(x) = α x²/2`, `π = target f = N(0, 1/α)`, the proximal chain
`ρ (k+1) = proxKernel f η ∘ₘ ρ k` and a probability law `ρ 0` with `KL(ρ 0‖π) < ∞` (no second
moment assumed): for every `k`, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. This is the PX-6 theorem
`ProximalStronglyLogConcave.toReal_klDiv_iterate_le_sq_of_stronglyLogConcave` with
`f - α x²/2 ≡ 0`. -/
theorem toReal_klDiv_iterate_le_sq_of_ne_top {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel (gaussPotential α) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (target (gaussPotential α)) ≠ ∞) (k : ℕ) :
    klDiv (ρ k) (target (gaussPotential α)) ≠ ∞ ∧
      (klDiv (ρ k) (target (gaussPotential α))).toReal
        ≤ (klDiv (ρ 0) (target (gaussPotential α))).toReal / (1 + α * η) ^ (2 * k) :=
  (ProximalStronglyLogConcave.toReal_klDiv_iterate_le_sq_of_stronglyLogConcave hα hη
    (by simpa using convexOn_const (0 : ℝ) convex_univ) ρ hstep hKL k).2

/-! ### Dimension `d` -/

section Pi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi

variable {d : ℕ}

/-- **PX-3 (sharp PX-2 rate for the isotropic Gaussian target), all iterates (`Fin d → ℝ`).**
For `α, η > 0`, `f(x) = α (∑ᵢ xᵢ²)/2`, `π = targetPi f = N(0, α⁻¹ I)`, the chain
`ρ (k+1) = proxKernelPi f η ∘ₘ ρ k` and a probability law `ρ 0` with `KL(ρ 0‖π) < ∞` (no second
moment assumed): for every `k`, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. This is the PX-6 theorem
`ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave` with
`f - α ‖x‖²/2 ≡ 0`. -/
theorem toReal_klDiv_iteratePi_le_sq_of_ne_top {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (gaussPotentialPi α) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (targetPi (gaussPotentialPi α)) ≠ ∞) (k : ℕ) :
    klDiv (ρ k) (targetPi (gaussPotentialPi α)) ≠ ∞ ∧
      (klDiv (ρ k) (targetPi (gaussPotentialPi α))).toReal
        ≤ (klDiv (ρ 0) (targetPi (gaussPotentialPi α))).toReal / (1 + α * η) ^ (2 * k) :=
  (ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave hα hη
    (by simpa using convexOn_const (0 : ℝ) convex_univ) ρ hstep hKL k).2

end Pi

end FormalizeSampling.ProximalGaussianUnconditional
