module

public import FormalizeSampling.Samplers.ProximalGeneralLSIPi
public import FormalizeSampling.Foundations.BakryEmeryGeneralPi

/-!
# Sharp proximal-sampler rate for all strongly log-concave targets on `Fin d → ℝ`

Status: **Verified** (no named hypotheses).

Let `f : (Fin d → ℝ) → ℝ` with `f - α |x|²/2` convex (`α > 0`; no separability, smoothness or
measurability assumption), `π = targetPi f ∝ e^{-f}`, `η > 0`. Bakry–Émery
(`BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`, proved via Prékopa–Leindler and the
Bobkov–Ledoux argument) gives `FunctionalLSIPi π (1/α)`, strong convexity gives a Gaussian upper
envelope of `π` (`ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi`), and
`ProximalGeneralLSIPi` then gives, for every probability law `ρ₀` with `KL(ρ₀‖π) < ∞`, along the
exact proximal sampler `ρ_{k+1} = proxKernelPi f η ∘ₘ ρ_k`:
`KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + α η)^{2k}` and `TV(ρ_k, π) ≤ √(KL(ρ₀‖π) / (2 (1 + α η)^{2k}))`.

## Main results

* `measurable_of_convexOn_sub_gaussPotentialPi`: `f` is automatically measurable (indeed
  continuous) when `f - α|x|²/2` is convex on `Fin d → ℝ`.
* `functionalLSIPi_targetPi_of_stronglyLogConcave`: `FunctionalLSIPi (targetPi f) (1/α)`.
* `toReal_klDiv_proxKernelPi_comp_le_sq_of_stronglyLogConcave` (one step),
  `toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave` (iterates),
  `tvSupPi_iterate_le_sq_of_stronglyLogConcave` (total variation).

## Not proved here

* Merely log-concave targets (`α = 0`) or targets that are strongly log-concave only outside a
  bounded set (use Holley–Stroock, `GaussianFunctionalLSIPi.functionalLSIPi_tilt`, for bounded
  perturbations).
* Inexact restricted Gaussian oracles.
* Starts with `KL(ρ₀‖π) = ∞` (vacuous).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalStronglyLogConcaveGeneralPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.LogSobolevPi FormalizeSampling.ProximalGeneralLSIPi
open FormalizeSampling.BakryEmeryGeneralPi

variable {d : ℕ} {f : (Fin d → ℝ) → ℝ} {α η : ℝ}

/-- If `f - α|x|²/2` is convex on `Fin d → ℝ`, then `f` is measurable (alias of
`BakryEmeryGeneralPi.measurable_of_convexOn_sub`). -/
theorem measurable_of_convexOn_sub_gaussPotentialPi
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) : Measurable f :=
  BakryEmeryGeneralPi.measurable_of_convexOn_sub hconv

/-- **Bakry–Émery on `Fin d → ℝ` (Verified).** If `α > 0` and `f - α|x|²/2` is convex, then
`FunctionalLSIPi (targetPi f) (1/α)`. -/
theorem functionalLSIPi_targetPi_of_stronglyLogConcave (hα : 0 < α)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) :
    FunctionalLSIPi (targetPi f) (1 / α) :=
  functionalLSIPi_targetPi_of_convexOn hα hconv

/-- **Sharp PX-2 for strongly log-concave targets on `Fin d → ℝ`, one step (Verified).** If
`α, η > 0` and `f - α|x|²/2` is convex, then for `π = targetPi f` and every probability law `ρ`
with `KL(ρ‖π) < ∞`: `KL(proxKernelPi f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernelPi f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernelPi_comp_le_sq_of_stronglyLogConcave (hα : 0 < α)
    (hη : 0 < η) (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (targetPi f) ≠ ⊤) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f) ≠ ⊤ ∧
      (klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)).toReal
        ≤ (klDiv ρ (targetPi f)).toReal / (1 + α * η) ^ 2 := by
  obtain ⟨-, C₂, -, henv⟩ := exists_envelope_of_strongConvexPi hα hconv
  exact toReal_klDiv_proxKernelPi_comp_le_sq_general
    (measurable_of_convexOn_sub_gaussPotentialPi hconv) hα hη
    (functionalLSIPi_targetPi_of_stronglyLogConcave hα hconv) henv ρ hKL

/-- **Sharp PX-2 for strongly log-concave targets on `Fin d → ℝ`, iterated (Verified).** If
`α, η > 0`, `f - α|x|²/2` is convex and `ρ (k+1) = proxKernelPi f η ∘ₘ ρ k` from a probability
law `ρ 0` with `KL(ρ 0‖π) < ∞`, then every `ρ k` is a probability law, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (targetPi f) ≠ ⊤)
    (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (targetPi f) ≠ ⊤ ∧
      (klDiv (ρ k) (targetPi f)).toReal
        ≤ (klDiv (ρ 0) (targetPi f)).toReal / (1 + α * η) ^ (2 * k) := by
  obtain ⟨-, C₂, -, henv⟩ := exists_envelope_of_strongConvexPi hα hconv
  exact toReal_klDiv_iteratePi_le_sq_general (measurable_of_convexOn_sub_gaussPotentialPi hconv)
    hα hη (functionalLSIPi_targetPi_of_stronglyLogConcave hα hconv) henv ρ hstep hKL k

/-- **TV rate for strongly log-concave targets on `Fin d → ℝ` (Verified).** Under the
hypotheses of `toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave`:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^(2k)))`. -/
theorem tvSupPi_iterate_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (targetPi f) ≠ ⊤)
    (k : ℕ) :
    TotalVariation.tvSup (ρ k) (targetPi f)
      ≤ √((klDiv (ρ 0) (targetPi f)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨-, C₂, -, henv⟩ := exists_envelope_of_strongConvexPi hα hconv
  exact tvSupPi_iterate_le_sq_general (measurable_of_convexOn_sub_gaussPotentialPi hconv)
    hα hη (functionalLSIPi_targetPi_of_stronglyLogConcave hα hconv) henv ρ hstep hKL k

end FormalizeSampling.ProximalStronglyLogConcaveGeneralPi
