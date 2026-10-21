module

public import FormalizeSampling.Samplers.ProximalGeneralLSI
public import FormalizeSampling.Foundations.BakryEmery

/-!
# Sharp proximal-sampler rate for strongly log-concave targets (1D, unconditional)

Status: **Verified** (dimension one; no named hypotheses).

Let `f : ℝ → ℝ` with `f - α x²/2` convex (`α > 0`, i.e. `π = target f ∝ e^{-f}` is
`α`-strongly log-concave) and `η > 0`. Bakry–Émery (`BakryEmery`, via the 1D Caffarelli
contraction) gives `FunctionalLSI π (1/α)`, strong convexity gives a Gaussian upper envelope of
`π` (`ProximalGeneralLSI.exists_envelope_of_strongConvex`), and `ProximalGeneralLSI` then gives,
for every
probability law `ρ₀` with `KL(ρ₀‖π) < ∞`, along the exact proximal sampler
`ρ_{k+1} = ρ_k P_prox`:
`KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + α η)^{2k}` and `TV(ρ_k, π) ≤ √(KL(ρ₀‖π) / (2 (1 + α η)^{2k}))`.
No measurability, integrability or LSI hypothesis on `f` is needed: continuity of `f` and
`∫ e^{-f} < ∞` follow from strong convexity.

## Main results

* `measurable_of_convexOn_sub_gaussPotential`: `f - α x²/2` convex ⇒ `f` measurable.
* `toReal_klDiv_proxKernel_comp_le_sq_of_stronglyLogConcave` (one step).
* `toReal_klDiv_iterate_le_sq_of_stronglyLogConcave` (iterates).
* `tvSup_iterate_le_sq_of_stronglyLogConcave` (total variation).

## Not proved here

* The `d`-dimensional version is not proved here: it is
  `ProximalStronglyLogConcaveGeneralPi` (Bakry–Émery via
  `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`; no separability needed).
* Starts with `KL(ρ₀‖π) = ∞` (vacuous).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalStronglyLogConcave

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp FormalizeSampling.LogSobolev
open FormalizeSampling.ProximalGeneralLSI FormalizeSampling.BakryEmery

variable {f : ℝ → ℝ} {α η : ℝ}

/-- `f - gaussPotential α` convex iff `f - α x²/2` convex (the two conventions agree). -/
theorem convexOn_sub_iff :
    (ConvexOn ℝ univ fun x => f x - gaussPotential α x) ↔
      ConvexOn ℝ univ fun x => f x - α / 2 * x ^ 2 := by
  have : (fun x => f x - gaussPotential α x) = fun x => f x - α / 2 * x ^ 2 := by
    funext x; unfold gaussPotential; ring
  rw [this]

/-- If `f - gaussPotential α` is convex, then `f` is continuous, hence measurable. -/
theorem measurable_of_convexOn_sub_gaussPotential
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotential α x) : Measurable f :=
  (continuous_of_convexOn_sub (convexOn_sub_iff.1 hconv)).measurable

/-- **Sharp PX-2 for strongly log-concave targets, one step (Verified).** If `α, η > 0` and
`f - α x²/2` is convex, then for every probability law `ρ` with `KL(ρ‖π) < ∞`
(`π = target f`): `KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)²`. -/
theorem toReal_klDiv_proxKernel_comp_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotential α x)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target f) ≠ ⊤) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ⊤ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) ^ 2 := by
  obtain ⟨-, C₂, -, henv⟩ := exists_envelope_of_strongConvex hα hconv
  exact toReal_klDiv_proxKernel_comp_le_sq_general (measurable_of_convexOn_sub_gaussPotential hconv)
    hα hη (functionalLSI_target_of_convexOn_sub_gaussPotential hα hconv) henv ρ hKL

/-- **Sharp PX-2 for strongly log-concave targets, iterated (Verified).** If `α, η > 0`,
`f - α x²/2` is convex, `ρ_{k+1} = proxKernel f η ∘ₘ ρ_k` and `KL(ρ₀‖π) < ∞`, then for all `k`:
`ρ_k` is a probability measure, `KL(ρ_k‖π) < ∞` and
`KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + α η)^{2k}`. -/
theorem toReal_klDiv_iterate_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotential α x)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ⊤)
    (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (target f) ≠ ⊤ ∧
      (klDiv (ρ k) (target f)).toReal
        ≤ (klDiv (ρ 0) (target f)).toReal / (1 + α * η) ^ (2 * k) := by
  obtain ⟨-, C₂, -, henv⟩ := exists_envelope_of_strongConvex hα hconv
  exact toReal_klDiv_iterate_le_sq_general (measurable_of_convexOn_sub_gaussPotential hconv)
    hα hη (functionalLSI_target_of_convexOn_sub_gaussPotential hα hconv) henv ρ hstep hKL k

/-- **Sharp PX-2 for strongly log-concave targets in total variation (Verified).** Under the
hypotheses of `toReal_klDiv_iterate_le_sq_of_stronglyLogConcave`,
`TV(ρ_k, π) ≤ √(KL(ρ₀‖π) / (2 (1 + α η)^{2k}))`. -/
theorem tvSup_iterate_le_sq_of_stronglyLogConcave (hα : 0 < α) (hη : 0 < η)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotential α x)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ⊤)
    (k : ℕ) :
    TotalVariation.tvSup (ρ k) (target f)
      ≤ √((klDiv (ρ 0) (target f)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨-, C₂, -, henv⟩ := exists_envelope_of_strongConvex hα hconv
  exact tvSup_iterate_le_sq_general (measurable_of_convexOn_sub_gaussPotential hconv)
    hα hη (functionalLSI_target_of_convexOn_sub_gaussPotential hα hconv) henv ρ hstep hKL k

end FormalizeSampling.ProximalStronglyLogConcave
