module

public import FormalizeSampling.Samplers.ProximalStronglyLogConcaveGeneralPi

/-!
# Bounded perturbations of a proximal target with an LSI and a Gaussian envelope

Status: **Conditional** only on the functional LSI of the unperturbed target in the general
form; **Verified** for strongly log-concave unperturbed targets (no named hypotheses).

Setting on `Fin d → ℝ`: potentials `f₀` and `f₀ + W`, targets `π₀ = targetPi f₀ ∝ e^{-f₀}` and
`π = targetPi (f₀ + W)`, with `W` measurable. The final form of PX-2
(`ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general`) needs a functional LSI and a
Gaussian upper envelope of `π`; both transfer from `π₀`:
* the envelope survives a perturbation bounded **below** (`a ≤ W`): `π ≤ e^{-a} (Z₀ / Z) • π₀`
  (`HeatFlowRegularityPerturbedPi.targetPi_add_le_smul_targetPi`, `Z₀`, `Z` the normalisers);
* the LSI survives a perturbation bounded on both sides (`a ≤ W ≤ b`), with the constant
  multiplied by `e^{b - a}` (Holley–Stroock, `GaussianFunctionalLSIPi.functionalLSIPi_tilt`,
  through `π = tilt π₀ W`).

PX-4 is the case `f₀ = α |x|²/2`; here `f₀` is any potential with an LSI and an envelope, for
example a strongly log-concave one (`f₀ - α |x|²/2` convex), which makes `f₀ + W` a
non-log-concave target in general.

## Main results

* `exists_envelope_add_of_le`: `π₀ ≤ C₂ • G` (any measure `G`) and `W ≥ a` give
  `∫ e^{-(f₀ + W)} < ∞` and `π ≤ C₂' • G` for some `C₂' ≥ 0`.
* `functionalLSIPi_targetPi_add`: `FunctionalLSIPi π₀ C`, `C ≥ 0`, `a ≤ W ≤ b` give
  `FunctionalLSIPi π (C e^{b - a})`.
* `toReal_klDiv_iteratePi_le_sq_add`: with `FunctionalLSIPi π₀ (1/α)` and
  `π₀ ≤ C₂ • N(0, v I)`, the exact proximal sampler for `π` from any `ρ₀` with
  `KL(ρ₀‖π) < ∞` satisfies `KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + α' η)^{2k}`, `α' = α e^{-(b-a)}`.
* `toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave_add`: the same for strongly log-concave
  `f₀` (Bakry–Émery and the envelope of strong convexity; no named hypotheses).

## Not proved here

* Optimality of `α' = α e^{-(b-a)}` (the Holley–Stroock constant) and unbounded perturbations.
* Starts with `KL(ρ₀‖π) = ∞` (vacuous).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalPerturbedGeneralPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.LogSobolevPi FormalizeSampling.ProximalGeneralLSIPi
open FormalizeSampling.HeatFlowRegularityPerturbedPi

variable {d : ℕ} {f₀ W : (Fin d → ℝ) → ℝ} {a b : ℝ}

/-- **The upper envelope survives a perturbation bounded below.** Let `f₀` be measurable with
`∫ e^{-f₀} < ∞`, `W` measurable with `a ≤ W`, and `targetPi f₀ ≤ C₂ • G` for a measure `G` (for
example `G = N(0, v I)`) and a real `C₂`. Then `∫ e^{-(f₀ + W)} < ∞` and
`targetPi (f₀ + W) ≤ C₂' • G` for some `C₂' ≥ 0` (one can take
`C₂' = e^{-a} (Z₀ / Z) max C₂ 0` with `Z₀`, `Z` the normalisers of `f₀`, `f₀ + W`). No upper
bound on `W` is needed. -/
theorem exists_envelope_add_of_le (hf₀ : Measurable f₀)
    (hint : Integrable (fun x => Real.exp (-f₀ x))) (hW : Measurable W) (ha : ∀ x, a ≤ W x)
    {G : Measure (Fin d → ℝ)} {C₂ : ℝ} (henv : targetPi f₀ ≤ ENNReal.ofReal C₂ • G) :
    Integrable (fun x => Real.exp (-(f₀ x + W x))) ∧ ∃ C₂' : ℝ, 0 ≤ C₂' ∧
      targetPi (fun x => f₀ x + W x) ≤ ENNReal.ofReal C₂' • G := by
  have hint' := integrable_exp_neg_add hf₀ hint hW ha
  set c := Real.exp (-a) * targetNormalizerPi f₀ / targetNormalizerPi fun x => f₀ x + W x
  have hc : 0 ≤ c := by
    have := targetNormalizerPi_pos hint
    have := targetNormalizerPi_pos hint'
    positivity
  refine ⟨hint', c * max C₂ 0, mul_nonneg hc (le_max_right C₂ 0),
    (targetPi_add_le_smul_targetPi hint hint' ha).trans ?_⟩
  rw [ENNReal.ofReal_mul hc, mul_smul, ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_left zero_le]
  gcongr

/-- **The functional LSI survives a bounded perturbation (Holley–Stroock).** Let `f₀` be
measurable with `∫ e^{-f₀} < ∞`, `FunctionalLSIPi (targetPi f₀) C` with `C ≥ 0`, and `W`
measurable with `a ≤ W ≤ b`. Then `FunctionalLSIPi (targetPi (f₀ + W)) (C e^{b - a})`. -/
theorem functionalLSIPi_targetPi_add (hf₀ : Measurable f₀)
    (hint : Integrable (fun x => Real.exp (-f₀ x))) {C : ℝ}
    (hLSI : FunctionalLSIPi (targetPi f₀) C) (hC : 0 ≤ C) (hW : Measurable W)
    (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) :
    FunctionalLSIPi (targetPi fun x => f₀ x + W x) (C * Real.exp (b - a)) := by
  have := isProbabilityMeasure_targetPi hint
  rw [GaussianFunctionalLSIPi.targetPi_add_eq_tilt hf₀ hW hint]
  exact GaussianFunctionalLSIPi.functionalLSIPi_tilt hLSI hC hW ha hb

/-- **PX-2 for a bounded perturbation of an LSI target with a Gaussian envelope (Conditional
only on the LSI of `targetPi f₀`).** Let `f₀` be measurable with `∫ e^{-f₀} < ∞`, `α, η > 0`,
`FunctionalLSIPi (targetPi f₀) (1/α)`, `targetPi f₀ ≤ C₂ • N(0, v I)` (`C₂`, `v` real), and `W`
measurable with `a ≤ W ≤ b`. Let `π = targetPi (f₀ + W)` and `ρ (k+1) = proxKernelPi (f₀ + W) η ∘ₘ
ρ k` from a probability law `ρ 0` with `KL(ρ 0‖π) < ∞`. Then for every `k`, `ρ k` is a probability
law, `KL(ρ k‖π) < ∞` and, with `α' = α e^{-(b-a)}`,
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α' η)^(2k)`. -/
theorem toReal_klDiv_iteratePi_le_sq_add {α η C₂ v : ℝ} (hf₀ : Measurable f₀)
    (hint : Integrable (fun x => Real.exp (-f₀ x))) (hα : 0 < α) (hη : 0 < η)
    (hLSI : FunctionalLSIPi (targetPi f₀) (1 / α))
    (henv : targetPi f₀ ≤ ENNReal.ofReal C₂ • Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (fun x => f₀ x + W x) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (targetPi fun x => f₀ x + W x) ≠ ⊤) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (targetPi fun x => f₀ x + W x) ≠ ⊤ ∧
      (klDiv (ρ k) (targetPi fun x => f₀ x + W x)).toReal
        ≤ (klDiv (ρ 0) (targetPi fun x => f₀ x + W x)).toReal
          / (1 + α * Real.exp (-(b - a)) * η) ^ (2 * k) := by
  obtain ⟨-, C₂', -, henv'⟩ := exists_envelope_add_of_le hf₀ hint hW ha henv
  have hLSI' := functionalLSIPi_targetPi_add hf₀ hint hLSI (by positivity) hW ha hb
  have e : 1 / α * Real.exp (b - a) = 1 / (α * Real.exp (-(b - a))) := by
    rw [Real.exp_neg]; field_simp
  rw [e] at hLSI'
  exact toReal_klDiv_iteratePi_le_sq_general (hf₀.add hW) (by positivity) hη hLSI' henv' ρ
    hstep hKL k

/-- **PX-2 for bounded perturbations of strongly log-concave targets (Verified).** Let
`α, η > 0`, `f₀ - α |x|²/2` convex on `Fin d → ℝ` (no separability or smoothness), and `W`
measurable with `a ≤ W ≤ b`. For `π = targetPi (f₀ + W)` and the exact proximal sampler
`ρ (k+1) = proxKernelPi (f₀ + W) η ∘ₘ ρ k` from a probability law `ρ 0` with `KL(ρ 0‖π) < ∞`:
for every `k`, `ρ k` is a probability law, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α e^{-(b-a)} η)^(2k)`. The LSI of `targetPi f₀` is
Bakry–Émery (`BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`) and its envelope comes
from strong convexity (`ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi`). -/
theorem toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave_add {α η : ℝ} (hα : 0 < α)
    (hη : 0 < η) (hconv : ConvexOn ℝ univ fun x => f₀ x - gaussPotentialPi α x)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (fun x => f₀ x + W x) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (targetPi fun x => f₀ x + W x) ≠ ⊤) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (targetPi fun x => f₀ x + W x) ≠ ⊤ ∧
      (klDiv (ρ k) (targetPi fun x => f₀ x + W x)).toReal
        ≤ (klDiv (ρ 0) (targetPi fun x => f₀ x + W x)).toReal
          / (1 + α * Real.exp (-(b - a)) * η) ^ (2 * k) := by
  obtain ⟨hint, C₂, -, henv⟩ := exists_envelope_of_strongConvexPi hα hconv
  exact toReal_klDiv_iteratePi_le_sq_add
    (BakryEmeryGeneralPi.measurable_of_convexOn_sub hconv) hint hα hη
    (BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn hα hconv) henv hW ha hb ρ hstep
    hKL k

end FormalizeSampling.ProximalPerturbedGeneralPi
