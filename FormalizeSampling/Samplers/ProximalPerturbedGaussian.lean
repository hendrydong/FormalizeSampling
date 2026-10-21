module

public import FormalizeSampling.Samplers.ProximalGeneralLSIPi
public import FormalizeSampling.Foundations.HolleyStroock
public import FormalizeSampling.Foundations.GaussianFunctionalLSIPi

/-!
# PX-4: the squared-exponent proximal rate for bounded perturbations of a Gaussian target

Status: **Verified** (dimension one and `Fin d → ℝ`; no named hypotheses).

For `f(x) = α |x|²/2 + W(x)` with `α > 0`, `W` measurable and `a ≤ W ≤ b`, the target
`π ∝ e^{-f}` need not be log-concave. For every probability law `ρ₀` with `KL(ρ₀‖π) < ∞` (no warm
start, no moment hypothesis) the exact proximal sampler `ρ_{k+1} = ρ_k P_prox` satisfies, with
`α' = α e^{-(b-a)}`,
`KL(ρ_k‖π) ≤ KL(ρ₀‖π) / (1 + α' η)^{2k}` and `TV(ρ_k, π) ≤ √(KL(ρ₀‖π) / (2 (1 + α' η)^{2k}))`.

These are the general theorems of `ProximalGeneralLSI(Pi)` (a functional LSI and a Gaussian
upper envelope of the target) applied with
* the functional LSI of `π` with constant `1/α'`: Holley–Stroock applied to Gross's inequality
  (`functionalLSI_perturbed`, `functionalLSIPi_perturbed`);
* the Gaussian upper envelope `π ≤ C₂ • N(0, I/α)`
  (`ProximalSharpPerturbed.exists_envelope_perturbed` and
  `ProximalSharpPerturbedPi.exists_envelope_perturbedPi`, in `Foundations/GibbsMeasure.lean`).

Mathematically this is Theorem 3 of Chen–Chewi–Salim–Wibisono (2022, arXiv:2202.06386), the KL
rate under a log-Sobolev inequality, combined with the Holley–Stroock perturbation lemma; the
Lean statements assume only the hypotheses listed above.

The one-dimensional statements live in the namespaces `ProximalSharpPerturbed` (the LSI) and
`ProximalSharpPerturbedCold` (the rates), the `Fin d → ℝ` statements in
`ProximalSharpPerturbedPi`.

## Main results

* `ProximalSharpPerturbed.functionalLSI_perturbed`,
  `ProximalSharpPerturbedPi.functionalLSIPi_perturbed`: `LSI(π, e^{b-a}/α)`.
* `ProximalSharpPerturbedCold.toReal_klDiv_proxKernel_comp_le_sq_perturbed_of_ne_top` (one
  step), `toReal_klDiv_iterate_le_sq_perturbed_of_ne_top` (iterates),
  `tvSup_iterate_le_sq_perturbed_of_ne_top` (TV), dimension one.
* `ProximalSharpPerturbedPi.toReal_klDiv_proxKernelPi_comp_le_sq_perturbed_of_ne_top`,
  `toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top`, `tvSupPi_iterate_le_sq_perturbed_of_ne_top`
  on `Fin d → ℝ`.

## Not proved here

* Optimality of `α' = α e^{-(b-a)}`: it is the Holley–Stroock constant, not optimal in general
  (the exponent `2` is attained for `W` constant, EX-3).
* Unbounded perturbations `W`, and starts with `KL(ρ₀‖π) = ∞` (vacuous).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal

/-! ### Dimension one -/

namespace FormalizeSampling.ProximalSharpPerturbed

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp FormalizeSampling.LogSobolev

variable {α a b : ℝ} {W : ℝ → ℝ}

/-- The functional LSI of the perturbed target with constant `1/α'`, `α' = α e^{-(b-a)}`
(Holley–Stroock; `α > 0`, `W` measurable, `a ≤ W ≤ b`). -/
theorem functionalLSI_perturbed (hα : 0 < α) (hW : Measurable W) (ha : ∀ x, a ≤ W x)
    (hb : ∀ x, W x ≤ b) :
    FunctionalLSI (target (gaussPotential α + W)) (1 / (α * Real.exp (-(b - a)))) := by
  have h := HolleyStroock.functionalLSI_target_gaussPotential_add hα hW ha hb
  have e : 1 / (α * Real.exp (-(b - a))) = Real.exp (b - a) / α := by
    rw [Real.exp_neg]; field_simp
  rw [e]
  exact h

end FormalizeSampling.ProximalSharpPerturbed

namespace FormalizeSampling.ProximalSharpPerturbedCold

open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
open FormalizeSampling.ProximalSharpPerturbed FormalizeSampling.ProximalGeneralLSI

variable {α η a b : ℝ} {W : ℝ → ℝ}

/-- **PX-2 for perturbed Gaussians, one step, any finite-KL start (Verified).** Let
`α, η > 0`, `W` measurable with `a ≤ W ≤ b`, `π = target (f_α + W)` and `ρ` a probability law
with `KL(ρ‖π) < ∞`. Then `KL(proxKernel (f_α + W) η ∘ₘ ρ‖π) < ∞` and, with
`α' = α e^{-(b-a)}`, `KL(proxKernel (f_α + W) η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α' η)²`.
-/
theorem toReal_klDiv_proxKernel_comp_le_sq_perturbed_of_ne_top (hα : 0 < α) (hη : 0 < η)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hKL : klDiv ρ (target (gaussPotential α + W)) ≠ ⊤) :
    klDiv (proxKernel (gaussPotential α + W) η ∘ₘ ρ) (target (gaussPotential α + W)) ≠ ⊤ ∧
      (klDiv (proxKernel (gaussPotential α + W) η ∘ₘ ρ) (target (gaussPotential α + W))).toReal
        ≤ (klDiv ρ (target (gaussPotential α + W))).toReal
          / (1 + α * Real.exp (-(b - a)) * η) ^ 2 := by
  obtain ⟨C₂, -, henv⟩ := exists_envelope_perturbed hα hW ha
  exact toReal_klDiv_proxKernel_comp_le_sq_general ((measurable_gaussPotential α).add hW)
    (by positivity) hη (functionalLSI_perturbed hα hW ha hb) henv ρ hKL

/-- **PX-2 for perturbed Gaussians, iterated, any finite-KL start (Verified).** Let
`α, η > 0`, `W` measurable with `a ≤ W ≤ b`, `π = target (f_α + W)`, and `ρ : ℕ → Measure ℝ` the
proximal-sampler laws (`ρ (k+1) = proxKernel (f_α + W) η ∘ₘ ρ k`) from a probability law `ρ 0`
with `KL(ρ 0‖π) < ∞`. Then for every `k`, `ρ k` is a probability law, `KL(ρ k‖π) < ∞` and, with
`α' = α e^{-(b-a)}`, `KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α' η)^(2k)`. -/
theorem toReal_klDiv_iterate_le_sq_perturbed_of_ne_top (hα : 0 < α) (hη : 0 < η)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) (ρ : ℕ → Measure ℝ)
    [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel (gaussPotential α + W) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (target (gaussPotential α + W)) ≠ ⊤) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (target (gaussPotential α + W)) ≠ ⊤ ∧
      (klDiv (ρ k) (target (gaussPotential α + W))).toReal
        ≤ (klDiv (ρ 0) (target (gaussPotential α + W))).toReal
          / (1 + α * Real.exp (-(b - a)) * η) ^ (2 * k) := by
  obtain ⟨C₂, -, henv⟩ := exists_envelope_perturbed hα hW ha
  exact toReal_klDiv_iterate_le_sq_general ((measurable_gaussPotential α).add hW)
    (by positivity) hη (functionalLSI_perturbed hα hW ha hb) henv ρ hstep hKL k

/-- **TV form of the squared-exponent rate.** Under the hypotheses of
`toReal_klDiv_iterate_le_sq_perturbed_of_ne_top`, with TV normalised as `sup_A |μ A - ν A|`:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α e^{-(b-a)} η)^(2k)))`. -/
theorem tvSup_iterate_le_sq_perturbed_of_ne_top (hα : 0 < α) (hη : 0 < η)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) (ρ : ℕ → Measure ℝ)
    [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel (gaussPotential α + W) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (target (gaussPotential α + W)) ≠ ⊤) (k : ℕ) :
    TotalVariation.tvSup (ρ k) (target (gaussPotential α + W))
      ≤ √((klDiv (ρ 0) (target (gaussPotential α + W))).toReal
          / (2 * (1 + α * Real.exp (-(b - a)) * η) ^ (2 * k))) := by
  obtain ⟨C₂, -, henv⟩ := exists_envelope_perturbed hα hW ha
  exact tvSup_iterate_le_sq_general ((measurable_gaussPotential α).add hW)
    (by positivity) hη (functionalLSI_perturbed hα hW ha hb) henv ρ hstep hKL k

end FormalizeSampling.ProximalSharpPerturbedCold

/-! ### Dimension `d` -/

namespace FormalizeSampling.ProximalSharpPerturbedPi

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.LogSobolevPi FormalizeSampling.ProximalGeneralLSIPi

variable {d : ℕ} {α η a b : ℝ} {W : (Fin d → ℝ) → ℝ}

/-- The functional LSI of the perturbed target on `Fin d → ℝ` with constant `1/α'`,
`α' = α e^{-(b-a)}` (Holley–Stroock; `α > 0`, `W` measurable, `a ≤ W ≤ b`). -/
theorem functionalLSIPi_perturbed (hα : 0 < α) (hW : Measurable W) (ha : ∀ x, a ≤ W x)
    (hb : ∀ x, W x ≤ b) :
    FunctionalLSIPi (targetPi fun x => gaussPotentialPi α x + W x)
      (1 / (α * Real.exp (-(b - a)))) := by
  have h := GaussianFunctionalLSIPi.functionalLSIPi_targetPi_gaussPotentialPi_add hα hW ha hb
  have e : 1 / (α * Real.exp (-(b - a))) = Real.exp (b - a) / α := by
    rw [Real.exp_neg]; field_simp
  rw [e]
  exact h

/-- **PX-2 on `Fin d → ℝ` for perturbed Gaussians, one step, any finite-KL start
(Verified).** Let `α, η > 0`, `W` measurable with `a ≤ W ≤ b`, `π = targetPi (f_α + W)`
(`f_α(x) = α (∑ᵢ xᵢ²)/2`) and `ρ` a probability law with `KL(ρ‖π) < ∞` (no warm start, no
moment assumption). Then `KL(proxKernelPi (f_α + W) η ∘ₘ ρ‖π) < ∞` and, with
`α' = α e^{-(b-a)}`, `KL(proxKernelPi (f_α + W) η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α' η)²`.
-/
theorem toReal_klDiv_proxKernelPi_comp_le_sq_perturbed_of_ne_top (hα : 0 < α) (hη : 0 < η)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (targetPi fun x => gaussPotentialPi α x + W x) ≠ ⊤) :
    klDiv (proxKernelPi (fun x => gaussPotentialPi α x + W x) η ∘ₘ ρ)
        (targetPi fun x => gaussPotentialPi α x + W x) ≠ ⊤ ∧
      (klDiv (proxKernelPi (fun x => gaussPotentialPi α x + W x) η ∘ₘ ρ)
          (targetPi fun x => gaussPotentialPi α x + W x)).toReal
        ≤ (klDiv ρ (targetPi fun x => gaussPotentialPi α x + W x)).toReal
          / (1 + α * Real.exp (-(b - a)) * η) ^ 2 := by
  obtain ⟨C₂, -, henv⟩ := exists_envelope_perturbedPi hα hW ha
  exact toReal_klDiv_proxKernelPi_comp_le_sq_general ((measurable_gaussPotentialPi α).add hW)
    (by positivity) hη (functionalLSIPi_perturbed hα hW ha hb) henv ρ hKL

/-- **PX-2 on `Fin d → ℝ` for perturbed Gaussians, iterated, any finite-KL start
(Verified).** Let `α, η > 0`, `W` measurable with `a ≤ W ≤ b`, `π = targetPi (f_α + W)`, and
`ρ : ℕ → Measure (Fin d → ℝ)` the proximal-sampler laws
(`ρ (k+1) = proxKernelPi (f_α + W) η ∘ₘ ρ k`) from a probability law `ρ 0` with
`KL(ρ 0‖π) < ∞`. Then for every `k`, `ρ k` is a probability law, `KL(ρ k‖π) < ∞` and, with
`α' = α e^{-(b-a)}`, `KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α' η)^(2k)`. -/
theorem toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top (hα : 0 < α) (hη : 0 < η)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (fun x => gaussPotentialPi α x + W x) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (targetPi fun x => gaussPotentialPi α x + W x) ≠ ⊤) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧
      klDiv (ρ k) (targetPi fun x => gaussPotentialPi α x + W x) ≠ ⊤ ∧
      (klDiv (ρ k) (targetPi fun x => gaussPotentialPi α x + W x)).toReal
        ≤ (klDiv (ρ 0) (targetPi fun x => gaussPotentialPi α x + W x)).toReal
          / (1 + α * Real.exp (-(b - a)) * η) ^ (2 * k) := by
  obtain ⟨C₂, -, henv⟩ := exists_envelope_perturbedPi hα hW ha
  exact toReal_klDiv_iteratePi_le_sq_general ((measurable_gaussPotentialPi α).add hW)
    (by positivity) hη (functionalLSIPi_perturbed hα hW ha hb) henv ρ hstep hKL k

/-- **TV form of the squared-exponent rate on `Fin d → ℝ`.** Under the hypotheses of
`toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top`, with TV normalised as `sup_A |μ A - ν A|`:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α e^{-(b-a)} η)^(2k)))`. -/
theorem tvSupPi_iterate_le_sq_perturbed_of_ne_top (hα : 0 < α) (hη : 0 < η)
    (hW : Measurable W) (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b)
    (ρ : ℕ → Measure (Fin d → ℝ)) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (fun x => gaussPotentialPi α x + W x) η ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) (targetPi fun x => gaussPotentialPi α x + W x) ≠ ⊤) (k : ℕ) :
    TotalVariation.tvSup (ρ k) (targetPi fun x => gaussPotentialPi α x + W x)
      ≤ √((klDiv (ρ 0) (targetPi fun x => gaussPotentialPi α x + W x)).toReal
          / (2 * (1 + α * Real.exp (-(b - a)) * η) ^ (2 * k))) := by
  obtain ⟨C₂, -, henv⟩ := exists_envelope_perturbedPi hα hW ha
  exact tvSupPi_iterate_le_sq_general ((measurable_gaussPotentialPi α).add hW)
    (by positivity) hη (functionalLSIPi_perturbed hα hW ha hb) henv ρ hstep hKL k

end FormalizeSampling.ProximalSharpPerturbedPi
