module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# One Stein test statistic does not identify the law (CE-04)

For the standard Gaussian `N(0,1)` Stein's identity `E[X φ(X)] = E[φ'(X)]` holds for every
sufficiently regular test function `φ`, and conversely the identity over a rich enough class
of `φ` characterises `N(0,1)`. A *single* test function (or a small class) is not enough:
the Rademacher law `ρ = ½ δ₁ + ½ δ₋₁` satisfies `∫ x φ(x) dρ = ∫ φ'(x) dρ` for every affine
`φ(x) = a x + b` (in particular for `φ(x) = x`), exactly like `N(0,1)` does, yet `ρ ≠ N(0,1)`.
The richer test function `φ(x) = x ^ 3` detects the difference: `∫ x · x ^ 3 dρ = 1` but
`∫ 3 x ^ 2 dρ = 3`.

So matching one (or finitely many) integration-by-parts statistics — e.g. a wrong score that
"looks plausible" on a small feature class — does not identify a distribution.

## Conventions

* `φ'` is written `deriv φ`; all test functions used here are polynomials, so `deriv` is the
  classical derivative (no `deriv`-of-non-differentiable-function artefact).
* `rademacher` is a probability measure on `ℝ` (`isProbabilityMeasure_rademacher`).

## Registry IDs

* `CE-04`: `integral_rademacher`, `stein_affine_rademacher`, `stein_id_rademacher`,
  `stein_affine_gaussian`, `stein_cube_rademacher`, `stein_cube_rademacher_ne`,
  `rademacher_ne_gaussian`, `single_stein_test_not_identifying`.

## Not proved here

* Stein's lemma for `N(0,1)` for general `C¹` test functions and the converse
  characterisation (Stein's identity over all bounded `C¹` `φ` forces `N(0,1)`) are not
  formalised; for `N(0,1)` only the affine case is checked (`stein_affine_gaussian`). The
  Gaussian value `∫ x ^ 4 dN(0,1) = 3` for the cubic test is not formalised either.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.Counterexamples.SteinSingleTest

/-- The Rademacher law `ρ = ½ δ₁ + ½ δ₋₁` on `ℝ`. -/
noncomputable def rademacher : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + (1 / 2 : ℝ≥0∞) • Measure.dirac (-1)

/-- The Rademacher law is a probability measure. -/
theorem isProbabilityMeasure_rademacher : IsProbabilityMeasure rademacher := by
  constructor
  simp only [rademacher, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.add_halves]

/-- **Integrals against the Rademacher law.** For every `f : ℝ → ℝ`,
`∫ f dρ = (f 1 + f (-1)) / 2`. -/
theorem integral_rademacher (f : ℝ → ℝ) :
    ∫ x, f x ∂rademacher = (f 1 + f (-1)) / 2 := by
  have h1 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have h2 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  rw [rademacher, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- **Stein identity for affine test functions under `ρ`.** For every `a b : ℝ`, with
`φ(x) = a x + b`, the Rademacher law satisfies `∫ x φ(x) dρ = ∫ φ'(x) dρ`. -/
theorem stein_affine_rademacher (a b : ℝ) :
    ∫ x, x * (a * x + b) ∂rademacher = ∫ x, deriv (fun y => a * y + b) x ∂rademacher := by
  have hd : ∀ x : ℝ, deriv (fun y => a * y + b) x = a := by
    intro x
    simp
  simp only [hd, integral_rademacher]
  ring

/-- **Stein identity for `φ(x) = x` under `ρ`.** `∫ x · x dρ = ∫ (d/dx x) dρ` (both equal `1`).
-/
theorem stein_id_rademacher :
    ∫ x, x * x ∂rademacher = ∫ x, deriv (fun y : ℝ => y) x ∂rademacher := by
  simpa using stein_affine_rademacher 1 0

/-- **The standard Gaussian passes the same affine Stein tests.** For every `a b : ℝ`,
`∫ x (a x + b) dN(0,1) = ∫ (a x + b)' dN(0,1)` (both equal `a`, using mean `0` and
variance `1`). -/
theorem stein_affine_gaussian (a b : ℝ) :
    ∫ x, x * (a * x + b) ∂(gaussianReal 0 1) =
      ∫ x, deriv (fun y => a * y + b) x ∂(gaussianReal 0 1) := by
  have hd : ∀ x : ℝ, deriv (fun y => a * y + b) x = a := by
    intro x
    simp
  have hint1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hsq : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
    simpa using hv
  have hexp : (fun x : ℝ => x * (a * x + b)) = fun x => a * x ^ 2 + b * x := by
    funext x
    ring
  simp only [hd, hexp]
  rw [integral_add (hint2.const_mul a) (hint1.const_mul b), integral_const_mul,
    integral_const_mul, hsq, integral_id_gaussianReal]
  simp

/-- **The cubic Stein test fails for `ρ`.** With `φ(x) = x ^ 3`,
`∫ x φ(x) dρ = ∫ x ^ 4 dρ = 1` while `∫ φ'(x) dρ = ∫ 3 x ^ 2 dρ = 3`. -/
theorem stein_cube_rademacher :
    ∫ x, x * x ^ 3 ∂rademacher = 1 ∧ ∫ x, deriv (fun y : ℝ => y ^ 3) x ∂rademacher = 3 := by
  have hd : ∀ x : ℝ, deriv (fun y : ℝ => y ^ 3) x = 3 * x ^ 2 := by
    intro x
    simp
  refine ⟨?_, ?_⟩
  · rw [integral_rademacher]
    norm_num
  · simp only [hd]
    rw [integral_rademacher]
    norm_num

/-- **The cubic Stein identity fails for `ρ`:** `∫ x · x ^ 3 dρ ≠ ∫ (x ^ 3)' dρ`. -/
theorem stein_cube_rademacher_ne :
    ∫ x, x * x ^ 3 ∂rademacher ≠ ∫ x, deriv (fun y : ℝ => y ^ 3) x ∂rademacher := by
  rw [stein_cube_rademacher.1, stein_cube_rademacher.2]
  norm_num

/-- **`ρ` is not the standard Gaussian:** `ρ {1} = 1 / 2` whereas `N(0,1)` has no atoms. -/
theorem rademacher_ne_gaussian : rademacher ≠ gaussianReal 0 1 := by
  intro h
  have h1 : rademacher {1} = 0 := by
    rw [h]
    have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    exact measure_singleton 1
  have h2 : rademacher {1} ≠ 0 := by
    simp only [rademacher, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_singleton (1 : ℝ))]
    simp
  exact h2 h1

/-- **CE-04: one Stein test statistic does not identify the law.** There is a probability
measure `ρ` on `ℝ` (the Rademacher law) with `ρ ≠ N(0,1)` that satisfies the Stein identity
`∫ x φ(x) dρ = ∫ φ'(x) dρ` for every affine test function `φ(x) = a x + b` — the same affine
Stein statistics as `N(0,1)` (`stein_affine_gaussian`) — while the identity fails for
`φ(x) = x ^ 3`. -/
theorem single_stein_test_not_identifying :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ ρ ≠ gaussianReal 0 1 ∧
      (∀ a b : ℝ, ∫ x, x * (a * x + b) ∂ρ = ∫ x, deriv (fun y => a * y + b) x ∂ρ) ∧
      ∫ x, x * x ^ 3 ∂ρ ≠ ∫ x, deriv (fun y : ℝ => y ^ 3) x ∂ρ :=
  ⟨rademacher, isProbabilityMeasure_rademacher, rademacher_ne_gaussian, stein_affine_rademacher,
    stein_cube_rademacher_ne⟩

end FormalizeSampling.Counterexamples.SteinSingleTest
