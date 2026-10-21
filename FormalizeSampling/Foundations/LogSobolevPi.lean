module

public import FormalizeSampling.Foundations.LogSobolev

/-!
# Functional log-Sobolev inequalities on `Fin d → ℝ`: definitions

Status: definitions only (no theorems are asserted here beyond basic facts).

The entropy `LogSobolev.ent` is reused. For `g : (Fin d → ℝ) → ℝ`, `gradSq g x = ∑ᵢ (∂ᵢ g(x))²`
is the squared Euclidean norm of the gradient. `LSIClassPi g` asks `g` to be differentiable,
bounded, with bounded `gradSq`, and bounded below by a positive constant. `FunctionalLSIPi μ C`
is `Ent_μ(g²) ≤ 2 C ∫ ‖∇g‖² dμ` for every `g` in that class (`C = 1/α` for an `α`-LSI; the
isotropic Gaussian `N(0, t I)` has `C = t`).
-/

@[expose] public section

open MeasureTheory

namespace FormalizeSampling.LogSobolevPi

open FormalizeSampling.LogSobolev

variable {d : ℕ}

/-- Squared Euclidean norm of the gradient: `gradSq g x = ∑ᵢ (∂ᵢ g(x))²`. -/
noncomputable def gradSq (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, (fderiv ℝ g x (Pi.single i 1)) ^ 2

/-- `gradSq g` is measurable for every `g` (each partial derivative `x ↦ fderiv ℝ g x eᵢ` is
measurable; no regularity of `g` is needed). -/
theorem measurable_gradSq (g : (Fin d → ℝ) → ℝ) : Measurable (gradSq g) := by
  unfold gradSq
  exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ g _).pow_const 2

/-- Test functions: differentiable, bounded, bounded `gradSq`, bounded below by some `c > 0`. -/
def LSIClassPi (g : (Fin d → ℝ) → ℝ) : Prop :=
  Differentiable ℝ g ∧ (∃ M, ∀ x, |g x| ≤ M) ∧ (∃ K, ∀ x, gradSq g x ≤ K) ∧
    ∃ c > 0, ∀ x, c ≤ g x

/-- The functional log-Sobolev inequality with constant `C` on `Fin d → ℝ`:
`Ent_μ(g²) ≤ 2 C ∫ ‖∇g‖² dμ` for every `g` in `LSIClassPi`. -/
def FunctionalLSIPi (μ : Measure (Fin d → ℝ)) (C : ℝ) : Prop :=
  ∀ g, LSIClassPi g → ent μ (fun x => g x ^ 2) ≤ 2 * C * ∫ x, gradSq g x ∂μ

/-- `gradSq` is nonnegative (no assumptions). -/
theorem gradSq_nonneg (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : 0 ≤ gradSq g x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end FormalizeSampling.LogSobolevPi
