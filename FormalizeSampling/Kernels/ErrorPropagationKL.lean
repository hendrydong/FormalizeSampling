module

public import FormalizeSampling.Kernels.ErrorPropagation
public import FormalizeSampling.Foundations.Pinsker
public import FormalizeSampling.Foundations.KLChainRule

/-!
# Kernel error propagation with per-step errors measured in KL

Two Markov chains on a measurable space `α`: the exact chain `μ (n+1) = κ n ∘ₘ μ n` and the
approximate chain `ν (n+1) = η n ∘ₘ ν n`, started from probability laws. The per-step kernel
errors are Kullback–Leibler divergences (Mathlib's `klDiv`, valued in `ℝ≥0∞`) bounded by real
budgets `c k` (as `klDiv … ≤ ENNReal.ofReal (c k)`), and are turned into total-variation bounds
(`tvSup`, normalised as `sup_A |μ(A) - ν(A)|`) by Pinsker's inequality (KL-1).

## Main results

* TV telescoping (KR-1) with one Pinsker step per kernel step:
  `tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} √(c k / 2)`, where `c k` bounds
  - the pointwise kernel KL, `KL(κ k x ‖ η k x) ≤ c k` for every `x`
    (`tvSup_chain_le_sum_sqrt_klDiv`, any measurable space);
  - the KL of the joint laws of one step, `KL(μ k ⊗ₘ κ k ‖ μ k ⊗ₘ η k) ≤ c k`
    (`tvSup_chain_le_sum_sqrt_klDiv_compProd`, any measurable space);
  - the kernel KL averaged under the exact chain's law, `∫⁻ x, KL(κ k x ‖ η k x) ∂(μ k) ≤ c k`
    (`tvSup_chain_le_sum_sqrt_lintegral_klDiv`, countably generated `α`, e.g. `Fin d → ℝ`).
  One-step forms: `tvSup_comp_le_sqrt_klDiv_compProd`, `tvSup_comp_le_sqrt_lintegral_klDiv`.
* KL telescoping with a single Pinsker step at the end (KL-2 and KL-1),
  `tvSup_chain_le_sqrt_klDiv_add_sum`: if `KL(ν 0 ‖ μ 0) < ∞` and the one-step errors averaged
  under the approximate chain's laws satisfy `∫⁻ x, KL(η k x ‖ κ k x) ∂(ν k) ≤ c k`, then
  `tvSup (ν n) (μ n) ≤ √((KL(ν 0 ‖ μ 0) + ∑_{k<n} c k) / 2)`.

The two forms are not comparable in general: the first pays one square root per step and allows
an initial error in TV; the second sums the errors inside one square root (no `√n` loss for
equal errors) but needs the initial error in KL.

## Not proved here

* Measurability of `x ↦ KL(κ x ‖ η x)` on a general measurable space. There the averaged error
  is stated through the joint laws, `KL(μ ⊗ₘ κ ‖ μ ⊗ₘ η)`, which equals the averaged kernel KL
  when `α` is countably generated (`KL.klDiv_compProd_right_eq_lintegral`).
-/

public section

open MeasureTheory
open ProbabilityTheory InformationTheory Finset
open scoped ENNReal

namespace FormalizeSampling
namespace ErrorPropagation

open TotalVariation

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### One step -/

/-- **One step, joint-law KL error.** For a probability law `μ` on `α`, Markov kernels
`κ η : Kernel α β` (any measurable spaces) and a real `c`, if the joint laws satisfy
`KL(μ ⊗ₘ κ ‖ μ ⊗ₘ η) ≤ c`, then `tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ √(c / 2)`. Proof: data processing
for the second marginal (`KL.klDiv_comp_le_compProd`) and Pinsker. -/
theorem tvSup_comp_le_sqrt_klDiv_compProd (κ η : Kernel α β) [IsMarkovKernel κ]
    [IsMarkovKernel η] (μ : Measure α) [IsProbabilityMeasure μ] {c : ℝ}
    (h : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤ ENNReal.ofReal c) :
    tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ √(c / 2) :=
  Pinsker.tvSup_le_sqrt_of_klDiv_le_ofReal ((KL.klDiv_comp_le_compProd μ μ κ η).trans h)

/-- **One step, averaged kernel KL error.** For `α` countable or `β` countably generated, a
probability law `μ` on `α`, Markov kernels `κ η : Kernel α β` and a real `c`, if
`∫⁻ x, KL(κ x ‖ η x) ∂μ ≤ c`, then `tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ √(c / 2)`. Pinsker is applied
once to the composed laws, so no Jensen step and no integrability are needed. -/
theorem tvSup_comp_le_sqrt_lintegral_klDiv [MeasurableSpace.CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure α)
    [IsProbabilityMeasure μ] {c : ℝ} (h : ∫⁻ x, klDiv (κ x) (η x) ∂μ ≤ ENNReal.ofReal c) :
    tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ √(c / 2) :=
  tvSup_comp_le_sqrt_klDiv_compProd κ η μ
    ((KL.klDiv_compProd_right_eq_lintegral μ κ η).trans_le h)

/-! ### TV telescoping along two chains -/

/-- **TV along two chains, pointwise KL errors.** Let `κ η : ℕ → Kernel α α` be Markov kernels
on a measurable space `α`, and `μ ν` the laws of the chains `μ (n+1) = κ n ∘ₘ μ n`,
`ν (n+1) = η n ∘ₘ ν n` from probability laws `μ 0`, `ν 0`. If `KL(κ k x ‖ η k x) ≤ c k` for every
step `k` and state `x` (`c k` real), then
`tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} √(c k / 2)`. -/
theorem tvSup_chain_le_sum_sqrt_klDiv {κ η : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)]
    [∀ n, IsMarkovKernel (η n)] {μ ν : ℕ → Measure α} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {c : ℕ → ℝ}
    (h : ∀ n x, klDiv (κ n x) (η n x) ≤ ENNReal.ofReal (c n)) (n : ℕ) :
    tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑ k ∈ range n, √(c k / 2) :=
  tvSup_chain_le_sum hμ hν (fun k x => Pinsker.tvSup_le_sqrt_of_klDiv_le_ofReal (h k x)) n

/-- **TV along two chains, joint-law KL errors (any measurable space).** With the chains of
`tvSup_chain_le_sum_sqrt_klDiv`, if the joint laws of step `k` under the exact chain's law
satisfy `KL(μ k ⊗ₘ κ k ‖ μ k ⊗ₘ η k) ≤ c k` (`c k` real), then
`tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} √(c k / 2)`. No measurability of
`x ↦ KL(κ k x ‖ η k x)` is needed; for countably generated `α` the joint-law KL equals the kernel
KL averaged under `μ k` (`tvSup_chain_le_sum_sqrt_lintegral_klDiv`). -/
theorem tvSup_chain_le_sum_sqrt_klDiv_compProd {κ η : ℕ → Kernel α α}
    [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)] {μ ν : ℕ → Measure α}
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {c : ℕ → ℝ}
    (h : ∀ n, klDiv (μ n ⊗ₘ κ n) (μ n ⊗ₘ η n) ≤ ENNReal.ofReal (c n)) (n : ℕ) :
    tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑ k ∈ range n, √(c k / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_of_comp_succ hμ n
    have := isProbabilityMeasure_of_comp_succ hν n
    have h1 := tvSup_triangle (κ n ∘ₘ μ n) (η n ∘ₘ μ n) (η n ∘ₘ ν n)
    have h2 := tvSup_comp_le_sqrt_klDiv_compProd (κ n) (η n) (μ n) (h n)
    have h3 := tvSup_comp_le (η n) (μ n) (ν n)
    rw [hμ n, hν n, sum_range_succ]
    linarith

/-- **TV along two chains, KL errors averaged under the exact chain's law.** For `α` countably
generated (e.g. `Fin d → ℝ` or `ℝ`) and the chains of `tvSup_chain_le_sum_sqrt_klDiv`, if
`∫⁻ x, KL(κ k x ‖ η k x) ∂(μ k) ≤ c k` for every step `k` (`c k` real), then
`tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} √(c k / 2)`. -/
theorem tvSup_chain_le_sum_sqrt_lintegral_klDiv
    [MeasurableSpace.CountableOrCountablyGenerated α α] {κ η : ℕ → Kernel α α}
    [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)] {μ ν : ℕ → Measure α}
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {c : ℕ → ℝ}
    (h : ∀ n, ∫⁻ x, klDiv (κ n x) (η n x) ∂(μ n) ≤ ENNReal.ofReal (c n)) (n : ℕ) :
    tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑ k ∈ range n, √(c k / 2) :=
  tvSup_chain_le_sum_sqrt_klDiv_compProd hμ hν (fun k => by
    have := isProbabilityMeasure_of_comp_succ hμ k
    exact (KL.klDiv_compProd_right_eq_lintegral (μ k) (κ k) (η k)).trans_le (h k)) n

/-! ### KL telescoping and one Pinsker step -/

/-- **TV from a per-step KL budget (KL telescoping).** For `α` countably generated and the
chains of `tvSup_chain_le_sum_sqrt_klDiv`, assume `KL(ν 0 ‖ μ 0) < ∞` and that the one-step
errors, averaged under the **approximate** chain's laws, satisfy
`∫⁻ x, KL(η k x ‖ κ k x) ∂(ν k) ≤ c k` with `c k ≥ 0`. Then
`tvSup (ν n) (μ n) ≤ √((KL(ν 0 ‖ μ 0) + ∑_{k<n} c k) / 2)` (KL chain rule
`KL.klDiv_chain_le_sum`, then Pinsker once). -/
theorem tvSup_chain_le_sqrt_klDiv_add_sum [MeasurableSpace.CountableOrCountablyGenerated α α]
    {κ η : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]
    {μ ν : ℕ → Measure α} [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n) (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n)
    (h0 : klDiv (ν 0) (μ 0) ≠ ∞) {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (h : ∀ n, ∫⁻ x, klDiv (η n x) (κ n x) ∂(ν n) ≤ ENNReal.ofReal (c n)) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ √(((klDiv (ν 0) (μ 0)).toReal + ∑ k ∈ range n, c k) / 2) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  have : ∀ k, IsFiniteMeasure (μ k) := fun k =>
    have := isProbabilityMeasure_of_comp_succ hμ k; inferInstance
  have : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    have := isProbabilityMeasure_of_comp_succ hν k; inferInstance
  refine Pinsker.tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal h0 hc
    ((KL.klDiv_chain_le_sum κ η μ ν hμ hν n).trans ?_)
  gcongr with k
  exact h k

end ErrorPropagation
end FormalizeSampling
