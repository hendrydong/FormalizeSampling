module

public import Mathlib.Probability.Kernel.Invariance
public import FormalizeSampling.Foundations.TotalVariation

/-!
# Kernel error propagation in total variation

Composable total-variation (TV) error certificates for Markov kernels on general measurable
spaces (no topology). `κ ∘ₘ μ` is Mathlib's composition of a measure with a kernel,
i.e. `MeasureTheory.Measure.bind μ κ`, the law of `X₁ ~ κ(X₀, ·)` when `X₀ ~ μ`; `tvSup` is
`FormalizeSampling.TotalVariation.tvSup`, normalised as `sup_A |μ(A) - ν(A)|`.

## Main results

* KR-1, `tvSup_comp_le`: a Markov kernel contracts TV,
  `tvSup (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvSup μ ν` (finite measures `μ ν`).
* Kernel perturbation with a common input law `μ`:
  - uniform: `tvSup_comp_le_of_forall`, `∀ x, tvSup (κ x) (η x) ≤ ε` gives
    `tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ε` (probability `μ`);
  - law-averaged: `tvSup_comp_le_integral`, an integrable majorant `e` with
    `tvSup (κ x) (η x) ≤ e x` for `μ`-a.e. `x` gives `tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ∫ e dμ`.
    A majorant is used because measurability of `x ↦ tvSup (κ x) (η x)` (a supremum over an
    uncountable family of sets) is not available on a general measurable space.
* KR-1 one-step certificates combining input mismatch and kernel error:
  `tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + (kernel error)`, where the kernel error is
  `ε` (`tvSup_comp_comp_le_of_forall`), `∫ e dν` averaged under the law `ν` fed to the
  approximate kernel `η` (`tvSup_comp_comp_le_integral_approx`), or `∫ e dμ` averaged under the
  law `μ` fed to the exact kernel `κ` (`tvSup_comp_comp_le_integral_exact`).
* KR-1 telescoping for an exact chain `μ (n+1) = κ n ∘ₘ μ n` and an approximate chain
  `ν (n+1) = η n ∘ₘ ν n` started from probability laws:
  `tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} err k`, with `err k` equal to
  - a uniform bound `ε k` (`tvSup_chain_le_sum`),
  - `∫ e k d(ν k)`, averaged under the **approximate** chain's law
    (`tvSup_chain_le_sum_integral_approx`),
  - `∫ e k d(μ k)`, averaged under the **exact** chain's law
    (`tvSup_chain_le_sum_integral_exact`).
* Invariant-target corollaries: if `π` is invariant for every exact kernel `κ k`, then
  `tvSup (ν n) π ≤ tvSup (ν 0) π + ∑_{k<n} err k` with `err k = ε k`
  (`tvSup_le_of_invariant`), `∫ e k d(ν k)` (`tvSup_le_of_invariant_integral_approx`) or
  `∫ e k dπ` (`tvSup_le_of_invariant_integral_exact`).

Registry: KR-1 (composable total-variation error certificates for sampling chains).

## Not proved here

* No mixing / geometric contraction (Dobrushin coefficient `< 1`) is proved; the contraction
  factor used is `1`, so errors accumulate additively without decay.
* Nothing is said about measurability of `x ↦ tvSup (κ x) (η x)`; averaged bounds are stated
  with an explicit integrable majorant `e`.
* Kernels are assumed Markov (probability kernels); sub-Markov or finite kernels are not treated.
* No specific sampler (ULA, MALA, RTK, proximal, rdMC) is instantiated here, and no per-step
  error bound `ε` or `e` is derived from score or discretisation errors (that is GI-1 and
  the three-chain decomposition of KR-1).
-/

public section

open MeasureTheory
open ProbabilityTheory Finset
open scoped ENNReal

namespace FormalizeSampling
namespace ErrorPropagation

open TotalVariation

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- For a finite kernel `κ`, any measure `μ` and a measurable set `A`,
`(κ ∘ₘ μ)(A) = ∫ κ(x, A) dμ(x)` as real numbers. -/
theorem measureReal_comp_apply (κ : Kernel α β) [IsFiniteKernel κ] (μ : Measure α)
    {s : Set β} (hs : MeasurableSet s) : (κ ∘ₘ μ).real s = ∫ x, (κ x).real s ∂μ := by
  rw [measureReal_def, Measure.bind_apply hs κ.aemeasurable,
    ← integral_toReal (κ.measurable_coe hs).aemeasurable
      (Filter.Eventually.of_forall fun x => measure_lt_top (κ x) s)]
  rfl

/-- For a Markov kernel and a measurable set `A`, `x ↦ κ(x, A)` is measurable with values in
`[0, 1]`, hence integrable for every finite measure. -/
private lemma integrable_measureReal (κ : Kernel α β) [IsMarkovKernel κ] (μ : Measure α)
    [IsFiniteMeasure μ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x).real s) μ :=
  Integrable.of_bound (κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)

/-- **KR-1, TV contraction.** For a Markov kernel `κ : Kernel α β` and finite measures
`μ ν` on `α`, `tvSup (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvSup μ ν`. -/
theorem tvSup_comp_le (κ : Kernel α β) [IsMarkovKernel κ] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : tvSup (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvSup μ ν :=
  tvSup_le_of_forall fun s hs => by
    rw [measureReal_comp_apply κ μ hs, measureReal_comp_apply κ ν hs]
    exact abs_integral_sub_integral_le_tvSup (κ.measurable_coe hs).ennreal_toReal
      (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)

/-- **Law-averaged kernel perturbation.** Let `κ η : Kernel α β` be Markov kernels, `μ` a finite
measure, and `e : α → ℝ` an integrable function (in particular a.e.-strongly measurable) with
`tvSup (κ x) (η x) ≤ e x` for `μ`-almost every `x`. Then
`tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ∫ e dμ`. The majorant `e` replaces the function
`x ↦ tvSup (κ x) (η x)`, whose measurability is not known on a general measurable space. -/
theorem tvSup_comp_le_integral (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure α) [IsFiniteMeasure μ] {e : α → ℝ} (he : Integrable e μ)
    (h : ∀ᵐ x ∂μ, tvSup (κ x) (η x) ≤ e x) : tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ∫ x, e x ∂μ :=
  tvSup_le_of_forall fun s hs => by
    rw [measureReal_comp_apply κ μ hs, measureReal_comp_apply η μ hs,
      ← integral_sub (integrable_measureReal κ μ hs) (integrable_measureReal η μ hs),
      ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le he (h.mono fun x hx => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_measureReal_sub_le_tvSup hs).trans hx

/-- **Uniform kernel perturbation.** For Markov kernels `κ η : Kernel α β` with
`tvSup (κ x) (η x) ≤ ε` for every `x`, and a probability measure `μ`,
`tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ε`. -/
theorem tvSup_comp_le_of_forall (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure α) [IsProbabilityMeasure μ] {ε : ℝ} (h : ∀ x, tvSup (κ x) (η x) ≤ ε) :
    tvSup (κ ∘ₘ μ) (η ∘ₘ μ) ≤ ε := by
  simpa using tvSup_comp_le_integral κ η μ (integrable_const ε) (Filter.Eventually.of_forall h)

/-- **One-step certificate, error averaged under the approximate input law (KR-1).** For Markov
kernels `κ η : Kernel α β`, finite measures `μ ν`, and an integrable `e` with
`tvSup (κ x) (η x) ≤ e x` for `ν`-a.e. `x`,
`tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + ∫ e dν`. Here `ν` is the law fed to the approximate
kernel `η`. -/
theorem tvSup_comp_comp_le_integral_approx (κ η : Kernel α β) [IsMarkovKernel κ]
    [IsMarkovKernel η] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {e : α → ℝ}
    (he : Integrable e ν) (h : ∀ᵐ x ∂ν, tvSup (κ x) (η x) ≤ e x) :
    tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + ∫ x, e x ∂ν :=
  (tvSup_triangle _ (κ ∘ₘ ν) _).trans
    (add_le_add (tvSup_comp_le κ μ ν) (tvSup_comp_le_integral κ η ν he h))

/-- **One-step certificate, error averaged under the exact input law (KR-1).** For Markov
kernels `κ η : Kernel α β`, finite measures `μ ν`, and an integrable `e` with
`tvSup (κ x) (η x) ≤ e x` for `μ`-a.e. `x`,
`tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + ∫ e dμ`. Here `μ` is the law fed to the exact
kernel `κ`; the proof uses the contraction of the approximate kernel `η`. -/
theorem tvSup_comp_comp_le_integral_exact (κ η : Kernel α β) [IsMarkovKernel κ]
    [IsMarkovKernel η] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {e : α → ℝ}
    (he : Integrable e μ) (h : ∀ᵐ x ∂μ, tvSup (κ x) (η x) ≤ e x) :
    tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + ∫ x, e x ∂μ := by
  have h1 := tvSup_triangle (κ ∘ₘ μ) (η ∘ₘ μ) (η ∘ₘ ν)
  have h2 := tvSup_comp_le_integral κ η μ he h
  have h3 := tvSup_comp_le η μ ν
  linarith

/-- **One-step certificate, uniform kernel error (KR-1).** For Markov kernels
`κ η : Kernel α β` with `tvSup (κ x) (η x) ≤ ε` for every `x`, a finite measure `μ` and a
probability measure `ν`, `tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + ε`. -/
theorem tvSup_comp_comp_le_of_forall (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {ε : ℝ}
    (h : ∀ x, tvSup (κ x) (η x) ≤ ε) : tvSup (κ ∘ₘ μ) (η ∘ₘ ν) ≤ tvSup μ ν + ε :=
  (tvSup_triangle _ (κ ∘ₘ ν) _).trans
    (add_le_add (tvSup_comp_le κ μ ν) (tvSup_comp_le_of_forall κ η ν h))

/-- The laws `μ n` of a Markov chain `μ (n+1) = κ n ∘ₘ μ n` driven by Markov kernels from a
probability initial law `μ 0` are probability measures. -/
theorem isProbabilityMeasure_of_comp_succ {κ : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)]
    {μ : ℕ → Measure α} [IsProbabilityMeasure (μ 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (n : ℕ) : IsProbabilityMeasure (μ n) := by
  induction n with
  | zero => infer_instance
  | succ n ih => rw [hμ n]; infer_instance

/-- **KR-1, telescoping with uniform per-step errors.** Let `κ η : ℕ → Kernel α α` be Markov
kernels (exact and approximate), and `μ ν : ℕ → Measure α` the laws of the two chains,
`μ (n+1) = κ n ∘ₘ μ n`, `ν (n+1) = η n ∘ₘ ν n`, with probability initial laws `μ 0`, `ν 0`.
If `tvSup (κ k x) (η k x) ≤ ε k` for every step `k` and every state `x`, then for all `n`,
`tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} ε k`. No law enters the error terms. -/
theorem tvSup_chain_le_sum {κ η : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)]
    [∀ n, IsMarkovKernel (η n)] {μ ν : ℕ → Measure α} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {ε : ℕ → ℝ} (h : ∀ n x, tvSup (κ n x) (η n x) ≤ ε n)
    (n : ℕ) : tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑ k ∈ range n, ε k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_of_comp_succ hμ n
    have := isProbabilityMeasure_of_comp_succ hν n
    have h1 := tvSup_comp_comp_le_of_forall (κ n) (η n) (μ n) (ν n) (h n)
    rw [← hμ n, ← hν n] at h1
    rw [sum_range_succ]
    linarith

/-- **KR-1, telescoping with errors averaged under the approximate chain's law.** With the
chains of `tvSup_chain_le_sum`, let `e k : α → ℝ` be integrable with respect to `ν k` (the
law of the **approximate** chain at step `k`) and satisfy `tvSup (κ k x) (η k x) ≤ e k x` for
`ν k`-a.e. `x`. Then
`tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} ∫ e k d(ν k)`. -/
theorem tvSup_chain_le_sum_integral_approx {κ η : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)]
    [∀ n, IsMarkovKernel (η n)] {μ ν : ℕ → Measure α} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {e : ℕ → α → ℝ} (he : ∀ n, Integrable (e n) (ν n))
    (h : ∀ n, ∀ᵐ x ∂(ν n), tvSup (κ n x) (η n x) ≤ e n x) (n : ℕ) :
    tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑ k ∈ range n, ∫ x, e k x ∂(ν k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_of_comp_succ hμ n
    have := isProbabilityMeasure_of_comp_succ hν n
    have h1 := tvSup_comp_comp_le_integral_approx (κ n) (η n) (μ n) (ν n) (he n) (h n)
    rw [← hμ n, ← hν n] at h1
    rw [sum_range_succ]
    linarith

/-- **KR-1, telescoping with errors averaged under the exact chain's law.** With the chains of
`tvSup_chain_le_sum`, let `e k : α → ℝ` be integrable with respect to `μ k` (the law of the
**exact** chain at step `k`) and satisfy `tvSup (κ k x) (η k x) ≤ e k x` for `μ k`-a.e. `x`.
Then `tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑_{k<n} ∫ e k d(μ k)`. -/
theorem tvSup_chain_le_sum_integral_exact {κ η : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)]
    [∀ n, IsMarkovKernel (η n)] {μ ν : ℕ → Measure α} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ n, μ (n + 1) = κ n ∘ₘ μ n)
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {e : ℕ → α → ℝ} (he : ∀ n, Integrable (e n) (μ n))
    (h : ∀ n, ∀ᵐ x ∂(μ n), tvSup (κ n x) (η n x) ≤ e n x) (n : ℕ) :
    tvSup (μ n) (ν n) ≤ tvSup (μ 0) (ν 0) + ∑ k ∈ range n, ∫ x, e k x ∂(μ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_of_comp_succ hμ n
    have := isProbabilityMeasure_of_comp_succ hν n
    have h1 := tvSup_comp_comp_le_integral_exact (κ n) (η n) (μ n) (ν n) (he n) (h n)
    rw [← hμ n, ← hν n] at h1
    rw [sum_range_succ]
    linarith

/-- **Invariant target, uniform errors.** Let `π` be a probability measure invariant for every
exact Markov kernel `κ k` (`κ k ∘ₘ π = π`), and let `ν (n+1) = η n ∘ₘ ν n` be the approximate
chain from a probability law `ν 0`, with `tvSup (κ k x) (η k x) ≤ ε k` for all `k`, `x`. Then
`tvSup (ν n) π ≤ tvSup (ν 0) π + ∑_{k<n} ε k`. -/
theorem tvSup_le_of_invariant {κ η : ℕ → Kernel α α} [∀ n, IsMarkovKernel (κ n)]
    [∀ n, IsMarkovKernel (η n)] {π : Measure α} [IsProbabilityMeasure π]
    (hπ : ∀ n, (κ n).Invariant π) {ν : ℕ → Measure α} [IsProbabilityMeasure (ν 0)]
    (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {ε : ℕ → ℝ} (h : ∀ n x, tvSup (κ n x) (η n x) ≤ ε n)
    (n : ℕ) : tvSup (ν n) π ≤ tvSup (ν 0) π + ∑ k ∈ range n, ε k := by
  have h1 := tvSup_chain_le_sum (μ := fun _ => π) (fun k => (hπ k).symm) hν h n
  rwa [tvSup_comm, tvSup_comm π] at h1

/-- **Invariant target, errors averaged under the approximate chain's law.** With `π`, `κ`, `η`
and `ν` as in `tvSup_le_of_invariant`, let `e k` be `ν k`-integrable with
`tvSup (κ k x) (η k x) ≤ e k x` for `ν k`-a.e. `x`. Then
`tvSup (ν n) π ≤ tvSup (ν 0) π + ∑_{k<n} ∫ e k d(ν k)`. -/
theorem tvSup_le_of_invariant_integral_approx {κ η : ℕ → Kernel α α}
    [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)] {π : Measure α}
    [IsProbabilityMeasure π] (hπ : ∀ n, (κ n).Invariant π) {ν : ℕ → Measure α}
    [IsProbabilityMeasure (ν 0)] (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {e : ℕ → α → ℝ}
    (he : ∀ n, Integrable (e n) (ν n)) (h : ∀ n, ∀ᵐ x ∂(ν n), tvSup (κ n x) (η n x) ≤ e n x)
    (n : ℕ) : tvSup (ν n) π ≤ tvSup (ν 0) π + ∑ k ∈ range n, ∫ x, e k x ∂(ν k) := by
  have h1 := tvSup_chain_le_sum_integral_approx (μ := fun _ => π) (fun k => (hπ k).symm) hν
    he h n
  rwa [tvSup_comm, tvSup_comm π] at h1

/-- **Invariant target, errors averaged under the target.** With `π`, `κ`, `η` and `ν` as in
`tvSup_le_of_invariant`, let `e k` be `π`-integrable with `tvSup (κ k x) (η k x) ≤ e k x` for
`π`-a.e. `x`. Then `tvSup (ν n) π ≤ tvSup (ν 0) π + ∑_{k<n} ∫ e k dπ`: the per-step kernel
errors only need to be controlled on average under the invariant law `π`. -/
theorem tvSup_le_of_invariant_integral_exact {κ η : ℕ → Kernel α α}
    [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)] {π : Measure α}
    [IsProbabilityMeasure π] (hπ : ∀ n, (κ n).Invariant π) {ν : ℕ → Measure α}
    [IsProbabilityMeasure (ν 0)] (hν : ∀ n, ν (n + 1) = η n ∘ₘ ν n) {e : ℕ → α → ℝ}
    (he : ∀ n, Integrable (e n) π) (h : ∀ n, ∀ᵐ x ∂π, tvSup (κ n x) (η n x) ≤ e n x)
    (n : ℕ) : tvSup (ν n) π ≤ tvSup (ν 0) π + ∑ k ∈ range n, ∫ x, e k x ∂π := by
  have h1 := tvSup_chain_le_sum_integral_exact (μ := fun _ => π) (fun k => (hπ k).symm) hν
    he h n
  rwa [tvSup_comm, tvSup_comm π] at h1

end ErrorPropagation
end FormalizeSampling
