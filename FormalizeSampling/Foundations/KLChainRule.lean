module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# KL chain rule in integrated form and KL propagation along Markov chains

Kullback–Leibler divergence `klDiv μ ν = KL(μ ‖ ν)` is Mathlib's
`InformationTheory.klDiv`, valued in `ℝ≥0∞` (it is `∞` unless `μ ≪ ν` and the log-likelihood
ratio is `μ`-integrable). `κ ∘ₘ μ` is the law of `X₁ ~ κ(X₀, ·)` when `X₀ ~ μ`, and
`μ ⊗ₘ κ` is the joint law of `(X₀, X₁)`.

## Conventions

* **Direction.** Every statement is about `KL(first ‖ second)`. In the chain results the
  *first* argument is the chain driven by the kernels `Q k` with laws `ν k` (typically the
  algorithm), the *second* is the chain driven by `P k` with laws `μ k` (typically the exact
  chain).
* **Averaging law.** The per-step kernel error `x ↦ KL(Q k x ‖ P k x)` is averaged under the law
  `ν k` of the chain appearing in the **first** argument. Since the two chains play symmetric
  roles, exchanging them gives `KL(μ n ‖ ν n)` with errors `KL(P k x ‖ Q k x)` averaged under
  `μ k`; no separate statement is needed.

## Main results

* KL-2, integrated chain rule (ported from Lean Machine Learning, see below):
  - `measurable_klDiv_kernel`: `a ↦ KL(κ a ‖ η a)` is measurable (finite kernels,
    `CountableOrCountablyGenerated α β`);
  - `klDiv_compProd_right_eq_lintegral`: `KL(μ ⊗ₘ κ ‖ μ ⊗ₘ η) = ∫⁻ a, KL(κ a ‖ η a) ∂μ`;
  - `klDiv_compProd_eq_add_lintegral`:
    `KL(μ ⊗ₘ κ ‖ ν ⊗ₘ η) = KL(μ ‖ ν) + ∫⁻ a, KL(κ a ‖ η a) ∂μ` (Markov kernels);
  - `klDiv_comp_le_compProd`: data processing for the second marginal,
    `KL(κ ∘ₘ μ ‖ η ∘ₘ ν) ≤ KL(μ ⊗ₘ κ ‖ ν ⊗ₘ η)`.
* KL propagation along two Markov chains (foundation of GI-1):
  - `klDiv_comp_comp_le`: one step,
    `KL(Q ∘ₘ ν ‖ P ∘ₘ μ) ≤ KL(ν ‖ μ) + ∫⁻ x, KL(Q x ‖ P x) ∂ν`;
  - `klDiv_chain_le_sum`: for `μ (k+1) = P k ∘ₘ μ k`, `ν (k+1) = Q k ∘ₘ ν k`,
    `KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ x, KL(Q k x ‖ P k x) ∂(ν k)`.
* The Gaussian-increment instance (GI-1) is in `Samplers/GaussianIncrement.lean`
  (`klDiv_emChain_le_sum`, `tvSup_emChain_le_sqrt_klDiv_sum`).

## Credit

The integrated chain rule (`measurable_klDiv_kernel`, `klDiv_compProd_right_eq_lintegral`,
`klDiv_compProd_eq_add_lintegral`, `klDiv_comp_le_compProd`) is ported from Lean Machine
Learning (LML), file `LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/
ChainRule.lean`, Copyright (c) 2026 Rémy Degenne, released under the Apache 2.0 license
(https://github.com/LeanMachineLearning/LML). The kernel helper lemmas it needs are already in
Mathlib v4.35, so only the statements above were ported.

## Not proved here

* Measurability of `x ↦ KL(Q x ‖ P x)` requires `CountableOrCountablyGenerated α α`
  (e.g. a standard Borel space such as `ℝ`); general measurable spaces are not treated.
-/

public section

open MeasureTheory ProbabilityTheory Finset InformationTheory
open scoped ENNReal NNReal

namespace FormalizeSampling
namespace KL

/-! ### Integrated chain rule (ported from LML) -/

section ChainRule

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- **Data processing for the second projection** (ported from LML). For finite measures `μ ν`
and finite kernels `κ η`, `κ ∘ₘ μ` and `η ∘ₘ ν` are the images of `μ ⊗ₘ κ` and `ν ⊗ₘ η` under
`Prod.snd`, hence `KL(κ ∘ₘ μ ‖ η ∘ₘ ν) ≤ KL(μ ⊗ₘ κ ‖ ν ⊗ₘ η)`. No assumption on the spaces. -/
theorem klDiv_comp_le_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  rw [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν η, Measure.snd, Measure.snd]
  exact klDiv_map_le _ _ measurable_snd

variable [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- **Measurability of the pointwise kernel KL** (ported from LML). For finite kernels
`κ η : Kernel α β` with `α` countable or `β` countably generated, the map
`a ↦ KL(κ a ‖ η a)` is measurable (as an `ℝ≥0∞`-valued function). -/
theorem measurable_klDiv_kernel (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable fun a ↦ klDiv (κ a) (η a) := by
  classical
  have h_meas : Measurable fun a ↦
      ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂(η a) :=
    Measurable.lintegral_kernel_prod_right
      ((measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal)
  have h_eq : ∀ a, klDiv (κ a) (η a) = if κ a ≪ η a then
      ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂(η a) else ∞ := by
    intro a
    split_ifs with hac
    · rw [klDiv_eq_lintegral_klFun_of_ac hac]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
      rw [hb]
    · exact klDiv_of_not_ac hac
  simp_rw [h_eq]
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η) h_meas measurable_const

/-- **Conditional KL as an integral** (ported from LML). For a finite measure `μ` and finite
kernels `κ η` (`α` countable or `β` countably generated),
`KL(μ ⊗ₘ κ ‖ μ ⊗ₘ η) = ∫⁻ a, KL(κ a ‖ η a) ∂μ`: the pointwise kernel KL averaged under the
common input law `μ`. -/
theorem klDiv_compProd_right_eq_lintegral (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η
  · rw [klDiv_eq_lintegral_klFun_of_ac h_ac]
    have h_ae := Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
    calc ∫⁻ p, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ η)
        = ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(μ ⊗ₘ η) := by
          refine lintegral_congr_ae ?_
          filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
          rw [hp]
      _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂(η a) ∂μ :=
          Measure.lintegral_compProd
            ((measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal)
      _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [h_ae] with a ha
          rw [klDiv_eq_lintegral_klFun_of_ac ha]
          refine lintegral_congr_ae ?_
          filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
          rw [hb]
  · rw [klDiv_of_not_ac h_ac, Measure.absolutelyContinuous_compProd_right_iff, ae_iff] at *
    symm
    rw [eq_top_iff]
    calc (∞ : ℝ≥0∞) = ∫⁻ _ in {a | ¬ κ a ≪ η a}, ∞ ∂μ := by
          rw [setLIntegral_const, ENNReal.top_mul h_ac]
      _ ≤ ∫⁻ a in {a | ¬ κ a ≪ η a}, klDiv (κ a) (η a) ∂μ :=
          setLIntegral_mono' (Kernel.measurableSet_absolutelyContinuous κ η).compl
            fun a ha ↦ by rw [klDiv_of_not_ac ha]
      _ ≤ ∫⁻ a, klDiv (κ a) (η a) ∂μ := setLIntegral_le_lintegral _ _

/-- **KL chain rule, integrated form** (KL-2; ported from LML). For finite measures `μ ν` and
Markov kernels `κ η` (`α` countable or `β` countably generated),
`KL(μ ⊗ₘ κ ‖ ν ⊗ₘ η) = KL(μ ‖ ν) + ∫⁻ a, KL(κ a ‖ η a) ∂μ`; the kernel term is averaged under
the first argument's input law `μ`. -/
theorem klDiv_compProd_eq_add_lintegral (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_right_eq_lintegral]

/-- **One-step KL propagation.** For finite measures `ν μ` and Markov kernels `Q P`
(`α` countable or `β` countably generated),
`KL(Q ∘ₘ ν ‖ P ∘ₘ μ) ≤ KL(ν ‖ μ) + ∫⁻ x, KL(Q x ‖ P x) ∂ν`: the kernel error is averaged under
the input law `ν` of the **first** argument. Exchanging the roles of `(ν, Q)` and `(μ, P)` gives
the bound for `KL(P ∘ₘ μ ‖ Q ∘ₘ ν)` with the error `KL(P x ‖ Q x)` averaged under `μ`. -/
theorem klDiv_comp_comp_le (ν μ : Measure α) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (Q P : Kernel α β) [IsMarkovKernel Q] [IsMarkovKernel P] :
    klDiv (Q ∘ₘ ν) (P ∘ₘ μ) ≤ klDiv ν μ + ∫⁻ x, klDiv (Q x) (P x) ∂ν :=
  (klDiv_comp_le_compProd ν μ Q P).trans_eq (klDiv_compProd_eq_add_lintegral ν μ Q P)

end ChainRule

/-! ### KL propagation along two Markov chains -/

section Chain

variable {α : Type*} {mα : MeasurableSpace α} [MeasurableSpace.CountableOrCountablyGenerated α α]

/-- **KL propagation along two Markov chains** (foundation of GI-1). Let `P Q : ℕ → Kernel α α`
be Markov kernels on a space with `CountableOrCountablyGenerated α α` (e.g. a standard Borel
space), and let `μ ν : ℕ → Measure α` be finite measures with `μ (k+1) = P k ∘ₘ μ k` and
`ν (k+1) = Q k ∘ₘ ν k`. Then for every `n`,
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ x, KL(Q k x ‖ P k x) ∂(ν k)`.
Direction: the `Q`-chain `ν` is the **first** argument of KL, and the per-step kernel errors are
averaged under its laws `ν k`. Since the hypotheses are symmetric in the two chains, applying the
theorem with the roles exchanged bounds `KL(μ n ‖ ν n)` with errors `KL(P k x ‖ Q k x)` averaged
under the other chain's laws `μ k`. -/
theorem klDiv_chain_le_sum (P Q : ℕ → Kernel α α) [∀ k, IsMarkovKernel (P k)]
    [∀ k, IsMarkovKernel (Q k)] (μ ν : ℕ → Measure α) [∀ k, IsFiniteMeasure (μ k)]
    [∀ k, IsFiniteMeasure (ν k)] (hμ : ∀ k, μ (k + 1) = P k ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = Q k ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤
      klDiv (ν 0) (μ 0) + ∑ k ∈ range n, ∫⁻ x, klDiv (Q k x) (P k x) ∂(ν k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hμ, hν, sum_range_succ, ← add_assoc]
    exact (klDiv_comp_comp_le (ν n) (μ n) (Q n) (P n)).trans (by gcongr)

end Chain

end KL
end FormalizeSampling
