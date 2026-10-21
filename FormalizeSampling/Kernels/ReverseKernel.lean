module

public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Posterior

/-!
# Reverse (Bayes) kernels: posterior form and density form

This file formalises the *exact reverse kernel* of one forward Markov step and of a chain of
forward steps, in two complementary forms.

## Reverse-time reading

A forward step draws `x ~ μ` and then `y ~ κ x`; its joint law is `μ ⊗ₘ κ` and its output law
is `κ ∘ₘ μ`. A *reverse kernel* `η` runs the step backwards: draw `y ~ κ ∘ₘ μ`, then
`x ~ η y`. It is exact when the reversed joint law is the forward joint law with coordinates
swapped, `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap` (`IsReverseKernel`). Mathlib's posterior
`κ†μ` (`ProbabilityTheory.posterior`, defined by disintegration) is such a kernel whenever the
parameter space is standard Borel.

## Main results

* (A) Abstract form, registry **KR-2**:
  `compProd_posterior_eq` (joint-law identity), `posterior_comp_marginal` and
  `IsReverseKernel.comp_marginal` (the reverse step maps the output law back to `μ`),
  `IsReverseKernel.ae_eq_posterior` and `isReverseKernel_iff_ae_eq_posterior` (a reverse kernel
  is unique **only up to a `κ ∘ₘ μ`-null set**), and the counterexample
  `exists_isReverseKernel_ne` (two different reverse kernels for the same forward step).
* (A) Composition, registry **KR-2**: `IsReverseKernel.two_step_comp_marginal`,
  `two_step_reverse_marginal`, `two_step_posterior_comp`; for `n` steps on one standard Borel
  space, the forward marginals `forwardMarginal` are built into the definition of the reverse
  steps `reverseStep n = (κ n)†(forwardMarginal κ μ₀ n)`, and we prove
  `reverseSegment_comp_forwardMarginal`, `reverseChain_comp_forwardMarginal` (running all reverse
  steps from the time-`n` law returns `μ₀`) and `reverseChain_ae_eq_posterior` (the composite of
  the exact reverse steps is a.e. the posterior of the composite forward kernel).
* (B) Density form, registry **KR-2**, with no standard-Borel assumption: for s-finite
  reference measures `ν` on `X` and `ρ` on `Y` (σ-finite measures are s-finite; `ρ` plays the
  role often written `λ`), a prior density `p : X → ℝ≥0∞` and a jointly measurable
  forward density `k : X → Y → ℝ≥0∞`, we set
  `marginalDensity ν p k y = ∫⁻ x, p x * k x y ∂ν` and
  `reverseDensity ν p k y x = p x * k x y / marginalDensity ν p k y`. We prove the joint
  symmetry `p x * k x y = m y * r y x` when `0 < m y < ∞`
  (`joint_density_eq_mul_reverseDensity`), its almost-everywhere versions and the nullity of the
  exceptional sets `{m = 0}`, `{m = ∞}` for the output law (under `∫⁻ p ≠ ∞` and
  `∫⁻ y, k x y ∂ρ = 1`), the measure-level joint identity `joint_map_swap`, marginal recovery
  `lintegral_marginalDensity_mul_setLIntegral_reverseDensity`, the forward-then-reverse
  invariance `lintegral_forward_reverse_setLIntegral`, and the kernel-level statements
  `isReverseKernel_densityKernel` and `densityKernel_reverseDensity_ae_eq_posterior` linking (B)
  to (A).

## Conventions

`κ ∘ₘ μ` is `Measure.bind`, `μ ⊗ₘ κ` is `Measure.compProd`, `η ∘ₖ κ` runs `κ` first. In ENNReal
`a / 0 = ∞` for `a ≠ 0` and `a / ∞ = 0` for `a ≠ ∞`; the reverse density is therefore only
meaningful where `0 < m y < ∞`, and every statement below either assumes this pointwise or
proves that the exceptional set is null.

## Not proved here

* Pointwise (everywhere) uniqueness of reverse kernels is false (`exists_isReverseKernel_ne`);
  only a.e. uniqueness is proved.
* Error propagation for *approximate* reverse kernels (TV non-expansiveness, KR-1) is not
  treated here.
* The density form uses ENNReal densities and lintegrals; no Bochner-integral (real-valued)
  version, and no statement for reverse kernels of continuous-time diffusions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FormalizeSampling.ReverseKernel

/-! ## (A) Abstract reverse kernels (KR-2) -/

section Abstract

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {mX : MeasurableSpace X}

/-- `η : Kernel X Ω` is an *exact reverse kernel* of the forward step `x ~ μ`, `y ~ κ x`: the
reversed joint law `(κ ∘ₘ μ) ⊗ₘ η` (draw `y` from the output law, then `x ~ η y`) equals the
forward joint law `μ ⊗ₘ κ` with its coordinates swapped. This is the defining property of a Bayes
posterior; it is a property of `η` only up to `κ ∘ₘ μ`-null sets. -/
def IsReverseKernel (κ : Kernel Ω X) (μ : Measure Ω) (η : Kernel X Ω) : Prop :=
  (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap

/-- **Marginal recovery for any reverse kernel.** If `κ` is Markov, `μ` is s-finite, `η` is
s-finite and `η` is an exact reverse kernel of `(κ, μ)`, then running the reverse step from the
output law gives back the input law: `η ∘ₘ (κ ∘ₘ μ) = μ`. No standard-Borel assumption. -/
theorem IsReverseKernel.comp_marginal {κ : Kernel Ω X} {μ : Measure Ω} {η : Kernel X Ω}
    [SFinite μ] [IsMarkovKernel κ] [IsSFiniteKernel η] (h : IsReverseKernel κ μ η) :
    η ∘ₘ (κ ∘ₘ μ) = μ := by
  rw [← Measure.snd_compProd, h, Measure.snd_map_swap, Measure.fst_compProd]

/-- **Reverse kernels are only determined up to null sets.** If `η` is an exact reverse kernel
of `(κ, μ)` and `η'` (both s-finite) agrees with `η` for `κ ∘ₘ μ`-almost every `y`, then `η'` is
also an exact reverse kernel; its values on a `κ ∘ₘ μ`-null set are arbitrary. -/
theorem isReverseKernel_of_ae_eq {κ : Kernel Ω X} {μ : Measure Ω} {η η' : Kernel X Ω}
    [IsSFiniteKernel η] [IsSFiniteKernel η'] (h : IsReverseKernel κ μ η)
    (h' : η =ᵐ[κ ∘ₘ μ] η') : IsReverseKernel κ μ η' := by
  unfold IsReverseKernel at *
  rw [← Measure.compProd_congr h', h]

/-- The identity kernel is an exact reverse kernel of the identity step, for every s-finite
`μ`: `(id ∘ₘ μ) ⊗ₘ id = (μ ⊗ₘ id).map swap`. -/
theorem isReverseKernel_id (μ : Measure Ω) [SFinite μ] :
    IsReverseKernel (Kernel.id : Kernel Ω Ω) μ Kernel.id := by
  unfold IsReverseKernel
  rw [Measure.id_comp, Measure.compProd_id_eq_copy_comp, ← Measure.swap_comp, Measure.comp_assoc,
    Kernel.swap_copy]

/-- Composition on the right preserves a.e. equality transported through a kernel: if
`A =ᵐ[R ∘ₘ ν] B` then `A ∘ₖ R =ᵐ[ν] B ∘ₖ R`. (Used to compose reverse kernels.) -/
theorem comp_ae_eq_comp_of_ae_eq {Y Z : Type*} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
    {A B : Kernel Y Z} {R : Kernel Ω Y} {ν : Measure Ω} (h : A =ᵐ[R ∘ₘ ν] B) :
    A ∘ₖ R =ᵐ[ν] B ∘ₖ R := by
  filter_upwards [Measure.ae_ae_of_ae_comp h] with y hy
  rw [Kernel.comp_apply, Kernel.comp_apply]
  exact Measure.comp_congr hy

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- **Joint-law identity for the posterior (KR-2).** For a finite measure `μ` on a nonempty
standard Borel space `Ω` and a finite kernel `κ : Kernel Ω X`, Mathlib's posterior `κ†μ`
satisfies `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`: forward step `x → y` by `κ`, reverse step
`y → x` by `κ†μ`, same joint law. -/
theorem compProd_posterior_eq (κ : Kernel Ω X) (μ : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] : (κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap :=
  compProd_posterior_eq_map_swap

/-- The posterior `κ†μ` is an exact reverse kernel (finite `μ` on a nonempty standard Borel
space, finite `κ`). -/
theorem isReverseKernel_posterior (κ : Kernel Ω X) (μ : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] : IsReverseKernel κ μ (κ†μ) :=
  compProd_posterior_eq_map_swap

/-- **Marginal recovery (KR-2).** For a Markov kernel `κ` and a finite measure `μ` on a
nonempty standard Borel space, the reverse step maps the output law back to the input law:
`κ†μ ∘ₘ (κ ∘ₘ μ) = μ`. -/
theorem posterior_comp_marginal (κ : Kernel Ω X) (μ : Measure Ω) [IsFiniteMeasure μ]
    [IsMarkovKernel κ] : κ†μ ∘ₘ (κ ∘ₘ μ) = μ :=
  posterior_comp_self

/-- **A.e. uniqueness of the reverse kernel (KR-2).** Any finite kernel `η` satisfying the
joint-law identity agrees with the posterior `κ†μ` for `κ ∘ₘ μ`-almost every `y` (finite `μ` on a
nonempty standard Borel space, finite `κ`). Uniqueness holds **only up to null sets**. -/
theorem IsReverseKernel.ae_eq_posterior {κ : Kernel Ω X} {μ : Measure Ω} [IsFiniteMeasure μ]
    [IsFiniteKernel κ] {η : Kernel X Ω} [IsFiniteKernel η] (h : IsReverseKernel κ μ η) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
  ae_eq_posterior_of_compProd_eq h

/-- **Characterisation of reverse kernels (KR-2).** For finite `μ` on a nonempty standard
Borel space and finite kernels `κ`, `η`: `η` is an exact reverse kernel iff `η = κ†μ` holds
`κ ∘ₘ μ`-almost everywhere. -/
theorem isReverseKernel_iff_ae_eq_posterior {κ : Kernel Ω X} {μ : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] {η : Kernel X Ω} [IsFiniteKernel η] :
    IsReverseKernel κ μ η ↔ η =ᵐ[κ ∘ₘ μ] κ†μ :=
  ⟨fun h => h.ae_eq_posterior, fun h =>
    isReverseKernel_of_ae_eq (isReverseKernel_posterior κ μ) h.symm⟩

/-- The posterior only depends on the prior measure, not on the proof of its finiteness:
`μ = μ' → κ†μ = κ†μ'`. -/
theorem posterior_congr_measure (κ : Kernel Ω X) [IsFiniteKernel κ] {μ μ' : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] (h : μ = μ') : κ†μ = κ†μ' := by
  subst h; rfl

end Abstract

/-- **Counterexample: reverse kernels are not unique pointwise.** On `Bool`, for the identity
step started from `μ = δ_false`, both the identity kernel and the constant kernel `δ_false` are
exact (Markov) reverse kernels, yet they differ (at `true`, a `κ ∘ₘ μ`-null point). -/
theorem exists_isReverseKernel_ne :
    ∃ (κ : Kernel Bool Bool) (μ : Measure Bool) (η₁ η₂ : Kernel Bool Bool),
      IsProbabilityMeasure μ ∧ IsMarkovKernel κ ∧ IsMarkovKernel η₁ ∧ IsMarkovKernel η₂ ∧
      IsReverseKernel κ μ η₁ ∧ IsReverseKernel κ μ η₂ ∧ η₁ ≠ η₂ := by
  refine ⟨Kernel.id, Measure.dirac false, Kernel.id, Kernel.const Bool (Measure.dirac false),
    inferInstance, inferInstance, inferInstance, inferInstance, isReverseKernel_id _, ?_, ?_⟩
  · refine isReverseKernel_of_ae_eq (isReverseKernel_id _) ?_
    rw [Measure.id_comp, Filter.EventuallyEq, ae_dirac_iff]
    · simp [Kernel.id_apply]
    · exact MeasurableSet.of_discrete
  · intro h
    have h1 := DFunLike.congr_fun h true
    simp only [Kernel.id_apply, Kernel.const_apply] at h1
    have := congrArg (fun m : Measure Bool => m {true}) h1
    simp at this

/-! ## (A) Composition of exact reverse kernels (KR-2) -/

section TwoStep

variable {Ω₀ Ω₁ Ω₂ : Type*} {m₀ : MeasurableSpace Ω₀} {m₁ : MeasurableSpace Ω₁}
  {m₂ : MeasurableSpace Ω₂}

/-- **Two-step composition for arbitrary exact reverse kernels (KR-2).** Let `ν₁ = κ₁ ∘ₘ μ₀`
and `ν₂ = κ₂ ∘ₘ ν₁` (Markov `κ₁`, `κ₂`, s-finite `μ₀`). If `R₁` is an exact reverse kernel of
`(κ₁, μ₀)` and `R₂` one of `(κ₂, ν₁)` (both s-finite), then `(R₁ ∘ₖ R₂) ∘ₘ ν₂ = μ₀`. The
intermediate marginal `ν₁` is the prior used for `R₂`. -/
theorem IsReverseKernel.two_step_comp_marginal {μ₀ : Measure Ω₀} [SFinite μ₀]
    {κ₁ : Kernel Ω₀ Ω₁} [IsMarkovKernel κ₁] {κ₂ : Kernel Ω₁ Ω₂} [IsMarkovKernel κ₂]
    {R₁ : Kernel Ω₁ Ω₀} [IsSFiniteKernel R₁] {R₂ : Kernel Ω₂ Ω₁} [IsSFiniteKernel R₂]
    (h₁ : IsReverseKernel κ₁ μ₀ R₁) (h₂ : IsReverseKernel κ₂ (κ₁ ∘ₘ μ₀) R₂) :
    (R₁ ∘ₖ R₂) ∘ₘ (κ₂ ∘ₘ (κ₁ ∘ₘ μ₀)) = μ₀ := by
  rw [← Measure.comp_assoc, h₂.comp_marginal, h₁.comp_marginal]

variable [StandardBorelSpace Ω₀] [Nonempty Ω₀] [StandardBorelSpace Ω₁] [Nonempty Ω₁]

/-- **Two-step reverse marginal recovery (KR-2).** With `ν₁ = κ₁ ∘ₘ μ₀`, `ν₂ = κ₂ ∘ₘ ν₁`,
`R₂ = κ₂†ν₁` and `R₁ = κ₁†μ₀` (finite `μ₀`, Markov `κ₁`, `κ₂`, standard Borel nonempty `Ω₀`,
`Ω₁`): `R₁ ∘ₘ (R₂ ∘ₘ ν₂) = μ₀`. -/
theorem two_step_reverse_marginal (μ₀ : Measure Ω₀) [IsFiniteMeasure μ₀]
    (κ₁ : Kernel Ω₀ Ω₁) [IsMarkovKernel κ₁] (κ₂ : Kernel Ω₁ Ω₂) [IsMarkovKernel κ₂] :
    κ₁†μ₀ ∘ₘ (κ₂†(κ₁ ∘ₘ μ₀) ∘ₘ (κ₂ ∘ₘ (κ₁ ∘ₘ μ₀))) = μ₀ := by
  rw [posterior_comp_self, posterior_comp_self]

/-- **The composite of exact reverse steps is the reverse of the composite (KR-2).** For
finite `μ₀` and finite kernels `κ₁ : Ω₀ → Ω₁`, `κ₂ : Ω₁ → Ω₂` (standard Borel nonempty `Ω₀`,
`Ω₁`): `(κ₂ ∘ₖ κ₁)†μ₀ = κ₁†μ₀ ∘ₖ κ₂†(κ₁ ∘ₘ μ₀)` for `ν₂`-almost every point, `ν₂ = κ₂ ∘ₘ κ₁ ∘ₘ μ₀`.
-/
theorem two_step_posterior_comp (μ₀ : Measure Ω₀) [IsFiniteMeasure μ₀]
    (κ₁ : Kernel Ω₀ Ω₁) [IsFiniteKernel κ₁] (κ₂ : Kernel Ω₁ Ω₂) [IsFiniteKernel κ₂] :
    (κ₂ ∘ₖ κ₁)†μ₀ =ᵐ[κ₂ ∘ₘ (κ₁ ∘ₘ μ₀)] κ₁†μ₀ ∘ₖ κ₂†(κ₁ ∘ₘ μ₀) :=
  posterior_comp

end TwoStep

section NStep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Forward marginals of a time-inhomogeneous chain with step kernels `κ n : Ω → Ω` started at
`μ₀`: `forwardMarginal κ μ₀ 0 = μ₀` and
`forwardMarginal κ μ₀ (n + 1) = κ n ∘ₘ forwardMarginal κ μ₀ n`. -/
noncomputable def forwardMarginal (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) : ℕ → Measure Ω
  | 0 => μ₀
  | n + 1 => κ n ∘ₘ forwardMarginal κ μ₀ n

/-- The composite forward kernel from time `0` to time `n`: `forwardChain κ 0 = id` and
`forwardChain κ (n + 1) = κ n ∘ₖ forwardChain κ n`. -/
noncomputable def forwardChain (κ : ℕ → Kernel Ω Ω) : ℕ → Kernel Ω Ω
  | 0 => Kernel.id
  | n + 1 => κ n ∘ₖ forwardChain κ n

/-- The time-`0` forward marginal is the initial law. -/
@[simp] theorem forwardMarginal_zero (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) :
    forwardMarginal κ μ₀ 0 = μ₀ := rfl

/-- One forward step: `forwardMarginal κ μ₀ (n + 1) = κ n ∘ₘ forwardMarginal κ μ₀ n`. -/
theorem forwardMarginal_succ (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) (n : ℕ) :
    forwardMarginal κ μ₀ (n + 1) = κ n ∘ₘ forwardMarginal κ μ₀ n := rfl

/-- Forward marginals of a finite initial law under finite kernels are finite. -/
theorem isFiniteMeasure_forwardMarginal (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω)
    [IsFiniteMeasure μ₀] [∀ n, IsFiniteKernel (κ n)] (n : ℕ) :
    IsFiniteMeasure (forwardMarginal κ μ₀ n) := by
  induction n with
  | zero => simpa using inferInstanceAs (IsFiniteMeasure μ₀)
  | succ n ih => rw [forwardMarginal_succ]; infer_instance

/-- The composite of Markov kernels is Markov. -/
theorem isMarkovKernel_forwardChain (κ : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    IsMarkovKernel (forwardChain κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (κ n ∘ₖ forwardChain κ n))

/-- The time-`n` forward marginal is the composite forward kernel applied to `μ₀`. -/
theorem forwardMarginal_eq_forwardChain_comp (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) (n : ℕ) :
    forwardMarginal κ μ₀ n = forwardChain κ n ∘ₘ μ₀ := by
  induction n with
  | zero => exact (Measure.id_comp (μ := μ₀)).symm
  | succ n ih => rw [forwardMarginal_succ, ih, Measure.comp_assoc]; rfl

attribute [local instance] isFiniteMeasure_forwardMarginal isMarkovKernel_forwardChain

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- The exact reverse step from time `n + 1` to time `n`: the posterior of the forward kernel
`κ n` **with respect to the forward marginal at time `n`** (the consistency of intermediate
marginals is built into this definition). -/
noncomputable def reverseStep (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) [IsFiniteMeasure μ₀]
    [∀ n, IsFiniteKernel (κ n)] (n : ℕ) : Kernel Ω Ω :=
  (κ n)†(forwardMarginal κ μ₀ n)

/-- The composite reverse kernel from time `k + j` down to time `k`:
`reverseSegment κ μ₀ k 0 = id`, `reverseSegment κ μ₀ k (j + 1) =
reverseSegment κ μ₀ k j ∘ₖ reverseStep κ μ₀ (k + j)` (first step back from `k + j + 1`). -/
noncomputable def reverseSegment (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) [IsFiniteMeasure μ₀]
    [∀ n, IsFiniteKernel (κ n)] (k : ℕ) : ℕ → Kernel Ω Ω
  | 0 => Kernel.id
  | j + 1 => reverseSegment κ μ₀ k j ∘ₖ reverseStep κ μ₀ (k + j)

/-- The full reverse chain from time `n` down to time `0`. -/
noncomputable def reverseChain (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) [IsFiniteMeasure μ₀]
    [∀ n, IsFiniteKernel (κ n)] (n : ℕ) : Kernel Ω Ω :=
  reverseSegment κ μ₀ 0 n

/-- Unfolding the reverse chain: `reverseChain (n + 1) = reverseChain n ∘ₖ reverseStep n`. -/
theorem reverseChain_succ (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) [IsFiniteMeasure μ₀]
    [∀ n, IsFiniteKernel (κ n)] (n : ℕ) :
    reverseChain κ μ₀ (n + 1) = reverseChain κ μ₀ n ∘ₖ reverseStep κ μ₀ n := by
  simp [reverseChain, reverseSegment]

variable (κ : ℕ → Kernel Ω Ω) (μ₀ : Measure Ω) [IsFiniteMeasure μ₀]

/-- **Joint law of each reverse step (KR-2).** For finite `μ₀` and finite kernels on a
nonempty standard Borel space, the reverse step `n + 1 → n` reproduces the swapped forward joint
law of `(X_n, X_{n+1})`. -/
theorem reverseStep_joint_law [∀ n, IsFiniteKernel (κ n)] (n : ℕ) :
    forwardMarginal κ μ₀ (n + 1) ⊗ₘ reverseStep κ μ₀ n
      = (forwardMarginal κ μ₀ n ⊗ₘ κ n).map Prod.swap :=
  compProd_posterior_eq_map_swap

/-- **Each reverse step recovers the previous marginal (KR-2).** For Markov `κ n` and finite
`μ₀`: `reverseStep κ μ₀ n ∘ₘ forwardMarginal κ μ₀ (n + 1) = forwardMarginal κ μ₀ n`. -/
theorem reverseStep_comp_forwardMarginal [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    reverseStep κ μ₀ n ∘ₘ forwardMarginal κ μ₀ (n + 1) = forwardMarginal κ μ₀ n :=
  posterior_comp_self

/-- **Reverse segments recover intermediate marginals (KR-2).** For Markov `κ n` and finite
`μ₀`, running the exact reverse steps from the time-`(k + j)` law down to time `k` gives the
time-`k` forward marginal. Proved by induction on `j`. -/
theorem reverseSegment_comp_forwardMarginal [∀ n, IsMarkovKernel (κ n)] (k j : ℕ) :
    reverseSegment κ μ₀ k j ∘ₘ forwardMarginal κ μ₀ (k + j) = forwardMarginal κ μ₀ k := by
  induction j with
  | zero => exact Measure.id_comp
  | succ j ih =>
    rw [reverseSegment, ← Measure.comp_assoc, ← Nat.add_assoc,
      reverseStep_comp_forwardMarginal, ih]

/-- **`n`-step reverse marginal recovery (KR-2).** For Markov `κ n` and finite `μ₀` on a
nonempty standard Borel space, the composite of the `n` exact reverse steps maps the time-`n`
forward marginal back to the initial law: `reverseChain κ μ₀ n ∘ₘ forwardMarginal κ μ₀ n = μ₀`. -/
theorem reverseChain_comp_forwardMarginal [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    reverseChain κ μ₀ n ∘ₘ forwardMarginal κ μ₀ n = μ₀ := by
  have := reverseSegment_comp_forwardMarginal κ μ₀ 0 n
  rwa [Nat.zero_add] at this

/-- **The `n`-step reverse chain is a.e. the posterior of the `n`-step forward kernel
(KR-2).** For Markov `κ n` and finite `μ₀` on a nonempty standard Borel space,
`reverseChain κ μ₀ n = (forwardChain κ n)†μ₀` holds `forwardMarginal κ μ₀ n`-almost everywhere.
-/
theorem reverseChain_ae_eq_posterior [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    reverseChain κ μ₀ n =ᵐ[forwardMarginal κ μ₀ n] (forwardChain κ n)†μ₀ := by
  induction n with
  | zero =>
    filter_upwards [posterior_id μ₀] with x hx
    exact hx.symm
  | succ n ih =>
    have hpc := posterior_comp (κ := forwardChain κ n) (η := κ n) (μ := μ₀)
    have hrs : (κ n)†(forwardChain κ n ∘ₘ μ₀) = reverseStep κ μ₀ n :=
      posterior_congr_measure _ (forwardMarginal_eq_forwardChain_comp κ μ₀ n).symm
    rw [hrs, ← forwardMarginal_eq_forwardChain_comp] at hpc
    rw [reverseChain_succ]
    have hih : reverseChain κ μ₀ n =ᵐ[reverseStep κ μ₀ n ∘ₘ forwardMarginal κ μ₀ (n + 1)]
        (forwardChain κ n)†μ₀ := by
      rwa [reverseStep_comp_forwardMarginal]
    exact (comp_ae_eq_comp_of_ae_eq hih).trans hpc.symm

end NStep

/-! ## (B) Density form of the reverse kernel (KR-2) -/

section Density

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The output-law density `m y = ∫⁻ x, p x * k x y ∂ν` of the forward step with prior density
`p` (w.r.t. `ν`) and forward density `k x ·` (w.r.t. the reference measure on `Y`). -/
noncomputable def marginalDensity (ν : Measure X) (p : X → ℝ≥0∞) (k : X → Y → ℝ≥0∞) (y : Y) :
    ℝ≥0∞ :=
  ∫⁻ x, p x * k x y ∂ν

/-- The Bayes reverse density `r y x = p x * k x y / m y`. In ENNReal this is `∞` or `0` when
`m y ∈ {0, ∞}`; it is a probability density in `x` exactly when `0 < m y < ∞`
(`lintegral_reverseDensity`). -/
noncomputable def reverseDensity (ν : Measure X) (p : X → ℝ≥0∞) (k : X → Y → ℝ≥0∞) (y : Y)
    (x : X) : ℝ≥0∞ :=
  p x * k x y / marginalDensity ν p k y

variable {ν : Measure X} {ρ : Measure Y} {p : X → ℝ≥0∞} {k : X → Y → ℝ≥0∞}

/-- The joint density `(x, y) ↦ p x * k x y` is measurable if `p` and `uncurry k` are. -/
theorem measurable_joint (hp : Measurable p) (hk : Measurable (Function.uncurry k)) :
    Measurable (fun z : X × Y => p z.1 * k z.1 z.2) :=
  (hp.comp measurable_fst).mul hk

/-- The marginal density is measurable (s-finite `ν`, measurable `p`, jointly measurable `k`). -/
theorem measurable_marginalDensity [SFinite ν] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) : Measurable (marginalDensity ν p k) :=
  (measurable_joint hp hk).lintegral_prod_left'

/-- The reverse density is jointly measurable in `(y, x)` (s-finite `ν`, measurable `p`, jointly
measurable `k`). -/
theorem measurable_reverseDensity [SFinite ν] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) :
    Measurable (Function.uncurry (reverseDensity ν p k)) := by
  have h1 : Measurable (fun z : Y × X => p z.2 * k z.2 z.1) :=
    (measurable_joint hp hk).comp measurable_swap
  exact h1.div ((measurable_marginalDensity hp hk).comp measurable_fst)

omit [MeasurableSpace Y] in
/-- **Pointwise joint symmetry (KR-2, density form).** If `0 < m y < ∞` then for every `x`,
`p x * k x y = m y * r y x`: prior times forward density equals marginal times reverse
density. This is the definition of `reverseDensity` rearranged; the substantive density-form
statement is `isReverseKernel_densityKernel`. -/
theorem joint_density_eq_mul_reverseDensity (y : Y) (x : X)
    (h0 : marginalDensity ν p k y ≠ 0) (htop : marginalDensity ν p k y ≠ ⊤) :
    p x * k x y = marginalDensity ν p k y * reverseDensity ν p k y x :=
  (ENNReal.mul_div_cancel h0 htop).symm

/-- Total mass of the reverse density: `∫⁻ x, r y x ∂ν = m y / m y` (measurable `p`, jointly
measurable `k`). In ENNReal this is `1` if `0 < m y < ∞` and `0` otherwise. -/
theorem lintegral_reverseDensity (hp : Measurable p) (hk : Measurable (Function.uncurry k))
    (y : Y) :
    ∫⁻ x, reverseDensity ν p k y x ∂ν = marginalDensity ν p k y / marginalDensity ν p k y := by
  simp_rw [reverseDensity, div_eq_mul_inv]
  rw [lintegral_mul_const (f := fun x => p x * k x y) _ (hp.mul hk.of_uncurry_right)]
  rfl

/-- If `0 < m y < ∞`, the reverse density `r y ·` is a probability density w.r.t. `ν`
(measurable `p`, jointly measurable `k`). -/
theorem lintegral_reverseDensity_eq_one (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (y : Y)
    (h0 : marginalDensity ν p k y ≠ 0) (htop : marginalDensity ν p k y ≠ ⊤) :
    ∫⁻ x, reverseDensity ν p k y x ∂ν = 1 := by
  rw [lintegral_reverseDensity hp hk, ENNReal.div_self h0 htop]

/-- The reverse density always has total mass at most `1` (measurable `p`, jointly measurable
`k`). -/
theorem lintegral_reverseDensity_le_one (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (y : Y) :
    ∫⁻ x, reverseDensity ν p k y x ∂ν ≤ 1 := by
  rw [lintegral_reverseDensity hp hk]
  exact ENNReal.div_self_le_one

/-- Where the marginal density vanishes, the joint density vanishes `ν`-a.e. in `x`
(measurable `p`, jointly measurable `k`). -/
theorem ae_joint_eq_zero_of_marginalDensity_eq_zero (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) {y : Y} (h0 : marginalDensity ν p k y = 0) :
    ∀ᵐ x ∂ν, p x * k x y = 0 :=
  (lintegral_eq_zero_iff (hp.mul hk.of_uncurry_right)).1 h0

/-- **A.e. joint symmetry for fixed `y` (KR-2).** If `m y < ∞` (no lower bound needed), then
`p x * k x y = m y * r y x` for `ν`-a.e. `x` (measurable `p`, jointly measurable `k`). -/
theorem ae_joint_density_eq_mul_reverseDensity (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (y : Y) (htop : marginalDensity ν p k y ≠ ⊤) :
    ∀ᵐ x ∂ν, p x * k x y = marginalDensity ν p k y * reverseDensity ν p k y x := by
  by_cases h0 : marginalDensity ν p k y = 0
  · filter_upwards [ae_joint_eq_zero_of_marginalDensity_eq_zero hp hk h0] with x hx
    rw [hx, h0, zero_mul]
  · exact Filter.Eventually.of_forall fun x => joint_density_eq_mul_reverseDensity y x h0 htop

/-- Bayes on a set, for fixed `y` with `m y < ∞`:
`m y * ∫⁻ x in A, r y x ∂ν = ∫⁻ x in A, p x * k x y ∂ν` for every set `A` (measurable `p`,
jointly measurable `k`). -/
theorem marginalDensity_mul_setLIntegral_reverseDensity (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (y : Y) (htop : marginalDensity ν p k y ≠ ⊤)
    (A : Set X) :
    marginalDensity ν p k y * ∫⁻ x in A, reverseDensity ν p k y x ∂ν
      = ∫⁻ x in A, p x * k x y ∂ν := by
  by_cases h0 : marginalDensity ν p k y = 0
  · rw [h0, zero_mul, eq_comm, ← lintegral_zero (μ := ν.restrict A)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [ae_joint_eq_zero_of_marginalDensity_eq_zero hp hk h0] with x hx
    simpa using hx
  · simp_rw [reverseDensity, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 h0), mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel h0 htop, mul_one]

/-- Tonelli for the marginal: `∫⁻ y, m y ∂ρ = ∫⁻ x, p x * ∫⁻ y, k x y ∂ρ ∂ν` (s-finite `ν`, `ρ`,
measurable `p`, jointly measurable `k`). -/
theorem lintegral_marginalDensity [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) :
    ∫⁻ y, marginalDensity ν p k y ∂ρ = ∫⁻ x, p x * ∫⁻ y, k x y ∂ρ ∂ν := by
  unfold marginalDensity
  rw [lintegral_lintegral_swap (f := fun y x => p x * k x y)
    ((measurable_joint hp hk).comp measurable_swap).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_const_mul _ hk.of_uncurry_left]

/-- If every forward density is normalised, `∫⁻ y, k x y ∂ρ = 1`, the marginal density has the
same total mass as the prior: `∫⁻ y, m y ∂ρ = ∫⁻ x, p x ∂ν` (s-finite `ν`, `ρ`, measurable `p`,
jointly measurable `k`). -/
theorem lintegral_marginalDensity_of_normalized [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1) :
    ∫⁻ y, marginalDensity ν p k y ∂ρ = ∫⁻ x, p x ∂ν := by
  rw [lintegral_marginalDensity (ρ := ρ) hp hk]
  simp [hk1]

/-- Under the normalisations `∫⁻ y, k x y ∂ρ = 1` and `∫⁻ p ∂ν < ∞`, the marginal density is
finite `ρ`-a.e. (s-finite `ν`, `ρ`, measurable `p`, jointly measurable `k`). -/
theorem ae_marginalDensity_ne_top [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1)
    (hp_fin : ∫⁻ x, p x ∂ν ≠ ⊤) : ∀ᵐ y ∂ρ, marginalDensity ν p k y ≠ ⊤ := by
  have hm : ∫⁻ y, marginalDensity ν p k y ∂ρ ≠ ⊤ := by
    rwa [lintegral_marginalDensity_of_normalized hp hk hk1]
  filter_upwards [ae_lt_top (measurable_marginalDensity hp hk) hm] with y hy
  exact hy.ne

/-- **The exceptional set `{m = 0}` is null for the output law** `ρ.withDensity m`
(s-finite `ν`, measurable `p`, jointly measurable `k`; no normalisation needed). -/
theorem withDensity_marginalDensity_setOf_eq_zero [SFinite ν] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) :
    ρ.withDensity (marginalDensity ν p k) {y | marginalDensity ν p k y = 0} = 0 := by
  have hS : MeasurableSet {y | marginalDensity ν p k y = 0} :=
    measurable_marginalDensity hp hk (measurableSet_singleton 0)
  rw [withDensity_apply _ hS, setLIntegral_congr_fun hS (g := fun _ => 0) (fun y hy => hy),
    lintegral_zero]

/-- **The exceptional set `{m = ∞}` is null for the output law** under the normalisations
`∫⁻ y, k x y ∂ρ = 1` and `∫⁻ p ∂ν < ∞` (s-finite `ν`, `ρ`, measurable `p`, jointly measurable
`k`). -/
theorem withDensity_marginalDensity_setOf_eq_top [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1)
    (hp_fin : ∫⁻ x, p x ∂ν ≠ ⊤) :
    ρ.withDensity (marginalDensity ν p k) {y | marginalDensity ν p k y = ⊤} = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  have := ae_marginalDensity_ne_top hp hk hk1 hp_fin
  rw [ae_iff] at this
  simpa using this

/-- **Joint symmetry almost surely under the output law (KR-2).** Under the normalisations
`∫⁻ y, k x y ∂ρ = 1` and `∫⁻ p ∂ν < ∞` (s-finite `ν`, `ρ`, measurable `p`, jointly measurable
`k`), for almost every `y` under the output law `ρ.withDensity m` we have `0 < m y < ∞` and
`p x * k x y = m y * r y x` for **every** `x`. -/
theorem ae_withDensity_joint_density_eq [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1)
    (hp_fin : ∫⁻ x, p x ∂ν ≠ ⊤) :
    ∀ᵐ y ∂ρ.withDensity (marginalDensity ν p k),
      0 < marginalDensity ν p k y ∧ marginalDensity ν p k y < ⊤ ∧
      ∀ x, p x * k x y = marginalDensity ν p k y * reverseDensity ν p k y x := by
  have h0 : ∀ᵐ y ∂ρ.withDensity (marginalDensity ν p k), marginalDensity ν p k y ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.1 (withDensity_marginalDensity_setOf_eq_zero hp hk)
  have htop : ∀ᵐ y ∂ρ.withDensity (marginalDensity ν p k), marginalDensity ν p k y ≠ ⊤ :=
    measure_eq_zero_iff_ae_notMem.1 (withDensity_marginalDensity_setOf_eq_top hp hk hk1 hp_fin)
  filter_upwards [h0, htop] with y h0 htop
  exact ⟨pos_iff_ne_zero.2 h0, lt_top_iff_ne_top.2 htop,
    fun x => joint_density_eq_mul_reverseDensity y x h0 htop⟩

/-- Swapping coordinates of a product measure with a density: for s-finite `ν`, `ρ` and
measurable `g`, `((ν.prod ρ).withDensity g).map swap = (ρ.prod ν).withDensity (g ∘ swap)`. -/
theorem map_swap_prod_withDensity [SFinite ν] [SFinite ρ] {g : X × Y → ℝ≥0∞}
    (hg : Measurable g) :
    ((ν.prod ρ).withDensity g).map Prod.swap = (ρ.prod ν).withDensity (fun z => g z.swap) := by
  ext s hs
  rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
    withDensity_apply _ hs, ← Measure.prod_swap (μ := ν) (ν := ρ),
    setLIntegral_map hs (f := fun z => g z.swap) (by fun_prop) measurable_swap]
  simp

/-- **Measure-level joint symmetry (KR-2, density form).** If `m < ∞` `ρ`-a.e. (s-finite `ν`,
`ρ`, measurable `p`, jointly measurable `k`), the forward joint law with density
`p x * k x y` w.r.t. `ν ⊗ ρ`, with coordinates swapped, equals the reverse joint law with
density `m y * r y x` w.r.t. `ρ ⊗ ν`. -/
theorem joint_map_swap [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (hm : ∀ᵐ y ∂ρ, marginalDensity ν p k y ≠ ⊤) :
    ((ν.prod ρ).withDensity (fun z => p z.1 * k z.1 z.2)).map Prod.swap
      = (ρ.prod ν).withDensity
          (fun z => marginalDensity ν p k z.1 * reverseDensity ν p k z.1 z.2) := by
  rw [map_swap_prod_withDensity (measurable_joint hp hk)]
  refine withDensity_congr_ae ?_
  have hmeas : MeasurableSet {z : Y × X | p z.2 * k z.2 z.1
      = marginalDensity ν p k z.1 * reverseDensity ν p k z.1 z.2} :=
    measurableSet_eq_fun ((measurable_joint hp hk).comp measurable_swap)
      (((measurable_marginalDensity hp hk).comp measurable_fst).mul
        (measurable_reverseDensity hp hk))
  refine (Measure.ae_prod_iff_ae_ae hmeas).2 ?_
  filter_upwards [hm] with y hy
  exact ae_joint_density_eq_mul_reverseDensity hp hk y hy

/-- **Marginal recovery in density form (KR-2).** If every forward density is normalised,
`∫⁻ y, k x y ∂ρ = 1`, and `m < ∞` `ρ`-a.e. (s-finite `ν`, `ρ`, measurable `p`, jointly
measurable `k`), then for every set `A ⊆ X`
`∫⁻ y, m y * (∫⁻ x in A, r y x ∂ν) ∂ρ = ∫⁻ x in A, p x ∂ν` (Tonelli). -/
theorem lintegral_marginalDensity_mul_setLIntegral_reverseDensity [SFinite ν] [SFinite ρ]
    (hp : Measurable p) (hk : Measurable (Function.uncurry k))
    (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1) (hm : ∀ᵐ y ∂ρ, marginalDensity ν p k y ≠ ⊤) (A : Set X) :
    ∫⁻ y, marginalDensity ν p k y * (∫⁻ x in A, reverseDensity ν p k y x ∂ν) ∂ρ
      = ∫⁻ x in A, p x ∂ν := by
  calc ∫⁻ y, marginalDensity ν p k y * (∫⁻ x in A, reverseDensity ν p k y x ∂ν) ∂ρ
      = ∫⁻ y, ∫⁻ x in A, p x * k x y ∂ν ∂ρ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hm] with y hy
        exact marginalDensity_mul_setLIntegral_reverseDensity hp hk y hy A
    _ = ∫⁻ x in A, ∫⁻ y, p x * k x y ∂ρ ∂ν :=
        lintegral_lintegral_swap (f := fun y x => p x * k x y)
          ((measurable_joint hp hk).comp measurable_swap).aemeasurable
    _ = ∫⁻ x in A, p x ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ hk.of_uncurry_left, hk1, mul_one]

/-- Marginal recovery under the natural normalisations `∫⁻ y, k x y ∂ρ = 1` and
`∫⁻ p ∂ν < ∞` (s-finite `ν`, `ρ`, measurable `p`, jointly measurable `k`):
`∫⁻ y, m y * (∫⁻ x in A, r y x ∂ν) ∂ρ = ∫⁻ x in A, p x ∂ν` for every `A ⊆ X`. -/
theorem lintegral_marginalDensity_mul_setLIntegral_reverseDensity_of_normalized [SFinite ν]
    [SFinite ρ] (hp : Measurable p) (hk : Measurable (Function.uncurry k))
    (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1) (hp_fin : ∫⁻ x, p x ∂ν ≠ ⊤) (A : Set X) :
    ∫⁻ y, marginalDensity ν p k y * (∫⁻ x in A, reverseDensity ν p k y x ∂ν) ∂ρ
      = ∫⁻ x in A, p x ∂ν :=
  lintegral_marginalDensity_mul_setLIntegral_reverseDensity hp hk hk1
    (ae_marginalDensity_ne_top hp hk hk1 hp_fin) A

/-- **Forward-then-reverse invariance (data augmentation, density form).** If
`∫⁻ y, k x y ∂ρ = 1` for all `x` and `m < ∞` `ρ`-a.e. (s-finite `ν`, `ρ`, measurable `p`,
jointly measurable `k`), the two-step kernel "`y ~ k x ·`, then `x' ~ r y ·`" leaves the prior
density invariant: `∫⁻ x, p x * ∫⁻ y, k x y * (∫⁻ x' in A, r y x' ∂ν) ∂ρ ∂ν = ∫⁻ x in A, p x ∂ν`
for every `A ⊆ X`. -/
theorem lintegral_forward_reverse_setLIntegral [SFinite ν] [SFinite ρ]
    (hp : Measurable p) (hk : Measurable (Function.uncurry k))
    (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1) (hm : ∀ᵐ y ∂ρ, marginalDensity ν p k y ≠ ⊤) (A : Set X) :
    ∫⁻ x, p x * (∫⁻ y, k x y * (∫⁻ x' in A, reverseDensity ν p k y x' ∂ν) ∂ρ) ∂ν
      = ∫⁻ x in A, p x ∂ν := by
  set F : Y → ℝ≥0∞ := fun y => ∫⁻ x' in A, reverseDensity ν p k y x' ∂ν with hF
  have hFm : Measurable F := (measurable_reverseDensity hp hk).lintegral_prod_right'
  have hjm : Measurable (fun z : X × Y => p z.1 * k z.1 z.2 * F z.2) :=
    (measurable_joint hp hk).mul (hFm.comp measurable_snd)
  calc ∫⁻ x, p x * (∫⁻ y, k x y * F y ∂ρ) ∂ν
      = ∫⁻ x, ∫⁻ y, p x * k x y * F y ∂ρ ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_const_mul (f := fun y => k x y * F y) _ (hk.of_uncurry_left.mul hFm)]
        simp_rw [mul_assoc]
    _ = ∫⁻ y, ∫⁻ x, p x * k x y * F y ∂ν ∂ρ :=
        lintegral_lintegral_swap (f := fun x y => p x * k x y * F y) hjm.aemeasurable
    _ = ∫⁻ y, marginalDensity ν p k y * F y ∂ρ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const (f := fun x => p x * k x y) _ (hp.mul hk.of_uncurry_right)]
        rfl
    _ = ∫⁻ x in A, p x ∂ν :=
        lintegral_marginalDensity_mul_setLIntegral_reverseDensity hp hk hk1 hm A

/-- The kernel `x ↦ ρ.withDensity (k x)` with density `k` w.r.t. the s-finite reference
measure `ρ` (Mathlib's `Kernel.withDensity` of the constant kernel; it is `0` if `uncurry k` is
not measurable). -/
noncomputable def densityKernel (ρ : Measure Y) [SFinite ρ] (k : X → Y → ℝ≥0∞) : Kernel X Y :=
  Kernel.withDensity (Kernel.const X ρ) k

/-- For jointly measurable `k`, `densityKernel ρ k x = ρ.withDensity (k x)`. -/
theorem densityKernel_apply [SFinite ρ] (hk : Measurable (Function.uncurry k)) (x : X) :
    densityKernel ρ k x = ρ.withDensity (k x) := by
  rw [densityKernel, Kernel.withDensity_apply _ hk, Kernel.const_apply]

/-- A jointly measurable forward density with `∫⁻ y, k x y ∂ρ = 1` for every `x` defines a
Markov kernel. -/
theorem isMarkovKernel_densityKernel [SFinite ρ] (hk : Measurable (Function.uncurry k))
    (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1) : IsMarkovKernel (densityKernel ρ k) :=
  ⟨fun x => ⟨by rw [densityKernel_apply hk, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hk1]⟩⟩

/-- Conversely, if `densityKernel ρ k` is Markov (and `k` jointly measurable), every
`k x ·` is a probability density: `∫⁻ y, k x y ∂ρ = 1`. -/
theorem lintegral_eq_one_of_isMarkovKernel_densityKernel [SFinite ρ]
    (hk : Measurable (Function.uncurry k)) [IsMarkovKernel (densityKernel ρ k)] (x : X) :
    ∫⁻ y, k x y ∂ρ = 1 := by
  have h := measure_univ (μ := densityKernel ρ k x)
  rwa [densityKernel_apply hk, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- The reverse-density kernel `y ↦ ν.withDensity (r y)` is a finite kernel (each `r y` has mass
`≤ 1`), for s-finite `ν`, measurable `p` and jointly measurable `k`. -/
theorem isFiniteKernel_densityKernel_reverseDensity [SFinite ν] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) :
    IsFiniteKernel (densityKernel ν (reverseDensity ν p k)) :=
  ⟨⟨1, ENNReal.one_lt_top, fun y => by
    rw [densityKernel_apply (measurable_reverseDensity hp hk),
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_reverseDensity_le_one hp hk y⟩⟩

/-- **Output law in density form.** For s-finite `ν`, `ρ`, measurable `p` and jointly measurable
`k`, the output law of the forward step is `densityKernel ρ k ∘ₘ ν.withDensity p =
ρ.withDensity m`. -/
theorem densityKernel_comp_withDensity [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) :
    densityKernel ρ k ∘ₘ ν.withDensity p = ρ.withDensity (marginalDensity ν p k) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), withDensity_apply _ hs,
    lintegral_withDensity_eq_lintegral_mul _ hp ((densityKernel ρ k).measurable_coe hs)]
  calc ∫⁻ x, (p * fun x => densityKernel ρ k x s) x ∂ν
      = ∫⁻ x, ∫⁻ y in s, p x * k x y ∂ρ ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, densityKernel_apply hk, withDensity_apply _ hs,
          lintegral_const_mul _ hk.of_uncurry_left]
    _ = ∫⁻ y in s, marginalDensity ν p k y ∂ρ :=
        lintegral_lintegral_swap (f := fun x y => p x * k x y)
          (measurable_joint hp hk).aemeasurable

/-- **Forward joint law in density form.** For s-finite `ν`, `ρ`, measurable `p`, jointly
measurable `k` and an s-finite kernel `densityKernel ρ k`,
`ν.withDensity p ⊗ₘ densityKernel ρ k = (ν.prod ρ).withDensity (fun z => p z.1 * k z.1 z.2)`. -/
theorem withDensity_compProd_densityKernel [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) [hks : IsSFiniteKernel (densityKernel ρ k)] :
    ν.withDensity p ⊗ₘ densityKernel ρ k
      = (ν.prod ρ).withDensity (fun z => p z.1 * k z.1 z.2) := by
  have : IsSFiniteKernel ((Kernel.const X ρ).withDensity k) := hks
  rw [densityKernel, Measure.compProd_withDensity hk, Measure.compProd_const,
    prod_withDensity_left hp]
  exact (withDensity_mul _ (f := fun z : X × Y => p z.1) (g := fun z => k z.1 z.2)
    (hp.comp measurable_fst) hk).symm

/-- **Bayes' formula as an exact reverse kernel (KR-2, (B) ⇒ (A)).** For s-finite `ν`, `ρ`,
measurable `p`, jointly measurable `k` with `∫⁻ y, k x y ∂ρ = 1` for every `x`, and a finite
prior `∫⁻ p ∂ν < ∞`, the reverse-density kernel `y ↦ ν.withDensity (r y)` is an exact reverse
kernel of the forward step `(densityKernel ρ k, ν.withDensity p)`. No standard-Borel
assumption. -/
theorem isReverseKernel_densityKernel [SFinite ν] [SFinite ρ] (hp : Measurable p)
    (hk : Measurable (Function.uncurry k)) (hk1 : ∀ x, ∫⁻ y, k x y ∂ρ = 1)
    (hp_fin : ∫⁻ x, p x ∂ν ≠ ⊤) :
    IsReverseKernel (densityKernel ρ k) (ν.withDensity p)
      (densityKernel ν (reverseDensity ν p k)) := by
  have := isMarkovKernel_densityKernel (ρ := ρ) hk hk1
  have := isFiniteKernel_densityKernel_reverseDensity (ν := ν) hp hk
  unfold IsReverseKernel
  rw [densityKernel_comp_withDensity hp hk,
    withDensity_compProd_densityKernel (measurable_marginalDensity hp hk)
      (measurable_reverseDensity hp hk),
    withDensity_compProd_densityKernel hp hk,
    joint_map_swap hp hk (ae_marginalDensity_ne_top hp hk hk1 hp_fin)]

/-- **The density-form reverse kernel is a.e. Mathlib's posterior (KR-2).** If moreover `X` is
a nonempty standard Borel space, the prior `ν.withDensity p` is finite and `densityKernel ρ k`
is Markov (equivalently `∫⁻ y, k x y ∂ρ = 1`), then
`densityKernel ν r = (densityKernel ρ k)†(ν.withDensity p)` almost everywhere under the output
law; i.e. for a.e. `y`, the posterior is `ν.withDensity (r y)` (Bayes' formula). -/
theorem densityKernel_reverseDensity_ae_eq_posterior [StandardBorelSpace X] [Nonempty X]
    [SFinite ν] [SFinite ρ] (hp : Measurable p) (hk : Measurable (Function.uncurry k))
    [IsFiniteMeasure (ν.withDensity p)] [IsMarkovKernel (densityKernel ρ k)] :
    densityKernel ν (reverseDensity ν p k)
      =ᵐ[densityKernel ρ k ∘ₘ ν.withDensity p] (densityKernel ρ k)†(ν.withDensity p) := by
  have := isFiniteKernel_densityKernel_reverseDensity (ν := ν) hp hk
  have hk1 := lintegral_eq_one_of_isMarkovKernel_densityKernel (ρ := ρ) hk
  have hp_fin : ∫⁻ x, p x ∂ν ≠ ⊤ := by
    have h := measure_ne_top (ν.withDensity p) Set.univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact (isReverseKernel_densityKernel hp hk hk1 hp_fin).ae_eq_posterior

end Density

end FormalizeSampling.ReverseKernel
