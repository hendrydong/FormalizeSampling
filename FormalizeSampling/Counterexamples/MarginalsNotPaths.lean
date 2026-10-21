module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Equal one-time marginals do not determine the two-time law (CE-01, finite two-time form)

Let `μ` be a probability measure on a space `α` without atoms. Compare two "processes"
observed at two times:

* the *constant process* `X_s = X_t = W` with `W ~ μ`, whose two-time law is
  `P := μ.map (fun z => (z, z))`;
* *independent draws* `Y_s, Y_t` i.i.d. `~ μ`, whose two-time law is `Q := μ.prod μ`.

Both have the same one-time marginals (`P.map Prod.fst = Q.map Prod.fst = μ`, and the same for
`Prod.snd`), but `P ≠ Q`: the diagonal `{(a, b) | a = b}` has `P`-measure `1` and `Q`-measure
`0`. Hence equality of all one-time marginal laws does not determine the two-time
(finite-dimensional) law, and therefore does not determine the path law of a process.

## Conventions

* The generic results assume a measurable diagonal (`MeasurableSet (Set.diagonal α)`), which
  is discharged in `diagonal_measurableSet_of_secondCountable` for second-countable Hausdorff
  Borel spaces (in particular `ℝ` and `Fin d → ℝ`).
* The concrete instance uses `μ = gaussianReal 0 1 = N(0,1)` on `ℝ`.

## Registry IDs

* `CE-01`: `constPair_map_fst`, `constPair_map_snd`, `indepPair_map_fst`,
  `indepPair_map_snd`, `constPair_diagonal`, `indepPair_diagonal`, `constPair_ne_indepPair`,
  `constPair_ne_indepPair_of_secondCountable`, and the Gaussian instances
  `gaussian_map_fst_eq`, `gaussian_map_snd_eq`, `gaussian_constPair_ne_indepPair`.

## Not proved here

* Only the finite two-time form is formalised. The continuous-time upgrade (constant process
  versus a stationary Ornstein–Uhlenbeck process, both with `N(0,1)` marginals, and the
  resulting difference of path laws on `C([0, ∞), ℝ)`) is not formalised.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace FormalizeSampling.Counterexamples.MarginalsNotPaths

variable {α : Type*} [MeasurableSpace α]

/-- Two-time law of the constant process `X_s = X_t = W`, `W ~ μ`: the image of `μ` under
`z ↦ (z, z)`. -/
noncomputable def constPair (μ : Measure α) : Measure (α × α) :=
  μ.map (fun z => (z, z))

/-- Two-time law of two independent draws `Y_s, Y_t ~ μ`: the product measure `μ ⊗ μ`. -/
noncomputable def indepPair (μ : Measure α) : Measure (α × α) :=
  μ.prod μ

private lemma measurable_diag_map : Measurable (fun z : α => (z, z)) :=
  measurable_id.prodMk measurable_id

/-- The first one-time marginal of the constant process is `μ`. -/
theorem constPair_map_fst (μ : Measure α) : (constPair μ).map Prod.fst = μ := by
  rw [constPair, Measure.map_map measurable_fst measurable_diag_map]
  exact Measure.map_id

/-- The second one-time marginal of the constant process is `μ`. -/
theorem constPair_map_snd (μ : Measure α) : (constPair μ).map Prod.snd = μ := by
  rw [constPair, Measure.map_map measurable_snd measurable_diag_map]
  exact Measure.map_id

/-- The first one-time marginal of two independent draws from a probability measure `μ` is
`μ`. -/
theorem indepPair_map_fst (μ : Measure α) [IsProbabilityMeasure μ] :
    (indepPair μ).map Prod.fst = μ := by
  rw [indepPair, Measure.map_fst_prod, measure_univ, one_smul]

/-- The second one-time marginal of two independent draws from a probability measure `μ` is
`μ`. -/
theorem indepPair_map_snd (μ : Measure α) [IsProbabilityMeasure μ] :
    (indepPair μ).map Prod.snd = μ := by
  rw [indepPair, Measure.map_snd_prod, measure_univ, one_smul]

/-- The constant process lies on the diagonal with probability one: for a probability measure
`μ` and a measurable diagonal, `constPair μ {(a, b) | a = b} = 1`. -/
theorem constPair_diagonal (μ : Measure α) [IsProbabilityMeasure μ]
    (hD : MeasurableSet (Set.diagonal α)) : constPair μ (Set.diagonal α) = 1 := by
  rw [constPair, Measure.map_apply measurable_diag_map hD]
  have : (fun z : α => (z, z)) ⁻¹' Set.diagonal α = Set.univ := by
    ext z
    simp
  rw [this, measure_univ]

/-- Two independent draws from an atomless measure `μ` almost surely differ: for a measurable
diagonal, `indepPair μ {(a, b) | a = b} = 0`. -/
theorem indepPair_diagonal (μ : Measure α) [SFinite μ] [NullSingletonClass μ]
    (hD : MeasurableSet (Set.diagonal α)) : indepPair μ (Set.diagonal α) = 0 := by
  rw [indepPair, Measure.prod_apply hD]
  have : ∀ x : α, Prod.mk x ⁻¹' Set.diagonal α = {x} := by
    intro x
    ext y
    simp [Set.mem_diagonal_iff, eq_comm]
  simp [this]

/-- **CE-01 (generic two-time form).** For an atomless probability measure `μ` on a space with
measurable diagonal, the constant process and the independent pair have the same one-time
marginals (`constPair_map_fst`, `constPair_map_snd`, `indepPair_map_fst`, `indepPair_map_snd`)
but different two-time laws: `constPair μ ≠ indepPair μ`. -/
theorem constPair_ne_indepPair (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hD : MeasurableSet (Set.diagonal α)) : constPair μ ≠ indepPair μ := by
  intro h
  have h1 := constPair_diagonal μ hD
  rw [h, indepPair_diagonal μ hD] at h1
  exact zero_ne_one h1

/-- The diagonal of a second-countable Hausdorff space with its Borel σ-algebra is measurable
(it is closed in `α × α`, whose Borel σ-algebra is the product σ-algebra). -/
theorem diagonal_measurableSet_of_secondCountable [TopologicalSpace α] [T2Space α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] :
    MeasurableSet (Set.diagonal α) :=
  isClosed_diagonal.measurableSet

/-- **CE-01 for second-countable Hausdorff Borel spaces.** For every atomless probability
measure `μ` on such a space (e.g. `ℝ`, `Fin d → ℝ`), equal one-time marginals coexist with
different two-time laws: `constPair μ ≠ indepPair μ`. -/
theorem constPair_ne_indepPair_of_secondCountable [TopologicalSpace α] [T2Space α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] : constPair μ ≠ indepPair μ :=
  constPair_ne_indepPair μ diagonal_measurableSet_of_secondCountable

/-- **CE-01, Gaussian instance, first marginals.** With `μ = N(0,1)`,
`P = μ.map (z ↦ (z, z))` and `Q = μ ⊗ μ`, both first marginals equal `μ`. -/
theorem gaussian_map_fst_eq :
    ((gaussianReal 0 1).map (fun z => (z, z))).map Prod.fst = gaussianReal 0 1 ∧
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.fst = gaussianReal 0 1 :=
  ⟨constPair_map_fst _, indepPair_map_fst _⟩

/-- **CE-01, Gaussian instance, second marginals.** With `μ = N(0,1)`,
`P = μ.map (z ↦ (z, z))` and `Q = μ ⊗ μ`, both second marginals equal `μ`. -/
theorem gaussian_map_snd_eq :
    ((gaussianReal 0 1).map (fun z => (z, z))).map Prod.snd = gaussianReal 0 1 ∧
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.snd = gaussianReal 0 1 :=
  ⟨constPair_map_snd _, indepPair_map_snd _⟩

/-- **CE-01, Gaussian instance.** With `μ = N(0,1)`, the two-time law of the constant process
`P = μ.map (z ↦ (z, z))` differs from the law of two independent `N(0,1)` draws `Q = μ ⊗ μ`,
although all one-time marginals agree (`gaussian_map_fst_eq`, `gaussian_map_snd_eq`). The
diagonal has `P`-measure `1` and `Q`-measure `0` because `N(0,1)` has no atoms. -/
theorem gaussian_constPair_ne_indepPair :
    (gaussianReal 0 1).map (fun z => (z, z)) ≠ (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact constPair_ne_indepPair_of_secondCountable (gaussianReal 0 1)

end FormalizeSampling.Counterexamples.MarginalsNotPaths
