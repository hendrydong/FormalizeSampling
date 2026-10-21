module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Tensorisation of KL divergence over finite products

Status: **Verified** (probability measures; no further hypotheses).

`klDiv μ ν = KL(μ ‖ ν)` is Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`; both sides of
every identity below may be `∞`. The declarations live in the namespace
`FormalizeSampling.GaussianIncrement`, where they are applied to isotropic Gaussians.

## Main results

* `klDiv_map_measurableEquiv`: KL is invariant under measurable equivalences.
* `klDiv_prod_prod`: `KL(μ ⊗ μ' ‖ ν ⊗ ν') = KL(μ ‖ ν) + KL(μ' ‖ ν')` for probability measures.
* `klDiv_pi_pi`: `KL(⊗ᵢ μ i ‖ ⊗ᵢ ν i) = ∑ᵢ KL(μ i ‖ ν i)` over `Fin n`.

Proof: the chain rule `klDiv_compProd_eq_add` with constant kernels, a coordinate swap, and
induction on `n` through `MeasurableEquiv.piFinSuccAbove`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling
namespace GaussianIncrement

/-- **KL is invariant under measurable equivalences.** For finite measures `μ ν` on `α` and a
measurable equivalence `e : α ≃ᵐ β`, `KL(e₊μ ‖ e₊ν) = KL(μ ‖ ν)` (data processing in both
directions, `klDiv_map_le` for `e` and for `e.symm`). -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [Measure.map_map e.symm.measurable e.measurable,
    Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id,
    Measure.map_id] at this

/-- **KL tensorises over binary products.** For probability measures `μ ν` on `α` and `μ' ν'`
on `β`, `KL(μ ⊗ μ' ‖ ν ⊗ ν') = KL(μ ‖ ν) + KL(μ' ‖ ν')` (Mathlib's `klDiv`, in `ℝ≥0∞`; both
sides may be `∞`). No countability assumption on the spaces is needed. -/
theorem klDiv_prod_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (μ' ν' : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
    klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + klDiv μ' ν' := by
  rw [← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const]
  congr 1
  rw [← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodComm]
  change klDiv ((μ.prod μ').map Prod.swap) ((μ.prod ν').map Prod.swap) = _
  rw [Measure.prod_swap, Measure.prod_swap, ← Measure.compProd_const, ← Measure.compProd_const,
    klDiv_compProd_left]

/-- **KL tensorises over finite products.** For probability measures `μ i ν i` on spaces `α i`,
`i : Fin n`, `KL(⊗ᵢ μ i ‖ ⊗ᵢ ν i) = ∑ᵢ KL(μ i ‖ ν i)` (product measures `Measure.pi`;
Mathlib's `klDiv`, in `ℝ≥0∞`). -/
theorem klDiv_pi_pi {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
    have : Measure.pi μ = Measure.pi ν := by
      ext s hs
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · simp
      · have : s = Set.univ := Set.eq_univ_of_forall fun y => by
          rwa [Subsingleton.elim y x]
        simp [this]
    simp [this]
  | succ n ih =>
    rw [← klDiv_map_measurableEquiv _ _ (MeasurableEquiv.piFinSuccAbove α 0),
      (measurePreserving_piFinSuccAbove μ 0).map_eq,
      (measurePreserving_piFinSuccAbove ν 0).map_eq, klDiv_prod_prod, ih, Fin.sum_univ_succ]
    rfl

end GaussianIncrement
end FormalizeSampling
