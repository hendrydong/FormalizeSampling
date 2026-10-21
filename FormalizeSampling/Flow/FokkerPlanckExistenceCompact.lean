module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import FormalizeSampling.Flow.NoiseScoreEquivalence

/-!
# Weak limits of tight families identified by `C²_c` test functions

Status: **Verified.** Abstract compactness facts on `ProbabilityMeasure (Fin d → ℝ)` (weak
topology) used in the `Flow/FokkerPlanckExistence*.lean` files, from Mathlib's Prokhorov theorem
(`isCompact_closure_of_isTightMeasureSet`) and the fact that `C²_c` functions determine finite
measures (`NoiseScore.ext_of_forall_integral_testFunction2_eq`):

* `tendsto_of_isTight_of_integral_tendsto`: a tight family whose `C²_c` integrals converge to
  those of `ν` converges weakly to `ν`;
* `exists_tendsto_of_isTight`: a tight sequence whose `C²_c` integrals all converge has a weak
  limit;
* `measure_compl_closedBall_le_of_tendsto`: mass bounds outside balls pass to weak limits.

## Not proved here

* Nothing beyond `Fin d → ℝ`; no metric (Lévy–Prokhorov) rates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence
open NoiseScore

variable {d : ℕ}

/-- In `ℝ`, a cluster point of a map along `l` that converges to `c` equals `c`. -/
theorem mapClusterPt_eq {ι : Type*} {l : Filter ι} {g : ι → ℝ} {y c : ℝ}
    (hy : MapClusterPt y l g) (hg : Tendsto g l (𝓝 c)) : y = c := by
  have : (𝓝 y ⊓ 𝓝 c).NeBot := hy.neBot.mono (inf_le_inf_left _ hg)
  exact eq_of_nhds_neBot this

/-- A `C²_c` test function viewed as a bounded continuous function. -/
noncomputable def testBCF {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    BoundedContinuousFunction (Fin d → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup φ hφ.1.continuous
    (Classical.choose (hφ.1.continuous.bounded_above_of_compact_support hφ.2))
    (Classical.choose_spec (hφ.1.continuous.bounded_above_of_compact_support hφ.2))

/-- `μ ↦ ∫ φ dμ` is weakly continuous on probability measures for `φ ∈ C²_c`. -/
theorem continuous_integral_test {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    Continuous fun μ : ProbabilityMeasure (Fin d → ℝ) => ∫ x, φ x ∂(μ : Measure (Fin d → ℝ)) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction (testBCF hφ)

/-- **Prokhorov.** The probability measures lying in a tight set `S` have compact closure in
the weak topology. -/
theorem isCompact_closure_of_tight {S : Set (Measure (Fin d → ℝ))} (hS : IsTightMeasureSet S) :
    IsCompact (closure {μ : ProbabilityMeasure (Fin d → ℝ) | (μ : Measure (Fin d → ℝ)) ∈ S}) :=
  isCompact_closure_of_isTightMeasureSet (hS.subset (by rintro _ ⟨μ, hμ, rfl⟩; exact hμ))

/-- A weak cluster point `x` of `μ i` equals `ν` if `∫ φ dμ i → ∫ φ dν` for all `φ ∈ C²_c`. -/
theorem eq_of_mapClusterPt {ι : Type*} {l : Filter ι}
    {μ : ι → ProbabilityMeasure (Fin d → ℝ)} {ν x : ProbabilityMeasure (Fin d → ℝ)}
    (hx : MapClusterPt x l μ)
    (h : ∀ φ, TestFunction2 φ → Tendsto (fun i => ∫ x, φ x ∂(μ i : Measure (Fin d → ℝ))) l
      (𝓝 (∫ x, φ x ∂(ν : Measure (Fin d → ℝ))))) : x = ν := by
  apply Subtype.ext
  have := x.prop
  have := ν.prop
  refine ext_of_forall_integral_testFunction2_eq fun φ hφ => ?_
  have hc := hx.continuousAt_comp (continuous_integral_test hφ).continuousAt
  exact mapClusterPt_eq hc (h φ hφ)

/-- **Identification of weak limits by `C²_c` tests.** Let `μ i` (indexed along a filter `l`)
be probability measures eventually in a tight set `S`, and `ν` a probability measure such that
`∫ φ dμ i → ∫ φ dν` for every `C²` compactly supported `φ`. Then `μ i → ν` weakly. -/
theorem tendsto_of_isTight_of_integral_tendsto {ι : Type*} {l : Filter ι}
    {μ : ι → ProbabilityMeasure (Fin d → ℝ)} {S : Set (Measure (Fin d → ℝ))}
    (hS : IsTightMeasureSet S) (hμ : ∀ᶠ i in l, (μ i : Measure (Fin d → ℝ)) ∈ S)
    {ν : ProbabilityMeasure (Fin d → ℝ)}
    (h : ∀ φ, TestFunction2 φ → Tendsto (fun i => ∫ x, φ x ∂(μ i : Measure (Fin d → ℝ))) l
      (𝓝 (∫ x, φ x ∂(ν : Measure (Fin d → ℝ))))) :
    Tendsto μ l (𝓝 ν) :=
  (isCompact_closure_of_tight hS).tendsto_nhds_of_unique_mapClusterPt
    (hμ.mono fun _ hi => subset_closure hi) fun _ _ hx => eq_of_mapClusterPt hx h

/-- **Existence of a weak limit.** A sequence of probability measures in a tight set whose
integrals `∫ φ dμ n` converge for every `C²` compactly supported `φ` converges weakly. -/
theorem exists_tendsto_of_isTight {μ : ℕ → ProbabilityMeasure (Fin d → ℝ)}
    {S : Set (Measure (Fin d → ℝ))} (hS : IsTightMeasureSet S)
    (hμ : ∀ n, (μ n : Measure (Fin d → ℝ)) ∈ S)
    (h : ∀ φ, TestFunction2 φ → ∃ c, Tendsto (fun n => ∫ x, φ x ∂(μ n : Measure (Fin d → ℝ)))
      atTop (𝓝 c)) :
    ∃ ν, Tendsto μ atTop (𝓝 ν) := by
  obtain ⟨ν, -, hν⟩ := (isCompact_closure_of_tight hS).exists_mapClusterPt (f := atTop) (u := μ)
    (by
      rw [le_principal_iff]
      exact Filter.mem_map.2 (Eventually.of_forall fun n => subset_closure (hμ n)))
  refine ⟨ν, tendsto_of_isTight_of_integral_tendsto hS (Eventually.of_forall hμ) fun φ hφ => ?_⟩
  obtain ⟨c, hc⟩ := h φ hφ
  have := mapClusterPt_eq ((hν.continuousAt_comp (continuous_integral_test hφ).continuousAt)) hc
  rw [show (∫ x, φ x ∂(ν : Measure (Fin d → ℝ))) = c from this]
  exact hc

/-- **Mass outside a ball passes to weak limits.** If `μ i → ν` weakly along a non-trivial
filter and eventually `μ i (closedBall 0 R)ᶜ ≤ ε`, then `ν (closedBall 0 R)ᶜ ≤ ε` (portmanteau,
open sets). -/
theorem measure_compl_closedBall_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → ProbabilityMeasure (Fin d → ℝ)} {ν : ProbabilityMeasure (Fin d → ℝ)}
    (hμν : Tendsto μ l (𝓝 ν)) {R : ℝ} {ε : ℝ≥0∞}
    (h : ∀ᶠ i in l, (μ i : Measure (Fin d → ℝ)) (closedBall 0 R)ᶜ ≤ ε) :
    (ν : Measure (Fin d → ℝ)) (closedBall 0 R)ᶜ ≤ ε :=
  (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμν isClosed_closedBall.isOpen_compl).trans
    (liminf_le_of_frequently_le' h.frequently)

end FormalizeSampling.FokkerPlanckExistence
