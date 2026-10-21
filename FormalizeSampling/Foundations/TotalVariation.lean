module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Total variation distance on a general measurable space

This file defines the total variation (TV) distance between measures on an arbitrary measurable
space `α` (no topology is used anywhere) and proves the basic facts needed to compose
sampling-error certificates (see `FormalizeSampling/Kernels/ErrorPropagation.lean`).

The distance is called `tvSup` (a supremum over sets). Mathlib (since v4.35) has its own
`MeasureTheory.tvDist`, the `L¹` normalisation `‖μ - ν‖₁`; for probability measures it takes
values in `[0, 2]` and equals `2 * tvSup μ ν` (`measureTheory_tvDist_eq_two_mul`). The distinct
names let both namespaces be opened together.

## Convention

`tvSup μ ν = sup_{A measurable} |μ(A) - ν(A)|`, with the measures of sets taken as real numbers
through `Measure.real` (`μ.real A = (μ A).toReal`). This is the probabilists' normalisation: for
probability measures `tvSup ≤ 1`, `tvSup` is half of Mathlib's `MeasureTheory.tvDist`, and on a
finite space it equals `½ ∑ₓ |μ{x} - ν{x}|` (an identity not formalised here). This convention is
used throughout. The supremum is a real `iSup`, which Lean sets to `0` for an unbounded family,
and `(μ A).toReal = 0` when `μ A = ∞`; therefore **all statements below that are not trivially
true assume finite (or probability) measures**, where the family is bounded by `μ(α) + ν(α)`
(`bddAbove_range_abs_sub`) and the definition means what it says.

## Main results

* `tvSup_nonneg`, `tvSup_comm`, `tvSup_self` (any measures);
* `abs_measureReal_sub_le_tvSup`, `tvSup_le_of_forall`, `tvSup_le_iff`,
  `tvSup_triangle`, `tvSup_eq_zero_iff` (finite measures);
* `tvSup_le_one` (probability measures), and the non-degeneracy check
  `tvSup_dirac_of_ne` (`tvSup δ_a δ_b = 1` for `a ≠ b`, measurable singletons);
* `tvSup_map_le` (data processing under measurable maps, finite measures) and
  `tvSup_map_measurableEquiv` (invariance under measurable equivalences, any measures);
* the key duality bound `abs_integral_sub_integral_le_tvSup`: for finite measures `μ ν` and a
  measurable `f` with `0 ≤ f ≤ 1`, `|∫ f dμ - ∫ f dν| ≤ tvSup μ ν`, proved with Mathlib's
  measure-level Hahn decomposition `MeasureTheory.hahn_decomposition`;
* its rescaled corollaries for probability measures: `a ≤ f ≤ b` gives the factor `b - a`
  (`abs_integral_sub_integral_le_mul_tvSup`) and `|f| ≤ M` gives the factor `2 M`
  (`abs_integral_sub_integral_le_two_mul_tvSup`);
* the bridge `measureTheory_tvDist_eq_two_mul` to Mathlib's `L¹` normalisation.

Registry: foundations for KR-1 (kernel TV propagation, `Kernels/ErrorPropagation.lean`) and
KL-1 (Pinsker, `Foundations/Pinsker.lean`).

## Not proved here

* The variational formula `tvSup μ ν = sup_{0 ≤ f ≤ 1 measurable} |∫ f dμ - ∫ f dν|` is not
  stated as an equality; only `|∫ f dμ - ∫ f dν| ≤ tvSup μ ν` (the direction used for error
  propagation) is proved.
* No identification of `tvSup` with `½ ∑ₓ |μ{x} - ν{x}|` on finite spaces, with `½ ∫ |p - q|`
  for densities, or with couplings. The identification with Mathlib's signed-measure total
  variation (`measureTheory_tvDist_eq_two_mul`) is proved for probability measures only.
* No `MetricSpace` instance on probability measures is built (the metric properties are
  proved as separate lemmas).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace FormalizeSampling
namespace TotalVariation

variable {α : Type*} [MeasurableSpace α]

/-- The **total variation distance** `tvSup μ ν = sup_{A measurable} |μ(A) - ν(A)|` between two
measures on a measurable space, using the real-valued measures `μ.real A = (μ A).toReal`.
It is meaningful for finite measures (for which the supremum is bounded); for infinite measures
Lean's conventions (`∞.toReal = 0`, unbounded real `iSup = 0`) make it degenerate, so every
nontrivial result below assumes finite or probability measures. -/
noncomputable def tvSup (μ ν : Measure α) : ℝ :=
  ⨆ s : {s : Set α // MeasurableSet s}, |μ.real s.1 - ν.real s.1|

private lemma nonempty_measurableSets : Nonempty {s : Set α // MeasurableSet s} :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩

/-- `0 ≤ tvSup μ ν` for all measures `μ ν` (no finiteness needed). -/
theorem tvSup_nonneg (μ ν : Measure α) : 0 ≤ tvSup μ ν :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- Symmetry: `tvSup μ ν = tvSup ν μ` for all measures `μ ν`. -/
theorem tvSup_comm (μ ν : Measure α) : tvSup μ ν = tvSup ν μ := by
  simp only [tvSup, abs_sub_comm]

/-- `tvSup μ μ = 0` for every measure `μ`. -/
theorem tvSup_self (μ : Measure α) : tvSup μ μ = 0 := by
  simp [tvSup]

/-- For finite measures and every set `A`, `|μ(A) - ν(A)| ≤ μ(α) + ν(α)`. -/
theorem abs_measureReal_sub_le (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set α) : |μ.real s - ν.real s| ≤ μ.real univ + ν.real univ := by
  have h1 : μ.real s ≤ μ.real univ := measureReal_mono (subset_univ s)
  have h2 : ν.real s ≤ ν.real univ := measureReal_mono (subset_univ s)
  have h3 : 0 ≤ μ.real s := measureReal_nonneg
  have h4 : 0 ≤ ν.real s := measureReal_nonneg
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- For finite measures `μ ν`, the family `A ↦ |μ(A) - ν(A)|` over measurable sets is bounded
above (by `μ(α) + ν(α)`), so the supremum defining `tvSup μ ν` is a genuine supremum. -/
theorem bddAbove_range_abs_sub (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove (range fun s : {s : Set α // MeasurableSet s} => |μ.real s.1 - ν.real s.1|) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact abs_measureReal_sub_le μ ν s.1

/-- For finite measures `μ ν` and every measurable set `A`, `|μ(A) - ν(A)| ≤ tvSup μ ν`. -/
theorem abs_measureReal_sub_le_tvSup {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) : |μ.real s - ν.real s| ≤ tvSup μ ν :=
  le_ciSup (f := fun s : {s : Set α // MeasurableSet s} => |μ.real s.1 - ν.real s.1|)
    (bddAbove_range_abs_sub μ ν) ⟨s, hs⟩

/-- Upper bounds on `tvSup`: if `|μ(A) - ν(A)| ≤ c` for every measurable set `A`, then
`tvSup μ ν ≤ c` (for any measures `μ ν`). -/
theorem tvSup_le_of_forall {μ ν : Measure α} {c : ℝ}
    (h : ∀ s, MeasurableSet s → |μ.real s - ν.real s| ≤ c) : tvSup μ ν ≤ c := by
  have := nonempty_measurableSets (α := α)
  exact ciSup_le fun s => h s.1 s.2

/-- For finite measures, `tvSup μ ν ≤ c` iff `|μ(A) - ν(A)| ≤ c` for every measurable `A`. -/
theorem tvSup_le_iff {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ} :
    tvSup μ ν ≤ c ↔ ∀ s, MeasurableSet s → |μ.real s - ν.real s| ≤ c :=
  ⟨fun h _ hs => (abs_measureReal_sub_le_tvSup hs).trans h, tvSup_le_of_forall⟩

/-- For probability measures `μ ν`, `tvSup μ ν ≤ 1`. -/
theorem tvSup_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvSup μ ν ≤ 1 := by
  refine tvSup_le_of_forall fun s _ => ?_
  have h1 : μ.real s ≤ 1 := measureReal_le_one
  have h2 : ν.real s ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ μ.real s := measureReal_nonneg
  have h4 : 0 ≤ ν.real s := measureReal_nonneg
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- Triangle inequality: for finite measures `μ ν ρ`,
`tvSup μ ρ ≤ tvSup μ ν + tvSup ν ρ`. -/
theorem tvSup_triangle (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] : tvSup μ ρ ≤ tvSup μ ν + tvSup ν ρ :=
  tvSup_le_of_forall fun _ hs => (abs_sub_le _ _ _).trans
    (add_le_add (abs_measureReal_sub_le_tvSup hs) (abs_measureReal_sub_le_tvSup hs))

/-- For finite measures, `tvSup μ ν = 0` iff `μ = ν` (so `tvSup` separates finite measures). -/
theorem tvSup_eq_zero_iff {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvSup μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    ext s hs
    have h1 := abs_measureReal_sub_le_tvSup (μ := μ) (ν := ν) hs
    rw [h, abs_nonpos_iff, sub_eq_zero] at h1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).1 h1
  · rintro rfl
    exact tvSup_self μ

/-- Non-degeneracy check: on a space with measurable singletons, two Dirac masses at distinct
points `a ≠ b` are at the maximal distance, `tvSup (δ_a) (δ_b) = 1`. -/
theorem tvSup_dirac_of_ne [MeasurableSingletonClass α] {a b : α} (hab : a ≠ b) :
    tvSup (Measure.dirac a) (Measure.dirac b) = 1 := by
  refine le_antisymm (tvSup_le_one _ _) ?_
  have h := abs_measureReal_sub_le_tvSup (μ := Measure.dirac a) (ν := Measure.dirac b)
    (measurableSet_singleton a)
  have h1 : (Measure.dirac a).real {a} = 1 := by simp [measureReal_def]
  have h2 : (Measure.dirac b).real {a} = 0 := by simp [measureReal_def, hab.symm]
  rw [h1, h2] at h
  simpa using h

/-- **Data processing for `tvSup` under measurable maps.** For finite measures `μ ν` on `α` and
a measurable `g : α → β`, `tvSup (g₊μ) (g₊ν) ≤ tvSup μ ν`: every event `B` of `β` pulls back
to the event `g⁻¹(B)` of `α`. -/
theorem tvSup_map_le {β : Type*} [MeasurableSpace β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {g : α → β} (hg : Measurable g) :
    tvSup (μ.map g) (ν.map g) ≤ tvSup μ ν := by
  refine tvSup_le_of_forall fun s hs => ?_
  rw [map_measureReal_apply hg hs, map_measureReal_apply hg hs]
  exact abs_measureReal_sub_le_tvSup (hg hs)

/-- **`tvSup` is invariant under measurable equivalences.** For all measures `μ ν` on `α` (no
finiteness needed) and a measurable equivalence `e : α ≃ᵐ β`,
`tvSup (e₊μ) (e₊ν) = tvSup μ ν`: `B ↦ e⁻¹(B)` is a bijection between the events of `β` and
those of `α`. -/
theorem tvSup_map_measurableEquiv {β : Type*} [MeasurableSpace β] (μ ν : Measure α)
    (e : α ≃ᵐ β) : tvSup (μ.map e) (ν.map e) = tvSup μ ν := by
  let E : {s : Set β // MeasurableSet s} ≃ {s : Set α // MeasurableSet s} :=
    { toFun := fun s => ⟨e ⁻¹' s.1, e.measurable s.2⟩
      invFun := fun s => ⟨e.symm ⁻¹' s.1, e.symm.measurable s.2⟩
      left_inv := fun s => Subtype.ext (by simp [Set.preimage_preimage])
      right_inv := fun s => Subtype.ext (by simp [Set.preimage_preimage]) }
  unfold tvSup
  rw [← E.iSup_comp]
  refine iSup_congr fun s => ?_
  simp only [measureReal_def, e.map_apply, E, Equiv.coe_fn_mk]

/-- A measurable function with values in `[0, 1]` is integrable for every finite measure. -/
private lemma integrable_of_unit {ρ : Measure α} [IsFiniteMeasure ρ] {f : α → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hf1 x)

/-- One-sided duality bound. For finite measures `μ ν` and a measurable `f` with `0 ≤ f ≤ 1`,
`∫ f dμ - ∫ f dν ≤ tvSup μ ν`. Proof: take a Hahn set `S` for `μ - ν`; on `S` use
`∫_S (1 - f) dν ≤ ∫_S (1 - f) dμ`, on `Sᶜ` use `∫_{Sᶜ} f dμ ≤ ∫_{Sᶜ} f dν`, so the difference
is at most `μ(S) - ν(S)`. -/
theorem integral_sub_integral_le_tvSup {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) : ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ tvSup μ ν := by
  obtain ⟨s, hs, hpos, hneg⟩ := hahn_decomposition μ ν
  have hle1 : ν.restrict s ≤ μ.restrict s := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hpos _ (ht.inter hs) inter_subset_right
  have hle2 : μ.restrict sᶜ ≤ ν.restrict sᶜ := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hneg _ (ht.inter hs.compl) inter_subset_right
  have h1 : ∫ x in s, (1 - f x) ∂ν ≤ ∫ x in s, (1 - f x) ∂μ :=
    integral_mono_measure hle1 (Filter.Eventually.of_forall fun x => sub_nonneg.2 (hf1 x))
      ((integrable_const 1).sub (integrable_of_unit hf hf0 hf1))
  have h2 : ∫ x in sᶜ, f x ∂μ ≤ ∫ x in sᶜ, f x ∂ν :=
    integral_mono_measure hle2 (Filter.Eventually.of_forall hf0) (integrable_of_unit hf hf0 hf1)
  rw [integral_sub (integrable_const 1) (integrable_of_unit hf hf0 hf1),
    integral_sub (integrable_const 1) (integrable_of_unit hf hf0 hf1), setIntegral_const,
    setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
  have hμs : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
    integral_add_compl hs (integrable_of_unit hf hf0 hf1)
  have hνs : ∫ x in s, f x ∂ν + ∫ x in sᶜ, f x ∂ν = ∫ x, f x ∂ν :=
    integral_add_compl hs (integrable_of_unit hf hf0 hf1)
  have h3 := abs_measureReal_sub_le_tvSup (μ := μ) (ν := ν) hs
  have h4 := le_abs_self (μ.real s - ν.real s)
  linarith

/-- **Duality bound (key lemma).** For finite measures `μ ν` on a measurable space and a
measurable `f` with `0 ≤ f ≤ 1` everywhere, `|∫ f dμ - ∫ f dν| ≤ tvSup μ ν`. -/
theorem abs_integral_sub_integral_le_tvSup {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) : |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ tvSup μ ν := by
  refine abs_sub_le_iff.2 ⟨integral_sub_integral_le_tvSup hf hf0 hf1, ?_⟩
  rw [tvSup_comm]
  exact integral_sub_integral_le_tvSup hf hf0 hf1

/-- **Rescaled duality bound.** For probability measures `μ ν` and a measurable `f` with
`a ≤ f ≤ b` everywhere, `|∫ f dμ - ∫ f dν| ≤ (b - a) * tvSup μ ν`. -/
theorem abs_integral_sub_integral_le_mul_tvSup {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (hab : ∀ x, f x ∈ Icc a b) : |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (b - a) * tvSup μ ν := by
  obtain ⟨x₀⟩ := Measure.nonempty_of_neZero μ
  have hc : 0 ≤ b - a := sub_nonneg.2 ((hab x₀).1.trans (hab x₀).2)
  rcases hc.eq_or_lt with hc | hc
  · have hfa : f = fun _ => a := by
      funext x
      exact le_antisymm (by linarith [(hab x).2]) (hab x).1
    simp [hfa, ← hc]
  · set g : α → ℝ := fun x => (f x - a) / (b - a) with hg
    have hgm : Measurable g := (hf.sub_const a).div_const _
    have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (sub_nonneg.2 (hab x).1) hc.le
    have hg1 : ∀ x, g x ≤ 1 := fun x =>
      (div_le_one hc).2 (by linarith [(hab x).2])
    have hfg : f = fun x => a + (b - a) * g x := by
      funext x
      simp only [hg]
      field_simp
      ring
    have hint : ∀ ρ : Measure α, IsProbabilityMeasure ρ →
        ∫ x, f x ∂ρ = a + (b - a) * ∫ x, g x ∂ρ := by
      intro ρ _
      rw [hfg, integral_add (integrable_const a) ((integrable_of_unit hgm hg0 hg1).const_mul _),
        integral_const_mul, integral_const, probReal_univ, one_smul]
    rw [hint μ inferInstance, hint ν inferInstance, add_sub_add_left_eq_sub, ← mul_sub,
      abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (abs_integral_sub_integral_le_tvSup hgm hg0 hg1) hc.le

/-- **Bounded test functions.** For probability measures `μ ν` and a measurable `f` with
`|f| ≤ M` everywhere, `|∫ f dμ - ∫ f dν| ≤ 2 * M * tvSup μ ν`. -/
theorem abs_integral_sub_integral_le_two_mul_tvSup {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : α → ℝ} {M : ℝ} (hf : Measurable f) (hM : ∀ x, |f x| ≤ M) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 2 * M * tvSup μ ν := by
  have h := abs_integral_sub_integral_le_mul_tvSup (μ := μ) (ν := ν) hf
    (a := -M) (b := M) fun x => abs_le.1 (hM x)
  rwa [show M - -M = 2 * M by ring] at h

/-- **Bridge to Mathlib's TV distance.** For probability measures, Mathlib's
`MeasureTheory.tvDist` (the `L¹` norm `‖μ - ν‖₁`, values in `[0, 2]`) is twice this library's
`tvSup μ ν = sup_A |μ(A) - ν(A)|`. Proof: both are computed on a Hahn set of `μ - ν`. -/
theorem measureTheory_tvDist_eq_two_mul (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : MeasureTheory.tvDist μ ν = 2 * tvSup μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsm := hs.measurableSet
  have hle : ∀ A, MeasurableSet A → μ.real (s ∩ A) ≤ ν.real (s ∩ A) := fun A hA => by
    have h := hs.le_on A
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Set.inter_comm] at h
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 h
  have hge : ∀ A, MeasurableSet A → ν.real (sᶜ ∩ A) ≤ μ.real (sᶜ ∩ A) := fun A hA => by
    have h := hs.ge_on_compl A
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Set.inter_comm] at h
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 h
  -- `m (Y ∩ X) + m (Yᶜ ∩ X) = m X`
  have split : ∀ (m : Measure α) [IsFiniteMeasure m] (X Y : Set α), MeasurableSet Y →
      m.real (Y ∩ X) + m.real (Yᶜ ∩ X) = m.real X := fun m _ X Y hY => by
    rw [Set.inter_comm Y X, Set.inter_comm Yᶜ X, ← Set.sdiff_eq]
    exact measureReal_inter_add_sdiff hY
  have hcμ := probReal_compl_eq_one_sub (μ := μ) hsm
  have hcν := probReal_compl_eq_one_sub (μ := ν) hsm
  have hT : tvSup μ ν = ν.real s - μ.real s := by
    apply le_antisymm
    · refine tvSup_le_of_forall fun A hA => abs_sub_le_iff.2 ⟨?_, ?_⟩
      · have a1 := split μ A s hsm
        have a2 := split ν A s hsm
        have c1 := split μ sᶜ A hA
        have c2 := split ν sᶜ A hA
        rw [Set.inter_comm A sᶜ, Set.inter_comm Aᶜ sᶜ] at c1 c2
        have := hle A hA
        have := hge Aᶜ hA.compl
        linarith
      · have a1 := split μ A s hsm
        have a2 := split ν A s hsm
        have c1 := split μ s A hA
        have c2 := split ν s A hA
        rw [Set.inter_comm A s, Set.inter_comm Aᶜ s] at c1 c2
        have := hge A hA
        have := hle Aᶜ hA.compl
        linarith
    · have := abs_measureReal_sub_le_tvSup (μ := μ) (ν := ν) hsm
      rw [abs_sub_comm] at this
      exact (le_abs_self _).trans this
  rw [hs.tvDist_eq, hT, hcμ, hcν]
  ring

end TotalVariation
end FormalizeSampling
