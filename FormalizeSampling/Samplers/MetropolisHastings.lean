module

public import Mathlib.Probability.Kernel.Invariance

/-!
# Metropolis–Hastings with densities on a general measurable space

Scope. A measurable space `Ω` with an s-finite reference measure `ν` (every σ-finite measure,
e.g. Lebesgue measure, is s-finite), a measurable **unnormalised** target density
`π : Ω → ℝ≥0∞` and a jointly measurable proposal density `q : Ω → Ω → ℝ≥0∞`
(`q x ·` is the `ν`-density of the proposal law from `x`). All arithmetic is in `ℝ≥0∞`.
The target law is `ν.withDensity π`; it need not be normalised, finite or σ-finite.

## Conventions and degenerate cases

* Acceptance probability: `acceptance π q x y = min 1 (π y * q y x / (π x * q x y))`, with
  `ℝ≥0∞` division (`a / b = a * b⁻¹`, `0⁻¹ = ∞`, `∞⁻¹ = 0`, `0 * ∞ = 0`). Hence
  - if `π x * q x y = 0 < π y * q y x`, the ratio is `∞` and the acceptance is `1`, the textbook
    convention (`acceptance_eq_one_of_eq_zero`);
  - if `π x * q x y = 0 = π y * q y x`, the ratio is `0 / 0 = 0` and the acceptance is `0`
    (the textbook value is `1`). If `π x > 0` this case forces `q x y = 0`, i.e. the move is
    proposed with density `0`, so `K(x, ·)` is unaffected; the kernel can differ from the
    textbook one only at `π`-null starting points (`π x = 0`). No result below depends on it;
  - if `π x * q x y = ∞`, the formula is meaningless; every balance statement therefore
    assumes `π x * q x y ≠ ∞` for all `x y` (e.g. `π < ∞` and `q < ∞` pointwise).
* `acceptProb ν π q x = ∫⁻ y, q x y * acceptance π q x y ∂ν` is the probability that the
  proposed move is accepted and `rejectProb ν π q x = 1 - acceptProb ν π q x` (truncated
  subtraction) the rejection probability. When `∫⁻ y, q x y ∂ν = 1` we have
  `acceptProb ≤ 1`, so the truncation is invisible (`acceptProb_add_rejectProb`).
* MH transition law from `x`:
  `mhMeasure ν π q x = ν.withDensity (fun y ↦ q x y * acceptance π q x y)
     + rejectProb ν π q x • dirac x`
  (accepted part plus rejected part). `mhKernel` packages it as a Mathlib
  `ProbabilityTheory.Kernel Ω Ω` (it takes the measurability proofs of `π` and `q`).
* `μ.bind κ` is the law after one step started from `μ`.

## Main results (registry ID MH-1)

* `mul_acceptance_eq_min`, `detailed_balance`: off-diagonal detailed balance
  `π x q(x,y) α(x,y) = min (π x q(x,y)) (π y q(y,x)) = π y q(y,x) α(y,x)`, assuming only
  finiteness of `π x q(x,y)` and `π y q(y,x)`.
* `isProbabilityMeasure_mhMeasure`, `isMarkovKernel_mhKernel`: the MH law from every state is
  a probability measure when `∫⁻ y, q x y ∂ν = 1`.
* `measurable_mhMeasure`: `x ↦ mhMeasure ν π q x` is measurable (so `mhKernel` is a kernel).
* `setLIntegral_mul_mhMeasure_comm`, `isReversible_mhKernel` (reversibility): for measurable
  `A`, `B`, `∫⁻ x in A, π x * K(x, B) ∂ν = ∫⁻ x in B, π x * K(x, A) ∂ν`, i.e. the joint law
  `π(dx) K(x, dy)` gives equal mass to `A × B` and `B × A` (Mathlib's
  `Kernel.IsReversible`). This needs no normalisation of `q`.
* `lintegral_mul_mhMeasure`, `invariant_mhKernel`, `bind_mhKernel` (invariance): for
  normalised `q`, `∫⁻ x, π x * K(x, A) ∂ν = ∫⁻ x in A, π x ∂ν`, i.e.
  `(ν.withDensity π).bind (mhKernel ν hπ hq) = ν.withDensity π` (Mathlib's
  `Kernel.Invariant`). The proof splits `K` into its accepted and rejected parts and uses
  pointwise detailed balance plus Tonelli (`lintegral_lintegral_swap`).
* `map_swap_compProd_mhKernel`: if moreover `∫⁻ x, π x ∂ν < ∞`, the two-time joint law
  `(ν.withDensity π) ⊗ₘ K` is invariant under `Prod.swap` (reversibility as an equality of
  measures on `Ω × Ω`).

## Not proved here

* Convergence, ergodicity, `π`-irreducibility, aperiodicity, mixing or uniqueness of the
  invariant law; only one-step reversibility and invariance are proved.
* Swap invariance of the joint law `(ν.withDensity π) ⊗ₘ K` for targets of infinite mass
  (only equality on measurable rectangles is proved then).
* Proposals without a `ν`-density (e.g. deterministic or mixed proposals) and acceptance
  functions other than the Metropolis–Hastings ratio (e.g. Barker).
* Anything for targets or proposals with `π x * q x y = ∞` somewhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace FormalizeSampling.MH

/-! ### Acceptance probability and pointwise detailed balance -/

section Acceptance

variable {Ω : Type*}

/-- The Metropolis–Hastings acceptance probability
`α(x, y) = min 1 (π(y) q(y, x) / (π(x) q(x, y)))`, computed in `ℝ≥0∞`. If
`π(x) q(x, y) = 0 < π(y) q(y, x)` it equals `1`; if both products vanish it equals `0`. -/
noncomputable def acceptance (π : Ω → ℝ≥0∞) (q : Ω → Ω → ℝ≥0∞) (x y : Ω) : ℝ≥0∞ :=
  min 1 (π y * q y x / (π x * q x y))

variable {π : Ω → ℝ≥0∞} {q : Ω → Ω → ℝ≥0∞}

/-- The acceptance probability is at most `1`. -/
theorem acceptance_le_one (x y : Ω) : acceptance π q x y ≤ 1 :=
  min_le_left _ _

/-- Textbook convention for moves into the support: if `π(x) q(x, y) = 0` while
`π(y) q(y, x) ≠ 0`, the acceptance probability is `1`. -/
theorem acceptance_eq_one_of_eq_zero {x y : Ω} (hxy : π x * q x y = 0)
    (hyx : π y * q y x ≠ 0) : acceptance π q x y = 1 := by
  simp [acceptance, hxy, ENNReal.div_zero hyx]

/-- The acceptance probability is positive whenever the reverse flux `π(y) q(y, x)` is nonzero
and the forward flux `π(x) q(x, y)` is finite. (So MH with a positive target and a positive
proposal never rejects with certainty; invariance below is not obtained by always rejecting.)
-/
theorem acceptance_pos {x y : Ω} (hxy : π x * q x y ≠ ∞) (hyx : π y * q y x ≠ 0) :
    0 < acceptance π q x y :=
  lt_min one_pos (ENNReal.div_pos_iff.2 ⟨hyx, hxy⟩)

/-- **Off-diagonal detailed balance, one side.** If `π(x) q(x, y) < ∞`, then
`π(x) q(x, y) α(x, y) = min (π(x) q(x, y)) (π(y) q(y, x))`. -/
theorem mul_acceptance_eq_min {x y : Ω} (hxy : π x * q x y ≠ ∞) :
    π x * q x y * acceptance π q x y = min (π x * q x y) (π y * q y x) := by
  unfold acceptance
  rw [mul_min_of_nonneg _ _ zero_le, mul_one]
  by_cases h0 : π x * q x y = 0
  · simp [h0]
  · rw [ENNReal.mul_div_cancel h0 hxy]

/-- **Off-diagonal detailed balance (MH-1).** If `π(x) q(x, y) < ∞` and `π(y) q(y, x) < ∞`,
then `π(x) q(x, y) α(x, y) = π(y) q(y, x) α(y, x)`; both sides equal
`min (π(x) q(x, y)) (π(y) q(y, x))`. No positivity is needed. -/
theorem detailed_balance {x y : Ω} (hxy : π x * q x y ≠ ∞) (hyx : π y * q y x ≠ ∞) :
    π x * q x y * acceptance π q x y = π y * q y x * acceptance π q y x := by
  rw [mul_acceptance_eq_min hxy, mul_acceptance_eq_min hyx, min_comm]

end Acceptance

variable {Ω : Type*} [MeasurableSpace Ω] {π : Ω → ℝ≥0∞} {q : Ω → Ω → ℝ≥0∞}

/-- The acceptance probability is jointly measurable when `π` is measurable and `q` is jointly
measurable. -/
theorem measurable_acceptance (hπ : Measurable π) (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (acceptance π q)) := by
  have hq' : Measurable fun p : Ω × Ω => q p.2 p.1 := hq.comp measurable_swap
  have h1 : Measurable fun p : Ω × Ω => π p.2 * q p.2 p.1 := (hπ.comp measurable_snd).mul hq'
  have h2 : Measurable fun p : Ω × Ω => π p.1 * q p.1 p.2 := (hπ.comp measurable_fst).mul hq
  exact measurable_const.min (h1.div h2)

/-! ### The Metropolis–Hastings transition law -/

/-- Acceptance probability from `x`: `a(x) = ∫⁻ y, q(x, y) α(x, y) dν(y)`. -/
noncomputable def acceptProb (ν : Measure Ω) (π : Ω → ℝ≥0∞) (q : Ω → Ω → ℝ≥0∞) (x : Ω) :
    ℝ≥0∞ :=
  ∫⁻ y, q x y * acceptance π q x y ∂ν

/-- Rejection probability from `x`: `r(x) = 1 - a(x)` (truncated subtraction in `ℝ≥0∞`; it is
the true complement whenever `∫⁻ y, q x y ∂ν ≤ 1`, see `acceptProb_le_one`). -/
noncomputable def rejectProb (ν : Measure Ω) (π : Ω → ℝ≥0∞) (q : Ω → Ω → ℝ≥0∞) (x : Ω) :
    ℝ≥0∞ :=
  1 - acceptProb ν π q x

/-- The Metropolis–Hastings transition law from `x`: the accepted part, with sub-probability
density `y ↦ q(x, y) α(x, y)` with respect to `ν`, plus the rejection mass `r(x)` at `x`. -/
noncomputable def mhMeasure (ν : Measure Ω) (π : Ω → ℝ≥0∞) (q : Ω → Ω → ℝ≥0∞) (x : Ω) :
    Measure Ω :=
  ν.withDensity (fun y => q x y * acceptance π q x y) + rejectProb ν π q x • Measure.dirac x

variable {ν : Measure Ω}

/-- If the proposal from `x` has total mass at most `1`, the acceptance probability `a(x)` is at
most `1`. -/
theorem acceptProb_le_one {x : Ω} (hq1 : ∫⁻ y, q x y ∂ν ≤ 1) : acceptProb ν π q x ≤ 1 := by
  refine le_trans (lintegral_mono fun y => ?_) hq1
  calc q x y * acceptance π q x y ≤ q x y * 1 := by gcongr; exact acceptance_le_one x y
    _ = q x y := mul_one _

/-- If the proposal from `x` has total mass at most `1`, acceptance and rejection probabilities
add up to `1`. -/
theorem acceptProb_add_rejectProb {x : Ω} (hq1 : ∫⁻ y, q x y ∂ν ≤ 1) :
    acceptProb ν π q x + rejectProb ν π q x = 1 :=
  add_tsub_cancel_of_le (acceptProb_le_one hq1)

/-- Value of the MH law on a measurable set:
`K(x, A) = ∫⁻ y in A, q(x, y) α(x, y) dν(y) + r(x) 1_A(x)`. -/
theorem mhMeasure_apply (x : Ω) {A : Set Ω} (hA : MeasurableSet A) :
    mhMeasure ν π q x A
      = (∫⁻ y in A, q x y * acceptance π q x y ∂ν) + rejectProb ν π q x * A.indicator 1 x := by
  simp [mhMeasure, withDensity_apply _ hA, Measure.dirac_apply' _ hA]

/-- **The MH law is a probability measure (MH-1).** If the proposal density from `x` is
normalised, `∫⁻ y, q(x, y) dν(y) = 1`, then `mhMeasure ν π q x` is a probability measure. -/
theorem isProbabilityMeasure_mhMeasure {x : Ω} (hq1 : ∫⁻ y, q x y ∂ν = 1) :
    IsProbabilityMeasure (mhMeasure ν π q x) := by
  constructor
  rw [mhMeasure_apply x MeasurableSet.univ, Measure.restrict_univ]
  simpa [acceptProb] using acceptProb_add_rejectProb (ν := ν) (π := π) (q := q) hq1.le

/-- For measurable `π` and jointly measurable `q` (and s-finite `ν`), the map
`x ↦ mhMeasure ν π q x` is measurable, i.e. `x ↦ K(x, A)` is measurable for measurable `A`. -/
theorem measurable_mhMeasure [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) : Measurable (mhMeasure ν π q) := by
  have hg : Measurable (Function.uncurry fun x y => q x y * acceptance π q x y) :=
    hq.mul (measurable_acceptance hπ hq)
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp_rw [mhMeasure_apply _ hA]
  have h1 : Measurable fun x => ∫⁻ y in A, q x y * acceptance π q x y ∂ν :=
    hg.lintegral_prod_right
  have h2 : Measurable (rejectProb ν π q) :=
    measurable_const.sub (hg.lintegral_prod_right (ν := ν))
  exact h1.add (h2.mul (measurable_const.indicator hA))

/-- The Metropolis–Hastings transition kernel `x ↦ mhMeasure ν π q x` as a Mathlib kernel. It
takes the measurability of `π` and the joint measurability of `q` as arguments; it is a Markov
kernel when `q` is normalised (`isMarkovKernel_mhKernel`). -/
noncomputable def mhKernel (ν : Measure Ω) [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) : Kernel Ω Ω where
  toFun := mhMeasure ν π q
  measurable' := measurable_mhMeasure hπ hq

/-- The kernel `mhKernel` evaluates to `mhMeasure`. -/
theorem mhKernel_apply [SFinite ν] (hπ : Measurable π) (hq : Measurable (Function.uncurry q))
    (x : Ω) : mhKernel ν hπ hq x = mhMeasure ν π q x :=
  rfl

/-- **The MH kernel is Markov (MH-1).** If every proposal density is normalised,
`∫⁻ y, q(x, y) dν(y) = 1` for all `x`, then `mhKernel ν hπ hq` is a Markov kernel. -/
theorem isMarkovKernel_mhKernel [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (hq1 : ∀ x, ∫⁻ y, q x y ∂ν = 1) :
    IsMarkovKernel (mhKernel ν hπ hq) :=
  ⟨fun x => isProbabilityMeasure_mhMeasure (hq1 x)⟩

/-! ### Reversibility and invariance -/

/-- Decomposition of the flux `∫⁻ x in A, π(x) K(x, B) dν(x)` into the accepted part
`∫⁻ x in A, ∫⁻ y in B, min (π x q(x,y)) (π y q(y,x))` and the rejected part
`∫⁻ x in B ∩ A, π(x) r(x)`. -/
private theorem setLIntegral_mul_mhMeasure_eq [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (hfin : ∀ x y, π x * q x y ≠ ∞) {A B : Set Ω}
    (hB : MeasurableSet B) :
    ∫⁻ x in A, π x * mhMeasure ν π q x B ∂ν
      = (∫⁻ x in A, ∫⁻ y in B, min (π x * q x y) (π y * q y x) ∂ν ∂ν)
        + ∫⁻ x in B ∩ A, π x * rejectProb ν π q x ∂ν := by
  have hg : Measurable (Function.uncurry fun x y => q x y * acceptance π q x y) :=
    hq.mul (measurable_acceptance hπ hq)
  have h1 : Measurable fun x => π x * ∫⁻ y in B, q x y * acceptance π q x y ∂ν :=
    hπ.mul hg.lintegral_prod_right
  simp_rw [mhMeasure_apply _ hB, mul_add]
  rw [lintegral_add_left h1]
  congr 1
  · refine lintegral_congr fun x => ?_
    have hgx : Measurable fun y => q x y * acceptance π q x y := hg.comp measurable_prodMk_left
    rw [← lintegral_const_mul (π x) hgx]
    refine lintegral_congr fun y => ?_
    rw [← mul_assoc, mul_acceptance_eq_min (hfin x y)]
  · have h2 : ∀ x, π x * (rejectProb ν π q x * B.indicator 1 x)
        = B.indicator (fun x => π x * rejectProb ν π q x) x := by
      intro x
      by_cases hx : x ∈ B <;> simp [hx]
    simp_rw [h2]
    rw [lintegral_indicator hB, Measure.restrict_restrict hB]

/-- Symmetry of the accepted flux: for s-finite `ν`, measurable `π`, jointly measurable `q`
and arbitrary sets `A`, `B`,
`∫⁻ x in A, ∫⁻ y in B, m(x, y) = ∫⁻ x in B, ∫⁻ y in A, m(x, y)` for the symmetric function
`m(x, y) = min (π x q(x,y)) (π y q(y,x))` (Tonelli). -/
private theorem setLIntegral_min_comm [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (A B : Set Ω) :
    ∫⁻ x in A, ∫⁻ y in B, min (π x * q x y) (π y * q y x) ∂ν ∂ν
      = ∫⁻ x in B, ∫⁻ y in A, min (π x * q x y) (π y * q y x) ∂ν ∂ν := by
  have hq' : Measurable fun p : Ω × Ω => q p.2 p.1 := hq.comp measurable_swap
  have hm : Measurable (Function.uncurry fun x y => min (π x * q x y) (π y * q y x)) :=
    ((hπ.comp measurable_fst).mul hq).min ((hπ.comp measurable_snd).mul hq')
  rw [lintegral_lintegral_swap hm.aemeasurable]
  exact lintegral_congr fun y => lintegral_congr fun x => min_comm _ _

/-- **Reversibility of the MH kernel (MH-1), set form.** Let `ν` be s-finite, `π` measurable,
`q` jointly measurable, and `π x * q x y < ∞` for all `x y`. Then for all measurable `A`, `B`,
`∫⁻ x in A, π(x) K(x, B) dν(x) = ∫⁻ x in B, π(x) K(x, A) dν(x)`, where
`K = mhMeasure ν π q`: the joint law `π(dx) K(x, dy)` gives equal mass to `A × B` and
`B × A`. No normalisation of `q` is required. -/
theorem setLIntegral_mul_mhMeasure_comm [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (hfin : ∀ x y, π x * q x y ≠ ∞) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, π x * mhMeasure ν π q x B ∂ν = ∫⁻ x in B, π x * mhMeasure ν π q x A ∂ν := by
  rw [setLIntegral_mul_mhMeasure_eq hπ hq hfin hB, setLIntegral_mul_mhMeasure_eq hπ hq hfin hA,
    setLIntegral_min_comm hπ hq A B, inter_comm]

/-- **Reversibility of the MH kernel (MH-1), Mathlib form.** Under the hypotheses of
`setLIntegral_mul_mhMeasure_comm` (s-finite `ν`, measurable `π`, jointly measurable `q`,
`π x * q x y < ∞`), `mhKernel ν hπ hq` is reversible with respect to the target law
`ν.withDensity π` in the sense of `ProbabilityTheory.Kernel.IsReversible`:
`∫⁻ x in A, K(x, B) d(πν) = ∫⁻ x in B, K(x, A) d(πν)` for measurable `A`, `B`. -/
theorem isReversible_mhKernel [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (hfin : ∀ x y, π x * q x y ≠ ∞) :
    (mhKernel ν hπ hq).IsReversible (ν.withDensity π) := by
  intro A B hA hB
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hπ (Kernel.measurable_coe _ hB) hA,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hπ (Kernel.measurable_coe _ hA) hB]
  exact setLIntegral_mul_mhMeasure_comm hπ hq hfin hA hB

/-- **Invariance of the target under the MH kernel (MH-1), integral form.** Let `ν` be
s-finite, `π` measurable, `q` jointly measurable with `∫⁻ y, q(x, y) dν(y) = 1` for all `x`,
and `π x * q x y < ∞` for all `x y`. Then for every measurable `A`,
`∫⁻ x, π(x) K(x, A) dν(x) = ∫⁻ x in A, π(x) dν(x)`, where `K = mhMeasure ν π q`. -/
theorem lintegral_mul_mhMeasure [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (hq1 : ∀ x, ∫⁻ y, q x y ∂ν = 1)
    (hfin : ∀ x y, π x * q x y ≠ ∞) {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ x, π x * mhMeasure ν π q x A ∂ν = ∫⁻ x in A, π x ∂ν := by
  have h := setLIntegral_mul_mhMeasure_comm (ν := ν) hπ hq hfin MeasurableSet.univ hA
  rw [Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have := isProbabilityMeasure_mhMeasure (π := π) (hq1 x)
  rw [measure_univ, mul_one]

/-- **Invariance of the target under the MH kernel (MH-1), Mathlib form.** Under the
hypotheses of `lintegral_mul_mhMeasure` (s-finite `ν`, measurable `π`, jointly measurable and
normalised `q`, `π x * q x y < ∞`), the (possibly unnormalised) target law `ν.withDensity π` is
invariant for `mhKernel ν hπ hq` (`ProbabilityTheory.Kernel.Invariant`). -/
theorem invariant_mhKernel [SFinite ν] (hπ : Measurable π) (hq : Measurable (Function.uncurry q))
    (hq1 : ∀ x, ∫⁻ y, q x y ∂ν = 1) (hfin : ∀ x y, π x * q x y ≠ ∞) :
    (mhKernel ν hπ hq).Invariant (ν.withDensity π) := by
  have := isMarkovKernel_mhKernel hπ hq hq1
  exact (isReversible_mhKernel hπ hq hfin).invariant

/-- **Invariance of the target under the MH kernel (MH-1), measure form.** Under the
hypotheses of `lintegral_mul_mhMeasure` (s-finite `ν`, measurable `π`, jointly measurable and
normalised `q`, `π x * q x y < ∞`), the (possibly unnormalised) target law `ν.withDensity π` is
invariant: `(ν.withDensity π).bind (mhKernel ν hπ hq) = ν.withDensity π`. -/
theorem bind_mhKernel [SFinite ν] (hπ : Measurable π) (hq : Measurable (Function.uncurry q))
    (hq1 : ∀ x, ∫⁻ y, q x y ∂ν = 1) (hfin : ∀ x y, π x * q x y ≠ ∞) :
    (ν.withDensity π).bind (mhKernel ν hπ hq) = ν.withDensity π :=
  invariant_mhKernel hπ hq hq1 hfin

/-- **Reversibility as a symmetry of the two-step joint law (MH-1).** If, in addition to the
hypotheses of `invariant_mhKernel`, the target has finite mass `∫⁻ x, π x ∂ν < ∞`, then the
joint law of `(X₀, X₁)` with `X₀ ∼ π ν` and `X₁ ∼ K(X₀, ·)` is exchangeable:
`((ν.withDensity π) ⊗ₘ K).map Prod.swap = (ν.withDensity π) ⊗ₘ K`. -/
theorem map_swap_compProd_mhKernel [SFinite ν] (hπ : Measurable π)
    (hq : Measurable (Function.uncurry q)) (hq1 : ∀ x, ∫⁻ y, q x y ∂ν = 1)
    (hfin : ∀ x y, π x * q x y ≠ ∞) (hπint : ∫⁻ x, π x ∂ν ≠ ∞) :
    ((ν.withDensity π) ⊗ₘ mhKernel ν hπ hq).map Prod.swap
      = (ν.withDensity π) ⊗ₘ mhKernel ν hπ hq := by
  have := isFiniteMeasure_withDensity hπint
  have := isMarkovKernel_mhKernel hπ hq hq1
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod,
    Measure.compProd_apply_prod hB hA, Measure.compProd_apply_prod hA hB]
  exact isReversible_mhKernel hπ hq hfin hB hA

end FormalizeSampling.MH
