module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.TotalVariation

/-!
# Pinsker's inequality for the Kullback–Leibler divergence

Setting: probability measures `μ ν` on an arbitrary measurable space `α` (no topology, no
reference measure). `klDiv μ ν` is Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`;
it is `KL(μ‖ν) = ∫ log (dμ/dν) dμ` when `μ ≪ ν` and the log-likelihood ratio is
`μ`-integrable, and `∞` otherwise. Direction: the **first** argument is the law integrated
against (`klDiv μ ν = KL(μ‖ν)`). Total variation is normalised as
`sup_A |μ(A) - ν(A)|` over measurable sets `A` (the repository's `tvSup`); the set-wise bound
is proved first and `tvSup_le_sqrt_klDiv` takes the supremum.

## Main results

* `binary_pinsker`: for `0 ≤ p ≤ 1` and `0 < q < 1`,
  `2 (p - q)² ≤ p log (p/q) + (1 - p) log ((1 - p)/(1 - q))` (Lean's `log 0 = 0` gives the
  convention `0 log 0 = 0`); `binary_pinsker_klFun` is the same bound written with `klFun`.
* `ofReal_le_klDiv_bool`: Pinsker on the two-point space `Bool`, in `ℝ≥0∞`.
* `ofReal_le_klDiv` (KL-1, `ℝ≥0∞` form, no finiteness hypothesis): for measurable `A`,
  `ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν`.
* `two_mul_sq_le_toReal_klDiv`: if `klDiv μ ν ≠ ∞`, `2 (μ(A) - ν(A))² ≤ (klDiv μ ν).toReal`.
* `abs_sub_le_sqrt_klDiv` (set-wise Pinsker): if `klDiv μ ν ≠ ∞`, then for every measurable
  `A`, `|μ(A) - ν(A)| ≤ √(KL(μ‖ν) / 2)`. Taking the supremum over `A` gives
  `tvSup_le_sqrt_klDiv`: `tvSup μ ν ≤ √(KL(μ‖ν) / 2)`.
* `tvSup_le_sqrt_of_klDiv_le_add_sum`: from a KL budget `KL(ν‖μ) ≤ K₀ + ∑_{k<n} ∫⁻ e k dρ_k`
  with integrable `e k ≥ 0`, `tvSup ν μ ≤ √(K₀ / 2 + ∑_{k<n} (∫ e k dρ_k) / 2)` (the last step
  of the chain-rule bounds GI-1 and GI-2).
* Real-valued budgets: `tvSup_le_sqrt_of_klDiv_le_ofReal` (`KL(μ‖ν) ≤ B` gives
  `tvSup μ ν ≤ √(B / 2)`), `tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal`
  (`KL(ν‖μ) ≤ K₀ + ∑_{k<n} c k` gives `tvSup ν μ ≤ √((K₀ + ∑_{k<n} c k) / 2)`) and
  `tvSup_le_sqrt_of_klDiv_le_add_tsum` (the same with `∑' k, c k` for summable `c ≥ 0`).

The proof maps both laws by `x ↦ decide (x ∈ A)` to `Bool`, uses Mathlib's data processing
inequality `InformationTheory.klDiv_map_le`, evaluates the two-point divergence through
`klDiv_eq_lintegral_klFun_of_ac`, and proves the scalar inequality by monotonicity in `q`:
`d/dq [KL(p‖q) - 2(p - q)²] = (q - p)(1 - 2q)² / (q (1 - q))`.

## Not proved here

* The real-valued forms need `klDiv μ ν ≠ ∞`, since `(∞ : ℝ≥0∞).toReal = 0`.
* The scalar bound is not stated for `q ∈ {0, 1}`: with Lean's conventions the right-hand side
  is then not the binary divergence (which is `∞` unless `p = q`); the measure-level results
  handle this case through absolute continuity.
* No refinements (Bretagnolle–Huber, Vajda, reverse Pinsker) and no finite (non-probability)
  measures.
-/

@[expose] public section

open Real MeasureTheory InformationTheory
open scoped ENNReal

namespace FormalizeSampling.Pinsker

/-- Auxiliary function `-p log x - (1 - p) log (1 - x) - 2 (p - x)²`; up to a constant in `x`
it is the binary divergence `KL(p‖x)` minus `2 (p - x)²`. -/
noncomputable def auxG (p x : ℝ) : ℝ := -(p * log x) - (1 - p) * log (1 - x) - 2 * (p - x) ^ 2

/-- Derivative of `auxG p` on `(0, 1)`: `(x - p)(1 - 2x)² / (x (1 - x))`. -/
lemma hasDerivAt_auxG (p : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (auxG p) ((x - p) * (1 - 2 * x) ^ 2 / (x * (1 - x))) x := by
  have h1 : HasDerivAt (fun y => log y) x⁻¹ x := hasDerivAt_log hx0.ne'
  have h2 : HasDerivAt (fun y => log (1 - y)) ((-1) / (1 - x)) x := by
    have := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
    simpa using this
  have h3 : HasDerivAt (fun y => (p - y) ^ 2) (2 * (p - x) * (-1)) x := by
    convert ((hasDerivAt_id x).const_sub p).pow 2 using 1
    · funext y; simp
    · simp
  have := ((h1.const_mul p).neg.sub (h2.const_mul (1 - p))).sub (h3.const_mul 2)
  convert this using 1
  · funext y; simp [auxG]
  · have : 1 - x ≠ 0 := by linarith
    field_simp
    ring

/-- `auxG p` is minimised at `x = p` over `(0, 1)`, for `p ∈ [0, 1]`. -/
lemma auxG_le (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    auxG p p ≤ auxG p q := by
  rcases lt_trichotomy p q with h | rfl | h
  · have hmono : MonotoneOn (auxG p) (Set.Icc p q) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc p q) ?_ ?_ ?_
      · have hc2 : ContinuousOn (fun x => (1 - p) * log (1 - x) + 2 * (p - x) ^ 2)
            (Set.Icc p q) := by
          refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) (by fun_prop)
          refine ContinuousOn.log (by fun_prop) fun x hx => ?_
          have := hx.2; linarith
        rcases hp0.eq_or_lt with hp | hp
        · subst hp
          exact (hc2.neg).congr fun x _ => by simp [auxG]; ring
        · have hc1 : ContinuousOn (fun x => p * log x) (Set.Icc p q) :=
            ContinuousOn.mul continuousOn_const
              (continuousOn_log.mono fun x hx => by simp; have := hx.1; linarith)
          exact (hc1.neg.sub hc2).congr fun x _ => by simp [auxG]; ring
      · intro x hx
        rw [interior_Icc] at hx
        exact (hasDerivAt_auxG p (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt
          |>.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_auxG p (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have : 0 < x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
        exact div_nonneg (mul_nonneg (by linarith [hx.1]) (sq_nonneg _)) this.le
    exact hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
  · exact le_rfl
  · have hanti : AntitoneOn (auxG p) (Set.Icc q p) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc q p) ?_ ?_ ?_
      · have hc1 : ContinuousOn (fun x => -(p * log x) - 2 * (p - x) ^ 2) (Set.Icc q p) :=
          (ContinuousOn.mul continuousOn_const
              (continuousOn_log.mono fun x hx => by simp; have := hx.1; linarith)).neg.sub
            (by fun_prop)
        rcases hp1.eq_or_lt with hp | hp
        · subst hp
          exact hc1.congr fun x _ => by simp [auxG]
        · have hc2 : ContinuousOn (fun x => (1 - p) * log (1 - x)) (Set.Icc q p) := by
            refine ContinuousOn.mul continuousOn_const (ContinuousOn.log (by fun_prop) ?_)
            intro x hx; have := hx.2; linarith
          exact (hc1.sub hc2).congr fun x _ => by simp [auxG]; ring
      · intro x hx
        rw [interior_Icc] at hx
        exact (hasDerivAt_auxG p (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt
          |>.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_auxG p (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have : 0 < x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (sq_nonneg _)) this.le
    exact hanti ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le

/-- **Binary Pinsker inequality.** For `p ∈ [0, 1]` and `q ∈ (0, 1)`,
`2 (p - q)² ≤ KL(Ber p ‖ Ber q) = p log (p/q) + (1 - p) log ((1 - p)/(1 - q))`, with the
convention `0 log 0 = 0` (Lean's `Real.log 0 = 0`). -/
theorem binary_pinsker {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  have h := auxG_le p q hp0 hp1 hq0 hq1
  have e1 : p * log (p / q) = p * log p - p * log q := by
    rcases hp0.eq_or_lt with hp | hp
    · subst hp; simp
    · rw [log_div hp.ne' hq0.ne']; ring
  have e2 : (1 - p) * log ((1 - p) / (1 - q)) = (1 - p) * log (1 - p) - (1 - p) * log (1 - q) := by
    rcases hp1.eq_or_lt with hp | hp
    · subst hp; simp
    · rw [log_div (by linarith) (by linarith)]; ring
  simp only [auxG, sub_self] at h
  rw [e1, e2]
  nlinarith [h]

/-- **Binary Pinsker inequality**, `klFun` form: for `p ∈ [0, 1]` and `q ∈ (0, 1)`,
`2 (p - q)² ≤ q klFun (p/q) + (1 - q) klFun ((1 - p)/(1 - q))`, where
`klFun x = x log x + 1 - x`; the right-hand side is `KL(Ber p ‖ Ber q)`. -/
theorem binary_pinsker_klFun {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤
      q * klFun (p / q) + (1 - q) * klFun ((1 - p) / (1 - q)) := by
  have h := binary_pinsker hp0 hp1 hq0 hq1
  have hq' : 1 - q ≠ 0 := by linarith
  have : q * klFun (p / q) + (1 - q) * klFun ((1 - p) / (1 - q))
      = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
    simp only [klFun]
    field_simp
    ring
  linarith


/-- On `Bool`, the Radon–Nikodym derivative satisfies `(dP/dQ)(b) Q{b} = P{b}` when `P ≪ Q`. -/
lemma rnDeriv_mul_singleton {P Q : Measure Bool} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : P ≪ Q) (b : Bool) : P.rnDeriv Q b * Q {b} = P {b} := by
  rw [← lintegral_singleton, Measure.setLIntegral_rnDeriv h]

/-- **Pinsker on the two-point space.** For probability measures `P Q` on `Bool`,
`ENNReal.ofReal (2 (P{true} - Q{true})²) ≤ KL(P‖Q)`, with no finiteness hypothesis. -/
theorem ofReal_le_klDiv_bool (P Q : Measure Bool) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    ENNReal.ofReal (2 * (P.real {true} - Q.real {true}) ^ 2) ≤ klDiv P Q := by
  by_cases hac : P ≪ Q
  swap; · simp [hac]
  set p := P.real {true}
  set q := Q.real {true}
  have hPf : P.real {false} = 1 - p := by
    rw [← probReal_compl_eq_one_sub (measurableSet_singleton true)]
    congr 1; ext b; cases b <;> simp
  have hQf : Q.real {false} = 1 - q := by
    rw [← probReal_compl_eq_one_sub (measurableSet_singleton true)]
    congr 1; ext b; cases b <;> simp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  rcases hq0.eq_or_lt with hq | hq
  · -- `Q {true} = 0`, so `P {true} = 0`
    have : Q {true} = 0 := by
      rw [← measureReal_eq_zero_iff]; exact hq.symm
    have hp : p = 0 := by simp [p, measureReal_def, hac this]
    rw [hp, ← hq]; simp
  rcases hq1.eq_or_lt with hq' | hq'
  · have : Q {false} = 0 := by
      rw [← measureReal_eq_zero_iff, hQf, hq']; simp
    have hp : p = 1 := by
      have := hac this
      have h2 : P.real {false} = 0 := by simp [measureReal_def, this]
      linarith
    rw [hp, hq']; simp
  have key := binary_pinsker_klFun hp0 hp1 hq hq'
  have hr : ∀ b, (P.rnDeriv Q b).toReal = P.real {b} / Q.real {b} := by
    intro b
    have hQb : Q.real {b} ≠ 0 := by
      cases b
      · rw [hQf]; linarith
      · exact hq.ne'
    rw [eq_div_iff hQb, measureReal_def, measureReal_def, ← ENNReal.toReal_mul,
      rnDeriv_mul_singleton hac]
  rw [klDiv_eq_lintegral_klFun_of_ac hac, lintegral_fintype, Fintype.sum_bool]
  simp only [hr]
  have e1 : Q {true} = ENNReal.ofReal q := (ofReal_measureReal (measure_ne_top Q _)).symm
  have e2 : Q {false} = ENNReal.ofReal (1 - q) := by rw [← hQf, ofReal_measureReal]
  rw [hPf, hQf, e1, e2]
  refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (mul_nonneg hq0 (klFun_nonneg (by positivity)))
      (mul_nonneg (by linarith) (klFun_nonneg (div_nonneg (by linarith) (by linarith)))),
    ENNReal.ofReal_mul hq0, ENNReal.ofReal_mul (by linarith)]
  simp only [p, q]
  ring

variable {α : Type*} [MeasurableSpace α]

/-- **Pinsker's inequality, set-wise, `ℝ≥0∞` form.** For probability measures `μ ν` on any
measurable space and a measurable set `A`,
`ENNReal.ofReal (2 (μ(A) - ν(A))²) ≤ KL(μ‖ν)` (`klDiv μ ν`), with no finiteness hypothesis. -/
theorem ofReal_le_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν := by
  classical
  set f : α → Bool := fun x => decide (x ∈ A)
  have hf : Measurable f := measurable_to_countable' fun b => by
    cases b
    · convert hA.compl using 1; ext x; simp [f]
    · convert hA using 1; ext x; simp [f]
  have hpre : f ⁻¹' {true} = A := by ext x; simp [f]
  have h := ofReal_le_klDiv_bool (μ.map f) (ν.map f)
  rw [map_measureReal_apply hf (measurableSet_singleton _),
    map_measureReal_apply hf (measurableSet_singleton _), hpre] at h
  exact h.trans (klDiv_map_le μ ν hf)

/-- **Pinsker's inequality, set-wise, real form.** For probability measures `μ ν` with
`KL(μ‖ν) = klDiv μ ν ≠ ∞` and a measurable set `A`, `2 (μ(A) - ν(A))² ≤ KL(μ‖ν)`. -/
theorem two_mul_sq_le_toReal_klDiv {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hKL : klDiv μ ν ≠ ∞) {A : Set α} (hA : MeasurableSet A) :
    2 * (μ.real A - ν.real A) ^ 2 ≤ (klDiv μ ν).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hKL).1 (ofReal_le_klDiv μ ν hA)

/-- **Pinsker's inequality, set-wise.** For probability measures `μ ν` with
`KL(μ‖ν) = klDiv μ ν ≠ ∞`, every measurable set `A` satisfies
`|μ(A) - ν(A)| ≤ √(KL(μ‖ν) / 2)`; the supremum over `A` is `tvSup μ ν`. -/
theorem abs_sub_le_sqrt_klDiv {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hKL : klDiv μ ν ≠ ∞) :
    ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  intro A hA
  rw [Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
  have := two_mul_sq_le_toReal_klDiv hKL hA
  linarith

/-- **Pinsker's inequality (KL-1).** For probability measures `μ ν` with
`KL(μ‖ν) = klDiv μ ν ≠ ∞`, `tvSup μ ν ≤ √(KL(μ‖ν) / 2)`, with TV normalised as
`sup_A |μ(A) - ν(A)|`. (If `klDiv μ ν = ∞` the bound is vacuous; `toReal ∞ = 0` is why the
hypothesis is needed.) -/
theorem tvSup_le_sqrt_klDiv {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hKL : klDiv μ ν ≠ ∞) :
    TotalVariation.tvSup μ ν ≤ √((klDiv μ ν).toReal / 2) :=
  TotalVariation.tvSup_le_of_forall (abs_sub_le_sqrt_klDiv hKL)

/-- **Pinsker after a KL budget.** For probability measures `μ ν`, a finite `K₀`, and
nonnegative functions `e k` integrable against measures `ρ k`, if
`KL(ν‖μ) ≤ K₀ + ∑_{k<n} ∫⁻ e k dρ_k` then
`tvSup ν μ ≤ √(K₀ / 2 + ∑_{k<n} (∫ e k dρ_k) / 2)`. This is the final step of the KL chain-rule
bounds for Markov chains (the per-step errors are summed inside one square root). -/
theorem tvSup_le_sqrt_of_klDiv_le_add_sum {β : Type*} [MeasurableSpace β] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {K₀ : ℝ≥0∞} (hK₀ : K₀ ≠ ∞) {n : ℕ}
    {ρ : ℕ → Measure β} {e : ℕ → β → ℝ} (he0 : ∀ k x, 0 ≤ e k x)
    (hei : ∀ k, Integrable (e k) (ρ k))
    (hKL : klDiv ν μ ≤ K₀ + ∑ k ∈ Finset.range n, ∫⁻ x, ENNReal.ofReal (e k x) ∂(ρ k)) :
    TotalVariation.tvSup ν μ ≤
      √(K₀.toReal / 2 + ∑ k ∈ Finset.range n, (∫ x, e k x ∂(ρ k)) / 2) := by
  have hl : ∀ k, ∫⁻ x, ENNReal.ofReal (e k x) ∂(ρ k) = ENNReal.ofReal (∫ x, e k x ∂(ρ k)) :=
    fun k => (ofReal_integral_eq_lintegral_ofReal (hei k) (ae_of_all _ (he0 k))).symm
  simp only [hl] at hKL
  have hsum : ∑ k ∈ Finset.range n, ENNReal.ofReal (∫ x, e k x ∂(ρ k)) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  have hB := ENNReal.add_ne_top.2 ⟨hK₀, hsum⟩
  refine (tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top hB hKL)).trans (Real.sqrt_le_sqrt ?_)
  have h1 := ENNReal.toReal_mono hB hKL
  rw [ENNReal.toReal_add hK₀ hsum, ENNReal.toReal_sum fun _ _ => ENNReal.ofReal_ne_top] at h1
  simp only [ENNReal.toReal_ofReal (integral_nonneg (he0 _))] at h1
  rw [← Finset.sum_div, ← add_div]
  linarith

/-- **Pinsker with a real KL budget.** For probability measures `μ ν` and a real number `B`, if
`KL(μ‖ν) ≤ ofReal B` then `tvSup μ ν ≤ √(B / 2)`. No finiteness hypothesis is needed (the
budget is finite) and no sign condition on `B` (for `B ≤ 0` the hypothesis forces
`KL(μ‖ν) = 0`). `DiffusionDiscretization.tvSup_le_sqrt_of_klDiv_le` is the same statement on
`Fin d → ℝ`. -/
theorem tvSup_le_sqrt_of_klDiv_le_ofReal {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {B : ℝ} (h : klDiv μ ν ≤ ENNReal.ofReal B) :
    TotalVariation.tvSup μ ν ≤ √(B / 2) := by
  refine (tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)).trans ?_
  rcases le_total 0 B with hB | hB
  · gcongr
    exact ENNReal.toReal_le_of_le_ofReal hB h
  · rw [ENNReal.ofReal_of_nonpos hB, nonpos_iff_eq_zero] at h
    simp only [h, ENNReal.toReal_zero, zero_div, Real.sqrt_zero]
    positivity

/-- **Pinsker after a real per-step KL budget.** For probability measures `μ ν`, a finite
`K₀ : ℝ≥0∞` and reals `c k ≥ 0`, if `KL(ν‖μ) ≤ K₀ + ∑_{k<n} c k` (in `ℝ≥0∞`, through
`ENNReal.ofReal`), then `tvSup ν μ ≤ √((K₀ + ∑_{k<n} c k) / 2)`. Typical use: `K₀` is the initial
divergence of two Markov chains and `c k` bounds the averaged one-step KL error of step `k`
(`KL.klDiv_chain_le_sum`). -/
theorem tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {K₀ : ℝ≥0∞} (hK₀ : K₀ ≠ ∞) {n : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k)
    (hKL : klDiv ν μ ≤ K₀ + ∑ k ∈ Finset.range n, ENNReal.ofReal (c k)) :
    TotalVariation.tvSup ν μ ≤ √((K₀.toReal + ∑ k ∈ Finset.range n, c k) / 2) := by
  refine tvSup_le_sqrt_of_klDiv_le_ofReal (hKL.trans_eq ?_)
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (Finset.sum_nonneg fun k _ => hc k),
    ENNReal.ofReal_toReal hK₀, ENNReal.ofReal_sum_of_nonneg fun k _ => hc k]

/-- **Pinsker after a summable per-step KL budget.** Under the hypotheses of
`tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal`, if moreover `c` is summable, then
`tvSup ν μ ≤ √((K₀ + ∑' k, c k) / 2)`, a bound that does not depend on the number `n` of
steps. -/
theorem tvSup_le_sqrt_of_klDiv_le_add_tsum {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {K₀ : ℝ≥0∞} (hK₀ : K₀ ≠ ∞) {n : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hsum : Summable c)
    (hKL : klDiv ν μ ≤ K₀ + ∑ k ∈ Finset.range n, ENNReal.ofReal (c k)) :
    TotalVariation.tvSup ν μ ≤ √((K₀.toReal + ∑' k, c k) / 2) :=
  (tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal hK₀ hc hKL).trans <| Real.sqrt_le_sqrt <| by
    gcongr
    exact hsum.sum_le_tsum _ fun k _ => hc k

/-- **Pinsker's inequality in Mathlib's normalisation.** For probability measures with
`klDiv μ ν ≠ ∞`, Mathlib's `L¹` total variation satisfies
`MeasureTheory.tvDist μ ν ≤ √(2 KL(μ‖ν))`. -/
theorem measureTheory_tvDist_le_sqrt_two_mul_klDiv {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hKL : klDiv μ ν ≠ ∞) :
    MeasureTheory.tvDist μ ν ≤ √(2 * (klDiv μ ν).toReal) := by
  rw [TotalVariation.measureTheory_tvDist_eq_two_mul]
  have h := tvSup_le_sqrt_klDiv hKL
  have h4 : √(2 * (klDiv μ ν).toReal) = 2 * √((klDiv μ ν).toReal / 2) := by
    rw [show 2 * (klDiv μ ν).toReal = 2 ^ 2 * ((klDiv μ ν).toReal / 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h4]
  linarith

end FormalizeSampling.Pinsker
