module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Order.CompletePartialOrder

/-!
# From warm starts to every start with finite KL

Status: **Verified** (general measurable spaces; no named hypotheses).

Let `P` be a Markov kernel from `α` to `β`, `π` a probability law on `α` and `π' = P ∘ₘ π`.
Suppose a contraction `KL(P ∘ₘ ρ'‖π') ≤ c · KL(ρ'‖π)` is known for every **warm** probability law
`ρ' ≤ C • π` (with `KL(ρ'‖π) < ∞`). Then the same inequality holds for every probability law `ρ`
with `KL(ρ‖π) < ∞`, with the same constant `c`, and `KL(P ∘ₘ ρ‖π') < ∞`.

Route. With `r = dρ/dπ` and `A_n = {r ≤ n}` (`m_n = ρ(A_n) → 1`), write
`ρ = m_n ρ[|A_n] + (1 - m_n) ρ[|A_nᶜ]`; the first conditional law is `n/m_n`-warm. Convexity of
`KL(·‖π')` (`klDiv_smul_add_smul_le`, from the convexity of `klFun`) and data processing
(Mathlib's `klDiv_comp_right_le`) give
`KL(Pρ‖π') ≤ c (I_n - m_n log m_n) + (KL(ρ‖π) - I_n) - (1 - m_n) log (1 - m_n)`,
`I_n = ∫_{A_n} log r dρ` (`mul_toReal_klDiv_cond`), and the right side tends to `c KL(ρ‖π)`.

## Main results

* `klDiv_smul_add_smul_le`: convexity of `KL(·‖π)` in the first argument (finite measures).
* `mul_toReal_klDiv_cond`: `ρ(s) · KL(ρ[|s]‖π) = ∫_s log (dρ/dπ) dρ - ρ(s) log ρ(s)`.
* `restrict_le_smul_of_rnDeriv_le`: `ρ|_{r ≤ t} ≤ t • π`.
* `klDiv_comp_le_of_warm`: warm contraction ⇒ contraction for every finite-KL start.
* `klDiv_iterate_le_of_forall`: iterating a one-step contraction (`c ≥ 0`).

## Not proved here

* Lower semicontinuity or continuity of KL along the truncation (not needed: only set integrals
  of the fixed integrable function `log (dρ/dπ)` are passed to the limit).
* Starts with `KL(ρ‖π) = ∞` (e.g. Dirac masses); the statement is vacuous there.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.KLWarmApprox

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Convexity of KL in the first argument.** For finite measures `μ₁, μ₂ ≪ π` (`π` finite)
and weights `a, b ≥ 0` with `a + b = 1`:
`KL(a μ₁ + b μ₂‖π) ≤ a KL(μ₁‖π) + b KL(μ₂‖π)` (in `ℝ≥0∞`). -/
theorem klDiv_smul_add_smul_le {π μ₁ μ₂ : Measure α} [IsFiniteMeasure π] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (h₁ : μ₁ ≪ π) (h₂ : μ₂ ≪ π) {a b : ℝ≥0} (hab : a + b = 1) :
    klDiv (a • μ₁ + b • μ₂) π ≤ (a : ℝ≥0∞) * klDiv μ₁ π + (b : ℝ≥0∞) * klDiv μ₂ π := by
  have hac : a • μ₁ + b • μ₂ ≪ π :=
    Measure.AbsolutelyContinuous.add_left (h₁.smul_left a) (h₂.smul_left b)
  rw [klDiv_eq_lintegral_klFun_of_ac hac, klDiv_eq_lintegral_klFun_of_ac h₁,
    klDiv_eq_lintegral_klFun_of_ac h₂, ← lintegral_const_mul _ (by fun_prop),
    ← lintegral_const_mul _ (by fun_prop), ← lintegral_add_left (by fun_prop)]
  refine lintegral_mono_ae ?_
  filter_upwards [Measure.rnDeriv_add (a • μ₁) (b • μ₂) π,
    Measure.rnDeriv_smul_left μ₁ π a, Measure.rnDeriv_smul_left μ₂ π b,
    Measure.rnDeriv_lt_top μ₁ π, Measure.rnDeriv_lt_top μ₂ π] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, ENNReal.smul_def,
    ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top h4.ne)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top h5.ne),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hc := convexOn_klFun.2 (mem_Ici.2 (ENNReal.toReal_nonneg (a := μ₁.rnDeriv π x)))
    (mem_Ici.2 (ENNReal.toReal_nonneg (a := μ₂.rnDeriv π x))) a.coe_nonneg b.coe_nonneg hab'
  simp only [smul_eq_mul] at hc
  have k1 := klFun_nonneg (ENNReal.toReal_nonneg (a := μ₁.rnDeriv π x))
  have k2 := klFun_nonneg (ENNReal.toReal_nonneg (a := μ₂.rnDeriv π x))
  calc ENNReal.ofReal (klFun (a * (μ₁.rnDeriv π x).toReal + b * (μ₂.rnDeriv π x).toReal))
      ≤ ENNReal.ofReal (a * klFun (μ₁.rnDeriv π x).toReal
          + b * klFun (μ₂.rnDeriv π x).toReal) := ENNReal.ofReal_le_ofReal hc
    _ = (a : ℝ≥0∞) * ENNReal.ofReal (klFun (μ₁.rnDeriv π x).toReal)
        + (b : ℝ≥0∞) * ENNReal.ofReal (klFun (μ₂.rnDeriv π x).toReal) := by
      rw [ENNReal.ofReal_add (mul_nonneg a.coe_nonneg k1) (mul_nonneg b.coe_nonneg k2),
        ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

/-- **Data processing against a stationary target.** If `P ∘ₘ π = π'` (`P` Markov), then
`KL(P ∘ₘ μ‖π') ≤ KL(μ‖π)` for finite `μ, π`. -/
theorem klDiv_comp_le_of_comp_eq {π : Measure α} [IsFiniteMeasure π] {π' : Measure β}
    (P : Kernel α β) [IsMarkovKernel P] (hπ : P ∘ₘ π = π') (μ : Measure α) [IsFiniteMeasure μ] :
    klDiv (P ∘ₘ μ) π' ≤ klDiv μ π := by
  have := klDiv_comp_right_le μ π P
  rwa [hπ] at this

/-- `ρ(s) • ρ[|s] = ρ|_s` for a finite measure with `ρ(s) ≠ 0` (weight in `ℝ≥0`). -/
theorem toNNReal_smul_cond {ρ : Measure α} [IsFiniteMeasure ρ] {s : Set α} (hs : ρ s ≠ 0) :
    (ρ s).toNNReal • ρ[|s] = ρ.restrict s := by
  ext u hu
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal (measure_ne_top _ _),
    ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hs (measure_ne_top _ _), one_mul]

/-- **KL of a conditional law.** For probability laws `ρ ≪ π` with `log (dρ/dπ)` `ρ`-integrable
and a measurable `s` with `ρ(s) ≠ 0`: `KL(ρ[|s]‖π) < ∞` and
`ρ(s) · KL(ρ[|s]‖π) = ∫_s log (dρ/dπ) dρ - ρ(s) log ρ(s)` (real parts). -/
theorem mul_toReal_klDiv_cond {ρ π : Measure α} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] (hρπ : ρ ≪ π) (hint : Integrable (llr ρ π) ρ) {s : Set α}
    (hs : MeasurableSet s) (hs0 : ρ s ≠ 0) :
    klDiv ρ[|s] π ≠ ⊤ ∧ ρ.real s * (klDiv ρ[|s] π).toReal
      = ∫ x in s, llr ρ π x ∂ρ - ρ.real s * Real.log (ρ.real s) := by
  have := cond_isProbabilityMeasure (μ := ρ) hs0
  set c : ℝ≥0∞ := (ρ s)⁻¹ with hc
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
  have hctop : c ≠ ∞ := ENNReal.inv_ne_top.2 hs0
  have hm : 0 < ρ.real s := ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  have hcd : ρ[|s] = c • ρ.restrict s := rfl
  have hacr : ρ.restrict s ≪ π :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hρπ
  have hacc : ρ[|s] ≪ π := cond_absolutelyContinuous.trans hρπ
  have hllr_r : llr (ρ.restrict s) π =ᵐ[ρ.restrict s] llr ρ π := by
    filter_upwards [hacr.ae_le (Measure.rnDeriv_restrict ρ π hs), ae_restrict_mem hs]
      with x h1 h2
    simp only [llr_def]
    rw [h1, indicator_of_mem h2]
  have hllr_c : llr ρ[|s] π =ᵐ[ρ.restrict s] fun x => llr ρ π x + Real.log c.toReal := by
    filter_upwards [llr_smul_left hacr c hc0 hctop, hllr_r] with x h1 h2
    rw [hcd, h1, h2]
  have hint_r : Integrable (llr ρ π) (ρ.restrict s) := hint.restrict
  have hint_c' : Integrable (llr ρ[|s] π) (ρ.restrict s) :=
    (hint_r.add (integrable_const _)).congr hllr_c.symm
  have hint_c : Integrable (llr ρ[|s] π) ρ[|s] := by
    rw [hcd]; exact hint_c'.smul_measure hctop
  refine ⟨klDiv_ne_top hacc hint_c, ?_⟩
  have hsm : ∫ x, llr ρ[|s] π x ∂ρ[|s] = c.toReal • ∫ x, llr ρ[|s] π x ∂(ρ.restrict s) :=
    integral_smul_measure _ _
  rw [toReal_klDiv_of_measure_eq hacc (by simp), hsm, integral_congr_ae hllr_c,
    integral_add hint_r (integrable_const _), integral_const,
    smul_eq_mul, smul_eq_mul, measureReal_restrict_apply_univ, hc, ENNReal.toReal_inv,
    ← measureReal_def, Real.log_inv]
  field_simp
  ring

/-- **Truncations are warm.** If `ρ ≪ π` and `t ≥ 0`, then the restriction of `ρ` to
`{x | (dρ/dπ)(x) ≤ t}` (real part) satisfies `ρ|_{r ≤ t} ≤ t • π`. -/
theorem restrict_le_smul_of_rnDeriv_le {ρ π : Measure α} [IsFiniteMeasure ρ] [SigmaFinite π]
    (hρπ : ρ ≪ π) (t : ℝ) :
    ρ.restrict {x | (ρ.rnDeriv π x).toReal ≤ t} ≤ ENNReal.ofReal t • π := by
  have hA : MeasurableSet {x | (ρ.rnDeriv π x).toReal ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  refine Measure.le_intro fun u hu _ => ?_
  rw [Measure.restrict_apply hu, Measure.smul_apply, smul_eq_mul,
    ← Measure.setLIntegral_rnDeriv hρπ]
  calc ∫⁻ x in u ∩ {x | (ρ.rnDeriv π x).toReal ≤ t}, ρ.rnDeriv π x ∂π
      ≤ ∫⁻ _ in u ∩ {x | (ρ.rnDeriv π x).toReal ≤ t}, ENNReal.ofReal t ∂π := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem (hu.inter hA),
          ae_restrict_of_ae (Measure.rnDeriv_lt_top ρ π)] with x hx hlt
        rw [← ENNReal.ofReal_toReal hlt.ne]
        exact ENNReal.ofReal_le_ofReal hx.2
    _ = ENNReal.ofReal t * π (u ∩ {x | (ρ.rnDeriv π x).toReal ≤ t}) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal t * π u := by gcongr; exact inter_subset_left

/-- **Warm contraction implies contraction for every finite-KL start (Verified).** Let `π` be a
probability law on `α`, `P` a Markov kernel from `α` to `β`, `π' = P ∘ₘ π`, and `c : ℝ`. Assume
that for every probability law `ρ'` with `ρ' ≤ C • π` for some `C ≥ 0` and `KL(ρ'‖π) < ∞`,
`KL(P ∘ₘ ρ'‖π').toReal ≤ c · KL(ρ'‖π).toReal`. Then for every probability law `ρ` with
`KL(ρ‖π) < ∞`: `KL(P ∘ₘ ρ‖π') < ∞` and `KL(P ∘ₘ ρ‖π').toReal ≤ c · KL(ρ‖π).toReal`. -/
theorem klDiv_comp_le_of_warm (π : Measure α) [IsProbabilityMeasure π] {π' : Measure β}
    (P : Kernel α β) [IsMarkovKernel P] (hπ : P ∘ₘ π = π') (c : ℝ)
    (hwarm : ∀ (ρ' : Measure α) [IsProbabilityMeasure ρ'] (C : ℝ), 0 ≤ C →
      ρ' ≤ ENNReal.ofReal C • π → klDiv ρ' π ≠ ⊤ →
      (klDiv (P ∘ₘ ρ') π').toReal ≤ c * (klDiv ρ' π).toReal)
    (ρ : Measure α) [IsProbabilityMeasure ρ] (hKL : klDiv ρ π ≠ ⊤) :
    klDiv (P ∘ₘ ρ) π' ≠ ⊤ ∧ (klDiv (P ∘ₘ ρ) π').toReal ≤ c * (klDiv ρ π).toReal := by
  obtain ⟨hρπ, hint⟩ := klDiv_ne_top_iff.1 hKL
  have hDP := klDiv_comp_le_of_comp_eq P hπ
  refine ⟨ne_top_of_le_ne_top hKL (hDP ρ), ?_⟩
  set A : ℕ → Set α := fun n => {x | (ρ.rnDeriv π x).toReal ≤ n} with hAdef
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le (by fun_prop) measurable_const
  have hAmono : Monotone A := fun i j hij x hx => by
    exact show (ρ.rnDeriv π x).toReal ≤ j from le_trans hx (Nat.cast_le.2 hij)
  have hAU : ⋃ n, A n = univ := eq_univ_of_forall fun x =>
    let ⟨n, hn⟩ := exists_nat_ge (ρ.rnDeriv π x).toReal; mem_iUnion.2 ⟨n, hn⟩
  set L := ∫ x, llr ρ π x ∂ρ with hLdef
  have hL : (klDiv ρ π).toReal = L := toReal_klDiv_of_measure_eq hρπ (by simp)
  set I : ℕ → ℝ := fun n => ∫ x in A n, llr ρ π x ∂ρ with hIdef
  set m : ℕ → ℝ := fun n => ρ.real (A n) with hmdef
  have hI : Tendsto I atTop (𝓝 L) := by
    have := tendsto_setIntegral_of_monotone hAm hAmono hint.integrableOn
    rwa [hAU, Measure.restrict_univ] at this
  have hm : Tendsto m atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := ρ) hAmono
    rw [hAU, measure_univ] at h
    exact (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  set g : ℕ → ℝ := fun n =>
    c * (I n - m n * Real.log (m n)) + (L - I n) - (1 - m n) * Real.log (1 - m n) with hgdef
  have hg : Tendsto g atTop (𝓝 (c * L)) := by
    have h1 : Tendsto (fun n => m n * Real.log (m n)) atTop (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto 1).comp hm
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n => (1 - m n) * Real.log (1 - m n)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n => 1 - m n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hm
      have := (Real.continuous_mul_log.tendsto 0).comp h3
      simpa [Function.comp_def] using this
    have := (((hI.sub h1).const_mul c).add ((tendsto_const_nhds (x := L)).sub hI)).sub h2
    simpa using this
  rw [hL]
  refine ge_of_tendsto hg ?_
  filter_upwards [hm.eventually_const_lt (zero_lt_one : (0 : ℝ) < 1)] with n hn
  have hA0 : ρ (A n) ≠ 0 := fun h => by simp [m, measureReal_def, h] at hn
  have := cond_isProbabilityMeasure (μ := ρ) hA0
  obtain ⟨hfinA, hidA⟩ := mul_toReal_klDiv_cond hρπ hint (hAm n) hA0
  -- the conditional law on `A n` is warm
  have hwarmA : ρ[|A n] ≤ ENNReal.ofReal (n / m n) • π := by
    have h := restrict_le_smul_of_rnDeriv_le hρπ (n : ℝ)
    refine Measure.le_intro fun u hu _ => ?_
    have hu' := Measure.le_iff'.1 h u
    rw [ProbabilityTheory.cond, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul]
    rw [Measure.smul_apply, smul_eq_mul] at hu'
    have e : ENNReal.ofReal (n / m n) = (ρ (A n))⁻¹ * ENNReal.ofReal n := by
      rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hn.le),
        ENNReal.ofReal_inv_of_pos hn]
      simp only [m, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [e, mul_assoc]
    gcongr
  have hstepA := hwarm ρ[|A n] (n / m n) (by positivity) hwarmA hfinA
  by_cases hC0 : ρ (A n)ᶜ = 0
  · -- `ρ` is itself warm
    have hA1 : ρ (A n) = 1 := (prob_compl_eq_zero_iff (hAm n)).1 hC0
    have hres : ρ.restrict (A n) = ρ := Measure.restrict_eq_self_of_ae_mem
      (measure_eq_zero_iff_ae_notMem.1 hC0 |>.mono fun x hx => by simpa using hx)
    have hcond : ρ[|A n] = ρ := by
      rw [ProbabilityTheory.cond, hA1, inv_one, one_smul, hres]
    have hm1 : m n = 1 := by simp [m, measureReal_def, hA1]
    have hI1 : I n = L := by simp only [I, hres, L]
    rw [hcond] at hstepA
    have : g n = c * L := by simp [g, hm1, hI1]
    rw [this, ← hL]; exact hstepA
  · have := cond_isProbabilityMeasure (μ := ρ) hC0
    obtain ⟨hfinC, hidC⟩ := mul_toReal_klDiv_cond hρπ hint (hAm n).compl hC0
    set a : ℝ≥0 := (ρ (A n)).toNNReal with ha
    set b : ℝ≥0 := (ρ (A n)ᶜ).toNNReal with hb
    have hab : a + b = 1 := by
      rw [ha, hb, ← ENNReal.toNNReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        measure_add_measure_compl (hAm n), measure_univ, ENNReal.toNNReal_one]
    have ha' : (a : ℝ) = m n := rfl
    have hb' : (b : ℝ) = 1 - m n := by
      simp only [hb, ENNReal.coe_toNNReal_eq_toReal, ← measureReal_def, m]
      rw [measureReal_compl (hAm n), probReal_univ]
    have hdec : ρ = a • ρ[|A n] + b • ρ[|(A n)ᶜ] := by
      rw [ha, hb, toNNReal_smul_cond hA0, toNNReal_smul_cond hC0,
        Measure.restrict_add_restrict_compl (hAm n)]
    have hPdec : P ∘ₘ ρ = a • (P ∘ₘ ρ[|A n]) + b • (P ∘ₘ ρ[|(A n)ᶜ]) := by
      conv_lhs => rw [hdec]
      rw [Measure.comp_add, ENNReal.smul_def a, ENNReal.smul_def b, Measure.comp_smul,
        Measure.comp_smul, ← ENNReal.smul_def, ← ENNReal.smul_def]
    have hfinPA : klDiv (P ∘ₘ ρ[|A n]) π' ≠ ⊤ := ne_top_of_le_ne_top hfinA (hDP _)
    have hfinPC : klDiv (P ∘ₘ ρ[|(A n)ᶜ]) π' ≠ ⊤ := ne_top_of_le_ne_top hfinC (hDP _)
    have : IsProbabilityMeasure π' := by rw [← hπ]; infer_instance
    have hconv := klDiv_smul_add_smul_le (klDiv_ne_top_iff.1 hfinPA).1
      (klDiv_ne_top_iff.1 hfinPC).1 hab
    rw [← hPdec] at hconv
    have hreal := ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hfinPA,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hfinPC⟩) hconv
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinPA)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinPC), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.coe_toReal, ha', hb'] at hreal
    have hDPC := ENNReal.toReal_mono hfinC (hDP ρ[|(A n)ᶜ])
    have hmC : ρ.real (A n)ᶜ = 1 - m n := by rw [measureReal_compl (hAm n), probReal_univ]
    have hIC : ∫ x in (A n)ᶜ, llr ρ π x ∂ρ = L - I n := by
      rw [hLdef, ← integral_add_compl (hAm n) hint]; ring
    rw [hmC, hIC] at hidC
    have hm1 : m n ≤ 1 := by
      simp only [m]; exact measureReal_le_one
    have h1 : m n * (klDiv (P ∘ₘ ρ[|A n]) π').toReal
        ≤ c * (m n * (klDiv ρ[|A n] π).toReal) := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hstepA hn.le
    have h2 : (1 - m n) * (klDiv (P ∘ₘ ρ[|(A n)ᶜ]) π').toReal
        ≤ (1 - m n) * (klDiv ρ[|(A n)ᶜ] π).toReal :=
      mul_le_mul_of_nonneg_left hDPC (by linarith)
    rw [hidA] at h1
    simp only [g]
    linarith

/-- **Iterating a one-step contraction.** Let `π` be a probability law, `P` a Markov kernel
with `c ≥ 0` such that every probability law `ρ` with `KL(ρ‖π) < ∞` satisfies
`KL(P ∘ₘ ρ‖π) < ∞` and `KL(P ∘ₘ ρ‖π).toReal ≤ c · KL(ρ‖π).toReal`. For the chain
`ρ (k+1) = P ∘ₘ ρ k` from a probability law `ρ 0` with `KL(ρ 0‖π) < ∞`: every `ρ k` is a
probability law, `KL(ρ k‖π) < ∞` and `KL(ρ k‖π).toReal ≤ c^k · KL(ρ 0‖π).toReal`. -/
theorem klDiv_iterate_le_of_forall (π : Measure α) (P : Kernel α α) [IsMarkovKernel P]
    {c : ℝ} (hc : 0 ≤ c)
    (hone : ∀ (ρ : Measure α) [IsProbabilityMeasure ρ], klDiv ρ π ≠ ⊤ →
      klDiv (P ∘ₘ ρ) π ≠ ⊤ ∧ (klDiv (P ∘ₘ ρ) π).toReal ≤ c * (klDiv ρ π).toReal)
    (ρ : ℕ → Measure α) [IsProbabilityMeasure (ρ 0)] (hstep : ∀ k, ρ (k + 1) = P ∘ₘ ρ k)
    (hKL : klDiv (ρ 0) π ≠ ⊤) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) π ≠ ⊤ ∧
      (klDiv (ρ k) π).toReal ≤ c ^ k * (klDiv (ρ 0) π).toReal := by
  induction k with
  | zero => exact ⟨inferInstance, hKL, by simp⟩
  | succ k ih =>
    obtain ⟨hp, hfin, hle⟩ := ih
    obtain ⟨h1, h2⟩ := hone (ρ k) hfin
    rw [hstep k]
    refine ⟨inferInstance, h1, h2.trans ?_⟩
    rw [pow_succ, mul_comm (c ^ k) c, mul_assoc]
    exact mul_le_mul_of_nonneg_left hle hc

end FormalizeSampling.KLWarmApprox
