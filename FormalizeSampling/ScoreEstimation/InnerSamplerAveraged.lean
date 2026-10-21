module

public import FormalizeSampling.ScoreEstimation.InnerSamplerBias

/-!
# Inner-sampler bias: averaged KL guarantees and coupling guarantees

`InnerSamplerBias.lean` drives GI-2 (`tvSup_biasedMonteCarloChain_le_sqrt`) by a KL guarantee
`KL(post k x ‖ postEx k x) ≤ δ_k` of the inner sampler, assumed for **every** state `x`, and
needs the exact posterior to be sub-Gaussian. The theorems here need neither restriction.

## Main results

The GI-2 chain bounds (`tvSup_biasedMonteCarloChain_le_sqrt_of_*`) are in
`Samplers/RandomScoreOracleInner.lean`, in this namespace.

* `tvSup_biasedMonteCarloChain_le_sqrt_of_integral_bias_le` (generic): GI-2 with the averaged
  squared bias `∫ ∑ᵢ (∫ yᵢ d(post k x) - m k x i)² dν_k(x)` replaced by any upper bound `β_k`.
* Averaged KL guarantee (`integral_sum_sq_bias_le_lintegral_klDiv`,
  `tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv`,
  `tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv_le`): the bias term becomes
  `2 s_k ∫⁻ KL(post k x ‖ postEx k x) dν_k(x)`, so only `∫⁻ KL dν_k ≤ δ_k` is needed.
  No measurability of `x ↦ KL(post k x ‖ postEx k x)` is required (lower Lebesgue integral).
* Coupling guarantee, no sub-Gaussianity (`ofReal_sum_sq_bias_le_lintegral_coupling`,
  `sum_sq_bias_le_of_coupling`): if `γ` is a coupling of `q'` and `q` (explicit measure on the
  product with marginals `q'`, `q`), then `∑ᵢ (∫ yᵢ dq' - ∫ yᵢ dq)² ≤ ∫ ‖y - y'‖² dγ` (Jensen),
  in particular `≤ W₂²(q', q)` (Mathlib has no `W₂`, so the coupling is explicit).
* `tvSup_biasedMonteCarloChain_le_sqrt_of_coupling` and
  `tvSup_biasedMonteCarloChain_le_sqrt_of_coupling_le`: GI-2 with bias term
  `∫ (∫ ‖y - y'‖² dγ_{k,x}) dν_k(x)`, resp. `∫ w_k dν_k` when `∫ ‖y - y'‖² dγ_{k,x} ≤ w_k(x)`.
* Tightness (`sum_sq_bias_translate_eq`): for a deterministic shift `q' = q ∘ (· + a)⁻¹` and the
  translation coupling `y ↦ (y + a, y)`, the coupling bias bound is an equality.

## Assumptions and scope

* `‖·‖²` is the Euclidean `∑ᵢ (·)ᵢ²` on `Fin d → ℝ`, as in the other files.
* Couplings `γ k x` are arbitrary measures on the product, indexed by `x` with no measurability
  in `x` required (only lower Lebesgue integrals in `x` are used).
* In the averaged statements the finiteness of the averaged KL / transport cost, the
  integrability of the GI-2 budget (`hB`) and of the variance term (`hV`) are hypotheses.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.InnerSamplerAveraged

open InnerSamplerBias

section Pointwise

variable {d : ℕ} {q q' : Measure (Fin d → ℝ)}

/-- Monotonicity of the sub-Gaussian parameter: `HasSubgaussianMGF X c μ` and `c ≤ c'` give
`HasSubgaussianMGF X c' μ`. -/
theorem hasSubgaussianMGF_mono {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ}
    {c c' : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hc : c ≤ c') : HasSubgaussianMGF X c' μ :=
  ⟨hX.integrable_exp_mul, fun t => (hX.mgf_le t).trans (exp_le_exp.2 (by gcongr))⟩

/-- **Squared bias from KL, extended-real form.** Under the hypotheses of `sum_sq_bias_le`
but without assuming `KL(q' ‖ q) < ∞`, and for `s ≠ 0`,
`ofReal (∑ᵢ (∫ yᵢ dq' - mᵢ)²) ≤ 2 s KL(q' ‖ q)` in `ℝ≥0∞`, where `mᵢ = ∫ yᵢ dq`. -/
theorem ofReal_sum_sq_bias_le [IsProbabilityMeasure q] [IsProbabilityMeasure q'] {s : ℝ≥0}
    (hs : s ≠ 0) {m : Fin d → ℝ} (hm : ∀ i, m i = ∫ y, y i ∂q)
    (hsub : ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂q) s q)
    (hq' : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q') :
    ENNReal.ofReal (∑ i, (∫ y, y i ∂q' - m i) ^ 2) ≤ 2 * (s : ℝ≥0∞) * klDiv q' q := by
  by_cases hKL : klDiv q' q = ∞
  · rw [hKL, ENNReal.mul_top (by simpa using hs)]
    exact le_top
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp_rw [hm]
  simpa using sum_sq_bias_le hsub hq' hKL

/-- **Jensen for a coupling.** Let `γ` be a coupling of `q'` and `q` (`γ.map Prod.fst = q'`,
`γ.map Prod.snd = q`), both with integrable coordinates. Then the squared distance of the means
is at most the expected squared distance under the coupling:
`ofReal (∑ᵢ (∫ yᵢ dq' - ∫ yᵢ dq)²) ≤ ∫⁻ ofReal (∑ᵢ (y - y')ᵢ²) dγ`. No sub-Gaussianity or
finiteness of the right-hand side is needed. Taking the infimum over couplings bounds the
squared bias by `W₂²(q', q)`. -/
theorem ofReal_sum_sq_bias_le_lintegral_coupling [IsProbabilityMeasure q']
    (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (h1 : γ.map Prod.fst = q')
    (h2 : γ.map Prod.snd = q) (hq' : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q')
    (hq : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q) :
    ENNReal.ofReal (∑ i, (∫ y, y i ∂q' - ∫ y, y i ∂q) ^ 2) ≤
      ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂γ := by
  set G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun p => ∑ i, (p.1 i - p.2 i) ^ 2 with hG
  have hγ : IsProbabilityMeasure γ := by
    constructor
    have := congrArg (fun μ : Measure (Fin d → ℝ) => μ Set.univ) h1
    simp only [measure_univ] at this
    rw [Measure.map_apply measurable_fst MeasurableSet.univ] at this
    simpa using this
  by_cases hfin : ∫⁻ p, ENNReal.ofReal (G p) ∂γ = ∞
  · rw [hfin]; exact le_top
  have hGm : Measurable G := by
    simp only [hG]; fun_prop
  have hG0 : ∀ p, 0 ≤ G p := fun p => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hGi : Integrable G γ :=
    ⟨hGm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hG0)).2
      (lt_top_iff_ne_top.2 hfin)⟩
  have hgm : ∀ i, Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 i - p.2 i := fun i => by
    fun_prop
  have hg2 : ∀ i, Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (p.1 i - p.2 i) ^ 2) γ :=
    fun i => hGi.mono' ((hgm i).pow_const 2).aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact Finset.single_le_sum (f := fun j => (p.1 j - p.2 j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hg : ∀ i, MemLp (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 i - p.2 i) 2 γ := fun i =>
    (memLp_two_iff_integrable_sq (hgm i).aestronglyMeasurable).2 (hg2 i)
  have hmean : ∀ i, ∫ y, y i ∂q' - ∫ y, y i ∂q = ∫ p, (p.1 i - p.2 i) ∂γ := fun i => by
    have e1 : ∫ y, y i ∂q' = ∫ p, p.1 i ∂γ := by
      rw [← h1]
      exact integral_map measurable_fst.aemeasurable
        (measurable_pi_apply i).aestronglyMeasurable
    have e2 : ∫ y, y i ∂q = ∫ p, p.2 i ∂γ := by
      rw [← h2]
      exact integral_map measurable_snd.aemeasurable
        (measurable_pi_apply i).aestronglyMeasurable
    have i1 : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 i) γ := by
      have := hq' i; rw [← h1] at this
      exact (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
        measurable_fst.aemeasurable).1 this
    have i2 : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 i) γ := by
      have := hq i; rw [← h2] at this
      exact (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
        measurable_snd.aemeasurable).1 this
    rw [e1, e2, integral_sub i1 i2]
  have hjensen : ∀ i, (∫ p, (p.1 i - p.2 i) ∂γ) ^ 2 ≤ ∫ p, (p.1 i - p.2 i) ^ 2 ∂γ := fun i => by
    have h0 := variance_nonneg (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 i - p.2 i) γ
    rw [variance_eq_sub (hg i)] at h0
    simp only [Pi.pow_apply] at h0
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ hG0)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hmean, hG]
  rw [integral_finsetSum _ fun i _ => hg2 i]
  exact Finset.sum_le_sum fun i _ => hjensen i

/-- **Squared bias from a `W₂`-type coupling bound.** If `γ` is a coupling of `q'` and `q`
(both with integrable coordinates) with `∫⁻ ‖y - y'‖² dγ ≤ w`, `w ≥ 0`, and `mᵢ = ∫ yᵢ dq`, then
`∑ᵢ (∫ yᵢ dq' - mᵢ)² ≤ w`. -/
theorem sum_sq_bias_le_of_coupling [IsProbabilityMeasure q']
    (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (h1 : γ.map Prod.fst = q')
    (h2 : γ.map Prod.snd = q) (hq' : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q')
    (hq : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q) {m : Fin d → ℝ}
    (hm : ∀ i, m i = ∫ y, y i ∂q) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂γ ≤ ENNReal.ofReal w) :
    ∑ i, (∫ y, y i ∂q' - m i) ^ 2 ≤ w := by
  have := (ofReal_sum_sq_bias_le_lintegral_coupling γ h1 h2 hq' hq).trans hw
  rw [ENNReal.ofReal_le_ofReal_iff hw0] at this
  simp_rw [hm]
  exact this

/-- **Tightness of the coupling bound (deterministic shift).** For a probability measure `q`
with integrable coordinates and a shift `a`, the translation coupling
`γ = q.map (y ↦ (y + a, y))` has marginals `q.map (· + a)` and `q`, and the coupling bias bound
of `ofReal_sum_sq_bias_le_lintegral_coupling` is an equality: both sides equal `∑ᵢ aᵢ²`.
(Point masses are the case `q = δ_x`.) -/
theorem sum_sq_bias_translate_eq (q : Measure (Fin d → ℝ)) [IsProbabilityMeasure q]
    (hq : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q) (a : Fin d → ℝ) :
    (q.map fun y => (y + a, y)).map Prod.fst = q.map (· + a) ∧
      (q.map fun y => (y + a, y)).map Prod.snd = q ∧
      ENNReal.ofReal (∑ i, (∫ y, y i ∂(q.map (· + a)) - ∫ y, y i ∂q) ^ 2) =
        ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂(q.map fun y => (y + a, y)) := by
  have hm : Measurable fun y : Fin d → ℝ => (y + a, y) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]; rfl
  · rw [Measure.map_map measurable_snd hm]; simp [Function.comp_def]
  · rw [lintegral_map (by fun_prop) hm]
    simp only [Pi.add_apply, add_sub_cancel_left, lintegral_const, measure_univ, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_map hm.fst.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    simp only [Pi.add_apply]
    rw [integral_add (hq i) (integrable_const _)]
    simp

end Pointwise

section BiasedMonteCarloChain

open GaussianIncrement

variable {d N : ℕ} {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {post : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (post k)]
  {postEx : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (postEx k)]
  {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {c : ℕ → ℝ}
  {R : ℕ → Kernel (Fin d → ℝ) (Fin N → Fin d → ℝ)} [∀ k, IsMarkovKernel (R k)]
  {bhat : ℕ → (Fin d → ℝ) × (Fin N → Fin d → ℝ) → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

omit [∀ k, IsMarkovKernel (post k)] in
/-- The squared bias `x ↦ ∑ᵢ (∫ yᵢ d(post k x) - m k x i)²` is `ν k`-integrable whenever the
GI-2 budget (`hB`) and the variance term (`hV`) are. -/
theorem integrable_sum_sq_bias {k : ℕ}
    (hB : Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    Integrable (fun x => ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2) (ν k) :=
  (hB.sub (hV.div_const N)).congr (ae_of_all _ fun x => by
    simp only [Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_div, add_sub_cancel_right])

/-- **Averaged squared bias from averaged KL.** Fix `k`. If `m k x` is the mean of `postEx k x`
(`hm`), `postEx k x` is `s`-sub-Gaussian in every unit direction for every `x` (`hsub`), the
squared bias is `ν k`-integrable and the averaged KL `∫⁻ KL(post k x ‖ postEx k x) dν_k(x)` is
finite, then `∫ ∑ᵢ (∫ yᵢ d(post k x) - m k x i)² dν_k(x) ≤ 2 s (∫⁻ KL dν_k).toReal`. No
measurability of `x ↦ KL(post k x ‖ postEx k x)` is needed. -/
theorem integral_sum_sq_bias_le_lintegral_klDiv {k : ℕ} {s : ℝ≥0}
    (hq : ∀ x i, Integrable (fun y : Fin d → ℝ => y i) (post k x))
    (hm : ∀ x i, m k x i = ∫ y, y i ∂(postEx k x))
    (hsub : ∀ x (u : Fin d → ℝ), u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂(postEx k x)) s (postEx k x))
    (hbi : Integrable (fun x => ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2) (ν k))
    (hKLfin : ∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k) ≠ ∞) :
    ∫ x, ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2 ∂(ν k) ≤
      2 * s * (∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k)).toReal := by
  set K := ∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k)
  set A := ∫ x, ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2 ∂(ν k)
  have hA0 : ∀ x, 0 ≤ ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2 := fun x =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  -- for every `ε > 0`, the bound holds with `s + ε` (which is nonzero)
  have hε : ∀ ε : ℝ≥0, 0 < ε → A ≤ 2 * (s + ε) * K.toReal := fun ε hε => by
    have hse : s + ε ≠ 0 := (lt_of_lt_of_le hε le_add_self).ne'
    have hpt : ∀ x, ENNReal.ofReal (∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2) ≤
        2 * ((s + ε : ℝ≥0) : ℝ≥0∞) * klDiv (post k x) (postEx k x) := fun x =>
      ofReal_sum_sq_bias_le hse (hm x)
        (fun u hu => hasSubgaussianMGF_mono (hsub x u hu) le_self_add) (hq x)
    have hl := (lintegral_mono (μ := ν k) hpt).trans_eq (lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top))
    rw [← ofReal_integral_eq_lintegral_ofReal hbi (ae_of_all _ hA0)] at hl
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top) hKLfin) hl
    rw [ENNReal.toReal_ofReal (integral_nonneg hA0), ENNReal.toReal_mul,
      ENNReal.toReal_mul] at this
    rw [ENNReal.toReal_ofNat, ENNReal.coe_toReal] at this
    push_cast at this
    exact this
  refine le_of_forall_pos_le_add fun ε hε0 => ?_
  have hK0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  set η : ℝ≥0 := ⟨ε / (2 * K.toReal + 1), by positivity⟩
  have hη := hε η (by
    change (0 : ℝ) < ε / (2 * K.toReal + 1)
    positivity)
  have hηK : 2 * (η : ℝ) * K.toReal ≤ ε := by
    change 2 * (ε / (2 * K.toReal + 1)) * K.toReal ≤ ε
    rw [mul_comm 2, mul_assoc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end BiasedMonteCarloChain

end FormalizeSampling.InnerSamplerAveraged
