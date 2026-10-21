module

public import FormalizeSampling.ScoreEstimation.InnerSamplerAveraged
public import FormalizeSampling.Samplers.RandomScoreOracle

/-!
# GI-2 driven by guarantees of an inexact inner sampler

GI-2 (`Samplers/RandomScoreOracle.lean`, `GaussianIncrement.tvSup_biasedMonteCarloChain_le_sqrt`)
charges an inexact inner sampler `post k` only through the squared bias
`∑ᵢ (∫ yᵢ d(post k x) - m k x i)²` of its output mean. The bias bounds of
`ScoreEstimation/InnerSamplerBias.lean` (KL guarantee, sub-Gaussian exact posterior) and
`ScoreEstimation/InnerSamplerAveraged.lean` (averaged KL guarantee, coupling guarantee) turn it
into a guarantee of the inner sampler. The declarations live in the namespaces of those files.

## Main results

* `InnerSamplerBias.tvSup_biasedMonteCarloChain_le_sqrt_of_klDiv`: if `m k x` is the mean of
  an exact posterior `postEx k x` that is `σ_k²`-sub-Gaussian in every unit direction and
  `KL(post k x ‖ postEx k x) ≤ δ_k` for every `x`, then
  `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h_k c_k²/8)(2 σ_k² δ_k + ∫ V_k dν_k / N))`
  with `V_k(x) = ∑ᵢ Var_{post k x}(yᵢ)`.
* `InnerSamplerAveraged.tvSup_biasedMonteCarloChain_le_sqrt_of_integral_bias_le` (generic):
  the averaged squared bias replaced by any upper bound `β_k`.
* `InnerSamplerAveraged.tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv` and
  `_lintegral_klDiv_le`: the bias term `2 s_k ∫⁻ KL(post k x ‖ postEx k x) dν_k(x)`, so only an
  averaged KL guarantee `∫⁻ KL dν_k ≤ δ_k` is needed.
* `InnerSamplerAveraged.tvSup_biasedMonteCarloChain_le_sqrt_of_coupling` and `_coupling_le`:
  the bias term `∫ (∫ ‖y - y'‖² dγ_{k,x}) dν_k(x)` for couplings `γ k x` of `post k x` and
  `postEx k x`, with no sub-Gaussianity.

## Assumptions and scope

* As in GI-2, the integrability of the budget (`hB`) and of the variance term (`hV`) are
  hypotheses; the variance term refers to the inexact law `post k x` and is not bounded here.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.InnerSamplerBias

section BiasedMonteCarloChain

open GaussianIncrement

variable {d N : ℕ} {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {post : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (post k)]
  {postEx : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (postEx k)]
  {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {c : ℕ → ℝ}
  {R : ℕ → Kernel (Fin d → ℝ) (Fin N → Fin d → ℝ)} [∀ k, IsMarkovKernel (R k)]
  {bhat : ℕ → (Fin d → ℝ) × (Fin N → Fin d → ℝ) → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-2 driven by a KL guarantee of the inner sampler.** Under the hypotheses of
`tvSup_biasedMonteCarloChain_le_sqrt` (draws `R k x = (post k x)^{⊗N}` from the inexact
inner sampler `post k`, plug-in drift centred at `m k x`, `KL(ν 0 ‖ μ 0) < ∞`, budget `hB`
integrable), suppose in addition that `m k x` is the mean of an exact posterior `postEx k x`
(`hm`), that `postEx k x` is `s k`-sub-Gaussian along every unit direction (`hsub`), that
`KL(post k x ‖ postEx k x) ≤ δ k` for every state `x` (`hKL`), and that
`V k x = ∑ᵢ Var_{post k x}(yᵢ)` is `ν k`-integrable (`hV`). Then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k²/8)(2 s k δ k + ∫ V k dν_k / N))`.
The bias contribution `2 s_k δ_k` does not decrease with `N`. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt_of_klDiv (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (s δ : ℕ → ℝ≥0)
    (hm : ∀ k x i, m k x i = ∫ y, y i ∂(postEx k x))
    (hsub : ∀ k x (u : Fin d → ℝ), u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂(postEx k x)) (s k) (postEx k x))
    (hKL : ∀ k x, klDiv (post k x) (postEx k x) ≤ δ k)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * (2 * s k * δ k +
        (∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) / N)) := by
  refine (tvSup_biasedMonteCarloChain_le_sqrt (hb := hb) (hbh := hbh) hN hR hq hbhat hμ hν n
    hKL0 hB).trans (Real.sqrt_le_sqrt (add_le_add_right (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) _))
  have hνk : IsProbabilityMeasure (ν k) := by
    cases k with
    | zero => infer_instance
    | succ j => exact ErrorPropagation.isProbabilityMeasure_of_comp_succ hν (j + 1)
  have hpt : ∀ x, ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N) ≤
      2 * s k * δ k + (∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) / N := fun x => by
    rw [Finset.sum_add_distrib, Finset.sum_div]
    gcongr
    exact sum_sq_bias_le_of_klDiv_le (hm k x) (hsub k x)
      (fun i => (hq k x i).integrable one_le_two) (hKL k x)
  refine (integral_mono (hB k) ((integrable_const _).add ((hV k).div_const _)) hpt).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) ((hV k).div_const _), integral_div]
  simp

end BiasedMonteCarloChain

end FormalizeSampling.InnerSamplerBias

namespace FormalizeSampling.InnerSamplerAveraged

open InnerSamplerBias

section BiasedMonteCarloChain

open GaussianIncrement

variable {d N : ℕ} {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {post : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (post k)]
  {postEx : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (postEx k)]
  {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {c : ℕ → ℝ}
  {R : ℕ → Kernel (Fin d → ℝ) (Fin N → Fin d → ℝ)} [∀ k, IsMarkovKernel (R k)]
  {bhat : ℕ → (Fin d → ℝ) × (Fin N → Fin d → ℝ) → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-2 under an averaged squared-bias bound.** Under the hypotheses of
`tvSup_biasedMonteCarloChain_le_sqrt`, with `hV` (variance term integrable), if the averaged
squared bias satisfies `∫ ∑ᵢ (∫ yᵢ d(post k x) - m k x i)² dν_k(x) ≤ β_k`, then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k²/8)(β_k + ∫ V k dν_k / N))`. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt_of_integral_bias_le (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞) (β : ℕ → ℝ)
    (hbias : ∀ k, ∫ x, ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2 ∂(ν k) ≤ β k)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * (β k +
        (∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) / N)) := by
  refine (tvSup_biasedMonteCarloChain_le_sqrt (hb := hb) (hbh := hbh) hN hR hq hbhat hμ hν n
    hKL0 hB).trans (Real.sqrt_le_sqrt (add_le_add_right (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) _))
  have hbi := integrable_sum_sq_bias (hB k) (hV k)
  have e : (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) = fun x =>
      ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2 +
        (∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) / N := by
    funext x; rw [Finset.sum_add_distrib, Finset.sum_div]
  rw [e, integral_add hbi ((hV k).div_const _), integral_div]
  linarith [hbias k]

/-- **GI-2 driven by an averaged KL guarantee of the inner sampler.** Under the hypotheses of
`tvSup_biasedMonteCarloChain_le_sqrt` (draws `R k x = (post k x)^{⊗N}`, plug-in drift centred at
`m k x`, `KL(ν 0 ‖ μ 0) < ∞`, budget `hB` and variance term `hV` integrable), suppose `m k x`
is the mean of an exact posterior `postEx k x` (`hm`) that is `s k`-sub-Gaussian along every
unit direction (`hsub`), and that the KL error of the inner sampler is finite **on average**
under the algorithm's law: `∫⁻ KL(post k x ‖ postEx k x) dν_k(x) < ∞` (`hKLfin`). Then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 +`
`∑_{k<n} (h k c k²/8)(2 s k ∫⁻ KL(post k x ‖ postEx k x) dν_k(x) + ∫ V k dν_k / N))`. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (s : ℕ → ℝ≥0)
    (hm : ∀ k x i, m k x i = ∫ y, y i ∂(postEx k x))
    (hsub : ∀ k x (u : Fin d → ℝ), u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂(postEx k x)) (s k) (postEx k x))
    (hKLfin : ∀ k, ∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k) ≠ ∞)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 *
        (2 * s k * (∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k)).toReal +
        (∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) / N)) :=
  tvSup_biasedMonteCarloChain_le_sqrt_of_integral_bias_le (hb := hb) (hbh := hbh) hN hR hq
    hbhat hμ hν n hKL0 _ (fun k => integral_sum_sq_bias_le_lintegral_klDiv
      (fun x i => (hq k x i).integrable one_le_two) (hm k) (hsub k)
      (integrable_sum_sq_bias (hB k) (hV k)) (hKLfin k)) hB hV

/-- **GI-2 under an averaged KL budget.** As
`tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv`, with the averaged KL guarantee
`∫⁻ KL(post k x ‖ postEx k x) dν_k(x) ≤ δ k` in place of the uniform-in-`x` hypothesis of
`tvSup_biasedMonteCarloChain_le_sqrt_of_klDiv`:
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k²/8)(2 s k δ k + ∫ V k dν_k / N))`. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv_le (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (s δ : ℕ → ℝ≥0)
    (hm : ∀ k x i, m k x i = ∫ y, y i ∂(postEx k x))
    (hsub : ∀ k x (u : Fin d → ℝ), u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂(postEx k x)) (s k) (postEx k x))
    (hKL : ∀ k, ∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k) ≤ δ k)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * (2 * s k * δ k +
        (∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) / N)) := by
  have hfin : ∀ k, ∫⁻ x, klDiv (post k x) (postEx k x) ∂(ν k) ≠ ∞ := fun k =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hKL k)
  refine tvSup_biasedMonteCarloChain_le_sqrt_of_integral_bias_le (hb := hb) (hbh := hbh) hN hR
    hq hbhat hμ hν n hKL0 _ (fun k => ?_) hB hV
  refine (integral_sum_sq_bias_le_lintegral_klDiv
    (fun x i => (hq k x i).integrable one_le_two) (hm k) (hsub k)
    (integrable_sum_sq_bias (hB k) (hV k)) (hfin k)).trans ?_
  gcongr
  exact ENNReal.toReal_le_coe_of_le_coe (hKL k)

omit [∀ k, IsMarkovKernel (postEx k)] in
/-- **GI-2 driven by a coupling (`W₂`-type) guarantee, averaged.** Under the hypotheses of
`tvSup_biasedMonteCarloChain_le_sqrt`, suppose `m k x` is the mean of an exact posterior
`postEx k x` with integrable coordinates (`hm`, `hqEx`), and `γ k x` is a coupling of
`post k x` and `postEx k x` (`hγ1`, `hγ2`) whose averaged transport cost
`∫⁻ (∫⁻ ‖y - y'‖² dγ_{k,x}) dν_k(x)` is finite (`hWfin`). No sub-Gaussianity is assumed. Then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 +`
`∑_{k<n} (h k c k²/8)(∫⁻ ∫⁻ ‖y - y'‖² dγ_{k,x} dν_k(x) + ∫ V k dν_k / N))`. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt_of_coupling (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hm : ∀ k x i, m k x i = ∫ y, y i ∂(postEx k x))
    (hqEx : ∀ k x i, Integrable (fun y : Fin d → ℝ => y i) (postEx k x))
    (γ : ℕ → (Fin d → ℝ) → Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hγ1 : ∀ k x, (γ k x).map Prod.fst = post k x)
    (hγ2 : ∀ k x, (γ k x).map Prod.snd = postEx k x)
    (hWfin : ∀ k, ∫⁻ x, ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂(γ k x) ∂(ν k) ≠ ∞)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 *
        ((∫⁻ x, ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂(γ k x) ∂(ν k)).toReal +
        (∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) / N)) := by
  refine tvSup_biasedMonteCarloChain_le_sqrt_of_integral_bias_le (hb := hb) (hbh := hbh) hN hR
    hq hbhat hμ hν n hKL0 _ (fun k => ?_) hB hV
  have hbi := integrable_sum_sq_bias (hB k) (hV k)
  have hA0 : ∀ x, 0 ≤ ∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2 := fun x =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hpt : ∀ x, ENNReal.ofReal (∑ i, (∫ y, y i ∂(post k x) - m k x i) ^ 2) ≤
      ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂(γ k x) := fun x => by
    simp_rw [hm k x]
    exact ofReal_sum_sq_bias_le_lintegral_coupling (γ k x) (hγ1 k x) (hγ2 k x)
      (fun i => (hq k x i).integrable one_le_two) (hqEx k x)
  have hl := lintegral_mono (μ := ν k) hpt
  rw [← ofReal_integral_eq_lintegral_ofReal hbi (ae_of_all _ hA0)] at hl
  have := ENNReal.toReal_mono (hWfin k) hl
  rwa [ENNReal.toReal_ofReal (integral_nonneg hA0)] at this

omit [∀ k, IsMarkovKernel (postEx k)] in
/-- **GI-2 under a pointwise coupling budget, averaged.** As
`tvSup_biasedMonteCarloChain_le_sqrt_of_coupling`, with the transport cost of `γ k x` bounded by
a nonnegative `ν k`-integrable function `w k` (`∫⁻ ‖y - y'‖² dγ_{k,x} ≤ w k x`, e.g.
`w k x ≥ W₂²(post k x, postEx k x)` attained by `γ k x`). Then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k²/8)(∫ w k dν_k + ∫ V k dν_k / N))`. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt_of_coupling_le (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hm : ∀ k x i, m k x i = ∫ y, y i ∂(postEx k x))
    (hqEx : ∀ k x i, Integrable (fun y : Fin d → ℝ => y i) (postEx k x))
    (γ : ℕ → (Fin d → ℝ) → Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hγ1 : ∀ k x, (γ k x).map Prod.fst = post k x)
    (hγ2 : ∀ k x, (γ k x).map Prod.snd = postEx k x)
    (w : ℕ → (Fin d → ℝ) → ℝ) (hw0 : ∀ k x, 0 ≤ w k x) (hwi : ∀ k, Integrable (w k) (ν k))
    (hw : ∀ k x, ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂(γ k x) ≤
      ENNReal.ofReal (w k x))
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k))
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * (∫ x, w k x ∂(ν k) +
        (∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) / N)) := by
  have hl : ∀ k, ∫⁻ x, ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2) ∂(γ k x) ∂(ν k) ≤
      ENNReal.ofReal (∫ x, w k x ∂(ν k)) := fun k => by
    rw [ofReal_integral_eq_lintegral_ofReal (hwi k) (ae_of_all _ (hw0 k))]
    exact lintegral_mono (hw k)
  refine (tvSup_biasedMonteCarloChain_le_sqrt_of_coupling (hb := hb) (hbh := hbh) hN hR hq
    hbhat hμ hν n hKL0 hm hqEx γ hγ1 hγ2
    (fun k => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hl k)) hB hV).trans
    (Real.sqrt_le_sqrt (add_le_add_right (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) _))
  gcongr
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hl k)
  rwa [ENNReal.toReal_ofReal (integral_nonneg (hw0 k))] at this

end BiasedMonteCarloChain

end FormalizeSampling.InnerSamplerAveraged
