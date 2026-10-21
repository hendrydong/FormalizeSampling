module

public import Mathlib.Probability.Kernel.Deterministic
public import FormalizeSampling.Samplers.GaussianIncrementPi
public import FormalizeSampling.ScoreEstimation.MonteCarlo

/-!
# Gaussian-increment chains with a random score oracle (GI-2)

GI-1 (`GaussianIncrementPi.lean`) compares two chains with **deterministic** drifts. Practical
score-based samplers re-estimate the score at every step from fresh random draws, so the drift
is random. This file models that and derives an explicit sample-size bound.

## Model

* Randomness space `Ω` (any measurable space). At step `k`, from state `x`, draw
  `ω ~ R k x` (a Markov kernel: the law of the draws may depend on the current state, as for
  posterior samples), then move to `N(x + h k · b̂ k (x, ω), 2 h k I)`. The resulting one-step
  kernel is `randomEmKernel (h k) (R k) (bhat k)`, i.e. the mixture
  `x ↦ ∫ N(x + h b̂(x, ω), 2hI) d(R x)(ω)`.
* The reference chain is the exact-drift chain `emKernelPi (h k) (b k)` of GI-1.

## Main results

* `klDiv_randomEmKernel_le` (one step): by data processing and the KL chain rule (KL-2),
  `KL(randomEmKernel h R b̂ x ‖ emKernelPi h b x) ≤ ∫ h ‖b(x) - b̂(x, ω)‖² / 4 d(R x)(ω)`:
  a random drift costs at most the **mean-square** drift error (convexity of KL).
* `klDiv_randomEmChain_le_sum`, `tvSup_randomEmChain_le_sqrt`: GI-1 for random oracles,
  errors averaged over the oracle's draws and over the algorithm's laws `ν k`.
* Monte Carlo instance. `R k x = (post k x)^{⊗N}` (`N` exact i.i.d. draws from a Markov kernel
  `post k`, e.g. the posterior of `X₀` given the current state), `m k x` the mean of
  `post k x`, and the plug-in drift `b̂ k (x, ω) = b k x + c k · (empMean ω - m k x)`
  (for the OU/denoising score `s = (a m - x)/σ²`, SE-3, an estimated score enters the drift
  in exactly this form with `c = (drift weight) · a / σ²`).
  - `integral_sq_empMean_sub`: `E‖m̂ - m‖²` coordinatewise `= Var / N` (SE-4 with
    independence from the product measure);
  - `lintegral_monteCarlo_error`: the per-step budget is `h c² V(x) / (4N)` with
    `V(x) = ∑ᵢ Var_{post x}(yᵢ)` (trace of the posterior covariance);
  - `klDiv_monteCarloChain_le_sum` and the end-to-end sample-size bound
    `tvSup_monteCarloChain_le_sqrt` (the zero-bias cases of the inexact forms below):
    `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² /(8N) ∫ V_k dν_k)`.
    Hence `tvSup ≤ ε` as soon as `N ≥ (∑_k h_k c_k² ∫ V_k dν_k / 8) / (ε² - KL(ν 0 ‖ μ 0)/2)`.
* Inexact inner sampler. If the draws come from an approximate posterior `post k x` whose mean
  differs from the exact mean `m k x`:
  - `integral_sq_empMean_sub_biased`: `E[(m̂ᵢ - a)²] = (bias)² + Var / N`;
  - `klDiv_biasedMonteCarloChain_le_sum`, `tvSup_biasedMonteCarloChain_le_sqrt`:
    `tvSup ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h_k c_k²/8) ∫ (‖bias_k‖² + V_k/N) dν_k)`.
    The bias part does not decrease with `N`.

## Assumptions and scope

* The draws are i.i.d. from `post k x` (hypothesis `hR`). In the exact results `post k x` has
  mean `m k x`; the biased results allow any `post k x` and only charge its mean-square bias,
  so an inner sampler enters through the bias of its output mean (bounding that bias, e.g.
  from a KL or Wasserstein guarantee for the inner sampler, is not done here). `R k` must be
  supplied as a kernel with `R k x = (post k x)^{⊗N}` (`hR`). Mathlib v4.35 has no product of
  kernels; `Kernels/KernelPi.lean` constructs it (`KernelPi.piConst N (post k)`, for any
  finite, possibly state-dependent kernel `post k`), and `Samplers/RandomScoreOracleKernel.lean`
  restates the TV bounds with `R k := KernelPi.piConst N (post k)` and `hR` discharged
  (`tvSup_piConstMonteCarloChain_le_sqrt`, `tvSup_piConstBiasedMonteCarloChain_le_sqrt`),
  with a state-dependent Gaussian posterior `N(x, t_k I)` as non-vacuity example
  (`tvSup_heatKernelPiMonteCarloChain_le_sqrt`).
* `post k x` has finite second moments (`hq`), and `V k` is `ν k`-integrable (`hV`).
* The relation between `b k`, `m k` and a true score (Tweedie) is not used: the bound holds
  for any exact drift `b k` and any plug-in estimator of the stated form. Bounds on `V k`
  (e.g. `V ≲ d σ²` for Gaussian-like posteriors) and on the discretisation error of the exact
  chain are not proved here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.GaussianIncrement
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]


/-- The Gaussian step with a drift that reads the randomness: `(x, ω) ↦ N(x + h b̂(x, ω), 2hI)`
(built from `emKernelPi` with zero drift, precomposed with `(x, ω) ↦ x + h b̂(x, ω)`). -/
noncomputable def randDriftKernel (h : ℝ≥0) (bhat : (Fin d → ℝ) × Ω → Fin d → ℝ)
    (hb : Measurable bhat) : Kernel ((Fin d → ℝ) × Ω) (Fin d → ℝ) :=
  Kernel.comap (emKernelPi h (fun _ => 0) measurable_const) (fun p => p.1 + h • bhat p)
    (measurable_fst.add (hb.const_smul _))

/-- `randDriftKernel h b̂ (x, ω)` is the isotropic EM step from `x` with the constant drift
`b̂(x, ω)`. -/
theorem randDriftKernel_apply (h : ℝ≥0) {bhat : (Fin d → ℝ) × Ω → Fin d → ℝ}
    (hb : Measurable bhat) (x : Fin d → ℝ) (ω : Ω) :
    randDriftKernel h bhat hb (x, ω) =
      emKernelPi h (fun _ => bhat (x, ω)) measurable_const x := by
  simp [randDriftKernel, emKernelPi_apply, Kernel.comap_apply, NNReal.smul_def]

/-- `randDriftKernel` is Markov (each value is a product of Gaussians). -/
instance isMarkovKernel_randDriftKernel (h : ℝ≥0) {bhat : (Fin d → ℝ) × Ω → Fin d → ℝ}
    (hb : Measurable bhat) :
    IsMarkovKernel (randDriftKernel h bhat hb) := by
  unfold randDriftKernel; infer_instance

/-- The **random-oracle EM kernel**: draw `ω ~ R x`, then step to `N(x + h b̂(x, ω), 2hI)`;
the one-step law is the mixture over `ω`. -/
noncomputable def randomEmKernel (h : ℝ≥0) (R : Kernel (Fin d → ℝ) Ω) [IsMarkovKernel R]
    (bhat : (Fin d → ℝ) × Ω → Fin d → ℝ) (hb : Measurable bhat) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  randDriftKernel h bhat hb ∘ₖ (Kernel.id ×ₖ R)

/-- `randomEmKernel` is Markov (a composition of Markov kernels). -/
instance isMarkovKernel_randomEmKernel (h : ℝ≥0) (R : Kernel (Fin d → ℝ) Ω) [IsMarkovKernel R]
    {bhat : (Fin d → ℝ) × Ω → Fin d → ℝ} (hb : Measurable bhat) :
    IsMarkovKernel (randomEmKernel h R bhat hb) := by
  unfold randomEmKernel; infer_instance

/-- The random-oracle kernel at `x` is the mixture `∫ N(x + h b̂(x, ω), 2hI) d(R x)(ω)`, written
as a composition with `R x`. -/
theorem randomEmKernel_apply (h : ℝ≥0) (R : Kernel (Fin d → ℝ) Ω) [IsMarkovKernel R]
    {bhat : (Fin d → ℝ) × Ω → Fin d → ℝ} (hb : Measurable bhat) (x : Fin d → ℝ) :
    randomEmKernel h R bhat hb x =
      (Kernel.comap (randDriftKernel h bhat hb) (fun ω => (x, ω)) measurable_prodMk_left) ∘ₘ
        R x := by
  rw [randomEmKernel, Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod]
  rw [Measure.bind_map]
  · rfl
  · exact measurable_prodMk_left.aemeasurable
  · exact (Kernel.measurable _).aemeasurable

/-- **One-step KL of a random-oracle EM step (GI-2).** For every state `x`,
`KL(randomEmKernel h R b̂ x ‖ emKernelPi h b x) ≤ ∫ h ‖b(x) - b̂(x, ω)‖² / 4 d(R x)(ω)`.
Direction: algorithm first; the drift error is averaged over the oracle's draws `ω ~ R x`.
Proof: data processing for the second marginal and the integrated chain rule (KL-2). -/
theorem klDiv_randomEmKernel_le (h : ℝ≥0) (R : Kernel (Fin d → ℝ) Ω) [IsMarkovKernel R]
    {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b)
    {bhat : (Fin d → ℝ) × Ω → Fin d → ℝ} (hbh : Measurable bhat) (x : Fin d → ℝ) :
    klDiv (randomEmKernel h R bhat hbh x) (emKernelPi h b hb x) ≤
      ∫⁻ ω, ENNReal.ofReal (h * (∑ i, (b x i - bhat (x, ω) i) ^ 2) / 4) ∂(R x) := by
  have hP : emKernelPi h b hb x = Kernel.const Ω (emKernelPi h b hb x) ∘ₘ R x := by
    simp
  rw [randomEmKernel_apply, hP]
  refine (KL.klDiv_comp_le_compProd _ _ _ _).trans_eq ?_
  rw [KL.klDiv_compProd_right_eq_lintegral]
  refine lintegral_congr fun ω => ?_
  rw [Kernel.comap_apply, randDriftKernel_apply, Kernel.const_apply, klDiv_emKernelPi]
  simp_rw [← neg_sub (b x _), neg_sq]


section Chain

variable {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {R : ℕ → Kernel (Fin d → ℝ) Ω} [∀ k, IsMarkovKernel (R k)]
  {bhat : ℕ → (Fin d → ℝ) × Ω → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-2, KL form.** For the exact chain `μ (k+1) = emKernelPi (h k) (b k) ∘ₘ μ k` and the
random-oracle chain `ν (k+1) = randomEmKernel (h k) (R k) (b̂ k) ∘ₘ ν k` from probability laws,
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫∫ h k ‖b k x - b̂ k (x, ω)‖² / 4 d(R k x)(ω) dν_k(x)`:
errors averaged over the draws and over the algorithm's laws `ν k`. -/
theorem klDiv_randomEmChain_le_sum [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) + ∑ k ∈ range n, ∫⁻ x, ∫⁻ ω,
      ENNReal.ofReal (h k * (∑ i, (b k x i - bhat k (x, ω) i) ^ 2) / 4) ∂(R k x) ∂(ν k) := by
  have : ∀ k, IsFiniteMeasure (μ k) := fun k =>
    have := ErrorPropagation.isProbabilityMeasure_of_comp_succ hμ k; inferInstance
  have : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    have := ErrorPropagation.isProbabilityMeasure_of_comp_succ hν k; inferInstance
  refine (KL.klDiv_chain_le_sum (fun k => emKernelPi (h k) (b k) (hb k))
    (fun k => randomEmKernel (h k) (R k) (bhat k) (hbh k)) μ ν hμ hν n).trans ?_
  gcongr with k hk x
  exact klDiv_randomEmKernel_le _ _ _ _ x

/-- **GI-2, TV form.** Same chains as `klDiv_randomEmChain_le_sum`; if the KL budget `B` there is
finite, `tvSup (ν n) (μ n) ≤ √(B / 2)` (one Pinsker step at the end). -/
theorem tvSup_randomEmChain_le_sqrt [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hB : klDiv (ν 0) (μ 0) + ∑ k ∈ range n, ∫⁻ x, ∫⁻ ω,
      ENNReal.ofReal (h k * (∑ i, (b k x i - bhat k (x, ω) i) ^ 2) / 4) ∂(R k x) ∂(ν k) ≠ ∞) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0) + ∑ k ∈ range n,
      ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (h k * (∑ i, (b k x i - bhat k (x, ω) i) ^ 2) / 4)
        ∂(R k x) ∂(ν k)).toReal / 2) := by
  have := ErrorPropagation.isProbabilityMeasure_of_comp_succ hμ n
  have := ErrorPropagation.isProbabilityMeasure_of_comp_succ hν n
  have hKL := klDiv_randomEmChain_le_sum hμ hν n
  refine (Pinsker.tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top hB hKL)).trans
    (Real.sqrt_le_sqrt ?_)
  gcongr

end Chain

section MonteCarlo
variable {d : ℕ}

/-- The empirical mean `(1/n) ∑ⱼ ωⱼ` of `n` points of `Fin d → ℝ`. -/
noncomputable def empMean (ω : Fin n → Fin d → ℝ) : Fin d → ℝ := (1 / (n : ℝ)) • ∑ j, ω j

/-- **Monte Carlo mean-square error, coordinatewise.** For `n > 0` i.i.d. draws from a probability
measure `q` on `Fin d → ℝ` with square-integrable coordinates,
`E[(m̂ᵢ - ∫ yᵢ dq)²] = Var_q(yᵢ) / n` under the product law `q^{⊗n}`. -/
theorem integral_sq_empMean_sub (hn : 0 < n) (q : Measure (Fin d → ℝ)) [IsProbabilityMeasure q]
    (hq : ∀ i, MemLp (fun y : Fin d → ℝ => y i) 2 q) (i : Fin d) :
    ∫ ω, (empMean ω i - ∫ y, y i ∂q) ^ 2 ∂(Measure.pi fun _ : Fin n => q) =
      variance (fun y : Fin d → ℝ => y i) q / n := by
  have hmeas : Measurable (fun y : Fin d → ℝ => y i) := measurable_pi_apply i
  have hlaw : ∀ j : Fin n, HasLaw (fun ω : Fin n → Fin d → ℝ => ω j i) (q.map fun y => y i)
      (Measure.pi fun _ : Fin n => q) := fun j => by
    refine ⟨(hmeas.comp (measurable_pi_apply j)).aemeasurable, ?_⟩
    rw [show (fun ω : Fin n → Fin d → ℝ => ω j i) = (fun y => y i) ∘ (fun ω => ω j) from rfl,
      ← Measure.map_map hmeas (measurable_pi_apply j),
      (measurePreserving_eval (fun _ : Fin n => q) j).map_eq]
  have hπ : MemLp id 2 (q.map fun y => y i) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hmeas.aemeasurable]
    exact hq i
  have hind : Pairwise fun j l => IndepFun (fun ω : Fin n → Fin d → ℝ => ω j i)
      (fun ω => ω l i) (Measure.pi fun _ : Fin n => q) := fun j l hjl =>
    (iIndepFun_pi (X := fun _ : Fin n => fun y : Fin d → ℝ => y i)
      (fun _ => hmeas.aemeasurable)).indepFun hjl
  have key := MonteCarlo.integral_sq_sampleMean_sub_of_hasLaw hn hπ hlaw hind
  have hm : ∫ x, x ∂(q.map fun y => y i) = ∫ y, y i ∂q := by
    exact integral_map hmeas.aemeasurable aestronglyMeasurable_id
  have hv : variance id (q.map fun y => y i) = variance (fun y : Fin d → ℝ => y i) q := by
    rw [variance_map aemeasurable_id hmeas.aemeasurable]; rfl
  rw [hm, hv] at key
  rw [← key]
  congr 1
  ext ω
  simp [empMean, MonteCarlo.sampleMean, Finset.sum_apply]


/-- Each coordinate of the empirical mean (minus a constant) is square-integrable under
`q^{⊗n}` when the coordinates are square-integrable under `q`. -/
theorem memLp_empMean_sub (q : Measure (Fin d → ℝ)) [IsProbabilityMeasure q] {n : ℕ}
    (hq : ∀ i, MemLp (fun y : Fin d → ℝ => y i) 2 q) (i : Fin d) (a : ℝ) :
    MemLp (fun ω : Fin n → Fin d → ℝ => empMean ω i - a) 2 (Measure.pi fun _ : Fin n => q) := by
  have hj : ∀ j : Fin n, MemLp (fun ω : Fin n → Fin d → ℝ => ω j i) 2
      (Measure.pi fun _ : Fin n => q) := fun j =>
    (hq i).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => q) j)
  have : (fun ω : Fin n → Fin d → ℝ => empMean ω i - a) =
      fun ω => (1 / (n : ℝ)) * ∑ j, ω j i - a := by
    ext ω; simp [empMean, Finset.sum_apply]
  rw [this]
  exact ((memLp_finsetSum _ fun j _ => hj j).const_mul _).sub (memLp_const a)

/-- **Bias–variance decomposition of the Monte Carlo mean.** For `n > 0` i.i.d. draws from `q`
(square-integrable coordinates) and any reference value `a`,
`E[(m̂ᵢ - a)²] = (∫ yᵢ dq - a)² + Var_q(yᵢ) / n`: squared bias plus variance over `n`. -/
theorem integral_sq_empMean_sub_biased {n : ℕ} (hn : 0 < n) (q : Measure (Fin d → ℝ))
    [IsProbabilityMeasure q] (hq : ∀ i, MemLp (fun y : Fin d → ℝ => y i) 2 q) (i : Fin d)
    (a : ℝ) :
    ∫ ω, (empMean ω i - a) ^ 2 ∂(Measure.pi fun _ : Fin n => q) =
      (∫ y, y i ∂q - a) ^ 2 + variance (fun y : Fin d → ℝ => y i) q / n := by
  set P := Measure.pi fun _ : Fin n => q
  set m' := ∫ y, y i ∂q
  have hL2 := memLp_empMean_sub q hq i (n := n) m'
  have hint1 : Integrable (fun ω : Fin n → Fin d → ℝ => empMean ω i - m') P :=
    hL2.integrable one_le_two
  have hmean : ∫ ω, (empMean ω i - m') ∂P = 0 := by
    have hmeas : Measurable (fun y : Fin d → ℝ => y i) := measurable_pi_apply i
    have hlaw : ∀ j : Fin n, HasLaw (fun ω : Fin n → Fin d → ℝ => ω j i) (q.map fun y => y i)
        P := fun j => by
      refine ⟨(hmeas.comp (measurable_pi_apply j)).aemeasurable, ?_⟩
      rw [show (fun ω : Fin n → Fin d → ℝ => ω j i) = (fun y => y i) ∘ (fun ω => ω j) from rfl,
        ← Measure.map_map hmeas (measurable_pi_apply j),
        (measurePreserving_eval (fun _ : Fin n => q) j).map_eq]
    have hπ : Integrable id (q.map fun y => y i) := by
      rw [integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable]
      exact (hq i).integrable one_le_two
    have key := MonteCarlo.integral_sampleMean_of_hasLaw hn hπ hlaw
    have hm : ∫ x, x ∂(q.map fun y => y i) = m' :=
      integral_map hmeas.aemeasurable aestronglyMeasurable_id
    have he : ∀ ω : Fin n → Fin d → ℝ,
        empMean ω i = MonteCarlo.sampleMean (fun j ω => ω j i) ω := fun ω => by
      simp [empMean, MonteCarlo.sampleMean, Finset.sum_apply]
    have hint0 : Integrable (fun ω => MonteCarlo.sampleMean (fun j ω => ω j i) ω) P :=
      (hint1.add (integrable_const m')).congr (ae_of_all _ fun ω => by simp [he])
    simp_rw [he]
    rw [integral_sub hint0 (integrable_const m'), key, hm]
    simp
  have hsq := integral_sq_empMean_sub hn q hq i
  have hint2 : Integrable (fun ω : Fin n → Fin d → ℝ => (empMean ω i - m') ^ 2) P :=
    hL2.integrable_sq
  have hexp : ∀ ω : Fin n → Fin d → ℝ, (empMean ω i - a) ^ 2 =
      (empMean ω i - m') ^ 2 + 2 * (m' - a) * (empMean ω i - m') + (m' - a) ^ 2 :=
    fun ω => by ring
  simp_rw [hexp]
  rw [integral_add (f := fun ω => (empMean ω i - m') ^ 2 + 2 * (m' - a) * (empMean ω i - m'))
      (g := fun _ => (m' - a) ^ 2) (hint2.add (hint1.const_mul _)) (integrable_const _),
    integral_add (f := fun ω => (empMean ω i - m') ^ 2)
      (g := fun ω => 2 * (m' - a) * (empMean ω i - m')) hint2 (hint1.const_mul _),
    integral_const_mul, hmean, hsq]
  simp
  ring

/-- **Per-step budget with an inexact sampler.** Draws from `q` (e.g. an approximate posterior
produced by an inner sampler) while the plug-in drift is centred at the exact mean `m`:
`∫ h ‖bx - (bx + c (m̂ - m))‖² / 4 dq^{⊗n} = (h c² / 4) ∑ᵢ ((∫ yᵢ dq - mᵢ)² + Var_q(yᵢ)/n)`. -/
theorem lintegral_monteCarlo_error_biased {n : ℕ} (hn : 0 < n) (q : Measure (Fin d → ℝ))
    [IsProbabilityMeasure q] (hq : ∀ i, MemLp (fun y : Fin d → ℝ => y i) 2 q)
    (m : Fin d → ℝ) (c : ℝ) (h : ℝ≥0) (bx : Fin d → ℝ) :
    ∫⁻ ω, ENNReal.ofReal (h * (∑ i, (bx i - (bx + c • (empMean ω - m)) i) ^ 2) / 4)
        ∂(Measure.pi fun _ : Fin n => q) =
      ENNReal.ofReal (h * c ^ 2 / 4 * ∑ i, ((∫ y, y i ∂q - m i) ^ 2 +
        variance (fun y : Fin d → ℝ => y i) q / n)) := by
  have hpt : ∀ ω : Fin n → Fin d → ℝ,
      (h : ℝ) * (∑ i, (bx i - (bx + c • (empMean ω - m)) i) ^ 2) / 4 =
        (h : ℝ) * c ^ 2 / 4 * ∑ i, (empMean ω i - m i) ^ 2 := fun ω => by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  have hint : ∀ i, Integrable (fun ω : Fin n → Fin d → ℝ => (empMean ω i - m i) ^ 2)
      (Measure.pi fun _ : Fin n => q) := fun i => (memLp_empMean_sub q hq i (m i)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_finsetSum _ fun i _ => hint i).const_mul _)
    (ae_of_all _ fun ω => by positivity), integral_const_mul,
    integral_finsetSum _ fun i _ => hint i]
  simp_rw [integral_sq_empMean_sub_biased hn q hq]


/-- **Per-step Monte Carlo budget.** For `n > 0` i.i.d. draws from `q` with mean `m` and
square-integrable coordinates, the plug-in drift `b̂(ω) = bx + c (m̂(ω) - m)` satisfies
`∫ h ‖bx - b̂(ω)‖² / 4 dq^{⊗n}(ω) = h c² (∑ᵢ Var_q(yᵢ)) / (4n)` (the zero-bias case of
`lintegral_monteCarlo_error_biased`). -/
theorem lintegral_monteCarlo_error {n : ℕ} (hn : 0 < n) (q : Measure (Fin d → ℝ))
    [IsProbabilityMeasure q] (hq : ∀ i, MemLp (fun y : Fin d → ℝ => y i) 2 q)
    (m : Fin d → ℝ) (hm : ∀ i, ∫ y, y i ∂q = m i) (c : ℝ) (h : ℝ≥0) (bx : Fin d → ℝ) :
    ∫⁻ ω, ENNReal.ofReal (h * (∑ i, (bx i - (bx + c • (empMean ω - m)) i) ^ 2) / 4)
        ∂(Measure.pi fun _ : Fin n => q) =
      ENNReal.ofReal (h * c ^ 2 * (∑ i, variance (fun y : Fin d → ℝ => y i) q) / (4 * n)) := by
  rw [lintegral_monteCarlo_error_biased hn q hq m c h bx]
  congr 1
  simp only [hm, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    ← Finset.sum_div]
  ring

end MonteCarlo

section MonteCarloChain

variable {d N : ℕ} {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {post : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (post k)]
  {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {c : ℕ → ℝ}
  {R : ℕ → Kernel (Fin d → ℝ) (Fin N → Fin d → ℝ)} [∀ k, IsMarkovKernel (R k)]
  {bhat : ℕ → (Fin d → ℝ) × (Fin N → Fin d → ℝ) → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-2 with an inexact inner sampler, KL form.** As `klDiv_monteCarloChain_le_sum`, but the
`N` i.i.d. draws come from an arbitrary Markov kernel `post k` (e.g. an approximate posterior
produced by an inner MCMC run) whose mean need **not** equal the exact mean `m k x` used to
centre the drift. Then
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫ (h k c k² / 4) B k(x) dν_k(x)` with
`B k x = ∑ᵢ ((mean of post k x)ᵢ - m k x i)² + ∑ᵢ Var_{post k x}(yᵢ) / N`
(squared inner-sampler bias plus Monte Carlo variance). -/
theorem klDiv_biasedMonteCarloChain_le_sum (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) + ∑ k ∈ range n, ∫⁻ x,
      ENNReal.ofReal (h k * c k ^ 2 / 4 * ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
        variance (fun y : Fin d → ℝ => y i) (post k x) / N)) ∂(ν k) := by
  refine (klDiv_randomEmChain_le_sum hμ hν n).trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => lintegral_congr fun x => ?_
  simp_rw [hbhat, hR]
  exact lintegral_monteCarlo_error_biased hN (post k x) (hq k x) (m k x) (c k) (h k) (b k x)

/-- **GI-2 with an inexact inner sampler, sample-size bound.** Under the hypotheses of
`klDiv_biasedMonteCarloChain_le_sum`, if `KL(ν 0 ‖ μ 0) < ∞` and the per-state budget `B k` is
`ν k`-integrable,
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k² / 8) ∫ B k dν_k)`, where `B k` is
squared bias plus variance over `N`. The bias term does not decrease with `N`: the number of
draws only controls the variance part. -/
theorem tvSup_biasedMonteCarloChain_le_sqrt (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * ∫ x, ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
        variance (fun y : Fin d → ℝ => y i) (post k x) / N) ∂(ν k)) := by
  set B : ℕ → (Fin d → ℝ) → ℝ := fun k x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
    variance (fun y : Fin d → ℝ => y i) (post k x) / N) with hBdef
  have hB0 : ∀ k x, 0 ≤ B k x := fun k x => Finset.sum_nonneg fun i _ =>
    add_nonneg (sq_nonneg _) (div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
  have := ErrorPropagation.isProbabilityMeasure_of_comp_succ hμ n
  have := ErrorPropagation.isProbabilityMeasure_of_comp_succ hν n
  refine (Pinsker.tvSup_le_sqrt_of_klDiv_le_add_sum (n := n) (ρ := ν)
    (e := fun k x => h k * c k ^ 2 / 4 * B k x) hKL0
    (fun k x => mul_nonneg (by positivity) (hB0 k x)) (fun k => (hB k).const_mul _)
    (klDiv_biasedMonteCarloChain_le_sum hN hR hq hbhat hμ hν n)).trans_eq ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

/-- **GI-2, Monte Carlo, KL form.** With `N > 0` exact i.i.d. draws from `post k x` at each step
(`hR`), square-integrable `post k x` with mean `m k x`, and the plug-in drift
`b̂ k (x, ω) = b k x + c k (m̂(ω) - m k x)`,
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫ h k c k² V k(x) / (4N) dν_k(x)`, with
`V k x = ∑ᵢ Var_{post k x}(yᵢ)`. -/
theorem klDiv_monteCarloChain_le_sum (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hm : ∀ k x i, ∫ y, y i ∂(post k x) = m k x i)
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) + ∑ k ∈ range n, ∫⁻ x,
      ENNReal.ofReal (h k * c k ^ 2 *
        (∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) / (4 * N)) ∂(ν k) := by
  refine (klDiv_randomEmChain_le_sum hμ hν n).trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => lintegral_congr fun x => ?_
  simp_rw [hbhat, hR]
  exact lintegral_monteCarlo_error hN (post k x) (hq k x) (m k x) (hm k x) (c k) (h k) (b k x)

/-- **GI-2, Monte Carlo sample-size bound.** Under the hypotheses of
`klDiv_monteCarloChain_le_sum`, if `KL(ν 0 ‖ μ 0) < ∞` and each `V k` is `ν k`-integrable,
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h k c k² / (8N) ∫ V k dν_k)`.
The Monte Carlo error enters inside one square root and decays like `1/N`. This is the
zero-bias case of `tvSup_biasedMonteCarloChain_le_sqrt`. -/
theorem tvSup_monteCarloChain_le_sqrt (hN : 0 < N)
    (hR : ∀ k x, R k x = Measure.pi fun _ : Fin N => post k x)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hm : ∀ k x i, ∫ y, y i ∂(post k x) = m k x i)
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (R k) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / (8 * N) *
        ∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) := by
  have hB : ∀ k x, ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N) =
      (∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) / N := fun k x => by
    simp [hm, Finset.sum_div]
  refine (tvSup_biasedMonteCarloChain_le_sqrt hN hR hq hbhat hμ hν n hKL0
    (fun k => by simp_rw [hB]; exact (hV k).div_const _)).trans_eq ?_
  simp_rw [hB, integral_div]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

end MonteCarloChain

end FormalizeSampling.GaussianIncrement
