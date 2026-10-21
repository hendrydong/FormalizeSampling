module

public import FormalizeSampling.Samplers.RandomScoreOracle
public import FormalizeSampling.Kernels.KernelPi
public import FormalizeSampling.Foundations.HeatKernelPi

/-!
# GI-2 with a state-dependent posterior kernel

Status: **Verified**.

The Monte Carlo theorems of `Samplers/RandomScoreOracle.lean` take the draw kernel `R k` as a
parameter together with the hypothesis `hR : ∀ k x, R k x = (post k x)^{⊗N}`. Mathlib v4.35
has no product of kernels, so before `Kernels/KernelPi.lean` such an `R` could only be built for
state-independent `post`. With `R k := KernelPi.piConst N (post k)` the hypothesis `hR` holds by
definition (`KernelPi.piConst_apply`) for every Markov kernel `post k`, in particular for
state-dependent posteriors.

## Main results

* `tvSup_piConstMonteCarloChain_le_sqrt`: GI-2 Monte Carlo sample-size bound
  `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² /(8N) ∫ V_k dν_k)` for `N`
  i.i.d. draws from an arbitrary Markov kernel `post k` (no `hR` hypothesis).
* `tvSup_piConstBiasedMonteCarloChain_le_sqrt`: the inexact-inner-sampler version (squared
  bias plus variance over `N`), again with no `hR` hypothesis.
* Non-vacuity, state-dependent posterior `post k = heatKernelPi (t k)`, i.e.
  `post k x = N(x, t_k I)`:
  `memLp_coord_heatKernelPi`, `integral_coord_heatKernelPi`, `variance_coord_heatKernelPi`
  (square-integrable, mean `x`, coordinate variance `t_k`), `measurable_plugInDrift`, and
  `tvSup_heatKernelPiMonteCarloChain_le_sqrt`: with the plug-in drift
  `b̂ k (x, ω) = b k x + c k (m̂(ω) - x)` and all hypotheses discharged except the chain
  recursions and `KL(ν 0 ‖ μ 0) < ∞`,
  `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² d t_k /(8N))`.

The KL, averaged and coupling corollaries in `Samplers/RandomScoreOracleInner.lean` take the same
`hR`; it is discharged for `R k := KernelPi.piConst N (post k)` by
`fun k x => KernelPi.piConst_apply N (post k) x`.

## Not proved here

* Draws that are not independent given the state (e.g. successive outputs of one inner MCMC
  run) are not covered: `R k x` is exactly the product `(post k x)^{⊗N}`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.GaussianIncrement

open KernelPi

section MonteCarloKernel

variable {d N : ℕ} {h : ℕ → ℝ≥0} {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hb : ∀ k, Measurable (b k)}
  {post : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)} [∀ k, IsMarkovKernel (post k)]
  {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} {c : ℕ → ℝ}
  {bhat : ℕ → (Fin d → ℝ) × (Fin N → Fin d → ℝ) → Fin d → ℝ} {hbh : ∀ k, Measurable (bhat k)}
  {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-2, Monte Carlo sample-size bound, state-dependent posterior.** Let `post k` be any
Markov kernel (the law of the draws may depend on the current state `x`), and let the
algorithm draw `ω ~ (post k x)^{⊗N}` through the product kernel `piConst N (post k)`. If
`post k x` is square-integrable with mean `m k x`, the drift is the plug-in
`b̂ k (x, ω) = b k x + c k (m̂(ω) - m k x)`, `KL(ν 0 ‖ μ 0) < ∞` and `V k` is `ν k`-integrable,
then `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h k c k² / (8N) ∫ V k dν_k)`, with
`V k x = ∑ᵢ Var_{post k x}(yᵢ)`. This is `tvSup_monteCarloChain_le_sqrt` with its product
hypothesis `hR` discharged. -/
theorem tvSup_piConstMonteCarloChain_le_sqrt (hN : 0 < N)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hm : ∀ k x i, ∫ y, y i ∂(post k x) = m k x i)
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) =
      randomEmKernel (h k) (piConst N (post k)) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hV : ∀ k, Integrable
      (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / (8 * N) *
        ∫ x, ∑ i, variance (fun y : Fin d → ℝ => y i) (post k x) ∂(ν k)) :=
  tvSup_monteCarloChain_le_sqrt (hb := hb) (hbh := hbh)
    (R := fun k => piConst N (post k)) hN (fun k x => piConst_apply N (post k) x) hq hm hbhat
    hμ hν n hKL0 hV

/-- **GI-2 with an inexact inner sampler, state-dependent posterior.** As
`tvSup_biasedMonteCarloChain_le_sqrt`, with the draws `ω ~ (post k x)^{⊗N}` produced by the
product kernel `piConst N (post k)` of an arbitrary Markov kernel `post k` (whose mean need not
be `m k x`), so the product hypothesis `hR` is gone:
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h k c k² / 8) ∫ B k dν_k)`, with
`B k x = ∑ᵢ ((mean of post k x)ᵢ - m k x i)² + ∑ᵢ Var_{post k x}(yᵢ) / N`. -/
theorem tvSup_piConstBiasedMonteCarloChain_le_sqrt (hN : 0 < N)
    (hq : ∀ k x i, MemLp (fun y : Fin d → ℝ => y i) 2 (post k x))
    (hbhat : ∀ k x ω, bhat k (x, ω) = b k x + c k • (empMean ω - m k x))
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) =
      randomEmKernel (h k) (piConst N (post k)) (bhat k) (hbh k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hB : ∀ k, Integrable (fun x => ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
      variance (fun y : Fin d → ℝ => y i) (post k x) / N)) (ν k)) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 / 8 * ∫ x, ∑ i, ((∫ y, y i ∂(post k x) - m k x i) ^ 2 +
        variance (fun y : Fin d → ℝ => y i) (post k x) / N) ∂(ν k)) :=
  tvSup_biasedMonteCarloChain_le_sqrt (hb := hb) (hbh := hbh)
    (R := fun k => piConst N (post k)) hN (fun k x => piConst_apply N (post k) x) hq hbhat
    hμ hν n hKL0 hB

end MonteCarloKernel

section HeatPosterior

open HeatKernelPi

variable {d : ℕ}

/-- The coordinates of the Gaussian kernel `heatKernelPi t x = N(x, t I)` are
square-integrable. -/
theorem memLp_coord_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) (i : Fin d) :
    MemLp (fun y : Fin d → ℝ => y i) 2 (heatKernelPi t x) := by
  rw [heatKernelPi_apply]
  exact (memLp_id_gaussianReal 2).comp_measurePreserving
    (measurePreserving_eval (fun j => gaussianReal (x j) t) i)

/-- The mean of `heatKernelPi t x = N(x, t I)` is `x`: `∫ yᵢ d(heatKernelPi t x) = xᵢ`. -/
theorem integral_coord_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) (i : Fin d) :
    ∫ y, y i ∂(heatKernelPi t x) = x i := by
  have hmp := measurePreserving_eval (fun j => gaussianReal (x j) t) i
  have e := integral_map (f := id) (measurable_pi_apply i).aemeasurable
    aestronglyMeasurable_id (μ := Measure.pi fun j => gaussianReal (x j) t)
  have hm : (Measure.pi fun j => gaussianReal (x j) t).map (fun y : Fin d → ℝ => y i) =
      gaussianReal (x i) t := hmp.map_eq
  rw [hm] at e
  rw [heatKernelPi_apply]
  exact e.symm.trans integral_id_gaussianReal

/-- The coordinate variances of `heatKernelPi t x = N(x, t I)` are `t`. -/
theorem variance_coord_heatKernelPi (t : ℝ≥0) (x : Fin d → ℝ) (i : Fin d) :
    variance (fun y : Fin d → ℝ => y i) (heatKernelPi t x) = t := by
  have hmp := measurePreserving_eval (fun j => gaussianReal (x j) t) i
  have := variance_map (X := id) (μ := Measure.pi fun j => gaussianReal (x j) t)
    (Y := fun y : Fin d → ℝ => y i) measurable_id.aemeasurable
    (measurable_pi_apply i).aemeasurable
  have hm : (Measure.pi fun j => gaussianReal (x j) t).map (fun y : Fin d → ℝ => y i) =
      gaussianReal (x i) t := hmp.map_eq
  rw [hm, variance_id_gaussianReal] at this
  rw [heatKernelPi_apply, this]
  rfl

/-- The plug-in drift `(x, ω) ↦ b x + c (m̂(ω) - x)` (empirical mean `m̂` of `N` draws, centred
at the state `x`) is measurable when `b` is. -/
theorem measurable_plugInDrift {N : ℕ} {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b)
    (c : ℝ) :
    Measurable fun p : (Fin d → ℝ) × (Fin N → Fin d → ℝ) => b p.1 + c • (empMean p.2 - p.1) := by
  unfold empMean
  fun_prop

/-- **GI-2 non-vacuity: Gaussian posterior centred at the state.** Take the state-dependent
posterior `post k x = heatKernelPi (t k) x = N(x, t_k I)`, `N > 0` i.i.d. draws
`ω ~ (post k x)^{⊗N}` via `piConst`, and the plug-in drift `b̂ k (x, ω) = b k x + c k (m̂(ω) - x)`
(centred at the exact posterior mean `x`). For any measurable exact drifts `b k`, the
exact-drift chain `μ` and the Monte Carlo chain `ν` started from probability measures with
`KL(ν 0 ‖ μ 0) < ∞` satisfy
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} h_k c_k² d t_k / (8N))`.
All moment and integrability hypotheses of `tvSup_piConstMonteCarloChain_le_sqrt` are
discharged. -/
theorem tvSup_heatKernelPiMonteCarloChain_le_sqrt {N : ℕ} (hN : 0 < N) {h : ℕ → ℝ≥0}
    {b : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hb : ∀ k, Measurable (b k)) (c : ℕ → ℝ)
    (t : ℕ → ℝ≥0) {μ ν : ℕ → Measure (Fin d → ℝ)}
    [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (b k) (hb k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = randomEmKernel (h k) (piConst N (heatKernelPi (t k)))
      (fun p : (Fin d → ℝ) × (Fin N → Fin d → ℝ) => b k p.1 + c k • (empMean p.2 - p.1))
      (measurable_plugInDrift (hb k) (c k)) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞) :
    TotalVariation.tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k * c k ^ 2 * (d * t k) / (8 * N)) := by
  have hprob := ErrorPropagation.isProbabilityMeasure_of_comp_succ hν
  have hV : ∀ k, (fun x => ∑ i, variance (fun y : Fin d → ℝ => y i)
      (heatKernelPi (t k) x)) = fun _ => (d : ℝ) * t k := fun k => by
    funext x
    simp [variance_coord_heatKernelPi]
  refine (tvSup_piConstMonteCarloChain_le_sqrt (hb := hb) (m := fun _ x => x)
    (post := fun k => heatKernelPi (t k)) hN (fun k x i => memLp_coord_heatKernelPi _ x i)
    (fun k x i => integral_coord_heatKernelPi _ x i) (fun _ _ _ => rfl) hμ hν n hKL0
    (fun k => by rw [hV k]; exact integrable_const _)).trans_eq ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hprob k
  rw [hV k, integral_const, probReal_univ, one_smul]
  ring

end HeatPosterior

end FormalizeSampling.GaussianIncrement
