module

public import FormalizeSampling.Samplers.GaussianIncrement
public import FormalizeSampling.Foundations.HeatKernelPi

/-!
# GI-1 in dimension `d`: isotropic Gaussian-increment (Euler–Maruyama / ULA) chains

The `d`-dimensional version, on the state space `Fin d → ℝ`, of the KL form of GI-1 proved in
one dimension in `FormalizeSampling/Samplers/GaussianIncrement.lean`: the drift (score)
estimation error of an isotropic Gaussian-increment chain is turned into a KL and a TV bound.

## Conventions

* `klDiv μ ν = KL(μ ‖ ν)` is Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`; `tvSup` is
  `FormalizeSampling.TotalVariation.tvSup`, normalised as `sup_A |μ(A) - ν(A)|`.
* Mathlib's `gaussianReal m v` is `N(m, v)` with **variance** `v : ℝ≥0`. The isotropic Gaussian
  `N(m, v I)` on `Fin d → ℝ` is the product measure `Measure.pi fun i => gaussianReal (m i) v`.
* Squared Euclidean norms are written as coordinate sums `∑ i, (m₁ i - m₂ i) ^ 2`; the norm
  `‖·‖` that Mathlib puts on `Fin d → ℝ` is the sup norm and is **not** used.
* The Euler–Maruyama (EM) kernel for `dX = b(X) dt + √2 dW` on `Fin d → ℝ` with step `h : ℝ≥0`
  and a measurable drift `b` is `emKernelPi h b hb x = N(x + h b(x), 2h I)`. With `b = ∇ log π`
  this is the unadjusted Langevin algorithm (ULA) for `π`.
* `κ ∘ₘ μ` is the law of one chain step from `μ` (`Measure.bind`).

## Main results

* Used from `Foundations`: the tensorisation of KL, `klDiv_pi_pi`
  (`Foundations/KLProduct.lean`), the isotropic mean shift `klDiv_pi_gaussianReal`:
  `KL(N(m₁, v I) ‖ N(m₂, v I)) = ∑ᵢ (m₁ i - m₂ i)² / (2v)` (`Foundations/GaussianKL.lean`), and
  the isotropic heat kernel `HeatKernelPi.heatKernelPi t x = N(x, t I)`
  (`Foundations/HeatKernelPi.lean`).
* `emKernelPi` (the heat kernel `heatKernelPi (2h)` started at `x + h b(x)`), `emKernelPi_apply`,
  `isMarkovKernel_emKernelPi`, and the one-step identity
  `klDiv_emKernelPi`: `KL(emKernelPi h s x ‖ emKernelPi h ŝ x) = h ∑ᵢ (s x i - ŝ x i)² / 4`.
* GI-1 (`d`-dimensional), for the exact chain `μ (k+1) = emKernelPi (h k) (s k) ∘ₘ μ k` and the
  algorithm `ν (k+1) = emKernelPi (h k) (ŝ k) ∘ₘ ν k` from probability laws:
  - `klDiv_emChainPi_le_sum`:
    `KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ h k ∑ᵢ (s k x i - ŝ k x i)² / 4 d(ν k)`;
  - `tvSup_emChainPi_le_sqrt_klDiv_sum`: `tvSup (ν n) (μ n) ≤ √(B / 2)` for that budget `B`;
  - `tvSup_emChainPi_le_sqrt_sum_integral_sq`:
    `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0) / 2 + ∑_{k<n} (h k / 8) ∫ ∑ᵢ (s k - ŝ k)ᵢ² d(ν k))`.
* Uniform drift errors `∑ᵢ (s k x i - ŝ k x i)² ≤ ε k` for all `x` (a real per-step KL budget
  `h k ε k / 4`): `klDiv_emChainPi_le_sum_of_forall_le`,
  `tvSup_emChainPi_le_sqrt_of_forall_le`
  (`tvSup (ν n) (μ n) ≤ √((KL(ν 0 ‖ μ 0) + ∑_{k<n} h k ε k / 4) / 2)`) and, for summable
  `h k ε k`, the bound uniform in `n` `tvSup_emChainPi_le_sqrt_tsum_of_forall_le`.

Registry: GI-1 (score-error theorem for Gaussian-increment chains), multivariate isotropic case.

## Not proved here

* Non-isotropic or state-dependent diffusion matrices, and Gaussians with different covariances.
* That the one-dimensional results are the case `d = 1` (they are proved separately).
* Any comparison with a continuous-time diffusion, and any bound on the score error itself.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory InformationTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling
namespace GaussianIncrement

open TotalVariation ErrorPropagation HeatKernelPi

/-! ### The `d`-dimensional EM kernel -/

variable {d : ℕ}

/-- The **isotropic Euler–Maruyama (EM) kernel** on `Fin d → ℝ` for `dX = b(X) dt + √2 dW` with
step `h : ℝ≥0` and a measurable drift (score) field `b`:
`emKernelPi h b hb x = N(x + h b(x), 2h I) = ⊗ᵢ N(x i + h b(x) i, 2h)`, the law of
`x + h b(x) + √(2h) Z` with `Z ∼ N(0, I)`, i.e. the heat kernel `heatKernelPi (2h)` started at
`x + h b(x)`. For `b = ∇ log π` this is one step of ULA for `π`. For `h = 0` it is the identity
kernel `x ↦ δₓ`. -/
noncomputable def emKernelPi (h : ℝ≥0) (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (heatKernelPi (2 * h)).comap (fun x i => x i + h * b x i) (by fun_prop)

/-- Evaluation of the isotropic EM kernel:
`emKernelPi h b hb x = ⊗ᵢ N(x i + h b(x) i, 2h) = N(x + h b(x), 2h I)`. -/
theorem emKernelPi_apply (h : ℝ≥0) {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b)
    (x : Fin d → ℝ) :
    emKernelPi h b hb x = Measure.pi fun i => gaussianReal (x i + h * b x i) (2 * h) := rfl

/-- The isotropic EM kernel is a Markov kernel (a product of Gaussian probability measures), for
every step `h` and measurable drift `b`. -/
instance isMarkovKernel_emKernelPi (h : ℝ≥0) {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : Measurable b) : IsMarkovKernel (emKernelPi h b hb) :=
  ⟨fun x => by rw [emKernelPi_apply]; infer_instance⟩

/-- **One-step oracle error of the isotropic EM kernel in KL.** For every step `h : ℝ≥0`,
measurable drifts `s ŝ` on `Fin d → ℝ` and state `x`,
`KL(emKernelPi h s x ‖ emKernelPi h ŝ x) = h ∑ᵢ (s x i - ŝ x i)² / 4 = h |s(x) - ŝ(x)|² / 4`
(Euclidean norm; Mathlib's `klDiv`). This holds also for `h = 0`, where both kernels are `δₓ`. -/
theorem klDiv_emKernelPi (h : ℝ≥0) {s ŝ : (Fin d → ℝ) → Fin d → ℝ} (hs : Measurable s)
    (hŝ : Measurable ŝ) (x : Fin d → ℝ) :
    klDiv (emKernelPi h s hs x) (emKernelPi h ŝ hŝ x) =
      ENNReal.ofReal (h * (∑ i, (s x i - ŝ x i) ^ 2) / 4) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [emKernelPi_apply]
  have hh' : 0 < (h : ℝ) := by positivity
  rw [emKernelPi_apply, emKernelPi_apply,
    klDiv_pi_gaussianReal _ _ (mul_ne_zero two_ne_zero hh)]
  congr 1
  rw [NNReal.coe_mul, NNReal.coe_ofNat]
  have : ∀ i, x i + h * s x i - (x i + h * ŝ x i) = h * (s x i - ŝ x i) := fun i => by ring
  simp_rw [this, mul_pow, ← mul_sum]
  field_simp
  ring

/-! ### GI-1 in dimension `d`: KL telescoping and a single Pinsker step -/

/-- The state space `Fin d → ℝ` is countably generated, as required by the KL chain rule
`KL.klDiv_chain_le_sum`. -/
example : MeasurableSpace.CountableOrCountablyGenerated (Fin d → ℝ) (Fin d → ℝ) :=
  inferInstance

variable {h : ℕ → ℝ≥0} {s ŝ : ℕ → (Fin d → ℝ) → Fin d → ℝ} {hs : ∀ k, Measurable (s k)}
  {hŝ : ∀ k, Measurable (ŝ k)} {μ ν : ℕ → Measure (Fin d → ℝ)}

/-- **GI-1 (`d`-dimensional), KL form: score-error theorem for isotropic Gaussian-increment
chains.** Let `h k : ℝ≥0` be steps, `s k` exact and `ŝ k` estimated measurable drift (score)
fields on `Fin d → ℝ`, `μ` the exact-score EM chain `μ (k+1) = emKernelPi (h k) (s k) ∘ₘ μ k`
and `ν` the estimated-score EM chain `ν (k+1) = emKernelPi (h k) (ŝ k) ∘ₘ ν k`, started from
probability laws `μ 0`, `ν 0`. Then
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ x, h k ∑ᵢ (s k x i - ŝ k x i)² / 4 ∂(ν k)`,
i.e. the squared Euclidean drift error `h k |s k - ŝ k|² / 4` averaged under the
**algorithm's** laws `ν k`. Direction: KL of the algorithm's law from the exact chain's law.
Exchanging the chains bounds `KL(μ n ‖ ν n)` with errors averaged under `μ k`. No integrability
is needed: both sides live in `ℝ≥0∞`. -/
theorem klDiv_emChainPi_le_sum [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi (h k) (ŝ k) (hŝ k) ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n,
        ∫⁻ x, ENNReal.ofReal (h k * (∑ i, (s k x i - ŝ k x i) ^ 2) / 4) ∂(ν k) := by
  have : ∀ k, IsFiniteMeasure (μ k) := fun k =>
    have := isProbabilityMeasure_of_comp_succ hμ k; inferInstance
  have : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    have := isProbabilityMeasure_of_comp_succ hν k; inferInstance
  refine (KL.klDiv_chain_le_sum (fun k => emKernelPi (h k) (s k) (hs k))
    (fun k => emKernelPi (h k) (ŝ k) (hŝ k)) μ ν hμ hν n).trans_eq ?_
  congr 1
  refine sum_congr rfl fun k _ => lintegral_congr fun x => ?_
  have hsym : ∀ i, (ŝ k x i - s k x i) ^ 2 = (s k x i - ŝ k x i) ^ 2 := fun i => by ring
  simp only [klDiv_emKernelPi, hsym]

/-- **GI-1 (`d`-dimensional), TV form: one Pinsker step at the end.** Same chains as
`klDiv_emChainPi_le_sum`. If the KL budget
`B = KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ h k ∑ᵢ (s k x i - ŝ k x i)² / 4 d(ν k)` (errors averaged under the
algorithm's laws `ν k`) is finite, then `tvSup (ν n) (μ n) ≤ √(B / 2)`. -/
theorem tvSup_emChainPi_le_sqrt_klDiv_sum [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi (h k) (ŝ k) (hŝ k) ∘ₘ ν k) (n : ℕ)
    (hB : klDiv (ν 0) (μ 0) + ∑ k ∈ range n,
      ∫⁻ x, ENNReal.ofReal (h k * (∑ i, (s k x i - ŝ k x i) ^ 2) / 4) ∂(ν k) ≠ ∞) :
    tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0) + ∑ k ∈ range n,
      ∫⁻ x, ENNReal.ofReal (h k * (∑ i, (s k x i - ŝ k x i) ^ 2) / 4) ∂(ν k)).toReal / 2) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  have hKL := klDiv_emChainPi_le_sum hμ hν n
  refine (Pinsker.tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top hB hKL)).trans
    (Real.sqrt_le_sqrt ?_)
  gcongr

/-- **GI-1 (`d`-dimensional), TV form with `L²` score errors.** Same chains as
`klDiv_emChainPi_le_sum`. If `KL(ν 0 ‖ μ 0) < ∞` and each squared Euclidean drift error
`∑ᵢ (s k x i - ŝ k x i)²` is integrable under the algorithm's law `ν k`, then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0) / 2 + ∑_{k<n} (h k / 8) ∫ ∑ᵢ (s k x i - ŝ k x i)² d(ν k))`,
the errors being averaged under the **algorithm's** laws `ν k`. -/
theorem tvSup_emChainPi_le_sqrt_sum_integral_sq [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi (h k) (ŝ k) (hŝ k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hint : ∀ k, Integrable (fun x => ∑ i, (s k x i - ŝ k x i) ^ 2) (ν k)) :
    tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k / 8 * ∫ x, ∑ i, (s k x i - ŝ k x i) ^ 2 ∂(ν k)) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  refine (Pinsker.tvSup_le_sqrt_of_klDiv_le_add_sum (n := n) hKL0 (fun k x => by positivity)
    (fun k => (hint k).const_mul (h k / 4 : ℝ))
    ((klDiv_emChainPi_le_sum hμ hν n).trans_eq ?_)).trans_eq ?_
  · congr 1
    refine sum_congr rfl fun k _ => lintegral_congr fun x => ?_
    congr 1; ring
  · congr 2
    refine sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; ring

/-! ### Uniform drift errors: a real per-step KL budget -/

/-- **GI-1 (`d`-dimensional) with uniform drift errors, KL form.** Same chains as
`klDiv_emChainPi_le_sum`. If at every step `k` the squared Euclidean drift error is bounded
uniformly in the state, `∑ᵢ (s k x i - ŝ k x i)² ≤ ε k` for all `x`, then
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} h k ε k / 4`: each one-step KL
`h k |s k x - ŝ k x|² / 4` (`klDiv_emKernelPi`) is at most `h k ε k / 4`, whatever the law. -/
theorem klDiv_emChainPi_le_sum_of_forall_le [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi (h k) (ŝ k) (hŝ k) ∘ₘ ν k) {ε : ℕ → ℝ}
    (hε : ∀ k x, ∑ i, (s k x i - ŝ k x i) ^ 2 ≤ ε k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤
      klDiv (ν 0) (μ 0) + ∑ k ∈ range n, ENNReal.ofReal (h k * ε k / 4) := by
  refine (klDiv_emChainPi_le_sum hμ hν n).trans ?_
  gcongr with k hk
  have := isProbabilityMeasure_of_comp_succ hν k
  calc ∫⁻ x, ENNReal.ofReal (h k * (∑ i, (s k x i - ŝ k x i) ^ 2) / 4) ∂(ν k)
      ≤ ∫⁻ _, ENNReal.ofReal (h k * ε k / 4) ∂(ν k) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by gcongr; exact hε k x)
    _ = ENNReal.ofReal (h k * ε k / 4) := by simp

/-- **GI-1 (`d`-dimensional) with uniform drift errors, TV form.** Same chains and hypothesis
as `klDiv_emChainPi_le_sum_of_forall_le`. If `KL(ν 0 ‖ μ 0) < ∞`, then
`tvSup (ν n) (μ n) ≤ √((KL(ν 0 ‖ μ 0) + ∑_{k<n} h k ε k / 4) / 2)`. For instance, from a common
start (`ν 0 = μ 0`) with Euclidean drift error at most `E` at every step,
`tvSup (ν n) (μ n) ≤ √(E² ∑_{k<n} h k / 8)`. -/
theorem tvSup_emChainPi_le_sqrt_of_forall_le [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi (h k) (ŝ k) (hŝ k) ∘ₘ ν k)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞) {ε : ℕ → ℝ}
    (hε : ∀ k x, ∑ i, (s k x i - ŝ k x i) ^ 2 ≤ ε k) (n : ℕ) :
    tvSup (ν n) (μ n) ≤
      √(((klDiv (ν 0) (μ 0)).toReal + ∑ k ∈ range n, h k * ε k / 4) / 2) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  refine Pinsker.tvSup_le_sqrt_of_klDiv_le_add_sum_ofReal hKL0 (fun k => ?_)
    (klDiv_emChainPi_le_sum_of_forall_le hμ hν hε n)
  have := (sum_nonneg fun i _ => sq_nonneg (s k 0 i - ŝ k 0 i)).trans (hε k 0)
  positivity

/-- **GI-1 (`d`-dimensional) with summable uniform drift errors.** Same chains and hypothesis as
`klDiv_emChainPi_le_sum_of_forall_le`. If `KL(ν 0 ‖ μ 0) < ∞` and `∑_k h k ε k < ∞`, then for
every `n`, `tvSup (ν n) (μ n) ≤ √((KL(ν 0 ‖ μ 0) + (∑' k, h k ε k) / 4) / 2)`, a bound uniform
in the number of steps (e.g. for step sizes or errors decaying fast enough). -/
theorem tvSup_emChainPi_le_sqrt_tsum_of_forall_le [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernelPi (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi (h k) (ŝ k) (hŝ k) ∘ₘ ν k)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞) {ε : ℕ → ℝ}
    (hε : ∀ k x, ∑ i, (s k x i - ŝ k x i) ^ 2 ≤ ε k)
    (hsum : Summable fun k => (h k : ℝ) * ε k) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ √(((klDiv (ν 0) (μ 0)).toReal + (∑' k, (h k : ℝ) * ε k) / 4) / 2) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  have hc : ∀ k, 0 ≤ (h k : ℝ) * ε k / 4 := fun k => by
    have := (sum_nonneg fun i _ => sq_nonneg (s k 0 i - ŝ k 0 i)).trans (hε k 0)
    positivity
  rw [← tsum_div_const]
  exact Pinsker.tvSup_le_sqrt_of_klDiv_le_add_tsum hKL0 hc (hsum.div_const 4)
    (klDiv_emChainPi_le_sum_of_forall_le hμ hν hε n)

end GaussianIncrement
end FormalizeSampling
