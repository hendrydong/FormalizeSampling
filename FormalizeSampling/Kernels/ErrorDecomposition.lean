module

public import FormalizeSampling.Kernels.ErrorPropagation

/-!
# Separating discretisation, oracle and mixing errors in total variation

Two composable error decompositions for Markov chains on a general measurable space `α`, in total
variation (TV, `FormalizeSampling.TotalVariation.tvSup`, normalised as `sup_A |μ(A) - ν(A)|`).

## Part 1 (KR-1): three-chain separation

Three families of Markov kernels indexed by the step `k`:

* `K k`, the **exact** kernels (e.g. the transition law of a diffusion over one step, or the
  exact reverse transition; never constructed here, they are arbitrary Markov kernels);
* `D k`, the **ideal discretised** kernels (the numerical scheme run with the exact score/drift);
* `I k`, the **implemented** kernels (the same scheme with the estimated score/oracle).

With the exact chain `μ (k+1) = K k ∘ₘ μ k` and the implemented chain `ν (k+1) = I k ∘ₘ ν k`
(and, when used, the ideal discretised chain `δ (k+1) = D k ∘ₘ δ k`), the final TV error splits as
`initial mismatch + ∑_k disc_k + ∑_k oracle_k`, where `disc_k` bounds `tvSup (D k x) (K k x)` and
`oracle_k` bounds `tvSup (I k x) (D k x)`:

* `tvSup_le_sum_disc_add_sum_oracle`: uniform bounds;
* `tvSup_le_sum_integral_disc_add_oracle`: measurable (integrable) majorants averaged under the
  **implemented** chain's law `ν k`;
* `tvSup_le_sum_integral_disc_add_oracle_exact`: majorants averaged under the **exact** chain's
  law `μ k`;
* `tvSup_le_three_chain`: initial mismatches `tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0)`, the
  discretisation majorant averaged under the **ideal discretised** chain's law `δ k` and the oracle
  majorant averaged under the **implemented** chain's law `ν k`;
* `tvSup_le_three_chain_exact`: the oracle majorant averaged under `δ k` and the discretisation
  majorant averaged under the **exact** chain's law `μ k`.

Instantiation of the oracle part with Euler–Maruyama kernels `D k = emKernel (h k) (s k)`,
`I k = emKernel (h k) (ŝ k)` (`FormalizeSampling.GaussianIncrement`, GI-1; these theorems are in
`Samplers/GaussianIncrement.lean`, in this namespace): `tvSup_le_disc_add_emOracle` (uniform
discretisation error, `L¹` score error under the algorithm's law),
`tvSup_le_disc_add_emOracle_sq_exact` (both errors under the exact chain's law, `L²` score
error: the usual score-matching loss along the exact process) and `tvSup_le_three_chain_em`
(discretisation error along the ideal EM chain, `L²` score error under the algorithm's law).

## Part 2 (Conditional): TV variant of the SPS outer framework

Exact Markov kernels `P k` (target `π`, a probability measure), inexact Markov kernels `P' k` and
the inexact chain `ν (k+1) = P' k ∘ₘ ν k` from a probability law `ν 0`, with uniform inexactness
`tvSup (P' k x) (P k x) ≤ ε k`.

**Recommended statement (along the algorithm's own laws).**
`tvSup_le_of_contraction_along`: under the named hypothesis `hAlong`,
`∀ k < K, tvSup (P k ∘ₘ ν k) π ≤ ρ tvSup (ν k) π` with `0 ≤ ρ` (one exact step applied to the
algorithm's current law contracts TV towards `π`),
`tvSup (ν K) π ≤ ρ^K tvSup (ν 0) π + ∑_{k<K} ρ^(K-1-k) ε k`. Law-averaged form with integrable
majorants `e k` under `ν k`: `tvSup_le_of_contraction_along_integral`. Proximal corollary (exact
forward step, inexact RGO `R' k` with `tvSup (R' k y) (rgoKernel f (η k) y) ≤ ε k`):
`tvSup_inexactProx_le_along` (in `Samplers/ProximalInexact.lean`, in this namespace).
`hAlong` is the TV analogue of the KL contraction along the chain that the LSI argument of SPS
(Lemma E.3) provides; it is a named hypothesis, not derived from LSI.

Facts about `hAlong` (nonvacuity and limits):

* `contraction_along_of_tvContraction`: the uniform hypothesis below implies it, so the
  along-the-chain theorems generalise the uniform ones (which are proved from them);
* `contraction_along_of_eq_target`: it holds with `ρ = 0` (indeed every `ρ`) along a stationary
  chain `ν k = π` of kernels leaving `π` invariant;
* `exists_contraction_along_lt_one`: at a fixed horizon `K` it only constrains the `K` laws
  `ν 0, …, ν (K-1)`; strict one-step decrease of TV along them already gives some `ρ < 1`. The
  quantitative content is therefore a `ρ < 1` independent of `K`, which LSI supplies in **KL**
  (`KL(νP ‖ π) ≤ KL(ν ‖ π)/(1 + αη)²` for every finite-KL law). In KL such a bound does not force
  uniform ergodicity since `KL(δₓ ‖ π) = ∞` for atomless `π`, whereas `tvSup δₓ π ≤ 1`; and
  turning the KL rate into TV needs Pinsker's inequality (`Foundations/Pinsker.lean`, not in
  Mathlib) and yields a KL-to-TV bound `tvSup (νP) π ≤ √(KL(ν ‖ π)/2)/(1 + αη)`, not
  `hAlong` itself;
* non-uniform witness: the reset kernel `resetKernel hA π` (`π` from `x ∈ A`, `δₓ` from
  `x ∉ A`) satisfies `hAlong` with `ρ = 0` along every chain of laws carried by `A`
  (`contraction_along_resetKernel`, `resetKernel_chain_compl_eq_zero`, including chains with
  `ν 0 ≠ π`), but for `π` carried by `A` and `Aᶜ` nonempty it is **not** uniformly ergodic:
  `TVContraction (resetKernel hA π) π ρ` fails for every `ρ < 1` (`not_tvContraction_resetKernel`).

**Uniform version (only for uniformly ergodic kernels).** `TVContraction P π ρ` is a named
hypothesis: `∀ μ` probability, `tvSup (P ∘ₘ μ) π ≤ ρ tvSup μ π`. Under it for every `P k` (with
`0 ≤ ρ`), the same bound holds (`tvSup_le_of_tvContraction`; law-averaged form
`tvSup_le_of_tvContraction_integral`; proximal form `tvSup_inexactProx_le`). Kernel-level
corollary (`tvSup_comp_kernel_apply_le`): an inner oracle `R'` that is `ε`-close to the exact RGO
`R` uniformly makes `R' ∘ₖ F` `ε`-close to `R ∘ₖ F` for the same forward step `F`.

Facts about `TVContraction` (nonvacuity and limits):

* `TVContraction.comp_eq`: it **implies** invariance `P ∘ₘ π = π`, so invariance is not an extra
  hypothesis;
* `tvContraction_one_of_comp_eq`: `ρ = 1` holds for every Markov `P` with invariant `π`
  (from KR-1, `tvSup_comp_le`), e.g. the exact proximal kernel (`tvContraction_proxKernel`);
* `tvContraction_const` and `TVContraction.mono`: the independent sampler `x ↦ π` satisfies it
  with every `ρ ≥ 0`, so the hypotheses of the uniform theorem are jointly satisfiable with `ρ < 1`;
* `TVContraction.tvSup_apply_le`: it forces the **uniform** bound `tvSup (P x) π ≤ ρ` for every
  starting point `x` (take `μ = δₓ`). This is a Doeblin/Dobrushin-type uniform-ergodicity
  condition. **Caveat:** for the exact proximal sampler on `ℝ` with, e.g., a Gaussian target, the
  law after one step from `x` drifts away from `π` as `|x| → ∞`, so `TVContraction` can then only
  hold with `ρ ≥ 1` (expected; this asymptotic is not formalised), and the uniform theorems with
  `ρ < 1` are then expected to be vacuous for such proximal samplers (not formalised: no lemma
  here shows that `TVContraction` fails for `proxKernel`). This caveat concerns the proximal
  sampler; it is not a claim about every kernel with unbounded support, since uniformly ergodic
  kernels can satisfy `TVContraction` with `ρ < 1` when `π` has unbounded support (e.g. the
  independent sampler above with a Gaussian `π`). The LSI input of the SPS paper (Lemma E.3,
  Chen et al. 2022) is a **KL** contraction `KL(νP ‖ π) ≤ KL(ν ‖ π)/(1 + α η)²`, which is a
  different, non-uniform statement; it does not by itself give `TVContraction` with `ρ < 1`.
  This is why the statement here restricts the contraction to the algorithm's own laws
  (`hAlong` above); proving `hAlong` with a `K`-independent `ρ < 1` for the proximal sampler (warm
  start / finite KL, or the KL route) is not done here.

## Relation to the papers

* SPS (Huang et al., ICML 2024), Theorem 3.1 / Lemma B.5 and RTK Lemma 3.2 / rdMC Eq. (15)/(19)
  telescope **KL** with the chain rule (SPS Lemma B.1) and apply Pinsker **once**:
  `TV(p̂_K, p_K) ≤ √(½ ∑_k δ_k)` for per-step KL oracle errors `δ_k` (SPS Eq. (7)). The TV route
  here (per-step TV errors `ε_k`, e.g. `ε_k = √(δ_k / 2)` from a per-step Pinsker,
  `Pinsker.tvSup_le_sqrt_klDiv`, not used here) gives `∑_k ε_k`, valid but looser by up to a
  factor `√K`; with the paper's choice `δ_k = Θ(ε²/K)` it yields `Θ(√K ε)` instead of `Θ(ε)`.
* SPS Theorem 3.1 bounds the initialisation term by
  `√((1+L²)d/(4α_*)) ∏(1 + α_* η_i)^{-1}`. That form is not formalised here: the initial term
  here is the actual initial TV `ρ^K tvSup (ν 0) π`, with the contraction packaged in the
  named hypothesis.
* Neither the mini-batch error (SPS Lemma B.4) nor the inner-sampler accuracy (SPS (H3), Lemmas
  C.1–C.7) is proved; the oracle accuracy enters as the uniform TV bound `ε k`.
* rdMC/RS-DMC Lemma 7 separate discretisation and score errors inside the Girsanov integrand;
  Part 1 is the kernel-level TV analogue, not that statement.

Registry: KR-1 (three-chain separation of discretisation, oracle and initialisation errors), with
the GI-1 Euler–Maruyama chains for the oracle term and the one-step certificates of
`Kernels/ErrorPropagation.lean` (also KR-1) as the engine; CE-07 (reset kernels, Part 2). Part 2
(a conditional TV bound for an SPS-type inner oracle) has no registry entry of its own.

## Not proved here

* No bound on any discretisation error `tvSup (D k x) (K k x)` (no SDE, no time regularity of
  scores, no moment bounds); it is an input.
* `TVContraction` with `ρ < 1` for any proximal, Langevin or diffusion kernel, and the
  along-the-chain hypothesis `hAlong` with a `K`-independent `ρ < 1` for any such kernel. No LSI
  or KL-contraction argument is used in this file (the KL contraction of SPS Lemma E.3 is proved
  in `Samplers/ProximalSharpLSI.lean` and `Samplers/ProximalGeneralLSI.lean`). The KL chain rule
  and Pinsker's inequality are not used in this file either; they are used elsewhere, for GI-1
  (`Foundations/KLChainRule.lean`, `Foundations/Pinsker.lean`).
* The SPS mini-batch kernel, batch-variance bounds, inner SGLD/MALA oracle guarantees, and the
  paper's Theorem 3.1 itself.
* Measurability of `x ↦ tvSup (κ x) (η x)`: averaged forms use explicit integrable majorants.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling
namespace ErrorDecomposition

open TotalVariation ErrorPropagation

variable {α : Type*} [MeasurableSpace α]

/-! ### Part 1: three-chain separation (KR-1) -/

section ThreeChain

variable {K D I : ℕ → Kernel α α} [∀ k, IsMarkovKernel (K k)] [∀ k, IsMarkovKernel (D k)]
  [∀ k, IsMarkovKernel (I k)] {μ ν : ℕ → Measure α}

/-- Kernel-level triangle inequality: `tvSup (K x) (I x) ≤ tvSup (I x) (D x) + tvSup (D x) (K x)`
for Markov kernels. -/
private lemma tvSup_exact_implemented_le (k : ℕ) (x : α) :
    tvSup (K k x) (I k x) ≤ tvSup (D k x) (K k x) + tvSup (I k x) (D k x) := by
  rw [tvSup_comm (K k x), add_comm]
  exact tvSup_triangle _ _ _

/-- **KR-1, uniform three-kernel separation.** Let `K k` (exact), `D k` (ideal discretised) and
`I k` (implemented) be Markov kernels on `α`, `μ (k+1) = K k ∘ₘ μ k` the exact chain and
`ν (k+1) = I k ∘ₘ ν k` the implemented chain, from probability laws. If
`tvSup (D k x) (K k x) ≤ disc k` and `tvSup (I k x) (D k x) ≤ oracle k` for all `k`, `x`, then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} disc k + ∑_{k<n} oracle k`. -/
theorem tvSup_le_sum_disc_add_sum_oracle [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = I k ∘ₘ ν k) {disc oracle : ℕ → ℝ}
    (hdisc : ∀ k x, tvSup (D k x) (K k x) ≤ disc k)
    (horacle : ∀ k x, tvSup (I k x) (D k x) ≤ oracle k) (n : ℕ) :
    tvSup (ν n) (μ n) ≤
      tvSup (ν 0) (μ 0) + ∑ k ∈ range n, disc k + ∑ k ∈ range n, oracle k := by
  have key := tvSup_chain_le_sum hμ hν (ε := fun k => disc k + oracle k)
    (fun k x => (tvSup_exact_implemented_le (D := D) k x).trans
      (add_le_add (hdisc k x) (horacle k x))) n
  rw [tvSup_comm (ν n), tvSup_comm (ν 0), add_assoc, ← sum_add_distrib]
  exact key

/-- **KR-1, separation with errors averaged under the implemented chain's law.** Same kernels
and chains as `tvSup_le_sum_disc_add_sum_oracle`. Let `d k`, `o k : α → ℝ` be integrable under
`ν k` (the law of the **implemented** chain at step `k`) with, for `ν k`-a.e. `x`,
`tvSup (D k x) (K k x) ≤ d k x` and `tvSup (I k x) (D k x) ≤ o k x`. Then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} ∫ d k d(ν k) + ∑_{k<n} ∫ o k d(ν k)`. -/
theorem tvSup_le_sum_integral_disc_add_oracle [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = I k ∘ₘ ν k) {d o : ℕ → α → ℝ} (hd : ∀ k, Integrable (d k) (ν k))
    (ho : ∀ k, Integrable (o k) (ν k)) (hdisc : ∀ k, ∀ᵐ x ∂(ν k), tvSup (D k x) (K k x) ≤ d k x)
    (horacle : ∀ k, ∀ᵐ x ∂(ν k), tvSup (I k x) (D k x) ≤ o k x) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n, ∫ x, d k x ∂(ν k) +
      ∑ k ∈ range n, ∫ x, o k x ∂(ν k) := by
  have key := tvSup_chain_le_sum_integral_approx hμ hν (e := fun k x => d k x + o k x)
    (fun k => (hd k).add (ho k))
    (fun k => (hdisc k).mp ((horacle k).mono fun x h2 h1 =>
      (tvSup_exact_implemented_le (D := D) k x).trans (add_le_add h1 h2))) n
  rw [tvSup_comm (ν n), tvSup_comm (ν 0), add_assoc, ← sum_add_distrib]
  refine key.trans (le_of_eq ?_)
  congr 1
  exact sum_congr rfl fun k _ => integral_add (hd k) (ho k)

/-- **KR-1, separation with errors averaged under the exact chain's law.** Same kernels and
chains as `tvSup_le_sum_disc_add_sum_oracle`. Let `d k`, `o k` be integrable under `μ k` (the law
of the **exact** chain at step `k`) with, for `μ k`-a.e. `x`, `tvSup (D k x) (K k x) ≤ d k x` and
`tvSup (I k x) (D k x) ≤ o k x`. Then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} ∫ d k d(μ k) + ∑_{k<n} ∫ o k d(μ k)`. -/
theorem tvSup_le_sum_integral_disc_add_oracle_exact [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = I k ∘ₘ ν k) {d o : ℕ → α → ℝ} (hd : ∀ k, Integrable (d k) (μ k))
    (ho : ∀ k, Integrable (o k) (μ k)) (hdisc : ∀ k, ∀ᵐ x ∂(μ k), tvSup (D k x) (K k x) ≤ d k x)
    (horacle : ∀ k, ∀ᵐ x ∂(μ k), tvSup (I k x) (D k x) ≤ o k x) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n, ∫ x, d k x ∂(μ k) +
      ∑ k ∈ range n, ∫ x, o k x ∂(μ k) := by
  have key := tvSup_chain_le_sum_integral_exact hμ hν (e := fun k x => d k x + o k x)
    (fun k => (hd k).add (ho k))
    (fun k => (hdisc k).mp ((horacle k).mono fun x h2 h1 =>
      (tvSup_exact_implemented_le (D := D) k x).trans (add_le_add h1 h2))) n
  rw [tvSup_comm (ν n), tvSup_comm (ν 0), add_assoc, ← sum_add_distrib]
  refine key.trans (le_of_eq ?_)
  congr 1
  exact sum_congr rfl fun k _ => integral_add (hd k) (ho k)

/-- **KR-1, three-chain separation (discretisation along the ideal chain, oracle along the
algorithm).** Kernels `K k` (exact), `D k` (ideal discretised), `I k` (implemented), with chains
`μ (k+1) = K k ∘ₘ μ k`, `δ (k+1) = D k ∘ₘ δ k`, `ν (k+1) = I k ∘ₘ ν k` from probability laws.
Let `d k` be integrable under `δ k` (the **ideal discretised** chain's law) with
`tvSup (D k x) (K k x) ≤ d k x` for `δ k`-a.e. `x`, and `o k` integrable under `ν k` (the
**implemented** chain's law) with `tvSup (I k x) (D k x) ≤ o k x` for `ν k`-a.e. `x`. Then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0)
  + ∑_{k<n} ∫ d k d(δ k) + ∑_{k<n} ∫ o k d(ν k)`. -/
theorem tvSup_le_three_chain {δ : ℕ → Measure α} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (δ 0)] [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hδ : ∀ k, δ (k + 1) = D k ∘ₘ δ k) (hν : ∀ k, ν (k + 1) = I k ∘ₘ ν k) {d o : ℕ → α → ℝ}
    (hd : ∀ k, Integrable (d k) (δ k)) (hdisc : ∀ k, ∀ᵐ x ∂(δ k), tvSup (D k x) (K k x) ≤ d k x)
    (ho : ∀ k, Integrable (o k) (ν k))
    (horacle : ∀ k, ∀ᵐ x ∂(ν k), tvSup (I k x) (D k x) ≤ o k x) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0) +
      ∑ k ∈ range n, ∫ x, d k x ∂(δ k) + ∑ k ∈ range n, ∫ x, o k x ∂(ν k) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hδ n
  have := isProbabilityMeasure_of_comp_succ hν n
  have h1 := tvSup_chain_le_sum_integral_approx hδ hν ho
    (fun k => (horacle k).mono fun x hx => by rwa [tvSup_comm]) n
  have h2 := tvSup_chain_le_sum_integral_approx hμ hδ hd
    (fun k => (hdisc k).mono fun x hx => by rwa [tvSup_comm]) n
  rw [tvSup_comm (δ n), tvSup_comm (δ 0)] at h1
  rw [tvSup_comm (μ n), tvSup_comm (μ 0)] at h2
  have h3 := tvSup_triangle (ν n) (δ n) (μ n)
  linarith

/-- **KR-1, three-chain separation (oracle along the ideal chain, discretisation along the
exact chain).** Same kernels and chains as `tvSup_le_three_chain`. Let `o k` be integrable under
`δ k` (the **ideal discretised** chain's law) with `tvSup (I k x) (D k x) ≤ o k x` for
`δ k`-a.e. `x`, and `d k` integrable under `μ k` (the **exact** chain's law) with
`tvSup (D k x) (K k x) ≤ d k x` for `μ k`-a.e. `x`. Then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0)
  + ∑_{k<n} ∫ d k d(μ k) + ∑_{k<n} ∫ o k d(δ k)`. -/
theorem tvSup_le_three_chain_exact {δ : ℕ → Measure α} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (δ 0)] [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hδ : ∀ k, δ (k + 1) = D k ∘ₘ δ k) (hν : ∀ k, ν (k + 1) = I k ∘ₘ ν k) {d o : ℕ → α → ℝ}
    (hd : ∀ k, Integrable (d k) (μ k)) (hdisc : ∀ k, ∀ᵐ x ∂(μ k), tvSup (D k x) (K k x) ≤ d k x)
    (ho : ∀ k, Integrable (o k) (δ k))
    (horacle : ∀ k, ∀ᵐ x ∂(δ k), tvSup (I k x) (D k x) ≤ o k x) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0) +
      ∑ k ∈ range n, ∫ x, d k x ∂(μ k) + ∑ k ∈ range n, ∫ x, o k x ∂(δ k) := by
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hδ n
  have := isProbabilityMeasure_of_comp_succ hν n
  have h1 := tvSup_chain_le_sum_integral_exact hδ hν ho
    (fun k => (horacle k).mono fun x hx => by rwa [tvSup_comm]) n
  have h2 := tvSup_chain_le_sum_integral_exact hμ hδ hd
    (fun k => (hdisc k).mono fun x hx => by rwa [tvSup_comm]) n
  rw [tvSup_comm (δ n), tvSup_comm (δ 0)] at h1
  rw [tvSup_comm (μ n), tvSup_comm (μ 0)] at h2
  have h3 := tvSup_triangle (ν n) (δ n) (μ n)
  linarith

end ThreeChain

/-! ### Part 2: TV variant of the SPS outer framework (Conditional) -/

section Contraction

/-- **Named hypothesis (SPS-type bound, uniform version, for uniformly ergodic kernels only): TV
contraction towards `π` from every initial law.** A kernel `P` contracts TV towards `π` with factor
`ρ` if `tvSup (P ∘ₘ μ) π ≤ ρ tvSup μ π` for **every** probability measure `μ`. With `ρ < 1` this
is a uniform-ergodicity condition: it forces `tvSup (P x) π ≤ ρ` for every starting point `x`
(`TVContraction.tvSup_apply_le`), which is not expected for the proximal sampler on `ℝ` with
unbounded support, e.g. a Gaussian target (module docstring; not formalised). This is a caveat
about the proximal sampler, not a general impossibility: uniformly ergodic kernels can satisfy it
with `ρ < 1` even when `π` has unbounded support (e.g. the independent sampler `x ↦ π` for a
Gaussian `π`, `tvContraction_const`). It is therefore **not** the recommended SPS-type
hypothesis; that is the along-the-chain contraction of `tvSup_le_of_contraction_along`, which
`TVContraction` implies (`contraction_along_of_tvContraction`). `TVContraction` is not proved with
`ρ < 1` for any proximal, Langevin or diffusion kernel. It implies invariance of `π`
(`TVContraction.comp_eq`). It holds with `ρ = 1` for every Markov `P` with invariant `π`
(`tvContraction_one_of_comp_eq`), and with every `ρ ≥ 0` for the independent sampler `x ↦ π`
(`tvContraction_const`). -/
def TVContraction (P : Kernel α α) (π : Measure α) (ρ : ℝ) : Prop :=
  ∀ μ : Measure α, IsProbabilityMeasure μ → tvSup (P ∘ₘ μ) π ≤ ρ * tvSup μ π

/-- **TV contraction implies invariance.** If `P` is Markov, `π` is a probability measure and
`TVContraction P π ρ` holds for some `ρ`, then `P ∘ₘ π = π` (apply the hypothesis to `μ = π`). -/
theorem TVContraction.comp_eq {P : Kernel α α} [IsMarkovKernel P] {π : Measure α}
    [IsProbabilityMeasure π] {ρ : ℝ} (hP : TVContraction P π ρ) : P ∘ₘ π = π := by
  have h := hP π inferInstance
  rw [tvSup_self, mul_zero] at h
  exact tvSup_eq_zero_iff.1 (le_antisymm h (tvSup_nonneg _ _))

/-- **TV contraction forces uniform ergodicity.** If `P` is Markov, `π` a probability measure,
`0 ≤ ρ` and `TVContraction P π ρ`, then `tvSup (P x) π ≤ ρ` for every starting point `x`
(apply the hypothesis to `μ = δₓ` and use `tvSup δₓ π ≤ 1`). In particular `ρ < 1` requires the
one-step laws from **all** starting points to be uniformly close to `π`. -/
theorem TVContraction.tvSup_apply_le {P : Kernel α α} [IsMarkovKernel P] {π : Measure α}
    [IsProbabilityMeasure π] {ρ : ℝ} (hρ : 0 ≤ ρ) (hP : TVContraction P π ρ) (x : α) :
    tvSup (P x) π ≤ ρ := by
  have h := hP (Measure.dirac x) inferInstance
  rw [Measure.dirac_bind P.measurable] at h
  exact h.trans (mul_le_of_le_one_right hρ (tvSup_le_one _ _))

/-- **Monotonicity in the factor.** `TVContraction P π ρ` and `ρ ≤ ρ'` give
`TVContraction P π ρ'` (TV is nonnegative). -/
theorem TVContraction.mono {P : Kernel α α} {π : Measure α} {ρ ρ' : ℝ}
    (hP : TVContraction P π ρ) (hρ : ρ ≤ ρ') : TVContraction P π ρ' := fun μ hμ =>
  (hP μ hμ).trans (mul_le_mul_of_nonneg_right hρ (tvSup_nonneg _ _))

/-- **Nonvacuity, `ρ = 1`.** Every Markov kernel `P` with an invariant finite measure `π`
(`P ∘ₘ π = π`) satisfies `TVContraction P π 1`; this is KR-1 (`tvSup_comp_le`). -/
theorem tvContraction_one_of_comp_eq {P : Kernel α α} [IsMarkovKernel P] {π : Measure α}
    [IsFiniteMeasure π] (hπ : P ∘ₘ π = π) : TVContraction P π 1 := fun μ _ => by
  rw [one_mul]
  conv_lhs => rw [← hπ]
  exact tvSup_comp_le P μ π

/-- **Nonvacuity, `ρ = 0`.** The independent sampler `x ↦ π` (`Kernel.const α π`) satisfies
`TVContraction (Kernel.const α π) π 0` for a probability measure `π` (one step reaches `π`
exactly), hence `TVContraction … ρ` for every `ρ ≥ 0` by `TVContraction.mono`. -/
theorem tvContraction_const (π : Measure α) [IsProbabilityMeasure π] :
    TVContraction (Kernel.const α π) π 0 := fun μ _ => by
  simp [tvSup_self]

/-- Linear recursion `d (k+1) ≤ ρ d k + a k` for `k < K`, with `0 ≤ ρ`, gives
`d K ≤ ρ^K d 0 + ∑_{k<K} ρ^(K-1-k) a k`. -/
private lemma le_geom_of_rec {d a : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {K : ℕ}
    (h : ∀ k < K, d (k + 1) ≤ ρ * d k + a k) :
    d K ≤ ρ ^ K * d 0 + ∑ k ∈ range K, ρ ^ (K - 1 - k) * a k := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ih := ih fun k hk => h k (by omega)
    have hsum : ρ * ∑ k ∈ range K, ρ ^ (K - 1 - k) * a k =
        ∑ k ∈ range K, ρ ^ (K + 1 - 1 - k) * a k := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hk' := mem_range.1 hk
      rw [← mul_assoc, ← pow_succ', show K - 1 - k + 1 = K + 1 - 1 - k by omega]
    calc d (K + 1) ≤ ρ * d K + a K := h K (by omega)
      _ ≤ ρ * (ρ ^ K * d 0 + ∑ k ∈ range K, ρ ^ (K - 1 - k) * a k) + a K := by
          gcongr
      _ = ρ ^ (K + 1) * d 0 + ∑ k ∈ range (K + 1), ρ ^ (K + 1 - 1 - k) * a k := by
          rw [mul_add, hsum, sum_range_succ, show K + 1 - 1 - K = 0 by omega, pow_zero,
            one_mul, pow_succ']
          ring

variable {P P' : ℕ → Kernel α α} [∀ k, IsMarkovKernel (P k)] [∀ k, IsMarkovKernel (P' k)]
  {π : Measure α} [IsProbabilityMeasure π] {ν : ℕ → Measure α}

/-- **SPS-type bound (Conditional), recommended form: TV contraction along the algorithm's own laws,
uniform oracle errors.** Let `π` be a probability measure, `P k` exact Markov kernels (in the
application `π` is invariant for `P k`; invariance is not used by the proof and not assumed),
`P' k` inexact Markov kernels, and `ν (k+1) = P' k ∘ₘ ν k` the inexact chain from a probability law
`ν 0`. Assume, for every `k < K`,
* `hAlong` (named hypothesis, the mixing input): `tvSup (P k ∘ₘ ν k) π ≤ ρ tvSup (ν k) π` with
  `0 ≤ ρ`, i.e. one **exact** step applied to the **algorithm's** current law `ν k` contracts TV
  towards `π`. It constrains only the `K` laws `ν 0, …, ν (K-1)`, not every initial law, so unlike
  `TVContraction` with `ρ < 1` it does not force uniform ergodicity (witness:
  `contraction_along_resetKernel`, `not_tvContraction_resetKernel`). It is the TV analogue of the
  KL contraction along the chain, `KL(ν_k P_k ‖ π) ≤ KL(ν_k ‖ π)/(1 + α η_k)²`, that the LSI
  argument of SPS (Lemma E.3) delivers; it is **not** derived from it here (that needs Pinsker's
  inequality (`Foundations/Pinsker.lean`, not in Mathlib), and even then yields a KL-to-TV, not
  a TV-to-TV, bound; see `exists_contraction_along_lt_one`);
* `hε`: `tvSup (P' k x) (P k x) ≤ ε k` for every `x` (uniform oracle error).
Then `tvSup (ν K) π ≤ ρ^K tvSup (ν 0) π + ∑_{k<K} ρ^(K-1-k) ε k`. It generalises
`tvSup_le_of_tvContraction` (`contraction_along_of_tvContraction`). -/
theorem tvSup_le_of_contraction_along {ρ : ℝ} (hρ : 0 ≤ ρ) [IsProbabilityMeasure (ν 0)]
    (hν : ∀ k, ν (k + 1) = P' k ∘ₘ ν k) {K : ℕ}
    (hAlong : ∀ k < K, tvSup (P k ∘ₘ ν k) π ≤ ρ * tvSup (ν k) π) {ε : ℕ → ℝ}
    (hε : ∀ k < K, ∀ x, tvSup (P' k x) (P k x) ≤ ε k) :
    tvSup (ν K) π ≤ ρ ^ K * tvSup (ν 0) π + ∑ k ∈ range K, ρ ^ (K - 1 - k) * ε k := by
  refine le_geom_of_rec (d := fun k => tvSup (ν k) π) hρ fun k hk => ?_
  have := isProbabilityMeasure_of_comp_succ hν k
  rw [hν k]
  have h1 := tvSup_triangle (P' k ∘ₘ ν k) (P k ∘ₘ ν k) π
  have h2 := tvSup_comp_le_of_forall (P' k) (P k) (ν k) (hε k hk)
  have h3 := hAlong k hk
  linarith

/-- **SPS-type bound (Conditional), recommended form, law-averaged oracle errors.** Same setting and
along-the-chain hypothesis `hAlong` as `tvSup_le_of_contraction_along` (for `k < K`,
`tvSup (P k ∘ₘ ν k) π ≤ ρ tvSup (ν k) π` with `0 ≤ ρ`), but the inexactness is controlled by
majorants `e k` integrable under the **inexact** chain's law `ν k`, with
`tvSup (P' k x) (P k x) ≤ e k x` for `ν k`-a.e. `x` and `k < K`. Then
`tvSup (ν K) π ≤ ρ^K tvSup (ν 0) π + ∑_{k<K} ρ^(K-1-k) ∫ e k d(ν k)`. -/
theorem tvSup_le_of_contraction_along_integral {ρ : ℝ} (hρ : 0 ≤ ρ)
    [IsProbabilityMeasure (ν 0)] (hν : ∀ k, ν (k + 1) = P' k ∘ₘ ν k) {K : ℕ}
    (hAlong : ∀ k < K, tvSup (P k ∘ₘ ν k) π ≤ ρ * tvSup (ν k) π) {e : ℕ → α → ℝ}
    (he : ∀ k < K, Integrable (e k) (ν k))
    (hε : ∀ k < K, ∀ᵐ x ∂(ν k), tvSup (P' k x) (P k x) ≤ e k x) :
    tvSup (ν K) π ≤
      ρ ^ K * tvSup (ν 0) π + ∑ k ∈ range K, ρ ^ (K - 1 - k) * ∫ x, e k x ∂(ν k) := by
  refine le_geom_of_rec (d := fun k => tvSup (ν k) π) (a := fun k => ∫ x, e k x ∂(ν k)) hρ
    fun k hk => ?_
  have := isProbabilityMeasure_of_comp_succ hν k
  rw [hν k]
  have h1 := tvSup_triangle (P' k ∘ₘ ν k) (P k ∘ₘ ν k) π
  have h2 := tvSup_comp_le_integral (P' k) (P k) (ν k) (he k hk) (hε k hk)
  have h3 := hAlong k hk
  linarith

omit [∀ k, IsMarkovKernel (P k)] [IsProbabilityMeasure π] in
/-- **The uniform hypothesis implies the along-the-chain one.** If `TVContraction (P k) π ρ`
holds for every `k` and `ν (k+1) = P' k ∘ₘ ν k` is a chain of Markov kernels from a probability law
`ν 0`, then `tvSup (P k ∘ₘ ν k) π ≤ ρ tvSup (ν k) π` for every `k` (every `ν k` is a probability
measure). Hence `tvSup_le_of_contraction_along` generalises `tvSup_le_of_tvContraction`. -/
theorem contraction_along_of_tvContraction {ρ : ℝ} (hP : ∀ k, TVContraction (P k) π ρ)
    [IsProbabilityMeasure (ν 0)] (hν : ∀ k, ν (k + 1) = P' k ∘ₘ ν k) (k : ℕ) :
    tvSup (P k ∘ₘ ν k) π ≤ ρ * tvSup (ν k) π :=
  hP k (ν k) (isProbabilityMeasure_of_comp_succ hν k)

/-- **SPS-type bound (Conditional), uniform version: only for uniformly ergodic kernels.** Let
`P k` be exact Markov kernels with target `π` (a probability measure) satisfying the named
hypothesis `TVContraction (P k) π ρ` with `0 ≤ ρ` (which implies `P k ∘ₘ π = π`), let `P' k` be
inexact Markov kernels with `tvSup (P' k x) (P k x) ≤ ε k` for every `x`, and let
`ν (k+1) = P' k ∘ₘ ν k` be the inexact chain from a probability law `ν 0`. Then
`tvSup (ν K) π ≤ ρ^K tvSup (ν 0) π + ∑_{k<K} ρ^(K-1-k) ε k`.
With `ρ < 1` the hypothesis forces uniform ergodicity (`TVContraction.tvSup_apply_le`), so this
form applies **only to uniformly ergodic kernels**; for the proximal sampler on `ℝ` with unbounded
support (e.g. a Gaussian target) uniform ergodicity is not expected, so with `ρ < 1` this form is
expected to be vacuous there (not formalised; see the module docstring). Use
`tvSup_le_of_contraction_along` instead, of which this is a special case.
With `ρ = 1` (always available for invariant `π`) this is the additive bound of
`ErrorPropagation.tvSup_le_of_invariant`; a fixed exact kernel is the case `P k = P`. -/
theorem tvSup_le_of_tvContraction {ρ : ℝ} (hρ : 0 ≤ ρ) (hP : ∀ k, TVContraction (P k) π ρ)
    [IsProbabilityMeasure (ν 0)] (hν : ∀ k, ν (k + 1) = P' k ∘ₘ ν k) {ε : ℕ → ℝ}
    (hε : ∀ k x, tvSup (P' k x) (P k x) ≤ ε k) (K : ℕ) :
    tvSup (ν K) π ≤ ρ ^ K * tvSup (ν 0) π + ∑ k ∈ range K, ρ ^ (K - 1 - k) * ε k :=
  tvSup_le_of_contraction_along hρ hν
    (fun k _ => contraction_along_of_tvContraction (P' := P') hP hν k) fun k _ => hε k

/-- **SPS-type bound (Conditional), uniform version, law-averaged form: only for uniformly ergodic
kernels.** Same setting as `tvSup_le_of_tvContraction`, but the inexactness is controlled by
majorants `e k` integrable under the **inexact** chain's law `ν k`, with
`tvSup (P' k x) (P k x) ≤ e k x` for `ν k`-a.e. `x`. Then
`tvSup (ν K) π ≤ ρ^K tvSup (ν 0) π + ∑_{k<K} ρ^(K-1-k) ∫ e k d(ν k)`. As for
`tvSup_le_of_tvContraction`, `TVContraction` with `ρ < 1` means uniform ergodicity; the
recommended form is `tvSup_le_of_contraction_along_integral`, of which this is a special case. -/
theorem tvSup_le_of_tvContraction_integral {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hP : ∀ k, TVContraction (P k) π ρ) [IsProbabilityMeasure (ν 0)]
    (hν : ∀ k, ν (k + 1) = P' k ∘ₘ ν k) {e : ℕ → α → ℝ} (he : ∀ k, Integrable (e k) (ν k))
    (hε : ∀ k, ∀ᵐ x ∂(ν k), tvSup (P' k x) (P k x) ≤ e k x) (K : ℕ) :
    tvSup (ν K) π ≤
      ρ ^ K * tvSup (ν 0) π + ∑ k ∈ range K, ρ ^ (K - 1 - k) * ∫ x, e k x ∂(ν k) :=
  tvSup_le_of_contraction_along_integral hρ hν
    (fun k _ => contraction_along_of_tvContraction (P' := P') hP hν k) (fun k _ => he k)
    fun k _ => hε k

end Contraction

/-! ### Satisfiability of the along-the-chain hypothesis -/

section AlongWitness

/-- **Stationary chains satisfy the along-the-chain hypothesis with `ρ = 0`.** If
`P k ∘ₘ π = π` and `ν k = π` for every `k < K`, then
`tvSup (P k ∘ₘ ν k) π ≤ ρ tvSup (ν k) π` for every `k < K` and every `ρ` (both sides vanish), in
particular with `ρ = 0`. No uniformity over starting points is involved. -/
theorem contraction_along_of_eq_target {P : ℕ → Kernel α α} {π : Measure α}
    {ν : ℕ → Measure α} {K : ℕ} (hπ : ∀ k < K, P k ∘ₘ π = π) (hνπ : ∀ k < K, ν k = π) (ρ : ℝ) :
    ∀ k < K, tvSup (P k ∘ₘ ν k) π ≤ ρ * tvSup (ν k) π := fun k hk => by
  rw [hνπ k hk, hπ k hk, tvSup_self, mul_zero]

/-- **At a fixed horizon the along-the-chain hypothesis only constrains finitely many laws.**
Let `P k` be kernels with `P k ∘ₘ π = π` and `ν k` measures such that for every `k < K`, if
`ν k ≠ π` then one exact step strictly decreases TV: `tvSup (P k ∘ₘ ν k) π < tvSup (ν k) π`.
Then some `ρ` with `0 ≤ ρ < 1` satisfies `tvSup (P k ∘ₘ ν k) π ≤ ρ tvSup (ν k) π` for all
`k < K` (the largest of the `K` one-step ratios). So, for a fixed `K`, `hAlong` with `ρ < 1`
only asks for strict one-step decrease along the algorithm's laws, with no uniformity over
starting points; the quantitative content of the SPS-type bound is a factor `ρ < 1` that does
not depend on the horizon `K`. Such a horizon-free geometric rate along the chain is what LSI-based
arguments supply, but **in KL**: under LSI, `KL(ν P ‖ π) ≤ KL(ν ‖ π)/(1 + α η)²` for every law with
finite KL (SPS Lemma E.3). In KL this does not force uniform ergodicity because
`KL(δₓ ‖ π) = ∞` for an atomless `π`, whereas `tvSup δₓ π ≤ 1`, which is why the TV hypothesis
must be restricted to the chain's own laws. Converting the KL rate to TV needs Pinsker's
inequality `TV ≤ √(KL/2)` (`Foundations/Pinsker.lean`, not in Mathlib), and even then gives
`tvSup (ν P) π ≤ √(KL(ν ‖ π)/2)/(1 + α η)`, a KL-to-TV bound rather than the TV-to-TV hypothesis
`hAlong`; so `hAlong` remains a named, unproved hypothesis for the proximal sampler. -/
theorem exists_contraction_along_lt_one {P : ℕ → Kernel α α} {π : Measure α}
    {ν : ℕ → Measure α} {K : ℕ} (hπ : ∀ k < K, P k ∘ₘ π = π)
    (hstrict : ∀ k < K, ν k ≠ π → tvSup (P k ∘ₘ ν k) π < tvSup (ν k) π) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k < K, tvSup (P k ∘ₘ ν k) π ≤ ρ * tvSup (ν k) π := by
  induction K with
  | zero => exact ⟨0, le_rfl, one_pos, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ K ih =>
    obtain ⟨ρ₀, h0, h1, h⟩ :=
      ih (fun k hk => hπ k (by omega)) fun k hk => hstrict k (by omega)
    by_cases hK : ν K = π
    · refine ⟨ρ₀, h0, h1, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact h k hk
      · rw [hk, hK, hπ K (by omega), tvSup_self, mul_zero]
    · have hst := hstrict K (by omega) hK
      have ht : 0 < tvSup (ν K) π := (tvSup_nonneg _ _).trans_lt hst
      refine ⟨max ρ₀ (tvSup (P K ∘ₘ ν K) π / tvSup (ν K) π), le_max_of_le_left h0,
        max_lt h1 ((div_lt_one ht).2 hst), fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact (h k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tvSup_nonneg _ _))
      · rw [hk]
        calc tvSup (P K ∘ₘ ν K) π
            = tvSup (P K ∘ₘ ν K) π / tvSup (ν K) π * tvSup (ν K) π := by
              field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le

open Classical in
/-- **Reset kernel (witness kernel).** For a measurable set `A` and a measure `π`, the kernel that
jumps to `π` from points of `A` and stays put outside `A`: `resetKernel hA π x = π` for `x ∈ A`
and `= δₓ` for `x ∉ A` (`Kernel.piecewise`). It is a toy kernel used only to show that the
along-the-chain hypothesis does not imply uniform ergodicity; it is not a sampler of interest. -/
noncomputable def resetKernel {A : Set α} (hA : MeasurableSet A) (π : Measure α) : Kernel α α :=
  Kernel.piecewise hA (Kernel.const α π) Kernel.id

variable {A : Set α} (hA : MeasurableSet A) {π : Measure α}

/-- The reset kernel is Markov when `π` is a probability measure. -/
instance isMarkovKernel_resetKernel [IsProbabilityMeasure π] :
    IsMarkovKernel (resetKernel hA π) := by
  unfold resetKernel
  infer_instance

/-- On `A` the reset kernel is `π`: `resetKernel hA π x = π` for `x ∈ A`. -/
theorem resetKernel_apply_of_mem {x : α} (hx : x ∈ A) : resetKernel hA π x = π := by
  classical
  simp [resetKernel, Kernel.piecewise_apply, hx]

/-- Off `A` the reset kernel does not move: `resetKernel hA π x = δₓ` for `x ∉ A`. -/
theorem resetKernel_apply_of_notMem {x : α} (hx : x ∉ A) :
    resetKernel hA π x = Measure.dirac x := by
  classical
  simp [resetKernel, Kernel.piecewise_apply, hx, Kernel.id_apply]

/-- From a probability law `μ` carried by `A` (`μ Aᶜ = 0`) the reset kernel reaches `π` in one
step: `resetKernel hA π ∘ₘ μ = π`. -/
theorem resetKernel_comp_of_compl_eq_zero {μ : Measure α} [IsProbabilityMeasure μ]
    (hμ : μ Aᶜ = 0) : resetKernel hA π ∘ₘ μ = π := by
  have h : ∀ᵐ x ∂μ, resetKernel hA π x = Kernel.const α π x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    rw [Kernel.const_apply]
    exact resetKernel_apply_of_mem hA (by simpa using hx)
  rw [Measure.comp_congr h, Measure.const_comp, measure_univ, one_smul]

/-- **Along-the-chain contraction with `ρ = 0` for the reset kernel.** If `P k = resetKernel hA π`
for every `k` and the laws `ν k` are probability measures carried by `A` (`ν k Aᶜ = 0`) for every
`k < K`, then `tvSup (P k ∘ₘ ν k) π ≤ 0 * tvSup (ν k) π` for every `k < K` (one step reaches
`π`). The laws `ν k` need not equal `π`. Together with `not_tvContraction_resetKernel` this shows
that the along-the-chain hypothesis of `tvSup_le_of_contraction_along` can hold with `ρ = 0` for a
kernel that is not uniformly ergodic. -/
theorem contraction_along_resetKernel {ν : ℕ → Measure α} [∀ k, IsProbabilityMeasure (ν k)]
    {K : ℕ} (hν : ∀ k < K, ν k Aᶜ = 0) :
    ∀ k < K, tvSup (resetKernel hA π ∘ₘ ν k) π ≤ 0 * tvSup (ν k) π := fun k hk => by
  rw [resetKernel_comp_of_compl_eq_zero hA (hν k hk), tvSup_self, zero_mul]

/-- **The reset chain stays on `A`.** If `π` is carried by `A` (`π Aᶜ = 0`), `ν 0` is a probability
law carried by `A` and `ν (k+1) = resetKernel hA π ∘ₘ ν k`, then every `ν k` is carried by `A`
(indeed `ν k = π` for `k ≥ 1`). So `contraction_along_resetKernel` applies to the reset chain from
any such initial law, in particular from `ν 0 ≠ π`. -/
theorem resetKernel_chain_compl_eq_zero [IsProbabilityMeasure π] (hπ : π Aᶜ = 0)
    {ν : ℕ → Measure α} [IsProbabilityMeasure (ν 0)] (hν0 : ν 0 Aᶜ = 0)
    (hν : ∀ k, ν (k + 1) = resetKernel hA π ∘ₘ ν k) (k : ℕ) : ν k Aᶜ = 0 := by
  induction k with
  | zero => exact hν0
  | succ k ih =>
    have := isProbabilityMeasure_of_comp_succ (κ := fun _ => resetKernel hA π) hν k
    rw [hν k, resetKernel_comp_of_compl_eq_zero hA ih, hπ]

/-- **The reset kernel is not uniformly TV-contracting.** If `π` is a probability measure carried
by `A` (`π Aᶜ = 0`) and some point `x ∉ A` exists, then `TVContraction (resetKernel hA π) π ρ` fails
for every `ρ < 1`: from `δₓ` the kernel does not move, and `δₓ ≠ π`. So the uniform hypothesis of
`tvSup_le_of_tvContraction` with `ρ < 1` is unavailable for this kernel, while the along-the-chain
hypothesis holds with `ρ = 0` (`contraction_along_resetKernel`). -/
theorem not_tvContraction_resetKernel [IsProbabilityMeasure π] (hπ : π Aᶜ = 0) {x : α}
    (hx : x ∉ A) {ρ : ℝ} (hρ : ρ < 1) : ¬ TVContraction (resetKernel hA π) π ρ := by
  intro h
  have h1 := h (Measure.dirac x) inferInstance
  rw [Measure.dirac_bind (resetKernel hA π).measurable, resetKernel_apply_of_notMem hA hx] at h1
  have hne : Measure.dirac x ≠ π := fun heq => by
    have hd : Measure.dirac x Aᶜ = 1 := by
      rw [Measure.dirac_apply' x hA.compl]
      simp [hx]
    rw [heq, hπ] at hd
    exact zero_ne_one hd
  have hpos : 0 < tvSup (Measure.dirac x) π :=
    lt_of_le_of_ne (tvSup_nonneg _ _) fun h0 => hne (tvSup_eq_zero_iff.1 h0.symm)
  nlinarith

end AlongWitness

/-! ### Kernel-level corollary -/

section KernelLevel

/-- **Inexact inner oracle, kernel level.** Let `F : Kernel α β` be a Markov kernel (forward
step) and `R R' : Kernel β γ` Markov kernels (exact and inexact inner oracle, e.g. the RGO and an
inner sampler). If `tvSup (R' y) (R y) ≤ ε` for every `y`, then for every `x`,
`tvSup ((R' ∘ₖ F) x) ((R ∘ₖ F) x) ≤ ε`: the inexact two-step kernel is `ε`-close to the exact one
for the same forward step. -/
theorem tvSup_comp_kernel_apply_le {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (F : Kernel α β) [IsMarkovKernel F] (R R' : Kernel β γ) [IsMarkovKernel R]
    [IsMarkovKernel R'] {ε : ℝ} (h : ∀ y, tvSup (R' y) (R y) ≤ ε) (x : α) :
    tvSup ((R' ∘ₖ F) x) ((R ∘ₖ F) x) ≤ ε := by
  rw [Kernel.comp_apply, Kernel.comp_apply]
  exact tvSup_comp_le_of_forall R' R (F x) h

end KernelLevel

end ErrorDecomposition
end FormalizeSampling
