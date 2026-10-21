module

public import FormalizeSampling.Kernels.ErrorDecomposition
public import FormalizeSampling.Samplers.Proximal

/-!
# The proximal sampler with an inexact inner oracle in total variation (Conditional)

The one-dimensional proximal sampler (`Samplers/Proximal.lean`) instance of Part 2 of
`Kernels/ErrorDecomposition.lean`, the TV variant of the SPS outer framework: an exact forward
step `forwardKernel η` followed by an inexact restricted Gaussian oracle `R'` with
`tvSup (R' y) (rgoKernel f η y) ≤ ε` for every `y`. `tvSup` is
`FormalizeSampling.TotalVariation.tvSup`. The declarations live in the namespace
`FormalizeSampling.ErrorDecomposition`.

## Main results

* `tvContraction_proxKernel`: the exact proximal kernel satisfies
  `TVContraction (proxKernel f η) (target f) 1` (from the invariance of the target, PX-1).
* `tvSup_inexactProx_le_along` (recommended form): under the named hypothesis `hAlong` (one
  exact step from the algorithm's law contracts TV towards the target with factor `ρ`),
  `tvSup (ν K) (target f) ≤ ρ^K tvSup (ν 0) (target f) + ∑_{k<K} ρ^(K-1-k) ε k`.
* `tvSup_inexactProx_le`: the same bound under the uniform hypothesis `TVContraction` (only
  for uniformly ergodic kernels; see the caveat in `Kernels/ErrorDecomposition.lean`).

## Not proved here

* `hAlong` or `TVContraction` with `ρ < 1` for the proximal sampler; with `ρ = 1` both hold and
  the bounds are additive.
-/

public section

open MeasureTheory
open ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling
namespace ErrorDecomposition

open TotalVariation ErrorPropagation

variable {f : ℝ → ℝ} {η : ℝ}

/-- **Nonvacuity for the proximal sampler, `ρ = 1` only.** For measurable `f` with integrable
`exp ∘ (-f)` and `η > 0`, the exact proximal kernel satisfies
`TVContraction (proxKernel f η) (target f) 1` (from its invariance,
`Proximal.proxKernel_comp_target`, PX-1). No `ρ < 1` is claimed; see the module docstring for
why uniform TV contraction with `ρ < 1` is not expected here (not formalised), and
`tvSup_inexactProx_le_along` for the recommended along-the-chain form. -/
theorem tvContraction_proxKernel (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) :
    TVContraction (Proximal.proxKernel f η) (Proximal.target f) 1 := by
  have := Proximal.isMarkovKernel_proxKernel hf hint hη
  have := Proximal.isProbabilityMeasure_target hint
  exact tvContraction_one_of_comp_eq (Proximal.proxKernel_comp_target hf hint hη)

/-- **SPS-type bound (Conditional), recommended form for the one-dimensional proximal sampler
with an inexact RGO: contraction along the algorithm's own laws.** Let `f` be measurable with
`exp ∘ (-f)` integrable, `η k > 0` step sizes (the Gaussian variances of the forward steps), and
`R' k` Markov kernels (inexact inner RGO samplers). Let
`ν (k+1) = (R' k ∘ₖ forwardKernel (η k)) ∘ₘ ν k` be the inexact proximal chain (exact forward
step, inexact backward step) from a probability law `ν 0`. Assume, for every `k < K`,
* `hAlong` (named hypothesis): `tvSup (proxKernel f (η k) ∘ₘ ν k) (target f) ≤
  ρ tvSup (ν k) (target f)` with `0 ≤ ρ`: one **exact** proximal step from the algorithm's law
  `ν k` contracts TV towards the target. This is the TV analogue of the KL contraction of the exact
  proximal sampler along the chain under LSI (SPS Lemma E.3); it is not proved here (no LSI or
  Pinsker argument is used), but unlike `TVContraction` it constrains only the laws
  `ν 0, …, ν (K-1)` and does not force uniform ergodicity;
* `hR`: `tvSup (R' k y) (rgoKernel f (η k) y) ≤ ε k` for every `y` (a uniform TV oracle
  condition, in place of the SPS paper's KL condition (7)).
Then `tvSup (ν K) (target f) ≤ ρ^K tvSup (ν 0) (target f) + ∑_{k<K} ρ^(K-1-k) ε k`. The target
is invariant for the exact kernel (`Proximal.proxKernel_comp_target`), so `hAlong` always holds
with `ρ = 1` (KR-1), giving the additive bound. -/
theorem tvSup_inexactProx_le_along (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℕ → ℝ} (hη : ∀ k, 0 < η k)
    {R' : ℕ → Kernel ℝ ℝ} [∀ k, IsMarkovKernel (R' k)] {ν : ℕ → Measure ℝ}
    [IsProbabilityMeasure (ν 0)]
    (hν : ∀ k, ν (k + 1) = (R' k ∘ₖ Proximal.forwardKernel (η k)) ∘ₘ ν k) {K : ℕ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hAlong : ∀ k < K, tvSup (Proximal.proxKernel f (η k) ∘ₘ ν k) (Proximal.target f) ≤
      ρ * tvSup (ν k) (Proximal.target f)) {ε : ℕ → ℝ}
    (hR : ∀ k < K, ∀ y, tvSup (R' k y) (Proximal.rgoKernel f (η k) y) ≤ ε k) :
    tvSup (ν K) (Proximal.target f) ≤
      ρ ^ K * tvSup (ν 0) (Proximal.target f) + ∑ k ∈ range K, ρ ^ (K - 1 - k) * ε k := by
  have := Proximal.isProbabilityMeasure_target hint
  have : ∀ k, IsMarkovKernel (Proximal.forwardKernel (η k)) :=
    fun k => Proximal.isMarkovKernel_forwardKernel (hη k)
  have : ∀ k, IsMarkovKernel (Proximal.rgoKernel f (η k)) :=
    fun k => Proximal.isMarkovKernel_rgoKernel hf hint (hη k)
  have : ∀ k, IsMarkovKernel (Proximal.proxKernel f (η k)) :=
    fun k => Proximal.isMarkovKernel_proxKernel hf hint (hη k)
  exact tvSup_le_of_contraction_along (P := fun k => Proximal.proxKernel f (η k)) hρ hν hAlong
    fun k hk x => tvSup_comp_kernel_apply_le (Proximal.forwardKernel (η k))
      (Proximal.rgoKernel f (η k)) (R' k) (hR k hk) x

/-- **SPS-type bound (Conditional) for the one-dimensional proximal sampler with an inexact RGO,
uniform version: only for uniformly ergodic kernels.** Let `f` be measurable with `exp ∘ (-f)`
integrable, `η k > 0` step sizes (the Gaussian variances of the forward steps), and `R' k` Markov
kernels (inexact inner RGO samplers) with `tvSup (R' k y) (rgoKernel f (η k) y) ≤ ε k` for every
`y` (a uniform TV oracle condition, in place of the SPS paper's KL condition (7)). Let
`ν (k+1) = (R' k ∘ₖ forwardKernel (η k)) ∘ₘ ν k` be the inexact proximal chain from a probability
law `ν 0`. Under the named hypothesis `TVContraction (proxKernel f (η k)) (target f) ρ` for every
`k`, with `0 ≤ ρ`,
`tvSup (ν K) (target f) ≤ ρ^K tvSup (ν 0) (target f) + ∑_{k<K} ρ^(K-1-k) ε k`. The hypothesis
holds with `ρ = 1` (`tvContraction_proxKernel`), giving the additive bound; with `ρ < 1` it would
make the proximal kernel uniformly ergodic, which is not expected on `ℝ` with unbounded support
(module docstring; not formalised), so for a geometric rate use `tvSup_inexactProx_le_along`, of
which this is a special case. -/
theorem tvSup_inexactProx_le (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℕ → ℝ} (hη : ∀ k, 0 < η k)
    {R' : ℕ → Kernel ℝ ℝ} [∀ k, IsMarkovKernel (R' k)] {ε : ℕ → ℝ}
    (hR : ∀ k y, tvSup (R' k y) (Proximal.rgoKernel f (η k) y) ≤ ε k) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hP : ∀ k, TVContraction (Proximal.proxKernel f (η k)) (Proximal.target f) ρ)
    {ν : ℕ → Measure ℝ} [IsProbabilityMeasure (ν 0)]
    (hν : ∀ k, ν (k + 1) = (R' k ∘ₖ Proximal.forwardKernel (η k)) ∘ₘ ν k) (K : ℕ) :
    tvSup (ν K) (Proximal.target f) ≤
      ρ ^ K * tvSup (ν 0) (Proximal.target f) + ∑ k ∈ range K, ρ ^ (K - 1 - k) * ε k := by
  have : ∀ k, IsMarkovKernel (Proximal.forwardKernel (η k)) :=
    fun k => Proximal.isMarkovKernel_forwardKernel (hη k)
  exact tvSup_inexactProx_le_along hf hint hη hν hρ
    (fun k _ => hP k (ν k) (isProbabilityMeasure_of_comp_succ hν k)) fun k _ => hR k

end ErrorDecomposition
end FormalizeSampling
