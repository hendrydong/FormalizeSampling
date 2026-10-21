module

public import FormalizeSampling.Samplers.Proximal
public import FormalizeSampling.Kernels.GaussianKernels
public import FormalizeSampling.Foundations.Pinsker

/-!
# PX-2: KL contraction of the exact proximal sampler under a log-Sobolev inequality

Status: **Conditional** (the de Bruijn identity along the heat flow and the propagation of a
log-Sobolev inequality under Gaussian convolution are packaged as named hypotheses). These named
hypotheses are superseded by the final form of PX-2 (`Samplers/ProximalGeneralLSI.lean`,
`Samplers/ProximalGeneralLSIPi.lean`), which assumes only a functional LSI and a Gaussian upper
envelope of the target; for `α, η > 0`, `HeatFlowLSI` with `I = heatFisher` is unsatisfiable
when `0 < KL(ρ‖π) < ∞` (see its docstring).

Setting (as in `Samplers/Proximal.lean`): target `π = target f` on `ℝ`, step `η > 0` (the
**variance** of the forward Gaussian), forward kernel `forwardKernel η` (`y ~ N(x, η)`),
backward kernel `rgoKernel f η` (the restricted Gaussian oracle), and the exact proximal step
`proxKernel f η = rgoKernel f η ∘ₖ forwardKernel η`. All divergences are `klDiv μ ν = KL(μ‖ν)`
with the **iterate (or current law) in the first argument and the target in the second**.

We follow the forward-step part of the argument of Chen, Chewi, Salim and Wibisono (2022):

1. **Forward step along the heat flow.** Let `ρ_t = heatKernel t ∘ₘ ρ` (`= ρ * N(0, t)`),
   `π_t = heatKernel t ∘ₘ π` and `K(t) = KL(ρ_t‖π_t)` (`heatKL ρ π t`, as a real number).
   de Bruijn's identity gives `K'(t) = -½ I(t)` with `I(t)` the relative Fisher information
   `I(ρ_t‖π_t)`; this is the named hypothesis `HeatFlowDissipation` (only the inequality
   `K'(t) ≤ -½ I(t)`, as a right derivative, is required). If `π` satisfies LSI(`α`), then
   `π_t` satisfies LSI(`α / (1 + α t)`), i.e. `K(t) ≤ (1 + α t) I(t) / (2 α)`; this is the
   named hypothesis `HeatFlowLSI` (only needed along the curve `ρ_t`). Together they give the
   differential inequality `K'(t) ≤ -(α / (1 + α t)) K(t)`, and the fully proved
   time-varying Grönwall comparison `le_div_of_hasDerivWithinAt_le` yields
   `K(η) ≤ K(0) / (1 + α η)`.
2. **Backward step.** By PX-1 (`isReverseKernel_rgoKernel`),
   `rgoKernel f η ∘ₘ (forwardKernel η ∘ₘ π) = π`, so the data-processing inequality
   (Mathlib's `klDiv_comp_right_le`) gives
   `KL(proxKernel ∘ₘ ρ ‖ π) ≤ KL(forwardKernel η ∘ₘ ρ ‖ forwardKernel η ∘ₘ π)`
   (`klDiv_proxKernel_comp_le_forward`, unconditional).
3. **Iteration.** `KL(ρ_k‖π) ≤ KL(ρ_0‖π) / (1 + α η)^k` for `ρ_{k+1} = proxKernel ∘ₘ ρ_k`,
   given the named hypotheses at every step, and the corresponding TV bound via Pinsker.

## Main results

* `le_div_of_hasDerivWithinAt_le` (fully proved): if `K` is continuous on `[0, η]`, has right
  derivatives `K'` on `[0, η)` with `K'(t) ≤ -(α / (1 + α t)) K(t)`, and `α ≥ 0`, then
  `K(η) ≤ K(0) / (1 + α η)`.
* `heatKL_le_div` (Conditional): the forward-step bound `K(η) ≤ K(0) / (1 + α η)`.
* `klDiv_proxKernel_comp_le_forward`, `klDiv_proxKernel_comp_le` (unconditional): backward-step
  data processing, and plain non-expansiveness `KL(proxKernel ∘ₘ ρ‖π) ≤ KL(ρ‖π)`.
* `toReal_klDiv_proxKernel_comp_le` (**PX-2**, Conditional): one-step contraction
  `KL(proxKernel ∘ₘ ρ‖π) ≤ KL(ρ‖π) / (1 + α η)`.
* `toReal_klDiv_iterate_le`, `tvSup_iterate_le` (Conditional): `k`-step KL and TV bounds.
* `forwardKernel_comp_gaussianReal`: the forward step maps `N(m, v)` to `N(m, v + η)`;
  `forwardKernel_eq` and `affineGaussian_map_comp_gaussianReal` (mixing `N(c x + b, w)` over
  `x ~ N(m, v)` gives `N(c m + b, c² v + w)`) are the affine-Gaussian form used for it.

## Not proved here

* The de Bruijn identity and the LSI-under-convolution statement (they are the named
  hypotheses); in particular nothing is said about when `K` is differentiable.
* The sharper rate `(1 + α η)^{-2}` per step of Chen–Chewi–Salim–Wibisono, which additionally
  needs the strong data-processing inequality for the backward (RGO) step along the reverse
  heat flow; only the forward-step factor `(1 + α η)^{-1}` is obtained here (the sharp rate is
  in `ProximalSharp`, `ProximalSharpLSI` and `ProximalStronglyLogConcave`).
* Only the one-dimensional state space `ℝ`; on `Fin d → ℝ` the forward step is
  `ProximalLSIPi` and the sharp rate `ProximalSharpLSIPi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.Proximal FormalizeSampling.ReverseKernel
open scoped ENNReal NNReal FormalizeSampling.OU

namespace FormalizeSampling.ProximalContraction

/-! ### Time-varying Grönwall comparison (fully proved) -/

/-- **Time-varying Grönwall comparison.** Let `α ≥ 0`, `η ≥ 0` and `K : ℝ → ℝ` be continuous on
`[0, η]` with right derivative `K' t` at every `t ∈ [0, η)` satisfying the differential
inequality `K' t ≤ -(α / (1 + α t)) K t`. Then `K η ≤ K 0 / (1 + α η)`.

Proof: `t ↦ (1 + α t) K t` has right derivative `α K t + (1 + α t) K' t ≤ 0`, hence does not
exceed its value `K 0` at `t = 0`. No sign assumption on `K` is needed. -/
theorem le_div_of_hasDerivWithinAt_le {α η : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η) {K K' : ℝ → ℝ}
    (hcont : ContinuousOn K (Icc 0 η))
    (hderiv : ∀ t ∈ Ico 0 η, HasDerivWithinAt K (K' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 η, K' t ≤ -(α / (1 + α * t)) * K t) :
    K η ≤ K 0 / (1 + α * η) := by
  set g : ℝ → ℝ := fun t => (1 + α * t) * K t with hg
  have hgc : ContinuousOn g (Icc 0 η) :=
    ((continuousOn_const.add (continuousOn_const.mul continuousOn_id))).mul hcont
  have hgd : ∀ t ∈ Ico 0 η,
      HasDerivWithinAt g (α * K t + (1 + α * t) * K' t) (Ici t) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t : ℝ => 1 + α * t) α (Ici t) t := by
      simpa using ((hasDerivAt_id t).const_mul α).const_add 1 |>.hasDerivWithinAt
    exact h1.mul (hderiv t ht)
  have hgb : ∀ t ∈ Ico 0 η, α * K t + (1 + α * t) * K' t ≤ 0 := by
    intro t ht
    have hpos : 0 < 1 + α * t := by nlinarith [ht.1]
    have := mul_le_mul_of_nonneg_left (hbound t ht) hpos.le
    have heq : (1 + α * t) * (-(α / (1 + α * t)) * K t) = -(α * K t) := by
      field_simp
    linarith
  have key := image_le_of_deriv_right_le_deriv_boundary (B := fun _ => g 0) (B' := fun _ => 0)
    hgc hgd le_rfl continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _) hgb
    (right_mem_Icc.2 hη)
  have hpos : 0 < 1 + α * η := by nlinarith
  rw [le_div_iff₀ hpos]
  simpa [hg, mul_comm] using key

/-! ### The heat flow and the named hypotheses -/

/-- **Named hypothesis: de Bruijn dissipation along the heat flow on `[0, η]`.**
For laws `ρ, π` on `ℝ`, a horizon `η` and a function `I : ℝ → ℝ` (intended to be the relative
Fisher information `I(ρ_t‖π_t) = ∫ |∂ₓ log(dρ_t/dπ_t)|² dρ_t`), it asserts that
`K(t) = heatKL ρ π t = KL(ρ_t‖π_t)` is continuous on `[0, η]` and has, at every `t ∈ [0, η)`,
a right derivative `K'(t) ≤ -½ I(t)`.

This packages the classical **de Bruijn identity** `d/dt KL(ρ * N(0,t) ‖ π * N(0,t)) =
-½ I(ρ_t‖π_t)` (both laws evolve by the same heat equation `∂ₜ p = ½ ∂ₓₓ p`), together with the
regularity making `K` continuous at `t = 0`. It is **not** proved here; only the inequality
`≤` is used.

**Superseded.** This hypothesis and `HeatFlowLSI` are the inputs of the conditional forms of
PX-2 in this file and in `ProximalSharp`. `HeatFlowDeBruijn.heatKL_le_div_of_regular` proves the
de Bruijn step from the concrete condition `HeatFlowDeBruijn.HeatFlowRegular`, and the final form
of PX-2 (`ProximalGeneralLSI.toReal_klDiv_iterate_le_sq_general`, on `Fin d → ℝ`
`ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general`) needs neither hypothesis: it
assumes only a functional LSI of the target and a Gaussian upper envelope. -/
structure HeatFlowDissipation (ρ π : Measure ℝ) (η : ℝ) (I : ℝ → ℝ) : Prop where
  /-- `t ↦ KL(ρ_t‖π_t)` is continuous on `[0, η]`. -/
  continuousOn : ContinuousOn (heatKL ρ π) (Icc 0 η)
  /-- At every `t ∈ [0, η)` the right derivative exists and is at most `-½ I(t)`. -/
  hasDerivWithinAt_le : ∀ t ∈ Ico 0 η,
    ∃ K' : ℝ, HasDerivWithinAt (heatKL ρ π) K' (Ici t) t ∧ K' ≤ -(1 / 2) * I t

/-- **Named hypothesis: log-Sobolev inequality along the heat flow.**

**Warning: unsatisfiable with `I = HeatFlowDeBruijn.heatFisher ρ π` when `0 < KL(ρ‖π) < ∞`.**
The slot `t = 0` is included and `heatFisher ρ π 0 = 0`, so for `α, η > 0` the hypothesis then
forces `KL(ρ‖π).toReal ≤ 0`, i.e. `KL(ρ‖π) = 0` when the divergence is finite
(`GaussianLSI.toReal_klDiv_nonpos_of_heatFlowLSI`; Gaussian instance:
`Audit.ProximalGeneral.not_heatFlowLSI_heatFisher_gauss`). It can be discharged only with a
hand-supplied `I`, such as the closed-form Fisher information of a Gaussian pair
(`Audit.ProximalGeneral.heatFlowLSI_gauss`). It is superseded by the final form of PX-2, which
assumes only a functional LSI of the target and a Gaussian upper envelope:
`ProximalGeneralLSI.toReal_klDiv_iterate_le_sq_general` (on `ℝ`) and
`ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general` (on `Fin d → ℝ`); for the forward
step alone, `HeatFlowDeBruijn.heatKL_le_div_of_regular` needs the LSI only on `(0, η)`.

For laws `ρ, π` on `ℝ`, a constant `α ≥ 0`, a horizon `η` and a function `I : ℝ → ℝ` (the
relative Fisher information of `HeatFlowDissipation`), it asserts, for every `t ∈ [0, η)`,
`2 α · KL(ρ_t‖π_t) ≤ (1 + α t) · I(t)`, i.e. `KL(ρ_t‖π_t) ≤ I(ρ_t‖π_t) / (2 α_t)` with
`α_t = α / (1 + α t)` (written without division so that `α = 0` is allowed).

This packages the classical facts that, if `π` satisfies LSI(`α`) (in the form
`KL(μ‖π) ≤ I(μ‖π) / (2α)`), then `π_t = π * N(0, t)` satisfies LSI(`α / (1 + α t)`) (LSI is
stable under convolution, and `N(0, t)` satisfies LSI(`1/t`)), applied to the test law `ρ_t`.
Only the instances along the single curve `t ↦ ρ_t` are required. It is **not** proved here;
`I` is a free function. -/
def HeatFlowLSI (ρ π : Measure ℝ) (α η : ℝ) (I : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ico 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * I t

/-- **Forward-step contraction (Conditional).** For laws `ρ, π` on `ℝ`, `α ≥ 0`, `η ≥ 0`, and a
function `I` such that `HeatFlowDissipation ρ π η I` (de Bruijn) and `HeatFlowLSI ρ π α η I`
(LSI of `π_t` with constant `α / (1 + α t)`) hold, the KL along the heat flow satisfies
`KL(ρ_η‖π_η) ≤ KL(ρ_0‖π_0) / (1 + α η)` (as real numbers, `heatKL ρ π`). -/
theorem heatKL_le_div {ρ π : Measure ℝ} {α η : ℝ} {I : ℝ → ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hD : HeatFlowDissipation ρ π η I) (hL : HeatFlowLSI ρ π α η I) :
    heatKL ρ π η ≤ heatKL ρ π 0 / (1 + α * η) := by
  choose! K' hK' hK'le using hD.hasDerivWithinAt_le
  refine le_div_of_hasDerivWithinAt_le hα hη hD.continuousOn hK' fun t ht => ?_
  have hpos : 0 < 1 + α * t := by nlinarith [ht.1]
  have hL' := hL t ht
  have h1 : α / (1 + α * t) * heatKL ρ π t ≤ (1 / 2) * I t := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  linarith [hK'le t ht]

/-! ### Identifying the endpoints of the heat flow -/

/-- For `η > 0`, the heat kernel with variance `η` is the proximal forward kernel:
`heatKernel η.toNNReal = forwardKernel η`. -/
theorem heatKernel_toNNReal_eq_forwardKernel {η : ℝ} (hη : 0 < η) :
    OU.heatKernel η.toNNReal = forwardKernel η := by
  ext x : 1
  rw [OU.heatKernel_apply, forwardKernel_apply hη]

/-- For `η > 0`, `heatKL ρ π η = KL(forwardKernel η ∘ₘ ρ ‖ forwardKernel η ∘ₘ π).toReal`. -/
theorem heatKL_eq_forwardKernel (ρ π : Measure ℝ) {η : ℝ} (hη : 0 < η) :
    heatKL ρ π η = (klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ π)).toReal := by
  rw [heatKL, heatKernel_toNNReal_eq_forwardKernel hη]

/-- **Forward step of the proximal sampler (Conditional).** For finite laws `ρ, π` on `ℝ`,
`α ≥ 0`, `η > 0` and `I` with `HeatFlowDissipation ρ π η I` and `HeatFlowLSI ρ π α η I`:
`KL(forwardKernel η ∘ₘ ρ ‖ forwardKernel η ∘ₘ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_forwardKernel_le {ρ π : Measure ℝ} {α η : ℝ} {I : ℝ → ℝ} (hα : 0 ≤ α)
    (hη : 0 < η) (hD : HeatFlowDissipation ρ π η I) (hL : HeatFlowLSI ρ π α η I) :
    (klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ π)).toReal
      ≤ (klDiv ρ π).toReal / (1 + α * η) := by
  rw [← heatKL_eq_forwardKernel ρ π hη, ← heatKL_zero ρ π]
  exact heatKL_le_div hα hη.le hD hL

/-! ### Backward step: data processing (unconditional) -/

variable {f : ℝ → ℝ} {η : ℝ}

/-- **Backward step (data processing, unconditional).** For measurable `f` with integrable
`exp ∘ (-f)`, `η > 0` and any finite law `ρ` on `ℝ`, with `π = target f`:
`KL(proxKernel f η ∘ₘ ρ ‖ π) ≤ KL(forwardKernel η ∘ₘ ρ ‖ forwardKernel η ∘ₘ π)`.
Proof: `π = rgoKernel f η ∘ₘ (forwardKernel η ∘ₘ π)` (PX-1) and KL data processing for the
Markov kernel `rgoKernel f η`. -/
theorem klDiv_proxKernel_comp_le_forward (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] :
    klDiv (proxKernel f η ∘ₘ ρ) (target f)
      ≤ klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target f) := by
  have := isMarkovKernel_rgoKernel hf hint hη
  have := isMarkovKernel_forwardKernel hη
  have := isFiniteMeasure_target f
  have hinv : rgoKernel f η ∘ₘ (forwardKernel η ∘ₘ target f) = target f :=
    (isReverseKernel_rgoKernel hf hint hη).comp_marginal
  conv_lhs => rw [← hinv, proxKernel, ← Measure.comp_assoc]
  exact klDiv_comp_right_le _ _ _

/-- **Non-expansiveness of the proximal step (unconditional).** For measurable `f` with
integrable `exp ∘ (-f)`, `η > 0` and any finite law `ρ`:
`KL(proxKernel f η ∘ₘ ρ ‖ π) ≤ KL(ρ‖π)` with `π = target f` (data processing and PX-1). -/
theorem klDiv_proxKernel_comp_le (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≤ klDiv ρ (target f) := by
  have := isMarkovKernel_forwardKernel hη
  have := isFiniteMeasure_target f
  exact (klDiv_proxKernel_comp_le_forward hf hint hη ρ).trans (klDiv_comp_right_le _ _ _)

/-! ### PX-2: one-step and iterated contraction (Conditional) -/

/-- **PX-2: KL contraction of the exact proximal sampler under LSI (Conditional).**
Let `f` be measurable with integrable `exp ∘ (-f)`, `π = target f`, `η > 0`, `α ≥ 0`, and `ρ`
a finite law on `ℝ` with `KL(ρ‖π) < ∞`. Assume, for some `I : ℝ → ℝ`, the named hypotheses
`HeatFlowDissipation ρ π η I` (de Bruijn along the heat flow) and `HeatFlowLSI ρ π α η I`
(LSI of `π * N(0, t)` with constant `α / (1 + α t)`, as implied by LSI(`α`) for `π`). Then
`KL(proxKernel f η ∘ₘ ρ ‖ π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ ‖ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`.
(Only the forward-step factor; the backward SDPI giving `(1 + α η)^{-2}` is not used.) -/
theorem toReal_klDiv_proxKernel_comp_le (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hKL : klDiv ρ (target f) ≠ ∞) {I : ℝ → ℝ}
    (hD : HeatFlowDissipation ρ (target f) η I) (hL : HeatFlowLSI ρ (target f) α η I) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ∞ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) := by
  have := isMarkovKernel_forwardKernel hη
  have := isFiniteMeasure_target f
  have hfwd : klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target f) ≠ ∞ :=
    ne_top_of_le_ne_top hKL (klDiv_comp_right_le _ _ _)
  have hback := klDiv_proxKernel_comp_le_forward hf hint hη ρ
  refine ⟨ne_top_of_le_ne_top hfwd hback, ?_⟩
  exact (ENNReal.toReal_mono hfwd hback).trans (toReal_klDiv_forwardKernel_le hα hη hD hL)

/-- **PX-2, iterated (Conditional).** Let `f` be measurable with integrable `exp ∘ (-f)`,
`π = target f`, `η > 0`, `α ≥ 0`, and let `ρ : ℕ → Measure ℝ` be the proximal-sampler laws:
`ρ 0` a probability measure with `KL(ρ 0‖π) < ∞` and `ρ (k+1) = proxKernel f η ∘ₘ ρ k`.
Assume at every step `k` the named hypotheses `HeatFlowDissipation (ρ k) π η (I k)` and
`HeatFlowLSI (ρ k) π α η (I k)`. Then for every `k`, `KL(ρ k‖π) < ∞` and
`KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^k`. -/
theorem toReal_klDiv_iterate_le (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ∞)
    {I : ℕ → ℝ → ℝ} (hD : ∀ k, HeatFlowDissipation (ρ k) (target f) η (I k))
    (hL : ∀ k, HeatFlowLSI (ρ k) (target f) α η (I k)) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (target f) ≠ ∞ ∧
      (klDiv (ρ k) (target f)).toReal
        ≤ (klDiv (ρ 0) (target f)).toReal / (1 + α * η) ^ k := by
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_rgoKernel hf hint hη
  have hpos : 0 < 1 + α * η := by nlinarith
  induction k with
  | zero => exact ⟨inferInstance, hKL, by simp⟩
  | succ k ih =>
    obtain ⟨hprob, hfin, hle⟩ := ih
    have := hprob
    obtain ⟨hfin', hle'⟩ :=
      toReal_klDiv_proxKernel_comp_le hf hint hη hα (ρ k) hfin (hD k) (hL k)
    rw [hstep k]
    refine ⟨by unfold proxKernel; infer_instance, hfin', hle'.trans ?_⟩
    rw [pow_succ, ← div_div]
    exact div_le_div_of_nonneg_right hle hpos.le

/-- **PX-2 in total variation (Conditional).** Under the hypotheses of
`toReal_klDiv_iterate_le`, with the TV distance `tvSup μ ν = sup_A |μ A - ν A|` and Pinsker's
inequality: `tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^k))` for every `k`. -/
theorem tvSup_iterate_le (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ∞)
    {I : ℕ → ℝ → ℝ} (hD : ∀ k, HeatFlowDissipation (ρ k) (target f) η (I k))
    (hL : ∀ k, HeatFlowLSI (ρ k) (target f) α η (I k)) (k : ℕ) :
    TotalVariation.tvSup (ρ k) (target f)
      ≤ √((klDiv (ρ 0) (target f)).toReal / (2 * (1 + α * η) ^ k)) := by
  obtain ⟨hprob, hfin, hle⟩ := toReal_klDiv_iterate_le hf hint hη hα ρ hstep hKL hD hL k
  have := hprob
  have := isProbabilityMeasure_target hint
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans (Real.sqrt_le_sqrt ?_)
  rw [mul_comm 2, ← div_div]
  exact div_le_div_of_nonneg_right hle zero_le_two

/-! ### Gaussian propagation through the forward step -/

section ForwardGaussian

open FormalizeSampling.OU

/-- **Affine Gaussian kernel with offset, applied to a Gaussian.** For `c, b, m : ℝ` and
variances `w, v : ℝ≥0`, mixing `N(c x + b, w)` over `x ~ N(m, v)` gives
`N(c m + b, c² v + w)` (via `OU.bind_affineGaussian` and Mathlib's Gaussian convolution). -/
theorem affineGaussian_map_comp_gaussianReal (c b : ℝ) (w : ℝ≥0) (m : ℝ) (v : ℝ≥0) :
    (affineGaussianKernel c w).map (· + b) ∘ₘ gaussianReal m v =
      gaussianReal (c * m + b) (⟨c ^ 2, sq_nonneg _⟩ * v + w) := by
  rw [← Measure.map_comp _ _ (measurable_add_const b)]
  have h : affineGaussianKernel c w ∘ₘ gaussianReal m v =
      (gaussianReal m v).bind (fun x => gaussianReal (c * x) w) := rfl
  rw [h, bind_affineGaussian, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal,
    add_zero, gaussianReal_map_add_const]
  rfl

/-- The forward kernel (`η > 0`) is the affine Gaussian kernel `x ↦ N(1 · x + 0, η)`. -/
theorem forwardKernel_eq {η : ℝ} (hη : 0 < η) :
    forwardKernel η = (affineGaussianKernel 1 η.toNNReal).map (· + 0) := by
  ext1 x
  rw [forwardKernel_apply hη, Kernel.map_apply _ (measurable_add_const _),
    affineGaussianKernel_apply, gaussianReal_map_add_const, one_mul, add_zero]

/-- **Forward step of a Gaussian.** For `η > 0`: `G_η(N(m, v)) = N(m, v + η)`. -/
theorem forwardKernel_comp_gaussianReal {η : ℝ} (hη : 0 < η) (m : ℝ) (v : ℝ≥0) :
    forwardKernel η ∘ₘ gaussianReal m v = gaussianReal m (v + η.toNNReal) := by
  rw [forwardKernel_eq hη, affineGaussian_map_comp_gaussianReal, add_zero]
  congr 1
  · exact one_mul m
  · apply NNReal.eq
    change (1 ^ 2 : ℝ) * v + η.toNNReal = v + η.toNNReal
    simp

end ForwardGaussian

end FormalizeSampling.ProximalContraction
