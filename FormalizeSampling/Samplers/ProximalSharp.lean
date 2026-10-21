module

public import FormalizeSampling.Samplers.ProximalContraction
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Samplers.GaussianIncrement
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# PX-2, sharp form: the exact proximal sampler contracts KL by `(1 + α η)^{-2}` per step

Registry ID: **PX-2** (sharp form; complements `Samplers/ProximalContraction.lean`, which
proves the forward-step factor `(1 + α η)^{-1}` only).

Status: **Conditional** for the rate (Part 1), **Verified** for its tightness (Part 2).

Setting as in `Samplers/Proximal.lean`: target `π = target f` on `ℝ`, step `η > 0` (the
**variance** of the forward Gaussian), forward kernel `forwardKernel η`, restricted Gaussian
oracle `rgoKernel f η`, and `proxKernel f η = rgoKernel f η ∘ₖ forwardKernel η`. Divergences are
`klDiv μ ν = KL(μ‖ν)` with the current law first and the target second.

## Part 1: the rate `(1 + α η)^{-2}` (Conditional)

Following Chen, Chewi, Salim and Wibisono (2022), each half-step contracts by `1/(1 + α η)`:
* forward step (`ProximalContraction`): `KL(ρ^Y‖π^Y) ≤ KL(ρ‖π) / (1 + α η)` with
  `ρ^Y = forwardKernel η ∘ₘ ρ`, `π^Y = forwardKernel η ∘ₘ π`, from the named hypotheses
  `HeatFlowDissipation` and `HeatFlowLSI`;
* backward step (here): `KL(rgoKernel f η ∘ₘ μ‖π) ≤ KL(μ‖π^Y) / (1 + α η)` for any input `μ`,
  from the named hypotheses `BackwardHeatFlowDissipation` (de Bruijn identity along the backward
  heat flow that realises the RGO, with endpoints linked to the two literal `klDiv` terms) and
  `BackwardHeatFlowLSI` (LSI(`α / (1 + α (η - t))`) of the reference marginals
  `π * N(0, η - t)`). These give `Kb' ≤ -(α / (1 + α (η - t))) Kb`, and the fully proved
  backward Grönwall comparison `le_div_of_hasDerivWithinAt_le_backward` closes the step.

Main results: `toReal_klDiv_rgoKernel_comp_le` (backward SDPI),
`toReal_klDiv_proxKernel_comp_le_sq` (one step, `(1 + α η)^{-2}`),
`toReal_klDiv_iterate_le_sq` (`k` steps, `(1 + α η)^{-2k}`), `tvSup_iterate_le_sq` (Pinsker).

## Part 2: tightness on Gaussians (Verified)

For `f_α(x) = α x²/2` (`gaussPotential`, `α > 0`), `π = N(0, 1/α)` (`target_gaussPotential`,
in `Foundations/GibbsMeasure.lean`),
the RGO is `N(y/(1 + α η), η/(1 + α η))` (`rgoKernel_gaussPotential_apply`) and
`proxKernel ∘ₘ N(m, 1/α) = N(m/(1 + α η), 1/α)` (`proxKernel_comp_gaussianReal_invVar`), so
`KL(N(m, 1/α)‖π) = α m²/2` drops by exactly `(1 + α η)^2` per step
(`klDiv_proxKernel_comp_gaussTarget`, `klDiv_iterate_gaussTarget`). Consequently no per-step
constant below `(1 + α η)^{-2}` holds for all LSI(`α`) targets (`not_exists_rate_lt`), and the
forward-only factor is strict on these examples (`toReal_klDiv_proxKernel_comp_gaussTarget_lt`).
That `N(0, 1/α)` satisfies LSI(`α`) is the classical Gaussian log-Sobolev inequality, proved as
`GaussianFunctionalLSI.functionalLSI_gaussianReal` (functional form; `Fin d → ℝ`:
`GaussianFunctionalLSIPi.functionalLSIPi_gaussian`) and, in KL form for positive differentiable
densities with finite second moment and Fisher information, as `GaussianLSIZero.klDiv_le_fisher0`
(`Fin d → ℝ`: `GaussianLSIZeroPi.klDiv_le_fisher0`).

## Not proved here

* The backward heat flow (reverse SDE), the identification of its endpoint kernel with the RGO,
  de Bruijn's identity along it, and LSI under Gaussian convolution: these are the named
  hypotheses. They follow (for an explicit affine curve) from the backward SDPI by
  `ProximalSharpLSI.exists_backwardHeatFlow_of_le`; that SDPI is proved from a functional LSI of
  the target in `Samplers/ProximalSharpLSI.lean`.
* Only the one-dimensional state space `ℝ`, matching `Samplers/Proximal.lean`; the `Fin d → ℝ`
  version is `Samplers/ProximalSharpPi.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.Proximal FormalizeSampling.ProximalContraction
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalSharp

/-! ### Backward time-varying Grönwall comparison (fully proved) -/

/-- **Backward time-varying Grönwall comparison.** Let `α ≥ 0`, `η ≥ 0` and `K : ℝ → ℝ` be
continuous on `[0, η]` with right derivative `K' t` at every `t ∈ [0, η)` satisfying the
differential inequality `K' t ≤ -(α / (1 + α (η - t))) K t` (the rate increases from
`α / (1 + α η)` at `t = 0` to `α` at `t = η`). Then `K η ≤ K 0 / (1 + α η)`.

Proof: `t ↦ K t / (1 + α (η - t))` has right derivative
`(K' t (1 + α (η - t)) + α K t) / (1 + α (η - t))² ≤ 0`, hence its value `K η` at `t = η` does
not exceed its value `K 0 / (1 + α η)` at `t = 0`. No sign assumption on `K` is needed. This is
the time-reversed counterpart of `ProximalContraction.le_div_of_hasDerivWithinAt_le`. -/
theorem le_div_of_hasDerivWithinAt_le_backward {α η : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η)
    {K K' : ℝ → ℝ} (hcont : ContinuousOn K (Icc 0 η))
    (hderiv : ∀ t ∈ Ico 0 η, HasDerivWithinAt K (K' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 η, K' t ≤ -(α / (1 + α * (η - t))) * K t) :
    K η ≤ K 0 / (1 + α * η) := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) η, 0 < 1 + α * (η - t) := fun t ht => by
    nlinarith [ht.2, mul_nonneg hα (sub_nonneg.2 ht.2)]
  set g : ℝ → ℝ := fun t => K t / (1 + α * (η - t)) with hg
  have hgc : ContinuousOn g (Icc 0 η) :=
    hcont.div (by fun_prop) fun t ht => (hpos t ht).ne'
  have hgd : ∀ t ∈ Ico 0 η, HasDerivWithinAt g
      ((K' t * (1 + α * (η - t)) - K t * (-α)) / (1 + α * (η - t)) ^ 2) (Ici t) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t : ℝ => 1 + α * (η - t)) (-α) (Ici t) t := by
      simpa using (((hasDerivAt_id t).const_sub η).const_mul α).const_add 1
        |>.hasDerivWithinAt
    exact (hderiv t ht).div h1 (hpos t (Ico_subset_Icc_self ht)).ne'
  have hgb : ∀ t ∈ Ico 0 η,
      (K' t * (1 + α * (η - t)) - K t * (-α)) / (1 + α * (η - t)) ^ 2 ≤ 0 := by
    intro t ht
    have hp := hpos t (Ico_subset_Icc_self ht)
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have := mul_le_mul_of_nonneg_right (hbound t ht) hp.le
    have heq : -(α / (1 + α * (η - t))) * K t * (1 + α * (η - t)) = -(α * K t) := by
      field_simp
    linarith
  have key := image_le_of_deriv_right_le_deriv_boundary (B := fun _ => g 0) (B' := fun _ => 0)
    hgc hgd le_rfl continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _) hgb
    (right_mem_Icc.2 hη)
  simpa [hg] using key

/-! ### The backward (RGO) step: named hypotheses -/

/-- **Named hypothesis: dissipation along the backward heat flow of the RGO step.**

Fix a potential `f` (target `π = target f`), a step `η > 0`, and a law `μ` on `ℝ` (the input of
the RGO step; in the proximal sampler `μ = forwardKernel η ∘ₘ ρ`). Write `π^Y = forwardKernel η
∘ₘ π = π * N(0, η)`. The classical picture (Chen–Chewi–Salim–Wibisono 2022, Lemma on the
backward step) is: run the **backward heat flow** of `π`, i.e. the time-reversal of
`dX = dB` started at `π`, for times `t ∈ [0, η]`; its marginals are `π_{η - t}` with
`π_s = π * N(0, s)`, so it carries `π^Y` at `t = 0` to `π` at `t = η`, and the conditional law of
its endpoint given the start `y` is exactly the RGO `rgoKernel f η y`. Started instead from `μ`,
it has marginals `μ_t` with `μ_0 = μ` and `μ_η = rgoKernel f η ∘ₘ μ`. Since `μ_t` and `π_{η - t}`
evolve under the same Fokker–Planck equation, the de Bruijn-type identity
`d/dt KL(μ_t‖π_{η - t}) = -½ I(μ_t‖π_{η - t})` holds (relative Fisher information `I`).

This structure abstracts that picture by a real curve `Kb` (intended: `Kb t = KL(μ_t‖π_{η-t})`)
and a function `Ib` (intended: `Ib t = I(μ_t‖π_{η-t})`), and asserts only:
* `start`: `Kb 0 ≤ KL(μ‖π^Y).toReal` (with equality in the intended instance);
* `finish`: `KL(rgoKernel f η ∘ₘ μ‖π).toReal ≤ Kb η` (with equality in the intended instance);
* `continuousOn`: `Kb` is continuous on `[0, η]`;
* `hasDerivWithinAt_le`: at each `t ∈ [0, η)`, `Kb` has a right derivative `≤ -½ Ib t`.

None of this (the reverse SDE, its marginals, the identification of the endpoint kernel with the
RGO, de Bruijn's identity along it, or the regularity of `Kb`) is proved here.

Since `Kb`, `Ib` are free curves, `BackwardHeatFlowDissipation f η μ Kb Ib ∧
BackwardHeatFlowLSI α η Kb Ib` (for some `Kb, Ib`) is equivalent to the conclusion of
`toReal_klDiv_rgoKernel_comp_le` (converse: `ProximalSharpLSI.exists_backwardHeatFlow_of_le`); it
does not force `Kb` to be the KL along the backward flow.

**Superseded.** The backward-step contraction is proved from a functional LSI of the target and
the explicit regularity conditions `ProximalSharpLSI.BackwardHeatFlowRegular` in
`ProximalSharpLSI.toReal_klDiv_rgoKernel_comp_le_of_targetLSI`, and the final form of PX-2
(`ProximalGeneralLSI.toReal_klDiv_iterate_le_sq_general`, on `Fin d → ℝ`
`ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general`) needs no backward named
hypothesis. -/
structure BackwardHeatFlowDissipation (f : ℝ → ℝ) (η : ℝ) (μ : Measure ℝ) (Kb Ib : ℝ → ℝ) :
    Prop where
  /-- The curve starts below `KL(μ‖π^Y)`, `π^Y = forwardKernel η ∘ₘ target f`. -/
  start : Kb 0 ≤ (klDiv μ (forwardKernel η ∘ₘ target f)).toReal
  /-- The curve ends above `KL(rgoKernel f η ∘ₘ μ‖π)`, `π = target f`. -/
  finish : (klDiv (rgoKernel f η ∘ₘ μ) (target f)).toReal ≤ Kb η
  /-- The curve is continuous on `[0, η]`. -/
  continuousOn : ContinuousOn Kb (Icc 0 η)
  /-- At every `t ∈ [0, η)` the right derivative exists and is at most `-½ Ib(t)`. -/
  hasDerivWithinAt_le : ∀ t ∈ Ico 0 η,
    ∃ K' : ℝ, HasDerivWithinAt Kb K' (Ici t) t ∧ K' ≤ -(1 / 2) * Ib t

/-- **Named hypothesis: log-Sobolev inequality along the backward heat flow.** For `α ≥ 0`, a
horizon `η` and real curves `Kb, Ib` (as in `BackwardHeatFlowDissipation`), it asserts for every
`t ∈ [0, η)`: `2 α · Kb t ≤ (1 + α (η - t)) · Ib t`, i.e.
`KL(μ_t‖π_{η-t}) ≤ I(μ_t‖π_{η-t}) / (2 α_{η-t})` with `α_s = α / (1 + α s)`.

It packages the classical fact that if `π` satisfies LSI(`α`) then `π_s = π * N(0, s)` satisfies
LSI(`α / (1 + α s)`) (stability of LSI under convolution; `N(0, s)` satisfies LSI(`1/s`)),
applied at `s = η - t` to the test law `μ_t` of the backward flow. It is **not** proved here.
Superseded in the same way as `BackwardHeatFlowDissipation` (see there). -/
def BackwardHeatFlowLSI (α η : ℝ) (Kb Ib : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ico 0 η, 2 * α * Kb t ≤ (1 + α * (η - t)) * Ib t

/-- **Backward-step strong data processing (Conditional).** Let `α ≥ 0`, `η ≥ 0`, `f` a
potential, `μ` a law on `ℝ`, and `Kb, Ib` with `BackwardHeatFlowDissipation f η μ Kb Ib` and
`BackwardHeatFlowLSI α η Kb Ib`. Then, with `π = target f` and `π^Y = forwardKernel η ∘ₘ π`,
`KL(rgoKernel f η ∘ₘ μ‖π).toReal ≤ KL(μ‖π^Y).toReal / (1 + α η)`. -/
theorem toReal_klDiv_rgoKernel_comp_le {f : ℝ → ℝ} {α η : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η)
    {μ : Measure ℝ} {Kb Ib : ℝ → ℝ} (hD : BackwardHeatFlowDissipation f η μ Kb Ib)
    (hL : BackwardHeatFlowLSI α η Kb Ib) :
    (klDiv (rgoKernel f η ∘ₘ μ) (target f)).toReal
      ≤ (klDiv μ (forwardKernel η ∘ₘ target f)).toReal / (1 + α * η) := by
  choose! K' hK' hK'le using hD.hasDerivWithinAt_le
  have hpos : 0 < 1 + α * η := by nlinarith
  have hG : Kb η ≤ Kb 0 / (1 + α * η) := by
    refine le_div_of_hasDerivWithinAt_le_backward hα hη hD.continuousOn hK' fun t ht => ?_
    have hp : 0 < 1 + α * (η - t) := by
      nlinarith [ht.2, mul_nonneg hα (sub_nonneg.2 ht.2.le)]
    have hL' := hL t ht
    have h1 : α / (1 + α * (η - t)) * Kb t ≤ (1 / 2) * Ib t := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hp]
      linarith
    linarith [hK'le t ht]
  calc (klDiv (rgoKernel f η ∘ₘ μ) (target f)).toReal ≤ Kb η := hD.finish
    _ ≤ Kb 0 / (1 + α * η) := hG
    _ ≤ _ := div_le_div_of_nonneg_right hD.start hpos.le

/-! ### PX-2, sharp rate: one step and iteration (Conditional) -/

variable {f : ℝ → ℝ} {η : ℝ}

/-- The proximal output is the RGO image of the forward image:
`proxKernel f η ∘ₘ ρ = rgoKernel f η ∘ₘ (forwardKernel η ∘ₘ ρ)` (no assumptions). -/
theorem proxKernel_comp_eq (f : ℝ → ℝ) (η : ℝ) (ρ : Measure ℝ) :
    proxKernel f η ∘ₘ ρ = rgoKernel f η ∘ₘ (forwardKernel η ∘ₘ ρ) := by
  rw [proxKernel, Measure.comp_assoc]

/-- **PX-2, sharp one-step rate (Conditional).** Let `f` be measurable with integrable
`exp ∘ (-f)`, `π = target f`, `η > 0`, `α ≥ 0`, and `ρ` a finite law on `ℝ` with
`KL(ρ‖π) < ∞`. Assume
* the forward-step named hypotheses `HeatFlowDissipation ρ π η I` and `HeatFlowLSI ρ π α η I`
  (de Bruijn along the heat flow `ρ * N(0, t)`, LSI(`α / (1 + α t)`) of `π * N(0, t)`), and
* the backward-step named hypotheses `BackwardHeatFlowDissipation f η (forwardKernel η ∘ₘ ρ) Kb Ib`
  and `BackwardHeatFlowLSI α η Kb Ib` (de Bruijn along the backward heat flow realising the RGO,
  LSI(`α / (1 + α (η - t))`) of its reference marginals).

Then `KL(proxKernel f η ∘ₘ ρ‖π) < ∞` and
`KL(proxKernel f η ∘ₘ ρ‖π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)²`
(Chen–Chewi–Salim–Wibisono 2022). The rate is attained by Gaussians:
`klDiv_proxKernel_comp_gaussTarget`. -/
theorem toReal_klDiv_proxKernel_comp_le_sq (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hKL : klDiv ρ (target f) ≠ ∞) {I Kb Ib : ℝ → ℝ}
    (hD : HeatFlowDissipation ρ (target f) η I) (hL : HeatFlowLSI ρ (target f) α η I)
    (hDb : BackwardHeatFlowDissipation f η (forwardKernel η ∘ₘ ρ) Kb Ib)
    (hLb : BackwardHeatFlowLSI α η Kb Ib) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≠ ∞ ∧
      (klDiv (proxKernel f η ∘ₘ ρ) (target f)).toReal
        ≤ (klDiv ρ (target f)).toReal / (1 + α * η) ^ 2 := by
  have hpos : 0 < 1 + α * η := by nlinarith
  refine ⟨(ProximalContraction.toReal_klDiv_proxKernel_comp_le hf hint hη hα ρ hKL hD hL).1, ?_⟩
  rw [proxKernel_comp_eq]
  calc _ ≤ (klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ target f)).toReal
        / (1 + α * η) := toReal_klDiv_rgoKernel_comp_le hα hη.le hDb hLb
    _ ≤ (klDiv ρ (target f)).toReal / (1 + α * η) / (1 + α * η) :=
        div_le_div_of_nonneg_right (toReal_klDiv_forwardKernel_le hα hη hD hL) hpos.le
    _ = _ := by rw [div_div, sq]

/-- **PX-2, sharp rate, iterated (Conditional).** Let `f` be measurable with integrable
`exp ∘ (-f)`, `π = target f`, `η > 0`, `α ≥ 0`, and `ρ : ℕ → Measure ℝ` the proximal-sampler
laws: `ρ 0` a probability measure with `KL(ρ 0‖π) < ∞`, `ρ (k+1) = proxKernel f η ∘ₘ ρ k`.
Assume at every step `k` the forward named hypotheses `HeatFlowDissipation (ρ k) π η (I k)`,
`HeatFlowLSI (ρ k) π α η (I k)` and the backward named hypotheses
`BackwardHeatFlowDissipation f η (forwardKernel η ∘ₘ ρ k) (Kb k) (Ib k)`,
`BackwardHeatFlowLSI α η (Kb k) (Ib k)`. Then for every `k`, `ρ k` is a probability measure,
`KL(ρ k‖π) < ∞` and `KL(ρ k‖π).toReal ≤ KL(ρ 0‖π).toReal / (1 + α η)^(2k)`. -/
theorem toReal_klDiv_iterate_le_sq (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ∞)
    {I Kb Ib : ℕ → ℝ → ℝ} (hD : ∀ k, HeatFlowDissipation (ρ k) (target f) η (I k))
    (hL : ∀ k, HeatFlowLSI (ρ k) (target f) α η (I k))
    (hDb : ∀ k, BackwardHeatFlowDissipation f η (forwardKernel η ∘ₘ ρ k) (Kb k) (Ib k))
    (hLb : ∀ k, BackwardHeatFlowLSI α η (Kb k) (Ib k)) (k : ℕ) :
    IsProbabilityMeasure (ρ k) ∧ klDiv (ρ k) (target f) ≠ ∞ ∧
      (klDiv (ρ k) (target f)).toReal
        ≤ (klDiv (ρ 0) (target f)).toReal / (1 + α * η) ^ (2 * k) := by
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_rgoKernel hf hint hη
  have hpos : 0 < 1 + α * η := by nlinarith
  induction k with
  | zero => exact ⟨inferInstance, hKL, by simp⟩
  | succ k ih =>
    obtain ⟨hprob, hfin, hle⟩ := ih
    have := hprob
    obtain ⟨hfin', hle'⟩ :=
      toReal_klDiv_proxKernel_comp_le_sq hf hint hη hα (ρ k) hfin (hD k) (hL k) (hDb k) (hLb k)
    rw [hstep k]
    refine ⟨by unfold proxKernel; infer_instance, hfin', hle'.trans ?_⟩
    rw [mul_add, mul_one, pow_add, ← div_div]
    exact div_le_div_of_nonneg_right hle (by positivity)

/-- **PX-2, sharp rate in total variation (Conditional).** Under the hypotheses of
`toReal_klDiv_iterate_le_sq`, with `tvSup μ ν = sup_A |μ A - ν A|` and Pinsker's inequality:
`tvSup (ρ k) π ≤ √(KL(ρ 0‖π).toReal / (2 (1 + α η)^(2k)))` for every `k`. -/
theorem tvSup_iterate_le_sq (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) (hη : 0 < η) {α : ℝ} (hα : 0 ≤ α)
    (ρ : ℕ → Measure ℝ) [IsProbabilityMeasure (ρ 0)]
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (hKL : klDiv (ρ 0) (target f) ≠ ∞)
    {I Kb Ib : ℕ → ℝ → ℝ} (hD : ∀ k, HeatFlowDissipation (ρ k) (target f) η (I k))
    (hL : ∀ k, HeatFlowLSI (ρ k) (target f) α η (I k))
    (hDb : ∀ k, BackwardHeatFlowDissipation f η (forwardKernel η ∘ₘ ρ k) (Kb k) (Ib k))
    (hLb : ∀ k, BackwardHeatFlowLSI α η (Kb k) (Ib k)) (k : ℕ) :
    TotalVariation.tvSup (ρ k) (target f)
      ≤ √((klDiv (ρ 0) (target f)).toReal / (2 * (1 + α * η) ^ (2 * k))) := by
  obtain ⟨hprob, hfin, hle⟩ :=
    toReal_klDiv_iterate_le_sq hf hint hη hα ρ hstep hKL hD hL hDb hLb k
  have := hprob
  have := isProbabilityMeasure_target hint
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans (Real.sqrt_le_sqrt ?_)
  rw [mul_comm 2, ← div_div]
  exact div_le_div_of_nonneg_right hle zero_le_two

/-! ### Tightness: the Gaussian target attains `(1 + α η)^{-2}` (Verified) -/

section Gaussian

open FormalizeSampling.OU

private theorem coe_rgoVar' {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ((η / (1 + α * η)).toNNReal : ℝ) = η / (1 + α * η) :=
  Real.coe_toNNReal _ (by positivity)

private theorem rgoVar_ne_zero' {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    (η / (1 + α * η)).toNNReal ≠ 0 := by
  rw [ne_eq, Real.toNNReal_eq_zero, not_le]
  positivity

/-- **Completing the square.** For `α, η > 0` and all `y, x`:
`exp(-α x²/2 - (x - y)²/(2η)) = C · N(x; y/(1 + αη), η/(1 + αη))` with the positive constant
`C = exp(-α y²/(2(1 + αη))) √(2π η/(1 + αη))`. -/
theorem rgo_integrand_gaussPotential {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (y x : ℝ) :
    Real.exp (-gaussPotential α x - (x - y) ^ 2 / (2 * η)) =
      (Real.exp (-(α * y ^ 2) / (2 * (1 + α * η))) *
        Real.sqrt (2 * Real.pi * ((η / (1 + α * η)).toNNReal : ℝ))) *
        gaussianPDFReal (y / (1 + α * η)) (η / (1 + α * η)).toNNReal x := by
  have hv : 0 < ((η / (1 + α * η)).toNNReal : ℝ) := by rw [coe_rgoVar' hα hη]; positivity
  rw [gaussianPDFReal, mul_assoc, ← mul_assoc (Real.sqrt _), mul_inv_cancel₀ (by positivity),
    one_mul, ← Real.exp_add]
  congr 1
  rw [coe_rgoVar' hα hη, gaussPotential]
  field_simp
  ring

/-- **Conjugate RGO kernel.** For `α, η > 0`, the exact RGO for `f_α(x) = α x²/2` at `y` is
`N(y/(1 + αη), η/(1 + αη))`. -/
theorem rgoKernel_gaussPotential_apply {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (y : ℝ) :
    rgoKernel (gaussPotential α) η y =
      gaussianReal (y / (1 + α * η)) (η / (1 + α * η)).toNNReal := by
  have hv : 0 < ((η / (1 + α * η)).toNNReal : ℝ) := by rw [coe_rgoVar' hα hη]; positivity
  have hd : ∀ x, rgoDensity (gaussPotential α) η y x =
      gaussianPDFReal (y / (1 + α * η)) (η / (1 + α * η)).toNNReal x :=
    MeasureHelpers.div_integral_eq_gaussianPDFReal (rgoVar_ne_zero' hα hη) (by positivity)
      (rgo_integrand_gaussPotential hα hη y)
  rw [rgoKernel_apply (measurable_gaussPotential α) (integrable_exp_neg_gaussPotential hα) hη,
    gaussianReal_of_var_ne_zero _ (rgoVar_ne_zero' hα hη), gaussianPDF_def]
  simp_rw [hd]

/-- For `α, η > 0`, the exact RGO kernel for `f_α` is the affine Gaussian kernel
`y ↦ N(y/(1 + αη) + 0, η/(1 + αη))`. -/
theorem rgoKernel_gaussPotential {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    rgoKernel (gaussPotential α) η =
      (affineGaussianKernel (1 / (1 + α * η)) (η / (1 + α * η)).toNNReal).map (· + 0) := by
  ext1 y
  rw [rgoKernel_gaussPotential_apply hα hη, Kernel.map_apply _ (measurable_add_const _),
    affineGaussianKernel_apply, gaussianReal_map_add_const, add_zero, one_div_mul_eq_div]

/-- **Exact proximal step of a Gaussian, target `N(0, 1/α)`.** For `α, η > 0` and `m : ℝ`,
`proxKernel f_α η ∘ₘ N(m, 1/α) = N(m/(1 + αη), 1/α)`: the variance is preserved and the mean
contracts by exactly `1/(1 + αη)`. -/
theorem proxKernel_comp_gaussianReal_invVar {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (m : ℝ) :
    proxKernel (gaussPotential α) η ∘ₘ gaussianReal m (α⁻¹).toNNReal =
      gaussianReal (m / (1 + α * η)) (α⁻¹).toNNReal := by
  rw [proxKernel_comp_eq, forwardKernel_comp_gaussianReal hη, rgoKernel_gaussPotential hα hη,
    affineGaussian_map_comp_gaussianReal]
  congr 1
  · rw [add_zero, one_div_mul_eq_div]
  · apply NNReal.eq
    rw [NNReal.coe_add]
    erw [NNReal.coe_mul, NNReal.coe_mk]
    rw [NNReal.coe_add, coe_rgoVar' hα hη, coe_invVar hα, Real.coe_toNNReal _ hη.le]
    field_simp

/-- **KL of the Gaussian iterate.** For `α > 0`, with `π = target f_α = N(0, 1/α)`:
`KL(N(m, 1/α)‖π) = α m²/2` (via `GaussianIncrement.klDiv_gaussianReal_gaussianReal`). -/
theorem klDiv_gaussianReal_gaussTarget {α : ℝ} (hα : 0 < α) (m : ℝ) :
    klDiv (gaussianReal m (α⁻¹).toNNReal) (target (gaussPotential α))
      = ENNReal.ofReal (α * m ^ 2 / 2) := by
  rw [target_gaussPotential hα,
    GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ (invVar_ne_zero hα), coe_invVar hα]
  congr 1
  field_simp
  ring

/-- **Tightness of the sharp PX-2 rate (Verified).** For `α, η > 0`, the Gaussian target
`π = target f_α = N(0, 1/α)` (`f_α(x) = α x²/2`), and the initial law `ρ = N(m, 1/α)`:
`proxKernel f_α η ∘ₘ ρ = N(m/(1 + αη), 1/α)` and
`KL(proxKernel f_α η ∘ₘ ρ‖π) = α m²/(2 (1 + αη)²) = KL(ρ‖π) / (1 + αη)²`
(as an identity in `ℝ≥0∞`). Since `π = N(0, 1/α)` satisfies LSI(`α`) (the Gaussian
log-Sobolev inequality, `GaussianFunctionalLSI.functionalLSI_gaussianReal`), the per-step factor
`(1 + αη)^{-2}` of `toReal_klDiv_proxKernel_comp_le_sq` is attained, and the forward-only factor
`(1 + αη)^{-1}` of `ProximalContraction.toReal_klDiv_proxKernel_comp_le` is not tight
(`toReal_klDiv_proxKernel_comp_gaussTarget_lt`). This sharpness on Gaussian targets is observed by
Chen–Chewi–Salim–Wibisono (2022, arXiv:2202.06386, §4.4); see also Mitra–Wibisono (2025,
arXiv:2410.10699, App. G.2). -/
theorem klDiv_proxKernel_comp_gaussTarget {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (m : ℝ) :
    proxKernel (gaussPotential α) η ∘ₘ gaussianReal m (α⁻¹).toNNReal =
        gaussianReal (m / (1 + α * η)) (α⁻¹).toNNReal ∧
      klDiv (proxKernel (gaussPotential α) η ∘ₘ gaussianReal m (α⁻¹).toNNReal)
          (target (gaussPotential α))
        = ENNReal.ofReal (α * m ^ 2 / (2 * (1 + α * η) ^ 2)) ∧
      klDiv (proxKernel (gaussPotential α) η ∘ₘ gaussianReal m (α⁻¹).toNNReal)
          (target (gaussPotential α))
        = klDiv (gaussianReal m (α⁻¹).toNNReal) (target (gaussPotential α))
          / ENNReal.ofReal ((1 + α * η) ^ 2) := by
  have hpos : 0 < 1 + α * η := by positivity
  have h1 := proxKernel_comp_gaussianReal_invVar hα hη m
  have h2 : klDiv (proxKernel (gaussPotential α) η ∘ₘ gaussianReal m (α⁻¹).toNNReal)
      (target (gaussPotential α)) = ENNReal.ofReal (α * m ^ 2 / (2 * (1 + α * η) ^ 2)) := by
    rw [h1, klDiv_gaussianReal_gaussTarget hα]
    congr 1
    field_simp
  refine ⟨h1, h2, ?_⟩
  rw [h2, klDiv_gaussianReal_gaussTarget hα, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Tightness, iterated (Verified).** For `α, η > 0`, `π = target f_α = N(0, 1/α)`, and the
proximal-sampler laws `ρ : ℕ → Measure ℝ` with `ρ 0 = N(m, 1/α)` and
`ρ (k+1) = proxKernel f_α η ∘ₘ ρ k`: for every `k`, `ρ k = N(m/(1 + αη)^k, 1/α)` and
`KL(ρ k‖π).toReal = KL(ρ 0‖π).toReal / (1 + αη)^(2k)` exactly, matching the bound of
`toReal_klDiv_iterate_le_sq` with equality. -/
theorem klDiv_iterate_gaussTarget {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (m : ℝ)
    (ρ : ℕ → Measure ℝ) (h0 : ρ 0 = gaussianReal m (α⁻¹).toNNReal)
    (hstep : ∀ k, ρ (k + 1) = proxKernel (gaussPotential α) η ∘ₘ ρ k) (k : ℕ) :
    ρ k = gaussianReal (m / (1 + α * η) ^ k) (α⁻¹).toNNReal ∧
      (klDiv (ρ k) (target (gaussPotential α))).toReal
        = (klDiv (ρ 0) (target (gaussPotential α))).toReal / (1 + α * η) ^ (2 * k) := by
  have hpos : 0 < 1 + α * η := by positivity
  have hlaw : ρ k = gaussianReal (m / (1 + α * η) ^ k) (α⁻¹).toNNReal := by
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [hstep k, ih, proxKernel_comp_gaussianReal_invVar hα hη, pow_succ, div_div]
  refine ⟨hlaw, ?_⟩
  rw [hlaw, h0, klDiv_gaussianReal_gaussTarget hα, klDiv_gaussianReal_gaussTarget hα,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  field_simp
  ring

/-- **No better per-step constant (Verified).** For `α, η > 0` and the Gaussian target
`π = target f_α = N(0, 1/α)` (which satisfies LSI(`α`),
`GaussianFunctionalLSI.functionalLSI_gaussianReal`),
there is no constant `c < 1/(1 + αη)²` such that
`KL(proxKernel f_α η ∘ₘ ρ‖π).toReal ≤ c · KL(ρ‖π).toReal` for every probability law `ρ` with
`KL(ρ‖π) < ∞`. Witness: `ρ = N(1, 1/α)`, for which `KL(ρ‖π) = α/2 > 0` and the sharp bound is an
equality (`klDiv_proxKernel_comp_gaussTarget`). -/
theorem not_exists_rate_lt {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ¬ ∃ c < 1 / (1 + α * η) ^ 2, ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      klDiv ρ (target (gaussPotential α)) ≠ ∞ →
      (klDiv (proxKernel (gaussPotential α) η ∘ₘ ρ) (target (gaussPotential α))).toReal
        ≤ c * (klDiv ρ (target (gaussPotential α))).toReal := by
  rintro ⟨c, hc, h⟩
  have hpos : 0 < 1 + α * η := by positivity
  have hρ := h (gaussianReal 1 (α⁻¹).toNNReal) inferInstance
    (by rw [klDiv_gaussianReal_gaussTarget hα]; exact ENNReal.ofReal_ne_top)
  rw [(klDiv_proxKernel_comp_gaussTarget hα hη 1).2.1, klDiv_gaussianReal_gaussTarget hα,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hρ
  have h2 : 0 < α * 1 ^ 2 / 2 := by positivity
  have h3 : α * 1 ^ 2 / (2 * (1 + α * η) ^ 2) = 1 / (1 + α * η) ^ 2 * (α * 1 ^ 2 / 2) := by
    field_simp
  rw [h3] at hρ
  exact absurd (le_of_mul_le_mul_right hρ h2) (not_le.2 hc)

/-- **The forward-only rate is not tight (Verified).** For `α, η > 0`, `π = N(0, 1/α)` and
`ρ = N(m, 1/α)` with `m ≠ 0`:
`KL(proxKernel f_α η ∘ₘ ρ‖π).toReal < KL(ρ‖π).toReal / (1 + αη)`, so the bound of
`ProximalContraction.toReal_klDiv_proxKernel_comp_le` holds strictly here. -/
theorem toReal_klDiv_proxKernel_comp_gaussTarget_lt {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    {m : ℝ} (hm : m ≠ 0) :
    (klDiv (proxKernel (gaussPotential α) η ∘ₘ gaussianReal m (α⁻¹).toNNReal)
        (target (gaussPotential α))).toReal
      < (klDiv (gaussianReal m (α⁻¹).toNNReal) (target (gaussPotential α))).toReal
        / (1 + α * η) := by
  have hpos : 0 < 1 + α * η := by positivity
  rw [(klDiv_proxKernel_comp_gaussTarget hα hη m).2.1, klDiv_gaussianReal_gaussTarget hα,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hm2 : 0 < α * m ^ 2 := by positivity
  have hgt : 1 + α * η < (1 + α * η) ^ 2 := by nlinarith [mul_pos hα hη]
  rw [div_lt_div_iff₀ (by positivity) hpos]
  nlinarith [mul_lt_mul_of_pos_left hgt hm2]

end Gaussian

end FormalizeSampling.ProximalSharp
