module

public import FormalizeSampling.Samplers.BackwardHeatFlow
public import FormalizeSampling.Foundations.HeatFlowDeBruijnPi
public import FormalizeSampling.Foundations.LogSobolevExtensionPi
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The backward heat flow of the RGO step on `Fin d → ℝ`: abstract de Bruijn identity, LSI bridge

Status: **Verified** (abstract analysis; every hypothesis is an explicit regularity or
integrability assumption, none of them is the identity or inequality being proved).

This is the `Fin d → ℝ` version of `Samplers/BackwardHeatFlow.lean`. The concrete backward flow
of the RGO step is built in `Samplers/ProximalSharpLSIPi.lean`; here everything is stated for
abstract families.

Setting. Let `W, U : ℝ → (Fin d → ℝ) → ℝ` (time, space) with `U > 0`, gradients `WG, UG` and
Hessians `WH, UH` given explicitly, solving the *backward* and the *forward* heat equation,
`∂_t W = -½ ΔW` and `∂_t U = ½ ΔU` (`Δ = ∑ᵢ ∂ᵢ²`). In the intended instance
`W t = π * N(0, (η - t) I)` and `U t = N(0, t I) * r` with `r = dμ/dπ^Y`, so that `p_t = W t · U t`
is the backward marginal and `∫ W U log U = KL(p_t‖W t)`.

As in `Foundations/HeatFlowDeBruijnPi.lean`, the integration by parts is done one coordinate at a
time (`KLTransport.integral_partialDeriv_eq_zero`), and vanishing boundary flux is replaced by
integrability of each flux coordinate `bklFluxPi i` and of its partial derivative
`bklFluxDerivPi i`.

## Main results

* `hasDerivAt_bklIntegrandPi_time`, `hasFDerivAt_bklFluxPi`, `sum_bklFluxDerivPi`: pointwise
  identities `∂_t [W U log U] = bklRatePi` and `∑ᵢ ∂ᵢ (bklFluxPi i) = 2 bklRatePi + W |∇U|² / U`.
* `integral_bklRatePi_eq`: `∫ bklRatePi = -½ ∫ W |∇U|² / U`.
* `hasDerivAt_integral_bklIntegrandPi` (**backward de Bruijn identity**):
  `d/dt ∫ W U log U = -½ ∫ W |∇U|² / U` under domination and integrability hypotheses.
* `integral_mul_log_le_of_functionalLSIPi` (**LSI bridge**): if `ν = q dx` (`q > 0`) satisfies
  `FunctionalLSIPi ν C` (`C ≥ 0`) and `u > 0` is differentiable with continuous gradient, with
  `∫ q u = 1`, then `∫ q u log u ≤ (C/2) ∫ q |∇u|² / u`, given integrability of both sides (no
  boundedness of `u`, via `LogSobolevExtensionPi.ent_sq_le_of_functionalLSIPi` applied to
  `√u`).

The interior backward Grönwall comparison is dimension free and is reused from
`BackwardHeatFlow.le_div_of_hasDerivAt_interior`.

## Not proved here

* Nothing about a concrete flow: the identification with the RGO step and the regularity of
  the concrete backward flow are in `Samplers/ProximalSharpLSIPi.lean` and
  `Samplers/BackwardHeatFlowRegularityWarmPi.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevPi
open FormalizeSampling.HeatFlowDeBruijnPi (dotCLM dotCLM_apply dotCLM_single)

namespace FormalizeSampling.BackwardHeatFlowPi

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_withDensity_ofReal_iff)

variable {d : ℕ}

/-! ### Abstract backward de Bruijn identity -/

section Abstract

variable {W U : ℝ → (Fin d → ℝ) → ℝ} {WG UG : ℝ → (Fin d → ℝ) → Fin d → ℝ}
  {WH UH : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ}

/-- The backward relative-entropy integrand `W · (U log U)`; for `p = W U` this is
`p log(p / W)`. -/
noncomputable def bklIntegrandPi (W U : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  W t x * (U t x * Real.log (U t x))

/-- The time derivative of `bklIntegrandPi` along `∂_t W = -½ ΔW`, `∂_t U = ½ ΔU`
(`hasDerivAt_bklIntegrandPi_time`): `(W ΔU (log U + 1) - ΔW U log U) / 2`, with the Laplacians
written as traces of the given Hessians. -/
noncomputable def bklRatePi (W U : ℝ → (Fin d → ℝ) → ℝ)
    (WH UH : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  (W t x * (∑ i, UH t x i i) * (Real.log (U t x) + 1)
    - (∑ i, WH t x i i) * (U t x * Real.log (U t x))) / 2

/-- The backward relative Fisher integrand `W |∇U|² / U` (Euclidean norm, written with
`dotProduct`); for `p = W U` this is `p |∇ log(p / W)|²`. -/
noncomputable def bFisherIntegrandPi (W U : ℝ → (Fin d → ℝ) → ℝ)
    (UG : ℝ → (Fin d → ℝ) → Fin d → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  W t x * (UG t x ⬝ᵥ UG t x) / U t x

/-- The `i`-th coordinate of the backward flux `W ∂ᵢU (log U + 1) - ∂ᵢW U log U`. -/
noncomputable def bklFluxPi (W U : ℝ → (Fin d → ℝ) → ℝ) (WG UG : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (t : ℝ) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  W t x * UG t x i * (Real.log (U t x) + 1) - WG t x i * (U t x * Real.log (U t x))

/-- The `i`-th partial derivative of the `i`-th backward flux coordinate:
`W ∂ᵢ²U (log U + 1) - ∂ᵢ²W U log U + W (∂ᵢU)² / U` (`hasFDerivAt_bklFluxPi`). -/
noncomputable def bklFluxDerivPi (W U : ℝ → (Fin d → ℝ) → ℝ)
    (UG : ℝ → (Fin d → ℝ) → Fin d → ℝ) (WH UH : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (t : ℝ) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  W t x * UH t x i i * (Real.log (U t x) + 1) - WH t x i i * (U t x * Real.log (U t x))
    + W t x * UG t x i ^ 2 / U t x

/-- The divergence of the backward flux: `∑ᵢ bklFluxDerivPi i = 2 · bklRatePi + W |∇U|² / U`
(pure algebra, no assumptions). -/
theorem sum_bklFluxDerivPi (t : ℝ) (x : Fin d → ℝ) :
    ∑ i, bklFluxDerivPi W U UG WH UH t i x =
      2 * bklRatePi W U WH UH t x + bFisherIntegrandPi W U UG t x := by
  unfold bklFluxDerivPi bklRatePi bFisherIntegrandPi
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum, dotProduct]
  simp only [sq]
  ring

/-- Pointwise time derivative of the backward KL integrand. If `U t x > 0`,
`∂_t W(·, x) = -½ ∑ᵢ WHᵢᵢ` and `∂_t U(·, x) = ½ ∑ᵢ UHᵢᵢ` at `t`, then
`∂_t [W U log U] = bklRatePi`. -/
theorem hasDerivAt_bklIntegrandPi_time {t : ℝ} {x : Fin d → ℝ} (hU : 0 < U t x)
    (hWt : HasDerivAt (fun r => W r x) (-((∑ i, WH t x i i) / 2)) t)
    (hUt : HasDerivAt (fun r => U r x) ((∑ i, UH t x i i) / 2) t) :
    HasDerivAt (fun r => bklIntegrandPi W U r x) (bklRatePi W U WH UH t x) t := by
  have h := hWt.mul (hUt.mul (hUt.log hU.ne'))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold bklRatePi
  field_simp
  ring

/-- Pointwise space derivative of the `i`-th backward flux coordinate. If `U t x > 0`,
`∇W = WG`, `∇U = UG` and the `i`-th gradient coordinates have gradients `(WH t x i j)ⱼ`,
`(UH t x i j)ⱼ` at `x`, then `bklFluxPi t i` is Fréchet differentiable at `x` and its `i`-th
partial derivative is `bklFluxDerivPi t i x`. -/
theorem hasFDerivAt_bklFluxPi {t : ℝ} {x : Fin d → ℝ} (i : Fin d) (hU : 0 < U t x)
    (hWx : HasFDerivAt (W t) (dotCLM (WG t x)) x) (hUx : HasFDerivAt (U t) (dotCLM (UG t x)) x)
    (hWxx : HasFDerivAt (fun y => WG t y i) (dotCLM fun j => WH t x i j) x)
    (hUxx : HasFDerivAt (fun y => UG t y i) (dotCLM fun j => UH t x i j) x) :
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, HasFDerivAt (bklFluxPi W U WG UG t i) L x ∧
      L (Pi.single i 1) = bklFluxDerivPi W U UG WH UH t i x := by
  have hlog := hUx.log hU.ne'
  have hF := ((hWx.mul hUxx).mul (hlog.add_const 1)).sub (hWxx.mul (hUx.mul hlog))
  refine ⟨_, hF, ?_⟩
  simp only [sub_apply, add_apply, smul_apply, dotCLM_single, smul_eq_mul, Pi.mul_apply]
  unfold bklFluxDerivPi
  field_simp
  ring

/-- **Integration-by-parts step of the backward de Bruijn identity on `Fin d → ℝ`.** At a fixed
time `t`, if `U t > 0`, `W t`, `U t` are twice differentiable (gradients `WG`, `UG`, Hessian rows
`WH`, `UH`), the Fisher integrand is integrable, and every flux coordinate `bklFluxPi t i` and
its partial derivative `bklFluxDerivPi t i` are Lebesgue integrable, then
`∫ bklRatePi = -½ ∫ W |∇U|² / U`. -/
theorem integral_bklRatePi_eq {t : ℝ} (hU : ∀ x, 0 < U t x)
    (hWx : ∀ x, HasFDerivAt (W t) (dotCLM (WG t x)) x)
    (hUx : ∀ x, HasFDerivAt (U t) (dotCLM (UG t x)) x)
    (hWxx : ∀ i x, HasFDerivAt (fun y => WG t y i) (dotCLM fun j => WH t x i j) x)
    (hUxx : ∀ i x, HasFDerivAt (fun y => UG t y i) (dotCLM fun j => UH t x i j) x)
    (hfisher : Integrable (bFisherIntegrandPi W U UG t))
    (hflux : ∀ i, Integrable (bklFluxPi W U WG UG t i))
    (hfluxD : ∀ i, Integrable (bklFluxDerivPi W U UG WH UH t i)) :
    ∫ x, bklRatePi W U WH UH t x = -(1 / 2) * ∫ x, bFisherIntegrandPi W U UG t x := by
  have hd : ∀ i x, DifferentiableAt ℝ (bklFluxPi W U WG UG t i) x ∧
      partialDeriv i (bklFluxPi W U WG UG t i) x = bklFluxDerivPi W U UG WH UH t i x := by
    intro i x
    obtain ⟨L, hL, hLv⟩ := hasFDerivAt_bklFluxPi i (hU x) (hWx x) (hUx x) (hWxx i x) (hUxx i x)
    exact ⟨hL.differentiableAt, by rw [partialDeriv, hL.fderiv, hLv]⟩
  have h0 : ∀ i, ∫ x, bklFluxDerivPi W U UG WH UH t i x = 0 := by
    intro i
    have e : (fun x => bklFluxDerivPi W U UG WH UH t i x) =
        fun x => partialDeriv i (bklFluxPi W U WG UG t i) x := funext fun x => (hd i x).2.symm
    rw [e]
    exact KLTransport.integral_partialDeriv_eq_zero i (fun x => (hd i x).1) (hflux i)
      (e ▸ hfluxD i)
  have hsum : ∫ x, ∑ i, bklFluxDerivPi W U UG WH UH t i x = 0 := by
    rw [integral_finsetSum _ fun i _ => hfluxD i]
    simp [h0]
  have e : ∀ x, bklRatePi W U WH UH t x =
      ((∑ i, bklFluxDerivPi W U UG WH UH t i x) - bFisherIntegrandPi W U UG t x) / 2 := by
    intro x; rw [sum_bklFluxDerivPi]; ring
  simp_rw [e]
  rw [integral_div, integral_sub (integrable_finsetSum _ fun i _ => hfluxD i) hfisher, hsum]
  ring

/-- **Backward de Bruijn identity on `Fin d → ℝ` (abstract form).** Let `s ∈ 𝓝 t₀`. Assume, for
all `t ∈ s` and all `x`: `U t x > 0`; `∂_t W = -½ ∑ᵢ WHᵢᵢ`, `∂_t U = ½ ∑ᵢ UHᵢᵢ`; `∇W = WG`,
`∇U = UG`; and at `t₀` the gradient coordinates have Hessian rows `WH`, `UH`. Assume
`W t₀ U t₀ log U t₀` is integrable, `bklRatePi` is dominated on `s` by an integrable `bound`, the
Fisher integrand at `t₀` is integrable and every flux coordinate and its partial derivative at
`t₀` are integrable. Then `d/dt ∫ W_t U_t log U_t dx = -½ ∫ W_{t₀} |∇U_{t₀}|² / U_{t₀} dx` at
`t = t₀`. -/
theorem hasDerivAt_integral_bklIntegrandPi {s : Set ℝ} {t₀ : ℝ} (hs : s ∈ 𝓝 t₀)
    (hU : ∀ t ∈ s, ∀ x, 0 < U t x)
    (hWt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => W r x) (-((∑ i, WH t x i i) / 2)) t)
    (hUt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => U r x) ((∑ i, UH t x i i) / 2) t)
    (hWx : ∀ t ∈ s, ∀ x, HasFDerivAt (W t) (dotCLM (WG t x)) x)
    (hUx : ∀ t ∈ s, ∀ x, HasFDerivAt (U t) (dotCLM (UG t x)) x)
    (hWxx : ∀ i x, HasFDerivAt (fun y => WG t₀ y i) (dotCLM fun j => WH t₀ x i j) x)
    (hUxx : ∀ i x, HasFDerivAt (fun y => UG t₀ y i) (dotCLM fun j => UH t₀ x i j) x)
    (hint : Integrable (bklIntegrandPi W U t₀)) {bound : (Fin d → ℝ) → ℝ}
    (hbound_int : Integrable bound) (hbound : ∀ t ∈ s, ∀ x, |bklRatePi W U WH UH t x| ≤ bound x)
    (hfisher : Integrable (bFisherIntegrandPi W U UG t₀))
    (hflux : ∀ i, Integrable (bklFluxPi W U WG UG t₀ i))
    (hfluxD : ∀ i, Integrable (bklFluxDerivPi W U UG WH UH t₀ i)) :
    HasDerivAt (fun t => ∫ x, bklIntegrandPi W U t x)
      (-(1 / 2) * ∫ x, bFisherIntegrandPi W U UG t₀ x) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  have hWc : ∀ t ∈ s, Continuous (W t) := fun t ht =>
    continuous_iff_continuousAt.2 fun x => (hWx t ht x).continuousAt
  have hUc : ∀ t ∈ s, Continuous (U t) := fun t ht =>
    continuous_iff_continuousAt.2 fun x => (hUx t ht x).continuousAt
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (bklIntegrandPi W U t) volume := by
    filter_upwards [hs] with t ht
    exact ((hWc t ht).mul ((hUc t ht).mul ((hUc t ht).log fun x => (hU t ht x).ne'))
      ).aestronglyMeasurable
  have hHm : ∀ (H : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ) (G : ℝ → (Fin d → ℝ) → Fin d → ℝ),
      (∀ i x, HasFDerivAt (fun y => G t₀ y i) (dotCLM fun j => H t₀ x i j) x) →
      Measurable fun x => ∑ i, H t₀ x i i := by
    intro H G hG
    refine Finset.measurable_sum _ fun i _ => ?_
    have e : (fun x => H t₀ x i i) = fun x => fderiv ℝ (fun y => G t₀ y i) x (Pi.single i 1) :=
      funext fun x => by rw [(hG i x).fderiv, dotCLM_single]
    rw [e]
    exact measurable_fderiv_apply_const ℝ _ _
  have hWm := (hWc t₀ ht₀).measurable
  have hUm := (hUc t₀ ht₀).measurable
  have hrate_meas : AEStronglyMeasurable (bklRatePi W U WH UH t₀) volume := by
    unfold bklRatePi
    exact (((hWm.mul (hHm UH UG hUxx)).mul (hUm.log.add_const 1)).sub
      ((hHm WH WG hWxx).mul (hUm.mul hUm.log))).div_const 2 |>.aestronglyMeasurable
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint
    hrate_meas (Eventually.of_forall fun x t ht => by simpa using hbound t ht x) hbound_int
    (Eventually.of_forall fun x t ht =>
      hasDerivAt_bklIntegrandPi_time (hU t ht x) (hWt t ht x) (hUt t ht x))
  rwa [integral_bklRatePi_eq (hU t₀ ht₀) (hWx t₀ ht₀) (hUx t₀ ht₀) hWxx hUxx hfisher hflux
    hfluxD] at hderiv

end Abstract

/-! ### The LSI bridge for a reference law with a density -/

section Bridge

variable {q : (Fin d → ℝ) → ℝ}

/-- **LSI bridge on `Fin d → ℝ`.** Let `q ≥ 0` be measurable with
`ν = volume.withDensity (ofReal ∘ q)` a probability measure satisfying `FunctionalLSIPi ν C`,
`C ≥ 0`. Let `u > 0` be differentiable with gradient `ug` (`∇u = ug`) whose coordinates are
continuous, with `∫ q u = 1` and with `q u`, `q u log u` and `q |∇u|² / u` Lebesgue integrable.
Then `∫ q u log u ≤ (C/2) ∫ q |∇u|² / u`, i.e. `KL(u ν‖ν) ≤ (C/2) I(u ν‖ν)`. No boundedness of
`u` or `∇u` and no lower bound on `u` are assumed. -/
theorem integral_mul_log_le_of_functionalLSIPi (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (q x))] {C : ℝ}
    (hC : 0 ≤ C) (hLSI : FunctionalLSIPi (volume.withDensity fun x => ENNReal.ofReal (q x)) C)
    {u : (Fin d → ℝ) → ℝ} {ug : (Fin d → ℝ) → Fin d → ℝ} (hu : ∀ x, 0 < u x)
    (hu' : ∀ x, HasFDerivAt u (dotCLM (ug x)) x) (hugc : ∀ i, Continuous fun x => ug x i)
    (hmass : Integrable (fun x => q x * u x)) (hone : ∫ x, q x * u x = 1)
    (hkl : Integrable (fun x => q x * (u x * Real.log (u x))))
    (hfi : Integrable (fun x => q x * (ug x ⬝ᵥ ug x) / u x)) :
    ∫ x, q x * (u x * Real.log (u x)) ≤ C / 2 * ∫ x, q x * (ug x ⬝ᵥ ug x) / u x := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (q x) with hν
  set g : (Fin d → ℝ) → ℝ := fun x => Real.sqrt (u x) with hg
  have hg0 : ∀ x, 0 < g x := fun x => Real.sqrt_pos.2 (hu x)
  have hg2 : ∀ x, g x ^ 2 = u x := fun x => Real.sq_sqrt (hu x).le
  have hgD : ∀ x, HasFDerivAt g ((1 / (2 * Real.sqrt (u x))) • dotCLM (ug x)) x :=
    fun x => (hu' x).sqrt (hu x).ne'
  have hpart : ∀ x i, fderiv ℝ g x (Pi.single i 1) = ug x i / (2 * g x) := by
    intro x i
    rw [(hgD x).fderiv, smul_apply, dotCLM_single, smul_eq_mul]
    simp only [hg]
    ring
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt
  have hgc : Continuous g := Real.continuous_sqrt.comp huc
  have hdc : ∀ i, Continuous fun x => fderiv ℝ g x (Pi.single i 1) := by
    intro i
    simp only [hpart]
    exact (hugc i).div (continuous_const.mul hgc) fun x => by have := hg0 x; positivity
  have hdsq : ∀ x, q x * gradSq g x = q x * (ug x ⬝ᵥ ug x) / u x / 4 := by
    intro x
    have := hu x
    have hg2' : (2 * g x) ^ 2 = 4 * u x := by rw [mul_pow, hg2]; norm_num
    simp only [gradSq, hpart, div_pow, hg2', dotProduct, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hi : Integrable (gradSq g) ν := by
    rw [integrable_withDensity_ofReal_iff hqm hq0]
    simp only [hdsq]
    exact hfi.div_const 4
  have hi2 : Integrable (fun x => g x ^ 2) ν := by
    rw [integrable_withDensity_ofReal_iff hqm hq0]
    simp only [hg2]
    exact hmass
  have hil : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) ν := by
    rw [integrable_withDensity_ofReal_iff hqm hq0]
    simp only [hg2]
    exact hkl
  have h := LogSobolevExtensionPi.ent_sq_le_of_functionalLSIPi hLSI hC hg0
    (fun x => (hgD x).differentiableAt) hdc hi hi2 hil
  have hent : ent ν (fun x => g x ^ 2) = ∫ x, q x * (u x * Real.log (u x)) := by
    unfold ent
    rw [integral_withDensity_ofReal hqm hq0, integral_withDensity_ofReal hqm hq0]
    simp only [hg2, hone, Real.log_one, mul_zero, sub_zero]
  have hfis : ∫ x, gradSq g x ∂ν = (∫ x, q x * (ug x ⬝ᵥ ug x) / u x) / 4 := by
    rw [integral_withDensity_ofReal hqm hq0, ← integral_div]
    exact integral_congr_ae (Eventually.of_forall hdsq)
  rw [hent, hfis] at h
  linarith

end Bridge

end FormalizeSampling.BackwardHeatFlowPi
