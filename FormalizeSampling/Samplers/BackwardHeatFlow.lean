module

public import FormalizeSampling.Foundations.LogSobolevExtension
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The backward heat flow of the RGO step: abstract de Bruijn identity, LSI bridge, Grönwall

Status: **Verified** (abstract analysis; every hypothesis is an explicit regularity or
integrability assumption, none of them is the identity or inequality being proved).

This file provides the analytic tools for the backward (restricted Gaussian oracle) step of the
proximal sampler, in dimension one. The concrete backward flow is built in
`Samplers/ProximalSharpLSI.lean`; here everything is stated for abstract families.

Setting. Let `W, U : ℝ → ℝ → ℝ` (time, space) with `U > 0`, solving the *backward* and the
*forward* heat equation respectively,
`∂_t W = -½ W''` and `∂_t U = ½ U''`
(space derivatives `Wx, Wxx, Ux, Uxx` given explicitly). In the intended instance
`W t = π * N(0, η - t)` is the density of the reference marginal of the backward flow and
`U t = N(0, t) * r` is the heat semigroup applied to the density ratio `r = dμ/dπ^Y`, so that
`p_t = W t · U t` is the backward marginal and `∫ W U log U = KL(p_t‖W t)`.

## Main results

* `hasDerivAt_bklIntegrand_time`, `hasDerivAt_bklFlux_space`: pointwise identities
  `∂_t [W U log U] = bklRate` and `∂_x bklFlux = 2 bklRate + W (U')² / U`.
* `integral_bklRate_eq`: `∫ bklRate = -½ ∫ W (U')² / U` (vanishing boundary flux).
* `hasDerivAt_integral_bklIntegrand` (**backward de Bruijn identity**):
  `d/dt ∫ W U log U = -½ ∫ W (U')² / U` under domination, integrability and boundary
  hypotheses.
* `integral_mul_log_le_of_functionalLSI` (**LSI bridge**): if `ν = q dx` (continuous `q > 0`)
  satisfies `FunctionalLSI ν C` (`C ≥ 0`) and `u > 0` is `C¹` with `∫ q u = 1`, then
  `∫ q u log u ≤ (C/2) ∫ q (u')² / u`, given integrability of both sides (no boundedness of
  `u`, via `LogSobolevExtension.ent_sq_le_of_functionalLSI` applied to `√u`).
* `le_div_of_hasDerivAt_interior` (**interior backward Grönwall**): if `K' = -½ I` and
  `2 α K ≤ (1 + α (η - t)) I` on the open interval `(0, η)`, `K ≤ A` and `B ≤ K` there, then
  `B ≤ A / (1 + α η)`. No regularity at the endpoints is used: in the application both
  endpoint bounds come from data processing.

## Not proved here

* Nothing about a concrete flow: the identification with the RGO step, and the regularity of
  the concrete backward flow, are in `Samplers/ProximalSharpLSI.lean` and
  `Samplers/BackwardHeatFlowRegularityWarm.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.LogSobolev

namespace FormalizeSampling.BackwardHeatFlow

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_withDensity_ofReal_iff)

/-! ### Abstract backward de Bruijn identity -/

variable {W U Wx Ux Wxx Uxx : ℝ → ℝ → ℝ}

/-- The backward relative-entropy integrand `W · (U log U)`; for `p = W U`, this is
`p log(p / W)`. -/
noncomputable def bklIntegrand (W U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  W t x * (U t x * Real.log (U t x))

/-- The time derivative of `bklIntegrand` along `∂_t W = -½ Wxx`, `∂_t U = ½ Uxx`
(`hasDerivAt_bklIntegrand_time`): `(W Uxx (log U + 1) - Wxx U log U) / 2`. -/
noncomputable def bklRate (W U Wxx Uxx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (W t x * Uxx t x * (Real.log (U t x) + 1) - Wxx t x * (U t x * Real.log (U t x))) / 2

/-- The backward relative Fisher integrand `W (U')² / U`; for `p = W U` this is
`p (∂_x log(p / W))²`. -/
noncomputable def bFisherIntegrand (W U Ux : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  W t x * Ux t x ^ 2 / U t x

/-- The backward boundary flux `W U' (log U + 1) - W' U log U`, whose space derivative is
`2 · bklRate + bFisherIntegrand` (`hasDerivAt_bklFlux_space`). -/
noncomputable def bklFlux (W U Wx Ux : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  W t x * Ux t x * (Real.log (U t x) + 1) - Wx t x * (U t x * Real.log (U t x))

/-- Pointwise time derivative of the backward KL integrand. If `U t x > 0`,
`∂_t W(·, x) = -½ Wxx` and `∂_t U(·, x) = ½ Uxx` at `t`, then `∂_t [W U log U] = bklRate`. -/
theorem hasDerivAt_bklIntegrand_time {t x : ℝ} (hU : 0 < U t x)
    (hWt : HasDerivAt (fun r => W r x) (-(Wxx t x / 2)) t)
    (hUt : HasDerivAt (fun r => U r x) (Uxx t x / 2) t) :
    HasDerivAt (fun r => bklIntegrand W U r x) (bklRate W U Wxx Uxx t x) t := by
  have h := hWt.mul (hUt.mul (hUt.log hU.ne'))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold bklRate
  field_simp
  ring

/-- Pointwise space derivative of the backward flux. If `U t x > 0` and
`∂_x W = Wx`, `∂_x U = Ux`, `∂_x Wx = Wxx`, `∂_x Ux = Uxx` at `x`, then
`∂_x bklFlux = 2 · bklRate + W (U')² / U`. -/
theorem hasDerivAt_bklFlux_space {t x : ℝ} (hU : 0 < U t x)
    (hWx : HasDerivAt (W t) (Wx t x) x) (hUx : HasDerivAt (U t) (Ux t x) x)
    (hWxx : HasDerivAt (Wx t) (Wxx t x) x) (hUxx : HasDerivAt (Ux t) (Uxx t x) x) :
    HasDerivAt (bklFlux W U Wx Ux t)
      (2 * bklRate W U Wxx Uxx t x + bFisherIntegrand W U Ux t x) x := by
  have hlog := hUx.log hU.ne'
  have e := ((hWx.mul hUxx).mul (hlog.add_const 1)).sub (hWxx.mul (hUx.mul hlog))
  convert e using 1
  · rfl
  · unfold bklRate bFisherIntegrand
    simp only [Pi.mul_apply]
    field_simp
    ring

/-- **Integration-by-parts step of the backward de Bruijn identity.** At a fixed time `t`, if
`U t > 0`, `W t`, `U t` are twice differentiable in `x` (derivatives `Wx, Wxx, Ux, Uxx`), the
rate `bklRate` and the Fisher integrand `W (U')² / U` are Lebesgue integrable and the flux
`bklFlux` tends to `0` at `±∞`, then `∫ bklRate = -½ ∫ W (U')² / U`. -/
theorem integral_bklRate_eq {t : ℝ} (hU : ∀ x, 0 < U t x)
    (hWx : ∀ x, HasDerivAt (W t) (Wx t x) x) (hUx : ∀ x, HasDerivAt (U t) (Ux t x) x)
    (hWxx : ∀ x, HasDerivAt (Wx t) (Wxx t x) x) (hUxx : ∀ x, HasDerivAt (Ux t) (Uxx t x) x)
    (hrate : Integrable (bklRate W U Wxx Uxx t))
    (hfisher : Integrable (bFisherIntegrand W U Ux t))
    (hbot : Tendsto (bklFlux W U Wx Ux t) atBot (𝓝 0))
    (htop : Tendsto (bklFlux W U Wx Ux t) atTop (𝓝 0)) :
    ∫ x, bklRate W U Wxx Uxx t x = -(1 / 2) * ∫ x, bFisherIntegrand W U Ux t x := by
  have hd : ∀ x, HasDerivAt (bklFlux W U Wx Ux t)
      (2 * bklRate W U Wxx Uxx t x + bFisherIntegrand W U Ux t x) x := fun x =>
    hasDerivAt_bklFlux_space (hU x) (hWx x) (hUx x) (hWxx x) (hUxx x)
  have h0 := integral_of_hasDerivAt_of_tendsto hd ((hrate.const_mul 2).add hfisher) hbot htop
  rw [integral_add (hrate.const_mul 2) hfisher, integral_const_mul, sub_self] at h0
  linarith

/-- **Backward de Bruijn identity (abstract form).** Let `s ∈ 𝓝 t₀`. Assume, for all `t ∈ s`
and all `x`: `U t x > 0`; `∂_t W = -½ Wxx`, `∂_t U = ½ Uxx`; `∂_x W = Wx`, `∂_x U = Ux`; and at
`t₀` also `∂_x Wx = Wxx`, `∂_x Ux = Uxx`. Assume `W t₀ U t₀ log U t₀` is integrable, `bklRate`
is dominated on `s` by an integrable `bound`, the Fisher integrand at `t₀` is integrable and
the flux at `t₀` vanishes at `±∞`. Then
`d/dt ∫ W_t U_t log U_t dx = -½ ∫ W_{t₀} (U_{t₀}')² / U_{t₀} dx` at `t = t₀`. -/
theorem hasDerivAt_integral_bklIntegrand {s : Set ℝ} {t₀ : ℝ} (hs : s ∈ 𝓝 t₀)
    (hU : ∀ t ∈ s, ∀ x, 0 < U t x)
    (hWt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => W r x) (-(Wxx t x / 2)) t)
    (hUt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => U r x) (Uxx t x / 2) t)
    (hWx : ∀ t ∈ s, ∀ x, HasDerivAt (W t) (Wx t x) x)
    (hUx : ∀ t ∈ s, ∀ x, HasDerivAt (U t) (Ux t x) x)
    (hWxx : ∀ x, HasDerivAt (Wx t₀) (Wxx t₀ x) x) (hUxx : ∀ x, HasDerivAt (Ux t₀) (Uxx t₀ x) x)
    (hint : Integrable (bklIntegrand W U t₀)) {bound : ℝ → ℝ} (hbound_int : Integrable bound)
    (hbound : ∀ t ∈ s, ∀ x, |bklRate W U Wxx Uxx t x| ≤ bound x)
    (hfisher : Integrable (bFisherIntegrand W U Ux t₀))
    (hbot : Tendsto (bklFlux W U Wx Ux t₀) atBot (𝓝 0))
    (htop : Tendsto (bklFlux W U Wx Ux t₀) atTop (𝓝 0)) :
    HasDerivAt (fun t => ∫ x, bklIntegrand W U t x)
      (-(1 / 2) * ∫ x, bFisherIntegrand W U Ux t₀ x) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  have hWc : ∀ t ∈ s, Continuous (W t) := fun t ht =>
    continuous_iff_continuousAt.2 fun x => (hWx t ht x).continuousAt
  have hUc : ∀ t ∈ s, Continuous (U t) := fun t ht =>
    continuous_iff_continuousAt.2 fun x => (hUx t ht x).continuousAt
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (bklIntegrand W U t) volume := by
    filter_upwards [hs] with t ht
    exact ((hWc t ht).mul ((hUc t ht).mul ((hUc t ht).log fun x => (hU t ht x).ne'))
      ).aestronglyMeasurable
  have hWxxm : Wxx t₀ = deriv (Wx t₀) := funext fun x => (hWxx x).deriv.symm
  have hUxxm : Uxx t₀ = deriv (Ux t₀) := funext fun x => (hUxx x).deriv.symm
  have hrate_meas : AEStronglyMeasurable (bklRate W U Wxx Uxx t₀) volume := by
    have h1 : Measurable (Wxx t₀) := hWxxm ▸ measurable_deriv _
    have h2 : Measurable (Uxx t₀) := hUxxm ▸ measurable_deriv _
    have hW := (hWc t₀ ht₀).measurable
    have hUm := (hUc t₀ ht₀).measurable
    unfold bklRate
    exact (((hW.mul h2).mul (hUm.log.add_const 1)).sub (h1.mul (hUm.mul hUm.log))).div_const 2
      |>.aestronglyMeasurable
  obtain ⟨hrate_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint
    hrate_meas (Eventually.of_forall fun x t ht => by simpa using hbound t ht x) hbound_int
    (Eventually.of_forall fun x t ht =>
      hasDerivAt_bklIntegrand_time (hU t ht x) (hWt t ht x) (hUt t ht x))
  rwa [integral_bklRate_eq (hU t₀ ht₀) (hWx t₀ ht₀) (hUx t₀ ht₀) hWxx hUxx hrate_int
    hfisher hbot htop] at hderiv

/-! ### The LSI bridge for a reference law with a density -/

section Bridge

variable {q : ℝ → ℝ}

/-- **LSI bridge.** Let `q ≥ 0` be measurable with `ν = volume.withDensity (ofReal ∘ q)` a
probability measure satisfying `FunctionalLSI ν C`, `C ≥ 0`. Let `u > 0` be differentiable
with continuous derivative `u'`, with `∫ q u = 1` (so `u dν` is a probability law) and with
`q u`, `q u log u` and `q (u')² / u` Lebesgue integrable. Then
`∫ q u log u ≤ (C/2) ∫ q (u')² / u`, i.e. `KL(u ν‖ν) ≤ (C/2) I(u ν‖ν)`. No boundedness of `u`
or `u'` and no lower bound on `u` are assumed. -/
theorem integral_mul_log_le_of_functionalLSI (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (q x))] {C : ℝ}
    (hC : 0 ≤ C) (hLSI : FunctionalLSI (volume.withDensity fun x => ENNReal.ofReal (q x)) C)
    {u u' : ℝ → ℝ} (hu : ∀ x, 0 < u x) (hu' : ∀ x, HasDerivAt u (u' x) x)
    (hu'c : Continuous u') (hmass : Integrable (fun x => q x * u x))
    (hone : ∫ x, q x * u x = 1) (hkl : Integrable (fun x => q x * (u x * Real.log (u x))))
    (hfi : Integrable (fun x => q x * u' x ^ 2 / u x)) :
    ∫ x, q x * (u x * Real.log (u x)) ≤ C / 2 * ∫ x, q x * u' x ^ 2 / u x := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (q x) with hν
  set g : ℝ → ℝ := fun x => Real.sqrt (u x) with hg
  have hg0 : ∀ x, 0 < g x := fun x => Real.sqrt_pos.2 (hu x)
  have hg2 : ∀ x, g x ^ 2 = u x := fun x => Real.sq_sqrt (hu x).le
  have hgD : ∀ x, HasDerivAt g (u' x / (2 * g x)) x := fun x => (hu' x).sqrt (hu x).ne'
  have hgd : deriv g = fun x => u' x / (2 * g x) := funext fun x => (hgD x).deriv
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt
  have hgc : Continuous g := Real.continuous_sqrt.comp huc
  have hdc : Continuous (deriv g) := by
    rw [hgd]
    exact hu'c.div (continuous_const.mul hgc) fun x => by have := hg0 x; positivity
  have hdsq : ∀ x, q x * deriv g x ^ 2 = q x * u' x ^ 2 / u x / 4 := by
    intro x
    rw [hgd, div_pow, mul_pow, hg2]
    have := hu x
    field_simp
    ring
  have hi : Integrable (fun x => deriv g x ^ 2) ν := by
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
  have h := LogSobolevExtension.ent_sq_le_of_functionalLSI hLSI hC hg0
    (fun x => (hgD x).differentiableAt) hdc hi hi2 hil
  have hent : ent ν (fun x => g x ^ 2) = ∫ x, q x * (u x * Real.log (u x)) := by
    unfold ent
    rw [integral_withDensity_ofReal hqm hq0, integral_withDensity_ofReal hqm hq0]
    simp only [hg2, hone, Real.log_one, mul_zero, sub_zero]
  have hfis : ∫ x, deriv g x ^ 2 ∂ν = (∫ x, q x * u' x ^ 2 / u x) / 4 := by
    rw [integral_withDensity_ofReal hqm hq0, ← integral_div]
    exact integral_congr_ae (Eventually.of_forall hdsq)
  rw [hent, hfis] at h
  linarith

end Bridge

/-! ### Interior backward Grönwall comparison -/

/-- **Interior backward Grönwall comparison.** Let `α ≥ 0`, `η > 0`, and `K, I : ℝ → ℝ` with
`K' t = -½ I t` and `2 α K t ≤ (1 + α (η - t)) I t` for every `t` in the **open** interval
`(0, η)`. If `K t ≤ A` and `B ≤ K t` for every `t ∈ (0, η)`, then `B ≤ A / (1 + α η)`.

Proof: `t ↦ K t / (1 + α (η - t))` is antitone on `(0, η)`, so for `0 < ε < η/2`,
`B ≤ K (η - ε) ≤ (1 + α ε) K ε / (1 + α (η - ε)) ≤ (1 + α ε) A / (1 + α (η - ε))`; let
`ε → 0⁺`. No continuity or derivative of `K` at `0` or `η` is needed. -/
theorem le_div_of_hasDerivAt_interior {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) {K I : ℝ → ℝ}
    {A B : ℝ} (hd : ∀ t ∈ Ioo 0 η, HasDerivAt K (-(1 / 2) * I t) t)
    (hL : ∀ t ∈ Ioo 0 η, 2 * α * K t ≤ (1 + α * (η - t)) * I t)
    (hA : ∀ t ∈ Ioo 0 η, K t ≤ A) (hB : ∀ t ∈ Ioo 0 η, B ≤ K t) :
    B ≤ A / (1 + α * η) := by
  have hpos : ∀ t, t ≤ η → 0 < 1 + α * (η - t) := fun t ht => by
    nlinarith [mul_nonneg hα (sub_nonneg.2 ht)]
  set g : ℝ → ℝ := fun t => K t / (1 + α * (η - t)) with hg
  have hgd : ∀ t ∈ Ioo 0 η, HasDerivAt g
      ((-(1 / 2) * I t * (1 + α * (η - t)) - K t * (-α)) / (1 + α * (η - t)) ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + α * (η - t)) (-α) t := by
      simpa using (((hasDerivAt_id t).const_sub η).const_mul α).const_add 1
    exact (hd t ht).div h1 (hpos t ht.2.le).ne'
  have hanti : ∀ τ σ, 0 < τ → τ ≤ σ → σ < η → g σ ≤ g τ := by
    intro τ σ hτ hτσ hσ
    have hsub : Icc τ σ ⊆ Ioo 0 η := fun t ht => ⟨hτ.trans_le ht.1, ht.2.trans_lt hσ⟩
    have hmono : AntitoneOn g (Icc τ σ) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc τ σ)
        (fun t ht => (hgd t (hsub ht)).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Icc]
        exact fun t ht => (hgd t (hsub (Ioo_subset_Icc_self ht))).differentiableAt
          |>.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        have ht' := hsub (Ioo_subset_Icc_self ht)
        rw [(hgd t ht').deriv]
        apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
        have := hL t ht'
        nlinarith
    exact hmono (left_mem_Icc.2 hτσ) (right_mem_Icc.2 hτσ) hτσ
  have hstep : ∀ ε ∈ Ioo 0 (η / 2),
      B ≤ (1 + α * ε) * A / (1 + α * (η - ε)) := by
    intro ε hε
    have h1 : η - ε ∈ Ioo 0 η := ⟨by linarith [hε.2], by linarith [hε.1]⟩
    have h2 : ε ∈ Ioo 0 η := ⟨hε.1, by linarith [hε.2]⟩
    have hp1 := hpos (η - ε) h1.2.le
    have hp2 := hpos ε h2.2.le
    have hg1 := hanti ε (η - ε) hε.1 (by linarith [hε.2]) h1.2
    simp only [hg] at hg1
    have e1 : η - (η - ε) = ε := by ring
    rw [e1] at hg1 hp1
    have hK := hB _ h1
    have hKA : K ε / (1 + α * (η - ε)) ≤ A / (1 + α * (η - ε)) :=
      div_le_div_of_nonneg_right (hA ε h2) hp2.le
    have h3 : K (η - ε) ≤ (1 + α * ε) * (A / (1 + α * (η - ε))) := by
      rw [div_le_iff₀ hp1] at hg1
      calc K (η - ε) ≤ K ε / (1 + α * (η - ε)) * (1 + α * ε) := hg1
        _ ≤ A / (1 + α * (η - ε)) * (1 + α * ε) :=
          mul_le_mul_of_nonneg_right hKA (by nlinarith [hε.1])
        _ = _ := by ring
    rw [mul_div_assoc]
    linarith
  have hcont : ContinuousAt (fun ε : ℝ => (1 + α * ε) * A / (1 + α * (η - ε))) 0 := by
    have : (1 + α * (η - 0)) ≠ 0 := (hpos 0 hη.le).ne'
    fun_prop (disch := exact this)
  have hlim : Tendsto (fun ε : ℝ => (1 + α * ε) * A / (1 + α * (η - ε))) (𝓝[>] 0)
      (𝓝 (A / (1 + α * η))) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  exact ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT (by linarith)) hstep)

end FormalizeSampling.BackwardHeatFlow
