module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import FormalizeSampling.Foundations.VectorCalculus
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# First variation of KL under deterministic transport (FL-1)

Registry ID: **FL-1** (KL first variation under deterministic transport, in transport form and
in Stein / directional-derivative form).

## Setting and conventions

The state space is `Fin d → ℝ` with Lebesgue measure `volume`. Densities `p`, `pStar` are
real-valued functions, assumed **strictly positive everywhere** (so `Real.log (p x / pStar x)`
and the scores `score p = ∇ log p` are never evaluated at junk values). Vector fields are
`v : (Fin d → ℝ) → Fin d → ℝ`; the flux is `p • v`, whose `i`-th coordinate is `p * vᵢ`
(`divergence_smul_apply`). Partial derivatives, divergence and scores are the shared ones of
`FormalizeSampling.Foundations.VectorCalculus`.

The KL functional used here is the density integral
`KL(p ‖ pStar) = ∫ x, p x * Real.log (p x / pStar x)`.
For probability densities it agrees with Mathlib's `InformationTheory.klDiv` of the measures
`volume.withDensity (ENNReal.ofReal ∘ p)` and `volume.withDensity (ENNReal.ofReal ∘ pStar)`;
this bridge is `klDiv_withDensity_eq_integral` (finite-KL case, in
`Foundations/MeasureHelpers.lean`). The coordinate integration-by-parts lemmas
`integral_mul_partialDeriv_eq_neg` and `integral_partialDeriv_eq_zero` are in
`Foundations/VectorCalculus.lean`.

## Contents

**(I) Fixed time** (integration by parts on `Fin d → ℝ`, each IBP backed by explicit
integrability hypotheses; Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`):
* (a) transport form `integral_neg_divergence_mul_log_div`:
  `∫ -div(p v) · log(p/p⋆) = ∫ (v · (∇log p - ∇log p⋆)) p`;
* (b) Stein identity `integral_dotProduct_score_mul_eq_neg`:
  `∫ (v · ∇log p) p = -∫ (div v) p`, and the Stein form
  `integral_transport_eq_stein_form`, `integral_neg_divergence_mul_log_div_eq_stein_form`:
  `∫ -div(p v) · log(p/p⋆) = -∫ (div v + v · ∇log p⋆) p`;
* (c) mass conservation `integral_divergence_flux_eq_zero`: `∫ div(p v) = 0`;
* discharged versions `*_of_hasCompactSupport`: for `v` compactly supported and `C¹` and
  `p`, `pStar` positive and `C¹`, every integrability hypothesis holds automatically.

**(II) Time derivative** `hasDerivAt_klIntegral` (and `hasDerivAt_klIntegral_stein_form`):
for `p : ℝ → (Fin d → ℝ) → ℝ` satisfying the strong (pointwise) continuity equation
`∂ₜ p_t(x) = -div(p_t v_t)(x)` for all `t, x` — the *model of the dynamics*, not the
conclusion — positivity, and explicit domination hypotheses in the shape of
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the map `t ↦ KL(p_t ‖ p⋆)` is
differentiable at `t₀` with derivative `∫ (v_{t₀} · (∇log p_{t₀} - ∇log p⋆)) p_{t₀}`
`= -∫ (div v_{t₀} + v_{t₀} · ∇log p⋆) p_{t₀}`.
The pointwise computation is `∂ₜ[p log(p/p⋆)] = ∂ₜp · (log(p/p⋆) + 1)`; the `+1` term
integrates to `0` by (c). `hasDerivAt_klIntegral_of_hasCompactSupport` discharges all
fixed-time (`t = t₀`) integrability hypotheses when `v_{t₀}` is compactly supported and `C¹`.

Status: **Verified** under explicit regularity hypotheses.

## What is NOT proved here

* The time-dependent hypotheses of (II) — the domination bound `h_bound` with integrable
  `bound`, the measurability `hp_meas` of `p t` near `t₀`, and finiteness of `KL(p_{t₀}‖p⋆)`
  (`hKL`) — are **not discharged in this file**; they remain explicit assumptions here. For
  the OU probability flow they are discharged (bundled as
  `KLDissipation.TransportKLRegularity`) in `Flow/ProbabilityFlowOUMoment.lean` (finite fourth
  moment; the bounded-support case is `ProbabilityFlowOU.transportKLRegularity_ou`).
* No existence or uniqueness theory for the continuity equation: the family `p` is given and
  is *assumed* to satisfy the strong continuity equation pointwise. Weak (distributional)
  continuity equations are not treated, and no integrated (interval) dissipation identity is
  derived.
* Densities vanishing somewhere (non-strict positivity) and non-compactly-supported velocity
  fields are only covered through the explicit integrability hypotheses; no boundary-decay
  criterion is proved for them.
* The preconditioned PFG dissipation identity (FL-2) and any convergence statement are not
  addressed here.
-/

public section

open MeasureTheory Matrix

namespace FormalizeSampling.KLTransport

variable {d : ℕ}

/-! ### Integration-by-parts helpers -/

/-- The divergence of the flux `p • v` is `∑ᵢ ∂ᵢ(p vᵢ)` (definitional unfolding; no
regularity is needed). -/
theorem divergence_smul_apply (p : (Fin d → ℝ) → ℝ) (v : (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin d → ℝ) :
    divergence (fun y => p y • v y) x = ∑ i, partialDeriv i (fun y => p y * v y i) x :=
  rfl

/-- For everywhere-positive `p` and `pStar`, `log (p / pStar) = log p - log pStar` as
functions. -/
theorem log_div_eq_sub {p pStar : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < p x)
    (hpStar_pos : ∀ x, 0 < pStar x) :
    (fun y => Real.log (p y / pStar y)) = fun y => Real.log (p y) - Real.log (pStar y) := by
  funext y
  exact Real.log_div (hpos y).ne' (hpStar_pos y).ne'

/-- For everywhere-positive, differentiable `p` and `pStar`, the log-ratio `log (p / pStar)` is
differentiable. -/
theorem differentiable_log_div {p pStar : (Fin d → ℝ) → ℝ}
    (hp : Differentiable ℝ p) (hpStar : Differentiable ℝ pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x) :
    Differentiable ℝ (fun y => Real.log (p y / pStar y)) := by
  rw [log_div_eq_sub hpos hpStar_pos]
  exact (hp.log fun x => (hpos x).ne').sub (hpStar.log fun x => (hpStar_pos x).ne')

/-- For everywhere-positive, differentiable `p` and `pStar`,
`∂ᵢ log (p / pStar)(x) = (∇log p)ᵢ(x) - (∇log pStar)ᵢ(x)`. -/
theorem partialDeriv_log_div {p pStar : (Fin d → ℝ) → ℝ}
    (hp : Differentiable ℝ p) (hpStar : Differentiable ℝ pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x) (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (fun y => Real.log (p y / pStar y)) x = score p x i - score pStar x i := by
  rw [log_div_eq_sub hpos hpStar_pos]
  unfold partialDeriv
  rw [fderiv_fun_sub ((hp x).log (hpos x).ne') ((hpStar x).log (hpStar_pos x).ne')]
  rfl

/-! ### (c) Mass conservation -/

/-- **Divergence theorem with vanishing boundary terms.** If every coordinate `wᵢ` of a vector
field `w` on `Fin d → ℝ` is differentiable, and `wᵢ` and `∂ᵢwᵢ` are Lebesgue integrable for
every `i`, then `∫ div w = 0`. -/
theorem integral_divergence_eq_zero {w : (Fin d → ℝ) → Fin d → ℝ}
    (hw : ∀ i, Differentiable ℝ (fun x => w x i))
    (hw_int : ∀ i, Integrable (fun x => w x i))
    (hdw_int : ∀ i, Integrable (fun x => partialDeriv i (fun y => w y i) x)) :
    ∫ x, divergence w x = 0 := by
  unfold divergence
  rw [integral_finsetSum _ fun i _ => hdw_int i]
  exact Finset.sum_eq_zero fun i _ =>
    integral_partialDeriv_eq_zero i (hw i) (hw_int i) (hdw_int i)

/-- **(c) Mass conservation under transport.** For `p` differentiable and `v` with
differentiable coordinates, if the flux coordinates `p vᵢ` and their partials `∂ᵢ(p vᵢ)` are
Lebesgue integrable, then `∫ div(p v) = 0`, i.e. the continuity equation
`∂ₜp = -div(p v)` conserves total mass. -/
theorem integral_divergence_flux_eq_zero {p : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : Differentiable ℝ p) (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hflux : ∀ i, Integrable (fun x => p x * v x i))
    (hdflux : ∀ i, Integrable (fun x => partialDeriv i (fun y => p y * v y i) x)) :
    ∫ x, divergence (fun y => p y • v y) x = 0 :=
  integral_divergence_eq_zero (w := fun y => p y • v y) (fun i => hp.mul (hv i)) hflux hdflux

/-! ### (a) Transport form -/

/-- **(a) KL first variation, transport form (FL-1, fixed time).** Let `p`, `pStar` be
everywhere positive and differentiable on `Fin d → ℝ` and let every coordinate of `v` be
differentiable. Assume, for every `i`, Lebesgue integrability of
`∂ᵢ(p vᵢ) · log(p/pStar)`, of `p vᵢ · log(p/pStar)` and of
`vᵢ ((∇log p)ᵢ - (∇log pStar)ᵢ) p` (the three integrands of the integration by parts). Then
`∫ -div(p v) · log(p/pStar) = ∫ (v · (∇log p - ∇log pStar)) p`. -/
theorem integral_neg_divergence_mul_log_div {p pStar : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : Differentiable ℝ p) (hpStar : Differentiable ℝ pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hdflux_log : ∀ i, Integrable (fun x =>
      partialDeriv i (fun y => p y * v y i) x * Real.log (p x / pStar x)))
    (hflux_log : ∀ i, Integrable (fun x => p x * v x i * Real.log (p x / pStar x)))
    (hflux_score : ∀ i, Integrable (fun x => v x i * (score p x i - score pStar x i) * p x)) :
    ∫ x, -(divergence (fun y => p y • v y) x) * Real.log (p x / pStar x) =
      ∫ x, (v x ⬝ᵥ (score p x - score pStar x)) * p x := by
  have hL := differentiable_log_div hp hpStar hpos hpStar_pos
  have hpt : ∀ x, -(divergence (fun y => p y • v y) x) * Real.log (p x / pStar x) =
      ∑ i, -(partialDeriv i (fun y => p y * v y i) x * Real.log (p x / pStar x)) := by
    intro x
    rw [divergence_smul_apply, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
  have hrhs : ∀ x, (v x ⬝ᵥ (score p x - score pStar x)) * p x =
      ∑ i, v x i * (score p x i - score pStar x i) * p x := by
    intro x
    simp only [dotProduct, Pi.sub_apply, Finset.sum_mul]
  simp_rw [hpt, hrhs]
  rw [integral_finsetSum _ fun i _ => (hdflux_log i).fun_neg,
    integral_finsetSum _ fun i _ => hflux_score i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hibp := integral_mul_partialDeriv_eq_neg (f := fun y => p y * v y i) i
    (hp.mul (hv i)) hL (hdflux_log i)
    (by
      refine (hflux_score i).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [partialDeriv_log_div hp hpStar hpos hpStar_pos]
      ring)
    (hflux_log i)
  rw [integral_neg, ← hibp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [partialDeriv_log_div hp hpStar hpos hpStar_pos]
  ring

/-! ### (b) Stein identity and Stein form -/

/-- **(b) Stein identity (FL-1).** Let `p` be everywhere positive and differentiable and let
every coordinate of `v` be differentiable. Assume, for every `i`, Lebesgue integrability of
`∂ᵢvᵢ · p`, of `vᵢ (∇log p)ᵢ p` (`= vᵢ ∂ᵢp`) and of `p vᵢ`. Then
`∫ (v · ∇log p) p = -∫ (div v) p`. -/
theorem integral_dotProduct_score_mul_eq_neg {p : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : Differentiable ℝ p) (hpos : ∀ x, 0 < p x)
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hdv : ∀ i, Integrable (fun x => partialDeriv i (fun y => v y i) x * p x))
    (hvs : ∀ i, Integrable (fun x => v x i * score p x i * p x))
    (hflux : ∀ i, Integrable (fun x => p x * v x i)) :
    ∫ x, (v x ⬝ᵥ score p x) * p x = -∫ x, divergence v x * p x := by
  have hl : ∀ x, (v x ⬝ᵥ score p x) * p x = ∑ i, v x i * score p x i * p x := by
    intro x
    simp only [dotProduct, Finset.sum_mul]
  have hr : ∀ x, divergence v x * p x = ∑ i, partialDeriv i (fun y => v y i) x * p x := by
    intro x
    simp only [divergence, Finset.sum_mul]
  simp_rw [hl, hr]
  rw [integral_finsetSum _ fun i _ => hvs i, integral_finsetSum _ fun i _ => hdv i,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpt : ∀ x, v x i * score p x i * p x = v x i * partialDeriv i p x := by
    intro x
    rw [score_apply_of_pos (hp x) (hpos x)]
    field_simp [(hpos x).ne']
  simp_rw [hpt]
  exact integral_mul_partialDeriv_eq_neg (f := fun y => v y i) i (hv i) hp (hdv i)
    ((hvs i).congr (Filter.Eventually.of_forall hpt))
    ((hflux i).congr (Filter.Eventually.of_forall fun x => mul_comm _ _))

/-- **Transport form equals Stein form (FL-1).** Under the hypotheses of the Stein
identity `integral_dotProduct_score_mul_eq_neg` (positive differentiable `p`, differentiable
coordinates of `v`, integrability of `∂ᵢvᵢ · p`, `vᵢ (∇log p)ᵢ p`, `p vᵢ`) and integrability of
`vᵢ ((∇log p)ᵢ - (∇log pStar)ᵢ) p` for every `i`,
`∫ (v · (∇log p - ∇log pStar)) p = -∫ (div v + v · ∇log pStar) p`.
No regularity of `pStar` is needed beyond these integrability hypotheses. -/
theorem integral_transport_eq_stein_form {p pStar : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : Differentiable ℝ p) (hpos : ∀ x, 0 < p x)
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hdv : ∀ i, Integrable (fun x => partialDeriv i (fun y => v y i) x * p x))
    (hvs : ∀ i, Integrable (fun x => v x i * score p x i * p x))
    (hflux : ∀ i, Integrable (fun x => p x * v x i))
    (hflux_score : ∀ i, Integrable (fun x => v x i * (score p x i - score pStar x i) * p x)) :
    ∫ x, (v x ⬝ᵥ (score p x - score pStar x)) * p x =
      -∫ x, (divergence v x + v x ⬝ᵥ score pStar x) * p x := by
  have h1 : Integrable (fun x => (v x ⬝ᵥ score p x) * p x) := by
    have := integrable_finsetSum Finset.univ fun i _ => hvs i
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [dotProduct, Finset.sum_mul]
  have h2 : Integrable (fun x => (v x ⬝ᵥ score pStar x) * p x) := by
    have := integrable_finsetSum Finset.univ fun i _ => (hvs i).sub (hflux_score i)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [dotProduct, Finset.sum_mul, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : Integrable (fun x => divergence v x * p x) := by
    have := integrable_finsetSum Finset.univ fun i _ => hdv i
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [divergence, Finset.sum_mul]
  have hstein := integral_dotProduct_score_mul_eq_neg hp hpos hv hdv hvs hflux
  calc ∫ x, (v x ⬝ᵥ (score p x - score pStar x)) * p x
      = ∫ x, ((v x ⬝ᵥ score p x) * p x - (v x ⬝ᵥ score pStar x) * p x) := by
        congr 1
        funext x
        rw [dotProduct_sub, sub_mul]
    _ = (-∫ x, divergence v x * p x) - ∫ x, (v x ⬝ᵥ score pStar x) * p x := by
        rw [integral_sub h1 h2, hstein]
    _ = -∫ x, (divergence v x + v x ⬝ᵥ score pStar x) * p x := by
        simp_rw [add_mul]
        rw [integral_add h3 h2]
        ring

/-- **(a)+(b) KL first variation, Stein form (FL-1, fixed time).** Let `p`, `pStar`
be everywhere positive and differentiable and let every coordinate of `v` be differentiable.
Under the integrability hypotheses of the transport form
`integral_neg_divergence_mul_log_div` and of the Stein identity
`integral_dotProduct_score_mul_eq_neg`,
`∫ -div(p v) · log(p/pStar) = -∫ (div v + v · ∇log pStar) p`. -/
theorem integral_neg_divergence_mul_log_div_eq_stein_form {p pStar : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : Differentiable ℝ p) (hpStar : Differentiable ℝ pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hdflux_log : ∀ i, Integrable (fun x =>
      partialDeriv i (fun y => p y * v y i) x * Real.log (p x / pStar x)))
    (hflux_log : ∀ i, Integrable (fun x => p x * v x i * Real.log (p x / pStar x)))
    (hflux_score : ∀ i, Integrable (fun x => v x i * (score p x i - score pStar x i) * p x))
    (hdv : ∀ i, Integrable (fun x => partialDeriv i (fun y => v y i) x * p x))
    (hvs : ∀ i, Integrable (fun x => v x i * score p x i * p x))
    (hflux : ∀ i, Integrable (fun x => p x * v x i)) :
    ∫ x, -(divergence (fun y => p y • v y) x) * Real.log (p x / pStar x) =
      -∫ x, (divergence v x + v x ⬝ᵥ score pStar x) * p x := by
  rw [integral_neg_divergence_mul_log_div hp hpStar hpos hpStar_pos hv hdflux_log hflux_log
    hflux_score]
  exact integral_transport_eq_stein_form hp hpos hv hdv hvs hflux hflux_score

/-! ### Discharged versions: compactly supported `C¹` velocity fields -/

section CompactSupport

private lemma continuous_score_apply {p : (Fin d → ℝ) → ℝ} (hp : ContDiff ℝ 1 p)
    (hpos : ∀ x, 0 < p x) (i : Fin d) : Continuous (fun x => score p x i) :=
  continuous_partialDeriv (hp.log fun x => (hpos x).ne') i

private lemma continuous_log_div {p pStar : (Fin d → ℝ) → ℝ} (hp : Continuous p)
    (hpStar : Continuous pStar) (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x) :
    Continuous (fun x => Real.log (p x / pStar x)) :=
  (hp.div hpStar fun x => (hpStar_pos x).ne').log fun x =>
    (div_pos (hpos x) (hpStar_pos x)).ne'

private lemma contDiff_coord {v : (Fin d → ℝ) → Fin d → ℝ} (hv : ContDiff ℝ 1 v)
    (i : Fin d) : ContDiff ℝ 1 (fun x => v x i) :=
  contDiff_pi.1 hv i

private lemma hasCompactSupport_coord {v : (Fin d → ℝ) → Fin d → ℝ}
    (hv : HasCompactSupport v) (i : Fin d) : HasCompactSupport (fun x => v x i) :=
  hv.comp_left (g := fun w : Fin d → ℝ => w i) (Pi.zero_apply i)

private lemma hasCompactSupport_flux {p : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hv : HasCompactSupport v) (i : Fin d) : HasCompactSupport (fun x => p x * v x i) :=
  (hasCompactSupport_coord hv i).mul_left (f := p)

private lemma integrable_dflux_log {p pStar : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpStar : ContDiff ℝ 1 pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => partialDeriv i (fun y => p y * v y i) x * Real.log (p x / pStar x)) :=
  ((continuous_partialDeriv (hp.mul (contDiff_coord hv i)) i).mul
    (continuous_log_div hp.continuous hpStar.continuous hpos hpStar_pos)
    ).integrable_of_hasCompactSupport
    (hasCompactSupport_partialDeriv (hasCompactSupport_flux hv_supp i) i).mul_right

private lemma integrable_flux_log {p pStar : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpStar : ContDiff ℝ 1 pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => p x * v x i * Real.log (p x / pStar x)) :=
  ((hp.continuous.mul (contDiff_coord hv i).continuous).mul
    (continuous_log_div hp.continuous hpStar.continuous hpos hpStar_pos)
    ).integrable_of_hasCompactSupport
    (hasCompactSupport_flux hv_supp i).mul_right

private lemma integrable_coord_score_sub {p pStar : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpStar : ContDiff ℝ 1 pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => v x i * (score p x i - score pStar x i) * p x) :=
  (((contDiff_coord hv i).continuous.mul ((continuous_score_apply hp hpos i).sub
    (continuous_score_apply hpStar hpStar_pos i))).mul
      hp.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_coord hv_supp i).mul_right.mul_right

private lemma integrable_dcoord {p : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => partialDeriv i (fun y => v y i) x * p x) :=
  ((continuous_partialDeriv (contDiff_coord hv i) i).mul
    hp.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_partialDeriv (hasCompactSupport_coord hv_supp i) i).mul_right

private lemma integrable_coord_score {p : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => v x i * score p x i * p x) :=
  (((contDiff_coord hv i).continuous.mul (continuous_score_apply hp hpos i)).mul
    hp.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_coord hv_supp i).mul_right.mul_right

private lemma integrable_flux {p : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => p x * v x i) :=
  (hp.continuous.mul (contDiff_coord hv i).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_flux hv_supp i)

private lemma integrable_dflux {p : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) (i : Fin d) :
    Integrable (fun x => partialDeriv i (fun y => p y * v y i) x) :=
  (continuous_partialDeriv (hp.mul (contDiff_coord hv i)) i).integrable_of_hasCompactSupport
    (hasCompactSupport_partialDeriv (hasCompactSupport_flux hv_supp i) i)

/-- **(a) Transport form, discharged (FL-1).** Let `p`, `pStar` be everywhere positive and
`C¹` on `Fin d → ℝ`, and let `v` be `C¹` with compact support. Then, with no further
integrability hypotheses,
`∫ -div(p v) · log(p/pStar) = ∫ (v · (∇log p - ∇log pStar)) p`. -/
theorem integral_neg_divergence_mul_log_div_of_hasCompactSupport
    {p pStar : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpStar : ContDiff ℝ 1 pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) :
    ∫ x, -(divergence (fun y => p y • v y) x) * Real.log (p x / pStar x) =
      ∫ x, (v x ⬝ᵥ (score p x - score pStar x)) * p x :=
  integral_neg_divergence_mul_log_div (hp.differentiable one_ne_zero)
    (hpStar.differentiable one_ne_zero) hpos hpStar_pos
    (fun i => (contDiff_coord hv i).differentiable one_ne_zero)
    (integrable_dflux_log hp hpStar hpos hpStar_pos hv hv_supp)
    (integrable_flux_log hp hpStar hpos hpStar_pos hv hv_supp)
    (integrable_coord_score_sub hp hpStar hpos hpStar_pos hv hv_supp)

/-- **(b) Stein identity, discharged (FL-1).** Let `p` be everywhere positive and `C¹` and
let `v` be `C¹` with compact support. Then `∫ (v · ∇log p) p = -∫ (div v) p`. -/
theorem integral_dotProduct_score_mul_eq_neg_of_hasCompactSupport {p : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) :
    ∫ x, (v x ⬝ᵥ score p x) * p x = -∫ x, divergence v x * p x :=
  integral_dotProduct_score_mul_eq_neg (hp.differentiable one_ne_zero) hpos
    (fun i => (contDiff_coord hv i).differentiable one_ne_zero)
    (integrable_dcoord hp hv hv_supp) (integrable_coord_score hp hpos hv hv_supp)
    (integrable_flux hp hv hv_supp)

/-- **(a)+(b) KL first variation in Stein form, discharged (FL-1).** Let `p`,
`pStar` be everywhere positive and `C¹`, and let `v` be `C¹` with compact support. Then
`∫ -div(p v) · log(p/pStar) = -∫ (div v + v · ∇log pStar) p`. -/
theorem integral_neg_divergence_mul_log_div_eq_stein_form_of_hasCompactSupport
    {p pStar : (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hpStar : ContDiff ℝ 1 pStar)
    (hpos : ∀ x, 0 < p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) :
    ∫ x, -(divergence (fun y => p y • v y) x) * Real.log (p x / pStar x) =
      -∫ x, (divergence v x + v x ⬝ᵥ score pStar x) * p x :=
  integral_neg_divergence_mul_log_div_eq_stein_form (hp.differentiable one_ne_zero)
    (hpStar.differentiable one_ne_zero) hpos hpStar_pos
    (fun i => (contDiff_coord hv i).differentiable one_ne_zero)
    (integrable_dflux_log hp hpStar hpos hpStar_pos hv hv_supp)
    (integrable_flux_log hp hpStar hpos hpStar_pos hv hv_supp)
    (integrable_coord_score_sub hp hpStar hpos hpStar_pos hv hv_supp)
    (integrable_dcoord hp hv hv_supp) (integrable_coord_score hp hpos hv hv_supp)
    (integrable_flux hp hv hv_supp)

/-- **(c) Mass conservation, discharged (FL-1).** Let `p` be `C¹` (no positivity needed) and
let `v` be `C¹` with compact support. Then `∫ div(p v) = 0`. -/
theorem integral_divergence_flux_eq_zero_of_hasCompactSupport {p : (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hv : ContDiff ℝ 1 v) (hv_supp : HasCompactSupport v) :
    ∫ x, divergence (fun y => p y • v y) x = 0 :=
  integral_divergence_flux_eq_zero (hp.differentiable one_ne_zero)
    (fun i => (contDiff_coord hv i).differentiable one_ne_zero)
    (integrable_flux hp hv hv_supp) (integrable_dflux hp hv hv_supp)

end CompactSupport

/-! ### (II) Differentiability of the time-dependent KL functional -/

/-- **Pointwise chain rule for `p log(p/c)`.** If `f : ℝ → ℝ` has derivative `f'` at `t`,
`f t > 0` and `c > 0`, then `s ↦ f s · log(f s / c)` has derivative
`f' · (log(f t / c) + 1)` at `t`. -/
theorem hasDerivAt_mul_log_div {f : ℝ → ℝ} {f' c t : ℝ} (hf : HasDerivAt f f' t)
    (hpos : 0 < f t) (hc : 0 < c) :
    HasDerivAt (fun s => f s * Real.log (f s / c)) (f' * (Real.log (f t / c) + 1)) t := by
  have h1 := (hf.div_const c).log (div_pos hpos hc).ne'
  convert hf.mul h1 using 1
  field_simp [hpos.ne', hc.ne']

/-- **(II) Time derivative of KL along a transport flow, transport form (FL-1).**

Model of the dynamics: `p : ℝ → (Fin d → ℝ) → ℝ` is everywhere positive and satisfies the
strong continuity equation `∂ₜ p_t(x) = -div(p_t v_t)(x)` for all `t, x` (`hce`); `pStar` is
everywhere positive and differentiable.

Domination hypotheses (the shape of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`):
`ε > 0`; `p t` is a.e.-strongly measurable for `t` in the ball `B(t₀, ε)`;
`KL(p_{t₀} ‖ pStar) = ∫ p_{t₀} log(p_{t₀}/pStar)` is finite (`hKL`); and the pointwise time
derivative `-div(p_t v_t)(x) · (log(p_t(x)/pStar(x)) + 1)` is bounded in absolute value by an
integrable `bound x` for all `t ∈ B(t₀, ε)` and a.e. `x`. (These force `p t log(p t/pStar)` to
be integrable for `t` near `t₀`, so the KL integrals are genuine.)

Fixed-time hypotheses at `t₀`: `p_{t₀}` and the coordinates of `v_{t₀}` are differentiable, and
the integrability hypotheses of mass conservation (`p vᵢ`, `∂ᵢ(p vᵢ)`) and of the transport form
(`∂ᵢ(p vᵢ) log(p/pStar)`, `p vᵢ log(p/pStar)`, `vᵢ((∇log p)ᵢ - (∇log pStar)ᵢ) p`) hold for
`p = p_{t₀}`, `v = v_{t₀}`.

Conclusion: `t ↦ ∫ p_t log(p_t/pStar)` is differentiable at `t₀` with derivative
`∫ (v_{t₀} · (∇log p_{t₀} - ∇log pStar)) p_{t₀}`. -/
theorem hasDerivAt_klIntegral {p : ℝ → (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {t₀ ε : ℝ} {bound : (Fin d → ℝ) → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hε : 0 < ε)
    (hp_meas : ∀ t ∈ Metric.ball t₀ ε, AEStronglyMeasurable (p t))
    (hKL : Integrable (fun x => p t₀ x * Real.log (p t₀ x / pStar x)))
    (h_bound : ∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => p t y • v t y) x) * (Real.log (p t x / pStar x) + 1)‖ ≤ bound x)
    (hbound : Integrable bound)
    (hp₀ : Differentiable ℝ (p t₀)) (hv₀ : ∀ i, Differentiable ℝ (fun x => v t₀ x i))
    (hflux : ∀ i, Integrable (fun x => p t₀ x * v t₀ x i))
    (hdflux : ∀ i, Integrable (fun x => partialDeriv i (fun y => p t₀ y * v t₀ y i) x))
    (hdflux_log : ∀ i, Integrable (fun x =>
      partialDeriv i (fun y => p t₀ y * v t₀ y i) x * Real.log (p t₀ x / pStar x)))
    (hflux_log : ∀ i, Integrable (fun x => p t₀ x * v t₀ x i * Real.log (p t₀ x / pStar x)))
    (hflux_score : ∀ i, Integrable (fun x =>
      v t₀ x i * (score (p t₀) x i - score pStar x i) * p t₀ x)) :
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
      (∫ x, (v t₀ x ⬝ᵥ (score (p t₀) x - score pStar x)) * p t₀ x) t₀ := by
  have hdiv_int : Integrable (fun x => divergence (fun y => p t₀ y • v t₀ y) x) :=
    integrable_finsetSum Finset.univ fun i _ => hdflux i
  have hdivL_int : Integrable (fun x =>
      -(divergence (fun y => p t₀ y • v t₀ y) x) * Real.log (p t₀ x / pStar x)) := by
    have := integrable_finsetSum Finset.univ fun i _ => (hdflux_log i).fun_neg
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [divergence_smul_apply, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
  have hsplit : ∀ x, -(divergence (fun y => p t₀ y • v t₀ y) x) *
      (Real.log (p t₀ x / pStar x) + 1) =
      -(divergence (fun y => p t₀ y • v t₀ y) x) * Real.log (p t₀ x / pStar x) +
        -(divergence (fun y => p t₀ y • v t₀ y) x) := fun x => by ring
  have hF'_int : Integrable (fun x => -(divergence (fun y => p t₀ y • v t₀ y) x) *
      (Real.log (p t₀ x / pStar x) + 1)) := by
    simp_rw [hsplit]
    exact hdivL_int.add hdiv_int.fun_neg
  have hpStar_meas : AEMeasurable pStar := hpStar.continuous.measurable.aemeasurable
  have hF_meas : ∀ᶠ t in nhds t₀,
      AEStronglyMeasurable (fun x => p t x * Real.log (p t x / pStar x)) := by
    filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
    have hpt := (hp_meas t ht).aemeasurable
    exact (hpt.mul (hpt.div hpStar_meas).log).aestronglyMeasurable
  have h_diff : ∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      HasDerivAt (fun s => p s x * Real.log (p s x / pStar x))
        (-(divergence (fun y => p t y • v t y) x) * (Real.log (p t x / pStar x) + 1)) t :=
    Filter.Eventually.of_forall fun x t _ =>
      hasDerivAt_mul_log_div (hce t x) (hpos t x) (hpStar_pos x)
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ hε) hF_meas hKL hF'_int.aestronglyMeasurable h_bound hbound h_diff
  convert hderiv using 1
  simp_rw [hsplit]
  rw [integral_add hdivL_int hdiv_int.fun_neg, integral_neg,
    integral_divergence_flux_eq_zero hp₀ hv₀ hflux hdflux, neg_zero, add_zero,
    integral_neg_divergence_mul_log_div hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hdflux_log
      hflux_log hflux_score]

/-- **(II) Time derivative of KL along a transport flow, Stein form (FL-1).** Under
the hypotheses of `hasDerivAt_klIntegral`, together with the Stein-identity integrability
hypotheses at `t₀` (`∂ᵢvᵢ · p` and `vᵢ (∇log p)ᵢ p` integrable for `p = p_{t₀}`,
`v = v_{t₀}`), the map `t ↦ ∫ p_t log(p_t/pStar)` is differentiable at `t₀` with derivative
`-∫ (div v_{t₀} + v_{t₀} · ∇log pStar) p_{t₀}`. -/
theorem hasDerivAt_klIntegral_stein_form {p : ℝ → (Fin d → ℝ) → ℝ}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {t₀ ε : ℝ} {bound : (Fin d → ℝ) → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hε : 0 < ε)
    (hp_meas : ∀ t ∈ Metric.ball t₀ ε, AEStronglyMeasurable (p t))
    (hKL : Integrable (fun x => p t₀ x * Real.log (p t₀ x / pStar x)))
    (h_bound : ∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => p t y • v t y) x) * (Real.log (p t x / pStar x) + 1)‖ ≤ bound x)
    (hbound : Integrable bound)
    (hp₀ : Differentiable ℝ (p t₀)) (hv₀ : ∀ i, Differentiable ℝ (fun x => v t₀ x i))
    (hflux : ∀ i, Integrable (fun x => p t₀ x * v t₀ x i))
    (hdflux : ∀ i, Integrable (fun x => partialDeriv i (fun y => p t₀ y * v t₀ y i) x))
    (hdflux_log : ∀ i, Integrable (fun x =>
      partialDeriv i (fun y => p t₀ y * v t₀ y i) x * Real.log (p t₀ x / pStar x)))
    (hflux_log : ∀ i, Integrable (fun x => p t₀ x * v t₀ x i * Real.log (p t₀ x / pStar x)))
    (hflux_score : ∀ i, Integrable (fun x =>
      v t₀ x i * (score (p t₀) x i - score pStar x i) * p t₀ x))
    (hdv : ∀ i, Integrable (fun x => partialDeriv i (fun y => v t₀ y i) x * p t₀ x))
    (hvs : ∀ i, Integrable (fun x => v t₀ x i * score (p t₀) x i * p t₀ x)) :
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
      (-∫ x, (divergence (v t₀) x + v t₀ x ⬝ᵥ score pStar x) * p t₀ x) t₀ :=
  (hasDerivAt_klIntegral hpos hpStar_pos hpStar hce hε hp_meas hKL h_bound hbound hp₀ hv₀
    hflux hdflux hdflux_log hflux_log hflux_score).congr_deriv
    (integral_transport_eq_stein_form hp₀ (hpos t₀) hv₀ hdv hvs hflux hflux_score)

/-- **(II) Time derivative of KL, fixed-time hypotheses discharged (FL-1).** Let
`p : ℝ → (Fin d → ℝ) → ℝ` be everywhere positive and satisfy the strong continuity equation
`∂ₜ p_t(x) = -div(p_t v_t)(x)` for all `t, x`; let `pStar` be everywhere positive and `C¹`;
assume the domination hypotheses of `hasDerivAt_klIntegral` (`ε > 0`, measurability of `p t`
on `B(t₀, ε)`, finite `KL(p_{t₀} ‖ pStar)`, integrable `bound` dominating the pointwise time
derivative on `B(t₀, ε)`). If moreover `p_{t₀}` is `C¹` and `v_{t₀}` is `C¹` with compact
support, then `t ↦ ∫ p_t log(p_t/pStar)` has derivative at `t₀` equal both to
`∫ (v_{t₀} · (∇log p_{t₀} - ∇log pStar)) p_{t₀}` and to
`-∫ (div v_{t₀} + v_{t₀} · ∇log pStar) p_{t₀}`. The domination hypotheses are **not**
discharged. -/
theorem hasDerivAt_klIntegral_of_hasCompactSupport {p : ℝ → (Fin d → ℝ) → ℝ}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {t₀ ε : ℝ} {bound : (Fin d → ℝ) → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : ContDiff ℝ 1 pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hε : 0 < ε)
    (hp_meas : ∀ t ∈ Metric.ball t₀ ε, AEStronglyMeasurable (p t))
    (hKL : Integrable (fun x => p t₀ x * Real.log (p t₀ x / pStar x)))
    (h_bound : ∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => p t y • v t y) x) * (Real.log (p t x / pStar x) + 1)‖ ≤ bound x)
    (hbound : Integrable bound)
    (hp₀ : ContDiff ℝ 1 (p t₀)) (hv₀ : ContDiff ℝ 1 (v t₀))
    (hv₀_supp : HasCompactSupport (v t₀)) :
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
      (∫ x, (v t₀ x ⬝ᵥ (score (p t₀) x - score pStar x)) * p t₀ x) t₀ ∧
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
      (-∫ x, (divergence (v t₀) x + v t₀ x ⬝ᵥ score pStar x) * p t₀ x) t₀ :=
  ⟨hasDerivAt_klIntegral hpos hpStar_pos (hpStar.differentiable one_ne_zero) hce hε hp_meas hKL
      h_bound hbound (hp₀.differentiable one_ne_zero)
      (fun i => (contDiff_coord hv₀ i).differentiable one_ne_zero)
      (integrable_flux hp₀ hv₀ hv₀_supp) (integrable_dflux hp₀ hv₀ hv₀_supp)
      (integrable_dflux_log hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hv₀_supp)
      (integrable_flux_log hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hv₀_supp)
      (integrable_coord_score_sub hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hv₀_supp),
    hasDerivAt_klIntegral_stein_form hpos hpStar_pos (hpStar.differentiable one_ne_zero) hce hε
      hp_meas hKL h_bound hbound (hp₀.differentiable one_ne_zero)
      (fun i => (contDiff_coord hv₀ i).differentiable one_ne_zero)
      (integrable_flux hp₀ hv₀ hv₀_supp) (integrable_dflux hp₀ hv₀ hv₀_supp)
      (integrable_dflux_log hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hv₀_supp)
      (integrable_flux_log hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hv₀_supp)
      (integrable_coord_score_sub hp₀ hpStar (hpos t₀) hpStar_pos hv₀ hv₀_supp)
      (integrable_dcoord hp₀ hv₀ hv₀_supp) (integrable_coord_score hp₀ (hpos t₀) hv₀ hv₀_supp)⟩

end FormalizeSampling.KLTransport
