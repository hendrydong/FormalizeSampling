module

public import FormalizeSampling.ScoreEstimation.SteinObjective
public import FormalizeSampling.Identities.KLTransportVariation

/-!
# PFG: KL dissipation, the discharged first variation, and Theorem 1

Registry IDs: **FL-2** (preconditioned KL dissipation identity), **FL-3** (approximate
minimiser implies a quantitative KL decrease), **FL-4** (log-Sobolev based exponential KL
convergence), **PFG Theorem 1**; they consume FL-1 (II) (`Identities/KLTransportVariation`)
and SE-1 / PFG Proposition 1 (`ScoreEstimation/SteinObjective`). Paper: Dong, Wang, Lin,
Zhang, ICLR 2023 (arXiv 2211.13954 v2): Eq. (1) (continuity equation), Eq. (2) (KL), Eq. (3)
(KL first variation, App. A.1), assumptions [A1]-[A4] (Section 2.2), Theorem 1 (proof in
App. A.5, Eqs. (31)-(32)).

## Setting and conventions

* `p : ℝ → (Fin d → ℝ) → ℝ` is the family of particle densities `p_t`, positive; `pStar` is
  the target density, everywhere positive and differentiable. The KL divergence of Eq. (2) is
  `D(t) = klDivDensity (p t) pStar = ∫ log(p_t/p⋆) d(p_t dx) = ∫ p_t log(p_t/p⋆) dx`
  (`klDivDensity_eq_integral`; for probability densities with finite KL it is Mathlib's
  `klDiv`, see `KLTransport.klDiv_withDensity_eq_integral`). Natural logarithm.
* **The dynamics is modelled, not constructed.** The family `p` is assumed to satisfy the
  strong continuity equation `∂ₜ p_t(x) = -div(p_t g_t)(x)` of Eq. (1) pointwise (hypothesis
  `hce`), with the velocity `g` actually used by the algorithm.
* `H` is a constant positive-definite matrix, independent of `x`, in FL-2 and
  `klDecay_of_approxVelocity`.
  The paper allows a time-dependent, state-independent `H_t` ("estimated at time `t`");
  `klDecay_of_approxVelocity_timeDependent` covers that case with a uniform bound `λ_max(H_t) ≤ m`.
* `v⋆_t = idealVelocity H (score (p t)) (score pStar) = H⁻¹ ∇ln(p⋆/p_t)` and
  `I_{H⁻¹}(t) = ∫ ‖∇log p_t - ∇log p⋆‖²_{H⁻¹} p_t dx`.
* [A4] is `KLDecay.LogSobolevAlong lam` with `lam` the paper's `μ`, in the paper's
  convention `KL ≤ I / (2μ)` (Eq. (31)), where `I = relFisher` is the unweighted relative
  Fisher information under `p_t dx`.
* `λ_max(H) ≤ m` is written `∀ u, sqNormH H u ≤ m * (u ⬝ᵥ u)`; only this upper bound is used
  (the paper writes `λ_max(H) = m`).

## Time domain of the flow

* **Free velocity.** The Theorem 1 statements take a free velocity field `g`. Their plain
  forms state `hpos` and `hce` for every `t ∈ ℝ`; their `_local` forms
  (`klDecay_of_approxVelocity_local`,
  `klDecay_of_idealVelocity_local`, `klDecay_of_approxVelocity_timeDependent_local`,
  `klDecay_of_steinMinimiser_local`) need them only for `t > -δ`, some `δ > 0`. The plain forms
  are the case `δ = 1`. The `_local` forms are proved through `exists_flow_extension`: a flow
  with free velocity on `(-δ, ∞)` extends to all of `ℝ` by a `C¹` time change on `(-∞, -δ/2]`
  that rescales the velocity. A two-sided neighbourhood of `t = 0` is still needed, because
  `HasDerivAt` at `0` is two-sided; a right derivative at `0` alone does not suffice here.
* **State-tied velocity.** `hasDerivAt_klIntegral_idealVelocity` and
  `TransportKLRegularity.hasDerivAt_klDivDensity_idealVelocity` state `hce` with the ideal
  velocity `v⋆_t`, which depends on the state `p_t`, for every `t ∈ ℝ` (these are
  exactly the hypotheses of `KLTransport.hasDerivAt_klIntegral` with `v = v⋆`). The time change
  does not apply there, so these two theorems require an **eternal (ancient) positive solution
  of the ideal PFG equation**. Example: for `H = I`, `p⋆ = N(0, I)` the ideal flow is the
  Ornstein–Uhlenbeck Fokker–Planck flow, with `Σ_t = I + e^{-2t}(Σ_0 - I)`. It degenerates at
  a finite negative time unless `Σ_0 ⪰ I`, so these two theorems do not cover the ideal flow
  from `N(0, σ² I)` with `σ < 1`. Use instead the free-velocity forms
  `hasDerivAt_klIntegral_of_eq_idealVelocity`,
  `TransportKLRegularity.hasDerivAt_klDivDensity_of_eq_idealVelocity_local` and
  `klDecay_of_idealVelocity(_local)`. There the velocity must equal `v⋆` only at the times
  considered
  (`t₀`, respectively all `t ≥ 0`). The ideal flow on `(-δ, ∞)` is the case `g_t = v⋆_t`,
  `hg := fun _ _ => rfl`.

## Main results

* `TransportKLRegularity p pStar v t₀`: the explicit time-local regularity of FL-1 (II) at
  `t₀`, bundling every hypothesis of `KLTransport.hasDerivAt_klIntegral` except positivity,
  the target's regularity and the continuity equation. Wrappers and tools:
  `TransportKLRegularity.hasDerivAt_klIntegral`, `TransportKLRegularity.hasDerivAt_klDivDensity`
  (transport form of Eq. (3)), `TransportKLRegularity.hasDerivAt_klDivDensity_stein_form`
  (literal Eq. (3)), `TransportKLRegularity.hasDerivAt_klDivDensity_local` (flow on
  `(-δ, ∞)`), `TransportKLRegularity.integrable_rate`, `TransportKLRegularity.congr`
  (locality in time), `exists_flow_extension`.
* **FL-2 (attributed to Eq. (3) plus algebra, not to Theorem 1).**
  `hasDerivAt_klIntegral_of_eq_idealVelocity`: under the hypotheses of
  `KLTransport.hasDerivAt_klIntegral` for a free velocity `v` with `v_{t₀} = v⋆_{t₀}`,
  `dD/dt(t₀) = -I_{H⁻¹}(t₀) ≤ 0`. `hasDerivAt_klIntegral_idealVelocity` is the form
  `v_t = v⋆_t` for all `t` (eternal ideal flow, see above). Bundled forms:
  `TransportKLRegularity.hasDerivAt_klDivDensity_of_eq_idealVelocity_local` (flow on
  `(-δ, ∞)`, free velocity) and `TransportKLRegularity.hasDerivAt_klDivDensity_idealVelocity`
  (eternal ideal flow). Pointwise algebra: `idealVelocity_dotProduct_mul`.
* **Discharge of `KLFirstVariation`.** `klFirstVariation_of_regularity` and
  `klFirstVariation_of_regularity_local`: the named hypothesis
  `KLDecay.KLFirstVariation` of the convergence layer holds whenever the continuity
  equation holds (on `ℝ`, resp. on `(-δ, ∞)`) and `TransportKLRegularity` holds at every
  `t ≥ 0`. The convergence theorems below therefore depend only on the modelled flow with
  explicit regularity, [A3] and [A4].
* **FL-3.** `rate_le_of_approx` (one time, paper constant): if
  `∫ ‖g - v⋆‖²_H p ≤ ε I_{H⁻¹}` then `∫ g ⬝ᵥ ∇ln(p/p⋆) p ≤ -((1 - ε)/2) I_{H⁻¹}`.
* **FL-4 / PFG Theorem 1 (Conditional).** `klDecay_of_approxVelocity` (both claims of Theorem 1
  for the
  velocity used, with [A3] in velocity form), `klDecay_of_steinMinimiser` ([A3] in the
  paper's form for some `f_t ∈ F_t`, transferred to the minimiser `g_t` through Proposition 1
  by `a3_of_isMinOn`), `klDecay_of_approxVelocity_timeDependent` (time-dependent `H_t`) and
  `klDecay_of_idealVelocity` (`ε = 0`: velocity equal to `v⋆_t` for `t ≥ 0`, giving
  `dD/dt = -I_{H⁻¹}` and the rate `exp(-2μt/m)`, via `KLDecay.exp_decay_idealVelocity`); each
  has a `_local` form (see above).
* Helpers: `klDivDensity_eq_integral` (the density KL as a Lebesgue integral, for
  a.e.-measurable densities), `integrable_fisher_of_dissipation` (under
  `λ_max(H) ≤ m`, finite `I_{H⁻¹}` gives finite `I`, so the LSI's Fisher information is a
  genuine integral).
* Nonvacuity (all degenerate, `D ≡ 0`, stationary flow `p_t = p⋆`, `g = 0`, for every positive
  differentiable `p⋆`): `stationary_transportKLRegularity`,
  `klDecay_of_approxVelocity_hypotheses_stationary`,
  `klDecay_of_idealVelocity_hypotheses_stationary`,
  `klDecay_of_approxVelocity_timeDependent_hypotheses_stationary`,
  `klDecay_of_steinMinimiser_hypotheses_stationary` (with `F t = {0}`). Global hypotheses
  imply the `_local` ones, so these also cover the `_local` forms.

## Paper item or setting ↔ Lean hypothesis or declaration

| Paper item or setting of this file | Lean | Kind |
| --- | --- | --- |
| Eq. (1) continuity equation | `hce` (strong, pointwise; `t > -δ` or `t ∈ ℝ`) | modelling |
| Eq. (2) KL | `klDivDensity (p t) pStar` | definition |
| Eq. (3), literal Stein form | `hasDerivAt_klDivDensity_stein_form`† | Verified* |
| Eq. (3), transport form (App. A.1) | `hasDerivAt_klDivDensity`†, `…_local`† | Verified* |
| Eq. (3) for all `t ≥ 0` | `klFirstVariation_of_regularity(_local)` | Verified* |
| Eq. (3) at `g = v⋆` (FL-2) | `hasDerivAt_klIntegral_of_eq_idealVelocity` | Verified* |
| FL-2, ideal flow on all of `ℝ` | `hasDerivAt_klIntegral_idealVelocity` | Verified* |
| Eqs. (4)-(7), Prop. 1 | `isMinOn_steinObjective_iff`, `a3_of_isMinOn` | Verified |
| [A1] positive-definite discrepancy | not used (only Proposition 2 needs it) | — |
| [A1] closure under scalars | only `c = -1` (`hneg`, minimiser variant) | modelling |
| [A1] closedness of `F` | not used; the argmin is an assumed minimiser `hmin` | — |
| [A1] tail condition (with `p⋆`) | integrability under `p_t` (`hreg`, `Admissible`) | regularity |
| [A2] positivity of `p_t`, `p⋆` | `hpos`, `hpStar_pos` | regularity |
| [A2] `L`-smooth, `𝔼‖x‖² < ∞`, Lemma 1 | not used; finiteness: `hdiss`, `herr`, `hreg` | — |
| [A3] `ε`-approximation | `hA3`, one `ε < 1` for all `t ≥ 0` | Conditional |
| [A4] `μ`-LSI | `hLSI : LogSobolevAlong lam …`, `lam = μ` | Conditional |
| `λ_max(H) = m` | `hspec` (upper bound only) | spectral |
| setting: `H` SPD, `x`-independent | `hH` | regularity |
| setting: flow exists, positive, `C¹` | `hpos`, `hce`, `hreg` | modelling + regularity |
| setting: argmin exists | `hmin` (minimiser variant only) | Conditional |
| setting: finite `I_{H⁻¹}(t)` | `hdiss` | regularity |
| setting: Stein IBP for every `f ∈ F` | `Admissible` (minimiser variant) | regularity |
| setting: `D(0) < ∞`, continuity at `0` | `hreg 0` (`integrable_kl`, `HasDerivAt`) | regularity |
| setting: `λ_min(H)` bounded below | not needed here | — |

† = in namespace `TransportKLRegularity`. Verified* = Verified relative to a modelled flow,
following the FL-1 precedent of `Identities/KLTransportVariation`: the flow (`hpos`, `hce`)
is a modelling hypothesis and `hreg` (with `hdv`, `hvs` for the Stein form) is explicit
regularity; neither packages the statement proved.

[A3] in velocity form: the comparison field here is `v⋆_t`, while the paper's [A3] is written
with `H⁻¹∇ln(p_t/p⋆) = -v⋆_t` (equivalent because `F = -F`; `klDecay_of_steinMinimiser` states
the paper's sign literally); the Grönwall step uses one `ε` for all `t`; and [A3] is stated
for the velocity `g_t` itself, while the paper's form is for some `f_t ∈ F` (the bridge is
Proposition 1, `a3_of_isMinOn`). `0 ≤ ε` is not needed; `ε < 1` suffices.

Status: **Verified** (relative to the modelled flow, as FL-1): FL-2, the two forms of
Eq. (3), the (f) discharge of `KLFirstVariation`, FL-3 at one time (`rate_le_of_approx`),
`a3_of_isMinOn`, `exists_flow_extension` and the nonvacuity instances. **Conditional**: the
Theorem 1 statements, on [A3] (`hA3`), [A4] (`hLSI`) and, in the minimiser variant, the assumed
argmin (`hmin`); their flow hypotheses `hpos`, `hce`, `hreg` are modelling + regularity
hypotheses, as above.

## What is NOT proved here

* No existence, uniqueness, positivity or smoothness of the PFG flow: the family `p`, its
  continuity equation and `TransportKLRegularity` are hypotheses in this file. For the
  non-degenerate OU probability flow all hypotheses are discharged in
  `ProbabilityFlowOUMoment.klDecay_of_idealVelocity_local_ou_moment` (finite fourth moment, in
  particular bounded support).
* No log-Sobolev inequality is proved in this file; the Gaussian case is
  `LogSobolevAlongGaussian.logSobolevAlong_gaussian`. The nonvacuity instances here are the
  stationary flow, where `D ≡ 0`: they show that the hypotheses are jointly satisfiable, not
  that they hold along a nontrivial flow.
* `HasDerivAt` at `t = 0` is two-sided, so every theorem needs the flow on some `(-δ, ∞)`; a
  flow given only for `t ≥ 0`, with a right derivative at `0`, is not covered. The two theorems
  whose `hce` uses the state-dependent `v⋆_t` for all `t ∈ ℝ` need an eternal ideal flow (see
  "Time domain").
* Proposition 2, Lemma 1, the constant `1 - ε` for a minimiser over a cone (by orthogonality),
  finite particles, time discretisation, the inner optimisation loop and the
  code's estimated preconditioner are not formalised. (The constant `1 - √ε` for any velocity
  is `ApproximateVelocity.transport_rate_le_sharp`.)
-/

@[expose] public section

open Matrix MeasureTheory

namespace FormalizeSampling
namespace KLDissipation

open SPD KLDecay SteinObjective

variable {d : ℕ}

/-- **Time-local regularity for the KL first variation (FL-1 (II)) at time `t₀`.** For a
family of densities `p`, a target density `pStar` and a velocity field `v`, this bundles the
domination and fixed-time hypotheses of `KLTransport.hasDerivAt_klIntegral`: there are `ε > 0`
and an integrable `bound` such that `p t` is a.e.-strongly measurable for `t ∈ B(t₀, ε)` and
`|-div(p_t v_t)(x) (log(p_t(x)/pStar(x)) + 1)| ≤ bound x` for a.e. `x` and all
`t ∈ B(t₀, ε)`; `p_{t₀} log(p_{t₀}/pStar)` is integrable (finite KL at `t₀`); `p_{t₀}` and the
coordinates of `v_{t₀}` are differentiable; and the flux integrands `p vᵢ`, `∂ᵢ(p vᵢ)`,
`∂ᵢ(p vᵢ) log(p/pStar)`, `p vᵢ log(p/pStar)` and `vᵢ ((∇log p)ᵢ - (∇log pStar)ᵢ) p` are
integrable at `t₀`. These are explicit regularity hypotheses on the (given) flow, playing the
role of the paper's [A1] tail condition and [A2]; they are not proved in this file. For the
OU probability flow they are proved in `ProbabilityFlowOU.transportKLRegularity_ou` (bounded
support) and `ProbabilityFlowOUMoment.transportKLRegularity_ou_moment` (finite fourth moment). -/
structure TransportKLRegularity (p : ℝ → (Fin d → ℝ) → ℝ) (pStar : (Fin d → ℝ) → ℝ)
    (v : ℝ → (Fin d → ℝ) → Fin d → ℝ) (t₀ : ℝ) : Prop where
  /-- Local domination of the time derivative of `p_t log(p_t/pStar)` near `t₀`. -/
  domination : ∃ ε > 0, ∃ bound : (Fin d → ℝ) → ℝ,
    (∀ t ∈ Metric.ball t₀ ε, AEStronglyMeasurable (p t)) ∧
    (∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => p t y • v t y) x) * (Real.log (p t x / pStar x) + 1)‖ ≤
        bound x) ∧
    Integrable bound
  /-- Finite KL at `t₀`: `p_{t₀} log(p_{t₀}/pStar)` is integrable. -/
  integrable_kl : Integrable (fun x => p t₀ x * Real.log (p t₀ x / pStar x))
  /-- `p_{t₀}` is differentiable. -/
  differentiable : Differentiable ℝ (p t₀)
  /-- Every coordinate of `v_{t₀}` is differentiable. -/
  differentiable_velocity : ∀ i, Differentiable ℝ (fun x => v t₀ x i)
  /-- The flux coordinates `p_{t₀} vᵢ` are integrable. -/
  integrable_flux : ∀ i, Integrable (fun x => p t₀ x * v t₀ x i)
  /-- The flux partials `∂ᵢ(p_{t₀} vᵢ)` are integrable. -/
  integrable_dflux : ∀ i, Integrable (fun x => partialDeriv i (fun y => p t₀ y * v t₀ y i) x)
  /-- `∂ᵢ(p_{t₀} vᵢ) log(p_{t₀}/pStar)` is integrable. -/
  integrable_dflux_log : ∀ i, Integrable (fun x =>
    partialDeriv i (fun y => p t₀ y * v t₀ y i) x * Real.log (p t₀ x / pStar x))
  /-- `p_{t₀} vᵢ log(p_{t₀}/pStar)` is integrable. -/
  integrable_flux_log : ∀ i, Integrable (fun x =>
    p t₀ x * v t₀ x i * Real.log (p t₀ x / pStar x))
  /-- `vᵢ ((∇log p_{t₀})ᵢ - (∇log pStar)ᵢ) p_{t₀}` is integrable. -/
  integrable_flux_score : ∀ i, Integrable (fun x =>
    v t₀ x i * (score (p t₀) x i - score pStar x i) * p t₀ x)

/-- **FL-1 (II), bundled.** If `p` is everywhere positive and satisfies the strong
continuity equation `∂ₜ p_t = -div(p_t v_t)` for all `t, x`, `pStar` is positive and
differentiable, and `TransportKLRegularity p pStar v t₀` holds, then
`t ↦ ∫ p_t log(p_t/pStar)` has derivative `∫ (v_{t₀} ⬝ᵥ (∇log p_{t₀} - ∇log pStar)) p_{t₀}` at
`t₀` (a repackaging of `KLTransport.hasDerivAt_klIntegral`). -/
theorem TransportKLRegularity.hasDerivAt_klIntegral {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀)
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t) :
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
      (∫ x, (v t₀ x ⬝ᵥ (score (p t₀) x - score pStar x)) * p t₀ x) t₀ := by
  obtain ⟨ε, hε, bound, hmeas, hb, hbint⟩ := hreg.domination
  exact KLTransport.hasDerivAt_klIntegral hpos hpStar_pos hpStar hce hε hmeas
    hreg.integrable_kl hb hbint hreg.differentiable hreg.differentiable_velocity
    hreg.integrable_flux hreg.integrable_dflux hreg.integrable_dflux_log
    hreg.integrable_flux_log hreg.integrable_flux_score

/-- Under `TransportKLRegularity p pStar v t₀`, the first-variation integrand
`(v_{t₀} ⬝ᵥ (∇log p_{t₀} - ∇log pStar)) p_{t₀}` is Lebesgue integrable. -/
theorem TransportKLRegularity.integrable_rate {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀) :
    Integrable (fun x => (v t₀ x ⬝ᵥ (score (p t₀) x - score pStar x)) * p t₀ x) := by
  refine (integrable_finsetSum Finset.univ fun i _ => hreg.integrable_flux_score i).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [dotProduct, Pi.sub_apply, Finset.sum_mul]

/-- **The density KL as a Lebesgue integral.** For a.e.-measurable nonnegative `q`,
`klDivDensity q pStar = ∫ q log(q/pStar) dx`, the KL integral used by
`Identities/KLTransportVariation`. -/
theorem klDivDensity_eq_integral {q pStar : (Fin d → ℝ) → ℝ} (hq : AEMeasurable q)
    (hq0 : ∀ x, 0 ≤ q x) :
    klDivDensity q pStar = ∫ x, q x * Real.log (q x / pStar x) := by
  rw [klDivDensity, integral_densityMeasure hq hq0]
  congr 1
  funext x
  ring

/-- **FL-1 (II) for `klDivDensity` (paper Eq. (3) in transport form, i.e. the intermediate
expression of App. A.1).** Under the hypotheses of `TransportKLRegularity.hasDerivAt_klIntegral`,
`t ↦ KL(p_t ‖ pStar) = klDivDensity (p t) pStar` has derivative
`∫ (v_{t₀} ⬝ᵥ (∇log p_{t₀} - ∇log pStar)) p_{t₀}` at `t₀`. (The two KL expressions agree near
`t₀` because `p t` is measurable there.) The literal Stein form of Eq. (3) is
`TransportKLRegularity.hasDerivAt_klDivDensity_stein_form`. -/
theorem TransportKLRegularity.hasDerivAt_klDivDensity {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀)
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t) :
    HasDerivAt (fun t => klDivDensity (p t) pStar)
      (∫ x, (v t₀ x ⬝ᵥ (score (p t₀) x - score pStar x)) * p t₀ x) t₀ := by
  refine (hreg.hasDerivAt_klIntegral hpos hpStar_pos hpStar hce).congr_of_eventuallyEq ?_
  obtain ⟨ε, hε, -, hmeas, -, -⟩ := hreg.domination
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  exact klDivDensity_eq_integral (hmeas t ht).aemeasurable fun x => (hpos t x).le

/-- **Paper Eq. (3), literal Stein form, for `klDivDensity`.** Under the hypotheses of
`TransportKLRegularity.hasDerivAt_klDivDensity` (positive `p` satisfying `∂ₜ p_t = -div(p_t v_t)`
for all `t, x`, positive differentiable `pStar`, `TransportKLRegularity p pStar v t₀`) and the
two Stein-identity integrability hypotheses at `t₀` (`(∂ᵢ vᵢ) p` and `vᵢ (∇log p)ᵢ p`
integrable for `p = p_{t₀}`, `v = v_{t₀}`), `t ↦ KL(p_t ‖ pStar)` has derivative
`-∫ (div v_{t₀} + v_{t₀} ⬝ᵥ ∇log pStar) p_{t₀}` at `t₀`. This is the paper's Eq. (3)
`dD/dt = -∫ p [∇·g + gᵀ∇ln p⋆]` verbatim; the transport form of
`TransportKLRegularity.hasDerivAt_klDivDensity` is App. A.1's intermediate expression, and the
two agree by `KLTransport.integral_transport_eq_stein_form`. -/
theorem TransportKLRegularity.hasDerivAt_klDivDensity_stein_form {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀)
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hdv : ∀ i, Integrable (fun x => partialDeriv i (fun y => v t₀ y i) x * p t₀ x))
    (hvs : ∀ i, Integrable (fun x => v t₀ x i * score (p t₀) x i * p t₀ x)) :
    HasDerivAt (fun t => klDivDensity (p t) pStar)
      (-∫ x, (divergence (v t₀) x + v t₀ x ⬝ᵥ score pStar x) * p t₀ x) t₀ :=
  (hreg.hasDerivAt_klDivDensity hpos hpStar_pos hpStar hce).congr_deriv
    (KLTransport.integral_transport_eq_stein_form hreg.differentiable (hpos t₀)
      hreg.differentiable_velocity hdv hvs hreg.integrable_flux hreg.integrable_flux_score)

/-- **Locality of `TransportKLRegularity`.** If `TransportKLRegularity p pStar v t₀` holds and
`p' t = p t`, `v' t = v t` for every `t` in a ball `B(t₀, r)` with `r > 0`, then
`TransportKLRegularity p' pStar v' t₀` holds (the domination radius is shrunk to `min ε r`). -/
theorem TransportKLRegularity.congr {p p' : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ}
    {v v' : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ r : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀) (hr : 0 < r)
    (h : ∀ t ∈ Metric.ball t₀ r, p' t = p t ∧ v' t = v t) :
    TransportKLRegularity p' pStar v' t₀ := by
  obtain ⟨ε, hε, bound, hmeas, hb, hbint⟩ := hreg.domination
  have hball : ∀ t ∈ Metric.ball t₀ (min ε r), t ∈ Metric.ball t₀ ε ∧ t ∈ Metric.ball t₀ r :=
    fun t ht => ⟨Metric.ball_subset_ball (min_le_left _ _) ht,
      Metric.ball_subset_ball (min_le_right _ _) ht⟩
  obtain ⟨e1, e2⟩ := h t₀ (Metric.mem_ball_self hr)
  refine ⟨⟨min ε r, lt_min hε hr, bound, fun t ht => ?_, ?_, hbint⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [(h t (hball t ht).2).1]
    exact hmeas t (hball t ht).1
  · filter_upwards [hb] with x hx t ht
    obtain ⟨h1, h2⟩ := h t (hball t ht).2
    rw [h1, h2]
    exact hx t (hball t ht).1
  all_goals
    try rw [e1]
    try rw [e2]
  · exact hreg.integrable_kl
  · exact hreg.differentiable
  · exact hreg.differentiable_velocity
  · exact hreg.integrable_flux
  · exact hreg.integrable_dflux
  · exact hreg.integrable_dflux_log
  · exact hreg.integrable_flux_log
  · exact hreg.integrable_flux_score

/-! ### Flows given only on `(-δ, ∞)`: extension by a time reparametrisation -/

/-- The time change `φ_η` used to extend a flow given on `(-2η, ∞)` to all times: `φ_η t = t`
for `t ≥ -η` and `φ_η t = -η + η (exp((t + η)/η) - 1) ∈ (-2η, -η)` for `t < -η`. -/
private noncomputable def reparam (η t : ℝ) : ℝ :=
  if -η ≤ t then t else -η + η * (Real.exp ((t + η) / η) - 1)

/-- The derivative of `reparam η`: `1` for `t ≥ -η`, `exp((t + η)/η)` for `t < -η`. -/
private noncomputable def reparamDeriv (η t : ℝ) : ℝ :=
  if -η ≤ t then 1 else Real.exp ((t + η) / η)

private theorem reparam_of_le {η t : ℝ} (h : -η ≤ t) : reparam η t = t := by
  simp [reparam, h]

private theorem reparamDeriv_of_le {η t : ℝ} (h : -η ≤ t) : reparamDeriv η t = 1 := by
  simp [reparamDeriv, h]

private theorem neg_two_mul_lt_reparam {η : ℝ} (hη : 0 < η) (t : ℝ) :
    -(2 * η) < reparam η t := by
  unfold reparam
  split_ifs with h
  · linarith
  · have := Real.exp_pos ((t + η) / η)
    nlinarith

private theorem hasDerivAt_reparam_aux {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (fun s => -η + η * (Real.exp ((s + η) / η) - 1))
      (Real.exp ((t + η) / η)) t := by
  have h := ((((hasDerivAt_id t).add_const η).div_const η).exp.sub_const 1).const_mul η
    |>.const_add (-η)
  convert h using 1 <;> simp only [id]
  field_simp

private theorem hasDerivAt_reparam {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (reparam η) (reparamDeriv η t) t := by
  rcases lt_trichotomy t (-η) with h | h | h
  · have hd : reparamDeriv η t = Real.exp ((t + η) / η) := by
      simp [reparamDeriv, not_le.2 h]
    rw [hd]
    refine (hasDerivAt_reparam_aux hη t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [reparam, not_le.2 (show s < -η from hs)]
  · subst h
    rw [reparamDeriv_of_le le_rfl]
    have h1 : HasDerivWithinAt (reparam η) 1 (Set.Ici (-η)) (-η) :=
      (hasDerivAt_id (-η)).hasDerivWithinAt.congr (fun y hy => reparam_of_le hy)
        (reparam_of_le le_rfl)
    have h2 : HasDerivWithinAt (reparam η) 1 (Set.Iic (-η)) (-η) := by
      have := (hasDerivAt_reparam_aux hη (-η)).hasDerivWithinAt (s := Set.Iic (-η))
      rw [show (-η + η) / η = 0 by simp, Real.exp_zero] at this
      refine this.congr (fun y hy => ?_) ?_
      · rcases eq_or_lt_of_le (show y ≤ -η from hy) with hy' | hy'
        · subst hy'
          simp [reparam]
        · simp [reparam, not_le.2 hy']
      · simp [reparam]
    have := h2.union h1
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · rw [reparamDeriv_of_le h.le]
    refine (hasDerivAt_id t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact reparam_of_le (le_of_lt hs)

private theorem divergence_smul_const_smul (q : (Fin d → ℝ) → ℝ) (c : ℝ)
    (w : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    divergence (fun y => q y • (c • w y)) x = c * divergence (fun y => q y • w y) x := by
  unfold divergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hf : (fun y => (q y • (c • w y)) i) = c • fun y => (q y • w y) i := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, partialDeriv, partialDeriv, fderiv_const_smul_field]
  rfl

/-- **Extension of a flow with free velocity from `(-δ, ∞)` to all times.** Let `δ > 0`, and
let `p` be positive and satisfy the strong continuity equation `∂ₜ p_t = -div(p_t g_t)` at every
`t > -δ` and every `x`. Then there are a family `p'` and a velocity `g'` such that `p'` is
positive and satisfies `∂ₜ p'_t = -div(p'_t g'_t)` for **every** `t ∈ ℝ` and `x`, and
`p'_t = p_t`, `g'_t = g_t` for all `t > -δ/2`. Construction: `p'_t = p_{φ(t)}` and
`g'_t = φ'(t) g_{φ(t)}` for a `C¹` time change `φ : ℝ → (-δ, ∞)` equal to the identity on
`[-δ/2, ∞)`. Consequently the theorems below whose continuity equation is stated for all
`t ∈ ℝ` with a **free** velocity lose nothing against a flow defined on `(-δ, ∞)` (their
`_local` versions are proved this way). The construction changes the velocity before time
`-δ/2`, so it does **not** apply when the velocity is tied to the state (e.g. `g_t = v⋆_t`
for all `t`). -/
theorem exists_flow_extension {p : ℝ → (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t) :
    ∃ (p' : ℝ → (Fin d → ℝ) → ℝ) (g' : ℝ → (Fin d → ℝ) → Fin d → ℝ),
      (∀ t x, 0 < p' t x) ∧
      (∀ t x, HasDerivAt (fun s => p' s x) (-(divergence (fun y => p' t y • g' t y) x)) t) ∧
      ∀ t, -(δ / 2) < t → p' t = p t ∧ g' t = g t := by
  have hη : 0 < δ / 2 := by positivity
  have hgt : ∀ t, -δ < reparam (δ / 2) t := fun t => by
    have := neg_two_mul_lt_reparam hη t
    linarith
  refine ⟨fun t => p (reparam (δ / 2) t),
    fun t x => reparamDeriv (δ / 2) t • g (reparam (δ / 2) t) x,
    fun t x => hpos _ (hgt t) x, fun t x => ?_, fun t ht => ?_⟩
  · have h := (hce _ (hgt t) x).comp t (hasDerivAt_reparam hη t)
    simp only [divergence_smul_const_smul]
    convert h using 1
    all_goals first | rfl | ring
  · have h1 := reparam_of_le ht.le
    have h2 := reparamDeriv_of_le ht.le
    refine ⟨by simp only [h1], ?_⟩
    funext x
    simp only [h1, h2, one_smul]

/-- **FL-1 (II) for `klDivDensity`, flow given on `(-δ, ∞)`.** Let `δ > 0` and `t₀ ≥ 0`.
Assume `p` is positive and satisfies `∂ₜ p_t = -div(p_t v_t)` for every `t > -δ` and `x`,
`pStar` is positive and differentiable, and `TransportKLRegularity p pStar v t₀`. Then
`t ↦ KL(p_t ‖ pStar)` has derivative `∫ (v_{t₀} ⬝ᵥ (∇log p_{t₀} - ∇log pStar)) p_{t₀}` at `t₀`.
(Proof: apply `TransportKLRegularity.hasDerivAt_klDivDensity` to the extension of
`exists_flow_extension`, which agrees with `(p, v)` near `t₀`.) -/
theorem TransportKLRegularity.hasDerivAt_klDivDensity_local {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ δ : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀) (hδ : 0 < δ) (ht₀ : 0 ≤ t₀)
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t) :
    HasDerivAt (fun t => klDivDensity (p t) pStar)
      (∫ x, (v t₀ x ⬝ᵥ (score (p t₀) x - score pStar x)) * p t₀ x) t₀ := by
  obtain ⟨p', v', hpos', hce', hagree⟩ := exists_flow_extension hδ hpos hce
  have hr : 0 < t₀ + δ / 2 := by linarith
  have hreg' : TransportKLRegularity p' pStar v' t₀ := by
    refine hreg.congr hr fun t ht => hagree t ?_
    rw [Metric.mem_ball, Real.dist_eq] at ht
    linarith [neg_abs_le (t - t₀)]
  have h := hreg'.hasDerivAt_klDivDensity hpos' hpStar_pos hpStar hce'
  obtain ⟨e1, e2⟩ := hagree t₀ (by linarith)
  rw [e1, e2] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (show -(δ / 2) < t₀ by linarith)] with t ht
  rw [(hagree t ht).1]

/-- **Pointwise dissipation algebra (FL-2).** For any matrix `H`, fields `s, sStar`, weight
`q` and point `x`, with `v⋆ = H⁻¹ (sStar - s)`:
`(v⋆(x) ⬝ᵥ (s x - sStar x)) q x = -(‖s x - sStar x‖²_{H⁻¹} q x)`. -/
theorem idealVelocity_dotProduct_mul (H : Matrix (Fin d) (Fin d) ℝ)
    (s sStar : (Fin d → ℝ) → Fin d → ℝ) (q : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (idealVelocity H s sStar x ⬝ᵥ (s x - sStar x)) * q x =
      -(sqNormH H⁻¹ (s x - sStar x) * q x) := by
  rw [idealVelocity, dotProduct_comm, ← neg_sub (s x) (sStar x), Matrix.mulVec_neg,
    dotProduct_neg, sqNormH, neg_mul]

/-- **FL-2 with a free velocity (paper Eq. (3) plus algebra).** Let `H` be positive definite
(constant). Assume exactly the hypotheses of `KLTransport.hasDerivAt_klIntegral` for a velocity
field `v` (positivity of `p`, the strong continuity equation `∂ₜ p_t = -div(p_t v_t)` for all
`t, x`, positive differentiable `pStar`, the local domination hypotheses near `t₀` and the
fixed-time differentiability and flux-integrability hypotheses at `t₀`), and that at the time
`t₀` the velocity is the ideal PFG direction, `v_{t₀} = H⁻¹ (∇log pStar - ∇log p_{t₀})`
(`hv`). Then `d/dt ∫ p_t log(p_t/p⋆) |_{t₀} = -∫ ‖∇log p_{t₀} - ∇log p⋆‖²_{H⁻¹} p_{t₀} dx`,
and this value is `≤ 0`. Only `v_{t₀}` enters the derivative, so the velocity at other times is
unconstrained: no eternal solution of the ideal PFG equation is needed. -/
theorem hasDerivAt_klIntegral_of_eq_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ ε : ℝ} {bound : (Fin d → ℝ) → ℝ}
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
    (hv : v t₀ = idealVelocity H (score (p t₀)) (score pStar)) :
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
        (-∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x) t₀ ∧
      -∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x ≤ 0 := by
  have h := KLTransport.hasDerivAt_klIntegral hpos hpStar_pos hpStar hce hε
    hp_meas hKL h_bound hbound hp₀ hv₀ hflux hdflux hdflux_log hflux_log hflux_score
  rw [hv] at h
  simp_rw [idealVelocity_dotProduct_mul, integral_neg] at h
  refine ⟨h, ?_⟩
  rw [neg_nonpos]
  exact integral_nonneg fun x => mul_nonneg (sqNormH_nonneg (inv_posDef hH) _) (hpos t₀ x).le

/-- **FL-2: preconditioned KL dissipation identity along the ideal PFG flow (paper Eq. (3)
plus algebra).** Let `H` be positive definite (constant; the paper's time-dependent `H_t` is
treated in `klDecay_of_approxVelocity_timeDependent`), and let the flow move along the ideal PFG
velocity
`v_t = v⋆_t = H⁻¹ (∇log pStar - ∇log p_t)`. Assume exactly the hypotheses of
`KLTransport.hasDerivAt_klIntegral` for this velocity: `p` everywhere positive and satisfying
the strong continuity equation `∂ₜ p_t = -div(p_t v⋆_t)` for all `t ∈ ℝ` and `x`; `pStar`
positive and differentiable; the local domination hypotheses near `t₀` (`ε`, `hp_meas`, finite
KL `hKL`, `h_bound`, integrable `bound`); and the fixed-time differentiability and
flux-integrability hypotheses at `t₀`. Then
`d/dt ∫ p_t log(p_t/p⋆) |_{t₀} = -∫ ‖∇log p_{t₀} - ∇log p⋆‖²_{H⁻¹} p_{t₀} dx`, and this value is
`≤ 0`. This is the computation that opens the proof of Theorem 1 (App. A.5), at `g = v⋆`; it
follows from Eq. (3). **Scope:** because the velocity is tied to the state for every
`t ∈ ℝ`, `hce` and `hpos` require an eternal (ancient) positive solution of the ideal PFG
equation; e.g. for `H = I`, `p⋆ = N(0, I)` the ideal flow from `N(0, σ² I)` with `σ < 1`
degenerates at a finite negative time, so it is not covered. The free-velocity versions
`hasDerivAt_klIntegral_of_eq_idealVelocity` and
`TransportKLRegularity.hasDerivAt_klDivDensity_of_eq_idealVelocity_local` avoid this. -/
theorem hasDerivAt_klIntegral_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {t₀ ε : ℝ}
    {bound : (Fin d → ℝ) → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y •
      idealVelocity H (score (p t)) (score pStar) y) x)) t)
    (hε : 0 < ε)
    (hp_meas : ∀ t ∈ Metric.ball t₀ ε, AEStronglyMeasurable (p t))
    (hKL : Integrable (fun x => p t₀ x * Real.log (p t₀ x / pStar x)))
    (h_bound : ∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => p t y • idealVelocity H (score (p t)) (score pStar) y) x) *
        (Real.log (p t x / pStar x) + 1)‖ ≤ bound x)
    (hbound : Integrable bound)
    (hp₀ : Differentiable ℝ (p t₀))
    (hv₀ : ∀ i, Differentiable ℝ (fun x => idealVelocity H (score (p t₀)) (score pStar) x i))
    (hflux : ∀ i, Integrable (fun x =>
      p t₀ x * idealVelocity H (score (p t₀)) (score pStar) x i))
    (hdflux : ∀ i, Integrable (fun x =>
      partialDeriv i (fun y => p t₀ y * idealVelocity H (score (p t₀)) (score pStar) y i) x))
    (hdflux_log : ∀ i, Integrable (fun x =>
      partialDeriv i (fun y => p t₀ y * idealVelocity H (score (p t₀)) (score pStar) y i) x *
        Real.log (p t₀ x / pStar x)))
    (hflux_log : ∀ i, Integrable (fun x =>
      p t₀ x * idealVelocity H (score (p t₀)) (score pStar) x i *
        Real.log (p t₀ x / pStar x)))
    (hflux_score : ∀ i, Integrable (fun x =>
      idealVelocity H (score (p t₀)) (score pStar) x i *
        (score (p t₀) x i - score pStar x i) * p t₀ x)) :
    HasDerivAt (fun t => ∫ x, p t x * Real.log (p t x / pStar x))
        (-∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x) t₀ ∧
      -∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x ≤ 0 :=
  hasDerivAt_klIntegral_of_eq_idealVelocity
    (v := fun t => idealVelocity H (score (p t)) (score pStar)) hH hpos hpStar_pos hpStar hce
    hε hp_meas hKL h_bound hbound hp₀ hv₀ hflux hdflux hdflux_log hflux_log hflux_score rfl

/-- **FL-2, bundled form, along the ideal PFG flow.** Let `H` be positive definite, `p`
everywhere positive and satisfying `∂ₜ p_t = -div(p_t v⋆_t)` for all `t ∈ ℝ` and `x` with
`v⋆_t = H⁻¹ (∇log pStar - ∇log p_t)`, `pStar` positive and differentiable, and
`TransportKLRegularity p pStar v⋆ t₀`. Then `t ↦ KL(p_t ‖ pStar)` has derivative
`-∫ ‖∇log p_{t₀} - ∇log pStar‖²_{H⁻¹} p_{t₀}` at `t₀`, and this value is `≤ 0`. **Scope:** as
for `hasDerivAt_klIntegral_idealVelocity`, `hce` along the state-dependent `v⋆` for all
`t ∈ ℝ` requires an eternal positive solution of the ideal PFG equation;
`TransportKLRegularity.hasDerivAt_klDivDensity_of_eq_idealVelocity_local` needs the flow only on
`(-δ, ∞)` and `v_{t₀} = v⋆_{t₀}` only at `t₀`. -/
theorem TransportKLRegularity.hasDerivAt_klDivDensity_idealVelocity
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {t₀ : ℝ}
    (hreg : TransportKLRegularity p pStar
      (fun t => idealVelocity H (score (p t)) (score pStar)) t₀)
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y •
      idealVelocity H (score (p t)) (score pStar) y) x)) t) :
    HasDerivAt (fun t => klDivDensity (p t) pStar)
        (-∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x) t₀ ∧
      -∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x ≤ 0 := by
  have h := hreg.hasDerivAt_klDivDensity hpos hpStar_pos hpStar hce
  simp_rw [idealVelocity_dotProduct_mul, integral_neg] at h
  refine ⟨h, ?_⟩
  rw [neg_nonpos]
  exact integral_nonneg fun x => mul_nonneg (sqNormH_nonneg (inv_posDef hH) _) (hpos t₀ x).le

/-- **FL-2, bundled, free velocity, flow given on `(-δ, ∞)`.** Let `H` be positive definite,
`δ > 0`, `t₀ ≥ 0`. Assume `p` is positive and satisfies `∂ₜ p_t = -div(p_t v_t)` for every
`t > -δ` and `x`, `pStar` is positive and differentiable,
`TransportKLRegularity p pStar v t₀`, and `v_{t₀} = H⁻¹ (∇log pStar - ∇log p_{t₀})` (`hv`).
Then `t ↦ KL(p_t ‖ pStar)` has derivative `-∫ ‖∇log p_{t₀} - ∇log pStar‖²_{H⁻¹} p_{t₀}` at
`t₀`, and this value is `≤ 0`. The ideal PFG flow on `(-δ, ∞)` is the case `v_t = v⋆_t`; no
eternal solution is needed (e.g. the Ornstein–Uhlenbeck flow from any Gaussian exists on some
`(-δ, ∞)`; its `TransportKLRegularity` is not proved here; for OU marginals at `t₀ > 0` from a
law with finite fourth moment it is `ProbabilityFlowOUMoment.transportKLRegularity_ou_moment`). -/
theorem TransportKLRegularity.hasDerivAt_klDivDensity_of_eq_idealVelocity_local
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {t₀ δ : ℝ}
    (hreg : TransportKLRegularity p pStar v t₀) (hδ : 0 < δ) (ht₀ : 0 ≤ t₀)
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hv : v t₀ = idealVelocity H (score (p t₀)) (score pStar)) :
    HasDerivAt (fun t => klDivDensity (p t) pStar)
        (-∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x) t₀ ∧
      -∫ x, sqNormH H⁻¹ (score (p t₀) x - score pStar x) * p t₀ x ≤ 0 := by
  have h := hreg.hasDerivAt_klDivDensity_local hδ ht₀ hpos hpStar_pos hpStar hce
  rw [hv] at h
  simp_rw [idealVelocity_dotProduct_mul, integral_neg] at h
  refine ⟨h, ?_⟩
  rw [neg_nonpos]
  exact integral_nonneg fun x =>
    mul_nonneg (sqNormH_nonneg (inv_posDef hH) _) (hpos t₀ (by linarith) x).le

/-- **Discharge of `KLDecay.KLFirstVariation` from FL-1 (II).** Let `p` be everywhere
positive and satisfy the strong continuity equation `∂ₜ p_t = -div(p_t v_t)` for all `t, x`,
let `pStar` be positive and differentiable, and assume `TransportKLRegularity p pStar v t` for
every `t ≥ 0`. Then `KLFirstVariation (t ↦ p_t dx) v (t ↦ ∇log p_t) (∇log pStar)
(t ↦ KL(p_t ‖ pStar))` holds: for every `t ≥ 0`, `d/dt KL(p_t ‖ pStar)` exists and equals
`∫ v_t ⬝ᵥ (∇log p_t - ∇log pStar) d(p_t dx)`. -/
theorem klFirstVariation_of_regularity {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar v t) :
    KLFirstVariation (fun t => densityMeasure (p t)) v (fun t => score (p t)) (score pStar)
      (fun t => klDivDensity (p t) pStar) := by
  intro t ht
  rw [integral_densityMeasure (hreg t ht).differentiable.continuous.aemeasurable
    fun x => (hpos t x).le]
  exact (hreg t ht).hasDerivAt_klDivDensity hpos hpStar_pos hpStar hce

/-- **Discharge of `KLDecay.KLFirstVariation`, flow given on `(-δ, ∞)`.** Let `δ > 0`,
let `p` be positive and satisfy `∂ₜ p_t = -div(p_t v_t)` for every `t > -δ` and `x`, let
`pStar` be positive and differentiable, and assume `TransportKLRegularity p pStar v t` for
every `t ≥ 0`. Then `KLFirstVariation (t ↦ p_t dx) v (t ↦ ∇log p_t) (∇log pStar)
(t ↦ KL(p_t ‖ pStar))` holds. -/
theorem klFirstVariation_of_regularity_local {p : ℝ → (Fin d → ℝ) → ℝ}
    {pStar : (Fin d → ℝ) → ℝ} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • v t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar v t) :
    KLFirstVariation (fun t => densityMeasure (p t)) v (fun t => score (p t)) (score pStar)
      (fun t => klDivDensity (p t) pStar) := by
  intro t ht
  rw [integral_densityMeasure (hreg t ht).differentiable.continuous.aemeasurable
    fun x => (hpos t (by linarith) x).le]
  exact (hreg t ht).hasDerivAt_klDivDensity_local hδ ht hpos hpStar_pos hpStar hce

/-- **FL-3 at one time, with the paper's constant (Theorem 1, first claim; App. A.5).** Let `H`
be positive definite, `q ≥ 0` a.e.-measurable, `f` a velocity field, `s, sStar` score fields
and `v⋆ = H⁻¹ (sStar - s)`. Assume `(f ⬝ᵥ (s - sStar)) q`, `‖s - sStar‖²_{H⁻¹} q` and
`‖f - v⋆‖²_H q` are integrable and the approximation bound
`∫ ‖f - v⋆‖²_H q ≤ ε ∫ ‖s - sStar‖²_{H⁻¹} q`. Then the KL rate along `f` satisfies
`∫ (f ⬝ᵥ (s - sStar)) q ≤ -((1 - ε)/2) ∫ ‖s - sStar‖²_{H⁻¹} q` (weighted Cauchy–Schwarz and
Young, via `KLDecay.transport_rate_le`). -/
theorem rate_le_of_approx {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {q : (Fin d → ℝ) → ℝ} (hq : AEMeasurable q) (hq0 : ∀ x, 0 ≤ q x)
    {f s sStar : (Fin d → ℝ) → Fin d → ℝ} {ε : ℝ}
    (hrate : Integrable (fun x => (f x ⬝ᵥ (s x - sStar x)) * q x))
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x) * q x))
    (herr : Integrable (fun x => sqNormH H (f x - idealVelocity H s sStar x) * q x))
    (happrox : ∫ x, sqNormH H (f x - idealVelocity H s sStar x) * q x ≤
      ε * ∫ x, sqNormH H⁻¹ (s x - sStar x) * q x) :
    ∫ x, (f x ⬝ᵥ (s x - sStar x)) * q x ≤
      -((1 - ε) / 2) * ∫ x, sqNormH H⁻¹ (s x - sStar x) * q x := by
  have h := transport_rate_le (μ := densityMeasure q) hH f s sStar
    ((integrable_densityMeasure_iff hq hq0).2 hrate)
    ((integrable_densityMeasure_iff hq hq0).2 hdiss)
    ((integrable_densityMeasure_iff hq hq0).2 herr)
  simp only [integral_densityMeasure hq hq0] at h
  nlinarith

/-- **Finite weighted Fisher information gives finite Fisher information.** Let `H` be positive
definite with `uᵀ H u ≤ m |u|²` for all `u` (`m > 0`, i.e. `λ_max(H) ≤ m`), and `q ≥ 0`
a.e.-measurable. If `‖∇log q - ∇log pStar‖²_{H⁻¹} q` is integrable, then so is
`|∇log q - ∇log pStar|² q` (pointwise `|u|² ≤ m ‖u‖²_{H⁻¹}`; scores are measurable). -/
theorem integrable_fisher_of_dissipation {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u))
    {q pStar : (Fin d → ℝ) → ℝ} (hq : AEMeasurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (score q x - score pStar x) * q x)) :
    Integrable (fun x =>
      ((score q x - score pStar x) ⬝ᵥ (score q x - score pStar x)) * q x) := by
  have h1 := (measurable_score q).sub (measurable_score pStar)
  have hmeas : Measurable fun x =>
      (score q x - score pStar x) ⬝ᵥ (score q x - score pStar x) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp h1).mul ((measurable_pi_apply i).comp h1)
  refine (hdiss.const_mul m).mono' (hmeas.aemeasurable.mul hq).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hb := inv_lower_bound_of_upper_bound hH hm hspec (score q x - score pStar x)
  have hnn : 0 ≤ (score q x - score pStar x) ⬝ᵥ (score q x - score pStar x) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hle : (score q x - score pStar x) ⬝ᵥ (score q x - score pStar x) ≤
      m * sqNormH H⁻¹ (score q x - score pStar x) := by
    have h2 := mul_le_mul_of_nonneg_left hb hm.le
    rwa [← mul_assoc, mul_one_div_cancel hm.ne', one_mul] at h2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hq0 x)), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hle (hq0 x)

/-- **PFG Theorem 1 at `ε = 0` with the exact velocity, flow on `(-δ, ∞)` (FL-2, FL-4;
Conditional).** Constant positive-definite `H` with `λ_max(H) ≤ m` (`m > 0`), `lam > 0`,
`δ > 0`. Let `p` be positive and satisfy `∂ₜ p_t = -div(p_t g_t)` for `t > -δ` with a velocity
`g` that equals the ideal PFG direction `v⋆_t = H⁻¹ ∇ln(p⋆/p_t)` for every `t ≥ 0` (`hg`;
before time `0` it is unconstrained). Assume `pStar` positive and differentiable,
`TransportKLRegularity p pStar g t` and finite `I_{H⁻¹}(t)` (`hdiss`) for `t ≥ 0`, and the LSI
along the flow (`hLSI`, [A4]). Then for every `t ≥ 0`, `dD/dt = -I_{H⁻¹}(t)` (FL-2) and
`D(t) ≤ exp(-2 μ t / m) D(0)`. The ideal flow itself (any positive solution of the ideal PFG
equation on `(-δ, ∞)`) is the case `g_t = v⋆_t`, `hg := fun _ _ => rfl`. -/
theorem klDecay_of_idealVelocity_local {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {m lam δ : ℝ}
    (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hδ : 0 < δ)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hg : ∀ t, 0 ≤ t → g t = idealVelocity H (score (p t)) (score pStar))
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x))
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t → HasDerivAt (fun t => klDivDensity (p t) pStar)
        (-∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) t) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-2 * lam * t / m) * klDivDensity (p 0) pStar := by
  have hmeas : ∀ t, 0 ≤ t → AEMeasurable (p t) := fun t ht =>
    (hreg t ht).differentiable.continuous.aemeasurable
  have hp0 : ∀ t, 0 ≤ t → ∀ x, 0 ≤ p t x := fun t ht x => (hpos t (by linarith) x).le
  have hKL := klFirstVariation_of_regularity_local hδ hpos hpStar_pos hpStar hce hreg
  have hKL' : KLFirstVariation (fun t => densityMeasure (p t))
      (fun t => idealVelocity H (score (p t)) (score pStar)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar) := by
    intro t ht
    have h := hKL t ht
    simp only [hg t ht] at h
    exact h
  refine ⟨fun t ht => ((hreg t ht).hasDerivAt_klDivDensity_of_eq_idealVelocity_local hH hδ ht
    hpos hpStar_pos hpStar hce (hg t ht)).1, ?_⟩
  exact exp_decay_idealVelocity hH hm hspec hlam hKL'
    (fun t ht => (integrable_densityMeasure_iff (hmeas t ht) (hp0 t ht)).2 (hdiss t ht))
    (fun t ht => (integrable_densityMeasure_iff (hmeas t ht) (hp0 t ht)).2
      (integrable_fisher_of_dissipation hH hm hspec (hmeas t ht) (hp0 t ht) (hdiss t ht))) hLSI

/-- **PFG Theorem 1 at `ε = 0` with the exact velocity (FL-2, FL-4; Conditional).** Constant
positive-definite `H` with `λ_max(H) ≤ m` (`m > 0`), `lam > 0`. Let
`p` be positive and satisfy `∂ₜ p_t = -div(p_t g_t)` for all `t, x` (`hce`), where the velocity
`g` equals the ideal PFG direction `v⋆_t = H⁻¹ ∇ln(p⋆/p_t)` for every `t ≥ 0` (`hg`) and is
unconstrained for `t < 0` (so no eternal solution of the ideal PFG equation is required; see
also `klDecay_of_idealVelocity_local` for a flow given only on `(-δ, ∞)`). Assume `pStar` positive
and
differentiable, `TransportKLRegularity p pStar g t` and finite `I_{H⁻¹}(t)` (`hdiss`) for
every `t ≥ 0`, and the LSI along the flow (`hLSI`, [A4]). Then for every `t ≥ 0`,
`dD/dt = -I_{H⁻¹}(t)` (FL-2) and `D(t) ≤ exp(-2 μ t / m) D(0)`. -/
theorem klDecay_of_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {m lam : ℝ}
    (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u)) (hlam : 0 < lam)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hg : ∀ t, 0 ≤ t → g t = idealVelocity H (score (p t)) (score pStar))
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x))
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t → HasDerivAt (fun t => klDivDensity (p t) pStar)
        (-∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) t) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-2 * lam * t / m) * klDivDensity (p 0) pStar :=
  klDecay_of_idealVelocity_local hH hm hspec hlam one_pos (fun t _ => hpos t) hpStar_pos hpStar
    (fun t _ => hce t) hg hreg hdiss hLSI

/-- **PFG Theorem 1 with a time-dependent preconditioner, flow on `(-δ, ∞)` (Conditional).**
As `klDecay_of_approxVelocity_timeDependent`, but positivity `hpos` and the continuity equation
`hce` are
only required for `t > -δ` (`δ > 0`). Hypotheses: `H_t` positive definite with
`λ_max(H_t) ≤ m` for `t ≥ 0`, `lam > 0`, `ε < 1`; `pStar` positive and differentiable;
`TransportKLRegularity`, finite `I_{H_t⁻¹}(t)`, integrable `‖g_t - v⋆_t‖²_{H_t} p_t` and
[A3] in velocity form with `H_t` for `t ≥ 0`; [A4] as `LogSobolevAlong lam`. Conclusions: for
`t ≥ 0`,
`dD/dt ≤ -((1 - ε)/2) ∫ ‖∇log p_t - ∇log p⋆‖²_{H_t⁻¹} p_t` and
`D(t) ≤ exp(-(1 - ε) μ t / m) D(0)`. -/
theorem klDecay_of_approxVelocity_timeDependent_local {H : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hH : ∀ t, 0 ≤ t → (H t).PosDef) {m lam ε δ : ℝ} (hm : 0 < m)
    (hspec : ∀ t, 0 ≤ t → ∀ u : Fin d → ℝ, sqNormH (H t) u ≤ m * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hε : ε < 1) (hδ : 0 < δ)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH (H t) (g t x - idealVelocity (H t) (score (p t)) (score pStar) x) * p t x))
    (hA3 : ∀ t, 0 ≤ t →
      ∫ x, sqNormH (H t) (g t x - idealVelocity (H t) (score (p t)) (score pStar) x) * p t x ≤
        ε * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x)
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t →
      HasDerivAt (fun t => klDivDensity (p t) pStar)
        (∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x) t ∧
      ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
        -((1 - ε) / 2) * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-((1 - ε) * lam * t / m)) * klDivDensity (p 0) pStar
    := by
  have hmeas : ∀ t, 0 ≤ t → AEMeasurable (p t) := fun t ht =>
    (hreg t ht).differentiable.continuous.aemeasurable
  have hp0 : ∀ t, 0 ≤ t → ∀ x, 0 ≤ p t x := fun t ht x => (hpos t (by linarith) x).le
  have hrate : ∀ t, 0 ≤ t → ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
      -((1 - ε) / 2) * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x :=
    fun t ht => rate_le_of_approx (hH t ht) (hmeas t ht) (hp0 t ht) (hreg t ht).integrable_rate
      (hdiss t ht) (herr t ht) (hA3 t ht)
  refine ⟨fun t ht =>
    ⟨(hreg t ht).hasDerivAt_klDivDensity_local hδ ht hpos hpStar_pos hpStar hce,
      hrate t ht⟩, ?_⟩
  have hκ : 0 < 1 - ε := by linarith
  have hdis : ∀ t, 0 ≤ t → ∫ x, g t x ⬝ᵥ (score (p t) x - score pStar x) ∂(densityMeasure (p t))
      ≤ -((1 - ε) / (2 * m)) * relFisher (densityMeasure (p t)) (score (p t)) (score pStar) := by
    intro t ht
    have h1 := fisher_le_dissipation (hH t ht) hm (hspec t ht)
      ((integrable_densityMeasure_iff (hmeas t ht) (hp0 t ht)).2 (hdiss t ht))
      ((integrable_densityMeasure_iff (hmeas t ht) (hp0 t ht)).2
        (integrable_fisher_of_dissipation (hH t ht) hm (hspec t ht) (hmeas t ht) (hp0 t ht)
          (hdiss t ht)))
    rw [integral_densityMeasure (hmeas t ht) (hp0 t ht)] at h1 ⊢
    have h2 := hrate t ht
    have h3 : -((1 - ε) / 2) * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x ≤
        -((1 - ε) / 2) * ((1 / m) * relFisher (densityMeasure (p t)) (score (p t))
          (score pStar)) :=
      mul_le_mul_of_nonpos_left h1 (by linarith)
    have h4 : -((1 - ε) / (2 * m)) * relFisher (densityMeasure (p t)) (score (p t))
        (score pStar) = -((1 - ε) / 2) * ((1 / m) * relFisher (densityMeasure (p t))
          (score (p t)) (score pStar)) := by
      field_simp
    rw [h4]
    linarith
  have key := exp_decay_of_lsi (K := fun t => klDivDensity (p t) pStar)
    (K' := fun t => ∫ x, g t x ⬝ᵥ (score (p t) x - score pStar x) ∂(densityMeasure (p t)))
    (I := fun t => relFisher (densityMeasure (p t)) (score (p t)) (score pStar))
    (c := (1 - ε) / (2 * m)) (by positivity) hlam
    (klFirstVariation_of_regularity_local hδ hpos hpStar_pos hpStar hce hreg) hdis hLSI
  intro t ht
  have h := key t ht
  have he : -2 * lam * ((1 - ε) / (2 * m)) * t = -((1 - ε) * lam * t / m) := by
    field_simp
  rwa [he] at h

/-- **PFG Theorem 1 with a time-dependent, state-independent preconditioner (Conditional).** As
`klDecay_of_approxVelocity`, but with `H_t` positive definite and `λ_max(H_t) ≤ m` for every `t ≥ 0`
(the paper's "for any `t > 0` ... `λ_max(H) = m`"), and the weighted quantities, [A3] and
`v⋆_t = H_t⁻¹ ∇ln(p⋆/p_t)` taken with `H_t`. Conclusions: for `t ≥ 0`,
`dD/dt ≤ -((1 - ε)/2) ∫ ‖∇log p_t - ∇log p⋆‖²_{H_t⁻¹} p_t` and
`D(t) ≤ exp(-(1 - ε) μ t / m) D(0)` (Grönwall through `KLDecay.exp_decay_of_lsi`). The
flow hypotheses `hpos`, `hce` are stated for all `t ∈ ℝ`;
`klDecay_of_approxVelocity_timeDependent_local`
needs them only on `(-δ, ∞)`. -/
theorem klDecay_of_approxVelocity_timeDependent {H : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hH : ∀ t, 0 ≤ t → (H t).PosDef) {m lam ε : ℝ} (hm : 0 < m)
    (hspec : ∀ t, 0 ≤ t → ∀ u : Fin d → ℝ, sqNormH (H t) u ≤ m * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hε : ε < 1)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH (H t) (g t x - idealVelocity (H t) (score (p t)) (score pStar) x) * p t x))
    (hA3 : ∀ t, 0 ≤ t →
      ∫ x, sqNormH (H t) (g t x - idealVelocity (H t) (score (p t)) (score pStar) x) * p t x ≤
        ε * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x)
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t →
      HasDerivAt (fun t => klDivDensity (p t) pStar)
        (∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x) t ∧
      ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
        -((1 - ε) / 2) * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-((1 - ε) * lam * t / m)) * klDivDensity (p 0) pStar
    :=
  klDecay_of_approxVelocity_timeDependent_local hH hm hspec hlam hε one_pos (fun t _ => hpos t)
      hpStar_pos
    hpStar (fun t _ => hce t) hreg hdiss herr hA3 hLSI

/-- **PFG Theorem 1, flow given on `(-δ, ∞)` (FL-3, FL-4; Conditional).** Identical to
`klDecay_of_approxVelocity` (see there for the 1:1 mapping of [A1]-[A4] and of the standing
hypotheses),
except that positivity `hpos` and the continuity equation `hce` with the velocity `g` are only
required for `t > -δ` (some `δ > 0`) instead of all `t ∈ ℝ`. Hypotheses: `H` constant positive
definite, `λ_max(H) ≤ m` (`hspec`, `m > 0`), `lam > 0`, `ε < 1`; `pStar` positive and
differentiable; `TransportKLRegularity p pStar g t`, finite `I_{H⁻¹}(t)` (`hdiss`) and
integrable `‖g_t - v⋆_t‖²_H p_t` (`herr`) for `t ≥ 0`; [A3] in velocity form with one `ε` (`hA3`);
[A4] as `LogSobolevAlong lam` (`hLSI`). Conclusions: for `t ≥ 0`,
`dD/dt = ∫ g_t ⬝ᵥ ∇ln(p_t/p⋆) p_t ≤ -((1 - ε)/2) I_{H⁻¹}(t)` and
`D(t) ≤ exp(-(1 - ε) μ t / m) D(0)`. A two-sided neighbourhood of `t = 0` is still needed
because `HasDerivAt` at `0` is two-sided. This is the constant case `H_t = H` of
`klDecay_of_approxVelocity_timeDependent_local`. -/
theorem klDecay_of_approxVelocity_local {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {m lam ε δ : ℝ}
    (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hε : ε < 1) (hδ : 0 < δ)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH H (g t x - idealVelocity H (score (p t)) (score pStar) x) * p t x))
    (hA3 : ∀ t, 0 ≤ t →
      ∫ x, sqNormH H (g t x - idealVelocity H (score (p t)) (score pStar) x) * p t x ≤
        ε * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t →
      HasDerivAt (fun t => klDivDensity (p t) pStar)
        (∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x) t ∧
      ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
        -((1 - ε) / 2) * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-((1 - ε) * lam * t / m)) * klDivDensity (p 0) pStar
    :=
  klDecay_of_approxVelocity_timeDependent_local (H := fun _ => H) (fun _ _ => hH) hm
    (fun _ _ => hspec) hlam hε hδ hpos hpStar_pos hpStar hce hreg hdiss herr hA3 hLSI

/-- **PFG Theorem 1 (FL-3, FL-4; Conditional).** Constant positive-definite `H` with
`λ_max(H) ≤ m` (`hspec`, `m > 0`), LSI constant `lam > 0` (the paper's `μ`) and `ε < 1`.
Hypotheses, mapped to the paper:
* flow (standing hypothesis, Eq. (1)): `p` everywhere positive (part of [A2]) and satisfying
  `∂ₜ p_t = -div(p_t g_t)` for all `t, x` (`hce`), with `g` the velocity used (a free field, so
  a flow on `(-δ, ∞)` suffices: `klDecay_of_approxVelocity_local`);
* regularity replacing [A1] (tail condition) and [A2]: `pStar` positive and differentiable,
  `TransportKLRegularity p pStar g t` for every `t ≥ 0` (`hreg`), finite weighted relative
  Fisher information `I_{H⁻¹}(t)` (`hdiss`) and integrable error `‖g_t - v⋆_t‖²_H p_t`
  (`herr`);
* [A3], velocity form: `∫ ‖g_t - v⋆_t‖²_H p_t ≤ ε I_{H⁻¹}(t)` for all `t ≥ 0` with one `ε`
  (`hA3`), where `v⋆_t = H⁻¹ ∇ln(p⋆/p_t)`; the paper's sign and its "some `f_t ∈ F`" form are
  handled in `klDecay_of_steinMinimiser`; `0 ≤ ε` is not needed;
* [A4]: `LogSobolevAlong lam` along the flow, `KL(p_t‖p⋆) ≤ I(t)/(2 lam)` (`hLSI`).
**Not used:** from [A1], the positive-definiteness of the discrepancy (only Proposition 2 needs
it), the closedness of `F` and its closure under scalars (there is no class `F` here; `g` is
any velocity); from [A2], the `L`-smoothness of the scores, the second moment `𝔼‖x‖² < ∞` and
Lemma 1 (in this file the finiteness of the integrals is stated directly by `hreg`, `hdiss`
and `herr`). The [A1] tail condition (stated with `p⋆` in the paper) is replaced by
the integrability hypotheses in `hreg`, stated with `p_t`.
Conclusions, as in the paper: for every `t ≥ 0`, `D(t) = KL(p_t ‖ p⋆)` is differentiable with
`dD/dt = ∫ g_t ⬝ᵥ ∇ln(p_t/p⋆) p_t ≤ -((1 - ε)/2) ∫ ‖∇log p_t - ∇log p⋆‖²_{H⁻¹} p_t`, and
`D(t) ≤ exp(-(1 - ε) μ t / m) D(0)`. This is the constant case `H_t = H` of
`klDecay_of_approxVelocity_timeDependent` (Grönwall through `KLDecay.exp_decay_of_lsi`, with
`KLFirstVariation` discharged by `klFirstVariation_of_regularity_local`). -/
theorem klDecay_of_approxVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {m lam ε : ℝ}
    (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hε : ε < 1)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH H (g t x - idealVelocity H (score (p t)) (score pStar) x) * p t x))
    (hA3 : ∀ t, 0 ≤ t →
      ∫ x, sqNormH H (g t x - idealVelocity H (score (p t)) (score pStar) x) * p t x ≤
        ε * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t →
      HasDerivAt (fun t => klDivDensity (p t) pStar)
        (∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x) t ∧
      ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
        -((1 - ε) / 2) * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-((1 - ε) * lam * t / m)) * klDivDensity (p 0) pStar
    :=
  klDecay_of_approxVelocity_local hH hm hspec hlam hε one_pos (fun t _ => hpos t) hpStar_pos hpStar
    (fun t _ => hce t) hreg hdiss herr hA3 hLSI

/-- **Transfer of the paper's [A3] to the minimiser (via Proposition 1).** Let `H` be positive
definite, `q` positive and differentiable with finite `∫ ‖v⋆‖²_H q`, and `F` a set of admissible
fields (`SteinObjective.Admissible`) closed under negation (the case `c = -1` of [A1]). If `g ∈ F`
minimises the PFG objective over `F` and some `f ∈ F` satisfies [A3] with the paper's sign,
`∫ ‖f - H⁻¹ (∇log q - sStar)‖²_H q ≤ ε ∫ ‖∇log q - sStar‖²_{H⁻¹} q`, then the minimiser
satisfies the velocity form `∫ ‖g - v⋆‖²_H q ≤ ε ∫ ‖∇log q - sStar‖²_{H⁻¹} q`. -/
theorem a3_of_isMinOn {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {q : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < q x) (hq : Differentiable ℝ q)
    {sStar : (Fin d → ℝ) → Fin d → ℝ}
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score q) sStar x) * q x))
    {F : Set ((Fin d → ℝ) → Fin d → ℝ)} (hF : ∀ f ∈ F, Admissible H q sStar f)
    (hneg : ∀ f ∈ F, -f ∈ F) {g : (Fin d → ℝ) → Fin d → ℝ} (hg : g ∈ F)
    (hmin : IsMinOn (steinObjective H q sStar) F g)
    {f : (Fin d → ℝ) → Fin d → ℝ} (hf : f ∈ F) {ε : ℝ}
    (hA3 : ∫ x, sqNormH H (f x - H⁻¹ *ᵥ (score q x - sStar x)) * q x ≤
      ε * ∫ x, sqNormH H⁻¹ (score q x - sStar x) * q x) :
    ∫ x, sqNormH H (g x - idealVelocity H (score q) sStar x) * q x ≤
      ε * ∫ x, sqNormH H⁻¹ (score q x - sStar x) * q x := by
  have hmin' := (isMinOn_steinObjective_iff hH hpos hq hv hF hg).1 hmin
  have h := isMinOn_iff.1 hmin' (-f) (hneg f hf)
  have hpt : ∀ x, sqNormH H ((-f) x - idealVelocity H (score q) sStar x) * q x =
      sqNormH H (f x - H⁻¹ *ᵥ (score q x - sStar x)) * q x := by
    intro x
    have : (-f) x - idealVelocity H (score q) sStar x =
        -(f x - H⁻¹ *ᵥ (score q x - sStar x)) := by
      rw [idealVelocity, ← neg_sub (score q x) (sStar x), mulVec_neg, Pi.neg_apply]
      abel
    rw [this, sqNormH_neg]
  simp only [projectionObjective, hpt] at h
  linarith

/-- **PFG Theorem 1 with [A3] in the paper's form, flow on `(-δ, ∞)` (Conditional).** As
`klDecay_of_steinMinimiser`, but positivity `hpos` and the continuity equation `hce` are only
required for `t > -δ` (`δ > 0`). Hypotheses: those of `klDecay_of_approxVelocity_local` without
`herr` and
with [A3] replaced by: admissible classes `F t` closed under negation, `g_t ∈ F t` an
(assumed) minimiser of the PFG objective over `F t`, and some `f ∈ F t` with
`∫ ‖f - H⁻¹ ∇ln(p_t/p⋆)‖²_H p_t ≤ ε I_{H⁻¹}(t)`, one `ε < 1`. Conclusions as in
`klDecay_of_approxVelocity`. -/
theorem klDecay_of_steinMinimiser_local {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {m lam ε δ : ℝ} (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u))
    (hlam : 0 < lam) (hε : ε < 1) (hδ : 0 < δ)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t, -δ < t → ∀ x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t, -δ < t → ∀ x,
      HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x))
    (F : ℝ → Set ((Fin d → ℝ) → Fin d → ℝ))
    (hF : ∀ t, 0 ≤ t → ∀ f ∈ F t, Admissible H (p t) (score pStar) f)
    (hneg : ∀ t, 0 ≤ t → ∀ f ∈ F t, -f ∈ F t)
    (hgF : ∀ t, 0 ≤ t → g t ∈ F t)
    (hmin : ∀ t, 0 ≤ t → IsMinOn (steinObjective H (p t) (score pStar)) (F t) (g t))
    (hA3 : ∀ t, 0 ≤ t → ∃ f ∈ F t,
      ∫ x, sqNormH H (f x - H⁻¹ *ᵥ (score (p t) x - score pStar x)) * p t x ≤
        ε * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t →
      HasDerivAt (fun t => klDivDensity (p t) pStar)
        (∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x) t ∧
      ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
        -((1 - ε) / 2) * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-((1 - ε) * lam * t / m)) * klDivDensity (p 0) pStar
    := by
  have hv : ∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH H (idealVelocity H (score (p t)) (score pStar) x) * p t x) := fun t ht =>
    (integrable_sqNormH_idealVelocity_iff hH (p t) (score pStar)).2 (hdiss t ht)
  have hpt : ∀ t, 0 ≤ t → ∀ x, 0 < p t x := fun t ht => hpos t (by linarith)
  refine klDecay_of_approxVelocity_local hH hm hspec hlam hε hδ hpos hpStar_pos hpStar hce hreg
      hdiss
    (fun t ht => (hF t ht (g t) (hgF t ht)).integrable_sqNormH_sub hH (hpt t ht)
      (hreg t ht).differentiable (hv t ht)) (fun t ht => ?_) hLSI
  obtain ⟨f, hf, hfA3⟩ := hA3 t ht
  exact a3_of_isMinOn hH (hpt t ht) (hreg t ht).differentiable (hv t ht) (hF t ht) (hneg t ht)
    (hgF t ht) (hmin t ht) hf hfA3

/-- **PFG Theorem 1 with [A3] in the paper's form (Conditional).** As `klDecay_of_approxVelocity`,
but [A3]
is stated as in the paper: for each `t ≥ 0` there is a class `F t` of admissible fields for
`p_t` (`SteinObjective.Admissible`: the Stein integration by parts and finiteness, stated
explicitly here as regularity hypotheses), closed under negation ([A1] with `c = -1`); the
velocity `g_t ∈ F t` minimises the PFG objective of Eq. (4) over `F t` (`hmin`; existence of
the argmin is assumed); and some `f ∈ F t` satisfies
`∫ ‖f - H⁻¹ ∇ln(p_t/p⋆)‖²_H p_t ≤ ε I_{H⁻¹}(t)` with one `ε < 1` for all `t` (`hA3`). The
integrability of `‖g_t - v⋆_t‖²_H p_t` is then derived. Conclusions as in
`klDecay_of_approxVelocity`. The
flow hypotheses `hpos`, `hce` are stated for all `t ∈ ℝ`; `klDecay_of_steinMinimiser_local`
needs them only on `(-δ, ∞)`. -/
theorem klDecay_of_steinMinimiser {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {m lam ε : ℝ} (hm : 0 < m) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ m * (u ⬝ᵥ u))
    (hlam : 0 < lam) (hε : ε < 1)
    {p : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ} {g : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ t x, 0 < p t x) (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar)
    (hce : ∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t)
    (hreg : ∀ t, 0 ≤ t → TransportKLRegularity p pStar g t)
    (hdiss : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x))
    (F : ℝ → Set ((Fin d → ℝ) → Fin d → ℝ))
    (hF : ∀ t, 0 ≤ t → ∀ f ∈ F t, Admissible H (p t) (score pStar) f)
    (hneg : ∀ t, 0 ≤ t → ∀ f ∈ F t, -f ∈ F t)
    (hgF : ∀ t, 0 ≤ t → g t ∈ F t)
    (hmin : ∀ t, 0 ≤ t → IsMinOn (steinObjective H (p t) (score pStar)) (F t) (g t))
    (hA3 : ∀ t, 0 ≤ t → ∃ f ∈ F t,
      ∫ x, sqNormH H (f x - H⁻¹ *ᵥ (score (p t) x - score pStar x)) * p t x ≤
        ε * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    (∀ t, 0 ≤ t →
      HasDerivAt (fun t => klDivDensity (p t) pStar)
        (∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x) t ∧
      ∫ x, (g t x ⬝ᵥ (score (p t) x - score pStar x)) * p t x ≤
        -((1 - ε) / 2) * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    ∀ t, 0 ≤ t →
      klDivDensity (p t) pStar ≤ Real.exp (-((1 - ε) * lam * t / m)) * klDivDensity (p 0) pStar
    :=
  klDecay_of_steinMinimiser_local hH hm hspec hlam hε one_pos (fun t _ => hpos t) hpStar_pos
    hpStar (fun t _ => hce t) hreg hdiss F hF hneg hgF hmin hA3 hLSI

private theorem divergence_smul_zero (q : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    divergence (fun y => q y • (0 : Fin d → ℝ)) x = 0 := by
  simp [divergence, partialDeriv]

/-- **Nonvacuity of `TransportKLRegularity`.** For every positive differentiable `pStar` and
every `t₀`, the stationary family `p_t = pStar` with zero velocity satisfies
`TransportKLRegularity`. -/
theorem stationary_transportKLRegularity {pStar : (Fin d → ℝ) → ℝ}
    (hpStar_pos : ∀ x, 0 < pStar x) (hpStar : Differentiable ℝ pStar) (t₀ : ℝ) :
    TransportKLRegularity (fun _ => pStar) pStar (fun _ _ => 0) t₀ := by
  have hlog : ∀ x, Real.log (pStar x / pStar x) = 0 := fun x => by
    rw [div_self (hpStar_pos x).ne', Real.log_one]
  refine ⟨⟨1, one_pos, fun _ => 0, fun t _ => hpStar.continuous.aestronglyMeasurable,
    Filter.Eventually.of_forall fun x t _ => ?_, integrable_zero _ _ _⟩, ?_, hpStar,
    fun i => differentiable_const _, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_⟩
  · simp [divergence, partialDeriv]
  · simp [hlog]
  · simp
  · simp [partialDeriv]
  · simp [partialDeriv]
  · simp
  · simp

/-- **Nonvacuity of PFG Theorem 1's hypotheses.** For every matrix `H`, constants `lam`, `ε` and
every positive differentiable `pStar`, the stationary flow `p_t = pStar`, `g_t = 0` satisfies
the continuity equation `hce`, `TransportKLRegularity` at every `t ≥ 0`, finite weighted
Fisher information, integrable approximation error, [A3] and the LSI-along-the-flow hypothesis
[A4] of `klDecay_of_approxVelocity` (hence also those of `klDecay_of_approxVelocity_local`, for any
`δ > 0`). (Here
`D ≡ 0`; the remaining hypotheses `H.PosDef`, `hspec`, `m > 0`,
`lam > 0`, `ε < 1` hold e.g. for `H = 1`, `m = 1`, `lam = 1`, `ε = 0`.) This shows that the
hypotheses are jointly satisfiable; it does not provide a nontrivial flow. -/
theorem klDecay_of_approxVelocity_hypotheses_stationary (H : Matrix (Fin d) (Fin d) ℝ) (lam ε : ℝ)
    {pStar : (Fin d → ℝ) → ℝ} (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar) :
    let p : ℝ → (Fin d → ℝ) → ℝ := fun _ => pStar
    let g : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ _ => 0
    (∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t) ∧
    (∀ t, 0 ≤ t → TransportKLRegularity p pStar g t) ∧
    (∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)) ∧
    (∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH H (g t x - idealVelocity H (score (p t)) (score pStar) x) * p t x)) ∧
    (∀ t, 0 ≤ t →
      ∫ x, sqNormH H (g t x - idealVelocity H (score (p t)) (score pStar) x) * p t x ≤
        ε * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar) := by
  intro p g
  have hv : ∀ x, idealVelocity H (score pStar) (score pStar) x = 0 := fun x => by
    simp [idealVelocity]
  refine ⟨fun t x => ?_, fun t _ => stationary_transportKLRegularity hpStar_pos hpStar t,
    fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun t _ => ?_⟩
  · simp only [p, g, divergence_smul_zero, neg_zero]
    exact hasDerivAt_const t (pStar x)
  · simp [p, sqNormH]
  · simp [p, g, hv, sqNormH]
  · simp [p, g, hv, sqNormH]
  · have hkl : klDivDensity pStar pStar = 0 := by
      rw [klDivDensity]
      have : ∀ x, Real.log (pStar x / pStar x) = 0 := fun x => by
        rw [div_self (hpStar_pos x).ne', Real.log_one]
      simp [this]
    simp [p, hkl, relFisher]

/-- **Nonvacuity of `klDecay_of_idealVelocity`'s hypotheses.** For every matrix `H`, constant `lam`
and every positive differentiable `pStar`, the stationary flow `p_t = pStar` with velocity
`g_t = 0` satisfies the continuity equation, `g_t = v⋆_t` for `t ≥ 0` (here `v⋆_t = 0`),
`TransportKLRegularity`, finite weighted Fisher information and the LSI-along-the-flow
hypothesis of `klDecay_of_idealVelocity` (hence also those of `klDecay_of_idealVelocity_local`, for
any
`δ > 0`). Degenerate instance (`D ≡ 0`): it shows joint satisfiability only. -/
theorem klDecay_of_idealVelocity_hypotheses_stationary (H : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ)
    {pStar : (Fin d → ℝ) → ℝ} (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar) :
    let p : ℝ → (Fin d → ℝ) → ℝ := fun _ => pStar
    let g : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ _ => 0
    (∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t) ∧
    (∀ t, 0 ≤ t → g t = idealVelocity H (score (p t)) (score pStar)) ∧
    (∀ t, 0 ≤ t → TransportKLRegularity p pStar g t) ∧
    (∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)) ∧
    LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar) := by
  intro p g
  obtain ⟨hce, hreg, hdiss, -, -, hLSI⟩ :=
    klDecay_of_approxVelocity_hypotheses_stationary H lam 0 hpStar_pos hpStar
  refine ⟨hce, fun t _ => ?_, hreg, hdiss, hLSI⟩
  funext x
  simp [p, g, idealVelocity]

/-- **Nonvacuity of `klDecay_of_approxVelocity_timeDependent`'s hypotheses.** For every family
`H_t`,
constants `lam`, `ε` and every positive differentiable `pStar`, the stationary flow
`p_t = pStar`, `g_t = 0` satisfies the continuity equation, `TransportKLRegularity`, finite
`I_{H_t⁻¹}(t)`, integrable approximation error, [A3] with `H_t` and the LSI-along-the-flow
hypothesis of `klDecay_of_approxVelocity_timeDependent` (and of its `_local` version). The remaining
hypotheses hold e.g. for `H_t = 1`, `m = 1`, `lam = 1`, `ε = 0`. Degenerate (`D ≡ 0`). -/
theorem klDecay_of_approxVelocity_timeDependent_hypotheses_stationary (H : ℝ → Matrix (Fin d) (Fin
    d) ℝ)
    (lam ε : ℝ) {pStar : (Fin d → ℝ) → ℝ} (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar) :
    let p : ℝ → (Fin d → ℝ) → ℝ := fun _ => pStar
    let g : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ _ => 0
    (∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t) ∧
    (∀ t, 0 ≤ t → TransportKLRegularity p pStar g t) ∧
    (∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x)) ∧
    (∀ t, 0 ≤ t → Integrable (fun x =>
      sqNormH (H t) (g t x - idealVelocity (H t) (score (p t)) (score pStar) x) * p t x)) ∧
    (∀ t, 0 ≤ t →
      ∫ x, sqNormH (H t) (g t x - idealVelocity (H t) (score (p t)) (score pStar) x) * p t x ≤
        ε * ∫ x, sqNormH (H t)⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar) := by
  intro p g
  have h := fun t => klDecay_of_approxVelocity_hypotheses_stationary (H t) lam ε hpStar_pos hpStar
  exact ⟨(h 0).1, (h 0).2.1, fun t ht => (h t).2.2.1 t ht, fun t ht => (h t).2.2.2.1 t ht,
    fun t ht => (h t).2.2.2.2.1 t ht, (h 0).2.2.2.2.2⟩

/-- **Nonvacuity of `klDecay_of_steinMinimiser`'s hypotheses.** For every matrix `H`, all
constants `lam`, `ε` and every positive differentiable `pStar`, the stationary flow
`p_t = pStar`, `g_t = 0`, with the class `F t = {0}`, satisfies the continuity equation,
`TransportKLRegularity`, finite weighted Fisher information, admissibility of `F t`, closure
under negation, `g_t ∈ F t`, minimality of `g_t` over `F t`, the paper-form [A3] (witness
`f = 0`) and the LSI-along-the-flow hypothesis of `klDecay_of_steinMinimiser` (and of its
`_local` version). Degenerate (`D ≡ 0`). -/
theorem klDecay_of_steinMinimiser_hypotheses_stationary (H : Matrix (Fin d) (Fin d) ℝ)
    (lam ε : ℝ) {pStar : (Fin d → ℝ) → ℝ} (hpStar_pos : ∀ x, 0 < pStar x)
    (hpStar : Differentiable ℝ pStar) :
    let p : ℝ → (Fin d → ℝ) → ℝ := fun _ => pStar
    let g : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ _ => 0
    let F : ℝ → Set ((Fin d → ℝ) → Fin d → ℝ) := fun _ => {0}
    (∀ t x, HasDerivAt (fun s => p s x) (-(divergence (fun y => p t y • g t y) x)) t) ∧
    (∀ t, 0 ≤ t → TransportKLRegularity p pStar g t) ∧
    (∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x)) ∧
    (∀ t, 0 ≤ t → ∀ f ∈ F t, Admissible H (p t) (score pStar) f) ∧
    (∀ t, 0 ≤ t → ∀ f ∈ F t, -f ∈ F t) ∧
    (∀ t, 0 ≤ t → g t ∈ F t) ∧
    (∀ t, 0 ≤ t → IsMinOn (steinObjective H (p t) (score pStar)) (F t) (g t)) ∧
    (∀ t, 0 ≤ t → ∃ f ∈ F t,
      ∫ x, sqNormH H (f x - H⁻¹ *ᵥ (score (p t) x - score pStar x)) * p t x ≤
        ε * ∫ x, sqNormH H⁻¹ (score (p t) x - score pStar x) * p t x) ∧
    LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar) := by
  intro p g F
  obtain ⟨hce, hreg, hdiss, -, -, hLSI⟩ :=
    klDecay_of_approxVelocity_hypotheses_stationary H lam ε hpStar_pos hpStar
  have hg0 : ∀ t, g t = 0 := fun t => rfl
  refine ⟨hce, hreg, hdiss, fun t _ f hf => ?_, fun t _ f hf => ?_, fun t _ => ?_,
    fun t _ => ?_, fun t _ => ?_, hLSI⟩
  · rw [Set.mem_singleton_iff.1 hf]
    exact SteinObjective.admissible_zero H _ _
  · rw [Set.mem_singleton_iff.1 hf, neg_zero]
    exact Set.mem_singleton _
  · rw [hg0 t]
    exact Set.mem_singleton _
  · rw [hg0 t]
    exact isMinOn_iff.2 fun f hf =>
      le_of_eq (congrArg (steinObjective H (p t) (score pStar)) (Set.mem_singleton_iff.1 hf).symm)
  · refine ⟨0, Set.mem_singleton _, ?_⟩
    simp [p, sqNormH]

end KLDissipation
end FormalizeSampling
