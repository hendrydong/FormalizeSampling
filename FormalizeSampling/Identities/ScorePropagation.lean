module

public import FormalizeSampling.Identities.Tweedie
public import FormalizeSampling.Kernels.GaussianKernels
public import FormalizeSampling.Identities.OUPosteriorScore

/-!
# Score propagation through a Gaussian channel (1D; companion of RS-DMC's Tweedie identity)

Registry ID: **SE-3** (score propagation through Gaussian channels). This is structural input
only for recursive score estimation: the error theorem for nested estimators is *not* proved
here. Source: **RS-DMC** (Huang, Zou, Dong, Ma, Zhang, COLT 2024, arXiv 2401.06325v1).

## Setting and conventions

* The prior is a Lebesgue density `q : ℝ → ℝ`; its regularity is packaged in the explicit
  hypothesis structure `RegularPrior q`: `q ≥ 0`, `q` differentiable on `ℝ`, `q` and `q'`
  Lebesgue integrable, and `∫ q > 0`. Normalisation `∫ q = 1` is **not** needed for the
  analytic identities (scores are scale invariant); it is assumed (or derived from
  `P.map X = priorMeasure q`) only where a law is identified. `RegularPrior.of_pos` covers the
  everywhere-positive case `q > 0`, and `regularPrior_gaussKernel` (every Gaussian density)
  shows the hypotheses are satisfiable.
* The channel is `Y = aX + σZ` with `a ≠ 0`, `σ ≠ 0`, `Z ~ N(0, 1)` independent of `X`. The
  Gaussian kernel is `Tweedie.gaussKernel σ m y`, the density at `y` of `N(m, σ²)` (Mathlib's
  `gaussianReal` / `gaussianPDFReal` take the **variance** `σ ^ 2`).
* `channelDensity q a σ y = ∫ q(x) gaussKernel σ (a x) y dx` is the density `p_Y` of `Y`
  (`map_channel_eq_priorMeasure`, `bind_gaussianReal_priorMeasure`).
* `posteriorExpect q a σ f y = (∫ f(x) q(x) gaussKernel σ (a x) y dx) / p_Y(y)` is the mean of
  `f` under the posterior `q(x | y) ∝ q(x) gaussKernel σ (a x) y`; `condExp_eq_posteriorExpect`
  proves that `posteriorExpect q a σ f ∘ Y` is a version of `E[f(X) | σ(Y)]` (an `=ᵐ`
  statement; no regular conditional distribution is chosen).
* Scores are state scores `score1 p = (log p)'` (`FormalizeSampling.score1`).
* Junk values: every Bochner integral appearing in a conclusion is of an integrable function
  under the stated hypotheses, and `p_Y > 0` everywhere (`channelDensity_pos`), so no division
  by `0` occurs. Where `q x = 0`, `score1 q x * q x = q'(x) = 0` still holds
  (`score1_mul_self`: a zero of a nonnegative differentiable function is a minimum).
* OU time gaps: `ouDensity p τ` is meaningful only for `τ > 0`. For `τ ≤ 0`,
  `1 - e^{-2τ} ≤ 0`, so `ouStd τ = √(1 - e^{-2τ}) = 0` and the kernel `gaussKernel 0 …` is
  identically `0` (Mathlib's convention for variance `0`); hence `ouDensity p τ` is identically
  `0`, a junk value that is the density of nothing. Every OU theorem below therefore assumes
  `s < t` (time gap `τ = t - s > 0`; `bind_ouKernel_priorMeasure` assumes `τ > 0` directly).

## Main results

* (a) **Score propagation** `score1_channelDensity`, `score1_channelDensity_eq_posteriorExpect`
  (a Stein-type companion of Tweedie's formula, see "Paper statement mapped"):
  `(log p_Y)'(y) = (1/a) (∫ (log q)'(x) q(x) gaussKernel σ (a x) y dx) / p_Y(y)`, i.e.
  `∇ log p_Y(y) = a⁻¹ E[∇ log q(X) | Y = y]`. Proof: differentiation under the integral with
  the constant domination of `Tweedie` (`hasDerivAt_channelDensity`), then integration by parts
  in `x` (`∂_y g(y - a x) = -(1/a) ∂_x g(y - a x)`), the boundary terms vanishing because `q`
  and `q'` are integrable and the kernel is bounded
  (`integral_mul_sub_div_mul_gaussKernel_eq`, via Mathlib's
  `integral_mul_deriv_eq_deriv_mul_of_integrable`).
* (b) **Consistency with Tweedie** `score1_channelDensity_tweedie`,
  `stein_posteriorExpect`: `(log p_Y)'(y) = (a E[X | Y = y] - y) / σ²`, hence the posterior
  Stein identity `a E[X | Y = y] - y = σ² a⁻¹ E[∇ log q(X) | Y = y]`. The Tweedie form needs
  only `q ≥ 0`, `q ∈ L¹`, `∫ q > 0` (no differentiability of `q`). For a normalised prior,
  `channelDensity_eq_smoothedDensity`, `posteriorMean_map_priorMeasure`,
  `score1_channelDensity_eq_tweedie` and `tweedie_eq_score_propagation` identify `p_Y` and the
  posterior mean with `Tweedie.smoothedDensity` / `Tweedie.posteriorMean` of the law of `aX`
  and reuse `Tweedie.tweedie`.
* (c) **OU specialisation** (`a = e^{-(t-s)}`, `σ² = 1 - e^{-2(t-s)}`, `s < t`, rate 1):
  `bind_ouKernel_priorMeasure` (the OU transition of the law with density `p_s` has density
  `ouDensity p_s (t - s)`), `score1_ouDensity`:
  `∇ log p_t(y) = e^{t-s} E[∇ log p_s(X_s) | X_t = y]`, `score1_ouDensity_tweedie` and
  `ou_stein_posteriorExpect`.
* Random-variable forms: `condExp_eq_posteriorExpect`, `score1_channelDensity_condExp`
  (`(log p_Y)'(Y) = a⁻¹ E[(log q)'(X) | σ(Y)]` a.s.), `stein_condExp`, `map_ou_eq_priorMeasure`,
  `score1_ouDensity_condExp` (`∇ log p_t(X_t) = e^{t-s} E[∇ log p_s(X_s) | σ(X_t)]` a.s.).

## Paper statement mapped

RS-DMC, arXiv v1 Lemma 2.1 (PMLR Lemma 1) and Lemma E.1 (PMLR Lemma 14), the **OU Tweedie
identity**: for the forward OU process `dx = -x dt + √2 dB` and a time gap `τ = S - t ∈ (0, S]`,
`∇ log p_{k,τ}(x) = E_{x' ∼ q_{k,τ}(·|x)}[-(x - e^{-τ} x') / (1 - e^{-2τ})]` with posterior
`q_{k,τ}(x'|x) ∝ p_{k,0}(x') exp(-|x - e^{-τ} x'|² / (2(1 - e^{-2τ})))`. In one dimension,
with `p_s = p_{k,0}` and `t - s = τ`, this is `score1_ouDensity_tweedie` (the posterior
`q_{k,τ}` is the one used in `posteriorExpect`). Here `s < t`
(`τ > 0`) is assumed, since the formula divides by `1 - e^{-2τ}`.

RS-DMC estimates scores through this Tweedie identity, not through score propagation. Its
Algorithm 1 (`RSE`) returns the empirical Tweedie (posterior-mean) estimate
`(1/n) Σᵢ -(x - e^{-τ} x'ᵢ)/(1 - e^{-2τ})`, where the `x'ᵢ` are the final iterates of `n` inner
ULA chains targeting the posterior `q_{k,τ}(· | x)`; the drift of those chains uses the earlier
score `∇ log p_{k,0}`, itself replaced by a recursive (nested) call of `RSE`. The
score-propagation form `∇ log p_{k,τ}(x) = e^{τ} E_{q_{k,τ}(·|x)}[∇ log p_{k,0}(x')]`
(`score1_ouDensity`) is not stated in the paper and is not the recursion that `RSE`
estimates: it is a related exact identity, a Stein-type companion of the Tweedie identity,
equivalent to it by the posterior Stein identity (b) (`ou_stein_posteriorExpect`). It expresses
the later score as a posterior average of the earlier score; Algorithm 1 does not form that
average.

## Not proved here

* Only dimension one; the `d`-dimensional (isotropic or matrix) version is not formalised.
* The OU transition is the Gaussian kernel `OU.ouKernel 1 τ` taken as a definition; no SDE is
  formalised, and only one transition `s → t` is treated (no segment re-indexing).
* **Nested estimators remain research**: nothing is proved about the error of nested /
  recursive Monte Carlo estimators of these conditional expectations (dependent inner samples,
  changing posterior targets, inexact inner ULA, failure probabilities).
  Only the exact identity is proved.
* No uniform-in-`y` or Lipschitz bounds on the scores (paper assumption [A1]) are derived.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.ScorePropagation

open FormalizeSampling.Tweedie

/-! ### Definitions -/

/-- Regularity hypotheses on a prior density `q : ℝ → ℝ` used in most of this file:
`q ≥ 0`, `q` is differentiable on `ℝ`, `q` and its derivative `q' = deriv q` are Lebesgue
integrable, and `∫ q > 0` (so `q` is not a.e. zero). Normalisation `∫ q = 1` is not required.
These are explicit regularity assumptions; they hold for every Gaussian density
(`regularPrior_gaussKernel`). -/
structure RegularPrior (q : ℝ → ℝ) : Prop where
  /-- `q` is nonnegative. -/
  nonneg : ∀ x, 0 ≤ q x
  /-- `q` is differentiable everywhere. -/
  differentiable : Differentiable ℝ q
  /-- `q` is Lebesgue integrable. -/
  integrable : Integrable q
  /-- The derivative `q'` is Lebesgue integrable. -/
  integrable_deriv : Integrable (deriv q)
  /-- `q` has positive total mass. -/
  integral_pos : 0 < ∫ x, q x

/-- The density of the channel output `Y = aX + σZ` for a prior density `q`:
`p_Y(y) = ∫ q(x) gaussKernel σ (a x) y dx`, where `gaussKernel σ m y` is the `N(m, σ²)` density
at `y`. It is the Lebesgue density of `Law(Y)` when `q` is a probability density, `X ∼ q` is
independent of `Z ∼ N(0, 1)` and `σ ≠ 0` (`map_channel_eq_priorMeasure`). -/
noncomputable def channelDensity (q : ℝ → ℝ) (a σ y : ℝ) : ℝ :=
  ∫ x, q x * gaussKernel σ (a * x) y

/-- The posterior expectation `E[f(X) | Y = y] = (∫ f(x) q(x) gaussKernel σ (a x) y dx) / p_Y(y)`
of `f` under the posterior density `q(x | y) ∝ q(x) gaussKernel σ (a x) y` of the channel
`Y = aX + σZ`. It is a version of the conditional expectation `E[f(X) | σ(Y)]`
(`condExp_eq_posteriorExpect`). -/
noncomputable def posteriorExpect (q : ℝ → ℝ) (a σ : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ x, f x * q x * gaussKernel σ (a * x) y) / channelDensity q a σ y

/-- The measure `q(x) dx` on `ℝ` with Lebesgue density `q` (as `volume.withDensity`; negative
values of `q` would be truncated to `0`, but all results assume `q ≥ 0`). It is a probability
measure when `∫ q = 1` (`isProbabilityMeasure_priorMeasure`). -/
noncomputable def priorMeasure (q : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (q x)

/-! ### The Gaussian kernel as a function of the prior variable -/

/-- Symmetry of the Gaussian kernel: `gaussKernel σ x y = gaussKernel σ y x`. -/
lemma gaussKernel_comm (σ x y : ℝ) : gaussKernel σ x y = gaussKernel σ y x := by
  rw [gaussKernel_eq, gaussKernel_eq]
  congr 3
  ring

/-- Derivative in the prior variable: for `σ ≠ 0`,
`∂_x gaussKernel σ (a x) y = a ((y - a x) / σ²) gaussKernel σ (a x) y`. Compared with
`Tweedie.hasDerivAt_gaussKernel` (the `y`-derivative `((a x - y)/σ²) gaussKernel`), this is the
relation `∂_y = -(1/a) ∂_x` used in the integration by parts. -/
lemma hasDerivAt_gaussKernel_mean {σ : ℝ} (hσ : σ ≠ 0) (a x y : ℝ) :
    HasDerivAt (fun x => gaussKernel σ (a * x) y)
      (a * ((y - a * x) / σ ^ 2) * gaussKernel σ (a * x) y) x := by
  have h1 := hasDerivAt_gaussKernel hσ y (a * x)
  have h2 : HasDerivAt (fun x : ℝ => a * x) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have h := h1.comp x h2
  simp_rw [gaussKernel_comm σ _ y]
  convert h using 1
  · rfl
  · ring

/-- Continuity of `x ↦ gaussKernel σ (a x) y`. -/
lemma continuous_gaussKernel_mul_left (σ a y : ℝ) :
    Continuous (fun x => gaussKernel σ (a * x) y) :=
  (continuous_gaussKernel_left σ y).comp (continuous_const.mul continuous_id)

/-- Bounded continuous multipliers preserve Lebesgue integrability (real-valued form). -/
private lemma integrable_mul_of_bdd {f g : ℝ → ℝ} (hf : Integrable f) (hg : Continuous g)
    (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable (fun x => f x * g x) := by
  have := hf.bdd_mul hg.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [mul_comm] using this

/-- For Lebesgue-integrable `f`, `x ↦ f(x) gaussKernel σ (a x) y` is Lebesgue integrable
(the kernel is bounded by `(√(2πσ²))⁻¹`); no assumption on `a` or `σ` is needed. -/
theorem integrable_mul_gaussKernel_mul {f : ℝ → ℝ} (hf : Integrable f) (σ a y : ℝ) :
    Integrable (fun x => f x * gaussKernel σ (a * x) y) :=
  integrable_mul_of_bdd hf (continuous_gaussKernel_mul_left σ a y) _ fun x => by
    rw [abs_of_nonneg (gaussKernel_nonneg _ _ _)]; exact gaussKernel_le σ _ y

/-- Uniform bound on the kernel score: for `σ ≠ 0` and all `m, y`,
`|((m - y)/σ²) gaussKernel σ m y| ≤ (2σ² + 1) (√(2πσ²))⁻¹ / σ²`. -/
lemma abs_sub_div_mul_gaussKernel_le {σ : ℝ} (hσ : σ ≠ 0) (m y : ℝ) :
    |(m - y) / σ ^ 2 * gaussKernel σ m y| ≤
      (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ / σ ^ 2 := by
  rw [abs_mul, abs_of_nonneg (gaussKernel_nonneg _ _ _), abs_div,
    div_mul_eq_mul_div, abs_of_nonneg (sq_nonneg σ)]
  exact div_le_div_of_nonneg_right (abs_sub_mul_gaussKernel_le hσ m y) (sq_nonneg σ)

/-- For Lebesgue-integrable `q`, `a ≠ 0` and `σ ≠ 0`, `x ↦ x q(x) gaussKernel σ (a x) y` is
Lebesgue integrable (no moment assumption on `q`: `|x| gaussKernel σ (a x) y` is bounded in
`x` by `(|y| + 2σ² + 1)(√(2πσ²))⁻¹ / |a|`). -/
theorem integrable_mul_mul_gaussKernel {q : ℝ → ℝ} (hq : Integrable q) {a σ : ℝ} (ha : a ≠ 0)
    (hσ : σ ≠ 0) (y : ℝ) : Integrable (fun x => x * q x * gaussKernel σ (a * x) y) := by
  have h := integrable_mul_of_bdd (g := fun x => x * gaussKernel σ (a * x) y) hq
    (continuous_id.mul (continuous_gaussKernel_mul_left σ a y))
    ((|y| + 2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ / |a|) fun x => ?_
  · refine h.congr (ae_of_all _ fun x => ?_)
    simp only
    ring
  · have hb := abs_mul_gaussKernel_le hσ (a * x) y
    have ha' : 0 < |a| := abs_pos.mpr ha
    rw [le_div_iff₀ ha', abs_mul, abs_of_nonneg (gaussKernel_nonneg _ _ _)]
    rw [abs_mul] at hb
    nlinarith [abs_nonneg x, gaussKernel_nonneg σ (a * x) y]

/-! ### Positivity, regularity and the score of the prior -/

/-- Where `q ≥ 0` is differentiable, `(log q)'(x) q(x) = q'(x)` at **every** `x`: for
`q x > 0` this is `score1_of_pos`; for `q x = 0` both sides vanish (`x` is a minimum of `q`,
so `q'(x) = 0`). -/
lemma score1_mul_self {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hd : Differentiable ℝ q) (x : ℝ) :
    score1 q x * q x = deriv q x := by
  rcases (hnn x).lt_or_eq with hpos | hzero
  · rw [score1_of_pos (hd x) hpos]
    field_simp
  · have hmin : IsLocalMin q x := Filter.Eventually.of_forall fun y => by
      rw [← hzero]; exact hnn y
    rw [← hzero, mul_zero, hmin.deriv_eq_zero]

/-- A positive, differentiable density with integrable `q` and `q'` satisfies `RegularPrior`
(the setting `q > 0` of the specification); `∫ q > 0` is automatic. -/
theorem RegularPrior.of_pos {q : ℝ → ℝ} (hpos : ∀ x, 0 < q x) (hd : Differentiable ℝ q)
    (hq : Integrable q) (hq' : Integrable (deriv q)) : RegularPrior q where
  nonneg x := (hpos x).le
  differentiable := hd
  integrable := hq
  integrable_deriv := hq'
  integral_pos := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hq]
    have : Function.support q = Set.univ :=
      Set.eq_univ_of_forall fun x => (hpos x).ne'
    rw [this, Real.volume_univ]
    exact ENNReal.zero_lt_top

/-- The channel density is nonnegative when `q ≥ 0`. -/
theorem channelDensity_nonneg {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (a σ y : ℝ) :
    0 ≤ channelDensity q a σ y :=
  integral_nonneg fun x => mul_nonneg (hnn x) (gaussKernel_nonneg _ _ _)

/-- Strict positivity of `p_Y` under explicit hypotheses: if `q ≥ 0` is integrable with
`∫ q > 0` and `σ ≠ 0`, then `p_Y(y) > 0` for every `a` and `y` (the kernel is strictly
positive). -/
theorem channelDensity_pos_of {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hint : Integrable q)
    (hpos : 0 < ∫ x, q x) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    0 < channelDensity q a σ y := by
  rw [integral_pos_iff_support_of_nonneg hnn hint] at hpos
  unfold channelDensity
  rw [integral_pos_iff_support_of_nonneg
    (fun x => mul_nonneg (hnn x) (gaussKernel_nonneg _ _ _))
    (integrable_mul_gaussKernel_mul hint σ a y)]
  have hsupp : Function.support (fun x => q x * gaussKernel σ (a * x) y) =
      Function.support q := by
    ext x
    simp [(gaussKernel_pos hσ (a * x) y).ne']
  rw [hsupp]
  exact hpos

/-- For a `RegularPrior q` and `σ ≠ 0`, the channel density is strictly positive everywhere. -/
theorem channelDensity_pos {q : ℝ → ℝ} (hq : RegularPrior q) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (y : ℝ) : 0 < channelDensity q a σ y :=
  channelDensity_pos_of hq.nonneg hq.integrable hq.integral_pos a hσ y

/-! ### Differentiation under the integral sign and integration by parts -/

/-- Differentiation under the integral sign: for Lebesgue-integrable `q` and `σ ≠ 0`,
`p_Y'(y) = ∫ q(x) ((a x - y)/σ²) gaussKernel σ (a x) y dx`, for every `a`. Dominating function
`|q(x)| (2σ² + 1)(√(2πσ²))⁻¹ / σ²` (constant domination as in `Tweedie`). -/
theorem hasDerivAt_channelDensity {q : ℝ → ℝ} (hq : Integrable q) {σ : ℝ} (hσ : σ ≠ 0)
    (a y : ℝ) :
    HasDerivAt (channelDensity q a σ)
      (∫ x, q x * ((a * x - y) / σ ^ 2 * gaussKernel σ (a * x) y)) y := by
  set C := (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ / σ ^ 2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y x => q x * gaussKernel σ (a * x) y)
    (F' := fun y x => q x * ((a * x - y) / σ ^ 2 * gaussKernel σ (a * x) y))
    (x₀ := y) (bound := fun x => |q x| * C) Filter.univ_mem
    (Eventually.of_forall fun y' =>
      (integrable_mul_gaussKernel_mul hq σ a y').aestronglyMeasurable)
    (integrable_mul_gaussKernel_mul hq σ a y)
    (hq.1.mul (((continuous_const.mul continuous_id).sub continuous_const).div_const _ |>.mul
      (continuous_gaussKernel_mul_left σ a y)).aestronglyMeasurable)
    (ae_of_all _ fun x y' _ => ?_) (hq.abs.mul_const C)
    (ae_of_all _ fun x y' _ => (hasDerivAt_gaussKernel hσ (a * x) y').const_mul (q x))
  · exact key.2
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub_div_mul_gaussKernel_le hσ _ _) (abs_nonneg _)

/-- For Lebesgue-integrable `q` and `σ ≠ 0`, the channel density is continuous. -/
theorem continuous_channelDensity {q : ℝ → ℝ} (hint : Integrable q) (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) : Continuous (channelDensity q a σ) := by
  have hd : Differentiable ℝ (channelDensity q a σ) :=
    fun y => (hasDerivAt_channelDensity hint hσ a y).differentiableAt
  exact hd.continuous

/-- **Integration by parts in the prior variable.** If `q` is differentiable with `q` and `q'`
Lebesgue integrable, `a ≠ 0` and `σ ≠ 0`, then
`∫ q(x) ((a x - y)/σ²) gaussKernel σ (a x) y dx = a⁻¹ ∫ q'(x) gaussKernel σ (a x) y dx`.
Proof: `((a x - y)/σ²) g = -(1/a) ∂_x g` for `g = gaussKernel σ (a x) y`, and Mathlib's
`integral_mul_deriv_eq_deriv_mul_of_integrable` (boundary terms vanish because `q g`, `q' g`
and `q ∂_x g` are integrable: the kernel and its `x`-derivative are bounded). -/
theorem integral_mul_sub_div_mul_gaussKernel_eq {q : ℝ → ℝ} (hd : Differentiable ℝ q)
    (hq : Integrable q) (hq' : Integrable (deriv q)) {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0)
    (y : ℝ) :
    ∫ x, q x * ((a * x - y) / σ ^ 2 * gaussKernel σ (a * x) y) =
      a⁻¹ * ∫ x, deriv q x * gaussKernel σ (a * x) y := by
  set C := (2 * σ ^ 2 + 1) * (√(2 * π * σ ^ 2))⁻¹ / σ ^ 2
  have hv'int : Integrable
      (fun x => q x * (a * ((y - a * x) / σ ^ 2) * gaussKernel σ (a * x) y)) := by
    refine integrable_mul_of_bdd hq ((continuous_const.mul ((continuous_const.sub
      (continuous_const.mul continuous_id)).div_const _)).mul
      (continuous_gaussKernel_mul_left σ a y)) (|a| * C) fun x => ?_
    rw [mul_assoc, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    rw [gaussKernel_comm σ (a * x) y]
    exact abs_sub_div_mul_gaussKernel_le hσ y (a * x)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := q) (u' := deriv q)
    (v := fun x => gaussKernel σ (a * x) y)
    (v' := fun x => a * ((y - a * x) / σ ^ 2) * gaussKernel σ (a * x) y)
    (fun x _ => (hd x).hasDerivAt) (fun x _ => hasDerivAt_gaussKernel_mean hσ a x y)
    hv'int (integrable_mul_gaussKernel_mul hq' σ a y) (integrable_mul_gaussKernel_mul hq σ a y)
  have hpt : (fun x => q x * ((a * x - y) / σ ^ 2 * gaussKernel σ (a * x) y)) =
      fun x => -a⁻¹ * (q x * (a * ((y - a * x) / σ ^ 2) * gaussKernel σ (a * x) y)) := by
    ext x
    field_simp
    ring
  rw [hpt, integral_const_mul, hibp]
  ring

/-- For a `RegularPrior q`, `a ≠ 0`, `σ ≠ 0`:
`p_Y'(y) = a⁻¹ ∫ q'(x) gaussKernel σ (a x) y dx` (derivative of the smoothed density as the
smoothed derivative of the prior, rescaled). -/
theorem hasDerivAt_channelDensity_eq {q : ℝ → ℝ} (hq : RegularPrior q) {a σ : ℝ} (ha : a ≠ 0)
    (hσ : σ ≠ 0) (y : ℝ) :
    HasDerivAt (channelDensity q a σ) (a⁻¹ * ∫ x, deriv q x * gaussKernel σ (a * x) y) y := by
  have h := hasDerivAt_channelDensity hq.integrable hσ a y
  rwa [integral_mul_sub_div_mul_gaussKernel_eq hq.differentiable hq.integrable
    hq.integrable_deriv ha hσ y] at h

/-! ### (a) Score propagation -/

/-- (a) **Score propagation** (1D; a Stein-type companion of the Tweedie identity whose
empirical version RS-DMC uses, see the module doc). For a prior density `q` satisfying
`RegularPrior q` (`q ≥ 0` differentiable, `q`, `q'` integrable, `∫ q > 0`), `a ≠ 0` and
`σ ≠ 0`, the score of the channel density `p_Y = q ∗ N(a ·, σ²)` is, at every `y`,
`(log p_Y)'(y) = (1/a) (∫ (log q)'(x) q(x) gaussKernel σ (a x) y dx) / p_Y(y)`,
i.e. `∇ log p_Y(y) = a⁻¹ E[∇ log q(X) | Y = y]` for `Y = aX + σZ`. -/
theorem score1_channelDensity {q : ℝ → ℝ} (hq : RegularPrior q) {a σ : ℝ} (ha : a ≠ 0)
    (hσ : σ ≠ 0) (y : ℝ) :
    score1 (channelDensity q a σ) y =
      (1 / a) * (∫ x, score1 q x * q x * gaussKernel σ (a * x) y) / channelDensity q a σ y := by
  have hd := hasDerivAt_channelDensity_eq hq ha hσ y
  rw [score1_of_pos hd.differentiableAt (channelDensity_pos hq a hσ y), hd.deriv]
  simp_rw [score1_mul_self hq.nonneg hq.differentiable, one_div]

/-- (a) **Score propagation, posterior form.** Under `RegularPrior q`, `a ≠ 0`, `σ ≠ 0`:
`(log p_Y)'(y) = a⁻¹ · posteriorExpect q a σ (log q)' y`, i.e.
`∇ log p_Y(y) = a⁻¹ E[∇ log q(X) | Y = y]` with the posterior `q(x | y)`. -/
theorem score1_channelDensity_eq_posteriorExpect {q : ℝ → ℝ} (hq : RegularPrior q) {a σ : ℝ}
    (ha : a ≠ 0) (hσ : σ ≠ 0) (y : ℝ) :
    score1 (channelDensity q a σ) y = a⁻¹ * posteriorExpect q a σ (score1 q) y := by
  rw [score1_channelDensity hq ha hσ y, posteriorExpect, one_div, mul_div_assoc]

/-! ### (b) Consistency with Tweedie's formula: a posterior Stein identity -/

/-- Algebraic rewriting of the derivative integral: for integrable `q`, `a ≠ 0`, `σ ≠ 0`,
`∫ q(x)((a x - y)/σ²) g dx = (a ∫ x q(x) g dx - y p_Y(y)) / σ²`, `g = gaussKernel σ (a x) y`. -/
theorem integral_mul_sub_div_mul_gaussKernel_eq_posteriorMean {q : ℝ → ℝ} (hq : Integrable q)
    {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) (y : ℝ) :
    ∫ x, q x * ((a * x - y) / σ ^ 2 * gaussKernel σ (a * x) y) =
      (a * (∫ x, x * q x * gaussKernel σ (a * x) y) - y * channelDensity q a σ y) / σ ^ 2 := by
  unfold channelDensity
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
    ((integrable_mul_mul_gaussKernel hq ha hσ y).const_mul a)
    ((integrable_mul_gaussKernel_mul hq σ a y).const_mul y), ← integral_div]
  congr 1
  ext x
  ring

/-- (b) **Tweedie form** for the channel `Y = aX + σZ`: for a prior density `q ≥ 0`, Lebesgue
integrable with `∫ q > 0` (not necessarily differentiable, no moment assumption), `a ≠ 0` and
`σ ≠ 0`, `(log p_Y)'(y) = (a E[X | Y = y] - y) / σ²` with `E[X | Y = y]` the posterior mean
`posteriorExpect q a σ id y`. These are the fields `nonneg`, `integrable` and `integral_pos`
of `RegularPrior q`. -/
theorem score1_channelDensity_tweedie {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hint : Integrable q)
    (hpos : 0 < ∫ x, q x) {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) (y : ℝ) :
    score1 (channelDensity q a σ) y = (a * posteriorExpect q a σ (fun x => x) y - y) / σ ^ 2 := by
  have hd := hasDerivAt_channelDensity hint hσ a y
  have hp := channelDensity_pos_of hnn hint hpos a hσ y
  rw [score1_of_pos hd.differentiableAt hp, hd.deriv,
    integral_mul_sub_div_mul_gaussKernel_eq_posteriorMean hint ha hσ y, posteriorExpect]
  field_simp

/-- (b) **Posterior Stein identity.** Under `RegularPrior q`, `a ≠ 0`, `σ ≠ 0`, the Tweedie
form and the score-propagation form give the same score, hence for every `y`:
`a E[X | Y = y] - y = σ² a⁻¹ E[∇ log q(X) | Y = y]` (posterior expectations under
`q(x | y) ∝ q(x) gaussKernel σ (a x) y`). Equivalently
`E[∇ log q(X) + a(y - aX)/σ² | Y = y] = 0`: the posterior score has posterior mean zero. -/
theorem stein_posteriorExpect {q : ℝ → ℝ} (hq : RegularPrior q) {a σ : ℝ} (ha : a ≠ 0)
    (hσ : σ ≠ 0) (y : ℝ) :
    a * posteriorExpect q a σ (fun x => x) y - y =
      σ ^ 2 * (a⁻¹ * posteriorExpect q a σ (score1 q) y) := by
  rw [← score1_channelDensity_eq_posteriorExpect hq ha hσ y,
    score1_channelDensity_tweedie hq.nonneg hq.integrable hq.integral_pos ha hσ y]
  field_simp

/-! ### Link with `Identities/Tweedie.lean` and law identification -/

/-- Integrals against `priorMeasure q` are Lebesgue integrals weighted by `q`:
`∫ g d(q dx) = ∫ q(x) g(x) dx`, for `q ≥ 0` a.e.-measurable and any `g` (Bochner convention on
both sides; no integrability needed). -/
theorem integral_priorMeasure {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hq : AEMeasurable q)
    (g : ℝ → ℝ) : ∫ x, g x ∂priorMeasure q = ∫ x, q x * g x := by
  rw [priorMeasure, integral_withDensity_eq_integral_toReal_smul₀ hq.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]

/-- Integrability against `priorMeasure q`: for `q ≥ 0` a.e.-measurable,
`g ∈ L¹(q dx) ↔ q g ∈ L¹(dx)`. -/
theorem integrable_priorMeasure_iff {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hq : AEMeasurable q)
    {g : ℝ → ℝ} : Integrable g (priorMeasure q) ↔ Integrable (fun x => q x * g x) := by
  rw [priorMeasure, integrable_withDensity_iff_integrable_smul₀' hq.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn _)]

/-- If `q ≥ 0` is integrable with `∫ q = 1`, then `priorMeasure q` is a probability measure. -/
theorem isProbabilityMeasure_priorMeasure {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x)
    (hq : Integrable q) (h1 : ∫ x, q x = 1) : IsProbabilityMeasure (priorMeasure q) :=
  ⟨by rw [priorMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hq (ae_of_all _ hnn), h1, ENNReal.ofReal_one]⟩

/-- Change of variables for the law of `aX`: for `q ≥ 0` a.e.-measurable and `g`
a.e.-strongly measurable for the image measure,
`∫ g d((q dx) ∘ (a ·)⁻¹) = ∫ q(x) g(a x) dx`. -/
theorem integral_map_priorMeasure {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hq : AEMeasurable q)
    (a : ℝ) {g : ℝ → ℝ} (hg : AEStronglyMeasurable g ((priorMeasure q).map (fun x => a * x))) :
    ∫ z, g z ∂(priorMeasure q).map (fun x => a * x) = ∫ x, q x * g (a * x) := by
  rw [integral_map (measurable_const_mul a).aemeasurable hg, integral_priorMeasure hnn hq]

/-- The channel density is `Tweedie.smoothedDensity` of the law of `aX`: for `q ≥ 0`
a.e.-measurable and all `a, σ`, `channelDensity q a σ = smoothedDensity ((q dx) ∘ (a ·)⁻¹) σ`. -/
theorem channelDensity_eq_smoothedDensity {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x)
    (hq : AEMeasurable q) (a σ : ℝ) :
    channelDensity q a σ = smoothedDensity ((priorMeasure q).map (fun x => a * x)) σ := by
  ext y
  rw [smoothedDensity, integral_map_priorMeasure hnn hq a
    (continuous_gaussKernel_left σ y).aestronglyMeasurable, channelDensity]

/-- The `Tweedie.posteriorMean` of `aX` given `Y = aX + σZ` is `a E[X | Y = y]`: for `q ≥ 0`
a.e.-measurable and all `a, σ, y`,
`posteriorMean ((q dx) ∘ (a ·)⁻¹) σ y = a · posteriorExpect q a σ id y`. -/
theorem posteriorMean_map_priorMeasure {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hq : AEMeasurable q)
    (a σ y : ℝ) :
    posteriorMean ((priorMeasure q).map (fun x => a * x)) σ y =
      a * posteriorExpect q a σ (fun x => x) y := by
  rw [posteriorMean, posteriorExpect, ← channelDensity_eq_smoothedDensity hnn hq,
    integral_map_priorMeasure hnn hq a (g := fun z => z * gaussKernel σ z y)
      (continuous_id.mul (continuous_gaussKernel_left σ y)).aestronglyMeasurable,
    mul_div_assoc', ← integral_const_mul]
  congr 2
  ext x
  ring

/-- (b) Tweedie's formula of `Identities/Tweedie.lean` applied to the channel: for a
`RegularPrior q` normalised by `∫ q = 1` and `σ ≠ 0`,
`(log p_Y)'(y) = (posteriorMean μ σ y - y) / σ²` with `μ` the law of `aX`
(this reuses `Tweedie.tweedie`). -/
theorem score1_channelDensity_eq_tweedie {q : ℝ → ℝ} (hq : RegularPrior q)
    (h1 : ∫ x, q x = 1) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    score1 (channelDensity q a σ) y =
      (posteriorMean ((priorMeasure q).map (fun x => a * x)) σ y - y) / σ ^ 2 := by
  have := isProbabilityMeasure_priorMeasure hq.nonneg hq.integrable h1
  have : IsProbabilityMeasure ((priorMeasure q).map (fun x => a * x)) :=
    inferInstance
  rw [channelDensity_eq_smoothedDensity hq.nonneg hq.integrable.1.aemeasurable,
    tweedie _ hσ y]

/-- (b) **Consistency of the two score formulas.** For a `RegularPrior q` with `∫ q = 1`,
`a ≠ 0`, `σ ≠ 0`, Tweedie's formula (from `Identities/Tweedie.lean`, for the law `μ` of `aX`)
and score propagation give the same value:
`(posteriorMean μ σ y - y) / σ² = a⁻¹ E[∇ log q(X) | Y = y]`. -/
theorem tweedie_eq_score_propagation {q : ℝ → ℝ} (hq : RegularPrior q)
    (h1 : ∫ x, q x = 1) {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) (y : ℝ) :
    (posteriorMean ((priorMeasure q).map (fun x => a * x)) σ y - y) / σ ^ 2 =
      a⁻¹ * posteriorExpect q a σ (score1 q) y := by
  rw [← score1_channelDensity_eq_tweedie hq h1 a hσ y,
    score1_channelDensity_eq_posteriorExpect hq ha hσ y]

/-- **Law identification.** If `q ≥ 0` is integrable with `∫ q = 1` and `σ ≠ 0`, mixing
`N(a x, σ²)` over `x ∼ q dx` gives the law with Lebesgue density `channelDensity q a σ`:
`(q dx).bind (x ↦ N(a x, σ²)) = p_Y(y) dy`, for every `a`. -/
theorem bind_gaussianReal_priorMeasure {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x) (hq : Integrable q)
    (h1 : ∫ x, q x = 1) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    (priorMeasure q).bind (fun x => gaussianReal (a * x) ⟨σ ^ 2, sq_nonneg σ⟩) =
      volume.withDensity (fun y => ENNReal.ofReal (channelDensity q a σ y)) := by
  have := isProbabilityMeasure_priorMeasure hnn hq h1
  refine (OU.bind_affineGaussian _ a _).trans ?_
  rw [conv_gaussianReal_eq_withDensity _ hσ,
    channelDensity_eq_smoothedDensity hnn hq.1.aemeasurable]

/-! ### (c) Ornstein–Uhlenbeck specialisation -/

/-- The OU transition standard deviation `√(1 - e^{-2τ})` (rate `1`, as in RS-DMC's forward
process `dx = -x dt + √2 dB`). It is positive for `τ > 0` (`ouStd_pos`); for `τ ≤ 0` it is the
junk value `0` (`Real.sqrt` of a nonpositive number). -/
noncomputable def ouStd (τ : ℝ) : ℝ := √(1 - rexp (-2 * τ))

/-- For `τ ≥ 0`, `ouStd τ ^ 2 = 1 - e^{-2τ}` (the OU transition variance). -/
theorem ouStd_sq {τ : ℝ} (hτ : 0 ≤ τ) : ouStd τ ^ 2 = 1 - rexp (-2 * τ) := by
  rw [ouStd, Real.sq_sqrt]
  rw [sub_nonneg, Real.exp_le_one_iff]
  linarith

/-- For `τ > 0`, `ouStd τ > 0`. -/
theorem ouStd_pos {τ : ℝ} (hτ : 0 < τ) : 0 < ouStd τ := by
  rw [ouStd, Real.sqrt_pos, sub_pos, Real.exp_lt_one_iff]
  linarith

/-- For `τ ≥ 0`, the variance `OU.ouVar 1 τ` of `Kernels/GaussianKernels.lean` is
`ouStd τ ^ 2` (as an element of `ℝ≥0`). -/
theorem ouVar_one_eq {τ : ℝ} (hτ : 0 ≤ τ) :
    OU.ouVar 1 τ = ⟨ouStd τ ^ 2, sq_nonneg _⟩ := by
  ext
  rw [OU.coe_ouVar zero_le_one hτ, mul_one]
  exact (ouStd_sq hτ).symm

/-- The OU-propagated density after a time `τ`:
`ouDensity p τ y = ∫ p(x) N(e^{-τ} x, 1 - e^{-2τ})(y) dx`, i.e. the channel density with
`a = e^{-τ}`, `σ = √(1 - e^{-2τ})`. For a probability density `p = p_s` and `τ = t - s > 0`
it is the density `p_t` of the OU marginal at time `t` (`bind_ouKernel_priorMeasure`,
`map_ou_eq_priorMeasure`). For `τ ≤ 0` it is identically `0` (junk: `ouStd τ = 0` and
`gaussKernel 0` vanishes), so every theorem about it assumes `τ > 0`, i.e. `s < t`. -/
noncomputable def ouDensity (p : ℝ → ℝ) (τ : ℝ) : ℝ → ℝ :=
  channelDensity p (rexp (-τ)) (ouStd τ)

/-- (c) **OU law identification.** If `p ≥ 0` is integrable with `∫ p = 1` and `τ > 0`, one
step of the OU (Mehler) kernel `OU.ouKernel 1 τ x = N(e^{-τ} x, 1 - e^{-2τ})` started from the
law `p(x) dx` has Lebesgue density `ouDensity p τ`. (The OU kernel is a definition; no SDE is
formalised.) -/
theorem bind_ouKernel_priorMeasure {p : ℝ → ℝ} (hnn : ∀ x, 0 ≤ p x) (hp : Integrable p)
    (h1 : ∫ x, p x = 1) {τ : ℝ} (hτ : 0 < τ) :
    (priorMeasure p).bind (OU.ouKernel 1 τ) =
      volume.withDensity (fun y => ENNReal.ofReal (ouDensity p τ y)) := by
  have hk : (⇑(OU.ouKernel 1 τ) : ℝ → Measure ℝ) =
      fun x => gaussianReal (rexp (-τ) * x) ⟨ouStd τ ^ 2, sq_nonneg _⟩ := by
    ext1 x
    rw [OU.ouKernel_apply, ouVar_one_eq hτ.le, neg_one_mul]
  rw [hk, bind_gaussianReal_priorMeasure hnn hp h1 _ (ouStd_pos hτ).ne']
  rfl

/-- (c) **OU score propagation.** For a prior density `p = p_s` with `RegularPrior p` and two
times `s < t`, the score of the OU-propagated density `p_t = ouDensity p (t - s)` is, at
every `y`, `∇ log p_t(y) = e^{t-s} E[∇ log p_s(X_s) | X_t = y]`, the posterior being
`q(x | y) ∝ p_s(x) N(e^{-(t-s)} x, 1 - e^{-2(t-s)})(y)`. This is an exact identity related
to RS-DMC, not the recursion its Algorithm 1 (`RSE`) estimates: `RSE` returns an empirical
Tweedie (posterior-mean) estimate, the form of `score1_ouDensity_tweedie`, nested through
the inner ULA drift; the present form is its Stein-type companion
(`ou_stein_posteriorExpect`). -/
theorem score1_ouDensity {p : ℝ → ℝ} (hp : RegularPrior p) {s t : ℝ} (hst : s < t) (y : ℝ) :
    score1 (ouDensity p (t - s)) y =
      rexp (t - s) * posteriorExpect p (rexp (-(t - s))) (ouStd (t - s)) (score1 p) y := by
  rw [ouDensity, score1_channelDensity_eq_posteriorExpect hp (Real.exp_pos _).ne'
    (ouStd_pos (sub_pos.mpr hst)).ne', Real.exp_neg, inv_inv]

/-- (c) **OU Tweedie form** (RS-DMC Lemma 2.1 / PMLR Lemma 1, in 1D with prior
`p_{k,0} = p` and time gap `τ = t - s > 0`): for a prior density `p ≥ 0`, Lebesgue integrable
with `∫ p > 0` (as in `score1_channelDensity_tweedie`; no differentiability), and `s < t`,
`∇ log p_t(y) = (e^{-(t-s)} E[X_s | X_t = y] - y) / (1 - e^{-2(t-s)})`. This is the identity
whose empirical (Monte Carlo) version RS-DMC's `RSE` returns. -/
theorem score1_ouDensity_tweedie {p : ℝ → ℝ} (hnn : ∀ x, 0 ≤ p x) (hint : Integrable p)
    (hpos : 0 < ∫ x, p x) {s t : ℝ} (hst : s < t) (y : ℝ) :
    score1 (ouDensity p (t - s)) y =
      (rexp (-(t - s)) * posteriorExpect p (rexp (-(t - s))) (ouStd (t - s)) (fun x => x) y
        - y) / (1 - rexp (-2 * (t - s))) := by
  rw [ouDensity, score1_channelDensity_tweedie hnn hint hpos (Real.exp_pos _).ne'
    (ouStd_pos (sub_pos.mpr hst)).ne', ouStd_sq (sub_pos.mpr hst).le]

/-- (c) **OU posterior Stein identity.** Under `RegularPrior p` and `s < t`:
`e^{-(t-s)} E[X_s | X_t = y] - y = (1 - e^{-2(t-s)}) e^{t-s} E[∇ log p_s(X_s) | X_t = y]`. -/
theorem ou_stein_posteriorExpect {p : ℝ → ℝ} (hp : RegularPrior p) {s t : ℝ} (hst : s < t)
    (y : ℝ) :
    rexp (-(t - s)) * posteriorExpect p (rexp (-(t - s))) (ouStd (t - s)) (fun x => x) y - y =
      (1 - rexp (-2 * (t - s))) *
        (rexp (t - s) * posteriorExpect p (rexp (-(t - s))) (ouStd (t - s)) (score1 p) y) := by
  rw [stein_posteriorExpect hp (Real.exp_pos _).ne' (ouStd_pos (sub_pos.mpr hst)).ne',
    ouStd_sq (sub_pos.mpr hst).le, Real.exp_neg, inv_inv]

/-! ### Random-variable form: `posteriorExpect` is a conditional expectation -/

/-- For Lebesgue-integrable `h` and `σ ≠ 0`, `(x, y) ↦ h(x) gaussKernel σ (a x) y` is integrable
on `ℝ × ℝ` for Lebesgue measure (its `y`-integral is `|h(x)|`), for every `a`. -/
theorem integrable_prod_mul_gaussKernel_mul {h : ℝ → ℝ} (hh : Integrable h) (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) :
    Integrable (fun p : ℝ × ℝ => h p.1 * gaussKernel σ (a * p.1) p.2) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 * gaussKernel σ (a * p.1) p.2)
      (volume.prod volume) :=
    hh.1.comp_fst.mul ((continuous_gaussKernel_uncurry σ).comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨ae_of_all _ fun x => (integrable_gaussKernel_right σ (a * x)).const_mul (h x), ?_⟩
  refine hh.norm.congr (ae_of_all _ fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_nonneg _ _ _)]
  rw [integral_const_mul, integral_gaussKernel_right hσ, mul_one]

/-- For measurable `q`, `f`, integrable `q` and `σ ≠ 0`, `y ↦ posteriorExpect q a σ f y` is
Borel measurable. -/
theorem measurable_posteriorExpect {q f : ℝ → ℝ} (hq : Measurable q) (hint : Integrable q)
    (hf : Measurable f) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    Measurable (posteriorExpect q a σ f) := by
  have h : StronglyMeasurable
      (Function.uncurry fun x y => f x * q x * gaussKernel σ (a * x) y) :=
    ((hf.comp measurable_fst).mul (hq.comp measurable_fst) |>.mul
      ((continuous_gaussKernel_uncurry σ).comp
        ((continuous_const.mul continuous_fst).prodMk
          continuous_snd)).measurable).stronglyMeasurable
  exact h.integral_prod_left.measurable.div (continuous_channelDensity hint a hσ).measurable

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Z : Ω → ℝ}

/-- If `X` has law `q(x) dx` on a probability space (`q ≥ 0` measurable), then `q` is a
probability density: `q` is integrable and `∫ q = 1`. -/
theorem integrable_and_integral_eq_one_of_map [IsProbabilityMeasure P] {q : ℝ → ℝ}
    (hnn : ∀ x, 0 ≤ q x) (hqm : Measurable q) (hX : Measurable X)
    (hXlaw : P.map X = priorMeasure q) : Integrable q ∧ ∫ x, q x = 1 := by
  have hprob : IsProbabilityMeasure (priorMeasure q) :=
    hXlaw ▸ (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have hl : ∫⁻ x, ENNReal.ofReal (q x) = 1 := by
    have := hprob.measure_univ
    rwa [priorMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hint : Integrable q := by
    refine ⟨hqm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hl]
    exact ENNReal.one_lt_top
  refine ⟨hint, ?_⟩
  have h := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)
  rw [hl] at h
  exact ENNReal.ofReal_eq_one.mp h

/-- **Law of the channel output.** Let `X`, `Z` be measurable, `P`-independent random variables
on a probability space with `Law(X) = q(x) dx` (`q ≥ 0` a.e.-measurable) and `Z ∼ N(0, 1)`,
and `σ ≠ 0`. Then `Y = aX + σZ` has Lebesgue density `channelDensity q a σ`, for every `a`. -/
theorem map_channel_eq_priorMeasure [IsProbabilityMeasure P] {q : ℝ → ℝ} (hnn : ∀ x, 0 ≤ q x)
    (hqm : AEMeasurable q) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hXlaw : P.map X = priorMeasure q) (hZlaw : P.map Z = gaussianReal 0 1) (a : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) :
    P.map (fun ω => a * X ω + σ * Z ω) = priorMeasure (channelDensity q a σ) := by
  have hX' : Measurable fun ω => a * X ω := hX.const_mul a
  have hind : IndepFun (fun ω => a * X ω) Z P :=
    hXZ.comp (φ := (a * ·)) (ψ := id) (measurable_const_mul a) measurable_id
  have hlaw : P.map (fun ω => a * X ω) = (priorMeasure q).map (fun x => a * x) := by
    rw [← hXlaw, Measure.map_map (measurable_const_mul a) hX]
    rfl
  rw [map_add_mul_eq_withDensity hX' hZ hind hlaw hZlaw hσ,
    ← channelDensity_eq_smoothedDensity hnn hqm]
  rfl

/-- **Defining property of the posterior expectation.** Let `X ∼ q(x) dx` (`q ≥ 0` measurable)
and `Z ∼ N(0, 1)` be measurable and `P`-independent on a probability space, `σ ≠ 0`,
`Y = aX + σZ`, `f` measurable with `f q` Lebesgue integrable (i.e. `f(X) ∈ L¹`), and `g`
measurable with `|g| ≤ M`. Then `E[g(Y) f(X)] = E[g(Y) posteriorExpect q a σ f (Y)]`. -/
theorem integral_mul_eq_integral_posteriorExpect [IsProbabilityMeasure P] {q f g : ℝ → ℝ}
    (hnn : ∀ x, 0 ≤ q x) (hqm : Measurable q) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hXlaw : P.map X = priorMeasure q)
    (hZlaw : P.map Z = gaussianReal 0 1) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (hf : Measurable f) (hfq : Integrable (fun x => f x * q x))
    (hg : Measurable g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) :
    ∫ ω, g (a * X ω + σ * Z ω) * f (X ω) ∂P =
      ∫ ω, g (a * X ω + σ * Z ω) * posteriorExpect q a σ f (a * X ω + σ * Z ω) ∂P := by
  obtain ⟨hint, h1⟩ := integrable_and_integral_eq_one_of_map hnn hqm hX hXlaw
  have := isProbabilityMeasure_priorMeasure hnn hint h1
  have hfμ : Integrable f (priorMeasure q) :=
    (integrable_priorMeasure_iff hnn hqm.aemeasurable).mpr
      (hfq.congr (ae_of_all _ fun x => mul_comm _ _))
  have hXW : Measurable fun ω => (X ω, σ * Z ω) := hX.prodMk (hZ.const_mul σ)
  have hY : Measurable fun ω => a * X ω + σ * Z ω := (hX.const_mul a).add (hZ.const_mul σ)
  have hgY : Measurable fun p : ℝ × ℝ => g (a * p.1 + p.2) :=
    hg.comp ((measurable_fst.const_mul a).add measurable_snd)
  have hF : Measurable fun p : ℝ × ℝ => g (a * p.1 + p.2) * f p.1 :=
    hgY.mul (hf.comp measurable_fst)
  have hL := integral_map (μ := P) hXW.aemeasurable hF.aestronglyMeasurable
  simp only at hL
  have hFint : Integrable (fun p : ℝ × ℝ => g (a * p.1 + p.2) * f p.1)
      ((priorMeasure q).prod (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) :=
    (hfμ.comp_fst _).bdd_mul hgY.aestronglyMeasurable
      (c := M) (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hM _)
  have hinner : ∀ x, ∫ w, g (a * x + w) * f x ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
      (∫ y, g y * gaussKernel σ (a * x) y) * f x := by
    intro x
    rw [integral_mul_const, integral_gaussianReal_const_add hσ hg (a * x)]
  have hprod : Integrable (Function.uncurry fun x y =>
      g y * (f x * q x * gaussKernel σ (a * x) y)) (volume.prod volume) :=
    (integrable_prod_mul_gaussKernel_mul hfq a hσ).bdd_mul
      (hg.comp measurable_snd).aestronglyMeasurable
      (c := M) (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hM _)
  have hR := integral_map (μ := P) hY.aemeasurable
    (f := fun y => g y * posteriorExpect q a σ f y)
    (hg.mul (measurable_posteriorExpect hqm hint hf a hσ)).aestronglyMeasurable
  rw [← hL, ← hR, map_prod_eq_prod hX hZ hXZ hXlaw hZlaw σ, integral_prod _ hFint,
    map_channel_eq_priorMeasure hnn hqm.aemeasurable hX hZ hXZ hXlaw hZlaw a hσ,
    integral_priorMeasure (channelDensity_nonneg hnn a σ)
      (continuous_channelDensity hint a hσ).aemeasurable]
  simp only [hinner]
  rw [integral_priorMeasure hnn hqm.aemeasurable]
  calc ∫ x, q x * ((∫ y, g y * gaussKernel σ (a * x) y) * f x)
      = ∫ x, ∫ y, g y * (f x * q x * gaussKernel σ (a * x) y) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        have h : ∫ y, g y * (f x * q x * gaussKernel σ (a * x) y) =
            (f x * q x) * ∫ y, g y * gaussKernel σ (a * x) y := by
          rw [← integral_const_mul]
          congr 1
          ext y
          ring
        simp only
        rw [h]
        ring
    _ = ∫ y, ∫ x, g y * (f x * q x * gaussKernel σ (a * x) y) := integral_integral_swap hprod
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        have hp := channelDensity_pos_of hnn hint (by rw [h1]; exact one_pos) a hσ y
        simp only
        rw [integral_const_mul, posteriorExpect]
        field_simp

/-- **Posterior expectation = conditional expectation.** Let `X ∼ q(x) dx` (`q ≥ 0`
measurable) and `Z ∼ N(0, 1)` be measurable and `P`-independent on a probability space,
`σ ≠ 0`, `Y = aX + σZ`, and `f` measurable with `f q` Lebesgue integrable (i.e.
`f(X) ∈ L¹(P)`). Then `E[f(X) | σ(Y)] = posteriorExpect q a σ f ∘ Y` `P`-almost surely (a
version of the conditional expectation; defined up to null sets). Every `a` is allowed. -/
theorem condExp_eq_posteriorExpect [IsProbabilityMeasure P] {q f : ℝ → ℝ}
    (hnn : ∀ x, 0 ≤ q x) (hqm : Measurable q) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hXlaw : P.map X = priorMeasure q)
    (hZlaw : P.map Z = gaussianReal 0 1) (a : ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (hf : Measurable f) (hfq : Integrable (fun x => f x * q x)) :
    P[fun ω => f (X ω) | MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance]
      =ᵐ[P] fun ω => posteriorExpect q a σ f (a * X ω + σ * Z ω) := by
  obtain ⟨hint, h1⟩ := integrable_and_integral_eq_one_of_map hnn hqm hX hXlaw
  have hY : Measurable fun ω => a * X ω + σ * Z ω := (hX.const_mul a).add (hZ.const_mul σ)
  have hm := measurable_posteriorExpect hqm hint hf a hσ
  have hfμ : Integrable f (priorMeasure q) :=
    (integrable_priorMeasure_iff hnn hqm.aemeasurable).mpr
      (hfq.congr (ae_of_all _ fun x => mul_comm _ _))
  have hfX : Integrable (fun ω => f (X ω)) P := by
    rw [← hXlaw] at hfμ
    exact (integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mp hfμ
  have hmY : Integrable (fun ω => posteriorExpect q a σ f (a * X ω + σ * Z ω)) P := by
    have h : Integrable (posteriorExpect q a σ f) (priorMeasure (channelDensity q a σ)) := by
      rw [integrable_priorMeasure_iff (channelDensity_nonneg hnn a σ)
        (continuous_channelDensity hint a hσ).aemeasurable]
      refine (integrable_prod_mul_gaussKernel_mul hfq a hσ).integral_prod_right.congr
        (ae_of_all _ fun y => ?_)
      have hp := channelDensity_pos_of hnn hint (by rw [h1]; exact one_pos) a hσ y
      simp only [posteriorExpect]
      field_simp
    rw [← map_channel_eq_priorMeasure hnn hqm.aemeasurable hX hZ hXZ hXlaw hZlaw a hσ] at h
    exact (integrable_map_measure hm.aestronglyMeasurable hY.aemeasurable).mp h
  refine (ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le hfX
    (fun s _ _ => hmY.integrableOn) (fun s hs _ => ?_)
    (hm.comp (comap_measurable _)).aestronglyMeasurable).symm
  exact setIntegral_comap_eq hY (fun g hg hgb =>
    integral_mul_eq_integral_posteriorExpect hnn hqm hX hZ hXZ hXlaw hZlaw a hσ hf hfq hg 1
      hgb) s hs

/-- (a) **Score propagation with conditional expectations.** Let `X ∼ q(x) dx` with
`RegularPrior q` and `Z ∼ N(0, 1)` be measurable and `P`-independent on a probability space,
`a ≠ 0`, `σ ≠ 0`, `Y = aX + σZ` (whose density is `p_Y = channelDensity q a σ`, see
`map_channel_eq_priorMeasure`). Then almost surely
`(log p_Y)'(Y) = a⁻¹ E[(log q)'(X) | σ(Y)]`. (`(log q)'(X) ∈ L¹` because
`(log q)' q = q'` is integrable.) -/
theorem score1_channelDensity_condExp [IsProbabilityMeasure P] {q : ℝ → ℝ}
    (hq : RegularPrior q) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hXlaw : P.map X = priorMeasure q) (hZlaw : P.map Z = gaussianReal 0 1) {a σ : ℝ}
    (ha : a ≠ 0) (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂P, score1 (channelDensity q a σ) (a * X ω + σ * Z ω) =
      a⁻¹ * (P[fun ω => score1 q (X ω) |
        MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance]) ω := by
  have hf : Measurable (score1 q) := measurable_deriv _
  have hfq : Integrable (fun x => score1 q x * q x) :=
    hq.integrable_deriv.congr (ae_of_all _ fun x =>
      (score1_mul_self hq.nonneg hq.differentiable x).symm)
  filter_upwards [condExp_eq_posteriorExpect hq.nonneg hq.differentiable.continuous.measurable
    hX hZ hXZ hXlaw hZlaw a hσ hf hfq] with ω hω
  rw [hω, score1_channelDensity_eq_posteriorExpect hq ha hσ]

/-- (b) **Posterior Stein identity with conditional expectations.** In the setting of
`score1_channelDensity_condExp`, assume moreover `∫ |x| q(x) dx < ∞` (so that `E[X | σ(Y)]`
is defined). Then almost surely
`a E[X | σ(Y)] - Y = σ² a⁻¹ E[(log q)'(X) | σ(Y)]`. -/
theorem stein_condExp [IsProbabilityMeasure P] {q : ℝ → ℝ} (hq : RegularPrior q)
    (hmom : Integrable (fun x => x * q x)) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hXlaw : P.map X = priorMeasure q)
    (hZlaw : P.map Z = gaussianReal 0 1) {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) :
    ∀ᵐ ω ∂P, a * (P[fun ω => X ω |
        MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance]) ω
        - (a * X ω + σ * Z ω) =
      σ ^ 2 * (a⁻¹ * (P[fun ω => score1 q (X ω) |
        MeasurableSpace.comap (fun ω => a * X ω + σ * Z ω) inferInstance]) ω) := by
  have hqm := hq.differentiable.continuous.measurable
  have hf : Measurable (score1 q) := measurable_deriv _
  have hfq : Integrable (fun x => score1 q x * q x) :=
    hq.integrable_deriv.congr (ae_of_all _ fun x =>
      (score1_mul_self hq.nonneg hq.differentiable x).symm)
  filter_upwards [condExp_eq_posteriorExpect hq.nonneg hqm hX hZ hXZ hXlaw hZlaw a hσ
      (f := fun x => x) measurable_id hmom,
    condExp_eq_posteriorExpect hq.nonneg hqm hX hZ hXZ hXlaw hZlaw a hσ hf hfq] with ω h1 h2
  rw [h1, h2]
  exact stein_posteriorExpect hq ha hσ _

/-- (c) **OU marginal law, random-variable form.** If `X_s ∼ p(x) dx` (`p ≥ 0` measurable) and
`Z ∼ N(0, 1)` are measurable and `P`-independent and `s < t`, then
`X_t = e^{-(t-s)} X_s + √(1 - e^{-2(t-s)}) Z` has Lebesgue density `ouDensity p (t - s)`. -/
theorem map_ou_eq_priorMeasure [IsProbabilityMeasure P] {p : ℝ → ℝ} (hnn : ∀ x, 0 ≤ p x)
    (hpm : Measurable p) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hXlaw : P.map X = priorMeasure p) (hZlaw : P.map Z = gaussianReal 0 1) {s t : ℝ}
    (hst : s < t) :
    P.map (fun ω => rexp (-(t - s)) * X ω + ouStd (t - s) * Z ω) =
      priorMeasure (ouDensity p (t - s)) :=
  map_channel_eq_priorMeasure hnn hpm.aemeasurable hX hZ hXZ hXlaw hZlaw _
    (ouStd_pos (sub_pos.mpr hst)).ne'

/-- (c) **OU score propagation with conditional expectations.** If `X_s ∼ p_s(x) dx` with
`RegularPrior p_s` and `Z ∼ N(0, 1)` are measurable and `P`-independent, `s < t`, and
`X_t = e^{-(t-s)} X_s + √(1 - e^{-2(t-s)}) Z` (density `p_t = ouDensity p_s (t - s)`), then
almost surely `∇ log p_t(X_t) = e^{t-s} E[∇ log p_s(X_s) | σ(X_t)]`. -/
theorem score1_ouDensity_condExp [IsProbabilityMeasure P] {p : ℝ → ℝ} (hp : RegularPrior p)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hXlaw : P.map X = priorMeasure p) (hZlaw : P.map Z = gaussianReal 0 1) {s t : ℝ}
    (hst : s < t) :
    ∀ᵐ ω ∂P, score1 (ouDensity p (t - s)) (rexp (-(t - s)) * X ω + ouStd (t - s) * Z ω) =
      rexp (t - s) * (P[fun ω => score1 p (X ω) | MeasurableSpace.comap
        (fun ω => rexp (-(t - s)) * X ω + ouStd (t - s) * Z ω) inferInstance]) ω := by
  filter_upwards [score1_channelDensity_condExp hp hX hZ hXZ hXlaw hZlaw
    (Real.exp_pos (-(t - s))).ne' (ouStd_pos (sub_pos.mpr hst)).ne'] with ω hω
  rw [ouDensity, hω, Real.exp_neg, inv_inv]

end RandomVariables

/-! ### Nonvacuity: Gaussian priors satisfy `RegularPrior` -/

/-- Every Gaussian density `y ↦ gaussKernel σ m y` (the `N(m, σ²)` density, `σ ≠ 0`) satisfies
`RegularPrior`: it is positive, differentiable with derivative `((m - y)/σ²) gaussKernel σ m y`,
and both it and its derivative are Lebesgue integrable. Hence all hypotheses of this file are
satisfiable. -/
theorem regularPrior_gaussKernel {σ : ℝ} (hσ : σ ≠ 0) (m : ℝ) :
    RegularPrior (gaussKernel σ m) := by
  have hderiv : deriv (gaussKernel σ m) = fun y => (m - y) / σ ^ 2 * gaussKernel σ m y :=
    funext fun y => (hasDerivAt_gaussKernel hσ m y).deriv
  refine RegularPrior.of_pos (gaussKernel_pos hσ m)
    (fun y => (hasDerivAt_gaussKernel hσ m y).differentiableAt)
    (integrable_gaussKernel_right σ m) ?_
  rw [hderiv]
  refine Integrable.mono' ((integrable_abs_sub_mul_gaussKernel_right hσ m).div_const (σ ^ 2))
    (((continuous_const.sub continuous_id).div_const _).mul
      (continuous_gaussKernel_uncurry σ |>.comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (sq_nonneg σ),
    abs_of_nonneg (gaussKernel_nonneg _ _ _), abs_sub_comm, div_mul_eq_mul_div]

end FormalizeSampling.ScorePropagation
