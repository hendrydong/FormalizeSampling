module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FormalizeSampling.Foundations.VectorCalculus
public import FormalizeSampling.Kernels.GaussianKernels
public import FormalizeSampling.Foundations.GaussianKL

/-!
# The Gaussian PFG flow versus Ornstein–Uhlenbeck: equal marginals, different two-time laws

An exact, self-contained one-dimensional example. Target `p⋆ = N(0, 1)`, scalar preconditioner
`a`, initial law `N(m₀, v₀)` with `v₀ > 0`.

* **Stochastic side.** Overdamped preconditioned Langevin dynamics for `p⋆` is the OU process
  `dXₜ = -a Xₜ dt + √(2a) dWₜ`, which is **represented by its exact Gaussian transition law**
  `FormalizeSampling.OU.ouKernel a t` (see `Kernels/GaussianKernels.lean`). No SDE theory is
  formalised: the kernel is a definition, not a theorem about an SDE.
* **Deterministic side (PFG).** With `mₜ = e^{-at} m₀`, `vₜ = 1 + (v₀ - 1) e^{-2at}` and
  `pₜ = N(mₜ, vₜ)`, the PFG / probability-flow velocity is
  `uₜ(y) = a (∂ log p⋆(y) - ∂ log pₜ(y))` (state scores, `score1`), and the explicit flow map is
  `Φₜ(y₀) = mₜ + √(vₜ / v₀) (y₀ - m₀)`.

## Main results (registry IDs)

* `velocity_eq`: `uₜ(y) = a (-y + (y - mₜ) / vₜ)` where `vₜ > 0`.
* `hasDerivAt_flow`, `flow_zero_eq_id`: `Φ` solves the PFG ODE `∂ₜ Φₜ(y₀) = uₜ(Φₜ(y₀))`,
  `Φ₀ = id`.
* `map_flow_gaussianReal`: `Φₜ # N(m₀, v₀) = N(mₜ, vₜ)`.
* FL-5, Gaussian instance: `map_flow_eq_bind_ouKernel` — one-time marginal equality
  `Φₜ # N(m₀, v₀) = N(m₀, v₀).bind (ouKernel a t)` for all `t ≥ 0`. In this Gaussian class both
  sides are computed explicitly, so **no PDE-uniqueness hypothesis is used**.
* CE-01-continuous: `twoTime_flow_ne_ou` — for `a, t > 0` the joint law of `(Y₀, Yₜ)` under the
  flow differs from the OU joint law `N(m₀, v₀) ⊗ₘ ouKernel a t` of `(X₀, Xₜ)`; witnessed by
  `flowTwoTime_graph` (graph of `Φₜ` has measure `1`) and `ouTwoTime_graph` (measure `0`).
  `marginal_eq_and_twoTime_ne` packages both facts.
* FL-2 (exact Gaussian instance, optional item): `klDiv_gaussianReal_stdGaussian` computes
  `KL(N(m, v) ‖ N(0, 1)) = (v + m² - 1 - log v) / 2` with Mathlib's `klDiv` (the case `m₂ = 0`,
  `v₂ = 1` of the general formula `klDiv_gaussianReal_gaussianReal_of_ne_zero`; both, with the
  Gaussian log-density and quadratic moments, are in `Foundations/GaussianKL.lean`);
  `hasDerivAt_klDiv_marginal` / `hasDerivAt_klDiv_flow` prove
  `d/dt KL(pₜ ‖ p⋆) = -a E_{pₜ} |∂ log pₜ - ∂ log p⋆|²` and
  `hasDerivAt_klDiv_marginal_closedForm` gives the value `-a (mₜ² + (vₜ - 1)² / vₜ)`.

## Conventions

* `v₀ : ℝ≥0` is the initial variance (Mathlib's `gaussianReal` takes variances); `vₜ` is
  computed in `ℝ` as `1 + ((v₀ : ℝ) - 1) e^{-2at}` (no truncated `ℝ≥0` subtraction) and passed
  to `gaussianReal` via `Real.toNNReal`, which is faithful whenever `vₜ ≥ 0` (e.g. `a, t ≥ 0`).
* Results that need it assume `v₀ ≠ 0` explicitly: for `v₀ = 0`, `√(vₜ / v₀) = 0` by the
  `x / 0 = 0` convention and the flow formula is meaningless.
* Scores are state scores `score1 p y = (log p)'(y)`; `targetScore` and `scoreAt` are defined
  through `score1` of the actual Gaussian densities, and their closed forms are theorems.

## Not proved here

* Anything about SDE solutions, or that the OU kernel is the law of an SDE (modelling input).
* General (non-Gaussian) marginal equality FL-5 or KL dissipation FL-2; only the
  Gaussian class is covered, and there is no uniqueness theorem for the continuity equation.
* That `Φ` is the *unique* solution of the PFG ODE, or that `pₜ` solves a continuity equation
  (only the explicit flow and its pushforward are computed).
* Equality or difference of full path laws beyond the two-time law.
* Matrix preconditioners and dimension `d > 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.GaussianFlowVsOU

/-! ### Gaussian state score -/

/-! ### The Gaussian PFG data -/

/-- The mean `mₜ = e^{-at} m₀` of `pₜ` (the OU / PFG marginal at time `t`). -/
noncomputable def meanAt (a m₀ t : ℝ) : ℝ := Real.exp (-a * t) * m₀

/-- The variance `vₜ = 1 + (v₀ - 1) e^{-2at}` of `pₜ`, computed in `ℝ` (no truncated
subtraction). It is positive for `a ≥ 0`, `t ≥ 0`, `v₀ > 0` (`varAt_pos`). -/
noncomputable def varAt (a : ℝ) (v₀ : ℝ≥0) (t : ℝ) : ℝ :=
  1 + ((v₀ : ℝ) - 1) * Real.exp (-2 * a * t)

/-- The target score `∂ log p⋆` for `p⋆ = N(0, 1)`; it equals `-y` (`targetScore_eq`). -/
noncomputable def targetScore (y : ℝ) : ℝ := score1 (gaussianPDFReal 0 1) y

/-- The state score `∂ log pₜ` of the current marginal `pₜ = N(mₜ, vₜ)`. -/
noncomputable def scoreAt (a m₀ : ℝ) (v₀ : ℝ≥0) (t y : ℝ) : ℝ :=
  score1 (gaussianPDFReal (meanAt a m₀ t) (varAt a v₀ t).toNNReal) y

/-- The PFG velocity with scalar preconditioner `a`:
`uₜ(y) = a (∂ log p⋆(y) - ∂ log pₜ(y))`. -/
noncomputable def velocity (a m₀ : ℝ) (v₀ : ℝ≥0) (t y : ℝ) : ℝ :=
  a * (targetScore y - scoreAt a m₀ v₀ t y)

/-- The explicit PFG flow map `Φₜ(y₀) = mₜ + √(vₜ / v₀) (y₀ - m₀)`. -/
noncomputable def flow (a m₀ : ℝ) (v₀ : ℝ≥0) (t y₀ : ℝ) : ℝ :=
  meanAt a m₀ t + Real.sqrt (varAt a v₀ t / v₀) * (y₀ - m₀)

/-- The target score of `N(0, 1)` is `y ↦ -y`. -/
theorem targetScore_eq (y : ℝ) : targetScore y = -y := by
  rw [targetScore, score1_gaussianPDFReal 0 one_ne_zero]
  simp

/-- For `0 ≤ a`, `v₀ ≠ 0` and `0 ≤ t`, the marginal variance `vₜ` is strictly positive. -/
theorem varAt_pos {a t : ℝ} {v₀ : ℝ≥0} (ha : 0 ≤ a) (hv₀ : v₀ ≠ 0) (ht : 0 ≤ t) :
    0 < varAt a v₀ t := by
  have hv : 0 < (v₀ : ℝ) := by positivity
  have he : Real.exp (-2 * a * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg ha ht]
  have he0 := Real.exp_pos (-2 * a * t)
  unfold varAt
  nlinarith [mul_pos hv he0]

/-- At time `0` the marginal variance is the initial one: `v₀` at `t = 0`. -/
theorem varAt_zero (a : ℝ) (v₀ : ℝ≥0) : varAt a v₀ 0 = v₀ := by
  simp [varAt]

/-- At time `0` the marginal mean is the initial one: `m₀` at `t = 0`. -/
theorem meanAt_zero (a m₀ : ℝ) : meanAt a m₀ 0 = m₀ := by
  simp [meanAt]

/-- Where `vₜ > 0`, the current score is `∂ log pₜ(y) = -(y - mₜ) / vₜ`. -/
theorem scoreAt_eq {a m₀ t : ℝ} {v₀ : ℝ≥0} (hvt : 0 < varAt a v₀ t) (y : ℝ) :
    scoreAt a m₀ v₀ t y = -(y - meanAt a m₀ t) / varAt a v₀ t := by
  rw [scoreAt, score1_gaussianPDFReal _ (by simpa using hvt), Real.coe_toNNReal _ hvt.le]

/-- **PFG velocity in closed form.** Where `vₜ > 0`,
`uₜ(y) = a (-y + (y - mₜ) / vₜ)`. -/
theorem velocity_eq {a m₀ t : ℝ} {v₀ : ℝ≥0} (hvt : 0 < varAt a v₀ t) (y : ℝ) :
    velocity a m₀ v₀ t y = a * (-y + (y - meanAt a m₀ t) / varAt a v₀ t) := by
  rw [velocity, targetScore_eq, scoreAt_eq hvt]
  ring

/-- The flow starts at the identity: `Φ₀(y₀) = y₀` (for `v₀ ≠ 0`). -/
theorem flow_zero (a m₀ : ℝ) {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0) (y₀ : ℝ) : flow a m₀ v₀ 0 y₀ = y₀ := by
  have hv : (v₀ : ℝ) ≠ 0 := by simpa using hv₀
  simp [flow, meanAt, varAt, hv]

/-- The flow starts at the identity: `Φ₀ = id` (for `v₀ ≠ 0`). -/
theorem flow_zero_eq_id (a m₀ : ℝ) {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0) : flow a m₀ v₀ 0 = id :=
  funext (flow_zero a m₀ hv₀)

/-- **`Φ` solves the PFG ODE.** For `v₀ ≠ 0`, every `a`, `m₀`, `y₀` and every time `t` with
`vₜ > 0`: `∂ₜ Φₜ(y₀) = uₜ(Φₜ(y₀))`, as a `HasDerivAt` statement in `t`. -/
theorem hasDerivAt_flow {a m₀ t : ℝ} {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0) (hvt : 0 < varAt a v₀ t)
    (y₀ : ℝ) :
    HasDerivAt (fun s => flow a m₀ v₀ s y₀) (velocity a m₀ v₀ t (flow a m₀ v₀ t y₀)) t := by
  have hv : 0 < (v₀ : ℝ) := by positivity
  have hm : HasDerivAt (fun s => meanAt a m₀ s) (Real.exp (-a * t) * (-a) * m₀) t := by
    have := (((hasDerivAt_id t).const_mul (-a)).exp).mul_const m₀
    exact this.congr_deriv (by simp)
  have hV : HasDerivAt (fun s => varAt a v₀ s / v₀)
      (((v₀ : ℝ) - 1) * (Real.exp (-2 * a * t) * (-2 * a)) / v₀) t := by
    have := ((((hasDerivAt_id t).const_mul (-2 * a)).exp).const_mul ((v₀ : ℝ) - 1)).const_add 1
      |>.div_const (v₀ : ℝ)
    exact this.congr_deriv (by simp)
  have hq : varAt a v₀ t / v₀ ≠ 0 := (div_pos hvt hv).ne'
  have hF := hm.add ((hV.sqrt hq).mul_const (y₀ - m₀))
  refine hF.congr_deriv ?_
  rw [velocity_eq hvt]
  set r := Real.sqrt (varAt a v₀ t / v₀) with hr_def
  have hr2 : r ^ 2 = varAt a v₀ t / v₀ := Real.sq_sqrt (div_pos hvt hv).le
  have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos hvt hv)
  have hVr : varAt a v₀ t = r ^ 2 * v₀ := by
    rw [hr2]
    field_simp
  have hE : ((v₀ : ℝ) - 1) * Real.exp (-2 * a * t) = r ^ 2 * v₀ - 1 := by
    rw [← hVr]
    unfold varAt
    ring
  rw [show flow a m₀ v₀ t y₀ = meanAt a m₀ t + r * (y₀ - m₀) from rfl, hVr,
    show ((v₀ : ℝ) - 1) * (Real.exp (-2 * a * t) * (-2 * a)) = (r ^ 2 * v₀ - 1) * (-2 * a) by
      rw [← hE]; ring]
  unfold meanAt
  field_simp
  ring

/-- `Φ` solves the PFG ODE for all `t ≥ 0` when `a ≥ 0` and `v₀ ≠ 0`:
`∂ₜ Φₜ(y₀) = uₜ(Φₜ(y₀))`. -/
theorem hasDerivAt_flow_of_nonneg {a m₀ t : ℝ} {v₀ : ℝ≥0} (ha : 0 ≤ a) (hv₀ : v₀ ≠ 0)
    (ht : 0 ≤ t) (y₀ : ℝ) :
    HasDerivAt (fun s => flow a m₀ v₀ s y₀) (velocity a m₀ v₀ t (flow a m₀ v₀ t y₀)) t :=
  hasDerivAt_flow hv₀ (varAt_pos ha hv₀ ht) y₀

/-- The flow map `Φₜ` is measurable (it is affine). -/
theorem measurable_flow (a m₀ : ℝ) (v₀ : ℝ≥0) (t : ℝ) : Measurable (flow a m₀ v₀ t) := by
  unfold flow
  fun_prop

/-! ### One-time marginals -/

/-- **Pushforward of the initial Gaussian.** For `v₀ ≠ 0` and any `t` with `vₜ ≥ 0`,
`Φₜ # N(m₀, v₀) = N(mₜ, vₜ)`. -/
theorem map_flow_gaussianReal {a m₀ t : ℝ} {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0)
    (hvt : 0 ≤ varAt a v₀ t) :
    (gaussianReal m₀ v₀).map (flow a m₀ v₀ t) =
      gaussianReal (meanAt a m₀ t) (varAt a v₀ t).toNNReal := by
  have hv : 0 < (v₀ : ℝ) := by positivity
  set r := Real.sqrt (varAt a v₀ t / v₀) with hr_def
  have hr2 : r ^ 2 = varAt a v₀ t / v₀ := Real.sq_sqrt (div_nonneg hvt hv.le)
  have hfl : flow a m₀ v₀ t = (fun y => y + (meanAt a m₀ t - r * m₀)) ∘ (fun y => r * y) := by
    funext y
    simp only [flow, Function.comp_apply, ← hr_def]
    ring
  rw [hfl, ← Measure.map_map (measurable_add_const _) (measurable_const_mul _),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  congr 1
  · ring
  · ext
    rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hvt, hr2]
    field_simp

/-- **One-time marginal equality (FL-5, Gaussian class).** For `0 ≤ a`, `0 ≤ t` and
`v₀ ≠ 0`, the PFG flow and the OU dynamics started from `N(m₀, v₀)` have the same law at time
`t`: `Φₜ # N(m₀, v₀) = N(m₀, v₀).bind (ouKernel a t)`. Both sides are computed explicitly as
`N(mₜ, vₜ)`; no uniqueness hypothesis is used. -/
theorem map_flow_eq_bind_ouKernel {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (m₀ : ℝ) {v₀ : ℝ≥0}
    (hv₀ : v₀ ≠ 0) :
    (gaussianReal m₀ v₀).map (flow a m₀ v₀ t) = (gaussianReal m₀ v₀).bind (OU.ouKernel a t) := by
  rw [map_flow_gaussianReal hv₀ (varAt_pos ha hv₀ ht).le, OU.bind_ouKernel_gaussianReal ha ht]
  rfl

/-! ### Two-time laws (CE-01-continuous) -/

/-- Under the flow, the joint law of `(Y₀, Yₜ) = (Y₀, Φₜ Y₀)` with `Y₀ ∼ N(m₀, v₀)` gives
measure `1` to the graph `{(y, Φₜ y)}`. -/
theorem flowTwoTime_graph (a m₀ : ℝ) (v₀ : ℝ≥0) (t : ℝ) :
    ((gaussianReal m₀ v₀).map (fun y => (y, flow a m₀ v₀ t y)))
      {p : ℝ × ℝ | p.2 = flow a m₀ v₀ t p.1} = 1 :=
  OU.map_graph_apply_graph _ (measurable_flow a m₀ v₀ t)

/-- For `0 < a` and `0 < t`, the OU joint law of `(X₀, Xₜ)` with `X₀ ∼ N(m₀, v₀)` gives
measure `0` to the graph `{(y, Φₜ y)}` of the flow map. -/
theorem ouTwoTime_graph {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (m₀ : ℝ) (v₀ : ℝ≥0) :
    ((gaussianReal m₀ v₀) ⊗ₘ OU.ouKernel a t) {p : ℝ × ℝ | p.2 = flow a m₀ v₀ t p.1} = 0 :=
  OU.compProd_ouKernel_graph_eq_zero ha ht _ (measurable_flow a m₀ v₀ t)

/-- **Two-time laws differ (CE-01-continuous).** For `0 < a` and `0 < t` (any `m₀`, `v₀`), the
flow's joint law of `(Y₀, Yₜ)` differs from the OU joint law of `(X₀, Xₜ)`:
`(id, Φₜ) # N(m₀, v₀) ≠ N(m₀, v₀) ⊗ₘ ouKernel a t`. -/
theorem twoTime_flow_ne_ou {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (m₀ : ℝ) (v₀ : ℝ≥0) :
    (gaussianReal m₀ v₀).map (fun y => (y, flow a m₀ v₀ t y)) ≠
      (gaussianReal m₀ v₀) ⊗ₘ OU.ouKernel a t :=
  OU.map_graph_ne_compProd_ouKernel ha ht _ (measurable_flow a m₀ v₀ t)

/-- **Equal one-time marginals, different two-time laws.** For `0 < a`, `0 < t` and
`v₀ ≠ 0`, starting from `N(m₀, v₀)`, the PFG flow and OU have the same law at time `t` but
different joint laws of the pair (time `0`, time `t`). -/
theorem marginal_eq_and_twoTime_ne {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (m₀ : ℝ) {v₀ : ℝ≥0}
    (hv₀ : v₀ ≠ 0) :
    (gaussianReal m₀ v₀).map (flow a m₀ v₀ t) = (gaussianReal m₀ v₀).bind (OU.ouKernel a t) ∧
      (gaussianReal m₀ v₀).map (fun y => (y, flow a m₀ v₀ t y)) ≠
        (gaussianReal m₀ v₀) ⊗ₘ OU.ouKernel a t :=
  ⟨map_flow_eq_bind_ouKernel ha.le ht.le m₀ hv₀, twoTime_flow_ne_ou ha ht m₀ v₀⟩

/-! ### KL dissipation along the Gaussian marginals (FL-2, Gaussian instance) -/

/-- **Relative Fisher information of the Gaussian marginal.** Where `vₜ > 0`,
`E_{pₜ} |∂ log pₜ - ∂ log p⋆|² = mₜ² + (vₜ - 1)² / vₜ` for `pₜ = N(mₜ, vₜ)`, `p⋆ = N(0, 1)`. -/
theorem integral_sq_scoreAt_sub_targetScore {a m₀ t : ℝ} {v₀ : ℝ≥0} (hvt : 0 < varAt a v₀ t) :
    ∫ y, (scoreAt a m₀ v₀ t y - targetScore y) ^ 2
        ∂gaussianReal (meanAt a m₀ t) (varAt a v₀ t).toNNReal =
      meanAt a m₀ t ^ 2 + (varAt a v₀ t - 1) ^ 2 / varAt a v₀ t := by
  have hfun : (fun y => (scoreAt a m₀ v₀ t y - targetScore y) ^ 2) = fun y =>
      (1 - 1 / varAt a v₀ t) ^ 2 * (y - meanAt a m₀ t) ^ 2 +
        (2 * meanAt a m₀ t * (1 - 1 / varAt a v₀ t)) * (y - meanAt a m₀ t) +
          meanAt a m₀ t ^ 2 := by
    funext y
    rw [scoreAt_eq hvt, targetScore_eq]
    field_simp
    ring
  rw [hfun, integral_quadratic_gaussianReal, Real.coe_toNNReal _ hvt.le]
  field_simp
  ring

/-- **KL dissipation along the Gaussian marginals (FL-2, exact Gaussian instance).** At every
time `t` with `vₜ > 0` (any `a`, `m₀`, `v₀`),
`d/dt KL(pₜ ‖ p⋆) = -a E_{pₜ} |∂ log (pₜ / p⋆)|²`, where `pₜ = N(mₜ, vₜ)`, `p⋆ = N(0, 1)` and the
KL divergence is Mathlib's `klDiv` (finite here, read through `ENNReal.toReal`). The integrand
is written as `(∂ log pₜ - ∂ log p⋆)²` using `scoreAt` and `targetScore`. -/
theorem hasDerivAt_klDiv_marginal {a m₀ t : ℝ} {v₀ : ℝ≥0} (hvt : 0 < varAt a v₀ t) :
    HasDerivAt (fun s => (klDiv (gaussianReal (meanAt a m₀ s) (varAt a v₀ s).toNNReal)
        (gaussianReal 0 1)).toReal)
      (-a * ∫ y, (scoreAt a m₀ v₀ t y - targetScore y) ^ 2
        ∂gaussianReal (meanAt a m₀ t) (varAt a v₀ t).toNNReal) t := by
  rw [integral_sq_scoreAt_sub_targetScore hvt]
  have hm : HasDerivAt (fun s => meanAt a m₀ s) (Real.exp (-a * t) * (-a) * m₀) t := by
    have := (((hasDerivAt_id t).const_mul (-a)).exp).mul_const m₀
    exact this.congr_deriv (by simp)
  have hV : HasDerivAt (fun s => varAt a v₀ s)
      (((v₀ : ℝ) - 1) * (Real.exp (-2 * a * t) * (-2 * a))) t := by
    have := ((((hasDerivAt_id t).const_mul (-2 * a)).exp).const_mul ((v₀ : ℝ) - 1)).const_add 1
    exact this.congr_deriv (by simp)
  have hg := (((hV.add (hm.pow 2)).sub_const 1).sub (hV.log hvt.ne')).div_const 2
  have heq : (fun s => (klDiv (gaussianReal (meanAt a m₀ s) (varAt a v₀ s).toNNReal)
        (gaussianReal 0 1)).toReal) =ᶠ[nhds t]
      fun s => (varAt a v₀ s + meanAt a m₀ s ^ 2 - 1 - Real.log (varAt a v₀ s)) / 2 := by
    filter_upwards [hV.continuousAt (Ioi_mem_nhds hvt)] with s hs
    have hs' : 0 < varAt a v₀ s := hs
    rw [klDiv_gaussianReal_stdGaussian _ (by simpa using hs'), Real.coe_toNNReal _ hs'.le,
      ENNReal.toReal_ofReal]
    have := Real.log_le_sub_one_of_pos hs'
    nlinarith [sq_nonneg (meanAt a m₀ s)]
  refine (hg.congr_of_eventuallyEq heq).congr_deriv ?_
  have hE : ((v₀ : ℝ) - 1) * (Real.exp (-2 * a * t) * (-2 * a)) =
      -2 * a * (varAt a v₀ t - 1) := by
    unfold varAt
    ring
  have hm' : Real.exp (-a * t) * (-a) * m₀ = -a * meanAt a m₀ t := by
    unfold meanAt
    ring
  rw [hE, hm']
  field_simp
  ring

/-- The dissipation rate in closed form: where `vₜ > 0`,
`d/dt KL(pₜ ‖ p⋆) = -a (mₜ² + (vₜ - 1)² / vₜ)` for `pₜ = N(mₜ, vₜ)`, `p⋆ = N(0, 1)`. -/
theorem hasDerivAt_klDiv_marginal_closedForm {a m₀ t : ℝ} {v₀ : ℝ≥0}
    (hvt : 0 < varAt a v₀ t) :
    HasDerivAt (fun s => (klDiv (gaussianReal (meanAt a m₀ s) (varAt a v₀ s).toNNReal)
        (gaussianReal 0 1)).toReal)
      (-a * (meanAt a m₀ t ^ 2 + (varAt a v₀ t - 1) ^ 2 / varAt a v₀ t)) t := by
  have h := hasDerivAt_klDiv_marginal (m₀ := m₀) hvt
  rwa [integral_sq_scoreAt_sub_targetScore hvt] at h

/-- **KL dissipation along the PFG flow.** For `v₀ ≠ 0` and every time `t` with `vₜ > 0`, the
law `Φₛ # N(m₀, v₀)` of the PFG flow satisfies
`d/ds KL(Φₛ # N(m₀, v₀) ‖ N(0, 1)) |_{s = t} = -a E_{pₜ} |∂ log pₜ - ∂ log p⋆|²`,
with `pₜ = N(mₜ, vₜ) = Φₜ # N(m₀, v₀)` (`map_flow_gaussianReal`). -/
theorem hasDerivAt_klDiv_flow {a m₀ t : ℝ} {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0)
    (hvt : 0 < varAt a v₀ t) :
    HasDerivAt (fun s => (klDiv ((gaussianReal m₀ v₀).map (flow a m₀ v₀ s))
        (gaussianReal 0 1)).toReal)
      (-a * ∫ y, (scoreAt a m₀ v₀ t y - targetScore y) ^ 2
        ∂gaussianReal (meanAt a m₀ t) (varAt a v₀ t).toNNReal) t := by
  refine (hasDerivAt_klDiv_marginal hvt).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun s => varAt a v₀ s) t := by
    unfold varAt
    fun_prop
  filter_upwards [hc (Ioi_mem_nhds hvt)] with s hs
  have hs' : 0 < varAt a v₀ s := hs
  rw [map_flow_gaussianReal hv₀ hs'.le]

end FormalizeSampling.GaussianFlowVsOU
