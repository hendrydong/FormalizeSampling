module

public import FormalizeSampling.Examples.NoiseScoreOUUnconditional
public import FormalizeSampling.Kernels.GaussianKernels

/-!
# Preconditioned FL-5: non-stationary instances with every hypothesis discharged

Status: **Verified, with no named hypotheses.** This file instantiates the preconditioned
noise–score theorems `NoiseScore.map_flow_eq_of_preconditionedWeakFokkerPlanck` and
`NoiseScore.map_flow_eq_of_klFlow` (`Flow/NoiseScoreEquivalence.lean`) on `Fin d → ℝ` with a
non-identity preconditioner and a **non-stationary** law curve. Every hypothesis of these
theorems, including the two named inputs `PreconditionedWeakFokkerPlanck` (Itô input) and
`UniqueWeakContinuity` (PDE uniqueness), is proved here. Target: `N(0, I_d)`, target score
`s⋆(x) = -x` (`stdScore`).

## Instance 1: diagonal (non-scalar) preconditioner, `ρ₀ = N(m, I)`

Preconditioner `A = diag(a)` with `aᵢ ≥ 0` (any diagonal, in particular non-scalar). Dynamics
`dX = -A X dt + √(2A) dW`: coordinates decouple, coordinate `i` is the OU process with rate
`aᵢ`, so the law curve is defined (`diagLaw`) as the product of the one-dimensional OU laws
`N(mᵢ, 1).bind (OU.ouKernel aᵢ t)`. For `t ≥ 0` it is `N(μ_t, I)` with
`μ_t,ᵢ = e^{-aᵢ t} mᵢ` (`diagLaw_eq`). The marginal score is `-x + μ_t`, so the PFG velocity
`A (s⋆ - ∇log p_t) = -A μ_t` is constant in space (`klFlowVelocity_diag`) and its flow is the
translation `Φ_t(x) = x + μ_t - m` (`diagFlow`). The weak Fokker–Planck equation
`PreconditionedWeakFokkerPlanck (diagLaw a m) (diag a) s⋆` is proved
(`preconditionedWeakFokkerPlanck_diagLaw`) from the explicit Gaussian marginals: the Gaussian
curve is the translation flow law, which solves the continuity equation (PT-1), and the ID-3
identity `ScoreFlowWeak.integral_preconditioned_generator_eq_klFlow_generator` converts that
equation into the preconditioned Fokker–Planck equation at each time.
Uniqueness comes from `uniqueWeakContinuity_klFlowVelocity_of_affine`.

## Instance 2: scalar preconditioner `a • 1`, `ρ₀ = N(m, v₀ I)`

`A = a • 1` with `a ≥ 0` (`a ≠ 1` allowed) and any initial variance `v₀ > 0`: the
preconditioned Langevin law is the OU law `NoiseScoreOUUnconditional.ouLaw a m v₀`
(`ouKernelPi a t ∘ₘ N(m, v₀ I)`), whose variance changes in time when `v₀ ≠ 1`. The Itô input
is obtained from `WeakFokkerPlanckOU.weakFokkerPlanck_ou` via
`weightedLaplacian (a • 1) φ = a Δφ`, and the PFG velocity is the probability-flow velocity of
the OU dynamics (`klFlowVelocity_smul_one`).

## Main results

* `map_diagFlow_eq_diagLaw`: conclusion of `map_flow_eq_of_preconditionedWeakFokkerPlanck`
  for instance 1 (`aᵢ ≥ 0`, any `m`).
* `map_diagFlow_eq_diagLaw_klFlow`: conclusion of `map_flow_eq_of_klFlow` for instance 1 with
  `H = diag(1/aᵢ)` (`aᵢ > 0`), `H⁻¹ = diag(a)`.
* `diagLaw_ne_diagLaw_zero`: instance 1 is non-stationary (`aᵢ > 0`, `mᵢ ≠ 0`, `t > 0`).
* `map_flow_eq_ouLaw_smul_one`, `map_flow_eq_ouLaw_klFlow`: the two theorems for instance 2
  (`a ≥ 0`, resp. `a > 0` with `H = a⁻¹ • 1`).
* `ouLaw_ne_ouLaw_zero`: instance 2 is non-stationary (`a > 0`, `mᵢ ≠ 0`, `t > 0`).
* `nonscalar_example`: a concrete `d = 2` instance with `A = diag(1, 2)`, which is not a scalar
  multiple of the identity, whose law at time `1` differs from the initial law.

## Not proved here

* Non-diagonal SPD preconditioners: not covered (the law would be `N(e^{-At} m, I)`, which
  needs matrix exponentials; no OU kernel for a general `A` exists in the library).
* Diagonal non-scalar `A` together with an initial covariance different from `I`: not covered.
  Then the PFG velocity is `diag(αᵢ(t)) x + β(t)`, which is not of the form `α(t) M x + β(t)`
  handled by the affine uniqueness theorem.
* No SDE theory: the dynamics are represented by OU transition kernels; only one-time
  marginals are matched.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Matrix

namespace FormalizeSampling.NoiseScorePreconditioned

open FormalizeSampling.NoiseScore FormalizeSampling.HeatKernelPi
  FormalizeSampling.HeatFlowDeBruijnPi FormalizeSampling.OULangevinDecayPi
  FormalizeSampling.NoiseScoreOUUnconditional

variable {d : ℕ}

/-- The score `s⋆(x) = -x` of the target `N(0, I_d)`. -/
def stdScore (x : Fin d → ℝ) : Fin d → ℝ := -x

/-- `s⋆` is continuous. -/
theorem continuous_stdScore : Continuous (stdScore (d := d)) := continuous_neg

/-! ### Gaussians `N(μ, I)` (densities `gaussDensity` in `Foundations/HeatFlowDeBruijnPi.lean`) -/

/-- Translation of `N(μ, I)` by `c` is `N(μ + c, I)`. -/
theorem map_add_pi_gaussianReal_one (μ c : Fin d → ℝ) :
    (Measure.pi fun i => gaussianReal (μ i) 1).map (fun x => x + c) =
      Measure.pi fun i => gaussianReal (μ i + c i) 1 := by
  have h := Measure.pi_map_pi (μ := fun i => gaussianReal (μ i) 1)
    (f := fun i u => u + c i)
    (hμ := fun i => by rw [gaussianReal_map_add_const]; infer_instance)
    (fun i => (measurable_add_const (c i)).aemeasurable)
  simp only [gaussianReal_map_add_const] at h
  exact h

/-! ### Instance 1: diagonal preconditioner, initial law `N(m, I)` -/

/-- The mean `μ_t,ᵢ = e^{-aᵢ t} mᵢ` of the diagonal OU dynamics (defined for all `t : ℝ`). -/
noncomputable def diagMean (a m : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i => Real.exp (-a i * t) * m i

/-- `μ_0 = m`. -/
theorem diagMean_zero (a m : Fin d → ℝ) : diagMean a m 0 = m := by
  funext i; simp [diagMean]

/-- `t ↦ μ_t` is continuous. -/
theorem continuous_diagMean (a m : Fin d → ℝ) : Continuous (diagMean a m) := by
  unfold diagMean; fun_prop

/-- **Law curve of `dX = -diag(a) X dt + √(2 diag(a)) dW` from `N(m, I)`.** The coordinates
are independent OU processes with rates `aᵢ`, so the law at time `t` is the product of the
one-dimensional OU laws `N(mᵢ, 1).bind (OU.ouKernel aᵢ t)`. -/
noncomputable def diagLaw (a m : Fin d → ℝ) (t : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => (gaussianReal (m i) 1).bind (OU.ouKernel (a i) t)

/-- **Gaussian marginals.** For `aᵢ ≥ 0` and `t ≥ 0`, `diagLaw a m t = N(μ_t, I)`. -/
theorem diagLaw_eq {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    diagLaw a m t = Measure.pi fun i => gaussianReal (diagMean a m t i) 1 := by
  unfold diagLaw
  congr 1
  funext i
  rw [OU.bind_ouKernel_gaussianReal (ha i) ht]
  simp [diagMean]

/-- At time `0` the law is the initial law `N(m, I)`. -/
theorem diagLaw_zero {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ) :
    diagLaw a m 0 = Measure.pi fun i => gaussianReal (m i) 1 := by
  rw [diagLaw_eq ha m le_rfl, diagMean_zero]

/-- The marginal density `p_t = gaussDensity μ_t` (defined for all `t : ℝ`). -/
noncomputable def diagDensity (a m : Fin d → ℝ) (t : ℝ) : (Fin d → ℝ) → ℝ :=
  gaussDensity (diagMean a m t)

/-- The PFG velocity `-diag(a) μ_t`, constant in space. -/
noncomputable def diagVel (a m : Fin d → ℝ) (t : ℝ) (_x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => -(a i * diagMean a m t i)

/-- **The PFG velocity of instance 1.** `diag(a) (s⋆(x) - ∇log p_t(x)) = -diag(a) μ_t`. -/
theorem klFlowVelocity_diag (a m : Fin d → ℝ) :
    klFlowVelocity (Matrix.diagonal a) stdScore (diagDensity a m) = diagVel a m := by
  funext t x i
  have e : stdScore x - score (diagDensity a m t) x = -diagMean a m t := by
    rw [diagDensity, score_gaussDensity, stdScore]; abel
  rw [klFlowVelocity, e, Matrix.mulVec_diagonal]
  simp [diagVel]

/-- The PFG velocity of instance 1 is jointly continuous. -/
theorem continuous_diagVel (a m : Fin d → ℝ) :
    Continuous (fun q : ℝ × (Fin d → ℝ) => diagVel a m q.1 q.2) := by
  unfold diagVel diagMean
  exact continuous_pi fun i => by fun_prop

/-- The flow of the PFG velocity: the translation `Φ_t(x) = x + μ_t - m`. -/
noncomputable def diagFlow (a m : Fin d → ℝ) (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  x + (diagMean a m t - m)

/-- `Φ_0 = id`. -/
theorem diagFlow_zero (a m x : Fin d → ℝ) : diagFlow a m 0 x = x := by
  simp [diagFlow, diagMean_zero]

/-- Each `Φ_t` is measurable. -/
theorem measurable_diagFlow (a m : Fin d → ℝ) (t : ℝ) : Measurable (diagFlow a m t) :=
  (continuous_id.add continuous_const).measurable

/-- `Φ` solves `∂ₜ Φ_t(x) = -diag(a) μ_t` for every `t : ℝ`. -/
theorem hasDerivAt_diagFlow (a m : Fin d → ℝ) (t : ℝ) (x : Fin d → ℝ) :
    HasDerivAt (fun s => diagFlow a m s x) (diagVel a m t (diagFlow a m t x)) t := by
  rw [hasDerivAt_pi]
  intro i
  have h := (((hasDerivAt_id t).const_mul (-a i)).exp.mul_const (m i)).sub_const (m i)
  have h2 := h.const_add (x i)
  have e : (fun s => diagFlow a m s x i) =
      fun s => x i + (Real.exp (-a i * id s) * m i - m i) := by
    funext s; simp [diagFlow, diagMean]
  have e' : diagVel a m t (diagFlow a m t x) i = Real.exp (-a i * id t) * (-a i * 1) * m i := by
    simp only [diagVel, diagMean, id]; ring
  rw [e, e']
  exact h2

/-- For `t ≥ 0`, `ρ_t = N(m, I).map Φ_t`. -/
theorem diagLaw_eq_map {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    diagLaw a m t = (Measure.pi fun i => gaussianReal (m i) 1).map (diagFlow a m t) := by
  rw [diagLaw_eq ha m ht]
  have e : diagFlow a m t = fun x => x + (diagMean a m t - m) := rfl
  rw [e, map_add_pi_gaussianReal_one]
  congr 1
  funext i
  simp

/-- For `t ≥ 0`, `ρ_t = p_t · Leb`. -/
theorem diagLaw_eq_withDensity {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    diagLaw a m t = volume.withDensity fun x => ENNReal.ofReal (diagDensity a m t x) := by
  rw [diagLaw_eq ha m ht, pi_gaussianReal_one_eq_withDensity]
  rfl

/-- For `t ≥ 0`, `ρ_t` is a probability measure. -/
theorem isProbabilityMeasure_diagLaw {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ)
    {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (diagLaw a m t) := by
  rw [diagLaw_eq ha m ht]; infer_instance

/-- **Itô input for instance 1 (Verified).** For `aᵢ ≥ 0`, the law curve `diagLaw a m`
satisfies the preconditioned weak Fokker–Planck equation of
`dX = diag(a) s⋆(X) dt + √(2 diag(a)) dW`, `s⋆(x) = -x`. Proof: on `t ≥ 0` the curve is the
law of the translation flow `Φ`, which solves the weak continuity equation with velocity
`-diag(a) μ_t` (PT-1); by the ID-3 identity the right-hand sides of the continuity and
preconditioned Fokker–Planck equations agree at every time. -/
theorem preconditionedWeakFokkerPlanck_diagLaw {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i)
    (m : Fin d → ℝ) :
    PreconditionedWeakFokkerPlanck (diagLaw a m) (Matrix.diagonal a) stdScore := by
  intro φ hφ t ht
  have hW : WeakContinuity2 (ContinuityEquation.flowLaw
      (Measure.pi fun i => gaussianReal (m i) 1) (diagFlow a m)) (diagVel a m) :=
    weakContinuity2_flowLaw (continuous_diagVel a m) (hasDerivAt_diagFlow a m)
      fun t => (measurable_diagFlow a m t).aemeasurable
  have h := hW φ hφ t ht
  have hval : ∫ x, diagVel a m t x ⬝ᵥ grad φ x
        ∂(ContinuityEquation.flowLaw (Measure.pi fun i => gaussianReal (m i) 1)
          (diagFlow a m) t) =
      ∫ x, ((Matrix.diagonal a *ᵥ stdScore x) ⬝ᵥ grad φ x +
        weightedLaplacian (Matrix.diagonal a) φ x) ∂(diagLaw a m t) := by
    have hm : Measurable (diagDensity a m t) := (contDiff_gaussDensity _).continuous.measurable
    have hnn : ∀ x, 0 ≤ diagDensity a m t x := fun x => (gaussDensity_pos _ x).le
    rw [ContinuityEquation.flowLaw, ← diagLaw_eq_map ha m ht, diagLaw_eq_withDensity ha m ht,
      integral_withDensity_ofReal hm hnn, integral_withDensity_ofReal hm hnn]
    simp only [diagDensity]
    rw [ScoreFlowWeak.integral_preconditioned_generator_eq_klFlow_generator
        (Matrix.diagonal_transpose a) continuous_stdScore (contDiff_gaussDensity _)
        (gaussDensity_pos _) hφ.1 hφ.2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e := congrFun (congrFun (klFlowVelocity_diag a m) t) x
    simp only [klFlowVelocity, diagDensity] at e
    simp only [e]
  rw [← hval]
  refine h.congr (fun s hs => ?_) ?_
  · simp only [ContinuityEquation.flowLaw]
    rw [diagLaw_eq_map ha m hs]
  · simp only [ContinuityEquation.flowLaw]
    rw [diagLaw_eq_map ha m ht]

/-- **PDE uniqueness for instance 1 (Verified)**, from the affine uniqueness theorem: the
target score is `(-1) x + 0` and the marginal score is `(-1) x + μ_t`. -/
theorem uniqueWeakContinuity_diag (a m : Fin d → ℝ) :
    UniqueWeakContinuity (klFlowVelocity (Matrix.diagonal a) stdScore (diagDensity a m)) :=
  uniqueWeakContinuity_klFlowVelocity_of_affine (Matrix.diagonal a) (σStar := -1)
    (τStar := 0) (σ := fun _ => -1) (τ := diagMean a m) continuousOn_const
    (continuous_diagMean a m).continuousOn (fun x => by simp [stdScore])
    fun t _ x => by rw [diagDensity, score_gaussDensity]; simp

/-- **FL-5 with a diagonal preconditioner, non-stationary instance (Verified, no named
hypotheses).** For `aᵢ ≥ 0` and `m : Fin d → ℝ`, with target `N(0, I)` (`s⋆(x) = -x`),
preconditioner `A = diag(a)`, preconditioned Langevin law `ρ_t = diagLaw a m t`
(`ρ_0 = N(m, I)`) and the translation flow `Φ_t(x) = x + μ_t - m` of the PFG velocity
`A (s⋆ - ∇log p_t)`, the conclusion of `map_flow_eq_of_preconditionedWeakFokkerPlanck` holds:
`ρ_0.map Φ_t = ρ_t` for every `t ≥ 0`. Every hypothesis of that theorem is discharged here.
Only one-time marginals are matched. -/
theorem map_diagFlow_eq_diagLaw {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ) :
    ∀ t, 0 ≤ t → (diagLaw a m 0).map (diagFlow a m t) = diagLaw a m t := by
  have hu : Continuous (fun q : ℝ × (Fin d → ℝ) =>
      klFlowVelocity (Matrix.diagonal a) stdScore (diagDensity a m) q.1 q.2) := by
    rw [klFlowVelocity_diag]; exact continuous_diagVel a m
  have hΦ : ∀ t x, HasDerivAt (fun s => diagFlow a m s x)
      (klFlowVelocity (Matrix.diagonal a) stdScore (diagDensity a m) t (diagFlow a m t x)) t := by
    rw [klFlowVelocity_diag]; exact hasDerivAt_diagFlow a m
  exact map_flow_eq_of_preconditionedWeakFokkerPlanck (Matrix.diagonal_transpose a)
    continuous_stdScore (fun t ht => isProbabilityMeasure_diagLaw ha m ht)
    (fun t ht => diagLaw_eq_withDensity ha m ht) (fun t _ => contDiff_gaussDensity _)
    (fun t _ => gaussDensity_pos _) hu hΦ (measurable_diagFlow a m) (diagFlow_zero a m)
    (preconditionedWeakFokkerPlanck_diagLaw ha m) (uniqueWeakContinuity_diag a m)

/-- `diag(1/aᵢ)⁻¹ = diag(a)` when every `aᵢ ≠ 0`. -/
theorem inv_diagonal_inv {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) :
    (Matrix.diagonal fun i => (a i)⁻¹)⁻¹ = Matrix.diagonal a := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (ha i)

/-- **FL-5 in the `A = H⁻¹` form with `H = diag(1/aᵢ)` (Verified, no named hypotheses).** For
`aᵢ > 0` and `m : Fin d → ℝ`, `H = diag(1/aᵢ)` is positive definite with `H⁻¹ = diag(a)`, and
the conclusion of `map_flow_eq_of_klFlow` holds for the instance of
`map_diagFlow_eq_diagLaw`: `ρ_0.map Φ_t = ρ_t` for every `t ≥ 0`. Every hypothesis of
`map_flow_eq_of_klFlow` is discharged. -/
theorem map_diagFlow_eq_diagLaw_klFlow {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (m : Fin d → ℝ) :
    ∀ t, 0 ≤ t → (diagLaw a m 0).map (diagFlow a m t) = diagLaw a m t := by
  have ha0 : ∀ i, 0 ≤ a i := fun i => (ha i).le
  have hH : (Matrix.diagonal fun i => (a i)⁻¹).PosDef :=
    Matrix.posDef_diagonal_iff.2 fun i => inv_pos.2 (ha i)
  have hinv := inv_diagonal_inv fun i => (ha i).ne'
  have hu : Continuous (fun q : ℝ × (Fin d → ℝ) =>
      klFlowVelocity (Matrix.diagonal fun i => (a i)⁻¹)⁻¹ stdScore (diagDensity a m)
        q.1 q.2) := by
    rw [hinv, klFlowVelocity_diag]; exact continuous_diagVel a m
  have hΦ : ∀ t x, HasDerivAt (fun s => diagFlow a m s x)
      (klFlowVelocity (Matrix.diagonal fun i => (a i)⁻¹)⁻¹ stdScore (diagDensity a m) t
        (diagFlow a m t x)) t := by
    rw [hinv, klFlowVelocity_diag]; exact hasDerivAt_diagFlow a m
  have hFP : PreconditionedWeakFokkerPlanck (diagLaw a m)
      (Matrix.diagonal fun i => (a i)⁻¹)⁻¹ stdScore := by
    rw [hinv]; exact preconditionedWeakFokkerPlanck_diagLaw ha0 m
  have huniq : UniqueWeakContinuity
      (klFlowVelocity (Matrix.diagonal fun i => (a i)⁻¹)⁻¹ stdScore (diagDensity a m)) := by
    rw [hinv]; exact uniqueWeakContinuity_diag a m
  exact map_flow_eq_of_klFlow hH continuous_stdScore
    (fun t ht => isProbabilityMeasure_diagLaw ha0 m ht)
    (fun t ht => diagLaw_eq_withDensity ha0 m ht) (fun t _ => contDiff_gaussDensity _)
    (fun t _ => gaussDensity_pos _) hu hΦ (measurable_diagFlow a m) (diagFlow_zero a m) hFP
    huniq

/-- Pushing a product of probability measures forward by evaluation at `i` gives the `i`-th
factor. -/
theorem map_eval_pi {μ : Fin d → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] (i : Fin d) :
    (Measure.pi μ).map (Function.eval i) = μ i :=
  (measurePreserving_eval μ i).map_eq

/-- If `e^{-c t} x = x` with `c > 0`, `t > 0`, then `x = 0`. -/
theorem eq_zero_of_exp_mul_eq {c t x : ℝ} (hc : 0 < c) (ht : 0 < t)
    (h : Real.exp (-c * t) * x = x) : x = 0 := by
  have hlt : Real.exp (-c * t) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have : (1 - Real.exp (-c * t)) * x = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · exact h1

/-- **Instance 1 is non-stationary.** If `aᵢ ≥ 0` for all `i`, and for some `i` both
`aᵢ > 0` and `mᵢ ≠ 0`, then for every `t > 0` the law `ρ_t` differs from the initial law
`ρ_0` (the `i`-th mean is `e^{-aᵢ t} mᵢ ≠ mᵢ`). -/
theorem diagLaw_ne_diagLaw_zero {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) (m : Fin d → ℝ) {i : Fin d}
    (hai : 0 < a i) (hmi : m i ≠ 0) {t : ℝ} (ht : 0 < t) : diagLaw a m t ≠ diagLaw a m 0 := by
  intro h
  rw [diagLaw_eq ha m ht.le, diagLaw_zero ha m] at h
  have h2 := congrArg (fun μ : Measure (Fin d → ℝ) => μ.map (Function.eval i)) h
  simp only [map_eval_pi] at h2
  have h3 := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) h2
  simp only [integral_id_gaussianReal, diagMean] at h3
  exact hmi (eq_zero_of_exp_mul_eq hai ht h3)

/-- **A concrete non-scalar, non-stationary instance (`d = 2`, `A = diag(1, 2)`).** With
`m = (1, 0)`: `A` is not a scalar multiple of the identity, the conclusion of
`map_flow_eq_of_preconditionedWeakFokkerPlanck` holds at every `t ≥ 0`
(`map_diagFlow_eq_diagLaw`), and the law at time `1` differs from the initial law. -/
theorem nonscalar_example :
    (∀ c : ℝ, Matrix.diagonal ![(1 : ℝ), 2] ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      (∀ t, 0 ≤ t → (diagLaw ![1, 2] ![1, 0] 0).map (diagFlow ![1, 2] ![1, 0] t) =
        diagLaw ![1, 2] ![1, 0] t) ∧
      diagLaw ![(1 : ℝ), 2] ![1, 0] 1 ≠ diagLaw ![1, 2] ![1, 0] 0 := by
  have ha : ∀ i, 0 ≤ (![(1 : ℝ), 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  refine ⟨fun c h => ?_, map_diagFlow_eq_diagLaw ha _, ?_⟩
  · have h0 := congrFun (congrFun h 0) 0
    have h1 := congrFun (congrFun h 1) 1
    simp at h0 h1
    linarith
  · exact diagLaw_ne_diagLaw_zero ha _ (i := 0) (by norm_num) (by norm_num) one_pos

/-! ### Instance 2: scalar preconditioner `a • 1`, initial law `N(m, v₀ I)` -/

/-- `∑ᵢⱼ (a • 1)ᵢⱼ ∂ᵢ∂ⱼφ = a Δφ`. -/
theorem weightedLaplacian_smul_one (a : ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    weightedLaplacian (a • (1 : Matrix (Fin d) (Fin d) ℝ)) φ x = a * laplacian φ x := by
  simp [weightedLaplacian, laplacian, Matrix.one_apply, Finset.mul_sum]

/-- With `A = a • 1`, the PFG velocity is the probability-flow velocity of
`dX = -a X dt + √(2a) dW`: `a (s⋆ - ∇log p_t) = -a x - a ∇log p_t`. -/
theorem klFlowVelocity_smul_one (a : ℝ) (p : ℝ → (Fin d → ℝ) → ℝ) :
    klFlowVelocity (a • (1 : Matrix (Fin d) (Fin d) ℝ)) stdScore p =
      probabilityFlowVelocity (fun _ x => -a • x) a p := by
  funext t x
  simp only [klFlowVelocity, probabilityFlowVelocity, Matrix.smul_mulVec, Matrix.one_mulVec,
    stdScore]
  module

/-- **Itô input for instance 2 (Verified).** For `a ≥ 0`, the OU law curve
`ouLaw a m v₀ = ouKernelPi a · ∘ₘ N(m, v₀ I)` satisfies the preconditioned weak Fokker–Planck
equation with `A = a • 1` and `s⋆(x) = -x`; it is `WeakFokkerPlanckOU.weakFokkerPlanck_ou`
rewritten with `weightedLaplacian (a • 1) φ = a Δφ`. -/
theorem preconditionedWeakFokkerPlanck_ouLaw {a : ℝ} (ha : 0 ≤ a) (m : Fin d → ℝ) (v₀ : ℝ) :
    PreconditionedWeakFokkerPlanck (ouLaw a m v₀) (a • (1 : Matrix (Fin d) (Fin d) ℝ))
      stdScore := by
  have : IsProbabilityMeasure (initLaw m v₀) := by unfold initLaw; infer_instance
  intro φ hφ t ht
  have h := WeakFokkerPlanckOU.weakFokkerPlanck_ou ha (initLaw m v₀) φ hφ t ht
  have e : ∀ x : Fin d → ℝ,
      ((a • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ stdScore x) ⬝ᵥ grad φ x +
        weightedLaplacian (a • (1 : Matrix (Fin d) (Fin d) ℝ)) φ x =
      (-a • x) ⬝ᵥ grad φ x + a * laplacian φ x := by
    intro x
    rw [weightedLaplacian_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, stdScore,
      smul_neg, neg_smul]
  simp only [e]
  exact h

/-- **PDE uniqueness for instance 2 (Verified)**, from the affine uniqueness theorem and the
affine OU score `score_density`. -/
theorem uniqueWeakContinuity_smul_one {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀)
    (m : Fin d → ℝ) :
    UniqueWeakContinuity
      (klFlowVelocity (a • (1 : Matrix (Fin d) (Fin d) ℝ)) stdScore (density a m v₀)) :=
  uniqueWeakContinuity_klFlowVelocity_of_affine _ (σStar := -1) (τStar := 0)
    (continuous_scoreCoef ha hv₀).continuousOn (continuous_scoreShift ha hv₀ m).continuousOn
    (fun x => by simp [stdScore]) fun t _ x => score_density ha hv₀ m t x

/-- **FL-5 with a scalar preconditioner `a • 1`, non-stationary instance (Verified, no named
hypotheses).** For `a ≥ 0` (e.g. `a ≠ 1`), `v₀ > 0` and `m : Fin d → ℝ`, with target
`N(0, I)` (`s⋆(x) = -x`), preconditioner `A = a • 1`, law curve `ρ_t = ouLaw a m v₀ t`
(`ρ_0 = N(m, v₀ I)`) and the explicit flow `Φ = NoiseScoreOUUnconditional.flow a m v₀` of the
PFG velocity `A (s⋆ - ∇log p_t)`, the conclusion of
`map_flow_eq_of_preconditionedWeakFokkerPlanck` holds: `ρ_0.map Φ_t = ρ_t` for every `t ≥ 0`.
Every hypothesis of that theorem is discharged. Only one-time marginals are matched. -/
theorem map_flow_eq_ouLaw_smul_one {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) :
    ∀ t, 0 ≤ t → (ouLaw a m v₀ 0).map (flow a m v₀ t) = ouLaw a m v₀ t := by
  have e := klFlowVelocity_smul_one (d := d) a (density a m v₀)
  have hu : Continuous (fun q : ℝ × (Fin d → ℝ) =>
      klFlowVelocity (a • (1 : Matrix (Fin d) (Fin d) ℝ)) stdScore (density a m v₀)
        q.1 q.2) := by
    rw [e]
    have e' : (fun q : ℝ × (Fin d → ℝ) =>
        probabilityFlowVelocity (fun _ x => -a • x) a (density a m v₀) q.1 q.2) =
        fun q => velCoef a v₀ q.1 • q.2 + velShift a m v₀ q.1 :=
      funext fun q => probabilityFlowVelocity_eq ha hv₀ m q.1 q.2
    rw [e']
    have hα : Continuous (velCoef a v₀) :=
      continuous_const.sub (continuous_const.mul (continuous_scoreCoef ha hv₀))
    have hβ : Continuous (velShift a m v₀) :=
      ((continuous_scoreShift ha hv₀ m).const_smul a).neg
    exact ((hα.comp continuous_fst).smul continuous_snd).add (hβ.comp continuous_fst)
  have hΦ : ∀ t x, HasDerivAt (fun s => flow a m v₀ s x)
      (klFlowVelocity (a • (1 : Matrix (Fin d) (Fin d) ℝ)) stdScore (density a m v₀) t
        (flow a m v₀ t x)) t := by
    rw [e]; exact hasDerivAt_flow ha hv₀ m
  have hA : (a • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ = a • 1 := by
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  exact map_flow_eq_of_preconditionedWeakFokkerPlanck hA continuous_stdScore
    (fun t _ => inferInstance) (fun t ht => ouLaw_eq_withDensity ha hv₀ ht m)
    (fun t _ => contDiff_density a m v₀ t) (fun t _ => density_pos ha hv₀ m t) hu hΦ
    (measurable_flow a m v₀) (flow_zero a m v₀) (preconditionedWeakFokkerPlanck_ouLaw ha m v₀)
    (uniqueWeakContinuity_smul_one ha hv₀ m)

/-- `(a⁻¹ • 1)⁻¹ = a • 1` for `a ≠ 0`. -/
theorem inv_smul_one_inv {a : ℝ} (ha : a ≠ 0) :
    (a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = a • 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ ha, one_smul]

/-- **FL-5 in the `A = H⁻¹` form with `H = a⁻¹ • 1` (Verified, no named hypotheses).** For
`a > 0`, `v₀ > 0` and `m : Fin d → ℝ`, `H = a⁻¹ • 1` is positive definite with
`H⁻¹ = a • 1`, and the conclusion of `map_flow_eq_of_klFlow` holds for the instance of
`map_flow_eq_ouLaw_smul_one`. Every hypothesis of `map_flow_eq_of_klFlow` is discharged. -/
theorem map_flow_eq_ouLaw_klFlow {a v₀ : ℝ} (ha : 0 < a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) :
    ∀ t, 0 ≤ t → (ouLaw a m v₀ 0).map (flow a m v₀ t) = ouLaw a m v₀ t := by
  have hH : (a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
    exact Matrix.PosDef.one.smul (inv_pos.2 ha)
  have hinv := inv_smul_one_inv (d := d) ha.ne'
  have e := klFlowVelocity_smul_one (d := d) a (density a m v₀)
  have hu : Continuous (fun q : ℝ × (Fin d → ℝ) =>
      klFlowVelocity (a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ stdScore (density a m v₀)
        q.1 q.2) := by
    rw [hinv, e]
    have e' : (fun q : ℝ × (Fin d → ℝ) =>
        probabilityFlowVelocity (fun _ x => -a • x) a (density a m v₀) q.1 q.2) =
        fun q => velCoef a v₀ q.1 • q.2 + velShift a m v₀ q.1 :=
      funext fun q => probabilityFlowVelocity_eq ha.le hv₀ m q.1 q.2
    rw [e']
    have hα : Continuous (velCoef a v₀) :=
      continuous_const.sub (continuous_const.mul (continuous_scoreCoef ha.le hv₀))
    have hβ : Continuous (velShift a m v₀) :=
      ((continuous_scoreShift ha.le hv₀ m).const_smul a).neg
    exact ((hα.comp continuous_fst).smul continuous_snd).add (hβ.comp continuous_fst)
  have hΦ : ∀ t x, HasDerivAt (fun s => flow a m v₀ s x)
      (klFlowVelocity (a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ stdScore (density a m v₀) t
        (flow a m v₀ t x)) t := by
    rw [hinv, e]; exact hasDerivAt_flow ha.le hv₀ m
  have hFP : PreconditionedWeakFokkerPlanck (ouLaw a m v₀)
      (a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ stdScore := by
    rw [hinv]; exact preconditionedWeakFokkerPlanck_ouLaw ha.le m v₀
  have huniq : UniqueWeakContinuity
      (klFlowVelocity (a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ stdScore (density a m v₀)) := by
    rw [hinv]; exact uniqueWeakContinuity_smul_one ha.le hv₀ m
  exact map_flow_eq_of_klFlow hH continuous_stdScore (fun t _ => inferInstance)
    (fun t ht => ouLaw_eq_withDensity ha.le hv₀ ht m) (fun t _ => contDiff_density a m v₀ t)
    (fun t _ => density_pos ha.le hv₀ m t) hu hΦ (measurable_flow a m v₀) (flow_zero a m v₀)
    hFP huniq

/-- **Instance 2 is non-stationary.** For `a > 0`, `v₀ ≥ 0`, `t > 0` and `m` with `mᵢ ≠ 0` for
some `i`, the OU law at time `t` differs from the initial law (the `i`-th mean is
`e^{-at} mᵢ ≠ mᵢ`). -/
theorem ouLaw_ne_ouLaw_zero {a v₀ : ℝ} (ha : 0 < a) (hv₀ : 0 ≤ v₀) (m : Fin d → ℝ) {i : Fin d}
    (hmi : m i ≠ 0) {t : ℝ} (ht : 0 < t) : ouLaw a m v₀ t ≠ ouLaw a m v₀ 0 := by
  intro h
  rw [ouLaw_eq_pi ha.le hv₀ ht.le, ouLaw_eq_pi ha.le hv₀ le_rfl] at h
  have h2 := congrArg (fun μ : Measure (Fin d → ℝ) => μ.map (Function.eval i)) h
  simp only [map_eval_pi] at h2
  have h3 := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) h2
  simp only [integral_id_gaussianReal, meanAt, mul_zero, Real.exp_zero, one_mul] at h3
  exact hmi (eq_zero_of_exp_mul_eq ha ht h3)

end FormalizeSampling.NoiseScorePreconditioned
