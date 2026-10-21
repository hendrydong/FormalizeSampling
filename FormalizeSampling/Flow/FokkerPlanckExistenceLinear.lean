module

public import FormalizeSampling.Flow.FokkerPlanckExistenceTime

/-!
# Existence for the weak Fokker–Planck equation: globally Lipschitz (linearly growing) drifts

Status: **Verified.** For an **autonomous, globally Lipschitz** drift
`b : ℝᵈ → ℝᵈ` (hence of linear growth `‖b x‖ ≤ (L + ‖b 0‖) (1 + ‖x‖)`, unbounded in general),
`D > 0` and an **arbitrary** probability measure `ρ₀` (no moment assumption), the dyadic
Euler–Maruyama laws `emCurve b hb D ρ₀ n t` of `Flow/FokkerPlanckExistenceStep.lean` converge
weakly at every time to a weakly continuous solution of `WeakFokkerPlanck (ν ·) (fun _ => b) D`.
This is the special case `K = 0` of the time-dependent theorem
`exists_weakFokkerPlanck_global` (`Flow/FokkerPlanckExistenceTime.lean`).

## Main results

* `exists_weakFokkerPlanck_lipschitz`, `exists_weakFokkerPlanck_lipschitz_measure`: the
  autonomous Lipschitz case (no bound on `b`); `exists_weakFokkerPlanck` and
  `exists_weakFokkerPlanck_measure` state it with an additional bound `‖b x‖ ≤ B`.
* `exists_weakFokkerPlanck_ou`: Ornstein–Uhlenbeck drift `b x = -a x` (any `a : ℝ`), any `ρ₀`.
* `exists_weakFokkerPlanck_langevin`: overdamped Langevin drift `b = -∇U` with `∇U` Lipschitz;
  `lipschitzWith_grad_of_fderiv_le`: this holds for every `C²` potential `U` whose Hessian
  `D(∇U)` is bounded in operator norm.
* `exists_langevin_law_fl5`: the Langevin law curve exists and discharges the **Itô input**
  `WeakFokkerPlanck` of FL-5 (`NoiseScore.map_flow_eq_of_weakFokkerPlanck`); the remaining
  inputs of FL-5 (densities, probability-flow ODE flow, PDE uniqueness) stay hypotheses.

## Not proved here

* Locally Lipschitz or superlinearly growing drifts (e.g. `U(x) = |x|⁴`, whose gradient is not
  globally Lipschitz); dissipative ones are in `Flow/FokkerPlanckExistenceDissipative`.
* Uniqueness of the solution (see `Flow/FokkerPlanckUniquenessLipschitz`); identification
  with the law of the SDE (no SDE theory); the density, flow and uniqueness hypotheses of FL-5
  for the Langevin law.
* `D = 0`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU

variable {d : ℕ}

/-- With a constant drift family, the time-dependent EM kernels are the autonomous ones. -/
theorem tdPow_const (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D h : ℝ) (k : ℕ) :
    tdPow (fun _ => b) (fun _ => hb) D h k = emPow b hb D h k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show emStep b hb D h ∘ₖ tdPow (fun _ => b) (fun _ => hb) D h k =
      emStep b hb D h ∘ₖ emPow b hb D h k
    rw [ih]

/-- With a constant drift family, the time-dependent dyadic laws are the autonomous ones. -/
theorem tdCurve_const (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D : ℝ)
    (ρ₀ : Measure (Fin d → ℝ)) (n : ℕ) (t : ℝ) :
    tdCurve (fun _ => b) (fun _ => hb) D ρ₀ n t = emCurve b hb D ρ₀ n t := by
  unfold tdCurve emCurve; rw [tdPow_const]

/-- `tdCurve_const` for the laws as elements of `ProbabilityMeasure`. -/
theorem emCurveP_eq_tdCurveP (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D : ℝ)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (n : ℕ) (t : ℝ) :
    emCurveP b hb D ρ₀ n t = tdCurveP (fun _ => b) (fun _ => hb) D ρ₀ n t :=
  Subtype.ext (tdCurve_const b hb D ρ₀ n t).symm

/-- **Lipschitz drifts grow at most linearly**: `‖b x‖ ≤ (L + ‖b 0‖) (1 + ‖x‖)`. -/
theorem norm_le_of_lipschitzWith {b : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L b) (x : Fin d → ℝ) : ‖b x‖ ≤ (L + ‖b 0‖) * (1 + ‖x‖) := by
  have h1 : ‖b x - b 0‖ ≤ L * ‖x‖ := by simpa using hL.norm_sub_le x 0
  have h2 : ‖b x‖ ≤ ‖b x - b 0‖ + ‖b 0‖ := by
    have := norm_add_le (b x - b 0) (b 0); rwa [sub_add_cancel] at this
  have := norm_nonneg x
  have := norm_nonneg (b 0)
  nlinarith [L.coe_nonneg, mul_nonneg (norm_nonneg (b 0)) (norm_nonneg x)]

/-- **Existence for the weak Fokker–Planck equation, globally Lipschitz drift (Verified, no Itô
input).** Let `b : ℝᵈ → ℝᵈ` be `L`-Lipschitz (no boundedness assumption; e.g. `b = -∇U` with
`∇U` Lipschitz, or `b x = -a x`), `D > 0` and `ρ₀` **any** probability measure on
`Fin d → ℝ`. There is a weakly continuous curve `ν : ℝ → 𝒫(ℝᵈ)` with `ν 0 = ρ₀` solving
`WeakFokkerPlanck (fun t => ν t) (fun _ => b) D`; moreover `ν t` is the weak limit of the
dyadic Euler–Maruyama laws `emCurve b hb D ρ₀ n t` (step `2⁻ⁿ`) at every time `t`. -/
theorem exists_weakFokkerPlanck_lipschitz {b : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L b) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (fun _ => b) D ∧
      ∀ t, Tendsto (fun n => emCurveP b hL.continuous.measurable D ρ₀ n t) atTop (𝓝 (ν t)) := by
  have hb := hL.continuous.measurable
  obtain ⟨ν, h0, hc, hfp, htd⟩ := exists_weakFokkerPlanck_global (b := fun _ => b)
    (fun _ => hb) (fun _ => hL) (B := L + ‖b 0‖) (fun _ x => norm_le_of_lipschitzWith hL x)
    (K := 0) (fun _ _ _ => by simp) hD ρ₀
  exact ⟨ν, h0, hc, hfp, fun t => (htd t).congr fun n => (emCurveP_eq_tdCurveP b hb D ρ₀ n t).symm⟩

/-- **Measure-curve form, globally Lipschitz drift.** For `b` Lipschitz, `D > 0` and any
probability measure `ρ₀`, there is `ρ : ℝ → Measure (Fin d → ℝ)` with `ρ 0 = ρ₀`, every `ρ t`
a probability measure and `WeakFokkerPlanck ρ (fun _ => b) D`. -/
theorem exists_weakFokkerPlanck_lipschitz_measure {b : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L b) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => b) D := by
  obtain ⟨ν, h0, -, hfp, -⟩ := exists_weakFokkerPlanck_lipschitz hL hD ρ₀
  exact ⟨fun t => ν t, h0, fun t => inferInstance, hfp⟩

/-- **Existence for the weak Fokker–Planck equation, bounded Lipschitz drift (Verified, no Itô
input).** Let `b : ℝᵈ → ℝᵈ` be `L`-Lipschitz and bounded (`‖b x‖ ≤ B`), `D > 0` and `ρ₀` any
probability measure on `Fin d → ℝ`. There is a weakly continuous curve
`ν : ℝ → ProbabilityMeasure` with `ν 0 = ρ₀` solving
`WeakFokkerPlanck (fun t => ν t) (fun _ => b) D`, and `ν t` is the weak limit of the dyadic
Euler–Maruyama laws (step `2⁻ⁿ`) at every time `t`. The bound on `b` is not needed: this is
`exists_weakFokkerPlanck_lipschitz`. -/
theorem exists_weakFokkerPlanck {b : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L b) {B : ℝ} (_hB : ∀ x, ‖b x‖ ≤ B) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (fun _ => b) D ∧
      ∀ t, Tendsto (fun n => emCurveP b hL.continuous.measurable D ρ₀ n t) atTop (𝓝 (ν t)) :=
  exists_weakFokkerPlanck_lipschitz hL hD ρ₀

/-- **Existence for the weak Fokker–Planck equation, measure-curve form (Verified).** For
`b` Lipschitz and bounded, `D > 0` and any probability measure `ρ₀` on `Fin d → ℝ`, there is
`ρ : ℝ → Measure (Fin d → ℝ)` with `ρ 0 = ρ₀`, every `ρ t` a probability measure, and
`WeakFokkerPlanck ρ (fun _ => b) D` (the named Itô input of FL-5, for this autonomous drift).
The bound on `b` is not needed: this is `exists_weakFokkerPlanck_lipschitz_measure`. -/
theorem exists_weakFokkerPlanck_measure {b : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L b) {B : ℝ} (_hB : ∀ x, ‖b x‖ ≤ B) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => b) D :=
  exists_weakFokkerPlanck_lipschitz_measure hL hD ρ₀

/-- **Ornstein–Uhlenbeck.** For any `a : ℝ`, `D > 0` and any probability measure `ρ₀`, the
weak Fokker–Planck equation of `dX = -a X dt + √(2D) dW` has a probability-measure solution
started at `ρ₀` (the weak limit of the dyadic EM laws). -/
theorem exists_weakFokkerPlanck_ou (a : ℝ) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ x => (-a) • x) D :=
  exists_weakFokkerPlanck_lipschitz_measure (lipschitzWith_smul (-a)) hD ρ₀

/-- **Bounded Hessian implies Lipschitz gradient.** If `U` is `C²` and the derivative of its
coordinate gradient (the Hessian) satisfies `‖D(∇U)(x)‖ ≤ L` for all `x`, then `∇U` is
`L`-Lipschitz. -/
theorem lipschitzWith_grad_of_fderiv_le {U : (Fin d → ℝ) → ℝ} (hU : ContDiff ℝ 2 U)
    {L : ℝ≥0} (hH : ∀ x, ‖fderiv ℝ (grad U) x‖₊ ≤ L) : LipschitzWith L (grad U) := by
  have hdiff : Differentiable ℝ (grad U) := by
    have : grad U = fun x i => partialDeriv i U x := rfl
    rw [this]
    exact differentiable_pi.2 fun i =>
      (contDiff_partialDeriv hU i).differentiable one_ne_zero
  exact lipschitzWith_of_nnnorm_fderiv_le hdiff hH

/-- `x ↦ -∇U(x)` is `L`-Lipschitz when `∇U` is. -/
theorem lipschitzWith_neg_grad {U : (Fin d → ℝ) → ℝ} {L : ℝ≥0}
    (hU : LipschitzWith L (grad U)) : LipschitzWith L fun x => -grad U x :=
  LipschitzWith.of_dist_le_mul fun x y => by rw [dist_neg_neg]; exact hU.dist_le_mul x y

/-- **Overdamped Langevin (Verified, no Itô input).** Let `U : ℝᵈ → ℝ` have an `L`-Lipschitz
gradient (e.g. `C²` with bounded Hessian, `lipschitzWith_grad_of_fderiv_le`), `D > 0` and `ρ₀`
any probability measure. Then the weak Fokker–Planck equation of
`dX = -∇U(X) dt + √(2D) dW` has a weakly continuous probability-measure solution `ν` with
`ν 0 = ρ₀`, equal at every time to the weak limit of the dyadic EM laws (the unadjusted
Langevin algorithm with step `2⁻ⁿ`). -/
theorem exists_weakFokkerPlanck_langevin {U : (Fin d → ℝ) → ℝ} {L : ℝ≥0}
    (hU : LipschitzWith L (grad U)) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧
      WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (fun _ x => -grad U x) D ∧
      ∀ t, Tendsto (fun n => emCurveP (fun x => -grad U x)
        (lipschitzWith_neg_grad hU).continuous.measurable D ρ₀ n t) atTop (𝓝 (ν t)) :=
  exists_weakFokkerPlanck_lipschitz (lipschitzWith_neg_grad hU) hD ρ₀

/-- **The Langevin law curve discharges the Itô input of FL-5.** For `∇U` `L`-Lipschitz,
`D > 0` and any probability measure `ρ₀`, there is a curve `ρ` of probability measures with
`ρ 0 = ρ₀` satisfying `WeakFokkerPlanck ρ b D` for `b = -∇U` (constant in time); hence, for
**any** densities `p`, flow `Φ` satisfying the remaining hypotheses of
`NoiseScore.map_flow_eq_of_weakFokkerPlanck` (density representation `ρ t = p t · Leb`, `C¹`
positive `p t`, jointly continuous probability-flow velocity `u = b - D ∇log p`, `Φ` a
measurable flow of `u` with `Φ 0 = id`, and the PDE-uniqueness input
`UniqueWeakContinuity u`), the one-time marginals agree: `(ρ 0).map (Φ t) = ρ t`, `t ≥ 0`. -/
theorem exists_langevin_law_fl5 {U : (Fin d → ℝ) → ℝ} {L : ℝ≥0}
    (hU : LipschitzWith L (grad U)) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ x => -grad U x) D ∧
      ∀ (p : ℝ → (Fin d → ℝ) → ℝ) (Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ),
        (∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x)) →
        (∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) → (∀ t, 0 ≤ t → ∀ x, 0 < p t x) →
        Continuous (fun q : ℝ × (Fin d → ℝ) =>
          probabilityFlowVelocity (fun _ x => -grad U x) D p q.1 q.2) →
        (∀ t x, HasDerivAt (fun s => Φ s x)
          (probabilityFlowVelocity (fun _ x => -grad U x) D p t (Φ t x)) t) →
        (∀ t, Measurable (Φ t)) → (∀ x, Φ 0 x = x) →
        UniqueWeakContinuity (probabilityFlowVelocity (fun _ x => -grad U x) D p) →
        ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t := by
  obtain ⟨ρ, h0, hprob, hfp⟩ :=
    exists_weakFokkerPlanck_lipschitz_measure (lipschitzWith_neg_grad hU) hD ρ₀
  refine ⟨ρ, h0, hprob, hfp, fun p Φ hρ hp hpos hu hΦ hΦm hΦ0 huniq => ?_⟩
  exact map_flow_eq_of_weakFokkerPlanck (fun t _ => hprob t) hρ hp hpos hu hΦ hΦm hΦ0 hfp
    huniq

end FormalizeSampling.FokkerPlanckExistence
