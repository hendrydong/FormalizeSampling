module

public import FormalizeSampling.Flow.ContinuityUniquenessAffine
public import FormalizeSampling.Flow.OULangevinDecayPi
public import FormalizeSampling.Foundations.HeatFlowDeBruijnPi
public import FormalizeSampling.Flow.WeakFokkerPlanckOU

/-!
# FL-5 for the OU dynamics with an isotropic Gaussian initial law

Status: **Verified, with no named hypotheses** (`map_flow_eq_ouLaw`). The conditional form
`map_flow_eq_ouLaw_of_weakFokkerPlanck` isolates the single named input `WeakFokkerPlanck` (the
Itô input) of FL-5; it is discharged by `WeakFokkerPlanckOU.weakFokkerPlanck_ou`
(`Flow/WeakFokkerPlanckOU.lean`), and PDE uniqueness by the affine uniqueness theorem.

Setting: rate `a ≥ 0`, mean `m : Fin d → ℝ`, initial variance `v₀ > 0`,
`ρ₀ = ⊗ᵢ N(mᵢ, v₀)` (`initLaw`), and the OU law curve `ρ_t = ouKernelPi a t ∘ₘ ρ₀` (`ouLaw`),
i.e. the transition law of `dX = -a X dt + √(2a) dW` (drift `b_t(x) = -a x`, `D = a`).

For `t ≥ 0` the law is explicit (`ouLaw_eq_pi`): `ρ_t = ⊗ᵢ N(μ_t,ᵢ, v_t)` with
`μ_t = e^{-at} m` (`meanAt`) and `v_t = 1 + (v₀ - 1) e^{-2at} > 0` (`varAt`), with Lebesgue
density `p_t(x) = heatDensityPi v_t (x - μ_t)` (`density`, `ouLaw_eq_withDensity`). For `t < 0`
the density is defined by clamping time to `max t 0`, so that every coefficient below is
continuous on all of `ℝ`. The score is affine, `∇log p_t(x) = σ_t x + τ_t` with
`σ_t = -1/v_t`, `τ_t = μ_t / v_t` (`score_density`), hence the probability-flow velocity
`u_t(x) = -a x - a ∇log p_t(x) = α_t x + β_t` is affine with scalar coefficient
(`probabilityFlowVelocity_eq`). Its explicit flow, defined for **all** `t : ℝ`, is
`Φ_t(x) = e^{A(t)} (x + ∫₀ᵗ e^{-A(u)} β_u du)` with `A(t) = ∫₀ᵗ α` (`flow`,
`hasDerivAt_flow`, `flow_zero`).

## Main results

* `ouLaw_eq_pi`, `ouLaw_eq_withDensity`, `ouLaw_zero`: the OU marginals.
* `contDiff_density`, `density_pos`, `score_density`: regularity and affine score.
* `hasDerivAt_flow`: `Φ` solves `∂ₜ Φ_t(x) = u_t(Φ_t(x))` for every `t : ℝ`.
* `map_flow_eq_ouLaw_of_weakFokkerPlanck` (FL-5, OU / Gaussian instance): if the OU law curve
  satisfies `WeakFokkerPlanck` with drift `-a x` and `D = a`, then
  `ρ₀.map Φ_t = ouKernelPi a t ∘ₘ ρ₀` for every `t ≥ 0`. All other hypotheses of
  `NoiseScore.map_flow_eq_of_weakFokkerPlanck_of_affine` (densities, regularity, positivity,
  joint continuity of the velocity, the flow, PDE uniqueness) are discharged here.
* `map_flow_eq_ouLaw` (FL-5, OU / Gaussian instance, **unconditional**): the same conclusion
  with the Itô input supplied by `WeakFokkerPlanckOU.weakFokkerPlanck_ou`.

## Not proved here

* The weak Fokker–Planck equation is not re-derived here: it is imported from
  `Flow/WeakFokkerPlanckOU.lean` (proved from the explicit transition kernel).
* No SDE theory: the OU dynamics is represented by its transition kernel `ouKernelPi`.
* Only isotropic Gaussian initial laws with a common variance `v₀ > 0`; only one-time
  marginals are matched (two-time laws differ, `GaussianFlowVsOU.twoTime_flow_ne_ou`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace FormalizeSampling.NoiseScoreOUUnconditional

open FormalizeSampling.NoiseScore FormalizeSampling.HeatKernelPi
  FormalizeSampling.HeatFlowDeBruijnPi FormalizeSampling.OULangevinDecayPi

variable {d : ℕ}

/-! ### Marginal parameters and laws -/

/-- The OU marginal mean `μ_t = e^{-at} m`. -/
noncomputable def meanAt (a : ℝ) (m : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i => Real.exp (-a * t) * m i

/-- The OU marginal variance `v_t = 1 + (v₀ - 1) e^{-2at}` (per coordinate). -/
noncomputable def varAt (a v₀ t : ℝ) : ℝ := 1 + (v₀ - 1) * Real.exp (-2 * a * t)

/-- For `a ≥ 0`, `v₀ > 0`, `t ≥ 0`, the marginal variance is positive. -/
theorem varAt_pos {a v₀ t : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (ht : 0 ≤ t) :
    0 < varAt a v₀ t := by
  have h1 : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 := Real.exp_pos (-2 * a * t)
  unfold varAt
  nlinarith

/-- The initial law `ρ₀ = ⊗ᵢ N(mᵢ, v₀)`. -/
noncomputable def initLaw (m : Fin d → ℝ) (v₀ : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => gaussianReal (m i) v₀.toNNReal

/-- The OU law curve `ρ_t = ouKernelPi a t ∘ₘ ρ₀`. -/
noncomputable def ouLaw (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) : Measure (Fin d → ℝ) :=
  ouKernelPi a t ∘ₘ initLaw m v₀

/-- Every `ρ_t` is a probability measure. -/
instance isProbabilityMeasure_ouLaw (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) :
    IsProbabilityMeasure (ouLaw a m v₀ t) := by
  unfold ouLaw initLaw; infer_instance

/-- At time `0` the OU law is the initial law. -/
theorem ouLaw_zero (a : ℝ) (m : Fin d → ℝ) (v₀ : ℝ) : ouLaw a m v₀ 0 = initLaw m v₀ := by
  rw [ouLaw, ouKernelPi_eq_ouKernelVarPi, ouKernelVarPi_comp_of_mul_eq_zero (mul_zero a)]

/-- **OU marginals of an isotropic Gaussian initial law.** For `t ≥ 0`,
`ouKernelPi a t ∘ₘ ⊗ᵢ N(mᵢ, v₀) = ⊗ᵢ N(e^{-at} mᵢ, 1 + (v₀ - 1) e^{-2at})`. -/
theorem ouLaw_eq_pi {a v₀ t : ℝ} (ha : 0 ≤ a) (hv₀ : 0 ≤ v₀) (ht : 0 ≤ t) (m : Fin d → ℝ) :
    ouLaw a m v₀ t =
      Measure.pi fun i => gaussianReal (meanAt a m t i) (varAt a v₀ t).toNNReal := by
  rw [ouLaw, ouKernelPi_eq_ouKernelVarPi, ouKernelVarPi_comp_eq, initLaw,
    pi_gaussianReal_map_scalePi _ hv₀]
  set c := Real.exp (-a * t)
  have hc2 : c ^ 2 = Real.exp (-2 * a * t) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 0 ≤ 1 * (1 - Real.exp (-2 * a * t)) := by
    have : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    linarith
  have e : (varAt a v₀ t).toNNReal =
      (1 * (1 - Real.exp (-2 * a * t))).toNNReal + (c ^ 2 * v₀).toNNReal := by
    rw [← Real.toNNReal_add h1 (by positivity), hc2]; unfold varAt; ring_nf
  calc heatKernelPi (1 * (1 - Real.exp (-2 * a * t))).toNNReal ∘ₘ
        (Measure.pi fun i => gaussianReal (c * m i) (c ^ 2 * v₀).toNNReal)
      = (heatKernelPi (c ^ 2 * v₀).toNNReal (meanAt a m t)).bind
          (heatKernelPi (1 * (1 - Real.exp (-2 * a * t))).toNNReal) := rfl
    _ = heatKernelPi ((1 * (1 - Real.exp (-2 * a * t))).toNNReal + (c ^ 2 * v₀).toNNReal)
          (meanAt a m t) := bind_heatKernelPi _ _ _
    _ = _ := by rw [← e, heatKernelPi_apply]

/-- The (clamped) OU marginal density `p_t(x) = heatDensityPi v_{t⁺} (x - μ_{t⁺})`,
`t⁺ = max t 0`. -/
noncomputable def density (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) (x : Fin d → ℝ) : ℝ :=
  heatDensityPi (varAt a v₀ (max t 0)) (x - meanAt a m (max t 0))

/-- **Density of the OU marginals.** For `t ≥ 0`, `ρ_t = p_t · Leb`. -/
theorem ouLaw_eq_withDensity {a v₀ t : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (ht : 0 ≤ t)
    (m : Fin d → ℝ) :
    ouLaw a m v₀ t = volume.withDensity fun x => ENNReal.ofReal (density a m v₀ t x) := by
  rw [ouLaw_eq_pi ha hv₀.le ht, ← heatKernelPi_apply,
    heatKernelPi_eq_withDensity (varAt_pos ha hv₀ ht)]
  simp [density, max_eq_left ht]

/-- The density is everywhere positive. -/
theorem density_pos {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) (t : ℝ)
    (x : Fin d → ℝ) : 0 < density a m v₀ t x :=
  heatDensityPi_pos (varAt_pos ha hv₀ (le_max_right t 0)) _

/-- Gradient of the density: `∇p_t(x) = heatGradPi v_{t⁺} (x - μ_{t⁺})`. -/
theorem hasFDerivAt_density (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (density a m v₀ t)
      (dotCLM (heatGradPi (varAt a v₀ (max t 0)) (x - meanAt a m (max t 0)))) x := by
  have h := (hasFDerivAt_heatDensityPi (varAt a v₀ (max t 0)) (x - meanAt a m (max t 0))).comp
    x ((hasFDerivAt_id x).sub_const (meanAt a m (max t 0)))
  have e : density a m v₀ t =
      fun x => heatDensityPi (varAt a v₀ (max t 0)) (x - meanAt a m (max t 0)) := rfl
  rw [e]
  simpa [Function.comp_def] using h

/-- The density is `C¹`. -/
theorem contDiff_density (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) :
    ContDiff ℝ 1 (density a m v₀ t) :=
  contDiff_one_iff_hasFDerivAt.2 ⟨_, continuous_dotCLM
    ((continuous_heatGradPi _).comp (continuous_id.sub continuous_const)),
    hasFDerivAt_density a m v₀ t⟩

/-- Scalar score coefficient `σ_t = -1 / v_{t⁺}`. -/
noncomputable def scoreCoef (a v₀ t : ℝ) : ℝ := -1 / varAt a v₀ (max t 0)

/-- Score shift `τ_t = μ_{t⁺} / v_{t⁺}`. -/
noncomputable def scoreShift (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) : Fin d → ℝ :=
  (1 / varAt a v₀ (max t 0)) • meanAt a m (max t 0)

/-- **Affine score.** `∇log p_t(x) = σ_t x + τ_t` for every `t : ℝ`. -/
theorem score_density {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) (t : ℝ)
    (x : Fin d → ℝ) :
    score (density a m v₀ t) x = scoreCoef a v₀ t • x + scoreShift a m v₀ t := by
  funext i
  have hV := varAt_pos ha hv₀ (le_max_right t 0)
  rw [score_apply_of_pos (hasFDerivAt_density a m v₀ t x).differentiableAt
    (density_pos ha hv₀ m t x), partialDeriv, (hasFDerivAt_density a m v₀ t x).fderiv,
    dotCLM_single]
  have hp := density_pos ha hv₀ m t x
  simp only [heatGradPi, density] at hp ⊢
  simp only [scoreCoef, scoreShift, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- `σ` is continuous on `ℝ`. -/
theorem continuous_scoreCoef {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) :
    Continuous (scoreCoef a v₀) := by
  unfold scoreCoef varAt
  refine continuous_const.div (by fun_prop) fun t => ?_
  exact (varAt_pos ha hv₀ (le_max_right t 0)).ne'

/-- `τ` is continuous on `ℝ`. -/
theorem continuous_scoreShift {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) :
    Continuous (scoreShift a m v₀) := by
  have hV : Continuous fun t => varAt a v₀ (max t 0) := by unfold varAt; fun_prop
  have hμ : Continuous fun t => meanAt a m (max t 0) := by unfold meanAt; fun_prop
  exact (continuous_const.div hV fun t => (varAt_pos ha hv₀ (le_max_right t 0)).ne').smul hμ

/-! ### The probability-flow velocity and its flow -/

/-- Velocity coefficient `α_t = -a - a σ_t`. -/
noncomputable def velCoef (a v₀ t : ℝ) : ℝ := -a - a * scoreCoef a v₀ t

/-- Velocity shift `β_t = -a τ_t`. -/
noncomputable def velShift (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) : Fin d → ℝ :=
  -(a • scoreShift a m v₀ t)

/-- **Affine probability-flow velocity.** `-a x - a ∇log p_t(x) = α_t x + β_t`. -/
theorem probabilityFlowVelocity_eq {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ)
    (t : ℝ) (x : Fin d → ℝ) :
    probabilityFlowVelocity (fun _ x => -a • x) a (density a m v₀) t x =
      velCoef a v₀ t • x + velShift a m v₀ t := by
  simp only [probabilityFlowVelocity, score_density ha hv₀ m t x, velCoef, velShift]
  module

/-- The primitive `A(t) = ∫₀ᵗ α`. -/
noncomputable def velPrim (a v₀ t : ℝ) : ℝ := affinePrim (velCoef a v₀) t

/-- The explicit flow `Φ_t(x) = e^{A(t)} (x + ∫₀ᵗ e^{-A(u)} β_u du)`, for all `t : ℝ`. -/
noncomputable def flow (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  Real.exp (velPrim a v₀ t) •
    (x + ∫ u in (0 : ℝ)..t, Real.exp (-velPrim a v₀ u) • velShift a m v₀ u)

/-- `Φ_0 = id`. -/
theorem flow_zero (a : ℝ) (m : Fin d → ℝ) (v₀ : ℝ) (x : Fin d → ℝ) : flow a m v₀ 0 x = x := by
  simp [flow, velPrim, affinePrim]

/-- Each `Φ_t` is measurable. -/
theorem measurable_flow (a : ℝ) (m : Fin d → ℝ) (v₀ t : ℝ) : Measurable (flow a m v₀ t) := by
  unfold flow; fun_prop

/-- **`Φ` is a flow of the probability-flow velocity on all of `ℝ`.** For every `t : ℝ` and
`x`, `∂ₜ Φ_t(x) = u_t(Φ_t(x))`, `u = probabilityFlowVelocity (-a ·) a p`. -/
theorem hasDerivAt_flow {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) (t : ℝ)
    (x : Fin d → ℝ) :
    HasDerivAt (fun s => flow a m v₀ s x)
      (probabilityFlowVelocity (fun _ x => -a • x) a (density a m v₀) t (flow a m v₀ t x)) t := by
  have hα : Continuous (velCoef a v₀) :=
    continuous_const.sub (continuous_const.mul (continuous_scoreCoef ha hv₀))
  have hβ : Continuous (velShift a m v₀) :=
    ((continuous_scoreShift ha hv₀ m).const_smul a).neg
  have hA : ∀ s, HasDerivAt (velPrim a v₀) (velCoef a v₀ s) s :=
    fun s => hasDerivAt_affinePrim hα s
  have hAc : Continuous (velPrim a v₀) := continuous_affinePrim hα
  have hI : HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, Real.exp (-velPrim a v₀ u) • velShift a m v₀ u)
      (Real.exp (-velPrim a v₀ t) • velShift a m v₀ t) t :=
    ((hAc.neg.rexp.smul hβ).integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := (hA t).exp.smul ((hasDerivAt_const t x).add hI)
  rw [probabilityFlowVelocity_eq ha hv₀ m t]
  refine h.congr_deriv ?_
  have he : Real.exp (velPrim a v₀ t) * Real.exp (-velPrim a v₀ t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [flow, Pi.add_apply, zero_add, smul_smul, he, one_smul]
  module

/-! ### FL-5 for OU with an isotropic Gaussian initial law -/

/-- **FL-5, OU / Gaussian instance (Conditional on the Itô input only).** For `a ≥ 0`,
`v₀ > 0`, `m : Fin d → ℝ`, if the OU law curve `ρ_t = ouKernelPi a t ∘ₘ ⊗ᵢ N(mᵢ, v₀)`
satisfies `WeakFokkerPlanck ρ (-a ·) a`, then the explicit probability-flow transport `Φ`
(`flow`) has the same one-time marginals: `ρ₀.map Φ_t = ρ_t` for every `t ≥ 0`. Every other
hypothesis of `map_flow_eq_of_weakFokkerPlanck_of_affine`, including PDE uniqueness, is
discharged. -/
theorem map_flow_eq_ouLaw_of_weakFokkerPlanck {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀)
    (m : Fin d → ℝ) (hFP : WeakFokkerPlanck (ouLaw a m v₀) (fun _ x => -a • x) a) :
    ∀ t, 0 ≤ t → (initLaw m v₀).map (flow a m v₀ t) = ouLaw a m v₀ t := by
  have hu : Continuous (fun q : ℝ × (Fin d → ℝ) =>
      probabilityFlowVelocity (fun _ x => -a • x) a (density a m v₀) q.1 q.2) := by
    have e : (fun q : ℝ × (Fin d → ℝ) =>
        probabilityFlowVelocity (fun _ x => -a • x) a (density a m v₀) q.1 q.2) =
        fun q => velCoef a v₀ q.1 • q.2 + velShift a m v₀ q.1 :=
      funext fun q => probabilityFlowVelocity_eq ha hv₀ m q.1 q.2
    rw [e]
    have hα : Continuous (velCoef a v₀) :=
      continuous_const.sub (continuous_const.mul (continuous_scoreCoef ha hv₀))
    have hβ : Continuous (velShift a m v₀) :=
      ((continuous_scoreShift ha hv₀ m).const_smul a).neg
    exact ((hα.comp continuous_fst).smul continuous_snd).add (hβ.comp continuous_fst)
  have h := map_flow_eq_of_weakFokkerPlanck_of_affine (ρ := ouLaw a m v₀)
    (p := density a m v₀) (Φ := flow a m v₀) (κ := fun _ => -a) (β := fun _ => 0)
    (σ := scoreCoef a v₀) (τ := scoreShift a m v₀)
    (fun t _ => inferInstance) (fun t ht => ouLaw_eq_withDensity ha hv₀ ht m)
    (fun t _ => contDiff_density a m v₀ t) (fun t _ => density_pos ha hv₀ m t) hu
    (hasDerivAt_flow ha hv₀ m) (measurable_flow a m v₀) (flow_zero a m v₀) hFP
    continuousOn_const continuousOn_const (continuous_scoreCoef ha hv₀).continuousOn
    (continuous_scoreShift ha hv₀ m).continuousOn (fun t _ x => by simp)
    (fun t _ x => score_density ha hv₀ m t x)
  intro t ht
  rw [← h t ht, ouLaw_zero]

/-- **FL-5 for OU with an isotropic Gaussian initial law (Verified, no named hypotheses).**
For `a ≥ 0`, `m : Fin d → ℝ` and `v₀ > 0`, let `ρ₀ = ⊗ᵢ N(mᵢ, v₀)` and let `Φ_t`
(`flow a m v₀ t`) be the flow of the probability-flow ODE `ẏ = -a y - a ∇log p_t(y)`, `p_t` the
OU marginal density.
Then for every `t ≥ 0` the transport law `Φ_t # ρ₀` equals the OU law
`ouKernelPi a t ∘ₘ ρ₀`. Both FL-5 inputs are discharged: the Itô input by
`WeakFokkerPlanckOU.weakFokkerPlanck_ou`, PDE uniqueness by the affine uniqueness theorem.
Only one-time marginals are matched. -/
theorem map_flow_eq_ouLaw {a v₀ : ℝ} (ha : 0 ≤ a) (hv₀ : 0 < v₀) (m : Fin d → ℝ) :
    ∀ t, 0 ≤ t → (initLaw m v₀).map (flow a m v₀ t) = ouKernelPi a t ∘ₘ initLaw m v₀ := by
  have : IsProbabilityMeasure (initLaw m v₀) := by unfold initLaw; infer_instance
  exact map_flow_eq_ouLaw_of_weakFokkerPlanck ha hv₀ m
    (WeakFokkerPlanckOU.weakFokkerPlanck_ou ha (initLaw m v₀))

end FormalizeSampling.NoiseScoreOUUnconditional
