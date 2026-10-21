module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Pushforward laws of a flow satisfy the weak continuity equation

Registry ID: **PT-1** (pushforward and weak continuity equation), population layer: a transport
flow moves a law along a velocity field. The finite-particle and discretisation layers are in
`FormalizeSampling/Samplers/Particles.lean`.

## Setting and conventions

The state space is `Fin d → ℝ` with its Borel σ-algebra. We are given

* a time-dependent velocity field `v : ℝ → (Fin d → ℝ) → Fin d → ℝ` that is *jointly*
  continuous, `Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2)`;
* a family of maps `Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ` whose trajectories solve the ODE
  `∂ₜ Φ t x = v t (Φ t x)` at every time `t` and every starting point `x`
  (`HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t`), with each `Φ t` (a.e.-)measurable;
* a finite initial measure `ρ₀` (e.g. a probability law).

The law at time `t` is the pushforward `flowLaw ρ₀ Φ t = ρ₀.map (Φ t)`; it is the law of
`Φ t X₀` when `X₀ ∼ ρ₀`. Test functions are `C¹` with compact support; `grad` is the Fréchet
gradient from `FormalizeSampling.Foundations.VectorCalculus`.

## Main results

* `hasDerivAt_integral_flowLaw` (PT-1 (a)): for every `C¹_c` test function `φ` and every
  time `t`,
  `d/dt ∫ φ d(ρ t) = ∫ ∇φ(x) ⬝ᵥ v t x d(ρ t)(x)`,
  a genuine (two-sided, classical) time derivative. This is the weak form of
  `∂ₜ ρ + div (ρ v) = 0`. The proof differentiates `∫ φ (Φ s x) dρ₀(x)` under the integral
  sign, dominating `|∇φ(z) ⬝ᵥ v s z|` by its maximum over the compact set
  `[t - 1, t + 1] × tsupport φ`.
* `weakContinuityEquation_flowLaw`: the same, packaged with the predicate
  `WeakContinuityEquation`.
* `continuous_integral_grad_dotProduct_flowLaw`: the right-hand side is continuous in time.
* `integral_flowLaw_sub_eq_intervalIntegral`, `integral_flowLaw_sub_initial` (PT-1 (b)):
  the integrated form
  `∫ φ d(ρ b) - ∫ φ d(ρ a) = ∫ s in a..b, ∫ ∇φ ⬝ᵥ v s d(ρ s)`.
* `weakContinuityEquation_translation`: a concrete instance (constant velocity, translation
  flow) showing the hypotheses are satisfiable by a non-trivial flow.

## What is NOT proved here

* **No PDE uniqueness.** We only show that the pushforward curve is *a* weak solution; we do
  not show that weak solutions of the continuity equation are unique, nor that any other curve
  of measures solving it equals `flowLaw ρ₀ Φ`.
* **No flow existence.** The flow `Φ` is an input: we do not derive it from `v` (no
  Cauchy–Lipschitz / Picard–Lindelöf), and we use neither the group property
  `Φ (t + s) = Φ t ∘ Φ s` nor invertibility of `Φ t`. The integrated form with `ρ₀` on the
  left (`integral_flowLaw_sub_initial`) additionally assumes `Φ 0 = id`.
* **No strong (density-level) equation.** Nothing is said about Lebesgue densities of
  `ρ t` or about `∂ₜ p + div (p v) = 0` pointwise; no Liouville / log-density formula.
* The test-function class is `C¹` with compact support in space only; the equation is not
  stated in the space-time distributional sense with test functions of `(t, x)`.
* Only finite initial measures are treated.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix Set Metric

namespace FormalizeSampling
namespace ContinuityEquation

variable {d : ℕ}

/-- The law at time `t` of the state transported by the flow `Φ` from the initial law `ρ₀`:
the pushforward measure `ρ t = (Φ t)₊ ρ₀ = ρ₀.map (Φ t)`. (It is the zero measure if `Φ t` is
not a.e.-measurable, by Mathlib's convention; every theorem below assumes measurability.) -/
noncomputable def flowLaw (ρ₀ : Measure (Fin d → ℝ)) (Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (t : ℝ) : Measure (Fin d → ℝ) :=
  ρ₀.map (Φ t)

/-- A curve of measures `ρ : ℝ → Measure (Fin d → ℝ)` satisfies the **weak continuity
equation** `∂ₜ ρ + div (ρ v) = 0` (weak in space, classical in time) if for every `C¹`
compactly supported test function `φ` and every time `t`, the map `s ↦ ∫ φ d(ρ s)` has
derivative `∫ ∇φ(x) ⬝ᵥ v t x d(ρ t)(x)` at `t`. This is a definition of the notion, not an
assumption of any theorem in this file. -/
def WeakContinuityEquation (ρ : ℝ → Measure (Fin d → ℝ))
    (v : ℝ → (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ t : ℝ,
    HasDerivAt (fun s => ∫ x, φ x ∂(ρ s)) (∫ x, grad φ x ⬝ᵥ v t x ∂(ρ t)) t

/-- If `φ` is `C¹`, its coordinate gradient `∇φ` is continuous. -/
theorem continuous_grad {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (grad φ) := by
  have h := hφ.continuous_fderiv one_ne_zero
  exact continuous_pi fun i => h.clm_apply continuous_const

/-- The gradient of `φ` vanishes outside the topological support of `φ`:
`z ∉ tsupport φ → ∇φ(z) = 0`. -/
theorem grad_eq_zero_of_notMem_tsupport {φ : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (hz : z ∉ tsupport φ) : grad φ z = 0 := by
  have : fderiv ℝ φ z = 0 := by
    by_contra h
    exact hz (support_fderiv_subset ℝ h)
  ext i
  simp [grad, partialDeriv, this]

/-- Uniform bound on `|∇φ(z) ⬝ᵥ v s z|` for `s ∈ [t - 1, t + 1]` and all `z`. -/
private lemma exists_bound_grad_dotProduct
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc (t - 1) (t + 1), ∀ z, |grad φ z ⬝ᵥ v s z| ≤ C := by
  have hG : Continuous (fun q : ℝ × (Fin d → ℝ) => grad φ q.2 ⬝ᵥ v q.1 q.2) :=
    Continuous.dotProduct ((continuous_grad hφ).comp continuous_snd) hv
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hφc).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s hs z => ?_⟩
  by_cases hz : z ∈ tsupport φ
  · exact (by simpa using hC (s, z) ⟨hs, hz⟩ : |grad φ z ⬝ᵥ v s z| ≤ C).trans (le_max_left _ _)
  · simp [grad_eq_zero_of_notMem_tsupport hz]

private lemma aestronglyMeasurable_comp {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {ρ₀ : Measure (Fin d → ℝ)} (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀)
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) (s : ℝ) :
    AEStronglyMeasurable (fun x => g (Φ s x)) ρ₀ :=
  hg.comp_aestronglyMeasurable (hΦm s).aestronglyMeasurable

private lemma continuous_grad_dotProduct
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    Continuous (fun z => grad φ z ⬝ᵥ v s z) :=
  Continuous.dotProduct (continuous_grad hφ)
    (hv.comp (continuous_const.prodMk continuous_id))

/-- The integrand `x ↦ ∇φ(x) ⬝ᵥ v t x` of the continuity equation is integrable against
`ρ t = ρ₀.map (Φ t)`, for `φ` a `C¹` function with compact support, `v` jointly continuous,
`ρ₀` finite and `Φ t` a.e.-measurable. (So the right-hand side of the weak continuity equation
is a genuine integral, not Mathlib's junk value `0`.) -/
theorem integrable_grad_dotProduct_flowLaw
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀]
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    Integrable (fun x => grad φ x ⬝ᵥ v t x) (flowLaw ρ₀ Φ t) := by
  obtain ⟨C, -, hC⟩ := exists_bound_grad_dotProduct hv hφ hφc t
  have ht : t ∈ Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have : IsFiniteMeasure (flowLaw ρ₀ Φ t) := by unfold flowLaw; infer_instance
  exact Integrable.of_bound (continuous_grad_dotProduct hv hφ t).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC t ht x)

/-- **Weak continuity equation for a pushforward flow (PT-1 (a)).**
Let `v` be a jointly continuous time-dependent velocity field on `Fin d → ℝ`, and let `Φ` be a
flow of `v`: for all `t, x`, `s ↦ Φ s x` has derivative `v t (Φ t x)` at `s = t`, and each
`Φ t` is a.e.-measurable for the finite measure `ρ₀` (e.g. `Φ t` measurable). Put
`ρ t = ρ₀.map (Φ t)`. Then for every `C¹` compactly supported `φ` and every `t`,
`d/dt ∫ φ d(ρ t) = ∫ ∇φ(x) ⬝ᵥ v t x d(ρ t)(x)`. No PDE uniqueness is used or claimed. -/
theorem hasDerivAt_integral_flowLaw
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t)
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀] (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, φ x ∂(flowLaw ρ₀ Φ s))
      (∫ x, grad φ x ⬝ᵥ v t x ∂(flowLaw ρ₀ Φ t)) t := by
  obtain ⟨C, -, hC⟩ := exists_bound_grad_dotProduct hv hφ hφc t
  have hball : ball t 1 ⊆ Icc (t - 1) (t + 1) := by
    intro s hs
    rw [mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ₀) (x₀ := t)
    (F := fun s x => φ (Φ s x)) (F' := fun s x => grad φ (Φ s x) ⬝ᵥ v s (Φ s x))
    (bound := fun _ => C) (ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun s => aestronglyMeasurable_comp hΦm hφ.continuous s)
    (Integrable.of_bound (aestronglyMeasurable_comp hΦm hφ.continuous t) M
      (Eventually.of_forall fun x => hM _))
    (aestronglyMeasurable_comp hΦm (continuous_grad_dotProduct hv hφ t) t)
    (Eventually.of_forall fun x s hs => by
      simpa [Real.norm_eq_abs] using hC s (hball hs) (Φ s x))
    (integrable_const C)
    (Eventually.of_forall fun x s _ => by
      have h := ((hφ.differentiable one_ne_zero) (Φ s x)).hasFDerivAt.comp_hasDerivAt s (hΦ s x)
      rw [fderiv_apply_eq_grad_dotProduct] at h
      exact h)
  have hmap : ∀ s, ∫ x, φ x ∂(flowLaw ρ₀ Φ s) = ∫ x, φ (Φ s x) ∂ρ₀ := fun s =>
    integral_map (hΦm s) hφ.continuous.aestronglyMeasurable
  have hmap' : ∫ x, grad φ x ⬝ᵥ v t x ∂(flowLaw ρ₀ Φ t) =
      ∫ x, grad φ (Φ t x) ⬝ᵥ v t (Φ t x) ∂ρ₀ :=
    integral_map (hΦm t) (continuous_grad_dotProduct hv hφ t).aestronglyMeasurable
  simp_rw [hmap, hmap']
  exact key.2

/-- Under the hypotheses of `hasDerivAt_integral_flowLaw` (jointly continuous `v`, flow `Φ`
of `v` with a.e.-measurable time slices, finite `ρ₀`), the pushforward curve
`t ↦ ρ₀.map (Φ t)` satisfies `WeakContinuityEquation` for the velocity `v`. -/
theorem weakContinuityEquation_flowLaw
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t)
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀] (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀) :
    WeakContinuityEquation (flowLaw ρ₀ Φ) v :=
  fun _ hφ hφc t => hasDerivAt_integral_flowLaw hv hΦ hΦm hφ hφc t

/-- Under the hypotheses of `hasDerivAt_integral_flowLaw`, the right-hand side of the weak
continuity equation, `s ↦ ∫ ∇φ(x) ⬝ᵥ v s x d(ρ s)(x)`, is continuous in `s` (so, together
with `hasDerivAt_integral_flowLaw`, `t ↦ ∫ φ d(ρ t)` is `C¹` in time). -/
theorem continuous_integral_grad_dotProduct_flowLaw
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t)
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀] (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    Continuous (fun s => ∫ x, grad φ x ⬝ᵥ v s x ∂(flowLaw ρ₀ Φ s)) := by
  have hmap : ∀ s, ∫ x, grad φ x ⬝ᵥ v s x ∂(flowLaw ρ₀ Φ s) =
      ∫ x, grad φ (Φ s x) ⬝ᵥ v s (Φ s x) ∂ρ₀ := fun s =>
    integral_map (hΦm s) (continuous_grad_dotProduct hv hφ s).aestronglyMeasurable
  simp_rw [hmap]
  have hG : Continuous (fun q : ℝ × (Fin d → ℝ) => grad φ q.2 ⬝ᵥ v q.1 q.2) :=
    Continuous.dotProduct ((continuous_grad hφ).comp continuous_snd) hv
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨C, -, hC⟩ := exists_bound_grad_dotProduct hv hφ hφc t
  have hIcc : Icc (t - 1) (t + 1) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  refine continuousAt_of_dominated (bound := fun _ => C)
    (Eventually.of_forall fun s =>
      aestronglyMeasurable_comp hΦm (continuous_grad_dotProduct hv hφ s) s)
    (eventually_of_mem hIcc fun s hs => Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC s hs (Φ s x))
    (integrable_const C)
    (Eventually.of_forall fun x => ?_)
  have hΦx : Continuous (fun s => Φ s x) :=
    continuous_iff_continuousAt.2 fun s => (hΦ s x).continuousAt
  exact (hG.comp (continuous_id.prodMk hΦx)).continuousAt

/-- **Integrated weak continuity equation (PT-1 (b)).** Under the hypotheses of
`hasDerivAt_integral_flowLaw`, for all times `a, b`,
`∫ φ d(ρ b) - ∫ φ d(ρ a) = ∫ s in a..b, ∫ ∇φ(x) ⬝ᵥ v s x d(ρ s)(x)`,
where `ρ s = ρ₀.map (Φ s)` and `φ` is `C¹` with compact support. -/
theorem integral_flowLaw_sub_eq_intervalIntegral
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t)
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀] (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (a b : ℝ) :
    ∫ x, φ x ∂(flowLaw ρ₀ Φ b) - ∫ x, φ x ∂(flowLaw ρ₀ Φ a) =
      ∫ s in a..b, ∫ x, grad φ x ⬝ᵥ v s x ∂(flowLaw ρ₀ Φ s) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_integral_flowLaw hv hΦ hΦm hφ hφc s)
    ((continuous_integral_grad_dotProduct_flowLaw hv hΦ hΦm hφ hφc).intervalIntegrable
      a b)).symm

/-- If the flow starts at the identity, `Φ 0 x = x` for all `x`, then `ρ 0 = ρ₀`. -/
theorem flowLaw_zero {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hΦ0 : ∀ x, Φ 0 x = x)
    (ρ₀ : Measure (Fin d → ℝ)) : flowLaw ρ₀ Φ 0 = ρ₀ := by
  have : Φ 0 = id := funext hΦ0
  simp [flowLaw, this]

/-- **Integrated weak continuity equation from the initial law (PT-1 (b)).** Under the
hypotheses of `hasDerivAt_integral_flowLaw` and additionally `Φ 0 = id`, for every `t`,
`∫ φ d(ρ t) - ∫ φ dρ₀ = ∫ s in 0..t, ∫ ∇φ(x) ⬝ᵥ v s x d(ρ s)(x)`. -/
theorem integral_flowLaw_sub_initial
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t) (hΦ0 : ∀ x, Φ 0 x = x)
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀] (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    ∫ x, φ x ∂(flowLaw ρ₀ Φ t) - ∫ x, φ x ∂ρ₀ =
      ∫ s in (0)..t, ∫ x, grad φ x ⬝ᵥ v s x ∂(flowLaw ρ₀ Φ s) := by
  rw [← integral_flowLaw_sub_eq_intervalIntegral hv hΦ hΦm hφ hφc 0 t, flowLaw_zero hΦ0 ρ₀]

/-- **Example: translation flow.** For a constant velocity `c`, the translation flow
`Φ t x = x + t • c` satisfies all hypotheses (jointly continuous velocity, ODE, measurable
slices), so for every finite `ρ₀` the translated laws `ρ₀.map (· + t • c)` satisfy the weak
continuity equation with velocity `v t x = c`. This shows the hypotheses of
`weakContinuityEquation_flowLaw` are satisfiable by a non-stationary flow. -/
theorem weakContinuityEquation_translation (c : Fin d → ℝ) (ρ₀ : Measure (Fin d → ℝ))
    [IsFiniteMeasure ρ₀] :
    WeakContinuityEquation (flowLaw ρ₀ (fun t x => x + t • c)) (fun _ _ => c) := by
  refine weakContinuityEquation_flowLaw continuous_const (fun t x => ?_)
    (fun t => (continuous_id.add continuous_const).measurable.aemeasurable)
  simpa using ((hasDerivAt_id t).smul_const c).const_add x

end ContinuityEquation
end FormalizeSampling
