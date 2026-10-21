module

public import Mathlib.Topology.Separation.CompletelyRegular
public import FormalizeSampling.Flow.ContinuityEquation

/-!
# Finite particles and explicit Euler steps for particle gradient flows

Registry ID: **PT-1**, finite-particle layer (part (c)) and explicit-Euler discretisation layer.
The population layer (pushforward of a
general law by a flow) is `FormalizeSampling/Flow/ContinuityEquation.lean`.

## Setting and conventions

Particles are `x : Fin n → (Fin d → ℝ)`; the empirical measure is
`empirical x = (n : ℝ≥0∞)⁻¹ • ∑ i, dirac (x i)`, i.e. `p̂ₙ = (1/n) ∑ᵢ δ_{xᵢ}`. It is a
probability measure when `n > 0` (`isProbabilityMeasure_empirical`).

**Velocity fields are inputs, not derived from the particles.** An atomic measure such as
`p̂ₙ` has no Lebesgue density (`empirical_ne_withDensity`, `not_absolutelyContinuous_empirical`,
for `d ≥ 1`), so `∇ log p̂ₙ` is meaningless and a PFG / score velocity `v` cannot be computed
as the state score of the empirical measure; it must be supplied from outside. In this file
the velocity `v` (continuous time) or `f k` (discrete step `k`) is an arbitrary vector field
given as an input — e.g. a trained network `f_{θ_k}`, a kernel-smoothed Stein direction, or an
exact population drift — and nothing is claimed about how well it approximates the ideal
population velocity.

## Main results

* `map_empirical`: for *any* map `T` (no measurability needed, singletons being measurable),
  `(empirical x).map T = empirical (T ∘ x)`.
* `integral_empirical`: `∫ f d(empirical x) = (1/n) ∑ᵢ f (xᵢ)` for any `f`.
* `map_flow_empirical`, `hasDerivAt_integral_empirical_flow`,
  `weakContinuityEquation_empirical_flow` (PT-1 (c)): the law of `n` particles moved by a
  flow `Φ` of a jointly continuous `v` is the empirical measure of the moved particles, and it
  satisfies the same weak continuity equation as the population law; `hasDerivAt_average_flow`
  is the explicit particle-average form.
* Discretisation layer: `eulerStep η f y = y + η • f y`, the time-inhomogeneous iterates
  `eulerIterates η f k` (step `k` uses the field `f k`, as in `x^{k+1} = x^k + η f_{θ_k}(x^k)`),
  `eulerIterates_const` (constant field = ordinary iterate), and the exact law identities
  `map_eulerStep_empirical`, `empirical_eulerParticles_succ`, `empirical_eulerParticles`:
  one Euler step pushes the empirical measure forward to the empirical measure of the updated
  particles, exactly, and so do `k` steps.

## What is NOT proved here

* **No error analysis of any kind**: no finite-particle (`p̂ₙ` vs population law) error, no
  propagation of chaos / mean-field limit, no time-discretisation error of the Euler scheme
  against the continuous flow, no stochastic-optimisation, function-approximation or
  preconditioner-estimation error, and no convergence of the particle system.
* No statement that the input velocity is a PFG direction for the particles.
* Existence of the continuous-time particle flow `Φ` is assumed, not derived from `v`.
-/

@[expose] public section

open MeasureTheory Filter Matrix Set
open scoped ENNReal

namespace FormalizeSampling
namespace Particles

open ContinuityEquation

variable {d n : ℕ}

/-! ### Empirical measures -/

/-- The empirical measure `p̂ₙ = (1/n) ∑ᵢ δ_{xᵢ}` of `n` particles `x : Fin n → (Fin d → ℝ)`,
written `(n : ℝ≥0∞)⁻¹ • ∑ i, dirac (x i)`. It is a probability measure when `n > 0`. -/
noncomputable def empirical (x : Fin n → (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The mass the empirical measure gives to an arbitrary set `s` (measurable or not):
`p̂ₙ(s) = (1/n) · #{i | xᵢ ∈ s}`, written as `(n)⁻¹ * ∑ᵢ 1_s(xᵢ)`. -/
theorem empirical_apply (x : Fin n → (Fin d → ℝ)) (s : Set (Fin d → ℝ)) :
    empirical x s = (n : ℝ≥0∞)⁻¹ * ∑ i, s.indicator 1 (x i) := by
  simp [empirical, Measure.dirac_apply]

/-- For `n > 0` particles, the empirical measure is a probability measure. -/
theorem isProbabilityMeasure_empirical (hn : 0 < n) (x : Fin n → (Fin d → ℝ)) :
    IsProbabilityMeasure (empirical x) := by
  constructor
  rw [empirical_apply]
  simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

/-- Every function `T` on the state space is a.e.-measurable for an empirical measure (it is
a.e. equal to a measurable function, singletons being measurable). -/
theorem aemeasurable_empirical {β : Type*} [MeasurableSpace β] (T : (Fin d → ℝ) → β)
    (x : Fin n → (Fin d → ℝ)) : AEMeasurable T (empirical x) := by
  unfold empirical
  refine AEMeasurable.smul_measure ?_ _
  rw [← Measure.sum_fintype]
  exact AEMeasurable.sum_measure fun i => aemeasurable_dirac

/-- **Pushforward of an empirical measure.** For any map `T` (no measurability assumption),
`T₊ p̂ₙ = (1/n) ∑ᵢ δ_{T xᵢ}`, i.e. `(empirical x).map T = empirical (fun i => T (x i))`. -/
theorem map_empirical (T : (Fin d → ℝ) → Fin d → ℝ) (x : Fin n → (Fin d → ℝ)) :
    (empirical x).map T = empirical (fun i => T (x i)) := by
  ext s hs
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_empirical T x) hs, empirical_apply,
    empirical_apply]
  congr 1

/-- **Integral against an empirical measure.** For any `f : (Fin d → ℝ) → ℝ`,
`∫ f dp̂ₙ = (1/n) ∑ᵢ f (xᵢ)`. -/
theorem integral_empirical (f : (Fin d → ℝ) → ℝ) (x : Fin n → (Fin d → ℝ)) :
    ∫ y, f y ∂(empirical x) = (n : ℝ)⁻¹ * ∑ i, f (x i) := by
  rw [empirical, integral_smul_measure, integral_finsetSum_measure
    (fun i _ => integrable_dirac enorm_lt_top)]
  simp [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **No Lebesgue density.** For `n > 0` particles in dimension `d ≥ 1`, the empirical
measure is not absolutely continuous with respect to Lebesgue measure: it charges the
Lebesgue-null singleton `{x₀}`. Hence a score `∇ log p̂ₙ` of the particle law does not exist. -/
theorem not_absolutelyContinuous_empirical [NeZero d] (hn : 0 < n)
    (x : Fin n → (Fin d → ℝ)) : ¬ empirical x ≪ (volume : Measure (Fin d → ℝ)) := by
  intro h
  have h0 := h (measure_singleton (x ⟨0, hn⟩))
  rw [empirical_apply] at h0
  refine mul_ne_zero (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)) ?_ h0
  intro hsum
  have := (Finset.sum_eq_zero_iff.1 hsum) ⟨0, hn⟩ (Finset.mem_univ _)
  simp at this

/-- **No Lebesgue density, density form.** For `n > 0` particles in dimension `d ≥ 1`, there
is no density `p : (Fin d → ℝ) → ℝ≥0∞` with `p̂ₙ = volume.withDensity p`. So a PFG or
score-based velocity must be supplied from outside as an input; it cannot be `∇ log` of the
empirical measure's density. -/
theorem empirical_ne_withDensity [NeZero d] (hn : 0 < n) (x : Fin n → (Fin d → ℝ))
    (p : (Fin d → ℝ) → ℝ≥0∞) : empirical x ≠ (volume : Measure (Fin d → ℝ)).withDensity p := by
  intro h
  exact not_absolutelyContinuous_empirical hn x (h ▸ withDensity_absolutelyContinuous _ p)

/-! ### Continuous-time particle flow -/

/-- **Particles moved by a flow (PT-1 (c), law identity).** If each particle is moved by
the map `Φ t`, the pushforward of the initial empirical measure is the empirical measure of
the moved particles: `(empirical x).map (Φ t) = empirical (fun i => Φ t (x i))`. No
measurability of `Φ t` is needed. -/
theorem map_flow_empirical (Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ) (x : Fin n → (Fin d → ℝ))
    (t : ℝ) : (empirical x).map (Φ t) = empirical (fun i => Φ t (x i)) :=
  map_empirical (Φ t) x

/-- **Weak continuity equation for finitely many particles (PT-1 (c)).** Let `v` be a
jointly continuous velocity field (an input) and `Φ` a flow of `v`
(`∂ₜ Φ t y = v t (Φ t y)` for all `t, y`; no measurability is needed here). For `n > 0`
particles `x` and every `C¹` compactly supported test function `φ`,
`d/dt ∫ φ dp̂ₙ(t) = ∫ ∇φ(y) ⬝ᵥ v t y dp̂ₙ(t)(y)`, where `p̂ₙ(t) = empirical (Φ t ∘ x)`.
This is a corollary of `ContinuityEquation.hasDerivAt_integral_flowLaw` with `ρ₀ = p̂ₙ`. -/
theorem hasDerivAt_integral_empirical_flow
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t y, HasDerivAt (fun s => Φ s y) (v t (Φ t y)) t)
    (hn : 0 < n) (x : Fin n → (Fin d → ℝ))
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun s => ∫ y, φ y ∂(empirical (fun i => Φ s (x i))))
      (∫ y, grad φ y ⬝ᵥ v t y ∂(empirical (fun i => Φ t (x i)))) t := by
  have := isProbabilityMeasure_empirical hn x
  have h := hasDerivAt_integral_flowLaw hv hΦ (ρ₀ := empirical x)
    (fun s => aemeasurable_empirical (Φ s) x) hφ hφc t
  simpa only [flowLaw, map_empirical] using h

/-- Under the hypotheses of `hasDerivAt_integral_empirical_flow` (jointly continuous `v`,
flow `Φ` of `v`, `n > 0`), the particle law `t ↦ empirical (fun i => Φ t (x i))` satisfies
`ContinuityEquation.WeakContinuityEquation` for the velocity `v`. -/
theorem weakContinuityEquation_empirical_flow
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t y, HasDerivAt (fun s => Φ s y) (v t (Φ t y)) t)
    (hn : 0 < n) (x : Fin n → (Fin d → ℝ)) :
    WeakContinuityEquation (fun t => empirical (fun i => Φ t (x i))) v :=
  fun _ hφ hφc t => hasDerivAt_integral_empirical_flow hv hΦ hn x hφ hφc t

/-- **Particle-average form.** Under the hypotheses of `hasDerivAt_integral_empirical_flow`,
`d/dt (1/n) ∑ᵢ φ(Φ t xᵢ) = (1/n) ∑ᵢ ∇φ(Φ t xᵢ) ⬝ᵥ v t (Φ t xᵢ)`. -/
theorem hasDerivAt_average_flow
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t y, HasDerivAt (fun s => Φ s y) (v t (Φ t y)) t)
    (hn : 0 < n) (x : Fin n → (Fin d → ℝ))
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun s => (n : ℝ)⁻¹ * ∑ i, φ (Φ s (x i)))
      ((n : ℝ)⁻¹ * ∑ i, grad φ (Φ t (x i)) ⬝ᵥ v t (Φ t (x i))) t := by
  simpa only [integral_empirical] using hasDerivAt_integral_empirical_flow hv hΦ hn x hφ hφc t

/-! ### Discretisation layer: explicit Euler steps -/

/-- One explicit Euler step with step size `η` along the vector field `f`:
`eulerStep η f y = y + η • f y`. -/
noncomputable def eulerStep (η : ℝ) (f : (Fin d → ℝ) → Fin d → ℝ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  y + η • f y

/-- Time-inhomogeneous Euler iterates: `eulerIterates η f 0 = id` and
`eulerIterates η f (k + 1) = eulerStep η (f k) ∘ eulerIterates η f k`, i.e. the scheme
`y^{k+1} = y^k + η f_k(y^k)` where `f k` is the (given) field at step `k`. -/
noncomputable def eulerIterates (η : ℝ) (f : ℕ → (Fin d → ℝ) → Fin d → ℝ) :
    ℕ → (Fin d → ℝ) → Fin d → ℝ
  | 0 => id
  | k + 1 => eulerStep η (f k) ∘ eulerIterates η f k

/-- Zero Euler steps do nothing: `eulerIterates η f 0 y = y`. -/
@[simp] theorem eulerIterates_zero (η : ℝ) (f : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (y : Fin d → ℝ) : eulerIterates η f 0 y = y :=
  rfl

/-- The recursion of the Euler scheme:
`eulerIterates η f (k + 1) y = y_k + η • f k y_k` with `y_k = eulerIterates η f k y`. -/
theorem eulerIterates_succ_apply (η : ℝ) (f : ℕ → (Fin d → ℝ) → Fin d → ℝ) (k : ℕ)
    (y : Fin d → ℝ) :
    eulerIterates η f (k + 1) y = eulerIterates η f k y + η • f k (eulerIterates η f k y) :=
  rfl

/-- With a step-independent field `f`, the Euler iterates are the ordinary iterates of one
Euler step: `eulerIterates η (fun _ => f) k = (eulerStep η f)^[k]`. -/
theorem eulerIterates_const (η : ℝ) (f : (Fin d → ℝ) → Fin d → ℝ) (k : ℕ) :
    eulerIterates η (fun _ => f) k = (eulerStep η f)^[k] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ', ← ih]; rfl

/-- The particle positions after `k` Euler steps, each particle moved by the same scheme:
`eulerParticles η f x k i = eulerIterates η f k (x i)`. -/
noncomputable def eulerParticles (η : ℝ) (f : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin n → (Fin d → ℝ)) (k : ℕ) : Fin n → (Fin d → ℝ) :=
  fun i => eulerIterates η f k (x i)

/-- **One Euler step on the empirical measure (exact identity).** For any field `f` (no
measurability needed), pushing `p̂ₙ` forward by one Euler step gives the empirical measure of
the updated particles: `(empirical x).map (eulerStep η f) = empirical (eulerStep η f ∘ x)`. -/
theorem map_eulerStep_empirical (η : ℝ) (f : (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin n → (Fin d → ℝ)) :
    (empirical x).map (eulerStep η f) = empirical (fun i => eulerStep η f (x i)) :=
  map_empirical _ x

/-- **Particle update = law update, one step.** The empirical measure of the particles after
step `k + 1` is the pushforward by the `k`-th Euler step `y ↦ y + η • f k y` of the empirical
measure after step `k`. -/
theorem empirical_eulerParticles_succ (η : ℝ) (f : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin n → (Fin d → ℝ)) (k : ℕ) :
    empirical (eulerParticles η f x (k + 1)) =
      (empirical (eulerParticles η f x k)).map (eulerStep η (f k)) := by
  rw [map_eulerStep_empirical]
  rfl

/-- **Particle update = law update, `k` steps.** The empirical measure of the particles after
`k` Euler steps is the pushforward of the initial empirical measure by the `k`-step Euler map:
`empirical (eulerParticles η f x k) = (empirical x).map (eulerIterates η f k)`. -/
theorem empirical_eulerParticles (η : ℝ) (f : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin n → (Fin d → ℝ)) (k : ℕ) :
    empirical (eulerParticles η f x k) = (empirical x).map (eulerIterates η f k) :=
  (map_empirical _ x).symm

end Particles
end FormalizeSampling
