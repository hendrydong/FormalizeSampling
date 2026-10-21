module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Identities.ScoreFlowWeak
public import FormalizeSampling.Flow.ContinuityEquation
public import FormalizeSampling.Flow.KLDecay

/-!
# One-time marginal equality of an SDE law and its probability-flow / PFG transport

Registry ID: **FL-5** (SDE / probability-flow ODE one-time marginal equality, and
its preconditioned form: one-time marginal equality of preconditioned Langevin and the PFG
flow). The verified bridges below integrate **ID-3** (`Identities/ScoreFlowWeak.lean`) along
time, and the flow side reuses **PT-1** (`Flow/ContinuityEquation.lean`).

## Paper statements mapped

* Probability-flow ODE: for `dX = b_t(X) dt + √(2D) dW` and `Ẏ = b_t(Y) - D ∇log p_t(Y)` with
  the same initial law, under regularity and *uniqueness of the weak Fokker–Planck / continuity
  equation*, `Law(X_t) = Law(Y_t) = p_t` for each `t`. The uniqueness input and the weak
  Fokker–Planck equation of the SDE law (the Itô input) are named hypotheses.
* Preconditioned bridge: with `A = H⁻¹` constant SPD, preconditioned Langevin
  `dX = A ∇log p⋆(X) dt + √(2A) dW` and the transport `Ẏ = A (∇log p⋆ - ∇log p_t)(Y)` have the same
  weak equations, hence (under uniqueness) the same **one-time** marginals. This bridge is
  discussed in App. B.7 of the PFG paper, not as a numbered statement; it follows from standard
  Fokker–Planck calculus, and here it is Conditional on two named inputs (the weak
  Fokker–Planck equation of the SDE law and uniqueness) and states one-time marginal equality
  only.

## Conventions

* State space `Fin d → ℝ`, `⬝ᵥ`, `*ᵥ`, `grad`, `laplacian`, `weightedLaplacian` and the state
  score `score p = ∇ₓ log p` from `Foundations/VectorCalculus.lean`.
* Test functions: `TestFunction2 φ := ContDiff ℝ 2 φ ∧ HasCompactSupport φ`.
* **Time half-line.** All weak equations are imposed for times `t ≥ 0`, with the time
  derivative taken within `Ici 0` (`HasDerivWithinAt … (Ici 0) t`): two-sided for `t > 0`,
  right derivative at `t = 0`. This is the natural setting for a process started at time `0`
  (a law on `[0, ∞)` need not extend to negative times). Two-sided `HasDerivAt` at every
  `t : ℝ` implies it (`weakFokkerPlanck_of_hasDerivAt`, `weakContinuity2_of_hasDerivAt`).
* A curve of measures is a map `ρ : ℝ → Measure (Fin d → ℝ)`; only `t ≥ 0` matters.
* `ρ t = volume.withDensity (ofReal ∘ p t)` says that `p t` is a Lebesgue density of `ρ t`.
* The probability-flow velocity is `probabilityFlowVelocity b D p t x = b t x - D • ∇log p_t(x)`;
  the PFG velocity is `klFlowVelocity A sStar p t x = A *ᵥ (s⋆ x - ∇log p_t(x))`, which for
  `A = H⁻¹` is `KLDecay.idealVelocity H (score (p t)) sStar` (`klFlowVelocity_inv_eq`).

## Named inputs (packaged unproved mathematics)

* `WeakFokkerPlanck ρ b D` (resp. `PreconditionedWeakFokkerPlanck ρ A sStar`): the weak
  Fokker–Planck equation, which Itô's formula gives for the law of the SDE. **Itô input**:
  no SDE, Brownian motion or Itô formula is formalized, so this is never proved for an SDE.
* `UniqueWeakContinuity v`: uniqueness, on `t ≥ 0`, of probability-measure solutions of the
  weak continuity equation with velocity `v` and a given initial law. **PDE-uniqueness input**:
  a theorem of PDE theory under Lipschitz-type conditions on `v` (e.g. Ambrosio–Gigli–Savaré,
  *Gradient Flows*, Chapter 8, Section 8.1, uniqueness for Lipschitz velocity fields;
  DiPerna–Lions / Ambrosio theory for weaker regularity), not proved here except for `v = 0`
  (`uniqueWeakContinuity_zero`); affine velocities are covered in
  `Flow/ContinuityUniquenessAffine`, and `C³` velocities with bounded derivative, continuous
  Lipschitz velocities and locally Lipschitz velocities of linear growth in
  `Flow/ContinuityUniquenessLocal`. It is stated on the half-line `t ≥ 0` (see "Time
  half-line").

## Main results

* Relations (Verified): `weakContinuity2_of_weakContinuityEquation` (the PT-1 predicate,
  `C¹_c` tests and all times, implies `WeakContinuity2`, `C²_c` tests and `t ≥ 0`; the converse
  is not claimed), `weakFokkerPlanck_of_hasDerivAt`, `weakContinuity2_of_hasDerivAt`,
  `weakContinuity2_flowLaw`.
* Bridges (Verified, ID-3 integrated along time, no uniqueness):
  `weakContinuity2_of_weakFokkerPlanck`, `weakContinuity2_of_preconditionedWeakFokkerPlanck`.
* Abstract representation step (Conditional on `UniqueWeakContinuity`):
  `map_flow_eq_of_weakContinuity2`.
* **FL-5**, plain Langevin (Conditional): `map_flow_eq_of_weakFokkerPlanck`.
* **FL-5**, preconditioned (Conditional): `map_flow_eq_of_preconditionedWeakFokkerPlanck`
  (symmetric `A`) and `map_flow_eq_of_klFlow` (`A = H⁻¹`, `H` SPD).
* Nonvacuity (Verified): `ext_of_forall_integral_testFunction2_eq` (`C²_c` functions determine
  finite measures on `Fin d → ℝ`), `uniqueWeakContinuity_zero`, the stationary instances
  `weakFokkerPlanck_stationary`, `preconditionedWeakFokkerPlanck_stationary`, the standard
  Gaussian density `stdGaussianDensity` with `isProbabilityMeasure_stdGaussian`, and
  `noiseScore_hypotheses_stationary` / `klFlow_hypotheses_stationary`, which discharge **every**
  hypothesis of FL-5 (including both named inputs) for a stationary density.

## Only one-time marginals

The conclusion `(ρ 0).map (Φ t) = ρ t` is equality of the laws at **one** time `t`. It says
nothing about two-time, finite-dimensional or path laws, which genuinely differ: see
`Counterexamples/MarginalsNotPaths.lean` (CE-01) and `GaussianFlowVsOU.twoTime_flow_ne_ou`, where
the PFG flow and the OU process have equal one-time marginals but different two-time laws.

A one-dimensional special case of the conclusion is obtained **without** either named input by
explicit computation: `GaussianFlowVsOU.map_flow_eq_bind_ouKernel` (target `N(0, 1)`, scalar
preconditioner `a ≥ 0`, Gaussian initial law `N(m₀, v₀)`, an explicit flow, and the OU dynamics
represented by the specific transition kernel `OU.ouKernel a t`, which is a definition). It is
an illustration only, not a discharge of the general hypotheses: it is a statement on `ℝ` about
a Gaussian initial law and that kernel, not an instance of the `ρ`/`p`/`Φ` theorems of this
file, and it proves neither named input for any velocity.

## What is NOT proved here

* No SDE theory: neither `WeakFokkerPlanck` nor `PreconditionedWeakFokkerPlanck` is derived
  from an SDE (Itô's formula is not formalized); the stationary instances are checked directly
  by integration by parts, not from a process.
* PDE uniqueness is not proved in this file (only `v = 0`); `UniqueWeakContinuity` is proved
  elsewhere for affine (`ContinuityUniquenessAffine`) and for `C³` Lipschitz, continuous
  Lipschitz and locally Lipschitz linear-growth (`ContinuityUniquenessLocal`) velocities.
* No existence of the flow `Φ` (no Cauchy–Lipschitz for the probability-flow ODE), no
  existence, positivity or regularity of the Fokker–Planck densities `p t`: all are inputs.
* The flow hypotheses are those of PT-1: `Φ` solves the ODE for **all** `t : ℝ` and the
  velocity is jointly continuous on `ℝ × (Fin d → ℝ)`; a flow defined only for `t ≥ 0` is not
  covered.
* Only constant `D` and constant matrices `A`; state-dependent diffusion is not treated.
* No two-time, finite-dimensional or path-law statement (see above).
-/

@[expose] public section

open MeasureTheory Matrix Set Filter Topology Metric
open scoped Manifold ContDiff

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-! ### Test functions and the named predicates -/

/-- The test-function class of this file: `φ : ℝᵈ → ℝ` is `C²` and has compact support. -/
def TestFunction2 (φ : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 φ ∧ HasCompactSupport φ

/-- **Weak Fokker–Planck equation (named Itô input).** A curve of measures `ρ` satisfies the
weak Fokker–Planck equation of `dX = b_t(X) dt + √(2D) dW` on `t ≥ 0` if for every `C²`
compactly supported `φ` and every `t ≥ 0`,

  `d/dt ∫ φ dρ_t = ∫ (b_t ⬝ ∇φ + D Δφ) dρ_t`,

the derivative taken within `[0, ∞)` (two-sided for `t > 0`, from the right at `t = 0`).
This is what Itô's formula gives for the law `ρ t = Law(X_t)` of the SDE (for `D ≥ 0` and
suitable `b`); it is **not proved here** (no SDE theory) and enters theorems only as a named
hypothesis. The right-hand side is a genuine integral when `b t` is continuous (the integrand
is then continuous with compact support); otherwise Mathlib's junk value `0` may appear. -/
def WeakFokkerPlanck (ρ : ℝ → Measure (Fin d → ℝ)) (b : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (D : ℝ) : Prop :=
  ∀ φ : (Fin d → ℝ) → ℝ, TestFunction2 φ → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => ∫ x, φ x ∂(ρ s))
      (∫ x, (b t x ⬝ᵥ grad φ x + D * laplacian φ x) ∂(ρ t)) (Ici 0) t

/-- **Preconditioned weak Fokker–Planck equation (named Itô input).** The weak Fokker–Planck
equation of preconditioned Langevin dynamics `dX = A s⋆(X) dt + √(2A) dW` on `t ≥ 0`: for
every `C²` compactly supported `φ` and `t ≥ 0`,

  `d/dt ∫ φ dρ_t = ∫ ((A s⋆) ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) dρ_t`

(derivative within `[0, ∞)`). Itô's formula gives this for the law of the SDE when `A` is
positive semidefinite; it is **not proved here**. -/
def PreconditionedWeakFokkerPlanck (ρ : ℝ → Measure (Fin d → ℝ))
    (A : Matrix (Fin d) (Fin d) ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∀ φ : (Fin d → ℝ) → ℝ, TestFunction2 φ → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => ∫ x, φ x ∂(ρ s))
      (∫ x, ((A *ᵥ sStar x) ⬝ᵥ grad φ x + weightedLaplacian A φ x) ∂(ρ t)) (Ici 0) t

/-- **Weak continuity equation with `C²_c` test functions on `t ≥ 0`.** `ρ` solves
`∂ₜ ρ + div (ρ v) = 0` weakly if for every `C²` compactly supported `φ` and `t ≥ 0`,
`d/dt ∫ φ dρ_t = ∫ v_t ⬝ ∇φ dρ_t` (derivative within `[0, ∞)`). Compared with
`ContinuityEquation.WeakContinuityEquation` (PT-1: `C¹_c` tests, two-sided derivative at
every `t : ℝ`) it uses fewer test functions and fewer times, so it is implied by it
(`weakContinuity2_of_weakContinuityEquation`); the converse is not claimed. -/
def WeakContinuity2 (ρ : ℝ → Measure (Fin d → ℝ)) (v : ℝ → (Fin d → ℝ) → Fin d → ℝ) :
    Prop :=
  ∀ φ : (Fin d → ℝ) → ℝ, TestFunction2 φ → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => ∫ x, φ x ∂(ρ s)) (∫ x, v t x ⬝ᵥ grad φ x ∂(ρ t)) (Ici 0) t

/-- **Uniqueness for the weak continuity equation (named PDE-uniqueness input).** For the
velocity `v`, any two curves `ρ, ρ'` of probability measures (on `t ≥ 0`) that both satisfy
`WeakContinuity2` with velocity `v` and have the same time-`0` law agree at every `t ≥ 0`.

This is a theorem of PDE theory under Lipschitz-type conditions on `v`, e.g. for `v` jointly
continuous, bounded, and Lipschitz in `x` locally uniformly in `t`: see Ambrosio–Gigli–Savaré,
*Gradient Flows in Metric Spaces and in the Space of Probability Measures*, Chapter 8,
Section 8.1 (the continuity equation in `ℝᵈ`; uniqueness for Lipschitz velocity fields, a
solution being the pushforward of its initial law by the flow of `v`), with weaker conditions in
DiPerna–Lions / Ambrosio theory. The exact hypotheses of those results, and the passage from
their distributional formulation to the pointwise-in-time `WeakContinuity2` used here, are not
formalized. **It is NOT proved here** except for `v = 0` (`uniqueWeakContinuity_zero`); it
enters FL-5 as a named hypothesis. Affine velocities `a(t) A x + b(t)` are handled in
`Flow/ContinuityUniquenessAffine` (`uniqueWeakContinuity_of_matrix_affine`); `C³` Lipschitz,
continuous Lipschitz and locally Lipschitz linear-growth velocities in
`Flow/ContinuityUniquenessLocal`.

Half-line convention: curves are constrained only for `t ≥ 0`, and `WeakContinuity2` takes the
time derivative within `Ici 0` (`HasDerivWithinAt`, one-sided at `t = 0`). The reason is that
the intended curves are laws `Law(X_t)` of processes started at time `0`, which need not be
defined, or satisfy any equation, for `t < 0`; the initial law is imposed at the endpoint
`t = 0`. Two-sided `HasDerivAt` at every `t : ℝ` would exclude such curves (it implies the
half-line form: `weakContinuity2_of_hasDerivAt`). -/
def UniqueWeakContinuity (v : ℝ → (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∀ ρ ρ' : ℝ → Measure (Fin d → ℝ),
    (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) → (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) →
    WeakContinuity2 ρ v → WeakContinuity2 ρ' v → ρ 0 = ρ' 0 → ∀ t, 0 ≤ t → ρ t = ρ' t

/-- The **probability-flow velocity** `u_t(x) = b_t(x) - D ∇log p_t(x)` of the SDE
`dX = b_t(X) dt + √(2D) dW` whose marginal densities are `p t`. -/
noncomputable def probabilityFlowVelocity (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (D : ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  b t x - D • score (p t) x

/-- The **PFG velocity** `u_t(x) = A (s⋆(x) - ∇log p_t(x))` with constant matrix `A` (the ideal
PFG direction when `A = H⁻¹`, see `klFlowVelocity_inv_eq`). -/
noncomputable def klFlowVelocity (A : Matrix (Fin d) (Fin d) ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  A *ᵥ (sStar x - score (p t) x)

/-- With `A = H⁻¹`, the PFG velocity at time `t` is the ideal PFG velocity
`KLDecay.idealVelocity H (score (p t)) sStar = H⁻¹ (s⋆ - ∇log p_t)` of
`Flow/KLDecay.lean` (definitional equality). -/
theorem klFlowVelocity_inv_eq (H : Matrix (Fin d) (Fin d) ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) :
    klFlowVelocity H⁻¹ sStar p t = KLDecay.idealVelocity H (score (p t)) sStar :=
  rfl

/-! ### Relations between the predicates -/

/-- **Relation to PT-1.** `ContinuityEquation.WeakContinuityEquation ρ v` (all `C¹` compactly
supported tests, two-sided derivative at every `t : ℝ`, integrand `∇φ ⬝ v_t`) implies
`WeakContinuity2 ρ v` (`C²` compactly supported tests, `t ≥ 0`, derivative within `[0, ∞)`,
integrand `v_t ⬝ ∇φ`). The converse is not claimed. -/
theorem weakContinuity2_of_weakContinuityEquation {ρ : ℝ → Measure (Fin d → ℝ)}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} (h : ContinuityEquation.WeakContinuityEquation ρ v) :
    WeakContinuity2 ρ v := by
  intro φ hφ t _
  have h1 := h φ (hφ.1.of_le (by norm_num)) hφ.2 t
  simp_rw [dotProduct_comm (v t _)]
  exact h1.hasDerivWithinAt

/-- A two-sided derivative at every time implies `WeakContinuity2`: if for every `C²_c` test
`φ` and every `t : ℝ`, `d/dt ∫ φ dρ_t = ∫ v_t ⬝ ∇φ dρ_t` (as `HasDerivAt`), then
`WeakContinuity2 ρ v`. -/
theorem weakContinuity2_of_hasDerivAt {ρ : ℝ → Measure (Fin d → ℝ)}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (h : ∀ φ : (Fin d → ℝ) → ℝ, TestFunction2 φ → ∀ t : ℝ,
      HasDerivAt (fun s => ∫ x, φ x ∂(ρ s)) (∫ x, v t x ⬝ᵥ grad φ x ∂(ρ t)) t) :
    WeakContinuity2 ρ v :=
  fun φ hφ t _ => (h φ hφ t).hasDerivWithinAt

/-- A two-sided derivative at every time implies `WeakFokkerPlanck`: if for every `C²_c` test
`φ` and every `t : ℝ`, `d/dt ∫ φ dρ_t = ∫ (b_t ⬝ ∇φ + D Δφ) dρ_t` (as `HasDerivAt`), then
`WeakFokkerPlanck ρ b D`. -/
theorem weakFokkerPlanck_of_hasDerivAt {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ}
    (h : ∀ φ : (Fin d → ℝ) → ℝ, TestFunction2 φ → ∀ t : ℝ,
      HasDerivAt (fun s => ∫ x, φ x ∂(ρ s))
        (∫ x, (b t x ⬝ᵥ grad φ x + D * laplacian φ x) ∂(ρ t)) t) :
    WeakFokkerPlanck ρ b D :=
  fun φ hφ t _ => (h φ hφ t).hasDerivWithinAt

/-- **Pushforward laws of a flow solve `WeakContinuity2` (PT-1, `C²_c` form).** If `v` is
jointly continuous, `Φ` is a flow of `v` (`∂ₜ Φ t x = v t (Φ t x)` for all `t, x`) with
a.e.-measurable time slices and `ρ₀` is finite, then `t ↦ ρ₀.map (Φ t)` satisfies
`WeakContinuity2` with velocity `v`. -/
theorem weakContinuity2_flowLaw {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : Continuous (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (v t (Φ t x)) t)
    {ρ₀ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ₀] (hΦm : ∀ t, AEMeasurable (Φ t) ρ₀) :
    WeakContinuity2 (ContinuityEquation.flowLaw ρ₀ Φ) v :=
  weakContinuity2_of_weakContinuityEquation
    (ContinuityEquation.weakContinuityEquation_flowLaw hv hΦ hΦm)

/-! ### Helpers -/

/-- Integrals against `volume.withDensity (ofReal ∘ p)` for a measurable nonnegative `p`:
`∫ g d(p · Leb) = ∫ g(x) p(x) dx` (for every `g`; both sides use the same integrability). -/
theorem integral_withDensity_ofReal {p : (Fin d → ℝ) → ℝ} (hp : Measurable p)
    (hpos : ∀ x, 0 ≤ p x) (g : (Fin d → ℝ) → ℝ) :
    ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (p x)) = ∫ x, g x * p x := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hpos x), smul_eq_mul, mul_comm]

/-! ### Verified bridges: ID-3 integrated along time -/

/-- **Weak Fokker–Planck ⇒ weak continuity equation for the probability-flow velocity
(ID-3 along time, Verified).** Let `ρ t = p_t · Leb` for `t ≥ 0`, where each `p t` (`t ≥ 0`)
is `C¹` and everywhere positive and each `b t` (`t ≥ 0`) is continuous. If `ρ` satisfies
`WeakFokkerPlanck ρ b D`, then it satisfies `WeakContinuity2` with velocity
`u_t = b_t - D ∇log p_t` (`probabilityFlowVelocity b D p`): at each time the two
right-hand sides are equal by the weak generator identity
`ScoreFlowWeak.integral_generator_eq_score_flow_generator`. No uniqueness is used, no
normalisation of `p t` is needed, and `D` is an arbitrary real. -/
theorem weakContinuity2_of_weakFokkerPlanck {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hb : ∀ t, 0 ≤ t → Continuous (b t)) (hFP : WeakFokkerPlanck ρ b D) :
    WeakContinuity2 ρ (probabilityFlowVelocity b D p) := by
  intro φ hφ t ht
  have hval : ∫ x, (b t x ⬝ᵥ grad φ x + D * laplacian φ x) ∂(ρ t) =
      ∫ x, probabilityFlowVelocity b D p t x ⬝ᵥ grad φ x ∂(ρ t) := by
    have hm : Measurable (p t) := (hp t ht).continuous.measurable
    have hnn : ∀ x, 0 ≤ p t x := fun x => (hpos t ht x).le
    rw [hρ t ht, integral_withDensity_ofReal hm hnn, integral_withDensity_ofReal hm hnn]
    exact ScoreFlowWeak.integral_generator_eq_score_flow_generator D (hb t ht) (hp t ht)
      (hpos t ht) hφ.1 hφ.2
  rw [← hval]
  exact hFP φ hφ t ht

/-- **Preconditioned weak Fokker–Planck ⇒ weak continuity equation for the PFG velocity
(ID-3 along time, Verified).** Let `A` be a symmetric constant matrix (`Aᵀ = A`), `s⋆` a
continuous field, and `ρ t = p_t · Leb` for `t ≥ 0` with each `p t` (`t ≥ 0`) `C¹` and
everywhere positive. If `PreconditionedWeakFokkerPlanck ρ A s⋆` holds, then `ρ` satisfies
`WeakContinuity2` with the PFG velocity `u_t = A (s⋆ - ∇log p_t)` (`klFlowVelocity A sStar p`),
by `ScoreFlowWeak.integral_preconditioned_generator_eq_klFlow_generator` at each time. No
uniqueness is used. -/
theorem weakContinuity2_of_preconditionedWeakFokkerPlanck {ρ : ℝ → Measure (Fin d → ℝ)}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) {sStar : (Fin d → ℝ) → Fin d → ℝ}
    {p : ℝ → (Fin d → ℝ) → ℝ} (hsStar : Continuous sStar)
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hFP : PreconditionedWeakFokkerPlanck ρ A sStar) :
    WeakContinuity2 ρ (klFlowVelocity A sStar p) := by
  intro φ hφ t ht
  have hval : ∫ x, ((A *ᵥ sStar x) ⬝ᵥ grad φ x + weightedLaplacian A φ x) ∂(ρ t) =
      ∫ x, klFlowVelocity A sStar p t x ⬝ᵥ grad φ x ∂(ρ t) := by
    have hm : Measurable (p t) := (hp t ht).continuous.measurable
    have hnn : ∀ x, 0 ≤ p t x := fun x => (hpos t ht x).le
    rw [hρ t ht, integral_withDensity_ofReal hm hnn, integral_withDensity_ofReal hm hnn]
    exact ScoreFlowWeak.integral_preconditioned_generator_eq_klFlow_generator hA hsStar (hp t ht)
      (hpos t ht) hφ.1 hφ.2
  rw [← hval]
  exact hFP φ hφ t ht

/-! ### Conditional one-time marginal equality -/

/-- **Uniqueness turns a weak solution into a flow pushforward (Conditional).** Let `ρ` be a
curve of probability measures on `t ≥ 0` satisfying `WeakContinuity2 ρ u`, where `u` is jointly
continuous, and let `Φ` be a flow of `u` (`∂ₜ Φ t x = u t (Φ t x)` for all `t : ℝ` and `x`)
with measurable time slices and `Φ 0 = id`. Under the named PDE-uniqueness hypothesis
`UniqueWeakContinuity u`, `(ρ 0).map (Φ t) = ρ t` for every `t ≥ 0`: the pushforward curve
solves the same equation (PT-1) with the same initial law.

Only **one-time** marginals are matched: for each fixed `t ≥ 0`, the law at time `t`.
Two-time, finite-dimensional and path laws differ in general (`Counterexamples.MarginalsNotPaths`,
`GaussianFlowVsOU.twoTime_flow_ne_ou`). `GaussianFlowVsOU.map_flow_eq_bind_ouKernel` obtains a
one-time
conclusion of this kind without any uniqueness hypothesis in a 1D special case (target
`N(0, 1)`, scalar preconditioner, Gaussian initial law, the specific OU kernel
`OU.ouKernel a t`); it is an illustration, not a discharge of the general hypotheses. -/
theorem map_flow_eq_of_weakContinuity2 {ρ : ℝ → Measure (Fin d → ℝ)}
    {u : ℝ → (Fin d → ℝ) → Fin d → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakContinuity2 ρ u)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => u q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (u t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (huniq : UniqueWeakContinuity u) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t := by
  have : IsProbabilityMeasure (ρ 0) := hprob 0 le_rfl
  have hflow : WeakContinuity2 (ContinuityEquation.flowLaw (ρ 0) Φ) u :=
    weakContinuity2_flowLaw hu hΦ fun t => (hΦm t).aemeasurable
  have hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ContinuityEquation.flowLaw (ρ 0) Φ t) :=
    fun t _ => (Measure.isProbabilityMeasure_map_iff (hΦm t).aemeasurable).2 inferInstance
  exact huniq _ ρ hprob' hprob hflow hρ (ContinuityEquation.flowLaw_zero hΦ0 (ρ 0))

/-- **SDE / probability-flow one-time marginal equality (FL-5, Conditional).**
Data: a curve `ρ` of probability measures (`ρ t` plays the role of `Law(X_t)` for
`dX = b_t(X) dt + √(2D) dW`), with `ρ t = p_t · Leb` for `t ≥ 0`, each `p t` (`t ≥ 0`) `C¹` and
everywhere positive; the probability-flow velocity `u_t = b_t - D ∇log p_t`
(`probabilityFlowVelocity b D p`) jointly continuous; a flow `Φ` of `u`
(`∂ₜ Φ t x = u_t(Φ t x)` for all `t : ℝ`, `x`), with measurable `Φ t` and `Φ 0 = id`.

Named inputs: `WeakFokkerPlanck ρ b D` (**Itô input**, what Itô's formula gives for the SDE
law; not proved here) and `UniqueWeakContinuity u` (**PDE-uniqueness input**; not proved here).

Conclusion: for every `t ≥ 0`, `(ρ 0).map (Φ t) = ρ t`, i.e.
`Law(Y_t) = Law(X_t) = p_t · Leb` for `Y_t = Φ t Y_0`, `Y_0 ∼ ρ 0`.

Only **one-time** marginals are matched: for each fixed `t ≥ 0`, the law at time `t`.
Two-time, finite-dimensional and path laws differ in general (`Counterexamples.MarginalsNotPaths`,
`GaussianFlowVsOU.twoTime_flow_ne_ou`). `GaussianFlowVsOU.map_flow_eq_bind_ouKernel` obtains the
same
one-time conclusion without the two named inputs in a 1D special case (target `N(0, 1)`, scalar
preconditioner, Gaussian initial law, the specific OU kernel `OU.ouKernel a t`); it is an
illustration, not a discharge of the general hypotheses. All hypotheses are jointly satisfiable
(`noiseScore_hypotheses_stationary`). -/
theorem map_flow_eq_of_weakFokkerPlanck {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : WeakFokkerPlanck ρ b D)
    (huniq : UniqueWeakContinuity (probabilityFlowVelocity b D p)) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t := by
  have hb : ∀ t, 0 ≤ t → Continuous (b t) := by
    intro t ht
    have hut : Continuous (probabilityFlowVelocity b D p t) :=
      hu.comp (continuous_const.prodMk continuous_id)
    have heq : b t = fun x => probabilityFlowVelocity b D p t x + D • score (p t) x :=
      funext fun x => by simp [probabilityFlowVelocity]
    rw [heq]
    exact hut.add ((continuous_score (hp t ht) (hpos t ht)).const_smul D)
  exact map_flow_eq_of_weakContinuity2 hprob
    (weakContinuity2_of_weakFokkerPlanck hρ hp hpos hb hFP) hu hΦ hΦm hΦ0 huniq

/-- **Preconditioned Langevin / PFG-flow one-time marginal equality (FL-5, Conditional),
symmetric `A`.** As `map_flow_eq_of_weakFokkerPlanck`, for `dX = A s⋆(X) dt + √(2A) dW` with a
constant symmetric matrix `A` (`Aᵀ = A`) and a continuous target score field `s⋆`: if
`ρ t = p_t · Leb` (`t ≥ 0`, `p t` `C¹` and positive) is a curve of probability measures solving
the named Itô input `PreconditionedWeakFokkerPlanck ρ A s⋆`, the PFG velocity
`u_t = A (s⋆ - ∇log p_t)` (`klFlowVelocity A sStar p`) is jointly continuous, `Φ` is a flow of
`u` with measurable slices and `Φ 0 = id`, and the named PDE-uniqueness input
`UniqueWeakContinuity u` holds, then `(ρ 0).map (Φ t) = ρ t` for every `t ≥ 0`.

Only **one-time** marginals are matched: for each fixed `t ≥ 0`, the law at time `t`.
Two-time, finite-dimensional and path laws differ in general (`Counterexamples.MarginalsNotPaths`,
`GaussianFlowVsOU.twoTime_flow_ne_ou`). `GaussianFlowVsOU.map_flow_eq_bind_ouKernel` obtains the
same
one-time conclusion without the two named inputs in a 1D special case (target `N(0, 1)`, scalar
preconditioner, Gaussian initial law, the specific OU kernel `OU.ouKernel a t`); it is an
illustration, not a discharge of the general hypotheses. -/
theorem map_flow_eq_of_preconditionedWeakFokkerPlanck {ρ : ℝ → Measure (Fin d → ℝ)}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) {sStar : (Fin d → ℝ) → Fin d → ℝ}
    {p : ℝ → (Fin d → ℝ) → ℝ} {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hsStar : Continuous sStar)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => klFlowVelocity A sStar p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (klFlowVelocity A sStar p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : PreconditionedWeakFokkerPlanck ρ A sStar)
    (huniq : UniqueWeakContinuity (klFlowVelocity A sStar p)) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_weakContinuity2 hprob
    (weakContinuity2_of_preconditionedWeakFokkerPlanck hA hsStar hρ hp hpos hFP) hu hΦ hΦm hΦ0
    huniq

/-- **Preconditioned Langevin / PFG-flow one-time marginal equality (FL-5, Conditional),
`A = H⁻¹`.** For a constant symmetric positive-definite preconditioner `H` (`H.PosDef`) and
`A = H⁻¹`: preconditioned Langevin `dX = H⁻¹ s⋆(X) dt + √(2 H⁻¹) dW` (law `ρ t = p_t · Leb`,
named Itô input `PreconditionedWeakFokkerPlanck ρ H⁻¹ s⋆`) and the ideal PFG transport
`Ẏ = H⁻¹ (s⋆ - ∇log p_t)(Y)` (flow `Φ`, `Φ 0 = id`) started from the same law have the same
law at every time `t ≥ 0`, `(ρ 0).map (Φ t) = ρ t`, provided `UniqueWeakContinuity` holds for
the PFG velocity (named PDE-uniqueness input) and the regularity hypotheses of
`map_flow_eq_of_preconditionedWeakFokkerPlanck` hold.

Only **one-time** marginals are matched: for each fixed `t ≥ 0`, the law at time `t`.
Two-time, finite-dimensional and path laws differ in general (`Counterexamples.MarginalsNotPaths`,
`GaussianFlowVsOU.twoTime_flow_ne_ou`). `GaussianFlowVsOU.map_flow_eq_bind_ouKernel` obtains the
same
one-time conclusion without the two named inputs in a 1D special case (target `N(0, 1)`, scalar
preconditioner, Gaussian initial law, the specific OU kernel `OU.ouKernel a t`); it is an
illustration, not a discharge of the general hypotheses. All hypotheses are jointly satisfiable
(`klFlow_hypotheses_stationary`). -/
theorem map_flow_eq_of_klFlow {ρ : ℝ → Measure (Fin d → ℝ)} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {sStar : (Fin d → ℝ) → Fin d → ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hsStar : Continuous sStar)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => klFlowVelocity H⁻¹ sStar p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (klFlowVelocity H⁻¹ sStar p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : PreconditionedWeakFokkerPlanck ρ H⁻¹ sStar)
    (huniq : UniqueWeakContinuity (klFlowVelocity H⁻¹ sStar p)) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_preconditionedWeakFokkerPlanck
    (SPD.transpose_eq_of_posDef (SPD.inv_posDef hH)) hsStar hprob hρ hp hpos hu hΦ hΦm hΦ0
    hFP huniq

/-! ### Smooth compactly supported functions determine finite measures -/

/-- Smooth Urysohn: for a compact `K ⊆ ℝᵈ` and `r > 0` there is a smooth compactly supported
`f` with values in `[0, 1]`, equal to `1` on `K` and to `0` outside the closed `r`-thickening
of `K`. -/
theorem exists_smooth_one_on_compact {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, f x = 1) ∧ (∀ x ∉ cthickening r K, f x = 0) := by
  have hsub : K ⊆ interior (cthickening r K) :=
    (self_subset_thickening hr K).trans (thickening_subset_interior_cthickening r K)
  obtain ⟨f, h1, h0, hI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Fin d → ℝ) hK.isClosed hsub (n := (⊤ : ℕ∞))
  have hf : ContDiff ℝ ∞ f := contMDiff_iff_contDiff.1 f.contMDiff
  exact ⟨f, hf, HasCompactSupport.intro hK.cthickening h0, hI,
    fun x hx => h1.self_of_nhdsSet x hx, h0⟩

/-- If two finite measures on `ℝᵈ` give equal integrals to every smooth compactly supported
function, then `μ K ≤ ν K` for every compact `K`. -/
theorem measure_le_of_forall_integral_smooth_eq {μ ν : Measure (Fin d → ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ x, φ x ∂ν)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) : μ K ≤ ν K := by
  have key : ∀ r > (0 : ℝ), μ K ≤ ν (cthickening r K) := by
    intro r hr
    obtain ⟨f, hf, hfc, hI, h1, h0⟩ := exists_smooth_one_on_compact hK hr
    have hfi : ∀ (m : Measure (Fin d → ℝ)) [IsFiniteMeasure m], Integrable f m := fun m _ =>
      hf.continuous.integrable_of_hasCompactSupport hfc
    have hnn : ∀ (m : Measure (Fin d → ℝ)), 0 ≤ᵐ[m] f := fun m =>
      Eventually.of_forall fun x => (hI x).1
    calc μ K = ∫⁻ x, K.indicator 1 x ∂μ := (lintegral_indicator_one hK.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ K
          · simp [hx, h1 x hx]
          · simp [hx]
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi μ) (hnn μ),
            ← ofReal_integral_eq_lintegral_ofReal (hfi ν) (hnn ν), h f hf hfc]
      _ ≤ ∫⁻ x, (cthickening r K).indicator 1 x ∂ν := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ cthickening r K
          · simp only [hx, indicator_of_mem, Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (hI x).2
          · simp [hx, h0 x hx]
      _ = ν (cthickening r K) := lintegral_indicator_one isClosed_cthickening.measurableSet
  have ht : Tendsto (fun r => ν (cthickening r K)) (𝓝[>] 0) (𝓝 (ν K)) :=
    (tendsto_measure_cthickening_of_isCompact hK).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun r hr => key r hr)

/-- **Smooth compactly supported functions determine finite measures on `ℝᵈ`.** If `μ, ν`
are finite Borel measures on `Fin d → ℝ` with `∫ φ dμ = ∫ φ dν` for every smooth (`C^∞`)
compactly supported `φ`, then `μ = ν`. (Compact sets via smooth Urysohn functions, closed sets
by exhaustion with closed balls, then the π-system of closed sets.) -/
theorem ext_of_forall_integral_smooth_eq {μ ν : Measure (Fin d → ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : μ = ν := by
  have hK : ∀ K, IsCompact K → μ K = ν K := fun K hK =>
    le_antisymm (measure_le_of_forall_integral_smooth_eq h hK)
      (measure_le_of_forall_integral_smooth_eq (fun φ hφ hφc => (h φ hφ hφc).symm) hK)
  have hF : ∀ F : Set (Fin d → ℝ), IsClosed F → μ F = ν F := by
    intro F hF
    have hmono : Monotone (fun n : ℕ => F ∩ closedBall 0 n) := fun m n hmn =>
      inter_subset_inter_right _ (closedBall_subset_closedBall (by exact_mod_cast hmn))
    have hU : (⋃ n : ℕ, F ∩ closedBall 0 n) = F := by
      rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
    have hμ := tendsto_measure_iUnion_atTop (μ := μ) hmono
    have hν := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hU] at hμ hν
    have heq : (μ ∘ fun n : ℕ => F ∩ closedBall 0 n) = (ν ∘ fun n : ℕ => F ∩ closedBall 0 n) :=
      funext fun n => hK _ ((isCompact_closedBall 0 n).inter_left hF)
    rw [heq] at hμ
    exact tendsto_nhds_unique hμ hν
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun F hF' => hF F hF')
    (hF univ isClosed_univ)
  rw [BorelSpace.measurable_eq (α := Fin d → ℝ), borel_eq_generateFrom_isClosed]

/-! ### Nonvacuity: `C²_c` functions determine finite measures -/

/-- For a compact `K ⊆ ℝᵈ` and `r > 0` there is a `C²` (indeed smooth) compactly supported
`f` with values in `[0, 1]`, equal to `1` on `K` and to `0` outside the closed
`r`-thickening of `K` (smooth Urysohn lemma). -/
theorem exists_testFunction2_one_on_compact {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ f : (Fin d → ℝ) → ℝ, TestFunction2 f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, f x = 1) ∧ (∀ x ∉ cthickening r K, f x = 0) := by
  obtain ⟨f, hf, hfc, hI, h1, h0⟩ := exists_smooth_one_on_compact hK hr
  exact ⟨f, ⟨hf.of_le (by norm_cast), hfc⟩, hI, h1, h0⟩

/-- If two finite measures on `ℝᵈ` give equal integrals to every `C²_c` function, then
`μ K ≤ ν K` for every compact `K` (a smooth compactly supported function is `C²_c`). -/
theorem measure_le_of_forall_integral_testFunction2_eq {μ ν : Measure (Fin d → ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ, TestFunction2 φ → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) : μ K ≤ ν K :=
  measure_le_of_forall_integral_smooth_eq (fun φ hφ hφc => h φ ⟨hφ.of_le (by norm_cast), hφc⟩) hK

/-- **`C²_c` test functions determine finite measures on `ℝᵈ`.** If `μ, ν` are finite Borel
measures on `Fin d → ℝ` with `∫ φ dμ = ∫ φ dν` for every `C²` compactly supported `φ`, then
`μ = ν` (a special case of `ext_of_forall_integral_smooth_eq`). -/
theorem ext_of_forall_integral_testFunction2_eq {μ ν : Measure (Fin d → ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ, TestFunction2 φ → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : μ = ν :=
  ext_of_forall_integral_smooth_eq fun φ hφ hφc => h φ ⟨hφ.of_le (by norm_cast), hφc⟩

/-! ### Nonvacuity: uniqueness for the zero velocity -/

/-- Under `WeakContinuity2 ρ 0` (zero velocity), `∫ φ dρ_t = ∫ φ dρ_0` for every `C²_c` test
`φ` and every `t ≥ 0`. -/
theorem integral_eq_of_weakContinuity2_zero {ρ : ℝ → Measure (Fin d → ℝ)}
    (hρ : WeakContinuity2 ρ fun _ _ => 0) {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ)
    {t : ℝ} (ht : 0 ≤ t) : ∫ x, φ x ∂(ρ t) = ∫ x, φ x ∂(ρ 0) := by
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => ∫ x, φ x ∂(ρ s)) 0 (Ici 0) s := by
    intro s hs
    simpa using hρ φ hφ s hs
  refine constant_of_has_deriv_right_zero (f := fun s => ∫ x, φ x ∂(ρ s)) (a := 0) (b := t)
    ?_ ?_ t ⟨ht, le_rfl⟩
  · intro s hs
    exact ((hd s hs.1).continuousWithinAt).mono Icc_subset_Ici_self
  · intro s hs
    exact (hd s hs.1).mono (Ici_subset_Ici.2 hs.1)

/-- **Nonvacuity of `UniqueWeakContinuity`: the zero velocity (Verified).** Two curves of
probability measures that both solve the weak continuity equation with `v = 0` (in the
`WeakContinuity2` sense) and agree at time `0` agree at every `t ≥ 0`: each `∫ φ dρ_t` with
`φ ∈ C²_c` is constant on `[0, ∞)`, and `C²_c` functions determine finite measures
(`ext_of_forall_integral_testFunction2_eq`). -/
theorem uniqueWeakContinuity_zero : UniqueWeakContinuity (d := d) fun _ _ => 0 := by
  intro ρ ρ' hρ hρ' hc hc' h0 t ht
  have := hρ t ht
  have := hρ' t ht
  refine ext_of_forall_integral_testFunction2_eq fun φ hφ => ?_
  rw [integral_eq_of_weakContinuity2_zero hc hφ ht, integral_eq_of_weakContinuity2_zero hc' hφ ht,
    h0]

/-! ### Nonvacuity: stationary instances of the named inputs -/

/-- **Stationary instance of the Itô input (Verified).** For any `D : ℝ` and any `C¹`
everywhere-positive `p`, the constant curve `ρ t = p · Leb` satisfies `WeakFokkerPlanck` with
the drift `b_t = D ∇log p` (overdamped Langevin targeting `p` when `D > 0`): the time
derivative is `0` and `∫ (D ∇log p ⬝ ∇φ + D Δφ) p = 0` by the ID-3 identity. -/
theorem weakFokkerPlanck_stationary (D : ℝ) {p : (Fin d → ℝ) → ℝ} (hp : ContDiff ℝ 1 p)
    (hpos : ∀ x, 0 < p x) :
    WeakFokkerPlanck (fun _ => volume.withDensity fun x => ENNReal.ofReal (p x))
      (fun _ x => D • score p x) D := by
  intro φ hφ t _
  have hval : ∫ x, (D • score p x ⬝ᵥ grad φ x + D * laplacian φ x)
      ∂(volume.withDensity fun x => ENNReal.ofReal (p x)) = 0 := by
    rw [integral_withDensity_ofReal hp.continuous.measurable fun x => (hpos x).le,
      ScoreFlowWeak.integral_generator_eq_score_flow_generator D (b := fun x => D • score p x)
        ((continuous_score hp hpos).const_smul D) hp hpos hφ.1 hφ.2]
    simp
  rw [hval]
  exact hasDerivWithinAt_const t _ _

/-- **Stationary instance of the preconditioned Itô input (Verified).** For a symmetric
constant matrix `A` and any `C¹` everywhere-positive `p`, the constant curve `ρ t = p · Leb`
satisfies `PreconditionedWeakFokkerPlanck` with target score `s⋆ = ∇log p`: by the ID-3
identity, `∫ ((A ∇log p) ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ (A (∇log p - ∇log p)) ⬝ ∇φ p = 0`. -/
theorem preconditionedWeakFokkerPlanck_stationary {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : Aᵀ = A) {p : (Fin d → ℝ) → ℝ} (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x) :
    PreconditionedWeakFokkerPlanck (fun _ => volume.withDensity fun x => ENNReal.ofReal (p x))
      A (score p) := by
  intro φ hφ t _
  have hval : ∫ x, ((A *ᵥ score p x) ⬝ᵥ grad φ x + weightedLaplacian A φ x)
      ∂(volume.withDensity fun x => ENNReal.ofReal (p x)) = 0 := by
    rw [integral_withDensity_ofReal hp.continuous.measurable fun x => (hpos x).le,
      ScoreFlowWeak.integral_preconditioned_generator_eq_klFlow_generator hA
        (continuous_score hp hpos) hp hpos hφ.1 hφ.2]
    simp
  rw [hval]
  exact hasDerivWithinAt_const t _ _

/-- The standard Gaussian density on `ℝᵈ`, `p(x) = ∏ᵢ N(0, 1)(xᵢ)` (Mathlib's
`gaussianPDFReal 0 1`, variance `1`). -/
noncomputable def stdGaussianDensity (x : Fin d → ℝ) : ℝ :=
  ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)

/-- The standard Gaussian density on `ℝᵈ` is `C¹`. -/
theorem contDiff_stdGaussianDensity : ContDiff ℝ 1 (stdGaussianDensity (d := d)) :=
  contDiff_prod fun i _ =>
    ScoreFlowWeak.contDiff_gaussianPDFReal_std.comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) i)

/-- The standard Gaussian density on `ℝᵈ` is everywhere positive. -/
theorem stdGaussianDensity_pos (x : Fin d → ℝ) : 0 < stdGaussianDensity x :=
  Finset.prod_pos fun i _ => ProbabilityTheory.gaussianPDFReal_pos 0 1 (x i) one_ne_zero

/-- The measure with the standard Gaussian density on `ℝᵈ` is a probability measure:
`∫ ∏ᵢ N(0, 1)(xᵢ) dx = ∏ᵢ ∫ N(0, 1) = 1` (Fubini on `Fin d → ℝ`). -/
theorem isProbabilityMeasure_stdGaussian :
    IsProbabilityMeasure
      (volume.withDensity fun x : Fin d → ℝ => ENNReal.ofReal (stdGaussianDensity x)) := by
  have hint : Integrable (stdGaussianDensity (d := d)) := by
    have h := Integrable.fintype_prod (ι := Fin d) (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ => ProbabilityTheory.gaussianPDFReal 0 1)
      fun _ => ProbabilityTheory.integrable_gaussianPDFReal 0 1
    rw [← volume_pi] at h
    exact h
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => (stdGaussianDensity_pos x).le)]
  have h1 : ∫ x, stdGaussianDensity (d := d) x = 1 := by
    unfold stdGaussianDensity
    rw [integral_fintype_prod_volume_eq_prod (fun _ => ProbabilityTheory.gaussianPDFReal 0 1)]
    simp [ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero]
  rw [h1, ENNReal.ofReal_one]

/-! ### Nonvacuity: every hypothesis of FL-5 at once -/

/-- **All hypotheses of FL-5 are jointly satisfiable (Verified).** Take `p` the standard
Gaussian density on `ℝᵈ` (`stdGaussianDensity`), any `D : ℝ`, the stationary curve
`ρ t = p · Leb`, the Langevin drift `b_t = D ∇log p`, the identity flow `Φ t = id`. Then every
hypothesis of `map_flow_eq_of_weakFokkerPlanck` holds, including the two named inputs
`WeakFokkerPlanck ρ b D` and `UniqueWeakContinuity u` (here `u = b - D ∇log p = 0`). The
conclusion of FL-5 is trivial for this instance; the point is that the hypotheses are
consistent. -/
theorem noiseScore_hypotheses_stationary (D : ℝ) :
    let p : ℝ → (Fin d → ℝ) → ℝ := fun _ => stdGaussianDensity
    let ρ : ℝ → Measure (Fin d → ℝ) := fun t => volume.withDensity fun x => ENNReal.ofReal (p t x)
    let b : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ x => D • score stdGaussianDensity x
    let Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ x => x
    (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) ∧
      (∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x)) ∧
      (∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) ∧ (∀ t, 0 ≤ t → ∀ x, 0 < p t x) ∧
      Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2) ∧
      (∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t) ∧
      (∀ t, Measurable (Φ t)) ∧ (∀ x, Φ 0 x = x) ∧
      WeakFokkerPlanck ρ b D ∧ UniqueWeakContinuity (probabilityFlowVelocity b D p) := by
  intro p ρ b Φ
  have hu : probabilityFlowVelocity b D p = fun _ _ => 0 := by
    funext t x
    simp [probabilityFlowVelocity, b, p]
  refine ⟨fun _ _ => isProbabilityMeasure_stdGaussian, fun _ _ => rfl,
    fun _ _ => contDiff_stdGaussianDensity, fun _ _ => stdGaussianDensity_pos, ?_, ?_,
    fun _ => measurable_id, fun _ => rfl,
    weakFokkerPlanck_stationary D contDiff_stdGaussianDensity stdGaussianDensity_pos, ?_⟩
  · rw [hu]
    exact continuous_const
  · intro t x
    rw [hu]
    exact hasDerivAt_const t x
  · rw [hu]
    exact uniqueWeakContinuity_zero

/-- **All hypotheses of FL-5 (`A = H⁻¹`) are jointly satisfiable (Verified).** For any
positive-definite `H`, take `p` the standard Gaussian density on `ℝᵈ`, target score
`s⋆ = ∇log p`, the stationary curve `ρ t = p · Leb` and the identity flow. Then every
hypothesis of `map_flow_eq_of_klFlow` holds, including the named inputs
`PreconditionedWeakFokkerPlanck ρ H⁻¹ s⋆` and `UniqueWeakContinuity u` (here
`u = H⁻¹ (s⋆ - ∇log p) = 0`). The conclusion is trivial for this instance; the point is
consistency of the hypotheses. -/
theorem klFlow_hypotheses_stationary {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    let p : ℝ → (Fin d → ℝ) → ℝ := fun _ => stdGaussianDensity
    let ρ : ℝ → Measure (Fin d → ℝ) := fun t => volume.withDensity fun x => ENNReal.ofReal (p t x)
    let sStar : (Fin d → ℝ) → Fin d → ℝ := score stdGaussianDensity
    let Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ x => x
    Continuous sStar ∧ (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) ∧
      (∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x)) ∧
      (∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) ∧ (∀ t, 0 ≤ t → ∀ x, 0 < p t x) ∧
      Continuous (fun q : ℝ × (Fin d → ℝ) => klFlowVelocity H⁻¹ sStar p q.1 q.2) ∧
      (∀ t x, HasDerivAt (fun s => Φ s x) (klFlowVelocity H⁻¹ sStar p t (Φ t x)) t) ∧
      (∀ t, Measurable (Φ t)) ∧ (∀ x, Φ 0 x = x) ∧
      PreconditionedWeakFokkerPlanck ρ H⁻¹ sStar ∧
      UniqueWeakContinuity (klFlowVelocity H⁻¹ sStar p) := by
  intro p ρ sStar Φ
  have hu : klFlowVelocity H⁻¹ sStar p = fun _ _ => 0 := by
    funext t x
    simp [klFlowVelocity, sStar, p]
  refine ⟨continuous_score contDiff_stdGaussianDensity stdGaussianDensity_pos,
    fun _ _ => isProbabilityMeasure_stdGaussian, fun _ _ => rfl,
    fun _ _ => contDiff_stdGaussianDensity,
    fun _ _ => stdGaussianDensity_pos, ?_, ?_, fun _ => measurable_id, fun _ => rfl,
    preconditionedWeakFokkerPlanck_stationary (SPD.transpose_eq_of_posDef (SPD.inv_posDef hH))
      contDiff_stdGaussianDensity stdGaussianDensity_pos, ?_⟩
  · rw [hu]
    exact continuous_const
  · intro t x
    rw [hu]
    exact hasDerivAt_const t x
  · rw [hu]
    exact uniqueWeakContinuity_zero

end NoiseScore
end FormalizeSampling
