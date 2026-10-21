module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import FormalizeSampling.Flow.NoiseScoreEquivalence

/-!
# Uniqueness for the weak continuity equation with affine velocity fields

Status: **Verified.** Discharges the named PDE-uniqueness input
`NoiseScore.UniqueWeakContinuity v` of FL-5 (`Flow/NoiseScoreEquivalence.lean`) for the class of
velocities that are, on `t ≥ 0`, affine in the state with a fixed linear part up to a scalar
time factor:

  `v_t(x) = a(t) • (A x) + b(t)`,  `a : ℝ → ℝ`, `b : ℝ → ℝᵈ` continuous on `[0, ∞)`,
  `A` a constant `d × d` matrix (or continuous linear map `L`).

This contains `v_t(x) = a(t) x + b(t)` (`A = 1`, scalar time-dependent coefficient) and
`v_t(x) = A x + b(t)` (`a ≡ 1`, constant matrix). For such `v` every solution is moreover
identified: `ρ_T = (X_{0→T})_# ρ_0` with the explicit flow map `X` of `ẋ = v_t(x)`.

## Method (duality)

Fix `T ≥ 0` and a smooth compactly supported `φ`. With the explicit flow map `X_{s→T}` of `v`
(`affineFlow`: `X_{s→T}(x) = e^{∫ₛᵀ a} x + ∫ₛᵀ e^{∫ᵤᵀ a} b(u) du`; `linFlow`: the same with
`exp((∫ₛᵀ a) L)`), `ψ(s, x) = φ(X_{s→T}(x))` solves the backward transport equation
`∂ₛψ + v_s ⬝ ∇ψ = 0`, and `ψ(s)`, `∂ₛψ(s)` are `C²_c` with supports in one compact set for
`s ∈ [0, T]`. `integral_eq_of_dual` shows `s ↦ ∫ ψ(s) dρ_s` has derivative `0` on `[0, T]`
(within `[0, T]`, so only the half-line form of `WeakContinuity2` is used), hence
`∫ φ dρ_T = ∫ φ ∘ X_{0→T} dρ_0`. Smooth compactly supported functions determine finite measures
(`ext_of_forall_integral_smooth_eq`), so `ρ_T = (X_{0→T})_# ρ_0`. Smooth (rather than `C²`) test
functions are used so that `∂ₛψ(s) = -v_s ⬝ ∇ψ(s)` is itself a `C²_c` test function.

## Main results

* `ext_of_forall_integral_smooth_eq` (in `Flow/NoiseScoreEquivalence.lean`): `C^∞_c` functions
  determine finite measures on `ℝᵈ`.
* `integral_eq_of_dual`: the abstract duality step (any `v`, any backward transport solution).
* `eq_map_affineFlow_of_weakContinuity2`, `uniqueWeakContinuity_affine`: `v = a(t) x + b(t)`.
* `eq_map_linFlow_of_weakContinuity2`, `uniqueWeakContinuity_linear`: `v = a(t) L x + b(t)`.
* `uniqueWeakContinuity_congr`: `UniqueWeakContinuity` only depends on `v t`, `t ≥ 0`.
* `uniqueWeakContinuity_of_affine`, `uniqueWeakContinuity_of_matrix_affine`: the half-line
  versions (coefficients only continuous on `[0, ∞)`, `v` arbitrary for `t < 0`).
* FL-5 instances: `uniqueWeakContinuity_probabilityFlowVelocity_of_affine` (affine drift and
  affine score with scalar coefficients), `uniqueWeakContinuity_klFlowVelocity_of_affine`
  (any matrix `A`, isotropic-affine target score, affine marginal scores), and
  `map_flow_eq_of_weakFokkerPlanck_of_affine`, FL-5 with the PDE-uniqueness input removed in
  the affine case (the Itô input `WeakFokkerPlanck` remains a named hypothesis).

## Not proved here

* Uniqueness for velocities with time-dependent, non-commuting matrix coefficients
  `A(t) x + b(t)` (this needs the propagator of a time-dependent linear ODE, not constructed
  here), or for non-affine velocities (Lipschitz and locally Lipschitz velocities are in
  `Flow/ContinuityUniquenessLocal`).
* Nothing about the Itô input `WeakFokkerPlanck`: in `map_flow_eq_of_weakFokkerPlanck_of_affine`
  it is still a hypothesis. Only one-time marginals are matched.
-/

@[expose] public section

open MeasureTheory Matrix Set Filter Topology Metric Asymptotics
open scoped Manifold ContDiff

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-! ### The duality argument -/

/-- **Duality step for `WeakContinuity2` (Verified).** Let `ρ` be a curve of probability
measures on `t ≥ 0` solving `WeakContinuity2 ρ v`, and `T ≥ 0`. Let `ψ : ℝ → ℝᵈ → ℝ` be a
solution of the backward transport equation `∂ₛψ + v_s ⬝ ∇ψ = 0` on `[0, T]` in the following
sense: `g s x` is the time derivative `∂ₛψ(s, x)` (for all `s, x`), `g` is jointly continuous,
`ψ s` and `g s` are `C²_c` for `s ∈ [0, T]`, the supports of `g s` (`s ∈ [0, T]`) lie in one
compact `K`, and `g s x = -(v_s(x) ⬝ ∇ψ(s, x))` for `s ∈ [0, T]`. Then
`∫ ψ(T) dρ_T = ∫ ψ(0) dρ_0`.

Proof: `G(s) = ∫ ψ(s) dρ_s` has derivative `0` within `[0, T]`. Splitting
`G(r) - G(s) = ∫ (ψ(r) - ψ(s)) dρ_r + (∫ ψ(s) dρ_r - ∫ ψ(s) dρ_s)`, the second term is
controlled by `WeakContinuity2` for the fixed test `ψ(s)`; in the first,
`ψ(r) - ψ(s) - (r - s) ∂ₛψ(s)` is `o(r - s)` uniformly in `x` (mean value theorem and uniform
continuity of `g` on `[0, T] × K`), `ρ_r` has mass `1`, and `∫ g(s) dρ_r → ∫ g(s) dρ_s` by
`WeakContinuity2` for the test `g(s)`. -/
theorem integral_eq_of_dual {ρ : ℝ → Measure (Fin d → ℝ)} {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakContinuity2 ρ v)
    {T : ℝ} (hT : 0 ≤ T) {ψ g : ℝ → (Fin d → ℝ) → ℝ}
    (hψ : ∀ s ∈ Icc 0 T, TestFunction2 (ψ s)) (hg : ∀ s ∈ Icc 0 T, TestFunction2 (g s))
    (hd : ∀ s x, HasDerivAt (fun u => ψ u x) (g s x) s)
    (hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hgK : ∀ s ∈ Icc 0 T, ∀ x ∉ K, g s x = 0)
    (htr : ∀ s ∈ Icc 0 T, ∀ x, g s x = -(v s x ⬝ᵥ grad (ψ s) x)) :
    ∫ x, ψ T x ∂(ρ T) = ∫ x, ψ 0 x ∂(ρ 0) := by
  set G : ℝ → ℝ := fun s => ∫ x, ψ s x ∂(ρ s) with hG
  have hint : ∀ r, 0 ≤ r → ∀ f : (Fin d → ℝ) → ℝ, TestFunction2 f → Integrable f (ρ r) := by
    intro r hr f hf
    have := hprob r hr
    exact hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hderiv : ∀ s ∈ Icc 0 T, HasDerivWithinAt G 0 (Icc 0 T) s := by
    intro s hs
    set L := 𝓝[Icc 0 T] s
    have hmem : ∀ᶠ r in L, r ∈ Icc 0 T := self_mem_nhdsWithin
    -- the three error terms
    set E1 : ℝ → ℝ := fun r => ∫ x, (ψ r x - ψ s x - (r - s) * g s x) ∂(ρ r)
    set E2 : ℝ → ℝ := fun r => (r - s) * (∫ x, g s x ∂(ρ r) - ∫ x, g s x ∂(ρ s))
    set E3 : ℝ → ℝ := fun r => ∫ x, ψ s x ∂(ρ r) - ∫ x, ψ s x ∂(ρ s) -
      (r - s) • ∫ x, v s x ⬝ᵥ grad (ψ s) x ∂(ρ s)
    have h3 : E3 =o[L] fun r => r - s :=
      hasDerivWithinAt_iff_isLittleO.1 ((hρ (ψ s) (hψ s hs) s hs.1).mono Icc_subset_Ici_self)
    have h2 : E2 =o[L] fun r => r - s := by
      have ht : Tendsto (fun r => ∫ x, g s x ∂(ρ r) - ∫ x, g s x ∂(ρ s)) L (𝓝 0) := by
        have hc := ((hρ (g s) (hg s hs) s hs.1).continuousWithinAt).mono
          (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0)
        simpa using hc.tendsto.sub_const (∫ x, g s x ∂(ρ s))
      have := (isBigO_refl (fun r => r - s) L).mul_isLittleO (isLittleO_one_iff ℝ |>.2 ht)
      simpa using this
    have h1 : E1 =o[L] fun r => r - s := by
      rw [isLittleO_iff]
      intro ε hε
      have huc : UniformContinuousOn (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) (Icc 0 T ×ˢ K) :=
        (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hgc.continuousOn
      obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
      have hbd : ∀ u ∈ Icc 0 T ∩ ball s δ, ∀ x, ‖g u x - g s x‖ ≤ ε := by
        intro u hu x
        by_cases hx : x ∈ K
        · have := hδu (u, x) ⟨hu.1, hx⟩ (s, x) ⟨hs, hx⟩ (by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hu.2)
          rw [← dist_eq_norm]; exact this.le
        · rw [hgK u hu.1 x hx, hgK s hs x hx, sub_self, norm_zero]; exact hε.le
      filter_upwards [hmem, inter_mem_nhdsWithin (Icc 0 T) (ball_mem_nhds s hδ)] with r hr hrb
      have := hprob r hr.1
      have hpt : ∀ x, ‖ψ r x - ψ s x - (r - s) * g s x‖ ≤ ε * ‖r - s‖ := by
        intro x
        have hcvx : Convex ℝ (Icc 0 T ∩ ball s δ) := (convex_Icc (0 : ℝ) T).inter (convex_ball s δ)
        have := hcvx.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun u => ψ u x - u * g s x) (f' := fun u => g u x - g s x)
          (fun u _ => (((hd u x).sub ((hasDerivAt_id u).mul_const (g s x))).congr_deriv
            (by simp)).hasDerivWithinAt) (hbd · · x) ⟨hs, mem_ball_self hδ⟩ hrb
        convert this using 2
        ring
      calc ‖E1 r‖ ≤ ε * ‖r - s‖ * (ρ r).real univ :=
            norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
        _ = ε * ‖r - s‖ := by simp
    have hsum : ∀ᶠ r in L, G r - G s - (r - s) • (0 : ℝ) = E1 r + E2 r + E3 r := by
      filter_upwards [hmem] with r hr
      have hgs : ∫ x, g s x ∂(ρ s) = -∫ x, v s x ⬝ᵥ grad (ψ s) x ∂(ρ s) := by
        rw [← integral_neg]; exact integral_congr_ae (Eventually.of_forall (htr s hs))
      have hE1 : E1 r = ∫ x, ψ r x ∂(ρ r) - ∫ x, ψ s x ∂(ρ r) - (r - s) * ∫ x, g s x ∂(ρ r) := by
        have i1 := hint r hr.1 _ (hψ r hr)
        have i2 := hint r hr.1 _ (hψ s hs)
        have i3 := (hint r hr.1 _ (hg s hs)).const_mul (r - s)
        have i12 : Integrable (fun x => ψ r x - ψ s x) (ρ r) := i1.sub i2
        simp only [E1]
        rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul]
      simp only [E2, E3, hE1, hG, smul_eq_mul, hgs]
      ring
    have := ((h1.add h2).add h3).congr' (hsum.mono fun r hr => hr.symm) EventuallyEq.rfl
    exact hasDerivWithinAt_iff_isLittleO.2 this
  have hcont : ContinuousOn G (Icc 0 T) := fun s hs => (hderiv s hs).continuousWithinAt
  refine constant_of_has_deriv_right_zero hcont (fun s hs => ?_) T ⟨hT, le_rfl⟩
  exact (hderiv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
    (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))

/-! ### Affine velocity fields with a scalar time-dependent coefficient -/

/-- For any `f : ℝᵈ → ℝ`, `w ⬝ ∇f(x)` is the Fréchet derivative of `f` at `x` in direction
`w`. -/
theorem dotProduct_grad (f : (Fin d → ℝ) → ℝ) (x w : Fin d → ℝ) :
    w ⬝ᵥ grad f x = fderiv ℝ f x w := by
  conv_rhs => rw [pi_eq_sum_univ w]
  simp only [dotProduct, grad, partialDeriv, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

/-- The primitive `A(s) = ∫₀ˢ a` of a scalar coefficient `a`. -/
noncomputable def affinePrim (a : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, a u

/-- The scale factor `e^{A(T) - A(s)}` of the flow of `ẋ = a(t) x + b(t)` from time `s` to
time `T` (`A = affinePrim a`). -/
noncomputable def affineScale (a : ℝ → ℝ) (T s : ℝ) : ℝ :=
  Real.exp (affinePrim a T - affinePrim a s)

/-- The shift `∫ₛᵀ e^{A(T) - A(u)} b(u) du` of the flow of `ẋ = a(t) x + b(t)` from time `s`
to time `T`. -/
noncomputable def affineShift (a : ℝ → ℝ) (b : ℝ → Fin d → ℝ) (T s : ℝ) : Fin d → ℝ :=
  -∫ u in T..s, affineScale a T u • b u

/-- The flow map `X_{s→T}(x) = e^{A(T) - A(s)} x + ∫ₛᵀ e^{A(T) - A(u)} b(u) du` of the affine
ODE `ẋ = a(t) x + b(t)`, from time `s` to time `T`. -/
noncomputable def affineFlow (a : ℝ → ℝ) (b : ℝ → Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ :=
  affineScale a T s • x + affineShift a b T s

section Affine

variable {a : ℝ → ℝ} {b : ℝ → Fin d → ℝ}

/-- `A' = a` for the primitive `A = affinePrim a` of a continuous `a`. -/
theorem hasDerivAt_affinePrim (ha : Continuous a) (s : ℝ) :
    HasDerivAt (affinePrim a) (a s) s :=
  (ha.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The primitive of a continuous `a` is continuous. -/
theorem continuous_affinePrim (ha : Continuous a) : Continuous (affinePrim a) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_affinePrim ha s).continuousAt

/-- `s ↦ e^{A(T) - A(s)}` is continuous. -/
theorem continuous_affineScale (ha : Continuous a) (T : ℝ) : Continuous (affineScale a T) :=
  (continuous_const.sub (continuous_affinePrim ha)).rexp

/-- The scale factor `e^{A(T) - A(s)}` is positive. -/
theorem affineScale_pos (a : ℝ → ℝ) (T s : ℝ) : 0 < affineScale a T s := Real.exp_pos _

/-- The scale factor from `T` to `T` is `1`. -/
theorem affineScale_self (a : ℝ → ℝ) (T : ℝ) : affineScale a T T = 1 := by
  simp [affineScale]

/-- `∂ₛ e^{A(T) - A(s)} = -a(s) e^{A(T) - A(s)}`. -/
theorem hasDerivAt_affineScale (ha : Continuous a) (T s : ℝ) :
    HasDerivAt (affineScale a T) (-(a s * affineScale a T s)) s := by
  have h := ((hasDerivAt_const s (affinePrim a T)).sub (hasDerivAt_affinePrim ha s)).exp
  refine h.congr_deriv ?_
  simp only [affineScale, Pi.sub_apply]
  ring

/-- `∂ₛ ∫ₛᵀ e^{A(T) - A(u)} b(u) du = -e^{A(T) - A(s)} b(s)`. -/
theorem hasDerivAt_affineShift (ha : Continuous a) (hb : Continuous b) (T s : ℝ) :
    HasDerivAt (affineShift a b T) (-(affineScale a T s • b s)) s :=
  ((((continuous_affineScale ha T).smul hb).integral_hasStrictDerivAt T s).hasDerivAt).neg

/-- The shift `s ↦ ∫ₛᵀ e^{A(T) - A(u)} b(u) du` is continuous. -/
theorem continuous_affineShift (ha : Continuous a) (hb : Continuous b) (T : ℝ) :
    Continuous (affineShift a b T) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_affineShift ha hb T s).continuousAt

/-- The shift from `T` to `T` is `0`. -/
theorem affineShift_self (a : ℝ → ℝ) (b : ℝ → Fin d → ℝ) (T : ℝ) :
    affineShift a b T T = 0 := by
  simp [affineShift]

/-- `X_{T→T} = id`. -/
theorem affineFlow_self (a : ℝ → ℝ) (b : ℝ → Fin d → ℝ) (T : ℝ) (x : Fin d → ℝ) :
    affineFlow a b T T x = x := by
  simp [affineFlow, affineScale_self, affineShift_self]

/-- `(s, x) ↦ X_{s→T}(x)` is jointly continuous. -/
theorem continuous_affineFlow (ha : Continuous a) (hb : Continuous b) (T : ℝ) :
    Continuous (fun q : ℝ × (Fin d → ℝ) => affineFlow a b T q.1 q.2) :=
  (((continuous_affineScale ha T).comp continuous_fst).smul continuous_snd).add
    ((continuous_affineShift ha hb T).comp continuous_fst)

/-- `∂ₛ X_{s→T}(x) = -e^{A(T) - A(s)} (a(s) x + b(s))`. -/
theorem hasDerivAt_affineFlow (ha : Continuous a) (hb : Continuous b) (T s : ℝ)
    (x : Fin d → ℝ) :
    HasDerivAt (fun u => affineFlow a b T u x) (-(affineScale a T s • (a s • x + b s))) s := by
  have h : HasDerivAt (fun u => affineScale a T u • x + affineShift a b T u) _ s :=
    ((hasDerivAt_affineScale ha T s).smul_const x).add (hasDerivAt_affineShift ha hb T s)
  refine h.congr_deriv ?_
  module

/-- If `R + ‖c‖ < e ‖x‖` with `e > 0`, then `R < ‖e x + c‖`. -/
theorem lt_norm_smul_add {e R : ℝ} (he : 0 < e) {c x : Fin d → ℝ} (h : R + ‖c‖ < e * ‖x‖) :
    R < ‖e • x + c‖ := by
  have h1 : ‖e • x‖ = e * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg he.le]
  have h2 : ‖e • x‖ ≤ ‖e • x + c‖ + ‖c‖ := by simpa using norm_sub_le (e • x + c) c
  linarith

/-- **Representation of solutions for an affine velocity (Verified).** Let `a : ℝ → ℝ` and
`b : ℝ → ℝᵈ` be continuous, `v_t(x) = a(t) x + b(t)`, and let `ρ` be a curve of probability
measures on `t ≥ 0` solving `WeakContinuity2 ρ v`. Then for every `T ≥ 0` and every smooth
compactly supported `φ`, `∫ φ dρ_T = ∫ φ(X_{0→T}(x)) dρ_0(x)`, where
`X_{0→T}(x) = e^{∫₀ᵀ a} x + ∫₀ᵀ e^{∫ᵤᵀ a} b(u) du` is the flow map (`affineFlow a b T 0`).

Proof: duality (`integral_eq_of_dual`) with the backward transport solution
`ψ(s, x) = φ(X_{s→T}(x))`. -/
theorem integral_eq_integral_affineFlow (ha : Continuous a) (hb : Continuous b)
    {ρ : ℝ → Measure (Fin d → ℝ)} (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : WeakContinuity2 ρ fun t x => a t • x + b t) {T : ℝ} (hT : 0 ≤ T)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x ∂(ρ T) = ∫ x, φ (affineFlow a b T 0 x) ∂(ρ 0) := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  have hout : ∀ y : Fin d → ℝ, R < ‖y‖ → y ∉ tsupport φ := fun y hy hmem => by
    have := hR hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_affineShift ha hb T).continuousOn
  obtain ⟨s0, -, hs0⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (continuous_affineScale ha T).continuousOn
  have he0 : 0 < affineScale a T s0 := affineScale_pos a T s0
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hflow : ∀ s, ContDiff ℝ ∞ (affineFlow a b T s) := fun s =>
    (contDiff_id.const_smul (affineScale a T s)).add contDiff_const
  have hlin : ∀ s, ContDiff ℝ ∞ (fun x : Fin d → ℝ => a s • x + b s) := fun s =>
    (contDiff_id.const_smul (a s)).add contDiff_const
  have hball : ∀ s x, x ∉ closedBall (0 : Fin d → ℝ)
      ((R + ‖affineShift a b T s‖) / affineScale a T s) → R < ‖affineFlow a b T s x‖ := by
    intro s x hx
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ (affineScale_pos a T s)] at hx
    exact lt_norm_smul_add (affineScale_pos a T s) (by linarith)
  set ψ : ℝ → (Fin d → ℝ) → ℝ := fun s x => φ (affineFlow a b T s x) with hψdef
  set g : ℝ → (Fin d → ℝ) → ℝ := fun s x =>
    -(affineScale a T s * fderiv ℝ φ (affineFlow a b T s x) (a s • x + b s)) with hgdef
  have hψ : ∀ s, TestFunction2 (ψ s) := fun s =>
    ⟨(hφ.comp (hflow s)).of_le (by simp),
      HasCompactSupport.intro (isCompact_closedBall _ _) fun x hx =>
        show φ _ = 0 from image_eq_zero_of_notMem_tsupport (hout _ (hball s x hx))⟩
  have hg : ∀ s, TestFunction2 (g s) := fun s =>
    ⟨(contDiff_const.mul
        (((hφ.fderiv_right (m := 2) (by simp)).comp
          ((hflow s).of_le (by simp))).clm_apply
          ((hlin s).of_le (by simp)))).neg,
      HasCompactSupport.intro (isCompact_closedBall 0
        ((R + ‖affineShift a b T s‖) / affineScale a T s)) fun x hx => by
        simp [g, fderiv_of_notMem_tsupport ℝ (hout _ (hball s x hx))]⟩
  have hd : ∀ s x, HasDerivAt (fun u => ψ u x) (g s x) s := by
    intro s x
    refine ((hφ1 _).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_affineFlow ha hb T s x)).congr_deriv ?_
    simp [g, map_neg, map_smul]
    ring
  have hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) := by
    refine (((continuous_affineScale ha T).comp continuous_fst).mul ?_).neg
    exact ((hφ.continuous_fderiv (by simp)).comp (continuous_affineFlow ha hb T)).clm_apply
      (((ha.comp continuous_fst).smul continuous_snd).add (hb.comp continuous_fst))
  have hgK : ∀ s ∈ Icc 0 T, ∀ x ∉ closedBall (0 : Fin d → ℝ) ((R + C) / affineScale a T s0),
      g s x = 0 := by
    intro s hs x hx
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ he0] at hx
    have h1 := hC s hs
    have h2 : affineScale a T s0 ≤ affineScale a T s := hs0 hs
    have h3 : R < ‖affineFlow a b T s x‖ := lt_norm_smul_add (affineScale_pos a T s)
      (by nlinarith [norm_nonneg x])
    simp [g, fderiv_of_notMem_tsupport ℝ (hout _ h3)]
  have htr : ∀ s ∈ Icc 0 T, ∀ x, g s x = -((a s • x + b s) ⬝ᵥ grad (ψ s) x) := by
    intro s _ x
    have hF : HasFDerivAt (affineFlow a b T s)
        (affineScale a T s • ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
      ((hasFDerivAt_id x).const_smul (affineScale a T s)).add_const _
    have hψF : fderiv ℝ (ψ s) x = (fderiv ℝ φ (affineFlow a b T s x)).comp
        (affineScale a T s • ContinuousLinearMap.id ℝ (Fin d → ℝ)) :=
      ((hφ1 _).hasFDerivAt.comp x hF).fderiv
    rw [dotProduct_grad, hψF]
    simp [g]
  have key := integral_eq_of_dual hprob hρ hT (fun s _ => hψ s) (fun s _ => hg s) hd hgc
    (isCompact_closedBall _ _) hgK htr
  simpa [ψ, affineFlow_self] using key

/-- **Every solution is the flow pushforward (affine velocity, Verified).** For continuous
`a : ℝ → ℝ`, `b : ℝ → ℝᵈ` and `v_t(x) = a(t) x + b(t)`, every curve `ρ` of probability measures
on `t ≥ 0` solving `WeakContinuity2 ρ v` satisfies `ρ_T = (X_{0→T})_# ρ_0` for every `T ≥ 0`,
where `X_{0→T} = affineFlow a b T 0` is the explicit flow map of `ẋ = a(t) x + b(t)`. This is
a one-time law equality at each `T ≥ 0`. -/
theorem eq_map_affineFlow_of_weakContinuity2 (ha : Continuous a) (hb : Continuous b)
    {ρ : ℝ → Measure (Fin d → ℝ)} (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : WeakContinuity2 ρ fun t x => a t • x + b t) {T : ℝ} (hT : 0 ≤ T) :
    ρ T = (ρ 0).map (affineFlow a b T 0) := by
  have := hprob T hT
  have := hprob 0 le_rfl
  have hm : Measurable (affineFlow a b T 0) :=
    ((continuous_id.const_smul (affineScale a T 0)).add continuous_const).measurable
  refine ext_of_forall_integral_smooth_eq fun φ hφ hφc => ?_
  rw [integral_map hm.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact integral_eq_integral_affineFlow ha hb hprob hρ hT hφ hφc

/-- **`UniqueWeakContinuity` for affine velocities with a scalar coefficient (Verified).** For
continuous `a : ℝ → ℝ` and `b : ℝ → ℝᵈ`, uniqueness holds for the weak continuity equation
(`WeakContinuity2`, probability measures on `t ≥ 0`) with velocity `v_t(x) = a(t) x + b(t)`:
both solutions equal the pushforward of the common initial law by the explicit flow
(`eq_map_affineFlow_of_weakContinuity2`). -/
theorem uniqueWeakContinuity_affine (ha : Continuous a) (hb : Continuous b) :
    UniqueWeakContinuity fun t (x : Fin d → ℝ) => a t • x + b t := by
  intro ρ ρ' hp hp' hc hc' h0 t ht
  rw [eq_map_affineFlow_of_weakContinuity2 ha hb hp hc ht,
    eq_map_affineFlow_of_weakContinuity2 ha hb hp' hc' ht, h0]

end Affine

/-! ### Affine velocity fields with a constant linear part -/

/-- The propagator `exp((A(T) - A(s)) L)` (`A = affinePrim a`) of the linear part of
`ẋ = a(t) L x + b(t)`, from time `s` to time `T`, for a continuous linear `L : ℝᵈ → ℝᵈ`. -/
noncomputable def linProp (a : ℝ → ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T s : ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  NormedSpace.exp ((affinePrim a T - affinePrim a s) • L)

/-- The shift `∫ₛᵀ exp((A(T) - A(u)) L) b(u) du` of the flow of `ẋ = a(t) L x + b(t)`. -/
noncomputable def linShift (a : ℝ → ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (b : ℝ → Fin d → ℝ) (T s : ℝ) : Fin d → ℝ :=
  -∫ u in T..s, linProp a L T u (b u)

/-- The flow map `X_{s→T}(x) = exp((A(T) - A(s)) L) x + ∫ₛᵀ exp((A(T) - A(u)) L) b(u) du` of
`ẋ = a(t) L x + b(t)`, from time `s` to time `T`. -/
noncomputable def linFlow (a : ℝ → ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (b : ℝ → Fin d → ℝ) (T s : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  linProp a L T s x + linShift a L b T s

section Linear

variable {a : ℝ → ℝ} {b : ℝ → Fin d → ℝ} {L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}

/-- `∂ₛ exp((A(T) - A(s)) L) = -a(s) exp((A(T) - A(s)) L) L`. -/
theorem hasDerivAt_linProp (ha : Continuous a) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (T s : ℝ) : HasDerivAt (linProp a L T) (-(a s • (linProp a L T s * L))) s := by
  have hw : HasDerivAt (fun s => affinePrim a T - affinePrim a s) (0 - a s) s :=
    (hasDerivAt_const _ _).sub (hasDerivAt_affinePrim ha s)
  have h := (hasDerivAt_exp_smul_const L (affinePrim a T - affinePrim a s)).scomp s hw
  exact h.congr_deriv (by simp [linProp])

/-- The propagator `s ↦ exp((A(T) - A(s)) L)` is continuous. -/
theorem continuous_linProp (ha : Continuous a) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T : ℝ) :
    Continuous (linProp a L T) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_linProp ha L T s).continuousAt

/-- The propagator from `T` to `T` is the identity. -/
theorem linProp_self (a : ℝ → ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T : ℝ) :
    linProp a L T T = 1 := by
  simp [linProp]

/-- The propagator of `-L` inverts the propagator of `L`. -/
theorem linProp_neg_apply (a : ℝ → ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T s : ℝ)
    (z : Fin d → ℝ) : linProp a (-L) T s (linProp a L T s z) = z := by
  have hb : ∀ M : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ),
      M ∈ Metric.eball (0 : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
        (NormedSpace.expSeries ℝ ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ))).radius := fun M => by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have h : linProp a (-L) T s * linProp a L T s = 1 := by
    rw [linProp, linProp, smul_neg, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
      (Commute.neg_left (Commute.refl _)) (hb _) (hb _), neg_add_cancel, NormedSpace.exp_zero]
  have := congrArg (fun M : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => M z) h
  simpa using this

/-- `∂ₛ ∫ₛᵀ exp((A(T) - A(u)) L) b(u) du = -exp((A(T) - A(s)) L) b(s)`. -/
theorem hasDerivAt_linShift (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T s : ℝ) :
    HasDerivAt (linShift a L b T) (-(linProp a L T s (b s))) s :=
  ((((continuous_linProp ha L T).clm_apply hb).integral_hasStrictDerivAt T s).hasDerivAt).neg

/-- The shift `s ↦ ∫ₛᵀ exp((A(T) - A(u)) L) b(u) du` is continuous. -/
theorem continuous_linShift (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T : ℝ) : Continuous (linShift a L b T) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_linShift ha hb L T s).continuousAt

/-- `X_{T→T} = id` for the flow of `ẋ = a(t) L x + b(t)`. -/
theorem linFlow_self (a : ℝ → ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (b : ℝ → Fin d → ℝ)
    (T : ℝ) (x : Fin d → ℝ) : linFlow a L b T T x = x := by
  simp [linFlow, linShift, linProp_self]

/-- `(s, x) ↦ X_{s→T}(x)` is jointly continuous (flow of `ẋ = a(t) L x + b(t)`). -/
theorem continuous_linFlow (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T : ℝ) :
    Continuous (fun q : ℝ × (Fin d → ℝ) => linFlow a L b T q.1 q.2) :=
  (((continuous_linProp ha L T).comp continuous_fst).clm_apply continuous_snd).add
    ((continuous_linShift ha hb L T).comp continuous_fst)

/-- `∂ₛ X_{s→T}(x) = -exp((A(T) - A(s)) L) (a(s) L x + b(s))`. -/
theorem hasDerivAt_linFlow (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T s : ℝ) (x : Fin d → ℝ) :
    HasDerivAt (fun u => linFlow a L b T u x) (-(linProp a L T s (a s • L x + b s))) s := by
  have h : HasDerivAt (fun u => linProp a L T u x + linShift a L b T u) _ s :=
    ((hasDerivAt_linProp ha L T s).clm_apply (hasDerivAt_const s x)).add
      (hasDerivAt_linShift ha hb L T s)
  refine h.congr_deriv ?_
  simp [map_add, map_smul]
  abel

/-- If `M' (M z) = z` for all `z` and `‖M'‖ (R + ‖c‖) < ‖x‖`, then `R < ‖M x + c‖`. -/
theorem lt_norm_clm_apply_add {M M' : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}
    (hM : ∀ z, M' (M z) = z) {R : ℝ} {c x : Fin d → ℝ} (h : ‖M'‖ * (R + ‖c‖) < ‖x‖) :
    R < ‖M x + c‖ := by
  by_contra hle
  push Not at hle
  have h1 : ‖x‖ ≤ ‖M'‖ * ‖M x‖ := by
    conv_lhs => rw [← hM x]
    exact M'.le_opNorm _
  have h2 : ‖M x‖ ≤ ‖M x + c‖ + ‖c‖ := by simpa using norm_sub_le (M x + c) c
  have h3 : ‖M'‖ * ‖M x‖ ≤ ‖M'‖ * (R + ‖c‖) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  linarith

/-- **Representation of solutions for `v_t(x) = a(t) L x + b(t)` (Verified).** Let
`a : ℝ → ℝ`, `b : ℝ → ℝᵈ` be continuous and `L : ℝᵈ →L ℝᵈ` a fixed continuous linear map. If
`ρ` is a curve of probability measures on `t ≥ 0` solving `WeakContinuity2 ρ v` for
`v_t(x) = a(t) L x + b(t)`, then for every `T ≥ 0` and every smooth compactly supported `φ`,
`∫ φ dρ_T = ∫ φ(X_{0→T}(x)) dρ_0(x)` with the explicit flow `X_{0→T} = linFlow a L b T 0`.
Proof: duality (`integral_eq_of_dual`) with `ψ(s, x) = φ(X_{s→T}(x))`. -/
theorem integral_eq_integral_linFlow (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    {ρ : ℝ → Measure (Fin d → ℝ)} (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : WeakContinuity2 ρ fun t x => a t • L x + b t) {T : ℝ} (hT : 0 ≤ T)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x ∂(ρ T) = ∫ x, φ (linFlow a L b T 0 x) ∂(ρ 0) := by
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  obtain ⟨R, hRnn, hR⟩ : ∃ R, 0 ≤ R ∧ tsupport φ ⊆ closedBall 0 R :=
    ⟨max R₀ 0, le_max_right _ _, hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  have hout : ∀ y : Fin d → ℝ, R < ‖y‖ → y ∉ tsupport φ := fun y hy hmem => by
    have := hR hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  set Minv : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := linProp a (-L) T with hMinv
  have hMinvc : Continuous Minv := continuous_linProp ha (-L) T
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_linShift ha hb L T).continuousOn
  obtain ⟨N, hN⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hMinvc.continuousOn
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hflow : ∀ s, ContDiff ℝ ∞ (linFlow a L b T s) := fun s =>
    (linProp a L T s).contDiff.add contDiff_const
  have hlin : ∀ s, ContDiff ℝ ∞ (fun x : Fin d → ℝ => a s • L x + b s) := fun s =>
    (L.contDiff.const_smul (a s)).add contDiff_const
  have hball : ∀ s x, x ∉ closedBall (0 : Fin d → ℝ) (‖Minv s‖ * (R + ‖linShift a L b T s‖)) →
      R < ‖linFlow a L b T s x‖ := by
    intro s x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact lt_norm_clm_apply_add (linProp_neg_apply a L T s) hx
  set ψ : ℝ → (Fin d → ℝ) → ℝ := fun s x => φ (linFlow a L b T s x) with hψdef
  set g : ℝ → (Fin d → ℝ) → ℝ := fun s x =>
    -(fderiv ℝ φ (linFlow a L b T s x) (linProp a L T s (a s • L x + b s))) with hgdef
  have hψ : ∀ s, TestFunction2 (ψ s) := fun s =>
    ⟨(hφ.comp (hflow s)).of_le (by simp),
      HasCompactSupport.intro (isCompact_closedBall _ _) fun x hx =>
        show φ _ = 0 from image_eq_zero_of_notMem_tsupport (hout _ (hball s x hx))⟩
  have hg : ∀ s, TestFunction2 (g s) := fun s =>
    ⟨((((hφ.fderiv_right (m := 2) (by simp)).comp
          ((hflow s).of_le (by simp))).clm_apply
          ((linProp a L T s).contDiff.comp ((hlin s).of_le (by simp))))).neg,
      HasCompactSupport.intro (isCompact_closedBall 0
        (‖Minv s‖ * (R + ‖linShift a L b T s‖))) fun x hx => by
        simp [g, fderiv_of_notMem_tsupport ℝ (hout _ (hball s x hx))]⟩
  have hd : ∀ s x, HasDerivAt (fun u => ψ u x) (g s x) s := by
    intro s x
    refine ((hφ1 _).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_linFlow ha hb L T s x)).congr_deriv ?_
    simp [g]
  have hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) := by
    refine (((hφ.continuous_fderiv (by simp)).comp (continuous_linFlow ha hb L T)).clm_apply
      (((continuous_linProp ha L T).comp continuous_fst).clm_apply
        (((ha.comp continuous_fst).smul (L.continuous.comp continuous_snd)).add
          (hb.comp continuous_fst)))).neg
  have hgK : ∀ s ∈ Icc 0 T, ∀ x ∉ closedBall (0 : Fin d → ℝ) (N * (R + C)), g s x = 0 := by
    intro s hs x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    have h1 := hC s hs
    have h2 := hN s hs
    have hR0 : 0 ≤ R + ‖linShift a L b T s‖ := by positivity
    have h3 : R < ‖linFlow a L b T s x‖ := by
      refine lt_norm_clm_apply_add (linProp_neg_apply a L T s) (lt_of_le_of_lt ?_ hx)
      calc ‖Minv s‖ * (R + ‖linShift a L b T s‖) ≤ N * (R + ‖linShift a L b T s‖) :=
            mul_le_mul_of_nonneg_right h2 hR0
        _ ≤ N * (R + C) := mul_le_mul_of_nonneg_left (by linarith)
            ((norm_nonneg _).trans h2)
    simp [g, fderiv_of_notMem_tsupport ℝ (hout _ h3)]
  have htr : ∀ s ∈ Icc 0 T, ∀ x, g s x = -((a s • L x + b s) ⬝ᵥ grad (ψ s) x) := by
    intro s _ x
    have hF : HasFDerivAt (linFlow a L b T s) (linProp a L T s) x :=
      (linProp a L T s).hasFDerivAt.add_const _
    have hψF : fderiv ℝ (ψ s) x = (fderiv ℝ φ (linFlow a L b T s x)).comp (linProp a L T s) :=
      ((hφ1 _).hasFDerivAt.comp x hF).fderiv
    rw [dotProduct_grad, hψF]
    simp [g]
  have key := integral_eq_of_dual hprob hρ hT (fun s _ => hψ s) (fun s _ => hg s) hd hgc
    (isCompact_closedBall _ _) hgK htr
  simpa [ψ, linFlow_self] using key

/-- **Every solution is the flow pushforward (`v_t(x) = a(t) L x + b(t)`, Verified).** For
continuous `a`, `b` and a continuous linear `L`, every curve `ρ` of probability measures on
`t ≥ 0` solving `WeakContinuity2 ρ v` satisfies `ρ_T = (X_{0→T})_# ρ_0` for every `T ≥ 0`, with
the explicit flow `X_{0→T} = linFlow a L b T 0`. -/
theorem eq_map_linFlow_of_weakContinuity2 (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    {ρ : ℝ → Measure (Fin d → ℝ)} (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : WeakContinuity2 ρ fun t x => a t • L x + b t) {T : ℝ} (hT : 0 ≤ T) :
    ρ T = (ρ 0).map (linFlow a L b T 0) := by
  have := hprob T hT
  have := hprob 0 le_rfl
  have hm : Measurable (linFlow a L b T 0) :=
    ((linProp a L T 0).continuous.add continuous_const).measurable
  refine ext_of_forall_integral_smooth_eq fun φ hφ hφc => ?_
  rw [integral_map hm.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact integral_eq_integral_linFlow ha hb L hprob hρ hT hφ hφc

/-- **`UniqueWeakContinuity` for `v_t(x) = a(t) L x + b(t)` (Verified).** For continuous
`a : ℝ → ℝ`, `b : ℝ → ℝᵈ` and a fixed continuous linear map `L : ℝᵈ →L ℝᵈ`, uniqueness holds
for `WeakContinuity2` (probability measures on `t ≥ 0`) with velocity `a(t) L x + b(t)`. -/
theorem uniqueWeakContinuity_linear (ha : Continuous a) (hb : Continuous b)
    (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    UniqueWeakContinuity fun t (x : Fin d → ℝ) => a t • L x + b t := by
  intro ρ ρ' hp hp' hc hc' h0 t ht
  rw [eq_map_linFlow_of_weakContinuity2 ha hb L hp hc ht,
    eq_map_linFlow_of_weakContinuity2 ha hb L hp' hc' ht, h0]

end Linear

/-! ### Only `t ≥ 0` matters -/

/-- `WeakContinuity2` only sees the velocity at times `t ≥ 0`. -/
theorem weakContinuity2_congr {ρ : ℝ → Measure (Fin d → ℝ)}
    {v v' : ℝ → (Fin d → ℝ) → Fin d → ℝ} (h : ∀ t, 0 ≤ t → v t = v' t) :
    WeakContinuity2 ρ v ↔ WeakContinuity2 ρ v' := by
  constructor
  · intro hρ φ hφ t ht
    rw [← h t ht]
    exact hρ φ hφ t ht
  · intro hρ φ hφ t ht
    rw [h t ht]
    exact hρ φ hφ t ht

/-- `UniqueWeakContinuity` only depends on the velocity at times `t ≥ 0`. -/
theorem uniqueWeakContinuity_congr {v v' : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (h : ∀ t, 0 ≤ t → v t = v' t) : UniqueWeakContinuity v ↔ UniqueWeakContinuity v' := by
  constructor
  · intro hu ρ ρ' hp hp' hc hc'
    exact hu ρ ρ' hp hp' ((weakContinuity2_congr h).2 hc) ((weakContinuity2_congr h).2 hc')
  · intro hu ρ ρ' hp hp' hc hc'
    exact hu ρ ρ' hp hp' ((weakContinuity2_congr h).1 hc) ((weakContinuity2_congr h).1 hc')

/-- **`UniqueWeakContinuity` for velocities that are affine on `t ≥ 0` (Verified).** If
`a : ℝ → ℝ` and `b : ℝ → ℝᵈ` are continuous on `[0, ∞)` and `v_t(x) = a(t) x + b(t)` for all
`t ≥ 0` and `x` (no condition on `v` for `t < 0`), then `UniqueWeakContinuity v` holds. -/
theorem uniqueWeakContinuity_of_affine {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {a : ℝ → ℝ}
    {b : ℝ → Fin d → ℝ} (ha : ContinuousOn a (Ici 0)) (hb : ContinuousOn b (Ici 0))
    (hv : ∀ t, 0 ≤ t → ∀ x, v t x = a t • x + b t) : UniqueWeakContinuity v := by
  have hm : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  have hmem : ∀ t : ℝ, max t 0 ∈ Ici (0 : ℝ) := fun t => le_max_right t 0
  have ha' : Continuous fun t => a (max t 0) := ha.comp_continuous hm hmem
  have hb' : Continuous fun t => b (max t 0) := hb.comp_continuous hm hmem
  refine (uniqueWeakContinuity_congr fun t ht => ?_).2 (uniqueWeakContinuity_affine ha' hb')
  funext x
  simp [hv t ht x, max_eq_left ht]

/-- **`UniqueWeakContinuity` for velocities `a(t) A x + b(t)` on `t ≥ 0`, `A` a constant
matrix (Verified).** If `A` is a `d × d` real matrix, `a : ℝ → ℝ` and `b : ℝ → ℝᵈ` are
continuous on `[0, ∞)`, and `v_t(x) = a(t) (A x) + b(t)` for all `t ≥ 0` and `x`, then
`UniqueWeakContinuity v` holds. With `a ≡ 1` this covers every affine field `A x + b(t)` with a
constant matrix; with `A = 1` it is `uniqueWeakContinuity_of_affine`. -/
theorem uniqueWeakContinuity_of_matrix_affine {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (A : Matrix (Fin d) (Fin d) ℝ) {a : ℝ → ℝ} {b : ℝ → Fin d → ℝ}
    (ha : ContinuousOn a (Ici 0)) (hb : ContinuousOn b (Ici 0))
    (hv : ∀ t, 0 ≤ t → ∀ x, v t x = a t • (A *ᵥ x) + b t) : UniqueWeakContinuity v := by
  have hm : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  have hmem : ∀ t : ℝ, max t 0 ∈ Ici (0 : ℝ) := fun t => le_max_right t 0
  have ha' : Continuous fun t => a (max t 0) := ha.comp_continuous hm hmem
  have hb' : Continuous fun t => b (max t 0) := hb.comp_continuous hm hmem
  refine (uniqueWeakContinuity_congr fun t ht => ?_).2
    (uniqueWeakContinuity_linear ha' hb' (Matrix.toLin' A).toContinuousLinearMap)
  funext x
  simp [hv t ht x, max_eq_left ht]

/-! ### FL-5 without the PDE-uniqueness hypothesis: affine probability-flow velocities -/

/-- **`UniqueWeakContinuity` for an affine probability-flow velocity (Verified).** If on
`t ≥ 0` the drift is affine with scalar coefficient, `b_t(x) = κ(t) x + β(t)`, and the score
of the marginal density is affine with scalar coefficient, `∇log p_t(x) = σ(t) x + τ(t)` (e.g.
`p_t` an isotropic Gaussian `N(m_t, s_t I)`, where `σ = -1/s_t`, `τ = m_t / s_t`), with
`κ, β, σ, τ` continuous on `[0, ∞)`, then `UniqueWeakContinuity` holds for
`u_t = b_t - D ∇log p_t` (`probabilityFlowVelocity b D p`), for every `D : ℝ`. -/
theorem uniqueWeakContinuity_probabilityFlowVelocity_of_affine
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {κ σ : ℝ → ℝ} {β τ : ℝ → Fin d → ℝ} (hκ : ContinuousOn κ (Ici 0))
    (hβ : ContinuousOn β (Ici 0)) (hσ : ContinuousOn σ (Ici 0)) (hτ : ContinuousOn τ (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, b t x = κ t • x + β t)
    (hs : ∀ t, 0 ≤ t → ∀ x, score (p t) x = σ t • x + τ t) :
    UniqueWeakContinuity (probabilityFlowVelocity b D p) := by
  refine uniqueWeakContinuity_of_affine (a := fun t => κ t - D * σ t)
    (b := fun t => β t - D • τ t) (hκ.sub (continuousOn_const.mul hσ))
    (hβ.sub (hτ.const_smul D)) fun t ht x => ?_
  simp only [probabilityFlowVelocity, hb t ht x, hs t ht x]
  module

/-- **`UniqueWeakContinuity` for an affine PFG velocity (Verified).** For any constant matrix
`A`, an isotropic-affine target score `s⋆(x) = σ⋆ x + τ⋆` (e.g. `p⋆ = N(μ, s I)`) and marginal
scores `∇log p_t(x) = σ(t) x + τ(t)` on `t ≥ 0` with `σ, τ` continuous on `[0, ∞)`,
`UniqueWeakContinuity` holds for the PFG velocity
`u_t(x) = A (s⋆(x) - ∇log p_t(x)) = (σ⋆ - σ(t)) A x + A (τ⋆ - τ(t))`
(`klFlowVelocity A sStar p`). -/
theorem uniqueWeakContinuity_klFlowVelocity_of_affine (A : Matrix (Fin d) (Fin d) ℝ)
    {sStar : (Fin d → ℝ) → Fin d → ℝ} {p : ℝ → (Fin d → ℝ) → ℝ} {σStar : ℝ}
    {τStar : Fin d → ℝ} {σ : ℝ → ℝ} {τ : ℝ → Fin d → ℝ} (hσ : ContinuousOn σ (Ici 0))
    (hτ : ContinuousOn τ (Ici 0)) (hsStar : ∀ x, sStar x = σStar • x + τStar)
    (hs : ∀ t, 0 ≤ t → ∀ x, score (p t) x = σ t • x + τ t) :
    UniqueWeakContinuity (klFlowVelocity A sStar p) := by
  have hA : Continuous fun w : Fin d → ℝ => A *ᵥ w :=
    (Matrix.toLin' A).toContinuousLinearMap.continuous
  refine uniqueWeakContinuity_of_matrix_affine A (a := fun t => σStar - σ t)
    (b := fun t => A *ᵥ (τStar - τ t)) (continuousOn_const.sub hσ)
    (hA.comp_continuousOn (continuousOn_const.sub hτ)) fun t ht x => ?_
  simp only [klFlowVelocity, hsStar x, hs t ht x, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul]
  module

/-- **SDE / probability-flow one-time marginal equality, affine case (FL-5 without the
PDE-uniqueness input).** The hypotheses of `map_flow_eq_of_weakFokkerPlanck` with the named
input `UniqueWeakContinuity` replaced by its sufficient condition
`uniqueWeakContinuity_probabilityFlowVelocity_of_affine`: on `t ≥ 0` the drift is
`b_t(x) = κ(t) x + β(t)` and the score is `∇log p_t(x) = σ(t) x + τ(t)`, with `κ, β, σ, τ`
continuous on `[0, ∞)`. Then `(ρ 0).map (Φ t) = ρ t` for every `t ≥ 0`; the only remaining
named input is the Itô input `WeakFokkerPlanck ρ b D`. Only one-time marginals are matched. -/
theorem map_flow_eq_of_weakFokkerPlanck_of_affine {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ} {κ σ : ℝ → ℝ} {β τ : ℝ → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : WeakFokkerPlanck ρ b D) (hκ : ContinuousOn κ (Ici 0))
    (hβ : ContinuousOn β (Ici 0)) (hσ : ContinuousOn σ (Ici 0)) (hτ : ContinuousOn τ (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, b t x = κ t • x + β t)
    (hs : ∀ t, 0 ≤ t → ∀ x, score (p t) x = σ t • x + τ t) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_weakFokkerPlanck hprob hρ hp hpos hu hΦ hΦm hΦ0 hFP
    (uniqueWeakContinuity_probabilityFlowVelocity_of_affine hκ hβ hσ hτ hb hs)

end NoiseScore
end FormalizeSampling
