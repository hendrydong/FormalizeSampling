module

public import FormalizeSampling.Flow.ContinuityUniquenessLocal

/-!
# Toward DiPerna–Lions uniqueness: the uniform commutator bound

Status: **Verified** (partial piece only). This file proves the first, quantitative ingredient of
the DiPerna–Lions renormalization argument for the transport / continuity equation: the
**uniform bound on the mollification commutator** in its kernel form

  `C_κ(u, v)(x) = ∫ u(y) Dκ(x - y) (v(y) - v(x)) dy`,

which for `κ = κ_ε` a mollifier is the commutator `(div(u v)) ⋆ κ_ε - v ⬝ ∇(u ⋆ κ_ε)` up to
the term `(u div v) ⋆ κ_ε` (the identification uses integration by parts and is **not**
formalized here). The bound requires only that `u` be bounded and `v` be Lipschitz **at the
scale of the mollifier around the point `x`**; no measurability or integrability of `u` or `v`
beyond that is needed (a non-integrable integrand has Bochner integral `0`).

## Main results

* `dlCommutator`: the kernel form of the commutator.
* `abs_dlCommutator_le`: if `κ ∈ C¹` vanishes outside `closedBall 0 r`, `|u| ≤ U` and
  `‖v(y) - v(x)‖ ≤ L ‖y - x‖` for `‖x - y‖ ≤ r`, then `|C_κ(u, v)(x)| ≤ U L r ∫ ‖Dκ‖`.
* `abs_dlCommutator_scaled_le`: for the rescaled kernel `κ_ε(z) = ε^{-d} κ(z / ε)` of a `C¹`
  kernel `κ` supported in the unit ball, `|C_{κ_ε}(u, v)(x)| ≤ U L ∫ ‖Dκ‖`, **uniformly in
  `ε > 0`** (using `∫ ‖Dκ_ε‖ = ε⁻¹ ∫ ‖Dκ‖`).

## Not proved here (the DiPerna–Lions theorem itself)

The `d ≥ 2` theorem for autonomous `v ∈ W^{1,1}_loc` with bounded divergence and
probability-density solutions is proved elsewhere:
`ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth` (`Flow/DiPernaLionsLinearGrowth.lean`,
linear growth, bounded densities; bounded `v` is `ae_eq_of_weakContinuityDensity_diPernaLions`),
with the commutator lemma in `Flow/DiPernaLionsCommutatorL1.lean` and renormalisation in
`Flow/DiPernaLionsRenormalizationBeta.lean`, and `ae_eq_of_weakContinuityDensity_diPernaLions_Lp`
(`Flow/DiPernaLionsLp.lean`, `L^p` densities).
The list below records what this file alone does not prove; still open overall: time-dependent
velocities, signed solutions, `L¹` densities, growth `v/(1+|x|) ∈ L¹ + L^∞`.

The full statement — uniqueness of `L^∞` density solutions `ρ_t = u_t · Lebesgue` of the
continuity equation for `v ∈ W^{1,1}_loc` with `div v ∈ L^∞` and linear growth — is **not**
proved in this file. Missing pieces here (each supplied by the files cited above), concretely:

* **Sobolev `W^{1,1}_loc` on `Fin d → ℝ`.** Mathlib v4.35 has distributions on open sets
  (`Mathlib/Analysis/Distribution/Distribution.lean`, with `lineDerivOp`) and the
  Fourier-defined Bessel potential spaces `TemperedDistribution.MemSobolev s p` on *inner
  product* spaces (`Mathlib/Analysis/Distribution/Sobolev.lean`), but no `W^{k,p}_loc` of
  functions with `L^p_loc` weak derivatives, no density of `C^∞` in `W^{1,1}_loc`, no
  absolute continuity on lines / difference-quotient characterization
  `‖v(· + h) - v‖_{L¹(K)} ≤ |h| ‖Dv‖_{L¹(K + B_|h|)}`, and `Fin d → ℝ` (sup norm) is not an
  inner product space, so `MemSobolev` does not even apply to the state space used here.
  Consequently the bound above is proved only for velocities Lipschitz at scale `ε` (the
  `W^{1,∞}_loc` case), not for `W^{1,1}_loc`.
* **Convergence `C_{κ_ε}(u, v) → 0` in `L¹_loc`.** Needs the smooth case (Taylor expansion
  plus the identity `∫ z ⊗ ∇κ(z) dz = -Id`) and an `L¹` density argument that combines the
  uniform bound with approximation of `Dv`; neither is formalized in this file.
* **Integration-by-parts identification** of `C_κ` with
  `(v ⬝ ∇u) ⋆ κ_ε - v ⬝ ∇(u ⋆ κ_ε)` (distributional `v ⬝ ∇u := div(u v) - u div v`).
* **Renormalization and Gronwall**: `β(u)` solves the equation for `β ∈ C¹`, then
  `∫ |u_t - u'_t| ≤ e^{‖div v‖_∞ t} ∫ |u_0 - u'_0|` with cut-offs controlled by the linear
  growth of `v`.

For globally or locally Lipschitz `v` (jointly continuous, linear growth) uniqueness already
holds among **all** probability-measure solutions — in particular among absolutely
continuous ones — by `uniqueWeakContinuity_of_locallyLipschitz`
(`Flow/ContinuityUniquenessLocal.lean`); no separate density-class statement is needed.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- The **DiPerna–Lions commutator in kernel form**:
`C_κ(u, v)(x) = ∫ u(y) Dκ(x - y) (v(y) - v(x)) dy` (Lebesgue measure on `ℝᵈ`). For a mollifier
`κ`, it is the commutator `(div(u v)) ⋆ κ - v ⬝ ∇(u ⋆ κ)` up to the term `(u div v) ⋆ κ`. -/
noncomputable def dlCommutator (κ u : (Fin d → ℝ) → ℝ) (v : (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∫ y, u y * fderiv ℝ κ (x - y) (v y - v x)

/-- **Uniform commutator bound at a fixed scale (Verified).** Let `κ : ℝᵈ → ℝ` be `C¹` and
vanish outside `closedBall 0 r`, `|u(y)| ≤ U` for all `y`, and suppose
`‖v(y) - v(x)‖ ≤ L ‖y - x‖` (`L ≥ 0`) whenever `‖x - y‖ ≤ r`. Then
`|C_κ(u, v)(x)| ≤ U (L r) ∫ ‖Dκ‖`. No measurability of `u` or `v` is assumed. -/
theorem abs_dlCommutator_le {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ) {r : ℝ}
    (hκr : ∀ z, r < ‖z‖ → κ z = 0) {u : (Fin d → ℝ) → ℝ} {U : ℝ} (hU : ∀ y, |u y| ≤ U)
    {v : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ} (hL : 0 ≤ L) {x : Fin d → ℝ}
    (hv : ∀ y, ‖x - y‖ ≤ r → ‖v y - v x‖ ≤ L * ‖y - x‖) :
    |dlCommutator κ u v x| ≤ U * (L * r) * ∫ z, ‖fderiv ℝ κ z‖ := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hts : tsupport κ ⊆ closedBall 0 r := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hz (hκr z (not_le.1 h))
  have hcs : HasCompactSupport κ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r)
      (subset_tsupport κ |>.trans hts)
  have hD0 : ∀ z, r < ‖z‖ → fderiv ℝ κ z = 0 := fun z hz =>
    fderiv_of_notMem_tsupport ℝ fun hm => by
      have := hts hm
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  have hint : Integrable (fun z => ‖fderiv ℝ κ z‖) :=
    ((hκ.continuous_fderiv one_ne_zero).norm).integrable_of_hasCompactSupport (hcs.fderiv ℝ).norm
  have hint' : Integrable (fun y => U * (L * r) * ‖fderiv ℝ κ (x - y)‖) :=
    (hint.comp_sub_left x).const_mul _
  rw [← Real.norm_eq_abs, dlCommutator]
  refine (norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall fun y => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_mul, Real.norm_eq_abs]
    by_cases hy : ‖x - y‖ ≤ r
    · have h1 : ‖fderiv ℝ κ (x - y) (v y - v x)‖ ≤ ‖fderiv ℝ κ (x - y)‖ * (L * r) := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (hv y hy).trans (mul_le_mul_of_nonneg_left ?_ hL)
        rwa [norm_sub_rev]
      calc |u y| * ‖fderiv ℝ κ (x - y) (v y - v x)‖
          ≤ U * (‖fderiv ℝ κ (x - y)‖ * (L * r)) :=
            mul_le_mul (hU y) h1 (norm_nonneg _) hU0
        _ = U * (L * r) * ‖fderiv ℝ κ (x - y)‖ := by ring
    · rw [hD0 _ (not_le.1 hy)]
      simp only [_root_.zero_apply, norm_zero, mul_zero]
      positivity
  · rw [integral_const_mul, integral_sub_left_eq_self (fun z => ‖fderiv ℝ κ z‖) volume x]

/-- **Uniform-in-`ε` commutator bound (Verified).** Let `κ : ℝᵈ → ℝ` be `C¹` and vanish
outside the closed unit ball, `ε > 0`, and `κ_ε(z) = ε^{-d} κ(ε⁻¹ z)`. If `|u| ≤ U` and
`‖v(y) - v(x)‖ ≤ L ‖y - x‖` (`L ≥ 0`) for `‖x - y‖ ≤ ε`, then
`|C_{κ_ε}(u, v)(x)| ≤ U L ∫ ‖Dκ‖`, a bound independent of `ε`. This is the
`W^{1,∞}_loc` case of the DiPerna–Lions commutator estimate. -/
theorem abs_dlCommutator_scaled_le {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hκ1 : ∀ z, 1 < ‖z‖ → κ z = 0) {ε : ℝ} (hε : 0 < ε) {u : (Fin d → ℝ) → ℝ} {U : ℝ}
    (hU : ∀ y, |u y| ≤ U) {v : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    {x : Fin d → ℝ} (hv : ∀ y, ‖x - y‖ ≤ ε → ‖v y - v x‖ ≤ L * ‖y - x‖) :
    |dlCommutator (fun z => (ε ^ d)⁻¹ * κ (ε⁻¹ • z)) u v x| ≤
      U * L * ∫ z, ‖fderiv ℝ κ z‖ := by
  set c := (ε ^ d)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hsc : ContDiff ℝ 1 (fun z : Fin d → ℝ => ε⁻¹ • z) := contDiff_const_smul _
  have hκε : ContDiff ℝ 1 (fun z => c * κ (ε⁻¹ • z)) := contDiff_const.mul (hκ.comp hsc)
  have hsupp : ∀ z : Fin d → ℝ, ε < ‖z‖ → c * κ (ε⁻¹ • z) = 0 := by
    intro z hz
    rw [hκ1, mul_zero]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le), inv_mul_eq_div,
      one_lt_div hε]
    exact hz
  have hfd : ∀ z : Fin d → ℝ, fderiv ℝ (fun z => c * κ (ε⁻¹ • z)) z =
      c • (fderiv ℝ κ (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) := by
    intro z
    have h1 : HasFDerivAt (fun z : Fin d → ℝ => ε⁻¹ • z)
        (ε⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) z :=
      (hasFDerivAt_id z).const_smul ε⁻¹
    have h2 := ((hκ.differentiable one_ne_zero _).hasFDerivAt.comp z h1).const_mul c
    exact h2.fderiv
  have hnorm : ∀ z : Fin d → ℝ, ‖fderiv ℝ (fun z => c * κ (ε⁻¹ • z)) z‖ =
      c * ε⁻¹ * ‖fderiv ℝ κ (ε⁻¹ • z)‖ := by
    intro z
    rw [hfd, ContinuousLinearMap.comp_smul, norm_smul, norm_smul, Real.norm_of_nonneg hc0,
      Real.norm_of_nonneg (inv_nonneg.2 hε.le), ContinuousLinearMap.comp_id]
    ring
  have hint : ∫ z, ‖fderiv ℝ (fun z => c * κ (ε⁻¹ • z)) z‖ =
      ε⁻¹ * ∫ z, ‖fderiv ℝ κ z‖ := by
    simp_rw [hnorm]
    rw [integral_const_mul,
      Measure.integral_comp_inv_smul_of_nonneg volume (fun z => ‖fderiv ℝ κ z‖) hε.le,
      Module.finrank_fin_fun, smul_eq_mul, hc]
    field_simp
  have := abs_dlCommutator_le hκε hsupp hU hL hv
  rw [hint] at this
  refine this.trans (le_of_eq ?_)
  field_simp

end NoiseScore
end FormalizeSampling
