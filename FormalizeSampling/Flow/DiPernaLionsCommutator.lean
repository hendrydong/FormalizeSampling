module

public import FormalizeSampling.Flow.ContinuityUniquenessDiPernaLions
public import FormalizeSampling.Flow.DiPernaLionsUniqueness

/-!
# The mollified continuity equation and the DiPerna–Lions commutator

Status: **Verified** (algebraic/first step only). This file formalizes the first step of the
DiPerna–Lions argument: mollifying a density solution of the continuity equation in space
produces an equation that holds **pointwise in `x`**, with an error given exactly by the
kernel-form commutator `dlCommutator` of `Flow/ContinuityUniquenessDiPernaLions.lean`:

  `∂ₜ (κ ⋆ u_t)(x) = -v(x) ⬝ ∇(κ ⋆ u_t)(x) - C_κ(u_t, v)(x)`,
  `C_κ(u, v)(x) = ∫ u(y) Dκ(x - y) (v(y) - v(x)) dy`.

It also identifies `C_κ` with the difference `(div(u v)) ⋆ κ - v ⬝ ∇(u ⋆ κ)` of the mollified
distributional divergence of the flux and the transport term (`dlCommutator_eq`).

## Main results

* `mollDivFlux κ u v x = ∫ u(y) Dκ(x - y) v(y) dy`, the distribution `div(u v)` tested
  against `κ(x - ·)`, i.e. `(div(u v)) ⋆ κ`.
* `fderiv_convolution_apply_eq`: `D(κ ⋆ u)(x) h = ∫ u(y) Dκ(x - y) h dy` for locally
  integrable `u`.
* `dlCommutator_eq`: `C_κ(u, v)(x) = (div(u v)) ⋆ κ (x) - D(κ ⋆ u)(x) v(x)`.
* `hasDerivWithinAt_convolution_of_weakContinuityDensity`: for a solution of
  `WeakContinuityDensity u v`, `t ↦ (κ ⋆ u_t)(x)` has derivative `-(div(u_t v)) ⋆ κ (x)`.
* `hasDerivWithinAt_convolution_eq_transport_add_commutator`: the mollified equation above.

## Not proved here

The `d ≥ 2` theorem for autonomous `v ∈ W^{1,1}_loc` with bounded divergence and
probability-density solutions is proved elsewhere:
`ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth` (`Flow/DiPernaLionsLinearGrowth.lean`,
linear growth, bounded densities; bounded `v` is `ae_eq_of_weakContinuityDensity_diPernaLions`),
with the commutator lemma in `Flow/DiPernaLionsCommutatorL1.lean` and renormalisation in
`Flow/DiPernaLionsRenormalizationBeta.lean`, and `ae_eq_of_weakContinuityDensity_diPernaLions_Lp`
(`Flow/DiPernaLionsLp.lean`, `L^p` densities).
The list below records what this file alone does not prove; still open overall: time-dependent
velocities, signed solutions, `L¹` densities, growth `v/(1+|x|) ∈ L¹ + L^∞`.

* **`C_{κ_ε}(u, v) → (u div v)` in `L¹_loc`** (equivalently `r_ε → 0`) for
  `v ∈ W^{1,1}_loc`, `u ∈ L^∞`. This needs continuity of translations in `L¹_loc`, the
  `L¹_loc` convergence of difference quotients `(v(· - ε z) - v)/ε → -Dv z` for Sobolev `v`
  (absolute continuity on lines), the moment identity `∫ z ⊗ ∇κ(z) dz = -Id`, and a density
  argument combined with the uniform bound `abs_dlCommutator_scaled_le` (which itself is only
  available for Lipschitz `v`). None of this is formalized in this file; it is
  `tendsto_lintegral_dlCommutator_sub` (`Flow/DiPernaLionsCommutatorL1.lean`).
* Renormalization (`β(u_ε)`), passage `ε → 0`, cut-offs and Gronwall, i.e. the
  `d ≥ 2` DiPerna–Lions uniqueness theorem (see the paragraph above). The one-dimensional case
  and the `W^{1,∞}` case are proved in `Flow/DiPernaLionsUniqueness.lean` by reduction to
  Lipschitz uniqueness.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff Convolution

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- The **mollified flux divergence** `(div(u v)) ⋆ κ (x) = ∫ u(y) Dκ(x - y) v(y) dy`: the
distributional divergence of the flux `u v` tested against `y ↦ κ(x - y)`. -/
noncomputable def mollDivFlux (κ u : (Fin d → ℝ) → ℝ) (v : (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∫ y, u y * fderiv ℝ κ (x - y) (v y)

/-- **Derivative of a mollification (Verified).** For locally integrable `u` and a `C¹`
compactly supported kernel `κ`, `D(κ ⋆ u)(x) h = ∫ u(y) Dκ(x - y) h dy`. -/
theorem fderiv_convolution_apply_eq {u κ : (Fin d → ℝ) → ℝ} (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ 1 κ) (hκc : HasCompactSupport κ) (x h : Fin d → ℝ) :
    fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x h =
      ∫ y, u y * fderiv ℝ κ (x - y) h := by
  have hd := hκc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hu x
  rw [hd.fderiv, convolution_eq_swap]
  have hex := (hκc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Fin d → ℝ))
    (hκ.continuous_fderiv (by simp)) hu x
  rw [ContinuousLinearMap.integral_apply hex.integrable_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp_rw [mul_comm (fderiv ℝ κ _ _)]

/-- **Commutator identification (Verified).** For locally integrable `u`, a `C¹` compactly
supported kernel `κ` and a velocity `v` such that the flux integrand
`y ↦ u(y) Dκ(x - y) v(y)` is integrable,
`C_κ(u, v)(x) = (div(u v)) ⋆ κ (x) - D(κ ⋆ u)(x) v(x)`, i.e. the kernel-form commutator
`dlCommutator` is the mollification commutator `(div(u v)) ⋆ κ - v ⬝ ∇(κ ⋆ u)`. -/
theorem dlCommutator_eq {u κ : (Fin d → ℝ) → ℝ} (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ 1 κ) (hκc : HasCompactSupport κ) {v : (Fin d → ℝ) → Fin d → ℝ}
    {x : Fin d → ℝ} (hint : Integrable fun y => u y * fderiv ℝ κ (x - y) (v y)) :
    dlCommutator κ u v x =
      mollDivFlux κ u v x - fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x (v x) := by
  rw [fderiv_convolution_apply_eq hu hκ hκc, dlCommutator, mollDivFlux]
  have hc : Continuous fun y => fderiv ℝ κ (x - y) (v x) :=
    ((hκ.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const
  have hcs : HasCompactSupport fun y => fderiv ℝ κ (x - y) (v x) := by
    refine ((hκc.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)).mono' fun y hy => ?_
    contrapose! hy
    have := image_eq_zero_of_notMem_tsupport hy
    simp only [Function.comp_apply, Homeomorph.subLeft_apply] at this
    simp [this]
  have hint2 : Integrable fun y => u y * fderiv ℝ κ (x - y) (v x) := by
    simpa [smul_eq_mul, mul_comm] using hu.integrable_smul_left_of_hasCompactSupport hc hcs
  rw [← integral_sub hint hint2]
  simp_rw [map_sub, mul_sub]

/-- **Mollified density solutions (Verified).** Let `u` solve `WeakContinuityDensity u v` and
let `κ` be `C²` with compact support. Then for every `x` and `t ≥ 0`, the mollification
`s ↦ (κ ⋆ u_s)(x) = ∫ κ(x - y) u_s(y) dy` has derivative `-(div(u_t v)) ⋆ κ (x)` at `t`
within `[0, ∞)` (test the equation with `y ↦ κ(x - y)`). -/
theorem hasDerivWithinAt_convolution_of_weakContinuityDensity {u : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} (h : WeakContinuityDensity u v) {κ : (Fin d → ℝ) → ℝ}
    (hκ : ContDiff ℝ 2 κ) (hκc : HasCompactSupport κ) (x : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u s) x)
      (-mollDivFlux κ (u t) v x) (Ici 0) t := by
  set ψ : (Fin d → ℝ) → ℝ := fun y => κ (x - y) with hψ
  have hψs : ContDiff ℝ 2 ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hκc.comp_homeomorph (Homeomorph.subLeft x)
  have hDψ : ∀ y w, fderiv ℝ ψ y w = -fderiv ℝ κ (x - y) w := by
    intro y w
    have h1 : HasFDerivAt (fun y : Fin d → ℝ => x - y)
        (-ContinuousLinearMap.id ℝ (Fin d → ℝ)) y := by
      simpa using (hasFDerivAt_const x y).sub (hasFDerivAt_id (𝕜 := ℝ) y)
    have h2 := ((hκ.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    rw [show ψ = κ ∘ HSub.hSub x from rfl, h2.fderiv]
    simp
  have hd := h ψ ⟨hψs, hψc⟩ t ht
  have hval : ∫ y, u t y * (v y ⬝ᵥ grad ψ y) = -mollDivFlux κ (u t) v x := by
    rw [mollDivFlux, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [dotProduct_comm, ← fderiv_apply_eq_grad_dotProduct, hDψ, mul_neg]
  rw [hval] at hd
  refine hd.congr (fun s _ => ?_) ?_ <;>
  · simp only [convolution_lsmul_swap, smul_eq_mul, hψ]
    simp_rw [mul_comm (κ _)]

/-- **The mollified continuity equation with commutator error (Verified).** Let `u` solve
`WeakContinuityDensity u v`, `κ` be `C²` with compact support, `t ≥ 0`, and assume `u_t` is
locally integrable and the flux integrand `y ↦ u_t(y) Dκ(x - y) v(y)` is integrable. Then
`u_κ(s) = κ ⋆ u_s` satisfies, at the point `x`,

  `∂ₜ u_κ(t)(x) = -D(κ ⋆ u_t)(x) v(x) - C_κ(u_t, v)(x)`

(derivative within `[0, ∞)`): the transport equation for `u_κ` up to the commutator
`dlCommutator κ (u t) v x`. -/
theorem hasDerivWithinAt_convolution_eq_transport_add_commutator
    {u : ℝ → (Fin d → ℝ) → ℝ} {v : (Fin d → ℝ) → Fin d → ℝ} (h : WeakContinuityDensity u v)
    {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ 2 κ) (hκc : HasCompactSupport κ) (x : Fin d → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hut : LocallyIntegrable (u t))
    (hint : Integrable fun y => u t y * fderiv ℝ κ (x - y) (v y)) :
    HasDerivWithinAt (fun s => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u s) x)
      (-fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u t) x (v x) -
        dlCommutator κ (u t) v x) (Ici 0) t := by
  have hd := hasDerivWithinAt_convolution_of_weakContinuityDensity h hκ hκc x ht
  rw [dlCommutator_eq hut (hκ.of_le (by norm_num)) hκc hint]
  convert hd using 1
  ring

end NoiseScore
end FormalizeSampling
