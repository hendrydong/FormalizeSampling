module

public import Mathlib.Order.Interval.Basic
public import FormalizeSampling.Flow.FokkerPlanckExistenceStep

/-!
# One Euler–Maruyama step with frozen drift: the generator identity

Status: **Verified.** For a `C²` compactly supported test function `φ`, `D > 0` and a frozen
drift `v : ℝᵈ`, the map `s ↦ E φ(x + s v + √(2Ds) Z)` (`Z ∼ N(0, I_d)`) is differentiable at
every `s > 0` with derivative `E[(frozenGen D φ v)(x + s v + √(2Ds) Z)]`, where
`frozenGen D φ v = Dφ[v] + D Δφ` (`hasDerivAt_integral_drift`: differentiation under the integral
and the Gaussian integration by parts `integral_fderiv_apply_self`, as in
`Flow/WeakFokkerPlanckOU`). Hence, for `h ≥ 0`,

  `E φ(x + h v + √(2Dh) Z) - φ(x) = ∫₀ʰ E[(frozenGen D φ v)(x + s v + √(2Ds) Z)] ds`
  (`integral_drift_sub`).

With the affine modulus of continuity `exists_modulus_bound`, this is the input of the generator
estimates for Euler–Maruyama steps in `Flow/FokkerPlanckExistenceLyap`
(`abs_integral_drift_generator_le`, `emOp_generator_lyap`). Only continuity of the second
derivatives of `φ` is used (no `C³` assumption).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace FormalizeSampling.FokkerPlanckExistence
open FormalizeSampling.HeatKernelPi FormalizeSampling.WeakFokkerPlanckOU NoiseScore

variable {d : ℕ}

/-- The generator of `dX = v dt + √(2D) dW` with **frozen** drift `v`, written with the
Fréchet derivative: `frozenGen D φ v y = Dφ(y)[v] + D Δφ(y)` (`= v ⬝ ∇φ(y) + D Δφ(y)`). -/
noncomputable def frozenGen (D : ℝ) (φ : (Fin d → ℝ) → ℝ) (v y : Fin d → ℝ) : ℝ :=
  fderiv ℝ φ y v + D * laplacian φ y

/-- **Uniform continuity as an affine modulus.** A bounded uniformly continuous map satisfies,
for every `ε > 0`, `‖f y - f x‖ ≤ ε + K ‖y - x‖` for some `K ≥ 0` and all `x, y`. -/
theorem exists_modulus_bound {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {f : E → F} (hf : UniformContinuous f) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) {ε : ℝ}
    (hε : 0 < ε) : ∃ K, 0 ≤ K ∧ ∀ x y, ‖f y - f x‖ ≤ ε + K * ‖y - x‖ := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1 hf ε hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨2 * M / δ, by positivity, fun x y => ?_⟩
  have hK : 0 ≤ 2 * M / δ * ‖y - x‖ := by positivity
  by_cases hxy : ‖y - x‖ < δ
  · have := hδf (a := y) (b := x) (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at this
    linarith
  · push Not at hxy
    have h1 : ‖f y - f x‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hM y, hM x])
    have h2 : 2 * M ≤ 2 * M / δ * ‖y - x‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; nlinarith
    linarith

section Drift

variable {φ : (Fin d → ℝ) → ℝ}

/-- **Gaussian integration by parts in the noise direction.** For `φ ∈ C²_c`, `w : ℝᵈ` and
`σ ≠ 0`, `E[Dφ(w + σ Z)[Z]] = σ E[Δφ(w + σ Z)]` for `Z ∼ N(0, I_d)`. -/
theorem integral_fderiv_apply_self (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (w : Fin d → ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    ∫ z, fderiv ℝ φ (w + σ • z) z ∂stdGauss =
      σ * ∫ z, laplacian φ (w + σ • z) ∂stdGauss := by
  have hdc : ∀ i, HasCompactSupport (partialDeriv i φ) := fun i =>
    hφc.fderiv_apply ℝ (Pi.single i 1)
  have hd2 : ∀ i, HasCompactSupport (partialDeriv i (partialDeriv i φ)) := fun i =>
    (hdc i).fderiv_apply ℝ (Pi.single i 1)
  have e1 : ∀ z, fderiv ℝ φ (w + σ • z) z = ∑ i, z i * partialDeriv i φ (w + σ • z) :=
    fun z => by rw [← dotProduct_grad]; rfl
  simp_rw [e1]
  simp only [laplacian]
  have hi1 : ∀ i ∈ Finset.univ, Integrable
      (fun z : Fin d → ℝ => z i * partialDeriv i φ (w + σ • z)) stdGauss := by
    intro i _
    obtain ⟨C, hC⟩ :=
      (contDiff_partialDeriv hφ i).continuous.bounded_above_of_compact_support (hdc i)
    exact ((integrable_coord i).norm.const_mul C).mono'
      ((continuous_apply i).mul ((contDiff_partialDeriv hφ i).continuous.comp
        (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have hi2 : ∀ i ∈ Finset.univ, Integrable
      (fun z : Fin d → ℝ => partialDeriv i (partialDeriv i φ) (w + σ • z)) stdGauss := by
    intro i _
    obtain ⟨C, hC⟩ := (continuous_partialDeriv2 hφ i i).bounded_above_of_compact_support (hd2 i)
    exact Integrable.of_bound ((continuous_partialDeriv2 hφ i i).comp
      (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hC _)
  rw [integral_finsetSum _ hi1, integral_finsetSum _ hi2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    integral_coord_mul_comp (contDiff_partialDeriv hφ i) (hdc i) w hσ i

/-- For bounded continuous `ψ`, `t ↦ E ψ(x + t v + √(2Dt) Z)` is continuous on `ℝ` (dominated
convergence; `√` truncates negative times). -/
theorem continuous_integral_drift {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) {C : ℝ}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (x v : Fin d → ℝ) (D : ℝ) :
    Continuous fun t : ℝ => ∫ z, ψ (x + t • v + Real.sqrt (2 * D * t) • z) ∂stdGauss :=
  continuous_of_dominated (bound := fun _ => C)
    (fun t => (hψ.comp (by fun_prop)).aestronglyMeasurable)
    (fun t => ae_of_all _ fun z => hC _) (integrable_const C)
    (ae_of_all _ fun z => hψ.comp (by fun_prop))

/-- `frozenGen D φ v` is continuous and bounded for `φ ∈ C²_c`. -/
theorem continuous_frozenGen (hφ : ContDiff ℝ 2 φ) (D : ℝ) (v : Fin d → ℝ) :
    Continuous (frozenGen D φ v) :=
  ((hφ.continuous_fderiv two_ne_zero).clm_apply continuous_const).add
    (continuous_const.mul (continuous_laplacian hφ))

/-- `Δφ` has compact support when `φ` does. -/
theorem hasCompactSupport_laplacian (hφc : HasCompactSupport φ) :
    HasCompactSupport (laplacian φ) := by
  have h := hasCompactSupport_ouGen hφc 0 1
  have e : ouGen 0 1 φ = laplacian φ := funext fun y => by simp [ouGen]
  rwa [e] at h

/-- `frozenGen D φ v` is bounded for `φ ∈ C²_c`. -/
theorem exists_bound_frozenGen (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (D : ℝ)
    (v : Fin d → ℝ) : ∃ C, ∀ y, ‖frozenGen D φ v y‖ ≤ C := by
  obtain ⟨M, hM⟩ := (hφ.continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨ML, hML⟩ := (continuous_laplacian hφ).bounded_above_of_compact_support
    (hasCompactSupport_laplacian hφc)
  refine ⟨M * ‖v‖ + |D| * ML, fun y => ?_⟩
  calc ‖frozenGen D φ v y‖ ≤ ‖fderiv ℝ φ y v‖ + ‖D * laplacian φ y‖ := norm_add_le _ _
    _ ≤ M * ‖v‖ + |D| * ML := by
        refine add_le_add (((fderiv ℝ φ y).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _))) ?_
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hML y) (abs_nonneg _)

/-- **Time derivative with frozen drift (`t₀ > 0`).** For `φ ∈ C²_c`, `D > 0` and `x, v : ℝᵈ`,
`d/dt E φ(x + t v + √(2Dt) Z) = E[(frozenGen D φ v)(x + t v + √(2Dt) Z)]` at `t₀ > 0`
(differentiation under the integral, then Gaussian integration by parts). -/
theorem hasDerivAt_integral_drift (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (x v : Fin d → ℝ) {D : ℝ} (hD : 0 < D) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => ∫ z, φ (x + t • v + Real.sqrt (2 * D * t) • z) ∂stdGauss)
      (∫ z, frozenGen D φ v (x + t₀ • v + Real.sqrt (2 * D * t₀) • z) ∂stdGauss) t₀ := by
  set σ : ℝ → ℝ := fun t => Real.sqrt (2 * D * t) with hσdef
  set σ' : ℝ → ℝ := fun t => 2 * D * 1 / (2 * Real.sqrt (2 * D * t)) with hσ'def
  have hpos : ∀ t, 0 < t → 0 < 2 * D * t := fun t ht => by positivity
  have hσd : ∀ t, 0 < t → HasDerivAt σ (σ' t) t := fun t ht =>
    ((hasDerivAt_id' t).const_mul (2 * D)).sqrt (hpos t ht).ne'
  have hK : closedBall t₀ (t₀ / 2) ⊆ Ioi 0 := by
    intro t ht
    rw [mem_closedBall, Real.dist_eq, abs_le] at ht
    simp only [mem_Ioi]
    linarith [ht.1]
  have hσ'c : ContinuousOn σ' (closedBall t₀ (t₀ / 2)) := by
    refine continuousOn_const.div (continuousOn_const.mul
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).continuousOn)
      fun t ht => ?_
    have := Real.sqrt_pos.2 (hpos t (hK ht))
    positivity
  obtain ⟨S', hS'⟩ := (isCompact_closedBall t₀ (t₀ / 2)).exists_bound_of_continuousOn hσ'c
  obtain ⟨M, hM⟩ := (hφ.continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hn : Integrable (fun z : Fin d → ℝ => ‖z‖) stdGauss := integrable_norm_stdGauss
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := stdGauss)
    (F := fun t z => φ (x + t • v + σ t • z))
    (F' := fun t z => fderiv ℝ φ (x + t • v + σ t • z) (v + σ' t • z)) (x₀ := t₀)
    (bound := fun z => M * (‖v‖ + S' * ‖z‖))
    (ball_mem_nhds t₀ (by linarith : (0 : ℝ) < t₀ / 2))
    (Eventually.of_forall fun t => (hφ.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hφ.continuous.comp (by fun_prop)).aestronglyMeasurable C
      (ae_of_all _ fun z => hC _))
    (((hφ.continuous_fderiv two_ne_zero).comp (by fun_prop)).clm_apply
      (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z t ht => ?_)
    (((integrable_const _).add (hn.const_mul S')).const_mul M)
    (ae_of_all _ fun z t ht => ?_)
  · refine key.2.congr_deriv ?_
    have hs : σ t₀ ≠ 0 := (Real.sqrt_pos.2 (hpos t₀ ht₀)).ne'
    have hss : σ' t₀ * σ t₀ = D := by
      simp only [hσ'def, hσdef]
      field_simp
    obtain ⟨ML, hML⟩ := (continuous_laplacian hφ).bounded_above_of_compact_support
      (hasCompactSupport_laplacian hφc)
    have hcY : Continuous fun z : Fin d → ℝ => x + t₀ • v + σ t₀ • z := by fun_prop
    have hfd := hφ.continuous_fderiv two_ne_zero
    have I1 : Integrable (fun z => fderiv ℝ φ (x + t₀ • v + σ t₀ • z) v) stdGauss :=
      Integrable.of_bound ((hfd.comp hcY).clm_apply continuous_const).aestronglyMeasurable
        (M * ‖v‖) (ae_of_all _ fun z => ((fderiv ℝ φ _).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))
    have I2 : Integrable (fun z => fderiv ℝ φ (x + t₀ • v + σ t₀ • z) z) stdGauss :=
      (hn.const_mul M).mono' ((hfd.comp hcY).clm_apply continuous_id).aestronglyMeasurable
        (ae_of_all _ fun z => ((fderiv ℝ φ _).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))
    have IL : Integrable (fun z => laplacian φ (x + t₀ • v + σ t₀ • z)) stdGauss :=
      Integrable.of_bound ((continuous_laplacian hφ).comp hcY).aestronglyMeasurable ML
        (ae_of_all _ fun z => hML _)
    have hpt : ∀ z, fderiv ℝ φ (x + t₀ • v + σ t₀ • z) (v + σ' t₀ • z) =
        fderiv ℝ φ (x + t₀ • v + σ t₀ • z) v +
          σ' t₀ * fderiv ℝ φ (x + t₀ • v + σ t₀ • z) z := fun z => by
      rw [map_add, map_smul, smul_eq_mul]
    simp only [frozenGen]
    simp_rw [hpt]
    rw [integral_add I1 (I2.const_mul _), integral_add I1 (IL.const_mul _), integral_const_mul,
      integral_const_mul, integral_fderiv_apply_self hφ hφc (x + t₀ • v) hs, ← mul_assoc, hss]
  · have htK : t ∈ closedBall t₀ (t₀ / 2) := ball_subset_closedBall ht
    have h2 : ‖σ' t • z‖ ≤ S' * ‖z‖ := by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hS' t htK) (norm_nonneg _)
    have h1 : ‖v + σ' t • z‖ ≤ ‖v‖ + S' * ‖z‖ := (norm_add_le _ _).trans (by linarith)
    exact ((fderiv ℝ φ _).le_opNorm _).trans (mul_le_mul (hM _) h1 (norm_nonneg _) hM0)
  · have ht0 : 0 < t := hK (ball_subset_closedBall ht)
    have hY : HasDerivAt (fun t : ℝ => x + t • v + σ t • z) (v + σ' t • z) t := by
      have := (((hasDerivAt_id t).smul_const v).const_add x).add ((hσd t ht0).smul_const z)
      rw [one_smul] at this
      exact this
    exact ((hφ.differentiable two_ne_zero _).hasFDerivAt.comp_hasDerivAt t hY)

/-- **Integrated form (FTC).** For `φ ∈ C²_c`, `D > 0`, `x, v : ℝᵈ` and `h ≥ 0`,
`E φ(x + h v + √(2Dh) Z) - φ(x) = ∫₀ʰ E[(frozenGen D φ v)(x + s v + √(2Ds) Z)] ds`. -/
theorem integral_drift_sub (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (x v : Fin d → ℝ) {D : ℝ} (hD : 0 < D) {h : ℝ} (hh : 0 ≤ h) :
    ∫ z, φ (x + h • v + Real.sqrt (2 * D * h) • z) ∂stdGauss - φ x =
      ∫ s in (0 : ℝ)..h,
        ∫ z, frozenGen D φ v (x + s • v + Real.sqrt (2 * D * s) • z) ∂stdGauss := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨CG, hCG⟩ := exists_bound_frozenGen hφ hφc D v
  have hg := continuous_integral_drift hφ.continuous hC x v D
  have hH := continuous_integral_drift (continuous_frozenGen hφ D v) hCG x v D
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hh hg.continuousOn
    (fun s hs => hasDerivAt_integral_drift hφ hφc x v hD hs.1) (hH.intervalIntegrable _ _)]
  simp

end Drift

end FormalizeSampling.FokkerPlanckExistence
