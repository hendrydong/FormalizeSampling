module

public import FormalizeSampling.Samplers.RGOCouplingWeakDefs
public import FormalizeSampling.Flow.FokkerPlanckExistenceLinear
public import FormalizeSampling.Flow.FokkerPlanckUniquenessUnbounded
public import FormalizeSampling.Identities.DensityStein

/-!
# The RGO law of a smooth convex potential as a stationary Langevin law

Status: **Verified** (no named hypotheses).

Let `g : (Fin d → ℝ) → ℝ` satisfy `SmoothConvexBdd g` (convex, `C²`, bounded first and second
derivatives; `∫ e^{-g} < ∞` is **not** assumed) and `η > 0`. The restricted Gaussian oracle
`RGO(y) ∝ exp(-g(x) - |x - y|² / (2η)) dx` (`rgoKernelPi g η y`) is the invariant law of the
overdamped Langevin dynamics `dX = b_y(X) dt + √2 dW` with drift
`b_y(x) = -∇g(x) - (x - y) / η` (`rgoDrift`). This file proves the analytic facts used by the
synchronous Euler–Maruyama coupling of `Samplers/RGOCouplingLangevin.lean`.

## Main results

* `isMarkovKernel_rgoKernelPi'`: the RGO kernel of `g` is a Markov kernel (the normaliser is
  finite by the affine lower bound `g x ≥ g 0 - B ‖x‖` and the Gaussian factor).
* `lintegral_exp_norm_lt_top`: `∫ exp ‖x‖ dRGO(y) < ∞`.
* `integral_generator_rgoKernelPi_eq_zero`, `weakFokkerPlanck_rgoKernelPi`: stationarity; the
  constant curve `t ↦ RGO(y)` solves `WeakFokkerPlanck` with drift `b_y` and `D = 1`
  (integration by parts against `exp(-g - |· - y|² / (2η))`).
* `exists_lipschitzWith_rgoDrift`: `b_y` is globally Lipschitz.
* `weakTendsto_emCurve_rgoKernelPi`: the dyadic Euler–Maruyama laws of `b_y` started at
  `RGO(y)` converge weakly to `RGO(y)` at every time `t ≥ 0` (existence of the weak
  Fokker–Planck limit for Lipschitz drifts plus uniqueness for linear-plus-bounded drifts).

## Not proved here

* Rates for the Euler–Maruyama bias, long-time convergence of the Langevin dynamics.
* Anything for non-smooth or non-convex `g`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingWeak
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingLangevin

variable {d : ℕ}

/-- Completing the square: `c ‖x‖ - |x - y|² / (2η) ≤ c ‖y‖ + c² η - |x - y|² / (4η)`
for `c ≥ 0`, `η > 0`. -/
theorem mul_norm_sub_sqDist_le {c η : ℝ} (hc : 0 ≤ c) (hη : 0 < η) (x y : Fin d → ℝ) :
    c * ‖x‖ - sqDist x y / (2 * η) ≤ c * ‖y‖ + c ^ 2 * η - sqDist x y / (4 * η) := by
  have h1 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have := norm_add_le y (x - y); rwa [add_sub_cancel] at this
  have h2 := sq_norm_sub_le_sqDist x y
  have h3 : c * ‖x - y‖ ≤ c ^ 2 * η + sqDist x y / (4 * η) := by
    have : c * ‖x - y‖ ≤ c ^ 2 * η + ‖x - y‖ ^ 2 / (4 * η) := by
      rw [← sub_nonneg]
      have e : c ^ 2 * η + ‖x - y‖ ^ 2 / (4 * η) - c * ‖x - y‖ =
          (2 * c * η - ‖x - y‖) ^ 2 / (4 * η) := by field_simp; ring
      rw [e]; positivity
    exact this.trans (by gcongr)
  have h4 : sqDist x y / (2 * η) = sqDist x y / (4 * η) + sqDist x y / (4 * η) := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]

/-! ### The RGO kernel of a smooth convex potential -/

variable {g : (Fin d → ℝ) → ℝ} {η : ℝ}

/-- A gradient bound for `g` can be taken nonnegative. -/
theorem exists_fderiv_bound (hg : SmoothConvexBdd g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖fderiv ℝ g x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hg.2.2.1
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩

/-- A function with gradient bounded by `B` grows at most linearly: `g 0 - B ‖x‖ ≤ g x`. -/
theorem lower_bound_of_fderiv (hg : SmoothConvexBdd g) {B : ℝ}
    (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B) (x : Fin d → ℝ) : g 0 - B * ‖x‖ ≤ g x := by
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hg.2.1.differentiable two_ne_zero) z) (fun z _ => hB z) (mem_univ 0)
    (mem_univ x)
  rw [sub_zero] at h
  have := neg_abs_le (g x - g 0)
  rw [← Real.norm_eq_abs] at this
  linarith

/-- The RGO weight `x ↦ exp(c ‖x‖) exp(-g x - |x - y|² / (2η))` is integrable (`c ≥ 0`). -/
theorem integrable_exp_norm_mul (hg : SmoothConvexBdd g) (hη : 0 < η) {c : ℝ}
    (hc : 0 ≤ c) (y : Fin d → ℝ) :
    Integrable (fun x => Real.exp (c * ‖x‖) * Real.exp (-g x - sqDist x y / (2 * η))) := by
  obtain ⟨B, hB0, hB⟩ := (exists_fderiv_bound hg)
  have hcont : Continuous g := hg.2.1.continuous
  have hsq : Continuous fun x : Fin d → ℝ => sqDist x y :=
    continuous_sqDist.comp (continuous_id.prodMk continuous_const)
  refine Integrable.mono' ((integrable_exp_neg_mul_sqDist (c := 1 / (4 * η)) (by positivity)
    y).const_mul (Real.exp (-g 0 + (B + c) * ‖y‖ + (B + c) ^ 2 * η))) ?_
    (ae_of_all _ fun x => ?_)
  · exact ((continuous_const.mul continuous_norm).rexp.mul
      ((hcont.neg.sub (hsq.div_const _)).rexp)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add,
      Real.exp_le_exp]
    have h1 := (lower_bound_of_fderiv hg) hB x
    have h2 := mul_norm_sub_sqDist_le (add_nonneg hB0 hc) hη x y
    have : 1 / (4 * η) * sqDist x y = sqDist x y / (4 * η) := by ring
    nlinarith

/-- The RGO weight `x ↦ exp(-g x - |x - y|² / (2η))` is integrable. -/
theorem integrable_weight (hg : SmoothConvexBdd g) (hη : 0 < η)
    (y : Fin d → ℝ) : Integrable (fun x => Real.exp (-g x - sqDist x y / (2 * η))) := by
  simpa using (integrable_exp_norm_mul hg) hη le_rfl y

/-- The RGO normaliser of a smooth convex potential is positive. -/
theorem rgoNormalizerPi_pos (hg : SmoothConvexBdd g) (hη : 0 < η)
    (y : Fin d → ℝ) : 0 < rgoNormalizerPi g η y :=
  integral_exp_pos ((integrable_weight hg) hη y)

/-- **The RGO kernel of a smooth convex potential is Markov** (`η > 0`; no integrability of
`e^{-g}` is needed). -/
theorem isMarkovKernel_rgoKernelPi' (hg : SmoothConvexBdd g) (hη : 0 < η) :
    IsMarkovKernel (rgoKernelPi g η) := by
  refine ReverseKernel.isMarkovKernel_densityKernel
    (measurable_rgoDensityPi_of_continuous hg.2.1.continuous) fun y => ?_
  have hZ := rgoNormalizerPi_pos hg hη y
  show ∫⁻ x, ENNReal.ofReal (Real.exp (-g x - sqDist x y / (2 * η)) / rgoNormalizerPi g η y)
    = 1
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_weight hg hη y).div_const _)
    (ae_of_all _ fun x => div_nonneg (Real.exp_pos _).le hZ.le)]
  rw [integral_div, ← rgoNormalizerPi, div_self hZ.ne', ENNReal.ofReal_one]

/-- **Exponential moment of the RGO kernel.** `∫⁻ exp ‖x‖ d RGO(y) < ∞` (sup norm). -/
theorem lintegral_exp_norm_lt_top (hg : SmoothConvexBdd g) (hη : 0 < η)
    (y : Fin d → ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ‖x‖) ∂(rgoKernelPi g η y) < ∞ := by
  have hZ := (rgoNormalizerPi_pos hg) hη y
  have hm : Measurable fun x => ENNReal.ofReal (rgoDensityPi g η y x) :=
    (measurable_rgoDensityPi_of_continuous hg.2.1.continuous).comp measurable_prodMk_left
  rw [rgoKernelPi_apply_of_continuous hg.2.1.continuous, lintegral_withDensity_eq_lintegral_mul₀
    hm.aemeasurable (by fun_prop)]
  have hint := ((integrable_exp_norm_mul hg) hη zero_le_one y).div_const
    (rgoNormalizerPi g η y)
  refine lt_of_eq_of_lt (lintegral_congr fun x => ?_) hint.lintegral_lt_top
  simp only [Pi.mul_apply, rgoDensityPi, one_mul]
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le)]
  congr 1; ring

/-! ### Stationarity of the RGO law for its Langevin dynamics -/

/-- The overdamped Langevin drift of the RGO potential `V_y(x) = g(x) + |x - y|² / (2η)`:
`b_y(x) = -∇V_y(x) = -∇g(x) - (x - y) / η`. -/
noncomputable def rgoDrift (g : (Fin d → ℝ) → ℝ) (η : ℝ) (y x : Fin d → ℝ) : Fin d → ℝ :=
  -grad g x - η⁻¹ • (x - y)

/-- Fréchet derivative of the squared Euclidean distance to `y`. -/
theorem hasFDerivAt_sqDist (x y : Fin d → ℝ) :
    HasFDerivAt (fun z : Fin d → ℝ => sqDist z y)
      (∑ j, (2 * (x j - y j)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
      x := by
  unfold sqDist
  refine HasFDerivAt.fun_sum fun j _ => ?_
  have := ((hasFDerivAt_apply (𝕜 := ℝ) j x).sub_const (y j)).pow 2
  convert this using 1
  ext v
  simp

/-- `∂ᵢ |x - y|² = 2 (xᵢ - yᵢ)`. -/
theorem partialDeriv_sqDist (i : Fin d) (x y : Fin d → ℝ) :
    partialDeriv i (fun z => sqDist z y) x = 2 * (x i - y i) := by
  rw [partialDeriv, (hasFDerivAt_sqDist x y).fderiv]
  simp [Pi.single_apply]

/-- **The score of the RGO weight is the Langevin drift**: for differentiable `g`,
`∇ log exp(-g - |· - y|² / (2η)) = b_y`. -/
theorem score_weight (hg : Differentiable ℝ g) (y x : Fin d → ℝ) :
    score (fun z => Real.exp (-g z - sqDist z y / (2 * η))) x = rgoDrift g η y x := by
  simp only [score, Real.log_exp]
  funext i
  have h := (hg x).hasFDerivAt.neg.sub ((hasFDerivAt_sqDist x y).mul_const (2 * η)⁻¹)
  simp only [div_eq_mul_inv]
  simp only [grad, partialDeriv]
  rw [show (fun z => -g z - sqDist z y * (2 * η)⁻¹) =
    (-g - fun z => sqDist z y * (2 * η)⁻¹) from rfl, h.fderiv]
  simp [rgoDrift, grad, partialDeriv, Pi.single_apply]
  ring

section Stationary

open NoiseScore WeakFokkerPlanckOU

/-- The Langevin drift `b_y` of a `C¹` potential is continuous. -/
theorem continuous_rgoDrift (hg : ContDiff ℝ 2 g) (η : ℝ) (y : Fin d → ℝ) :
    Continuous (rgoDrift g η y) :=
  (continuous_grad hg).neg.sub (by fun_prop)

/-- **Integration by parts against the RGO weight.** For `g` smooth convex with bounded
derivatives and a `C²` compactly supported `φ`:
`∫ (b_y ⬝ ∇φ + Δφ) exp(-g - |· - y|² / (2η)) dx = 0`. -/
theorem integral_generator_mul_weight_eq_zero (hg : SmoothConvexBdd g) (y : Fin d → ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    ∫ x, (rgoDrift g η y x ⬝ᵥ grad φ x + 1 * laplacian φ x) *
      Real.exp (-g x - sqDist x y / (2 * η)) = 0 := by
  set p : (Fin d → ℝ) → ℝ := fun z => Real.exp (-g z - sqDist z y / (2 * η)) with hp
  have hpos : ∀ x, 0 < p x := fun x => Real.exp_pos _
  have hsq : ContDiff ℝ 1 fun z : Fin d → ℝ => sqDist z y := by unfold sqDist; fun_prop
  have hpC : ContDiff ℝ 1 p := ((hg.2.1.of_le one_le_two).neg.sub (hsq.div_const _)).exp
  have hstein :=
    DensityStein.integral_divergence_mul_eq_neg_integral_dotProduct_score_of_hasCompactSupport
    (f := grad φ) hpos hpC (fun i => contDiff_partialDeriv hφ.1 i)
    (fun i => hasCompactSupport_partialDeriv hφ.2 i)
  have hscore : ∀ x, score p x = rgoDrift g η y x := fun x =>
    score_weight (hg.2.1.differentiable two_ne_zero) y x
  have hdiv : ∀ x, divergence (grad φ) x = laplacian φ x := fun x => rfl
  simp_rw [hscore, hdiv] at hstein
  have hb := continuous_rgoDrift hg.2.1 η y
  have hint1 : Integrable fun x => (rgoDrift g η y x ⬝ᵥ grad φ x) * p x := by
    refine ((hb.dotProduct (continuous_grad hφ.1)).mul
      hpC.continuous).integrable_of_hasCompactSupport (HasCompactSupport.intro hφ.2 fun x hx => ?_)
    simp [(grad_laplacian_eq_zero_of_notMem_tsupport hx).1]
  have hint2 : Integrable fun x => laplacian φ x * p x := by
    refine ((continuous_laplacian hφ.1).mul hpC.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hφ.2 fun x hx => ?_)
    simp [(grad_laplacian_eq_zero_of_notMem_tsupport hx).2]
  simp_rw [one_mul, add_mul]
  rw [integral_add hint1 hint2, hstein]
  simp_rw [dotProduct_comm (grad φ _)]
  ring

/-- **Stationarity.** The generator of the Langevin dynamics `dX = b_y(X) dt + √2 dW` has zero
mean under `RGO(y)`: `∫ (b_y ⬝ ∇φ + Δφ) dRGO(y) = 0` for every `C²` compactly supported `φ`. -/
theorem integral_generator_rgoKernelPi_eq_zero (hg : SmoothConvexBdd g) (y : Fin d → ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    ∫ x, (rgoDrift g η y x ⬝ᵥ grad φ x + 1 * laplacian φ x) ∂(rgoKernelPi g η y) = 0 := by
  rw [integral_rgoKernelPi_of_continuous hg.2.1.continuous,
    integral_generator_mul_weight_eq_zero hg y hφ, zero_div]

/-- **The RGO law is a stationary weak Fokker–Planck solution** of the Langevin dynamics
`dX = b_y(X) dt + √2 dW` (`D = 1`): the constant curve `t ↦ RGO(y)` satisfies
`WeakFokkerPlanck`. -/
theorem weakFokkerPlanck_rgoKernelPi (hg : SmoothConvexBdd g) (y : Fin d → ℝ) :
    WeakFokkerPlanck (fun _ => rgoKernelPi g η y) (fun _ => rgoDrift g η y) 1 := by
  intro φ hφ t _
  rw [integral_generator_rgoKernelPi_eq_zero hg y hφ]
  exact hasDerivWithinAt_const _ _ _

end Stationary

/-! ### Identification of the Euler–Maruyama limit -/

/-- A bound on the second derivative of `g` can be taken nonnegative and stated for
`fderiv (fderiv g)`. -/
theorem exists_fderiv_fderiv_bound (hg : SmoothConvexBdd g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L := by
  obtain ⟨L, hL⟩ := hg.2.2.2
  refine ⟨max L 0, le_max_right _ _, fun x => ?_⟩
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact (hL x).trans (le_max_left _ _)

/-- The standard basis vectors have sup norm at most one. -/
theorem norm_single_le_one (i : Fin d) : ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Derivative of a partial derivative of a `C²` function. -/
theorem hasFDerivAt_partialDeriv (hg : ContDiff ℝ 2 g) (i : Fin d) (x : Fin d → ℝ) :
    HasFDerivAt (partialDeriv i g) ((fderiv ℝ (fderiv ℝ g) x).flip (Pi.single i 1)) x := by
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) x)
  have h2 : HasFDerivAt (fun y => fderiv ℝ g y (Pi.single i 1))
      ((fderiv ℝ (fderiv ℝ g) x).flip (Pi.single i 1)) x := by simpa using this
  exact h2

/-- The coordinate gradient of `g` is bounded by the bound on `fderiv g` (sup norms). -/
theorem norm_grad_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B) (x : Fin d → ℝ) :
    ‖grad g x‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB0).2 fun i => ?_
  calc ‖grad g x i‖ = ‖fderiv ℝ g x (Pi.single i 1)‖ := rfl
    _ ≤ ‖fderiv ℝ g x‖ * ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B * 1 := mul_le_mul (hB x) (norm_single_le_one i) (norm_nonneg _) hB0
    _ = B := mul_one B

/-- The coordinate gradient of a smooth convex potential with bounded second derivative is
Lipschitz (sup norms). -/
theorem exists_lipschitzWith_grad (hg : SmoothConvexBdd g) :
    ∃ L : ℝ≥0, LipschitzWith L (grad g) := by
  obtain ⟨L, hL0, hL⟩ := exists_fderiv_fderiv_bound hg
  refine ⟨L.toNNReal, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := partialDeriv i g) (C := L)
    (fun z _ => (hasFDerivAt_partialDeriv hg.2.1 i z).differentiableAt) (fun z _ => ?_)
    (mem_univ x') (mem_univ x)
  · rw [(hasFDerivAt_partialDeriv hg.2.1 i z).fderiv]
    calc ‖(fderiv ℝ (fderiv ℝ g) z).flip (Pi.single i 1)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ g) z).flip‖ * ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * 1 := by
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul (hL z) (norm_single_le_one i) (norm_nonneg _) hL0
      _ = L := mul_one L

/-- The Langevin drift `b_y` is Lipschitz (sup norms). -/
theorem exists_lipschitzWith_rgoDrift (hg : SmoothConvexBdd g) (η : ℝ) (y : Fin d → ℝ) :
    ∃ L : ℝ≥0, LipschitzWith L (rgoDrift g η y) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_grad hg
  refine ⟨L + ‖η⁻¹‖₊, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
  have h1 := hL.dist_le_mul x x'
  rw [dist_eq_norm] at h1 ⊢
  have e : rgoDrift g η y x - rgoDrift g η y x' =
      -(grad g x - grad g x') - η⁻¹ • (x - x') := by
    simp only [rgoDrift, smul_sub]; abel
  rw [e, dist_eq_norm, NNReal.coe_add, coe_nnnorm, add_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rwa [norm_neg]
  · rw [norm_smul]

/-- **Euler–Maruyama from the RGO law converges back to it.** For `g` smooth convex with
bounded derivatives, `η > 0`, `y` and `t ≥ 0`, the dyadic Euler–Maruyama laws of the Langevin
dynamics `dX = b_y(X) dt + √2 dW` started at `RGO(y)` converge weakly to `RGO(y)` (existence:
`exists_weakFokkerPlanck_lipschitz`; identification: stationarity and uniqueness for
linear-plus-bounded drifts). -/
theorem weakTendsto_emCurve_rgoKernelPi (hg : SmoothConvexBdd g) (hη : 0 < η)
    (y : Fin d → ℝ) (hb : Measurable (rgoDrift g η y)) {t : ℝ} (ht : 0 ≤ t) :
    WeakTendsto (fun n => FokkerPlanckExistence.emCurve (rgoDrift g η y) hb 1
      (rgoKernelPi g η y) n t) (rgoKernelPi g η y) := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  obtain ⟨L, hL⟩ := exists_lipschitzWith_rgoDrift hg η y
  obtain ⟨ν, h0, -, hfp, htd⟩ :=
    FokkerPlanckExistence.exists_weakFokkerPlanck_lipschitz hL one_pos (rgoKernelPi g η y)
  obtain ⟨B, hB0, hB⟩ := exists_fderiv_bound hg
  have heq : (ν t : Measure (Fin d → ℝ)) = rgoKernelPi g η y := by
    refine FokkerPlanckUniqueness.eq_of_weakFokkerPlanck_linear_add_bounded
      (ρ := fun t => (ν t : Measure (Fin d → ℝ))) (ρ' := fun _ => rgoKernelPi g η y)
      (a := η⁻¹) (B := B + ‖η⁻¹ • y‖) (inv_nonneg.2 hη.le) one_pos
      (fun _ _ => continuous_rgoDrift hg.2.1 η y) (fun _ _ x => ?_) (fun _ _ => inferInstance)
      (fun _ _ => inferInstance) hfp (weakFokkerPlanck_rgoKernelPi hg y) h0 t ht
    have e : rgoDrift g η y x + η⁻¹ • x = -grad g x + η⁻¹ • y := by
      simp only [rgoDrift, smul_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by rw [norm_neg]; gcongr; exact norm_grad_le hB0 hB x)
  intro f hf N hN
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (htd t)
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf N fun x => by
      rw [Real.norm_eq_abs]; exact hN x)
  rw [heq] at h
  exact h

end FormalizeSampling.RGOCouplingLangevin
