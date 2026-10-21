module

public import Mathlib.MeasureTheory.Function.Floor
public import FormalizeSampling.Flow.FokkerPlanckExistenceCauchy
public import FormalizeSampling.Flow.FokkerPlanckExistenceGenerator
public import FormalizeSampling.Flow.FokkerPlanckExistenceTight
public import FormalizeSampling.Flow.FokkerPlanckExistenceCompact

/-!
# Weak Fokker–Planck existence: generator, test-function bounds and the dyadic grid

Status: **Verified** (infrastructure). Shared definitions and elementary lemmas for the
analytic existence proofs of the weak Fokker–Planck equation `NoiseScore.WeakFokkerPlanck` of
`dX = b(X) dt + √(2D) dW` as weak limits of dyadic Euler–Maruyama laws:

* `fpGen`: the generator `L φ = b ⬝ ∇φ + D Δφ`, continuous, compactly supported and bounded for
  `φ ∈ C²_c` (`continuous_fpGen`, `hasCompactSupport_fpGen`, `exists_bound_fpGen`), and the
  bounds of `C²_c` test functions (`testFunction2_bounds`);
* integrals of bounded continuous functions against probability measures and their weak limits
  (`abs_integral_le_of_abs_le`, `tendsto_integral_of_tendsto`,
  `continuous_integral_of_abs_le`);
* `emCurveP`: the dyadic Euler–Maruyama law `emCurve b hb D ρ₀ n t` of
  `Flow/FokkerPlanckExistenceStep` as an element of `ProbabilityMeasure`;
* Riemann sums of piecewise constant functions on the dyadic time grid (`integral_grid`).

The existence theorems are in `Flow/FokkerPlanckExistenceTime` (time-dependent drifts of linear
growth, `exists_weakFokkerPlanck_global`), `Flow/FokkerPlanckExistenceLinear` (autonomous
globally Lipschitz drifts: `exists_weakFokkerPlanck_lipschitz`, with the bounded case
`exists_weakFokkerPlanck`), `Flow/FokkerPlanckExistenceContinuousTime` and
`Flow/FokkerPlanckExistenceDissipative`. No SDE, Brownian motion or Itô formula is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU

variable {d : ℕ}

/-! ### The generator and test-function bounds -/

/-- The Fokker–Planck generator `L φ = b ⬝ ∇φ + D Δφ` of `dX = b(X) dt + √(2D) dW`; this is the
integrand of `WeakFokkerPlanck` for the autonomous drift `fun _ => b`. -/
noncomputable def fpGen (b : (Fin d → ℝ) → Fin d → ℝ) (D : ℝ) (φ : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  b x ⬝ᵥ grad φ x + D * laplacian φ x

/-- For continuous `b` and `φ ∈ C²`, the generator `L φ` is continuous. -/
theorem continuous_fpGen {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Continuous b) (D : ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (fpGen b D φ) :=
  (Continuous.dotProduct hb (continuous_grad hφ)).add
    (continuous_const.mul (continuous_laplacian hφ))

/-- For compactly supported `φ`, the generator `L φ` is compactly supported. -/
theorem hasCompactSupport_fpGen {φ : (Fin d → ℝ) → ℝ} (hφc : HasCompactSupport φ)
    (b : (Fin d → ℝ) → Fin d → ℝ) (D : ℝ) : HasCompactSupport (fpGen b D φ) := by
  refine hφc.mono' fun y hy => ?_
  by_contra hn
  apply hy
  have h1 : ∀ i, partialDeriv i φ y = 0 := fun i => image_eq_zero_of_notMem_tsupport
    fun h => hn (tsupport_partialDeriv_subset i φ h)
  have h2 : ∀ i, partialDeriv i (partialDeriv i φ) y = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport fun h =>
      hn ((tsupport_partialDeriv_subset i _).trans (tsupport_partialDeriv_subset i φ) h)
  simp [fpGen, grad, laplacian, h1, h2, dotProduct]

/-- For continuous `b` and `φ ∈ C²_c`, the generator `L φ` is bounded. -/
theorem exists_bound_fpGen {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Continuous b) (D : ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) : ∃ M, ∀ y, |fpGen b D φ y| ≤ M := by
  obtain ⟨M, hM⟩ := (continuous_fpGen hb D hφ.1).bounded_above_of_compact_support
    (hasCompactSupport_fpGen hφ.2 b D)
  exact ⟨M, fun y => by simpa [Real.norm_eq_abs] using hM y⟩

/-- A `C²_c` test function is bounded and Lipschitz (with a nonnegative constant). -/
theorem testFunction2_bounds {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    (∃ M, ∀ y, |φ y| ≤ M) ∧ ∃ C, 0 ≤ C ∧ ∀ x y, |φ x - φ y| ≤ C * ‖x - y‖ := by
  obtain ⟨hφ2, hφc⟩ := hφ
  obtain ⟨M, hM⟩ := hφ2.continuous.bounded_above_of_compact_support hφc
  obtain ⟨C, hC⟩ := (hφ2.continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  refine ⟨⟨M, fun y => by simpa [Real.norm_eq_abs] using hM y⟩, C,
    (norm_nonneg _).trans (hC 0), fun x y => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ)
    (fun z _ => (hφ2.differentiable two_ne_zero) z) (fun z _ => hC z) (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- A bounded continuous function is integrable against a finite measure. -/
theorem integrable_of_abs_le {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ]
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ y, |g y| ≤ M) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)

/-- `|∫ g dμ| ≤ M` for `|g| ≤ M` and a probability measure `μ`. -/
theorem abs_integral_le_of_abs_le {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    {g : (Fin d → ℝ) → ℝ} {M : ℝ} (hM : ∀ y, |g y| ≤ M) : |∫ y, g y ∂μ| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := M)
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)
  simpa [Real.norm_eq_abs] using this

/-- Weak convergence of probability measures gives convergence of integrals of bounded
continuous functions. -/
theorem tendsto_integral_of_tendsto {ι : Type*} {l : Filter ι}
    {μ : ι → ProbabilityMeasure (Fin d → ℝ)} {ν : ProbabilityMeasure (Fin d → ℝ)}
    (h : Tendsto μ l (𝓝 ν)) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) :
    Tendsto (fun i => ∫ y, g y ∂(μ i : Measure (Fin d → ℝ))) l
      (𝓝 (∫ y, g y ∂(ν : Measure (Fin d → ℝ)))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h
    (BoundedContinuousFunction.ofNormedAddCommGroup g hg M
      fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- `μ ↦ ∫ g dμ` is weakly continuous on probability measures for bounded continuous `g`. -/
theorem continuous_integral_of_abs_le {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) :
    Continuous fun μ : ProbabilityMeasure (Fin d → ℝ) => ∫ y, g y ∂(μ : Measure (Fin d → ℝ)) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup g hg M
      fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-! ### Dyadic EM laws as probability measures -/

/-- The dyadic EM law `emCurve b hb D ρ₀ n t` as an element of `ProbabilityMeasure`. -/
noncomputable def emCurveP (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D : ℝ)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (n : ℕ) (t : ℝ) :
    ProbabilityMeasure (Fin d → ℝ) :=
  ⟨emCurve b hb D ρ₀ n t, inferInstance⟩

/-! ### The dyadic time grid -/

/-- `2⁻ⁿ 2ⁿ = 1`. -/
theorem dyadicStep_mul_pow (n : ℕ) : dyadicStep n * 2 ^ n = 1 := by
  rw [dyadicStep, ← mul_pow]; norm_num

/-- The grid index is measurable in time. -/
theorem measurable_gridIndex (n : ℕ) : Measurable (gridIndex n) :=
  Nat.measurable_floor.comp (measurable_id.mul_const _)

/-- A bounded function of the grid index is interval integrable in time. -/
theorem intervalIntegrable_grid (n : ℕ) {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, |c j| ≤ M) (a b : ℝ) :
    IntervalIntegrable (fun r => c (gridIndex n r)) volume a b := by
  refine (intervalIntegrable_const (c := M)).mono_fun'
    ((Measurable.of_discrete (f := c)).comp (measurable_gridIndex n)).aestronglyMeasurable
    (ae_of_all _ fun r => ?_)
  simp only [Real.norm_eq_abs]
  exact hc _

/-- **Riemann sums of the piecewise constant EM curve.** For `c : ℕ → ℝ` bounded,
`∫₀^{k 2⁻ⁿ} c(⌊r 2ⁿ⌋₊) dr = 2⁻ⁿ ∑_{j<k} c j`. -/
theorem integral_grid (n : ℕ) {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, |c j| ≤ M) (k : ℕ) :
    ∫ r in (0 : ℝ)..(k * dyadicStep n), c (gridIndex n r) =
      dyadicStep n * ∑ j ∈ Finset.range k, c j := by
  set h := dyadicStep n with hhdef
  have hh : 0 < h := dyadicStep_pos n
  have hh2 : h * 2 ^ n = 1 := dyadicStep_mul_pow n
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := k * h)
      (intervalIntegrable_grid n hc _ _) (intervalIntegrable_grid n hc _ _), ih,
      Finset.sum_range_succ, mul_add]
    congr 1
    have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have : ∫ r in (k * h : ℝ)..((k + 1 : ℕ) * h), c (gridIndex n r) =
        ∫ r in (k * h : ℝ)..((k + 1 : ℕ) * h), c k := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [(countable_singleton (((k + 1 : ℕ) : ℝ) * h)).ae_notMem volume]
        with r hr hrI
      rw [uIoc_of_le hle] at hrI
      have hr' : r < ((k + 1 : ℕ) : ℝ) * h := lt_of_le_of_ne hrI.2 hr
      congr 1
      unfold gridIndex
      rw [Nat.floor_eq_iff (by nlinarith [hrI.1, pow_pos (two_pos (α := ℝ)) n])]
      have e1 : (k : ℝ) = k * h * 2 ^ n := by rw [mul_assoc, hh2, mul_one]
      have e2 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) * h * 2 ^ n := by
        rw [mul_assoc, hh2, mul_one]; push_cast; ring
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      constructor
      · rw [e1]; exact mul_le_mul_of_nonneg_right hrI.1.le h2n.le
      · rw [e2]; exact mul_lt_mul_of_pos_right hr' h2n
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    push_cast; ring

end FormalizeSampling.FokkerPlanckExistence
