module

public import FormalizeSampling.Flow.FokkerPlanckExistenceStep

/-!
# Second moments of Gaussian steps and the squared Euclidean distance

Status: **Verified** (elementary lemmas). The squared Euclidean distance
`sqDist x y = ∑ᵢ (y i - x i)²` (`measurable_sqDist`, `sq_norm_le_sqDist`: it dominates the
squared sup norm) and the second moments of Gaussian laws about a point:
`∫ (u - c)² dN(m, v) = (m - c)² + v` (`integral_sub_sq_gaussianReal`,
`lintegral_sub_sq_gaussianReal`) and, for `N(m, v I) = ⊗ᵢ N(m i, v)`,
`∫⁻ |z - x|² = ∑ᵢ ((m i - x i)² + v)` (`lintegral_sqDist_pi`). Also the dyadic grid bound
`⌊t 2ⁿ⌋₊ 2⁻ⁿ ≤ max T 0` for `t ≤ T` (`dyadic_grid_bound`).

These are the moment inputs of the Lyapunov estimates for Euler–Maruyama steps
(`Flow/FokkerPlanckExistenceLyap`), of the tightness of the dyadic Euler–Maruyama laws
(`Flow/FokkerPlanckExistenceTimeOp`, `Flow/FokkerPlanckExistenceDissipative`), and of the second-
moment computations for diffusion samplers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence
open FormalizeSampling.HeatKernelPi

variable {d : ℕ}

/-- Second moment about `c` of `N(m, v)`: `∫ (u - c)² dN(m, v) = (m - c)² + v`. -/
theorem integral_sub_sq_gaussianReal (m c : ℝ) (v : ℝ≥0) :
    ∫ u, (u - c) ^ 2 ∂gaussianReal m v = (m - c) ^ 2 + v := by
  have hid : MemLp (fun u : ℝ => u) 2 (gaussianReal m v) := by
    have := memLp_id_gaussianReal (μ := m) (v := v) 2; simp at this; exact this
  have hX : MemLp (fun u : ℝ => u - c) 2 (gaussianReal m v) := hid.sub (memLp_const c)
  have h1 := variance_eq_sub hX
  rw [variance_sub_const hid.aestronglyMeasurable c, variance_fun_id_gaussianReal] at h1
  have h2 : ∫ u, (u - c) ∂gaussianReal m v = m - c := by
    rw [integral_sub (hid.integrable one_le_two) (integrable_const c), integral_const]
    simp [integral_id_gaussianReal]
  simp only [Pi.pow_apply] at h1
  rw [h2] at h1
  linarith

/-- Lower-integral form of `integral_sub_sq_gaussianReal`. -/
theorem lintegral_sub_sq_gaussianReal (m c : ℝ) (v : ℝ≥0) :
    ∫⁻ u, ENNReal.ofReal ((u - c) ^ 2) ∂gaussianReal m v = ENNReal.ofReal ((m - c) ^ 2 + v) := by
  have hid : MemLp (fun u : ℝ => u) 2 (gaussianReal m v) := by
    have := memLp_id_gaussianReal (μ := m) (v := v) 2; simp at this; exact this
  have hX : MemLp (fun u : ℝ => u - c) 2 (gaussianReal m v) := hid.sub (memLp_const c)
  rw [← integral_sub_sq_gaussianReal, ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (ae_of_all _ fun u => sq_nonneg _)]

/-- Squared Euclidean distance `∑ᵢ (y i - x i)²`. -/
noncomputable def sqDist (x y : Fin d → ℝ) : ℝ := ∑ i, (y i - x i) ^ 2

/-- `sqDist x` is measurable. -/
theorem measurable_sqDist (x : Fin d → ℝ) : Measurable (sqDist x) := by
  unfold sqDist; fun_prop

/-- Second moment about `x` of `N(m, v I) = ⊗ᵢ N(m i, v)`:
`∫⁻ |z - x|² = ∑ᵢ ((m i - x i)² + v)` (Euclidean). -/
theorem lintegral_sqDist_pi (x m : Fin d → ℝ) (v : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal (sqDist x z) ∂(Measure.pi fun i => gaussianReal (m i) v) =
      ENNReal.ofReal (∑ i, ((m i - x i) ^ 2 + v)) := by
  simp only [sqDist]
  have e : ∀ z : Fin d → ℝ, ENNReal.ofReal (∑ i, (z i - x i) ^ 2) =
      ∑ i, ENNReal.ofReal ((z i - x i) ^ 2) := fun z =>
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)
  simp_rw [e]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    lintegral_finsetSum' _ (fun i _ => (by fun_prop : Measurable fun z : Fin d → ℝ =>
      ENNReal.ofReal ((z i - x i) ^ 2)).aemeasurable)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← lintegral_sub_sq_gaussianReal]
  exact (measurePreserving_eval (fun i => gaussianReal (m i) v) i).lintegral_comp
    (f := fun u => ENNReal.ofReal ((u - x i) ^ 2)) (by fun_prop)

/-- The squared sup norm is at most the squared Euclidean distance. -/
theorem sq_norm_le_sqDist (x z : Fin d → ℝ) : ‖z - x‖ ^ 2 ≤ sqDist x z := by
  have hs : 0 ≤ sqDist x z := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : ‖z - x‖ ≤ Real.sqrt (sqDist x z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun j => (z j - x j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc ‖z - x‖ ^ 2 ≤ Real.sqrt (sqDist x z) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = sqDist x z := Real.sq_sqrt hs

/-- The dyadic grid time `⌊t 2ⁿ⌋₊ 2⁻ⁿ` is at most `max T 0` when `t ≤ T`. -/
theorem dyadic_grid_bound (n : ℕ) {t T : ℝ} (ht : t ≤ T) :
    (gridIndex n t : ℝ) * dyadicStep n ≤ max T 0 := by
  unfold gridIndex dyadicStep
  rcases le_or_gt 0 (t * 2 ^ n) with h | h
  · have h1 := Nat.floor_le h
    calc (⌊t * 2 ^ n⌋₊ : ℝ) * (1 / 2) ^ n ≤ t * 2 ^ n * (1 / 2) ^ n := by gcongr
      _ = t := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ max T 0 := ht.trans (le_max_left _ _)
  · rw [Nat.floor_of_nonpos h.le]
    simp

end FormalizeSampling.FokkerPlanckExistence
