module

public import FormalizeSampling.Flow.FokkerPlanckExistenceStep

/-!
# Dyadic grid arithmetic for the Euler–Maruyama laws

Status: **Verified** (elementary lemmas). Facts about the dyadic step `dyadicStep n = 2⁻ⁿ` and
the grid index `gridIndex n t = ⌊t 2ⁿ⌋₊` of `Flow/FokkerPlanckExistenceStep` used by the
existence proofs for the weak Fokker–Planck equation (`Flow/FokkerPlanckExistenceTimeOp`,
`Flow/FokkerPlanckExistenceTime`): positivity and refinement of the step
(`dyadicStep_pos`, `dyadicStep_succ`, `sqrt_dyadicStep`), the level-`n + 1` index is `2k` or
`2k + 1` (`gridIndex_succ`), the grid time is at most `max t 0` (`gridIndex_mul_le`), together
with `(1 + a)^m ≤ e^{a m}` (`one_add_pow_le_exp`) and the comparison
`|∫ g₁ dμ - ∫ g₂ dμ| ≤ sup |g₁ - g₂|` for bounded continuous functions
(`abs_integral_sub_le_of_abs_le`).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal

namespace FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-- `(1 + a)^m ≤ exp (a m)` for `a ≥ 0`. -/
theorem one_add_pow_le_exp {a : ℝ} (ha : 0 ≤ a) (m : ℕ) : (1 + a) ^ m ≤ Real.exp (a * m) := by
  calc (1 + a) ^ m ≤ Real.exp a ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp a]) m
    _ = Real.exp (a * m) := by rw [← Real.exp_nat_mul]; ring_nf

section Dyadic

/-- `2⁻⁽ⁿ⁺¹⁾ = 2⁻ⁿ / 2`. -/
theorem dyadicStep_succ (n : ℕ) : dyadicStep (n + 1) = dyadicStep n / 2 := by
  simp only [dyadicStep, pow_succ]; ring

/-- `0 < 2⁻ⁿ`. -/
theorem dyadicStep_pos (n : ℕ) : 0 < dyadicStep n := by unfold dyadicStep; positivity

/-- `2⁻ⁿ ≤ 1`. -/
theorem dyadicStep_le_one (n : ℕ) : dyadicStep n ≤ 1 := by
  unfold dyadicStep; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- `√(2⁻ⁿ) = (√(1/2))ⁿ`. -/
theorem sqrt_dyadicStep (n : ℕ) : Real.sqrt (dyadicStep n) = Real.sqrt (1 / 2) ^ n := by
  unfold dyadicStep
  rw [show ((1 : ℝ) / 2) ^ n = (Real.sqrt (1 / 2) ^ n) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

/-- The level-`(n+1)` grid index is `2k` or `2k + 1` where `k` is the level-`n` index. -/
theorem gridIndex_succ (n : ℕ) (t : ℝ) :
    gridIndex (n + 1) t = 2 * gridIndex n t ∨ gridIndex (n + 1) t = 2 * gridIndex n t + 1 := by
  unfold gridIndex
  have e : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
  rw [e]
  set x := t * 2 ^ n
  rcases lt_or_ge x 0 with hx | hx
  · left
    rw [Nat.floor_of_nonpos (by linarith), Nat.floor_of_nonpos hx.le]
  · have h1 : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by
      apply Nat.le_floor; push_cast; linarith [Nat.floor_le hx]
    have h2 : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
      rw [Nat.floor_lt (by linarith)]; push_cast; linarith [Nat.lt_floor_add_one x]
    omega

/-- The grid time is at most `max t 0`: `⌊t 2ⁿ⌋₊ 2⁻ⁿ ≤ max t 0`. -/
theorem gridIndex_mul_le (n : ℕ) (t : ℝ) : (gridIndex n t : ℝ) * dyadicStep n ≤ max t 0 := by
  unfold gridIndex dyadicStep
  rcases lt_or_ge t 0 with ht | ht
  · rw [Nat.floor_of_nonpos (by nlinarith [pow_pos (two_pos (α := ℝ)) n])]; simp
  · have h := Nat.floor_le (by positivity : 0 ≤ t * 2 ^ n)
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    calc (⌊t * 2 ^ n⌋₊ : ℝ) * (1 / 2) ^ n ≤ t * 2 ^ n * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = t := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ max t 0 := le_max_left _ _

end Dyadic

/-- `|∫ g₁ dμ - ∫ g₂ dμ| ≤ c` for bounded continuous `g₁, g₂` with `|g₁ - g₂| ≤ c` and a
probability measure `μ`. -/
theorem abs_integral_sub_le_of_abs_le {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    {g₁ g₂ : (Fin d → ℝ) → ℝ} (h1 : Continuous g₁) (h2 : Continuous g₂) {M : ℝ}
    (hM1 : ∀ y, |g₁ y| ≤ M) (hM2 : ∀ y, |g₂ y| ≤ M) {c : ℝ} (hc : ∀ y, |g₁ y - g₂ y| ≤ c) :
    |∫ y, g₁ y ∂μ - ∫ y, g₂ y ∂μ| ≤ c := by
  have i1 : Integrable g₁ μ := Integrable.of_bound h1.aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM1 y)
  have i2 : Integrable g₂ μ := Integrable.of_bound h2.aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM2 y)
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => g₁ y - g₂ y) (C := c)
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hc y)
  simpa using this

end FormalizeSampling.FokkerPlanckExistence
