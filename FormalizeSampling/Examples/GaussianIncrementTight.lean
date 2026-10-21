module

public import FormalizeSampling.Samplers.GaussianIncrement
public import FormalizeSampling.Foundations.Pinsker

/-!
# GI-1 is attained: constant drift error on Gaussian random walks

Tightness of the score-error theorem GI-1 (`GaussianIncrement.klDiv_emChain_le_sum`).
Take the exact drift `b = 0` and the estimated drift `b̂ = Δ` (a constant error), a constant
step `h`, and both chains started at the same point `x₀`. Both chains are Gaussian random walks:
`μ n = N(x₀, 2nh)` and `ν n = N(x₀ + nhΔ, 2nh)` (`law_const_chain`), so
`KL(ν n ‖ μ n) = n h Δ² / 4` (`klDiv_const_chain`), which is **exactly** the GI-1 budget
`KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫ h (b - b̂)² / 4 dν_k` (`klDiv_const_chain_eq_bound`). Hence the
constant `1/4` and the linear accumulation in GI-1 cannot be improved.

The same example quantifies the loss of the TV-telescoping route
(`GaussianIncrement.tvSup_emChain_le_sum`, per-step bound `√h |Δ| / (2√π)`): by Pinsker the
true distance is at most `√(n h Δ² / 8)`, so the telescoped bound `n √h |Δ| / (2√π)` exceeds
the true TV by a factor at least `√(2n/π)` (`sqrt_mul_tvSup_le_telescoped`), which grows
without bound in the number of steps.

## Not proved here

* A quantitative lower bound on the true TV (it is `2Φ(√(nh)|Δ|/(2√2)) - 1`); only the
  comparison above and its positivity for `n ≥ 1`, `h > 0`, `Δ ≠ 0` (`tvSup_const_chain_pos`).
* Tightness of the Pinsker step itself (it is not tight in this example for large `nhΔ²`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.GaussianIncrementTight

open GaussianIncrement

/-- One EM step with constant drift `Δ` maps `N(m, v)` to `N(m + hΔ, v + 2h)`. -/
theorem emKernel_const_comp_gaussianReal (h : ℝ≥0) (Δ m : ℝ) (v : ℝ≥0) :
    emKernel h (fun _ => Δ) measurable_const ∘ₘ gaussianReal m v =
      gaussianReal (m + h * Δ) (v + 2 * h) := by
  have hb := Measure.bind_map (m := gaussianReal m v) (f := fun x => x + (h : ℝ) * Δ)
    (g := fun y => gaussianReal y (2 * h)) (measurable_add_const _).aemeasurable
    (OU.heatKernel (2 * h)).measurable.aemeasurable
  rw [gaussianReal_map_add_const, OU.bind_heat] at hb
  rw [hb]
  rfl

/-- The EM chain with constant drift `Δ` started at `δ_{x₀}` has law
`N(x₀ + k h Δ, 2 k h)` at step `k`. -/
theorem law_const_chain (h : ℝ≥0) (Δ x₀ : ℝ) (ν : ℕ → Measure ℝ) (h0 : ν 0 = Measure.dirac x₀)
    (hν : ∀ k, ν (k + 1) = emKernel h (fun _ => Δ) measurable_const ∘ₘ ν k) (k : ℕ) :
    ν k = gaussianReal (x₀ + k * (h * Δ)) (k * (2 * h)) := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [hν, ih, emKernel_const_comp_gaussianReal]
    congr 1
    · push_cast; ring
    · push_cast; ring

/-- **Exact KL of the constant-error example.** With exact drift `0` and estimated drift `Δ`,
both chains started at `x₀`, `KL(ν n ‖ μ n) = n h Δ² / 4` (every `h ≥ 0`, every `n`). -/
theorem klDiv_const_chain (h : ℝ≥0) (Δ x₀ : ℝ) (μ ν : ℕ → Measure ℝ)
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernel h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) = ENNReal.ofReal (n * (h * Δ ^ 2 / 4)) := by
  rw [law_const_chain h Δ x₀ ν hν0 hν n, law_const_chain h 0 x₀ μ hμ0 hμ n]
  rcases eq_or_ne ((n : ℝ≥0) * (2 * h)) 0 with hv | hv
  · have : (n : ℝ) * h = 0 := by
      have := congrArg (fun r : ℝ≥0 => (r : ℝ)) hv
      simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_zero] at this
      nlinarith [this]
    have e : (n : ℝ) * (h * Δ) = 0 := by rw [← mul_assoc, this, zero_mul]
    have e2 : (n : ℝ) * (h * Δ ^ 2 / 4) = 0 := by
      rw [show (n : ℝ) * (h * Δ ^ 2 / 4) = (n * h) * Δ ^ 2 / 4 by ring, this]; simp
    rw [e, e2, hv]
    simp
  · rw [klDiv_gaussianReal_gaussianReal _ _ hv]
    congr 1
    have hv' : (n : ℝ) * (2 * h) ≠ 0 := by exact_mod_cast hv
    have hn : (n : ℝ) ≠ 0 := fun e => hv' (by rw [e, zero_mul])
    have hh : (h : ℝ) ≠ 0 := fun e => hv' (by rw [e, mul_zero, mul_zero])
    push_cast
    field_simp
    ring

/-- **GI-1 is attained.** In the constant-error example, `KL(ν n ‖ μ n)` equals the GI-1
budget `KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫ h (0 - Δ)² / 4 dν_k` exactly. -/
theorem klDiv_const_chain_eq_bound (h : ℝ≥0) (Δ x₀ : ℝ) (μ ν : ℕ → Measure ℝ)
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernel h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) = klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ∫⁻ x, ENNReal.ofReal (h * ((fun _ : ℝ => (0 : ℝ)) x - Δ) ^ 2 / 4) ∂(ν k) := by
  have hp : ∀ k, IsProbabilityMeasure (ν k) := fun k => by
    rw [law_const_chain h Δ x₀ ν hν0 hν k]; infer_instance
  rw [klDiv_const_chain h Δ x₀ μ ν hμ0 hν0 hμ hν n, hμ0, hν0, klDiv_self, zero_add]
  simp only [lintegral_const, measure_univ, mul_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- **TV telescoping loses `√n`.** In the constant-error example,
`√(2n/π) · tvSup (ν n) (μ n) ≤ n · √h |Δ| / (2√π)`, the right side being the bound of
`GaussianIncrement.tvSup_emChain_le_sum`: that bound overestimates the true distance by a
factor at least `√(2n/π)`. -/
theorem sqrt_mul_tvSup_le_telescoped (h : ℝ≥0) (Δ x₀ : ℝ) (μ ν : ℕ → Measure ℝ)
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernel h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    Real.sqrt (2 * n / Real.pi) * TotalVariation.tvSup (ν n) (μ n) ≤
      n * (Real.sqrt h / (2 * Real.sqrt Real.pi) * |Δ|) := by
  have hpν : IsProbabilityMeasure (ν n) := by
    rw [law_const_chain h Δ x₀ ν hν0 hν n]; infer_instance
  have hpμ : IsProbabilityMeasure (μ n) := by
    rw [law_const_chain h 0 x₀ μ hμ0 hμ n]; infer_instance
  have hKL := klDiv_const_chain h Δ x₀ μ ν hμ0 hν0 hμ hν n
  have hT := Pinsker.tvSup_le_sqrt_klDiv (μ := ν n) (ν := μ n)
    (by rw [hKL]; exact ENNReal.ofReal_ne_top)
  rw [hKL, ENNReal.toReal_ofReal (by positivity)] at hT
  calc Real.sqrt (2 * n / Real.pi) * TotalVariation.tvSup (ν n) (μ n)
      ≤ Real.sqrt (2 * n / Real.pi) * Real.sqrt (n * (h * Δ ^ 2 / 4) / 2) :=
        mul_le_mul_of_nonneg_left hT (Real.sqrt_nonneg _)
    _ = n * (Real.sqrt h / (2 * Real.sqrt Real.pi) * |Δ|) := by
        rw [← Real.sqrt_mul (by positivity)]
        have hpi := Real.pi_pos
        rw [show 2 * (n : ℝ) / Real.pi * (n * (h * Δ ^ 2 / 4) / 2) =
            (n * (Real.sqrt h / (2 * Real.sqrt Real.pi) * |Δ|)) ^ 2 by
          rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt (NNReal.coe_nonneg h),
            Real.sq_sqrt hpi.le, sq_abs]
          field_simp
          ring]
        exact Real.sqrt_sq (by positivity)

/-- **The example is non-degenerate: the true TV is positive.** In the constant-error example
with `h > 0`, `Δ ≠ 0` and `n ≥ 1`, `0 < tvSup (ν n) (μ n)` (the laws `N(x₀ + nhΔ, 2nh)` and
`N(x₀, 2nh)` differ, since `KL(ν n ‖ μ n) = n h Δ² / 4 > 0`). So the comparison of
`sqrt_mul_tvSup_le_telescoped` is not satisfied trivially by `tvSup = 0`. -/
theorem tvSup_const_chain_pos {h : ℝ≥0} (hh : 0 < h) {Δ : ℝ} (hΔ : Δ ≠ 0) (x₀ : ℝ)
    (μ ν : ℕ → Measure ℝ) (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernel h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel h (fun _ => Δ) measurable_const ∘ₘ ν k) {n : ℕ}
    (hn : 1 ≤ n) : 0 < TotalVariation.tvSup (ν n) (μ n) := by
  have hpν : IsProbabilityMeasure (ν n) := by
    rw [law_const_chain h Δ x₀ ν hν0 hν n]; infer_instance
  have hpμ : IsProbabilityMeasure (μ n) := by
    rw [law_const_chain h 0 x₀ μ hμ0 hμ n]; infer_instance
  refine lt_of_le_of_ne (TotalVariation.tvSup_nonneg _ _) fun h0 => ?_
  have heq : ν n = μ n := TotalVariation.tvSup_eq_zero_iff.1 h0.symm
  have hKL := klDiv_const_chain h Δ x₀ μ ν hμ0 hν0 hμ hν n
  rw [heq, klDiv_self, eq_comm, ENNReal.ofReal_eq_zero] at hKL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hh' : (0 : ℝ) < h := hh
  have : 0 < (n : ℝ) * (h * Δ ^ 2 / 4) := by positivity
  linarith

end FormalizeSampling.GaussianIncrementTight
