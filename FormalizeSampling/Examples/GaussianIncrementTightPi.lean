module

public import FormalizeSampling.Samplers.GaussianIncrementPi
public import FormalizeSampling.Examples.GaussianIncrementTight
public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.Pinsker

/-!
# GI-1 is attained in dimension `d`: constant drift error on isotropic Gaussian random walks

Status: **Verified** (tightness example for GI-1, `d`-dimensional isotropic case).

The `d`-dimensional analogue, on `Fin d → ℝ`, of `FormalizeSampling/Examples/
GaussianIncrementTight.lean`. Take the exact drift `b = 0` and the estimated drift `b̂ = Δ` (a
constant vector `Δ : Fin d → ℝ`), a constant step `h`, and both chains of the isotropic
Euler–Maruyama kernel `GaussianIncrement.emKernelPi` started at the same point mass `δ_{x₀}`.
Both chains are product Gaussian random walks:
`μ n = N(x₀, 2nh I)` and `ν n = N(x₀ + nhΔ, 2nh I)` (`law_const_chainPi`), so
`KL(ν n ‖ μ n) = n h ‖Δ‖² / 4` with `‖Δ‖² = ∑ᵢ Δᵢ²` Euclidean (`klDiv_const_chainPi`), which is
**exactly** the `d`-dimensional GI-1 budget of `GaussianIncrement.klDiv_emChainPi_le_sum`,
`KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ h ∑ᵢ (0 - Δᵢ)² / 4 dν_k` (`klDiv_const_chainPi_eq_bound`). Hence the
constant `1/4` and the linear accumulation in multivariate GI-1 cannot be improved, in any
dimension and for every error direction `Δ`.

## Main results

* `emKernelPi_const_comp_pi_gaussianReal`: one EM step with constant drift `Δ` maps
  `N(m, v I)` to `N(m + hΔ, (v + 2h) I)`.
* `law_const_chainPi`, `klDiv_const_chainPi`, `klDiv_const_chainPi_eq_bound` (see above).
* `GaussianIncrementTightPiTV.sqrt_mul_tvSup_le_telescoped`: **TV telescoping loses `√n`**, the
  `d`-dimensional analogue of `GaussianIncrementTight.sqrt_mul_tvSup_le_telescoped`. By Pinsker
  (`Pinsker.tvSup_le_sqrt_klDiv`) and the exact KL, `tvSup (ν n) (μ n) ≤ √(n h ‖Δ‖² / 8)`,
  so a TV-telescoping bound with per-step cost `√h ‖Δ‖ / (2√π)` (the one-dimensional per-step
  bound of `GaussianIncrement.tvSup_emChain_le_sum` with `|Δ|` replaced by `‖Δ‖`) exceeds the
  true TV by a factor at least `√(2n/π)`:
  `√(2n/π) · tvSup (ν n) (μ n) ≤ n · (√h / (2√π) · ‖Δ‖)`, `‖Δ‖ = √(∑ᵢ Δᵢ²)`.

## Not proved here

* Non-isotropic noise, non-constant drift errors, and initial laws other than point masses.
* That `n √h ‖Δ‖ / (2√π)` is the output of a formalised `d`-dimensional TV-telescoping theorem
  (it is only the comparison quantity); a lower bound on the true TV
  (`2Φ(√(nh)‖Δ‖/(2√2)) - 1`); tightness of the Pinsker step itself.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.GaussianIncrementTightPi

open FormalizeSampling.MeasureHelpers (pi_dirac lintegral_pi_prod)

open GaussianIncrement

variable {d : ℕ}

/-- **One isotropic EM step with constant drift.** One step of `emKernelPi` with constant drift
`Δ : Fin d → ℝ` maps the isotropic Gaussian `N(m, v I)` to `N(m + hΔ, (v + 2h) I)` (equality of
laws on `Fin d → ℝ`). -/
theorem emKernelPi_const_comp_pi_gaussianReal (h : ℝ≥0) (Δ m : Fin d → ℝ) (v : ℝ≥0) :
    emKernelPi h (fun _ => Δ) measurable_const ∘ₘ
        Measure.pi (fun i => gaussianReal (m i) v) =
      Measure.pi fun i => gaussianReal (m i + h * Δ i) (v + 2 * h) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) (Kernel.aemeasurable _)]
  simp_rw [emKernelPi_apply, Measure.pi_pi]
  rw [lintegral_pi_prod _ (fun i y => gaussianReal (y + h * Δ i) (2 * h) (s i))
    (fun i => ?_)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← GaussianIncrementTight.emKernel_const_comp_gaussianReal h (Δ i) (m i) v,
      Measure.bind_apply (hs i) (Kernel.aemeasurable _)]
    rfl
  · exact (emKernel h (fun _ => Δ i) measurable_const).measurable_coe (hs i)

/-- **Law of the isotropic constant-drift chain.** The `emKernelPi` chain with constant drift
`Δ : Fin d → ℝ` started at `δ_{x₀}` has law `N(x₀ + k h Δ, 2 k h I)` at step `k`, i.e.
`ν k = ⊗ᵢ N(x₀ i + k h Δ i, 2 k h)`. -/
theorem law_const_chainPi (h : ℝ≥0) (Δ x₀ : Fin d → ℝ) (ν : ℕ → Measure (Fin d → ℝ))
    (h0 : ν 0 = Measure.dirac x₀)
    (hν : ∀ k, ν (k + 1) = emKernelPi h (fun _ => Δ) measurable_const ∘ₘ ν k) (k : ℕ) :
    ν k = Measure.pi fun i => gaussianReal (x₀ i + k * (h * Δ i)) (k * (2 * h)) := by
  induction k with
  | zero =>
    simp only [h0, Nat.cast_zero, zero_mul, add_zero, gaussianReal_zero_var, pi_dirac]
  | succ k ih =>
    rw [hν, ih, emKernelPi_const_comp_pi_gaussianReal]
    congr 1
    funext i
    congr 1
    · push_cast; ring
    · push_cast; ring

/-- **Exact KL of the `d`-dimensional constant-error example.** With exact drift `0` and
estimated drift `Δ : Fin d → ℝ`, both `emKernelPi` chains started at `δ_{x₀}`,
`KL(ν n ‖ μ n) = n h ∑ᵢ Δᵢ² / 4 = n h ‖Δ‖² / 4` (Euclidean norm; Mathlib's `klDiv`), for
every `h ≥ 0` and every `n`. -/
theorem klDiv_const_chainPi (h : ℝ≥0) (Δ x₀ : Fin d → ℝ) (μ ν : ℕ → Measure (Fin d → ℝ))
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernelPi h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) = ENNReal.ofReal (n * (h * (∑ i, Δ i ^ 2) / 4)) := by
  rw [law_const_chainPi h Δ x₀ ν hν0 hν n, law_const_chainPi h 0 x₀ μ hμ0 hμ n, klDiv_pi_pi]
  rw [mul_sum, sum_div, mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  refine sum_congr rfl fun i _ => ?_
  have := GaussianIncrementTight.klDiv_const_chain h (Δ i) (x₀ i)
    (fun k => gaussianReal (x₀ i + k * (h * (0 : ℝ))) (k * (2 * h)))
    (fun k => gaussianReal (x₀ i + k * (h * Δ i)) (k * (2 * h)))
    (by simp) (by simp)
    (fun k => by
      rw [GaussianIncrementTight.emKernel_const_comp_gaussianReal]
      congr 1 <;> push_cast <;> ring)
    (fun k => by
      rw [GaussianIncrementTight.emKernel_const_comp_gaussianReal]
      congr 1 <;> push_cast <;> ring) n
  simp only [Pi.zero_apply] at this ⊢
  rw [this]

/-- **GI-1 is attained in dimension `d`.** In the constant-error example (exact drift `0`,
estimated drift `Δ : Fin d → ℝ`, constant step `h`, both chains from `δ_{x₀}`),
`KL(ν n ‖ μ n)` **equals** the budget of `GaussianIncrement.klDiv_emChainPi_le_sum`,
`KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ h ∑ᵢ (0 - Δᵢ)² / 4 d(ν k)` (errors averaged under the algorithm's
laws `ν k`; Mathlib's `klDiv`, in `ℝ≥0∞`). -/
theorem klDiv_const_chainPi_eq_bound (h : ℝ≥0) (Δ x₀ : Fin d → ℝ)
    (μ ν : ℕ → Measure (Fin d → ℝ))
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernelPi h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) = klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ∫⁻ x, ENNReal.ofReal
        (h * (∑ i, ((fun _ : Fin d → ℝ => (0 : Fin d → ℝ)) x i - Δ i) ^ 2) / 4) ∂(ν k) := by
  have hp : ∀ k, IsProbabilityMeasure (ν k) := fun k => by
    rw [law_const_chainPi h Δ x₀ ν hν0 hν k]; infer_instance
  rw [klDiv_const_chainPi h Δ x₀ μ ν hμ0 hν0 hμ hν n, hμ0, hν0, klDiv_self, zero_add]
  simp only [lintegral_const, measure_univ, mul_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Pi.zero_apply, zero_sub, neg_sq]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- **Consistency with GI-1.** The exact KL of the constant-error example is (trivially) below
the `d`-dimensional GI-1 bound `klDiv_emChainPi_le_sum` instantiated with these chains; by
`klDiv_const_chainPi_eq_bound` the inequality is an equality. -/
example (h : ℝ≥0) (Δ x₀ : Fin d → ℝ) (μ ν : ℕ → Measure (Fin d → ℝ))
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernelPi h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ∫⁻ x, ENNReal.ofReal
        (h * (∑ i, ((fun _ : Fin d → ℝ => (0 : Fin d → ℝ)) x i - Δ i) ^ 2) / 4) ∂(ν k) := by
  have : IsProbabilityMeasure (μ 0) := by rw [hμ0]; infer_instance
  have : IsProbabilityMeasure (ν 0) := by rw [hν0]; infer_instance
  exact klDiv_emChainPi_le_sum (h := fun _ => h) (s := fun _ _ => 0) (ŝ := fun _ _ => Δ)
    (hs := fun _ => measurable_const) (hŝ := fun _ => measurable_const) hμ hν n

end FormalizeSampling.GaussianIncrementTightPi

/-! ### TV telescoping loses `√n` in dimension `d` -/

namespace FormalizeSampling.GaussianIncrementTightPiTV

open GaussianIncrement GaussianIncrementTightPi

variable {d : ℕ}

/-- **TV telescoping loses `√n` in dimension `d`.** In the `d`-dimensional constant-error
example (exact drift `0`, estimated drift `Δ : Fin d → ℝ`, constant step `h`, both
`emKernelPi` chains from `δ_{x₀}`), for every `n`,
`√(2n/π) · tvSup (ν n) (μ n) ≤ n · (√h / (2√π) · ‖Δ‖)` with `‖Δ‖ = √(∑ᵢ Δᵢ²)` Euclidean and
TV normalised as `sup_A |ν n A - μ n A|`. The right side is `n` times the per-step TV cost
`√h ‖Δ‖ / (2√π)`, so the telescoped bound overestimates the true distance by a factor at
least `√(2n/π)`. Proof: Pinsker and the exact KL `n h ‖Δ‖² / 4` of `klDiv_const_chainPi`. -/
theorem sqrt_mul_tvSup_le_telescoped (h : ℝ≥0) (Δ x₀ : Fin d → ℝ)
    (μ ν : ℕ → Measure (Fin d → ℝ))
    (hμ0 : μ 0 = Measure.dirac x₀) (hν0 : ν 0 = Measure.dirac x₀)
    (hμ : ∀ k, μ (k + 1) = emKernelPi h (fun _ => 0) measurable_const ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernelPi h (fun _ => Δ) measurable_const ∘ₘ ν k) (n : ℕ) :
    Real.sqrt (2 * n / Real.pi) * TotalVariation.tvSup (ν n) (μ n) ≤
      n * (Real.sqrt h / (2 * Real.sqrt Real.pi) * Real.sqrt (∑ i, Δ i ^ 2)) := by
  have hpν : IsProbabilityMeasure (ν n) := by
    rw [law_const_chainPi h Δ x₀ ν hν0 hν n]; infer_instance
  have hpμ : IsProbabilityMeasure (μ n) := by
    rw [law_const_chainPi h 0 x₀ μ hμ0 hμ n]; infer_instance
  have hKL := klDiv_const_chainPi h Δ x₀ μ ν hμ0 hν0 hμ hν n
  set S := ∑ i, Δ i ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => sq_nonneg _
  have hT := Pinsker.tvSup_le_sqrt_klDiv (μ := ν n) (ν := μ n)
    (by rw [hKL]; exact ENNReal.ofReal_ne_top)
  rw [hKL, ENNReal.toReal_ofReal (by positivity)] at hT
  calc Real.sqrt (2 * n / Real.pi) * TotalVariation.tvSup (ν n) (μ n)
      ≤ Real.sqrt (2 * n / Real.pi) * Real.sqrt (n * (h * S / 4) / 2) :=
        mul_le_mul_of_nonneg_left hT (Real.sqrt_nonneg _)
    _ = n * (Real.sqrt h / (2 * Real.sqrt Real.pi) * Real.sqrt S) := by
        rw [← Real.sqrt_mul (by positivity)]
        have hpi := Real.pi_pos
        rw [show 2 * (n : ℝ) / Real.pi * (n * (h * S / 4) / 2) =
            (n * (Real.sqrt h / (2 * Real.sqrt Real.pi) * Real.sqrt S)) ^ 2 by
          rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt (NNReal.coe_nonneg h),
            Real.sq_sqrt hpi.le, Real.sq_sqrt hS0]
          field_simp
          ring]
        exact Real.sqrt_sq (by positivity)

end FormalizeSampling.GaussianIncrementTightPiTV
