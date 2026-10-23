module

public import FormalizeSampling.Samplers.DiffusionMain

/-!
# Statement audit: the DDPM geometric-grid bound for singular, non-Gaussian data

Rows: DF-1.

Non-vacuity witness for `DiffusionDiscretization.klDiv_output_le_geomGrid` and
`DiffusionDiscretization.tvSup_output_le_geomGrid`. The data law is a Dirac mass `δ_c` or a
two-point mixture `(δ_a + δ_b) / 2` on `Fin (d + 1) → ℝ`: non-Gaussian and with no Lebesgue
density (`¬ μ ≪ volume`). The learned score is the exact score `s_k = ∇ log p_k`
(`exactScore`, with `p_k = fwdDensity μ t k`), so every hypothesis of the headline theorems is
discharged (measurability of `s_k` holds because `fderiv` of any function is measurable; the
score error vanishes identically). The audit then shows the bound is not vacuous: for every
`u_1 > 0` and `ε > 0` there are `r > 1`, `N ≥ 1` with `KL(p_1 ‖ q_1) ≤ ε` and
`TV(p_1, q_1) ≤ ε`, where `p_1` is the `t_1`-smoothed data law (`t_1 = log(1 + u_1) / 2`) and
`q_1` the sampler output. The choice is `r = 1 + η` with `η → 0` and `N - 1 = ⌈X / η⌉`, so that
`u_N / u_1 = r^{N-1} ≥ 1 + X` kills the initialisation term while the discretisation term
`(r - 1) d / 2 (1 + (N - 1) log r) ≤ η d (X + 2) / 2` vanishes.

## Main results

The general statements live in `Samplers/DiffusionMain.lean` (namespace
`DiffusionDiscretization`) and are re-exported here under their audit names:

* `exists_geomGrid_params`: the real-analysis core; the right-hand side of the geometric-grid
  bound (with zero score error) can be made `≤ ε`.
* `measurable_exactScore`, `integrable_exactScore_err`, `scoreErr_exactScore`: the exact score is
  an admissible learned score with `scoreErr = 0`.
* `exists_klDiv_output_le`, `exists_tvSup_output_le`: for every data law with finite second
  moment, exact score, `u_1 > 0`, `ε > 0`: some geometric grid gives `KL(p_1 ‖ q_1) ≤ ε`
  (resp. `TV(p_1, q_1) ≤ ε`).

Proved here:

* `dirac_tvSup_output_le`, `twoPoint_tvSup_output_le`: the TV statement for a Dirac mass and
  for a two-point mixture, together with the absence of a Lebesgue density.

## Not proved here

* No witness with an inexact learned score (`scoreErr > 0`); the score-error term is only
  exercised at the value `0`.
* No rate or explicit `(r, N)` as a function of `ε`; only existence (the construction in the
  proof of `exists_geomGrid_params` is explicit).
* Nothing about `p_1` versus the data law `μ` itself (the `t_1`-smoothing error).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.Audit.Diffusion

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization

export FormalizeSampling.DiffusionDiscretization (exists_geomGrid_params exactScore
  measurable_exactScore integrable_exactScore_err scoreErr_exactScore initConst_nonneg
  exists_klDiv_output_le exists_tvSup_output_le)

/-- A Dirac mass on `Fin (d + 1) → ℝ` has no Lebesgue density: `¬ δ_c ≪ volume`. -/
theorem dirac_not_ac {d : ℕ} (c : Fin (d + 1) → ℝ) :
    ¬ Measure.dirac c ≪ (volume : Measure (Fin (d + 1) → ℝ)) := fun h => by
  have := h (measure_singleton c)
  simp at this

/-- A Dirac mass has finite second moment: `x ↦ ∑ᵢ xᵢ²` is `δ_c`-integrable. -/
theorem integrable_sqNorm_dirac {d : ℕ} (c : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ => ∑ i, x i ^ 2) (Measure.dirac c) :=
  integrable_dirac (by simp)

/-- The two-point mixture `(δ_a + δ_b) / 2`. -/
noncomputable def twoPoint {d : ℕ} (a b : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac a + (2⁻¹ : ℝ≥0∞) • Measure.dirac b

/-- The two-point mixture is a probability measure. -/
instance {d : ℕ} (a b : Fin d → ℝ) : IsProbabilityMeasure (twoPoint a b) :=
  ⟨by simp [twoPoint, ENNReal.inv_two_add_inv_two]⟩

/-- The two-point mixture has finite second moment. -/
theorem integrable_sqNorm_twoPoint {d : ℕ} (a b : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ => ∑ i, x i ^ 2) (twoPoint a b) :=
  ((integrable_sqNorm_dirac a).smul_measure (by simp)).add_measure
    ((integrable_sqNorm_dirac b).smul_measure (by simp))

/-- The two-point mixture on `Fin (d + 1) → ℝ` has no Lebesgue density. -/
theorem twoPoint_not_ac {d : ℕ} (a b : Fin (d + 1) → ℝ) :
    ¬ twoPoint a b ≪ (volume : Measure (Fin (d + 1) → ℝ)) := fun h => by
  have := h (measure_singleton a)
  simp [twoPoint] at this

/-- **Witness, Dirac data.** For `μ = δ_c` on `Fin (d + 1) → ℝ` (no Lebesgue density), the
exact score, `u_1 > 0` and `ε > 0`, some geometric grid gives `TV(p_1, q_1) ≤ ε`. -/
theorem dirac_tvSup_output_le {d : ℕ} (c : Fin (d + 1) → ℝ) {u1 : ℝ} (hu1 : 0 < u1)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ Measure.dirac c ≪ volume ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      TotalVariation.tvSup (fwdLaw (Measure.dirac c) (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r))
        (scoreMean (geomGrid u1 r) (exactScore (Measure.dirac c) (geomGrid u1 r)))
        (measurable_scoreMean _ (measurable_exactScore _ _)) N 1) ≤ ε :=
  ⟨dirac_not_ac c, exists_tvSup_output_le _ (integrable_sqNorm_dirac c) hu1 hε⟩

/-- **Witness, two-point data.** For `μ = (δ_a + δ_b) / 2` on `Fin (d + 1) → ℝ` (non-Gaussian,
no Lebesgue density), the exact score, `u_1 > 0`, `ε > 0`, some geometric grid gives
`TV(p_1, q_1) ≤ ε`. -/
theorem twoPoint_tvSup_output_le {d : ℕ} (a b : Fin (d + 1) → ℝ) {u1 : ℝ} (hu1 : 0 < u1)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ twoPoint a b ≪ volume ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      TotalVariation.tvSup (fwdLaw (twoPoint a b) (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r))
        (scoreMean (geomGrid u1 r) (exactScore (twoPoint a b) (geomGrid u1 r)))
        (measurable_scoreMean _ (measurable_exactScore _ _)) N 1) ≤ ε :=
  ⟨twoPoint_not_ac a b, exists_tvSup_output_le _ (integrable_sqNorm_twoPoint a b) hu1 hε⟩

end FormalizeSampling.Audit.Diffusion
