module

public import FormalizeSampling.Audit.DiffusionAdvancedSeparation
public import FormalizeSampling.Samplers.DiffusionVarianceMain
public import FormalizeSampling.Samplers.DiffusionRate
public import FormalizeSampling.Samplers.DiffusionGaussianOutputExt

/-!
# Statement audit: variance, path-KL, rate and Gaussian-output witnesses (DF-4, DF-5, DF-6, DF-8)

Non-vacuity witnesses for the diffusion rows DF-4, DF-5, DF-6 and DF-8. Data laws on
`Fin 1 → ℝ`: the two-point law `(δ_{-1} + δ_1)/2` (`pm`, second moment `1 = d`, no density),
the point mass `δ_0`, and the Gaussians `N(0, 1)` and `N(0, 1/2)`. Grids: the uniform grid
`t_k = k` (`unifGrid`), `t_k = k/4` (`quarterGrid`) and the geometric grid `u_1 = 1`,
`r = e²`. Every hypothesis of the headline theorems is discharged in Lean.

* **DF-4** (`DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_ge`,
  `klDiv_output_le_betaVar_explicit`): on `t_k = k` with data `pm`, the per-step KL sum of the
  `σ² = β/α²` sampler is `≥ (N - 1)/2` (linear in `N` and in `T = t_N`), while the output KL of
  the exact-score `σ² = β` sampler is `≤ 1` for every `N ≥ 1`.
* **DF-5** (`DiffusionPath.klDiv_truePath_ddpm_ge_uniform`,
  `DiffusionPath.klDiv_truePath_betaVar_le_explicit`): same instance; the path KL of the
  `σ² = β/α²` sampler with the exact Bayes means is `≥ (N - 1)/2`, the path KL of the
  `σ² = β` sampler is `≤ 1`.
* **DF-6** (`sum_lintegral_klDiv_revKernel_geomGrid_ge`, `..._geomGrid_dirac`,
  `discBound_geomGrid_le_dirac`): on the geometric grid `u_1 = 1`, `r = e²`, the per-step sum is
  `≥ (N - 2)/2` for `pm` and equals `(N - 1)(1 + e^{-2})/2 > 0` for `δ_0` (`N ≥ 2`).
* **DF-8** (`DiffusionGaussian.gaussian_output_two_sided`): `N(0, 1)` data, `t_k = k/4`
  (`h = 1/4`, `e^{2h} ≤ 2`), `N ≥ 2`:
  `0 < (1 - e^{-(N-1)/2})²/48 ≤ KL(p_1 ‖ q_1) ≤ (e^{1/2} - 1)²/4 ≤ 1/4`, path KL `≥ (N - 1)/20`;
  for `N(0, 1/2)` the same lower bounds and the finite upper bound of the theorem.

## Main results

* `perStep_ddpm_witness`, `output_betaVar_witness` (DF-4).
* `path_witness` (DF-5).
* `rate_witness_pm`, `rate_witness_dirac` (DF-6).
* `gaussian_witness_one`, `gaussian_witness_half` (DF-8).

## Not proved here

* No lower bound on the output KL of the `σ² = β/α²` sampler for non-Gaussian data (the
  theorems do not give one); DF-4/DF-5 lower bounds concern the per-step sum and the path KL.
* The upper bound `1` for `σ² = β` is not tight; the actual KL is not computed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.Audit.DiffusionAdvancedRate

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
  FormalizeSampling.Audit.Diffusion FormalizeSampling.DiffusionPath
  FormalizeSampling.DiffusionGaussian FormalizeSampling.Audit.DiffusionAdvancedSeparation

/-! ### Uniform grid `t_k = k` -/

/-- `e² ≥ 3`. -/
theorem three_le_exp_two : 3 ≤ Real.exp 2 := by
  linarith [Real.add_one_le_exp (2 : ℝ)]

/-- `pm` has second moment `1 = d`. -/
theorem secondMoment_pm' : secondMoment pm = 1 := secondMoment_pm

/-- On `t_k = k` each step contributes `2 (t_k - t_{k-1}) - β_k = 1 + e^{-2} ≥ 1`. -/
theorem step_unifGrid {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ 2 * (unifGrid k - unifGrid (k - 1)) - fwdVar unifGrid k := by
  have h1 : unifGrid k - unifGrid (k - 1) = 1 := by
    simp only [unifGrid]; rw [Nat.cast_sub hk]; ring
  rw [h1, fwdVar, fwdScale_unifGrid hk]
  nlinarith [Real.exp_pos (-1)]

/-- `heatTime` of the first point of `t_k = k` is `e² - 1`. -/
theorem heatTime_unifGrid_one : heatTime unifGrid 1 = Real.exp 2 - 1 := by
  simp [heatTime, unifGrid]

/-- **The `σ² = β` bound on `t_k = k` is at most `1`.** With `κ = 1/u_1`, `u_1 = e² - 1`:
`I + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺) ≤ 1` for `pm` and every `N ≥ 1`. -/
theorem betaBound_unifGrid_le {N : ℕ} (hN : 1 ≤ N) :
    initBound pm unifGrid N + (heatTime unifGrid 1)⁻¹ / 2 * (((1 : ℕ) : ℝ) *
      (2 + Real.log ((1 + (heatTime unifGrid 1)⁻¹) /
        ((heatTime unifGrid 1)⁻¹ * heatTime unifGrid 1))) +
      2 * max (secondMoment pm - ((1 : ℕ) : ℝ)) 0) ≤ 1 := by
  have he := three_le_exp_two
  have hu : 0 < heatTime unifGrid 1 := by rw [heatTime_unifGrid_one]; linarith
  set κ := (heatTime unifGrid 1)⁻¹ with hκ
  have hκ0 : 0 < κ := inv_pos.2 hu
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκ, heatTime_unifGrid_one, inv_eq_one_div, div_le_div_iff₀ (by linarith) two_pos]
    linarith
  have hlog : Real.log ((1 + κ) / (κ * heatTime unifGrid 1)) ≤ κ := by
    rw [hκ, inv_mul_cancel₀ hu.ne', div_one]
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + κ)]
  -- the initialisation term
  have hI : initBound pm unifGrid N ≤ 1 / 3 := by
    rw [initBound, show ∫ x, ∑ i, x i ^ 2 ∂pm = 1 from secondMoment_pm, mul_one]
    have hs : fwdScale unifGrid 1 ^ 2 ≤ 1 / 4 := by
      rw [fwdScale_unifGrid le_rfl]
      have h1 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) two_pos]
        linarith [Real.add_one_le_exp (1 : ℝ)]
      nlinarith [Real.exp_pos (-1)]
    have hβ : fwdVar unifGrid 1 = 1 - fwdScale unifGrid 1 ^ 2 := rfl
    have hβ0 : 3 / 4 ≤ fwdVar unifGrid 1 := by linarith
    have hl := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < fwdVar unifGrid 1)
    have hinv : (fwdVar unifGrid 1)⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hE : Real.exp (-2 * (unifGrid N - unifGrid 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : unifGrid 1 ≤ unifGrid N := unifGrid_strictMono.monotone hN
      linarith
    have hbr : 0 ≤ (((1 : ℕ) : ℝ) * (fwdVar unifGrid 1 - 1 - Real.log (fwdVar unifGrid 1)) +
        fwdScale unifGrid 1 ^ 2) / 2 := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < fwdVar unifGrid 1)
      have := sq_nonneg (fwdScale unifGrid 1)
      push_cast; linarith
    calc Real.exp (-2 * (unifGrid N - unifGrid 1)) * ((((1 : ℕ) : ℝ) *
          (fwdVar unifGrid 1 - 1 - Real.log (fwdVar unifGrid 1)) +
          fwdScale unifGrid 1 ^ 2) / 2)
        ≤ 1 * ((((1 : ℕ) : ℝ) * (fwdVar unifGrid 1 - 1 - Real.log (fwdVar unifGrid 1)) +
          fwdScale unifGrid 1 ^ 2) / 2) := mul_le_mul_of_nonneg_right hE hbr
      _ ≤ 1 / 3 := by
        have hl' : 1 - (fwdVar unifGrid 1)⁻¹ ≤ Real.log (fwdVar unifGrid 1) := by
          rw [hβ]; exact hl
        push_cast; linarith
  rw [secondMoment_pm', Nat.cast_one, sub_self, max_self, mul_zero, add_zero, one_mul]
  nlinarith

/-- **Witness DF-4, lower bound.** For `pm = (δ_{-1} + δ_1)/2` (second moment `1 ≤ d = 1`) on the
uniform grid `t_k = k`, the per-step discretisation KL of the `σ² = β/α²` sampler satisfies
`(N - 1)/2 ≤ ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), β_k/α_k²)) dp_k`, for every `N`. -/
theorem perStep_ddpm_witness (N : ℕ) :
    ENNReal.ofReal (((N - 1 : ℕ) : ℝ) / 2) ≤
      ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel pm unifGrid k y)
        (Measure.pi fun i => gaussianReal (postMean pm unifGrid k y i) (ddpmVar unifGrid k))
          ∂(fwdLaw pm unifGrid k) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (sum_lintegral_klDiv_revKernel_ddpm_ge pm
    (integrable_sqNorm_twoPoint _ _) (by rw [secondMoment_pm']; simp) unifGrid_zero
    unifGrid_strictMono N)
  have h : ((N - 1 : ℕ) : ℝ) ≤ ∑ k ∈ Ioc 1 N,
      (2 * (unifGrid k - unifGrid (k - 1)) - fwdVar unifGrid k) := by
    have := Finset.card_nsmul_le_sum (Ioc 1 N)
      (fun k => 2 * (unifGrid k - unifGrid (k - 1)) - fwdVar unifGrid k) 1 fun k hk =>
      step_unifGrid (by simp only [mem_Ioc] at hk; omega)
    simpa [Nat.card_Ioc] using this
  push_cast
  linarith

/-- **Witness DF-4, upper bound.** For `pm` on `t_k = k`, the exact-score sampler with
`σ_k² = β_k` has `KL(p_1 ‖ q_1) ≤ 1` for every `N ≥ 1` (uniformly in `N` and `T`). -/
theorem output_betaVar_witness {N : ℕ} (hN : 1 ≤ N) :
    klDiv (fwdLaw pm unifGrid 1) (algLaw (betaVar unifGrid)
      (scoreMean unifGrid (exactScore pm unifGrid))
        (measurable_scoreMean unifGrid (measurable_exactScore pm unifGrid)) N 1) ≤ 1 := by
  have hu : 0 < heatTime unifGrid 1 :=
    heatTime_pos unifGrid_zero unifGrid_strictMono le_rfl
  have h := klDiv_output_le_betaVar_explicit pm (integrable_sqNorm_twoPoint _ _) unifGrid_zero
    unifGrid_strictMono (κ := (heatTime unifGrid 1)⁻¹) le_rfl hN (fun k hk hk' => by omega)
    (by rw [inv_mul_cancel₀ hu.ne']) (by rw [inv_mul_cancel₀ hu.ne']; linarith [inv_pos.2 hu])
    (exactScore pm unifGrid) (measurable_exactScore pm unifGrid)
    (integrable_exactScore_err pm unifGrid N)
  have h0 : scoreErrBeta pm unifGrid (exactScore pm unifGrid) N = 0 := by
    simp [scoreErrBeta, scoreErrW, exactScore]
  rw [h0, add_zero] at h
  exact h.trans (ENNReal.ofReal_le_one.2 (betaBound_unifGrid_le hN))

/-- **Witness DF-5.** For `pm` on `t_k = k` and every `N ≥ 1`: the path KL of the
`σ² = β/α²` sampler, even with the exact Bayes means `m*_k`, is `≥ (N - 1)/2`, while the path
KL of the `σ² = β` sampler with the same means is `≤ 1`; and output KL `≤` path KL. -/
theorem path_witness {N : ℕ} (hN : 1 ≤ N) :
    ENNReal.ofReal (((N - 1 : ℕ) : ℝ) / 2) ≤
        klDiv (truePath pm unifGrid N (N - 1))
          (algPath (ddpmVar unifGrid) (postMean pm unifGrid) (measurable_postMean pm unifGrid)
            N (N - 1)) ∧
      klDiv (truePath pm unifGrid N (N - 1))
          (algPath (betaVar unifGrid) (postMean pm unifGrid) (measurable_postMean pm unifGrid)
            N (N - 1)) ≤ 1 ∧
      klDiv (fwdLaw pm unifGrid 1) (algLaw (betaVar unifGrid) (postMean pm unifGrid)
          (measurable_postMean pm unifGrid) N 1) ≤ 1 := by
  have hu : 0 < heatTime unifGrid 1 :=
    heatTime_pos unifGrid_zero unifGrid_strictMono le_rfl
  have hup := (klDiv_truePath_betaVar_le_explicit pm (integrable_sqNorm_twoPoint _ _)
    unifGrid_zero unifGrid_strictMono (κ := (heatTime unifGrid 1)⁻¹) le_rfl hN
    (fun k hk hk' => by omega)
    (by rw [inv_mul_cancel₀ hu.ne']) (by rw [inv_mul_cancel₀ hu.ne']; linarith [inv_pos.2 hu])
    (N := N)).trans (ENNReal.ofReal_le_one.2 (betaBound_unifGrid_le hN))
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) (klDiv_truePath_ddpm_ge_uniform pm
    (integrable_sqNorm_twoPoint _ _) (by rw [secondMoment_pm']; simp) unifGrid_zero
    unifGrid_strictMono _ _ hN one_pos fun k _ _ => by simp [unifGrid]),
    hup, (klDiv_output_le_path pm unifGrid _ _ _ hN).trans hup⟩
  have hN1 : unifGrid N - unifGrid 1 = ((N - 1 : ℕ) : ℝ) := by
    simp only [unifGrid]; rw [Nat.cast_sub hN, Nat.cast_one]
  rw [hN1]
  rw [div_one, Nat.cast_one]
  have e : 1 / 2 * ((N - 1 : ℕ) : ℝ) * (2 - (1 - Real.exp (-2 * 1))) =
      ((N - 1 : ℕ) : ℝ) / 2 + ((N - 1 : ℕ) : ℝ) * Real.exp (-2 * 1) / 2 := by ring
  rw [e]
  exact le_add_of_nonneg_right (by positivity)

/-! ### DF-6: geometric grid `u_1 = 1`, `r = e²` -/

/-- **Witness DF-6, two-point data.** For `pm` (second moment `1`) on `geomGrid 1 (e²)`
(`log r - 1 + 1/r = 1 + e^{-2}`), the per-step sum of the `σ² = β/α²` sampler is
`≥ (N - 2)/2` for every `N ≥ 1`: strictly positive and linear in `N` for `N ≥ 3`. -/
theorem rate_witness_pm {N : ℕ} (hN : 1 ≤ N) :
    ENNReal.ofReal ((((N - 1 : ℕ) : ℝ) - 1) / 2) ≤
      ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel pm (geomGrid 1 (Real.exp 2)) k y)
        (Measure.pi fun i => gaussianReal (postMean pm (geomGrid 1 (Real.exp 2)) k y i)
          (ddpmVar (geomGrid 1 (Real.exp 2)) k)) ∂(fwdLaw pm (geomGrid 1 (Real.exp 2)) k) := by
  have he := three_le_exp_two
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (sum_lintegral_klDiv_revKernel_geomGrid_ge pm
    (integrable_sqNorm_twoPoint _ _) one_pos (by linarith) le_rfl hN)
  rw [secondMoment_pm', Real.log_exp, Nat.sub_self, pow_zero]
  have hl := Real.log_two_lt_d9
  norm_num at hl
  have : 0 ≤ ((N - 1 : ℕ) : ℝ) * (Real.exp 2)⁻¹ := by positivity
  norm_num
  nlinarith

/-- **Witness DF-6, point mass.** For `δ_0` on `ℝ` and `geomGrid 1 (e²)`: the per-step sum
equals `(N - 1)(1 + e^{-2})/2`, which is `> 0` for `N ≥ 2`, and the DF-1 discretisation bound
`(r - 1)/2 (1 + 2(N - 1))` is at most `2e²` times it plus `(e² - 1)/2`. -/
theorem rate_witness_dirac {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel (Measure.dirac (0 : Fin 1 → ℝ))
        (geomGrid 1 (Real.exp 2)) k y)
        (Measure.pi fun i => gaussianReal (postMean (Measure.dirac 0)
          (geomGrid 1 (Real.exp 2)) k y i) (ddpmVar (geomGrid 1 (Real.exp 2)) k))
          ∂(fwdLaw (Measure.dirac 0) (geomGrid 1 (Real.exp 2)) k) =
      ENNReal.ofReal (((N - 1 : ℕ) : ℝ) * (1 + Real.exp (-2)) / 2) ∧
    0 < ((N - 1 : ℕ) : ℝ) * (1 + Real.exp (-2)) / 2 ∧
    ENNReal.ofReal ((Real.exp 2 - 1) * ((1 : ℕ) : ℝ) / 2 *
        (1 + ((N - 1 : ℕ) : ℝ) * Real.log (Real.exp 2))) ≤
      ENNReal.ofReal (2 * Real.exp 2) *
        (∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel (Measure.dirac (0 : Fin 1 → ℝ))
          (geomGrid 1 (Real.exp 2)) k y)
          (Measure.pi fun i => gaussianReal (postMean (Measure.dirac 0)
            (geomGrid 1 (Real.exp 2)) k y i) (ddpmVar (geomGrid 1 (Real.exp 2)) k))
            ∂(fwdLaw (Measure.dirac 0) (geomGrid 1 (Real.exp 2)) k)) +
        ENNReal.ofReal ((Real.exp 2 - 1) * ((1 : ℕ) : ℝ) / 2) := by
  have he := three_le_exp_two
  have hr : 1 < Real.exp 2 := by linarith
  refine ⟨?_, ?_, discBound_geomGrid_le_dirac one_pos hr N⟩
  · rw [sum_lintegral_klDiv_revKernel_geomGrid_dirac one_pos hr N, Real.log_exp,
      one_div, ← Real.exp_neg]
    congr 1; push_cast; ring
  · have : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      rw [Nat.one_le_cast]; omega
    have := Real.exp_pos (-2)
    positivity

/-! ### DF-8: Gaussian data on `t_k = k/4` -/

/-- The uniform grid `t_k = k/4` (step `h = 1/4`). -/
noncomputable def quarterGrid : ℕ → ℝ := fun k => (k : ℝ) / 4

/-- `t_k = k/4` is strictly increasing. -/
theorem quarterGrid_strictMono : StrictMono quarterGrid := fun a b h => by
  simp only [quarterGrid]
  exact div_lt_div_of_pos_right (by exact_mod_cast h) (by norm_num)

/-- `t_0 = 0`. -/
theorem quarterGrid_zero : quarterGrid 0 = 0 := by simp [quarterGrid]

/-- `t_k = t_1 + (k - 1)/4`: the grid is uniform with step `h = 1/4`. -/
theorem quarterGrid_unif (k : ℕ) : quarterGrid k = quarterGrid 1 + ((k : ℝ) - 1) * (1 / 4) := by
  simp only [quarterGrid]; push_cast; ring

/-- `e^{2h} = e^{1/2} ≤ 2` for `h = 1/4`. -/
theorem exp_half_le_two : Real.exp (2 * (1 / 4)) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (2 * (1 / 4)) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (2 * (1 / 4))]

/-- `t_N - t_1 = (N - 1)/4`. -/
theorem quarterGrid_sub {N : ℕ} : quarterGrid N - quarterGrid 1 = ((N : ℝ) - 1) / 4 := by
  simp only [quarterGrid]; push_cast; ring

/-- **Witness DF-8, `v = 1`.** For `μ = N(0, 1)` on `ℝ`, `t_k = k/4`, `N ≥ 2`, exact score and
`σ² = β/α²`: `0 < (1/4)²(1 - e^{-(N-1)/2})²/3 ≤ KL(p_1 ‖ q_1) ≤ (e^{1/2} - 1)²/4 ≤ 1/4`, and
the path KL is `≥ (N - 1)/20`. -/
theorem gaussian_witness_one {N : ℕ} (hN : 2 ≤ N) :
    0 < (1 / 4 : ℝ) ^ 2 * (1 - Real.exp (-2 * (((N : ℝ) - 1) / 4))) ^ 2 / 3 ∧
    ENNReal.ofReal ((1 / 4 : ℝ) ^ 2 * (1 - Real.exp (-2 * (((N : ℝ) - 1) / 4))) ^ 2 / 3) ≤
        klDiv (fwdLaw (isoGauss 1 1) quarterGrid 1)
          (algLaw (ddpmVar quarterGrid) (scoreMean quarterGrid (exactScore (isoGauss 1 1)
            quarterGrid)) (measurable_scoreMean _ (measurable_exactScore _ _)) N 1) ∧
    klDiv (fwdLaw (isoGauss 1 1) quarterGrid 1)
          (algLaw (ddpmVar quarterGrid) (scoreMean quarterGrid (exactScore (isoGauss 1 1)
            quarterGrid)) (measurable_scoreMean _ (measurable_exactScore _ _)) N 1) ≤
        ENNReal.ofReal ((Real.exp (2 * (1 / 4)) - 1) ^ 2 / 4) ∧
    (Real.exp (2 * (1 / 4)) - 1) ^ 2 / 4 ≤ 1 / 4 ∧
    ENNReal.ofReal (((N : ℝ) - 1) / 20) ≤
        klDiv (truePath (isoGauss 1 1) quarterGrid N (N - 1))
          (algPath (ddpmVar quarterGrid) (scoreMean quarterGrid (exactScore (isoGauss 1 1)
            quarterGrid)) (measurable_scoreMean _ (measurable_exactScore _ _)) N (N - 1)) := by
  obtain ⟨hlo, hup, hpath⟩ := gaussian_output_two_sided (d := 1) one_pos le_rfl quarterGrid_zero
    quarterGrid_strictMono (by omega : 1 ≤ N) (by norm_num : (0 : ℝ) < 1 / 4) exp_half_le_two
    fun k _ _ => quarterGrid_unif k
  rw [quarterGrid_sub] at hlo hpath
  rw [DiffusionODELipschitz.gaussVar_one, sub_self, zero_mul, zero_add] at hup
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have he2 := exp_half_le_two
  have he1 : 1 ≤ Real.exp (2 * (1 / 4)) := Real.one_le_exp (by norm_num)
  refine ⟨?_, by simpa using hlo, by simpa using hup, ?_, ?_⟩
  · have : Real.exp (-2 * (((N : ℝ) - 1) / 4)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have : 0 < 1 - Real.exp (-2 * (((N : ℝ) - 1) / 4)) := by linarith
    positivity
  · nlinarith
  · refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) hpath
    push_cast; ring

/-- **Witness DF-8, `v = 1/2`.** For `μ = N(0, 1/2)` on `ℝ`, `t_k = k/4`, `N ≥ 2`: the same
strictly positive lower bound `(1/4)²(1 - e^{-(N-1)/2})²/3 ≤ KL(p_1 ‖ q_1)`, the finite upper
bound `((1/2) e^{-2(2t_N - t_1)} + e^{1/2} - 1)²/(4 s_1²)` with `s_1 ≥ 1/2` (so the bound is
`≤ 9/4`), and path KL `≥ (N - 1)/20`. -/
theorem gaussian_witness_half {N : ℕ} (hN : 2 ≤ N) :
    0 < (1 / 4 : ℝ) ^ 2 * (1 - Real.exp (-2 * (((N : ℝ) - 1) / 4))) ^ 2 / 3 ∧
    ENNReal.ofReal ((1 / 4 : ℝ) ^ 2 * (1 - Real.exp (-2 * (((N : ℝ) - 1) / 4))) ^ 2 / 3) ≤
        klDiv (fwdLaw (isoGauss 1 (1 / 2)) quarterGrid 1)
          (algLaw (ddpmVar quarterGrid) (scoreMean quarterGrid (exactScore (isoGauss 1 (1 / 2))
            quarterGrid)) (measurable_scoreMean _ (measurable_exactScore _ _)) N 1) ∧
    klDiv (fwdLaw (isoGauss 1 (1 / 2)) quarterGrid 1)
          (algLaw (ddpmVar quarterGrid) (scoreMean quarterGrid (exactScore (isoGauss 1 (1 / 2))
            quarterGrid)) (measurable_scoreMean _ (measurable_exactScore _ _)) N 1) ≤
        ENNReal.ofReal (((1 - 1 / 2) * Real.exp (-2 * (2 * quarterGrid N - quarterGrid 1)) +
          (Real.exp (2 * (1 / 4)) - 1)) ^ 2 / (4 * gaussVar (1 / 2) quarterGrid 1 ^ 2)) ∧
    ((1 - 1 / 2) * Real.exp (-2 * (2 * quarterGrid N - quarterGrid 1)) +
          (Real.exp (2 * (1 / 4)) - 1)) ^ 2 / (4 * gaussVar (1 / 2) quarterGrid 1 ^ 2) ≤ 9 / 4 ∧
    ENNReal.ofReal (((N : ℝ) - 1) / 20) ≤
        klDiv (truePath (isoGauss 1 (1 / 2)) quarterGrid N (N - 1))
          (algPath (ddpmVar quarterGrid) (scoreMean quarterGrid (exactScore (isoGauss 1 (1 / 2))
            quarterGrid)) (measurable_scoreMean _ (measurable_exactScore _ _)) N (N - 1)) := by
  obtain ⟨hlo, hup, hpath⟩ := gaussian_output_two_sided (d := 1) (v := 1 / 2) (by norm_num)
    (by norm_num) quarterGrid_zero quarterGrid_strictMono (by omega : 1 ≤ N)
    (by norm_num : (0 : ℝ) < 1 / 4) exp_half_le_two fun k _ _ => quarterGrid_unif k
  rw [quarterGrid_sub] at hlo hpath
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have he2 := exp_half_le_two
  have he1 : 1 ≤ Real.exp (2 * (1 / 4)) := Real.one_le_exp (by norm_num)
  refine ⟨?_, by simpa using hlo, by simpa using hup, ?_, ?_⟩
  · have : Real.exp (-2 * (((N : ℝ) - 1) / 4)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have : 0 < 1 - Real.exp (-2 * (((N : ℝ) - 1) / 4)) := by linarith
    positivity
  · have hs : 1 / 2 ≤ gaussVar (1 / 2) quarterGrid 1 := by
      rw [gaussVar]
      have := Real.exp_pos (-2 * quarterGrid 1)
      have : Real.exp (-2 * quarterGrid 1) ≤ 1 :=
        Real.exp_le_one_iff.2 (by simp [quarterGrid])
      nlinarith
    have hE : Real.exp (-2 * (2 * quarterGrid N - quarterGrid 1)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by simp only [quarterGrid]; push_cast; nlinarith)
    have hE0 := Real.exp_pos (-2 * (2 * quarterGrid N - quarterGrid 1))
    rw [div_le_iff₀ (by positivity)]
    have hnum : ((1 - 1 / 2) * Real.exp (-2 * (2 * quarterGrid N - quarterGrid 1)) +
        (Real.exp (2 * (1 / 4)) - 1)) ^ 2 ≤ (3 / 2) ^ 2 := by
      apply pow_le_pow_left₀ (by nlinarith); nlinarith
    nlinarith
  · refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) hpath
    push_cast; ring

end FormalizeSampling.Audit.DiffusionAdvancedRate
