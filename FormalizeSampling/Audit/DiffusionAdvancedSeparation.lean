module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import FormalizeSampling.Samplers.DiffusionMemorization
public import FormalizeSampling.Samplers.DiffusionODELipschitz
public import FormalizeSampling.Audit.Diffusion

/-!
# Statement audit: memorisation and deterministic-sampler witnesses (DF-2, DF-3, DF-7, DF-9)

Non-vacuity witnesses for the diffusion rows DF-2, DF-3, DF-7 and DF-9: each headline theorem is
applied to a concrete instance on `Fin 1 → ℝ` with every hypothesis discharged in Lean, and the
conclusion is made explicit.

* **DF-2** (`DiffusionMemorization.output_concentrates_on_training_set`): training set
  `{0, 1}` (empirical law of two distinct points, no Lebesgue density), radius `ρ = 1/4`,
  `ε = 1/4`: some exact-score sampler puts mass `≥ 3/4` within `1/4` of the training points and
  mass `≤ 1/4` on the set of points at distance `≥ 1/4` from both, a set containing the whole
  segment `[1/4, 3/4]` between them (in particular the midpoint `1/2`).
* **DF-3** (`DiffusionODESeparation.pf_ddpm_separation_geomGrid`) and **DF-7**
  (`DiffusionODESmooth.pf_ddpm_smooth_separation_geomGrid`): data `(δ_{-1} + δ_1)/2`
  (non-Gaussian, no density), probability-flow (exponential-integrator) step, geometric grid
  `u_1 = 1`, `r = 2`, `N = 2`, score accuracy `ε = 1/2`. The deterministic sampler has
  `TV(p_1, q_1) = 1` (DF-3), resp. `TV ≥ 9/10` with an analytic score error (DF-7, `η = 1/10`),
  while DDPM with the same score has `TV(p_1, q_1) ≤ 4/5`, a strict separation.
* **DF-9** (`DiffusionODELipschitz.pf_isoGauss_coupling`): data `N(0, 1)`, uniform grid
  `t_k = k`, any `N ≥ 1`, learned score `∇ log p_k + ε` (a constant shift, uniformly
  `ε`-accurate). The probability-flow output is coupled with `N(0, 1)` (which is here the exact
  deterministic output, and the data law itself) with `|x - x*| ≤ (N - 1)(e - 1) ε` a.s. and
  `∫ |x - x*|² ≤ ((N - 1)(e - 1) ε)²`.

## Main results

* `memorisation_witness` (DF-2).
* `ddpmBound_pm_le`: the DF-1 bound `√((I + (r-1)d/2 (1 + (N-1) log r) + β_2 ε²/2)/2)` for
  `(δ_{-1} + δ_1)/2`, `u_1 = 1`, `r = 2`, `N = 2`, `ε ≤ 1/2` is `≤ 4/5`.
* `pf_separation_witness` (DF-3), `pf_smooth_separation_witness` (DF-7).
* `pfGain_one`, `pfCoeff_unifGrid`, `lipBound_unifGrid`, `algVar_pfGain_one`,
  `pf_coupling_witness` (DF-9).

## Not proved here

* DF-2: no statement that `q_1` differs from a law that is not concentrated (the "far" set is
  only shown to be nonempty and to contain `[1/4, 3/4]`); the parameters `(u_1, r, N)` are
  existential.
* DF-3/DF-7: the DDPM bound `4/5` is far from tight (the actual TV is not computed).
* DF-9: tightness of the coupling bound for the constant shift is not proved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.Audit.DiffusionAdvancedSeparation

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
  FormalizeSampling.Audit.Diffusion FormalizeSampling.DiffusionMemorization
  FormalizeSampling.DiffusionODESeparation FormalizeSampling.DiffusionODESmooth
  FormalizeSampling.DiffusionODELipschitz FormalizeSampling.DiffusionGaussian
open FormalizeSampling.FokkerPlanckExistence (sqDist)
open FormalizeSampling.RGOCouplingChainPi (eDist)
open FormalizeSampling.ProximalLogConcaveRatePi (sqCostPi)

/-! ### DF-2: memorisation for a two-point training set -/

/-- The training set `{0, 1}` in `Fin 1 → ℝ`. -/
noncomputable def train01 : Fin 2 → Fin 1 → ℝ := ![fun _ => 0, fun _ => 1]

/-- Every point `y` with `y 0 ∈ [1/4, 3/4]` (e.g. the midpoint `1/2`) is at distance `≥ 1/4`
from both training points. -/
theorem segment_subset_far {y : Fin 1 → ℝ} (h1 : 1 / 4 ≤ y 0) (h2 : y 0 ≤ 3 / 4) :
    y ∈ ⋂ i, {z | (1 / 4 : ℝ) ^ 2 ≤ sqDist (train01 i) z} := by
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro i
  fin_cases i <;> simp [train01, sqDist] <;> nlinarith

/-- **Witness DF-2.** For the empirical law of the two distinct points `0, 1 ∈ ℝ` (no Lebesgue
density), radius `1/4` and `ε = 1/4`, some exact-score DDPM sampler on a geometric grid puts
mass `≥ 3/4` within distance `1/4` of the training points and mass `≤ 1/4` on the points at
distance `≥ 1/4` from both; that set contains every `y` with `y 0 ∈ [1/4, 3/4]`. -/
theorem memorisation_witness :
    ¬ empirical train01 ≪ volume ∧
    (∀ y : Fin 1 → ℝ, 1 / 4 ≤ y 0 → y 0 ≤ 3 / 4 →
      y ∈ ⋂ i, {z | (1 / 4 : ℝ) ^ 2 ≤ sqDist (train01 i) z}) ∧
    ∃ u1 : ℝ, 0 < u1 ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      (exactScoreOutput (empirical train01) u1 r N).real
          (⋂ i, {y | (1 / 4 : ℝ) ^ 2 ≤ sqDist (train01 i) y}) ≤ 1 / 4 ∧
      3 / 4 ≤ (exactScoreOutput (empirical train01) u1 r N).real
          (⋃ i, {y | sqDist (train01 i) y < (1 / 4 : ℝ) ^ 2}) := by
  refine ⟨empirical_not_ac (d := 0) train01, fun y h1 h2 => segment_subset_far h1 h2, ?_⟩
  obtain ⟨u1, hu1, r, hr, N, hN, hfar, hnear⟩ :=
    exists_output_near_training_set train01 two_pos (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 4)
  exact ⟨u1, hu1, r, hr, N, hN, hfar, by linarith⟩

/-! ### DF-3 and DF-7: two-point data, probability-flow step, `u_1 = 1`, `r = 2`, `N = 2` -/

/-- The data law `(δ_{-1} + δ_1)/2` on `Fin 1 → ℝ`. -/
noncomputable abbrev pm : Measure (Fin 1 → ℝ) := twoPoint (fun _ => -1) (fun _ => 1)

/-- `(δ_{-1} + δ_1)/2` has second moment `1`. -/
theorem secondMoment_pm : ∫ x, ∑ i, x i ^ 2 ∂pm = 1 := by
  simp only [pm, twoPoint]
  rw [integral_add_measure ((integrable_sqNorm_dirac _).smul_measure (by simp))
    ((integrable_sqNorm_dirac _).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  norm_num

/-- `β_k ≤ 1`. -/
theorem fwdVar_le_one (t : ℕ → ℝ) (k : ℕ) : fwdVar t k ≤ 1 := by
  have := sq_nonneg (fwdScale t k)
  rw [fwdVar]; linarith

/-- **The DDPM bound is `≤ 4/5`.** For `μ = (δ_{-1} + δ_1)/2`, `u_1 = 1`, `r = 2`, `N = 2` and
`0 ≤ ε ≤ 1/2`: `√((I + (r - 1) d/2 (1 + (N - 1) log r) + β_2 ε²/2)/2) ≤ 4/5`
(numerically `I = log 2 / 3 ≈ 0.23`, the discretisation term `(1 + log 2)/2 ≈ 0.85`). -/
theorem ddpmBound_pm_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    Real.sqrt ((initBound pm (geomGrid 1 2) 2 +
      (2 - 1) * ((1 : ℕ) : ℝ) / 2 * (1 + ((2 - 1 : ℕ) : ℝ) * Real.log 2) +
      fwdVar (geomGrid 1 2) 2 / 2 * ε ^ 2) / 2) ≤ 4 / 5 := by
  rw [initBound_geomGrid pm one_pos two_pos (by norm_num), secondMoment_pm]
  have hl := Real.log_two_lt_d9
  have hl' := Real.log_two_gt_d9
  have hlog : Real.log (1 / (1 + 1)) = -Real.log 2 := by
    rw [show (1 : ℝ) / (1 + 1) = 2⁻¹ by norm_num, Real.log_inv]
  have hβ := fwdVar_le_one (geomGrid 1 2) 2
  have hε2 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have hβε : fwdVar (geomGrid 1 2) 2 * ε ^ 2 ≤ 1 / 4 := by
    have h0 : 0 ≤ fwdVar (geomGrid 1 2) 2 :=
      fwdVar_nonneg_of_monotone (geomGrid_strictMono one_pos one_lt_two).monotone 2
    nlinarith [sq_nonneg ε]
  rw [Real.sqrt_le_left (by norm_num), hlog]
  norm_num
  nlinarith

/-- **Witness DF-3.** Data `(δ_{-1} + δ_1)/2` on `ℝ` (non-Gaussian, no Lebesgue density),
geometric grid `u_1 = 1`, `r = 2`, `N = 2`, score accuracy `ε = 1/2`: there is a measurable
learned score, uniformly `1/2`-accurate, such that the deterministic probability-flow sampler
has `TV(p_1, q_1) = 1` while DDPM with the same score has `TV(p_1, q_1) ≤ 4/5 < 1`. -/
theorem pf_separation_witness :
    ¬ pm ≪ volume ∧
    ∃ (s : ℕ → (Fin 1 → ℝ) → Fin 1 → ℝ) (hs : ∀ k, Measurable (s k)),
      (∀ k y, ∑ i, (s k y i - score (fwdDensity pm (geomGrid 1 2) k) y i) ^ 2 ≤ (1 / 2) ^ 2) ∧
      TotalVariation.tvSup (fwdLaw pm (geomGrid 1 2) 1)
        (algLaw zeroVar (pfMean (geomGrid 1 2) s)
          (measurable_detMean (measurable_pfLin _) _ hs) 2 1) = 1 ∧
      TotalVariation.tvSup (fwdLaw pm (geomGrid 1 2) 1)
        (algLaw (ddpmVar (geomGrid 1 2)) (scoreMean (geomGrid 1 2) s)
          (measurable_scoreMean _ hs) 2 1) ≤ 4 / 5 := by
  refine ⟨twoPoint_not_ac (d := 0) _ _, ?_⟩
  obtain ⟨s, hs, hacc, hdet, hddpm⟩ := pf_ddpm_separation_geomGrid pm
    (integrable_sqNorm_twoPoint _ _) one_pos one_pos one_lt_two le_rfl
    (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨s, hs, hacc, hdet, hddpm.trans (ddpmBound_pm_le (by norm_num) le_rfl)⟩

/-- **Witness DF-7.** Same instance as `pf_separation_witness` with `η = 1/10`: there are a
measurable learned score `s` and an analytic (`C^∞`) error field `E` with `|E| ≤ 1/2`, `s` exact
except at step `2` where `s_2 = ∇ log p_2 + E(z)`, such that the deterministic probability-flow
sampler has `TV(p_1, q_1) ≥ 9/10` while DDPM with the same score has `TV(p_1, q_1) ≤ 4/5`. -/
theorem pf_smooth_separation_witness :
    ∃ (s : ℕ → (Fin 1 → ℝ) → Fin 1 → ℝ) (hs : ∀ k, Measurable (s k))
      (E : (Fin 1 → ℝ) → Fin 1 → ℝ),
      ContDiff ℝ ⊤ E ∧ (∀ z, ∑ i, E z i ^ 2 ≤ (1 / 2) ^ 2) ∧
      (∀ k, k ≠ 2 → ∀ y, s k y = score (fwdDensity pm (geomGrid 1 2) k) y) ∧
      (∀ y, s 2 y = score (fwdDensity pm (geomGrid 1 2) 2) y +
        E (pfMean (geomGrid 1 2) (exactScore pm (geomGrid 1 2)) 2 y)) ∧
      9 / 10 ≤ TotalVariation.tvSup (fwdLaw pm (geomGrid 1 2) 1)
        (algLaw zeroVar (pfMean (geomGrid 1 2) s)
          (measurable_detMean (measurable_pfLin _) _ hs) 2 1) ∧
      TotalVariation.tvSup (fwdLaw pm (geomGrid 1 2) 1)
        (algLaw (ddpmVar (geomGrid 1 2)) (scoreMean (geomGrid 1 2) s)
          (measurable_scoreMean _ hs) 2 1) ≤ 4 / 5 := by
  obtain ⟨s, hs, E, hE, hEb, hk, h2, -, hdet, hddpm⟩ := pf_ddpm_smooth_separation_geomGrid pm
    (integrable_sqNorm_twoPoint _ _) one_pos one_pos one_lt_two le_rfl
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10)
  refine ⟨s, hs, E, hE, hEb, hk, h2, by linarith, ?_⟩
  exact hddpm.trans (ddpmBound_pm_le (by norm_num) le_rfl)

/-! ### DF-9: Gaussian data, uniform grid, constant score error -/

/-- The uniform grid `t_k = k`. -/
noncomputable def unifGrid : ℕ → ℝ := fun k => k

/-- `t_k = k` is strictly increasing. -/
theorem unifGrid_strictMono : StrictMono unifGrid := Nat.strictMono_cast

/-- `t_0 = 0`. -/
theorem unifGrid_zero : unifGrid 0 = 0 := by simp [unifGrid]

/-- On the uniform grid `α_k = e^{-1}` for `k ≥ 1`. -/
theorem fwdScale_unifGrid {k : ℕ} (hk : 1 ≤ k) : fwdScale unifGrid k = Real.exp (-1) := by
  rw [fwdScale, unifGrid, unifGrid, Nat.cast_sub hk]
  congr 1; push_cast; ring

/-- On the uniform grid `b_k = α_k⁻¹ - 1 = e - 1` for `k ≥ 1`. -/
theorem pfCoeff_unifGrid {k : ℕ} (hk : 1 ≤ k) : pfCoeff unifGrid k = Real.exp 1 - 1 := by
  rw [pfCoeff, fwdScale_unifGrid hk, Real.exp_neg, inv_inv]

/-- For `N(0, 1)` data the forward variance is `s_k = 1`. -/
theorem gaussVar_one (t : ℕ → ℝ) (k : ℕ) : gaussVar 1 t k = 1 := by
  rw [gaussVar]; ring

/-- For `N(0, 1)` data the probability-flow gain is `g_k = α_k⁻¹ - (α_k⁻¹ - 1) = 1`. -/
theorem pfGain_one (t : ℕ → ℝ) (k : ℕ) : pfGain 1 t k = 1 := by
  rw [pfGain, gaussVar_one, div_one, pfCoeff]; ring

/-- With gains `1` and zero variance the algorithm variance stays `1`. -/
theorem algVar_pfGain_one (t : ℕ → ℝ) {N k : ℕ} (hk : k ≤ N) :
    algVar (pfGain 1 t) zeroVar N k = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, N = k + j := ⟨N - k, by omega⟩
  induction j generalizing k with
  | zero => simpa using algVar_self (pfGain 1 t) zeroVar k
  | succ j ih =>
    rw [algVar_of_lt _ _ (by omega : k < k + (j + 1)), pfGain_one,
      show k + (j + 1) = (k + 1) + j by ring, ih (by omega)]
    simp [zeroVar]

/-- The coupling bound on the uniform grid for `N(0,1)` data and constant accuracy `ε`:
`B = ∑_{1 < i ≤ N} (∏ 1) (e - 1) ε = (N - 1)(e - 1) ε`. -/
theorem lipBound_unifGrid (ε : ℝ) (N : ℕ) :
    lipBound (fun i => |pfGain 1 unifGrid i|) (fun i => |pfCoeff unifGrid i| * ε) N 1 =
      ((N - 1 : ℕ) : ℝ) * ((Real.exp 1 - 1) * ε) := by
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [lipBound, Finset.sum_congr rfl fun i hi => by
    rw [Finset.prod_congr rfl fun j _ => by rw [pfGain_one, abs_one], Finset.prod_const_one,
      one_mul, pfCoeff_unifGrid (by simp only [Finset.mem_Ioc] at hi; omega), abs_of_nonneg he],
    Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

/-- The learned score `∇ log p_k + ε` (every coordinate shifted by `ε`) for `N(0, 1)` data. -/
noncomputable def shiftScore (ε : ℝ) : ℕ → (Fin 1 → ℝ) → Fin 1 → ℝ :=
  fun k y => exactScore (isoGauss 1 1) unifGrid k y + fun _ => ε

/-- The shifted score is measurable. -/
theorem measurable_shiftScore (ε : ℝ) (k : ℕ) : Measurable (shiftScore ε k) :=
  (measurable_exactScore _ _ k).add measurable_const

/-- **Witness DF-9.** Data `N(0, 1)` on `ℝ`, uniform grid `t_k = k`, `N ≥ 1`, `ε ≥ 0`, learned
score `∇ log p_k + ε` (uniformly `ε`-accurate). The deterministic probability-flow output `q_1`
and `N(0, 1)` (the exact-score deterministic output, equal to the data law) admit a coupling
`Γ` with `|x - x*| ≤ (N - 1)(e - 1) ε` `Γ`-a.s. and `∫⁻ |x - x*|² dΓ ≤ ((N - 1)(e - 1) ε)²`. -/
theorem pf_coupling_witness {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ k y, ∑ j, (shiftScore ε k y j -
      score (fwdDensity (isoGauss 1 1) unifGrid k) y j) ^ 2 ≤ ε ^ 2) ∧
    ∃ Γ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ)), IsProbabilityMeasure Γ ∧
      Γ.map Prod.fst = algLaw zeroVar (pfMean unifGrid (shiftScore ε))
        (measurable_detMean (measurable_pfLin unifGrid) _ (measurable_shiftScore ε)) N 1 ∧
      Γ.map Prod.snd = isoGauss 1 1 ∧
      (∀ᵐ p ∂Γ, eDist p.1 p.2 ≤ ((N - 1 : ℕ) : ℝ) * ((Real.exp 1 - 1) * ε)) ∧
      sqCostPi Γ ≤ ENNReal.ofReal ((((N - 1 : ℕ) : ℝ) * ((Real.exp 1 - 1) * ε)) ^ 2) := by
  have hacc : ∀ k y, ∑ j, (shiftScore ε k y j -
      score (fwdDensity (isoGauss 1 1) unifGrid k) y j) ^ 2 ≤ ε ^ 2 := fun k y => by
    simp [shiftScore, exactScore]
  refine ⟨hacc, ?_⟩
  obtain ⟨Γ, hΓ, h1, h2, h3, h4⟩ := pf_isoGauss_coupling one_pos unifGrid_zero
    unifGrid_strictMono hN (measurable_shiftScore ε) (ε := fun _ => ε) (fun _ _ _ => hε)
    (fun i _ _ y => hacc i y)
  rw [lipBound_unifGrid] at h3 h4
  rw [algVar_pfGain_one _ hN] at h2
  exact ⟨Γ, hΓ, h1, h2, h3, h4⟩

end FormalizeSampling.Audit.DiffusionAdvancedSeparation
