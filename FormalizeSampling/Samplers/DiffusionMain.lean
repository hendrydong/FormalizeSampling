module

public import FormalizeSampling.Samplers.Diffusion
public import FormalizeSampling.Samplers.DiffusionDiscretizationStep

/-!
# The `d`-linear KL bound for the DDPM sampler

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean`: data law `μ` on `Fin d → ℝ` with finite second
moment (no density, smoothness or log-concavity assumed), grid `0 = t_0 < t_1 < ⋯ < t_N`,
forward OU steps `F_k(x) = N(α_k x, β_k I)` with `α_k = e^{-(t_k - t_{k-1})}`, `β_k = 1 - α_k²`,
marginals `p_k`, and the DDPM sampler started at `q_N = N(0, I)` with reverse steps
`Q_k(y) = N(α_k⁻¹ (y + β_k s_k(y)), (β_k / α_k²) I)` for a learned score `s_k`. Write
`u_k = e^{2 t_k} - 1` (`heatTime`).

**Main theorem** (`klDiv_output_le_ddpm_grid`). If `u_{k+1} - u_k ≤ κ u_k` for `1 ≤ k < N`, then
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + (κ d / 2) (1 + log(u_N / u_1))
  + ∑_{k=2}^N (β_k / 2) ∫ |s_k - ∇ log p_k|² dp_k`.
For the geometric grid `u_k = u_1 r^{k-1}` (`geomGrid`) the discretisation term is
`(r - 1) d / 2 (1 + (N - 1) log r)`; with `r = (u_N/u_1)^{1/(N-1)}` this is
`≈ d L (1 + L) / (2 (N - 1))`, `L = log(u_N/u_1) ≈ 2 T + log(1/(2 t_1))`: the `d`-linear rate of
Benton–De Bortoli–Doucet–Deligiannidis (2024), proved here without stochastic calculus.

Proof: the exact path decomposition `DiffusionPath.klDiv_truePath_eq_ddpm` + Theorem A
(`lintegral_klDiv_revKernel_ddpm_eq`, each reverse-step error is an exact entropy increment of
the heat flow) + Theorem B (`sum_entropyStep_le`, the increments telescope up to a Riemann
error controlled by `u J(u) ≤ d`) bound the path KL (`DiffusionPath.klDiv_truePath_ddpm_le`);
the output KL is at most the path KL (`DiffusionPath.klDiv_output_le_path`).

## Main results

* `sum_lintegral_klDiv_revKernel_ddpm_le`: the discretisation sum is
  `≤ (κ d / 2) (1 + log(u_N / u_1))`.
* `DiffusionPath.klDiv_truePath_ddpm_le`: the same bound for the path KL.
* `klDiv_output_le_ddpm_grid`: the headline KL bound.
* `klDiv_output_le_ddpm_grid_explicit`: with the initialisation error bounded explicitly by
  `e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² ∫ |x|² dμ) / 2`
  (`initBound`, the weighted score-error sums `scoreErrW`, `scoreErr`, and the generic step
  `klDiv_le_initBound_add`).
* `tvSup_output_le_ddpm_grid`: the TV corollary (Pinsker, `tvSup_le_sqrt_of_klDiv_le`).
* `geomGrid`, `klDiv_output_le_geomGrid`, `tvSup_output_le_geomGrid`: the geometric grid.
* `exactScore`, `measurable_exactScore`, `integrable_exactScore_err`, `scoreErr_exactScore`: the
  exact score `s_k = ∇ log p_k` is an admissible learned score with zero score error.
* `integrable_score_err_of_integrable_sq`, `integrable_score_err_of_bounded`: hypothesis `hsint`
  holds for every measurable learned score with `∫ |s_k|² dp_k < ∞` (resp. `|s_k|² ≤ B`).
* `exists_geomGrid_params`, `exists_klDiv_output_le`, `exists_tvSup_output_le`: with the exact
  score, for every data law with finite second moment, `u_1 > 0` and `ε > 0`, some geometric
  grid gives `KL(p_1 ‖ q_1) ≤ ε` (resp. `TV(p_1, q_1) ≤ ε`).

## Not proved here

* No bound on the score error `∫ |s_k - ∇ log p_k|² dp_k` (it is an input).
* The optimisation of `r` (or `N`) in terms of `T`, `t_1` is left as the informal remark above.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.Diffusion

variable {d : ℕ}

/-! ### Heat-flow time -/

/-- The heat-flow time `u_k = e^{2 t_k} - 1` of the OU time `t_k`. -/
noncomputable def heatTime (t : ℕ → ℝ) (k : ℕ) : ℝ := Real.exp (2 * t k) - 1

/-- `u_k > 0` for `k ≥ 1` when `t 0 = 0` and `t` is strictly increasing. -/
theorem heatTime_pos {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    0 < heatTime t k := by
  have : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  exact sub_pos.2 (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith))

/-- `k ↦ u_k` is monotone for a monotone grid. -/
theorem heatTime_mono {t : ℕ → ℝ} (ht : Monotone t) : Monotone (heatTime t) := fun _ _ h =>
  sub_le_sub_right (Real.exp_le_exp.2 (by linarith [ht h])) _

/-! ### The discretisation sum -/

/-- **Discretisation bound (Theorems A + B).** For data with finite second moment, `t 0 = 0`,
`t` strictly increasing, `N ≥ 1`, and a grid with `u_{k+1} - u_k ≤ κ u_k` for `1 ≤ k < N`
(`u = heatTime t`):
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k(y) ≤ (κ d / 2) (1 + log(u_N / u_1))`.
No sign condition on `κ` is assumed: for `N = 1` the sum is empty, and for `N ≥ 2` the grid
condition at `k = 1` forces `κ > 0`. -/
theorem sum_lintegral_klDiv_revKernel_ddpm_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) ≤
      ENNReal.ofReal (κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1))) := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · obtain rfl : N = 1 := by omega
    simp
  have hκ : 0 ≤ κ := by
    have hu1 := heatTime_pos h0 ht le_rfl
    have h12 : heatTime t 1 < heatTime t 2 :=
      sub_lt_sub_right (Real.exp_lt_exp.2 (by linarith [ht (show 1 < 2 by norm_num)])) _
    have := hgrid 1 le_rfl (by omega)
    nlinarith
  have hA : ∀ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
      (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) =
      ENNReal.ofReal (entropyStep μ (heatTime t (k - 1)) (heatTime t k)) := by
    intro k hk
    simp only [mem_Ioc] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [lintegral_klDiv_revKernel_ddpm_eq μ hμ h0 ht (by omega), Nat.add_sub_cancel]
    rfl
  rw [sum_congr rfl hA, ← ENNReal.ofReal_sum_of_nonneg fun k hk => by
    simp only [mem_Ioc] at hk
    exact entropyStep_nonneg μ hμ (heatTime_pos h0 ht (by omega))
      (heatTime_mono ht.monotone (by omega))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hre : ∑ k ∈ Ioc 1 N, entropyStep μ (heatTime t (k - 1)) (heatTime t k) =
      ∑ n ∈ range (N - 1), entropyStep μ (heatTime t (n + 1)) (heatTime t (n + 1 + 1)) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
      show N + 1 - (1 + 1) = N - 1 by omega]
    refine sum_congr rfl fun n _ => ?_
    rw [show 1 + 1 + n - 1 = n + 1 by omega, show 1 + 1 + n = n + 1 + 1 by omega]
  have hB := sum_entropyStep_le μ hμ (u := fun n => heatTime t (n + 1)) (N - 1) hκ
    (heatTime_pos h0 ht le_rfl) (fun n _ => heatTime_mono ht.monotone (by omega))
    (fun n hn => hgrid (n + 1) (by omega) (by omega))
  rw [hre]
  simpa only [show N - 1 + 1 = N by omega, zero_add] using hB

end FormalizeSampling.DiffusionDiscretization

/-! ### The path KL -/

namespace FormalizeSampling.DiffusionPath

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization

/-- **Path-KL upper bound for `σ² = β/α²`** (Theorem B on path space). For data with finite
second moment, `t 0 = 0`, `t` strictly increasing, `N ≥ 1`, a grid with
`u_{k+1} - u_k ≤ κ u_k` for `1 ≤ k < N` and measurable learned scores `s`:
`KL(truePath ‖ algPath) ≤ KL(p_N ‖ N(0,I)) + (κd/2)(1 + log(u_N/u_1))
  + ∑_{k=2}^N (β_k/2) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`. -/
theorem klDiv_truePath_ddpm_le {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {κ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) :
    klDiv (truePath μ t N (N - 1))
        (algPath (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N (N - 1)) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ENNReal.ofReal (κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1))) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / 2) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) := by
  rw [klDiv_truePath_eq_ddpm μ hμ ht s hs]
  gcongr
  exact sum_lintegral_klDiv_revKernel_ddpm_le μ hμ h0 ht hN hgrid

end FormalizeSampling.DiffusionPath

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-! ### The sampler -/

/-- **Main theorem: `d`-linear KL bound for the DDPM sampler.** For data with finite second
moment, `t 0 = 0`, `t` strictly increasing, `N ≥ 1`, a grid with `u_{k+1} - u_k ≤ κ u_k` for
`1 ≤ k < N` (`u_k = e^{2 t_k} - 1`), DDPM variance `σ_k² = β_k / α_k²` and any measurable learned
score `s`:
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + (κ d / 2) (1 + log(u_N / u_1))
  + ∑_{k=2}^N (β_k / 2) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`. -/
theorem klDiv_output_le_ddpm_grid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) :
    klDiv (fwdLaw μ t 1) (algLaw (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ENNReal.ofReal (κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1))) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / 2) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) :=
  (klDiv_output_le_path μ t _ _ _ hN).trans (klDiv_truePath_ddpm_le μ hμ h0 ht hN hgrid s hs)

/-- The explicit initialisation constant
`I = e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² ∫ ∑ᵢ xᵢ² dμ) / 2`
of `Diffusion.klDiv_fwdLaw_le_init`. -/
noncomputable def initBound (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.exp (-2 * (t N - t 1)) * ((d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
    fwdScale t 1 ^ 2 * ∫ x, ∑ i, x i ^ 2 ∂μ) / 2)

/-- `initBound μ t N ≥ 0` when `t 0 < t 1`. -/
theorem initBound_nonneg (μ : Measure (Fin d → ℝ)) {t : ℕ → ℝ} (ht : t 0 < t 1) (N : ℕ) :
    0 ≤ initBound μ t N := by
  have : 0 ≤ ∫ x, ∑ i, x i ^ 2 ∂μ := integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
    sq_nonneg _
  have := Real.log_le_sub_one_of_pos (fwdVar_pos (t := t) (k := 1) ht)
  have : 0 ≤ (d : ℝ) * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  unfold initBound
  positivity

/-- The weighted score-error term
`∑_{k=2}^N w_k ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)` for weights `w_k`. -/
noncomputable def scoreErrW (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (w : ℕ → ℝ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Ioc 1 N, w k * ∫ y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ∂(fwdLaw μ t k)

/-- `scoreErrW ≥ 0` for nonnegative weights. -/
theorem scoreErrW_nonneg (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) {w : ℕ → ℝ} {N : ℕ}
    (hw : ∀ k ∈ Ioc 1 N, 0 ≤ w k) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) :
    0 ≤ scoreErrW μ t w s N :=
  Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk)
    (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- For nonnegative weights and integrable score errors, the `ℝ≥0∞`-valued score-error sum of
the KL bounds is `ofReal (scoreErrW μ t w s N)`. -/
theorem sum_ofReal_mul_lintegral_eq_scoreErrW (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {w : ℕ → ℝ} {N : ℕ} (hw : ∀ k ∈ Ioc 1 N, 0 ≤ w k) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k)) :
    ∑ k ∈ Ioc 1 N, ENNReal.ofReal (w k) *
        ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
          ∂(fwdLaw μ t k) = ENNReal.ofReal (scoreErrW μ t w s N) := by
  rw [scoreErrW, ENNReal.ofReal_sum_of_nonneg fun k hk => mul_nonneg (hw k hk)
    (integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine sum_congr rfl fun k hk => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hsint k hk)
    (ae_of_all _ fun y => Finset.sum_nonneg fun i _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (hw k hk)]

/-- **Explicit form of a KL bound.** If `KL(P ‖ Q) ≤ KL(p_N ‖ N(0,I)) + D + ∑_{k=2}^N w_k ε_k²`
(`ε_k² = ∫ |s_k - ∇ log p_k|² dp_k`, integrable score errors, `D ≥ 0`, `w_k ≥ 0`), then, for a
data law with finite second moment and a strictly increasing grid,
`KL(P ‖ Q) ≤ I + D + scoreErrW μ t w s N`, with `I = initBound μ t N`. -/
theorem klDiv_le_initBound_add (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : StrictMono t) {N : ℕ}
    (hN : 1 ≤ N) {P Q : Measure (Fin d → ℝ)} {D : ℝ} (hD : 0 ≤ D) {w : ℕ → ℝ}
    (hw : ∀ k ∈ Ioc 1 N, 0 ≤ w k) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k))
    (h : klDiv P Q ≤ klDiv (fwdLaw μ t N) (stdGaussianPi d) + ENNReal.ofReal D +
      ∑ k ∈ Ioc 1 N, ENNReal.ofReal (w k) *
        ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
          ∂(fwdLaw μ t k)) :
    klDiv P Q ≤ ENNReal.ofReal (initBound μ t N + D + scoreErrW μ t w s N) := by
  have hI := initBound_nonneg μ (ht zero_lt_one) N
  rw [sum_ofReal_mul_lintegral_eq_scoreErrW μ t hw hsint] at h
  rw [ENNReal.ofReal_add (add_nonneg hI hD) (scoreErrW_nonneg μ t hw s),
    ENNReal.ofReal_add hI hD]
  refine h.trans ?_
  gcongr
  exact klDiv_fwdLaw_le_init μ hμ ht hN

/-- **Pinsker for the explicit bounds.** For probability measures `P Q` and any real `B`, if
`KL(P ‖ Q) ≤ ofReal B` then `TV(P, Q) ≤ √(B / 2)`. -/
theorem tvSup_le_sqrt_of_klDiv_le {P Q : Measure (Fin d → ℝ)} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {B : ℝ} (h : klDiv P Q ≤ ENNReal.ofReal B) :
    TotalVariation.tvSup P Q ≤ Real.sqrt (B / 2) := by
  refine (Pinsker.tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)).trans ?_
  rcases le_total 0 B with hB | hB
  · gcongr
    exact ENNReal.toReal_le_of_le_ofReal hB h
  · rw [ENNReal.ofReal_of_nonpos hB, nonpos_iff_eq_zero] at h
    simp only [h, ENNReal.toReal_zero, zero_div, Real.sqrt_zero]
    positivity

/-- The score-error term `∑_{k=2}^N (β_k / 2) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`
(`scoreErrW` with weights `β_k / 2`). -/
noncomputable def scoreErr (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) : ℝ :=
  scoreErrW μ t (fun k => fwdVar t k / 2) s N

/-- `(κ d / 2) (1 + log(u_N / u_1)) ≥ 0` for `κ ≥ 0`, `N ≥ 1`. -/
theorem discBound_nonneg {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {κ : ℝ} (hκ : 0 ≤ κ)
    {N : ℕ} (hN : 1 ≤ N) : 0 ≤ κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) := by
  have h1 := heatTime_pos h0 ht le_rfl
  have : 0 ≤ Real.log (heatTime t N / heatTime t 1) := Real.log_nonneg
    ((one_le_div h1).2 (heatTime_mono ht.monotone hN))
  positivity

/-- **Fully explicit KL bound.** Under the hypotheses of `klDiv_output_le_ddpm_grid`, if each
score error `∑ᵢ (s_k - ∂ᵢ log p_k)²` is `p_k`-integrable (`2 ≤ k ≤ N`):
`KL(p_1 ‖ q_1) ≤ e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² ∫ |x|² dμ) / 2
  + (κ d / 2) (1 + log(u_N / u_1)) + ∑_{k=2}^N (β_k / 2) ∫ |s_k - ∇ log p_k|² dp_k`.
The integrability hypothesis `hsint` holds whenever `∫ |s_k|² dp_k < ∞`
(`integrable_score_err_of_integrable_sq`), in particular for bounded scores
(`integrable_score_err_of_bounded`). -/
theorem klDiv_output_le_ddpm_grid_explicit (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 1 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k)) :
    klDiv (fwdLaw μ t 1) (algLaw (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      ENNReal.ofReal (initBound μ t N +
        κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) + scoreErr μ t s N) :=
  klDiv_le_initBound_add μ hμ ht hN (discBound_nonneg h0 ht hκ hN)
    (fun k hk => div_nonneg (fwdVar_pos_of_strictMono ht (by simp only [mem_Ioc] at hk; omega)).le
      zero_le_two) hsint (klDiv_output_le_ddpm_grid μ hμ h0 ht hN hgrid s hs)

/-- **TV corollary (Pinsker).** Under the hypotheses of `klDiv_output_le_ddpm_grid_explicit`:
`TV(p_1, q_1) ≤ √((I + (κ d / 2) (1 + log(u_N / u_1)) + ∑_{k=2}^N (β_k/2) ε_k²) / 2)`, with `I`
the explicit initialisation constant `initBound` and `ε_k² = ∫ |s_k - ∇ log p_k|² dp_k`. -/
theorem tvSup_output_le_ddpm_grid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 1 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k)) :
    TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      Real.sqrt ((initBound μ t N + κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) +
        scoreErr μ t s N) / 2) :=
  tvSup_le_sqrt_of_klDiv_le
    (klDiv_output_le_ddpm_grid_explicit μ hμ h0 ht hκ hN hgrid s hs hsint)

/-! ### The geometric grid -/

/-- The geometric grid: `t_0 = 0` and, for `k ≥ 1`, `t_k = log(1 + u_1 r^{k-1}) / 2`, i.e.
`u_k = e^{2 t_k} - 1 = u_1 r^{k-1}`. With `t_1 = δ` (`u_1 = e^{2δ} - 1`) and `t_N = T` this is the
exponentially-decaying-steps-near-`δ` schedule of Benton et al. -/
noncomputable def geomGrid (u1 r : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else Real.log (1 + u1 * r ^ (k - 1)) / 2

/-- `geomGrid u1 r 0 = 0`. -/
theorem geomGrid_zero (u1 r : ℝ) : geomGrid u1 r 0 = 0 := ite_eq_left rfl

/-- `u_k = u_1 r^{k-1}` on the geometric grid (`k ≥ 1`). -/
theorem heatTime_geomGrid {u1 r : ℝ} (hu1 : 0 < u1) (hr : 0 < r) {k : ℕ} (hk : 1 ≤ k) :
    heatTime (geomGrid u1 r) k = u1 * r ^ (k - 1) := by
  unfold heatTime geomGrid
  rw [ite_eq_right (by omega), show ∀ L : ℝ, 2 * (L / 2) = L from fun L => by ring,
    Real.exp_log (by positivity)]
  ring

/-- The geometric grid is strictly increasing for `u_1 > 0`, `r > 1`. -/
theorem geomGrid_strictMono {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r) :
    StrictMono (geomGrid u1 r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  refine strictMono_nat_of_lt_succ fun k => ?_
  rcases k with _ | m
  · rw [geomGrid_zero, geomGrid, ite_eq_right (by omega)]
    have : 0 < u1 * r ^ (0 + 1 - 1) := by positivity
    exact div_pos (Real.log_pos (by linarith)) two_pos
  · rw [geomGrid, geomGrid, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel,
      Nat.add_sub_cancel]
    have h1 : 0 < u1 * r ^ m := by positivity
    have h2 : u1 * r ^ m < u1 * r ^ (m + 1) :=
      mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hr (by omega)) hu1
    have := Real.log_lt_log (by linarith) (by linarith : 1 + u1 * r ^ m < 1 + u1 * r ^ (m + 1))
    linarith

/-- The geometric grid satisfies the grid condition with `κ = r - 1` (with equality). -/
theorem geomGrid_grid {u1 r : ℝ} (hu1 : 0 < u1) (hr : 0 < r) {k : ℕ} (hk : 1 ≤ k) :
    heatTime (geomGrid u1 r) (k + 1) - heatTime (geomGrid u1 r) k ≤
      (r - 1) * heatTime (geomGrid u1 r) k := by
  rw [heatTime_geomGrid hu1 hr hk, heatTime_geomGrid hu1 hr (by omega),
    show k + 1 - 1 = k - 1 + 1 by omega, pow_succ]
  linarith

/-- On the geometric grid, `log(u_N / u_1) = (N - 1) log r`. -/
theorem log_heatTime_geomGrid {u1 r : ℝ} (hu1 : 0 < u1) (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N) :
    Real.log (heatTime (geomGrid u1 r) N / heatTime (geomGrid u1 r) 1) =
      ((N - 1 : ℕ) : ℝ) * Real.log r := by
  rw [heatTime_geomGrid hu1 hr hN, heatTime_geomGrid hu1 hr le_rfl, Nat.sub_self, pow_zero,
    mul_one, mul_div_cancel_left₀ _ hu1.ne', Real.log_pow]

/-- On the geometric grid the initialisation constant is explicit in `u_1`, `u_N = u_1 r^{N-1}`
and the second moment `M₂ = ∫ |x|² dμ`:
`I = (1 + u_1) / (1 + u_N) · (d (v - 1 - log v) + M₂ / (1 + u_1)) / 2`, `v = u_1 / (1 + u_1)`.
(For small `u_1 ≈ 2δ` and large `u_N ≈ e^{2T}`: `I ≈ e^{-2T} (d log(1/(2δ)) + M₂) / 2`.) -/
theorem initBound_geomGrid (μ : Measure (Fin d → ℝ)) {u1 r : ℝ} (hu1 : 0 < u1) (hr : 0 < r)
    {N : ℕ} (hN : 1 ≤ N) :
    initBound μ (geomGrid u1 r) N = (1 + u1) / (1 + u1 * r ^ (N - 1)) *
      ((d * (u1 / (1 + u1) - 1 - Real.log (u1 / (1 + u1))) +
        (∫ x, ∑ i, x i ^ 2 ∂μ) / (1 + u1)) / 2) := by
  have h1 : geomGrid u1 r 1 = Real.log (1 + u1) / 2 := by
    rw [geomGrid, ite_eq_right (by omega), Nat.sub_self, pow_zero, mul_one]
  have hN' : geomGrid u1 r N = Real.log (1 + u1 * r ^ (N - 1)) / 2 := by
    rw [geomGrid, ite_eq_right (by omega)]
  have hpos1 : 0 < 1 + u1 := by linarith
  have hposN : 0 < 1 + u1 * r ^ (N - 1) := by positivity
  have hsq : fwdScale (geomGrid u1 r) 1 ^ 2 = 1 / (1 + u1) := by
    rw [fwdScale_sq, Nat.sub_self, geomGrid_zero, h1,
      show -2 * 1 * (Real.log (1 + u1) / 2 - 0) = -Real.log (1 + u1) by ring, Real.exp_neg,
      Real.exp_log hpos1, one_div]
  have hv : fwdVar (geomGrid u1 r) 1 = u1 / (1 + u1) := by
    rw [fwdVar, hsq]; field_simp; ring
  have he : Real.exp (-2 * (geomGrid u1 r N - geomGrid u1 r 1)) =
      (1 + u1) / (1 + u1 * r ^ (N - 1)) := by
    rw [hN', h1, show -2 * (Real.log (1 + u1 * r ^ (N - 1)) / 2 - Real.log (1 + u1) / 2) =
      Real.log (1 + u1) - Real.log (1 + u1 * r ^ (N - 1)) by ring, Real.exp_sub,
      Real.exp_log hpos1, Real.exp_log hposN]
  rw [initBound, he, hv, hsq]
  ring

/-- **KL bound on the geometric grid.** For data with finite second moment, `u_1 > 0`, `r > 1`,
`N ≥ 1`, the geometric grid `t = geomGrid u_1 r`, DDPM variance and any measurable learned score
with integrable errors:
`KL(p_1 ‖ q_1) ≤ I + (r - 1) d / 2 (1 + (N - 1) log r) + ∑_{k=2}^N (β_k / 2) ε_k²`, with `I`
given explicitly by `initBound_geomGrid`. -/
theorem klDiv_output_le_geomGrid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r)
    {N : ℕ} (hN : 1 ≤ N) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ (geomGrid u1 r) k) y i) ^ 2)
        (fwdLaw μ (geomGrid u1 r) k)) :
    klDiv (fwdLaw μ (geomGrid u1 r) 1) (algLaw (ddpmVar (geomGrid u1 r))
        (scoreMean (geomGrid u1 r) s) (measurable_scoreMean _ hs) N 1) ≤
      ENNReal.ofReal (initBound μ (geomGrid u1 r) N +
        (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
        scoreErr μ (geomGrid u1 r) s N) := by
  have h := klDiv_output_le_ddpm_grid_explicit μ hμ (geomGrid_zero u1 r)
    (geomGrid_strictMono hu1 hr) (by linarith : 0 ≤ r - 1) hN
    (fun k hk _ => geomGrid_grid hu1 (zero_lt_one.trans hr) hk) s hs hsint
  rwa [log_heatTime_geomGrid hu1 (zero_lt_one.trans hr) hN] at h

/-- **TV bound on the geometric grid.** Under the hypotheses of `klDiv_output_le_geomGrid`:
`TV(p_1, q_1) ≤ √((I + (r - 1) d / 2 (1 + (N - 1) log r) + ∑_{k=2}^N (β_k / 2) ε_k²) / 2)`. -/
theorem tvSup_output_le_geomGrid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r)
    {N : ℕ} (hN : 1 ≤ N) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ (geomGrid u1 r) k) y i) ^ 2)
        (fwdLaw μ (geomGrid u1 r) k)) :
    TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1) (algLaw (ddpmVar (geomGrid u1 r))
        (scoreMean (geomGrid u1 r) s) (measurable_scoreMean _ hs) N 1) ≤
      Real.sqrt ((initBound μ (geomGrid u1 r) N +
        (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
        scoreErr μ (geomGrid u1 r) s N) / 2) := by
  have h := tvSup_output_le_ddpm_grid μ hμ (geomGrid_zero u1 r)
    (geomGrid_strictMono hu1 hr) (by linarith : 0 ≤ r - 1) hN
    (fun k hk _ => geomGrid_grid hu1 (zero_lt_one.trans hr) hk) s hs hsint
  rwa [log_heatTime_geomGrid hu1 (zero_lt_one.trans hr) hN] at h

/-! ### The exact score: the bounds can be made arbitrarily small -/

/-- **Real-analysis core.** For `u_1 > 0`, `A ≥ 0`, `ε > 0` there are `r > 1`, `N ≥ 1` with
`(1 + u_1) / (1 + u_1 r^{N-1}) · A + (r - 1) d / 2 (1 + (N - 1) log r) ≤ ε`
(the initialisation and discretisation terms of `initBound_geomGrid` and
`klDiv_output_le_geomGrid`). -/
theorem exists_geomGrid_params (d : ℕ) {u1 A ε : ℝ} (hu1 : 0 < u1) (hA : 0 ≤ A)
    (hε : 0 < ε) : ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      (1 + u1) / (1 + u1 * r ^ (N - 1)) * A +
        (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) ≤ ε := by
  set X : ℝ := 2 * ((1 + u1) * A) / (ε * u1) with hX
  have hX0 : 0 ≤ X := by positivity
  set η : ℝ := min 1 (ε / ((d + 1) * (X + 2))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / ((d + 1) * (X + 2)) := min_le_right _ _
  set M : ℕ := ⌈X / η⌉₊ with hM
  have hM1 : X / η ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) < X / η + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMη1 : X ≤ M * η := by rwa [div_le_iff₀ hη0] at hM1
  have hMη2 : (M : ℝ) * η < X + η := by
    have := mul_lt_mul_of_pos_right hM2 hη0
    rwa [add_mul, div_mul_cancel₀ _ hη0.ne', one_mul] at this
  refine ⟨1 + η, by linarith, M + 1, by omega, ?_⟩
  rw [Nat.add_sub_cancel]
  have hpow : 1 + X ≤ (1 + η) ^ M := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ η) M
    linarith
  have hlog : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + η); linarith
  -- initialisation term
  have hinit : (1 + u1) / (1 + u1 * (1 + η) ^ M) * A ≤ ε / 2 := by
    have hD : u1 * X ≤ 1 + u1 * (1 + η) ^ M := by nlinarith
    have hD0 : 0 < 1 + u1 * (1 + η) ^ M := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hD0]
    have : (1 + u1) * A = ε / 2 * (u1 * X) := by
      rw [hX]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  -- discretisation term
  have hdisc : (1 + η - 1) * d / 2 * (1 + (M : ℝ) * Real.log (1 + η)) ≤ ε / 2 := by
    have h1 : (M : ℝ) * Real.log (1 + η) ≤ X + 1 :=
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans (by linarith)
    have h2 : (1 + η - 1) * d / 2 * (1 + (M : ℝ) * Real.log (1 + η)) ≤
        η * (d + 1) / 2 * (X + 2) := by
      rw [show 1 + η - 1 = η by ring]
      have : η * d / 2 ≤ η * (d + 1) / 2 := by nlinarith
      have h0 : 0 ≤ η * d / 2 := by positivity
      calc η * d / 2 * (1 + (M : ℝ) * Real.log (1 + η)) ≤ η * d / 2 * (X + 2) :=
            mul_le_mul_of_nonneg_left (by linarith) h0
        _ ≤ η * (d + 1) / 2 * (X + 2) := mul_le_mul_of_nonneg_right this (by linarith)
    have h3 : η * ((d + 1) * (X + 2)) ≤ ε := by
      rwa [le_div_iff₀ (by positivity)] at hηε
    linarith [show η * (d + 1) / 2 * (X + 2) = η * ((d + 1) * (X + 2)) / 2 by ring]
  linarith

/-- The exact score of the forward marginals, `s_k = ∇ log p_k` with `p_k = fwdDensity μ t k`,
used as the learned score. -/
noncomputable def exactScore {d : ℕ} (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) :
    ℕ → (Fin d → ℝ) → Fin d → ℝ :=
  fun k => score (fwdDensity μ t k)

/-- The exact score is measurable (each coordinate is `x ↦ fderiv (log ∘ p_k) x eᵢ`, which is
measurable for any function). -/
theorem measurable_exactScore {d : ℕ} (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (k : ℕ) :
    Measurable (exactScore μ t k) :=
  measurable_pi_iff.mpr fun _ => measurable_fderiv_apply_const ℝ _ _

/-- The score-error integrand `∑ᵢ (s_k - ∂ᵢ log p_k)²` of the exact score is identically `0`,
hence `p_k`-integrable for every `k`: hypothesis `hsint` of the headline theorems. -/
theorem integrable_exactScore_err {d : ℕ} (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (N : ℕ) :
    ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (exactScore μ t k y i - score (fwdDensity μ t k) y i) ^ 2)
        (fwdLaw μ t k) := fun k _ => by
  simp only [exactScore, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sum_const_zero]
  exact integrable_zero _ _ _

/-- **Discharging `hsint` for a square-integrable learned score.** Let `μ` be a probability law,
`t 0 = 0`, `t` strictly increasing, and `s_k` measurable learned scores with `∑ᵢ s_k(y)ᵢ²`
`p_k`-integrable for `2 ≤ k ≤ N`. Then the score-error integrand `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))²`
is `p_k`-integrable for `2 ≤ k ≤ N`: hypothesis `hsint` of the headline theorems. The exact
score is square-integrable under `p_k`, `k ≥ 1` (finite Fisher information,
`integral_score_sq_fwdDensity`), and `(u - v)² ≤ 2u² + 2v²`. No moment or regularity of `μ` is
used. -/
theorem integrable_score_err_of_integrable_sq (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hs : ∀ k, Measurable (s k))
    (hs2 : ∀ k ∈ Ioc 1 N, Integrable (fun y => ∑ i, s k y i ^ 2) (fwdLaw μ t k)) :
    ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k) := by
  intro k hk
  have hk1 : 1 ≤ k := by simp only [mem_Ioc] at hk; omega
  have hsc := (integral_score_sq_fwdDensity μ h0 ht hk1).1
  refine ((hs2 k hk).const_mul 2 |>.add (hsc.const_mul 2)).mono' ?_ (ae_of_all _ fun y => ?_)
  · refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
    exact (((measurable_pi_apply i).comp (hs k)).sub
      ((measurable_pi_apply i).comp (measurable_exactScore μ t k))).pow_const 2
  · rw [Real.norm_of_nonneg (sum_nonneg fun i _ => sq_nonneg _), Pi.add_apply, mul_sum, mul_sum,
      ← sum_add_distrib]
    exact sum_le_sum fun i _ => by nlinarith [sq_nonneg (s k y i + score (fwdDensity μ t k) y i)]

/-- **Discharging `hsint` for a bounded learned score.** Let `μ` be a probability law, `t 0 = 0`,
`t` strictly increasing, and `s_k` measurable learned scores with `∑ᵢ s_k(y)ᵢ² ≤ B` for all `k`
and `y` (for example a network output clipped coordinatewise). Then hypothesis `hsint` of the
headline theorems holds for every `N` (`integrable_score_err_of_integrable_sq`). -/
theorem integrable_score_err_of_bounded (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hs : ∀ k, Measurable (s k)) {B : ℝ} (hB : ∀ k y, ∑ i, s k y i ^ 2 ≤ B) (N : ℕ) :
    ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k) :=
  integrable_score_err_of_integrable_sq μ h0 ht hs fun k _ =>
    Integrable.of_bound ((Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hs k)).pow_const 2).aestronglyMeasurable) B
      (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (sum_nonneg fun i _ => sq_nonneg _)]
        exact hB k y)

/-- The exact score has zero score-error term: `scoreErr μ t (exactScore μ t) N = 0`. -/
theorem scoreErr_exactScore {d : ℕ} (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (N : ℕ) :
    scoreErr μ t (exactScore μ t) N = 0 := by
  simp [scoreErr, scoreErrW, exactScore]

/-- The bracket of `initBound_geomGrid` is nonnegative:
`(d (v - 1 - log v) + M / (1 + u_1)) / 2 ≥ 0` for `v = u_1 / (1 + u_1)`, `u_1 > 0`, `M ≥ 0`. -/
theorem initConst_nonneg (d : ℕ) {u1 M : ℝ} (hu1 : 0 < u1) (hM : 0 ≤ M) :
    0 ≤ (d * (u1 / (1 + u1) - 1 - Real.log (u1 / (1 + u1))) + M / (1 + u1)) / 2 := by
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < u1 / (1 + u1))
  have : 0 ≤ (d : ℝ) * (u1 / (1 + u1) - 1 - Real.log (u1 / (1 + u1))) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  positivity

/-- **KL goes to zero (exact score).** For a probability law `μ` with finite second moment, the
exact score, `u_1 > 0` and `ε > 0`, there are `r > 1` and `N ≥ 1` such that on the geometric grid
`geomGrid u_1 r` the DDPM output satisfies `KL(p_1 ‖ q_1) ≤ ε` (`p_1` the forward law at
`t_1 = log(1 + u_1) / 2`). Obtained from `klDiv_output_le_geomGrid`. -/
theorem exists_klDiv_output_le {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {u1 : ℝ} (hu1 : 0 < u1) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      klDiv (fwdLaw μ (geomGrid u1 r) 1) (algLaw (ddpmVar (geomGrid u1 r))
        (scoreMean (geomGrid u1 r) (exactScore μ (geomGrid u1 r)))
        (measurable_scoreMean _ (measurable_exactScore μ _)) N 1) ≤ ENNReal.ofReal ε := by
  obtain ⟨r, hr, N, hN, hle⟩ := exists_geomGrid_params d hu1
    (initConst_nonneg d hu1 (integral_nonneg fun x => sum_nonneg fun i _ => sq_nonneg (x i))
      (M := ∫ x, ∑ i, x i ^ 2 ∂μ)) hε
  refine ⟨r, hr, N, hN, ?_⟩
  refine (klDiv_output_le_geomGrid μ hμ hu1 hr hN _ (measurable_exactScore μ _)
    (integrable_exactScore_err μ _ N)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [scoreErr_exactScore, add_zero, initBound_geomGrid μ hu1 (zero_lt_one.trans hr) hN]
  exact hle

/-- **TV goes to zero (exact score).** Under the hypotheses of `exists_klDiv_output_le`, there
are `r > 1`, `N ≥ 1` with `TV(p_1, q_1) ≤ ε`. Obtained from `tvSup_output_le_geomGrid`. -/
theorem exists_tvSup_output_le {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {u1 : ℝ} (hu1 : 0 < u1) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1) (algLaw (ddpmVar (geomGrid u1 r))
        (scoreMean (geomGrid u1 r) (exactScore μ (geomGrid u1 r)))
        (measurable_scoreMean _ (measurable_exactScore μ _)) N 1) ≤ ε := by
  obtain ⟨r, hr, N, hN, hle⟩ := exists_geomGrid_params d hu1
    (initConst_nonneg d hu1 (integral_nonneg fun x => sum_nonneg fun i _ => sq_nonneg (x i))
      (M := ∫ x, ∑ i, x i ^ 2 ∂μ)) (by positivity : 0 < 2 * ε ^ 2)
  refine ⟨r, hr, N, hN, ?_⟩
  refine (tvSup_output_le_geomGrid μ hμ hu1 hr hN _ (measurable_exactScore μ _)
    (integrable_exactScore_err μ _ N)).trans ?_
  rw [scoreErr_exactScore, add_zero, initBound_geomGrid μ hu1 (zero_lt_one.trans hr) hN]
  refine Real.sqrt_le_iff.2 ⟨hε.le, ?_⟩
  linarith

end FormalizeSampling.DiffusionDiscretization
