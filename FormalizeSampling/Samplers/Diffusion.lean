module

public import FormalizeSampling.Samplers.DiffusionKL
public import FormalizeSampling.Samplers.DiffusionPosterior
public import FormalizeSampling.Samplers.DiffusionPath
public import FormalizeSampling.Foundations.Pinsker

/-!
# Convergence of diffusion models (DDPM-type samplers): the KL error decomposition

Setting (`Samplers/DiffusionSetup.lean`): data law `μ` on `Fin d → ℝ` (a probability measure
with a finite second moment, **no density assumed**), a time grid `t : ℕ → ℝ`, forward OU
steps `F_k(x) = N(α_k x, β_k I)` (`α_k = e^{-(t_k - t_{k-1})}`, `β_k = 1 - α_k²`), forward
marginals `p_k` (`p_0 = μ`, `p_k = F_k ∘ p_{k-1}`), exact reverse kernels
`R_k = F_k†p_{k-1}` (Bayes posterior) with means `m*_k`, and the algorithm
`q_N = N(0, I)`, `q_{k-1} = Q_k ∘ q_k` with `Q_k(y) = N(m_k(y), σ_k² I)` for arbitrary
measurable mean maps `m_k` and variances `σ_k² > 0`. The sampler outputs `q_1`; the target is
`p_1`, the data law smoothed up to the early-stopping time `δ = t_1` (`t_0` is the time origin).

All divergences are Mathlib's `klDiv` (`KL(first ‖ second)`, valued in `ℝ≥0∞`); the per-step
errors are averaged under the **true** marginals `p_k`. Squared Euclidean norms are coordinate
sums.

The decompositions are exact on path space: the KL between the law of the true reverse path
`(x_N, …, x_1)` and the sampler's path law is the initialisation error plus the averaged
per-step kernel errors (`DiffusionPath.klDiv_truePath_algPath`, `Samplers/DiffusionPath.lean`).
The output bounds follow by data processing for the last coordinate
(`DiffusionPath.klDiv_output_le_path`).

## Main results

* `lintegral_klDiv_revKernel_eq`: for each step, the averaged kernel error splits exactly as
  `∫ KL(R_k y ‖ N(m_k y, σ²I)) dp_k = ∫ KL(R_k y ‖ N(m*_k y, σ²I)) dp_k
  + ∫ ∑ᵢ (m*_k(y)ᵢ - m_k(y)ᵢ)² / (2σ²) dp_k` (Gaussian mean-shift identity, `DiffusionKL`).
* **Path decompositions** (equalities in `ℝ≥0∞`):
  `DiffusionPath.klDiv_truePath_eq_disc_add_meanErr` (`KL(truePath ‖ algPath)` is the sum of
  the three terms of `klDiv_output_le` below), `DiffusionPath.klDiv_truePath_eq_score` (score
  form) and `DiffusionPath.klDiv_truePath_eq_ddpm` (`σ² = β/α²`).
* `klDiv_output_le_chain`: `KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ Q_k y) dp_k`.
* **Headline** `klDiv_output_le`:
  `KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k y, σ_k² I)) dp_k(y)
                  + ∑_{k=2}^N ∫ ∑ᵢ (m*_k(y)ᵢ - m_k(y)ᵢ)² / (2σ_k²) dp_k(y)`.
* (a) **Score form** `klDiv_output_le_score`: for `m_k = α_k⁻¹(y + β_k s_k(y))` with learned
  scores `s_k` and an increasing grid, the last sum equals
  `∑_{k=2}^N β_k² / (2 α_k² σ_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`, where `p_k(y)` is the
  Lebesgue density `fwdDensity μ t k` of the marginal (Tweedie's formula,
  `Diffusion.postMean_ae_eq_tweedie`, `lintegral_meanError_eq_scoreError`). With the
  DDPM variance `σ_k² = β_k / α_k²` the weight becomes `β_k / 2` (`klDiv_output_le_ddpm`).
* (b) **Initialisation**: `klDiv_fwdLaw_one_le` (`KL(p_1 ‖ N(0,I)) ≤ ∫ KL(F_1 x ‖ N(0,I)) dμ =
  (d (β_1 - 1 - log β_1) + α_1² ∫ ∑ᵢ xᵢ² dμ) / 2`), `toReal_klDiv_fwdLaw_le` (OU decay
  `KL(p_N ‖ N(0,I)) ≤ e^{-2(t_N - t_1)} KL(p_1 ‖ N(0,I))`), combined in
  `klDiv_fwdLaw_le_init`; the fully explicit bound `klDiv_output_le_explicit`.
* (c) **TV corollary** `tvSup_output_le` (Pinsker).
* Non-vacuity: `fwdLaw_stdGaussian`, `fwdDensity_stdGaussian`, `score_fwdDensity_stdGaussian`,
  `scoreError_stdGaussian_eq_zero` (for Gaussian data `μ = N(0, I)`, all marginals are `N(0,I)`,
  the true score is `-y`, the learned score `s_k(y) = -y` has zero score error and the
  initialisation term vanishes).

## Not proved here

* A bound on the discretisation term `∑_k ∫ KL(R_k y ‖ N(m*_k y, σ_k² I)) dp_k` (it is finite
  only if each posterior has a density, and its size is bounded in
  `Samplers/DiffusionDiscretization*.lean`).
* Score-estimation guarantees (the score error is an explicit input quantity here).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.Diffusion

open FormalizeSampling.OULangevinDecayPi

variable {d : ℕ}

/-! ### Exact split of each step's error -/

/-- **Per-step error split (bias–variance form).** If `μ` has a finite second moment and
`σ² ≠ 0`, then for every measurable mean map `m'` and every step `k + 1`,
`∫ KL(R_{k+1} y ‖ N(m'(y), σ² I)) dp_{k+1} = ∫ KL(R_{k+1} y ‖ N(m*_{k+1}(y), σ² I)) dp_{k+1}
 + ∫ ∑ᵢ (m*_{k+1}(y)ᵢ - m'(y)ᵢ)² / (2σ²) dp_{k+1}`, an identity in `ℝ≥0∞`. -/
theorem lintegral_klDiv_revKernel_eq (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (t : ℕ → ℝ) (k : ℕ) {v : ℝ≥0} (hv : v ≠ 0)
    {m' : (Fin d → ℝ) → Fin d → ℝ} (hm' : Measurable m') :
    ∫⁻ y, klDiv (revKernel μ t (k + 1) y) (gaussKernelPi v m' hm' y) ∂(fwdLaw μ t (k + 1)) =
      ∫⁻ y, klDiv (revKernel μ t (k + 1) y)
          (Measure.pi fun i => gaussianReal (postMean μ t (k + 1) y i) v) ∂(fwdLaw μ t (k + 1)) +
        ∫⁻ y, ENNReal.ofReal ((∑ i, (postMean μ t (k + 1) y i - m' y i) ^ 2) / (2 * v))
          ∂(fwdLaw μ t (k + 1)) := by
  rw [← lintegral_add_right]
  · refine lintegral_congr_ae ?_
    filter_upwards [ae_integrable_revKernel μ hμ t k] with y hy
    rw [gaussKernelPi_apply]
    exact klDiv_pi_gaussianReal_eq_add _ hy (m' y) hv
  · refine ENNReal.measurable_ofReal.comp (Measurable.div_const ?_ _)
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((measurable_pi_apply i).comp (measurable_postMean μ t (k + 1))).sub
      ((measurable_pi_apply i).comp hm')).pow_const 2

/-- `∑_{k ∈ (1, N]} f k = ∑_{k ∈ (1, N]} g k` if `f (j + 1) = g (j + 1)` whenever
`j + 1 ∈ (1, N]`. -/
private theorem sum_Ioc_congr_succ {M : Type*} [AddCommMonoid M] {N : ℕ} {f g : ℕ → M}
    (h : ∀ j, j + 1 ∈ Ioc 1 N → f (j + 1) = g (j + 1)) :
    ∑ k ∈ Ioc 1 N, f k = ∑ k ∈ Ioc 1 N, g k := by
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
  exact h j hk

/-! ### (a) Score form via Tweedie's formula -/

/-- **Score error under the true marginals.** For an increasing grid (`t_j < t_{j+1}`), the
score-parametrised mean `m_{j+1} = α⁻¹(y + β s_{j+1}(y))` and any `σ² ≠ 0`,
`∫ ∑ᵢ (m*_{j+1}(y)ᵢ - m_{j+1}(y)ᵢ)² / (2σ²) dp_{j+1}
 = β² / (2α²σ²) · ∫ ∑ᵢ (s_{j+1}(y)ᵢ - ∂ᵢ log p_{j+1}(y))² dp_{j+1}`. -/
theorem lintegral_meanError_eq_scoreError (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} {j : ℕ} (hj : t j < t (j + 1)) (v : ℝ≥0)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) :
    ∫⁻ y, ENNReal.ofReal
        ((∑ i, (postMean μ t (j + 1) y i - scoreMean t s (j + 1) y i) ^ 2) / (2 * v))
        ∂(fwdLaw μ t (j + 1)) =
      ENNReal.ofReal (fwdVar t (j + 1) ^ 2 / (2 * fwdScale t (j + 1) ^ 2 * v)) *
        ∫⁻ y, ENNReal.ofReal (∑ i, (s (j + 1) y i - score (fwdDensity μ t (j + 1)) y i) ^ 2)
          ∂(fwdLaw μ t (j + 1)) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [postMean_ae_eq_tweedie μ hj] with y hy
  have hα := fwdScale_pos t (j + 1)
  rw [hy, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [scoreMean]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (v : ℝ) 0 with hv | hv
  · simp [hv]
  field_simp
  ring

/-- `β_k > 0` for `k ≥ 1` on a strictly increasing grid. -/
theorem fwdVar_pos_of_strictMono {t : ℕ → ℝ} (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    0 < fwdVar t k :=
  fwdVar_pos (ht (by omega))

end FormalizeSampling.Diffusion

namespace FormalizeSampling.DiffusionPath

open FormalizeSampling.Diffusion

variable {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]

/-! ### Exact decompositions of the path KL -/

/-- **Exact path-KL decomposition (bias–variance form).** For data with finite second moment,
any grid `t`, variances `σ_k² ≠ 0` (`2 ≤ k ≤ N`) and measurable mean maps `m_k`:
`KL(truePath ‖ algPath) = KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), σ_k² I)) dp_k
  + ∑_{k=2}^N ∫ ∑ᵢ (m*_k(y)ᵢ - m_k(y)ᵢ)² / (2σ_k²) dp_k`, an identity in `ℝ≥0∞`. -/
theorem klDiv_truePath_eq_disc_add_meanErr (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (t : ℕ → ℝ) {N : ℕ} (σ2 : ℕ → ℝ≥0) (hσ2 : ∀ k ∈ Ioc 1 N, σ2 k ≠ 0)
    (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hm : ∀ k, Measurable (m k)) :
    klDiv (truePath μ t N (N - 1)) (algPath σ2 m hm N (N - 1)) =
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, ENNReal.ofReal
          ((∑ i, (postMean μ t k y i - m k y i) ^ 2) / (2 * σ2 k)) ∂(fwdLaw μ t k) := by
  rw [klDiv_truePath_algPath, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact sum_Ioc_congr_succ fun j hj =>
    lintegral_klDiv_revKernel_eq μ hμ t j (hσ2 (j + 1) hj) (hm (j + 1))

/-- **Exact path-KL decomposition, score form.** For data with finite second moment, a strictly
increasing grid, variances `σ_k² ≠ 0` and measurable learned scores `s_k`, with
`m_k(y) = α_k⁻¹ (y + β_k s_k(y))`:
`KL(truePath ‖ algPath) = KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), σ_k² I)) dp_k
  + ∑_{k=2}^N β_k²/(2α_k²σ_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`
(`p_k(y) = fwdDensity μ t k y`), an identity in `ℝ≥0∞`. -/
theorem klDiv_truePath_eq_score (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ}
    (ht : StrictMono t) {N : ℕ} (σ2 : ℕ → ℝ≥0) (hσ2 : ∀ k ∈ Ioc 1 N, σ2 k ≠ 0)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) :
    klDiv (truePath μ t N (N - 1))
        (algPath σ2 (scoreMean t s) (measurable_scoreMean t hs) N (N - 1)) =
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k ^ 2 / (2 * fwdScale t k ^ 2 * σ2 k)) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) := by
  rw [klDiv_truePath_eq_disc_add_meanErr μ hμ t σ2 hσ2]
  congr 1
  exact sum_Ioc_congr_succ fun j _ =>
    lintegral_meanError_eq_scoreError μ (ht (Nat.lt_succ_self j)) (σ2 (j + 1)) s

/-- **Exact path-KL decomposition for `σ² = β/α²`.** For data with finite second moment, a
strictly increasing grid and measurable learned scores `s_k`, with
`m_k(y) = α_k⁻¹ (y + β_k s_k(y))` and the DDPM variance `σ_k² = β_k/α_k²` (`ddpmVar`):
`KL(truePath ‖ algPath) = KL(p_N ‖ N(0,I))
  + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k
  + ∑_{k=2}^N (β_k/2) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`, an identity in `ℝ≥0∞`. -/
theorem klDiv_truePath_eq_ddpm (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ}
    (ht : StrictMono t) {N : ℕ} (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) :
    klDiv (truePath μ t N (N - 1))
        (algPath (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N (N - 1)) =
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / 2) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) := by
  rw [klDiv_truePath_eq_score μ hμ ht (ddpmVar t)
    (fun k hk => ddpmVar_ne_zero ht (by simp only [mem_Ioc] at hk; omega)) s hs]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [mem_Ioc] at hk
  have hβ := fwdVar_pos_of_strictMono ht (k := k) (by omega)
  have hα := (fwdScale_pos t k).ne'
  rw [ddpmVar, Real.coe_toNNReal _ (div_pos hβ (pow_pos (fwdScale_pos t k) 2)).le]
  congr 2
  field_simp

end FormalizeSampling.DiffusionPath

namespace FormalizeSampling.Diffusion

open FormalizeSampling.OULangevinDecayPi FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-! ### Output KL: data processing from the path KL -/

/-- **KL chain rule along the reverse process.** For a probability data law `μ`, any time grid
`t`, any variances `σ2` and measurable mean maps `m k`, and `N ≥ 1`:
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫⁻ KL(R_k y ‖ Q_k y) dp_k(y)`,
where `R_k` is the exact reverse kernel and `Q_k` the algorithm's kernel. No moment, density or
grid assumption. -/
theorem klDiv_output_le_chain (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hm : ∀ k, Measurable (m k))
    {N : ℕ} (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t 1) (algLaw σ2 m hm N 1) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y) (algKernel σ2 m hm k y)
          ∂(fwdLaw μ t k) :=
  (klDiv_output_le_path μ t σ2 m hm hN).trans_eq (klDiv_truePath_algPath μ t σ2 m hm N)

/-- **Headline: KL error decomposition of a Gaussian reverse sampler.** Let `μ` be a probability
measure on `Fin d → ℝ` with `∫ ∑ᵢ xᵢ² dμ < ∞` (no density assumed), `t` any time grid,
`σ_k² ≠ 0`, `m_k` measurable mean maps and `N ≥ 1`. Then
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I))`
`  + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), σ_k² I)) dp_k(y)`   (discretisation)
`  + ∑_{k=2}^N ∫ ∑ᵢ (m*_k(y)ᵢ - m_k(y)ᵢ)² / (2σ_k²) dp_k(y)`   (mean / score error),
where `p_k = fwdLaw μ t k`, `q_1 = algLaw σ2 m hm N 1` is the sampler output, `R_k = revKernel`
and `m*_k = postMean` (the posterior mean `E[x_{k-1} | x_k = y]`). All terms are in `ℝ≥0∞`. -/
theorem klDiv_output_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (t : ℕ → ℝ) {N : ℕ} (σ2 : ℕ → ℝ≥0)
    (hσ2 : ∀ k ∈ Ioc 1 N, σ2 k ≠ 0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hm : ∀ k, Measurable (m k))
    (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t 1) (algLaw σ2 m hm N 1) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, ENNReal.ofReal
          ((∑ i, (postMean μ t k y i - m k y i) ^ 2) / (2 * σ2 k)) ∂(fwdLaw μ t k) :=
  (klDiv_output_le_path μ t σ2 m hm hN).trans_eq
    (klDiv_truePath_eq_disc_add_meanErr μ hμ t σ2 hσ2 m hm)

/-- **(a) Headline in score form.** Under the hypotheses of `klDiv_output_le`, with a strictly
increasing time grid and the score parametrisation `m_k(y) = α_k⁻¹ (y + β_k s_k(y))` for
measurable learned scores `s_k`:
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), σ_k² I)) dp_k(y)
  + ∑_{k=2}^N β_k² / (2 α_k² σ_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`,
with `p_k(y) = fwdDensity μ t k y` the (everywhere positive, `fwdLaw_eq_withDensity`) Lebesgue
density of the marginal and `∂ᵢ log p_k = score (fwdDensity μ t k)`. -/
theorem klDiv_output_le_score (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : StrictMono t)
    {N : ℕ} (σ2 : ℕ → ℝ≥0) (hσ2 : ∀ k ∈ Ioc 1 N, σ2 k ≠ 0) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hs : ∀ k, Measurable (s k)) (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t 1) (algLaw σ2 (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k ^ 2 / (2 * fwdScale t k ^ 2 * σ2 k)) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) :=
  (klDiv_output_le_path μ t _ _ _ hN).trans_eq (klDiv_truePath_eq_score μ hμ ht σ2 hσ2 s hs)

/-- **(a') DDPM variance.** With the DDPM reverse variance `σ_k² = β_k / α_k²` (`ddpmVar`), the
score-error weight `β_k² / (2 α_k² σ_k²)` of `klDiv_output_le_score` equals `β_k / 2`:
for a strictly increasing grid, measurable learned scores `s_k` and `N ≥ 1`,
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k(y)
  + ∑_{k=2}^N (β_k / 2) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`. -/
theorem klDiv_output_le_ddpm (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : StrictMono t)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) {N : ℕ} (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t 1) (algLaw (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / 2) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) :=
  (klDiv_output_le_path μ t _ _ _ hN).trans_eq (klDiv_truePath_eq_ddpm μ hμ ht s hs)

/-! ### (b) Initialisation error -/

/-- `KL(N(α x, β I) ‖ N(0, I)) = ∑ᵢ (β + (α xᵢ)² - 1 - log β) / 2` for `β > 0`. -/
theorem klDiv_fwdKernel_stdGaussianPi {t : ℕ → ℝ} {k : ℕ} (hk : t (k - 1) < t k)
    (x : Fin d → ℝ) :
    klDiv (fwdKernel t k x) (stdGaussianPi d) = ENNReal.ofReal
      (∑ i, (fwdVar t k + (fwdScale t k * x i) ^ 2 - 1 - Real.log (fwdVar t k)) / 2) := by
  have hβ := fwdVar_pos hk
  have hβ' : (fwdVar t k).toNNReal ≠ 0 := by simpa using hβ
  rw [fwdKernel_apply, stdGaussianPi, GaussianIncrement.klDiv_pi_pi,
    ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian _ hβ', Real.coe_toNNReal _ hβ.le]
  · intro i _
    have := Real.log_le_sub_one_of_pos hβ
    have := sq_nonneg (fwdScale t k * x i)
    linarith

/-- **(b1) KL of the smoothed data to `N(0, I)` (convexity).** If `t_0 < t_1` and
`∫ ∑ᵢ xᵢ² dμ < ∞`, then
`KL(p_1 ‖ N(0,I)) ≤ ∫ KL(N(α_1 x, β_1 I) ‖ N(0,I)) dμ(x)
 = (d (β_1 - 1 - log β_1) + α_1² ∫ ∑ᵢ xᵢ² dμ) / 2`. No density of `μ` is needed. -/
theorem klDiv_fwdLaw_one_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : t 0 < t 1) :
    klDiv (fwdLaw μ t 1) (stdGaussianPi d) ≤ ENNReal.ofReal
      ((d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
        fwdScale t 1 ^ 2 * ∫ x, ∑ i, x i ^ 2 ∂μ) / 2) := by
  have hk : t (1 - 1) < t 1 := ht
  have hpt : ∀ x : Fin d → ℝ, (∑ i, (fwdVar t 1 + (fwdScale t 1 * x i) ^ 2 - 1 -
      Real.log (fwdVar t 1)) / 2) = (d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
        fwdScale t 1 ^ 2 * ∑ i, x i ^ 2) / 2 := fun x => by
    rw [← Finset.sum_div, Finset.mul_sum]
    congr 1
    rw [show (d : ℝ) * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) =
      ∑ _i : Fin d, (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) by simp; ring,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin d → ℝ => (d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
      fwdScale t 1 ^ 2 * ∑ i, x i ^ 2) / 2) μ :=
    ((integrable_const _).add (hμ.const_mul _)).div_const _
  have hnn : 0 ≤ᵐ[μ] fun x : Fin d → ℝ => (d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
      fwdScale t 1 ^ 2 * ∑ i, x i ^ 2) / 2 := ae_of_all _ fun x => by
    simp only [Pi.zero_apply]
    rw [← hpt x]
    refine Finset.sum_nonneg fun i _ => div_nonneg ?_ zero_le_two
    have := Real.log_le_sub_one_of_pos (fwdVar_pos hk)
    have := sq_nonneg (fwdScale t 1 * x i)
    linarith
  calc klDiv (fwdLaw μ t 1) (stdGaussianPi d)
      = klDiv (fwdKernel t 1 ∘ₘ μ) ((Kernel.const (Fin d → ℝ) (stdGaussianPi d)) ∘ₘ μ) := by
        rw [Measure.const_comp, measure_univ, one_smul]; rfl
    _ ≤ klDiv (μ ⊗ₘ fwdKernel t 1) (μ ⊗ₘ Kernel.const (Fin d → ℝ) (stdGaussianPi d)) :=
        KL.klDiv_comp_le_compProd _ _ _ _
    _ = ∫⁻ x, klDiv (fwdKernel t 1 x) (stdGaussianPi d) ∂μ := by
        rw [KL.klDiv_compProd_right_eq_lintegral]
        rfl
    _ = ∫⁻ x, ENNReal.ofReal ((d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
          fwdScale t 1 ^ 2 * ∑ i, x i ^ 2) / 2) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [klDiv_fwdKernel_stdGaussianPi hk, hpt]
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_div, integral_add
          (integrable_const _) (hμ.const_mul _), integral_const_mul (fwdScale t 1 ^ 2),
          integral_const]
        simp

/-- **(b2) OU decay of the initialisation error.** For a monotone grid, `N ≥ 1`, a data law with
finite second moment and `KL(p_1 ‖ N(0,I)) < ∞`: `KL(p_N ‖ N(0,I)) < ∞` and
`KL(p_N ‖ N(0,I)) ≤ e^{-2(t_N - t_1)} KL(p_1 ‖ N(0,I))` (as real numbers). -/
theorem toReal_klDiv_fwdLaw_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : Monotone t)
    (h1 : klDiv (fwdLaw μ t 1) (stdGaussianPi d) ≠ ∞) {N : ℕ} (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t N) (stdGaussianPi d) ≠ ∞ ∧
      (klDiv (fwdLaw μ t N) (stdGaussianPi d)).toReal ≤
        Real.exp (-2 * (t N - t 1)) * (klDiv (fwdLaw μ t 1) (stdGaussianPi d)).toReal := by
  induction N, hN using Nat.le_induction with
  | base => simp [h1]
  | succ n hn ih =>
    have h := toReal_klDiv_ouKernelPi_comp_le (a := 1) zero_le_one
      (sub_nonneg.2 (ht (Nat.le_succ n))) (fwdLaw μ t n) ih.1
      (integrable_sum_sq_fwdLaw μ hμ t n)
    refine ⟨h.1, h.2.trans ?_⟩
    calc Real.exp (-2 * 1 * (t (n + 1) - t n)) *
          (klDiv (fwdLaw μ t n) (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal
        ≤ Real.exp (-2 * 1 * (t (n + 1) - t n)) *
          (Real.exp (-2 * (t n - t 1)) * (klDiv (fwdLaw μ t 1) (stdGaussianPi d)).toReal) :=
          mul_le_mul_of_nonneg_left ih.2 (Real.exp_pos _).le
      _ = _ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- **(b) Explicit initialisation bound.** For a strictly increasing grid, `N ≥ 1` and a data law
with finite second moment:
`KL(p_N ‖ N(0,I)) ≤ e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² ∫ ∑ᵢ xᵢ² dμ) / 2`. -/
theorem klDiv_fwdLaw_le_init (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : StrictMono t) {N : ℕ}
    (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t N) (stdGaussianPi d) ≤ ENNReal.ofReal (Real.exp (-2 * (t N - t 1)) *
      ((d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
        fwdScale t 1 ^ 2 * ∫ x, ∑ i, x i ^ 2 ∂μ) / 2)) := by
  have hb1 := klDiv_fwdLaw_one_le μ hμ (ht zero_lt_one)
  have h1 : klDiv (fwdLaw μ t 1) (stdGaussianPi d) ≠ ∞ := ne_top_of_le_ne_top
    ENNReal.ofReal_ne_top hb1
  obtain ⟨hfin, hdec⟩ := toReal_klDiv_fwdLaw_le μ hμ ht.monotone h1 hN
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal (hdec.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le))
  refine ENNReal.toReal_le_of_le_ofReal ?_ hb1
  have : 0 ≤ ∫ x, ∑ i, x i ^ 2 ∂μ := integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
    sq_nonneg _
  have := Real.log_le_sub_one_of_pos (fwdVar_pos (t := t) (k := 1) (ht zero_lt_one))
  have : 0 ≤ (d : ℝ) * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  positivity

/-- **Fully explicit KL bound (score form + initialisation).** Under the hypotheses of
`klDiv_output_le_score`:
`KL(p_1 ‖ q_1) ≤ e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² ∫ ∑ᵢ xᵢ² dμ) / 2
  + ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), σ_k² I)) dp_k(y)
  + ∑_{k=2}^N β_k² / (2 α_k² σ_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`. -/
theorem klDiv_output_le_explicit (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (ht : StrictMono t)
    {N : ℕ} (σ2 : ℕ → ℝ≥0) (hσ2 : ∀ k ∈ Ioc 1 N, σ2 k ≠ 0) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hs : ∀ k, Measurable (s k)) (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t 1) (algLaw σ2 (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      ENNReal.ofReal (Real.exp (-2 * (t N - t 1)) *
          ((d * (fwdVar t 1 - 1 - Real.log (fwdVar t 1)) +
            fwdScale t 1 ^ 2 * ∫ x, ∑ i, x i ^ 2 ∂μ) / 2)) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k ^ 2 / (2 * fwdScale t k ^ 2 * σ2 k)) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) := by
  refine (klDiv_output_le_score μ hμ ht σ2 hσ2 s hs hN).trans ?_
  gcongr
  exact klDiv_fwdLaw_le_init μ hμ ht hN

/-! ### (c) Total variation -/

/-- **(c) TV bound (Pinsker).** Under the hypotheses of `klDiv_output_le`, if the right-hand side
`B` of the decomposition is finite, then `TV(p_1, q_1) ≤ √(B / 2)`. -/
theorem tvSup_output_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (t : ℕ → ℝ) {N : ℕ} (σ2 : ℕ → ℝ≥0)
    (hσ2 : ∀ k ∈ Ioc 1 N, σ2 k ≠ 0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hm : ∀ k, Measurable (m k))
    (hN : 1 ≤ N)
    (hB : klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, ENNReal.ofReal
          ((∑ i, (postMean μ t k y i - m k y i) ^ 2) / (2 * σ2 k)) ∂(fwdLaw μ t k) ≠ ∞) :
    TotalVariation.tvSup (fwdLaw μ t 1) (algLaw σ2 m hm N 1) ≤
      Real.sqrt ((klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
          (Measure.pi fun i => gaussianReal (postMean μ t k y i) (σ2 k)) ∂(fwdLaw μ t k) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, ENNReal.ofReal
          ((∑ i, (postMean μ t k y i - m k y i) ^ 2) / (2 * σ2 k)) ∂(fwdLaw μ t k)).toReal
          / 2) := by
  have h := klDiv_output_le μ hμ t σ2 hσ2 m hm hN
  refine (Pinsker.tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top hB h)).trans ?_
  gcongr

/-! ### Non-vacuity: Gaussian data -/

/-- For Gaussian data `μ = N(0, I)` and a monotone grid, every forward marginal is `N(0, I)`. -/
theorem fwdLaw_stdGaussian {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ) :
    fwdLaw (stdGaussianPi d) t k = stdGaussianPi d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fwdLaw_succ, ih, fwdKernel, ouKernelPi_eq_ouKernelVarPi, stdGaussianPi]
    have h := ouKernelVarPi_comp_pi_gaussianReal (d := d) zero_le_one zero_le_one
      (sub_nonneg.2 (ht (Nat.le_succ k))) 0
    simp only [Pi.zero_apply, mul_zero, Real.toNNReal_one] at h
    exact h

/-- For Gaussian data and an increasing grid, the density of every marginal `p_{k+1}` is the
standard Gaussian density, everywhere. -/
theorem fwdDensity_stdGaussian {t : ℕ → ℝ} (ht : StrictMono t) (k : ℕ) :
    fwdDensity (stdGaussianPi d) t (k + 1) = NoiseScorePreconditioned.gaussDensity 0 := by
  have hk : t k < t (k + 1) := ht (Nat.lt_succ_self k)
  have h0 := fwdLaw_eq_withDensity (stdGaussianPi d) hk
  rw [fwdLaw_stdGaussian ht.monotone] at h0
  have hγ : stdGaussianPi d = volume.withDensity fun x =>
      ENNReal.ofReal (NoiseScorePreconditioned.gaussDensity (d := d) 0 x) :=
    NoiseScorePreconditioned.pi_gaussianReal_one_eq_withDensity 0
  have h1 := hγ.symm.trans h0
  have hcont1 : Continuous (fwdDensity (stdGaussianPi d) t (k + 1)) := by
    unfold fwdDensity OUPosterior.piAffineDensity
    refine continuous_of_dominated (bound := fun _ => ∏ _i : Fin d,
      (Real.sqrt (2 * Real.pi * Real.sqrt (fwdVar t (k + 1)) ^ 2))⁻¹)
      (fun y => ((Tweedie.continuous_piGaussKernel_left _ y).comp
        (continuous_const_smul _)).aestronglyMeasurable)
      (fun y => ae_of_all _ fun x => ?_) (integrable_const _)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_of_nonneg (Tweedie.piGaussKernel_nonneg _ _ _)]
      exact Tweedie.piGaussKernel_le _ _ _
    · have h := (Tweedie.continuous_piGaussKernel_uncurry (d := d)
        (Real.sqrt (fwdVar t (k + 1)))).comp
        (continuous_const.prodMk continuous_id : Continuous fun y : Fin d → ℝ =>
          (fwdScale t (k + 1) • x, y))
      exact h
  have hcont2 : Continuous (NoiseScorePreconditioned.gaussDensity (d := d) 0) :=
    (NoiseScorePreconditioned.contDiff_gaussDensity 0).continuous
  have hae : fwdDensity (stdGaussianPi d) t (k + 1) =ᵐ[volume]
      NoiseScorePreconditioned.gaussDensity 0 := by
    have h2 := (withDensity_eq_iff_of_sigmaFinite
      (ENNReal.measurable_ofReal.comp hcont2.measurable).aemeasurable
      (ENNReal.measurable_ofReal.comp hcont1.measurable).aemeasurable).1 h1
    filter_upwards [h2] with y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (fwdDensity_pos _ hk y).le
      (NoiseScorePreconditioned.gaussDensity_pos 0 y).le).1 hy.symm
  exact (Continuous.ae_eq_iff_eq volume hcont1 hcont2).1 hae

/-- For Gaussian data and an increasing grid, the true score of every marginal `p_{k+1}` is
`∇ log p_{k+1}(y) = -y`. -/
theorem score_fwdDensity_stdGaussian {t : ℕ → ℝ} (ht : StrictMono t) (k : ℕ)
    (y : Fin d → ℝ) : score (fwdDensity (stdGaussianPi d) t (k + 1)) y = -y := by
  rw [fwdDensity_stdGaussian ht, NoiseScorePreconditioned.score_gaussDensity, add_zero]

/-- **Non-vacuity of the score-form bound.** For Gaussian data `μ = N(0, I)` (which satisfies
all hypotheses of `klDiv_output_le_score`), an increasing grid and the exact learned score
`s_k(y) = -y`, the initialisation term `KL(p_N ‖ N(0,I))` and every score-error term vanish. -/
theorem scoreError_stdGaussian_eq_zero {t : ℕ → ℝ} (ht : StrictMono t) (N : ℕ) :
    klDiv (fwdLaw (stdGaussianPi d) t N) (stdGaussianPi d) = 0 ∧
      ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k ^ 2 / (2 * fwdScale t k ^ 2 * 1)) *
        ∫⁻ y, ENNReal.ofReal (∑ i, ((-y) i - score (fwdDensity (stdGaussianPi d) t k) y i) ^ 2)
          ∂(fwdLaw (stdGaussianPi d) t k) = 0 := by
  refine ⟨by rw [fwdLaw_stdGaussian ht.monotone]; exact klDiv_self _, ?_⟩
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
  simp [score_fwdDensity_stdGaussian ht]

end FormalizeSampling.Diffusion
