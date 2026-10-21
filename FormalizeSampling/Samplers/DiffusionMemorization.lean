module

public import FormalizeSampling.Samplers.DiffusionMain
public import FormalizeSampling.Flow.FokkerPlanckExistenceTight

/-!
# Memorisation: exact empirical scores concentrate near training data as terminal noise vanishes

Status: **Verified.** Let `x_1, …, x_n ∈ ℝ^d` be a training set and
`μ_n = (1/n) ∑ᵢ δ_{x_i}` its empirical measure (`empirical x`). Run the DDPM sampler of
`Samplers/DiffusionSetup.lean` on the geometric grid `geomGrid u_1 r` with `N` steps and the
**exact** score of the forward marginals of `μ_n` (`DiffusionDiscretization.exactScore`, i.e.
`s_k = ∇ log p_k` with `p_k` the law of the OU chain started at `μ_n`), and call `q_1` its
output law (`exactScoreOutput`). Then the output concentrates on the training points: for every
radius `ρ > 0` and every `ε > 0` there are sampler parameters `(u_1, r, N)` such that
`q_1(⋃ᵢ B(x_i, ρ)) ≥ 1 - ε`, where `B(x, ρ) = {y | |y - x|² < ρ²}` is the open Euclidean ball
(`sqDist x y = ∑ⱼ (y j - x j)²`).

## Interpretation

The denoising-score-matching objective for the training set is minimised by the score of the
forward marginals of the *empirical* measure. The theorem concerns this empirical score:
as the early-stopping time `t_1 = log(1 + u_1) / 2` shrinks, with grid and horizon chosen to
control discretisation and initialisation error, output mass concentrates near the training
points. It does not identify the source of generalisation at fixed positive terminal noise,
nor does it concern an exact population score. A positive terminal noise gives a smoothed
empirical target; how well that target generalises is a separate statistical question.
The statement is for the empirical measure, which is singular
(`empirical_not_ac`), so it also exercises the end-to-end guarantee of
`Samplers/DiffusionMain.lean` far from any density assumption. The phenomenon is known for the
continuous-time sampler: Pidstrigach (2022, arXiv:2206.01018, Cor. 1) shows that a score close
to that of the empirical measure (in an exponentially integrable sense) gives an output supported
on the training data, Li–Chen–Li (2024, arXiv:2401.04856, Thm 4.3) that with early stopping it
returns a Gaussian kernel density estimate of the training set, and Gu et al. (2023,
arXiv:2310.02664) derive the memorisation from the closed-form optimal score; here it is proved
for the discretised DDPM sampler.

## Proof

* `p_1 = (1/n) ∑ᵢ N(α x_i, β I)` with `α = e^{-t_1}`, `β = 1 - α² = u_1 / (1 + u_1)`.
  Markov's inequality on `|y - x_i|²`, whose mean is `(1 - α)² |x_i|² + d β ≤ u_1 (|x_i|² + d)`
  (`lintegral_sqDist_pi`), gives `p_1(|y - x_i| ≥ ρ for all i) ≤ u_1 (∑ᵢ |x_i|² + d) / ρ²`
  (`fwdLaw_one_outside_le`).
* `TV(p_1, q_1) ≤ ε / 2` for suitable `(r, N)` by `DiffusionDiscretization.exists_tvSup_output_le`
  (the geometric-grid guarantee with zero score error); TV is `sup_A |p_1(A) - q_1(A)|`.

## Main results

* `empirical`, `isProbabilityMeasure_empirical`, `integrable_sqNorm_empirical`: the empirical
  measure, a probability measure with finite second moment.
* `empirical_not_ac`: on `Fin (d + 1) → ℝ` the empirical measure has no Lebesgue density.
* `exactScoreOutput`: the output law `q_1` of the exact-score DDPM sampler.
* `fwdKernel_one_geomGrid_far_le`, `fwdLaw_one_outside_le`: Gaussian (Markov) tail bounds for
  the first forward step and for the smoothed empirical law `p_1`.
* `output_concentrates_on_training_set` (headline): `q_1(⋃ᵢ B(x_i, ρ)) ≥ 1 - ε`.
* `output_outside_training_set_le`: `q_1({y | |y - x_i| ≥ ρ ∀ i}) ≤ ε`.
* `output_outside_nhds_le`, `tendsto_output_outside_nhds`: for any set `U` that is a
  neighbourhood of every training point, `q_1(Uᶜ) ≤ ε` for suitable parameters, and along a
  sequence of parameters `q_1(Uᶜ) → 0`.

## Not proved here

* No statement about which training point is copied, or with what weights (the output is close
  in TV to `p_1`, whose weights are exactly `1/n`, but this is not spelled out).
* No rate: the parameters are only shown to exist (the choice of `u_1` is explicit,
  `u_1 = ε ρ² / (2 (∑ᵢ |x_i|² + d + 1))`; `(r, N)` come from `exists_geomGrid_params`).
* Nothing about generalisation with learned or population scores, or at fixed positive
  terminal noise; the result concerns concentration for the exact empirical score.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionMemorization

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
open FormalizeSampling.FokkerPlanckExistence (sqDist measurable_sqDist lintegral_sqDist_pi)

variable {d n : ℕ}

/-! ### The empirical measure -/

/-- The empirical measure of a training set `x : Fin n → (Fin d → ℝ)`:
`μ_n = (1/n) ∑ᵢ δ_{x_i}`. -/
noncomputable def empirical (x : Fin n → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- Evaluation of the empirical measure: `μ_n(s) = (1/n) ∑ᵢ δ_{x_i}(s)`. -/
theorem empirical_apply (x : Fin n → Fin d → ℝ) (s : Set (Fin d → ℝ)) :
    empirical x s = (n : ℝ≥0∞)⁻¹ * ∑ i, Measure.dirac (x i) s := by
  simp [empirical]

/-- The empirical measure of a nonempty training set is a probability measure. -/
instance isProbabilityMeasure_empirical [NeZero n] (x : Fin n → Fin d → ℝ) :
    IsProbabilityMeasure (empirical x) := by
  refine ⟨?_⟩
  rw [empirical_apply]
  simp only [measure_univ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp [NeZero.ne n]) (by simp)

/-- The empirical measure has finite second moment: `y ↦ ∑ⱼ yⱼ²` is `μ_n`-integrable. -/
theorem integrable_sqNorm_empirical [NeZero n] (x : Fin n → Fin d → ℝ) :
    Integrable (fun y : Fin d → ℝ => ∑ j, y j ^ 2) (empirical x) := by
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by simp [NeZero.ne n]))
  exact (integrable_finsetSum_measure).2 fun i _ => integrable_dirac (by simp)

/-- **The empirical measure is singular.** On `Fin (d + 1) → ℝ`, a nonempty empirical measure
has no Lebesgue density: `¬ μ_n ≪ volume` (it charges the Lebesgue-null set `{x_0}`). -/
theorem empirical_not_ac [NeZero n] (x : Fin n → Fin (d + 1) → ℝ) :
    ¬ empirical x ≪ (volume : Measure (Fin (d + 1) → ℝ)) := fun h => by
  have h0 := h (measure_singleton (x 0))
  rw [empirical_apply, mul_eq_zero, sum_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · simp at h0
  · simpa using h0 0 (mem_univ _)

/-! ### The exact-score sampler -/

/-- The output law `q_1` of the DDPM sampler of `Samplers/DiffusionSetup.lean` on the geometric
grid `geomGrid u1 r` with `N` steps, started at `N(0, I)`, with reverse variances `ddpmVar` and
the **exact** score `s_k = ∇ log p_k` of the forward marginals of the data law `μ`
(`DiffusionDiscretization.exactScore`). -/
noncomputable abbrev exactScoreOutput (μ : Measure (Fin d → ℝ)) (u1 r : ℝ) (N : ℕ) :
    Measure (Fin d → ℝ) :=
  algLaw (ddpmVar (geomGrid u1 r)) (scoreMean (geomGrid u1 r) (exactScore μ (geomGrid u1 r)))
    (measurable_scoreMean _ (measurable_exactScore μ _)) N 1

/-! ### Gaussian tails of the first forward step -/

/-- On the geometric grid the first forward step has `α_1² = 1 / (1 + u_1)`. -/
theorem fwdScale_one_geomGrid_sq {u1 : ℝ} (hu1 : 0 < u1) (r : ℝ) :
    fwdScale (geomGrid u1 r) 1 ^ 2 = (1 + u1)⁻¹ := by
  rw [fwdScale_sq, Nat.sub_self, geomGrid_zero, geomGrid, ite_eq_right one_ne_zero, Nat.sub_self,
    pow_zero, sub_zero]
  have h : -2 * 1 * (Real.log (1 + u1 * 1) / 2) = -Real.log (1 + u1) := by
    rw [mul_one, mul_one]; ring
  rw [h, Real.exp_neg, Real.exp_log (by linarith)]

/-- **Markov tail bound for the first forward step.** On the grid `geomGrid u1 r` with
`u_1 > 0`, for `ρ > 0` and every start `z`: the forward step `F_1 z = N(α_1 z, β_1 I)` gives
`F_1 z ({y | ρ² ≤ |y - z|²}) ≤ u_1 (|z|² + d) / ρ²`. -/
theorem fwdKernel_one_geomGrid_far_le {u1 : ℝ} (hu1 : 0 < u1) (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Fin d → ℝ) :
    fwdKernel (geomGrid u1 r) 1 z {y | ρ ^ 2 ≤ sqDist z y} ≤
      ENNReal.ofReal (u1 * (∑ j, z j ^ 2 + d) / ρ ^ 2) := by
  set t := geomGrid u1 r
  set α := fwdScale t 1 with hα
  have hα2 : α ^ 2 = (1 + u1)⁻¹ := fwdScale_one_geomGrid_sq hu1 r
  have hα0 : 0 < α := fwdScale_pos t 1
  have hβ : fwdVar t 1 = 1 - α ^ 2 := rfl
  have hinv1 : (1 + u1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hβ0 : 0 ≤ fwdVar t 1 := by rw [hβ, hα2]; linarith
  have hβu : fwdVar t 1 ≤ u1 := by
    rw [hβ, hα2]
    have h1 : 1 - (1 + u1)⁻¹ = u1 * (1 + u1)⁻¹ := by field_simp; ring
    rw [h1]
    exact mul_le_of_le_one_right hu1.le hinv1
  have hα1 : α ≤ 1 := by nlinarith
  have hαu : (1 - α) ^ 2 ≤ u1 := by nlinarith
  -- Markov's inequality on `|y - z|²`
  have hmeas : Measurable fun y => ENNReal.ofReal (sqDist z y) :=
    ENNReal.measurable_ofReal.comp (measurable_sqDist z)
  have hM := mul_meas_ge_le_lintegral₀ (μ := fwdKernel t 1 z) hmeas.aemeasurable
    (ENNReal.ofReal (ρ ^ 2))
  rw [fwdKernel_apply, lintegral_sqDist_pi z (fun i => α * z i)] at hM
  rw [← fwdKernel_apply] at hM
  have hsub : {y | ρ ^ 2 ≤ sqDist z y} ⊆
      {y | ENNReal.ofReal (ρ ^ 2) ≤ ENNReal.ofReal (sqDist z y)} :=
    fun y hy => ENNReal.ofReal_le_ofReal hy
  have hM' : ENNReal.ofReal (ρ ^ 2) * fwdKernel t 1 z {y | ρ ^ 2 ≤ sqDist z y} ≤
      ENNReal.ofReal (u1 * (∑ j, z j ^ 2 + d)) := by
    refine (mul_le_mul_right (measure_mono hsub) _).trans (hM.trans
      (ENNReal.ofReal_le_ofReal ?_))
    rw [Real.coe_toNNReal _ hβ0, mul_add, mul_sum,
      show u1 * (d : ℝ) = ∑ _j : Fin d, u1 by simp; ring, ← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    have : (α * z j - z j) ^ 2 = (1 - α) ^ 2 * z j ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (z j)]
  have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
  rw [ENNReal.ofReal_div_of_pos hρ2,
    ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hρ2).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hM'

/-- **Tail bound for the smoothed empirical law.** For a nonempty training set `x`, `u_1 > 0`
and `ρ > 0`, the time-`t_1` forward law `p_1` of `μ_n` on the grid `geomGrid u1 r` puts mass
`≤ u_1 (∑ᵢ |x_i|² + d) / ρ²` on the set of points at distance `≥ ρ` from every training point.
-/
theorem fwdLaw_one_outside_le [NeZero n] (x : Fin n → Fin d → ℝ) {u1 : ℝ} (hu1 : 0 < u1)
    (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (fwdLaw (empirical x) (geomGrid u1 r) 1).real (⋂ i, {y | ρ ^ 2 ≤ sqDist (x i) y}) ≤
      u1 * (∑ i, ∑ j, x i j ^ 2 + d) / ρ ^ 2 := by
  set C := u1 * (∑ i, ∑ j, x i j ^ 2 + d) / ρ ^ 2 with hCdef
  have hC : 0 ≤ C := by positivity
  have hmeas : MeasurableSet (⋂ i, {y | ρ ^ 2 ≤ sqDist (x i) y}) :=
    MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_sqDist _)
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  rw [fwdLaw_succ, fwdLaw_zero, Measure.bind_apply hmeas (Kernel.aemeasurable _), empirical,
    lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  calc (n : ℝ≥0∞)⁻¹ * ∑ i, fwdKernel (geomGrid u1 r) (0 + 1) (x i)
        (⋂ i, {y | ρ ^ 2 ≤ sqDist (x i) y})
      ≤ (n : ℝ≥0∞)⁻¹ * ∑ _i : Fin n, ENNReal.ofReal C := by
        gcongr with i
        refine (measure_mono (Set.iInter_subset _ i)).trans
          ((fwdKernel_one_geomGrid_far_le hu1 r hρ (x i)).trans (ENNReal.ofReal_le_ofReal ?_))
        rw [hCdef]
        gcongr
        exact single_le_sum (f := fun i => ∑ j, x i j ^ 2)
          (fun i _ => sum_nonneg fun j _ => sq_nonneg _) (mem_univ i)
    _ = ENNReal.ofReal C := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by simp [NeZero.ne n]) (by simp), one_mul]

/-! ### Memorisation -/

/-- Core statement: for a nonempty training set, `ρ > 0`, `ε > 0`, some exact-score sampler
puts mass `≤ ε` far from the training set and `≥ 1 - ε` on the union of the balls. -/
theorem exists_output_near_training_set (x : Fin n → Fin d → ℝ) (hn : 0 < n) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ u1 : ℝ, 0 < u1 ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      (exactScoreOutput (empirical x) u1 r N).real (⋂ i, {y | ρ ^ 2 ≤ sqDist (x i) y}) ≤ ε ∧
      1 - ε ≤ (exactScoreOutput (empirical x) u1 r N).real (⋃ i, {y | sqDist (x i) y < ρ ^ 2})
    := by
  have : NeZero n := ⟨hn.ne'⟩
  set K : ℝ := ∑ i, ∑ j, x i j ^ 2 + d with hK
  have hK0 : 0 ≤ K := by positivity
  set u1 : ℝ := ε * ρ ^ 2 / (2 * (K + 1)) with hu1def
  have hu1 : 0 < u1 := by positivity
  have hu1K : u1 * K / ρ ^ 2 ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity), hu1def]
    have : ε * ρ ^ 2 / (2 * (K + 1)) * K = ε / 2 * ρ ^ 2 * (K / (K + 1)) := by
      field_simp
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  obtain ⟨r, hr, N, hN, htv⟩ :=
    exists_tvSup_output_le (empirical x) (integrable_sqNorm_empirical x) hu1
      (by positivity : 0 < ε / 2)
  refine ⟨u1, hu1, r, hr, N, hN, ?_⟩
  set p := fwdLaw (empirical x) (geomGrid u1 r) 1
  set q := exactScoreOutput (empirical x) u1 r N
  set T := ⋂ i, {y | ρ ^ 2 ≤ sqDist (x i) y}
  set S := ⋃ i, {y | sqDist (x i) y < ρ ^ 2}
  have hT : MeasurableSet T :=
    MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_sqDist _)
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion fun i => measurableSet_lt (measurable_sqDist _) measurable_const
  have hpT : p.real T ≤ ε / 2 := (fwdLaw_one_outside_le x hu1 r hρ).trans hu1K
  have htvT := abs_le.1 (TotalVariation.abs_measureReal_sub_le_tvSup (μ := p) (ν := q) hT)
  have htvS := abs_le.1 (TotalVariation.abs_measureReal_sub_le_tvSup (μ := p) (ν := q) hS)
  have hcover : S ∪ T = Set.univ := by
    ext y
    simp only [S, T, Set.mem_union, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq,
      Set.mem_univ, iff_true]
    by_cases h : ∃ i, sqDist (x i) y < ρ ^ 2
    · exact Or.inl h
    · push Not at h; exact Or.inr h
  have hpS : 1 - ε / 2 ≤ p.real S := by
    have := measureReal_union_le (μ := p) S T
    rw [hcover, probReal_univ] at this
    linarith
  constructor <;> linarith

/-- **Memorisation (headline).** Let `x : Fin n → (Fin d → ℝ)` be a nonempty training set with
empirical measure `μ_n = (1/n) ∑ᵢ δ_{x_i}`. For every radius `ρ > 0` and every `ε > 0` there
are sampler parameters `u_1 > 0`, `r > 1`, `N ≥ 1` such that the DDPM sampler on the geometric
grid `geomGrid u_1 r` with `N` steps and the **exact** score of `μ_n` outputs a law `q_1`
(`exactScoreOutput`) with `q_1(⋃ᵢ {y | |y - x_i|² < ρ²}) ≥ 1 - ε` (Euclidean balls). A perfect
score model only reproduces its training data. -/
theorem output_concentrates_on_training_set (x : Fin n → Fin d → ℝ) (hn : 0 < n) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ u1 : ℝ, 0 < u1 ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      1 - ε ≤ (exactScoreOutput (empirical x) u1 r N).real (⋃ i, {y | sqDist (x i) y < ρ ^ 2})
    := by
  obtain ⟨u1, hu1, r, hr, N, hN, -, h⟩ := exists_output_near_training_set x hn hρ hε
  exact ⟨u1, hu1, r, hr, N, hN, h⟩

/-- **Nothing new is generated.** Under the hypotheses of `output_concentrates_on_training_set`,
some exact-score sampler gives mass `≤ ε` to the points at Euclidean distance `≥ ρ` from every
training point: `q_1({y | ∀ i, |y - x_i|² ≥ ρ²}) ≤ ε`. -/
theorem output_outside_training_set_le (x : Fin n → Fin d → ℝ) (hn : 0 < n) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ u1 : ℝ, 0 < u1 ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      (exactScoreOutput (empirical x) u1 r N).real (⋂ i, {y | ρ ^ 2 ≤ sqDist (x i) y}) ≤ ε := by
  obtain ⟨u1, hu1, r, hr, N, hN, h, -⟩ := exists_output_near_training_set x hn hρ hε
  exact ⟨u1, hu1, r, hr, N, hN, h⟩

/-- A set that is a neighbourhood of every training point contains a common Euclidean ball
around each of them: `∃ ρ > 0, ∀ i, {y | |y - x_i|² < ρ²} ⊆ U`. -/
theorem exists_ball_subset_of_nhds (x : Fin n → Fin d → ℝ) (hn : 0 < n)
    {U : Set (Fin d → ℝ)} (hU : ∀ i, U ∈ 𝓝 (x i)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, {y | sqDist (x i) y < ρ ^ 2} ⊆ U := by
  choose δ hδ hδU using fun i => Metric.mem_nhds_iff.1 (hU i)
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  refine ⟨univ.inf' hne δ, (lt_inf'_iff hne).2 fun i _ => hδ i, fun i y hy => hδU i ?_⟩
  have hρ : 0 < univ.inf' hne δ := (lt_inf'_iff hne).2 fun i _ => hδ i
  refine lt_of_lt_of_le ((dist_pi_lt_iff hρ).2 fun j => ?_) (inf'_le _ (mem_univ i))
  rw [Real.dist_eq]
  refine abs_lt_of_sq_lt_sq ?_ hρ.le
  exact lt_of_le_of_lt (single_le_sum (f := fun j => (y j - x i j) ^ 2)
    (fun j _ => sq_nonneg _) (mem_univ j)) hy

/-- **Mass outside any neighbourhood of the training set.** If `U` is a neighbourhood of every
training point (e.g. an open set containing them), then for every `ε > 0` some exact-score
sampler gives `q_1(Uᶜ) ≤ ε`. -/
theorem output_outside_nhds_le (x : Fin n → Fin d → ℝ) (hn : 0 < n) {U : Set (Fin d → ℝ)}
    (hU : ∀ i, U ∈ 𝓝 (x i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u1 : ℝ, 0 < u1 ∧ ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      (exactScoreOutput (empirical x) u1 r N).real Uᶜ ≤ ε := by
  obtain ⟨ρ, hρ, hρU⟩ := exists_ball_subset_of_nhds x hn hU
  obtain ⟨u1, hu1, r, hr, N, hN, h⟩ := output_outside_training_set_le x hn hρ hε
  refine ⟨u1, hu1, r, hr, N, hN, le_trans (measureReal_mono fun y hy => ?_) h⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro i
  by_contra hlt
  exact hy (hρU i (not_le.1 hlt))

/-- **The output's mass outside the training set tends to `0`.** If `U` is a neighbourhood of
every training point, there is a sequence of exact-score samplers (parameters
`u_1^{(m)} > 0`, `r^{(m)} > 1`, `N^{(m)} ≥ 1`) whose outputs satisfy `q_1^{(m)}(Uᶜ) → 0`. -/
theorem tendsto_output_outside_nhds (x : Fin n → Fin d → ℝ) (hn : 0 < n)
    {U : Set (Fin d → ℝ)} (hU : ∀ i, U ∈ 𝓝 (x i)) :
    ∃ (u1 r : ℕ → ℝ) (N : ℕ → ℕ), (∀ m, 0 < u1 m ∧ 1 < r m ∧ 1 ≤ N m) ∧
      Tendsto (fun m => (exactScoreOutput (empirical x) (u1 m) (r m) (N m)).real Uᶜ) atTop
        (𝓝 0) := by
  choose u1 hu1 r hr N hN h using fun m : ℕ =>
    output_outside_nhds_le x hn hU (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
  exact ⟨u1, r, N, fun m => ⟨hu1 m, hr m, hN m⟩,
    squeeze_zero (fun _ => measureReal_nonneg) h tendsto_one_div_add_atTop_nhds_zero_nat⟩

end FormalizeSampling.DiffusionMemorization
