module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import FormalizeSampling.Flow.FokkerPlanckExistence

/-!
# Extraction of a weakly convergent subsequence of measure curves

Status: **Verified.** An Arzelà–Ascoli-type compactness statement for curves of probability
measures on `Fin d → ℝ` (weak topology), used to pass to the limit in families of solutions of
the weak Fokker–Planck equation (`Flow/FokkerPlanckExistenceDissipative.lean`).

Let `ν k : ℝ → 𝒫(ℝᵈ)`, `k ∈ ℕ`, be curves such that

* (**uniform tightness**) for every `T`, `{ν k t | k ∈ ℕ, t ≤ T}` is tight;
* (**uniform local equicontinuity on test functions**) for every `φ ∈ C²_c` and `T` there are
  `C` and `k₀` with `|∫ φ dν k t - ∫ φ dν k s| ≤ C |t - s|` for all `k ≥ k₀` and `s, t ≤ T`.

Then (`exists_subseq_tendsto_curve`) there are a strictly increasing `ψ : ℕ → ℕ` and a weakly
continuous curve `ν∞` with `ν (ψ j) t → ν∞ t` weakly for **every** `t : ℝ`.

Proof: Prokhorov at every rational time, Tychonoff in `ℚ → 𝒫(ℝᵈ)` (a countable product of
metrizable spaces, so compact sets are sequentially compact): this is the diagonal argument.
At an arbitrary time the `C²_c` integrals are Cauchy by equicontinuity, and tightness
identifies a limit (`exists_tendsto_of_isTight`). Continuity of `ν∞` follows from the inherited
Lipschitz bound and tightness.

## Not proved here

* No rate, no metric (Lévy–Prokhorov) statement, no uniqueness of the limit (different
  subsequences may a priori have different limits).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence
open NoiseScore

variable {d : ℕ}

/-- **Diagonal extraction at rational times.** If `{ν k t | k, t ≤ T}` is tight for every `T`,
there is a strictly increasing `ψ` such that `ν (ψ j) q` converges weakly for every `q : ℚ`. -/
theorem exists_subseq_tendsto_rat {ν : ℕ → ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (htight : ∀ T : ℝ, IsTightMeasureSet
      {μ | ∃ k : ℕ, ∃ t ≤ T, μ = (ν k t : Measure (Fin d → ℝ))}) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ a : ℚ → ProbabilityMeasure (Fin d → ℝ),
      ∀ q : ℚ, Tendsto (fun j => ν (ψ j) q) atTop (𝓝 (a q)) := by
  set K : ℚ → Set (ProbabilityMeasure (Fin d → ℝ)) := fun q =>
    closure {μ : ProbabilityMeasure (Fin d → ℝ) | (μ : Measure (Fin d → ℝ)) ∈
      {μ | ∃ k : ℕ, ∃ t ≤ (q : ℝ), μ = (ν k t : Measure (Fin d → ℝ))}}
  have hK : IsCompact (Set.pi univ K) :=
    isCompact_univ_pi fun q => isCompact_closure_of_tight (htight q)
  set u : ℕ → ℚ → ProbabilityMeasure (Fin d → ℝ) := fun k q => ν k q
  have hu : ∀ k, u k ∈ Set.pi univ K := fun k q _ =>
    subset_closure ⟨k, q, le_rfl, rfl⟩
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq hu
  exact ⟨ψ, hψ, a, fun q => tendsto_pi_nhds.1 hlim q⟩

/-- A strictly increasing `ψ : ℕ → ℕ` satisfies `j ≤ ψ j`. -/
theorem le_of_strictMono {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (j : ℕ) : j ≤ ψ j :=
  hψ.id_le j

/-- **Cauchy property at an arbitrary time.** Under uniform equicontinuity on a test function
`φ` on `(-∞, T]`, if `∫ φ dν (ψ j) q` converges for every rational `q`, then `∫ φ dν (ψ j) t`
converges for every real `t < T`. -/
theorem exists_tendsto_integral_of_rat {ν : ℕ → ℝ → ProbabilityMeasure (Fin d → ℝ)}
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {φ : (Fin d → ℝ) → ℝ} {C T : ℝ} {k₀ : ℕ}
    (hC : ∀ k ≥ k₀, ∀ s t, s ≤ T → t ≤ T → |∫ x, φ x ∂(ν k t : Measure (Fin d → ℝ)) -
      ∫ x, φ x ∂(ν k s : Measure (Fin d → ℝ))| ≤ C * |t - s|)
    (hq : ∀ q : ℚ, ∃ c, Tendsto (fun j => ∫ x, φ x ∂(ν (ψ j) q : Measure (Fin d → ℝ))) atTop
      (𝓝 c)) {t : ℝ} (htT : t < T) :
    ∃ c, Tendsto (fun j => ∫ x, φ x ∂(ν (ψ j) t : Measure (Fin d → ℝ))) atTop (𝓝 c) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set δ := ε / (4 * (|C| + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right t hδ0) htT)
  have hqT : (q : ℝ) ≤ T := hq2.le.trans (min_le_right _ _)
  have hqδ : (q : ℝ) < t + δ := hq2.trans_le (min_le_left _ _)
  obtain ⟨c, hc⟩ := hq q
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hc.cauchySeq (ε / 2) (by positivity)
  refine ⟨max N₁ k₀, fun n hn => ?_⟩
  have hCδ : |C| * |(q : ℝ) - t| ≤ ε / 4 := by
    have h1 : |(q : ℝ) - t| ≤ δ := by rw [abs_le]; constructor <;> linarith
    calc |C| * |(q : ℝ) - t| ≤ |C| * δ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ (|C| + 1) * δ := by nlinarith
      _ = ε / 4 := by rw [hδ]; field_simp
  have hb : ∀ m ≥ k₀, |∫ x, φ x ∂(ν (ψ m) q : Measure (Fin d → ℝ)) -
      ∫ x, φ x ∂(ν (ψ m) t : Measure (Fin d → ℝ))| ≤ ε / 4 := fun m hm =>
    (hC _ ((hm.trans (le_of_strictMono hψ m))) t q htT.le hqT).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)).trans hCδ)
  have h1 := hb n (le_of_max_le_right hn)
  have h2 := hb (max N₁ k₀) (le_max_right _ _)
  have h3 := hN₁ n (le_of_max_le_left hn) (max N₁ k₀) (le_max_left _ _)
  rw [Real.dist_eq] at h3 ⊢
  have := abs_sub_lt_iff.1 h3
  rw [abs_lt]
  constructor <;> linarith [abs_le.1 h1, abs_le.1 h2]

/-- **Arzelà–Ascoli for measure curves (Verified).** Let `ν k : ℝ → 𝒫(ℝᵈ)` be curves such
that `{ν k t | k ∈ ℕ, t ≤ T}` is tight for every `T`, and such that for every `φ ∈ C²_c` and
every `T` there are `C`, `k₀` with `|∫ φ dν k t - ∫ φ dν k s| ≤ C |t - s|` for all `k ≥ k₀` and
all `s, t ≤ T`. Then some subsequence `ν (ψ j)` converges weakly at **every** time `t` to a
weakly continuous curve `ν∞`. -/
theorem exists_subseq_tendsto_curve {ν : ℕ → ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (htight : ∀ T : ℝ, IsTightMeasureSet
      {μ | ∃ k : ℕ, ∃ t ≤ T, μ = (ν k t : Measure (Fin d → ℝ))})
    (hlip : ∀ φ, TestFunction2 φ → ∀ T : ℝ, ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ s t, s ≤ T →
      t ≤ T → |∫ x, φ x ∂(ν k t : Measure (Fin d → ℝ)) -
        ∫ x, φ x ∂(ν k s : Measure (Fin d → ℝ))| ≤ C * |t - s|) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ ν' : ℝ → ProbabilityMeasure (Fin d → ℝ), Continuous ν' ∧
      ∀ t, Tendsto (fun j => ν (ψ j) t) atTop (𝓝 (ν' t)) := by
  obtain ⟨ψ, hψ, a, ha⟩ := exists_subseq_tendsto_rat htight
  have hconv : ∀ t : ℝ, ∃ μ : ProbabilityMeasure (Fin d → ℝ),
      Tendsto (fun j => ν (ψ j) t) atTop (𝓝 μ) := by
    intro t
    refine exists_tendsto_of_isTight (htight t) (fun j => ⟨ψ j, t, le_rfl, rfl⟩)
      fun φ hφ => ?_
    obtain ⟨C, k₀, hC⟩ := hlip φ hφ (t + 1)
    refine exists_tendsto_integral_of_rat hψ hC (fun q => ?_) (lt_add_one t)
    obtain ⟨⟨M, hM⟩, -⟩ := testFunction2_bounds hφ
    exact ⟨_, tendsto_integral_of_tendsto (ha q) hφ.1.continuous hM⟩
  choose ν' hν' using hconv
  refine ⟨ψ, hψ, ν', ?_, hν'⟩
  -- tightness of the limit curve on `t ≤ T`
  have htight' : ∀ T : ℝ, IsTightMeasureSet
      {μ | ∃ r ≤ T, μ = (ν' r : Measure (Fin d → ℝ))} := by
    intro T
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKε⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (htight T) ε hε
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
    refine ⟨closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    rintro μ ⟨r, hr, rfl⟩
    refine measure_compl_closedBall_le_of_tendsto (hν' r) (Eventually.of_forall fun j => ?_)
    exact (measure_mono (compl_subset_compl.2 hR)).trans (hKε _ ⟨ψ j, r, hr, rfl⟩)
  -- local Lipschitz bound of the limit integrals, hence continuity
  have hcont : ∀ φ, TestFunction2 φ →
      Continuous fun t => ∫ x, φ x ∂(ν' t : Measure (Fin d → ℝ)) := by
    intro φ hφ
    obtain ⟨⟨M, hM⟩, -⟩ := testFunction2_bounds hφ
    rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨C, k₀, hC⟩ := hlip φ hφ (t₀ + 1)
    have hl : ∀ t, t ≤ t₀ + 1 → |∫ x, φ x ∂(ν' t : Measure (Fin d → ℝ)) -
        ∫ x, φ x ∂(ν' t₀ : Measure (Fin d → ℝ))| ≤ C * |t - t₀| := by
      intro t ht
      have h1 := tendsto_integral_of_tendsto (hν' t) hφ.1.continuous hM
      have h2 := tendsto_integral_of_tendsto (hν' t₀) hφ.1.continuous hM
      refine le_of_tendsto (h1.sub h2).abs (eventually_atTop.2 ⟨k₀, fun j hj => ?_⟩)
      exact hC _ (hj.trans (le_of_strictMono hψ j)) t₀ t (by linarith) ht
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (g := fun t => C * |t - t₀|) ?_
    · filter_upwards [eventually_le_nhds (lt_add_one t₀)] with t ht
      rw [Real.norm_eq_abs]; exact hl t ht
    · have : Tendsto (fun t : ℝ => C * |t - t₀|) (𝓝 t₀) (𝓝 (C * |t₀ - t₀|)) :=
        ((continuous_id.sub continuous_const).abs.const_mul C).continuousAt
      simpa using this
  rw [continuous_iff_continuousAt]
  intro r₀
  exact tendsto_of_isTight_of_integral_tendsto (htight' (r₀ + 1))
    ((eventually_le_nhds (lt_add_one r₀)).mono fun r hr => ⟨r, hr, rfl⟩)
    fun φ hφ => (hcont φ hφ).continuousAt

end FormalizeSampling.FokkerPlanckExistence
