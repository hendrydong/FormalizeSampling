module

public import FormalizeSampling.Flow.FokkerPlanckExistenceExtract
public import FormalizeSampling.Flow.FokkerPlanckExistenceTime

/-!
# Existence for the weak Fokker–Planck equation: drifts merely continuous in time

Status: **Verified.** Removes the Hölder-`½`-in-time assumption of
`Flow/FokkerPlanckExistenceTime.lean`. For a drift `b : ℝ → ℝᵈ → ℝᵈ` that is **jointly
continuous** in `(t, x)` and, on every bounded time interval `[0, T]`, Lipschitz in `x`
uniformly in `t`, a diffusion constant `D > 0` and an **arbitrary** probability measure `ρ₀`,
there is a weakly continuous curve `ν` of probability measures with `ν 0 = ρ₀` solving
`WeakFokkerPlanck (ν ·) b D` (`exists_weakFokkerPlanck_continuousTime`).

## Construction

1. **Time averaging** (`timeAvg`): `b^ε(t, x) = ε⁻¹ ∫₀^ε b(t + u, x) du`. On `[0, T]` it is
   Lipschitz in `x` with the constant of `b` on `[0, T + 1]`, has linear growth with the
   constant of `b` on `[0, T + 1]` (`norm_timeAvg_le`), and is Lipschitz in time with constant
   `2 B / ε` (`norm_timeAvg_sub_time_le`), hence Hölder-`½` on `[0, T]`. The existing theorem
   `exists_weakFokkerPlanck_time` gives solutions `ν^k` for `ε = 1 / (k + 1)`.
2. **Uniform estimates**: tightness of `{ν^k_t | k, t ≤ T}` from the Lyapunov estimate of the
   EM laws, which only depends on the linear growth constant on `[0, T]`
   (`isTightMeasureSet_tdCurve_family`, `isTight_avgSol`); local equicontinuity on test
   functions from the integrated identity (`abs_integral_avgSol_sub_le`).
3. **Extraction** (`exists_subseq_tendsto_curve`) and **passage to the limit**: `b^ε → b`
   uniformly on compact sets in `x` at each time (`norm_timeAvg_sub_le`), so the generators
   converge uniformly on the support of each test function; dominated convergence in time.
4. **Continuity of the generator integral** `r ↦ ∫ (b_r ⬝ ∇φ + D Δφ) dν_r` for jointly
   continuous `b` and weakly continuous `ν` (`continuous_integral_fpGen_curve`, by uniform
   continuity on compact sets), used both for the FTC (`integral_eq_of_weakFokkerPlanck`) and
   for the final derivative.

## Not proved here

* Uniqueness (it is
  `FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_lipschitz_continuousTime`, in
  `Flow/FokkerPlanckUniquenessLipschitz.lean`); convergence of the whole family `ν^k` (only a
  subsequence is extracted); the time-dependent EM scheme for `b` itself.
* Locally Lipschitz / dissipative time-dependent drifts (the autonomous case is
  `Flow/FokkerPlanckExistenceDissipative.lean`); drifts measurable but not continuous in time.
* Identification with the law of an SDE; `D = 0`; non-constant diffusion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal Interval

namespace FormalizeSampling.FokkerPlanckExistence
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU

variable {d : ℕ}

section Avg

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-- The **time-averaged drift** `b^ε(t, x) = ε⁻¹ ∫₀^ε b(u + t, x) du`. -/
noncomputable def timeAvg (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (ε t : ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ :=
  ε⁻¹ • ∫ u in (0 : ℝ)..ε, b (u + t) x

/-- Space slices of a jointly continuous drift are continuous. -/
theorem continuous_slice (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2) (t : ℝ) :
    Continuous (b t) :=
  hbc.comp (continuous_const.prodMk continuous_id)

/-- Time slices of a jointly continuous drift are continuous. -/
theorem continuous_slice_time (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (x : Fin d → ℝ) : Continuous fun t => b t x :=
  hbc.comp (continuous_id.prodMk continuous_const)

/-- `u ↦ b (u + t) x` is interval integrable. -/
theorem intervalIntegrable_shift (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (t : ℝ) (x : Fin d → ℝ) (a c : ℝ) :
    IntervalIntegrable (fun u => b (u + t) x) volume a c :=
  ((continuous_slice_time hbc x).comp (continuous_id.add continuous_const)).intervalIntegrable
    a c

/-- The time-averaged drift is jointly continuous. -/
theorem continuous_timeAvg (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (ε : ℝ) : Continuous fun p : ℝ × (Fin d → ℝ) => timeAvg b ε p.1 p.2 := by
  unfold timeAvg
  have hf : Continuous (Function.uncurry
      fun (p : ℝ × (Fin d → ℝ)) (u : ℝ) => b (u + p.1) p.2) :=
    hbc.comp ((continuous_snd.add (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst))
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 ε).const_smul
    ε⁻¹

/-- **Uniform continuity on compact sets.** For jointly continuous `b`, compact `K` and
`η > 0`: `‖b r y - b r₀ y‖ < η` for all `y ∈ K` and all `r` near `r₀`. -/
theorem eventually_norm_sub_lt (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (r₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝 r₀, ∀ y ∈ K, ‖b r y - b r₀ y‖ < η := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : Continuous (Function.uncurry fun (r : ℝ) (y : K) => b r y) :=
    hbc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu := Continuous.tendstoUniformly (fun (r : ℝ) (y : K) => b r y) hc r₀
  rw [Metric.tendstoUniformly_iff] at hu
  filter_upwards [hu η hη] with r hr y hy
  have := hr ⟨y, hy⟩
  rwa [dist_eq_norm, norm_sub_rev] at this

/-- **Linear growth on bounded time intervals.** If `b` is jointly continuous and `b t` is
`L_T`-Lipschitz for `t ∈ [0, T]`, then `‖b t x‖ ≤ B (1 + ‖x‖)` on `[0, T]` for some `B ≥ 0`. -/
theorem exists_linGrowth (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (hL : ∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (b t)) (T : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ v ∈ Icc 0 T, ∀ x, ‖b v x‖ ≤ B * (1 + ‖x‖) := by
  obtain ⟨L, hLT⟩ := hL T
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_slice_time hbc 0).continuousOn
  refine ⟨L + max M₀ 0, by positivity, fun v hv x => ?_⟩
  have h1 : ‖b v x - b v 0‖ ≤ L * ‖x‖ := by simpa using (hLT v hv).norm_sub_le x 0
  have h2 : ‖b v 0‖ ≤ max M₀ 0 := (hM₀ v hv).trans (le_max_left _ _)
  have h3 : ‖b v x‖ ≤ ‖b v x - b v 0‖ + ‖b v 0‖ := by
    calc ‖b v x‖ = ‖(b v x - b v 0) + b v 0‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  nlinarith [L.coe_nonneg, norm_nonneg x, mul_nonneg (le_max_right M₀ 0) (norm_nonneg x)]

/-- **Linear growth of the average.** If `‖b v x‖ ≤ B (1 + ‖x‖)` for `v ∈ [0, T]`, then
`‖b^ε t x‖ ≤ B (1 + ‖x‖)` for `ε > 0` and `0 ≤ t`, `t + ε ≤ T`. -/
theorem norm_timeAvg_le {ε : ℝ} (hε : 0 < ε) {T B : ℝ}
    (hB : ∀ v ∈ Icc 0 T, ∀ x, ‖b v x‖ ≤ B * (1 + ‖x‖)) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t + ε ≤ T) (x : Fin d → ℝ) : ‖timeAvg b ε t x‖ ≤ B * (1 + ‖x‖) := by
  unfold timeAvg
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  have h : ‖∫ u in (0 : ℝ)..ε, b (u + t) x‖ ≤ B * (1 + ‖x‖) * |ε - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => hB _ ?_ x
    rw [uIoc_of_le hε.le] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [sub_zero, abs_of_pos hε] at h
  calc ε⁻¹ * ‖∫ u in (0 : ℝ)..ε, b (u + t) x‖ ≤ ε⁻¹ * (B * (1 + ‖x‖) * ε) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = B * (1 + ‖x‖) := by field_simp

/-- **Lipschitz property of the average.** If `b v` is `L`-Lipschitz for `v ∈ [0, T]`, then
`b^ε t` is `L`-Lipschitz for `ε > 0`, `0 ≤ t`, `t + ε ≤ T`. -/
theorem lipschitzWith_timeAvg (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    {ε : ℝ} (hε : 0 < ε) {T : ℝ} {L : ℝ≥0} (hL : ∀ v ∈ Icc 0 T, LipschitzWith L (b v))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t + ε ≤ T) : LipschitzWith L (timeAvg b ε t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  unfold timeAvg
  rw [← smul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_shift hbc t x 0 ε)
    (intervalIntegrable_shift hbc t y 0 ε), norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hε]
  have h : ‖∫ u in (0 : ℝ)..ε, (b (u + t) x - b (u + t) y)‖ ≤ L * ‖x - y‖ * |ε - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le hε.le] at hu
    exact (hL _ ⟨by linarith [hu.1], by linarith [hu.2]⟩).norm_sub_le x y
  rw [sub_zero, abs_of_pos hε] at h
  calc ε⁻¹ * ‖∫ u in (0 : ℝ)..ε, (b (u + t) x - b (u + t) y)‖ ≤
      ε⁻¹ * (L * ‖x - y‖ * ε) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = L * ‖x - y‖ := by field_simp

/-- **Time regularity of the average.** If `‖b v x‖ ≤ B (1 + ‖x‖)` for `v ∈ [0, T + 1]`, then
for `0 < ε ≤ 1` and `s, t ∈ [0, T]`: `‖b^ε t x - b^ε s x‖ ≤ 2 ε⁻¹ B (1 + ‖x‖) |t - s|`. -/
theorem norm_timeAvg_sub_time_le (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {T B : ℝ}
    (hB : ∀ v ∈ Icc 0 (T + 1), ∀ x, ‖b v x‖ ≤ B * (1 + ‖x‖)) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (x : Fin d → ℝ) :
    ‖timeAvg b ε t x - timeAvg b ε s x‖ ≤ 2 * ε⁻¹ * B * (1 + ‖x‖) * |t - s| := by
  have hfi : ∀ a c, IntervalIntegrable (fun v => b v x) volume a c := fun a c =>
    (continuous_slice_time hbc x).intervalIntegrable a c
  unfold timeAvg
  rw [← smul_sub, intervalIntegral.integral_comp_add_right (fun v => b v x),
    intervalIntegral.integral_comp_add_right (fun v => b v x),
    intervalIntegral.integral_interval_sub_interval_comm (hfi _ _) (hfi _ _) (hfi _ _),
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  have hmem : ∀ a c v, a ∈ Icc (0 : ℝ) (T + 1) → c ∈ Icc (0 : ℝ) (T + 1) → v ∈ Ι a c →
      v ∈ Icc (0 : ℝ) (T + 1) := by
    intro a c v ha hc hv
    rcases mem_uIoc.1 hv with h | h
    · exact ⟨by linarith [ha.1, h.1], by linarith [hc.2, h.2]⟩
    · exact ⟨by linarith [hc.1, h.1], by linarith [ha.2, h.2]⟩
  have h1 : ‖∫ v in (0 + t)..(0 + s), b v x‖ ≤ B * (1 + ‖x‖) * |0 + s - (0 + t)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => hB v (hmem _ _ v
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩ hv) x
  have h2 : ‖∫ v in (ε + t)..(ε + s), b v x‖ ≤ B * (1 + ‖x‖) * |ε + s - (ε + t)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => hB v (hmem _ _ v
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩ hv) x
  have e1 : |0 + s - (0 + t)| = |t - s| := by rw [abs_sub_comm]; ring_nf
  have e2 : |ε + s - (ε + t)| = |t - s| := by rw [abs_sub_comm]; ring_nf
  rw [e1] at h1
  rw [e2] at h2
  calc ε⁻¹ * ‖(∫ v in (0 + t)..(0 + s), b v x) - ∫ v in (ε + t)..(ε + s), b v x‖ ≤
      ε⁻¹ * (B * (1 + ‖x‖) * |t - s| + B * (1 + ‖x‖) * |t - s|) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = 2 * ε⁻¹ * B * (1 + ‖x‖) * |t - s| := by ring

/-- **Convergence of the average, uniformly on compact sets.** For jointly continuous `b`,
compact `K`, a time `r` and `η > 0`, there is `δ > 0` with `‖b^ε r y - b r y‖ ≤ η` for all
`y ∈ K` and `0 < ε < δ`. -/
theorem norm_timeAvg_sub_le (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (r : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ∀ y ∈ K, ‖timeAvg b ε r y - b r y‖ ≤ η := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_norm_sub_lt hbc hK r hη)
  refine ⟨δ, hδ, fun ε hε hεδ y hy => ?_⟩
  have e : timeAvg b ε r y - b r y = ε⁻¹ • ∫ u in (0 : ℝ)..ε, (b (u + r) y - b r y) := by
    unfold timeAvg
    rw [intervalIntegral.integral_sub (intervalIntegrable_shift hbc r y 0 ε)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_sub, smul_smul, sub_zero,
      inv_mul_cancel₀ hε.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  have h : ‖∫ u in (0 : ℝ)..ε, (b (u + r) y - b r y)‖ ≤ η * |ε - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le hε.le] at hu
    refine (hball ?_ y hy).le
    rw [Real.dist_eq, add_sub_cancel_right, abs_of_pos hu.1]
    linarith [hu.2]
  rw [sub_zero, abs_of_pos hε] at h
  calc ε⁻¹ * ‖∫ u in (0 : ℝ)..ε, (b (u + r) y - b r y)‖ ≤ ε⁻¹ * (η * ε) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = η := by field_simp

end Avg

/-! ### Generators of jointly continuous drifts -/

/-- **Generator difference on the support.** If `(1 + ‖y‖) ∑ᵢ |∂ᵢφ(y)| ≤ Mψ` and
`‖v y - w y‖ ≤ η` on `tsupport φ` (`η ≥ 0`), then `|L^v φ - L^w φ| ≤ η Mψ` everywhere. -/
theorem abs_fpGen_sub_le_of_tsupport {φ : (Fin d → ℝ) → ℝ} {Mψ : ℝ}
    (hMψ : ∀ y, (1 + ‖y‖) * ∑ i, |partialDeriv i φ y| ≤ Mψ) (D : ℝ)
    {v w : (Fin d → ℝ) → Fin d → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hvw : ∀ y ∈ tsupport φ, ‖v y - w y‖ ≤ η) (y : Fin d → ℝ) :
    |fpGen v D φ y - fpGen w D φ y| ≤ η * Mψ := by
  have hMψ0 : 0 ≤ Mψ := by
    have h := hMψ 0
    have : 0 ≤ (1 + ‖(0 : Fin d → ℝ)‖) * ∑ i, |partialDeriv i φ 0| :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    linarith
  have e : fpGen v D φ y - fpGen w D φ y = (v y - w y) ⬝ᵥ grad φ y := by
    simp only [fpGen, sub_dotProduct]; ring
  rw [e]
  by_cases hy : y ∈ tsupport φ
  · refine (abs_dotProduct_grad_le _ φ y).trans ?_
    have hs : 0 ≤ ∑ i, |partialDeriv i φ y| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h1 : ∑ i, |partialDeriv i φ y| ≤ Mψ := by
      have := hMψ y
      nlinarith [norm_nonneg y]
    calc ‖v y - w y‖ * ∑ i, |partialDeriv i φ y| ≤ η * ∑ i, |partialDeriv i φ y| :=
          mul_le_mul_of_nonneg_right (hvw y hy) hs
      _ ≤ η * Mψ := mul_le_mul_of_nonneg_left h1 hη
  · have hg : grad φ y = 0 := funext fun i => by
      show partialDeriv i φ y = 0
      exact image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_partialDeriv_subset i φ h)
    rw [hg, dotProduct_zero, abs_zero]
    exact mul_nonneg hη hMψ0

/-- **Continuity of the generator integral along a curve.** For a jointly continuous drift
`b`, a weakly continuous curve `ν` of probability measures and `φ ∈ C²_c`,
`r ↦ ∫ (b_r ⬝ ∇φ + D Δφ) dν_r` is continuous. -/
theorem continuous_integral_fpGen_curve {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)} (hν : Continuous ν) (D : ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    Continuous fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) := by
  obtain ⟨Mψ, hMψ0, hMψ⟩ := exists_bound_gradWeight hφ
  rw [continuous_iff_continuousAt]
  intro r₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M0, hM0⟩ := exists_bound_fpGen (continuous_slice hbc r₀) D hφ
  have hc0 := continuous_fpGen (continuous_slice hbc r₀) D hφ.1
  have h1 : Tendsto (fun r => ∫ y, fpGen (b r₀) D φ y ∂(ν r : Measure (Fin d → ℝ))) (𝓝 r₀)
      (𝓝 (∫ y, fpGen (b r₀) D φ y ∂(ν r₀ : Measure (Fin d → ℝ)))) :=
    ((continuous_integral_of_abs_le hc0 hM0).comp hν).tendsto r₀
  set η := ε / (2 * (Mψ + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hηM : η * Mψ < ε / 2 := by
    rw [hηdef]
    have : ε / (2 * (Mψ + 1)) * Mψ = ε / 2 * (Mψ / (Mψ + 1)) := by field_simp
    rw [this]
    have : Mψ / (Mψ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  filter_upwards [eventually_norm_sub_lt hbc hφ.2.isCompact r₀ hη,
    Metric.tendsto_nhds.1 h1 (ε / 2) (by positivity)] with r hr hr'
  obtain ⟨Mr, hMr⟩ := exists_bound_fpGen (continuous_slice hbc r) D hφ
  have h3 : |∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) -
      ∫ y, fpGen (b r₀) D φ y ∂(ν r : Measure (Fin d → ℝ))| ≤ η * Mψ :=
    abs_integral_sub_le_of_abs_le (continuous_fpGen (continuous_slice hbc r) D hφ.1) hc0
      (fun y => (hMr y).trans (le_max_left Mr M0)) (fun y => (hM0 y).trans (le_max_right Mr M0))
      (abs_fpGen_sub_le_of_tsupport hMψ D hη.le fun y hy => (hr y hy).le)
  rw [Real.dist_eq] at hr' ⊢
  calc _ = |(∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) -
        ∫ y, fpGen (b r₀) D φ y ∂(ν r : Measure (Fin d → ℝ))) +
        (∫ y, fpGen (b r₀) D φ y ∂(ν r : Measure (Fin d → ℝ)) -
        ∫ y, fpGen (b r₀) D φ y ∂(ν r₀ : Measure (Fin d → ℝ)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

/-- **Integrated form of the weak Fokker–Planck equation.** If `ν` is weakly continuous,
`b` jointly continuous and `WeakFokkerPlanck (ν ·) b D`, then for `φ ∈ C²_c` and `t ≥ 0`,
`∫ φ dν_t = ∫ φ dν_0 + ∫₀ᵗ ∫ (b_r ⬝ ∇φ + D Δφ) dν_r dr`. -/
theorem integral_eq_of_weakFokkerPlanck {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)} (hν : Continuous ν) {D : ℝ}
    (hfp : WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) b D)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, φ y ∂(ν t : Measure (Fin d → ℝ)) = ∫ y, φ y ∂(ν 0 : Measure (Fin d → ℝ)) +
      ∫ r in (0 : ℝ)..t, ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) := by
  have hF := continuous_integral_fpGen_curve hbc hν D hφ
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    ((continuous_integral_test hφ).comp hν).continuousOn
    (fun x hx => (hfp φ hφ x hx.1.le).mono (Ioi_subset_Ici hx.1.le))
    (hF.intervalIntegrable 0 t)
  simp only [Function.comp] at this
  rw [show (fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ))) =
    fun r => ∫ y, (b r y ⬝ᵥ grad φ y + D * laplacian φ y) ∂(ν r : Measure (Fin d → ℝ)) from rfl,
    this]
  ring

/-! ### Tightness of time-dependent EM laws, uniformly over a family of drifts -/

/-- **Tightness, uniformly over drifts with a common linear growth bound.** For `B`,
`D ≥ 0`, a probability measure `ρ₀` and `T`, the dyadic time-dependent EM laws
`tdCurve b hb D ρ₀ n t` over **all** drift families `b` with `‖b t y‖ ≤ B (1 + ‖y‖)` (all `t`),
all levels `n` and times `t ≤ T` form a tight set. -/
theorem isTightMeasureSet_tdCurve_family {B D : ℝ} (hD : 0 ≤ D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] (T : ℝ) :
    IsTightMeasureSet {μ | ∃ b : ℝ → (Fin d → ℝ) → Fin d → ℝ, ∃ hb : ∀ t, Measurable (b t),
      (∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) ∧ ∃ n : ℕ, ∃ t ≤ T, μ = tdCurve b hb D ρ₀ n t} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K₀, hK₀, hρK₀⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := ρ₀)) (ε / 2) hε2
  have hρ : ρ₀ K₀ᶜ ≤ ε / 2 := hρK₀ ρ₀ rfl
  obtain ⟨Λ₀, hΛ₀⟩ := hK₀.exists_bound_of_continuousOn continuous_lyap.continuousOn
  obtain ⟨η, hη0, hη1, hη2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε2
  have hη : 0 < η := ENNReal.ofReal_pos.1 hη1
  set T' := max T 0
  set c := lyapConst d B D with hcdef
  have hc0 : 0 ≤ c := lyapConst_nonneg B hD
  set C' : ℝ := Real.exp (c * T') * |Λ₀| with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set r : ℝ := Real.sqrt (C' / η) + 1 with hr
  have hr0 : 0 < r := by positivity
  have hCr : ENNReal.ofReal C' / ENNReal.ofReal (r ^ 2) ≤ ε / 2 := by
    refine (ENNReal.div_le_of_le_mul ?_).trans hη2.le
    rw [← ENNReal.ofReal_mul hη.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.sqrt (C' / η) ≤ r := by linarith
    have h2 : C' / η ≤ r ^ 2 := by
      calc C' / η = Real.sqrt (C' / η) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [div_le_iff₀ hη] at h2
    linarith
  refine ⟨closedBall 0 r, isCompact_closedBall _ _, ?_⟩
  rintro μ ⟨b, hb, hB, n, t, ht, rfl⟩
  have hh0 : 0 ≤ dyadicStep n := (dyadicStep_pos n).le
  have hh1 : dyadicStep n ≤ 1 := dyadicStep_le_one n
  have hT := dyadic_grid_bound n ht
  have hsub : (closedBall (0 : Fin d → ℝ) r)ᶜ ⊆
      {z | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (lyap z)} := by
    intro z hz
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
    have := one_add_sq_norm_le_lyap z
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  unfold tdCurve
  rw [Measure.bind_apply measurableSet_closedBall.compl (Kernel.aemeasurable _)]
  calc ∫⁻ x, tdPow b hb D (dyadicStep n) (gridIndex n t) x (closedBall 0 r)ᶜ ∂ρ₀
      ≤ ∫⁻ x, (ε / 2 + K₀ᶜ.indicator 1 x) ∂ρ₀ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K₀
        · refine le_trans ?_ (hCr.trans le_self_add)
          refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
            (ENNReal.measurable_ofReal.comp continuous_lyap.measurable).aemeasurable
            (by simp; positivity) ENNReal.ofReal_ne_top).trans ?_)
          gcongr
          refine (lintegral_lyap_tdPow_le hb hB hD hh0 hh1 x _).trans
            (ENNReal.ofReal_le_ofReal ?_)
          have hp : (1 + c * dyadicStep n) ^ gridIndex n t ≤ Real.exp (c * T') := by
            refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.2 ?_)
            nlinarith
          have hlx : lyap x ≤ |Λ₀| := by
            have := hΛ₀ x hx
            rw [Real.norm_eq_abs, abs_of_pos (lyap_pos x)] at this
            exact this.trans (le_abs_self _)
          calc (1 + c * dyadicStep n) ^ gridIndex n t * lyap x ≤
              Real.exp (c * T') * lyap x :=
                mul_le_mul_of_nonneg_right hp (lyap_pos x).le
            _ ≤ C' := mul_le_mul_of_nonneg_left hlx (by positivity)
        · rw [indicator_of_mem (mem_compl hx)]
          exact prob_le_one.trans le_add_self
    _ = ε / 2 + ρ₀ K₀ᶜ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_one hK₀.isClosed.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

/-! ### The averaged drifts satisfy the hypotheses of `exists_weakFokkerPlanck_time` -/

/-- The averaging window `ε_k = 1 / (k + 1)`. -/
noncomputable def avgEps (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

/-- `0 < ε_k`. -/
theorem avgEps_pos (k : ℕ) : 0 < avgEps k := by unfold avgEps; positivity

/-- `ε_k ≤ 1`. -/
theorem avgEps_le_one (k : ℕ) : avgEps k ≤ 1 := by
  unfold avgEps; exact inv_le_one_of_one_le₀ (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

/-- `ε_k < δ` for all large `k`. -/
theorem eventually_avgEps_lt {δ : ℝ} (hδ : 0 < δ) : ∃ N : ℕ, ∀ k ≥ N, avgEps k < δ := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun k hk => lt_of_le_of_lt ?_ hN⟩
  unfold avgEps
  rw [one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)

section AvgSol

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
  (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
  (hL : ∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (b t))

include hbc in
/-- Slices of the averaged drift are measurable. -/
theorem measurable_timeAvg (ε : ℝ) : ∀ t, Measurable (timeAvg b ε t) := fun t =>
  (continuous_slice (continuous_timeAvg hbc ε) t).measurable

include hbc hL in
/-- **The averaged drift satisfies the local hypotheses of `exists_weakFokkerPlanck_time`:**
on every `[0, T]` it is Lipschitz in `x` uniformly in `t`, and Hölder-`½` in time with linear
weight. -/
theorem timeAvg_hyps {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (timeAvg b ε t)) ∧
    (∀ T, ∃ K : ℝ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
      ‖timeAvg b ε t x - timeAvg b ε s x‖ ≤ K * Real.sqrt |t - s| * (1 + ‖x‖)) := by
  refine ⟨fun T => ?_, fun T => ?_⟩
  · obtain ⟨L, hLT⟩ := hL (T + 1)
    exact ⟨L, fun t ht => lipschitzWith_timeAvg hbc hε hLT ht.1 (by linarith [ht.2])⟩
  · obtain ⟨B, hB0, hB⟩ := exists_linGrowth hbc hL (T + 1)
    refine ⟨2 * ε⁻¹ * B * Real.sqrt T, fun s hs t ht x => ?_⟩
    refine (norm_timeAvg_sub_time_le hbc hε hε1 hB hs ht x).trans ?_
    have h1 : |t - s| ≤ Real.sqrt T * Real.sqrt |t - s| := by
      have hts : |t - s| ≤ T := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      calc |t - s| = Real.sqrt |t - s| * Real.sqrt |t - s| :=
            (Real.mul_self_sqrt (abs_nonneg _)).symm
        _ ≤ Real.sqrt T * Real.sqrt |t - s| :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hts) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ 2 * ε⁻¹ * B * (1 + ‖x‖) := by positivity
    calc 2 * ε⁻¹ * B * (1 + ‖x‖) * |t - s| ≤
        2 * ε⁻¹ * B * (1 + ‖x‖) * (Real.sqrt T * Real.sqrt |t - s|) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 2 * ε⁻¹ * B * Real.sqrt T * Real.sqrt |t - s| * (1 + ‖x‖) := by ring

variable {D : ℝ} (hD : 0 < D) {ρ₀ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ₀]
  {ν : ℕ → ℝ → ProbabilityMeasure (Fin d → ℝ)}

include hbc hL in
/-- Linear growth of all averaged drifts on `[0, T]`, with a constant independent of `k`. -/
theorem exists_linGrowth_timeAvg (T : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ (k : ℕ), ∀ r ∈ Icc 0 T, ∀ x,
      ‖timeAvg b (avgEps k) r x‖ ≤ B * (1 + ‖x‖) ∧ ‖b r x‖ ≤ B * (1 + ‖x‖) := by
  obtain ⟨B, hB0, hB⟩ := exists_linGrowth hbc hL (T + 1)
  refine ⟨B, hB0, fun k r hr x => ⟨norm_timeAvg_le (avgEps_pos k) hB hr.1
    (by linarith [hr.2, avgEps_le_one k]) x, hB r ⟨hr.1, by linarith [hr.2]⟩ x⟩⟩

include hbc hL hD in
/-- **Uniform tightness of the averaged-drift solutions.** If `ν k t` is the weak limit of the
dyadic time-dependent EM laws of `b^{ε_k}` for all `k, t`, then `{ν k t | k, t ≤ T}` is tight. -/
theorem isTight_avgSol
    (htd : ∀ (k : ℕ) t, Tendsto (fun n => tdCurveP (timeAvg b (avgEps k))
      (measurable_timeAvg hbc (avgEps k)) D ρ₀ n t) atTop (𝓝 (ν k t))) (T : ℝ) :
    IsTightMeasureSet {μ | ∃ k : ℕ, ∃ t ≤ T, μ = (ν k t : Measure (Fin d → ℝ))} := by
  set T' := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  obtain ⟨B, -, hB⟩ := exists_linGrowth_timeAvg hbc hL T'
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_tdCurve_family (B := B) hD.le ρ₀ T) ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
  refine ⟨closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro μ ⟨k, t, ht, rfl⟩
  set b₂ : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun s => timeAvg b (avgEps k) (clampTime T' s)
  have hb₂ : ∀ s, Measurable (b₂ s) := fun s => measurable_timeAvg hbc _ _
  have hB₂ : ∀ s y, ‖b₂ s y‖ ≤ B * (1 + ‖y‖) := fun s y =>
    (hB k _ (clampTime_mem hT' s) y).1
  refine measure_compl_closedBall_le_of_tendsto (htd k t) (Eventually.of_forall fun n => ?_)
  refine (measure_mono (compl_subset_compl.2 hR)).trans (hKε _ ⟨b₂, hb₂, hB₂, n, t, ht, ?_⟩)
  exact tdCurve_congr _ hb₂ D ρ₀ n hT' (ht.trans (le_max_left _ _)) fun s hs => by
    simp only [b₂, clampTime_of_mem hs]

include hbc in
/-- **Integrated identity for the averaged-drift solutions on all of `ℝ`.** -/
theorem integral_avgSol_eq
    (hcont : ∀ k, Continuous (ν k))
    (hfp : ∀ k, WeakFokkerPlanck (fun t => (ν k t : Measure (Fin d → ℝ)))
      (timeAvg b (avgEps k)) D)
    (htd : ∀ (k : ℕ) t, Tendsto (fun n => tdCurveP (timeAvg b (avgEps k))
      (measurable_timeAvg hbc (avgEps k)) D ρ₀ n t) atTop (𝓝 (ν k t)))
    (k : ℕ) {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) (t : ℝ) :
    ∫ y, φ y ∂(ν k t : Measure (Fin d → ℝ)) = ∫ y, φ y ∂ρ₀ +
      ∫ r in (0 : ℝ)..max t 0,
        ∫ y, fpGen (timeAvg b (avgEps k) r) D φ y ∂(ν k r : Measure (Fin d → ℝ)) := by
  have h0 : (ν k 0 : Measure (Fin d → ℝ)) = ρ₀ := tdLimit_of_nonpos _ (htd k) le_rfl
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, ← h0]
    exact integral_eq_of_weakFokkerPlanck (continuous_timeAvg hbc _) (hcont k) (hfp k) hφ ht
  · rw [max_eq_right ht, intervalIntegral.integral_same, add_zero,
      tdLimit_of_nonpos _ (htd k) ht]

include hbc hL in
/-- **Local equicontinuity of the averaged-drift solutions.** For `φ ∈ C²_c` and `T` there is
`M` with `|∫ φ dν k t - ∫ φ dν k s| ≤ M |t - s|` for all `k` and all `s, t ≤ T`. -/
theorem abs_integral_avgSol_sub_le
    (hcont : ∀ k, Continuous (ν k))
    (hfp : ∀ k, WeakFokkerPlanck (fun t => (ν k t : Measure (Fin d → ℝ)))
      (timeAvg b (avgEps k)) D)
    (htd : ∀ (k : ℕ) t, Tendsto (fun n => tdCurveP (timeAvg b (avgEps k))
      (measurable_timeAvg hbc (avgEps k)) D ρ₀ n t) atTop (𝓝 (ν k t)))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) (T : ℝ) :
    ∃ M : ℝ, ∀ (k : ℕ) s t, s ≤ T → t ≤ T → |∫ y, φ y ∂(ν k t : Measure (Fin d → ℝ)) -
      ∫ y, φ y ∂(ν k s : Measure (Fin d → ℝ))| ≤ M * |t - s| := by
  set T' := max T 0
  obtain ⟨B, hB0, hB⟩ := exists_linGrowth_timeAvg hbc hL T'
  obtain ⟨Mψ, ML, hMψ0, hML0, hGu⟩ := exists_bound_fpGen_unif hφ D
  set M := B * Mψ + |D| * ML
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, fun k s t hs ht => ?_⟩
  have hGc := continuous_integral_fpGen_curve (continuous_timeAvg hbc (avgEps k)) (hcont k) D hφ
  rw [integral_avgSol_eq hbc hcont hfp htd k hφ t, integral_avgSol_eq hbc hcont hfp htd k hφ s,
    add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (hGc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _), ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun r hr => ?_).trans ?_
  · have hr' : r ∈ Icc 0 T' := by
      rcases mem_uIoc.1 hr with h | h
      · exact ⟨by linarith [h.1, le_max_right s 0], h.2.trans (max_le_max_right 0 ht)⟩
      · exact ⟨by linarith [h.1, le_max_right t 0], h.2.trans (max_le_max_right 0 hs)⟩
    rw [Real.norm_eq_abs]
    exact abs_integral_le_of_abs_le (hGu _ B (fun y => (hB k r hr' y).1))
  · exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs t s 0) hM0

end AvgSol

/-! ### Main theorem -/

/-- **Existence for the weak Fokker–Planck equation, drift continuous in time (Verified, no
Itô input).** Let `b : ℝ → ℝᵈ → ℝᵈ` be jointly continuous in `(t, x)` and, on every bounded
time interval `[0, T]`, Lipschitz in `x` uniformly in `t ∈ [0, T]` (no regularity in time
beyond continuity; linear growth on `[0, T]` is then automatic). Let `D > 0` and `ρ₀` be
**any** probability measure on `Fin d → ℝ`. Then there is a weakly continuous curve
`ν : ℝ → 𝒫(ℝᵈ)` with `ν 0 = ρ₀` solving `WeakFokkerPlanck (fun t => ν t) b D`. `ν` is a weak
limit (along a subsequence, at every time) of solutions for the time-averaged drifts
`b^ε(t, x) = ε⁻¹ ∫₀^ε b(t + u, x) du`, `ε = 1/(k + 1)`. -/
theorem exists_weakFokkerPlanck_continuousTime {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (hL : ∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (b t))
    {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) b D := by
  have hex : ∀ k : ℕ, ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), Continuous ν ∧
      WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (timeAvg b (avgEps k)) D ∧
      ∀ t, Tendsto (fun n => tdCurveP (timeAvg b (avgEps k))
        (measurable_timeAvg hbc (avgEps k)) D ρ₀ n t) atTop (𝓝 (ν t)) := fun k => by
    obtain ⟨h1, h2⟩ := timeAvg_hyps hbc hL (avgEps_pos k) (avgEps_le_one k)
    obtain ⟨ν, -, hc, hfp, htd⟩ := exists_weakFokkerPlanck_time
      (measurable_timeAvg hbc (avgEps k)) h1 h2 hD ρ₀
    exact ⟨ν, hc, hfp, htd⟩
  choose ν hcont hfp htd using hex
  obtain ⟨ψ, hψ, ν', hν'c, hν'⟩ := exists_subseq_tendsto_curve
    (isTight_avgSol hbc hL hD htd) fun φ hφ T => by
      obtain ⟨M, hM⟩ := abs_integral_avgSol_sub_le hbc hL hcont hfp htd hφ T
      exact ⟨M, 0, fun k _ s t hs ht => hM k s t hs ht⟩
  -- initial condition
  have h0 : (ν' 0 : Measure (Fin d → ℝ)) = ρ₀ := by
    have hc : (fun j => ν (ψ j) 0) = fun _ => ⟨ρ₀, inferInstance⟩ := by
      funext j; apply Subtype.ext
      exact tdLimit_of_nonpos _ (htd (ψ j)) le_rfl
    have := tendsto_nhds_unique (hν' 0) (by rw [hc]; exact tendsto_const_nhds)
    rw [this]; rfl
  -- integrated identity for the limit
  have hid : ∀ φ, TestFunction2 φ → ∀ t, 0 ≤ t →
      ∫ y, φ y ∂(ν' t : Measure (Fin d → ℝ)) = ∫ y, φ y ∂ρ₀ +
        ∫ r in (0 : ℝ)..t, ∫ y, fpGen (b r) D φ y ∂(ν' r : Measure (Fin d → ℝ)) := by
    intro φ hφ t ht
    obtain ⟨⟨Mφ, hMφ⟩, -⟩ := testFunction2_bounds hφ
    obtain ⟨B, hB0, hB⟩ := exists_linGrowth_timeAvg hbc hL t
    obtain ⟨Mψ, ML, hMψ0, hML0, hGu⟩ := exists_bound_fpGen_unif hφ D
    obtain ⟨Mψ', hMψ'0, hMψ'⟩ := exists_bound_gradWeight hφ
    set M := B * Mψ + |D| * ML
    have h1 := tendsto_integral_of_tendsto (hν' t) hφ.1.continuous hMφ
    have hpt : ∀ r ∈ Icc 0 t, Tendsto (fun j =>
        ∫ y, fpGen (timeAvg b (avgEps (ψ j)) r) D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ)))
        atTop (𝓝 (∫ y, fpGen (b r) D φ y ∂(ν' r : Measure (Fin d → ℝ)))) := by
      intro r hr
      have hGr : ∀ y, |fpGen (b r) D φ y| ≤ M := hGu _ B fun y => (hB 0 r hr y).2
      have hGk : ∀ k y, |fpGen (timeAvg b (avgEps k) r) D φ y| ≤ M :=
        fun k => hGu _ B fun y => (hB k r hr y).1
      have hcr := continuous_fpGen (continuous_slice hbc r) D hφ.1
      have hH := tendsto_integral_of_tendsto (hν' r) hcr hGr
      have hdiff : Tendsto (fun j =>
          ∫ y, fpGen (timeAvg b (avgEps (ψ j)) r) D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ)) -
          ∫ y, fpGen (b r) D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ))) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        set η := ε / (2 * (Mψ' + 1)) with hηdef
        have hη : 0 < η := by positivity
        obtain ⟨δ, hδ, hconv⟩ := norm_timeAvg_sub_le hbc hφ.2.isCompact r hη
        obtain ⟨N, hN⟩ := eventually_avgEps_lt hδ
        refine ⟨N, fun j hj => ?_⟩
        have hk := hN (ψ j) (hj.trans (le_of_strictMono hψ j))
        have := abs_integral_sub_le_of_abs_le (μ := (ν (ψ j) r : Measure (Fin d → ℝ)))
          (continuous_fpGen (continuous_slice (continuous_timeAvg hbc _) r) D hφ.1) hcr
          (hGk (ψ j)) hGr (abs_fpGen_sub_le_of_tsupport hMψ' D hη.le
            fun y hy => hconv _ (avgEps_pos _) hk y hy)
        rw [Real.dist_eq, sub_zero]
        have hηM : η * Mψ' < ε := by
          rw [hηdef]
          have : ε / (2 * (Mψ' + 1)) * Mψ' = ε / 2 * (Mψ' / (Mψ' + 1)) := by field_simp
          rw [this]
          have : Mψ' / (Mψ' + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
          nlinarith
        linarith
      have := hdiff.add hH
      simp only [sub_add_cancel, zero_add] at this
      exact this
    have h2 : Tendsto (fun j => ∫ r in (0 : ℝ)..t,
        ∫ y, fpGen (timeAvg b (avgEps (ψ j)) r) D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ)))
        atTop (𝓝 (∫ r in (0 : ℝ)..t,
          ∫ y, fpGen (b r) D φ y ∂(ν' r : Measure (Fin d → ℝ)))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
        (Eventually.of_forall fun j => ?_)
        (Eventually.of_forall fun j => ae_of_all _ fun r hr => ?_)
        intervalIntegrable_const (ae_of_all _ fun r hr => ?_)
      · exact (continuous_integral_fpGen_curve (continuous_timeAvg hbc _) (hcont (ψ j)) D
          hφ).aestronglyMeasurable
      · rw [uIoc_of_le ht] at hr
        rw [Real.norm_eq_abs]
        exact abs_integral_le_of_abs_le
          (hGu _ B fun y => (hB (ψ j) r ⟨hr.1.le, hr.2⟩ y).1)
      · rw [uIoc_of_le ht] at hr
        exact hpt r ⟨hr.1.le, hr.2⟩
    have h3 : ∀ j, ∫ y, φ y ∂ρ₀ + ∫ r in (0 : ℝ)..t,
        ∫ y, fpGen (timeAvg b (avgEps (ψ j)) r) D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ)) =
        ∫ y, φ y ∂(ν (ψ j) t : Measure (Fin d → ℝ)) := fun j => by
      rw [integral_avgSol_eq hbc hcont hfp htd (ψ j) hφ t, max_eq_left ht]
    exact tendsto_nhds_unique h1 ((h2.const_add _).congr h3)
  refine ⟨ν', h0, hν'c, fun φ hφ t ht => ?_⟩
  have hGc := continuous_integral_fpGen_curve hbc hν'c D hφ
  have hd := ((hGc.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt
    (s := Ici 0)).const_add (∫ y, φ y ∂ρ₀)
  exact hd.congr_of_mem (fun s hs => hid φ hφ s (mem_Ici.1 hs)) ht

/-- **Measure-curve form, drift continuous in time.** Under the hypotheses of
`exists_weakFokkerPlanck_continuousTime`, there is `ρ : ℝ → Measure (Fin d → ℝ)` with
`ρ 0 = ρ₀`, every `ρ t` a probability measure and `WeakFokkerPlanck ρ b D`. -/
theorem exists_weakFokkerPlanck_continuousTime_measure {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (hL : ∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (b t))
    {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ b D := by
  obtain ⟨ν, h0, -, hfp⟩ := exists_weakFokkerPlanck_continuousTime hbc hL hD ρ₀
  exact ⟨fun t => ν t, h0, fun t => inferInstance, hfp⟩

end FormalizeSampling.FokkerPlanckExistence
