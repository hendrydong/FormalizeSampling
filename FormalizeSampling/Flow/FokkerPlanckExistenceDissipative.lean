module

public import FormalizeSampling.Flow.FokkerPlanckExistenceExtract
public import FormalizeSampling.Flow.FokkerPlanckExistenceLinear

/-!
# Existence for the weak Fokker–Planck equation: dissipative, locally Lipschitz drifts

Status: **Verified.** Removes the global Lipschitz (linear growth) assumption of
`Flow/FokkerPlanckExistenceLinear.lean`. For an autonomous drift `b : ℝᵈ → ℝᵈ` that is
**locally Lipschitz** (Mathlib's `LocallyLipschitz`, e.g. `C¹`) and satisfies the
**dissipativity (Lyapunov) condition**

  `⟪x, b x⟫ ≤ C (1 + |x|²)`   (Euclidean: `x ⬝ᵥ b x ≤ C (1 + x ⬝ᵥ x)`),

a diffusion constant `D > 0` and an **arbitrary** probability measure `ρ₀` (no moment
assumption), there is a weakly continuous curve of probability measures `ν` with `ν 0 = ρ₀`
solving `WeakFokkerPlanck (ν ·) (fun _ => b) D` (`exists_weakFokkerPlanck_dissipative`). This
covers superlinear drifts such as `b = -∇U` with `U(x) = |x|⁴` or a double well
`U(x) = |x|⁴ - a |x|²` (`exists_weakFokkerPlanck_langevin_dissipative`,
`exists_weakFokkerPlanck_langevin_contDiff`, and the explicit instance
`exists_weakFokkerPlanck_doubleWell`), for which explicit Euler–Maruyama diverges.

## Construction (no limit in Euler–Maruyama for the superlinear drift itself)

1. **Truncation** (`truncDrift`): `b_R = χ_R • b` with the Lipschitz cut-off
   `χ_R(x) = max 0 (min 1 (R + 1 - ‖x‖))` (sup norm), `χ_R = 1` on `‖x‖ ≤ R`, `χ_R = 0` on
   `‖x‖ ≥ R + 1`. `b_R` is globally Lipschitz and bounded (`lipschitzWith_truncDrift`,
   `exists_bound_truncDrift`), equals `b` on the ball of radius `R` (`truncDrift_eq`), and —
   because `0 ≤ χ_R ≤ 1` — is dissipative with the **same** constant `max C 0`
   (`dotProduct_truncDrift_le`).
2. **Truncated solutions**: `exists_weakFokkerPlanck_lipschitz` (globally Lipschitz drift) gives
   solutions `ν^R`, weak limits of the dyadic EM laws for `b_R`.
3. **Uniform Lyapunov bound**: one EM step with a dissipative drift satisfies
   `E lyap(Y) ≤ (1 + c h) lyap(y)`, `lyap = 1 + |·|²`, `c = 2C + 2dD + 1`, as soon as
   `h d ‖b‖² ≤ 1` (`lintegral_lyap_emStep_diss`). The constant does not depend on `R`; the
   step condition holds for all fine dyadic levels, so the tightness of the EM laws
   (`isTightMeasureSet_emCurve_diss`) passes to `{ν^R_t | R ∈ ℕ, t ≤ T}`
   (`isTight_truncSol`), with no moment assumption on `ρ₀`.
4. **Equicontinuity**: `|b_R| ≤ |b|` (`norm_truncDrift_le_norm`), so
   `|∫ φ dν^R_t - ∫ φ dν^R_s| ≤ C_φ |t - s|` uniformly in `R` for every `φ ∈ C²_c`
   (`abs_integral_truncSol_sub_le`).
5. **Extraction** (`exists_subseq_tendsto_curve`, `Flow/FokkerPlanckExistenceExtract.lean`):
   a subsequence converges weakly at every time to a weakly continuous `ν`.
6. **Passage to the limit**: for `φ ∈ C²_c`, `b_R ⬝ ∇φ = b ⬝ ∇φ` once the support of `φ` lies
   in the ball of radius `R`; dominated convergence in time gives the integrated identity for
   `ν`, hence `WeakFokkerPlanck`.

## Not proved here

* Uniqueness of the solution (for continuous bounded drifts see
  `Flow/FokkerPlanckUniqueness.lean`; nothing is claimed for superlinear drifts), nor that the
  whole family `ν^R` (rather than a subsequence) converges.
* Identification with the law of an SDE (no SDE theory); moment bounds for the limit beyond
  tightness; time-dependent dissipative drifts (time-dependent globally Lipschitz drifts are in
  `Flow/FokkerPlanckExistenceTime.lean` and `Flow/FokkerPlanckExistenceContinuousTime.lean`).
* Convergence of the explicit Euler–Maruyama scheme for `b` itself (false in general for
  superlinear drifts).
* `D = 0`; non-constant diffusion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence
open FormalizeSampling.HeatKernelPi FormalizeSampling.WeakFokkerPlanckOU NoiseScore

variable {d : ℕ}

/-! ### The cut-off and the truncated drift -/

/-- The Lipschitz cut-off `χ_R(x) = max 0 (min 1 (R + 1 - ‖x‖))` (sup norm): `1` on the ball
of radius `R`, `0` outside the ball of radius `R + 1`, values in `[0, 1]`. -/
noncomputable def cutoff (R : ℝ) (x : Fin d → ℝ) : ℝ := max 0 (min 1 (R + 1 - ‖x‖))

/-- `0 ≤ χ_R`. -/
theorem cutoff_nonneg (R : ℝ) (x : Fin d → ℝ) : 0 ≤ cutoff R x := le_max_left _ _

/-- `χ_R ≤ 1`. -/
theorem cutoff_le_one (R : ℝ) (x : Fin d → ℝ) : cutoff R x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- `χ_R = 1` on the ball of radius `R`. -/
theorem cutoff_eq_one {R : ℝ} {x : Fin d → ℝ} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  unfold cutoff; rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- `χ_R = 0` outside the ball of radius `R + 1`. -/
theorem cutoff_eq_zero {R : ℝ} {x : Fin d → ℝ} (hx : R + 1 ≤ ‖x‖) : cutoff R x = 0 := by
  unfold cutoff; exact max_eq_left (min_le_of_right_le (by linarith))

/-- `χ_R` is `1`-Lipschitz: `|χ_R x - χ_R y| ≤ ‖x - y‖`. -/
theorem abs_cutoff_sub_le (R : ℝ) (x y : Fin d → ℝ) :
    |cutoff R x - cutoff R y| ≤ ‖x - y‖ := by
  unfold cutoff
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero]
  refine max_le (norm_nonneg _) ?_
  rw [show R + 1 - ‖x‖ - (R + 1 - ‖y‖) = ‖y‖ - ‖x‖ by ring, abs_sub_comm]
  exact abs_norm_sub_norm_le x y

/-- The **truncated drift** `b_R = χ_R • b`. -/
noncomputable def truncDrift (b : (Fin d → ℝ) → Fin d → ℝ) (R : ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ :=
  cutoff R x • b x

/-- `b_R = b` on the ball of radius `R`. -/
theorem truncDrift_eq {b : (Fin d → ℝ) → Fin d → ℝ} {R : ℝ} {x : Fin d → ℝ} (hx : ‖x‖ ≤ R) :
    truncDrift b R x = b x := by
  rw [truncDrift, cutoff_eq_one hx, one_smul]

/-- `‖b_R x‖ ≤ ‖b x‖`. -/
theorem norm_truncDrift_le_norm (b : (Fin d → ℝ) → Fin d → ℝ) (R : ℝ) (x : Fin d → ℝ) :
    ‖truncDrift b R x‖ ≤ ‖b x‖ := by
  rw [truncDrift, norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg R x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R x)

/-- **The truncated drift is dissipative with the same constant.** If
`x ⬝ᵥ b x ≤ C (1 + x ⬝ᵥ x)` for all `x`, then `x ⬝ᵥ b_R x ≤ max C 0 (1 + x ⬝ᵥ x)`. -/
theorem dotProduct_truncDrift_le {b : (Fin d → ℝ) → Fin d → ℝ} {C : ℝ}
    (hdiss : ∀ x, x ⬝ᵥ b x ≤ C * (1 + x ⬝ᵥ x)) (R : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ truncDrift b R x ≤ max C 0 * (1 + x ⬝ᵥ x) := by
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have h1 : x ⬝ᵥ b x ≤ max C 0 * (1 + x ⬝ᵥ x) :=
    (hdiss x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  have h2 : 0 ≤ max C 0 * (1 + x ⬝ᵥ x) := mul_nonneg (le_max_right _ _) (by linarith)
  rw [truncDrift, dotProduct_smul, smul_eq_mul]
  have hc0 := cutoff_nonneg R x
  have hc1 := cutoff_le_one R x
  nlinarith [mul_nonneg hc0 (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hc1) h2]

/-- A locally Lipschitz map is bounded and Lipschitz on every closed ball. -/
theorem exists_lipschitzOnWith_closedBall {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : LocallyLipschitz b) (r : ℝ) :
    ∃ L : ℝ≥0, ∃ B : ℝ, 0 ≤ B ∧ LipschitzOnWith L b (closedBall 0 r) ∧
      ∀ x ∈ closedBall (0 : Fin d → ℝ) r, ‖b x‖ ≤ B := by
  obtain ⟨L, hL⟩ := hb.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Fin d → ℝ) r)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin d → ℝ) r).exists_bound_of_continuousOn
    hb.continuous.continuousOn
  exact ⟨L, max B 0, le_max_right _ _, hL, fun x hx => (hB x hx).trans (le_max_left _ _)⟩

/-- **The truncated drift is bounded.** -/
theorem exists_bound_truncDrift {b : (Fin d → ℝ) → Fin d → ℝ} (hb : LocallyLipschitz b)
    (R : ℝ) : ∃ B : ℝ, ∀ x, ‖truncDrift b R x‖ ≤ B := by
  obtain ⟨-, B, hB0, -, hB⟩ := exists_lipschitzOnWith_closedBall hb (R + 1)
  refine ⟨B, fun x => ?_⟩
  by_cases hx : x ∈ closedBall (0 : Fin d → ℝ) (R + 1)
  · exact (norm_truncDrift_le_norm b R x).trans (hB x hx)
  · have : R + 1 ≤ ‖x‖ := by simp only [mem_closedBall, dist_zero_right, not_le] at hx; linarith
    rw [truncDrift, cutoff_eq_zero this, zero_smul, norm_zero]; exact hB0

/-- **The truncated drift is globally Lipschitz.** -/
theorem lipschitzWith_truncDrift {b : (Fin d → ℝ) → Fin d → ℝ} (hb : LocallyLipschitz b)
    (R : ℝ) : ∃ L : ℝ≥0, LipschitzWith L (truncDrift b R) := by
  obtain ⟨L, B, hB0, hL, hB⟩ := exists_lipschitzOnWith_closedBall hb (R + 1)
  set S := closedBall (0 : Fin d → ℝ) (R + 1)
  have hout : ∀ y, y ∉ S → truncDrift b R y = 0 := fun y hy => by
    have : R + 1 ≤ ‖y‖ := by simp only [S, mem_closedBall, dist_zero_right, not_le] at hy; linarith
    rw [truncDrift, cutoff_eq_zero this, zero_smul]
  have key : ∀ x ∈ S, ∀ y, ‖truncDrift b R x - truncDrift b R y‖ ≤ (L + B) * ‖x - y‖ := by
    intro x hx y
    have hc := abs_cutoff_sub_le R x y
    by_cases hy : y ∈ S
    · have e : truncDrift b R x - truncDrift b R y =
          cutoff R x • (b x - b y) + (cutoff R x - cutoff R y) • b y := by
        simp only [truncDrift, smul_sub, sub_smul]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (cutoff_nonneg R x)]
      have h1 : ‖b x - b y‖ ≤ L * ‖x - y‖ := by
        have := hL.dist_le_mul x hx y hy; rwa [dist_eq_norm, dist_eq_norm] at this
      have h2 := hB y hy
      have hc1 := cutoff_le_one R x
      have hc0 := cutoff_nonneg R x
      nlinarith [mul_le_mul hc h2 (norm_nonneg _) (norm_nonneg _),
        mul_le_mul hc1 h1 (norm_nonneg _) zero_le_one, norm_nonneg (x - y),
        mul_nonneg hc0 (norm_nonneg (b x - b y))]
    · rw [hout y hy, sub_zero]
      have e : truncDrift b R x = (cutoff R x - cutoff R y) • b x := by
        have : R + 1 ≤ ‖y‖ := by
          simp only [S, mem_closedBall, dist_zero_right, not_le] at hy; linarith
        rw [truncDrift, cutoff_eq_zero this, sub_zero]
      rw [e, norm_smul, Real.norm_eq_abs]
      have h2 := hB x hx
      nlinarith [mul_le_mul hc h2 (norm_nonneg _) (norm_nonneg _), norm_nonneg (x - y),
        L.coe_nonneg, mul_nonneg L.coe_nonneg (norm_nonneg (x - y))]
  refine ⟨L + B.toNNReal, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  push_cast
  rw [Real.coe_toNNReal _ hB0]
  by_cases hx : x ∈ S
  · exact key x hx y
  · by_cases hy : y ∈ S
    · rw [norm_sub_rev, norm_sub_rev x]; exact key y hy x
    · rw [hout x hx, hout y hy, sub_zero, norm_zero]
      exact mul_nonneg (by positivity) (norm_nonneg _)

/-! ### Lyapunov estimate for one Euler–Maruyama step with a dissipative drift -/

/-- `lyap x = 1 + x ⬝ᵥ x`. -/
theorem lyap_eq_dotProduct (x : Fin d → ℝ) : lyap x = 1 + x ⬝ᵥ x := by
  simp [lyap, sqDist, dotProduct, sq]

/-- **One-step Lyapunov estimate under dissipativity.** If `y ⬝ᵥ b y ≤ C lyap y`, `D ≥ 0`,
`h ≥ 0` and the step condition `h d ‖b y‖² ≤ 1`, then
`E lyap(Y) ≤ (1 + (2C + 2dD + 1) h) lyap(y)` for `Y ∼ emStep b hb D h y`. The constant does not
depend on any bound for `b`. -/
theorem lintegral_lyap_emStep_diss {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b)
    {C D h : ℝ} (hD : 0 ≤ D) (hh0 : 0 ≤ h) {y : Fin d → ℝ}
    (hy : y ⬝ᵥ b y ≤ C * lyap y) (hs : h * (d * ‖b y‖ ^ 2) ≤ 1) :
    ∫⁻ z, ENNReal.ofReal (lyap z) ∂(emStep b hb D h y) ≤
      ENNReal.ofReal ((1 + (2 * C + 2 * d * D + 1) * h) * lyap y) := by
  have e1 : ∀ z : Fin d → ℝ, ENNReal.ofReal (lyap z) = 1 + ENNReal.ofReal (sqDist 0 z) := by
    intro z
    rw [lyap, ENNReal.ofReal_add zero_le_one (sqDist_nonneg' 0 z), ENNReal.ofReal_one]
  simp_rw [e1]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, emStep,
    Kernel.comap_apply, heatKernelPi_apply, lintegral_sqDist_pi, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun i _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv : ((stepVar D h : ℝ≥0) : ℝ) = 2 * D * h := by
    rw [stepVar, Real.coe_toNNReal _ (by positivity)]
  rw [hv]
  have e : ∀ i, ((y + h • b y) i - (0 : Fin d → ℝ) i) ^ 2 + 2 * D * h =
      (y i - (0 : Fin d → ℝ) i) ^ 2 + 2 * h * (y i * b y i) + h ^ 2 * (b y i) ^ 2 +
        2 * D * h := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hS : ∑ i, (y i - (0 : Fin d → ℝ) i) ^ 2 = sqDist 0 y := rfl
  have hdot : ∑ i, y i * b y i = y ⬝ᵥ b y := rfl
  rw [hS, hdot]
  have hQ : ∑ i, (b y i) ^ 2 ≤ d * ‖b y‖ ^ 2 := by
    have : ∀ i ∈ Finset.univ, (b y i) ^ 2 ≤ ‖b y‖ ^ 2 := fun i _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm (b y) i) 2
    have := Finset.sum_le_sum this
    simpa using this
  have hQ' : h ^ 2 * ∑ i, (b y i) ^ 2 ≤ h := by
    have := mul_le_mul_of_nonneg_left hQ (sq_nonneg h)
    nlinarith
  have hS0 := sqDist_nonneg' 0 y
  have hly : lyap y = 1 + sqDist 0 y := rfl
  rw [hly] at hy ⊢
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * h),
    mul_nonneg (mul_nonneg (mul_nonneg hd0 hD) hh0) hS0, mul_nonneg hh0 hS0]

/-- **Lyapunov bound along the chain.** Under the hypotheses of `lintegral_lyap_emStep_diss`
at every point: `E lyap(X_k) ≤ (1 + c h)^k lyap(x)`, `c = 2C + 2dD + 1`, `X_k ∼ emPow k x`. -/
theorem lintegral_lyap_emPow_diss {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b)
    {C D h : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hy : ∀ y, y ⬝ᵥ b y ≤ C * lyap y)
    (hs : ∀ y, h * (d * ‖b y‖ ^ 2) ≤ 1) (x : Fin d → ℝ) (k : ℕ) :
    ∫⁻ z, ENNReal.ofReal (lyap z) ∂(emPow b hb D h k x) ≤
      ENNReal.ofReal ((1 + (2 * C + 2 * d * D + 1) * h) ^ k * lyap x) := by
  have hm : Measurable fun z : Fin d → ℝ => ENNReal.ofReal (lyap z) :=
    ENNReal.measurable_ofReal.comp continuous_lyap.measurable
  set c := 2 * C + 2 * d * D + 1
  have hc : 0 ≤ 1 + c * h := by positivity
  induction k with
  | zero =>
    simp only [emPow, Kernel.id_apply]
    rw [lintegral_dirac' _ hm]
    simp
  | succ k ih =>
    show ∫⁻ z, ENNReal.ofReal (lyap z) ∂((emStep b hb D h ∘ₖ emPow b hb D h k) x) ≤ _
    rw [Kernel.lintegral_comp _ _ _ hm]
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (1 + c * h) * ENNReal.ofReal (lyap y)
          ∂(emPow b hb D h k x) := by
          refine lintegral_mono fun y => ?_
          refine (lintegral_lyap_emStep_diss hb hD hh0 (hy y) (hs y)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul hc]
      _ = ENNReal.ofReal (1 + c * h) *
            ∫⁻ y, ENNReal.ofReal (lyap y) ∂(emPow b hb D h k x) := lintegral_const_mul _ hm
      _ ≤ ENNReal.ofReal (1 + c * h) * ENNReal.ofReal ((1 + c * h) ^ k * lyap x) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hc, pow_succ]; ring_nf

/-- **Tightness of EM laws, uniformly over dissipative drifts.** Fix `C ≥ 0`, `D ≥ 0`, a
probability measure `ρ₀` and `T`. The dyadic EM laws `emCurve b hb D ρ₀ n t` over **all**
measurable drifts `b` with `y ⬝ᵥ b y ≤ C lyap y`, all levels `n` with `2⁻ⁿ d ‖b‖² ≤ 1`, and all
times `t ≤ T` form a tight set. -/
theorem isTightMeasureSet_emCurve_diss {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (T : ℝ) :
    IsTightMeasureSet {μ | ∃ b : (Fin d → ℝ) → Fin d → ℝ, ∃ hb : Measurable b, ∃ n : ℕ,
      ∃ t ≤ T, (∀ y, y ⬝ᵥ b y ≤ C * lyap y) ∧ (∀ y, dyadicStep n * (d * ‖b y‖ ^ 2) ≤ 1) ∧
        μ = emCurve b hb D ρ₀ n t} := by
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
  set c := 2 * C + 2 * d * D + 1 with hcdef
  have hc0 : 0 ≤ c := by positivity
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
  rintro μ ⟨b, hb, n, t, ht, hy, hs, rfl⟩
  have hh0 : 0 ≤ dyadicStep n := (dyadicStep_pos n).le
  have hT := dyadic_grid_bound n ht
  have hsub : (closedBall (0 : Fin d → ℝ) r)ᶜ ⊆
      {z | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (lyap z)} := by
    intro z hz
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
    have := one_add_sq_norm_le_lyap z
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  unfold emCurve
  rw [Measure.bind_apply measurableSet_closedBall.compl (Kernel.aemeasurable _)]
  calc ∫⁻ x, emPow b hb D (dyadicStep n) (gridIndex n t) x (closedBall 0 r)ᶜ ∂ρ₀
      ≤ ∫⁻ x, (ε / 2 + K₀ᶜ.indicator 1 x) ∂ρ₀ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K₀
        · refine le_trans ?_ (hCr.trans le_self_add)
          refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
            (ENNReal.measurable_ofReal.comp continuous_lyap.measurable).aemeasurable
            (by simp; positivity) ENNReal.ofReal_ne_top).trans ?_)
          gcongr
          refine (lintegral_lyap_emPow_diss hb hC hD hh0 hy hs x _).trans
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

/-! ### Solutions for the truncated drifts: uniform estimates -/

/-- The truncated drift is continuous (`b` locally Lipschitz). -/
theorem continuous_truncDrift {b : (Fin d → ℝ) → Fin d → ℝ} (hb : LocallyLipschitz b)
    (R : ℝ) : Continuous (truncDrift b R) := by
  obtain ⟨L, hL⟩ := lipschitzWith_truncDrift hb R
  exact hL.continuous

/-- **Uniform generator bound.** For continuous `b` and `φ ∈ C²_c` there is `M` with
`|b_R ⬝ ∇φ + D Δφ| ≤ M` for **all** `R` (because `0 ≤ χ_R ≤ 1`). -/
theorem exists_bound_fpGen_truncDrift {b : (Fin d → ℝ) → Fin d → ℝ} (hbc : Continuous b)
    (D : ℝ) {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    ∃ M, 0 ≤ M ∧ ∀ R y, |fpGen (truncDrift b R) D φ y| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := exists_bound_fpGen hbc D hφ
  obtain ⟨M₂, hM₂⟩ := exists_bound_fpGen (b := fun _ => (0 : Fin d → ℝ)) continuous_const D hφ
  have h10 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ 0)
  have h20 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  refine ⟨M₁ + M₂, by positivity, fun R y => ?_⟩
  have e : fpGen (truncDrift b R) D φ y = cutoff R y * fpGen b D φ y +
      (1 - cutoff R y) * fpGen (fun _ => (0 : Fin d → ℝ)) D φ y := by
    simp only [fpGen, truncDrift, smul_dotProduct, zero_dotProduct, smul_eq_mul]; ring
  have hc0 := cutoff_nonneg R y
  have hc1 := cutoff_le_one R y
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg (sub_nonneg.2 hc1)]
  nlinarith [mul_le_mul_of_nonneg_left (hM₁ y) hc0,
    mul_le_mul_of_nonneg_left (hM₂ y) (sub_nonneg.2 hc1)]

/-- **Locality of the generator.** If the support of `φ` lies in the ball of radius `R`, the
generators of `b_R` and `b` agree on `φ`. -/
theorem fpGen_truncDrift_eq {b : (Fin d → ℝ) → Fin d → ℝ} {R : ℝ} (D : ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hR : tsupport φ ⊆ closedBall 0 R) :
    fpGen (truncDrift b R) D φ = fpGen b D φ := by
  funext y
  by_cases hy : y ∈ tsupport φ
  · have : ‖y‖ ≤ R := by simpa using hR hy
    simp only [fpGen, truncDrift_eq this]
  · have hg : grad φ y = 0 := funext fun i => by
      show partialDeriv i φ y = 0
      exact image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_partialDeriv_subset i φ h)
    simp only [fpGen, hg, dotProduct_zero]

section Truncated

variable {b : (Fin d → ℝ) → Fin d → ℝ} (hb : LocallyLipschitz b) {C : ℝ}
  (hdiss : ∀ x, x ⬝ᵥ b x ≤ C * (1 + x ⬝ᵥ x)) {D : ℝ} (hD : 0 < D)
  {ρ₀ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ₀]
  {ν : ℕ → ℝ → ProbabilityMeasure (Fin d → ℝ)}

include hb hdiss hD in
/-- **Uniform tightness of the truncated solutions.** If `ν R t` is the weak limit of the
dyadic EM laws of the truncated drift `b_R` (for every `R ∈ ℕ` and `t`), then
`{ν R t | R ∈ ℕ, t ≤ T}` is tight for every `T`. -/
theorem isTight_truncSol
    (hν : ∀ (R : ℕ) t, Tendsto (fun n => emCurveP (truncDrift b R)
      (continuous_truncDrift hb R).measurable D ρ₀ n t) atTop (𝓝 (ν R t))) (T : ℝ) :
    IsTightMeasureSet {μ | ∃ R : ℕ, ∃ t ≤ T, μ = (ν R t : Measure (Fin d → ℝ))} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_emCurve_diss (C := max C 0) (le_max_right _ _) hD.le ρ₀ T) ε hε
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
  refine ⟨closedBall 0 R₀, isCompact_closedBall 0 R₀, ?_⟩
  rintro μ ⟨R, t, ht, rfl⟩
  obtain ⟨B, hB⟩ := exists_bound_truncDrift hb (R : ℝ)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hdy : Tendsto (fun n => dyadicStep n * (d * B ^ 2)) atTop (𝓝 0) := by
    have h0 : Tendsto dyadicStep atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h0.mul_const (d * B ^ 2)
  have ev : ∀ᶠ n in atTop, dyadicStep n * (d * B ^ 2) ≤ 1 :=
    hdy.eventually (ge_mem_nhds zero_lt_one)
  refine measure_compl_closedBall_le_of_tendsto (hν R t) (ev.mono fun n hn => ?_)
  refine (measure_mono (compl_subset_compl.2 hR₀)).trans (hKε _ ⟨truncDrift b R,
    (continuous_truncDrift hb R).measurable, n, t, ht, fun y => ?_, fun y => ?_, rfl⟩)
  · rw [lyap_eq_dotProduct]; exact dotProduct_truncDrift_le hdiss R y
  · have h1 : ‖truncDrift b R y‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB y) 2
    have h2 := (dyadicStep_pos n).le
    have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc dyadicStep n * (d * ‖truncDrift b R y‖ ^ 2) ≤ dyadicStep n * (d * B ^ 2) := by gcongr
      _ ≤ 1 := hn

/-- The truncated solutions as limits of the time-dependent dyadic laws of the constant drift
family `fun _ => b_R` (`emCurveP_eq_tdCurveP`). -/
theorem tendsto_tdCurveP_truncSol
    (hν : ∀ (R : ℕ) t, Tendsto (fun n => emCurveP (truncDrift b R)
      (continuous_truncDrift hb R).measurable D ρ₀ n t) atTop (𝓝 (ν R t))) (R : ℕ) (t : ℝ) :
    Tendsto (fun n => tdCurveP (fun _ => truncDrift b R)
      (fun _ => (continuous_truncDrift hb R).measurable) D ρ₀ n t) atTop (𝓝 (ν R t)) :=
  (hν R t).congr fun n => emCurveP_eq_tdCurveP _ _ D ρ₀ n t

include hb hD in
/-- **Integrated identity for the truncated solutions.** Under the hypotheses of
`isTight_truncSol`, `∫ φ dν R t = ∫ φ dρ₀ + ∫₀^{max t 0} ∫ (b_R ⬝ ∇φ + D Δφ) dν R r dr`, and
`r ↦ ∫ g dν R r` is continuous for bounded continuous `g`. -/
theorem integral_truncSol_eq
    (hν : ∀ (R : ℕ) t, Tendsto (fun n => emCurveP (truncDrift b R)
      (continuous_truncDrift hb R).measurable D ρ₀ n t) atTop (𝓝 (ν R t)))
    (R : ℕ) {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) (t : ℝ) :
    ∫ y, φ y ∂(ν R t : Measure (Fin d → ℝ)) = ∫ y, φ y ∂ρ₀ +
      ∫ r in (0 : ℝ)..max t 0,
        ∫ y, fpGen (truncDrift b R) D φ y ∂(ν R r : Measure (Fin d → ℝ)) := by
  obtain ⟨L, hL⟩ := lipschitzWith_truncDrift hb (R : ℝ)
  exact integral_tdLimit_eq _ (fun _ => hL) (fun _ => norm_le_of_lipschitzWith hL) (K := 0)
    (fun _ _ _ => by simp) hD ρ₀ (tendsto_tdCurveP_truncSol hb hν R) hφ t

include hb hD in
/-- The truncated solutions are weakly continuous in time. -/
theorem continuous_truncSol
    (hν : ∀ (R : ℕ) t, Tendsto (fun n => emCurveP (truncDrift b R)
      (continuous_truncDrift hb R).measurable D ρ₀ n t) atTop (𝓝 (ν R t))) (R : ℕ) :
    Continuous (ν R) := by
  obtain ⟨L, hL⟩ := lipschitzWith_truncDrift hb (R : ℝ)
  exact continuous_tdLimit _ (fun _ => hL) (fun _ => norm_le_of_lipschitzWith hL) (K := 0)
    (fun _ _ _ => by simp) hD ρ₀ (tendsto_tdCurveP_truncSol hb hν R)

include hb hD in
/-- **Equicontinuity of the truncated solutions.** For `φ ∈ C²_c` there is `M` with
`|∫ φ dν R t - ∫ φ dν R s| ≤ M |t - s|` for all `R ∈ ℕ` and all `s, t`. -/
theorem abs_integral_truncSol_sub_le
    (hν : ∀ (R : ℕ) t, Tendsto (fun n => emCurveP (truncDrift b R)
      (continuous_truncDrift hb R).measurable D ρ₀ n t) atTop (𝓝 (ν R t)))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    ∃ M : ℝ, ∀ (R : ℕ) s t, |∫ y, φ y ∂(ν R t : Measure (Fin d → ℝ)) -
      ∫ y, φ y ∂(ν R s : Measure (Fin d → ℝ))| ≤ M * |t - s| := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fpGen_truncDrift hb.continuous D hφ
  refine ⟨M, fun R s t => ?_⟩
  have hGc : Continuous fun r =>
      ∫ y, fpGen (truncDrift b R) D φ y ∂(ν R r : Measure (Fin d → ℝ)) :=
    (continuous_integral_of_abs_le (continuous_fpGen (continuous_truncDrift hb R) D hφ.1)
      (hM R)).comp (continuous_truncSol hb hD hν R)
  rw [integral_truncSol_eq hb hD hν R hφ t, integral_truncSol_eq hb hD hν R hφ s,
    add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (hGc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _), ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun r _ => ?_).trans ?_
  · rw [Real.norm_eq_abs]; exact abs_integral_le_of_abs_le (hM R)
  · exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs t s 0) hM0

end Truncated

/-! ### Main theorems -/

/-- **Existence for the weak Fokker–Planck equation, dissipative locally Lipschitz drift
(Verified, no Itô input).** Let `b : ℝᵈ → ℝᵈ` be locally Lipschitz (`LocallyLipschitz b`, e.g.
`C¹`; no growth bound) and dissipative, `x ⬝ᵥ b x ≤ C (1 + x ⬝ᵥ x)` for all `x` (Euclidean inner
product and norm; any `C : ℝ`), let `D > 0` and let `ρ₀` be **any** probability measure on
`Fin d → ℝ`. There is a weakly continuous curve `ν : ℝ → 𝒫(ℝᵈ)` with `ν 0 = ρ₀` solving
`WeakFokkerPlanck (fun t => ν t) (fun _ => b) D`, i.e.
`d/dt ∫ φ dν_t = ∫ (b ⬝ ∇φ + D Δφ) dν_t` on `t ≥ 0` for every `φ ∈ C²_c`. `ν` is a weak limit
(along a subsequence, at every time) of the solutions for the truncated drifts `χ_R • b`. -/
theorem exists_weakFokkerPlanck_dissipative {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : LocallyLipschitz b) {C : ℝ} (hdiss : ∀ x, x ⬝ᵥ b x ≤ C * (1 + x ⬝ᵥ x)) {D : ℝ}
    (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (fun _ => b) D := by
  have hex : ∀ R : ℕ, ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), ∀ t,
      Tendsto (fun n => emCurveP (truncDrift b R) (continuous_truncDrift hb R).measurable D ρ₀
        n t) atTop (𝓝 (ν t)) := fun R => by
    obtain ⟨L, hL⟩ := lipschitzWith_truncDrift hb (R : ℝ)
    obtain ⟨ν, -, -, -, hν⟩ := exists_weakFokkerPlanck_lipschitz hL hD ρ₀
    exact ⟨ν, hν⟩
  choose ν hν using hex
  obtain ⟨ψ, hψ, ν', hν'c, hν'⟩ := exists_subseq_tendsto_curve
    (isTight_truncSol hb hdiss hD hν) fun φ hφ => by
      obtain ⟨M, hM⟩ := abs_integral_truncSol_sub_le hb hD hν hφ
      exact fun _ => ⟨M, 0, fun k _ s t _ _ => hM k s t⟩
  -- initial condition
  have h0 : (ν' 0 : Measure (Fin d → ℝ)) = ρ₀ := by
    have hc : (fun j => ν (ψ j) 0) = fun _ => ⟨ρ₀, inferInstance⟩ := by
      funext j; apply Subtype.ext
      exact tdLimit_of_nonpos _ (tendsto_tdCurveP_truncSol hb hν (ψ j)) le_rfl
    have := tendsto_nhds_unique (hν' 0) (by rw [hc]; exact tendsto_const_nhds)
    rw [this]; rfl
  -- integrated identity for the limit
  have hid : ∀ φ, TestFunction2 φ → ∀ t, 0 ≤ t →
      ∫ y, φ y ∂(ν' t : Measure (Fin d → ℝ)) = ∫ y, φ y ∂ρ₀ +
        ∫ r in (0 : ℝ)..t, ∫ y, fpGen b D φ y ∂(ν' r : Measure (Fin d → ℝ)) := by
    intro φ hφ t ht
    obtain ⟨⟨Mφ, hMφ⟩, -⟩ := testFunction2_bounds hφ
    obtain ⟨MG, hMG⟩ := exists_bound_fpGen hb.continuous D hφ
    have hGc := continuous_fpGen hb.continuous D hφ.1
    obtain ⟨Rφ, hRφ⟩ := hφ.2.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
    have h1 := tendsto_integral_of_tendsto (hν' t) hφ.1.continuous hMφ
    have h2 : Tendsto (fun j => ∫ r in (0 : ℝ)..t,
        ∫ y, fpGen b D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ))) atTop
        (𝓝 (∫ r in (0 : ℝ)..t, ∫ y, fpGen b D φ y ∂(ν' r : Measure (Fin d → ℝ)))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => MG)
        (Eventually.of_forall fun j => ?_)
        (Eventually.of_forall fun j => ae_of_all _ fun r _ => ?_)
        intervalIntegrable_const (ae_of_all _ fun r _ => ?_)
      · exact ((continuous_integral_of_abs_le hGc hMG).comp
          (continuous_truncSol hb hD hν (ψ j))).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact abs_integral_le_of_abs_le hMG
      · exact tendsto_integral_of_tendsto (hν' r) hGc hMG
    have h3 : ∀ᶠ j in atTop, ∫ y, φ y ∂ρ₀ + ∫ r in (0 : ℝ)..t,
        ∫ y, fpGen b D φ y ∂(ν (ψ j) r : Measure (Fin d → ℝ)) =
        ∫ y, φ y ∂(ν (ψ j) t : Measure (Fin d → ℝ)) := by
      refine eventually_atTop.2 ⟨⌈Rφ⌉₊, fun j hj => ?_⟩
      have hR : tsupport φ ⊆ closedBall 0 (ψ j : ℝ) := by
        refine hRφ.trans (closedBall_subset_closedBall ?_)
        calc Rφ ≤ ⌈Rφ⌉₊ := Nat.le_ceil Rφ
          _ ≤ (ψ j : ℝ) := by exact_mod_cast hj.trans (le_of_strictMono hψ j)
      rw [integral_truncSol_eq hb hD hν (ψ j) hφ t, max_eq_left ht,
        fpGen_truncDrift_eq D hR]
    exact tendsto_nhds_unique h1 ((h2.const_add _).congr' h3)
  refine ⟨ν', h0, hν'c, fun φ hφ t ht => ?_⟩
  obtain ⟨MG, hMG⟩ := exists_bound_fpGen hb.continuous D hφ
  have hGc : Continuous fun r => ∫ y, fpGen b D φ y ∂(ν' r : Measure (Fin d → ℝ)) :=
    (continuous_integral_of_abs_le (continuous_fpGen hb.continuous D hφ.1) hMG).comp hν'c
  have hd := ((hGc.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt
    (s := Ici 0)).const_add (∫ y, φ y ∂ρ₀)
  exact hd.congr_of_mem (fun s hs => hid φ hφ s (mem_Ici.1 hs)) ht

/-- **Measure-curve form, dissipative drift.** Under the hypotheses of
`exists_weakFokkerPlanck_dissipative`, there is `ρ : ℝ → Measure (Fin d → ℝ)` with `ρ 0 = ρ₀`,
every `ρ t` a probability measure and `WeakFokkerPlanck ρ (fun _ => b) D`. -/
theorem exists_weakFokkerPlanck_dissipative_measure {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : LocallyLipschitz b) {C : ℝ} (hdiss : ∀ x, x ⬝ᵥ b x ≤ C * (1 + x ⬝ᵥ x)) {D : ℝ}
    (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => b) D := by
  obtain ⟨ν, h0, -, hfp⟩ := exists_weakFokkerPlanck_dissipative hb hdiss hD ρ₀
  exact ⟨fun t => ν t, h0, fun t => inferInstance, hfp⟩

/-! ### Overdamped Langevin with superlinear (e.g. quartic) potentials -/

/-- **Overdamped Langevin, confining potential (Verified, no Itô input).** Let `U : ℝᵈ → ℝ`
have a locally Lipschitz gradient (e.g. `U ∈ C²`, see
`exists_weakFokkerPlanck_langevin_contDiff`) satisfying the one-sided growth condition
`x ⬝ᵥ ∇U(x) ≥ -C (1 + x ⬝ᵥ x)` (e.g. `U(x) = |x|⁴`, double wells `|x|⁴ - a|x|²`, any convex
`U`), `D > 0` and `ρ₀` any probability measure. Then the weak Fokker–Planck equation of
`dX = -∇U(X) dt + √(2D) dW` has a weakly continuous probability-measure solution `ν` with
`ν 0 = ρ₀`. No global Lipschitz bound on `∇U` is assumed. -/
theorem exists_weakFokkerPlanck_langevin_dissipative {U : (Fin d → ℝ) → ℝ}
    (hU : LocallyLipschitz (grad U)) {C : ℝ}
    (hcoer : ∀ x, -(C * (1 + x ⬝ᵥ x)) ≤ x ⬝ᵥ grad U x) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧
      WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (fun _ x => -grad U x) D := by
  have hn : LipschitzWith 1 fun v : Fin d → ℝ => -v :=
    LipschitzWith.of_dist_le_mul fun x y => by simp [dist_neg_neg]
  have hneg : LocallyLipschitz fun x => -grad U x := hn.locallyLipschitz.comp hU
  refine exists_weakFokkerPlanck_dissipative hneg (C := C) (fun x => ?_) hD ρ₀
  rw [dotProduct_neg]; linarith [hcoer x]

/-- **Overdamped Langevin, `C²` confining potential (Verified).** For `U ∈ C²` with
`x ⬝ᵥ ∇U(x) ≥ -C (1 + x ⬝ᵥ x)`, `D > 0` and any probability measure `ρ₀`, the weak
Fokker–Planck equation of `dX = -∇U(X) dt + √(2D) dW` has a weakly continuous
probability-measure solution started at `ρ₀`. -/
theorem exists_weakFokkerPlanck_langevin_contDiff {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiff ℝ 2 U) {C : ℝ} (hcoer : ∀ x, -(C * (1 + x ⬝ᵥ x)) ≤ x ⬝ᵥ grad U x) {D : ℝ}
    (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧
      WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) (fun _ x => -grad U x) D := by
  have h1 : ContDiff ℝ 1 (grad U) := contDiff_pi.2 fun i => contDiff_partialDeriv hU i
  exact exists_weakFokkerPlanck_langevin_dissipative h1.locallyLipschitz hcoer hD ρ₀

/-! ### Example: quartic and double-well potentials -/

/-- `x ⬝ᵥ ∇U(x) = DU(x) x` (the coordinate gradient against the position vector). -/
theorem dotProduct_grad_eq_fderiv (U : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ grad U x = fderiv ℝ U x x := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j; simp [Pi.single_apply]
  rw [congrArg (fderiv ℝ U x) hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- The **double-well potential** `U_a(x) = |x|⁴ - a |x|²` (Euclidean norm); `a = 0` is the
quartic potential `|x|⁴`, whose gradient `4 |x|² x` is not globally Lipschitz. -/
noncomputable def doubleWell (a : ℝ) (x : Fin d → ℝ) : ℝ := (x ⬝ᵥ x) ^ 2 - a * (x ⬝ᵥ x)

/-- The double-well potential is `C²`. -/
theorem contDiff_doubleWell (a : ℝ) : ContDiff ℝ 2 (doubleWell (d := d) a) := by
  unfold doubleWell dotProduct; fun_prop

/-- `x ⬝ᵥ ∇U_a(x) = 4 |x|⁴ - 2 a |x|²`. -/
theorem dotProduct_grad_doubleWell (a : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ grad (doubleWell a) x = 4 * (x ⬝ᵥ x) ^ 2 - 2 * a * (x ⬝ᵥ x) := by
  rw [dotProduct_grad_eq_fderiv]
  set q := x ⬝ᵥ x
  have hγ : HasDerivAt (fun s : ℝ => x + s • x) x 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add x
  have h1 := ((contDiff_doubleWell (d := d) a).differentiable two_ne_zero
    (x + (0 : ℝ) • x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  simp only [zero_smul, add_zero] at h1
  have e : (doubleWell a ∘ fun s : ℝ => x + s • x) =
      fun s => ((1 + s) ^ 2 * q) ^ 2 - a * ((1 + s) ^ 2 * q) := by
    funext s
    have hs : ∑ i, (x i + s * x i) * (x i + s * x i) = (1 + s) ^ 2 * q := by
      rw [show q = ∑ i, x i * x i from rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [Function.comp, doubleWell, dotProduct, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hs]
  rw [e] at h1
  have h2 : HasDerivAt (fun s : ℝ => ((1 + s) ^ 2 * q) ^ 2 - a * ((1 + s) ^ 2 * q))
      (4 * q ^ 2 - 2 * a * q) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const q)
    have h3 := (this.pow 2).sub (this.const_mul a)
    convert h3 using 1
    · funext s; simp only [Pi.sub_apply, Pi.pow_apply, id]
    · simp only [id, Pi.pow_apply, add_zero, one_pow, mul_one]; ring
  exact h1.unique h2

/-- **Langevin dynamics in a quartic / double-well potential (Verified).** For every `a : ℝ`
(`a = 0`: `U(x) = |x|⁴`; `a > 0`: double well), `D > 0` and any probability measure `ρ₀`, the
weak Fokker–Planck equation of `dX = -∇U_a(X) dt + √(2D) dW` has a weakly continuous
probability-measure solution started at `ρ₀`. The drift `-∇U_a(x) = -(4|x|² - 2a) x` grows
cubically, so neither `exists_weakFokkerPlanck_langevin` nor explicit Euler–Maruyama applies. -/
theorem exists_weakFokkerPlanck_doubleWell (a : ℝ) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ)))
        (fun _ x => -grad (doubleWell a) x) D := by
  refine exists_weakFokkerPlanck_langevin_contDiff (contDiff_doubleWell a) (C := 2 * |a|)
    (fun x => ?_) hD ρ₀
  rw [dotProduct_grad_doubleWell]
  have hq : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  nlinarith [sq_nonneg (x ⬝ᵥ x), abs_nonneg a, mul_le_mul_of_nonneg_right (le_abs_self a) hq]

end FormalizeSampling.FokkerPlanckExistence
