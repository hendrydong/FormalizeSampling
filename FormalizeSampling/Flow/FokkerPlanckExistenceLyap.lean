module

public import FormalizeSampling.Flow.FokkerPlanckExistenceGenerator
public import FormalizeSampling.Flow.FokkerPlanckExistenceTight

/-!
# Weighted (Lyapunov) estimates for Euler–Maruyama steps with linearly growing drift

Status: **Verified.** Infrastructure for the existence proofs for drifts of linear growth
`‖b x‖ ≤ B (1 + ‖x‖)` (time-dependent in `Flow/FokkerPlanckExistenceTime*.lean`, autonomous in
`Flow/FokkerPlanckExistenceLinear.lean`). Estimates are weighted by the Lyapunov function

  `lyap y = 1 + |y|²` (Euclidean norm),

which the EM step contracts up to a factor `1 + c h`:

* `lintegral_lyap_emStep_le`: `E lyap(Y) ≤ (1 + c h) lyap(y)` for `Y ∼ emStep b hb D h y`,
  `c = lyapConst d B D = 1 + 4 d B² + 2 d D`, `0 ≤ h ≤ 1` (centred Gaussian noise);
* `abs_emOp_le_lyap`: hence `|F| ≤ A lyap` implies `|emOp b D h F| ≤ A (1 + c h) lyap`;
* `abs_emOp_sub_le_pt`: `|emOp f x - f x| ≤ C (h ‖b x‖ + √(2Dh) E‖Z‖)` (pointwise in `x`);
* `abs_emOp_two_sub_le`: two half steps with drifts `b₁`, then `b₂`, versus one step with `b₁`,
  for `b₁` Lipschitz and `‖b₂ - b₁‖ ≤ η (1 + ‖·‖)`;
* `emOp_generator_lyap`: the generator expansion
  `|emOp b D h φ x - φ x - h (b(x) ⬝ ∇φ(x) + D Δφ(x))| ≤ ε h lyap(x)` for `φ ∈ C²_c`, uniformly
  over all drifts with `‖b x‖ ≤ B (1 + ‖x‖)`.

## Not proved here

* No statement about the EM chain itself (iterates, laws, limits): see
  `Flow/FokkerPlanckExistenceTimeOp.lean` and `Flow/FokkerPlanckExistenceTime.lean`.
* Superlinear drifts (the weight `1 + |y|²` is only a Lyapunov function under linear growth).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal Interval

namespace FormalizeSampling.FokkerPlanckExistence
open FormalizeSampling.HeatKernelPi FormalizeSampling.WeakFokkerPlanckOU NoiseScore

variable {d : ℕ}

/-! ### The Lyapunov weight -/

/-- The Lyapunov weight `lyap y = 1 + |y|²` (Euclidean norm, `|y|² = ∑ᵢ yᵢ²`). -/
noncomputable def lyap (y : Fin d → ℝ) : ℝ := 1 + sqDist 0 y

/-- The squared Euclidean distance is nonnegative. -/
theorem sqDist_nonneg' (x y : Fin d → ℝ) : 0 ≤ sqDist x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `1 ≤ lyap y`. -/
theorem one_le_lyap (y : Fin d → ℝ) : 1 ≤ lyap y := by
  unfold lyap; linarith [sqDist_nonneg' 0 y]

/-- `0 < lyap y`. -/
theorem lyap_pos (y : Fin d → ℝ) : 0 < lyap y := lt_of_lt_of_le one_pos (one_le_lyap y)

/-- `1 + ‖y‖² ≤ lyap y` (sup norm versus Euclidean norm). -/
theorem one_add_sq_norm_le_lyap (y : Fin d → ℝ) : 1 + ‖y‖ ^ 2 ≤ lyap y := by
  have := sq_norm_le_sqDist 0 y
  rw [sub_zero] at this
  unfold lyap; linarith

/-- `(1 + ‖y‖)² ≤ 2 lyap y`. -/
theorem sq_one_add_norm_le_lyap (y : Fin d → ℝ) : (1 + ‖y‖) ^ 2 ≤ 2 * lyap y := by
  nlinarith [one_add_sq_norm_le_lyap y, sq_nonneg (‖y‖ - 1)]

/-- `1 + ‖y‖ ≤ 2 lyap y`. -/
theorem one_add_norm_le_lyap (y : Fin d → ℝ) : 1 + ‖y‖ ≤ 2 * lyap y := by
  nlinarith [one_add_sq_norm_le_lyap y, sq_nonneg (‖y‖ - 1), norm_nonneg y]

/-- `lyap` is continuous. -/
theorem continuous_lyap : Continuous (lyap (d := d)) := by
  unfold lyap sqDist; fun_prop

/-- The constant `c = 1 + 4 d B² + 2 d D` of the one-step Lyapunov estimate. -/
noncomputable def lyapConst (d : ℕ) (B D : ℝ) : ℝ := 1 + 4 * d * B ^ 2 + 2 * d * D

/-- `0 ≤ lyapConst d B D` for `D ≥ 0`. -/
theorem lyapConst_nonneg (B : ℝ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ lyapConst d B D := by
  unfold lyapConst; positivity

/-- **One-step Lyapunov estimate.** If `‖b y‖ ≤ B (1 + ‖y‖)`, `D ≥ 0` and `0 ≤ h ≤ 1`, then
`E lyap(Y) ≤ (1 + c h) lyap(y)` for `Y ∼ emStep b hb D h y`, `c = lyapConst d B D`. -/
theorem lintegral_lyap_emStep_le {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b) {B D h : ℝ}
    (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) {y : Fin d → ℝ} (hy : ‖b y‖ ≤ B * (1 + ‖y‖)) :
    ∫⁻ z, ENNReal.ofReal (lyap z) ∂(emStep b hb D h y) ≤
      ENNReal.ofReal ((1 + lyapConst d B D * h) * lyap y) := by
  have hm : Measurable fun z : Fin d → ℝ => ENNReal.ofReal (sqDist 0 z) :=
    ENNReal.measurable_ofReal.comp (measurable_sqDist 0)
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
  set S := sqDist 0 y with hS
  have hS0 : 0 ≤ S := sqDist_nonneg' 0 y
  have hly : lyap y = 1 + S := rfl
  have hbi : ∀ i, b y i ^ 2 ≤ ‖b y‖ ^ 2 := fun i => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm (b y) i)) 2
  have hpt : ∀ i ∈ Finset.univ, ((y + h • b y) i - (0 : Fin d → ℝ) i) ^ 2 + 2 * D * h ≤
      (1 + h) * (y i - (0 : Fin d → ℝ) i) ^ 2 + (2 * h * ‖b y‖ ^ 2 + 2 * D * h) := by
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero]
    nlinarith [sq_nonneg (y i - b y i), mul_nonneg hh0 (sq_nonneg (y i - b y i)),
      mul_nonneg (mul_nonneg hh0 (sub_nonneg.2 hh1)) (sq_nonneg (b y i)),
      mul_le_mul_of_nonneg_left (hbi i) hh0]
  have hsum := Finset.sum_le_sum hpt
  have hR : ∑ i ∈ Finset.univ, ((1 + h) * (y i - (0 : Fin d → ℝ) i) ^ 2 +
      (2 * h * ‖b y‖ ^ 2 + 2 * D * h)) = (1 + h) * S + d * (2 * h * ‖b y‖ ^ 2 + 2 * D * h) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [hR] at hsum
  have hb2 : ‖b y‖ ^ 2 ≤ 2 * B ^ 2 * lyap y := by
    have h1 : ‖b y‖ ^ 2 ≤ (B * (1 + ‖y‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy 2
    have h2 := sq_one_add_norm_le_lyap y
    nlinarith [sq_nonneg B]
  have hl1 := one_le_lyap y
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold lyapConst
  rw [hly] at hb2 hl1 ⊢
  have key : (d : ℝ) * (2 * h * ‖b y‖ ^ 2 + 2 * D * h) ≤
      h * (4 * d * B ^ 2 + 2 * d * D) * (1 + S) := by
    have := mul_le_mul_of_nonneg_left hb2 (mul_nonneg hd0 hh0)
    nlinarith [mul_nonneg (mul_nonneg hd0 hh0) hD, mul_nonneg (mul_nonneg hd0 hh0)
      (mul_nonneg hD hS0)]
  nlinarith [mul_nonneg hh0 hS0]

/-- **Weighted integral bound.** If `F` is integrable for `μ`, `|F| ≤ A lyap` with `A ≥ 0`, and
`∫⁻ lyap dμ ≤ W` with `W ≥ 0`, then `|∫ F dμ| ≤ A W`. -/
theorem abs_integral_le_of_le_lyap {μ : Measure (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}
    (hF : Integrable F μ) {A W : ℝ} (hA : 0 ≤ A) (hW0 : 0 ≤ W)
    (hFV : ∀ y, |F y| ≤ A * lyap y)
    (hW : ∫⁻ y, ENNReal.ofReal (lyap y) ∂μ ≤ ENNReal.ofReal W) :
    |∫ y, F y ∂μ| ≤ A * W := by
  refine (abs_integral_le_integral_abs).trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _)
    hF.abs.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ y, ENNReal.ofReal |F y| ∂μ ≤ ∫⁻ y, ENNReal.ofReal A * ENNReal.ofReal (lyap y) ∂μ :=
        lintegral_mono fun y => by
          rw [← ENNReal.ofReal_mul hA]; exact ENNReal.ofReal_le_ofReal (hFV y)
    _ = ENNReal.ofReal A * ∫⁻ y, ENNReal.ofReal (lyap y) ∂μ :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp continuous_lyap.measurable)
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal W := by gcongr
    _ = ENNReal.ofReal (A * W) := (ENNReal.ofReal_mul hA).symm

/-- **The EM operator in the weighted norm.** If `‖b y‖ ≤ B (1 + ‖y‖)` for all `y`, `D ≥ 0`,
`0 ≤ h ≤ 1`, and `F` is bounded, continuous, with `|F| ≤ A lyap` (`A ≥ 0`), then
`|emOp b D h F x| ≤ A (1 + c h) lyap x`, `c = lyapConst d B D`. -/
theorem abs_emOp_le_lyap {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Measurable b) {B D h : ℝ}
    (hB : ∀ y, ‖b y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) {A : ℝ}
    (hA : 0 ≤ A) (hFV : ∀ y, |F y| ≤ A * lyap y) (x : Fin d → ℝ) :
    |emOp b D h F x| ≤ A * ((1 + lyapConst d B D * h) * lyap x) := by
  rw [← integral_emStep hb hD hh0 hF x]
  have hc := lyapConst_nonneg (d := d) B hD
  exact abs_integral_le_of_le_lyap (Integrable.of_bound hF.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)) hA
    (by have := lyap_pos x; positivity) hFV (lintegral_lyap_emStep_le hb hD hh0 hh1 (hB x))

/-! ### Pointwise one-step and two-step defects -/

section Defects

variable {D h : ℝ} {f : (Fin d → ℝ) → ℝ}

/-- **One step moves Lipschitz test functions by `O(√h)`, pointwise.** For any drift `b`,
`D, h ≥ 0` and `f` bounded, continuous, `C`-Lipschitz (`C ≥ 0`):
`|emOp b D h f x - f x| ≤ C (h ‖b x‖ + √(2Dh) E‖Z‖)`. -/
theorem abs_emOp_sub_le_pt (b : (Fin d → ℝ) → Fin d → ℝ) (hD : 0 ≤ D) (hh : 0 ≤ h)
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ}
    (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C) (x : Fin d → ℝ) :
    |emOp b D h f x - f x| ≤
      C * (h * ‖b x‖ + Real.sqrt (2 * D * h) * gaussNormMean (d := d)) :=
  abs_emOp_sub_le (b := fun _ => b x) (B := ‖b x‖) (fun _ => le_rfl) hD hh hf hM hC hC0 x

/-- **Two half steps with different drifts versus one step.** Let `b₁` be `L`-Lipschitz, `b₂`
continuous with `‖b₂ y - b₁ y‖ ≤ η (1 + ‖y‖)` (`η ≥ 0`), `D, h ≥ 0`, and `f` bounded,
continuous, `C`-Lipschitz (`C ≥ 0`). With `P^{(i)}_s = emOp bᵢ D s`,
`|P^{(1)}_{h/2} (P^{(2)}_{h/2} f) x - P^{(1)}_h f x| ≤
  C (h/2) (η (1 + ‖x‖) + (η + L) ((h/2) ‖b₁ x‖ + √(Dh) E‖Z‖))`. -/
theorem abs_emOp_two_sub_le {b₁ b₂ : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L b₁) (hb₂ : Continuous b₂) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ y, ‖b₂ y - b₁ y‖ ≤ η * (1 + ‖y‖)) (hD : 0 ≤ D) (hh : 0 ≤ h)
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ}
    (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C) (x : Fin d → ℝ) :
    |emOp b₁ D (h / 2) (emOp b₂ D (h / 2) f) x - emOp b₁ D h f x| ≤
      C * (h / 2) * (η * (1 + ‖x‖) + (η + L) * (h / 2 * ‖b₁ x‖ +
        Real.sqrt (D * h) * gaussNormMean (d := d))) := by
  have hs : Real.sqrt (2 * D * (h / 2)) = Real.sqrt (D * h) := by ring_nf
  set s := Real.sqrt (D * h) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hh2 : 0 ≤ h / 2 := by positivity
  have hPc : Continuous (emOp b₂ D (h / 2) f) := continuous_emOp hb₂ hf hM
  have hPM : ∀ y, |emOp b₂ D (h / 2) f y| ≤ M := abs_emOp_le hf hM
  have hP : ∀ (b' : (Fin d → ℝ) → Fin d → ℝ) (g : (Fin d → ℝ) → ℝ) y,
      emOp b' D (h / 2) g y = ∫ z, g (y + (h / 2) • b' y + s • z) ∂stdGauss := by
    intro b' g y; simp only [emOp, hs]
  set F : (Fin d → ℝ) → ℝ := fun y => ∫ z, f (y + s • z) ∂stdGauss with hF
  have hFc : Continuous F := continuous_integral_shift hf hM s
  have hFM : ∀ y, |F y| ≤ M := fun y => abs_integral_stdGauss_le fun z => hM _
  have hv : ((stepVar D (h / 2) : ℝ≥0) : ℝ) = D * h := by
    rw [stepVar, Real.coe_toNNReal _ (by positivity)]; ring
  have hfull : emOp b₁ D h f x =
      ∫ z₁, F (x + (h / 2) • b₁ x + s • z₁ + (h / 2) • b₁ x) ∂stdGauss := by
    have hsum := integral_integral_stdGauss_add hf hM (stepVar D (h / 2)) (x + h • b₁ x)
    rw [NNReal.coe_add, hv, show D * h + D * h = 2 * D * h by ring] at hsum
    rw [emOp, ← hsum]
    congr 1; funext z₁
    simp only [hF, hsdef]
    congr 1; funext z₂
    congr 1
    module
  rw [hfull, hP]
  have hG : Integrable (fun z₁ => F (x + (h / 2) • b₁ x + s • z₁ + (h / 2) • b₁ x)) stdGauss :=
    Integrable.of_bound (hFc.comp (by fun_prop)).aestronglyMeasurable M
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hFM _)
  set E := gaussNormMean (d := d) with hE
  have hpt : ∀ z₁ : Fin d → ℝ,
      |emOp b₂ D (h / 2) f (x + (h / 2) • b₁ x + s • z₁) -
          F (x + (h / 2) • b₁ x + s • z₁ + (h / 2) • b₁ x)| ≤
        C * (h / 2) * (η * (1 + ‖x‖) + (η + L) * (h / 2 * ‖b₁ x‖)) +
          C * (h / 2) * (η + L) * s * ‖z₁‖ := by
    intro z₁
    set y₁ := x + (h / 2) • b₁ x + s • z₁ with hy₁
    have hy : ‖y₁ - x‖ ≤ h / 2 * ‖b₁ x‖ + s * ‖z₁‖ := by
      have e : y₁ - x = (h / 2) • b₁ x + s • z₁ := by rw [hy₁]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hh2, Real.norm_of_nonneg hs0]
    have hbb : ‖b₂ y₁ - b₁ x‖ ≤ η * (1 + ‖x‖) + (η + L) * ‖y₁ - x‖ := by
      have h1 : ‖b₂ y₁ - b₁ x‖ ≤ ‖b₂ y₁ - b₁ y₁‖ + ‖b₁ y₁ - b₁ x‖ := by
        rw [show b₂ y₁ - b₁ x = (b₂ y₁ - b₁ y₁) + (b₁ y₁ - b₁ x) by abel]
        exact norm_add_le _ _
      have h2 := hη y₁
      have h3 := hL.norm_sub_le y₁ x
      have h4 : ‖y₁‖ ≤ ‖x‖ + ‖y₁ - x‖ := by
        have := norm_add_le x (y₁ - x)
        rwa [add_sub_cancel] at this
      have : η * (1 + ‖y₁‖) ≤ η * (1 + ‖x‖ + ‖y₁ - x‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hη0
      nlinarith
    have hin : ∀ z₂ : Fin d → ℝ,
        |f (y₁ + (h / 2) • b₂ y₁ + s • z₂) - f (y₁ + (h / 2) • b₁ x + s • z₂)| ≤
          C * (h / 2) * (η * (1 + ‖x‖) + (η + L) * ‖y₁ - x‖) + 0 * ‖z₂‖ := by
      intro z₂
      rw [zero_mul, add_zero]
      refine (hC _ _).trans ?_
      have e : y₁ + (h / 2) • b₂ y₁ + s • z₂ - (y₁ + (h / 2) • b₁ x + s • z₂) =
          (h / 2) • (b₂ y₁ - b₁ x) := by rw [smul_sub]; abel
      rw [e, norm_smul, Real.norm_of_nonneg hh2, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hbb (by positivity)
    have key := abs_integral_sub_le (integrable_comp_affine hf hM (y₁ + (h / 2) • b₂ y₁) s)
      (integrable_comp_affine hf hM (y₁ + (h / 2) • b₁ x) s) hin
    rw [hP, hF]
    simp only
    refine (le_of_eq_of_le ?_ key).trans ?_
    · congr 3
    · rw [zero_mul, add_zero]
      have : (η + L) * ‖y₁ - x‖ ≤ (η + L) * (h / 2 * ‖b₁ x‖ + s * ‖z₁‖) := by
        gcongr
      have hCh : 0 ≤ C * (h / 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hCh]
  have key := abs_integral_sub_le (integrable_comp_affine hPc hPM (x + (h / 2) • b₁ x) s) hG hpt
  refine key.trans (le_of_eq ?_)
  ring

end Defects

/-! ### Generator expansion under linear growth -/

section Generator

variable {φ : (Fin d → ℝ) → ℝ}

/-- **Frozen-drift generator expansion with explicit dependence on the drift.** For `φ ∈ C²_c`,
`D > 0` and `ε > 0` there is `K ≥ 0` such that for all `h ≥ 0` and all `x, v`,
`|E φ(x + h v + √(2Dh) Z) - φ x - h (frozenGen D φ v x)| ≤
  h (ε (‖v‖ + D) + K (‖v‖ + 1) (h ‖v‖ + √(2Dh) E‖Z‖))`. -/
theorem abs_integral_drift_generator_le (hφ : TestFunction2 φ) {D : ℝ} (hD : 0 < D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K, 0 ≤ K ∧ ∀ h, 0 ≤ h → ∀ x v : Fin d → ℝ,
      |∫ z, φ (x + h • v + Real.sqrt (2 * D * h) • z) ∂stdGauss - φ x -
          h * frozenGen D φ v x| ≤
        h * (ε * (‖v‖ + D) + K * (‖v‖ + 1) *
          (h * ‖v‖ + Real.sqrt (2 * D * h) * gaussNormMean (d := d))) := by
  obtain ⟨hφ2, hφc⟩ := hφ
  have hLc := hasCompactSupport_laplacian hφc
  have hUd : UniformContinuous (fderiv ℝ φ) :=
    (hφc.fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous (hφ2.continuous_fderiv two_ne_zero)
  have hUL : UniformContinuous (laplacian φ) :=
    hLc.uniformContinuous_of_continuous (continuous_laplacian hφ2)
  obtain ⟨M1, hM1⟩ := (hφ2.continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨ML, hML⟩ := (continuous_laplacian hφ2).bounded_above_of_compact_support hLc
  obtain ⟨K1, hK1, h1⟩ := exists_modulus_bound hUd hM1 hε
  obtain ⟨K2, hK2, h2⟩ := exists_modulus_bound hUL hML hε
  set K := K1 + D * K2 with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨K, hK, fun h hh x v => ?_⟩
  set E := gaussNormMean (d := d) with hEdef
  have hE : 0 ≤ E := integral_nonneg fun z => norm_nonneg z
  have hv0 := norm_nonneg v
  have hmod : ∀ y, |frozenGen D φ v y - frozenGen D φ v x| ≤
      ε * (‖v‖ + D) + K * (‖v‖ + 1) * ‖y - x‖ := by
    intro y
    have e : frozenGen D φ v y - frozenGen D φ v x =
        (fderiv ℝ φ y - fderiv ℝ φ x) v + D * (laplacian φ y - laplacian φ x) := by
      simp only [frozenGen, sub_apply]; ring
    have ha : |(fderiv ℝ φ y - fderiv ℝ φ x) v| ≤ (ε + K1 * ‖y - x‖) * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ φ y - fderiv ℝ φ x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (h1 x y) (norm_nonneg _))
    have hl : |D * (laplacian φ y - laplacian φ x)| ≤ D * (ε + K2 * ‖y - x‖) := by
      rw [abs_mul, abs_of_pos hD]
      exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact h2 x y) hD.le
    rw [e]
    have hr := norm_nonneg (y - x)
    calc _ ≤ |(fderiv ℝ φ y - fderiv ℝ φ x) v| + |D * (laplacian φ y - laplacian φ x)| :=
          abs_add_le _ _
      _ ≤ (ε + K1 * ‖y - x‖) * ‖v‖ + D * (ε + K2 * ‖y - x‖) := add_le_add ha hl
      _ ≤ _ := by
          rw [hKdef]
          nlinarith [mul_nonneg (mul_nonneg hK1 hr) hv0, mul_nonneg (mul_nonneg hD.le hK2) hr,
            mul_nonneg (mul_nonneg (mul_nonneg hD.le hK2) hr) hv0, mul_nonneg hK1 hr]
  set Q := ε * (‖v‖ + D) + K * (‖v‖ + 1) * (h * ‖v‖ + Real.sqrt (2 * D * h) * E) with hQ
  obtain ⟨CG, hCG⟩ := exists_bound_frozenGen hφ2 hφc D v
  have hH := continuous_integral_drift (continuous_frozenGen hφ2 D v) hCG x v D
  have hftc := integral_drift_sub hφ2 hφc x v hD hh
  have hrep : ∫ z, φ (x + h • v + Real.sqrt (2 * D * h) • z) ∂stdGauss - φ x -
      h * frozenGen D φ v x =
      ∫ s in (0 : ℝ)..h, ((∫ z, frozenGen D φ v (x + s • v + Real.sqrt (2 * D * s) • z)
        ∂stdGauss) - frozenGen D φ v x) := by
    rw [intervalIntegral.integral_sub (hH.intervalIntegrable _ _) intervalIntegrable_const,
      hftc]
    simp
  rw [hrep, ← Real.norm_eq_abs]
  have hbd : ∀ s ∈ Ι (0 : ℝ) h, ‖(∫ z, frozenGen D φ v (x + s • v + Real.sqrt (2 * D * s) • z)
      ∂stdGauss) - frozenGen D φ v x‖ ≤ Q := by
    intro s hs
    rw [uIoc_of_le hh] at hs
    have hs0 : 0 ≤ s := hs.1.le
    set σ := Real.sqrt (2 * D * s) with hσ
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have hσh : σ ≤ Real.sqrt (2 * D * h) := Real.sqrt_le_sqrt (by nlinarith [hs.2])
    have hcY : Continuous fun z : Fin d → ℝ => x + s • v + σ • z := by fun_prop
    have hn : Integrable (fun z : Fin d → ℝ => ‖z‖) stdGauss := integrable_norm_stdGauss
    have hint : Integrable (fun z => frozenGen D φ v (x + s • v + σ • z)) stdGauss :=
      Integrable.of_bound ((continuous_frozenGen hφ2 D v).comp hcY).aestronglyMeasurable CG
        (ae_of_all _ fun z => hCG _)
    have e1 : (∫ z, frozenGen D φ v (x + s • v + σ • z) ∂stdGauss) - frozenGen D φ v x =
        ∫ z, (frozenGen D φ v (x + s • v + σ • z) - frozenGen D φ v x) ∂stdGauss := by
      rw [integral_sub hint (integrable_const _)]
      simp
    set Kv := K * (‖v‖ + 1) with hKv
    have hKv0 : 0 ≤ Kv := by positivity
    have hgi : Integrable (fun z : Fin d → ℝ => (ε * (‖v‖ + D) + Kv * (s * ‖v‖)) +
        (Kv * σ) * ‖z‖) stdGauss := (integrable_const _).add (hn.const_mul _)
    rw [e1]
    refine (norm_integral_le_of_norm_le hgi (ae_of_all _ fun z => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      refine (hmod _).trans ?_
      have hY : ‖x + s • v + σ • z - x‖ ≤ s * ‖v‖ + σ * ‖z‖ := by
        rw [show x + s • v + σ • z - x = s • v + σ • z by abel]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg hs0]
        · rw [norm_smul, Real.norm_of_nonneg hσ0]
      nlinarith [mul_le_mul_of_nonneg_left hY hKv0]
    · rw [integral_add (integrable_const _) (hn.const_mul _), integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      have hE' : ∫ a, ‖a‖ ∂(stdGauss (d := d)) = E := rfl
      try rw [hE']
      have i1 : s * ‖v‖ ≤ h * ‖v‖ := mul_le_mul_of_nonneg_right hs.2 hv0
      have i2 : σ * E ≤ Real.sqrt (2 * D * h) * E := mul_le_mul_of_nonneg_right hσh hE
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add i1 i2) hKv0]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans ?_
  rw [sub_zero, abs_of_nonneg hh]
  linarith

/-- **Generator expansion of one EM step under linear growth (weighted `o(h)`).** For
`φ ∈ C²_c`, `B ≥ 0`, `D > 0` and `ε > 0` there is `δ > 0` such that for every `0 < h ≤ δ`,
every drift `b` and every `x` with `‖b x‖ ≤ B (1 + ‖x‖)`,
`|emOp b D h φ x - φ x - h (b(x) ⬝ ∇φ(x) + D Δφ(x))| ≤ ε h lyap(x)`. -/
theorem emOp_generator_lyap (hφ : TestFunction2 φ) {B : ℝ} (hB0 : 0 ≤ B) {D : ℝ} (hD : 0 < D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h ≤ δ → ∀ (b : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ),
      ‖b x‖ ≤ B * (1 + ‖x‖) →
      |emOp b D h φ x - φ x - h * (b x ⬝ᵥ grad φ x + D * laplacian φ x)| ≤
        ε * h * lyap x := by
  set ε₁ := ε / (4 * (B + D + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁B : ε₁ * (2 * (B + D)) ≤ ε / 2 := by
    rw [hε₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨K, hK, hgen⟩ := abs_integral_drift_generator_le hφ hD hε₁0
  set E := gaussNormMean (d := d) with hEdef
  have hE : 0 ≤ E := integral_nonneg fun z => norm_nonneg z
  set q : ℝ → ℝ := fun h => K * (2 * (B + 1)) * (h * B + Real.sqrt (2 * D * h) * E) with hqdef
  have hq : Continuous q := by fun_prop
  have hq0 : q 0 = 0 := by simp [hqdef]
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.1 ((hq.tendsto 0).eventually
    (gt_mem_nhds (show q 0 < ε / 2 by rw [hq0]; positivity)))
  refine ⟨δ / 2, by positivity, fun h hh hhδ b x hbx => ?_⟩
  have hqh : q h < ε / 2 := hδq (by rw [Real.dist_eq, sub_zero, abs_of_pos hh]; linarith)
  set v := b x with hv
  have hgenx := hgen h hh.le x v
  have hgx : b x ⬝ᵥ grad φ x + D * laplacian φ x = frozenGen D φ v x := by
    rw [dotProduct_grad]; rfl
  have hem : emOp b D h φ x = ∫ z, φ (x + h • v + Real.sqrt (2 * D * h) • z) ∂stdGauss := rfl
  rw [hgx, hem]
  refine hgenx.trans ?_
  set r := 1 + ‖x‖ with hr
  have hr1 : 1 ≤ r := by simp [hr]
  have hl1 := one_add_norm_le_lyap x
  have hl2 := sq_one_add_norm_le_lyap x
  rw [← hr] at hl1 hl2
  have hv0 := norm_nonneg v
  have hs0 : 0 ≤ Real.sqrt (2 * D * h) := Real.sqrt_nonneg _
  have t1 : ε₁ * (‖v‖ + D) ≤ ε / 2 * lyap x := by
    have : ‖v‖ + D ≤ (B + D) * r := by nlinarith
    have h2 : ε₁ * (‖v‖ + D) ≤ ε₁ * ((B + D) * r) := by gcongr
    have h3 : ε₁ * ((B + D) * r) ≤ ε₁ * ((B + D) * (2 * lyap x)) := by
      gcongr
    nlinarith
  have t2 : K * (‖v‖ + 1) * (h * ‖v‖ + Real.sqrt (2 * D * h) * E) ≤ ε / 2 * lyap x := by
    have a1 : ‖v‖ + 1 ≤ (B + 1) * r := by nlinarith
    have a2 : h * ‖v‖ + Real.sqrt (2 * D * h) * E ≤ (h * B + Real.sqrt (2 * D * h) * E) * r := by
      have : h * ‖v‖ ≤ h * (B * r) := mul_le_mul_of_nonneg_left hbx hh.le
      nlinarith [mul_nonneg hs0 hE]
    have a3 : K * (‖v‖ + 1) * (h * ‖v‖ + Real.sqrt (2 * D * h) * E) ≤
        K * ((B + 1) * r) * ((h * B + Real.sqrt (2 * D * h) * E) * r) := by
      gcongr
    have a4 : K * ((B + 1) * r) * ((h * B + Real.sqrt (2 * D * h) * E) * r) =
        K * (B + 1) * (h * B + Real.sqrt (2 * D * h) * E) * r ^ 2 := by ring
    have a5 : K * (B + 1) * (h * B + Real.sqrt (2 * D * h) * E) * r ^ 2 ≤
        K * (B + 1) * (h * B + Real.sqrt (2 * D * h) * E) * (2 * lyap x) := by
      gcongr
    have a6 : K * (B + 1) * (h * B + Real.sqrt (2 * D * h) * E) * (2 * lyap x) =
        q h * lyap x := by simp only [hqdef]; ring
    have a7 : q h * lyap x ≤ ε / 2 * lyap x :=
      mul_le_mul_of_nonneg_right hqh.le (lyap_pos x).le
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add t1 t2) hh.le]

end Generator

end FormalizeSampling.FokkerPlanckExistence
