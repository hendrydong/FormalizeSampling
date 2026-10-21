module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-!
# Smooth convex approximation of convex functions on `Fin d → ℝ`

Status: **Verified** (no named hypotheses).

Every convex `f : (Fin d → ℝ) → ℝ` is the pointwise limit of convex `C²` functions with bounded
first and second derivatives, all bounded below by one common function `-A - B ‖x‖`. The
construction has two steps (`‖·‖` is Mathlib's sup norm on `Fin d → ℝ`; any norm would do):

1. **Pasch–Hausdorff envelope** `lipEnvelope f L x = ⨅ z, f z + L ‖x - z‖`. For `L ≥ B`, where
   `f x ≥ -A - B ‖x‖`, it is convex, `L`-Lipschitz, `≤ f`, `≥ -A - B ‖x‖`, and it converges to
   `f` pointwise as `L → ∞` (`f` is continuous).
2. **Mollification** `mollify h ε` by a normalised `ContDiffBump` of outer radius `ε`
   (`φ ⋆ h`). For `L`-Lipschitz `h` it is `C^∞`, `L`-Lipschitz (so `‖Dg‖ ≤ L`), its derivative
   is Lipschitz (so `‖D²g‖` is bounded), it stays convex if `h` is, and `|φ ⋆ h - h| ≤ L ε`.

## Main results

* `continuous_of_convexOn`, `exists_lowerBound_of_convexOn`: a convex function on
  `Fin d → ℝ` is continuous and satisfies `f x ≥ -A - B ‖x‖` with `B ≥ 0`.
* `convexOn_lipEnvelope`, `lipschitzWith_lipEnvelope`, `lipEnvelope_le_self`,
  `le_lipEnvelope`, `tendsto_lipEnvelope`.
* `contDiff_mollify`, `convexOn_mollify`, `lipschitzWith_mollify`, `norm_fderiv_mollify_le`,
  `norm_iteratedFDeriv_two_mollify_le`, `abs_mollify_sub_le`.
* `exists_smooth_convex_approx`: the approximating sequence, with a uniform lower bound
  `-A - B ‖x‖` and pointwise convergence to `f`.

## Not proved here

* Monotonicity of the approximants in `n` and locally uniform convergence (not needed).
* Any statement for convex functions taking the value `+∞` or defined on a proper convex
  subset; `f` is real-valued and convex on all of `Fin d → ℝ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal Convolution

namespace FormalizeSampling.ConvexSmoothing

variable {d : ℕ}

/-- A convex function on all of `Fin d → ℝ` is continuous. -/
theorem continuous_of_convexOn {f : (Fin d → ℝ) → ℝ} (hf : ConvexOn ℝ univ f) : Continuous f :=
  continuousOn_univ.1 (hf.continuousOn isOpen_univ)

/-- **Linear lower bound.** A convex `f` on `Fin d → ℝ` satisfies `-A - B ‖x‖ ≤ f x` for some
`A` and some `B ≥ 0` (sup norm). Proof: `f` is bounded below on the closed unit ball (continuity
and compactness), and convexity along the segment `[0, x]` propagates the bound linearly. -/
theorem exists_lowerBound_of_convexOn {f : (Fin d → ℝ) → ℝ} (hf : ConvexOn ℝ univ f) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ x, -A - B * ‖x‖ ≤ f x := by
  have hc := continuous_of_convexOn hf
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_closedBall (0 : Fin d → ℝ) 1).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hc.continuousOn
  set m := |f x₀| + |f 0| with hm
  have hm0 : 0 ≤ m := by positivity
  refine ⟨m, 2 * m, by positivity, fun x => ?_⟩
  have hball : ∀ z ∈ Metric.closedBall (0 : Fin d → ℝ) 1, -m ≤ f z := by
    intro z hz
    have := hx₀ hz
    simp only [mem_ofPred_eq] at this
    have := neg_abs_le (f x₀)
    have := abs_nonneg (f 0)
    linarith
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · have := hball x (by simpa using hx)
    have : 0 ≤ m * ‖x‖ := by positivity
    linarith
  · set r := ‖x‖ with hr
    have hr0 : 0 < r := by linarith
    have hu : (1 - r⁻¹) • (0 : Fin d → ℝ) + r⁻¹ • x ∈ Metric.closedBall (0 : Fin d → ℝ) 1 := by
      simp only [smul_zero, zero_add, mem_closedBall_zero_iff, norm_smul, norm_inv]
      rw [← hr, Real.norm_of_nonneg hr0.le, inv_mul_cancel₀ hr0.ne']
    have hconv : f ((1 - r⁻¹) • (0 : Fin d → ℝ) + r⁻¹ • x) ≤ (1 - r⁻¹) • f 0 + r⁻¹ • f x :=
      hf.2 (mem_univ _) (mem_univ _) (by
      rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hx.le) (inv_nonneg.2 hr0.le) (by ring)
    have hlow := hball _ hu
    simp only [smul_eq_mul] at hconv
    have h0 : -|f 0| ≤ f 0 := neg_abs_le _
    have : -m ≤ (1 - r⁻¹) * f 0 + r⁻¹ * f x := hlow.trans hconv
    have h1 : -m * r ≤ (r - 1) * f 0 + f x := by
      have := mul_le_mul_of_nonneg_right this hr0.le
      have e : ((1 - r⁻¹) * f 0 + r⁻¹ * f x) * r = (r - 1) * f 0 + f x := by
        field_simp
      linarith
    have h2 : (r - 1) * f 0 ≤ (r - 1) * |f 0| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
    have h3 : (r - 1) * |f 0| ≤ r * m := by nlinarith [abs_nonneg (f x₀), abs_nonneg (f 0)]
    nlinarith


/-- The **Pasch–Hausdorff envelope** `x ↦ ⨅ z, f z + L ‖x - z‖` (sup norm). It is the largest
`L`-Lipschitz minorant of `f` when the infimum is finite (see the lemmas below, which assume
`f x ≥ -A - B ‖x‖` with `B ≤ L`). -/
noncomputable def lipEnvelope (f : (Fin d → ℝ) → ℝ) (L : ℝ) (x : Fin d → ℝ) : ℝ :=
  ⨅ z, f z + L * ‖x - z‖

section Envelope

variable {f : (Fin d → ℝ) → ℝ} {A B L : ℝ}

/-- Each term of the envelope infimum is `≥ -A - B ‖x‖` if `f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`. -/
theorem lowerBound_le_envelope_term (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L)
    (x z : Fin d → ℝ) : -A - B * ‖x‖ ≤ f z + L * ‖x - z‖ := by
  have h1 := hlow z
  have h2 : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
    have := norm_sub_le x (x - z); simp only [sub_sub_cancel] at this
    linarith [norm_sub_rev x z]
  have h3 : B * ‖x - z‖ ≤ L * ‖x - z‖ := mul_le_mul_of_nonneg_right hBL (norm_nonneg _)
  nlinarith

/-- The envelope infimum is over a set bounded below (`f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`). -/
theorem bddBelow_envelope (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L)
    (x : Fin d → ℝ) : BddBelow (range fun z => f z + L * ‖x - z‖) :=
  ⟨-A - B * ‖x‖, by rintro _ ⟨z, rfl⟩; exact lowerBound_le_envelope_term hlow hB hBL x z⟩

/-- The envelope is `≤ f z + L ‖x - z‖` for every `z` (`f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`). -/
theorem lipEnvelope_le (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L)
    (x z : Fin d → ℝ) : lipEnvelope f L x ≤ f z + L * ‖x - z‖ :=
  ciInf_le (bddBelow_envelope hlow hB hBL x) z

/-- The envelope is a minorant: `lipEnvelope f L x ≤ f x` (`f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`). -/
theorem lipEnvelope_le_self (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L)
    (x : Fin d → ℝ) : lipEnvelope f L x ≤ f x := by
  simpa using lipEnvelope_le hlow hB hBL x x

/-- The envelope keeps the lower bound: `-A - B ‖x‖ ≤ lipEnvelope f L x` (`f ≥ -A - B ‖·‖`,
`0 ≤ B ≤ L`). -/
theorem le_lipEnvelope (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L)
    (x : Fin d → ℝ) : -A - B * ‖x‖ ≤ lipEnvelope f L x :=
  le_ciInf fun z => lowerBound_le_envelope_term hlow hB hBL x z

/-- One-sided Lipschitz bound of the envelope (`f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`). -/
theorem lipEnvelope_le_add (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L)
    (x y : Fin d → ℝ) : lipEnvelope f L x ≤ lipEnvelope f L y + L * ‖x - y‖ := by
  have hL : 0 ≤ L := hB.trans hBL
  have : lipEnvelope f L x - L * ‖x - y‖ ≤ lipEnvelope f L y := by
    refine le_ciInf fun z => ?_
    have h1 := lipEnvelope_le hlow hB hBL x z
    have h2 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
    have h3 := mul_le_mul_of_nonneg_left h2 hL
    linarith
  linarith

/-- The envelope is `L`-Lipschitz (`f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`). -/
theorem lipschitzWith_lipEnvelope (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B) (hBL : B ≤ L) :
    LipschitzWith (Real.toNNReal L) (lipEnvelope f L) := by
  have hL : 0 ≤ L := hB.trans hBL
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ hL, dist_eq_norm, abs_le]
  have h1 := lipEnvelope_le_add hlow hB hBL x y
  have h2 := lipEnvelope_le_add hlow hB hBL y x
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- The envelope of a convex function is convex (`f ≥ -A - B ‖·‖`, `0 ≤ B ≤ L`): it is the
infimal convolution of the convex functions `f` and `L ‖·‖`. -/
theorem convexOn_lipEnvelope (hf : ConvexOn ℝ univ f) (hlow : ∀ x, -A - B * ‖x‖ ≤ f x)
    (hB : 0 ≤ B) (hBL : B ≤ L) : ConvexOn ℝ univ (lipEnvelope f L) := by
  have hL : 0 ≤ L := hB.trans hBL
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨_, ⟨z₁, rfl⟩, hz₁⟩ := exists_lt_of_csInf_lt (range_nonempty _)
    (lt_add_of_pos_right (lipEnvelope f L x) hε)
  obtain ⟨_, ⟨z₂, rfl⟩, hz₂⟩ := exists_lt_of_csInf_lt (range_nonempty _)
    (lt_add_of_pos_right (lipEnvelope f L y) hε)
  have h1 := lipEnvelope_le hlow hB hBL (a • x + b • y) (a • z₁ + b • z₂)
  have h2 : f (a • z₁ + b • z₂) ≤ a • f z₁ + b • f z₂ := hf.2 (mem_univ _) (mem_univ _) ha hb hab
  have h3 : ‖a • x + b • y - (a • z₁ + b • z₂)‖ ≤ a * ‖x - z₁‖ + b * ‖y - z₂‖ := by
    have : a • x + b • y - (a • z₁ + b • z₂) = a • (x - z₁) + b • (y - z₂) := by
      simp only [smul_sub]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  simp only [smul_eq_mul] at h2
  have h4 := mul_le_mul_of_nonneg_left h3 hL
  have h5 := mul_le_mul_of_nonneg_left hz₁.le ha
  have h6 := mul_le_mul_of_nonneg_left hz₂.le hb
  simp only [mul_add] at h4 h5 h6
  have hε' : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  linarith [mul_left_comm L a ‖x - z₁‖, mul_left_comm L b ‖y - z₂‖]


/-- **Pointwise convergence of the envelopes.** For continuous `f ≥ -A - B ‖·‖` with `B ≥ 0`,
`lipEnvelope f (B + 1 + n) x → f x` as `n → ∞`, for every `x`. -/
theorem tendsto_lipEnvelope (hc : Continuous f) (hlow : ∀ x, -A - B * ‖x‖ ≤ f x) (hB : 0 ≤ B)
    (x : Fin d → ℝ) :
    Tendsto (fun n : ℕ => lipEnvelope f (B + 1 + n) x) atTop (𝓝 (f x)) := by
  have hBL : ∀ n : ℕ, B ≤ B + 1 + n := fun n => by linarith [n.cast_nonneg (α := ℝ)]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun n =>
    (lipEnvelope_le_self hlow hB (hBL n) x).trans_lt ha⟩
  obtain ⟨r, hr, hball⟩ := Metric.continuous_iff.1 hc x ((f x - a) / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt ((f x + A + B * ‖x‖) / r)
  rw [div_lt_iff₀ hr] at hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have key : (f x + a) / 2 ≤ lipEnvelope f (B + 1 + n) x := by
    refine le_ciInf fun z => ?_
    have hL : 0 ≤ B + 1 + (n : ℝ) := hB.trans (hBL n)
    rcases lt_or_ge (dist z x) r with hz | hz
    · have h1 := hball z hz
      rw [Real.dist_eq, abs_lt] at h1
      have : 0 ≤ (B + 1 + n) * ‖x - z‖ := by positivity
      linarith
    · rw [dist_eq_norm, norm_sub_rev] at hz
      have h1 := hlow z
      have h2 : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
        have := norm_sub_le x (x - z); simp only [sub_sub_cancel] at this
        linarith [norm_sub_rev x z]
      have h3 : (1 + (n : ℝ)) * r ≤ (1 + n) * ‖x - z‖ :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      have h4 : (N : ℝ) * r ≤ n * r := mul_le_mul_of_nonneg_right hn' hr.le
      nlinarith
  linarith

end Envelope

/-- The smooth bump on `Fin d → ℝ` centred at `0` with inner radius `ε / 2` and outer radius
`ε` (`ε > 0`). -/
noncomputable def bump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Fin d → ℝ) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩

/-- **Mollification** `φ ⋆ h`, `(φ ⋆ h) x = ∫ φ(t) h(x - t) dt`, by the Lebesgue-normalised
bump `φ = (bump ε hε).normed volume` (nonnegative, integral `1`, support in the ball of radius
`ε`). -/
noncomputable def mollify (h : (Fin d → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε) : (Fin d → ℝ) → ℝ :=
  (bump ε hε).normed volume ⋆[lsmul ℝ ℝ, volume] h

section Mollify

variable {h : (Fin d → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε)

/-- The mollification as an integral: `mollify h ε hε x = ∫ φ(t) h(x - t) dt`. -/
theorem mollify_apply (x : Fin d → ℝ) :
    mollify h ε hε x = ∫ t, (bump ε hε).normed volume t * h (x - t) := by
  rw [mollify, convolution_def]
  rfl

/-- The mollification of a continuous function is `C²` (indeed `C^∞`). -/
theorem contDiff_mollify (hh : Continuous h) : ContDiff ℝ 2 (mollify h ε hε) :=
  (bump ε hε).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    ((bump ε hε).contDiff_normed) hh.locallyIntegrable

/-- For continuous `h`, `t ↦ φ(t) h(x - t)` is integrable (continuous, compact support). -/
theorem integrable_bump_mul (hh : Continuous h) (x : Fin d → ℝ) :
    Integrable (fun t => (bump ε hε).normed volume t * h (x - t)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (bump ε hε).continuous_normed.mul (hh.comp (continuous_const.sub continuous_id))
  · exact (bump ε hε).hasCompactSupport_normed.mul_right

/-- **Uniform closeness.** For `L`-Lipschitz `h` (`L ≥ 0`): `|φ ⋆ h - h| ≤ L ε`. -/
theorem abs_mollify_sub_le {L : ℝ} (hL : 0 ≤ L) (hlip : LipschitzWith (Real.toNNReal L) h)
    (x : Fin d → ℝ) : |mollify h ε hε x - h x| ≤ L * ε := by
  rw [← Real.dist_eq]
  refine ContDiffBump.dist_normed_convolution_le hlip.continuous.aestronglyMeasurable
    fun z hz => ?_
  have := hlip.dist_le_mul z x
  rw [Real.coe_toNNReal _ hL] at this
  refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
  exact (Metric.mem_ball.1 hz).le

/-- The mollification of a continuous convex function is convex. -/
theorem convexOn_mollify (hh : Continuous h) (hcv : ConvexOn ℝ univ h) :
    ConvexOn ℝ univ (mollify h ε hε) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, mollify_apply]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_bump_mul hε hh x).const_mul a) ((integrable_bump_mul hε hh y).const_mul b)]
  refine integral_mono (integrable_bump_mul hε hh _)
    (((integrable_bump_mul hε hh x).const_mul a).add
      ((integrable_bump_mul hε hh y).const_mul b)) fun t => ?_
  have e : a • x + b • y - t = a • (x - t) + b • (y - t) := by
    have ht : t = (a + b) • t := by rw [hab, one_smul]
    nth_rewrite 1 [ht]
    rw [smul_sub, smul_sub, add_smul]
    abel
  have h1 : h (a • (x - t) + b • (y - t)) ≤ a • h (x - t) + b • h (y - t) :=
    hcv.2 (mem_univ _) (mem_univ _) ha hb hab
  simp only [smul_eq_mul] at h1
  rw [e]
  have h0 := (bump ε hε).nonneg_normed (μ := volume) t
  exact (mul_le_mul_of_nonneg_left h1 h0).trans (le_of_eq (by ring))

/-- The mollification of a continuous `L`-Lipschitz function is `L`-Lipschitz (`L ≥ 0`). -/
theorem lipschitzWith_mollify (hh : Continuous h) {L : ℝ} (hL : 0 ≤ L)
    (hlip : LipschitzWith (Real.toNNReal L) h) :
    LipschitzWith (Real.toNNReal L) (mollify h ε hε) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ hL, Real.dist_eq, mollify_apply, mollify_apply,
    ← integral_sub (integrable_bump_mul hε hh x) (integrable_bump_mul hε hh y)]
  have hb : Integrable (fun t : Fin d → ℝ => (bump ε hε).normed volume t * (L * dist x y)) :=
    ((bump ε hε).integrable_normed).mul_const _
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ t, |(bump ε hε).normed volume t * h (x - t) - (bump ε hε).normed volume t * h (y - t)|
      ≤ ∫ t, (bump ε hε).normed volume t * (L * dist x y) := by
        refine integral_mono ((integrable_bump_mul hε hh x).sub
          (integrable_bump_mul hε hh y)).abs hb fun t => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg ((bump ε hε).nonneg_normed (μ := volume) t)]
        refine mul_le_mul_of_nonneg_left ?_ ((bump ε hε).nonneg_normed (μ := volume) t)
        have := hlip.dist_le_mul (x - t) (y - t)
        rw [Real.coe_toNNReal _ hL, dist_sub_right, Real.dist_eq] at this
        exact this
    _ = L * dist x y := by rw [integral_mul_const, (bump ε hε).integral_normed, one_mul]


/-- The derivative of the mollification falls on the bump: `D(φ ⋆ h) = Dφ ⋆ h`, i.e.
`D(φ ⋆ h)(x) = ∫ h(x - t) Dφ(t) dt` (continuous `h`). -/
theorem fderiv_mollify (hh : Continuous h) :
    fderiv ℝ (mollify h ε hε) = fun x => ∫ t, (lsmul ℝ ℝ).precompL (Fin d → ℝ)
      (fderiv ℝ ((bump ε hε).normed volume) t) (h (x - t)) := by
  funext x
  unfold mollify
  rw [((bump ε hε).hasCompactSupport_normed.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    ((bump ε hε).contDiff_normed (n := 1)) hh.locallyIntegrable x).fderiv,
    convolution_def]

/-- For continuous `h`, the integrand of `fderiv_mollify` is integrable. -/
theorem integrable_fderiv_bump_apply (hh : Continuous h) (x : Fin d → ℝ) :
    Integrable (fun t => (lsmul ℝ ℝ).precompL (Fin d → ℝ)
      (fderiv ℝ ((bump ε hε).normed volume) t) (h (x - t))) := by
  have hc : Continuous (fderiv ℝ ((bump (d := d) ε hε).normed volume)) :=
    ((bump ε hε).contDiff_normed (n := 1)).continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((lsmul ℝ ℝ).precompL (Fin d → ℝ)).continuous₂.comp
      (hc.prodMk (hh.comp (continuous_const.sub continuous_id)))
  · refine ((bump ε hε).hasCompactSupport_normed (μ := volume) |>.fderiv (𝕜 := ℝ)).mono
      fun t ht => ?_
    by_contra h0
    rw [Function.notMem_support] at h0
    simp [h0] at ht

/-- **Bounded second derivative.** For continuous `L`-Lipschitz `h` (`L ≥ 0`), the second
derivative of `φ ⋆ h` is bounded: `D(φ ⋆ h) = Dφ ⋆ h` is `(L ∫ ‖Dφ‖)`-Lipschitz. -/
theorem norm_iteratedFDeriv_two_mollify_le (hh : Continuous h) {L : ℝ} (hL : 0 ≤ L)
    (hlip : LipschitzWith (Real.toNNReal L) h) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 (mollify h ε hε) x‖ ≤ C := by
  set P := (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Fin d → ℝ)
  set Dφ := fderiv ℝ ((bump (d := d) ε hε).normed volume)
  have hc : Continuous Dφ := ((bump ε hε).contDiff_normed (n := 1)).continuous_fderiv one_ne_zero
  have hDφ : Integrable fun t => ‖Dφ t‖ := by
    refine Continuous.integrable_of_hasCompactSupport hc.norm ?_
    exact ((bump ε hε).hasCompactSupport_normed (μ := volume) |>.fderiv (𝕜 := ℝ)).norm
  have hP : ∀ A c, ‖P A c‖ ≤ ‖A‖ * ‖c‖ := fun A c => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [P, precompL_apply, lsmul_apply, smul_eq_mul, norm_mul]
    have := A.le_opNorm v
    nlinarith [norm_nonneg c, norm_nonneg v]
  have hC : 0 ≤ (∫ t, ‖Dφ t‖) * L :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hL
  have hlip2 : LipschitzWith (Real.toNNReal ((∫ t, ‖Dφ t‖) * L))
      (fderiv ℝ (mollify h ε hε)) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.coe_toNNReal _ hC, fderiv_mollify hε hh, dist_eq_norm,
      ← integral_sub (integrable_fderiv_bump_apply hε hh y)
        (integrable_fderiv_bump_apply hε hh z)]
    have hb : Integrable fun t => ‖Dφ t‖ * (L * dist y z) := hDφ.mul_const _
    refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans
      (le_of_eq ?_)
    · rw [← map_sub]
      refine (hP _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := hlip.dist_le_mul (y - t) (z - t)
      rw [Real.coe_toNNReal _ hL, dist_sub_right, Real.dist_eq] at this
      rwa [Real.norm_eq_abs]
    · rw [integral_mul_const]
      ring
  refine ⟨(∫ t, ‖Dφ t‖) * L, fun x => ?_⟩
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hlip2
  rwa [Real.coe_toNNReal _ hC] at this

/-- **Bounded gradient.** For continuous `L`-Lipschitz `h` (`L ≥ 0`): `‖D(φ ⋆ h)(x)‖ ≤ L`. -/
theorem norm_fderiv_mollify_le (hh : Continuous h) {L : ℝ} (hL : 0 ≤ L)
    (hlip : LipschitzWith (Real.toNNReal L) h) (x : Fin d → ℝ) :
    ‖fderiv ℝ (mollify h ε hε) x‖ ≤ L := by
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (lipschitzWith_mollify hε hh hL hlip)
  rwa [Real.coe_toNNReal _ hL] at this

end Mollify

/-- **Smooth convex approximation.** Every convex `f : (Fin d → ℝ) → ℝ` is the pointwise limit
of functions `g n` that are convex, `C²`, with bounded first and second derivatives, and that
are all bounded below by one function `-A - B ‖x‖`, which also bounds `f` from below. The
`g n` are mollified Pasch–Hausdorff envelopes. -/
theorem exists_smooth_convex_approx {f : (Fin d → ℝ) → ℝ} (hf : ConvexOn ℝ univ f) :
    ∃ (g : ℕ → (Fin d → ℝ) → ℝ) (A B : ℝ),
      (∀ n, ConvexOn ℝ univ (g n) ∧ ContDiff ℝ 2 (g n) ∧ (∃ C, ∀ x, ‖fderiv ℝ (g n) x‖ ≤ C) ∧
        ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 (g n) x‖ ≤ C) ∧
      (∀ n x, -A - B * ‖x‖ ≤ g n x) ∧ (∀ x, -A - B * ‖x‖ ≤ f x) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
  obtain ⟨A, B, hB, hlow⟩ := exists_lowerBound_of_convexOn hf
  have hc := continuous_of_convexOn hf
  set L : ℕ → ℝ := fun n => B + 1 + n with hLdef
  have hL1 : ∀ n, 1 ≤ L n := fun n => by simp only [L]; linarith [n.cast_nonneg (α := ℝ)]
  have hBL : ∀ n, B ≤ L n := fun n => by simp only [L]; linarith [n.cast_nonneg (α := ℝ)]
  have hL0 : ∀ n, 0 ≤ L n := fun n => hB.trans (hBL n)
  set ε : ℕ → ℝ := fun n => 1 / ((n + 1) * L n) with hεdef
  have hε : ∀ n, 0 < ε n := fun n => by
    have := hL1 n
    simp only [ε]; positivity
  have hLε : ∀ n, L n * ε n = 1 / (n + 1) := fun n => by
    have := hL1 n
    simp only [ε]; field_simp
  set e : ℕ → (Fin d → ℝ) → ℝ := fun n => lipEnvelope f (L n) with hedef
  have hlip : ∀ n, LipschitzWith (Real.toNNReal (L n)) (e n) := fun n =>
    lipschitzWith_lipEnvelope hlow hB (hBL n)
  have hclose : ∀ n x, |mollify (e n) (ε n) (hε n) x - e n x| ≤ 1 / (n + 1) := fun n x => by
    rw [← hLε n]; exact abs_mollify_sub_le (hε n) (hL0 n) (hlip n) x
  refine ⟨fun n => mollify (e n) (ε n) (hε n), A + 1, B, fun n => ⟨?_, ?_, ?_, ?_⟩, ?_,
    fun x => by linarith [hlow x], fun x => ?_⟩
  · exact convexOn_mollify (hε n) (hlip n).continuous
      (convexOn_lipEnvelope hf hlow hB (hBL n))
  · exact contDiff_mollify (hε n) (hlip n).continuous
  · exact ⟨L n, norm_fderiv_mollify_le (hε n) (hlip n).continuous (hL0 n) (hlip n)⟩
  · exact norm_iteratedFDeriv_two_mollify_le (hε n) (hlip n).continuous (hL0 n) (hlip n)
  · intro n x
    have h1 := le_lipEnvelope hlow hB (hBL n) x
    have h2 := (abs_le.1 (hclose n x)).1
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    simp only [e] at h1 h2 ⊢
    linarith
  · have h1 : Tendsto (fun n => e n x) atTop (𝓝 (f x)) := tendsto_lipEnvelope hc hlow hB x
    have h2 : Tendsto (fun n => mollify (e n) (ε n) (hε n) x - e n x) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hclose n x)
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.add h2

end FormalizeSampling.ConvexSmoothing
