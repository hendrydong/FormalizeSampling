module

public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.GaussianFunctionalLSIPi
public import FormalizeSampling.Foundations.PrekopaLeindler
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Bakry–Émery on `Fin d → ℝ` for general strongly convex potentials (Bobkov–Ledoux)

Status: **Verified** (no named hypothesis).

Notation: `gradSq`, `LSIClassPi`, `FunctionalLSIPi` are those of `Foundations/LogSobolevPi.lean`;
`targetPi f ∝ e^{-f}`, `sqDist x z = ∑ᵢ (xᵢ - zᵢ)²` and `gaussPotentialPi α x = α |x|²/2` are
from `Samplers/ProximalPi.lean` and `Foundations/GibbsMeasure.lean`. The sup norm Mathlib puts on
`Fin d → ℝ` is only used through `‖v‖ ≤ √(∑ᵢ vᵢ²)`.

## Main results

* `functionalLSIPi_targetPi_of_convexOn` (**Bakry–Émery, general case**): if `α > 0` and
  `f - α |x|²/2` is convex on `Fin d → ℝ` (no product structure assumed), then
  `FunctionalLSIPi (targetPi f) (1 / α)`. Measurability of `f` is derived from convexity
  (`measurable_of_convexOn_sub`).

Route (Bobkov–Ledoux 2000, "From Brunn–Minkowski to Brascamp–Lieb and to logarithmic Sobolev
inequalities"). For `g ∈ LSIClassPi` put `φ = log g²` (bounded, Lipschitz) and
`K_s(z) = sup_x [φ x - φ z - α |x - z|² / (2 s)]` (`hjGap`).
1. `rpow_mul_rpow_le_integral_hj`: strong convexity (`le_of_convexOn_sub_gaussPotentialPi`) gives
   `(1 - s)(φ x - f x) - s f y ≤ (1 - s)(φ z + K_s z) - f z` for `z = (1 - s) x + s y`
   (`hj_pointwise`), and Prékopa–Leindler (`PrekopaLeindler.prekopa_leindler`) yields
   `(∫ e^{φ} e^{-f})^{1-s} (∫ e^{-f})^s ≤ ∫ e^{(1-s)(φ + K_s)} e^{-f}` for `0 < s < 1`.
2. `tendsto_hjGap_div`: `K_s(z) / s → |∇φ(z)|² / (2 α)` as `s → 0⁺`; with the uniform bounds
   `0 ≤ K_s ≤ s L² / (2 α)` and dominated convergence, `tendsto_integral_exp_hj_slope` computes
   the right derivative at `s = 0` of the right-hand side.
3. `mul_log_sub_log_le`: comparing the two right derivatives at `s = 0` (equality at `s = 0`)
   gives `A (log Z - log A) ≤ ∫ e^{φ} (|∇φ|²/(2α) - φ) e^{-f}`, which is exactly
   `Ent_π(g²) ≤ (2/α) ∫ |∇g|² dπ` after `e^{φ} = g²`, `e^{φ} |∇φ|² = 4 |∇g|²`.

Auxiliary: `abs_clm_apply_le` (Cauchy–Schwarz for linear functionals), `sub_le_of_gradSq_le`
(Euclidean Lipschitz bound from `gradSq ≤ L²`), `integral_targetPi_eq`.

## Not proved here

* LSI for targets that are only log-concave (`α = 0`), or with `f` convex only on a subset.
* The Γ₂ / semigroup proof and Caffarelli's contraction theorem in dimension `d ≥ 2` (not
  needed: the Bobkov–Ledoux route goes through Prékopa–Leindler).
* Test functions outside `LSIClassPi` (e.g. unbounded or not bounded below); see
  `LogSobolevExtensionPi` for the extensions available from the class.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FormalizeSampling.BakryEmeryGeneralPi

open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevPi
open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi

variable {d : ℕ}

/-- Cauchy–Schwarz for a linear functional on `Fin d → ℝ`:
`|L v| ≤ √(∑ᵢ (L eᵢ)²) √(∑ᵢ vᵢ²)`. -/
theorem abs_clm_apply_le (L : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ) :
    |L v| ≤ √(∑ i, L (Pi.single i 1) ^ 2) * √(∑ i, v i ^ 2) := by
  have hL : L v = ∑ i, L (Pi.single i 1) * v i := by
    conv_lhs => rw [GaussianFunctionalLSIPi.eq_dotCLM_apply_single L]
    rw [HeatFlowDeBruijnPi.dotCLM_apply, dotProduct]
  rw [hL, ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- A linear functional evaluated on its own gradient vector:
`L (∑ᵢ (L eᵢ) eᵢ) = ∑ᵢ (L eᵢ)²`. -/
theorem clm_apply_grad (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    L (fun i => L (Pi.single i 1)) = ∑ i, L (Pi.single i 1) ^ 2 := by
  conv_lhs => rw [GaussianFunctionalLSIPi.eq_dotCLM_apply_single L]
  rw [HeatFlowDeBruijnPi.dotCLM_apply, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [HeatFlowDeBruijnPi.dotCLM_single, sq]

/-- The sup norm on `Fin d → ℝ` is at most the Euclidean norm `√(∑ᵢ vᵢ²)`. -/
theorem norm_le_sqrt_sum_sq (v : Fin d → ℝ) : ‖v‖ ≤ √(∑ i, v i ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- **Euclidean Lipschitz bound from a gradient bound.** If `φ` is differentiable with
`gradSq φ ≤ L²` (`L ≥ 0`), then `φ x - φ z ≤ L √|x - z|²`. -/
theorem sub_le_of_gradSq_le {φ : (Fin d → ℝ) → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x, gradSq φ x ≤ L ^ 2) (x z : Fin d → ℝ) :
    φ x - φ z ≤ L * √(sqDist x z) := by
  set v : Fin d → ℝ := x - z
  have hv : sqDist x z = ∑ i, v i ^ 2 := rfl
  set ψ : ℝ → ℝ := fun τ => φ (z + τ • v)
  have hψ : ∀ τ, HasDerivAt ψ (fderiv ℝ φ (z + τ • v) v) τ := fun τ => by
    have h1 : HasDerivAt (fun τ : ℝ => z + τ • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add z
    exact (hφ _).hasFDerivAt.comp_hasDerivAt τ h1
  have hb : ∀ τ ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ φ (z + τ • v) v‖ ≤ L * √(sqDist x z) := by
    intro τ _
    rw [Real.norm_eq_abs, hv]
    refine (abs_clm_apply_le _ v).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    rw [← Real.sqrt_sq hL0]
    exact Real.sqrt_le_sqrt (hL _)
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun τ _ => (hψ τ).hasDerivWithinAt) hb
  have e1 : ψ 1 = φ x := by simp [ψ, v]
  have e0 : ψ 0 = φ z := by simp [ψ]
  rw [e1, e0, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this


/-! ### The Hamilton–Jacobi gap -/

/-- The Hamilton–Jacobi gap `K_s(z) = sup_x [φ x - φ z - α |x - z|² / (2 s)]` (a sup-convolution
of `φ` with a Gaussian kernel, shifted by `φ z`). -/
noncomputable def hjGap (φ : (Fin d → ℝ) → ℝ) (α s : ℝ) (z : Fin d → ℝ) : ℝ :=
  ⨆ x, (φ x - φ z - α / (2 * s) * sqDist x z)

/-- Young's inequality in the form `L r - α r² / (2 s) ≤ s L² / (2 α)` (`α, s > 0`). -/
theorem mul_sub_div_mul_sq_le {L α s r : ℝ} (hα : 0 < α) (hs : 0 < s) :
    L * r - α / (2 * s) * r ^ 2 ≤ s * L ^ 2 / (2 * α) := by
  rw [← sub_nonneg]
  have : s * L ^ 2 / (2 * α) - (L * r - α / (2 * s) * r ^ 2)
      = (α * r - s * L) ^ 2 / (2 * α * s) := by
    field_simp; ring
  rw [this]; positivity

section HJ

variable {φ : (Fin d → ℝ) → ℝ} {L α s : ℝ}

/-- Each term of the Hamilton–Jacobi supremum is at most `s L² / (2 α)` when
`φ x - φ z ≤ L √|x - z|²`. -/
theorem hjTerm_le (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α) (hs : 0 < s)
    (x z : Fin d → ℝ) : φ x - φ z - α / (2 * s) * sqDist x z ≤ s * L ^ 2 / (2 * α) := by
  have h := mul_sub_div_mul_sq_le (L := L) (r := √(sqDist x z)) hα hs
  rw [Real.sq_sqrt (sqDist_nonneg x z)] at h
  linarith [hLip x z]

/-- The Hamilton–Jacobi supremum is bounded above (under the Lipschitz bound). -/
theorem bddAbove_hjTerm (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α)
    (hs : 0 < s) (z : Fin d → ℝ) :
    BddAbove (range fun x => φ x - φ z - α / (2 * s) * sqDist x z) :=
  ⟨_, forall_mem_range.2 fun x => hjTerm_le hLip hα hs x z⟩

/-- Every term is below the Hamilton–Jacobi gap. -/
theorem le_hjGap (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α) (hs : 0 < s)
    (x z : Fin d → ℝ) : φ x - φ z - α / (2 * s) * sqDist x z ≤ hjGap φ α s z :=
  le_ciSup (bddAbove_hjTerm hLip hα hs z) x

/-- The Hamilton–Jacobi gap is nonnegative (take `x = z`). -/
theorem hjGap_nonneg (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α) (hs : 0 < s)
    (z : Fin d → ℝ) : 0 ≤ hjGap φ α s z := by
  have h := le_hjGap hLip hα hs z z
  simpa [sqDist] using h

/-- The Hamilton–Jacobi gap is at most `s L² / (2 α)`. -/
theorem hjGap_le (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α) (hs : 0 < s)
    (z : Fin d → ℝ) : hjGap φ α s z ≤ s * L ^ 2 / (2 * α) :=
  ciSup_le fun x => hjTerm_le hLip hα hs x z

/-- The Hamilton–Jacobi gap of a continuous `φ` is measurable (it is lower semicontinuous). -/
theorem measurable_hjGap (hφ : Continuous φ) (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z))
    (hα : 0 < α) (hs : 0 < s) : Measurable (hjGap φ α s) := by
  refine (lowerSemicontinuous_ciSup (bddAbove_hjTerm hLip hα hs) fun x => ?_).measurable
  refine Continuous.lowerSemicontinuous ?_
  unfold sqDist
  fun_prop

/-- Squeeze along `s → 0⁺` with an auxiliary parameter: if for every `ε > 0` eventually
`lo ε ≤ F s ≤ hi ε`, and `lo, hi → ℓ` as `ε → 0⁺`, then `F s → ℓ`. -/
theorem tendsto_of_forall_eps {F lo hi : ℝ → ℝ} {ℓ : ℝ}
    (hlo : Tendsto lo (𝓝[>] 0) (𝓝 ℓ)) (hhi : Tendsto hi (𝓝[>] 0) (𝓝 ℓ))
    (h : ∀ ε > 0, ∀ᶠ s in 𝓝[>] 0, lo ε ≤ F s ∧ F s ≤ hi ε) :
    Tendsto F (𝓝[>] 0) (𝓝 ℓ) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨ε, h1, h2⟩ := ((hlo.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    exact (h ε h2).mono fun s hs => h1.trans_le hs.1
  · obtain ⟨ε, h1, h2⟩ := ((hhi.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    exact (h ε h2).mono fun s hs => hs.2.trans_lt h1

/-- **First-order behaviour of the Hamilton–Jacobi gap.** If `φ` is differentiable at `z` and
`φ x - φ z ≤ L √|x - z|²` everywhere, then `K_s(z) / s → |∇φ(z)|² / (2 α)` as `s → 0⁺`. -/
theorem tendsto_hjGap_div (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hL0 : 0 ≤ L)
    (hα : 0 < α) {z : Fin d → ℝ} (hφz : DifferentiableAt ℝ φ z) :
    Tendsto (fun s => hjGap φ α s z / s) (𝓝[>] 0) (𝓝 (gradSq φ z / (2 * α))) := by
  set D := fderiv ℝ φ z with hD
  set G := √(gradSq φ z) with hGdef
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hGsq : G ^ 2 = gradSq φ z := Real.sq_sqrt (gradSq_nonneg _ _)
  have hGD : G = √(∑ i, D (Pi.single i 1) ^ 2) := rfl
  refine tendsto_of_forall_eps (lo := fun ε => (G ^ 2 - 2 * ε * G) / (2 * α))
    (hi := fun ε => (G + ε) ^ 2 / (2 * α)) ?_ ?_ fun ε hε => ?_
  · have : Continuous fun ε : ℝ => (G ^ 2 - 2 * ε * G) / (2 * α) := by fun_prop
    simpa [hGsq] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  · have : Continuous fun ε : ℝ => (G + ε) ^ 2 / (2 * α) := by fun_prop
    simpa [hGsq] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hφz.hasFDerivAt).def hε
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.1 hlo
  have hs₀ : 0 < α * r / (2 * L + G + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hs₀] with s ⟨hs, hss⟩
  have hsr : s * (2 * L + G + 1) < α * r := by
    rwa [lt_div_iff₀ (by positivity)] at hss
  constructor
  · -- lower bound: test `x = z + (s/α) ∇φ(z)`
    rw [le_div_iff₀ hs]
    set δ : Fin d → ℝ := (s / α) • fun i => D (Pi.single i 1) with hδ
    have hsα : 0 ≤ s / α := by positivity
    have hδsq : ∑ i, δ i ^ 2 = (s / α) ^ 2 * G ^ 2 := by
      rw [hGsq, gradSq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [hδ, mul_pow, hD]
    have hδn : √(∑ i, δ i ^ 2) = s / α * G := by
      rw [hδsq, ← mul_pow, Real.sqrt_sq (by positivity)]
    have hDδ : D δ = s / α * G ^ 2 := by
      rw [hδ, map_smul, clm_apply_grad, smul_eq_mul, hGsq, gradSq]
    have hδr : dist δ 0 < r := by
      rw [dist_zero_right]
      refine (norm_le_sqrt_sum_sq δ).trans_lt ?_
      rw [hδn, div_mul_eq_mul_div, div_lt_iff₀ hα]
      nlinarith
    have h1 := hrb hδr
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖δ‖ ≤ s / α * G := (norm_le_sqrt_sum_sq δ).trans hδn.le
    have h3 := le_hjGap hLip hα hs (z + δ) z
    have h4 : sqDist (z + δ) z = (s / α) ^ 2 * G ^ 2 := by
      rw [← hδsq, sqDist]; simp
    rw [h4] at h3
    have h5 : φ (z + δ) - φ z ≥ s / α * G ^ 2 - ε * (s / α * G) := by
      have := (abs_le.1 h1).1
      nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
    have h6 : (G ^ 2 - 2 * ε * G) / (2 * α) * s
        = s / α * G ^ 2 - ε * (s / α * G) - α / (2 * s) * ((s / α) ^ 2 * G ^ 2) := by
      field_simp; ring
    rw [h6]; linarith
  · -- upper bound
    rw [div_le_iff₀ hs]
    refine ciSup_le fun x => ?_
    set ρ := √(sqDist x z) with hρ
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρsq : sqDist x z = ρ ^ 2 := (Real.sq_sqrt (sqDist_nonneg x z)).symm
    rw [hρsq]
    rcases lt_or_ge ρ r with hρr | hρr
    · have hxz : dist (x - z) 0 < r := by
        rw [dist_zero_right]; exact (norm_le_sqrt_sum_sq _).trans_lt hρr
      have h1 := hrb hxz
      rw [add_sub_cancel, Real.norm_eq_abs] at h1
      have h2 : ‖x - z‖ ≤ ρ := norm_le_sqrt_sum_sq _
      have h3 : D (x - z) ≤ G * ρ := by
        have := abs_clm_apply_le D (x - z)
        exact (le_abs_self _).trans this
      have h4 : φ x - φ z ≤ (G + ε) * ρ := by
        have := (abs_le.1 h1).2
        nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
      have h5 := mul_sub_div_mul_sq_le (L := G + ε) (r := ρ) hα hs
      have h6 : (G + ε) ^ 2 / (2 * α) * s = s * (G + ε) ^ 2 / (2 * α) := by ring
      rw [h6]; linarith
    · have h1 := hLip x z
      rw [← hρ] at h1
      have h2 : L * ρ ≤ α / (2 * s) * ρ ^ 2 := by
        have : 2 * s * L ≤ α * ρ := by nlinarith
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : 0 ≤ (G + ε) ^ 2 / (2 * α) * s := by positivity
      linarith

/-- `|a s z| ≤ s (L² / (2 α) + M)` for `a = (1 - s)(φ + K_s) - φ`, `0 < s < 1`, `|φ| ≤ M`. -/
theorem abs_hjShift_le (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α) (hs : 0 < s)
    (hs1 : s < 1) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) (z : Fin d → ℝ) :
    |(1 - s) * (φ z + hjGap φ α s z) - φ z| ≤ s * (L ^ 2 / (2 * α) + M) := by
  have h0 := hjGap_nonneg hLip hα hs z
  have h1 := hjGap_le hLip hα hs z
  have h2 := abs_le.1 (hM z)
  have h3 : (1 - s) * hjGap φ α s z ≤ s * L ^ 2 / (2 * α) :=
    (mul_le_of_le_one_left h0 (by linarith)).trans h1
  have h4 : 0 ≤ (1 - s) * hjGap φ α s z := mul_nonneg (by linarith) h0
  have h5 : s * L ^ 2 / (2 * α) = s * (L ^ 2 / (2 * α)) := by ring
  rw [abs_le]
  constructor <;> nlinarith

/-- **Derivative of the Hamilton–Jacobi integral at `s = 0⁺`.** Let `φ` be differentiable with
`|φ| ≤ M` and `φ x - φ z ≤ L √|x - z|²`, `α > 0`, and `w ≥ 0` integrable. With
`H_s = (1 - s)(φ + K_s)`,
`(∫ e^{H_s} w - ∫ e^{φ} w) / s → ∫ e^{φ} (|∇φ|² / (2 α) - φ) w` as `s → 0⁺`. -/
theorem tendsto_integral_exp_hj_slope (hφ : Differentiable ℝ φ)
    (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hL0 : 0 ≤ L) (hα : 0 < α) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) {w : (Fin d → ℝ) → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwi : Integrable w) :
    Tendsto (fun s => ((∫ z, Real.exp ((1 - s) * (φ z + hjGap φ α s z)) * w z)
        - ∫ z, Real.exp (φ z) * w z) / s) (𝓝[>] 0)
      (𝓝 (∫ z, Real.exp (φ z) * (gradSq φ z / (2 * α) - φ z) * w z)) := by
  set C₁ := L ^ 2 / (2 * α) + M with hC₁
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hC₁0 : 0 ≤ C₁ := by positivity
  set a : ℝ → (Fin d → ℝ) → ℝ := fun s z => (1 - s) * (φ z + hjGap φ α s z) - φ z with ha
  set F : ℝ → (Fin d → ℝ) → ℝ := fun s z =>
    (Real.exp ((1 - s) * (φ z + hjGap φ α s z)) * w z - Real.exp (φ z) * w z) / s with hF
  have hs₀ : (0 : ℝ) < min 1 (1 / (C₁ + 1)) := lt_min one_pos (by positivity)
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (min 1 (1 / (C₁ + 1))) := Ioo_mem_nhdsGT hs₀
  have hint : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ (c : (Fin d → ℝ) → ℝ), Measurable c →
      (∀ z, |c z| ≤ C₁ + M + 1) → Integrable fun z => Real.exp (c z) * w z := by
    intro s _ c hc hcb
    refine hwi.bdd_mul (c := Real.exp (C₁ + M + 1))
      (Real.measurable_exp.comp hc).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hcb z))
  have hφc : Continuous φ := hφ.continuous
  have hHm : ∀ s, 0 < s → Measurable fun z => (1 - s) * (φ z + hjGap φ α s z) := fun s hs =>
    measurable_const.mul (hφc.measurable.add (measurable_hjGap hφc hLip hα hs))
  have hHb : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, |(1 - s) * (φ z + hjGap φ α s z)| ≤ C₁ + M + 1 := by
    intro s hs z
    have h1 := abs_hjShift_le hLip hα hs.1 hs.2 hM z
    have h2 := abs_le.1 (hM z)
    have h3 : s * C₁ ≤ C₁ := mul_le_of_le_one_left hC₁0 hs.2.le
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith
  -- the integrals as one integral
  have hcongr : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫ z, F s z = ((∫ z, Real.exp ((1 - s) *
      (φ z + hjGap φ α s z)) * w z) - ∫ z, Real.exp (φ z) * w z) / s := by
    filter_upwards [hev] with s hs
    have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
    have i1 : Integrable fun z => Real.exp ((1 - s) * (φ z + hjGap φ α s z)) * w z :=
      hint s hs1 _ (hHm s hs.1) (hHb s hs1)
    have i2 : Integrable fun z => Real.exp (φ z) * w z :=
      hint s hs1 _ hφc.measurable fun z => by linarith [hM z]
    rw [← integral_sub i1 i2, ← integral_div]
  refine Tendsto.congr' hcongr ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => Real.exp M * (2 * C₁) * w z) ?_ ?_ (hwi.const_mul _) ?_
  · filter_upwards [hev] with s hs
    exact (((Real.measurable_exp.comp (hHm s hs.1)).mul hwm).sub
      ((Real.measurable_exp.comp hφc.measurable).mul hwm)).div_const _ |>.aestronglyMeasurable
  · filter_upwards [hev] with s hs
    refine ae_of_all _ fun z => ?_
    have hs1 : s < 1 := hs.2.trans_le (min_le_left _ _)
    have hsC : s * (C₁ + 1) ≤ 1 := by
      have := hs.2.le.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    have h1 := abs_hjShift_le hLip hα hs.1 hs1 hM z
    have h2 : |a s z| ≤ 1 := h1.trans (by nlinarith)
    have h3 := Real.abs_exp_sub_one_le h2
    have he : F s z = Real.exp (φ z) * (Real.exp (a s z) - 1) * w z / s := by
      simp only [hF, ha, Real.exp_sub]
      field_simp
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hs.1, div_le_iff₀ hs.1, abs_mul, abs_mul,
      Real.abs_exp, abs_of_nonneg (hw0 z)]
    have h4 : Real.exp (φ z) ≤ Real.exp M := Real.exp_le_exp.2 ((le_abs_self _).trans (hM z))
    have h5 : |Real.exp (a s z) - 1| ≤ 2 * C₁ * s := by
      have : |a s z| ≤ s * C₁ := h1
      nlinarith
    calc Real.exp (φ z) * |Real.exp (a s z) - 1| * w z
        ≤ Real.exp M * (2 * C₁ * s) * w z :=
          mul_le_mul_of_nonneg_right (mul_le_mul h4 h5 (abs_nonneg _) (Real.exp_pos _).le)
            (hw0 z)
      _ = Real.exp M * (2 * C₁) * w z * s := by ring
  · refine ae_of_all _ fun z => ?_
    have hK := tendsto_hjGap_div hLip hL0 hα (hφ z)
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hdiv : Tendsto (fun s => a s z / s) (𝓝[>] 0)
        (𝓝 (gradSq φ z / (2 * α) - φ z)) := by
      have : Tendsto (fun s => (1 - s) * (hjGap φ α s z / s) - φ z) (𝓝[>] 0)
          (𝓝 ((1 - 0) * (gradSq φ z / (2 * α)) - φ z)) :=
        ((tendsto_const_nhds.sub hid).mul hK).sub tendsto_const_nhds
      rw [sub_zero, one_mul] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [ha]
      field_simp [ne_of_gt (show (0 : ℝ) < s from hs)]
      ring
    have ha0 : Tendsto (fun s => a s z) (𝓝[>] 0) (𝓝 0) := by
      have := hid.mul hdiv
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      field_simp [ne_of_gt (show (0 : ℝ) < s from hs)]
    have hdsl : Tendsto (fun s => dslope Real.exp 0 (a s z)) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (dslope Real.exp 0) 0 :=
        continuousAt_dslope_same.2 Real.differentiableAt_exp
      have := hc.tendsto.comp ha0
      rwa [dslope_same, Real.deriv_exp, Real.exp_zero] at this
    have hlim := ((tendsto_const_nhds (x := Real.exp (φ z))).mul (hdsl.mul hdiv)).mul
      (tendsto_const_nhds (x := w z))
    rw [one_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hd := sub_smul_dslope Real.exp 0 (a s z)
    rw [sub_zero, smul_eq_mul, Real.exp_zero] at hd
    have he : Real.exp ((1 - s) * (φ z + hjGap φ α s z)) = Real.exp (φ z) * Real.exp (a s z) := by
      rw [← Real.exp_add]; congr 1; simp only [ha]; ring
    have hd' : Real.exp (a s z) = a s z * dslope Real.exp 0 (a s z) + 1 := by linarith
    simp only [hF, he]
    rw [hd']
    field_simp
    ring

end HJ

/-! ### Strong convexity and the Prékopa–Leindler step -/

section PL

variable {f φ : (Fin d → ℝ) → ℝ} {α L : ℝ}

/-- Strong convexity in two-point form: if `f - α |x|²/2` is convex and `0 ≤ s ≤ 1`, then
`f((1 - s) x + s y) ≤ (1 - s) f x + s f y - (α/2) (1 - s) s |x - y|²`. -/
theorem le_of_convexOn_sub_gaussPotentialPi
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (x y : Fin d → ℝ) :
    f ((1 - s) • x + s • y)
      ≤ (1 - s) * f x + s * f y - α / 2 * (1 - s) * s * ∑ i, (x i - y i) ^ 2 := by
  have h := hconv.2 (mem_univ x) (mem_univ y) (sub_nonneg.2 hs1) hs0 (by ring)
  simp only [smul_eq_mul, gaussPotentialPi_apply] at h
  have key : α * (∑ i, ((1 - s) • x + s • y) i ^ 2) / 2
      = (1 - s) * (α * (∑ i, x i ^ 2) / 2) + s * (α * (∑ i, y i ^ 2) / 2)
        - α / 2 * (1 - s) * s * ∑ i, (x i - y i) ^ 2 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- The pointwise inequality behind the Prékopa–Leindler step: for `z = (1 - s) x + s y`,
`(1 - s)(φ x - f x) + s (-f y) ≤ (1 - s)(φ z + K_s(z)) - f z`. -/
theorem hj_pointwise (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x)
    (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hα : 0 < α) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (x y : Fin d → ℝ) :
    (φ x - f x) * (1 - s) + -f y * s
      ≤ (1 - s) * (φ ((1 - s) • x + s • y) + hjGap φ α s ((1 - s) • x + s • y))
        - f ((1 - s) • x + s • y) := by
  set z := (1 - s) • x + s • y with hz
  have h1 := le_of_convexOn_sub_gaussPotentialPi hconv hs0.le hs1.le x y
  have h2 := le_hjGap hLip hα hs0 x z
  have hD : sqDist x z = s ^ 2 * ∑ i, (x i - y i) ^ 2 := by
    rw [sqDist, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hD] at h2
  have h3 : α / (2 * s) * (s ^ 2 * ∑ i, (x i - y i) ^ 2)
      = α / 2 * s * ∑ i, (x i - y i) ^ 2 := by field_simp
  rw [h3] at h2
  have h4 : 0 ≤ 1 - s := by linarith
  have h5 := mul_le_mul_of_nonneg_left h2 h4
  nlinarith

/-- **Prékopa–Leindler applied to the Hamilton–Jacobi sup-convolution.** If `f - α|x|²/2` is
convex, `e^{-f}` is integrable, `φ` is differentiable with `|φ| ≤ M` and
`φ x - φ z ≤ L √|x - z|²`, then for `0 < s < 1`
`(∫ e^{φ} e^{-f})^{1-s} (∫ e^{-f})^s ≤ ∫ e^{(1-s)(φ + K_s)} e^{-f}`. -/
theorem rpow_mul_rpow_le_integral_hj (hf : Measurable f)
    (hint : Integrable fun x => Real.exp (-f x))
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) (hα : 0 < α)
    (hφ : Differentiable ℝ φ) (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ z, Real.exp (φ z) * Real.exp (-f z)) ^ (1 - s) * (∫ z, Real.exp (-f z)) ^ s
      ≤ ∫ z, Real.exp ((1 - s) * (φ z + hjGap φ α s z)) * Real.exp (-f z) := by
  have hφc : Continuous φ := hφ.continuous
  set H : (Fin d → ℝ) → ℝ := fun z => (1 - s) * (φ z + hjGap φ α s z) with hH
  have hHm : Measurable H :=
    measurable_const.mul (hφc.measurable.add (measurable_hjGap hφc hLip hα hs0))
  have hHb : ∀ z, |H z| ≤ s * (L ^ 2 / (2 * α) + M) + M := fun z => by
    have h1 := abs_hjShift_le hLip hα hs0 hs1 hM z
    calc |H z| = |((1 - s) * (φ z + hjGap φ α s z) - φ z) + φ z| := by simp [hH]
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 (hM z))
  have hintb : ∀ c : (Fin d → ℝ) → ℝ, Measurable c → ∀ B, (∀ z, |c z| ≤ B) →
      Integrable fun z => Real.exp (c z) * Real.exp (-f z) := fun c hc B hcb =>
    hint.bdd_mul (c := Real.exp B) (Real.measurable_exp.comp hc).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Real.abs_exp]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hcb z)))
  have iu := hintb φ hφc.measurable M hM
  have iw := hintb H hHm _ hHb
  have hPL := PrekopaLeindler.prekopa_leindler (d := d) (t := 1 - s) (by linarith) (by linarith)
    (u := fun x => ENNReal.ofReal (Real.exp (φ x) * Real.exp (-f x)))
    (v := fun x => ENNReal.ofReal (Real.exp (-f x)))
    (w := fun x => ENNReal.ofReal (Real.exp (H x) * Real.exp (-f x)))
    ((Real.measurable_exp.comp hφc.measurable).mul
      (Real.measurable_exp.comp hf.neg)).ennreal_ofReal
    (Real.measurable_exp.comp hf.neg).ennreal_ofReal
    ((Real.measurable_exp.comp hHm).mul (Real.measurable_exp.comp hf.neg)).ennreal_ofReal
    (fun x y => by
      rw [sub_sub_cancel, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0.le, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add,
        Real.exp_le_exp]
      have := hj_pointwise hconv hLip hα hs0 hs1 x y
      simp only [hH]
      linarith)
  rw [sub_sub_cancel] at hPL
  rw [← ofReal_integral_eq_lintegral_ofReal iu (ae_of_all _ fun _ => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal iw (ae_of_all _ fun _ => by positivity),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => by positivity) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => by positivity) hs0.le,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => by positivity)] at hPL
  exact hPL

/-- **The Bobkov–Ledoux limit `s → 0⁺`.** Under the hypotheses of
`rpow_mul_rpow_le_integral_hj` (and `L ≥ 0`), with `A = ∫ e^{φ} e^{-f}`, `Z = ∫ e^{-f}`:
`A (log Z - log A) ≤ ∫ e^{φ} (|∇φ|² / (2 α) - φ) e^{-f}`. -/
theorem mul_log_sub_log_le (hf : Measurable f) (hint : Integrable fun x => Real.exp (-f x))
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) (hα : 0 < α)
    (hφ : Differentiable ℝ φ) (hLip : ∀ x z, φ x - φ z ≤ L * √(sqDist x z)) (hL0 : 0 ≤ L)
    {M : ℝ} (hM : ∀ x, |φ x| ≤ M) :
    (∫ z, Real.exp (φ z) * Real.exp (-f z)) *
        (Real.log (∫ z, Real.exp (-f z)) - Real.log (∫ z, Real.exp (φ z) * Real.exp (-f z)))
      ≤ ∫ z, Real.exp (φ z) * (gradSq φ z / (2 * α) - φ z) * Real.exp (-f z) := by
  set A := ∫ z, Real.exp (φ z) * Real.exp (-f z) with hAdef
  set Z := ∫ z, Real.exp (-f z) with hZdef
  have hZ : 0 < Z := targetNormalizerPi_pos hint
  have hiu : Integrable fun z => Real.exp (φ z) * Real.exp (-f z) :=
    hint.bdd_mul (c := Real.exp M)
      (Real.measurable_exp.comp hφ.continuous.measurable).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Real.abs_exp]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hM z)))
  have hA : 0 < A := by
    have h1 : ∫ z, Real.exp (-M) * Real.exp (-f z) ≤ A :=
      integral_mono (hint.const_mul _) hiu fun z => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (by linarith [neg_abs_le (φ z), hM z])) (Real.exp_pos _).le
    rw [integral_const_mul] at h1
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hZ) h1
  have hT := tendsto_integral_exp_hj_slope hφ hLip hL0 hα hM (w := fun z => Real.exp (-f z))
    (Real.measurable_exp.comp hf.neg) (fun _ => (Real.exp_pos _).le) hint
  set c := Real.log Z - Real.log A
  have hq : HasDerivAt (fun s : ℝ => Real.exp (Real.log A + s * c))
      (Real.exp (Real.log A + 0 * c) * (1 * c)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add _).exp
  rw [zero_mul, add_zero, Real.exp_log hA, one_mul] at hq
  have hS := hq.tendsto_slope_zero_right
  refine le_of_tendsto_of_tendsto hS hT ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  have hpl := rpow_mul_rpow_le_integral_hj hf hint hconv hα hφ hLip hM hs.1 hs.2
  have hpe : A ^ (1 - s) * Z ^ s = Real.exp (Real.log A + (0 + s) * c) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hZ, ← Real.exp_add]
    congr 1
    ring
  have hp0 : Real.exp (Real.log A + 0 * c) = A := by rw [zero_mul, add_zero, Real.exp_log hA]
  simp only [smul_eq_mul]
  rw [hp0, ← hpe, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hpl _) hs.1.le

end PL

/-! ### Bakry–Émery on `Fin d → ℝ` -/

/-- **Strong convexity implies measurability.** If `f - α |x|²/2` is convex on all of
`Fin d → ℝ`, then `f` is measurable (indeed continuous: a real convex function on the whole
finite-dimensional space is continuous, and `α |x|²/2` is continuous). Hence a `Measurable f`
hypothesis next to such a convexity hypothesis is redundant. -/
theorem measurable_of_convexOn_sub {f : (Fin d → ℝ) → ℝ} {α : ℝ}
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) : Measurable f :=
  ProximalGeneralLSI.measurable_of_convexOn_sub
    (ProximalGeneralLSIPi.continuous_gaussPotentialPi α) hconv

/-- Integrals against `targetPi f`: `∫ F dπ = (∫ F e^{-f}) / ∫ e^{-f}`. -/
theorem integral_targetPi_eq {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (F : (Fin d → ℝ) → ℝ) :
    ∫ x, F x ∂targetPi f = (∫ x, F x * Real.exp (-f x)) / ∫ x, Real.exp (-f x) := by
  rw [targetPi, MeasureHelpers.integral_withDensity_ofReal (measurable_targetDensityPi hf)
    (fun x => targetDensityPi_nonneg x), ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [targetDensityPi, targetNormalizerPi]
  ring

/-- **Bakry–Émery on `Fin d → ℝ` (general, non-separable potentials).** If `α > 0` and
`f - α |x|²/2` is convex on `Fin d → ℝ` (no separate measurability assumption: convexity on the
whole space makes `f` continuous, see `measurable_of_convexOn_sub`), then the target `π ∝ e^{-f}`
satisfies the functional log-Sobolev inequality with constant `1/α`:
`Ent_π(g²) ≤ (2/α) ∫ ‖∇g‖² dπ` for every `g ∈ LSIClassPi`. Proof: Bobkov–Ledoux
(Prékopa–Leindler applied to the Hamilton–Jacobi sup-convolution of `φ = log g²`, then
`s → 0⁺`). -/
theorem functionalLSIPi_targetPi_of_convexOn {f : (Fin d → ℝ) → ℝ} {α : ℝ} (hα : 0 < α)
    (hconv : ConvexOn ℝ univ fun x => f x - gaussPotentialPi α x) :
    FunctionalLSIPi (targetPi f) (1 / α) := by
  intro g hg
  obtain ⟨hgd, ⟨M₀, hM₀⟩, ⟨K, hK⟩, c, hc, hcg⟩ := hg
  have hf : Measurable f := measurable_of_convexOn_sub hconv
  have hint := (ProximalGeneralLSIPi.exists_envelope_of_strongConvexPi hα hconv).1
  have hgpos : ∀ x, 0 < g x := fun x => hc.trans_le (hcg x)
  have hgM : ∀ x, g x ≤ M₀ := fun x => (le_abs_self _).trans (hM₀ x)
  have hK0 : 0 ≤ K := (gradSq_nonneg g 0).trans (hK 0)
  set φ : (Fin d → ℝ) → ℝ := fun x => 2 * Real.log (g x) with hφdef
  have hφd : ∀ x, HasFDerivAt φ ((2 : ℝ) • ((g x)⁻¹ • fderiv ℝ g x)) x := fun x =>
    (((hgd x).hasFDerivAt.log (hgpos x).ne').const_mul 2)
  have hφ : Differentiable ℝ φ := fun x => (hφd x).differentiableAt
  have hgradφ : ∀ x, gradSq φ x = 4 * gradSq g x / g x ^ 2 := fun x => by
    rw [gradSq, gradSq, (hφd x).fderiv, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [(hgpos x).ne']
    ring
  set L := 2 * √K / c with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hL : ∀ x, gradSq φ x ≤ L ^ 2 := fun x => by
    rw [hgradφ, hLdef, div_pow, mul_pow, Real.sq_sqrt hK0]
    have h1 : c ^ 2 ≤ g x ^ 2 := pow_le_pow_left₀ hc.le (hcg x) 2
    rw [div_le_div_iff₀ (pow_pos (hgpos x) 2) (pow_pos hc 2)]
    have := hK x
    nlinarith [gradSq_nonneg g x]
  have hLip := sub_le_of_gradSq_le hφ hL0 hL
  have hM : ∀ x, |φ x| ≤ 2 * (|Real.log c| + |Real.log M₀|) := fun x => by
    have h1 : Real.log c ≤ Real.log (g x) := Real.log_le_log hc (hcg x)
    have h2 : Real.log (g x) ≤ Real.log M₀ := Real.log_le_log (hgpos x) (hgM x)
    simp only [hφdef, abs_mul, abs_two]
    gcongr
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log M₀),
      abs_nonneg (Real.log c), abs_nonneg (Real.log M₀)]
  have key := mul_log_sub_log_le hf hint hconv hα hφ hLip hL0 hM
  have hexp : ∀ x, Real.exp (φ x) = g x ^ 2 := fun x => by
    simp only [hφdef]
    rw [show (2 : ℝ) * Real.log (g x) = Real.log (g x ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos (hgpos x) 2)]
  have hlog : ∀ x, Real.log (g x ^ 2) = φ x := fun x => by
    simp only [hφdef, Real.log_pow]; norm_num
  -- rewrite the integrand of `key`
  have hpt : ∀ z, Real.exp (φ z) * (gradSq φ z / (2 * α) - φ z) * Real.exp (-f z)
      = 2 / α * (gradSq g z * Real.exp (-f z))
        - g z ^ 2 * Real.log (g z ^ 2) * Real.exp (-f z) := fun z => by
    rw [hexp, hgradφ, hlog]
    field_simp [(hgpos z).ne']
    ring
  simp only [hpt] at key
  simp only [hexp] at key
  -- integrability
  have hbd : ∀ F : (Fin d → ℝ) → ℝ, Measurable F → ∀ B, (∀ x, |F x| ≤ B) →
      Integrable fun x => F x * Real.exp (-f x) := fun F hF B hB =>
    hint.bdd_mul (c := B) hF.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have hgm : Measurable g := hgd.continuous.measurable
  have hg2 : ∀ x, |g x ^ 2| ≤ M₀ ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM₀ x) 2
  have i1 := hbd (fun x => gradSq g x) (LogSobolevPi.measurable_gradSq g) K
    fun x => by rw [abs_of_nonneg (gradSq_nonneg g x)]; exact hK x
  have i2 := hbd (fun x => g x ^ 2 * Real.log (g x ^ 2)) (by fun_prop) ((M₀ ^ 2) ^ 2 + 1)
    fun x => (abs_mul_log_le (sq_nonneg _)).trans (by
      have := hg2 x; rw [abs_of_nonneg (sq_nonneg _)] at this; gcongr)
  rw [integral_sub (i1.const_mul _) i2, integral_const_mul] at key
  -- translate to `targetPi f`
  set A := ∫ z, g z ^ 2 * Real.exp (-f z)
  set Z := ∫ z, Real.exp (-f z)
  have hZ : 0 < Z := targetNormalizerPi_pos hint
  have hA : 0 < A := by
    have h1 : ∫ z, c ^ 2 * Real.exp (-f z) ≤ A :=
      integral_mono (hint.const_mul _) (hbd _ (hgm.pow_const 2) _ hg2) fun z =>
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le (hcg z) 2) (Real.exp_pos _).le
    rw [integral_const_mul] at h1
    exact lt_of_lt_of_le (mul_pos (pow_pos hc 2) hZ) h1
  simp only [ent]
  rw [integral_targetPi_eq hf, integral_targetPi_eq hf, integral_targetPi_eq hf,
    Real.log_div hA.ne' hZ.ne']
  have e : (∫ z, g z ^ 2 * Real.log (g z ^ 2) * Real.exp (-f z)) / Z
      - A / Z * (Real.log A - Real.log Z)
      = ((∫ z, g z ^ 2 * Real.log (g z ^ 2) * Real.exp (-f z))
        + A * (Real.log Z - Real.log A)) / Z := by
    field_simp
    ring
  rw [e, show 2 * (1 / α) * ((∫ z, gradSq g z * Real.exp (-f z)) / Z)
      = (2 / α * ∫ z, gradSq g z * Real.exp (-f z)) / Z by ring]
  exact div_le_div_of_nonneg_right (by linarith) hZ.le

end FormalizeSampling.BakryEmeryGeneralPi
