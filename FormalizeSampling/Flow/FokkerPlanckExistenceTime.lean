module

public import FormalizeSampling.Flow.FokkerPlanckExistenceTimeOp
public import FormalizeSampling.Flow.FokkerPlanckExistence
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Existence for the weak Fokker–Planck equation: time-dependent, linearly growing drifts

Status: **Verified.** Existence for **time-dependent** drifts `b : ℝ → ℝᵈ → ℝᵈ` of **linear
growth**, for an arbitrary initial probability measure `ρ₀` (no moment assumption) and `D > 0`.
The autonomous globally Lipschitz case is `Flow/FokkerPlanckExistenceLinear.lean`.

## Main results

* `exists_weakFokkerPlanck_global`: if, for **all** times, `b t` is `L`-Lipschitz,
  `‖b t x‖ ≤ B (1 + ‖x‖)` and `‖b t x - b s x‖ ≤ K √|t - s| (1 + ‖x‖)`, there is a weakly
  continuous curve `ν : ℝ → 𝒫(ℝᵈ)` with `ν 0 = ρ₀`, solving `WeakFokkerPlanck (ν ·) b D`, and
  equal at every time to the weak limit of the dyadic time-dependent Euler–Maruyama laws
  `tdCurve b hb D ρ₀ n t`.
* `exists_weakFokkerPlanck_time`: the same with **local-in-time** hypotheses: each `b t` is
  measurable and, on every `[0, T]`, Lipschitz in `x` uniformly in `t` and Hölder-`½` in `t`
  with linear weight (`‖b t x - b s x‖ ≤ K_T √|t - s| (1 + ‖x‖)`); linear growth on `[0, T]` is
  then automatic. Reduction to the global case by freezing the drift outside `[0, T]`
  (`clampTime`).
* `exists_weakFokkerPlanck_time_measure`: the measure-curve form (the Itô input of FL-5).

## Method

The solution is the weak limit of the dyadic Euler–Maruyama laws. Every estimate is
**weighted** by `lyap x = 1 + |x|²` and made **pointwise in the starting point** `x` (Dirac
start); integration against `ρ₀` is then done by dominated convergence, using only that the
integrands (test functions, generators) are bounded.

* Cauchy property and tightness: `Flow/FokkerPlanckExistenceTimeOp.lean`.
* Discrete Fokker–Planck identity from a Dirac start with weighted `o(h)` error
  (`abs_discrete_fp_td_le`, from `emOp_generator_lyap`), its vanishing as `n → ∞` for each `x`
  (`tendsto_discrete_fp_err`), and the passage to the limit (`integral_tdLimit_sub_eq`).
* Time regularity of the generator: `|L_t φ - L_s φ| ≤ K √|t - s| sup (1 + ‖y‖) |∇φ(y)|₁`
  (`abs_fpGen_sub_le`), used for the grid-time evaluation of the drift and for the continuity
  of `r ↦ ∫ L_r φ dν_r`.

## Not proved here

* **Drifts merely continuous in time**: the Cauchy rate in the dyadic level uses the
  Hölder-`½` time bound (Lipschitz-in-time drifts are included); drifts that are only
  continuous in `t` would need a compactness (Arzelà–Ascoli) argument instead; this is
  `Flow/FokkerPlanckExistenceContinuousTime`.
* **Locally Lipschitz or superlinear drifts** (e.g. `−∇U` with `U` quartic); the autonomous
  dissipative case is `Flow/FokkerPlanckExistenceDissipative`.
* **Uniqueness** of the solution (for drifts `-a x + bounded` it is
  `Flow/FokkerPlanckUniquenessUnbounded`), identification with the law of an SDE, rates.
* `D = 0`; non-constant diffusion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence

open FormalizeSampling.MeasureHelpers (integral_comp_markov)
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU

variable {d : ℕ}

/-! ### Generator bounds uniform in the drift -/

/-- `|v ⬝ ∇φ(y)| ≤ ‖v‖ ∑ᵢ |∂ᵢφ(y)|` (sup norm on `v`). -/
theorem abs_dotProduct_grad_le (v : Fin d → ℝ) (φ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    |v ⬝ᵥ grad φ y| ≤ ‖v‖ * ∑ i, |partialDeriv i φ y| := by
  show |∑ i, v i * partialDeriv i φ y| ≤ _
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-- For `φ ∈ C²_c`, `(1 + ‖y‖) ∑ᵢ |∂ᵢφ(y)|` is bounded. -/
theorem exists_bound_gradWeight {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    ∃ Mψ, 0 ≤ Mψ ∧ ∀ y, (1 + ‖y‖) * ∑ i, |partialDeriv i φ y| ≤ Mψ := by
  have hpc : ∀ i, Continuous (partialDeriv i φ) := fun i =>
    (contDiff_partialDeriv hφ.1 i).continuous
  have hcont : Continuous fun y : Fin d → ℝ => (1 + ‖y‖) * ∑ i, |partialDeriv i φ y| :=
    (continuous_const.add continuous_norm).mul
      (continuous_finsetSum _ fun i _ => (hpc i).abs)
  obtain ⟨M, hM⟩ := hφ.2.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|M|, abs_nonneg _, fun y => ?_⟩
  by_cases hy : y ∈ tsupport φ
  · have := hM y hy
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self M))
  · have h1 : ∀ i, partialDeriv i φ y = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_partialDeriv_subset i φ h)
    simp [h1]

/-- **Uniform generator bound.** For `φ ∈ C²_c` and `D` there are `Mψ, ML ≥ 0` such that for
every drift `v` with `‖v y‖ ≤ B (1 + ‖y‖)`: `|v(y) ⬝ ∇φ(y) + D Δφ(y)| ≤ B Mψ + |D| ML`. -/
theorem exists_bound_fpGen_unif {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) (D : ℝ) :
    ∃ Mψ ML, 0 ≤ Mψ ∧ 0 ≤ ML ∧ ∀ (v : (Fin d → ℝ) → Fin d → ℝ) (B : ℝ),
      (∀ y, ‖v y‖ ≤ B * (1 + ‖y‖)) → ∀ y, |fpGen v D φ y| ≤ B * Mψ + |D| * ML := by
  obtain ⟨Mψ, hMψ0, hMψ⟩ := exists_bound_gradWeight hφ
  obtain ⟨ML, hML⟩ := (continuous_laplacian hφ.1).bounded_above_of_compact_support
    (hasCompactSupport_laplacian hφ.2)
  have hML0 : 0 ≤ ML := (norm_nonneg _).trans (hML 0)
  refine ⟨Mψ, ML, hMψ0, hML0, fun v B hv y => ?_⟩
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hv 0); simpa using this
  have h1 : |v y ⬝ᵥ grad φ y| ≤ B * Mψ := by
    refine (abs_dotProduct_grad_le _ φ y).trans ?_
    have hs : 0 ≤ ∑ i, |partialDeriv i φ y| := Finset.sum_nonneg fun i _ => abs_nonneg _
    calc ‖v y‖ * ∑ i, |partialDeriv i φ y| ≤ B * (1 + ‖y‖) * ∑ i, |partialDeriv i φ y| :=
          mul_le_mul_of_nonneg_right (hv y) hs
      _ = B * ((1 + ‖y‖) * ∑ i, |partialDeriv i φ y|) := by ring
      _ ≤ B * Mψ := mul_le_mul_of_nonneg_left (hMψ y) hB0
  have h2 : |D * laplacian φ y| ≤ |D| * ML := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hML y) (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **Drift modulus of the generator.** If `(1 + ‖y‖) ∑ᵢ |∂ᵢφ(y)| ≤ Mψ` and
`‖v y - w y‖ ≤ η (1 + ‖y‖)` for all `y`, then `|L^v φ - L^w φ| ≤ η Mψ` everywhere
(`L^v φ = v ⬝ ∇φ + D Δφ`). -/
theorem abs_fpGen_sub_le {φ : (Fin d → ℝ) → ℝ} {Mψ : ℝ}
    (hMψ : ∀ y, (1 + ‖y‖) * ∑ i, |partialDeriv i φ y| ≤ Mψ) (D : ℝ)
    {v w : (Fin d → ℝ) → Fin d → ℝ} {η : ℝ} (hvw : ∀ y, ‖v y - w y‖ ≤ η * (1 + ‖y‖))
    (y : Fin d → ℝ) : |fpGen v D φ y - fpGen w D φ y| ≤ η * Mψ := by
  have hη : 0 ≤ η := by
    have := (norm_nonneg _).trans (hvw 0); simpa using this
  have e : fpGen v D φ y - fpGen w D φ y = (v y - w y) ⬝ᵥ grad φ y := by
    simp only [fpGen, sub_dotProduct]; ring
  rw [e]
  refine (abs_dotProduct_grad_le _ φ y).trans ?_
  have hs : 0 ≤ ∑ i, |partialDeriv i φ y| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc ‖v y - w y‖ * ∑ i, |partialDeriv i φ y| ≤ η * (1 + ‖y‖) * ∑ i, |partialDeriv i φ y| :=
        mul_le_mul_of_nonneg_right (hvw y) hs
    _ = η * ((1 + ‖y‖) * ∑ i, |partialDeriv i φ y|) := by ring
    _ ≤ η * Mψ := mul_le_mul_of_nonneg_left (hMψ y) hη

/-! ### The discrete Fokker–Planck identity from a Dirac start -/

section Discrete

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0} {B K D h : ℝ}

/-- **Discrete Fokker–Planck identity with weighted error, Dirac start.** Let `b t` be
`L`-Lipschitz with `‖b t y‖ ≤ B (1 + ‖y‖)`, `D ≥ 0`, `0 ≤ h ≤ 1`, `ε ≥ 0`, `φ ∈ C²_c`, and
suppose every step satisfies `|P_τ φ - φ - h L_τ φ| ≤ ε h lyap` (`P_τ = emOp (b τ) D h`,
`L_τ φ = b τ ⬝ ∇φ + D Δφ`). Then after `k` steps from `x`,
`|∫ φ d(tdPow k x) - φ x - h ∑_{j<k} ∫ L_{jh} φ d(tdPow j x)| ≤ k ε h (1 + c h)^k lyap(x)`. -/
theorem abs_discrete_fp_td_le (hb : ∀ t, Measurable (b t)) (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) {ε : ℝ} (hε : 0 ≤ ε)
    (hgen : ∀ τ y, |emOp (b τ) D h φ y - φ y - h * fpGen (b τ) D φ y| ≤ ε * h * lyap y)
    (x : Fin d → ℝ) (k : ℕ) :
    |∫ y, φ y ∂(tdPow b hb D h k x) - φ x -
        h * ∑ j ∈ Finset.range k, ∫ y, fpGen (b (j * h)) D φ y ∂(tdPow b hb D h j x)| ≤
      k * (ε * h) * (1 + lyapConst d B D * h) ^ k * lyap x := by
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  obtain ⟨⟨M, hM⟩, -⟩ := testFunction2_bounds hφ
  have hφc := hφ.1.continuous
  have hc : 1 ≤ 1 + lyapConst d B D * h :=
    le_add_of_nonneg_right (mul_nonneg (lyapConst_nonneg B hD) hh0)
  have hl := lyap_pos x
  induction k with
  | zero =>
    simp only [tdPow, Kernel.id_apply, integral_dirac, Finset.range_zero, Finset.sum_empty]
    simp
  | succ k ih =>
    set μ := tdPow b hb D h k x with hμ
    set τ : ℝ := k * h
    obtain ⟨MG, hMG⟩ := exists_bound_fpGen (hbc τ) D hφ
    have hPc := continuous_emOp (D := D) (h := h) (hbc τ) hφc hM
    have hPM : ∀ y, |emOp (b τ) D h φ y| ≤ M := abs_emOp_le hφc hM
    have hGc := continuous_fpGen (hbc τ) D hφ.1
    have e1 : ∫ y, φ y ∂(tdPow b hb D h (k + 1) x) = ∫ y, emOp (b τ) D h φ y ∂μ := by
      show ∫ y, φ y ∂((emStep (b (k * h)) (hb _) D h ∘ₖ tdPow b hb D h k) x) = _
      rw [Kernel.integral_comp (integrable_of_abs_le hφc hM)]
      simp_rw [integral_emStep (hb _) hD hh0 hφc]
      rfl
    have hstep : |∫ y, emOp (b τ) D h φ y ∂μ - ∫ y, φ y ∂μ - h * ∫ y, fpGen (b τ) D φ y ∂μ| ≤
        ε * h * ((1 + lyapConst d B D * h) ^ k * lyap x) := by
      have i1 : Integrable (fun y => emOp (b τ) D h φ y - φ y) μ :=
        (integrable_of_abs_le hPc hPM).sub (integrable_of_abs_le hφc hM)
      have i2 : Integrable (fun y => h * fpGen (b τ) D φ y) μ :=
        (integrable_of_abs_le hGc hMG).const_mul h
      have e : ∫ y, (emOp (b τ) D h φ y - φ y - h * fpGen (b τ) D φ y) ∂μ =
          ∫ y, emOp (b τ) D h φ y ∂μ - ∫ y, φ y ∂μ - h * ∫ y, fpGen (b τ) D φ y ∂μ := by
        rw [integral_sub i1 i2, integral_sub (integrable_of_abs_le hPc hPM)
          (integrable_of_abs_le hφc hM), integral_const_mul]
      rw [← e]
      exact abs_integral_tdPow_le hb hB hD hh0 hh1 (i1.sub i2) (by positivity) (hgen τ)
    rw [e1, Finset.sum_range_succ]
    have hW1 : (1 + lyapConst d B D * h) ^ k ≤ (1 + lyapConst d B D * h) ^ (k + 1) :=
      pow_le_pow_right₀ hc (Nat.le_succ k)
    have hεh : 0 ≤ ε * h := mul_nonneg hε hh0
    calc _ = |(∫ y, φ y ∂μ - φ x -
          h * ∑ j ∈ Finset.range k, ∫ y, fpGen (b (j * h)) D φ y ∂(tdPow b hb D h j x)) +
          (∫ y, emOp (b τ) D h φ y ∂μ - ∫ y, φ y ∂μ - h * ∫ y, fpGen (b τ) D φ y ∂μ)| := by
          congr 1; ring
      _ ≤ k * (ε * h) * (1 + lyapConst d B D * h) ^ k * lyap x +
          ε * h * ((1 + lyapConst d B D * h) ^ k * lyap x) :=
          (abs_add_le _ _).trans (add_le_add ih hstep)
      _ ≤ k * (ε * h) * (1 + lyapConst d B D * h) ^ (k + 1) * lyap x +
          ε * h * ((1 + lyapConst d B D * h) ^ (k + 1) * lyap x) := by gcongr
      _ = _ := by push_cast; ring

/-- `|⌊r 2ⁿ⌋₊ 2⁻ⁿ - r| ≤ 2⁻ⁿ` for `r ≥ 0`. -/
theorem abs_grid_sub_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    |(gridIndex n r : ℝ) * dyadicStep n - r| ≤ dyadicStep n := by
  have h1 : (gridIndex n r : ℝ) * dyadicStep n ≤ r :=
    (gridIndex_mul_le n r).trans (by simp [hr])
  have hh : 0 < dyadicStep n := dyadicStep_pos n
  have hh2 : dyadicStep n * 2 ^ n = 1 := dyadicStep_mul_pow n
  have hfl := Nat.lt_floor_add_one (r * 2 ^ n)
  have h2 : r < ((gridIndex n r : ℝ) + 1) * dyadicStep n := by
    have e : r * 2 ^ n * dyadicStep n = r := by
      rw [mul_assoc, mul_comm (2 ^ n : ℝ), hh2, mul_one]
    have := mul_lt_mul_of_pos_right hfl hh
    rw [e] at this
    exact this
  rw [abs_le]; constructor <;> nlinarith

/-- **The discrete error vanishes pointwise.** Under linear growth and Lipschitz `b t`, `D > 0`,
`φ ∈ C²_c` and `t ≥ 0`, for every starting point `x`,
`P^{(n)}_k φ(x) - φ(x) - h ∑_{j<k} P^{(n)}_j (L_{jh} φ)(x) → 0` as `n → ∞`
(`h = 2⁻ⁿ`, `k = ⌊t 2ⁿ⌋₊`, `P^{(n)}_j = tdOp b D h 0 j`). -/
theorem tendsto_discrete_fp_err (hb : ∀ t, Measurable (b t)) (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 < D) {φ : (Fin d → ℝ) → ℝ}
    (hφ : TestFunction2 φ) {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    Tendsto (fun n => tdOp b D (dyadicStep n) 0 (gridIndex n t) φ x - φ x -
      dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t),
        tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x) atTop (𝓝 0) := by
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  have hB0 := nonneg_of_linGrowth hB
  obtain ⟨⟨M, hM⟩, -⟩ := testFunction2_bounds hφ
  set c := lyapConst d B D with hcdef
  have hc0 : 0 ≤ c := lyapConst_nonneg B hD.le
  have hl := lyap_pos x
  set W := (t + 1) * Real.exp (c * t) * lyap x with hW
  have hW0 : 0 < W := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε₀ := ε / (2 * W) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  obtain ⟨δ, hδ, hgen⟩ := emOp_generator_lyap hφ hB0 hD hε₀0
  have hdy : Tendsto dyadicStep atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdy.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set h := dyadicStep n with hhdef
  set k := gridIndex n t with hk
  have hh : 0 < h := dyadicStep_pos n
  have hh1 : h ≤ 1 := dyadicStep_le_one n
  have hkh : (k : ℝ) * h ≤ t := (gridIndex_mul_le n t).trans (by simp [ht])
  have hg : ∀ τ y, |emOp (b τ) D h φ y - φ y - h * fpGen (b τ) D φ y| ≤ ε₀ * h * lyap y :=
    fun τ y => hgen h hh (hN n hn) (b τ) y (hB τ y)
  have key := abs_discrete_fp_td_le hb hL hB hD.le hh.le hh1 hφ hε₀0.le hg x k
  obtain ⟨MG, -⟩ := exists_bound_fpGen (hbc 0) D hφ
  rw [integral_tdPow hb hbc hD.le hh.le hφ.1.continuous hM] at key
  have hsum : ∑ j ∈ Finset.range k, ∫ y, fpGen (b (j * h)) D φ y ∂(tdPow b hb D h j x) =
      ∑ j ∈ Finset.range k, tdOp b D h 0 j (fpGen (b (j * h)) D φ) x := by
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨MGj, hMGj⟩ := exists_bound_fpGen (hbc (j * h)) D hφ
    exact integral_tdPow hb hbc hD.le hh.le (continuous_fpGen (hbc _) D hφ.1) hMGj j x
  rw [hsum] at key
  rw [Real.dist_eq, sub_zero]
  refine lt_of_le_of_lt key ?_
  have hp : (1 + c * h) ^ k ≤ Real.exp (c * t) := by
    refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.2 ?_)
    nlinarith
  have : (k : ℝ) * (ε₀ * h) * (1 + c * h) ^ k * lyap x ≤ ε₀ * W := by
    rw [hW]
    have e : (k : ℝ) * (ε₀ * h) * (1 + c * h) ^ k * lyap x =
        ε₀ * ((k * h) * (1 + c * h) ^ k * lyap x) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hε₀0.le
    have : (k : ℝ) * h * (1 + c * h) ^ k ≤ (t + 1) * Real.exp (c * t) :=
      mul_le_mul (by linarith) hp (by positivity) (by positivity)
    nlinarith
  have hεW : ε₀ * W = ε / 2 := by rw [hε₀]; field_simp
  linarith

end Discrete

/-! ### The limit curve (global hypotheses) -/

/-- The dyadic time-dependent EM law as an element of `ProbabilityMeasure`. -/
noncomputable def tdCurveP (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ t, Measurable (b t))
    (D : ℝ) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (n : ℕ) (t : ℝ) :
    ProbabilityMeasure (Fin d → ℝ) :=
  ⟨tdCurve b hb D ρ₀ n t, inferInstance⟩

section Limit

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0} {B K D : ℝ}

/-- For `t ≤ 0` no step has been taken: `tdCurve b hb D ρ₀ n t = ρ₀`. -/
theorem tdCurve_of_nonpos (hb : ∀ t, Measurable (b t)) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] (n : ℕ) {t : ℝ} (ht : t ≤ 0) : tdCurve b hb D ρ₀ n t = ρ₀ := by
  have : gridIndex n t = 0 :=
    Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ht (by positivity))
  rw [tdCurve, this]
  exact Measure.id_comp

/-- **Existence of the weak limit at a fixed time** (global hypotheses, `D ≥ 0`, any `ρ₀`). -/
theorem exists_tdLimit (hb : ∀ t, Measurable (b t)) (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hK0 : 0 ≤ K)
    (hD : 0 ≤ D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (t : ℝ) :
    ∃ ν : ProbabilityMeasure (Fin d → ℝ),
      Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 ν) := by
  refine exists_tendsto_of_isTight (isTightMeasureSet_tdCurve hb hB hD ρ₀ t)
    (fun n => ⟨n, t, le_rfl, rfl⟩) fun φ hφ => ?_
  obtain ⟨⟨M, hM⟩, C, hC0, hC⟩ := testFunction2_bounds hφ
  exact exists_tendsto_integral_tdCurve hb hL hB hK hK0 hD ρ₀ hφ.1.continuous hM hC hC0 t

/-- **Integrated weak Fokker–Planck identity for time-dependent EM limits.** Under the global
hypotheses (`b t` `L`-Lipschitz, linear growth, Hölder-`½` in time, `K ≥ 0`), `D > 0`, a
probability measure `ρ₀`, and `ν t` the weak limit of the dyadic laws at every time: for
`φ ∈ C²_c` and `t ≥ 0`, `∫ φ dν_t - ∫ φ dρ₀ = ∫₀ᵗ ∫ (b_r ⬝ ∇φ + D Δφ) dν_r dr`. -/
theorem integral_tdLimit_sub_eq (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, φ y ∂(ν t : Measure (Fin d → ℝ)) - ∫ y, φ y ∂ρ₀ =
      ∫ r in (0 : ℝ)..t, ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) := by
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  obtain ⟨⟨M, hM⟩, -⟩ := testFunction2_bounds hφ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨Mψ, ML, hMψ0, hML0, hGu⟩ := exists_bound_fpGen_unif hφ D
  obtain ⟨Mψ', hMψ'0, hMψ'⟩ := exists_bound_gradWeight hφ
  have hB0 := nonneg_of_linGrowth hB
  set MG := B * Mψ + |D| * ML with hMGdef
  have hMG0 : 0 ≤ MG := by positivity
  have hGb : ∀ τ y, |fpGen (b τ) D φ y| ≤ MG := fun τ => hGu (b τ) B (hB τ)
  have hGc : ∀ τ, Continuous (fpGen (b τ) D φ) := fun τ => continuous_fpGen (hbc τ) D hφ.1
  have hmod : ∀ τ σ y, |fpGen (b τ) D φ y - fpGen (b σ) D φ y| ≤
      K * Real.sqrt |τ - σ| * Mψ' := fun τ σ y => abs_fpGen_sub_le hMψ' D (hK σ τ) y
  set c : ℕ → ℕ → ℝ := fun n j => ∫ y, fpGen (b (j * dyadicStep n)) D φ y
    ∂(tdPow b hb D (dyadicStep n) j ∘ₘ ρ₀) with hcdef
  have hcb : ∀ n j, |c n j| ≤ MG := fun n j => abs_integral_le_of_abs_le (hGb _)
  set G : ℝ → ℝ := fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) with hG
  have hdy : Tendsto dyadicStep atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun n => ∫ y, φ y ∂(tdCurve b hb D ρ₀ n t)) atTop
      (𝓝 (∫ y, φ y ∂(ν t : Measure (Fin d → ℝ)))) :=
    tendsto_integral_of_tendsto (hν t) hφ.1.continuous hM
  have h2 : Tendsto (fun n => ∫ r in (0 : ℝ)..t, c n (gridIndex n r)) atTop
      (𝓝 (∫ r in (0 : ℝ)..t, G r)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => MG)
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ae_of_all _ fun r _ => ?_)
      intervalIntegrable_const (ae_of_all _ fun r hr => ?_)
    · exact ((Measurable.of_discrete (f := c n)).comp
        (measurable_gridIndex n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hcb n _
    · rw [uIoc_of_le ht] at hr
      have hr0 : 0 ≤ r := hr.1.le
      have hA : Tendsto (fun n => ∫ y, fpGen (b r) D φ y ∂(tdCurve b hb D ρ₀ n r)) atTop
          (𝓝 (G r)) := tendsto_integral_of_tendsto (hν r) (hGc r) (hGb r)
      have hBn : Tendsto (fun n => c n (gridIndex n r) -
          ∫ y, fpGen (b r) D φ y ∂(tdCurve b hb D ρ₀ n r)) atTop (𝓝 0) := by
        have hsq : Tendsto (fun n => K * Real.sqrt (dyadicStep n) * Mψ') atTop (𝓝 0) := by
          have := ((Real.continuous_sqrt.tendsto 0).comp hdy).const_mul K
          simpa using this.mul_const Mψ'
        refine squeeze_zero_norm (fun n => ?_) hsq
        rw [Real.norm_eq_abs]
        have hK0 : 0 ≤ K := by
          have := (norm_nonneg _).trans (hK 0 1 0)
          have h2 : 0 ≤ K * Real.sqrt |1 - 0| := by simpa using this
          simpa using h2
        refine (abs_integral_sub_le_of_abs_le (hGc _) (hGc r) (hGb _) (hGb r)
          (fun y => hmod _ r y)).trans ?_
        gcongr
        exact abs_grid_sub_le n hr0
      simpa using hBn.add hA
  have hlim := (h1.sub_const (∫ y, φ y ∂ρ₀)).sub h2
  -- the discrete error tends to zero
  have h0 : Tendsto (fun n => ∫ y, φ y ∂(tdCurve b hb D ρ₀ n t) - ∫ y, φ y ∂ρ₀ -
      ∫ r in (0 : ℝ)..t, c n (gridIndex n r)) atTop (𝓝 0) := by
    set e : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
      tdOp b D (dyadicStep n) 0 (gridIndex n t) φ x - φ x -
        dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t),
          tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x with he
    have hjc : ∀ n j, Continuous (tdOp b D (dyadicStep n) 0 j
        (fpGen (b (j * dyadicStep n)) D φ)) := fun n j =>
      (tdOp_cont hbc (hGc _) (hGb _) 0 j).1
    have hjb : ∀ n j x, |tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x|
        ≤ MG := fun n j => (tdOp_cont hbc (hGc _) (hGb _) 0 j).2
    have hpc : ∀ n, Continuous (tdOp b D (dyadicStep n) 0 (gridIndex n t) φ) := fun n =>
      (tdOp_cont hbc hφ.1.continuous hM 0 _).1
    have hpb : ∀ n x, |tdOp b D (dyadicStep n) 0 (gridIndex n t) φ x| ≤ M := fun n =>
      (tdOp_cont hbc hφ.1.continuous hM 0 _).2
    have hec : ∀ n, Continuous (e n) := fun n =>
      ((hpc n).sub hφ.1.continuous).sub (continuous_const.mul
        (continuous_finsetSum _ fun j _ => hjc n j))
    have heb : ∀ n x, |e n x| ≤ M + M + t * MG := by
      intro n x
      have hkh : (gridIndex n t : ℝ) * dyadicStep n ≤ t :=
        (gridIndex_mul_le n t).trans (by simp [ht])
      have hs : |dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t),
          tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x| ≤ t * MG := by
        rw [abs_mul, abs_of_pos (dyadicStep_pos n)]
        have := Finset.abs_sum_le_sum_abs (s := Finset.range (gridIndex n t))
          (fun j => tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x)
        have h2 : ∑ j ∈ Finset.range (gridIndex n t),
            |tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x| ≤
            gridIndex n t * MG := by
          have := Finset.sum_le_sum (s := Finset.range (gridIndex n t))
            (fun j _ => hjb n j x)
          simpa using this
        calc dyadicStep n * |∑ j ∈ Finset.range (gridIndex n t),
              tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x|
            ≤ dyadicStep n * (gridIndex n t * MG) :=
              mul_le_mul_of_nonneg_left (this.trans h2) (dyadicStep_pos n).le
          _ = (gridIndex n t * dyadicStep n) * MG := by ring
          _ ≤ t * MG := mul_le_mul_of_nonneg_right hkh hMG0
      have := hpb n x
      have := hM x
      simp only [he]
      calc _ ≤ |tdOp b D (dyadicStep n) 0 (gridIndex n t) φ x - φ x| +
            |dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t),
              tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x| :=
            abs_sub _ _
        _ ≤ (|tdOp b D (dyadicStep n) 0 (gridIndex n t) φ x| + |φ x|) + t * MG :=
            add_le_add (abs_sub _ _) hs
        _ ≤ M + M + t * MG := by linarith
    have hE : Tendsto (fun n => ∫ x, e n x ∂ρ₀) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := ρ₀) (F := e) (f := fun _ => 0)
        (fun _ => M + M + t * MG) (fun n => (hec n).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]; exact heb n x)
        (ae_of_all _ fun x => tendsto_discrete_fp_err hb hL hB hD hφ ht x)
      simpa using this
    have hEeq : ∀ n, ∫ x, e n x ∂ρ₀ = ∫ y, φ y ∂(tdCurve b hb D ρ₀ n t) - ∫ y, φ y ∂ρ₀ -
        dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t), c n j := by
      intro n
      have ip := integrable_of_abs_le (μ := ρ₀) (hpc n) (hpb n)
      have iφ := integrable_of_abs_le (μ := ρ₀) hφ.1.continuous hM
      have ij : ∀ j ∈ Finset.range (gridIndex n t), Integrable
          (fun x => tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x) ρ₀ :=
        fun j _ => integrable_of_abs_le (hjc n j) (hjb n j)
      have i1 : Integrable (fun x => tdOp b D (dyadicStep n) 0 (gridIndex n t) φ x - φ x) ρ₀ :=
        ip.sub iφ
      have i2 : Integrable (fun x => dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t),
          tdOp b D (dyadicStep n) 0 j (fpGen (b (j * dyadicStep n)) D φ) x) ρ₀ :=
        (integrable_finsetSum _ ij).const_mul _
      simp only [he]
      rw [integral_sub i1 i2, integral_sub ip iφ, integral_const_mul, integral_finsetSum _ ij,
        ← integral_tdCurve hb hbc hD.le ρ₀ hφ.1.continuous hM n t]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hcdef]
      rw [integral_comp_markov _ ρ₀ (hGc _) (hGb _)]
      exact integral_congr_ae (ae_of_all _ fun x =>
        (integral_tdPow hb hbc hD.le (dyadicStep_pos n).le (hGc _) (hGb _) j x).symm)
    have htail : Tendsto (fun n => ∫ r in ((gridIndex n t : ℝ) * dyadicStep n)..t,
        c n (gridIndex n r)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by simpa using hdy.mul_const MG)
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := MG)
        fun r _ => ?_).trans ?_
      · rw [Real.norm_eq_abs]; exact hcb n _
      · have := abs_grid_sub_le n ht
        rw [abs_sub_comm] at this
        rw [mul_comm MG]
        exact mul_le_mul_of_nonneg_right this hMG0
    have hsplit : ∀ n, ∫ r in (0 : ℝ)..t, c n (gridIndex n r) =
        dyadicStep n * ∑ j ∈ Finset.range (gridIndex n t), c n j +
          ∫ r in ((gridIndex n t : ℝ) * dyadicStep n)..t, c n (gridIndex n r) := by
      intro n
      rw [← integral_grid n (hcb n) (gridIndex n t)]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_grid n (hcb n) _ _) (intervalIntegrable_grid n (hcb n) _ _)).symm
    have : (fun n => ∫ y, φ y ∂(tdCurve b hb D ρ₀ n t) - ∫ y, φ y ∂ρ₀ -
        ∫ r in (0 : ℝ)..t, c n (gridIndex n r)) = fun n => ∫ x, e n x ∂ρ₀ -
          ∫ r in ((gridIndex n t : ℝ) * dyadicStep n)..t, c n (gridIndex n r) := by
      funext n; rw [hEeq, hsplit]; ring
    rw [this]
    simpa using hE.sub htail
  have := tendsto_nhds_unique hlim h0
  linarith

end Limit

/-! ### Properties of the limit curve (global hypotheses) -/

section Curve

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0} {B K D : ℝ}

/-- `0 ≤ K` follows from a time-Hölder bound `‖b t y - b s y‖ ≤ K √|t - s| (1 + ‖y‖)`. -/
theorem nonneg_of_timeHolder
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) : 0 ≤ K := by
  have := (norm_nonneg _).trans (hK 0 1 0)
  simpa using this

/-- Before time `0` the limit is the initial law: `ν t = ρ₀` for `t ≤ 0`. -/
theorem tdLimit_of_nonpos (hb : ∀ t, Measurable (b t)) {ρ₀ : Measure (Fin d → ℝ)}
    [IsProbabilityMeasure ρ₀] {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t))) {t : ℝ}
    (ht : t ≤ 0) : (ν t : Measure (Fin d → ℝ)) = ρ₀ := by
  have hc : (fun n => tdCurveP b hb D ρ₀ n t) = fun _ => ⟨ρ₀, inferInstance⟩ := by
    funext n; apply Subtype.ext; exact tdCurve_of_nonpos hb ρ₀ n ht
  have := tendsto_nhds_unique (hν t) (by rw [hc]; exact tendsto_const_nhds)
  rw [this]; rfl

/-- For a probability measure `μ` and `φ ∈ C²_c`, `r ↦ ∫ (b_r ⬝ ∇φ + D Δφ) dμ` is continuous
when `b` is Hölder-`½` in time with linear weight. -/
theorem continuous_integral_fpGen_time {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    Continuous fun r => ∫ y, fpGen (b r) D φ y ∂μ := by
  obtain ⟨Mψ, ML, -, -, hGu⟩ := exists_bound_fpGen_unif hφ D
  obtain ⟨Mψ', -, hMψ'⟩ := exists_bound_gradWeight hφ
  have hGc : ∀ τ, Continuous (fpGen (b τ) D φ) := fun τ =>
    continuous_fpGen (hL τ).continuous D hφ.1
  rw [continuous_iff_continuousAt]
  intro r₀
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto (fun r => K * Real.sqrt |r - r₀| * Mψ') (𝓝 r₀) (𝓝 0) := by
    have : Continuous fun r => K * Real.sqrt |r - r₀| * Mψ' := by fun_prop
    simpa using this.tendsto r₀
  refine squeeze_zero_norm (fun r => ?_) hlim
  rw [Real.norm_eq_abs]
  exact abs_integral_sub_le_of_abs_le (hGc r) (hGc r₀) (hGu _ B (hB r)) (hGu _ B (hB r₀))
    (fun y => abs_fpGen_sub_le hMψ' D (hK r₀ r) y)

/-- `r ↦ ∫ (b_r ⬝ ∇φ + D Δφ) dν_r` is measurable for an EM limit `ν` (pointwise limit of
the measurable functions `r ↦ ∫ (b_r ⬝ ∇φ + D Δφ) d(tdCurve n r)`). -/
theorem measurable_integral_tdLimit (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖))
    {ρ₀ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    Measurable fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) := by
  obtain ⟨Mψ, ML, -, -, hGu⟩ := exists_bound_fpGen_unif hφ D
  have hGc : ∀ τ, Continuous (fpGen (b τ) D φ) := fun τ =>
    continuous_fpGen (hL τ).continuous D hφ.1
  refine measurable_of_tendsto_metrizable
    (f := fun n r => ∫ y, fpGen (b r) D φ y ∂(tdCurve b hb D ρ₀ n r)) (fun n => ?_)
    (tendsto_pi_nhds.2 fun r => tendsto_integral_of_tendsto (hν r) (hGc r) (hGu _ B (hB r)))
  have hΦm : Measurable fun p : ℝ × ℕ => ∫ y, fpGen (b p.1) D φ y
      ∂(tdPow b hb D (dyadicStep n) p.2 ∘ₘ ρ₀) :=
    measurable_from_prod_countable_left fun j =>
      (continuous_integral_fpGen_time (D := D) (μ := tdPow b hb D (dyadicStep n) j ∘ₘ ρ₀)
        hL hB hK hφ).measurable
  have e : (fun r => ∫ y, fpGen (b r) D φ y ∂(tdCurve b hb D ρ₀ n r)) =
      (fun p : ℝ × ℕ => ∫ y, fpGen (b p.1) D φ y ∂(tdPow b hb D (dyadicStep n) p.2 ∘ₘ ρ₀)) ∘
        fun r => (r, gridIndex n r) := by
    funext r; simp only [Function.comp, tdCurve]
  rw [e]
  exact hΦm.comp (measurable_id.prodMk (measurable_gridIndex n))

/-- **Integrated identity on all of `ℝ`.** Under the global hypotheses and `D > 0`,
`∫ φ dν_t = ∫ φ dρ₀ + ∫₀^{max t 0} ∫ (b_r ⬝ ∇φ + D Δφ) dν_r dr` for every `t`. -/
theorem integral_tdLimit_eq (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) (t : ℝ) :
    ∫ y, φ y ∂(ν t : Measure (Fin d → ℝ)) = ∫ y, φ y ∂ρ₀ +
      ∫ r in (0 : ℝ)..max t 0, ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, ← integral_tdLimit_sub_eq hb hL hB hK hD ρ₀ hν hφ ht]; ring
  · rw [max_eq_right ht, intervalIntegral.integral_same, add_zero, tdLimit_of_nonpos hb hν ht]

/-- For `φ ∈ C²_c`, `t ↦ ∫ φ dν_t` is continuous (global hypotheses, `D > 0`). -/
theorem continuous_integral_tdLimit (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)))
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) :
    Continuous fun t => ∫ y, φ y ∂(ν t : Measure (Fin d → ℝ)) := by
  obtain ⟨Mψ, ML, -, -, hGu⟩ := exists_bound_fpGen_unif hφ D
  have hmeas := measurable_integral_tdLimit hb hL hB hK hν hφ
  have hint : ∀ a c, IntervalIntegrable
      (fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ))) volume a c := fun a c =>
    (intervalIntegrable_const (c := B * Mψ + |D| * ML)).mono_fun' hmeas.aestronglyMeasurable
      (ae_of_all _ fun r => by
        simp only [Real.norm_eq_abs]; exact abs_integral_le_of_abs_le (hGu _ B (hB r)))
  have e : (fun t => ∫ y, φ y ∂(ν t : Measure (Fin d → ℝ))) = fun t => ∫ y, φ y ∂ρ₀ +
      ∫ r in (0 : ℝ)..max t 0, ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) :=
    funext (integral_tdLimit_eq hb hL hB hK hD ρ₀ hν hφ)
  rw [e]
  exact continuous_const.add ((intervalIntegral.continuous_primitive hint 0).comp
    (continuous_id.max continuous_const))

/-- **Tightness of the limit on bounded time sets.** `{ν r | r ≤ T}` is tight. -/
theorem isTight_tdLimit (hb : ∀ t, Measurable (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hD : 0 ≤ D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t))) (T : ℝ) :
    IsTightMeasureSet {μ | ∃ r ≤ T, μ = (ν r : Measure (Fin d → ℝ))} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K₀, hK₀, hKε⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_tdCurve hb hB hD ρ₀ T) ε hε
  obtain ⟨R, hR⟩ := hK₀.isBounded.subset_closedBall (0 : Fin d → ℝ)
  refine ⟨closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro μ ⟨r, hr, rfl⟩
  refine measure_compl_closedBall_le_of_tendsto (hν r) (Eventually.of_forall fun n => ?_)
  exact (measure_mono (compl_subset_compl.2 hR)).trans (hKε _ ⟨n, r, hr, rfl⟩)

/-- **Weak continuity of the limit curve** (global hypotheses, `D > 0`). -/
theorem continuous_tdLimit (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t))) : Continuous ν := by
  rw [continuous_iff_continuousAt]
  intro r₀
  exact tendsto_of_isTight_of_integral_tendsto (isTight_tdLimit hb hB hD.le ρ₀ hν (r₀ + 1))
    ((eventually_le_nhds (lt_add_one r₀)).mono fun r hr => ⟨r, hr, rfl⟩)
    fun φ hφ => (continuous_integral_tdLimit hb hL hB hK hD ρ₀ hν hφ).continuousAt

/-- **Weak Fokker–Planck equation for time-dependent EM limits (global hypotheses).** Let
`b t` be `L`-Lipschitz with `‖b t x‖ ≤ B (1 + ‖x‖)` and
`‖b t x - b s x‖ ≤ K √|t - s| (1 + ‖x‖)` for all `s, t, x`, `D > 0`, `ρ₀` a probability
measure and `ν t` the weak limit of the dyadic laws `tdCurve b hb D ρ₀ n t` for every `t`.
Then `WeakFokkerPlanck (fun t => ν t) b D`. -/
theorem weakFokkerPlanck_tdLimit (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    {ν : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (hν : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t))) :
    WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) b D := by
  intro φ hφ t ht
  obtain ⟨Mψ, ML, -, -, hGu⟩ := exists_bound_fpGen_unif hφ D
  obtain ⟨Mψ', -, hMψ'⟩ := exists_bound_gradWeight hφ
  have hGc : ∀ τ, Continuous (fpGen (b τ) D φ) := fun τ =>
    continuous_fpGen (hL τ).continuous D hφ.1
  have hνc := continuous_tdLimit hb hL hB hK hD ρ₀ hν
  have hG : Continuous fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) := by
    rw [continuous_iff_continuousAt]
    intro r₀
    have h1 : Tendsto (fun r => ∫ y, fpGen (b r₀) D φ y ∂(ν r : Measure (Fin d → ℝ))) (𝓝 r₀)
        (𝓝 (∫ y, fpGen (b r₀) D φ y ∂(ν r₀ : Measure (Fin d → ℝ)))) :=
      ((continuous_integral_of_abs_le (hGc r₀) (hGu _ B (hB r₀))).comp hνc).tendsto r₀
    have hlim : Tendsto (fun r => K * Real.sqrt |r - r₀| * Mψ') (𝓝 r₀) (𝓝 0) := by
      have : Continuous fun r => K * Real.sqrt |r - r₀| * Mψ' := by fun_prop
      simpa using this.tendsto r₀
    have h2 : Tendsto (fun r => ∫ y, fpGen (b r) D φ y ∂(ν r : Measure (Fin d → ℝ)) -
        ∫ y, fpGen (b r₀) D φ y ∂(ν r : Measure (Fin d → ℝ))) (𝓝 r₀) (𝓝 0) := by
      refine squeeze_zero_norm (fun r => ?_) hlim
      rw [Real.norm_eq_abs]
      exact abs_integral_sub_le_of_abs_le (hGc r) (hGc r₀) (hGu _ B (hB r))
        (hGu _ B (hB r₀)) (fun y => abs_fpGen_sub_le hMψ' D (hK r₀ r) y)
    have := h2.add h1
    simp only [sub_add_cancel, zero_add] at this
    exact this
  have hd := ((hG.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt
    (s := Ici 0)).const_add (∫ y, φ y ∂ρ₀)
  refine hd.congr_of_mem (fun s hs => ?_) ht
  rw [integral_tdLimit_eq hb hL hB hK hD ρ₀ hν hφ s, max_eq_left (mem_Ici.1 hs)]

/-- **Existence for the weak Fokker–Planck equation, time-dependent drift with linear growth
(global hypotheses, Verified).** Let `b : ℝ → ℝᵈ → ℝᵈ` with measurable slices such that for
**all** `s, t, x, y`: `‖b t x - b t y‖ ≤ L ‖x - y‖`, `‖b t x‖ ≤ B (1 + ‖x‖)` and
`‖b t x - b s x‖ ≤ K √|t - s| (1 + ‖x‖)`; let `D > 0` and `ρ₀` be any probability measure.
Then there is a weakly continuous `ν : ℝ → 𝒫(ℝᵈ)` with `ν 0 = ρ₀`, solving
`WeakFokkerPlanck (fun t => ν t) b D`, and equal at every time to the weak limit of the dyadic
time-dependent Euler–Maruyama laws. -/
theorem exists_weakFokkerPlanck_global (hb : ∀ t, Measurable (b t))
    (hL : ∀ t, LipschitzWith L (b t)) (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) b D ∧
      ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)) := by
  choose ν hν using exists_tdLimit hb hL hB hK (nonneg_of_timeHolder hK) hD.le ρ₀
  exact ⟨ν, tdLimit_of_nonpos hb hν le_rfl, continuous_tdLimit hb hL hB hK hD ρ₀ hν,
    weakFokkerPlanck_tdLimit hb hL hB hK hD ρ₀ hν, hν⟩

end Curve

/-! ### Local-in-time hypotheses -/

/-- Projection of times onto `[0, T]`: `clampTime T t = max (min t T) 0`. -/
noncomputable def clampTime (T t : ℝ) : ℝ := max (min t T) 0

/-- `clampTime T t ∈ [0, T]` for `T ≥ 0`. -/
theorem clampTime_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTime T t ∈ Icc 0 T :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) hT⟩

/-- `clampTime T t = t` for `t ∈ [0, T]`. -/
theorem clampTime_of_mem {T t : ℝ} (ht : t ∈ Icc 0 T) : clampTime T t = t := by
  unfold clampTime; rw [min_eq_left ht.2, max_eq_left ht.1]

/-- `clampTime T` is `1`-Lipschitz. -/
theorem abs_clampTime_sub_le (T s t : ℝ) : |clampTime T t - clampTime T s| ≤ |t - s| := by
  unfold clampTime
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- Two drift families agreeing at the first `k` grid times give the same `k`-step kernel. -/
theorem tdPow_congr {b₁ b₂ : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hb₁ : ∀ t, Measurable (b₁ t))
    (hb₂ : ∀ t, Measurable (b₂ t)) (D h : ℝ) {k : ℕ}
    (hk : ∀ j < k, b₁ (j * h) = b₂ (j * h)) : tdPow b₁ hb₁ D h k = tdPow b₂ hb₂ D h k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : ∀ (f g : (Fin d → ℝ) → Fin d → ℝ) (hf : Measurable f) (hg : Measurable g),
        f = g → emStep f hf D h = emStep g hg D h := by
      rintro f g hf hg rfl; rfl
    show emStep (b₁ (k * h)) _ D h ∘ₖ tdPow b₁ hb₁ D h k =
      emStep (b₂ (k * h)) _ D h ∘ₖ tdPow b₂ hb₂ D h k
    rw [ih fun j hj => hk j (by omega)]
    congr 1
    exact e _ _ _ _ (hk k (Nat.lt_succ_self k))

/-- Two drift families agreeing on `[0, T]` give the same dyadic laws at times `t ≤ T`. -/
theorem tdCurve_congr {b₁ b₂ : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hb₁ : ∀ t, Measurable (b₁ t))
    (hb₂ : ∀ t, Measurable (b₂ t)) (D : ℝ) (ρ₀ : Measure (Fin d → ℝ)) (n : ℕ) {t T : ℝ}
    (hT : 0 ≤ T) (htT : t ≤ T) (h : ∀ s ∈ Icc 0 T, b₁ s = b₂ s) :
    tdCurve b₁ hb₁ D ρ₀ n t = tdCurve b₂ hb₂ D ρ₀ n t := by
  unfold tdCurve
  rw [tdPow_congr hb₁ hb₂ D (dyadicStep n) fun j hj => h _ ⟨by
    have := (dyadicStep_pos n).le; positivity, ?_⟩]
  have hkh := (gridIndex_mul_le n t).trans (max_le htT hT)
  have hj' : (j : ℝ) ≤ gridIndex n t := by exact_mod_cast hj.le
  calc (j : ℝ) * dyadicStep n ≤ gridIndex n t * dyadicStep n :=
        mul_le_mul_of_nonneg_right hj' (dyadicStep_pos n).le
    _ ≤ T := hkh

/-- **Global hypotheses for the time-clamped drift.** If on `[0, T]` (`T ≥ 0`) each `b t` is
`L`-Lipschitz and `‖b t x - b s x‖ ≤ K √|t - s| (1 + ‖x‖)`, then `b ∘ clampTime T` satisfies
these for all times with `K' = max K 0`, and has linear growth with
`B = L + K' √T + ‖b 0 0‖`. -/
theorem clamp_hyps {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {T : ℝ} (hT : 0 ≤ T) {L : ℝ≥0}
    (hL : ∀ t ∈ Icc 0 T, LipschitzWith L (b t)) {K : ℝ}
    (hK : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x, ‖b t x - b s x‖ ≤ K * Real.sqrt |t - s| * (1 + ‖x‖)) :
    (∀ t, LipschitzWith L (b (clampTime T t))) ∧
    (∀ t x, ‖b (clampTime T t) x‖ ≤
      (L + max K 0 * Real.sqrt T + ‖b 0 0‖) * (1 + ‖x‖)) ∧
    (∀ s t x, ‖b (clampTime T t) x - b (clampTime T s) x‖ ≤
      max K 0 * Real.sqrt |t - s| * (1 + ‖x‖)) := by
  have hK' : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
      ‖b t x - b s x‖ ≤ max K 0 * Real.sqrt |t - s| * (1 + ‖x‖) := by
    intro s hs t ht x
    refine (hK s hs t ht x).trans ?_
    gcongr
    exact le_max_left _ _
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  refine ⟨fun t => hL _ (clampTime_mem hT t), fun t x => ?_, fun s t x => ?_⟩
  · set τ := clampTime T t
    have hτ := clampTime_mem hT t
    have h1 : ‖b τ x - b τ 0‖ ≤ L * ‖x‖ := by
      have := (hL τ hτ).norm_sub_le x 0
      simpa using this
    have h2 : ‖b τ 0 - b 0 0‖ ≤ max K 0 * Real.sqrt T := by
      have := hK' 0 h0 τ hτ 0
      simp only [norm_zero, add_zero, mul_one, sub_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (le_max_right _ _))
      rw [abs_of_nonneg hτ.1]; exact hτ.2
    have h3 : ‖b τ x‖ ≤ ‖b τ x - b τ 0‖ + ‖b τ 0 - b 0 0‖ + ‖b 0 0‖ := by
      have e : b τ x = (b τ x - b τ 0) + (b τ 0 - b 0 0) + b 0 0 := by abel
      calc ‖b τ x‖ = ‖(b τ x - b τ 0) + (b τ 0 - b 0 0) + b 0 0‖ := by rw [← e]
        _ ≤ _ := norm_add₃_le
    have hx := norm_nonneg x
    have hKs : 0 ≤ max K 0 * Real.sqrt T := by positivity
    have hb0 := norm_nonneg (b 0 0)
    nlinarith [L.coe_nonneg, mul_nonneg hKs hx, mul_nonneg hb0 hx]
  · refine (hK' _ (clampTime_mem hT s) _ (clampTime_mem hT t) x).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (abs_clampTime_sub_le T s t)) (le_max_right _ _)) (by positivity)

/-- **Existence for the weak Fokker–Planck equation, time-dependent drift, local hypotheses
(Verified, no Itô input).** Let `b : ℝ → ℝᵈ → ℝᵈ` have measurable slices `b t`, and suppose
that on every bounded time interval `[0, T]`:

* `b t` is Lipschitz in `x`, uniformly in `t ∈ [0, T]` (constant `L_T`);
* `‖b t x - b s x‖ ≤ K_T √|t - s| (1 + ‖x‖)` for `s, t ∈ [0, T]` (Hölder-`½` in time with linear
  weight; e.g. any `b` that is Lipschitz in `t` with this weight).

(Linear growth `‖b t x‖ ≤ B_T (1 + ‖x‖)` on `[0, T]` follows.) Let `D > 0` and `ρ₀` be any
probability measure on `Fin d → ℝ`. Then there is a weakly continuous curve
`ν : ℝ → 𝒫(ℝᵈ)` with `ν 0 = ρ₀` solving `WeakFokkerPlanck (fun t => ν t) b D`, and `ν t` is,
at every time `t`, the weak limit of the dyadic time-dependent Euler–Maruyama laws
`tdCurve b hb D ρ₀ n t` (step `2⁻ⁿ`, drift frozen at the left grid point). -/
theorem exists_weakFokkerPlanck_time {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hb : ∀ t, Measurable (b t))
    (hL : ∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (b t))
    (hK : ∀ T, ∃ K : ℝ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
      ‖b t x - b s x‖ ≤ K * Real.sqrt |t - s| * (1 + ‖x‖))
    {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ν : ℝ → ProbabilityMeasure (Fin d → ℝ), (ν 0 : Measure (Fin d → ℝ)) = ρ₀ ∧
      Continuous ν ∧ WeakFokkerPlanck (fun t => (ν t : Measure (Fin d → ℝ))) b D ∧
      ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)) := by
  -- global solutions for the clamped drifts `b ∘ clampTime N`
  have glob : ∀ N : ℕ, ∃ νN : ℝ → ProbabilityMeasure (Fin d → ℝ), Continuous νN ∧
      WeakFokkerPlanck (fun t => (νN t : Measure (Fin d → ℝ)))
        (fun t => b (clampTime N t)) D ∧
      ∀ t : ℝ, t ≤ N → Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (νN t)) := by
    intro N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    obtain ⟨L, hLN⟩ := hL N
    obtain ⟨K, hKN⟩ := hK N
    obtain ⟨h1, h2, h3⟩ := clamp_hyps hN hLN hKN
    have hbN : ∀ t, Measurable (b (clampTime N t)) := fun t => hb _
    obtain ⟨νN, -, hc, hfp, htd⟩ := exists_weakFokkerPlanck_global hbN h1 h2 h3 hD ρ₀
    refine ⟨νN, hc, hfp, fun t ht => ?_⟩
    have e : (fun n => tdCurveP b hb D ρ₀ n t) =
        fun n => tdCurveP (fun t => b (clampTime N t)) hbN D ρ₀ n t := by
      funext n
      apply Subtype.ext
      exact tdCurve_congr hb hbN D ρ₀ n hN ht fun s hs => by
        simp only [clampTime_of_mem hs]
    rw [e]
    exact htd t
  choose νN hcN hfpN htdN using glob
  set ν : ℝ → ProbabilityMeasure (Fin d → ℝ) := fun t => νN ⌈t⌉₊ t with hνdef
  have hνt : ∀ t, Tendsto (fun n => tdCurveP b hb D ρ₀ n t) atTop (𝓝 (ν t)) := fun t =>
    htdN ⌈t⌉₊ t (Nat.le_ceil t)
  have hagree : ∀ (N : ℕ) (t : ℝ), t ≤ N → νN N t = ν t := fun N t ht =>
    tendsto_nhds_unique (htdN N t ht) (hνt t)
  refine ⟨ν, ?_, ?_, ?_, hνt⟩
  · have hc : (fun n => tdCurveP b hb D ρ₀ n 0) = fun _ => ⟨ρ₀, inferInstance⟩ := by
      funext n; apply Subtype.ext; exact tdCurve_of_nonpos hb ρ₀ n le_rfl
    have := tendsto_nhds_unique (hνt 0) (by rw [hc]; exact tendsto_const_nhds)
    rw [this]; rfl
  · rw [continuous_iff_continuousAt]
    intro r₀
    set N := ⌈r₀⌉₊ + 1
    have hr : r₀ < N := by
      have := Nat.le_ceil r₀
      simp only [N]; push_cast; linarith
    refine (hcN N).continuousAt.congr ?_
    filter_upwards [eventually_lt_nhds hr] with r hr'
    exact hagree N r hr'.le
  · intro φ hφ t ht
    set N := ⌈t⌉₊ + 1
    have hr : t < N := by
      have := Nat.le_ceil t
      simp only [N]; push_cast; linarith
    have hmem : t ∈ Icc 0 (N : ℝ) := ⟨ht, hr.le⟩
    have hd := hfpN N φ hφ t ht
    simp only [clampTime_of_mem hmem, hagree N t hr.le] at hd
    refine hd.congr_of_eventuallyEq ?_ (by simp only [hagree N t hr.le])
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hr)] with s hs
    simp only [hagree N s hs.le]

/-- **Measure-curve form (Itô input of FL-5, time-dependent drift).** Under the hypotheses of
`exists_weakFokkerPlanck_time`, there is `ρ : ℝ → Measure (Fin d → ℝ)` with `ρ 0 = ρ₀`, every
`ρ t` a probability measure, and `WeakFokkerPlanck ρ b D`. -/
theorem exists_weakFokkerPlanck_time_measure {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hb : ∀ t, Measurable (b t))
    (hL : ∀ T, ∃ L : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzWith L (b t))
    (hK : ∀ T, ∃ K : ℝ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
      ‖b t x - b s x‖ ≤ K * Real.sqrt |t - s| * (1 + ‖x‖))
    {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ b D := by
  obtain ⟨ν, h0, -, hfp, -⟩ := exists_weakFokkerPlanck_time hb hL hK hD ρ₀
  exact ⟨fun t => ν t, h0, fun t => inferInstance, hfp⟩

end FormalizeSampling.FokkerPlanckExistence
