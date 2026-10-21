module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import FormalizeSampling.Foundations.LogSobolevExtension
public import FormalizeSampling.Foundations.LogSobolevPi
public import FormalizeSampling.Foundations.GaussianLSIPi

/-!
# Extending the functional log-Sobolev inequality beyond `LSIClassPi` (`Fin d → ℝ`)

Status: **Verified** for the extension theorems and the KL/Fisher bridge (no hypothesis beyond
the functional LSI that is their input and the stated integrability).

This is the `Fin d → ℝ` version of `Foundations/LogSobolevExtension.lean`. `FunctionalLSIPi μ C`
(`Foundations/LogSobolevPi.lean`) quantifies only over `LSIClassPi` (differentiable, bounded,
bounded `gradSq`, bounded below by `c > 0`), which `√(p_t/q_t)` typically violates; this file
removes the class condition.

Route.
1. *Spatial cut-off* (`ent_sq_le_of_bounded`). The 1D trick (compose with a primitive of a
   weight whose transition layer has small mass, so the test function is constant outside) has
   no analogue in dimension `d ≥ 2` with bounded gradient. Instead, for `g` with continuous
   partial derivatives, `c ≤ g ≤ M` (`c > 0`) and `‖∇g‖² ∈ L¹(μ)`, put
   `h_n = c + θ_n (g - c)` with `θ_n(x) = v(⟨x⟩ - n)`, `⟨x⟩ = √(1 + ‖x‖²)` and `v` a `C¹`
   profile equal to `1` on `(-∞, 0]` and `0` on `[1, ∞)`. Then `h_n ∈ LSIClassPi` (`θ_n` has
   compact support, where `∇g` is bounded), `c ≤ h_n ≤ M`, `h_n = g` near any fixed point for `n`
   large, and `‖∇h_n‖² ≤ 2 ‖∇g‖² + 2 (M - c)² sup|v'|²` uniformly in `n`, so both
   `Ent_μ(h_n²)` and `∫ ‖∇h_n‖² dμ` converge by dominated convergence.
2. *Value cut-off* (`ent_sq_le_of_functionalLSIPi`). For positive `g`, `g_N = φ_N ∘ g` with the
   value cut-off `φ_N` of `LogSobolevExtension`; `‖∇g_N‖ ≤ ‖∇g‖`, step 1 applies, and
   `Ent_μ(g_N²) → Ent_μ(g²)` by dominated convergence (dominated by `g² + 1` and
   `|g² log g²| + 1`).
3. *Bridge* (`heatKL_le_of_functionalLSIPi_of_integrable`). `g = √(p_t/q_t)` is positive with
   continuous partial derivatives, and under `π_t = q_t dx`: `q_t ‖∇g‖² = ¼ · fisherIntegrand`,
   `q_t g² = p_t`, `q_t g² log g² = klIntegrand`; so integrability of the KL and Fisher
   integrands (fields of `HeatFlowRegularPi`) is all that is needed.

## Main results

* `ent_sq_le_of_bounded`: `FunctionalLSIPi μ C`, `μ` a probability measure, `g` differentiable
  with continuous partial derivatives, `c ≤ g ≤ M` (`c > 0`), `gradSq g ∈ L¹(μ)` ⇒
  `Ent_μ(g²) ≤ 2 C ∫ gradSq g dμ`.
* `ent_sq_le_of_functionalLSIPi` (**extension**): the same for every `g > 0` differentiable with
  continuous partial derivatives and `gradSq g, g², g² log g² ∈ L¹(μ)`, `C ≥ 0`.
* `heatKL_le_of_functionalLSIPi_of_integrable` (**bridge**): for `t > 0`, `C ≥ 0`,
  `FunctionalLSIPi (heatKernelPi t ∘ₘ π) C` and integrable KL and Fisher integrands at `t`:
  `heatKL ρ π t ≤ C/2 · heatFisher ρ π t`.
* `heatFlowLSIPi_of_functionalLSIPi`: `FunctionalLSIPi π_t (1/α + t)` on `(0, η)` and
  `HeatFlowRegularPi` ⇒ `2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` on `(0, η)`.
* The PX-2 corollaries `toReal_klDiv_proxKernelPi_comp_le_of_heatFlowLSI` (and `_Ioi`) are in
  `Samplers/ProximalLSIPi.lean`.

## Not proved here

* Convolution stability `FunctionalLSIPi π C ⇒ FunctionalLSIPi (heatKernelPi t ∘ₘ π) (C + t)`:
  here `heatFlowLSIPi_of_functionalLSIPi` takes the LSI of every `π_t`, `t ∈ (0, η)`, as
  hypothesis. Convolution stability is `LogSobolevTensorPi.functionalLSIPi_heatKernelPi_comp`.
* `HeatFlowRegularPi ρ (targetPi f) s` for non-Gaussian `f`, and the target LSI itself for
  non-Gaussian `f` (Bakry–Émery, Holley–Stroock).
* Test functions that vanish somewhere or are merely Sobolev (`H¹(μ)`); the extension is not
  packaged as a new LSI predicate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal
open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevPi

namespace FormalizeSampling.LogSobolevExtensionPi

open FormalizeSampling.LogSobolevExtension (prim hasDerivAt_prim valueWeight continuous_valueWeight
  valueWeight_nonneg valueWeight_le_one valueCut_eq valueCut_mem valueCut_dom tendsto_ent)
open FormalizeSampling.HeatFlowDeBruijnPi (dotCLM dotCLM_apply dotCLM_single hasFDerivAt_sum_sq)

variable {d : ℕ}

/-! ### Elementary facts -/

/-- Elementary bound `∑ᵢ (s aᵢ + r bᵢ)² ≤ 2 s² ∑ᵢ aᵢ² + 2 r² ∑ᵢ bᵢ²`. -/
theorem sum_sq_add_le (a b : Fin d → ℝ) (s r : ℝ) :
    ∑ i, (s * a i + r * b i) ^ 2 ≤ 2 * s ^ 2 * ∑ i, a i ^ 2 + 2 * r ^ 2 * ∑ i, b i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (s * a i - r * b i)]

/-! ### The spatial cut-off -/

/-- The one-dimensional cut-off profile `v(s) = smoothTransition (1 - s)`: smooth, with values in
`[0, 1]`, equal to `1` on `s ≤ 0` and to `0` on `s ≥ 1`. -/
noncomputable def cutProfile (s : ℝ) : ℝ := Real.smoothTransition (1 - s)

/-- The cut-off profile equals `1` on `s ≤ 0`. -/
theorem cutProfile_eq_one {s : ℝ} (hs : s ≤ 0) : cutProfile s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The cut-off profile vanishes on `s ≥ 1`. -/
theorem cutProfile_eq_zero {s : ℝ} (hs : 1 ≤ s) : cutProfile s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The cut-off profile is nonnegative. -/
theorem cutProfile_nonneg (s : ℝ) : 0 ≤ cutProfile s := Real.smoothTransition.nonneg _

/-- The cut-off profile is at most `1`. -/
theorem cutProfile_le_one (s : ℝ) : cutProfile s ≤ 1 := Real.smoothTransition.le_one _

/-- The cut-off profile is `C¹`. -/
theorem contDiff_cutProfile : ContDiff ℝ 1 cutProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- The cut-off profile is differentiable everywhere. -/
theorem hasDerivAt_cutProfile (s : ℝ) : HasDerivAt cutProfile (deriv cutProfile s) s :=
  ((contDiff_cutProfile.differentiable one_ne_zero) s).hasDerivAt

/-- The derivative of the cut-off profile is bounded (it is continuous and vanishes off
`[0, 1]`). -/
theorem exists_abs_deriv_cutProfile_le : ∃ B, ∀ s, |deriv cutProfile s| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_cutProfile.continuous_deriv le_rfl).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨B, fun s => ?_⟩
  rcases lt_or_ge s 0 with h | h
  · have : cutProfile =ᶠ[𝓝 s] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds h] with y hy using cutProfile_eq_one hy.le
    rw [this.deriv_eq]; simpa using hB0
  rcases le_or_gt s 1 with h' | h'
  · simpa [Real.norm_eq_abs] using hB s ⟨h, h'⟩
  · have : cutProfile =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h'] with y hy using cutProfile_eq_zero (le_of_lt hy)
    rw [this.deriv_eq]; simpa using hB0

/-- The smooth radius `⟨x⟩ = √(1 + ∑ᵢ xᵢ²)` on `Fin d → ℝ`. -/
noncomputable def japBracket (x : Fin d → ℝ) : ℝ := Real.sqrt (1 + ∑ i, x i ^ 2)

/-- `⟨x⟩ > 0`. -/
theorem japBracket_pos (x : Fin d → ℝ) : 0 < japBracket x :=
  Real.sqrt_pos.2 (by positivity)

/-- `⟨x⟩² = 1 + ∑ᵢ xᵢ²`. -/
theorem sq_japBracket (x : Fin d → ℝ) : japBracket x ^ 2 = 1 + ∑ i, x i ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `x ↦ ⟨x⟩` is continuous. -/
theorem continuous_japBracket : Continuous (japBracket (d := d)) := by
  unfold japBracket; fun_prop

/-- Each coordinate satisfies `|xᵢ| ≤ ⟨x⟩`. -/
theorem abs_le_japBracket (x : Fin d → ℝ) (i : Fin d) : |x i| ≤ japBracket x :=
  Real.abs_le_sqrt (by
    have := Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
    linarith)

/-- Gradient of the smooth radius: `∇⟨x⟩ = x / ⟨x⟩`. -/
theorem hasFDerivAt_japBracket (x : Fin d → ℝ) :
    HasFDerivAt japBracket (dotCLM fun i => x i / japBracket x) x := by
  have h := ((hasFDerivAt_sum_sq x).const_add 1).sqrt (by positivity)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [smul_apply, dotCLM_apply, smul_eq_mul, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := japBracket_pos x
  unfold japBracket at this ⊢
  field_simp

/-- The spatial cut-off `θ_n(x) = v(⟨x⟩ - n)`: equal to `1` on `⟨x⟩ ≤ n`, to `0` on
`⟨x⟩ ≥ n + 1`, with values in `[0, 1]`. -/
noncomputable def cutoff (n : ℝ) (x : Fin d → ℝ) : ℝ := cutProfile (japBracket x - n)

/-- Gradient of the spatial cut-off: `∂ᵢθ_n(x) = v'(⟨x⟩ - n) · xᵢ / ⟨x⟩`. -/
theorem hasFDerivAt_cutoff (n : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (cutoff n)
      (dotCLM fun i => deriv cutProfile (japBracket x - n) * (x i / japBracket x)) x := by
  have h := (hasDerivAt_cutProfile (japBracket x - n)).comp_hasFDerivAt x
    ((hasFDerivAt_japBracket x).sub_const n)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [smul_apply, dotCLM_apply, smul_eq_mul, dotProduct,
    Finset.mul_sum, mul_assoc]

/-- The gradient of the spatial cut-off is bounded uniformly in `n`: if `|v'| ≤ B` then
`∑ᵢ (∂ᵢθ_n(x))² ≤ B²` (because `|∇⟨x⟩| ≤ 1`). -/
theorem sum_sq_cutoff_le {B : ℝ} (hB : ∀ s, |deriv cutProfile s| ≤ B) (n : ℝ)
    (x : Fin d → ℝ) :
    ∑ i, (deriv cutProfile (japBracket x - n) * (x i / japBracket x)) ^ 2 ≤ B ^ 2 := by
  set v := deriv cutProfile (japBracket x - n)
  have hΛ := japBracket_pos x
  have h1 : ∑ i, (v * (x i / japBracket x)) ^ 2 =
      v ^ 2 * ((∑ i, x i ^ 2) / japBracket x ^ 2) := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i, x i ^ 2) / japBracket x ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity), sq_japBracket]; linarith
  have h3 : v ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
  rw [h1]
  have : 0 ≤ (∑ i, x i ^ 2) / japBracket x ^ 2 := by positivity
  nlinarith [sq_nonneg v]

/-! ### Step 1: bounded test functions with square-integrable gradient -/

/-- **Extension to bounded `C¹` test functions with square-integrable gradient.** Let `μ` be a
probability measure on `Fin d → ℝ` with `FunctionalLSIPi μ C`, and let `g` be differentiable with
continuous partial derivatives, `c ≤ g ≤ M` for some `c > 0`, and `‖∇g‖² = gradSq g` integrable
under `μ` (`∇g` may be unbounded). Then `Ent_μ(g²) ≤ 2 C ∫ ‖∇g‖² dμ`. (Route: the test functions
`h_n = c + θ_n (g - c)` lie in `LSIClassPi`, equal `g` near any fixed point for `n` large, and
satisfy `‖∇h_n‖² ≤ 2 ‖∇g‖² + 2 (M - c)² B²`; both sides of the LSI for `h_n` converge by
dominated convergence.) -/
theorem ent_sq_le_of_bounded {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {C : ℝ}
    (hLSI : FunctionalLSIPi μ C) {g : (Fin d → ℝ) → ℝ} (hd : Differentiable ℝ g)
    (hcont : ∀ i, Continuous fun x => fderiv ℝ g x (Pi.single i 1)) {c M : ℝ} (hc : 0 < c)
    (hcg : ∀ x, c ≤ g x) (hgM : ∀ x, g x ≤ M) (hi : Integrable (gradSq g) μ) :
    ent μ (fun x => g x ^ 2) ≤ 2 * C * ∫ x, gradSq g x ∂μ := by
  obtain ⟨B, hB⟩ := exists_abs_deriv_cutProfile_le
  set h : ℕ → (Fin d → ℝ) → ℝ := fun n x => c + cutoff n x * (g x - c) with hh
  have hhd : ∀ n x, HasFDerivAt (h n) (cutoff n x • fderiv ℝ g x + (g x - c) •
      dotCLM fun i => deriv cutProfile (japBracket x - n) * (x i / japBracket x)) x :=
    fun n x => (((hasFDerivAt_cutoff n x).mul ((hd x).hasFDerivAt.sub_const c))).const_add c
  have hgr : ∀ n x, gradSq (h n) x = ∑ i, (cutoff n x * fderiv ℝ g x (Pi.single i 1) +
      (g x - c) * (deriv cutProfile (japBracket x - n) * (x i / japBracket x))) ^ 2 := by
    intro n x
    simp only [gradSq, (hhd n x).fderiv, add_apply, smul_apply,
      dotCLM_single, smul_eq_mul]
  have hθ0 : ∀ (n : ℕ) (x : Fin d → ℝ), 0 ≤ cutoff n x := fun n x => cutProfile_nonneg _
  have hθ1 : ∀ (n : ℕ) (x : Fin d → ℝ), cutoff n x ≤ 1 := fun n x => cutProfile_le_one _
  have hgrle : ∀ n x, gradSq (h n) x ≤
      2 * cutoff n x ^ 2 * gradSq g x + 2 * (M - c) ^ 2 * B ^ 2 := by
    intro n x
    rw [hgr]
    refine (sum_sq_add_le _ _ _ _).trans ?_
    have h1 := sum_sq_cutoff_le hB n x
    have h2 : (g x - c) ^ 2 ≤ (M - c) ^ 2 :=
      pow_le_pow_left₀ (by linarith [hcg x]) (by linarith [hgM x]) 2
    have h3 : 0 ≤ ∑ i, (deriv cutProfile (japBracket x - n) * (x i / japBracket x)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : (g x - c) ^ 2 * ∑ i, (deriv cutProfile (japBracket x - n) * (x i / japBracket x)) ^ 2
        ≤ (M - c) ^ 2 * B ^ 2 :=
      mul_le_mul h2 h1 h3 (sq_nonneg _)
    unfold gradSq; linarith
  have hgdom : ∀ n x, gradSq (h n) x ≤ 2 * gradSq g x + 2 * (M - c) ^ 2 * B ^ 2 := by
    intro n x
    have : cutoff n x ^ 2 ≤ 1 := by nlinarith [hθ0 n x, hθ1 n x]
    have := gradSq_nonneg g x
    nlinarith [hgrle n x]
  have hgc : Continuous (gradSq g) := by
    unfold gradSq; exact continuous_finsetSum _ fun i _ => (hcont i).pow 2
  have hbd : ∀ n : ℕ, ∃ K, ∀ x, gradSq (h n) x ≤ K := by
    intro n
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Fin d → ℝ)
      ((n : ℝ) + 1)).exists_bound_of_continuousOn hgc.continuousOn
    refine ⟨2 * max K 0 + 2 * (M - c) ^ 2 * B ^ 2, fun x => (hgrle n x).trans ?_⟩
    rcases le_or_gt ((n : ℝ) + 1) (japBracket x) with hx | hx
    · rw [show cutoff n x = 0 from cutProfile_eq_zero (by linarith)]
      have : 0 ≤ max K 0 := le_max_right _ _
      nlinarith
    · have hmem : x ∈ Metric.closedBall (0 : Fin d → ℝ) ((n : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
        intro i; rw [Real.norm_eq_abs]; exact (abs_le_japBracket x i).trans hx.le
      have hk := hK x hmem
      rw [Real.norm_of_nonneg (gradSq_nonneg g x)] at hk
      have : cutoff n x ^ 2 ≤ 1 := by nlinarith [hθ0 n x, hθ1 n x]
      have := gradSq_nonneg g x
      have : gradSq g x ≤ max K 0 := hk.trans (le_max_left _ _)
      nlinarith
  have hbnd : ∀ n x, c ≤ h n x ∧ h n x ≤ M := by
    intro n x
    have := hcg x; have := hgM x; have := hθ0 n x; have := hθ1 n x
    constructor <;> simp only [hh] <;> nlinarith
  have hcls : ∀ n, LSIClassPi (h n) := fun n =>
    ⟨fun x => (hhd n x).differentiableAt,
      ⟨M, fun x => abs_le.2 ⟨by linarith [(hbnd n x).1, hcg x, hgM x], (hbnd n x).2⟩⟩, hbd n,
      ⟨c, hc, fun x => (hbnd n x).1⟩⟩
  have hev : ∀ x, ∀ᶠ n : ℕ in atTop, h n =ᶠ[𝓝 x] g := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (japBracket x + 1)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hU : {y | japBracket y < japBracket x + 1} ∈ 𝓝 x :=
      (isOpen_lt continuous_japBracket continuous_const).mem_nhds (by simp)
    filter_upwards [hU] with y hy
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hy' : japBracket y < japBracket x + 1 := hy
    have h1 : cutoff n y = 1 := cutProfile_eq_one (by linarith)
    simp only [hh, h1, one_mul, add_sub_cancel]
  have hlimE : Tendsto (fun n => ent μ (fun x => h n x ^ 2)) atTop
      (𝓝 (ent μ fun x => g x ^ 2)) := by
    refine tendsto_ent (B := fun _ => M ^ 2) (B' := fun _ => (M ^ 2) ^ 2 + 1)
      (fun n => ((continuous_iff_continuousAt.2 fun x =>
        (hhd n x).continuousAt).pow 2).aestronglyMeasurable)
      (integrable_const _) (integrable_const _) (fun n x => ?_) (fun n x => ?_) (fun x => ?_)
    · have h0 : 0 ≤ h n x := hc.le.trans (hbnd n x).1
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h0 (hbnd n x).2 2
    · have h0 : 0 ≤ h n x := hc.le.trans (hbnd n x).1
      have h1 : h n x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ h0 (hbnd n x).2 2
      refine (abs_mul_log_le (sq_nonneg _)).trans ?_
      gcongr
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.eq_of_nhds]
  have hlimG : Tendsto (fun n => ∫ x, gradSq (h n) x ∂μ) atTop (𝓝 (∫ x, gradSq g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * gradSq g x + 2 * (M - c) ^ 2 * B ^ 2)
      (fun n => (measurable_gradSq _).aestronglyMeasurable)
      ((hi.const_mul 2).add (integrable_const _))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_of_nonneg (gradSq_nonneg _ x)]; exact hgdom n x
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      simp only [gradSq, hn.fderiv_eq]
  have hle : ∀ n, ent μ (fun x => h n x ^ 2) ≤ 2 * C * ∫ x, gradSq (h n) x ∂μ :=
    fun n => hLSI (h n) (hcls n)
  exact le_of_tendsto_of_tendsto' hlimE (hlimG.const_mul (2 * C)) hle

/-! ### Step 2: the value cut-off -/

/-- **Functional LSI on `Fin d → ℝ` for unbounded test functions (extension).** Let `μ` be a
probability measure with `FunctionalLSIPi μ C`, `C ≥ 0`, and let `g` be positive, differentiable,
with continuous partial derivatives, and with `‖∇g‖² = gradSq g`, `g²` and `g² log g²` integrable
under `μ` (no boundedness of `g` or `∇g`, no lower bound beyond positivity). Then
`Ent_μ(g²) ≤ 2 C ∫ ‖∇g‖² dμ`. (Route: `g_N = φ_N ∘ g` with the value cut-off `φ_N` of
`LogSobolevExtension`, so `1/(2N) ≤ g_N ≤ N + 1` and `‖∇g_N‖ ≤ ‖∇g‖`; `ent_sq_le_of_bounded`
applies to `g_N`, and `Ent_μ(g_N²) → Ent_μ(g²)` by dominated convergence.) -/
theorem ent_sq_le_of_functionalLSIPi {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {C : ℝ}
    (hLSI : FunctionalLSIPi μ C) (hC : 0 ≤ C) {g : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < g x)
    (hd : Differentiable ℝ g) (hcont : ∀ i, Continuous fun x => fderiv ℝ g x (Pi.single i 1))
    (hi : Integrable (gradSq g) μ) (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hgl : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ) :
    ent μ (fun x => g x ^ 2) ≤ 2 * C * ∫ x, gradSq g x ∂μ := by
  set G : ℕ → (Fin d → ℝ) → ℝ := fun n x => prim (valueWeight ((n : ℝ) + 1)) 1 (g x) with hG
  have hN : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hGd : ∀ n x, HasFDerivAt (G n)
      (valueWeight ((n : ℝ) + 1) (g x) • fderiv ℝ g x) x :=
    fun n x => (hasDerivAt_prim (continuous_valueWeight _) 1 (g x)).comp_hasFDerivAt x
      (hd x).hasFDerivAt
  have hGp : ∀ n x i, fderiv ℝ (G n) x (Pi.single i 1) =
      valueWeight ((n : ℝ) + 1) (g x) * fderiv ℝ g x (Pi.single i 1) := fun n x i => by
    rw [(hGd n x).fderiv, smul_apply, smul_eq_mul]
  have hGgr : ∀ n x, gradSq (G n) x = valueWeight ((n : ℝ) + 1) (g x) ^ 2 * gradSq g x := by
    intro n x
    simp only [gradSq, hGp, mul_pow, Finset.mul_sum]
  have hsq : ∀ n x, gradSq (G n) x ≤ gradSq g x := by
    intro n x
    rw [hGgr]
    have h0 := valueWeight_nonneg ((n : ℝ) + 1) (g x)
    have h1 := valueWeight_le_one ((n : ℝ) + 1) (g x)
    have : valueWeight ((n : ℝ) + 1) (g x) ^ 2 ≤ 1 := by nlinarith
    nlinarith [gradSq_nonneg g x]
  have hGi : ∀ n, Integrable (gradSq (G n)) μ := fun n =>
    hi.mono' (measurable_gradSq _).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (gradSq_nonneg _ _)]; exact hsq n x)
  have hent : ∀ n, ent μ (fun x => G n x ^ 2) ≤ 2 * C * ∫ x, gradSq g x ∂μ := by
    intro n
    have hb := fun x => valueCut_mem (hN n) (g x)
    have h1 := ent_sq_le_of_bounded hLSI (g := G n) (fun x => (hGd n x).differentiableAt)
      (fun i => by
        simp only [hGp]
        exact ((continuous_valueWeight _).comp hd.continuous).mul (hcont i))
      (by have := hN n; positivity) (fun x => (hb x).1) (fun x => (hb x).2) (hGi n)
    exact h1.trans (mul_le_mul_of_nonneg_left (integral_mono (hGi n) hi (hsq n))
      (by positivity))
  have hlim : Tendsto (fun n => ent μ (fun x => G n x ^ 2)) atTop
      (𝓝 (ent μ fun x => g x ^ 2)) := by
    refine tendsto_ent (B := fun x => g x ^ 2 + 1)
      (B' := fun x => |g x ^ 2 * Real.log (g x ^ 2)| + 1)
      (fun n => (((continuous_iff_continuousAt.2 fun x =>
        (hGd n x).continuousAt)).pow 2).aestronglyMeasurable)
      (hg2.add (integrable_const _)) (hgl.abs.add (integrable_const _))
      (fun n x => ?_) (fun n x => (valueCut_dom (hN n) (hpos x)).2) (fun x => ?_)
    · rw [abs_of_nonneg (sq_nonneg _)]
      exact (valueCut_dom (hN n) (hpos x)).1
    · obtain ⟨N, hN'⟩ := exists_nat_ge (max (g x) (1 / g x))
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      have hn' : max (g x) (1 / g x) ≤ (n : ℝ) + 1 :=
        hN'.trans ((Nat.cast_le.2 hn).trans (by linarith))
      have h1 : 1 / ((n : ℝ) + 1) ≤ g x := by
        rw [div_le_iff₀ (by linarith [hN n])]
        have := (le_max_right _ _).trans hn'
        rw [div_le_iff₀ (hpos x)] at this
        linarith
      simp only [hG, valueCut_eq (hN n) h1 ((le_max_left _ _).trans hn')]
  exact le_of_tendsto' hlim hent

/-! ### The KL/Fisher bridge and PX-2 -/

section Bridge

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
open FormalizeSampling.GaussianLSIPi (continuous_heatFlowGradPi integrable_heatFlowDensityPi)

/-- Integrals against `π_t = heatKernelPi t ∘ₘ π` (`t > 0`, `π` a probability measure) are
Lebesgue integrals against the density `q_t = heatFlowDensityPi π t`. -/
theorem integral_heatKernelPi_comp (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] {t : ℝ}
    (ht : 0 < t) (F : (Fin d → ℝ) → ℝ) :
    ∫ y, F y ∂(heatKernelPi t.toNNReal ∘ₘ π) = ∫ y, heatFlowDensityPi π t y * F y := by
  rw [heatKernelPi_comp_eq_withDensity π ht, integral_withDensity_eq_integral_toReal_smul
    (continuous_heatFlowDensityPi π ht).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (heatFlowDensityPi_pos π ht y).le, smul_eq_mul]

/-- Integrability against `π_t = heatKernelPi t ∘ₘ π` (`t > 0`) is Lebesgue integrability of
`q_t · F`, `q_t = heatFlowDensityPi π t`. -/
theorem integrable_heatKernelPi_comp_iff (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    {t : ℝ} (ht : 0 < t) (F : (Fin d → ℝ) → ℝ) :
    Integrable F (heatKernelPi t.toNNReal ∘ₘ π) ↔
      Integrable (fun y => heatFlowDensityPi π t y * F y) := by
  rw [heatKernelPi_comp_eq_withDensity π ht, integrable_withDensity_iff_integrable_smul'
    (continuous_heatFlowDensityPi π ht).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (heatFlowDensityPi_pos π ht y).le]

/-- **From the functional LSI of `π_t` to the KL/Fisher LSI at a positive time on `Fin d → ℝ`.**
Let `ρ, π` be probability measures on `Fin d → ℝ`, `t > 0`, `C ≥ 0`, and suppose
`π_t = heatKernelPi t ∘ₘ π` satisfies `FunctionalLSIPi π_t C`. If the KL integrand
`p_t log(p_t/q_t)` and the relative Fisher integrand `p_t ‖∇ log(p_t/q_t)‖²` are Lebesgue
integrable (the fields `integrable_kl`, `integrable_fisher` of `HeatFlowRegularPi`), then
`KL(ρ_t‖π_t) ≤ (C/2) I(ρ_t‖π_t)` (`heatKL`, `heatFisher`). (Applies
`ent_sq_le_of_functionalLSIPi` to `g = √(p_t/q_t)`, for which `q_t ‖∇g‖² = ¼ · fisherIntegrand`,
`q_t g² = p_t` and `q_t g² log g² = klIntegrand`.) -/
theorem heatKL_le_of_functionalLSIPi_of_integrable (ρ π : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hLSI : FunctionalLSIPi (heatKernelPi t.toNNReal ∘ₘ π) C)
    (hkl : Integrable (klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) t))
    (hfi : Integrable (fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
      (heatFlowGradPi ρ) (heatFlowGradPi π) t)) :
    heatKL ρ π t ≤ C / 2 * heatFisher ρ π t := by
  set p := heatFlowDensityPi ρ t with hpdef
  set q := heatFlowDensityPi π t with hqdef
  have hp : ∀ y, 0 < p y := heatFlowDensityPi_pos ρ ht
  have hq : ∀ y, 0 < q y := heatFlowDensityPi_pos π ht
  set g : (Fin d → ℝ) → ℝ := fun y => Real.sqrt (p y / q y) with hg
  have hg0 : ∀ y, 0 < g y := fun y => Real.sqrt_pos.2 (div_pos (hp y) (hq y))
  have hg2 : ∀ y, g y ^ 2 = p y / q y := fun y => Real.sq_sqrt (div_pos (hp y) (hq y)).le
  have hgD : ∀ y, ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, HasFDerivAt g L y ∧ ∀ i, L (Pi.single i 1) =
      (heatFlowGradPi ρ t y i * q y - p y * heatFlowGradPi π t y i) / (2 * g y * q y ^ 2) := by
    intro y
    have hinv := (hasDerivAt_inv (hq y).ne').comp_hasFDerivAt y
      (hasFDerivAt_heatFlowDensityPi π ht y)
    have hdiv := (hasFDerivAt_heatFlowDensityPi ρ ht y).mul hinv
    have hne : (p * (Inv.inv ∘ q)) y ≠ 0 := by
      simp only [Pi.mul_apply, Function.comp_apply]; have := hp y; have := hq y; positivity
    have hs := hdiv.sqrt hne
    refine ⟨_, hs.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_), fun i => ?_⟩
    · simp [hg, div_eq_mul_inv]; rfl
    · simp only [smul_apply, add_apply, dotCLM_single, smul_eq_mul, Function.comp_apply,
        Pi.mul_apply]
      have h1 : Real.sqrt (p y * (q y)⁻¹) = g y := by simp [hg, div_eq_mul_inv]
      rw [h1]
      have := hg0 y; have := hq y
      field_simp
      ring
  choose L hL hLi using hgD
  have hpart : ∀ y i, fderiv ℝ g y (Pi.single i 1) =
      (heatFlowGradPi ρ t y i * q y - p y * heatFlowGradPi π t y i) / (2 * g y * q y ^ 2) :=
    fun y i => by rw [(hL y).fderiv, hLi]
  have hpc : Continuous p := continuous_heatFlowDensityPi ρ ht
  have hqc : Continuous q := continuous_heatFlowDensityPi π ht
  have hgc : Continuous g := Real.continuous_sqrt.comp (hpc.div hqc fun y => (hq y).ne')
  have hdc : ∀ i, Continuous fun y => fderiv ℝ g y (Pi.single i 1) := by
    intro i
    simp only [hpart]
    refine Continuous.div ?_ ((continuous_const.mul hgc).mul (hqc.pow 2)) fun y => by
      have := hg0 y; have := hq y; positivity
    exact ((continuous_heatFlowGradPi ρ ht i).mul hqc).sub
      (hpc.mul (continuous_heatFlowGradPi π ht i))
  have hfish : ∀ y, q y * gradSq g y = fisherIntegrand (heatFlowDensityPi ρ)
      (heatFlowDensityPi π) (heatFlowGradPi ρ) (heatFlowGradPi π) t y / 4 := by
    intro y
    have := hp y
    have := hq y
    have hg2' : (2 * g y * q y ^ 2) ^ 2 = 4 * p y * q y ^ 3 := by
      rw [mul_pow, mul_pow, hg2]; field_simp; norm_num
    simp only [gradSq, hpart, fisherIntegrand, relScore, dotProduct, Finset.mul_sum,
      Finset.sum_div, div_pow, hg2']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← hpdef, ← hqdef]
    field_simp
  have hkl' : ∀ y, q y * (g y ^ 2 * Real.log (g y ^ 2)) =
      klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) t y := by
    intro y
    have := hq y
    rw [hg2, klIntegrand]
    simp only [← hpdef, ← hqdef]
    field_simp
  have hp' : ∀ y, q y * g y ^ 2 = p y := fun y => by
    have := hq y
    rw [hg2]; field_simp
  have hi : Integrable (gradSq g) (heatKernelPi t.toNNReal ∘ₘ π) := by
    rw [integrable_heatKernelPi_comp_iff π ht]
    simp only [← hqdef, hfish]
    exact hfi.div_const 4
  have hi2 : Integrable (fun y => g y ^ 2) (heatKernelPi t.toNNReal ∘ₘ π) := by
    rw [integrable_heatKernelPi_comp_iff π ht]
    simp only [← hqdef, hp']
    exact (integrable_heatFlowDensityPi ρ ht).1
  have hil : Integrable (fun y => g y ^ 2 * Real.log (g y ^ 2))
      (heatKernelPi t.toNNReal ∘ₘ π) := by
    rw [integrable_heatKernelPi_comp_iff π ht]
    simp only [← hqdef, hkl']
    exact hkl
  have hent : ent (heatKernelPi t.toNNReal ∘ₘ π) (fun y => g y ^ 2) = heatKL ρ π t := by
    unfold ent
    rw [integral_heatKernelPi_comp π ht, integral_heatKernelPi_comp π ht,
      heatKL_eq_integral ht hkl]
    have h1 : ∫ y, q y * g y ^ 2 = 1 := by
      simp only [hp']
      exact (integrable_heatFlowDensityPi ρ ht).2
    rw [h1, Real.log_one, mul_zero, sub_zero]
    exact integral_congr_ae (ae_of_all _ hkl')
  have hfi' : ∫ y, gradSq g y ∂(heatKernelPi t.toNNReal ∘ₘ π) = heatFisher ρ π t / 4 := by
    rw [integral_heatKernelPi_comp π ht, heatFisher, ← integral_div]
    exact integral_congr_ae (ae_of_all _ hfish)
  have := ent_sq_le_of_functionalLSIPi hLSI hC hg0 (fun y => (hL y).differentiableAt) hdc hi
    hi2 hil
  rw [hent, hfi'] at this
  linarith

/-- **The LSI hypothesis of `heatKL_le_div_of_regular` from functional LSIs along the flow.** For
probability measures `ρ, π` on `Fin d → ℝ`, `α > 0`, `FunctionalLSIPi (heatKernelPi t ∘ₘ π)
(1/α + t)` for `t ∈ (0, η)` and `HeatFlowRegularPi ρ π s` with `(0, η) ⊆ s`:
`2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` for every `t ∈ (0, η)`. -/
theorem heatFlowLSIPi_of_functionalLSIPi (ρ π : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {α η : ℝ} (hα : 0 < α)
    (hπt : ∀ t ∈ Ioo 0 η, FunctionalLSIPi (heatKernelPi t.toNNReal ∘ₘ π) (1 / α + t))
    {s : Set ℝ} (hreg : HeatFlowRegularPi ρ π s) (hs : Ioo 0 η ⊆ s) :
    ∀ t ∈ Ioo 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * heatFisher ρ π t := by
  intro t ht
  have hC : 0 ≤ 1 / α + t := by have := ht.1; positivity
  have h := heatKL_le_of_functionalLSIPi_of_integrable ρ π ht.1 hC (hπt t ht)
    (hreg.integrable_kl t (hs ht)) (hreg.integrable_fisher t (hs ht))
  have h2 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * α)
  have : 2 * α * ((1 / α + t) / 2 * heatFisher ρ π t) = (1 + α * t) * heatFisher ρ π t := by
    field_simp
  linarith

end Bridge

end FormalizeSampling.LogSobolevExtensionPi
