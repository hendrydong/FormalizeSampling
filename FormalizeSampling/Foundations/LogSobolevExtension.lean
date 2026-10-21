module

public import FormalizeSampling.Foundations.GaussianFunctionalLSI
public import FormalizeSampling.Foundations.HeatFlowRegularity

/-!
# Extending the functional log-Sobolev inequality beyond `LSIClass` (1D)

Status: **Verified** for the extension theorems and the KL/Fisher bridge (no hypothesis beyond
the functional LSI that is their input and the stated integrability).

Motivation: `FunctionalLSI μ C` (`Foundations/LogSobolev.lean`) quantifies only over `LSIClass`
(differentiable, bounded, bounded derivative, bounded below by `c > 0`). Applying it directly to
`g = √(p_t/q_t)` would require `√(p_t/q_t) ∈ LSIClass`, which fails for typical `ρ, π`
(`p_t/q_t` is usually unbounded, e.g. growing like `exp(c y²)`, and tends to `0` somewhere). The
theorems here do not need that class condition.

Route.
1. *Spatial cut-off* (`exists_lsiClass_approx`, `ent_sq_le_of_bounded`). For `g` `C¹` with
   `c ≤ g ≤ M` (`c > 0`) and `(g')² ∈ L¹(μ)` (`g'` possibly unbounded), put `h = g ∘ χ` where
   `χ(x) = ∫_0^x w`, `w` continuous, `w = 1` on `[-n, n]`, `w = 0` off `[-n-δ, n+δ]`,
   `0 ≤ w ≤ 1`. Then `h ∈ LSIClass` (`g'` is bounded on the compact range of `χ` on the support
   of `w`), `h = g` on `[-n, n]`, `(h')² ≤ (g')² + K_n² 1_{n<|x|<n+δ}`, and `δ` is chosen so that
   the `μ`-mass of the layer `{n < |x| < n + δ}` (which decreases to `∅` as `δ ↓ 0`, so no
   atom condition is needed) times `K_n²` is `≤ ε`. Then `Ent_μ(h_n²) → Ent_μ(g²)` by dominated
   convergence (constant domination), giving `Ent_μ(g²) ≤ 2C ∫ (g')² + 2Cε` for all `ε > 0`.
2. *Value cut-off* (`ent_sq_le_of_functionalLSI`). For positive `C¹` `g` put `g_N = φ_N ∘ g` with
   `φ_N(s) = 1 + ∫_1^s v_N`, `v_N` continuous, `= 1` on `[1/N, N]`, `= 0` off
   `(1/(2N), N+1)`, `0 ≤ v_N ≤ 1`. Then `1/(2N) ≤ g_N ≤ N + 1`, `|g_N'| ≤ |g'|`, step 1 applies,
   and `Ent_μ(g_N²) → Ent_μ(g²)` by dominated convergence with dominating functions `g² + 1` and
   `|g² log g²| + 1` (on `{g ≥ 1}`, `1 ≤ g_N ≤ g`; on `{g ≤ 1}`, `|x log x| ≤ 1` for
   `x = g_N² ≤ 1`). So the limit is an actual limit, no Fatou-type argument is needed.
3. *Bridge* (`heatKL_le_of_functionalLSI_of_integrable`). `g = √(p_t/q_t)` is positive and
   `C¹`; under `π_t = q_t dx`, `(g')²`, `g²` and `g² log g²` are integrable exactly when the Fisher
   integrand, `p_t` and the KL integrand are Lebesgue integrable — the fields `integrable_fisher`
   and `integrable_kl` of `HeatFlowRegular` (and `p_t ∈ L¹` always).

## Main results

* `ent_sq_le_of_bounded`: `FunctionalLSI μ C`, `C ≥ 0`, `μ` a probability measure, `g`
  differentiable with continuous `g'`, `c ≤ g ≤ M` (`c > 0`), `(g')² ∈ L¹(μ)` ⇒
  `Ent_μ(g²) ≤ 2 C ∫ (g')² dμ`.
* `ent_sq_le_of_functionalLSI` (**extension**): the same for every `g > 0` differentiable with
  continuous `g'` and `(g')², g², g² log g² ∈ L¹(μ)`.
* `heatKL_le_of_functionalLSI_of_integrable` (**bridge without class condition**): for `t > 0`,
  `C ≥ 0`, `FunctionalLSI π_t C` and integrable KL and Fisher integrands at `t`:
  `KL(ρ_t‖π_t) ≤ (C/2) I(ρ_t‖π_t)`.
* `heatFlowLSI_of_targetLSI`: `FunctionalLSI π (1/α)` and `HeatFlowRegular ρ π s`,
  `(0, η) ⊆ s` ⇒ `2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` on `(0, η)` (via the convolution
  stability `GaussianFunctionalLSI.functionalLSI_heatKernel_comp_of_targetLSI`).
* The PX-2 corollaries `toReal_klDiv_proxKernel_comp_le_of_targetLSI` (and `_Ioi`) are in
  `Samplers/ProximalHeatFlow.lean`.

## Not proved here

* Test functions that vanish somewhere or are merely absolutely continuous / in `H¹(μ)` (the
  extension requires `g > 0` everywhere, differentiable, with continuous derivative); the
  extension is not packaged as a new LSI predicate.
* `HeatFlowRegular ρ (target f) s` for non-Gaussian `f`, and `FunctionalLSI (target f) (1/α)` for
  non-Gaussian `f` (e.g. Bakry–Émery for strongly convex `f`, Holley–Stroock perturbation): both
  remain hypotheses of the non-Gaussian PX-2 statement; only the Gaussian instance is
  discharged.
* Multi-dimensional versions: `LogSobolevExtensionPi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.LogSobolev

namespace FormalizeSampling.LogSobolevExtension

/-! ### Primitives of continuous weights in `[0, 1]` -/

section Prim

/-- The primitive `a + ∫_a^x w` of a weight `w`, based at `a`. -/
noncomputable def prim (w : ℝ → ℝ) (a x : ℝ) : ℝ := a + ∫ y in a..x, w y

variable {w : ℝ → ℝ} {a : ℝ}

/-- The primitive of a continuous weight has derivative `w`. -/
theorem hasDerivAt_prim (hw : Continuous w) (a x : ℝ) : HasDerivAt (prim w a) (w x) x :=
  ((hw.integral_hasStrictDerivAt a x).hasDerivAt).const_add a

/-- If `w = 1` on `[a, x]` (unordered), then `prim w a x = x`. -/
theorem prim_eq_self {x : ℝ} (h : ∀ y ∈ uIcc a x, w y = 1) : prim w a x = x := by
  rw [prim, intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) h,
    intervalIntegral.integral_const]
  simp

/-- For a weight with `|w| ≤ 1`, `|prim w a x - a| ≤ |x - a|`. -/
theorem abs_prim_sub_le (hw1 : ∀ y, |w y| ≤ 1) (x : ℝ) : |prim w a x - a| ≤ |x - a| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := x) (f := w)
    (C := 1) fun y _ => by simpa [Real.norm_eq_abs] using hw1 y
  simpa [prim, Real.norm_eq_abs] using this

/-- If `w = 0` on `[b, x]` (unordered), then `prim w a x = prim w a b`. -/
theorem prim_eq_of_zero (hw : Continuous w) {b x : ℝ} (h : ∀ y ∈ uIcc b x, w y = 0) :
    prim w a x = prim w a b := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) a b) (hw.intervalIntegrable b x)
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) h] at hadd
  simp only [intervalIntegral.integral_zero, add_zero] at hadd
  rw [prim, prim, hadd]

/-- For a weight with `0 ≤ w ≤ 1` and `a ≤ x`: `a ≤ prim w a x ≤ x`. -/
theorem prim_mem_of_le (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) {x : ℝ}
    (hx : a ≤ x) : a ≤ prim w a x ∧ prim w a x ≤ x := by
  have h0 : 0 ≤ ∫ y in a..x, w y := intervalIntegral.integral_nonneg hx fun y _ => hw0 y
  have h1 : ∫ y in a..x, w y ≤ ∫ y in a..x, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hx (hw.intervalIntegrable a x) intervalIntegrable_const
      fun y _ => hw1 y
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
  exact ⟨by simp only [prim]; linarith, by simp only [prim]; linarith⟩

/-- For a weight with `0 ≤ w ≤ 1` and `x ≤ a`: `x ≤ prim w a x ≤ a`. -/
theorem prim_mem_of_ge (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) {x : ℝ}
    (hx : x ≤ a) : x ≤ prim w a x ∧ prim w a x ≤ a := by
  have h0 : 0 ≤ ∫ y in x..a, w y := intervalIntegral.integral_nonneg hx fun y _ => hw0 y
  have h1 : ∫ y in x..a, w y ≤ ∫ y in x..a, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hx (hw.intervalIntegrable x a) intervalIntegrable_const
      fun y _ => hw1 y
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
  rw [intervalIntegral.integral_symm] at h0 h1
  constructor <;> simp only [prim] <;> linarith

end Prim

/-! ### The spatial and value weights -/

/-- The spatial weight `w_{n,δ}(y) = clamp((n + δ - |y|)/δ, 0, 1)`: equal to `1` on `|y| ≤ n`,
to `0` on `|y| ≥ n + δ`. -/
noncomputable def spaceWeight (n δ y : ℝ) : ℝ := max 0 (min 1 ((n + δ - |y|) / δ))

/-- The value weight `v_N(r) = clamp(min(2 N r - 1, N + 1 - r), 0, 1)`: equal to `1` on
`[1/N, N]`, to `0` on `r ≤ 1/(2N)` and on `r ≥ N + 1`. -/
noncomputable def valueWeight (N r : ℝ) : ℝ := max 0 (min 1 (min (2 * N * r - 1) (N + 1 - r)))

/-- The spatial weight is continuous. -/
theorem continuous_spaceWeight (n δ : ℝ) : Continuous (spaceWeight n δ) := by
  unfold spaceWeight; fun_prop

/-- The value weight is continuous. -/
theorem continuous_valueWeight (N : ℝ) : Continuous (valueWeight N) := by
  unfold valueWeight; fun_prop

/-- The spatial weight is nonnegative. -/
theorem spaceWeight_nonneg (n δ y : ℝ) : 0 ≤ spaceWeight n δ y := le_max_left _ _

/-- The spatial weight is at most `1`. -/
theorem spaceWeight_le_one (n δ y : ℝ) : spaceWeight n δ y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The value weight is nonnegative. -/
theorem valueWeight_nonneg (N r : ℝ) : 0 ≤ valueWeight N r := le_max_left _ _

/-- The value weight is at most `1`. -/
theorem valueWeight_le_one (N r : ℝ) : valueWeight N r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The spatial weight equals `1` on `|y| ≤ n` (`δ > 0`). -/
theorem spaceWeight_eq_one {n δ y : ℝ} (hδ : 0 < δ) (hy : |y| ≤ n) : spaceWeight n δ y = 1 := by
  have : 1 ≤ (n + δ - |y|) / δ := by rw [le_div_iff₀ hδ]; linarith
  simp [spaceWeight, min_eq_left this]

/-- The spatial weight vanishes on `|y| ≥ n + δ` (`δ > 0`). -/
theorem spaceWeight_eq_zero {n δ y : ℝ} (hδ : 0 < δ) (hy : n + δ ≤ |y|) :
    spaceWeight n δ y = 0 := by
  have : (n + δ - |y|) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp only [spaceWeight]
  exact max_eq_left ((min_le_right _ _).trans this)

/-- The value weight equals `1` on `[1/N, N]` (`N > 0`). -/
theorem valueWeight_eq_one {N r : ℝ} (hN : 0 < N) (h1 : 1 / N ≤ r) (h2 : r ≤ N) :
    valueWeight N r = 1 := by
  have h3 : 1 ≤ 2 * N * r - 1 := by
    rw [div_le_iff₀ hN] at h1; nlinarith
  simp only [valueWeight]
  rw [min_eq_left (le_min h3 (by linarith)), max_eq_right zero_le_one]

/-- The value weight vanishes on `r ≤ 1/(2N)` (`N > 0`). -/
theorem valueWeight_eq_zero_of_le {N r : ℝ} (hN : 0 < N) (h : r ≤ 1 / (2 * N)) :
    valueWeight N r = 0 := by
  have : 2 * N * r - 1 ≤ 0 := by
    rw [le_div_iff₀ (by positivity)] at h; linarith
  simp only [valueWeight]
  exact max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans this))

/-- The value weight vanishes on `r ≥ N + 1`. -/
theorem valueWeight_eq_zero_of_ge {N r : ℝ} (h : N + 1 ≤ r) : valueWeight N r = 0 := by
  simp only [valueWeight]
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (by linarith)))

/-- Points of `[0, x]` (unordered) have absolute value at most `|x|`. -/
theorem abs_le_of_mem_uIcc_zero {x y : ℝ} (hy : y ∈ uIcc 0 x) : |y| ≤ |x| := by
  rcases mem_uIcc.1 hy with h | h
  · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
  · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith [h.1]

/-! ### Convergence of the entropy under domination -/

/-- **Dominated convergence for the entropy.** If `F n → f` pointwise, the `F n` are
a.e.-strongly measurable, and `|F n| ≤ B`, `|F n log F n| ≤ B'` with `B, B'` integrable, then
`Ent_μ(F n) → Ent_μ(f)`. -/
theorem tendsto_ent {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    {f : α → ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) μ) {B B' : α → ℝ} (hB : Integrable B μ)
    (hB' : Integrable B' μ) (h1 : ∀ n x, |F n x| ≤ B x)
    (h2 : ∀ n x, |F n x * Real.log (F n x)| ≤ B' x)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ent μ (F n)) atTop (𝓝 (ent μ f)) := by
  have hI : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence B hF hB (fun n => ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using h1 n x) (ae_of_all _ hlim)
  have hL : Tendsto (fun n => ∫ x, F n x * Real.log (F n x) ∂μ) atTop
      (𝓝 (∫ x, f x * Real.log (f x) ∂μ)) :=
    tendsto_integral_of_dominated_convergence B'
      (fun n => Real.continuous_mul_log.comp_aestronglyMeasurable (hF n)) hB'
      (fun n => ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h2 n x)
      (ae_of_all _ fun x => (Real.continuous_mul_log.tendsto _).comp (hlim x))
  exact hL.sub ((Real.continuous_mul_log.tendsto _).comp hI)

/-! ### Step 1: bounded `C¹` test functions with square-integrable derivative -/

variable {μ : Measure ℝ}

/-- **Spatial cut-off approximation.** Let `g` be differentiable with continuous derivative,
`c ≤ g ≤ M` (`c > 0`), and `(g')²` integrable under the finite measure `μ`. For every `n` and
`ε > 0` there is `h ∈ LSIClass` with `h = g` on `[-n, n]`, `c ≤ h ≤ M`, and
`∫ (h')² dμ ≤ ∫ (g')² dμ + ε`. (`h = g ∘ χ` with `χ` a primitive of a spatial weight equal to
`1` on `[-n, n]` and `0` off `[-n-δ, n+δ]`; the transition layer has small `μ`-mass.) -/
theorem exists_lsiClass_approx [IsFiniteMeasure μ] {g : ℝ → ℝ} (hd : Differentiable ℝ g)
    (hcont : Continuous (deriv g)) {c M : ℝ} (hc : 0 < c) (hcg : ∀ x, c ≤ g x)
    (hgM : ∀ x, g x ≤ M) (hi : Integrable (fun x => deriv g x ^ 2) μ) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, LSIClass h ∧ (∀ x : ℝ, |x| ≤ n → h x = g x) ∧ (∀ x, c ≤ h x ∧ h x ≤ M) ∧
      ∫ x, deriv h x ^ 2 ∂μ ≤ ∫ x, deriv g x ^ 2 ∂μ + ε := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -((n : ℝ) + 1)) (b := n + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)],
    by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩)
  set A : ℕ → Set ℝ := fun k => {x | (n : ℝ) < |x| ∧ |x| < n + 1 / ((k : ℝ) + 1)} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hanti : Antitone A := by
    intro i j hij x hx
    refine ⟨hx.1, hx.2.trans_le ?_⟩
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    gcongr
  have hinter : (⋂ k, A k) = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (hcon 0).1)
    have := (hcon k).2
    linarith
  have htend := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hAm k).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at htend
  have hη : 0 < ε / (K ^ 2 + 1) := by positivity
  obtain ⟨k, hk⟩ := ((tendsto_order.1 htend).2 _ (ENNReal.ofReal_pos.2 hη)).exists
  have hAk : μ.real (A k) ≤ ε / (K ^ 2 + 1) :=
    ENNReal.toReal_le_of_le_ofReal hη.le hk.le
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  set w := spaceWeight n δ with hw
  have hwc : Continuous w := continuous_spaceWeight _ _
  set χ := prim w 0 with hχ
  have hχd : ∀ x, HasDerivAt χ (w x) x := hasDerivAt_prim hwc 0
  have hχabs : ∀ x, |χ x| ≤ |x| := fun x => by
    simpa using abs_prim_sub_le (a := 0) (fun y => by
      rw [abs_of_nonneg (spaceWeight_nonneg _ _ _)]; exact spaceWeight_le_one _ _ _) x
  have hχeq : ∀ x : ℝ, |x| ≤ n → χ x = x := fun x hx =>
    prim_eq_self fun y hy => spaceWeight_eq_one hδ0 ((abs_le_of_mem_uIcc_zero hy).trans hx)
  set h : ℝ → ℝ := fun x => g (χ x) with hh
  have hhd : ∀ x, HasDerivAt h (deriv g (χ x) * w x) x := fun x =>
    (hd (χ x)).hasDerivAt.comp x (hχd x)
  have hderiv : ∀ x, deriv h x = deriv g (χ x) * w x := fun x => (hhd x).deriv
  have hbd : ∀ x, |deriv h x| ≤ K := by
    intro x
    rw [hderiv]
    by_cases hx : (n : ℝ) + δ ≤ |x|
    · rw [hw, spaceWeight_eq_zero hδ0 hx, mul_zero, abs_zero]; exact hK0
    · push Not at hx
      have hmem : χ x ∈ Icc (-((n : ℝ) + 1)) (n + 1) :=
        abs_le.1 ((hχabs x).trans (by linarith))
      have := hK _ hmem
      rw [Real.norm_eq_abs] at this
      rw [abs_mul, abs_of_nonneg (spaceWeight_nonneg _ _ _)]
      calc |deriv g (χ x)| * w x ≤ K * 1 :=
            mul_le_mul this (spaceWeight_le_one _ _ _) (spaceWeight_nonneg _ _ _) hK0
        _ = K := mul_one K
  have hpt : ∀ x, deriv h x ^ 2 ≤ deriv g x ^ 2 + (A k).indicator (fun _ => K ^ 2) x := by
    intro x
    by_cases hx1 : |x| ≤ n
    · rw [hderiv, hw, spaceWeight_eq_one hδ0 hx1, mul_one, hχeq x hx1]
      have : 0 ≤ (A k).indicator (fun _ => K ^ 2) x :=
        indicator_nonneg (fun _ _ => sq_nonneg K) x
      linarith
    · push Not at hx1
      by_cases hx2 : |x| < n + δ
      · rw [indicator_of_mem (show x ∈ A k from ⟨hx1, hx2⟩)]
        have : deriv h x ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
        nlinarith [sq_nonneg (deriv g x)]
      · push Not at hx2
        rw [hderiv, hw, spaceWeight_eq_zero hδ0 hx2, mul_zero]
        have : 0 ≤ (A k).indicator (fun _ => K ^ 2) x :=
          indicator_nonneg (fun _ _ => sq_nonneg K) x
        nlinarith [sq_nonneg (deriv g x)]
  have hcls : LSIClass h :=
    { differentiable := fun x => (hhd x).differentiableAt
      bounded := ⟨M, fun x => abs_le.2 ⟨by linarith [hcg (χ x), hgM (χ x)], hgM _⟩⟩
      bounded_deriv := ⟨K, hbd⟩
      pos := ⟨c, hc, fun x => hcg _⟩ }
  refine ⟨h, hcls, fun x hx => by simp only [hh, hχeq x hx], fun x => ⟨hcg _, hgM _⟩, ?_⟩
  have hint_ind : Integrable ((A k).indicator fun _ => K ^ 2) μ :=
    (integrable_const _).indicator (hAm k)
  have hhi : Integrable (fun x => deriv h x ^ 2) μ :=
    integrable_of_abs_le ((measurable_deriv h).pow_const 2).aestronglyMeasurable (K ^ 2)
      fun x => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
  calc ∫ x, deriv h x ^ 2 ∂μ ≤ ∫ x, (deriv g x ^ 2 + (A k).indicator (fun _ => K ^ 2) x) ∂μ :=
        integral_mono hhi (hi.add hint_ind) hpt
    _ = ∫ x, deriv g x ^ 2 ∂μ + μ.real (A k) * K ^ 2 := by
        rw [integral_add hi hint_ind, integral_indicator_const _ (hAm k), smul_eq_mul]
    _ ≤ ∫ x, deriv g x ^ 2 ∂μ + ε := by
        have h1 : μ.real (A k) * K ^ 2 ≤ ε / (K ^ 2 + 1) * K ^ 2 :=
          mul_le_mul_of_nonneg_right hAk (sq_nonneg K)
        have h2 : ε / (K ^ 2 + 1) * K ^ 2 ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
        linarith

/-- **Extension to bounded `C¹` test functions with square-integrable derivative.** Let `μ` be a
probability measure on `ℝ` with `FunctionalLSI μ C`, `C ≥ 0`, and let `g` be differentiable with
continuous derivative, `c ≤ g ≤ M` for some `c > 0`, and `(g')²` integrable under `μ` (`g'` may
be unbounded). Then `Ent_μ(g²) ≤ 2 C ∫ (g')² dμ`. -/
theorem ent_sq_le_of_bounded [IsProbabilityMeasure μ] {C : ℝ} (hLSI : FunctionalLSI μ C)
    (hC : 0 ≤ C) {g : ℝ → ℝ} (hd : Differentiable ℝ g) (hcont : Continuous (deriv g))
    {c M : ℝ} (hc : 0 < c) (hcg : ∀ x, c ≤ g x) (hgM : ∀ x, g x ≤ M)
    (hi : Integrable (fun x => deriv g x ^ 2) μ) :
    ent μ (fun x => g x ^ 2) ≤ 2 * C * ∫ x, deriv g x ^ 2 ∂μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (2 * C + 1) := by positivity
  choose h hcls heq hbd hint using
    fun n : ℕ => exists_lsiClass_approx hd hcont hc hcg hgM hi n hε'
  have hlim : Tendsto (fun n => ent μ (fun x => h n x ^ 2)) atTop
      (𝓝 (ent μ fun x => g x ^ 2)) := by
    refine tendsto_ent (B := fun _ => M ^ 2) (B' := fun _ => (M ^ 2) ^ 2 + 1)
      (fun n => ((hcls n).differentiable.continuous.pow 2).aestronglyMeasurable)
      (integrable_const _) (integrable_const _) (fun n x => ?_) (fun n x => ?_) (fun x => ?_)
    · have h0 : 0 ≤ h n x := hc.le.trans (hbd n x).1
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h0 (hbd n x).2 2
    · have h0 : 0 ≤ h n x := hc.le.trans (hbd n x).1
      have h1 : h n x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ h0 (hbd n x).2 2
      refine (abs_mul_log_le (sq_nonneg _)).trans ?_
      gcongr
    · obtain ⟨N, hN⟩ := exists_nat_ge |x|
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      simp only [heq n x (hN.trans (by exact_mod_cast hn))]
  have hle : ∀ n, ent μ (fun x => h n x ^ 2) ≤ 2 * C * ∫ x, deriv g x ^ 2 ∂μ + ε := by
    intro n
    have h1 := hLSI (h n) (hcls n)
    have h2 := mul_le_mul_of_nonneg_left (hint n) (by positivity : 0 ≤ 2 * C)
    have h3 : 2 * C * (ε / (2 * C + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  exact le_of_tendsto' hlim hle

/-! ### Step 2: the value cut-off -/

section ValueCut

variable {N : ℝ}

/-- The value cut-off `φ_N = prim (valueWeight N) 1`: `φ_N(s) = s` for `s ∈ [1/N, N]`. -/
theorem valueCut_eq (hN : 1 ≤ N) {s : ℝ} (h1 : 1 / N ≤ s) (h2 : s ≤ N) :
    prim (valueWeight N) 1 s = s := by
  have hN0 : 0 < N := by linarith
  have h1N : 1 / N ≤ 1 := by rw [div_le_one hN0]; exact hN
  refine prim_eq_self fun y hy => ?_
  have hy' := uIcc_subset_Icc (a₁ := 1) (b₁ := s) (a₂ := 1 / N) (b₂ := N) ⟨h1N, hN⟩ ⟨h1, h2⟩ hy
  exact valueWeight_eq_one hN0 hy'.1 hy'.2

/-- Bounds on the value cut-off: `1/(2N) ≤ φ_N(s) ≤ N + 1` for all `s` (`N ≥ 1`). -/
theorem valueCut_mem (hN : 1 ≤ N) (s : ℝ) :
    1 / (2 * N) ≤ prim (valueWeight N) 1 s ∧ prim (valueWeight N) 1 s ≤ N + 1 := by
  have hN0 : 0 < N := by linarith
  have hc := continuous_valueWeight N
  have h0 := valueWeight_nonneg N
  have h1 := valueWeight_le_one N
  have hlow : (1 : ℝ) / (2 * N) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  constructor
  · rcases le_or_gt 1 s with hs | hs
    · exact hlow.trans (prim_mem_of_le hc h0 h1 hs).1
    rcases le_or_gt (1 / (2 * N)) s with hs' | hs'
    · exact hs'.trans (prim_mem_of_ge hc h0 h1 hs.le).1
    · rw [prim_eq_of_zero hc (b := 1 / (2 * N)) fun y hy => valueWeight_eq_zero_of_le hN0
        (by rcases mem_uIcc.1 hy with h | h <;> linarith [h.1, h.2])]
      exact (prim_mem_of_ge hc h0 h1 hlow).1
  · rcases le_or_gt s 1 with hs | hs
    · linarith [(prim_mem_of_ge hc h0 h1 hs).2]
    rcases le_or_gt s (N + 1) with hs' | hs'
    · exact (prim_mem_of_le hc h0 h1 hs.le).2.trans hs'
    · rw [prim_eq_of_zero hc (b := N + 1) fun y hy => valueWeight_eq_zero_of_ge
        (by rcases mem_uIcc.1 hy with h | h <;> linarith [h.1, h.2])]
      exact (prim_mem_of_le hc h0 h1 (by linarith)).2

/-- Domination by the original function: for `s > 0` and `N ≥ 1`, with `φ = φ_N`,
`φ(s)² ≤ s² + 1` and `|φ(s)² log φ(s)²| ≤ |s² log s²| + 1`. -/
theorem valueCut_dom (hN : 1 ≤ N) {s : ℝ} (hs : 0 < s) :
    prim (valueWeight N) 1 s ^ 2 ≤ s ^ 2 + 1 ∧
      |prim (valueWeight N) 1 s ^ 2 * Real.log (prim (valueWeight N) 1 s ^ 2)|
        ≤ |s ^ 2 * Real.log (s ^ 2)| + 1 := by
  have hN0 : 0 < N := by linarith
  have hc := continuous_valueWeight N
  have h0 := valueWeight_nonneg N
  have h1 := valueWeight_le_one N
  set φ := prim (valueWeight N) 1 s with hφ
  have hφ0 : 0 < φ := lt_of_lt_of_le (by positivity) (valueCut_mem hN s).1
  rcases le_or_gt 1 s with h1s | h1s
  · obtain ⟨ha, hb⟩ := prim_mem_of_le hc h0 h1 h1s
    have hsq : φ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hφ0.le hb 2
    have hone : 1 ≤ φ ^ 2 := one_le_pow₀ ha
    refine ⟨by linarith, ?_⟩
    have hl0 : 0 ≤ Real.log (φ ^ 2) := Real.log_nonneg hone
    have hl : Real.log (φ ^ 2) ≤ Real.log (s ^ 2) := Real.log_le_log (by positivity) hsq
    rw [abs_of_nonneg (mul_nonneg (by positivity) hl0),
      abs_of_nonneg (mul_nonneg (by positivity) (hl0.trans hl))]
    nlinarith [mul_le_mul hsq hl hl0 (by positivity)]
  · obtain ⟨_, hb⟩ := prim_mem_of_ge hc h0 h1 h1s.le
    have hsq : φ ^ 2 ≤ 1 := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    have := Real.abs_log_mul_self_lt (φ ^ 2) (by positivity) hsq
    rw [mul_comm] at this
    linarith [abs_nonneg (s ^ 2 * Real.log (s ^ 2))]

end ValueCut

/-! ### Step 3: positive `C¹` test functions with finite energy and entropy -/

/-- **Functional LSI for unbounded test functions.** Let `μ` be a probability measure on `ℝ`
with `FunctionalLSI μ C`, `C ≥ 0`, and let `g : ℝ → ℝ` be positive, differentiable with
continuous derivative, with `(g')²`, `g²` and `g² log g²` integrable under `μ` (no
boundedness of `g` or `g'`, no lower bound on `g` beyond positivity). Then
`Ent_μ(g²) ≤ 2 C ∫ (g')² dμ`. (Route: `g_N = φ_N ∘ g` with the value cut-off `φ_N`, so
`1/(2N) ≤ g_N ≤ N + 1` and `|g_N'| ≤ |g'|`; `ent_sq_le_of_bounded` applies to `g_N`, and
`Ent_μ(g_N²) → Ent_μ(g²)` by dominated convergence, dominated by `g² + 1` and
`|g² log g²| + 1`.) -/
theorem ent_sq_le_of_functionalLSI [IsProbabilityMeasure μ] {C : ℝ} (hLSI : FunctionalLSI μ C)
    (hC : 0 ≤ C) {g : ℝ → ℝ} (hpos : ∀ x, 0 < g x) (hd : Differentiable ℝ g)
    (hcont : Continuous (deriv g)) (hi : Integrable (fun x => deriv g x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hgl : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ) :
    ent μ (fun x => g x ^ 2) ≤ 2 * C * ∫ x, deriv g x ^ 2 ∂μ := by
  set G : ℕ → ℝ → ℝ := fun n x => prim (valueWeight ((n : ℝ) + 1)) 1 (g x) with hG
  have hN : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hGd : ∀ n x, HasDerivAt (G n) (valueWeight ((n : ℝ) + 1) (g x) * deriv g x) x :=
    fun n x => (hasDerivAt_prim (continuous_valueWeight _) 1 (g x)).comp x (hd x).hasDerivAt
  have hGderiv : ∀ n, deriv (G n) = fun x => valueWeight ((n : ℝ) + 1) (g x) * deriv g x :=
    fun n => funext fun x => (hGd n x).deriv
  have hsq : ∀ n x, deriv (G n) x ^ 2 ≤ deriv g x ^ 2 := by
    intro n x
    rw [hGderiv, mul_pow]
    have h0 := valueWeight_nonneg ((n : ℝ) + 1) (g x)
    have h1 := valueWeight_le_one ((n : ℝ) + 1) (g x)
    have : valueWeight ((n : ℝ) + 1) (g x) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (deriv g x)]
  have hGi : ∀ n, Integrable (fun x => deriv (G n) x ^ 2) μ := fun n =>
    hi.mono' ((measurable_deriv (G n)).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq n x)
  have hent : ∀ n, ent μ (fun x => G n x ^ 2) ≤ 2 * C * ∫ x, deriv g x ^ 2 ∂μ := by
    intro n
    have hb := fun x => valueCut_mem (hN n) (g x)
    have h1 := ent_sq_le_of_bounded hLSI hC (g := G n) (fun x => (hGd n x).differentiableAt)
      (by rw [hGderiv]; exact ((continuous_valueWeight _).comp hd.continuous).mul hcont)
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

/-! ### The KL/Fisher bridge without the class condition -/

section Bridge

open InformationTheory FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction
open FormalizeSampling.GaussianLSI
open scoped FormalizeSampling.OU

/-- Integrals against `π_t = heatKernel t ∘ₘ π` (`t > 0`, `π` a probability measure) are
Lebesgue integrals against its density: `∫ h dπ_t = ∫ q_t(y) h(y) dy`, `q_t = heatFlowDensity π t`
(no integrability needed: both sides are Bochner integrals, `0` when undefined). -/
theorem integral_heatKernel_comp (π : Measure ℝ) [IsProbabilityMeasure π] {t : ℝ} (ht : 0 < t)
    (h : ℝ → ℝ) :
    ∫ y, h y ∂(OU.heatKernel t.toNNReal ∘ₘ π) = ∫ y, heatFlowDensity π t y * h y := by
  rw [heatKernel_comp_eq_withDensity π ht, integral_withDensity_eq_integral_toReal_smul
    (continuous_heatFlowDensity π ht).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (heatFlowDensity_pos π ht y).le, smul_eq_mul]

/-- Integrability against `π_t = heatKernel t ∘ₘ π` (`t > 0`) is Lebesgue integrability of
`q_t · F`, `q_t = heatFlowDensity π t`. -/
theorem integrable_heatKernel_comp_iff (π : Measure ℝ) [IsProbabilityMeasure π] {t : ℝ}
    (ht : 0 < t) (F : ℝ → ℝ) :
    Integrable F (OU.heatKernel t.toNNReal ∘ₘ π) ↔
      Integrable (fun y => heatFlowDensity π t y * F y) := by
  rw [heatKernel_comp_eq_withDensity π ht, integrable_withDensity_iff_integrable_smul'
    (continuous_heatFlowDensity π ht).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (heatFlowDensity_pos π ht y).le]

/-- **From the functional LSI to the KL/Fisher LSI at a positive time, without the class
condition.** Let `ρ, π` be probability measures on `ℝ`, `t > 0`, `C ≥ 0`, and suppose
`π_t = heatKernel t ∘ₘ π` satisfies `FunctionalLSI π_t C`. If the KL integrand
`p_t log(p_t/q_t)` and the relative Fisher integrand `p_t (∂ log(p_t/q_t))²` are Lebesgue
integrable (the fields `integrable_kl`, `integrable_fisher` of `HeatFlowRegular`), then
`KL(ρ_t‖π_t) ≤ (C/2) I(ρ_t‖π_t)`. (Applies `ent_sq_le_of_functionalLSI` to
`g = √(p_t/q_t)`, which is positive and `C¹` but in general unbounded, not bounded away from
`0`, and with unbounded derivative.) -/
theorem heatKL_le_of_functionalLSI_of_integrable (ρ π : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hLSI : FunctionalLSI (OU.heatKernel t.toNNReal ∘ₘ π) C)
    (hkl : Integrable (klIntegrand (heatFlowDensity ρ) (heatFlowDensity π) t))
    (hfi : Integrable (fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t)) :
    heatKL ρ π t ≤ C / 2 * heatFisher ρ π t := by
  set p := heatFlowDensity ρ t with hpdef
  set q := heatFlowDensity π t with hqdef
  have hp : ∀ y, 0 < p y := heatFlowDensity_pos ρ ht
  have hq : ∀ y, 0 < q y := heatFlowDensity_pos π ht
  set g : ℝ → ℝ := fun y => Real.sqrt (p y / q y) with hg
  have hg0 : ∀ y, 0 < g y := fun y => Real.sqrt_pos.2 (div_pos (hp y) (hq y))
  have hg2 : ∀ y, g y ^ 2 = p y / q y := fun y => Real.sq_sqrt (div_pos (hp y) (hq y)).le
  have hgD : ∀ y, HasDerivAt g
      (((heatFlowD1 ρ t y * q y - p y * heatFlowD1 π t y) / q y ^ 2) / (2 * g y)) y := fun y =>
    ((hasDerivAt_heatFlowDensity_x ρ ht y).div (hasDerivAt_heatFlowDensity_x π ht y)
      (hq y).ne').sqrt (div_pos (hp y) (hq y)).ne'
  have hgd : ∀ y, deriv g y =
      ((heatFlowD1 ρ t y * q y - p y * heatFlowD1 π t y) / q y ^ 2) / (2 * g y) := fun y =>
    (hgD y).deriv
  have hpc : Continuous p := continuous_heatFlowDensity ρ ht
  have hqc : Continuous q := continuous_heatFlowDensity π ht
  have hgc : Continuous g :=
    Real.continuous_sqrt.comp (hpc.div hqc fun y => (hq y).ne')
  have hdc : Continuous (deriv g) := by
    rw [funext hgd]
    refine Continuous.div ?_ (continuous_const.mul hgc) fun y => by
      have := hg0 y; positivity
    exact (((continuous_heatFlowD1 ρ ht).mul hqc).sub
      (hpc.mul (continuous_heatFlowD1 π ht))).div (hqc.pow 2) fun y => by
        have := hq y; positivity
  have hfish : ∀ y, q y * deriv g y ^ 2 = fisherIntegrand (heatFlowDensity ρ)
      (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t y / 4 := by
    intro y
    rw [hgd, fisherIntegrand, relScore, div_pow, mul_pow, hg2]
    simp only [← hpdef, ← hqdef]
    have := hp y
    have := hq y
    field_simp
    ring
  have hkl' : ∀ y, q y * (g y ^ 2 * Real.log (g y ^ 2)) =
      klIntegrand (heatFlowDensity ρ) (heatFlowDensity π) t y := by
    intro y
    have := hq y
    rw [hg2, klIntegrand]
    simp only [← hpdef, ← hqdef]
    field_simp
  have hp' : ∀ y, q y * g y ^ 2 = p y := fun y => by
    have := hq y
    rw [hg2]; field_simp
  have hi : Integrable (fun y => deriv g y ^ 2) (OU.heatKernel t.toNNReal ∘ₘ π) := by
    rw [integrable_heatKernel_comp_iff π ht]
    simp only [← hqdef, hfish]
    exact hfi.div_const 4
  have hi2 : Integrable (fun y => g y ^ 2) (OU.heatKernel t.toNNReal ∘ₘ π) := by
    rw [integrable_heatKernel_comp_iff π ht]
    simp only [← hqdef, hp']
    exact integrable_heatFlowDensity ρ ht
  have hil : Integrable (fun y => g y ^ 2 * Real.log (g y ^ 2))
      (OU.heatKernel t.toNNReal ∘ₘ π) := by
    rw [integrable_heatKernel_comp_iff π ht]
    simp only [← hqdef, hkl']
    exact hkl
  have hent : ent (OU.heatKernel t.toNNReal ∘ₘ π) (fun y => g y ^ 2) = heatKL ρ π t := by
    unfold ent
    rw [integral_heatKernel_comp π ht, integral_heatKernel_comp π ht, heatKL_eq_integral ht hkl]
    have h1 : ∫ y, q y * g y ^ 2 = 1 := by
      simp only [hp']
      have := integral_heatKernel_comp ρ ht (fun _ => 1)
      simpa using this.symm
    rw [h1, Real.log_one, mul_zero, sub_zero]
    exact integral_congr_ae (ae_of_all _ hkl')
  have hfi' : ∫ y, deriv g y ^ 2 ∂(OU.heatKernel t.toNNReal ∘ₘ π) = heatFisher ρ π t / 4 := by
    rw [integral_heatKernel_comp π ht, heatFisher, ← integral_div]
    exact integral_congr_ae (ae_of_all _ hfish)
  have := ent_sq_le_of_functionalLSI hLSI hC hg0 (fun y => (hgD y).differentiableAt) hdc hi
    hi2 hil
  rw [hent, hfi'] at this
  linarith

open FormalizeSampling.GaussianFunctionalLSI in
/-- **The LSI hypothesis of `heatKL_le_div_of_regular` from a functional LSI of `π`, without the
class condition.** For probability measures `ρ, π` on `ℝ`, `α > 0`, `FunctionalLSI π (1/α)` and
`HeatFlowRegular ρ π s` with `(0, η) ⊆ s`:
`2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` for every `t ∈ (0, η)`. -/
theorem heatFlowLSI_of_targetLSI (ρ π : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {α η : ℝ} (hα : 0 < α) (hπ : FunctionalLSI π (1 / α)) {s : Set ℝ}
    (hreg : HeatFlowRegular ρ π s) (hs : Ioo 0 η ⊆ s) :
    ∀ t ∈ Ioo 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * heatFisher ρ π t := by
  intro t ht
  have hL := functionalLSI_heatKernel_comp_of_targetLSI π ht.1.le hπ
  have hC : 0 ≤ 1 / α + t := by have := ht.1; positivity
  have h := heatKL_le_of_functionalLSI_of_integrable ρ π ht.1 hC hL
    (hreg.integrable_kl t (hs ht)) (hreg.integrable_fisher t (hs ht))
  have h2 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * α)
  have : 2 * α * ((1 / α + t) / 2 * heatFisher ρ π t) = (1 + α * t) * heatFisher ρ π t := by
    field_simp
  linarith

end Bridge

end FormalizeSampling.LogSobolevExtension
