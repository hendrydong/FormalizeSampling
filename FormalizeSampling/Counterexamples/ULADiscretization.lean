module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# ULA and SGLD discretisation bias for the standard Gaussian target (CE-03, SGLD)

For the target `N(0,1)` (potential `U(x) = x ^ 2 / 2`, so `∇U(x) = x`) one step of the
unadjusted Langevin algorithm (ULA) with step size `h` is
`X' = X - h ∇U(X) + √(2h) Z = (1 - h) X + √(2h) Z` with `Z ~ N(0,1)` independent of `X`.
Stochastic-gradient Langevin dynamics (SGLD) with additive Gaussian gradient noise
`ξ ~ N(0, τ ^ 2)` is modelled as `X' = (1 - h) X + h ξ + √(2h) Z` with `X, ξ, Z` mutually
independent (the sign of `h ξ` is irrelevant for the law because `N(0, τ ^ 2)` is symmetric).

The ULA limit is a known example: Wibisono (2018, arXiv:1802.08089, Example 2) shows that for a
Gaussian target `N(μ, Σ)` ULA converges to `N(μ, Σ (I - (h/2) Σ⁻¹)⁻¹)`, which is `N(0, 2/(2 - h))`
here. The SGLD variance is the fixed point of the same linear recursion with the extra noise.

## Conventions

* `gaussianReal m v` is Mathlib's Gaussian with mean `m` and **variance** `v : ℝ≥0`.
* `ulaStep h μ` and `sgldStep h τ μ` are the laws of `X'` when `X ~ μ`; they are written as
  convolutions of image measures. `law_ulaUpdate` and `law_sgldUpdate` check that these
  definitions are exactly the laws of the random-variable updates on a probability space.
* All statements are *one-time marginal law* identities (equalities of measures on `ℝ`).

## Registry IDs

* `CE-03` (ULA has a finite-step bias): `ulaStep_gaussianReal`, `ulaStep_standardGaussian`,
  `ulaStep_standardGaussian_ne`, `law_ulaUpdate`, `law_ulaUpdate_standard`,
  `law_ulaUpdate_ne_standard`, `var_eq_of_gaussianReal_eq` (helper).
* `CE-03` (biased invariant law): `ulaStep_biasedGaussian`, `ulaStep_gaussianReal_eq_self_iff`
  (the `τ = 0` cases of the SGLD statements, via `sgldStep_zero`), `one_lt_two_div_two_sub`,
  `two_div_two_sub_ne_one`, `biasedGaussian_ne_standard`, `ulaStep_iterate_gaussianReal`,
  `ulaStep_iterate_var_tendsto`.
* `SGLD` (gradient noise inflates the invariant variance): `sgldStep_gaussianReal`,
  `sgld_invariantVar_nonneg`, `sgldStep_stationaryGaussian`,
  `sgldStep_gaussianReal_eq_self_iff`, `sgld_invariantVar_strictMono`,
  `sgld_invariantVar_lt_of_sq_lt`, `ula_invariantVar_lt_sgld_invariantVar`, `law_sgldUpdate`.

## Not proved here

* Only the Gaussian target `N(0,1)` and centred Gaussian initial laws are treated; nothing is
  said about ULA/SGLD for other targets or other initial laws.
* Convergence of the ULA iterates is proved only at the level of the variance parameter
  (`ulaStep_iterate_var_tendsto`); weak/TV/`W₂` convergence of the laws is not formalised,
  and neither are SGLD iterates.
* No bound on the bias in TV, `W₂` or KL is proved beyond the exact variance formulas.
* The SGLD noise model is the idealised additive Gaussian one, independent of the state;
  minibatch gradient noise is not modelled.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.Counterexamples.ULADiscretization

open FormalizeSampling.MeasureHelpers (aemeasurable_of_map_eq_gaussianReal
  map_const_mul_of_aemeasurable)

/-- Coercion of an anonymous-constructor nonnegative real (a `Subtype.mk`) back to `ℝ`. -/
@[simp] private lemma coe_anonMk (a : ℝ) (ha : 0 ≤ a) : NNReal.toReal ⟨a, ha⟩ = a := rfl

/-- Law of one ULA step for the target `N(0,1)` with step size `h`: if `X ~ μ` and
`Z ~ N(0,1)` are independent, then `X' = (1 - h) X + √(2h) Z` has law `ulaStep h μ`
(see `law_ulaUpdate`). -/
noncomputable def ulaStep (h : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (μ.map (fun x => (1 - h) * x)) ∗ ((gaussianReal 0 1).map (fun z => Real.sqrt (2 * h) * z))

/-- Law of one SGLD step for the target `N(0,1)` with step size `h` and Gaussian gradient
noise of variance `τ ^ 2`: if `X ~ μ`, `ξ ~ N(0, τ ^ 2)` and `Z ~ N(0,1)` are mutually
independent, then `X' = (1 - h) X + h ξ + √(2h) Z` has law `sgldStep h τ μ`
(see `law_sgldUpdate`). -/
noncomputable def sgldStep (h τ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ((μ.map (fun x => (1 - h) * x)) ∗
      ((gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩).map (fun e => h * e))) ∗
    ((gaussianReal 0 1).map (fun z => Real.sqrt (2 * h) * z))

/-- Parameter injectivity of `gaussianReal` in the variance: equal Gaussian laws have equal
variance parameters (via `variance_id_gaussianReal`). -/
theorem var_eq_of_gaussianReal_eq {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0}
    (h : gaussianReal m₁ v₁ = gaussianReal m₂ v₂) : v₁ = v₂ := by
  have h1 := variance_id_gaussianReal (μ := m₁) (v := v₁)
  rw [h, variance_id_gaussianReal] at h1
  exact_mod_cast h1.symm

/-- **SGLD step on a centred Gaussian.** For `h ≥ 0`, any `τ` and any variance `v`,
`sgldStep h τ (N(0, v)) = N(0, (1 - h) ^ 2 v + h ^ 2 τ ^ 2 + 2h)`. -/
theorem sgldStep_gaussianReal {h : ℝ} (hh : 0 ≤ h) (τ : ℝ) (v : ℝ≥0) :
    sgldStep h τ (gaussianReal 0 v) =
      gaussianReal 0 ⟨(1 - h) ^ 2 * v + h ^ 2 * τ ^ 2 + 2 * h, by positivity⟩ := by
  rw [sgldStep, gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  erw [gaussianReal_map_const_mul]
  rw [gaussianReal_conv_gaussianReal, gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext
    simp only [mul_one, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, coe_anonMk]
    rw [Real.sq_sqrt (by positivity)]
    rfl

/-- Nonnegativity of the SGLD invariant variance `(2 + h τ ^ 2) / (2 - h)` for `0 ≤ h < 2`. -/
theorem sgld_invariantVar_nonneg {h : ℝ} (hh : 0 ≤ h) (hh2 : h < 2) (τ : ℝ) :
    0 ≤ (2 + h * τ ^ 2) / (2 - h) :=
  div_nonneg (by positivity) (sub_nonneg.2 hh2.le)

/-- **SGLD invariant law.** For `0 ≤ h < 2` and gradient-noise variance `τ ^ 2`, the centred
Gaussian `N(0, (2 + h τ ^ 2) / (2 - h))` is exactly invariant for the SGLD step. -/
theorem sgldStep_stationaryGaussian {h : ℝ} (hh : 0 ≤ h) (hh2 : h < 2) (τ : ℝ) :
    sgldStep h τ (gaussianReal 0 ⟨(2 + h * τ ^ 2) / (2 - h), sgld_invariantVar_nonneg hh hh2 τ⟩) =
      gaussianReal 0 ⟨(2 + h * τ ^ 2) / (2 - h), sgld_invariantVar_nonneg hh hh2 τ⟩ := by
  refine (sgldStep_gaussianReal hh _ _).trans ?_
  congr 1
  ext
  simp only [coe_anonMk]
  have : (2 - h) ≠ 0 := by linarith
  field_simp
  ring

/-- **Uniqueness among centred Gaussians for SGLD.** For `0 < h < 2`, any `τ` and any
variance `v`, `N(0, v)` is invariant for the SGLD step if and only if
`v = (2 + h τ ^ 2) / (2 - h)`. -/
theorem sgldStep_gaussianReal_eq_self_iff {h : ℝ} (hh : 0 < h) (hh2 : h < 2) (τ : ℝ)
    (v : ℝ≥0) :
    sgldStep h τ (gaussianReal 0 v) = gaussianReal 0 v ↔ (v : ℝ) = (2 + h * τ ^ 2) / (2 - h) := by
  have h2 : (2 - h) ≠ 0 := by linarith
  rw [sgldStep_gaussianReal hh.le]
  constructor
  · intro heq
    have hv := congrArg (fun w : ℝ≥0 => (w : ℝ)) (var_eq_of_gaussianReal_eq heq)
    simp only [coe_anonMk] at hv
    rw [eq_div_iff h2]
    refine mul_left_cancel₀ hh.ne' ?_
    linear_combination (-1 : ℝ) * hv
  · intro hv
    congr 1
    ext
    simp only [coe_anonMk]
    rw [hv]
    field_simp
    ring

/-- **ULA is SGLD without gradient noise.** For any s-finite `μ`, `sgldStep h 0 μ = ulaStep h μ`
(the noise `N(0, 0)` is the Dirac mass at `0`). -/
theorem sgldStep_zero (h : ℝ) (μ : Measure ℝ) [SFinite μ] : sgldStep h 0 μ = ulaStep h μ := by
  have h0 : gaussianReal 0 ⟨(0 : ℝ) ^ 2, sq_nonneg 0⟩ = Measure.dirac 0 := by
    rw [← gaussianReal_zero_var]; congr 1; ext; simp
  rw [sgldStep, ulaStep, h0, Measure.map_dirac' (measurable_const_mul h), mul_zero,
    Measure.conv_dirac_zero]

/-- **ULA step on a centred Gaussian.** For `h ≥ 0` and any variance `v`,
`ulaStep h (N(0, v)) = N(0, (1 - h) ^ 2 v + 2h)` (`sgldStep_gaussianReal` at `τ = 0`). -/
theorem ulaStep_gaussianReal {h : ℝ} (hh : 0 ≤ h) (v : ℝ≥0) :
    ulaStep h (gaussianReal 0 v) =
      gaussianReal 0 ⟨(1 - h) ^ 2 * v + 2 * h, by positivity⟩ := by
  rw [← sgldStep_zero, sgldStep_gaussianReal hh]
  congr 2; simp

/-- **CE-03, measure form.** For `h ≥ 0`, if `X ~ N(0,1)` and `Z ~ N(0,1)` are independent,
then `X' = (1 - h) X + √(2h) Z ~ N(0, (1 - h) ^ 2 + 2h) = N(0, 1 + h ^ 2)`:
`((N(0,1)).map ((1 - h) * ·)) ∗ ((N(0,1)).map (√(2h) * ·)) = N(0, 1 + h ^ 2)`. -/
theorem ulaStep_standardGaussian {h : ℝ} (hh : 0 ≤ h) :
    ((gaussianReal 0 1).map (fun x => (1 - h) * x)) ∗
        ((gaussianReal 0 1).map (fun z => Real.sqrt (2 * h) * z)) =
      gaussianReal 0 ⟨1 + h ^ 2, by positivity⟩ := by
  have := ulaStep_gaussianReal hh 1
  rw [ulaStep] at this
  rw [this]
  congr 1
  ext
  simp only [coe_anonMk, NNReal.coe_one]
  ring

/-- **CE-03, bias.** For `h > 0` one ULA step started at the target `N(0,1)` does not return
`N(0,1)`: the output variance is `1 + h ^ 2 ≠ 1`. ULA does not preserve its target. -/
theorem ulaStep_standardGaussian_ne {h : ℝ} (hh : 0 < h) :
    ((gaussianReal 0 1).map (fun x => (1 - h) * x)) ∗
        ((gaussianReal 0 1).map (fun z => Real.sqrt (2 * h) * z)) ≠ gaussianReal 0 1 := by
  rw [ulaStep_standardGaussian hh.le]
  intro heq
  have hv := congrArg (fun v : ℝ≥0 => (v : ℝ)) (var_eq_of_gaussianReal_eq heq)
  simp only [coe_anonMk, NNReal.coe_one, add_eq_left] at hv
  exact (pow_ne_zero 2 hh.ne') hv

/-- **Random-variable form of the ULA step.** On a probability space, if `X` and `Z` are
independent, `X` is a.e.-measurable and `Z ~ N(0,1)`, then the law of
`X' = (1 - h) X + √(2h) Z` is `ulaStep h (Law X)`. -/
theorem law_ulaUpdate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hXm : AEMeasurable X P) (hXZ : IndepFun X Z P)
    (hZ : P.map Z = gaussianReal 0 1) (h : ℝ) :
    P.map (fun ω => (1 - h) * X ω + Real.sqrt (2 * h) * Z ω) = ulaStep h (P.map X) := by
  have hZm : AEMeasurable Z P := aemeasurable_of_map_eq_gaussianReal one_ne_zero hZ
  have hA : AEMeasurable (fun ω => (1 - h) * X ω) P :=
    (measurable_const_mul _).comp_aemeasurable hXm
  have hC : AEMeasurable (fun ω => Real.sqrt (2 * h) * Z ω) P :=
    (measurable_const_mul _).comp_aemeasurable hZm
  have hind : IndepFun (fun ω => (1 - h) * X ω) (fun ω => Real.sqrt (2 * h) * Z ω) P :=
    hXZ.comp (measurable_const_mul _) (measurable_const_mul _)
  have hsum : P.map (fun ω => (1 - h) * X ω + Real.sqrt (2 * h) * Z ω) =
      P.map (fun ω => (1 - h) * X ω) ∗ P.map (fun ω => Real.sqrt (2 * h) * Z ω) :=
    hind.map_add_eq_map_conv_map₀ hA hC
  rw [hsum, map_const_mul_of_aemeasurable hXm, map_const_mul_of_aemeasurable hZm, hZ, ulaStep]

/-- **CE-03, random-variable form.** On a probability space, let `X ~ N(0,1)` and
`Z ~ N(0,1)` be independent and `h ≥ 0`. Then `X' = (1 - h) X + √(2h) Z ~ N(0, 1 + h ^ 2)`. -/
theorem law_ulaUpdate_standard {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hXZ : IndepFun X Z P)
    (hX : P.map X = gaussianReal 0 1) (hZ : P.map Z = gaussianReal 0 1) {h : ℝ} (hh : 0 ≤ h) :
    P.map (fun ω => (1 - h) * X ω + Real.sqrt (2 * h) * Z ω) =
      gaussianReal 0 ⟨1 + h ^ 2, by positivity⟩ := by
  have hXm : AEMeasurable X P := aemeasurable_of_map_eq_gaussianReal one_ne_zero hX
  rw [law_ulaUpdate hXm hXZ hZ h, hX, ulaStep]
  exact ulaStep_standardGaussian hh

/-- **CE-03, random-variable form of the bias.** On a probability space, let `X ~ N(0,1)` and
`Z ~ N(0,1)` be independent and `h > 0`. Then `X' = (1 - h) X + √(2h) Z` is *not*
`N(0,1)`-distributed. -/
theorem law_ulaUpdate_ne_standard {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hXZ : IndepFun X Z P)
    (hX : P.map X = gaussianReal 0 1) (hZ : P.map Z = gaussianReal 0 1) {h : ℝ} (hh : 0 < h) :
    P.map (fun ω => (1 - h) * X ω + Real.sqrt (2 * h) * Z ω) ≠ gaussianReal 0 1 := by
  have hXm : AEMeasurable X P := aemeasurable_of_map_eq_gaussianReal one_ne_zero hX
  rw [law_ulaUpdate hXm hXZ hZ h, hX, ulaStep]
  exact ulaStep_standardGaussian_ne hh

/-- **CE-03, biased invariant law.** For `0 ≤ h < 2` the centred Gaussian `N(0, 2 / (2 - h))`
is exactly invariant for the ULA step: `ulaStep h (N(0, 2/(2-h))) = N(0, 2/(2-h))`
(`sgldStep_stationaryGaussian` at `τ = 0`). -/
theorem ulaStep_biasedGaussian {h : ℝ} (hh : 0 ≤ h) (hh2 : h < 2) :
    ulaStep h (gaussianReal 0 ⟨2 / (2 - h), div_nonneg zero_le_two (sub_nonneg.2 hh2.le)⟩) =
      gaussianReal 0 ⟨2 / (2 - h), div_nonneg zero_le_two (sub_nonneg.2 hh2.le)⟩ := by
  refine (sgldStep_zero h (gaussianReal 0 _)).symm.trans ?_
  convert sgldStep_stationaryGaussian hh hh2 0 using 3 <;> simp

/-- **Uniqueness among centred Gaussians for ULA.** For `0 < h < 2` and any variance `v`,
`N(0, v)` is invariant for the ULA step if and only if `v = 2 / (2 - h)`
(`sgldStep_gaussianReal_eq_self_iff` at `τ = 0`). -/
theorem ulaStep_gaussianReal_eq_self_iff {h : ℝ} (hh : 0 < h) (hh2 : h < 2) (v : ℝ≥0) :
    ulaStep h (gaussianReal 0 v) = gaussianReal 0 v ↔ (v : ℝ) = 2 / (2 - h) := by
  simpa [sgldStep_zero] using sgldStep_gaussianReal_eq_self_iff hh hh2 0 v

/-- **The ULA invariant variance is biased.** For `0 < h < 2`, `1 < 2 / (2 - h)`. -/
theorem one_lt_two_div_two_sub {h : ℝ} (hh : 0 < h) (hh2 : h < 2) : 1 < 2 / (2 - h) := by
  rw [one_lt_div (by linarith)]
  linarith

/-- **The ULA invariant variance is biased.** For `0 < h < 2`, `2 / (2 - h) ≠ 1`, so the
invariant law `N(0, 2 / (2 - h))` of the ULA step is not the target `N(0,1)`. -/
theorem two_div_two_sub_ne_one {h : ℝ} (hh : 0 < h) (hh2 : h < 2) : 2 / (2 - h) ≠ 1 :=
  (one_lt_two_div_two_sub hh hh2).ne'

/-- **ULA's invariant Gaussian is not the target.** For `0 < h < 2`,
`N(0, 2 / (2 - h)) ≠ N(0, 1)`. -/
theorem biasedGaussian_ne_standard {h : ℝ} (hh : 0 < h) (hh2 : h < 2) :
    gaussianReal 0 ⟨2 / (2 - h), div_nonneg zero_le_two (sub_nonneg.2 hh2.le)⟩ ≠
      gaussianReal 0 1 := by
  intro heq
  have hv := congrArg (fun w : ℝ≥0 => (w : ℝ)) (var_eq_of_gaussianReal_eq heq)
  simp only [coe_anonMk, NNReal.coe_one] at hv
  exact two_div_two_sub_ne_one hh hh2 hv

/-- **ULA iterates from a centred Gaussian, closed form.** For `0 ≤ h < 2`, any initial
variance `v` and any `k : ℕ`, the `k`-th ULA iterate of `N(0, v)` is `N(0, w)` with
`w = 2 / (2 - h) + ((1 - h) ^ 2) ^ k (v - 2 / (2 - h))`. -/
theorem ulaStep_iterate_gaussianReal {h : ℝ} (hh : 0 ≤ h) (hh2 : h < 2) (v : ℝ≥0) (k : ℕ) :
    ∃ w : ℝ≥0, (ulaStep h)^[k] (gaussianReal 0 v) = gaussianReal 0 w ∧
      (w : ℝ) = 2 / (2 - h) + ((1 - h) ^ 2) ^ k * (v - 2 / (2 - h)) := by
  have h2 : (2 - h) ≠ 0 := by linarith
  induction k with
  | zero => exact ⟨v, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, hwv⟩ := ih
    refine ⟨⟨(1 - h) ^ 2 * w + 2 * h, by positivity⟩, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', hw, ulaStep_gaussianReal hh]
    · simp only [coe_anonMk]
      rw [hwv, pow_succ]
      field_simp
      ring

/-- **ULA iterates converge to the biased variance.** For `0 < h < 2` and any initial variance
`v`, the ULA iterates of `N(0, v)` are centred Gaussians `N(0, w k)` whose variances converge
to `2 / (2 - h)`, which differs from the target variance `1` (`two_div_two_sub_ne_one`). -/
theorem ulaStep_iterate_var_tendsto {h : ℝ} (hh : 0 < h) (hh2 : h < 2) (v : ℝ≥0) :
    ∃ w : ℕ → ℝ≥0, (∀ k, (ulaStep h)^[k] (gaussianReal 0 v) = gaussianReal 0 (w k)) ∧
      Filter.Tendsto (fun k => (w k : ℝ)) Filter.atTop (nhds (2 / (2 - h))) := by
  choose w hw hwv using ulaStep_iterate_gaussianReal hh.le hh2 v
  refine ⟨w, hw, ?_⟩
  have hq0 : 0 ≤ (1 - h) ^ 2 := sq_nonneg _
  have hq1 : (1 - h) ^ 2 < 1 := by nlinarith
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
    ((v : ℝ) - 2 / (2 - h))).const_add (2 / (2 - h))
  simp only [zero_mul, add_zero] at hlim
  simp_rw [hwv]
  exact hlim

/-- **SGLD bias grows with the gradient noise.** For `0 < h < 2` the invariant variance
`s ↦ (2 + h s) / (2 - h)` is strictly increasing in the noise variance `s = τ ^ 2`. -/
theorem sgld_invariantVar_strictMono {h : ℝ} (hh : 0 < h) (hh2 : h < 2) :
    StrictMono (fun s : ℝ => (2 + h * s) / (2 - h)) := by
  intro s t hst
  have h2 : 0 < 2 - h := by linarith
  simp only
  rw [div_lt_div_iff_of_pos_right h2]
  nlinarith

/-- **SGLD bias grows with the gradient noise, in terms of `τ`.** For `0 < h < 2` and
`τ₁ ^ 2 < τ₂ ^ 2`, `(2 + h τ₁ ^ 2) / (2 - h) < (2 + h τ₂ ^ 2) / (2 - h)`. -/
theorem sgld_invariantVar_lt_of_sq_lt {h : ℝ} (hh : 0 < h) (hh2 : h < 2) {τ₁ τ₂ : ℝ}
    (hτ : τ₁ ^ 2 < τ₂ ^ 2) :
    (2 + h * τ₁ ^ 2) / (2 - h) < (2 + h * τ₂ ^ 2) / (2 - h) :=
  sgld_invariantVar_strictMono hh hh2 hτ

/-- **SGLD is more biased than ULA.** For `0 < h < 2` and `τ ≠ 0`,
`1 < 2 / (2 - h) < (2 + h τ ^ 2) / (2 - h)`: nonzero gradient noise strictly inflates the
invariant variance beyond the (already biased) ULA value. -/
theorem ula_invariantVar_lt_sgld_invariantVar {h : ℝ} (hh : 0 < h) (hh2 : h < 2) {τ : ℝ}
    (hτ : τ ≠ 0) : 1 < 2 / (2 - h) ∧ 2 / (2 - h) < (2 + h * τ ^ 2) / (2 - h) := by
  refine ⟨one_lt_two_div_two_sub hh hh2, ?_⟩
  have := sgld_invariantVar_lt_of_sq_lt hh hh2 (τ₁ := 0) (τ₂ := τ) (by simp [sq_pos_iff, hτ])
  simpa using this

/-- **Random-variable form of the SGLD step.** On a probability space, let `X`, `ξ`, `Z` be
mutually independent (`iIndepFun ![X, ξ, Z]`), `X` and `ξ` a.e.-measurable, `ξ ~ N(0, τ ^ 2)` and
`Z ~ N(0,1)`. (Measurability of `ξ` is needed for `τ = 0`: an image law `δ₀` does not force it.)
Then `X' = (1 - h) X + h ξ + √(2h) Z` has law `sgldStep h τ (Law X)`. -/
theorem law_sgldUpdate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X ξ Z : Ω → ℝ} (hXm : AEMeasurable X P)
    (hξm : AEMeasurable ξ P) (hind : iIndepFun ![X, ξ, Z] P) {τ : ℝ}
    (hξ : P.map ξ = gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩)
    (hZ : P.map Z = gaussianReal 0 1) (h : ℝ) :
    P.map (fun ω => (1 - h) * X ω + h * ξ ω + Real.sqrt (2 * h) * Z ω) =
      sgldStep h τ (P.map X) := by
  have hZm : AEMeasurable Z P := aemeasurable_of_map_eq_gaussianReal one_ne_zero hZ
  let g : Fin 3 → ℝ → ℝ :=
    ![fun x => (1 - h) * x, fun e => h * e, fun z => Real.sqrt (2 * h) * z]
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    fin_cases i <;> exact measurable_const_mul _
  have hY := hind.comp g hgm
  have hA : AEMeasurable (fun ω => (1 - h) * X ω) P :=
    (measurable_const_mul _).comp_aemeasurable hXm
  have hB : AEMeasurable (fun ω => h * ξ ω) P := (measurable_const_mul _).comp_aemeasurable hξm
  have hC : AEMeasurable (fun ω => Real.sqrt (2 * h) * Z ω) P :=
    (measurable_const_mul _).comp_aemeasurable hZm
  have hYm : ∀ i, AEMeasurable ((fun i => g i ∘ ![X, ξ, Z] i) i) P := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hC
  have h012 : IndepFun (fun ω => (1 - h) * X ω + h * ξ ω)
      (fun ω => Real.sqrt (2 * h) * Z ω) P :=
    hY.indepFun_add_left₀ hYm 0 1 2 (by decide) (by decide)
  have h01 : IndepFun (fun ω => (1 - h) * X ω) (fun ω => h * ξ ω) P :=
    hY.indepFun (i := 0) (j := 1) (by decide)
  have hsum : P.map (fun ω => (1 - h) * X ω + h * ξ ω + Real.sqrt (2 * h) * Z ω) =
      P.map (fun ω => (1 - h) * X ω + h * ξ ω) ∗ P.map (fun ω => Real.sqrt (2 * h) * Z ω) :=
    h012.map_add_eq_map_conv_map₀ (hA.add hB) hC
  have hsum01 : P.map (fun ω => (1 - h) * X ω + h * ξ ω) =
      P.map (fun ω => (1 - h) * X ω) ∗ P.map (fun ω => h * ξ ω) :=
    h01.map_add_eq_map_conv_map₀ hA hB
  rw [hsum, hsum01, map_const_mul_of_aemeasurable hXm, map_const_mul_of_aemeasurable hξm,
    map_const_mul_of_aemeasurable hZm, hξ, hZ, sgldStep]

end FormalizeSampling.Counterexamples.ULADiscretization
