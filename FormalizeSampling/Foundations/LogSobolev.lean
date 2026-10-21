module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Functional log-Sobolev inequalities: tensorization and convolution (1D)

Status: **Verified** (no named hypothesis beyond the log-Sobolev inequalities that are the
inputs of each statement).

Setting: probability measures on `ℝ` (and products on `ℝ × ℝ`). The entropy of a function
`h` under `μ` is `Ent_μ(h) = ∫ h log h dμ - (∫ h dμ) log (∫ h dμ)` (`ent`). The test-function
class `LSIClass` consists of differentiable `g : ℝ → ℝ` that are bounded, have bounded
derivative `deriv g`, and are bounded below by a positive constant. `FunctionalLSI μ C` is
the functional log-Sobolev inequality `Ent_μ(g²) ≤ 2 C ∫ (g')² dμ` for every `g` in that class
(`C` is the LSI *constant*, i.e. `C = 1/α` for an `α`-LSI; a Gaussian `N(0, t)` has `C = t`).

## Main results

* `ent_prod_eq` (chain rule for entropy, any measurable spaces, s-finite measures):
  `Ent_{μ⊗ν}(F) = ∫ Ent_μ(F(·, y)) dν(y) + Ent_ν(y ↦ ∫ F(x, y) dμ(x))`, given integrability of
  `F`, `F log F` and of `H log H` for the marginal `H`.
* `sq_integral_mul_le_of_pos`: Cauchy–Schwarz `(∫ a b)² ≤ (∫ a²)(∫ b²)` when `∫ a² > 0`.
* `ent_prod_le_of_functionalLSI` (**tensorization**): if `FunctionalLSI μ C₁`,
  `FunctionalLSI ν C₂` (`C₂ ≥ 0`) and `G : ℝ × ℝ → ℝ` has partial derivatives `D₁, D₂`
  everywhere, with `c ≤ G ≤ M`, `|D₁|, |D₂| ≤ M` (`c > 0`) and `G, D₁, D₂` measurable, then
  `Ent_{μ⊗ν}(G²) ≤ 2 ∫ (C₁ D₁² + C₂ D₂²) d(μ⊗ν)`. The second-marginal term is handled by
  applying `FunctionalLSI ν` to `y ↦ √(∫ G(x, y)² dμ(x))`, differentiating under the integral
  and using Cauchy–Schwarz.
* `ent_map`: `Ent_{φ#μ}(h) = Ent_μ(h ∘ φ)` for measurable `φ, h`.
* `functionalLSI_map_add` (**convolution**): `FunctionalLSI μ C₁`, `FunctionalLSI ν C₂`,
  `C₂ ≥ 0` imply `FunctionalLSI (μ ∗ ν) (C₁ + C₂)`, where `μ ∗ ν` is written as the push-forward
  of `μ ⊗ ν` under `(x, z) ↦ x + z`.
* `functionalLSI_dirac`, `lsiClass_const`: non-vacuity of the predicates.

## Not proved here

* The functional LSI of a Gaussian, `FunctionalLSI (gaussianReal 0 t) t` (Gross's
  inequality), is proved in `GaussianFunctionalLSI`.
* The general Lipschitz push-forward principle (LSI of `μ` on `ℝ²` with a weighted gradient
  ⇒ LSI of `φ#μ`); only the sum map `(x, z) ↦ x + z` is treated, directly.
* Extension of the inequality to wider test-function classes (unbounded `g`, `g` vanishing
  somewhere) by truncation / approximation; the class `LSIClass` is the same in the hypotheses
  and in the conclusions, so the results are self-consistent but stated for this class only.
* Multi-dimensional versions: `LogSobolevPi`, `LogSobolevTensorPi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace FormalizeSampling.LogSobolev

/-- The entropy of `h` under `μ`: `Ent_μ(h) = ∫ h log h dμ - (∫ h dμ) log (∫ h dμ)` (Lean's
`Real.log`, so `0 log 0 = 0`; intended for nonnegative `h`). -/
noncomputable def ent {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ) : ℝ :=
  ∫ x, h x * Real.log (h x) ∂μ - (∫ x, h x ∂μ) * Real.log (∫ x, h x ∂μ)

/-- For `x ≥ 0`, `|x log x| ≤ x² + 1` (from `1 - 1/x ≤ log x ≤ x - 1`). -/
theorem abs_mul_log_le {x : ℝ} (hx : 0 ≤ x) : |x * Real.log x| ≤ x ^ 2 + 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [abs_le]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hx
    have h2 : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left this hx.le
    rw [mul_sub, mul_inv_cancel₀ hx.ne', mul_one] at h2
    nlinarith
  · have := Real.log_le_sub_one_of_pos hx
    have h2 : x * Real.log x ≤ x * (x - 1) := mul_le_mul_of_nonneg_left this hx.le
    nlinarith

/-- A measurable function bounded in absolute value by a constant is integrable against a
finite measure. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (K : ℝ) (h : ∀ x, |f x| ≤ K) :
    Integrable f μ :=
  Integrable.of_bound hf K (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h x)

/-- **Chain rule for entropy.** For s-finite `μ` on `α`, `ν` on `β` and `F : α × β → ℝ` with
`F`, `F log F` integrable under `μ ⊗ ν` and `H log H` integrable under `ν`, where
`H y = ∫ F(x, y) dμ(x)`:
`Ent_{μ⊗ν}(F) = ∫ Ent_μ(F(·, y)) dν(y) + Ent_ν(H)`. -/
theorem ent_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [SFinite ν] {F : α × β → ℝ}
    (hF : Integrable F (μ.prod ν)) (hFl : Integrable (fun p => F p * Real.log (F p)) (μ.prod ν))
    (hH : Integrable (fun y => (∫ x, F (x, y) ∂μ) * Real.log (∫ x, F (x, y) ∂μ)) ν) :
    ent (μ.prod ν) F =
      ∫ y, ent μ (fun x => F (x, y)) ∂ν + ent ν (fun y => ∫ x, F (x, y) ∂μ) := by
  unfold ent
  rw [integral_prod_symm _ hFl, integral_prod_symm _ hF,
    integral_sub hFl.integral_prod_right hH]
  ring

/-- **Cauchy–Schwarz for integrals.** If `a², b², a b` are integrable and `∫ a² dμ > 0`, then
`(∫ a b dμ)² ≤ (∫ a² dμ)(∫ b² dμ)`. -/
theorem sq_integral_mul_le_of_pos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : Integrable (fun x => a x ^ 2) μ) (hb : Integrable (fun x => b x ^ 2) μ)
    (hab : Integrable (fun x => a x * b x) μ) (hA : 0 < ∫ x, a x ^ 2 ∂μ) :
    (∫ x, a x * b x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 ∂μ) * ∫ x, b x ^ 2 ∂μ := by
  set A := ∫ x, a x ^ 2 ∂μ
  set B := ∫ x, b x ^ 2 ∂μ
  set X := ∫ x, a x * b x ∂μ
  set l := X / A
  have h0 : 0 ≤ ∫ x, (l * a x - b x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hexp : ∫ x, (l * a x - b x) ^ 2 ∂μ = l ^ 2 * A - 2 * l * X + B := by
    have : (fun x => (l * a x - b x) ^ 2) =
        fun x => (l ^ 2 * a x ^ 2 - 2 * l * (a x * b x)) + b x ^ 2 := by
      funext x; ring
    have h1 : Integrable (fun x => l ^ 2 * a x ^ 2 - 2 * l * (a x * b x)) μ :=
      (ha.const_mul _).sub (hab.const_mul _)
    rw [this, integral_add h1 hb, integral_sub (ha.const_mul _) (hab.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hexp] at h0
  have : l ^ 2 * A - 2 * l * X = -(X ^ 2 / A) := by
    simp only [l]; field_simp; ring
  rw [this] at h0
  have h1 : X ^ 2 / A ≤ B := by linarith
  rwa [div_le_iff₀ hA, mul_comm] at h1


/-- The test-function class of the functional log-Sobolev inequality: `g : ℝ → ℝ` is
differentiable, bounded, has bounded derivative, and is bounded below by a positive
constant. -/
structure LSIClass (g : ℝ → ℝ) : Prop where
  /-- `g` is differentiable everywhere. -/
  differentiable : Differentiable ℝ g
  /-- `g` is bounded. -/
  bounded : ∃ M, ∀ x, |g x| ≤ M
  /-- The derivative of `g` is bounded. -/
  bounded_deriv : ∃ M, ∀ x, |deriv g x| ≤ M
  /-- `g` is bounded below by a positive constant. -/
  pos : ∃ c, 0 < c ∧ ∀ x, c ≤ g x

/-- **Functional log-Sobolev inequality** with constant `C` for a measure `μ` on `ℝ`:
`Ent_μ(g²) ≤ 2 C ∫ (g')² dμ` for every `g` in `LSIClass`. For the target `π ∝ e^{-f}` of an
`α`-LSI, `C = 1/α`; for `N(0, t)`, `C = t`. -/
def FunctionalLSI (μ : Measure ℝ) (C : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, LSIClass g → ent μ (fun x => g x ^ 2) ≤ 2 * C * ∫ x, deriv g x ^ 2 ∂μ

/-- A pointwise lower bound `a ≤ f` gives `a ≤ ∫ f dμ` for a probability measure `μ`. -/
theorem le_integral_of_le_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {a : ℝ} (h : ∀ x, a ≤ f x) :
    a ≤ ∫ x, f x ∂μ := by
  simpa using integral_mono (integrable_const a) hf h

/-- A pointwise upper bound `f ≤ a` gives `∫ f dμ ≤ a` for a probability measure `μ`. -/
theorem integral_le_of_le_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {a : ℝ} (h : ∀ x, f x ≤ a) :
    ∫ x, f x ∂μ ≤ a := by
  simpa using integral_mono hf (integrable_const a) h

/-- **Tensorization of the functional LSI.** Let `μ, ν` be probability measures on `ℝ` with
`FunctionalLSI μ C₁` and `FunctionalLSI ν C₂`, `C₂ ≥ 0`. Let `G : ℝ × ℝ → ℝ` have partial
derivative `D₁(x, y)` in `x` and `D₂(x, y)` in `y` everywhere, with `G, D₁, D₂` measurable,
`c ≤ G ≤ M` for some `c > 0`, and `|D₁|, |D₂| ≤ M`. Then
`Ent_{μ⊗ν}(G²) ≤ 2 ∫ (C₁ D₁² + C₂ D₂²) d(μ ⊗ ν)`. -/
theorem ent_prod_le_of_functionalLSI {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C₁ C₂ : ℝ} (hμ : FunctionalLSI μ C₁) (hν : FunctionalLSI ν C₂)
    (hC₂ : 0 ≤ C₂) {G D₁ D₂ : ℝ × ℝ → ℝ} (hGm : Measurable G) (hD₁m : Measurable D₁)
    (hD₂m : Measurable D₂)
    (hD₁ : ∀ x y, HasDerivAt (fun x => G (x, y)) (D₁ (x, y)) x)
    (hD₂ : ∀ x y, HasDerivAt (fun y => G (x, y)) (D₂ (x, y)) y)
    {M c : ℝ} (hc : 0 < c) (hcG : ∀ p, c ≤ G p) (hGM : ∀ p, G p ≤ M)
    (hD₁M : ∀ p, |D₁ p| ≤ M) (hD₂M : ∀ p, |D₂ p| ≤ M) :
    ent (μ.prod ν) (fun p => G p ^ 2) ≤
      2 * ∫ p, (C₁ * D₁ p ^ 2 + C₂ * D₂ p ^ 2) ∂(μ.prod ν) := by
  have hM : 0 ≤ M := (hc.le.trans (hcG (0, 0))).trans (hGM (0, 0))
  have hGabs : ∀ p, |G p| ≤ M := fun p => abs_le.2 ⟨by linarith [hcG p, hGM p], hGM p⟩
  set F : ℝ × ℝ → ℝ := fun p => G p ^ 2 with hFdef
  have hFm : Measurable F := hGm.pow_const 2
  have hF0 : ∀ p, 0 ≤ F p := fun p => sq_nonneg _
  have hFM : ∀ p, F p ≤ M ^ 2 := fun p => pow_le_pow_left₀ (hc.le.trans (hcG p)) (hGM p) 2
  have hFb : ∀ p, |F p| ≤ M ^ 2 := fun p => by rw [abs_of_nonneg (hF0 p)]; exact hFM p
  have hFc : ∀ p, c ^ 2 ≤ F p := fun p => pow_le_pow_left₀ hc.le (hcG p) 2
  have hF : Integrable F (μ.prod ν) := integrable_of_abs_le hFm.aestronglyMeasurable _ hFb
  have hFl : Integrable (fun p => F p * Real.log (F p)) (μ.prod ν) :=
    integrable_of_abs_le (hFm.mul hFm.log).aestronglyMeasurable ((M ^ 2) ^ 2 + 1) fun p =>
      (abs_mul_log_le (hF0 p)).trans (by have := hF0 p; have := hFM p; gcongr)
  have hFx : ∀ y, Integrable (fun x => F (x, y)) μ := fun y =>
    integrable_of_abs_le (hFm.comp measurable_prodMk_right).aestronglyMeasurable _
      fun x => hFb (x, y)
  set H : ℝ → ℝ := fun y => ∫ x, F (x, y) ∂μ with hHdef
  have hHi : Integrable H ν := hF.integral_prod_right
  have hHc : ∀ y, c ^ 2 ≤ H y := fun y => le_integral_of_le_prob (hFx y) fun x => hFc _
  have hHM : ∀ y, H y ≤ M ^ 2 := fun y => integral_le_of_le_prob (hFx y) fun x => hFM _
  have hH0 : ∀ y, 0 ≤ H y := fun y => (sq_nonneg c).trans (hHc y)
  have hHl : Integrable (fun y => H y * Real.log (H y)) ν :=
    integrable_of_abs_le (Real.continuous_mul_log.comp_aestronglyMeasurable
      hHi.aestronglyMeasurable) ((M ^ 2) ^ 2 + 1) fun y =>
      (abs_mul_log_le (hH0 y)).trans (by have := hH0 y; have := hHM y; gcongr)
  rw [ent_prod_eq μ ν hF hFl hHl]
  -- integrability of the squared derivatives
  have hD₁sq : Integrable (fun p => D₁ p ^ 2) (μ.prod ν) :=
    integrable_of_abs_le (hD₁m.pow_const 2).aestronglyMeasurable (M ^ 2) fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_sq' (abs_le.1 (hD₁M p)).1 (abs_le.1 (hD₁M p)).2
  have hD₂sq : Integrable (fun p => D₂ p ^ 2) (μ.prod ν) :=
    integrable_of_abs_le (hD₂m.pow_const 2).aestronglyMeasurable (M ^ 2) fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_sq' (abs_le.1 (hD₂M p)).1 (abs_le.1 (hD₂M p)).2
  -- Step 2: the conditional entropies
  have hstep2 : ∫ y, ent μ (fun x => F (x, y)) ∂ν ≤ 2 * C₁ * ∫ p, D₁ p ^ 2 ∂(μ.prod ν) := by
    have hpt : ∀ y, ent μ (fun x => F (x, y)) ≤ 2 * C₁ * ∫ x, D₁ (x, y) ^ 2 ∂μ := by
      intro y
      have hcl : LSIClass (fun x => G (x, y)) :=
        ⟨fun x => (hD₁ x y).differentiableAt, ⟨M, fun x => hGabs _⟩,
          ⟨M, fun x => by rw [(hD₁ x y).deriv]; exact hD₁M _⟩, ⟨c, hc, fun x => hcG _⟩⟩
      have h := hμ _ hcl
      have hd : deriv (fun x => G (x, y)) = fun x => D₁ (x, y) :=
        funext fun x => (hD₁ x y).deriv
      rw [hd] at h
      exact h
    rw [integral_prod_symm _ hD₁sq, ← integral_const_mul]
    exact integral_mono (hFl.integral_prod_right.sub hHl)
      (hD₁sq.integral_prod_right.const_mul _) hpt
  -- Step 3: the entropy of the marginal
  set H' : ℝ → ℝ := fun y => ∫ x, 2 * (G (x, y) * D₂ (x, y)) ∂μ with hH'def
  have hHd : ∀ y, HasDerivAt H (H' y) y := by
    intro y
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun y x => F (x, y)) (F' := fun y x => 2 * (G (x, y) * D₂ (x, y))) (x₀ := y)
      (bound := fun _ => 2 * (M * M)) univ_mem
      (Eventually.of_forall fun y' => (hFx y').aestronglyMeasurable) (hFx y)
      ((measurable_const.mul ((hGm.mul hD₂m).comp measurable_prodMk_right)).aestronglyMeasurable)
      (ae_of_all _ fun x y' _ => ?_) (integrable_const _) (ae_of_all _ fun x y' _ => ?_)).2
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
      gcongr
      exacts [hGabs _, hD₂M _]
    · have := (hD₂ x y').pow 2
      convert this using 1
      push_cast; ring
  set S : ℝ → ℝ := fun y => Real.sqrt (H y) with hSdef
  have hSpos : ∀ y, 0 < S y := fun y =>
    Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos hc 2) (hHc y))
  have hSd : ∀ y, HasDerivAt S (H' y / (2 * S y)) y := fun y =>
    (hHd y).sqrt (lt_of_lt_of_le (pow_pos hc 2) (hHc y)).ne'
  have hD₂x : ∀ y, Integrable (fun x => D₂ (x, y) ^ 2) μ := fun y =>
    integrable_of_abs_le ((hD₂m.comp measurable_prodMk_right).pow_const 2).aestronglyMeasurable
      (M ^ 2) fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (abs_le.1 (hD₂M _)).1 (abs_le.1 (hD₂M _)).2
  have hCS : ∀ y, (H' y / (2 * S y)) ^ 2 ≤ ∫ x, D₂ (x, y) ^ 2 ∂μ := by
    intro y
    have hGD : Integrable (fun x => G (x, y) * D₂ (x, y)) μ :=
      integrable_of_abs_le ((hGm.mul hD₂m).comp measurable_prodMk_right).aestronglyMeasurable
        (M * M) fun x => by rw [abs_mul]; gcongr; exacts [hGabs _, hD₂M _]
    have hcs := sq_integral_mul_le_of_pos (μ := μ) (a := fun x => G (x, y))
      (b := fun x => D₂ (x, y)) (hFx y) (hD₂x y) hGD
      (lt_of_lt_of_le (pow_pos hc 2) (hHc y))
    have hH'y : H' y = 2 * ∫ x, G (x, y) * D₂ (x, y) ∂μ := integral_const_mul _ _
    have hS2 : S y ^ 2 = H y := Real.sq_sqrt (hH0 y)
    have hHy : 0 < H y := lt_of_lt_of_le (pow_pos hc 2) (hHc y)
    rw [hH'y, div_pow, mul_pow, mul_pow, hS2]
    rw [div_le_iff₀ (by positivity)]
    have : (∫ x, G (x, y) * D₂ (x, y) ∂μ) ^ 2 ≤ H y * ∫ x, D₂ (x, y) ^ 2 ∂μ := hcs
    nlinarith
  have hdS : deriv S = fun y => H' y / (2 * S y) := funext fun y => (hSd y).deriv
  have hdSM : ∀ y, deriv S y ^ 2 ≤ M ^ 2 := fun y => by
    rw [hdS]
    exact (hCS y).trans (integral_le_of_le_prob (hD₂x y) fun x =>
      sq_le_sq' (abs_le.1 (hD₂M _)).1 (abs_le.1 (hD₂M _)).2)
  have hSclass : LSIClass S :=
    ⟨fun y => (hSd y).differentiableAt,
      ⟨Real.sqrt (M ^ 2), fun y => by
        rw [abs_of_pos (hSpos y)]; exact Real.sqrt_le_sqrt (hHM y)⟩,
      ⟨Real.sqrt (M ^ 2), fun y => Real.abs_le_sqrt (hdSM y)⟩,
      ⟨c, hc, fun y => (Real.le_sqrt hc.le (hH0 y)).2 (hHc y)⟩⟩
  have hstep3 := hν S hSclass
  have hSH : (fun y => S y ^ 2) = H := funext fun y => Real.sq_sqrt (hH0 y)
  rw [hSH] at hstep3
  have hstep3' : ∫ y, deriv S y ^ 2 ∂ν ≤ ∫ p, D₂ p ^ 2 ∂(μ.prod ν) := by
    rw [integral_prod_symm _ hD₂sq]
    refine integral_mono (integrable_of_abs_le
      ((measurable_deriv S).pow_const 2).aestronglyMeasurable (M ^ 2) fun y => ?_)
      hD₂sq.integral_prod_right fun y => ?_
    · rw [abs_of_nonneg (sq_nonneg _)]; exact hdSM y
    · rw [hdS]; exact hCS y
  have hsum : ∫ p, (C₁ * D₁ p ^ 2 + C₂ * D₂ p ^ 2) ∂(μ.prod ν) =
      C₁ * ∫ p, D₁ p ^ 2 ∂(μ.prod ν) + C₂ * ∫ p, D₂ p ^ 2 ∂(μ.prod ν) := by
    rw [integral_add (hD₁sq.const_mul _) (hD₂sq.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hsum]
  have := mul_le_mul_of_nonneg_left hstep3' (by linarith : (0 : ℝ) ≤ 2 * C₂)
  linarith


/-- Entropy under a push-forward: for measurable `φ` and `h`, `Ent_{φ#μ}(h) = Ent_μ(h ∘ φ)`. -/
theorem ent_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    {φ : α → β} (hφ : Measurable φ) {h : β → ℝ} (hh : Measurable h) :
    ent (μ.map φ) h = ent μ (fun x => h (φ x)) := by
  unfold ent
  have hm : Measurable fun y => h y * Real.log (h y) := hh.mul hh.log
  rw [integral_map hφ.aemeasurable hm.aestronglyMeasurable,
    integral_map hφ.aemeasurable hh.aestronglyMeasurable]

/-- **LSI of a convolution.** For probability measures `μ, ν` on `ℝ` with `FunctionalLSI μ C₁`
and `FunctionalLSI ν C₂`, `C₂ ≥ 0`, the convolution `μ ∗ ν`, written as the push-forward of
`μ ⊗ ν` by `(x, z) ↦ x + z`, satisfies `FunctionalLSI (μ ∗ ν) (C₁ + C₂)`. -/
theorem functionalLSI_map_add {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C₁ C₂ : ℝ} (hμ : FunctionalLSI μ C₁) (hν : FunctionalLSI ν C₂)
    (hC₂ : 0 ≤ C₂) :
    FunctionalLSI ((μ.prod ν).map (fun p : ℝ × ℝ => p.1 + p.2)) (C₁ + C₂) := by
  intro g hg
  obtain ⟨M₀, hM₀⟩ := hg.bounded
  obtain ⟨M₁, hM₁⟩ := hg.bounded_deriv
  obtain ⟨c, hc, hcg⟩ := hg.pos
  have hgm : Measurable g := hg.differentiable.continuous.measurable
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hdm : Measurable (fun p : ℝ × ℝ => deriv g (p.1 + p.2)) := (measurable_deriv g).comp hadd
  have hD : ∀ p : ℝ × ℝ, |deriv g (p.1 + p.2)| ≤ max M₀ M₁ := fun p =>
    (hM₁ _).trans (le_max_right _ _)
  have h := ent_prod_le_of_functionalLSI hμ hν hC₂ (G := fun p => g (p.1 + p.2))
    (hgm.comp hadd) hdm hdm
    (fun x y => (hg.differentiable (x + y)).hasDerivAt.comp_add_const x y)
    (fun x y => (hg.differentiable (x + y)).hasDerivAt.comp_const_add x y)
    hc (fun p => hcg _) (fun p => (le_abs_self _).trans ((hM₀ _).trans (le_max_left _ _))) hD hD
  rw [ent_map _ hadd (hgm.pow_const 2),
    integral_map hadd.aemeasurable ((measurable_deriv g).pow_const 2).aestronglyMeasurable]
  have hsum : ∫ p, (C₁ * deriv g (p.1 + p.2) ^ 2 + C₂ * deriv g (p.1 + p.2) ^ 2) ∂(μ.prod ν) =
      (C₁ + C₂) * ∫ p, deriv g (p.1 + p.2) ^ 2 ∂(μ.prod ν) := by
    rw [← integral_const_mul]; congr 1; funext p; ring
  rw [hsum] at h
  linarith

/-- Non-vacuity: a Dirac mass satisfies `FunctionalLSI` with every constant `C ≥ 0`
(its entropy functional vanishes). -/
theorem functionalLSI_dirac (a : ℝ) {C : ℝ} (hC : 0 ≤ C) : FunctionalLSI (Measure.dirac a) C := by
  intro g _
  have h0 : ent (Measure.dirac a) (fun x => g x ^ 2) = 0 := by
    simp [ent]
  rw [h0]
  have : 0 ≤ ∫ x, deriv g x ^ 2 ∂(Measure.dirac a) := integral_nonneg fun x => sq_nonneg _
  positivity

/-- Non-vacuity: a positive constant function is in `LSIClass`. -/
theorem lsiClass_const {a : ℝ} (ha : 0 < a) : LSIClass (fun _ => a) :=
  ⟨differentiable_const a, ⟨|a|, fun _ => le_rfl⟩, ⟨0, fun _ => by simp⟩, ⟨a, ha, fun _ => le_rfl⟩⟩

end FormalizeSampling.LogSobolev
