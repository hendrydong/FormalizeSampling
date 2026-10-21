module

public import FormalizeSampling.Flow.IdealVelocityStep
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# DT-1 with integrability from a finite second moment (dimension one)

Status: **Verified** (no named unproved hypothesis).

The descent lemma DT-1 (`DeterministicStep.klDiv_map_step_le`) and its ideal-velocity form
(`IdealVelocityStep.klDiv_map_step_idealVel_le`) assume the integrability of several
integrands explicitly. Under their own standing hypotheses (`|v'| ≤ Lv`, bounded `U''`) the
velocity, `U'` and the step `T = id + η v` grow at most linearly, so all those integrands
grow at most quadratically and are integrable as soon as `ρ = p dx` has a finite second moment.
This file restates both theorems in that form. The `d`-dimensional versions are in
`FormalizeSampling/Flow/DeterministicStepMomentsPi.lean`.

## Main results

* `LinGrowth`, `QuadGrowth`: `‖f x‖ ≤ c (1 + ‖x‖)`, `|f x| ≤ C (1 + ‖x‖²)`, with closure
  lemmas; `LinGrowth.of_norm_fderiv_le` (mean value inequality: `‖Df‖ ≤ L` gives linear
  growth); `QuadGrowth.integrable_mul`: `p f` is integrable if `f` (measurable) has quadratic
  growth, `p ≥ 0` is integrable and `∫ ‖x‖² p < ∞`.
* `integrable_klIntegrand_of_klDiv_ne_top`: **KL bridge**, `KL(p μ ‖ p⋆ μ) < ∞` implies
  `p log(p/p⋆) ∈ L¹(μ)` (any σ-finite `μ`; converse of `klDiv_withDensity_real`).
* `quadGrowth_comp_step_sub`: with the **two-sided** bound `|U''| ≤ M` and `v` of linear
  growth, `U∘T - U` has quadratic growth.
* `klDiv_map_step_le` (DT-1, moment form). Compared with `DeterministicStep.klDiv_map_step_le`:
  - `p log(p/π) ∈ L¹` is **replaced** by `KL(ρ ‖ π) < ∞`;
  - `p (U∘T - U)`, `p U' v`, `p v² ∈ L¹` are **eliminated**;
  - **added**: `∫ x² p < ∞` and `|U''| ≤ M` (the original only has `U'' ≤ L`, which does not
    control `|U'|` from below; `U'' ≤ L` is kept for the constant).
* `klDiv_map_step_idealVel_le` (ideal velocity, moment form). Compared with
  `IdealVelocityStep.klDiv_map_step_idealVel_le`:
  - `p log(p/π) ∈ L¹` is **replaced** by `KL(ρ ‖ π) < ∞`;
  - `p (U∘T - U)`, the Fisher integrand `((log p)' + U')² p`, `v p'` and `v p ∈ L¹` are
    **eliminated** (finite Fisher information is a consequence: `|(log p)''| ≤ L_p` makes the
    score of linear growth);
  - **added**: only `∫ x² p < ∞` (`|U''| ≤ L_U` is already two-sided).

## NOT proved here

* The density-level statements (`integral_pushDensity_klIntegrand_le(_stein)`) are not
  restated; the same growth lemmas apply to them verbatim.
* Finite KL itself is not derived from moment/regularity assumptions (it would need a lower
  bound on `p log p`, e.g. bounded `p`, plus the upper growth of `U`).
-/

@[expose] public section

open MeasureTheory Set Filter InformationTheory
open scoped ENNReal

namespace FormalizeSampling.DeterministicStepMoments

open FormalizeSampling.MeasureHelpers (integrable_of_isProbabilityMeasure)

/-! ### Linear and quadratic growth -/

section Growth

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- `f` has **at most linear growth**: `‖f x‖ ≤ c (1 + ‖x‖)` for some `c ≥ 0`. -/
def LinGrowth (f : E → F) : Prop := ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * (1 + ‖x‖)

/-- `f` has **at most quadratic growth**: `|f x| ≤ C (1 + ‖x‖²)` for some `C`. -/
def QuadGrowth (f : E → ℝ) : Prop := ∃ C : ℝ, ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2)

namespace LinGrowth

/-- The identity has linear growth. -/
theorem id : LinGrowth (fun x : E => x) :=
  ⟨1, zero_le_one, fun x => by linarith⟩

/-- Constants have linear growth. -/
theorem const (a : F) : LinGrowth (fun _ : E => a) :=
  ⟨‖a‖, norm_nonneg _, fun x => by nlinarith [norm_nonneg a, norm_nonneg x]⟩

/-- Sums of functions of linear growth have linear growth. -/
theorem add {f g : E → F} (hf : LinGrowth f) (hg : LinGrowth g) :
    LinGrowth fun x => f x + g x := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  exact ⟨c + c', add_nonneg hc hc', fun x =>
    (norm_add_le _ _).trans (by nlinarith [hf x, hg x])⟩

/-- Negation preserves linear growth. -/
theorem neg {f : E → F} (hf : LinGrowth f) : LinGrowth fun x => -f x := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, hc, fun x => by rw [norm_neg]; exact hf x⟩

/-- Scalar multiples preserve linear growth. -/
theorem const_smul [NormedSpace ℝ F] {f : E → F} (hf : LinGrowth f) (a : ℝ) :
    LinGrowth fun x => a • f x := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨|a| * c, mul_nonneg (abs_nonneg _) hc, fun x => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)

/-- Composition of functions of linear growth has linear growth. -/
theorem comp {G : Type*} [NormedAddCommGroup G] {f : F → G} {g : E → F} (hf : LinGrowth f)
    (hg : LinGrowth g) : LinGrowth fun x => f (g x) := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  refine ⟨c * (1 + c'), mul_nonneg hc (by linarith), fun x => (hf (g x)).trans ?_⟩
  have := hg x
  nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left this hc]

/-- **Linear growth from a bounded derivative** (mean value inequality): if `f` is
differentiable with `‖Df‖ ≤ L`, then `‖f x‖ ≤ ‖f 0‖ + L ‖x‖`. -/
theorem of_norm_fderiv_le [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E → F} {L : ℝ}
    (hf : Differentiable ℝ f) (hf' : ∀ x, ‖fderiv ℝ f x‖ ≤ L) : LinGrowth f := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hf' 0)
  refine ⟨max ‖f 0‖ L, (norm_nonneg _).trans (le_max_left _ _), fun x => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf x)
    (fun x _ => hf' x) (mem_univ 0) (mem_univ x)
  rw [sub_zero] at h
  have h1 := norm_le_insert' (f x) (f 0)
  nlinarith [le_max_left ‖f 0‖ L, le_max_right ‖f 0‖ L, norm_nonneg x, norm_nonneg (f 0)]

end LinGrowth

/-- **Linear growth from a bounded derivative** (scalar version): if `f : ℝ → ℝ` is
differentiable with `|f'| ≤ L`, then `f` has linear growth. -/
theorem linGrowth_of_abs_deriv_le {f : ℝ → ℝ} {L : ℝ} (hf : Differentiable ℝ f)
    (hf' : ∀ x, |deriv f x| ≤ L) : LinGrowth f :=
  LinGrowth.of_norm_fderiv_le hf fun x => by
    rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]; exact hf' x

namespace QuadGrowth

/-- Pointwise domination by a function of quadratic growth. -/
theorem mono {f g : E → ℝ} (hg : QuadGrowth g) (h : ∀ x, |f x| ≤ g x) : QuadGrowth f := by
  obtain ⟨C, hC⟩ := hg
  exact ⟨C, fun x => (h x).trans ((le_abs_self _).trans (hC x))⟩

/-- Sums of functions of quadratic growth have quadratic growth. -/
theorem add {f g : E → ℝ} (hf : QuadGrowth f) (hg : QuadGrowth g) :
    QuadGrowth fun x => f x + g x := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨C', hC'⟩ := hg
  exact ⟨C + C', fun x => (abs_add_le _ _).trans (by nlinarith [hC x, hC' x])⟩

/-- Negation preserves quadratic growth. -/
theorem neg {f : E → ℝ} (hf : QuadGrowth f) : QuadGrowth fun x => -f x := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun x => by rw [abs_neg]; exact hC x⟩

/-- Absolute values preserve quadratic growth. -/
theorem abs {f : E → ℝ} (hf : QuadGrowth f) : QuadGrowth fun x => |f x| := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun x => by rw [abs_abs]; exact hC x⟩

/-- Constant multiples preserve quadratic growth. -/
theorem const_mul {f : E → ℝ} (hf : QuadGrowth f) (a : ℝ) : QuadGrowth fun x => a * f x := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|a| * C, fun x => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

/-- Finite sums of functions of quadratic growth have quadratic growth. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, QuadGrowth (f i)) :
    QuadGrowth fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Scalar inequality behind `QuadGrowth.of_le_mul`: `(1 + t)² ≤ 2 (1 + t²)`. -/
theorem one_add_sq_le (t : ℝ) : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by
  nlinarith [sq_nonneg (1 - t)]

/-- If `|f x| ≤ ‖g x‖ ‖h x‖` with `g`, `h` of linear growth, then `f` has quadratic
growth. -/
theorem of_le_mul {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H] {f : E → ℝ}
    {g : E → G} {h : E → H} (hg : LinGrowth g) (hh : LinGrowth h)
    (hle : ∀ x, |f x| ≤ ‖g x‖ * ‖h x‖) : QuadGrowth f := by
  obtain ⟨c, hc, hg⟩ := hg
  obtain ⟨c', hc', hh⟩ := hh
  refine ⟨2 * (c * c'), fun x => (hle x).trans ?_⟩
  have h1 := mul_le_mul (hg x) (hh x) (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left (one_add_sq_le ‖x‖) (mul_nonneg hc hc')
  nlinarith

/-- Products of real functions of linear growth have quadratic growth. -/
theorem mul {g h : E → ℝ} (hg : LinGrowth g) (hh : LinGrowth h) :
    QuadGrowth fun x => g x * h x :=
  of_le_mul hg hh fun x => by rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]

/-- Squares of real functions of linear growth have quadratic growth. -/
theorem sq {g : E → ℝ} (hg : LinGrowth g) : QuadGrowth fun x => g x ^ 2 := by
  simpa only [pow_two] using mul hg hg

/-- Functions of linear growth have quadratic growth. -/
theorem of_linGrowth {g : E → ℝ} (hg : LinGrowth g) : QuadGrowth g :=
  of_le_mul hg (LinGrowth.const (1 : ℝ)) fun x => by simp

/-- **Integrability from a finite second moment.** If `p ≥ 0` is integrable with
`∫ ‖x‖² p < ∞` and `f` is a.e.-strongly measurable of quadratic growth, then `p f` is
integrable. -/
theorem integrable_mul [MeasurableSpace E] {μ : Measure E} {p f : E → ℝ}
    (hf : QuadGrowth f) (hf_meas : AEStronglyMeasurable f μ) (hp0 : ∀ x, 0 ≤ p x)
    (hp_int : Integrable p μ) (hm : Integrable (fun x => ‖x‖ ^ 2 * p x) μ) :
    Integrable (fun x => p x * f x) μ := by
  obtain ⟨C, hC⟩ := hf
  refine Integrable.mono' ((hp_int.add hm).const_mul C) (hp_int.1.mul hf_meas)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 x)]
  have := mul_le_mul_of_nonneg_left (hC x) (hp0 x)
  simp only [Pi.add_apply]
  nlinarith

end QuadGrowth

end Growth

/-! ### Finite KL gives an integrable KL integrand -/

/-- **KL bridge (converse direction).** Let `μ` be σ-finite, `p ≥ 0` and `p⋆ > 0` measurable.
If Mathlib's `klDiv (p μ) (p⋆ μ)` is finite, then `p log(p/p⋆)` is `μ`-integrable. (The
forward direction is `DeterministicStep.klDiv_withDensity_real`.) -/
theorem integrable_klIntegrand_of_klDiv_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {p pStar : α → ℝ} (hp_meas : Measurable p) (hpStar_meas : Measurable pStar)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hpStar_pos : ∀ x, 0 < pStar x)
    (h : klDiv (μ.withDensity fun x => ENNReal.ofReal (p x))
      (μ.withDensity fun x => ENNReal.ofReal (pStar x)) ≠ ∞) :
    Integrable (fun x => p x * Real.log (p x / pStar x)) μ := by
  set P := μ.withDensity fun x => ENNReal.ofReal (p x) with hP
  set Q := μ.withDensity fun x => ENNReal.ofReal (pStar x) with hQ
  have hfp : Measurable fun x => ENNReal.ofReal (p x) := ENNReal.measurable_ofReal.comp hp_meas
  have hfq : Measurable fun x => ENNReal.ofReal (pStar x) :=
    ENNReal.measurable_ofReal.comp hpStar_meas
  have h1 : P.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (p x) :=
    Measure.rnDeriv_withDensity _ hfp
  have h2 : P.rnDeriv Q =ᵐ[μ] fun x => (ENNReal.ofReal (pStar x))⁻¹ * P.rnDeriv μ x :=
    Measure.rnDeriv_withDensity_right P μ hfq.aemeasurable
      (Eventually.of_forall fun x => by simp [hpStar_pos x])
      (Eventually.of_forall fun x => by simp)
  have hllr : llr P Q =ᵐ[μ] fun x => Real.log (p x / pStar x) := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [llr_def]
    simp only
    rw [hx2, hx1, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hp_nonneg x),
      ENNReal.toReal_ofReal (hpStar_pos x).le, inv_mul_eq_div]
  have hlt : ∀ᵐ x ∂μ, ENNReal.ofReal (p x) < ⊤ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  obtain ⟨-, hint⟩ := klDiv_ne_top_iff.1 h
  rw [hP, integrable_withDensity_iff_integrable_smul' hfp hlt] at hint
  refine hint.congr ?_
  filter_upwards [hllr] with x hx
  rw [hx, ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]

/-! ### Dimension one: DT-1 from a finite second moment -/

section OneDim

open DeterministicStep

variable {η Lv L M Z : ℝ} {v U p : ℝ → ℝ}

/-- In dimension one, `‖x‖² = x²`, so the second moment `∫ x² p` is the `‖x‖²`-moment used by
`QuadGrowth.integrable_mul`. -/
theorem integrable_norm_sq_mul_of_sq {μ : Measure ℝ} (hm : Integrable (fun x => x ^ 2 * p x) μ) :
    Integrable (fun x => ‖x‖ ^ 2 * p x) μ := by
  simpa only [Real.norm_eq_abs, sq_abs] using hm

/-- A velocity of linear growth gives a step `T = id + η v` of linear growth. -/
theorem linGrowth_step (hv : LinGrowth v) : LinGrowth (step η v) := by
  have h := LinGrowth.id.add (hv.const_smul η)
  simp only [smul_eq_mul] at h
  exact h

/-- **Quadratic growth of `U∘T - U`.** If `U`, `U'` are differentiable with the two-sided bound
`|U''| ≤ M` and `v` has linear growth, then `U(T x) - U(x)` has quadratic growth,
`T = id + η v`. (Taylor's bound `le_quadratic_of_deriv2_le` at `x` and at `T x`; an upper
bound `U'' ≤ L` alone does not suffice, since it allows `U'` to grow superlinearly.) -/
theorem quadGrowth_comp_step_sub (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hUM : ∀ z, |deriv (deriv U) z| ≤ M) (hv : LinGrowth v) :
    QuadGrowth fun x => U (step η v x) - U x := by
  have hUM' : ∀ z, deriv (deriv U) z ≤ M := fun z => (le_abs_self _).trans (hUM z)
  have hdU : LinGrowth (deriv U) := linGrowth_of_abs_deriv_le hU' hUM
  have hw : LinGrowth fun x => η * v x := by simpa only [smul_eq_mul] using hv.const_smul η
  have hg : QuadGrowth fun x => |deriv U x * (η * v x)| +
      |deriv U (step η v x) * (η * v x)| + M / 2 * (η * v x) ^ 2 :=
    ((QuadGrowth.mul hdU hw).abs.add
      (QuadGrowth.mul (hdU.comp (linGrowth_step hv)) hw).abs).add ((QuadGrowth.sq hw).const_mul _)
  refine hg.mono fun x => ?_
  have h1 := le_quadratic_of_deriv2_le hU hU' hUM' x (step η v x)
  have h2 := le_quadratic_of_deriv2_le hU hU' hUM' (step η v x) x
  have e1 : step η v x - x = η * v x := by rw [step]; ring
  have e2 : x - step η v x = -(η * v x) := by rw [step]; ring
  rw [e1] at h1
  rw [e2, neg_sq] at h2
  have a1 := neg_abs_le (deriv U x * (η * v x))
  have a2 := le_abs_self (deriv U (step η v x) * (η * v x))
  have a3 := abs_nonneg (deriv U x * (η * v x))
  have a4 := abs_nonneg (deriv U (step η v x) * (η * v x))
  have a5 := le_abs_self (deriv U x * (η * v x))
  have a6 := neg_abs_le (deriv U (step η v x) * (η * v x))
  rw [abs_le]
  constructor <;> nlinarith

/-- **DT-1 (Mathlib `klDiv`) in dimension one, moment form.** Same conclusion as
`DeterministicStep.klDiv_map_step_le`, with its integrability hypotheses replaced as follows:
`p log(p/π)` integrable is replaced by `KL(ρ ‖ π) < ∞`; `p (U∘T - U)`, `p U' v` and `p v²`
integrable are **derived** from the finite second moment `∫ x² p < ∞` and the extra two-sided
bound `|U''| ≤ M` (the upper bound `U'' ≤ L` is kept for the constant of the descent bound).

Setting: `ρ = p dx`, `π = e^{-U}/Z dx` probability measures (`Z > 0`), `p > 0` measurable,
`U`, `U'` differentiable, `v` differentiable with `|v'| ≤ Lv`, `0 ≤ η`, `η Lv ≤ 1/2`,
`T = id + η v`. Then `KL(T#ρ ‖ π) < ∞` and
`KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η ∫ p (v' - U' v) + η² ∫ p (v'² + (L/2) v²)`. -/
theorem klDiv_map_step_le (hv : Differentiable ℝ v) (hv' : ∀ x, |deriv v x| ≤ Lv)
    (hη : 0 ≤ η) (hηL : η * Lv ≤ 1 / 2) (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hZ : 0 < Z) (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, deriv (deriv U) z ≤ L) (hUM : ∀ z, |deriv (deriv U) z| ≤ M)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞)
    (hm : Integrable fun x => x ^ 2 * p x) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step η v)) (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (∫ x, p x * (deriv v x - deriv U x * v x)) +
        η ^ 2 * ∫ x, p x * (deriv v x ^ 2 + L / 2 * v x ^ 2) := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hp_int : Integrable p := integrable_of_isProbabilityMeasure hp_meas hp0
  have hm' := integrable_norm_sq_mul_of_sq hm
  have hπ_meas : Measurable (gibbsDensity U Z) :=
    (Real.measurable_exp.comp hU.continuous.measurable.neg).div_const Z
  have hKL' := integrable_klIntegrand_of_klDiv_ne_top hp_meas hπ_meas hp0
    (fun x => div_pos (Real.exp_pos _) hZ) hKL
  have hvl : LinGrowth v := linGrowth_of_abs_deriv_le hv hv'
  have hdU : LinGrowth (deriv U) := linGrowth_of_abs_deriv_le hU' hUM
  have hUT := (quadGrowth_comp_step_sub (η := η) hU hU' hUM hvl).integrable_mul
    ((hU.continuous.comp (continuous_step hv)).sub hU.continuous).aestronglyMeasurable
    hp0 hp_int hm'
  have hUv := (QuadGrowth.mul hdU hvl).integrable_mul
    (hU'.continuous.mul hv.continuous).aestronglyMeasurable hp0 hp_int hm'
  have hv2 := (QuadGrowth.sq hvl).integrable_mul
    (hv.continuous.pow 2).aestronglyMeasurable hp0 hp_int hm'
  exact DeterministicStep.klDiv_map_step_le hv hv' hη hηL hp hp_meas hZ hU hU' hU'' hKL' hUT
    hUv hv2

end OneDim

/-! ### Dimension one: the ideal velocity from a finite second moment -/

section IdealOneDim

open DeterministicStep IdealVelocityStep

variable {η LU Lp Z : ℝ} {U p : ℝ → ℝ}

/-- **DT-1 for the ideal velocity (Mathlib `klDiv`) in dimension one, moment form.** Same
conclusion as `IdealVelocityStep.klDiv_map_step_idealVel_le`, with its integrability
hypotheses replaced as follows: `p log(p/π)` integrable is replaced by `KL(ρ ‖ π) < ∞`; the
integrability of `p (U∘T - U)`, of the Fisher integrand `((log p)' + U')² p`, of `v p'` and of
`v p` is **derived** from the finite second moment `∫ x² p < ∞`. No extra Hessian hypothesis is
needed: `|U''| ≤ L_U` is already two-sided, and `|(log p)''| ≤ L_p` makes the score
`(log p)'`, hence `v = -U' - (log p)'`, of linear growth. In particular the relative Fisher
information `I(ρ‖π)` is automatically finite (`∫ v² p < ∞`).

Setting: `ρ = p dx`, `π = e^{-U}/Z dx` probability measures (`Z > 0`), `p > 0` measurable with
`p`, `p'` differentiable and `|(log p)''| ≤ L_p`, `U`, `U'` differentiable with `|U''| ≤ L_U`,
`v = -U' - (log p)'`, `0 ≤ η`, `η (L_U + L_p) ≤ 1/2`, `T = id + η v`. Then `KL(T#ρ ‖ π) < ∞`
and `KL(T#ρ ‖ π) ≤ KL(ρ ‖ π) - η (1 - η L_U / 2) I(ρ‖π) + η² (L_U + L_p)²`. -/
theorem klDiv_map_step_idealVel_le (hη : 0 ≤ η) (hηL : η * (LU + Lp) ≤ 1 / 2) (hZ : 0 < Z)
    (hU : Differentiable ℝ U) (hU' : Differentiable ℝ (deriv U))
    (hU'' : ∀ z, |deriv (deriv U) z| ≤ LU) (hp : ∀ x, 0 < p x) (hp_meas : Measurable p)
    (hpd : Differentiable ℝ p) (hpd2 : Differentiable ℝ (deriv p))
    (hs' : ∀ z, |deriv (score1 p) z| ≤ Lp)
    [hρ : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [hπ : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))]
    (hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞)
    (hm : Integrable fun x => x ^ 2 * p x) :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step η (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        η * (1 - η * LU / 2) * relFisher U p + η ^ 2 * (LU + Lp) ^ 2 := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hp_int : Integrable p := integrable_of_isProbabilityMeasure hp_meas hp0
  have hm' := integrable_norm_sq_mul_of_sq hm
  have hπ_meas : Measurable (gibbsDensity U Z) :=
    (Real.measurable_exp.comp hU.continuous.measurable.neg).div_const Z
  have hKL' := integrable_klIntegrand_of_klDiv_ne_top hp_meas hπ_meas hp0
    (fun x => div_pos (Real.exp_pos _) hZ) hKL
  have hs := differentiable_score1 hp hpd hpd2
  have hvd := differentiable_idealVel hU' hs
  have hvl : LinGrowth (idealVel U p) :=
    linGrowth_of_abs_deriv_le hvd (abs_deriv_idealVel_le hU' hs hU'' hs')
  have hsl : LinGrowth (score1 p) := linGrowth_of_abs_deriv_le hs hs'
  have hUT := (quadGrowth_comp_step_sub (η := η) hU hU' hU'' hvl).integrable_mul
    ((hU.continuous.comp (continuous_step hvd)).sub hU.continuous).aestronglyMeasurable
    hp0 hp_int hm'
  have hv2 := (QuadGrowth.sq hvl).integrable_mul
    (hvd.continuous.pow 2).aestronglyMeasurable hp0 hp_int hm'
  have hF : Integrable fun x => (score1 p x + deriv U x) ^ 2 * p x :=
    hv2.congr (Eventually.of_forall fun x => mul_idealVel_sq x)
  have hvp' : Integrable fun x => idealVel U p x * deriv p x := by
    refine ((QuadGrowth.mul hvl hsl).integrable_mul
      (hvd.continuous.mul hs.continuous).aestronglyMeasurable hp0 hp_int hm').congr
      (Eventually.of_forall fun x => ?_)
    simp only
    rw [← DensityStein.score1_mul_eq_of_hasDerivAt (hpd x).hasDerivAt (hp x)]
    ring
  have hvp : Integrable fun x => idealVel U p x * p x :=
    ((QuadGrowth.of_linGrowth hvl).integrable_mul hvd.continuous.aestronglyMeasurable hp0
      hp_int hm').congr (Eventually.of_forall fun x => mul_comm _ _)
  exact IdealVelocityStep.klDiv_map_step_idealVel_le hη hηL hZ hU hU' hU'' hp hp_meas hpd hpd2
    hs' hKL' hUT hF hvp' hvp

end IdealOneDim

end FormalizeSampling.DeterministicStepMoments
