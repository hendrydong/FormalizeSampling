module

public import FormalizeSampling.Foundations.GaussianFunctionalLSI
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The Holley–Stroock perturbation lemma for the functional log-Sobolev inequality (1D)

Status: **Verified** (no named hypothesis: the only inputs are the functional LSI of the
reference measure, measurability and two-sided boundedness of the perturbation).

Notation: `Ent`, `LSIClass`, `FunctionalLSI` are those of `Foundations/LogSobolev.lean`
(`FunctionalLSI μ C` is `Ent_μ(g²) ≤ 2 C ∫ (g')² dμ` for `g ∈ LSIClass`). For `c > 0` put
`ψ_c(x) = x log x - x log c - x + c` (`psi c x`).

## Main results

* `psi_nonneg`: `ψ_c(x) ≥ 0` for `c > 0`, `x ≥ 0` (pointwise; from `log y ≤ y - 1`).
* `integral_psi_eq` / `ent_le_integral_psi` / `isGLB_integral_psi` / `isLeast_integral_psi`
  (**variational formula for entropy**): for a probability measure `μ` and `h` with `h`,
  `h log h` integrable, `∫ ψ_c(h) dμ = Ent_μ(h) + ψ_c(∫ h dμ)`; hence `Ent_μ(h) ≤ ∫ ψ_c(h) dμ`
  for every `c > 0` when `∫ h ≥ 0`, `Ent_μ(h) = inf_{c > 0} ∫ ψ_c(h) dμ` (as an `IsGLB`), and the
  infimum is attained at `c = ∫ h dμ` when `∫ h dμ > 0`.
* `functionalLSI_withDensity` (**Holley–Stroock, density form**): if `μ` is a probability measure
  with `FunctionalLSI μ C` (`C ≥ 0`) and `ν = ρ · μ` is a probability measure with measurable
  density `0 < m ≤ ρ ≤ M`, then `FunctionalLSI ν (C · M / m)`.
* `tilt μ W = (e^{-W} / ∫ e^{-W} dμ) · μ` (Mathlib's `μ.tilted (-W)`, `tilt_eq_tilted`),
  `isProbabilityMeasure_tilt`, and `functionalLSI_tilt` (**Holley–Stroock**): for
  `a ≤ W ≤ b` measurable,
  `FunctionalLSI μ C → FunctionalLSI (tilt μ W) (C · e^{b - a})` (`b - a ≥ osc W`).
* `target_add_eq_tilt`: `target (f₀ + W) = tilt (target f₀) W` for measurable `f₀, W` with
  `e^{-f₀}` integrable (targets of `Foundations/GibbsMeasure.lean`).
* `functionalLSI_target_gaussPotential_add` (**bounded perturbation of a Gaussian**): for
  `α > 0` and measurable `W` with `a ≤ W ≤ b`, the proximal-sampler target of
  `f = α x²/2 + W` satisfies `FunctionalLSI (target f) (e^{b - a} / α)`.

## Not proved here

* Unbounded perturbations (e.g. Lipschitz `W`, Aida–Shigekawa / Miclo-type results), and the
  sharper constant with `osc W = sup W - inf W` taken as an essential oscillation; the bounds
  `a ≤ W ≤ b` are pointwise and the constant is `e^{b - a}`.
* Test functions outside `LSIClass` (see `LogSobolevExtension`); the multi-dimensional
  version is in `GaussianFunctionalLSIPi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open FormalizeSampling.LogSobolev FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
open FormalizeSampling.GaussianFunctionalLSI

namespace FormalizeSampling.HolleyStroock

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal)

/-! ### The variational formula for entropy -/

/-- `ψ_c(x) = x log x - x log c - x + c`, the integrand of the variational formula
`Ent_μ(h) = inf_{c > 0} ∫ ψ_c(h) dμ`. -/
noncomputable def psi (c x : ℝ) : ℝ := x * Real.log x - x * Real.log c - x + c

/-- **Pointwise nonnegativity.** For `c > 0` and `x ≥ 0`, `x log x - x log c - x + c ≥ 0`. -/
theorem psi_nonneg {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) : 0 ≤ psi c x := by
  unfold psi
  rcases hx.eq_or_lt with rfl | hx
  · simp [hc.le]
  have h := Real.log_le_sub_one_of_pos (div_pos hc hx)
  rw [Real.log_div hc.ne' hx.ne'] at h
  have h2 := mul_le_mul_of_nonneg_left h hx.le
  have h3 : x * (c / x - 1) = c - x := by field_simp
  rw [mul_sub, h3] at h2
  linarith

/-- `ψ_c(c) = 0`. -/
theorem psi_self (c : ℝ) : psi c c = 0 := by
  unfold psi; ring

/-- `ψ_c(0) = c`. -/
theorem psi_zero (c : ℝ) : psi c 0 = c := by
  simp [psi]

/-- **Variational identity.** For a probability measure `μ` and `h` with `h`, `h log h`
integrable, `∫ ψ_c(h) dμ = Ent_μ(h) + ψ_c(∫ h dμ)` for every `c`. -/
theorem integral_psi_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : α → ℝ} (hh : Integrable h μ)
    (hhl : Integrable (fun x => h x * Real.log (h x)) μ) (c : ℝ) :
    ∫ x, psi c (h x) ∂μ = ent μ h + psi c (∫ x, h x ∂μ) := by
  unfold psi ent
  have i1 : Integrable (fun x => h x * Real.log (h x) - h x * Real.log c) μ :=
    hhl.sub (hh.mul_const _)
  have i2 : Integrable (fun x => h x * Real.log (h x) - h x * Real.log c - h x) μ := i1.sub hh
  rw [integral_add i2 (integrable_const c), integral_sub i1 hh,
    integral_sub hhl (hh.mul_const _), integral_mul_const]
  simp
  ring

/-- Under the hypotheses of `integral_psi_eq`, `x ↦ ψ_c(h x)` is integrable. -/
theorem integrable_psi {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {h : α → ℝ} (hh : Integrable h μ) (hhl : Integrable (fun x => h x * Real.log (h x)) μ)
    (c : ℝ) : Integrable (fun x => psi c (h x)) μ :=
  ((hhl.sub (hh.mul_const _)).sub hh).add (integrable_const _)

/-- **Variational upper bound.** For a probability measure `μ`, `h` with `h`, `h log h`
integrable and `∫ h dμ ≥ 0` (e.g. `h ≥ 0`), `Ent_μ(h) ≤ ∫ ψ_c(h) dμ` for every `c > 0`. -/
theorem ent_le_integral_psi {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : α → ℝ} (hh : Integrable h μ)
    (hhl : Integrable (fun x => h x * Real.log (h x)) μ) (hm : 0 ≤ ∫ x, h x ∂μ) {c : ℝ}
    (hc : 0 < c) : ent μ h ≤ ∫ x, psi c (h x) ∂μ := by
  rw [integral_psi_eq hh hhl]
  linarith [psi_nonneg hc hm]

/-- **Variational formula for entropy.** For a probability measure `μ` and `h` with `h`,
`h log h` integrable and `∫ h dμ ≥ 0`: `Ent_μ(h) = inf_{c > 0} ∫ ψ_c(h) dμ`, i.e. `Ent_μ(h)` is
the greatest lower bound of `{∫ ψ_c(h) dμ | c > 0}`. -/
theorem isGLB_integral_psi {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : α → ℝ} (hh : Integrable h μ)
    (hhl : Integrable (fun x => h x * Real.log (h x)) μ) (hm : 0 ≤ ∫ x, h x ∂μ) :
    IsGLB ((fun c => ∫ x, psi c (h x) ∂μ) '' Ioi 0) (ent μ h) := by
  refine ⟨?_, fun l hl => ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ent_le_integral_psi hh hhl hm hc
  rcases hm.eq_or_lt with hm0 | hmpos
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hl ⟨ε, hε, rfl⟩
    simp only at this
    rwa [integral_psi_eq hh hhl, ← hm0, psi_zero] at this
  · have := hl ⟨_, hmpos, rfl⟩
    simp only at this
    rwa [integral_psi_eq hh hhl, psi_self, add_zero] at this

/-- **The infimum is attained.** If moreover `∫ h dμ > 0`, then `Ent_μ(h)` is the least element
of `{∫ ψ_c(h) dμ | c > 0}`, attained at `c = ∫ h dμ`. -/
theorem isLeast_integral_psi {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : α → ℝ} (hh : Integrable h μ)
    (hhl : Integrable (fun x => h x * Real.log (h x)) μ) (hm : 0 < ∫ x, h x ∂μ) :
    IsLeast ((fun c => ∫ x, psi c (h x) ∂μ) '' Ioi 0) (ent μ h) :=
  ⟨⟨_, hm, by simp only; rw [integral_psi_eq hh hhl, psi_self, add_zero]⟩,
    (isGLB_integral_psi hh hhl hm.le).1⟩

/-! ### Holley–Stroock: bounded density perturbations -/

/-- **Holley–Stroock, density form.** Let `μ` be a probability measure on `ℝ` with
`FunctionalLSI μ C`, `C ≥ 0`, and let `ρ` be measurable with `0 < m ≤ ρ ≤ M` such that
`ν = ρ · μ` is a probability measure. Then `FunctionalLSI ν (C · (M / m))`. -/
theorem functionalLSI_withDensity {μ : Measure ℝ} [IsProbabilityMeasure μ] {C : ℝ}
    (hμ : FunctionalLSI μ C) (hC : 0 ≤ C) {ρ : ℝ → ℝ} (hρ : Measurable ρ) {m M : ℝ}
    (hm : 0 < m) (hmρ : ∀ x, m ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (ρ x))] :
    FunctionalLSI (μ.withDensity fun x => ENNReal.ofReal (ρ x)) (C * (M / m)) := by
  intro g hg
  set ν := μ.withDensity fun x => ENNReal.ofReal (ρ x) with hνdef
  obtain ⟨K₀, hK₀⟩ := hg.bounded
  obtain ⟨K₁, hK₁⟩ := hg.bounded_deriv
  obtain ⟨c, hc, hcg⟩ := hg.pos
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => hm.le.trans (hmρ x)
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have hρabs : ∀ x, ‖ρ x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]; exact hρM x
  have hgm : Measurable g := hg.differentiable.continuous.measurable
  set h : ℝ → ℝ := fun x => g x ^ 2 with hhdef
  have hhm : Measurable h := hgm.pow_const 2
  have hh0 : ∀ x, 0 ≤ h x := fun x => sq_nonneg _
  have hhK : ∀ x, |h x| ≤ K₀ ^ 2 := fun x => by
    rw [abs_of_nonneg (hh0 x)]
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ K₀ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hK₀ x) 2
  have hhlK : ∀ x, |h x * Real.log (h x)| ≤ (K₀ ^ 2) ^ 2 + 1 := fun x =>
    (abs_mul_log_le (hh0 x)).trans (by
      have := hhK x; rw [abs_of_nonneg (hh0 x)] at this; have := hh0 x; gcongr)
  have hdm : Measurable fun x => deriv g x ^ 2 := (measurable_deriv g).pow_const 2
  have hdK : ∀ x, |deriv g x ^ 2| ≤ K₁ ^ 2 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hK₁ x) 2
  -- integrability under `μ` and `ν`
  have hhμ : Integrable h μ := integrable_of_abs_le hhm.aestronglyMeasurable _ hhK
  have hhlμ : Integrable (fun x => h x * Real.log (h x)) μ :=
    integrable_of_abs_le (hhm.mul hhm.log).aestronglyMeasurable _ hhlK
  have hhν : Integrable h ν := integrable_of_abs_le hhm.aestronglyMeasurable _ hhK
  have hhlν : Integrable (fun x => h x * Real.log (h x)) ν :=
    integrable_of_abs_le (hhm.mul hhm.log).aestronglyMeasurable _ hhlK
  have hdμ : Integrable (fun x => deriv g x ^ 2) μ :=
    integrable_of_abs_le hdm.aestronglyMeasurable _ hdK
  have hρdμ : Integrable (fun x => ρ x * deriv g x ^ 2) μ :=
    hdμ.bdd_mul hρ.aestronglyMeasurable (ae_of_all _ hρabs)
  -- the mass `s = ∫ g² dμ > 0`
  set s := ∫ x, h x ∂μ with hsdef
  have hs : 0 < s := lt_of_lt_of_le (pow_pos hc 2)
    (le_integral_of_le_prob hhμ fun x => pow_le_pow_left₀ hc.le (hcg x) 2)
  have hψμ := integrable_psi hhμ hhlμ s
  have hψ0 : ∀ x, 0 ≤ psi s (h x) := fun x => psi_nonneg hs (hh0 x)
  have hνent : ent ν h ≤ ∫ x, psi s (h x) ∂ν :=
    ent_le_integral_psi hhν hhlν (integral_nonneg hh0) hs
  have hμent : ∫ x, psi s (h x) ∂μ = ent μ h := by
    rw [integral_psi_eq hhμ hhlμ, ← hsdef, psi_self, add_zero]
  have hLSI : ent μ h ≤ 2 * C * ∫ x, deriv g x ^ 2 ∂μ := hμ g hg
  have hd_le : ∫ x, deriv g x ^ 2 ∂μ ≤ (1 / m) * ∫ x, ρ x * deriv g x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hdμ (hρdμ.const_mul _) fun x => ?_
    have h1 : m * deriv g x ^ 2 ≤ ρ x * deriv g x ^ 2 :=
      mul_le_mul_of_nonneg_right (hmρ x) (sq_nonneg _)
    rw [← mul_assoc, one_div, ← div_eq_inv_mul, div_mul_eq_mul_div, le_div_iff₀ hm]
    linarith
  calc ent ν h ≤ ∫ x, psi s (h x) ∂ν := hνent
    _ = ∫ x, ρ x * psi s (h x) ∂μ := integral_withDensity_ofReal hρ hρ0 _
    _ ≤ ∫ x, M * psi s (h x) ∂μ :=
        integral_mono (hψμ.bdd_mul hρ.aestronglyMeasurable (ae_of_all _ hρabs))
          (hψμ.const_mul _) fun x => mul_le_mul_of_nonneg_right (hρM x) (hψ0 x)
    _ = M * ent μ h := by rw [integral_const_mul, hμent]
    _ ≤ M * (2 * C * ∫ x, deriv g x ^ 2 ∂μ) := mul_le_mul_of_nonneg_left hLSI hM
    _ ≤ M * (2 * C * ((1 / m) * ∫ x, ρ x * deriv g x ^ 2 ∂μ)) := by gcongr
    _ = 2 * (C * (M / m)) * ∫ x, deriv g x ^ 2 ∂ν := by
        rw [hνdef, integral_withDensity_ofReal hρ hρ0]
        ring

/-- The **tilt** of `μ` by a potential `W`: `(e^{-W} / Z) · μ` with `Z = ∫ e^{-W} dμ`. -/
noncomputable def tilt {α : Type*} [MeasurableSpace α] (μ : Measure α) (W : α → ℝ) :
    Measure α :=
  μ.withDensity fun x => ENNReal.ofReal (Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂μ)

/-- `tilt μ W` is Mathlib's exponential tilt of `μ` by `-W`:
`tilt μ W = μ.tilted (-W)`, where `μ.tilted g = (e^{g} / ∫ e^{g} dμ) · μ`
(`MeasureTheory.Measure.tilted`). Mathlib's API for `Measure.tilted` (e.g.
`MeasureTheory.isProbabilityMeasure_tilted`, `MeasureTheory.tilted_tilted`) therefore applies to
`tilt`. -/
theorem tilt_eq_tilted {α : Type*} [MeasurableSpace α] (μ : Measure α) (W : α → ℝ) :
    tilt μ W = μ.tilted fun x => -W x := rfl

/-- For a probability measure `μ` and measurable `W` with `a ≤ W ≤ b`, the normaliser
`Z = ∫ e^{-W} dμ` satisfies `e^{-b} ≤ Z ≤ e^{-a}`, and `e^{-W}` is `μ`-integrable. -/
theorem integrable_exp_neg_and_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {W : α → ℝ} (hW : Measurable W) {a b : ℝ} (ha : ∀ x, a ≤ W x)
    (hb : ∀ x, W x ≤ b) :
    Integrable (fun x => Real.exp (-W x)) μ ∧ Real.exp (-b) ≤ ∫ x, Real.exp (-W x) ∂μ ∧
      ∫ x, Real.exp (-W x) ∂μ ≤ Real.exp (-a) := by
  have hi : Integrable (fun x => Real.exp (-W x)) μ :=
    integrable_of_abs_le (Real.measurable_exp.comp hW.neg).aestronglyMeasurable
      (Real.exp (-a)) fun x => by
        rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (by linarith [ha x])
  exact ⟨hi, le_integral_of_le_prob hi fun x => Real.exp_le_exp.2 (by linarith [hb x]),
    integral_le_of_le_prob hi fun x => Real.exp_le_exp.2 (by linarith [ha x])⟩

/-- For a probability measure `μ` and measurable `W` with `a ≤ W ≤ b`, the tilt `tilt μ W` is a
probability measure. -/
theorem isProbabilityMeasure_tilt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {W : α → ℝ} (hW : Measurable W) {a b : ℝ} (ha : ∀ x, a ≤ W x)
    (hb : ∀ x, W x ≤ b) : IsProbabilityMeasure (tilt μ W) := by
  obtain ⟨hi, hZb, -⟩ := integrable_exp_neg_and_bounds (μ := μ) hW ha hb
  have hZ : 0 < ∫ x, Real.exp (-W x) ∂μ := (Real.exp_pos _).trans_le hZb
  constructor
  rw [tilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (ae_of_all _ fun x => by positivity), integral_div, div_self hZ.ne', ENNReal.ofReal_one]

/-- **Holley–Stroock perturbation lemma.** Let `μ` be a probability measure on `ℝ` with
`FunctionalLSI μ C`, `C ≥ 0`, and let `W` be measurable with `a ≤ W ≤ b`. Then the tilted
measure `ν = (e^{-W} / Z) · μ` satisfies `FunctionalLSI ν (C · e^{b - a})`. -/
theorem functionalLSI_tilt {μ : Measure ℝ} [IsProbabilityMeasure μ] {C : ℝ}
    (hμ : FunctionalLSI μ C) (hC : 0 ≤ C) {W : ℝ → ℝ} (hW : Measurable W) {a b : ℝ}
    (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) :
    FunctionalLSI (tilt μ W) (C * Real.exp (b - a)) := by
  obtain ⟨-, hZb, -⟩ := integrable_exp_neg_and_bounds (μ := μ) hW ha hb
  set Z := ∫ x, Real.exp (-W x) ∂μ with hZdef
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hZb
  have hP : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (Real.exp (-W x) / Z)) :=
    isProbabilityMeasure_tilt (μ := μ) hW ha hb
  have h := functionalLSI_withDensity hμ hC (ρ := fun x => Real.exp (-W x) / Z)
    ((Real.measurable_exp.comp hW.neg).div_const _) (m := Real.exp (-b) / Z)
    (M := Real.exp (-a) / Z) (by positivity)
    (fun x => div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hb x])) hZ.le)
    (fun x => div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [ha x])) hZ.le)
  have hr : Real.exp (-a) / Z / (Real.exp (-b) / Z) = Real.exp (b - a) := by
    rw [div_div_div_cancel_right₀ hZ.ne', ← Real.exp_sub]; ring_nf
  rw [hr] at h
  exact h

/-! ### Bounded perturbations of the proximal-sampler targets -/

/-- **Targets of perturbed potentials are tilts.** For measurable `f₀`, `W` with `e^{-f₀}`
Lebesgue-integrable, `target (f₀ + W) = tilt (target f₀) W`. -/
theorem target_add_eq_tilt {f₀ W : ℝ → ℝ} (hf₀ : Measurable f₀) (hW : Measurable W)
    (hint : Integrable (fun x => Real.exp (-f₀ x))) :
    target (fun x => f₀ x + W x) = tilt (target f₀) W := by
  have hZ₀ : 0 < targetNormalizer f₀ := targetNormalizer_pos hint
  have hZ' : ∫ y, Real.exp (-W y) ∂target f₀ =
      targetNormalizer (fun x => f₀ x + W x) / targetNormalizer f₀ := by
    rw [target, integral_withDensity_ofReal (measurable_targetDensity hf₀)
      (targetDensity_nonneg), targetNormalizer, ← integral_div]
    congr 1
    funext x
    rw [targetDensity, neg_add, Real.exp_add]
    ring
  have m₁ : Measurable fun x => ENNReal.ofReal (targetDensity f₀ x) :=
    (measurable_targetDensity hf₀).ennreal_ofReal
  have m₂ : Measurable fun x => ENNReal.ofReal (Real.exp (-W x) /
      (targetNormalizer (fun x => f₀ x + W x) / targetNormalizer f₀)) := by
    fun_prop
  rw [tilt, hZ', target, target, ← withDensity_mul _ m₁ m₂]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (targetDensity_nonneg x)]
  congr 1
  rw [targetDensity, targetDensity, neg_add, Real.exp_add]
  field_simp

/-- **Bounded perturbation of a Gaussian target.** For `α > 0` and measurable `W` with
`a ≤ W ≤ b`, the proximal-sampler target of `f(x) = α x²/2 + W(x)` satisfies
`FunctionalLSI (target f) (e^{b - a} / α)`: it is the tilt of `N(0, 1/α)` (Gross's inequality,
constant `1/α`) by `W`. -/
theorem functionalLSI_target_gaussPotential_add {α : ℝ} (hα : 0 < α) {W : ℝ → ℝ}
    (hW : Measurable W) {a b : ℝ} (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) :
    FunctionalLSI (target fun x => gaussPotential α x + W x) (Real.exp (b - a) / α) := by
  rw [target_add_eq_tilt (measurable_gaussPotential α) hW
    (integrable_exp_neg_gaussPotential hα), target_gaussPotential hα, div_eq_inv_mul]
  exact functionalLSI_tilt (functionalLSI_gaussianReal α⁻¹ (inv_pos.2 hα))
    (inv_nonneg.2 hα.le) hW ha hb

end FormalizeSampling.HolleyStroock
