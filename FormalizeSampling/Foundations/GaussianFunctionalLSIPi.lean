module

public import FormalizeSampling.Foundations.GaussianLSIZeroPi
public import FormalizeSampling.Foundations.LogSobolevPi
public import FormalizeSampling.Foundations.HolleyStroock
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The Gaussian functional log-Sobolev inequality and Holley–Stroock on `Fin d → ℝ`

Status: **Verified** (no named hypotheses: Gross's inequality needs only `t > 0`; Holley–Stroock
needs the functional LSI of the reference measure, measurability and two-sided bounds of the
perturbation).

Notation: `gradSq`, `LSIClassPi`, `FunctionalLSIPi` are those of
`Foundations/LogSobolevPi.lean` (`FunctionalLSIPi μ C` is `Ent_μ(g²) ≤ 2 C ∫ |∇g|² dμ` for
`g ∈ LSIClassPi`); `φ_t = heatDensityPi t` is the density of `N(0, t I)`.

Route (Gross): for `g ∈ LSIClassPi`, `Z = ∫ g² φ_t` and `p = g² φ_t / Z`, the KL-form time-zero
Gaussian LSI applied to `p` gives `Ent(g²) / Z = KL(p‖N(0, tI)) ≤ (t/2) · 4 ∫ |∇g|² φ_t / Z`.
The time-zero LSI of `Foundations/GaussianLSIZeroPi.lean` needs no continuity of the gradient,
which matters because `∇g` is only measurable for `g ∈ LSIClassPi`. The Holley–Stroock argument
is that of `Foundations/HolleyStroock.lean`, whose variational entropy lemmas and `tilt` are
stated for general measure spaces and are reused.

## Main results

* `functionalLSIPi_gaussian` (**Gross's inequality**):
  `∀ t > 0, FunctionalLSIPi (Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal) t`.
* `functionalLSIPi_withDensity` (**Holley–Stroock, density form**): `FunctionalLSIPi μ C`,
  `C ≥ 0`, measurable `0 < m ≤ ρ ≤ M` with `ρ · μ` a probability measure
  `⇒ FunctionalLSIPi (ρ · μ) (C · (M / m))`.
* `functionalLSIPi_tilt` (**Holley–Stroock**): `a ≤ W ≤ b` measurable
  `⇒ FunctionalLSIPi (tilt μ W) (C · e^{b - a})`.
* `targetPi_add_eq_tilt`: `targetPi (f₀ + W) = tilt (targetPi f₀) W`.
* `functionalLSIPi_targetPi_gaussPotentialPi_add`: for `α > 0` and measurable `a ≤ W ≤ b`,
  `FunctionalLSIPi (targetPi (gaussPotentialPi α + W)) (e^{b - a} / α)`.

## Not proved here

* Gross's inequality for test functions outside `LSIClassPi`, and the `t = 0` (Dirac) case.
* Unbounded perturbations; essential (rather than pointwise) oscillation bounds on `W`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.GaussianFunctionalLSIPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
open FormalizeSampling.GaussianLSIPi FormalizeSampling.GaussianLSIZeroPi
open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevPi
open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_of_isProbabilityMeasure)
open FormalizeSampling.GaussianLSIZero (abs_le_add_sq_div integrable_of_sq_div
  klDiv_withDensity_eq_lintegral continuousAt_heatDensity_time)

variable {d : ℕ}

/-! ### Gradients -/

/-- Every continuous linear functional on `Fin d → ℝ` is a dot product with its values on the
basis: `L = dotCLM (i ↦ L eᵢ)` (no assumptions). -/
theorem eq_dotCLM_apply_single (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    L = dotCLM fun i => L (Pi.single i 1) := by
  refine eq_dotCLM_of_apply fun v => ?_
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (v i) : Fin d → ℝ) = v i • Pi.single i 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

/-! ### Gross's inequality on `Fin d → ℝ` -/

section Functional

/-- For `t > 0`, `N(0, t I) = ⊗ᵢ N(0, t)` is the Lebesgue density law of `heatDensityPi t`. -/
theorem pi_gaussianReal_eq_withDensity {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal)
      = volume.withDensity fun y => ENNReal.ofReal (heatDensityPi t y) := by
  rw [pi_gaussianReal_eq_heatKernelPi, heatKernelPi_eq_withDensity ht]
  simp_rw [sub_zero]

/-- For `t > 0`, `∫ h dN(0, t I) = ∫ φ_t(y) h(y) dy` (`φ_t = heatDensityPi t`; Bochner integrals,
no integrability needed). -/
theorem integral_pi_gaussianReal_eq {t : ℝ} (ht : 0 < t) (h : (Fin d → ℝ) → ℝ) :
    ∫ y, h y ∂(Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal)
      = ∫ y, heatDensityPi t y * h y := by
  rw [pi_gaussianReal_eq_withDensity ht]
  exact integral_withDensity_ofReal (continuous_heatDensityPi t).measurable
    (fun y => (heatDensityPi_pos ht y).le) h

/-- For `t > 0`, `heatDensityPi t` is Lebesgue integrable. -/
theorem integrable_heatDensityPi {t : ℝ} (ht : 0 < t) :
    Integrable (heatDensityPi (d := d) t) := by
  simpa using (integrable_heatDensityPi_sub (d := d) ht 0).1

/-- For `t > 0`, `∫ heatDensityPi t = 1`. -/
theorem integral_heatDensityPi {t : ℝ} (ht : 0 < t) :
    ∫ y, heatDensityPi (d := d) t y = 1 := by
  simpa using (integrable_heatDensityPi_sub (d := d) ht 0).2

/-- For `t > 0`, `y ↦ (∑ᵢ yᵢ²) φ_t(y)` is Lebesgue integrable (second moment of `N(0, t I)`). -/
theorem integrable_sumSq_mul_heatDensityPi {t : ℝ} (ht : 0 < t) :
    Integrable fun y : Fin d → ℝ => (∑ i, y i ^ 2) * heatDensityPi t y := by
  have h : Integrable (fun y : Fin d → ℝ => ∑ i, y i ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal) :=
    integrable_finsetSum _ fun i _ =>
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 t.toNNReal)
        i).integrable_comp_of_integrable (memLp_id_gaussianReal 2).integrable_sq
  rw [pi_gaussianReal_eq_withDensity ht, integrable_withDensity_iff_integrable_smul'
    (continuous_heatDensityPi t).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (heatDensityPi_pos ht y).le, smul_eq_mul, mul_comm]

/-- If `f` is measurable with `|f| ≤ K`, then `φ_t f` is Lebesgue integrable (`t > 0`). -/
theorem integrable_heatDensityPi_mul {t : ℝ} (ht : 0 < t) {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) (K : ℝ) (hK : ∀ y, |f y| ≤ K) :
    Integrable fun y => heatDensityPi t y * f y :=
  (integrable_heatDensityPi ht).mul_bdd (c := K) hf.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hK y)

/-- **Gaussian functional log-Sobolev inequality on `Fin d → ℝ` (Gross).** For every `t > 0`,
`N(0, t I) = Measure.pi fun _ => gaussianReal 0 t` satisfies `FunctionalLSIPi N(0, t I) t`:
`Ent_{N(0,tI)}(g²) ≤ 2 t ∫ |∇g|² dN(0, t I)` for every `g ∈ LSIClassPi`.

Proof: with `φ = φ_t`, `Z = ∫ g² φ > 0` and the probability density `p = g² φ / Z`
(gradient `∇p = (2 g ∇g φ + g² ∇φ) / Z`, so `∇p/p + x/t = 2 ∇g / g`), one has
`KL(p‖N(0, t I)) = Ent(g²) / Z` and `p |∇p/p + x/t|² = 4 |∇g|² φ / Z`; the KL-form time-zero LSI
`GaussianLSIZeroPi.klDiv_le_fisher0` (no continuity of `∇g` needed) gives the claim. -/
theorem functionalLSIPi_gaussian : ∀ t > 0,
    FunctionalLSIPi (Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal) t := by
  intro t ht g hg
  obtain ⟨hgdiff, ⟨M, hM⟩, ⟨K, hK⟩, c, hc, hcg⟩ := hg
  set γ := Measure.pi fun _ : Fin d => gaussianReal 0 t.toNNReal with hγ
  set φ : (Fin d → ℝ) → ℝ := heatDensityPi t with hφdef
  set gg : (Fin d → ℝ) → Fin d → ℝ := fun x i => fderiv ℝ g x (Pi.single i 1) with hggdef
  have hφ : ∀ x, 0 < φ x := heatDensityPi_pos ht
  have hφc : Continuous φ := continuous_heatDensityPi t
  have hgd : ∀ x, HasFDerivAt g (dotCLM (gg x)) x := fun x => by
    have := (hgdiff x).hasFDerivAt
    rwa [eq_dotCLM_apply_single (fderiv ℝ g x)] at this
  have hgc : Continuous g := hgdiff.continuous
  have hg0 : ∀ x, 0 < g x := fun x => hc.trans_le (hcg x)
  have hg2M : ∀ x, |g x ^ 2| ≤ M ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have hGK : ∀ x, |gradSq g x| ≤ K := fun x => by
    rw [abs_of_nonneg (gradSq_nonneg g x)]; exact hK x
  have hlogM : ∀ x, |g x ^ 2 * Real.log (g x ^ 2)| ≤ (M ^ 2) ^ 2 + 1 := fun x =>
    (abs_mul_log_le (sq_nonneg _)).trans (by
      have := hg2M x; rw [abs_of_nonneg (sq_nonneg _)] at this; gcongr)
  -- integrals against `γ` as Lebesgue integrals
  have hI1 : Integrable fun x => φ x * g x ^ 2 :=
    integrable_heatDensityPi_mul ht (hgc.measurable.pow_const 2) _ hg2M
  have hI2 : Integrable fun x => φ x * (g x ^ 2 * Real.log (g x ^ 2)) :=
    integrable_heatDensityPi_mul ht
      ((hgc.measurable.pow_const 2).mul (hgc.measurable.pow_const 2).log) _ hlogM
  have hI3 : Integrable fun x => φ x * gradSq g x :=
    integrable_heatDensityPi_mul ht (measurable_gradSq g) _ hGK
  set Z := ∫ x, φ x * g x ^ 2 with hZdef
  have hZ : 0 < Z := by
    have h1 : ∫ x, φ x * c ^ 2 ≤ Z :=
      integral_mono ((integrable_heatDensityPi ht).mul_const _) hI1
        fun x => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le (hcg x) 2) (hφ x).le
    rw [integral_mul_const, integral_heatDensityPi ht, one_mul] at h1
    exact (pow_pos hc 2).trans_le h1
  -- the probability density `p = g² φ / Z`
  set p : (Fin d → ℝ) → ℝ := fun x => g x ^ 2 * φ x / Z with hpdef
  set gp : (Fin d → ℝ) → Fin d → ℝ :=
    fun x i => (2 * g x * gg x i * φ x + g x ^ 2 * heatGradPi t x i) / Z with hgpdef
  have hp : ∀ x, 0 < p x := fun x => div_pos (mul_pos (pow_pos (hg0 x) 2) (hφ x)) hZ
  have hpd : ∀ x, HasFDerivAt p (dotCLM (gp x)) x := by
    intro x
    have h := (((hgd x).mul (hgd x)).mul (hasFDerivAt_heatDensityPi t x)).mul_const Z⁻¹
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_fderiv
      (eq_dotCLM_of_apply fun w => ?_)
    · simp only [hpdef, hφdef, Pi.mul_apply]; ring
    simp only [add_apply, smul_apply, smul_eq_mul, dotCLM_apply, dotProduct, hgpdef, hφdef,
      Finset.mul_sum, Pi.mul_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hpc : Continuous p := ((hgc.pow 2).mul hφc).div_const Z
  have hpint : ∫ x, p x = 1 := by
    simp only [hpdef]
    rw [integral_div]
    simp_rw [mul_comm (g _ ^ 2)]
    exact div_self hZ.ne'
  have hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal _ (Eventually.of_forall fun x => (hp x).le), hpint,
      ENNReal.ofReal_one]
    exact (hI1.div_const Z).congr (Eventually.of_forall fun x => by simp only [hpdef]; ring)
  -- second moment and Fisher information
  have hmom : Integrable fun x => (∑ i, x i ^ 2) * p x := by
    refine ((integrable_sumSq_mul_heatDensityPi ht).mul_bdd (c := M ^ 2 / Z)
      ((hgc.measurable.pow_const 2).div_const Z).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)).congr (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos hZ]
      exact div_le_div_of_nonneg_right (hg2M x) hZ.le
    · simp only [hpdef]; ring
  have hfe : ∀ x, p x * ∑ i, (gp x i / p x + x i / t) ^ 2 = 4 / Z * (φ x * gradSq g x) := by
    intro x
    have h1 := (hg0 x).ne'
    have h2 := (hφ x).ne'
    simp only [hpdef, hgpdef, heatGradPi, gradSq, ← hφdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hfish : Integrable fun x => p x * ∑ i, (gp x i / p x + x i / t) ^ 2 :=
    (hI3.const_mul (4 / Z)).congr (Eventually.of_forall fun x => (hfe x).symm)
  obtain ⟨-, hlsi⟩ := GaussianLSIZeroPi.klDiv_le_fisher0 hp hpd ht hmom hfish
  -- the KL divergence is `Ent / Z`
  have hkl : (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x)) γ).toReal
      = ent γ (fun x => g x ^ 2) / Z := by
    have : IsProbabilityMeasure (volume.withDensity fun y => ENNReal.ofReal (φ y)) :=
      pi_gaussianReal_eq_withDensity (d := d) ht ▸ inferInstance
    have hent : ent γ (fun x => g x ^ 2)
        = (∫ x, φ x * (g x ^ 2 * Real.log (g x ^ 2))) - Z * Real.log Z := by
      unfold ent
      rw [integral_pi_gaussianReal_eq ht, integral_pi_gaussianReal_eq ht]
    have hφ1 : ∫ x, φ x = 1 := integral_heatDensityPi ht
    rw [hent, hγ, pi_gaussianReal_eq_withDensity ht, klDiv_withDensity_eq_lintegral
      hpc.measurable hφc.measurable (fun x => (hp x).le) hφ]
    have hpt : ∀ x, φ x * klFun (p x / φ x) = 1 / Z * (φ x * (g x ^ 2 * Real.log (g x ^ 2)))
        - Real.log Z / Z * (φ x * g x ^ 2) + φ x - 1 / Z * (φ x * g x ^ 2) := by
      intro x
      have h1 : p x / φ x = g x ^ 2 / Z := by
        simp only [hpdef]; field_simp [(hφ x).ne']
      rw [h1, klFun_apply, Real.log_div (pow_pos (hg0 x) 2).ne' hZ.ne']
      field_simp
    have hint : Integrable fun x => φ x * klFun (p x / φ x) := by
      refine ((((hI2.const_mul (1 / Z)).sub (hI1.const_mul (Real.log Z / Z))).add
        (integrable_heatDensityPi ht)).sub (hI1.const_mul (1 / Z))).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
      mul_nonneg (hφ x).le (klFun_nonneg (div_pos (hp x) (hφ x)).le)),
      ENNReal.toReal_ofReal (integral_nonneg fun x =>
        mul_nonneg (hφ x).le (klFun_nonneg (div_pos (hp x) (hφ x)).le))]
    simp_rw [hpt]
    rw [integral_sub ?_ (hI1.const_mul _), integral_add ?_ (integrable_heatDensityPi ht),
      integral_sub (hI2.const_mul _) (hI1.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, hφ1, ← hZdef]
    · field_simp
      ring
    · exact (hI2.const_mul _).sub (hI1.const_mul _)
    · exact ((hI2.const_mul _).sub (hI1.const_mul _)).add (integrable_heatDensityPi ht)
  have hfi : ∫ x, p x * ∑ i, (gp x i / p x + x i / t) ^ 2 = 4 / Z * ∫ x, gradSq g x ∂γ := by
    rw [integral_pi_gaussianReal_eq ht, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hfe)
  rw [hkl, hfi, div_le_iff₀ hZ] at hlsi
  have : t / 2 * (4 / Z * ∫ x, gradSq g x ∂γ) * Z = 2 * t * ∫ x, gradSq g x ∂γ := by
    field_simp; ring
  linarith

end Functional

/-! ### Holley–Stroock perturbation lemma on `Fin d → ℝ` -/

section HolleyStroock

open FormalizeSampling.HolleyStroock (psi psi_nonneg psi_self integral_psi_eq integrable_psi
  ent_le_integral_psi tilt integrable_exp_neg_and_bounds isProbabilityMeasure_tilt)

/-- **Holley–Stroock, density form, on `Fin d → ℝ`.** Let `μ` be a probability measure with
`FunctionalLSIPi μ C`, `C ≥ 0`, and `ρ` measurable with `0 < m ≤ ρ ≤ M` such that `ν = ρ · μ`
is a probability measure. Then `FunctionalLSIPi ν (C · (M / m))`. Same proof as
`HolleyStroock.functionalLSI_withDensity` (variational formula for the entropy). -/
theorem functionalLSIPi_withDensity {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {C : ℝ}
    (hμ : FunctionalLSIPi μ C) (hC : 0 ≤ C) {ρ : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ)
    {m M : ℝ} (hm : 0 < m) (hmρ : ∀ x, m ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (ρ x))] :
    FunctionalLSIPi (μ.withDensity fun x => ENNReal.ofReal (ρ x)) (C * (M / m)) := by
  intro g hg
  set ν := μ.withDensity fun x => ENNReal.ofReal (ρ x) with hνdef
  obtain ⟨hgdiff, ⟨K₀, hK₀⟩, ⟨K₁, hK₁⟩, c, hc, hcg⟩ := id hg
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => hm.le.trans (hmρ x)
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have hρabs : ∀ x, ‖ρ x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]; exact hρM x
  have hgm : Measurable g := hgdiff.continuous.measurable
  set h : (Fin d → ℝ) → ℝ := fun x => g x ^ 2 with hhdef
  have hhm : Measurable h := hgm.pow_const 2
  have hh0 : ∀ x, 0 ≤ h x := fun x => sq_nonneg _
  have hhK : ∀ x, |h x| ≤ K₀ ^ 2 := fun x => by
    rw [abs_of_nonneg (hh0 x)]
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ K₀ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hK₀ x) 2
  have hhlK : ∀ x, |h x * Real.log (h x)| ≤ (K₀ ^ 2) ^ 2 + 1 := fun x =>
    (abs_mul_log_le (hh0 x)).trans (by
      have := hhK x; rw [abs_of_nonneg (hh0 x)] at this; have := hh0 x; gcongr)
  have hdm : Measurable (gradSq g) := measurable_gradSq g
  have hdK : ∀ x, |gradSq g x| ≤ K₁ := fun x => by
    rw [abs_of_nonneg (gradSq_nonneg g x)]; exact hK₁ x
  -- integrability under `μ` and `ν`
  have hhμ : Integrable h μ := integrable_of_abs_le hhm.aestronglyMeasurable _ hhK
  have hhlμ : Integrable (fun x => h x * Real.log (h x)) μ :=
    integrable_of_abs_le (hhm.mul hhm.log).aestronglyMeasurable _ hhlK
  have hhν : Integrable h ν := integrable_of_abs_le hhm.aestronglyMeasurable _ hhK
  have hhlν : Integrable (fun x => h x * Real.log (h x)) ν :=
    integrable_of_abs_le (hhm.mul hhm.log).aestronglyMeasurable _ hhlK
  have hdμ : Integrable (gradSq g) μ := integrable_of_abs_le hdm.aestronglyMeasurable _ hdK
  have hρdμ : Integrable (fun x => ρ x * gradSq g x) μ :=
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
  have hLSI : ent μ h ≤ 2 * C * ∫ x, gradSq g x ∂μ := hμ g hg
  have hd_le : ∫ x, gradSq g x ∂μ ≤ (1 / m) * ∫ x, ρ x * gradSq g x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hdμ (hρdμ.const_mul _) fun x => ?_
    have h1 : m * gradSq g x ≤ ρ x * gradSq g x :=
      mul_le_mul_of_nonneg_right (hmρ x) (gradSq_nonneg g x)
    rw [← mul_assoc, one_div, ← div_eq_inv_mul, div_mul_eq_mul_div, le_div_iff₀ hm]
    linarith
  calc ent ν h ≤ ∫ x, psi s (h x) ∂ν := hνent
    _ = ∫ x, ρ x * psi s (h x) ∂μ := integral_withDensity_ofReal hρ hρ0 _
    _ ≤ ∫ x, M * psi s (h x) ∂μ :=
        integral_mono (hψμ.bdd_mul hρ.aestronglyMeasurable (ae_of_all _ hρabs))
          (hψμ.const_mul _) fun x => mul_le_mul_of_nonneg_right (hρM x) (hψ0 x)
    _ = M * ent μ h := by rw [integral_const_mul, hμent]
    _ ≤ M * (2 * C * ∫ x, gradSq g x ∂μ) := mul_le_mul_of_nonneg_left hLSI hM
    _ ≤ M * (2 * C * ((1 / m) * ∫ x, ρ x * gradSq g x ∂μ)) := by gcongr
    _ = 2 * (C * (M / m)) * ∫ x, gradSq g x ∂ν := by
        rw [hνdef, integral_withDensity_ofReal hρ hρ0]
        ring

/-- **Holley–Stroock perturbation lemma on `Fin d → ℝ`.** If `μ` is a probability measure with
`FunctionalLSIPi μ C`, `C ≥ 0`, and `W` is measurable with `a ≤ W ≤ b`, then the tilt
`ν = (e^{-W} / Z) · μ` (`HolleyStroock.tilt`) satisfies `FunctionalLSIPi ν (C · e^{b - a})`. -/
theorem functionalLSIPi_tilt {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {C : ℝ}
    (hμ : FunctionalLSIPi μ C) (hC : 0 ≤ C) {W : (Fin d → ℝ) → ℝ} (hW : Measurable W)
    {a b : ℝ} (ha : ∀ x, a ≤ W x) (hb : ∀ x, W x ≤ b) :
    FunctionalLSIPi (tilt μ W) (C * Real.exp (b - a)) := by
  obtain ⟨-, hZb, -⟩ := integrable_exp_neg_and_bounds (μ := μ) hW ha hb
  set Z := ∫ x, Real.exp (-W x) ∂μ with hZdef
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hZb
  have hP : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (Real.exp (-W x) / Z)) :=
    isProbabilityMeasure_tilt (μ := μ) hW ha hb
  have h := functionalLSIPi_withDensity hμ hC (ρ := fun x => Real.exp (-W x) / Z)
    ((Real.measurable_exp.comp hW.neg).div_const _) (m := Real.exp (-b) / Z)
    (M := Real.exp (-a) / Z) (by positivity)
    (fun x => div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hb x])) hZ.le)
    (fun x => div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [ha x])) hZ.le)
  have hr : Real.exp (-a) / Z / (Real.exp (-b) / Z) = Real.exp (b - a) := by
    rw [div_div_div_cancel_right₀ hZ.ne', ← Real.exp_sub]; ring_nf
  rw [hr] at h
  exact h

end HolleyStroock

/-! ### Bounded perturbations of the isotropic Gaussian target -/

section Target

open FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi
open FormalizeSampling.HolleyStroock (tilt)

/-- **Targets of perturbed potentials are tilts.** For measurable `f₀`, `W` on `Fin d → ℝ` with
`e^{-f₀}` Lebesgue-integrable, `targetPi (f₀ + W) = tilt (targetPi f₀) W`. -/
theorem targetPi_add_eq_tilt {f₀ W : (Fin d → ℝ) → ℝ} (hf₀ : Measurable f₀) (hW : Measurable W)
    (hint : Integrable (fun x => Real.exp (-f₀ x))) :
    targetPi (fun x => f₀ x + W x) = tilt (targetPi f₀) W := by
  have hZ₀ : 0 < targetNormalizerPi f₀ := targetNormalizerPi_pos hint
  have hZ' : ∫ y, Real.exp (-W y) ∂targetPi f₀ =
      targetNormalizerPi (fun x => f₀ x + W x) / targetNormalizerPi f₀ := by
    rw [targetPi, integral_withDensity_ofReal (measurable_targetDensityPi hf₀)
      (targetDensityPi_nonneg), targetNormalizerPi, ← integral_div]
    congr 1
    funext x
    rw [targetDensityPi, neg_add, Real.exp_add]
    ring
  have m₁ : Measurable fun x => ENNReal.ofReal (targetDensityPi f₀ x) :=
    (measurable_targetDensityPi hf₀).ennreal_ofReal
  have m₂ : Measurable fun x => ENNReal.ofReal (Real.exp (-W x) /
      (targetNormalizerPi (fun x => f₀ x + W x) / targetNormalizerPi f₀)) := by
    fun_prop
  rw [tilt, hZ', targetPi, targetPi, ← withDensity_mul _ m₁ m₂]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (targetDensityPi_nonneg x)]
  congr 1
  rw [targetDensityPi, targetDensityPi, neg_add, Real.exp_add]
  field_simp

/-- **Bounded perturbation of an isotropic Gaussian target.** For `α > 0` and measurable
`W : (Fin d → ℝ) → ℝ` with `a ≤ W ≤ b`, the target of `f(x) = α |x|²/2 + W(x)` satisfies
`FunctionalLSIPi (targetPi f) (e^{b - a} / α)`: it is the tilt of `N(0, I/α)` (Gross, constant
`1/α`) by `W`. -/
theorem functionalLSIPi_targetPi_gaussPotentialPi_add {α : ℝ} (hα : 0 < α)
    {W : (Fin d → ℝ) → ℝ} (hW : Measurable W) {a b : ℝ} (ha : ∀ x, a ≤ W x)
    (hb : ∀ x, W x ≤ b) :
    FunctionalLSIPi (targetPi fun x => gaussPotentialPi α x + W x) (Real.exp (b - a) / α) := by
  rw [targetPi_add_eq_tilt (measurable_gaussPotentialPi α) hW
    (integrable_exp_neg_gaussPotentialPi hα), targetPi_gaussPotentialPi hα, div_eq_inv_mul]
  exact functionalLSIPi_tilt (functionalLSIPi_gaussian α⁻¹ (inv_pos.2 hα))
    (inv_nonneg.2 hα.le) hW ha hb

end Target

end FormalizeSampling.GaussianFunctionalLSIPi
