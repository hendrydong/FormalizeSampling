module

public import Mathlib.Analysis.Real.Pi.Bounds
public import FormalizeSampling.Examples.NoiseScoreOUUnconditional
public import FormalizeSampling.Flow.FokkerPlanckUniqueness
public import FormalizeSampling.Flow.FokkerPlanckExistenceDissipative
public import FormalizeSampling.Flow.DiPernaLionsLinearGrowth
public import FormalizeSampling.Flow.ContinuityUniquenessLocal

/-!
# Statement audit: noise–score equivalence, weak Fokker–Planck and continuity equations

Rows: FL-5.

Non-vacuity witnesses for the headline statements of FL-5 (noise–score equivalence,
continuity-equation uniqueness, weak Fokker–Planck existence / uniqueness, DiPerna–Lions).
Each theorem below *applies* a headline theorem to a concrete instance and, where cheap,
shows that its conclusion is non-trivial.

## Main results

* `fl5_ou_nonstationary`: FL-5 (`map_flow_eq_ouLaw`) for `d = 1`, `a = 1`, `m = 1`, `v₀ = 1`
  at `t = 1`, together with the fact that the common law differs from the initial law (the
  instance is not stationary).
* `fp_existence_heat_nonconstant`: the existence theorem `exists_weakFokkerPlanck_measure`
  (drift `0`, `D = 1/2`, `ρ₀ = δ₀`) combined with uniqueness `eq_of_weakFokkerPlanck` and the
  heat solution `weakFokkerPlanck_heat`: the constructed solution satisfies `ρ 1 = N(0, 1)`,
  in particular `ρ 1 ≠ ρ 0`, so the existence theorem does not produce a degenerate curve.
* `fp_dissipative_doubleWell_applies`: the dissipative existence theorem applies to the
  double-well drift from any initial law (hypotheses are discharged by the repo itself).
* `uniqueWeakContinuity_sin`: `uniqueWeakContinuity_of_contDiff_linearGrowth` applied to the
  non-affine velocity `v(x)ᵢ = sin xᵢ`.
* `weakContinuityDensity_translate`, `dl_uniqueness_translate`: a non-stationary density
  solution (Gaussian translated at constant speed `c`) of `WeakContinuityDensity`, and the
  DiPerna–Lions theorem `ae_eq_of_weakContinuityDensity_diPernaLions` applied to it, with every
  hypothesis (`MemW11locBddDiv`, boundedness, probability densities) discharged.

## Not proved here

* No witness that the DiPerna–Lions theorems apply to a velocity that is **not** locally
  Lipschitz (the witness uses a constant velocity); constructing an explicit
  `W^{1,1}_loc \ W^{1,∞}_loc` field with bounded divergence is not attempted.
* No witness for the `L^p` and linear-growth DiPerna–Lions variants beyond the observation
  that their hypotheses are implied by those of the bounded witness.
* No non-constancy proof for the dissipative / time-dependent existence theorems (only that
  they apply); the heat witness shows non-constancy for the bounded Lipschitz existence theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real

namespace FormalizeSampling.Audit.FlowPDE

open FormalizeSampling.NoiseScore FormalizeSampling.NoiseScoreOUUnconditional
  FormalizeSampling.OULangevinDecayPi FormalizeSampling.HeatKernelPi

/-! ### FL-5 headline: a non-stationary instance -/

/-- Pushing a product of probability measures on `Fin 1 → ℝ` forward by evaluation at `0`
recovers the factor. -/
theorem map_eval_pi_fin_one (μ : Fin 1 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map (Function.eval 0) = μ 0 :=
  (measurePreserving_eval μ 0).map_eq

/-- **FL-5 witness (non-stationary).** For `d = 1`, rate `a = 1`, initial law `N(1, 1)`, the
probability-flow transport and the OU law agree at `t = 1` (`map_flow_eq_ouLaw`), and this law
is not the initial law (its mean is `e⁻¹ ≠ 1`), so the conclusion of FL-5 is non-trivial. -/
theorem fl5_ou_nonstationary :
    (initLaw (d := 1) (fun _ => 1) 1).map (flow 1 (fun _ => 1) 1 1) =
        ouKernelPi 1 1 ∘ₘ initLaw (d := 1) (fun _ => 1) 1 ∧
      ouKernelPi 1 1 ∘ₘ initLaw (d := 1) (fun _ => 1) 1 ≠ initLaw (fun _ => 1) 1 := by
  refine ⟨map_flow_eq_ouLaw (d := 1) zero_le_one one_pos _ 1 zero_le_one, fun h => ?_⟩
  have h1 : ouLaw (d := 1) 1 (fun _ => 1) 1 1 = initLaw (fun _ => 1) 1 := h
  rw [ouLaw_eq_pi zero_le_one zero_le_one zero_le_one, initLaw] at h1
  have h2 := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (Function.eval 0)) h1
  simp only [map_eval_pi_fin_one] at h2
  have h3 := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) h2
  simp only [integral_id_gaussianReal, meanAt] at h3
  have : Real.exp (-1 * 1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  linarith

/-! ### Fokker–Planck existence + uniqueness: the constructed curve is not constant -/

/-- **Existence witness (non-constant).** In dimension `1`, the curve given by
`exists_weakFokkerPlanck_measure` for drift `0`, `D = 1/2` and initial law `δ₀` is, by the
uniqueness theorem `eq_of_weakFokkerPlanck` and `weakFokkerPlanck_heat`, the heat curve; at
`t = 1` it is `N(0, 1)` and in particular differs from its initial law `δ₀`. -/
theorem fp_existence_heat_nonconstant :
    ∃ ρ : ℝ → Measure (Fin 1 → ℝ), ρ 0 = Measure.dirac 0 ∧
      (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ _ => 0) (1 / 2) ∧
      ρ 1 = Measure.pi (fun _ => gaussianReal 0 1) ∧ ρ 1 ≠ ρ 0 := by
  obtain ⟨ρ, h0, hprob, hFP⟩ := FokkerPlanckExistence.exists_weakFokkerPlanck_measure
    (b := fun _ : Fin 1 → ℝ => (0 : Fin 1 → ℝ)) (L := 0) (LipschitzWith.const 0)
    (B := 0) (fun _ => by simp) (D := 1 / 2) (by norm_num) (Measure.dirac 0)
  have hheat := WeakFokkerPlanckOU.weakFokkerPlanck_heat (Measure.dirac (0 : Fin 1 → ℝ))
  have huniq := FokkerPlanckUniqueness.eq_of_weakFokkerPlanck (B := 0) (by norm_num)
    (fun _ _ => continuous_const) (fun _ _ _ => by simp) (fun t _ => hprob t)
    (fun t _ => by infer_instance) hFP hheat
    (by simp [h0, heatKernelPi_zero, Measure.id_comp])
  have h1 : ρ 1 = Measure.pi (fun _ => gaussianReal 0 1) := by
    rw [huniq 1 zero_le_one]
    rw [Measure.dirac_bind (Kernel.measurable _), heatKernelPi_apply]
    simp
  refine ⟨ρ, h0, hprob, hFP, h1, fun h => ?_⟩
  rw [h1, h0] at h
  have h2 := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (Function.eval 0)) h
  simp only [map_eval_pi_fin_one] at h2
  have h3 := congrArg (fun μ : Measure ℝ => μ {0}) h2
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  simp at h3

/-- **Dissipative existence applies (double well).** For every `a`, `D > 0` and initial law,
`exists_weakFokkerPlanck_doubleWell` yields a weakly continuous probability solution of the
weak Fokker–Planck equation with the cubic drift `-∇U_a`; here instantiated at `d = 2`,
`a = 1`, `D = 1`, `ρ₀ = δ₀`. -/
theorem fp_dissipative_doubleWell_applies :
    ∃ ν : ℝ → ProbabilityMeasure (Fin 2 → ℝ),
      (ν 0 : Measure (Fin 2 → ℝ)) = Measure.dirac 0 ∧ Continuous ν ∧
      WeakFokkerPlanck (fun t => (ν t : Measure (Fin 2 → ℝ)))
        (fun _ x => -grad (FokkerPlanckExistence.doubleWell 1) x) 1 :=
  FokkerPlanckExistence.exists_weakFokkerPlanck_doubleWell 1 one_pos _

/-! ### Continuity-equation uniqueness for a non-affine velocity -/

/-- The coordinatewise sine field `x ↦ (sin xᵢ)ᵢ`. -/
noncomputable def sinField {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun i => Real.sin (x i)

/-- The sine field is smooth. -/
theorem contDiff_sinField {d : ℕ} : ContDiff ℝ ⊤ (sinField (d := d)) :=
  contDiff_pi.2 fun i => Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) i)

/-- **Uniqueness witness (non-affine velocity).** `uniqueWeakContinuity_of_contDiff_linearGrowth`
applies to the autonomous velocity `v(x)ᵢ = sin xᵢ`, which is neither affine nor of the form
covered by the explicit-flow theorems. -/
theorem uniqueWeakContinuity_sin {d : ℕ} :
    UniqueWeakContinuity (d := d) fun _ => sinField := by
  have hc : ContDiff ℝ 1 (sinField (d := d)) := contDiff_sinField.of_le (by simp)
  refine uniqueWeakContinuity_of_contDiff_linearGrowth (fun _ _ => hc.differentiable one_ne_zero)
    (hc.continuous.comp continuous_snd).continuousOn
    ((hc.continuous_fderiv one_ne_zero).comp continuous_snd).continuousOn
    fun T _ => ⟨1, fun t _ x => ?_⟩
  have h : ‖sinField x‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      simpa [sinField, Real.norm_eq_abs] using Real.abs_sin_le_one (x i)
  have : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

/-! ### DiPerna–Lions: a non-stationary density solution -/

/-- The standard Gaussian density on `ℝᵈ` is at most `1`. -/
theorem stdGaussianDensity_le_one {d : ℕ} (x : Fin d → ℝ) : stdGaussianDensity x ≤ 1 := by
  refine Finset.prod_le_one₀ (fun i _ => (gaussianPDFReal_pos 0 1 (x i) one_ne_zero).le)
    fun i _ => ?_
  rw [gaussianPDFReal_def]
  have h1 : Real.exp (-(x i - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := sq_nonneg (x i - 0); push_cast; linarith)
  have h2 : (1 : ℝ) ≤ √(2 * π * ((1 : ℝ≥0) : ℝ)) := by
    rw [Real.one_le_sqrt]; push_cast; nlinarith [Real.pi_gt_three]
  have h3 : (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
  have h4 : 0 ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ := by positivity
  calc _ ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h4
    _ ≤ 1 := by linarith

/-- The standard Gaussian density on `ℝᵈ` is a probability density (`IsProbDensity`). -/
theorem isProbDensity_stdGaussianDensity {d : ℕ} :
    IsProbDensity (stdGaussianDensity (d := d)) := by
  have hint : Integrable (stdGaussianDensity (d := d)) := by
    have h := Integrable.fintype_prod (ι := Fin d) (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ => gaussianPDFReal 0 1) fun _ => integrable_gaussianPDFReal 0 1
    rw [← volume_pi] at h
    exact h
  have hnn : 0 ≤ᵐ[volume] stdGaussianDensity (d := d) :=
    Eventually.of_forall fun x => (stdGaussianDensity_pos x).le
  refine ⟨hint, hnn, ?_⟩
  have hP := (isProbabilityMeasure_stdGaussian (d := d)).measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn] at hP
  exact (ENNReal.ofReal_eq_one).1 hP

/-- The Gaussian density translated at constant speed `c`: `u_t(x) = g(x - t c)`. -/
noncomputable def transGauss {d : ℕ} (c : Fin d → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  stdGaussianDensity (x - t • c)

/-- Translating a probability density gives a probability density. -/
theorem isProbDensity_transGauss {d : ℕ} (c : Fin d → ℝ) (t : ℝ) :
    IsProbDensity (transGauss c t) := by
  obtain ⟨hi, _, h1⟩ := isProbDensity_stdGaussianDensity (d := d)
  refine ⟨hi.comp_sub_right (t • c), Eventually.of_forall fun x => (stdGaussianDensity_pos _).le,
    ?_⟩
  rw [← h1]
  exact integral_sub_right_eq_self (μ := volume) (fun x => stdGaussianDensity x) (t • c)

/-- Integrals against the translated measure `(g dx) ∘ (· + t c)⁻¹` are integrals against
`transGauss c t`. -/
theorem integral_map_translate {d : ℕ} (c : Fin d → ℝ) (t : ℝ) (ψ : (Fin d → ℝ) → ℝ) :
    ∫ x, ψ x ∂((densityMeasure (stdGaussianDensity (d := d))).map fun x => x + t • c) =
      ∫ x, transGauss c t x * ψ x := by
  let e : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) := (Homeomorph.addRight (t • c)).toMeasurableEquiv
  have he : (fun x : Fin d → ℝ => x + t • c) = e := rfl
  rw [he, integral_map_equiv, densityMeasure,
    integral_withDensity_ofReal (contDiff_stdGaussianDensity.continuous.measurable)
      (fun x => (stdGaussianDensity_pos x).le)]
  rw [← integral_sub_right_eq_self (μ := volume) _ (t • c)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [e, transGauss, mul_comm]

/-- **Non-stationary solution of `WeakContinuityDensity` (Verified).** For any `c`, the
translated Gaussian `u_t(x) = g(x - t c)` solves the weak continuity equation for densities
with the constant velocity `v ≡ c`. -/
theorem weakContinuityDensity_translate {d : ℕ} (c : Fin d → ℝ) :
    WeakContinuityDensity (transGauss c) (fun _ => c) := by
  have hP := isProbabilityMeasure_densityMeasure (isProbDensity_stdGaussianDensity (d := d))
  have hW := weakContinuity2_flowLaw (v := fun _ _ => c) (Φ := fun s x => x + s • c)
    continuous_const (fun t x => by simpa using ((hasDerivAt_id t).smul_const c).const_add x)
    (ρ₀ := densityMeasure (stdGaussianDensity (d := d)))
    fun t => (by fun_prop : Measurable fun x : Fin d → ℝ => x + t • c).aemeasurable
  intro φ hφ t ht
  have h := hW φ hφ t ht
  simp only [ContinuityEquation.flowLaw, integral_map_translate] at h
  exact h

/-- **DiPerna–Lions witness (Verified).** `ae_eq_of_weakContinuityDensity_diPernaLions`
applies to the constant velocity `v ≡ c` with all hypotheses discharged, and forces every
uniformly bounded probability-density solution started from the Gaussian density to be the
translated Gaussian `g(· - t c)`: a non-trivial (non-stationary) conclusion. -/
theorem dl_uniqueness_translate {d : ℕ} (c : Fin d → ℝ) {u' : ℝ → (Fin d → ℝ) → ℝ}
    (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t)) {U : ℝ} (hU : ∀ t, 0 ≤ t → ∀ᵐ x, |u' t x| ≤ U)
    (h' : WeakContinuityDensity u' (fun _ => c))
    (h0 : u' 0 =ᵐ[volume] stdGaussianDensity) :
    ∀ t, 0 ≤ t → u' t =ᵐ[volume] transGauss c t := by
  have hv : MemW11locBddDiv (fun _ : Fin d → ℝ => c) := by
    refine ⟨fun x j i => partialDeriv i (fun _ : Fin d → ℝ => c j) x,
      fun j i => hasWeakPartialDeriv_of_contDiff contDiff_const i, 0,
      Eventually.of_forall fun x => ?_⟩
    simp [weakDiv, partialDeriv]
  have h0' : transGauss c 0 =ᵐ[volume] u' 0 := by
    refine EventuallyEq.trans (Eventually.of_forall fun x => ?_) h0.symm
    simp [transGauss]
  intro t ht
  refine (ae_eq_of_weakContinuityDensity_diPernaLions hv (V := ‖c‖)
    (Eventually.of_forall fun _ => le_rfl) (fun s _ => isProbDensity_transGauss c s) hu'
    (U := max U 1) (fun s _ => Eventually.of_forall fun x => ?_)
    (fun s hs => (hU s hs).mono fun x hx => hx.trans (le_max_left _ _))
    (weakContinuityDensity_translate c) h' h0' t ht).symm
  rw [transGauss, abs_of_pos (stdGaussianDensity_pos _)]
  exact (stdGaussianDensity_le_one _).trans (le_max_right _ _)

end FormalizeSampling.Audit.FlowPDE
