module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import FormalizeSampling.Samplers.Particles
public import FormalizeSampling.Examples.DiscreteGaussianFlow
public import FormalizeSampling.Examples.GaussianIncrementTight
public import FormalizeSampling.Examples.GaussianIncrementTightPi
public import FormalizeSampling.Samplers.ProximalSharpPi
public import FormalizeSampling.Counterexamples.MarginalsNotPaths
public import FormalizeSampling.Counterexamples.ScoreNotNoise
public import FormalizeSampling.Counterexamples.ULADiscretization
public import FormalizeSampling.Counterexamples.SteinSingleTest
public import FormalizeSampling.Counterexamples.ParticleVsPopulation
public import FormalizeSampling.Counterexamples.EmpiricalSteinUnbounded
public import FormalizeSampling.Kernels.ErrorDecomposition
public import FormalizeSampling.Flow.IdealVelocityStepPi
public import FormalizeSampling.Flow.DeterministicStepMoments
public import FormalizeSampling.Flow.DeterministicStepMomentsPi
public import FormalizeSampling.Foundations.HeatKernelPi
public import FormalizeSampling.Identities.GaussianStein
public import FormalizeSampling.Samplers.GaussianIncrementPi
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Statement audit: particles, deterministic steps, exact examples and counterexamples

Rows: PT-1, DT-1, EX-1, EX-2, EX-3, CE-01, CE-02, CE-03, CE-04, CE-05, CE-06, CE-07, CE-08.

Non-vacuity witnesses for these rows of `docs/theorem_registry.md`. Each theorem below
*applies* an audited headline theorem to a concrete, non-degenerate instance, discharging
every hypothesis; where useful it also shows that the conclusion is not trivial (finite and
nonzero KL, strictly negative dissipation rate, nonzero Fisher term).

## Main witnesses

* PT-1: `pt1_weakContinuityEquation_nonvacuous` (two particles, nonzero constant field).
* DT-1, dimension one: `dt1_idealVel_moment_instance`, `dt1_idealVel_explicit_instance`
  (`ρ = N(1,2)`, `π = N(0,1)`, `η = 1/4`, `L_U = 1`, `L_p = 1/2`), with `relFisher_instance`
  (`I = 3/2`), and `dt1_general_explicit_instance`, `dt1_general_moment_instance`
  (`v = -x/2`, `η L_v = 1/2`).
* DT-1, `Fin d → ℝ`: `gaussPi_hyps` (all shared hypotheses for `ρ = N(0,2I)`, `π = N(0,I)`),
  `dt1_idealVelPi_moment_instance` (constant `d (L_U+L_p)²`),
  `dt1_symmPi_moment_instance`, `dt1_generalPi_moment_instance` (`d = 1`).
* EX-1 `ex1_*`, EX-2 `ex2_*`, EX-3 `ex3_*`; counterexamples `ce0*_instance(s)`.

## Not proved here

* The `Fin d → ℝ` DT-1 theorems with *explicit* integrability hypotheses
  (`DeterministicStepPi.klDiv_map_step_le`,
  `DeterministicStepGeneral.klDiv_map_step_le(_of_mul_dim_le)`,
  `IdealVelocityStepPi.klDiv_map_step_idealVel_le`) are not instantiated directly; their
  moment forms are (and the moment forms are proved by deriving exactly those integrability
  hypotheses). The density-level statements (`integral_pushDensity_klIntegrand*`) are not
  instantiated separately (they share the hypotheses of the `klDiv` forms, which call them).
* The general-Jacobian `Fin d → ℝ` instance is given for `d = 1` only.
* For EX-3 the TV telescoping inequality is instantiated, but `tvSup > 0` of the instance is
  not proved (it is true since the two laws differ).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.Audit.StepsExamples

export FormalizeSampling.IdealVelocityStepPi (log_gaussianPDFPi
  differentiable_log_gaussianPDFReal score_gaussianPDFPi)

/-! ### Generic chain constructor (used for EX-3 witnesses) -/

/-- The Markov chain `ρ 0 = δ_{x₀}`, `ρ (k+1) = κ ∘ₘ ρ k` (a definitional witness for the
recursion hypotheses of the EX-3 theorems). -/
noncomputable def chainFrom {α : Type*} [MeasurableSpace α] (κ : Kernel α α) (ρ₀ : Measure α) :
    ℕ → Measure α
  | 0 => ρ₀
  | k + 1 => κ ∘ₘ chainFrom κ ρ₀ k

/-! ### PT-1 -/

/-- **PT-1 non-vacuity.** Two particles in `ℝ¹` moved by the nonzero constant field `c` along
the flow `Φ t y = y + t c`: the particle law solves the weak continuity equation. -/
theorem pt1_weakContinuityEquation_nonvacuous (c : Fin 1 → ℝ) (x : Fin 2 → (Fin 1 → ℝ)) :
    ContinuityEquation.WeakContinuityEquation
      (fun t => Particles.empirical (fun i => x i + t • c)) (fun _ _ => c) :=
  Particles.weakContinuityEquation_empirical_flow (Φ := fun t y => y + t • c) continuous_const
    (fun t y => by simpa using ((hasDerivAt_id t).smul_const c).const_add y) (by norm_num) x

/-! ### EX-1 -/

/-- **EX-1 non-vacuity (marginals vs two-time laws).** `a = t = 1`, `N(1, 2)` initial law. -/
theorem ex1_marginal_eq_and_twoTime_ne_instance :
    (gaussianReal 1 2).map (GaussianFlowVsOU.flow 1 1 2 1) =
        (gaussianReal 1 2).bind (OU.ouKernel 1 1) ∧
      (gaussianReal 1 2).map (fun y => (y, GaussianFlowVsOU.flow 1 1 2 1 y)) ≠
        (gaussianReal 1 2) ⊗ₘ OU.ouKernel 1 1 :=
  GaussianFlowVsOU.marginal_eq_and_twoTime_ne one_pos one_pos 1 two_ne_zero

/-- **EX-1 non-vacuity (KL dissipation).** For `a = 1`, initial law `N(1, 2)` and every
`t ≥ 0`, the hypotheses of `hasDerivAt_klDiv_flow` hold and the derivative of
`t ↦ KL(Φₜ # N(1,2) ‖ N(0,1))` is strictly negative (so the `toReal` is not a junk zero
derivative). -/
theorem ex1_hasDerivAt_klDiv_flow_neg {t : ℝ} (ht : 0 ≤ t) :
    ∃ r < 0, HasDerivAt (fun s => (klDiv ((gaussianReal 1 2).map
      (GaussianFlowVsOU.flow 1 1 2 s)) (gaussianReal 0 1)).toReal) r t := by
  have hvt := GaussianFlowVsOU.varAt_pos (a := 1) (v₀ := 2) zero_le_one two_ne_zero ht
  refine ⟨_, ?_, GaussianFlowVsOU.hasDerivAt_klDiv_flow two_ne_zero hvt⟩
  rw [GaussianFlowVsOU.integral_sq_scoreAt_sub_targetScore hvt]
  have h1 : 0 < GaussianFlowVsOU.meanAt 1 1 t ^ 2 := by
    unfold GaussianFlowVsOU.meanAt; positivity
  have h2 : 0 ≤ (GaussianFlowVsOU.varAt 1 2 t - 1) ^ 2 / GaussianFlowVsOU.varAt 1 2 t :=
    div_nonneg (sq_nonneg _) hvt.le
  linarith

/-! ### EX-2 -/

/-- **EX-2 non-vacuity.** `η = 1/2`, `h = 1`, target `N(0,1)`, initial `N(1,2)`
(`η = h σ⋆²/2`, the boundary of the step-size range): the KL bound holds with rate
`(1/2)^{2k}` and a finite nonzero constant `3/4`. -/
theorem ex2_klDiv_popLaw_le_instance (k : ℕ) :
    klDiv (DiscreteGaussianFlow.popLaw (1 / 2) 1 0 (1 : ℝ≥0) (gaussianReal 1 2) k)
        (gaussianReal 0 1) ≤ ENNReal.ofReal ((1 / 2) ^ (2 * k) * (3 / 4)) := by
  have := DiscreteGaussianFlow.klDiv_popLaw_le (η := 1 / 2) (h := 1) (σ2 := 1) (s2₀ := 2)
    (by norm_num) one_pos one_ne_zero (by norm_num) (by norm_num) 0 1 k
  convert this using 3
  · norm_num
  · simp only [NNReal.coe_one, NNReal.coe_ofNat]
    norm_num

/-- **EX-2 non-vacuity (variance gap).** Same instance: the relative gap contracts by
`1/2` per step. -/
theorem ex2_relGap_varSeq_le_instance (k : ℕ) :
    (DiscreteGaussianFlow.varSeq (1 / 2) 1 1 2 k - 1) / 1 ≤ (1 - (1 / 2) / (1 * 1)) ^ k *
      ((2 - 1) / 1) :=
  DiscreteGaussianFlow.relGap_varSeq_le (by norm_num) one_pos (by norm_num) one_pos
    (by norm_num) k

/-! ### EX-3 -/

/-- **EX-3 non-vacuity (GI-1 attained).** Exact drift `0`, estimated drift `1`, `h = 1`, both
chains from `δ₀`: after one step the KL is exactly `1/4 ≠ 0`. -/
theorem ex3_klDiv_const_chain_instance :
    klDiv (chainFrom (GaussianIncrement.emKernel 1 (fun _ => 1) measurable_const)
        (Measure.dirac 0) 1)
      (chainFrom (GaussianIncrement.emKernel 1 (fun _ => 0) measurable_const)
        (Measure.dirac 0) 1) = ENNReal.ofReal (1 / 4) ∧ ENNReal.ofReal (1 / 4) ≠ 0 := by
  refine ⟨?_, by simp⟩
  rw [GaussianIncrementTight.klDiv_const_chain 1 1 0 _ _ rfl rfl (fun _ => rfl)
    (fun _ => rfl) 1]
  norm_num

/-- **EX-3 non-vacuity (TV telescoping).** Same instance, any `n`. -/
theorem ex3_sqrt_mul_tvSup_le_telescoped_instance (n : ℕ) :
    Real.sqrt (2 * n / Real.pi) * TotalVariation.tvSup
        (chainFrom (GaussianIncrement.emKernel 1 (fun _ => 1) measurable_const)
          (Measure.dirac 0) n)
        (chainFrom (GaussianIncrement.emKernel 1 (fun _ => 0) measurable_const)
          (Measure.dirac 0) n) ≤
      n * (Real.sqrt (1 : ℝ≥0) / (2 * Real.sqrt Real.pi) * |(1 : ℝ)|) :=
  GaussianIncrementTight.sqrt_mul_tvSup_le_telescoped 1 1 0 _ _ rfl rfl (fun _ => rfl)
    (fun _ => rfl) n

/-- **EX-3 non-vacuity, `Fin 2 → ℝ`.** Drift error `Δ = (1, 1)`, `h = 1`: after one step
`KL = 1 · 1 · 2 / 4 = 1/2`. -/
theorem ex3_klDiv_const_chainPi_instance :
    klDiv (chainFrom (GaussianIncrement.emKernelPi (d := 2) 1 (fun _ => fun _ => 1)
        measurable_const) (Measure.dirac 0) 1)
      (chainFrom (GaussianIncrement.emKernelPi (d := 2) 1 (fun _ => 0) measurable_const)
        (Measure.dirac 0) 1) = ENNReal.ofReal (1 / 2) := by
  rw [GaussianIncrementTightPi.klDiv_const_chainPi 1 (fun _ => 1) 0 _ _ rfl rfl (fun _ => rfl)
    (fun _ => rfl) 1]
  norm_num

/-- **EX-3 non-vacuity, `Fin 2 → ℝ`, TV telescoping.** -/
theorem ex3_sqrt_mul_tvSup_le_telescopedPi_instance (n : ℕ) :
    Real.sqrt (2 * n / Real.pi) * TotalVariation.tvSup
        (chainFrom (GaussianIncrement.emKernelPi (d := 2) 1 (fun _ => fun _ => 1)
          measurable_const) (Measure.dirac 0) n)
        (chainFrom (GaussianIncrement.emKernelPi (d := 2) 1 (fun _ => 0) measurable_const)
          (Measure.dirac 0) n) ≤
      n * (Real.sqrt (1 : ℝ≥0) / (2 * Real.sqrt Real.pi) *
        Real.sqrt (∑ i : Fin 2, (fun _ => (1 : ℝ)) i ^ 2)) :=
  GaussianIncrementTightPiTV.sqrt_mul_tvSup_le_telescoped 1 (fun _ => 1) 0 _ _ rfl rfl
    (fun _ => rfl) (fun _ => rfl) n

/-- **EX-3 non-vacuity (proximal tightness).** `α = η = 1`, `ρ = N(1, 1)`: the one-step KL is
exactly `1/8 = KL(ρ‖π)/4`, and the forward-only rate `1/2` is strict. -/
theorem ex3_proximal_instance :
    klDiv (Proximal.proxKernel (ProximalSharp.gaussPotential 1) 1 ∘ₘ
        gaussianReal 1 ((1 : ℝ)⁻¹).toNNReal) (Proximal.target (ProximalSharp.gaussPotential 1))
      = ENNReal.ofReal (1 / 8) ∧
    (klDiv (Proximal.proxKernel (ProximalSharp.gaussPotential 1) 1 ∘ₘ
        gaussianReal 1 ((1 : ℝ)⁻¹).toNNReal)
        (Proximal.target (ProximalSharp.gaussPotential 1))).toReal
      < (klDiv (gaussianReal 1 ((1 : ℝ)⁻¹).toNNReal)
        (Proximal.target (ProximalSharp.gaussPotential 1))).toReal / (1 + 1 * 1) := by
  refine ⟨?_, ProximalSharp.toReal_klDiv_proxKernel_comp_gaussTarget_lt one_pos one_pos
    one_ne_zero⟩
  rw [(ProximalSharp.klDiv_proxKernel_comp_gaussTarget one_pos one_pos 1).2.1]
  norm_num

/-- **EX-3 non-vacuity (iterated proximal tightness).** The chain from `N(1,1)` exists and its
KL decays exactly by `4^{-k}`. -/
theorem ex3_proximal_iterate_instance (k : ℕ) :
    (klDiv (chainFrom (Proximal.proxKernel (ProximalSharp.gaussPotential 1) 1)
        (gaussianReal 1 ((1 : ℝ)⁻¹).toNNReal) k)
        (Proximal.target (ProximalSharp.gaussPotential 1))).toReal =
      (klDiv (gaussianReal 1 ((1 : ℝ)⁻¹).toNNReal)
        (Proximal.target (ProximalSharp.gaussPotential 1))).toReal / (1 + 1 * 1) ^ (2 * k) :=
  (ProximalSharp.klDiv_iterate_gaussTarget one_pos one_pos 1 _ rfl (fun _ => rfl) k).2

/-- **EX-3 non-vacuity (no better rate), dimension one and `Fin 2 → ℝ`.** -/
theorem ex3_not_exists_rate_lt_instances :
    (¬ ∃ c < 1 / (1 + 1 * 1 : ℝ) ^ 2, ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      klDiv ρ (Proximal.target (ProximalSharp.gaussPotential 1)) ≠ ∞ →
      (klDiv (Proximal.proxKernel (ProximalSharp.gaussPotential 1) 1 ∘ₘ ρ)
        (Proximal.target (ProximalSharp.gaussPotential 1))).toReal
        ≤ c * (klDiv ρ (Proximal.target (ProximalSharp.gaussPotential 1))).toReal) ∧
    (¬ ∃ c < 1 / (1 + 1 * 1 : ℝ) ^ 2, ∀ ρ : Measure (Fin 2 → ℝ), IsProbabilityMeasure ρ →
      klDiv ρ (ProximalPi.targetPi (ProximalSharpPi.gaussPotentialPi 1)) ≠ ∞ →
      (klDiv (ProximalPi.proxKernelPi (ProximalSharpPi.gaussPotentialPi 1) 1 ∘ₘ ρ)
        (ProximalPi.targetPi (ProximalSharpPi.gaussPotentialPi 1))).toReal
        ≤ c * (klDiv ρ (ProximalPi.targetPi (ProximalSharpPi.gaussPotentialPi 1))).toReal) :=
  ⟨ProximalSharp.not_exists_rate_lt one_pos one_pos,
    ProximalSharpPi.not_exists_rate_lt_pi two_pos one_pos one_pos⟩

/-- **EX-3 non-vacuity (`Fin 2 → ℝ` proximal KL).** `α = η = 1`, `ρ = N((1,1), I)`: the
one-step KL is `2/8 = 1/4`. -/
theorem ex3_proximalPi_instance :
    klDiv (ProximalPi.proxKernelPi (ProximalSharpPi.gaussPotentialPi 1) 1 ∘ₘ
        (Measure.pi fun _ : Fin 2 => gaussianReal 1 ((1 : ℝ)⁻¹).toNNReal))
        (ProximalPi.targetPi (ProximalSharpPi.gaussPotentialPi 1)) = ENNReal.ofReal (1 / 4) := by
  rw [(ProximalSharpPi.klDiv_proxKernelPi_comp_gaussTarget one_pos one_pos
    (fun _ : Fin 2 => (1 : ℝ))).2.1]
  norm_num

/-! ### Counterexamples -/

/-- **CE-01** (no hypotheses; restated). -/
theorem ce01_instance :
    (gaussianReal 0 1).map (fun z => (z, z)) ≠ (gaussianReal 0 1).prod (gaussianReal 0 1) :=
  Counterexamples.MarginalsNotPaths.gaussian_constPair_ne_indepPair


/-- **CE-04** (no hypotheses; restated). The witness is a genuine probability measure and all
integrals are finite sums, so no junk integral is involved. -/
theorem ce04_instance :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ ρ ≠ gaussianReal 0 1 ∧
      (∀ a b : ℝ, ∫ x, x * (a * x + b) ∂ρ = ∫ x, deriv (fun y => a * y + b) x ∂ρ) ∧
      ∫ x, x * x ^ 3 ∂ρ ≠ ∫ x, deriv (fun y : ℝ => y ^ 3) x ∂ρ :=
  Counterexamples.SteinSingleTest.single_stein_test_not_identifying

/-- **CE-02 non-vacuity.** Witness space `Ω = ℝ × ℝ`, `P = N(0,1) ⊗ N(0,1)`, `X = fst`,
`Z = snd` (independent by `indepFun_prod`), `σ = 1`. -/
theorem ce02_nonvacuous :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun ω : ℝ × ℝ => -ω.2 / 1) ≠
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun ω : ℝ × ℝ =>
        score1 (gaussianPDFReal 0 ⟨1 + (1 : ℝ) ^ 2, by positivity⟩) (ω.1 + 1 * ω.2)) :=
  Counterexamples.ScoreNotNoise.law_noiseTarget_ne_law_scoreOfNoisy
    (P := (gaussianReal 0 1).prod (gaussianReal 0 1)) (X := Prod.fst) (Z := Prod.snd)
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
    (by rw [Measure.map_fst_prod]; simp) (by rw [Measure.map_snd_prod]; simp) one_pos


/-- **CE-02 non-vacuity, a.s. form.** Same witness space as `ce02_nonvacuous`. -/
theorem ce02_ae_nonvacuous :
    ¬ ((fun ω : ℝ × ℝ => -ω.2 / 1) =ᵐ[(gaussianReal 0 1).prod (gaussianReal 0 1)]
      fun ω => score1 (gaussianPDFReal 0 ⟨1 + (1 : ℝ) ^ 2, by positivity⟩) (ω.1 + 1 * ω.2)) :=
  Counterexamples.ScoreNotNoise.not_noiseTarget_ae_eq_scoreOfNoisy
    (P := (gaussianReal 0 1).prod (gaussianReal 0 1)) (X := Prod.fst) (Z := Prod.snd)
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
    (by rw [Measure.map_fst_prod]; simp) (by rw [Measure.map_snd_prod]; simp) one_pos

/-- **CE-03 non-vacuity.** `h = 1` (bias) and `h = 1`, `τ = 1` (SGLD comparison); the SGLD
comparison is tied to the actual invariant law by `sgldStep_gaussianReal_eq_self_iff`. -/
theorem ce03_instances :
    ((gaussianReal 0 1).map (fun x => (1 - 1) * x)) ∗
        ((gaussianReal 0 1).map (fun z => Real.sqrt (2 * 1) * z)) ≠ gaussianReal 0 1 ∧
    (1 < 2 / (2 - 1 : ℝ) ∧ 2 / (2 - 1 : ℝ) < (2 + 1 * 1 ^ 2) / (2 - 1)) ∧
    Counterexamples.ULADiscretization.sgldStep 1 1 (gaussianReal 0 3) = gaussianReal 0 3 := by
  refine ⟨Counterexamples.ULADiscretization.ulaStep_standardGaussian_ne one_pos,
    Counterexamples.ULADiscretization.ula_invariantVar_lt_sgld_invariantVar one_pos
      one_lt_two one_ne_zero, ?_⟩
  rw [Counterexamples.ULADiscretization.sgldStep_gaussianReal_eq_self_iff one_pos one_lt_two]
  norm_num

/-- **CE-05 non-vacuity.** `d = n = 1`. -/
theorem ce05_instance (x : Fin 1 → (Fin 1 → ℝ)) :
    ¬ ∃ f : (Fin 1 → ℝ) → ℝ≥0∞,
      Counterexamples.ParticleVsPopulation.empirical x =
        (volume : Measure (Fin 1 → ℝ)).withDensity f :=
  Counterexamples.ParticleVsPopulation.empirical_has_no_density one_pos one_pos x

/-- **CE-06 non-vacuity.** `n = d = 1`, `H = 1`, zero target score. -/
theorem ce06_instance (y : Fin 1 → Fin 1 → ℝ) :
    ¬ ∃ W, ∀ V, FeatureClass.featureSteinObjective 1 y 0
        Counterexamples.EmpiricalSteinUnbounded.affineFeatures W ≤
      FeatureClass.featureSteinObjective 1 y 0
        Counterexamples.EmpiricalSteinUnbounded.affineFeatures V :=
  Counterexamples.EmpiricalSteinUnbounded.not_exists_minimiser one_pos le_rfl 1 y 0

/-- **CE-07 non-vacuity with a non-Dirac target.** `π = N(0,1)` is carried by `A = {1}ᶜ` and
`1 ∉ A`; the reset kernel is not a uniform TV contraction for any `ρ < 1`. -/
theorem ce07_instance {ρ : ℝ} (hρ : ρ < 1) :
    ¬ ErrorDecomposition.TVContraction
      (ErrorDecomposition.resetKernel (measurableSet_singleton (1 : ℝ)).compl
        (gaussianReal 0 1)) (gaussianReal 0 1) ρ := by
  have h1 : gaussianReal 0 1 ({1}ᶜᶜ : Set ℝ) = 0 := by
    rw [compl_compl]
    exact gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  exact ErrorDecomposition.not_tvContraction_resetKernel _ h1 (x := 1) (by simp) hρ

/-- **CE-08 non-vacuity.** Both negative results apply at `η = 1` (`d = 2` for the `Pi`
form). -/
theorem ce08_instances :
    (∃ s : ℝ≥0, s ≠ 0 ∧ 1 / 2 < (1 : ℝ) * |1 / (s : ℝ) - 1| ∧
      klDiv (gaussianReal 0 s) (gaussianReal 0 1) <
        klDiv ((gaussianReal 0 s).map (DeterministicStep.step 1
            (IdealVelocityStep.idealVel (fun x => x ^ 2 / 2) (gaussianPDFReal 0 s))))
          (gaussianReal 0 1)) ∧
    (∃ s : ℝ≥0, s ≠ 0 ∧ 1 / 2 < (1 : ℝ) * |1 / (s : ℝ) - 1| ∧
      klDiv (Measure.pi fun _ : Fin 2 => gaussianReal 0 s)
          (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) <
        klDiv ((Measure.pi fun _ : Fin 2 => gaussianReal 0 s).map
            (DeterministicStepPi.step 1 (IdealVelocityStepPi.idealVel
              IdealVelocityStepPi.stdPotential (IdealVelocityStepPi.gaussianPDFPi s))))
          (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) :=
  ⟨IdealVelocityStep.exists_klDiv_map_step_idealVel_gt one_pos,
    IdealVelocityStepPi.exists_klDiv_map_step_idealVel_gt two_pos one_pos⟩

/-! ### DT-1, dimension one -/

section OneDim

open DeterministicStep IdealVelocityStep


/-- `N(m, v)` is `volume.withDensity (ofReal ∘ gaussianPDFReal m v)` (`v ≠ 0`). -/
theorem withDensity_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal m v x)) = gaussianReal m v := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]

/-- The target `π = e^{-x²/2}/√(2π) dx` is `N(0, 1)`. -/
theorem withDensity_gibbs_std :
    (volume.withDensity fun x =>
      ENNReal.ofReal (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) =
      gaussianReal 0 1 := by
  rw [← gaussianPDFReal_zero_one_eq_gibbsDensity, withDensity_gaussianPDFReal 0 one_ne_zero]

/-- `deriv (gaussianPDFReal m v) = x ↦ -((x - m)/v) p(x)`. -/
theorem deriv_gaussianPDFReal_eq (m : ℝ) (v : ℝ≥0) :
    deriv (gaussianPDFReal m v) = fun x => -((x - m) / v) * gaussianPDFReal m v x :=
  funext fun x => (GaussianStein.hasDerivAt_gaussianPDFReal m v x).deriv

/-- The Gaussian density is differentiable. -/
theorem differentiable_gaussianPDFReal (m : ℝ) (v : ℝ≥0) :
    Differentiable ℝ (gaussianPDFReal m v) :=
  fun x => (GaussianStein.hasDerivAt_gaussianPDFReal m v x).differentiableAt

/-- The derivative of the Gaussian density is differentiable. -/
theorem differentiable_deriv_gaussianPDFReal (m : ℝ) (v : ℝ≥0) :
    Differentiable ℝ (deriv (gaussianPDFReal m v)) := by
  rw [deriv_gaussianPDFReal_eq]
  exact ((differentiable_id.sub_const m).div_const _).neg.mul
    (differentiable_gaussianPDFReal m v)

/-- The Gaussian score is affine. -/
theorem score1_gaussianPDFReal_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    score1 (gaussianPDFReal m v) = fun x => -(x - m) / v :=
  funext (score1_gaussianPDFReal m hv)

/-- `|(log p)''| = 1/v` for `p = N(m, v)`. -/
theorem abs_deriv_score1_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (z : ℝ) :
    |deriv (score1 (gaussianPDFReal m v)) z| ≤ 1 / v := by
  rw [score1_gaussianPDFReal_eq m hv]
  have h : HasDerivAt (fun x : ℝ => -(x - m) / v) (-1 / v) z := by
    simpa using ((hasDerivAt_id z).sub_const m).neg.div_const (v : ℝ)
  rw [h.deriv, neg_div, abs_neg, abs_of_nonneg (by positivity)]

/-- `U = x²/2` has `U' = id`. -/
theorem deriv_half_sq_eq : deriv (fun x : ℝ => x ^ 2 / 2) = fun x => x :=
  funext deriv_half_sq

/-- `U = x²/2` has `|U''| ≤ 1` (indeed `U'' = 1`). -/
theorem abs_deriv_deriv_half_sq (z : ℝ) : |deriv (deriv (fun x : ℝ => x ^ 2 / 2)) z| ≤ 1 := by
  rw [deriv_half_sq_eq, deriv_id'']
  simp

/-- Finite second moment of `N(m, v)` at the density level. -/
theorem integrable_sq_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable fun x => x ^ 2 * gaussianPDFReal m v x := by
  have h := (GaussianStein.integrable_gaussianReal_iff_integrable_pdf_mul
    (m := m) hv (f := fun x => x ^ 2)).1 (memLp_id_gaussianReal 2).integrable_sq
  simpa only [mul_comm] using h

/-- **DT-1 (ideal velocity, moment form) non-vacuity.** Target `π = N(0,1)` (`U = x²/2`,
`Z = √(2π)`, `L_U = 1`), current law `ρ = N(1, 2)` (`L_p = 1/2`), step `η = 1/4`
(`η (L_U + L_p) = 3/8 ≤ 1/2`); the ideal velocity is `v(x) = -(x + 1)/2`, a nontrivial affine
field. Every hypothesis of `DeterministicStepMoments.klDiv_map_step_idealVel_le` is
discharged, and in addition `KL(ρ‖π) = ofReal(...) ` is finite and nonzero. -/
theorem dt1_idealVel_moment_instance :
    let p := gaussianPDFReal 1 2
    let U := fun x : ℝ => x ^ 2 / 2
    let Z := Real.sqrt (2 * Real.pi)
    (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map (step (1 / 4) (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (p x)).map
        (step (1 / 4) (idealVel U p)))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x))).toReal -
        1 / 4 * (1 - 1 / 4 * 1 / 2) * relFisher U p + (1 / 4) ^ 2 * (1 + 1 / 2) ^ 2) ∧
    klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ 0 ∧
    klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ := by
  intro p U Z
  have hρ : (volume.withDensity fun x => ENNReal.ofReal (p x)) = gaussianReal 1 2 :=
    withDensity_gaussianPDFReal 1 two_ne_zero
  have hπ : (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) =
      gaussianReal 0 1 := withDensity_gibbs_std
  have hKLeq : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) =
      ENNReal.ofReal (((2 : ℝ≥0) + (1 : ℝ) ^ 2 - 1 - Real.log (2 : ℝ≥0)) / 2) := by
    rw [hρ, hπ, GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian 1 two_ne_zero]
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) := by
    rw [hρ]; infer_instance
  have : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) := by
    rw [hπ]; infer_instance
  have hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (gibbsDensity U Z x)) ≠ ∞ := by
    rw [hKLeq]; exact ENNReal.ofReal_ne_top
  have hmain := DeterministicStepMoments.klDiv_map_step_idealVel_le (η := 1 / 4) (LU := 1)
    (Lp := 1 / (2 : ℝ≥0)) (Z := Z) (U := U) (p := p) (by norm_num) (by norm_num)
    (Real.sqrt_pos.2 (by positivity)) (by fun_prop)
    (by rw [deriv_half_sq_eq]; exact differentiable_id) abs_deriv_deriv_half_sq
    (fun x => gaussianPDFReal_pos 1 2 x two_ne_zero) (measurable_gaussianPDFReal 1 2)
    (differentiable_gaussianPDFReal 1 2) (differentiable_deriv_gaussianPDFReal 1 2)
    (abs_deriv_score1_gaussianPDFReal 1 two_ne_zero) hKL
    (integrable_sq_mul_gaussianPDFReal 1 two_ne_zero)
  refine ⟨?_, ?_, hKL⟩
  · convert hmain using 4; norm_num
  · rw [hKLeq]
    have hlog : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    simp only [NNReal.coe_ofNat, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith

/-- **The first-order term is nonzero.** For the DT-1 instance (`ρ = N(1,2)`, `π = N(0,1)`),
the relative Fisher information is `I(ρ‖π) = 3/2`, so the bound of
`dt1_idealVel_moment_instance` reads `KL(T#ρ‖π) ≤ KL(ρ‖π) - 21/64 + 9/64`, a strict
decrease. -/
theorem relFisher_instance :
    relFisher (fun x : ℝ => x ^ 2 / 2) (gaussianPDFReal 1 2) = 3 / 2 := by
  have hs := score1_gaussianPDFReal_eq 1 (two_ne_zero (α := ℝ≥0))
  have h := GaussianFlowVsOU.integral_quadratic_gaussianReal 1 2 (1 / 4) 1 1
  rw [integral_gaussianReal_eq_integral_smul two_ne_zero] at h
  rw [relFisher]
  convert h using 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hs, deriv_half_sq_eq, NNReal.coe_ofNat, smul_eq_mul]
    ring
  · norm_num

/-- Polynomial moments of `N(1, 2)` at the density level. -/
theorem integrable_pdf_mul_poly (a b c : ℝ) :
    Integrable fun x => gaussianPDFReal 1 2 x * (a * x ^ 2 + b * x + c) := by
  have h := (GaussianStein.integrable_gaussianReal_iff_integrable_pdf_mul (m := 1)
    two_ne_zero).1 (GaussianFlowVsOU.integrable_quadratic_gaussianReal 1 2 a (2 * a + b)
      (a + b + c))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- The ideal velocity from `N(1, 2)` to `N(0, 1)` is `v(x) = -(x + 1)/2`. -/
theorem idealVel_instance :
    idealVel (fun x : ℝ => x ^ 2 / 2) (gaussianPDFReal 1 2) = fun x => -(x + 1) / 2 := by
  funext x
  rw [idealVel, deriv_half_sq, score1_gaussianPDFReal 1 two_ne_zero]
  norm_num
  ring

/-- The Gibbs density of `x²/2` is measurable and positive. -/
theorem gibbs_std_measurable_pos :
    Measurable (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi))) ∧
      ∀ x, 0 < gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x := by
  rw [← gaussianPDFReal_zero_one_eq_gibbsDensity]
  exact ⟨measurable_gaussianPDFReal 0 1, fun x => gaussianPDFReal_pos 0 1 x one_ne_zero⟩

/-- `KL(N(1,2) ‖ N(0,1)) < ∞` in the `withDensity` form used by DT-1. -/
theorem klDiv_instance_ne_top :
    klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x))
      (volume.withDensity fun x => ENNReal.ofReal
        (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) ≠ ∞ := by
  rw [withDensity_gaussianPDFReal 1 two_ne_zero, withDensity_gibbs_std,
    GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian 1 two_ne_zero]
  exact ENNReal.ofReal_ne_top

/-- **DT-1 (ideal velocity, explicit integrability) non-vacuity.** Same instance as
`dt1_idealVel_moment_instance` (`ρ = N(1,2)`, `π = N(0,1)`, `η = 1/4`, `L_U = 1`,
`L_p = 1/2`): all five integrability hypotheses of
`IdealVelocityStep.klDiv_map_step_idealVel_le` hold, so the theorem applies. -/
theorem dt1_idealVel_explicit_instance :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)).map
        (step (1 / 4) (idealVel (fun x : ℝ => x ^ 2 / 2) (gaussianPDFReal 1 2))))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)).map
        (step (1 / 4) (idealVel (fun x : ℝ => x ^ 2 / 2) (gaussianPDFReal 1 2))))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x))).toReal -
        1 / 4 * (1 - 1 / 4 * 1 / 2) *
          relFisher (fun x : ℝ => x ^ 2 / 2) (gaussianPDFReal 1 2) +
        (1 / 4) ^ 2 * (1 + 1 / (2 : ℝ≥0)) ^ 2 := by
  have hρ := withDensity_gaussianPDFReal 1 (two_ne_zero (α := ℝ≥0))
  have : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)) := by
    rw [hρ]; infer_instance
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal
      (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) := by
    rw [withDensity_gibbs_std]; infer_instance
  have hv := idealVel_instance
  have hs := score1_gaussianPDFReal_eq 1 (two_ne_zero (α := ℝ≥0))
  refine IdealVelocityStep.klDiv_map_step_idealVel_le (by norm_num) (by norm_num)
    (Real.sqrt_pos.2 (by positivity)) (by fun_prop)
    (by rw [deriv_half_sq_eq]; exact differentiable_id) abs_deriv_deriv_half_sq
    (fun x => gaussianPDFReal_pos 1 2 x two_ne_zero) (measurable_gaussianPDFReal 1 2)
    (differentiable_gaussianPDFReal 1 2) (differentiable_deriv_gaussianPDFReal 1 2)
    (abs_deriv_score1_gaussianPDFReal 1 two_ne_zero)
    (DeterministicStepMoments.integrable_klIntegrand_of_klDiv_ne_top
      (measurable_gaussianPDFReal 1 2) gibbs_std_measurable_pos.1
      (fun x => (gaussianPDFReal_pos 1 2 x two_ne_zero).le) gibbs_std_measurable_pos.2
      klDiv_instance_ne_top) ?_ ?_ ?_ ?_
  · refine (integrable_pdf_mul_poly (-15 / 128) (-14 / 128) (1 / 128)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hv, step]
    ring
  · refine (integrable_pdf_mul_poly (1 / 4) (1 / 2) (1 / 4)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hs, deriv_half_sq_eq, NNReal.coe_ofNat]
    ring
  · refine (integrable_pdf_mul_poly (1 / 4) 0 (-1 / 4)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hv, deriv_gaussianPDFReal_eq, NNReal.coe_ofNat]
    ring
  · refine (integrable_pdf_mul_poly 0 (-1 / 2) (-1 / 2)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hv]
    ring

/-- `v(x) = -x/2` is differentiable with `|v'| ≤ 1/2`. -/
theorem halfNeg_props :
    Differentiable ℝ (fun x : ℝ => -x / 2) ∧ ∀ x, |deriv (fun x : ℝ => -x / 2) x| ≤ 1 / 2 := by
  refine ⟨by fun_prop, fun x => ?_⟩
  have h : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) x := by
    simpa using (hasDerivAt_id x).neg.div_const 2
  rw [h.deriv]
  norm_num [abs_of_neg]

/-- **DT-1 (general velocity, 1D, explicit integrability) non-vacuity.** `ρ = N(1,2)`,
`π = N(0,1)` (`L = 1`), `v(x) = -x/2` (`L_v = 1/2`), `η = 1` (`η L_v = 1/2`, the boundary):
all hypotheses of `DeterministicStep.klDiv_map_step_le` hold. -/
theorem dt1_general_explicit_instance :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)).map
        (step 1 (fun x : ℝ => -x / 2)))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)).map
        (step 1 (fun x : ℝ => -x / 2)))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x))).toReal -
        1 * (∫ x, gaussianPDFReal 1 2 x * (deriv (fun x : ℝ => -x / 2) x -
          deriv (fun x : ℝ => x ^ 2 / 2) x * (-x / 2))) +
        1 ^ 2 * ∫ x, gaussianPDFReal 1 2 x * (deriv (fun x : ℝ => -x / 2) x ^ 2 +
          1 / 2 * (-x / 2) ^ 2) := by
  have hρ := withDensity_gaussianPDFReal 1 (two_ne_zero (α := ℝ≥0))
  have : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)) := by
    rw [hρ]; infer_instance
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal
      (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) := by
    rw [withDensity_gibbs_std]; infer_instance
  refine DeterministicStep.klDiv_map_step_le (L := 1) halfNeg_props.1 halfNeg_props.2
    zero_le_one (by norm_num) (fun x => gaussianPDFReal_pos 1 2 x two_ne_zero)
    (measurable_gaussianPDFReal 1 2) (Real.sqrt_pos.2 (by positivity)) (by fun_prop)
    (by rw [deriv_half_sq_eq]; exact differentiable_id)
    (fun z => (le_abs_self _).trans (abs_deriv_deriv_half_sq z))
    (DeterministicStepMoments.integrable_klIntegrand_of_klDiv_ne_top
      (measurable_gaussianPDFReal 1 2) gibbs_std_measurable_pos.1
      (fun x => (gaussianPDFReal_pos 1 2 x two_ne_zero).le) gibbs_std_measurable_pos.2
      klDiv_instance_ne_top) ?_ ?_ ?_
  · refine (integrable_pdf_mul_poly (-3 / 8) 0 0).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [step]
    ring
  · refine (integrable_pdf_mul_poly (-1 / 2) 0 0).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [deriv_half_sq_eq]
    ring
  · refine (integrable_pdf_mul_poly (1 / 4) 0 0).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring

/-- **DT-1 (general velocity, 1D, moment form) non-vacuity.** Same instance as
`dt1_general_explicit_instance`, with `M = 1`. -/
theorem dt1_general_moment_instance :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)).map
        (step 1 (fun x : ℝ => -x / 2)))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) ≠ ∞ := by
  have hρ := withDensity_gaussianPDFReal 1 (two_ne_zero (α := ℝ≥0))
  have : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 2 x)) := by
    rw [hρ]; infer_instance
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal
      (gibbsDensity (fun x : ℝ => x ^ 2 / 2) (Real.sqrt (2 * Real.pi)) x)) := by
    rw [withDensity_gibbs_std]; infer_instance
  exact (DeterministicStepMoments.klDiv_map_step_le (L := 1) (M := 1) halfNeg_props.1
    halfNeg_props.2 zero_le_one (by norm_num) (fun x => gaussianPDFReal_pos 1 2 x two_ne_zero)
    (measurable_gaussianPDFReal 1 2) (Real.sqrt_pos.2 (by positivity)) (by fun_prop)
    (by rw [deriv_half_sq_eq]; exact differentiable_id)
    (fun z => (le_abs_self _).trans (abs_deriv_deriv_half_sq z)) abs_deriv_deriv_half_sq
    klDiv_instance_ne_top (integrable_sq_mul_gaussianPDFReal 1 two_ne_zero)).1

end OneDim

/-! ### DT-1, `Fin d → ℝ` -/

section Pi

open Matrix DeterministicStepPi IdealVelocityStepPi

variable {d : ℕ}



/-- `N(0, sI)` on `Fin d → ℝ` is `volume.withDensity (ofReal ∘ gaussianPDFPi s)`. -/
theorem withDensity_gaussianPDFPi {s : ℝ≥0} (hs : s ≠ 0) :
    (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) s x)) =
      Measure.pi fun _ : Fin d => gaussianReal 0 s := by
  have h := MeasureHelpers.pi_withDensity_ofReal (d := d) (g := fun _ => gaussianPDFReal 0 s)
    (fun _ => integrable_gaussianPDFReal 0 s) (fun _ u => gaussianPDFReal_nonneg 0 s u)
  simp only [gaussianPDFPi]
  rw [← h]
  congr 1
  funext i
  rw [gaussianReal_of_var_ne_zero _ hs, gaussianPDF_def]

/-- The standard Gibbs measure on `Fin d → ℝ` is `N(0, I)`. -/
theorem withDensity_gibbs_stdPi :
    (volume.withDensity fun x => ENNReal.ofReal
      (gibbsDensity (stdPotential (d := d)) (Real.sqrt (2 * Real.pi) ^ d) x)) =
      Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  rw [← gaussianPDFPi_one_eq_gibbsDensity, withDensity_gaussianPDFPi one_ne_zero]

/-- The Gaussian product density is positive. -/
theorem gaussianPDFPi_pos {s : ℝ≥0} (hs : s ≠ 0) (x : Fin d → ℝ) : 0 < gaussianPDFPi s x :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 s (x i) hs

/-- The Gaussian product density is measurable. -/
theorem measurable_gaussianPDFPi' (s : ℝ≥0) : Measurable (gaussianPDFPi (d := d) s) :=
  Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 s).comp (measurable_pi_apply i)

/-- The Gaussian product density is differentiable. -/
theorem differentiable_gaussianPDFPi (s : ℝ≥0) : Differentiable ℝ (gaussianPDFPi (d := d) s) :=
  by
  have hg : Differentiable ℝ (gaussianPDFReal 0 s) :=
    fun x => (GaussianStein.hasDerivAt_gaussianPDFReal 0 s x).differentiableAt
  intro x
  classical
  have hgi : ∀ i, DifferentiableAt ℝ (fun y : Fin d → ℝ => gaussianPDFReal 0 s (y i)) x :=
    fun i => DifferentiableAt.comp (g := gaussianPDFReal 0 s) (f := fun y : Fin d → ℝ => y i) x
      (hg (x i)) (differentiableAt_apply (𝕜 := ℝ) i x)
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun (i : Fin d) (y : Fin d → ℝ) => gaussianPDFReal 0 s (y i))
    fun i _ => (hgi i).hasFDerivAt).differentiableAt

/-- `‖D(c • id)‖ ≤ |c|`. -/
theorem norm_fderiv_smul_id_le (c : ℝ) (z : Fin d → ℝ) :
    ‖fderiv ℝ (fun x : Fin d → ℝ => c • x) z‖ ≤ |c| := by
  have h : HasFDerivAt (fun x : Fin d → ℝ => c • x) (c • ContinuousLinearMap.id ℝ (Fin d → ℝ)) z :=
    (hasFDerivAt_id z).const_smul c
  rw [h.fderiv]
  refine (norm_smul_le c (ContinuousLinearMap.id ℝ (Fin d → ℝ))).trans ?_
  rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le

/-- `∇U₀ = id` for `U₀ = ‖x‖²/2`. -/
theorem grad_stdPotential : grad (stdPotential (d := d)) = fun x => (1 : ℝ) • x := by
  funext x
  have := grad_sum_comp (d := d) (f := fun t : ℝ => t ^ 2 / 2) (by fun_prop) x
  simp only [IdealVelocityStep.deriv_half_sq] at this
  simp only [one_smul]
  exact this

/-- `U₀ = ‖x‖²/2` is `C^∞`. -/
theorem contDiff_stdPotential : ContDiff ℝ 2 (stdPotential (d := d)) := by
  unfold stdPotential
  fun_prop


/-- Shared hypotheses of the `Fin d → ℝ` Gaussian instance (`ρ = N(0, 2I)`, `π = N(0, I)`):
probability measures, finite KL, finite second moment, regularity of `U₀` and `log p`. -/
theorem gaussPi_hyps :
    IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x)) ∧
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal
      (gibbsDensity (stdPotential (d := d)) (Real.sqrt (2 * Real.pi) ^ d) x)) ∧
    klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x))
      (volume.withDensity fun x => ENNReal.ofReal
        (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) x)) ≠ ∞ ∧
    (Integrable fun x : Fin d → ℝ => (x ⬝ᵥ x) * gaussianPDFPi 2 x) ∧
    Differentiable ℝ (stdPotential (d := d)) ∧ Differentiable ℝ (fderiv ℝ (stdPotential (d := d)))
    ∧ (∀ z, ‖fderiv ℝ (grad (stdPotential (d := d))) z‖ ≤ 1) ∧
    Differentiable ℝ (fderiv ℝ fun x => Real.log (gaussianPDFPi (d := d) 2 x)) ∧
    Differentiable ℝ (fun x => Real.log (gaussianPDFPi (d := d) 2 x)) ∧
    (∀ z, ‖fderiv ℝ (score (gaussianPDFPi (d := d) 2)) z‖ ≤ 1 / 2) := by
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  have hρ := withDensity_gaussianPDFPi (d := d) h2
  have hπ := withDensity_gibbs_stdPi (d := d)
  have hKL : klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x))
      (volume.withDensity fun x => ENNReal.ofReal
        (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) x)) ≠ ∞ := by
    rw [hρ, hπ, GaussianIncrement.klDiv_pi_pi]
    refine ENNReal.sum_ne_top.2 fun i _ => ?_
    rw [GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian 0 h2]
    exact ENNReal.ofReal_ne_top
  have hm : Integrable fun x : Fin d → ℝ => (x ⬝ᵥ x) * gaussianPDFPi 2 x := by
    have hpi : Integrable (fun x : Fin d → ℝ => x ⬝ᵥ x)
        (Measure.pi fun _ : Fin d => gaussianReal 0 (2 : ℝ≥0)) := by
      simp only [dotProduct]
      refine integrable_finsetSum _ fun i _ => ?_
      have hi := (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 (2 : ℝ≥0)) i)
      have hsq : Integrable (fun t : ℝ => t * t) (gaussianReal 0 (2 : ℝ≥0)) := by
        simpa only [pow_two, id_eq] using
          (memLp_id_gaussianReal (μ := 0) (v := 2) 2).integrable_sq
      exact (hi.integrable_comp hsq.aestronglyMeasurable).2 hsq
    rw [← hρ, integrable_withDensity_iff_integrable_smul'
      ((measurable_gaussianPDFPi' 2).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hpi
    refine hpi.congr (Filter.Eventually.of_forall fun x => ?_)
    show (ENNReal.ofReal (gaussianPDFPi 2 x)).toReal • (x ⬝ᵥ x) = (x ⬝ᵥ x) * gaussianPDFPi 2 x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (gaussianPDFPi_pos h2 x).le, mul_comm]
  have hcd : ContDiff ℝ 2 fun x => Real.log (gaussianPDFPi (d := d) 2 x) := by
    rw [log_gaussianPDFPi h2]
    simp only [GaussianFlowVsOU.log_gaussianPDFReal 0 h2]
    fun_prop
  refine ⟨by rw [hρ]; infer_instance, by rw [hπ]; infer_instance, hKL, hm,
    contDiff_stdPotential.differentiable (by norm_num),
    (contDiff_stdPotential.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num),
    fun z => by rw [grad_stdPotential]; simpa using norm_fderiv_smul_id_le (d := d) 1 z,
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num),
    hcd.differentiable (by norm_num), fun z => ?_⟩
  rw [score_gaussianPDFPi h2]
  refine (norm_fderiv_smul_id_le _ z).trans ?_
  norm_num [abs_of_neg]

/-- **DT-1 (`Fin d → ℝ`, symmetric Jacobian, moment form) non-vacuity.** `ρ = N(0, 2I)`,
`π = N(0, I)` (`L = M = 1`), `v` = the ideal velocity `-x/2` (symmetric Jacobian,
`‖Dv‖ ≤ L_v = 3/2` via `norm_fderiv_idealVel_le`), `η = 1/4`: every hypothesis of
`DeterministicStepMomentsPi.klDiv_map_step_le` is discharged; we record the finiteness part. -/
theorem dt1_symmPi_moment_instance :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x)).map
        (step (1 / 4) (idealVel stdPotential (gaussianPDFPi 2))))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) x)) ≠ ∞ := by
  obtain ⟨hρ, hπ, hKL, hm, hU, hU', hUH, hℓ', hℓ, hsH⟩ := gaussPi_hyps (d := d)
  have hv' : ∀ x, ‖fderiv ℝ (idealVel (stdPotential (d := d)) (gaussianPDFPi 2)) x‖ ≤ 1 + 1 / 2 :=
    norm_fderiv_idealVel_le hU' hℓ' hUH hsH
  exact (DeterministicStepMomentsPi.klDiv_map_step_le (L := 1) (M := 1)
    (differentiable_idealVel hU' hℓ') hv' (by norm_num) (by norm_num)
    (isSymm_jacMat_idealVel hU hU' hℓ hℓ') (gaussianPDFPi_pos two_ne_zero)
    (measurable_gaussianPDFPi' 2) (by positivity) hU hU'
    (fderiv_fderiv_apply_le hU hU' hUH) hUH hKL hm).1

/-- **DT-1 (`Fin 1 → ℝ`, general Jacobian, moment form) non-vacuity.** Same instance with
`d = 1`, where `η² ‖Dv‖_F² ≤ (1/16)(9/4) ≤ 1/4` holds (`frobSq_le_mul_dim`): every hypothesis
of `DeterministicStepMomentsPi.klDiv_map_step_le_general` is discharged. -/
theorem dt1_generalPi_moment_instance :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := 1) 2 x)).map
        (step (1 / 4) (idealVel stdPotential (gaussianPDFPi 2))))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ 1) x)) ≠ ∞ := by
  obtain ⟨hρ, hπ, hKL, hm, hU, hU', hUH, hℓ', hℓ, hsH⟩ := gaussPi_hyps (d := 1)
  have hv' : ∀ x, ‖fderiv ℝ (idealVel (stdPotential (d := 1)) (gaussianPDFPi 2)) x‖ ≤ 1 + 1 / 2 :=
    norm_fderiv_idealVel_le hU' hℓ' hUH hsH
  have hF : ∀ x, (1 / 4 : ℝ) ^ 2 *
      frobSq (jacMat (idealVel (stdPotential (d := 1)) (gaussianPDFPi 2)) x) ≤ 1 / 4 := by
    intro x
    have h := DeterministicStepPi.frobSq_le_mul_dim
      (A := jacMat (idealVel (stdPotential (d := 1)) (gaussianPDFPi 2)) x) (L := 1 + 1 / 2)
      fun w => by
        rw [jacMat_mulVec]
        exact ((fderiv ℝ _ x).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hv' x) (norm_nonneg w))
    norm_num at h ⊢
    linarith
  exact (DeterministicStepMomentsPi.klDiv_map_step_le_general (L := 1) (M := 1)
    (differentiable_idealVel hU' hℓ') hv' (by norm_num) (by norm_num) hF
    (gaussianPDFPi_pos two_ne_zero) (measurable_gaussianPDFPi' 2) (by positivity) hU hU'
    (fderiv_fderiv_apply_le hU hU' hUH) hUH hKL hm).1

/-- **DT-1 (ideal velocity, `Fin d → ℝ`, `d`-linear constant, moment form) non-vacuity.** Target
`N(0, I)` (`U₀ = ‖x‖²/2`, `Z = (2π)^{d/2}`, `L_U = 1`), current law `N(0, 2I)` (`L_p = 1/2`),
`η = 1/4`; the ideal velocity is `-x/2`. Every hypothesis of
`DeterministicStepMomentsPi.klDiv_map_step_idealVel_le` is discharged (any `d`; the instance
is non-degenerate for `d ≥ 1`), so its conclusion holds. -/
theorem dt1_idealVelPi_moment_instance :
    klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x)).map
        (step (1 / 4) (idealVel stdPotential (gaussianPDFPi 2))))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) x)) ≠ ∞ ∧
      (klDiv ((volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x)).map
        (step (1 / 4) (idealVel stdPotential (gaussianPDFPi 2))))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) x))).toReal ≤
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFPi (d := d) 2 x))
        (volume.withDensity fun x => ENNReal.ofReal
          (gibbsDensity stdPotential (Real.sqrt (2 * Real.pi) ^ d) x))).toReal -
        1 / 4 * (1 - 1 / 4 * 1 / 2) * relFisher (d := d) stdPotential (gaussianPDFPi 2) +
        (1 / 4) ^ 2 * (d * (1 + 1 / 2) ^ 2) := by
  obtain ⟨hρ, hπ, hKL, hm, hU, hU', hUH, hℓ', -, hsH⟩ := gaussPi_hyps (d := d)
  exact DeterministicStepMomentsPi.klDiv_map_step_idealVel_le (by norm_num) (by norm_num)
    (by positivity) hU hU' hUH (gaussianPDFPi_pos two_ne_zero) (measurable_gaussianPDFPi' 2)
    (differentiable_gaussianPDFPi 2) hℓ' hsH hKL hm

end Pi

end FormalizeSampling.Audit.StepsExamples
