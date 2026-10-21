module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Real.Pi.Bounds
public import FormalizeSampling.ScoreEstimation.SteinObjective
public import FormalizeSampling.Identities.Tweedie
public import FormalizeSampling.Identities.ScorePropagation
public import FormalizeSampling.Identities.OUPosteriorScore
public import FormalizeSampling.ScoreEstimation.MonteCarlo
public import FormalizeSampling.Kernels.ErrorDecomposition
public import FormalizeSampling.Kernels.ReverseKernel
public import FormalizeSampling.ScoreEstimation.InnerSamplerAveraged
public import FormalizeSampling.Samplers.MALA
public import FormalizeSampling.Samplers.RandomScoreOracleInner

/-!
# Statement audit `EstimationChains`: non-vacuity witnesses

Registry rows SE-1, SE-2, SE-3, SE-4, KR-1, KR-2, GI-1, GI-2, MH-1 of
`docs/theorem_registry.md`. Each theorem below **applies** a headline theorem of the row to a
concrete, non-degenerate instance and discharges every hypothesis; where cheap, it also shows
the conclusion is non-trivial. A summary is in `docs/statement_audit.md`.

* SE-1: `se1_isMinOn_iff` (`p = exp(-x₀²)`, `H = 1`, non-equilibrium `sStar = ∇log p + G`,
  `v⋆ = G ≠ 0`).
* SE-2: `se2_svgd_isMinimiser`, `se2_normalEq_isMinimiser`, `se2_pop_iff` (`μ = N(0, 1)`),
  `se2_projection` (projection form with the SE-1 density).
* SE-3: `se3_tweedie`, `se3_tweedie_pi`, `se3_channel`, `se3_ou` (Gaussian priors).
* SE-4: `se4_moments` (two i.i.d. `N(0, 1)` draws; MSE `1/2`, Chebyshev bound `1/2`).
* KR-1: `kr1_chain` (bound `1/√(2π) < 1`), `kr1_averaged` (law-averaged and three-chain forms).
* KR-2: `kr2_reverse` (Gaussian AR(1) forward kernel), `kr2_density`.
* GI-1: `gi1_tv`, `gi1Pi_tv` (initial `KL = 1/2 ≠ 0`, bound `√(1/4 + n/8)`).
* GI-2: `gi2_monteCarlo` (exact Monte Carlo oracle), `gi2_coupling` (biased inner sampler with
  squared bias `1`, `gi2Post_mean`), `gi2_tight`.
* MH-1: `mh1_invariant` (random-walk MH for `N(0, 1)`), `mh1_mala` (MALA on `Fin 2 → ℝ`).

## Not proved here

* No witness for the sub-Gaussian vector hypothesis `hsub` of
  `InnerSamplerBias.tvSup_biasedMonteCarloChain_le_sqrt_of_klDiv` and of the averaged-KL
  variant on `Fin d → ℝ` (only the scalar Gaussian case `gi2_tight`); the coupling route is
  witnessed instead.
* The GI-2 witnesses use a **state-independent** posterior; the state-dependent case
  (`KernelPi.piConst`, `Samplers/RandomScoreOracleKernel`) has no separate witness here.
* No closed-form evaluation of the Tweedie / OU posterior means for the Gaussian prior (the
  SE-3 witnesses only show the hypotheses hold and the density is positive).
* The KR-2 density witness uses a Dirac reference measure (the audited statement is the
  defining identity of `reverseDensity`, so a richer witness adds nothing).
-/

@[expose] public section

open MeasureTheory
open Matrix

namespace FormalizeSampling.Audit.EstimationChains

section SE1

open SteinObjective KLDecay

/-- Log-density `φ(x) = -x₀²` on `Fin 1 → ℝ`. -/
noncomputable def se1Phi (x : Fin 1 → ℝ) : ℝ := -(x 0 ^ 2)

/-- The (unnormalised) Gaussian density `p = exp φ`. -/
noncomputable def se1P (x : Fin 1 → ℝ) : ℝ := Real.exp (se1Phi x)

/-- A smooth bump equal to `1` on the unit ball and supported in the ball of radius `2`. -/
noncomputable def se1Bump : ContDiffBump (0 : Fin 1 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The compactly supported field `G(x) = (bump(x))`. -/
noncomputable def se1G (x : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => se1Bump x

/-- The target score field `sStar = ∇log p + G`, so that `v⋆ = G ≠ 0`. -/
noncomputable def se1SStar (x : Fin 1 → ℝ) : Fin 1 → ℝ := score se1P x + se1G x

/-- `φ` is `C¹`. -/
theorem se1Phi_contDiff : ContDiff ℝ 1 se1Phi := by
  unfold se1Phi; fun_prop

/-- `p = exp φ` is `C¹`. -/
theorem se1P_contDiff : ContDiff ℝ 1 se1P := by
  unfold se1P; exact Real.contDiff_exp.comp se1Phi_contDiff

/-- The score of `p = exp φ` is the gradient of `φ`. -/
theorem score_se1P : score se1P = fun x i => partialDeriv i se1Phi x := by
  funext x i
  simp [score, grad, se1P, Real.log_exp]

/-- The target score field `sStar` is continuous. -/
theorem se1SStar_continuous : Continuous se1SStar := by
  have h1 : Continuous (score se1P) := by
    rw [score_se1P]
    exact continuous_pi fun i => continuous_partialDeriv se1Phi_contDiff i
  have h2 : Continuous se1G := continuous_pi fun _ => se1Bump.continuous
  exact h1.add h2

/-- The ideal velocity of the SE-1 witness is `v⋆ = H⁻¹(sStar - ∇log p) = G`. -/
theorem se1_idealVelocity : idealVelocity 1 (score se1P) se1SStar = se1G := by
  funext x
  simp [idealVelocity, se1SStar]

/-- The ideal velocity of the SE-1 witness is not the zero field: `v⋆(0) = (1)`. -/
theorem se1G_ne_zero : se1G 0 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [se1G, Pi.zero_apply] at this
  rw [se1Bump.one_of_mem_closedBall (by simp [se1Bump])] at this
  exact one_ne_zero this

/-- `G` is admissible (compactly supported `C¹` field). -/
theorem se1G_admissible : Admissible 1 se1P se1SStar se1G :=
  admissible_of_hasCompactSupport 1 se1P_contDiff se1SStar_continuous
    (fun _ => se1Bump.contDiff) (fun _ => se1Bump.hasCompactSupport)

/-- Finite relative Fisher information for the SE-1 witness. -/
theorem se1_fisher_integrable :
    Integrable (fun x => sqNormH 1 (idealVelocity 1 (score se1P) se1SStar x) * se1P x) := by
  rw [se1_idealVelocity]
  have he : (fun x => sqNormH 1 (se1G x) * se1P x) = fun x => se1Bump x * (se1Bump x * se1P x) := by
    funext x; simp [sqNormH, se1G, dotProduct]; ring
  rw [he]
  exact (se1Bump.continuous.mul (se1Bump.continuous.mul se1P_contDiff.continuous))
    |>.integrable_of_hasCompactSupport se1Bump.hasCompactSupport.mul_right

/-- **SE-1 non-vacuity (non-equilibrium case).** For `p(x) = exp(-x₀²)` on `Fin 1 → ℝ`,
`H = 1`, `sStar = ∇log p + G` with `G` a nonzero smooth bump field, and `F` the set of all
admissible fields, every hypothesis of `isMinOn_iff_ae_eq_idealVelocity` holds, the ideal
velocity `v⋆ = G` is nonzero, and the minimisers over `F` are exactly the fields `= G` a.e. -/
theorem se1_isMinOn_iff (g : (Fin 1 → ℝ) → Fin 1 → ℝ)
    (hg : g ∈ {f | Admissible 1 se1P se1SStar f}) :
    se1G 0 ≠ 0 ∧ (IsMinOn (steinObjective 1 se1P se1SStar) {f | Admissible 1 se1P se1SStar f} g
      ↔ g =ᵐ[volume] se1G) := by
  refine ⟨se1G_ne_zero, ?_⟩
  have h := isMinOn_iff_ae_eq_idealVelocity (p := se1P)
    (F := {f | Admissible 1 se1P se1SStar f}) (Matrix.PosDef.one) (fun x => Real.exp_pos _)
    (se1P_contDiff.differentiable one_ne_zero) se1_fisher_integrable (fun f hf => hf)
    (by rw [se1_idealVelocity]; exact se1G_admissible) hg
  rwa [se1_idealVelocity] at h

end SE1

section SE2

open FeatureClass

/-- Constant feature map `ψ ≡ (1)` on `Fin 1 → ℝ`. -/
def se2Psi (_ : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => 1

/-- One particle at the origin. -/
def se2Y : Fin 1 → Fin 1 → ℝ := fun _ => 0

/-- The constant feature has identity empirical second-moment matrix on one particle. -/
theorem se2_featureCov : featureCov se2Y se2Psi = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [featureCov, se2Psi, vecMulVec]

/-- **SE-2 non-vacuity (SVGD as a special case of PFG).** With one particle, the constant
feature (so `Σψ = 1`), `λ = 1`, `H = 1 • 1` and the target score `sStar x = -x`, all
hypotheses of `featureStein_isMinimiser_iff_eq_svgdMatrix` hold and the SVGD matrix is a
global minimiser of the empirical PFG objective. -/
theorem se2_svgd_isMinimiser :
    ∀ V, featureSteinObjective ((1 : ℝ) • 1) se2Y (fun x => -x) se2Psi
        (svgdMatrix 1 se2Y (fun x => -x) se2Psi) ≤
      featureSteinObjective ((1 : ℝ) • 1) se2Y (fun x => -x) se2Psi V :=
  (featureStein_isMinimiser_iff_eq_svgdMatrix one_pos se2Y (fun x => -x) se2Psi
    (fun _ _ => differentiableAt_const _) se2_featureCov rfl _).2 rfl

/-- **SE-2 non-vacuity (normal equations are solvable).** In the same instance, with
`H = 1` (positive semidefinite), the SVGD matrix solves the normal equations, so
`featureStein_isMinimiser_iff_normalEq` yields an actual minimiser. -/
theorem se2_normalEq_isMinimiser :
    ∀ V, featureSteinObjective 1 se2Y (fun x => -x) se2Psi
        (svgdMatrix 1 se2Y (fun x => -x) se2Psi) ≤
      featureSteinObjective 1 se2Y (fun x => -x) se2Psi V := by
  refine (featureStein_isMinimiser_iff_normalEq Matrix.PosSemidef.one se2Y (fun x => -x) se2Psi
    (fun _ _ => differentiableAt_const _) _).2 ?_
  exact svgdMatrix_normalEq one_ne_zero se2Y (fun x => -x) se2Psi se2_featureCov
    (one_smul ℝ (1 : Matrix (Fin 1) (Fin 1) ℝ)).symm

/-- The standard Gaussian on `Fin 1 → ℝ`. -/
noncomputable def stdGauss1 : Measure (Fin 1 → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

/-- Instance needed to apply the audited theorem. -/
instance : IsProbabilityMeasure stdGauss1 := by unfold stdGauss1; infer_instance

/-- Coordinates are integrable under the standard Gaussian on `Fin 1 → ℝ`. -/
theorem integrable_coord_stdGauss1 (i : Fin 1) :
    Integrable (fun x : Fin 1 → ℝ => x i) stdGauss1 :=
  ((measurePreserving_eval (fun _ : Fin 1 => ProbabilityTheory.gaussianReal 0 1) i).integrable_comp
    (g := id) aestronglyMeasurable_id).2
    ((ProbabilityTheory.memLp_id_gaussianReal 1).integrable le_rfl)

/-- **SE-2 non-vacuity (population form).** For `μ = N(0, 1)` on `Fin 1 → ℝ`, the constant
feature, `H = 1` and `sStar x = -x`, all hypotheses of `popStein_isMinimiser_iff_normalEq`
hold. -/
theorem se2_pop_iff (W : Matrix (Fin 1) (Fin 1) ℝ) :
    (∀ V, popSteinObjective 1 stdGauss1 (fun x => -x) se2Psi W ≤
        popSteinObjective 1 stdGauss1 (fun x => -x) se2Psi V) ↔
      1 * W * popFeatureCov stdGauss1 se2Psi = popSteinMatrix stdGauss1 (fun x => -x) se2Psi := by
  refine popStein_isMinimiser_iff_normalEq Matrix.PosSemidef.one _ _
    (ae_of_all _ fun _ _ => differentiableAt_const _) (fun i k => ?_) (fun k l => ?_) W
  · refine ((integrable_coord_stdGauss1 i).neg).congr (ae_of_all _ fun x => ?_)
    simp [partialDeriv]
    exact (mul_one (x i)).symm
  · exact (integrable_const (1 : ℝ)).congr (ae_of_all _ fun x => (mul_one (1 : ℝ)).symm)

/-- **SE-2 non-vacuity (projection form).** For the SE-1 witness density `p = exp(-x₀²)`,
`H = 1`, the non-equilibrium target score `sStar = ∇log p + G` and the single compactly
supported feature `ψ = bump`, every hypothesis of `featureField_isMinimiser_iff_projection`
holds. -/
theorem se2_projection (W : Matrix (Fin 1) (Fin 1) ℝ) :
    (∀ V : Matrix (Fin 1) (Fin 1) ℝ,
        SteinObjective.steinObjective 1 se1P se1SStar (fun x => W *ᵥ (fun _ => se1Bump x)) ≤
        SteinObjective.steinObjective 1 se1P se1SStar (fun x => V *ᵥ (fun _ => se1Bump x))) ↔
      W * popFeatureCov (KLDecay.densityMeasure se1P) (fun x _ => se1Bump x) =
        Matrix.of fun i k => ∫ x, KLDecay.idealVelocity 1 (score se1P) se1SStar x i *
          (fun (x : Fin 1 → ℝ) (_ : Fin 1) => se1Bump x) x k * se1P x := by
  have hb : ContDiff ℝ 1 (se1Bump : (Fin 1 → ℝ) → ℝ) := se1Bump.contDiff
  have hbc := se1Bump.hasCompactSupport
  have hpc := se1P_contDiff.continuous
  have hsc : ∀ i, Continuous fun x => se1SStar x i :=
    fun i => (continuous_apply i).comp se1SStar_continuous
  exact SteinObjective.featureField_isMinimiser_iff_projection Matrix.PosDef.one
    (fun x => Real.exp_pos _) (se1P_contDiff.differentiable one_ne_zero) se1SStar
    (fun x _ => se1Bump x) (fun _ => hb.differentiable one_ne_zero)
    (fun i _ => ((continuous_partialDeriv hb i).mul hpc)
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_partialDeriv hbc i).mul_right)
    (fun i _ => (se1Bump.continuous.mul (continuous_partialDeriv se1P_contDiff i))
      |>.integrable_of_hasCompactSupport hbc.mul_right)
    (fun _ => (se1Bump.continuous.mul hpc).integrable_of_hasCompactSupport hbc.mul_right)
    (fun i _ => (((hsc i).mul se1Bump.continuous).mul hpc).integrable_of_hasCompactSupport
      (hbc.mul_left).mul_right)
    (fun _ _ => ((se1Bump.continuous.mul se1Bump.continuous).mul hpc)
      |>.integrable_of_hasCompactSupport hbc.mul_right.mul_right) W

end SE2

section SE3

open ProbabilityTheory

/-- **SE-3 non-vacuity (Tweedie, 1D).** `tweedie` applies to the non-degenerate prior
`N(0, 1)` with noise level `σ = 1`; the smoothed density is positive (so the score is the
genuine `p'/p`, not a junk value). -/
theorem se3_tweedie (y : ℝ) :
    0 < Tweedie.smoothedDensity (gaussianReal 0 1) 1 y ∧
      score1 (Tweedie.smoothedDensity (gaussianReal 0 1) 1) y =
        (Tweedie.posteriorMean (gaussianReal 0 1) 1 y - y) / 1 ^ 2 :=
  ⟨Tweedie.smoothedDensity_pos _ one_ne_zero y, Tweedie.tweedie _ one_ne_zero y⟩

/-- **SE-3 non-vacuity (Tweedie, `d`-dimensional).** `tweedie_pi` applies to `N(0, I)` on
`Fin 1 → ℝ` with `σ = 1`, and the smoothed density is positive. -/
theorem se3_tweedie_pi (y : Fin 1 → ℝ) :
    0 < Tweedie.piSmoothedDensity stdGauss1 1 y ∧
      score (Tweedie.piSmoothedDensity stdGauss1 1) y =
        fun i => (Tweedie.piPosteriorMean stdGauss1 1 y i - y i) / 1 ^ 2 :=
  ⟨Tweedie.piSmoothedDensity_pos _ one_ne_zero y, Tweedie.tweedie_pi _ one_ne_zero y⟩

/-- **SE-3 non-vacuity (Gaussian channel).** The Gaussian prior density `N(0, 1)` is
nonnegative and integrable with positive integral (fields of `RegularPrior`), so
`score1_channelDensity_tweedie` applies with `a = 2`, `σ = 1`. -/
theorem se3_channel (y : ℝ) :
    score1 (ScorePropagation.channelDensity (Tweedie.gaussKernel 1 0) 2 1) y =
      (2 * ScorePropagation.posteriorExpect (Tweedie.gaussKernel 1 0) 2 1 (fun x => x) y - y) /
        1 ^ 2 :=
  have hq := ScorePropagation.regularPrior_gaussKernel one_ne_zero 0
  ScorePropagation.score1_channelDensity_tweedie hq.nonneg hq.integrable hq.integral_pos
    two_ne_zero one_ne_zero y

/-- **SE-3 non-vacuity (OU posterior score).** `ouPosteriorScore` and `ouPosteriorScore_pi`
apply to the prior `N(0, 1)` (resp. `N(0, I)` on `Fin 1 → ℝ`) at time `s = 1`. -/
theorem se3_ou (y : ℝ) (z : Fin 1 → ℝ) :
    score1 (OUPosterior.ouDensity (gaussianReal 0 1) 1) y =
        (Real.exp (-1) * OUPosterior.affinePosteriorMean (gaussianReal 0 1) (Real.exp (-1))
          (Real.sqrt (1 - Real.exp (-2 * 1))) y - y) / (1 - Real.exp (-2 * 1)) ∧
      score (OUPosterior.piOUDensity stdGauss1 1) z =
        (1 - Real.exp (-2 * 1))⁻¹ • (Real.exp (-1) • OUPosterior.piAffinePosteriorMean stdGauss1
          (Real.exp (-1)) (Real.sqrt (1 - Real.exp (-2 * 1))) z - z) :=
  ⟨OUPosterior.ouPosteriorScore _ one_pos y, OUPosterior.ouPosteriorScore_pi _ one_pos z⟩

end SE3

section SE4

open ProbabilityTheory MonteCarlo

/-- Two i.i.d. standard Gaussian coordinates. -/
noncomputable def se4P : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- Instance needed to apply the audited theorem. -/
instance : IsProbabilityMeasure se4P := by unfold se4P; infer_instance

/-- Each coordinate has law `N(0, 1)` under `se4P`. -/
theorem se4_hasLaw (i : Fin 2) : HasLaw (fun ω : Fin 2 → ℝ => ω i) (gaussianReal 0 1) se4P :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).map_eq⟩

/-- The coordinates are mutually independent under `se4P`. -/
theorem se4_iIndep : iIndepFun (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i) se4P :=
  iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id

/-- **SE-4 non-vacuity (MSE and Chebyshev).** For `n = 2` i.i.d. `N(0, 1)` draws, all
hypotheses of `integral_sq_scoreEstimate_sub` and `meas_abs_scoreEstimate_sub_ge_le` hold;
with `a = s2 = ε = 1` the MSE is `1/2` and the Chebyshev bound is `1/2` (not `0`, not `≥ 1`). -/
theorem se4_moments (y : ℝ) :
    ∫ ω, (scoreEstimate 1 y 1 (fun i ω => ω i) ω - (1 * 0 - y) / 1) ^ 2 ∂se4P = 1 / 2 ∧
      se4P {ω | 1 ≤ |scoreEstimate 1 y 1 (fun i ω => ω i) ω - (1 * 0 - y) / 1|} ≤
        ENNReal.ofReal (1 / 2) := by
  have hX : ∀ i : Fin 2, MemLp (fun ω : Fin 2 → ℝ => ω i) 2 se4P :=
    fun i => memLp_of_hasLaw (memLp_id_gaussianReal 2) (se4_hasLaw i)
  have hind : Pairwise fun i j : Fin 2 =>
      IndepFun (fun ω : Fin 2 → ℝ => ω i) (fun ω => ω j) se4P :=
    fun _ _ hij => se4_iIndep.indepFun hij
  have hm : ∀ i : Fin 2, ∫ ω, ω i ∂se4P = 0 := fun i => by
    rw [(se4_hasLaw i).integral_eq, integral_id_gaussianReal]
  have hv : ∀ i : Fin 2, variance (fun ω : Fin 2 → ℝ => ω i) se4P = 1 := fun i => by
    rw [(se4_hasLaw i).variance_eq, variance_id_gaussianReal]; simp
  refine ⟨?_, ?_⟩
  · rw [integral_sq_scoreEstimate_sub two_pos 1 y 1 hX hind hm hv]; norm_num
  · refine (meas_abs_scoreEstimate_sub_ge_le two_pos 1 y 1 hX hind hm hv one_pos).trans_eq ?_
    norm_num

end SE4

section KR1

open ProbabilityTheory TotalVariation ErrorPropagation ReverseKernel

/-- The constant Markov kernel `x ↦ N(m, 1)` on `ℝ`. -/
noncomputable def kr1K (m : ℝ) : Kernel ℝ ℝ := Kernel.const ℝ (gaussianReal m 1)

/-- Instance needed to apply the audited theorem. -/
instance (m : ℝ) : IsMarkovKernel (kr1K m) := by unfold kr1K; infer_instance

/-- The chain driven by `kr1K m` from `N(0, 1)`. -/
noncomputable def kr1Chain (m : ℝ) : ℕ → Measure ℝ :=
  forwardMarginal (fun _ => kr1K m) (gaussianReal 0 1)

/-- Instance needed to apply the audited theorem. -/
instance (m : ℝ) : IsProbabilityMeasure (kr1Chain m 0) := by
  simp only [kr1Chain, forwardMarginal_zero]; infer_instance

/-- The one-step kernel error `tvSup (N(a, 1)) (N(b, 1)) ≤ |a - b| / √(2π)`. -/
theorem kr1_err (a b : ℝ) (x : ℝ) :
    tvSup (kr1K a x) (kr1K b x) ≤ |a - b| / Real.sqrt (2 * Real.pi) := by
  simpa [kr1K] using GaussianIncrement.tvSup_gaussianReal_le a b one_ne_zero

/-- **KR-1 non-vacuity (uniform telescoping).** For the chains driven by `N(0, 1)` and
`N(1, 1)` from the same start, `tvSup_chain_le_sum` gives after one step the nontrivial bound
`tvSup ≤ 1/√(2π) < 1`. -/
theorem kr1_chain :
    tvSup (kr1Chain 0 1) (kr1Chain 1 1) ≤ 1 / Real.sqrt (2 * Real.pi) ∧
      1 / Real.sqrt (2 * Real.pi) < 1 := by
  refine ⟨?_, ?_⟩
  · have h := tvSup_chain_le_sum (μ := kr1Chain 0) (ν := kr1Chain 1)
      (fun n => forwardMarginal_succ _ _ n) (fun n => forwardMarginal_succ _ _ n)
      (ε := fun _ => |(0 : ℝ) - 1| / Real.sqrt (2 * Real.pi)) (fun _ x => kr1_err 0 1 x) 1
    simpa [kr1Chain, tvSup_self] using h
  · rw [div_lt_one (by positivity), Real.lt_sqrt zero_le_one]
    nlinarith [Real.pi_gt_three]

/-- **KR-1 non-vacuity (law-averaged forms and three-chain split).** The hypotheses of
`tvSup_chain_le_sum_integral_approx`, `tvSup_chain_le_sum_integral_exact` and
`ErrorDecomposition.tvSup_le_three_chain` hold for the Gaussian constant-kernel chains
(exact `N(0, 1)`, ideal `N(1, 1)`, implemented `N(2, 1)`) with constant integrable
majorants. -/
theorem kr1_averaged (n : ℕ) :
    tvSup (kr1Chain 0 n) (kr1Chain 1 n) ≤ tvSup (kr1Chain 0 0) (kr1Chain 1 0) +
        ∑ k ∈ Finset.range n, ∫ _x, 1 / Real.sqrt (2 * Real.pi) ∂(kr1Chain 1 k) ∧
    tvSup (kr1Chain 0 n) (kr1Chain 1 n) ≤ tvSup (kr1Chain 0 0) (kr1Chain 1 0) +
        ∑ k ∈ Finset.range n, ∫ _x, 1 / Real.sqrt (2 * Real.pi) ∂(kr1Chain 0 k) ∧
    tvSup (kr1Chain 2 n) (kr1Chain 0 n) ≤ tvSup (kr1Chain 2 0) (kr1Chain 1 0) +
        tvSup (kr1Chain 1 0) (kr1Chain 0 0) +
        ∑ k ∈ Finset.range n, ∫ _x, 1 / Real.sqrt (2 * Real.pi) ∂(kr1Chain 1 k) +
        ∑ k ∈ Finset.range n, ∫ _x, 1 / Real.sqrt (2 * Real.pi) ∂(kr1Chain 2 k) := by
  have hs : ∀ m, ∀ k, kr1Chain m (k + 1) = kr1K m ∘ₘ kr1Chain m k :=
    fun m k => forwardMarginal_succ _ _ k
  have hp : ∀ m k, IsProbabilityMeasure (kr1Chain m k) := fun m k =>
    isProbabilityMeasure_of_comp_succ (hs m) k
  have e01 : ∀ x, tvSup (kr1K 0 x) (kr1K 1 x) ≤ 1 / Real.sqrt (2 * Real.pi) := fun x => by
    simpa using kr1_err 0 1 x
  have e10 : ∀ x, tvSup (kr1K 1 x) (kr1K 0 x) ≤ 1 / Real.sqrt (2 * Real.pi) := fun x => by
    simpa using kr1_err 1 0 x
  have e21 : ∀ x, tvSup (kr1K 2 x) (kr1K 1 x) ≤ 1 / Real.sqrt (2 * Real.pi) := fun x => by
    have h := kr1_err 2 1 x
    norm_num at h ⊢
    simpa [mul_comm] using h
  refine ⟨?_, ?_, ?_⟩
  · exact tvSup_chain_le_sum_integral_approx (hs 0) (hs 1) (fun _ => integrable_const _)
      (fun _ => ae_of_all _ e01) n
  · exact tvSup_chain_le_sum_integral_exact (hs 0) (hs 1) (fun _ => integrable_const _)
      (fun _ => ae_of_all _ e01) n
  · exact ErrorDecomposition.tvSup_le_three_chain (K := fun _ => kr1K 0) (D := fun _ => kr1K 1)
      (I := fun _ => kr1K 2) (hs 0) (hs 1) (hs 2) (fun _ => integrable_const _)
      (fun _ => ae_of_all _ e10) (fun _ => integrable_const _) (fun _ => ae_of_all _ e21) n

end KR1

section KR2

open ProbabilityTheory ReverseKernel

/-- The non-trivial forward Markov kernel `x ↦ N(-x/2, 1)` on `ℝ`. -/
noncomputable def kr2K : Kernel ℝ ℝ :=
  GaussianIncrement.emKernel (1 / 2) (fun x => -x) measurable_neg

/-- Instance needed to apply the audited theorem. -/
instance : IsMarkovKernel kr2K := GaussianIncrement.isMarkovKernel_emKernel _ _

/-- **KR-2 non-vacuity.** For the forward chain `x ↦ N(x - x/2, 1)` from `N(0, 1)` on the
standard Borel space `ℝ`, the posterior is a reverse kernel, every reverse kernel equals it
a.e., and the `n`-step reverse chain maps the time-`n` marginal back to `N(0, 1)`. -/
theorem kr2_reverse (n : ℕ) :
    IsReverseKernel kr2K (gaussianReal 0 1) (kr2K†(gaussianReal 0 1)) ∧
      (IsReverseKernel kr2K (gaussianReal 0 1) (kr2K†(gaussianReal 0 1)) ↔
        kr2K†(gaussianReal 0 1) =ᵐ[kr2K ∘ₘ gaussianReal 0 1] kr2K†(gaussianReal 0 1)) ∧
      reverseChain (fun _ => kr2K) (gaussianReal 0 1) n ∘ₘ
          forwardMarginal (fun _ => kr2K) (gaussianReal 0 1) n = gaussianReal 0 1 :=
  ⟨isReverseKernel_posterior _ _, isReverseKernel_iff_ae_eq_posterior,
    reverseChain_comp_forwardMarginal _ _ n⟩

/-- **KR-2 density form: hypotheses satisfiable.** With the Dirac reference measure and unit
densities, `0 < m(y) < ∞` holds, so `joint_density_eq_mul_reverseDensity` applies (the
statement itself is the defining identity `r = p k / m` rearranged). -/
theorem kr2_density (x y : ℝ) :
    marginalDensity (Measure.dirac (0 : ℝ)) (fun _ => 1) (fun _ _ => (1 : ENNReal)) y = 1 ∧
      (fun _ : ℝ => (1 : ENNReal)) x * (fun _ _ : ℝ => (1 : ENNReal)) x y =
        marginalDensity (Measure.dirac (0 : ℝ)) (fun _ => 1) (fun _ _ => 1) y *
          reverseDensity (Measure.dirac (0 : ℝ)) (fun _ => 1) (fun _ _ => 1) y x := by
  have hm : marginalDensity (Measure.dirac (0 : ℝ)) (fun _ => 1) (fun _ _ => (1 : ENNReal)) y
      = 1 := by simp [marginalDensity]
  exact ⟨hm, joint_density_eq_mul_reverseDensity y x (by rw [hm]; exact one_ne_zero)
    (by rw [hm]; exact ENNReal.one_ne_top)⟩

end KR2

section GI1

open ProbabilityTheory InformationTheory TotalVariation ReverseKernel GaussianIncrement
open scoped NNReal

/-- The 1D EM chain with step `1` and constant drift `c` started from `N(m, 1)`. -/
noncomputable def gi1Chain (c m : ℝ) : ℕ → Measure ℝ :=
  forwardMarginal (fun _ => emKernel 1 (fun _ => c) measurable_const) (gaussianReal m 1)

/-- Instance needed to apply the audited theorem. -/
instance (c m : ℝ) : IsProbabilityMeasure (gi1Chain c m 0) := by
  simp only [gi1Chain, forwardMarginal_zero]; infer_instance

/-- **GI-1 (1D) non-vacuity.** Exact drift `0` from `N(0, 1)`, estimated drift `1` from
`N(1, 1)`, step `1`: `KL(ν₀ ‖ μ₀) = 1/2` is finite and nonzero, all hypotheses of
`tvSup_emChain_le_sqrt_sum_integral_sq` hold, and the bound is `√(1/4 + n/8)`. -/
theorem gi1_tv (n : ℕ) :
    klDiv (gi1Chain 1 1 0) (gi1Chain 0 0 0) = ENNReal.ofReal (1 / 2) ∧
      tvSup (gi1Chain 1 1 n) (gi1Chain 0 0 n) ≤ Real.sqrt (1 / 4 + n / 8) := by
  have hKL : klDiv (gi1Chain 1 1 0) (gi1Chain 0 0 0) = ENNReal.ofReal (1 / 2) := by
    simp only [gi1Chain, forwardMarginal_zero]
    rw [klDiv_gaussianReal_gaussianReal 1 0 one_ne_zero]; norm_num
  have hs : ∀ c m k, gi1Chain c m (k + 1) =
      emKernel 1 (fun _ => c) measurable_const ∘ₘ gi1Chain c m k :=
    fun c m k => forwardMarginal_succ _ _ k
  have hp : ∀ k, IsProbabilityMeasure (gi1Chain 1 1 k) := fun k =>
    haveI := isMarkovKernel_emKernel (1 : ℝ≥0) (s := fun _ : ℝ => (1 : ℝ)) measurable_const
    ErrorPropagation.isProbabilityMeasure_of_comp_succ (κ := fun _ => _) (hs 1 1) k
  refine ⟨hKL, ?_⟩
  have h := tvSup_emChain_le_sqrt_sum_integral_sq (h := fun _ => 1) (s := fun _ _ => 0)
    (ŝ := fun _ _ => 1) (hs := fun _ => measurable_const) (hŝ := fun _ => measurable_const)
    (hs 0 0) (hs 1 1) n (by rw [hKL]; exact ENNReal.ofReal_ne_top)
    (fun _ => integrable_const _)
  refine h.trans_eq (congrArg Real.sqrt ?_)
  rw [hKL]
  simp [probReal_univ]
  ring

/-- The isotropic EM chain on `Fin 1 → ℝ` with step `1` and constant drift `c`, from
`N(m, I)`. -/
noncomputable def gi1PiChain (c m : ℝ) : ℕ → Measure (Fin 1 → ℝ) :=
  forwardMarginal (fun _ => emKernelPi 1 (fun _ _ => c) measurable_const)
    (Measure.pi fun _ => gaussianReal m 1)

/-- Instance needed to apply the audited theorem. -/
instance (c m : ℝ) : IsProbabilityMeasure (gi1PiChain c m 0) := by
  simp only [gi1PiChain, forwardMarginal_zero]; infer_instance

/-- **GI-1 (`Fin d → ℝ`) non-vacuity.** The `d = 1` analogue of `gi1_tv` for
`tvSup_emChainPi_le_sqrt_sum_integral_sq`: finite nonzero initial KL and bound `√(1/4 + n/8)`. -/
theorem gi1Pi_tv (n : ℕ) :
    klDiv (gi1PiChain 1 1 0) (gi1PiChain 0 0 0) = ENNReal.ofReal (1 / 2) ∧
      tvSup (gi1PiChain 1 1 n) (gi1PiChain 0 0 n) ≤ Real.sqrt (1 / 4 + n / 8) := by
  have hKL : klDiv (gi1PiChain 1 1 0) (gi1PiChain 0 0 0) = ENNReal.ofReal (1 / 2) := by
    simp only [gi1PiChain, forwardMarginal_zero]
    rw [klDiv_pi_gaussianReal (fun _ => 1) (fun _ => 0) one_ne_zero]; norm_num
  have hs : ∀ c m k, gi1PiChain c m (k + 1) =
      emKernelPi 1 (fun _ _ => c) measurable_const ∘ₘ gi1PiChain c m k :=
    fun c m k => forwardMarginal_succ _ _ k
  have hp : ∀ k, IsProbabilityMeasure (gi1PiChain 1 1 k) := fun k =>
    haveI := isMarkovKernel_emKernelPi (1 : ℝ≥0)
      (b := fun (_ : Fin 1 → ℝ) (_ : Fin 1) => (1 : ℝ)) measurable_const
    ErrorPropagation.isProbabilityMeasure_of_comp_succ (κ := fun _ => _) (hs 1 1) k
  refine ⟨hKL, ?_⟩
  have h := tvSup_emChainPi_le_sqrt_sum_integral_sq (h := fun _ => 1) (s := fun _ _ _ => 0)
    (ŝ := fun _ _ _ => 1) (hs := fun _ => measurable_const) (hŝ := fun _ => measurable_const)
    (hs 0 0) (hs 1 1) n (by rw [hKL]; exact ENNReal.ofReal_ne_top)
    (fun _ => integrable_const _)
  refine h.trans_eq (congrArg Real.sqrt ?_)
  rw [hKL]
  simp [probReal_univ]
  ring

end GI1

section GI2

open ProbabilityTheory InformationTheory TotalVariation ReverseKernel GaussianIncrement
open scoped NNReal

/-- Each coordinate has law `N(0, 1)` under `stdGauss1`. -/
theorem stdGauss1_hasLaw (i : Fin 1) :
    HasLaw (fun y : Fin 1 → ℝ => y i) (gaussianReal 0 1) stdGauss1 :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) i).map_eq⟩

/-- `N = 1` draws: the draw space `Fin 1 → Fin 1 → ℝ` with law `stdGauss1^{⊗1}`. -/
noncomputable def gi2R : Kernel (Fin 1 → ℝ) (Fin 1 → Fin 1 → ℝ) :=
  Kernel.const _ (Measure.pi fun _ : Fin 1 => stdGauss1)

/-- Instance needed to apply the audited theorem. -/
instance : IsMarkovKernel gi2R := by unfold gi2R; infer_instance

/-- The plug-in drift `b̂(x, ω) = 0 + 1 • (m̂(ω) - 0)` (exact drift `0`, posterior mean `0`). -/
noncomputable def gi2Bhat (p : (Fin 1 → ℝ) × (Fin 1 → Fin 1 → ℝ)) : Fin 1 → ℝ := empMean p.2

/-- The plug-in drift is measurable. -/
theorem gi2Bhat_measurable : Measurable gi2Bhat := by
  have : Continuous gi2Bhat := by unfold gi2Bhat empMean; fun_prop
  exact this.measurable

/-- The exact-drift chain (drift `0`) from `N(0, I)` on `Fin 1 → ℝ`. -/
noncomputable def gi2Mu : ℕ → Measure (Fin 1 → ℝ) :=
  forwardMarginal (fun _ => emKernelPi 1 (fun _ _ => 0) measurable_const) stdGauss1

/-- The random-oracle chain from `N(1, I)` with draws `gi2R` and drift `gi2Bhat`. -/
noncomputable def gi2Nu : ℕ → Measure (Fin 1 → ℝ) :=
  forwardMarginal (fun _ => randomEmKernel 1 gi2R gi2Bhat gi2Bhat_measurable)
    (Measure.pi fun _ => gaussianReal 1 1)

/-- Instance needed to apply the audited theorem. -/
instance : IsProbabilityMeasure (gi2Mu 0) := by
  simp only [gi2Mu, forwardMarginal_zero]; infer_instance

/-- Instance needed to apply the audited theorem. -/
instance : IsProbabilityMeasure (gi2Nu 0) := by
  simp only [gi2Nu, forwardMarginal_zero]; infer_instance

/-- All laws of the random-oracle chain are probability measures. -/
theorem gi2Nu_prob (k : ℕ) : IsProbabilityMeasure (gi2Nu k) :=
  ErrorPropagation.isProbabilityMeasure_of_comp_succ (μ := gi2Nu)
    (κ := fun _ => randomEmKernel 1 gi2R gi2Bhat gi2Bhat_measurable)
    (fun k => forwardMarginal_succ _ _ k) k

/-- The initial KL of the GI-2 witness is `KL(N(1, I) ‖ N(0, I)) = 1/2`. -/
theorem gi2_klDiv0 : klDiv (gi2Nu 0) (gi2Mu 0) = ENNReal.ofReal (1 / 2) := by
  simp only [gi2Nu, gi2Mu, forwardMarginal_zero, stdGauss1]
  rw [klDiv_pi_gaussianReal (fun _ => 1) (fun _ => 0) one_ne_zero]; norm_num

/-- **GI-2 non-vacuity (exact Monte Carlo oracle).** `N = 1` exact `N(0, 1)` posterior draws,
plug-in drift `b̂ = m̂`, initial `KL = 1/2`: every hypothesis of
`tvSup_monteCarloChain_le_sqrt` holds and the bound is `√(1/4 + n/8)`. -/
theorem gi2_monteCarlo (n : ℕ) :
    tvSup (gi2Nu n) (gi2Mu n) ≤ Real.sqrt (1 / 4 + n / 8) := by
  have hq : ∀ i, MemLp (fun y : Fin 1 → ℝ => y i) 2 stdGauss1 := fun i =>
    MonteCarlo.memLp_of_hasLaw (memLp_id_gaussianReal 2) (stdGauss1_hasLaw i)
  have hm : ∀ i, ∫ y, y i ∂stdGauss1 = 0 := fun i => by
    rw [(stdGauss1_hasLaw i).integral_eq, integral_id_gaussianReal]
  have hv : ∀ i, variance (fun y : Fin 1 → ℝ => y i) stdGauss1 = 1 := fun i => by
    rw [(stdGauss1_hasLaw i).variance_eq, variance_id_gaussianReal]; simp
  have := gi2Nu_prob
  have h := tvSup_monteCarloChain_le_sqrt (N := 1) (h := fun _ => 1) (b := fun _ _ => 0)
    (hb := fun _ => measurable_const) (post := fun _ => Kernel.const _ stdGauss1)
    (m := fun _ _ => 0) (c := fun _ => 1) (R := fun _ => gi2R) (bhat := fun _ => gi2Bhat)
    (hbh := fun _ => gi2Bhat_measurable) (μ := gi2Mu) (ν := gi2Nu) one_pos
    (fun _ _ => rfl) (fun _ _ i => hq i) (fun _ _ i => hm i)
    (fun _ x ω => by simp [gi2Bhat]) (fun k => forwardMarginal_succ _ _ k)
    (fun k => forwardMarginal_succ _ _ k) n (by rw [gi2_klDiv0]; exact ENNReal.ofReal_ne_top)
    (fun _ => by simp only [Kernel.const_apply]; exact integrable_const _)
  refine h.trans_eq (congrArg Real.sqrt ?_)
  rw [gi2_klDiv0]
  simp [hv, probReal_univ]
  ring

/-- The translation `y ↦ y + 1` on `Fin 1 → ℝ`. -/
def gi2Shift : Fin 1 → ℝ := fun _ => 1

/-- The biased inner sampler output law `N(1, I)`, written as the shift of `N(0, I)`. -/
noncomputable def gi2Post : Measure (Fin 1 → ℝ) := stdGauss1.map (· + gi2Shift)

/-- Instance needed to apply the audited theorem. -/
instance : IsProbabilityMeasure gi2Post := by
  unfold gi2Post; infer_instance

/-- Draws from the biased inner sampler. -/
noncomputable def gi2RB : Kernel (Fin 1 → ℝ) (Fin 1 → Fin 1 → ℝ) :=
  Kernel.const _ (Measure.pi fun _ : Fin 1 => gi2Post)

/-- Instance needed to apply the audited theorem. -/
instance : IsMarkovKernel gi2RB := by unfold gi2RB; infer_instance

/-- The chain driven by the biased oracle, from `N(1, I)`. -/
noncomputable def gi2NuB : ℕ → Measure (Fin 1 → ℝ) :=
  forwardMarginal (fun _ => randomEmKernel 1 gi2RB gi2Bhat gi2Bhat_measurable)
    (Measure.pi fun _ => gaussianReal 1 1)

/-- Instance needed to apply the audited theorem. -/
instance : IsProbabilityMeasure (gi2NuB 0) := by
  simp only [gi2NuB, forwardMarginal_zero]; infer_instance

/-- **GI-2 non-vacuity (biased inner sampler, coupling form).** The inner sampler outputs
`N(1, 1)` while the exact posterior is `N(0, 1)` (squared bias `1`, not `0`); with the
translation coupling and `w = 1`, every hypothesis of
`tvSup_biasedMonteCarloChain_le_sqrt_of_coupling_le` holds. -/
theorem gi2_coupling (n : ℕ) :
    tvSup (gi2NuB n) (gi2Mu n) ≤ Real.sqrt ((klDiv (gi2NuB 0) (gi2Mu 0)).toReal / 2 +
      ∑ k ∈ Finset.range n, (1 : ℝ≥0) * (1 : ℝ) ^ 2 / 8 * (∫ _x, (1 : ℝ) ∂(gi2NuB k) +
        (∫ _x, ∑ i, variance (fun y : Fin 1 → ℝ => y i) gi2Post ∂(gi2NuB k)) / (1 : ℕ))) := by
  have hpB : ∀ k, IsProbabilityMeasure (gi2NuB k) := fun k =>
    ErrorPropagation.isProbabilityMeasure_of_comp_succ (μ := gi2NuB)
      (κ := fun _ => randomEmKernel 1 gi2RB gi2Bhat gi2Bhat_measurable)
      (fun k => forwardMarginal_succ _ _ k) k
  have hmeas : Measurable fun y : Fin 1 → ℝ => y + gi2Shift := by fun_prop
  have hq : ∀ i, MemLp (fun y : Fin 1 → ℝ => y i) 2 gi2Post := fun i => by
    unfold gi2Post
    rw [memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable hmeas.aemeasurable]
    exact (MonteCarlo.memLp_of_hasLaw (memLp_id_gaussianReal 2) (stdGauss1_hasLaw i)).add
      (memLp_const _)
  have hm : ∀ i, (0 : ℝ) = ∫ y, y i ∂stdGauss1 := fun i => by
    rw [(stdGauss1_hasLaw i).integral_eq, integral_id_gaussianReal]
  have htr := InnerSamplerAveraged.sum_sq_bias_translate_eq stdGauss1
    integrable_coord_stdGauss1 gi2Shift
  have hw : ∫⁻ p, ENNReal.ofReal (∑ i, (p.1 i - p.2 i) ^ 2)
      ∂(stdGauss1.map fun y => (y + gi2Shift, y)) ≤ ENNReal.ofReal 1 := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    simp [gi2Shift]
  exact InnerSamplerAveraged.tvSup_biasedMonteCarloChain_le_sqrt_of_coupling_le (N := 1)
    (h := fun _ => 1) (b := fun _ _ => 0) (hb := fun _ => measurable_const)
    (post := fun _ => Kernel.const _ gi2Post) (postEx := fun _ => Kernel.const _ stdGauss1)
    (m := fun _ _ => 0) (c := fun _ => 1) (R := fun _ => gi2RB) (bhat := fun _ => gi2Bhat)
    (hbh := fun _ => gi2Bhat_measurable) (μ := gi2Mu) (ν := gi2NuB) one_pos
    (fun _ _ => rfl) (fun _ _ i => hq i) (fun _ x ω => by simp [gi2Bhat])
    (fun k => forwardMarginal_succ _ _ k) (fun k => forwardMarginal_succ _ _ k) n
    (by simp only [gi2NuB, gi2Mu, forwardMarginal_zero, stdGauss1]
        rw [klDiv_pi_gaussianReal (fun _ => 1) (fun _ => 0) one_ne_zero]
        exact ENNReal.ofReal_ne_top)
    (fun _ _ i => hm i) (fun _ _ i => integrable_coord_stdGauss1 i)
    (fun _ _ => stdGauss1.map fun y => (y + gi2Shift, y)) (fun _ _ => htr.1)
    (fun _ _ => htr.2.1) (fun _ _ => 1) (fun _ _ => zero_le_one) (fun _ => integrable_const _)
    (fun _ _ => hw) (fun _ => by simp only [Kernel.const_apply]; exact integrable_const _)
    (fun _ => by simp only [Kernel.const_apply]; exact integrable_const _)

/-- The inner sampler of `gi2_coupling` is genuinely biased: its mean is `1`, the exact
posterior mean is `0`. -/
theorem gi2Post_mean : ∫ y, y 0 ∂gi2Post = 1 := by
  unfold gi2Post
  rw [integral_map (φ := fun y : Fin 1 → ℝ => y + gi2Shift) (f := fun y : Fin 1 → ℝ => y 0)
    (by fun_prop) (measurable_pi_apply (0 : Fin 1)).aestronglyMeasurable]
  simp only [Pi.add_apply, gi2Shift]
  rw [integral_add (integrable_coord_stdGauss1 0) (integrable_const _),
    (stdGauss1_hasLaw 0).integral_eq, integral_id_gaussianReal]
  simp

/-- **GI-2 non-vacuity (Gaussian tightness and Donsker–Varadhan hypothesis).** The
sub-Gaussian hypothesis holds for `N(0, 1)` and the squared-bias bound is attained with value
`1 = 2 · 1 · KL(N(1, 1) ‖ N(0, 1))`. -/
theorem gi2_tight :
    (∫ y, y ∂gaussianReal 1 1 - ∫ y, y ∂gaussianReal 0 1) ^ 2 =
      2 * (1 : ℝ≥0) * (klDiv (gaussianReal 1 1) (gaussianReal 0 1)).toReal ∧
    (∫ y, y ∂gaussianReal 1 1 - ∫ y, y ∂gaussianReal 0 1) ^ 2 = 1 :=
  ⟨InnerSamplerBias.sq_bias_gaussianReal_eq 1 one_ne_zero,
    by rw [integral_id_gaussianReal, integral_id_gaussianReal]; norm_num⟩

end GI2

section MH1

open ProbabilityTheory MH

/-- Joint measurability of the random-walk proposal density `q(x, y) = N(x, 1)(y)`. -/
theorem mh1_q_measurable :
    Measurable (Function.uncurry fun x y : ℝ => gaussianPDF x 1 y) :=
  MALA.measurable_gaussianPDF_comp measurable_fst measurable_snd 1

/-- **MH-1 non-vacuity (general Metropolis–Hastings).** Target `π = N(0, 1)` density with
respect to Lebesgue measure and random-walk proposal `N(x, 1)`: all hypotheses of
`invariant_mhKernel` hold, the target law is `N(0, 1)` itself, and every move is accepted with
positive probability (so invariance is not obtained by always rejecting). -/
theorem mh1_invariant (x y : ℝ) :
    (mhKernel volume (measurable_gaussianPDF 0 1) mh1_q_measurable).Invariant
        (volume.withDensity (gaussianPDF 0 1)) ∧
      volume.withDensity (gaussianPDF 0 1) = gaussianReal 0 1 ∧
      0 < acceptance (gaussianPDF 0 1) (fun x y => gaussianPDF x 1 y) x y := by
  refine ⟨invariant_mhKernel _ _ (fun x => lintegral_gaussianPDF_eq_one x one_ne_zero)
    (fun _ _ => ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top),
    (gaussianReal_of_var_ne_zero 0 one_ne_zero).symm, ?_⟩
  exact acceptance_pos (ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top)
    (mul_ne_zero (gaussianPDF_pos _ one_ne_zero _).ne' (gaussianPDF_pos _ one_ne_zero _).ne')

/-- **MH-1 non-vacuity (MALA on `Fin 2 → ℝ`).** For the standard Gaussian target
`π(x) = exp(-(x₀² + x₁²)/2)` and step `h = 1`, `invariant_malaKernelPi` applies and every move
is accepted with positive probability. -/
theorem mh1_mala (x y : Fin 2 → ℝ) :
    (MALA.malaKernelPi (fun z : Fin 2 → ℝ => Real.exp (-(z 0 ^ 2 + z 1 ^ 2) / 2))
        (by fun_prop) 1).Invariant
      (volume.withDensity (MALA.targetDensity fun z : Fin 2 → ℝ =>
        Real.exp (-(z 0 ^ 2 + z 1 ^ 2) / 2))) ∧
    0 < acceptance (MALA.targetDensity fun z : Fin 2 → ℝ => Real.exp (-(z 0 ^ 2 + z 1 ^ 2) / 2))
      (MALA.proposalPi (fun z : Fin 2 → ℝ => Real.exp (-(z 0 ^ 2 + z 1 ^ 2) / 2)) 1) x y :=
  ⟨MALA.invariant_malaKernelPi _ one_pos, MALA.acceptance_pos_pi one_pos (Real.exp_pos _)⟩

end MH1

end FormalizeSampling.Audit.EstimationChains
