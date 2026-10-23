module

public import Mathlib.Tactic.NormNum.Parity
public import FormalizeSampling.Flow.ProbabilityFlowOUZero
public import FormalizeSampling.Flow.ProbabilityFlowOUCounterexample
public import FormalizeSampling.Flow.DecayWithError
public import FormalizeSampling.Flow.ApproximateVelocity
public import FormalizeSampling.Foundations.TotalVariation
public import FormalizeSampling.Kernels.GaussianKernels

/-!
# Statement audit: KL first variation, dissipation and decay along continuity equations

Rows: FL-1, FL-2, FL-3, FL-4.

Non-vacuity witnesses for these rows of `docs/theorem_registry.md`. Each theorem below applies a
headline theorem of these rows to a concrete instance, discharging every hypothesis, and where cheap
shows that the conclusion is non-trivial (nonzero KL, equality cases).

## Instances

* **Abstract instance** (`Fin 1 → ℝ`, `μ_t = δ_0`, `H = 1`, target score `0`): the score field
  `s_t ≡ e^{-t}` with `KL(t) = e^{-2t}/2` satisfies every hypothesis of
  `KLDecay.exp_decay_idealVelocity` (and of `exp_decay_of_lsi`) with `lam = M = 1`; the
  conclusion `KL(t) ≤ e^{-2t} KL(0)` holds with equality. The zero velocity with `s_t ≡ 1`,
  `KL ≡ 1/2` satisfies every hypothesis of `DecayWithError.exp_decay_absError_sup` with `ε = 1`,
  and its first conclusion holds with equality, so the error term cannot be dropped.
* **Gaussian initial law** `ρ₁ = N(1, I)` on `Fin d → ℝ` (product of `N(1, 1)`), target
  `N(0, I)` (`v = 1`), OU rate `a = 1`. It is non-stationary for the OU flow and has every
  polynomial moment; `KL(ρ₁ ‖ N(0, I)) = d/2`, nonzero for `d ≥ 1`.

## Not proved here

* No witness applies `KLTransport.hasDerivAt_klIntegral` to a flow defined on all of `ℝ`
  directly; FL-1 is witnessed through `TransportKLRegularity.hasDerivAt_klDivDensity_local`,
  whose proof applies `hasDerivAt_klIntegral` to the time extension of the shifted OU flow.
* No witness for the eternal-ideal-flow form `KLDissipation.hasDerivAt_klIntegral_idealVelocity`
  other than the repo's stationary ones (`p_t = p⋆`).
* No witness for `KLDissipation.klDecay_of_steinMinimiser` beyond the repo's stationary one.
* The positivity of `klDivDensity` along the OU flow (only the `klDiv` form is shown nonzero).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Matrix Filter
open scoped ENNReal

namespace FormalizeSampling.Audit.FlowDecay

open KLDecay

/-! ### Abstract instance for the FL-3 / FL-4 skeleton theorems -/

/-- The abstract score field `s_t(x) = e^{-t}` on `Fin 1 → ℝ` (constant in `x`). -/
noncomputable def sAb (t : ℝ) (_x : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => Real.exp (-t)

/-- The abstract KL curve `KL(t) = e^{-2t} / 2`. -/
noncomputable def klAb (t : ℝ) : ℝ := Real.exp (-2 * t) / 2

/-- The zero target score field. -/
def sZero : (Fin 1 → ℝ) → Fin 1 → ℝ := 0

/-- With `H = 1` and target score `0`, the ideal velocity of `sAb t` is `-e^{-t}`. -/
theorem idealVelocity_one_sAb (t : ℝ) (x : Fin 1 → ℝ) :
    idealVelocity (1 : Matrix (Fin 1) (Fin 1) ℝ) (sAb t) sZero x =
      fun _ => -Real.exp (-t) := by
  funext i
  simp [idealVelocity, sAb, sZero]

/-- `e^{-t} e^{-t} = e^{-2t}`. -/
theorem exp_neg_mul_self (t : ℝ) : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
  rw [← Real.exp_add]; ring_nf

/-- The ideal-velocity rate along the abstract instance is `-e^{-2t}`. -/
theorem rate_sAb (t : ℝ) :
    ∫ x, idealVelocity (1 : Matrix (Fin 1) (Fin 1) ℝ) (sAb t) sZero x ⬝ᵥ
      (sAb t x - sZero x) ∂(Measure.dirac 0) = -Real.exp (-2 * t) := by
  rw [integral_dirac]
  simp only [idealVelocity_one_sAb]
  simp [sAb, sZero, dotProduct]
  rw [← Real.exp_add]; ring_nf

/-- The relative Fisher information along the abstract instance is `e^{-2t}`. -/
theorem relFisher_sAb (t : ℝ) :
    relFisher (Measure.dirac 0) (sAb t) sZero = Real.exp (-2 * t) := by
  rw [relFisher, integral_dirac]
  simp [sAb, sZero, dotProduct, exp_neg_mul_self]

/-- Every real function is integrable against `δ_0` on `Fin 1 → ℝ`. -/
theorem integrable_dirac_fin1 (f : (Fin 1 → ℝ) → ℝ) : Integrable f (Measure.dirac 0) :=
  integrable_dirac enorm_lt_top

/-- `d/dt (e^{-2t}/2) = -e^{-2t}`. -/
theorem hasDerivAt_klAb (t : ℝ) : HasDerivAt klAb (-Real.exp (-2 * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (-2 : ℝ)).exp.div_const 2
  convert h using 1
  · funext s; simp [klAb]
  · simp; ring

/-- **Non-vacuity of `KLDecay.exp_decay_idealVelocity` (FL-4).** On `Fin 1 → ℝ` with
`μ_t = δ_0`, `H = 1`, `M = lam = 1`, score `s_t ≡ e^{-t}`, target score `0` and
`KL(t) = e^{-2t}/2`, every hypothesis (`KLFirstVariation`, integrability, `LogSobolevAlong`)
holds and the conclusion `KL(t) ≤ e^{-2t} KL(0)` is an equality with `KL(0) = 1/2 ≠ 0`. -/
theorem exp_decay_idealVelocity_witness :
    (∀ t, 0 ≤ t → klAb t ≤ Real.exp (-2 * 1 * t / 1) * klAb 0) ∧
      (∀ t, klAb t = Real.exp (-2 * 1 * t / 1) * klAb 0) ∧ klAb 0 = 1 / 2 := by
  refine ⟨?_, fun t => ?_, by simp [klAb]⟩
  · refine exp_decay_idealVelocity (μ := fun _ => Measure.dirac 0) (s := sAb) (sStar := sZero)
      Matrix.PosDef.one one_pos (fun u => by simp [sqNormH]) one_pos (fun t _ => ?_)
      (fun t _ => integrable_dirac_fin1 _) (fun t _ => integrable_dirac_fin1 _) (fun t _ => ?_)
    · rw [rate_sAb]; exact hasDerivAt_klAb t
    · rw [relFisher_sAb]; simp [klAb]
  · simp [klAb]; ring

/-- **Non-vacuity of `KLDecay.exp_decay_of_lsi` (FL-4 skeleton).** `K(t) = e^{-2t}/2`,
`K' = -e^{-2t}`, `I(t) = e^{-2t}`, `c = lam = 1` satisfy all hypotheses; the bound is attained. -/
theorem exp_decay_of_lsi_witness :
    ∀ t, 0 ≤ t → klAb t ≤ Real.exp (-2 * 1 * 1 * t) * klAb 0 :=
  exp_decay_of_lsi (K' := fun t => -Real.exp (-2 * t)) (I := fun t => Real.exp (-2 * t))
    one_pos one_pos (fun t _ => hasDerivAt_klAb t) (fun t _ => by simp)
    (fun t _ => by simp [klAb])

/-- The constant score field `s_t(x) ≡ 1` on `Fin 1 → ℝ`. -/
def sOne (_t : ℝ) (_x : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => 1

/-- **Non-vacuity and tightness of `DecayWithError.exp_decay_absError_sup` (FL-4 with error).**
Zero velocity, `μ_t = δ_0`, `H = 1`, `M = lam = 1`, score `s_t ≡ 1`, target score `0`,
`KL ≡ 1/2`: every hypothesis holds with `ε = 1` (the velocity error is `E(t) = 1`), and the first
conclusion `KL(t) ≤ e^{-t} KL(0) + (ε M / (2 lam)) (1 - e^{-t})` is an equality, so the
additive error term cannot be dropped. -/
theorem exp_decay_absError_sup_witness :
    (∀ t, 0 ≤ t →
      (1 / 2 : ℝ) ≤ Real.exp (-(1 * t / 1)) * (1 / 2) +
          1 * 1 / (2 * 1) * (1 - Real.exp (-(1 * t / 1))) ∧
      (1 / 2 : ℝ) ≤ Real.exp (-(1 * t / 1)) * (1 / 2) + 1 * 1 / (2 * 1)) ∧
    ∀ t : ℝ, (1 / 2 : ℝ) = Real.exp (-(1 * t / 1)) * (1 / 2) +
          1 * 1 / (2 * 1) * (1 - Real.exp (-(1 * t / 1))) := by
  refine ⟨?_, fun t => by ring⟩
  refine DecayWithError.exp_decay_absError_sup (μ := fun _ => Measure.dirac 0)
    (f := fun _ _ => 0) (s := sOne) (sStar := sZero) (KL := fun _ => 1 / 2)
    Matrix.PosDef.one one_pos (fun u => by simp [sqNormH]) one_pos zero_le_one (fun t _ => ?_)
    (fun t _ => integrable_dirac_fin1 _) (fun t _ => integrable_dirac_fin1 _)
    (fun t _ => integrable_dirac_fin1 _) (fun t _ => integrable_dirac_fin1 _)
    (fun t _ => ?_) (fun t _ => ?_)
  · simp only [integral_dirac, zero_dotProduct]
    exact hasDerivAt_const t _
  · simp [relFisher, sOne, sZero, dotProduct]
  · simp [sqNormH, idealVelocity, sOne, sZero, dotProduct]

/-- **Non-vacuity of FL-3(a) `ApproximateVelocity.transport_rate_le_sharp`.** With `μ = δ_0`,
`H = 1`, `s ≡ 1`, `sStar = 0` (so `I = 1`), `ε = 1/4` and `f = (1/2) v⋆`, the hypotheses hold
and the conclusion is the nontrivial bound `rate ≤ -1/2`. -/
theorem transport_rate_le_sharp_witness :
    ∫ x, ((1 / 2 : ℝ) • idealVelocity (1 : Matrix (Fin 1) (Fin 1) ℝ) (sOne 0) sZero x) ⬝ᵥ
        (sOne 0 x - sZero x) ∂(Measure.dirac 0) ≤ -(1 / 2) := by
  have h := ApproximateVelocity.transport_rate_le_sharp (μ := Measure.dirac 0)
    (ε := 1 / 4) Matrix.PosDef.one
    (fun x => (1 / 2 : ℝ) • idealVelocity (1 : Matrix (Fin 1) (Fin 1) ℝ) (sOne 0) sZero x)
    (sOne 0) sZero (by norm_num) (integrable_dirac_fin1 _) (integrable_dirac_fin1 _)
    (integrable_dirac_fin1 _) (by
      simp only [integral_dirac]
      norm_num [sqNormH, idealVelocity, sOne, sZero, dotProduct])
  have hs : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hI : ∫ x, sqNormH (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ (sOne 0 x - sZero x)
      ∂(Measure.dirac (0 : Fin 1 → ℝ)) = 1 := by
    simp [sqNormH, sOne, sZero, dotProduct]
  rw [hI, hs] at h
  linarith

/-! ### Gaussian initial law `N(1, I)` -/

variable {d : ℕ}

/-- The initial law `ρ₁ = N(1, I) = ⊗ᵢ N(1, 1)` on `Fin d → ℝ`. -/
noncomputable abbrev rho1 (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 1 1

/-- `N(1, 1)` has a finite second moment. -/
theorem integrable_sq_gaussianReal_one : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 1 1) := by
  have := (memLp_id_gaussianReal (μ := 1) (v := 1) 2).integrable_norm_pow (by norm_num)
  simpa using this

/-- `N(1, 1)` has a finite fourth moment. -/
theorem integrable_pow_four_gaussianReal_one :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 1 1) := by
  have := (memLp_id_gaussianReal (μ := 1) (v := 1) 4).integrable_norm_pow (by norm_num)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [id, Real.norm_eq_abs]
  exact Even.pow_abs (by norm_num) x

/-- `ρ₁` has a finite second moment. -/
theorem integrable_sum_sq_rho1 : Integrable (fun x => ∑ i, x i ^ 2) (rho1 d) :=
  integrable_finsetSum _ fun i _ =>
    integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 1 1) (i := i)
      (f := fun x : ℝ => x ^ 2) integrable_sq_gaussianReal_one

/-- `ρ₁` has a finite fourth moment `∫ |y|⁴ dρ₁ < ∞` (Euclidean norm). -/
theorem integrable_sum_sq_sq_rho1 :
    Integrable (fun y => (∑ i, y i ^ 2) ^ 2) (rho1 d) := by
  have h4 : Integrable (fun x => (d : ℝ) * ∑ i, (x i ^ 2) ^ 2) (rho1 d) := by
    refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
    have := integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 1 1) (i := i)
      (f := fun x : ℝ => x ^ 4) integrable_pow_four_gaussianReal_one
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  refine h4.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => x i ^ 2)
    simpa using this

/-- `KL(ρ₁ ‖ N(0, I)) = d / 2` (`klDiv`, in `ℝ≥0∞`). -/
theorem klDiv_rho1 :
    klDiv (rho1 d) (Measure.pi fun _ : Fin d => gaussianReal 0 1) = ENNReal.ofReal (d / 2) := by
  rw [GaussianIncrement.klDiv_pi_gaussianReal _ _ one_ne_zero]
  congr 1
  simp

/-- The repo's `gaussPi d 1` is `⊗ᵢ N(0, 1)`. -/
theorem gaussPi_one_eq : HeatFlowRegularityPi.gaussPi d 1 =
    Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  simp [HeatFlowRegularityPi.gaussPi]

/-- `KL(ρ₁ ‖ N(0, I))` is finite. -/
theorem klDiv_rho1_ne_top :
    klDiv (rho1 d) (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≠ ∞ := by
  rw [klDiv_rho1]; exact ENNReal.ofReal_ne_top

/-! ### FL-4: OU (Langevin) flow, kernel form -/

/-- **Non-vacuity of `OULangevinDecay.toReal_klDiv_ouKernel_comp_le` (1D) and of its TV form.**
For `ρ = N(1, 1)`, `a = 1`, `t ≥ 0`, all hypotheses hold; `KL(ρ ‖ N(0,1)) = 1/2 ≠ 0`. -/
theorem ouKernel_witness {t : ℝ} (ht : 0 ≤ t) :
    (klDiv (OU.ouKernel 1 t ∘ₘ gaussianReal 1 1) (gaussianReal 0 1) ≠ ∞ ∧
      (klDiv (OU.ouKernel 1 t ∘ₘ gaussianReal 1 1) (gaussianReal 0 1)).toReal
        ≤ Real.exp (-2 * 1 * t) * (klDiv (gaussianReal 1 1) (gaussianReal 0 1)).toReal) ∧
    TotalVariation.tvSup (OU.ouKernel 1 t ∘ₘ gaussianReal 1 1) (gaussianReal 0 1)
      ≤ √(Real.exp (-2 * 1 * t) * (klDiv (gaussianReal 1 1) (gaussianReal 0 1)).toReal / 2) ∧
    (klDiv (gaussianReal 1 1) (gaussianReal 0 1)).toReal = 1 / 2 := by
  have hKL : klDiv (gaussianReal 1 1) (gaussianReal 0 1) = ENNReal.ofReal (1 / 2) := by
    rw [GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ one_ne_zero]; norm_num
  have hne : klDiv (gaussianReal 1 1) (gaussianReal 0 1) ≠ ∞ := by
    rw [hKL]; exact ENNReal.ofReal_ne_top
  refine ⟨OULangevinDecay.toReal_klDiv_ouKernel_comp_le zero_le_one ht _ hne
      integrable_sq_gaussianReal_one,
    OULangevinDecay.tvSup_ouKernel_comp_le zero_le_one ht _ hne integrable_sq_gaussianReal_one,
    ?_⟩
  rw [hKL, ENNReal.toReal_ofReal (by norm_num)]

/-- **Non-vacuity of `OULangevinDecayPi.toReal_klDiv_ouKernelPi_comp_le` and
`tvSup_ouKernelPi_comp_le` (`Fin d → ℝ`).** For `ρ₁ = N(1, I)`, `a = 1`, `t ≥ 0`, all
hypotheses hold and `KL(ρ₁ ‖ N(0, I)) = d/2`. -/
theorem ouKernelPi_witness {t : ℝ} (ht : 0 ≤ t) :
    (klDiv (OULangevinDecayPi.ouKernelPi 1 t ∘ₘ rho1 d)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≠ ∞ ∧
      (klDiv (OULangevinDecayPi.ouKernelPi 1 t ∘ₘ rho1 d)
          (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal
        ≤ Real.exp (-2 * 1 * t) *
          (klDiv (rho1 d) (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal) ∧
    TotalVariation.tvSup (OULangevinDecayPi.ouKernelPi 1 t ∘ₘ rho1 d)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1)
      ≤ √(Real.exp (-2 * 1 * t) *
          (klDiv (rho1 d) (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal / 2) ∧
    (klDiv (rho1 d) (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal = d / 2 := by
  refine ⟨OULangevinDecayPi.toReal_klDiv_ouKernelPi_comp_le zero_le_one ht _ klDiv_rho1_ne_top
      integrable_sum_sq_rho1,
    OULangevinDecayPi.tvSup_ouKernelPi_comp_le zero_le_one ht _ klDiv_rho1_ne_top
      integrable_sum_sq_rho1, ?_⟩
  rw [klDiv_rho1, ENNReal.toReal_ofReal (by positivity)]

/-! ### FL-1 / FL-2 / FL-4 along the OU probability flow from `ρ₁` -/

open ProbabilityFlowOU in
/-- **Non-vacuity of `ProbabilityFlowOU.gaussKL_ouDensity_le` and
`toReal_klDiv_ouKernelVarPi_comp_le_of_le`.** From `ρ₁ = N(1, I)`, `v = a = 1`, `0 < s ≤ t`. -/
theorem probabilityFlowOU_decay_witness {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    LogSobolevAlongGaussian.gaussKL (ouDensity (rho1 d) 1 1) 1 t ≤
        Real.exp (-2 * 1 * (t - s)) * LogSobolevAlongGaussian.gaussKL (ouDensity (rho1 d) 1 1) 1 s ∧
      klDiv (OULangevinDecayPi.ouKernelVarPi 1 1 t ∘ₘ rho1 d) (HeatFlowRegularityPi.gaussPi d 1)
        ≠ ⊤ :=
  ⟨gaussKL_ouDensity_le (rho1 d) one_pos one_pos integrable_sum_sq_rho1 hs hst,
    (toReal_klDiv_ouKernelVarPi_comp_le_of_le (rho1 d) one_pos one_pos integrable_sum_sq_rho1 hs
      hst).1⟩

open ProbabilityFlowOU in
/-- **Non-vacuity of `ProbabilityFlowOUMoment.transportKLRegularity_ou_moment` and
`klDecay_of_idealVelocity_local_ou_moment` (FL-2 / FL-4 with `TransportKLRegularity`).** For the
Gaussian initial law `ρ₁ = N(1, I)` (finite fourth moment, unbounded support), `v = a = 1`. -/
theorem probabilityFlowOU_moment_witness {s : ℝ} (hs : 0 < s) :
    KLDissipation.TransportKLRegularity (ouDensity (rho1 d) 1 1) (HeatKernelPi.heatDensityPi 1)
        (ouVelocity (rho1 d) 1 1) s ∧
    ∀ t, 0 ≤ t → KLDecay.klDivDensity (ouDensity (rho1 d) 1 1 (s + t))
        (HeatKernelPi.heatDensityPi 1) ≤
      Real.exp (-2 * 1 * t) *
        KLDecay.klDivDensity (ouDensity (rho1 d) 1 1 s) (HeatKernelPi.heatDensityPi 1) :=
  ⟨ProbabilityFlowOUMoment.transportKLRegularity_ou_moment (rho1 d) integrable_sum_sq_sq_rho1
      one_pos one_pos hs,
    (ProbabilityFlowOUMoment.klDecay_of_idealVelocity_local_ou_moment (rho1 d)
      integrable_sum_sq_sq_rho1 one_pos one_pos hs).2⟩

open ProbabilityFlowOU in
/-- **Non-vacuity of FL-1 (II), `TransportKLRegularity.hasDerivAt_klDivDensity_local`, on a
non-stationary flow.** For the OU probability flow from `ρ₁ = N(1, I)` (`v = a = 1`) shifted by
`s > 0`, every hypothesis is discharged and the first variation formula holds at `t₀ = 0`.
The proof of the theorem applies `KLTransport.hasDerivAt_klIntegral` to a time extension. -/
theorem fl1_witness {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => KLDecay.klDivDensity (ouDensity (rho1 d) 1 1 (s + t))
        (HeatKernelPi.heatDensityPi 1))
      (∫ x, (ouVelocity (rho1 d) 1 1 (s + 0) x ⬝ᵥ
        (score (ouDensity (rho1 d) 1 1 (s + 0)) x - score (HeatKernelPi.heatDensityPi 1) x)) *
          ouDensity (rho1 d) 1 1 (s + 0) x) 0 := by
  have hreg := ProbabilityFlowOU.transportKLRegularity_shift (s := s) (t₀ := 0)
    (ProbabilityFlowOUMoment.transportKLRegularity_ou_moment (rho1 d) integrable_sum_sq_sq_rho1
      one_pos one_pos (by simpa using hs))
  refine KLDissipation.TransportKLRegularity.hasDerivAt_klDivDensity_local hreg hs le_rfl
    (fun t ht x => ouDensity_pos (rho1 d) one_pos one_pos (by linarith) x)
    (HeatKernelPi.heatDensityPi_pos one_pos)
    (fun x => (HeatFlowDeBruijnPi.hasFDerivAt_heatDensityPi 1 x).differentiableAt)
    (fun t ht x => ?_)
  have h := (hasDerivAt_ouDensity_continuity (rho1 d) one_pos one_pos integrable_sum_sq_rho1
    (by linarith : 0 < s + t) x).comp t ((hasDerivAt_id' t).const_add s)
  rw [mul_one] at h
  exact h

open ProbabilityFlowOU LogSobolevAlongGaussian in
/-- **Non-vacuity of `LogSobolevAlongGaussian.exp_decay_idealVelocity_gaussian_one` and
`logSobolevAlong_gaussian`.** The OU probability flow from `ρ₁ = N(1, I)` with `v = a = 1` has
preconditioner `(a v)⁻¹ I = I`; shifted by `s > 0` it satisfies `GaussianDensityHyp` and
`KLFirstVariation` along `idealVelocity 1`, giving `KL(s+t) ≤ e^{-2t} KL(s)`. -/
theorem gaussian_one_witness {s : ℝ} (hs : 0 < s) :
    LogSobolevAlong (1 / 1) (fun t => lawOf (ouDensity (rho1 d) 1 1 (s + t)))
        (fun t => densityScore (ouDensity (rho1 d) 1 1 (s + t)) (ouGrad (rho1 d) 1 1 (s + t)))
        (gaussScore 1) (gaussKL (fun t => ouDensity (rho1 d) 1 1 (s + t)) 1) ∧
    ∀ t, 0 ≤ t → gaussKL (fun t => ouDensity (rho1 d) 1 1 (s + t)) 1 t ≤
      Real.exp (-2 * t / 1) * gaussKL (fun t => ouDensity (rho1 d) 1 1 (s + t)) 1 0 := by
  have hp : ∀ t, 0 ≤ t → GaussianDensityHyp (ouDensity (rho1 d) 1 1 (s + t))
      (ouGrad (rho1 d) 1 1 (s + t)) 1 := fun t ht =>
    gaussianDensityHyp_ouDensity (rho1 d) one_pos one_pos (by linarith) integrable_sum_sq_rho1
  have hP : ouPrecond d 1 1 = 1 := by simp [ouPrecond]
  have hKL := klFirstVariation_ou (rho1 d) one_pos one_pos integrable_sum_sq_rho1 hs
  rw [hP] at hKL
  exact ⟨logSobolevAlong_gaussian one_pos hp,
    exp_decay_idealVelocity_gaussian_one one_pos hp hKL⟩

/-- **Non-vacuity of `ProbabilityFlowOUZero.toReal_klDiv_ouKernelVarPi_comp_le_zero` (decay
from `t = 0`).** For `ρ₁ = N(1, I)`, `v = a = 1`, `t ≥ 0`; here `KL(ρ₁ ‖ N(0, I)) = d/2`. -/
theorem probabilityFlowOU_zero_witness {t : ℝ} (ht : 0 ≤ t) :
    klDiv (OULangevinDecayPi.ouKernelVarPi 1 1 t ∘ₘ rho1 d) (HeatFlowRegularityPi.gaussPi d 1)
        ≠ ⊤ ∧
      (klDiv (OULangevinDecayPi.ouKernelVarPi 1 1 t ∘ₘ rho1 d)
          (HeatFlowRegularityPi.gaussPi d 1)).toReal ≤
        Real.exp (-2 * 1 * t) * (klDiv (rho1 d) (HeatFlowRegularityPi.gaussPi d 1)).toReal := by
  refine ProbabilityFlowOUZero.toReal_klDiv_ouKernelVarPi_comp_le_zero (rho1 d) one_pos one_pos
    integrable_sum_sq_rho1 ?_ ht
  rw [gaussPi_one_eq]; exact klDiv_rho1_ne_top

/-- **The moment counterexamples are about genuine laws.** `rhoGeom (1/16)` has a finite third
moment and `rhoGeom (1/8)` a finite second moment, and for `v = a = t₀ = 1`
`TransportKLRegularity` fails for both. -/
theorem counterexample_witness :
    Integrable (fun y => ‖y‖ ^ 3) (ProbabilityFlowOUCounterexample.rhoGeom (1 / 16)) ∧
    ¬ KLDissipation.TransportKLRegularity
      (ProbabilityFlowOU.ouDensity (ProbabilityFlowOUCounterexample.rhoGeom (1 / 16)) 1 1)
      (HeatKernelPi.heatDensityPi 1)
      (ProbabilityFlowOU.ouVelocity (ProbabilityFlowOUCounterexample.rhoGeom (1 / 16)) 1 1) 1 ∧
    ¬ KLDissipation.TransportKLRegularity
      (ProbabilityFlowOU.ouDensity (ProbabilityFlowOUCounterexample.rhoGeom (1 / 8)) 1 1)
      (HeatKernelPi.heatDensityPi 1)
      (ProbabilityFlowOU.ouVelocity (ProbabilityFlowOUCounterexample.rhoGeom (1 / 8)) 1 1) 1 :=
  ⟨ProbabilityFlowOUCounterexample.integrable_norm_pow_three_rhoGeom_sixteenth,
    ProbabilityFlowOUCounterexample.not_transportKLRegularity_rhoGeom_sixteenth one_pos one_pos
      one_pos,
    fun h => ProbabilityFlowOUCounterexample.not_integrable_flux_log_rhoGeom (by norm_num)
      (by norm_num) one_pos one_pos one_pos (h.integrable_flux_log 0)⟩

end FormalizeSampling.Audit.FlowDecay
