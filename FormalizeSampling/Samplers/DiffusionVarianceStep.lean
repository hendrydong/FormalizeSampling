module

public import FormalizeSampling.Samplers.DiffusionDiscretizationStep
public import FormalizeSampling.Samplers.DiffusionVarianceHeat
public import FormalizeSampling.Flow.FokkerPlanckExistenceTight

/-!
# The exact one-step discretisation error for an arbitrary reverse variance (Theorem A, general σ)

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean`: data law `μ` on `Fin d → ℝ` with finite second
moment, grid `t` with `t 0 = 0`, strictly increasing; forward OU steps
`F_k(x) = N(α_k x, β_k I)`, marginals `p_k`, exact reverse kernels `R_k = F_k†p_{k-1}`, posterior
means `m*_k`. Heat-flow times `a = u_j = e^{2 t_j} - 1`, `b = u_{j+1}`.

**Theorem A, general variance** (`lintegral_klDiv_revKernel_var_eq`). For `j ≥ 1` and every
reverse variance `v > 0`, with `w = β/α² = (b - a)/(1 + a)` (`ddpmVar`) and
`C = (d (b - a) - (b - a)² J(b)) / (1 + a)` (`= E|X_j - m*(X_{j+1})|²`, the posterior variance):
`∫ KL(R_{j+1} y ‖ N(m*(y), v I)) dp_{j+1}(y)
  = entropyStep μ a b + (d/2) log(v / w) + C (1/(2v) - 1/(2w))`.
In particular `v ↦ KL` is minimised at `v* = C/d` (Bao, Li, Zhu, Zhang, *Analytic-DPM*, ICLR 2022,
Thm 1), with excess `(d/2)(log(v/v*) + v*/v - 1)` (`varStep_eq_opt`, `varStep_opt_le`),
and for `v = β`, one of the two choices of Ho, Jain and Abbeel (2020), the error is
`betaStep μ a b` (`lintegral_klDiv_revKernel_fwdVar_eq`).

Proof: average the per-`y` formula `klDiv_revKernel_var_ae_eq`
(`Samplers/DiffusionDiscretizationStep.lean`) over `y ∼ p_{j+1}`. Its `v`-independent part
averages to `entropyStep μ a b` (Theorem A for `σ² = β/α²`); the posterior variance
`V(y) = ∫ |x - y/α|² dR_y - (β/α)² |∇ log p_{j+1}(y)|²` averages to `C`, because the first term
averages to `d β/α²` through the joint law `p_{j+1} ⊗ R = (p_j ⊗ F).swap`
(`compProd_posterior_eq_map_swap`).

## Main results

* `integral_sqDist_revKernel`: `∫∫ |x - y/α|² dR_y dp_{j+1} = d β/α²`.
* `postVarHeat`, `varStep` (defs), `lintegral_klDiv_revKernel_var_eq`, `varStep_nonneg`:
  Theorem A for every `v > 0`.
* `varStep_fwdVar`, `lintegral_klDiv_revKernel_fwdVar_eq`: `σ² = β` gives `betaStep ≥ 0`.
* `postVarHeat_pos`, `varStep_eq_opt`, `varStep_opt_le`: the optimal variance (Analytic-DPM).

## Not proved here

* Nothing beyond the setting: no density, smoothness or log-concavity of `μ` is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi FormalizeSampling.Diffusion FormalizeSampling.ReverseKernel
open FormalizeSampling.ProbabilityFlowOU (ouDensity ouGrad ouTau ouDensity_pos
  continuous_ouDensity score_ouDensity)

variable {d : ℕ}

/-! ### The joint second moment `E|X_j - X_{j+1}/α|² = d β/α²` -/

section Joint

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ}

/-- **Joint second moment.** For `t_j < t_{j+1}`:
`y ↦ ∫ ∑ᵢ (xᵢ - yᵢ/α)² dR_{j+1} y` is `p_{j+1}`-integrable with integral `d β / α²`
(`α = α_{j+1}`, `β = β_{j+1}`): `E|X_j - X_{j+1}/α|² = E|√β Z/α|²`. -/
theorem integral_sqDist_revKernel {j : ℕ} (hj : t j < t (j + 1)) :
    Integrable (fun y => ∫ x, ∑ i, (x i - y i / fwdScale t (j + 1)) ^ 2
        ∂(revKernel μ t (j + 1) y)) (fwdLaw μ t (j + 1)) ∧
      ∫ y, ∫ x, ∑ i, (x i - y i / fwdScale t (j + 1)) ^ 2 ∂(revKernel μ t (j + 1) y)
        ∂(fwdLaw μ t (j + 1)) = d * fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2 := by
  set α := fwdScale t (j + 1) with hα
  set β := fwdVar t (j + 1) with hβ
  have hα0 : 0 < α := fwdScale_pos t _
  have hβ0 : 0 < β := fwdVar_pos (by simpa using hj)
  set G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun p => ∑ i, (p.2 i - p.1 i / α) ^ 2 with hG
  have hGc : Continuous G := by
    simp only [hG]
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_snd).sub
        (((continuous_apply i).comp continuous_fst).div_const _)).pow 2
  have hG0 : ∀ p, 0 ≤ G p := fun p => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hjoint : fwdLaw μ t (j + 1) ⊗ₘ revKernel μ t (j + 1) =
      (fwdLaw μ t j ⊗ₘ fwdKernel t (j + 1)).map Prod.swap := by
    rw [fwdLaw_succ]
    exact compProd_posterior_eq_map_swap
  -- the lower integral on the joint law
  have hinner : ∀ x : Fin d → ℝ, ∫⁻ y, ENNReal.ofReal (G (y, x)) ∂(fwdKernel t (j + 1) x) =
      ENNReal.ofReal (d * β / α ^ 2) := by
    intro x
    have e : ∀ y : Fin d → ℝ, ENNReal.ofReal (G (y, x)) = ENNReal.ofReal (α ^ 2)⁻¹ *
        ENNReal.ofReal (FokkerPlanckExistence.sqDist (fun i => α * x i) y) := by
      intro y
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [hG, FokkerPlanckExistence.sqDist, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
      ring
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, fwdKernel_apply,
      FokkerPlanckExistence.lintegral_sqDist_pi, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← hα, ← hβ, Real.coe_toNNReal _ hβ0.le]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hlint : ∫⁻ p, ENNReal.ofReal (G p) ∂(fwdLaw μ t (j + 1) ⊗ₘ revKernel μ t (j + 1)) =
      ENNReal.ofReal (d * β / α ^ 2) := by
    rw [hjoint, lintegral_map (f := fun p => ENNReal.ofReal (G p))
        hGc.measurable.ennreal_ofReal measurable_swap,
      Measure.lintegral_compProd (f := fun p => ENNReal.ofReal (G p.swap))
        (hGc.measurable.comp measurable_swap).ennreal_ofReal]
    simp only [Prod.swap_prod_mk]
    simp_rw [hinner]
    rw [lintegral_const, measure_univ, mul_one]
  have hint : Integrable G (fwdLaw μ t (j + 1) ⊗ₘ revKernel μ t (j + 1)) := by
    refine ⟨hGc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hG0), hlint]
    exact ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · have h := ((Measure.integrable_compProd_iff hGc.aestronglyMeasurable).1 hint).2
    refine h.congr (ae_of_all _ fun y => ?_)
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact Real.norm_of_nonneg (hG0 _)
  · have h := Measure.integral_compProd hint
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hG0) hGc.aestronglyMeasurable,
      hlint, ENNReal.toReal_ofReal (by positivity)] at h
    rw [h]

end Joint

/-! ### Theorem A for an arbitrary variance -/

section Step

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ}

/-- The posterior variance in heat-flow coordinates,
`postVarHeat ρ a b = (d (b - a) - (b - a)² J(b)) / (1 + a)`; by
`lintegral_klDiv_revKernel_var_eq` it is `E|X_j - m*(X_{j+1})|²` (`= (dβ - β² J(p_{j+1}))/α²`). -/
noncomputable def postVarHeat (ρ : Measure (Fin d → ℝ)) (a b : ℝ) : ℝ :=
  (d * (b - a) - (b - a) ^ 2 * heatFisherInfo ρ b) / (1 + a)

/-- The averaged one-step KL for reverse variance `v`, in heat-flow coordinates:
`varStep ρ a b v = entropyStep ρ a b + (d/2) log(v/w) + C (1/(2v) - 1/(2w))` with
`w = (b - a)/(1 + a)` (`= β/α²`) and `C = postVarHeat ρ a b`. -/
noncomputable def varStep (ρ : Measure (Fin d → ℝ)) (a b v : ℝ) : ℝ :=
  entropyStep ρ a b + d / 2 * Real.log (v / ((b - a) / (1 + a))) +
    postVarHeat ρ a b * (1 / (2 * v) - 1 / (2 * ((b - a) / (1 + a))))

/-- Theorem A for an arbitrary reverse variance together with nonnegativity of the right side;
see `lintegral_klDiv_revKernel_var_eq` and `varStep_nonneg`. -/
theorem lintegral_klDiv_revKernel_var_eq_and_nonneg
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ y, klDiv (revKernel μ t (j + 1) y)
        (Measure.pi fun i => gaussianReal (postMean μ t (j + 1) y i) v) ∂(fwdLaw μ t (j + 1)) =
      ENNReal.ofReal (varStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) v) ∧
    0 ≤ varStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) v := by
  set f := fwdDensity μ t j with hf
  set g := fwdDensity μ t (j + 1) with hg
  set α := fwdScale t (j + 1) with hα
  set β := fwdVar t (j + 1) with hβ
  set a := Real.exp (2 * t j) - 1 with ha
  set b := Real.exp (2 * t (j + 1)) - 1 with hb
  have hβ0 : 0 < β := fwdVar_pos (by simpa using ht (Nat.lt_succ_self j))
  have hα0 : 0 < α := fwdScale_pos t _
  have hfm : Measurable f := (continuous_fwdDensity μ t j).measurable
  obtain ⟨hlogf, hvalf⟩ := integral_log_fwdDensity μ hμ h0 ht hj
  obtain ⟨hlogg, hvalg⟩ := integral_log_fwdDensity μ hμ h0 ht (j := j + 1) (by omega)
  obtain ⟨hsc, hvalsc⟩ := integral_score_sq_fwdDensity μ h0 ht (j := j + 1) (by omega)
  obtain ⟨-, hT, hvalT⟩ := tower_revKernel μ (Real.measurable_log.comp hfm) hlogf
  obtain ⟨hSint, hSval⟩ := integral_sqDist_revKernel μ (ht (Nat.lt_succ_self j))
  set A := fun y => ∫ x, Real.log (f x) ∂(revKernel μ t (j + 1) y)
  have hA : Integrable A (fwdLaw μ t (j + 1)) := hT
  set ΛQ : (Fin d → ℝ) → ℝ := fun y => (A y - Real.log (g y) - d * Real.log α) -
    β / 2 * ∑ i, score g y i ^ 2 with hΛQ
  have hΛQint : Integrable ΛQ (fwdLaw μ t (j + 1)) :=
    ((hA.sub hlogg).sub (integrable_const _)).sub (hsc.const_mul _)
  -- `∫ (Λ - Q) = entropyStep` from Theorem A for `σ² = β/α²`
  have hΛQval : ∫ y, ΛQ y ∂(fwdLaw μ t (j + 1)) = entropyStep μ a b := by
    have hae := klDiv_revKernel_ddpm_ae_eq μ hμ h0 ht hj
    have h1 := lintegral_klDiv_revKernel_ddpm_eq μ hμ h0 ht hj
    rw [lintegral_congr_ae (hae.mono fun y hy => hy.1),
      ← ofReal_integral_eq_lintegral_ofReal hΛQint (hae.mono fun y hy => sub_nonneg.2 hy.2)]
      at h1
    exact (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg_of_ae (hae.mono fun y hy => sub_nonneg.2 hy.2))
      (entropyStep_nonneg μ hμ (by
        simp only [ha]
        refine sub_pos.2 ?_
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.2 (by have := h0 ▸ ht (by omega : 0 < j); linarith))
        (by simp only [ha, hb]; exact sub_le_sub_right (Real.exp_le_exp.2
          (by linarith [ht (Nat.lt_succ_self j)])) _))).1 h1
  -- the posterior-variance term
  set V : (Fin d → ℝ) → ℝ := fun y =>
    ∫ x, ∑ i, (x i - postMean μ t (j + 1) y i) ^ 2 ∂(revKernel μ t (j + 1) y) with hVdef
  have hvae := klDiv_revKernel_var_ae_eq μ hμ h0 ht hj hv
  have hVae : V =ᵐ[fwdLaw μ t (j + 1)] fun y =>
      (∫ x, ∑ i, (x i - y i / α) ^ 2 ∂(revKernel μ t (j + 1) y)) -
        (β / α) ^ 2 * ∑ i, score g y i ^ 2 := hvae.mono fun y hy => hy.2.2
  have hVint : Integrable V (fwdLaw μ t (j + 1)) :=
    (hSint.sub (hsc.const_mul _)).congr hVae.symm
  have hVval : ∫ y, V y ∂(fwdLaw μ t (j + 1)) =
      d * β / α ^ 2 - (β / α) ^ 2 * (Real.exp (2 * t (j + 1)) *
        heatFisherInfo μ (Real.exp (2 * t (j + 1)) - 1)) := by
    rw [integral_congr_ae hVae, integral_sub hSint (hsc.const_mul _), integral_const_mul,
      hSval, hvalsc]
  -- assemble
  set w : ℝ := β / α ^ 2 with hw
  set κ' : ℝ := 1 / (2 * (v : ℝ)) - 1 / (2 * w) with hκ'
  have hK : Integrable (fun y => ΛQ y + d / 2 * Real.log (v / w) + V y * κ')
      (fwdLaw μ t (j + 1)) := (hΛQint.add (integrable_const _)).add (hVint.mul_const _)
  have hK0 : 0 ≤ ∫ y, ΛQ y + d / 2 * Real.log (v / w) + V y * κ' ∂(fwdLaw μ t (j + 1)) :=
    integral_nonneg_of_ae (hvae.mono fun y hy => hy.2.1)
  rw [lintegral_congr_ae (hvae.mono fun y hy => hy.1),
    ← ofReal_integral_eq_lintegral_ofReal hK (hvae.mono fun y hy => hy.2.1)]
  suffices hKv : ∫ y, ΛQ y + d / 2 * Real.log (v / w) + V y * κ' ∂(fwdLaw μ t (j + 1)) =
      varStep μ a b v by
    rw [hKv] at hK0 ⊢; exact ⟨rfl, hK0⟩
  rw [integral_add (f := fun y => ΛQ y + d / 2 * Real.log (v / w))
      (hΛQint.add (integrable_const _)) (hVint.mul_const _),
    integral_add hΛQint (integrable_const _), integral_mul_const κ' V, hΛQval, hVval,
    integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  -- heat-flow coordinates
  have hE := Real.exp_pos (2 * t (j + 1))
  have hαE : α ^ 2 * Real.exp (2 * t (j + 1)) = 1 + a := by
    have := fwdScale_sq_mul_exp t (j + 1)
    rw [Nat.add_sub_cancel] at this
    rw [hα, this, ha]; ring
  have hβE : β * Real.exp (2 * t (j + 1)) = b - a := by
    have := fwdVar_mul_exp t (j + 1)
    rw [Nat.add_sub_cancel] at this
    rw [hβ, this, ha, hb]
  have hw' : w = (b - a) / (1 + a) := by
    rw [hw, ← hβE, ← hαE]; field_simp
  have hC : d * β / α ^ 2 - (β / α) ^ 2 * (Real.exp (2 * t (j + 1)) *
      heatFisherInfo μ (Real.exp (2 * t (j + 1)) - 1)) = postVarHeat μ a b := by
    rw [postVarHeat, ← hβE, ← hαE, ← hb]
    field_simp
  rw [hC, varStep, ← hw', hκ']

/-- **Theorem A for an arbitrary reverse variance.** Let `μ` be a probability measure on
`Fin d → ℝ` with finite second moment, `t 0 = 0`, `t` strictly increasing, `j ≥ 1`, and `v ≠ 0`.
With `a = e^{2 t_j} - 1`, `b = e^{2 t_{j+1}} - 1`:
`∫ KL(R_{j+1} y ‖ N(m*_{j+1}(y), v I)) dp_{j+1}(y) = ofReal (varStep μ a b v)`, i.e.
`entropyStep μ a b + (d/2) log(v/w) + C (1/(2v) - 1/(2w))` with `w = β/α² = (b-a)/(1+a)` and
`C = (d (b-a) - (b-a)² J(b))/(1+a)` (the averaged posterior variance). -/
theorem lintegral_klDiv_revKernel_var_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ y, klDiv (revKernel μ t (j + 1) y)
        (Measure.pi fun i => gaussianReal (postMean μ t (j + 1) y i) v) ∂(fwdLaw μ t (j + 1)) =
      ENNReal.ofReal (varStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) v) :=
  (lintegral_klDiv_revKernel_var_eq_and_nonneg μ hμ h0 ht hj hv).1

/-- The averaged one-step KL is nonnegative: under the hypotheses of
`lintegral_klDiv_revKernel_var_eq`, `0 ≤ varStep μ a b v`. -/
theorem varStep_nonneg (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) {v : ℝ≥0} (hv : v ≠ 0) :
    0 ≤ varStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) v :=
  (lintegral_klDiv_revKernel_var_eq_and_nonneg μ hμ h0 ht hj hv).2

/-- In heat-flow coordinates `β_{j+1} = (b - a)/(1 + b)` and `varStep μ a b β_{j+1} =
betaStep μ a b` (`a = e^{2 t_j} - 1`, `b = e^{2 t_{j+1}} - 1`, `t_j < t_{j+1}`). -/
theorem varStep_fwdVar (ρ : Measure (Fin d → ℝ)) {j : ℕ} (hj : t j < t (j + 1)) :
    varStep ρ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) (fwdVar t (j + 1)) =
      betaStep ρ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) := by
  have hβ0 : 0 < fwdVar t (j + 1) := fwdVar_pos (by simpa using hj)
  set a := Real.exp (2 * t j) - 1 with ha
  set b := Real.exp (2 * t (j + 1)) - 1 with hb
  have hβE : fwdVar t (j + 1) * Real.exp (2 * t (j + 1)) = b - a := by
    have := fwdVar_mul_exp t (j + 1)
    rw [Nat.add_sub_cancel] at this
    rw [this, ha, hb]
  have hE : Real.exp (2 * t (j + 1)) = 1 + b := by rw [hb]; ring
  have hab : 0 < b - a := by rw [← hβE]; positivity
  have hca : 0 < 1 + a := by rw [ha]; have := Real.exp_pos (2 * t j); linarith
  have hcb : 0 < 1 + b := by rw [← hE]; positivity
  have hβ' : fwdVar t (j + 1) = (b - a) / (1 + b) := by
    rw [eq_div_iff hcb.ne', ← hE, hβE]
  rw [varStep, betaStep, postVarHeat, hβ']
  have e1 : (b - a) / (1 + b) / ((b - a) / (1 + a)) = (1 + a) / (1 + b) := by
    field_simp
  have e2 : 1 / (2 * ((b - a) / (1 + b))) - 1 / (2 * ((b - a) / (1 + a))) = 1 / 2 := by
    field_simp; ring
  rw [e1, e2]
  ring

/-- **The variance `σ² = β` (Ho, Jain, Abbeel).** Under the hypotheses of
`lintegral_klDiv_revKernel_var_eq`:
`∫ KL(R_{j+1} y ‖ N(m*_{j+1}(y), β_{j+1} I)) dp_{j+1}(y) = ofReal (betaStep μ a b)`,
`betaStep μ a b = entropyStep μ a b + (d/2) log((1+a)/(1+b)) + (d (b-a) - (b-a)² J(b))/(2(1+a))`
(Ho, Jain, Abbeel 2020, the first of their two choices "σ_t² = β_t"), and
`betaStep μ a b ≥ 0`. -/
theorem lintegral_klDiv_revKernel_fwdVar_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    ∫⁻ y, klDiv (revKernel μ t (j + 1) y)
        (Measure.pi fun i => gaussianReal (postMean μ t (j + 1) y i)
          (fwdVar t (j + 1)).toNNReal) ∂(fwdLaw μ t (j + 1)) =
      ENNReal.ofReal (betaStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1)) ∧
    0 ≤ betaStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1) := by
  have hβ0 : 0 < fwdVar t (j + 1) := fwdVar_pos (by simpa using ht (Nat.lt_succ_self j))
  have hv : (fwdVar t (j + 1)).toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hβ0
  obtain ⟨h1, h2⟩ := lintegral_klDiv_revKernel_var_eq_and_nonneg μ hμ h0 ht hj hv
  rw [Real.coe_toNNReal _ hβ0.le, varStep_fwdVar μ (ht (Nat.lt_succ_self j))] at h1 h2
  exact ⟨h1, h2⟩

/-- The averaged posterior variance is positive: for `d ≥ 1`, a probability `ρ` with finite
second moment and `0 < a < b`, `postVarHeat ρ a b > 0` (from `J(b) ≤ d/b`). -/
theorem postVarHeat_pos (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : 0 < postVarHeat ρ a b := by
  have hb : 0 < b := ha.trans hab
  have hJ := heatFisherInfo_le ρ hb
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (b - a) * heatFisherInfo ρ b ≤ (b - a) * (d / b) :=
    mul_le_mul_of_nonneg_left hJ (by linarith)
  have h2 : (b - a) * (d / b) < d := by
    rw [mul_div_assoc', div_lt_iff₀ hb]; nlinarith
  unfold postVarHeat
  refine div_pos ?_ (by linarith)
  have : d * (b - a) - (b - a) ^ 2 * heatFisherInfo ρ b =
      (b - a) * (d - (b - a) * heatFisherInfo ρ b) := by ring
  rw [this]
  exact mul_pos (by linarith) (by linarith)

/-- **Optimal reverse variance (Analytic-DPM).** For `d ≥ 1`, `0 < a < b` and every `v > 0`,
with `v* = C/d`, `C = postVarHeat ρ a b > 0`:
`varStep ρ a b v = varStep ρ a b v* + (d/2) (log(v/v*) + v*/v - 1)`.
Hence `v*` minimises the averaged one-step KL (`log r + 1/r - 1 ≥ 0`), recovering
Bao–Li–Zhu–Zhang (ICLR 2022, Thm 1) for the DDPM forward process, with the exact excess. -/
theorem varStep_eq_opt (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] (hd : 0 < d)
    {a b v : ℝ} (ha : 0 < a) (hab : a < b) (hv : 0 < v) :
    varStep ρ a b v = varStep ρ a b (postVarHeat ρ a b / d) +
      d / 2 * (Real.log (v / (postVarHeat ρ a b / d)) + postVarHeat ρ a b / d / v - 1) := by
  have hC := postVarHeat_pos ρ hd ha hab
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hw : 0 < (b - a) / (1 + a) := div_pos (by linarith) (by linarith)
  simp only [varStep]
  set C := postVarHeat ρ a b
  set w := (b - a) / (1 + a)
  have hl1 : Real.log (v / w) = Real.log (v / (C / d)) + Real.log (C / d / w) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hl1]
  field_simp
  ring

/-- **The optimal variance never loses.** Under `varStep_eq_opt`:
`varStep ρ a b (C/d) ≤ varStep ρ a b v` for every `v > 0`. -/
theorem varStep_opt_le (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] (hd : 0 < d)
    {a b v : ℝ} (ha : 0 < a) (hab : a < b) (hv : 0 < v) :
    varStep ρ a b (postVarHeat ρ a b / d) ≤ varStep ρ a b v := by
  rw [varStep_eq_opt ρ hd ha hab hv]
  have hC := postVarHeat_pos ρ hd ha hab
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 < v / (postVarHeat ρ a b / d) := by positivity
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
  rw [Real.log_inv] at this
  have e : (v / (postVarHeat ρ a b / d))⁻¹ = postVarHeat ρ a b / d / v := by
    field_simp
  rw [e] at this
  have : 0 ≤ Real.log (v / (postVarHeat ρ a b / d)) + postVarHeat ρ a b / d / v - 1 := by
    linarith
  nlinarith

end Step

end FormalizeSampling.DiffusionDiscretization
