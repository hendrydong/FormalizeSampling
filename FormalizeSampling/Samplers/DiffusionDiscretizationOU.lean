module

public import FormalizeSampling.Samplers.DiffusionDiscretizationEntropy
public import FormalizeSampling.Samplers.DiffusionSetup
public import FormalizeSampling.Flow.ProbabilityFlowOU
public import FormalizeSampling.Flow.ProbabilityFlowOUMoment

/-!
# OU marginals of the diffusion chain as rescaled heat flows

Status: **Verified**.

For the forward chain of `Samplers/DiffusionSetup.lean` (data law `μ`, grid `t` with `t 0 = 0`,
strictly increasing) the marginal `p_k = fwdLaw μ t k` is the law of
`e^{-t_k} X₀ + √(1 - e^{-2 t_k}) Z`, i.e. a rescaling of the heat flow `μ * N(0, u_k I)` with
`u_k = e^{2 t_k} - 1` (`ouTau 1 1 t_k`). This file proves the identification and transports the
negative entropy and the Fisher information:

* `H^{OU}(p_k) = ∫ p_k log p_k = H(u_k) + d t_k`,
* `J^{OU}(p_k) = ∫ |∇p_k|²/p_k = e^{2 t_k} J(u_k)`,

with `H = heatNegEntropy μ`, `J = heatFisherInfo μ` the heat-flow quantities of
`Samplers/DiffusionDiscretizationEntropy.lean`.

## Main results

* `ouKernelVarPi_comp_comp`: OU semigroup `P_h ∘ P_s = P_{s+h}` (rate 1, stationary `N(0, I)`).
* `fwdLaw_eq_ouKernelVarPi_comp`: `p_k = ouKernelVarPi 1 1 (t k) ∘ₘ μ` (monotone grid,
  `t 0 = 0`).
* `continuous_fwdDensity`, `fwdDensity_eq_ouDensity`: `fwdDensity μ t k = ouDensity μ 1 1 (t k)`
  pointwise (`k ≥ 1`, strictly increasing grid).
* `ouNegEntropy_eq`: `p log p` is integrable and `∫ p log p = H(u) + d τ` for
  `p = ouDensity μ 1 1 τ`, `τ > 0` (`μ` with finite second moment).
* `ouFisherInfo_eq`: `|∇p|²/p` is integrable and `∫ |∇p|²/p = e^{2τ} J(u)`.
* `fwdScale_sq_mul_exp`, `fwdVar_mul_exp`: `α_k² e^{2t_k} = e^{2t_{k-1}}`,
  `β_k e^{2t_k} = u_k - u_{k-1}`.

## Not proved here

* The per-step KL identity (`Samplers/DiffusionDiscretizationStep.lean`).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Module
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi FormalizeSampling.Diffusion
  FormalizeSampling.OULangevinDecayPi
open FormalizeSampling.ProbabilityFlowOU (ouDensity ouGrad ouC ouTau ouDensity_scale
  ouGrad_scale ouDensity_pos continuous_ouDensity continuous_ouGrad lawOf_ouDensity)
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi)

variable {d : ℕ}

/-! ### OU semigroup and the forward marginals -/

/-- `scalePi b ∘ scalePi a = scalePi (b a)`. -/
theorem scalePi_comp_scalePi (a b : ℝ) :
    scalePi (d := d) b ∘ scalePi a = scalePi (b * a) := by
  funext x i; simp [scalePi, mul_assoc]

/-- **OU semigroup** (rate `1`, stationary law `N(0, I)`): for `s, h ≥ 0` and any measure `μ`,
`ouKernelVarPi 1 1 h ∘ₘ (ouKernelVarPi 1 1 s ∘ₘ μ) = ouKernelVarPi 1 1 (s + h) ∘ₘ μ`. -/
theorem ouKernelVarPi_comp_comp {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h)
    (μ : Measure (Fin d → ℝ)) :
    ouKernelVarPi 1 1 h ∘ₘ (ouKernelVarPi 1 1 s ∘ₘ μ) = ouKernelVarPi 1 1 (s + h) ∘ₘ μ := by
  rw [ouKernelVarPi_comp_eq 1 1 s μ, ouKernelVarPi_comp_eq 1 1 h,
    ouKernelVarPi_comp_eq 1 1 (s + h)]
  have hτ : 0 ≤ 1 * (1 - Real.exp (-2 * 1 * s)) := by
    have : Real.exp (-2 * 1 * s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hσ : 0 ≤ 1 * (1 - Real.exp (-2 * 1 * h)) := by
    have : Real.exp (-2 * 1 * h) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  rw [← ProbabilityFlowOU.heatKernelPi_comp_map_scalePi (Real.exp (-1 * h)) hτ,
    Measure.map_map (measurable_scalePi _) (measurable_scalePi _), scalePi_comp_scalePi,
    Measure.comp_assoc, heatKernelPi_comp_heatKernelPi,
    ← Real.toNNReal_add hσ (mul_nonneg (sq_nonneg _) hτ)]
  have e1 : Real.exp (-1 * h) * Real.exp (-1 * s) = Real.exp (-1 * (s + h)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : 1 * (1 - Real.exp (-2 * 1 * h)) +
      Real.exp (-1 * h) ^ 2 * (1 * (1 - Real.exp (-2 * 1 * s))) =
      1 * (1 - Real.exp (-2 * 1 * (s + h))) := by
    have a1 : Real.exp (-1 * h) ^ 2 = Real.exp (-2 * 1 * h) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have a2 : Real.exp (-2 * 1 * h) * Real.exp (-2 * 1 * s) = Real.exp (-2 * 1 * (s + h)) := by
      rw [← Real.exp_add]; ring_nf
    rw [a1]; nlinarith [a2]
  rw [e1, e2]

/-- **The forward marginals are OU marginals.** If `t 0 = 0` and `t` is monotone, then for
every `k`, `p_k = fwdLaw μ t k = ouKernelVarPi 1 1 (t k) ∘ₘ μ`. -/
theorem fwdLaw_eq_ouKernelVarPi_comp (μ : Measure (Fin d → ℝ)) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (hmono : Monotone t) (k : ℕ) : fwdLaw μ t k = ouKernelVarPi 1 1 (t k) ∘ₘ μ := by
  induction k with
  | zero =>
    rw [fwdLaw_zero, h0, OULangevinDecayPi.ouKernelVarPi_comp_of_mul_eq_zero (by ring)]
  | succ k ih =>
    have hk : 0 ≤ t k := h0 ▸ hmono (Nat.zero_le k)
    have hh : 0 ≤ t (k + 1) - t k := sub_nonneg.2 (hmono (Nat.le_succ k))
    rw [fwdLaw_succ, ih, fwdKernel, Nat.add_sub_cancel, ouKernelPi_eq_ouKernelVarPi,
      ouKernelVarPi_comp_comp hk hh, add_sub_cancel]

/-! ### The forward density is the OU density -/

/-- The forward density `fwdDensity μ t k` is continuous (any finite `μ`). -/
theorem continuous_fwdDensity (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (k : ℕ) : Continuous (fwdDensity μ t k) := by
  have e : fwdDensity μ t k = fun y => ∫ x, fwdTransDensity t k x y ∂(fwdLaw μ t (k - 1)) := by
    funext y; rw [fwdDensity, OUPosterior.piAffineDensity]; rfl
  rw [e]
  refine continuous_of_dominated (bound := fun _ => ∏ _i : Fin d,
    (Real.sqrt (2 * Real.pi * Real.sqrt (fwdVar t k) ^ 2))⁻¹) ?_ ?_ (integrable_const _) ?_
  · exact fun y => ((continuous_fwdTransDensity t k).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact fun y => Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (fwdTransDensity_nonneg t k x y)]
      exact fwdTransDensity_le t k x y
  · refine Eventually.of_forall fun x => ?_
    have hc := continuous_fwdTransDensity (d := d) t k
    have h2 : Continuous fun y : Fin d → ℝ => ((x, y) : (Fin d → ℝ) × (Fin d → ℝ)) :=
      continuous_const.prodMk continuous_id
    have h3 := hc.comp h2
    simp only [Function.comp_def] at h3
    exact h3

/-- **`fwdDensity` is the OU density.** For a probability `μ`, `t 0 = 0`, `t` strictly
increasing and `k ≥ 1`: `fwdDensity μ t k = ouDensity μ 1 1 (t k)` everywhere. -/
theorem fwdDensity_eq_ouDensity (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (h0 : t 0 = 0) (hmono : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    fwdDensity μ t k = ouDensity μ 1 1 (t k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have htk : 0 < t (j + 1) := h0 ▸ hmono (Nat.succ_pos j)
  have h1 := fwdLaw_eq_withDensity μ (hmono (Nat.lt_succ_self j))
  have h2 := fwdLaw_eq_ouKernelVarPi_comp μ h0 hmono.monotone (j + 1)
  rw [← lawOf_ouDensity μ one_pos one_pos htk] at h2
  rw [h2] at h1
  have : IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (fwdDensity μ t (j + 1) y)) := by
    rw [← h1, lawOf_ouDensity μ one_pos one_pos htk]; infer_instance
  exact eq_of_withDensity_eq (continuous_fwdDensity μ t (j + 1))
    (continuous_ouDensity μ one_pos one_pos htk)
    (fun y => integral_nonneg fun x => fwdTransDensity_nonneg t (j + 1) x y)
    (fun y => (ouDensity_pos μ one_pos one_pos htk y).le) h1.symm

/-! ### Entropy and Fisher information under the OU ↔ heat-flow rescaling -/

/-- `scalePi c y = c • y`. -/
theorem scalePi_eq_smul (c : ℝ) (y : Fin d → ℝ) : scalePi c y = c • y := by
  funext i; simp [scalePi]

/-- Change of variables for the scaling `y ↦ c • y` on `Fin d → ℝ` (`c > 0`):
`∫ F = c^d ∫ F(c • y) dy`. -/
theorem integral_eq_pow_mul_integral_scalePi {c : ℝ} (hc : 0 < c) (F : (Fin d → ℝ) → ℝ) :
    ∫ x, F x = c ^ d * ∫ y, F (scalePi c y) := by
  simp_rw [scalePi_eq_smul]
  rw [Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul, ← mul_assoc,
    abs_of_pos (inv_pos.2 (pow_pos hc d)), mul_inv_cancel₀ (pow_pos hc d).ne', one_mul]

/-- Integrability is invariant under the scaling `y ↦ c • y` (`c ≠ 0`). -/
theorem integrable_iff_scalePi {c : ℝ} (hc : c ≠ 0) (F : (Fin d → ℝ) → ℝ) :
    Integrable F ↔ Integrable fun y => F (scalePi c y) := by
  simp_rw [scalePi_eq_smul]
  exact (integrable_comp_smul_iff volume F hc).symm

section Scaling

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]

/-- `ouC 1 τ = e^{-τ}` satisfies `log (ouC 1 τ) = -τ`. -/
theorem log_ouC (τ : ℝ) : Real.log (ouC 1 τ) = -τ := by
  simp [ouC]

/-- **Negative entropy of the OU marginal.** For a probability `μ` with finite second moment and
`τ > 0`, `p = ouDensity μ 1 1 τ` satisfies: `p log p` is integrable and
`∫ p log p = H(u) + d τ`, `u = ouTau 1 1 τ = e^{2τ} - 1`, `H = heatNegEntropy μ`. -/
theorem ouNegEntropy_eq (hmom : Integrable (fun x => ∑ i, x i ^ 2) μ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x => ouDensity μ 1 1 τ x * Real.log (ouDensity μ 1 1 τ x)) ∧
      ∫ x, ouDensity μ 1 1 τ x * Real.log (ouDensity μ 1 1 τ x) =
        heatNegEntropy μ (ouTau 1 1 τ) + d * τ := by
  set c := ouC 1 τ with hcdef
  have hc : 0 < c := ProbabilityFlowOU.ouC_pos 1 τ
  have hu : 0 < ouTau 1 1 τ := ProbabilityFlowOU.ouTau_pos one_pos one_pos hτ
  set q := heatFlowDensityPi μ (ouTau 1 1 τ)
  have hent := (heatKL_gaussian_eq μ hmom one_pos hu).1
  have hq := integrable_heatFlowDensityPi μ hu
  have hpt : ∀ y, ouDensity μ 1 1 τ (scalePi c y) * Real.log (ouDensity μ 1 1 τ (scalePi c y)) =
      (c ^ d)⁻¹ * (q y * Real.log (q y) + d * τ * q y) := by
    intro y
    rw [ouDensity_scale μ one_pos one_pos hτ]
    have hqy := heatFlowDensityPi_pos μ hu y
    rw [Real.log_mul (inv_pos.2 (pow_pos hc d)).ne' hqy.ne', Real.log_inv, Real.log_pow,
      log_ouC]
    ring
  have hint : Integrable fun y =>
      ouDensity μ 1 1 τ (scalePi c y) * Real.log (ouDensity μ 1 1 τ (scalePi c y)) := by
    simp_rw [hpt]
    exact (hent.add (hq.1.const_mul _)).const_mul _
  refine ⟨(integrable_iff_scalePi hc.ne' _).2 hint, ?_⟩
  rw [integral_eq_pow_mul_integral_scalePi hc]
  simp_rw [hpt]
  rw [integral_const_mul, integral_add hent (hq.1.const_mul _), integral_const_mul, hq.2,
    heatNegEntropy, ← mul_assoc, mul_inv_cancel₀ (pow_pos hc d).ne', one_mul, mul_one]

/-- **Fisher information of the OU marginal.** For a probability `μ` and `τ > 0`,
`p = ouDensity μ 1 1 τ`: `|∇p|²/p` is integrable and `∫ |∇p|²/p = e^{2τ} J(u)`,
`u = ouTau 1 1 τ`, `J = heatFisherInfo μ`. -/
theorem ouFisherInfo_eq {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x => (∑ i, ouGrad μ 1 1 τ x i ^ 2) / ouDensity μ 1 1 τ x) ∧
      ∫ x, (∑ i, ouGrad μ 1 1 τ x i ^ 2) / ouDensity μ 1 1 τ x =
        Real.exp (2 * τ) * heatFisherInfo μ (ouTau 1 1 τ) := by
  set c := ouC 1 τ with hcdef
  have hc : 0 < c := ProbabilityFlowOU.ouC_pos 1 τ
  have hu : 0 < ouTau 1 1 τ := ProbabilityFlowOU.ouTau_pos one_pos one_pos hτ
  have hJ := integrable_heatFisherInfo_integrand μ hu
  have hpt : ∀ y, (∑ i, ouGrad μ 1 1 τ (scalePi c y) i ^ 2) / ouDensity μ 1 1 τ (scalePi c y) =
      (c ^ d)⁻¹ * (c⁻¹ ^ 2 * ((∑ i, heatFlowGradPi μ (ouTau 1 1 τ) y i ^ 2) /
        heatFlowDensityPi μ (ouTau 1 1 τ) y)) := by
    intro y
    rw [ouDensity_scale μ one_pos one_pos hτ]
    have hg : ∀ i, ouGrad μ 1 1 τ (scalePi c y) i =
        (c ^ d)⁻¹ * c⁻¹ * heatFlowGradPi μ (ouTau 1 1 τ) y i := fun i =>
      ouGrad_scale μ one_pos one_pos hτ y i
    simp only [hg]
    have hqy := (heatFlowDensityPi_pos μ hu y).ne'
    have hcd := (pow_pos hc d).ne'
    rw [← hcdef]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    field_simp
  have hint : Integrable fun y => (∑ i, ouGrad μ 1 1 τ (scalePi c y) i ^ 2) /
      ouDensity μ 1 1 τ (scalePi c y) := by
    simp_rw [hpt]
    exact (hJ.const_mul _).const_mul _
  refine ⟨(integrable_iff_scalePi hc.ne' _).2 hint, ?_⟩
  rw [integral_eq_pow_mul_integral_scalePi hc]
  simp_rw [hpt]
  rw [integral_const_mul, integral_const_mul, ← heatFisherInfo, ← mul_assoc,
    mul_inv_cancel₀ (pow_pos hc d).ne', one_mul]
  congr 1
  rw [hcdef, ouC, inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
  ring_nf

end Scaling

/-! ### Grid algebra -/

/-- `α_k² e^{2 t_k} = e^{2 t_{k-1}}`. -/
theorem fwdScale_sq_mul_exp (t : ℕ → ℝ) (k : ℕ) :
    fwdScale t k ^ 2 * Real.exp (2 * t k) = Real.exp (2 * t (k - 1)) := by
  rw [fwdScale, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- `β_k e^{2 t_k} = (e^{2 t_k} - 1) - (e^{2 t_{k-1}} - 1)`. -/
theorem fwdVar_mul_exp (t : ℕ → ℝ) (k : ℕ) :
    fwdVar t k * Real.exp (2 * t k) =
      (Real.exp (2 * t k) - 1) - (Real.exp (2 * t (k - 1)) - 1) := by
  rw [fwdVar, sub_mul, one_mul, fwdScale_sq_mul_exp]; ring

/-- `ouTau 1 1 τ = e^{2τ} - 1`. -/
theorem ouTau_one (τ : ℝ) : ouTau 1 1 τ = Real.exp (2 * τ) - 1 := by
  simp [ouTau]

end FormalizeSampling.DiffusionDiscretization
