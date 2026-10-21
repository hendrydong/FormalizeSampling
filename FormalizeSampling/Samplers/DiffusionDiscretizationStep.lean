module

public import FormalizeSampling.Samplers.DiffusionDiscretizationOU
public import FormalizeSampling.Samplers.DiffusionPosterior
public import FormalizeSampling.Samplers.DiffusionKL
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The exact one-step discretisation error of the DDPM reverse step (Theorem A)

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean`: data law `μ` on `Fin d → ℝ` with finite second
moment, grid `t` with `t 0 = 0`, strictly increasing; forward OU steps
`F_k(x) = N(α_k x, β_k I)`, marginals `p_k` (densities `fwdDensity μ t k`, `k ≥ 1`), exact reverse
kernels `R_k`, posterior means `m*_k`, DDPM reverse variance `σ_k² = β_k / α_k²` (`ddpmVar`).

**Theorem A** (`lintegral_klDiv_revKernel_ddpm_eq`). For `k ≥ 2`, with `u_k = e^{2 t_k} - 1`,
`∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k(y) = H(u_{k-1}) - H(u_k) - ½ (u_k - u_{k-1}) J(u_k)`
(`= entropyStep μ u_{k-1} u_k`), where `H(u) = ∫ q_u log q_u` and `J(u) = ∫ |∇q_u|²/q_u` for the
heat flow `q_u = μ * N(0, u I)`. Together with Theorem B (`sum_entropyStep_le`) this gives the
`d`-linear discretisation bound.

Proof: for a.e. `y`, `R_k y` has Lebesgue density `r_y(x) = f(x) φ(x, y) / g(y)` (Bayes;
`f = p_{k-1}`, `g = p_k`, `φ` the forward transition density), and
`φ(x, y) = α^{-d} · N(y/α, (β/α²) I)(x)`, so the log-likelihood ratio of `R_y` against any
isotropic Gaussian is explicit. Against `N(m*(y), v I)` its `R_y`-mean involves
`∫ |x - m*(y)|² dR_y = ∫ |x - y/α|² dR_y - |m*(y) - y/α|²` (bias–variance), and Tweedie gives
`m*(y) - y/α = (β/α) ∇log g(y)`: this is the per-`y` formula `klDiv_revKernel_var_ae_eq`, for
every reverse variance `v > 0`. For `v = β/α²` the variance terms cancel
(`klDiv_revKernel_ddpm_ae_eq`):
`KL(R_y ‖ N(m*(y), (β/α²) I)) = E[log f(X_{k-1}) | X_k = y] - log g(y) - d log α
- (β/2)|∇log g(y)|²`. Averaging over `y ∼ p_k` (tower property through `R_k ∘ p_k = p_{k-1}`)
and the OU ↔ heat-flow rescaling (`ouNegEntropy_eq`, `ouFisherInfo_eq`) give the formula.

## Main results

* `klDiv_withDensity_pi_gaussianReal`: KL of a positive-density law against an isotropic
  Gaussian from a pointwise formula for the log-likelihood ratio.
* `integrable_sum_sub_sq`, `integral_sum_sub_sq_eq`: bias–variance for `∫ |x - c|²`.
* `revKernel_ae_eq_withDensity`: `R_{j+1} y = Leb.withDensity (f φ(·, y) / g(y))` a.e.
* `klDiv_revKernel_var_ae_eq`: the per-`y` formula for an arbitrary reverse variance `v > 0`;
  `klDiv_revKernel_ddpm_ae_eq`: its case `v = β/α²`.
* `integral_log_fwdDensity`, `integral_score_sq_fwdDensity`: entropy and Fisher information of
  the forward marginals in heat-flow coordinates.
* `lintegral_klDiv_revKernel_ddpm_eq` (Theorem A).

## Not proved here

* Nothing beyond the setting: no density, smoothness or log-concavity of `μ` is assumed.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_withDensity_ofReal_iff)

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.GaussianLSIPi FormalizeSampling.Diffusion FormalizeSampling.ReverseKernel
open FormalizeSampling.ProbabilityFlowOU (ouDensity ouGrad ouTau ouDensity_pos
  continuous_ouDensity score_ouDensity)

variable {d : ℕ}

/-! ### Densities against Lebesgue measure -/

/-- **KL against an isotropic Gaussian from a pointwise log-likelihood formula.** Let
`ν = Leb.withDensity r` be a probability measure with `r > 0` measurable, `a` a mean, `v ≠ 0`,
and `L` with `log r(x) + ∑ᵢ (log(2πv)/2 + (xᵢ - aᵢ)²/(2v)) = L(x)` for all `x` and
`L ∈ L¹(ν)`. Then `KL(ν ‖ N(a, v I)) = ofReal (∫ L dν)` and `∫ L dν ≥ 0`. -/
theorem klDiv_withDensity_pi_gaussianReal {r : (Fin d → ℝ) → ℝ} (hr : Measurable r)
    (hpos : ∀ x, 0 < r x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (r x))]
    (a : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (L : (Fin d → ℝ) → ℝ)
    (hL : ∀ x, Real.log (r x) + ∑ i, (Real.log (2 * Real.pi * v) / 2 + (x i - a i) ^ 2 / (2 * v))
      = L x)
    (hLint : Integrable L (volume.withDensity fun x => ENNReal.ofReal (r x))) :
    klDiv (volume.withDensity fun x => ENNReal.ofReal (r x))
        (Measure.pi fun i => gaussianReal (a i) v) =
      ENNReal.ofReal (∫ x, L x ∂(volume.withDensity fun x => ENNReal.ofReal (r x))) ∧
      0 ≤ ∫ x, L x ∂(volume.withDensity fun x => ENNReal.ofReal (r x)) := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (r x) with hνdef
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  have hacN : ν ≪ Measure.pi fun i => gaussianReal (a i) v :=
    hac.trans (volume_ac_pi_gaussianReal a hv)
  have hrn : ν.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (r x) :=
    Measure.rnDeriv_withDensity (volume : Measure (Fin d → ℝ)) hr.ennreal_ofReal
  have hllr : llr ν (Measure.pi fun i => gaussianReal (a i) v) =ᵐ[ν] L := by
    filter_upwards [llr_pi_gaussianReal_ae_eq ν hac a hv, hac.ae_le hrn] with x h1 h2
    rw [h1, h2, ENNReal.toReal_ofReal (hpos x).le, hL x]
  have hint : Integrable (llr ν (Measure.pi fun i => gaussianReal (a i) v)) ν :=
    hLint.congr hllr.symm
  have h0 := integral_llr_add_sub_measure_univ_nonneg hacN hint
  rw [integral_congr_ae hllr] at h0
  simp only [probReal_univ, add_sub_cancel_right] at h0
  refine ⟨?_, h0⟩
  rw [klDiv_of_ac_of_integrable hacN hint, integral_congr_ae hllr]
  simp

/-! ### Bias–variance for the squared distance -/

/-- If `∑ᵢ xᵢ²` is `ν`-integrable then so is `∑ᵢ (xᵢ - cᵢ)²`, for every `c`. -/
theorem integrable_sum_sub_sq {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (hν : Integrable (fun x => ∑ i, x i ^ 2) ν) (c : Fin d → ℝ) :
    Integrable (fun x => ∑ i, (x i - c i) ^ 2) ν := by
  refine ((hν.const_mul 2).add (integrable_const (2 * ∑ i, c i ^ 2))).mono'
    (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).sub continuous_const).pow 2).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have h : ∀ i, (x i - c i) ^ 2 ≤ 2 * x i ^ 2 + 2 * c i ^ 2 := fun i => by
    nlinarith [sq_nonneg (x i + c i)]
  calc ∑ i, (x i - c i) ^ 2 ≤ ∑ i, (2 * x i ^ 2 + 2 * c i ^ 2) :=
        Finset.sum_le_sum fun i _ => h i
    _ = 2 * ∑ i, x i ^ 2 + 2 * ∑ i, c i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- **Bias–variance identity.** For a probability `ν` on `Fin d → ℝ` with `∑ᵢ xᵢ²` integrable
and mean `m = meanPi ν`: `∫ |x - c|² dν = ∫ |x - m|² dν + |m - c|²` for every `c`. -/
theorem integral_sum_sub_sq_eq {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    (hν : Integrable (fun x => ∑ i, x i ^ 2) ν) (c : Fin d → ℝ) :
    ∫ x, ∑ i, (x i - c i) ^ 2 ∂ν =
      ∫ x, ∑ i, (x i - meanPi ν i) ^ 2 ∂ν + ∑ i, (meanPi ν i - c i) ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, m = meanPi ν := ⟨_, rfl⟩
  rw [← hm]
  have hxi := fun i => integrable_apply_of_sum_sq hν i
  have hpt : ∀ x : Fin d → ℝ, ∑ i, (x i - c i) ^ 2 = ∑ i, (x i - m i) ^ 2 +
      ∑ i, 2 * (m i - c i) * (x i - m i) + ∑ i, (m i - c i) ^ 2 := by
    intro x
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae (ae_of_all _ hpt)]
  have hmid : ∀ i, Integrable (fun x : Fin d → ℝ => 2 * (m i - c i) * (x i - m i)) ν :=
    fun i => ((hxi i).sub (integrable_const _)).const_mul _
  have i1 : Integrable (fun x : Fin d → ℝ => ∑ i, (x i - m i) ^ 2) ν :=
    integrable_sum_sub_sq hν m
  have i2 : Integrable (fun x : Fin d → ℝ => ∑ i, 2 * (m i - c i) * (x i - m i)) ν :=
    integrable_finsetSum _ fun i _ => hmid i
  have i12 : Integrable (fun x : Fin d → ℝ =>
      ∑ i, (x i - m i) ^ 2 + ∑ i, 2 * (m i - c i) * (x i - m i)) ν := i1.add i2
  have e1 := integral_add i12 (integrable_const (∑ i, (m i - c i) ^ 2))
  have e2 := integral_add i1 i2
  have e3 := integral_finsetSum (μ := ν) Finset.univ fun i _ => hmid i
  have h0 : ∀ i, ∫ x, 2 * (m i - c i) * (x i - m i) ∂ν = 0 := by
    intro i
    have hmi : ∫ x, x i ∂ν = m i := by rw [hm]; rfl
    rw [integral_const_mul, integral_sub (hxi i) (integrable_const _), integral_const, hmi,
      probReal_univ, one_smul, sub_self, mul_zero]
  simp only [h0, Finset.sum_const_zero] at e3
  rw [e1, e2, e3, integral_const, probReal_univ, one_smul, add_zero]

/-! ### The exact reverse kernel in explicit density form -/

section Step

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ}

/-- For `j ≥ 1` on a strictly increasing grid, `p_j = Leb.withDensity (fwdDensity μ t j)`. -/
theorem fwdLaw_eq_withDensity_of_one_le (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    fwdLaw μ t j = volume.withDensity fun y => ENNReal.ofReal (fwdDensity μ t j y) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact fwdLaw_eq_withDensity μ (ht (Nat.lt_succ_self i))

/-- For `j ≥ 1` on a strictly increasing grid, `fwdDensity μ t j > 0` everywhere. -/
theorem fwdDensity_pos_of_one_le (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) (y : Fin d → ℝ) :
    0 < fwdDensity μ t j y := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact fwdDensity_pos μ (ht (Nat.lt_succ_self i)) y

/-- **Explicit reverse kernel.** For `j ≥ 1` on a strictly increasing grid, for `p_{j+1}`-a.e.
`y`, `R_{j+1} y = Leb.withDensity (x ↦ f(x) φ(x, y) / g(y))` with `f = fwdDensity μ t j`,
`g = fwdDensity μ t (j+1)` and `φ = fwdTransDensity t (j+1)`. -/
theorem revKernel_ae_eq_withDensity (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ y ∂(fwdLaw μ t (j + 1)), revKernel μ t (j + 1) y =
      volume.withDensity fun x => ENNReal.ofReal
        (fwdDensity μ t j x * fwdTransDensity t (j + 1) x y / fwdDensity μ t (j + 1) y) := by
  filter_upwards [revKernel_ae_eq_bayes μ (ht (Nat.lt_succ_self j))] with y hy
  have hZ := fwdDensity_pos μ (ht (Nat.lt_succ_self j)) y
  have hmeas2 : Measurable (Function.uncurry
      (reverseDensity (fwdLaw μ t j) 1 (fwdTransDensityE t j))) :=
    measurable_reverseDensity (p := 1) measurable_const (measurable_fwdTransDensityE t j)
  have hm : marginalDensity (fwdLaw μ t j) 1 (fwdTransDensityE t j) y =
      ENNReal.ofReal (fwdDensity μ t (j + 1) y) := marginalDensity_eq_fwdDensity μ t j y
  have hr : reverseDensity (fwdLaw μ t j) 1 (fwdTransDensityE t j) y = fun x =>
      ENNReal.ofReal (fwdTransDensity t (j + 1) x y / fwdDensity μ t (j + 1) y) := by
    funext x
    rw [reverseDensity, hm, Pi.one_apply, one_mul, fwdTransDensityE,
      ENNReal.ofReal_div_of_pos hZ]
  have hφ : Measurable fun x => ENNReal.ofReal
      (fwdTransDensity t (j + 1) x y / fwdDensity μ t (j + 1) y) := by
    have hc := continuous_fwdTransDensity (d := d) t (j + 1)
    have h2 : Continuous fun x : Fin d → ℝ => ((x, y) : (Fin d → ℝ) × (Fin d → ℝ)) :=
      continuous_id.prodMk continuous_const
    have h3 := hc.comp h2
    simp only [Function.comp_def] at h3
    exact (h3.div_const _).measurable.ennreal_ofReal
  rw [← hy, densityKernel_apply hmeas2, hr, fwdLaw_eq_withDensity_of_one_le μ ht hj,
    ← withDensity_mul _ (continuous_fwdDensity μ t j).measurable.ennreal_ofReal hφ]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (fwdDensity_pos_of_one_le μ ht hj x).le, mul_div_assoc]

/-- `log` of the isotropic Gaussian kernel: for `σ > 0`,
`log piGaussKernel σ m y = ∑ᵢ (-log(2π σ²)/2 - (yᵢ - mᵢ)²/(2σ²))`. -/
theorem log_piGaussKernel {σ : ℝ} (hσ : 0 < σ) (m y : Fin d → ℝ) :
    Real.log (Tweedie.piGaussKernel σ m y) =
      ∑ i, (-Real.log (2 * Real.pi * σ ^ 2) / 2 - (y i - m i) ^ 2 / (2 * σ ^ 2)) := by
  have hv : (⟨σ ^ 2, sq_nonneg _⟩ : ℝ≥0) ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < σ ^ 2 by positivity)
  simp only [Tweedie.piGaussKernel, Tweedie.gaussKernel]
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos _ _ _ hv).ne')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GaussianFlowVsOU.log_gaussianPDFReal _ hv]
  rfl

/-- The Gaussian log-density identity behind Theorem A: with `v = β/α²`,
`log φ(x, y) + ∑ᵢ (log(2πv)/2 + (xᵢ - yᵢ/α)²/(2v)) = -d log α`. -/
theorem log_fwdTransDensity_add (ht : StrictMono t) {j : ℕ} (x y : Fin d → ℝ) :
    Real.log (fwdTransDensity t (j + 1) x y) +
      ∑ i, (Real.log (2 * Real.pi * (fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2)) / 2 +
        (x i - y i / fwdScale t (j + 1)) ^ 2 / (2 * (fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2)))
      = -(d * Real.log (fwdScale t (j + 1))) := by
  have hβ : 0 < fwdVar t (j + 1) := fwdVar_pos (by simpa using ht (Nat.lt_succ_self j))
  have hα := fwdScale_pos t (j + 1)
  have hlog : Real.log (fwdTransDensity t (j + 1) x y) =
      ∑ i, (-Real.log (2 * Real.pi * fwdVar t (j + 1)) / 2 -
        (y i - fwdScale t (j + 1) * x i) ^ 2 / (2 * fwdVar t (j + 1))) := by
    rw [fwdTransDensity, log_piGaussKernel (Real.sqrt_pos.2 hβ), Real.sq_sqrt hβ.le]
    rfl
  set α := fwdScale t (j + 1)
  set β := fwdVar t (j + 1)
  rw [hlog, ← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin d, -Real.log (2 * Real.pi * β) / 2 - (y i - α * x i) ^ 2 / (2 * β) +
      (Real.log (2 * Real.pi * (β / α ^ 2)) / 2 + (x i - y i / α) ^ 2 / (2 * (β / α ^ 2))) =
      -Real.log α := by
    intro i
    rw [show 2 * Real.pi * (β / α ^ 2) = (2 * Real.pi * β) / α ^ 2 by ring,
      Real.log_div (by positivity) (by positivity), Real.log_pow]
    field_simp
    ring
  simp_rw [hterm]
  simp

/-- `(ddpmVar t (j+1) : ℝ) = β_{j+1} / α_{j+1}²` on a strictly increasing grid. -/
theorem coe_ddpmVar (ht : StrictMono t) (j : ℕ) :
    (ddpmVar t (j + 1) : ℝ) = fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2 := by
  have hβ : 0 < fwdVar t (j + 1) := fwdVar_pos (by simpa using ht (Nat.lt_succ_self j))
  rw [ddpmVar, Real.coe_toNNReal _ (div_pos hβ (pow_pos (fwdScale_pos t _) 2)).le]

/-- `log f` is integrable under `R_{j+1} y` for `p_{j+1}`-a.e. `y`, and
`y ↦ ∫ log f dR_{j+1} y` is integrable with `∫∫ log f dR dp_{j+1} = ∫ log f dp_j`,
whenever `log f ∈ L¹(p_j)` (tower property through `R_{j+1} ∘ p_{j+1} = p_j`). -/
theorem tower_revKernel {j : ℕ} {F : (Fin d → ℝ) → ℝ} (hF : Measurable F)
    (hint : Integrable F (fwdLaw μ t j)) :
    (∀ᵐ y ∂(fwdLaw μ t (j + 1)), Integrable F (revKernel μ t (j + 1) y)) ∧
      Integrable (fun y => ∫ x, F x ∂(revKernel μ t (j + 1) y)) (fwdLaw μ t (j + 1)) ∧
      ∫ y, ∫ x, F x ∂(revKernel μ t (j + 1) y) ∂(fwdLaw μ t (j + 1)) =
        ∫ x, F x ∂(fwdLaw μ t j) := by
  have hc : revKernel μ t (j + 1) ∘ₘ fwdLaw μ t (j + 1) = fwdLaw μ t j :=
    revKernel_comp_fwdLaw μ t j
  rw [← hc] at hint ⊢
  have hmeas : Measurable fun y => ∫ x, F x ∂(revKernel μ t (j + 1) y) :=
    (hF.stronglyMeasurable.integral_kernel (κ := revKernel μ t (j + 1))).measurable
  refine ⟨Measure.ae_integrable_of_integrable_comp hint, ?_, ?_⟩
  · refine (Measure.integrable_integral_norm_of_integrable_comp hint).mono'
      hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact norm_integral_le_integral_norm _
  · have hP : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => F p.2)
        (fwdLaw μ t (j + 1) ⊗ₘ revKernel μ t (j + 1)) :=
      (Measure.integrable_compProd_snd_iff hF.aestronglyMeasurable).2 hint
    rw [← Measure.integral_compProd hP, ← Measure.snd_compProd, Measure.snd,
      integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable]

/-- **Entropy of the forward marginals.** For `j ≥ 1` (`t 0 = 0`, strictly increasing grid,
finite second moment): `log p_j ∈ L¹(p_j)` and `∫ log p_j dp_j = H(e^{2 t_j} - 1) + d t_j`. -/
theorem integral_log_fwdDensity (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (h0 : t 0 = 0)
    (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    Integrable (fun x => Real.log (fwdDensity μ t j x)) (fwdLaw μ t j) ∧
      ∫ x, Real.log (fwdDensity μ t j x) ∂(fwdLaw μ t j) =
        heatNegEntropy μ (Real.exp (2 * t j) - 1) + d * t j := by
  have htj : 0 < t j := h0 ▸ ht (by omega : 0 < j)
  have hfm := (continuous_fwdDensity μ t j).measurable
  have hf0 : ∀ x, 0 ≤ fwdDensity μ t j x := fun x => (fwdDensity_pos_of_one_le μ ht hj x).le
  have h := ouNegEntropy_eq μ hμ htj
  rw [← fwdDensity_eq_ouDensity μ h0 ht hj, ouTau_one] at h
  rw [fwdLaw_eq_withDensity_of_one_le μ ht hj, integrable_withDensity_ofReal_iff hfm hf0,
    integral_withDensity_ofReal hfm hf0]
  exact h

/-- `∑ᵢ (A + zᵢ / B) = d A + (∑ᵢ zᵢ) / B`. -/
private theorem sum_add_div (A B : ℝ) (z : Fin d → ℝ) :
    ∑ i, (A + z i / B) = d * A + (∑ i, z i) / B := by
  rw [Finset.sum_add_distrib, Finset.sum_div]
  simp

/-- **Per-`y` formula, arbitrary variance.** For a data law with finite second moment,
`t 0 = 0`, `t` strictly increasing, `j ≥ 1` and `v > 0`, for `p_{j+1}`-a.e. `y`, with
`f = p_j`, `g = p_{j+1}`, `w = β/α²`, `Λ(y) = ∫ log f dR_{j+1} y - log g(y) - d log α`,
`Q(y) = (β/2) |∇ log g(y)|²` and `V(y) = ∫ |x - m*(y)|² dR_{j+1} y`:
`KL(R_{j+1} y ‖ N(m*(y), v I)) = ofReal (Λ - Q + (d/2) log(v/w) + V (1/(2v) - 1/(2w)))`, the
argument is `≥ 0`, and `V(y) = ∫ |x - y/α|² dR_{j+1} y - (β/α)² |∇ log g(y)|²`. -/
theorem klDiv_revKernel_var_ae_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) {v : ℝ≥0} (hv : v ≠ 0) :
    ∀ᵐ y ∂(fwdLaw μ t (j + 1)),
      klDiv (revKernel μ t (j + 1) y)
          (Measure.pi fun i => gaussianReal (postMean μ t (j + 1) y i) v) =
        ENNReal.ofReal ((∫ x, Real.log (fwdDensity μ t j x) ∂(revKernel μ t (j + 1) y) -
          Real.log (fwdDensity μ t (j + 1) y) - d * Real.log (fwdScale t (j + 1))) -
          fwdVar t (j + 1) / 2 * ∑ i, score (fwdDensity μ t (j + 1)) y i ^ 2 +
          d / 2 * Real.log (v / (fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2)) +
          (∫ x, ∑ i, (x i - postMean μ t (j + 1) y i) ^ 2 ∂(revKernel μ t (j + 1) y)) *
            (1 / (2 * v) - 1 / (2 * (fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2)))) ∧
      0 ≤ (∫ x, Real.log (fwdDensity μ t j x) ∂(revKernel μ t (j + 1) y) -
          Real.log (fwdDensity μ t (j + 1) y) - d * Real.log (fwdScale t (j + 1))) -
          fwdVar t (j + 1) / 2 * ∑ i, score (fwdDensity μ t (j + 1)) y i ^ 2 +
          d / 2 * Real.log (v / (fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2)) +
          (∫ x, ∑ i, (x i - postMean μ t (j + 1) y i) ^ 2 ∂(revKernel μ t (j + 1) y)) *
            (1 / (2 * v) - 1 / (2 * (fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2))) ∧
      ∫ x, ∑ i, (x i - postMean μ t (j + 1) y i) ^ 2 ∂(revKernel μ t (j + 1) y) =
        ∫ x, ∑ i, (x i - y i / fwdScale t (j + 1)) ^ 2 ∂(revKernel μ t (j + 1) y) -
          (fwdVar t (j + 1) / fwdScale t (j + 1)) ^ 2 *
            ∑ i, score (fwdDensity μ t (j + 1)) y i ^ 2 := by
  set f := fwdDensity μ t j with hf
  set g := fwdDensity μ t (j + 1) with hg
  set α := fwdScale t (j + 1) with hα
  set β := fwdVar t (j + 1) with hβ
  set w := β / α ^ 2 with hw
  have hβ0 : 0 < β := fwdVar_pos (by simpa using ht (Nat.lt_succ_self j))
  have hα0 : 0 < α := fwdScale_pos t _
  have hw0 : 0 < w := by positivity
  have hv0 : (0 : ℝ) < v := by
    rcases (v.coe_nonneg).eq_or_lt with h | h
    · exact absurd (NNReal.coe_eq_zero.1 h.symm) hv
    · exact h
  have hfpos := fwdDensity_pos_of_one_le μ ht hj
  have hgpos := fwdDensity_pos_of_one_le μ ht (j := j + 1) (by omega)
  have hfm : Measurable f := (continuous_fwdDensity μ t j).measurable
  have hlogf : Integrable (fun x => Real.log (f x)) (fwdLaw μ t j) :=
    (integral_log_fwdDensity μ hμ h0 ht hj).1
  have htow := (tower_revKernel μ (Real.measurable_log.comp hfm) hlogf).1
  have htow2 := (tower_revKernel μ (t := t) (j := j)
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)
    (integrable_sum_sq_fwdLaw μ hμ t j)).1
  filter_upwards [revKernel_ae_eq_withDensity μ ht hj, postMean_ae_eq_tweedie μ
    (ht (Nat.lt_succ_self j)), htow, htow2] with y hy htw hlf0 hsq0
  have hlf : Integrable (fun x => Real.log (f x)) (revKernel μ t (j + 1) y) := hlf0
  have hsq : Integrable (fun x => ∑ i, x i ^ 2) (revKernel μ t (j + 1) y) := hsq0
  set m := postMean μ t (j + 1) y with hm
  set c : Fin d → ℝ := fun i => y i / α with hc
  set Λ := ∫ x, Real.log (f x) ∂(revKernel μ t (j + 1) y) - Real.log (g y) - d * Real.log α
  set Q := β / 2 * ∑ i, score g y i ^ 2
  set S := ∫ x, ∑ i, (x i - c i) ^ 2 ∂(revKernel μ t (j + 1) y)
  set V := ∫ x, ∑ i, (x i - m i) ^ 2 ∂(revKernel μ t (j + 1) y)
  -- bias–variance and Tweedie
  have hbv : S = V + ∑ i, (m i - c i) ^ 2 := integral_sum_sub_sq_eq hsq c
  have htw' : ∑ i, (m i - c i) ^ 2 = (β / α) ^ 2 * ∑ i, score g y i ^ 2 := by
    rw [htw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [scoreMean, hc, ← hα, ← hβ]
    field_simp
    ring
  -- KL against `N(m, v I)` from the density of `R_y`
  have hr : Measurable fun x => f x * fwdTransDensity t (j + 1) x y / g y := by
    have hcont := continuous_fwdTransDensity (d := d) t (j + 1)
    have h2 : Continuous fun x : Fin d → ℝ => ((x, y) : (Fin d → ℝ) × (Fin d → ℝ)) :=
      continuous_id.prodMk continuous_const
    have h3 := hcont.comp h2
    simp only [Function.comp_def] at h3
    exact ((continuous_fwdDensity μ t j).mul h3).div_const _ |>.measurable
  have hrpos : ∀ x, 0 < f x * fwdTransDensity t (j + 1) x y / g y := fun x =>
    div_pos (mul_pos (hfpos x) (fwdTransDensity_pos (t := t) (k := j + 1)
      (by simpa using ht (Nat.lt_succ_self j)) x y)) (hgpos y)
  have hprob : IsProbabilityMeasure (volume.withDensity fun x =>
      ENNReal.ofReal (f x * fwdTransDensity t (j + 1) x y / g y)) := by
    rw [← hy]; infer_instance
  set L : (Fin d → ℝ) → ℝ := fun x => (Real.log (f x) - Real.log (g y) - d * Real.log α) -
    (d * (Real.log (2 * Real.pi * w) / 2) + (∑ i, (x i - c i) ^ 2) / (2 * w)) +
    (d * (Real.log (2 * Real.pi * v) / 2) + (∑ i, (x i - m i) ^ 2) / (2 * v)) with hL
  have hLx : ∀ x, Real.log (f x * fwdTransDensity t (j + 1) x y / g y) +
      ∑ i, (Real.log (2 * Real.pi * v) / 2 + (x i - m i) ^ 2 / (2 * v)) = L x := by
    intro x
    have hφ := fwdTransDensity_pos (d := d) (t := t) (k := j + 1)
      (by simpa using ht (Nat.lt_succ_self j)) x y
    rw [Real.log_div (mul_pos (hfpos x) hφ).ne' (hgpos y).ne',
      Real.log_mul (hfpos x).ne' hφ.ne']
    have h1 := log_fwdTransDensity_add (d := d) ht (j := j) x y
    rw [sum_add_div] at h1
    rw [sum_add_div]
    simp only [hL, hc]
    rw [← hα, ← hβ, ← hw] at h1
    linarith
  have hq1 : Integrable (fun x => (∑ i, (x i - c i) ^ 2) / (2 * w))
      (revKernel μ t (j + 1) y) := (integrable_sum_sub_sq hsq c).div_const _
  have hq2 : Integrable (fun x => (∑ i, (x i - m i) ^ 2) / (2 * (v : ℝ)))
      (revKernel μ t (j + 1) y) := (integrable_sum_sub_sq hsq m).div_const _
  have hA : Integrable (fun x => Real.log (f x) - Real.log (g y) - d * Real.log α)
      (revKernel μ t (j + 1) y) := (hlf.sub (integrable_const _)).sub (integrable_const _)
  have hB : Integrable (fun x => d * (Real.log (2 * Real.pi * w) / 2) +
      (∑ i, (x i - c i) ^ 2) / (2 * w)) (revKernel μ t (j + 1) y) :=
    (integrable_const _).add hq1
  have hC : Integrable (fun x => d * (Real.log (2 * Real.pi * v) / 2) +
      (∑ i, (x i - m i) ^ 2) / (2 * v)) (revKernel μ t (j + 1) y) :=
    (integrable_const _).add hq2
  have hLint : Integrable L (volume.withDensity fun x =>
      ENNReal.ofReal (f x * fwdTransDensity t (j + 1) x y / g y)) := by
    rw [← hy]; exact (hA.sub hB).add hC
  obtain ⟨hKL, hL0⟩ := klDiv_withDensity_pi_gaussianReal hr hrpos m hv L hLx hLint
  have hIL : ∫ x, L x ∂(revKernel μ t (j + 1) y) =
      Λ - (d * (Real.log (2 * Real.pi * w) / 2) + S / (2 * w)) +
        (d * (Real.log (2 * Real.pi * v) / 2) + V / (2 * v)) := by
    simp only [hL]
    rw [integral_add (f := fun x => Real.log (f x) - Real.log (g y) - d * Real.log α -
        (d * (Real.log (2 * Real.pi * w) / 2) + (∑ i, (x i - c i) ^ 2) / (2 * w)))
        (hA.sub hB) hC,
      integral_sub (f := fun x => Real.log (f x) - Real.log (g y) - d * Real.log α) hA hB,
      integral_add (f := fun _ => (d : ℝ) * (Real.log (2 * Real.pi * w) / 2))
        (integrable_const _) hq1,
      integral_add (f := fun _ => (d : ℝ) * (Real.log (2 * Real.pi * v) / 2))
        (integrable_const _) hq2, integral_div, integral_div,
      integral_sub (f := fun x => Real.log (f x) - Real.log (g y))
        (hlf.sub (integrable_const _)) (integrable_const _),
      integral_sub hlf (integrable_const _)]
    simp [Λ, S, V]
  have hval : Λ - (d * (Real.log (2 * Real.pi * w) / 2) + S / (2 * w)) +
      (d * (Real.log (2 * Real.pi * v) / 2) + V / (2 * v)) =
      Λ - Q + d / 2 * Real.log (v / w) + V * (1 / (2 * v) - 1 / (2 * w)) := by
    have hlog : Real.log (2 * Real.pi * v) - Real.log (2 * Real.pi * w) = Real.log (v / w) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1; field_simp
    have hQ : (∑ i, (m i - c i) ^ 2) / (2 * w) = Q := by
      rw [htw', hw]; simp only [Q]; field_simp
    rw [hbv, ← hQ]
    have e : (V + ∑ i, (m i - c i) ^ 2) / (2 * w) = V / (2 * w) +
        (∑ i, (m i - c i) ^ 2) / (2 * w) := by ring
    rw [e]
    have : d * (Real.log (2 * Real.pi * v) / 2) - d * (Real.log (2 * Real.pi * w) / 2) =
        d / 2 * Real.log (v / w) := by rw [← hlog]; ring
    have e2 : V * (1 / (2 * v) - 1 / (2 * w)) = V / (2 * v) - V / (2 * w) := by ring
    rw [e2]
    linarith
  rw [← hy, hIL, hval] at hKL
  rw [← hy, hIL, hval] at hL0
  refine ⟨hKL, hL0, ?_⟩
  rw [← htw']
  linarith [hbv]

/-- **Per-`y` formula, DDPM variance.** For a data law with finite second moment, `t 0 = 0`,
`t` strictly increasing and `j ≥ 1`, for `p_{j+1}`-a.e. `y`, with `f = p_j`, `g = p_{j+1}`
(densities), `Λ(y) = ∫ log f dR_{j+1} y - log g(y) - d log α_{j+1}` and
`Q(y) = (β_{j+1}/2) ∑ᵢ (∂ᵢ log g(y))²`:
`KL(R_{j+1} y ‖ N(m*(y), (β/α²) I)) = ofReal (Λ(y) - Q(y))` and `Q(y) ≤ Λ(y)`
(the case `v = β/α²` of `klDiv_revKernel_var_ae_eq`). -/
theorem klDiv_revKernel_ddpm_ae_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ y ∂(fwdLaw μ t (j + 1)),
      klDiv (revKernel μ t (j + 1) y)
          (Measure.pi fun i => gaussianReal (postMean μ t (j + 1) y i) (ddpmVar t (j + 1))) =
        ENNReal.ofReal ((∫ x, Real.log (fwdDensity μ t j x) ∂(revKernel μ t (j + 1) y) -
          Real.log (fwdDensity μ t (j + 1) y) - d * Real.log (fwdScale t (j + 1))) -
          fwdVar t (j + 1) / 2 * ∑ i, score (fwdDensity μ t (j + 1)) y i ^ 2) ∧
      fwdVar t (j + 1) / 2 * ∑ i, score (fwdDensity μ t (j + 1)) y i ^ 2 ≤
        ∫ x, Real.log (fwdDensity μ t j x) ∂(revKernel μ t (j + 1) y) -
          Real.log (fwdDensity μ t (j + 1) y) - d * Real.log (fwdScale t (j + 1)) := by
  have hw : 0 < fwdVar t (j + 1) / fwdScale t (j + 1) ^ 2 :=
    div_pos (fwdVar_pos (by simpa using ht (Nat.lt_succ_self j))) (pow_pos (fwdScale_pos t _) 2)
  filter_upwards [klDiv_revKernel_var_ae_eq μ hμ h0 ht hj
    (ddpmVar_ne_zero ht (k := j + 1) (by omega))] with y hy
  obtain ⟨h1, h2, -⟩ := hy
  rw [coe_ddpmVar ht j, div_self hw.ne', Real.log_one, sub_self, mul_zero, mul_zero,
    add_zero, add_zero] at h1 h2
  exact ⟨h1, sub_nonneg.1 h2⟩

/-- **Fisher information of the forward marginals.** For `j ≥ 1` (`t 0 = 0`, strictly
increasing grid): `|∇ log p_j|² ∈ L¹(p_j)` and `∫ |∇ log p_j|² dp_j = e^{2 t_j} J(e^{2 t_j} - 1)`
(`score` is the state score `∇ log p`). -/
theorem integral_score_sq_fwdDensity (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    Integrable (fun y => ∑ i, score (fwdDensity μ t j) y i ^ 2) (fwdLaw μ t j) ∧
      ∫ y, ∑ i, score (fwdDensity μ t j) y i ^ 2 ∂(fwdLaw μ t j) =
        Real.exp (2 * t j) * heatFisherInfo μ (Real.exp (2 * t j) - 1) := by
  have htj : 0 < t j := h0 ▸ ht (by omega : 0 < j)
  have hfm := (continuous_fwdDensity μ t j).measurable
  have hf0 : ∀ x, 0 ≤ fwdDensity μ t j x := fun x => (fwdDensity_pos_of_one_le μ ht hj x).le
  have h := ouFisherInfo_eq μ htj
  rw [ouTau_one] at h
  have hpt : ∀ y, fwdDensity μ t j y * ∑ i, score (fwdDensity μ t j) y i ^ 2 =
      (∑ i, ouGrad μ 1 1 (t j) y i ^ 2) / ouDensity μ 1 1 (t j) y := by
    intro y
    rw [fwdDensity_eq_ouDensity μ h0 ht hj]
    simp_rw [score_ouDensity μ one_pos one_pos htj y]
    have := (ouDensity_pos μ one_pos one_pos htj y).ne'
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [fwdLaw_eq_withDensity_of_one_le μ ht hj, integrable_withDensity_ofReal_iff hfm hf0,
    integral_withDensity_ofReal hfm hf0]
  simp_rw [hpt]
  exact h

/-- **Theorem A (exact one-step discretisation error of the DDPM reverse step).** Let `μ` be a
probability measure on `Fin d → ℝ` with finite second moment, `t 0 = 0`, `t` strictly increasing
and `j ≥ 1`. With `u_k = e^{2 t_k} - 1`, `σ² = β_{j+1}/α_{j+1}²` (`ddpmVar`):
`∫ KL(R_{j+1} y ‖ N(m*_{j+1}(y), σ² I)) dp_{j+1}(y) = entropyStep μ u_j u_{j+1}
  = H(u_j) - H(u_{j+1}) - ½ (u_{j+1} - u_j) J(u_{j+1})`,
with `H`, `J` the negative entropy and Fisher information of the heat flow `μ * N(0, u I)`. -/
theorem lintegral_klDiv_revKernel_ddpm_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (h0 : t 0 = 0) (ht : StrictMono t) {j : ℕ} (hj : 1 ≤ j) :
    ∫⁻ y, klDiv (revKernel μ t (j + 1) y)
        (Measure.pi fun i => gaussianReal (postMean μ t (j + 1) y i) (ddpmVar t (j + 1)))
        ∂(fwdLaw μ t (j + 1)) =
      ENNReal.ofReal (entropyStep μ (Real.exp (2 * t j) - 1) (Real.exp (2 * t (j + 1)) - 1)) := by
  set f := fwdDensity μ t j with hf
  set g := fwdDensity μ t (j + 1) with hg
  have hfm : Measurable f := (continuous_fwdDensity μ t j).measurable
  obtain ⟨hlogf, hvalf⟩ := integral_log_fwdDensity μ hμ h0 ht hj
  obtain ⟨hlogg, hvalg⟩ := integral_log_fwdDensity μ hμ h0 ht (j := j + 1) (by omega)
  obtain ⟨hsc, hvalsc⟩ := integral_score_sq_fwdDensity μ h0 ht (j := j + 1) (by omega)
  obtain ⟨-, hT, hvalT⟩ := tower_revKernel μ (Real.measurable_log.comp hfm) hlogf
  set A := fun y => ∫ x, Real.log (f x) ∂(revKernel μ t (j + 1) y)
  have hA : Integrable A (fwdLaw μ t (j + 1)) := hT
  have hF : Integrable (fun y => (A y - Real.log (g y) - d * Real.log (fwdScale t (j + 1))) -
      fwdVar t (j + 1) / 2 * ∑ i, score g y i ^ 2) (fwdLaw μ t (j + 1)) :=
    ((hA.sub hlogg).sub (integrable_const _)).sub (hsc.const_mul _)
  have hae := klDiv_revKernel_ddpm_ae_eq μ hμ h0 ht hj
  rw [lintegral_congr_ae (hae.mono fun y hy => hy.1),
    ← ofReal_integral_eq_lintegral_ofReal hF (hae.mono fun y hy => sub_nonneg.2 hy.2)]
  congr 1
  have h1 : Integrable (fun y => A y - Real.log (g y)) (fwdLaw μ t (j + 1)) := hA.sub hlogg
  have h2 : Integrable (fun y => A y - Real.log (g y) - d * Real.log (fwdScale t (j + 1)))
      (fwdLaw μ t (j + 1)) := h1.sub (integrable_const _)
  have h3 : Integrable (fun y => fwdVar t (j + 1) / 2 * ∑ i, score g y i ^ 2)
      (fwdLaw μ t (j + 1)) := hsc.const_mul _
  rw [integral_sub h2 h3, integral_sub h1 (integrable_const _), integral_sub hA hlogg,
    integral_const_mul (fwdVar t (j + 1) / 2), integral_const]
  have hTA : ∫ y, A y ∂(fwdLaw μ t (j + 1)) = ∫ x, Real.log (f x) ∂(fwdLaw μ t j) := hvalT
  rw [hTA, hvalf, hvalg, hvalsc]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hlogα : Real.log (fwdScale t (j + 1)) = -(t (j + 1) - t j) := by
    rw [fwdScale, Real.log_exp, Nat.add_sub_cancel]
  have hβ := fwdVar_mul_exp t (j + 1)
  rw [Nat.add_sub_cancel] at hβ
  rw [hlogα, entropyStep, ← hβ]
  ring

end Step

end FormalizeSampling.DiffusionDiscretization
