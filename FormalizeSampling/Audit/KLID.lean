module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum.RealSqrt
public import FormalizeSampling.Foundations.Pinsker
public import FormalizeSampling.Foundations.KLChainRule
public import FormalizeSampling.Foundations.KLWarmApprox
public import FormalizeSampling.Foundations.KLLowerSemicontinuity
public import FormalizeSampling.Samplers.GaussianIncrementPi
public import FormalizeSampling.Examples.DiscreteGaussianFlow
public import FormalizeSampling.Foundations.HeatFlowRegularity
public import FormalizeSampling.Foundations.HeatFlowRegularityPi
public import FormalizeSampling.Foundations.GaussianLSIZero
public import FormalizeSampling.Foundations.GaussianLSIPi
public import FormalizeSampling.Foundations.BakryEmery
public import FormalizeSampling.Foundations.BakryEmeryPi
public import FormalizeSampling.Foundations.BakryEmeryGeneralPi
public import FormalizeSampling.Foundations.HolleyStroock
public import FormalizeSampling.Foundations.GaussianFunctionalLSIPi
public import FormalizeSampling.Foundations.LogSobolevTensorPi
public import FormalizeSampling.Foundations.LogSobolevExtension
public import FormalizeSampling.Foundations.LogSobolevLipschitzMap
public import FormalizeSampling.Foundations.PrekopaLeindler
public import FormalizeSampling.Identities.GaussianStein
public import FormalizeSampling.Identities.DensityStein
public import FormalizeSampling.Identities.ScoreFlowWeak
public import FormalizeSampling.Flow.ReverseTime

/-!
# Statement audit: KL tools, log-Sobolev inequalities, Stein, generator and reverse-time identities

Rows: KL-1, KL-2, KL-3, KL-4, KL-5, KL-6, ID-1, ID-2, ID-3, ID-4.

Non-vacuity witnesses for these rows of `docs/theorem_registry.md`. Each theorem below applies an
audited theorem to a concrete instance (Gaussians, constant kernels, explicit densities, bump test
functions), discharging every hypothesis; where cheap it also shows that the conclusion is not a
junk value (finite nonzero KL, positive Fisher information, sharp time-zero LSI, non-constant test
functions, non-Gaussian potentials).

Highlights:
* `pinsker_gauss`: KL-1 with `KL ≠ ∞` discharged by KL-3, giving `tvSup ≤ 1/2`.
* `lsi_heat_gauss`: KL-5(a) with `heatKL = 1/4 ≠ 0`, forcing `heatFisher ≥ 1/4`.
* `lsi_zero_gauss`: KL-5(b) for `N(1, 1)` against `N(0, 1)`; both sides equal `1/2`.
* `bakryEmery_quartic`, `bakryEmery_general`: KL-6 Bakry–Émery for non-Gaussian and
  non-separable potentials.
* `extension_exp`: KL-6 extension with the unbounded test function `e^{x/2}`.
* `reverseFP_exp`: ID-4 with a non-constant eternal solution of the heat equation.

## Not proved here

* Nothing about the proofs of the audited theorems (Lean checks those); no new mathematics.
* No separate witness for declarations whose hypotheses are typeclass assumptions only
  (`klDiv_comp_le_compProd`, `klDiv_comp_comp_le`, `klDiv_smul_add_smul_le`,
  `klDiv_map_measurableEquiv`, `klDiv_pi_pi`, `ent_prod_eq`); they are exercised indirectly.
* No witness for `GaussianLSIZeroPi.klDiv_le_fisher0` (the 1D analogue is
  `lsi_zero_gauss`), `ent_prod_le_of_functionalLSIPi`, `ent_sq_le_of_functionalLSIPi`,
  `DensityStein.integral_divergence_mul_eq_neg_integral_dotProduct_score`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal

namespace FormalizeSampling.Audit.KLID

/-! ### KL-3: Gaussian KL formulas -/

/-- `KL(N(1, 1)‖N(0, 1)) = 1/2` (KL-3 instance; finite and nonzero). -/
theorem klDiv_gauss_one_zero :
    klDiv (gaussianReal 1 1) (gaussianReal 0 1) = ENNReal.ofReal (1 / 2) := by
  rw [GaussianIncrement.klDiv_gaussianReal_gaussianReal 1 0 one_ne_zero]
  norm_num

/-- `KL(N(1, 1)‖N(0, 1))` is finite and nonzero. -/
theorem klDiv_gauss_one_zero_ne :
    klDiv (gaussianReal 1 1) (gaussianReal 0 1) ≠ ⊤ ∧
      klDiv (gaussianReal 1 1) (gaussianReal 0 1) ≠ 0 := by
  rw [klDiv_gauss_one_zero]
  exact ⟨ENNReal.ofReal_ne_top, by simp⟩

/-- `KL(N(0, 2)‖N(0, 1)) = (1 - log 2)/2 > 0` (general-variance KL-3 formula, nonzero). -/
theorem klDiv_gauss_var_two :
    klDiv (gaussianReal 0 2) (gaussianReal 0 1) = ENNReal.ofReal ((1 - Real.log 2) / 2) ∧
      0 < (1 - Real.log 2) / 2 := by
  refine ⟨?_, ?_⟩
  · rw [DiscreteGaussianFlow.klDiv_gaussianReal_gaussianReal 0 0 (by norm_num) one_ne_zero]
    congr 1
    push_cast
    norm_num
  · have := Real.log_two_lt_d9
    linarith

/-- Isotropic `d`-dimensional KL-3 instance: `KL(N(1, I_2)‖N(0, I_2)) = 1` (sum of squares
`/ (2v)`, Euclidean). -/
theorem klDiv_pi_gauss_two :
    klDiv (Measure.pi fun _ : Fin 2 => gaussianReal 1 1)
        (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = 1 := by
  rw [GaussianIncrement.klDiv_pi_gaussianReal (fun _ => 1) (fun _ => 0) one_ne_zero]
  norm_num

/-! ### KL-1: Pinsker -/

/-- Pinsker (KL-1) applied to `N(1, 1)` vs `N(0, 1)`, discharging `KL ≠ ∞` with KL-3:
`tvSup ≤ √(1/4) = 1/2`, a non-trivial bound (`tvSup ≤ 1` always). -/
theorem pinsker_gauss :
    TotalVariation.tvSup (gaussianReal 1 1) (gaussianReal 0 1) ≤ 1 / 2 := by
  have h := Pinsker.tvSup_le_sqrt_klDiv (klDiv_gauss_one_zero_ne).1
  rw [klDiv_gauss_one_zero, ENNReal.toReal_ofReal (by norm_num)] at h
  have : √((1 / 2 : ℝ) / 2) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) / 2 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [this ▸ h]

/-- Mathlib-normalised Pinsker (KL-1) on the same instance: `‖μ - ν‖₁ ≤ 1`. -/
theorem pinsker_gauss_mathlib :
    MeasureTheory.tvDist (gaussianReal 1 1) (gaussianReal 0 1) ≤ 1 := by
  have h := Pinsker.measureTheory_tvDist_le_sqrt_two_mul_klDiv (klDiv_gauss_one_zero_ne).1
  rw [klDiv_gauss_one_zero, ENNReal.toReal_ofReal (by norm_num)] at h
  simpa using h

/-! ### KL-4: tensorisation -/

/-- KL-4 instance: `KL(N(1,1) ⊗ N(1,1)‖N(0,1) ⊗ N(0,1)) = 1`, the sum of the factors. -/
theorem klDiv_prod_gauss :
    klDiv ((gaussianReal 1 1).prod (gaussianReal 1 1))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
  rw [GaussianIncrement.klDiv_prod_prod, klDiv_gauss_one_zero, ← ENNReal.ofReal_add
    (by norm_num) (by norm_num)]
  norm_num

/-! ### KL-2: chain rule, warm approximation, lower semicontinuity -/

/-- KL-2 chain-rule instance with constant kernels on `ℝ` (standard Borel, so
`CountableOrCountablyGenerated` is found by instance search): the kernel term contributes
`KL(N(1,1)‖N(0,1)) = 1/2` and the marginal term `1/2`. -/
theorem chainRule_gauss :
    klDiv ((gaussianReal 1 1) ⊗ₘ Kernel.const ℝ (gaussianReal 1 1))
        ((gaussianReal 0 1) ⊗ₘ Kernel.const ℝ (gaussianReal 0 1)) = 1 := by
  rw [KL.klDiv_compProd_eq_add_lintegral]
  simp only [Kernel.const_apply, lintegral_const, measure_univ, mul_one, klDiv_gauss_one_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- KL-2 propagation along two chains with non-zero per-step kernel error: `P k` constant at
`N(0,1)`, `Q k` constant at `N(1,1)`, chains `μ k = N(0,1)`, `ν k = N(1,1)`; the bound reads
`1/2 ≤ 1/2 + n/2` (each step contributes `KL(N(1,1)‖N(0,1)) = 1/2`). -/
theorem chain_le_sum_gauss (n : ℕ) :
    klDiv (gaussianReal 1 1) (gaussianReal 0 1) ≤
      klDiv (gaussianReal 1 1) (gaussianReal 0 1) +
        ∑ _k ∈ Finset.range n, ∫⁻ x, klDiv (Kernel.const ℝ (gaussianReal 1 1) x)
          (Kernel.const ℝ (gaussianReal 0 1) x) ∂(gaussianReal 1 1) :=
  KL.klDiv_chain_le_sum (fun _ => Kernel.const ℝ (gaussianReal 0 1))
    (fun _ => Kernel.const ℝ (gaussianReal 1 1)) (fun _ => gaussianReal 0 1)
    (fun _ => gaussianReal 1 1) (fun _ => by simp) (fun _ => by simp) n

/-- The warm-start hypothesis of `klDiv_comp_le_of_warm` is satisfiable with a non-identity
kernel: any Markov kernel `P` with `P ∘ₘ π = π'` satisfies it with `c = 1` (data processing),
so the theorem yields `KL(P ∘ₘ ρ‖π') < ∞` for every finite-KL `ρ`. Instance: `P` constant at
`N(0, 1)` and `ρ = N(1, 1)`. -/
theorem warm_const_kernel :
    klDiv (Kernel.const ℝ (gaussianReal 0 1) ∘ₘ gaussianReal 1 1)
        (gaussianReal 0 1) ≠ ⊤ := by
  have hπ : Kernel.const ℝ (gaussianReal 0 1) ∘ₘ gaussianReal 0 1 = gaussianReal 0 1 := by
    simp
  refine (KLWarmApprox.klDiv_comp_le_of_warm (gaussianReal 0 1)
    (Kernel.const ℝ (gaussianReal 0 1)) hπ 1 ?_ (gaussianReal 1 1)
    (klDiv_gauss_one_zero_ne).1).1
  intro ρ' _ C _ _ hKL
  rw [one_mul]
  exact ENNReal.toReal_mono hKL (KLWarmApprox.klDiv_comp_le_of_comp_eq _ hπ ρ')

/-- KL-2 lower semicontinuity instance (constant sequence): hypotheses discharged. -/
theorem lsc_const :
    klDiv (gaussianReal 1 1) (gaussianReal 0 1) ≤
      liminf (fun _ : ℕ => klDiv (gaussianReal 1 1) (gaussianReal 0 1)) atTop :=
  KLLowerSemicontinuity.klDiv_le_liminf_of_tendsto_integral (μ := fun _ : ℕ => gaussianReal 1 1)
    (fun _ _ _ _ => tendsto_const_nhds)


/-- KL-2 iteration (`klDiv_iterate_le_of_forall`) with the kernel constant at `π = N(0, 1)`
(one-step contraction factor `c = 0`) started at `N(1, 1)`: hypotheses discharged. -/
theorem iterate_const (k : ℕ) :
    (klDiv ((fun n : ℕ => if n = 0 then gaussianReal 1 1 else gaussianReal 0 1) k)
      (gaussianReal 0 1)).toReal ≤
      0 ^ k * (klDiv (gaussianReal 1 1) (gaussianReal 0 1)).toReal := by
  have hone : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], klDiv ρ (gaussianReal 0 1) ≠ ⊤ →
      klDiv (Kernel.const ℝ (gaussianReal 0 1) ∘ₘ ρ) (gaussianReal 0 1) ≠ ⊤ ∧
        (klDiv (Kernel.const ℝ (gaussianReal 0 1) ∘ₘ ρ) (gaussianReal 0 1)).toReal ≤
          0 * (klDiv ρ (gaussianReal 0 1)).toReal := by
    intro ρ _ _
    simp
  have : IsProbabilityMeasure
      ((fun n : ℕ => if n = 0 then gaussianReal 1 1 else gaussianReal 0 1) 0) := by
    simp only [ite_true]; infer_instance
  exact (KLWarmApprox.klDiv_iterate_le_of_forall (gaussianReal 0 1) _ le_rfl hone
    (fun n : ℕ => if n = 0 then gaussianReal 1 1 else gaussianReal 0 1)
    (fun n => by simp) (by simpa using (klDiv_gauss_one_zero_ne).1) k).2.2

/-! ### KL-5, KL-6, ID-1 … ID-4 -/

open scoped FormalizeSampling.OU in
/-- Heat flow of a Gaussian: `heatKernel t ∘ₘ N(m, v) = N(m, v + t)` (helper). -/
theorem heatKernel_comp_gauss (m : ℝ) (v t : ℝ≥0) :
    OU.heatKernel t ∘ₘ gaussianReal m v = gaussianReal m (v + t) := by
  exact OU.bind_heat v t m

/-- `x ↦ x²` is integrable under `N(m, v)` (helper). -/
theorem integrable_sq_gauss (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal m v) := by
  have := (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
  simpa using this

/-- `heatKL N(1,1) N(0,1) 1 = KL(N(1,2)‖N(0,2)) = 1/4`: finite and nonzero. -/
theorem heatKL_gauss :
    ProximalContraction.heatKL (gaussianReal 1 1) (gaussianReal 0 (1 : ℝ).toNNReal) 1 = 1 / 4 := by
  simp only [ProximalContraction.heatKL, Real.toNNReal_one, heatKernel_comp_gauss]
  rw [GaussianIncrement.klDiv_gaussianReal_gaussianReal 1 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  norm_num

/-- KL-5(a) applied to `ρ = N(1, 1)`, `π = N(0, 1)`, `t = 1`
(`GaussianLSI.heatKL_le_heatFisher_gaussianReal`): the KL side is `1/4 ≠ 0`, so the theorem forces
`heatFisher ≥ 1/4`, i.e. its conclusion is not the junk `0 ≤ 0`. -/
theorem lsi_heat_gauss :
    ProximalContraction.heatKL (gaussianReal 1 1) (gaussianReal 0 (1 : ℝ).toNNReal) 1 = 1 / 4 ∧
      1 / 4 ≤ HeatFlowDeBruijn.heatFisher (gaussianReal 1 1)
        (gaussianReal 0 (1 : ℝ).toNNReal) 1 := by
  have h := GaussianLSI.heatKL_le_heatFisher_gaussianReal (gaussianReal 1 1)
    one_pos (integrable_sq_gauss 1 1) one_pos
  rw [heatKL_gauss] at h
  exact ⟨heatKL_gauss, by linarith⟩

/-- `volume.withDensity (gaussianPDFReal 1 1) = N(1, 1)` (helper). -/
theorem withDensity_gauss :
    volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 1 1 x)) = gaussianReal 1 1 :=
  (gaussianReal_of_var_ne_zero 1 one_ne_zero).symm

/-- Probability-measure instance for the density `φ_{1,1}` (helper). -/
instance : IsProbabilityMeasure
    (volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 1 1 x))) := by
  rw [withDensity_gauss]; infer_instance

/-- The relative Fisher integrand of `p = φ_{1,1}` against `N(0, 1)` is `p` itself
(`p'/p + x = 1`). -/
theorem gauss_fisher_eq (x : ℝ) :
    gaussianPDFReal 1 1 x * ((-((x - 1) / ((1 : ℝ≥0) : ℝ)) * gaussianPDFReal 1 1 x) /
      gaussianPDFReal 1 1 x + x / 1) ^ 2 = gaussianPDFReal 1 1 x := by
  have hp := (gaussianPDFReal_pos 1 1 x one_ne_zero).ne'
  simp only [NNReal.coe_one, div_one]
  field_simp
  ring

/-- KL-5(b) applied to `p = density of N(1, 1)`, `v = 1`
(`GaussianLSIZero.klDiv_le_fisher0`): every hypothesis is discharged, and both sides
equal `1/2`, so the time-zero Gaussian LSI is attained (the constant `v/2` is sharp). -/
theorem lsi_zero_gauss :
    klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 1 x))
        (gaussianReal 0 (1 : ℝ).toNNReal) ≠ ⊤ ∧
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 1 1 x))
        (gaussianReal 0 (1 : ℝ).toNNReal)).toReal = 1 / 2 ∧
      (1 : ℝ) / 2 * ∫ x, gaussianPDFReal 1 1 x * ((-((x - 1) / ((1 : ℝ≥0) : ℝ)) *
        gaussianPDFReal 1 1 x) / gaussianPDFReal 1 1 x + x / 1) ^ 2 = 1 / 2 := by
  have hmom : Integrable fun x => x ^ 2 * gaussianPDFReal 1 1 x := by
    have h := integrable_sq_gauss 1 1
    rw [gaussianReal_of_var_ne_zero 1 one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 1 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
    simpa [mul_comm] using h
  have hfish : Integrable fun x => gaussianPDFReal 1 1 x * ((-((x - 1) / ((1 : ℝ≥0) : ℝ)) *
      gaussianPDFReal 1 1 x) / gaussianPDFReal 1 1 x + x / 1) ^ 2 := by
    simp_rw [gauss_fisher_eq]; exact integrable_gaussianPDFReal 1 1
  have h := GaussianLSIZero.klDiv_le_fisher0
    (fun x => gaussianPDFReal_pos 1 1 x one_ne_zero)
    (fun x => GaussianStein.hasDerivAt_gaussianPDFReal 1 1 x) one_pos hmom hfish
  have hI : ∫ x, gaussianPDFReal 1 1 x * ((-((x - 1) / ((1 : ℝ≥0) : ℝ)) *
      gaussianPDFReal 1 1 x) / gaussianPDFReal 1 1 x + x / 1) ^ 2 = 1 := by
    simp_rw [gauss_fisher_eq]; exact integral_gaussianPDFReal_eq_one 1 one_ne_zero
  refine ⟨h.1, ?_, by rw [hI]; norm_num⟩
  rw [withDensity_gauss, Real.toNNReal_one,
    GaussianIncrement.klDiv_gaussianReal_gaussianReal 1 0 one_ne_zero,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num


open LogSobolev

/-- `2 + sin` is a non-constant member of `LSIClass` (helper). -/
theorem lsiClass_two_add_sin : LSIClass (fun x => 2 + Real.sin x) where
  differentiable := by fun_prop
  bounded := ⟨3, fun x => by
    rw [abs_le]; constructor <;> linarith [Real.neg_one_le_sin x, Real.sin_le_one x]⟩
  bounded_deriv := ⟨1, fun x => by
    have : deriv (fun x => 2 + Real.sin x) x = Real.cos x := by
      simp
    rw [this]; exact Real.abs_cos_le_one x⟩
  pos := ⟨1, one_pos, fun x => by linarith [Real.neg_one_le_sin x]⟩

/-- Gross's inequality instance `FunctionalLSI N(0, 1) 1` (KL-6). -/
theorem gross_gauss :
    FunctionalLSI (gaussianReal 0 (1 : ℝ).toNNReal) 1 :=
  GaussianFunctionalLSI.functionalLSI_gaussianReal 1 one_pos

/-- KL-6 Gross's inequality applied to the non-constant test function `2 + sin`. -/
theorem gross_sin :
    ent (gaussianReal 0 (1 : ℝ).toNNReal) (fun x => (2 + Real.sin x) ^ 2) ≤
      2 * 1 * ∫ x, deriv (fun x => 2 + Real.sin x) x ^ 2 ∂(gaussianReal 0 (1 : ℝ).toNNReal) :=
  gross_gauss _ lsiClass_two_add_sin

/-- `(x²/2 + x⁴) - x²/2` is convex (helper). -/
theorem convexOn_quartic :
    ConvexOn ℝ Set.univ fun x : ℝ => (x ^ 2 / 2 + x ^ 4) - 1 / 2 * x ^ 2 := by
  have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 4) ⟨2, rfl⟩)
  refine h.congr fun x _ => ?_
  ring

/-- KL-6 Bakry–Émery (1D) for the non-Gaussian potential `x²/2 + x⁴`; the target is a
genuine probability measure (not the zero measure produced by a junk normaliser). -/
theorem bakryEmery_quartic :
    IsProbabilityMeasure (Proximal.target fun x => x ^ 2 / 2 + x ^ 4) ∧
      FunctionalLSI (Proximal.target fun x => x ^ 2 / 2 + x ^ 4) (1 / 1) := by
  refine ⟨Proximal.isProbabilityMeasure_target ?_,
    BakryEmery.functionalLSI_target_of_convexOn_sub one_pos convexOn_quartic⟩
  refine (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).mono' ?_ ?_
  · fun_prop
  · refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [pow_two_nonneg (x ^ 2)])

/-- KL-6 Holley–Stroock for `f = x²/2 + sin x` (`W = sin`, `a = -1`, `b = 1`). -/
theorem holleyStroock_sin :
    FunctionalLSI (Proximal.target fun x => ProximalSharp.gaussPotential 1 x + Real.sin x)
      (Real.exp (1 - -1) / 1) :=
  HolleyStroock.functionalLSI_target_gaussPotential_add one_pos Real.measurable_sin
    Real.neg_one_le_sin Real.sin_le_one

/-- KL-6 Lipschitz transport: push-forward of `N(0, 1)` by `sin` (`K = 1`). -/
theorem lipschitzMap_sin :
    FunctionalLSI ((gaussianReal 0 (1 : ℝ).toNNReal).map Real.sin) (1 ^ 2 * 1) :=
  LogSobolevLipschitzMap.functionalLSI_map_of_abs_deriv_le gross_gauss zero_le_one
    Real.differentiable_sin fun x => by simpa using Real.abs_cos_le_one x

/-- KL-6 convolution: `N(0, 1) * N(0, 1)` with constant `1 + 1`. -/
theorem convolution_gauss :
    FunctionalLSI (((gaussianReal 0 (1 : ℝ).toNNReal).prod (gaussianReal 0 (1 : ℝ).toNNReal)).map
      (fun p : ℝ × ℝ => p.1 + p.2)) (1 + 1) :=
  functionalLSI_map_add gross_gauss gross_gauss zero_le_one

/-- KL-6 tensorisation applied to `G(x, y) = 3 + sin x + sin y` under `N(0,1) ⊗ N(0,1)`
(all hypotheses discharged, `c = 1`, `M = 5`). -/
theorem tensor_sin :
    ent ((gaussianReal 0 (1 : ℝ).toNNReal).prod (gaussianReal 0 (1 : ℝ).toNNReal))
        (fun p => (3 + Real.sin p.1 + Real.sin p.2) ^ 2) ≤
      2 * ∫ p, (1 * Real.cos p.1 ^ 2 + 1 * Real.cos p.2 ^ 2)
        ∂((gaussianReal 0 (1 : ℝ).toNNReal).prod (gaussianReal 0 (1 : ℝ).toNNReal)) :=
  ent_prod_le_of_functionalLSI (G := fun p => 3 + Real.sin p.1 + Real.sin p.2)
    (D₁ := fun p => Real.cos p.1) (D₂ := fun p => Real.cos p.2) gross_gauss gross_gauss
    zero_le_one (by fun_prop) (by fun_prop) (by fun_prop)
    (fun x y => by simpa using ((Real.hasDerivAt_sin x).const_add 3).add_const (Real.sin y))
    (fun x y => by simpa using (Real.hasDerivAt_sin y).const_add (3 + Real.sin x))
    (M := 5) (c := 1) one_pos
    (fun p => by linarith [Real.neg_one_le_sin p.1, Real.neg_one_le_sin p.2])
    (fun p => by linarith [Real.sin_le_one p.1, Real.sin_le_one p.2])
    (fun p => by linarith [Real.abs_cos_le_one p.1])
    (fun p => by linarith [Real.abs_cos_le_one p.2])

/-- KL-6 variational formula for entropy, constant instance (hypotheses discharged). -/
theorem isGLB_const :
    IsGLB ((fun c => ∫ _x, HolleyStroock.psi c 2 ∂(gaussianReal 0 1)) '' Set.Ioi 0)
      (ent (gaussianReal 0 1) fun _ => 2) :=
  HolleyStroock.isGLB_integral_psi (integrable_const _) (integrable_const _) (by simp)

open ProximalContraction HeatFlowDeBruijn in
/-- KL-6 functional-to-KL bridge `heatKL_le_of_functionalLSI_of_integrable` with
`ρ = π = N(0, 1)` at `t = 1`; the integrability hypotheses come from `heatFlowRegular_self`. -/
theorem heatKL_bridge_self :
    heatKL (gaussianReal 0 1) (gaussianReal 0 1) 1 ≤
      (1 + 1) / 2 * heatFisher (gaussianReal 0 1) (gaussianReal 0 1) 1 :=
  LogSobolevExtension.heatKL_le_of_functionalLSI_of_integrable _ _ one_pos (by norm_num)
    (GaussianFunctionalLSI.functionalLSI_heatKernel_comp_of_targetLSI _ zero_le_one
      (by simpa using gross_gauss))
    ((heatFlowRegular_self _).integrable_kl 1 (Set.mem_Ioi.2 one_pos))
    ((heatFlowRegular_self _).integrable_fisher 1 (Set.mem_Ioi.2 one_pos))

open ProximalContraction HeatFlowDeBruijn in
/-- KL-6 functional-to-KL bridge `heatKL_le_of_functionalLSI_of_integrable` with
`ρ = N(1, 1) ≠ π = N(0, 1)` at `t = 1`; the integrability hypotheses come from
`HeatFlowRegularity.heatFlowRegular_gaussianReal` (finite second moment). -/
theorem heatKL_bridge_shift :
    heatKL (gaussianReal 1 1) (gaussianReal 0 (1 : ℝ).toNNReal) 1 ≤
      (1 + 1) / 2 * heatFisher (gaussianReal 1 1) (gaussianReal 0 (1 : ℝ).toNNReal) 1 :=
  have hreg := HeatFlowRegularity.heatFlowRegular_gaussianReal (gaussianReal 1 1)
    (integrable_sq_gauss 1 1) one_pos
  LogSobolevExtension.heatKL_le_of_functionalLSI_of_integrable _ _ one_pos (by norm_num)
    (GaussianFunctionalLSI.functionalLSI_heatKernel_comp_of_targetLSI _ zero_le_one gross_gauss)
    (hreg.integrable_kl 1 (Set.mem_Ioi.2 one_pos))
    (hreg.integrable_fisher 1 (Set.mem_Ioi.2 one_pos))

open LogSobolevPi in
/-- Gross's inequality on `Fin 2 → ℝ`: `FunctionalLSIPi N(0, I₂) 1`. -/
theorem gross_gauss_pi :
    FunctionalLSIPi (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 : ℝ).toNNReal) 1 :=
  GaussianFunctionalLSIPi.functionalLSIPi_gaussian 1 one_pos

open LogSobolevPi in
/-- KL-6 Holley–Stroock on `Fin 2 → ℝ` with `W x = sin x₀`. -/
theorem tilt_pi :
    FunctionalLSIPi
      (HolleyStroock.tilt (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 : ℝ).toNNReal)
      fun x => Real.sin (x 0)) (1 * Real.exp (1 - -1)) :=
  GaussianFunctionalLSIPi.functionalLSIPi_tilt gross_gauss_pi zero_le_one (by fun_prop)
    (fun x => Real.neg_one_le_sin (x 0)) (fun x => Real.sin_le_one (x 0))

open LogSobolevPi in
/-- KL-6 convolution on `Fin 2 → ℝ`. -/
theorem convolution_pi :
    FunctionalLSIPi (((Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 : ℝ).toNNReal).prod
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 : ℝ).toNNReal)).map
        (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 + p.2)) (1 + 1) :=
  LogSobolevTensorPi.functionalLSIPi_map_add gross_gauss_pi gross_gauss_pi zero_le_one

open LogSobolevPi in
/-- KL-6 Bakry–Émery for the separable potential `∑ᵢ (xᵢ²/2 + xᵢ⁴)` on `Fin 2 → ℝ`. -/
theorem bakryEmery_sep :
    FunctionalLSIPi (ProximalPi.targetPi (ProximalSharpPi.sepPotential
      fun (_ : Fin 2) (x : ℝ) => x ^ 2 / 2 + x ^ 4)) (1 / 1) :=
  BakryEmeryPi.functionalLSIPi_targetPi_sepPotential one_pos fun _ => convexOn_quartic

/-- `x ↦ (x₀ + x₁)²` is convex on `Fin 2 → ℝ` (helper, non-separable). -/
theorem convexOn_cross :
    ConvexOn ℝ Set.univ fun x : Fin 2 → ℝ =>
      (ProximalSharpPi.gaussPotentialPi 1 x + (x 0 + x 1) ^ 2) -
        ProximalSharpPi.gaussPotentialPi 1 x := by
  have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).comp_linearMap
    ((LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) + LinearMap.proj 1)
  refine h.congr fun x _ => ?_
  simp

open LogSobolevPi in
/-- KL-6 general Bakry–Émery on `Fin 2 → ℝ` for the non-separable potential
`|x|²/2 + (x₀ + x₁)²`. -/
theorem bakryEmery_general :
    FunctionalLSIPi (ProximalPi.targetPi fun x : Fin 2 → ℝ =>
      ProximalSharpPi.gaussPotentialPi 1 x + (x 0 + x 1) ^ 2) (1 / 1) :=
  BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn one_pos convexOn_cross

/-- KL-6 Prékopa–Leindler with `u = v = w = 1_{B(0,1)}` on `Fin 2 → ℝ` (finite nonzero
integrals; the inequality is an equality here). -/
theorem prekopa_ball {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ x, (Metric.ball (0 : Fin 2 → ℝ) 1).indicator 1 x) ^ t *
        (∫⁻ x, (Metric.ball (0 : Fin 2 → ℝ) 1).indicator 1 x) ^ (1 - t) ≤
      ∫⁻ x, (Metric.ball (0 : Fin 2 → ℝ) 1).indicator (1 : (Fin 2 → ℝ) → ℝ≥0∞) x := by
  refine PrekopaLeindler.prekopa_leindler ht0 ht1 (measurable_one.indicator measurableSet_ball)
    (measurable_one.indicator measurableSet_ball) (measurable_one.indicator measurableSet_ball)
    fun x y => ?_
  by_cases hx : x ∈ Metric.ball (0 : Fin 2 → ℝ) 1
  · by_cases hy : y ∈ Metric.ball (0 : Fin 2 → ℝ) 1
    · have hm := (convex_ball (0 : Fin 2 → ℝ) 1) hx hy (a := t) (b := 1 - t) ht0.le
        (by linarith) (by ring)
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (by linarith : 0 < 1 - t)]
  · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ht0]

/-- `(e^{x/2})' = e^{x/2}/2` (helper). -/
theorem deriv_exp_half (x : ℝ) :
    deriv (fun x : ℝ => Real.exp (x / 2)) x = Real.exp (x / 2) / 2 := by
  have : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
    ((hasDerivAt_id x).div_const 2).exp
  rw [this.deriv]; ring

/-- `(e^{x/2})² = eˣ` (helper). -/
theorem sq_exp_half (x : ℝ) : Real.exp (x / 2) ^ 2 = Real.exp x := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- KL-6 extension to unbounded test functions: `g = e^{x/2}` (unbounded, no positive
lower bound) under `N(0, 1)`; all integrability hypotheses discharged. -/
theorem extension_exp :
    ent (gaussianReal 0 (1 : ℝ).toNNReal) (fun x => Real.exp (x / 2) ^ 2) ≤
      2 * 1 * ∫ x, deriv (fun x : ℝ => Real.exp (x / 2)) x ^ 2
        ∂(gaussianReal 0 (1 : ℝ).toNNReal) := by
  have hE : Integrable (fun x : ℝ => Real.exp x) (gaussianReal 0 (1 : ℝ).toNNReal) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := (1 : ℝ).toNNReal) 1
  have hE2 : Integrable (fun x : ℝ => Real.exp (2 * x)) (gaussianReal 0 (1 : ℝ).toNNReal) :=
    integrable_exp_mul_gaussianReal 2
  refine LogSobolevExtension.ent_sq_le_of_functionalLSI gross_gauss zero_le_one
    (fun x => Real.exp_pos _) (by fun_prop) ?_ ?_ ?_ ?_
  · rw [show deriv (fun x : ℝ => Real.exp (x / 2)) = fun x => Real.exp (x / 2) / 2 from
      funext deriv_exp_half]
    fun_prop
  · simp_rw [deriv_exp_half, div_pow, sq_exp_half]; exact hE.div_const _
  · simp_rw [sq_exp_half]; exact hE
  · simp_rw [sq_exp_half, Real.log_exp]
    refine (hE2.add (integrable_const 1)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos x)]
    simp only [Pi.add_apply]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
      have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
        rw [← Real.exp_add]; ring_nf
      nlinarith [Real.exp_pos x]
    · rw [abs_of_neg hx]
      have h1 : -x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
      have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos x, Real.exp_pos (2 * x)]


open Matrix

/-- KL-5(a) on `Fin 2 → ℝ` (`GaussianLSIPi.heatKL_le_heatFisher_gaussian`) with
`ρ = N(0, 2I)`, `π = N(0, I)`, `t = 1` (hypotheses discharged). -/
theorem lsi_heat_pi :
    HeatKernelPi.heatKL (Measure.pi fun _ : Fin 2 => gaussianReal 0 (2 : ℝ).toNNReal)
        (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 : ℝ).toNNReal) 1
      ≤ (1 + 1) / 2 * HeatFlowDeBruijnPi.heatFisher
        (Measure.pi fun _ : Fin 2 => gaussianReal 0 (2 : ℝ).toNNReal)
        (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 : ℝ).toNNReal) 1 :=
  GaussianLSIPi.heatKL_le_heatFisher_gaussian _ one_pos
    (GaussianLSIPi.gaussian_hypotheses_satisfiable 2).1 one_pos

/-- ID-1 applied to `φ = id`: `E[(X - m) X] = v` for `X ~ N(m, v)` (hypotheses
discharged). -/
theorem stein_id (m : ℝ) (v : ℝ≥0) :
    ∫ x, (x - m) * x ∂(gaussianReal m v) = v * ∫ _x, (1 : ℝ) ∂(gaussianReal m v) := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal m v) := by
    simpa using (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl
  refine GaussianStein.integral_sub_mul_eq_var_mul_integral_deriv (fun x => hasDerivAt_id x)
    ?_ (integrable_const _)
  refine (h2.sub (h1.const_mul m)).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply]; ring

/-- A smooth compactly supported bump on `Fin 2 → ℝ`. -/
noncomputable def bump2 : ContDiffBump (0 : Fin 2 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump is `C²` (helper). -/
theorem bump2_contDiff : ContDiff ℝ 2 (bump2 : (Fin 2 → ℝ) → ℝ) := bump2.contDiff

/-- The bump is not identically zero: it equals `1` at the origin. -/
theorem bump2_ne : (bump2 : (Fin 2 → ℝ) → ℝ) 0 = 1 :=
  bump2.one_of_mem_closedBall (by simpa using bump2.rIn_pos.le)

/-- ID-1 (`d`-dimensional) applied to the non-zero bump `bump2`. -/
theorem stein_pi_bump (i : Fin 2) :
    ∫ z, z i * (bump2 : (Fin 2 → ℝ) → ℝ) z ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, partialDeriv i (bump2 : (Fin 2 → ℝ) → ℝ) z ∂(Measure.pi fun _ => gaussianReal 0 1) :=
  GaussianStein.integral_coord_mul_eq_integral_partialDeriv bump2.contDiff
    bump2.hasCompactSupport i

/-- ID-3 weak generator identity on `Fin 2 → ℝ` with `b = 0`, `D = 1`, `p ≡ 1` and the
bump as test function (hypotheses discharged). -/
theorem weak_generator_bump :
    ∫ x, ((0 : Fin 2 → ℝ) ⬝ᵥ grad (bump2 : (Fin 2 → ℝ) → ℝ) x +
        1 * laplacian (bump2 : (Fin 2 → ℝ) → ℝ) x) * (fun _ => (1 : ℝ)) x =
      ∫ x, (((0 : Fin 2 → ℝ) - (1 : ℝ) • score (fun _ => (1 : ℝ)) x) ⬝ᵥ
        grad (bump2 : (Fin 2 → ℝ) → ℝ) x) * (fun _ => (1 : ℝ)) x :=
  ScoreFlowWeak.integral_generator_eq_score_flow_generator (b := fun _ => 0) 1
    continuous_const contDiff_const (fun _ => one_pos) bump2.contDiff bump2.hasCompactSupport

/-- ID-3 preconditioned identity with `A = I`, `s⋆ = 0`, `p ≡ 1`, bump test function. -/
theorem precond_generator_bump :
    ∫ x, (((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (0 : Fin 2 → ℝ)) ⬝ᵥ
        grad (bump2 : (Fin 2 → ℝ) → ℝ) x +
        weightedLaplacian 1 (bump2 : (Fin 2 → ℝ) → ℝ) x) * (fun _ => (1 : ℝ)) x =
      ∫ x, (((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ((0 : Fin 2 → ℝ) - score (fun _ => (1 : ℝ)) x)) ⬝ᵥ
        grad (bump2 : (Fin 2 → ℝ) → ℝ) x) * (fun _ => (1 : ℝ)) x :=
  ScoreFlowWeak.integral_preconditioned_generator_eq_klFlow_generator (sStar := fun _ => 0)
    Matrix.transpose_one continuous_const contDiff_const (fun _ => one_pos) bump2.contDiff
    bump2.hasCompactSupport

/-- Partial derivatives of a constant vanish (helper). -/
theorem partialDeriv_const {d : ℕ} (i : Fin d) (c : ℝ) :
    partialDeriv i (fun _ : Fin d → ℝ => c) = fun _ => 0 := by
  funext x; simp [partialDeriv]

/-- ID-4 reverse Fokker–Planck, trivial instance `p ≡ 1`, `b = 0`, `g = 1`. -/
theorem reverseFP_const (T : ℝ) :
    ∀ s x, HasDerivAt (fun s => ReverseTime.timeReversal T (fun _ _ => (1 : ℝ)) s x)
      (ReverseTime.fpRHS (ReverseTime.reverseDrift T (fun _ _ => (0 : Fin 2 → ℝ)) (fun _ => 1)
        (fun _ _ => 1)) (fun s => (fun _ => (1 : ℝ)) (T - s))
        (ReverseTime.timeReversal T (fun _ _ => (1 : ℝ))) s x) s := by
  refine ReverseTime.reverse_fokkerPlanck T (fun t x => ?_) (fun _ => contDiff_const)
    (fun _ _ => one_pos) (fun _ => differentiable_const _)
  simpa [ReverseTime.fpRHS, divergence, laplacian, partialDeriv_const] using
    hasDerivAt_const t (1 : ℝ)

/-- `∂₀ e^{y₀ + c} = e^{y₀ + c}` on `Fin 1 → ℝ` (helper). -/
theorem partialDeriv_exp (c : ℝ) :
    partialDeriv 0 (fun y : Fin 1 → ℝ => Real.exp (y 0 + c)) =
      fun y => Real.exp (y 0 + c) := by
  funext y
  have h : HasFDerivAt (fun y : Fin 1 → ℝ => Real.exp (y 0 + c))
      (Real.exp (y 0 + c) • ContinuousLinearMap.proj (0 : Fin 1)) y :=
    ((hasFDerivAt_apply 0 y).add_const c).exp
  simp [partialDeriv, h.fderiv]

/-- ID-4 reverse Fokker–Planck, non-trivial instance on `Fin 1 → ℝ`:
`p(t, y) = e^{y₀ + t/2}` solves the heat equation (`b = 0`, `g = 1`) for all `t ∈ ℝ`, and the
reversed density solves the reverse equation with drift `∇ log p = 1`. -/
theorem reverseFP_exp (T : ℝ) :
    ∀ s x, HasDerivAt (fun s => ReverseTime.timeReversal T
        (fun t (y : Fin 1 → ℝ) => Real.exp (y 0 + t / 2)) s x)
      (ReverseTime.fpRHS (ReverseTime.reverseDrift T (fun _ _ => (0 : Fin 1 → ℝ)) (fun _ => 1)
        (fun t y => Real.exp (y 0 + t / 2))) (fun s => (fun _ => (1 : ℝ)) (T - s))
        (ReverseTime.timeReversal T (fun t y => Real.exp (y 0 + t / 2))) s x) s := by
  refine ReverseTime.reverse_fokkerPlanck T (fun t x => ?_) (fun _ => by fun_prop)
    (fun _ _ => Real.exp_pos _) (fun _ => differentiable_const _)
  have h : HasDerivAt (fun t => Real.exp (x 0 + t / 2)) (Real.exp (x 0 + t / 2) * (1 / 2)) t :=
    (((hasDerivAt_id t).div_const 2).const_add (x 0)).exp
  convert h using 1
  simp [ReverseTime.fpRHS, divergence, laplacian, partialDeriv_exp, partialDeriv_const]
  ring

/-- ID-4 probability-flow rewriting at every point for `p = e^{y₀}`, `b = 0`, `g = 1`. -/
theorem probFlow_exp (x : Fin 1 → ℝ) :
    -divergence (fun y i => (fun _ _ => (0 : ℝ)) y i * Real.exp (y 0 + 0)) x +
        1 ^ 2 / 2 * laplacian (fun y : Fin 1 → ℝ => Real.exp (y 0 + 0)) x =
      -divergence (fun y i => ((fun _ _ => (0 : ℝ)) y i - 1 ^ 2 / 2 *
        score (fun y : Fin 1 → ℝ => Real.exp (y 0 + 0)) y i) * Real.exp (y 0 + 0)) x :=
  ReverseTime.probFlow_rewrite 1
    (Eventually.of_forall fun y => ⟨by fun_prop, Real.exp_pos _⟩)
    (fun i => by fin_cases i; simp only [Fin.zero_eta, partialDeriv_exp]; fun_prop)
    (differentiableAt_const _)

/-- Fréchet derivative of `y ↦ e^{-y₀²}` on `Fin 1 → ℝ` (helper). -/
theorem hasFDerivAt_gaussExp (y : Fin 1 → ℝ) :
    HasFDerivAt (fun y : Fin 1 → ℝ => Real.exp (-(y 0) ^ 2))
      (Real.exp (-(y 0) ^ 2) • (-((2 : ℕ) * y 0 ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) y := by
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) 0 y).pow 2).neg.exp
  convert h using 2
  ext v; simp

/-- `∂₀ e^{-y₀²} = -2 y₀ e^{-y₀²}` (helper). -/
theorem partialDeriv_gaussExp :
    partialDeriv 0 (fun y : Fin 1 → ℝ => Real.exp (-(y 0) ^ 2)) =
      fun y => -(2 * y 0) * Real.exp (-(y 0) ^ 2) := by
  funext y
  simp [partialDeriv, (hasFDerivAt_gaussExp y).fderiv]
  ring

/-- Integrability transfers from `ℝ` to `Fin 1 → ℝ` (helper). -/
theorem integrable_fin1 {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable fun y : Fin 1 → ℝ => g (y 0) :=
  ((volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).2 hg

/-- ID-2 zero-mean score for the (unnormalised) Gaussian density `e^{-y₀²}` on
`Fin 1 → ℝ` (hypotheses discharged). -/
theorem score_mean_zero_gauss :
    ∫ x, score (fun y : Fin 1 → ℝ => Real.exp (-(y 0) ^ 2)) x 0 *
      Real.exp (-(x 0) ^ 2) = 0 :=
  DensityStein.integral_score_mul_eq_zero (fun _ => Real.exp_pos _)
    (fun y => (hasFDerivAt_gaussExp y).differentiableAt) 0
    (integrable_fin1 (g := fun t => Real.exp (-t ^ 2)) (by
      simpa using integrable_exp_neg_mul_sq (b := 1) one_pos))
    (by
      rw [partialDeriv_gaussExp]
      refine integrable_fin1 (g := fun t => -(2 * t) * Real.exp (-t ^ 2)) ?_
      have := (integrable_mul_exp_neg_mul_sq (b := 1) one_pos).const_mul (-2)
      refine this.congr (ae_of_all _ fun t => ?_)
      simp only [neg_mul, one_mul]; ring)


end FormalizeSampling.Audit.KLID
