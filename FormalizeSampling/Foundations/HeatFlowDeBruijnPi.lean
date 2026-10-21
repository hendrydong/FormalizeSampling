module

public import FormalizeSampling.Foundations.HeatKernelPi
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# de Bruijn's identity along the isotropic heat flow on `Fin d → ℝ`

Status: **Verified** for the heat equation of isotropic Gaussian convolutions, the de Bruijn
identity for relative entropy and the derived heat-flow contraction, under the explicit
regularity hypotheses `HeatFlowRegularPi`; the contraction `heatKL_le_div_of_regular` is then
**Conditional** only on the log-Sobolev inequality of `π_t` along the flow at positive times
`t ∈ (0, η)` (see `GaussianLSIPi` for Gaussian targets). This is the `Fin d → ℝ` version of
`Foundations/HeatFlowDeBruijn.lean`.

Notation: `φ_t = heatDensityPi t` is the `N(0, t I)` density on `Fin d → ℝ` (`t` = variance per
coordinate). For a measure `ρ` on `Fin d → ℝ`, `p_t = heatFlowDensityPi ρ t = ρ * φ_t`, with
gradient `heatFlowGradPi ρ t` and Hessian `heatFlowHessPi ρ t`; for a finite `ρ` and `t > 0`,
`p_t` is the Lebesgue density of `ρ_t = heatKernelPi t ∘ₘ ρ` (`heatKernelPi_comp_eq_withDensity`).
Euclidean squared norms are `∑ᵢ zᵢ²` or `v ⬝ᵥ v`; Fréchet derivatives are written through their
gradients with `dotCLM g v = g ⬝ᵥ v`. All divergences are `KL(ρ_t‖π_t)`, evolving law first.

## Main results

* `hasFDerivAt_heatDensityPi`, `hasFDerivAt_heatGradPi`, `hasDerivAt_heatDensityPi_t`: gradient,
  Hessian and heat equation `∂_t φ_t = ½ Δφ_t` of the kernel, with uniform bounds
  `abs_heatGradPi_le`, `abs_heatHessPi_le`, `abs_heatLapPi_le`.
* `hasFDerivAt_heatFlowDensityPi`, `hasFDerivAt_heatFlowGradPi`,
  `hasDerivAt_heatFlowDensityPi_t` (Verified, `ρ` any finite measure): `∇p_t`, `∇²p_t` and the
  heat equation `∂_t p_t = ½ Δp_t`; `heatFlowDensityPi_pos`; `heatKernelPi_comp_eq_withDensity`.
* `integral_klRate_eq` (Verified): integration by parts
  `∫ ∂_t[p log(p/q)] = -½ ∫ p |∇ log(p/q)|²`, one coordinate at a time through Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (via
  `KLTransport.integral_partialDeriv_eq_zero`), with vanishing boundary flux replaced by
  integrability of each flux coordinate `klFlux i` and of its partial derivative `klFluxDeriv i`.
* `hasDerivAt_integral_klIntegrand` (Verified): abstract `d`-dimensional de Bruijn identity.
* `toReal_klDiv_withDensity_eq_integral`: `KL(p‖q).toReal = ∫ p log(p/q)` for densities.
* `hasDerivAt_heatKL` (Verified under `HeatFlowRegularPi`): `d/dt KL(ρ_t‖π_t) = -½ I(ρ_t‖π_t)`
  for `t > 0`, with `I = heatFisher`.
* `heatKL_le_div_of_regular`, `toReal_klDiv_heatKernelPi_le_of_regular`:
  `KL(ρ_η‖π_η) ≤ KL(ρ‖π) / (1 + α η)` given `HeatFlowRegularPi` on `(0, η]` and the LSI
  `2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` only for `t ∈ (0, η)`; no regularity and no LSI at
  `t = 0`.
* `heatFlowRegularPi_self`: `HeatFlowRegularPi ρ ρ (Ioi 0)` (non-vacuity).
* `NoiseScorePreconditioned.gaussDensity μ = heatDensityPi 1 (· - μ)`, the Lebesgue density of
  `N(μ, I)` (`NoiseScorePreconditioned.pi_gaussianReal_one_eq_withDensity`), with its gradient,
  positivity and score `NoiseScorePreconditioned.score_gaussDensity`: `∇log p(x) = -x + μ`.

## Not proved here

* The fields of `HeatFlowRegularPi` (integrability of `p_t log(p_t/q_t)`, of the Fisher
  integrand, of the flux coordinates and their partial derivatives, and local-in-time domination
  of the KL time-derivative) are not derived here from conditions on `ρ, π` themselves; they
  are derived in `HeatFlowRegularityPerturbedPi` (Gaussian `π` and bounded perturbations,
  finite second moment of `ρ`) and `HeatFlowRegularityWarmPi` (warm `ρ`).
* The LSI of `π * N(0, t I)` for non-Gaussian `π` (the Gaussian case is in `GaussianLSIPi`; the
  convolution route from a functional LSI of `π` is
  `LogSobolevTensorPi.functionalLSIPi_heatKernelPi_comp`, used in `ProximalLSIPi`).
* The `d`-dimensional proximal sampler step itself (only the forward heat-flow step is treated
  here; see `ProximalGaussianPi`, `ProximalLSIPi`), and the `d = 1` specialisation to
  `Foundations/HeatFlowDeBruijn.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.HeatFlowDeBruijnPi

open FormalizeSampling.HeatKernelPi
open FormalizeSampling.HeatFlowDeBruijn (heatDensity heatDensityD2 heatDensity_pos
  heatDensity_le hasDerivAt_heatDensity_t)

variable {d : ℕ}

/-! ### Linear forms given by a coefficient vector -/

/-- The continuous linear form `v ↦ g ⬝ᵥ v = ∑ᵢ gᵢ vᵢ` on `Fin d → ℝ` (used to write Fréchet
derivatives through their gradient `g`). -/
noncomputable def dotCLM (g : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, g i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i

/-- Evaluation of `dotCLM`: `dotCLM g v = g ⬝ᵥ v`. -/
theorem dotCLM_apply (g v : Fin d → ℝ) : dotCLM g v = g ⬝ᵥ v := by
  simp [dotCLM, dotProduct]

/-- `dotCLM g` applied to the `i`-th basis vector is `g i`. -/
theorem dotCLM_single (g : Fin d → ℝ) (i : Fin d) : dotCLM g (Pi.single i 1) = g i := by
  rw [dotCLM_apply, dotProduct_single, mul_one]

/-- Operator-norm bound: `‖dotCLM g‖ ≤ ∑ᵢ |gᵢ|` (sup norm on `Fin d → ℝ`). -/
theorem norm_dotCLM_le (g : Fin d → ℝ) : ‖dotCLM g‖ ≤ ∑ i, |g i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
    fun v => ?_
  rw [dotCLM_apply, Real.norm_eq_abs, dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v i) (abs_nonneg _)

/-- If `g` is continuous then so is `x ↦ dotCLM (g x)`. -/
theorem continuous_dotCLM {α : Type*} [TopologicalSpace α] {g : α → Fin d → ℝ}
    (hg : Continuous g) : Continuous fun x => dotCLM (g x) := by
  unfold dotCLM
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hg).smul continuous_const

/-- Two linear forms `dotCLM g`, `dotCLM g'` agree iff `g = g'`; here, the direction used:
if `∀ v, dotCLM g v = L v` then `L = dotCLM g`. -/
theorem eq_dotCLM_of_apply {g : Fin d → ℝ} {L : (Fin d → ℝ) →L[ℝ] ℝ}
    (h : ∀ v, L v = g ⬝ᵥ v) : L = dotCLM g :=
  ContinuousLinearMap.ext fun v => by rw [h, dotCLM_apply]

/-! ### Derivatives of the isotropic heat kernel -/

/-- The gradient of the heat kernel: `∇ heatDensityPi t z = -(z / t) heatDensityPi t z`
(`hasFDerivAt_heatDensityPi`). -/
noncomputable def heatGradPi (t : ℝ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => -(z i / t) * heatDensityPi t z

/-- The Hessian of the heat kernel:
`∂ᵢ∂ⱼ heatDensityPi t z = (zᵢ zⱼ / t² - δᵢⱼ / t) heatDensityPi t z`. -/
noncomputable def heatHessPi (t : ℝ) (z : Fin d → ℝ) (i j : Fin d) : ℝ :=
  (z i * z j / t ^ 2 - if i = j then 1 / t else 0) * heatDensityPi t z

/-- The Laplacian of the heat kernel, `Δ heatDensityPi t z = ∑ᵢ ∂ᵢ² heatDensityPi t z`. -/
noncomputable def heatLapPi (t : ℝ) (z : Fin d → ℝ) : ℝ := ∑ i, heatHessPi t z i i

/-- The squared Euclidean norm `∑ᵢ zᵢ²` has Fréchet derivative `v ↦ (2 z) ⬝ᵥ v`. -/
theorem hasFDerivAt_sum_sq (z : Fin d → ℝ) :
    HasFDerivAt (fun z : Fin d → ℝ => ∑ i, z i ^ 2) (dotCLM fun i => 2 * z i) z := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hasFDerivAt_apply (𝕜 := ℝ) i z).pow 2)
  refine h.congr_fderiv (eq_dotCLM_of_apply fun v => ?_)
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => by simp

/-- **Gradient of the heat kernel.** For every `t` and `z`,
`HasFDerivAt (heatDensityPi t) (dotCLM (heatGradPi t z)) z`, i.e.
`∇ heatDensityPi t z = -(z / t) heatDensityPi t z`. -/
theorem hasFDerivAt_heatDensityPi (t : ℝ) (z : Fin d → ℝ) :
    HasFDerivAt (heatDensityPi t) (dotCLM (heatGradPi t z)) z := by
  set C := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d
  have he : heatDensityPi (d := d) t = fun z =>
      C * Real.exp (-(2 * t)⁻¹ * ∑ i, z i ^ 2) := by
    funext z; rw [heatDensityPi_eq_exp]; congr 2; ring
  have h := (((hasFDerivAt_sum_sq z).const_mul (-(2 * t)⁻¹)).exp).const_mul C
  rw [he]
  refine h.congr_fderiv (eq_dotCLM_of_apply fun v => ?_)
  simp only [heatGradPi, he, smul_apply, dotCLM_apply, smul_eq_mul,
    dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  field_simp

/-- **Hessian of the heat kernel.** For every `t`, `z` and `i`, the `i`-th gradient coordinate
`z ↦ heatGradPi t z i` has Fréchet derivative `v ↦ ∑ⱼ heatHessPi t z i j vⱼ`. -/
theorem hasFDerivAt_heatGradPi (t : ℝ) (i : Fin d) (z : Fin d → ℝ) :
    HasFDerivAt (fun z => heatGradPi t z i) (dotCLM fun j => heatHessPi t z i j) z := by
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) i z).const_mul (-t⁻¹))).mul
    (hasFDerivAt_heatDensityPi t z)
  have e : (fun z => heatGradPi t z i) = fun z => -t⁻¹ * z i * heatDensityPi t z := by
    funext z; simp only [heatGradPi]; ring
  rw [e]
  refine h.congr_fderiv (eq_dotCLM_of_apply fun v => ?_)
  have h1 : ∑ j, heatGradPi t z j * v j = -(heatDensityPi t z / t) * ∑ j, z j * v j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; simp only [heatGradPi]; ring
  have h2 : ∑ j, heatHessPi t z i j * v j =
      z i * heatDensityPi t z / t ^ 2 * ∑ j, z j * v j - 1 / t * heatDensityPi t z * v i := by
    simp only [heatHessPi, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [add_apply, smul_apply, dotCLM_apply, dotProduct, smul_eq_mul,
    ContinuousLinearMap.proj_apply, h1, h2]
  ring

/-- `heatLapPi` in closed form:
`Δ heatDensityPi t z = (∑ᵢ (zᵢ² / t² - 1 / t)) heatDensityPi t z`. -/
theorem heatLapPi_eq (t : ℝ) (z : Fin d → ℝ) :
    heatLapPi t z = ∑ i, (z i ^ 2 / t ^ 2 - 1 / t) * heatDensityPi t z := by
  unfold heatLapPi heatHessPi
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sq]

/-- **Heat equation for the isotropic kernel.** For `t > 0` and every `z`,
`∂_t heatDensityPi t z = ½ Δ heatDensityPi t z = heatLapPi t z / 2`. -/
theorem hasDerivAt_heatDensityPi_t {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) :
    HasDerivAt (fun s => heatDensityPi s z) (heatLapPi t z / 2) t := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun i s => heatDensity s (z i)) fun i _ => hasDerivAt_heatDensity_t ht (z i)
  refine h.congr_deriv ?_
  rw [heatLapPi_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [heatDensityPi, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_eq_mul, heatDensityD2]
  ring

/-! ### Uniform bounds on the kernel and its derivatives -/

/-- Elementary Gaussian tail bound: `u exp(-u / (2t)) ≤ 2t` for `u ≥ 0`, `t > 0`. -/
theorem mul_exp_neg_le {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    u * Real.exp (-u / (2 * t)) ≤ 2 * t := by
  have h1 := Real.add_one_le_exp (u / (2 * t))
  have h2 : Real.exp (-u / (2 * t)) * Real.exp (u / (2 * t)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have h3 : u = 2 * t * (u / (2 * t)) := by field_simp
  have h4 := Real.exp_pos (-u / (2 * t))
  have h5 : 0 ≤ u / (2 * t) := by positivity
  calc u * Real.exp (-u / (2 * t))
      = 2 * t * (u / (2 * t)) * Real.exp (-u / (2 * t)) := by rw [← h3]
    _ ≤ 2 * t * Real.exp (u / (2 * t)) * Real.exp (-u / (2 * t)) := by gcongr; linarith
    _ = 2 * t := by rw [mul_assoc, mul_comm (Real.exp _), h2, mul_one]

/-- `exp(-u / (2t)) ≤ 1` for `u ≥ 0`, `t > 0`. -/
theorem exp_neg_le_one {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) : Real.exp (-u / (2 * t)) ≤ 1 :=
  Real.exp_le_one_iff.2 (by rw [neg_div]; linarith [div_nonneg hu (by positivity : 0 ≤ 2 * t)])

/-- Uniform bound on the gradient of the heat kernel, `t > 0`:
`|∂ᵢ heatDensityPi t z| ≤ (1 + 2t) / t · (2π t)^{-d/2}`. -/
theorem abs_heatGradPi_le {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (i : Fin d) :
    |heatGradPi t z i| ≤ (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by
  set S := ∑ j, z j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hzi : z i ^ 2 ≤ S := Finset.single_le_sum (f := fun j => z j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hE := mul_exp_neg_le ht hS
  have hE1 := exp_neg_le_one ht hS
  have hE0 := Real.exp_pos (-S / (2 * t))
  have hz : |z i| ≤ 1 + S := by nlinarith [abs_nonneg (z i), sq_abs (z i)]
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by positivity
  have hφ : heatDensityPi t z = (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-S / (2 * t)) :=
    heatDensityPi_eq_exp t z
  have hCE : 0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-S / (2 * t)) := by positivity
  rw [heatGradPi, hφ, abs_mul, abs_neg, abs_div, abs_of_pos ht, abs_of_nonneg hCE]
  have key : |z i| * Real.exp (-S / (2 * t)) ≤ 1 + 2 * t := by nlinarith
  calc |z i| / t * ((Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-S / (2 * t)))
      = (|z i| * Real.exp (-S / (2 * t))) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by ring
    _ ≤ (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by gcongr

/-- Uniform bound on the Hessian of the heat kernel, `t > 0`:
`|∂ᵢ∂ⱼ heatDensityPi t z| ≤ 3 / t · (2π t)^{-d/2}`. -/
theorem abs_heatHessPi_le {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (i j : Fin d) :
    |heatHessPi t z i j| ≤ 3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by
  set S := ∑ j, z j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hzi : z i ^ 2 ≤ S := Finset.single_le_sum (f := fun j => z j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hzj : z j ^ 2 ≤ S := Finset.single_le_sum (f := fun j => z j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  have hzz : |z i * z j| ≤ S := by
    rw [abs_mul]
    nlinarith [sq_abs (z i), sq_abs (z j), sq_nonneg (|z i| - |z j|)]
  have hE := mul_exp_neg_le ht hS
  have hE1 := exp_neg_le_one ht hS
  have hE0 := Real.exp_pos (-S / (2 * t))
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by positivity
  have hq : |z i * z j / t ^ 2 - (if i = j then 1 / t else 0)| ≤ S / t ^ 2 + 1 / t := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]; gcongr
    · split_ifs <;> simp [abs_of_pos ht, ht.le]
  have hφ : heatDensityPi t z = (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-S / (2 * t)) :=
    heatDensityPi_eq_exp t z
  rw [heatHessPi, hφ, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-S / (2 * t)))]
  have key : |z i * z j / t ^ 2 - (if i = j then 1 / t else 0)| * Real.exp (-S / (2 * t))
      ≤ 3 / t := by
    have h2 : (S / t ^ 2 + 1 / t) * Real.exp (-S / (2 * t)) ≤ 3 / t := by
      have e1 : S / t ^ 2 * Real.exp (-S / (2 * t)) ≤ 2 / t := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) ht]; nlinarith
      have e2 : 1 / t * Real.exp (-S / (2 * t)) ≤ 1 / t := by
        have : 0 < 1 / t := by positivity
        nlinarith
      have : 3 / t = 2 / t + 1 / t := by ring
      nlinarith
    calc _ ≤ (S / t ^ 2 + 1 / t) * Real.exp (-S / (2 * t)) := by gcongr
      _ ≤ 3 / t := h2
  calc |z i * z j / t ^ 2 - (if i = j then 1 / t else 0)| *
        ((Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-S / (2 * t)))
      = (|z i * z j / t ^ 2 - (if i = j then 1 / t else 0)| * Real.exp (-S / (2 * t))) *
          (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by ring
    _ ≤ 3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by gcongr

/-- Uniform bound on the Laplacian of the heat kernel, `t > 0`:
`|Δ heatDensityPi t z| ≤ d · 3 / t · (2π t)^{-d/2}`. -/
theorem abs_heatLapPi_le {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) :
    |heatLapPi t z| ≤ d * (3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d) := by
  unfold heatLapPi
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |heatHessPi t z i i| ≤ ∑ _i : Fin d, 3 / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d :=
        Finset.sum_le_sum fun i _ => abs_heatHessPi_le ht z i i
    _ = _ := by simp

/-- `z ↦ heatGradPi t z` is continuous. -/
theorem continuous_heatGradPi (t : ℝ) : Continuous (heatGradPi (d := d) t) :=
  continuous_pi fun i => ((by fun_prop : Continuous fun z : Fin d → ℝ => -(z i / t))).mul
    (continuous_heatDensityPi t)

/-- `z ↦ heatHessPi t z i j` is continuous. -/
theorem continuous_heatHessPi (t : ℝ) (i j : Fin d) : Continuous fun z => heatHessPi t z i j :=
  (by fun_prop : Continuous fun z : Fin d → ℝ =>
    z i * z j / t ^ 2 - if i = j then 1 / t else 0).mul (continuous_heatDensityPi t)

/-- `z ↦ heatLapPi t z` is continuous. -/
theorem continuous_heatLapPi (t : ℝ) : Continuous (heatLapPi (d := d) t) :=
  continuous_finsetSum _ fun i _ => continuous_heatHessPi t i i

/-! ### Gaussian convolutions of a finite measure -/

/-- **Differentiation under the integral against a finite measure.** Let `k` be differentiable
on `Fin d → ℝ` with gradient `g` (`HasFDerivAt k (dotCLM (g z)) z`), `g` continuous, `|k| ≤ A`
and `|gᵢ| ≤ B`. Then for a finite measure `ρ`, `y ↦ ∫ k(y - x) dρ(x)` has gradient
`∫ g(y - x) dρ(x)`. -/
theorem hasFDerivAt_integral_sub (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ]
    {k : (Fin d → ℝ) → ℝ} {g : (Fin d → ℝ) → Fin d → ℝ}
    (hk : ∀ z, HasFDerivAt k (dotCLM (g z)) z) (hg : Continuous g) {A B : ℝ}
    (hkb : ∀ z, |k z| ≤ A) (hgb : ∀ z i, |g z i| ≤ B) (y : Fin d → ℝ) :
    HasFDerivAt (fun y => ∫ x, k (y - x) ∂ρ) (dotCLM fun i => ∫ x, g (y - x) i ∂ρ) y := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun z => (hk z).continuousAt
  have hF' : ∀ y : Fin d → ℝ, Continuous fun x => dotCLM (g (y - x)) := fun y =>
    continuous_dotCLM (hg.comp (by fun_prop))
  have hbd : ∀ z, ‖dotCLM (g z)‖ ≤ d * B := fun z =>
    (norm_dotCLM_le _).trans (by
      calc ∑ i, |g z i| ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => hgb z i
        _ = d * B := by simp)
  have hgi : ∀ i, Integrable (fun x => g (y - x) i) ρ := fun i =>
    Integrable.of_bound (((continuous_apply i).comp (hg.comp (by fun_prop)))).aestronglyMeasurable
      B (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb _ i)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ρ) (s := univ) univ_mem
    (F := fun y x => k (y - x)) (F' := fun y x => dotCLM (g (y - x))) (bound := fun _ => d * B)
    (Eventually.of_forall fun y => (hkc.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hkc.comp (by fun_prop)).aestronglyMeasurable A
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hkb _))
    (hF' y).aestronglyMeasurable
    (Eventually.of_forall fun x y _ => hbd _) (integrable_const _)
    (Eventually.of_forall fun x y _ => by
      have := (hk (y - x)).comp y ((hasFDerivAt_id y).sub_const x)
      simpa [Function.comp_def] using this)
  refine h.congr_fderiv (eq_dotCLM_of_apply fun v => ?_)
  rw [ContinuousLinearMap.integral_apply (Integrable.of_bound (hF' y).aestronglyMeasurable _
    (Eventually.of_forall fun x => hbd _)) v]
  simp_rw [dotCLM_apply, dotProduct]
  rw [integral_finsetSum _ fun i _ => (hgi i).mul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _

/-- The heat-flow density of a measure `ρ` on `Fin d → ℝ`:
`heatFlowDensityPi ρ t y = ∫ φ_t(y - x) dρ(x)` with `φ_t = heatDensityPi t`. For a finite `ρ` and
`t > 0` it is the Lebesgue density of `heatKernelPi t ∘ₘ ρ = ρ * N(0, t I)`
(`heatKernelPi_comp_eq_withDensity`). -/
noncomputable def heatFlowDensityPi (ρ : Measure (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ x, heatDensityPi t (y - x) ∂ρ

/-- The gradient of the heat-flow density, `∫ ∇φ_t(y - x) dρ(x)`
(`hasFDerivAt_heatFlowDensityPi`). -/
noncomputable def heatFlowGradPi (ρ : Measure (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => ∫ x, heatGradPi t (y - x) i ∂ρ

/-- The Hessian of the heat-flow density, `∫ ∂ᵢ∂ⱼφ_t(y - x) dρ(x)`
(`hasFDerivAt_heatFlowGradPi`). -/
noncomputable def heatFlowHessPi (ρ : Measure (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  ∫ x, heatHessPi t (y - x) i j ∂ρ

/-- The Laplacian of the heat-flow density, `∑ᵢ ∂ᵢ² p_t(y)`. -/
noncomputable def heatFlowLapPi (ρ : Measure (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∑ i, heatFlowHessPi ρ t y i i

section HF
variable (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ]

/-- For a finite measure `ρ` and `t > 0`, `y ↦ heatFlowDensityPi ρ t y` is Fréchet
differentiable with gradient `heatFlowGradPi ρ t y`. -/
theorem hasFDerivAt_heatFlowDensityPi {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    HasFDerivAt (heatFlowDensityPi ρ t) (dotCLM (heatFlowGradPi ρ t y)) y :=
  hasFDerivAt_integral_sub ρ (hasFDerivAt_heatDensityPi t) (continuous_heatGradPi t)
    (fun z => by rw [abs_of_pos (heatDensityPi_pos ht z)]; exact heatDensityPi_le ht z)
    (fun z i => abs_heatGradPi_le ht z i) y

/-- For a finite measure `ρ` and `t > 0`, each gradient coordinate `y ↦ heatFlowGradPi ρ t y i`
is Fréchet differentiable with gradient `(heatFlowHessPi ρ t y i j)ⱼ`. -/
theorem hasFDerivAt_heatFlowGradPi {t : ℝ} (ht : 0 < t) (i : Fin d) (y : Fin d → ℝ) :
    HasFDerivAt (fun y => heatFlowGradPi ρ t y i) (dotCLM fun j => heatFlowHessPi ρ t y i j) y :=
  hasFDerivAt_integral_sub ρ (k := fun z => heatGradPi t z i)
    (g := fun z j => heatHessPi t z i j) (hasFDerivAt_heatGradPi t i)
    (continuous_pi fun j => continuous_heatHessPi t i j) (fun z => abs_heatGradPi_le ht z i)
    (fun z j => abs_heatHessPi_le ht z i j) y

/-- **Heat equation for the Gaussian convolution of a finite measure.** For a finite measure `ρ`
on `Fin d → ℝ`, `t > 0` and every `y`, `p_t = ρ * φ_t` satisfies `∂_t p_t(y) = ½ Δ p_t(y)`:
`HasDerivAt (fun r => heatFlowDensityPi ρ r y) (heatFlowLapPi ρ t y / 2) t`. No density, moment
or integrability assumption on `ρ` is needed. -/
theorem hasDerivAt_heatFlowDensityPi_t {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    HasDerivAt (fun r => heatFlowDensityPi ρ r y) (heatFlowLapPi ρ t y / 2) t := by
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  set M := d * (6 / t * (Real.sqrt (Real.pi * t))⁻¹ ^ d)
  have hbd : ∀ r ∈ Ioo (t / 2) (2 * t), ∀ z : Fin d → ℝ, ‖heatLapPi r z / 2‖ ≤ M := by
    intro r hr z
    have hr0 : 0 < r := by linarith [hr.1]
    rw [Real.norm_eq_abs, abs_div, abs_two]
    have h1 := abs_heatLapPi_le hr0 z
    have h2 : (Real.sqrt (2 * Real.pi * r))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_le_sqrt (by nlinarith [hr.1, Real.pi_pos]))
    have h3 : 3 / r ≤ 6 / t := by rw [div_le_div_iff₀ hr0 ht]; linarith [hr.1]
    have h4 : (Real.sqrt (2 * Real.pi * r))⁻¹ ^ d ≤ (Real.sqrt (Real.pi * t))⁻¹ ^ d :=
      pow_le_pow_left₀ (by positivity) h2 d
    have : 0 ≤ (Real.sqrt (2 * Real.pi * r))⁻¹ ^ d := by positivity
    have : 0 ≤ 3 / r := by positivity
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc |heatLapPi r z| / 2 ≤ |heatLapPi r z| := by linarith [abs_nonneg (heatLapPi r z)]
      _ ≤ d * (3 / r * (Real.sqrt (2 * Real.pi * r))⁻¹ ^ d) := h1
      _ ≤ d * (6 / t * (Real.sqrt (Real.pi * t))⁻¹ ^ d) := by gcongr
  have hmeas : ∀ r ∈ Ioo (t / 2) (2 * t),
      AEStronglyMeasurable (fun x => heatDensityPi r (y - x)) ρ := fun r _ =>
    ((continuous_heatDensityPi r).comp (by fun_prop)).aestronglyMeasurable
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) hs
    (F := fun r x => heatDensityPi r (y - x)) (F' := fun r x => heatLapPi r (y - x) / 2)
    (bound := fun _ => M)
    (eventually_of_mem hs hmeas)
    (Integrable.of_bound (hmeas t ⟨by linarith, by linarith⟩)
      ((Real.sqrt (2 * Real.pi * t))⁻¹ ^ d)
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensityPi_pos ht _).le]; exact heatDensityPi_le ht _))
    (((continuous_heatLapPi t).comp (by fun_prop)).div_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x r hr => hbd r hr _) (integrable_const _)
    (Eventually.of_forall fun x r hr => hasDerivAt_heatDensityPi_t (by linarith [hr.1]) _)).2
  rw [integral_div] at this
  have e : heatFlowLapPi ρ t y = ∫ x, heatLapPi t (y - x) ∂ρ := by
    have hI : ∀ i, Integrable (fun x => heatHessPi t (y - x) i i) ρ := fun i =>
      Integrable.of_bound
        (((continuous_heatHessPi t i i).comp (by fun_prop : Continuous fun x => y - x))
          |>.aestronglyMeasurable) _
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_heatHessPi_le ht _ i i)
    unfold heatFlowLapPi heatFlowHessPi heatLapPi
    rw [integral_finsetSum _ fun i _ => hI i]
  rw [e]
  exact this

/-- For a nonzero finite measure `ρ` and `t > 0`, the heat-flow density is positive
everywhere: `0 < heatFlowDensityPi ρ t y`. -/
theorem heatFlowDensityPi_pos [NeZero ρ] {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    0 < heatFlowDensityPi ρ t y := by
  have hi : Integrable (fun x => heatDensityPi t (y - x)) ρ :=
    Integrable.of_bound ((continuous_heatDensityPi t).comp (by fun_prop)).aestronglyMeasurable
      ((Real.sqrt (2 * Real.pi * t))⁻¹ ^ d) (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensityPi_pos ht _).le]; exact heatDensityPi_le ht _)
  unfold heatFlowDensityPi
  rw [integral_pos_iff_support_of_nonneg (fun x => (heatDensityPi_pos ht _).le) hi]
  have : Function.support (fun x => heatDensityPi t (y - x)) = univ :=
    eq_univ_of_forall fun x => (heatDensityPi_pos ht _).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne ρ)

/-- **Law identification.** For a finite measure `ρ` on `Fin d → ℝ` and `t > 0`,
`heatKernelPi t ∘ₘ ρ = ρ * N(0, t I)` has Lebesgue density `heatFlowDensityPi ρ t`. -/
theorem heatKernelPi_comp_eq_withDensity {t : ℝ} (ht : 0 < t) :
    heatKernelPi t.toNNReal ∘ₘ ρ =
      volume.withDensity (fun y => ENNReal.ofReal (heatFlowDensityPi ρ t y)) := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_heatKernelPi _).aemeasurable, withDensity_apply _ hs]
  simp_rw [heatKernelPi_eq_withDensity ht, withDensity_apply _ hs]
  have hc : Continuous fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
      ENNReal.ofReal (heatDensityPi t (q.2 - q.1)) :=
    ENNReal.continuous_ofReal.comp ((continuous_heatDensityPi t).comp (by fun_prop))
  rw [lintegral_lintegral_swap hc.measurable.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [heatFlowDensityPi]
  refine (ofReal_integral_eq_lintegral_ofReal (f := fun x => heatDensityPi t (y - x))
    (Integrable.of_bound ((continuous_heatDensityPi t).comp (by fun_prop)).aestronglyMeasurable
      ((Real.sqrt (2 * Real.pi * t))⁻¹ ^ d) (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (heatDensityPi_pos ht _).le]; exact heatDensityPi_le ht _))
    (Eventually.of_forall fun x => (heatDensityPi_pos ht _).le)).symm

end HF

/-! ### de Bruijn's identity for two families of densities on `Fin d → ℝ` -/

section Abstract

variable {P Q : ℝ → (Fin d → ℝ) → ℝ} {PG QG : ℝ → (Fin d → ℝ) → Fin d → ℝ}
  {PH QH : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ}

/-- The relative-entropy integrand `p_t log(p_t / q_t)` of two time-indexed densities
`P t x`, `Q t x` on `Fin d → ℝ`. -/
noncomputable def klIntegrand (P Q : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  P t x * Real.log (P t x / Q t x)

/-- The time derivative of `klIntegrand` along the heat equations `∂_t P = ½ ΔP`, `∂_t Q = ½ ΔQ`
(`hasDerivAt_klIntegrand_time`): `(ΔP (log(P/Q) + 1) - (P/Q) ΔQ) / 2`, with the Hessians given as
`PH`, `QH` and `Δ = ∑ᵢ ∂ᵢ²`. -/
noncomputable def klRate (P Q : ℝ → (Fin d → ℝ) → ℝ) (PH QH : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  ((∑ i, PH t x i i) * (Real.log (P t x / Q t x) + 1) - P t x / Q t x * ∑ i, QH t x i i) / 2

/-- The relative score `∇ log(P/Q) = ∇P/P - ∇Q/Q`, with the gradients given as `PG`, `QG`. -/
noncomputable def relScore (P Q : ℝ → (Fin d → ℝ) → ℝ) (PG QG : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => PG t x i / P t x - QG t x i / Q t x

/-- The relative Fisher information integrand `P |∇ log(P/Q)|²` (Euclidean norm, written with
`dotProduct`). -/
noncomputable def fisherIntegrand (P Q : ℝ → (Fin d → ℝ) → ℝ)
    (PG QG : ℝ → (Fin d → ℝ) → Fin d → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  P t x * (relScore P Q PG QG t x ⬝ᵥ relScore P Q PG QG t x)

/-- The `i`-th coordinate of the KL flux `∇P (log(P/Q) + 1) - (P/Q) ∇Q`, whose divergence is
`2 · klRate + fisherIntegrand` (`sum_klFluxDeriv`, `hasFDerivAt_klFlux`). -/
noncomputable def klFlux (P Q : ℝ → (Fin d → ℝ) → ℝ) (PG QG : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (t : ℝ) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  PG t x i * (Real.log (P t x / Q t x) + 1) - P t x / Q t x * QG t x i

/-- The `i`-th partial derivative `∂ᵢ (klFlux i)` of the `i`-th flux coordinate:
`∂ᵢ²P (log(P/Q) + 1) - (P/Q) ∂ᵢ²Q + P (∂ᵢ log(P/Q))²` (`hasFDerivAt_klFlux`). -/
noncomputable def klFluxDeriv (P Q : ℝ → (Fin d → ℝ) → ℝ)
    (PG QG : ℝ → (Fin d → ℝ) → Fin d → ℝ) (PH QH : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (t : ℝ) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  PH t x i i * (Real.log (P t x / Q t x) + 1) - P t x / Q t x * QH t x i i +
    P t x * relScore P Q PG QG t x i ^ 2

/-- The divergence of the KL flux: `∑ᵢ klFluxDeriv i = 2 · klRate + fisherIntegrand`
(pure algebra, no assumptions). -/
theorem sum_klFluxDeriv (t : ℝ) (x : Fin d → ℝ) :
    ∑ i, klFluxDeriv P Q PG QG PH QH t i x =
      2 * klRate P Q PH QH t x + fisherIntegrand P Q PG QG t x := by
  unfold klFluxDeriv klRate fisherIntegrand
  rw [dotProduct, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.mul_sum (s := Finset.univ) (a := P t x)]
  simp only [sq]
  ring

/-- Pointwise time derivative of the KL integrand along the heat equation. If at `(t, x)`
`P, Q > 0` and `∂_t P = ½ ∑ᵢ PHᵢᵢ`, `∂_t Q = ½ ∑ᵢ QHᵢᵢ`, then `∂_t [P log(P/Q)] = klRate`. -/
theorem hasDerivAt_klIntegrand_time {t : ℝ} {x : Fin d → ℝ} (hP : 0 < P t x) (hQ : 0 < Q t x)
    (hPt : HasDerivAt (fun r => P r x) ((∑ i, PH t x i i) / 2) t)
    (hQt : HasDerivAt (fun r => Q r x) ((∑ i, QH t x i i) / 2) t) :
    HasDerivAt (fun r => klIntegrand P Q r x) (klRate P Q PH QH t x) t := by
  have hdiv := hPt.div hQt hQ.ne'
  have hlog := hdiv.log (div_pos hP hQ).ne'
  have := hPt.mul hlog
  refine this.congr_deriv ?_
  unfold klRate
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Pointwise space derivative of the `i`-th flux coordinate (the integration-by-parts identity
in differential form). If at `(t, x)` `P, Q > 0`, `∇P = PG`, `∇Q = QG`, and the `i`-th gradient
coordinates have gradients `(PH t x i j)ⱼ`, `(QH t x i j)ⱼ`, then `klFlux t i` is Fréchet
differentiable at `x` and its `i`-th partial derivative is `klFluxDeriv t i x`. -/
theorem hasFDerivAt_klFlux {t : ℝ} {x : Fin d → ℝ} (i : Fin d) (hP : 0 < P t x)
    (hQ : 0 < Q t x) (hPx : HasFDerivAt (P t) (dotCLM (PG t x)) x)
    (hQx : HasFDerivAt (Q t) (dotCLM (QG t x)) x)
    (hPxx : HasFDerivAt (fun y => PG t y i) (dotCLM fun j => PH t x i j) x)
    (hQxx : HasFDerivAt (fun y => QG t y i) (dotCLM fun j => QH t x i j) x) :
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, HasFDerivAt (klFlux P Q PG QG t i) L x ∧
      L (Pi.single i 1) = klFluxDeriv P Q PG QG PH QH t i x := by
  have hinv := (hasDerivAt_inv hQ.ne').comp_hasFDerivAt x hQx
  have hdiv := hPx.mul hinv
  have hne : (P t * (Inv.inv ∘ Q t)) x ≠ 0 := by
    simp only [Pi.mul_apply, Function.comp_apply]; positivity
  have hlog := (hdiv.log hne).add_const 1
  have hF := (hPxx.mul hlog).sub (hdiv.mul hQxx)
  refine ⟨_, hF.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_), ?_⟩
  · simp [klFlux, div_eq_mul_inv]
  · simp only [sub_apply, add_apply, smul_apply, dotCLM_single,
      smul_eq_mul, Function.comp_apply, Pi.mul_apply]
    unfold klFluxDeriv relScore
    rw [div_eq_mul_inv (P t x) (Q t x)]
    field_simp
    ring

/-- **Integration-by-parts step of de Bruijn's identity on `Fin d → ℝ`.** At a fixed time `t`,
if `P t`, `Q t` are positive and twice differentiable (gradients `PG`, `QG`, Hessians `PH`,
`QH`), the Fisher integrand is integrable, and for every coordinate `i` the flux coordinate
`klFlux t i` and its partial derivative `klFluxDeriv t i` are Lebesgue integrable (these
integrability conditions replace vanishing boundary flux), then
`∫ klRate = -½ ∫ P |∇ log(P/Q)|²`. -/
theorem integral_klRate_eq {t : ℝ} (hP : ∀ x, 0 < P t x) (hQ : ∀ x, 0 < Q t x)
    (hPx : ∀ x, HasFDerivAt (P t) (dotCLM (PG t x)) x)
    (hQx : ∀ x, HasFDerivAt (Q t) (dotCLM (QG t x)) x)
    (hPxx : ∀ i x, HasFDerivAt (fun y => PG t y i) (dotCLM fun j => PH t x i j) x)
    (hQxx : ∀ i x, HasFDerivAt (fun y => QG t y i) (dotCLM fun j => QH t x i j) x)
    (hfisher : Integrable (fisherIntegrand P Q PG QG t))
    (hflux : ∀ i, Integrable (klFlux P Q PG QG t i))
    (hfluxD : ∀ i, Integrable (klFluxDeriv P Q PG QG PH QH t i)) :
    ∫ x, klRate P Q PH QH t x = -(1 / 2) * ∫ x, fisherIntegrand P Q PG QG t x := by
  have hd : ∀ i x, DifferentiableAt ℝ (klFlux P Q PG QG t i) x ∧
      partialDeriv i (klFlux P Q PG QG t i) x = klFluxDeriv P Q PG QG PH QH t i x := by
    intro i x
    obtain ⟨L, hL, hLv⟩ := hasFDerivAt_klFlux i (hP x) (hQ x) (hPx x) (hQx x) (hPxx i x)
      (hQxx i x)
    exact ⟨hL.differentiableAt, by rw [partialDeriv, hL.fderiv, hLv]⟩
  have h0 : ∀ i, ∫ x, klFluxDeriv P Q PG QG PH QH t i x = 0 := by
    intro i
    have e : (fun x => klFluxDeriv P Q PG QG PH QH t i x) =
        fun x => partialDeriv i (klFlux P Q PG QG t i) x := funext fun x => (hd i x).2.symm
    rw [e]
    exact KLTransport.integral_partialDeriv_eq_zero i (fun x => (hd i x).1) (hflux i)
      (e ▸ hfluxD i)
  have hsum : ∫ x, ∑ i, klFluxDeriv P Q PG QG PH QH t i x = 0 := by
    rw [integral_finsetSum _ fun i _ => hfluxD i]
    simp [h0]
  have e : ∀ x, klRate P Q PH QH t x =
      ((∑ i, klFluxDeriv P Q PG QG PH QH t i x) - fisherIntegrand P Q PG QG t x) / 2 := by
    intro x; rw [sum_klFluxDeriv]; ring
  simp_rw [e]
  rw [integral_div, integral_sub (integrable_finsetSum _ fun i _ => hfluxD i) hfisher, hsum]
  ring

/-- If `P t`, `Q t` are continuous and positive then `x ↦ P log(P/Q)` is continuous. -/
theorem continuous_klIntegrand {t : ℝ} (hP : ∀ x, 0 < P t x) (hQ : ∀ x, 0 < Q t x)
    (hPc : Continuous (P t)) (hQc : Continuous (Q t)) : Continuous (klIntegrand P Q t) :=
  hPc.mul ((hPc.div hQc fun x => (hQ x).ne').log fun x => (div_pos (hP x) (hQ x)).ne')

/-- **de Bruijn identity for relative entropy on `Fin d → ℝ` (abstract form).** Let
`P, Q : ℝ → (Fin d → ℝ) → ℝ` (time, space) and `s ∈ 𝓝 t₀`. Assume, for all `t ∈ s` and all `x`:
`P t x, Q t x > 0`; the heat equations `∂_t P = ½ ∑ᵢ PHᵢᵢ`, `∂_t Q = ½ ∑ᵢ QHᵢᵢ`; `∇P = PG`,
`∇Q = QG`; and at `t₀` the gradient coordinates have Hessian rows `PH`, `QH`. Assume further:
`P t₀ log(P t₀ / Q t₀)` is integrable; `klRate` is dominated on `s` by an integrable `bound`; the
relative Fisher integrand at `t₀` is integrable; and each flux coordinate `klFlux t₀ i` and its
partial derivative `klFluxDeriv t₀ i` are integrable. Then
`d/dt ∫ P_t log(P_t/Q_t) = -½ ∫ P_{t₀} |∇ log(P_{t₀}/Q_{t₀})|²` at `t = t₀`. -/
theorem hasDerivAt_integral_klIntegrand {s : Set ℝ} {t₀ : ℝ} (hs : s ∈ 𝓝 t₀)
    (hP : ∀ t ∈ s, ∀ x, 0 < P t x) (hQ : ∀ t ∈ s, ∀ x, 0 < Q t x)
    (hPt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => P r x) ((∑ i, PH t x i i) / 2) t)
    (hQt : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => Q r x) ((∑ i, QH t x i i) / 2) t)
    (hPx : ∀ t ∈ s, ∀ x, HasFDerivAt (P t) (dotCLM (PG t x)) x)
    (hQx : ∀ t ∈ s, ∀ x, HasFDerivAt (Q t) (dotCLM (QG t x)) x)
    (hPxx : ∀ i x, HasFDerivAt (fun y => PG t₀ y i) (dotCLM fun j => PH t₀ x i j) x)
    (hQxx : ∀ i x, HasFDerivAt (fun y => QG t₀ y i) (dotCLM fun j => QH t₀ x i j) x)
    (hint : Integrable (klIntegrand P Q t₀)) {bound : (Fin d → ℝ) → ℝ}
    (hbound_int : Integrable bound) (hbound : ∀ t ∈ s, ∀ x, |klRate P Q PH QH t x| ≤ bound x)
    (hfisher : Integrable (fisherIntegrand P Q PG QG t₀))
    (hflux : ∀ i, Integrable (klFlux P Q PG QG t₀ i))
    (hfluxD : ∀ i, Integrable (klFluxDeriv P Q PG QG PH QH t₀ i)) :
    HasDerivAt (fun t => ∫ x, klIntegrand P Q t x)
      (-(1 / 2) * ∫ x, fisherIntegrand P Q PG QG t₀ x) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (klIntegrand P Q t) volume := by
    filter_upwards [hs] with t ht
    exact (continuous_klIntegrand (hP t ht) (hQ t ht)
      (continuous_iff_continuousAt.2 fun x => (hPx t ht x).continuousAt)
      (continuous_iff_continuousAt.2 fun x => (hQx t ht x).continuousAt)).aestronglyMeasurable
  have hHm : ∀ (H : ℝ → (Fin d → ℝ) → Fin d → Fin d → ℝ) (G : ℝ → (Fin d → ℝ) → Fin d → ℝ),
      (∀ i x, HasFDerivAt (fun y => G t₀ y i) (dotCLM fun j => H t₀ x i j) x) →
      Measurable fun x => ∑ i, H t₀ x i i := by
    intro H G hG
    refine Finset.measurable_sum _ fun i _ => ?_
    have e : (fun x => H t₀ x i i) = fun x => fderiv ℝ (fun y => G t₀ y i) x (Pi.single i 1) :=
      funext fun x => by rw [(hG i x).fderiv, dotCLM_single]
    rw [e]
    exact measurable_fderiv_apply_const ℝ _ _
  have hPm : Measurable (P t₀) :=
    (continuous_iff_continuousAt.2 fun x => (hPx t₀ ht₀ x).continuousAt).measurable
  have hQm : Measurable (Q t₀) :=
    (continuous_iff_continuousAt.2 fun x => (hQx t₀ ht₀ x).continuousAt).measurable
  have hrate_meas : AEStronglyMeasurable (klRate P Q PH QH t₀) volume := by
    unfold klRate
    exact (((hHm PH PG hPxx).mul (((hPm.div hQm).log).add_const 1)).sub
      ((hPm.div hQm).mul (hHm QH QG hQxx))).div_const 2 |>.aestronglyMeasurable
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint
    hrate_meas (Eventually.of_forall fun x t ht => by simpa using hbound t ht x) hbound_int
    (Eventually.of_forall fun x t ht =>
      hasDerivAt_klIntegrand_time (hP t ht x) (hQ t ht x) (hPt t ht x) (hQt t ht x))
  rwa [integral_klRate_eq (hP t₀ ht₀) (hQ t₀ ht₀) (hPx t₀ ht₀) (hQx t₀ ht₀) hPxx hQxx
    hfisher hflux hfluxD] at hderiv

end Abstract

/-! ### Densities of probability measures and the KL integral -/

/-- If `p ≥ 0` is measurable and `p · volume` is a probability measure on `Fin d → ℝ`, then `p` is
Lebesgue integrable and `∫ p = 1`. -/
theorem integrable_and_integral_eq_one {p : (Fin d → ℝ) → ℝ} (hm : Measurable p)
    (h0 : ∀ x, 0 ≤ p x) [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))] :
    Integrable p ∧ ∫ x, p x = 1 := by
  have h1 := measure_univ (μ := volume.withDensity fun x => ENNReal.ofReal (p x))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [HasFiniteIntegral]
    simp_rw [Real.enorm_eq_ofReal (h0 _), h1]
    exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hm.aestronglyMeasurable, h1]
    simp

/-- **Density KL as a real number.** For measurable `p > 0`, `q > 0` on `Fin d → ℝ` whose density
measures are probability measures and with `p log(p/q)` integrable,
`KL(p · volume ‖ q · volume).toReal = ∫ p log(p/q)` (the integral is `≥ 0` by Gibbs'
inequality `p log(p/q) ≥ p - q`). -/
theorem toReal_klDiv_withDensity_eq_integral {p q : (Fin d → ℝ) → ℝ} (hpm : Measurable p)
    (hqm : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (q x))]
    (hKL : Integrable fun x => p x * Real.log (p x / q x)) :
    (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (volume.withDensity fun x => ENNReal.ofReal (q x))).toReal =
        ∫ x, p x * Real.log (p x / q x) := by
  rw [KLTransport.klDiv_withDensity_eq_integral hpm hqm (fun x => (hp x).le) hq hKL,
    ENNReal.toReal_ofReal]
  obtain ⟨hpi, hp1⟩ := integrable_and_integral_eq_one hpm fun x => (hp x).le
  obtain ⟨hqi, hq1⟩ := integrable_and_integral_eq_one hqm fun x => (hq x).le
  have hg : ∀ x, p x - q x ≤ p x * Real.log (p x / q x) := by
    intro x
    have h := Real.one_sub_inv_le_log_of_pos (div_pos (hp x) (hq x))
    rw [inv_div] at h
    have := mul_le_mul_of_nonneg_left h (hp x).le
    rwa [mul_sub, mul_one, mul_div_cancel₀ _ (hp x).ne'] at this
  calc (0 : ℝ) = ∫ x, (p x - q x) := by rw [integral_sub hpi hqi, hp1, hq1, sub_self]
    _ ≤ _ := integral_mono (hpi.sub hqi) hKL hg

/-! ### de Bruijn along the heat flow of two laws -/

/-- The relative Fisher information along the heat flow,
`heatFisher ρ π t = ∫ p_t |∇ log(p_t / q_t)|² dx` with `p_t = heatFlowDensityPi ρ t` and
`q_t = heatFlowDensityPi π t`, i.e. `I(ρ_t‖π_t)` for `t > 0`. -/
noncomputable def heatFisher (ρ π : Measure (Fin d → ℝ)) (t : ℝ) : ℝ :=
  ∫ x, fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowGradPi ρ)
    (heatFlowGradPi π) t x

/-- **Regularity hypotheses for de Bruijn's identity along the isotropic heat flow** on an open
set `s` of positive times, for `p_t = heatFlowDensityPi ρ t`, `q_t = heatFlowDensityPi π t` (all
derivatives are the explicit Gaussian-convolution derivatives `heatFlowGradPi`,
`heatFlowHessPi`). These are standard integrability conditions on the convolutions; the boundary
terms of the integration by parts are controlled by integrability of each flux coordinate and of
its partial derivative (no decay at infinity is assumed). None of them is the identity itself. -/
structure HeatFlowRegularPi (ρ π : Measure (Fin d → ℝ)) (s : Set ℝ) : Prop where
  /-- The time set is open. -/
  isOpen : IsOpen s
  /-- Only positive times. -/
  subset_Ioi : s ⊆ Ioi 0
  /-- `p_t log(p_t/q_t)` is Lebesgue integrable (finite KL along the flow). -/
  integrable_kl : ∀ t ∈ s,
    Integrable (klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) t)
  /-- The time derivative `klRate` of the KL integrand is dominated, locally uniformly in time,
  by an integrable function of `x`. -/
  dominated : ∀ t ∈ s, ∃ bound : (Fin d → ℝ) → ℝ, Integrable bound ∧ ∀ᶠ r in 𝓝 t, ∀ x,
    |klRate (heatFlowDensityPi ρ) (heatFlowDensityPi π) (heatFlowHessPi ρ) (heatFlowHessPi π)
      r x| ≤ bound x
  /-- The relative Fisher integrand `p_t |∇ log(p_t/q_t)|²` is integrable. -/
  integrable_fisher : ∀ t ∈ s, Integrable (fisherIntegrand (heatFlowDensityPi ρ)
    (heatFlowDensityPi π) (heatFlowGradPi ρ) (heatFlowGradPi π) t)
  /-- Each coordinate of the KL flux `∇p_t (log(p_t/q_t) + 1) - (p_t/q_t) ∇q_t` is integrable. -/
  integrable_flux : ∀ t ∈ s, ∀ i, Integrable (klFlux (heatFlowDensityPi ρ)
    (heatFlowDensityPi π) (heatFlowGradPi ρ) (heatFlowGradPi π) t i)
  /-- The `i`-th partial derivative of the `i`-th flux coordinate is integrable. -/
  integrable_fluxDeriv : ∀ t ∈ s, ∀ i, Integrable (klFluxDeriv (heatFlowDensityPi ρ)
    (heatFlowDensityPi π) (heatFlowGradPi ρ) (heatFlowGradPi π) (heatFlowHessPi ρ)
    (heatFlowHessPi π) t i)

variable {ρ π : Measure (Fin d → ℝ)}

/-- For a finite `ρ` and `t > 0`, `y ↦ heatFlowDensityPi ρ t y` is continuous. -/
theorem continuous_heatFlowDensityPi (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ] {t : ℝ}
    (ht : 0 < t) : Continuous (heatFlowDensityPi ρ t) :=
  continuous_iff_continuousAt.2 fun y => (hasFDerivAt_heatFlowDensityPi ρ ht y).continuousAt

/-- For a probability `ρ` and `t > 0`, `ρ * N(0, t I)` written as a density measure is a
probability measure. -/
theorem isProbabilityMeasure_withDensity_heatFlowDensityPi (ρ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensityPi ρ t y)) := by
  rw [← heatKernelPi_comp_eq_withDensity ρ ht]; infer_instance

/-- For probability measures `ρ, π`, `t > 0` and integrable `p_t log(p_t/q_t)`, the heat-flow KL
is the density integral: `heatKL ρ π t = ∫ p_t log(p_t / q_t) dx`. -/
theorem heatKL_eq_integral [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {t : ℝ}
    (ht : 0 < t)
    (hint : Integrable (klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) t)) :
    heatKL ρ π t = ∫ x, klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π) t x := by
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi ρ ht
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi π ht
  rw [heatKL, heatKernelPi_comp_eq_withDensity ρ ht, heatKernelPi_comp_eq_withDensity π ht]
  exact toReal_klDiv_withDensity_eq_integral (continuous_heatFlowDensityPi ρ ht).measurable
    (continuous_heatFlowDensityPi π ht).measurable (heatFlowDensityPi_pos ρ ht)
    (heatFlowDensityPi_pos π ht) hint

/-- **de Bruijn identity along the isotropic heat flow (Verified under `HeatFlowRegularPi`).**
For probability measures `ρ, π` on `Fin d → ℝ` and `t₀ ∈ s` with `HeatFlowRegularPi ρ π s`,
`t ↦ KL(ρ * N(0, t I) ‖ π * N(0, t I))` is differentiable at `t₀` with derivative
`-½ I(ρ_{t₀}‖π_{t₀}) = -(1/2) * heatFisher ρ π t₀`. -/
theorem hasDerivAt_heatKL [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {s : Set ℝ}
    (hreg : HeatFlowRegularPi ρ π s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    HasDerivAt (heatKL ρ π) (-(1 / 2) * heatFisher ρ π t₀) t₀ := by
  obtain ⟨bound, hb_int, hev⟩ := hreg.dominated t₀ ht₀
  obtain ⟨v, hv, hvb⟩ := hev.exists_mem
  have hs : s ∈ 𝓝 t₀ := hreg.isOpen.mem_nhds ht₀
  have hpos : ∀ t ∈ s, 0 < t := fun t ht => hreg.subset_Ioi ht
  have hd := hasDerivAt_integral_klIntegrand (s := v ∩ s) (inter_mem hv hs)
    (fun t ht x => heatFlowDensityPi_pos ρ (hpos t ht.2) x)
    (fun t ht x => heatFlowDensityPi_pos π (hpos t ht.2) x)
    (fun t ht x => hasDerivAt_heatFlowDensityPi_t ρ (hpos t ht.2) x)
    (fun t ht x => hasDerivAt_heatFlowDensityPi_t π (hpos t ht.2) x)
    (fun t ht x => hasFDerivAt_heatFlowDensityPi ρ (hpos t ht.2) x)
    (fun t ht x => hasFDerivAt_heatFlowDensityPi π (hpos t ht.2) x)
    (fun i x => hasFDerivAt_heatFlowGradPi ρ (hpos t₀ ht₀) i x)
    (fun i x => hasFDerivAt_heatFlowGradPi π (hpos t₀ ht₀) i x)
    (hreg.integrable_kl t₀ ht₀) hb_int (fun t ht => hvb t ht.1)
    (hreg.integrable_fisher t₀ ht₀) (hreg.integrable_flux t₀ ht₀)
    (hreg.integrable_fluxDeriv t₀ ht₀)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact heatKL_eq_integral (hpos t ht) (hreg.integrable_kl t ht)

/-! ### Forward-step contraction along the heat flow -/

/-- **Heat-flow KL contraction on `Fin d → ℝ` from an LSI along the flow.** For probability
measures `ρ, π` on `Fin d → ℝ` with `KL(ρ‖π) < ∞`, `α ≥ 0`, `η > 0`, `HeatFlowRegularPi ρ π s`
with `(0, η] ⊆ s`, and the log-Sobolev inequality of `π_t` along the curve for `t ∈ (0, η)`,
`2 α KL(ρ_t‖π_t) ≤ (1 + α t) I(ρ_t‖π_t)` (`heatKL`, `heatFisher`):
`KL(ρ_η‖π_η) ≤ KL(ρ‖π) / (1 + α η)` (as `heatKL ρ π η ≤ heatKL ρ π 0 / (1 + α η)`). No regularity
and no LSI at `t = 0` is required (there `heatFisher ρ π 0` carries no information): the Grönwall
argument runs on `[τ, η]` and `τ → 0⁺` is handled by data processing `KL(ρ_τ‖π_τ) ≤ KL(ρ‖π)`
(`Gronwall.le_div_of_hasDerivAt_Ioc`). -/
theorem heatKL_le_div_of_regular [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {α η : ℝ}
    (hα : 0 ≤ α) (hη : 0 < η) (hKL : klDiv ρ π ≠ ⊤) {s : Set ℝ}
    (hreg : HeatFlowRegularPi ρ π s) (hs : Ioc 0 η ⊆ s)
    (hL : ∀ t ∈ Ioo 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * heatFisher ρ π t) :
    heatKL ρ π η ≤ heatKL ρ π 0 / (1 + α * η) :=
  Gronwall.le_div_of_hasDerivAt_Ioc hα hη (fun _ ht => hasDerivAt_heatKL hreg (hs ht)) hL
    fun τ _ => heatKL_le_heatKL_zero ρ π hKL τ

/-- Contraction in `klDiv` form: under the hypotheses of `heatKL_le_div_of_regular`,
`KL(heatKernelPi η ∘ₘ ρ ‖ heatKernelPi η ∘ₘ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_heatKernelPi_le_of_regular [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) (hKL : klDiv ρ π ≠ ⊤)
    {s : Set ℝ} (hreg : HeatFlowRegularPi ρ π s) (hs : Ioc 0 η ⊆ s)
    (hL : ∀ t ∈ Ioo 0 η, 2 * α * heatKL ρ π t ≤ (1 + α * t) * heatFisher ρ π t) :
    (klDiv (heatKernelPi η.toNNReal ∘ₘ ρ) (heatKernelPi η.toNNReal ∘ₘ π)).toReal
      ≤ (klDiv ρ π).toReal / (1 + α * η) := by
  rw [← heatKL_zero ρ π]
  exact heatKL_le_div_of_regular hα hη hKL hreg hs hL

/-! ### Non-vacuity -/

/-- Non-vacuity of `HeatFlowRegularPi`: for every probability measure `ρ` on `Fin d → ℝ`,
`HeatFlowRegularPi ρ ρ (Ioi 0)` holds (all integrands vanish identically). -/
theorem heatFlowRegularPi_self (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] :
    HeatFlowRegularPi ρ ρ (Ioi 0) := by
  have hdiv : ∀ t ∈ Ioi (0 : ℝ), ∀ x,
      heatFlowDensityPi ρ t x / heatFlowDensityPi ρ t x = 1 :=
    fun t ht x => div_self (heatFlowDensityPi_pos ρ ht x).ne'
  have hkl : ∀ t ∈ Ioi (0 : ℝ),
      klIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi ρ) t = 0 :=
    fun t ht => funext fun x => by simp [klIntegrand, hdiv t ht x]
  have hrate : ∀ t ∈ Ioi (0 : ℝ), ∀ x, klRate (heatFlowDensityPi ρ) (heatFlowDensityPi ρ)
      (heatFlowHessPi ρ) (heatFlowHessPi ρ) t x = 0 :=
    fun t ht x => by simp [klRate, hdiv t ht x]
  have hrel : ∀ t x, relScore (heatFlowDensityPi ρ) (heatFlowDensityPi ρ) (heatFlowGradPi ρ)
      (heatFlowGradPi ρ) t x = 0 :=
    fun t x => funext fun i => by simp [relScore]
  have hfis : ∀ t ∈ Ioi (0 : ℝ), fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi ρ)
      (heatFlowGradPi ρ) (heatFlowGradPi ρ) t = 0 :=
    fun t _ => funext fun x => by simp [fisherIntegrand, hrel]
  have hflux : ∀ t ∈ Ioi (0 : ℝ), ∀ i, klFlux (heatFlowDensityPi ρ) (heatFlowDensityPi ρ)
      (heatFlowGradPi ρ) (heatFlowGradPi ρ) t i = 0 :=
    fun t ht i => funext fun x => by simp [klFlux, hdiv t ht x]
  have hfluxD : ∀ t ∈ Ioi (0 : ℝ), ∀ i, klFluxDeriv (heatFlowDensityPi ρ) (heatFlowDensityPi ρ)
      (heatFlowGradPi ρ) (heatFlowGradPi ρ) (heatFlowHessPi ρ) (heatFlowHessPi ρ) t i = 0 :=
    fun t ht i => funext fun x => by simp [klFluxDeriv, hdiv t ht x, hrel]
  refine ⟨isOpen_Ioi, subset_rfl, fun t ht => by rw [hkl t ht]; exact integrable_zero _ _ _,
    fun t ht => ⟨0, integrable_zero _ _ _, ?_⟩,
    fun t ht => by rw [hfis t ht]; exact integrable_zero _ _ _,
    fun t ht i => by rw [hflux t ht i]; exact integrable_zero _ _ _,
    fun t ht i => by rw [hfluxD t ht i]; exact integrable_zero _ _ _⟩
  filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr x
  simp [hrate r hr x]

end FormalizeSampling.HeatFlowDeBruijnPi

namespace FormalizeSampling.NoiseScorePreconditioned

/-! ### Gaussians `N(μ, I)` with their densities -/

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi

variable {d : ℕ}

/-- The Lebesgue density `y ↦ heatDensityPi 1 (y - μ)` of `N(μ, I_d)`. -/
noncomputable def gaussDensity (μ : Fin d → ℝ) (y : Fin d → ℝ) : ℝ := heatDensityPi 1 (y - μ)

/-- `N(μ, I_d)` has Lebesgue density `gaussDensity μ`. -/
theorem pi_gaussianReal_one_eq_withDensity (μ : Fin d → ℝ) :
    (Measure.pi fun i => gaussianReal (μ i) 1) =
      volume.withDensity fun x => ENNReal.ofReal (gaussDensity μ x) := by
  have h := heatKernelPi_eq_withDensity (d := d) one_pos μ
  rw [heatKernelPi_apply, Real.toNNReal_one] at h
  exact h

/-- Gradient of `gaussDensity μ`. -/
theorem hasFDerivAt_gaussDensity (μ x : Fin d → ℝ) :
    HasFDerivAt (gaussDensity μ) (dotCLM (heatGradPi 1 (x - μ))) x := by
  have h := (hasFDerivAt_heatDensityPi 1 (x - μ)).comp x ((hasFDerivAt_id x).sub_const μ)
  have e : gaussDensity μ = fun x => heatDensityPi 1 (x - μ) := rfl
  rw [e]
  simpa [Function.comp_def] using h

/-- `gaussDensity μ` is `C¹`. -/
theorem contDiff_gaussDensity (μ : Fin d → ℝ) : ContDiff ℝ 1 (gaussDensity μ) :=
  contDiff_one_iff_hasFDerivAt.2 ⟨_, continuous_dotCLM
    ((continuous_heatGradPi _).comp (continuous_id.sub continuous_const)),
    hasFDerivAt_gaussDensity μ⟩

/-- `gaussDensity μ` is everywhere positive. -/
theorem gaussDensity_pos (μ x : Fin d → ℝ) : 0 < gaussDensity μ x :=
  heatDensityPi_pos one_pos _

/-- **Score of `N(μ, I)`.** `∇log p(x) = -x + μ` for `p = gaussDensity μ`. -/
theorem score_gaussDensity (μ x : Fin d → ℝ) : score (gaussDensity μ) x = -x + μ := by
  funext i
  have hd := hasFDerivAt_gaussDensity μ x
  have hp := gaussDensity_pos μ x
  rw [score_apply_of_pos hd.differentiableAt hp, partialDeriv, hd.fderiv, dotCLM_single]
  simp only [gaussDensity, heatGradPi] at hp ⊢
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, div_one]
  field_simp
  ring

end FormalizeSampling.NoiseScorePreconditioned
