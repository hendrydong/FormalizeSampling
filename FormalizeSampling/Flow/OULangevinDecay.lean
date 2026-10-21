module

public import FormalizeSampling.Foundations.HeatFlowRegularity
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.GaussianLSI
public import FormalizeSampling.Foundations.GaussianKL
public import FormalizeSampling.Foundations.Pinsker
public import FormalizeSampling.Kernels.GaussianKernels

/-!
# FL-4 for the OU / Langevin flow with Gaussian target: sharp exponential KL decay

Registry ID: **FL-4** (unconditional instance: Langevin flow for the Gaussian target, i.e. the
Ornstein–Uhlenbeck semigroup, in dimension one).

Status: **Verified**. Hypotheses on the initial law `ρ`: probability measure, `KL(ρ‖π) < ∞` and
`∫ x² dρ < ∞`. No regularity, functional-inequality or Fokker–Planck hypothesis.

Setting: the OU kernel with stationary law `N(0, v)` (`v > 0`) and rate `a ≥ 0`,
`ouKernelVar v a t x = N(e^{-at} x, v (1 - e^{-2at}))`; for `v = 1` this is
`OU.ouKernel a t` (`ouKernel_eq_ouKernelVar_one`). The law at time `t` started from `ρ` is
`ouKernelVar v a t ∘ₘ ρ` (the kernel is taken as the definition of the flow, as in
`Kernels/GaussianKernels`).

## Idea

Write `c = e^{-at}` and `w = v (1 - c²)`. The OU step is a scaled heat step:
`ouKernelVar v a t ∘ₘ ρ = heatKernel w ∘ₘ ρ.map (c * ·)` (`affineGaussian_comp_eq_heat_comp_map`)
and the target is `N(0, v) = heatKernel w ∘ₘ N(0, c² v)` with `N(0, c² v) = N(0, v).map (c * ·)`.
The heat flow contracts KL against a Gaussian reference `N(0, α⁻¹)` by `1/(1 + α η)`
(`toReal_klDiv_heatKernel_le_gaussian_of_moment`, from `HeatFlowRegularityPerturbed` and the de
Bruijn argument of `HeatFlowDeBruijn`); with `α⁻¹ = c² v`, `η = w` the factor is `c² = e^{-2at}`.
The scaling does not increase KL (`klDiv_map_le`).

## Main results

* `toReal_klDiv_heatKernel_le_gaussian_of_moment`: 1D heat-flow contraction
  `KL(ρ_η‖π_η) ≤ KL(ρ‖π) / (1 + α η)` for `π = N(0, α⁻¹)`, finite KL and second moment.
* `toReal_klDiv_ouKernelVar_comp_le` (general variance) and `toReal_klDiv_ouKernel_comp_le`
  (`v = 1`): `KL(ρ_t‖N(0, v)) < ∞` and `KL(ρ_t‖N(0, v)) ≤ e^{-2at} KL(ρ‖N(0, v))`.
* `toReal_klDiv_ouKernel_comp_gaussianReal` and `toReal_klDiv_ouKernelVar_comp_gaussianReal`
  (tightness): for `ρ = N(m, v)`, `KL(ρ_t‖N(0, v)) = e^{-2at} KL(ρ‖N(0, v)) = e^{-2at} m²/(2v)`.
* `tvSup_ouKernel_comp_le`, `tvSup_ouKernelVar_comp_le` (Pinsker):
  `tvSup(ρ_t, N(0, v)) ≤ √(e^{-2at} KL(ρ‖N(0, v)) / 2)`.

## Not proved here

* That `ouKernelVar` is the transition kernel of the OU SDE (it is the definition here).
* Non-Gaussian targets (they need an LSI along the flow; see `LogSobolevExtension`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal FormalizeSampling.OU

namespace FormalizeSampling.OULangevinDecay

open FormalizeSampling.OU FormalizeSampling.ProximalContraction
  FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.HeatFlowRegularity

/-! ### The OU kernel with stationary law `N(0, v)` -/

/-- The OU (Mehler) kernel with stationary law `N(0, v)` and rate `a`:
`ouKernelVar v a t x = N(e^{-at} x, v (1 - e^{-2at}))` (variance truncated at `0`). -/
noncomputable def ouKernelVar (v a t : ℝ) : Kernel ℝ ℝ :=
  affineGaussianKernel (Real.exp (-a * t)) (v * (1 - Real.exp (-2 * a * t))).toNNReal

/-- Evaluation: `ouKernelVar v a t x = N(e^{-at} x, v (1 - e^{-2at}))`. -/
theorem ouKernelVar_apply (v a t x : ℝ) :
    ouKernelVar v a t x =
      gaussianReal (Real.exp (-a * t) * x) (v * (1 - Real.exp (-2 * a * t))).toNNReal := rfl

/-- `ouKernelVar v a t` is a Markov kernel. -/
instance isMarkovKernel_ouKernelVar (v a t : ℝ) : IsMarkovKernel (ouKernelVar v a t) := by
  unfold ouKernelVar; infer_instance

/-- The standard OU kernel is the case `v = 1`: `ouKernel a t = ouKernelVar 1 a t`. -/
theorem ouKernel_eq_ouKernelVar_one (a t : ℝ) : ouKernel a t = ouKernelVar 1 a t := by
  rw [ouKernel, ouKernelVar, ouVar, one_mul]

/-! ### Scaling identities -/

/-- An affine Gaussian step is a heat step after scaling: for any measure `μ`,
`affineGaussianKernel c w ∘ₘ μ = heatKernel w ∘ₘ μ.map (c * ·)`. -/
theorem affineGaussian_comp_eq_heat_comp_map (c : ℝ) (w : ℝ≥0) (μ : Measure ℝ) :
    affineGaussianKernel c w ∘ₘ μ = heatKernel w ∘ₘ μ.map (c * ·) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (measurable_const_mul _)]
  rfl

/-- Scaling a centred Gaussian: for `v ≥ 0`, `N(0, v).map (c * ·) = N(0, c² v)`. -/
theorem gaussianReal_map_const_mul_zero (c : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    (gaussianReal 0 v.toNNReal).map (c * ·) = gaussianReal 0 (c ^ 2 * v).toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv,
    Real.coe_toNNReal _ (by positivity)]

/-- The heat step `w = v (1 - c²)` from `N(0, c² v)` returns `N(0, v)` (`v ≥ 0`, `c² ≤ 1`). -/
theorem heatKernel_comp_gaussianReal_scaled {c v : ℝ} (hv : 0 ≤ v) (hc : c ^ 2 ≤ 1) :
    heatKernel (v * (1 - c ^ 2)).toNNReal ∘ₘ gaussianReal 0 (c ^ 2 * v).toNNReal =
      gaussianReal 0 v.toNNReal := by
  have h1 : 0 ≤ v * (1 - c ^ 2) := mul_nonneg hv (by linarith)
  have e : v.toNNReal = (c ^ 2 * v).toNNReal + (v * (1 - c ^ 2)).toNNReal := by
    rw [← Real.toNNReal_add (by positivity) h1]; ring_nf
  rw [e, ← bind_heat]
  rfl

/-! ### Heat-flow contraction against a Gaussian (dimension one) -/

/-- **Heat-flow KL contraction for a Gaussian target (dimension one, no regularity
hypothesis).** For `α, η > 0`, `π = N(0, α⁻¹)` and a probability law `ρ` with `KL(ρ‖π) < ∞` and
`∫ x² dρ < ∞`: `KL(heatKernel η ∘ₘ ρ ‖ heatKernel η ∘ₘ π).toReal ≤ KL(ρ‖π).toReal / (1 + α η)`. -/
theorem toReal_klDiv_heatKernel_le_gaussian_of_moment {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (gaussianReal 0 α⁻¹.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    (klDiv (heatKernel η.toNNReal ∘ₘ ρ)
        (heatKernel η.toNNReal ∘ₘ gaussianReal 0 α⁻¹.toNNReal)).toReal
      ≤ (klDiv ρ (gaussianReal 0 α⁻¹.toNNReal)).toReal / (1 + α * η) := by
  have hv : 0 < α⁻¹ := inv_pos.2 hα
  have hreg := heatFlowRegular_gaussianReal ρ hmom hv
  have h := heatKL_le_div_of_regular hα.le hη hKL hreg (fun t ht => ht.1) fun t ht => by
    have h := GaussianLSI.heatKL_le_heatFisher_gaussianReal ρ hv hmom ht.1
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * α)
    have e : 2 * α * ((α⁻¹ + t) / 2 * heatFisher ρ (gaussianReal 0 α⁻¹.toNNReal) t)
        = (1 + α * t) * heatFisher ρ (gaussianReal 0 α⁻¹.toNNReal) t := by
      field_simp
    linarith
  rwa [heatKL_zero] at h

/-! ### Exponential KL decay along OU -/

/-- **Core contraction.** For `0 < c < 1`, `v > 0` and a probability law `ρ` with
`KL(ρ‖N(0, v)) < ∞` and `∫ x² dρ < ∞`, the kernel `x ↦ N(c x, v (1 - c²))` (which fixes
`N(0, v)`) satisfies `KL(· ∘ₘ ρ‖N(0, v)) < ∞` and
`KL(· ∘ₘ ρ‖N(0, v)).toReal ≤ c² KL(ρ‖N(0, v)).toReal`. -/
theorem toReal_klDiv_affineGaussian_comp_le {c v : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hv : 0 < v)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (gaussianReal 0 v.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    klDiv (affineGaussianKernel c (v * (1 - c ^ 2)).toNNReal ∘ₘ ρ) (gaussianReal 0 v.toNNReal)
        ≠ ∞ ∧
      (klDiv (affineGaussianKernel c (v * (1 - c ^ 2)).toNNReal ∘ₘ ρ)
          (gaussianReal 0 v.toNNReal)).toReal
        ≤ c ^ 2 * (klDiv ρ (gaussianReal 0 v.toNNReal)).toReal := by
  have hc2 : c ^ 2 < 1 := by nlinarith
  have hc2p : 0 < c ^ 2 := by positivity
  set μ := ρ.map (c * ·) with hμ
  have : IsProbabilityMeasure μ := by
    rw [hμ]; infer_instance
  have hmomμ : Integrable (fun x => x ^ 2) μ :=
    ProximalSharpGaussian.integrable_sq_map_const_mul ρ hmom c
  have hmap := klDiv_map_le ρ (gaussianReal 0 v.toNNReal) (measurable_const_mul c)
  rw [gaussianReal_map_const_mul_zero c hv.le] at hmap
  have hKLμ : klDiv μ (gaussianReal 0 (c ^ 2 * v).toNNReal) ≠ ∞ := ne_top_of_le_ne_top hKL hmap
  have hcomp := affineGaussian_comp_eq_heat_comp_map c (v * (1 - c ^ 2)).toNNReal ρ
  have hπ := heatKernel_comp_gaussianReal_scaled hv.le hc2.le
  rw [← hμ] at hcomp
  have hdp := klDiv_comp_right_le (μ := μ) (ν := gaussianReal 0 (c ^ 2 * v).toNNReal)
    (heatKernel (v * (1 - c ^ 2)).toNNReal)
  rw [hπ, ← hcomp] at hdp
  refine ⟨ne_top_of_le_ne_top hKLμ hdp, ?_⟩
  have hα : 0 < (c ^ 2 * v)⁻¹ := by positivity
  have hη : 0 < v * (1 - c ^ 2) := mul_pos hv (by linarith)
  have hKLμ' : klDiv μ (gaussianReal 0 (c ^ 2 * v)⁻¹⁻¹.toNNReal) ≠ ∞ := by rwa [inv_inv]
  have h := toReal_klDiv_heatKernel_le_gaussian_of_moment hα hη μ hKLμ' hmomμ
  rw [inv_inv, hπ, ← hcomp] at h
  have e : 1 + (c ^ 2 * v)⁻¹ * (v * (1 - c ^ 2)) = (c ^ 2)⁻¹ := by
    field_simp; ring
  rw [e, div_inv_eq_mul] at h
  refine h.trans ?_
  rw [mul_comm]
  gcongr

/-- `e^{-at} ^ 2 = e^{-2at}`. -/
theorem exp_neg_mul_sq (a t : ℝ) : Real.exp (-a * t) ^ 2 = Real.exp (-2 * a * t) := by
  rw [← Real.exp_nat_mul]; ring_nf

/-- If `a = 0` or `t = 0` (`a, t ≥ 0` with `a t ≤ 0`), the OU flow is the identity. -/
theorem ouKernelVar_comp_of_mul_eq_zero {v a t : ℝ} (h : a * t = 0) (ρ : Measure ℝ) :
    ouKernelVar v a t ∘ₘ ρ = ρ := by
  have hk : ouKernelVar v a t = Kernel.id := by
    ext1 x
    rw [ouKernelVar_apply, Kernel.id_apply,
      show -a * t = -(a * t) by ring, show -2 * a * t = -2 * (a * t) by ring, h]
    simp [gaussianReal_zero_var]
  rw [hk, Measure.id_comp]

/-- **FL-4 for OU with stationary law `N(0, v)` (Verified, unconditional).** For `v > 0`,
`a, t ≥ 0` and a probability law `ρ` on `ℝ` with `KL(ρ‖N(0, v)) < ∞` and `∫ x² dρ < ∞`:
`KL(ouKernelVar v a t ∘ₘ ρ‖N(0, v)) < ∞` and
`KL(ouKernelVar v a t ∘ₘ ρ‖N(0, v)).toReal ≤ e^{-2at} KL(ρ‖N(0, v)).toReal`. -/
theorem toReal_klDiv_ouKernelVar_comp_le {v a t : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (gaussianReal 0 v.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    klDiv (ouKernelVar v a t ∘ₘ ρ) (gaussianReal 0 v.toNNReal) ≠ ∞ ∧
      (klDiv (ouKernelVar v a t ∘ₘ ρ) (gaussianReal 0 v.toNNReal)).toReal
        ≤ Real.exp (-2 * a * t) * (klDiv ρ (gaussianReal 0 v.toNNReal)).toReal := by
  rcases (mul_nonneg ha ht).eq_or_lt with h0 | hpos
  · rw [ouKernelVar_comp_of_mul_eq_zero h0.symm, show -2 * a * t = -2 * (a * t) by ring,
      ← h0, mul_zero, Real.exp_zero, one_mul]
    exact ⟨hKL, le_rfl⟩
  · have hc0 : 0 < Real.exp (-a * t) := Real.exp_pos _
    have hc1 : Real.exp (-a * t) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have h := toReal_klDiv_affineGaussian_comp_le hc0 hc1 hv ρ hKL hmom
    rwa [exp_neg_mul_sq] at h

/-- **FL-4 for the standard OU flow (Verified, unconditional).** For `a, t ≥ 0` and a
probability law `ρ` on `ℝ` with `KL(ρ‖N(0, 1)) < ∞` and `∫ x² dρ < ∞`:
`KL(ouKernel a t ∘ₘ ρ‖N(0, 1)) < ∞` and
`KL(ouKernel a t ∘ₘ ρ‖N(0, 1)).toReal ≤ e^{-2at} KL(ρ‖N(0, 1)).toReal`. -/
theorem toReal_klDiv_ouKernel_comp_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (gaussianReal 0 1) ≠ ∞)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    klDiv (ouKernel a t ∘ₘ ρ) (gaussianReal 0 1) ≠ ∞ ∧
      (klDiv (ouKernel a t ∘ₘ ρ) (gaussianReal 0 1)).toReal
        ≤ Real.exp (-2 * a * t) * (klDiv ρ (gaussianReal 0 1)).toReal := by
  have h1 : (1 : ℝ).toNNReal = 1 := Real.toNNReal_one
  rw [← h1] at hKL ⊢
  rw [ouKernel_eq_ouKernelVar_one]
  exact toReal_klDiv_ouKernelVar_comp_le one_pos ha ht ρ hKL hmom

/-! ### Tightness: Gaussian initial laws `N(m, v)` with the target's variance -/

/-- OU with stationary law `N(0, v)` maps `N(m, v)` to `N(e^{-at} m, v)` (`v ≥ 0`,
`a, t ≥ 0`). -/
theorem ouKernelVar_comp_gaussianReal {v a t : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (m : ℝ) :
    ouKernelVar v a t ∘ₘ gaussianReal m v.toNNReal =
      gaussianReal (Real.exp (-a * t) * m) v.toNNReal := by
  have hc : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  change (gaussianReal m v.toNNReal).bind (fun x => gaussianReal (Real.exp (-a * t) * x) _) = _
  rw [bind_affineGaussian, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal, add_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv,
    Real.coe_toNNReal _ (mul_nonneg hv (by linarith)), exp_neg_mul_sq]
  ring

/-- **Tightness of FL-4 (general variance).** For `v > 0`, `a, t ≥ 0` and `ρ = N(m, v)`:
`KL(ouKernelVar v a t ∘ₘ ρ‖N(0, v)).toReal = e^{-2at} KL(ρ‖N(0, v)).toReal = e^{-2at} m²/(2v)`.
-/
theorem toReal_klDiv_ouKernelVar_comp_gaussianReal {v a t : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (ht : 0 ≤ t) (m : ℝ) :
    (klDiv (ouKernelVar v a t ∘ₘ gaussianReal m v.toNNReal) (gaussianReal 0 v.toNNReal)).toReal
        = Real.exp (-2 * a * t) * (klDiv (gaussianReal m v.toNNReal)
          (gaussianReal 0 v.toNNReal)).toReal ∧
      (klDiv (ouKernelVar v a t ∘ₘ gaussianReal m v.toNNReal)
          (gaussianReal 0 v.toNNReal)).toReal = Real.exp (-2 * a * t) * (m ^ 2 / (2 * v)) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  have hkl : ∀ m' : ℝ, (klDiv (gaussianReal m' v.toNNReal) (gaussianReal 0 v.toNNReal)).toReal
      = m' ^ 2 / (2 * v) := fun m' => by
    rw [GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ hv0, sub_zero,
      Real.coe_toNNReal _ hv.le, ENNReal.toReal_ofReal (by positivity)]
  rw [ouKernelVar_comp_gaussianReal hv.le ha ht, hkl, hkl, mul_pow, exp_neg_mul_sq]
  constructor <;> ring

/-- **Tightness of FL-4 (standard OU).** For `a, t ≥ 0` and `ρ = N(m, 1)`:
`KL(ouKernel a t ∘ₘ ρ‖N(0, 1)).toReal = e^{-2at} KL(ρ‖N(0, 1)).toReal = e^{-2at} m²/2`. -/
theorem toReal_klDiv_ouKernel_comp_gaussianReal {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (m : ℝ) :
    (klDiv (ouKernel a t ∘ₘ gaussianReal m 1) (gaussianReal 0 1)).toReal
        = Real.exp (-2 * a * t) * (klDiv (gaussianReal m 1) (gaussianReal 0 1)).toReal ∧
      (klDiv (ouKernel a t ∘ₘ gaussianReal m 1) (gaussianReal 0 1)).toReal
        = Real.exp (-2 * a * t) * (m ^ 2 / 2) := by
  have h := toReal_klDiv_ouKernelVar_comp_gaussianReal one_pos ha ht m
  rw [Real.toNNReal_one, mul_one] at h
  rwa [ouKernel_eq_ouKernelVar_one]

/-! ### Total variation (Pinsker) -/

/-- **TV form (general variance).** Under the hypotheses of `toReal_klDiv_ouKernelVar_comp_le`:
`tvSup (ouKernelVar v a t ∘ₘ ρ) N(0, v) ≤ √(e^{-2at} KL(ρ‖N(0, v)).toReal / 2)`. -/
theorem tvSup_ouKernelVar_comp_le {v a t : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (gaussianReal 0 v.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    TotalVariation.tvSup (ouKernelVar v a t ∘ₘ ρ) (gaussianReal 0 v.toNNReal)
      ≤ √(Real.exp (-2 * a * t) * (klDiv ρ (gaussianReal 0 v.toNNReal)).toReal / 2) := by
  obtain ⟨hfin, hle⟩ := toReal_klDiv_ouKernelVar_comp_le hv ha ht ρ hKL hmom
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans ?_
  gcongr

/-- **TV form (standard OU).** Under the hypotheses of `toReal_klDiv_ouKernel_comp_le`:
`tvSup (ouKernel a t ∘ₘ ρ) N(0, 1) ≤ √(e^{-2at} KL(ρ‖N(0, 1)).toReal / 2)`. -/
theorem tvSup_ouKernel_comp_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ (gaussianReal 0 1) ≠ ∞)
    (hmom : Integrable (fun x => x ^ 2) ρ) :
    TotalVariation.tvSup (ouKernel a t ∘ₘ ρ) (gaussianReal 0 1)
      ≤ √(Real.exp (-2 * a * t) * (klDiv ρ (gaussianReal 0 1)).toReal / 2) := by
  obtain ⟨hfin, hle⟩ := toReal_klDiv_ouKernel_comp_le ha ht ρ hKL hmom
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans ?_
  gcongr

end FormalizeSampling.OULangevinDecay
