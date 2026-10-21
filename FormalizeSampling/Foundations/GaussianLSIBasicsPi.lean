module

public import FormalizeSampling.Foundations.HeatFlowDeBruijnPi
public import FormalizeSampling.Foundations.KLChainRule
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Helpers for the Gaussian log-Sobolev inequality along the isotropic heat flow on `Fin d → ℝ`

Status: **Verified** (helper module; the hypotheses are stated in each theorem). This file holds
the parts of the Gaussian LSI along the heat flow on `Fin d → ℝ` that do not need the regularity
theorem of `Foundations/HeatFlowRegularityPerturbedPi.lean`; `Foundations/GaussianLSIPi.lean` (which
imports that regularity theorem) states the LSI itself. All declarations live in the namespace
`FormalizeSampling.GaussianLSIPi`. This is the `Fin d → ℝ` version of
`Foundations/GaussianLSIBasics.lean`.

Notation (as in `HeatFlowDeBruijnPi`): `φ_a = heatDensityPi a` is the `N(0, a I)` density,
`p_t = heatFlowDensityPi ρ t = ρ * φ_t`, `π = N(0, v I) = ⊗ᵢ N(0, v)` (`v > 0`),
`π_t = heatKernelPi t ∘ₘ π = N(0, (v + t) I)`, `K(t) = heatKL ρ π t = KL(ρ_t‖π_t)` and
`I(t) = heatFisher ρ π t = I(ρ_t‖π_t)`. The relative score flux is
`G_t = gaussRelFluxPi ρ v t = ∇p_t + y p_t / (v + t) = p_t ∇ log(p_t / q_t)`. Euclidean norms are
`|z|² = ∑ᵢ zᵢ²`.

## Main results

* `heatFlow_semigroup`: `p_{t+a} = p_t * φ_a` and `∇p_{t+a} = p_t * ∇φ_a` pointwise.
* `heatKernelPi_comp_pi_gaussianReal`, `heatFlowDensityPi_gaussian`, `heatFlowGradPi_gaussian`:
  the heat flow of `N(0, v I)` is `N(0, (v + t) I)`, with density `heatDensityPi (v + t)`.
* `integral_heatDensityPi_mul_heatFlowGradPi` (integration by parts against the heat kernel,
  via `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) and
  `integral_heatDensityPi_mul_gaussRelFluxPi`: `G_{t+a} = c ∫ φ_a(· - z) G_t(z) dz`,
  `c = (v + t)/(v + t + a)` (the relative score as a heat-kernel average).
* `heatFisher_gaussian_le` (Fisher decay): `I(t + a) ≤ ((v + t)/(v + t + a))² I(t)`.
* `heatKL_le_div_two_mul`: `KL(ρ_T‖π_T) ≤ (∫ |x - u|² d(ρ ⊗ π)) / (2T)` (KL chain rule).
* `klDiv_heatKernelPi_comp_ne_top_of_regular`, `klDiv_heatKernelPi_comp_gaussian_ne_top`:
  `KL(ρ_t‖π_t) < ∞` under `HeatFlowRegularPi` (no moment assumption).
* `gaussian_hypotheses_satisfiable`: `ρ = N(0, v I)` has a finite second moment and satisfies
  `HeatFlowRegularPi ρ ρ (Ioi 0)`.

## Not proved here

* The Gaussian LSI along the heat flow: `Foundations/GaussianLSIPi.lean`.
* The fields of `HeatFlowRegularPi`: `Foundations/HeatFlowRegularityPerturbedPi.lean` derives them
  from a finite second moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.GaussianLSIPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi

variable {d : ℕ}

/-! ### Elementary facts on the kernel -/

/-- The isotropic heat kernel is even: `heatDensityPi t (-z) = heatDensityPi t z`. -/
theorem heatDensityPi_neg (t : ℝ) (z : Fin d → ℝ) : heatDensityPi t (-z) = heatDensityPi t z := by
  simp [heatDensityPi_eq_exp]

/-- For `t > 0` and every `x`, `y ↦ heatDensityPi t (y - x)` is Lebesgue integrable with
integral `1` (it is the density of `heatKernelPi t x`). -/
theorem integrable_heatDensityPi_sub {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    Integrable (fun y => heatDensityPi t (y - x)) ∧ ∫ y, heatDensityPi t (y - x) = 1 := by
  have : IsProbabilityMeasure
      (volume.withDensity fun y => ENNReal.ofReal (heatDensityPi t (y - x))) := by
    rw [← heatKernelPi_eq_withDensity ht]; infer_instance
  exact integrable_and_integral_eq_one ((continuous_heatDensityPi t).comp
    (by fun_prop)).measurable fun y => (heatDensityPi_pos ht _).le

/-- For `t > 0` and every `y`, `z ↦ heatDensityPi t (y - z)` is Lebesgue integrable. -/
theorem integrable_heatDensityPi_sub' {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    Integrable (fun z => heatDensityPi t (y - z)) := by
  have e : (fun z => heatDensityPi t (y - z)) = fun z => heatDensityPi t (z - y) := by
    funext z; rw [← heatDensityPi_neg, neg_sub]
  rw [e]; exact (integrable_heatDensityPi_sub ht y).1

/-! ### Uniqueness of continuous densities -/

/-- Two continuous nonnegative functions on `Fin d → ℝ` with the same finite density measure
coincide. -/
theorem eq_of_withDensity_eq {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    [IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (f x))]
    (h : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : f = g :=
  MeasureHelpers.eq_of_withDensity_eq hf hg hf0 hg0 h

/-! ### The heat-flow density of a probability measure -/

section HeatFlow

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- For a probability `ρ` and `t > 0`, `y ↦ heatFlowGradPi ρ t y` is continuous. -/
theorem continuous_heatFlowGradPi {t : ℝ} (ht : 0 < t) (i : Fin d) :
    Continuous fun y => heatFlowGradPi ρ t y i :=
  continuous_iff_continuousAt.2 fun y => (hasFDerivAt_heatFlowGradPi ρ ht i y).continuousAt

/-- For a probability `ρ` and `t > 0`, `heatFlowDensityPi ρ t y ≤ (2π t)^{-d/2}`. -/
theorem heatFlowDensityPi_le {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    heatFlowDensityPi ρ t y ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by
  unfold heatFlowDensityPi
  calc ∫ x, heatDensityPi t (y - x) ∂ρ ≤ ∫ _x, (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d ∂ρ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => (heatDensityPi_pos ht _).le)
          (integrable_const _) (Eventually.of_forall fun x => heatDensityPi_le ht _)
    _ = _ := by simp

/-- For a probability `ρ` and `t > 0`,
`|∂ᵢ heatFlowDensityPi ρ t y| ≤ (1 + 2t)/t · (2π t)^{-d/2}`. -/
theorem abs_heatFlowGradPi_le {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) (i : Fin d) :
    |heatFlowGradPi ρ t y i| ≤ (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by
  unfold heatFlowGradPi
  calc |∫ x, heatGradPi t (y - x) i ∂ρ| ≤ ∫ x, |heatGradPi t (y - x) i| ∂ρ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d ∂ρ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun x => abs_heatGradPi_le ht _ i)
    _ = _ := by simp

/-- For a probability `ρ` and `t > 0`, `heatFlowDensityPi ρ t` is Lebesgue integrable with
integral `1`. -/
theorem integrable_heatFlowDensityPi {t : ℝ} (ht : 0 < t) :
    Integrable (heatFlowDensityPi ρ t) ∧ ∫ y, heatFlowDensityPi ρ t y = 1 := by
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi ρ ht
  exact integrable_and_integral_eq_one (continuous_heatFlowDensityPi ρ ht).measurable
    fun y => (heatFlowDensityPi_pos ρ ht y).le

/-- **Heat semigroup, density form.** For a probability `ρ` and `t, a > 0`,
`p_{t+a}(y) = ∫ p_t(z) φ_a(y - z) dz` and `∂ᵢp_{t+a}(y) = ∫ p_t(z) ∂ᵢφ_a(y - z) dz`, where
`p_t = heatFlowDensityPi ρ t`, `φ_a = heatDensityPi a`, `∇φ_a = heatGradPi a`. -/
theorem heatFlow_semigroup {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    (∀ y, heatFlowDensityPi ρ (t + a) y =
      ∫ z, heatFlowDensityPi ρ t z * heatDensityPi a (y - z)) ∧
    ∀ y i, heatFlowGradPi ρ (t + a) y i =
      ∫ z, heatFlowDensityPi ρ t z * heatGradPi a (y - z) i := by
  set μ := heatKernelPi t.toNNReal ∘ₘ ρ with hμ
  have hμd := heatKernelPi_comp_eq_withDensity ρ ht
  have hcomp : heatKernelPi a.toNNReal ∘ₘ μ = heatKernelPi (t + a).toNNReal ∘ₘ ρ := by
    rw [hμ, Measure.comp_assoc, heatKernelPi_comp_heatKernelPi, Real.toNNReal_add ht.le ha.le,
      add_comm]
  have hd := heatKernelPi_comp_eq_withDensity μ ha
  rw [hcomp, heatKernelPi_comp_eq_withDensity ρ (by linarith)] at hd
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi ρ (show 0 < t + a by linarith)
  have heq : heatFlowDensityPi ρ (t + a) = heatFlowDensityPi μ a :=
    eq_of_withDensity_eq (continuous_heatFlowDensityPi ρ (by linarith))
      (continuous_heatFlowDensityPi μ ha)
      (fun y => (heatFlowDensityPi_pos ρ (by linarith) y).le)
      (fun y => (heatFlowDensityPi_pos μ ha y).le) hd
  have hmeas : Measurable fun y => ENNReal.ofReal (heatFlowDensityPi ρ t y) :=
    ENNReal.measurable_ofReal.comp (continuous_heatFlowDensityPi ρ ht).measurable
  have hlt : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)),
      ENNReal.ofReal (heatFlowDensityPi ρ t y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hint : ∀ g : (Fin d → ℝ) → ℝ, ∫ z, g z ∂μ = ∫ z, heatFlowDensityPi ρ t z * g z := by
    intro g
    rw [hμ, hμd, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
    congr 1; funext z
    rw [ENNReal.toReal_ofReal (heatFlowDensityPi_pos ρ ht z).le, smul_eq_mul]
  refine ⟨fun y => by rw [heq]; exact hint _, fun y i => ?_⟩
  have h1 := hasFDerivAt_heatFlowDensityPi ρ (show 0 < t + a by linarith) y
  rw [heq] at h1
  have h2 := congrArg (fun L => L (Pi.single i 1))
    (h1.unique (hasFDerivAt_heatFlowDensityPi μ ha y))
  simp only [dotCLM_single] at h2
  rw [h2]
  exact hint _

end HeatFlow

/-! ### The heat flow of the Gaussian target -/

/-- The isotropic Gaussian `N(0, v I)` on `Fin d → ℝ` is the heat kernel from `0`:
`⊗ᵢ N(0, v) = heatKernelPi v 0`. -/
theorem pi_gaussianReal_eq_heatKernelPi (v : ℝ≥0) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 v) = heatKernelPi v 0 := by
  rw [heatKernelPi_apply]; rfl

/-- For `v, t ≥ 0`, the heat flow of `N(0, v I)` is `N(0, (v + t) I)`:
`heatKernelPi t ∘ₘ N(0, v I) = N(0, (v + t) I)`. -/
theorem heatKernelPi_comp_pi_gaussianReal {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    heatKernelPi t.toNNReal ∘ₘ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) =
      Measure.pi fun _ : Fin d => gaussianReal 0 (v + t).toNNReal := by
  rw [pi_gaussianReal_eq_heatKernelPi, pi_gaussianReal_eq_heatKernelPi]
  change (heatKernelPi v.toNNReal 0).bind (heatKernelPi t.toNNReal) = _
  rw [bind_heatKernelPi, Real.toNNReal_add hv ht, add_comm]

/-- For `v, t > 0`, `heatFlowDensityPi N(0, v I) t = heatDensityPi (v + t)`. -/
theorem heatFlowDensityPi_gaussian {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    heatFlowDensityPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t =
      heatDensityPi (v + t) := by
  have hd := heatKernelPi_comp_eq_withDensity
    (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ht
  rw [heatKernelPi_comp_pi_gaussianReal hv.le ht.le, pi_gaussianReal_eq_heatKernelPi,
    heatKernelPi_eq_withDensity (by linarith)] at hd
  simp_rw [sub_zero] at hd
  have : IsProbabilityMeasure
      (volume.withDensity fun y : Fin d → ℝ => ENNReal.ofReal (heatDensityPi (v + t) y)) := by
    rw [hd, ← heatKernelPi_comp_eq_withDensity _ ht]; infer_instance
  exact (eq_of_withDensity_eq (continuous_heatDensityPi _)
    (continuous_heatFlowDensityPi _ ht) (fun y => (heatDensityPi_pos (by linarith) y).le)
    (fun y => (heatFlowDensityPi_pos _ ht y).le) hd).symm

/-- For `v, t > 0`, `heatFlowGradPi N(0, v I) t = heatGradPi (v + t)`. -/
theorem heatFlowGradPi_gaussian {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    heatFlowGradPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t =
      heatGradPi (v + t) := by
  funext y i
  have h1 := hasFDerivAt_heatFlowDensityPi
    (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ht y
  rw [heatFlowDensityPi_gaussian hv ht] at h1
  have h2 := congrArg (fun L => L (Pi.single i 1)) (h1.unique (hasFDerivAt_heatDensityPi _ y))
  simpa only [dotCLM_single] using h2

/-! ### The relative score of the heat flow against the Gaussian heat flow -/

/-- The relative score flux of the heat flow of `ρ` against `N(0, (v + t) I)`:
`gaussRelFluxPi ρ v t y i = ∂ᵢp_t(y) + yᵢ / (v + t) · p_t(y)`, i.e. `p_t ∇ log(p_t / q_t)` with
`q_t = heatDensityPi (v + t)` (`fisherIntegrand_gaussian`). -/
noncomputable def gaussRelFluxPi (ρ : Measure (Fin d → ℝ)) (v t : ℝ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => heatFlowGradPi ρ t y i + y i / (v + t) * heatFlowDensityPi ρ t y

section Score

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- **Integration by parts against the heat kernel.** For a probability `ρ`, `t, a > 0`, every
`y` and coordinate `i`: `∫ φ_a(y - z) ∂ᵢp_t(z) dz = ∫ p_t(z) ∂ᵢφ_a(y - z) dz`. -/
theorem integral_heatDensityPi_mul_heatFlowGradPi {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (y : Fin d → ℝ) (i : Fin d) :
    ∫ z, heatDensityPi a (y - z) * heatFlowGradPi ρ t z i
      = ∫ z, heatFlowDensityPi ρ t z * heatGradPi a (y - z) i := by
  set C1 := (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d
  set Ca := (1 + 2 * a) / a * (Real.sqrt (2 * Real.pi * a))⁻¹ ^ d
  set Ct := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d
  have hf : ∀ z, HasFDerivAt (fun z => heatDensityPi a (y - z))
      (dotCLM fun j => -heatGradPi a (y - z) j) z := by
    intro z
    have h := (hasFDerivAt_heatDensityPi a (y - z)).comp z
      ((hasFDerivAt_id z).const_sub y)
    refine h.congr_fderiv (eq_dotCLM_of_apply fun w => ?_)
    simp [dotCLM_apply, dotProduct]
  have hg := hasFDerivAt_heatFlowDensityPi ρ ht
  have hfv : ∀ z, fderiv ℝ (fun z => heatDensityPi a (y - z)) z (Pi.single i 1) =
      -heatGradPi a (y - z) i := fun z => by rw [(hf z).fderiv, dotCLM_single]
  have hgv : ∀ z, fderiv ℝ (heatFlowDensityPi ρ t) z (Pi.single i 1) =
      heatFlowGradPi ρ t z i := fun z => by rw [(hg z).fderiv, dotCLM_single]
  have hPi := (integrable_heatFlowDensityPi ρ ht).1
  have hA : Integrable fun z => -heatGradPi a (y - z) i * heatFlowDensityPi ρ t z :=
    hPi.bdd_mul (c := Ca)
      ((((continuous_apply i).comp (continuous_heatGradPi a)).comp
        (by fun_prop : Continuous fun z => y - z)).neg.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_neg]; exact abs_heatGradPi_le ha _ i)
  have hB : Integrable fun z => heatDensityPi a (y - z) * heatFlowGradPi ρ t z i :=
    (integrable_heatDensityPi_sub' ha y).mul_bdd (c := C1)
      (continuous_heatFlowGradPi ρ ht i).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_heatFlowGradPi_le ρ ht z i)
  have hC : Integrable fun z => heatDensityPi a (y - z) * heatFlowDensityPi ρ t z :=
    (integrable_heatDensityPi_sub' ha y).mul_bdd (c := Ct)
      (continuous_heatFlowDensityPi ρ ht).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatFlowDensityPi_pos ρ ht z).le]
        exact heatFlowDensityPi_le ρ ht z)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun z => heatDensityPi a (y - z)) (g := heatFlowDensityPi ρ t)
    (μ := volume) (v := Pi.single i 1)
    (by simp_rw [hfv]; exact hA) (by simp_rw [hgv]; exact hB) hC
    (fun z _ => (hf z).differentiableAt) (fun z _ => (hg z).differentiableAt)
  simp_rw [hfv, hgv] at h
  rw [h, ← integral_neg]
  congr 1; funext z; ring

/-- **Relative score as a heat-kernel average.** For a probability `ρ`, `v, t, a > 0`, every `y`
and coordinate `i`, with `G_t = gaussRelFluxPi ρ v t`:
`∫ φ_a(y - z) G_t(z)ᵢ dz = ((v + t + a) / (v + t)) · G_{t+a}(y)ᵢ`. -/
theorem integral_heatDensityPi_mul_gaussRelFluxPi {v t a : ℝ} (hv : 0 < v) (ht : 0 < t)
    (ha : 0 < a) (y : Fin d → ℝ) (i : Fin d) :
    ∫ z, heatDensityPi a (y - z) * gaussRelFluxPi ρ v t z i
      = (v + t + a) / (v + t) * gaussRelFluxPi ρ v (t + a) y i := by
  obtain ⟨hP, hP1⟩ := heatFlow_semigroup ρ ht ha
  have hPi := (integrable_heatFlowDensityPi ρ ht).1
  have hI1 : Integrable fun z => heatDensityPi a (y - z) * heatFlowGradPi ρ t z i :=
    (integrable_heatDensityPi_sub' ha y).mul_bdd
      (continuous_heatFlowGradPi ρ ht i).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_heatFlowGradPi_le ρ ht z i)
  have hI2 : Integrable fun z => heatFlowDensityPi ρ t z * heatDensityPi a (y - z) :=
    hPi.mul_bdd ((continuous_heatDensityPi a).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatDensityPi_pos ha _).le]; exact heatDensityPi_le ha _)
  have hI3 : Integrable fun z => heatFlowDensityPi ρ t z * heatGradPi a (y - z) i :=
    hPi.mul_bdd (((continuous_apply i).comp (continuous_heatGradPi a)).comp
        (by fun_prop : Continuous fun z => y - z)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_heatGradPi_le ha _ i)
  have hpt : ∀ z, heatDensityPi a (y - z) * gaussRelFluxPi ρ v t z i
      = heatDensityPi a (y - z) * heatFlowGradPi ρ t z i + (1 / (v + t)) *
        (y i * (heatFlowDensityPi ρ t z * heatDensityPi a (y - z))
          + a * (heatFlowDensityPi ρ t z * heatGradPi a (y - z) i)) := by
    intro z
    unfold gaussRelFluxPi heatGradPi
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hI23 : Integrable fun z => 1 / (v + t) *
      (y i * (heatFlowDensityPi ρ t z * heatDensityPi a (y - z))
        + a * (heatFlowDensityPi ρ t z * heatGradPi a (y - z) i)) :=
    ((hI2.const_mul (y i)).add (hI3.const_mul a)).const_mul _
  simp_rw [hpt]
  rw [integral_add hI1 hI23, integral_const_mul,
    integral_add (hI2.const_mul (y i)) (hI3.const_mul a), integral_const_mul,
    integral_const_mul, integral_heatDensityPi_mul_heatFlowGradPi ρ ht ha, ← hP, ← hP1]
  unfold gaussRelFluxPi
  have : v + t ≠ 0 := by linarith
  have : v + (t + a) ≠ 0 := by linarith
  field_simp
  ring

end Score

/-! ### Fisher information decay along the heat flow (Gaussian target) -/

/-- **Weighted Cauchy–Schwarz on `Fin d → ℝ`.** For `k ≥ 0`, `p > 0` and `g` with `k p`, `k g`,
`k g² / p` integrable and `∫ k p > 0`: `(∫ k g)² ≤ (∫ k p) (∫ k g² / p)`. -/
theorem sq_integral_mul_le {k p g : (Fin d → ℝ) → ℝ} (hk : ∀ z, 0 ≤ k z) (hp : ∀ z, 0 < p z)
    (h1 : Integrable fun z => k z * p z) (h2 : Integrable fun z => k z * g z)
    (h3 : Integrable fun z => k z * (g z ^ 2 / p z)) (hC : 0 < ∫ z, k z * p z) :
    (∫ z, k z * g z) ^ 2 ≤ (∫ z, k z * p z) * ∫ z, k z * (g z ^ 2 / p z) :=
  MeasureHelpers.sq_integral_mul_le hk hp h1 h2 h3 hC

section Fisher

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- For a probability `ρ` and `v, t > 0`, the relative Fisher integrand of `ρ_t` against the
Gaussian heat flow `N(0, (v + t) I)` is `|G_t|² / p_t` with `G_t = gaussRelFluxPi ρ v t`. -/
theorem fisherIntegrand_gaussian {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (y : Fin d → ℝ) :
    fisherIntegrand (heatFlowDensityPi ρ)
        (heatFlowDensityPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal))
        (heatFlowGradPi ρ)
        (heatFlowGradPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)) t y
      = (∑ i, gaussRelFluxPi ρ v t y i ^ 2) / heatFlowDensityPi ρ t y := by
  have hP := (heatFlowDensityPi_pos ρ ht y).ne'
  have hq := (heatDensityPi_pos (show 0 < v + t by linarith) y).ne'
  have hvt : v + t ≠ 0 := by linarith
  unfold fisherIntegrand relScore
  rw [heatFlowDensityPi_gaussian hv ht, heatFlowGradPi_gaussian hv ht, dotProduct,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold gaussRelFluxPi heatGradPi
  field_simp
  ring

/-- `y ↦ gaussRelFluxPi ρ v t y i` is continuous for `t > 0`. -/
theorem continuous_gaussRelFluxPi {v t : ℝ} (ht : 0 < t) (i : Fin d) :
    Continuous fun y => gaussRelFluxPi ρ v t y i :=
  (continuous_heatFlowGradPi ρ ht i).add
    (((continuous_apply i).div_const _).mul (continuous_heatFlowDensityPi ρ ht))

/-- **Fisher information decay along the heat flow, Gaussian target.** For a probability `ρ` on
`Fin d → ℝ`, `π = N(0, v I)` (`v > 0`), `t, a > 0` and integrable relative Fisher integrand at
time `t`: `I(ρ_{t+a}‖π_{t+a}) ≤ ((v + t) / (v + t + a))² · I(ρ_t‖π_t)` (`I = heatFisher`). -/
theorem heatFisher_gaussian_le {v t a : ℝ} (hv : 0 < v) (ht : 0 < t) (ha : 0 < a)
    (hint : Integrable (fisherIntegrand (heatFlowDensityPi ρ)
      (heatFlowDensityPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal))
      (heatFlowGradPi ρ)
      (heatFlowGradPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)) t)) :
    heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) (t + a)
      ≤ ((v + t) / (v + t + a)) ^ 2 *
        heatFisher ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t := by
  set π := Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal with hπ
  set p := heatFlowDensityPi ρ t with hp
  set G := gaussRelFluxPi ρ v t with hG
  set F : (Fin d → ℝ) → ℝ := fun z => (∑ i, G z i ^ 2) / p z with hF
  set c := (v + t) / (v + t + a) with hc
  set Ca := (Real.sqrt (2 * Real.pi * a))⁻¹ ^ d with hCa
  have hFeq : fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
      (heatFlowGradPi ρ) (heatFlowGradPi π) t = F :=
    funext fun y => fisherIntegrand_gaussian ρ hv ht y
  rw [hFeq] at hint
  have hp0 : ∀ z, 0 < p z := heatFlowDensityPi_pos ρ ht
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hp0 z).le
  have hGc : ∀ i, Continuous fun z => G z i := fun i => continuous_gaussRelFluxPi ρ ht i
  have hpc : Continuous p := continuous_heatFlowDensityPi ρ ht
  have hFc : Continuous F := (continuous_finsetSum _ fun i _ => (hGc i).pow 2).div hpc
    fun z => (hp0 z).ne'
  have hFi : ∀ i z, G z i ^ 2 / p z ≤ F z := fun i z =>
    div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun j => G z j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)) (hp0 z).le
  have hPta : ∀ y, 0 < heatFlowDensityPi ρ (t + a) y :=
    heatFlowDensityPi_pos ρ (by linarith)
  have hkc : ∀ y : Fin d → ℝ, Continuous fun z => heatDensityPi a (y - z) := fun y =>
    (continuous_heatDensityPi a).comp (by fun_prop)
  -- pointwise bound
  have hpt : ∀ y, (∑ i, gaussRelFluxPi ρ v (t + a) y i ^ 2) / heatFlowDensityPi ρ (t + a) y
      ≤ c ^ 2 * ∫ z, heatDensityPi a (y - z) * F z := by
    intro y
    have hk : ∀ z, 0 ≤ heatDensityPi a (y - z) := fun z => (heatDensityPi_pos ha _).le
    have hkb : ∀ z, ‖heatDensityPi a (y - z)‖ ≤ Ca := fun z => by
      rw [Real.norm_of_nonneg (hk z)]; exact heatDensityPi_le ha _
    have h1 : Integrable fun z => heatDensityPi a (y - z) * p z :=
      (integrable_heatFlowDensityPi ρ ht).1.bdd_mul (c := Ca)
        (hkc y).aestronglyMeasurable (Eventually.of_forall hkb)
    have h3F : Integrable fun z => heatDensityPi a (y - z) * F z :=
      hint.bdd_mul (c := Ca) (hkc y).aestronglyMeasurable (Eventually.of_forall hkb)
    have h3 : ∀ i, Integrable fun z => heatDensityPi a (y - z) * (G z i ^ 2 / p z) := by
      intro i
      refine h3F.mono ((hkc y).mul (((hGc i).pow 2).div hpc
        fun z => (hp0 z).ne')).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hk z),
        abs_of_nonneg (div_nonneg (sq_nonneg _) (hp0 z).le), abs_of_nonneg (hF0 z)]
      exact mul_le_mul_of_nonneg_left (hFi i z) (hk z)
    have h2 : ∀ i, Integrable fun z => heatDensityPi a (y - z) * G z i := by
      intro i
      have h13 : Integrable fun z => (heatDensityPi a (y - z) * p z
          + heatDensityPi a (y - z) * (G z i ^ 2 / p z)) / 2 := (h1.add (h3 i)).div_const 2
      refine h13.mono' ((hkc y).mul (hGc i)).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      have hpz := hp0 z
      have hamgm : |G z i| ≤ (p z + G z i ^ 2 / p z) / 2 := by
        rw [abs_le]
        have e : G z i ^ 2 / p z * p z = G z i ^ 2 := div_mul_cancel₀ _ hpz.ne'
        constructor <;> nlinarith [sq_nonneg (G z i - p z), sq_nonneg (G z i + p z)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk z)]
      calc heatDensityPi a (y - z) * |G z i|
          ≤ heatDensityPi a (y - z) * ((p z + G z i ^ 2 / p z) / 2) :=
            mul_le_mul_of_nonneg_left hamgm (hk z)
        _ = _ := by ring
    have hC : ∫ z, heatDensityPi a (y - z) * p z = heatFlowDensityPi ρ (t + a) y := by
      rw [(heatFlow_semigroup ρ ht ha).1 y]; congr 1; funext z; ring
    have hca : (v + t + a) / (v + t) * c = 1 := by rw [hc]; field_simp
    have hCSi : ∀ i, gaussRelFluxPi ρ v (t + a) y i ^ 2 ≤
        c ^ 2 * (heatFlowDensityPi ρ (t + a) y *
          ∫ z, heatDensityPi a (y - z) * (G z i ^ 2 / p z)) := by
      intro i
      have hCS := sq_integral_mul_le hk hp0 h1 (h2 i) (h3 i) (by rw [hC]; exact hPta y)
      rw [hC, integral_heatDensityPi_mul_gaussRelFluxPi ρ hv ht ha y i] at hCS
      calc gaussRelFluxPi ρ v (t + a) y i ^ 2
          = c ^ 2 * ((v + t + a) / (v + t) * gaussRelFluxPi ρ v (t + a) y i) ^ 2 := by
            rw [mul_pow, ← mul_assoc, ← mul_pow, mul_comm c, hca, one_pow, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    have hsumF : ∑ i, ∫ z, heatDensityPi a (y - z) * (G z i ^ 2 / p z) =
        ∫ z, heatDensityPi a (y - z) * F z := by
      rw [← integral_finsetSum _ fun i _ => h3 i]
      congr 1; funext z
      rw [← Finset.mul_sum, hF]; simp only; rw [Finset.sum_div]
    rw [div_le_iff₀ (hPta y)]
    calc ∑ i, gaussRelFluxPi ρ v (t + a) y i ^ 2
        ≤ ∑ i, c ^ 2 * (heatFlowDensityPi ρ (t + a) y *
            ∫ z, heatDensityPi a (y - z) * (G z i ^ 2 / p z)) :=
          Finset.sum_le_sum fun i _ => hCSi i
      _ = c ^ 2 * (∫ z, heatDensityPi a (y - z) * F z) * heatFlowDensityPi ρ (t + a) y := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hsumF]; ring
  -- integrate in `y`
  have hHm : AEStronglyMeasurable
      (fun q : (Fin d → ℝ) × (Fin d → ℝ) => heatDensityPi a (q.1 - q.2) * F q.2)
      (volume.prod volume) :=
    (((continuous_heatDensityPi a).comp (continuous_fst.sub continuous_snd)).mul
      (hFc.comp continuous_snd)).aestronglyMeasurable
  have hH : Integrable
      (fun q : (Fin d → ℝ) × (Fin d → ℝ) => heatDensityPi a (q.1 - q.2) * F q.2)
      (volume.prod volume) := by
    refine (integrable_prod_iff' hHm).2 ⟨Eventually.of_forall fun z => by
      simpa only using (integrable_heatDensityPi_sub ha z).1.mul_const (F z), ?_⟩
    refine hint.congr (Eventually.of_forall fun z => ?_)
    simp only
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatDensityPi_pos ha _),
      abs_of_nonneg (hF0 z)]
    rw [integral_mul_const, (integrable_heatDensityPi_sub ha z).2, one_mul]
  have hswap := integral_integral_swap (f := fun y z => heatDensityPi a (y - z) * F z) hH
  have hinner : ∫ z, ∫ y, heatDensityPi a (y - z) * F z = ∫ z, F z := by
    congr 1; funext z
    rw [integral_mul_const, (integrable_heatDensityPi_sub ha z).2, one_mul]
  unfold heatFisher
  rw [hFeq]
  have hFeq' : fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
      (heatFlowGradPi ρ) (heatFlowGradPi π) (t + a)
      = fun y => (∑ i, gaussRelFluxPi ρ v (t + a) y i ^ 2) / heatFlowDensityPi ρ (t + a) y :=
    funext fun y => fisherIntegrand_gaussian ρ hv (by linarith) y
  rw [hFeq']
  calc ∫ y, (∑ i, gaussRelFluxPi ρ v (t + a) y i ^ 2) / heatFlowDensityPi ρ (t + a) y
      ≤ ∫ y, c ^ 2 * ∫ z, heatDensityPi a (y - z) * F z :=
        integral_mono_of_nonneg (Eventually.of_forall fun y =>
          div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hPta y).le)
          (hH.integral_prod_left.const_mul _) (Eventually.of_forall hpt)
    _ = c ^ 2 * ∫ z, F z := by rw [integral_const_mul, hswap, hinner]

end Fisher

/-! ### Vanishing of the heat-flow KL at large times -/

/-- If `ρ` and `π` have finite second moments (`∫ ∑ᵢ xᵢ² < ∞`), then
`(x, u) ↦ ∑ᵢ (xᵢ - uᵢ)²` is integrable under `ρ ⊗ π`. -/
theorem integrable_sum_sub_sq_prod {ρ π : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] (hρ : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    (hπ : Integrable (fun x => ∑ i, x i ^ 2) π) :
    Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) => ∑ i, (q.1 i - q.2 i) ^ 2) (ρ.prod π) := by
  refine (((hρ.comp_fst π).const_mul 2).add ((hπ.comp_snd ρ).const_mul 2)).mono'
    (by fun_prop : Continuous fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
      ∑ i, (q.1 i - q.2 i) ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (q.1 i + q.2 i)]

/-- **Large-time KL bound along the heat flow.** For probability measures `ρ, π` on `Fin d → ℝ`
with `(x, u) ↦ ∑ᵢ (xᵢ - uᵢ)²` integrable under `ρ ⊗ π` and `T > 0`:
`KL(ρ_T‖π_T) ≤ (∫ |x - u|² d(ρ ⊗ π)) / (2T)`. Proof: `ρ_T`, `π_T` are the images of `ρ ⊗ π`
under the kernels `(x, u) ↦ N(x, T I)`, `(x, u) ↦ N(u, T I)`; apply the KL chain rule
(`KL.klDiv_comp_comp_le`) and `KL(N(x, T I)‖N(u, T I)) = |x - u|² / (2T)`. -/
theorem heatKL_le_div_two_mul (ρ π : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π]
    (hint : Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) => ∑ i, (q.1 i - q.2 i) ^ 2)
      (ρ.prod π)) {T : ℝ} (hT : 0 < T) :
    heatKL ρ π T ≤ (∫ q, ∑ i, (q.1 i - q.2 i) ^ 2 ∂(ρ.prod π)) / (2 * T) := by
  set κ := heatKernelPi (d := d) T.toNNReal
  set Q : Kernel ((Fin d → ℝ) × (Fin d → ℝ)) (Fin d → ℝ) := Kernel.prodMkRight (Fin d → ℝ) κ
  set P : Kernel ((Fin d → ℝ) × (Fin d → ℝ)) (Fin d → ℝ) := Kernel.prodMkLeft (Fin d → ℝ) κ
  have hQ : Q ∘ₘ (ρ.prod π) = κ ∘ₘ ρ := by
    have : Q = κ ∘ₖ Kernel.deterministic Prod.fst measurable_fst :=
      (Kernel.comp_deterministic_eq_comap κ measurable_fst).symm
    rw [this, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, Measure.map_fst_prod]
    simp
  have hP : P ∘ₘ (ρ.prod π) = κ ∘ₘ π := by
    have : P = κ ∘ₖ Kernel.deterministic Prod.snd measurable_snd :=
      (Kernel.comp_deterministic_eq_comap κ measurable_snd).symm
    rw [this, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, Measure.map_snd_prod]
    simp
  have hT' : T.toNNReal ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hT
  have hkl : ∀ q : (Fin d → ℝ) × (Fin d → ℝ), klDiv (Q q) (P q) =
      ENNReal.ofReal ((∑ i, (q.1 i - q.2 i) ^ 2) / (2 * T)) := by
    intro q
    rw [Kernel.prodMkRight_apply, Kernel.prodMkLeft_apply, heatKernelPi_apply,
      heatKernelPi_apply, GaussianIncrement.klDiv_pi_gaussianReal _ _ hT',
      Real.coe_toNNReal _ hT.le]
  have h := FormalizeSampling.KL.klDiv_comp_comp_le (ρ.prod π) (ρ.prod π) Q P
  rw [hQ, hP, klDiv_self, zero_add] at h
  simp_rw [hkl] at h
  have hint' : Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
      (∑ i, (q.1 i - q.2 i) ^ 2) / (2 * T)) (ρ.prod π) := hint.div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (Eventually.of_forall fun q => by positivity)] at h
  calc heatKL ρ π T
      ≤ (ENNReal.ofReal (∫ q, (∑ i, (q.1 i - q.2 i) ^ 2) / (2 * T) ∂(ρ.prod π))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = _ := by
        rw [ENNReal.toReal_ofReal (integral_nonneg fun q => by positivity), integral_div]

/-! ### Finiteness of KL along a regular heat flow -/

/-- The relative Fisher information along the heat flow is nonnegative for `t > 0`. -/
theorem heatFisher_nonneg (ρ π : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {t : ℝ}
    (ht : 0 < t) : 0 ≤ heatFisher ρ π t :=
  integral_nonneg fun y => mul_nonneg (heatFlowDensityPi_pos ρ ht y).le
    (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- `N(0, v I)` on `Fin d → ℝ` has a finite second moment: `x ↦ ∑ᵢ xᵢ²` is integrable. -/
theorem integrable_sum_sq_pi_gaussianReal (v : ℝ) :
    Integrable (fun x => ∑ i, x i ^ 2) (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) := by
  have h1 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v.toNNReal) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := v.toNNReal) 2).integrable_sq
    simpa using this
  exact integrable_finsetSum _ fun i _ =>
    integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 0 v.toNNReal) (i := i)
      (f := fun x : ℝ => x ^ 2) h1

/-- **KL is finite along a regular isotropic heat flow.** For probability measures `ρ, π` on
`Fin d → ℝ` with `HeatFlowRegularPi ρ π s` and `t ∈ s`,
`KL(ρ_t‖π_t) = KL(heatKernelPi t ∘ₘ ρ‖heatKernelPi t ∘ₘ π) ≠ ∞` (the integrability field
`integrable_kl` gives a finite density integral). So the real number
`heatKL ρ π t = KL(ρ_t‖π_t).toReal` is the actual divergence, not the junk value of `∞`. -/
theorem klDiv_heatKernelPi_comp_ne_top_of_regular {ρ π : Measure (Fin d → ℝ)}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure π] {s : Set ℝ}
    (hreg : HeatFlowRegularPi ρ π s) {t : ℝ} (hts : t ∈ s) :
    klDiv (heatKernelPi t.toNNReal ∘ₘ ρ) (heatKernelPi t.toNNReal ∘ₘ π) ≠ ⊤ := by
  have ht : 0 < t := hreg.subset_Ioi hts
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi ρ ht
  have := isProbabilityMeasure_withDensity_heatFlowDensityPi π ht
  rw [heatKernelPi_comp_eq_withDensity ρ ht, heatKernelPi_comp_eq_withDensity π ht,
    KLTransport.klDiv_withDensity_eq_integral (continuous_heatFlowDensityPi ρ ht).measurable
      (continuous_heatFlowDensityPi π ht).measurable (fun y => (heatFlowDensityPi_pos ρ ht y).le)
      (heatFlowDensityPi_pos π ht) (hreg.integrable_kl t hts)]
  exact ENNReal.ofReal_ne_top

/-- **KL to the smoothed isotropic Gaussian target is finite.** For a probability measure `ρ`
on `Fin d → ℝ`, `v, t > 0` and `HeatFlowRegularPi ρ N(0, v I) (Ioi 0)` (no moment assumption),
`KL(ρ_t‖N(0, (v + t) I)) ≠ ∞` where `ρ_t = heatKernelPi t ∘ₘ ρ`. With a finite second moment
instead of `HeatFlowRegularPi`, see `HeatFlowRegularityPi.klDiv_heatKernelPi_comp_ne_top_of_moment`.
-/
theorem klDiv_heatKernelPi_comp_gaussian_ne_top (ρ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] {v : ℝ} (hv : 0 < v)
    (hreg : HeatFlowRegularPi ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) (Ioi 0))
    {t : ℝ} (ht : 0 < t) :
    klDiv (heatKernelPi t.toNNReal ∘ₘ ρ)
      (Measure.pi fun _ : Fin d => gaussianReal 0 (v + t).toNNReal) ≠ ⊤ := by
  have h := klDiv_heatKernelPi_comp_ne_top_of_regular hreg (show t ∈ Ioi 0 from ht)
  rwa [heatKernelPi_comp_pi_gaussianReal hv.le ht.le] at h

/-- Satisfiability of a finite second moment together with the regularity hypothesis of
`klDiv_heatKernelPi_comp_gaussian_ne_top`: `ρ = N(0, v I)` has a finite second moment and
`HeatFlowRegularPi ρ ρ (Ioi 0)` holds. -/
theorem gaussian_hypotheses_satisfiable (v : ℝ) :
    Integrable (fun x => ∑ i, x i ^ 2) (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ∧
      HeatFlowRegularPi (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) (Ioi 0) :=
  ⟨integrable_sum_sq_pi_gaussianReal v, heatFlowRegularPi_self _⟩

end FormalizeSampling.GaussianLSIPi
