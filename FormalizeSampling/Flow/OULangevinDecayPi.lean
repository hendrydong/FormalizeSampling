module

public import FormalizeSampling.Flow.OULangevinDecay
public import FormalizeSampling.Foundations.HeatFlowRegularityPi
public import FormalizeSampling.Foundations.GaussianLSIPi

/-!
# FL-4 for the OU / Langevin flow with isotropic Gaussian target on `Fin d → ℝ`

Registry ID: **FL-4** (unconditional instance: Langevin flow for the isotropic Gaussian target,
i.e. the product Ornstein–Uhlenbeck semigroup; the `d`-dimensional counterpart of
`Flow/OULangevinDecay.lean`).

Status: **Verified**. Hypotheses on the initial law `ρ`: probability measure on `Fin d → ℝ`,
`KL(ρ‖π) < ∞` and `∫ ∑ᵢ xᵢ² dρ < ∞`. No regularity or functional-inequality hypothesis.

Setting: the product OU kernel with stationary law `N(0, v I)` (`v > 0`) and rate `a ≥ 0`,
`ouKernelVarPi v a t x = ⊗ᵢ N(e^{-at} xᵢ, v (1 - e^{-2at}))`, defined as the heat kernel
`heatKernelPi (v (1 - e^{-2at}))` precomposed with the scaling `x ↦ e^{-at} x`; for `v = 1` it is
`ouKernelPi a t x = ⊗ᵢ OU.ouKernel a t (xᵢ)` (`ouKernelPi_apply`, `ouKernelPi_eq_ouKernelVarPi`).

## Idea

As in dimension one, with `c = e^{-at}` and `w = v (1 - c²)`:
`ouKernelVarPi v a t ∘ₘ ρ = heatKernelPi w ∘ₘ ρ.map (c • ·)`, `N(0, v I).map (c • ·) =
N(0, c² v I)` and `heatKernelPi w ∘ₘ N(0, c² v I) = N(0, v I)`. The heat-flow contraction
`GaussianLSIPi.toReal_klDiv_heatKernelPi_le_gaussian` with `α = (c² v)⁻¹`, `η = w` gives the
factor `1/(1 + α η) = c² = e^{-2at}`, and the scaling does not increase KL.

## Main results

* `toReal_klDiv_ouKernelVarPi_comp_le` (general variance), `toReal_klDiv_ouKernelPi_comp_le`
  (`v = 1`): `KL(ρ_t‖N(0, v I)) < ∞` and `KL(ρ_t‖N(0, v I)) ≤ e^{-2at} KL(ρ‖N(0, v I))`.
* `toReal_klDiv_ouKernelVarPi_comp_gaussian`, `toReal_klDiv_ouKernelPi_comp_gaussian`
  (tightness): for `ρ = N(m, v I)`, `KL(ρ_t‖N(0, v I)) = e^{-2at} KL(ρ‖N(0, v I))
  = e^{-2at} ∑ᵢ mᵢ² / (2v)`.
* `tvSup_ouKernelVarPi_comp_le`, `tvSup_ouKernelPi_comp_le` (Pinsker).

## Not proved here

* That `ouKernelVarPi` is the transition kernel of the OU SDE (it is the definition here).
* Anisotropic Gaussian targets and non-Gaussian targets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal FormalizeSampling.OU

namespace FormalizeSampling.OULangevinDecayPi

open FormalizeSampling.OU FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowRegularityPi
  FormalizeSampling.OULangevinDecay
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi
  integrable_sum_sq_map_scalePi)

variable {d : ℕ}

/-! ### The product OU kernel -/

/-- The product OU kernel on `Fin d → ℝ` with stationary law `N(0, v I)` and rate `a`:
`ouKernelVarPi v a t x = ⊗ᵢ N(e^{-at} xᵢ, v (1 - e^{-2at}))` (variance truncated at `0`). -/
noncomputable def ouKernelVarPi (v a t : ℝ) : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (heatKernelPi (v * (1 - Real.exp (-2 * a * t))).toNNReal).comap
    (scalePi (Real.exp (-a * t))) (measurable_scalePi _)

/-- Evaluation: `ouKernelVarPi v a t x = ⊗ᵢ N(e^{-at} xᵢ, v (1 - e^{-2at}))`. -/
theorem ouKernelVarPi_apply (v a t : ℝ) (x : Fin d → ℝ) :
    ouKernelVarPi v a t x = Measure.pi fun i =>
      gaussianReal (Real.exp (-a * t) * x i) (v * (1 - Real.exp (-2 * a * t))).toNNReal := rfl

/-- `ouKernelVarPi v a t` is a Markov kernel. -/
instance isMarkovKernel_ouKernelVarPi (v a t : ℝ) :
    IsMarkovKernel (ouKernelVarPi (d := d) v a t) := by
  unfold ouKernelVarPi; infer_instance

/-- The standard product OU kernel (stationary law `N(0, I)`):
`ouKernelPi a t x = ⊗ᵢ N(e^{-at} xᵢ, ouVar a t)`. -/
noncomputable def ouKernelPi (a t : ℝ) : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (heatKernelPi (ouVar a t)).comap (scalePi (Real.exp (-a * t))) (measurable_scalePi _)

/-- The product OU kernel acts coordinatewise: `ouKernelPi a t x = ⊗ᵢ ouKernel a t (xᵢ)`. -/
theorem ouKernelPi_apply (a t : ℝ) (x : Fin d → ℝ) :
    ouKernelPi a t x = Measure.pi fun i => ouKernel a t (x i) := rfl

/-- `ouKernelPi a t` is a Markov kernel. -/
instance isMarkovKernel_ouKernelPi (a t : ℝ) : IsMarkovKernel (ouKernelPi (d := d) a t) := by
  unfold ouKernelPi; infer_instance

/-- The standard product OU kernel is the case `v = 1`: `ouKernelPi a t = ouKernelVarPi 1 a t`. -/
theorem ouKernelPi_eq_ouKernelVarPi (a t : ℝ) :
    ouKernelPi (d := d) a t = ouKernelVarPi 1 a t := by
  rw [ouKernelPi, ouKernelVarPi, ouVar, one_mul]

/-! ### Scaling identities -/

/-- The product OU step is a heat step after scaling: for any measure `μ`,
`ouKernelVarPi v a t ∘ₘ μ = heatKernelPi (v (1 - e^{-2at})) ∘ₘ μ.map (e^{-at} • ·)`. -/
theorem ouKernelVarPi_comp_eq (v a t : ℝ) (μ : Measure (Fin d → ℝ)) :
    ouKernelVarPi v a t ∘ₘ μ = heatKernelPi (v * (1 - Real.exp (-2 * a * t))).toNNReal ∘ₘ
      μ.map (scalePi (Real.exp (-a * t))) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (measurable_scalePi _)]
  rfl

/-- Scaling an isotropic Gaussian: for `v ≥ 0`,
`N(m, v I).map (c • ·) = N(c m, c² v I)`. -/
theorem pi_gaussianReal_map_scalePi (c : ℝ) {v : ℝ} (hv : 0 ≤ v) (m : Fin d → ℝ) :
    (Measure.pi fun i => gaussianReal (m i) v.toNNReal).map (scalePi c) =
      Measure.pi fun i => gaussianReal (c * m i) (c ^ 2 * v).toNNReal := by
  rw [show scalePi (d := d) c = fun x i => c * x i from rfl,
    Measure.pi_map_pi (fun _ => (measurable_const_mul _).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv,
    Real.coe_toNNReal _ (by positivity)]

/-- The heat step `w = v (1 - c²)` from `N(c m, c² v I)` gives `N(c m, v I)` (`v ≥ 0`, `c² ≤ 1`).
-/
theorem heatKernelPi_comp_pi_gaussianReal_scaled {c v : ℝ} (hv : 0 ≤ v) (hc : c ^ 2 ≤ 1)
    (m : Fin d → ℝ) :
    heatKernelPi (v * (1 - c ^ 2)).toNNReal ∘ₘ
        (Measure.pi fun i => gaussianReal (m i) (c ^ 2 * v).toNNReal) =
      Measure.pi fun i => gaussianReal (m i) v.toNNReal := by
  have h1 : 0 ≤ v * (1 - c ^ 2) := mul_nonneg hv (by linarith)
  have e : v.toNNReal = (v * (1 - c ^ 2)).toNNReal + (c ^ 2 * v).toNNReal := by
    rw [← Real.toNNReal_add h1 (by positivity)]; ring_nf
  rw [e, ← heatKernelPi_apply, ← heatKernelPi_apply, ← bind_heatKernelPi]

/-! ### Exponential KL decay along the product OU flow -/

/-- **Core contraction.** For `0 < c < 1`, `v > 0` and a probability law `ρ` on `Fin d → ℝ`
with `KL(ρ‖N(0, v I)) < ∞` and `∫ ∑ᵢ xᵢ² dρ < ∞`:
`KL(heatKernelPi (v (1 - c²)) ∘ₘ ρ.map (c • ·)‖N(0, v I)) < ∞` and its `toReal` is at most
`c² KL(ρ‖N(0, v I)).toReal`. -/
theorem toReal_klDiv_heatKernelPi_comp_map_le {c v : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hv : 0 < v) (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    klDiv (heatKernelPi (v * (1 - c ^ 2)).toNNReal ∘ₘ ρ.map (scalePi c))
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ≠ ∞ ∧
      (klDiv (heatKernelPi (v * (1 - c ^ 2)).toNNReal ∘ₘ ρ.map (scalePi c))
          (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal
        ≤ c ^ 2 * (klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal := by
  have hc2 : c ^ 2 < 1 := by nlinarith
  have hc2p : 0 < c ^ 2 := by positivity
  set μ := ρ.map (scalePi c) with hμ
  have : IsProbabilityMeasure μ := by
    rw [hμ]; infer_instance
  have hmomμ : Integrable (fun x => ∑ i, x i ^ 2) μ := integrable_sum_sq_map_scalePi ρ hmom c
  have hmap := klDiv_map_le ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
    (measurable_scalePi c)
  have hg := pi_gaussianReal_map_scalePi (d := d) c hv.le 0
  simp only [Pi.zero_apply, mul_zero] at hg
  rw [hg] at hmap
  have hKLμ : klDiv μ (Measure.pi fun _ : Fin d => gaussianReal 0 (c ^ 2 * v).toNNReal) ≠ ∞ :=
    ne_top_of_le_ne_top hKL hmap
  have hπ := heatKernelPi_comp_pi_gaussianReal_scaled (d := d) hv.le hc2.le 0
  simp only [Pi.zero_apply] at hπ
  have hdp := klDiv_comp_right_le (μ := μ)
    (ν := Measure.pi fun _ : Fin d => gaussianReal 0 (c ^ 2 * v).toNNReal)
    (heatKernelPi (v * (1 - c ^ 2)).toNNReal)
  rw [hπ] at hdp
  refine ⟨ne_top_of_le_ne_top hKLμ hdp, ?_⟩
  have hα : 0 < (c ^ 2 * v)⁻¹ := by positivity
  have hη : 0 < v * (1 - c ^ 2) := mul_pos hv (by linarith)
  have hKLμ' : klDiv μ (Measure.pi fun _ : Fin d => gaussianReal 0 (c ^ 2 * v)⁻¹⁻¹.toNNReal)
      ≠ ∞ := by rwa [inv_inv]
  have h := GaussianLSIPi.toReal_klDiv_heatKernelPi_le_gaussian hα hη μ hKLμ' hmomμ
  rw [inv_inv, hπ] at h
  have e : 1 + (c ^ 2 * v)⁻¹ * (v * (1 - c ^ 2)) = (c ^ 2)⁻¹ := by
    field_simp; ring
  rw [e, div_inv_eq_mul] at h
  refine h.trans ?_
  rw [mul_comm]
  gcongr

/-- If `a t = 0`, the product OU flow is the identity. -/
theorem ouKernelVarPi_comp_of_mul_eq_zero {v a t : ℝ} (h : a * t = 0)
    (ρ : Measure (Fin d → ℝ)) : ouKernelVarPi v a t ∘ₘ ρ = ρ := by
  rw [ouKernelVarPi_comp_eq, show -a * t = -(a * t) by ring,
    show -2 * a * t = -2 * (a * t) by ring, h]
  have hs : scalePi (d := d) 1 = id := by
    funext x i; simp [scalePi]
  simp [hs, heatKernelPi_zero, Measure.id_comp]

/-- **FL-4 for the product OU flow with stationary law `N(0, v I)` (Verified,
unconditional).** For `v > 0`, `a, t ≥ 0` and a probability law `ρ` on `Fin d → ℝ` with
`KL(ρ‖N(0, v I)) < ∞` and `∫ ∑ᵢ xᵢ² dρ < ∞`: `KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)) < ∞` and
`KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)).toReal ≤ e^{-2at} KL(ρ‖N(0, v I)).toReal`. -/
theorem toReal_klDiv_ouKernelVarPi_comp_le {v a t : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    klDiv (ouKernelVarPi v a t ∘ₘ ρ) (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
        ≠ ∞ ∧
      (klDiv (ouKernelVarPi v a t ∘ₘ ρ)
          (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal
        ≤ Real.exp (-2 * a * t) *
          (klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal := by
  rcases (mul_nonneg ha ht).eq_or_lt with h0 | hpos
  · rw [ouKernelVarPi_comp_of_mul_eq_zero h0.symm, show -2 * a * t = -2 * (a * t) by ring,
      ← h0, mul_zero, Real.exp_zero, one_mul]
    exact ⟨hKL, le_rfl⟩
  · have hc0 : 0 < Real.exp (-a * t) := Real.exp_pos _
    have hc1 : Real.exp (-a * t) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have h := toReal_klDiv_heatKernelPi_comp_map_le hc0 hc1 hv ρ hKL hmom
    rw [exp_neg_mul_sq] at h
    rwa [ouKernelVarPi_comp_eq]

/-- **FL-4 for the standard product OU flow (Verified, unconditional).** For `a, t ≥ 0` and a
probability law `ρ` on `Fin d → ℝ` with `KL(ρ‖N(0, I)) < ∞` and `∫ ∑ᵢ xᵢ² dρ < ∞`:
`KL(ouKernelPi a t ∘ₘ ρ‖N(0, I)) < ∞` and
`KL(ouKernelPi a t ∘ₘ ρ‖N(0, I)).toReal ≤ e^{-2at} KL(ρ‖N(0, I)).toReal`. -/
theorem toReal_klDiv_ouKernelPi_comp_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≠ ∞)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    klDiv (ouKernelPi a t ∘ₘ ρ) (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≠ ∞ ∧
      (klDiv (ouKernelPi a t ∘ₘ ρ) (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal
        ≤ Real.exp (-2 * a * t) *
          (klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal := by
  have h1 : (1 : ℝ).toNNReal = 1 := Real.toNNReal_one
  rw [← h1] at hKL ⊢
  rw [ouKernelPi_eq_ouKernelVarPi]
  exact toReal_klDiv_ouKernelVarPi_comp_le one_pos ha ht ρ hKL hmom

/-! ### Tightness: Gaussian initial laws `N(m, v I)` with the target's covariance -/

/-- The product OU flow with stationary law `N(0, v I)` maps `N(m, v I)` to `N(e^{-at} m, v I)`
(`v ≥ 0`, `a, t ≥ 0`). -/
theorem ouKernelVarPi_comp_pi_gaussianReal {v a t : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (m : Fin d → ℝ) :
    ouKernelVarPi v a t ∘ₘ (Measure.pi fun i => gaussianReal (m i) v.toNNReal) =
      Measure.pi fun i => gaussianReal (Real.exp (-a * t) * m i) v.toNNReal := by
  have hc : Real.exp (-a * t) ^ 2 ≤ 1 := by
    rw [exp_neg_mul_sq]; exact Real.exp_le_one_iff.2 (by nlinarith)
  rw [ouKernelVarPi_comp_eq, pi_gaussianReal_map_scalePi _ hv, ← exp_neg_mul_sq]
  exact heatKernelPi_comp_pi_gaussianReal_scaled hv hc _

/-- **Tightness of FL-4 in dimension `d` (general variance).** For `v > 0`, `a, t ≥ 0` and
`ρ = N(m, v I)`: `KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)).toReal = e^{-2at} KL(ρ‖N(0, v I)).toReal
= e^{-2at} ∑ᵢ mᵢ² / (2v)`. -/
theorem toReal_klDiv_ouKernelVarPi_comp_gaussian {v a t : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (ht : 0 ≤ t) (m : Fin d → ℝ) :
    (klDiv (ouKernelVarPi v a t ∘ₘ (Measure.pi fun i => gaussianReal (m i) v.toNNReal))
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal
        = Real.exp (-2 * a * t) * (klDiv (Measure.pi fun i => gaussianReal (m i) v.toNNReal)
          (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal ∧
      (klDiv (ouKernelVarPi v a t ∘ₘ (Measure.pi fun i => gaussianReal (m i) v.toNNReal))
          (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal
        = Real.exp (-2 * a * t) * ((∑ i, m i ^ 2) / (2 * v)) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  have hkl : ∀ m' : Fin d → ℝ, (klDiv (Measure.pi fun i => gaussianReal (m' i) v.toNNReal)
      (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal
      = (∑ i, m' i ^ 2) / (2 * v) := fun m' => by
    have h := GaussianIncrement.klDiv_pi_gaussianReal m' (fun _ => 0) hv0
    simp only [sub_zero] at h
    rw [h, Real.coe_toNNReal _ hv.le, ENNReal.toReal_ofReal (by positivity)]
  rw [ouKernelVarPi_comp_pi_gaussianReal hv.le ha ht, hkl, hkl]
  simp_rw [mul_pow, exp_neg_mul_sq, ← Finset.mul_sum]
  constructor <;> ring

/-- **Tightness of FL-4 in dimension `d` (standard OU).** For `a, t ≥ 0` and `ρ = N(m, I)`:
`KL(ouKernelPi a t ∘ₘ ρ‖N(0, I)).toReal = e^{-2at} KL(ρ‖N(0, I)).toReal
= e^{-2at} ∑ᵢ mᵢ² / 2`. -/
theorem toReal_klDiv_ouKernelPi_comp_gaussian {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (m : Fin d → ℝ) :
    (klDiv (ouKernelPi a t ∘ₘ (Measure.pi fun i => gaussianReal (m i) 1))
        (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal
        = Real.exp (-2 * a * t) * (klDiv (Measure.pi fun i => gaussianReal (m i) 1)
          (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal ∧
      (klDiv (ouKernelPi a t ∘ₘ (Measure.pi fun i => gaussianReal (m i) 1))
          (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal
        = Real.exp (-2 * a * t) * ((∑ i, m i ^ 2) / 2) := by
  have h := toReal_klDiv_ouKernelVarPi_comp_gaussian (d := d) one_pos ha ht m
  rw [Real.toNNReal_one, mul_one] at h
  rwa [ouKernelPi_eq_ouKernelVarPi]

/-! ### Total variation (Pinsker) -/

/-- **TV form (general variance).** Under the hypotheses of
`toReal_klDiv_ouKernelVarPi_comp_le`:
`tvSup (ouKernelVarPi v a t ∘ₘ ρ) N(0, v I) ≤ √(e^{-2at} KL(ρ‖N(0, v I)).toReal / 2)`. -/
theorem tvSup_ouKernelVarPi_comp_le {v a t : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ≠ ∞)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    TotalVariation.tvSup (ouKernelVarPi v a t ∘ₘ ρ)
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)
      ≤ √(Real.exp (-2 * a * t) *
          (klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal / 2) := by
  obtain ⟨hfin, hle⟩ := toReal_klDiv_ouKernelVarPi_comp_le hv ha ht ρ hKL hmom
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans ?_
  gcongr

/-- **TV form (standard OU).** Under the hypotheses of `toReal_klDiv_ouKernelPi_comp_le`:
`tvSup (ouKernelPi a t ∘ₘ ρ) N(0, I) ≤ √(e^{-2at} KL(ρ‖N(0, I)).toReal / 2)`. -/
theorem tvSup_ouKernelPi_comp_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (hKL : klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≠ ∞)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    TotalVariation.tvSup (ouKernelPi a t ∘ₘ ρ) (Measure.pi fun _ : Fin d => gaussianReal 0 1)
      ≤ √(Real.exp (-2 * a * t) *
          (klDiv ρ (Measure.pi fun _ : Fin d => gaussianReal 0 1)).toReal / 2) := by
  obtain ⟨hfin, hle⟩ := toReal_klDiv_ouKernelPi_comp_le ha ht ρ hKL hmom
  refine (Pinsker.tvSup_le_sqrt_klDiv hfin).trans ?_
  gcongr

end FormalizeSampling.OULangevinDecayPi
