module

public import FormalizeSampling.Foundations.HeatFlowDeBruijn
public import FormalizeSampling.Foundations.GaussianKL
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The isotropic heat kernel on `Fin d → ℝ`

Status: **Verified** (no hypotheses beyond positivity of the variance where a density is used).

The `d`-dimensional heat kernel with variance `t : ℝ≥0` is the isotropic Gaussian kernel
`heatKernelPi t x = N(x, t I) = ⊗ᵢ N(x i, t)` on `Fin d → ℝ` (a `Measure.pi` of Mathlib's
`gaussianReal`, which takes the **variance**). For `t > 0` it has the Lebesgue density
`y ↦ heatDensityPi t (y - x)`, where `heatDensityPi t z = ∏ᵢ heatDensity t (z i)` is the product
of the one-dimensional heat kernels of `Foundations/HeatFlowDeBruijn.lean`.

## Main results

* `heatKernelPi`, `heatKernelPi_apply`: the kernel `x ↦ ⊗ᵢ N(x i, t)` (the Euler–Maruyama
  kernel of `Samplers/GaussianIncrementPi.lean` is built from it).
* `isMarkovKernel_heatKernelPi`, `measurable_heatKernelPi`: it is a Markov kernel.
* `heatKernelPi_zero`: `heatKernelPi 0 = Kernel.id`.
* `bind_heatKernelPi`, `heatKernelPi_comp_heatKernelPi`: the semigroup law
  `heatKernelPi s ∘ₖ heatKernelPi t = heatKernelPi (s + t)` (coordinatewise from the 1D law
  `OU.bind_heat`).
* `heatDensityPi`, `heatDensityPi_eq_exp`: the product density and its closed form
  `(2π t)^{-d/2} exp(-∑ᵢ zᵢ² / (2t))`.
* `heatKernelPi_eq_withDensity`: for `t > 0`,
  `heatKernelPi t x = volume.withDensity (y ↦ ofReal (heatDensityPi t (y - x)))`.
* `heatKL`, `heatKL_zero`, `heatKL_le_klDiv`: `heatKL ρ π t = KL(ρ_t‖π_t).toReal` with
  `ρ_t = heatKernelPi t ∘ₘ ρ` (`t` the added variance, truncated at `0`), `heatKL ρ π 0 =
  KL(ρ‖π).toReal`, and data processing `heatKL ρ π t ≤ KL(ρ‖π).toReal` when `KL(ρ‖π) < ∞`.

## Not proved here

* That the `d = 1` objects agree with the one-dimensional `OU.heatKernel` (they are related
  only through the coordinatewise construction).
* Non-isotropic Gaussian kernels.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal

namespace FormalizeSampling.HeatKernelPi

open FormalizeSampling.MeasureHelpers (pi_dirac lintegral_pi_prod pi_withDensity_ofReal)

open FormalizeSampling.HeatFlowDeBruijn (heatDensity heatDensity_pos heatDensity_le
  continuous_heatDensity gaussianPDFReal_eq_heatDensity)

variable {d : ℕ}

/-! ### The kernel -/

/-- The **isotropic heat kernel** on `Fin d → ℝ` with variance `t : ℝ≥0`:
`heatKernelPi t x = ⊗ᵢ N(x i, t) = N(x, t I)`, the law of `x + √t Z` with `Z ∼ N(0, I)`. -/
noncomputable def heatKernelPi (t : ℝ≥0) : Kernel (Fin d → ℝ) (Fin d → ℝ) where
  toFun x := Measure.pi fun i => gaussianReal (x i) t
  measurable' := by
    have e : (fun x : Fin d → ℝ => Measure.pi fun i => gaussianReal (x i) t) =
        fun x => (Measure.pi fun _ : Fin d => gaussianReal 0 t).map (fun y i => y i + x i) :=
      funext fun x => GaussianIncrement.pi_gaussianReal_eq_map x t
    rw [e]
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hg : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => fun i => p.2 i + p.1 i := by
      fun_prop
    have := measurable_measure_prodMk_left
      (ν := Measure.pi fun _ : Fin d => gaussianReal 0 t) (hg hs)
    convert this using 1
    funext x
    rw [Measure.map_apply (by fun_prop) hs]
    rfl

/-- Evaluation of the heat kernel: `heatKernelPi t x = ⊗ᵢ N(x i, t)`. -/
theorem heatKernelPi_apply (t : ℝ≥0) (x : Fin d → ℝ) :
    heatKernelPi t x = Measure.pi fun i => gaussianReal (x i) t := rfl

/-- `heatKernelPi t` is a Markov kernel (a product of Gaussian probability measures). -/
instance isMarkovKernel_heatKernelPi (t : ℝ≥0) : IsMarkovKernel (heatKernelPi (d := d) t) :=
  ⟨fun x => by rw [heatKernelPi_apply]; infer_instance⟩

/-- `x ↦ heatKernelPi t x` is measurable (as a map into measures). -/
theorem measurable_heatKernelPi (t : ℝ≥0) : Measurable (heatKernelPi (d := d) t) :=
  (heatKernelPi t).measurable

/-- At variance `0` the heat kernel is the identity kernel: `heatKernelPi 0 = Kernel.id`. -/
theorem heatKernelPi_zero : heatKernelPi (d := d) 0 = Kernel.id := by
  ext1 x
  rw [heatKernelPi_apply, Kernel.id_apply]
  simp_rw [gaussianReal_zero_var]
  exact pi_dirac x

/-! ### Products of finitely many one-dimensional integrals -/

/-! ### The semigroup law -/

/-- **Heat semigroup law, pointwise form.** For variances `s t : ℝ≥0` and `x : Fin d → ℝ`,
`(heatKernelPi t x).bind (heatKernelPi s) = heatKernelPi (s + t) x`, i.e.
`N(x, t I) * N(0, s I) = N(x, (s + t) I)`. -/
theorem bind_heatKernelPi (s t : ℝ≥0) (x : Fin d → ℝ) :
    (heatKernelPi t x).bind (heatKernelPi s) = heatKernelPi (s + t) x := by
  rw [heatKernelPi_apply (s + t)]
  refine (Measure.pi_eq fun S hS => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hS)
    (measurable_heatKernelPi s).aemeasurable]
  simp_rw [heatKernelPi_apply s, Measure.pi_pi]
  rw [heatKernelPi_apply t, lintegral_pi_prod _ (fun i u => gaussianReal u s (S i))
    (fun i => (OU.heatKernel s).measurable_coe (hS i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := OU.bind_heat t s (x i)
  rw [add_comm t s] at h
  rw [← h, Measure.bind_apply (f := fun y => gaussianReal y s) (hS i)
    (OU.heatKernel s).measurable.aemeasurable]

/-- **Heat semigroup law, kernel form**:
`heatKernelPi s ∘ₖ heatKernelPi t = heatKernelPi (s + t)` for variances `s t : ℝ≥0`. -/
theorem heatKernelPi_comp_heatKernelPi (s t : ℝ≥0) :
    heatKernelPi s ∘ₖ heatKernelPi t = heatKernelPi (d := d) (s + t) := by
  ext1 x
  rw [Kernel.comp_apply, bind_heatKernelPi]

/-! ### The product density -/

/-- The isotropic Gaussian density with variance `t` on `Fin d → ℝ`:
`heatDensityPi t z = ∏ᵢ heatDensity t (z i) = (2π t)^{-d/2} exp(-∑ᵢ zᵢ² / (2t))`
(`heatDensityPi_eq_exp`). Only meaningful for `t > 0`. -/
noncomputable def heatDensityPi (t : ℝ) (z : Fin d → ℝ) : ℝ := ∏ i, heatDensity t (z i)

/-- Closed form of the product density:
`heatDensityPi t z = (√(2π t))⁻¹ ^ d · exp(-(∑ᵢ zᵢ²) / (2t))` (no assumptions). -/
theorem heatDensityPi_eq_exp (t : ℝ) (z : Fin d → ℝ) :
    heatDensityPi t z =
      (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d * Real.exp (-(∑ i, z i ^ 2) / (2 * t)) := by
  unfold heatDensityPi heatDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  simp_rw [neg_div]

/-- The product density is positive for `t > 0`. -/
theorem heatDensityPi_pos {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) : 0 < heatDensityPi t z :=
  Finset.prod_pos fun _ _ => heatDensity_pos ht _

/-- Uniform bound: `heatDensityPi t z ≤ (√(2π t))⁻¹ ^ d` for `t > 0`. -/
theorem heatDensityPi_le {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) :
    heatDensityPi t z ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d := by
  unfold heatDensityPi
  calc ∏ i, heatDensity t (z i) ≤ ∏ _i : Fin d, (Real.sqrt (2 * Real.pi * t))⁻¹ := ?_
    _ = _ := by simp
  gcongr with i
  · exact fun i _ => (heatDensity_pos ht _).le
  · exact heatDensity_le ht _

/-- `z ↦ heatDensityPi t z` is continuous (every `t`). -/
theorem continuous_heatDensityPi (t : ℝ) : Continuous (heatDensityPi (d := d) t) := by
  unfold heatDensityPi
  exact continuous_finsetProd _ fun i _ => (continuous_heatDensity t).comp (continuous_apply i)

/-- **Density of the heat kernel.** For `t > 0` and `x : Fin d → ℝ`,
`heatKernelPi t x = volume.withDensity (y ↦ ofReal (heatDensityPi t (y - x)))`. -/
theorem heatKernelPi_eq_withDensity {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    heatKernelPi t.toNNReal x =
      volume.withDensity fun y => ENNReal.ofReal (heatDensityPi t (y - x)) := by
  have ht' : t.toNNReal ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact ht
  rw [heatKernelPi_apply]
  simp_rw [gaussianReal_of_var_ne_zero _ ht', gaussianPDF_def]
  rw [pi_withDensity_ofReal (fun i => integrable_gaussianPDFReal _ _)
    (fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  simp_rw [gaussianPDFReal_eq_heatDensity ht]
  rfl

/-! ### KL along the heat flow -/

/-- KL along the heat flow on `Fin d → ℝ`: `heatKL ρ π t = KL(ρ_t‖π_t).toReal` with
`ρ_t = heatKernelPi t ∘ₘ ρ = ρ * N(0, t I)` and `π_t = heatKernelPi t ∘ₘ π` (`t` is the added
**variance**; negative `t` is truncated to `0`). -/
noncomputable def heatKL (ρ π : Measure (Fin d → ℝ)) (t : ℝ) : ℝ :=
  (klDiv (heatKernelPi t.toNNReal ∘ₘ ρ) (heatKernelPi t.toNNReal ∘ₘ π)).toReal

/-- At time `0` the heat-flow KL is the KL of the initial laws:
`heatKL ρ π 0 = KL(ρ‖π).toReal` (no assumptions). -/
theorem heatKL_zero (ρ π : Measure (Fin d → ℝ)) : heatKL ρ π 0 = (klDiv ρ π).toReal := by
  simp [heatKL, heatKernelPi_zero, Measure.id_comp]

/-- **Data processing along the heat flow.** For probability measures `ρ, π` on `Fin d → ℝ` with
`KL(ρ‖π) < ∞` and every `t`, `heatKL ρ π t ≤ KL(ρ‖π).toReal`. -/
theorem heatKL_le_klDiv (ρ π : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] (hKL : klDiv ρ π ≠ ⊤) (t : ℝ) :
    heatKL ρ π t ≤ (klDiv ρ π).toReal :=
  ENNReal.toReal_mono hKL (klDiv_comp_right_le _ _ _)

/-- Data processing in `heatKL` form: `heatKL ρ π t ≤ heatKL ρ π 0` when `KL(ρ‖π) < ∞`. -/
theorem heatKL_le_heatKL_zero (ρ π : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] (hKL : klDiv ρ π ≠ ⊤) (t : ℝ) : heatKL ρ π t ≤ heatKL ρ π 0 := by
  rw [heatKL_zero]; exact heatKL_le_klDiv ρ π hKL t

/-- Semigroup shift of the heat-flow KL: for finite `ρ₀, π₀` and `σ, t ≥ 0`,
`heatKL (heatKernelPi σ ∘ₘ ρ₀) (heatKernelPi σ ∘ₘ π₀) t = heatKL ρ₀ π₀ (σ + t)`. -/
theorem heatKL_heatKernelPi_comp (ρ₀ π₀ : Measure (Fin d → ℝ)) {σ t : ℝ} (hσ : 0 ≤ σ)
    (ht : 0 ≤ t) :
    heatKL (heatKernelPi σ.toNNReal ∘ₘ ρ₀) (heatKernelPi σ.toNNReal ∘ₘ π₀) t =
      heatKL ρ₀ π₀ (σ + t) := by
  simp only [heatKL]
  rw [Measure.comp_assoc, Measure.comp_assoc, heatKernelPi_comp_heatKernelPi,
    Real.toNNReal_add hσ ht, add_comm]

end FormalizeSampling.HeatKernelPi
