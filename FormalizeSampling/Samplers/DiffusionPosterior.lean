module

public import FormalizeSampling.Samplers.DiffusionSetup

/-!
# Diffusion models: the exact reverse kernel in Bayes form and Tweedie's formula

For the forward OU chain of `Samplers/DiffusionSetup.lean` (data law `μ`, time grid `t`), this
file identifies the exact reverse kernel `R_{k+1} = F_{k+1}†p_k` (Mathlib's posterior, defined by
disintegration) with the explicit Bayes kernel, computes its mean, and proves Tweedie's formula
for it.

## Main results

* `ae_integrable_revKernel`: if `μ` has a finite second moment then for every `k`, for
  `p_{k+1}`-a.e. `y`, every coordinate is integrable under `R_{k+1} y` (so the posterior mean
  `m*_{k+1}(y)` is a genuine mean). No density and no time-grid assumption.
* `revKernel_ae_eq_bayes`: if `t_k < t_{k+1}`, then for `p_{k+1}`-a.e. `y`,
  `R_{k+1} y = p_k.withDensity (x ↦ φ(x, y) / ∫ φ(x', y) dp_k(x'))` with the Gaussian
  transition density `φ = fwdTransDensity t (k+1)`.
* `postMean_ae_eq_piAffinePosteriorMean`: for `p_{k+1}`-a.e. `y`, `m*_{k+1}(y)` is the explicit
  Bayes ratio `OUPosterior.piAffinePosteriorMean p_k α_{k+1} √β_{k+1} y`.
* **Tweedie's formula** `postMean_ae_eq_tweedie`: if `t_k < t_{k+1}`, then for
  `p_{k+1}`-a.e. `y`,
  `m*_{k+1}(y) = α_{k+1}⁻¹ (y + β_{k+1} ∇ log p_{k+1}(y))`, where `p_{k+1}(y)` is the Lebesgue
  density `fwdDensity μ t (k+1)` of the marginal (`fwdLaw_eq_withDensity`) and `∇ log` is the
  state score `FormalizeSampling.score`; equivalently
  `postMean μ t (k+1) =ᵐ scoreMean t (fun j => score (fwdDensity μ t j)) (k+1)`.

## Not proved here

* Uniqueness: the posterior is only determined `p_{k+1}`-a.e., so every statement is a.e.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace FormalizeSampling.Diffusion

open FormalizeSampling.ReverseKernel

variable {d : ℕ}

/-! ### Integrability of the posterior -/

/-- **The posterior has integrable coordinates almost surely.** If the data law `μ` has a finite
second moment, then for every `k` and `p_{k+1}`-almost every `y`, `x ↦ xᵢ` is integrable under
the exact reverse kernel `R_{k+1} y`, for every coordinate `i`. -/
theorem ae_integrable_revKernel (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (t : ℕ → ℝ) (k : ℕ) :
    ∀ᵐ y ∂(fwdLaw μ t (k + 1)), ∀ i, Integrable (fun x => x i) (revKernel μ t (k + 1) y) := by
  rw [ae_all_iff]
  intro i
  have hf : Measurable fun x : Fin d → ℝ => ‖x i‖ₑ := (measurable_pi_apply i).enorm
  have hbind : ∫⁻ y, ∫⁻ x, ‖x i‖ₑ ∂(revKernel μ t (k + 1) y) ∂(fwdLaw μ t (k + 1)) ≠ ∞ := by
    rw [← Measure.lintegral_bind (revKernel μ t (k + 1)).aemeasurable hf.aemeasurable]
    rw [revKernel_comp_fwdLaw]
    exact (integrable_apply_fwdLaw μ hμ t k i).hasFiniteIntegral.ne
  filter_upwards [ae_lt_top (hf.lintegral_kernel) hbind] with y hy
  exact ⟨(measurable_pi_apply i).aestronglyMeasurable, hy⟩

/-! ### Bayes form of the exact reverse kernel -/

/-- The Gaussian transition density of step `k + 1` as an `ℝ≥0∞`-valued kernel density. -/
noncomputable def fwdTransDensityE (t : ℕ → ℝ) (k : ℕ) (x y : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fwdTransDensity t (k + 1) x y)

/-- The `ℝ≥0∞`-valued transition density is jointly measurable. -/
theorem measurable_fwdTransDensityE (t : ℕ → ℝ) (k : ℕ) :
    Measurable (Function.uncurry (fwdTransDensityE (d := d) t k)) :=
  ENNReal.measurable_ofReal.comp (continuous_fwdTransDensity t (k + 1)).measurable

/-- The density `fwdDensity μ t (k + 1)` of `p_{k+1}` is positive everywhere if
`t_k < t_{k+1}`. -/
theorem fwdDensity_pos (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ} {k : ℕ}
    (hk : t k < t (k + 1)) (y : Fin d → ℝ) : 0 < fwdDensity μ t (k + 1) y := by
  have hk' : t (k + 1 - 1) < t (k + 1) := by rwa [Nat.add_sub_cancel]
  change 0 < ∫ x, fwdTransDensity t (k + 1) x y ∂(fwdLaw μ t (k + 1 - 1))
  rw [Nat.add_sub_cancel, integral_pos_iff_support_of_nonneg
    (fun x => fwdTransDensity_nonneg t (k + 1) x y) (integrable_fwdTransDensity _ t (k + 1) y)]
  have : Function.support (fun x => fwdTransDensity t (k + 1) x y) = Set.univ :=
    Set.eq_univ_of_forall fun x => (fwdTransDensity_pos hk' x y).ne'
  rw [this, measure_univ]
  exact one_pos

/-- **The exact reverse kernel in Bayes form.** If `t_k < t_{k+1}`, then for `p_{k+1}`-a.e. `y`,
`R_{k+1} y = p_k.withDensity (reverseDensity p_k 1 φ y)` with
`reverseDensity p_k 1 φ y x = φ(x, y) / ∫⁻ φ(x', y) dp_k(x')` and `φ` the Gaussian transition
density of step `k + 1`. -/
theorem revKernel_ae_eq_bayes (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ}
    {k : ℕ} (hk : t k < t (k + 1)) :
    densityKernel (fwdLaw μ t k) (reverseDensity (fwdLaw μ t k) 1 (fwdTransDensityE t k))
      =ᵐ[fwdLaw μ t (k + 1)] revKernel μ t (k + 1) := by
  have hk' : t (k + 1 - 1) < t (k + 1) := by rwa [Nat.add_sub_cancel]
  have hF : fwdKernel (d := d) t (k + 1) = densityKernel volume (fwdTransDensityE t k) :=
    fwdKernel_eq_densityKernel hk'
  have key : ∀ (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsMarkovKernel κ],
      κ = densityKernel volume (fwdTransDensityE t k) →
      densityKernel (fwdLaw μ t k) (reverseDensity (fwdLaw μ t k) 1 (fwdTransDensityE t k))
        =ᵐ[κ ∘ₘ fwdLaw μ t k] κ†(fwdLaw μ t k) := by
    intro κ _ hκ
    subst hκ
    have : IsFiniteMeasure ((fwdLaw μ t k).withDensity 1) := by
      rw [withDensity_one]; infer_instance
    have h := densityKernel_reverseDensity_ae_eq_posterior (ν := fwdLaw μ t k) (ρ := volume)
      (p := 1) measurable_const (measurable_fwdTransDensityE t k)
    rw [posterior_congr_measure _ withDensity_one, withDensity_one] at h
    exact h
  exact key _ hF

/-- **The posterior mean is the explicit Bayes ratio.** If `t_k < t_{k+1}`, then for
`p_{k+1}`-a.e. `y`, `m*_{k+1}(y) = piAffinePosteriorMean p_k α_{k+1} √β_{k+1} y`, i.e.
coordinatewise `(∫ xᵢ φ(x, y) dp_k(x)) / ∫ φ(x, y) dp_k(x)`. -/
theorem postMean_ae_eq_piAffinePosteriorMean (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} {k : ℕ} (hk : t k < t (k + 1)) :
    ∀ᵐ y ∂(fwdLaw μ t (k + 1)), postMean μ t (k + 1) y =
      OUPosterior.piAffinePosteriorMean (fwdLaw μ t k) (fwdScale t (k + 1))
        (Real.sqrt (fwdVar t (k + 1))) y := by
  filter_upwards [revKernel_ae_eq_bayes μ hk] with y hy
  funext i
  have hZ := fwdDensity_pos μ hk y
  have hmeas2 : Measurable (Function.uncurry
      (reverseDensity (fwdLaw μ t k) 1 (fwdTransDensityE t k))) :=
    measurable_reverseDensity (p := 1) measurable_const (measurable_fwdTransDensityE t k)
  have hmeas : Measurable (reverseDensity (fwdLaw μ t k) 1 (fwdTransDensityE t k) y) :=
    hmeas2.of_uncurry_left
  have hm : marginalDensity (fwdLaw μ t k) 1 (fwdTransDensityE t k) y =
      ENNReal.ofReal (fwdDensity μ t (k + 1) y) := marginalDensity_eq_fwdDensity μ t k y
  have hr : ∀ x, reverseDensity (fwdLaw μ t k) 1 (fwdTransDensityE t k) y x =
      ENNReal.ofReal (fwdTransDensity t (k + 1) x y / fwdDensity μ t (k + 1) y) := fun x => by
    rw [reverseDensity, hm, Pi.one_apply, one_mul, fwdTransDensityE,
      ENNReal.ofReal_div_of_pos hZ]
  rw [postMean, meanPi, ← hy, densityKernel_apply hmeas2,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun x => by rw [hr]; exact ENNReal.ofReal_lt_top)]
  simp_rw [hr, ENNReal.toReal_ofReal (div_nonneg (fwdTransDensity_nonneg t (k + 1) _ y) hZ.le),
    smul_eq_mul]
  rw [OUPosterior.piAffinePosteriorMean]
  have hden : OUPosterior.piAffineDensity (fwdLaw μ t k) (fwdScale t (k + 1))
      (Real.sqrt (fwdVar t (k + 1))) y = fwdDensity μ t (k + 1) y := by
    rw [fwdDensity, Nat.add_sub_cancel]
  rw [hden, ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [fwdTransDensity]
  ring

/-- **Tweedie's formula for the exact reverse kernel.** If `t_k < t_{k+1}`, then for
`p_{k+1}`-a.e. `y`, the posterior mean `m*_{k+1}(y) = E[x_k | x_{k+1} = y]` satisfies
`m*_{k+1}(y)ᵢ = α_{k+1}⁻¹ (yᵢ + β_{k+1} ∂ᵢ log p_{k+1}(y))`, where `p_{k+1} = fwdDensity μ t (k+1)`
is the Lebesgue density of the marginal (`fwdLaw_eq_withDensity`). In the notation of
`scoreMean`: `m*_{k+1} = scoreMean t (fun j => score (fwdDensity μ t j)) (k + 1)` a.e. No
density or moment assumption on the data law `μ`. -/
theorem postMean_ae_eq_tweedie (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} {k : ℕ} (hk : t k < t (k + 1)) :
    ∀ᵐ y ∂(fwdLaw μ t (k + 1)),
      postMean μ t (k + 1) y = scoreMean t (fun j => score (fwdDensity μ t j)) (k + 1) y := by
  have hk' : t (k + 1 - 1) < t (k + 1) := by rwa [Nat.add_sub_cancel]
  have hβ := fwdVar_pos hk'
  have hα := fwdScale_pos t (k + 1)
  have hσ : Real.sqrt (fwdVar t (k + 1)) ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  filter_upwards [postMean_ae_eq_piAffinePosteriorMean μ hk] with y hy
  have hs := OUPosterior.score_piAffineDensity (fwdLaw μ t k) (fwdScale t (k + 1)) hσ y
  have hden : fwdDensity μ t (k + 1) = OUPosterior.piAffineDensity (fwdLaw μ t k)
      (fwdScale t (k + 1)) (Real.sqrt (fwdVar t (k + 1))) := by
    funext z; rw [fwdDensity, Nat.add_sub_cancel]
  funext i
  rw [hy, scoreMean, hden, hs, Real.sq_sqrt hβ.le]
  field_simp
  ring

end FormalizeSampling.Diffusion
