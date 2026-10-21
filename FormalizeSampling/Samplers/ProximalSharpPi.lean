module

public import Mathlib.Probability.Independence.Integration
public import FormalizeSampling.Samplers.ProximalPi
public import FormalizeSampling.Samplers.ProximalSharp
public import FormalizeSampling.Foundations.GibbsMeasure
public import FormalizeSampling.Foundations.BakryEmeryGeneralPi

/-!
# Tightness of the sharp proximal rate on `Fin d → ℝ`: separable and Gaussian targets

Status: **Verified** (no named hypotheses).

`d`-dimensional counterpart of Part 2 of `Samplers/ProximalSharp.lean`. We first show that the
exact proximal sampler of `Samplers/ProximalPi.lean` **tensorises** over separable potentials
`f(x) = ∑ᵢ gᵢ(xᵢ)` (`sepPotential g`): the target, the RGO kernel and the proximal kernel are
the products of the one-dimensional objects of `Samplers/Proximal.lean`. Specialising to the
isotropic Gaussian potential `f_α(x) = α |x|² / 2 = ∑ᵢ α xᵢ² / 2` (`gaussPotentialPi`; `|·|`
the Euclidean norm, written as a coordinate sum), the one-dimensional Gaussian computations of
`ProximalSharp` give the exact rate `(1 + α η)^{-2}` in every dimension `d ≥ 1`.

## Main results

* General tool: `bind_pi_eq_pi_bind` (a product kernel applied to a product law is the product
  of the one-dimensional outputs).
* Separable potentials (`hg : ∀ i, Measurable (g i)`, `hint : ∀ i, Integrable (exp ∘ (-gᵢ))`,
  `η > 0`; `sepPotential`, `targetPi_sepPotential` (`π = ⊗ᵢ target gᵢ`) and
  `withDensity_prod_ofReal` are in `Foundations/GibbsMeasure.lean`):
  `rgoKernelPi_sepPotential_apply`
  (`RGO(y) = ⊗ᵢ RGOᵢ(yᵢ)`), `proxKernelPi_sepPotential_apply`,
  `proxKernelPi_sepPotential_comp_pi` (one proximal step of a product law is the product of
  the one-dimensional proximal steps).
* Gaussian target (`α, η > 0`; `π = N(0, I/α)` is `targetPi_gaussPotentialPi` in
  `Foundations/GibbsMeasure.lean`): `rgoKernelPi_gaussPotentialPi_apply`
  (`RGO(y) = N(y/(1 + αη), η/(1 + αη) I)`), `proxKernelPi_comp_pi_gaussianReal_invVar`
  (`N(m, I/α) ↦ N(m/(1 + αη), I/α)`), `klDiv_pi_gaussTarget` (`KL(N(m, I/α)‖π) = α|m|²/2`),
  `klDiv_proxKernelPi_comp_gaussTarget` (exact factor `(1 + αη)^{-2}`),
  `klDiv_iteratePi_gaussTarget` (`k` steps, `(1 + αη)^{-2k}` exactly), `not_exists_rate_lt_pi`
  (for `d ≥ 1` no per-step constant `< (1 + αη)^{-2}` holds for this LSI(`α`) target) and
  `toReal_klDiv_proxKernelPi_comp_gaussTarget_lt` (the forward-only rate is strict).

## Not proved here

* Nothing on the LSI of the target here: that `N(0, I/α)` satisfies LSI(`α`) is proved as
  `GaussianFunctionalLSIPi.functionalLSIPi_gaussian` (functional form) and, for positive
  differentiable densities with finite second moment and Fisher information, in KL form as
  `GaussianLSIZeroPi.klDiv_le_fisher0` (here the rate is computed directly).
* Exact rate computations for non-isotropic Gaussian targets. For non-separable potentials the
  sharp rate is proved elsewhere: strongly log-concave targets in
  `Samplers/ProximalStronglyLogConcaveGeneralPi.lean`, LSI targets with a Gaussian upper
  envelope in `Samplers/ProximalGeneralLSIPi.lean`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.ProximalPi FormalizeSampling.ReverseKernel
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalSharpPi

variable {d : ℕ}

/-! ### Product kernels -/

/-- **A product kernel applied to a product law.** For Markov kernels `κ i : Kernel ℝ ℝ`, a
kernel `K` on `Fin d → ℝ` with `K x = ⊗ᵢ κ i (x i)` for every `x`, and probability measures
`μ i` on `ℝ`: `K ∘ₘ (⊗ᵢ μ i) = ⊗ᵢ (κ i ∘ₘ μ i)`. (Coordinates of `⊗ᵢ μ i` are independent.) -/
theorem bind_pi_eq_pi_bind {κ : Fin d → Kernel ℝ ℝ} [∀ i, IsMarkovKernel (κ i)]
    {K : Kernel (Fin d → ℝ) (Fin d → ℝ)} (hK : ∀ x, K x = Measure.pi fun i => κ i (x i))
    (μ : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    K ∘ₘ Measure.pi μ = Measure.pi fun i => κ i ∘ₘ μ i := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) K.aemeasurable]
  simp_rw [hK, Measure.pi_pi]
  have hm : ∀ i, Measurable fun t => κ i t (s i) := fun i => (κ i).measurable_coe (hs i)
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : Fin d → ℝ) => κ i (x i) (s i))
    (iIndepFun_pi (X := fun i t => κ i t (s i)) fun i => (hm i).aemeasurable)
    (fun i => (hm i).comp (measurable_pi_apply i))).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.bind_apply (hs i) (κ i).aemeasurable]
  exact (measurePreserving_eval μ i).lintegral_comp (hm i)

/-! ### Separable potentials -/

variable {g : Fin d → ℝ → ℝ} {η : ℝ}

/-- The RGO integrand of a separable potential factorises:
`exp(-∑ᵢ gᵢ(xᵢ) - |x - y|²/(2η)) = ∏ᵢ exp(-gᵢ(xᵢ) - (xᵢ - yᵢ)²/(2η))`. -/
theorem exp_rgo_sepPotential (g : Fin d → ℝ → ℝ) (η : ℝ) (y x : Fin d → ℝ) :
    Real.exp (-sepPotential g x - sqDist x y / (2 * η))
      = ∏ i, Real.exp (-g i (x i) - (x i - y i) ^ 2 / (2 * η)) := by
  rw [← Real.exp_sum, sepPotential, sqDist, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_div]

/-- **The RGO of a separable potential is a product.** For measurable `gᵢ` with integrable
`exp ∘ (-gᵢ)` and `η > 0`: `rgoKernelPi (sepPotential g) η y = ⊗ᵢ rgoKernel (g i) η (y i)`. -/
theorem rgoKernelPi_sepPotential_apply (hg : ∀ i, Measurable (g i))
    (hint : ∀ i, Integrable (fun t => Real.exp (-g i t))) (hη : 0 < η) (y : Fin d → ℝ) :
    rgoKernelPi (sepPotential g) η y = Measure.pi fun i => Proximal.rgoKernel (g i) η (y i) := by
  have hd : ∀ x, rgoDensityPi (sepPotential g) η y x
      = ∏ i, Proximal.rgoDensity (g i) η (y i) (x i) := by
    intro x
    rw [rgoDensityPi, rgoNormalizerPi]
    simp_rw [exp_rgo_sepPotential]
    exact prod_div_integral_prod (fun i t => Real.exp (-g i t - (t - y i) ^ 2 / (2 * η))) x
  rw [rgoKernelPi_apply (measurable_sepPotential hg) (integrable_exp_neg_sepPotential hint) hη]
  simp_rw [hd]
  rw [withDensity_prod_ofReal (fun i t => Proximal.rgoDensity (g i) η (y i) t)
    (fun i => (Proximal.integrable_rgo (hint i) hη (y i)).div_const _)
    (fun i t => Proximal.rgoDensity_nonneg _ _)]
  congr 1
  funext i
  rw [Proximal.rgoKernel_apply (hg i) (hint i) hη]

/-- **The proximal kernel of a separable potential is a product.** For measurable `gᵢ` with
integrable `exp ∘ (-gᵢ)` and `η > 0`:
`proxKernelPi (sepPotential g) η x = ⊗ᵢ proxKernel (g i) η (x i)`. -/
theorem proxKernelPi_sepPotential_apply (hg : ∀ i, Measurable (g i))
    (hint : ∀ i, Integrable (fun t => Real.exp (-g i t))) (hη : 0 < η) (x : Fin d → ℝ) :
    proxKernelPi (sepPotential g) η x = Measure.pi fun i => Proximal.proxKernel (g i) η (x i) := by
  have : ∀ i, IsMarkovKernel (Proximal.rgoKernel (g i) η) :=
    fun i => Proximal.isMarkovKernel_rgoKernel (hg i) (hint i) hη
  rw [proxKernelPi, Kernel.comp_apply, forwardKernelPi_apply]
  change rgoKernelPi (sepPotential g) η ∘ₘ _ = _
  rw [bind_pi_eq_pi_bind (rgoKernelPi_sepPotential_apply hg hint hη)]
  congr 1
  funext i
  rw [Proximal.proxKernel, Kernel.comp_apply, Proximal.forwardKernel_apply hη]

/-- **One proximal step of a product law, separable potential.** For measurable `gᵢ` with
integrable `exp ∘ (-gᵢ)`, `η > 0` and probability measures `μ i` on `ℝ`:
`proxKernelPi (sepPotential g) η ∘ₘ (⊗ᵢ μ i) = ⊗ᵢ (proxKernel (g i) η ∘ₘ μ i)`. -/
theorem proxKernelPi_sepPotential_comp_pi (hg : ∀ i, Measurable (g i))
    (hint : ∀ i, Integrable (fun t => Real.exp (-g i t))) (hη : 0 < η)
    (μ : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    proxKernelPi (sepPotential g) η ∘ₘ Measure.pi μ
      = Measure.pi fun i => Proximal.proxKernel (g i) η ∘ₘ μ i := by
  have : ∀ i, IsMarkovKernel (Proximal.rgoKernel (g i) η) :=
    fun i => Proximal.isMarkovKernel_rgoKernel (hg i) (hint i) hη
  have := Proximal.isMarkovKernel_forwardKernel hη
  have : ∀ i, IsMarkovKernel (Proximal.proxKernel (g i) η) := fun i => by
    unfold Proximal.proxKernel
    infer_instance
  exact bind_pi_eq_pi_bind (proxKernelPi_sepPotential_apply hg hint hη) μ

/-! ### The isotropic Gaussian target -/

open FormalizeSampling.ProximalSharp

/-- **Explicit RGO for the isotropic Gaussian.** For `α, η > 0`:
`rgoKernelPi f_α η y = N(y/(1 + αη), η/(1 + αη) I)`, i.e.
`Measure.pi fun i => gaussianReal (y i / (1 + αη)) (η / (1 + αη)).toNNReal`. -/
theorem rgoKernelPi_gaussPotentialPi_apply {α : ℝ} (hα : 0 < α) (hη : 0 < η) (y : Fin d → ℝ) :
    rgoKernelPi (gaussPotentialPi α) η y
      = Measure.pi fun i => gaussianReal (y i / (1 + α * η)) (η / (1 + α * η)).toNNReal := by
  rw [gaussPotentialPi, rgoKernelPi_sepPotential_apply (fun _ => measurable_gaussPotential α)
    (fun _ => integrable_exp_neg_gaussPotential hα) hη]
  simp_rw [rgoKernel_gaussPotential_apply hα hη]

/-- **Exact proximal step of an isotropic Gaussian.** For `α, η > 0` and `m : Fin d → ℝ`:
`proxKernelPi f_α η ∘ₘ N(m, I/α) = N(m/(1 + αη), I/α)` (product form). -/
theorem proxKernelPi_comp_pi_gaussianReal_invVar {α : ℝ} (hα : 0 < α) (hη : 0 < η)
    (m : Fin d → ℝ) :
    proxKernelPi (gaussPotentialPi α) η ∘ₘ (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)
      = Measure.pi fun i => gaussianReal (m i / (1 + α * η)) (α⁻¹).toNNReal := by
  rw [gaussPotentialPi, proxKernelPi_sepPotential_comp_pi
    (fun _ => measurable_gaussPotential α) (fun _ => integrable_exp_neg_gaussPotential hα) hη]
  simp_rw [proxKernel_comp_gaussianReal_invVar hα hη]

/-- **KL to the isotropic Gaussian target.** For `α > 0` and `m : Fin d → ℝ`:
`KL(N(m, I/α)‖π) = α |m|²/2 = α (∑ᵢ mᵢ²)/2` with `π = targetPi f_α` (tensorisation of KL,
`GaussianIncrement.klDiv_pi_gaussianReal`). -/
theorem klDiv_pi_gaussTarget {α : ℝ} (hα : 0 < α) (m : Fin d → ℝ) :
    klDiv (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)
        (targetPi (gaussPotentialPi α))
      = ENNReal.ofReal (α * (∑ i, m i ^ 2) / 2) := by
  rw [targetPi_gaussPotentialPi hα,
    GaussianIncrement.klDiv_pi_gaussianReal m (fun _ => 0) (invVar_ne_zero hα), coe_invVar hα]
  congr 1
  simp_rw [sub_zero]
  field_simp

/-- **Tightness of the sharp rate on `Fin d → ℝ` (Verified).** For `α, η > 0`, the isotropic
Gaussian target `π = targetPi f_α = N(0, I/α)`, and `ρ = N(m, I/α)`:
`proxKernelPi f_α η ∘ₘ ρ = N(m/(1 + αη), I/α)`,
`KL(proxKernelPi f_α η ∘ₘ ρ‖π) = α |m|²/(2 (1 + αη)²)` and
`KL(proxKernelPi f_α η ∘ₘ ρ‖π) = KL(ρ‖π) / (1 + αη)²` (in `ℝ≥0∞`). -/
theorem klDiv_proxKernelPi_comp_gaussTarget {α : ℝ} (hα : 0 < α) (hη : 0 < η)
    (m : Fin d → ℝ) :
    proxKernelPi (gaussPotentialPi α) η ∘ₘ (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)
        = (Measure.pi fun i => gaussianReal (m i / (1 + α * η)) (α⁻¹).toNNReal) ∧
      klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ
          (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)) (targetPi (gaussPotentialPi α))
        = ENNReal.ofReal (α * (∑ i, m i ^ 2) / (2 * (1 + α * η) ^ 2)) ∧
      klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ
          (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)) (targetPi (gaussPotentialPi α))
        = klDiv (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)
            (targetPi (gaussPotentialPi α)) / ENNReal.ofReal ((1 + α * η) ^ 2) := by
  have hpos : 0 < 1 + α * η := by positivity
  have h1 := proxKernelPi_comp_pi_gaussianReal_invVar hα hη m
  have hS : 0 ≤ ∑ i, m i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ
      (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)) (targetPi (gaussPotentialPi α))
      = ENNReal.ofReal (α * (∑ i, m i ^ 2) / (2 * (1 + α * η) ^ 2)) := by
    rw [h1, klDiv_pi_gaussTarget hα]
    congr 1
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    field_simp
  refine ⟨h1, h2, ?_⟩
  rw [h2, klDiv_pi_gaussTarget hα, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Tightness, iterated (Verified).** For `α, η > 0`, `π = targetPi f_α = N(0, I/α)`, and
laws `ρ : ℕ → Measure (Fin d → ℝ)` with `ρ 0 = N(m, I/α)` and
`ρ (k+1) = proxKernelPi f_α η ∘ₘ ρ k`: for every `k`, `ρ k = N(m/(1 + αη)^k, I/α)` and
`KL(ρ k‖π).toReal = KL(ρ 0‖π).toReal / (1 + αη)^(2k)` exactly, matching the bound of
`ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general` with equality. -/
theorem klDiv_iteratePi_gaussTarget {α : ℝ} (hα : 0 < α) (hη : 0 < η) (m : Fin d → ℝ)
    (ρ : ℕ → Measure (Fin d → ℝ))
    (h0 : ρ 0 = Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)
    (hstep : ∀ k, ρ (k + 1) = proxKernelPi (gaussPotentialPi α) η ∘ₘ ρ k) (k : ℕ) :
    ρ k = (Measure.pi fun i => gaussianReal (m i / (1 + α * η) ^ k) (α⁻¹).toNNReal) ∧
      (klDiv (ρ k) (targetPi (gaussPotentialPi α))).toReal
        = (klDiv (ρ 0) (targetPi (gaussPotentialPi α))).toReal / (1 + α * η) ^ (2 * k) := by
  have hpos : 0 < 1 + α * η := by positivity
  have hlaw : ρ k = Measure.pi fun i => gaussianReal (m i / (1 + α * η) ^ k) (α⁻¹).toNNReal := by
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [hstep k, ih, proxKernelPi_comp_pi_gaussianReal_invVar hα hη]
      simp_rw [pow_succ, div_div]
  have hS : 0 ≤ ∑ i, m i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨hlaw, ?_⟩
  rw [hlaw, h0, klDiv_pi_gaussTarget hα, klDiv_pi_gaussTarget hα,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  simp_rw [div_pow]
  rw [← Finset.sum_div, ← pow_mul]
  field_simp
  ring

/-- **No better per-step constant on `Fin d → ℝ` (Verified).** For `d ≥ 1`, `α, η > 0` and the
isotropic Gaussian target `π = targetPi f_α = N(0, I/α)` (which satisfies LSI(`α`),
`GaussianFunctionalLSIPi.functionalLSIPi_gaussian`), there is no `c < 1/(1 + αη)²` with
`KL(proxKernelPi f_α η ∘ₘ ρ‖π).toReal ≤ c · KL(ρ‖π).toReal` for every probability law `ρ` with
`KL(ρ‖π) < ∞`. Witness: `ρ = N(𝟙, I/α)`, `KL(ρ‖π) = α d/2 > 0`. (For `d = 0` every KL vanishes
and the statement is false, hence `0 < d`.) -/
theorem not_exists_rate_lt_pi (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ¬ ∃ c < 1 / (1 + α * η) ^ 2, ∀ ρ : Measure (Fin d → ℝ), IsProbabilityMeasure ρ →
      klDiv ρ (targetPi (gaussPotentialPi α)) ≠ ∞ →
      (klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ ρ) (targetPi (gaussPotentialPi α))).toReal
        ≤ c * (klDiv ρ (targetPi (gaussPotentialPi α))).toReal := by
  rintro ⟨c, hc, h⟩
  have hpos : 0 < 1 + α * η := by positivity
  have hρ := h (Measure.pi fun _ : Fin d => gaussianReal 1 (α⁻¹).toNNReal) inferInstance
    (by rw [klDiv_pi_gaussTarget hα (fun _ => 1)]; exact ENNReal.ofReal_ne_top)
  rw [(klDiv_proxKernelPi_comp_gaussTarget hα hη (fun _ => 1)).2.1,
    klDiv_pi_gaussTarget hα (fun _ => 1)] at hρ
  have hS : (∑ _i : Fin d, (1 : ℝ) ^ 2) = d := by simp
  rw [hS, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hρ
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : 0 < α * (d : ℝ) / 2 := by positivity
  have h3 : α * (d : ℝ) / (2 * (1 + α * η) ^ 2) = 1 / (1 + α * η) ^ 2 * (α * d / 2) := by
    field_simp
  rw [h3] at hρ
  exact absurd (le_of_mul_le_mul_right hρ h2) (not_le.2 hc)

/-- **The forward-only rate is not tight on `Fin d → ℝ` (Verified).** For `α, η > 0`,
`π = N(0, I/α)` and `ρ = N(m, I/α)` with `m ≠ 0`:
`KL(proxKernelPi f_α η ∘ₘ ρ‖π).toReal < KL(ρ‖π).toReal / (1 + αη)`. -/
theorem toReal_klDiv_proxKernelPi_comp_gaussTarget_lt {α : ℝ} (hα : 0 < α) (hη : 0 < η)
    {m : Fin d → ℝ} (hm : m ≠ 0) :
    (klDiv (proxKernelPi (gaussPotentialPi α) η ∘ₘ
        (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal))
        (targetPi (gaussPotentialPi α))).toReal
      < (klDiv (Measure.pi fun i => gaussianReal (m i) (α⁻¹).toNNReal)
          (targetPi (gaussPotentialPi α))).toReal / (1 + α * η) := by
  have hpos : 0 < 1 + α * η := by positivity
  have hS : 0 < ∑ i, m i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hm
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i,
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hi).symm⟩
  rw [(klDiv_proxKernelPi_comp_gaussTarget hα hη m).2.1, klDiv_pi_gaussTarget hα,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hm2 : 0 < α * ∑ i, m i ^ 2 := by positivity
  have hgt : 1 + α * η < (1 + α * η) ^ 2 := by nlinarith [mul_pos hα hη]
  rw [div_lt_div_iff₀ (by positivity) hpos]
  nlinarith [mul_lt_mul_of_pos_left hgt hm2]

end FormalizeSampling.ProximalSharpPi
