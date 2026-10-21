module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure

/-!
# Shared measure-theory helpers

Small dimension-free facts about densities, products of measures and Gaussian laws that several
modules need. Each lemma is stated once here instead of being re-proved locally.

Status: **Verified** (no named hypotheses).

## Main results

* `integral_withDensity_ofReal`, `integrable_withDensity_ofReal_iff`: integrals and
  integrability against `μ.withDensity (ofReal ∘ p)` for measurable `p ≥ 0`, on any measure
  space.
* `integrable_of_isProbabilityMeasure`: a density `p ≥ 0` with `μ.withDensity (ofReal ∘ p)` a
  probability measure is `μ`-integrable.
* `eq_of_withDensity_eq`: continuous densities of the same finite measure coincide.
* `sq_integral_mul_le`: a weighted Cauchy–Schwarz inequality.
* `klDiv_withDensity_ofReal`: `KL(p μ ‖ p⋆ μ)` is finite and equals `∫ p log(p/p⋆) dμ`.
* `comp_le_smul_comp`: kernel composition preserves `ρ ≤ c • π` (warmness).
* `pi_dirac`: `⊗ᵢ δ_{x i} = δ_x` on `Fin d → ℝ`.
* `lintegral_pi_prod`: Tonelli for products of one-dimensional functions under `Measure.pi`.
* `pi_withDensity_ofReal`: a product of measures with densities has the product density.
* `integral_comp_markov`: integrals of bounded continuous functions against `κ ∘ₘ ρ`.
* `div_integral_eq_gaussianPDFReal`: normalising a multiple of a Gaussian density.
* `aemeasurable_of_map_eq_gaussianReal`, `map_const_mul_of_aemeasurable`: random variables with
  a non-degenerate Gaussian law are a.e.-measurable; laws of scalar multiples.
* `MALA.lintegral_prod_ofReal`: Tonelli for products `∏ᵢ gᵢ(yᵢ)` of integrable nonnegative
  functions on `Fin d → ℝ`.
* `DeterministicStep.klDiv_withDensity_real` (on `ℝ`) and
  `KLTransport.klDiv_withDensity_eq_integral` (on `Fin d → ℝ`): forms of
  `klDiv_withDensity_ofReal` for Lebesgue densities.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace FormalizeSampling.MeasureHelpers

/-! ### Densities -/

/-- For a measurable `p ≥ 0`, integrals against `μ.withDensity (ofReal ∘ p)` are
`μ`-integrals weighted by `p`. -/
theorem integral_withDensity_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : α → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (g : α → ℝ) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (p x)) = ∫ x, p x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (p x))
    hpm.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1; funext x; rw [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul]

/-- For a measurable `p ≥ 0`, integrability against `μ.withDensity (ofReal ∘ p)` is
`μ`-integrability of `p · g`. -/
theorem integrable_withDensity_ofReal_iff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : α → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (g : α → ℝ) :
    Integrable g (μ.withDensity fun x => ENNReal.ofReal (p x)) ↔
      Integrable (fun x => p x * g x) μ := by
  rw [integrable_withDensity_iff_integrable_smul' hpm.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]

/-- A measurable `p ≥ 0` whose density measure `μ.withDensity p` is a probability measure is
`μ`-integrable. -/
theorem integrable_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : α → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (p x))] : Integrable p μ := by
  refine ⟨hpm.aestronglyMeasurable, ?_⟩
  have h1 := measure_univ (μ := μ.withDensity fun x => ENNReal.ofReal (p x))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [HasFiniteIntegral]
  simp_rw [Real.enorm_eq_ofReal (hp0 _), h1]
  exact ENNReal.one_lt_top

/-- Two continuous nonnegative functions with the same finite density measure coincide, for any
reference measure that charges nonempty open sets. -/
theorem eq_of_withDensity_eq {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [μ.IsOpenPosMeasure] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    [IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x))]
    (h : μ.withDensity (fun x => ENNReal.ofReal (f x)) =
      μ.withDensity (fun x => ENNReal.ofReal (g x))) : f = g := by
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ := by
    have := measure_ne_top (μ.withDensity fun x => ENNReal.ofReal (f x)) univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hae := (withDensity_eq_iff (ENNReal.measurable_ofReal.comp hf.measurable).aemeasurable
    (ENNReal.measurable_ofReal.comp hg.measurable).aemeasurable hfin).1 h
  refine (Continuous.ae_eq_iff_eq μ hf hg).1 ?_
  filter_upwards [hae] with x hx
  have := congrArg ENNReal.toReal hx
  simpa [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using this

/-- **Weighted Cauchy–Schwarz.** For `k ≥ 0`, `p > 0` and `g` with `k p`, `k g`, `k g² / p`
`μ`-integrable and `∫ k p dμ > 0`: `(∫ k g dμ)² ≤ (∫ k p dμ) (∫ k g² / p dμ)`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {k p g : α → ℝ}
    (hk : ∀ z, 0 ≤ k z) (hp : ∀ z, 0 < p z) (h1 : Integrable (fun z => k z * p z) μ)
    (h2 : Integrable (fun z => k z * g z) μ) (h3 : Integrable (fun z => k z * (g z ^ 2 / p z)) μ)
    (hC : 0 < ∫ z, k z * p z ∂μ) :
    (∫ z, k z * g z ∂μ) ^ 2 ≤ (∫ z, k z * p z ∂μ) * ∫ z, k z * (g z ^ 2 / p z) ∂μ := by
  set A := ∫ z, k z * (g z ^ 2 / p z) ∂μ
  set B := ∫ z, k z * g z ∂μ
  set C := ∫ z, k z * p z ∂μ
  set m := B / C
  have hpt : ∀ z, k z * ((g z - m * p z) ^ 2 / p z)
      = k z * (g z ^ 2 / p z) - 2 * m * (k z * g z) + m ^ 2 * (k z * p z) := by
    intro z
    have := (hp z).ne'
    field_simp
    ring
  have h0 : 0 ≤ ∫ z, k z * ((g z - m * p z) ^ 2 / p z) ∂μ :=
    integral_nonneg fun z => mul_nonneg (hk z) (div_nonneg (sq_nonneg _) (hp z).le)
  simp_rw [hpt] at h0
  have hI : Integrable (fun z => k z * (g z ^ 2 / p z) - 2 * m * (k z * g z)) μ :=
    h3.sub (h2.const_mul _)
  rw [integral_add hI (h1.const_mul _), integral_sub h3 (h2.const_mul _),
    integral_const_mul, integral_const_mul] at h0
  have hm : m * C = B := div_mul_cancel₀ B hC.ne'
  have : B ^ 2 ≤ A * C := by nlinarith
  linarith

/-- **Density KL bridge.** For a σ-finite `μ`, measurable `p ≥ 0` and `p⋆ > 0` whose density
measures are probability measures, with `p log(p/p⋆)` `μ`-integrable: `klDiv (p μ) (p⋆ μ)` is
finite and its real value is `∫ p log(p/p⋆) dμ`. -/
theorem klDiv_withDensity_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p pStar : α → ℝ} (hp_meas : Measurable p) (hpStar_meas : Measurable pStar)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hpStar_pos : ∀ x, 0 < pStar x)
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (p x))]
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (pStar x))]
    (hKL : Integrable (fun x => p x * Real.log (p x / pStar x)) μ) :
    InformationTheory.klDiv (μ.withDensity fun x => ENNReal.ofReal (p x))
        (μ.withDensity fun x => ENNReal.ofReal (pStar x)) ≠ ∞ ∧
      (InformationTheory.klDiv (μ.withDensity fun x => ENNReal.ofReal (p x))
        (μ.withDensity fun x => ENNReal.ofReal (pStar x))).toReal =
        ∫ x, p x * Real.log (p x / pStar x) ∂μ := by
  set P := μ.withDensity fun x => ENNReal.ofReal (p x) with hP
  set Q := μ.withDensity fun x => ENNReal.ofReal (pStar x) with hQ
  have hfp : Measurable fun x => ENNReal.ofReal (p x) := ENNReal.measurable_ofReal.comp hp_meas
  have hfq : Measurable fun x => ENNReal.ofReal (pStar x) :=
    ENNReal.measurable_ofReal.comp hpStar_meas
  have hPμ : P ≪ μ := withDensity_absolutelyContinuous _ _
  have hμQ : μ ≪ Q :=
    withDensity_absolutelyContinuous' hfq.aemeasurable
      (Eventually.of_forall fun x => by simp [hpStar_pos x])
  have hPQ : P ≪ Q := hPμ.trans hμQ
  have h1 : P.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (p x) :=
    Measure.rnDeriv_withDensity _ hfp
  have h2 : P.rnDeriv Q =ᵐ[μ] fun x => (ENNReal.ofReal (pStar x))⁻¹ * P.rnDeriv μ x :=
    Measure.rnDeriv_withDensity_right P μ hfq.aemeasurable
      (Eventually.of_forall fun x => by simp [hpStar_pos x])
      (Eventually.of_forall fun x => by simp)
  have hllr : llr P Q =ᵐ[μ] fun x => Real.log (p x / pStar x) := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [llr_def]
    simp only
    rw [hx2, hx1, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hp_nonneg x),
      ENNReal.toReal_ofReal (hpStar_pos x).le, inv_mul_eq_div]
  have hlt : ∀ᵐ x ∂μ, ENNReal.ofReal (p x) < ⊤ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hint : ∫ x, llr P Q x ∂P = ∫ x, p x * Real.log (p x / pStar x) ∂μ := by
    rw [hP, integral_withDensity_eq_integral_toReal_smul hfp hlt]
    refine integral_congr_ae ?_
    filter_upwards [hllr] with x hx
    rw [hx, ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]
  have hint' : Integrable (llr P Q) P := by
    rw [hP, integrable_withDensity_iff_integrable_smul' hfp hlt]
    refine hKL.congr ?_
    filter_upwards [hllr] with x hx
    rw [hx, ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]
  refine ⟨InformationTheory.klDiv_ne_top_iff.2 ⟨hPQ, hint'⟩, ?_⟩
  rw [InformationTheory.toReal_klDiv_of_measure_eq hPQ (by simp [measure_univ]), hint]

/-! ### Kernels -/

/-- Kernel composition preserves warmness: `ρ ≤ c • π` gives `κ ∘ₘ ρ ≤ c • (κ ∘ₘ π)`. -/
theorem comp_le_smul_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsSFiniteKernel κ] {ρ π : Measure X} {c : ℝ≥0∞} (h : ρ ≤ c • π) :
    κ ∘ₘ ρ ≤ c • (κ ∘ₘ π) := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hs κ.aemeasurable,
    Measure.bind_apply hs κ.aemeasurable]
  calc ∫⁻ a, κ a s ∂ρ ≤ ∫⁻ a, κ a s ∂(c • π) := lintegral_mono' h le_rfl
    _ = c * ∫⁻ a, κ a s ∂π := by simp [lintegral_smul_measure]

/-! ### Products over `Fin d` -/

variable {d : ℕ}

/-- A product of Dirac masses is the Dirac mass of the tuple:
`⊗ᵢ δ_{x i} = δ_x` on `Fin d → ℝ`. -/
theorem pi_dirac (x : Fin d → ℝ) :
    Measure.pi (fun i => Measure.dirac (x i)) = Measure.dirac x := by
  rw [← Measure.infinitePi_eq_pi, Measure.infinitePi_dirac]

/-- **Lebesgue integral of a product function under a product measure.** For σ-finite
measures `μ i` on `ℝ` and measurable `f i : ℝ → ℝ≥0∞` (`i : Fin n`),
`∫⁻ x, ∏ᵢ f i (x i) ∂(⊗ᵢ μ i) = ∏ᵢ ∫⁻ y, f i y ∂(μ i)`. -/
theorem lintegral_pi_prod {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove μ 0
    rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have e : ∀ z : ℝ × (Fin n → ℝ),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm z i) =
          f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := fun z => by
      rw [Fin.prod_univ_succ]
      rfl
    simp_rw [e]
    simp only [Fin.succAbove_zero]
    have hg : Measurable fun y : Fin n → ℝ => ∏ i : Fin n, f i.succ (y i) :=
      Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
    refine (lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ j.succ) (f := f 0)
      (hf 0).aemeasurable hg.aemeasurable).trans ?_
    rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ), Fin.prod_univ_succ]

/-- **Products of densities.** For nonnegative Lebesgue-integrable `g i : ℝ → ℝ`,
`⊗ᵢ (g i · volume) = (y ↦ ∏ᵢ g i (y i)) · volume` on `Fin d → ℝ`. -/
theorem pi_withDensity_ofReal {g : Fin d → ℝ → ℝ} (hg : ∀ i, Integrable (g i))
    (hg0 : ∀ i u, 0 ≤ g i u) :
    Measure.pi (fun i => volume.withDensity fun u => ENNReal.ofReal (g i u)) =
      volume.withDensity fun y => ENNReal.ofReal (∏ i, g i (y i)) := by
  have : ∀ i, IsFiniteMeasure (volume.withDensity fun u => ENNReal.ofReal (g i u)) :=
    fun i => isFiniteMeasure_withDensity_ofReal (hg i).2
  refine Measure.pi_eq fun S hS => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS), ← lintegral_indicator
    (MeasurableSet.univ_pi hS)]
  have hpt : ∀ y : Fin d → ℝ, (univ.pi S).indicator
      (fun y => ENNReal.ofReal (∏ i, g i (y i))) y =
      ENNReal.ofReal (∏ i, (S i).indicator (g i) (y i)) := by
    intro y
    by_cases h : y ∈ univ.pi S
    · rw [indicator_of_mem h]
      have : ∀ i, y i ∈ S i := fun i => h i (mem_univ i)
      simp [indicator_of_mem (this _)]
    · rw [indicator_of_notMem h]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  simp_rw [hpt]
  have hint : ∀ i, Integrable ((S i).indicator (g i)) := fun i => (hg i).indicator (hS i)
  have hnn : ∀ i u, 0 ≤ (S i).indicator (g i) u := fun i u =>
    indicator_nonneg (fun u _ => hg0 i u) u
  rw [← ofReal_integral_eq_lintegral_ofReal (by
      rw [volume_pi]; exact Integrable.fintype_prod hint)
    (Eventually.of_forall fun y => Finset.prod_nonneg fun i _ => hnn i _), volume_pi,
    integral_fintype_prod_eq_prod (fun i => (S i).indicator (g i)),
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg (hnn i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hS i), ← lintegral_indicator (hS i),
    ofReal_integral_eq_lintegral_ofReal (hint i) (Eventually.of_forall (hnn i))]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ S i
  · simp [indicator_of_mem hu]
  · simp [indicator_of_notMem hu]

/-- Integrals of a bounded continuous `f` against the mixture `κ ∘ₘ ρ₀` of a Markov kernel and
a probability law: `∫ f d(κ ∘ₘ ρ₀) = ∫ (∫ f dκ x) dρ₀(x)`. -/
theorem integral_comp_markov {f : (Fin d → ℝ) → ℝ} (κ : Kernel (Fin d → ℝ) (Fin d → ℝ))
    [IsMarkovKernel κ] (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    ∫ y, f y ∂(κ ∘ₘ ρ₀) = ∫ x, ∫ y, f y ∂(κ x) ∂ρ₀ := by
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp, Kernel.const_apply]
  exact Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)

/-! ### Gaussian laws on `ℝ` -/

/-- If `g = K · N(·; m, v)` pointwise with `K ≠ 0` and `v ≠ 0`, then `g / ∫ g = N(·; m, v)`. -/
theorem div_integral_eq_gaussianPDFReal {g : ℝ → ℝ} {K m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hK : K ≠ 0) (hg : ∀ x, g x = K * gaussianPDFReal m v x) (x : ℝ) :
    g x / ∫ z, g z = gaussianPDFReal m v x := by
  have hint : ∫ z, g z = K := by
    simp_rw [hg]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one m hv, mul_one]
  rw [hint, hg, mul_div_cancel_left₀ _ hK]

/-- A random variable whose law is a nondegenerate Gaussian is a.e.-measurable (otherwise its
image measure would be `0` or a Dirac mass). -/
theorem aemeasurable_of_map_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (h : P.map X = gaussianReal m v) : AEMeasurable X P := by
  by_contra hX
  by_cases hP : P = 0
  · subst hP
    rw [Measure.map_zero] at h
    exact IsProbabilityMeasure.ne_zero (gaussianReal m v) h.symm
  · rw [Measure.map_of_not_aemeasurable_of_ne_zero hX hP] at h
    have h1 := congrArg (fun μ : Measure ℝ => μ {Classical.ofNonempty}) h
    have h0 : gaussianReal m v {Classical.ofNonempty} = 0 :=
      gaussianReal_absolutelyContinuous m hv (Real.volume_singleton)
    simp only [h0, Measure.dirac_apply_of_mem (Set.mem_singleton _)] at h1
    exact one_ne_zero h1

/-- Image of a law under scaling: `Law(c X) = (Law X).map (c * ·)` for a.e.-measurable `X`. -/
theorem map_const_mul_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hXm : AEMeasurable X P) (c : ℝ) :
    P.map (fun ω => c * X ω) = (P.map X).map (fun x => c * x) :=
  (AEMeasurable.map_map_of_aemeasurable (measurable_const_mul c).aemeasurable hXm).symm

end FormalizeSampling.MeasureHelpers

namespace FormalizeSampling.MALA

variable {d : ℕ}

/-- Tonelli for products of one-variable functions on `Fin d → ℝ`: for integrable nonnegative
`gᵢ : ℝ → ℝ`, `∫⁻ y, ∏ᵢ gᵢ(yᵢ) dy = ∏ᵢ ∫⁻ t, gᵢ(t) dt` (in `ℝ≥0∞`). -/
theorem lintegral_prod_ofReal (g : Fin d → ℝ → ℝ) (hg : ∀ i, Integrable (g i))
    (hnn : ∀ i t, 0 ≤ g i t) :
    ∫⁻ y : Fin d → ℝ, ∏ i, ENNReal.ofReal (g i (y i)) = ∏ i, ∫⁻ t, ENNReal.ofReal (g i t) := by
  have hnn' : ∀ y : Fin d → ℝ, 0 ≤ ∏ i, g i (y i) := fun y =>
    Finset.prod_nonneg fun i _ => hnn _ _
  have hint : Integrable (fun y : Fin d → ℝ => ∏ i, g i (y i)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ)) hg
    rw [volume_pi]
    exact this
  have hpt : ∀ y : Fin d → ℝ,
      ∏ i, ENNReal.ofReal (g i (y i)) = ENNReal.ofReal (∏ i, g i (y i)) := fun y =>
    (ENNReal.ofReal_prod_of_nonneg fun i _ => hnn _ _).symm
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn'),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
      fun i _ => integral_nonneg (hnn i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact ofReal_integral_eq_lintegral_ofReal (hg i) (ae_of_all _ (hnn i))

end FormalizeSampling.MALA

/-! ### Density KL bridges in the namespaces of their applications -/

namespace FormalizeSampling.DeterministicStep

/-- One-dimensional density KL bridge: for measurable `p ≥ 0`, measurable `pStar > 0` whose
density measures are probability measures and `p log(p/p⋆)` Lebesgue integrable, Mathlib's
`klDiv (p dx) (p⋆ dx)` is finite and its real value is `∫ p log(p/p⋆)`. (The library's
`KLTransport.klDiv_withDensity_eq_integral` is the same statement on `Fin d → ℝ`.) -/
theorem klDiv_withDensity_real {p pStar : ℝ → ℝ} (hp_meas : Measurable p)
    (hpStar_meas : Measurable pStar) (hp_nonneg : ∀ x, 0 ≤ p x)
    (hpStar_pos : ∀ x, 0 < pStar x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (pStar x))]
    (hKL : Integrable fun x => p x * Real.log (p x / pStar x)) :
    InformationTheory.klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (pStar x)) ≠ ∞ ∧
      (InformationTheory.klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (pStar x))).toReal =
        ∫ x, p x * Real.log (p x / pStar x) :=
  MeasureHelpers.klDiv_withDensity_ofReal hp_meas hpStar_meas hp_nonneg hpStar_pos hKL

end FormalizeSampling.DeterministicStep

namespace FormalizeSampling.KLTransport

variable {d : ℕ}

/-- **Density KL equals Mathlib's `klDiv` (finite-KL case).** Let `p ≥ 0` and `pStar > 0` be
measurable on `Fin d → ℝ` such that `P = volume.withDensity (ofReal ∘ p)` and
`Q = volume.withDensity (ofReal ∘ pStar)` are probability measures, and assume
`p log(p/pStar)` is Lebesgue integrable. Then
`InformationTheory.klDiv P Q = ENNReal.ofReal (∫ p log(p/pStar))`. -/
theorem klDiv_withDensity_eq_integral {p pStar : (Fin d → ℝ) → ℝ}
    (hp_meas : Measurable p) (hpStar_meas : Measurable pStar)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hpStar_pos : ∀ x, 0 < pStar x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (pStar x))]
    (hKL : Integrable (fun x => p x * Real.log (p x / pStar x))) :
    InformationTheory.klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (volume.withDensity fun x => ENNReal.ofReal (pStar x)) =
      ENNReal.ofReal (∫ x, p x * Real.log (p x / pStar x)) := by
  obtain ⟨hne, h⟩ := MeasureHelpers.klDiv_withDensity_ofReal hp_meas hpStar_meas hp_nonneg
    hpStar_pos hKL
  rw [← ENNReal.ofReal_toReal hne, h]

end FormalizeSampling.KLTransport
