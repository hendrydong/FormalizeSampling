module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.Moments.SubGaussian
public import FormalizeSampling.Foundations.GaussianKL

/-!
# Bias of an inexact inner sampler from its KL error

GI-2 (`Samplers/RandomScoreOracle.lean`) charges an inexact inner sampler only through the
squared bias `∑ᵢ (∫ yᵢ d(post k x) - m k x i)²` of its output mean
(`tvSup_biasedMonteCarloChain_le_sqrt`). This file bounds that bias by the inner sampler's
KL error, so GI-2 can be driven by a KL guarantee of the inner sampler.

## Main results

* `integral_le_toReal_klDiv_add_log` (Donsker–Varadhan, the half used here): for probability
  measures `μ, ν` with `KL(μ ‖ ν) < ∞`, `f` `μ`-integrable and `exp ∘ f` `ν`-integrable,
  `∫ f dμ ≤ KL(μ ‖ ν) + log ∫ exp f dν`. Proof: Gibbs' inequality `KL(μ ‖ ν_f) ≥ 0` for the
  tilted measure `ν_f = ν.tilted f` together with Mathlib's `integral_llr_tilted_right`.
* `integral_sub_integral_le_sqrt` (scalar transport inequality): if `X - E_ν X` is
  `σ²`-sub-Gaussian under `ν` (Mathlib's `HasSubgaussianMGF`), then
  `E_μ X - E_ν X ≤ √(2 σ² KL(μ ‖ ν))`.
* `sum_sq_bias_le` (dimension-free vector form on `Fin d → ℝ`): if every unit linear
  functional `y ↦ u ⬝ᵥ y` is `σ²`-sub-Gaussian under the exact law `q`, then
  `∑ᵢ (∫ yᵢ dq' - ∫ yᵢ dq)² ≤ 2 σ² KL(q' ‖ q)` (apply the scalar bound along the unit
  direction of the bias). `sum_sq_bias_le_of_klDiv_le` is the form with a KL budget `δ`.
* Tightness (`hasSubgaussianMGF_gaussianReal`, `sq_bias_gaussianReal_eq`): for
  `q = N(0, v)` (which is `v`-sub-Gaussian) and `q' = N(δ, v)`,
  `(E_{q'} y - E_q y)² = 2 v KL(q' ‖ q)`, so the constant `2` cannot be improved.
* `tvSup_biasedMonteCarloChain_le_sqrt_of_klDiv` (GI-2 driven by a KL guarantee, in
  `Samplers/RandomScoreOracleInner.lean`): if the plug-in centre `m k x` is the mean of an exact
  posterior `postEx k x` that is `σ_k²`-sub-Gaussian in every unit direction, and the inner
  sampler satisfies
  `KL(post k x ‖ postEx k x) ≤ δ_k` for every `x`, then
  `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0)/2 + ∑_{k<n} (h_k c_k²/8)(2 σ_k² δ_k + ∫ V_k dν_k / N))`
  with `V_k(x) = ∑ᵢ Var_{post k x}(yᵢ)`.

## Assumptions and scope

* The KL direction is `KL(inexact ‖ exact)` (output of the inner sampler first), the direction
  delivered by Langevin-type KL guarantees. Sub-Gaussianity is assumed for the **exact** law.
* The KL guarantee is assumed uniformly in the state `x`; the averaged version is
  `InnerSamplerAveraged.tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv_le`. Integrability
  of the GI-2 budget (`hB`) and of
  `V_k` (`hV`) remain hypotheses, as in GI-2. The variance term still refers to the inexact
  law `post k x`; no bound on it is proved.
* Coordinate integrability under the exact law follows from the sub-Gaussian hypothesis
  (`integrable_coord_of_hasSubgaussianMGF`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.InnerSamplerBias

section DonskerVaradhan

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- **Donsker–Varadhan inequality** (the half used for transport bounds). For probability
measures `μ, ν` with `KL(μ ‖ ν) < ∞`, any `f` that is `μ`-integrable with `exp ∘ f`
`ν`-integrable satisfies `∫ f dμ ≤ KL(μ ‖ ν) + log ∫ exp f dν` (KL as a real number). Proof:
Gibbs' inequality for `μ` against the tilted measure `ν.tilted f`. -/
theorem integral_le_toReal_klDiv_add_log [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hKL : klDiv μ ν ≠ ∞) (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => exp (f x)) ν) :
    ∫ x, f x ∂μ ≤ (klDiv μ ν).toReal + log (∫ x, exp (f x) ∂ν) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hKL
  have := isProbabilityMeasure_tilted hfν
  have hac' : μ ≪ ν.tilted f := hac.trans (absolutelyContinuous_tilted hfν)
  have h0 : 0 ≤ (klDiv μ (ν.tilted f)).toReal := ENNReal.toReal_nonneg
  rw [toReal_klDiv_of_measure_eq hac' (by simp), integral_llr_tilted_right hac hfμ hfν hint]
    at h0
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  linarith

/-- Elementary optimisation step behind transport inequalities: if `s, K ≥ 0` and
`t a ≤ K + s t² / 2` for every `t > 0`, then `a ≤ √(2 s K)` (take `t = a / s`). -/
theorem le_sqrt_of_forall_mul_le {a s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 0 < t → t * a ≤ K + s * t ^ 2 / 2) : a ≤ √(2 * s * K) := by
  rcases le_or_gt a 0 with ha | ha
  · exact ha.trans (sqrt_nonneg _)
  refine Real.le_sqrt_of_sq_le ?_
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have := h ((K + 1) / a) (by positivity)
    rw [div_mul_cancel₀ _ ha.ne'] at this
    linarith
  · have := h (a / s) (by positivity)
    have e1 : a / s * a = a ^ 2 / s := by ring
    have e2 : s * (a / s) ^ 2 / 2 = a ^ 2 / s / 2 := by field_simp
    rw [e1, e2] at this
    have : a ^ 2 / s ≤ 2 * K := by linarith
    rw [div_le_iff₀ hs0] at this
    linarith

/-- **Sub-Gaussian transport inequality.** For probability measures `μ, ν`, if the centred
variable `X - E_ν X` is `s`-sub-Gaussian under `ν` (`HasSubgaussianMGF`, i.e.
`log E_ν exp(t (X - E_ν X)) ≤ s t² / 2` for all `t`), `X` is `μ`-integrable and
`KL(μ ‖ ν) < ∞`, then `E_μ X - E_ν X ≤ √(2 s KL(μ ‖ ν))`. -/
theorem integral_sub_integral_le_sqrt [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : α → ℝ} {s : ℝ≥0} (hX : HasSubgaussianMGF (fun y => X y - ∫ z, X z ∂ν) s ν)
    (hXμ : Integrable X μ) (hKL : klDiv μ ν ≠ ∞) :
    ∫ x, X x ∂μ - ∫ x, X x ∂ν ≤ √(2 * s * (klDiv μ ν).toReal) := by
  set c := ∫ z, X z ∂ν
  refine le_sqrt_of_forall_mul_le s.2 ENNReal.toReal_nonneg fun t _ => ?_
  have hfμ : Integrable (fun y => t * (X y - c)) μ := (hXμ.sub (integrable_const c)).const_mul t
  have hfν := hX.integrable_exp_mul t
  have key := integral_le_toReal_klDiv_add_log hKL hfμ hfν
  rw [integral_const_mul, integral_sub hXμ (integrable_const c)] at key
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at key
  have hlog : log (∫ x, exp (t * (X x - c)) ∂ν) ≤ s * t ^ 2 / 2 := by
    have hm := hX.mgf_le t
    have hpos := mgf_pos (X := fun y => X y - c) (t := t) hfν
    calc log (∫ x, exp (t * (X x - c)) ∂ν) = log (mgf (fun y => X y - c) ν t) := rfl
      _ ≤ log (exp (s * t ^ 2 / 2)) := log_le_log hpos hm
      _ = s * t ^ 2 / 2 := log_exp _
  linarith

end DonskerVaradhan

section Vector

variable {d : ℕ} {q q' : Measure (Fin d → ℝ)}

/-- Linearity of the integral for a linear functional on `Fin d → ℝ`:
`∫ u ⬝ᵥ y dq = ∑ᵢ uᵢ ∫ yᵢ dq` when every coordinate is `q`-integrable. -/
theorem integral_dotProduct (q : Measure (Fin d → ℝ)) (u : Fin d → ℝ)
    (hq : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q) :
    ∫ y, u ⬝ᵥ y ∂q = ∑ i, u i * ∫ y, y i ∂q := by
  simp only [dotProduct]
  rw [integral_finsetSum _ fun i _ => (hq i).const_mul (u i)]
  simp_rw [integral_const_mul]

/-- If every unit linear functional `y ↦ u ⬝ᵥ y` (centred) is sub-Gaussian under a finite
measure `q`, then every coordinate is `q`-integrable (take `u` a standard basis vector). -/
theorem integrable_coord_of_hasSubgaussianMGF [IsFiniteMeasure q] {s : ℝ≥0}
    (hsub : ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂q) s q) (i : Fin d) :
    Integrable (fun y : Fin d → ℝ => y i) q := by
  have h1 : (Pi.single i 1 : Fin d → ℝ) ⬝ᵥ Pi.single i 1 = 1 := by simp
  have := ((hsub _ h1).integrable).add
    (integrable_const (∫ z, (Pi.single i 1 : Fin d → ℝ) ⬝ᵥ z ∂q))
  refine this.congr (ae_of_all _ fun y => ?_)
  simp

/-- **Squared bias from KL, dimension-free.** Let `q` (exact law) and `q'` (inexact law,
coordinates integrable) be probability measures on `Fin d → ℝ` with `KL(q' ‖ q) < ∞`. If for
every unit vector `u` (`u ⬝ᵥ u = 1`) the centred functional `u ⬝ᵥ y - E_q[u ⬝ᵥ y]` is
`s`-sub-Gaussian under `q`, then
`∑ᵢ (∫ yᵢ dq' - ∫ yᵢ dq)² ≤ 2 s KL(q' ‖ q)`. -/
theorem sum_sq_bias_le [IsProbabilityMeasure q] [IsProbabilityMeasure q'] {s : ℝ≥0}
    (hsub : ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂q) s q)
    (hq' : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q') (hKL : klDiv q' q ≠ ∞) :
    ∑ i, (∫ y, y i ∂q' - ∫ y, y i ∂q) ^ 2 ≤ 2 * s * (klDiv q' q).toReal := by
  have hq := integrable_coord_of_hasSubgaussianMGF hsub
  set b : Fin d → ℝ := fun i => ∫ y, y i ∂q' - ∫ y, y i ∂q with hb
  set S := ∑ i, b i ^ 2 with hS
  have hR : 0 ≤ 2 * (s : ℝ) * (klDiv q' q).toReal := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hR
  set r := √S with hr
  have hr0 : 0 < r := sqrt_pos.2 hpos
  set u : Fin d → ℝ := r⁻¹ • b with hu
  have huu : u ⬝ᵥ u = 1 := by
    simp only [hu, dotProduct, Pi.smul_apply, smul_eq_mul]
    have : ∑ i, r⁻¹ * b i * (r⁻¹ * b i) = (r ^ 2)⁻¹ * S := by
      rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hr, sq_sqrt hS0, inv_mul_cancel₀ hpos.ne']
  have hXq' : Integrable (fun y => u ⬝ᵥ y) q' := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hq' i).const_mul (u i)
  have key := integral_sub_integral_le_sqrt (hsub u huu) hXq' hKL
  rw [integral_dotProduct q' u hq', integral_dotProduct q u hq, ← Finset.sum_sub_distrib] at key
  have : ∑ i, (u i * ∫ y, y i ∂q' - u i * ∫ y, y i ∂q) = r := by
    have e : ∀ i, u i * ∫ y, y i ∂q' - u i * ∫ y, y i ∂q = r⁻¹ * b i ^ 2 / 1 * 1 := fun i => by
      simp only [hu, hb, Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [e, div_one, mul_one, ← Finset.mul_sum, ← hS]
    rw [hr]
    field_simp
    rw [sq_sqrt hS0]
  rw [this, hr, sqrt_le_sqrt_iff hR] at key
  exact key

/-- **Squared bias under a KL budget.** As `sum_sq_bias_le`, with the exact mean given as a
vector `m` (`mᵢ = ∫ yᵢ dq`) and a KL guarantee `KL(q' ‖ q) ≤ δ`:
`∑ᵢ (∫ yᵢ dq' - mᵢ)² ≤ 2 s δ`. This is the squared-bias term of GI-2. -/
theorem sum_sq_bias_le_of_klDiv_le [IsProbabilityMeasure q] [IsProbabilityMeasure q']
    {s δ : ℝ≥0} {m : Fin d → ℝ} (hm : ∀ i, m i = ∫ y, y i ∂q)
    (hsub : ∀ u : Fin d → ℝ, u ⬝ᵥ u = 1 →
      HasSubgaussianMGF (fun y => u ⬝ᵥ y - ∫ z, u ⬝ᵥ z ∂q) s q)
    (hq' : ∀ i, Integrable (fun y : Fin d → ℝ => y i) q') (hKL : klDiv q' q ≤ δ) :
    ∑ i, (∫ y, y i ∂q' - m i) ^ 2 ≤ 2 * s * δ := by
  have hne : klDiv q' q ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hKL
  have h1 := sum_sq_bias_le hsub hq' hne
  have h2 : (klDiv q' q).toReal ≤ δ := ENNReal.toReal_le_coe_of_le_coe hKL
  simp_rw [hm]
  exact h1.trans (by gcongr)

end Vector

section GaussianTight

/-- The centred Gaussian `N(0, v)` is `v`-sub-Gaussian: the hypothesis of
`integral_sub_integral_le_sqrt` holds for `ν = N(0, v)`, `X = id` with `s = v`. -/
theorem hasSubgaussianMGF_gaussianReal (v : ℝ≥0) :
    HasSubgaussianMGF (fun y => y - ∫ z, z ∂gaussianReal 0 v) v (gaussianReal 0 v) := by
  simp only [integral_id_gaussianReal, sub_zero]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_fun_id_gaussianReal]
  simp

/-- **Tightness of the bias bound.** For `q = N(0, v)` and `q' = N(δ, v)` with `v ≠ 0`,
`(E_{q'} y - E_q y)² = 2 v KL(q' ‖ q)` (both sides equal `δ²`), so the constant in
`integral_sub_integral_le_sqrt` and `sum_sq_bias_le` (for `d = 1`) is attained. -/
theorem sq_bias_gaussianReal_eq (δ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ y, y ∂gaussianReal δ v - ∫ y, y ∂gaussianReal 0 v) ^ 2 =
      2 * v * (klDiv (gaussianReal δ v) (gaussianReal 0 v)).toReal := by
  have hv' : 0 < (v : ℝ) := by positivity
  rw [GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ hv,
    ENNReal.toReal_ofReal (by positivity), integral_id_gaussianReal, integral_id_gaussianReal]
  field_simp

end GaussianTight

end FormalizeSampling.InnerSamplerBias
