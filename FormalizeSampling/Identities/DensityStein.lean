module

public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Density Stein identities and the zero-mean state score

Registry ID: **ID-2** (density Stein identity and zero mean of the spatial score), in
dimension one and on `Fin d → ℝ`.

## Scope and conventions

* `p` is a strictly positive function (`∀ x, 0 < p x`) playing the role of an (unnormalised)
  density; `φ` (resp. a vector field `f`) is a test function. All integrals are Lebesgue
  integrals with respect to `volume`, on `ℝ` or on `Fin d → ℝ`. No normalisation `∫ p = 1` is
  ever assumed: every statement is an identity between Lebesgue integrals weighted by `p`.
* Scores are *state* scores from `FormalizeSampling.Foundations.VectorCalculus`:
  `score1 p x = (log p)'(x)` and `score p x i = ∂ᵢ log p(x)`. Strict positivity of `p` is what
  makes `score1 p x * p x = p'(x)` and `score p x i * p x = ∂ᵢ p(x)` hold pointwise (Lean's
  `Real.log 0 = 0` convention would otherwise break the identity).
* Boundary terms are controlled by **integrability** (`φ p`, `φ' p`, `φ p'` integrable), the
  convention of Mathlib's `integral_mul_deriv_eq_deriv_mul_of_integrable` and
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`; no decay at infinity is assumed.

## Main results

ID-2 (density Stein identity `∫ φ' p = -∫ φ (∇ log p) p`):
* `integral_deriv_mul_eq_neg_integral_mul_score1`: 1D, with explicit derivatives and the three
  integrability hypotheses.
* `integral_deriv_mul_eq_neg_integral_mul_score1_of_hasCompactSupport`: 1D, `p` positive and
  `C¹`, `φ` `C¹` with compact support; no integrability hypotheses.
* `integral_partialDeriv_mul_eq_neg_integral_mul_score`: `Fin d → ℝ`, `i`-th coordinate
  direction, with the three integrability hypotheses.
* `integral_divergence_mul_eq_neg_integral_dotProduct_score`: vector-field form
  `∫ (div f) p = -∫ (f ⬝ᵥ ∇ log p) p`, with coordinatewise integrability hypotheses.
* `integral_partialDeriv_mul_eq_neg_integral_mul_score_of_hasCompactSupport` and
  `integral_divergence_mul_eq_neg_integral_dotProduct_score_of_hasCompactSupport`: the two
  `d`-dimensional identities for `C¹` positive `p` and `C¹` compactly supported test functions,
  with no integrability hypotheses.

ID-2 (zero-mean score `∫ (∇ log p) p = 0`):
* `integral_score1_mul_eq_zero`, `integral_score1_withDensity_eq_zero`: 1D.
* `integral_score_mul_eq_zero` (one coordinate), `integral_smul_score_eq_zero` (vector-valued
  Bochner integral), `integral_score_withDensity_eq_zero` (integral of the vector score against
  the measure `p · volume`): on `Fin d → ℝ`.

## What is NOT proved here

* Versions with boundary terms controlled by decay at infinity (`φ p → 0`) instead of
  integrability of `φ p`, and discharges for Schwartz-class test functions or for specific
  densities such as Gaussians (the identities hold for them, but the integrability hypotheses
  are not discharged here except in the compact-support corollaries).
* Densities that vanish somewhere or are supported on a proper domain (only `∀ x, 0 < p x` is
  treated), weakly differentiable densities, and non-Lebesgue reference measures.
* The ID-2 statements are not specialised to probability densities; when `∫ p = 1` they say
  that the expectation of the score under `p · volume` is zero, but that is not stated
  separately.
-/

public section

open MeasureTheory Matrix

namespace FormalizeSampling.DensityStein

/-! ### One dimension -/

/-- Pointwise identity behind the 1D density Stein identity: if `p` has derivative `p'` at `x`
and `p x > 0`, then `score1 p x * p x = p'`, i.e. `(log p)'(x) p(x) = p'(x)`. -/
theorem score1_mul_eq_of_hasDerivAt {p : ℝ → ℝ} {p' x : ℝ} (hp : HasDerivAt p p' x)
    (hpos : 0 < p x) : score1 p x * p x = p' := by
  rw [score1_of_pos hp.differentiableAt hpos, hp.deriv]
  field_simp

/-- **Density Stein identity (ID-2), 1D.** Let `p, φ : ℝ → ℝ` with `p x > 0` for all `x`,
`p` having derivative `p' x` and `φ` having derivative `φ' x` at every `x`. If `φ' p`, `φ p'`
and `φ p` are Lebesgue integrable, then
`∫ φ'(x) p(x) dx = -∫ φ(x) (log p)'(x) p(x) dx`.
No normalisation of `p` is assumed; integrability of `φ p` replaces vanishing boundary terms. -/
theorem integral_deriv_mul_eq_neg_integral_mul_score1 {p p' φ φ' : ℝ → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : ∀ x, HasDerivAt p (p' x) x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'p : Integrable (fun x => φ' x * p x)) (hφp' : Integrable (fun x => φ x * p' x))
    (hφp : Integrable (fun x => φ x * p x)) :
    ∫ x, φ' x * p x = -∫ x, φ x * score1 p x * p x := by
  have h : ∀ x, φ x * score1 p x * p x = φ x * p' x := fun x => by
    rw [mul_assoc, score1_mul_eq_of_hasDerivAt (hp x) (hpos x)]
  simp_rw [h]
  rw [integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hφ x) (fun x _ => hp x)
    hφp' hφ'p hφp, neg_neg]

/-- **Density Stein identity (ID-2), 1D, compactly supported test functions.** If
`p : ℝ → ℝ` is `C¹` with `p x > 0` for all `x`, and `φ : ℝ → ℝ` is `C¹` with compact support,
then `∫ φ'(x) p(x) dx = -∫ φ(x) (log p)'(x) p(x) dx`. No integrability or normalisation of `p`
is required: all integrands are continuous with compact support. -/
theorem integral_deriv_mul_eq_neg_integral_mul_score1_of_hasCompactSupport {p φ : ℝ → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : ContDiff ℝ 1 p) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, deriv φ x * p x = -∫ x, φ x * score1 p x * p x := by
  have hp' : Continuous (deriv p) := hp.continuous_deriv le_rfl
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hpd : Differentiable ℝ p := hp.differentiable one_ne_zero
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  refine integral_deriv_mul_eq_neg_integral_mul_score1 hpos (fun x => (hpd x).hasDerivAt)
    (fun x => (hφd x).hasDerivAt) ?_ ?_ ?_
  · exact (hφ'.mul hp.continuous).integrable_of_hasCompactSupport hφc.deriv.mul_right
  · exact (hφ.continuous.mul hp').integrable_of_hasCompactSupport hφc.mul_right
  · exact (hφ.continuous.mul hp.continuous).integrable_of_hasCompactSupport hφc.mul_right

/-- **Zero-mean score (ID-2), 1D.** If `p : ℝ → ℝ` is differentiable with `p x > 0` for all
`x`, and both `p` and `p'` are Lebesgue integrable, then `∫ (log p)'(x) p(x) dx = 0`.
Normalisation `∫ p = 1` is not needed, only integrability of `p` and of its derivative. -/
theorem integral_score1_mul_eq_zero {p : ℝ → ℝ} (hpos : ∀ x, 0 < p x)
    (hp : Differentiable ℝ p) (hpi : Integrable p) (hp'i : Integrable (deriv p)) :
    ∫ x, score1 p x * p x = 0 := by
  have h : ∀ x, score1 p x * p x = deriv p x := fun x =>
    score1_mul_eq_of_hasDerivAt (hp x).hasDerivAt (hpos x)
  simp_rw [h]
  exact integral_eq_zero_of_hasDerivAt_of_integrable (fun x => (hp x).hasDerivAt) hp'i hpi

/-- **Zero-mean score (ID-2), 1D, measure form.** Under the hypotheses of
`integral_score1_mul_eq_zero` (`p` differentiable and strictly positive, `p` and `p'`
integrable), the integral of the score `(log p)'` against the measure `p · volume`
(`volume.withDensity (ENNReal.ofReal ∘ p)`) is zero. When `∫ p = 1` this is the statement that
the score has mean zero under the law with density `p`; normalisation is not assumed. -/
theorem integral_score1_withDensity_eq_zero {p : ℝ → ℝ} (hpos : ∀ x, 0 < p x)
    (hp : Differentiable ℝ p) (hpi : Integrable p) (hp'i : Integrable (deriv p)) :
    ∫ x, score1 p x ∂(volume.withDensity fun x => ENNReal.ofReal (p x)) = 0 := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul, mul_comm (p _)]
  exact integral_score1_mul_eq_zero hpos hp hpi hp'i

/-! ### The state space `Fin d → ℝ` -/

variable {d : ℕ}

/-- **Density Stein identity (ID-2), `d`-dimensional, one coordinate.** Let
`p, φ : (Fin d → ℝ) → ℝ` be differentiable with `p x > 0` for all `x`, and `i : Fin d`. If
`(∂ᵢ φ) p`, `φ (∂ᵢ p)` and `φ p` are Lebesgue integrable on `Fin d → ℝ`, then
`∫ ∂ᵢ φ(x) p(x) dx = -∫ φ(x) (∂ᵢ log p)(x) p(x) dx`.
No normalisation of `p` is assumed; integrability replaces vanishing boundary terms. -/
theorem integral_partialDeriv_mul_eq_neg_integral_mul_score {p φ : (Fin d → ℝ) → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hφ : Differentiable ℝ φ) (i : Fin d)
    (hφ'p : Integrable (fun x => partialDeriv i φ x * p x))
    (hφp' : Integrable (fun x => φ x * partialDeriv i p x))
    (hφp : Integrable (fun x => φ x * p x)) :
    ∫ x, partialDeriv i φ x * p x = -∫ x, φ x * score p x i * p x := by
  have h : ∀ x, φ x * score p x i * p x = φ x * partialDeriv i p x := fun x => by
    rw [mul_assoc, score_mul_self_of_pos (hp x) (hpos x)]
  simp_rw [h]
  simp only [partialDeriv] at hφ'p hφp' ⊢
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hφ'p hφp' hφp
    (fun x _ => hφ x) (fun x _ => hp x), neg_neg]

/-- **Density Stein identity (ID-2), `d`-dimensional, compactly supported test function.**
If `p : (Fin d → ℝ) → ℝ` is `C¹` with `p x > 0` for all `x`, and `φ` is `C¹` with compact
support, then for every `i`, `∫ ∂ᵢ φ(x) p(x) dx = -∫ φ(x) (∂ᵢ log p)(x) p(x) dx`.
No integrability or normalisation of `p` is required. -/
theorem integral_partialDeriv_mul_eq_neg_integral_mul_score_of_hasCompactSupport
    {p φ : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < p x) (hp : ContDiff ℝ 1 p)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin d) :
    ∫ x, partialDeriv i φ x * p x = -∫ x, φ x * score p x i * p x := by
  refine integral_partialDeriv_mul_eq_neg_integral_mul_score hpos (hp.differentiable one_ne_zero)
    (hφ.differentiable one_ne_zero) i ?_ ?_ ?_
  · exact ((continuous_partialDeriv hφ i).mul hp.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_partialDeriv hφc i).mul_right
  · exact (hφ.continuous.mul (continuous_partialDeriv hp i)).integrable_of_hasCompactSupport
      hφc.mul_right
  · exact (hφ.continuous.mul hp.continuous).integrable_of_hasCompactSupport hφc.mul_right

/-- **Density Stein identity (ID-2), vector-field form.** Let `p : (Fin d → ℝ) → ℝ` be
differentiable with `p x > 0` for all `x`, and `f : (Fin d → ℝ) → Fin d → ℝ` a vector field
whose coordinates `fᵢ` are differentiable. If for every `i` the functions `(∂ᵢ fᵢ) p`,
`fᵢ (∂ᵢ p)` and `fᵢ p` are Lebesgue integrable, then
`∫ (div f)(x) p(x) dx = -∫ (f(x) ⬝ᵥ ∇ log p(x)) p(x) dx`. -/
theorem integral_divergence_mul_eq_neg_integral_dotProduct_score
    {p : (Fin d → ℝ) → ℝ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (hf : ∀ i, Differentiable ℝ (fun y => f y i))
    (hf'p : ∀ i, Integrable (fun x => partialDeriv i (fun y => f y i) x * p x))
    (hfp' : ∀ i, Integrable (fun x => f x i * partialDeriv i p x))
    (hfp : ∀ i, Integrable (fun x => f x i * p x)) :
    ∫ x, divergence f x * p x = -∫ x, (f x ⬝ᵥ score p x) * p x := by
  have h1 : ∀ x, divergence f x * p x = ∑ i, partialDeriv i (fun y => f y i) x * p x := by
    intro x; simp [divergence, Finset.sum_mul]
  have h2 : ∀ x, (f x ⬝ᵥ score p x) * p x = ∑ i, f x i * score p x i * p x := by
    intro x; simp [dotProduct, Finset.sum_mul]
  have h3 : ∀ i, Integrable (fun x => f x i * score p x i * p x) := fun i =>
    (hfp' i).congr (Filter.Eventually.of_forall fun x => by
      simp only; rw [mul_assoc, score_mul_self_of_pos (hp x) (hpos x)])
  simp_rw [h1, h2]
  rw [integral_finsetSum _ (fun i _ => hf'p i), integral_finsetSum _ (fun i _ => h3 i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact integral_partialDeriv_mul_eq_neg_integral_mul_score hpos hp (hf i) i (hf'p i)
    (hfp' i) (hfp i)

/-- **Density Stein identity (ID-2), vector-field form, compactly supported test field.**
If `p : (Fin d → ℝ) → ℝ` is `C¹` with `p x > 0` for all `x`, and every coordinate `fᵢ` of the
vector field `f` is `C¹` with compact support, then
`∫ (div f)(x) p(x) dx = -∫ (f(x) ⬝ᵥ ∇ log p(x)) p(x) dx`, with no integrability or
normalisation hypotheses on `p`. -/
theorem integral_divergence_mul_eq_neg_integral_dotProduct_score_of_hasCompactSupport
    {p : (Fin d → ℝ) → ℝ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : ContDiff ℝ 1 p)
    (hf : ∀ i, ContDiff ℝ 1 (fun y => f y i))
    (hfc : ∀ i, HasCompactSupport (fun y => f y i)) :
    ∫ x, divergence f x * p x = -∫ x, (f x ⬝ᵥ score p x) * p x := by
  refine integral_divergence_mul_eq_neg_integral_dotProduct_score hpos
    (hp.differentiable one_ne_zero) (fun i => (hf i).differentiable one_ne_zero) (fun i => ?_)
    (fun i => ?_) (fun i => ?_)
  · exact ((continuous_partialDeriv (hf i) i).mul hp.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_partialDeriv (hfc i) i).mul_right
  · exact ((hf i).continuous.mul (continuous_partialDeriv hp i)).integrable_of_hasCompactSupport
      (hfc i).mul_right
  · exact ((hf i).continuous.mul hp.continuous).integrable_of_hasCompactSupport (hfc i).mul_right

/-- **Zero-mean score (ID-2), `d`-dimensional, one coordinate.** If
`p : (Fin d → ℝ) → ℝ` is differentiable with `p x > 0` for all `x`, and `p` and `∂ᵢ p` are
Lebesgue integrable, then `∫ (∂ᵢ log p)(x) p(x) dx = 0`. Normalisation `∫ p = 1` is not
needed, only integrability of `p` and of `∂ᵢ p`. -/
theorem integral_score_mul_eq_zero {p : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < p x)
    (hp : Differentiable ℝ p) (i : Fin d) (hpi : Integrable p)
    (hp'i : Integrable (partialDeriv i p)) :
    ∫ x, score p x i * p x = 0 := by
  have h0 : ∀ x, partialDeriv i (fun _ => (1 : ℝ)) x = 0 := fun x => by simp [partialDeriv]
  have key := integral_partialDeriv_mul_eq_neg_integral_mul_score (φ := fun _ => (1 : ℝ))
    hpos hp (differentiable_const 1) i (by simp only [h0, zero_mul]; exact integrable_zero _ _ _)
    (by simpa using hp'i) (by simpa using hpi)
  simp only [h0, zero_mul, integral_zero, one_mul] at key
  linarith

/-- **Zero-mean score (ID-2), `d`-dimensional, vector form.** If `p : (Fin d → ℝ) → ℝ` is
differentiable with `p x > 0` for all `x`, `p` is integrable and every partial derivative
`∂ᵢ p` is integrable, then the vector-valued (Bochner) integral `∫ p(x) ∇ log p(x) dx` is `0`.
Normalisation is not needed. -/
theorem integral_smul_score_eq_zero {p : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < p x)
    (hp : Differentiable ℝ p) (hpi : Integrable p)
    (hp'i : ∀ i, Integrable (partialDeriv i p)) :
    ∫ x, p x • score p x = 0 := by
  have h : ∀ i x, (p x • score p x) i = partialDeriv i p x := fun i x => by
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, score_mul_self_of_pos (hp x) (hpos x)]
  have hint : ∀ i, Integrable (fun x => (p x • score p x) i) := fun i => by
    simp_rw [h]; exact hp'i i
  funext i
  rw [eval_integral hint i, Pi.zero_apply, ← integral_score_mul_eq_zero hpos hp i hpi (hp'i i)]
  congr 1
  funext x
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Zero-mean score (ID-2), `d`-dimensional, measure form.** Under the hypotheses of
`integral_smul_score_eq_zero` (`p` differentiable and strictly positive, `p` and all `∂ᵢ p`
integrable), the integral of the vector score `∇ log p` against the measure `p · volume`
(`volume.withDensity (ENNReal.ofReal ∘ p)`) is zero. When `∫ p = 1` this says the score has
mean zero under the law with density `p`; normalisation is not assumed. -/
theorem integral_score_withDensity_eq_zero {p : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < p x)
    (hp : Differentiable ℝ p) (hpi : Integrable p)
    (hp'i : ∀ i, Integrable (partialDeriv i p)) :
    ∫ x, score p x ∂(volume.withDensity fun x => ENNReal.ofReal (p x)) = 0 := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hpos _).le]
  exact integral_smul_score_eq_zero hpos hp hpi hp'i

end FormalizeSampling.DensityStein
