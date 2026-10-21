module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Order.CompletePartialOrder
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Weak equality of the noise generator and the score-flow generator

Registry ID: **ID-3** (weak noise-score generator equality, including the preconditioned
Langevin / PFG weak generator identity).

For a drift `b`, a constant `D`, and a density `p > 0`, the diffusion generator
`L φ = b ⬝ ∇φ + D Δφ` (of `dX = b(X) dt + √(2D) dW`) and the probability-flow (transport)
generator `L^pf φ = (b - D ∇log p) ⬝ ∇φ` have the same expectation under `p`:

  `∫ (b ⬝ ∇φ + D Δφ) p dx = ∫ ((b - D ∇log p) ⬝ ∇φ) p dx`.

This is an integration-by-parts identity: `∫ ∂ᵢ∂ᵢφ · p = -∫ ∂ᵢφ · ∂ᵢp` and
`∂ᵢp = (∇log p)ᵢ · p`. No Brownian motion, SDE solution, or Fokker–Planck equation is
involved; the two generators are integrated against the *same* given function `p`.

## Conventions

* State space `Fin d → ℝ` with Lebesgue measure `volume`; `⬝ᵥ` is `dotProduct`, `*ᵥ` is
  `Matrix.mulVec`. Partial derivatives, `grad`, `laplacian`, `weightedLaplacian` and the
  state score `score p = ∇ₓ log p` are those of `FormalizeSampling.Foundations.VectorCalculus`
  (Fréchet-derivative based).
* "Expectation under `p`" means `∫ f x * p x`. None of the theorems needs `p` to be integrable
  or normalised; when `p` is a probability density the integrals are expectations.
* The constant `D` and the matrix `A` are arbitrary: the identities are algebraic and hold for
  every sign. The stochastic interpretation (`√(2D)`, `√(2A)`) needs `D ≥ 0`, resp. `A`
  positive semidefinite, but nothing here uses or proves that.

## Main results

* `integral_generator_eq_score_flow_generator` (ID-3 headline, `d`-dimensional, fully
  discharged): `b` continuous, `p` `C¹` and everywhere positive, `φ` `C²` with compact support.
* `integral_generator_eq_score_flow_generator_of_integrable`: the same identity under
  explicit differentiability and integrability hypotheses instead of compact support.
* `integral_weighted_generator_eq_transport_of_integrable` /
  `integral_weighted_generator_eq_transport`: the general constant-matrix version
  `∫ (b ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ ((b - Aᵀ ∇log p) ⬝ ∇φ) p`, no symmetry needed.
* `integral_preconditioned_generator_eq_klFlow_generator` (ID-3, `Aᵀ = A`) and
  `integral_preconditioned_generator_eq_klFlow_generator_transpose` (ID-3, arbitrary `A`,
  `Aᵀ` in the score term): preconditioned Langevin vs. ideal PFG transport.
* `integral_generator_eq_score_flow_generator_one_dim` (and `_of_integrable`): the readable
  one-dimensional corollary with `deriv` and `score1`.
* `generator_integrands_ne_at_zero`, `weak_generator_eq_but_not_pointwise`: for the standard
  Gaussian density, `b = 0`, `D = 1` and an explicit compactly supported smooth test function,
  the two generator integrands differ at `x = 0` although their integrals agree. The identity
  is therefore a *weak* (expectation-level) equality, not a pointwise generator equality.

## What is NOT proved here

* Nothing about stochastic processes: no Brownian motion, no existence or uniqueness of SDE or
  ODE solutions, no Fokker–Planck / continuity equation, no equality of one-time marginal laws
  (FL-5) and no path-law statement.
* Test functions are `C²` with compact support (or satisfy the explicit integrability
  hypotheses of the `_of_integrable` versions); Schwartz-class or merely decaying test
  functions are only covered through those hypotheses.
* `p` must be differentiable and *strictly positive everywhere*; densities vanishing on a set,
  or only a.e. regular, are not covered.
* Only constant `D` and constant `A`; a state-dependent diffusion matrix `A(x)` (which needs
  extra divergence terms) is not treated.
* The symmetry of the Hessian of `φ` is not used; in particular the fact that
  `weightedLaplacian A φ = weightedLaplacian Aᵀ φ` for `C²` functions is not proved here.
-/

@[expose] public section

open MeasureTheory Matrix ProbabilityTheory

namespace FormalizeSampling
namespace ScoreFlowWeak

variable {d : ℕ}

/-! ### Pointwise algebra and one-step integration by parts -/

/-- **Integration by parts in one coordinate direction on `ℝᵈ`.** If `g` and `p` are
differentiable on `Fin d → ℝ` and `∂ᵢg · p`, `g · ∂ᵢp` and `g · p` are Lebesgue integrable,
then `∫ ∂ᵢg · p = -∫ g · ∂ᵢp` (no boundary term). -/
theorem integral_partialDeriv_mul_eq_neg {g p : (Fin d → ℝ) → ℝ} (i : Fin d)
    (hg : Differentiable ℝ g) (hp : Differentiable ℝ p)
    (hg'p : Integrable (fun x => partialDeriv i g x * p x))
    (hgp' : Integrable (fun x => g x * partialDeriv i p x))
    (hgp : Integrable (fun x => g x * p x)) :
    ∫ x, partialDeriv i g x * p x = -∫ x, g x * partialDeriv i p x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := p) (g := g) (v := Pi.single i 1)
    (by simpa [partialDeriv, mul_comm] using hgp')
    (by simpa [partialDeriv, mul_comm] using hg'p)
    (by simpa [mul_comm] using hgp) (fun x _ => hp x) (fun x _ => hg x)
  simp only [partialDeriv] at h ⊢
  simpa [mul_comm] using h

/-- Pointwise expansion of the matrix transport integrand: where `p` is differentiable and
positive, `((b - Aᵀ ∇log p) ⬝ ∇φ) p = (b ⬝ ∇φ) p - ∑ᵢⱼ Aᵢⱼ ∂ⱼφ ∂ᵢp`. -/
theorem transport_integrand_eq {A : Matrix (Fin d) (Fin d) ℝ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {p φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hp : DifferentiableAt ℝ p x) (hpos : 0 < p x) :
    ((b x - Aᵀ *ᵥ score p x) ⬝ᵥ grad φ x) * p x =
      (b x ⬝ᵥ grad φ x) * p x -
        ∑ i, ∑ j, A i j * (partialDeriv j φ x * partialDeriv i p x) := by
  have hs : ∀ i, score p x i * p x = partialDeriv i p x := score_mul_self_of_pos hp hpos
  rw [sub_dotProduct, sub_mul, sub_right_inj]
  simp only [dotProduct, mulVec, transpose_apply, grad, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hs i]
  ring

/-- Pointwise expansion of the scalar-diffusion transport integrand: where `p` is
differentiable and positive, `((b - D ∇log p) ⬝ ∇φ) p = (b ⬝ ∇φ) p - D ∑ᵢ ∂ᵢφ ∂ᵢp`. -/
theorem transport_integrand_eq_smul {D : ℝ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {p φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hp : DifferentiableAt ℝ p x) (hpos : 0 < p x) :
    ((b x - D • score p x) ⬝ᵥ grad φ x) * p x =
      (b x ⬝ᵥ grad φ x) * p x - D * ∑ i, partialDeriv i φ x * partialDeriv i p x := by
  have hs : ∀ i, score p x i * p x = partialDeriv i p x := score_mul_self_of_pos hp hpos
  rw [sub_dotProduct, sub_mul, sub_right_inj, smul_dotProduct, smul_eq_mul]
  simp only [dotProduct, grad, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hs i]
  ring

/-! ### Versions with explicit integrability hypotheses -/

/-- **Weak noise-score generator equality (ID-3), explicit-integrability version.**
For `D : ℝ`, a drift `b`, a differentiable everywhere-positive `p` and a test function `φ`
whose first partials `∂ᵢφ` are differentiable,

  `∫ (b ⬝ ∇φ + D Δφ) p = ∫ ((b - D ∇log p) ⬝ ∇φ) p`,

provided `(b ⬝ ∇φ) p`, and for every `i` the functions `∂ᵢ∂ᵢφ · p`, `∂ᵢφ · ∂ᵢp` and `∂ᵢφ · p`,
are Lebesgue integrable. These are the standard no-boundary-term integration-by-parts
hypotheses; they are discharged for compactly supported `C²` test functions in
`integral_generator_eq_score_flow_generator`. -/
theorem integral_generator_eq_score_flow_generator_of_integrable (D : ℝ)
    (b : (Fin d → ℝ) → Fin d → ℝ) {p φ : (Fin d → ℝ) → ℝ} (hp : Differentiable ℝ p)
    (hpos : ∀ x, 0 < p x) (hφ : ∀ i, Differentiable ℝ (partialDeriv i φ))
    (hb : Integrable (fun x => (b x ⬝ᵥ grad φ x) * p x))
    (h2 : ∀ i, Integrable (fun x => partialDeriv i (partialDeriv i φ) x * p x))
    (h1 : ∀ i, Integrable (fun x => partialDeriv i φ x * partialDeriv i p x))
    (h0 : ∀ i, Integrable (fun x => partialDeriv i φ x * p x)) :
    ∫ x, (b x ⬝ᵥ grad φ x + D * laplacian φ x) * p x =
      ∫ x, ((b x - D • score p x) ⬝ᵥ grad φ x) * p x := by
  have hL : (fun x => (b x ⬝ᵥ grad φ x + D * laplacian φ x) * p x) = fun x =>
      (b x ⬝ᵥ grad φ x) * p x + D * ∑ i, partialDeriv i (partialDeriv i φ) x * p x := by
    funext x
    simp only [laplacian, add_mul, Finset.sum_mul, mul_assoc]
  have hR : (fun x => ((b x - D • score p x) ⬝ᵥ grad φ x) * p x) = fun x =>
      (b x ⬝ᵥ grad φ x) * p x - D * ∑ i, partialDeriv i φ x * partialDeriv i p x :=
    funext fun x => transport_integrand_eq_smul (hp x) (hpos x)
  rw [hL, hR, integral_add hb ((integrable_finsetSum _ fun i _ => h2 i).const_mul D),
    integral_sub hb ((integrable_finsetSum _ fun i _ => h1 i).const_mul D),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => h2 i,
    integral_finsetSum _ fun i _ => h1 i, sub_eq_add_neg, ← mul_neg,
    ← Finset.sum_neg_distrib]
  congr 3
  funext i
  exact integral_partialDeriv_mul_eq_neg i (hφ i) hp (h2 i) (h1 i) (h0 i)

/-- **Constant-matrix weak generator identity, explicit-integrability version.**
For any matrix `A` (not necessarily symmetric), a drift `b`, a differentiable
everywhere-positive `p` and a test function `φ` whose first partials are differentiable,

  `∫ (b ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ ((b - Aᵀ ∇log p) ⬝ ∇φ) p`,

provided `(b ⬝ ∇φ) p` and, for all `i, j`, `∂ᵢ∂ⱼφ · p`, `∂ⱼφ · ∂ᵢp` and `∂ⱼφ · p` are
Lebesgue integrable. The transpose appears because the integration by parts moves `∂ᵢ` off
`∂ⱼφ` onto `p`; the symmetry of the Hessian of `φ` is not used. -/
theorem integral_weighted_generator_eq_transport_of_integrable
    (A : Matrix (Fin d) (Fin d) ℝ) (b : (Fin d → ℝ) → Fin d → ℝ)
    {p φ : (Fin d → ℝ) → ℝ} (hp : Differentiable ℝ p) (hpos : ∀ x, 0 < p x)
    (hφ : ∀ j, Differentiable ℝ (partialDeriv j φ))
    (hb : Integrable (fun x => (b x ⬝ᵥ grad φ x) * p x))
    (h2 : ∀ i j, Integrable (fun x => partialDeriv i (partialDeriv j φ) x * p x))
    (h1 : ∀ i j, Integrable (fun x => partialDeriv j φ x * partialDeriv i p x))
    (h0 : ∀ j, Integrable (fun x => partialDeriv j φ x * p x)) :
    ∫ x, (b x ⬝ᵥ grad φ x + weightedLaplacian A φ x) * p x =
      ∫ x, ((b x - Aᵀ *ᵥ score p x) ⬝ᵥ grad φ x) * p x := by
  have hL : (fun x => (b x ⬝ᵥ grad φ x + weightedLaplacian A φ x) * p x) = fun x =>
      (b x ⬝ᵥ grad φ x) * p x +
        ∑ i, ∑ j, A i j * (partialDeriv i (partialDeriv j φ) x * p x) := by
    funext x
    simp only [weightedLaplacian, add_mul, Finset.sum_mul, mul_assoc]
  have hR : (fun x => ((b x - Aᵀ *ᵥ score p x) ⬝ᵥ grad φ x) * p x) = fun x =>
      (b x ⬝ᵥ grad φ x) * p x -
        ∑ i, ∑ j, A i j * (partialDeriv j φ x * partialDeriv i p x) :=
    funext fun x => transport_integrand_eq (hp x) (hpos x)
  have i2 : ∀ i, Integrable
      (fun x => ∑ j, A i j * (partialDeriv i (partialDeriv j φ) x * p x)) := fun i =>
    integrable_finsetSum _ fun j _ => (h2 i j).const_mul (A i j)
  have i1 : ∀ i, Integrable
      (fun x => ∑ j, A i j * (partialDeriv j φ x * partialDeriv i p x)) := fun i =>
    integrable_finsetSum _ fun j _ => (h1 i j).const_mul (A i j)
  rw [hL, hR, integral_add hb (integrable_finsetSum _ fun i _ => i2 i),
    integral_sub hb (integrable_finsetSum _ fun i _ => i1 i),
    integral_finsetSum _ fun i _ => i2 i, integral_finsetSum _ fun i _ => i1 i,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (h2 i j).const_mul (A i j),
    integral_finsetSum _ fun j _ => (h1 i j).const_mul (A i j), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul,
    integral_partialDeriv_mul_eq_neg i (hφ j) hp (h2 i j) (h1 i j) (h0 j), mul_neg]

/-- **Preconditioned Langevin / PFG weak generator identity (ID-3), explicit-integrability
version.** For a symmetric matrix `A` (`Aᵀ = A`), a target score field `s⋆`, a differentiable
everywhere-positive `p` and a test function `φ` with differentiable first partials,

  `∫ ((A s⋆) ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ ((A (s⋆ - ∇log p)) ⬝ ∇φ) p`,

provided `((A s⋆) ⬝ ∇φ) p` and, for all `i, j`, `∂ᵢ∂ⱼφ · p`, `∂ⱼφ · ∂ᵢp` and `∂ⱼφ · p` are
integrable. See `integral_preconditioned_generator_eq_klFlow_generator` for the interpretation. -/
theorem integral_preconditioned_generator_eq_klFlow_generator_of_integrable
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (sStar : (Fin d → ℝ) → Fin d → ℝ)
    {p φ : (Fin d → ℝ) → ℝ} (hp : Differentiable ℝ p) (hpos : ∀ x, 0 < p x)
    (hφ : ∀ j, Differentiable ℝ (partialDeriv j φ))
    (hb : Integrable (fun x => ((A *ᵥ sStar x) ⬝ᵥ grad φ x) * p x))
    (h2 : ∀ i j, Integrable (fun x => partialDeriv i (partialDeriv j φ) x * p x))
    (h1 : ∀ i j, Integrable (fun x => partialDeriv j φ x * partialDeriv i p x))
    (h0 : ∀ j, Integrable (fun x => partialDeriv j φ x * p x)) :
    ∫ x, ((A *ᵥ sStar x) ⬝ᵥ grad φ x + weightedLaplacian A φ x) * p x =
      ∫ x, ((A *ᵥ (sStar x - score p x)) ⬝ᵥ grad φ x) * p x := by
  have h := integral_weighted_generator_eq_transport_of_integrable A
    (fun x => A *ᵥ sStar x) hp hpos hφ hb h2 h1 h0
  simpa only [mulVec_sub, hA] using h

/-! ### Discharging the hypotheses for compactly supported `C²` test functions -/

/-- If `f` is `Cⁿ` and `m + 1 ≤ n`, then each partial derivative `∂ⱼf` is `Cᵐ`. -/
theorem contDiff_partialDeriv {m n : WithTop ℕ∞} {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (j : Fin d) : ContDiff ℝ m (partialDeriv j f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- A continuous compactly supported function times a continuous function is integrable. -/
private theorem integrable_mul_of_hasCompactSupport {g p : (Fin d → ℝ) → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hp : Continuous p) :
    Integrable (fun x => g x * p x) :=
  (hg.mul hp).integrable_of_hasCompactSupport hgc.mul_right

/-- If `b` and `p` are continuous and `φ` is `C¹` with compact support, then
`x ↦ (b(x) ⬝ ∇φ(x)) p(x)` is Lebesgue integrable. -/
theorem integrable_drift_mul_of_hasCompactSupport {b : (Fin d → ℝ) → Fin d → ℝ}
    {p φ : (Fin d → ℝ) → ℝ} (hb : Continuous b) (hp : Continuous p) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) : Integrable (fun x => (b x ⬝ᵥ grad φ x) * p x) := by
  refine integrable_mul_of_hasCompactSupport ?_ ?_ hp
  · exact hb.dotProduct (continuous_pi fun i =>
      (contDiff_partialDeriv (m := 0) hφ (by norm_num) i).continuous)
  · refine hφc.mono' fun x hx => ?_
    by_contra h
    have h0 : grad φ x = 0 := by
      funext i
      simp [grad, partialDeriv, fderiv_of_notMem_tsupport ℝ h]
    exact hx (by simp [h0])

/-- **Constant-matrix weak generator identity (compactly supported test functions).**
For any matrix `A` (not necessarily symmetric), a continuous drift `b`, a `C¹`
everywhere-positive `p` and a `C²` compactly supported test function `φ`,

  `∫ (b ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ ((b - Aᵀ ∇log p) ⬝ ∇φ) p`. -/
theorem integral_weighted_generator_eq_transport (A : Matrix (Fin d) (Fin d) ℝ)
    {b : (Fin d → ℝ) → Fin d → ℝ} {p φ : (Fin d → ℝ) → ℝ} (hb : Continuous b)
    (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, (b x ⬝ᵥ grad φ x + weightedLaplacian A φ x) * p x =
      ∫ x, ((b x - Aᵀ *ᵥ score p x) ⬝ᵥ grad φ x) * p x := by
  have hφ1 : ∀ j, ContDiff ℝ 1 (partialDeriv j φ) := fun j =>
    contDiff_partialDeriv hφ (by norm_num) j
  have hφ1c : ∀ j, HasCompactSupport (partialDeriv j φ) := fun j =>
    hasCompactSupport_partialDeriv hφc j
  refine integral_weighted_generator_eq_transport_of_integrable A b
    (hp.differentiable one_ne_zero) hpos (fun j => (hφ1 j).differentiable one_ne_zero)
    (integrable_drift_mul_of_hasCompactSupport hb hp.continuous (hφ.of_le (by norm_num)) hφc)
    (fun i j => ?_) (fun i j => ?_) (fun j => ?_)
  · exact integrable_mul_of_hasCompactSupport
      (contDiff_partialDeriv (m := 0) (hφ1 j) (by norm_num) i).continuous
      (hasCompactSupport_partialDeriv (hφ1c j) i) hp.continuous
  · exact integrable_mul_of_hasCompactSupport (hφ1 j).continuous (hφ1c j)
      (contDiff_partialDeriv (m := 0) hp (by norm_num) i).continuous
  · exact integrable_mul_of_hasCompactSupport (hφ1 j).continuous (hφ1c j) hp.continuous

/-- **Weak noise-score generator equality (ID-3, headline).** Let `D : ℝ`, let
`b : ℝᵈ → ℝᵈ` be continuous, let `p` be `C¹` with `p(x) > 0` for every `x`, and let `φ` be
`C²` with compact support. Then

  `∫ (b ⬝ ∇φ + D Δφ) p dx = ∫ ((b - D ∇log p) ⬝ ∇φ) p dx`.

The left integrand is the generator of `dX = b(X) dt + √(2D) dW` applied to `φ`, the right one
the generator of the deterministic probability-flow transport `ẏ = b(y) - D ∇log p(y)`; when
`p` is a probability density both sides are expectations under `p`. This is a weak
(expectation-level) equality only: the integrands differ pointwise in general
(`generator_integrands_ne_at_zero`), and no statement about processes or laws is made. -/
theorem integral_generator_eq_score_flow_generator (D : ℝ)
    {b : (Fin d → ℝ) → Fin d → ℝ} {p φ : (Fin d → ℝ) → ℝ} (hb : Continuous b)
    (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, (b x ⬝ᵥ grad φ x + D * laplacian φ x) * p x =
      ∫ x, ((b x - D • score p x) ⬝ᵥ grad φ x) * p x := by
  have hφ1 : ∀ j, ContDiff ℝ 1 (partialDeriv j φ) := fun j =>
    contDiff_partialDeriv hφ (by norm_num) j
  have hφ1c : ∀ j, HasCompactSupport (partialDeriv j φ) := fun j =>
    hasCompactSupport_partialDeriv hφc j
  refine integral_generator_eq_score_flow_generator_of_integrable D b
    (hp.differentiable one_ne_zero) hpos (fun j => (hφ1 j).differentiable one_ne_zero)
    (integrable_drift_mul_of_hasCompactSupport hb hp.continuous (hφ.of_le (by norm_num)) hφc)
    (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · exact integrable_mul_of_hasCompactSupport
      (contDiff_partialDeriv (m := 0) (hφ1 i) (by norm_num) i).continuous
      (hasCompactSupport_partialDeriv (hφ1c i) i) hp.continuous
  · exact integrable_mul_of_hasCompactSupport (hφ1 i).continuous (hφ1c i)
      (contDiff_partialDeriv (m := 0) hp (by norm_num) i).continuous
  · exact integrable_mul_of_hasCompactSupport (hφ1 i).continuous (hφ1c i) hp.continuous

/-- **Preconditioned Langevin / PFG weak generator identity (ID-3), general `A`.**
For any constant matrix `A` (no symmetry assumed), a continuous target score field
`s⋆ : ℝᵈ → ℝᵈ`, a `C¹` everywhere-positive `p` and a `C²` compactly supported `φ`,

  `∫ ((A s⋆) ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ ((A s⋆ - Aᵀ ∇log p) ⬝ ∇φ) p`.

The transpose `Aᵀ` appears in the score term; for symmetric `A` see
`integral_preconditioned_generator_eq_klFlow_generator`. -/
theorem integral_preconditioned_generator_eq_klFlow_generator_transpose
    (A : Matrix (Fin d) (Fin d) ℝ) {sStar : (Fin d → ℝ) → Fin d → ℝ} {p φ : (Fin d → ℝ) → ℝ}
    (hsStar : Continuous sStar) (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, ((A *ᵥ sStar x) ⬝ᵥ grad φ x + weightedLaplacian A φ x) * p x =
      ∫ x, ((A *ᵥ sStar x - Aᵀ *ᵥ score p x) ⬝ᵥ grad φ x) * p x :=
  integral_weighted_generator_eq_transport A
    (continuous_const.matrix_mulVec hsStar) hp hpos hφ hφc

/-- **Preconditioned Langevin / PFG weak generator identity (ID-3).** Let `A` be a
symmetric constant matrix (`Aᵀ = A`), `s⋆ : ℝᵈ → ℝᵈ` a continuous target score field, `p` a
`C¹` function with `p(x) > 0` for every `x`, and `φ` a `C²` compactly supported test function.
Then

  `∫ ((A s⋆) ⬝ ∇φ + ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) p = ∫ ((A (s⋆ - ∇log p)) ⬝ ∇φ) p`.

The left integrand is the generator of the preconditioned Langevin diffusion
`dX = A s⋆(X) dt + √(2A) dW` applied to `φ` (the SDE needs `A` positive semidefinite; the
identity does not). The right integrand is the generator of the deterministic transport with
velocity `A (s⋆ - ∇log p)`, the ideal PFG direction when `A = H⁻¹`. Only the expectations under
`p` agree; nothing about solutions or laws of either dynamics is asserted. -/
theorem integral_preconditioned_generator_eq_klFlow_generator {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : Aᵀ = A) {sStar : (Fin d → ℝ) → Fin d → ℝ} {p φ : (Fin d → ℝ) → ℝ}
    (hsStar : Continuous sStar) (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, ((A *ᵥ sStar x) ⬝ᵥ grad φ x + weightedLaplacian A φ x) * p x =
      ∫ x, ((A *ᵥ (sStar x - score p x)) ⬝ᵥ grad φ x) * p x := by
  simpa only [mulVec_sub, hA] using
    integral_preconditioned_generator_eq_klFlow_generator_transpose A hsStar hp hpos hφ hφc

/-! ### One-dimensional corollary -/

section OneDim

/-- **One-dimensional weak generator equality, explicit-integrability version.** For `D : ℝ`,
`b : ℝ → ℝ`, a differentiable everywhere-positive `p` and `φ` with differentiable `φ'`,

  `∫ (b φ' + D φ'') p = ∫ ((b - D (log p)') φ') p`,

provided `b φ' p`, `φ'' p`, `φ' p'` and `φ' p` are Lebesgue integrable on `ℝ`. -/
theorem integral_generator_eq_score_flow_generator_one_dim_of_integrable (D : ℝ)
    {b p φ : ℝ → ℝ} (hp : Differentiable ℝ p) (hpos : ∀ x, 0 < p x)
    (hφ : Differentiable ℝ (deriv φ))
    (hb : Integrable (fun x => b x * deriv φ x * p x))
    (h2 : Integrable (fun x => deriv (deriv φ) x * p x))
    (h1 : Integrable (fun x => deriv φ x * deriv p x))
    (h0 : Integrable (fun x => deriv φ x * p x)) :
    ∫ x, (b x * deriv φ x + D * deriv (deriv φ) x) * p x =
      ∫ x, ((b x - D * score1 p x) * deriv φ x) * p x := by
  have hibp : ∫ x, p x * deriv (deriv φ) x = -∫ x, deriv p x * deriv φ x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => (hp x).hasDerivAt)
      (fun x _ => (hφ x).hasDerivAt) (by simpa [Pi.mul_def, mul_comm] using h2)
      (by simpa [Pi.mul_def, mul_comm] using h1) (by simpa [Pi.mul_def, mul_comm] using h0)
  have hL : (fun x => (b x * deriv φ x + D * deriv (deriv φ) x) * p x) = fun x =>
      b x * deriv φ x * p x + D * (p x * deriv (deriv φ) x) := by
    funext x
    ring
  have hR : (fun x => ((b x - D * score1 p x) * deriv φ x) * p x) = fun x =>
      b x * deriv φ x * p x - D * (deriv p x * deriv φ x) := by
    funext x
    rw [score1_of_pos (hp x) (hpos x)]
    field_simp [(hpos x).ne']
  rw [hL, hR, integral_add hb ((by simpa [mul_comm] using h2 :
      Integrable (fun x => p x * deriv (deriv φ) x)).const_mul D),
    integral_sub hb ((by simpa [mul_comm] using h1 :
      Integrable (fun x => deriv p x * deriv φ x)).const_mul D),
    integral_const_mul, integral_const_mul, hibp, mul_neg, sub_eq_add_neg]

/-- **One-dimensional weak noise-score generator equality (ID-3, readable form).** For
`D : ℝ`, a continuous drift `b : ℝ → ℝ`, a `C¹` function `p` with `p(x) > 0` for every `x`, and
a `C²` compactly supported test function `φ`,

  `∫ (b φ' + D φ'') p dx = ∫ ((b - D (log p)') φ') p dx`.

As in the `d`-dimensional theorem this is an equality of expectations, not of integrands. -/
theorem integral_generator_eq_score_flow_generator_one_dim (D : ℝ) {b p φ : ℝ → ℝ}
    (hb : Continuous b) (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, (b x * deriv φ x + D * deriv (deriv φ) x) * p x =
      ∫ x, ((b x - D * score1 p x) * deriv φ x) * p x := by
  have hφ1 : ContDiff ℝ 1 (deriv φ) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) φ from hφ)).2.2
  have hdc : HasCompactSupport (deriv φ) := hφc.deriv
  refine integral_generator_eq_score_flow_generator_one_dim_of_integrable D
    (hp.differentiable one_ne_zero) hpos (hφ1.differentiable one_ne_zero) ?_ ?_ ?_ ?_
  · exact ((hb.mul hφ1.continuous).mul hp.continuous).integrable_of_hasCompactSupport
      (hdc.mul_left.mul_right)
  · exact ((hφ1.continuous_deriv le_rfl).mul hp.continuous).integrable_of_hasCompactSupport
      hdc.deriv.mul_right
  · exact (hφ1.continuous.mul (hp.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hdc.mul_right
  · exact (hφ1.continuous.mul hp.continuous).integrable_of_hasCompactSupport hdc.mul_right

end OneDim

/-! ### The generators are not pointwise equal -/

section Counterexample

/-- A smooth bump on `ℝ` centred at `0`, equal to `1` on `[-1, 1]` and supported in
`(-2, 2)`. -/
noncomputable def unitBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The explicit test function `φ₀(x) = x² · β(x)`, with `β = unitBump`. It is smooth, has
compact support, and equals `x²` on `[-1, 1]`. -/
noncomputable def quadBump (x : ℝ) : ℝ := x ^ 2 * unitBump x

/-- `quadBump` is `Cⁿ` for every finite or infinite order `n : ℕ∞` (it is smooth). -/
theorem contDiff_quadBump {n : ℕ∞} : ContDiff ℝ n quadBump :=
  (contDiff_id.pow 2).mul unitBump.contDiff

/-- `quadBump` has compact support. -/
theorem hasCompactSupport_quadBump : HasCompactSupport quadBump :=
  unitBump.hasCompactSupport.mul_left

/-- Near `0`, `quadBump` coincides with `x ↦ x²`. -/
theorem quadBump_eventuallyEq : quadBump =ᶠ[nhds 0] fun x => x ^ 2 := by
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with x hx
  simp [quadBump, unitBump.one_of_mem_closedBall (by simpa [unitBump] using hx)]

/-- `quadBump''(0) = 2`. -/
theorem deriv_deriv_quadBump_zero : deriv (deriv quadBump) 0 = 2 := by
  rw [quadBump_eventuallyEq.deriv.deriv_eq]
  have : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    funext x
    simp
  rw [this]
  simp

/-- The state score of the standard Gaussian density (mean `0`, variance `1`) is
`(log p)'(x) = -x`. -/
theorem score1_gaussianPDFReal_std (x : ℝ) : score1 (gaussianPDFReal 0 1) x = -x := by
  have h : (fun y => Real.log (gaussianPDFReal 0 1 y)) =
      fun y => Real.log (Real.sqrt (2 * Real.pi))⁻¹ + -y ^ 2 / 2 := by
    funext y
    rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    simp
  unfold score1
  rw [h]
  simp
  ring

/-- The standard Gaussian density `gaussianPDFReal 0 1` is `C¹`. -/
theorem contDiff_gaussianPDFReal_std : ContDiff ℝ 1 (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- **The noise generator and the score-flow generator are not pointwise equal.** Take
`p = gaussianPDFReal 0 1` (standard Gaussian density), `b = 0`, `D = 1` and the compactly
supported smooth test function `φ₀ = quadBump`. At `x = 0` the diffusion integrand
`(0 · φ₀'(0) + 1 · φ₀''(0)) p(0) = 2 p(0)` is positive, while the transport integrand
`((0 - 1 · (log p)'(0)) φ₀'(0)) p(0)` vanishes because `(log p)'(0) = 0`. -/
theorem generator_integrands_ne_at_zero :
    (0 * deriv quadBump 0 + 1 * deriv (deriv quadBump) 0) * gaussianPDFReal 0 1 0 ≠
      ((0 - 1 * score1 (gaussianPDFReal 0 1) 0) * deriv quadBump 0) *
        gaussianPDFReal 0 1 0 := by
  rw [deriv_deriv_quadBump_zero, score1_gaussianPDFReal_std]
  have := gaussianPDFReal_pos 0 1 0 one_ne_zero
  simp only [neg_zero, mul_zero, sub_zero, zero_mul, zero_add, one_mul, ne_eq]
  positivity

/-- **Weak but not pointwise generator equality.** For `p = gaussianPDFReal 0 1`, `b = 0`,
`D = 1` and `φ₀ = quadBump` (smooth, compactly supported), the integrals of the diffusion
generator `1 · φ₀''` and of the score-flow generator `-(log p)' φ₀'` against `p` are equal
(instance of `integral_generator_eq_score_flow_generator_one_dim`), while the integrands
differ at `x = 0` (`generator_integrands_ne_at_zero`). -/
theorem weak_generator_eq_but_not_pointwise :
    (∫ x, (0 * deriv quadBump x + 1 * deriv (deriv quadBump) x) * gaussianPDFReal 0 1 x =
      ∫ x, ((0 - 1 * score1 (gaussianPDFReal 0 1) x) * deriv quadBump x) *
        gaussianPDFReal 0 1 x) ∧
    (0 * deriv quadBump 0 + 1 * deriv (deriv quadBump) 0) * gaussianPDFReal 0 1 0 ≠
      ((0 - 1 * score1 (gaussianPDFReal 0 1) 0) * deriv quadBump 0) *
        gaussianPDFReal 0 1 0 :=
  ⟨integral_generator_eq_score_flow_generator_one_dim 1 (b := fun _ => 0) continuous_const
    contDiff_gaussianPDFReal_std (fun x => gaussianPDFReal_pos 0 1 x one_ne_zero)
    (contDiff_quadBump (n := 2)) hasCompactSupport_quadBump, generator_integrands_ne_at_zero⟩

end Counterexample

end ScoreFlowWeak
end FormalizeSampling
