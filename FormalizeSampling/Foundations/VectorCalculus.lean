module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Coordinate vector calculus on `Fin d → ℝ`

Shared definitions for spatial derivatives, gradients, divergences, Laplacians and
state-space scores `∇ₓ log p`. The state space is the plain product space `Fin d → ℝ`
with Lebesgue measure `volume`; inner products are written with `dotProduct` (`⬝ᵥ`) and
matrices act by `Matrix.mulVec` (`*ᵥ`). Derivatives are Fréchet derivatives, so the choice
of (sup) norm on `Fin d → ℝ` does not affect them.

A *state score* `score p x = ∇ₓ log p(x)` is a spatial derivative of a density. It is not a
parameter score `∇θ log πθ`; nothing in this library differentiates with respect to model
parameters.

Status: **Verified** (definitions and elementary helper lemmas; no named hypotheses).

## Main results

* `score_apply_of_pos`, `score1_of_pos`, `score_mul_self_of_pos`: the score as `∇p / p`.
* `fderiv_apply_eq_grad_dotProduct`: `Dφ(z) w = ∇φ(z) ⬝ᵥ w`.
* `continuous_partialDeriv`, `hasCompactSupport_partialDeriv`, `continuous_score`,
  `measurable_score`: regularity of partial derivatives and scores.
* `score1_gaussianPDFReal`: the score of the Gaussian density `N(m, v)` is `-(x - m) / v`.
* `abs_dotProduct_le_norm`, `sq_norm_le_sum_sq`, `norm_sq_le_dotProduct_self`,
  `norm_le_of_abs_apply_single_le`: comparisons between the sup norm and Euclidean quantities.
* `KLTransport.integral_mul_partialDeriv_eq_neg`, `KLTransport.integral_partialDeriv_eq_zero`:
  integration by parts along a coordinate, `∫ f ∂ᵢg = -∫ ∂ᵢf g` and `∫ ∂ᵢf = 0` under
  integrability hypotheses.
-/

@[expose] public section

open Matrix

namespace FormalizeSampling

variable {d : ℕ}

/-- The `i`-th partial derivative `∂ᵢ f(x)`, defined as the Fréchet derivative of `f` at `x`
applied to the `i`-th standard basis vector. It is `0` where `f` is not differentiable. -/
noncomputable def partialDeriv (i : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The coordinate gradient `∇f(x) = (∂₁f(x), …, ∂_d f(x))`. -/
noncomputable def grad (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => partialDeriv i f x

/-- The divergence `div v(x) = ∑ᵢ ∂ᵢ vᵢ(x)` of a vector field `v`. -/
noncomputable def divergence (v : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, partialDeriv i (fun y => v y i) x

/-- The Laplacian `Δf(x) = ∑ᵢ ∂ᵢ∂ᵢ f(x)`. -/
noncomputable def laplacian (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, partialDeriv i (partialDeriv i f) x

/-- The matrix-weighted second-order term `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ f(x)`, i.e. `tr(A ∇²f(x))` when the
Hessian is symmetric. With `A = D • 1` it is `D * Δf(x)`. -/
noncomputable def weightedLaplacian (A : Matrix (Fin d) (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * partialDeriv i (partialDeriv j f) x

/-- The state-space score `∇ₓ log p(x)` of a (density) function `p`. Where `p` is positive and
differentiable it equals `∇p(x) / p(x)` (see `score_apply_of_pos`). -/
noncomputable def score (p : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  grad (fun y => Real.log (p y)) x

/-- The one-dimensional state score `(log p)'(x)`. -/
noncomputable def score1 (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun y => Real.log (p y)) x

/-- The squared `H`-weighted norm `‖u‖²_H = uᵀ H u`. It is a squared norm when `H` is
positive definite. -/
def sqNormH (H : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) : ℝ :=
  u ⬝ᵥ (H *ᵥ u)

/-- At a point where `p` is positive and differentiable, the `i`-th score coordinate is
`∂ᵢ p(x) / p(x)`. -/
theorem score_apply_of_pos {p : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hp : DifferentiableAt ℝ p x) (hpos : 0 < p x) (i : Fin d) :
    score p x i = partialDeriv i p x / p x := by
  have h : fderiv ℝ (fun y => Real.log (p y)) x = (p x)⁻¹ • fderiv ℝ p x :=
    (hp.hasFDerivAt.log hpos.ne').fderiv
  simp only [score, grad, partialDeriv, h, _root_.smul_apply, smul_eq_mul]
  rw [inv_mul_eq_div]

/-- At a point where `p` is positive and differentiable, `(log p)'(x) = p'(x) / p(x)`. -/
theorem score1_of_pos {p : ℝ → ℝ} {x : ℝ} (hp : DifferentiableAt ℝ p x) (hpos : 0 < p x) :
    score1 p x = deriv p x / p x := by
  unfold score1
  exact (hp.hasDerivAt.log hpos.ne').deriv

/-- Where `p` is differentiable and positive, `(∇log p)ᵢ(x) · p(x) = ∂ᵢp(x)`. -/
theorem score_mul_self_of_pos {p : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hp : DifferentiableAt ℝ p x) (hpos : 0 < p x) (i : Fin d) :
    score p x i * p x = partialDeriv i p x := by
  rw [score_apply_of_pos hp hpos i, div_mul_cancel₀ _ hpos.ne']

/-! ### Helper lemmas -/

/-- For any function `φ : (Fin d → ℝ) → ℝ` and points `z, w`, the Fréchet derivative of `φ`
at `z` applied to `w` is the coordinate formula `Dφ(z) w = ∇φ(z) ⬝ᵥ w`. (No differentiability
is needed: if `φ` is not differentiable at `z` both sides are `0`.) -/
theorem fderiv_apply_eq_grad_dotProduct (φ : (Fin d → ℝ) → ℝ) (z w : Fin d → ℝ) :
    fderiv ℝ φ z w = grad φ z ⬝ᵥ w := by
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, dotProduct, grad, partialDeriv, mul_comm]

/-- If `φ : (Fin d → ℝ) → ℝ` is `C¹`, then each partial derivative `∂ᵢ φ` is continuous. -/
theorem continuous_partialDeriv {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (i : Fin d) :
    Continuous (partialDeriv i φ) :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- If `φ : (Fin d → ℝ) → ℝ` has compact support, then so does each partial derivative
`∂ᵢ φ` (no differentiability assumption is needed: `partialDeriv` vanishes off `tsupport φ`). -/
theorem hasCompactSupport_partialDeriv {φ : (Fin d → ℝ) → ℝ} (hφc : HasCompactSupport φ)
    (i : Fin d) : HasCompactSupport (partialDeriv i φ) :=
  hφc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

/-- If `p` is `C¹` and everywhere positive, its state score `∇log p = ∇p / p` is continuous. -/
theorem continuous_score {p : (Fin d → ℝ) → ℝ} (hp : ContDiff ℝ 1 p) (hpos : ∀ x, 0 < p x) :
    Continuous (score p) :=
  continuous_pi fun i => continuous_partialDeriv (hp.log fun x => (hpos x).ne') i

/-- The state score `∇ log π` of **every** `π` is measurable (each partial derivative is a
measurable function, `measurable_fderiv_apply_const`). -/
theorem measurable_score (π : (Fin d → ℝ) → ℝ) : Measurable (score π) :=
  Measurable.of_eval fun i =>
    measurable_fderiv_apply_const ℝ (fun y => Real.log (π y)) (Pi.single i 1)

open scoped NNReal in
/-- **Gaussian score.** For `v ≠ 0` the state score of the Gaussian density
`gaussianPDFReal m v` is `y ↦ -(y - m) / v`. -/
theorem score1_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    score1 (ProbabilityTheory.gaussianPDFReal m v) y = -(y - m) / v := by
  have hv' : (0 : ℝ) < v := by positivity
  have hlog : (fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) =
      fun x => Real.log (Real.sqrt (2 * Real.pi * v))⁻¹ + -(x - m) ^ 2 / (2 * v) := by
    funext x
    rw [ProbabilityTheory.gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_exp]
  have hd : HasDerivAt
      (fun x => Real.log (Real.sqrt (2 * Real.pi * v))⁻¹ + -(x - m) ^ 2 / (2 * v))
      (-(y - m) / v) y := by
    have h1 := (((hasDerivAt_id' y).sub_const m).pow 2).neg.div_const (2 * (v : ℝ))
    refine (h1.const_add (Real.log (Real.sqrt (2 * Real.pi * v))⁻¹)).congr_deriv ?_
    field_simp
    ring
  rw [score1, hlog]
  exact hd.deriv

/-- `|u ⬝ᵥ w| ≤ d ‖u‖ ‖w‖` for the sup norm on `Fin d → ℝ`. -/
theorem abs_dotProduct_le_norm (u w : Fin d → ℝ) : |u ⬝ᵥ w| ≤ d * (‖u‖ * ‖w‖) := by
  calc |u ⬝ᵥ w| ≤ ∑ i, |u i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖u‖ * ‖w‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm w i) (norm_nonneg _)
          (norm_nonneg _)
    _ = d * (‖u‖ * ‖w‖) := by simp

/-- The sup norm on `Fin d → ℝ` is dominated by the Euclidean norm: `‖x‖² ≤ ∑ᵢ xᵢ²`. -/
theorem sq_norm_le_sum_sq (x : Fin d → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => x j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

/-- The squared sup norm is at most the squared Euclidean norm: `‖x‖² ≤ x ⬝ᵥ x`. -/
theorem norm_sq_le_dotProduct_self (x : Fin d → ℝ) : ‖x‖ ^ 2 ≤ x ⬝ᵥ x := by
  simpa [dotProduct, sq] using sq_norm_le_sum_sq x

/-- **Operator norm from coordinate values (Verified).** A continuous linear form `L` on
`Fin d → ℝ` (sup norm) with `|L eᵢ| ≤ G` for every standard basis vector `eᵢ` has
`‖L‖ ≤ d G`. -/
theorem norm_le_of_abs_apply_single_le (L : (Fin d → ℝ) →L[ℝ] ℝ) {G : ℝ} (hG : 0 ≤ G)
    (hL : ∀ i, |L (Pi.single i 1)| ≤ G) : ‖L‖ ≤ d * G := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have hsum : h = ∑ i, h i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum, map_sum, ← hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖L (h i • (Pi.single i (1 : ℝ) : Fin d → ℝ))‖ ≤ ∑ _i : Fin d, G * ‖h‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_smul, norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul (hL i) (norm_le_pi_norm h i) (abs_nonneg _) hG
    _ = d * G * ‖h‖ := by simp; ring

end FormalizeSampling

namespace FormalizeSampling.KLTransport

open MeasureTheory

variable {d : ℕ}

/-! ### Integration by parts along a coordinate direction -/

/-- **Integration by parts along a coordinate direction.** For `f g : (Fin d → ℝ) → ℝ`
differentiable everywhere, if `∂ᵢf · g`, `f · ∂ᵢg` and `f · g` are Lebesgue integrable, then
`∫ f ∂ᵢg = -∫ ∂ᵢf · g`. -/
theorem integral_mul_partialDeriv_eq_neg {f g : (Fin d → ℝ) → ℝ} (i : Fin d)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf'g : Integrable (fun x => partialDeriv i f x * g x))
    (hfg' : Integrable (fun x => f x * partialDeriv i g x))
    (hfg : Integrable (fun x => f x * g x)) :
    ∫ x, f x * partialDeriv i g x = -∫ x, partialDeriv i f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg (fun x _ => hf x)
    (fun x _ => hg x)

/-- **Vanishing boundary term.** If `f : (Fin d → ℝ) → ℝ` is differentiable everywhere and both
`f` and `∂ᵢf` are Lebesgue integrable, then `∫ ∂ᵢf = 0`. -/
theorem integral_partialDeriv_eq_zero {f : (Fin d → ℝ) → ℝ} (i : Fin d)
    (hf : Differentiable ℝ f) (hf_int : Integrable f)
    (hf'_int : Integrable (fun x => partialDeriv i f x)) :
    ∫ x, partialDeriv i f x = 0 := by
  have h := integral_mul_partialDeriv_eq_neg (g := fun _ => (1 : ℝ)) i hf
    (differentiable_const _) (by simpa using hf'_int)
    (by simp [partialDeriv]) (by simpa using hf_int)
  simpa [partialDeriv] using h.symm

end FormalizeSampling.KLTransport
