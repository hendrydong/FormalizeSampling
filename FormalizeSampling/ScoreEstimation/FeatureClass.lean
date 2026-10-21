module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Topology.Separation.CompletelyRegular
public import FormalizeSampling.Foundations.SPDPreconditioner

/-!
# Finite-feature SVGD as a special case of regularised functional descent

Registry ID: **SE-2** (finite-feature SVGD as a special case of regularised functional
descent; the PFG direction in a finite-feature linear class is the unique minimiser of the
weighted quadratic objective, unique on the support of the weighting measure).

## Setting and conventions

* State space `Fin d → ℝ`; `n` particles `y : Fin n → (Fin d → ℝ)`; a target state score
  `sStar : (Fin d → ℝ) → Fin d → ℝ` (in applications `sStar = ∇ log p⋆`, but nothing here
  uses that); a feature map `ψ : (Fin d → ℝ) → Fin m → ℝ`.
* Velocity class: `f_W x = W *ᵥ ψ x` for `W : Matrix (Fin d) (Fin m) ℝ`.
* Feature kernel: `featureKernel ψ y x = ψ y ⬝ᵥ ψ x`, i.e. `k(y, x) = ψ(y)ᵀψ(x)`.
* Matrices are paired by `frobInner A B = ∑ᵢ ∑ₖ Aᵢₖ Bᵢₖ`; the squared Frobenius norm is written
  out as the double sum `∑ᵢ ∑ₖ Wᵢₖ ^ 2`.
* Empirical averages are written `(1 / n) * ∑ j, …`. With Lean's convention `1 / 0 = 0`
  the case `n = 0` is degenerate but every statement below remains true for it, so no
  hypothesis `0 < n` is needed.
* Regularity is explicit: every statement about divergences or gradients of `f_W` assumes the
  coordinates `ψ · k` are differentiable at the points where they are evaluated (at the
  particles in the empirical part, `μ`-a.e. in the population part). Without this, Lean's
  `fderiv` would silently be `0`.

## Two different regularisers (the point of SE-2)

Both objectives share the empirical Stein (linear) term
`S(W) = (1/n) ∑ⱼ (div f_W (yⱼ) + f_W(yⱼ) ⬝ sStar(yⱼ))`.

* **SVGD / fixed feature (RKHS) norm.** `svgdFeatureObjective λ` adds `(λ/2) ‖W‖_F²`. This
  penalty does not depend on the particles. (When the coordinate functions `ψ · k` are
  linearly independent, `‖W‖_F` is the norm of `f_W` in the vector-valued RKHS of the kernel
  `k(y, x) = ψ(y)ᵀψ(x)`; that identification is *not* formalised here and is not used.)
  For `λ > 0` its unique minimiser is `svgdMatrix`, and `svgdMatrix *ᵥ ψ x` is the kernelised
  Stein (SVGD) direction `(1/(λ n)) ∑ⱼ (k(yⱼ, x) sStar(yⱼ) + ∇_y k(yⱼ, x))`.
* **PFG / distribution-weighted output norm.** `featureSteinObjective H` adds
  `(1/2) (1/n) ∑ⱼ ‖f_W(yⱼ)‖²_H`, a norm of the *output* of `f_W` weighted by the (empirical)
  particle distribution and the preconditioner `H`. For `H` positive (semi)definite its
  minimisers are exactly the solutions of the normal equations `H W Σψ = G`, where
  `Σψ = (1/n) ∑ⱼ ψ(yⱼ)ψ(yⱼ)ᵀ` and `G = steinFeatureMatrix = λ • svgdMatrix`. For `H`
  positive definite they are unique on the particles, and unique outright, equal to
  `H⁻¹ G Σψ⁻¹`, when `Σψ` is invertible.
* The two minimisers coincide, and the two objectives agree identically, when `Σψ = 1` and
  `H = λ • 1` (`featureSteinObjective_eq_svgdFeatureObjective`,
  `featureStein_isMinimiser_iff_eq_svgdMatrix`).

## Main results

* (a) `divergence_featureField`; the pointwise Stein integrand `steinIntegrand_eq`.
* Population versions against an arbitrary measure `μ` with explicit integrability
  hypotheses: `popSteinTerm_eq`, `integrable_mulVec_dotProduct_mulVec`,
  `integral_mulVec_dotProduct_mulVec`, `svgdPopObjective_isMinimiser_iff`,
  `svgdPopMatrix_mulVec_apply`, `popSteinObjective_add`, `popStein_isMinimiser_iff_normalEq`,
  `popSteinObjective_eq_iff_of_normalEq` (minimisers unique `μ`-a.e.),
  `popSteinObjective_eq_svgdPopObjective`.
* The empirical measure `empMeasure y = (1/n) ∑ⱼ δ_{yⱼ}` (`integral_empMeasure`,
  `integrable_empMeasure`, `ae_empMeasure_iff`): every empirical object is its population
  counterpart at `μ = empMeasure y` (`empiricalSteinTerm_eq_popSteinTerm`,
  `featureSteinObjective_eq_popSteinObjective`, `svgdFeatureObjective_eq_svgdPopObjective`,
  `featureCov_eq_popFeatureCov`, `steinFeatureMatrix_eq_popSteinMatrix`), and the empirical
  statements of (d), (e) are the population ones at the empirical measure.
* Linear term: `empiricalSteinTerm_eq` (`S(W) = ⟨W, G⟩_F`), `svgdMatrix_apply`,
  `smul_svgdMatrix` (`G = λ • Wsvgd`).
* (b) `svgdFeatureObjective_eq_completeSquare`, `svgdFeatureObjective_isMinimiser_iff`.
* (c) `svgdMatrix_mulVec`: the SVGD kernel form.
* (d), SE-2: `featureSteinObjective_add`,
  `featureSteinObjective_add_of_normalEq`, `featureSteinObjective_le_of_normalEq`,
  `featureStein_isMinimiser_iff_normalEq`, `featureSteinObjective_eq_iff_of_normalEq`,
  `featureStein_minimiser_agree_on_particles`, `normalEq_of_isUnit_det`,
  `featureStein_isMinimiser_iff_of_isUnit_det`.
* (e), SE-2: `featureSteinObjective_eq_svgdFeatureObjective`, `svgdMatrix_normalEq`,
  `featureStein_isMinimiser_iff_eq_svgdMatrix`.

## What is NOT proved here

* No general RKHS theory: the identification of `‖W‖_F` with an RKHS norm of `f_W`, and the
  infinite-dimensional SVGD direction as a minimiser over a full RKHS, are not formalised.
* No Stein identity / integration by parts: the population objectives are stated with the
  divergence form `-E_μ[div f + f ⬝ sStar]`; their relation to `E_μ[‖f - v⋆‖²_H]` with
  `v⋆ = H⁻¹ ∇ log (p⋆/p)` (SE-1 for the full `L²(p)` class) is not proved here (it is proved in
  `ScoreEstimation/SteinObjective.lean`, `featureField_isMinimiser_iff_projection`).
* No dynamics: nothing about particle updates, KL dissipation or convergence.
* Existence of a PFG minimiser when `Σψ` is singular is not claimed (the objective may then
  be unbounded below; this is not formalised). `featureStein_isMinimiser_iff_normalEq` only
  shows that a minimiser exists iff the normal equations are solvable.
* Only the simple sufficient coincidence condition `Σψ = 1`, `H = λ • 1` is proved (informally
  it forces `m ≤ n`, as `Σψ` has rank at most `n`; not formalised); no necessary condition is
  given.
* `sStar` is an arbitrary vector field: nothing here uses that it is a score `∇ log p⋆`.
* No relation between the empirical objects of random particles and the population objects of
  their law (law of large numbers, finite-particle error), and population SVGD is stated
  coordinatewise only (no vector-valued Bochner integral).
-/

@[expose] public section

open Matrix MeasureTheory

namespace FormalizeSampling.FeatureClass

variable {n d m : ℕ}

/-! ### Feature fields, kernel and divergence -/

/-- The feature kernel `k(y, x) = ψ(y) ⬝ ψ(x)` of a finite feature map
`ψ : (Fin d → ℝ) → Fin m → ℝ`. -/
def featureKernel (ψ : (Fin d → ℝ) → Fin m → ℝ) (y x : Fin d → ℝ) : ℝ :=
  ψ y ⬝ᵥ ψ x

/-- Partial derivatives commute with finite linear combinations of functions that are
differentiable at the point. -/
private theorem partialDeriv_sum_const_mul (i : Fin d) {x : Fin d → ℝ} (c : Fin m → ℝ)
    (g : Fin m → (Fin d → ℝ) → ℝ) (hg : ∀ k, DifferentiableAt ℝ (g k) x) :
    partialDeriv i (fun z => ∑ k, c k * g k z) x = ∑ k, c k * partialDeriv i (g k) x := by
  have h : HasFDerivAt (fun z => ∑ k, c k * g k z) (∑ k, c k • fderiv ℝ (g k) x) x :=
    HasFDerivAt.fun_sum (fun k _ => (hg k).hasFDerivAt.const_mul (c k))
  simp only [partialDeriv, h.fderiv, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- **(a) Divergence of a linear feature field.** If every feature coordinate `ψ · k` is
differentiable at `x`, then for `f_W(z) = W ψ(z)`,
`div f_W (x) = ∑ᵢ ∑ₖ Wᵢₖ ∂ᵢ ψₖ(x)`. -/
theorem divergence_featureField (W : Matrix (Fin d) (Fin m) ℝ)
    (ψ : (Fin d → ℝ) → Fin m → ℝ) (x : Fin d → ℝ)
    (hψ : ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x) :
    divergence (fun z => W *ᵥ ψ z) x =
      ∑ i, ∑ k, W i k * partialDeriv i (fun z => ψ z k) x := by
  unfold divergence
  refine Finset.sum_congr rfl fun i _ => ?_
  exact partialDeriv_sum_const_mul i (W i) (fun k z => ψ z k) hψ

/-- **Pointwise Stein integrand of a feature field.** If every `ψ · k` is differentiable at
`x`, then `div f_W (x) + f_W(x) ⬝ sStar(x) = ∑ᵢ ∑ₖ Wᵢₖ (sStarᵢ(x) ψₖ(x) + ∂ᵢ ψₖ(x))`,
i.e. the Stein integrand is linear in `W`. -/
theorem steinIntegrand_eq (W : Matrix (Fin d) (Fin m) ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) (x : Fin d → ℝ)
    (hψ : ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x) :
    divergence (fun z => W *ᵥ ψ z) x + (W *ᵥ ψ x) ⬝ᵥ sStar x =
      ∑ i, ∑ k, W i k * (sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) := by
  rw [divergence_featureField W ψ x hψ]
  simp only [dotProduct, mulVec, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Frobenius pairing and the ridge (fixed-norm) quadratic -/

/-- The Frobenius pairing `⟨A, B⟩_F = ∑ᵢ ∑ₖ Aᵢₖ Bᵢₖ` of two `d × m` real matrices. -/
def frobInner (A B : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ k, A i k * B i k

private theorem frobInner_add_left (A B C : Matrix (Fin d) (Fin m) ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp only [frobInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem frobInner_sub_right (A B C : Matrix (Fin d) (Fin m) ℝ) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  simp only [frobInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem frobInner_smul_left (c : ℝ) (A B : Matrix (Fin d) (Fin m) ℝ) :
    frobInner (c • A) B = c * frobInner A B := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem frobInner_zero_right (A : Matrix (Fin d) (Fin m) ℝ) :
    frobInner A 0 = 0 := by
  simp [frobInner]

private theorem frobInner_self (A : Matrix (Fin d) (Fin m) ℝ) :
    frobInner A A = ∑ i, ∑ k, A i k ^ 2 := by
  simp only [frobInner, sq]

private theorem sum_sum_sq_nonneg (A : Matrix (Fin d) (Fin m) ℝ) :
    0 ≤ ∑ i, ∑ k, A i k ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem eq_zero_of_sum_sum_sq_eq_zero (A : Matrix (Fin d) (Fin m) ℝ)
    (h : ∑ i, ∑ k, A i k ^ 2 = 0) : A = 0 := by
  ext i k
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg (A i k))).mp h i (Finset.mem_univ _)
  have hk := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => sq_nonneg (A i k))).mp hi k (Finset.mem_univ _)
  simpa using hk

/-- Completing the square for the ridge quadratic `-⟨W, G⟩_F + (λ/2)‖W‖_F²`. -/
private theorem ridge_completeSquare {lam : ℝ} (hlam : lam ≠ 0)
    (G W : Matrix (Fin d) (Fin m) ℝ) :
    -frobInner W G + lam / 2 * ∑ i, ∑ k, W i k ^ 2 =
      lam / 2 * ∑ i, ∑ k, (W i k - G i k / lam) ^ 2
        - lam / 2 * ∑ i, ∑ k, (G i k / lam) ^ 2 := by
  simp only [frobInner, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  field_simp
  ring

/-- For `λ > 0`, `W` minimises the ridge quadratic iff `W = G / λ` entrywise. -/
private theorem ridge_isMinimiser_iff {lam : ℝ} (hlam : 0 < lam)
    (G W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V : Matrix (Fin d) (Fin m) ℝ, -frobInner W G + lam / 2 * ∑ i, ∑ k, W i k ^ 2 ≤
        -frobInner V G + lam / 2 * ∑ i, ∑ k, V i k ^ 2) ↔
      W = fun i k => G i k / lam := by
  set W₀ : Matrix (Fin d) (Fin m) ℝ := fun i k => G i k / lam with hW₀
  have hsq : ∀ V : Matrix (Fin d) (Fin m) ℝ, -frobInner V G + lam / 2 * ∑ i, ∑ k, V i k ^ 2 =
      lam / 2 * ∑ i, ∑ k, (V - W₀) i k ^ 2 - lam / 2 * ∑ i, ∑ k, W₀ i k ^ 2 := fun V => by
    rw [ridge_completeSquare hlam.ne' G V]
    rfl
  constructor
  · intro h
    have h1 := h W₀
    rw [hsq, hsq, sub_self] at h1
    simp only [Matrix.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, zero_sub] at h1
    have h2 : ∑ i, ∑ k, (W - W₀) i k ^ 2 = 0 := by
      have := sum_sum_sq_nonneg (W - W₀)
      nlinarith
    exact sub_eq_zero.mp (eq_zero_of_sum_sum_sq_eq_zero _ h2)
  · rintro rfl V
    rw [hsq, hsq, sub_self]
    have := sum_sum_sq_nonneg (V - W₀)
    simp only [Matrix.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, zero_sub]
    nlinarith

/-- Abstract first-order characterisation used for both PFG objectives: if
`J (W + Δ) = J W + ⟨Δ, N⟩_F + q Δ` for all `Δ`, where `q ≥ 0` is quadratic
(`q (t Δ) = t² q Δ`), then `W` is a global minimiser of `J` iff `N = 0`. -/
private theorem isMinimiser_iff_of_expansion {J q : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {W N : Matrix (Fin d) (Fin m) ℝ}
    (hexp : ∀ Δ, J (W + Δ) = J W + frobInner Δ N + q Δ) (hq0 : ∀ Δ, 0 ≤ q Δ)
    (hqs : ∀ (t : ℝ) Δ, q (t • Δ) = t ^ 2 * q Δ) :
    (∀ V, J W ≤ J V) ↔ N = 0 := by
  constructor
  · intro hmin
    set a := frobInner N N with ha
    have ha0 : 0 ≤ a := by rw [ha, frobInner_self]; exact sum_sum_sq_nonneg N
    have hb0 : 0 ≤ q N := hq0 N
    have key : ∀ t : ℝ, 0 ≤ -(t * a) + t ^ 2 * q N := by
      intro t
      have h := hmin (W + (-t) • N)
      rw [hexp, frobInner_smul_left, hqs, neg_sq] at h
      linarith
    have ha' : a = 0 := by
      by_contra hne
      have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hne)
      have hab : 0 < a + q N := by linarith
      have h4 := key (a / (a + q N))
      have h3 : -(a / (a + q N) * a) + (a / (a + q N)) ^ 2 * q N =
          -(a ^ 3 / (a + q N) ^ 2) := by
        field_simp
        ring
      rw [h3] at h4
      have : 0 < a ^ 3 / (a + q N) ^ 2 := by positivity
      linarith
    rw [ha, frobInner_self] at ha'
    exact eq_zero_of_sum_sum_sq_eq_zero N ha'
  · intro hN V
    have h := hexp (V - W)
    rw [add_sub_cancel, hN, frobInner_zero_right] at h
    rw [h]
    linarith [hq0 (V - W)]

/-! ### Weighted output norms -/

private theorem sqNormH_add_of_isSymm {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm)
    (u v : Fin d → ℝ) :
    sqNormH H (u + v) = sqNormH H u + 2 * (v ⬝ᵥ (H *ᵥ u)) + sqNormH H v := by
  have h : u ⬝ᵥ (H *ᵥ v) = v ⬝ᵥ (H *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hH.eq, dotProduct_comm]
  simp only [sqNormH, mulVec_add, add_dotProduct, dotProduct_add, h]
  ring

private theorem sqNormH_nonneg' {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosSemidef)
    (u : Fin d → ℝ) : 0 ≤ sqNormH H u := by
  simpa [sqNormH] using hH.dotProduct_mulVec_nonneg u

private theorem isSymm_of_posSemidef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosSemidef) :
    H.IsSymm := by
  have h := hH.1
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- Pointwise trace identity: `(Δ v) ⬝ (M v) = ⟨Δ, M (v vᵀ)⟩_F`. -/
private theorem mulVec_dotProduct_mulVec (Δ M : Matrix (Fin d) (Fin m) ℝ) (v : Fin m → ℝ) :
    (Δ *ᵥ v) ⬝ᵥ (M *ᵥ v) = frobInner Δ (M * vecMulVec v v) := by
  simp only [frobInner, mulVec, dotProduct, mul_apply, vecMulVec_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### Population versions against a measure `μ`

The objectives against an arbitrary measure `μ` on the state space (typically a probability
measure `p`; no normalisation is needed for the algebra); the empirical objectives below are
the case `μ = empMeasure y`. Integrability is explicit: `hG` (the Stein integrands
`sStarᵢ ψₖ + ∂ᵢ ψₖ` are `μ`-integrable) and `hCov` (the products `ψₖ ψₗ` are
`μ`-integrable); differentiability of the features is assumed `μ`-a.e. -/

/-- The population Stein matrix `G_μ,ᵢₖ = ∫ (sStarᵢ(x) ψₖ(x) + ∂ᵢ ψₖ(x)) dμ(x)`. -/
noncomputable def popSteinMatrix (μ : Measure (Fin d → ℝ))
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  fun i k => ∫ x, (sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) ∂μ

/-- The population feature second-moment matrix `Σ_μ,ₖₗ = ∫ ψₖ(x) ψₗ(x) dμ(x)`. -/
noncomputable def popFeatureCov (μ : Measure (Fin d → ℝ)) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun k l => ∫ x, ψ x k * ψ x l ∂μ

/-- The population Stein term `∫ (div f_W + f_W ⬝ sStar) dμ` of `f_W(x) = W ψ(x)`. -/
noncomputable def popSteinTerm (μ : Measure (Fin d → ℝ))
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∫ x, (divergence (fun z => W *ᵥ ψ z) x + (W *ᵥ ψ x) ⬝ᵥ sStar x) ∂μ

/-- **Population SVGD objective (fixed feature norm)**:
`-∫ (div f_W + f_W ⬝ sStar) dμ + (λ/2) ∑ᵢ ∑ₖ Wᵢₖ²`. -/
noncomputable def svgdPopObjective (lam : ℝ) (μ : Measure (Fin d → ℝ))
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  -popSteinTerm μ sStar ψ W + lam / 2 * ∑ i, ∑ k, W i k ^ 2

/-- The population SVGD coefficient matrix `G_μ / λ`. -/
noncomputable def svgdPopMatrix (lam : ℝ) (μ : Measure (Fin d → ℝ))
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  fun i k => popSteinMatrix μ sStar ψ i k / lam

/-- **Population PFG objective (`μ`-weighted output norm)**:
`-∫ (div f_W + f_W ⬝ sStar) dμ + (1/2) ∫ ‖f_W‖²_H dμ`. -/
noncomputable def popSteinObjective (H : Matrix (Fin d) (Fin d) ℝ) (μ : Measure (Fin d → ℝ))
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  -popSteinTerm μ sStar ψ W + 1 / 2 * ∫ x, sqNormH H (W *ᵥ ψ x) ∂μ

/-- **Population linear term.** If the features are differentiable `μ`-a.e. and every Stein
integrand `sStarᵢ ψₖ + ∂ᵢ ψₖ` is `μ`-integrable, then `∫ (div f_W + f_W ⬝ sStar) dμ =
⟨W, G_μ⟩_F`. -/
theorem popSteinTerm_eq {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    popSteinTerm μ sStar ψ W = frobInner W (popSteinMatrix μ sStar ψ) := by
  rw [popSteinTerm, integral_congr_ae (hψ.mono fun x hx => steinIntegrand_eq W sStar ψ x hx),
    integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun k _ => (hG i k).const_mul (W i k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => (hG i k).const_mul (W i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  rfl

private theorem mulVec_dotProduct_mulVec_eq_sum (Δ M : Matrix (Fin d) (Fin m) ℝ)
    (v : Fin m → ℝ) :
    (Δ *ᵥ v) ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ k, Δ i k * ∑ l, M i l * (v l * v k) := by
  rw [mulVec_dotProduct_mulVec]
  simp only [frobInner, mul_apply, vecMulVec_apply]

/-- If every product `ψₖ ψₗ` is `μ`-integrable, then so is `x ↦ (Δ ψ(x)) ⬝ (M ψ(x))`. -/
theorem integrable_mulVec_dotProduct_mulVec {μ : Measure (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → Fin m → ℝ} (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (Δ M : Matrix (Fin d) (Fin m) ℝ) :
    Integrable (fun x => (Δ *ᵥ ψ x) ⬝ᵥ (M *ᵥ ψ x)) μ := by
  simp only [mulVec_dotProduct_mulVec_eq_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    (integrable_finsetSum _ fun l _ => (hCov l k).const_mul (M i l)).const_mul (Δ i k)

/-- **Population trace identity.** If every product `ψₖ ψₗ` is `μ`-integrable, then
`∫ (Δ ψ) ⬝ (M ψ) dμ = ⟨Δ, M Σ_μ⟩_F`. -/
theorem integral_mulVec_dotProduct_mulVec {μ : Measure (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → Fin m → ℝ} (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (Δ M : Matrix (Fin d) (Fin m) ℝ) :
    ∫ x, (Δ *ᵥ ψ x) ⬝ᵥ (M *ᵥ ψ x) ∂μ = frobInner Δ (M * popFeatureCov μ ψ) := by
  simp only [mulVec_dotProduct_mulVec_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    (integrable_finsetSum _ fun l _ => (hCov l k).const_mul (M i l)).const_mul (Δ i k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ =>
    (integrable_finsetSum _ fun l _ => (hCov l k).const_mul (M i l)).const_mul (Δ i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun l _ => (hCov l k).const_mul (M i l)]
  simp only [integral_const_mul, mul_apply, popFeatureCov]

private theorem integrable_sqNormH {μ : Measure (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → Fin m → ℝ} (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (H : Matrix (Fin d) (Fin d) ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Integrable (fun x => sqNormH H (A *ᵥ ψ x)) μ := by
  simpa only [sqNormH, mulVec_mulVec] using integrable_mulVec_dotProduct_mulVec hCov A (H * A)

/-- **Population SVGD: unique minimiser.** For `λ > 0`, features differentiable `μ`-a.e. and
integrable Stein integrands, `W` minimises the population SVGD objective iff
`W = G_μ / λ`. -/
theorem svgdPopObjective_isMinimiser_iff {lam : ℝ} (hlam : 0 < lam)
    {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V, svgdPopObjective lam μ sStar ψ W ≤ svgdPopObjective lam μ sStar ψ V) ↔
      W = svgdPopMatrix lam μ sStar ψ := by
  simp only [svgdPopObjective, popSteinTerm_eq sStar ψ hψ hG]
  exact ridge_isMinimiser_iff hlam _ W

/-- **Population SVGD kernel form (coordinatewise).** If the features are differentiable
`μ`-a.e. and the Stein integrands are `μ`-integrable, then for every `x` and coordinate `i`,
`(W_μ ψ(x))ᵢ = (1/λ) ∫ (k(y, x) sStarᵢ(y) + (∇_y k(y, x))ᵢ) dμ(y)` with
`k(y, x) = ψ(y) ⬝ ψ(x)` and `W_μ = G_μ / λ`. -/
theorem svgdPopMatrix_mulVec_apply (lam : ℝ) {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (x : Fin d → ℝ) (i : Fin d) :
    (svgdPopMatrix lam μ sStar ψ *ᵥ ψ x) i = (1 / lam) *
      ∫ y, (featureKernel ψ y x * sStar y i + grad (fun z => featureKernel ψ z x) y i) ∂μ := by
  have hae : (fun y => featureKernel ψ y x * sStar y i +
      grad (fun z => featureKernel ψ z x) y i) =ᵐ[μ]
      fun y => ∑ k, (sStar y i * ψ y k + partialDeriv i (fun z => ψ z k) y) * ψ x k := by
    filter_upwards [hψ] with y hy
    have hfun : (fun z => featureKernel ψ z x) = fun z => ∑ k, ψ x k * ψ z k := by
      funext z
      simp only [featureKernel, dotProduct, mul_comm]
    rw [grad, hfun, partialDeriv_sum_const_mul i (ψ x) (fun k z => ψ z k) hy]
    simp only [featureKernel, dotProduct, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [integral_congr_ae hae, integral_finsetSum _ fun k _ => (hG i k).mul_const (ψ x k)]
  simp only [mulVec, dotProduct, svgdPopMatrix, popSteinMatrix, integral_mul_const,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Exact expansion of the population PFG objective.** For a symmetric `H`, features
differentiable `μ`-a.e., integrable Stein integrands and integrable feature products,
`J_μ(W + Δ) = J_μ(W) + ⟨Δ, H W Σ_μ - G_μ⟩_F + (1/2) ∫ ‖Δ ψ‖²_H dμ`. -/
theorem popSteinObjective_add {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm)
    {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (W Δ : Matrix (Fin d) (Fin m) ℝ) :
    popSteinObjective H μ sStar ψ (W + Δ) = popSteinObjective H μ sStar ψ W
      + frobInner Δ (H * W * popFeatureCov μ ψ - popSteinMatrix μ sStar ψ)
      + 1 / 2 * ∫ x, sqNormH H (Δ *ᵥ ψ x) ∂μ := by
  have hpt : (fun x => sqNormH H ((W + Δ) *ᵥ ψ x)) = fun x => sqNormH H (W *ᵥ ψ x)
      + 2 * ((Δ *ᵥ ψ x) ⬝ᵥ ((H * W) *ᵥ ψ x)) + sqNormH H (Δ *ᵥ ψ x) := by
    funext x
    rw [add_mulVec, sqNormH_add_of_isSymm hH, mulVec_mulVec]
  have hcross := (integrable_mulVec_dotProduct_mulVec hCov Δ (H * W)).const_mul 2
  have hq : ∫ x, sqNormH H ((W + Δ) *ᵥ ψ x) ∂μ = ∫ x, sqNormH H (W *ᵥ ψ x) ∂μ
      + 2 * frobInner Δ (H * W * popFeatureCov μ ψ) + ∫ x, sqNormH H (Δ *ᵥ ψ x) ∂μ := by
    have h1 : Integrable (fun x => sqNormH H (W *ᵥ ψ x)
        + 2 * ((Δ *ᵥ ψ x) ⬝ᵥ ((H * W) *ᵥ ψ x))) μ :=
      (integrable_sqNormH hCov H W).add hcross
    rw [hpt, integral_add h1 (integrable_sqNormH hCov H Δ),
      integral_add (integrable_sqNormH hCov H W) hcross, integral_const_mul,
      integral_mulVec_dotProduct_mulVec hCov]
  rw [popSteinObjective, popSteinObjective, hq, popSteinTerm_eq sStar ψ hψ hG,
    popSteinTerm_eq sStar ψ hψ hG, frobInner_add_left, frobInner_sub_right]
  ring

private theorem half_integral_sqNormH_nonneg {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef) (μ : Measure (Fin d → ℝ)) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (Δ : Matrix (Fin d) (Fin m) ℝ) :
    0 ≤ 1 / 2 * ∫ x, sqNormH H (Δ *ᵥ ψ x) ∂μ := by
  have : 0 ≤ ∫ x, sqNormH H (Δ *ᵥ ψ x) ∂μ := integral_nonneg fun x => sqNormH_nonneg' hH _
  positivity

/-- **Population PFG: minimisers are exactly the solutions of the normal equations.** For
`H` positive semidefinite, features differentiable `μ`-a.e., integrable Stein integrands and
integrable feature products, `W` minimises the population PFG objective iff
`H W Σ_μ = G_μ`. -/
theorem popStein_isMinimiser_iff_normalEq {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef) {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V, popSteinObjective H μ sStar ψ W ≤ popSteinObjective H μ sStar ψ V) ↔
      H * W * popFeatureCov μ ψ = popSteinMatrix μ sStar ψ := by
  rw [isMinimiser_iff_of_expansion (popSteinObjective_add (isSymm_of_posSemidef hH)
    sStar ψ hψ hG hCov W) (half_integral_sqNormH_nonneg hH μ ψ) (fun t Δ => ?_), sub_eq_zero]
  simp only [smul_mulVec, SPD.sqNormH_smul, integral_const_mul]
  ring

/-- **Population PFG (SE-2, population form): `μ`-a.e. uniqueness.** Let `H` be
positive definite, the features differentiable `μ`-a.e., the Stein integrands and feature
products `μ`-integrable, and `H W Σ_μ = G_μ`. Then for every `V`,
`J_μ(V) = J_μ(W)` iff `V ψ(x) = W ψ(x)` for `μ`-a.e. `x`: the minimising velocity field in
the class `{x ↦ W ψ(x)}` is unique `μ`-almost everywhere. -/
theorem popSteinObjective_eq_iff_of_normalEq {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    {W : Matrix (Fin d) (Fin m) ℝ}
    (hW : H * W * popFeatureCov μ ψ = popSteinMatrix μ sStar ψ)
    (V : Matrix (Fin d) (Fin m) ℝ) :
    popSteinObjective H μ sStar ψ V = popSteinObjective H μ sStar ψ W ↔
      ∀ᵐ x ∂μ, V *ᵥ ψ x = W *ᵥ ψ x := by
  have h := popSteinObjective_add (isSymm_of_posSemidef hH.posSemidef) sStar ψ hψ hG hCov W
    (V - W)
  rw [add_sub_cancel, hW, sub_self, frobInner_zero_right, add_zero] at h
  rw [h, add_eq_left, mul_eq_zero, or_iff_right (by norm_num),
    integral_eq_zero_iff_of_nonneg (fun x => sqNormH_nonneg' hH.posSemidef _)
      (integrable_sqNormH hCov H (V - W))]
  constructor
  · intro h0
    filter_upwards [h0] with x hx
    rw [Pi.zero_apply, SPD.sqNormH_eq_zero_iff hH, sub_mulVec, sub_eq_zero] at hx
    exact hx
  · intro h0
    filter_upwards [h0] with x hx
    rw [Pi.zero_apply, SPD.sqNormH_eq_zero_iff hH, sub_mulVec, sub_eq_zero]
    exact hx

/-- **Population form of (e).** If every product `ψₖ ψₗ` is `μ`-integrable, `Σ_μ = 1` and
`H = λ • 1`, then the population PFG and SVGD objectives agree for every `W`. -/
theorem popSteinObjective_eq_svgdPopObjective {lam : ℝ} {H : Matrix (Fin d) (Fin d) ℝ}
    {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (hCovOne : popFeatureCov μ ψ = 1) (hH : H = lam • 1) (W : Matrix (Fin d) (Fin m) ℝ) :
    popSteinObjective H μ sStar ψ W = svgdPopObjective lam μ sStar ψ W := by
  have hq : ∫ x, sqNormH H (W *ᵥ ψ x) ∂μ = lam * ∑ i, ∑ k, W i k ^ 2 := by
    simp only [sqNormH, mulVec_mulVec]
    rw [integral_mulVec_dotProduct_mulVec hCov, hCovOne, hH, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul, frobInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [popSteinObjective, svgdPopObjective, hq]
  ring

/-! ### Empirical objects -/

/-- The empirical Stein (linear-term) matrix
`Gᵢₖ = (1/n) ∑ⱼ (sStarᵢ(yⱼ) ψₖ(yⱼ) + ∂ᵢ ψₖ(yⱼ))`, the matrix `G` of the normal equations;
`G = λ • svgdMatrix λ` for `λ ≠ 0` (`smul_svgdMatrix`). -/
noncomputable def steinFeatureMatrix (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  fun i k => (1 / (n : ℝ)) *
    ∑ j, (sStar (y j) i * ψ (y j) k + partialDeriv i (fun z => ψ z k) (y j))

/-- The finite-feature SVGD coefficient matrix
`Wsvgdᵢₖ = (1/(λ n)) ∑ⱼ (sStarᵢ(yⱼ) ψₖ(yⱼ) + ∂ᵢ ψₖ(yⱼ))`. -/
noncomputable def svgdMatrix (lam : ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  fun i k => 1 / (lam * n) *
    ∑ j, (sStar (y j) i * ψ (y j) k + partialDeriv i (fun z => ψ z k) (y j))

/-- The empirical feature second-moment matrix `Σψ = (1/n) ∑ⱼ ψ(yⱼ) ψ(yⱼ)ᵀ`. -/
noncomputable def featureCov (y : Fin n → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 / (n : ℝ)) • ∑ j, vecMulVec (ψ (y j)) (ψ (y j))

/-- The empirical Stein term `(1/n) ∑ⱼ (div f_W (yⱼ) + f_W(yⱼ) ⬝ sStar(yⱼ))` of the feature
field `f_W(x) = W ψ(x)`. -/
noncomputable def empiricalSteinTerm (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ j, (divergence (fun x => W *ᵥ ψ x) (y j) + (W *ᵥ ψ (y j)) ⬝ᵥ sStar (y j))

/-- **Empirical SVGD objective with the fixed feature (RKHS) norm**:
`Jsvgd(W) = -(1/n) ∑ⱼ (div f_W (yⱼ) + f_W(yⱼ) ⬝ sStar(yⱼ)) + (λ/2) ∑ᵢ ∑ₖ Wᵢₖ²`.
The regulariser `(λ/2)‖W‖_F²` is a fixed norm on the coefficients, independent of the
particle distribution. -/
noncomputable def svgdFeatureObjective (lam : ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  -empiricalSteinTerm y sStar ψ W + lam / 2 * ∑ i, ∑ k, W i k ^ 2

/-- **Empirical PFG objective with the distribution-weighted output norm**:
`Jstein(W) = -(1/n) ∑ⱼ (div f_W (yⱼ) + f_W(yⱼ) ⬝ sStar(yⱼ)) + (1/2) (1/n) ∑ⱼ ‖f_W(yⱼ)‖²_H`.
The regulariser penalises the output `f_W(yⱼ)` in the `H`-norm, averaged over the particles,
so it depends on the particle distribution. -/
noncomputable def featureSteinObjective (H : Matrix (Fin d) (Fin d) ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  -empiricalSteinTerm y sStar ψ W + 1 / 2 * ((1 / (n : ℝ)) * ∑ j, sqNormH H (W *ᵥ ψ (y j)))

/-- The empirical measure `(1/n) ∑ⱼ δ_{yⱼ}` of the particles (zero when `n = 0`). -/
noncomputable def empMeasure (y : Fin n → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ((n : ENNReal)⁻¹) • ∑ j, Measure.dirac (y j)

/-- Integration against the empirical measure is the particle average:
`∫ f d(empMeasure y) = (1/n) ∑ⱼ f(yⱼ)`. -/
theorem integral_empMeasure (y : Fin n → Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) :
    ∫ x, f x ∂(empMeasure y) = (1 / (n : ℝ)) * ∑ j, f (y j) := by
  rw [empMeasure, integral_smul_measure, integral_finsetSum_measure
    (fun j _ => integrable_dirac enorm_lt_top)]
  simp [integral_dirac, ENNReal.toReal_inv]

/-- Every function is integrable against the empirical measure. -/
theorem integrable_empMeasure (y : Fin n → Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) :
    Integrable f (empMeasure y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empMeasure]
  exact (integrable_finsetSum_measure.2 fun j _ => integrable_dirac enorm_lt_top).smul_measure
    (by simp [hn.ne'])

/-- A property holds almost everywhere for the empirical measure iff it holds at every
particle. -/
theorem ae_empMeasure_iff (y : Fin n → Fin d → ℝ) {P : (Fin d → ℝ) → Prop} :
    (∀ᵐ x ∂(empMeasure y), P x) ↔ ∀ j, P (y j) := by
  rw [ae_iff, empMeasure, Measure.smul_apply, smul_eq_mul, mul_eq_zero,
    Measure.coe_finsetSum, Finset.sum_apply]
  simp [Measure.dirac_apply]

/-- The empirical Stein term is the population Stein term at the empirical measure. -/
theorem empiricalSteinTerm_eq_popSteinTerm (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    empiricalSteinTerm y sStar ψ W = popSteinTerm (empMeasure y) sStar ψ W := by
  rw [popSteinTerm, integral_empMeasure, empiricalSteinTerm]

/-- The empirical PFG objective is the population PFG objective at the empirical measure. -/
theorem featureSteinObjective_eq_popSteinObjective (H : Matrix (Fin d) (Fin d) ℝ)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    featureSteinObjective H y sStar ψ W = popSteinObjective H (empMeasure y) sStar ψ W := by
  rw [featureSteinObjective, popSteinObjective, empiricalSteinTerm_eq_popSteinTerm,
    integral_empMeasure]

/-- The empirical SVGD objective is the population SVGD objective at the empirical measure. -/
theorem svgdFeatureObjective_eq_svgdPopObjective (lam : ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    svgdFeatureObjective lam y sStar ψ W = svgdPopObjective lam (empMeasure y) sStar ψ W := by
  rw [svgdFeatureObjective, svgdPopObjective, empiricalSteinTerm_eq_popSteinTerm]

/-- The empirical feature second-moment matrix is `Σ_μ` at the empirical measure. -/
theorem featureCov_eq_popFeatureCov (y : Fin n → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    featureCov y ψ = popFeatureCov (empMeasure y) ψ := by
  ext k l
  simp [featureCov, popFeatureCov, integral_empMeasure, Matrix.sum_apply, vecMulVec_apply]

/-- The empirical Stein matrix is `G_μ` at the empirical measure. -/
theorem steinFeatureMatrix_eq_popSteinMatrix (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    steinFeatureMatrix y sStar ψ = popSteinMatrix (empMeasure y) sStar ψ := by
  ext i k
  simp [steinFeatureMatrix, popSteinMatrix, integral_empMeasure]

/-- **Linear term as a Frobenius pairing.** If every `ψ · k` is differentiable at every
particle, the empirical Stein term equals `⟨W, G⟩_F` with `G = steinFeatureMatrix`
(`popSteinTerm_eq` at the empirical measure). -/
theorem empiricalSteinTerm_eq (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    (W : Matrix (Fin d) (Fin m) ℝ) :
    empiricalSteinTerm y sStar ψ W = frobInner W (steinFeatureMatrix y sStar ψ) := by
  rw [empiricalSteinTerm_eq_popSteinTerm, steinFeatureMatrix_eq_popSteinMatrix]
  exact popSteinTerm_eq sStar ψ ((ae_empMeasure_iff y).2 hψ)
    (fun _ _ => integrable_empMeasure _ _) W

/-- Entrywise, `Wsvgdᵢₖ = Gᵢₖ / λ` (for every `λ`, with Lean's `x / 0 = 0`). -/
theorem svgdMatrix_apply (lam : ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) (i : Fin d) (k : Fin m) :
    svgdMatrix lam y sStar ψ i k = steinFeatureMatrix y sStar ψ i k / lam := by
  simp only [svgdMatrix, steinFeatureMatrix]
  rw [mul_comm lam, ← div_div, div_eq_mul_one_div _ lam]
  ring

/-- For `λ ≠ 0`, the linear-term matrix is `G = λ • Wsvgd`. -/
theorem smul_svgdMatrix {lam : ℝ} (hlam : lam ≠ 0) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ) :
    lam • svgdMatrix lam y sStar ψ = steinFeatureMatrix y sStar ψ := by
  ext i k
  rw [Matrix.smul_apply, svgdMatrix_apply, smul_eq_mul]
  field_simp

/-! ### (b), (c): the SVGD objective and the kernelised Stein direction -/

/-- **(b) Completing the square for the SVGD objective.** For `λ ≠ 0` and features
differentiable at every particle,
`Jsvgd(W) = (λ/2) ∑ᵢ ∑ₖ (Wᵢₖ - Wsvgdᵢₖ)² - (λ/2) ∑ᵢ ∑ₖ Wsvgdᵢₖ²`. -/
theorem svgdFeatureObjective_eq_completeSquare {lam : ℝ} (hlam : lam ≠ 0)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    (W : Matrix (Fin d) (Fin m) ℝ) :
    svgdFeatureObjective lam y sStar ψ W =
      lam / 2 * ∑ i, ∑ k, (W i k - svgdMatrix lam y sStar ψ i k) ^ 2
        - lam / 2 * ∑ i, ∑ k, svgdMatrix lam y sStar ψ i k ^ 2 := by
  rw [svgdFeatureObjective, empiricalSteinTerm_eq y sStar ψ hψ W,
    ridge_completeSquare hlam]
  simp only [svgdMatrix_apply]

/-- **(b) The SVGD coefficient matrix is the unique minimiser.** For `λ > 0` and features
differentiable at every particle, `W` minimises `Jsvgd` over all `d × m` matrices iff
`W = Wsvgd`. -/
theorem svgdFeatureObjective_isMinimiser_iff {lam : ℝ} (hlam : 0 < lam)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V, svgdFeatureObjective lam y sStar ψ W ≤ svgdFeatureObjective lam y sStar ψ V) ↔
      W = svgdMatrix lam y sStar ψ := by
  have hW : svgdMatrix lam y sStar ψ = fun i k => steinFeatureMatrix y sStar ψ i k / lam := by
    ext i k
    exact svgdMatrix_apply lam y sStar ψ i k
  simp only [svgdFeatureObjective, empiricalSteinTerm_eq y sStar ψ hψ, hW]
  exact ridge_isMinimiser_iff hlam _ W

/-- **(c) SVGD kernel form.** If every `ψ · k` is differentiable at every particle, then for
every `x`,
`Wsvgd ψ(x) = (1/(λ n)) ∑ⱼ (k(yⱼ, x) sStar(yⱼ) + ∇_y k(yⱼ, x))` with
`k(y, x) = ψ(y) ⬝ ψ(x)`: the minimiser of the fixed-norm objective is the kernelised Stein
(SVGD) direction. -/
theorem svgdMatrix_mulVec (lam : ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j)) (x : Fin d → ℝ) :
    svgdMatrix lam y sStar ψ *ᵥ ψ x = (1 / (lam * n)) •
      ∑ j, (featureKernel ψ (y j) x • sStar (y j) +
        grad (fun z => featureKernel ψ z x) (y j)) := by
  have hg : ∀ j i, grad (fun z => featureKernel ψ z x) (y j) i =
      ∑ k, ψ x k * partialDeriv i (fun z => ψ z k) (y j) := by
    intro j i
    have : (fun z => featureKernel ψ z x) = fun z => ∑ k, ψ x k * ψ z k := by
      funext z
      simp only [featureKernel, dotProduct, mul_comm]
    rw [grad, this]
    exact partialDeriv_sum_const_mul i (ψ x) (fun k z => ψ z k) (hψ j)
  ext i
  rw [Pi.smul_apply, Finset.sum_apply]
  simp only [Pi.add_apply, Pi.smul_apply, hg, smul_eq_mul]
  simp only [mulVec, dotProduct, svgdMatrix, featureKernel]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### (d) The PFG objective: normal equations and uniqueness on the particles -/

/-- **Exact expansion of the PFG objective.** For a symmetric `H` and features differentiable
at every particle, for all `W, Δ`,
`Jstein(W + Δ) = Jstein(W) + ⟨Δ, H W Σψ - G⟩_F + (1/2) (1/n) ∑ⱼ ‖Δ ψ(yⱼ)‖²_H`
(`popSteinObjective_add` at the empirical measure). -/
theorem featureSteinObjective_add {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    (W Δ : Matrix (Fin d) (Fin m) ℝ) :
    featureSteinObjective H y sStar ψ (W + Δ) = featureSteinObjective H y sStar ψ W
      + frobInner Δ (H * W * featureCov y ψ - steinFeatureMatrix y sStar ψ)
      + 1 / 2 * ((1 / (n : ℝ)) * ∑ j, sqNormH H (Δ *ᵥ ψ (y j))) := by
  simpa only [← featureSteinObjective_eq_popSteinObjective, ← featureCov_eq_popFeatureCov,
    ← steinFeatureMatrix_eq_popSteinMatrix, integral_empMeasure]
    using popSteinObjective_add hH sStar ψ ((ae_empMeasure_iff y).2 hψ)
      (fun _ _ => integrable_empMeasure _ _) (fun _ _ => integrable_empMeasure _ _) W Δ

/-- **(d) Expansion at a solution of the normal equations.** If `H` is symmetric, the
features are differentiable at every particle and `H W Σψ = G` (normal equations), then
for every `Δ`, `Jstein(W + Δ) = Jstein(W) + (1/2) (1/n) ∑ⱼ ‖Δ ψ(yⱼ)‖²_H`. -/
theorem featureSteinObjective_add_of_normalEq {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    {W : Matrix (Fin d) (Fin m) ℝ}
    (hW : H * W * featureCov y ψ = steinFeatureMatrix y sStar ψ)
    (Δ : Matrix (Fin d) (Fin m) ℝ) :
    featureSteinObjective H y sStar ψ (W + Δ) = featureSteinObjective H y sStar ψ W
      + 1 / 2 * ((1 / (n : ℝ)) * ∑ j, sqNormH H (Δ *ᵥ ψ (y j))) := by
  rw [featureSteinObjective_add hH y sStar ψ hψ, hW, sub_self, frobInner_zero_right, add_zero]

/-- **(d) Minimisers are exactly the solutions of the normal equations.** For `H` positive
semidefinite and features differentiable at every particle, `W` is a global minimiser of
`Jstein` iff `H W Σψ = G`. In particular a minimiser exists iff the normal equations are
solvable (no existence is claimed when `Σψ` is singular). This is
`popStein_isMinimiser_iff_normalEq` at the empirical measure. -/
theorem featureStein_isMinimiser_iff_normalEq {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j)) (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V, featureSteinObjective H y sStar ψ W ≤ featureSteinObjective H y sStar ψ V) ↔
      H * W * featureCov y ψ = steinFeatureMatrix y sStar ψ := by
  simpa only [← featureSteinObjective_eq_popSteinObjective, ← featureCov_eq_popFeatureCov,
    ← steinFeatureMatrix_eq_popSteinMatrix]
    using popStein_isMinimiser_iff_normalEq hH sStar ψ ((ae_empMeasure_iff y).2 hψ)
      (fun _ _ => integrable_empMeasure _ _) (fun _ _ => integrable_empMeasure _ _) W

/-- **(d) Solutions of the normal equations are global minimisers.** If `H` is positive
semidefinite (in particular if it is positive definite), the features are differentiable at
every particle and `H W Σψ = G`, then `Jstein(W) ≤ Jstein(V)` for every `V`. -/
theorem featureSteinObjective_le_of_normalEq {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    {W : Matrix (Fin d) (Fin m) ℝ}
    (hW : H * W * featureCov y ψ = steinFeatureMatrix y sStar ψ)
    (V : Matrix (Fin d) (Fin m) ℝ) :
    featureSteinObjective H y sStar ψ W ≤ featureSteinObjective H y sStar ψ V :=
  (featureStein_isMinimiser_iff_normalEq hH y sStar ψ hψ W).2 hW V

/-- **(d) SE-2: uniqueness on the particles.** Let `H` be positive definite, the
features differentiable at every particle and `W` a solution of `H W Σψ = G`. Then for every
`V`, `Jstein(V) = Jstein(W)` iff `V ψ(yⱼ) = W ψ(yⱼ)` for every particle `j`; i.e. the minimising
velocity field is unique on the support of the empirical measure
(`popSteinObjective_eq_iff_of_normalEq` at the empirical measure). -/
theorem featureSteinObjective_eq_iff_of_normalEq {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    {W : Matrix (Fin d) (Fin m) ℝ}
    (hW : H * W * featureCov y ψ = steinFeatureMatrix y sStar ψ)
    (V : Matrix (Fin d) (Fin m) ℝ) :
    featureSteinObjective H y sStar ψ V = featureSteinObjective H y sStar ψ W ↔
      ∀ j, V *ᵥ ψ (y j) = W *ᵥ ψ (y j) := by
  rw [featureCov_eq_popFeatureCov, steinFeatureMatrix_eq_popSteinMatrix] at hW
  simpa only [← featureSteinObjective_eq_popSteinObjective, ae_empMeasure_iff]
    using popSteinObjective_eq_iff_of_normalEq hH sStar ψ ((ae_empMeasure_iff y).2 hψ)
      (fun _ _ => integrable_empMeasure _ _) (fun _ _ => integrable_empMeasure _ _) hW V

/-- **(d) Every minimiser agrees with a normal-equation solution on the particles.** If `H`
is positive definite, the features are differentiable at every particle, `H W Σψ = G` and
`V` is any global minimiser of `Jstein`, then `V ψ(yⱼ) = W ψ(yⱼ)` for every particle `j`. -/
theorem featureStein_minimiser_agree_on_particles {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    {W : Matrix (Fin d) (Fin m) ℝ}
    (hW : H * W * featureCov y ψ = steinFeatureMatrix y sStar ψ)
    {V : Matrix (Fin d) (Fin m) ℝ}
    (hV : ∀ U, featureSteinObjective H y sStar ψ V ≤ featureSteinObjective H y sStar ψ U)
    (j : Fin n) :
    V *ᵥ ψ (y j) = W *ᵥ ψ (y j) := by
  refine (featureSteinObjective_eq_iff_of_normalEq hH y sStar ψ hψ hW V).mp ?_ j
  exact le_antisymm (hV W) (featureSteinObjective_le_of_normalEq hH.posSemidef y sStar ψ hψ hW V)

/-- **(d) Explicit solution when `Σψ` is invertible.** If `H` is positive definite and
`det Σψ` is a unit (i.e. `Σψ` is invertible), then `W = H⁻¹ G Σψ⁻¹` solves the normal
equations `H W Σψ = G`. -/
theorem normalEq_of_isUnit_det {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hCov : IsUnit (featureCov y ψ).det) :
    H * (H⁻¹ * steinFeatureMatrix y sStar ψ * (featureCov y ψ)⁻¹) * featureCov y ψ =
      steinFeatureMatrix y sStar ψ := by
  have hHdet : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH.isUnit
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hHdet, Matrix.one_mul,
    Matrix.mul_assoc, nonsing_inv_mul _ hCov, Matrix.mul_one]

/-- **(d) Unique minimiser when `Σψ` is invertible.** If `H` is positive definite, the
features are differentiable at every particle and `Σψ` is invertible, then `W` minimises
`Jstein` iff `W = H⁻¹ G Σψ⁻¹`. -/
theorem featureStein_isMinimiser_iff_of_isUnit_det {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    (hCov : IsUnit (featureCov y ψ).det) (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V, featureSteinObjective H y sStar ψ W ≤ featureSteinObjective H y sStar ψ V) ↔
      W = H⁻¹ * steinFeatureMatrix y sStar ψ * (featureCov y ψ)⁻¹ := by
  rw [featureStein_isMinimiser_iff_normalEq hH.posSemidef y sStar ψ hψ]
  have hHdet : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH.isUnit
  constructor
  · intro hW
    rw [← hW, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCov, Matrix.mul_one,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hHdet, Matrix.one_mul]
  · rintro rfl
    exact normalEq_of_isUnit_det hH y sStar ψ hCov

/-! ### (e) When the fixed norm and the weighted output norm coincide -/

/-- **(e) The objectives coincide when `Σψ = 1` and `H = λ • 1`.** If the empirical feature
second-moment matrix is the identity and the preconditioner is `λ • 1`, the weighted output
norm equals the fixed feature norm, `(1/2)(1/n) ∑ⱼ ‖W ψ(yⱼ)‖²_H = (λ/2) ‖W‖_F²`, so
`Jstein(W) = Jsvgd(W)` for every `W` (no regularity needed: the linear terms are literally the
same; `popSteinObjective_eq_svgdPopObjective` at the empirical measure). -/
theorem featureSteinObjective_eq_svgdFeatureObjective {lam : ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ}
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hCov : featureCov y ψ = 1) (hH : H = lam • 1) (W : Matrix (Fin d) (Fin m) ℝ) :
    featureSteinObjective H y sStar ψ W = svgdFeatureObjective lam y sStar ψ W := by
  rw [featureCov_eq_popFeatureCov] at hCov
  rw [featureSteinObjective_eq_popSteinObjective, svgdFeatureObjective_eq_svgdPopObjective]
  exact popSteinObjective_eq_svgdPopObjective sStar ψ (fun _ _ => integrable_empMeasure _ _)
    hCov hH W

/-- **(e) The SVGD matrix solves the PFG normal equations when `Σψ = 1` and `H = λ • 1`**
(for `λ ≠ 0`): `H Wsvgd Σψ = G`. -/
theorem svgdMatrix_normalEq {lam : ℝ} (hlam : lam ≠ 0) {H : Matrix (Fin d) (Fin d) ℝ}
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hCov : featureCov y ψ = 1) (hH : H = lam • 1) :
    H * svgdMatrix lam y sStar ψ * featureCov y ψ = steinFeatureMatrix y sStar ψ := by
  rw [hCov, hH, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_svgdMatrix hlam]

/-- **(e) SE-2: SVGD as a special case of PFG.** If `λ > 0`, the features are
differentiable at every particle, `Σψ = 1` and `H = λ • 1`, then `W` minimises the PFG
objective iff `W = Wsvgd`, the finite-feature SVGD matrix. -/
theorem featureStein_isMinimiser_iff_eq_svgdMatrix {lam : ℝ} (hlam : 0 < lam)
    {H : Matrix (Fin d) (Fin d) ℝ}
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ j k, DifferentiableAt ℝ (fun z => ψ z k) (y j))
    (hCov : featureCov y ψ = 1) (hH : H = lam • 1) (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V, featureSteinObjective H y sStar ψ W ≤ featureSteinObjective H y sStar ψ V) ↔
      W = svgdMatrix lam y sStar ψ := by
  simp only [featureSteinObjective_eq_svgdFeatureObjective y sStar ψ hCov hH]
  exact svgdFeatureObjective_isMinimiser_iff hlam y sStar ψ hψ W

end FormalizeSampling.FeatureClass
