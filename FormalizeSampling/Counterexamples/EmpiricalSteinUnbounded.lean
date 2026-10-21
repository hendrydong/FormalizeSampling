module

public import FormalizeSampling.ScoreEstimation.FeatureClass
public import FormalizeSampling.Flow.KLDecay

/-!
# The empirical Stein objective is unbounded below with few particles (CE-06)

Registry ID: **CE-06** (the finite-particle Monte Carlo Stein objective has no minimiser). It
concerns finite-particle error bounds for particle methods driven by a Stein-type objective,
which are not proved here (the particle layer is a separate proof layer of the error
decomposition). Population contrast: **SE-1** (in its finite-feature form SE-2 and the projected
form of `Flow/KLDecay.lean`).

## Setting

The Stein objective with regulariser `h = ½‖·‖²_H`, evaluated on particles `y₁, …, yₙ` (its
Monte Carlo version), is
`L̂(f) = (1/n) ∑ⱼ [½ ‖f(yⱼ)‖²_H - f(yⱼ) ⬝ s⋆(yⱼ) - div f(yⱼ)]`.
For the linear feature class `f_W = W ψ` this is exactly
`FormalizeSampling.FeatureClass.featureSteinObjective H y sStar ψ W`
(`ScoreEstimation/FeatureClass`).
For `n ≤ d` and any class containing the affine fields, `L̂` is unbounded below: a field
vanishing at every particle but with positive divergence drives `L̂` to `-∞`. This file proves
this for the affine feature class. By contrast the population objective (SE-1) is bounded
below by `-½ ∫ ‖∇log(p/p⋆)‖²_{H⁻¹} dp`, i.e. `-½` times the relative Fisher information when
`H = 1`.

The same degeneracy is known for Gaussian score matching: the empirical score-matching estimator
of a Gaussian precision matrix is the inverse sample covariance (Hyvärinen 2005, JMLR 6, §3.1),
and the empirical loss `-tr K + ½ tr(K K W)` has a singular Hessian in high dimension
(Lin–Drton–Shojaie 2016, arXiv:1507.00433).

**Consequence for the error analysis.** For `0 < n ≤ d` and a class containing the affine
fields, the lower bound of the population objective does not carry over to the finite-particle
Monte Carlo objective: replacing `p_t` by the empirical measure removes the lower bound and the
existence of a minimiser. This is why the particle layer is a separate layer of the error
analysis with its own error terms, and this file is a companion of CE-05
(`Counterexamples/ParticleVsPopulation`: particles have no density).

## Conventions

* State space `Fin d → ℝ`, `n` particles `y : Fin n → Fin d → ℝ`, an arbitrary target-score
  field `sStar` (nothing uses that it is a score) and an arbitrary matrix `H` (not even
  positive definite is needed for the unboundedness).
* Affine features `affineFeatures x = (1, x₁, …, x_d) : Fin (d + 1) → ℝ` (`Fin.cons 1 x`), so
  `m = d + 1` and `f_W(x) = W ψ(x) = W₀ + A x`, where `W₀` is column `0` of `W` and `A` the
  remaining `d × d` block (`Aᵢₗ = W i l.succ`). Then `div f_W ≡ tr A = ∑ᵢ W i i.succ`
  (`divergence_affineField`).
* `0 < n` is necessary: with `n = 0` Lean's `1 / 0 = 0` makes the empirical objective
  identically `0`.

## Main results

* `featureSteinObjective_eq_neg_trace`: if `f_W(yⱼ) = 0` for every particle, the empirical
  objective equals `-tr A = -∑ᵢ W i i.succ` (any `H`, any `sStar`).
* `exists_vanishing_trace_one`: for `0 < n ≤ d` there is such a `W` with `tr A = 1`
  (a nonzero affine functional vanishing at all particles exists since `n < d + 1`).
* **CE-06** `exists_featureSteinObjective_lt` (`∀ C, ∃ W, L̂(W) < C`),
  `not_bddBelow_featureSteinObjective`, `not_exists_minimiser`, and the linear-algebra
  consequences `normalEq_not_solvable` (the normal equations `H W Σψ = G` have no solution for
  positive-semidefinite `H`) and `not_isUnit_det_featureCov` (`Σψ` is singular).
* An explicit one-dimensional instance: `oneParticleMatrix_mulVec`
  (`f(x) = w (x - y₀)`) and `oneParticle_featureSteinObjective` (`L̂ = -w` for `d = n = 1`,
  `m = 2`, any `H`, in particular `H = 1`, and any target score), with
  `oneParticle_exists_lt`.
* Population contrast: `popSteinObjective_exists_minimiser`, `bddBelow_popSteinObjective` (the
  population feature objective attains its minimum when `H ≻ 0` and the population feature
  second-moment matrix `Σ_μ` is invertible, with explicit integrability), and
  `neg_half_integral_le_projectedObjective`, `neg_half_relFisher_le_projectedObjective` (the
  projected population objective is `≥ -½ ∫ ‖s - s⋆‖²_{H⁻¹}`, `= -½ relFisher` for `H = 1`).

## What is NOT proved here

* The bump-function version (unboundedness for **every** `n` once the class contains
  `C_c^∞` fields) and any nonlinear parametric class `f_θ` (neural networks) are not treated.
* The population lower bound is proved for the **projected** form
  `-∫ f ⬝ (s⋆ - s) dμ + ½ ∫ ‖f‖²_H dμ` (`KLDecay.projectedObjective`). Its identification
  with the Stein (divergence) form `popSteinObjective` requires the Stein integration by parts
  under a density (SE-1) and is not proved here. For the Stein form only the feature-class
  statement with an invertible `Σ_μ` is given; that `Σ_μ` is invertible for the affine features
  under a law with finite, nondegenerate covariance (e.g. a Gaussian) is standard but not
  formalised.
* Nothing about `n > d`: there the affine-feature objective may or may not be bounded (it has a
  minimiser iff the normal equations are solvable,
  `FeatureClass.featureStein_isMinimiser_iff_normalEq`).
* No statement about the implicit regularisation of a finite inner optimisation loop, about
  particle dynamics, or about quantitative finite-particle error bounds (these remain open
  beyond this obstruction).
-/

@[expose] public section

open Matrix MeasureTheory

namespace FormalizeSampling.Counterexamples.EmpiricalSteinUnbounded

open FormalizeSampling.FeatureClass

variable {n d : ℕ}

/-! ### Affine features -/

/-- The affine feature map `ψ(x) = (1, x₁, …, x_d) : Fin (d + 1) → ℝ`, so that
`W ψ(x) = W₀ + A x` is an arbitrary affine vector field. -/
def affineFeatures (x : Fin d → ℝ) : Fin (d + 1) → ℝ := Fin.cons 1 x

/-- The constant feature: `ψ(x)₀ = 1`. -/
theorem affineFeatures_zero (x : Fin d → ℝ) : affineFeatures x 0 = 1 := rfl

/-- The linear features: `ψ(x)_{i+1} = xᵢ`. -/
theorem affineFeatures_succ (x : Fin d → ℝ) (i : Fin d) : affineFeatures x i.succ = x i := rfl

/-- Every affine feature coordinate `z ↦ ψ(z)ₖ` is differentiable everywhere (no
assumptions). -/
theorem differentiableAt_affineFeatures (k : Fin (d + 1)) (x : Fin d → ℝ) :
    DifferentiableAt ℝ (fun z => affineFeatures z k) x := by
  refine Fin.cases ?_ (fun i => ?_) k
  · exact differentiableAt_const _
  · exact differentiableAt_apply i x

/-- The constant feature has zero partial derivatives: `∂ᵢ ψ₀ = 0`. -/
theorem partialDeriv_affineFeatures_zero (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (fun z => affineFeatures z 0) x = 0 := by
  simp [partialDeriv, affineFeatures_zero]

/-- The linear features have constant partial derivatives: `∂ᵢ ψ_{l+1} = δᵢₗ`. -/
theorem partialDeriv_affineFeatures_succ (i l : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (fun z => affineFeatures z l.succ) x = if l = i then 1 else 0 := by
  simp only [partialDeriv, affineFeatures_succ]
  rw [(hasFDerivAt_apply l x).fderiv]
  simp [Pi.single_apply]

/-- **Divergence of an affine field.** For `f_W(x) = W ψ(x) = W₀ + A x` with the affine
features, `div f_W (x) = tr A = ∑ᵢ W i i.succ` at every `x` (no assumptions). -/
theorem divergence_affineField (W : Matrix (Fin d) (Fin (d + 1)) ℝ) (x : Fin d → ℝ) :
    divergence (fun z => W *ᵥ affineFeatures z) x = ∑ i, W i i.succ := by
  rw [divergence_featureField W affineFeatures x (fun k => differentiableAt_affineFeatures k x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succ, partialDeriv_affineFeatures_zero]
  simp [partialDeriv_affineFeatures_succ]

/-! ### The empirical objective on fields vanishing at the particles -/

/-- **The empirical objective only sees the divergence.** Let `n ≠ 0`, `H` any `d × d` matrix,
`sStar` any vector field, and let the affine field `f_W = W ψ` vanish at every particle:
`W ψ(yⱼ) = 0` for all `j`. Then the empirical Stein objective is
`L̂(W) = -(1/n) ∑ⱼ (div f_W(yⱼ) + f_W(yⱼ) ⬝ sStar(yⱼ)) + ½ (1/n) ∑ⱼ ‖f_W(yⱼ)‖²_H = -tr A`,
with `tr A = ∑ᵢ W i i.succ`. -/
theorem featureSteinObjective_eq_neg_trace (hn : n ≠ 0) (H : Matrix (Fin d) (Fin d) ℝ)
    (y : Fin n → Fin d → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ)
    {W : Matrix (Fin d) (Fin (d + 1)) ℝ} (hW : ∀ j, W *ᵥ affineFeatures (y j) = 0) :
    featureSteinObjective H y sStar affineFeatures W = -∑ i, W i i.succ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [featureSteinObjective, empiricalSteinTerm, hW, divergence_affineField, sqNormH,
    zero_dotProduct, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_zero]
  field_simp

/-- **A vanishing affine field with unit divergence (`n ≤ d`).** If `0 < n ≤ d`, then for every
particle configuration `y` there is `W` with `W ψ(yⱼ) = 0` for all `j` and `tr A = 1`.
Construction: the `n` vectors `ψ(yⱼ) ∈ ℝ^{d+1}` span a proper subspace (`n < d + 1`), so some
`w ≠ 0` is orthogonal to all of them; its linear part `ℓ = (w₁, …, w_d)` is nonzero because
`n > 0`; take `W = ℓ wᵀ / ‖ℓ‖²`, i.e. `f_W(x) = (w ⬝ ψ(x)) ℓ / ‖ℓ‖²`. -/
theorem exists_vanishing_trace_one (hn : 0 < n) (hnd : n ≤ d) (y : Fin n → Fin d → ℝ) :
    ∃ W : Matrix (Fin d) (Fin (d + 1)) ℝ,
      (∀ j, W *ᵥ affineFeatures (y j) = 0) ∧ ∑ i, W i i.succ = 1 := by
  let M : Matrix (Fin n) (Fin (d + 1)) ℝ := Matrix.of fun j k => affineFeatures (y j) k
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
  obtain ⟨w, hwker, hw0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hw : ∀ j, affineFeatures (y j) ⬝ᵥ w = 0 := fun j => by
    have := congrFun (LinearMap.mem_ker.1 hwker) j
    simpa [M, mulVec] using this
  set l : Fin d → ℝ := fun i => w i.succ with hl
  have hdot : ∀ x : Fin d → ℝ, affineFeatures x ⬝ᵥ w = w 0 + x ⬝ᵥ l := fun x => by
    simp [dotProduct, Fin.sum_univ_succ, affineFeatures_zero, affineFeatures_succ, l]
  have hl0 : l ≠ 0 := by
    intro h
    apply hw0
    have h0 : w 0 = 0 := by
      have := hw ⟨0, hn⟩
      rw [hdot, h, dotProduct_zero, add_zero] at this
      exact this
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using h0
    · simpa [l] using congrFun h i
  have hs : 0 < l ⬝ᵥ l :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (l i))
      (fun h => hl0 (dotProduct_self_eq_zero.1 h.symm))
  refine ⟨fun i k => l i * w k / (l ⬝ᵥ l), fun j => ?_, ?_⟩
  · funext i
    simp only [mulVec, dotProduct, Pi.zero_apply]
    have := hw j
    simp only [dotProduct] at this
    calc ∑ k, l i * w k / (l ⬝ᵥ l) * affineFeatures (y j) k
        = l i / (l ⬝ᵥ l) * ∑ k, affineFeatures (y j) k * w k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = 0 := by rw [this, mul_zero]
  · simp only [l]
    rw [← Finset.sum_div]
    exact div_self hs.ne'

/-! ### CE-06: unboundedness and non-existence of a minimiser -/

/-- **CE-06 (affine class): the empirical Stein objective is unbounded below.** Let
`0 < n ≤ d`, `y` any configuration of `n` particles in `ℝ^d`, `H` any `d × d` matrix and
`sStar` any target-score field. With the affine features `ψ(x) = (1, x)`, for every `C : ℝ`
there is `W` with `L̂(W) = featureSteinObjective H y sStar ψ W < C`. -/
theorem exists_featureSteinObjective_lt (hn : 0 < n) (hnd : n ≤ d)
    (H : Matrix (Fin d) (Fin d) ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (C : ℝ) :
    ∃ W, featureSteinObjective H y sStar affineFeatures W < C := by
  obtain ⟨W₁, hW₁, htr⟩ := exists_vanishing_trace_one hn hnd y
  refine ⟨(1 - C) • W₁, ?_⟩
  rw [featureSteinObjective_eq_neg_trace hn.ne' H y sStar
    (fun j => by rw [smul_mulVec, hW₁, smul_zero])]
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, htr]
  linarith

/-- **CE-06, range form.** Under the hypotheses of `exists_featureSteinObjective_lt`
(`0 < n ≤ d`, affine features, any `H`, `y`, `sStar`), the set of values of the empirical
Stein objective is not bounded below. -/
theorem not_bddBelow_featureSteinObjective (hn : 0 < n) (hnd : n ≤ d)
    (H : Matrix (Fin d) (Fin d) ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) :
    ¬ BddBelow (Set.range (featureSteinObjective H y sStar affineFeatures)) := by
  rintro ⟨C, hC⟩
  obtain ⟨W, hW⟩ := exists_featureSteinObjective_lt hn hnd H y sStar C
  exact absurd (hC ⟨W, rfl⟩) (not_le.2 hW)

/-- **CE-06: no empirical minimiser.** Under the hypotheses of `exists_featureSteinObjective_lt`
(`0 < n ≤ d`, affine features, any `H`, `y`, `sStar`), no `W` minimises the empirical Stein
objective. -/
theorem not_exists_minimiser (hn : 0 < n) (hnd : n ≤ d)
    (H : Matrix (Fin d) (Fin d) ℝ) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) :
    ¬ ∃ W, ∀ V, featureSteinObjective H y sStar affineFeatures W ≤
      featureSteinObjective H y sStar affineFeatures V := by
  rintro ⟨W, hW⟩
  obtain ⟨V, hV⟩ := exists_featureSteinObjective_lt hn hnd H y sStar
    (featureSteinObjective H y sStar affineFeatures W)
  exact absurd (hW V) (not_le.2 hV)

/-- **CE-06: the empirical normal equations are unsolvable.** For `0 < n ≤ d`, affine features
and positive-semidefinite `H`, no `W` solves `H W Σψ = G` (`Σψ = featureCov`,
`G = steinFeatureMatrix`); otherwise it would be a minimiser
(`FeatureClass.featureStein_isMinimiser_iff_normalEq`). -/
theorem normalEq_not_solvable (hn : 0 < n) (hnd : n ≤ d)
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosSemidef) (y : Fin n → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (W : Matrix (Fin d) (Fin (d + 1)) ℝ) :
    H * W * featureCov y affineFeatures ≠ steinFeatureMatrix y sStar affineFeatures := by
  intro h
  refine not_exists_minimiser hn hnd H y sStar ⟨W, ?_⟩
  exact (featureStein_isMinimiser_iff_normalEq hH y sStar affineFeatures
    (fun j k => differentiableAt_affineFeatures k (y j)) W).2 h

/-- **The empirical affine feature second-moment matrix is singular for `n ≤ d`.** For
`0 < n ≤ d` and any particles `y`, `Σψ = (1/n) ∑ⱼ ψ(yⱼ) ψ(yⱼ)ᵀ` is not invertible (its
determinant is not a unit). Derived from CE-06: an invertible `Σψ` would give a minimiser
(`FeatureClass.normalEq_of_isUnit_det` with `H = 1`, `sStar = 0`). -/
theorem not_isUnit_det_featureCov (hn : 0 < n) (hnd : n ≤ d) (y : Fin n → Fin d → ℝ) :
    ¬ IsUnit (featureCov y affineFeatures).det := by
  intro h
  have hH : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := PosDef.one
  exact normalEq_not_solvable hn hnd hH.posSemidef y 0 _
    (normalEq_of_isUnit_det hH y 0 affineFeatures h)

/-! ### The one-dimensional, one-particle instance -/

/-- The coefficient matrix `W_w = (-w y₀, w) : Matrix (Fin 1) (Fin 2) ℝ` of the affine field
`f(x) = w (x - y₀)` on `ℝ¹` (`oneParticleMatrix_mulVec`). -/
def oneParticleMatrix (y₀ w : ℝ) : Matrix (Fin 1) (Fin 2) ℝ := !![-(w * y₀), w]

/-- With the affine features on `ℝ¹` (`m = 2`), `W_w ψ(x) = w (x - y₀)`; in particular the field
vanishes at `y₀` and has divergence `w` (`divergence_affineField`). -/
theorem oneParticleMatrix_mulVec (y₀ w : ℝ) (x : Fin 1 → ℝ) :
    oneParticleMatrix y₀ w *ᵥ affineFeatures x = fun _ => w * (x 0 - y₀) := by
  funext i
  fin_cases i
  simp [oneParticleMatrix, mulVec, dotProduct, Fin.sum_univ_succ, affineFeatures_zero]
  rw [show affineFeatures x 1 = x 0 from rfl]
  ring

/-- **CE-06, explicit instance (`d = n = 1`, `m = 2`).** For one particle `y₀ = y 0 0` in `ℝ`,
the affine features `ψ(x) = (1, x)`, any `1 × 1` matrix `H` (in particular `H = 1`), any target
score `sStar` and any `w : ℝ`, the empirical Stein objective of `f(x) = w (x - y₀)` is exactly
`-w`: the field vanishes at the particle and has divergence `w`. -/
theorem oneParticle_featureSteinObjective (H : Matrix (Fin 1) (Fin 1) ℝ)
    (y : Fin 1 → Fin 1 → ℝ) (sStar : (Fin 1 → ℝ) → Fin 1 → ℝ) (w : ℝ) :
    featureSteinObjective H y sStar affineFeatures (oneParticleMatrix (y 0 0) w) = -w := by
  rw [featureSteinObjective_eq_neg_trace one_ne_zero H y sStar (fun j => ?_)]
  · simp [oneParticleMatrix]
  · rw [oneParticleMatrix_mulVec]
    funext i
    fin_cases j
    simp

/-- **CE-06, explicit instance, unboundedness.** In the setting of
`oneParticle_featureSteinObjective` (`d = n = 1`, affine features, any `H`, `y`, `sStar`), for
every `C` the field `f(x) = (1 - C)(x - y₀)` has empirical Stein objective `C - 1 < C`. -/
theorem oneParticle_exists_lt (H : Matrix (Fin 1) (Fin 1) ℝ)
    (y : Fin 1 → Fin 1 → ℝ) (sStar : (Fin 1 → ℝ) → Fin 1 → ℝ) (C : ℝ) :
    ∃ W, featureSteinObjective H y sStar affineFeatures W < C :=
  ⟨oneParticleMatrix (y 0 0) (1 - C), by
    rw [oneParticle_featureSteinObjective]
    linarith⟩

/-! ### Population contrast (SE-1) -/

/-- **Population contrast, feature form.** Let `H` be positive definite, `μ` a measure,
`ψ : (Fin d → ℝ) → Fin m → ℝ` features differentiable `μ`-a.e., the Stein integrands
`sStarᵢ ψₖ + ∂ᵢ ψₖ` and the feature products `ψₖ ψₗ` `μ`-integrable, and the population feature
second-moment matrix `Σ_μ = popFeatureCov μ ψ` invertible. Then the population Stein objective
`popSteinObjective H μ sStar ψ` attains its minimum (at `W = H⁻¹ G_μ Σ_μ⁻¹`, via SE-2
`FeatureClass.popStein_isMinimiser_iff_normalEq`). Contrast with `not_exists_minimiser`: the
empirical `Σψ` of `n ≤ d` particles is singular (`not_isUnit_det_featureCov`). -/
theorem popSteinObjective_exists_minimiser {m : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (hCovInv : IsUnit (popFeatureCov μ ψ).det) :
    ∃ W, ∀ V, popSteinObjective H μ sStar ψ W ≤ popSteinObjective H μ sStar ψ V := by
  refine ⟨H⁻¹ * popSteinMatrix μ sStar ψ * (popFeatureCov μ ψ)⁻¹,
    (popStein_isMinimiser_iff_normalEq hH.posSemidef sStar ψ hψ hG hCov _).2 ?_⟩
  have hHdet : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH.isUnit
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hHdet, Matrix.one_mul,
    Matrix.mul_assoc, nonsing_inv_mul _ hCovInv, Matrix.mul_one]

/-- **Population contrast, feature form, boundedness.** Under the hypotheses of
`popSteinObjective_exists_minimiser` (`H ≻ 0`, a.e. differentiable features, integrable Stein
integrands and feature products, invertible `Σ_μ`), the population Stein objective is bounded
below. -/
theorem bddBelow_popSteinObjective {m : ℕ} {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)}
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ᵐ x ∂μ, ∀ k, DifferentiableAt ℝ (fun z => ψ z k) x)
    (hG : ∀ i k, Integrable
      (fun x => sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) μ)
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l) μ)
    (hCovInv : IsUnit (popFeatureCov μ ψ).det) :
    BddBelow (Set.range (popSteinObjective H μ sStar ψ)) := by
  obtain ⟨W, hW⟩ := popSteinObjective_exists_minimiser hH sStar ψ hψ hG hCov hCovInv
  exact ⟨_, by rintro _ ⟨V, rfl⟩; exact hW V⟩

section ProjectedForm

open FormalizeSampling.KLDecay FormalizeSampling.SPD

/-- **Population contrast, projected form (SE-1 lower bound).** Let `H` be positive definite,
`μ` a measure, `s` (standing for `∇log p`), `sStar` (for `∇log p⋆`) and `f` vector fields with
`f ⬝ (sStar - s)`, `‖f‖²_H` and `‖s - sStar‖²_{H⁻¹}` `μ`-integrable. Then the projected
Stein objective `J(f) = -∫ f ⬝ (sStar - s) dμ + ½ ∫ ‖f‖²_H dμ` satisfies
`J(f) ≥ -½ ∫ ‖s - sStar‖²_{H⁻¹} dμ` (pointwise completion of squares,
`Foundations/SPDPreconditioner`); equality holds at `v⋆ = H⁻¹(sStar - s)`
(`KLDecay.projectedObjective_sub_eq`). -/
theorem neg_half_integral_le_projectedObjective {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {μ : Measure (Fin d → ℝ)} (f s sStar : (Fin d → ℝ) → Fin d → ℝ)
    (hfg : Integrable (fun x => f x ⬝ᵥ (sStar x - s x)) μ)
    (hf : Integrable (fun x => sqNormH H (f x)) μ)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ) :
    -(1 / 2) * ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ ≤ projectedObjective H μ s sStar f := by
  have hrhs : projectedObjective H μ s sStar f =
      ∫ x, (-(f x ⬝ᵥ (sStar x - s x)) + (1 / 2) * sqNormH H (f x)) ∂μ := by
    rw [projectedObjective, integral_add (f := fun x => -(f x ⬝ᵥ (sStar x - s x)))
      (g := fun x => (1 / 2) * sqNormH H (f x)) hfg.neg (hf.const_mul _), integral_neg,
      integral_const_mul]
  rw [hrhs, ← integral_const_mul]
  refine integral_mono (hdiss.const_mul _) (hfg.neg.add (hf.const_mul _)) fun x => ?_
  have h := quadratic_ge_min hH (f x) (sStar x - s x)
  rwa [← neg_sub (s x) (sStar x), sqNormH_neg, neg_sub] at h

/-- **Population contrast, `H = 1`: `-½` relative Fisher information.** For a measure `μ` and
vector fields `f, s, sStar` with `f ⬝ (sStar - s)`, `|f|²` and `|s - sStar|²` `μ`-integrable,
the projected Stein objective with `H = 1` satisfies `J(f) ≥ -½ ∫ |s - sStar|² dμ`, i.e.
`-½ relFisher μ s sStar`, the relative Fisher information `∫ |∇log(p/p⋆)|² dp` when `μ = p`,
`s = ∇log p`, `sStar = ∇log p⋆`. -/
theorem neg_half_relFisher_le_projectedObjective {μ : Measure (Fin d → ℝ)}
    (f s sStar : (Fin d → ℝ) → Fin d → ℝ)
    (hfg : Integrable (fun x => f x ⬝ᵥ (sStar x - s x)) μ)
    (hf : Integrable (fun x => f x ⬝ᵥ f x) μ)
    (hfisher : Integrable (fun x => (s x - sStar x) ⬝ᵥ (s x - sStar x)) μ) :
    -(1 / 2) * relFisher μ s sStar ≤ projectedObjective 1 μ s sStar f := by
  have h1 : ∀ u : Fin d → ℝ, sqNormH (1 : Matrix (Fin d) (Fin d) ℝ) u = u ⬝ᵥ u := fun u => by
    simp [sqNormH]
  have h2 : ∀ u : Fin d → ℝ, sqNormH (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ u = u ⬝ᵥ u := fun u => by
    simp [sqNormH]
  have h := neg_half_integral_le_projectedObjective PosDef.one f s sStar hfg
    (by simpa only [h1] using hf) (by simpa only [h2] using hfisher)
  simpa only [h2, relFisher] using h

end ProjectedForm

end FormalizeSampling.Counterexamples.EmpiricalSteinUnbounded
