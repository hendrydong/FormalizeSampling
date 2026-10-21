module

public import Mathlib.Analysis.ODE.Gronwall
public import FormalizeSampling.Foundations.SPDPreconditioner

/-!
# PFG: approximate minimisers, KL dissipation and conditional exponential decay

Guarantee layer for preconditioned functional gradient flow (PFG, Dong–Wang–Lin–Zhang,
ICLR 2023) with a constant positive-definite preconditioner `H`.

## Conventions

* `μ` (or `μ t`) is the law of the particles, a measure on `Fin d → ℝ`; `s` (or `s t`) is a
  vector field standing for its state score `∇log p` and `sStar` for the target score
  `∇log p⋆`. The theorems are stated for arbitrary vector fields `s, sStar`; the reading
  `s = score p`, `sStar = score p⋆` (shared `FormalizeSampling.score`) is made explicit in
  `exp_decay_idealVelocity_density`.
* The ideal PFG velocity is `v⋆ = H⁻¹ (sStar - s)` (`idealVelocity`), so `H v⋆ = sStar - s`.
* The FL-1 first variation of KL along a velocity `f` is the number
  `∫ f ⬝ᵥ (s - sStar) dμ = 𝔼_p[f ⬝ᵥ ∇log(p/p⋆)] = -∫ f ⬝ᵥ (H v⋆) dμ`.
* The relative Fisher information is `relFisher μ s sStar = ∫ |s - sStar|² dμ`.

## Contents (registry IDs)

* **FL-3** (Verified, explicit integrability): `neg_integral_dotProduct_mulVec_le` and its
  exact form `neg_integral_dotProduct_mulVec_eq`; the score form `transport_rate_le`; the
  objective-gap identity `projectedObjective_sub_eq` (`J(f) - J(v⋆) = ½ ∫ ‖f - v⋆‖²_H dμ`)
  and `transport_rate_le_objective_gap` (loss of dissipation ≤ optimisation gap).
* **FL-2 input** (Verified): `integral_idealVelocity_dotProduct` /
  `integral_idealVelocity_dotProduct_nonpos`: along `v⋆` the first-variation integrand
  integrates to `-∫ ‖s - sStar‖²_{H⁻¹} dμ ≤ 0`; `ideal_rate_le_neg_fisher` bounds it by
  `-(1/M) relFisher` using the spectral comparison of `SPD.inv_lower_bound_of_upper_bound`.
* **FL-4** (Conditional): the abstract Grönwall step `exp_decay_of_lsi`, and the PFG-shaped
  corollaries `exp_decay_idealVelocity` (exact `v⋆`), `exp_decay_approxVelocity` (velocity with
  relative weighted-L² error) and `exp_decay_idealVelocity_density` (concrete densities and scores).

## Assumed (named hypotheses, Conditional status)

* `KLFirstVariation`: `t ↦ KL t` is differentiable on `t ≥ 0` with derivative given by the
  FL-1 transport formula along the velocity actually used. This packages the continuity
  equation, its well-posedness and the boundary/integration-by-parts arguments (FL-1,
  FL-2), none of which is proved here.
* `LogSobolevAlong`: the log-Sobolev inequality `KL ≤ I / (2λ)` of the target, evaluated
  along the flow. This is an assumption on `p⋆` (the paper's LSI assumption); it is not
  proved in this file (the Gaussian case is `LogSobolevAlongGaussian.logSobolevAlong_gaussian`).

## What is NOT proved

* No PDE: existence, uniqueness or regularity of the PFG flow, the continuity equation, and the
  KL first-variation formula itself are hypotheses.
* No LSI is proved in this file; the Gaussian case is
  `LogSobolevAlongGaussian.logSobolevAlong_gaussian`.
* The paper's assumptions A1–A4, its approximation parameter and its exact constants are not
  reproduced here; the relative-error condition in `exp_decay_approxVelocity` is one natural
  sufficient condition, not necessarily the paper's.
* No finite-particle, discretisation or optimisation-error analysis.
-/

@[expose] public section

open Matrix MeasureTheory

namespace FormalizeSampling
namespace KLDecay

open SPD

variable {d : ℕ}

/-! ### Definitions -/

/-- The ideal PFG velocity field `v⋆(x) = H⁻¹ (sStar x - s x)`, i.e.
`H⁻¹ (∇log p⋆ - ∇log p)` when `s = ∇log p` and `sStar = ∇log p⋆`. -/
noncomputable def idealVelocity (H : Matrix (Fin d) (Fin d) ℝ)
    (s sStar : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  H⁻¹ *ᵥ (sStar x - s x)

/-- The relative Fisher information `∫ |s - sStar|² dμ`, i.e. `𝔼_p |∇log(p/p⋆)|²` when
`μ = p`, `s = ∇log p` and `sStar = ∇log p⋆`. (Lean's Bochner integral returns `0` for a
non-integrable integrand, so theorems using it assume integrability explicitly.) -/
noncomputable def relFisher (μ : Measure (Fin d → ℝ)) (s sStar : (Fin d → ℝ) → Fin d → ℝ) :
    ℝ :=
  ∫ x, (s x - sStar x) ⬝ᵥ (s x - sStar x) ∂μ

/-- The PFG quadratic objective in its projected (post integration-by-parts) form,
`J(f) = -∫ f ⬝ᵥ (sStar - s) dμ + ½ ∫ ‖f‖²_H dμ`. Identifying it with the Stein form
`-𝔼_p[div f + f ⬝ᵥ ∇log p⋆] + ½ 𝔼_p‖f‖²_H` is SE-1 and is not done here. -/
noncomputable def projectedObjective (H : Matrix (Fin d) (Fin d) ℝ) (μ : Measure (Fin d → ℝ))
    (s sStar f : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  -(∫ x, f x ⬝ᵥ (sStar x - s x) ∂μ) + (1 / 2) * ∫ x, sqNormH H (f x) ∂μ

/-- **Assumed KL first-variation formula (FL-1/FL-2 input, a hypothesis).**
Along a time-dependent law `μ t`, score field `s t`, target score `sStar` and velocity `v t`,
the function `KL` (standing for `t ↦ KL(p_t ‖ p⋆)`) has, for every `t ≥ 0`, the derivative
`d/dt KL(t) = ∫ v t x ⬝ᵥ (s t x - sStar x) dμ_t(x)`, the first variation of KL under transport
by `v t`. This packages the continuity equation `∂ₜ p_t = -div(p_t v_t)` and its analytic
justification, which are not proved in this file. -/
def KLFirstVariation (μ : ℝ → Measure (Fin d → ℝ)) (v s : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (KL : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt KL (∫ x, v t x ⬝ᵥ (s t x - sStar x) ∂(μ t)) t

/-- **Assumed log-Sobolev inequality along the flow (a hypothesis).** With constant `lam > 0`,
for every `t ≥ 0`, `KL t ≤ I(p_t ‖ p⋆) / (2 lam)` where `I` is the relative Fisher information
`relFisher (μ t) (s t) sStar`. This is the target's LSI evaluated at `p_t`; it is assumed, not
proved. -/
def LogSobolevAlong (lam : ℝ) (μ : ℝ → Measure (Fin d → ℝ)) (s : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (KL : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → KL t ≤ relFisher (μ t) (s t) sStar / (2 * lam)

/-! ### Pointwise facts about the ideal velocity -/

/-- For positive-definite `H`, `H v⋆(x) = sStar x - s x`. -/
theorem mulVec_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (s sStar : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    H *ᵥ idealVelocity H s sStar x = sStar x - s x :=
  mulVec_inv_mulVec hH _

/-- For positive-definite `H`, `‖v⋆(x)‖²_H = ‖s x - sStar x‖²_{H⁻¹}`. -/
theorem sqNormH_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (s sStar : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    sqNormH H (idealVelocity H s sStar x) = sqNormH H⁻¹ (s x - sStar x) := by
  rw [idealVelocity, (sqNormH_inv_mulVec hH _).2, ← sqNormH_neg, neg_sub]

/-- For positive-definite `H`, the FL-1 integrand along any velocity value `u` is
`u ⬝ᵥ (s x - sStar x) = -(u ⬝ᵥ H v⋆(x))`. -/
theorem dotProduct_score_diff_eq {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (s sStar : (Fin d → ℝ) → Fin d → ℝ) (x u : Fin d → ℝ) :
    u ⬝ᵥ (s x - sStar x) = -(u ⬝ᵥ (H *ᵥ idealVelocity H s sStar x)) := by
  rw [mulVec_idealVelocity hH, ← dotProduct_neg, neg_sub]

/-! ### (B, f) Exact dissipation along the ideal velocity (input to FL-2) -/

/-- **Exact dissipation algebra (input to FL-2).** For any matrix `H`, measure `μ` and
vector fields `s, sStar`, with `v⋆ = H⁻¹ (sStar - s)`:
`∫ v⋆ ⬝ᵥ (s - sStar) dμ = -∫ ‖s - sStar‖²_{H⁻¹} dμ`.
The identity holds pointwise, so no integrability is needed (if the integrands are not
integrable both sides are `0` by Lean's convention). -/
theorem integral_idealVelocity_dotProduct (H : Matrix (Fin d) (Fin d) ℝ)
    (μ : Measure (Fin d → ℝ)) (s sStar : (Fin d → ℝ) → Fin d → ℝ) :
    ∫ x, idealVelocity H s sStar x ⬝ᵥ (s x - sStar x) ∂μ =
      -∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ := by
  rw [← integral_neg]
  congr 1
  funext x
  rw [idealVelocity, dotProduct_comm, ← neg_sub (s x) (sStar x), Matrix.mulVec_neg,
    dotProduct_neg, sqNormH]

/-- **Ideal PFG dissipates KL (input to FL-2).** For positive-definite `H`, the FL-1 rate
along the ideal velocity is nonpositive: `∫ v⋆ ⬝ᵥ (s - sStar) dμ ≤ 0`. -/
theorem integral_idealVelocity_dotProduct_nonpos {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (μ : Measure (Fin d → ℝ)) (s sStar : (Fin d → ℝ) → Fin d → ℝ) :
    ∫ x, idealVelocity H s sStar x ⬝ᵥ (s x - sStar x) ∂μ ≤ 0 := by
  rw [integral_idealVelocity_dotProduct, neg_nonpos]
  exact integral_nonneg fun x => sqNormH_nonneg (inv_posDef hH) _

/-- **Dissipation versus Fisher information.** Let `H` be positive definite with
`uᵀ H u ≤ M |u|²` for all `u` (`M > 0`), and assume `‖s - sStar‖²_{H⁻¹}` and `|s - sStar|²`
are `μ`-integrable. Then `(1/M) relFisher μ s sStar ≤ ∫ ‖s - sStar‖²_{H⁻¹} dμ`. -/
theorem fisher_le_dissipation {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u))
    {μ : Measure (Fin d → ℝ)} {s sStar : (Fin d → ℝ) → Fin d → ℝ}
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (hfisher : Integrable (fun x => (s x - sStar x) ⬝ᵥ (s x - sStar x)) μ) :
    (1 / M) * relFisher μ s sStar ≤ ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ := by
  rw [relFisher, ← integral_const_mul]
  exact integral_mono (hfisher.const_mul _) hdiss fun x =>
    inv_lower_bound_of_upper_bound hH hM hspec _

/-- **Ideal PFG rate bounded by Fisher information.** Under the hypotheses of
`fisher_le_dissipation`, `∫ v⋆ ⬝ᵥ (s - sStar) dμ ≤ -(1/M) relFisher μ s sStar`. -/
theorem ideal_rate_le_neg_fisher {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u))
    {μ : Measure (Fin d → ℝ)} {s sStar : (Fin d → ℝ) → Fin d → ℝ}
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (hfisher : Integrable (fun x => (s x - sStar x) ⬝ᵥ (s x - sStar x)) μ) :
    ∫ x, idealVelocity H s sStar x ⬝ᵥ (s x - sStar x) ∂μ ≤ -(1 / M) * relFisher μ s sStar := by
  rw [integral_idealVelocity_dotProduct]
  have := fisher_le_dissipation hH hM hspec hdiss hfisher
  linarith

/-! ### (B, e) FL-3: approximate minimisers still dissipate -/

/-- **FL-3, exact form.** Let `H` be positive definite and `f, v⋆` vector fields with
`f ⬝ᵥ H v⋆`, `‖v⋆‖²_H`, `‖f‖²_H` and `‖f - v⋆‖²_H` all `μ`-integrable. Then
`-∫ f ⬝ᵥ H v⋆ dμ = -½ ∫ ‖v⋆‖²_H dμ - ½ ∫ ‖f‖²_H dμ + ½ ∫ ‖f - v⋆‖²_H dμ`. -/
theorem neg_integral_dotProduct_mulVec_eq {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f vStar : (Fin d → ℝ) → Fin d → ℝ)
    (hv : Integrable (fun x => sqNormH H (vStar x)) μ)
    (hf : Integrable (fun x => sqNormH H (f x)) μ)
    (hfv : Integrable (fun x => sqNormH H (f x - vStar x)) μ) :
    -∫ x, f x ⬝ᵥ (H *ᵥ vStar x) ∂μ =
      -(1 / 2) * ∫ x, sqNormH H (vStar x) ∂μ - (1 / 2) * ∫ x, sqNormH H (f x) ∂μ +
        (1 / 2) * ∫ x, sqNormH H (f x - vStar x) ∂μ := by
  have h1 : Integrable
      (fun x => -(1 / 2) * sqNormH H (vStar x) - (1 / 2) * sqNormH H (f x)) μ :=
    (hv.const_mul _).sub (hf.const_mul _)
  have h2 : Integrable (fun x => (1 / 2) * sqNormH H (f x - vStar x)) μ := hfv.const_mul _
  calc -∫ x, f x ⬝ᵥ (H *ᵥ vStar x) ∂μ =
        ∫ x, (-(1 / 2) * sqNormH H (vStar x) - (1 / 2) * sqNormH H (f x)) +
          (1 / 2) * sqNormH H (f x - vStar x) ∂μ := by
        rw [← integral_neg]
        congr 1
        funext x
        exact neg_dotProduct_mulVec_eq (transpose_eq_of_posDef hH) (f x) (vStar x)
    _ = _ := by
        rw [integral_add h1 h2, integral_sub (hv.const_mul _) (hf.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]

/-- **FL-3 (approximate functional minimiser ⇒ quantitative KL decrease).** Let `H` be
positive definite, `μ` a measure and `f, v⋆` vector fields such that `f ⬝ᵥ H v⋆`, `‖v⋆‖²_H` and
`‖f - v⋆‖²_H` are `μ`-integrable. If the KL derivative along `f` is
`D(f) = -∫ f ⬝ᵥ H v⋆ dμ` (the FL-1 formula with `v⋆ = H⁻¹(∇log p⋆ - ∇log p)`), then
`D(f) ≤ -½ ∫ ‖v⋆‖²_H dμ + ½ ∫ ‖f - v⋆‖²_H dμ`.
Since the optimisation gap of the PFG objective is `J(f) - J(v⋆) = ½ ∫ ‖f - v⋆‖²_H dμ`
(`projectedObjective_sub_eq`), the gap controls the loss of dissipation relative to the ideal
rate `-½ ∫ ‖v⋆‖²_H dμ`. -/
theorem neg_integral_dotProduct_mulVec_le {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f vStar : (Fin d → ℝ) → Fin d → ℝ)
    (hfv' : Integrable (fun x => f x ⬝ᵥ (H *ᵥ vStar x)) μ)
    (hv : Integrable (fun x => sqNormH H (vStar x)) μ)
    (hfv : Integrable (fun x => sqNormH H (f x - vStar x)) μ) :
    -∫ x, f x ⬝ᵥ (H *ᵥ vStar x) ∂μ ≤
      -(1 / 2) * ∫ x, sqNormH H (vStar x) ∂μ + (1 / 2) * ∫ x, sqNormH H (f x - vStar x) ∂μ := by
  rw [← integral_neg, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hv.const_mul _) (hfv.const_mul _)]
  exact integral_mono hfv'.neg ((hv.const_mul _).add (hfv.const_mul _)) fun x =>
    neg_dotProduct_mulVec_le hH (f x) (vStar x)

/-- **FL-3, score form.** Let `H` be positive definite, `v⋆ = H⁻¹(sStar - s)` and `f` a
velocity field with `f ⬝ᵥ (s - sStar)`, `‖s - sStar‖²_{H⁻¹}` and `‖f - v⋆‖²_H` integrable. Then
the FL-1 KL rate along `f` satisfies
`∫ f ⬝ᵥ (s - sStar) dμ ≤ -½ ∫ ‖s - sStar‖²_{H⁻¹} dμ + ½ ∫ ‖f - v⋆‖²_H dμ`. -/
theorem transport_rate_le {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f s sStar : (Fin d → ℝ) → Fin d → ℝ)
    (hrate : Integrable (fun x => f x ⬝ᵥ (s x - sStar x)) μ)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (herr : Integrable (fun x => sqNormH H (f x - idealVelocity H s sStar x)) μ) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ ≤
      -(1 / 2) * ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ +
        (1 / 2) * ∫ x, sqNormH H (f x - idealVelocity H s sStar x) ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hdiss.const_mul _) (herr.const_mul _)]
  refine integral_mono hrate ((hdiss.const_mul _).add (herr.const_mul _)) fun x => ?_
  have h := neg_dotProduct_mulVec_le hH (f x) (idealVelocity H s sStar x)
  rw [sqNormH_idealVelocity hH, ← dotProduct_score_diff_eq hH] at h
  exact h

/-- **Optimisation gap of the projected PFG objective.** Let `H` be positive definite and
`v⋆ = H⁻¹(sStar - s)`. If `f ⬝ᵥ (sStar - s)`, `‖f‖²_H` and `‖v⋆‖²_H` are `μ`-integrable, then
`J(f) - J(v⋆) = ½ ∫ ‖f - v⋆‖²_H dμ` for `J = projectedObjective H μ s sStar`. -/
theorem projectedObjective_sub_eq {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f s sStar : (Fin d → ℝ) → Fin d → ℝ)
    (hfg : Integrable (fun x => f x ⬝ᵥ (sStar x - s x)) μ)
    (hf : Integrable (fun x => sqNormH H (f x)) μ)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H s sStar x)) μ) :
    projectedObjective H μ s sStar f - projectedObjective H μ s sStar (idealVelocity H s sStar) =
      (1 / 2) * ∫ x, sqNormH H (f x - idealVelocity H s sStar x) ∂μ := by
  have hJf := integral_completion_of_squares hH f (fun x => sStar x - s x) hfg hf hv
  have hvv : ∫ x, idealVelocity H s sStar x ⬝ᵥ (sStar x - s x) ∂μ =
      ∫ x, sqNormH H (idealVelocity H s sStar x) ∂μ := by
    congr 1
    funext x
    rw [sqNormH, mulVec_idealVelocity hH]
  simp only [projectedObjective, idealVelocity] at hJf hvv ⊢
  rw [hJf, hvv]
  ring

/-- **FL-3, loss of dissipation ≤ optimisation gap.** Under the hypotheses of
`transport_rate_le` and `projectedObjective_sub_eq` (integrability of `f ⬝ᵥ (s - sStar)`,
`‖f‖²_H`, `‖s - sStar‖²_{H⁻¹}` and `‖f - v⋆‖²_H`), the KL rate along `f` satisfies
`∫ f ⬝ᵥ (s - sStar) dμ ≤ -½ ∫ ‖s - sStar‖²_{H⁻¹} dμ + (J(f) - J(v⋆))`. -/
theorem transport_rate_le_objective_gap {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {μ : Measure (Fin d → ℝ)} (f s sStar : (Fin d → ℝ) → Fin d → ℝ)
    (hrate : Integrable (fun x => f x ⬝ᵥ (s x - sStar x)) μ)
    (hf : Integrable (fun x => sqNormH H (f x)) μ)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (herr : Integrable (fun x => sqNormH H (f x - idealVelocity H s sStar x)) μ) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ ≤
      -(1 / 2) * ∫ x, sqNormH H⁻¹ (s x - sStar x) ∂μ +
        (projectedObjective H μ s sStar f -
          projectedObjective H μ s sStar (idealVelocity H s sStar)) := by
  have hfg : Integrable (fun x => f x ⬝ᵥ (sStar x - s x)) μ := by
    refine hrate.neg.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, ← dotProduct_neg, neg_sub]
  have hv : Integrable (fun x => sqNormH H (idealVelocity H s sStar x)) μ := by
    refine hdiss.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [sqNormH_idealVelocity hH]
  rw [projectedObjective_sub_eq hH f s sStar hfg hf hv]
  exact transport_rate_le hH f s sStar hrate hdiss herr

/-! ### (C) FL-4: conditional exponential decay -/

/-- **Abstract Grönwall step under an assumed log-Sobolev-type inequality (FL-4 skeleton).**
Let `K K' I : ℝ → ℝ`, `c > 0`, `lam > 0`, and for every `t ≥ 0` assume
(i) `HasDerivAt K (K' t) t`, (ii) the dissipation bound `K' t ≤ -c * I t`, and
(iii) the **assumed log-Sobolev-type inequality** `K t ≤ I t / (2 * lam)`.
Then `K t ≤ exp(-2 lam c t) K 0` for all `t ≥ 0`. No PDE is involved; the LSI is a
hypothesis. -/
theorem exp_decay_of_lsi {K K' I : ℝ → ℝ} {c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt K (K' t) t)
    (hdiss : ∀ t, 0 ≤ t → K' t ≤ -c * I t)
    (hLSI : ∀ t, 0 ≤ t → K t ≤ I t / (2 * lam)) :
    ∀ t, 0 ≤ t → K t ≤ Real.exp (-2 * lam * c * t) * K 0 := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := K) (f' := K') (δ := K 0)
    (K := -(2 * lam * c)) (ε := 0) (a := 0) (b := t)
    (fun s hs => (hderiv s hs.1).continuousAt.continuousWithinAt)
    (fun s hs r hr => ((hderiv s hs.1).hasDerivWithinAt).liminf_right_slope_le hr) le_rfl
    (fun s hs => by
      have h1 := hdiss s hs.1
      have h2 := hLSI s hs.1
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith) t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  calc K t ≤ K 0 * Real.exp (-(2 * lam * c) * t) := h
    _ = _ := by ring_nf

/-- **FL-4, PFG exponential KL decay (Conditional).** Let `H` be positive definite with
`uᵀ H u ≤ M |u|²` for all `u` (`M > 0`, i.e. `λ_max(H) ≤ M`; such an `M` always exists by
`SPD.exists_sqNormH_le`), and `lam > 0`. Along a law `μ t` with score field `s t`, target score
`sStar` and ideal PFG velocity `v⋆_t = H⁻¹(sStar - s t)`, assume for every `t ≥ 0`:
* `KLFirstVariation`: `d/dt KL(t) = ∫ v⋆_t ⬝ᵥ (s t - sStar) dμ_t` (**assumed** FL-1/FL-2);
* integrability of `‖s t - sStar‖²_{H⁻¹}` and of `|s t - sStar|²` under `μ t`;
* `LogSobolevAlong lam`: `KL(t) ≤ relFisher(μ t, s t, sStar) / (2 lam)` (**assumed** LSI).
Then `KL(t) ≤ exp(-2 lam t / M) KL(0)` for all `t ≥ 0`. Status: Conditional (the KL derivative
formula and the LSI are hypotheses). -/
theorem exp_decay_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M lam : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hlam : 0 < lam)
    {μ : ℝ → Measure (Fin d → ℝ)} {s : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sStar : (Fin d → ℝ) → Fin d → ℝ} {KL : ℝ → ℝ}
    (hKL : KLFirstVariation μ (fun t => idealVelocity H (s t) sStar) s sStar KL)
    (hdiss : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H⁻¹ (s t x - sStar x)) (μ t))
    (hfisher : ∀ t, 0 ≤ t →
      Integrable (fun x => (s t x - sStar x) ⬝ᵥ (s t x - sStar x)) (μ t))
    (hLSI : LogSobolevAlong lam μ s sStar KL) :
    ∀ t, 0 ≤ t → KL t ≤ Real.exp (-2 * lam * t / M) * KL 0 := by
  have key := exp_decay_of_lsi (K := KL)
    (K' := fun t => ∫ x, idealVelocity H (s t) sStar x ⬝ᵥ (s t x - sStar x) ∂(μ t))
    (I := fun t => relFisher (μ t) (s t) sStar) (c := 1 / M) (by positivity) hlam hKL
    (fun t ht => ideal_rate_le_neg_fisher hH hM hspec (hdiss t ht) (hfisher t ht)) hLSI
  intro t ht
  have h := key t ht
  have he : -2 * lam * (1 / M) * t = -2 * lam * t / M := by ring
  rwa [he] at h

/-- **FL-4, approximate PFG velocity (Conditional).** Same setting as `exp_decay_idealVelocity`,
but
the flow moves along an arbitrary velocity `f t` whose weighted-L² error relative to the ideal
velocity is a fraction of the ideal dissipation: for some `κ > 0` and all `t ≥ 0`,
`∫ ‖f t - v⋆_t‖²_H dμ_t ≤ (1 - κ) ∫ ‖s t - sStar‖²_{H⁻¹} dμ_t`.
Assume `KLFirstVariation` along `f` (**assumed** FL-1), integrability of
`f t ⬝ᵥ (s t - sStar)`, `‖s t - sStar‖²_{H⁻¹}`, `‖f t - v⋆_t‖²_H` and `|s t - sStar|²`, and the
**assumed** LSI `LogSobolevAlong lam`. Then `KL(t) ≤ exp(-lam κ t / M) KL(0)` for `t ≥ 0`.
The relative-error condition is a sufficient condition chosen here, not the paper's A1–A4. -/
theorem exp_decay_approxVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M lam κ : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hκ : 0 < κ) {μ : ℝ → Measure (Fin d → ℝ)} {f s : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sStar : (Fin d → ℝ) → Fin d → ℝ} {KL : ℝ → ℝ}
    (hKL : KLFirstVariation μ f s sStar KL)
    (hrate : ∀ t, 0 ≤ t → Integrable (fun x => f t x ⬝ᵥ (s t x - sStar x)) (μ t))
    (hdiss : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H⁻¹ (s t x - sStar x)) (μ t))
    (herr : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H (f t x - idealVelocity H (s t) sStar x)) (μ t))
    (hfisher : ∀ t, 0 ≤ t →
      Integrable (fun x => (s t x - sStar x) ⬝ᵥ (s t x - sStar x)) (μ t))
    (happrox : ∀ t, 0 ≤ t →
      ∫ x, sqNormH H (f t x - idealVelocity H (s t) sStar x) ∂(μ t) ≤
        (1 - κ) * ∫ x, sqNormH H⁻¹ (s t x - sStar x) ∂(μ t))
    (hLSI : LogSobolevAlong lam μ s sStar KL) :
    ∀ t, 0 ≤ t → KL t ≤ Real.exp (-(lam * κ * t / M)) * KL 0 := by
  have hdis : ∀ t, 0 ≤ t → ∫ x, f t x ⬝ᵥ (s t x - sStar x) ∂(μ t) ≤
      -(κ / (2 * M)) * relFisher (μ t) (s t) sStar := by
    intro t ht
    have h1 := transport_rate_le hH (f t) (s t) sStar (hrate t ht) (hdiss t ht) (herr t ht)
    have h2 := happrox t ht
    have h3 := fisher_le_dissipation hH hM hspec (hdiss t ht) (hfisher t ht)
    have h4 : -(κ / (2 * M)) * relFisher (μ t) (s t) sStar =
        -(κ / 2) * ((1 / M) * relFisher (μ t) (s t) sStar) := by
      field_simp
    rw [h4]
    nlinarith
  have key := exp_decay_of_lsi (K := KL)
    (K' := fun t => ∫ x, f t x ⬝ᵥ (s t x - sStar x) ∂(μ t))
    (I := fun t => relFisher (μ t) (s t) sStar) (c := κ / (2 * M)) (by positivity) hlam hKL
    hdis hLSI
  intro t ht
  have h := key t ht
  have he : -2 * lam * (κ / (2 * M)) * t = -(lam * κ * t / M) := by
    field_simp
  rwa [he] at h

/-- The measure `p(x) dx` with Lebesgue density `p` (as `volume.withDensity`; negative values
of `p` are truncated to `0` by `ENNReal.ofReal`). It is a probability measure when `p` is a
probability density; this is not required by the definition. The same measure is
`NoiseScore.densityMeasure` (`Flow/DiPernaLionsUniqueness.lean`) and
`LogSobolevAlongGaussian.lawOf` (`Flow/LogSobolevAlongGaussian.lean`); the identifications are
`NoiseScore.densityMeasure_eq_klDecay_densityMeasure` and
`LogSobolevAlongGaussian.lawOf_eq_densityMeasure`. -/
noncomputable def densityMeasure (p : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (p x)

/-- The Kullback–Leibler divergence `KL(p ‖ p⋆) = ∫ log(p/p⋆) p dx` for Lebesgue densities.
It has its intended meaning when `p` is a probability density, `p⋆ > 0` and the integrand is
integrable (Lean's conventions `log 0 = 0`, `x / 0 = 0` and the Bochner integral of a
non-integrable function being `0` apply otherwise). -/
noncomputable def klDivDensity (p pStar : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, Real.log (p x / pStar x) ∂densityMeasure p

/-- **FL-4 for densities (Conditional).** For a family of Lebesgue densities `p t` and a target
density `pStar`, with the shared state scores `score (p t) = ∇log p_t` and
`score pStar = ∇log p⋆`, positive-definite `H` with `uᵀ H u ≤ M |u|²` (`M > 0`) and `lam > 0`:
if `t ↦ KL(p_t ‖ p⋆)` satisfies the **assumed** first-variation formula along the ideal PFG
velocity `H⁻¹(∇log p⋆ - ∇log p_t)`, the integrability conditions of `exp_decay_idealVelocity` hold
under `p_t dx`, and the target satisfies the **assumed** LSI with constant `lam` along the flow,
then `KL(p_t ‖ p⋆) ≤ exp(-2 lam t / M) KL(p_0 ‖ p⋆)` for all `t ≥ 0`. -/
theorem exp_decay_idealVelocity_density {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M lam : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (p : ℝ → (Fin d → ℝ) → ℝ) (pStar : (Fin d → ℝ) → ℝ)
    (hKL : KLFirstVariation (fun t => densityMeasure (p t))
      (fun t => idealVelocity H (score (p t)) (score pStar)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar))
    (hdiss : ∀ t, 0 ≤ t → Integrable
      (fun x => sqNormH H⁻¹ (score (p t) x - score pStar x)) (densityMeasure (p t)))
    (hfisher : ∀ t, 0 ≤ t → Integrable
      (fun x => (score (p t) x - score pStar x) ⬝ᵥ (score (p t) x - score pStar x))
      (densityMeasure (p t)))
    (hLSI : LogSobolevAlong lam (fun t => densityMeasure (p t)) (fun t => score (p t))
      (score pStar) (fun t => klDivDensity (p t) pStar)) :
    ∀ t, 0 ≤ t → klDivDensity (p t) pStar ≤
      Real.exp (-2 * lam * t / M) * klDivDensity (p 0) pStar :=
  exp_decay_idealVelocity hH hM hspec hlam hKL hdiss hfisher hLSI

end KLDecay
end FormalizeSampling
