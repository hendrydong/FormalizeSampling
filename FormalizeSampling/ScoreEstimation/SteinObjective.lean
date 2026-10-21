module

public import FormalizeSampling.Flow.KLDecay
public import FormalizeSampling.Identities.DensityStein
public import FormalizeSampling.ScoreEstimation.FeatureClass

/-!
# The PFG functional objective: Proposition 1 and the ideal direction
Registry ID: **SE-1** (the PFG quadratic Stein objective equals the weighted projection objective,
and the ideal PFG direction is its a.e.-unique minimiser), i.e. **PFG Proposition 1** (argmin
equivalence); the projection form for linear feature classes is part of **SE-2**. Paper: Dong, Wang,
Lin, Zhang, *Particle-based Variational Inference with Preconditioned Functional Gradient Flow*,
ICLR 2023 (arXiv 2211.13954 v2), Section 2: Eq. (4) (regularised functional-gradient objective), Eq.
(6) (`Q(f) = ½ ∫ p ‖f‖²_H`), Proposition 1 / Eq. (7) (proof in App. A.3, Eqs. (15)-(18)).

## Setting and conventions

* State space `Fin d → ℝ` with Lebesgue measure; `p : (Fin d → ℝ) → ℝ` is the current density
  `p_t` at a **fixed** time, assumed strictly positive everywhere and differentiable (`C¹` in
  the discharged statements). Normalisation `∫ p = 1` is never used: all integrals are Lebesgue
  integrals `∫ g(x) p(x) dx`, which equal `∫ g d(p dx)` for the measure `densityMeasure p`
  (`integral_densityMeasure`).
* `sStar` is an arbitrary vector field standing for the target score `∇log p⋆`
  (in `Flow/KLDissipation.lean` it is `score pStar`). The state score of `p` is the shared
  `score p = ∇log p`.
* `H` is a constant positive-definite matrix (`H.PosDef`), independent of `x`. The paper allows
  `H = H_t` to depend on time; at the fixed time considered here that is a constant matrix.
* `steinObjective H p sStar f = -∫ (div f + f ⬝ᵥ sStar) p + ½ ∫ ‖f‖²_H p` is Eq. (4) with the
  regulariser `Q` of Eq. (6) (including the factor `½` of Eq. (6)).
* The ideal direction is `v⋆ = idealVelocity H (score p) sStar = H⁻¹ (sStar - ∇log p)`, i.e.
  `H⁻¹ ∇ln(p⋆/p)` (reused from `Flow/KLDecay.lean`). Note
  `‖v⋆‖²_H = ‖∇log p - sStar‖²_{H⁻¹}` (`KLDecay.sqNormH_idealVelocity`), so
  `∫ ‖v⋆‖²_H p` is the `H⁻¹`-weighted relative Fisher information `I_{H⁻¹}`.
* `projectionObjective H p sStar f = ½ ∫ ‖f - v⋆‖²_H p` is the objective of Eq. (7).
* `Admissible H p sStar f` bundles the explicit regularity of a velocity field: differentiable
  coordinates, the three integrability hypotheses of the density Stein identity (ID-2, used
  coordinatewise) and finiteness of `∫ (f ⬝ᵥ sStar) p` and of `Q(f)`. It states explicitly the
  Stein integration by parts `∫ p ∇·f = -∫ p f ⬝ ∇ln p` for every `f ∈ F` used in the proof, and
  plays the role of the [A1] tail condition (stated in the paper with `p⋆`; here with `p_t`).

## Main results

* **SE-1, Proposition 1 as a value identity (App. A.3, Eqs. (15)-(18)).**
  `steinObjective_eq`: for admissible `f` and finite relative Fisher information
  `∫ ‖v⋆‖²_H p < ∞`, `steinObjective = ½ ∫ ‖f - v⋆‖²_H p - ½ ∫ ‖v⋆‖²_H p` (general version (ii));
  `steinObjective_eq_projectionObjective_sub` restates it with `projectionObjective`.
  `steinObjective_eq_of_hasCompactSupport`: the same for `f` with `C¹` compactly supported
  coordinates, `p` positive `C¹` and `sStar` continuous, with only finite Fisher information
  assumed (version (i)); `admissible_of_hasCompactSupport` discharges admissibility
  (`admissible_zero`: the zero field is admissible with no hypothesis at all).
  Nonvacuity: `steinObjective_score_eq_of_hasCompactSupport` (case `sStar = ∇log p`, where all
  hypotheses hold for every positive `C¹` `p`).
* **SE-1.** `neg_half_le_steinObjective` (`steinObjective ≥ -½ ∫ ‖v⋆‖²_H p` on admissible
  fields), `steinObjective_eq_neg_half_iff` (equality iff `f = v⋆` Lebesgue-a.e.),
  `steinObjective_eq_neg_half_iff_ae_densityMeasure` (the same, `p dx`-a.e.),
  `ae_densityMeasure_iff` (Lebesgue-a.e. = `p dx`-a.e. since `p > 0`),
  `steinObjective_idealVelocity` (the value at `v⋆` when `v⋆` is itself admissible) and
  `isMinOn_iff_ae_eq_idealVelocity` (if `v⋆ ∈ F`, the minimisers over `F` are exactly the
  admissible fields `= v⋆` a.e.; this is the paper's "well-specified `F`" remark after Eq. (5),
  generalised to any `H`).
* **PFG Proposition 1, as stated in the paper.** `isMinOn_steinObjective_iff`: for **any** set
  `F` of admissible fields and `g ∈ F`, `g` minimises `steinObjective` over `F` iff it minimises
  `projectionObjective` over `F`; `steinObjective_sub_steinObjective` (the two objectives differ by
  a constant on admissible fields). No minimiser is claimed to exist.
* **Finite-dimensional linear class `F = {x ↦ W ψ(x)}`.** `steinObjective_featureField`: the
  objective on `W ψ` *is* `FeatureClass.popSteinObjective H (densityMeasure p) sStar ψ W` of
  `ScoreEstimation/FeatureClass.lean` (the definitions match exactly once `μ = p dx`).
  Hence `featureField_isMinimiser_iff_normalEq` (minimisers ⇔ normal equations
  `H W Σ = G`, a corollary of `FeatureClass.popStein_isMinimiser_iff_normalEq`) and
  `featureField_eq_iff_of_normalEq` (a.e. uniqueness of the minimising field). With the Stein
  identity, `popSteinMatrix_eq_integral_score_sub` rewrites `G` as `∫ (sStar - ∇log p) ψᵀ p`,
  and `featureField_isMinimiser_iff_projection` gives the normal equations of the weighted
  least-squares projection of `v⋆` onto the class: `W Σ = ∫ v⋆ ψᵀ p`.
* Helpers: `sqNormH_sub_idealVelocity_mul` (pointwise completion of squares, Eqs. (16)-(18)),
  `Admissible.integrable_divergence_mul`, `Admissible.integrable_dotProduct_score_mul`,
  `Admissible.integrable_dotProduct_sub_score`, `Admissible.integral_stein`,
  `Admissible.integrable_sqNormH_sub`, `integrable_sqNormH_idealVelocity_iff`,
  `integral_densityMeasure`, `integrable_densityMeasure_iff` (integrals and integrability
  against `p dx`).

Status: **Verified** (all hypotheses are explicit regularity or integrability conditions).

## Regularity hypotheses stated explicitly here

* Finite relative Fisher information `∫ ‖v⋆‖²_H p < ∞` (argument `hv` / `hfisher`), used in
  the Lean proof of the completion of squares (Eq. (17)). The Lean statement assumes it so that
  the right-hand side of the identity is a difference of finite integrals: without it that side
  is `∞ - ∞` mathematically and `0 - 0` under Lean's junk convention for the Bochner integral,
  while the left-hand side is finite for compactly supported `f`.
* Stein integration by parts for every `f ∈ F` (through `Admissible`), with boundary terms
  controlled by integrability under `p` rather than by the [A1] tail condition under `p⋆`.
* `p > 0` everywhere and differentiable; `H` symmetric positive definite and `x`-independent.

## What is NOT proved here

* **Existence of a minimiser** over a nonlinear or non-convex class `F` is not formalised
  here. Proposition 1 is proved as an equivalence of the two minimisation problems over an
  arbitrary `F`; for the linear feature class a minimiser exists iff the normal equations are
  solvable.
* `v⋆` itself need not be admissible (it is differentiable for instance if `p` is `C²` and
  `sStar` is `C¹`, and it is typically not compactly supported); `steinObjective_idealVelocity`
  and `isMinOn_iff_ae_eq_idealVelocity` assume it.
* Uniqueness is only almost everywhere; nothing is said about densities that vanish somewhere,
  weakly differentiable densities, or infinite-dimensional (RKHS / Mercer) classes.
* No dynamics: KL dissipation, Proposition 2 and Theorem 1 are in
  `Flow/KLDissipation.lean` (Theorem 1) or not formalised (Proposition 2).
* The paper's [A1] positive-definiteness of the discrepancy and its closedness clause are not
  used here.
-/

@[expose] public section

open Matrix MeasureTheory

namespace FormalizeSampling
namespace SteinObjective

open SPD KLDecay

variable {d : ℕ}

/-! ### Definitions -/

/-- **The PFG objective (paper Eq. (4) with `Q` of Eq. (6)).** For a preconditioner `H`, a
density `p`, a target score field `sStar` and a velocity field `f`,
`steinObjective H p sStar f = -∫ (div f + f ⬝ᵥ sStar) p dx + ½ ∫ ‖f‖²_H p dx`
(Lebesgue integrals; Lean's Bochner integral is `0` for non-integrable integrands, so results
about it assume integrability explicitly, see `Admissible`). -/
noncomputable def steinObjective (H : Matrix (Fin d) (Fin d) ℝ) (p : (Fin d → ℝ) → ℝ)
    (sStar f : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  -(∫ x, (divergence f x + f x ⬝ᵥ sStar x) * p x) + (1 / 2) * ∫ x, sqNormH H (f x) * p x

/-- **The weighted projection objective of Eq. (7).** `½ ∫ ‖f - v⋆‖²_H p dx` with
`v⋆ = idealVelocity H (score p) sStar = H⁻¹ (sStar - ∇log p)`. -/
noncomputable def projectionObjective (H : Matrix (Fin d) (Fin d) ℝ) (p : (Fin d → ℝ) → ℝ)
    (sStar f : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  (1 / 2) * ∫ x, sqNormH H (f x - idealVelocity H (score p) sStar x) * p x

/-- **Admissible velocity field** for the PFG objective under the density `p` (explicit
regularity, not a modelling assumption): every coordinate `fᵢ` is differentiable; for every `i`
the functions `(∂ᵢ fᵢ) p`, `fᵢ (∂ᵢ p)` and `fᵢ p` are Lebesgue integrable (the hypotheses of the
density Stein identity ID-2, whose boundary terms they control); and `(f ⬝ᵥ sStar) p` and
`‖f‖²_H p` are Lebesgue integrable (both terms of the objective are finite). Every `C¹` field
with compact support is admissible when `p` is `C¹` and `sStar` is continuous
(`admissible_of_hasCompactSupport`). -/
structure Admissible (H : Matrix (Fin d) (Fin d) ℝ) (p : (Fin d → ℝ) → ℝ)
    (sStar f : (Fin d → ℝ) → Fin d → ℝ) : Prop where
  /-- Every coordinate `fᵢ` is differentiable. -/
  differentiable : ∀ i, Differentiable ℝ (fun y => f y i)
  /-- `(∂ᵢ fᵢ) p` is Lebesgue integrable for every `i`. -/
  integrable_partialDeriv_mul :
    ∀ i, Integrable (fun x => partialDeriv i (fun y => f y i) x * p x)
  /-- `fᵢ (∂ᵢ p)` is Lebesgue integrable for every `i`. -/
  integrable_mul_partialDeriv : ∀ i, Integrable (fun x => f x i * partialDeriv i p x)
  /-- `fᵢ p` is Lebesgue integrable for every `i` (controls the boundary terms). -/
  integrable_mul : ∀ i, Integrable (fun x => f x i * p x)
  /-- `(f ⬝ᵥ sStar) p` is Lebesgue integrable. -/
  integrable_dotProduct : Integrable (fun x => (f x ⬝ᵥ sStar x) * p x)
  /-- `‖f‖²_H p` is Lebesgue integrable (finite regulariser `Q(f)`). -/
  integrable_sqNormH : Integrable (fun x => sqNormH H (f x) * p x)

/-! ### Pointwise algebra and integrability bookkeeping -/

/-- **Pointwise completion of squares (Eqs. (16)-(18)), weighted by `p`.** For positive-definite
`H`, with `v⋆ = H⁻¹ (sStar - ∇log p)`:
`‖f - v⋆‖²_H p = (-2 (f ⬝ᵥ (sStar - ∇log p)) p + ‖f‖²_H p) + ‖v⋆‖²_H p` at every `x`. -/
theorem sqNormH_sub_idealVelocity_mul {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (p : (Fin d → ℝ) → ℝ) (sStar f : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    sqNormH H (f x - idealVelocity H (score p) sStar x) * p x =
      (-2 * ((f x ⬝ᵥ (sStar x - score p x)) * p x) + sqNormH H (f x) * p x) +
        sqNormH H (idealVelocity H (score p) sStar x) * p x := by
  have h := completion_of_squares hH (f x) (sStar x - score p x)
  simp only [idealVelocity] at h ⊢
  have h2 : sqNormH H (f x - H⁻¹ *ᵥ (sStar x - score p x)) =
      -2 * (f x ⬝ᵥ (sStar x - score p x)) + sqNormH H (f x) +
        sqNormH H (H⁻¹ *ᵥ (sStar x - score p x)) := by linarith
  rw [h2]
  ring

/-- For an admissible field `f`, `(div f) p` is Lebesgue integrable. -/
theorem Admissible.integrable_divergence_mul {H : Matrix (Fin d) (Fin d) ℝ}
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ} (hf : Admissible H p sStar f) :
    Integrable (fun x => divergence f x * p x) := by
  refine (integrable_finsetSum Finset.univ fun i _ => hf.integrable_partialDeriv_mul i).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [divergence, Finset.sum_mul]

/-- For an admissible field `f` and a positive differentiable `p`, `(f ⬝ᵥ ∇log p) p` is
Lebesgue integrable (it equals `∑ᵢ fᵢ ∂ᵢp` pointwise). -/
theorem Admissible.integrable_dotProduct_score_mul {H : Matrix (Fin d) (Fin d) ℝ}
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ} (hf : Admissible H p sStar f)
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) :
    Integrable (fun x => (f x ⬝ᵥ score p x) * p x) := by
  refine (integrable_finsetSum Finset.univ fun i _ => hf.integrable_mul_partialDeriv i).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, score_mul_self_of_pos (hp x) (hpos x)]

/-- For an admissible field `f` and a positive differentiable `p`,
`(f ⬝ᵥ (sStar - ∇log p)) p` is Lebesgue integrable. -/
theorem Admissible.integrable_dotProduct_sub_score {H : Matrix (Fin d) (Fin d) ℝ}
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ} (hf : Admissible H p sStar f)
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) :
    Integrable (fun x => (f x ⬝ᵥ (sStar x - score p x)) * p x) := by
  refine (hf.integrable_dotProduct.sub (hf.integrable_dotProduct_score_mul hpos hp)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, dotProduct_sub, sub_mul]

/-- **Stein step of Proposition 1 (Eq. (15) to Eq. (16)).** For an admissible field `f` and a
positive differentiable `p`, the Stein term of the objective is a transport term:
`∫ (div f + f ⬝ᵥ sStar) p = ∫ (f ⬝ᵥ (sStar - ∇log p)) p`. This is the density Stein identity
`∫ (div f) p = -∫ (f ⬝ᵥ ∇log p) p` (ID-2, `DensityStein`) plus linearity. -/
theorem Admissible.integral_stein {H : Matrix (Fin d) (Fin d) ℝ}
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ} (hf : Admissible H p sStar f)
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) :
    ∫ x, (divergence f x + f x ⬝ᵥ sStar x) * p x =
      ∫ x, (f x ⬝ᵥ (sStar x - score p x)) * p x := by
  have hstein := DensityStein.integral_divergence_mul_eq_neg_integral_dotProduct_score hpos hp
    hf.differentiable hf.integrable_partialDeriv_mul hf.integrable_mul_partialDeriv
    hf.integrable_mul
  have h1 := hf.integrable_divergence_mul
  have h2 := hf.integrable_dotProduct_score_mul hpos hp
  have h3 := hf.integrable_dotProduct
  calc ∫ x, (divergence f x + f x ⬝ᵥ sStar x) * p x
      = (∫ x, divergence f x * p x) + ∫ x, (f x ⬝ᵥ sStar x) * p x := by
        simp_rw [add_mul]
        exact integral_add h1 h3
    _ = ∫ x, ((f x ⬝ᵥ sStar x) * p x - (f x ⬝ᵥ score p x) * p x) := by
        rw [integral_sub h3 h2, hstein]
        ring
    _ = ∫ x, (f x ⬝ᵥ (sStar x - score p x)) * p x := by
        congr 1
        funext x
        rw [dotProduct_sub, sub_mul]

/-- For an admissible field `f`, a positive differentiable `p` and finite relative Fisher
information `∫ ‖v⋆‖²_H p < ∞`, the projection integrand `‖f - v⋆‖²_H p` is Lebesgue integrable
(so `projectionObjective` is a genuine, finite integral). -/
theorem Admissible.integrable_sqNormH_sub {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hf : Admissible H p sStar f)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    Integrable (fun x => sqNormH H (f x - idealVelocity H (score p) sStar x) * p x) := by
  simp_rw [sqNormH_sub_idealVelocity_mul hH p sStar f]
  exact (((hf.integrable_dotProduct_sub_score hpos hp).const_mul (-2)).add
    hf.integrable_sqNormH).add hv

/-- For positive-definite `H`, `‖v⋆‖²_H p` is integrable iff the weighted relative Fisher
integrand `‖∇log p - sStar‖²_{H⁻¹} p` is (they agree pointwise). -/
theorem integrable_sqNormH_idealVelocity_iff {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (p : (Fin d → ℝ) → ℝ) (sStar : (Fin d → ℝ) → Fin d → ℝ) :
    Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x) ↔
      Integrable (fun x => sqNormH H⁻¹ (score p x - sStar x) * p x) := by
  simp only [sqNormH_idealVelocity hH]

/-! ### SE-1: Proposition 1 as a value identity -/

/-- **SE-1 (PFG Proposition 1, value identity; App. A.3, Eqs. (15)-(18)), general version.**
Let `H` be positive definite, `p` strictly positive and differentiable, `f` an admissible
velocity field (`Admissible`: differentiable coordinates and the integrability hypotheses of
the Stein identity, of `(f ⬝ᵥ sStar) p` and of `‖f‖²_H p`), and assume finite relative Fisher
information `∫ ‖v⋆‖²_H p < ∞` (`hv`; equivalently `∫ ‖∇log p - sStar‖²_{H⁻¹} p < ∞`, see
`integrable_sqNormH_idealVelocity_iff`), where `v⋆ = H⁻¹ (sStar - ∇log p)`. Then
`-∫ (div f + f ⬝ᵥ sStar) p + ½ ∫ ‖f‖²_H p = ½ ∫ ‖f - v⋆‖²_H p - ½ ∫ ‖v⋆‖²_H p`. -/
theorem steinObjective_eq {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hf : Admissible H p sStar f)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    steinObjective H p sStar f =
      (1 / 2) * (∫ x, sqNormH H (f x - idealVelocity H (score p) sStar x) * p x) -
        (1 / 2) * ∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x := by
  have hfa := hf.integrable_dotProduct_sub_score hpos hp
  have h1 : Integrable (fun x => -2 * ((f x ⬝ᵥ (sStar x - score p x)) * p x) +
      sqNormH H (f x) * p x) := (hfa.const_mul (-2)).add hf.integrable_sqNormH
  simp_rw [sqNormH_sub_idealVelocity_mul hH p sStar f]
  rw [integral_add h1 hv, integral_add (hfa.const_mul (-2)) hf.integrable_sqNormH,
    integral_const_mul, steinObjective, hf.integral_stein hpos hp]
  ring

/-- **SE-1 restated with the Eq. (7) objective.** Under the hypotheses of `steinObjective_eq`,
`steinObjective H p sStar f = projectionObjective H p sStar f - ½ ∫ ‖v⋆‖²_H p`. -/
theorem steinObjective_eq_projectionObjective_sub {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hf : Admissible H p sStar f)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    steinObjective H p sStar f = projectionObjective H p sStar f -
      (1 / 2) * ∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x :=
  steinObjective_eq hH hpos hp hf hv

/-- **The zero field is admissible.** For every `H`, `q` and `sStar`, the zero velocity field
satisfies `SteinObjective.Admissible H q sStar 0` (all its integrands vanish). -/
theorem admissible_zero (H : Matrix (Fin d) (Fin d) ℝ) (q : (Fin d → ℝ) → ℝ)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) : Admissible H q sStar 0 := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact differentiable_const 0
  · simp [partialDeriv]
  · simp
  · simp
  · simp
  · simp [sqNormH]

/-- **Admissibility of compactly supported fields.** If `p` is `C¹`, `sStar` is continuous and
every coordinate `fᵢ` of `f` is `C¹` with compact support, then `f` is admissible for every
matrix `H`: all integrands in `Admissible` are continuous with compact support. (Positivity of
`p` is not needed for this step.) -/
theorem admissible_of_hasCompactSupport (H : Matrix (Fin d) (Fin d) ℝ)
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hp : ContDiff ℝ 1 p) (hsStar : Continuous sStar)
    (hf : ∀ i, ContDiff ℝ 1 (fun y => f y i)) (hfc : ∀ i, HasCompactSupport (fun y => f y i)) :
    Admissible H p sStar f := by
  have hfcont : ∀ i, Continuous (fun y => f y i) := fun i => (hf i).continuous
  refine ⟨fun i => (hf i).differentiable one_ne_zero, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact ((continuous_partialDeriv (hf i) i).mul hp.continuous)
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_partialDeriv (hfc i) i).mul_right
  · exact ((hfcont i).mul (continuous_partialDeriv hp i))
      |>.integrable_of_hasCompactSupport (hfc i).mul_right
  · exact ((hfcont i).mul hp.continuous).integrable_of_hasCompactSupport (hfc i).mul_right
  · have hterm : ∀ i, Integrable (fun x => f x i * (sStar x i * p x)) := fun i =>
      ((hfcont i).mul (((continuous_apply i).comp hsStar).mul hp.continuous))
        |>.integrable_of_hasCompactSupport (hfc i).mul_right
    refine (integrable_finsetSum Finset.univ fun i _ => hterm i).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · have hterm : ∀ i j, Integrable (fun x => f x i * (H i j * f x j * p x)) := fun i j =>
      ((hfcont i).mul ((continuous_const.mul (hfcont j)).mul hp.continuous))
        |>.integrable_of_hasCompactSupport (hfc i).mul_right
    refine (integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hterm i j).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [sqNormH, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **SE-1 (PFG Proposition 1, value identity), discharged for compactly supported fields.**
Let `H` be positive definite, `p` strictly positive and `C¹`, `sStar` continuous, and let every
coordinate of `f` be `C¹` with compact support. The only remaining hypothesis is finite
relative Fisher information `∫ ‖∇log p - sStar‖²_{H⁻¹} p < ∞` (`hfisher`; its integrand is
continuous here, so this is exactly finiteness of the integral). Then
`steinObjective H p sStar f = ½ ∫ ‖f - v⋆‖²_H p - ½ ∫ ‖v⋆‖²_H p` with
`v⋆ = H⁻¹ (sStar - ∇log p)`. -/
theorem steinObjective_eq_of_hasCompactSupport {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : ContDiff ℝ 1 p) (hsStar : Continuous sStar)
    (hf : ∀ i, ContDiff ℝ 1 (fun y => f y i)) (hfc : ∀ i, HasCompactSupport (fun y => f y i))
    (hfisher : Integrable (fun x => sqNormH H⁻¹ (score p x - sStar x) * p x)) :
    steinObjective H p sStar f =
      (1 / 2) * (∫ x, sqNormH H (f x - idealVelocity H (score p) sStar x) * p x) -
        (1 / 2) * ∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x :=
  steinObjective_eq hH hpos (hp.differentiable one_ne_zero)
    (admissible_of_hasCompactSupport H hp hsStar hf hfc)
    ((integrable_sqNormH_idealVelocity_iff hH p sStar).2 hfisher)

/-- **Nonvacuity of SE-1: the equilibrium case `sStar = ∇log p`.** For positive-definite `H`,
strictly positive `C¹` `p` (not necessarily integrable) and `f` with `C¹` compactly supported
coordinates, all hypotheses of `steinObjective_eq_of_hasCompactSupport` hold with
`sStar = score p` (then `v⋆ = 0` and the Fisher integrand vanishes), and the identity reads
`steinObjective H p (∇log p) f = ½ ∫ ‖f‖²_H p ≥ 0`: at equilibrium the best velocity is `0`. -/
theorem steinObjective_score_eq_of_hasCompactSupport {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {p : (Fin d → ℝ) → ℝ} {f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : ContDiff ℝ 1 p)
    (hf : ∀ i, ContDiff ℝ 1 (fun y => f y i)) (hfc : ∀ i, HasCompactSupport (fun y => f y i)) :
    steinObjective H p (score p) f = (1 / 2) * ∫ x, sqNormH H (f x) * p x := by
  have hzero : ∀ x, idealVelocity H (score p) (score p) x = 0 := fun x => by
    simp [idealVelocity]
  have h := steinObjective_eq_of_hasCompactSupport hH hpos hp (continuous_score hp hpos) hf hfc
    (by simp only [sub_self]; simp [sqNormH])
  simp only [hzero, sub_zero] at h
  rw [h]
  simp [sqNormH]

/-! ### SE-1: lower bound and almost-everywhere uniqueness -/

/-- **SE-1, lower bound.** Under the hypotheses of `steinObjective_eq` (positive-definite `H`,
positive differentiable `p`, admissible `f`, finite relative Fisher information), the PFG
objective is bounded below by the value attained by the ideal direction:
`-½ ∫ ‖v⋆‖²_H p ≤ steinObjective H p sStar f`. -/
theorem neg_half_le_steinObjective {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hf : Admissible H p sStar f)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    -(1 / 2) * (∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x) ≤
      steinObjective H p sStar f := by
  rw [steinObjective_eq hH hpos hp hf hv]
  have : 0 ≤ ∫ x, sqNormH H (f x - idealVelocity H (score p) sStar x) * p x :=
    integral_nonneg fun x => mul_nonneg (sqNormH_nonneg hH _) (hpos x).le
  linarith

/-- **SE-1, equality case (a.e. uniqueness).** Under the hypotheses of `steinObjective_eq`,
`steinObjective H p sStar f = -½ ∫ ‖v⋆‖²_H p` if and only if `f = v⋆` Lebesgue-almost
everywhere (equivalently `p dx`-a.e., `ae_densityMeasure_iff`, because `p > 0`). -/
theorem steinObjective_eq_neg_half_iff {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hf : Admissible H p sStar f)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    steinObjective H p sStar f =
        -(1 / 2) * (∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x) ↔
      f =ᵐ[volume] idealVelocity H (score p) sStar := by
  rw [steinObjective_eq hH hpos hp hf hv]
  have hint := hf.integrable_sqNormH_sub hH hpos hp hv
  have hnn : 0 ≤ fun x => sqNormH H (f x - idealVelocity H (score p) sStar x) * p x :=
    fun x => mul_nonneg (sqNormH_nonneg hH _) (hpos x).le
  constructor
  · intro h
    have h0 : ∫ x, sqNormH H (f x - idealVelocity H (score p) sStar x) * p x = 0 := by
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 h0
    filter_upwards [hae] with x hx
    have hx' : sqNormH H (f x - idealVelocity H (score p) sStar x) * p x = 0 := hx
    rcases mul_eq_zero.1 hx' with h1 | h1
    · exact sub_eq_zero.1 ((sqNormH_eq_zero_iff hH _).1 h1)
    · exact absurd h1 (hpos x).ne'
  · intro h
    have hae : (fun x => sqNormH H (f x - idealVelocity H (score p) sStar x) * p x) =ᵐ[volume]
        0 := by
      filter_upwards [h] with x hx
      simp [hx, sqNormH]
    rw [(integral_eq_zero_iff_of_nonneg hnn hint).2 hae]
    ring

/-- **`p dx`-a.e. equals Lebesgue-a.e. for an everywhere positive density.** If `p` is
a.e.-measurable and `p x > 0` for every `x`, then a property holds `densityMeasure p`-a.e. iff
it holds Lebesgue-a.e. (the two measures are mutually absolutely continuous). -/
theorem ae_densityMeasure_iff {p : (Fin d → ℝ) → ℝ} (hp : AEMeasurable p)
    (hpos : ∀ x, 0 < p x) {P : (Fin d → ℝ) → Prop} :
    (∀ᵐ x ∂densityMeasure p, P x) ↔ ∀ᵐ x, P x := by
  constructor
  · intro h
    have hac : (volume : Measure (Fin d → ℝ)) ≪ densityMeasure p :=
      withDensity_absolutelyContinuous' hp.ennreal_ofReal
        (Filter.Eventually.of_forall fun x => by simp [hpos x])
    exact hac.ae_le h
  · intro h
    exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- **SE-1, equality case, `p dx`-a.e. form.** Under the hypotheses of `steinObjective_eq`,
`steinObjective H p sStar f = -½ ∫ ‖v⋆‖²_H p` iff `f = v⋆` almost everywhere with respect to the
law `p dx` (`densityMeasure p`). -/
theorem steinObjective_eq_neg_half_iff_ae_densityMeasure {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {p : (Fin d → ℝ) → ℝ} {sStar f : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p) (hf : Admissible H p sStar f)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    steinObjective H p sStar f =
        -(1 / 2) * (∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x) ↔
      f =ᵐ[densityMeasure p] idealVelocity H (score p) sStar := by
  rw [steinObjective_eq_neg_half_iff hH hpos hp hf hv, Filter.EventuallyEq,
    Filter.EventuallyEq, ae_densityMeasure_iff hp.continuous.aemeasurable hpos]

/-- **Integrals against `p dx`.** If `p` is a.e.-measurable and nonnegative, then for every
real function `g`, `∫ g d(densityMeasure p) = ∫ g(x) p(x) dx` (no integrability needed: both
sides are `0` together when the integrand is not integrable). -/
theorem integral_densityMeasure {p : (Fin d → ℝ) → ℝ} (hp : AEMeasurable p)
    (hp0 : ∀ x, 0 ≤ p x) (g : (Fin d → ℝ) → ℝ) :
    ∫ x, g x ∂densityMeasure p = ∫ x, g x * p x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀ hp.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul, mul_comm]

/-- **Integrability against `p dx`.** If `p` is a.e.-measurable and nonnegative, then `g` is
`densityMeasure p`-integrable iff `g p` is Lebesgue integrable. -/
theorem integrable_densityMeasure_iff {p : (Fin d → ℝ) → ℝ} (hp : AEMeasurable p)
    (hp0 : ∀ x, 0 ≤ p x) {g : (Fin d → ℝ) → ℝ} :
    Integrable g (densityMeasure p) ↔ Integrable (fun x => g x * p x) := by
  rw [densityMeasure, integrable_withDensity_iff_integrable_smul₀' hp.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul, mul_comm]

/-! ### PFG Proposition 1: argmin equivalence over an arbitrary class -/

/-- **The two objectives differ by a constant (Proposition 1, core).** Under the hypotheses of
`steinObjective_eq` for two admissible fields `f, g`,
`steinObjective f - steinObjective g = projectionObjective f - projectionObjective g`: the
optimisation gap of Eq. (4) equals that of Eq. (7). -/
theorem steinObjective_sub_steinObjective {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar f g : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (hf : Admissible H p sStar f) (hg : Admissible H p sStar g)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    steinObjective H p sStar f - steinObjective H p sStar g =
      projectionObjective H p sStar f - projectionObjective H p sStar g := by
  rw [steinObjective_eq hH hpos hp hf hv, steinObjective_eq hH hpos hp hg hv, projectionObjective,
    projectionObjective]
  ring

/-- **PFG Proposition 1 (as stated in the paper).** Let `H` be positive definite, `p` strictly
positive and differentiable with finite relative Fisher information `∫ ‖v⋆‖²_H p < ∞`, and let
`F` be **any** set of admissible velocity fields and `g ∈ F`. Then `g` minimises the PFG
objective (Eq. (4) with Eq. (6)) over `F` iff `g` minimises the weighted projection objective
`½ ∫ ‖f - H⁻¹ ∇ln(p⋆/p)‖²_H p` (Eq. (7)) over `F`. Existence of a minimiser is not claimed. -/
theorem isMinOn_steinObjective_iff {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x))
    {F : Set ((Fin d → ℝ) → Fin d → ℝ)} (hF : ∀ f ∈ F, Admissible H p sStar f)
    {g : (Fin d → ℝ) → Fin d → ℝ} (hg : g ∈ F) :
    IsMinOn (steinObjective H p sStar) F g ↔ IsMinOn (projectionObjective H p sStar) F g := by
  simp only [isMinOn_iff]
  refine forall₂_congr fun f hf => ?_
  have h := steinObjective_sub_steinObjective hH hpos hp (hF f hf) (hF g hg) hv
  constructor <;> intro h' <;> linarith

/-- **SE-1, value at the ideal direction.** If, in addition to positive-definite `H`, positive
differentiable `p` and finite relative Fisher information, the ideal direction
`v⋆ = H⁻¹ (sStar - ∇log p)` is itself admissible, then
`steinObjective H p sStar v⋆ = -½ ∫ ‖v⋆‖²_H p`, the lower bound of `neg_half_le_steinObjective`. -/
theorem steinObjective_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (hvA : Admissible H p sStar (idealVelocity H (score p) sStar))
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x)) :
    steinObjective H p sStar (idealVelocity H (score p) sStar) =
      -(1 / 2) * (∫ x, sqNormH H (idealVelocity H (score p) sStar x) * p x) :=
  (steinObjective_eq_neg_half_iff hH hpos hp hvA hv).2 (Filter.EventuallyEq.refl _ _)

/-- **SE-1, well-specified class.** Let `H` be positive definite, `p` strictly positive and
differentiable with finite relative Fisher information, `F` a set of admissible fields that
contains the ideal direction `v⋆ = H⁻¹ (sStar - ∇log p)`, and `g ∈ F`. Then `g` minimises the
PFG objective over `F` iff `g = v⋆` Lebesgue-a.e. (the paper's remark after Eq. (5), for any
SPD `H`). -/
theorem isMinOn_iff_ae_eq_idealVelocity {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {p : (Fin d → ℝ) → ℝ} {sStar : (Fin d → ℝ) → Fin d → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (hv : Integrable (fun x => sqNormH H (idealVelocity H (score p) sStar x) * p x))
    {F : Set ((Fin d → ℝ) → Fin d → ℝ)} (hF : ∀ f ∈ F, Admissible H p sStar f)
    (hvF : idealVelocity H (score p) sStar ∈ F) {g : (Fin d → ℝ) → Fin d → ℝ} (hg : g ∈ F) :
    IsMinOn (steinObjective H p sStar) F g ↔ g =ᵐ[volume] idealVelocity H (score p) sStar := by
  rw [← steinObjective_eq_neg_half_iff hH hpos hp (hF g hg) hv]
  have hmin := steinObjective_idealVelocity hH hpos hp (hF _ hvF) hv
  constructor
  · intro h
    exact le_antisymm (hmin ▸ isMinOn_iff.1 h _ hvF)
      (neg_half_le_steinObjective hH hpos hp (hF g hg) hv)
  · intro h
    rw [isMinOn_iff]
    intro f hf
    rw [h]
    exact neg_half_le_steinObjective hH hpos hp (hF f hf) hv

/-! ### Finite-dimensional linear class `F = {x ↦ W ψ(x)}` -/

/-- **The PFG objective on a linear feature class is `FeatureClass.popSteinObjective`.** For a
nonnegative
a.e.-measurable `p`, a feature map `ψ : (Fin d → ℝ) → Fin m → ℝ` and a matrix `W`,
`steinObjective H p sStar (x ↦ W ψ(x)) = FeatureClass.popSteinObjective H (densityMeasure p) sStar ψ
W`.
The two definitions agree exactly once the measure of `SVGDSpecialCase` is `μ = p dx`, because
`∫ g d(p dx) = ∫ g p dx` (`integral_densityMeasure`); no integrability is needed. -/
theorem steinObjective_featureField {m : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    {p : (Fin d → ℝ) → ℝ} (hp : AEMeasurable p) (hp0 : ∀ x, 0 ≤ p x)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (W : Matrix (Fin d) (Fin m) ℝ) :
    steinObjective H p sStar (fun x => W *ᵥ ψ x) =
      FeatureClass.popSteinObjective H (densityMeasure p) sStar ψ W := by
  rw [steinObjective, FeatureClass.popSteinObjective, FeatureClass.popSteinTerm,
      integral_densityMeasure hp hp0,
    integral_densityMeasure hp hp0]

/-- **Linear class: minimisers ⇔ normal equations** (corollary of
`FeatureClass.popStein_isMinimiser_iff_normalEq` with `μ = p dx`). Let `H` be positive semidefinite,
`p`
nonnegative and a.e.-measurable, the features `ψₖ` differentiable, and the functions
`(sStarᵢ ψₖ + ∂ᵢ ψₖ) p` and `ψₖ ψₗ p` Lebesgue integrable. Then `W` minimises
`V ↦ steinObjective H p sStar (V ψ)` over all matrices iff `H W Σ = G`, where
`Σ = ∫ ψ ψᵀ p` (`FeatureClass.popFeatureCov`) and `G = ∫ (sStar ψᵀ + (∇ψ)ᵀ) p`
(`FeatureClass.popSteinMatrix`),
both taken against `densityMeasure p`. -/
theorem featureField_isMinimiser_iff_normalEq {m : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef) {p : (Fin d → ℝ) → ℝ} (hp : AEMeasurable p) (hp0 : ∀ x, 0 ≤ p x)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ k, Differentiable ℝ (fun z => ψ z k))
    (hG : ∀ i k, Integrable
      (fun x => (sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) * p x))
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l * p x))
    (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V : Matrix (Fin d) (Fin m) ℝ, steinObjective H p sStar (fun x => W *ᵥ ψ x) ≤
        steinObjective H p sStar (fun x => V *ᵥ ψ x)) ↔
      H * W * FeatureClass.popFeatureCov (densityMeasure p) ψ =
        FeatureClass.popSteinMatrix (densityMeasure p) sStar ψ := by
  simp only [steinObjective_featureField H hp hp0]
  exact FeatureClass.popStein_isMinimiser_iff_normalEq hH sStar ψ
    (Filter.Eventually.of_forall fun x k => (hψ k) x)
    (fun i k => (integrable_densityMeasure_iff hp hp0).2 (hG i k))
    (fun k l => (integrable_densityMeasure_iff hp hp0).2 (hCov k l)) W

/-- **Linear class: the minimising field is unique a.e.** (corollary of
`FeatureClass.popSteinObjective_eq_iff_of_normalEq`). Let `H` be positive definite, `p`
a.e.-measurable
and strictly positive, and assume the hypotheses of `featureField_isMinimiser_iff_normalEq`.
If `W` solves the normal equations `H W Σ = G`, then for every `V` the objective values of
`V ψ` and `W ψ` coincide iff `V ψ(x) = W ψ(x)` for Lebesgue-a.e. `x`. -/
theorem featureField_eq_iff_of_normalEq {m : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {p : (Fin d → ℝ) → ℝ} (hp : AEMeasurable p) (hpos : ∀ x, 0 < p x)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ k, Differentiable ℝ (fun z => ψ z k))
    (hG : ∀ i k, Integrable
      (fun x => (sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) * p x))
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l * p x))
    {W : Matrix (Fin d) (Fin m) ℝ}
    (hW : H * W * FeatureClass.popFeatureCov (densityMeasure p) ψ =
      FeatureClass.popSteinMatrix (densityMeasure p) sStar ψ)
    (V : Matrix (Fin d) (Fin m) ℝ) :
    steinObjective H p sStar (fun x => V *ᵥ ψ x) = steinObjective H p sStar (fun x => W *ᵥ ψ x) ↔
      ∀ᵐ x, V *ᵥ ψ x = W *ᵥ ψ x := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hpos x).le
  simp only [steinObjective_featureField H hp hp0]
  rw [FeatureClass.popSteinObjective_eq_iff_of_normalEq hH sStar ψ
    (Filter.Eventually.of_forall fun x k => (hψ k) x)
    (fun i k => (integrable_densityMeasure_iff hp hp0).2 (hG i k))
    (fun k l => (integrable_densityMeasure_iff hp hp0).2 (hCov k l)) hW V,
    ae_densityMeasure_iff hp hpos]

/-- **Stein form of the population Stein matrix.** Let `p` be strictly positive and
differentiable, the features `ψₖ` differentiable, and the functions `(∂ᵢ ψₖ) p`, `ψₖ (∂ᵢ p)`,
`ψₖ p` and `sStarᵢ ψₖ p` Lebesgue integrable. Then the population Stein matrix of
`SVGDSpecialCase` under `p dx` is
`G_{ik} = ∫ (sStarᵢ - (∇log p)ᵢ) ψₖ p`, i.e. `G = ∫ (H v⋆) ψᵀ p` (density Stein identity
ID-2 applied to each `ψₖ`). -/
theorem popSteinMatrix_eq_integral_score_sub {m : ℕ} {p : (Fin d → ℝ) → ℝ}
    (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ k, Differentiable ℝ (fun z => ψ z k))
    (hdψ : ∀ i k, Integrable (fun x => partialDeriv i (fun z => ψ z k) x * p x))
    (hψdp : ∀ i k, Integrable (fun x => ψ x k * partialDeriv i p x))
    (hψp : ∀ k, Integrable (fun x => ψ x k * p x))
    (hsψ : ∀ i k, Integrable (fun x => sStar x i * ψ x k * p x)) (i : Fin d) (k : Fin m) :
    FeatureClass.popSteinMatrix (densityMeasure p) sStar ψ i k =
      ∫ x, (sStar x i - score p x i) * ψ x k * p x := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hpos x).le
  have hstein := DensityStein.integral_partialDeriv_mul_eq_neg_integral_mul_score hpos hp
    (hψ k) i (hdψ i k) (hψdp i k) (hψp k)
  have hsc : Integrable (fun x => ψ x k * score p x i * p x) := by
    refine (hψdp i k).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_assoc, score_mul_self_of_pos (hp x) (hpos x)]
  rw [FeatureClass.popSteinMatrix, integral_densityMeasure hp.continuous.aemeasurable hp0]
  calc ∫ x, (sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) * p x
      = (∫ x, sStar x i * ψ x k * p x) + ∫ x, partialDeriv i (fun z => ψ z k) x * p x := by
        simp_rw [add_mul]
        exact integral_add (hsψ i k) (hdψ i k)
    _ = (∫ x, sStar x i * ψ x k * p x) - ∫ x, ψ x k * score p x i * p x := by
        rw [hstein]
        ring
    _ = ∫ x, (sStar x i - score p x i) * ψ x k * p x := by
        rw [← integral_sub (hsψ i k) hsc]
        congr 1
        funext x
        ring

/-- **Linear class and Proposition 1: the PFG minimiser is the weighted least-squares fit of
`v⋆`.** Let `H` be positive definite, `p` strictly positive and differentiable, the features
`ψₖ` differentiable, and the functions `(∂ᵢ ψₖ) p`, `ψₖ (∂ᵢ p)`, `ψₖ p`, `sStarᵢ ψₖ p` and
`ψₖ ψₗ p` Lebesgue integrable. Then `W` minimises `V ↦ steinObjective H p sStar (V ψ)` iff
`W Σ = ∫ v⋆ ψᵀ p`, with `Σ = ∫ ψ ψᵀ p` and `v⋆ = H⁻¹ (sStar - ∇log p)`: these are the normal
equations of the `H`-weighted `L²(p)` projection of `v⋆` onto `{V ψ}`, as Proposition 1
predicts. (Because the class is closed under `V ↦ A V`, the weight `H` drops out of the
normal equations; `H` still enters through `v⋆`.) -/
theorem featureField_isMinimiser_iff_projection {m : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {p : (Fin d → ℝ) → ℝ} (hpos : ∀ x, 0 < p x) (hp : Differentiable ℝ p)
    (sStar : (Fin d → ℝ) → Fin d → ℝ) (ψ : (Fin d → ℝ) → Fin m → ℝ)
    (hψ : ∀ k, Differentiable ℝ (fun z => ψ z k))
    (hdψ : ∀ i k, Integrable (fun x => partialDeriv i (fun z => ψ z k) x * p x))
    (hψdp : ∀ i k, Integrable (fun x => ψ x k * partialDeriv i p x))
    (hψp : ∀ k, Integrable (fun x => ψ x k * p x))
    (hsψ : ∀ i k, Integrable (fun x => sStar x i * ψ x k * p x))
    (hCov : ∀ k l, Integrable (fun x => ψ x k * ψ x l * p x))
    (W : Matrix (Fin d) (Fin m) ℝ) :
    (∀ V : Matrix (Fin d) (Fin m) ℝ, steinObjective H p sStar (fun x => W *ᵥ ψ x) ≤
        steinObjective H p sStar (fun x => V *ᵥ ψ x)) ↔
      W * FeatureClass.popFeatureCov (densityMeasure p) ψ =
        Matrix.of fun i k => ∫ x, idealVelocity H (score p) sStar x i * ψ x k * p x := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hpos x).le
  have hpm : AEMeasurable p := hp.continuous.aemeasurable
  have hG : ∀ i k, Integrable
      (fun x => (sStar x i * ψ x k + partialDeriv i (fun z => ψ z k) x) * p x) := fun i k =>
    ((hsψ i k).add (hdψ i k)).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply]
      ring)
  have hsc : ∀ j k, Integrable (fun x => (sStar x j - score p x j) * ψ x k * p x) := by
    intro j k
    refine ((hsψ j k).sub (hψdp j k)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [← score_mul_self_of_pos (hp x) (hpos x)]
    ring
  rw [featureField_isMinimiser_iff_normalEq hH.posSemidef hpm hp0 sStar ψ hψ hG hCov W]
  have hGeq : FeatureClass.popSteinMatrix (densityMeasure p) sStar ψ =
      Matrix.of fun i k => ∫ x, (sStar x i - score p x i) * ψ x k * p x := by
    ext i k
    exact popSteinMatrix_eq_integral_score_sub hpos hp sStar ψ hψ hdψ hψdp hψp hsψ i k
  have hHinv : H⁻¹ * FeatureClass.popSteinMatrix (densityMeasure p) sStar ψ =
      Matrix.of fun i k => ∫ x, idealVelocity H (score p) sStar x i * ψ x k * p x := by
    rw [hGeq]
    ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply, idealVelocity, mulVec, dotProduct,
      Pi.sub_apply]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun j _ => (hsc j k).const_mul (H⁻¹ i j)]
    congr 1
    funext x
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [← hHinv]
  constructor
  · intro h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_of_posDef hH, Matrix.one_mul]
  · intro h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, mul_inv_of_posDef hH, Matrix.one_mul]

end SteinObjective
end FormalizeSampling
