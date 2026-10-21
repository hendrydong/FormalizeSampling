module

public import FormalizeSampling.Foundations.LogSobolevPi
public import FormalizeSampling.Foundations.HeatKernelPi
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Functional log-Sobolev inequalities on `Fin d → ℝ`: tensorization and convolution

Status: **Verified** (no named hypothesis beyond the log-Sobolev inequalities that are the
inputs of each statement; the heat-flow corollary takes the Gaussian LSI
`FunctionalLSIPi (N(0, t I)) t` as a hypothesis).

This is the `d`-dimensional counterpart of `Foundations/LogSobolev.lean`, for the definitions
`LogSobolevPi.gradSq`, `LSIClassPi`, `FunctionalLSIPi`. For `G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ`,
`gradSqFst G (x, y) = ∑ᵢ (∂_{xᵢ} G(x, y))²` and `gradSqSnd G (x, y) = ∑ᵢ (∂_{yᵢ} G(x, y))²` are
the squared norms of the two partial gradients.

## Main results

* `ent_prod_le_of_functionalLSIPi` (**tensorization**): for probability measures `μ, ν` on
  `Fin d → ℝ` with `FunctionalLSIPi μ C₁`, `FunctionalLSIPi ν C₂` (`C₂ ≥ 0`), and `G` measurable,
  differentiable in each variable, with measurable partial derivatives bounded by `M` and
  `c ≤ G ≤ M` (`c > 0`):
  `Ent_{μ⊗ν}(G²) ≤ 2 ∫ (C₁ ‖∇ₓG‖² + C₂ ‖∇_yG‖²) d(μ⊗ν)`. The `ν`-term applies the LSI of `ν` to
  `y ↦ √(∫ G(x, y)² dμ(x))`, differentiating under the integral (Fréchet derivative) and using
  Cauchy–Schwarz coordinatewise.
* `functionalLSIPi_map_add` (**convolution**): `FunctionalLSIPi μ C₁`, `FunctionalLSIPi ν C₂`,
  `C₂ ≥ 0` imply `FunctionalLSIPi ((μ ⊗ ν).map (+)) (C₁ + C₂)`.
* `heatKernelPi_comp_eq_map_add`: `heatKernelPi t ∘ₘ π = (π ⊗ N(0, t I)).map (+)`.
* `functionalLSIPi_heatKernelPi_comp`: `FunctionalLSIPi π C` and the Gaussian LSI
  `FunctionalLSIPi (N(0, t I)) t` imply `FunctionalLSIPi (heatKernelPi t ∘ₘ π) (C + t)`.

## Not proved here

* The Gaussian functional LSI `FunctionalLSIPi (N(0, t I)) t` is a hypothesis of
  `functionalLSIPi_heatKernelPi_comp`; it is proved in `GaussianFunctionalLSIPi`.
* Measurability of the partial derivatives of `G` is assumed in the tensorization theorem, not
  derived from the measurability of `G`.
* General Lipschitz push-forwards and wider test-function classes (as in the 1D file).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace FormalizeSampling.LogSobolevTensorPi

open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevPi FormalizeSampling.HeatKernelPi

variable {d : ℕ}

/-- Squared norm of the gradient of `G` in its first argument:
`gradSqFst G (x, y) = ∑ᵢ (∂_{xᵢ} G(x, y))²`. -/
noncomputable def gradSqFst (G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ :=
  gradSq (fun x => G (x, p.2)) p.1

/-- Squared norm of the gradient of `G` in its second argument:
`gradSqSnd G (x, y) = ∑ᵢ (∂_{yᵢ} G(x, y))²`. -/
noncomputable def gradSqSnd (G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ :=
  gradSq (fun y => G (p.1, y)) p.2

/-- `gradSqFst` is nonnegative. -/
theorem gradSqFst_nonneg (G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    0 ≤ gradSqFst G p :=
  gradSq_nonneg _ _

/-- `gradSqSnd` is nonnegative. -/
theorem gradSqSnd_nonneg (G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    0 ≤ gradSqSnd G p :=
  gradSq_nonneg _ _

/-- A continuous linear functional on `Fin d → ℝ` is determined by its values on the standard
basis: `L = ∑ᵢ L(eᵢ) • projᵢ`. -/
theorem clm_eq_sum_single (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    L = ∑ i, L (Pi.single i 1) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
  refine ContinuousLinearMap.ext fun v => ?_
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (v i) : Fin d → ℝ) = v i • Pi.single i 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
  rfl

/-- If every coordinate satisfies `|aᵢ| ≤ M`, then `∑ᵢ aᵢ² ≤ d M²`. -/
theorem sum_sq_le_of_abs_le {a : Fin d → ℝ} {M : ℝ} (h : ∀ i, |a i| ≤ M) :
    ∑ i, a i ^ 2 ≤ d * M ^ 2 := by
  calc ∑ i, a i ^ 2 ≤ ∑ _i : Fin d, M ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_le_sq' (abs_le.1 (h i)).1 (abs_le.1 (h i)).2
    _ = d * M ^ 2 := by simp

/-- `gradSq` of a function whose basis directional derivatives are bounded by `M` is at most
`d M²`. -/
theorem gradSq_le_of_abs_le {g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} {M : ℝ}
    (h : ∀ i, |fderiv ℝ g x (Pi.single i 1)| ≤ M) : gradSq g x ≤ d * M ^ 2 :=
  sum_sq_le_of_abs_le h

/-- **Tensorization of the functional LSI on `Fin d → ℝ`.** Let `μ, ν` be probability measures on
`Fin d → ℝ` with `FunctionalLSIPi μ C₁`, `FunctionalLSIPi ν C₂` and `C₂ ≥ 0`. Let
`G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ` be measurable, differentiable in each variable separately,
with measurable partial derivatives `∂_{xᵢ} G`, `∂_{yᵢ} G` bounded by `M` in absolute value, and
`c ≤ G ≤ M` for some `c > 0`. Then
`Ent_{μ⊗ν}(G²) ≤ 2 ∫ (C₁ ‖∇ₓG‖² + C₂ ‖∇_yG‖²) d(μ ⊗ ν)`. -/
theorem ent_prod_le_of_functionalLSIPi {μ ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C₁ C₂ : ℝ} (hμ : FunctionalLSIPi μ C₁)
    (hν : FunctionalLSIPi ν C₂) (hC₂ : 0 ≤ C₂) {G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ}
    (hGm : Measurable G) (hG₁ : ∀ y, Differentiable ℝ fun x => G (x, y))
    (hG₂ : ∀ x, Differentiable ℝ fun y => G (x, y))
    (hD₁m : ∀ i, Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      fderiv ℝ (fun x => G (x, p.2)) p.1 (Pi.single i 1))
    (hD₂m : ∀ i, Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      fderiv ℝ (fun y => G (p.1, y)) p.2 (Pi.single i 1))
    {M c : ℝ} (hc : 0 < c) (hcG : ∀ p, c ≤ G p) (hGM : ∀ p, G p ≤ M)
    (hD₁M : ∀ (p : (Fin d → ℝ) × (Fin d → ℝ)) i,
      |fderiv ℝ (fun x => G (x, p.2)) p.1 (Pi.single i 1)| ≤ M)
    (hD₂M : ∀ (p : (Fin d → ℝ) × (Fin d → ℝ)) i,
      |fderiv ℝ (fun y => G (p.1, y)) p.2 (Pi.single i 1)| ≤ M) :
    ent (μ.prod ν) (fun p => G p ^ 2) ≤
      2 * ∫ p, (C₁ * gradSqFst G p + C₂ * gradSqSnd G p) ∂(μ.prod ν) := by
  have hM : 0 ≤ M := (hc.le.trans (hcG (0, 0))).trans (hGM (0, 0))
  have hGabs : ∀ p, |G p| ≤ M := fun p => abs_le.2 ⟨by linarith [hcG p, hGM p], hGM p⟩
  set F : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun p => G p ^ 2 with hFdef
  have hFm : Measurable F := hGm.pow_const 2
  have hF0 : ∀ p, 0 ≤ F p := fun p => sq_nonneg _
  have hFM : ∀ p, F p ≤ M ^ 2 := fun p => pow_le_pow_left₀ (hc.le.trans (hcG p)) (hGM p) 2
  have hFb : ∀ p, |F p| ≤ M ^ 2 := fun p => by rw [abs_of_nonneg (hF0 p)]; exact hFM p
  have hFc : ∀ p, c ^ 2 ≤ F p := fun p => pow_le_pow_left₀ hc.le (hcG p) 2
  have hF : Integrable F (μ.prod ν) := integrable_of_abs_le hFm.aestronglyMeasurable _ hFb
  have hFl : Integrable (fun p => F p * Real.log (F p)) (μ.prod ν) :=
    integrable_of_abs_le (hFm.mul hFm.log).aestronglyMeasurable ((M ^ 2) ^ 2 + 1) fun p =>
      (abs_mul_log_le (hF0 p)).trans (by have := hF0 p; have := hFM p; gcongr)
  have hFx : ∀ y, Integrable (fun x => F (x, y)) μ := fun y =>
    integrable_of_abs_le (hFm.comp measurable_prodMk_right).aestronglyMeasurable _
      fun x => hFb (x, y)
  set H : (Fin d → ℝ) → ℝ := fun y => ∫ x, F (x, y) ∂μ with hHdef
  have hHi : Integrable H ν := hF.integral_prod_right
  have hHc : ∀ y, c ^ 2 ≤ H y := fun y => le_integral_of_le_prob (hFx y) fun x => hFc _
  have hHM : ∀ y, H y ≤ M ^ 2 := fun y => integral_le_of_le_prob (hFx y) fun x => hFM _
  have hH0 : ∀ y, 0 ≤ H y := fun y => (sq_nonneg c).trans (hHc y)
  have hHpos : ∀ y, 0 < H y := fun y => lt_of_lt_of_le (pow_pos hc 2) (hHc y)
  have hHl : Integrable (fun y => H y * Real.log (H y)) ν :=
    integrable_of_abs_le (Real.continuous_mul_log.comp_aestronglyMeasurable
      hHi.aestronglyMeasurable) ((M ^ 2) ^ 2 + 1) fun y =>
      (abs_mul_log_le (hH0 y)).trans (by have := hH0 y; have := hHM y; gcongr)
  rw [ent_prod_eq μ ν hF hFl hHl]
  -- integrability of the squared partial gradients
  have hg₁m : Measurable (gradSqFst G) := by
    unfold gradSqFst gradSq
    exact Finset.measurable_sum _ fun i _ => (hD₁m i).pow_const 2
  have hg₂m : Measurable (gradSqSnd G) := by
    unfold gradSqSnd gradSq
    exact Finset.measurable_sum _ fun i _ => (hD₂m i).pow_const 2
  have hg₁b : ∀ p, |gradSqFst G p| ≤ d * M ^ 2 := fun p => by
    rw [abs_of_nonneg (gradSqFst_nonneg G p)]
    exact gradSq_le_of_abs_le (hD₁M p)
  have hg₂b : ∀ p, |gradSqSnd G p| ≤ d * M ^ 2 := fun p => by
    rw [abs_of_nonneg (gradSqSnd_nonneg G p)]
    exact gradSq_le_of_abs_le (hD₂M p)
  have hg₁ : Integrable (gradSqFst G) (μ.prod ν) :=
    integrable_of_abs_le hg₁m.aestronglyMeasurable _ hg₁b
  have hg₂ : Integrable (gradSqSnd G) (μ.prod ν) :=
    integrable_of_abs_le hg₂m.aestronglyMeasurable _ hg₂b
  -- Step 2: the conditional entropies
  have hstep2 : ∫ y, ent μ (fun x => F (x, y)) ∂ν ≤ 2 * C₁ * ∫ p, gradSqFst G p ∂(μ.prod ν) := by
    have hpt : ∀ y, ent μ (fun x => F (x, y)) ≤ 2 * C₁ * ∫ x, gradSqFst G (x, y) ∂μ := by
      intro y
      have hcl : LSIClassPi (fun x => G (x, y)) :=
        ⟨hG₁ y, ⟨M, fun x => hGabs _⟩, ⟨d * M ^ 2, fun x => gradSq_le_of_abs_le (hD₁M (x, y))⟩,
          c, hc, fun x => hcG _⟩
      exact hμ _ hcl
    rw [integral_prod_symm _ hg₁, ← integral_const_mul]
    exact integral_mono (hFl.integral_prod_right.sub hHl)
      (hg₁.integral_prod_right.const_mul _) hpt
  -- Step 3: the entropy of the marginal
  set D : Fin d → (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun i p =>
    fderiv ℝ (fun y => G (p.1, y)) p.2 (Pi.single i 1) with hDdef
  set F' : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ := fun y x =>
    (2 * G (x, y)) • fderiv ℝ (fun y' => G (x, y')) y with hF'def
  have hF'apply : ∀ y x i, F' y x (Pi.single i 1) = 2 * (G (x, y) * D i (x, y)) := by
    intro y x i
    simp only [hF'def, hDdef, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hF'm : ∀ y, AEStronglyMeasurable (F' y) μ := by
    intro y
    have he : F' y = fun x => (2 * G (x, y)) •
        ∑ i, D i (x, y) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
      funext x
      simp only [hF'def, hDdef]
      rw [← clm_eq_sum_single]
    rw [he]
    have hcont : Continuous fun q : ℝ × (Fin d → ℝ) => q.1 •
        ∑ i, q.2 i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
      fun_prop
    have hmeas : Measurable fun x : Fin d → ℝ => (2 * G (x, y), fun i => D i (x, y)) :=
      (measurable_const.mul (hGm.comp measurable_prodMk_right)).prodMk
        (measurable_pi_iff.2 fun i => (hD₂m i).comp measurable_prodMk_right)
    exact hcont.comp_aestronglyMeasurable hmeas.aestronglyMeasurable
  have hF'b : ∀ y x, ‖F' y x‖ ≤ 2 * M * (d * M) := by
    intro y x
    simp only [hF'def]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hGabs _) zero_le_two)
      (norm_le_of_abs_apply_single_le _ hM fun i => hD₂M (x, y) i) (norm_nonneg _)
      (by positivity)
  have hF'i : ∀ y, Integrable (F' y) μ := fun y =>
    Integrable.of_bound (hF'm y) _ (ae_of_all _ (hF'b y))
  have hHd : ∀ y, HasFDerivAt H (∫ x, F' y x ∂μ) y := by
    intro y
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
      (F := fun y x => F (x, y)) (F' := F') (x₀ := y)
      (bound := fun _ => 2 * M * (d * M)) univ_mem
      (Eventually.of_forall fun y' => (hFx y').aestronglyMeasurable) (hFx y) (hF'm y)
      (ae_of_all _ fun x y' _ => hF'b y' x) (integrable_const _) (ae_of_all _ fun x y' _ => ?_)
    have := ((hG₂ x y').hasFDerivAt).pow 2
    convert this using 1
    simp only [hF'def]
    ext v
    simp
  set S : (Fin d → ℝ) → ℝ := fun y => Real.sqrt (H y) with hSdef
  have hSpos : ∀ y, 0 < S y := fun y => Real.sqrt_pos.2 (hHpos y)
  have hSd : ∀ y, HasFDerivAt S ((1 / (2 * S y)) • ∫ x, F' y x ∂μ) y := fun y =>
    (hHd y).sqrt (hHpos y).ne'
  have hDx : ∀ y i, Integrable (fun x => D i (x, y) ^ 2) μ := fun y i =>
    integrable_of_abs_le (((hD₂m i).comp measurable_prodMk_right).pow_const 2).aestronglyMeasurable
      (M ^ 2) fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (abs_le.1 (hD₂M _ i)).1 (abs_le.1 (hD₂M _ i)).2
  have hCS : ∀ y i, (fderiv ℝ S y (Pi.single i 1)) ^ 2 ≤ ∫ x, D i (x, y) ^ 2 ∂μ := by
    intro y i
    rw [(hSd y).fderiv, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.integral_apply (hF'i y)]
    simp only [hF'apply]
    have hGD : Integrable (fun x => G (x, y) * D i (x, y)) μ :=
      integrable_of_abs_le ((hGm.mul (hD₂m i)).comp measurable_prodMk_right).aestronglyMeasurable
        (M * M) fun x => by rw [abs_mul]; gcongr; exacts [hGabs _, hD₂M _ i]
    have hcs := sq_integral_mul_le_of_pos (μ := μ) (a := fun x => G (x, y))
      (b := fun x => D i (x, y)) (hFx y) (hDx y i) hGD (hHpos y)
    rw [integral_const_mul, smul_eq_mul]
    have hS2 : S y ^ 2 = H y := Real.sq_sqrt (hH0 y)
    have hSy := hSpos y
    have : (∫ x, G (x, y) * D i (x, y) ∂μ) ^ 2 ≤ H y * ∫ x, D i (x, y) ^ 2 ∂μ := hcs
    rw [show 1 / (2 * S y) * (2 * ∫ x, G (x, y) * D i (x, y) ∂μ) =
      (∫ x, G (x, y) * D i (x, y) ∂μ) / S y by field_simp, div_pow, hS2,
      div_le_iff₀ (hHpos y)]
    linarith
  have hgS : ∀ y, gradSq S y ≤ ∫ x, gradSqSnd G (x, y) ∂μ := by
    intro y
    have he : ∫ x, gradSqSnd G (x, y) ∂μ = ∑ i, ∫ x, D i (x, y) ^ 2 ∂μ := by
      show ∫ x, ∑ i, D i (x, y) ^ 2 ∂μ = _
      exact integral_finsetSum _ fun i _ => hDx y i
    rw [he]
    exact Finset.sum_le_sum fun i _ => hCS y i
  have hg₂x : ∀ y, Integrable (fun x => gradSqSnd G (x, y)) μ := fun y =>
    integrable_of_abs_le (hg₂m.comp measurable_prodMk_right).aestronglyMeasurable _
      fun x => hg₂b (x, y)
  have hgSM : ∀ y, gradSq S y ≤ d * M ^ 2 := fun y =>
    (hgS y).trans (integral_le_of_le_prob (hg₂x y) fun x => (le_abs_self _).trans (hg₂b _))
  have hSclass : LSIClassPi S :=
    ⟨fun y => (hSd y).differentiableAt,
      ⟨Real.sqrt (M ^ 2), fun y => by
        rw [abs_of_pos (hSpos y)]; exact Real.sqrt_le_sqrt (hHM y)⟩,
      ⟨d * M ^ 2, hgSM⟩, c, hc, fun y => (Real.le_sqrt hc.le (hH0 y)).2 (hHc y)⟩
  have hstep3 := hν S hSclass
  have hSH : (fun y => S y ^ 2) = H := funext fun y => Real.sq_sqrt (hH0 y)
  rw [hSH] at hstep3
  have hgSm : Measurable (gradSq S) := by
    unfold gradSq
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ S _).pow_const 2
  have hstep3' : ∫ y, gradSq S y ∂ν ≤ ∫ p, gradSqSnd G p ∂(μ.prod ν) := by
    rw [integral_prod_symm _ hg₂]
    refine integral_mono (integrable_of_abs_le hgSm.aestronglyMeasurable (d * M ^ 2)
      fun y => ?_) hg₂.integral_prod_right hgS
    rw [abs_of_nonneg (gradSq_nonneg _ _)]; exact hgSM y
  have hsum : ∫ p, (C₁ * gradSqFst G p + C₂ * gradSqSnd G p) ∂(μ.prod ν) =
      C₁ * ∫ p, gradSqFst G p ∂(μ.prod ν) + C₂ * ∫ p, gradSqSnd G p ∂(μ.prod ν) := by
    rw [integral_add (hg₁.const_mul _) (hg₂.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hsum]
  have := mul_le_mul_of_nonneg_left hstep3' (by linarith : (0 : ℝ) ≤ 2 * C₂)
  linarith

/-- **LSI of a convolution on `Fin d → ℝ`.** For probability measures `μ, ν` on `Fin d → ℝ` with
`FunctionalLSIPi μ C₁`, `FunctionalLSIPi ν C₂` and `C₂ ≥ 0`, the convolution `μ ∗ ν`, written
as the push-forward of `μ ⊗ ν` by `(x, z) ↦ x + z`, satisfies `FunctionalLSIPi (μ ∗ ν) (C₁ + C₂)`.
-/
theorem functionalLSIPi_map_add {μ ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C₁ C₂ : ℝ} (hμ : FunctionalLSIPi μ C₁)
    (hν : FunctionalLSIPi ν C₂) (hC₂ : 0 ≤ C₂) :
    FunctionalLSIPi ((μ.prod ν).map (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2))
      (C₁ + C₂) := by
  intro g hg
  obtain ⟨hgd, ⟨M₀, hM₀⟩, ⟨K, hK⟩, c, hc, hcg⟩ := hg
  have hgm : Measurable g := hgd.continuous.measurable
  have hadd : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) := by fun_prop
  set M := max M₀ (Real.sqrt K) with hMdef
  have hDg : ∀ z i, |fderiv ℝ g z (Pi.single i 1)| ≤ M := fun z i =>
    (Real.abs_le_sqrt ((Finset.single_le_sum (f := fun j => fderiv ℝ g z (Pi.single j 1) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans (hK z))).trans (le_max_right _ _)
  have h₁ : ∀ p : (Fin d → ℝ) × (Fin d → ℝ),
      fderiv ℝ (fun x => g (x + p.2)) p.1 = fderiv ℝ g (p.1 + p.2) := fun p =>
    fderiv_comp_add_right _
  have h₂ : ∀ p : (Fin d → ℝ) × (Fin d → ℝ),
      fderiv ℝ (fun y => g (p.1 + y)) p.2 = fderiv ℝ g (p.1 + p.2) := fun p =>
    fderiv_comp_add_left _
  have hDm : ∀ i, Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      fderiv ℝ g (p.1 + p.2) (Pi.single i 1) := fun i =>
    (measurable_fderiv_apply_const ℝ g _).comp hadd
  have h := ent_prod_le_of_functionalLSIPi hμ hν hC₂ (G := fun p => g (p.1 + p.2))
    (hgm.comp hadd) (fun y => hgd.comp (differentiable_id.add_const y))
    (fun x => hgd.comp (differentiable_id.const_add x))
    (fun i => by simp only [h₁]; exact hDm i) (fun i => by simp only [h₂]; exact hDm i)
    hc (fun p => hcg _) (fun p => (le_abs_self _).trans ((hM₀ _).trans (le_max_left _ _)))
    (fun p i => by simp only [h₁]; exact hDg _ i) (fun p i => by simp only [h₂]; exact hDg _ i)
  have hgs : ∀ p : (Fin d → ℝ) × (Fin d → ℝ),
      gradSqFst (fun p => g (p.1 + p.2)) p = gradSq g (p.1 + p.2) ∧
        gradSqSnd (fun p => g (p.1 + p.2)) p = gradSq g (p.1 + p.2) := fun p => by
    simp only [gradSqFst, gradSqSnd, gradSq, h₁, h₂, and_self]
  have hgradm : Measurable (gradSq g) := by
    unfold gradSq
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ g _).pow_const 2
  rw [ent_map _ hadd (hgm.pow_const 2),
    integral_map hadd.aemeasurable hgradm.aestronglyMeasurable]
  have hsum : ∫ p, (C₁ * gradSqFst (fun p => g (p.1 + p.2)) p +
      C₂ * gradSqSnd (fun p => g (p.1 + p.2)) p) ∂(μ.prod ν) =
      (C₁ + C₂) * ∫ p, gradSq g (p.1 + p.2) ∂(μ.prod ν) := by
    rw [← integral_const_mul]
    congr 1
    funext p
    rw [(hgs p).1, (hgs p).2]
    ring
  rw [hsum] at h
  linarith

/-- The isotropic heat kernel is the convolution with `N(0, t I)`:
`heatKernelPi t ∘ₘ π = (π ⊗ N(0, t I)).map (x, z) ↦ x + z` (for s-finite `π`). -/
theorem heatKernelPi_comp_eq_map_add (π : Measure (Fin d → ℝ)) [SFinite π] (t : ℝ≥0) :
    heatKernelPi t ∘ₘ π =
      (π.prod (Measure.pi fun _ : Fin d => gaussianReal 0 t)).map (fun p => p.1 + p.2) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply ((by fun_prop : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      p.1 + p.2) hs)]
  refine lintegral_congr fun x => ?_
  rw [heatKernelPi_apply, GaussianIncrement.pi_gaussianReal_eq_map,
    Measure.map_apply (by fun_prop) hs]
  congr 1
  ext y
  simp only [Set.mem_preimage, add_comm x y]
  rfl

/-- **LSI along the heat flow.** If `π` is a probability measure on `Fin d → ℝ` with
`FunctionalLSIPi π C`, and the Gaussian `N(0, t I)` satisfies `FunctionalLSIPi (N(0, t I)) t`
(the Gaussian LSI, taken here as a hypothesis), then
`FunctionalLSIPi (heatKernelPi t ∘ₘ π) (C + t)`. -/
theorem functionalLSIPi_heatKernelPi_comp {π : Measure (Fin d → ℝ)} [IsProbabilityMeasure π]
    {C : ℝ} (t : ℝ≥0) (hπ : FunctionalLSIPi π C)
    (hγ : FunctionalLSIPi (Measure.pi fun _ : Fin d => gaussianReal 0 t) t) :
    FunctionalLSIPi (heatKernelPi t ∘ₘ π) (C + t) := by
  rw [heatKernelPi_comp_eq_map_add]
  exact functionalLSIPi_map_add hπ hγ t.2

end FormalizeSampling.LogSobolevTensorPi
