module

public import FormalizeSampling.Flow.FokkerPlanckExistence

/-!
# Gaussian smoothing of test functions (heat operator)

Status: **Verified.** Infrastructure for the uniqueness proof of the weak Fokker–Planck equation
(`Flow/FokkerPlanckUniqueness.lean`). For `σ : ℝ` and `f : ℝᵈ → E` the Gaussian smoothing

  `heatOp σ f x = E f(x + σ Z)`, `Z ∼ N(0, I_d)` (`stdGauss`),

is the heat semigroup at time `σ² / 2`. Proved here:

* `abs_heatOp_le`, `continuous_heatOp`, `continuous_heatOp_joint`: sup-norm contraction and
  (joint) continuity for bounded continuous `f`;
* `hasFDerivAt_heatOp`: for `f ∈ C¹_c` (any complete target `E`), `D(heatOp σ f) =
  heatOp σ (Df)` (differentiation under the integral sign);
* `contDiff_heatOp_two`, `partialDeriv_heatOp`, `laplacian_heatOp`: for `φ ∈ C²_c`,
  `heatOp σ φ ∈ C²`, and partial derivatives and the Laplacian commute with `heatOp σ`.

## Not proved here

* The smoothing estimate `|∇ heatOp σ φ| ≤ ‖φ‖_∞ / σ` and the heat equation in `σ` are in
  separate files; nothing here uses `σ ≠ 0`.
* Only compactly supported `C¹`/`C²` inputs are treated (no `C^k_b` or `C^∞` statements).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gaussian smoothing `heatOp σ f x = E f(x + σ Z)`, `Z ∼ N(0, I_d)`. -/
noncomputable def heatOp (σ : ℝ) (f : (Fin d → ℝ) → E) (x : Fin d → ℝ) : E :=
  ∫ z, f (x + σ • z) ∂stdGauss

/-- `heatOp` is a sup-norm contraction: `|f| ≤ M` implies `|heatOp σ f| ≤ M`. -/
theorem abs_heatOp_le {f : (Fin d → ℝ) → ℝ} {M : ℝ} (hM : ∀ y, |f y| ≤ M) (σ : ℝ)
    (x : Fin d → ℝ) : |heatOp σ f x| ≤ M :=
  abs_integral_stdGauss_le fun _ => hM _

/-- For bounded continuous `f`, `(σ, x) ↦ heatOp σ f x` is jointly continuous (dominated
convergence). -/
theorem continuous_heatOp_joint {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) :
    Continuous (fun q : ℝ × (Fin d → ℝ) => heatOp q.1 f q.2) :=
  continuous_of_dominated (bound := fun _ => M)
    (fun q => (hf.comp (by fun_prop)).aestronglyMeasurable)
    (fun q => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM _)
    (integrable_const M) (ae_of_all _ fun z => hf.comp (by fun_prop))

/-- For a continuous compactly supported `f` (any normed target), `heatOp σ f` is
continuous. -/
theorem continuous_heatOp {f : (Fin d → ℝ) → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) (σ : ℝ) : Continuous (heatOp σ f) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  exact continuous_of_dominated (bound := fun _ => C)
    (fun x => (hf.comp (by fun_prop)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun z => hC _)
    (integrable_const C) (ae_of_all _ fun z => hf.comp (by fun_prop))

omit [NormedSpace ℝ E] in
/-- A continuous compactly supported `f` composed with `z ↦ x + σ z` is `stdGauss`-integrable. -/
theorem integrable_comp_shift {f : (Fin d → ℝ) → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) (σ : ℝ) (x : Fin d → ℝ) :
    Integrable (fun z => f (x + σ • z)) stdGauss := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  exact Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable C
    (ae_of_all _ fun z => hC _)

/-- **Differentiation under the Gaussian integral.** For `f ∈ C¹_c` (any normed target),
`heatOp σ f` has derivative `heatOp σ (Df)` at every point. -/
theorem hasFDerivAt_heatOp {f : (Fin d → ℝ) → E} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (σ : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (heatOp σ f) (heatOp σ (fderiv ℝ f) x) x := by
  have hf' : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support (hfc.fderiv (𝕜 := ℝ))
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun y z => fderiv ℝ f (y + σ • z)) univ_mem
    (Eventually.of_forall fun y => (hf.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_shift hf.continuous hfc σ x)
    (hf'.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z y _ => hC _) (integrable_const C)
    (ae_of_all _ fun z y _ => ?_)
  have := (hfd (y + σ • z)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const (σ • z))
  exact this

/-- For `φ ∈ C²_c`, `heatOp σ φ` is `C²`. -/
theorem contDiff_heatOp_two {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (σ : ℝ) : ContDiff ℝ 2 (heatOp σ φ) := by
  have h1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hDc : HasCompactSupport (fderiv ℝ φ) := hφc.fderiv (𝕜 := ℝ)
  have h2 : (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  rw [h2]
  refine contDiff_succ_iff_hasFDerivAt.2 ⟨heatOp σ (fderiv ℝ φ), ?_,
    fun x => hasFDerivAt_heatOp h1 hφc σ x⟩
  refine contDiff_one_iff_hasFDerivAt.2 ⟨heatOp σ (fderiv ℝ (fderiv ℝ φ)), ?_,
    fun x => hasFDerivAt_heatOp hD hDc σ x⟩
  exact continuous_heatOp (hD.continuous_fderiv one_ne_zero)
    (hDc.fderiv (𝕜 := ℝ)) σ

/-- Partial derivatives commute with Gaussian smoothing on `C¹_c`:
`∂ᵢ (heatOp σ φ) = heatOp σ (∂ᵢ φ)`. -/
theorem partialDeriv_heatOp {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (σ : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (heatOp σ φ) x = heatOp σ (partialDeriv i φ) x := by
  have hf' : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  rw [partialDeriv, (hasFDerivAt_heatOp hφ hφc σ x).fderiv, heatOp,
    ContinuousLinearMap.integral_apply (integrable_comp_shift hf' (hφc.fderiv (𝕜 := ℝ)) σ x)]
  rfl

/-- The Laplacian commutes with Gaussian smoothing on `C²_c`:
`Δ (heatOp σ φ) = heatOp σ (Δ φ)`. -/
theorem laplacian_heatOp {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (σ : ℝ) (x : Fin d → ℝ) :
    laplacian (heatOp σ φ) x = heatOp σ (laplacian φ) x := by
  have h1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hpc : ∀ i : Fin d, HasCompactSupport (partialDeriv i φ) := fun i =>
    hφc.mono' ((subset_tsupport _).trans (tsupport_partialDeriv_subset i φ))
  have hstep : ∀ i : Fin d, partialDeriv i (partialDeriv i (heatOp σ φ)) x =
      heatOp σ (partialDeriv i (partialDeriv i φ)) x := by
    intro i
    have e : partialDeriv i (heatOp σ φ) = heatOp σ (partialDeriv i φ) :=
      funext (partialDeriv_heatOp h1 hφc σ i)
    rw [e, partialDeriv_heatOp (contDiff_partialDeriv hφ i) (hpc i) σ i x]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun z => partialDeriv i (partialDeriv i φ) (x + σ • z)) stdGauss := by
    intro i _
    refine integrable_comp_shift (continuous_partialDeriv2 hφ i i) ?_ σ x
    exact hφc.mono' ((subset_tsupport _).trans ((tsupport_partialDeriv_subset i _).trans
        (tsupport_partialDeriv_subset i φ)))
  simp only [laplacian, hstep, heatOp]
  rw [← integral_finsetSum _ hint]

end FormalizeSampling.FokkerPlanckUniqueness
