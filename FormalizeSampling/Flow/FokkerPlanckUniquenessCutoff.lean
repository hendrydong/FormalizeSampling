module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import FormalizeSampling.Flow.ContinuityUniquenessAffine
public import FormalizeSampling.Flow.FokkerPlanckExistence

/-!
# Cutoffs, product rules and smooth approximation for Fokker–Planck uniqueness

Status: **Verified.** Elementary infrastructure for the uniqueness proof of the weak
Fokker–Planck equation (`Flow/FokkerPlanckUniqueness.lean`):

* `grad_mul`, `laplacian_mul`: product rules `∇(χ u) = χ ∇u + u ∇χ` and
  `Δ(χ u) = χ Δu + 2 ∇χ ⬝ ∇u + u Δχ` for the coordinate `grad`/`laplacian`;
* `grad_comp_smul`, `laplacian_comp_smul`: behaviour under the scaling `x ↦ c x`;
* `exists_cutoff`: smooth compactly supported cutoffs in `[0, 1]`, equal to `1` on a given
  compact set, with `‖∇χ‖ ≤ ε` and `|Δχ| ≤ ε`;
* `abs_integral_sub_le_of_smooth`: a bound `|∫ φ dμ - ∫ φ dν| ≤ M sup|φ|` on smooth compactly
  supported tests extends to continuous compactly supported tests (uniform smooth
  approximation from Mathlib's `Continuous.exists_contDiff_approx`).

## Not proved here

* No extension to bounded continuous (non compactly supported) or measurable test functions,
  i.e. no total-variation statement; no quantitative cutoff constants are exported.
* Nothing about the Fokker–Planck equation itself.
-/

public section

open MeasureTheory Matrix Set Filter Topology Metric
open scoped ContDiff

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-- Product rule for a partial derivative: `∂ᵢ(χ u) = χ ∂ᵢu + u ∂ᵢχ` (as functions). -/
theorem partialDeriv_mul {χ u : (Fin d → ℝ) → ℝ} (hχ : Differentiable ℝ χ)
    (hu : Differentiable ℝ u) (i : Fin d) :
    partialDeriv i (fun y => χ y * u y) =
      fun y => χ y * partialDeriv i u y + u y * partialDeriv i χ y := by
  funext y
  simp only [partialDeriv]
  rw [fderiv_fun_mul (hχ y) (hu y)]
  simp

/-- Partial derivatives are additive at points of differentiability. -/
theorem partialDeriv_add {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    partialDeriv i (fun y => f y + g y) x = partialDeriv i f x + partialDeriv i g x := by
  simp only [partialDeriv]
  rw [fderiv_fun_add hf hg]
  simp

/-- Product rule for the gradient: `∇(χ u) = χ ∇u + u ∇χ`. -/
theorem grad_mul {χ u : (Fin d → ℝ) → ℝ} (hχ : Differentiable ℝ χ) (hu : Differentiable ℝ u)
    (x : Fin d → ℝ) : grad (fun y => χ y * u y) x = χ x • grad u x + u x • grad χ x := by
  funext i
  simp only [grad, partialDeriv_mul hχ hu i, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Product rule for the Laplacian of `C²` functions:
`Δ(χ u) = χ Δu + 2 ∇χ ⬝ ∇u + u Δχ`. -/
theorem laplacian_mul {χ u : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u)
    (x : Fin d → ℝ) : laplacian (fun y => χ y * u y) x =
      χ x * laplacian u x + 2 * (grad χ x ⬝ᵥ grad u x) + u x * laplacian χ x := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hχi : ∀ i, Differentiable ℝ (partialDeriv i χ) := fun i =>
    (contDiff_partialDeriv hχ i).differentiable one_ne_zero
  have hui : ∀ i, Differentiable ℝ (partialDeriv i u) := fun i =>
    (contDiff_partialDeriv hu i).differentiable one_ne_zero
  simp only [laplacian, partialDeriv_mul hχd hud]
  have e : ∀ i, partialDeriv i
      (fun y => χ y * partialDeriv i u y + u y * partialDeriv i χ y) x =
      (χ x * partialDeriv i (partialDeriv i u) x + partialDeriv i u x * partialDeriv i χ x) +
      (u x * partialDeriv i (partialDeriv i χ) x + partialDeriv i χ x * partialDeriv i u x) := by
    intro i
    rw [partialDeriv_add (f := fun y => χ y * partialDeriv i u y)
      (g := fun y => u y * partialDeriv i χ y) ((hχd x).mul (hui i x)) ((hud x).mul (hχi i x)),
      congrFun (partialDeriv_mul hχd (hui i) i) x, congrFun (partialDeriv_mul hud (hχi i) i) x]
  simp only [e, dotProduct, grad, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


/-- Scaling rule: `∂ᵢ (f(c ·))(x) = c ∂ᵢf(c x)` for differentiable `f`. -/
theorem partialDeriv_comp_smul {f : (Fin d → ℝ) → ℝ} (hf : Differentiable ℝ f) (c : ℝ)
    (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (fun y => f (c • y)) x = c * partialDeriv i f (c • x) := by
  have h : HasFDerivAt (fun y : Fin d → ℝ => f (c • y))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ (Fin d → ℝ))) x :=
    (hf (c • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  simp only [partialDeriv, h.fderiv, ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- `∂ᵢ (c f) = c ∂ᵢ f` at points of differentiability of `f`. -/
theorem partialDeriv_const_mul {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin d) :
    partialDeriv i (fun y => c * f y) x = c * partialDeriv i f x := by
  simp only [partialDeriv]
  rw [fderiv_const_mul hf]
  simp

/-- Scaling rule for the gradient: `∇(f(c ·))(x) = c ∇f(c x)`. -/
theorem grad_comp_smul {f : (Fin d → ℝ) → ℝ} (hf : Differentiable ℝ f) (c : ℝ)
    (x : Fin d → ℝ) : grad (fun y => f (c • y)) x = c • grad f (c • x) := by
  funext i
  simp only [grad, partialDeriv_comp_smul hf c i x, Pi.smul_apply, smul_eq_mul]

/-- Scaling rule for the Laplacian of a `C²` function: `Δ(f(c ·))(x) = c² Δf(c x)`. -/
theorem laplacian_comp_smul {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ)
    (x : Fin d → ℝ) : laplacian (fun y => f (c • y)) x = c ^ 2 * laplacian f (c • x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfi : ∀ i, Differentiable ℝ (partialDeriv i f) := fun i =>
    (contDiff_partialDeriv hf i).differentiable one_ne_zero
  simp only [laplacian, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : partialDeriv i (fun y => f (c • y)) = fun y => c * partialDeriv i f (c • y) :=
    funext fun y => partialDeriv_comp_smul hfd c i y
  rw [e, partialDeriv_const_mul (f := fun y => partialDeriv i f (c • y))
      ((hfi i).comp (differentiable_id.const_smul c) x),
    partialDeriv_comp_smul (hfi i) c i x]
  ring

/-- **Cutoffs with small derivatives.** For a compact `K ⊆ ℝᵈ` and `ε > 0` there is a smooth
compactly supported `χ` with values in `[0, 1]`, equal to `1` on `K`, with `‖∇χ‖ ≤ ε` and
`|Δχ| ≤ ε` everywhere (a fixed bump rescaled by a large factor `R`). -/
theorem exists_cutoff {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, χ x ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ K, χ x = 1) ∧ (∀ x, ‖grad χ x‖ ≤ ε) ∧ (∀ x, |laplacian χ x| ≤ ε) := by
  obtain ⟨χ₁, hχ₁, hχ₁c, hI, h1, -⟩ :=
    exists_smooth_one_on_compact (isCompact_closedBall (0 : Fin d → ℝ) 1) one_pos
  have hχ₂ : ContDiff ℝ 2 χ₁ := hχ₁.of_le (by norm_cast)
  obtain ⟨A, hA⟩ := (continuous_grad hχ₂).bounded_above_of_compact_support
    (HasCompactSupport.intro hχ₁c.isCompact fun z hz =>
      ContinuityEquation.grad_eq_zero_of_notMem_tsupport hz)
  obtain ⟨A', hA'⟩ := (continuous_laplacian hχ₂).bounded_above_of_compact_support
    (hasCompactSupport_laplacian hχ₁c)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
  set R : ℝ := max (max r 1) (max (A / ε) (A' / ε)) with hRdef
  have hR1 : 1 ≤ R := (le_max_right r 1).trans (le_max_left _ _)
  have hR0 : 0 < R := one_pos.trans_le hR1
  have hRr : r ≤ R := (le_max_left r 1).trans (le_max_left _ _)
  have hRA : A ≤ ε * R := by
    have : A / ε ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hε] at this; linarith
  have hRA' : A' ≤ ε * R := by
    have : A' / ε ≤ R := (le_max_right _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hε] at this; linarith
  have hRi : R⁻¹ ≠ 0 := inv_ne_zero hR0.ne'
  refine ⟨fun x => χ₁ (R⁻¹ • x), hχ₁.comp (contDiff_const_smul _), ?_, fun x => hI _,
    fun x hx => h1 _ ?_, fun x => ?_, fun x => ?_⟩
  · exact hχ₁c.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ hRi)
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hR0), inv_mul_le_iff₀ hR0, mul_one]
    have := hr hx
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  · rw [grad_comp_smul (hχ₂.differentiable (by norm_num)), norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hR0), inv_mul_le_iff₀ hR0]
    linarith [hA (R⁻¹ • x)]
  · rw [laplacian_comp_smul hχ₂, abs_mul, abs_of_nonneg (by positivity)]
    have hl : |laplacian χ₁ (R⁻¹ • x)| ≤ A' := by
      simpa [Real.norm_eq_abs] using hA' (R⁻¹ • x)
    have hA'0 : 0 ≤ A' := (abs_nonneg _).trans hl
    have hRsq : (R⁻¹) ^ 2 ≤ R⁻¹ := by
      rw [sq]
      exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hR1)
    calc (R⁻¹) ^ 2 * |laplacian χ₁ (R⁻¹ • x)| ≤ R⁻¹ * A' :=
          mul_le_mul hRsq hl (abs_nonneg _) (by positivity)
      _ ≤ ε := by rw [inv_mul_le_iff₀ hR0]; linarith

/-- **From smooth compactly supported tests to continuous compactly supported ones.** If two
probability measures satisfy `|∫ φ dμ - ∫ φ dν| ≤ M C` for every smooth compactly supported `φ`
with `|φ| ≤ C`, then the same bound holds for every continuous compactly supported `g` with
`|g| ≤ C` (uniform smooth approximation, `Continuous.exists_contDiff_approx`). -/
theorem abs_integral_sub_le_of_smooth {μ ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ C : ℝ,
      (∀ x, |φ x| ≤ C) → |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ M * C)
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) : |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ M * C := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  set ε : ℝ := η / (M + 2) with hεdef
  have hε : 0 < ε := div_pos hη (by linarith)
  obtain ⟨φ, hφ, hdist, hsupp⟩ :=
    hg.exists_contDiff_approx (n := ⊤) (ε := fun _ => ε) continuous_const fun _ => hε
  have hφc : HasCompactSupport φ := hgc.mono hsupp
  have hφd : ∀ x, |g x - φ x| ≤ ε := fun x => by
    have := (hdist x).le
    rwa [Real.dist_eq, abs_sub_comm] at this
  have hφC : ∀ x, |φ x| ≤ C + ε := fun x => by
    have := abs_sub_abs_le_abs_sub (φ x) (g x)
    rw [abs_sub_comm] at this
    linarith [hC x, hφd x]
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have key := h φ hφ' hφc (C + ε) hφC
  have hcomp : ∀ (m : Measure (Fin d → ℝ)) [IsProbabilityMeasure m],
      |∫ x, g x ∂m - ∫ x, φ x ∂m| ≤ ε := by
    intro m _
    rw [← integral_sub (hg.integrable_of_hasCompactSupport hgc)
      (hφ'.continuous.integrable_of_hasCompactSupport hφc)]
    exact abs_integral_le_of_abs_le hφd
  have e1 := hcomp μ
  have e2 := hcomp ν
  have hεη : (M + 2) * ε = η := by rw [hεdef]; field_simp
  calc |∫ x, g x ∂μ - ∫ x, g x ∂ν|
      ≤ |∫ x, g x ∂μ - ∫ x, φ x ∂μ| + |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| +
          |∫ x, φ x ∂ν - ∫ x, g x ∂ν| := by
        have := abs_sub_le (∫ x, g x ∂μ) (∫ x, φ x ∂ν) (∫ x, g x ∂ν)
        have := abs_sub_le (∫ x, g x ∂μ) (∫ x, φ x ∂μ) (∫ x, φ x ∂ν)
        linarith
    _ ≤ ε + M * (C + ε) + ε := by
        rw [abs_sub_comm (∫ x, φ x ∂ν)]; linarith
    _ = M * C + η := by linarith

end FormalizeSampling.FokkerPlanckUniqueness
