module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import FormalizeSampling.Flow.OULangevinDecayPi
public import FormalizeSampling.Flow.ContinuityUniquenessAffine
public import FormalizeSampling.Identities.GaussianStein

/-!
# The weak Fokker–Planck equation for the heat and Ornstein–Uhlenbeck flows

Status: **Verified.** Discharges the named Itô input `NoiseScore.WeakFokkerPlanck` of FL-5
(`Flow/NoiseScoreEquivalence.lean`) for two explicit transition semigroups on `Fin d → ℝ`,
started from an **arbitrary** probability measure `ρ₀` (no density, moment or regularity
assumption). No SDE is involved: `WeakFokkerPlanck` is a statement about a curve of laws, and
the curves here are defined through explicit Gaussian kernels.

* Heat flow: `ρ t = heatKernelPi t.toNNReal ∘ₘ ρ₀` (variance `t` per coordinate; `t < 0` is
  mapped to variance `0` by `toNNReal`, which is irrelevant since only `t ≥ 0` matters) solves
  `WeakFokkerPlanck ρ 0 (1/2)` (`weakFokkerPlanck_heat`).
* OU flow: `ρ t = ouKernelVarPi v a t ∘ₘ ρ₀` (`v > 0`, `a ≥ 0`) solves
  `WeakFokkerPlanck ρ (fun _ x => -a • x) (a v)` (`weakFokkerPlanck_ouVar`), and
  `ρ t = ouKernelPi a t ∘ₘ ρ₀` solves it with `D = a` (`weakFokkerPlanck_ou`).

## Method

For `t ≥ 0`, `ρ t` is the law of `e^{-at} X + σ_t Z` with `X ∼ ρ₀`, `Z ∼ N(0, I_d)` independent
(`gaussPush`, `heatKernelPi_comp_map_scalePi`), so `∫ φ dρ_t = E[φ(e^{-at} X + σ_t Z)]`.
For `t > 0` we differentiate under the expectation (dominated by `C (1 + ‖Z‖)` thanks to the
compact support of `φ`), and integrate the `Z`-term by parts with the `d`-dimensional Stein
identity (ID-1, `GaussianStein.integral_coord_mul_eq_integral_partialDeriv`):
`d/dt E φ(Y_t) = E[(-a Y_t) ⬝ ∇φ(Y_t) + (σ σ' + a σ²) Δφ(Y_t)]`, and `σ σ' + a σ² = D` is
constant (`= 1/2` for the heat flow, `= a v` for OU). At `t = 0`, where `σ_t ∼ √t` is not
differentiable, the right derivative follows from continuity of `t ↦ ∫ Lφ dρ_t` on `[0, ∞)`
(`hasDerivWithinAt_Ici_of_tendsto_deriv`).

## Main results

* `weakFokkerPlanck_of_gaussPush`: the abstract statement for curves `e^{-at} X + σ_t Z`.
* `weakFokkerPlanck_heat`, `weakFokkerPlanck_ouVar`, `weakFokkerPlanck_ou`.
* Auxiliary: `pi_gaussianReal_eq_map`, `heatKernelPi_comp_map_scalePi`,
  `integral_coord_mul_comp` (scaled Stein identity), `integral_fderiv_eq_integral_ouGen`,
  `hasDerivAt_integral_comp`, `grad_laplacian_eq_zero_of_notMem_tsupport`.

## Not proved here

* Nothing about SDEs, Brownian motion or Itô's formula: the curves are defined by kernels,
  and identifying them with laws of SDE solutions is a modelling statement, not a theorem here.
* The degenerate OU case `v = 0` with `a > 0` (deterministic contraction, `D = 0`) is not
  covered (`a = 0` is: the curve is constant).
* Only scalar drift coefficients `-a x` and isotropic diffusion; no general linear SDE
  `dX = A X dt + Σ dW`, no non-Gaussian transition semigroups.
* Two-sided derivatives at `t = 0` (only the right derivative, as `WeakFokkerPlanck` requires).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ContDiff

namespace FormalizeSampling.WeakFokkerPlanckOU
open FormalizeSampling.HeatKernelPi FormalizeSampling.OULangevinDecayPi NoiseScore
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi)

variable {d : ℕ}

/-- The standard Gaussian `N(0, I_d)` on `Fin d → ℝ`, as the product of `d` copies of
`gaussianReal 0 1`. -/
noncomputable def stdGauss : Measure (Fin d → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- `N(0, I_d)` is a probability measure. -/
instance isProbabilityMeasure_stdGauss : IsProbabilityMeasure (stdGauss (d := d)) := by
  unfold stdGauss; infer_instance

/-- The law of `c X + σ Z` for independent `X ∼ ρ₀` and `Z ∼ N(0, I_d)`: the pushforward of
`ρ₀ ⊗ N(0, I_d)` by `(x, z) ↦ c • x + σ • z`. -/
noncomputable def gaussPush (ρ₀ : Measure (Fin d → ℝ)) (c σ : ℝ) : Measure (Fin d → ℝ) :=
  (ρ₀.prod stdGauss).map fun q => c • q.1 + σ • q.2

/-- `N(m, s I) = (z ↦ m + √s z)_# N(0, I_d)` on `Fin d → ℝ`. -/
theorem pi_gaussianReal_eq_map (m : Fin d → ℝ) (s : ℝ≥0) :
    Measure.pi (fun i => gaussianReal (m i) s) =
      (stdGauss (d := d)).map (fun z => m + Real.sqrt s • z) := by
  have h : (fun z : Fin d → ℝ => m + Real.sqrt s • z) = fun z i => m i + Real.sqrt s * z i := rfl
  rw [stdGauss, h, Measure.pi_map_pi (f := fun i u => m i + Real.sqrt s * u) (fun i => by fun_prop)]
  congr 1
  funext i
  have : (fun u : ℝ => m i + Real.sqrt s * u) = (fun u => m i + u) ∘ (fun u => Real.sqrt s * u) :=
    rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · simp
  · apply NNReal.eq; simp [Real.sq_sqrt s.coe_nonneg]

/-- **Representation of a scaled heat step.** For an s-finite `ρ₀`, `c : ℝ` and variance
`s ≥ 0`, `heatKernelPi s ∘ₘ (c •)_# ρ₀` is the law of `c X + √s Z`, `X ∼ ρ₀ ⊥ Z ∼ N(0, I_d)`. -/
theorem heatKernelPi_comp_map_scalePi (ρ₀ : Measure (Fin d → ℝ)) [SFinite ρ₀] (c : ℝ)
    (s : ℝ≥0) :
    heatKernelPi s ∘ₘ ρ₀.map (scalePi c) = gaussPush ρ₀ c (Real.sqrt s) := by
  ext A hA
  have hf : Measurable fun q : (Fin d → ℝ) × (Fin d → ℝ) => c • q.1 + Real.sqrt s • q.2 := by
    fun_prop
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hA) (measurable_scalePi _), gaussPush,
    Measure.map_apply hf hA, Measure.prod_apply (hf hA)]
  refine lintegral_congr fun x => ?_
  rw [heatKernelPi_apply, pi_gaussianReal_eq_map (scalePi c x) s,
    Measure.map_apply (by fun_prop) hA]
  rfl


/-- Each coordinate `z ↦ zᵢ` is integrable under `N(0, I_d)`. -/
theorem integrable_coord (i : Fin d) : Integrable (fun z : Fin d → ℝ => z i) stdGauss :=
  (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).integrable_comp_of_integrable
    (g := fun u : ℝ => u) IsGaussian.integrable_fun_id

/-- The (sup) norm `z ↦ ‖z‖` is integrable under `N(0, I_d)`. -/
theorem integrable_norm_stdGauss : Integrable (fun z : Fin d → ℝ => ‖z‖) stdGauss := by
  refine (integrable_finsetSum Finset.univ fun i _ => (integrable_coord i).abs).mono'
    continuous_norm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_norm]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- **Scaled Gaussian integration by parts.** For `g` `C¹` with compact support, `w : ℝᵈ` and
`σ ≠ 0`, `E[Zᵢ g(w + σ Z)] = σ E[∂ᵢ g(w + σ Z)]` for `Z ∼ N(0, I_d)` (from the `d`-dimensional
Stein identity `GaussianStein.integral_coord_mul_eq_integral_partialDeriv`). -/
theorem integral_coord_mul_comp {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (w : Fin d → ℝ) {σ : ℝ} (hσ : σ ≠ 0) (i : Fin d) :
    ∫ z, z i * g (w + σ • z) ∂stdGauss =
      σ * ∫ z, partialDeriv i g (w + σ • z) ∂stdGauss := by
  set e : (Fin d → ℝ) ≃ₜ (Fin d → ℝ) :=
    (Homeomorph.smulOfNeZero σ hσ).trans (Homeomorph.addLeft w)
  have hh : ContDiff ℝ 1 (fun z => g (w + σ • z)) :=
    hg.comp (contDiff_const.add (contDiff_id.const_smul σ))
  have hhc : HasCompactSupport (fun z => g (w + σ • z)) := hgc.comp_homeomorph e
  have hpd : ∀ z, partialDeriv i (fun z => g (w + σ • z)) z =
      σ * partialDeriv i g (w + σ • z) := by
    intro z
    have hA : HasFDerivAt (fun z : Fin d → ℝ => w + σ • z)
        (σ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) z :=
      ((hasFDerivAt_id z).const_smul σ).const_add w
    have := ((hg.differentiable one_ne_zero _).hasFDerivAt.comp z hA).fderiv
    simp only [partialDeriv]
    rw [show (fun z => g (w + σ • z)) = g ∘ (fun z => w + σ • z) from rfl, this]
    simp
  have key := GaussianStein.integral_coord_mul_eq_integral_partialDeriv hh hhc i
  simp only [stdGauss] at key ⊢
  rw [key]
  simp_rw [hpd]
  exact integral_const_mul _ _


/-- The OU generator `L φ(y) = (-a y) ⬝ ∇φ(y) + D Δφ(y)` (drift `b(y) = -a y`, diffusion
`D`); this is exactly the integrand of `WeakFokkerPlanck` for `b t x = -a • x`. -/
noncomputable def ouGen (a D : ℝ) (φ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  (-a • y) ⬝ᵥ grad φ y + D * laplacian φ y

section TestFunction

variable {φ : (Fin d → ℝ) → ℝ}

/-- For `φ ∈ C²`, each partial derivative `∂ᵢφ` is `C¹`. -/
theorem contDiff_partialDeriv (hφ : ContDiff ℝ 2 φ) (i : Fin d) :
    ContDiff ℝ 1 (partialDeriv i φ) :=
  (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- For `φ ∈ C²`, each second partial derivative `∂ᵢ∂ⱼφ` is continuous. -/
theorem continuous_partialDeriv2 (hφ : ContDiff ℝ 2 φ) (i j : Fin d) :
    Continuous (partialDeriv i (partialDeriv j φ)) :=
  ((contDiff_partialDeriv hφ j).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- For `φ ∈ C²`, the gradient `∇φ` is continuous. -/
theorem continuous_grad (hφ : ContDiff ℝ 2 φ) : Continuous (grad φ) :=
  continuous_pi fun i => (contDiff_partialDeriv hφ i).continuous

/-- For `φ ∈ C²`, the Laplacian `Δφ` is continuous. -/
theorem continuous_laplacian (hφ : ContDiff ℝ 2 φ) : Continuous (laplacian φ) :=
  continuous_finsetSum _ fun i _ => continuous_partialDeriv2 hφ i i

/-- `tsupport (∂ᵢ f) ⊆ tsupport f`. -/
theorem tsupport_partialDeriv_subset (i : Fin d) (f : (Fin d → ℝ) → ℝ) :
    tsupport (partialDeriv i f) ⊆ tsupport f := by
  refine (closure_mono fun x hx => ?_).trans (tsupport_fderiv_subset ℝ (f := f))
  intro h0
  apply hx
  simp [partialDeriv, h0]

/-- Outside the topological support of a function its gradient and Laplacian vanish. -/
theorem grad_laplacian_eq_zero_of_notMem_tsupport {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hx : x ∉ tsupport f) : grad f x = 0 ∧ laplacian f x = 0 := by
  have h1 : ∀ i, partialDeriv i f x = 0 := fun i => image_eq_zero_of_notMem_tsupport
    fun h => hx (tsupport_partialDeriv_subset i f h)
  have h2 : ∀ i, partialDeriv i (partialDeriv i f) x = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport fun h =>
      hx ((tsupport_partialDeriv_subset i _).trans (tsupport_partialDeriv_subset i f) h)
  exact ⟨funext fun i => h1 i, by simp [laplacian, h2]⟩

/-- For `φ ∈ C²`, the generator `L φ` is continuous. -/
theorem continuous_ouGen (hφ : ContDiff ℝ 2 φ) (a D : ℝ) : Continuous (ouGen a D φ) :=
  show Continuous fun y => (-a • y) ⬝ᵥ grad φ y + D * laplacian φ y from
  (Continuous.dotProduct (A := fun y : Fin d → ℝ => -a • y) (by fun_prop)
    (continuous_grad hφ)).add (continuous_const.mul (continuous_laplacian hφ))

/-- For compactly supported `φ`, the generator `L φ` is compactly supported. -/
theorem hasCompactSupport_ouGen (hφc : HasCompactSupport φ) (a D : ℝ) :
    HasCompactSupport (ouGen a D φ) := by
  refine hφc.mono' fun y hy => ?_
  by_contra hn
  apply hy
  have h1 : ∀ i, partialDeriv i φ y = 0 := fun i => image_eq_zero_of_notMem_tsupport
    fun h => hn (tsupport_partialDeriv_subset i φ h)
  have h2 : ∀ i, partialDeriv i (partialDeriv i φ) y = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport fun h =>
      hn ((tsupport_partialDeriv_subset i _).trans (tsupport_partialDeriv_subset i φ) h)
  simp [ouGen, grad, laplacian, h1, h2, dotProduct]

end TestFunction

/-- For bounded continuous `ψ` and coefficients `c, σ` continuous on `S`, the map
`t ↦ E[ψ(c t X + σ t Z)]` (`X ∼ ρ₀ ⊥ Z ∼ N(0, I_d)`) is continuous on `S` (dominated
convergence). -/
theorem continuousOn_integral_comp {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) {C : ℝ}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (ρ₀ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ₀] {c σ : ℝ → ℝ}
    {S : Set ℝ} (hc : ContinuousOn c S) (hσ : ContinuousOn σ S) :
    ContinuousOn (fun t => ∫ q, ψ (c t • q.1 + σ t • q.2) ∂(ρ₀.prod stdGauss)) S := by
  refine continuousOn_of_dominated (bound := fun _ => C) (fun t _ => ?_)
    (fun t _ => ae_of_all _ fun q => hC _) (integrable_const C) (ae_of_all _ fun q => ?_)
  · exact (hψ.comp (by fun_prop)).aestronglyMeasurable
  · exact hψ.comp_continuousOn ((hc.smul continuousOn_const).add (hσ.smul continuousOn_const))

/-- `(x, z) ↦ ψ(c x + σ z)` is integrable under `ρ₀ ⊗ N(0, I_d)` for bounded continuous
`ψ`. -/
theorem integrable_comp_of_bound {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) {C : ℝ}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (ρ₀ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ₀] (c σ : ℝ) :
    Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) => ψ (c • q.1 + σ • q.2))
      (ρ₀.prod stdGauss) :=
  Integrable.of_bound (hψ.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun _ => hC _)


/-- `(x, z) ↦ zᵢ g(c x + σ z)` is integrable under `ρ₀ ⊗ N(0, I_d)` for bounded continuous
`g`. -/
theorem integrable_coord_mul_comp {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, ‖g y‖ ≤ C) (ρ₀ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ₀] (c σ : ℝ)
    (i : Fin d) :
    Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) => q.2 i * g (c • q.1 + σ • q.2))
      (ρ₀.prod stdGauss) := by
  refine (((integrable_coord i).comp_snd ρ₀).norm.const_mul C).mono'
    (((continuous_apply i).comp continuous_snd).mul (hg.comp (by fun_prop))).aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

section Core

variable {φ : (Fin d → ℝ) → ℝ}

/-- Pointwise algebra behind the time derivative: with `y = c x + σ z`,
`Dφ(y)[(-a c) x + τ z] = (-a y) ⬝ ∇φ(y) + (τ + a σ) (z ⬝ ∇φ(y))`. -/
theorem fderiv_apply_decomp (a c σ τ : ℝ) (x z : Fin d → ℝ) :
    fderiv ℝ φ (c • x + σ • z) ((-a * c) • x + τ • z) =
      (-a • (c • x + σ • z)) ⬝ᵥ grad φ (c • x + σ • z) +
        (τ + a * σ) * (z ⬝ᵥ grad φ (c • x + σ • z)) := by
  have hv : (-a * c) • x + τ • z = -a • (c • x + σ • z) + (τ + a * σ) • z := by module
  rw [hv, map_add, map_smul, map_smul, ← dotProduct_grad, ← dotProduct_grad, smul_eq_mul,
    smul_eq_mul, smul_dotProduct, smul_eq_mul]

/-- **Stein step.** For `φ ∈ C²_c`, `σ ≠ 0` and `y = c X + σ Z` (`X ∼ ρ₀ ⊥ Z ∼ N(0, I_d)`),
`E[Dφ(y)[(-a c) X + τ Z]] = E[(-a y) ⬝ ∇φ(y) + (σ τ + a σ²) Δφ(y)]`. The `Z`-term is
integrated by parts in `Z` coordinatewise (`integral_coord_mul_comp`) after Fubini. -/
theorem integral_fderiv_eq_integral_ouGen (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (a c : ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (τ : ℝ) :
    ∫ q, fderiv ℝ φ (c • q.1 + σ • q.2) ((-a * c) • q.1 + τ • q.2) ∂(ρ₀.prod stdGauss) =
      ∫ q, ouGen a (σ * τ + a * σ ^ 2) φ (c • q.1 + σ • q.2) ∂(ρ₀.prod stdGauss) := by
  have eP : (fun y => (-a • y) ⬝ᵥ grad φ y) = ouGen a 0 φ := funext fun y => by simp [ouGen]
  have eL : laplacian φ = ouGen 0 1 φ := funext fun y => by simp [ouGen]
  have hP : HasCompactSupport fun y => (-a • y) ⬝ᵥ grad φ y := by
    rw [eP]; exact hasCompactSupport_ouGen hφc a 0
  have hPc : Continuous fun y => (-a • y) ⬝ᵥ grad φ y := by
    rw [eP]; exact continuous_ouGen hφ a 0
  have hL : HasCompactSupport (laplacian φ) := by
    rw [eL]; exact hasCompactSupport_ouGen hφc 0 1
  obtain ⟨CP, hCP⟩ := hPc.bounded_above_of_compact_support hP
  obtain ⟨CL, hCL⟩ := (continuous_laplacian hφ).bounded_above_of_compact_support hL
  have hdc : ∀ i, HasCompactSupport (partialDeriv i φ) := fun i =>
    hφc.fderiv_apply ℝ (Pi.single i 1)
  have hd2 : ∀ i, HasCompactSupport (partialDeriv i (partialDeriv i φ)) := fun i =>
    (hdc i).fderiv_apply ℝ (Pi.single i 1)
  have hPint := integrable_comp_of_bound hPc hCP ρ₀ c σ
  have hLint := integrable_comp_of_bound (continuous_laplacian hφ) hCL ρ₀ c σ
  have hQint : Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
      q.2 ⬝ᵥ grad φ (c • q.1 + σ • q.2)) (ρ₀.prod stdGauss) := by
    simp only [dotProduct, grad]
    refine integrable_finsetSum _ fun i _ => ?_
    obtain ⟨C, hC⟩ := (contDiff_partialDeriv hφ i).continuous.bounded_above_of_compact_support
      (hdc i)
    exact integrable_coord_mul_comp (contDiff_partialDeriv hφ i).continuous hC ρ₀ c σ i
  have hQ : ∫ q, q.2 ⬝ᵥ grad φ (c • q.1 + σ • q.2) ∂(ρ₀.prod stdGauss) =
      σ * ∫ q, laplacian φ (c • q.1 + σ • q.2) ∂(ρ₀.prod stdGauss) := by
    rw [integral_prod _ hQint, integral_prod _ hLint, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [dotProduct, grad, laplacian]
    have hi1 : ∀ i ∈ Finset.univ, Integrable
        (fun z : Fin d → ℝ => z i * partialDeriv i φ (c • x + σ • z)) stdGauss := by
      intro i _
      obtain ⟨C, hC⟩ :=
        (contDiff_partialDeriv hφ i).continuous.bounded_above_of_compact_support (hdc i)
      exact ((integrable_coord i).norm.const_mul C).mono'
        ((continuous_apply i).mul ((contDiff_partialDeriv hφ i).continuous.comp
          (by fun_prop))).aestronglyMeasurable
        (ae_of_all _ fun z => by
          rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
    have hi2 : ∀ i ∈ Finset.univ, Integrable
        (fun z : Fin d → ℝ => partialDeriv i (partialDeriv i φ) (c • x + σ • z)) stdGauss := by
      intro i _
      obtain ⟨C, hC⟩ := (continuous_partialDeriv2 hφ i i).bounded_above_of_compact_support (hd2 i)
      exact Integrable.of_bound ((continuous_partialDeriv2 hφ i i).comp
        (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hC _)
    rw [integral_finsetSum _ hi1, integral_finsetSum _ hi2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_coord_mul_comp (contDiff_partialDeriv hφ i) (hdc i) (c • x) hσ i
  have hpt : ∀ q : (Fin d → ℝ) × (Fin d → ℝ),
      fderiv ℝ φ (c • q.1 + σ • q.2) ((-a * c) • q.1 + τ • q.2) =
        (-a • (c • q.1 + σ • q.2)) ⬝ᵥ grad φ (c • q.1 + σ • q.2) +
          (τ + a * σ) * (q.2 ⬝ᵥ grad φ (c • q.1 + σ • q.2)) := fun q =>
    fderiv_apply_decomp a c σ τ q.1 q.2
  simp_rw [hpt]
  simp only [ouGen]
  rw [integral_add hPint (hQint.const_mul _), integral_add hPint (hLint.const_mul _),
    integral_const_mul, integral_const_mul, hQ]
  ring


/-- **Time derivative of the Gaussian representation (`t₀ > 0`).** For `φ ∈ C²_c`, a
probability `ρ₀`, `a : ℝ`, and `σ` differentiable on `(0, ∞)` with continuous derivative `σ'`
there and `σ ≠ 0` there,
`d/dt E[φ(e^{-at} X + σ_t Z)] = E[(L φ)(e^{-at} X + σ_t Z)]` at every `t₀ > 0`, where `L` is
`ouGen a (σ σ' + a σ²)`. Differentiation under the integral sign is dominated using the
compact support of `φ` (which controls the unbounded factor `e^{-at} X`). -/
theorem hasDerivAt_integral_comp (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (a : ℝ) {σ σ' : ℝ → ℝ}
    (hσd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt σ (σ' t) t) (hσ' : ContinuousOn σ' (Ioi 0))
    (hσ0 : ∀ t ∈ Ioi (0 : ℝ), σ t ≠ 0) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => ∫ q, φ (Real.exp (-a * t) • q.1 + σ t • q.2) ∂(ρ₀.prod stdGauss))
      (∫ q, ouGen a (σ t₀ * σ' t₀ + a * σ t₀ ^ 2) φ
        (Real.exp (-a * t₀) • q.1 + σ t₀ • q.2) ∂(ρ₀.prod stdGauss)) t₀ := by
  have hK : closedBall t₀ (t₀ / 2) ⊆ Ioi 0 := by
    intro t ht
    rw [mem_closedBall, Real.dist_eq, abs_le] at ht
    simp only [mem_Ioi]
    linarith [ht.1]
  have hσc : ContinuousOn σ (closedBall t₀ (t₀ / 2)) := fun t ht =>
    (hσd t (hK ht)).continuousAt.continuousWithinAt
  obtain ⟨S, hS⟩ := (isCompact_closedBall t₀ (t₀ / 2)).exists_bound_of_continuousOn hσc
  obtain ⟨S', hS'⟩ :=
    (isCompact_closedBall t₀ (t₀ / 2)).exists_bound_of_continuousOn (hσ'.mono hK)
  obtain ⟨M, hM⟩ :=
    (hφ.continuous_fderiv two_ne_zero).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  set R := max R₀ 0 with hRdef
  have hout : ∀ y, y ∈ tsupport φ → ‖y‖ ≤ R := fun y hy => by
    have := hR₀ hy
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have ht₀K : t₀ ∈ closedBall t₀ (t₀ / 2) := mem_closedBall_self (by linarith)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS t₀ ht₀K)
  have hS'0 : 0 ≤ S' := (norm_nonneg _).trans (hS' t₀ ht₀K)
  have hR0 : 0 ≤ R := le_max_right _ _
  have hdiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hn : Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) => ‖q.2‖) (ρ₀.prod stdGauss) :=
    integrable_norm_stdGauss.comp_snd ρ₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := ρ₀.prod stdGauss)
    (F := fun t (q : (Fin d → ℝ) × (Fin d → ℝ)) => φ (Real.exp (-a * t) • q.1 + σ t • q.2))
    (F' := fun t q => fderiv ℝ φ (Real.exp (-a * t) • q.1 + σ t • q.2)
      ((-a * Real.exp (-a * t)) • q.1 + σ' t • q.2)) (x₀ := t₀)
    (bound := fun q => M * (|a| * (R + S * ‖q.2‖) + S' * ‖q.2‖))
    (ball_mem_nhds t₀ (by linarith : (0 : ℝ) < t₀ / 2))
    (Eventually.of_forall fun t => (hφ.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_of_bound hφ.continuous hC ρ₀ _ _)
    (((hφ.continuous_fderiv two_ne_zero).comp (by fun_prop)).clm_apply
      (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun q t ht => ?_)
    ((((integrable_const R).add (hn.const_mul S)).const_mul |a|).add
      (hn.const_mul S') |>.const_mul M)
    (ae_of_all _ fun q t ht => ?_)
  · rw [← integral_fderiv_eq_integral_ouGen hφ hφc ρ₀ a _ (hσ0 t₀ ht₀)]
    exact key.2
  · have htK : t ∈ closedBall t₀ (t₀ / 2) := ball_subset_closedBall ht
    set y := Real.exp (-a * t) • q.1 + σ t • q.2 with hy
    by_cases hys : y ∈ tsupport φ
    · have hσt : ‖σ t‖ ≤ S := hS t htK
      have hσ't : ‖σ' t‖ ≤ S' := hS' t htK
      have hx : ‖Real.exp (-a * t) • q.1‖ ≤ R + S * ‖q.2‖ := by
        have e : Real.exp (-a * t) • q.1 = y - σ t • q.2 := by rw [hy]; abel
        rw [e]
        calc ‖y - σ t • q.2‖ ≤ ‖y‖ + ‖σ t • q.2‖ := norm_sub_le _ _
          _ ≤ R + S * ‖q.2‖ := add_le_add (hout y hys)
              (by rw [norm_smul]; exact mul_le_mul_of_nonneg_right hσt (norm_nonneg _))
      have hv : ‖(-a * Real.exp (-a * t)) • q.1 + σ' t • q.2‖ ≤
          |a| * (R + S * ‖q.2‖) + S' * ‖q.2‖ := by
        calc _ ≤ ‖(-a * Real.exp (-a * t)) • q.1‖ + ‖σ' t • q.2‖ := norm_add_le _ _
          _ = |a| * ‖Real.exp (-a * t) • q.1‖ + ‖σ' t‖ * ‖q.2‖ := by
              rw [mul_smul, norm_smul (-a), norm_smul (σ' t), Real.norm_eq_abs, abs_neg]
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hσ't (norm_nonneg _))
      calc _ ≤ ‖fderiv ℝ φ y‖ * ‖(-a * Real.exp (-a * t)) • q.1 + σ' t • q.2‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ _ := mul_le_mul (hM y) hv (norm_nonneg _) hM0
    · simp only [fderiv_of_notMem_tsupport ℝ hys, zero_apply, norm_zero]
      positivity
  · have ht0 : t ∈ Ioi (0 : ℝ) := hK (ball_subset_closedBall ht)
    have h1 : HasDerivAt (fun t => Real.exp (-a * t)) (-a * Real.exp (-a * t)) t :=
      (((hasDerivAt_id t).const_mul (-a)).exp).congr_deriv (by simp only [id, mul_one]; ring)
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt t
      ((h1.smul_const q.1).add ((hσd t ht0).smul_const q.2))

end Core


/-- Integrals against `gaussPush ρ₀ c σ` are expectations `E[ψ(c X + σ Z)]`. -/
theorem integral_gaussPush {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ)
    (ρ₀ : Measure (Fin d → ℝ)) (c σ : ℝ) :
    ∫ y, ψ y ∂(gaussPush ρ₀ c σ) = ∫ q, ψ (c • q.1 + σ • q.2) ∂(ρ₀.prod stdGauss) :=
  integral_map (by fun_prop : Measurable fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
    c • q.1 + σ • q.2).aemeasurable hψ.aestronglyMeasurable

/-- **Weak Fokker–Planck equation for Gaussian-represented curves (Verified).** Let `ρ₀` be a
probability measure and `ρ t` the law of `e^{-at} X + σ_t Z` (`X ∼ ρ₀ ⊥ Z ∼ N(0, I_d)`) for
`t ≥ 0`, where `σ` is continuous on `[0, ∞)`, differentiable on `(0, ∞)` with continuous
derivative `σ'`, nonzero on `(0, ∞)`, and `σ σ' + a σ² = D` on `(0, ∞)`. Then
`WeakFokkerPlanck ρ (fun _ x => -a • x) D`. At `t > 0` this is `hasDerivAt_integral_comp`;
at `t = 0` the right derivative is obtained from continuity of the derivative
(`hasDerivWithinAt_Ici_of_tendsto_deriv`). -/
theorem weakFokkerPlanck_of_gaussPush {ρ : ℝ → Measure (Fin d → ℝ)}
    {ρ₀ : Measure (Fin d → ℝ)} [IsProbabilityMeasure ρ₀] {a D : ℝ} {σ σ' : ℝ → ℝ}
    (hρ : ∀ t, 0 ≤ t → ρ t = gaussPush ρ₀ (Real.exp (-a * t)) (σ t))
    (hσc : ContinuousOn σ (Ici 0)) (hσd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt σ (σ' t) t)
    (hσ' : ContinuousOn σ' (Ioi 0)) (hσ0 : ∀ t ∈ Ioi (0 : ℝ), σ t ≠ 0)
    (hD : ∀ t ∈ Ioi (0 : ℝ), σ t * σ' t + a * σ t ^ 2 = D) :
    WeakFokkerPlanck ρ (fun _ x => -a • x) D := by
  intro φ hφ t ht
  obtain ⟨hφ2, hφc⟩ := hφ
  set G : ℝ → ℝ := fun t =>
    ∫ q, φ (Real.exp (-a * t) • q.1 + σ t • q.2) ∂(ρ₀.prod stdGauss) with hG
  set H : ℝ → ℝ := fun t =>
    ∫ q, ouGen a D φ (Real.exp (-a * t) • q.1 + σ t • q.2) ∂(ρ₀.prod stdGauss) with hH
  have hGd : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt G (H s) s := fun s hs => by
    have := hasDerivAt_integral_comp hφ2 hφc ρ₀ a hσd hσ' hσ0 hs
    rwa [hD s hs] at this
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-a * t)) (Ici 0) := by fun_prop
  obtain ⟨C, hC⟩ := hφ2.continuous.bounded_above_of_compact_support hφc
  obtain ⟨CH, hCH⟩ := (continuous_ouGen hφ2 a D).bounded_above_of_compact_support
    (hasCompactSupport_ouGen hφc a D)
  have hGc : ContinuousOn G (Ici 0) := continuousOn_integral_comp hφ2.continuous hC ρ₀ hc hσc
  have hHc : ContinuousOn H (Ici 0) :=
    continuousOn_integral_comp (continuous_ouGen hφ2 a D) hCH ρ₀ hc hσc
  have hGt : HasDerivWithinAt G (H t) (Ici 0) t := by
    rcases ht.lt_or_eq with ht' | rfl
    · exact (hGd t ht').hasDerivWithinAt
    · refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
        (fun s hs => (hGd s hs).differentiableAt.differentiableWithinAt)
        ((hGc 0 self_mem_Ici).mono Ioi_subset_Ici_self) self_mem_nhdsWithin ?_
      have h1 : Tendsto H (𝓝[>] 0) (𝓝 (H 0)) :=
        ((hHc 0 self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hGd s hs).deriv.symm
  have hint : ∀ s, 0 ≤ s → ∫ x, φ x ∂(ρ s) = G s := fun s hs => by
    rw [hρ s hs, integral_gaussPush hφ2.continuous]
  have hval : ∫ x, ((fun (_ : ℝ) (x : Fin d → ℝ) => -a • x) t x ⬝ᵥ grad φ x +
      D * laplacian φ x) ∂(ρ t) = H t := by
    rw [hρ t ht]
    exact integral_gaussPush (continuous_ouGen hφ2 a D) _ _ _
  rw [hval]
  exact hGt.congr (fun s hs => hint s hs) (hint t ht)

/-- For `t ≥ 0`, the heat flow `heatKernelPi t ∘ₘ ρ₀` is the law of `X + √t Z`. -/
theorem heatKernelPi_comp_eq_gaussPush (ρ₀ : Measure (Fin d → ℝ)) [SFinite ρ₀] {t : ℝ}
    (ht : 0 ≤ t) :
    heatKernelPi t.toNNReal ∘ₘ ρ₀ = gaussPush ρ₀ (Real.exp (-0 * t)) (Real.sqrt t) := by
  have h1 : scalePi (d := d) 1 = id := funext fun x => funext fun i => one_mul _
  rw [neg_zero, zero_mul, Real.exp_zero,
    show Real.sqrt t = Real.sqrt (t.toNNReal : ℝ) by rw [Real.coe_toNNReal _ ht],
    ← heatKernelPi_comp_map_scalePi, h1, Measure.map_id]

/-- **Weak Fokker–Planck equation of the heat flow (Verified, no Itô input).** For every
probability measure `ρ₀` on `Fin d → ℝ`, the heat-flow curve
`t ↦ heatKernelPi t.toNNReal ∘ₘ ρ₀` (variance `t` per coordinate, i.e. `X_t = X_0 + W_t`) solves
`WeakFokkerPlanck` with drift `0` and diffusion `D = 1/2`:
`d/dt ∫ φ dρ_t = ½ ∫ Δφ dρ_t` on `t ≥ 0` (derivative within `[0, ∞)`). -/
theorem weakFokkerPlanck_heat (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    WeakFokkerPlanck (fun t => heatKernelPi t.toNNReal ∘ₘ ρ₀) (fun _ _ => 0) (1 / 2) := by
  have h := weakFokkerPlanck_of_gaussPush (ρ := fun t => heatKernelPi t.toNNReal ∘ₘ ρ₀)
    (a := 0) (D := 1 / 2) (σ := Real.sqrt) (σ' := fun t => 1 / (2 * Real.sqrt t))
    (fun t ht => heatKernelPi_comp_eq_gaussPush ρ₀ ht) Real.continuous_sqrt.continuousOn
    (fun t ht => Real.hasDerivAt_sqrt (ne_of_gt ht)) ?_ (fun t ht => (Real.sqrt_pos.2 ht).ne') ?_
  · have e : (fun (_ : ℝ) (x : Fin d → ℝ) => -(0 : ℝ) • x) = fun _ _ => 0 := by
      funext t x; simp
    rwa [e] at h
  · refine continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
      fun t ht => ?_
    have := Real.sqrt_pos.2 (mem_Ioi.1 ht)
    positivity
  · intro t ht
    have := Real.sqrt_pos.2 (mem_Ioi.1 ht)
    field_simp
    ring

/-- For `v, a, t ≥ 0`, `ouKernelVarPi v a t ∘ₘ ρ₀` is the law of
`e^{-at} X + √(v (1 - e^{-2at})) Z`. -/
theorem ouKernelVarPi_comp_eq_gaussPush {v a : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a)
    (ρ₀ : Measure (Fin d → ℝ)) [SFinite ρ₀] {t : ℝ} (ht : 0 ≤ t) :
    ouKernelVarPi v a t ∘ₘ ρ₀ = gaussPush ρ₀ (Real.exp (-a * t))
      (Real.sqrt (v * (1 - Real.exp (-2 * a * t)))) := by
  have h : 0 ≤ v * (1 - Real.exp (-2 * a * t)) :=
    mul_nonneg hv (by rw [sub_nonneg]; exact Real.exp_le_one_iff.2 (by nlinarith))
  rw [ouKernelVarPi_comp_eq, heatKernelPi_comp_map_scalePi, Real.coe_toNNReal _ h]

/-- **Weak Fokker–Planck equation of the OU flow with stationary variance `v` (Verified, no Itô
input).** For `v > 0`, `a ≥ 0` and every probability measure `ρ₀` on `Fin d → ℝ`, the curve
`t ↦ ouKernelVarPi v a t ∘ₘ ρ₀` (the law of `dX = -a X dt + √(2 a v) dW`) solves
`WeakFokkerPlanck` with drift `b t x = -a • x` and diffusion `D = a v`. -/
theorem weakFokkerPlanck_ouVar {v a : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    WeakFokkerPlanck (fun t => ouKernelVarPi v a t ∘ₘ ρ₀) (fun _ x => -a • x) (a * v) := by
  rcases ha.lt_or_eq with ha | rfl
  swap
  · intro φ _ t ht
    have hc : ∀ s, ouKernelVarPi v 0 s ∘ₘ ρ₀ = ρ₀ := fun s =>
      ouKernelVarPi_comp_of_mul_eq_zero (zero_mul s) ρ₀
    simp only [hc, neg_zero, zero_smul, zero_dotProduct, zero_mul, add_zero, integral_zero]
    exact hasDerivWithinAt_const _ _ _
  set s : ℝ → ℝ := fun t => v * (1 - Real.exp (-2 * a * t)) with hsdef
  set s' : ℝ → ℝ := fun t => v * (2 * a * Real.exp (-2 * a * t)) with hs'def
  have hs : ∀ t, HasDerivAt s (s' t) t := fun t => by
    have := (((hasDerivAt_id t).const_mul (-2 * a)).exp.const_sub 1).const_mul v
    exact this.congr_deriv (by simp only [id, mul_one, hs'def]; ring)
  have hspos : ∀ t ∈ Ioi (0 : ℝ), 0 < s t := fun t ht =>
    mul_pos hv (by rw [sub_pos]; exact Real.exp_lt_one_iff.2 (by nlinarith [mem_Ioi.1 ht]))
  refine weakFokkerPlanck_of_gaussPush (σ := fun t => Real.sqrt (s t))
    (σ' := fun t => s' t / (2 * Real.sqrt (s t)))
    (fun t ht => ouKernelVarPi_comp_eq_gaussPush hv.le ha.le ρ₀ ht) ?_
    (fun t ht => (hs t).sqrt (hspos t ht).ne') ?_
    (fun t ht => (Real.sqrt_pos.2 (hspos t ht)).ne') ?_
  · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
  · refine ContinuousOn.div (by fun_prop)
      (continuousOn_const.mul (Real.continuous_sqrt.comp (by fun_prop)).continuousOn)
      fun t ht => ?_
    have := Real.sqrt_pos.2 (hspos t ht)
    positivity
  · intro t ht
    have h1 := Real.sqrt_pos.2 (hspos t ht)
    have h2 := Real.sq_sqrt (hspos t ht).le
    calc Real.sqrt (s t) * (s' t / (2 * Real.sqrt (s t))) + a * Real.sqrt (s t) ^ 2
        = s' t / 2 + a * s t := by rw [h2]; field_simp
      _ = a * v := by simp only [hsdef, hs'def]; ring

/-- **Weak Fokker–Planck equation of the OU flow (Verified, no Itô input).** For `a ≥ 0` and
every probability measure `ρ₀` on `Fin d → ℝ`, the curve `t ↦ ouKernelPi a t ∘ₘ ρ₀` (the law of
`dX = -a X dt + √(2a) dW`, target `N(0, I_d)`) solves `WeakFokkerPlanck` with drift
`b t x = -a • x` and diffusion `D = a`. This discharges the Itô input of FL-5 for these
dynamics. -/
theorem weakFokkerPlanck_ou {a : ℝ} (ha : 0 ≤ a) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    WeakFokkerPlanck (fun t => ouKernelPi a t ∘ₘ ρ₀) (fun _ x => -a • x) a := by
  have e : (fun t => ouKernelPi (d := d) a t ∘ₘ ρ₀) = fun t => ouKernelVarPi 1 a t ∘ₘ ρ₀ :=
    funext fun t => by rw [ouKernelPi_eq_ouKernelVarPi]
  have h := weakFokkerPlanck_ouVar one_pos ha ρ₀
  rwa [mul_one, ← e] at h

end FormalizeSampling.WeakFokkerPlanckOU
