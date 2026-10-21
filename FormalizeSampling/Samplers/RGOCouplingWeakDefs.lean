module

public import FormalizeSampling.Samplers.ShiftedCompositionPi
public import FormalizeSampling.Samplers.ProximalSharpPi

/-!
# Weak contractive couplings of a kernel: definitions

Shared definitions for the `1/k` rate of the proximal sampler for general log-concave targets
on `Fin d → ℝ`.

* `WeakTendsto μ ν`: convergence of integrals of bounded continuous functions.
* `HasWeakCoupling K`: for every pair of probability laws `μ, ν` on `(Fin d → ℝ)²` there are
  laws `μ', ν'` whose marginals are the images of those of `μ, ν` under `K`, with
  `KL(μ' ‖ ν') ≤ KL(μ ‖ ν)` and `∫ |x - y|² dμ' ≤ ∫ |x - y|² dμ`. This is all the
  shifted-composition argument uses; it is implied by a pathwise `1`-Lipschitz representation
  (`RGOCouplingPi.HasLipRep`) but does not require one.
* `SmoothConvexBdd g`: `g` convex, `C²`, with bounded gradient and bounded second derivative.

## Main results

* `sq_norm_sub_le_sqDist`: `‖x - y‖² ≤ |x - y|²` (sup norm against Euclidean distance).
* `integrable_exp_neg_mul_sqDist`: `x ↦ exp(-c |x - y|²)` is integrable for `c > 0`.
* `measurable_rgoDensityPi_of_continuous`, `rgoKernelPi_apply_of_continuous`,
  `integral_rgoKernelPi_of_continuous`: for a continuous potential the RGO kernel is the density
  kernel of `rgoDensityPi` (no integrability assumption on `e^{-h}`).

## Not proved here

Everything else about these definitions: see `Samplers/RGOCouplingWeak.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.ReverseKernel
open FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcaveRatePi
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingWeak

variable {d : ℕ}

/-- Weak convergence, stated through integrals: `∫ f dμₙ → ∫ f dν` for every bounded
continuous `f`. -/
def WeakTendsto {α : Type*} [MeasurableSpace α] [TopologicalSpace α] (μ : ℕ → Measure α)
    (ν : Measure α) : Prop :=
  ∀ f : α → ℝ, Continuous f → ∀ N : ℝ, (∀ x, |f x| ≤ N) →
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

/-- **Weak contractive coupling of a kernel.** For all probability laws `μ, ν` on pairs there
are probability laws `μ', ν'` with all four marginals pushed through `K`, KL not increased and
the squared-distance cost of `μ` not increased. -/
def HasWeakCoupling (K : Kernel (Fin d → ℝ) (Fin d → ℝ)) : Prop :=
  ∀ μ ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∃ μ' ν' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ' ∧
      IsProbabilityMeasure ν' ∧
      μ'.map Prod.fst = K ∘ₘ μ.map Prod.fst ∧ μ'.map Prod.snd = K ∘ₘ μ.map Prod.snd ∧
      ν'.map Prod.fst = K ∘ₘ ν.map Prod.fst ∧ ν'.map Prod.snd = K ∘ₘ ν.map Prod.snd ∧
      klDiv μ' ν' ≤ klDiv μ ν ∧ sqCostPi μ' ≤ sqCostPi μ

/-- **Smooth convex potentials with bounded derivatives.** `g` is convex on `Fin d → ℝ`, `C²`,
and has bounded first and second derivatives. -/
def SmoothConvexBdd (g : (Fin d → ℝ) → ℝ) : Prop :=
  ConvexOn ℝ univ g ∧ ContDiff ℝ 2 g ∧ (∃ B : ℝ, ∀ x, ‖fderiv ℝ g x‖ ≤ B) ∧
    ∃ L : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ L

/-! ### The RGO kernel of a continuous potential -/

/-- The sup norm is dominated by the Euclidean norm: `‖x - y‖² ≤ |x - y|² = sqDist x y`. -/
theorem sq_norm_sub_le_sqDist (x y : Fin d → ℝ) : ‖x - y‖ ^ 2 ≤ sqDist x y := by
  have h : ‖x - y‖ ≤ Real.sqrt (sqDist x y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => (x i - y i) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖x - y‖ ^ 2 ≤ Real.sqrt (sqDist x y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sqDist x y := Real.sq_sqrt (sqDist_nonneg x y)

/-- **Gaussian integrability on `Fin d → ℝ`.** For `c > 0`, `x ↦ exp(-c |x - y|²)` is
Lebesgue integrable. -/
theorem integrable_exp_neg_mul_sqDist {c : ℝ} (hc : 0 < c) (y : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-(c * sqDist x y))) := by
  have h1 : ∀ i : Fin d, Integrable (fun t : ℝ => Real.exp (-c * (t - y i) ^ 2)) :=
    fun i => (integrable_exp_neg_mul_sq hc).comp_sub_right (y i)
  have h2 := Integrable.fintype_prod (f := fun i t => Real.exp (-c * (t - y i) ^ 2))
    (μ := fun _ => (volume : Measure ℝ)) h1
  rw [← volume_pi] at h2
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp only [sqDist]
  rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

section Continuous

variable {h : (Fin d → ℝ) → ℝ} {η : ℝ}

/-- For continuous `h`, the RGO density is jointly measurable in `(y, x)` (no integrability
assumption: the normaliser is a parametric integral of a continuous function). -/
theorem measurable_rgoDensityPi_of_continuous (hh : Continuous h) :
    Measurable (Function.uncurry fun y x => ENNReal.ofReal (rgoDensityPi h η y x)) := by
  have hF : Continuous (Function.uncurry fun (y x : Fin d → ℝ) =>
      Real.exp (-h x - sqDist x y / (2 * η))) := by
    have : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) => sqDist p.2 p.1 :=
      continuous_sqDist.comp continuous_swap
    change Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      Real.exp (-h p.2 - sqDist p.2 p.1 / (2 * η))
    fun_prop
  have hZ : Measurable fun y : Fin d → ℝ => rgoNormalizerPi h η y :=
    (hF.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  have : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      Real.exp (-h p.2 - sqDist p.2 p.1 / (2 * η)) / rgoNormalizerPi h η p.1 :=
    hF.measurable.div (hZ.comp measurable_fst)
  exact this.ennreal_ofReal

/-- For continuous `h`, `rgoKernelPi h η y = volume.withDensity (ofReal ∘ rgoDensityPi h η y)`
(no integrability assumption). -/
theorem rgoKernelPi_apply_of_continuous (hh : Continuous h) (y : Fin d → ℝ) :
    rgoKernelPi h η y = volume.withDensity (fun x => ENNReal.ofReal (rgoDensityPi h η y x)) :=
  densityKernel_apply (measurable_rgoDensityPi_of_continuous hh) y

/-- **Integrals against the RGO kernel** (continuous `h`, any integrand `φ`):
`∫ φ d(rgoKernelPi h η y) = (∫ φ(x) exp(-h x - |x - y|²/(2η)) dx) / Z_η(y)`. -/
theorem integral_rgoKernelPi_of_continuous (hh : Continuous h) (y : Fin d → ℝ)
    (φ : (Fin d → ℝ) → ℝ) :
    ∫ x, φ x ∂(rgoKernelPi h η y) =
      (∫ x, φ x * Real.exp (-h x - sqDist x y / (2 * η))) / rgoNormalizerPi h η y := by
  rw [rgoKernelPi_apply_of_continuous hh, integral_withDensity_eq_integral_toReal_smul
    (measurable_rgoDensityPi_of_continuous hh).of_uncurry_left
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (rgoDensityPi_nonneg y x), smul_eq_mul, rgoDensityPi]
  ring

end Continuous

end FormalizeSampling.RGOCouplingWeak
