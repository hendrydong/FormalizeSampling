module

public import FormalizeSampling.Foundations.BakryEmeryGeneralPi

/-!
# Bakry–Émery for separable strongly convex potentials on `Fin d → ℝ`

Status: **Verified** (no named hypothesis).

Notation: `gradSq`, `LSIClassPi`, `FunctionalLSIPi` are those of `Foundations/LogSobolevPi.lean`
(`FunctionalLSIPi μ C` is `Ent_μ(g²) ≤ 2 C ∫ ‖∇g‖² dμ` for every `g ∈ LSIClassPi`). For maps
`T i : ℝ → ℝ`, `piMap T x = (T i (x i))ᵢ` is the coordinatewise map; `sepPotential g x =
∑ᵢ gᵢ(xᵢ)` and `gaussPotentialPi α x = α |x|²/2` are from `Samplers/ProximalSharpPi.lean`.

## Main results

* `hasFDerivAt_piMap`, `gradSq_comp_piMap_le`: for differentiable `T i` with `|T i'| ≤ 1`,
  `‖∇(g ∘ piMap T)(x)‖² ≤ ‖∇g(piMap T x)‖²`.
* `lsiClassPi_comp_piMap`: `g ∈ LSIClassPi ⇒ g ∘ piMap T ∈ LSIClassPi`.
* `functionalLSIPi_map_piMap` (**coordinatewise contraction transports the LSI**): for a finite
  measure `μ` on `Fin d → ℝ` with `FunctionalLSIPi μ C` (`C ≥ 0`), and `T i` differentiable
  with `|T i'| ≤ 1`, `FunctionalLSIPi (μ.map (piMap T)) C`.
* `convexOn_sepPotential_sub_gaussPotentialPi`: if each `gᵢ - α x²/2` is convex on `ℝ`, then
  `sepPotential g - gaussPotentialPi α` is convex on `Fin d → ℝ`.
* `functionalLSIPi_targetPi_sepPotential` (**Bakry–Émery, separable case**): if `α > 0` and
  each `gᵢ - α x²/2` is convex on `ℝ`, then the target of `f(x) = ∑ᵢ gᵢ(xᵢ)` satisfies
  `FunctionalLSIPi (targetPi (sepPotential g)) (1 / α)`: the separable case of the general
  Bakry–Émery theorem `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`, through the
  previous convexity statement.

## Not proved here

* Coordinatewise maps that are only Lipschitz (not differentiable), and general (non-diagonal)
  maps of `Fin d → ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace FormalizeSampling.BakryEmeryPi

open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevPi
open FormalizeSampling.ProximalSharp FormalizeSampling.ProximalPi FormalizeSampling.ProximalSharpPi

variable {d : ℕ}

/-- The coordinatewise map `piMap T x = (T i (x i))ᵢ` on `Fin d → ℝ`. -/
def piMap (T : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => T i (x i)

/-- Derivative of the coordinatewise map: `D(piMap T)(x) v = (T i'(x i) v i)ᵢ`. -/
theorem hasFDerivAt_piMap {T : Fin d → ℝ → ℝ} (hT : ∀ i, Differentiable ℝ (T i))
    (x : Fin d → ℝ) :
    HasFDerivAt (piMap T) (ContinuousLinearMap.pi fun i =>
      deriv (T i) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
  refine hasFDerivAt_pi.2 fun i => ?_
  exact (hT i (x i)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply i x)

/-- The coordinatewise map of differentiable maps is differentiable. -/
theorem differentiable_piMap {T : Fin d → ℝ → ℝ} (hT : ∀ i, Differentiable ℝ (T i)) :
    Differentiable ℝ (piMap T) :=
  fun x => (hasFDerivAt_piMap hT x).differentiableAt

/-- Gradient bound for a composition with a coordinatewise contraction:
`‖∇(g ∘ piMap T)(x)‖² ≤ ‖∇g(piMap T x)‖²` when `|T i'| ≤ 1` and `g` is differentiable. -/
theorem gradSq_comp_piMap_le {T : Fin d → ℝ → ℝ} (hT : ∀ i, Differentiable ℝ (T i))
    (hK : ∀ i t, |deriv (T i) t| ≤ 1) {g : (Fin d → ℝ) → ℝ} (hg : Differentiable ℝ g)
    (x : Fin d → ℝ) : gradSq (fun y => g (piMap T y)) x ≤ gradSq g (piMap T x) := by
  unfold gradSq
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := (hg (piMap T x)).hasFDerivAt.comp x (hasFDerivAt_piMap hT x)
  have hv : (ContinuousLinearMap.pi fun i =>
      deriv (T i) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
      (Pi.single i 1) = deriv (T i) (x i) • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have : fderiv ℝ (fun y => g (piMap T y)) x (Pi.single i 1) =
      deriv (T i) (x i) * fderiv ℝ g (piMap T x) (Pi.single i 1) := by
    rw [show (fun y => g (piMap T y)) = g ∘ piMap T from rfl, hc.fderiv,
      ContinuousLinearMap.comp_apply, hv, map_smul, smul_eq_mul]
  rw [this, mul_pow]
  have h1 : deriv (T i) (x i) ^ 2 ≤ 1 := by
    have := hK i (x i)
    rw [← sq_abs]
    nlinarith [abs_nonneg (deriv (T i) (x i))]
  exact mul_le_of_le_one_left (sq_nonneg _) h1

/-- Composition with a coordinatewise contraction preserves the test class `LSIClassPi`. -/
theorem lsiClassPi_comp_piMap {T : Fin d → ℝ → ℝ} (hT : ∀ i, Differentiable ℝ (T i))
    (hK : ∀ i t, |deriv (T i) t| ≤ 1) {g : (Fin d → ℝ) → ℝ} (hg : LSIClassPi g) :
    LSIClassPi fun y => g (piMap T y) := by
  obtain ⟨hgd, ⟨M, hM⟩, ⟨K, hKg⟩, c, hc, hcg⟩ := hg
  exact ⟨hgd.comp (differentiable_piMap hT), ⟨M, fun x => hM _⟩,
    ⟨K, fun x => (gradSq_comp_piMap_le hT hK hgd x).trans (hKg _)⟩, c, hc, fun x => hcg _⟩

/-- **Coordinatewise contractions transport the LSI.** If `μ` is a finite measure on
`Fin d → ℝ` with `FunctionalLSIPi μ C` (`C ≥ 0`), and each `T i : ℝ → ℝ` is differentiable
with `|T i'| ≤ 1`, then `FunctionalLSIPi (μ.map (piMap T)) C`. -/
theorem functionalLSIPi_map_piMap {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ] {C : ℝ}
    (hμ : FunctionalLSIPi μ C) (hC : 0 ≤ C) {T : Fin d → ℝ → ℝ}
    (hT : ∀ i, Differentiable ℝ (T i)) (hK : ∀ i t, |deriv (T i) t| ≤ 1) :
    FunctionalLSIPi (μ.map (piMap T)) C := by
  intro g hg
  have hTm : Measurable (piMap T) := (differentiable_piMap hT).continuous.measurable
  have hgm : Measurable g := hg.1.continuous.measurable
  obtain ⟨K, hKg⟩ := hg.2.2.1
  have h := hμ _ (lsiClassPi_comp_piMap hT hK hg)
  rw [ent_map _ hTm (hgm.pow_const 2),
    integral_map hTm.aemeasurable (measurable_gradSq g).aestronglyMeasurable]
  have hint : Integrable (fun x => gradSq g (piMap T x)) μ :=
    integrable_of_abs_le ((measurable_gradSq g).comp hTm).aestronglyMeasurable K fun x => by
      rw [abs_of_nonneg (gradSq_nonneg _ _)]; exact hKg _
  have hmono : ∫ x, gradSq (fun y => g (piMap T y)) x ∂μ ≤ ∫ x, gradSq g (piMap T x) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun x => gradSq_nonneg _ _) hint
      (ae_of_all _ fun x => gradSq_comp_piMap_le hT hK hg.1 x)
  calc ent μ (fun x => g (piMap T x) ^ 2)
      ≤ 2 * C * ∫ x, gradSq (fun y => g (piMap T y)) x ∂μ := h
    _ ≤ 2 * C * ∫ x, gradSq g (piMap T x) ∂μ := mul_le_mul_of_nonneg_left hmono (by positivity)

/-- If each `gᵢ - gaussPotential α` is convex, so is `sepPotential g - gaussPotentialPi α`. -/
theorem convexOn_sepPotential_sub_gaussPotentialPi {α : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ConvexOn ℝ univ fun x => g i x - gaussPotential α x) :
    ConvexOn ℝ univ fun x => sepPotential g x - gaussPotentialPi (d := d) α x := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [gaussPotentialPi, sepPotential, ← Finset.sum_sub_distrib, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := (hg i).2 (mem_univ (x i)) (mem_univ (y i)) ha hb hab
  simpa only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] using this

/-- **Bakry–Émery for separable potentials.** If `α > 0` and each `gᵢ - α x²/2` is convex on
`ℝ`, then the target `π ∝ e^{-f}` of `f(x) = ∑ᵢ gᵢ(xᵢ)` on `Fin d → ℝ` satisfies the
functional log-Sobolev inequality with constant `1/α` (the separable case of
`BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`). -/
theorem functionalLSIPi_targetPi_sepPotential {α : ℝ} (hα : 0 < α) {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ConvexOn ℝ univ fun x => g i x - α / 2 * x ^ 2) :
    FunctionalLSIPi (targetPi (sepPotential g)) (1 / α) := by
  refine BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn hα
    (convexOn_sepPotential_sub_gaussPotentialPi fun i => ?_)
  convert hg i using 2 with x
  simp [gaussPotential]; ring

end FormalizeSampling.BakryEmeryPi
