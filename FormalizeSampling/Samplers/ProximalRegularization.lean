module

public import FormalizeSampling.Samplers.ProximalContraction
public import FormalizeSampling.Samplers.ProximalPi

/-!
# Regularisation of the exact proximal sampler: KL after one step is bounded by a transport cost

Status: **Verified** (no named hypotheses).

Setting: the exact proximal sampler of `Samplers/Proximal.lean` (on `ℝ`) and
`Samplers/ProximalPi.lean` (on `Fin d → ℝ`), step `η > 0` (the **variance** of the forward
Gaussian), target `π = target f` (resp. `targetPi f`). A *coupling* of two laws `ρ, π` is
expressed without a Wasserstein-space library as a finite measure `γ` on the product whose
marginals `γ.map Prod.fst`, `γ.map Prod.snd` are `ρ` and `π`.

## Main results

* `klDiv_forwardKernel_comp_map_le` (**any** finite `γ` on `ℝ × ℝ`, no assumption on a target):
  `KL(N_η ∘ₘ γ₁ ‖ N_η ∘ₘ γ₂) ≤ ∫⁻ (x - y)² / (2η) dγ`, with `γ₁, γ₂` the marginals of `γ`.
  Proof: `N_η ∘ₘ γᵢ = (N_η ∘ prᵢ) ∘ₘ γ`, data processing for the second marginal of
  `γ ⊗ₘ (N_η ∘ prᵢ)` and the chain rule `KL(γ ⊗ₘ κ ‖ γ ⊗ₘ κ') = ∫⁻ KL(κ p ‖ κ' p) dγ(p)`
  (`Foundations/KLChainRule.lean`), together with the Gaussian identity
  `KL(N(x, η) ‖ N(y, η)) = (x - y)² / (2η)`. This is the joint convexity of KL in the form
  needed here.
* `klDiv_forwardKernel_comp_le_coupling`: the same bound written for a coupling of `(ρ, π)`.
* `klDiv_proxKernel_comp_le_coupling` (**regularisation**, any measurable `f` with integrable
  `exp ∘ (-f)`, no convexity): for every coupling `γ` of `(ρ, π)`,
  `KL(proxKernel f η ∘ₘ ρ ‖ π) ≤ ∫⁻ (x - y)² / (2η) dγ`; the RGO step is KL non-expansive
  toward `π` (`ProximalContraction.klDiv_proxKernel_comp_le_forward`).
* `d`-dimensional versions `klDiv_forwardKernelPi_comp_map_le`,
  `klDiv_forwardKernelPi_comp_le_coupling`, `klDiv_proxKernelPi_comp_le_coupling`, with
  `(x - y)²` replaced by the squared Euclidean distance `sqDist x y = ∑ᵢ (xᵢ - yᵢ)²`.

All bounds are in `ℝ≥0∞` and hold trivially when the right-hand side is `∞`.

## Not proved here

* Any statement about Wasserstein distances as such (infima over couplings); the bounds hold
  for each coupling and the infimum is left to the reader.
* Convergence of the iterates (see `Samplers/ProximalLogConcave.lean` for the log-concave
  case).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open FormalizeSampling.Proximal FormalizeSampling.ProximalPi
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalRegularization

/-! ### Composition with a marginal -/

/-- Composing a kernel with a marginal of a measure on a product is composing the pulled-back
kernel with the measure: `κ ∘ₘ (γ.map g) = (κ.comap g) ∘ₘ γ` for measurable `g`. -/
theorem comp_map_eq_comap_comp {α β γ' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ'] (κ : Kernel α β) (μ : Measure γ') {g : γ' → α} (hg : Measurable g) :
    κ ∘ₘ μ.map g = (κ.comap g hg) ∘ₘ μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hs) hg]
  rfl

/-- **Joint convexity of KL for coupled kernels.** For a finite measure `γ` on `α × α`
(`α` countably generated or countable) and a Markov kernel `κ : Kernel α β`:
`KL(κ ∘ₘ γ₁ ‖ κ ∘ₘ γ₂) ≤ ∫⁻ KL(κ p.1 ‖ κ p.2) dγ(p)`, with `γᵢ` the marginals of `γ`. -/
theorem klDiv_comp_map_le_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated (α × α) β]
    (γ : Measure (α × α)) [IsFiniteMeasure γ] (κ : Kernel α β) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ γ.map Prod.fst) (κ ∘ₘ γ.map Prod.snd) ≤ ∫⁻ p, klDiv (κ p.1) (κ p.2) ∂γ := by
  rw [comp_map_eq_comap_comp κ γ measurable_fst, comp_map_eq_comap_comp κ γ measurable_snd]
  refine (KL.klDiv_comp_le_compProd γ γ _ _).trans_eq ?_
  rw [KL.klDiv_compProd_right_eq_lintegral]
  rfl

/-! ### One dimension -/

/-- **Gaussian KL for the forward kernel.** For `η > 0`:
`KL(N(x, η) ‖ N(y, η)) = (x - y)² / (2η)`. -/
theorem klDiv_forwardKernel_apply {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    klDiv (forwardKernel η x) (forwardKernel η y) = ENNReal.ofReal ((x - y) ^ 2 / (2 * η)) := by
  rw [forwardKernel_apply hη, forwardKernel_apply hη,
    GaussianIncrement.klDiv_gaussianReal_gaussianReal _ _ (by simpa using hη),
    Real.coe_toNNReal _ hη.le]

/-- **Forward-step regularisation (any finite `γ` on `ℝ × ℝ`).** For `η > 0`:
`KL(N_η ∘ₘ γ₁ ‖ N_η ∘ₘ γ₂) ≤ ∫⁻ (x - y)² / (2η) dγ(x, y)`, with `γ₁, γ₂` the marginals. -/
theorem klDiv_forwardKernel_comp_map_le {η : ℝ} (hη : 0 < η) (γ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ] :
    klDiv (forwardKernel η ∘ₘ γ.map Prod.fst) (forwardKernel η ∘ₘ γ.map Prod.snd)
      ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / (2 * η)) ∂γ := by
  have := isMarkovKernel_forwardKernel hη
  refine (klDiv_comp_map_le_lintegral γ (forwardKernel η)).trans_eq ?_
  simp_rw [klDiv_forwardKernel_apply hη]

/-- **Forward-step regularisation for a coupling.** For `η > 0` and a finite measure `γ` on
`ℝ × ℝ` with marginals `ρ` and `μ`:
`KL(N_η ∘ₘ ρ ‖ N_η ∘ₘ μ) ≤ ∫⁻ (x - y)² / (2η) dγ(x, y)`. -/
theorem klDiv_forwardKernel_comp_le_coupling {η : ℝ} (hη : 0 < η) {ρ μ : Measure ℝ}
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ)
    (h₂ : γ.map Prod.snd = μ) :
    klDiv (forwardKernel η ∘ₘ ρ) (forwardKernel η ∘ₘ μ)
      ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / (2 * η)) ∂γ := by
  subst h₁ h₂
  exact klDiv_forwardKernel_comp_map_le hη γ

/-- **Regularisation of the proximal step (any target).** Let `f` be measurable with
integrable `exp ∘ (-f)`, `π = target f`, `η > 0`, and let `γ` be a finite measure on `ℝ × ℝ`
with marginals `ρ` and `π` (a coupling). Then
`KL(proxKernel f η ∘ₘ ρ ‖ π) ≤ ∫⁻ (x - y)² / (2η) dγ(x, y)`. No convexity is needed. -/
theorem klDiv_proxKernel_comp_le_coupling {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) {ρ : Measure ℝ}
    [IsFiniteMeasure ρ] (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ)
    (h₂ : γ.map Prod.snd = target f) :
    klDiv (proxKernel f η ∘ₘ ρ) (target f)
      ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / (2 * η)) ∂γ :=
  (ProximalContraction.klDiv_proxKernel_comp_le_forward hf hint hη ρ).trans
    (klDiv_forwardKernel_comp_le_coupling hη γ h₁ h₂)

/-! ### Dimension `d` -/

variable {d : ℕ}

/-- **Gaussian KL for the `d`-dimensional forward kernel.** For `η > 0`:
`KL(N(x, η I) ‖ N(y, η I)) = |x - y|² / (2η)`. -/
theorem klDiv_forwardKernelPi_apply {η : ℝ} (hη : 0 < η) (x y : Fin d → ℝ) :
    klDiv (forwardKernelPi η x) (forwardKernelPi η y)
      = ENNReal.ofReal (sqDist x y / (2 * η)) := by
  rw [forwardKernelPi_apply, forwardKernelPi_apply,
    GaussianIncrement.klDiv_pi_gaussianReal _ _ (by simpa using hη),
    Real.coe_toNNReal _ hη.le]
  rfl

/-- **Forward-step regularisation in dimension `d` (any finite `γ`).** For `η > 0`:
`KL(N_η ∘ₘ γ₁ ‖ N_η ∘ₘ γ₂) ≤ ∫⁻ |x - y|² / (2η) dγ(x, y)`, with `γ₁, γ₂` the marginals. -/
theorem klDiv_forwardKernelPi_comp_map_le {η : ℝ} (hη : 0 < η)
    (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ] :
    klDiv (forwardKernelPi η ∘ₘ γ.map Prod.fst) (forwardKernelPi η ∘ₘ γ.map Prod.snd)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * η)) ∂γ := by
  refine (klDiv_comp_map_le_lintegral γ (forwardKernelPi η)).trans_eq ?_
  simp_rw [klDiv_forwardKernelPi_apply hη]

/-- **Forward-step regularisation for a coupling, dimension `d`.** For `η > 0` and a finite
measure `γ` with marginals `ρ` and `μ`:
`KL(N_η ∘ₘ ρ ‖ N_η ∘ₘ μ) ≤ ∫⁻ |x - y|² / (2η) dγ(x, y)`. -/
theorem klDiv_forwardKernelPi_comp_le_coupling {η : ℝ} (hη : 0 < η)
    {ρ μ : Measure (Fin d → ℝ)} (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ]
    (h₁ : γ.map Prod.fst = ρ) (h₂ : γ.map Prod.snd = μ) :
    klDiv (forwardKernelPi η ∘ₘ ρ) (forwardKernelPi η ∘ₘ μ)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * η)) ∂γ := by
  subst h₁ h₂
  exact klDiv_forwardKernelPi_comp_map_le hη γ

/-- **Regularisation of the proximal step in dimension `d` (any target).** Let `f` be
measurable with integrable `exp ∘ (-f)`, `π = targetPi f`, `η > 0`, and `γ` a coupling of
`(ρ, π)`. Then `KL(proxKernelPi f η ∘ₘ ρ ‖ π) ≤ ∫⁻ |x - y|² / (2η) dγ(x, y)`. -/
theorem klDiv_proxKernelPi_comp_le_coupling {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η)
    {ρ : Measure (Fin d → ℝ)} [IsFiniteMeasure ρ] (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ) (h₂ : γ.map Prod.snd = targetPi f) :
    klDiv (proxKernelPi f η ∘ₘ ρ) (targetPi f)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * η)) ∂γ :=
  (klDiv_proxKernelPi_comp_le_forward hf hint hη ρ).trans
    (klDiv_forwardKernelPi_comp_le_coupling hη γ h₁ h₂)

end FormalizeSampling.ProximalRegularization
