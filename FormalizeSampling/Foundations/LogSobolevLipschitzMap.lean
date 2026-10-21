module

public import FormalizeSampling.Foundations.LogSobolev

/-!
# Functional log-Sobolev inequalities under Lipschitz push-forward (1D)

Status: **Verified** (no named hypothesis: the only inputs are the functional LSI of the
source measure and a pointwise bound on the derivative of the map).

Notation: `ent`, `LSIClass`, `FunctionalLSI` are those of `Foundations/LogSobolev.lean`
(`FunctionalLSI μ C` is `Ent_μ(g²) ≤ 2 C ∫ (g')² dμ` for every `g ∈ LSIClass`).

## Main results

* `lsiClass_comp`: if `g ∈ LSIClass` and `T : ℝ → ℝ` is differentiable with `|T'| ≤ K`, then
  `g ∘ T ∈ LSIClass` (boundedness, the positive lower bound and the derivative bound
  `|(g ∘ T)'| ≤ K sup |g'|` survive composition).
* `functionalLSI_map_of_abs_deriv_le` (**Lipschitz transport of the LSI**): for a finite
  measure `μ` on `ℝ` with `FunctionalLSI μ C` (`C ≥ 0`) and `T` differentiable with
  `|T'(x)| ≤ K` for all `x`, the push-forward `T#μ` satisfies `FunctionalLSI (T#μ) (K² C)`.
  Proof: apply the LSI of `μ` to `g ∘ T`, use `Ent_{T#μ}(g²) = Ent_μ((g ∘ T)²)` and
  `((g ∘ T)')² = (g' ∘ T)² (T')² ≤ K² (g' ∘ T)²`.

## Not proved here

* Maps that are only Lipschitz (not everywhere differentiable), or Lipschitz only
  `μ`-almost everywhere; the derivative bound is assumed at every point.
* Multi-dimensional Lipschitz maps in general (the coordinatewise case is
  `BakryEmeryPi.functionalLSIPi_map_piMap`).
-/

public section

open MeasureTheory Set

namespace FormalizeSampling.LogSobolevLipschitzMap

open FormalizeSampling.LogSobolev

/-- Chain rule: `(g ∘ T)'(x) = g'(T x) T'(x)` for `g ∈ LSIClass` and differentiable `T`. -/
theorem deriv_comp_apply {g T : ℝ → ℝ} (hg : LSIClass g) (hT : Differentiable ℝ T) (x : ℝ) :
    deriv (fun x => g (T x)) x = deriv g (T x) * deriv T x :=
  ((hg.differentiable (T x)).hasDerivAt.comp x (hT x).hasDerivAt).deriv

/-- **Composition preserves the LSI test class.** If `g ∈ LSIClass` and `T : ℝ → ℝ` is
differentiable with `|T'(x)| ≤ K` for all `x`, then `g ∘ T ∈ LSIClass`. -/
theorem lsiClass_comp {g T : ℝ → ℝ} (hg : LSIClass g) (hT : Differentiable ℝ T) {K : ℝ}
    (hK : ∀ x, |deriv T x| ≤ K) : LSIClass (fun x => g (T x)) := by
  obtain ⟨M₀, hM₀⟩ := hg.bounded
  obtain ⟨M₁, hM₁⟩ := hg.bounded_deriv
  obtain ⟨c, hc, hcg⟩ := hg.pos
  refine ⟨hg.differentiable.comp hT, ⟨M₀, fun x => hM₀ _⟩, ⟨M₁ * K, fun x => ?_⟩,
    ⟨c, hc, fun x => hcg _⟩⟩
  rw [deriv_comp_apply hg hT x, abs_mul]
  exact mul_le_mul (hM₁ _) (hK x) (abs_nonneg _) ((abs_nonneg _).trans (hM₁ 0))

/-- **Lipschitz transport of the functional LSI.** If `μ` is a finite measure on `ℝ` with
`FunctionalLSI μ C`, `C ≥ 0`, and `T : ℝ → ℝ` is differentiable with `|T'(x)| ≤ K` for every
`x`, then the push-forward `T#μ = μ.map T` satisfies `FunctionalLSI (μ.map T) (K² C)`. -/
theorem functionalLSI_map_of_abs_deriv_le {μ : Measure ℝ} [IsFiniteMeasure μ] {C : ℝ}
    (hμ : FunctionalLSI μ C) (hC : 0 ≤ C) {T : ℝ → ℝ} (hT : Differentiable ℝ T) {K : ℝ}
    (hK : ∀ x, |deriv T x| ≤ K) : FunctionalLSI (μ.map T) (K ^ 2 * C) := by
  intro g hg
  have hTm : Measurable T := hT.continuous.measurable
  have hgm : Measurable g := hg.differentiable.continuous.measurable
  obtain ⟨M₁, hM₁⟩ := hg.bounded_deriv
  have h := hμ _ (lsiClass_comp hg hT hK)
  rw [ent_map _ hTm (hgm.pow_const 2),
    integral_map hTm.aemeasurable ((measurable_deriv g).pow_const 2).aestronglyMeasurable]
  have hpt : ∀ x, deriv (fun x => g (T x)) x ^ 2 ≤ K ^ 2 * deriv g (T x) ^ 2 := by
    intro x
    rw [deriv_comp_apply hg hT x, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.1 (hK x)).1 (abs_le.1 (hK x)).2)
      (sq_nonneg _)
  have hint : Integrable (fun x => K ^ 2 * deriv g (T x) ^ 2) μ := by
    refine (integrable_of_abs_le (((measurable_deriv g).comp hTm).pow_const 2
      ).aestronglyMeasurable (M₁ ^ 2) fun x => ?_).const_mul _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.1 (hM₁ _)).1 (abs_le.1 (hM₁ _)).2
  have hmono : ∫ x, deriv (fun x => g (T x)) x ^ 2 ∂μ ≤
      ∫ x, K ^ 2 * deriv g (T x) ^ 2 ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hint (ae_of_all _ hpt)
  rw [integral_const_mul] at hmono
  calc ent μ (fun x => g (T x) ^ 2)
      ≤ 2 * C * ∫ x, deriv (fun x => g (T x)) x ^ 2 ∂μ := h
    _ ≤ 2 * C * (K ^ 2 * ∫ x, deriv g (T x) ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 2 * (K ^ 2 * C) * ∫ x, deriv g (T x) ^ 2 ∂μ := by ring

end FormalizeSampling.LogSobolevLipschitzMap
