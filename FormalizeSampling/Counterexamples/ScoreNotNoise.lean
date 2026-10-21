module

public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# The noise is not the score (CE-02)

Let `X ~ N(0,1)` and `Z ~ N(0,1)` be independent, `σ > 0`, and `Y = X + σ Z`. Then
`Y ~ N(0, 1 + σ ^ 2)` and the (state) score of `Law(Y)` is `y ↦ -y / (1 + σ ^ 2)`.
Denoising score matching regresses onto the *noise target* `-Z / σ`; Tweedie's formula says
`E[-Z / σ | Y] = score(Y)`. The equality holds only **after conditioning on `Y`**, not in
law and not almost surely: `-Z / σ ~ N(0, 1 / σ ^ 2)` whereas
`score(Y) = -Y / (1 + σ ^ 2) ~ N(0, 1 / (1 + σ ^ 2))`, and these laws differ.

## Conventions

* `gaussianReal m v` has **variance** `v : ℝ≥0`; `gaussianPDFReal m v` is its Lebesgue
  density. The one-dimensional state score is `FormalizeSampling.score1 p y = (log p)'(y)`.
* Random variables live on a probability space `(Ω, P)`; laws are image measures `P.map`.

## Registry IDs

* `CE-02`: `law_noisy`, `law_noisy_eq_withDensity`,
  `score1_law_noisy`, `law_noiseTarget`, `law_scoreOfNoisy`, `noiseTarget_law_ne_scoreLaw`,
  `law_noiseTarget_ne_law_scoreOfNoisy`, `not_noiseTarget_ae_eq_scoreOfNoisy`.

## Not proved here

* Tweedie's formula `E[-Z / σ | Y] = score(Y)` itself (a conditional-expectation identity) is
  **not** formalised; it is only quoted in docstrings as the correct, conditional statement.
* Only the Gaussian-data case is treated.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.Counterexamples.ScoreNotNoise

open FormalizeSampling.MeasureHelpers (aemeasurable_of_map_eq_gaussianReal
  map_const_mul_of_aemeasurable)

/-- **Law of the noisy observation.** On a probability space, if `X ~ N(0,1)` and
`Z ~ N(0,1)` are independent, then `Y = X + σ Z ~ N(0, 1 + σ ^ 2)` for every real `σ`. -/
theorem law_noisy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Z : Ω → ℝ}
    (hXZ : IndepFun X Z P) (hX : P.map X = gaussianReal 0 1) (hZ : P.map Z = gaussianReal 0 1)
    (σ : ℝ) :
    P.map (fun ω => X ω + σ * Z ω) = gaussianReal 0 ⟨1 + σ ^ 2, by positivity⟩ := by
  show _ = gaussianReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity))
  have hZm : AEMeasurable Z P := aemeasurable_of_map_eq_gaussianReal one_ne_zero hZ
  have hind : IndepFun X (fun ω => σ * Z ω) P :=
    hXZ.comp (φ := id) (ψ := fun z => σ * z) measurable_id (measurable_const_mul σ)
  have hσZ : P.map (fun ω => σ * Z ω) = gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ)) := by
    rw [map_const_mul_of_aemeasurable hZm, hZ, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  have := gaussianReal_add_gaussianReal_of_indepFun hind
    ⟨aemeasurable_of_map_eq_gaussianReal one_ne_zero hX, hX⟩ ⟨hZm.const_mul σ, hσZ⟩
  rw [show (fun ω => X ω + σ * Z ω) = X + fun ω => σ * Z ω from rfl, this]
  congr 1
  simp

/-- The law `N(0, 1 + σ ^ 2)` of `Y = X + σ Z` has Lebesgue density
`gaussianPDFReal 0 (1 + σ ^ 2)`: `Law(Y) = volume.withDensity (ofReal ∘ gaussianPDFReal …)`.
So `score1 (gaussianPDFReal 0 (1 + σ ^ 2))` is the score of `Law(Y)`. -/
theorem law_noisy_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Z : Ω → ℝ} (hXZ : IndepFun X Z P) (hX : P.map X = gaussianReal 0 1)
    (hZ : P.map Z = gaussianReal 0 1) (σ : ℝ) :
    P.map (fun ω => X ω + σ * Z ω) = volume.withDensity
      (fun y => ENNReal.ofReal (gaussianPDFReal 0 ⟨1 + σ ^ 2, by positivity⟩ y)) := by
  show _ = volume.withDensity
    (fun y => ENNReal.ofReal (gaussianPDFReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity)) y))
  have hY : P.map (fun ω => X ω + σ * Z ω) =
      gaussianReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity)) := law_noisy hXZ hX hZ σ
  rw [hY, gaussianReal_of_var_ne_zero]
  · rfl
  · intro h
    have := congrArg (fun w : ℝ≥0 => (w : ℝ)) h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at this
    nlinarith [sq_nonneg σ]

/-- **Score of the noisy law.** The state score of the density of `N(0, 1 + σ ^ 2)` is
`y ↦ -y / (1 + σ ^ 2)`. -/
theorem score1_law_noisy (σ y : ℝ) :
    score1 (gaussianPDFReal 0 ⟨1 + σ ^ 2, by positivity⟩) y = -y / (1 + σ ^ 2) := by
  show score1 (gaussianPDFReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity))) y = _
  have hv : NNReal.mk (1 + σ ^ 2) (by positivity) ≠ 0 := by
    intro h
    have := congrArg (fun w : ℝ≥0 => (w : ℝ)) h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at this
    nlinarith [sq_nonneg σ]
  rw [score1_gaussianPDFReal 0 hv y]
  simp

/-- **Law of the noise target.** If `Z ~ N(0,1)` and `σ ≠ 0`, then
`-Z / σ ~ N(0, 1 / σ ^ 2)`. -/
theorem law_noiseTarget {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : P.map Z = gaussianReal 0 1) {σ : ℝ} (hσ : σ ≠ 0) :
    P.map (fun ω => -Z ω / σ) = gaussianReal 0 ⟨1 / σ ^ 2, by positivity⟩ := by
  show _ = gaussianReal 0 (NNReal.mk (1 / σ ^ 2) (by positivity))
  have hZm : AEMeasurable Z P := aemeasurable_of_map_eq_gaussianReal one_ne_zero hZ
  have hf : (fun ω => -Z ω / σ) = (fun z => (-σ⁻¹) * z) ∘ Z := by
    funext ω
    simp [div_eq_mul_inv, mul_comm]
  rw [hf, ← AEMeasurable.map_map_of_aemeasurable (measurable_const_mul _).aemeasurable hZm, hZ,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp

/-- **Law of the score of the noisy observation.** If `X ~ N(0,1)` and `Z ~ N(0,1)` are
independent and `Y = X + σ Z`, then
`score(Y) = score1 (gaussianPDFReal 0 (1 + σ ^ 2)) Y = -Y / (1 + σ ^ 2) ~ N(0, 1 / (1 + σ ^ 2))`.
-/
theorem law_scoreOfNoisy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Z : Ω → ℝ}
    (hXZ : IndepFun X Z P) (hX : P.map X = gaussianReal 0 1) (hZ : P.map Z = gaussianReal 0 1)
    (σ : ℝ) :
    P.map (fun ω => score1 (gaussianPDFReal 0 ⟨1 + σ ^ 2, by positivity⟩) (X ω + σ * Z ω)) =
      gaussianReal 0 ⟨1 / (1 + σ ^ 2), by positivity⟩ := by
  show P.map (fun ω => score1 (gaussianPDFReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity)))
    (X ω + σ * Z ω)) = gaussianReal 0 (NNReal.mk (1 / (1 + σ ^ 2)) (by positivity))
  have hY : P.map (fun ω => X ω + σ * Z ω) =
      gaussianReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity)) := law_noisy hXZ hX hZ σ
  have hYm : AEMeasurable (fun ω => X ω + σ * Z ω) P :=
    (aemeasurable_of_map_eq_gaussianReal one_ne_zero hX).add
      ((aemeasurable_of_map_eq_gaussianReal one_ne_zero hZ).const_mul σ)
  have hpos : (0 : ℝ) < 1 + σ ^ 2 := by positivity
  have hf : (fun ω => score1 (gaussianPDFReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity)))
      (X ω + σ * Z ω)) =
      (fun y => (-(1 + σ ^ 2)⁻¹) * y) ∘ (fun ω => X ω + σ * Z ω) := by
    funext ω
    have hs : score1 (gaussianPDFReal 0 (NNReal.mk (1 + σ ^ 2) (by positivity)))
        (X ω + σ * Z ω) = -(X ω + σ * Z ω) / (1 + σ ^ 2) := score1_law_noisy σ _
    simp only [Function.comp_apply, hs]
    rw [div_eq_mul_inv]
    ring
  rw [hf, ← AEMeasurable.map_map_of_aemeasurable (measurable_const_mul _).aemeasurable hYm, hY,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    field_simp

/-- **The two variances differ.** For `σ ≠ 0`, the laws `N(0, 1 / σ ^ 2)` (noise target) and
`N(0, 1 / (1 + σ ^ 2))` (score of the noisy observation) are different measures. -/
theorem noiseTarget_law_ne_scoreLaw {σ : ℝ} (hσ : σ ≠ 0) :
    gaussianReal 0 ⟨1 / σ ^ 2, by positivity⟩ ≠
      gaussianReal 0 ⟨1 / (1 + σ ^ 2), by positivity⟩ := by
  show gaussianReal 0 (NNReal.mk (1 / σ ^ 2) (by positivity)) ≠
    gaussianReal 0 (NNReal.mk (1 / (1 + σ ^ 2)) (by positivity))
  intro h
  have h1 := variance_id_gaussianReal (μ := 0) (v := NNReal.mk (1 / σ ^ 2) (by positivity))
  rw [h, variance_id_gaussianReal] at h1
  simp only [NNReal.coe_mk] at h1
  have hσ2 : 0 < σ ^ 2 := by positivity
  rw [div_eq_div_iff (by positivity) hσ2.ne'] at h1
  linarith

/-- **CE-02: the noise target and the score are not equal in law.** On a probability space, let
`X ~ N(0,1)` and `Z ~ N(0,1)` be independent, `σ > 0` and `Y = X + σ Z`. Then the law of the
denoising target `-Z / σ` differs from the law of `score(Y) = -Y / (1 + σ ^ 2)`. (Tweedie's
formula `E[-Z / σ | Y] = score(Y)` only identifies them after conditioning on `Y`.) -/
theorem law_noiseTarget_ne_law_scoreOfNoisy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Z : Ω → ℝ} (hXZ : IndepFun X Z P) (hX : P.map X = gaussianReal 0 1)
    (hZ : P.map Z = gaussianReal 0 1) {σ : ℝ} (hσ : 0 < σ) :
    P.map (fun ω => -Z ω / σ) ≠
      P.map (fun ω => score1 (gaussianPDFReal 0 ⟨1 + σ ^ 2, by positivity⟩) (X ω + σ * Z ω)) := by
  rw [law_noiseTarget hZ hσ.ne', law_scoreOfNoisy hXZ hX hZ σ]
  exact noiseTarget_law_ne_scoreLaw hσ.ne'

/-- **CE-02, almost-sure form.** Under the hypotheses of
`law_noiseTarget_ne_law_scoreOfNoisy`, the noise target `-Z / σ` is not `P`-a.s. equal to
`score(Y)`, `Y = X + σ Z`. -/
theorem not_noiseTarget_ae_eq_scoreOfNoisy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Z : Ω → ℝ} (hXZ : IndepFun X Z P) (hX : P.map X = gaussianReal 0 1)
    (hZ : P.map Z = gaussianReal 0 1) {σ : ℝ} (hσ : 0 < σ) :
    ¬ ((fun ω => -Z ω / σ) =ᵐ[P]
      fun ω => score1 (gaussianPDFReal 0 ⟨1 + σ ^ 2, by positivity⟩) (X ω + σ * Z ω)) := by
  intro hae
  exact law_noiseTarget_ne_law_scoreOfNoisy hXZ hX hZ hσ (Measure.map_congr hae)

end FormalizeSampling.Counterexamples.ScoreNotNoise
