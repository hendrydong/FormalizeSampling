module

public import FormalizeSampling.Flow.DecayWithError
public import FormalizeSampling.Foundations.GaussianLSIZeroPi
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The log-Sobolev hypothesis of FL-4 for an isotropic Gaussian target

The FL-4 decay theorems of `Flow/KLDecay.lean` and `Flow/DecayWithError.lean` assume the named
hypothesis `KLDecay.LogSobolevAlong lam μ s sStar KL`, i.e.
`KL t ≤ relFisher (μ t) (s t) sStar / (2 lam)` for all `t ≥ 0`, where
`relFisher μ s sStar = ∫ |s - sStar|² dμ` (Euclidean norm; there is no preconditioner in
`relFisher`). This file discharges it for the target `π = N(0, v I)` on `Fin d → ℝ`
(`v > 0`, target score `sStar x = -(1/v) x`, `lam = 1/v`), for any flow of positive differentiable
densities, using the time-zero Gaussian LSI
`GaussianLSIZeroPi.klDiv_le_fisher0` at every time.

Status: **Verified** (`logSobolevAlong_gaussian`); the restated decay theorems are
**Conditional** on `KLDecay.KLFirstVariation` only (plus the per-time density hypotheses).

## Setting

`p : ℝ → (Fin d → ℝ) → ℝ` with gradients `gp : ℝ → (Fin d → ℝ) → Fin d → ℝ`;
`μ t = volume.withDensity (ofReal ∘ p t)`; state score `s t x i = gp t x i / p t x`
(`densityScore`); `KL t = (klDiv (μ t) π).toReal` (`gaussKL`). For each `t ≥ 0` the
hypotheses of `klDiv_le_fisher0` (`GaussianDensityHyp`) are assumed:
`μ t` is a probability measure, `p t > 0`, `HasFDerivAt (p t) (dotCLM (gp t x)) x`,
`∫ |x|² p t < ∞` and `∫ p t ∑ᵢ (∂ᵢp/p + xᵢ/v)² < ∞`.

## Main results

* `relFisher_densityScore`: `relFisher (μ t) (s t) sStar = ∫ p ∑ᵢ (∂ᵢp/p + xᵢ/v)²`, the Fisher
  functional of `klDiv_le_fisher0`, together with integrability of
  `|s - sStar|²` under `μ t` (`integrable_fisher_densityScore`).
* `logSobolevAlong_gaussian`: `LogSobolevAlong (1/v) μ s sStar KL`.
* `logSobolevAlong_gaussian_score`: the same with `s t = score (p t)` (the shared
  `FormalizeSampling.score`, i.e. `∇ log p t`).
* FL-4 for the Gaussian target with the LSI (and the Fisher integrability) discharged:
  `exp_decay_idealVelocity_gaussian` (any SPD `H`, `λ_max(H) ≤ M`; rate `2 t / (v M)`),
  `exp_decay_idealVelocity_gaussian_one` (`H = 1`, rate `2 t / v`, also the dissipation
  integrability discharged), `exp_decay_approxVelocity_gaussian`,
  `exp_decay_absError_gaussian` and `exp_decay_absError_sup_gaussian`.

## Not proved here

* The KL first-variation formula `KLFirstVariation` (continuity equation and its analytic
  justification) remains a hypothesis, as do the per-time regularity hypotheses on `p t` and the
  integrability hypotheses involving the velocity or the preconditioner `H ≠ 1`.
* No LSI for non-Gaussian targets; no existence of a flow with the assumed properties.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Matrix Filter
open scoped ENNReal

namespace FormalizeSampling.LogSobolevAlongGaussian

open FormalizeSampling.KLDecay FormalizeSampling.DecayWithError
open FormalizeSampling.HeatFlowDeBruijnPi (dotCLM dotCLM_single)

variable {d : ℕ}

/-! ### Definitions -/

/-- The score `x ↦ -(1/v) x` of the isotropic Gaussian `N(0, v I)`. -/
noncomputable def gaussScore (v : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  -(1 / v) • x

/-- The state score `∂ᵢp(x) / p(x)` of a density `p` with gradient `gp`. -/
noncomputable def densityScore (p : (Fin d → ℝ) → ℝ) (gp : (Fin d → ℝ) → Fin d → ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => gp x i / p x

/-- The isotropic Gaussian target `N(0, v I)` on `Fin d → ℝ`. -/
noncomputable def gaussTarget (v : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal

/-- The law `p(x) dx` (with `ENNReal.ofReal` truncation). It is the same measure as
`KLDecay.densityMeasure` (`lawOf_eq_densityMeasure`). -/
noncomputable def lawOf (p : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (p x)

/-- `lawOf p` coincides with `KLDecay.densityMeasure p` (and with `NoiseScore.densityMeasure p`):
all three are `volume.withDensity (ofReal ∘ p)`. -/
theorem lawOf_eq_densityMeasure (p : (Fin d → ℝ) → ℝ) :
    lawOf p = KLDecay.densityMeasure p := rfl

/-- The real-valued KL divergence `t ↦ KL(p t dx ‖ N(0, v I))` along a family of densities
(`0` where the divergence is infinite, by `ENNReal.toReal`). Under `GaussianDensityHyp` the
divergence is finite (`GaussianLSIZeroPi.klDiv_le_fisher0`.1), so the `toReal` is not
truncated there. -/
noncomputable def gaussKL (p : ℝ → (Fin d → ℝ) → ℝ) (v t : ℝ) : ℝ :=
  (klDiv (lawOf (p t)) (gaussTarget (d := d) v)).toReal

/-- The per-time hypotheses of `GaussianLSIZeroPi.klDiv_le_fisher0` for a density `p`
with gradient `gp` and variance `v`: `p dx` is a probability measure, `p > 0`, `p` is Fréchet
differentiable with gradient `gp` (no continuity of `gp`), finite second moment and finite
relative Fisher information against `N(0, v I)`. -/
structure GaussianDensityHyp (p : (Fin d → ℝ) → ℝ) (gp : (Fin d → ℝ) → Fin d → ℝ) (v : ℝ) :
    Prop where
  /-- `p dx` is a probability measure. -/
  prob : IsProbabilityMeasure (lawOf p)
  /-- `p` is everywhere positive. -/
  pos : ∀ x, 0 < p x
  /-- `p` has gradient `gp`. -/
  hasFDerivAt : ∀ x, HasFDerivAt p (dotCLM (gp x)) x
  /-- Finite second moment. -/
  moment : Integrable fun x => (∑ i, x i ^ 2) * p x
  /-- Finite relative Fisher information against `N(0, v I)`. -/
  fisher : Integrable fun x => p x * ∑ i, (gp x i / p x + x i / v) ^ 2

/-! ### The relative Fisher information of `KLDecay` for the Gaussian target -/

/-- Pointwise: `|∇p/p - gaussScore v x|² = ∑ᵢ (∂ᵢp/p + xᵢ/v)²`. -/
theorem fisher_integrand_eq (p : (Fin d → ℝ) → ℝ) (gp : (Fin d → ℝ) → Fin d → ℝ) (v : ℝ)
    (x : Fin d → ℝ) :
    (densityScore p gp x - gaussScore v x) ⬝ᵥ (densityScore p gp x - gaussScore v x) =
      ∑ i, (gp x i / p x + x i / v) ^ 2 := by
  simp only [dotProduct, densityScore, gaussScore, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Under `GaussianDensityHyp`, `|s - sStar|²` is integrable under `p dx`, for the state score
`s = ∇p/p` and the Gaussian score `sStar = -(1/v) x`. -/
theorem integrable_fisher_densityScore {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ}
    {v : ℝ} (h : GaussianDensityHyp p gp v) :
    Integrable (fun x => (densityScore p gp x - gaussScore v x) ⬝ᵥ
      (densityScore p gp x - gaussScore v x)) (lawOf p) := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (h.hasFDerivAt x).continuousAt
  rw [lawOf, integrable_withDensity_iff_integrable_smul' hpc.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine h.fisher.congr (Eventually.of_forall fun x => ?_)
  simp only [fisher_integrand_eq, ENNReal.toReal_ofReal (h.pos x).le, smul_eq_mul]

/-- Under `GaussianDensityHyp`, the `KLDecay` relative Fisher information
`relFisher (p dx) (∇p/p) (-(1/v) x) = ∫ |∇p/p + x/v|² p dx` is the Fisher functional
`∫ p ∑ᵢ (∂ᵢp/p + xᵢ/v)²` of `klDiv_le_fisher0`. -/
theorem relFisher_densityScore {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ} {v : ℝ}
    (h : GaussianDensityHyp p gp v) :
    relFisher (lawOf p) (densityScore p gp) (gaussScore v) =
      ∫ x, p x * ∑ i, (gp x i / p x + x i / v) ^ 2 := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (h.hasFDerivAt x).continuousAt
  rw [relFisher, lawOf, MeasureHelpers.integral_withDensity_ofReal hpc.measurable
    fun x => (h.pos x).le]
  simp only [fisher_integrand_eq]

/-- **Gaussian LSI in `KLDecay` form at a single time.** Under `GaussianDensityHyp p gp v` with
`v > 0`: `KL(p dx ‖ N(0, v I)) ≤ relFisher (p dx) (∇p/p) (-(1/v) x) / (2 (1/v))`. -/
theorem klDiv_le_relFisher {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ} {v : ℝ}
    (hv : 0 < v) (h : GaussianDensityHyp p gp v) :
    (klDiv (lawOf p) (gaussTarget (d := d) v)).toReal ≤
      relFisher (lawOf p) (densityScore p gp) (gaussScore v) / (2 * (1 / v)) := by
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) := h.prob
  have key := (GaussianLSIZeroPi.klDiv_le_fisher0 h.pos h.hasFDerivAt hv
    h.moment h.fisher).2
  rw [relFisher_densityScore h]
  have he : ∀ F : ℝ, F / (2 * (1 / v)) = v / 2 * F := fun F => by field_simp
  rw [he]
  exact key

/-! ### `LogSobolevAlong` for the Gaussian target -/

/-- **`LogSobolevAlong` for `N(0, v I)` (Verified).** Let `v > 0` and let `p t` be densities with
gradients `gp t` satisfying `GaussianDensityHyp (p t) (gp t) v` for every `t ≥ 0`. With
`μ t = p t dx`, `s t = ∇p t / p t`, `sStar x = -(1/v) x` and `KL t = KL(μ t ‖ N(0, v I))`,
the FL-4 hypothesis `LogSobolevAlong (1/v) μ s sStar KL` holds. -/
theorem logSobolevAlong_gaussian {v : ℝ} (hv : 0 < v) {p : ℝ → (Fin d → ℝ) → ℝ}
    {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v) :
    LogSobolevAlong (1 / v) (fun t => lawOf (p t)) (fun t => densityScore (p t) (gp t))
      (gaussScore v) (gaussKL p v) :=
  fun t ht => klDiv_le_relFisher hv (hp t ht)

/-- Under `GaussianDensityHyp`, the shared score `score p = ∇ log p` equals `∇p/p`. -/
theorem score_eq_densityScore {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ} {v : ℝ}
    (h : GaussianDensityHyp p gp v) : score p = densityScore p gp := by
  funext x i
  rw [score_apply_of_pos (h.hasFDerivAt x).differentiableAt (h.pos x), partialDeriv,
    (h.hasFDerivAt x).fderiv, dotCLM_single, densityScore]

/-- **`LogSobolevAlong` for `N(0, v I)` with the shared score (Verified).** As
`logSobolevAlong_gaussian`, with state score `score (p t) = ∇ log p t`. -/
theorem logSobolevAlong_gaussian_score {v : ℝ} (hv : 0 < v) {p : ℝ → (Fin d → ℝ) → ℝ}
    {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v) :
    LogSobolevAlong (1 / v) (fun t => lawOf (p t)) (fun t => score (p t))
      (gaussScore v) (gaussKL p v) := by
  intro t ht
  beta_reduce
  rw [score_eq_densityScore (hp t ht)]
  exact logSobolevAlong_gaussian hv hp t ht

/-! ### FL-4 for the Gaussian target -/

/-- **FL-4, ideal PFG velocity, Gaussian target (Conditional on `KLFirstVariation`).** Let
`v > 0`, `H` positive definite with `uᵀ H u ≤ M |u|²` (`M > 0`), and densities `p t` with
gradients `gp t` satisfying `GaussianDensityHyp (p t) (gp t) v` for `t ≥ 0`. Assume the
**assumed** first-variation formula along `v⋆_t = H⁻¹(sStar - s t)` and integrability of
`‖s t - sStar‖²_{H⁻¹}` under `p t dx`. Then
`KL(p t ‖ N(0, v I)) ≤ exp(-2 t / (v M)) KL(p 0 ‖ N(0, v I))` for `t ≥ 0`. -/
theorem exp_decay_idealVelocity_gaussian {v : ℝ} (hv : 0 < v) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {M : ℝ} (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u))
    {p : ℝ → (Fin d → ℝ) → ℝ} {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v)
    (hKL : KLFirstVariation (fun t => lawOf (p t))
      (fun t => idealVelocity H (densityScore (p t) (gp t)) (gaussScore v))
      (fun t => densityScore (p t) (gp t)) (gaussScore v) (gaussKL p v))
    (hdiss : ∀ t, 0 ≤ t → Integrable
      (fun x => sqNormH H⁻¹ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t))) :
    ∀ t, 0 ≤ t → gaussKL p v t ≤ Real.exp (-2 * t / (v * M)) * gaussKL p v 0 := by
  intro t ht
  have h := exp_decay_idealVelocity hH hM hspec (by positivity : (0 : ℝ) < 1 / v) hKL hdiss
    (fun t ht => integrable_fisher_densityScore (hp t ht)) (logSobolevAlong_gaussian hv hp) t ht
  have he : -2 * (1 / v) * t / M = -2 * t / (v * M) := by field_simp
  rwa [he] at h

/-- **FL-4, ideal velocity with `H = 1`, Gaussian target (Conditional on
`KLFirstVariation`).** For `v > 0` and densities satisfying `GaussianDensityHyp (p t) (gp t) v`
for `t ≥ 0`, if `KL` satisfies the **assumed** first-variation formula along
`v⋆_t = sStar - s t` (written `idealVelocity 1`), then
`KL(p t ‖ N(0, v I)) ≤ exp(-2 t / v) KL(p 0 ‖ N(0, v I))` for `t ≥ 0`. -/
theorem exp_decay_idealVelocity_gaussian_one {v : ℝ} (hv : 0 < v)
    {p : ℝ → (Fin d → ℝ) → ℝ} {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v)
    (hKL : KLFirstVariation (fun t => lawOf (p t))
      (fun t => idealVelocity 1 (densityScore (p t) (gp t)) (gaussScore v))
      (fun t => densityScore (p t) (gp t)) (gaussScore v) (gaussKL p v)) :
    ∀ t, 0 ≤ t → gaussKL p v t ≤ Real.exp (-2 * t / v) * gaussKL p v 0 := by
  have hdiss : ∀ t, 0 ≤ t → Integrable
      (fun x => sqNormH (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹
        (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)) := by
    intro t ht
    simpa only [inv_one, sqNormH, one_mulVec] using integrable_fisher_densityScore (hp t ht)
  intro t ht
  have h := exp_decay_idealVelocity_gaussian hv Matrix.PosDef.one one_pos
    (fun u => by simp [sqNormH]) hp hKL hdiss t ht
  rwa [mul_one] at h

/-- **FL-4, approximate velocity with relative error, Gaussian target (Conditional on
`KLFirstVariation`).** As `KLDecay.exp_decay_approxVelocity` with `lam = 1/v`, the target
`N(0, v I)` and `LogSobolevAlong` and the Fisher integrability discharged from
`GaussianDensityHyp`: `KL(t) ≤ exp(-κ t / (v M)) KL(0)` for `t ≥ 0`. -/
theorem exp_decay_approxVelocity_gaussian {v : ℝ} (hv : 0 < v) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {M κ : ℝ} (hM : 0 < M)
    (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hκ : 0 < κ)
    {p : ℝ → (Fin d → ℝ) → ℝ} {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {f : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v)
    (hKL : KLFirstVariation (fun t => lawOf (p t)) f (fun t => densityScore (p t) (gp t))
      (gaussScore v) (gaussKL p v))
    (hrate : ∀ t, 0 ≤ t → Integrable
      (fun x => f t x ⬝ᵥ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)))
    (hdiss : ∀ t, 0 ≤ t → Integrable
      (fun x => sqNormH H⁻¹ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H
      (f t x - idealVelocity H (densityScore (p t) (gp t)) (gaussScore v) x)) (lawOf (p t)))
    (happrox : ∀ t, 0 ≤ t →
      ∫ x, sqNormH H (f t x - idealVelocity H (densityScore (p t) (gp t)) (gaussScore v) x)
          ∂(lawOf (p t)) ≤
        (1 - κ) * ∫ x, sqNormH H⁻¹ (densityScore (p t) (gp t) x - gaussScore v x)
          ∂(lawOf (p t))) :
    ∀ t, 0 ≤ t → gaussKL p v t ≤ Real.exp (-(κ * t / (v * M))) * gaussKL p v 0 := by
  intro t ht
  have h := exp_decay_approxVelocity hH hM hspec (by positivity : (0 : ℝ) < 1 / v) hκ hKL
    hrate hdiss herr (fun t ht => integrable_fisher_densityScore (hp t ht)) happrox
    (logSobolevAlong_gaussian hv hp) t ht
  have he : -(1 / v * κ * t / M) = -(κ * t / (v * M)) := by field_simp
  rwa [he] at h

/-- **FL-4 with absolute velocity error, Gaussian target (Conditional on
`KLFirstVariation`).** As `DecayWithError.exp_decay_absError` with `lam = 1/v`, the target
`N(0, v I)` and `LogSobolevAlong` and the Fisher integrability discharged from
`GaussianDensityHyp`: with `E t = ∫ ‖f t - v⋆_t‖²_H d(p t dx)` continuous on `[0, ∞)`,
`KL(t) ≤ exp(-t / (v M)) KL(0) + ½ ∫₀ᵗ exp(-(t - r) / (v M)) E(r) dr` for `t ≥ 0`. -/
theorem exp_decay_absError_gaussian {v : ℝ} (hv : 0 < v) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {M : ℝ} (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u))
    {p : ℝ → (Fin d → ℝ) → ℝ} {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {f : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v)
    (hKL : KLFirstVariation (fun t => lawOf (p t)) f (fun t => densityScore (p t) (gp t))
      (gaussScore v) (gaussKL p v))
    (hrate : ∀ t, 0 ≤ t → Integrable
      (fun x => f t x ⬝ᵥ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)))
    (hdiss : ∀ t, 0 ≤ t → Integrable
      (fun x => sqNormH H⁻¹ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H
      (f t x - idealVelocity H (densityScore (p t) (gp t)) (gaussScore v) x)) (lawOf (p t)))
    (hEcont : ContinuousOn (fun t => ∫ x, sqNormH H
      (f t x - idealVelocity H (densityScore (p t) (gp t)) (gaussScore v) x) ∂(lawOf (p t)))
      (Set.Ici 0)) :
    ∀ t, 0 ≤ t → gaussKL p v t ≤ Real.exp (-(t / (v * M))) * gaussKL p v 0 +
      (1 / 2) * ∫ r in (0 : ℝ)..t, Real.exp (-((t - r) / (v * M))) *
        ∫ x, sqNormH H (f r x - idealVelocity H (densityScore (p r) (gp r)) (gaussScore v) x)
          ∂(lawOf (p r)) := by
  intro t ht
  have h := exp_decay_absError hH hM hspec (by positivity : (0 : ℝ) < 1 / v) hKL hrate hdiss
    herr (fun t ht => integrable_fisher_densityScore (hp t ht)) (logSobolevAlong_gaussian hv hp)
    hEcont t ht
  have he : ∀ a : ℝ, -(1 / v * a / M) = -(a / (v * M)) := fun a => by field_simp
  simp only [he] at h
  exact h

/-- **FL-4 with a uniform absolute velocity error, Gaussian target (Conditional on
`KLFirstVariation`).** As `DecayWithError.exp_decay_absError_sup` with `lam = 1/v`, the target
`N(0, v I)` and `LogSobolevAlong` and the Fisher integrability discharged from
`GaussianDensityHyp`: if `∫ ‖f t - v⋆_t‖²_H d(p t dx) ≤ ε` for all `t ≥ 0` (`ε ≥ 0`), then
`KL(t) ≤ exp(-t / (v M)) KL(0) + ε M v / 2 · (1 - exp(-t / (v M)))` and
`KL(t) ≤ exp(-t / (v M)) KL(0) + ε M v / 2` for `t ≥ 0`. -/
theorem exp_decay_absError_sup_gaussian {v : ℝ} (hv : 0 < v) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {M ε : ℝ} (hM : 0 < M)
    (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hε : 0 ≤ ε)
    {p : ℝ → (Fin d → ℝ) → ℝ} {gp : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {f : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hp : ∀ t, 0 ≤ t → GaussianDensityHyp (p t) (gp t) v)
    (hKL : KLFirstVariation (fun t => lawOf (p t)) f (fun t => densityScore (p t) (gp t))
      (gaussScore v) (gaussKL p v))
    (hrate : ∀ t, 0 ≤ t → Integrable
      (fun x => f t x ⬝ᵥ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)))
    (hdiss : ∀ t, 0 ≤ t → Integrable
      (fun x => sqNormH H⁻¹ (densityScore (p t) (gp t) x - gaussScore v x)) (lawOf (p t)))
    (herr : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H
      (f t x - idealVelocity H (densityScore (p t) (gp t)) (gaussScore v) x)) (lawOf (p t)))
    (hEbound : ∀ t, 0 ≤ t → ∫ x, sqNormH H
      (f t x - idealVelocity H (densityScore (p t) (gp t)) (gaussScore v) x)
        ∂(lawOf (p t)) ≤ ε) :
    ∀ t, 0 ≤ t →
      gaussKL p v t ≤ Real.exp (-(t / (v * M))) * gaussKL p v 0 +
          ε * M * v / 2 * (1 - Real.exp (-(t / (v * M)))) ∧
      gaussKL p v t ≤ Real.exp (-(t / (v * M))) * gaussKL p v 0 + ε * M * v / 2 := by
  intro t ht
  have h := exp_decay_absError_sup hH hM hspec (by positivity : (0 : ℝ) < 1 / v) hε hKL hrate
    hdiss herr (fun t ht => integrable_fisher_densityScore (hp t ht))
    (logSobolevAlong_gaussian hv hp) hEbound t ht
  have he : -(1 / v * t / M) = -(t / (v * M)) := by field_simp
  have hc : ε * M / (2 * (1 / v)) = ε * M * v / 2 := by field_simp
  rwa [he, hc] at h

end FormalizeSampling.LogSobolevAlongGaussian
