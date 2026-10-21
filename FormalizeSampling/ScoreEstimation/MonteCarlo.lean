module

public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Finite-sample Monte Carlo posterior-mean and score oracles

Registry ID: **SE-4** (unbiased posterior sample-mean estimator; the mean squared error of the
sample mean of `n` independent draws is `variance / n`), together with
their consequences for a Monte Carlo score oracle in the style of Reverse Diffusion Monte Carlo
(rdMC).

## Setting and conventions

* `(Ω, P)` is a measure space, a probability space wherever an expectation of a constant
  appears. Samples are real random variables `X : Fin n → Ω → ℝ`.
* `sampleMean X ω = (1 / n) * ∑ᵢ X i ω`. All quantitative results assume `0 < n`
  (for `n = 0` Lean's convention `1 / 0 = 0` makes the sample mean identically `0`).
* Moments are stated with Mathlib's Bochner integral `∫ ω, f ω ∂P` and
  `ProbabilityTheory.variance`. Every result that uses a second moment assumes
  `MemLp (X i) 2 P`, so that the integrals are genuine (finite) integrals and the variance is
  the real variance (not a truncation of `∞`).
* Independence is **pairwise** independence `IndepFun (X i) (X j) P` for `i ≠ j`; the
  i.i.d. corollaries take mutual independence `iIndepFun X P` and a common law
  `HasLaw (X i) π P`, with `π` the (posterior) law on `ℝ`.
* The score oracle is `scoreEstimate a y s2 X ω = (a * sampleMean X ω - y) / s2`. In the
  OU/rdMC application `a = a_t = e^{-t}`, `s2 = σ_t² = 1 - e^{-2t} > 0`, `y` is the current
  point and the `X i` are draws from the posterior of `X₀` given `X_t = y`; then
  `(a * m - y) / s2` with `m = 𝔼[X₀ | X_t = y]` is the exact OU score `∇ log p_t(y)` by SE-3
  (proved elsewhere; this file does not import it). The algebraic results below hold for every
  real `s2`; for `s2 = 0` both sides degenerate to `0` by the convention `x / 0 = 0`, so only
  `s2 > 0` is meaningful.

## Main results

* `integral_sampleMean` (SE-4): `𝔼[sampleMean] = m`.
* `variance_sampleMean`, `integral_sq_sampleMean_sub` (SE-4):
  `Var[sampleMean] = v / n` and `𝔼[(sampleMean - m)²] = v / n`.
* `*_of_hasLaw`, `*_of_iid`: the same with `m = ∫ x dπ`, `v = Var_π` for i.i.d. draws from `π`;
  `sampleMean_moments_of_identDistrib`: the same with `IdentDistrib (X i) (X 0) P P`.
* `integral_scoreEstimate`, `integral_sq_scoreEstimate_sub`, `variance_scoreEstimate`:
  `𝔼[ŝ] = (a m - y) / s2` and `𝔼[(ŝ - (a m - y) / s2)²] = a² v / (n s2²)`.
* `meas_abs_scoreEstimate_sub_ge_le` (Chebyshev):
  `P(|ŝ - (a m - y) / s2| ≥ ε) ≤ a² v / (n s2² ε²)`.
* Vector version on `Fin d → ℝ`: `integral_vecSampleMean` and
  `integral_dotProduct_vecSampleMean_sub`, `𝔼‖mean - m‖₂² = (∑ₖ vₖ) / n`.

## What is NOT proved

* **Exact sampling is assumed.** The samples must be exact, independent draws from the
  posterior (or at least have the stated common mean and variance and be pairwise
  independent). Approximate inner samplers (e.g. Langevin-type inner loops) produce biased,
  correlated draws; that bias and its propagation are not covered here.
* The identification of `(a * m - y) / s2` with the OU score `∇ log p_t(y)` is SE-3 and is
  not re-proved or imported here; the posterior mean `m` is an input constant.
* No high-probability bounds beyond Chebyshev (no sub-Gaussian / Bernstein concentration),
  no uniform-in-`y` bounds, and no propagation of the score error into a sampling (kernel or
  TV / KL) error (that is GI-1 and KR-1).
* The vector version controls the Euclidean MSE coordinatewise (sum of coordinate variances,
  i.e. the trace of the covariance); no matrix-valued covariance statement is given.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace FormalizeSampling
namespace MonteCarlo

section Defs

variable {Ω : Type*} {n : ℕ}

/-- The Monte Carlo sample mean `(1 / n) * ∑ᵢ X i ω` of `n` real samples. For `n = 0` it is
identically `0` (Lean's `1 / 0 = 0`); all quantitative results assume `0 < n`. -/
noncomputable def sampleMean (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, X i ω

/-- The sample mean as a function is the scalar multiple `(1 / n) • ∑ᵢ X i`. -/
theorem sampleMean_eq_smul (X : Fin n → Ω → ℝ) :
    sampleMean X = (1 / (n : ℝ)) • ∑ i, X i := by
  funext ω
  simp [sampleMean, Finset.sum_apply]

/-- The rdMC-style Monte Carlo score estimate `ŝ(ω) = (a * sampleMean X ω - y) / s2` built from
posterior samples `X i`. In the OU application `a = e^{-t}`, `s2 = σ_t² = 1 - e^{-2t} > 0` and
`y` is the evaluation point; for `s2 = 0` it is `0` by Lean's `x / 0 = 0` convention. -/
noncomputable def scoreEstimate (a y s2 : ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (a * sampleMean X ω - y) / s2

/-- The vector-valued sample mean `(1 / n) • ∑ᵢ X i ω` of `n` samples in `Fin d → ℝ`. -/
noncomputable def vecSampleMean {d : ℕ} (X : Fin n → Ω → Fin d → ℝ) (ω : Ω) : Fin d → ℝ :=
  (1 / (n : ℝ)) • ∑ i, X i ω

/-- The `k`-th coordinate of the vector sample mean is the scalar sample mean of the `k`-th
coordinates of the samples. -/
theorem vecSampleMean_apply {d : ℕ} (X : Fin n → Ω → Fin d → ℝ) (ω : Ω) (k : Fin d) :
    vecSampleMean X ω k = sampleMean (fun i ω => X i ω k) ω := by
  simp [vecSampleMean, sampleMean, Finset.sum_apply]

end Defs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-! ### Integrability of the estimators -/

/-- If every sample `X i` is integrable, so is the sample mean. -/
theorem integrable_sampleMean {X : Fin n → Ω → ℝ} (hX : ∀ i, Integrable (X i) P) :
    Integrable (sampleMean X) P := by
  show Integrable (fun ω => (1 / (n : ℝ)) * ∑ i, X i ω) P
  exact (integrable_finsetSum _ fun i _ => hX i).const_mul _

/-- If every sample `X i` has a finite second moment (`MemLp (X i) 2 P`), so does the sample
mean. -/
theorem memLp_sampleMean {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (sampleMean X) 2 P := by
  rw [sampleMean_eq_smul]
  exact (memLp_finsetSum' _ fun i _ => hX i).const_smul _

/-- On a finite measure space, if every sample has a finite second moment then so does the
score estimate `(a * sampleMean X - y) / s2` (for all real constants `a, y, s2`). -/
theorem memLp_scoreEstimate [IsFiniteMeasure P] {X : Fin n → Ω → ℝ} (a y s2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) : MemLp (scoreEstimate a y s2 X) 2 P := by
  have h : scoreEstimate a y s2 X = fun ω => s2⁻¹ * (a * sampleMean X ω - y) := by
    funext ω
    simp [scoreEstimate, div_eq_inv_mul]
  rw [h]
  exact (((memLp_sampleMean hX).const_mul a).sub (memLp_const y)).const_mul s2⁻¹

/-! ### SE-4: unbiasedness of the sample mean -/

/-- **SE-4 (unbiased sample mean).** If `0 < n` and the samples `X i` are integrable with
common mean `∫ X i dP = m`, then `𝔼[sampleMean X] = m`. No independence is needed. -/
theorem integral_sampleMean (hn : 0 < n) {X : Fin n → Ω → ℝ} {m : ℝ}
    (hX : ∀ i, Integrable (X i) P) (hm : ∀ i, ∫ ω, X i ω ∂P = m) :
    ∫ ω, sampleMean X ω ∂P = m := by
  simp only [sampleMean]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hX i]
  simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-! ### SE-4: variance and mean squared error of the sample mean -/

/-- **SE-4 (variance of the sample mean).** If `0 < n`, the samples have finite second
moments (`MemLp (X i) 2 P`), are pairwise independent and have common variance `v`, then
`Var[sampleMean X] = v / n`. -/
theorem variance_sampleMean (hn : 0 < n) {X : Fin n → Ω → ℝ} {v : ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hv : ∀ i, variance (X i) P = v) :
    variance (sampleMean X) P = v / n := by
  rw [sampleMean_eq_smul, variance_smul, IndepFun.variance_sum (fun i _ => hX i) ?_]
  · simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · rw [Finset.coe_univ, Set.pairwise_univ]
    exact hindep

/-- **SE-4 (mean squared error of the sample mean).** On a probability space, if `0 < n`,
the samples have finite second moments, are pairwise independent, and have common mean `m`
and common variance `v`, then `𝔼[(sampleMean X - m)²] = v / n`. -/
theorem integral_sq_sampleMean_sub [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {m v : ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hm : ∀ i, ∫ ω, X i ω ∂P = m) (hv : ∀ i, variance (X i) P = v) :
    ∫ ω, (sampleMean X ω - m) ^ 2 ∂P = v / n := by
  rw [← variance_sampleMean hn hX hindep hv,
    variance_eq_integral (memLp_sampleMean hX).aemeasurable,
    integral_sampleMean hn (fun i => (hX i).integrable one_le_two) hm]

/-! ### Identically distributed (posterior-law) formulation -/

/-- **SE-4, common-law form.** If `0 < n`, every sample `X i` has law `π` on `ℝ`
(`HasLaw (X i) π P`) and `π` has a finite first moment (`Integrable id π`), then
`𝔼[sampleMean X] = ∫ x dπ(x)`, the mean of `π`. -/
theorem integral_sampleMean_of_hasLaw (hn : 0 < n) {X : Fin n → Ω → ℝ} {π : Measure ℝ}
    (hπ : Integrable id π) (hlaw : ∀ i, HasLaw (X i) π P) :
    ∫ ω, sampleMean X ω ∂P = ∫ x, x ∂π := by
  have hXi : ∀ i, Integrable (X i) P := fun i => by
    have h := hπ
    rw [← (hlaw i).map_eq] at h
    exact (integrable_map_measure aestronglyMeasurable_id (hlaw i).aemeasurable).1 h
  exact integral_sampleMean hn hXi fun i => (hlaw i).integral_eq

/-- If `X` has law `π` and `π` has a finite second moment, then `X` has a finite second
moment. -/
theorem memLp_of_hasLaw {Y : Ω → ℝ} {π : Measure ℝ} (hπ : MemLp id 2 π) (hlaw : HasLaw Y π P) :
    MemLp Y 2 P := by
  have h := hπ
  rw [← hlaw.map_eq] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id hlaw.aemeasurable).1 h

/-- **SE-4, common-law form (variance).** If `0 < n`, every sample has law `π` on `ℝ`,
`π` has a finite second moment and the samples are pairwise independent, then
`Var[sampleMean X] = Var_π / n`, where `Var_π = variance id π`. -/
theorem variance_sampleMean_of_hasLaw (hn : 0 < n) {X : Fin n → Ω → ℝ} {π : Measure ℝ}
    (hπ : MemLp id 2 π) (hlaw : ∀ i, HasLaw (X i) π P)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P) :
    variance (sampleMean X) P = variance id π / n :=
  variance_sampleMean hn (fun i => memLp_of_hasLaw hπ (hlaw i)) hindep
    fun i => (hlaw i).variance_eq

/-- **SE-4, common-law form (MSE).** On a probability space, if `0 < n`, every sample has law
`π` on `ℝ`, `π` has a finite second moment and the samples are pairwise independent, then
`𝔼[(sampleMean X - ∫ x dπ)²] = Var_π / n`. -/
theorem integral_sq_sampleMean_sub_of_hasLaw [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {π : Measure ℝ}
    (hπ : MemLp id 2 π) (hlaw : ∀ i, HasLaw (X i) π P)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P) :
    ∫ ω, (sampleMean X ω - ∫ x, x ∂π) ^ 2 ∂P = variance id π / n :=
  integral_sq_sampleMean_sub hn (fun i => memLp_of_hasLaw hπ (hlaw i)) hindep
    (fun i => (hlaw i).integral_eq) fun i => (hlaw i).variance_eq

/-- **SE-4 for i.i.d. draws.** On a probability space, if `0 < n` and `X 0, …, X (n-1)`
are mutually independent (`iIndepFun X P`) draws from a law `π` on `ℝ` with finite second
moment, then the sample mean is unbiased for `∫ x dπ` and its mean squared error is
`Var_π / n`. -/
theorem sampleMean_moments_of_iid [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {π : Measure ℝ}
    (hπ : MemLp id 2 π) (hlaw : ∀ i, HasLaw (X i) π P) (hiid : iIndepFun X P) :
    ∫ ω, sampleMean X ω ∂P = ∫ x, x ∂π ∧
      ∫ ω, (sampleMean X ω - ∫ x, x ∂π) ^ 2 ∂P = variance id π / n := by
  have : IsProbabilityMeasure π := (hlaw ⟨0, hn⟩).isProbabilityMeasure_iff.1 inferInstance
  exact ⟨integral_sampleMean_of_hasLaw hn (hπ.integrable one_le_two) hlaw,
    integral_sq_sampleMean_sub_of_hasLaw hn hπ hlaw fun _ _ hij => hiid.indepFun hij⟩

/-- **SE-4, `IdentDistrib` form.** On a probability space, if `0 < n`, every sample is
identically distributed with the first one, `IdentDistrib (X i) (X 0) P P`, the first sample has
a finite second moment and the samples are pairwise independent, then the sample mean is
unbiased for `𝔼[X 0]` and `𝔼[(sampleMean X - 𝔼[X 0])²] = Var[X 0] / n`. -/
theorem sampleMean_moments_of_identDistrib [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hX₀ : MemLp (X ⟨0, hn⟩) 2 P)
    (hid : ∀ i, IdentDistrib (X i) (X ⟨0, hn⟩) P P)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P) :
    ∫ ω, sampleMean X ω ∂P = ∫ ω, X ⟨0, hn⟩ ω ∂P ∧
      ∫ ω, (sampleMean X ω - ∫ ω', X ⟨0, hn⟩ ω' ∂P) ^ 2 ∂P = variance (X ⟨0, hn⟩) P / n := by
  have hX : ∀ i, MemLp (X i) 2 P := fun i => (hid i).memLp_iff.2 hX₀
  exact ⟨integral_sampleMean hn (fun i => (hX i).integrable one_le_two)
      fun i => (hid i).integral_eq,
    integral_sq_sampleMean_sub hn hX hindep (fun i => (hid i).integral_eq)
      fun i => (hid i).variance_eq⟩

/-! ### Monte Carlo score oracle (rdMC style) -/

/-- **Unbiased score oracle.** On a probability space, if `0 < n` and the samples are integrable
with common mean `m`, then for all real `a, y, s2` the score estimate satisfies
`𝔼[(a * sampleMean X - y) / s2] = (a * m - y) / s2`. When `m` is the posterior mean
`𝔼[X₀ | X_t = y]`, `a = e^{-t}` and `s2 = σ_t² > 0`, the right side is the exact OU score
`∇ log p_t(y)` (SE-3, not imported here). Requires exact posterior draws. -/
theorem integral_scoreEstimate [IsProbabilityMeasure P] (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {m : ℝ} (a y s2 : ℝ) (hX : ∀ i, Integrable (X i) P) (hm : ∀ i, ∫ ω, X i ω ∂P = m) :
    ∫ ω, scoreEstimate a y s2 X ω ∂P = (a * m - y) / s2 := by
  simp only [scoreEstimate]
  rw [integral_div, integral_sub ((integrable_sampleMean hX).const_mul a) (integrable_const y),
    integral_const_mul, integral_sampleMean hn hX hm]
  simp

/-- **Score-oracle mean squared error.** On a probability space, if `0 < n` and the samples have
finite second moments, are pairwise independent and have common mean `m` and common variance
`v`, then for all real `a, y, s2`,
`𝔼[((a * sampleMean X - y) / s2 - (a * m - y) / s2)²] = a² v / (n s2²)`.
(Meaningful for `s2 = σ_t² > 0`; for `s2 = 0` both sides are `0` by Lean's `x / 0 = 0`.)
Requires exact independent posterior draws; inner-sampler bias is not covered. -/
theorem integral_sq_scoreEstimate_sub [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {m v : ℝ} (a y s2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hm : ∀ i, ∫ ω, X i ω ∂P = m) (hv : ∀ i, variance (X i) P = v) :
    ∫ ω, (scoreEstimate a y s2 X ω - (a * m - y) / s2) ^ 2 ∂P = a ^ 2 * v / (n * s2 ^ 2) := by
  have h : ∀ ω, (scoreEstimate a y s2 X ω - (a * m - y) / s2) ^ 2
      = (a / s2) ^ 2 * (sampleMean X ω - m) ^ 2 := by
    intro ω
    simp only [scoreEstimate]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_sq_sampleMean_sub hn hX hindep hm hv]
  ring

/-- **Score-oracle variance.** Under the hypotheses of `integral_sq_scoreEstimate_sub`
(probability space, `0 < n`, finite second moments, pairwise independence, common mean `m` and
variance `v`), `Var[(a * sampleMean X - y) / s2] = a² v / (n s2²)` for all real `a, y, s2`. -/
theorem variance_scoreEstimate [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {m v : ℝ} (a y s2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hm : ∀ i, ∫ ω, X i ω ∂P = m) (hv : ∀ i, variance (X i) P = v) :
    variance (scoreEstimate a y s2 X) P = a ^ 2 * v / (n * s2 ^ 2) := by
  rw [variance_eq_integral (memLp_scoreEstimate a y s2 hX).aemeasurable,
    integral_scoreEstimate hn a y s2 (fun i => (hX i).integrable one_le_two) hm,
    integral_sq_scoreEstimate_sub hn a y s2 hX hindep hm hv]

/-- **Chebyshev bound for the score oracle.** On a probability space, if `0 < n` and the samples
have finite second moments, are pairwise independent and have common mean `m` and common
variance `v`, then for every `ε > 0` and all real `a, y, s2`,
`P(|(a * sampleMean X - y) / s2 - (a * m - y) / s2| ≥ ε) ≤ a² v / (n s2² ε²)`.
With `m` the posterior mean, `(a * m - y) / s2` is the exact OU score (SE-3). The samples
must be exact independent posterior draws; approximate inner samplers add uncovered bias. -/
theorem meas_abs_scoreEstimate_sub_ge_le [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {m v : ℝ} (a y s2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hm : ∀ i, ∫ ω, X i ω ∂P = m) (hv : ∀ i, variance (X i) P = v) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |scoreEstimate a y s2 X ω - (a * m - y) / s2|}
      ≤ ENNReal.ofReal (a ^ 2 * v / (n * s2 ^ 2 * ε ^ 2)) := by
  have h := meas_ge_le_variance_div_sq (memLp_scoreEstimate a y s2 hX) hε
  rw [integral_scoreEstimate hn a y s2 (fun i => (hX i).integrable one_le_two) hm,
    variance_scoreEstimate hn a y s2 hX hindep hm hv, div_div] at h
  exact h

/-- **Chebyshev bound for the score oracle, i.i.d. posterior draws.** On a probability space, if
`0 < n` and `X 0, …, X (n-1)` are mutually independent draws from a law `π` on `ℝ` with finite
second moment (the exact posterior), then for every `ε > 0` and all real `a, y, s2`,
`P(|ŝ - (a * ∫ x dπ - y) / s2| ≥ ε) ≤ a² Var_π / (n s2² ε²)` with
`ŝ = (a * sampleMean X - y) / s2`. -/
theorem meas_abs_scoreEstimate_sub_ge_le_of_iid [IsProbabilityMeasure P] (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {π : Measure ℝ} (a y s2 : ℝ)
    (hπ : MemLp id 2 π) (hlaw : ∀ i, HasLaw (X i) π P) (hiid : iIndepFun X P)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |scoreEstimate a y s2 X ω - (a * ∫ x, x ∂π - y) / s2|}
      ≤ ENNReal.ofReal (a ^ 2 * variance id π / (n * s2 ^ 2 * ε ^ 2)) :=
  meas_abs_scoreEstimate_sub_ge_le hn a y s2 (fun i => memLp_of_hasLaw hπ (hlaw i))
    (fun _ _ hij => hiid.indepFun hij) (fun i => (hlaw i).integral_eq)
    (fun i => (hlaw i).variance_eq) hε

/-! ### Vector-valued sample mean on `Fin d → ℝ` -/

/-- **SE-4, vector form (coordinatewise).** If `0 < n`, every coordinate `X i · k` of every
sample is integrable and the samples have common coordinate means `∫ X i ω k dP = m k`, then
`𝔼[(vecSampleMean X) k] = m k` for every coordinate `k`. -/
theorem integral_vecSampleMean_apply (hn : 0 < n) {d : ℕ} {X : Fin n → Ω → Fin d → ℝ}
    {m : Fin d → ℝ} (hX : ∀ i k, Integrable (fun ω => X i ω k) P)
    (hm : ∀ i k, ∫ ω, X i ω k ∂P = m k) (k : Fin d) :
    ∫ ω, vecSampleMean X ω k ∂P = m k := by
  simp_rw [vecSampleMean_apply]
  exact integral_sampleMean hn (fun i => hX i k) fun i => hm i k

/-- **SE-4, vector form.** Under the hypotheses of `integral_vecSampleMean_apply`, the
(Bochner) expectation of the vector sample mean is the common mean vector:
`𝔼[vecSampleMean X] = m` in `Fin d → ℝ`. -/
theorem integral_vecSampleMean (hn : 0 < n) {d : ℕ} {X : Fin n → Ω → Fin d → ℝ}
    {m : Fin d → ℝ} (hX : ∀ i k, Integrable (fun ω => X i ω k) P)
    (hm : ∀ i k, ∫ ω, X i ω k ∂P = m k) :
    ∫ ω, vecSampleMean X ω ∂P = m := by
  funext k
  have hint : ∀ k, Integrable (fun ω => vecSampleMean X ω k) P := fun k => by
    simp_rw [vecSampleMean_apply]
    exact integrable_sampleMean fun i => hX i k
  rw [eval_integral hint k]
  exact integral_vecSampleMean_apply hn hX hm k

/-- **SE-4, vector form (Euclidean MSE).** On a probability space, if `0 < n`, every
coordinate of every sample has a finite second moment, the `Fin d → ℝ`-valued samples are
pairwise independent, and they have common coordinate means `m k` and common coordinate
variances `v k`, then
`𝔼[(vecSampleMean X - m) ⬝ᵥ (vecSampleMean X - m)] = (∑ₖ v k) / n`,
i.e. the expected squared Euclidean error is the trace of the covariance divided by `n`. -/
theorem integral_dotProduct_vecSampleMean_sub [IsProbabilityMeasure P] (hn : 0 < n) {d : ℕ}
    {X : Fin n → Ω → Fin d → ℝ} {m v : Fin d → ℝ}
    (hX : ∀ i k, MemLp (fun ω => X i ω k) 2 P)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hm : ∀ i k, ∫ ω, X i ω k ∂P = m k) (hv : ∀ i k, variance (fun ω => X i ω k) P = v k) :
    ∫ ω, (vecSampleMean X ω - m) ⬝ᵥ (vecSampleMean X ω - m) ∂P = (∑ k, v k) / n := by
  have h : ∀ ω, (vecSampleMean X ω - m) ⬝ᵥ (vecSampleMean X ω - m)
      = ∑ k, (sampleMean (fun i ω => X i ω k) ω - m k) ^ 2 := by
    intro ω
    simp [dotProduct, vecSampleMean_apply, sq]
  have hint : ∀ k, Integrable (fun ω => (sampleMean (fun i ω => X i ω k) ω - m k) ^ 2) P :=
    fun k => ((memLp_sampleMean fun i => hX i k).sub (memLp_const (m k))).integrable_sq
  simp_rw [h]
  rw [integral_finsetSum _ fun k _ => hint k, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hik : Pairwise fun i j => IndepFun (fun ω => X i ω k) (fun ω => X j ω k) P :=
    fun i j hij => (hindep hij).comp (measurable_pi_apply k) (measurable_pi_apply k)
  exact integral_sq_sampleMean_sub hn (fun i => hX i k) hik (fun i => hm i k) fun i => hv i k

end MonteCarlo
end FormalizeSampling
