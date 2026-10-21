module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Gaussian integration by parts (Stein identity)

Registry ID covered: **ID-1** (1D Gaussian Stein identity), plus a `d`-dimensional
standard-Gaussian version for compactly supported `C¹` test functions.

## Conventions

* `gaussianReal m v` is Mathlib's real Gaussian law with mean `m` and **variance** `v : ℝ≥0`;
  for `v = 0` it is the Dirac mass `δ_m`. `gaussianPDFReal m v` is its Lebesgue density
  `(2πv)^{-1/2} exp(-(x - m)² / (2v))` (identically `0` when `v = 0`).
* Test functions `φ : ℝ → ℝ` come with an explicit derivative `φ'` and the hypothesis
  `∀ x, HasDerivAt φ (φ' x) x`, so no statement relies on the junk value of `deriv`.
* In dimension `d` the state space is `Fin d → ℝ`, the standard Gaussian is the product
  measure `Measure.pi (fun _ => gaussianReal 0 1)`, and `∂ᵢ φ` is
  `FormalizeSampling.partialDeriv i φ`.

## Main results

* `hasDerivAt_gaussianPDFReal`: `d/dx gaussianPDFReal m v x = -((x - m) / v) * pdf(x)`.
* The state score of the Gaussian density, `-(x - m) / v`, is
  `FormalizeSampling.score1_gaussianPDFReal` (`Foundations/VectorCalculus`).
* `integral_sub_mul_eq_var_mul_integral_deriv` (ID-1, general form):
  `E[(X - m) φ(X)] = v E[φ'(X)]` for `X ~ N(m, v)`, assuming `φ` differentiable everywhere
  and `x ↦ (x - m) φ x`, `φ'` integrable against `N(m, v)`. Integrability of `φ` itself and
  `v ≠ 0` are *not* assumed: they are proved redundant (`φ` is continuous, and `v = 0` is the
  Dirac case where both sides vanish).
* `integral_mul_eq_integral_deriv_std`: the standard-normal case `E[Z φ(Z)] = E[φ'(Z)]`.
* Discharged corollaries without integrability hypotheses:
  `integral_sub_mul_eq_of_bounded` / `integral_sub_mul_eq_of_differentiable` (bounded `φ` and
  bounded derivative) and `integral_sub_mul_eq_of_hasCompactSupport` (`C¹`, compact support).
* `integral_coord_mul_eq_integral_partialDeriv`: `E[Zᵢ φ(Z)] = E[∂ᵢ φ(Z)]` for
  `Z ~ N(0, I_d)` and `φ` `C¹` with compact support on `Fin d → ℝ`.

## Not proved here

* The `d`-dimensional identity is proved only for `C¹` compactly supported test functions and
  the standard Gaussian `N(0, I_d)`; no general mean / covariance matrix, and no version
  under mere integrability hypotheses in dimension `d > 1`.
* Only real-valued test functions; no vector-valued `φ`.
* The converse (Stein's characterisation of the Gaussian law) is not proved.
* The general-density Stein identity (ID-2) is not part of this file.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace FormalizeSampling.GaussianStein

/-- **Derivative of the Gaussian density.** For every mean `m`, variance `v : ℝ≥0` and point
`x`, the Gaussian density `gaussianPDFReal m v` has derivative
`-((x - m) / v) * gaussianPDFReal m v x` at `x`. No hypothesis `v ≠ 0` is needed: for `v = 0`
Mathlib's density is the zero function and both sides are `0`. -/
theorem hasDerivAt_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v) (-((x - m) / v) * gaussianPDFReal m v x) x := by
  have h1 : HasDerivAt (fun y => -(y - m) ^ 2 / (2 * (v : ℝ)))
      (-((2 : ℕ) * (x - m) ^ (2 - 1) * 1) / (2 * (v : ℝ))) x :=
    (((hasDerivAt_id x).sub_const m).pow 2).neg.div_const _
  have h2 := (h1.exp).const_mul (√(2 * π * v))⁻¹
  rw [gaussianPDFReal_def]
  convert h2 using 1
  have : -((2 : ℕ) * (x - m) ^ (2 - 1) * 1) / (2 * (v : ℝ)) = -((x - m) / v) := by
    push_cast
    rw [pow_one, mul_one, neg_div, mul_div_mul_left _ _ two_ne_zero]
  rw [this]
  ring

/-- For `v ≠ 0`, a real function `f` is integrable against `gaussianReal m v` if and only if
`x ↦ gaussianPDFReal m v x * f x` is Lebesgue integrable. -/
theorem integrable_gaussianReal_iff_integrable_pdf_mul {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f : ℝ → ℝ} :
    Integrable f (gaussianReal m v) ↔ Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF m v) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

/-- Let `μ` be a measure on `ℝ` that is finite on compact sets and `φ : ℝ → ℝ` continuous.
If `x ↦ (x - m) * φ x` is `μ`-integrable then so is `φ`: on `|x - m| ≥ 1` it is dominated by
`|(x - m) φ x|`, and on the compact interval `[m - 1, m + 1]` it is bounded. -/
theorem integrable_of_integrable_sub_mul {μ : Measure ℝ} [IsFiniteMeasureOnCompacts μ]
    {m : ℝ} {φ : ℝ → ℝ} (hc : Continuous φ) (h : Integrable (fun x => (x - m) * φ x) μ) :
    Integrable φ μ := by
  have hI : Integrable ((Set.Icc (m - 1) (m + 1)).indicator φ) μ :=
    (integrable_indicator_iff measurableSet_Icc).2
      (hc.continuousOn.integrableOn_compact isCompact_Icc)
  refine (h.norm.add hI.norm).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ Set.Icc (m - 1) (m + 1)
  · simp only [Set.indicator_of_mem hx, Pi.add_apply]
    have := norm_nonneg ((x - m) * φ x)
    linarith
  · simp only [Set.indicator_of_notMem hx, Pi.add_apply, norm_zero, add_zero, norm_mul]
    have h1 : 1 ≤ ‖x - m‖ := by
      rw [Real.norm_eq_abs]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    calc ‖φ x‖ = 1 * ‖φ x‖ := (one_mul _).symm
      _ ≤ ‖x - m‖ * ‖φ x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Gaussian Stein identity (ID-1), general mean and variance.** Let `X ~ N(m, v)`
(`gaussianReal m v`, variance `v`). Let `φ φ' : ℝ → ℝ` with `φ` differentiable everywhere and
`φ'` its derivative (`∀ x, HasDerivAt φ (φ' x) x`). Assume `x ↦ (x - m) * φ x` and `φ'` are
integrable against `N(m, v)`. Then
`∫ (x - m) φ(x) dN(m, v) = v * ∫ φ'(x) dN(m, v)`, i.e. `E[(X - m) φ(X)] = v E[φ'(X)]`.

Integrability of `φ` is not assumed (it follows from continuity of `φ` and integrability of
`(x - m) φ x`), and neither is `v ≠ 0`: for `v = 0` the law is `δ_m` and both sides are `0`.
The proof integrates by parts against the density, using
`(gaussianPDFReal m v)' = -((x - m) / v) * gaussianPDFReal m v`. -/
theorem integral_sub_mul_eq_var_mul_integral_deriv {m : ℝ} {v : ℝ≥0} {φ φ' : ℝ → ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hint : Integrable (fun x => (x - m) * φ x) (gaussianReal m v))
    (hint' : Integrable φ' (gaussianReal m v)) :
    ∫ x, (x - m) * φ x ∂(gaussianReal m v) = v * ∫ x, φ' x ∂(gaussianReal m v) := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hφi : Integrable φ (gaussianReal m v) := integrable_of_integrable_sub_mul hc hint
  rw [integrable_gaussianReal_iff_integrable_pdf_mul hv] at hint hint' hφi
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  have h1 : Integrable (φ * fun x => -((x - m) / v) * gaussianPDFReal m v x) := by
    have := hint.const_mul (-(v : ℝ)⁻¹)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    field_simp
  have h2 : Integrable (φ' * gaussianPDFReal m v) := by
    refine hint'.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have h3 : Integrable (φ * gaussianPDFReal m v) := by
    refine hφi.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hφ x)
    (fun x _ => hasDerivAt_gaussianPDFReal m v x) h1 h2 h3
  have e1 : ∫ x, φ x * (-((x - m) / v) * gaussianPDFReal m v x) =
      -(v : ℝ)⁻¹ * ∫ x, gaussianPDFReal m v x * ((x - m) * φ x) := by
    rw [← integral_const_mul]
    congr 1 with x
    field_simp
  have e2 : ∫ x, φ' x * gaussianPDFReal m v x = ∫ x, gaussianPDFReal m v x * φ' x := by
    congr 1 with x
    ring
  rw [e1, e2, neg_mul, neg_inj] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ hv', one_mul]

/-- **Gaussian Stein identity, standard normal (ID-1).** For `Z ~ N(0, 1)` and
`φ φ' : ℝ → ℝ` with `∀ x, HasDerivAt φ (φ' x) x`, if `x ↦ x * φ x` and `φ'` are integrable
against `N(0, 1)` then `E[Z φ(Z)] = E[φ'(Z)]`. -/
theorem integral_mul_eq_integral_deriv_std {φ φ' : ℝ → ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hint : Integrable (fun x => x * φ x) (gaussianReal 0 1))
    (hint' : Integrable φ' (gaussianReal 0 1)) :
    ∫ x, x * φ x ∂(gaussianReal 0 1) = ∫ x, φ' x ∂(gaussianReal 0 1) := by
  simpa using integral_sub_mul_eq_var_mul_integral_deriv (m := 0) (v := 1) hφ
    (by simpa using hint) hint'

/-- **Gaussian Stein identity for bounded test functions (ID-1, discharged).** For
`X ~ N(m, v)` and `φ φ' : ℝ → ℝ` with `∀ x, HasDerivAt φ (φ' x) x`, `φ` bounded and `φ'`
bounded, `E[(X - m) φ(X)] = v E[φ'(X)]`. No integrability hypothesis is needed: it follows from
finiteness of the first Gaussian moment and measurability of the derivative. -/
theorem integral_sub_mul_eq_of_bounded {m : ℝ} {v : ℝ≥0} {φ φ' : ℝ → ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hb : ∃ C, ∀ x, |φ x| ≤ C)
    (hb' : ∃ C, ∀ x, |φ' x| ≤ C) :
    ∫ x, (x - m) * φ x ∂(gaussianReal m v) = v * ∫ x, φ' x ∂(gaussianReal m v) := by
  have hc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hd : φ' = deriv φ := funext fun x => (hφ x).deriv.symm
  refine integral_sub_mul_eq_var_mul_integral_deriv hφ ?_ ?_
  · have hid : Integrable (fun x => x - m) (gaussianReal m v) :=
      (memLp_one_iff_integrable.1 (memLp_id_gaussianReal (μ := m) (v := v) 1)).sub
        (integrable_const m)
    obtain ⟨C, hC⟩ := hb
    have := hid.bdd_mul hc.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hC x)
    simpa [mul_comm] using this
  · obtain ⟨C, hC⟩ := hb'
    refine Integrable.of_bound ?_ C (ae_of_all _ fun x => by simpa using hC x)
    rw [hd]
    exact (measurable_deriv φ).aestronglyMeasurable

/-- **Gaussian Stein identity, differentiable bounded test functions (ID-1, discharged).**
For `X ~ N(m, v)` and `φ : ℝ → ℝ` differentiable with `φ` and `deriv φ` bounded,
`E[(X - m) φ(X)] = v E[φ'(X)]`. Continuity of `deriv φ` is not required. -/
theorem integral_sub_mul_eq_of_differentiable {m : ℝ} {v : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hb : ∃ C, ∀ x, |φ x| ≤ C)
    (hb' : ∃ C, ∀ x, |deriv φ x| ≤ C) :
    ∫ x, (x - m) * φ x ∂(gaussianReal m v) = v * ∫ x, deriv φ x ∂(gaussianReal m v) :=
  integral_sub_mul_eq_of_bounded (fun x => (hφ x).hasDerivAt) hb hb'

/-- **Gaussian Stein identity, compactly supported `C¹` test functions (ID-1,
discharged).** For `X ~ N(m, v)` and `φ : ℝ → ℝ` continuously differentiable with compact
support, `E[(X - m) φ(X)] = v E[φ'(X)]`. -/
theorem integral_sub_mul_eq_of_hasCompactSupport {m : ℝ} {v : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∫ x, (x - m) * φ x ∂(gaussianReal m v) = v * ∫ x, deriv φ x ∂(gaussianReal m v) := by
  refine integral_sub_mul_eq_of_differentiable (hφ.differentiable one_ne_zero) ?_ ?_
  · obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hs
    exact ⟨C, fun x => by simpa using hC x⟩
  · obtain ⟨C, hC⟩ := (hφ.continuous_deriv le_rfl).bounded_above_of_compact_support hs.deriv
    exact ⟨C, fun x => by simpa using hC x⟩

/-- **Standard-normal Stein identity, compactly supported `C¹` test functions.** For
`Z ~ N(0, 1)` and `φ : ℝ → ℝ` continuously differentiable with compact support,
`E[Z φ(Z)] = E[φ'(Z)]`. -/
theorem integral_mul_eq_integral_deriv_std_of_hasCompactSupport {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∫ x, x * φ x ∂(gaussianReal 0 1) = ∫ x, deriv φ x ∂(gaussianReal 0 1) := by
  simpa using integral_sub_mul_eq_of_hasCompactSupport (m := 0) (v := 1) hφ hs

/-- The line `t ↦ Fin.insertNth i t y` through `Fin (n + 1) → ℝ` (vary the `i`-th coordinate,
keep the others equal to `y`) has derivative `Pi.single i 1`, the `i`-th basis vector. -/
theorem hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Fin.insertNth i s y : Fin (n + 1) → ℝ)) (Pi.single i 1) t := by
  rw [hasDerivAt_pi]
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa using hasDerivAt_id' t
  · simpa [Pi.single_eq_of_ne (Fin.succAbove_ne i k)] using hasDerivAt_const t (y k)

/-- **`d`-dimensional standard Gaussian Stein identity.** Let `Z ~ N(0, I_d)`, realised as the
product measure `Measure.pi (fun _ => gaussianReal 0 1)` on `Fin d → ℝ`, and let
`φ : (Fin d → ℝ) → ℝ` be continuously differentiable with compact support. Then for every
coordinate `i`, `E[Zᵢ φ(Z)] = E[∂ᵢ φ(Z)]`, where `∂ᵢ φ = partialDeriv i φ`.
The proof applies the 1D identity in the `i`-th coordinate and Fubini over the others. -/
theorem integral_coord_mul_eq_integral_partialDeriv {d : ℕ} {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (i : Fin d) :
    ∫ z, z i * φ z ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, partialDeriv i φ z ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  set μ : Measure ℝ := gaussianReal 0 1
  set P : Measure (Fin (n + 1) → ℝ) := Measure.pi fun _ => μ
  set Q : Measure (Fin n → ℝ) := Measure.pi fun _ => μ
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).symm
  have fub : ∀ F : (Fin (n + 1) → ℝ) → ℝ, Integrable F P →
      ∫ z, F z ∂P = ∫ y, ∫ t, F (Fin.insertNth i t y) ∂μ ∂Q := by
    intro F hF
    rw [← he.integral_comp' F, integral_prod_symm]
    · rfl
    · exact (he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  have hdiff := hφ.differentiable one_ne_zero
  have hcont' : Continuous (partialDeriv i φ) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs' : HasCompactSupport (partialDeriv i φ) := hs.fderiv_apply ℝ (Pi.single i 1)
  have hint1 : Integrable (fun z : Fin (n + 1) → ℝ => z i * φ z) P :=
    ((continuous_apply i).mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left
  have hint2 : Integrable (partialDeriv i φ) P := hcont'.integrable_of_hasCompactSupport hs'
  rw [fub _ hint1, fub _ hint2]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hs
  obtain ⟨C', hC'⟩ := hcont'.bounded_above_of_compact_support hs'
  have hder : ∀ t, HasDerivAt (fun s => φ (Fin.insertNth i s y))
      (partialDeriv i φ (Fin.insertNth i t y)) t :=
    fun t => (hdiff _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i y t)
  have := integral_sub_mul_eq_of_bounded (m := 0) (v := 1) hder
    ⟨C, fun t => by simpa using hC _⟩ ⟨C', fun t => by simpa using hC' _⟩
  simpa using this

end FormalizeSampling.GaussianStein
