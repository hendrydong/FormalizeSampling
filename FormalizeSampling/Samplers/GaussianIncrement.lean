module

public import FormalizeSampling.Kernels.ErrorDecomposition
public import FormalizeSampling.Kernels.GaussianKernels
public import FormalizeSampling.Foundations.GaussianKL
public import FormalizeSampling.Foundations.KLChainRule
public import FormalizeSampling.Foundations.Pinsker

/-!
# Score-oracle error in total variation: Gaussian mean shifts and Euler–Maruyama chains

Composable certificates that turn a **score (drift) estimation error** into a **distributional
error** in total variation (TV), for one-dimensional Gaussian-increment samplers on `ℝ`.

## Conventions

* `tvSup` is `FormalizeSampling.TotalVariation.tvSup`, normalised as `sup_A |μ(A) - ν(A)|`
  (so `tvSup ≤ 1` for probability measures). `klDiv μ ν = KL(μ ‖ ν)` is Mathlib's
  `InformationTheory.klDiv`, valued in `ℝ≥0∞`.
* Mathlib's `gaussianReal m v` is `N(m, v)` with **variance** `v : ℝ≥0`.
* The Euler–Maruyama (EM) kernel for `dX = s(X) dt + √2 dW` with step `h : ℝ≥0` and a
  measurable drift (score) field `s : ℝ → ℝ` is `emKernel h s hs x = N(x + h s(x), 2h)`:
  `X' = X + h s(X) + √(2h) Z`, `Z ∼ N(0, 1)`. With `s = (log π)'` this is the unadjusted Langevin
  algorithm (ULA) for `π`. Measurability of `s` is an explicit argument `hs` of `emKernel`,
  because a kernel must be measurable in its input.
* `κ ∘ₘ μ` is the law of one chain step from `μ` (`Measure.bind`).

## Main results

* (a) `tvSup_gaussianReal_le`: for `v ≠ 0`,
  `tvSup (N(m₁, v)) (N(m₂, v)) ≤ |m₁ - m₂| / √(2πv)`. This is the **sharp first-order**
  constant: the true value is `2Φ(|m₁ - m₂| / (2√v)) - 1`, whose derivative at `0` is
  `1/√(2πv)` (the exact value is not formalised). Proof: a Hahn set `S = (-∞, (m₁+m₂)/2]`
  gives `tvSup = μ₁(S) - μ₂(S)` (Scheffé; only `≤` is proved), which is the `N(m₁, v)`-mass of an
  interval of length `|m₁ - m₂|`, bounded by length times the peak density `1/√(2πv)`.
* (b) `klDiv_gaussianReal_gaussianReal` (in `Foundations/GaussianKL.lean`):
  `KL(N(m₁, v) ‖ N(m₂, v)) = (m₁ - m₂)² / (2v)`
  (generalising `GaussianFlowVsOU.klDiv_gaussianReal_stdGaussian` in the mean, at equal variances).
  TV is then bounded by the general Pinsker inequality `Pinsker.tvSup_le_sqrt_klDiv`.
* (c) `emKernel`, `isMarkovKernel_emKernel`, `map_em_update` (the kernel is the law of
  `X + h s(X) + √(2h) Z` for independent `Z ∼ N(0, 1)`) and the one-step oracle error
  `tvSup_emKernel_le`: `tvSup (emKernel h s x) (emKernel h ŝ x) ≤ √h |s x - ŝ x| / (2√π)`,
  and `klDiv_emKernel`: `KL = h (s x - ŝ x)² / 4` (both for every `h`, including `h = 0`).
* (d) TV telescoping (KR-1 applied to Gaussian increments). For time-dependent measurable fields `s
  k, ŝ k`, steps `h k`, the exact
  score chain `μ (k+1) = emKernel (h k) (s k) ∘ₘ μ k` and the estimated chain
  `ν (k+1) = emKernel (h k) (ŝ k) ∘ₘ ν k` from probability laws:
  - `tvSup_emChain_le_sum_integral`: errors averaged under the **algorithm's** law `ν k`,
    `tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} √(h k)/(2√π) ∫ |s k - ŝ k| d(ν k)`;
  - `tvSup_emChain_le_sum`: uniform errors `|s k x - ŝ k x| ≤ ε k`;
  - `tvSup_emChain_le_sum_sqrt_integral_sq`: the score-matching (`L²`) form
    `… + ∑_{k<n} √(h k / (4π)) √(∫ (s k - ŝ k)² d(ν k))`, via
    `integral_abs_le_sqrt_integral_sq` (Jensen / Cauchy–Schwarz).
* (e) GI-1, KL telescoping with one Pinsker step at the end:
  - `klDiv_emChain_le_sum`:
    `KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ h k (s k - ŝ k)² / 4 d(ν k)`;
  - `tvSup_emChain_le_sqrt_klDiv_sum`: `tvSup (ν n) (μ n) ≤ √(B / 2)` for that budget `B`;
  - `tvSup_emChain_le_sqrt_sum_integral_sq`:
    `tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0) / 2 + ∑_{k<n} (h k / 8) ∫ (s k - ŝ k)² d(ν k))`.
* KR-1 with Euler–Maruyama oracle kernels (the three-chain separation of
  `Kernels/ErrorDecomposition.lean` with `D k = emKernel (h k) (s k)`,
  `I k = emKernel (h k) (ŝ k)`, in the namespace `ErrorDecomposition`):
  `tvSup_le_disc_add_emOracle`, `tvSup_le_disc_add_emOracle_sq_exact` and
  `tvSup_le_three_chain_em`.

Registry: GI-1 (score-error theorem for Gaussian-increment chains); KR-1 for the TV-telescoped
forms. The discretisation gap to a continuous-time diffusion is kept abstract in
`FormalizeSampling/Kernels/ErrorDecomposition.lean`.

## Relation to the papers

The rdMC / RS-DMC / RTK / SPS analyses propagate score error in **KL** (Girsanov on path space,
or the KL chain rule for kernels) and apply Pinsker **once** at the end, e.g. rdMC Eq. (15)/(19)
and SPS Lemma B.5 `TV(p̂_K, p_K) ≤ √(½ Σ_k δ_k)`. The rdMC grid-level identity
`KL ≤ (η/4)|v - v'|²` for its exponential-integrator step has the same `(step/4)·|Δ drift|²`
form as the EM identity `klDiv_emKernel` here.
Section (e) proves exactly this route in general (`tvSup_emChain_le_sqrt_klDiv_sum`).
Section (d) instead **telescopes TV** (`ErrorPropagation.tvSup_chain_le_sum_integral_approx`)
with a per-step Gaussian TV bound. That route is valid but looser: with per-step KL errors
`δ_k = h (s - ŝ)²/4`, it gives `∑_k √(δ_k / π)` (`≤ ∑_k √(δ_k / 2)`) instead of `√(½ ∑_k δ_k)`,
i.e. up to a factor `√n` worse for `n` comparable steps; its advantage is that it needs no
finite initial KL. No paper theorem is formalised here.

## Not proved here

* The exact TV value `2Φ(|Δ|/(2√v)) - 1` of a Gaussian mean shift, and Gaussians with
  different variances.
* Non-isotropic noise; dimension `d > 1` is in `Samplers/GaussianIncrementPi.lean`.
* Any statement about SDE solutions: the EM chain is compared with the exact-score EM chain, not
  with the continuous-time diffusion (that discretisation gap is kept abstract in
  `ErrorDecomposition.lean`).
* No bound on the score error itself (finite-sample, importance-sampling or learned estimators,
  oracle hierarchies) is derived; it enters as `|s k - ŝ k|` or its `L¹`/`L²` norm.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory InformationTheory Finset Set
open scoped NNReal ENNReal

namespace FormalizeSampling
namespace GaussianIncrement

open TotalVariation ErrorPropagation

/-! ### Hahn-set bound for TV -/

section Hahn

variable {α : Type*} [MeasurableSpace α]

/-- If `ν ≤ μ` on the subsets of a measurable `S` and `μ ≤ ν` on the subsets of `Sᶜ`, then for
every measurable `A`, `μ(A) - ν(A) ≤ μ(S) - ν(S)` (finite measures). -/
private lemma measureReal_sub_le_of_hahn {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {S : Set α} (hS : MeasurableSet S)
    (hle : ∀ B, MeasurableSet B → B ⊆ S → ν B ≤ μ B)
    (hge : ∀ B, MeasurableSet B → B ⊆ Sᶜ → μ B ≤ ν B) {A : Set α} (hA : MeasurableSet A) :
    μ.real A - ν.real A ≤ μ.real S - ν.real S := by
  have h1 := measureReal_inter_add_sdiff (μ := μ) (s := A) hS
  have h2 := measureReal_inter_add_sdiff (μ := ν) (s := A) hS
  have h3 := measureReal_inter_add_sdiff (μ := μ) (s := S) hA
  have h4 := measureReal_inter_add_sdiff (μ := ν) (s := S) hA
  have h5 : μ.real (A \ S) ≤ ν.real (A \ S) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hge _ (hA.diff hS) fun _ hx => hx.2)
  have h6 : ν.real (S \ A) ≤ μ.real (S \ A) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hle _ (hS.diff hA) Set.sdiff_subset)
  rw [inter_comm] at h1 h2
  linarith

/-- **Scheffé-type bound.** For probability measures `μ ν` and a measurable `S` such that
`ν ≤ μ` on subsets of `S` and `μ ≤ ν` on subsets of `Sᶜ` (a Hahn set of `μ - ν`),
`tvSup μ ν ≤ μ(S) - ν(S)`. -/
private lemma tvSup_le_of_hahn {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {S : Set α} (hS : MeasurableSet S)
    (hle : ∀ B, MeasurableSet B → B ⊆ S → ν B ≤ μ B)
    (hge : ∀ B, MeasurableSet B → B ⊆ Sᶜ → μ B ≤ ν B) :
    tvSup μ ν ≤ μ.real S - ν.real S := by
  refine tvSup_le_of_forall fun A hA => abs_sub_le_iff.2
    ⟨measureReal_sub_le_of_hahn hS hle hge hA, ?_⟩
  have h := measureReal_sub_le_of_hahn (μ := ν) (ν := μ) hS.compl hge
    (fun B hB hBS => hle B hB (by simpa using hBS)) hA
  rw [measureReal_compl hS, measureReal_compl hS] at h
  simp only [probReal_univ] at h
  linarith

end Hahn

/-! ### (a) Gaussian mean shift in TV -/

/-- Pointwise density comparison: if `(x - m₁)² ≤ (x - m₂)²` then `N(m₂, v)(x) ≤ N(m₁, v)(x)`
for the Gaussian densities (any variance `v`). -/
private lemma gaussianPDFReal_le_of_sq_le {m₁ m₂ x : ℝ} (v : ℝ≥0)
    (h : (x - m₁) ^ 2 ≤ (x - m₂) ^ 2) : gaussianPDFReal m₂ v x ≤ gaussianPDFReal m₁ v x := by
  unfold gaussianPDFReal
  gcongr

/-- The Gaussian density is bounded by its peak value: `N(m, v)(x) ≤ 1/√(2πv)`. -/
private lemma gaussianPDFReal_le_peak (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- The `N(m, v)`-mass of an interval `(a, b]` with `a ≤ b` is at most `(b - a)/√(2πv)`. -/
private lemma measureReal_gaussianReal_Ioc_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ}
    (hab : a ≤ b) : (gaussianReal m v).real (Ioc a b) ≤ (b - a) / Real.sqrt (2 * Real.pi * v) := by
  have hK : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (sub_nonneg.2 hab) (Real.sqrt_nonneg _)) ?_
  rw [gaussianReal_apply m hv]
  calc ∫⁻ x in Ioc a b, gaussianPDF m v x
      ≤ ∫⁻ _ in Ioc a b, ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ :=
        setLIntegral_mono measurable_const fun x _ =>
          ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_peak m v x)
    _ = ENNReal.ofReal ((b - a) / Real.sqrt (2 * Real.pi * v)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hK, div_eq_inv_mul]

/-- The ordered case `m₁ ≤ m₂` of `tvSup_gaussianReal_le`. -/
private lemma tvSup_gaussianReal_le_of_le {m₁ m₂ : ℝ} (hm : m₁ ≤ m₂) {v : ℝ≥0} (hv : v ≠ 0) :
    tvSup (gaussianReal m₁ v) (gaussianReal m₂ v) ≤ (m₂ - m₁) / Real.sqrt (2 * Real.pi * v) := by
  set c := (m₁ + m₂) / 2 with hc
  have hS : MeasurableSet (Iic c) := measurableSet_Iic
  have hle : ∀ B, MeasurableSet B → B ⊆ Iic c →
      gaussianReal m₂ v B ≤ gaussianReal m₁ v B := by
    intro B _ hB
    rw [gaussianReal_apply m₂ hv, gaussianReal_apply m₁ hv]
    refine setLIntegral_mono (measurable_gaussianPDF _ _) fun x hx => ?_
    refine ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_of_sq_le v ?_)
    have hx' : x ≤ c := hB hx
    nlinarith
  have hge : ∀ B, MeasurableSet B → B ⊆ (Iic c)ᶜ →
      gaussianReal m₁ v B ≤ gaussianReal m₂ v B := by
    intro B _ hB
    rw [gaussianReal_apply m₂ hv, gaussianReal_apply m₁ hv]
    refine setLIntegral_mono (measurable_gaussianPDF _ _) fun x hx => ?_
    refine ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_of_sq_le v ?_)
    have hx' : c < x := not_le.1 (hB hx)
    nlinarith
  refine (tvSup_le_of_hahn hS hle hge).trans ?_
  -- `N(m₂, v)` is the shift of `N(m₁, v)` by `m₂ - m₁`.
  have hshift : gaussianReal m₂ v = (gaussianReal m₁ v).map (· + (m₂ - m₁)) := by
    rw [gaussianReal_map_add_const, add_sub_cancel]
  have h2 : (gaussianReal m₂ v).real (Iic c) = (gaussianReal m₁ v).real (Iic (c - (m₂ - m₁))) := by
    rw [hshift, measureReal_def, Measure.map_apply (measurable_add_const _) hS,
      preimage_add_const_Iic, measureReal_def]
  have hsub : Iic (c - (m₂ - m₁)) ⊆ Iic c := Iic_subset_Iic.2 (by linarith)
  rw [h2, ← measureReal_sdiff hsub measurableSet_Iic, Iic_sdiff_Iic]
  convert measureReal_gaussianReal_Ioc_le m₁ hv (by linarith : c - (m₂ - m₁) ≤ c) using 2
  ring

/-- **(a) Gaussian mean shift in TV (sharp first-order constant).** For a variance `v ≠ 0` and
means `m₁ m₂`,
`tvSup (N(m₁, v)) (N(m₂, v)) ≤ |m₁ - m₂| / √(2πv)`.
The constant is the peak density `1/√(2πv)`, which is the exact first-order behaviour of
`2Φ(|m₁ - m₂|/(2√v)) - 1`. The hypothesis `v ≠ 0` is necessary: for `v = 0` both laws are Dirac
masses and the left side is `1` for `m₁ ≠ m₂`. -/
theorem tvSup_gaussianReal_le (m₁ m₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    tvSup (gaussianReal m₁ v) (gaussianReal m₂ v) ≤ |m₁ - m₂| / Real.sqrt (2 * Real.pi * v) := by
  rcases le_total m₁ m₂ with hm | hm
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hm)]
    exact tvSup_gaussianReal_le_of_le hm hv
  · rw [abs_of_nonneg (sub_nonneg.2 hm), tvSup_comm]
    exact tvSup_gaussianReal_le_of_le hm hv

/-! ### (c) The Euler–Maruyama / ULA kernel and its one-step oracle error -/

/-- The **Euler–Maruyama (EM) kernel** for `dX = s(X) dt + √2 dW` with step `h : ℝ≥0` and a
measurable drift (score) field `s : ℝ → ℝ`:
`emKernel h s hs x = N(x + h s(x), 2h)`, the law of `x + h s(x) + √(2h) Z` with `Z ∼ N(0, 1)`
(variance `2h`). For `s = (log π)'` this is one step of ULA for `π`. For `h = 0` it is the
identity kernel `x ↦ δₓ`. -/
noncomputable def emKernel (h : ℝ≥0) (s : ℝ → ℝ) (hs : Measurable s) : Kernel ℝ ℝ where
  toFun x := gaussianReal (x + h * s x) (2 * h)
  measurable' := (OU.heatKernel (2 * h)).measurable.comp (measurable_id.add (hs.const_mul _))

/-- Evaluation of the EM kernel: `emKernel h s hs x = N(x + h s(x), 2h)`. -/
theorem emKernel_apply (h : ℝ≥0) {s : ℝ → ℝ} (hs : Measurable s) (x : ℝ) :
    emKernel h s hs x = gaussianReal (x + h * s x) (2 * h) := rfl

/-- The EM kernel is a Markov kernel (every `N(m, w)` is a probability measure), for every step
`h` and measurable field `s`. -/
theorem isMarkovKernel_emKernel (h : ℝ≥0) {s : ℝ → ℝ} (hs : Measurable s) :
    IsMarkovKernel (emKernel h s hs) :=
  ⟨fun x => by rw [emKernel_apply]; infer_instance⟩

/-- **The EM kernel is the law of the EM update.** Let `X`, `Z` be independent measurable real
random variables on a probability space with `Z ∼ N(0, 1)`. For a step `h : ℝ≥0` and a measurable
field `s`, the law of the Euler–Maruyama update `X + h s(X) + √(2h) Z` is
`emKernel h s hs ∘ₘ Law(X)` (one-time law equality; no SDE is involved). -/
theorem map_em_update {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZlaw : P.map Z = gaussianReal 0 1) (h : ℝ≥0) {s : ℝ → ℝ} (hs : Measurable s) :
    P.map (fun ω => X ω + h * s (X ω) + Real.sqrt (2 * h) * Z ω) =
      emKernel h s hs ∘ₘ P.map X := by
  have hg : Measurable (fun x : ℝ => x + h * s x) := measurable_id.add (hs.const_mul _)
  have hY : Measurable (fun ω => X ω + h * s (X ω)) := hg.comp hX
  have hYZ : IndepFun (fun ω => X ω + h * s (X ω)) Z P := hXZ.comp hg measurable_id
  have key := OU.map_affine_add_noise hY hZ hYZ hZlaw 1 (2 * h)
  simp only [one_mul, NNReal.coe_mul, NNReal.coe_ofNat] at key
  rw [key]
  ext t ht
  rw [Measure.bind_apply ht (Kernel.aemeasurable _), Measure.bind_apply ht,
    show (fun ω => X ω + (h : ℝ) * s (X ω)) = (fun x => x + (h : ℝ) * s x) ∘ X from rfl,
    ← Measure.map_map hg hX, lintegral_map _ hg]
  · rfl
  · exact (Measure.measurable_coe ht).comp (OU.heatKernel (2 * h)).measurable
  · exact ((OU.heatKernel (2 * h)).measurable).aemeasurable

/-- Arithmetic of the EM constants: for `h > 0`,
`|h a| / √(2π (2h)) = √h |a| / (2√π)`. -/
private lemma em_const_eq {h : ℝ≥0} (hh : h ≠ 0) (a : ℝ) :
    |(h : ℝ) * a| / Real.sqrt (2 * Real.pi * ((2 * h : ℝ≥0) : ℝ)) =
      Real.sqrt h * |a| / (2 * Real.sqrt Real.pi) := by
  have hh' : 0 < (h : ℝ) := by positivity
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh'
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h4 : Real.sqrt (2 * Real.pi * ((2 * h : ℝ≥0) : ℝ)) =
      2 * Real.sqrt Real.pi * Real.sqrt h := by
    rw [NNReal.coe_mul, NNReal.coe_ofNat]
    rw [show 2 * Real.pi * (2 * (h : ℝ)) = (2 * Real.sqrt Real.pi * Real.sqrt h) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hh'.le]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [h4, abs_mul, abs_of_pos hh']
  field_simp
  rw [Real.sq_sqrt hh'.le]
  ring

/-- **(c) One-step oracle error of the EM kernel in TV.** For every step `h : ℝ≥0`, measurable
fields `s ŝ` (exact and estimated scores) and every state `x`,
`tvSup (emKernel h s x) (emKernel h ŝ x) ≤ √h |s(x) - ŝ(x)| / (2√π)`.
(Both kernels have variance `2h`; their means differ by `h (s x - ŝ x)`; apply (a). For `h = 0`
both are `δₓ` and both sides vanish.) -/
theorem tvSup_emKernel_le (h : ℝ≥0) {s ŝ : ℝ → ℝ} (hs : Measurable s) (hŝ : Measurable ŝ)
    (x : ℝ) :
    tvSup (emKernel h s hs x) (emKernel h ŝ hŝ x) ≤
      Real.sqrt h * |s x - ŝ x| / (2 * Real.sqrt Real.pi) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [emKernel_apply, tvSup_self]
  have h2 : (2 * h : ℝ≥0) ≠ 0 := mul_ne_zero two_ne_zero hh
  rw [emKernel_apply, emKernel_apply]
  refine (tvSup_gaussianReal_le _ _ h2).trans (le_of_eq ?_)
  rw [← em_const_eq hh]
  congr 2
  ring

/-- **(c) One-step oracle error of the EM kernel in KL.** For every step `h : ℝ≥0`, measurable
fields `s ŝ` and state `x`, `KL(emKernel h s x ‖ emKernel h ŝ x) = h (s(x) - ŝ(x))² / 4`
(Mathlib's `klDiv`). This is the frozen-drift Girsanov integrand `(1/4) ∫_0^h |s - ŝ|² dt`. -/
theorem klDiv_emKernel (h : ℝ≥0) {s ŝ : ℝ → ℝ} (hs : Measurable s) (hŝ : Measurable ŝ)
    (x : ℝ) :
    klDiv (emKernel h s hs x) (emKernel h ŝ hŝ x) =
      ENNReal.ofReal (h * (s x - ŝ x) ^ 2 / 4) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [emKernel_apply]
  have hh' : 0 < (h : ℝ) := by positivity
  rw [emKernel_apply, emKernel_apply,
    klDiv_gaussianReal_gaussianReal _ _ (mul_ne_zero two_ne_zero hh)]
  congr 1
  rw [NNReal.coe_mul, NNReal.coe_ofNat]
  field_simp
  ring

/-! ### (d) TV-telescoped score-error certificates for EM chains -/

/-- **Jensen / Cauchy–Schwarz.** For a probability measure `μ` and an a.e.-strongly measurable
`f` with `f²` integrable, `∫ |f| dμ ≤ √(∫ f² dμ)`. -/
theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, |f x| ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hL2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf).2 hf2
  have habs : MemLp (fun x => |f x|) 2 μ := hL2.abs
  have hvar := variance_eq_sub habs
  have hnn := variance_nonneg (fun x => |f x|) μ
  have hsq : ∫ x, ((fun x => |f x|) ^ 2) x ∂μ = ∫ x, f x ^ 2 ∂μ := by
    simp [sq_abs]
  rw [hsq] at hvar
  refine (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).2 ?_
  linarith

/-- The EM per-step constant: for `h : ℝ≥0`, `√h / (2√π) = √(h / (4π))`. -/
theorem sqrt_div_two_mul_sqrt_pi (h : ℝ≥0) :
    Real.sqrt h / (2 * Real.sqrt Real.pi) = Real.sqrt (h / (4 * Real.pi)) := by
  rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 4 * Real.pi),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

variable {h : ℕ → ℝ≥0} {s ŝ : ℕ → ℝ → ℝ} {hs : ∀ k, Measurable (s k)}
  {hŝ : ∀ k, Measurable (ŝ k)} {μ ν : ℕ → Measure ℝ}

/-- **TV telescoping, law-averaged under the algorithm's law.** Let `h k : ℝ≥0` be steps, `s k`
exact
and `ŝ k` estimated measurable score fields, `μ` the exact-score EM chain
`μ (k+1) = emKernel (h k) (s k) ∘ₘ μ k` and `ν` the estimated-score EM chain
`ν (k+1) = emKernel (h k) (ŝ k) ∘ₘ ν k`, started from probability laws `μ 0`, `ν 0`. If the score
error `s k - ŝ k` is integrable under `ν k` (the **algorithm's** law at step `k`), then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} √(h k)/(2√π) ∫ |s k - ŝ k| d(ν k)`. -/
theorem tvSup_emChain_le_sum_integral [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k)
    (hint : ∀ k, Integrable (fun x => s k x - ŝ k x) (ν k)) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n,
      Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * ∫ x, |s k x - ŝ k x| ∂(ν k) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have key := tvSup_chain_le_sum_integral_approx hμ hν
    (e := fun k x => Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * |s k x - ŝ k x|)
    (fun k => (hint k).abs.const_mul _)
    (fun k => Filter.Eventually.of_forall fun x => by
      simpa [mul_div_right_comm] using tvSup_emKernel_le (h k) (hs k) (hŝ k) x) n
  rw [tvSup_comm (ν n), tvSup_comm (ν 0)]
  simpa only [integral_const_mul] using key

/-- **TV telescoping, uniform score error.** Same chains as `tvSup_emChain_le_sum_integral`; if
`|s k x - ŝ k x| ≤ ε k` for every `k` and every `x`, then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} √(h k)/(2√π) ε k`. -/
theorem tvSup_emChain_le_sum [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) {ε : ℕ → ℝ}
    (hε : ∀ k x, |s k x - ŝ k x| ≤ ε k) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n,
      Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * ε k := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have key := tvSup_chain_le_sum hμ hν
    (ε := fun k => Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * ε k)
    (fun k x => (tvSup_emKernel_le (h k) (hs k) (hŝ k) x).trans (by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left (hε k x) (by positivity))) n
  rw [tvSup_comm (ν n), tvSup_comm (ν 0)]
  exact key

/-- **TV telescoping, score-matching (`L²`) form under the algorithm's law.** Same chains as
`tvSup_emChain_le_sum_integral`; if the squared score error `(s k - ŝ k)²` is integrable under
the algorithm's law `ν k`, then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} √(h k / (4π)) √(∫ (s k - ŝ k)² d(ν k))`. -/
theorem tvSup_emChain_le_sum_sqrt_integral_sq [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k)
    (hint : ∀ k, Integrable (fun x => (s k x - ŝ k x) ^ 2) (ν k)) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n,
      Real.sqrt (h k / (4 * Real.pi)) * Real.sqrt (∫ x, (s k x - ŝ k x) ^ 2 ∂(ν k)) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have hprob := isProbabilityMeasure_of_comp_succ hν
  have hm : ∀ k, AEStronglyMeasurable (fun x => s k x - ŝ k x) (ν k) :=
    fun k => ((hs k).sub (hŝ k)).aestronglyMeasurable
  have hint1 : ∀ k, Integrable (fun x => s k x - ŝ k x) (ν k) := fun k =>
    haveI := hprob k
    ((memLp_two_iff_integrable_sq (hm k)).2 (hint k)).integrable one_le_two
  refine (tvSup_emChain_le_sum_integral hμ hν hint1 n).trans
    (add_le_add_right (sum_le_sum fun k _ => ?_) _)
  have := hprob k
  rw [← sqrt_div_two_mul_sqrt_pi]
  exact mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq (hm k) (hint k))
    (by positivity)

/-! ### (e) GI-1: KL telescoping and a single Pinsker step -/

/-- **GI-1 (1D), KL form: score-error theorem for Gaussian-increment chains.** Same chains as
`tvSup_emChain_le_sum_integral` (exact drifts `s k`, estimated drifts `ŝ k`, steps `h k`, laws
`μ k` of the exact chain and `ν k` of the algorithm, both started from probability laws). Then
`KL(ν n ‖ μ n) ≤ KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ x, h k (s k x - ŝ k x)² / 4 ∂(ν k)`.
Direction: KL of the algorithm's law from the exact chain's law; the drift errors are averaged
under the **algorithm's** laws `ν k`. Exchanging the chains (the per-step formula is symmetric)
bounds `KL(μ n ‖ ν n)` with errors averaged under the exact chain's laws `μ k`. No
integrability is needed: both sides live in `ℝ≥0∞`. -/
theorem klDiv_emChain_le_sum [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) (n : ℕ) :
    klDiv (ν n) (μ n) ≤ klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ∫⁻ x, ENNReal.ofReal (h k * (s k x - ŝ k x) ^ 2 / 4) ∂(ν k) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsFiniteMeasure (μ k) := fun k =>
    haveI := isProbabilityMeasure_of_comp_succ hμ k; inferInstance
  have : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    haveI := isProbabilityMeasure_of_comp_succ hν k; inferInstance
  refine (KL.klDiv_chain_le_sum (fun k => emKernel (h k) (s k) (hs k))
    (fun k => emKernel (h k) (ŝ k) (hŝ k)) μ ν hμ hν n).trans_eq ?_
  congr 1
  refine sum_congr rfl fun k _ => lintegral_congr fun x => ?_
  rw [klDiv_emKernel, ← neg_sub, neg_sq]

/-- **GI-1 (1D), TV form: one Pinsker step at the end.** Same chains as `klDiv_emChain_le_sum`.
If the KL budget `B = KL(ν 0 ‖ μ 0) + ∑_{k<n} ∫⁻ h k (s k - ŝ k)² / 4 d(ν k)` is finite, then
`tvSup (ν n) (μ n) ≤ √(B / 2)`. Compared with `tvSup_emChain_le_sum_sqrt_integral_sq`, which
telescopes TV and pays one square root per step, the per-step errors are summed **inside** a
single square root (no `√n` loss). -/
theorem tvSup_emChain_le_sqrt_klDiv_sum [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) (n : ℕ)
    (hB : klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ∫⁻ x, ENNReal.ofReal (h k * (s k x - ŝ k x) ^ 2 / 4) ∂(ν k) ≠ ∞) :
    tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0) +
      ∑ k ∈ range n, ∫⁻ x, ENNReal.ofReal (h k * (s k x - ŝ k x) ^ 2 / 4) ∂(ν k)).toReal / 2) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  have hKL := klDiv_emChain_le_sum hμ hν n
  refine (Pinsker.tvSup_le_sqrt_klDiv (ne_top_of_le_ne_top hB hKL)).trans
    (Real.sqrt_le_sqrt ?_)
  gcongr

/-- **GI-1 (1D), TV form with `L²` score errors.** Same chains as `klDiv_emChain_le_sum`. If
`KL(ν 0 ‖ μ 0) < ∞` and each squared drift error `(s k - ŝ k)²` is integrable under the
algorithm's law `ν k`, then
`tvSup (ν n) (μ n) ≤ √(KL(ν 0 ‖ μ 0) / 2 + ∑_{k<n} (h k / 8) ∫ (s k - ŝ k)² d(ν k))`. -/
theorem tvSup_emChain_le_sqrt_sum_integral_sq [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) (n : ℕ)
    (hKL0 : klDiv (ν 0) (μ 0) ≠ ∞)
    (hint : ∀ k, Integrable (fun x => (s k x - ŝ k x) ^ 2) (ν k)) :
    tvSup (ν n) (μ n) ≤ Real.sqrt ((klDiv (ν 0) (μ 0)).toReal / 2 +
      ∑ k ∈ range n, h k / 8 * ∫ x, (s k x - ŝ k x) ^ 2 ∂(ν k)) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hν n
  refine (Pinsker.tvSup_le_sqrt_of_klDiv_le_add_sum (n := n) hKL0 (fun k x => by positivity)
    (fun k => (hint k).const_mul (h k / 4 : ℝ))
    ((klDiv_emChain_le_sum hμ hν n).trans_eq ?_)).trans_eq ?_
  · congr 1
    refine sum_congr rfl fun k _ => lintegral_congr fun x => ?_
    congr 1; ring
  · congr 2
    refine sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; ring

end GaussianIncrement

namespace ErrorDecomposition

open TotalVariation ErrorPropagation GaussianIncrement

/-! ### KR-1: instantiation of the oracle part with Euler–Maruyama kernels -/

section EM

variable {K : ℕ → Kernel ℝ ℝ} [∀ k, IsMarkovKernel (K k)] {h : ℕ → ℝ≥0}
  {s ŝ : ℕ → ℝ → ℝ} {hs : ∀ k, Measurable (s k)} {hŝ : ∀ k, Measurable (ŝ k)}
  {μ ν : ℕ → Measure ℝ}

/-- **KR-1 + GI-1, EM oracle, uniform discretisation error.** Let `K k` be arbitrary exact
Markov kernels on `ℝ` (e.g. one-step transitions of a diffusion, not constructed here), the ideal
discretisation `D k = emKernel (h k) (s k)` (EM with the exact score `s k`) and the implementation
`I k = emKernel (h k) (ŝ k)` (EM with the estimated score `ŝ k`); `μ (k+1) = K k ∘ₘ μ k` (exact
chain) and `ν (k+1) = I k ∘ₘ ν k` (algorithm) from probability laws. If
`tvSup (emKernel (h k) (s k) x) (K k x) ≤ disc k` for all `k`, `x` and `s k - ŝ k` is integrable
under the algorithm's law `ν k`, then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} disc k
  + ∑_{k<n} √(h k)/(2√π) ∫ |s k - ŝ k| d(ν k)`. -/
theorem tvSup_le_disc_add_emOracle [IsProbabilityMeasure (μ 0)] [IsProbabilityMeasure (ν 0)]
    (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) {disc : ℕ → ℝ}
    (hdisc : ∀ k x, tvSup (emKernel (h k) (s k) (hs k) x) (K k x) ≤ disc k)
    (hint : ∀ k, Integrable (fun x => s k x - ŝ k x) (ν k)) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n, disc k + ∑ k ∈ range n,
      Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * ∫ x, |s k x - ŝ k x| ∂(ν k) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have hprob := isProbabilityMeasure_of_comp_succ hν
  have key := tvSup_le_sum_integral_disc_add_oracle (D := fun k => emKernel (h k) (s k) (hs k))
    hμ hν (d := fun k _ => disc k)
    (o := fun k x => Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * |s k x - ŝ k x|)
    (fun k => haveI := hprob k; integrable_const _) (fun k => (hint k).abs.const_mul _)
    (fun k => Filter.Eventually.of_forall fun x => hdisc k x)
    (fun k => Filter.Eventually.of_forall fun x => by
      rw [tvSup_comm]
      exact (tvSup_emKernel_le (h k) (hs k) (hŝ k) x).trans_eq (by ring)) n
  refine key.trans (le_of_eq ?_)
  congr 1
  · congr 1
    exact sum_congr rfl fun k _ => by have := hprob k; simp
  · exact sum_congr rfl fun k _ => integral_const_mul _ _

/-- **KR-1 + GI-1, EM oracle, all errors under the exact chain's law (score-matching form).**
Same setting as `tvSup_le_disc_add_emOracle`. Let `d k` be integrable under `μ k` (the **exact**
chain's law) with `tvSup (emKernel (h k) (s k) x) (K k x) ≤ d k x` for `μ k`-a.e. `x`, and let the
squared score error `(s k - ŝ k)²` be integrable under `μ k`. Then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑_{k<n} ∫ d k d(μ k)
  + ∑_{k<n} √(h k / (4π)) √(∫ (s k - ŝ k)² d(μ k))`;
the last sum is the usual score-matching loss along the exact process, turned into TV. -/
theorem tvSup_le_disc_add_emOracle_sq_exact [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) {d : ℕ → ℝ → ℝ}
    (hd : ∀ k, Integrable (d k) (μ k))
    (hdisc : ∀ k, ∀ᵐ x ∂(μ k), tvSup (emKernel (h k) (s k) (hs k) x) (K k x) ≤ d k x)
    (hint : ∀ k, Integrable (fun x => (s k x - ŝ k x) ^ 2) (μ k)) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (μ 0) + ∑ k ∈ range n, ∫ x, d k x ∂(μ k) +
      ∑ k ∈ range n,
        Real.sqrt (h k / (4 * Real.pi)) * Real.sqrt (∫ x, (s k x - ŝ k x) ^ 2 ∂(μ k)) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have hprob := isProbabilityMeasure_of_comp_succ hμ
  have hm : ∀ k, AEStronglyMeasurable (fun x => s k x - ŝ k x) (μ k) :=
    fun k => ((hs k).sub (hŝ k)).aestronglyMeasurable
  have hint1 : ∀ k, Integrable (fun x => s k x - ŝ k x) (μ k) := fun k =>
    haveI := hprob k
    ((memLp_two_iff_integrable_sq (hm k)).2 (hint k)).integrable one_le_two
  have key := tvSup_le_sum_integral_disc_add_oracle_exact
    (D := fun k => emKernel (h k) (s k) (hs k)) hμ hν (d := d)
    (o := fun k x => Real.sqrt (h k) / (2 * Real.sqrt Real.pi) * |s k x - ŝ k x|)
    hd (fun k => (hint1 k).abs.const_mul _) hdisc
    (fun k => Filter.Eventually.of_forall fun x => by
      rw [tvSup_comm]
      exact (tvSup_emKernel_le (h k) (hs k) (hŝ k) x).trans_eq (by ring)) n
  refine key.trans (add_le_add_right (sum_le_sum fun k _ => ?_) _)
  have := hprob k
  rw [integral_const_mul, ← sqrt_div_two_mul_sqrt_pi]
  exact mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq (hm k) (hint k))
    (by positivity)

/-- **KR-1 + GI-1, EM three-chain form.** Kernels `K k` (exact, arbitrary Markov),
`emKernel (h k) (s k)` (ideal EM, exact score) and `emKernel (h k) (ŝ k)` (implemented EM,
estimated score), with chains `μ (k+1) = K k ∘ₘ μ k`, `δ (k+1) = emKernel (h k) (s k) ∘ₘ δ k`,
`ν (k+1) = emKernel (h k) (ŝ k) ∘ₘ ν k` from probability laws. Let `d k` be integrable under
`δ k` (the **ideal EM** chain's law) with `tvSup (emKernel (h k) (s k) x) (K k x) ≤ d k x` for
`δ k`-a.e. `x`, and `(s k - ŝ k)²` integrable under `ν k` (the **algorithm's** law). Then
`tvSup (ν n) (μ n) ≤ tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0) + ∑_{k<n} ∫ d k d(δ k)
  + ∑_{k<n} √(h k / (4π)) √(∫ (s k - ŝ k)² d(ν k))`. -/
theorem tvSup_le_three_chain_em {δ : ℕ → Measure ℝ} [IsProbabilityMeasure (μ 0)]
    [IsProbabilityMeasure (δ 0)] [IsProbabilityMeasure (ν 0)] (hμ : ∀ k, μ (k + 1) = K k ∘ₘ μ k)
    (hδ : ∀ k, δ (k + 1) = emKernel (h k) (s k) (hs k) ∘ₘ δ k)
    (hν : ∀ k, ν (k + 1) = emKernel (h k) (ŝ k) (hŝ k) ∘ₘ ν k) {d : ℕ → ℝ → ℝ}
    (hd : ∀ k, Integrable (d k) (δ k))
    (hdisc : ∀ k, ∀ᵐ x ∂(δ k), tvSup (emKernel (h k) (s k) (hs k) x) (K k x) ≤ d k x)
    (hint : ∀ k, Integrable (fun x => (s k x - ŝ k x) ^ 2) (ν k)) (n : ℕ) :
    tvSup (ν n) (μ n) ≤ tvSup (ν 0) (δ 0) + tvSup (δ 0) (μ 0) +
      ∑ k ∈ range n, ∫ x, d k x ∂(δ k) + ∑ k ∈ range n,
        Real.sqrt (h k / (4 * Real.pi)) * Real.sqrt (∫ x, (s k x - ŝ k x) ^ 2 ∂(ν k)) := by
  have : ∀ k, IsMarkovKernel (emKernel (h k) (s k) (hs k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have := isProbabilityMeasure_of_comp_succ hμ n
  have := isProbabilityMeasure_of_comp_succ hδ n
  have : ∀ k, IsMarkovKernel (emKernel (h k) (ŝ k) (hŝ k)) :=
    fun k => isMarkovKernel_emKernel _ _
  have := isProbabilityMeasure_of_comp_succ hν n
  have h1 := tvSup_emChain_le_sum_sqrt_integral_sq hδ hν hint n
  have h2 := tvSup_chain_le_sum_integral_approx hμ hδ hd
    (fun k => (hdisc k).mono fun x hx => by rwa [tvSup_comm]) n
  rw [tvSup_comm (μ n), tvSup_comm (μ 0)] at h2
  have h3 := tvSup_triangle (ν n) (δ n) (μ n)
  linarith

end EM

end ErrorDecomposition
end FormalizeSampling
