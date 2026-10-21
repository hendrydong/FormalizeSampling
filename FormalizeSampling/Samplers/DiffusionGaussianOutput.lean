module

public import FormalizeSampling.Samplers.DiffusionVarianceMain
public import FormalizeSampling.Foundations.GaussianLSIPi
public import FormalizeSampling.Samplers.DiffusionMain
public import FormalizeSampling.Flow.IdealVelocityStepPi
public import FormalizeSampling.Samplers.DiffusionODESmooth

/-!
# DDPM on Gaussian data: closed-form forward, reverse and output laws

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean` with Gaussian data `μ = N(0, v I)` on `Fin d → ℝ`
(`isoGauss d v`, `v > 0`), a time grid `0 = t_0 ≤ t_1 ≤ ⋯`, `α_k = e^{-(t_k - t_{k-1})}`,
`β_k = 1 - α_k²`.

* **Forward marginals.** `p_k = N(0, s_k I)` with `s_k = e^{-2t_k} v + 1 - e^{-2t_k}`
  (`gaussVar`, `fwdLaw_isoGauss`); `s_k = α_k² s_{k-1} + β_k` (`gaussVar_succ`).
* **Exact score.** The Lebesgue density of `p_k` (`fwdDensity`) is the Gaussian density, so the
  exact score is `∇ log p_k(y) = -y/s_k` (`exactScore_isoGauss`), and the score-parametrised
  reverse mean of the sampler is linear: `scoreMean t (exactScore μ t) k y = c_k y` with
  `c_k = α_k s_{k-1}/s_k` (`gaussGain`, `scoreMean_exactScore_isoGauss`).
* **Algorithm laws.** For any reverse means that are linear, `m_k(y) = c_k y` (`2 ≤ k ≤ N`), and
  any variances `σ_k²`, the sampler started at `q_N = N(0, I)` has Gaussian laws
  `q_k = N(0, w_k I)` (`algLaw_eq_isoGauss`) with `w_N = 1`, `w_{k-1} = c_k² w_k + σ_k²`
  (`algVar`, `algVar_self`, `algVar_of_lt`).
* **KL.** `KL(N(0, s I) ‖ N(0, w I)) = d (s/w - 1 - log(s/w))/2` (`klDiv_isoGauss`).

Headline (`klDiv_output_isoGauss_eq`): for Gaussian data, exact score, any variances `σ_k² ≥ 0`,
`KL(p_1 ‖ q_1) = d (s_1/w_1 - 1 - log(s_1/w_1))/2` with the explicit recursion for `w`.
The quantitative output upper bound (with initialisation term; `O(d h²)` for `v = 1`) and the
path/output separation are in `Samplers/DiffusionGaussianOutputRate.lean`.

## Main results

* `gaussVar`, `gaussVar_succ`, `gaussVar_pos`, `fwdLaw_isoGauss`.
* `algVar`, `algVar_self`, `algVar_of_lt`, `algVar_nonneg`, `algLaw_eq_isoGauss`.
* `gaussGain`, `fwdDensity_isoGauss`, `exactScore_isoGauss`, `scoreMean_exactScore_isoGauss`.
* `klDiv_isoGauss`, `klDiv_output_isoGauss_eq`.

## Not proved here

* Non-centred Gaussian data `N(m, v I)` (the mean recursion is affine; not formalised) and
  non-isotropic covariances.
* That the mean `c_k y` equals Mathlib's posterior mean `postMean` (it is proved equal to the
  score-parametrised mean with the exact score `∇ log p_k`, `DiffusionDiscretization.exactScore`,
  which is the quantity the DDPM theorems use).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionGaussian

open FormalizeSampling.Diffusion FormalizeSampling.OULangevinDecayPi
  FormalizeSampling.HeatKernelPi
open FormalizeSampling.DiffusionDiscretization (exactScore measurable_exactScore)
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi)

variable {d : ℕ}

/-- The centred isotropic Gaussian `N(0, v I) = ⊗ᵢ N(0, v)` on `Fin d → ℝ` (variance `v`,
truncated at `0` if `v < 0`). -/
noncomputable def isoGauss (d : ℕ) (v : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal

/-- `N(0, v I)` is a probability measure. -/
instance isProbabilityMeasure_isoGauss (v : ℝ) : IsProbabilityMeasure (isoGauss d v) := by
  unfold isoGauss; infer_instance

/-- `N(0, I)` is the algorithm's initial law: `isoGauss d 1 = stdGaussianPi d`. -/
theorem isoGauss_one : isoGauss d 1 = stdGaussianPi d := by
  simp [isoGauss, stdGaussianPi]

/-! ### Forward marginals -/

/-- The forward variance of Gaussian data `N(0, v I)` at time `t_k`:
`s_k = e^{-2t_k} v + 1 - e^{-2t_k}`. -/
noncomputable def gaussVar (v : ℝ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.exp (-2 * t k) * v + (1 - Real.exp (-2 * t k))

/-- `s_0 = v` when `t_0 = 0`. -/
theorem gaussVar_zero {v : ℝ} {t : ℕ → ℝ} (h0 : t 0 = 0) : gaussVar v t 0 = v := by
  simp [gaussVar, h0]

/-- The forward variance recursion: `s_{k+1} = α_{k+1}² s_k + β_{k+1}` (any grid). -/
theorem gaussVar_succ (v : ℝ) (t : ℕ → ℝ) (k : ℕ) :
    gaussVar v t (k + 1) = fwdScale t (k + 1) ^ 2 * gaussVar v t k + fwdVar t (k + 1) := by
  have e : Real.exp (-2 * t (k + 1)) = fwdScale t (k + 1) ^ 2 * Real.exp (-2 * t k) := by
    rw [fwdScale_sq, ← Real.exp_add, Nat.add_sub_cancel]; ring_nf
  rw [fwdVar, gaussVar, gaussVar, e]; ring

/-- `s_k > 0` when `v > 0` and `t_k ≥ 0` (a convex combination of `v` and `1`). -/
theorem gaussVar_pos {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} {k : ℕ} (htk : 0 ≤ t k) :
    0 < gaussVar v t k := by
  have h1 : Real.exp (-2 * t k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.exp_pos (-2 * t k)
  unfold gaussVar; nlinarith

/-- `s_k ≥ 0` when `v ≥ 0` and `t_k ≥ 0`. -/
theorem gaussVar_nonneg {v : ℝ} (hv : 0 ≤ v) {t : ℕ → ℝ} {k : ℕ} (htk : 0 ≤ t k) :
    0 ≤ gaussVar v t k := by
  have h1 : Real.exp (-2 * t k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.exp_pos (-2 * t k)
  unfold gaussVar; nlinarith

/-- `β_k ≥ 0` on a monotone grid. -/
theorem fwdVar_nonneg_of_monotone {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ) : 0 ≤ fwdVar t k := by
  rw [fwdVar, fwdScale_sq, sub_nonneg, Real.exp_le_one_iff]
  have := ht (Nat.sub_le k 1)
  linarith

/-- **Forward marginals of Gaussian data.** If `t_0 = 0`, `t` is monotone and `v ≥ 0`, then
`p_k = fwdLaw (N(0, v I)) t k = N(0, s_k I)` for every `k` (law equality). -/
theorem fwdLaw_isoGauss {v : ℝ} (hv : 0 ≤ v) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : Monotone t)
    (k : ℕ) : fwdLaw (isoGauss d v) t k = isoGauss d (gaussVar v t k) := by
  have htk : ∀ j, 0 ≤ t j := fun j => h0 ▸ ht (Nat.zero_le j)
  induction k with
  | zero => rw [fwdLaw_zero, gaussVar_zero h0]
  | succ k ih =>
    rw [fwdLaw_succ, ih, fwdKernel, ouKernelPi_eq_ouKernelVarPi, ouKernelVarPi_comp_eq]
    have hs := gaussVar_nonneg hv (htk k)
    have hmap := pi_gaussianReal_map_scalePi (d := d) (Real.exp (-1 * (t (k + 1) - t k))) hs 0
    simp only [Pi.zero_apply, mul_zero] at hmap
    rw [isoGauss, Nat.add_sub_cancel, hmap]
    have hβ : 0 ≤ 1 * (1 - Real.exp (-2 * 1 * (t (k + 1) - t k))) := by
      have := fwdVar_nonneg_of_monotone ht (k + 1)
      rw [fwdVar, fwdScale_sq, Nat.add_sub_cancel] at this
      linarith
    have e : Real.exp (-1 * (t (k + 1) - t k)) ^ 2 * gaussVar v t k +
        1 * (1 - Real.exp (-2 * 1 * (t (k + 1) - t k))) = gaussVar v t (k + 1) := by
      rw [gaussVar_succ, fwdVar, fwdScale_sq, Nat.add_sub_cancel, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [GaussianLSIPi.heatKernelPi_comp_pi_gaussianReal (by positivity) hβ, isoGauss, e]

/-! ### Exact score and the linear reverse mean -/

/-- The gain of the exact-score reverse mean for Gaussian data: `c_k = α_k s_{k-1}/s_k`. -/
noncomputable def gaussGain (v : ℝ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  fwdScale t k * gaussVar v t (k - 1) / gaussVar v t k

/-- The density of `N(0, s I)` is continuous. -/
theorem continuous_gaussianPDFPi (s : ℝ≥0) :
    Continuous (IdealVelocityStepPi.gaussianPDFPi (d := d) s) := by
  unfold IdealVelocityStepPi.gaussianPDFPi gaussianPDFReal
  fun_prop

/-- **The forward density of Gaussian data is the Gaussian density.** If `v > 0`, `t_0 = 0`, `t`
is strictly increasing and `k ≥ 1`, then `fwdDensity (N(0, v I)) t k = ∏ᵢ N(0, s_k)(yᵢ)`
pointwise (both are continuous Lebesgue densities of `p_k`). -/
theorem fwdDensity_isoGauss {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    fwdDensity (isoGauss d v) t k =
      IdealVelocityStepPi.gaussianPDFPi (gaussVar v t k).toNNReal := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have htk : 0 ≤ t (j + 1) := h0 ▸ ht.monotone (Nat.zero_le _)
  have hs0 : (gaussVar v t (j + 1)).toNNReal ≠ 0 := by
    simpa using gaussVar_pos hv htk
  have h1 := fwdLaw_eq_withDensity (isoGauss d v) (ht (Nat.lt_succ_self j))
  rw [fwdLaw_isoGauss hv.le h0 ht.monotone, isoGauss,
    pi_gaussianReal_eq_withDensity_prod (fun _ => 0) hs0] at h1
  have hc1 := DiffusionDiscretization.continuous_fwdDensity (isoGauss d v) t (j + 1)
  have hc2 := continuous_gaussianPDFPi (d := d) (gaussVar v t (j + 1)).toNNReal
  have hm1 : AEMeasurable (fun y => ENNReal.ofReal
      (gaussPiPDF (d := d) (fun _ => (0 : ℝ)) (gaussVar v t (j + 1)).toNNReal y)) volume :=
    (ENNReal.measurable_ofReal.comp (measurable_gaussPiPDF (d := d) _ _)).aemeasurable
  have hm2 : AEMeasurable (fun y => ENNReal.ofReal (fwdDensity (isoGauss d v) t (j + 1) y))
      volume := (ENNReal.measurable_ofReal.comp hc1.measurable).aemeasurable
  replace h1 := (withDensity_eq_iff_of_sigmaFinite hm1 hm2).1 h1
  refine ((hc1.ae_eq_iff_eq volume hc2).1 ?_)
  filter_upwards [h1] with y hy
  have hp : 0 ≤ fwdDensity (isoGauss d v) t (j + 1) y := by
    rw [fwdDensity, OUPosterior.piAffineDensity]
    exact integral_nonneg fun x => fwdTransDensity_nonneg t (j + 1) x y
  have hg : 0 ≤ gaussPiPDF (fun _ => (0 : ℝ)) (gaussVar v t (j + 1)).toNNReal y :=
    (gaussPiPDF_pos _ hs0 y).le
  rw [ENNReal.ofReal_eq_ofReal_iff hg hp] at hy
  rw [← hy]
  rfl

/-- **Exact score of Gaussian data.** Under the hypotheses of `fwdDensity_isoGauss`,
`∇ log p_k(y) = -y/s_k`: `exactScore (N(0, v I)) t k = fun y => (-s_k⁻¹) • y`. -/
theorem exactScore_isoGauss {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    exactScore (isoGauss d v) t k = fun y => (-(gaussVar v t k)⁻¹) • y := by
  have htk : 0 ≤ t k := h0 ▸ ht.monotone (Nat.zero_le _)
  have hpos := gaussVar_pos hv htk
  have hs0 : (gaussVar v t k).toNNReal ≠ 0 := by simpa using hpos
  rw [exactScore, fwdDensity_isoGauss hv h0 ht hk,
    IdealVelocityStepPi.score_gaussianPDFPi hs0, Real.coe_toNNReal _ hpos.le]

/-- **The exact-score DDPM mean is linear for Gaussian data.** Under the hypotheses of
`fwdDensity_isoGauss`, for `k ≥ 1`:
`scoreMean t (exactScore (N(0, v I)) t) k = scalePi c_k`, i.e.
`α_k⁻¹ (y + β_k ∇ log p_k(y)) = c_k y` with `c_k = α_k s_{k-1}/s_k`. -/
theorem scoreMean_exactScore_isoGauss {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    scoreMean t (exactScore (isoGauss d v) t) k = scalePi (gaussGain v t k) := by
  have htk : 0 ≤ t k := h0 ▸ ht.monotone (Nat.zero_le _)
  have hpos := gaussVar_pos hv htk
  have hα := fwdScale_pos t k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hrec := gaussVar_succ v t j
  funext y i
  rw [scoreMean, exactScore_isoGauss hv h0 ht hk, scalePi, gaussGain, Nat.add_sub_cancel]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  rw [hrec]
  ring

/-! ### Algorithm laws for linear reverse means -/

/-- Auxiliary: the variance after `j` reverse steps from `w_N = 1`. -/
noncomputable def algVarAux (c : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => c (N - j) ^ 2 * algVarAux c σ2 N j + σ2 (N - j)

/-- The variance `w_k` of the algorithm's law `q_k = N(0, w_k I)` for linear reverse means
`m_k(y) = c_k y` and variances `σ_k²`: `w_N = 1`, `w_{k-1} = c_k² w_k + σ_k²`
(`algVar_self`, `algVar_of_lt`). -/
noncomputable def algVar (c : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) (N k : ℕ) : ℝ :=
  algVarAux c σ2 N (N - k)

/-- `w_N = 1`. -/
theorem algVar_self (c : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) (N : ℕ) : algVar c σ2 N N = 1 := by
  simp [algVar, algVarAux]

/-- The backward recursion: for `k < N`, `w_k = c_{k+1}² w_{k+1} + σ_{k+1}²`. -/
theorem algVar_of_lt (c : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) {N k : ℕ} (hk : k < N) :
    algVar c σ2 N k = c (k + 1) ^ 2 * algVar c σ2 N (k + 1) + σ2 (k + 1) := by
  have h : N - k = (N - (k + 1)) + 1 := by omega
  rw [algVar, h, algVarAux, algVar, show N - (N - (k + 1)) = k + 1 by omega]

/-- `w_k ≥ 0`. -/
theorem algVar_nonneg (c : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) (N k : ℕ) : 0 ≤ algVar c σ2 N k := by
  unfold algVar
  induction N - k with
  | zero => simp [algVarAux]
  | succ j ih => simp only [algVarAux]; positivity

/-- **Algorithm laws for linear reverse means.** If the reverse means are linear,
`m_k = scalePi c_k` (`m_k(y) = c_k y`) for `2 ≤ k ≤ N`, then for every variance sequence `σ2`
and `1 ≤ k ≤ N`, the algorithm's law is `q_k = algLaw σ2 m hm N k = N(0, w_k I)` (law equality),
`w_k = algVar c σ2 N k`. -/
theorem algLaw_eq_isoGauss (c : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N : ℕ} (hlin : ∀ k, 2 ≤ k → k ≤ N → m k = scalePi (c k))
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    algLaw σ2 m hm N k = isoGauss d (algVar c σ2 N k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = N - j := ⟨N - k, by omega⟩
  have hj : j ≤ N - 1 := by omega
  clear hk1 hkN
  induction j with
  | zero => rw [Nat.sub_zero, algLaw_self, algVar_self, isoGauss_one]
  | succ j ih =>
    have hlt : N - (j + 1) < N := by omega
    have he : N - (j + 1) + 1 = N - j := by omega
    rw [algLaw_of_lt σ2 m hm hlt, he, ih (by omega), algKernel, gaussKernelPi,
      DiffusionPath.comp_comap_eq_comp_map, hlin (N - j) (by omega) (by omega), isoGauss,
      pi_gaussianReal_map_scalePi _ (algVar_nonneg c σ2 N (N - j))]
    simp only [mul_zero]
    have h := GaussianLSIPi.heatKernelPi_comp_pi_gaussianReal (d := d)
      (v := c (N - j) ^ 2 * algVar c σ2 N (N - j)) (t := (σ2 (N - j) : ℝ))
      (by have := algVar_nonneg c σ2 N (N - j); positivity) (NNReal.coe_nonneg _)
    rw [Real.toNNReal_coe] at h
    rw [h, isoGauss, algVar_of_lt c σ2 hlt, he]

/-! ### KL between centred isotropic Gaussians -/

/-- **KL between centred isotropic Gaussians.** For `s, w > 0`,
`KL(N(0, s I) ‖ N(0, w I)) = d (s/w - 1 - log(s/w))/2` (Mathlib's `klDiv`, in `ℝ≥0∞`). -/
theorem klDiv_isoGauss {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    klDiv (isoGauss d s) (isoGauss d w) =
      ENNReal.ofReal (d * ((s / w - 1 - Real.log (s / w)) / 2)) := by
  have hs0 : s.toNNReal ≠ 0 := by simpa using hs
  have hw0 : w.toNNReal ≠ 0 := by simpa using hw
  have hx : 0 ≤ (s / w - 1 - Real.log (s / w)) / 2 := by
    have := Real.log_le_sub_one_of_pos (div_pos hs hw); linarith
  rw [isoGauss, isoGauss, GaussianIncrement.klDiv_pi_pi]
  simp_rw [DiscreteGaussianFlow.klDiv_gaussianReal_gaussianReal 0 0 hs0 hw0,
    Real.coe_toNNReal _ hs.le, Real.coe_toNNReal _ hw.le]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 2
  ring

/-- **Exact output KL of the exact-score DDPM sampler on Gaussian data.** Let `v > 0`,
`t_0 = 0`, `t` strictly increasing, `N ≥ 1`, and let the sampler use the exact score
(`scoreMean t (exactScore μ t)`, `μ = N(0, v I)`) with arbitrary variances `σ_k²` such that
`w_1 > 0` (e.g. some `σ_k² > 0`, or `N = 1`). Then the output is `q_1 = N(0, w_1 I)`,
`w_1 = algVar c σ2 N 1` with `c_k = α_k s_{k-1}/s_k`, and
`KL(p_1 ‖ q_1) = d (s_1/w_1 - 1 - log(s_1/w_1))/2`. -/
theorem klDiv_output_isoGauss_eq {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (σ2 : ℕ → ℝ≥0) {N : ℕ} (hN : 1 ≤ N)
    (hw : 0 < algVar (gaussGain v t) σ2 N 1) :
    algLaw σ2 (scoreMean t (exactScore (isoGauss d v) t))
        (measurable_scoreMean t (measurable_exactScore _ t)) N 1 =
        isoGauss d (algVar (gaussGain v t) σ2 N 1) ∧
      klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw σ2 (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) =
      ENNReal.ofReal (d * ((gaussVar v t 1 / algVar (gaussGain v t) σ2 N 1 - 1 -
        Real.log (gaussVar v t 1 / algVar (gaussGain v t) σ2 N 1)) / 2)) := by
  have hq := algLaw_eq_isoGauss (d := d) (gaussGain v t) σ2 _
    (measurable_scoreMean t (measurable_exactScore _ t))
    (fun k hk _ => scoreMean_exactScore_isoGauss hv h0 ht (by omega)) le_rfl hN
  refine ⟨hq, ?_⟩
  have hs := gaussVar_pos hv (t := t) (k := 1) (h0 ▸ ht.monotone (Nat.zero_le 1))
  rw [hq, fwdLaw_isoGauss hv.le h0 ht.monotone, klDiv_isoGauss hs hw]

end FormalizeSampling.DiffusionGaussian
