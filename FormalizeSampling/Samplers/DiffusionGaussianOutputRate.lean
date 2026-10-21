module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import FormalizeSampling.Samplers.DiffusionGaussianOutput

/-!
# Gaussian output-KL upper bound with initialisation and a path-KL lower bound

Status: **Verified**.

Setting of `Samplers/DiffusionGaussianOutput.lean`: data `μ = N(0, v I)` on `Fin d → ℝ`, grid
`0 = t_0 < t_1 < ⋯ < t_N`, step sizes `h_k = t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`), exact score,
reverse variance `σ_k² = β_k/α_k² = e^{2h_k} - 1` (`ddpmVar`). The forward marginal is
`p_k = N(0, s_k I)`, the sampler's laws are `q_k = N(0, w_k I)` with `w_N = 1`,
`w_{k-1} = c_k² w_k + σ_k²`, `c_k = α_k s_{k-1}/s_k`.

**Exact error recursion.** With `φ_k = e^{-2t_k}/s_k²`, `G_k = e^{-2t_k}/s_k = 1/(v + e^{2t_k} - 1)`
and the exact posterior variance `τ_k² = s_{k-1}β_k/s_k`, for **any** reverse variances
(`errWeight_mul_sub_eq_gen`, telescoped in `errWeight_telescope`):
`φ_k (w_k - s_k) = φ_{k+1} (w_{k+1} - s_{k+1}) + φ_k (σ_{k+1}² - τ_{k+1}²)`, so
`φ_k (w_k - s_k) = φ_N (1 - s_N) + ∑_{j=k}^{N-1} φ_j (σ_{j+1}² - τ_{j+1}²)`. For `σ² = β/α²`
the local term is `σ_{k+1}² (G_k - G_{k+1})/s_k` (`errWeight_mul_ddpm_sub`; one-step form
`errWeight_mul_sub_eq`, telescoped form `errWeight_ddpm_telescope`), and
`G_k - G_{k+1} = β_{k+1} e^{-2t_k}/(s_k s_{k+1}) ≥ 0`. The local error `σ² - τ² = β²/(α² s)`
of one step is `O(h²)`, but it is weighted by the telescoping increments `G_k - G_{k+1}` (`O(h)`
each, summing to `≤ G_1`), so the discretisation contribution `w_1 - s_1 - ι` is `O(h)`, with
the initialisation term `ι` specified below.

**Bounds.** If `1 ≤ K s_j` for `1 ≤ j < N` (`errWeight_bounds`, `algVar_ddpm_sub_gaussVar_mem`):
`ι ≤ w_1 - s_1 ≤ ι + (e^{2h} - 1) K s_1`, with the initialisation term
`ι = e^{-2(t_N - t_1)} (1 - s_N) s_1²/s_N²`. For `v ≤ 1` (`K = 1/s_1`,
`algVar_ddpm_sub_gaussVar_le`): `0 ≤ w_1 - s_1 ≤ (1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1`.

**Generic KL step** (any reverse variances `σ²`, `klDiv_output_isoGauss_le_of_mem`). If
`s_1 - b ≤ w_1 ≤ s_1 + a` with `b < s_1`, then `KL(p_1 ‖ q_1) ≤ d (a²/s_1² + b²/(s_1 - b)²)/4`.

**Output KL** (`klDiv_output_isoGauss_ddpm_le`, `v ≤ 1`; the generic step with `b = 0`):
`KL(p_1 ‖ q_1) ≤ d ((1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1)² / (4 s_1²)`
for **any** grid with maximal step `h` (not only uniform). For `v = 1`, initialisation is
exact and this gives `O(d h²)`. For `v < 1`, the displayed initialisation allowance decays
exponentially in `t_N` but remains nonzero as `h → 0` at fixed `t_1`, `t_N` and `v`.

**Path KL** (`klDiv_truePath_isoGauss_ddpm_ge`, from DF-5/DF-6
`DiffusionPath.klDiv_truePath_ddpm_ge_uniform`; the second moment of `N(0, v I)` is
`d v ≤ d`): on the uniform grid `t_k = t_1 + (k - 1) h`,
`KL(truePath ‖ algPath) ≥ d (t_N - t_1) h/(1 + h)`.

**Separation** (`gaussian_output_path_separation`): both bounds hold for the same sampler.
For `v = 1`, `d ≥ 1` and a fixed positive interval `t_N - t_1`, their ratio gives
`KL(output)/KL(path) = O(h)`. For `v < 1`, the initialisation allowance must also be controlled
relative to `h`; these inequalities do not give that ratio limit at a fixed horizon.

## Main results

* `ddpmVar_coe`, `fwdVar_div_fwdScale_sq`, `gaussPot_sub_succ`, `gaussPot_succ_le`,
  `sum_gaussPot_sub`.
* `errWeight_mul_sub_eq_gen`, `errWeight_telescope`: the exact error identity for any `σ²`.
* `errWeight_mul_ddpm_sub`, `errWeight_mul_sub_eq`, `errWeight_ddpm_telescope`: its form for
  `σ² = β/α²`.
* `errWeight_bounds`, `algVar_ddpm_sub_gaussVar_mem`, `algVar_ddpm_sub_gaussVar_le`.
* `log_le_half_sub_inv`, `sub_one_sub_log_div_le`: `x - 1 - log x ≤ (1 - x)²/(2x)` for
  `0 < x ≤ 1`; `sub_one_sub_log_le_sq_div_two`, `sub_one_sub_log_div_le_two_sided`.
* `klDiv_output_isoGauss_le_of_mem` (any `σ²`), and `klDiv_output_isoGauss_ddpm_le`: the
  output upper bound retaining initialisation.
* `sq_div_two_add_le_expGap`, `two_mul_div_one_add_le`, `secondMoment_isoGauss`,
  `klDiv_truePath_isoGauss_ddpm_ge`: the path lower bound `d (T - t_1) h/(1 + h)`.
* `gaussian_output_path_separation`: the headline.

## Scope and companion modules

* `DiffusionGaussianOutputExt` adds an output lower bound, giving `Θ(d h²)` for `v = 1`
  on a uniform grid over a fixed positive interval.
* `DiffusionGaussianOutputExtLarge` treats `v ≥ 1` with an explicit initialisation condition;
  `DiffusionGaussianOutputExtBeta` treats `σ² = β`.
* A path-KL upper bound of order `h`, non-centred or non-isotropic Gaussian output rates,
  and an `O(h²)` output theorem for non-Gaussian data are not proved here. The non-Gaussian
  examples in `showcase/ddpm_rate.py` are numerical illustrations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionGaussian

open FormalizeSampling.Diffusion
  FormalizeSampling.DiffusionDiscretization FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-! ### The exact one-step error identity -/

/-- The error weight `φ_k = e^{-2t_k}/s_k²`; `φ_k c_{k+1}² = φ_{k+1}`. -/
noncomputable def errWeight (v : ℝ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.exp (-2 * t k) / gaussVar v t k ^ 2

/-- The potential `G_k = e^{-2t_k}/s_k = 1/(v + e^{2t_k} - 1)` whose increments weight the local
errors. -/
noncomputable def gaussPot (v : ℝ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.exp (-2 * t k) / gaussVar v t k

/-- `e^{-2t_{k+1}} = α_{k+1}² e^{-2t_k}`. -/
theorem exp_neg_two_succ (t : ℕ → ℝ) (k : ℕ) :
    Real.exp (-2 * t (k + 1)) = fwdScale t (k + 1) ^ 2 * Real.exp (-2 * t k) := by
  rw [fwdScale_sq, ← Real.exp_add, Nat.add_sub_cancel]; ring_nf

/-- `β_k/α_k² = e^{2(t_k - t_{k-1})} - 1`. -/
theorem fwdVar_div_fwdScale_sq (t : ℕ → ℝ) (k : ℕ) :
    fwdVar t k / fwdScale t k ^ 2 = Real.exp (2 * (t k - t (k - 1))) - 1 := by
  rw [fwdVar, fwdScale_sq, sub_div, div_self (Real.exp_pos _).ne', one_div, ← Real.exp_neg]
  ring_nf

/-- On a monotone grid the DDPM variance is `σ_k² = β_k/α_k²` as a real number. -/
theorem ddpmVar_coe {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ) :
    (ddpmVar t k : ℝ) = fwdVar t k / fwdScale t k ^ 2 :=
  Real.coe_toNNReal _ (div_nonneg (fwdVar_nonneg_of_monotone ht k) (sq_nonneg _))

/-- `G_k - G_{k+1} = β_{k+1} e^{-2t_k}/(s_k s_{k+1})` (for `s_k, s_{k+1} > 0`). -/
theorem gaussPot_sub_succ (v : ℝ) (t : ℕ → ℝ) (k : ℕ) (hs : 0 < gaussVar v t k)
    (hs' : 0 < gaussVar v t (k + 1)) :
    gaussPot v t k - gaussPot v t (k + 1) =
      fwdVar t (k + 1) * Real.exp (-2 * t k) / (gaussVar v t k * gaussVar v t (k + 1)) := by
  have hrec := gaussVar_succ v t k
  rw [gaussPot, gaussPot, exp_neg_two_succ, fwdVar]
  rw [fwdVar] at hrec
  set s' := gaussVar v t (k + 1)
  set a := fwdScale t (k + 1)
  set s := gaussVar v t k
  field_simp
  rw [hrec]
  ring

/-- `G_{k+1} ≤ G_k` on a monotone grid (for `s_k, s_{k+1} > 0`). -/
theorem gaussPot_succ_le (v : ℝ) {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ)
    (hs : 0 < gaussVar v t k) (hs' : 0 < gaussVar v t (k + 1)) :
    gaussPot v t (k + 1) ≤ gaussPot v t k := by
  have := gaussPot_sub_succ v t k hs hs'
  have := fwdVar_nonneg_of_monotone ht (k + 1)
  have : 0 ≤ fwdVar t (k + 1) * Real.exp (-2 * t k) / (gaussVar v t k * gaussVar v t (k + 1)) :=
    by positivity
  linarith

/-- `∑_{j=k}^{N-1} (G_j - G_{j+1}) = G_k - G_N` for `k ≤ N`. -/
theorem sum_gaussPot_sub (v : ℝ) (t : ℕ → ℝ) {N k : ℕ} (hkN : k ≤ N) :
    ∑ j ∈ Ico k N, (gaussPot v t j - gaussPot v t (j + 1)) = gaussPot v t k - gaussPot v t N := by
  rw [← neg_sub, ← Finset.sum_Ico_sub _ hkN, ← Finset.sum_neg_distrib]
  simp

/-- **Exact one-step error identity (any variances `σ²`).** For `k < N` and `s_k, s_{k+1} > 0`,
with `w = algVar c σ² N` for the exact-score gain `c_k = α_k s_{k-1}/s_k`:
`φ_k (w_k - s_k) = φ_{k+1} (w_{k+1} - s_{k+1}) + φ_k (σ_{k+1}² - τ_{k+1}²)`, where
`τ_{k+1}² = s_k β_{k+1}/s_{k+1}` is the exact posterior variance. -/
theorem errWeight_mul_sub_eq_gen (v : ℝ) (t : ℕ → ℝ) (σ2 : ℕ → ℝ≥0) {N k : ℕ} (hk : k < N)
    (hs : 0 < gaussVar v t k) (hs' : 0 < gaussVar v t (k + 1)) :
    errWeight v t k * (algVar (gaussGain v t) σ2 N k - gaussVar v t k) =
      errWeight v t (k + 1) * (algVar (gaussGain v t) σ2 N (k + 1) - gaussVar v t (k + 1)) +
      errWeight v t k *
        (σ2 (k + 1) - gaussVar v t k * fwdVar t (k + 1) / gaussVar v t (k + 1)) := by
  have hα := fwdScale_pos t (k + 1)
  rw [algVar_of_lt _ _ hk, gaussGain, Nat.add_sub_cancel]
  set w := algVar (gaussGain v t) σ2 N (k + 1)
  rw [errWeight, errWeight, exp_neg_two_succ]
  have hrec := gaussVar_succ v t k
  rw [fwdVar] at hrec ⊢
  set s' := gaussVar v t (k + 1)
  set a := fwdScale t (k + 1)
  set s := gaussVar v t k
  field_simp
  rw [hrec]
  ring

/-- **Telescoped error identity (any variances `σ²`).** For `v > 0`, `t_0 = 0`, `t` monotone
and `k ≤ N`:
`φ_k (w_k - s_k) = φ_N (1 - s_N) + ∑_{j=k}^{N-1} φ_j (σ_{j+1}² - s_j β_{j+1}/s_{j+1})`. -/
theorem errWeight_telescope {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : Monotone t) (σ2 : ℕ → ℝ≥0) {N k : ℕ} (hkN : k ≤ N) :
    errWeight v t k * (algVar (gaussGain v t) σ2 N k - gaussVar v t k) =
      errWeight v t N * (1 - gaussVar v t N) +
      ∑ j ∈ Ico k N, errWeight v t j *
        (σ2 (j + 1) - gaussVar v t j * fwdVar t (j + 1) / gaussVar v t (j + 1)) := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht (Nat.zero_le j))
  induction hkN using Nat.decreasingInduction with
  | self => simp [algVar_self]
  | of_succ k hk ih =>
    rw [errWeight_mul_sub_eq_gen v t σ2 hk (hpos _) (hpos _), ih,
      Finset.sum_eq_sum_Ico_succ_bot hk]
    ring

/-- **Local error for `σ² = β/α²`.** On a monotone grid, for `s_k, s_{k+1} > 0`:
`φ_k (β_{k+1}/α_{k+1}² - s_k β_{k+1}/s_{k+1}) = (β_{k+1}/α_{k+1}²) (G_k - G_{k+1})/s_k`. -/
theorem errWeight_mul_ddpm_sub (v : ℝ) {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ)
    (hs : 0 < gaussVar v t k) (hs' : 0 < gaussVar v t (k + 1)) :
    errWeight v t k *
        (ddpmVar t (k + 1) - gaussVar v t k * fwdVar t (k + 1) / gaussVar v t (k + 1)) =
      fwdVar t (k + 1) / fwdScale t (k + 1) ^ 2 * (gaussPot v t k - gaussPot v t (k + 1)) /
        gaussVar v t k := by
  have hα := fwdScale_pos t (k + 1)
  rw [ddpmVar_coe ht, gaussPot_sub_succ v t k hs hs', errWeight]
  have hrec := gaussVar_succ v t k
  have e := exp_neg_two_succ t k
  field_simp
  rw [hrec]
  ring_nf

/-- **Exact one-step error identity.** For a monotone grid, `k < N` and `s_k, s_{k+1} > 0`,
with `w = algVar c σ² N` for the exact-score gain `c_k = α_k s_{k-1}/s_k` and `σ² = β/α²`
(`ddpmVar`):
`φ_k (w_k - s_k) = φ_{k+1} (w_{k+1} - s_{k+1}) + (β_{k+1}/α_{k+1}²) (G_k - G_{k+1})/s_k`. -/
theorem errWeight_mul_sub_eq (v : ℝ) {t : ℕ → ℝ} (ht : Monotone t) {N k : ℕ} (hk : k < N)
    (hs : 0 < gaussVar v t k) (hs' : 0 < gaussVar v t (k + 1)) :
    errWeight v t k * (algVar (gaussGain v t) (ddpmVar t) N k - gaussVar v t k) =
      errWeight v t (k + 1) * (algVar (gaussGain v t) (ddpmVar t) N (k + 1) -
        gaussVar v t (k + 1)) +
      fwdVar t (k + 1) / fwdScale t (k + 1) ^ 2 * (gaussPot v t k - gaussPot v t (k + 1)) /
        gaussVar v t k := by
  rw [errWeight_mul_sub_eq_gen v t _ hk hs hs', errWeight_mul_ddpm_sub v ht k hs hs']

/-- **Telescoped error identity for `σ² = β/α²`.** For `v > 0`, `t_0 = 0`, `t` monotone and
`k ≤ N`: `φ_k (w_k - s_k) = φ_N (1 - s_N) + ∑_{j=k}^{N-1} (e^{2h_{j+1}} - 1) (G_j - G_{j+1})/s_j`,
`h_{j+1} = t_{j+1} - t_j`. -/
theorem errWeight_ddpm_telescope {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : Monotone t) {N k : ℕ} (hkN : k ≤ N) :
    errWeight v t k * (algVar (gaussGain v t) (ddpmVar t) N k - gaussVar v t k) =
      errWeight v t N * (1 - gaussVar v t N) +
      ∑ j ∈ Ico k N, (Real.exp (2 * (t (j + 1) - t j)) - 1) / gaussVar v t j *
        (gaussPot v t j - gaussPot v t (j + 1)) := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht (Nat.zero_le j))
  rw [errWeight_telescope hv h0 ht _ hkN]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [errWeight_mul_ddpm_sub v ht j (hpos _) (hpos _), fwdVar_div_fwdScale_sq,
    Nat.add_sub_cancel]
  ring

/-! ### Two-sided bounds on the accumulated error -/

/-- **Accumulated error, weighted form.** Let `v > 0`, `t_0 = 0`, `t` strictly increasing, all
steps `t_k - t_{k-1} ≤ h` for `2 ≤ k ≤ N`, and `1 ≤ K s_j` for `1 ≤ j < N`. Then for
`1 ≤ k ≤ N` (with `w = algVar c (β/α²) N`, exact gain `c`):
`φ_N (1 - s_N) ≤ φ_k (w_k - s_k) ≤ φ_N (1 - s_N) + (e^{2h} - 1) K (G_k - G_N)`. -/
theorem errWeight_bounds {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {N : ℕ} {h K : ℝ} (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h)
    (hK : ∀ j, 1 ≤ j → j < N → 1 ≤ K * gaussVar v t j) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    errWeight v t N * (1 - gaussVar v t N) ≤
        errWeight v t k * (algVar (gaussGain v t) (ddpmVar t) N k - gaussVar v t k) ∧
      errWeight v t k * (algVar (gaussGain v t) (ddpmVar t) N k - gaussVar v t k) ≤
        errWeight v t N * (1 - gaussVar v t N) +
          (Real.exp (2 * h) - 1) * K * (gaussPot v t k - gaussPot v t N) := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  rw [errWeight_ddpm_telescope hv h0 ht.monotone hkN, ← sum_gaussPot_sub v t hkN, Finset.mul_sum]
  have hterm : ∀ j ∈ Ico k N, 0 ≤ (Real.exp (2 * (t (j + 1) - t j)) - 1) / gaussVar v t j ∧
      (Real.exp (2 * (t (j + 1) - t j)) - 1) / gaussVar v t j ≤ (Real.exp (2 * h) - 1) * K := by
    intro j hj
    simp only [mem_Ico] at hj
    have h1 : 0 ≤ Real.exp (2 * (t (j + 1) - t j)) - 1 := by
      linarith [Real.one_le_exp (by linarith [ht.monotone (Nat.le_succ j)] :
        0 ≤ 2 * (t (j + 1) - t j))]
    have h2 : Real.exp (2 * (t (j + 1) - t j)) - 1 ≤ Real.exp (2 * h) - 1 := by
      have := hstep (j + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at this
      linarith [Real.exp_le_exp.2 (by linarith : 2 * (t (j + 1) - t j) ≤ 2 * h)]
    have h3 : (gaussVar v t j)⁻¹ ≤ K := by
      rw [inv_le_iff_one_le_mul₀ (hpos j)]; linarith [hK j (by omega) hj.2]
    rw [div_eq_mul_inv]
    exact ⟨by have := hpos j; positivity,
      mul_le_mul h2 h3 (inv_nonneg.2 (hpos j).le) (h1.trans h2)⟩
  have hdG : ∀ j, 0 ≤ gaussPot v t j - gaussPot v t (j + 1) := fun j =>
    sub_nonneg.2 (gaussPot_succ_le v ht.monotone j (hpos _) (hpos _))
  constructor
  · linarith [Finset.sum_nonneg fun j hj => mul_nonneg (hterm j hj).1 (hdG j)]
  · linarith [Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hterm j hj).2 (hdG j)]

/-- **Accumulated error of the output variance (any `v > 0`).** Under the hypotheses of
`errWeight_bounds`, with `N ≥ 1`, `h ≥ 0` and `K ≥ 0`:
`ι ≤ w_1 - s_1 ≤ ι + (e^{2h} - 1) K s_1`, where
`ι = e^{-2t_N} (1 - s_N) s_1² / (s_N² e^{-2t_1})` is the initialisation term
(`1 - s_N = (1 - v) e^{-2t_N}`). -/
theorem algVar_ddpm_sub_gaussVar_mem {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h K : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h) (hK0 : 0 ≤ K)
    (hK : ∀ j, 1 ≤ j → j < N → 1 ≤ K * gaussVar v t j) :
    Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) ≤
        algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 ∧
      algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 ≤
        Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
          (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) +
        (Real.exp (2 * h) - 1) * K * gaussVar v t 1 := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  obtain ⟨b1, b2⟩ := errWeight_bounds hv h0 ht hstep hK le_rfl hN
  have hφ : 0 < errWeight v t 1 := by unfold errWeight; have := hpos 1; positivity
  have hGN : 0 ≤ gaussPot v t N := by unfold gaussPot; have := hpos N; positivity
  have hη : 0 ≤ (Real.exp (2 * h) - 1) * K :=
    mul_nonneg (by linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * h)]) hK0
  set e := algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1
  have hι : Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
      (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) =
      errWeight v t N * (1 - gaussVar v t N) / errWeight v t 1 := by
    unfold errWeight
    have := hpos 1; have := hpos N
    field_simp
  have hG1 : gaussPot v t 1 / errWeight v t 1 = gaussVar v t 1 := by
    unfold gaussPot errWeight
    have := hpos 1
    field_simp
  rw [hι]
  constructor
  · rw [div_le_iff₀ hφ]; linarith
  · have hG : gaussPot v t 1 = gaussVar v t 1 * errWeight v t 1 := by
      rw [← hG1, div_mul_cancel₀ _ hφ.ne']
    have hηG := mul_nonneg hη hGN
    have key : errWeight v t 1 * e ≤ errWeight v t 1 * (errWeight v t N *
        (1 - gaussVar v t N) / errWeight v t 1 + (Real.exp (2 * h) - 1) * K * gaussVar v t 1) := by
      rw [mul_add, mul_div_cancel₀ _ hφ.ne']
      have : (Real.exp (2 * h) - 1) * K * (gaussPot v t 1 - gaussPot v t N) ≤
          errWeight v t 1 * ((Real.exp (2 * h) - 1) * K * gaussVar v t 1) := by
        rw [hG]; nlinarith
      linarith
    exact le_of_mul_le_mul_left key hφ

/-- `s_j = 1 - (1 - v) e^{-2t_j}` is nondecreasing along a monotone grid when `v ≤ 1`. -/
theorem gaussVar_mono {v : ℝ} (hv1 : v ≤ 1) {t : ℕ → ℝ} (ht : Monotone t) {i j : ℕ}
    (hij : i ≤ j) : gaussVar v t i ≤ gaussVar v t j := by
  have := Real.exp_le_exp.2 (by linarith [ht hij] : -2 * t j ≤ -2 * t i)
  unfold gaussVar; nlinarith

/-- **Accumulated error for `v ≤ 1`.** If `0 < v ≤ 1`, `t_0 = 0`, `t` strictly increasing,
`N ≥ 1`, `h ≥ 0` and all steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`), then the output variance of
the exact-score `β/α²` sampler satisfies
`0 ≤ w_1 - s_1 ≤ (1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1`. -/
theorem algVar_ddpm_sub_gaussVar_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h) :
    0 ≤ algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 ∧
      algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 ≤
        (1 - v) * Real.exp (-2 * (2 * t N - t 1)) + (Real.exp (2 * h) - 1) := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  have hs1 := hpos 1
  have hK : ∀ j, 1 ≤ j → j < N → 1 ≤ (gaussVar v t 1)⁻¹ * gaussVar v t j := fun j hj _ => by
    rw [inv_mul_eq_div, one_le_div hs1]; exact gaussVar_mono hv1 ht.monotone hj
  obtain ⟨b1, b2⟩ := algVar_ddpm_sub_gaussVar_mem hv h0 ht hN hh hstep (inv_nonneg.2 hs1.le) hK
  have h1sN : 1 - gaussVar v t N = (1 - v) * Real.exp (-2 * t N) := by unfold gaussVar; ring
  have hsN := hpos N
  have h1N : gaussVar v t 1 ≤ gaussVar v t N := gaussVar_mono hv1 ht.monotone hN
  have hι0 : 0 ≤ Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
      (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) := by
    rw [h1sN]; have : 0 ≤ 1 - v := by linarith
    positivity
  have hι : Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
      (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) ≤
      (1 - v) * Real.exp (-2 * (2 * t N - t 1)) := by
    rw [h1sN]
    have e : Real.exp (-2 * (2 * t N - t 1)) =
        Real.exp (-2 * t N) * Real.exp (-2 * t N) / Real.exp (-2 * t 1) := by
      rw [← Real.exp_add, ← Real.exp_sub]; ring_nf
    rw [e, div_le_iff₀ (by positivity)]
    have hr : gaussVar v t 1 ^ 2 / gaussVar v t N ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact pow_le_pow_left₀ hs1.le h1N 2
    have h1v : 0 ≤ 1 - v := by linarith
    have hE := Real.exp_pos (-2 * t N)
    have hE1 := Real.exp_pos (-2 * t 1)
    calc Real.exp (-2 * t N) * ((1 - v) * Real.exp (-2 * t N)) * gaussVar v t 1 ^ 2
        = (1 - v) * Real.exp (-2 * t N) * Real.exp (-2 * t N) *
            (gaussVar v t 1 ^ 2 / gaussVar v t N ^ 2) * gaussVar v t N ^ 2 := by
          field_simp
      _ ≤ (1 - v) * Real.exp (-2 * t N) * Real.exp (-2 * t N) * 1 * gaussVar v t N ^ 2 := by
          gcongr
      _ = _ := by field_simp
  have hmul : (Real.exp (2 * h) - 1) * (gaussVar v t 1)⁻¹ * gaussVar v t 1 =
      Real.exp (2 * h) - 1 := by field_simp
  rw [hmul] at b2
  exact ⟨hι0.trans b1, by linarith⟩

/-! ### From variances to KL -/

/-- `log y ≤ (y - y⁻¹)/2` for `y ≥ 1`. -/
theorem log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ (y - y⁻¹) / 2 := by
  rw [← Real.sinh_log (by linarith)]
  exact Real.self_le_sinh_iff.2 (Real.log_nonneg hy)

/-- For `0 < s ≤ w`: `s/w - 1 - log(s/w) ≤ (w - s)²/(2 s w)` (the per-coordinate KL integrand
`KL(N(0,s) ‖ N(0,w)) = (s/w - 1 - log(s/w))/2` is quadratic in `w - s`). -/
theorem sub_one_sub_log_div_le {s w : ℝ} (hs : 0 < s) (hsw : s ≤ w) :
    s / w - 1 - Real.log (s / w) ≤ (w - s) ^ 2 / (2 * s * w) := by
  have hw : 0 < w := lt_of_lt_of_le hs hsw
  have hy : 1 ≤ w / s := by rw [one_le_div hs]; exact hsw
  have hl := log_le_half_sub_inv hy
  rw [Real.log_div hs.ne' hw.ne']
  rw [Real.log_div hw.ne' hs.ne'] at hl
  rw [inv_div] at hl
  have e : (w - s) ^ 2 / (2 * s * w) = (w / s - s / w) / 2 - (1 - s / w) := by
    field_simp; ring
  rw [e]
  linarith

/-- `x - 1 - log x ≤ (x - 1)²/2` for `x ≥ 1` (from `log x ≥ 2(x - 1)/(x + 1)`). -/
theorem sub_one_sub_log_le_sq_div_two {x : ℝ} (hx : 1 ≤ x) :
    x - 1 - Real.log x ≤ (x - 1) ^ 2 / 2 := by
  have hl := DiffusionDiscretization.two_mul_sub_div_le_log hx
  have e : x - 1 - 2 * (x - 1) / (x + 1) = (x - 1) ^ 2 / (x + 1) := by
    field_simp; ring
  have h2 : (x - 1) ^ 2 / (x + 1) ≤ (x - 1) ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
  linarith

/-- **Two-sided quadratic bound on the KL integrand.** For `s > 0`, `b < s` and
`s - b ≤ w ≤ s + a`: `s/w - 1 - log(s/w) ≤ a²/(2 s²) + b²/(2 (s - b)²)`. -/
theorem sub_one_sub_log_div_le_two_sided {s w a b : ℝ} (hs : 0 < s)
    (hbs : b < s) (hlo : s - b ≤ w) (hhi : w ≤ s + a) :
    s / w - 1 - Real.log (s / w) ≤ a ^ 2 / (2 * s ^ 2) + b ^ 2 / (2 * (s - b) ^ 2) := by
  have hw : 0 < w := by linarith
  have hB : 0 ≤ b ^ 2 / (2 * (s - b) ^ 2) := by positivity
  have hA : 0 ≤ a ^ 2 / (2 * s ^ 2) := by positivity
  rcases le_total s w with hsw | hws
  · have h1 := sub_one_sub_log_div_le hs hsw
    have h2 : (w - s) ^ 2 / (2 * s * w) ≤ a ^ 2 / (2 * s ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : (w - s) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have : 2 * s ^ 2 ≤ 2 * s * w := by nlinarith
      calc (w - s) ^ 2 * (2 * s ^ 2) ≤ a ^ 2 * (2 * s ^ 2) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ ≤ a ^ 2 * (2 * s * w) := mul_le_mul_of_nonneg_left this (sq_nonneg _)
    linarith
  · have hx : 1 ≤ s / w := by rw [one_le_div hw]; exact hws
    have h1 := sub_one_sub_log_le_sq_div_two hx
    have hsb : 0 < s - b := by linarith
    have h3 : s / w - 1 ≤ b / (s - b) := by
      rw [div_sub_one hw.ne', div_le_div_iff₀ hw hsb]; nlinarith
    have h4 : (s / w - 1) ^ 2 ≤ (b / (s - b)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h3 2
    have e : (b / (s - b)) ^ 2 / 2 = b ^ 2 / (2 * (s - b) ^ 2) := by field_simp
    linarith

/-- **Generic output-KL upper bound (any variances `σ²`).** Let `v > 0`, `t_0 = 0`, `t` strictly
increasing, `N ≥ 1`, exact score, any `σ²`, and `s_1 - b ≤ w_1 ≤ s_1 + a` with `b < s_1`.
Then `KL(p_1 ‖ q_1) ≤ d (a²/s_1² + b²/(s_1 - b)²)/4`. -/
theorem klDiv_output_isoGauss_le_of_mem {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (σ2 : ℕ → ℝ≥0) {N : ℕ} (hN : 1 ≤ N) {a b : ℝ}
    (hbs : b < gaussVar v t 1)
    (hlo : gaussVar v t 1 - b ≤ algVar (gaussGain v t) σ2 N 1)
    (hhi : algVar (gaussGain v t) σ2 N 1 ≤ gaussVar v t 1 + a) :
    klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw σ2 (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
      ENNReal.ofReal (d * (a ^ 2 / gaussVar v t 1 ^ 2 +
        b ^ 2 / (gaussVar v t 1 - b) ^ 2) / 4) := by
  have hs := gaussVar_pos hv (t := t) (k := 1) (h0 ▸ ht.monotone (Nat.zero_le 1))
  have hw : 0 < algVar (gaussGain v t) σ2 N 1 := by linarith
  rw [(klDiv_output_isoGauss_eq hv h0 ht σ2 hN hw).2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hkl := sub_one_sub_log_div_le_two_sided hs hbs hlo hhi
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsb : 0 < gaussVar v t 1 - b := by linarith
  have e : (d : ℝ) * (a ^ 2 / gaussVar v t 1 ^ 2 + b ^ 2 / (gaussVar v t 1 - b) ^ 2) / 4 =
      d * ((a ^ 2 / (2 * gaussVar v t 1 ^ 2) + b ^ 2 / (2 * (gaussVar v t 1 - b) ^ 2)) / 2) := by
    field_simp; ring
  rw [e]
  gcongr

/-- **Output upper bound for exact-score DDPM on Gaussian data (`v ≤ 1`), with initialisation
term.** Let `μ = N(0, v I)` with `0 < v ≤ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`,
`h ≥ 0` with all steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`; any such grid, uniform or not), the
exact score
(`scoreMean t (exactScore μ t)`) and `σ_k² = β_k/α_k²` (`ddpmVar`). Then
`KL(p_1 ‖ q_1) ≤ d ((1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1)² / (4 s_1²)`,
`s_1 = e^{-2t_1} v + 1 - e^{-2t_1}`. For `v = 1` this is `O(d h²)`; for `v < 1` the
initialisation term `(1 - v) e^{-2(2t_N - t_1)}` does not vanish as `h → 0` at fixed `t_1`,
`t_N`. -/
theorem klDiv_output_isoGauss_ddpm_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h) :
    klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
      ENNReal.ofReal (d * ((1 - v) * Real.exp (-2 * (2 * t N - t 1)) +
        (Real.exp (2 * h) - 1)) ^ 2 / (4 * gaussVar v t 1 ^ 2)) := by
  have hs := gaussVar_pos hv (t := t) (k := 1) (h0 ▸ ht.monotone (Nat.zero_le 1))
  obtain ⟨b1, b2⟩ := algVar_ddpm_sub_gaussVar_le hv hv1 h0 ht hN hh hstep
  refine (klDiv_output_isoGauss_le_of_mem hv h0 ht (ddpmVar t) hN
    (a := (1 - v) * Real.exp (-2 * (2 * t N - t 1)) + (Real.exp (2 * h) - 1)) (b := 0) hs
    (by linarith) (by linarith)).trans_eq ?_
  congr 1
  ring

/-! ### The path lower bound for Gaussian data -/

/-- `x²/(2 + x) ≤ x - 1 + e^{-x}` for `x ≥ 0`. -/
theorem sq_div_two_add_le_expGap {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / (2 + x) ≤ x - 1 + Real.exp (-x) := by
  rw [div_le_iff₀ (by linarith)]
  rcases lt_or_ge x 2 with h2 | h2
  · have he := Real.exp_le_two_add_div_two_sub hx h2
    have hE : (2 - x) / (2 + x) ≤ Real.exp (-x) := by
      rw [Real.exp_neg, div_le_iff₀ (by linarith)]
      have hpos := Real.exp_pos x
      rw [le_div_iff₀ (by linarith)] at he
      field_simp
      nlinarith
    rw [div_le_iff₀ (by linarith)] at hE
    nlinarith
  · have := Real.exp_pos (-x)
    nlinarith

/-- `2h/(1 + h) ≤ 2 - (1 - e^{-2h})/h` for `h > 0` (the per-unit-time path factor of
`klDiv_truePath_ddpm_ge_uniform` is at least `2h/(1+h)`). -/
theorem two_mul_div_one_add_le {h : ℝ} (hh : 0 < h) :
    2 * h / (1 + h) ≤ 2 - (1 - Real.exp (-2 * h)) / h := by
  have key := sq_div_two_add_le_expGap (by linarith : 0 ≤ 2 * h)
  rw [div_le_iff₀ (by linarith)] at key
  have e : 2 - (1 - Real.exp (-2 * h)) / h = (2 * h - 1 + Real.exp (-2 * h)) / h := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by linarith) hh]
  rw [neg_mul] at *
  nlinarith

/-- The second moment of `N(0, v I)` is `d v` (`v ≥ 0`). -/
theorem secondMoment_isoGauss {v : ℝ} (hv : 0 ≤ v) : secondMoment (isoGauss d v) = d * v := by
  have h1 : ∫ x, x ^ 2 ∂gaussianReal 0 v.toNNReal = v := by
    have h := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 v.toNNReal)
      aemeasurable_id (by simp [integral_id_gaussianReal])
    rw [variance_id_gaussianReal, Real.coe_toNNReal _ hv] at h
    simpa using h.symm
  rw [secondMoment, isoGauss, integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 v.toNNReal)
      (f := fun x : ℝ => x ^ 2) (by fun_prop), h1]
    simp
  · intro i _
    exact integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 0 v.toNNReal) (i := i)
      (f := fun x : ℝ => x ^ 2)
      (by simpa using (memLp_id_gaussianReal (μ := 0) (v := v.toNNReal) 2).integrable_sq)

/-- **Path-KL lower bound for Gaussian data (DF-5/DF-6 specialised).** For `0 < v ≤ 1`,
`t_0 = 0`, `t` strictly increasing, `N ≥ 1`, and the uniform grid `t_k = t_1 + (k - 1) h`
(`1 ≤ k ≤ N`, `h > 0`), for **every** measurable mean map (in particular the exact score):
`d (t_N - t_1) h/(1 + h) ≤ KL(truePath ‖ algPath (β/α²) m)`. -/
theorem klDiv_truePath_isoGauss_ddpm_ge {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 < h)
    (hunif : ∀ k, 1 ≤ k → k ≤ N → t k = t 1 + ((k : ℝ) - 1) * h) :
    ENNReal.ofReal (d * (t N - t 1) * h / (1 + h)) ≤
      klDiv (truePath (isoGauss d v) t N (N - 1)) (algPath (ddpmVar t) m hm N (N - 1)) := by
  have hM : secondMoment (isoGauss d v) ≤ d := by
    rw [secondMoment_isoGauss hv.le]
    exact mul_le_of_le_one_right (Nat.cast_nonneg d) hv1
  have hμ := GaussianLSIPi.integrable_sum_sq_pi_gaussianReal (d := d) v
  refine le_trans ?_ (klDiv_truePath_ddpm_ge_uniform (isoGauss d v) hμ hM h0 ht m hm hN hh hunif)
  refine ENNReal.ofReal_le_ofReal ?_
  have hT : 0 ≤ t N - t 1 := by linarith [ht.monotone hN]
  have := two_mul_div_one_add_le hh
  have e : (d : ℝ) * (t N - t 1) * h / (1 + h) = d / 2 * (t N - t 1) * (2 * h / (1 + h)) := by
    field_simp
  rw [e]
  gcongr

/-! ### The headline -/

/-- **Gaussian output upper bound with initialisation and a path lower bound.** Let
`μ = N(0, v I)` on `Fin d → ℝ` with `0 < v ≤ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`,
the uniform grid `t_k = t_1 + (k - 1) h` (`1 ≤ k ≤ N`, `h > 0`), the exact score and the DDPM
variance `σ_k² = β_k/α_k²`. Then, for the same sampler,
* output: `KL(p_1 ‖ q_1) ≤ d ((1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1)² / (4 s_1²)`;
* path: `KL(truePath ‖ algPath) ≥ d (t_N - t_1) h/(1 + h)`.
At fixed `t_1` and `t_N - t_1 > 0`, the output is `O(d h²)` when `v = 1`; for `v < 1`
the initialisation term remains. The path statement is a lower bound, not a matching upper
bound. -/
theorem gaussian_output_path_separation {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 < h)
    (hunif : ∀ k, 1 ≤ k → k ≤ N → t k = t 1 + ((k : ℝ) - 1) * h) :
    klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
      ENNReal.ofReal (d * ((1 - v) * Real.exp (-2 * (2 * t N - t 1)) +
        (Real.exp (2 * h) - 1)) ^ 2 / (4 * gaussVar v t 1 ^ 2)) ∧
    ENNReal.ofReal (d * (t N - t 1) * h / (1 + h)) ≤
      klDiv (truePath (isoGauss d v) t N (N - 1))
        (algPath (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N (N - 1)) := by
  refine ⟨klDiv_output_isoGauss_ddpm_le hv hv1 h0 ht hN hh.le fun k hk2 hkN => ?_,
    klDiv_truePath_isoGauss_ddpm_ge hv hv1 h0 ht _ _ hN hh hunif⟩
  rw [hunif k (by omega) hkN, hunif (k - 1) (by omega) (by omega), Nat.cast_sub (by omega)]
  push_cast; linarith

end FormalizeSampling.DiffusionGaussian
