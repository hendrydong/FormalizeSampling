module

public import FormalizeSampling.Samplers.DiffusionGaussianOutputRate

/-!
# Output KL of exact-score DDPM on Gaussian data: an `Ω(h²)` lower bound, matching for `v = 1`

Status: **Verified**.

Setting of `Samplers/DiffusionGaussianOutputRate.lean` (DF-8): data `μ = N(0, v I)` on
`Fin d → ℝ`, grid `0 = t_0 < t_1 < ⋯ < t_N`, exact score, reverse variance
`σ_k² = β_k/α_k² = e^{2h_k} - 1` (`ddpmVar`), forward variances `s_k`, sampler variances `w_k`
(`w_N = 1`, `w_{k-1} = c_k² w_k + σ_k²`), `φ_k = e^{-2t_k}/s_k²`, `G_k = e^{-2t_k}/s_k`.

**Lower side of the error identity** (`errWeight_lower_bound`, `algVar_ddpm_sub_gaussVar_ge`).
If every step satisfies `t_k - t_{k-1} ≥ h'` (`2 ≤ k ≤ N`) and `K' s_j ≤ 1` (`1 ≤ j < N`,
`K' ≥ 0`), then the telescoped identity `errWeight_ddpm_telescope` gives, for every `v > 0`,
`w_1 - s_1 ≥ ι + (e^{2h'} - 1) K' (s_1 - e^{-2t_N} s_1²/(s_N e^{-2t_1}))`, with the
initialisation term `ι = e^{-2t_N} (1 - s_N) s_1²/(s_N² e^{-2t_1})` of
`algVar_ddpm_sub_gaussVar_mem`. For `v ≤ 1` (`ι ≥ 0`, `K' = 1`, `s_1 ≤ s_N`):
`w_1 ≥ s_1 (1 + ρ)`, `ρ = (e^{2h'} - 1)(1 - e^{-2(t_N - t_1)})` (`algVar_ddpm_ge_of_le_one`).

**KL lower bound.** With `y = w/s ≥ 1`, `log y ≥ 2(y - 1)/(y + 1)`
(`DiffusionDiscretization.two_mul_sub_div_le_log`) gives
`s/w - 1 - log(s/w) ≥ (y - 1)²/(y (y + 1))`, increasing in `y`
(`sq_div_le_sub_one_sub_log_div`). Hence, for any reverse variances, `s_1 (1 + ρ) ≤ w_1` with
`ρ ≥ 0` gives `KL(p_1 ‖ q_1) ≥ d ρ²/(2 (1 + ρ)(2 + ρ))` (`klDiv_output_isoGauss_ge_of_ge`); for
`σ² = β/α²`, `0 < v ≤ 1` and all steps `≥ h' ≥ 0` (`klDiv_output_isoGauss_ddpm_ge`):
`KL(p_1 ‖ q_1) ≥ d ρ² / (2 (1 + ρ)(2 + ρ))`, and if `e^{2h'} ≤ 2`
(`klDiv_output_isoGauss_ddpm_ge_sq`): `KL(p_1 ‖ q_1) ≥ d h'² (1 - e^{-2(t_N - t_1)})² / 3`.

**Two-sided headline** (`gaussian_output_two_sided`). On the uniform grid
`t_k = t_1 + (k - 1) h`, `0 < v ≤ 1`, `e^{2h} ≤ 2`:
`d h² (1 - e^{-2(t_N - t_1)})²/3 ≤ KL(p_1 ‖ q_1)`,
`KL(p_1 ‖ q_1) ≤ d ((1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1)²/(4 s_1²)`, and
`KL(truePath ‖ algPath) ≥ d (t_N - t_1) h/(1 + h)`. At fixed `t_1`, `t_N - t_1 > 0` and
`v = 1`, initialisation is exact: the output KL is `Θ(d h²)` and the path KL is `Ω(d h)`;
for `d ≥ 1` their ratio is `O(h) → 0`. For fixed `v < 1` and horizon the upper bound retains
a nonzero initialisation allowance. The output lower bound does not remove it, so pure
quadratic total-error scaling and that ratio limit require additional initialisation control.

Relation to the literature: Jiao–Zhou–Li (2025, arXiv:2510.27562, Thm 2) prove an output lower
bound of order `d/N²` for a family of isotropic Gaussian data laws `N(0, λ I)`, with the oracle
score on their schedule (including the
variance `β/α²`).

## Main results

* `errWeight_lower_bound`, `algVar_ddpm_sub_gaussVar_ge`, `algVar_ddpm_ge_of_le_one`.
* `sq_div_le_sub_one_sub_log_div`, `klDiv_output_isoGauss_ge_of_ge` (any `σ²`).
* `klDiv_output_isoGauss_ddpm_ge`, `klDiv_output_isoGauss_ddpm_ge_sq`.
* `gaussian_output_two_sided`.

## Not proved here

* A path-KL **upper** bound `O(d h)` (for `v = 1`, the ratio output/path is shown to be
  `O(h)`, not `Θ(h)`).
* The constants are not matched: the lower bound uses `K' = 1` and the upper bound
  `K = 1/s_1`, so for `v < 1` they differ by the factor `≈ 1/s_1²` (numerically
  `showcase/gauss_output_ext.py`). `v > 1` and `σ² = β` are in
  `Samplers/DiffusionGaussianOutputExtLarge.lean` and
  `Samplers/DiffusionGaussianOutputExtBeta.lean`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionGaussian

open FormalizeSampling.Diffusion
  FormalizeSampling.DiffusionDiscretization FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-! ### Lower side of the accumulated error -/

/-- **Accumulated error, weighted lower bound.** Let `v > 0`, `t_0 = 0`, `t` strictly increasing,
all steps `t_k - t_{k-1} ≥ h'` for `2 ≤ k ≤ N`, and `K' ≥ 0` with `K' s_j ≤ 1` for
`1 ≤ j < N`. Then for `1 ≤ k ≤ N` (with `w = algVar c (β/α²) N`, exact gain `c`):
`φ_N (1 - s_N) + (e^{2h'} - 1) K' (G_k - G_N) ≤ φ_k (w_k - s_k)`. -/
theorem errWeight_lower_bound {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} {hl K : ℝ} (hstep : ∀ k, 2 ≤ k → k ≤ N → hl ≤ t k - t (k - 1))
    (hK0 : 0 ≤ K) (hK : ∀ j, 1 ≤ j → j < N → K * gaussVar v t j ≤ 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) :
    errWeight v t N * (1 - gaussVar v t N) +
        (Real.exp (2 * hl) - 1) * K * (gaussPot v t k - gaussPot v t N) ≤
      errWeight v t k * (algVar (gaussGain v t) (ddpmVar t) N k - gaussVar v t k) := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  rw [errWeight_ddpm_telescope hv h0 ht.monotone hkN, ← sum_gaussPot_sub v t hkN, Finset.mul_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_
    (sub_nonneg.2 (gaussPot_succ_le v ht.monotone j (hpos _) (hpos _))))
  simp only [mem_Ico] at hj
  have h1 : 0 ≤ Real.exp (2 * (t (j + 1) - t j)) - 1 := by
    linarith [Real.one_le_exp (by linarith [ht.monotone (Nat.le_succ j)] :
      0 ≤ 2 * (t (j + 1) - t j))]
  have h2 : Real.exp (2 * hl) - 1 ≤ Real.exp (2 * (t (j + 1) - t j)) - 1 := by
    have := hstep (j + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at this
    linarith [Real.exp_le_exp.2 (by linarith : 2 * hl ≤ 2 * (t (j + 1) - t j))]
  have h3 : K ≤ (gaussVar v t j)⁻¹ := by
    rw [← one_div, le_div_iff₀ (hpos j)]; exact hK j (by omega) hj.2
  rw [div_eq_mul_inv]
  exact mul_le_mul h2 h3 hK0 h1

/-- **Accumulated error of the output variance, lower bound (any `v > 0`).** Under the
hypotheses of `errWeight_lower_bound` with `N ≥ 1`:
`ι + (e^{2h'} - 1) K' (s_1 - e^{-2t_N} s_1²/(s_N e^{-2t_1})) ≤ w_1 - s_1`, where
`ι = e^{-2t_N} (1 - s_N) s_1²/(s_N² e^{-2t_1})` is the initialisation term of
`algVar_ddpm_sub_gaussVar_mem`. -/
theorem algVar_ddpm_sub_gaussVar_ge {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {hl K : ℝ}
    (hstep : ∀ k, 2 ≤ k → k ≤ N → hl ≤ t k - t (k - 1)) (hK0 : 0 ≤ K)
    (hK : ∀ j, 1 ≤ j → j < N → K * gaussVar v t j ≤ 1) :
    Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) +
        (Real.exp (2 * hl) - 1) * K * (gaussVar v t 1 - Real.exp (-2 * t N) *
          gaussVar v t 1 ^ 2 / (gaussVar v t N * Real.exp (-2 * t 1))) ≤
      algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  have b := errWeight_lower_bound hv h0 ht hstep hK0 hK le_rfl hN
  have hφ : 0 < errWeight v t 1 := by unfold errWeight; have := hpos 1; positivity
  have hs1 := hpos 1
  have hsN := hpos N
  have e : Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) +
        (Real.exp (2 * hl) - 1) * K * (gaussVar v t 1 - Real.exp (-2 * t N) *
          gaussVar v t 1 ^ 2 / (gaussVar v t N * Real.exp (-2 * t 1))) =
      (errWeight v t N * (1 - gaussVar v t N) +
        (Real.exp (2 * hl) - 1) * K * (gaussPot v t 1 - gaussPot v t N)) / errWeight v t 1 := by
    unfold errWeight gaussPot
    field_simp
  rw [e, div_le_iff₀ hφ]
  linarith [b]

/-- **Lower bound on the output variance for `v ≤ 1`.** If `0 < v ≤ 1`, `t_0 = 0`, `t` strictly
increasing, `N ≥ 1`, `h' ≥ 0` and all steps `t_k - t_{k-1} ≥ h'` (`2 ≤ k ≤ N`), then
`s_1 (1 + (e^{2h'} - 1)(1 - e^{-2(t_N - t_1)})) ≤ w_1`. -/
theorem algVar_ddpm_ge_of_le_one {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {hl : ℝ} (hl0 : 0 ≤ hl)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → hl ≤ t k - t (k - 1)) :
    gaussVar v t 1 * (1 + (Real.exp (2 * hl) - 1) * (1 - Real.exp (-2 * (t N - t 1)))) ≤
      algVar (gaussGain v t) (ddpmVar t) N 1 := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  have hle1 : ∀ j, gaussVar v t j ≤ 1 := fun j => by
    have := Real.exp_pos (-2 * t j)
    unfold gaussVar; nlinarith
  have b := algVar_ddpm_sub_gaussVar_ge hv h0 ht hN hstep zero_le_one
    (fun j _ _ => by rw [one_mul]; exact hle1 j)
  have hs1 := hpos 1
  have hsN := hpos N
  have h1sN : 1 - gaussVar v t N = (1 - v) * Real.exp (-2 * t N) := by unfold gaussVar; ring
  have hι0 : 0 ≤ Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
      (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) := by
    rw [h1sN]; have : 0 ≤ 1 - v := by linarith
    positivity
  have h1N : gaussVar v t 1 ≤ gaussVar v t N := gaussVar_mono hv1 ht.monotone hN
  have hη : 0 ≤ Real.exp (2 * hl) - 1 := by
    linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * hl)]
  have hE : Real.exp (-2 * (t N - t 1)) = Real.exp (-2 * t N) / Real.exp (-2 * t 1) := by
    rw [← Real.exp_sub]; ring_nf
  have hrat : gaussVar v t 1 * Real.exp (-2 * (t N - t 1)) ≥
      Real.exp (-2 * t N) * gaussVar v t 1 ^ 2 / (gaussVar v t N * Real.exp (-2 * t 1)) := by
    rw [hE]
    have := Real.exp_pos (-2 * t N)
    have := Real.exp_pos (-2 * t 1)
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    have : gaussVar v t 1 * (Real.exp (-2 * t N) / Real.exp (-2 * t 1)) *
        (gaussVar v t N * Real.exp (-2 * t 1)) =
        gaussVar v t 1 * Real.exp (-2 * t N) * gaussVar v t N := by field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_left h1N (by positivity :
      0 ≤ gaussVar v t 1 * Real.exp (-2 * t N))
    nlinarith
  have := mul_le_mul_of_nonneg_left hrat.le hη
  nlinarith

/-! ### From variances to a KL lower bound -/

/-- For `0 < s`, `ρ ≥ 0` and `s (1 + ρ) ≤ w`:
`ρ²/((1 + ρ)(2 + ρ)) ≤ s/w - 1 - log(s/w)` (the per-coordinate KL integrand is at least
quadratic in the relative error `w/s - 1`). -/
theorem sq_div_le_sub_one_sub_log_div {s w ρ : ℝ} (hs : 0 < s) (hρ : 0 ≤ ρ)
    (hsw : s * (1 + ρ) ≤ w) :
    ρ ^ 2 / ((1 + ρ) * (2 + ρ)) ≤ s / w - 1 - Real.log (s / w) := by
  have hw : 0 < w := by nlinarith
  set y := w / s with hy
  have hy1 : 1 + ρ ≤ y := by rw [hy, le_div_iff₀ hs]; linarith
  have hy0 : 0 < y := by linarith
  have hl := DiffusionDiscretization.two_mul_sub_div_le_log (by linarith : 1 ≤ y)
  have hsw' : s / w = y⁻¹ := by rw [hy, inv_div]
  rw [hsw', Real.log_inv]
  have h1 : ρ / (1 + ρ) ≤ (y - 1) / y := by
    rw [div_le_div_iff₀ (by linarith) hy0]; nlinarith
  have h2 : ρ / (2 + ρ) ≤ (y - 1) / (y + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have h1' : 0 ≤ ρ / (1 + ρ) := by positivity
  have h2' : 0 ≤ ρ / (2 + ρ) := by positivity
  have hprod := mul_le_mul h1 h2 h2' (by
    have : 0 ≤ y - 1 := by linarith
    positivity)
  have e1 : ρ / (1 + ρ) * (ρ / (2 + ρ)) = ρ ^ 2 / ((1 + ρ) * (2 + ρ)) := by
    field_simp
  have e2 : (y - 1) / y * ((y - 1) / (y + 1)) = y⁻¹ - 1 + 2 * (y - 1) / (y + 1) := by
    field_simp; ring
  rw [e1, e2] at hprod
  linarith

/-- **Generic output-KL lower bound (any variances `σ²`).** Let `v > 0`, `t_0 = 0`, `t` strictly
increasing, `N ≥ 1`, exact score, any `σ²`, `ρ ≥ 0` and `s_1 (1 + ρ) ≤ w_1`. Then
`d ρ²/(2 (1 + ρ)(2 + ρ)) ≤ KL(p_1 ‖ q_1)`. -/
theorem klDiv_output_isoGauss_ge_of_ge {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (σ2 : ℕ → ℝ≥0) {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hge : gaussVar v t 1 * (1 + ρ) ≤ algVar (gaussGain v t) σ2 N 1) :
    ENNReal.ofReal (d * ρ ^ 2 / (2 * (1 + ρ) * (2 + ρ))) ≤
      klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw σ2 (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) := by
  have hs := gaussVar_pos hv (t := t) (k := 1) (h0 ▸ ht.monotone (Nat.zero_le 1))
  have hw : 0 < algVar (gaussGain v t) σ2 N 1 := by nlinarith
  rw [(klDiv_output_isoGauss_eq hv h0 ht σ2 hN hw).2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hkl := sq_div_le_sub_one_sub_log_div hs hρ hge
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e : (d : ℝ) * ρ ^ 2 / (2 * (1 + ρ) * (2 + ρ)) = d * (ρ ^ 2 / ((1 + ρ) * (2 + ρ)) / 2) := by
    field_simp
  rw [e]
  gcongr

/-- **`Ω(h²)` output lower bound for exact-score DDPM on Gaussian data (`v ≤ 1`).** Let
`μ = N(0, v I)` with `0 < v ≤ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`, `h' ≥ 0` with
all steps `t_k - t_{k-1} ≥ h'` (`2 ≤ k ≤ N`; any such grid), the exact score and
`σ_k² = β_k/α_k²` (`ddpmVar`). With `ρ = (e^{2h'} - 1)(1 - e^{-2(t_N - t_1)})`:
`d ρ²/(2 (1 + ρ)(2 + ρ)) ≤ KL(p_1 ‖ q_1)`. -/
theorem klDiv_output_isoGauss_ddpm_ge {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {hl : ℝ} (hl0 : 0 ≤ hl)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → hl ≤ t k - t (k - 1)) :
    ENNReal.ofReal (d * ((Real.exp (2 * hl) - 1) * (1 - Real.exp (-2 * (t N - t 1)))) ^ 2 /
        (2 * (1 + (Real.exp (2 * hl) - 1) * (1 - Real.exp (-2 * (t N - t 1)))) *
          (2 + (Real.exp (2 * hl) - 1) * (1 - Real.exp (-2 * (t N - t 1)))))) ≤
      klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) := by
  refine klDiv_output_isoGauss_ge_of_ge hv h0 ht _ hN (mul_nonneg ?_ ?_)
    (algVar_ddpm_ge_of_le_one hv hv1 h0 ht hN hl0 hstep)
  · linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * hl)]
  · rw [sub_nonneg, Real.exp_le_one_iff]
    linarith [ht.monotone hN]

/-- **Clean `Ω(h²)` form.** Under the hypotheses of `klDiv_output_isoGauss_ddpm_ge` and
`e^{2h'} ≤ 2` (i.e. `h' ≤ log 2/2`):
`d h'² (1 - e^{-2(t_N - t_1)})²/3 ≤ KL(p_1 ‖ q_1)`. -/
theorem klDiv_output_isoGauss_ddpm_ge_sq {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {hl : ℝ} (hl0 : 0 ≤ hl)
    (hl2 : Real.exp (2 * hl) ≤ 2) (hstep : ∀ k, 2 ≤ k → k ≤ N → hl ≤ t k - t (k - 1)) :
    ENNReal.ofReal (d * hl ^ 2 * (1 - Real.exp (-2 * (t N - t 1))) ^ 2 / 3) ≤
      klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) := by
  refine le_trans ?_ (klDiv_output_isoGauss_ddpm_ge hv hv1 h0 ht hN hl0 hstep)
  refine ENNReal.ofReal_le_ofReal ?_
  set E := 1 - Real.exp (-2 * (t N - t 1))
  have hE0 : 0 ≤ E := by
    simp only [E]; rw [sub_nonneg, Real.exp_le_one_iff]; linarith [ht.monotone hN]
  have hE1 : E ≤ 1 := by simp only [E]; linarith [Real.exp_pos (-2 * (t N - t 1))]
  set η := Real.exp (2 * hl) - 1
  have hη : 2 * hl ≤ η := by simp only [η]; linarith [Real.add_one_le_exp (2 * hl)]
  have hη1 : η ≤ 1 := by simp only [η]; linarith
  set ρ := η * E
  have hρ0 : 0 ≤ ρ := mul_nonneg (by linarith) hE0
  have hρ1 : ρ ≤ 1 := by simp only [ρ]; nlinarith
  have hρ2 : 2 * hl * E ≤ ρ := mul_le_mul_of_nonneg_right hη hE0
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have hsq : (2 * hl * E) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by positivity) hρ2 2
  have hden : 2 * (1 + ρ) * (2 + ρ) ≤ 12 := by nlinarith
  have : d * hl ^ 2 * E ^ 2 * (2 * (1 + ρ) * (2 + ρ)) ≤ d * hl ^ 2 * E ^ 2 * 12 :=
    mul_le_mul_of_nonneg_left hden (by positivity)
  have h4 : d * hl ^ 2 * E ^ 2 * 12 = d * (2 * hl * E) ^ 2 * 3 := by ring
  have : d * (2 * hl * E) ^ 2 * 3 ≤ d * ρ ^ 2 * 3 := by gcongr
  linarith

/-! ### The two-sided headline -/

/-- **Two-sided Gaussian output bounds with initialisation, and a path lower bound.** Let
`μ = N(0, v I)` with `0 < v ≤ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`, the uniform grid
`t_k = t_1 + (k - 1) h` (`1 ≤ k ≤ N`) with `h > 0`, `e^{2h} ≤ 2`, the exact score and
`σ_k² = β_k/α_k²`. Then for the same sampler
* `d h² (1 - e^{-2(t_N - t_1)})²/3 ≤ KL(p_1 ‖ q_1)`;
* `KL(p_1 ‖ q_1) ≤ d ((1 - v) e^{-2(2t_N - t_1)} + e^{2h} - 1)²/(4 s_1²)`;
* `d (t_N - t_1) h/(1 + h) ≤ KL(truePath ‖ algPath)`.
For `v = 1` and a fixed positive interval this yields output `Θ(d h²)`; for `v < 1`
the total-error upper bound retains the displayed initialisation term. -/
theorem gaussian_output_two_sided {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 < h)
    (hh2 : Real.exp (2 * h) ≤ 2)
    (hunif : ∀ k, 1 ≤ k → k ≤ N → t k = t 1 + ((k : ℝ) - 1) * h) :
    ENNReal.ofReal (d * h ^ 2 * (1 - Real.exp (-2 * (t N - t 1))) ^ 2 / 3) ≤
        klDiv (fwdLaw (isoGauss d v) t 1)
          (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
            (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ∧
      klDiv (fwdLaw (isoGauss d v) t 1)
          (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
            (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
        ENNReal.ofReal (d * ((1 - v) * Real.exp (-2 * (2 * t N - t 1)) +
          (Real.exp (2 * h) - 1)) ^ 2 / (4 * gaussVar v t 1 ^ 2)) ∧
      ENNReal.ofReal (d * (t N - t 1) * h / (1 + h)) ≤
        klDiv (truePath (isoGauss d v) t N (N - 1))
          (algPath (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
            (measurable_scoreMean t (measurable_exactScore _ t)) N (N - 1)) := by
  have hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) = h := fun k hk2 hkN => by
    rw [hunif k (by omega) hkN, hunif (k - 1) (by omega) (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  obtain ⟨hup, hpath⟩ := gaussian_output_path_separation hv hv1 h0 ht hN hh hunif
  exact ⟨klDiv_output_isoGauss_ddpm_ge_sq hv hv1 h0 ht hN hh.le hh2
    (fun k hk2 hkN => (hstep k hk2 hkN).ge), hup, hpath⟩

end FormalizeSampling.DiffusionGaussian
