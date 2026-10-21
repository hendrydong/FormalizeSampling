module

public import FormalizeSampling.Samplers.DiffusionGaussianOutputExt

/-!
# Output KL of exact-score DDPM on Gaussian data with variance `v ≥ 1`

Status: **Verified**.

Setting of `Samplers/DiffusionGaussianOutputRate.lean` (DF-8): data `μ = N(0, v I)`, grid
`0 = t_0 < t_1 < ⋯ < t_N`, exact score, forward variances `s_k = 1 + (v - 1) e^{-2t_k}`, sampler
variances `w_k`, initialisation term `ι = e^{-2t_N} (1 - s_N) s_1²/(s_N² e^{-2t_1})`.

**Generic KL step** (any reverse variances `σ²`). If `s_1 - b ≤ w_1 ≤ s_1 + a` with
`b < s_1`, then `KL(p_1 ‖ q_1) ≤ d (a²/s_1² + b²/(s_1 - b)²)/4`
(`klDiv_output_isoGauss_le_of_mem`, `Samplers/DiffusionGaussianOutputRate.lean`); if
`s_1 (1 + ρ) ≤ w_1` with `ρ ≥ 0`, then `KL(p_1 ‖ q_1) ≥ d ρ²/(2 (1 + ρ)(2 + ρ))`
(`klDiv_output_isoGauss_ge_of_ge`, `Samplers/DiffusionGaussianOutputExt.lean`).

**Initialisation term** (`initTerm_mem_of_le_one`, `initTerm_mem_of_one_le`): for `v ≤ 1`,
`0 ≤ ι ≤ (1 - v) e^{-2(2t_N - t_1)}`; for `v ≥ 1`, `-(v - 1) e^{-2(2t_N - t_1)} s_1² ≤ ι ≤ 0`
(now negative: the sampler may undershoot `s_1`, and the KL step needs a lower bound on `w_1`).

**`v ≥ 1`, `σ² = β/α²`.** With all steps `≤ h` (`algVar_ddpm_sub_gaussVar_mem_of_one_le`,
`K = 1` since `s_j ≥ 1`): `-(v - 1) e^{-2(2t_N - t_1)} s_1² ≤ w_1 - s_1 ≤ (e^{2h} - 1) s_1`.
Hence, if `ε ≥ (v - 1) e^{-2(2t_N - t_1)} s_1` and `ε < 1` (the required lower bound on `ε`
decays exponentially in `t_N` at fixed `v, t_1`), (`klDiv_output_isoGauss_ddpm_le_of_one_le`)
`KL(p_1 ‖ q_1) ≤ d ((e^{2h} - 1)² + (ε/(1 - ε))²)/4`.
With all steps `≥ h' ≥ 0` (`K' = 1/s_1` since `s_j ≤ s_1`), for every
`0 ≤ ρ ≤ (e^{2h'} - 1)(1 - e^{-2(t_N - t_1)} s_1)/s_1 - ε`
(`klDiv_output_isoGauss_ddpm_ge_of_one_le`): `KL(p_1 ‖ q_1) ≥ d ρ²/(2 (1 + ρ)(2 + ρ))`.
For `ε` bounded away from one the upper bound is `O(d (h² + ε²))`. A lower bound of order
`h²` additionally requires an admissible `ρ` bounded below by a positive multiple of `h`.
Thus `Θ(d h²)` requires controlling initialisation relative to the discretisation scale;
it does not follow for fixed `v > 1` and fixed horizon as `h → 0`.

## Main results

* `gaussVar_anti`, `one_le_gaussVar`, `initTerm_mem_of_le_one`, `initTerm_mem_of_one_le`.
* `algVar_ddpm_sub_gaussVar_mem_of_one_le`, `klDiv_output_isoGauss_ddpm_le_of_one_le`,
  `klDiv_output_isoGauss_ddpm_ge_of_one_le`.

## Not proved here

* The constants of the upper and lower bounds are not matched (factor
  `≈ s_1²/(1 - e^{-2(t_N - t_1)} s_1)²` in the `h²` coefficient, see
  `showcase/gauss_output_ext.py`).
* A path-KL lower bound for `v > 1` (`klDiv_truePath_isoGauss_ddpm_ge` assumes second moment
  `≤ d`, i.e. `v ≤ 1`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionGaussian

open FormalizeSampling.Diffusion
  FormalizeSampling.DiffusionDiscretization FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-! ### Forward variances and the initialisation term -/

/-- For `v ≥ 1`, `s_j = 1 + (v - 1) e^{-2t_j}` is nonincreasing along a monotone grid. -/
theorem gaussVar_anti {v : ℝ} (hv1 : 1 ≤ v) {t : ℕ → ℝ} (ht : Monotone t) {i j : ℕ}
    (hij : i ≤ j) : gaussVar v t j ≤ gaussVar v t i := by
  have := Real.exp_le_exp.2 (by linarith [ht hij] : -2 * t j ≤ -2 * t i)
  unfold gaussVar; nlinarith

/-- For `v ≥ 1`, `s_j ≥ 1`. -/
theorem one_le_gaussVar {v : ℝ} (hv1 : 1 ≤ v) (t : ℕ → ℝ) (j : ℕ) : 1 ≤ gaussVar v t j := by
  have := Real.exp_pos (-2 * t j)
  unfold gaussVar; nlinarith

/-- `e^{-2t_N} e^{-2t_N}/e^{-2t_1} = e^{-2(2t_N - t_1)}`. -/
theorem exp_two_init (t : ℕ → ℝ) (N : ℕ) :
    Real.exp (-2 * t N) * Real.exp (-2 * t N) / Real.exp (-2 * t 1) =
      Real.exp (-2 * (2 * t N - t 1)) := by
  rw [← Real.exp_add, ← Real.exp_sub]; ring_nf

/-- **Initialisation term, `v ≤ 1`.** For `0 < v ≤ 1`, `t_0 = 0`, `t` monotone and `1 ≤ N`:
`0 ≤ ι ≤ (1 - v) e^{-2(2t_N - t_1)}`, `ι = e^{-2t_N} (1 - s_N) s_1²/(s_N² e^{-2t_1})`. -/
theorem initTerm_mem_of_le_one {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : Monotone t) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) ∧
      Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) ≤ (1 - v) * Real.exp (-2 * (2 * t N - t 1)) := by
  have hs1 := gaussVar_pos hv (t := t) (k := 1) (h0 ▸ ht (Nat.zero_le 1))
  have hsN := gaussVar_pos hv (t := t) (k := N) (h0 ▸ ht (Nat.zero_le N))
  have h1N : gaussVar v t 1 ≤ gaussVar v t N := gaussVar_mono hv1 ht hN
  have h1sN : 1 - gaussVar v t N = (1 - v) * Real.exp (-2 * t N) := by unfold gaussVar; ring
  have h1v : 0 ≤ 1 - v := by linarith
  have hE := Real.exp_pos (-2 * t N)
  have hE1 := Real.exp_pos (-2 * t 1)
  rw [h1sN]
  refine ⟨by positivity, ?_⟩
  rw [← exp_two_init, div_le_iff₀ (by positivity)]
  have hr : gaussVar v t 1 ^ 2 ≤ gaussVar v t N ^ 2 := pow_le_pow_left₀ hs1.le h1N 2
  have e : (1 - v) * (Real.exp (-2 * t N) * Real.exp (-2 * t N) / Real.exp (-2 * t 1)) *
      (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) =
      (1 - v) * Real.exp (-2 * t N) * Real.exp (-2 * t N) * gaussVar v t N ^ 2 := by
    field_simp
  rw [e]
  have : 0 ≤ (1 - v) * Real.exp (-2 * t N) * Real.exp (-2 * t N) := by positivity
  nlinarith

/-- **Initialisation term, `v ≥ 1`.** For `v ≥ 1` and any grid with `1 ≤ N`:
`-(v - 1) e^{-2(2t_N - t_1)} s_1² ≤ ι ≤ 0`. -/
theorem initTerm_mem_of_one_le {v : ℝ} (hv1 : 1 ≤ v) (t : ℕ → ℝ) (N : ℕ) :
    -((v - 1) * Real.exp (-2 * (2 * t N - t 1)) * gaussVar v t 1 ^ 2) ≤
        Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
          (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) ∧
      Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
          (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) ≤ 0 := by
  have hsN := one_le_gaussVar hv1 t N
  have h1sN : 1 - gaussVar v t N = -((v - 1) * Real.exp (-2 * t N)) := by unfold gaussVar; ring
  have hv0 : 0 ≤ v - 1 := by linarith
  have hE := Real.exp_pos (-2 * t N)
  have hE1 := Real.exp_pos (-2 * t 1)
  have hP : 0 ≤ (v - 1) * Real.exp (-2 * t N) * Real.exp (-2 * t N) * gaussVar v t 1 ^ 2 := by
    positivity
  have e : Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
      (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) =
      -((v - 1) * Real.exp (-2 * t N) * Real.exp (-2 * t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1))) := by
    rw [h1sN]; ring
  rw [e]
  refine ⟨?_, by rw [neg_nonpos]; positivity⟩
  rw [neg_le_neg_iff, ← exp_two_init, div_le_iff₀ (by positivity)]
  have e2 : (v - 1) * (Real.exp (-2 * t N) * Real.exp (-2 * t N) / Real.exp (-2 * t 1)) *
      gaussVar v t 1 ^ 2 * (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) =
      (v - 1) * Real.exp (-2 * t N) * Real.exp (-2 * t N) * gaussVar v t 1 ^ 2 *
        gaussVar v t N ^ 2 := by
    field_simp
  rw [e2]
  have : 1 ≤ gaussVar v t N ^ 2 := one_le_pow₀ hsN
  nlinarith

/-! ### `v ≥ 1` with `σ² = β/α²` -/

/-- **Accumulated error for `v ≥ 1`.** If `v ≥ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`,
`h ≥ 0` and all steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`), then the output variance of the
exact-score `β/α²` sampler satisfies
`-(v - 1) e^{-2(2t_N - t_1)} s_1² ≤ w_1 - s_1 ≤ (e^{2h} - 1) s_1`. -/
theorem algVar_ddpm_sub_gaussVar_mem_of_one_le {v : ℝ} (hv1 : 1 ≤ v) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h) :
    -((v - 1) * Real.exp (-2 * (2 * t N - t 1)) * gaussVar v t 1 ^ 2) ≤
        algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 ∧
      algVar (gaussGain v t) (ddpmVar t) N 1 - gaussVar v t 1 ≤
        (Real.exp (2 * h) - 1) * gaussVar v t 1 := by
  have hv : 0 < v := by linarith
  obtain ⟨b1, b2⟩ := algVar_ddpm_sub_gaussVar_mem hv h0 ht hN hh hstep zero_le_one
    (fun j _ _ => by rw [one_mul]; exact one_le_gaussVar hv1 t j)
  obtain ⟨i1, i2⟩ := initTerm_mem_of_one_le hv1 t N
  rw [mul_one] at b2
  exact ⟨i1.trans b1, by linarith⟩

/-- **Output upper bound for `v ≥ 1` with initialisation allowance `ε`.** Let `μ = N(0, v I)`
with `v ≥ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`, `h ≥ 0` with all steps
`t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`), the exact score and `σ_k² = β_k/α_k²`. If
`(v - 1) e^{-2(2t_N - t_1)} s_1 ≤ ε < 1`, then
`KL(p_1 ‖ q_1) ≤ d ((e^{2h} - 1)² + (ε/(1 - ε))²)/4`. This is `O(d (h² + ε²))`; it is not
`O(h²)` at fixed `v > 1` and fixed horizon. -/
theorem klDiv_output_isoGauss_ddpm_le_of_one_le {v : ℝ} (hv1 : 1 ≤ v) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h ε : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h)
    (hε : (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * gaussVar v t 1 ≤ ε) (hε1 : ε < 1) :
    klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
      ENNReal.ofReal (d * ((Real.exp (2 * h) - 1) ^ 2 + (ε / (1 - ε)) ^ 2) / 4) := by
  have hv : 0 < v := by linarith
  have hs := one_le_gaussVar hv1 t 1
  obtain ⟨b1, b2⟩ := algVar_ddpm_sub_gaussVar_mem_of_one_le hv1 h0 ht hN hh hstep
  set s := gaussVar v t 1
  have hε0 : 0 ≤ ε := le_trans (by
    have := Real.exp_pos (-2 * (2 * t N - t 1)); have : 0 ≤ v - 1 := by linarith
    positivity) hε
  have hη : 0 ≤ Real.exp (2 * h) - 1 := by
    linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * h)]
  have hlo : s - ε * s ≤ algVar (gaussGain v t) (ddpmVar t) N 1 := by
    have : (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * s ^ 2 ≤ ε * s := by
      have := mul_le_mul_of_nonneg_right hε (by linarith : (0 : ℝ) ≤ s)
      nlinarith
    linarith
  have hbs : ε * s < s := by nlinarith
  refine le_trans (klDiv_output_isoGauss_le_of_mem hv h0 ht (ddpmVar t) hN
    (a := (Real.exp (2 * h) - 1) * s) (b := ε * s) hbs hlo (by linarith)) ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have h1ε : 0 < 1 - ε := by linarith
  have key : ∀ x : ℝ, 0 < x → (d : ℝ) * (((Real.exp (2 * h) - 1) * x) ^ 2 / x ^ 2 +
      (ε * x) ^ 2 / (x - ε * x) ^ 2) / 4 =
      d * ((Real.exp (2 * h) - 1) ^ 2 + (ε / (1 - ε)) ^ 2) / 4 := fun x hx => by
    have : x - ε * x = x * (1 - ε) := by ring
    rw [this]
    field_simp
  exact key _ (by linarith)

/-- **Output lower bound for `v ≥ 1` with initialisation allowance `ε`.** Let `μ = N(0, v I)`
with `v ≥ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`, `h' ≥ 0` with all steps
`t_k - t_{k-1} ≥ h'` (`2 ≤ k ≤ N`), the exact score and `σ_k² = β_k/α_k²`. If
`(v - 1) e^{-2(2t_N - t_1)} s_1 ≤ ε` and
`0 ≤ ρ ≤ (e^{2h'} - 1)(1 - e^{-2(t_N - t_1)} s_1)/s_1 - ε`, then
`d ρ²/(2 (1 + ρ)(2 + ρ)) ≤ KL(p_1 ‖ q_1)`. This is of order `h'²` only when some admissible `ρ`
is at least a positive multiple of `h'`; at fixed `v > 1` and fixed horizon no `ρ` is admissible
once `h'` is small. -/
theorem klDiv_output_isoGauss_ddpm_ge_of_one_le {v : ℝ} (hv1 : 1 ≤ v) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {hl ε ρ : ℝ} (hl0 : 0 ≤ hl)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → hl ≤ t k - t (k - 1))
    (hε : (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * gaussVar v t 1 ≤ ε) (hρ : 0 ≤ ρ)
    (hρε : ρ ≤ (Real.exp (2 * hl) - 1) * (1 - Real.exp (-2 * (t N - t 1)) * gaussVar v t 1) /
      gaussVar v t 1 - ε) :
    ENNReal.ofReal (d * ρ ^ 2 / (2 * (1 + ρ) * (2 + ρ))) ≤
      klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (ddpmVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) := by
  have hv : 0 < v := by linarith
  have hs := one_le_gaussVar hv1 t 1
  have hsN := one_le_gaussVar hv1 t N
  refine klDiv_output_isoGauss_ge_of_ge hv h0 ht (ddpmVar t) hN hρ ?_
  have b := algVar_ddpm_sub_gaussVar_ge hv h0 ht hN hstep (K := (gaussVar v t 1)⁻¹)
    (inv_nonneg.2 (by linarith))
    (fun j hj _ => by
      rw [inv_mul_le_one₀ (by linarith)]; exact gaussVar_anti hv1 ht.monotone hj)
  obtain ⟨i1, -⟩ := initTerm_mem_of_one_le hv1 t N
  set s := gaussVar v t 1
  set sN := gaussVar v t N
  set η := Real.exp (2 * hl) - 1
  have hη : 0 ≤ η := by
    simp only [η]; linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * hl)]
  have hE1 := Real.exp_pos (-2 * t 1)
  have hEN := Real.exp_pos (-2 * t N)
  have hE : Real.exp (-2 * (t N - t 1)) = Real.exp (-2 * t N) / Real.exp (-2 * t 1) := by
    rw [← Real.exp_sub]; ring_nf
  -- the drift term
  have hdrift : η * (1 - Real.exp (-2 * (t N - t 1)) * s) ≤
      η * s⁻¹ * (s - Real.exp (-2 * t N) * s ^ 2 / (sN * Real.exp (-2 * t 1))) := by
    have e : s⁻¹ * (s - Real.exp (-2 * t N) * s ^ 2 / (sN * Real.exp (-2 * t 1))) =
        1 - Real.exp (-2 * (t N - t 1)) * s / sN := by
      rw [hE]; field_simp
    rw [mul_assoc, e]
    refine mul_le_mul_of_nonneg_left ?_ hη
    have : Real.exp (-2 * (t N - t 1)) * s / sN ≤ Real.exp (-2 * (t N - t 1)) * s :=
      div_le_self (by positivity) hsN
    linarith
  have hεs : (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * s ^ 2 ≤ ε * s := by
    have := mul_le_mul_of_nonneg_right hε (by linarith : (0 : ℝ) ≤ s)
    nlinarith
  have hρs : s * ρ ≤ η * (1 - Real.exp (-2 * (t N - t 1)) * s) - ε * s := by
    have := mul_le_mul_of_nonneg_left hρε (by linarith : (0 : ℝ) ≤ s)
    have e : s * (η * (1 - Real.exp (-2 * (t N - t 1)) * s) / s - ε) =
        η * (1 - Real.exp (-2 * (t N - t 1)) * s) - ε * s := by
      field_simp
    linarith
  nlinarith

end FormalizeSampling.DiffusionGaussian
