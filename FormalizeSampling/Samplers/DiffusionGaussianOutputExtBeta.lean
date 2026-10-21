module

public import FormalizeSampling.Samplers.DiffusionGaussianOutputExtLarge

/-!
# Output KL of exact-score DDPM on Gaussian data with reverse variance `σ² = β`

Status: **Verified**.

Setting of `Samplers/DiffusionGaussianOutputRate.lean` (DF-8) but with the reverse variance
`σ_k² = β_k = 1 - e^{-2h_k}` (`betaVar`, `Samplers/DiffusionVarianceMain.lean`) instead of
`β_k/α_k²`. Data `μ = N(0, v I)`, exact score, forward variances `s_k`, sampler variances
`w_k` (`w_N = 1`, `w_{k-1} = c_k² w_k + β_k`), `φ_k = e^{-2t_k}/s_k²`, `G_k = e^{-2t_k}/s_k`.

**Exact one-step identity** (`errWeight_mul_beta_sub` in the general identity
`errWeight_mul_sub_eq_gen`). The local error is now
`β - τ² = β (1 - s_{k-1}/s_k) = β² (1 - s_{k-1})/s_k`, which carries the factor
`1 - s_{k-1} = (1 - v) e^{-2t_{k-1}}`:
`φ_k (w_k - s_k) = φ_{k+1} (w_{k+1} - s_{k+1}) + (1 - v) β_{k+1} G_k (G_k - G_{k+1})`.

**Telescoped form** (`errWeight_beta_telescope`, `algVar_beta_sub_gaussVar_eq`, any `v > 0`,
steps `≤ h`):
`w_1 - s_1 = ι + (1 - v) D` with `0 ≤ D ≤ (1 - e^{-2h}) e^{-2t_1}` and the same initialisation
term `ι = e^{-2t_N} (1 - s_N) s_1²/(s_N² e^{-2t_1})` as for `β/α²`. In particular for `v = 1`
the sampler is exact: `w_1 = s_1` and `KL(p_1 ‖ q_1) = 0` (`klDiv_output_isoGauss_beta_one`).

**Output KL.** For `0 < v ≤ 1` (`klDiv_output_isoGauss_beta_le`):
`KL(p_1 ‖ q_1) ≤ d (1 - v)² (e^{-2(2t_N - t_1)} + (1 - e^{-2h}) e^{-2t_1})²/(4 s_1²)`.
For `v ≥ 1` and `(v - 1)(e^{-2(2t_N - t_1)} s_1 + (1 - e^{-2h}) e^{-2t_1}/s_1) ≤ ε < 1`
(`klDiv_output_isoGauss_beta_le_of_one_le`): `KL(p_1 ‖ q_1) ≤ d (ε/(1 - ε))²/4`.
These bounds keep the initialisation term explicit. For `v ≠ 1`, `ι ≠ 0` and `ι` does not
depend on the steps, so it does not vanish as `h → 0` at fixed `t_1`, `t_N`; quadratic
total-error scaling requires controlling it as well. For
`v = 1` both error contributions vanish and the sampler is exact.

## Main results

* `betaVar_coe`, `errWeight_mul_beta_sub`, `errWeight_beta_telescope`.
* `algVar_beta_sub_gaussVar_eq`.
* `klDiv_output_isoGauss_beta_le`, `klDiv_output_isoGauss_beta_le_of_one_le`,
  `klDiv_output_isoGauss_beta_one`.

## Not proved here

* A matching lower bound for `σ² = β` (the finite grids in `showcase/gauss_output_ext.py`
  illustrate quadratic decay in a regime with small initialisation error).
* A matching Gaussian path-KL rate for `σ² = β`. `DiffusionPath.klDiv_truePath_betaVar_le`
  (`Samplers/DiffusionVarianceMain.lean`) gives general path upper bounds on its grids, with the
  learned-score error as an additive term.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionGaussian

open FormalizeSampling.Diffusion
  FormalizeSampling.DiffusionDiscretization FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-- On a monotone grid, `σ_k² = β_k` as a real number. -/
theorem betaVar_coe {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ) : (betaVar t k : ℝ) = fwdVar t k :=
  Real.coe_toNNReal _ (fwdVar_nonneg_of_monotone ht k)

/-- **Local error for `σ² = β`.** On a monotone grid, for `s_k, s_{k+1} > 0`:
`φ_k (β_{k+1} - s_k β_{k+1}/s_{k+1}) = (1 - v) β_{k+1} G_k (G_k - G_{k+1})`. With
`errWeight_mul_sub_eq_gen` this is the one-step error identity for `σ² = β`. -/
theorem errWeight_mul_beta_sub (v : ℝ) {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ)
    (hs : 0 < gaussVar v t k) (hs' : 0 < gaussVar v t (k + 1)) :
    errWeight v t k *
        (betaVar t (k + 1) - gaussVar v t k * fwdVar t (k + 1) / gaussVar v t (k + 1)) =
      (1 - v) * fwdVar t (k + 1) * gaussPot v t k * (gaussPot v t k - gaussPot v t (k + 1)) := by
  have h1s : 1 - gaussVar v t k = (1 - v) * Real.exp (-2 * t k) := by unfold gaussVar; ring
  rw [gaussPot_sub_succ v t k hs hs', betaVar_coe ht, errWeight, gaussPot,
    show (1 - v) = (1 - gaussVar v t k) / Real.exp (-2 * t k) by
      rw [h1s, mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]]
  have hrec := gaussVar_succ v t k
  rw [fwdVar] at hrec ⊢
  field_simp
  rw [hrec]
  ring

/-- **Telescoped identity and bounds for `σ² = β`.** Let `v > 0`, `t_0 = 0`, `t` strictly
increasing, all steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`). For `1 ≤ k ≤ N` there is `S` with
`φ_k (w_k - s_k) = φ_N (1 - s_N) + (1 - v) S` and `0 ≤ S ≤ (1 - e^{-2h}) G_k (G_k - G_N)`;
moreover `0 ≤ G_N ≤ G_k`. -/
theorem errWeight_beta_telescope {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} {h : ℝ} (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (∃ S, 0 ≤ S ∧ S ≤ (1 - Real.exp (-2 * h)) * gaussPot v t k *
        (gaussPot v t k - gaussPot v t N) ∧
      errWeight v t k * (algVar (gaussGain v t) (betaVar t) N k - gaussVar v t k) =
        errWeight v t N * (1 - gaussVar v t N) + (1 - v) * S) ∧
      0 ≤ gaussPot v t N ∧ gaussPot v t N ≤ gaussPot v t k := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  have hanti : Antitone (gaussPot v t) := antitone_nat_of_succ_le fun j =>
    gaussPot_succ_le v ht.monotone j (hpos _) (hpos _)
  have hG : ∀ j, 0 ≤ gaussPot v t j := fun j => by unfold gaussPot; have := hpos j; positivity
  refine ⟨⟨∑ j ∈ Ico k N, fwdVar t (j + 1) * gaussPot v t j *
    (gaussPot v t j - gaussPot v t (j + 1)), Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (fwdVar_nonneg_of_monotone ht.monotone _) (hG j))
      (sub_nonneg.2 (hanti (Nat.le_succ j))), ?_, ?_⟩, hG N, hanti hkN⟩
  · rw [← sum_gaussPot_sub v t hkN, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_
      (sub_nonneg.2 (hanti (Nat.le_succ j)))
    simp only [mem_Ico] at hj
    have hβ : fwdVar t (j + 1) ≤ 1 - Real.exp (-2 * h) := by
      rw [fwdVar, fwdScale_sq, Nat.add_sub_cancel]
      have := hstep (j + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at this
      linarith [Real.exp_le_exp.2 (by linarith : -2 * h ≤ -2 * 1 * (t (j + 1) - t j))]
    exact mul_le_mul hβ (hanti hj.1) (hG j) ((fwdVar_nonneg_of_monotone ht.monotone _).trans hβ)
  · rw [errWeight_telescope hv h0 ht.monotone _ hkN, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [errWeight_mul_beta_sub v ht.monotone j (hpos _) (hpos _)]
    ring

/-- **Accumulated error for `σ² = β` (any `v > 0`).** Let `v > 0`, `t_0 = 0`, `t` strictly
increasing, `N ≥ 1`, `h ≥ 0`, all steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`). Then the output
variance `w_1` of the exact-score sampler with `σ_k² = β_k` satisfies
`w_1 - s_1 = ι + (1 - v) D` for some `0 ≤ D ≤ (1 - e^{-2h}) e^{-2t_1}`, where
`ι = e^{-2t_N} (1 - s_N) s_1²/(s_N² e^{-2t_1})`. -/
theorem algVar_beta_sub_gaussVar_eq {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h) :
    ∃ D, 0 ≤ D ∧ D ≤ (1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1) ∧
      algVar (gaussGain v t) (betaVar t) N 1 - gaussVar v t 1 =
        Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
          (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) + (1 - v) * D := by
  have hpos : ∀ j, 0 < gaussVar v t j := fun j => gaussVar_pos hv (h0 ▸ ht.monotone (Nat.zero_le j))
  obtain ⟨⟨S, hS0, hS1, hS⟩, hGN, -⟩ := errWeight_beta_telescope hv h0 ht hstep le_rfl hN
  have hφ : 0 < errWeight v t 1 := by unfold errWeight; have := hpos 1; positivity
  have hs1 := hpos 1
  have hsN := hpos N
  have hE1 := Real.exp_pos (-2 * t 1)
  refine ⟨S / errWeight v t 1, div_nonneg hS0 hφ.le, ?_, ?_⟩
  · rw [div_le_iff₀ hφ]
    have hc : S ≤ (1 - Real.exp (-2 * h)) * gaussPot v t 1 * gaussPot v t 1 := by
      have hc : 0 ≤ 1 - Real.exp (-2 * h) := by
        rw [sub_nonneg, Real.exp_le_one_iff]; linarith
      have hG1 : 0 ≤ gaussPot v t 1 := by unfold gaussPot; positivity
      have := mul_nonneg hc hG1
      nlinarith
    have e : (1 - Real.exp (-2 * h)) * gaussPot v t 1 * gaussPot v t 1 =
        (1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1) * errWeight v t 1 := by
      unfold gaussPot errWeight; field_simp
    linarith
  · have e : Real.exp (-2 * t N) * (1 - gaussVar v t N) * gaussVar v t 1 ^ 2 /
        (gaussVar v t N ^ 2 * Real.exp (-2 * t 1)) + (1 - v) * (S / errWeight v t 1) =
        (errWeight v t N * (1 - gaussVar v t N) + (1 - v) * S) / errWeight v t 1 := by
      unfold errWeight; field_simp
    rw [e, ← hS, mul_div_cancel_left₀ _ hφ.ne']

/-- **Output upper bound for `σ² = β`, `v ≤ 1`, with initialisation term.** Let
`μ = N(0, v I)` with `0 < v ≤ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`, `h ≥ 0`, all
steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`), the exact score and `σ_k² = β_k` (`betaVar`). Then
`KL(p_1 ‖ q_1) ≤ d (1 - v)² (e^{-2(2t_N - t_1)} + (1 - e^{-2h}) e^{-2t_1})²/(4 s_1²)`. For
`v < 1` the initialisation part `e^{-2(2t_N - t_1)}` does not vanish as `h → 0` at fixed `t_1`,
`t_N`. -/
theorem klDiv_output_isoGauss_beta_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h) :
    klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (betaVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
      ENNReal.ofReal (d * ((1 - v) * (Real.exp (-2 * (2 * t N - t 1)) +
        (1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1))) ^ 2 / (4 * gaussVar v t 1 ^ 2)) := by
  have hs := gaussVar_pos hv (t := t) (k := 1) (h0 ▸ ht.monotone (Nat.zero_le 1))
  obtain ⟨D, hD0, hD1, hw⟩ := algVar_beta_sub_gaussVar_eq hv h0 ht hN hh hstep
  obtain ⟨i0, i1⟩ := initTerm_mem_of_le_one hv hv1 h0 ht.monotone hN
  have h1v : 0 ≤ 1 - v := by linarith
  have hDv := mul_le_mul_of_nonneg_left hD1 h1v
  have hDv0 := mul_nonneg h1v hD0
  set a := (1 - v) * (Real.exp (-2 * (2 * t N - t 1)) +
    (1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1))
  refine le_trans (klDiv_output_isoGauss_le_of_mem hv h0 ht (betaVar t) hN (a := a) (b := 0)
    hs (by linarith) (by simp only [a]; nlinarith)) ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero]
  ring

/-- **Output upper bound for `σ² = β`, `v ≥ 1`, with initialisation allowance `ε`.** Let
`μ = N(0, v I)` with `v ≥ 1`, `t_0 = 0`, `t` strictly increasing, `N ≥ 1`, `h ≥ 0`, all
steps `t_k - t_{k-1} ≤ h` (`2 ≤ k ≤ N`), the exact score and `σ_k² = β_k`. If
`(v - 1)(e^{-2(2t_N - t_1)} s_1 + (1 - e^{-2h}) e^{-2t_1}/s_1) ≤ ε < 1`, then
`KL(p_1 ‖ q_1) ≤ d (ε/(1 - ε))²/4` (here `w_1 ≤ s_1`: the sampler undershoots). -/
theorem klDiv_output_isoGauss_beta_le_of_one_le {v : ℝ} (hv1 : 1 ≤ v) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {h ε : ℝ} (hh : 0 ≤ h)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → t k - t (k - 1) ≤ h)
    (hε : (v - 1) * (Real.exp (-2 * (2 * t N - t 1)) * gaussVar v t 1 +
      (1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1) / gaussVar v t 1) ≤ ε) (hε1 : ε < 1) :
    klDiv (fwdLaw (isoGauss d v) t 1)
        (algLaw (betaVar t) (scoreMean t (exactScore (isoGauss d v) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) ≤
      ENNReal.ofReal (d * (ε / (1 - ε)) ^ 2 / 4) := by
  have hv : 0 < v := by linarith
  have hs := one_le_gaussVar hv1 t 1
  obtain ⟨D, hD0, hD1, hw⟩ := algVar_beta_sub_gaussVar_eq hv h0 ht hN hh hstep
  obtain ⟨i0, i1⟩ := initTerm_mem_of_one_le hv1 t N
  have hv0 : 0 ≤ v - 1 := by linarith
  have hDv := mul_le_mul_of_nonneg_left hD1 hv0
  have hDv0 := mul_nonneg hv0 hD0
  set s := gaussVar v t 1
  have hεs : (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * s ^ 2 +
      (v - 1) * ((1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1)) ≤ ε * s := by
    have := mul_le_mul_of_nonneg_right hε (by linarith : (0 : ℝ) ≤ s)
    have e : (v - 1) * (Real.exp (-2 * (2 * t N - t 1)) * s +
        (1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1) / s) * s =
        (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * s ^ 2 +
          (v - 1) * ((1 - Real.exp (-2 * h)) * Real.exp (-2 * t 1)) := by
      field_simp
    linarith
  have hε0 : 0 ≤ ε := by
    have : 0 ≤ (v - 1) * Real.exp (-2 * (2 * t N - t 1)) * s ^ 2 := by positivity
    nlinarith
  have hbs : ε * s < s := by nlinarith
  refine le_trans (klDiv_output_isoGauss_le_of_mem hv h0 ht (betaVar t) hN (a := 0) (b := ε * s)
    hbs (by nlinarith) (by nlinarith)) ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have h1ε : 0 < 1 - ε := by linarith
  have key : ∀ x : ℝ, 0 < x → (d : ℝ) * ((0 : ℝ) ^ 2 / x ^ 2 + (ε * x) ^ 2 / (x - ε * x) ^ 2) / 4 =
      d * (ε / (1 - ε)) ^ 2 / 4 := fun x hx => by
    have : x - ε * x = x * (1 - ε) := by ring
    rw [this]
    field_simp
    ring
  exact key _ (by linarith)

/-- **`σ² = β` is exact for `v = 1`.** For `μ = N(0, I)`, `t_0 = 0`, `t` strictly increasing,
`N ≥ 1` (any grid), exact score and `σ_k² = β_k`: `KL(p_1 ‖ q_1) = 0`. -/
theorem klDiv_output_isoGauss_beta_one {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {N : ℕ}
    (hN : 1 ≤ N) :
    klDiv (fwdLaw (isoGauss d 1) t 1)
        (algLaw (betaVar t) (scoreMean t (exactScore (isoGauss d 1) t))
          (measurable_scoreMean t (measurable_exactScore _ t)) N 1) = 0 := by
  have htk : ∀ j, 0 ≤ t j := fun j => h0 ▸ ht.monotone (Nat.zero_le j)
  obtain ⟨D, -, -, hw⟩ := algVar_beta_sub_gaussVar_eq one_pos h0 ht hN (h := t N) (htk N)
    (fun k _ hkN => by linarith [htk (k - 1), ht.monotone hkN])
  have hsN : gaussVar 1 t N = 1 := by unfold gaussVar; ring
  have hs1 : gaussVar 1 t 1 = 1 := by unfold gaussVar; ring
  rw [hsN, hs1] at hw
  have hw1 : algVar (gaussGain 1 t) (betaVar t) N 1 = 1 := by
    have : algVar (gaussGain 1 t) (betaVar t) N 1 - 1 = 0 := by rw [hw]; ring
    linarith
  rw [(klDiv_output_isoGauss_eq one_pos h0 ht (betaVar t) hN (by rw [hw1]; norm_num)).2, hw1,
    hs1]
  simp

end FormalizeSampling.DiffusionGaussian
