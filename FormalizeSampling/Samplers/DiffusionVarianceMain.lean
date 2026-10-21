module

public import FormalizeSampling.Samplers.DiffusionMain
public import FormalizeSampling.Samplers.DiffusionVarianceStep

/-!
# Reverse-variance choice in DDPM: a `T`-uniform discretisation bound for `σ² = β` and a lower
# bound for `β/α²`, for the output and the path KL

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean`: data law `μ` on `Fin d → ℝ` with finite second
moment `M = ∫ |x|² dμ` (no density assumed), grid `0 = t_0 < t_1 < ⋯ < t_N`, forward OU steps
`F_k(x) = N(α_k x, β_k I)`, marginals `p_k`, exact reverse kernels `R_k`, posterior means `m*_k`,
heat-flow times `u_k = e^{2 t_k} - 1` (`heatTime`), `h_k = t_k - t_{k-1}`. The sampler starts at
`N(0, I)` and uses `Q_k(y) = N(α_k⁻¹ (y + β_k s_k(y)), σ_k² I)`. Path laws
(`Samplers/DiffusionPath.lean`): `truePath μ t N (N-1)` (law of `(x_N, …, x_1)`, which equals
the reversed forward path, `DiffusionPath.fwdPath_eq_truePath`) and `algPath σ2 m hm N (N-1)`
(the sampler's path law); the output KL is at most the path KL
(`DiffusionPath.klDiv_output_le_path`).

**(1) The variance `σ_k² = β_k`, one of the two choices of Ho, Jain and Abbeel (2020).**
`DiffusionPath.klDiv_truePath_betaVar_le`: if `u_{k+1} - u_k ≤ κ u_k` only for `1 ≤ k < m` and
`1 ≤ κ u_m ≤ 1 + κ` (the grid after `m` is arbitrary), then
`KL(path) ≤ KL(p_N ‖ N(0,I)) + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)
  + ∑_{k=2}^N β_k/(2α_k²) ∫ |s_k - ∇ log p_k|² dp_k`,
and the same bound holds for the output KL (`klDiv_output_le_betaVar`).
The discretisation term is **independent of the horizon `t_N = T` and of the number of steps
after `m`** (the whole near-stationary stretch may be a single step). With the exact posterior
mean, `DiffusionPath.klDiv_truePath_betaVar_le_explicit` gives
`KL(path) ≤ e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² M)/2
  + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)`, uniform in `N` and `T` at fixed `t_1`,
`κ`, `d` and `M`; for learned scores a uniform bound also needs control of the score-error sum.
Bounds with no term growing in `T` are known for this variance: Koike (2026, arXiv:2605.18040,
Thm 3.1 and Remark 3.2) for the DDPM sampler, as the Euler–Maruyama scheme of the Föllmer
process, and Conforti–Durmus–Gentiloni Silveri (2023, arXiv:2308.12240, Cor. 1) for an
exponential-integrator scheme with step variance `β_k`.
By contrast, for the variance `σ_k² = β_k/α_k²` of `DiffusionMain` (the exponential-integrator
variance `e^{2h} - 1`):

**(2) Lower bound** (`sum_lintegral_klDiv_revKernel_ddpm_ge`). If `M ≤ d`, then for every grid
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k ≥ (d/2) ∑_{k=2}^N (2 h_k - β_k)`,
where `2h - β = -log(1-β) - β ≥ β²/2`. For a grid with steps of size
`≈ h` up to `T` this grows like `d h T`: the `κ d T` term of Theorem B
(`sum_lintegral_klDiv_revKernel_ddpm_le`) is attained up to a factor `≈ 2` for every normalised
data law, and comes from the variance choice `β_k/α_k²`. (The bound of Benton et al. 2024 also
contains a term of order `κ d T`; Koike, Remark 3.2, makes the same comparison.) In the notation
of Bao et al. (2022, arXiv:2201.06503, App. D, Cor. 3), the KL-optimal reverse variance lies
between the posterior variance `β̃_k` and `β_k/α_k²`, so `β_k/α_k²` is the upper end of that
range.
On path space (`DiffusionPath.klDiv_truePath_ddpm_ge`) this is a lower bound on
`KL(truePath ‖ algPath)` for **every** measurable mean map (in particular the exact score); on a
uniform grid `t_k = t_1 + (k-1)h` it reads `KL(path) ≥ (d/2) (t_N - t_1) (2 - (1 - e^{-2h})/h)`
(`DiffusionPath.klDiv_truePath_ddpm_ge_uniform`), linear in the horizon; the matching upper bound
is `DiffusionPath.klDiv_truePath_ddpm_le` (`Samplers/DiffusionMain.lean`). Since
`KL(p_1 ‖ q_1) ≤ KL(path)`, the lower bound is a statement about the **path**, not the output: the
`T`-linear term cannot be removed by any analysis that bounds `KL(truePath ‖ algPath)`.
That path-KL analyses stop at this order is noted by Benton–De Bortoli–Doucet–Deligiannidis
(2024, arXiv:2308.03686, §4; worst case, point-mass data) and Li–Yan (2024, arXiv:2409.18959,
§3.1), after Chen et al. (2023, arXiv:2209.11215, Thm 7) for the critically damped Langevin
sampler; the bound here holds for every data law with `M ≤ d` and every mean map.

## Main results

* `betaVar`: the variance `σ_k² = β_k` as an `ℝ≥0`.
* `sum_lintegral_klDiv_revKernel_betaVar_le`, `sum_lintegral_klDiv_revKernel_betaVar_le_of_le_mul`:
  the discretisation sum for `σ² = β`.
* `sum_lintegral_klDiv_revKernel_ddpm_ge`: the lower bound for `σ² = β/α²`.
* `DiffusionPath.klDiv_truePath_ddpm_ge`, `DiffusionPath.klDiv_truePath_ddpm_ge_uniform`,
  `DiffusionPath.klDiv_truePath_betaVar_le`, `DiffusionPath.klDiv_truePath_betaVar_le_explicit`:
  the path-KL bounds.
* `klDiv_output_le_betaVar`, `klDiv_output_le_betaVar_explicit`, `tvSup_output_le_betaVar`:
  the end-to-end output bounds.
* `two_mul_sub_div_le_log`: the elementary bound `2 (r - 1)/(r + 1) ≤ log r` for `r ≥ 1`.

## Not proved here

* Output-marginal lower bounds for general data. For exact-score Gaussian data `N(0, v I)`,
  `v ≤ 1`, the output KL of the `β/α²` sampler is bounded uniformly in `T` and below in
  `DiffusionGaussianOutputRate` and `DiffusionGaussianOutputExt`; `showcase/path_kl.py`
  contrasts this with the growing path KL.
* No bound on the score error (it is an input).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.Diffusion

variable {d : ℕ}

/-- The reverse variance `σ_k² = β_k = 1 - α_k²`, one of the two choices of Ho, Jain and Abbeel
(2020), as an element of `ℝ≥0`. -/
noncomputable def betaVar (t : ℕ → ℝ) (k : ℕ) : ℝ≥0 := (fwdVar t k).toNNReal

section Sums

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]

/-- The discretisation sum for `σ² = β` as a real sum in heat-flow coordinates:
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), β_k I)) dp_k = ofReal (∑_{n < N-1} betaStep μ u_{n+1} u_{n+2})`.
-/
theorem sum_lintegral_klDiv_revKernel_betaVar_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) (N : ℕ) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (betaVar t k)) ∂(fwdLaw μ t k) =
      ENNReal.ofReal (∑ n ∈ range (N - 1),
        betaStep μ (heatTime t (n + 1)) (heatTime t (n + 1 + 1))) := by
  have hA : ∀ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
      (Measure.pi fun i => gaussianReal (postMean μ t k y i) (betaVar t k)) ∂(fwdLaw μ t k) =
      ENNReal.ofReal (betaStep μ (heatTime t (k - 1)) (heatTime t k)) := by
    intro k hk
    simp only [mem_Ioc] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [betaVar, (lintegral_klDiv_revKernel_fwdVar_eq μ hμ h0 ht (by omega)).1,
      Nat.add_sub_cancel]
    rfl
  have hnn : ∀ k ∈ Ioc 1 N, 0 ≤ betaStep μ (heatTime t (k - 1)) (heatTime t k) := by
    intro k hk
    simp only [mem_Ioc] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact (lintegral_klDiv_revKernel_fwdVar_eq μ hμ h0 ht (by omega)).2
  rw [sum_congr rfl hA, ← ENNReal.ofReal_sum_of_nonneg hnn]
  congr 1
  rw [← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show N + 1 - (1 + 1) = N - 1 by omega]
  refine sum_congr rfl fun n _ => ?_
  rw [show 1 + 1 + n - 1 = n + 1 by omega, show 1 + 1 + n = n + 1 + 1 by omega]

/-- **Discretisation bound for `σ² = β`.** For data with finite second moment `M`, `t 0 = 0`,
`t` strictly increasing, `1 ≤ m ≤ N`, `κ ≥ 0` and a grid with `u_{k+1} - u_k ≤ κ u_k` for
`1 ≤ k < m` only (`u = heatTime t`):
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), β_k I)) dp_k ≤ (κd/2)(1 + log(u_m/u_1)) + (κ/2)(M-d)⁺
  + (d/2)(log(1 + u_m) - log u_m) + (M-d)⁺/(2 u_m)`. -/
theorem sum_lintegral_klDiv_revKernel_betaVar_le (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {κ : ℝ} (hκ : 0 ≤ κ) {m N : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (betaVar t k)) ∂(fwdLaw μ t k) ≤
      ENNReal.ofReal (κ * d / 2 * (1 + Real.log (heatTime t m / heatTime t 1)) +
        κ / 2 * max (secondMoment μ - d) 0 +
        d / 2 * (Real.log (1 + heatTime t m) - Real.log (heatTime t m)) +
        max (secondMoment μ - d) 0 / (2 * heatTime t m)) := by
  rw [sum_lintegral_klDiv_revKernel_betaVar_eq μ hμ h0 ht N]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := sum_betaStep_le μ hμ (u := fun n => heatTime t (n + 1)) (m := m - 1) (n := N - 1)
    (by omega) hκ (heatTime_pos h0 ht le_rfl)
    (fun n _ => heatTime_mono ht.monotone (by omega))
    (fun n hn => hgrid (n + 1) (by omega) (by omega))
  simpa only [show m - 1 + 1 = m by omega, zero_add] using h

/-- `1 ≤ κ u_m` with `m ≥ 1` forces `κ > 0` (`u_m > 0` for `t 0 = 0`, `t` strictly
increasing). -/
theorem pos_of_one_le_mul_heatTime {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {κ : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (hm1 : 1 ≤ κ * heatTime t m) : 0 < κ := by
  have hu := heatTime_pos h0 ht hm
  by_contra hc
  have : κ * heatTime t m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hu.le
  linarith

/-- **Discretisation bound for `σ² = β`, headline form.** Under the hypotheses of
`sum_lintegral_klDiv_revKernel_betaVar_le` (without the sign condition on `κ`) and
`1 ≤ κ u_m ≤ 1 + κ` (which forces `κ > 0`):
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), β_k I)) dp_k ≤
  (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)`, for every `N ≥ m` and every continuation
of the grid after `m`. -/
theorem sum_lintegral_klDiv_revKernel_betaVar_le_of_le_mul
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (hm1 : 1 ≤ κ * heatTime t m) (hm2 : κ * heatTime t m ≤ 1 + κ) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (betaVar t k)) ∂(fwdLaw μ t k) ≤
      ENNReal.ofReal (κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
        2 * max (secondMoment μ - d) 0)) := by
  rw [sum_lintegral_klDiv_revKernel_betaVar_eq μ hμ h0 ht N]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := sum_betaStep_le_of_le_mul μ hμ (u := fun n => heatTime t (n + 1)) (m := m - 1)
    (n := N - 1) (by omega) (heatTime_pos h0 ht le_rfl)
    (fun n _ => heatTime_mono ht.monotone (by omega))
    (fun n hn => hgrid (n + 1) (by omega) (by omega))
    (by simpa only [show m - 1 + 1 = m by omega] using hm1)
    (by simpa only [show m - 1 + 1 = m by omega] using hm2)
  simpa only [zero_add] using h

/-- **Lower bound for the variance `σ² = β/α²` on normalised data.** If the data law has
`M = ∫ |x|² dμ ≤ d` (e.g. data in `[-1, 1]^d`), `t 0 = 0` and `t` strictly increasing, then for
every `N`:
`(d/2) ∑_{k=2}^N (2 (t_k - t_{k-1}) - β_k) ≤ ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k`.
Each summand `2h - β = -log(1 - β) - β` is the exact per-step excess of `β/α²` over `β` up to a
nonnegative Fisher-information term (`entropyStep_sub_betaStep`); `Cramér–Rao`
(`sq_le_mul_heatFisherInfo`) makes that term nonnegative. -/
theorem sum_lintegral_klDiv_revKernel_ddpm_ge (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (hM : secondMoment μ ≤ d) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) (N : ℕ) :
    ENNReal.ofReal (d / 2 * ∑ k ∈ Ioc 1 N, (2 * (t k - t (k - 1)) - fwdVar t k)) ≤
      ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) := by
  have hψ : ∀ k, 0 ≤ 2 * (t k - t (k - 1)) - fwdVar t k := by
    intro k
    have := Real.add_one_le_exp (-2 * (t k - t (k - 1)))
    rw [fwdVar, fwdScale_sq]
    simp only [mul_one] at *
    linarith
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (by positivity) (hψ k)]
  refine Finset.sum_le_sum fun k hk => ?_
  simp only [mem_Ioc] at hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [lintegral_klDiv_revKernel_ddpm_eq μ hμ h0 ht (by omega)]
  refine ENNReal.ofReal_le_ofReal ?_
  set a := Real.exp (2 * t j) - 1 with ha
  set b := Real.exp (2 * t (j + 1)) - 1 with hb
  have hj0 : 0 < t j := h0 ▸ ht (by omega : 0 < j)
  have hapos : 0 < a := by
    simp only [ha]; refine sub_pos.2 ?_; rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hab : a ≤ b := by
    simp only [ha, hb]
    exact sub_le_sub_right (Real.exp_le_exp.2 (by linarith [ht (Nat.lt_succ_self j)])) _
  have h1 := betaStep_add_le_entropyStep μ hμ hM hapos hab
  have h2 := (lintegral_klDiv_revKernel_fwdVar_eq μ hμ h0 ht (by omega : 1 ≤ j)).2
  have hlog : Real.log ((1 + b) / (1 + a)) = 2 * (t (j + 1) - t j) := by
    simp only [ha, hb, add_sub_cancel]
    rw [← Real.exp_sub, Real.log_exp]; ring
  have hβE : fwdVar t (j + 1) * Real.exp (2 * t (j + 1)) = b - a := by
    have := fwdVar_mul_exp t (j + 1)
    rw [Nat.add_sub_cancel] at this
    rw [this, ha, hb]
  have hβ : (b - a) / (1 + b) = fwdVar t (j + 1) := by
    rw [div_eq_iff (by simp only [hb, add_sub_cancel]; positivity), ← hβE, hb]
    ring
  rw [hlog, hβ] at h1
  rw [Nat.add_sub_cancel]
  linarith

end Sums

/-- The discretisation constant `(κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)` is `≥ 0` when
`κ > 0` and `κ u_1 ≤ 1 + κ`. -/
theorem betaDiscBound_nonneg (μ : Measure (Fin d → ℝ)) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {κ : ℝ} (hκ : 0 < κ) (h1 : κ * heatTime t 1 ≤ 1 + κ) :
    0 ≤ κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
      2 * max (secondMoment μ - d) 0) := by
  have hu := heatTime_pos h0 ht le_rfl
  have : 0 ≤ Real.log ((1 + κ) / (κ * heatTime t 1)) :=
    Real.log_nonneg ((one_le_div (by positivity)).2 h1)
  have : 0 ≤ max (secondMoment μ - d) 0 := le_max_right _ _
  positivity

end FormalizeSampling.DiffusionDiscretization

/-! ### The path KL -/

namespace FormalizeSampling.DiffusionPath

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization

variable {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]

/-- **Path-KL lower bound for `σ² = β/α²`.** If the data has finite second moment
`M = ∫ |x|² dμ ≤ d`, `t 0 = 0` and `t` is strictly increasing, then for **every** family of
measurable mean maps `m_k` (in particular the exact posterior mean `m*_k`, i.e. the exact score)
and every `N`:
`(d/2) ∑_{k=2}^N (2 (t_k - t_{k-1}) - β_k) ≤ KL(truePath μ t N (N-1) ‖ algPath (β/α²) m N (N-1))`.
-/
theorem klDiv_truePath_ddpm_ge (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (hM : secondMoment μ ≤ d) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hm : ∀ k, Measurable (m k)) (N : ℕ) :
    ENNReal.ofReal (d / 2 * ∑ k ∈ Ioc 1 N, (2 * (t k - t (k - 1)) - fwdVar t k)) ≤
      klDiv (truePath μ t N (N - 1)) (algPath (ddpmVar t) m hm N (N - 1)) := by
  rw [klDiv_truePath_eq_disc_add_meanErr μ hμ t (ddpmVar t)
    (fun k hk => ddpmVar_ne_zero ht (by simp only [mem_Ioc] at hk; omega)) m hm]
  exact (sum_lintegral_klDiv_revKernel_ddpm_ge μ hμ hM h0 ht N).trans
    (le_add_self.trans le_self_add)

/-- **The path KL of the `σ² = β/α²` sampler grows linearly in the horizon.** Under the
hypotheses of `klDiv_truePath_ddpm_ge`, if moreover `N ≥ 1` and the grid is uniform after `t_1`,
`t_k = t_1 + (k - 1) h` for `1 ≤ k ≤ N` with `h > 0`, then for every measurable mean map:
`(d/2) (t_N - t_1) (2 - (1 - e^{-2h})/h) ≤ KL(truePath ‖ algPath (β/α²) m)`.
The factor `2 - (1 - e^{-2h})/h` is positive (`≈ 2h` for small `h`), so at fixed step size the
lower bound is linear in `T = t_N`. -/
theorem klDiv_truePath_ddpm_ge_uniform (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    (hM : secondMoment μ ≤ d) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hm : ∀ k, Measurable (m k)) {N : ℕ} (hN : 1 ≤ N)
    {h : ℝ} (hh : 0 < h) (hunif : ∀ k, 1 ≤ k → k ≤ N → t k = t 1 + ((k : ℝ) - 1) * h) :
    ENNReal.ofReal (d / 2 * (t N - t 1) * (2 - (1 - Real.exp (-2 * h)) / h)) ≤
      klDiv (truePath μ t N (N - 1)) (algPath (ddpmVar t) m hm N (N - 1)) := by
  refine le_of_eq_of_le ?_ (klDiv_truePath_ddpm_ge μ hμ hM h0 ht m hm N)
  congr 1
  have hterm : ∀ k ∈ Ioc 1 N, 2 * (t k - t (k - 1)) - fwdVar t k =
      2 * h - (1 - Real.exp (-2 * h)) := by
    intro k hk
    simp only [mem_Ioc] at hk
    have hstep : t k - t (k - 1) = h := by
      rw [hunif k (by omega) hk.2, hunif (k - 1) (by omega) (by omega),
        Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast; ring
    rw [fwdVar, fwdScale_sq, hstep, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
    hunif N hN le_rfl, Nat.cast_sub hN]
  field_simp
  push_cast
  ring

/-- **Path-KL bound with a `T`-uniform discretisation term for `σ² = β`, learned score.**
For data with finite second moment `M`, `t 0 = 0`, `t` strictly increasing,
`1 ≤ m ≤ N`, a grid with
`u_{k+1} - u_k ≤ κ u_k` for `1 ≤ k < m` and `1 ≤ κ u_m ≤ 1 + κ` (the grid after `m` is
arbitrary) and measurable learned scores `s`, the sampler with `σ_k² = β_k` satisfies
`KL(truePath ‖ algPath) ≤ KL(p_N ‖ N(0,I)) + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)
  + ∑_{k=2}^N β_k/(2α_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`.
Uniform control of the total path KL also requires control of the score-error sum. -/
theorem klDiv_truePath_betaVar_le (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ}
    (h0 : t 0 = 0) (ht : StrictMono t) {κ : ℝ} {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (hm1 : 1 ≤ κ * heatTime t m) (hm2 : κ * heatTime t m ≤ 1 + κ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) :
    klDiv (truePath μ t N (N - 1))
        (algPath (betaVar t) (scoreMean t s) (measurable_scoreMean t hs) N (N - 1)) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ENNReal.ofReal (κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
          2 * max (secondMoment μ - d) 0)) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / (2 * fwdScale t k ^ 2)) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) := by
  have hσ2 : ∀ k ∈ Ioc 1 N, betaVar t k ≠ 0 := fun k hk => by
    simp only [mem_Ioc] at hk
    simpa [betaVar, Real.toNNReal_eq_zero, not_le] using
      fwdVar_pos_of_strictMono ht (k := k) (by omega)
  rw [klDiv_truePath_eq_score μ hμ ht (betaVar t) hσ2 s hs]
  have hw : ∑ k ∈ Ioc 1 N,
      ENNReal.ofReal (fwdVar t k ^ 2 / (2 * fwdScale t k ^ 2 * betaVar t k)) *
        ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
          ∂(fwdLaw μ t k) =
      ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / (2 * fwdScale t k ^ 2)) *
        ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
          ∂(fwdLaw μ t k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [mem_Ioc] at hk
    have hβ := fwdVar_pos_of_strictMono ht (k := k) (by omega)
    have hα := fwdScale_pos t k
    rw [betaVar, Real.coe_toNNReal _ hβ.le]
    congr 2
    field_simp
  rw [hw]
  gcongr
  exact sum_lintegral_klDiv_revKernel_betaVar_le_of_le_mul μ hμ h0 ht hm hmN hgrid hm1 hm2

/-- **`T`-uniform path-KL bound for `σ² = β`, exact posterior mean, fully explicit.** For data
with finite second moment `M`, under the grid hypotheses of `klDiv_truePath_betaVar_le`, the
sampler `Q_k(y) = N(m*_k(y), β_k I)` with the exact posterior mean (the exact score) satisfies
`KL(truePath ‖ algPath) ≤ e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² M)/2
  + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)`
(`initBound μ t N` + discretisation constant), uniformly bounded in `N` and `T = t_N` at
fixed `t_1`, `κ`, `d` and `M` (`initBound` is decreasing in `t_N`). -/
theorem klDiv_truePath_betaVar_le_explicit (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {κ : ℝ} {m N : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (hm1 : 1 ≤ κ * heatTime t m) (hm2 : κ * heatTime t m ≤ 1 + κ) :
    klDiv (truePath μ t N (N - 1))
        (algPath (betaVar t) (postMean μ t) (measurable_postMean μ t) N (N - 1)) ≤
      ENNReal.ofReal (initBound μ t N +
        κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
          2 * max (secondMoment μ - d) 0)) := by
  have hκ := pos_of_one_le_mul_heatTime h0 ht hm hm1
  rw [klDiv_truePath_algPath, ENNReal.ofReal_add (initBound_nonneg μ (ht zero_lt_one) N)
    (betaDiscBound_nonneg μ h0 ht hκ
      ((mul_le_mul_of_nonneg_left (heatTime_mono ht.monotone hm) hκ.le).trans hm2))]
  gcongr
  · exact klDiv_fwdLaw_le_init μ hμ ht (hm.trans hmN)
  · exact sum_lintegral_klDiv_revKernel_betaVar_le_of_le_mul μ hμ h0 ht hm hmN hgrid hm1 hm2

end FormalizeSampling.DiffusionPath

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionPath

variable {d : ℕ}

/-! ### The sampler with the variance `σ² = β` (one of the two choices of Ho, Jain, Abbeel) -/

/-- **Main theorem: KL bound with a `T`-uniform discretisation term for the DDPM sampler with
`σ_k² = β_k`.** For data with finite second moment `M`, `t 0 = 0`, `t` strictly increasing,
`1 ≤ m ≤ N`, a grid with
`u_{k+1} - u_k ≤ κ u_k` for `1 ≤ k < m` and `1 ≤ κ u_m ≤ 1 + κ` (`u = heatTime t`; the grid
after `m` is arbitrary; these force `κ > 0`), and any measurable learned score `s`, the DDPM
sampler
`Q_k(y) = N(α_k⁻¹ (y + β_k s_k(y)), β_k I)` started at `N(0, I)` satisfies
`KL(p_1 ‖ q_1) ≤ KL(p_N ‖ N(0,I)) + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺)
  + ∑_{k=2}^N β_k/(2α_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)`.
The discretisation term depends neither on `T = t_N` nor on `N`. Uniform control of the total
output KL also requires control of the score-error sum. -/
theorem klDiv_output_le_betaVar (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (hm1 : 1 ≤ κ * heatTime t m) (hm2 : κ * heatTime t m ≤ 1 + κ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)) :
    klDiv (fwdLaw μ t 1) (algLaw (betaVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ENNReal.ofReal (κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
          2 * max (secondMoment μ - d) 0)) +
        ∑ k ∈ Ioc 1 N, ENNReal.ofReal (fwdVar t k / (2 * fwdScale t k ^ 2)) *
          ∫⁻ y, ENNReal.ofReal (∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2)
            ∂(fwdLaw μ t k) :=
  (klDiv_output_le_path μ t _ _ _ (hm.trans hmN)).trans
    (klDiv_truePath_betaVar_le μ hμ h0 ht hm hmN hgrid hm1 hm2 s hs)

/-- The score-error term for `σ² = β`:
`∑_{k=2}^N β_k/(2α_k²) ∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y)` (`scoreErrW` with weights
`β_k/(2α_k²)`). -/
noncomputable def scoreErrBeta (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) : ℝ :=
  scoreErrW μ t (fun k => fwdVar t k / (2 * fwdScale t k ^ 2)) s N

/-- **Fully explicit KL bound for `σ² = β`.** Under the hypotheses of `klDiv_output_le_betaVar`,
if each score error is `p_k`-integrable (`2 ≤ k ≤ N`):
`KL(p_1 ‖ q_1) ≤ e^{-2(t_N - t_1)} (d (β_1 - 1 - log β_1) + α_1² ∫ |x|² dμ) / 2
  + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺) + ∑_{k=2}^N β_k/(2α_k²) ∫ |s_k - ∇ log p_k|²`.
-/
theorem klDiv_output_le_betaVar_explicit (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (hm1 : 1 ≤ κ * heatTime t m) (hm2 : κ * heatTime t m ≤ 1 + κ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k)) :
    klDiv (fwdLaw μ t 1) (algLaw (betaVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      ENNReal.ofReal (initBound μ t N +
        κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
          2 * max (secondMoment μ - d) 0) + scoreErrBeta μ t s N) := by
  have hκ := pos_of_one_le_mul_heatTime h0 ht hm hm1
  exact klDiv_le_initBound_add μ hμ ht (hm.trans hmN) (betaDiscBound_nonneg μ h0 ht hκ
      ((mul_le_mul_of_nonneg_left (heatTime_mono ht.monotone hm) hκ.le).trans hm2))
    (fun k hk => div_nonneg (fwdVar_pos_of_strictMono ht (by simp only [mem_Ioc] at hk; omega)).le
      (by positivity)) hsint (klDiv_output_le_betaVar μ hμ h0 ht hm hmN hgrid hm1 hm2 s hs)

/-- **TV corollary (Pinsker) for `σ² = β`.** Under the hypotheses of
`klDiv_output_le_betaVar_explicit`:
`TV(p_1, q_1) ≤ √((I + (κ/2)(d (2 + log((1+κ)/(κ u_1))) + 2 (M - d)⁺) + E) / 2)`, with `I` the
initialisation constant `initBound` and `E = scoreErrBeta`. -/
theorem tvSup_output_le_betaVar (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < m → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    (hm1 : 1 ≤ κ * heatTime t m) (hm2 : κ * heatTime t m ≤ 1 + κ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
    (hsint : ∀ k ∈ Ioc 1 N, Integrable
      (fun y => ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2) (fwdLaw μ t k)) :
    TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw (betaVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
      Real.sqrt ((initBound μ t N +
        κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * heatTime t 1))) +
          2 * max (secondMoment μ - d) 0) + scoreErrBeta μ t s N) / 2) :=
  tvSup_le_sqrt_of_klDiv_le
    (klDiv_output_le_betaVar_explicit μ hμ h0 ht hm hmN hgrid hm1 hm2 s hs hsint)

/-- `2 (r - 1)/(r + 1) ≤ log r` for `r ≥ 1`. -/
theorem two_mul_sub_div_le_log {r : ℝ} (hr : 1 ≤ r) : 2 * (r - 1) / (r + 1) ≤ Real.log r := by
  set g : ℝ → ℝ := fun s => Real.log s - 2 * (s - 1) / (s + 1) with hg
  have hgd : ∀ s ∈ Set.Ici (1 : ℝ), HasDerivAt g
      (s⁻¹ - (2 * (s + 1) - 2 * (s - 1) * 1) / (s + 1) ^ 2) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
    have h1 : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 s := by
      simpa using ((hasDerivAt_id s).sub_const 1).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => s + 1) 1 s := by
      simpa using (hasDerivAt_id s).add_const (1 : ℝ)
    exact (Real.hasDerivAt_log hs0.ne').sub (h1.div h2 (by linarith))
  have hmono : MonotoneOn g (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun s hs => (hgd s hs).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ici]
      exact fun s hs => (hgd s (Set.mem_Ici.2 (le_of_lt hs))).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Ici]
      intro s hs
      have hs1 : 1 < s := hs
      rw [(hgd s (Set.mem_Ici.2 hs1.le)).deriv]
      have hs0 : 0 < s := by linarith
      have e : s⁻¹ - (2 * (s + 1) - 2 * (s - 1) * 1) / (s + 1) ^ 2 =
          (s - 1) ^ 2 / (s * (s + 1) ^ 2) := by
        field_simp; ring
      rw [e]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr) hr
  simp only [hg, Real.log_one, sub_self, mul_zero, zero_div] at this
  linarith

end FormalizeSampling.DiffusionDiscretization
