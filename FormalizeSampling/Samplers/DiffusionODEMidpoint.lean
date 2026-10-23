module

public import FormalizeSampling.Samplers.DiffusionODELongHorizon
public import FormalizeSampling.Samplers.DiffusionTwoPoint

/-!
# Deterministic reverse sampler on two-point data: a high-noise score error and the midpoint

Status: **Verified** (a separation result; two-point companion of
`Samplers/DiffusionODELongHorizon.lean`).

This module is a formal counterpart, with its own construction, of the phenomenon in the
third-mode figure of the README (`showcase/ode_third_mode.py`,
`showcase/figures/ode_third_mode.png`): the data have two modes, the learned score has a
uniformly small error with a small Lipschitz constant, the deterministic sampler puts output
mass between the two modes, where the data have little, and DDPM driven by the same score is
close to the data. The figure is numerical, and its construction (two Gaussian modes, an error
localised near the midpoint at every noise level, a fine ODE solver) is not formalised; in the
figure the deterministic output keeps the two modes and adds a third at the midpoint. Here the
data are two atoms, the samplers are the discrete exponential-integrator step and DDPM on a
geometric grid, and the error is a linear clamp switched on at high noise only. The
deterministic output collapses onto the midpoint: it puts mass at least `1 - η` on a slab
around the midpoint where `p_1` puts mass at most `η`, so at most `η` of it lies outside the
slab, near the two data modes or elsewhere (`pf_ddpm_midpoint_separation`).

Setting of `Samplers/DiffusionTwoPoint.lean` in dimension one: data `μ = (δ_{-a} + δ_a)/2` on
`Fin 1 → ℝ` (`symTwoPoint fun _ => a`), a grid with `t_0 = 0`, `t` strictly increasing,
`ᾱ_k = e^{-t_k}` (`cumScale`), `v_k = 1 - e^{-2 t_k}` (`cumVar`), and forward marginals
`p_k = (N(-ᾱ_k a, v_k) + N(ᾱ_k a, v_k))/2`. The deterministic sampler is the
exponential-integrator probability-flow step `pfMean`, `m_k(y) = α_k⁻¹ y + b_k s_k(y)` with
`b_k = α_k⁻¹ - 1 = e^{t_k - t_{k-1}} - 1` (`pfCoeff`), and its output is
`q_1 = algLaw 0 (pfMean t s) N 1 = Φ_1 # N(0, 1)`, `Φ_1 = m_2 ∘ ⋯ ∘ m_N`. With the exact score
the step is the scalar map `m*_k = pfTwoPoint t a k`: odd, increasing, with lower slope
`α_k⁻¹ - b_k/v_k ≥ 1/2` (`half_le_inv_fwdScale_sub_pfCoeff_div_cumVar`). The stochastic
sampler is DDPM, `algLaw (ddpmVar t) (scoreMean t s)`, driven by the same learned score.

## The construction

The learned score is `s_k = ∇ log p_k + E_k` with `E_k(y) = -λ clip_R(y_0)` (`clampErr`) at
the high-noise steps `k > K` and `E_k = 0` at the steps `k ≤ K` (`clampErrAfter`,
`clampScoreAfter`). With `λ = ε / R` and `R ≥ 1` the score error is at most `ε` in sup norm and
the error field is `ε`-Lipschitz at every step (`clampScoreAfter_accuracy`).

* **Neutral phase** (`K < k ≤ N`). Assume `(ᾱ_k a)² / v_k² ≤ λ/2` (it holds once
  `t_k ≥ log(2 + 8 a²/λ) / 2`, `sq_cumScale_mul_div_sq_cumVar_le`) and `b_k λ ≤ 1`. On the window
  `|y_0| ≤ R` the perturbed step is `y_0 ↦ m*_k(y_0) - b_k λ y_0`. For `x ≥ 0`,
  `m*_k(x) ≤ (1 + b_k (ᾱ_k a)²/v_k²) x` (as `α_k⁻¹ = 1 + b_k` and `v_k ≤ 1`) and
  `m*_k(x) ≥ x/2`; with oddness, `|m_k(y)_0| ≤ (1 - b_k λ/2) |y_0|`. The window is invariant and
  the flow `Φ_K = m_{K+1} ∘ ⋯ ∘ m_N` shrinks it by
  `∏_{K < k ≤ N} (1 - b_k λ/2) ≤ exp(-(λ/2)(t_N - t_K))` (`b_k ≥ t_k - t_{k-1}`).
* **Phase without error** (`1 < k ≤ K`). `Φ_1 = Φ*^K_1 ∘ Φ_K` with the exact-score flow
  `Φ*^K_1 = m*_2 ∘ ⋯ ∘ m*_K`, which is odd, fixes `0` and is Lipschitz with constant
  `∏_{1 < k ≤ K} L_k ≤ C = exp(a²/(e^{2 t_1} - 1))` on every grid whose steps are at most
  `log 2` (`DiffusionTwoPoint.prod_lipTwoPoint_le`: `L_k ≤ 1 + b_k a² ᾱ_k²/v_k²`, and these
  increments telescope against `F(s) = -1/(2 (e^{2s} - 1))`). Every window point is therefore
  mapped into `[-ρ, ρ]` as soon as `C exp(-(λ/2)(t_N - t_K)) R ≤ ρ`.
* **Collapse.** The slab `G = {|x_0| ≤ ρ}` around the midpoint of the two atoms then has
  `q_1(G) ≥ N(0, 1)([-R, R])`, while `p_1(G) ≤ 2ρ / √(2π v_1)` (the density of `p_1` is at
  most `1/√(2π v_1)`), so `TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - 2ρ / √(2π v_1)`.
* **Parameters.** `R` with `N(0, 1)([-R, R]) ≥ 1 - η`; on the geometric grid `geomGrid u_1 r`,
  `e^{2 t_1} = 1 + u_1`, `v_1 = u_1/(1 + u_1)`, the two Gaussian components of `p_1` are
  centred at `±a/√(1 + u_1)` (the images `ᾱ_1 (±a)` of the atoms) and `C = exp(a²/u_1)`; `ρ`
  with `2ρ / √(2π v_1) ≤ η` and `ρ ≤ a/(2√(1 + u_1))`; `K = max(1, G)`, `G` the largest index
  `k ≤ N` with `t_k < t_* = log(2 + 8 a² R/ε)/2` (`G = 0` if there is none), so that the error
  acts at the steps `k > K` (`exists_switchIndex`). A horizon
  `t_N - t_1 ≥ t_* + (2R/ε) log(C R/ρ)` gives the collapse (`exists_pf_clampScoreAfter_collapse`).
  Since `t_* ≤ (1 + 8 a² R)/ε` for `ε ≤ 1`, the horizon `A₀/ε` with
  `A₀ = 2R log(C R/ρ) + 1 + 8 a² R` suffices, and on a geometric grid with horizon between
  `A₀/ε` and `A₀/ε + c` the DDPM score term `ε² (t_N - t_1)` is at most `ε A₀ + ε² c`; the
  horizon is then at most `A/ε` with `A = A₀ + c + 1`.

## Main results

* Error field and learned score: `clampErrAfter`, `clampScoreAfter`, `clampErrAfter_of_lt`,
  `clampErrAfter_of_le`, `clampScoreAfter_of_le`, `clampScoreAfter_of_lt`, `clampScoreAfter_sub`,
  `clampScoreAfter_sub_eq` (the score error is the field `E_k`), `sum_sq_clampErrAfter_le`,
  `lipschitzWith_clampErrAfter`, `eDist_clampErrAfter_le`,
  `sum_sq_clampScoreAfter_sub_le` (`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ (λ R)²` for all `k`, `y`),
  `clampScoreAfter_accuracy` (`λ = ε/R`, `R ≥ 1`: error `≤ ε`, `ε`-Lipschitz error field),
  `measurable_clampScoreAfter`, `measurable_pfMean_clampScoreAfter`,
  `integrable_sq_clampScoreAfter_sub`.
* `tvSup_ddpm_clampScoreAfter_le_geomGrid`: DDPM with the same score (any data with finite
  second moment) on a geometric grid has
  `TV(p_1, q_1) ≤ √((I + (r - 1) d/2 (1 + (N - 1) log r) + (λ R)² (t_N - t_1)) / 2)`.
* Splitting the flow: `detFlow_eq_comp` (`Φ_k = Φ^K_k ∘ Φ_K` for any maps),
  `detFlow_pf_clampScoreAfter_eq_exact`, `detFlow_pf_clampScoreAfter_eq_comp`.
* One step: `half_le_inv_fwdScale_sub_pfCoeff_div_cumVar`, `abs_mixMap_sub_mul_le` (scalar
  form), `pfMean_clampScoreAfter_symTwoPoint`, `abs_pfMean_clampScoreAfter_symTwoPoint_le`
  (`|m_k(y)_0| ≤ (1 - b_k λ/2) |y_0|` on the window), `sq_cumScale_mul_div_sq_cumVar_le`.
* Neutral phase: `abs_detFlow_clampScoreAfter_symTwoPoint_le_prod`,
  `abs_detFlow_clampScoreAfter_symTwoPoint_le`
  (`|Φ_K(y)_0| ≤ exp(-(λ/2)(t_N - t_K)) |y_0| ≤ R` on the window, on every grid, with
  `DiffusionODELongHorizon.prod_one_sub_pfCoeff_le`).
* Collapse: `abs_detFlow_pf_clampScoreAfter_symTwoPoint_le`
  (`|Φ_1(y)_0| ≤ C exp(-(λ/2)(t_N - t_K)) R` on the window, `C` the Lipschitz constant of
  `Φ*^K_1`), `gaussianReal_Icc_le_ofReal`, `fwdLaw_symTwoPoint_real_abs_le`
  (`p_k(G) ≤ 2ρ / √(2π v_k)`), `le_detOutput_real_abs_le` (`q_1(G) ≥ N(0, 1)([-R, R])`),
  `tvSup_pf_clampScoreAfter_symTwoPoint_ge`
  (`TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - 2ρ / √(2π v_1)`, `C` a parameter).
* Phase without error in coordinates: `abs_detFlow_pf_exactScore_symTwoPoint_sub_le`
  (`C = ∏_{1 < k ≤ K} L_k`, `L_k = lipTwoPoint t a k`) and
  `abs_detFlow_pf_exactScore_symTwoPoint_sub_le_exp` (`C = exp(a²/(e^{2 t_1} - 1))`), with the
  TV bounds `tvSup_pf_clampScoreAfter_symTwoPoint_ge_prod` and
  `tvSup_pf_clampScoreAfter_symTwoPoint_ge_exp`.
* Parameters: `exists_switchIndex`, `exp_two_mul_geomGrid_one`, `cumVar_geomGrid_one`,
  `cumScale_geomGrid_one`, and `exists_pf_clampScoreAfter_collapse` (collapse on every grid with
  steps `≤ log 2` and horizon `t_N - t_1 ≥ t_* + (2R/ε) log(C R/ρ)`, for a switching index
  `K < N` with `t_k ≥ t_*` on `(K, N]`).
* `pf_ddpm_midpoint_separation` (**separation**): for `a > 0` and `η > 0` there is `R ≥ 1`
  such that for every `u_1 > 0` there are `ρ > 0` with `ρ ≤ a/(2√(1 + u_1))`, `A > 0` and
  `ε₀ > 0` such that for every `ε ∈ (0, ε₀]` some geometric grid `geomGrid u_1 r` with horizon
  `t_N - t_1 ≤ A/ε`, `N ≥ 2` and `1 ≤ K < N` give, for one learned score whose error is `≤ ε`
  in sup norm, `ε`-Lipschitz, and zero below the threshold `t_*`: `p_1(G) ≤ η`,
  `q_1^det(G) ≥ 1 - η`, `TV(p_1, q_1^det) ≥ 1 - 2η` and `TV(p_1, q_1^DDPM) ≤ η`. The
  deterministic output collapses onto the midpoint.

Relation to the literature: the neutral phase is modelled on the setting of Li–Di–Gu (2024,
arXiv:2410.14237, Thm 3.1): for the forward OU process started at `N(0, 1)` the law is stationary
and the exact probability-flow velocity vanishes, so a uniformly small score error is not corrected
by the flow. For two atoms the forward law is only close to `N(0, 1)` at high noise and the exact
step only close to the identity; here the error acts over a horizon of order `1/ε` at the high-noise
steps, where `(ᾱ_k a)²/v_k² ≤ λ/2` (`sq_cumScale_mul_div_sq_cumVar_le`), so that on the window the
perturbed step shrinks `|y_0|` by the factor `1 - b_k λ/2` (`abs_mixMap_sub_mul_le`). The region
between the two modes, and the trapping of deterministic trajectories at the midpoint late in
sampling, are described by Ashiq et al. (2026, arXiv:2605.06831). That deterministic samplers
over-concentrate, that this starts at high noise and that the error is retained along the run is
observed by Zhang, Liao, Wu and Zou (2025, arXiv:2508.16154); that a velocity with small training
error can send almost all of the probability-flow ODE's output into a chosen region is shown by
Beltran-Velez et al. (2026, arXiv:2606.19162, Prop. 3.1). That the deterministic flow carries a
mismatch forward while the stochastic sampler forgets it is described by Nie et al. (2024,
arXiv:2311.01410, Thms 3.1–3.2) and Cao et al. (2023, arXiv:2306.02063). Here the neutral phase, the
bound on the expansion of the exact-score flow after it, the collapse and the DDPM upper bound for
the same learned score are formalised for the discrete steps and combined into a separation on
geometric grids.

## Not proved here

* **A collapse, not a third mode.** The deterministic output puts mass at least `1 - η` on the
  slab around the midpoint, so the two data modes are lost; an output that keeps the two modes
  and adds a third, as in the figure, is not proved.
* **Dimension one, two atoms.** The data are `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, not the
  Gaussian modes of the figure; asymmetric, multi-atom or higher-dimensional data are not
  treated. Among deterministic steps only the exponential-integrator step `pfMean` is treated.
* **The shape of `p_1`.** No statement about the density of `p_1` near `0` is made: `p_1(G) ≤ η`
  comes from `ρ ≤ η √(2π v_1)/2`, as every interval of length `2ρ` has `p_1`-mass at most
  `2ρ/√(2π v_1)`, not from a low density of `p_1` at the midpoint.
* **Long horizon.** In the proof the grid horizon lies between `A₀/ε` and `A₀/ε + c`, with
  `A₀ = 2R log(C R/ρ) + 1 + 8 a² R`, `log C = a²/u_1` and `c` independent of `ε`, so it is of
  order `R (log(R/ρ) + a²/u_1 + a²)/ε` (the separation records `t_N - t_1 ≤ A/ε`); the
  statement proved for every grid is `exists_pf_clampScoreAfter_collapse` (horizon
  `t_N - t_1 ≥ t_* + (2R/ε) log(C R/ρ)`). `R` is chosen from `η` by continuity of `N(0, 1)` (no
  explicit rate in `η`);
  `ρ = min(η √(2π v_1)/2, a/(2√(1 + u_1)), 1/2)` is explicit. No bound on the necessary horizon
  is proved: it is not shown that shorter horizons, or an error acting over a shorter time,
  leave `q_1^det` close to `p_1`. The constant `exp(a²/(e^{2 t_1} - 1))` of the phase without
  error is an upper bound and is not shown to be attained.
* **Error switched on only at high noise.** The error vanishes at the steps `k ≤ K` and acts at
  the steps `k > K`; the switching index `K` depends on `ε`, `R` and the grid (the threshold
  `t_*` is of order `log(1/ε)`). An error present at every noise level, as in the figure, is not
  treated. `clip_R` has two kinks, so the error field is Lipschitz but not differentiable, and
  it is piecewise constant in time; smooth profiles are not formalised.
* **No continuous-time statement.** Both samplers are discrete chains on the grid; the
  probability-flow ODE and the reverse SDE in continuous time are not treated.
* The DDPM side is the KL bound of `Samplers/DiffusionMain.lean` through Pinsker; no lower bound
  for DDPM is given.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionODEMidpoint

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
open FormalizeSampling.DiffusionODESeparation FormalizeSampling.DiffusionODELipschitz
open FormalizeSampling.DiffusionODELongHorizon
open FormalizeSampling.DiffusionTwoPoint (symTwoPoint cumScale cumVar mixMap pfTwoPoint lipTwoPoint)
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingChainPi

variable {d : ℕ}

/-! ### The error field switched on at high noise -/

/-- **The error field switched on at high noise.** At step `k` it is the clamp field
`clampErr i₀ λ R` (`E(y)_{i₀} = -λ clip_R(y_{i₀})`) if `k > K`, and `0` if `k ≤ K`. -/
noncomputable def clampErrAfter (i₀ : Fin d) (lam R : ℝ) (K k : ℕ) (y : Fin d → ℝ) :
    Fin d → ℝ :=
  if K < k then clampErr i₀ lam R y else 0

/-- For `k > K` the field is the clamp field `clampErr i₀ λ R`. -/
theorem clampErrAfter_of_lt (i₀ : Fin d) (lam R : ℝ) {K k : ℕ} (h : K < k) :
    clampErrAfter i₀ lam R K k = clampErr i₀ lam R := by
  funext y
  simp [clampErrAfter, h]

/-- For `k ≤ K` the field vanishes. -/
theorem clampErrAfter_of_le (i₀ : Fin d) (lam R : ℝ) {K k : ℕ} (h : k ≤ K) :
    clampErrAfter i₀ lam R K k = 0 := by
  funext y
  simp [clampErrAfter, not_lt.2 h]

/-- The field is continuous at every step. -/
theorem continuous_clampErrAfter (i₀ : Fin d) (lam R : ℝ) (K k : ℕ) :
    Continuous (clampErrAfter i₀ lam R K k) := by
  by_cases h : K < k
  · rw [clampErrAfter_of_lt i₀ lam R h]
    exact continuous_clampErr i₀ lam R
  · rw [clampErrAfter_of_le i₀ lam R (not_lt.1 h)]
    exact continuous_const

/-- **Size of the field.** For `λ ≥ 0`, `R ≥ 0`, every `K`, `k` and `y`:
`∑ᵢ E_k(y)ᵢ² ≤ (λ R)²`. -/
theorem sum_sq_clampErrAfter_le (i₀ : Fin d) {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R)
    (K k : ℕ) (y : Fin d → ℝ) : ∑ i, clampErrAfter i₀ lam R K k y i ^ 2 ≤ (lam * R) ^ 2 := by
  by_cases h : K < k
  · rw [clampErrAfter_of_lt i₀ lam R h]
    exact sum_sq_clampErr_le i₀ hlam hR y
  · rw [clampErrAfter_of_le i₀ lam R (not_lt.1 h)]
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity

/-- **Regularity of the field (sup metric).** For `λ ≥ 0`, at every step `k` the field
`E_k` is `λ`-Lipschitz for the sup metric of `Fin d → ℝ`. -/
theorem lipschitzWith_clampErrAfter (i₀ : Fin d) {lam : ℝ} (hlam : 0 ≤ lam) (R : ℝ)
    (K k : ℕ) : LipschitzWith lam.toNNReal (clampErrAfter i₀ lam R K k) := by
  by_cases h : K < k
  · rw [clampErrAfter_of_lt i₀ lam R h]
    exact lipschitzWith_clampErr i₀ hlam R
  · rw [clampErrAfter_of_le i₀ lam R (not_lt.1 h)]
    exact (LipschitzWith.const (0 : Fin d → ℝ)).weaken zero_le

/-- **Regularity of the field (Euclidean metric).** At every step `k` and for all `x`, `y`:
`|E_k(x) - E_k(y)| ≤ |λ| |x - y|` (Euclidean distance `eDist`). -/
theorem eDist_clampErrAfter_le (i₀ : Fin d) (lam R : ℝ) (K k : ℕ) (x y : Fin d → ℝ) :
    eDist (clampErrAfter i₀ lam R K k x) (clampErrAfter i₀ lam R K k y) ≤ |lam| * eDist x y := by
  by_cases h : K < k
  · rw [clampErrAfter_of_lt i₀ lam R h]
    exact eDist_clampErr_le i₀ lam R x y
  · rw [clampErrAfter_of_le i₀ lam R (not_lt.1 h), Pi.zero_apply, Pi.zero_apply, eDist_self]
    exact mul_nonneg (abs_nonneg _) (eDist_nonneg x y)

/-- **The learned score with an error at high noise only.** For data `μ`:
`s_k = ∇ log p_k + E_k`, where `E_k = clampErr i₀ λ R` for `k > K` and `E_k = 0` for `k ≤ K`
(`clampErrAfter`). -/
noncomputable def clampScoreAfter (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    (lam R : ℝ) (K : ℕ) : ℕ → (Fin d → ℝ) → Fin d → ℝ :=
  fun k y i => exactScore μ t k y i + clampErrAfter i₀ lam R K k y i

/-- The learned score is measurable at every step. -/
theorem measurable_clampScoreAfter (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    (lam R : ℝ) (K k : ℕ) : Measurable (clampScoreAfter μ t i₀ lam R K k) :=
  Measurable.of_eval fun i => ((measurable_pi_apply i).comp (measurable_exactScore μ t k)).add
    ((measurable_pi_apply i).comp (continuous_clampErrAfter i₀ lam R K k).measurable)

/-- For `k ≤ K` the learned score is the exact score. -/
theorem clampScoreAfter_of_le (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ)
    {K k : ℕ} (h : k ≤ K) : clampScoreAfter μ t i₀ lam R K k = exactScore μ t k := by
  funext y i
  simp [clampScoreAfter, clampErrAfter_of_le i₀ lam R h]

/-- For `k > K` the learned score is `clampScore μ t i₀ λ R k = ∇ log p_k + clampErr i₀ λ R`. -/
theorem clampScoreAfter_of_lt (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ)
    {K k : ℕ} (h : K < k) : clampScoreAfter μ t i₀ lam R K k = clampScore μ t i₀ lam R k := by
  funext y i
  simp [clampScoreAfter, clampScore, clampErrAfter_of_lt i₀ lam R h]

/-- The score error is the field: `s_k(y) - ∇ log p_k(y) = E_k(y)`. -/
theorem clampScoreAfter_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ)
    (K k : ℕ) (y : Fin d → ℝ) (i : Fin d) :
    clampScoreAfter μ t i₀ lam R K k y i - score (fwdDensity μ t k) y i =
      clampErrAfter i₀ lam R K k y i := by
  simp only [clampScoreAfter, exactScore]
  ring

/-- The score error as a field: `(y ↦ s_k(y) - ∇ log p_k(y)) = E_k` at every step `k`. -/
theorem clampScoreAfter_sub_eq (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ)
    (K k : ℕ) :
    (fun y => clampScoreAfter μ t i₀ lam R K k y - score (fwdDensity μ t k) y) =
      clampErrAfter i₀ lam R K k := by
  funext y i
  rw [Pi.sub_apply]
  exact clampScoreAfter_sub μ t i₀ lam R K k y i

/-- **Uniform accuracy.** For `λ ≥ 0`, `R ≥ 0`, every `k` and `y`:
`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ (λ R)²`. -/
theorem sum_sq_clampScoreAfter_sub_le (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R) (K k : ℕ) (y : Fin d → ℝ) :
    ∑ i, (clampScoreAfter μ t i₀ lam R K k y i - score (fwdDensity μ t k) y i) ^ 2 ≤
      (lam * R) ^ 2 := by
  simp_rw [clampScoreAfter_sub]
  exact sum_sq_clampErrAfter_le i₀ hlam hR K k y

/-- **Accuracy and regularity of the learned score.** For `ε ≥ 0`, `R ≥ 1` and `λ = ε / R`:
`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y` (any data `μ`, any grid), and at every
step `k` the error field `E_k` is `ε`-Lipschitz for the sup metric and satisfies
`|E_k(x) - E_k(y)| ≤ ε |x - y|` for the Euclidean distance. -/
theorem clampScoreAfter_accuracy (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (K : ℕ)
    {ε R : ℝ} (hε : 0 ≤ ε) (hR : 1 ≤ R) :
    (∀ k y, ∑ i, (clampScoreAfter μ t i₀ (ε / R) R K k y i - score (fwdDensity μ t k) y i) ^ 2 ≤
      ε ^ 2) ∧ (∀ k, LipschitzWith ε.toNNReal (clampErrAfter i₀ (ε / R) R K k)) ∧
      ∀ k x y, eDist (clampErrAfter i₀ (ε / R) R K k x) (clampErrAfter i₀ (ε / R) R K k y) ≤
        ε * eDist x y := by
  have hR0 : 0 < R := by linarith
  have hlam : 0 ≤ ε / R := by positivity
  have hle : ε / R ≤ ε := div_le_self hε hR
  refine ⟨fun k y => ?_, fun k => (lipschitzWith_clampErrAfter i₀ hlam R K k).weaken
    (Real.toNNReal_le_toNNReal hle), fun k x y => ?_⟩
  · have := sum_sq_clampScoreAfter_sub_le μ t i₀ hlam hR0.le K k y
    rwa [div_mul_cancel₀ ε hR0.ne'] at this
  · refine (eDist_clampErrAfter_le i₀ _ R K k x y).trans ?_
    rw [abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_right hle (eDist_nonneg x y)

/-- The score-error integrand of the learned score is integrable under every probability law
(it is bounded by `(λ R)²`). -/
theorem integrable_sq_clampScoreAfter_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R) (K k : ℕ) (ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ν] :
    Integrable (fun y =>
      ∑ i, (clampScoreAfter μ t i₀ lam R K k y i - score (fwdDensity μ t k) y i) ^ 2) ν := by
  have hmeas : Measurable fun y =>
      ∑ i, (clampScoreAfter μ t i₀ lam R K k y i - score (fwdDensity μ t k) y i) ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp (measurable_clampScoreAfter μ t i₀ lam R K k)).sub
        ((measurable_pi_apply i).comp (measurable_exactScore μ t k))).pow_const 2
  refine Integrable.of_bound hmeas.aestronglyMeasurable ((lam * R) ^ 2)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (sum_nonneg fun i _ => sq_nonneg _)]
  exact sum_sq_clampScoreAfter_sub_le μ t i₀ hlam hR K k y

/-- The exponential-integrator step driven by the learned score is measurable at every step. -/
theorem measurable_pfMean_clampScoreAfter (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    (lam R : ℝ) (K k : ℕ) : Measurable (pfMean t (clampScoreAfter μ t i₀ lam R K) k) :=
  measurable_detMean (measurable_pfLin t) _ (measurable_clampScoreAfter μ t i₀ lam R K) k

/-- **DDPM with the same score, geometric grid.** Data `μ` with finite second moment,
`u_1 > 0`, `r > 1`, `N ≥ 1`, `λ, R ≥ 0`: DDPM driven by `s = ∇ log p + clampErrAfter i₀ λ R K`
has `TV(p_1, q_1) ≤ √((I + (r - 1) d/2 (1 + (N - 1) log r) + (λ R)² (t_N - t_1)) / 2)`,
`I = initBound` (`tvSup_output_le_geomGrid` with `scoreErr_le_of_sum_sq_le`). -/
theorem tvSup_ddpm_clampScoreAfter_le_geomGrid (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (i₀ : Fin d)
    {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r) {N : ℕ} (hN : 1 ≤ N) {lam R : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (K : ℕ) :
    TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r))
          (scoreMean (geomGrid u1 r) (clampScoreAfter μ (geomGrid u1 r) i₀ lam R K))
          (measurable_scoreMean _ (measurable_clampScoreAfter μ _ i₀ lam R K)) N 1) ≤
      Real.sqrt ((initBound μ (geomGrid u1 r) N +
        (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
        (lam * R) ^ 2 * (geomGrid u1 r N - geomGrid u1 r 1)) / 2) := by
  refine (tvSup_output_le_geomGrid μ hμ hu1 hr hN _ (measurable_clampScoreAfter μ _ i₀ lam R K)
    (fun k _ => integrable_sq_clampScoreAfter_sub μ _ i₀ hlam hR K k _)).trans ?_
  gcongr
  exact scoreErr_le_of_sum_sq_le μ (geomGrid_strictMono hu1 hr).monotone hN
    (fun k _ y => sum_sq_clampScoreAfter_sub_le μ _ i₀ hlam hR K k y)

/-! ### Splitting the deterministic flow at the switching index -/

/-- **Splitting a deterministic flow.** For `k ≤ K ≤ N`: `Φ_k = Φ^K_k ∘ Φ_K`, where
`Φ_K = m_{K+1} ∘ ⋯ ∘ m_N` (`detFlow m N K`) and `Φ^K_k = m_{k+1} ∘ ⋯ ∘ m_K`
(`detFlow m K k`). -/
theorem detFlow_eq_comp (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) {k K N : ℕ} (hkK : k ≤ K)
    (hKN : K ≤ N) : detFlow m N k = detFlow m K k ∘ detFlow m N K := by
  induction hn : K - k generalizing k with
  | zero =>
    obtain rfl : k = K := by omega
    rw [detFlow_self]
    rfl
  | succ n ih =>
    have hlt : k < K := by omega
    rw [detFlow_of_lt m (by omega : k < N), detFlow_of_lt m hlt,
      ih (k := k + 1) (by omega) (by omega)]
    rfl

/-- **The flow below the switching index is the exact-score flow.** For `k ≤ K`, the
exponential-integrator flow from `K` to `k` driven by `clampScoreAfter μ t i₀ λ R K` is the
exact-score flow: `Φ^K_k = m*_{k+1} ∘ ⋯ ∘ m*_K`. -/
theorem detFlow_pf_clampScoreAfter_eq_exact (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    (lam R : ℝ) {k K : ℕ} (hkK : k ≤ K) :
    detFlow (pfMean t (clampScoreAfter μ t i₀ lam R K)) K k =
      detFlow (pfMean t (exactScore μ t)) K k :=
  detFlow_congr hkK fun i _ hiK => by
    funext y j
    change pfLin t i y j + pfCoeff t i * clampScoreAfter μ t i₀ lam R K i y j =
      pfLin t i y j + pfCoeff t i * exactScore μ t i y j
    rw [clampScoreAfter_of_le μ t i₀ lam R hiK]

/-- **The deterministic flow with the high-noise error, split.** For `k ≤ K ≤ N`, the
exponential-integrator flow driven by `clampScoreAfter μ t i₀ λ R K` is the exact-score flow
from `K` to `k` after the perturbed flow from `N` to `K`:
`Φ_k = Φ*^K_k ∘ Φ_K`. -/
theorem detFlow_pf_clampScoreAfter_eq_comp (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    (lam R : ℝ) {k K N : ℕ} (hkK : k ≤ K) (hKN : K ≤ N) :
    detFlow (pfMean t (clampScoreAfter μ t i₀ lam R K)) N k =
      detFlow (pfMean t (exactScore μ t)) K k ∘
        detFlow (pfMean t (clampScoreAfter μ t i₀ lam R K)) N K := by
  rw [detFlow_eq_comp _ hkK hKN, detFlow_pf_clampScoreAfter_eq_exact μ t i₀ lam R hkK]

/-! ### One step on two-point data -/

/-- **The lower slope is at least `1/2`.** If `t_0 = 0`, `t` is strictly increasing and
`k ≥ 1`, then `1/2 ≤ α_k⁻¹ - b_k / v_k` (its value is `(1 - e^{-(t_k + t_{k-1})}) / v_k`, and
`v_k = (1 - e^{-t_k})(1 + e^{-t_k})`). -/
theorem half_le_inv_fwdScale_sub_pfCoeff_div_cumVar {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    1 / 2 ≤ (fwdScale t k)⁻¹ - pfCoeff t k / cumVar t k := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hprev : 0 ≤ t (k - 1) := h0 ▸ ht.monotone (Nat.zero_le _)
  have hv := DiffusionTwoPoint.cumVar_pos htk
  rw [DiffusionTwoPoint.inv_fwdScale_sub_pfCoeff_div_cumVar htk, le_div_iff₀ hv,
    DiffusionTwoPoint.cumVar]
  have hu0 : 0 < Real.exp (-t k) := Real.exp_pos _
  have hu1 : Real.exp (-t k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have e1 : Real.exp (-2 * t k) = Real.exp (-t k) ^ 2 := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have e2 : Real.exp (-(t k + t (k - 1))) ≤ Real.exp (-t k) := Real.exp_le_exp.2 (by linarith)
  rw [e1]
  nlinarith [sq_nonneg (1 - Real.exp (-t k))]

/-- **One perturbed step of the scalar map on the window.** Let `b ≥ 0`, `0 < v ≤ 1`,
`A = 1 + b`, lower slope `A - b/v ≥ 1/2`, `m²/v² ≤ λ/2` and `b λ ≤ 1`. Then for every `x`:
`|mixMap A b m v x - b λ x| ≤ (1 - b λ/2) |x|` (slope bounds `mixMap_bounds_of_nonneg` on
`x ≥ 0`, oddness for `x < 0`). -/
theorem abs_mixMap_sub_mul_le {A b m v lam : ℝ} (hb : 0 ≤ b) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : A = 1 + b) (hlow : 1 / 2 ≤ A - b / v) (hm : m ^ 2 / v ^ 2 ≤ lam / 2)
    (hbl : b * lam ≤ 1) (x : ℝ) :
    |mixMap A b m v x - b * lam * x| ≤ (1 - b * lam / 2) * |x| := by
  have key : ∀ x : ℝ, 0 ≤ x → |mixMap A b m v x - b * lam * x| ≤ (1 - b * lam / 2) * x := by
    intro x hx
    obtain ⟨h1, h2⟩ := DiffusionTwoPoint.mixMap_bounds_of_nonneg A m hb hv hx
    have e : A + b * (m ^ 2 / v - 1) / v = A - b / v + b * (m ^ 2 / v ^ 2) := by
      field_simp
      ring
    have hbv : b ≤ b / v := by
      rw [le_div_iff₀ hv]
      nlinarith
    have hbm : b * (m ^ 2 / v ^ 2) ≤ b * (lam / 2) := mul_le_mul_of_nonneg_left hm hb
    rw [e] at h2
    have p1 := mul_nonneg (sub_nonneg.2 hlow) hx
    have p2 := mul_nonneg (sub_nonneg.2 hbl) hx
    have p3 := mul_nonneg (sub_nonneg.2 hbv) hx
    have p4 := mul_nonneg (sub_nonneg.2 hbm) hx
    rw [abs_le]
    constructor
    · nlinarith
    · subst hA
      nlinarith
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact key x hx
  · have h := key (-x) (by linarith)
    rw [DiffusionTwoPoint.mixMap_neg,
      show -mixMap A b m v x - b * lam * -x = -(mixMap A b m v x - b * lam * x) by ring,
      abs_neg] at h
    rw [abs_of_nonpos hx]
    exact h

/-- **The perturbed probability-flow step on two-point data.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing and `k ≥ 1`, the
exponential-integrator step driven by `clampScoreAfter μ t 0 λ R K` is
`m_k(y)_0 = pfTwoPoint t a k (y_0) + b_k E_k(y)_0`. -/
theorem pfMean_clampScoreAfter_symTwoPoint (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (lam R : ℝ) (K : ℕ) {k : ℕ} (hk : 1 ≤ k) (y : Fin 1 → ℝ) :
    pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K) k y 0 =
      pfTwoPoint t a k (y 0) + pfCoeff t k * clampErrAfter 0 lam R K k y 0 := by
  have h := congrFun (DiffusionTwoPoint.pfMean_exactScore_symTwoPoint a h0 ht hk y) 0
  simp only [pfMean, detMean, clampScoreAfter] at h ⊢
  linear_combination h

/-- **One step of the neutral phase contracts the window.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `K < k`, neutral-phase
condition `(ᾱ_k a)² / v_k² ≤ λ/2` at `t_k`, and `b_k λ ≤ 1` (`b_k = pfCoeff t k`). For `y` in
the window `|y_0| ≤ R`, the exponential-integrator step driven by `clampScoreAfter μ t 0 λ R K`
satisfies `|m_k(y)_0| ≤ (1 - b_k λ/2) |y_0|`. -/
theorem abs_pfMean_clampScoreAfter_symTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R : ℝ} {K k : ℕ} (hKk : K < k)
    (hf : (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2) (hb : pfCoeff t k * lam ≤ 1)
    {y : Fin 1 → ℝ} (hy : |y 0| ≤ R) :
    |pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K) k y 0| ≤
      (1 - pfCoeff t k * lam / 2) * |y 0| := by
  have hk : 1 ≤ k := by omega
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hb0 := DiffusionTwoPoint.pfCoeff_nonneg (ht.monotone (Nat.sub_le k 1))
  have hv := DiffusionTwoPoint.cumVar_pos htk
  have hv1 := (DiffusionTwoPoint.cumVar_lt_one t k).le
  have hA : (fwdScale t k)⁻¹ = 1 + pfCoeff t k := by
    rw [pfCoeff]
    ring
  have hlow := half_le_inv_fwdScale_sub_pfCoeff_div_cumVar h0 ht hk
  have h := abs_mixMap_sub_mul_le hb0 hv hv1 hA hlow hf hb (y 0)
  rw [pfMean_clampScoreAfter_symTwoPoint a h0 ht lam R K hk, clampErrAfter_of_lt 0 lam R hKk]
  simp only [clampErr, ↓reduceIte]
  rw [clip_of_abs_le hy]
  have e : pfTwoPoint t a k (y 0) + pfCoeff t k * (-lam * y 0) =
      mixMap (fwdScale t k)⁻¹ (pfCoeff t k) (cumScale t k * a) (cumVar t k) (y 0) -
        pfCoeff t k * lam * y 0 := by
    rw [pfTwoPoint]
    ring
  rw [e]
  exact h

/-- **A clean sufficient condition for the neutral phase.** For `λ > 0` and
`t_k ≥ log(2 + 8 a²/λ) / 2`: `(ᾱ_k a)² / v_k² ≤ λ/2` (then `ᾱ_k² ≤ 1/2`, so `v_k ≥ 1/2`, and
`8 a² ᾱ_k² ≤ λ`). -/
theorem sq_cumScale_mul_div_sq_cumVar_le {t : ℕ → ℝ} {k : ℕ} (a : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (htk : Real.log (2 + 8 * a ^ 2 / lam) / 2 ≤ t k) :
    (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2 := by
  have hu0 : 0 < Real.exp (-2 * t k) := Real.exp_pos _
  have hcs : cumScale t k ^ 2 = Real.exp (-2 * t k) := by
    rw [DiffusionTwoPoint.cumScale, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hx : 2 + 8 * a ^ 2 / lam ≤ Real.exp (2 * t k) := by
    rw [← Real.log_le_iff_le_exp (by positivity)]
    linarith
  have hu : Real.exp (-2 * t k) * Real.exp (2 * t k) = 1 := by
    rw [← Real.exp_add]
    simp
  have h1 : Real.exp (-2 * t k) * (2 + 8 * a ^ 2 / lam) ≤ 1 := by
    calc Real.exp (-2 * t k) * (2 + 8 * a ^ 2 / lam)
        ≤ Real.exp (-2 * t k) * Real.exp (2 * t k) := mul_le_mul_of_nonneg_left hx hu0.le
      _ = 1 := hu
  have hq : 0 ≤ 8 * a ^ 2 / lam := by positivity
  have hhalf : Real.exp (-2 * t k) ≤ 1 / 2 := by nlinarith
  have h2 : 8 * a ^ 2 * Real.exp (-2 * t k) ≤ lam := by
    have e : Real.exp (-2 * t k) * (8 * a ^ 2 / lam) = 8 * a ^ 2 * Real.exp (-2 * t k) / lam := by
      ring
    have : Real.exp (-2 * t k) * (8 * a ^ 2 / lam) ≤ 1 := by nlinarith
    rw [e, div_le_one hlam] at this
    exact this
  have hv : cumVar t k = 1 - Real.exp (-2 * t k) := rfl
  have hv2 : 1 / 2 ≤ cumVar t k := by rw [hv]; linarith
  have hv4 : 1 / 4 ≤ cumVar t k ^ 2 := by nlinarith
  have h3 : lam / 2 * (1 / 4) ≤ lam / 2 * cumVar t k ^ 2 :=
    mul_le_mul_of_nonneg_left hv4 (by linarith)
  rw [mul_pow, hcs, div_le_iff₀ (by positivity)]
  linarith

/-! ### The neutral phase: the window contracts -/

/-- **The neutral phase contracts the window, step by step.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `λ ≥ 0`, and for every
`K < k ≤ N` the neutral-phase condition `(ᾱ_k a)² / v_k² ≤ λ/2` and `b_k λ ≤ 1`. For
`K ≤ j ≤ N` and `y` in the window `|y_0| ≤ R`, the exponential-integrator flow `Φ_j` driven by
`clampScoreAfter μ t 0 λ R K` satisfies `|Φ_j(y)_0| ≤ (∏_{j < k ≤ N} (1 - b_k λ/2)) |y_0|`; in
particular the window is invariant. -/
theorem abs_detFlow_clampScoreAfter_symTwoPoint_le_prod (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R : ℝ} (hlam : 0 ≤ lam) {K N : ℕ}
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1) {j : ℕ} (hKj : K ≤ j) (hjN : j ≤ N)
    {y : Fin 1 → ℝ} (hy : |y 0| ≤ R) :
    |detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K)) N j y 0|
      ≤ (∏ k ∈ Ioc j N, (1 - pfCoeff t k * lam / 2)) * |y 0| := by
  have hx : ∀ k ∈ Ioc K N, 0 ≤ pfCoeff t k * lam / 2 ∧ pfCoeff t k * lam / 2 ≤ 1 :=
    fun k hk => ⟨by
      have := DiffusionTwoPoint.pfCoeff_nonneg (ht.monotone (Nat.sub_le k 1))
      positivity, by linarith [hb k hk]⟩
  induction hn : N - j generalizing j with
  | zero =>
    obtain rfl : j = N := by omega
    simp [detFlow_self]
  | succ n ih =>
    have hlt : j < N := by omega
    have hsub : Ioc (j + 1) N ⊆ Ioc K N := Finset.Ioc_subset_Ioc_left (by omega)
    have hj1 : j + 1 ∈ Ioc K N := by simp only [mem_Ioc]; omega
    have ih' := ih (j := j + 1) (by omega) (by omega) (by omega)
    have hP := prod_one_sub_mem_Icc (s := Ioc (j + 1) N) (x := fun k => pfCoeff t k * lam / 2)
      (fun k hk => hx k (hsub hk))
    set z := detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
      N (j + 1) y
    have hz : |z 0| ≤ R :=
      ih'.trans ((mul_le_of_le_one_left (abs_nonneg _) hP.2).trans hy)
    have hstep := abs_pfMean_clampScoreAfter_symTwoPoint_le a h0 ht (lam := lam) (R := R)
      (K := K) (k := j + 1) (by omega) (hf _ hj1) (hb _ hj1) hz
    rw [detFlow_of_lt _ hlt, Function.comp_apply, prod_Ioc_eq_mul hlt, mul_assoc]
    exact hstep.trans (mul_le_mul_of_nonneg_left ih' (by linarith [(hx _ hj1).2]))

/-- **The neutral phase contracts the window.** For `a : ℝ`, data `(δ_{-a} + δ_a)/2` on
`Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `λ ≥ 0`, `K ≤ N`, and for every `K < k ≤ N` the
neutral-phase condition `(ᾱ_k a)² / v_k² ≤ λ/2` and `b_k λ ≤ 1`. For `y` in the window
`|y_0| ≤ R`, the exponential-integrator flow `Φ_K = m_{K+1} ∘ ⋯ ∘ m_N` driven by
`clampScoreAfter μ t 0 λ R K` satisfies `|Φ_K(y)_0| ≤ exp(-(λ/2)(t_N - t_K)) |y_0| ≤ R`
(`DiffusionODELongHorizon.prod_one_sub_pfCoeff_le` with `λ/2`). -/
theorem abs_detFlow_clampScoreAfter_symTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R : ℝ} (hlam : 0 ≤ lam) {K N : ℕ} (hKN : K ≤ N)
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1) {y : Fin 1 → ℝ} (hy : |y 0| ≤ R) :
    |detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K)) N K y 0|
      ≤ Real.exp (-(lam / 2) * (t N - t K)) * |y 0| ∧
    |detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K)) N K y 0|
      ≤ R := by
  have h := abs_detFlow_clampScoreAfter_symTwoPoint_le_prod a h0 ht hlam hf hb le_rfl hKN hy
  have hP := prod_one_sub_pfCoeff_le (t := t) hKN (lam := lam / 2) (by linarith)
    (fun k hk => by rw [← mul_div_assoc]; linarith [hb k hk])
  simp only [← mul_div_assoc] at hP
  have hE : Real.exp (-(lam / 2) * (t N - t K)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := (sub_nonneg.2 (ht.monotone hKN))
    nlinarith
  have h1 := h.trans (mul_le_mul_of_nonneg_right hP (abs_nonneg _))
  exact ⟨h1, h1.trans ((mul_le_of_le_one_left (abs_nonneg _) hE).trans hy)⟩

/-! ### The collapse

The phase without error is the exact-score flow `Φ*^K_1 = m*_2 ∘ ⋯ ∘ m*_K`. It is odd, fixes
`0` (`DiffusionTwoPoint.detFlow_pfMean_exactScore_symTwoPoint_zero`) and is
`∏_{1 < k ≤ K} L_k`-Lipschitz (`DiffusionTwoPoint.eDist_detFlow_pfMean_exactScore_symTwoPoint_le`),
and on every grid whose steps up to `K` are at most `log 2` this product is at most
`exp(a²/(e^{2 t_1} - 1))` (`DiffusionTwoPoint.prod_lipTwoPoint_le`). -/

/-- **The deterministic output collapses to the midpoint.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `λ ≥ 0`,
`1 ≤ K ≤ N`, and for every `K < k ≤ N` the neutral-phase condition `(ᾱ_k a)² / v_k² ≤ λ/2` and
`b_k λ ≤ 1`. Suppose the exact-score flow `Φ*^K_1 = m*_2 ∘ ⋯ ∘ m*_K` is `C`-Lipschitz in the
coordinate. Then the exponential-integrator flow `Φ_1 = m_2 ∘ ⋯ ∘ m_N` driven by
`clampScoreAfter μ t 0 λ R K` satisfies `|Φ_1(y)_0| ≤ C exp(-(λ/2)(t_N - t_K)) R` for every `y`
in the window `|y_0| ≤ R`: `Φ_1 = Φ*^K_1 ∘ Φ_K`, `Φ*^K_1(0) = 0`, and the neutral phase
contracts the window (`abs_detFlow_clampScoreAfter_symTwoPoint_le`). The constant
`C = ∏_{1 < k ≤ K} L_k` is admissible
(`DiffusionTwoPoint.eDist_detFlow_pfMean_exactScore_symTwoPoint_le`). -/
theorem abs_detFlow_pf_clampScoreAfter_symTwoPoint_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R C : ℝ} (hlam : 0 ≤ lam) {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1)
    (hC : ∀ x z : Fin 1 → ℝ,
      |detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x 0 -
        detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 z 0| ≤
        C * |x 0 - z 0|)
    {y : Fin 1 → ℝ} (hy : |y 0| ≤ R) :
    |detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K)) N 1 y 0|
      ≤ C * Real.exp (-(lam / 2) * (t N - t K)) * R := by
  have hC0 : 0 ≤ C := by
    have h := hC (fun _ => 1) 0
    simp only [Pi.zero_apply, sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  obtain ⟨h1, -⟩ := abs_detFlow_clampScoreAfter_symTwoPoint_le a h0 ht hlam hKN hf hb hy
  rw [detFlow_pf_clampScoreAfter_eq_comp _ t 0 lam R hK hKN, Function.comp_apply]
  set z := detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
    N K y
  have h2 := hC z 0
  rw [DiffusionTwoPoint.detFlow_pfMean_exactScore_symTwoPoint_zero a h0 ht K] at h2
  simp only [Pi.zero_apply, sub_zero] at h2
  calc _ ≤ C * |z 0| := h2
    _ ≤ C * (Real.exp (-(lam / 2) * (t N - t K)) * |y 0|) := mul_le_mul_of_nonneg_left h1 hC0
    _ ≤ C * Real.exp (-(lam / 2) * (t N - t K)) * R := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hy (by positivity)

/-! ### Masses of the slab around the midpoint -/

/-- **A Gaussian puts little mass on a short interval.** For `v > 0`, every mean `m` and
every `ρ`: `N(m, v)([-ρ, ρ]) ≤ 2ρ / √(2π v)` (the density is at most `1/√(2π v)`; for
`ρ < 0` the right side is `ofReal` of a negative number, `0`, and the interval is empty). -/
theorem gaussianReal_Icc_le_ofReal (m : ℝ) {v : ℝ} (hv : 0 < v) (ρ : ℝ) :
    gaussianReal m v.toNNReal (Set.Icc (-ρ) ρ) ≤
      ENNReal.ofReal (2 * ρ / Real.sqrt (2 * Real.pi * v)) := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  rw [gaussianReal_apply m hv']
  calc ∫⁻ x in Set.Icc (-ρ) ρ, gaussianPDF m v.toNNReal x
      ≤ ∫⁻ _x in Set.Icc (-ρ) ρ, ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ := by
        refine lintegral_mono fun x => ?_
        rw [gaussianPDF, HeatFlowDeBruijn.gaussianPDFReal_eq_heatDensity hv]
        exact ENNReal.ofReal_le_ofReal (HeatFlowDeBruijn.heatDensity_le hv _)
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ * ENNReal.ofReal (2 * ρ) := by
        rw [setLIntegral_const, Real.volume_Icc]
        congr 2
        ring
    _ = ENNReal.ofReal (2 * ρ / Real.sqrt (2 * Real.pi * v)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The data-side mass of the slab.** For `a : ℝ`, data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`,
`t_0 = 0`, `t` strictly increasing, `k ≥ 1` and `ρ ≥ 0`, the forward marginal
`p_k = (N(-ᾱ_k a, v_k) + N(ᾱ_k a, v_k))/2` gives the slab `{x | |x_0| ≤ ρ}` mass at most
`2ρ / √(2π v_k)`. -/
theorem fwdLaw_symTwoPoint_real_abs_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (fwdLaw (symTwoPoint fun _ : Fin 1 => a) t k).real {x | |x 0| ≤ ρ} ≤
      2 * ρ / Real.sqrt (2 * Real.pi * cumVar t k) := by
  have htk : 0 < t k := h0 ▸ ht (by omega : 0 < k)
  have hv := DiffusionTwoPoint.cumVar_pos htk
  have e : {x : Fin 1 → ℝ | |x 0| ≤ ρ} = Function.eval 0 ⁻¹' Set.Icc (-ρ) ρ := by
    ext x
    simp [abs_le]
  have hpi : ∀ m : ℝ, Measure.pi (fun _ : Fin 1 => gaussianReal m (cumVar t k).toNNReal)
      (Function.eval 0 ⁻¹' Set.Icc (-ρ) ρ) = gaussianReal m (cumVar t k).toNNReal
        (Set.Icc (-ρ) ρ) := fun m =>
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal m (cumVar t k).toNNReal)
      0).measure_preimage measurableSet_Icc.nullMeasurableSet
  rw [DiffusionTwoPoint.fwdLaw_symTwoPoint _ h0 ht.monotone k, measureReal_def, e,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hpi, hpi, smul_eq_mul,
    smul_eq_mul]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc 2⁻¹ * gaussianReal (-(cumScale t k * a)) (cumVar t k).toNNReal (Set.Icc (-ρ) ρ) +
        2⁻¹ * gaussianReal (cumScale t k * a) (cumVar t k).toNNReal (Set.Icc (-ρ) ρ)
      ≤ 2⁻¹ * ENNReal.ofReal (2 * ρ / Real.sqrt (2 * Real.pi * cumVar t k)) +
        2⁻¹ * ENNReal.ofReal (2 * ρ / Real.sqrt (2 * Real.pi * cumVar t k)) :=
        add_le_add (by gcongr; exact gaussianReal_Icc_le_ofReal _ hv ρ)
          (by gcongr; exact gaussianReal_Icc_le_ofReal _ hv ρ)
    _ = ENNReal.ofReal (2 * ρ / Real.sqrt (2 * Real.pi * cumVar t k)) := by
        rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- **The sampler-side mass of the slab.** In the setting of
`abs_detFlow_pf_clampScoreAfter_symTwoPoint_le` (`a : ℝ`, data `(δ_{-a} + δ_a)/2` on
`Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `λ ≥ 0`, `1 ≤ K ≤ N`, the neutral-phase
conditions on `(K, N]`, exact-score flow `Φ*^K_1` `C`-Lipschitz in the coordinate), if
`C exp(-(λ/2)(t_N - t_K)) R ≤ ρ`, then the deterministic output
`q_1 = algLaw 0 (pfMean t s) N 1 = Φ_1 # N(0, 1)` gives the slab `{x | |x_0| ≤ ρ}` mass at least
`N(0, 1)([-R, R])`. -/
theorem le_detOutput_real_abs_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {lam R C ρ : ℝ} (hlam : 0 ≤ lam) {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1)
    (hC : ∀ x z : Fin 1 → ℝ,
      |detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x 0 -
        detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 z 0| ≤
        C * |x 0 - z 0|)
    (hc : C * Real.exp (-(lam / 2) * (t N - t K)) * R ≤ ρ) :
    (gaussianReal 0 1).real (Set.Icc (-R) R) ≤
      (algLaw zeroVar (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
        (measurable_pfMean_clampScoreAfter _ t 0 lam R K) N 1).real {x | |x 0| ≤ ρ} := by
  have hm := measurable_pfMean_clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K
  have hG : MeasurableSet {x : Fin 1 → ℝ | |x 0| ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hΦ := measurable_detFlow hm N 1
  have hsub : {y : Fin 1 → ℝ | |y 0| ≤ R} ⊆
      detFlow (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K)) N 1 ⁻¹'
        {x | |x 0| ≤ ρ} := fun y hy =>
    (abs_detFlow_pf_clampScoreAfter_symTwoPoint_le a h0 ht hlam hK hKN hf hb hC hy).trans hc
  rw [algLaw_zeroVar_eq_map, ← stdGaussianPi_real_abs_le (0 : Fin 1) R, measureReal_def,
    measureReal_def, Measure.map_apply hΦ hG]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

/-- **The deterministic sampler is far from the data in total variation.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `λ ≥ 0`, `ρ ≥ 0`,
`1 ≤ K ≤ N`, and for every `K < k ≤ N` the neutral-phase condition `(ᾱ_k a)² / v_k² ≤ λ/2` and
`b_k λ ≤ 1`. Suppose the exact-score flow `Φ*^K_1` is `C`-Lipschitz in the coordinate and
`C exp(-(λ/2)(t_N - t_K)) R ≤ ρ`. Then the exponential-integrator sampler driven by
`s = ∇ log p + clampErrAfter 0 λ R K` (error only at steps `k > K`) has
`TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - 2ρ / √(2π v_1)`: the slab `G = {|x_0| ≤ ρ}` has
`q_1(G) ≥ N(0, 1)([-R, R])` (`le_detOutput_real_abs_le`) and `p_1(G) ≤ 2ρ / √(2π v_1)`
(`fwdLaw_symTwoPoint_real_abs_le`). -/
theorem tvSup_pf_clampScoreAfter_symTwoPoint_ge (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R C ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) {K N : ℕ} (hK : 1 ≤ K)
    (hKN : K ≤ N)
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1)
    (hC : ∀ x z : Fin 1 → ℝ,
      |detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x 0 -
        detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 z 0| ≤
        C * |x 0 - z 0|)
    (hc : C * Real.exp (-(lam / 2) * (t N - t K)) * R ≤ ρ) :
    (gaussianReal 0 1).real (Set.Icc (-R) R) - 2 * ρ / Real.sqrt (2 * Real.pi * cumVar t 1) ≤
      TotalVariation.tvSup (fwdLaw (symTwoPoint fun _ : Fin 1 => a) t 1)
        (algLaw zeroVar
          (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
          (measurable_pfMean_clampScoreAfter _ t 0 lam R K) N 1) := by
  have hG : MeasurableSet {x : Fin 1 → ℝ | |x 0| ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hq := le_detOutput_real_abs_le a h0 ht hlam hK hKN hf hb hC hc
  have hp := fwdLaw_symTwoPoint_real_abs_le a h0 ht le_rfl hρ
  have hTV := TotalVariation.abs_measureReal_sub_le_tvSup
    (μ := fwdLaw (symTwoPoint fun _ : Fin 1 => a) t 1)
    (ν := algLaw zeroVar
      (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
      (measurable_pfMean_clampScoreAfter _ t 0 lam R K) N 1) hG
  have := neg_abs_le ((fwdLaw (symTwoPoint fun _ : Fin 1 => a) t 1).real {x | |x 0| ≤ ρ} -
    (algLaw zeroVar
      (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
      (measurable_pfMean_clampScoreAfter _ t 0 lam R K) N 1).real {x | |x 0| ≤ ρ})
  linarith

/-- **The exact-score flow is Lipschitz in the coordinate.** For `a : ℝ`, data
`(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0` and `t` strictly increasing, the exact-score flow
`Φ*^K_1 = m*_2 ∘ ⋯ ∘ m*_K` satisfies
`|Φ*^K_1(x)_0 - Φ*^K_1(z)_0| ≤ (∏_{1 < k ≤ K} L_k) |x_0 - z_0|`, with
`L_k = lipTwoPoint t a k = α_k⁻¹ - b_k/v_k + b_k (ᾱ_k a)²/v_k²`
(`DiffusionTwoPoint.eDist_detFlow_pfMean_exactScore_symTwoPoint_le` in coordinates). -/
theorem abs_detFlow_pf_exactScore_symTwoPoint_sub_le (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (K : ℕ) (x z : Fin 1 → ℝ) :
    |detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x 0 -
        detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 z 0| ≤
      (∏ k ∈ Ioc 1 K, lipTwoPoint t a k) * |x 0 - z 0| := by
  have h := DiffusionTwoPoint.eDist_detFlow_pfMean_exactScore_symTwoPoint_le a h0 ht K x z
  rwa [DiffusionTwoPoint.eDist_fin_one, DiffusionTwoPoint.eDist_fin_one] at h

/-- **The exact-score flow is Lipschitz in the coordinate, grid-uniform constant.** For `a : ℝ`,
data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing and steps
`t_k - t_{k-1} ≤ log 2` for `1 < k ≤ K`, the exact-score flow `Φ*^K_1 = m*_2 ∘ ⋯ ∘ m*_K`
satisfies `|Φ*^K_1(x)_0 - Φ*^K_1(z)_0| ≤ exp(a²/(e^{2 t_1} - 1)) |x_0 - z_0|`
(`DiffusionTwoPoint.eDist_detFlow_pfMean_exactScore_symTwoPoint_le_exp` in coordinates). -/
theorem abs_detFlow_pf_exactScore_symTwoPoint_sub_le_exp (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {K : ℕ} (hstep : ∀ k ∈ Ioc 1 K, t k - t (k - 1) ≤ Real.log 2)
    (x z : Fin 1 → ℝ) :
    |detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 x 0 -
        detFlow (pfMean t (exactScore (symTwoPoint fun _ : Fin 1 => a) t)) K 1 z 0| ≤
      Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) * |x 0 - z 0| := by
  have h := DiffusionTwoPoint.eDist_detFlow_pfMean_exactScore_symTwoPoint_le_exp a h0 ht hstep x z
  rwa [DiffusionTwoPoint.eDist_fin_one, DiffusionTwoPoint.eDist_fin_one] at h

/-- **The deterministic sampler is far from the data, explicit late constant.** The statement of
`tvSup_pf_clampScoreAfter_symTwoPoint_ge` with `C = ∏_{1 < k ≤ K} L_k`, `L_k = lipTwoPoint t a k`
(`abs_detFlow_pf_exactScore_symTwoPoint_sub_le`): if `C exp(-(λ/2)(t_N - t_K)) R ≤ ρ`, then
`TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - 2ρ / √(2π v_1)`. -/
theorem tvSup_pf_clampScoreAfter_symTwoPoint_ge_prod (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) {K N : ℕ} (hK : 1 ≤ K)
    (hKN : K ≤ N)
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1)
    (hc : (∏ k ∈ Ioc 1 K, lipTwoPoint t a k) * Real.exp (-(lam / 2) * (t N - t K)) * R ≤ ρ) :
    (gaussianReal 0 1).real (Set.Icc (-R) R) - 2 * ρ / Real.sqrt (2 * Real.pi * cumVar t 1) ≤
      TotalVariation.tvSup (fwdLaw (symTwoPoint fun _ : Fin 1 => a) t 1)
        (algLaw zeroVar
          (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
          (measurable_pfMean_clampScoreAfter _ t 0 lam R K) N 1) :=
  tvSup_pf_clampScoreAfter_symTwoPoint_ge a h0 ht hlam hρ hK hKN hf hb
    (abs_detFlow_pf_exactScore_symTwoPoint_sub_le a h0 ht K) hc

/-- **The deterministic sampler is far from the data, grid-uniform late constant.** For `a : ℝ`,
data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, `t_0 = 0`, `t` strictly increasing, `λ ≥ 0`, `ρ ≥ 0`,
`1 ≤ K ≤ N`, steps `t_k - t_{k-1} ≤ log 2` for `1 < k ≤ K`, and for every `K < k ≤ N` the
neutral-phase condition `(ᾱ_k a)² / v_k² ≤ λ/2` and `b_k λ ≤ 1`. With
`C = exp(a²/(e^{2 t_1} - 1))` (which depends on `a` and `t_1` only), if
`C exp(-(λ/2)(t_N - t_K)) R ≤ ρ`, then the exponential-integrator sampler driven by
`s = ∇ log p + clampErrAfter 0 λ R K` has `TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - 2ρ / √(2π v_1)`
(`tvSup_pf_clampScoreAfter_symTwoPoint_ge` with
`abs_detFlow_pf_exactScore_symTwoPoint_sub_le_exp`). -/
theorem tvSup_pf_clampScoreAfter_symTwoPoint_ge_exp (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {lam R ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) {K N : ℕ} (hK : 1 ≤ K)
    (hKN : K ≤ N) (hstep : ∀ k ∈ Ioc 1 K, t k - t (k - 1) ≤ Real.log 2)
    (hf : ∀ k ∈ Ioc K N, (cumScale t k * a) ^ 2 / cumVar t k ^ 2 ≤ lam / 2)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1)
    (hc : Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) * Real.exp (-(lam / 2) * (t N - t K)) *
        R ≤ ρ) :
    (gaussianReal 0 1).real (Set.Icc (-R) R) - 2 * ρ / Real.sqrt (2 * Real.pi * cumVar t 1) ≤
      TotalVariation.tvSup (fwdLaw (symTwoPoint fun _ : Fin 1 => a) t 1)
        (algLaw zeroVar
          (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 lam R K))
          (measurable_pfMean_clampScoreAfter _ t 0 lam R K) N 1) :=
  tvSup_pf_clampScoreAfter_symTwoPoint_ge a h0 ht hlam hρ hK hKN hf hb
    (abs_detFlow_pf_exactScore_symTwoPoint_sub_le_exp a h0 ht hstep) hc

/-! ### Choosing the parameters -/

/-- **Choosing the switching index.** For every sequence `t`, `N ≥ 1` and threshold `T` there is
an index `K` with `1 ≤ K ≤ N`, `t_k ≥ T` for every `K < k ≤ N`, and `t_K ≤ max(t_1, T)`. The
witness is `K = max(1, G)`, where `G` is the largest `k ≤ N` with `t_k < T`, and `G = 0` if
there is none (`Nat.findGreatest`); if `t_1 ≥ T`, then `K = 1` and `t_K` is not below `T`. -/
theorem exists_switchIndex (t : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (T : ℝ) :
    ∃ K : ℕ, 1 ≤ K ∧ K ≤ N ∧ (∀ k ∈ Ioc K N, T ≤ t k) ∧ t K ≤ max (t 1) T := by
  classical
  obtain ⟨G, hG⟩ : ∃ G, G = Nat.findGreatest (fun k => t k < T) N := ⟨_, rfl⟩
  have hGN : G ≤ N := hG ▸ Nat.findGreatest_le N
  refine ⟨max 1 G, le_max_left _ _, max_le hN hGN, fun k hk => ?_, ?_⟩
  · simp only [mem_Ioc] at hk
    exact not_lt.1 (Nat.findGreatest_is_greatest (hG ▸ lt_of_le_of_lt (le_max_right _ _) hk.1)
      hk.2)
  · rcases le_total G 1 with h | h
    · rw [max_eq_left h]
      exact le_max_left _ _
    · rw [max_eq_right h]
      exact (Nat.findGreatest_of_ne_zero hG.symm (by omega)).le.trans (le_max_right _ _)

/-- On the geometric grid `e^{2 t_1} = 1 + u_1` (`u_1 > 0`, every `r`). -/
theorem exp_two_mul_geomGrid_one {u1 : ℝ} (hu1 : 0 < u1) (r : ℝ) :
    Real.exp (2 * geomGrid u1 r 1) = 1 + u1 := by
  rw [geomGrid_of_one_le u1 r le_rfl, Nat.sub_self, pow_zero, mul_one,
    mul_div_cancel₀ _ two_ne_zero, Real.exp_log (by linarith)]

/-- On the geometric grid `v_1 = 1 - e^{-2 t_1} = u_1 / (1 + u_1)` (`u_1 > 0`, every `r`). -/
theorem cumVar_geomGrid_one {u1 : ℝ} (hu1 : 0 < u1) (r : ℝ) :
    cumVar (geomGrid u1 r) 1 = u1 / (1 + u1) := by
  have h := exp_two_mul_geomGrid_one hu1 r
  rw [DiffusionTwoPoint.cumVar,
    show -2 * geomGrid u1 r 1 = -(2 * geomGrid u1 r 1) by ring, Real.exp_neg, h]
  field_simp
  ring

/-- On the geometric grid `ᾱ_1 = e^{-t_1} = 1/√(1 + u_1)` (`u_1 > 0`, every `r`): the two
Gaussian components of the forward marginal `p_1 = (N(-ᾱ_1 a, v_1) + N(ᾱ_1 a, v_1))/2` of
two-point data are centred at `±a/√(1 + u_1)`. -/
theorem cumScale_geomGrid_one {u1 : ℝ} (hu1 : 0 < u1) (r : ℝ) :
    cumScale (geomGrid u1 r) 1 = 1 / Real.sqrt (1 + u1) := by
  have h := exp_two_mul_geomGrid_one hu1 r
  have e : Real.sqrt (1 + u1) = Real.exp (geomGrid u1 r 1) := by
    rw [← h, two_mul, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [DiffusionTwoPoint.cumScale, e, Real.exp_neg, one_div]

/-- **Collapse on every long grid.** For `a : ℝ`, data `(δ_{-a} + δ_a)/2` on `Fin 1 → ℝ`, a
grid with `t_0 = 0`, `t` strictly increasing, `N ≥ 1` and steps `t_k - t_{k-1} ≤ log 2`
(`1 < k ≤ N`), `0 < ε ≤ 1`, `R ≥ 1` and `0 < ρ < R`, write `t_* = log(2 + 8 a² R/ε)/2` and
`C = exp(a²/(e^{2 t_1} - 1))`. If the horizon satisfies
`t_N - t_1 ≥ t_* + (2R/ε) log(C R/ρ)`, there is a switching index `K` with `1 ≤ K < N` and
`t_k ≥ t_*` for every `K < k ≤ N` such that the exponential-integrator sampler driven by
`s = ∇ log p + clampErrAfter 0 (ε/R) R K` (score error at most `ε` in sup norm, `ε`-Lipschitz
error field: `clampScoreAfter_accuracy`) gives the slab `{x | |x_0| ≤ ρ}` mass at least
`N(0, 1)([-R, R])`. Proof: `K` from `exists_switchIndex` with threshold `t_*`; on `(K, N]` the
neutral-phase condition holds (`sq_cumScale_mul_div_sq_cumVar_le`) and `b_k ≤ 1`; the phase
without error is `C`-Lipschitz (`abs_detFlow_pf_exactScore_symTwoPoint_sub_le_exp`); and
`t_K ≤ max(t_1, t_*)` gives `t_N - t_K ≥ (2R/ε) log(C R/ρ)`, hence
`C exp(-(λ/2)(t_N - t_K)) R ≤ ρ` for `λ = ε/R` (`le_detOutput_real_abs_le`). -/
theorem exists_pf_clampScoreAfter_collapse (a : ℝ) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N)
    (hstep : ∀ k ∈ Ioc 1 N, t k - t (k - 1) ≤ Real.log 2) {ε R ρ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 1 ≤ R) (hρ : 0 < ρ) (hρR : ρ < R)
    (hT : Real.log (2 + 8 * a ^ 2 * R / ε) / 2 +
        2 * R / ε * Real.log (Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) * R / ρ) ≤
      t N - t 1) :
    ∃ K : ℕ, 1 ≤ K ∧ K < N ∧ (∀ k ∈ Ioc K N, Real.log (2 + 8 * a ^ 2 * R / ε) / 2 ≤ t k) ∧
      (gaussianReal 0 1).real (Set.Icc (-R) R) ≤
        (algLaw zeroVar
          (pfMean t (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) t 0 (ε / R) R K))
          (measurable_pfMean_clampScoreAfter _ t 0 (ε / R) R K) N 1).real {x | |x 0| ≤ ρ} := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.log (2 + 8 * a ^ 2 * R / ε) / 2 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.exp (a ^ 2 / (Real.exp (2 * t 1) - 1)) := ⟨_, rfl⟩
  rw [← hTdef, ← hCdef] at hT
  obtain ⟨K, hK1, hKN, hKT, hKt⟩ := exists_switchIndex t hN T
  have hR0 : 0 < R := by linarith
  have hlam : 0 < ε / R := by positivity
  have hlam1 : ε / R ≤ 1 := (div_le_one hR0).2 (by linarith)
  have ht1 : 0 < t 1 := h0 ▸ ht zero_lt_one
  have hT0 : 0 ≤ T := by
    have : 0 ≤ 8 * a ^ 2 * R / ε := by positivity
    rw [hTdef]
    exact div_nonneg (Real.log_nonneg (by linarith)) two_pos.le
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    refine Real.one_le_exp (div_nonneg (sq_nonneg a) ?_)
    linarith [Real.add_one_le_exp (2 * t 1)]
  have hL : 0 < Real.log (C * R / ρ) := Real.log_pos (by rw [one_lt_div hρ]; nlinarith)
  have hNK : 2 * R / ε * Real.log (C * R / ρ) ≤ t N - t K := by
    have : t K ≤ t 1 + T := hKt.trans (max_le (by linarith) (by linarith))
    linarith
  have hKN' : K < N := by
    have : 0 < 2 * R / ε * Real.log (C * R / ρ) := by positivity
    exact ht.lt_iff_lt.1 (by linarith)
  refine ⟨K, hK1, hKN', fun k hk => hTdef ▸ hKT k hk, ?_⟩
  refine le_detOutput_real_abs_le a h0 ht hlam.le hK1 hKN (fun k hk => ?_) (fun k hk => ?_)
    (C := C) (fun x z => ?_) ?_
  · refine sq_cumScale_mul_div_sq_cumVar_le a hlam ?_
    rw [div_div_eq_mul_div, ← hTdef]
    exact hKT k hk
  · have hk' : k ∈ Ioc 1 N := Finset.Ioc_subset_Ioc_left hK1 hk
    have hb := pfCoeff_le_one (hstep k hk')
    calc pfCoeff t k * (ε / R) ≤ 1 * 1 := mul_le_mul hb hlam1 hlam.le zero_le_one
      _ = 1 := one_mul 1
  · rw [hCdef]
    exact abs_detFlow_pf_exactScore_symTwoPoint_sub_le_exp a h0 ht
      (fun k hk => hstep k (Finset.Ioc_subset_Ioc_right hKN hk)) x z
  · have hlog : Real.log (C * R / ρ) ≤ ε / R / 2 * (t N - t K) := by
      have h := mul_le_mul_of_nonneg_left hNK (by positivity : 0 ≤ ε / R / 2)
      have e : ε / R / 2 * (2 * R / ε * Real.log (C * R / ρ)) = Real.log (C * R / ρ) := by
        field_simp
      linarith
    have hCR : 0 < C * R / ρ := by positivity
    calc C * Real.exp (-(ε / R / 2) * (t N - t K)) * R
        ≤ C * Real.exp (-Real.log (C * R / ρ)) * R := by gcongr; linarith
      _ = ρ := by
        rw [Real.exp_neg, Real.exp_log hCR]
        field_simp

/-! ### The separation -/

/-- **Two-point data: the deterministic sampler collapses onto the midpoint, DDPM does not
(same learned score, `ε`-small and `ε`-Lipschitz error).** Data `(δ_{-a} + δ_a)/2` on
`Fin 1 → ℝ` with `a > 0`, and `η > 0`. There is `R ≥ 1` such that for every `u_1 > 0` there are
a slab radius `ρ > 0` with `ρ ≤ a/(2√(1 + u_1))` (half the distance from the midpoint `0` to
the centres `±a/√(1 + u_1)` of the two Gaussian components of `p_1`, `cumScale_geomGrid_one`),
`A > 0` and `ε₀ > 0` such that for every `0 < ε ≤ ε₀` there are a geometric grid
`geomGrid u_1 r` (`r > 1`), `N ≥ 2` and a switching index `K`, `1 ≤ K < N`, for which
1. the horizon is at most `A / ε`: `t_N - t_1 ≤ A / ε`;

and the learned score `s = ∇ log p + clampErrAfter 0 (ε/R) R K` (error `-(ε/R) clip_R(y_0)` at
the steps `k > K`, no error at the steps `k ≤ K`) satisfies
2. the error acts only at high noise: `t_k ≥ log(2 + 8 a² R/ε)/2` for `K < k ≤ N`;
3. `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y`;
4. the score error `y ↦ s_k(y) - ∇ log p_k(y)` is `ε`-Lipschitz (sup metric) at every step;
5. the slab `G = {x | |x_0| ≤ ρ}` has `p_1(G) ≤ η`, while the deterministic
   exponential-integrator output has `q_1^det(G) ≥ 1 - η`; hence `TV(p_1, q_1^det) ≥ 1 - 2η`;
6. DDPM with the same `s` has `TV(p_1, q_1^DDPM) ≤ η`.
In the proof `R` is chosen from `η` alone (`N(0, 1)([-R, R]) ≥ 1 - η`, `exists_window`) and `ρ`
from `η`, `a`, `u_1` (`p_1(G) ≤ 2ρ/√(2π v_1)`, `v_1 = u_1/(1 + u_1)`); `p_1(G) ≤ η` comes from
the smallness of `ρ`, not from a low density of `p_1` at `0`. The grid has horizon
`A₀/ε ≤ t_N - t_1 ≤ A₀/ε + c` with `A₀ = 2R log(C R/ρ) + 1 + 8 a² R`, `C = exp(a²/u_1)` and
`c` independent of `ε` (`exists_longHorizon_geomGrid_params`), so `A = A₀ + c + 1` works for
`ε ≤ 1`. Since
`t_* = log(2 + 8 a² R/ε)/2 ≤ (1 + 8 a² R)/ε`, the lower end covers `t_*` plus the contraction
time `(2R/ε) log(C R/ρ)` (`exists_pf_clampScoreAfter_collapse`), and the DDPM score term
`ε² (t_N - t_1)` is at most `ε A₀ + ε² c`. -/
theorem pf_ddpm_midpoint_separation {a : ℝ} (ha : 0 < a) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ u1 : ℝ, 0 < u1 →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ a / (2 * Real.sqrt (1 + u1)) ∧ ∃ A : ℝ, 0 < A ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 2 ≤ N ∧ ∃ K : ℕ, 1 ≤ K ∧ K < N ∧
        geomGrid u1 r N - geomGrid u1 r 1 ≤ A / ε ∧
        (∀ k ∈ Ioc K N, Real.log (2 + 8 * a ^ 2 * R / ε) / 2 ≤ geomGrid u1 r k) ∧
        (∀ k y, ∑ i, (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0
            (ε / R) R K k y i -
          score (fwdDensity (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) k) y i) ^ 2 ≤
            ε ^ 2) ∧
        (∀ k, LipschitzWith ε.toNNReal (fun y =>
          clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 (ε / R) R K k y -
            score (fwdDensity (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) k) y)) ∧
        (fwdLaw (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 1).real
          {x | |x 0| ≤ ρ} ≤ η ∧
        1 - η ≤ (algLaw zeroVar (pfMean (geomGrid u1 r)
            (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 (ε / R) R K))
          (measurable_pfMean_clampScoreAfter _ _ 0 (ε / R) R K) N 1).real {x | |x 0| ≤ ρ} ∧
        1 - 2 * η ≤ TotalVariation.tvSup
          (fwdLaw (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 1)
          (algLaw zeroVar (pfMean (geomGrid u1 r)
            (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 (ε / R) R K))
          (measurable_pfMean_clampScoreAfter _ _ 0 (ε / R) R K) N 1) ∧
        TotalVariation.tvSup (fwdLaw (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 1)
          (algLaw (ddpmVar (geomGrid u1 r)) (scoreMean (geomGrid u1 r)
            (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 (ε / R) R K))
            (measurable_scoreMean _ (measurable_clampScoreAfter _ _ 0 (ε / R) R K)) N 1) ≤
          η := by
  -- the window `[-R, R]` has `N(0, 1)`-mass at least `1 - η`
  obtain ⟨R, hR, ρ', -, -, hwin⟩ := exists_window hη
  have hγ : 1 - η ≤ (gaussianReal 0 1).real (Set.Icc (-R) R) :=
    hwin.trans (sub_le_self _ measureReal_nonneg)
  have hR0 : 0 < R := by linarith
  refine ⟨R, hR, fun u1 hu1 => ?_⟩
  -- the slab radius: `p_1`-mass at most `η`, and at most half the distance from `0` to the
  -- centres `±a/√(1 + u_1)` of the components of `p_1`
  have hv : 0 < Real.sqrt (2 * Real.pi * (u1 / (1 + u1))) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (min (η * Real.sqrt (2 * Real.pi * (u1 / (1 + u1))) / 2)
      (a / (2 * Real.sqrt (1 + u1)))) (1 / 2) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    have : 0 < Real.sqrt (1 + u1) := Real.sqrt_pos.2 (by linarith)
    exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hρa : ρ ≤ a / (2 * Real.sqrt (1 + u1)) :=
    hρdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρη : 2 * ρ / Real.sqrt (2 * Real.pi * (u1 / (1 + u1))) ≤ η := by
    have h : ρ ≤ η * Real.sqrt (2 * Real.pi * (u1 / (1 + u1))) / 2 :=
      hρdef ▸ (min_le_left _ _).trans (min_le_left _ _)
    rw [div_le_iff₀ hv]
    linarith
  have hρ1 : ρ ≤ 1 / 2 := hρdef ▸ min_le_right _ _
  have hρR : ρ < R := by linarith
  -- the horizon constant `A`
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.exp (a ^ 2 / u1) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hCdef ▸ Real.one_le_exp (by positivity)
  have hL : 0 ≤ Real.log (C * R / ρ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hρ0]; nlinarith)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * R * Real.log (C * R / ρ) + (1 + 8 * a ^ 2 * R) :=
    ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  obtain ⟨c, hc, ε₀, hε₀, hε₀1, hpar⟩ := exists_longHorizon_geomGrid_params 1 hu1
    (initConst_nonneg 1 hu1 (integral_nonneg fun x => sum_nonneg fun i _ => sq_nonneg (x i))
      (M := ∫ x, ∑ i, x i ^ 2 ∂(symTwoPoint fun _ : Fin 1 => a))) hA hη
  refine ⟨ρ, hρ0, hρa, A + c + 1, by linarith only [hA, hc], ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans hε₀1
  obtain ⟨r, hr, N, hN, hstep, hTlo, hTup, hbound⟩ := hpar ε hε hεε₀
  have hTA : geomGrid u1 r N - geomGrid u1 r 1 ≤ (A + c + 1) / ε := by
    have hcε : c ≤ c / ε := by rw [le_div_iff₀ hε]; nlinarith only [hc, hε1]
    have h1ε : 0 ≤ 1 / ε := by positivity
    rw [add_div, add_div]
    linarith only [hTup, hcε, h1ε]
  have h0 := geomGrid_zero u1 r
  have ht := geomGrid_strictMono hu1 hr
  -- the horizon covers the neutral-phase threshold and the contraction time
  have hT : Real.log (2 + 8 * a ^ 2 * R / ε) / 2 + 2 * R / ε *
      Real.log (Real.exp (a ^ 2 / (Real.exp (2 * geomGrid u1 r 1) - 1)) * R / ρ) ≤
      geomGrid u1 r N - geomGrid u1 r 1 := by
    rw [exp_two_mul_geomGrid_one hu1 r, add_sub_cancel_left, ← hCdef]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 2 + 8 * a ^ 2 * R / ε by positivity)
    have h2 : 1 ≤ 1 / ε := one_le_one_div hε hε1
    have h3 : 0 ≤ 8 * a ^ 2 * R / ε := by positivity
    have h4 : A / ε = 2 * R / ε * Real.log (C * R / ρ) + (1 / ε + 8 * a ^ 2 * R / ε) := by
      rw [hAdef]
      ring
    linarith
  obtain ⟨K, hK1, hKN, hKT, hq⟩ :=
    exists_pf_clampScoreAfter_collapse a h0 ht (by omega) hstep hε hε1 hR hρ0 hρR hT
  obtain ⟨hacc, hlip, -⟩ :=
    clampScoreAfter_accuracy (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 K hε.le hR
  have hp : (fwdLaw (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 1).real
      {x | |x 0| ≤ ρ} ≤ η := by
    refine (fwdLaw_symTwoPoint_real_abs_le a h0 ht le_rfl hρ0.le).trans ?_
    rw [cumVar_geomGrid_one hu1 r]
    exact hρη
  have hq' := hγ.trans hq
  refine ⟨r, hr, N, hN, K, hK1, hKN, hTA, hKT, hacc, fun k => ?_, hp, hq', ?_, ?_⟩
  · rw [clampScoreAfter_sub_eq]
    exact hlip k
  · have hG : MeasurableSet {x : Fin 1 → ℝ | |x 0| ≤ ρ} :=
      measurableSet_le (by fun_prop) measurable_const
    have hTV := TotalVariation.abs_measureReal_sub_le_tvSup
      (μ := fwdLaw (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 1)
      (ν := algLaw zeroVar (pfMean (geomGrid u1 r)
        (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 (ε / R) R K))
        (measurable_pfMean_clampScoreAfter _ _ 0 (ε / R) R K) N 1) hG
    have := neg_abs_le ((fwdLaw (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 1).real
        {x | |x 0| ≤ ρ} -
      (algLaw zeroVar (pfMean (geomGrid u1 r)
        (clampScoreAfter (symTwoPoint fun _ : Fin 1 => a) (geomGrid u1 r) 0 (ε / R) R K))
        (measurable_pfMean_clampScoreAfter _ _ 0 (ε / R) R K) N 1).real {x | |x 0| ≤ ρ})
    linarith
  · refine (tvSup_ddpm_clampScoreAfter_le_geomGrid (symTwoPoint fun _ : Fin 1 => a)
      (DiffusionTwoPoint.integrable_sum_sq_symTwoPoint _) 0 hu1 hr (by omega : 1 ≤ N)
      (by positivity : 0 ≤ ε / R) hR0.le K).trans ?_
    rw [div_mul_cancel₀ ε hR0.ne', initBound_geomGrid _ hu1 (zero_lt_one.trans hr) (by omega)]
    exact Real.sqrt_le_iff.2 ⟨hη.le, by linarith⟩

end FormalizeSampling.DiffusionODEMidpoint
