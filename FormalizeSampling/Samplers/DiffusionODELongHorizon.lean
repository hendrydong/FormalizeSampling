module

public import FormalizeSampling.Samplers.DiffusionODELipschitz

/-!
# Deterministic versus stochastic reverse samplers: a small Lipschitz score error, long horizon

Status: **Verified** (a separation result; long-horizon companion of
`Samplers/DiffusionODESmooth.lean` and `Samplers/DiffusionODELipschitz.lean`).

Setting of `Samplers/DiffusionODESeparation.lean`, with standard Gaussian data `μ = N(0, I)` on
`Fin d → ℝ` and a coordinate `i₀` (so `d ≥ 1`). The forward marginals are `p_k = N(0, I)` for
every `k` on every grid (`fwdLaw_isoGauss_one`). Deterministic samplers are
`algLaw 0 (detMean A b s)` with score-affine update `m_k(y) = A_k(y) + b_k s_k(y)` whose
**exact-score map is the identity**, `A_k(y) + b_k ∇ log p_k(y) = y`; the example is the
exponential-integrator probability-flow step `pfMean` (`A_k = α_k⁻¹ id`,
`b_k = α_k⁻¹ - 1 = e^{t_k - t_{k-1}} - 1`), for which this holds on every grid
(`pfMean_exactScore_isoGauss_one`). The stochastic sampler is DDPM,
`algLaw (ddpmVar t) (scoreMean t s)`, driven by the same learned score.

## The construction

The learned score is `s_k = ∇ log p_k + E` at **every** step, with the time-independent field
`E(y) = -λ clip_R(y_{i₀}) e_{i₀}`, `clip_R(x) = max(-R, min(R, x))` (`clampErr`, `clampScore`).
Then `|E| ≤ λ R` and `E` is `λ`-Lipschitz; with `λ = ε / R` and `R ≥ 1` the score error is at most
`ε` in sup norm **and** `ε`-Lipschitz. On the window `|y_{i₀}| ≤ R` the perturbed step is
`y_{i₀} ↦ (1 - b_k λ) y_{i₀}`, and for `0 ≤ b_k λ ≤ 1` the window is invariant, so the
deterministic flow `Φ_1 = m_2 ∘ ⋯ ∘ m_N` multiplies coordinate `i₀` of every window point by
`∏_{1 < k ≤ N} (1 - b_k λ)`. For `pfMean`, `b_k = e^{t_k - t_{k-1}} - 1 ≥ t_k - t_{k-1}`, so this
factor is at most `exp(-λ (t_N - t_1))` on every grid. Pick `R` with
`N(0, 1)([-R, R]) ≥ 1 - η/2` and `ρ` with `N(0, 1)([-ρ, ρ]) ≤ η/2`; once
`t_N - t_1 ≥ R log(R/ρ) / ε` the window is mapped into `[-ρ, ρ]`, so the slab
`G = {|x_{i₀}| ≤ ρ}` has `q_1(G) ≥ 1 - η/2` and `p_1(G) ≤ η/2`: `TV(p_1, q_1) ≥ 1 - η`. DDPM pays
`∑_{1 < k ≤ N} (β_k / 2) ε² ≤ ε² (t_N - t_1)` in its KL bound; on a geometric grid with horizon
between `A₀ / ε` and `A₀ / ε + c` (`A₀ = R log(R/ρ)`, `c` independent of `ε`) this is at most
`ε A₀ + ε² c`, hence small for small `ε`, and the horizon is at most `A / ε` with
`A = A₀ + c + 1`.

## Main results

* `sum_sq_clampScore_sub_le`, `lipschitzWith_clampErr`, `eDist_clampErr_le`,
  `clampScore_accuracy`: uniform accuracy `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ (λ R)²` for all `k`,
  `y` (the uniform-accuracy hypothesis of `DiffusionODELipschitz.exists_coupling_detMean`), and a
  `λ`-Lipschitz error field (sup metric and Euclidean distance).
* `detFlow_clampScore_apply` (score-affine steps whose exact-score map is the identity) and
  `detFlow_pf_clampScore_apply` (probability flow): on the window,
  `Φ_1(y)_{i₀} = (∏_{1 < k ≤ N} (1 - b_k λ)) y_{i₀}`.
* `prod_one_sub_pfCoeff_le`: for `pfMean` and `K ≤ N`,
  `∏_{K < k ≤ N} (1 - b_k λ) ≤ exp(-λ (t_N - t_K))` on every grid.
* `tvSup_detOutput_clampScore_ge` (general steps) and `tvSup_pf_clampScore_ge` (probability
  flow): `TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - N(0, 1)([-ρ, ρ])` as soon as
  `(∏ (1 - b_k λ)) R ≤ ρ`, resp. `exp(-λ (t_N - t_1)) R ≤ ρ`.
* `exists_tvSup_pf_clampScore_ge`: for every `η > 0` there are `R ≥ 1` and `0 < ρ ≤ 1` such that
  on **every** grid with steps `≤ log 2` and horizon `t_N - t_1 ≥ R log(R/ρ) / ε`
  (`0 < ε ≤ 1`) the probability-flow output has `TV(p_1, q_1) ≥ 1 - η`;
  `exists_pf_clampScore_collapse_geomGrid` exhibits such a geometric grid for every
  `ε ∈ (0, 1]`.
* `scoreErr_le_of_sum_sq_le`, `tvSup_ddpm_clampScore_le_geomGrid`: DDPM with the same score (any
  data with finite second moment) has
  `TV(p_1, q_1) ≤ √((I + (r - 1) d/2 (1 + (N - 1) log r) + (λ R)² (t_N - t_1)) / 2)`.
* `pf_ddpm_longHorizon_separation` (**separation**): for every `η > 0` there is `R ≥ 1` such
  that for every `u_1 > 0` there are `A > 0` and `ε₀ > 0` such that for every `ε ∈ (0, ε₀]` some
  geometric grid `geomGrid u_1 r` with horizon `t_N - t_1 ≤ A / ε` and `N ≥ 2` give, for one
  learned score whose error is `≤ ε` in sup norm and `ε`-Lipschitz at every step,
  `TV(p_1, q_1^det) ≥ 1 - η` and `TV(p_1, q_1^DDPM) ≤ η`. Its real-analysis core is
  `exists_longHorizon_geomGrid_params`, a variant of
  `DiffusionDiscretization.exists_geomGrid_params` that also prescribes the horizon,
  `A₀ / ε ≤ t_N - t_1 ≤ A₀ / ε + c`.

Relation to the literature: the neutral phase is the setting of Li–Di–Gu (2024,
arXiv:2410.14237, Thm 3.1): for the forward OU process started at `N(0, 1)` the law is
stationary and the exact probability-flow velocity vanishes, so a uniformly small smooth score
error is not corrected by the flow. That the deterministic flow carries a mismatch forward while
the stochastic sampler forgets it is described by Nie et al. (2024, arXiv:2311.01410,
Thms 3.1–3.2) and Cao et al. (2023, arXiv:2306.02063). Here a piecewise-linear clamp error
acting over a horizon of order `1/ε` is formalised for discrete score-affine steps on any grid
with `0 ≤ b_k λ ≤ 1`, together with the DDPM upper bound for the same learned score on geometric
grids. The learned score is uniformly `ε`-accurate, so the synchronous-coupling bound of DF-9
(`DiffusionODELipschitz.eDist_detFlow_le`, `DiffusionODELipschitz.exists_coupling_detMean`;
cf. Beltran-Velez et al. 2026, arXiv:2606.19162, Prop. 3.2, in continuous time) applies to it.
The related construction of `Samplers/DiffusionODESmooth.lean` (DF-7) perturbs a single step
and has a large Lipschitz constant; here the error acts at every step with Lipschitz
constant `ε`.

## Not proved here

* **Gaussian data only.** The collapse uses `p_k = N(0, I)` and that the exact-score map is the
  identity; a version for two-point or multimodal data (an error moving mass between modes or
  creating a further mode) is not here. A version for two-point data in dimension one, with the
  error switched on at high noise and the deterministic output collapsing onto the midpoint, is
  `Samplers/DiffusionODEMidpoint.lean`. Only coordinate `i₀` is perturbed (this suffices for
  every `d ≥ 1`).
* **Long horizon.** The collapse is proved for `t_N - t_1 ≥ R log(R/ρ) / ε`, with `R`, `ρ`
  chosen from `η` by continuity of `N(0, 1)` (no explicit rate in `η`). No lower bound on the
  horizon that a collapse requires is proved: it is not shown that `TV(p_1, q_1^det)` stays
  small for horizons `≪ 1/ε` under an `ε`-small, `ε`-Lipschitz error.
* The error field is switched on at **every** step and does not depend on time; errors acting
  on part of the grid, or time-dependent profiles, are not treated. `clip_R` has two kinks, so
  the field is Lipschitz but not differentiable; a smooth saturating profile is not formalised.
* Lipschitz continuity is stated for the score error `s_k - ∇ log p_k = E`. That the learned
  score `s_k(y) = -y + E(y)` is `(1 + ε)`-Lipschitz for `k ≥ 1` follows from
  `DiffusionGaussian.exactScore_isoGauss` but is not stated.
* The DDPM side is the KL bound of `Samplers/DiffusionMain.lean` through Pinsker; no lower bound
  for DDPM is given. Among steps whose exact-score map is the identity only the
  exponential-integrator step is worked out as an example.
* No transport-distance statement: whether the coupling bound of DF-9 is attained for this
  error, or any lower bound on a transport distance between `q_1` and `p_1`, is not studied.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionODELongHorizon

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
open FormalizeSampling.DiffusionODESeparation FormalizeSampling.DiffusionODELipschitz
open FormalizeSampling.DiffusionGaussian
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingChainPi
open FormalizeSampling.ProximalSharpGaussianPi (scalePi)

variable {d : ℕ}

/-! ### The clamp error field -/

/-- The clamp of `x` to `[-R, R]`: `clip R x = max (-R) (min R x)`. -/
noncomputable def clip (R x : ℝ) : ℝ := max (-R) (min R x)

/-- On the window `|x| ≤ R` the clamp is the identity. -/
theorem clip_of_abs_le {R x : ℝ} (h : |x| ≤ R) : clip R x = x := by
  rw [abs_le] at h
  unfold clip
  rw [min_eq_right h.2, max_eq_right h.1]

/-- Beyond the window the clamp saturates: `clip R x = R` for `0 ≤ R ≤ x`. -/
theorem clip_of_le {R x : ℝ} (hR : 0 ≤ R) (h : R ≤ x) : clip R x = R := by
  unfold clip
  rw [min_eq_left h, max_eq_right (by linarith)]

/-- For `R ≥ 0`, `|clip R x| ≤ R`. -/
theorem abs_clip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clip R x| ≤ R := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- The clamp is `1`-Lipschitz: `|clip R x - clip R y| ≤ |x - y|`. -/
theorem abs_clip_sub_le (R x y : ℝ) : |clip R x - clip R y| ≤ |x - y| := by
  unfold clip
  rw [max_comm (-R), max_comm (-R)]
  exact (abs_max_sub_max_le_abs _ _ _).trans <| by
    simpa using abs_min_sub_min_le_max R x R y

/-- The clamp is continuous. -/
theorem continuous_clip (R : ℝ) : Continuous (clip R) := by
  unfold clip; fun_prop

/-- **The clamp error field** acting on coordinate `i₀`:
`E(y)_{i₀} = -λ clip_R(y_{i₀})`, `E(y)_i = 0` for `i ≠ i₀`. On the window `|y_{i₀}| ≤ R` it is
the linear field `-λ y_{i₀} e_{i₀}`; outside the window it is constant in `y_{i₀}`. It does not
depend on time. -/
noncomputable def clampErr (i₀ : Fin d) (lam R : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if i = i₀ then -lam * clip R (y i₀) else 0

/-- `E` is continuous. -/
theorem continuous_clampErr (i₀ : Fin d) (lam R : ℝ) : Continuous (clampErr i₀ lam R) := by
  refine continuous_pi fun i => ?_
  unfold clampErr
  split_ifs
  · exact continuous_const.mul ((continuous_clip R).comp (continuous_apply i₀))
  · exact continuous_const

/-- `∑ᵢ E(y)ᵢ² = (λ clip_R(y_{i₀}))²`. -/
theorem sum_sq_clampErr (i₀ : Fin d) (lam R : ℝ) (y : Fin d → ℝ) :
    ∑ i, clampErr i₀ lam R y i ^ 2 = (lam * clip R (y i₀)) ^ 2 := by
  simp [clampErr]

/-- **Size of the error field.** For `λ ≥ 0`, `R ≥ 0`: `∑ᵢ E(y)ᵢ² ≤ (λ R)²` for every `y`. -/
theorem sum_sq_clampErr_le (i₀ : Fin d) {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R)
    (y : Fin d → ℝ) : ∑ i, clampErr i₀ lam R y i ^ 2 ≤ (lam * R) ^ 2 := by
  rw [sum_sq_clampErr, ← sq_abs, abs_mul, abs_of_nonneg hlam]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left (abs_clip_le hR _) hlam) 2

/-- **Regularity of the error field (sup metric).** For `λ ≥ 0` the field `E` is
`λ`-Lipschitz for the sup metric of `Fin d → ℝ`. -/
theorem lipschitzWith_clampErr (i₀ : Fin d) {lam : ℝ} (hlam : 0 ≤ lam) (R : ℝ) :
    LipschitzWith lam.toNNReal (clampErr i₀ lam R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ hlam]
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  rw [Real.dist_eq]
  unfold clampErr
  split_ifs
  · rw [show -lam * clip R (x i₀) - -lam * clip R (y i₀) = -(lam * (clip R (x i₀) -
      clip R (y i₀))) by ring, abs_neg, abs_mul, abs_of_nonneg hlam]
    refine mul_le_mul_of_nonneg_left ((abs_clip_sub_le R _ _).trans ?_) hlam
    rw [← Real.dist_eq]
    exact dist_le_pi_dist x y i₀
  · simp only [sub_self, abs_zero]
    exact mul_nonneg hlam dist_nonneg

/-- **Regularity of the error field (Euclidean metric).** For every `x, y`:
`|E(x) - E(y)| ≤ |λ| |x - y|` (Euclidean distance `eDist`). -/
theorem eDist_clampErr_le (i₀ : Fin d) (lam R : ℝ) (x y : Fin d → ℝ) :
    eDist (clampErr i₀ lam R x) (clampErr i₀ lam R y) ≤ |lam| * eDist x y := by
  have e : sqDist (clampErr i₀ lam R x) (clampErr i₀ lam R y) =
      (lam * (clip R (x i₀) - clip R (y i₀))) ^ 2 := by
    rw [sqDist]
    simp only [clampErr]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
    simp only [↓reduceIte]
    ring
  have hx : |x i₀ - y i₀| ≤ eDist x y := by
    rw [eDist, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    rw [sqDist]
    exact Finset.single_le_sum (f := fun i => (x i - y i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i₀)
  rw [eDist, e, Real.sqrt_sq_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_clip_sub_le R _ _).trans hx) (abs_nonneg _)

/-! ### The learned score -/

/-- **The learned score** `s_k = ∇ log p_k + E` for data `μ`: the exact score plus the
time-independent clamp error field `E = clampErr i₀ λ R`, at every step `k`. -/
noncomputable def clampScore (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ) :
    ℕ → (Fin d → ℝ) → Fin d → ℝ :=
  fun k y i => exactScore μ t k y i + clampErr i₀ lam R y i

/-- The learned score is measurable. -/
theorem measurable_clampScore (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    (lam R : ℝ) (k : ℕ) : Measurable (clampScore μ t i₀ lam R k) :=
  Measurable.of_eval fun i => ((measurable_pi_apply i).comp (measurable_exactScore μ t k)).add
    ((measurable_pi_apply i).comp (continuous_clampErr i₀ lam R).measurable)

/-- The score error is the error field: `s_k(y) - ∇ log p_k(y) = E(y)`. -/
theorem clampScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ)
    (k : ℕ) (y : Fin d → ℝ) (i : Fin d) :
    clampScore μ t i₀ lam R k y i - score (fwdDensity μ t k) y i = clampErr i₀ lam R y i := by
  simp only [clampScore, exactScore]; ring

/-- The score error as a function: `y ↦ s_k(y) - ∇ log p_k(y)` is the error field `E`. -/
theorem clampScore_sub_eq (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) (lam R : ℝ)
    (k : ℕ) :
    (fun y => clampScore μ t i₀ lam R k y - score (fwdDensity μ t k) y) = clampErr i₀ lam R := by
  funext y i
  exact clampScore_sub μ t i₀ lam R k y i

/-- **Uniform accuracy.** For `λ ≥ 0`, `R ≥ 0`, every `k` and `y`:
`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ (λ R)²`: the uniform-accuracy hypothesis of
`DiffusionODELipschitz.exists_coupling_detMean` with `ε = λ R` (the same notion that
`DiffusionODESmooth.sum_sq_smoothScore_sub_le` proves for the score of that module). -/
theorem sum_sq_clampScore_sub_le (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R) (k : ℕ) (y : Fin d → ℝ) :
    ∑ i, (clampScore μ t i₀ lam R k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ (lam * R) ^ 2 := by
  simp_rw [clampScore_sub]
  exact sum_sq_clampErr_le i₀ hlam hR y

/-! ### Score-affine steps whose exact-score map is the identity -/

/-- **One perturbed step.** If the exact-score update of step `k` is the identity,
`A_k(y) + b_k ∇ log p_k(y) = y`, then the update driven by `s = ∇ log p + E` is
`y + b_k E(y)`. -/
theorem detMean_clampScore_apply {μ : Measure (Fin d → ℝ)} {t : ℕ → ℝ}
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} {b : ℕ → ℝ} {k : ℕ}
    (hid : detMean A b (exactScore μ t) k = id) (i₀ : Fin d) (lam R : ℝ) (y : Fin d → ℝ)
    (i : Fin d) :
    detMean A b (clampScore μ t i₀ lam R) k y i = y i + b k * clampErr i₀ lam R y i := by
  have h := congrFun (congrFun hid y) i
  simp only [detMean, id] at h
  simp only [detMean, clampScore]
  linear_combination h

/-- `∏_{j ∈ (k, N]} f_j = f_{k+1} ∏_{j ∈ (k+1, N]} f_j` for `k < N`. -/
theorem prod_Ioc_eq_mul {k N : ℕ} (hk : k < N) (f : ℕ → ℝ) :
    ∏ j ∈ Ioc k N, f j = f (k + 1) * ∏ j ∈ Ioc (k + 1) N, f j := by
  rw [← Finset.Icc_add_one_left_eq_Ioc, ← Finset.Ioc_insert_left (by omega : k + 1 ≤ N),
    Finset.prod_insert (by simp)]

/-- A product of factors in `[0, 1]` lies in `[0, 1]`. -/
theorem prod_one_sub_mem_Icc {s : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1) :
    0 ≤ ∏ j ∈ s, (1 - x j) ∧ ∏ j ∈ s, (1 - x j) ≤ 1 :=
  ⟨Finset.prod_nonneg fun j hj => by linarith [(hx j hj).2],
    Finset.prod_le_one₀ (fun j hj => by linarith [(hx j hj).2])
      (fun j hj => by linarith [(hx j hj).1])⟩

/-- **The flow on the window.** Data `μ`, score-affine steps `m_j = A_j + b_j s_j` whose
exact-score map is the identity for `k < j ≤ N`, learned score `s = ∇ log p + E` with
`E = clampErr i₀ λ R`, and `0 ≤ b_j λ ≤ 1` for `k < j ≤ N`. If `|y_{i₀}| ≤ R`, the window is
invariant and the deterministic flow `Φ_k = m_{k+1} ∘ ⋯ ∘ m_N` (`detFlow`) acts on coordinate
`i₀` by the scalar `∏_{k < j ≤ N} (1 - b_j λ)`:
`Φ_k(y)_{i₀} = (∏_{k < j ≤ N} (1 - b_j λ)) y_{i₀}`. -/
theorem detFlow_clampScore_apply {μ : Measure (Fin d → ℝ)} {t : ℕ → ℝ}
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} {b : ℕ → ℝ} (i₀ : Fin d) {lam R : ℝ} {N k : ℕ}
    (hk : k ≤ N) (hid : ∀ j ∈ Ioc k N, detMean A b (exactScore μ t) j = id)
    (hb : ∀ j ∈ Ioc k N, 0 ≤ b j * lam ∧ b j * lam ≤ 1) {y : Fin d → ℝ} (hy : |y i₀| ≤ R) :
    detFlow (detMean A b (clampScore μ t i₀ lam R)) N k y i₀ =
      (∏ j ∈ Ioc k N, (1 - b j * lam)) * y i₀ := by
  induction hn : N - k generalizing k with
  | zero =>
    obtain rfl : k = N := by omega
    simp [detFlow_self]
  | succ n ih =>
    have hlt : k < N := by omega
    have hsub : Ioc (k + 1) N ⊆ Ioc k N := Finset.Ioc_subset_Ioc_left (by omega)
    have ih' := ih (k := k + 1) (by omega) (fun j hj => hid j (hsub hj))
      (fun j hj => hb j (hsub hj)) (by omega)
    have hk1 : k + 1 ∈ Ioc k N := by simp only [mem_Ioc]; omega
    have hP := prod_one_sub_mem_Icc (s := Ioc (k + 1) N) (x := fun j => b j * lam)
      (fun j hj => hb j (hsub hj))
    have hu : |detFlow (detMean A b (clampScore μ t i₀ lam R)) N (k + 1) y i₀| ≤ R := by
      rw [ih', abs_mul, abs_of_nonneg hP.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hP.2).trans hy
    rw [detFlow_of_lt _ hlt, Function.comp_apply, detMean_clampScore_apply (hid _ hk1),
      prod_Ioc_eq_mul hlt]
    simp only [clampErr, ↓reduceIte]
    rw [clip_of_abs_le hu, ih']
    ring

/-! ### The probability-flow step for standard Gaussian data -/

/-- For `N(0, I)` data the forward marginals are `p_k = N(0, I)` (`t_0 = 0`, `t` monotone). -/
theorem fwdLaw_isoGauss_one {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : Monotone t) (k : ℕ) :
    fwdLaw (isoGauss d 1) t k = stdGaussianPi d := by
  rw [fwdLaw_isoGauss zero_le_one h0 ht, gaussVar_one, isoGauss_one]

/-- **The exact-score probability-flow map is the identity for `N(0, I)` data.** For `t_0 = 0`,
`t` strictly increasing and `k ≥ 1`: `α_k⁻¹ y + (α_k⁻¹ - 1) ∇ log p_k(y) = y` (any grid). -/
theorem pfMean_exactScore_isoGauss_one {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {k : ℕ}
    (hk : 1 ≤ k) : detMean (pfLin t) (pfCoeff t) (exactScore (isoGauss d 1) t) k = id := by
  have h := pfMean_trueScore_isoGauss (d := d) one_pos h0 ht hk
  rw [pfGain_one] at h
  funext y i
  have hy := congrFun (congrFun h y) i
  simpa [pfMean, scalePi] using hy

/-- **The probability-flow sampler on the window.** Data `N(0, I)`, `t_0 = 0`, `t` strictly
increasing, `N ≥ 1`, `0 ≤ b_k λ ≤ 1` for `1 < k ≤ N` (`b_k = α_k⁻¹ - 1`), learned score
`s = ∇ log p + clampErr i₀ λ R`. If `|y_{i₀}| ≤ R`, the exponential-integrator flow
`Φ_1 = m_2 ∘ ⋯ ∘ m_N` satisfies `Φ_1(y)_{i₀} = (∏_{1 < k ≤ N} (1 - b_k λ)) y_{i₀}`. -/
theorem detFlow_pf_clampScore_apply (i₀ : Fin d) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {lam R : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hb : ∀ k ∈ Ioc 1 N, 0 ≤ pfCoeff t k * lam ∧ pfCoeff t k * lam ≤ 1) {y : Fin d → ℝ}
    (hy : |y i₀| ≤ R) :
    detFlow (pfMean t (clampScore (isoGauss d 1) t i₀ lam R)) N 1 y i₀ =
      (∏ k ∈ Ioc 1 N, (1 - pfCoeff t k * lam)) * y i₀ :=
  detFlow_clampScore_apply i₀ hN
    (fun k hk => pfMean_exactScore_isoGauss_one h0 ht (by simp only [mem_Ioc] at hk; omega)) hb hy

/-- The exponential-integrator coefficient is `b_k = α_k⁻¹ - 1 = e^{t_k - t_{k-1}} - 1`. -/
theorem pfCoeff_eq (t : ℕ → ℝ) (k : ℕ) : pfCoeff t k = Real.exp (t k - t (k - 1)) - 1 := by
  rw [pfCoeff, fwdScale, Real.exp_neg, inv_inv]

/-- `b_k ≥ t_k - t_{k-1}` (from `e^x ≥ 1 + x`). -/
theorem sub_le_pfCoeff (t : ℕ → ℝ) (k : ℕ) : t k - t (k - 1) ≤ pfCoeff t k := by
  rw [pfCoeff_eq]; linarith [Real.add_one_le_exp (t k - t (k - 1))]

/-- `b_k ≥ 0` on a monotone grid. -/
theorem pfCoeff_nonneg {t : ℕ → ℝ} (ht : Monotone t) (k : ℕ) : 0 ≤ pfCoeff t k :=
  (sub_nonneg.2 (ht (Nat.sub_le k 1))).trans (sub_le_pfCoeff t k)

/-- `b_k ≤ 1` when the step is at most `log 2`. -/
theorem pfCoeff_le_one {t : ℕ → ℝ} {k : ℕ} (h : t k - t (k - 1) ≤ Real.log 2) :
    pfCoeff t k ≤ 1 := by
  rw [pfCoeff_eq]
  have := Real.exp_le_exp.2 h
  rw [Real.exp_log two_pos] at this
  linarith

/-! ### Contraction over a long horizon -/

/-- `∏_{j ∈ s} (1 - x_j) ≤ exp(-∑_{j ∈ s} x_j)` when every `x_j ≤ 1` (from `1 - x ≤ e^{-x}`). -/
theorem prod_one_sub_le_exp {s : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ j ∈ s, x j ≤ 1) :
    ∏ j ∈ s, (1 - x j) ≤ Real.exp (-∑ j ∈ s, x j) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun j hj => by linarith [hx j hj])
    (fun j _ => by linarith [Real.add_one_le_exp (-x j)])

/-- **Grid-free contraction.** For `λ ≥ 0`, `K ≤ N` and `b_k λ ≤ 1` (`K < k ≤ N`,
`b = pfCoeff t`): `∏_{K < k ≤ N} (1 - b_k λ) ≤ exp(-λ (t_N - t_K))`, since
`b_k ≥ t_k - t_{k-1}`. -/
theorem prod_one_sub_pfCoeff_le {t : ℕ → ℝ} {K N : ℕ} (hKN : K ≤ N) {lam : ℝ} (hlam : 0 ≤ lam)
    (hb : ∀ k ∈ Ioc K N, pfCoeff t k * lam ≤ 1) :
    ∏ k ∈ Ioc K N, (1 - pfCoeff t k * lam) ≤ Real.exp (-lam * (t N - t K)) := by
  refine (prod_one_sub_le_exp hb).trans (Real.exp_le_exp.2 ?_)
  have : lam * (t N - t K) ≤ ∑ k ∈ Ioc K N, pfCoeff t k * lam := by
    rw [← sum_Ioc_sub_pred t hKN, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (sub_le_pfCoeff t k) hlam
  linarith

/-! ### The collapse -/

/-- `N(0, I)` gives the slab `{y | |y_{i₀}| ≤ R}` the mass `N(0, 1)([-R, R])`. -/
theorem stdGaussianPi_real_abs_le (i₀ : Fin d) (R : ℝ) :
    (stdGaussianPi d).real {y | |y i₀| ≤ R} = (gaussianReal 0 1).real (Set.Icc (-R) R) := by
  have e : {y : Fin d → ℝ | |y i₀| ≤ R} = Function.eval i₀ ⁻¹' Set.Icc (-R) R := by
    ext y; simp [abs_le]
  rw [e, measureReal_def, measureReal_def, stdGaussianPi,
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i₀).measure_preimage
      measurableSet_Icc.nullMeasurableSet]

/-- **Collapse of a deterministic sampler (general score-affine steps).** Data `N(0, I)` on
`Fin d → ℝ`, `t_0 = 0`, `t` monotone, `N ≥ 1`; deterministic steps `m_k = A_k + b_k s_k`
(measurable `A`) whose exact-score map is the identity for `1 < k ≤ N`; learned score
`s = ∇ log p + E`, `E = clampErr i₀ λ R`; `0 ≤ b_k λ ≤ 1` for `1 < k ≤ N`; and
`(∏_{1 < k ≤ N} (1 - b_k λ)) R ≤ ρ`. Then the deterministic output `q_1` puts mass at least
`N(0, 1)([-R, R])` on the slab `G = {|x_{i₀}| ≤ ρ}`, which has `p_1(G) = N(0, 1)([-ρ, ρ])`, so
`TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - N(0, 1)([-ρ, ρ])`. -/
theorem tvSup_detOutput_clampScore_ge (i₀ : Fin d) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : Monotone t) {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k))
    {b : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hid : ∀ k ∈ Ioc 1 N, detMean A b (exactScore (isoGauss d 1) t) k = id)
    {lam R ρ : ℝ} (hb : ∀ k ∈ Ioc 1 N, 0 ≤ b k * lam ∧ b k * lam ≤ 1)
    (hc : (∏ k ∈ Ioc 1 N, (1 - b k * lam)) * R ≤ ρ) :
    (gaussianReal 0 1).real (Set.Icc (-R) R) - (gaussianReal 0 1).real (Set.Icc (-ρ) ρ) ≤
      TotalVariation.tvSup (fwdLaw (isoGauss d 1) t 1)
        (algLaw zeroVar (detMean A b (clampScore (isoGauss d 1) t i₀ lam R))
          (measurable_detMean hA b (measurable_clampScore _ t i₀ lam R)) N 1) := by
  have hm := measurable_detMean hA b (measurable_clampScore (isoGauss d 1) t i₀ lam R)
  set G : Set (Fin d → ℝ) := {x | |x i₀| ≤ ρ}
  have hG : MeasurableSet G := measurableSet_le (by fun_prop) measurable_const
  have hΦ := measurable_detFlow hm N 1
  have hP := prod_one_sub_mem_Icc hb
  have hsub : {y : Fin d → ℝ | |y i₀| ≤ R} ⊆
      detFlow (detMean A b (clampScore (isoGauss d 1) t i₀ lam R)) N 1 ⁻¹' G := by
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    simp only [Set.mem_preimage, G, Set.mem_ofPred_eq]
    rw [detFlow_clampScore_apply i₀ hN hid hb hy, abs_mul, abs_of_nonneg hP.1]
    exact (mul_le_mul_of_nonneg_left hy hP.1).trans hc
  have hq : (gaussianReal 0 1).real (Set.Icc (-R) R) ≤
      (algLaw zeroVar (detMean A b (clampScore (isoGauss d 1) t i₀ lam R)) hm N 1).real G := by
    rw [algLaw_zeroVar_eq_map, ← stdGaussianPi_real_abs_le i₀ R, measureReal_def,
      measureReal_def, Measure.map_apply hΦ hG]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hp : (fwdLaw (isoGauss d 1) t 1).real G = (gaussianReal 0 1).real (Set.Icc (-ρ) ρ) := by
    rw [fwdLaw_isoGauss_one h0 ht, stdGaussianPi_real_abs_le]
  have hTV := TotalVariation.abs_measureReal_sub_le_tvSup (μ := fwdLaw (isoGauss d 1) t 1)
    (ν := algLaw zeroVar (detMean A b (clampScore (isoGauss d 1) t i₀ lam R)) hm N 1) hG
  have := neg_abs_le ((fwdLaw (isoGauss d 1) t 1).real G -
    (algLaw zeroVar (detMean A b (clampScore (isoGauss d 1) t i₀ lam R)) hm N 1).real G)
  linarith

/-- **Collapse of the probability-flow sampler.** Data `N(0, I)`, `t_0 = 0`, `t` strictly
increasing, `N ≥ 1`, `λ, R ≥ 0`, `b_k λ ≤ 1` for `1 < k ≤ N` (`b_k = α_k⁻¹ - 1`), and
`exp(-λ (t_N - t_1)) R ≤ ρ`. The exponential-integrator sampler `pfMean` driven by
`s = ∇ log p + clampErr i₀ λ R` satisfies
`TV(p_1, q_1) ≥ N(0, 1)([-R, R]) - N(0, 1)([-ρ, ρ])`. -/
theorem tvSup_pf_clampScore_ge (i₀ : Fin d) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {N : ℕ} (hN : 1 ≤ N) {lam R ρ : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R)
    (hb : ∀ k ∈ Ioc 1 N, pfCoeff t k * lam ≤ 1)
    (hc : Real.exp (-lam * (t N - t 1)) * R ≤ ρ) :
    (gaussianReal 0 1).real (Set.Icc (-R) R) - (gaussianReal 0 1).real (Set.Icc (-ρ) ρ) ≤
      TotalVariation.tvSup (fwdLaw (isoGauss d 1) t 1)
        (algLaw zeroVar (pfMean t (clampScore (isoGauss d 1) t i₀ lam R))
          (measurable_detMean (measurable_pfLin t) _ (measurable_clampScore _ t i₀ lam R)) N 1) :=
  tvSup_detOutput_clampScore_ge i₀ h0 ht.monotone (measurable_pfLin t) hN
    (fun k hk => pfMean_exactScore_isoGauss_one h0 ht (by simp only [mem_Ioc] at hk; omega))
    (fun k hk => ⟨mul_nonneg (pfCoeff_nonneg ht.monotone k) hlam, hb k hk⟩)
    ((mul_le_mul_of_nonneg_right (prod_one_sub_pfCoeff_le hN hlam hb) hR).trans hc)

/-! ### Choosing the window -/

/-- **Window parameters.** For `η > 0` there are `R ≥ 1` and `0 < ρ ≤ 1` with
`N(0, 1)([-R, R]) - N(0, 1)([-ρ, ρ]) ≥ 1 - η` (continuity of `N(0, 1)` from below along
`[-n, n]` and from above along `[-1/(j+1), 1/(j+1)]`, whose intersection `{0}` is null). -/
theorem exists_window {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      1 - η ≤ (gaussianReal 0 1).real (Set.Icc (-R) R) -
        (gaussianReal 0 1).real (Set.Icc (-ρ) ρ) := by
  set γ := gaussianReal 0 1
  -- large window
  have hU : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) n) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, abs_le.1 hn⟩
  have hmono : Monotone fun n : ℕ => Set.Icc (-(n : ℝ)) n := fun m n hmn =>
    Set.Icc_subset_Icc (by simp [hmn]) (by simp [hmn])
  have hlim := tendsto_measure_iUnion_atTop (μ := γ) hmono
  rw [hU, measure_univ] at hlim
  have hlt : ENNReal.ofReal (1 - η / 2) < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  obtain ⟨n, hn, hn1⟩ :=
    ((hlim.eventually (lt_mem_nhds hlt)).and (eventually_ge_atTop 1)).exists
  have hbig : 1 - η / 2 ≤ γ.real (Set.Icc (-(n : ℝ)) n) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hn.le
  -- small window
  have hI : (⋂ j : ℕ, Set.Icc (-(1 / ((j : ℝ) + 1))) (1 / ((j : ℝ) + 1))) = {0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (abs_pos.2 hne)
      have := abs_le.2 (hx j)
      linarith
    · rintro rfl j
      constructor <;> [linarith [show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity]; positivity]
  have hanti : Antitone fun j : ℕ => Set.Icc (-(1 / ((j : ℝ) + 1))) (1 / ((j : ℝ) + 1)) :=
    fun i j hij => Set.Icc_subset_Icc (neg_le_neg (Nat.one_div_le_one_div hij))
      (Nat.one_div_le_one_div hij)
  have hlim2 := tendsto_measure_iInter_atTop (μ := γ)
    (fun j => measurableSet_Icc.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have h0 : γ {0} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_singleton 0
  rw [hI, h0] at hlim2
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨j, hj⟩ := (hlim2.eventually (gt_mem_nhds hpos)).exists
  have hsmall : γ.real (Set.Icc (-(1 / ((j : ℝ) + 1))) (1 / ((j : ℝ) + 1))) ≤ η / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hj.le
  refine ⟨n, by exact_mod_cast hn1, 1 / ((j : ℝ) + 1), by positivity, ?_, by linarith⟩
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- **Collapse on every long grid.** For `η > 0` there are `R ≥ 1` and `0 < ρ ≤ 1` such that
for every grid (`t_0 = 0`, strictly increasing) and `N ≥ 1` with steps
`t_k - t_{k-1} ≤ log 2` (`1 < k ≤ N`), and every `0 < ε ≤ 1` with horizon
`t_N - t_1 ≥ R log(R/ρ) / ε`, the probability-flow sampler driven by
`s = ∇ log p + clampErr i₀ (ε/R) R` (score error `≤ ε` in sup norm and `ε`-Lipschitz) has
`TV(p_1, q_1) ≥ 1 - η` on `N(0, I)` data. -/
theorem exists_tvSup_pf_clampScore_ge (i₀ : Fin d) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ t : ℕ → ℝ, t 0 = 0 → StrictMono t → ∀ N : ℕ, 1 ≤ N →
        (∀ k ∈ Ioc 1 N, t k - t (k - 1) ≤ Real.log 2) →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 → R * Real.log (R / ρ) / ε ≤ t N - t 1 →
          1 - η ≤ TotalVariation.tvSup (fwdLaw (isoGauss d 1) t 1)
            (algLaw zeroVar (pfMean t (clampScore (isoGauss d 1) t i₀ (ε / R) R))
              (measurable_detMean (measurable_pfLin t) _
                (measurable_clampScore _ t i₀ (ε / R) R)) N 1) := by
  obtain ⟨R, hR, ρ, hρ, hρ1, hgap⟩ := exists_window hη
  refine ⟨R, hR, ρ, hρ, hρ1, fun t h0 ht N hN hstep ε hε hε1 hT => ?_⟩
  have hR0 : 0 < R := by linarith
  have hlam : 0 ≤ ε / R := by positivity
  have hlam1 : ε / R ≤ 1 := (div_le_one hR0).2 (by linarith)
  refine hgap.trans (tvSup_pf_clampScore_ge i₀ h0 ht hN hlam hR0.le (fun k hk => ?_) ?_)
  · exact (mul_le_mul (pfCoeff_le_one (hstep k hk)) hlam1 hlam zero_le_one).trans_eq (one_mul 1)
  · have hRρ : 0 < R / ρ := by positivity
    have hlog : Real.log (R / ρ) ≤ ε / R * (t N - t 1) := by
      rw [div_le_iff₀ hε] at hT
      rw [div_mul_eq_mul_div, le_div_iff₀ hR0]
      linarith
    calc Real.exp (-(ε / R) * (t N - t 1)) * R ≤ Real.exp (-Real.log (R / ρ)) * R := by
          gcongr; linarith
      _ = ρ := by
          rw [Real.exp_neg, Real.exp_log hRρ]; field_simp

/-! ### The geometric grid -/

/-- `geomGrid u_1 r k = log(1 + u_1 r^{k-1}) / 2` for `k ≥ 1`. -/
theorem geomGrid_of_one_le (u1 r : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    geomGrid u1 r k = Real.log (1 + u1 * r ^ (k - 1)) / 2 := by
  rw [geomGrid, ite_eq_right (by omega)]

/-- On the geometric grid every step after the first is at most `log r / 2`
(`u_1 > 0`, `r ≥ 1`, `k ≥ 2`). -/
theorem geomGrid_step_le {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 ≤ r) {k : ℕ} (hk : 2 ≤ k) :
    geomGrid u1 r k - geomGrid u1 r (k - 1) ≤ Real.log r / 2 := by
  have hr0 : 0 < r := by linarith
  rw [geomGrid_of_one_le u1 r (by omega : 1 ≤ k), geomGrid_of_one_le u1 r (by omega : 1 ≤ k - 1),
    show k - 1 - 1 = k - 2 by omega, show k - 1 = k - 2 + 1 by omega, pow_succ]
  have h1 : 0 < 1 + u1 * r ^ (k - 2) := by positivity
  have h2 : 1 + u1 * (r ^ (k - 2) * r) ≤ r * (1 + u1 * r ^ (k - 2)) := by
    have : r * (1 + u1 * r ^ (k - 2)) = r + u1 * (r ^ (k - 2) * r) := by ring
    linarith
  have := Real.log_le_log (by positivity) h2
  rw [Real.log_mul hr0.ne' h1.ne'] at this
  linarith

/-- Upper bound on the horizon of the geometric grid: `2 (t_N - t_1) ≤ (N - 1) log r`
(`u_1 > 0`, `r ≥ 1`, `N ≥ 1`). -/
theorem two_mul_geomGrid_sub_le {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 ≤ r) {N : ℕ} (hN : 1 ≤ N) :
    2 * (geomGrid u1 r N - geomGrid u1 r 1) ≤ ((N - 1 : ℕ) : ℝ) * Real.log r := by
  rw [geomGrid_of_one_le u1 r hN, geomGrid_of_one_le u1 r le_rfl, Nat.sub_self, pow_zero,
    mul_one, ← Real.log_pow]
  have hx : 1 ≤ r ^ (N - 1) := one_le_pow₀ hr
  have h : 1 + u1 * r ^ (N - 1) ≤ r ^ (N - 1) * (1 + u1) := by nlinarith
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by positivity) (by positivity)] at this
  linarith

/-- Lower bound on the horizon of the geometric grid:
`2 (t_N - t_1) ≥ (N - 1) log r - log((1 + u_1)/u_1)` (`u_1 > 0`, `r > 0`, `N ≥ 1`). -/
theorem le_two_mul_geomGrid_sub {u1 r : ℝ} (hu1 : 0 < u1) (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N) :
    ((N - 1 : ℕ) : ℝ) * Real.log r - Real.log ((1 + u1) / u1) ≤
      2 * (geomGrid u1 r N - geomGrid u1 r 1) := by
  rw [geomGrid_of_one_le u1 r hN, geomGrid_of_one_le u1 r le_rfl, Nat.sub_self, pow_zero,
    mul_one, ← Real.log_pow, Real.log_div (by positivity) hu1.ne']
  have hx : 0 < r ^ (N - 1) := by positivity
  have := Real.log_le_log (by positivity) (show u1 * r ^ (N - 1) ≤ 1 + u1 * r ^ (N - 1) by
    linarith)
  rw [Real.log_mul hu1.ne' hx.ne'] at this
  linarith

/-- **Accuracy and regularity of the learned score.** For `ε ≥ 0`, `R ≥ 1` and `λ = ε / R`:
`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y` (any data `μ`, any grid), the error field
`E = clampErr i₀ λ R` is `ε`-Lipschitz for the sup metric, and `|E(x) - E(y)| ≤ ε |x - y|` for
the Euclidean distance. -/
theorem clampScore_accuracy (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d) {ε R : ℝ}
    (hε : 0 ≤ ε) (hR : 1 ≤ R) :
    (∀ k y, ∑ i, (clampScore μ t i₀ (ε / R) R k y i - score (fwdDensity μ t k) y i) ^ 2 ≤
      ε ^ 2) ∧ LipschitzWith ε.toNNReal (clampErr i₀ (ε / R) R) ∧
      ∀ x y, eDist (clampErr i₀ (ε / R) R x) (clampErr i₀ (ε / R) R y) ≤ ε * eDist x y := by
  have hR0 : 0 < R := by linarith
  have hlam : 0 ≤ ε / R := by positivity
  have hle : ε / R ≤ ε := div_le_self hε hR
  refine ⟨fun k y => ?_, (lipschitzWith_clampErr i₀ hlam R).weaken
    (Real.toNNReal_le_toNNReal hle), fun x y => ?_⟩
  · have := sum_sq_clampScore_sub_le μ t i₀ hlam hR0.le k y
    rwa [div_mul_cancel₀ ε hR0.ne'] at this
  · refine (eDist_clampErr_le i₀ _ R x y).trans ?_
    rw [abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_right hle (eDist_nonneg x y)

/-- **Collapse for a fixed score accuracy (existence).** Data `N(0, I)`, `u_1 > 0`,
`0 < ε ≤ 1`, `η > 0`. On the geometric grid `geomGrid u_1 2` there are `N ≥ 2` and `R ≥ 1` such
that the learned score `s = ∇ log p + clampErr i₀ (ε/R) R` has error `≤ ε` in sup norm, an
`ε`-Lipschitz error field, and the probability-flow sampler has `TV(p_1, q_1) ≥ 1 - η`. -/
theorem exists_pf_clampScore_collapse_geomGrid (i₀ : Fin d) {u1 : ℝ} (hu1 : 0 < u1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ R : ℝ, 1 ≤ R ∧
      (∀ k y, ∑ i, (clampScore (isoGauss d 1) (geomGrid u1 2) i₀ (ε / R) R k y i -
          score (fwdDensity (isoGauss d 1) (geomGrid u1 2) k) y i) ^ 2 ≤ ε ^ 2) ∧
      LipschitzWith ε.toNNReal (clampErr i₀ (ε / R) R) ∧
      1 - η ≤ TotalVariation.tvSup (fwdLaw (isoGauss d 1) (geomGrid u1 2) 1)
        (algLaw zeroVar (pfMean (geomGrid u1 2)
          (clampScore (isoGauss d 1) (geomGrid u1 2) i₀ (ε / R) R))
          (measurable_detMean (measurable_pfLin _) _
            (measurable_clampScore _ _ i₀ (ε / R) R)) N 1) := by
  obtain ⟨R, hR, ρ, hρ, hρ1, hcol⟩ := exists_tvSup_pf_clampScore_ge (d := d) i₀ hη
  set X := R * Real.log (R / ρ) / ε
  set D := Real.log ((1 + u1) / u1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set M := ⌈(2 * X + D) / Real.log 2⌉₊
  have hM : 2 * X + D ≤ M * Real.log 2 := by
    have := Nat.le_ceil ((2 * X + D) / Real.log 2)
    rwa [div_le_iff₀ hlog2] at this
  obtain ⟨hacc, hlip, -⟩ := clampScore_accuracy (isoGauss d 1) (geomGrid u1 2) i₀ hε.le hR
  refine ⟨M + 2, by omega, R, hR, hacc, hlip, hcol _ (geomGrid_zero u1 2)
    (geomGrid_strictMono hu1 one_lt_two) (M + 2) (by omega) (fun k hk => ?_) ε hε hε1 ?_⟩
  · have hk2 : 2 ≤ k := by simp only [mem_Ioc] at hk; omega
    have := geomGrid_step_le hu1 one_le_two hk2
    linarith
  · have h := le_two_mul_geomGrid_sub hu1 two_pos (by omega : 1 ≤ M + 2)
    rw [show M + 2 - 1 = M + 1 by omega] at h
    push_cast at h
    nlinarith

/-! ### DDPM with the same score -/

/-- **The DDPM score term under a uniform score error.** For a probability law `μ`, a monotone
grid, `N ≥ 1`, and `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ e²` for `1 < k ≤ N` and all `y`:
`scoreErr μ t s N ≤ e² (t_N - t_1)` (since `β_k = 1 - e^{-2(t_k - t_{k-1})} ≤ 2 (t_k - t_{k-1})`).
-/
theorem scoreErr_le_of_sum_sq_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (ht : Monotone t) {N : ℕ} (hN : 1 ≤ N) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    {e : ℝ} (hs : ∀ k ∈ Ioc 1 N, ∀ y,
      ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ e ^ 2) :
    scoreErr μ t s N ≤ e ^ 2 * (t N - t 1) := by
  unfold scoreErr scoreErrW
  rw [← sum_Ioc_sub_pred t hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hβ0 : 0 ≤ fwdVar t k := fwdVar_nonneg_of_monotone ht k
  have hβ : fwdVar t k / 2 ≤ t k - t (k - 1) := by
    rw [fwdVar, fwdScale_sq]
    have := Real.add_one_le_exp (-2 * 1 * (t k - t (k - 1)))
    generalize Real.exp (-2 * 1 * (t k - t (k - 1))) = E at this ⊢
    linarith
  have hint : ∫ y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ∂(fwdLaw μ t k) ≤
      e ^ 2 := by
    calc _ ≤ ∫ _y, e ^ 2 ∂(fwdLaw μ t k) :=
          integral_mono_of_nonneg (ae_of_all _ fun y => sum_nonneg fun i _ => sq_nonneg _)
            (integrable_const _) (ae_of_all _ fun y => hs k hk y)
      _ = e ^ 2 := by simp
  have hint0 : 0 ≤ ∫ y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ∂(fwdLaw μ t k) :=
    integral_nonneg fun y => sum_nonneg fun i _ => sq_nonneg _
  calc fwdVar t k / 2 * ∫ y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ∂(fwdLaw μ t k)
      ≤ (t k - t (k - 1)) * e ^ 2 := mul_le_mul hβ hint hint0 (by linarith)
    _ = e ^ 2 * (t k - t (k - 1)) := by ring

/-- The score-error integrand of the learned score is integrable under every probability law
(it is bounded by `(λ R)²`). -/
theorem integrable_sq_clampScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (i₀ : Fin d)
    {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R) (k : ℕ) (ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ν] :
    Integrable (fun y =>
      ∑ i, (clampScore μ t i₀ lam R k y i - score (fwdDensity μ t k) y i) ^ 2) ν := by
  have hmeas : Measurable fun y =>
      ∑ i, (clampScore μ t i₀ lam R k y i - score (fwdDensity μ t k) y i) ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp (measurable_clampScore μ t i₀ lam R k)).sub
        ((measurable_pi_apply i).comp (measurable_exactScore μ t k))).pow_const 2
  refine Integrable.of_bound hmeas.aestronglyMeasurable ((lam * R) ^ 2)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (sum_nonneg fun i _ => sq_nonneg _)]
  exact sum_sq_clampScore_sub_le μ t i₀ hlam hR k y

/-- **DDPM with the same score, geometric grid.** Data `μ` with finite second moment,
`u_1 > 0`, `r > 1`, `N ≥ 1`, `λ, R ≥ 0`: DDPM driven by `s = ∇ log p + clampErr i₀ λ R` has
`TV(p_1, q_1) ≤ √((I + (r - 1) d/2 (1 + (N - 1) log r) + (λ R)² (t_N - t_1)) / 2)`,
`I = initBound` (`tvSup_output_le_geomGrid` with `scoreErr_le_of_sum_sq_le`). -/
theorem tvSup_ddpm_clampScore_le_geomGrid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (i₀ : Fin d) {u1 r : ℝ} (hu1 : 0 < u1)
    (hr : 1 < r) {N : ℕ} (hN : 1 ≤ N) {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R) :
    TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r))
          (scoreMean (geomGrid u1 r) (clampScore μ (geomGrid u1 r) i₀ lam R))
          (measurable_scoreMean _ (measurable_clampScore μ _ i₀ lam R)) N 1) ≤
      Real.sqrt ((initBound μ (geomGrid u1 r) N +
        (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
        (lam * R) ^ 2 * (geomGrid u1 r N - geomGrid u1 r 1)) / 2) := by
  refine (tvSup_output_le_geomGrid μ hμ hu1 hr hN _ (measurable_clampScore μ _ i₀ lam R)
    (fun k _ => integrable_sq_clampScore_sub μ _ i₀ hlam hR k _)).trans ?_
  gcongr
  exact scoreErr_le_of_sum_sq_le μ (geomGrid_strictMono hu1 hr).monotone hN
    (fun k _ y => sum_sq_clampScore_sub_le μ _ i₀ hlam hR k y)

/-! ### The separation -/

/-- **Real-analysis core of the separation: a long geometric grid.** For `u_1 > 0`, `C ≥ 0`,
`A ≥ 0`, `η > 0` there are `c ≥ 0` and `0 < ε₀ ≤ 1` such that for every `0 < ε ≤ ε₀` some
`r > 1`, `N ≥ 2` give, on `t = geomGrid u_1 r`: steps `t_k - t_{k-1} ≤ log 2` (`1 < k ≤ N`),
horizon `A / ε ≤ t_N - t_1 ≤ A / ε + c`, and
`(1 + u_1)/(1 + u_1 r^{N-1}) C + (r - 1) d/2 (1 + (N - 1) log r) + ε² (t_N - t_1) ≤ 2 η²`
(the initialisation, discretisation and score terms of the DDPM bound with a uniform score
error `ε`). By the horizon bounds the score term is at most `ε A + ε² c`. -/
theorem exists_longHorizon_geomGrid_params (d : ℕ) {u1 C A η : ℝ} (hu1 : 0 < u1) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 2 ≤ N ∧
        (∀ k ∈ Ioc 1 N, geomGrid u1 r k - geomGrid u1 r (k - 1) ≤ Real.log 2) ∧
        A / ε ≤ geomGrid u1 r N - geomGrid u1 r 1 ∧
        geomGrid u1 r N - geomGrid u1 r 1 ≤ A / ε + c ∧
        (1 + u1) / (1 + u1 * r ^ (N - 1)) * C +
          (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
          ε ^ 2 * (geomGrid u1 r N - geomGrid u1 r 1) ≤ 2 * η ^ 2 := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * (1 + u1) / u1 := ⟨_, rfl⟩
  have hK0 : 0 ≤ 2 * K / η ^ 2 := by rw [hK]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.log ((1 + u1) / u1) := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; exact Real.log_pos ((one_lt_div hu1).2 (by linarith))
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (D + 2 * K / η ^ 2 + 1) / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨c, hc0.le, min 1 (η ^ 2 / (A + c)), lt_min one_pos (by positivity), min_le_left _ _,
    fun ε hε hεε₀ => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_left _ _)
  have hεη : ε * (A + c) ≤ η ^ 2 := by
    have := hεε₀.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  -- target value `ℓ₀` of `2 (t_N - t_1)`, step `δ = log r`, `N = M + 1`, `ℓ = M δ ∈ [ℓ₀, ℓ₀ + 1]`
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : ℝ, ℓ₀ = 2 * (A / ε) + D + 2 * K / η ^ 2 := ⟨_, rfl⟩
  have hAε : 0 ≤ A / ε := by positivity
  have hℓ₀0 : 0 < ℓ₀ := by rw [hℓ₀]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2); linarith only [this]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (Real.log 2) (η ^ 2 / (2 * (d + 1) * (ℓ₀ + 2))) :=
    ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hlog2 (by positivity)
  have hδ2 : δ ≤ Real.log 2 := by rw [hδ]; exact min_le_left _ _
  have hδη : δ * (2 * (d + 1) * (ℓ₀ + 2)) ≤ η ^ 2 := by
    have := min_le_right (Real.log 2) (η ^ 2 / (2 * (d + 1) * (ℓ₀ + 2)))
    rwa [← hδ, le_div_iff₀ (by positivity)] at this
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈ℓ₀ / δ⌉₊ := ⟨_, rfl⟩
  have hM0 : 1 ≤ M := by rw [hM]; exact Nat.one_le_ceil_iff.2 (by positivity)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = M * δ := ⟨_, rfl⟩
  have hM1 : ℓ₀ ≤ ℓ := by
    rw [hℓ, hM, ← div_le_iff₀ hδ0]; exact Nat.le_ceil _
  have hM2 : ℓ ≤ ℓ₀ + 1 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ ℓ₀ / δ by positivity)
    rw [← hM] at h
    have := mul_lt_mul_of_pos_right h hδ0
    rw [add_mul, div_mul_cancel₀ _ hδ0.ne', one_mul] at this
    rw [hℓ]; linarith only [this, hδ2, hlog21]
  have hℓ0 : 0 < ℓ := hℓ₀0.trans_le hM1
  have hr1 : 1 ≤ Real.exp δ := Real.one_le_exp hδ0.le
  have hNl : ((M + 1 - 1 : ℕ) : ℝ) * Real.log (Real.exp δ) = ℓ := by
    rw [Nat.add_sub_cancel, Real.log_exp, hℓ]
  -- the horizon `T = t_N - t_1`
  have hTlo := le_two_mul_geomGrid_sub hu1 (Real.exp_pos δ) (by omega : 1 ≤ M + 1)
  have hThi := two_mul_geomGrid_sub_le hu1 hr1 (by omega : 1 ≤ M + 1)
  rw [hNl, ← hD] at hTlo
  rw [hNl] at hThi
  set T := geomGrid u1 (Real.exp δ) (M + 1) - geomGrid u1 (Real.exp δ) 1 with hTdef
  have hTup : T ≤ A / ε + c := by linarith only [hThi, hM2, hℓ₀, hc]
  refine ⟨Real.exp δ, Real.one_lt_exp_iff.2 hδ0, M + 1, by omega, fun k hk => ?_,
    by linarith only [hTlo, hM1, hℓ₀, hK0], hTup, ?_⟩
  · have hk2 : 2 ≤ k := by simp only [mem_Ioc] at hk; omega
    have := geomGrid_step_le hu1 hr1 hk2
    rw [Real.log_exp] at this
    linarith only [this, hδ2, hlog2]
  rw [hNl, Nat.add_sub_cancel, ← Real.exp_nat_mul, ← hℓ]
  -- initialisation term
  have hI : (1 + u1) / (1 + u1 * Real.exp ℓ) * C ≤ η ^ 2 / 2 := by
    have he : u1 * ℓ ≤ 1 + u1 * Real.exp ℓ := by
      have h1 : u1 * (ℓ + 1) ≤ u1 * Real.exp ℓ :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp ℓ) hu1.le
      linarith only [h1, hu1]
    have h1 : (1 + u1) / (1 + u1 * Real.exp ℓ) ≤ (1 + u1) / (u1 * ℓ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) he
    have h2 : (1 + u1) / (u1 * ℓ) * C = K / ℓ := by
      rw [hK]; field_simp
    have h4 : 2 * K / η ^ 2 ≤ ℓ := by linarith only [hM1, hℓ₀, hAε, hD0]
    have h3 : K / ℓ ≤ η ^ 2 / 2 := by
      rw [div_le_iff₀ (by positivity)] at h4
      rw [div_le_iff₀ hℓ0]
      linarith only [h4]
    calc (1 + u1) / (1 + u1 * Real.exp ℓ) * C ≤ (1 + u1) / (u1 * ℓ) * C :=
          mul_le_mul_of_nonneg_right h1 hC
      _ = K / ℓ := h2
      _ ≤ η ^ 2 / 2 := h3
  -- discretisation term
  have hDisc : (Real.exp δ - 1) * d / 2 * (1 + ℓ) ≤ η ^ 2 / 2 := by
    have he1 : Real.exp δ - 1 ≤ 2 * δ := by
      have := Real.abs_exp_sub_one_le (x := δ)
        (by rw [abs_of_pos hδ0]; linarith only [hδ2, hlog21])
      rw [abs_of_pos hδ0] at this
      exact (le_abs_self _).trans this
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : (Real.exp δ - 1) * d ≤ 2 * δ * (d + 1) :=
      mul_le_mul he1 (by linarith only) hd (by positivity)
    have h3 : (Real.exp δ - 1) * d * (1 + ℓ) ≤ 2 * δ * (d + 1) * (ℓ₀ + 2) :=
      mul_le_mul h1 (by linarith only [hM2]) (by linarith only [hℓ0]) (by positivity)
    linarith only [h3, hδη]
  -- score term
  have hS : ε ^ 2 * T ≤ η ^ 2 := by
    have h1 : ε ^ 2 * T ≤ ε ^ 2 * (A / ε + c) := mul_le_mul_of_nonneg_left hTup (by positivity)
    have h2 : ε ^ 2 * (A / ε + c) = ε * A + ε ^ 2 * c := by field_simp
    have h3 : ε ^ 2 * c ≤ ε * c :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hε, hε1]) hc0.le
    linarith only [h1, h2, h3, hεη]
  linarith only [hI, hDisc, hS]

/-- **Long-horizon separation (DDPM vs probability-flow sampler, same learned score,
`ε`-Lipschitz score error).** Data `N(0, I)` on `Fin d → ℝ`, coordinate `i₀`, `η > 0`. There is
`R ≥ 1` such that for every `u_1 > 0` there are `A > 0` and `ε₀ > 0` such that for every
`0 < ε ≤ ε₀` there are a geometric grid `geomGrid u_1 r` (`r > 1`) and `N ≥ 2` for which
1. the horizon is at most `A / ε`: `t_N - t_1 ≤ A / ε`;

and the learned score `s = ∇ log p + clampErr i₀ (ε/R) R` satisfies
2. `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y`;
3. the score error `y ↦ s_k(y) - ∇ log p_k(y)` is `ε`-Lipschitz (sup metric) at every step;
4. the deterministic exponential-integrator sampler `pfMean` has `TV(p_1, q_1) ≥ 1 - η`;
5. DDPM with the same `s` has `TV(p_1, q_1) ≤ η`.
`R` does not depend on the grid parameter `u_1` or on `ε`. In the proof, `R` and a radius
`0 < ρ ≤ 1` are chosen from `η` alone (`exists_window`), and the grid has horizon
`A₀ / ε ≤ t_N - t_1 ≤ A₀ / ε + c` with `A₀ = R log(R/ρ)` and `c` independent of `ε`
(`exists_longHorizon_geomGrid_params`), so `A = A₀ + c + 1` works for `ε ≤ 1`: the lower end
makes the deterministic sampler collapse (`exists_tvSup_pf_clampScore_ge`), and the DDPM score
term `ε² (t_N - t_1)` is at most `ε A₀ + ε² c`. -/
theorem pf_ddpm_longHorizon_separation (i₀ : Fin d) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ u1 : ℝ, 0 < u1 → ∃ A : ℝ, 0 < A ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 2 ≤ N ∧
        geomGrid u1 r N - geomGrid u1 r 1 ≤ A / ε ∧
        (∀ k y, ∑ i, (clampScore (isoGauss d 1) (geomGrid u1 r) i₀ (ε / R) R k y i -
            score (fwdDensity (isoGauss d 1) (geomGrid u1 r) k) y i) ^ 2 ≤ ε ^ 2) ∧
        (∀ k, LipschitzWith ε.toNNReal (fun y =>
          clampScore (isoGauss d 1) (geomGrid u1 r) i₀ (ε / R) R k y -
            score (fwdDensity (isoGauss d 1) (geomGrid u1 r) k) y)) ∧
        1 - η ≤ TotalVariation.tvSup (fwdLaw (isoGauss d 1) (geomGrid u1 r) 1)
          (algLaw zeroVar (pfMean (geomGrid u1 r)
            (clampScore (isoGauss d 1) (geomGrid u1 r) i₀ (ε / R) R))
            (measurable_detMean (measurable_pfLin _) _
              (measurable_clampScore _ _ i₀ (ε / R) R)) N 1) ∧
        TotalVariation.tvSup (fwdLaw (isoGauss d 1) (geomGrid u1 r) 1)
          (algLaw (ddpmVar (geomGrid u1 r)) (scoreMean (geomGrid u1 r)
            (clampScore (isoGauss d 1) (geomGrid u1 r) i₀ (ε / R) R))
            (measurable_scoreMean _ (measurable_clampScore _ _ i₀ (ε / R) R)) N 1) ≤ η := by
  obtain ⟨R, hR, ρ, hρ, hρ1, hcol⟩ := exists_tvSup_pf_clampScore_ge (d := d) i₀ hη
  have hR0 : 0 < R := by linarith
  have hL : 0 ≤ R * Real.log (R / ρ) :=
    mul_nonneg hR0.le (Real.log_nonneg ((one_le_div hρ).2 (hρ1.trans hR)))
  refine ⟨R, hR, fun u1 hu1 => ?_⟩
  obtain ⟨c, hc, ε₀, hε₀, hε₀1, hpar⟩ := exists_longHorizon_geomGrid_params d hu1
    (initConst_nonneg d hu1 (integral_nonneg fun x => sum_nonneg fun i _ => sq_nonneg (x i))
      (M := ∫ x, ∑ i, x i ^ 2 ∂(isoGauss d 1))) hL hη
  refine ⟨R * Real.log (R / ρ) + c + 1, by linarith only [hL, hc], ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨r, hr, N, hN, hstep, hT, hTup, hbound⟩ := hpar ε hε hεε₀
  have hε1 : ε ≤ 1 := hεε₀.trans hε₀1
  have hTA : geomGrid u1 r N - geomGrid u1 r 1 ≤ (R * Real.log (R / ρ) + c + 1) / ε := by
    have hcε : c ≤ c / ε := by rw [le_div_iff₀ hε]; nlinarith only [hc, hε1]
    have h1ε : 0 ≤ 1 / ε := by positivity
    rw [add_div, add_div]
    linarith only [hTup, hcε, h1ε]
  obtain ⟨hacc, hlip, -⟩ := clampScore_accuracy (isoGauss d 1) (geomGrid u1 r) i₀ hε.le hR
  refine ⟨r, hr, N, hN, hTA, hacc, fun k => ?_, hcol _ (geomGrid_zero u1 r)
    (geomGrid_strictMono hu1 hr) N (by omega) hstep ε hε hε1 hT, ?_⟩
  · rw [clampScore_sub_eq]
    exact hlip
  refine (tvSup_ddpm_clampScore_le_geomGrid (isoGauss d 1)
    (GaussianLSIPi.integrable_sum_sq_pi_gaussianReal (d := d) 1) i₀
    hu1 hr (by omega : 1 ≤ N) (by positivity : 0 ≤ ε / R) hR0.le).trans ?_
  rw [div_mul_cancel₀ ε hR0.ne', initBound_geomGrid _ hu1 (zero_lt_one.trans hr) (by omega)]
  exact Real.sqrt_le_iff.2 ⟨hη.le, by linarith⟩

end FormalizeSampling.DiffusionODELongHorizon
