module

public import Mathlib.MeasureTheory.Order.Group.Lattice
public import FormalizeSampling.Samplers.DiffusionODESeparation
public import FormalizeSampling.Samplers.DiffusionODESmoothMap

/-!
# Deterministic versus stochastic reverse samplers: separation with a smooth (analytic) score error

Status: **Verified** (DF-7; a separation result; smooth companion of
`Samplers/DiffusionODESeparation.lean`, DF-3).

Setting of `Samplers/DiffusionODESeparation.lean`: data `μ` on `Fin d → ℝ` (`d ≥ 1`), forward
marginals `p_k = fwdLaw μ t k`, deterministic sampler `algLaw 0 (detMean A b s)` with score-affine
update `m_k(y) = A_k(y) + b_k s_k(y)`, `b_2 ≠ 0` (example: the exponential-integrator
probability-flow step `pfMean`). DF-3 uses a discontinuous (`Int.fract`) score error and gets
`TV = 1`. Here the score error is an **analytic** function of the exact update, uniformly `≤ ε`,
and the deterministic output has `TV ≥ 1 - η` for any prescribed `η > 0`.

Relation to the literature: the closest earlier result is Li–Di–Gu (2024, arXiv:2410.14237,
Thm 3.1 and Remark 3.2), a smooth score within `ε` of the true score at every time and point for
which the continuous-time probability-flow ODE from `N(0, 1)` data stays at `TV ≥ 1/(4π)`. The
statement here reaches `TV ≥ 1 - η` for every data law with finite second moment, for a discrete
step, at the price of a large Lipschitz constant (below).

## The construction

`ψ(u) = u - sin(2πu)/(2π)` (`DiffusionODESmoothMap.lean`) fixes `½ℤ`; integers are
superattracting, half-integers repelling. Its iterate `Φ_m = ψ^[m]` is analytic, satisfies
`Φ_m(u + n) = Φ_m(u) + n` and `|Φ_m(u) - u| ≤ 1/2`, and sends every point not in `½ + ℤ` to the
nearest integer as `m → ∞`. At step `k = 2`, coordinate `i₀ = 0`, the learned score is
`s_2 = ∇ log p_2 + E(z)` with `E(z)_{i₀} = b_2⁻¹ (θ + h Φ_m((z_{i₀} - θ)/h) - z_{i₀})`
(`smoothErr`, `smoothScore`), `z` the exact update; so the perturbed update is
`θ + h Φ_m((z_{i₀} - θ)/h)` and `|E| ≤ h / (2|b_2|) = ε` for `h = 2|b_2| ε`. The proof picks
`θ` such that the law of `z_{i₀}` has no atom on the repelling set `θ + h/2 + hℤ`
(`exists_shift_atom_free`), then `r` with `p_1(G_r) ≤ η/2` for the test set
`G_r = {x | dist((x_{i₀} - θ)/h, ℤ) ≤ r}` (continuity from above, `p_1 ≪ Lebesgue`), then `m` with
`q_1(G_rᶜ) ≤ η/2` (continuity from above along `m`). Hence `TV ≥ q_1(G_r) - p_1(G_r) ≥ 1 - η`.

## Main results

* `contDiff_smoothErr`: the error field is `ContDiff ℝ ⊤` (analytic); `sum_sq_smoothErr_le`,
  `sum_sq_smoothScore_sub_le`: uniform accuracy `∑ᵢ (s_k - ∂ᵢ log p_k)² ≤ ε²` for all `k`, `y`.
* `exists_tvSup_detOutput_smoothScore_ge`: for every `η > 0` some `θ, m` give
  `TV(p_1, q_1^det) ≥ 1 - η`.
* `tvSup_ddpm_smoothScore_le`: DDPM with the same score satisfies the DF-1 bound
  `√((I + (κ d/2)(1 + log(u_N/u_1)) + (β_2/2) ε²)/2)`.
* `ddpm_ddim_smooth_separation` (general `A`, `b`) and `pf_ddpm_smooth_separation_geomGrid`
  (probability-flow example, geometric grid): the combined existence statements.
* `lipschitzWith_errProfile`, `le_of_lipschitzWith_errProfile`: the error profile has Lipschitz
  constant between `(2^m - 1)/|b_2|` and `(2^m + 1)/|b_2|`.

## Not proved here

* **Necessity of a large Lipschitz constant.** The iteration count `m` is obtained
  non-constructively, so no Lean statement says `Lip(E) → ∞` as `η → 0`, and no complementary
  positive result ("a score error with Lipschitz constant `L` gives deterministic TV error
  `≤ f(L, ε)`") is formalised. Heuristically (and numerically, `showcase/ode_smooth.py`) any
  `Z`-periodic map that puts mass `1 - η` within `r h` of the lattice must have slope `≳ 1/η` on
  the rest of each cell, so `b_2 Lip(E) ≳ 1/η`; with this construction `b_2 Lip(E) ≈ 2^m`,
  of order `1/η` (between `2/η` and about `10/η` in the experiment).
* Only coordinate `i₀ = 0` is perturbed (this suffices for every `d ≥ 1`). The *learned score*
  is `∇ log p_2 + E ∘ z`; its smoothness in `y` additionally needs smoothness of `A_2` and of the
  true score, which is not formalised here (only `E` is shown to be analytic).
* No rate: `θ`, `r` and `m` are not quantified in terms of `ε, η` or the data.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionODESmooth

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization
open FormalizeSampling.DiffusionODESeparation

variable {d : ℕ}

/-- The one-dimensional collapse map at scale `h` and offset `θ`:
`cellCoord h θ m x = θ + h Φ_m((x - θ) / h)`. -/
noncomputable def cellCoord (h θ : ℝ) (m : ℕ) (x : ℝ) : ℝ := θ + h * cellMap m ((x - θ) / h)

/-- **The smooth error field** `E : ℝ^d → ℝ^d`, acting on coordinate `i₀` only:
`E(z)_{i₀} = c (θ + h Φ_m((z_{i₀} - θ)/h) - z_{i₀})`, `E(z)_i = 0` for `i ≠ i₀`. With
`c = b_2⁻¹` the deterministic update `z + b_2 E(z)` replaces `z_{i₀}` by
`cellCoord h θ m z_{i₀}`. -/
noncomputable def smoothErr (i₀ : Fin d) (c h θ : ℝ) (m : ℕ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if i = i₀ then c * (cellCoord h θ m (z i₀) - z i₀) else 0

/-- **The smooth learned score.** Equal to the true score `∇ log p_k` for `k ≠ 2`; at `k = 2`,
`s_2(y) = ∇ log p_2(y) + E(z(y))` with `E = smoothErr i₀ b_2⁻¹ h θ m` and
`z(y) = A_2(y) + b_2 ∇ log p_2(y)` the exact deterministic update (as in `latticeScore`, with the
floor replaced by the analytic map `Φ_m`). -/
noncomputable def smoothScore (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (i₀ : Fin d) (h θ : ℝ) (m : ℕ) :
    ℕ → (Fin d → ℝ) → Fin d → ℝ :=
  fun k y i => exactScore μ t k y i +
    if k = 2 then smoothErr i₀ (b 2)⁻¹ h θ m (detMean A b (exactScore μ t) 2 y) i else 0

/-- `cellCoord h θ m` is analytic. -/
theorem contDiff_cellCoord (h θ : ℝ) (m : ℕ) : ContDiff ℝ ⊤ (cellCoord h θ m) := by
  unfold cellCoord
  exact contDiff_const.add (contDiff_const.mul
    ((contDiff_cellMap m).comp ((contDiff_id.sub contDiff_const).div_const h)))

/-- **Smoothness.** The error field `E = smoothErr i₀ c h θ m` is `ContDiff ℝ ⊤` (analytic). -/
theorem contDiff_smoothErr (i₀ : Fin d) (c h θ : ℝ) (m : ℕ) :
    ContDiff ℝ ⊤ (smoothErr i₀ c h θ m) := by
  refine contDiff_pi.2 fun i => ?_
  unfold smoothErr
  split_ifs
  · have he : ContDiff ℝ ⊤ fun z : Fin d → ℝ => z i₀ := by fun_prop
    exact contDiff_const.mul (((contDiff_cellCoord h θ m).comp he).sub he)
  · exact contDiff_const

/-- `cellCoord h θ m x - x = h (Φ_m(u) - u)` with `u = (x - θ)/h` (`h ≠ 0`). -/
theorem cellCoord_sub (h θ : ℝ) (m : ℕ) {x : ℝ} (hh : h ≠ 0) :
    cellCoord h θ m x - x = h * (cellMap m ((x - θ) / h) - (x - θ) / h) := by
  unfold cellCoord; field_simp; ring

/-- For `h > 0`, `|cellCoord h θ m x - x| ≤ h/2` for all `x`. -/
theorem abs_cellCoord_sub_le {h : ℝ} (hh : 0 < h) (θ : ℝ) (m : ℕ) (x : ℝ) :
    |cellCoord h θ m x - x| ≤ h / 2 := by
  rw [cellCoord_sub h θ m hh.ne', abs_mul, abs_of_pos hh]
  have := abs_cellMap_sub_le m ((x - θ) / h)
  nlinarith

/-- **Uniform size of the error field.** For `h > 0` and `|c| h / 2 ≤ ε`:
`∑ᵢ E(z)ᵢ² ≤ ε²` for every `z`. -/
theorem sum_sq_smoothErr_le (i₀ : Fin d) {c h : ℝ} (hh : 0 < h) (θ : ℝ) (m : ℕ) {ε : ℝ}
    (hε : |c| * h / 2 ≤ ε) (z : Fin d → ℝ) :
    ∑ i, smoothErr i₀ c h θ m z i ^ 2 ≤ ε ^ 2 := by
  have : ∑ i, smoothErr i₀ c h θ m z i ^ 2 = (c * (cellCoord h θ m (z i₀) - z i₀)) ^ 2 := by
    simp [smoothErr]
  rw [this, ← sq_abs, abs_mul]
  have h1 := abs_cellCoord_sub_le hh θ m (z i₀)
  have h2 : |c| * |cellCoord h θ m (z i₀) - z i₀| ≤ ε :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg c)).trans (by linarith)
  exact pow_le_pow_left₀ (by positivity) h2 2

/-- The smooth score is measurable when `A` is. -/
theorem measurable_smoothScore (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) (i₀ : Fin d)
    (h θ : ℝ) (m : ℕ) (k : ℕ) : Measurable (smoothScore μ t A b i₀ h θ m k) := by
  refine Measurable.of_eval fun i => ?_
  refine ((measurable_pi_apply i).comp (measurable_exactScore μ t k)).add ?_
  split_ifs
  · exact (measurable_pi_apply i).comp ((contDiff_smoothErr i₀ _ h θ m).continuous.measurable.comp
      (measurable_detMean hA b (measurable_exactScore μ t) 2))
  · exact measurable_const

/-- `s_k - ∇ log p_k` is `E(z(y))` at `k = 2` and `0` otherwise. -/
theorem smoothScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (i₀ : Fin d) (h θ : ℝ) (m k : ℕ)
    (y : Fin d → ℝ) (i : Fin d) :
    smoothScore μ t A b i₀ h θ m k y i - score (fwdDensity μ t k) y i =
      if k = 2 then smoothErr i₀ (b 2)⁻¹ h θ m (detMean A b (exactScore μ t) 2 y) i else 0 := by
  simp only [smoothScore, exactScore]; ring

/-- **The perturbed deterministic update.** For `b_2 ≠ 0`, coordinate `i₀` of
`A_2(y) + b_2 s_2(y)` equals `θ + h Φ_m((z_{i₀}(y) - θ)/h)`. -/
theorem detMean_smoothScore_apply (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) {b : ℕ → ℝ} (hb : b 2 ≠ 0) (i₀ : Fin d) (h θ : ℝ)
    (m : ℕ) (y : Fin d → ℝ) :
    detMean A b (smoothScore μ t A b i₀ h θ m) 2 y i₀ =
      cellCoord h θ m (detMean A b (exactScore μ t) 2 y i₀) := by
  simp only [detMean, smoothScore, smoothErr, ↓reduceIte]
  field_simp
  ring


/-! ### The scalar error profile and its Lipschitz constant -/

/-- The scalar profile `e(x) = c (θ + h Φ_m((x - θ)/h) - x)` of the error field. -/
noncomputable def errProfile (c h θ : ℝ) (m : ℕ) (x : ℝ) : ℝ := c * (cellCoord h θ m x - x)

/-- `E(z)_{i₀} = errProfile c h θ m (z_{i₀})`. -/
theorem smoothErr_apply_self (i₀ : Fin d) (c h θ : ℝ) (m : ℕ) (z : Fin d → ℝ) :
    smoothErr i₀ c h θ m z i₀ = errProfile c h θ m (z i₀) := by
  simp [smoothErr, errProfile]

/-- Derivative of `cellCoord`: `Φ_m'((x - θ)/h)` (`h ≠ 0`). -/
theorem hasDerivAt_cellCoord {h : ℝ} (hh : h ≠ 0) (θ : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (cellCoord h θ m) (deriv (cellMap m) ((x - θ) / h)) x := by
  have hin : HasDerivAt (fun x : ℝ => (x - θ) / h) (1 / h) x :=
    ((hasDerivAt_id x).sub_const θ).div_const h
  have hout : HasDerivAt (cellMap m) (deriv (cellMap m) ((x - θ) / h)) ((x - θ) / h) :=
    ((contDiff_cellMap m).differentiable (by simp) _).hasDerivAt
  have := ((hout.comp x hin).const_mul h).const_add θ
  convert this using 1
  · rfl
  · field_simp

/-- Derivative of the profile: `e'(x) = c (Φ_m'((x - θ)/h) - 1)`. -/
theorem hasDerivAt_errProfile {c h : ℝ} (hh : h ≠ 0) (θ : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (errProfile c h θ m) (c * (deriv (cellMap m) ((x - θ) / h) - 1)) x :=
  ((hasDerivAt_cellCoord hh θ m x).sub (hasDerivAt_id x)).const_mul c

/-- At the repelling points `x = θ + h/2` (mod `h`): `e'(x) = c (2^m - 1)`. -/
theorem hasDerivAt_errProfile_half {c h : ℝ} (hh : h ≠ 0) (θ : ℝ) (m : ℕ) :
    HasDerivAt (errProfile c h θ m) (c * (2 ^ m - 1)) (θ + h / 2) := by
  have := hasDerivAt_errProfile (c := c) hh θ m (θ + h / 2)
  have e : (θ + h / 2 - θ) / h = 1 / 2 := by field_simp; ring
  rwa [e, (hasDerivAt_cellMap_half m).deriv] at this

/-- **Upper Lipschitz bound.** The profile is `|c| (2^m + 1)`-Lipschitz (`h ≠ 0`). -/
theorem lipschitzWith_errProfile (c : ℝ) {h : ℝ} (hh : h ≠ 0) (θ : ℝ) (m : ℕ) :
    LipschitzWith (‖c‖₊ * (2 ^ m + 1)) (errProfile c h θ m) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_errProfile hh θ m x).differentiableAt) fun x => ?_
  rw [(hasDerivAt_errProfile hh θ m x).deriv, ← NNReal.coe_le_coe, coe_nnnorm]
  have hD := norm_deriv_le_of_lipschitz (x₀ := (x - θ) / h) (lipschitzWith_cellMap m)
  push_cast at hD ⊢
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at *
  have : |deriv (cellMap m) ((x - θ) / h) - 1| ≤ 2 ^ m + 1 :=
    (abs_sub _ _).trans (by simp only [abs_one]; linarith)
  exact mul_le_mul_of_nonneg_left this (abs_nonneg c)

/-- **Lower Lipschitz bound.** Any Lipschitz constant `K` of the profile satisfies
`|c| (2^m - 1) ≤ K`. With `c = b_2⁻¹`: the error field is uniformly `≤ ε` but its Lipschitz
constant is `≥ (2^m - 1)/|b_2|`, independent of `ε`. -/
theorem le_of_lipschitzWith_errProfile {c h : ℝ} (hh : h ≠ 0) (θ : ℝ) (m : ℕ) {K : ℝ≥0}
    (hK : LipschitzWith K (errProfile c h θ m)) : |c| * (2 ^ m - 1) ≤ K := by
  have := norm_deriv_le_of_lipschitz (x₀ := θ + h / 2) hK
  rwa [(hasDerivAt_errProfile_half hh θ m).deriv, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (a := (2 : ℝ) ^ m - 1)
      (by have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ one_le_two; linarith)] at this

/-! ### Measure-theoretic lemmas -/

/-- Auxiliary congruence: `algLawAux … N j` depends only on the mean maps at indices `> N - j`. -/
theorem algLawAux_congr (σ2 : ℕ → ℝ≥0) {m m' : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hm : ∀ k, Measurable (m k)) (hm' : ∀ k, Measurable (m' k)) (N : ℕ) :
    ∀ j, j ≤ N → (∀ k, N - j < k → m k = m' k) →
      algLawAux σ2 m hm N j = algLawAux σ2 m' hm' N j := by
  intro j
  induction j with
  | zero => intro _ _; rfl
  | succ j ih =>
    intro hj h
    simp only [algLawAux]
    rw [ih (by omega) (fun k hk => h k (by omega))]
    congr 1
    ext y : 1
    simp [algKernel, gaussKernelPi_apply, h (N - j) (by omega)]

/-- The sampler's law at index `2` depends only on the mean maps `m_k`, `k > 2` (`N ≥ 2`). -/
theorem algLaw_two_congr (σ2 : ℕ → ℝ≥0) {m m' : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hm : ∀ k, Measurable (m k)) (hm' : ∀ k, Measurable (m' k)) {N : ℕ} (hN : 2 ≤ N)
    (h : ∀ k, 2 < k → m k = m' k) : algLaw σ2 m hm N 2 = algLaw σ2 m' hm' N 2 :=
  algLawAux_congr σ2 hm hm' N (N - 2) (by omega) fun k hk => h k (by omega)

/-- For a finite measure `ν` on `ℝ` and `h ∈ ℝ` there is an offset `θ` such that `ν` has no atom
on `θ + h/2 + hℤ` (atoms are countable, `ℝ` is not). -/
theorem exists_shift_atom_free (ν : Measure ℝ) [IsFiniteMeasure ν] (h : ℝ) :
    ∃ θ : ℝ, ∀ n : ℤ, ν {θ + h / 2 + h * n} = 0 := by
  set S := {a : ℝ | 0 < ν {a}}
  have hS : S.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := ν) (As := fun a : ℝ => ({a} : Set ℝ)) (fun _ => measurableSet_singleton _)
    (fun a b hab => Set.disjoint_singleton.2 hab)
  set T := ⋃ n : ℤ, (fun a => a - h / 2 - h * n) '' S
  have hT : T.Countable := Set.countable_iUnion fun n => hS.image _
  obtain ⟨θ, hθ⟩ : ∃ θ, θ ∉ T := by
    by_contra hc
    push Not at hc
    exact Set.not_countable_univ (hT.mono fun x _ => hc x)
  refine ⟨θ, fun n => ?_⟩
  by_contra hne
  exact hθ (Set.mem_iUnion.2 ⟨n, θ + h / 2 + h * n, pos_iff_ne_zero.2 hne, by ring⟩)

/-- The test set `G_r = {x | ∃ n ∈ ℤ, |(x_{i₀} - θ)/h - n| ≤ r}`: coordinate `i₀` within `r h`
of the shifted lattice `θ + hℤ`. -/
def goodSet (i₀ : Fin d) (h θ r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ n : ℤ, |(x i₀ - θ) / h - n| ≤ r}

/-- `G_r` is measurable. -/
theorem measurableSet_goodSet (i₀ : Fin d) (h θ r : ℝ) : MeasurableSet (goodSet i₀ h θ r) := by
  have : goodSet i₀ h θ r = ⋃ n : ℤ, {x | |(x i₀ - θ) / h - n| ≤ r} := by
    ext; simp [goodSet]
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_le (by fun_prop) measurable_const

/-- `⋂_j G_{1/(j+1)} ⊆ {x | x_{i₀} ∈ θ + hℤ}` (`h ≠ 0`). -/
theorem iInter_goodSet_subset (i₀ : Fin d) {h : ℝ} (hh : h ≠ 0) (θ : ℝ) :
    ⋂ j : ℕ, goodSet i₀ h θ (1 / (j + 1)) ⊆
      Function.eval i₀ ⁻¹' Set.range (fun n : ℤ => θ + h * n) := by
  intro x hx
  simp only [Set.mem_iInter, goodSet, Set.mem_ofPred_eq] at hx
  set w := (x i₀ - θ) / h with hw_def
  have hw : |w - round w| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hlt
    obtain ⟨n, hn⟩ := hx j
    have := (round_le w n).trans hn
    linarith
  refine ⟨round w, ?_⟩
  have hw' : w = round w := by have := abs_eq_zero.1 hw; linarith
  simp only [Function.eval]
  rw [← hw', hw_def]
  field_simp
  ring

/-- For a finite `p ≪ Lebesgue`, `p(G_{1/(j+1)}) → 0` as `j → ∞`. -/
theorem tendsto_measure_goodSet (p : Measure (Fin d → ℝ)) [IsFiniteMeasure p]
    (hp : p ≪ volume) (i₀ : Fin d) {h : ℝ} (hh : h ≠ 0) (θ : ℝ) :
    Tendsto (fun j : ℕ => p (goodSet i₀ h θ (1 / (j + 1)))) atTop (𝓝 0) := by
  have hnull : p (⋂ j : ℕ, goodSet i₀ h θ (1 / (j + 1))) = 0 := by
    refine hp (measure_mono_null (iInter_goodSet_subset i₀ hh θ) ?_)
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ ((Set.countable_range _).measure_zero _)
  rw [← hnull]
  refine tendsto_measure_iInter_atTop
    (fun j => (measurableSet_goodSet i₀ h θ _).nullMeasurableSet) ?_ ⟨0, measure_ne_top _ _⟩
  intro j k hjk x ⟨n, hn⟩
  exact ⟨n, hn.trans (Nat.one_div_le_one_div hjk)⟩

/-- `y ↦ g y - round (g y)` is measurable when `g` is. -/
theorem measurable_sub_round {X : Type*} [MeasurableSpace X] {g : X → ℝ} (hg : Measurable g) :
    Measurable fun y => g y - round (g y) := by
  simp_rw [round_eq]
  exact hg.sub ((measurable_of_countable fun n : ℤ => (n : ℝ)).comp
    (Int.measurable_floor.comp (hg.add_const _)))

/-- If `ρ` gives no mass to `{|g - round g| = 1/2}`, then for `r > 0`,
`ρ{y | r < |Φ_m(g y - round (g y))|} → 0` as `m → ∞`. -/
theorem tendsto_measure_bad {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ]
    {g : X → ℝ} (hg : Measurable g) (hnull : ρ {y | |g y - round (g y)| = 1 / 2} = 0) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun m => ρ {y | r < |cellMap m (g y - round (g y))|}) atTop (𝓝 0) := by
  have hv := measurable_sub_round hg
  have hmeas : ∀ m, MeasurableSet {y | r < |cellMap m (g y - round (g y))|} := fun m =>
    measurableSet_lt measurable_const
      ((contDiff_cellMap m).continuous.measurable.comp hv).abs
  have hsub : ⋂ m, {y | r < |cellMap m (g y - round (g y))|} ⊆
      {y | |g y - round (g y)| = 1 / 2} := by
    intro y hy
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy ⊢
    refine le_antisymm (abs_sub_round _) (not_lt.1 fun hlt => ?_)
    obtain ⟨m, hm⟩ := exists_abs_cellMap_le hlt hr
    exact absurd (hy m) (not_lt.2 hm)
  have h0 : ρ (⋂ m, {y | r < |cellMap m (g y - round (g y))|}) = 0 :=
    measure_mono_null hsub hnull
  rw [← h0]
  refine tendsto_measure_iInter_atTop (fun m => (hmeas m).nullMeasurableSet) ?_
    ⟨0, measure_ne_top _ _⟩
  refine antitone_nat_of_succ_le fun m y hy => ?_
  simp only [Set.mem_ofPred_eq] at hy ⊢
  have hle := (abs_cellMap_le m (abs_sub_round (g y))).1
  have h1 := (abs_cellMap_le 1 (hle.trans (abs_sub_round (g y)))).1
  have he : cellMap (m + 1) (g y - round (g y)) =
      cellMap 1 (cellMap m (g y - round (g y))) := by
    simp only [cellMap]; rw [Function.iterate_succ_apply']; rfl
  rw [he] at hy
  exact hy.trans_le h1


/-- The deterministic output misses `G_r` only if the exact update lands in the band
`{|Φ_m(v)| > r}` around the repelling points: `q_1(G_rᶜ) ≤ ρ{y | r < |Φ_m(v(y))|}`, with `ρ` the
law at index `2` of the deterministic sampler with exact scores (`N ≥ 2`, `b_2 ≠ 0`, `h ≠ 0`). -/
theorem detOutput_compl_goodSet_le (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ} (hb : b 2 ≠ 0)
    (i₀ : Fin d) {h : ℝ} (hh : h ≠ 0) (θ r : ℝ) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    algLaw zeroVar (detMean A b (smoothScore μ t A b i₀ h θ m))
        (measurable_detMean hA b (measurable_smoothScore μ t hA b i₀ h θ m)) N 1
        (goodSet i₀ h θ r)ᶜ ≤
      algLaw zeroVar (detMean A b (exactScore μ t))
        (measurable_detMean hA b (measurable_exactScore μ t)) N 2
        {y | r < |cellMap m ((detMean A b (exactScore μ t) 2 y i₀ - θ) / h -
          round ((detMean A b (exactScore μ t) 2 y i₀ - θ) / h))|} := by
  set z := detMean A b (exactScore μ t) 2
  have hz : Measurable fun y => (z y i₀ - θ) / h :=
    (((measurable_pi_apply i₀).comp (measurable_detMean hA b (measurable_exactScore μ t) 2)).sub
      measurable_const).div_const h
  have hmeas : MeasurableSet {y | r < |cellMap m ((z y i₀ - θ) / h -
      round ((z y i₀ - θ) / h))|} :=
    measurableSet_lt measurable_const
      ((contDiff_cellMap m).continuous.measurable.comp (measurable_sub_round hz)).abs
  have hcongr : ∀ k, 2 < k → detMean A b (smoothScore μ t A b i₀ h θ m) k =
      detMean A b (exactScore μ t) k := by
    intro k hk
    funext y i
    simp [detMean, smoothScore, show k ≠ 2 by omega]
  rw [algLaw_of_lt _ _ _ (by omega : 1 < N), Measure.bind_apply
    (measurableSet_goodSet i₀ h θ r).compl (Kernel.aemeasurable _),
    algLaw_two_congr zeroVar _ (measurable_detMean hA b (measurable_exactScore μ t)) hN hcongr,
    ← lintegral_indicator_one hmeas]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ {y | r < |cellMap m ((z y i₀ - θ) / h - round ((z y i₀ - θ) / h))|}
  · rw [Set.indicator_of_mem hy]
    exact prob_le_one
  · rw [Set.indicator_of_notMem hy]
    simp only [Set.mem_ofPred_eq, not_lt] at hy
    refine le_of_eq ?_
    simp only [algKernel, gaussKernelPi_apply, zeroVar, gaussianReal_zero_var]
    have hsub : (goodSet i₀ h θ r)ᶜ ⊆ Function.eval i₀ ⁻¹'
        {x0 | ¬ ∃ n : ℤ, |(x0 - θ) / h - n| ≤ r} := fun x hx => hx
    refine measure_mono_null hsub (Measure.pi_eval_preimage_null _ ?_)
    rw [Measure.dirac_apply, Set.indicator_of_notMem]
    simp only [Set.mem_ofPred_eq, not_not]
    refine ⟨round ((z y i₀ - θ) / h), ?_⟩
    rw [show (1 + 1 : ℕ) = 2 from rfl, detMean_smoothScore_apply μ t A hb i₀ h θ m y]
    have he : (cellCoord h θ m (z y i₀) - θ) / h = cellMap m ((z y i₀ - θ) / h) := by
      unfold cellCoord; field_simp; ring
    rw [he, cellMap_eq_round]
    simpa using hy


/-- **The deterministic sampler is TV-far.** Data `μ` (probability law), `t_0 < t_1`, `N ≥ 2`,
measurable `A`, `b_2 ≠ 0`, `h ≠ 0`, `η > 0`: there are an offset `θ` and an iteration count `m`
such that the deterministic sampler `algLaw 0 (detMean A b s)` driven by
`s = smoothScore μ t A b i₀ h θ m` satisfies `TV(p_1, q_1) ≥ 1 - η`. -/
theorem exists_tvSup_detOutput_smoothScore_ge (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] {t : ℕ → ℝ} (ht : t 0 < t 1) {A : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ} (hb : b 2 ≠ 0) (i₀ : Fin d) {h : ℝ} (hh : h ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : 0 < η) :
    ∃ (θ : ℝ) (m : ℕ), 1 - η ≤ TotalVariation.tvSup (fwdLaw μ t 1)
      (algLaw zeroVar (detMean A b (smoothScore μ t A b i₀ h θ m))
        (measurable_detMean hA b (measurable_smoothScore μ t hA b i₀ h θ m)) N 1) := by
  set z := detMean A b (exactScore μ t) 2
  have hzm : Measurable fun y => z y i₀ :=
    (measurable_pi_apply i₀).comp (measurable_detMean hA b (measurable_exactScore μ t) 2)
  set ρ := algLaw zeroVar (detMean A b (exactScore μ t))
    (measurable_detMean hA b (measurable_exactScore μ t)) N 2
  obtain ⟨θ, hθ⟩ := exists_shift_atom_free (ρ.map fun y => z y i₀) h
  have hp : fwdLaw μ t 1 ≪ volume := by
    rw [fwdLaw_eq_withDensity μ (k := 0) ht]
    exact withDensity_absolutelyContinuous _ _
  have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨j, hj⟩ :=
    ((tendsto_measure_goodSet _ hp i₀ hh θ).eventually (gt_mem_nhds hη2)).exists
  set r : ℝ := 1 / ((j : ℝ) + 1)
  have hr : 0 < r := by positivity
  set g := fun y => (z y i₀ - θ) / h
  have hg : Measurable g := (hzm.sub measurable_const).div_const h
  have hnull : ρ {y | |g y - round (g y)| = 1 / 2} = 0 := by
    have hsub : {y | |g y - round (g y)| = 1 / 2} ⊆
        (fun y => z y i₀) ⁻¹' ⋃ n : ℤ, {θ + h / 2 + h * n} := by
      intro y hy
      simp only [Set.mem_ofPred_eq] at hy
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 hy with h1 | h1
      · refine ⟨round (g y), ?_⟩
        have e : z y i₀ - θ = (round (g y) + 1 / 2) * h :=
          (div_eq_iff hh).1 (show g y = round (g y) + 1 / 2 by linarith)
        linear_combination e
      · refine ⟨round (g y) - 1, ?_⟩
        have e : z y i₀ - θ = (round (g y) - 1 / 2) * h :=
          (div_eq_iff hh).1 (show g y = round (g y) - 1 / 2 by linarith)
        push_cast
        linear_combination e
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply hzm (MeasurableSet.iUnion fun n => measurableSet_singleton _)]
    exact measure_iUnion_null hθ
  obtain ⟨m, hm⟩ := ((tendsto_measure_bad ρ hg hnull hr).eventually (gt_mem_nhds hη2)).exists
  refine ⟨θ, m, ?_⟩
  set q := algLaw zeroVar (detMean A b (smoothScore μ t A b i₀ h θ m))
    (measurable_detMean hA b (measurable_smoothScore μ t hA b i₀ h θ m)) N 1
  have hG := measurableSet_goodSet i₀ h θ r
  have hq : q (goodSet i₀ h θ r)ᶜ ≤ ENNReal.ofReal (η / 2) :=
    ((detOutput_compl_goodSet_le μ t hA hb i₀ hh θ r m hN).trans_lt hm).le
  have h1 : (fwdLaw μ t 1).real (goodSet i₀ h θ r) ≤ η / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hj.le
  have h2 : q.real (goodSet i₀ h θ r)ᶜ ≤ η / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hq
  rw [probReal_compl_eq_one_sub hG] at h2
  have hTV := TotalVariation.abs_measureReal_sub_le_tvSup (μ := fwdLaw μ t 1) (ν := q) hG
  have := neg_abs_le ((fwdLaw μ t 1).real (goodSet i₀ h θ r) - q.real (goodSet i₀ h θ r))
  linarith


/-! ### DDPM with the same score -/

/-- **Uniform accuracy.** For `h > 0` and `|b_2⁻¹| h / 2 ≤ ε`:
`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y`. -/
theorem sum_sq_smoothScore_sub_le (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (i₀ : Fin d) {h : ℝ} (hh : 0 < h) (θ : ℝ)
    (m : ℕ) {ε : ℝ} (hε : |(b 2)⁻¹| * h / 2 ≤ ε) (k : ℕ) (y : Fin d → ℝ) :
    ∑ i, (smoothScore μ t A b i₀ h θ m k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ ε ^ 2 := by
  simp_rw [smoothScore_sub]
  split_ifs
  · exact sum_sq_smoothErr_le i₀ hh θ m hε _
  · simpa using sq_nonneg ε

/-- At every `k ≠ 2` the smooth score is exact. -/
theorem sum_sq_smoothScore_sub_of_ne (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (i₀ : Fin d) (h θ : ℝ) (m : ℕ) {k : ℕ}
    (hk : k ≠ 2) (y : Fin d → ℝ) :
    ∑ i, (smoothScore μ t A b i₀ h θ m k y i - score (fwdDensity μ t k) y i) ^ 2 = 0 := by
  simp [smoothScore_sub, hk]

/-- The score-error integrand is integrable under every probability law (bounded by `ε²`). -/
theorem integrable_sq_smoothScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) (i₀ : Fin d)
    {h : ℝ} (hh : 0 < h) (θ : ℝ) (m : ℕ) {ε : ℝ} (hε : |(b 2)⁻¹| * h / 2 ≤ ε) (k : ℕ)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    Integrable (fun y =>
      ∑ i, (smoothScore μ t A b i₀ h θ m k y i - score (fwdDensity μ t k) y i) ^ 2) ν := by
  have hmeas : Measurable fun y =>
      ∑ i, (smoothScore μ t A b i₀ h θ m k y i - score (fwdDensity μ t k) y i) ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp (measurable_smoothScore μ t hA b i₀ h θ m k)).sub
        ((measurable_pi_apply i).comp (measurable_exactScore μ t k))).pow_const 2
  refine Integrable.of_bound hmeas.aestronglyMeasurable (ε ^ 2)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (sum_nonneg fun i _ => sq_nonneg _)]
  exact sum_sq_smoothScore_sub_le μ t A b i₀ hh θ m hε k y

/-- **`L²(p_k)` accuracy**: `∫ ∑ᵢ (s_k - ∂ᵢ log p_k)² dp_k ≤ ε²`. -/
theorem integral_sq_smoothScore_sub_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ → ℝ) (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (i₀ : Fin d) {h : ℝ}
    (hh : 0 < h) (θ : ℝ) (m : ℕ) {ε : ℝ} (hε : |(b 2)⁻¹| * h / 2 ≤ ε) (k : ℕ) :
    ∫ y, ∑ i, (smoothScore μ t A b i₀ h θ m k y i - score (fwdDensity μ t k) y i) ^ 2
      ∂(fwdLaw μ t k) ≤ ε ^ 2 := by
  calc _ ≤ ∫ _y, ε ^ 2 ∂(fwdLaw μ t k) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
          sum_nonneg fun i _ => sq_nonneg _) (integrable_const _)
          (Filter.Eventually.of_forall fun y =>
            sum_sq_smoothScore_sub_le μ t A b i₀ hh θ m hε k y)
    _ = ε ^ 2 := by simp

/-- The DDPM score term is `≤ (β_2/2) ε²` (only step `2` contributes; `t_1 ≤ t_2`, `N ≥ 2`). -/
theorem scoreErr_smoothScore_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (ht : t 1 ≤ t 2) (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (i₀ : Fin d)
    {h : ℝ} (hh : 0 < h) (θ : ℝ) (m : ℕ) {ε : ℝ} (hε : |(b 2)⁻¹| * h / 2 ≤ ε) {N : ℕ}
    (hN : 2 ≤ N) :
    scoreErr μ t (smoothScore μ t A b i₀ h θ m) N ≤ fwdVar t 2 / 2 * ε ^ 2 := by
  unfold scoreErr scoreErrW
  rw [sum_eq_single_of_mem 2 (by simp; omega) fun k _ hk => by
    simp [sum_sq_smoothScore_sub_of_ne μ t A b i₀ h θ m hk]]
  have hβ : 0 ≤ fwdVar t 2 := by
    have h1 : fwdScale t 2 ≤ 1 := by
      unfold fwdScale; exact Real.exp_le_one_iff.2 (by norm_num; linarith)
    have h0 : 0 < fwdScale t 2 := Real.exp_pos _
    unfold fwdVar; nlinarith
  exact mul_le_mul_of_nonneg_left (integral_sq_smoothScore_sub_le μ t A b i₀ hh θ m hε 2)
    (by positivity)

/-- **DDPM with the same score.** Under the hypotheses of `tvSup_output_le_ddpm_grid` and
`N ≥ 2`, `h > 0`, `|b_2⁻¹| h/2 ≤ ε`: DDPM driven by the smooth score has
`TV(p_1, q_1^DDPM) ≤ √((I + (κ d / 2)(1 + log(u_N/u_1)) + (β_2/2) ε²) / 2)`. -/
theorem tvSup_ddpm_smoothScore_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 2 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) (i₀ : Fin d)
    {h : ℝ} (hh : 0 < h) (θ : ℝ) (m : ℕ) {ε : ℝ} (hε : |(b 2)⁻¹| * h / 2 ≤ ε) :
    TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw (ddpmVar t) (scoreMean t (smoothScore μ t A b i₀ h θ m))
          (measurable_scoreMean t (measurable_smoothScore μ t hA b i₀ h θ m)) N 1) ≤
      Real.sqrt ((initBound μ t N + κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) +
        fwdVar t 2 / 2 * ε ^ 2) / 2) := by
  refine (tvSup_output_le_ddpm_grid μ hμ h0 ht hκ (by omega) hgrid _
    (measurable_smoothScore μ t hA b i₀ h θ m)
    (fun k _ => integrable_sq_smoothScore_sub μ t hA b i₀ hh θ m hε k _)).trans ?_
  gcongr
  exact scoreErr_smoothScore_le μ (ht.monotone (by norm_num)) A b i₀ hh θ m hε hN

/-! ### The separation -/

/-- Arithmetic: with `h = 2 |b_2| ε`, `|b_2⁻¹| h / 2 = ε`. -/
theorem abs_inv_mul_step (b2 : ℝ) (hb : b2 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    |b2⁻¹| * (2 * |b2| * ε) / 2 = ε := by
  rw [abs_inv]
  have : |b2| ≠ 0 := abs_ne_zero.2 hb
  field_simp

/-- **Smooth separation theorem (DDPM vs deterministic sampler, same smooth learned score).**
Let `μ` be a probability law on `Fin d → ℝ`, `d ≥ 1`, with finite second moment; `t 0 = 0`, `t`
strictly increasing, `N ≥ 2`, grid ratio `κ ≥ 0`; `m_k(y) = A_k(y) + b_k s_k(y)` any deterministic
score-affine update with measurable `A` and `b_2 ≠ 0`. For every `ε > 0` and `η > 0` there are a
measurable learned score `s` and an analytic (`ContDiff ℝ ⊤`) field `E` with
1. `∑ᵢ E(z)ᵢ² ≤ ε²` for all `z`;
2. `s_k = ∇ log p_k` for `k ≠ 2` and `s_2(y) = ∇ log p_2(y) + E(z(y))`, `z(y)` the exact update
   (so the score error is a smooth function of the exact update);
3. uniform accuracy `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y`;
4. the deterministic sampler has `TV(p_1, q_1) ≥ 1 - η`;
5. DDPM with the same `s` has `TV(p_1, q_1) ≤ √((I + (κ d/2)(1 + log(u_N/u_1)) + (β_2/2) ε²)/2)`.
The Lipschitz constant of `E` is not controlled (see `le_of_lipschitzWith_errProfile`). -/
theorem ddpm_ddim_smooth_separation (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (hd : 0 < d) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 2 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ}
    (hb : b 2 ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
      (E : (Fin d → ℝ) → Fin d → ℝ),
      ContDiff ℝ ⊤ E ∧ (∀ z, ∑ i, E z i ^ 2 ≤ ε ^ 2) ∧
      (∀ k, k ≠ 2 → ∀ y, s k y = score (fwdDensity μ t k) y) ∧
      (∀ y, s 2 y = score (fwdDensity μ t 2) y + E (detMean A b (exactScore μ t) 2 y)) ∧
      (∀ k y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ ε ^ 2) ∧
      1 - η ≤ TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw zeroVar (detMean A b s) (measurable_detMean hA b hs) N 1) ∧
      TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
        Real.sqrt ((initBound μ t N +
          κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) +
          fwdVar t 2 / 2 * ε ^ 2) / 2) := by
  set i₀ : Fin d := ⟨0, hd⟩
  set h := 2 * |b 2| * ε
  have hh : 0 < h := by have := abs_pos.2 hb; positivity
  have hεh : |(b 2)⁻¹| * h / 2 ≤ ε := (abs_inv_mul_step (b 2) hb hε).le
  obtain ⟨θ, m, hTV⟩ := exists_tvSup_detOutput_smoothScore_ge μ (ht zero_lt_one) hA hb i₀
    hh.ne' hN hη
  refine ⟨smoothScore μ t A b i₀ h θ m, measurable_smoothScore μ t hA b i₀ h θ m,
    smoothErr i₀ (b 2)⁻¹ h θ m, contDiff_smoothErr i₀ _ h θ m,
    sum_sq_smoothErr_le i₀ hh θ m hεh, fun k hk y => ?_, fun y => ?_,
    sum_sq_smoothScore_sub_le μ t A b i₀ hh θ m hεh, hTV,
    tvSup_ddpm_smoothScore_le μ hμ h0 ht hκ hN hgrid hA b i₀ hh θ m hεh⟩
  · funext i; simp [smoothScore, exactScore, hk]
  · funext i; simp [smoothScore, exactScore]


/-- **Example: probability-flow ODE (exponential integrator `pfMean`) on the geometric grid.**
Data with finite second moment, `d ≥ 1`, `u_1 > 0`, `r > 1`, `N ≥ 2`, `ε, η > 0`: the conclusions
of `ddpm_ddim_smooth_separation` hold with `A_k = α_k⁻¹ id`, `b_k = α_k⁻¹ - 1` and the DDPM bound
`√((I + (r - 1) d/2 (1 + (N - 1) log r) + (β_2/2) ε²)/2)`. -/
theorem pf_ddpm_smooth_separation_geomGrid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (hd : 0 < d) {u1 r : ℝ} (hu1 : 0 < u1)
    (hr : 1 < r) {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
      (E : (Fin d → ℝ) → Fin d → ℝ),
      ContDiff ℝ ⊤ E ∧ (∀ z, ∑ i, E z i ^ 2 ≤ ε ^ 2) ∧
      (∀ k, k ≠ 2 → ∀ y, s k y = score (fwdDensity μ (geomGrid u1 r) k) y) ∧
      (∀ y, s 2 y = score (fwdDensity μ (geomGrid u1 r) 2) y +
        E (pfMean (geomGrid u1 r) (exactScore μ (geomGrid u1 r)) 2 y)) ∧
      (∀ k y, ∑ i, (s k y i - score (fwdDensity μ (geomGrid u1 r) k) y i) ^ 2 ≤ ε ^ 2) ∧
      1 - η ≤ TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw zeroVar (pfMean (geomGrid u1 r) s)
          (measurable_detMean (measurable_pfLin _) _ hs) N 1) ∧
      TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r)) (scoreMean (geomGrid u1 r) s)
          (measurable_scoreMean _ hs) N 1) ≤
        Real.sqrt ((initBound μ (geomGrid u1 r) N +
          (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
          fwdVar (geomGrid u1 r) 2 / 2 * ε ^ 2) / 2) := by
  have h := ddpm_ddim_smooth_separation μ hμ hd (geomGrid_zero u1 r)
    (geomGrid_strictMono hu1 hr) (by linarith : 0 ≤ r - 1) hN
    (fun k hk _ => geomGrid_grid hu1 (zero_lt_one.trans hr) hk)
    (A := pfLin (geomGrid u1 r)) (b := pfCoeff (geomGrid u1 r)) (measurable_pfLin _)
    (pfCoeff_two_ne_zero (geomGrid_strictMono hu1 hr one_lt_two)) hε hη
  rw [log_heatTime_geomGrid hu1 (zero_lt_one.trans hr) (by omega : 1 ≤ N)] at h
  exact h

end FormalizeSampling.DiffusionODESmooth
