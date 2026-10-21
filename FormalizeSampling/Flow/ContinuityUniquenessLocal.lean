module

public import FormalizeSampling.Flow.ContinuityUniquenessMollified

/-!
# Uniqueness for the weak continuity equation with locally Lipschitz velocity fields

Status: **Verified.** Discharges the named PDE-uniqueness input
`NoiseScore.UniqueWeakContinuity v` of FL-5 (`Flow/NoiseScoreEquivalence.lean`) for velocities
`v : ℝ → ℝᵈ → ℝᵈ` with

* `(t, x) ↦ v_t(x)` jointly continuous on `[0, ∞) × ℝᵈ`,
* on every `[0, T]`, linear growth `‖v_t(x)‖ ≤ M (1 + ‖x‖)`,
* on every `[0, T]` and every ball `‖x‖, ‖y‖ ≤ R`, a Lipschitz bound
  `‖v_t(x) - v_t(y)‖ ≤ L_R ‖x - y‖` (the constant may grow arbitrarily with `R`).

No differentiability in `x` or `t` is required; globally Lipschitz velocities
(`uniqueWeakContinuity_of_lipschitz_continuous`) and `C³` velocities with bounded derivative
(`uniqueWeakContinuity_of_lipschitz`) are corollaries. Typical example: the probability-flow
velocity `b_t - D ∇log p_t` for a smooth positive density `p_t` whose score grows at most linearly
(e.g. Gaussian mixtures, or densities `∝ e^{-U}` with `∇U` of linear growth and smooth `U`),
whose Hessian of `log p_t` is in general unbounded but always bounded on compact sets; see
`uniqueWeakContinuity_of_contDiff_linearGrowth` and
`map_flow_eq_of_weakFokkerPlanck_of_locallyLipschitz`.

## Method

Approximate duality with backward Euler test functions (`Flow/ContinuityUniquenessLipschitz.lean`)
for a smooth approximating Euler velocity (`Flow/ContinuityUniquenessMollified.lean`), with the
**growth constant `A` and the Lipschitz constant `L` separated**:

1. `abs_integral_sub_integral_eulerBack_le_of_localApprox`: the backward Euler estimate for an
   approximating Euler velocity `w`, where `A` controls `‖v_t(x)‖, ‖w_t(x)‖ ≤ A (‖x‖ + c)` and
   hence the support radius `(R + c) e^{2AT}` of all Euler test functions (via the existing
   `eulerBack_eq_zero`, which only uses the growth constant), while `L` bounds `‖Dw_t‖` and
   enters only the gradient bound `e^{LT} G` (`norm_fderiv_eulerBack_le`). The closeness
   `‖v_s - w_t‖ ≤ ε` is needed only on the ball of radius `(R + c) e^{2AT}`.
2. `integral_eq_of_weakContinuity2_of_localApprox`: uniqueness on `C³_c` test functions when
   for every radius `r` there is `L` such that for every `η > 0` an approximant `w` exists
   with `‖Dw_t‖ ≤ L`, growth `A`, and `‖w_t - v_t‖ ≤ η` **on the ball of radius `r` only**.
3. `clampBox`: the coordinatewise clamp `x ↦ (max (min x_i R) (-R))_i`, which (in the sup norm
   of `Fin d → ℝ`) is `1`-Lipschitz, maps into the closed ball of radius `R`, is the identity
   on it and does not increase the norm. Then `v_t ∘ clampBox R` is **globally**
   `L_R`-Lipschitz with growth `M (1 + ‖x‖)`, agrees with `v_t` on the ball, and its
   mollification (`exists_contDiff_lipschitz_approx`) provides the approximants of step 2.
   The solution `ρ` is never localized: only the Euler test functions are, and on their
   supports the truncated field coincides with `v`.

## Main results

* `abs_integral_sub_integral_eulerBack_le_of_localApprox`,
  `integral_eq_of_weakContinuity2_of_localApprox`.
* `clampBox` and its properties (`norm_clampBox_le`, `norm_clampBox_le_norm`,
  `clampBox_eq_self`, `norm_clampBox_sub_le`).
* `uniqueWeakContinuity_of_locallyLipschitz`: the main uniqueness theorem.
* `uniqueWeakContinuity_of_contDiff_linearGrowth`: the `C¹` case (spatial derivative jointly
  continuous in `(t, x)`), where the local Lipschitz constants come from compactness.
* Globally Lipschitz velocities: `integral_eq_of_weakContinuity2_of_approx` (global smooth
  approximants), `uniqueWeakContinuity_of_lipschitz_continuous` (jointly continuous, Lipschitz
  in `x` uniformly on every `[0, T]`), `uniqueWeakContinuity_of_autonomous_lipschitzWith`,
  `uniqueWeakContinuity_of_lipschitz` and `uniqueWeakContinuity_of_autonomous_lipschitz`
  (`C³` in `x` with bounded derivative).
* `map_flow_eq_of_weakFokkerPlanck_of_locallyLipschitz`,
  `map_flow_eq_of_weakFokkerPlanck_of_contDiff_linearGrowth`,
  `map_flow_eq_of_weakFokkerPlanck_of_lipschitz_continuous`,
  `map_flow_eq_of_weakFokkerPlanck_of_lipschitz`: FL-5 with the PDE-uniqueness input replaced
  by these sufficient conditions on the probability-flow velocity.

## Not proved here

* No flow map is constructed and solutions are **not** identified with `(X_{0→T})_# ρ_0`;
  only uniqueness among probability-measure solutions is proved. Existence is not addressed.
* Superlinear growth (e.g. `v(x) = -x³`, or scores of densities `∝ e^{-‖x‖⁴}`) is **not**
  covered: the linear-growth bound is what confines the Euler test functions to a fixed ball.
  (For such fields uniqueness can genuinely require moment/integrability assumptions on `ρ`.)
* Velocities discontinuous in `t`, or with merely Sobolev/BV regularity in `x`
  (DiPerna–Lions / Ambrosio); see `Flow/ContinuityUniquenessDiPernaLions.lean` for what is and
  is not available.
* For the probability-flow application, verifying linear growth and local Lipschitz bounds for
  a concrete score `∇log p_t` is left to the user, as is the Itô input `WeakFokkerPlanck`.
  Only one-time marginals are matched.
-/

@[expose] public section

open MeasureTheory Matrix Set Filter Topology Metric
open scoped ContDiff

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-! ### Euler estimate with separate growth and Lipschitz constants -/

/-- **Backward Euler estimate with separate growth and Lipschitz constants (Verified).** Let
`ρ` be a probability solution of `WeakContinuity2 ρ v` on `t ≥ 0`, `T ≥ 0`. Assume on
`[0, T]`: `v_t` continuous, `‖v_t(x)‖ ≤ A (‖x‖ + c)`, and `w_t ∈ C³` with `‖Dw_t‖ ≤ L` and
`‖w_t(x)‖ ≤ A (‖x‖ + c)` (`A, c ≥ 0`). Let `φ ∈ C³` vanish for `‖x‖ > R ≥ 0`, `‖Dφ‖ ≤ G`,
`N h = T`, `h ≥ 0`, `hA ≤ 1/2`, and let `ε ≥ 0` bound `‖v_s(x) - w_t(x)‖` for `s, t ∈ [0, T]`,
`|s - t| ≤ h`, `‖x‖ ≤ (R + c) e^{2AT}`. Then
`|∫ φ dρ_T - ∫ eulerBack w T h φ N dρ_0| ≤ T e^{LT} G (ε + h L A ((R + c) e^{2AT} + c))`.
The support radius depends only on the growth constant `A`, not on `L`. -/
theorem abs_integral_sub_integral_eulerBack_le_of_localApprox {ρ : ℝ → Measure (Fin d → ℝ)}
    {v w : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakContinuity2 ρ v)
    {T : ℝ} (hT : 0 ≤ T) (hw : ∀ t ∈ Icc 0 T, ContDiff ℝ 3 (w t))
    (hvc : ∀ t ∈ Icc 0 T, Continuous (v t))
    {A L c : ℝ} (hA0 : 0 ≤ A) (hc : 0 ≤ c) (hL : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (w t) x‖ ≤ L)
    (hgr : ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ A * (‖x‖ + c))
    (hgrw : ∀ t ∈ Icc 0 T, ∀ x, ‖w t x‖ ≤ A * (‖x‖ + c))
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 3 φ) {R G : ℝ} (hR : 0 ≤ R)
    (hφR : ∀ x, R < ‖x‖ → φ x = 0) (hG : ∀ x, ‖fderiv ℝ φ x‖ ≤ G)
    {N : ℕ} {h ε : ℝ} (hh : 0 ≤ h) (hNh : (N : ℝ) * h = T) (hhA : h * A ≤ 1 / 2)
    (hε0 : 0 ≤ ε)
    (hε : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |s - t| ≤ h → ∀ x : Fin d → ℝ,
      ‖x‖ ≤ (R + c) * Real.exp (2 * A * T) → ‖v s x - w t x‖ ≤ ε) :
    |∫ x, φ x ∂(ρ T) - ∫ x, eulerBack w T h φ N x ∂(ρ 0)| ≤
      T * (Real.exp (L * T) * G *
        (ε + h * (L * (A * ((R + c) * Real.exp (2 * A * T) + c))))) := by
  set ρK := (R + c) * Real.exp (2 * A * T) with hρK
  set B := L * (A * (ρK + c)) with hBdef
  set C := Real.exp (L * T) * G * (ε + h * B) with hCdef
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 ⟨le_rfl, hT⟩ 0)
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hρK0 : 0 ≤ ρK := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hjh : ∀ j : ℕ, j ≤ N → (j : ℝ) * h ≤ T := fun j hj => by
    rw [← hNh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh
  have claim : ∀ j : ℕ, j ≤ N →
      |∫ x, φ x ∂(ρ T) - ∫ x, eulerBack w T h φ j x ∂(ρ (T - j * h))| ≤ j * (C * h) := by
    intro j
    induction j with
    | zero => intro _; simp [eulerBack]
    | succ j ih =>
      intro hj
      have hj' : j ≤ N := by omega
      have hj1 := hjh (j + 1) hj
      push_cast at hj1
      set t := T - j * h with ht
      have htmem : t ∈ Icc 0 T := sub_mul_mem_Icc hh hNh hj'
      have hht : h ≤ t := by rw [ht]; linarith
      have hsub : Icc (t - h) t ⊆ Icc 0 T := fun s hs => ⟨by linarith [hs.1], hs.2.trans htmem.2⟩
      have hsupp : tsupport (eulerBack w T h φ j) ⊆
          {z | (‖z‖ + c) * (1 - h * A) ^ j ≤ R + c} := by
        refine closure_minimal (fun z hz => ?_) (isClosed_le (by fun_prop) continuous_const)
        by_contra hlt
        exact hz (eulerBack_eq_zero hh hNh hc (by linarith) hgrw hφR j hj' z (not_le.1 hlt))
      have hΨK : ∀ s ∈ Icc (t - h) t, ∀ x ∉ closedBall (0 : Fin d → ℝ) ρK,
          x + (t - s) • w t x ∉ tsupport (eulerBack w T h φ j) := by
        intro s hs x hx hy
        rw [mem_closedBall, dist_zero_right, not_le] at hx
        have hy' := hsupp hy
        simp only [Set.mem_ofPred_eq] at hy'
        have hτ : 0 ≤ t - s := by linarith [hs.2]
        have h1 := one_sub_mul_le_norm_add_smul (w := w t) hτ x (hgrw t htmem x)
        have hxc : 0 ≤ ‖x‖ + c := by positivity
        have h2 : (1 - h * A) * (‖x‖ + c) ≤ (1 - (t - s) * A) * (‖x‖ + c) :=
          mul_le_mul_of_nonneg_right (by nlinarith [hs.1]) hxc
        have hq0 : 0 ≤ (1 - h * A) ^ j := pow_nonneg (by linarith) j
        have hq := exp_neg_le_pow_one_sub hh hA0 hhA (j := j + 1) (hjh (j + 1) hj)
        have he : Real.exp (2 * A * T) * Real.exp (-(2 * A * T)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have he0 : 0 < Real.exp (-(2 * A * T)) := Real.exp_pos _
        have h3 : R + c < (‖x‖ + c) * Real.exp (-(2 * A * T)) := by
          have : ρK + 0 < ‖x‖ + c := by linarith
          calc R + c = ρK * Real.exp (-(2 * A * T)) := by rw [hρK, mul_assoc, he, mul_one]
            _ < (‖x‖ + c) * Real.exp (-(2 * A * T)) :=
              mul_lt_mul_of_pos_right (by linarith) he0
        have h4 : (‖x‖ + c) * Real.exp (-(2 * A * T)) ≤ (‖x‖ + c) * (1 - h * A) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left hq hxc
        have h5 : (‖x‖ + c) * (1 - h * A) ^ (j + 1) ≤
            (‖x + (t - s) • w t x‖ + c) * (1 - h * A) ^ j := by
          rw [pow_succ]
          calc (‖x‖ + c) * ((1 - h * A) ^ j * (1 - h * A))
              = (1 - h * A) * (‖x‖ + c) * (1 - h * A) ^ j := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (h2.trans h1) hq0
        linarith
      have hG' : ∀ y, ‖fderiv ℝ (eulerBack w T h φ j) y‖ ≤ Real.exp (L * T) * G := fun y =>
        (norm_fderiv_eulerBack_le hh hNh hw hφ hL hG j hj' y).trans
          (mul_le_mul_of_nonneg_right (pow_one_add_le_exp hh hL0 (hjh j hj')) hG0)
      have hεs : ∀ s ∈ Icc (t - h) t, ∀ x ∈ closedBall (0 : Fin d → ℝ) ρK,
          ‖v s x - w t x‖ ≤ ε := by
        intro s hs x hx
        rw [mem_closedBall, dist_zero_right] at hx
        refine hε s (hsub hs) t htmem ?_ x hx
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.2])]
        linarith [hs.1]
      have hBs : ∀ s ∈ Icc (t - h) t, ∀ x ∈ closedBall (0 : Fin d → ℝ) ρK,
          ‖fderiv ℝ (w t) x (v s x)‖ ≤ B := by
        intro s hs x hx
        rw [mem_closedBall, dist_zero_right] at hx
        calc _ ≤ ‖fderiv ℝ (w t) x‖ * ‖v s x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ L * (A * (‖x‖ + c)) :=
            mul_le_mul (hL t htmem x) (hgr s (hsub hs) x) (norm_nonneg _) hL0
          _ ≤ B := by rw [hBdef]; gcongr
      have step := abs_integral_eulerStep_le_of_approx hprob hρ hh hht (hw t htmem)
        (fun s hs => hvc s (hsub hs)) (contDiff_eulerBack hh hNh hw hφ j hj')
        (isCompact_closedBall 0 ρK) hΨK hG' hε0 hB0 hεs hBs
      have hstep : |∫ x, eulerBack w T h φ j x ∂(ρ t) -
          ∫ x, eulerBack w T h φ (j + 1) x ∂(ρ (T - ↑(j + 1) * h))| ≤ C * h := by
        have e1 : T - ((j + 1 : ℕ) : ℝ) * h = t - h := by rw [ht]; push_cast; ring
        rw [e1]
        exact step
      calc _ ≤ |∫ x, φ x ∂(ρ T) - ∫ x, eulerBack w T h φ j x ∂(ρ t)| +
            |∫ x, eulerBack w T h φ j x ∂(ρ t) -
              ∫ x, eulerBack w T h φ (j + 1) x ∂(ρ (T - ↑(j + 1) * h))| := abs_sub_le _ _ _
        _ ≤ j * (C * h) + C * h := add_le_add (ih hj') hstep
        _ = ↑(j + 1) * (C * h) := by push_cast; ring
  have := claim N le_rfl
  rw [hNh, sub_self] at this
  calc _ ≤ (N : ℝ) * (C * h) := this
    _ = T * C := by rw [← hNh]; ring

/-! ### Uniqueness from local smooth approximation -/

/-- **Two solutions agree on `C³_c` test functions (locally approximable velocity,
Verified).** Let `ρ, ρ'` be curves of probability measures on `t ≥ 0`, both solving
`WeakContinuity2` with velocity `v`, with `ρ 0 = ρ' 0`, and let `T ≥ 0`. Assume
`(t, x) ↦ v_t(x)` is continuous on `[0, T] × ℝᵈ` and `‖v_t(x)‖ ≤ A (‖x‖ + c)` on `[0, T]`
(`A, c ≥ 0`). Assume moreover that for every radius `r` there is a constant `L` such that for
every `η > 0` some field `w` (no regularity in `t`) satisfies, for `t ∈ [0, T]`: `w_t ∈ C³`,
`‖Dw_t‖ ≤ L`, `‖w_t(x)‖ ≤ A (‖x‖ + c)` for all `x`, and `‖w_t(x) - v_t(x)‖ ≤ η` for
`‖x‖ ≤ r` only. Then `∫ φ dρ_T = ∫ φ dρ'_T` for every `C³` compactly supported `φ`. Proof:
`abs_integral_sub_integral_eulerBack_le_of_localApprox` with `r = (R + c) e^{2AT}`. -/
theorem integral_eq_of_weakContinuity2_of_localApprox {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakContinuity2 ρ v) (hρ' : WeakContinuity2 ρ' v) (h0 : ρ 0 = ρ' 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hvc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2) (Icc 0 T ×ˢ univ))
    {A c : ℝ} (hA0 : 0 ≤ A) (hc : 0 ≤ c) (hgr : ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ A * (‖x‖ + c))
    (happrox : ∀ r : ℝ, ∃ L : ℝ, ∀ η > 0, ∃ w : ℝ → (Fin d → ℝ) → Fin d → ℝ,
      (∀ t ∈ Icc 0 T, ContDiff ℝ 3 (w t)) ∧ (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (w t) x‖ ≤ L) ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖w t x‖ ≤ A * (‖x‖ + c)) ∧
      ∀ t ∈ Icc 0 T, ∀ x, ‖x‖ ≤ r → ‖w t x - v t x‖ ≤ η)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x ∂(ρ T) = ∫ x, φ x ∂(ρ' T) := by
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  set R := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hφR : ∀ x, R < ‖x‖ → φ x = 0 := fun x hx => by
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hR₀ hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R₀ 0]
  obtain ⟨G, hG⟩ := (hφ.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  set ρK := (R + c) * Real.exp (2 * A * T) with hρK
  obtain ⟨L, hLw⟩ := happrox ρK
  have hL0 : 0 ≤ L := by
    obtain ⟨w, -, hwL, -⟩ := hLw 1 one_pos
    exact (norm_nonneg _).trans (hwL 0 ⟨le_rfl, hT⟩ 0)
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hvc' : ∀ t ∈ Icc 0 T, Continuous (v t) := fun t ht =>
    hvc.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, mem_univ x⟩
  set B := L * (A * (ρK + c)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set Kc := 2 * (T * (Real.exp (L * T) * G * 3)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have huc : UniformContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2)
      (Icc 0 T ×ˢ closedBall 0 ρK) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).uniformContinuousOn_of_continuous
      (hvc.mono (prod_mono subset_rfl (subset_univ _)))
  have key : ∀ ε > 0, |∫ x, φ x ∂(ρ T) - ∫ x, φ x ∂(ρ' T)| ≤ Kc * ε := by
    intro ε hε
    obtain ⟨w, hw, hwL, hwgr, hwv⟩ := hLw ε hε
    obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    set δ0 := min η (min (1 / (2 * (A + 1))) (ε / (B + 1))) with hδ0
    have hδ0p : 0 < δ0 := lt_min hη (lt_min (by positivity) (by positivity))
    obtain ⟨N, hN⟩ := exists_nat_gt (T / δ0)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hT hδ0p.le) hN
    set h := T / N with hhdef
    have hh : 0 ≤ h := div_nonneg hT hNpos.le
    have hNh : (N : ℝ) * h = T := by rw [hhdef]; field_simp
    have hhδ : h < δ0 := by
      rw [hhdef, div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hδ0p] at hN
      linarith
    have hhη : h < η := hhδ.trans_le (min_le_left _ _)
    have hhA : h * A ≤ 1 / 2 := by
      have h1 : h ≤ 1 / (2 * (A + 1)) :=
        hhδ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      calc h * A ≤ 1 / (2 * (A + 1)) * A := mul_le_mul_of_nonneg_right h1 hA0
        _ ≤ 1 / 2 := by rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
                        nlinarith
    have hhB : h * B ≤ ε := by
      have h1 : h ≤ ε / (B + 1) := hhδ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      calc h * B ≤ ε / (B + 1) * B := mul_le_mul_of_nonneg_right h1 hB0
        _ ≤ ε := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    have hεv : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |s - t| ≤ h → ∀ x : Fin d → ℝ,
        ‖x‖ ≤ ρK → ‖v s x - w t x‖ ≤ 2 * ε := by
      intro s hs t ht hst x hx
      have hxm : x ∈ closedBall (0 : Fin d → ℝ) ρK := by
        rwa [mem_closedBall, dist_zero_right]
      have h1 := hηu (s, x) ⟨hs, hxm⟩ (t, x) ⟨ht, hxm⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
        exact hst.trans_lt hhη)
      rw [dist_eq_norm] at h1
      have h2 := hwv t ht x hx
      rw [norm_sub_rev] at h2
      calc ‖v s x - w t x‖ = ‖(v s x - v t x) + (v t x - w t x)‖ := by abel_nf
        _ ≤ ‖v s x - v t x‖ + ‖v t x - w t x‖ := norm_add_le _ _
        _ ≤ 2 * ε := by linarith
    have e1 := abs_integral_sub_integral_eulerBack_le_of_localApprox hprob hρ hT hw hvc' hA0 hc
      hwL hgr hwgr hφ hR hφR hG hh hNh hhA (by positivity) hεv
    have e2 := abs_integral_sub_integral_eulerBack_le_of_localApprox hprob' hρ' hT hw hvc' hA0
      hc hwL hgr hwgr hφ hR hφR hG hh hNh hhA (by positivity) hεv
    rw [← h0] at e2
    have hE : T * (Real.exp (L * T) * G * (2 * ε + h * B)) ≤
        T * (Real.exp (L * T) * G * 3) * ε := by
      have : Real.exp (L * T) * G * (2 * ε + h * B) ≤ Real.exp (L * T) * G * (3 * ε) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    calc _ ≤ |∫ x, φ x ∂(ρ T) - ∫ x, eulerBack w T h φ N x ∂(ρ 0)| +
          |∫ x, φ x ∂(ρ' T) - ∫ x, eulerBack w T h φ N x ∂(ρ 0)| := by
          rw [abs_sub_comm (∫ x, φ x ∂(ρ' T))]
          exact abs_sub_le _ _ _
      _ ≤ Kc * ε := by rw [hKc]; linarith
  have hlim : |∫ x, φ x ∂(ρ T) - ∫ x, φ x ∂(ρ' T)| ≤ 0 := by
    refine le_of_forall_pos_le_add fun e he => ?_
    have h1 := key (e / (Kc + 1)) (by positivity)
    have h2 : Kc * (e / (Kc + 1)) ≤ e := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hlim)

/-! ### Truncation by a coordinatewise clamp -/

/-- The **coordinatewise clamp** of `x : ℝᵈ` to the box `[-R, R]ᵈ`, which is the closed ball
of radius `R` for the sup norm of `Fin d → ℝ`: `(clampBox R x)_i = max (min x_i R) (-R)`. -/
def clampBox (R : ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => max (min (x i) R) (-R)

/-- The clamp lands in the closed ball of radius `R ≥ 0`. -/
theorem norm_clampBox_le {R : ℝ} (hR : 0 ≤ R) (x : Fin d → ℝ) : ‖clampBox R x‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  simp only [clampBox]
  constructor
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (by linarith)

/-- The clamp does not increase the norm (`R ≥ 0`). -/
theorem norm_clampBox_le_norm {R : ℝ} (hR : 0 ≤ R) (x : Fin d → ℝ) :
    ‖clampBox R x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
  have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  rw [Real.norm_eq_abs, abs_le] at *
  simp only [clampBox]
  constructor
  · exact le_max_of_le_left (le_min hi.1 (by linarith))
  · exact max_le ((min_le_left _ _).trans hi.2) (by linarith)

/-- The clamp is the identity on the closed ball of radius `R`. -/
theorem clampBox_eq_self {R : ℝ} {x : Fin d → ℝ} (hx : ‖x‖ ≤ R) : clampBox R x = x := by
  funext i
  have hi : |x i| ≤ R := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hx
  rw [abs_le] at hi
  simp only [clampBox]
  rw [min_eq_left hi.2, max_eq_left hi.1]

/-- The clamp is `1`-Lipschitz for the sup norm. -/
theorem norm_clampBox_sub_le (R : ℝ) (x y : Fin d → ℝ) :
    ‖clampBox R x - clampBox R y‖ ≤ ‖x - y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have hi : ‖x i - y i‖ ≤ ‖x - y‖ := by simpa using norm_le_pi_norm (x - y) i
  refine le_trans ?_ hi
  simp only [Pi.sub_apply, clampBox, Real.norm_eq_abs]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-! ### Main theorem -/

/-- **`UniqueWeakContinuity` for locally Lipschitz velocities with linear growth
(Verified).** Let `v : ℝ → ℝᵈ → ℝᵈ` with `(t, x) ↦ v_t(x)` continuous on `[0, ∞) × ℝᵈ` and,
for every `T ≥ 0`:

* a constant `M` with `‖v_t(x)‖ ≤ M (1 + ‖x‖)` for `t ∈ [0, T]`, `x ∈ ℝᵈ`;
* for every `R`, a constant `L` with `‖v_t(x) - v_t(y)‖ ≤ L ‖x - y‖` for `t ∈ [0, T]` and
  `‖x‖, ‖y‖ ≤ R`.

No differentiability of `v` is assumed. Then uniqueness holds for `WeakContinuity2`
(probability measures on `t ≥ 0`): two solutions with the same time-`0` law agree at every
`t ≥ 0`. Proof: `integral_eq_of_weakContinuity2_of_localApprox`, the approximants being
mollifications (`exists_contDiff_lipschitz_approx`) of the globally Lipschitz truncations
`v_t ∘ clampBox r`, which agree with `v_t` on the ball of radius `r`. -/
theorem uniqueWeakContinuity_of_locallyLipschitz {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hvc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2) (Ici 0 ×ˢ univ))
    (hgrowth : ∀ T, 0 ≤ T → ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ M * (1 + ‖x‖))
    (hloc : ∀ T, 0 ≤ T → ∀ R : ℝ, ∃ L : ℝ, ∀ t ∈ Icc 0 T, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖v t x - v t y‖ ≤ L * ‖x - y‖) :
    UniqueWeakContinuity v := by
  intro ρ ρ' hp hp' hc hc' h0 T hT
  obtain ⟨M₀, hM₀⟩ := hgrowth T hT
  set A := max M₀ 0 + 1 with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hgr : ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ A * (‖x‖ + 1) := by
    intro t ht x
    have h1 := hM₀ t ht x
    have h2 : M₀ * (1 + ‖x‖) ≤ max M₀ 0 * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith [norm_nonneg x, le_max_right M₀ 0]
  have happrox : ∀ r : ℝ, ∃ L : ℝ, ∀ η > 0, ∃ w : ℝ → (Fin d → ℝ) → Fin d → ℝ,
      (∀ t ∈ Icc 0 T, ContDiff ℝ 3 (w t)) ∧ (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (w t) x‖ ≤ L) ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖w t x‖ ≤ A * (‖x‖ + 1)) ∧
      ∀ t ∈ Icc 0 T, ∀ x, ‖x‖ ≤ r → ‖w t x - v t x‖ ≤ η := by
    intro r
    set r' := max r 0 with hr'
    have hr'0 : 0 ≤ r' := le_max_right _ _
    obtain ⟨L₀, hL₀⟩ := hloc T hT r'
    set L := max L₀ 0 with hLdef
    have hL0 : 0 ≤ L := le_max_right _ _
    refine ⟨L, fun η hη => ?_⟩
    set η' := min η 1 with hη'
    have hη'0 : 0 < η' := lt_min hη one_pos
    have hrad : 0 < η' / (L + 1) := by positivity
    have hLr : L * (η' / (L + 1)) ≤ η' := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    have hlipc : ∀ t ∈ Icc 0 T, ∀ x y,
        ‖v t (clampBox r' x) - v t (clampBox r' y)‖ ≤ L * ‖x - y‖ := by
      intro t ht x y
      refine (hL₀ t ht _ _ (norm_clampBox_le hr'0 x) (norm_clampBox_le hr'0 y)).trans ?_
      calc L₀ * ‖clampBox r' x - clampBox r' y‖ ≤ L * ‖clampBox r' x - clampBox r' y‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_left (norm_clampBox_sub_le _ _ _) hL0
    have hex : ∀ t, ∃ g : (Fin d → ℝ) → Fin d → ℝ, t ∈ Icc 0 T →
        ContDiff ℝ ∞ g ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L) ∧
          ∀ x, ‖g x - v t (clampBox r' x)‖ ≤ L * (η' / (L + 1)) := by
      intro t
      by_cases ht : t ∈ Icc 0 T
      · obtain ⟨g, hg⟩ := exists_contDiff_lipschitz_approx (f := fun x => v t (clampBox r' x))
          hL0 (hlipc t ht) hrad
        exact ⟨g, fun _ => hg⟩
      · exact ⟨0, fun h => absurd h ht⟩
    choose w hw using hex
    refine ⟨w, fun t ht => (hw t ht).1.of_le (by simp), fun t ht x => (hw t ht).2.1 x,
      fun t ht x => ?_, fun t ht x hx => ?_⟩
    · have h1 : ‖w t x‖ ≤ ‖w t x - v t (clampBox r' x)‖ + ‖v t (clampBox r' x)‖ :=
        norm_le_norm_sub_add _ _
      have h2 : ‖w t x - v t (clampBox r' x)‖ ≤ 1 :=
        ((hw t ht).2.2 x).trans (hLr.trans (min_le_right _ _))
      have h3 := hM₀ t ht (clampBox r' x)
      have h4 := norm_clampBox_le_norm hr'0 x
      have h5 : M₀ * (1 + ‖clampBox r' x‖) ≤ max M₀ 0 * (1 + ‖x‖) :=
        mul_le_mul (le_max_left _ _) (by linarith) (by positivity) (le_max_right _ _)
      nlinarith [norm_nonneg x, le_max_right M₀ 0]
    · have hxr : ‖x‖ ≤ r' := hx.trans (le_max_left _ _)
      have := (hw t ht).2.2 x
      rw [clampBox_eq_self hxr] at this
      exact this.trans (hLr.trans (min_le_left _ _))
  have := hp T hT
  have := hp' T hT
  refine ext_of_forall_integral_smooth_eq fun φ hφ hφc => ?_
  exact integral_eq_of_weakContinuity2_of_localApprox hp hp' hc hc' h0 hT
    (hvc.mono (prod_mono Icc_subset_Ici_self subset_rfl)) hA0 zero_le_one hgr happrox
    (hφ.of_le (by simp)) hφc

/-- **`UniqueWeakContinuity` for `C¹` velocities with linear growth (Verified).** Let
`v : ℝ → ℝᵈ → ℝᵈ` with `v_t` differentiable for every `t ≥ 0`, both `(t, x) ↦ v_t(x)` and
`(t, x) ↦ Dv_t(x)` continuous on `[0, ∞) × ℝᵈ`, and for every `T ≥ 0` a constant `M` with
`‖v_t(x)‖ ≤ M (1 + ‖x‖)` on `[0, T]`. The derivative may be unbounded in `x`. Then uniqueness
holds for `WeakContinuity2`. Proof: the derivative is bounded on the compact sets
`[0, T] × closedBall 0 R`, so `v_t` is Lipschitz on each ball (mean value inequality), and
`uniqueWeakContinuity_of_locallyLipschitz` applies. -/
theorem uniqueWeakContinuity_of_contDiff_linearGrowth {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hvd : ∀ t, 0 ≤ t → Differentiable ℝ (v t))
    (hvc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2) (Ici 0 ×ˢ univ))
    (hdc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => fderiv ℝ (v q.1) q.2) (Ici 0 ×ˢ univ))
    (hgrowth : ∀ T, 0 ≤ T → ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ M * (1 + ‖x‖)) :
    UniqueWeakContinuity v := by
  refine uniqueWeakContinuity_of_locallyLipschitz hvc hgrowth fun T hT R => ?_
  have hK : IsCompact (Icc 0 T ×ˢ closedBall (0 : Fin d → ℝ) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn
    (hdc.mono (prod_mono Icc_subset_Ici_self (subset_univ _)))
  refine ⟨L, fun t ht x y hx hy => ?_⟩
  have hxm : x ∈ closedBall (0 : Fin d → ℝ) R := by rwa [mem_closedBall, dist_zero_right]
  have hym : y ∈ closedBall (0 : Fin d → ℝ) R := by rwa [mem_closedBall, dist_zero_right]
  exact (convex_closedBall (0 : Fin d → ℝ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hvd t ht.1 z) (fun z hz => hL (t, z) ⟨ht, hz⟩) hym hxm

/-! ### Globally Lipschitz velocities -/

/-- **Two solutions agree on `C³_c` test functions (approximable velocity, Verified).** Let
`ρ, ρ'` be curves of probability measures on `t ≥ 0`, both solving `WeakContinuity2` with
velocity `v`, with `ρ 0 = ρ' 0`, and let `T ≥ 0`. Assume `(t, x) ↦ v_t(x)` is continuous on
`[0, T] × ℝᵈ` and `‖v_t(x)‖ ≤ L (‖x‖ + c)` on `[0, T]` (`c ≥ 0`). Assume moreover that for every
`η > 0` there is a field `w` (no regularity in `t`) with, for `t ∈ [0, T]`: `w_t ∈ C³`,
`‖Dw_t‖ ≤ L`, `‖w_t(x)‖ ≤ L (‖x‖ + c)` and `‖w_t(x) - v_t(x)‖ ≤ η` for all `x`. Then
`∫ φ dρ_T = ∫ φ dρ'_T` for every `C³` compactly supported `φ`. No differentiability of `v` is
assumed. The case of `integral_eq_of_weakContinuity2_of_localApprox` where the growth and
Lipschitz constants coincide and the approximation is global. -/
theorem integral_eq_of_weakContinuity2_of_approx {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakContinuity2 ρ v) (hρ' : WeakContinuity2 ρ' v) (h0 : ρ 0 = ρ' 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hvc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2) (Icc 0 T ×ˢ univ))
    {L c : ℝ} (hc : 0 ≤ c) (hgr : ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ L * (‖x‖ + c))
    (happrox : ∀ η > 0, ∃ w : ℝ → (Fin d → ℝ) → Fin d → ℝ,
      (∀ t ∈ Icc 0 T, ContDiff ℝ 3 (w t)) ∧ (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (w t) x‖ ≤ L) ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖w t x‖ ≤ L * (‖x‖ + c)) ∧
      ∀ t ∈ Icc 0 T, ∀ x, ‖w t x - v t x‖ ≤ η)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x ∂(ρ T) = ∫ x, φ x ∂(ρ' T) := by
  have hL0 : 0 ≤ L := by
    obtain ⟨w, -, hwL, -⟩ := happrox 1 one_pos
    exact (norm_nonneg _).trans (hwL 0 ⟨le_rfl, hT⟩ 0)
  refine integral_eq_of_weakContinuity2_of_localApprox hprob hprob' hρ hρ' h0 hT hvc hL0 hc hgr
    (fun _ => ⟨L, fun η hη => ?_⟩) hφ hφc
  obtain ⟨w, hw, hwL, hwgr, hwv⟩ := happrox η hη
  exact ⟨w, hw, hwL, hwgr, fun t ht x _ => hwv t ht x⟩

/-- **`UniqueWeakContinuity` for continuous velocities that are globally Lipschitz in space
(Verified).** Let `v : ℝ → ℝᵈ → ℝᵈ` with `(t, x) ↦ v_t(x)` continuous on `[0, ∞) × ℝᵈ` and,
for every `T ≥ 0`, constants `L, M` with `‖v_t(x) - v_t(y)‖ ≤ L ‖x - y‖` and `‖v_t(0)‖ ≤ M`
for all `t ∈ [0, T]`, `x, y ∈ ℝᵈ`. No differentiability of `v` (in `t` or `x`) is assumed.
Then uniqueness holds for `WeakContinuity2` (probability measures on `t ≥ 0`): two solutions
with the same time-`0` law agree at every `t ≥ 0`. Nothing is assumed for `t < 0`. The case
of `uniqueWeakContinuity_of_locallyLipschitz` with growth constant `max L 0 + M`. -/
theorem uniqueWeakContinuity_of_lipschitz_continuous {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hvc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2) (Ici 0 ×ˢ univ))
    (hbd : ∀ T, 0 ≤ T → ∃ L M : ℝ, ∀ t ∈ Icc 0 T,
      ‖v t 0‖ ≤ M ∧ ∀ x y, ‖v t x - v t y‖ ≤ L * ‖x - y‖) :
    UniqueWeakContinuity v := by
  refine uniqueWeakContinuity_of_locallyLipschitz hvc (fun T hT => ?_) (fun T hT R => ?_)
  · obtain ⟨L, M, h⟩ := hbd T hT
    refine ⟨max L 0 + M, fun t ht x => ?_⟩
    have h1 := (h t ht).2 x 0
    rw [sub_zero] at h1
    have h3 : ‖v t x‖ ≤ ‖v t x - v t 0‖ + ‖v t 0‖ := norm_le_norm_sub_add _ _
    have h4 : L * ‖x‖ ≤ max L 0 * ‖x‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have hM : 0 ≤ M := (norm_nonneg _).trans (h t ht).1
    nlinarith [norm_nonneg x, le_max_right L 0, (h t ht).1]
  · obtain ⟨L, M, h⟩ := hbd T hT
    exact ⟨L, fun t ht x y _ _ => (h t ht).2 x y⟩

/-- **`UniqueWeakContinuity` for autonomous Lipschitz velocities (Verified).** If
`w : ℝᵈ → ℝᵈ` is globally Lipschitz (`LipschitzWith K w`; no differentiability), uniqueness
holds for `WeakContinuity2` with the time-independent velocity `v_t = w`. -/
theorem uniqueWeakContinuity_of_autonomous_lipschitzWith {w : (Fin d → ℝ) → Fin d → ℝ}
    {K : NNReal} (hw : LipschitzWith K w) :
    UniqueWeakContinuity fun _ => w :=
  uniqueWeakContinuity_of_lipschitz_continuous (hw.continuous.comp continuous_snd).continuousOn
    fun _ _ => ⟨K, ‖w 0‖, fun _ _ => ⟨le_rfl, hw.norm_sub_le⟩⟩

/-- **`UniqueWeakContinuity` for smooth velocities with bounded spatial derivative
(Verified).** Let `v : ℝ → ℝᵈ → ℝᵈ` with `v_t ∈ C³` for every `t ≥ 0`, `(t, x) ↦ v_t(x)`
continuous on `[0, ∞) × ℝᵈ`, and, for every `T ≥ 0`, constants `L, M` with
`‖Dv_t(x)‖ ≤ L` and `‖v_t(0)‖ ≤ M` for all `t ∈ [0, T]`, `x ∈ ℝᵈ` (i.e. `v_t` globally
Lipschitz in `x`, locally uniformly in `t`). Then uniqueness holds for `WeakContinuity2`
(probability measures on `t ≥ 0`): two solutions with the same time-`0` law agree at every
`t ≥ 0`. Nothing is assumed about `v` for `t < 0`. Proof: the mean value inequality and
`uniqueWeakContinuity_of_lipschitz_continuous`. -/
theorem uniqueWeakContinuity_of_lipschitz {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hv : ∀ t, 0 ≤ t → ContDiff ℝ 3 (v t))
    (hvc : ContinuousOn (fun q : ℝ × (Fin d → ℝ) => v q.1 q.2) (Ici 0 ×ˢ univ))
    (hbd : ∀ T, 0 ≤ T → ∃ L M : ℝ, ∀ t ∈ Icc 0 T,
      ‖v t 0‖ ≤ M ∧ ∀ x, ‖fderiv ℝ (v t) x‖ ≤ L) :
    UniqueWeakContinuity v := by
  refine uniqueWeakContinuity_of_lipschitz_continuous hvc fun T hT => ?_
  obtain ⟨L, M, hLM⟩ := hbd T hT
  exact ⟨L, M, fun t ht => ⟨(hLM t ht).1, fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ((hv t ht.1).differentiable (by norm_num)) z) (fun z _ => (hLM t ht).2 z)
      (mem_univ y) (mem_univ x)⟩⟩

/-- **`UniqueWeakContinuity` for autonomous smooth velocities with bounded derivative
(Verified).** If `w : ℝᵈ → ℝᵈ` is `C³` with `‖Dw(x)‖ ≤ L` for all `x`, then uniqueness holds
for `WeakContinuity2` with the time-independent velocity `v_t = w`. -/
theorem uniqueWeakContinuity_of_autonomous_lipschitz {w : (Fin d → ℝ) → Fin d → ℝ}
    (hw : ContDiff ℝ 3 w) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ w x‖ ≤ L) :
    UniqueWeakContinuity fun _ => w :=
  uniqueWeakContinuity_of_lipschitz (fun _ _ => hw)
    (hw.continuous.comp continuous_snd).continuousOn
    fun _ _ => ⟨L, ‖w 0‖, fun _ _ => ⟨le_rfl, hL⟩⟩

/-! ### FL-5 corollaries -/

/-- **SDE / probability-flow one-time marginal equality for a locally Lipschitz
probability-flow velocity (FL-5 without the PDE-uniqueness input).** The hypotheses of
`map_flow_eq_of_weakFokkerPlanck` with the named input `UniqueWeakContinuity` replaced by the
sufficient condition of `uniqueWeakContinuity_of_locallyLipschitz` for
`u = probabilityFlowVelocity b D p` (`u_t = b_t - D ∇log p_t`): on each `[0, T]`,
`‖u_t(x)‖ ≤ M (1 + ‖x‖)`, and on each ball `‖x‖, ‖y‖ ≤ R`, `‖u_t(x) - u_t(y)‖ ≤ L_R ‖x - y‖`
(joint continuity of `u` is already a hypothesis). Then `(ρ 0).map (Φ t) = ρ t` for every
`t ≥ 0`; the Itô input `WeakFokkerPlanck ρ b D` remains a named hypothesis. Only one-time
marginals are matched. -/
theorem map_flow_eq_of_weakFokkerPlanck_of_locallyLipschitz {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : WeakFokkerPlanck ρ b D)
    (hgrowth : ∀ T, 0 ≤ T → ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
      ‖probabilityFlowVelocity b D p t x‖ ≤ M * (1 + ‖x‖))
    (hloc : ∀ T, 0 ≤ T → ∀ R : ℝ, ∃ L : ℝ, ∀ t ∈ Icc 0 T, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖probabilityFlowVelocity b D p t x - probabilityFlowVelocity b D p t y‖ ≤
        L * ‖x - y‖) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_weakFokkerPlanck hprob hρ hp hpos hu hΦ hΦm hΦ0 hFP
    (uniqueWeakContinuity_of_locallyLipschitz hu.continuousOn hgrowth hloc)

/-- **SDE / probability-flow one-time marginal equality for a `C¹` probability-flow velocity
of linear growth (FL-5 without the PDE-uniqueness input).** As
`map_flow_eq_of_weakFokkerPlanck_of_locallyLipschitz`, with the local Lipschitz bound replaced
by: `u_t = b_t - D ∇log p_t` differentiable for `t ≥ 0` with `(t, x) ↦ Du_t(x)` continuous
(e.g. `b` jointly `C¹` in `x` and `p` jointly `C²` in `x` with continuous derivatives in
`(t, x)` and `p > 0`). The Hessian of `log p_t` may be unbounded; only linear growth
`‖u_t(x)‖ ≤ M (1 + ‖x‖)` on each `[0, T]` is required. -/
theorem map_flow_eq_of_weakFokkerPlanck_of_contDiff_linearGrowth
    {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : WeakFokkerPlanck ρ b D)
    (hud : ∀ t, 0 ≤ t → Differentiable ℝ (probabilityFlowVelocity b D p t))
    (hdc : ContinuousOn
      (fun q : ℝ × (Fin d → ℝ) => fderiv ℝ (probabilityFlowVelocity b D p q.1) q.2)
      (Ici 0 ×ˢ univ))
    (hgrowth : ∀ T, 0 ≤ T → ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
      ‖probabilityFlowVelocity b D p t x‖ ≤ M * (1 + ‖x‖)) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_weakFokkerPlanck hprob hρ hp hpos hu hΦ hΦm hΦ0 hFP
    (uniqueWeakContinuity_of_contDiff_linearGrowth hud hu.continuousOn hdc hgrowth)

/-- **SDE / probability-flow one-time marginal equality for a Lipschitz probability-flow
velocity (FL-5 without the PDE-uniqueness input, no differentiability of the velocity).** The
hypotheses of `map_flow_eq_of_weakFokkerPlanck` with the named input `UniqueWeakContinuity`
replaced by its sufficient condition `uniqueWeakContinuity_of_lipschitz_continuous` for
`u = probabilityFlowVelocity b D p` (`u_t = b_t - D ∇log p_t`): on each `[0, T]`,
`‖u_t(x) - u_t(y)‖ ≤ L ‖x - y‖` and `‖u_t(0)‖ ≤ M` (joint continuity of `u` is already a
hypothesis). Then `(ρ 0).map (Φ t) = ρ t` for every `t ≥ 0`; the Itô input
`WeakFokkerPlanck ρ b D` remains a named hypothesis. Only one-time marginals are matched. -/
theorem map_flow_eq_of_weakFokkerPlanck_of_lipschitz_continuous {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : WeakFokkerPlanck ρ b D)
    (hbd : ∀ T, 0 ≤ T → ∃ L M : ℝ, ∀ t ∈ Icc 0 T, ‖probabilityFlowVelocity b D p t 0‖ ≤ M ∧
      ∀ x y, ‖probabilityFlowVelocity b D p t x - probabilityFlowVelocity b D p t y‖ ≤
        L * ‖x - y‖) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_weakFokkerPlanck hprob hρ hp hpos hu hΦ hΦm hΦ0 hFP
    (uniqueWeakContinuity_of_lipschitz_continuous hu.continuousOn hbd)

/-- **SDE / probability-flow one-time marginal equality for a smooth Lipschitz
probability-flow velocity (FL-5 without the PDE-uniqueness input).** The hypotheses of
`map_flow_eq_of_weakFokkerPlanck` with the named input `UniqueWeakContinuity` replaced by its
sufficient condition `uniqueWeakContinuity_of_lipschitz` for `u = probabilityFlowVelocity b D p`
(`u_t = b_t - D ∇log p_t`): `u_t` is `C³` for `t ≥ 0` and, on each `[0, T]`, `‖D u_t‖ ≤ L` and
`‖u_t(0)‖ ≤ M`. Then `(ρ 0).map (Φ t) = ρ t` for every `t ≥ 0`; the Itô input
`WeakFokkerPlanck ρ b D` remains a named hypothesis. Only one-time marginals are matched. -/
theorem map_flow_eq_of_weakFokkerPlanck_of_lipschitz {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} {p : ℝ → (Fin d → ℝ) → ℝ}
    {Φ : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : ∀ t, 0 ≤ t → ρ t = volume.withDensity fun x => ENNReal.ofReal (p t x))
    (hp : ∀ t, 0 ≤ t → ContDiff ℝ 1 (p t)) (hpos : ∀ t, 0 ≤ t → ∀ x, 0 < p t x)
    (hu : Continuous (fun q : ℝ × (Fin d → ℝ) => probabilityFlowVelocity b D p q.1 q.2))
    (hΦ : ∀ t x, HasDerivAt (fun s => Φ s x) (probabilityFlowVelocity b D p t (Φ t x)) t)
    (hΦm : ∀ t, Measurable (Φ t)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hFP : WeakFokkerPlanck ρ b D)
    (hu3 : ∀ t, 0 ≤ t → ContDiff ℝ 3 (probabilityFlowVelocity b D p t))
    (hbd : ∀ T, 0 ≤ T → ∃ L M : ℝ, ∀ t ∈ Icc 0 T, ‖probabilityFlowVelocity b D p t 0‖ ≤ M ∧
      ∀ x, ‖fderiv ℝ (probabilityFlowVelocity b D p t) x‖ ≤ L) :
    ∀ t, 0 ≤ t → (ρ 0).map (Φ t) = ρ t :=
  map_flow_eq_of_weakFokkerPlanck hprob hρ hp hpos hu hΦ hΦm hΦ0 hFP
    (uniqueWeakContinuity_of_lipschitz hu3 hu.continuousOn hbd)

end NoiseScore
end FormalizeSampling
