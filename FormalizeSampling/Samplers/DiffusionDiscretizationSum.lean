module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Summation by parts for the discretisation error of diffusion samplers

Status: **Verified** (elementary real analysis).

This is the deterministic summation step of the `d`-linear bound on the discretisation term of a
DDPM-type sampler (used in `Samplers/DiffusionDiscretizationEntropy.lean`). In heat-flow
coordinates the per-step discretisation error is at most `½ (u_{k+1} - u_k) (J_k - J_{k+1})`,
a Riemann error of the non-increasing Fisher information `J_k = J(u_k) ≤ d / u_k`. On a grid
that is geometric with ratio at most `1 + κ` (`u_{k+1} - u_k ≤ κ u_k`) the total is
`O(κ d log(u_n / u_0))`.

Indices: the grid is `u 0 < u 1 < … < u n` and steps are `k → k + 1`, `k < n`.

## Main results

* `sum_sub_mul_sub_le`: `∑_{k<n} (u_{k+1} - u_k)(J_k - J_{k+1}) ≤
  κ (u_0 J_0 + ∑_{k<n} (u_{k+1} - u_k) J_{k+1})` for non-increasing `J` and
  `u_{k+1} - u_k ≤ κ u_k`.
* `sum_sub_div_le_log`: `∑_{k<n} (u_{k+1} - u_k) / u_{k+1} ≤ log(u_n / u_0)` for a positive
  non-decreasing grid.
* `sum_riemannError_le`: the combination, `∑_{k<n} (u_{k+1} - u_k)(J_k - J_{k+1}) ≤
  κ D (1 + log(u_n / u_0))` when moreover `0 ≤ J_k ≤ D / u_k`.

## Not proved here

* The analytic inputs (`J` non-increasing along the heat flow, `J(u) ≤ d / u`, and the per-step
  bound) — see `Samplers/DiffusionDiscretization*.lean`.
-/

public section

open Finset

namespace FormalizeSampling.DiffusionDiscretization

/-- **Summation by parts.** Let `u J : ℕ → ℝ`, `κ ≥ 0`, with `J` non-increasing on
`0..n` (`J (k+1) ≤ J k`) and grid increments `u (k+1) - u k ≤ κ u k` (`k < n`). Then
`∑_{k<n} (u_{k+1} - u_k)(J_k - J_{k+1}) ≤ κ (u_0 J_0 - u_n J_n + ∑_{k<n} (u_{k+1} - u_k) J_{k+1})`.
-/
theorem sum_sub_mul_sub_le {u J : ℕ → ℝ} {κ : ℝ} (n : ℕ)
    (hJ : ∀ k < n, J (k + 1) ≤ J k) (hu : ∀ k < n, u (k + 1) - u k ≤ κ * u k) :
    ∑ k ∈ range n, (u (k + 1) - u k) * (J k - J (k + 1)) ≤
      κ * (u 0 * J 0 - u n * J n + ∑ k ∈ range n, (u (k + 1) - u k) * J (k + 1)) := by
  have h1 : ∑ k ∈ range n, (u (k + 1) - u k) * (J k - J (k + 1)) ≤
      ∑ k ∈ range n, κ * u k * (J k - J (k + 1)) :=
    sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hu k (mem_range.1 hk)) (sub_nonneg.2 (hJ k (mem_range.1 hk)))
  have h2 : ∑ k ∈ range n, κ * u k * (J k - J (k + 1)) =
      κ * (∑ k ∈ range n, (u k * J k - u (k + 1) * J (k + 1)) +
        ∑ k ∈ range n, (u (k + 1) - u k) * J (k + 1)) := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have h3 : ∑ k ∈ range n, (u k * J k - u (k + 1) * J (k + 1)) = u 0 * J 0 - u n * J n :=
    sum_range_sub' (fun k => u k * J k) n
  rw [h2, h3] at h1
  exact h1

/-- **Logarithmic sum.** For a grid `0 < u 0` with `u k ≤ u (k+1)` (`k < n`):
`∑_{k<n} (u_{k+1} - u_k) / u_{k+1} ≤ log(u_n / u_0)`. -/
theorem sum_sub_div_le_log {u : ℕ → ℝ} (n : ℕ) (h0 : 0 < u 0)
    (hmono : ∀ k < n, u k ≤ u (k + 1)) :
    ∑ k ∈ range n, (u (k + 1) - u k) / u (k + 1) ≤ Real.log (u n / u 0) := by
  have hpos : ∀ k ≤ n, 0 < u k := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact (ih (by omega)).trans_le (hmono k (by omega))
  have hterm : ∀ k < n,
      (u (k + 1) - u k) / u (k + 1) ≤ Real.log (u (k + 1)) - Real.log (u k) := by
    intro k hk
    have ha := hpos k hk.le
    have hb := hpos (k + 1) hk
    rw [← Real.log_div hb.ne' ha.ne']
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    rw [inv_div] at h
    calc (u (k + 1) - u k) / u (k + 1) = 1 - u k / u (k + 1) := by field_simp
      _ ≤ _ := h
  calc ∑ k ∈ range n, (u (k + 1) - u k) / u (k + 1)
      ≤ ∑ k ∈ range n, (Real.log (u (k + 1)) - Real.log (u k)) :=
        sum_le_sum fun k hk => hterm k (mem_range.1 hk)
    _ = Real.log (u n) - Real.log (u 0) := sum_range_sub (fun k => Real.log (u k)) n
    _ = Real.log (u n / u 0) := (Real.log_div (hpos n le_rfl).ne' h0.ne').symm

/-- **Riemann-error sum on a geometric grid.** Let `0 < u 0`, `u` non-decreasing on `0..n` with
`u (k+1) - u k ≤ κ u k` (`κ ≥ 0`), and `J` non-increasing with `0 ≤ J k` and `u k J k ≤ D`
(`k ≤ n`). Then `∑_{k<n} (u_{k+1} - u_k)(J_k - J_{k+1}) ≤ κ D (1 + log(u_n / u_0))`.
Applied with `J k = J(u_k)` the Fisher information of the heat flow, `J(u) ≤ d / u`, `D = d`. -/
theorem sum_riemannError_le {u J : ℕ → ℝ} {κ D : ℝ} (n : ℕ) (hκ : 0 ≤ κ) (h0 : 0 < u 0)
    (hmono : ∀ k < n, u k ≤ u (k + 1)) (hu : ∀ k < n, u (k + 1) - u k ≤ κ * u k)
    (hJ : ∀ k < n, J (k + 1) ≤ J k) (hJ0 : ∀ k ≤ n, 0 ≤ J k)
    (hJD : ∀ k ≤ n, u k * J k ≤ D) :
    ∑ k ∈ range n, (u (k + 1) - u k) * (J k - J (k + 1)) ≤
      κ * D * (1 + Real.log (u n / u 0)) := by
  have hpos : ∀ k ≤ n, 0 < u k := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact (ih (by omega)).trans_le (hmono k (by omega))
  have hD : 0 ≤ D := (mul_nonneg h0.le (hJ0 0 (Nat.zero_le _))).trans (hJD 0 (Nat.zero_le _))
  have hS := sum_sub_mul_sub_le n hJ hu
  have hterm : ∀ k < n, (u (k + 1) - u k) * J (k + 1) ≤ D * ((u (k + 1) - u k) / u (k + 1)) := by
    intro k hk
    have hb := hpos (k + 1) hk
    have hJk : J (k + 1) ≤ D / u (k + 1) := by
      rw [le_div_iff₀ hb, mul_comm]; exact hJD (k + 1) hk
    calc (u (k + 1) - u k) * J (k + 1) ≤ (u (k + 1) - u k) * (D / u (k + 1)) :=
          mul_le_mul_of_nonneg_left hJk (sub_nonneg.2 (hmono k hk))
      _ = D * ((u (k + 1) - u k) / u (k + 1)) := by ring
  have hsum : ∑ k ∈ range n, (u (k + 1) - u k) * J (k + 1) ≤ D * Real.log (u n / u 0) := by
    calc ∑ k ∈ range n, (u (k + 1) - u k) * J (k + 1)
        ≤ ∑ k ∈ range n, D * ((u (k + 1) - u k) / u (k + 1)) :=
          sum_le_sum fun k hk => hterm k (mem_range.1 hk)
      _ = D * ∑ k ∈ range n, (u (k + 1) - u k) / u (k + 1) := by rw [mul_sum]
      _ ≤ D * Real.log (u n / u 0) :=
          mul_le_mul_of_nonneg_left (sum_sub_div_le_log n h0 hmono) hD
  have hn : 0 ≤ u n * J n := mul_nonneg (hpos n le_rfl).le (hJ0 n le_rfl)
  have h00 := hJD 0 (Nat.zero_le _)
  calc ∑ k ∈ range n, (u (k + 1) - u k) * (J k - J (k + 1))
      ≤ κ * (u 0 * J 0 - u n * J n + ∑ k ∈ range n, (u (k + 1) - u k) * J (k + 1)) := hS
    _ ≤ κ * (D + D * Real.log (u n / u 0)) := by
        apply mul_le_mul_of_nonneg_left _ hκ; linarith
    _ = κ * D * (1 + Real.log (u n / u 0)) := by ring

end FormalizeSampling.DiffusionDiscretization
