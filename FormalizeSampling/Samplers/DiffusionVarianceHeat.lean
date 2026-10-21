module

public import FormalizeSampling.Samplers.DiffusionDiscretizationEntropy

/-!
# Reverse variance `σ² = β`: the heat-flow analysis (T-uniform discretisation bound)

Status: **Verified** for every probability measure `ρ` on `Fin d → ℝ` with finite second
moment `M = ∫ |x|² dρ` (no density of `ρ` is assumed).

Notation as in `DiffusionDiscretizationEntropy.lean`: `p_u = heatFlowDensityPi ρ u`,
`H(u) = ∫ p_u log p_u`, `J(u) = ∫ |∇p_u|²/p_u`, `entropyStep ρ a b = H(a) - H(b) - ½ (b - a) J(b)`.

For a reverse step of the OU-forward DDPM chain between heat-flow times `a < b`
(`u = e^{2t} - 1`), the exact averaged KL of the Gaussian reverse step with the posterior mean and
the variance `σ² = β` (one of the two choices of Ho et al. 2020, "σ_t² = β_t") is
`betaStep ρ a b = entropyStep ρ a b + (d/2) log((1+a)/(1+b)) + (d(b-a) - (b-a)² J(b)) / (2(1+a))`
(identified with the KL in `DiffusionVarianceStep.lean`). This file bounds sums of `betaStep`.

## Main results

* `sq_le_mul_heatFisherInfo` (Cramér–Rao along the heat flow): `d² ≤ (M + d u) J(u)`.
* `heatNegEntropy_sub_le_log`: `H(a) - H(b) ≤ (d/2) log(b/a)` for `0 < a ≤ b`.
* `mul_fisherGap_le`: `b (d - (1+b) J(b)) ≤ (M - d)⁺`.
* `betaStep_le_entropyStep`: `betaStep ≤ entropyStep + (κ/2)(M-d)⁺ (1/(1+a) - 1/(1+b))` when
  `b - a ≤ κ a` (so `σ² = β` is never worse than `σ² = β/α²` up to the `(M-d)⁺` term).
* `betaStep_le_tail`: `betaStep ≤ (d/2)(L(b) - L(a)) + ((M-d)⁺/2)(1/a - 1/b)`,
  `L(x) = log x - log(1+x)`, **for any step size**.
* `sum_betaStep_le`: for a grid that satisfies `u_{k+1} - u_k ≤ κ u_k` only up to an index `m`
  (arbitrary afterwards),
  `∑_{k<n} betaStep ≤ (κd/2)(1 + log(u_m/u_0)) + (κ/2)(M-d)⁺ + (d/2) log((1+u_m)/u_m)
    + (M-d)⁺/(2u_m)`, independent of `n` and of `u_n`.
* `entropyStep_sub_betaStep`, `betaStep_add_le_entropyStep`: the exact difference between
  `σ² = β/α²` and `σ² = β`, and its lower bound `(d/2)(log((1+b)/(1+a)) - (b-a)/(1+b))` when
  `M ≤ d`.
* `sum_betaStep_le_of_le_mul`: if moreover `1 ≤ κ u_m ≤ 1 + κ`, the sum is
  `≤ (κ/2)(d (2 + log((1+κ)/(κ u_0))) + 2 (M-d)⁺)`.

## Not proved here

* The identification of `betaStep` with an averaged KL (`DiffusionVarianceStep.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi

variable {d : ℕ}

section Variance

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ρ] in
/-- `secondMoment ρ ≥ 0`. -/
theorem secondMoment_nonneg : 0 ≤ secondMoment ρ :=
  integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- **Cramér–Rao inequality along the heat flow.** For a probability `ρ` with finite second
moment `M` and `t > 0`: `d² ≤ (M + d t) J(t)`, i.e. `J(t) ≥ d² / E|Y_t|²`. Proof: Stein's
identity `∫ yᵢ ∂ᵢp_t = -1` and `0 ≤ ∫ ∑ᵢ (λ yᵢ p_t + ∂ᵢp_t)² / p_t` with `λ = d/(M + d t)`. -/
theorem sq_le_mul_heatFisherInfo (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ}
    (ht : 0 < t) : (d : ℝ) ^ 2 ≤ (secondMoment ρ + d * t) * heatFisherInfo ρ t := by
  obtain ⟨hqint, hqval⟩ := integral_heatFlowDensityPi_mul_sumSq hmom ht
  have hstein := fun i => integral_mul_heatFlowGradPi (ρ := ρ) hmom ht i
  have hJint := integrable_heatFisherInfo_integrand ρ ht
  set q := heatFlowDensityPi ρ t with hq
  set g := heatFlowGradPi ρ t with hg
  set P := secondMoment ρ + d * t with hP
  have hM0 := secondMoment_nonneg ρ
  have hJ0 := heatFisherInfo_nonneg ρ ht
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hPpos : 0 < P := by positivity
  set l := (d : ℝ) / P with hl
  set F : (Fin d → ℝ) → ℝ := fun y => l ^ 2 * (q y * ∑ i, y i ^ 2) +
    2 * l * ∑ i, y i * g y i + (∑ i, g y i ^ 2) / q y with hF
  have hFnn : ∀ y, 0 ≤ F y := by
    intro y
    have hqy : 0 < q y := heatFlowDensityPi_pos ρ ht y
    have e : F y = ∑ i, (l * y i * q y + g y i) ^ 2 / q y := by
      simp only [hF]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
      ring
    rw [e]
    exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) hqy.le
  have hsint : Integrable fun y => ∑ i, y i * g y i :=
    integrable_finsetSum _ fun i _ => (hstein i).1
  have hFint : ∫ y, F y = l ^ 2 * P + 2 * l * (-(d : ℝ)) + heatFisherInfo ρ t := by
    simp only [hF]
    rw [integral_add (f := fun y => l ^ 2 * (q y * ∑ i, y i ^ 2) + 2 * l * ∑ i, y i * g y i)
        ((hqint.const_mul _).add (hsint.const_mul _)) hJint,
      integral_add (f := fun y => l ^ 2 * (q y * ∑ i, y i ^ 2))
        (g := fun y => 2 * l * ∑ i, y i * g y i) (hqint.const_mul _) (hsint.const_mul _),
      integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun i _ => (hstein i).1, hqval]
    simp only [fun i => (hstein i).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_neg, mul_one]
    rfl
  have h0 : 0 ≤ ∫ y, F y := integral_nonneg hFnn
  rw [hFint, hl] at h0
  have e : ((d : ℝ) / P) ^ 2 * P + 2 * (d / P) * -(d : ℝ) = -((d : ℝ) ^ 2 / P) := by
    field_simp; ring
  rw [e] at h0
  have : (d : ℝ) ^ 2 / P ≤ heatFisherInfo ρ t := by linarith
  rwa [div_le_iff₀ hPpos, mul_comm] at this

/-- **Entropy production is at most that of a point mass.** For a probability `ρ` with finite
second moment and `0 < a ≤ b`: `H(a) - H(b) ≤ (d/2) log(b/a)` (from `H' = -J/2` and
`J(s) ≤ d/s`). -/
theorem heatNegEntropy_sub_le_log (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    heatNegEntropy ρ a - heatNegEntropy ρ b ≤ d / 2 * Real.log (b / a) := by
  set g : ℝ → ℝ := fun s => heatNegEntropy ρ s + d / 2 * Real.log s with hg
  have hgd : ∀ s ∈ Icc a b, HasDerivAt g
      (-(1 / 2) * heatFisherInfo ρ s + d / 2 * s⁻¹) s := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    exact (hasDerivAt_heatNegEntropy ρ hmom hs0).add
      ((Real.hasDerivAt_log hs0.ne').const_mul _)
  have hmono : MonotoneOn g (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun s hs => (hgd s hs).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hgd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs0 : 0 < s := ha.trans hs.1
      rw [(hgd s (Ioo_subset_Icc_self hs)).deriv]
      have h := heatFisherInfo_le ρ hs0
      have : heatFisherInfo ρ s ≤ d * s⁻¹ := by rwa [div_eq_mul_inv] at h
      linarith
  have := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  simp only [hg] at this
  rw [Real.log_div (ha.trans_le hab).ne' ha.ne']
  linarith

/-- **Fisher-information gap.** For a probability `ρ` with finite second moment `M` and `b > 0`:
`b (d - (1 + b) J(b)) ≤ max (M - d) 0`. (Cramér–Rao; in OU coordinates this says
`J(p_t) ≥ d` when `M ≤ d`.) -/
theorem mul_fisherGap_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {b : ℝ} (hb : 0 < b) :
    b * (d - (1 + b) * heatFisherInfo ρ b) ≤ max (secondMoment ρ - d) 0 := by
  set M := secondMoment ρ
  set J := heatFisherInfo ρ b
  have hM0 : 0 ≤ M := secondMoment_nonneg ρ
  have hJ0 : 0 ≤ J := heatFisherInfo_nonneg ρ hb
  have hCR := sq_le_mul_heatFisherInfo ρ hmom hb
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : b * (0 - (1 + b) * J) ≤ 0 := by
      have : 0 ≤ b * ((1 + b) * J) := by positivity
      linarith
    simp only [CharP.cast_eq_zero]
    exact this.trans (le_max_right _ _)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set P := M + d * b
  have hP : 0 < P := by positivity
  refine le_of_mul_le_mul_left ?_ hP
  have h1 : P * (b * (d - (1 + b) * J)) ≤ b * d * (M - d) := by
    have : (d : ℝ) ^ 2 * (b * (1 + b)) ≤ P * J * (b * (1 + b)) :=
      mul_le_mul_of_nonneg_right hCR (by positivity)
    have e : P * (b * (d - (1 + b) * J)) = P * b * d - P * J * (b * (1 + b)) := by ring
    have e2 : b * d * (M - d) = P * b * d - (d : ℝ) ^ 2 * (b * (1 + b)) := by ring
    rw [e, e2]; linarith
  refine h1.trans ?_
  rcases le_total (d : ℝ) M with h | h
  · rw [max_eq_left (by linarith)]
    have : b * d ≤ P := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  · rw [max_eq_right (by linarith)]
    have : b * d * (M - d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

/-- The exact averaged KL of the Gaussian reverse step with posterior mean and variance
`σ² = β` (one of the two choices of Ho et al. 2020), in heat-flow coordinates `a < b`:
`entropyStep ρ a b + (d/2) log((1+a)/(1+b)) + (d (b-a) - (b-a)² J(b)) / (2 (1+a))`
(see `DiffusionDiscretization.lintegral_klDiv_revKernel_fwdVar_eq`). -/
noncomputable def betaStep (ρ : Measure (Fin d → ℝ)) (a b : ℝ) : ℝ :=
  entropyStep ρ a b + d / 2 * Real.log ((1 + a) / (1 + b)) +
    (d * (b - a) - (b - a) ^ 2 * heatFisherInfo ρ b) / (2 * (1 + a))

/-- **Head bound: `σ² = β` versus `σ² = β/α²`.** For `0 < a ≤ b` with `b - a ≤ κ a`
(`κ ≥ 0`): `betaStep ρ a b ≤ entropyStep ρ a b + (κ/2)(M-d)⁺ (1/(1+a) - 1/(1+b))`. -/
theorem betaStep_le_entropyStep (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b κ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hκ : 0 ≤ κ) (hstep : b - a ≤ κ * a) :
    betaStep ρ a b ≤ entropyStep ρ a b +
      κ / 2 * max (secondMoment ρ - d) 0 * (1 / (1 + a) - 1 / (1 + b)) := by
  have hb : 0 < b := ha.trans_le hab
  set J := heatFisherInfo ρ b
  set m := max (secondMoment ρ - d) 0
  have hm0 : 0 ≤ m := le_max_right _ _
  have hX := mul_fisherGap_le ρ hmom hb
  set X := b * (d - (1 + b) * J)
  set Δ := b - a
  have hΔ : 0 ≤ Δ := by simp only [Δ]; linarith
  have hca : 0 < 1 + a := by linarith
  have hcb : 0 < 1 + b := by linarith
  have hlog : Real.log ((1 + a) / (1 + b)) ≤ (1 + a) / (1 + b) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hid : betaStep ρ a b - entropyStep ρ a b =
      d / 2 * (Real.log ((1 + a) / (1 + b)) - ((1 + a) / (1 + b) - 1)) +
        Δ ^ 2 * X / (2 * (1 + a) * (1 + b) * b) := by
    simp only [betaStep, X, Δ]
    field_simp
    ring
  have h1 : d / 2 * (Real.log ((1 + a) / (1 + b)) - ((1 + a) / (1 + b) - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hΔb : Δ ≤ κ * b := hstep.trans (mul_le_mul_of_nonneg_left hab hκ)
  have h2 : Δ ^ 2 * X / (2 * (1 + a) * (1 + b) * b) ≤
      κ / 2 * m * (1 / (1 + a) - 1 / (1 + b)) := by
    have e : κ / 2 * m * (1 / (1 + a) - 1 / (1 + b)) =
        κ * b * Δ * m / (2 * (1 + a) * (1 + b) * b) := by
      simp only [Δ]; field_simp; ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc Δ ^ 2 * X ≤ Δ ^ 2 * m := mul_le_mul_of_nonneg_left hX (by positivity)
      _ = Δ * Δ * m := by ring
      _ ≤ κ * b * Δ * m := by
          have := mul_le_mul_of_nonneg_left hΔb hΔ
          nlinarith
  linarith

/-- **Tail bound for `σ² = β`, any step size.** For `0 < a ≤ b`, with `L(x) = log x - log(1+x)`:
`betaStep ρ a b ≤ (d/2)(L(b) - L(a)) + ((M - d)⁺ / 2)(1/a - 1/b)`. -/
theorem betaStep_le_tail (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    betaStep ρ a b ≤ d / 2 * ((Real.log b - Real.log (1 + b)) - (Real.log a - Real.log (1 + a)))
      + max (secondMoment ρ - d) 0 / 2 * (1 / a - 1 / b) := by
  have hb : 0 < b := ha.trans_le hab
  set J := heatFisherInfo ρ b
  set m := max (secondMoment ρ - d) 0
  have hm0 : 0 ≤ m := le_max_right _ _
  have hX := mul_fisherGap_le ρ hmom hb
  set X := b * (d - (1 + b) * J)
  have hca : 0 < 1 + a := by linarith
  have hcb : 0 < 1 + b := by linarith
  have hH := heatNegEntropy_sub_le_log ρ hmom ha hab
  rw [Real.log_div hb.ne' ha.ne'] at hH
  have hid : betaStep ρ a b = (heatNegEntropy ρ a - heatNegEntropy ρ b) +
      d / 2 * (Real.log (1 + a) - Real.log (1 + b)) + (b - a) * X / (2 * (1 + a) * b) := by
    simp only [betaStep, entropyStep, X]
    rw [Real.log_div hca.ne' hcb.ne']
    field_simp
    ring
  have h2 : (b - a) * X / (2 * (1 + a) * b) ≤ m / 2 * (1 / a - 1 / b) := by
    have e : m / 2 * (1 / a - 1 / b) = (b - a) * m / (2 * a * b) := by field_simp
    rw [e]
    calc (b - a) * X / (2 * (1 + a) * b) ≤ (b - a) * m / (2 * (1 + a) * b) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by linarith))
            (by positivity)
      _ ≤ (b - a) * m / (2 * a * b) :=
          div_le_div_of_nonneg_left (mul_nonneg (by linarith) hm0) (by positivity)
            (by nlinarith)
  rw [hid]
  linarith

/-- **T-uniform discretisation sum for `σ² = β` (heat-flow coordinates).** Let `ρ` have finite
second moment `M`, `κ ≥ 0`, `m ≤ n`, and `0 < u 0 ≤ u 1 ≤ ⋯ ≤ u n` with
`u (k+1) - u k ≤ κ u k` **only for `k < m`** (the steps after `m` are arbitrary). Then
`∑_{k<n} betaStep ρ (u k) (u (k+1)) ≤ (κd/2)(1 + log(u_m/u_0)) + (κ/2)(M-d)⁺
  + (d/2)(log(1 + u_m) - log u_m) + (M-d)⁺ / (2 u_m)`.
The right side depends neither on `n` nor on `u_n`. -/
theorem sum_betaStep_le (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {u : ℕ → ℝ} {κ : ℝ}
    {m n : ℕ} (hmn : m ≤ n) (hκ : 0 ≤ κ) (h0 : 0 < u 0)
    (hmono : ∀ k < n, u k ≤ u (k + 1)) (hu : ∀ k < m, u (k + 1) - u k ≤ κ * u k) :
    ∑ k ∈ Finset.range n, betaStep ρ (u k) (u (k + 1)) ≤
      κ * d / 2 * (1 + Real.log (u m / u 0)) + κ / 2 * max (secondMoment ρ - d) 0 +
        d / 2 * (Real.log (1 + u m) - Real.log (u m)) +
        max (secondMoment ρ - d) 0 / (2 * u m) := by
  set mx := max (secondMoment ρ - d) 0
  have hmx : 0 ≤ mx := le_max_right _ _
  have hpos : ∀ k ≤ n, 0 < u k := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact (ih (by omega)).trans_le (hmono k (by omega))
  rw [← Finset.sum_range_add_sum_Ico _ hmn]
  -- head
  have hhead : ∑ k ∈ Finset.range m, betaStep ρ (u k) (u (k + 1)) ≤
      κ * d / 2 * (1 + Real.log (u m / u 0)) + κ / 2 * mx := by
    have hB := sum_entropyStep_le ρ hmom (u := u) m hκ h0 (fun k hk => hmono k (by omega)) hu
    have hstep : ∑ k ∈ Finset.range m, betaStep ρ (u k) (u (k + 1)) ≤
        ∑ k ∈ Finset.range m, (entropyStep ρ (u k) (u (k + 1)) +
          κ / 2 * mx * (1 / (1 + u k) - 1 / (1 + u (k + 1)))) :=
      Finset.sum_le_sum fun k hk => by
        have hk' := Finset.mem_range.1 hk
        exact betaStep_le_entropyStep ρ hmom (hpos k (by omega)) (hmono k (by omega)) hκ
          (hu k hk')
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_range_sub' (fun k => 1 / (1 + u k)) m] at hstep
    have hm' : 0 < u m := hpos m hmn
    have h1 : 1 / (1 + u 0) - 1 / (1 + u m) ≤ 1 := by
      have : 1 / (1 + u 0) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have : 0 ≤ 1 / (1 + u m) := by positivity
      linarith
    have h2 : κ / 2 * mx * (1 / (1 + u 0) - 1 / (1 + u m)) ≤ κ / 2 * mx :=
      by simpa using mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ κ / 2 * mx)
    linarith
  -- tail
  have htail : ∑ k ∈ Finset.Ico m n, betaStep ρ (u k) (u (k + 1)) ≤
      d / 2 * (Real.log (1 + u m) - Real.log (u m)) + mx / (2 * u m) := by
    set L : ℝ → ℝ := fun x => Real.log x - Real.log (1 + x)
    have hstep : ∑ k ∈ Finset.Ico m n, betaStep ρ (u k) (u (k + 1)) ≤
        ∑ k ∈ Finset.Ico m n, (d / 2 * (L (u (k + 1)) - L (u k)) +
          mx / 2 * (1 / u k - 1 / u (k + 1))) :=
      Finset.sum_le_sum fun k hk => by
        have hk' := Finset.mem_Ico.1 hk
        exact betaStep_le_tail ρ hmom (hpos k (by omega)) (hmono k hk'.2)
    have e1 : ∑ k ∈ Finset.Ico m n, (L (u (k + 1)) - L (u k)) = L (u n) - L (u m) :=
      Finset.sum_Ico_sub (fun k => L (u k)) hmn
    have e2 : ∑ k ∈ Finset.Ico m n, (1 / u k - 1 / u (k + 1)) = 1 / u m - 1 / u n := by
      simpa only [neg_sub_neg] using Finset.sum_Ico_sub (fun k => -(1 / u k)) hmn
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, e2] at hstep
    have hun := hpos n le_rfl
    have hum := hpos m hmn
    have hLn : L (u n) ≤ 0 := by
      simp only [L]
      have := Real.log_le_log hun (by linarith : u n ≤ 1 + u n)
      linarith
    have h3 : mx / 2 * (1 / u m - 1 / u n) ≤ mx / (2 * u m) := by
      have : 0 ≤ 1 / u n := by positivity
      have e : mx / (2 * u m) = mx / 2 * (1 / u m) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : d / 2 * (L (u n) - L (u m)) ≤ d / 2 * (Real.log (1 + u m) - Real.log (u m)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simp only [L] at hLn ⊢
      linarith
    linarith
  linarith

/-- **Headline form of `sum_betaStep_le`.** Under the hypotheses of `sum_betaStep_le` with
the switching index chosen so that `1 ≤ κ u_m ≤ 1 + κ` (this forces `κ > 0`, since
`u_m ≥ u_0 > 0`):
`∑_{k<n} betaStep ρ (u k) (u (k+1)) ≤ (κ/2)(d (2 + log((1+κ)/(κ u_0))) + 2 (M - d)⁺)`,
for every `n ≥ m` and every continuation of the grid after `m`. -/
theorem sum_betaStep_le_of_le_mul (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    {u : ℕ → ℝ} {κ : ℝ} {m n : ℕ} (hmn : m ≤ n) (h0 : 0 < u 0)
    (hmono : ∀ k < n, u k ≤ u (k + 1)) (hu : ∀ k < m, u (k + 1) - u k ≤ κ * u k)
    (hm1 : 1 ≤ κ * u m) (hm2 : κ * u m ≤ 1 + κ) :
    ∑ k ∈ Finset.range n, betaStep ρ (u k) (u (k + 1)) ≤
      κ / 2 * (d * (2 + Real.log ((1 + κ) / (κ * u 0))) +
        2 * max (secondMoment ρ - d) 0) := by
  have hum : 0 < u m := by
    have hpos : ∀ k ≤ n, 0 < u k := by
      intro k hk
      induction k with
      | zero => exact h0
      | succ k ih => exact (ih (by omega)).trans_le (hmono k (by omega))
    exact hpos m hmn
  have hκ : 0 < κ := by
    by_contra hc
    have : κ * u m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hum.le
    linarith
  have h := sum_betaStep_le ρ hmom hmn hκ.le h0 hmono hu
  set mx := max (secondMoment ρ - d) 0
  have hmx : 0 ≤ mx := le_max_right _ _
  have hinv : 1 / u m ≤ κ := by rw [div_le_iff₀ hum]; linarith
  have hl1 : Real.log (1 + u m) - Real.log (u m) ≤ κ := by
    rw [← Real.log_div (by linarith) hum.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    have : (1 + u m) / u m - 1 = 1 / u m := by field_simp; ring
    rw [this]; exact hinv
  have hl2 : Real.log (u m / u 0) ≤ Real.log ((1 + κ) / (κ * u 0)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ h0 (by positivity)]
    nlinarith
  have hl3 : mx / (2 * u m) ≤ κ / 2 * mx := by
    have e : mx / (2 * u m) = mx / 2 * (1 / u m) := by field_simp
    rw [e]
    nlinarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h4 : κ * d / 2 * (1 + Real.log (u m / u 0)) ≤
      κ * d / 2 * (1 + Real.log ((1 + κ) / (κ * u 0))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h5 : d / 2 * (Real.log (1 + u m) - Real.log (u m)) ≤ d / 2 * κ :=
    mul_le_mul_of_nonneg_left hl1 (by positivity)
  nlinarith

omit [IsProbabilityMeasure ρ] in
/-- **Exact difference between `σ² = β/α²` and `σ² = β`** (heat-flow coordinates, `-1 < a < b`):
`entropyStep ρ a b - betaStep ρ a b = (d/2)(log((1+b)/(1+a)) - (b-a)/(1+b))
  + (b-a)² ((1+b) J(b) - d) / (2 (1+a)(1+b))`.
In OU coordinates: `(d/2)(-log(1-β) - β) + β² (J(p_{k}) - d)/(2α²)`. -/
theorem entropyStep_sub_betaStep {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) :
    entropyStep ρ a b - betaStep ρ a b =
      d / 2 * (Real.log ((1 + b) / (1 + a)) - (b - a) / (1 + b)) +
        (b - a) ^ 2 * ((1 + b) * heatFisherInfo ρ b - d) / (2 * (1 + a) * (1 + b)) := by
  have hca : 0 < 1 + a := by linarith
  have hcb : 0 < 1 + b := by linarith
  have hl : Real.log ((1 + a) / (1 + b)) = -Real.log ((1 + b) / (1 + a)) := by
    rw [← Real.log_inv, inv_div]
  simp only [betaStep]
  rw [hl]
  field_simp
  ring

/-- **`σ² = β/α²` loses at least `(d/2)ψ(β)` against `σ² = β` on normalised data.** If
`M = ∫ |x|² dρ ≤ d` and `0 < a ≤ b`:
`entropyStep ρ a b ≥ betaStep ρ a b + (d/2)(log((1+b)/(1+a)) - (b-a)/(1+b))`
(in OU coordinates `(d/2)(-log(1-β) - β) = (d/2)(2h - β)`). -/
theorem betaStep_add_le_entropyStep (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    (hM : secondMoment ρ ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    betaStep ρ a b + d / 2 * (Real.log ((1 + b) / (1 + a)) - (b - a) / (1 + b)) ≤
      entropyStep ρ a b := by
  have hb : 0 < b := ha.trans_le hab
  have hX := mul_fisherGap_le ρ hmom hb
  rw [max_eq_right (by linarith)] at hX
  have hJ : 0 ≤ (1 + b) * heatFisherInfo ρ b - d := by
    by_contra h
    push Not at h
    have : 0 < b * (d - (1 + b) * heatFisherInfo ρ b) := mul_pos hb (by linarith)
    linarith
  have h := entropyStep_sub_betaStep ρ (by linarith : -1 < a) hab
  have : 0 ≤ (b - a) ^ 2 * ((1 + b) * heatFisherInfo ρ b - d) / (2 * (1 + a) * (1 + b)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) hJ) (by positivity)
  linarith

end Variance

end FormalizeSampling.DiffusionDiscretization
