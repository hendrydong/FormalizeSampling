module

public import FormalizeSampling.Samplers.DiffusionVarianceMain

/-!
# Sharpness of the `O(κ)` discretisation bound of the DDPM sampler

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean` and `Samplers/DiffusionMain.lean`: data law `μ` on
`Fin d → ℝ` with finite second moment `M = ∫ |x|² dμ`, grid `0 = t_0 < t_1 < ⋯ < t_N`, heat-flow
times `u_k = e^{2 t_k} - 1` (`heatTime`), exact reverse kernels `R_k`, posterior means `m*_k`,
and the Gaussian reverse step `N(m*_k(y), (β_k/α_k²) I)` (`ddpmVar`). Write
`D_N := ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k(y)` (the discretisation part of the
path-space KL with exact score). `DiffusionMain` proves
`D_N ≤ (κd/2)(1 + log(u_N/u_1))` when `u_{k+1} ≤ (1+κ) u_k`, i.e. `O(1/N)` in the number of steps.
This file shows that this rate is the true rate of `D_N` (neither `D_N` nor the path KL
`KL(truePath ‖ algPath) ≥ D_N` can be `O(1/N²)` once the noise dominates the data scale, see
(3)), for every data law, with the constant correct up to a factor `≈ 2`.

**(1) Universal per-step sandwich** (`le_entropyStep`, `entropyStep_le_log`). For every law
with finite second moment `M` and `0 < a ≤ b`, the heat-coordinate step error
`entropyStep ρ a b = H(a) - H(b) - ½ (b - a) J(b)` satisfies
`(d/2)(log((M + d b)/(M + d a)) - (b - a)/b) ≤ entropyStep ρ a b
  ≤ (d/2)(log(b/a) - d (b - a)/(M + d b))`.
Proof: de Bruijn `H' = -J/2`, Cramér–Rao `J(s) ≥ d²/(M + d s)` and `J(s) ≤ d/s`.

**(2) Point mass: exact formula** (`entropyStep_dirac`, `sum_lintegral_klDiv_revKernel_ddpm_dirac`).
For `μ = δ_0`, `D_N = (d/2) ∑_{k=2}^N (log(u_k/u_{k-1}) - (u_k - u_{k-1})/u_k)`, for every grid.

**(3) Universal lower bound** (`sum_lintegral_klDiv_revKernel_ddpm_ge_log`). For every data law
with finite second moment, every grid and every `1 ≤ m ≤ N`:
`D_N ≥ (d/2) (∑_{k=m+1}^N (log(u_k/u_{k-1}) - (u_k - u_{k-1})/u_k) - log(1 + M/(d u_m)))`.
On the geometric grid `u_k = u_1 r^{k-1}` (`sum_lintegral_klDiv_revKernel_geomGrid_ge`) this is
`(d/2)((N - m)(log r - 1 + 1/r) - log(1 + M/(d u_1 r^{m-1})))`; choosing `u_m ≈ M/(d (r-1))` it
is `≈ (d (r-1)/4) log((r-1) d u_N / M)`: every law pays `Θ(κ)` per unit of `log u` once the noise
dominates the data scale, so the path/per-step discretisation error is `Θ(1/N)`, never `O(1/N²)`.

**(4) The geometric grid is optimal for `δ_0`, and the bound of `DiffusionMain` is tight
within a factor `2r`.** For `μ = δ_0` and any grid with `N - 1` steps between `u_1` and `u_N`,
`D_N ≥ (d/2)(N-1) g(L/(N-1))`, `g(x) = x - 1 + e^{-x}`, `L = log(u_N/u_1)`
(`sum_lintegral_klDiv_revKernel_ddpm_dirac_ge`, convexity of `g`), with equality on the geometric
grid (`sum_lintegral_klDiv_revKernel_geomGrid_dirac`). On the geometric grid
`(r-1)(d/2)(1 + (N-1) log r) ≤ 2r D_N + (r-1) d/2` (`discBound_geomGrid_le_dirac`), so the
`DiffusionMain` bound is attained up to the factor `2r → 2` (as `r → 1`) for `δ_0`.

Relation to the literature: Benton–De Bortoli–Doucet–Deligiannidis (2024, arXiv:2308.03686, §4)
point out that the path KL is of the order of the step size in the worst case, for instance for
point-mass data; Chen–Lee–Lu (2023, arXiv:2211.01916, App. B) show by a convexity argument in
log-time that geometric steps minimise their upper bound (compare (4)); Sun–Poor–Zhang (2026,
arXiv:2601.13602, Thm 3) give an asymptotic continuous-time path-KL lower bound in which Gaussian
data is the extremal case. We have not found the non-asymptotic lower bound (3) for every data
law, or the exact optimality in (4), stated in this form.

## Main results

* `le_heatNegEntropy_sub_log`, `le_entropyStep`, `entropyStep_le_log`: the sandwich (1).
* `entropyStep_dirac`, `sum_lintegral_klDiv_revKernel_ddpm_dirac`: the exact point-mass value (2).
* `sum_entropyStep_ge`, `sum_lintegral_klDiv_revKernel_ddpm_ge_log`,
  `sum_lintegral_klDiv_revKernel_geomGrid_ge`: the universal lower bound (3).
* `sum_lintegral_klDiv_revKernel_ddpm_dirac_ge`, `sum_lintegral_klDiv_revKernel_geomGrid_dirac`,
  `discBound_geomGrid_le_dirac`: optimality of the geometric grid and tightness (4).

## Not proved here

* Statements about the **output** law `q_1` for general data. For exact-score Gaussian data
  `N(0, I)` on a uniform grid over a fixed interval, `DiffusionGaussianOutputExt` proves output
  KL `Θ(d h²)` against a path lower bound of order `d h`; for other data the faster output
  decay is numerical (`showcase/ddpm_rate.py`).
* The per-step sum with the optimal (Analytic-DPM) isotropic variance vanishes for Gaussian and
  point-mass data but is numerically `Θ(1/N)` for two-point data; no Lean statement.
* Translation invariance (point masses other than `δ_0`): a point mass at `x₀` is covered by (3)
  with `M = |x₀|²`, not by the exact formula (2).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped NNReal ENNReal

namespace FormalizeSampling.DiffusionDiscretization

open FormalizeSampling.Diffusion

variable {d : ℕ}

/-! ### The per-step sandwich -/

section Heat

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- **Entropy production is at least that of a Gaussian with the same second moment.** For a
probability `ρ` with finite second moment `M` and `0 < a ≤ b`:
`(d/2)(log(M + d b) - log(M + d a)) ≤ H(a) - H(b)`. Proof: `H' = -J/2` and Cramér–Rao
`J(s) ≥ d²/(M + d s)` make `s ↦ H(s) + (d/2) log(M + d s)` non-increasing. -/
theorem le_heatNegEntropy_sub_log (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    d / 2 * (Real.log (secondMoment ρ + d * b) - Real.log (secondMoment ρ + d * a)) ≤
      heatNegEntropy ρ a - heatNegEntropy ρ b := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have h1 := le_heatNegEntropy_sub ρ hmom ha hab
    have h2 : 0 ≤ (b - a) / 2 * heatFisherInfo ρ b :=
      mul_nonneg (by linarith) (heatFisherInfo_nonneg ρ (ha.trans_le hab))
    subst hd
    simp only [CharP.cast_eq_zero, zero_div, zero_mul]
    linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set M := secondMoment ρ with hM
  have hM0 : 0 ≤ M := secondMoment_nonneg ρ
  set g : ℝ → ℝ := fun s => heatNegEntropy ρ s + d / 2 * Real.log (M + d * s) with hg
  have hgd : ∀ s ∈ Set.Icc a b, HasDerivAt g
      (-(1 / 2) * heatFisherInfo ρ s + d / 2 * (d / (M + d * s))) s := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hpos : 0 < M + d * s := by positivity
    have h2 : HasDerivAt (fun s : ℝ => M + d * s) d s := by
      simpa using ((hasDerivAt_id s).const_mul (d : ℝ)).const_add M
    exact (hasDerivAt_heatNegEntropy ρ hmom hs0).add ((h2.log hpos.ne').const_mul _)
  have hanti : AntitoneOn g (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun s hs => (hgd s hs).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hgd s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs0 : 0 < s := ha.trans hs.1
      have hpos : 0 < M + d * s := by positivity
      rw [(hgd s (Set.Ioo_subset_Icc_self hs)).deriv]
      have hCR := sq_le_mul_heatFisherInfo ρ hmom hs0
      have : (d : ℝ) * (d / (M + d * s)) ≤ heatFisherInfo ρ s := by
        rw [← mul_div_assoc, div_le_iff₀ hpos]
        nlinarith
      linarith
  have := hanti (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab) hab
  simp only [hg] at this
  linarith

/-- **Per-step lower bound (every law).** For a probability `ρ` with finite second moment `M` and
`0 < a ≤ b`: `(d/2)(log(M + d b) - log(M + d a) - (b - a)/b) ≤ entropyStep ρ a b`
(`le_heatNegEntropy_sub_log` and `J(b) ≤ d/b`). -/
theorem le_entropyStep (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    d / 2 * (Real.log (secondMoment ρ + d * b) - Real.log (secondMoment ρ + d * a) -
      (b - a) / b) ≤ entropyStep ρ a b := by
  have h1 := le_heatNegEntropy_sub_log ρ hmom ha hab
  have h2 : (b - a) / 2 * heatFisherInfo ρ b ≤ (b - a) / 2 * (d / b) :=
    mul_le_mul_of_nonneg_left (heatFisherInfo_le ρ (ha.trans_le hab)) (by linarith)
  have e : (b - a) / 2 * ((d : ℝ) / b) = d / 2 * ((b - a) / b) := by ring
  unfold entropyStep
  nlinarith

/-- **Per-step upper bound (every law): a point mass is the worst case.** For a probability `ρ`
with finite second moment `M` and `0 < a ≤ b`:
`entropyStep ρ a b ≤ (d/2)(log(b/a) - d (b - a)/(M + d b))`
(`heatNegEntropy_sub_le_log` and Cramér–Rao `J(b) ≥ d²/(M + d b)`). -/
theorem entropyStep_le_log (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    entropyStep ρ a b ≤
      d / 2 * (Real.log (b / a) - d * (b - a) / (secondMoment ρ + d * b)) := by
  have hb : 0 < b := ha.trans_le hab
  have h1 := heatNegEntropy_sub_le_log ρ hmom ha hab
  have hP : 0 ≤ secondMoment ρ + d * b := by
    have := secondMoment_nonneg ρ; positivity
  have hJ : (d : ℝ) ^ 2 / (secondMoment ρ + d * b) ≤ heatFisherInfo ρ b :=
    div_le_of_le_mul₀ hP (heatFisherInfo_nonneg ρ hb) (by
      have := sq_le_mul_heatFisherInfo ρ hmom hb; linarith [mul_comm (heatFisherInfo ρ b)
        (secondMoment ρ + d * b)])
  have h2 : (b - a) / 2 * ((d : ℝ) ^ 2 / (secondMoment ρ + d * b)) ≤
      (b - a) / 2 * heatFisherInfo ρ b := mul_le_mul_of_nonneg_left hJ (by linarith)
  have e : (b - a) / 2 * ((d : ℝ) ^ 2 / (secondMoment ρ + d * b)) =
      d / 2 * (d * (b - a) / (secondMoment ρ + d * b)) := by ring
  unfold entropyStep
  nlinarith

end Heat

/-! ### The point mass at the origin -/

/-- The point mass at `0` has finite second moment. -/
theorem integrable_sumSq_dirac : Integrable (fun x : Fin d → ℝ => ∑ i, x i ^ 2)
    (Measure.dirac (0 : Fin d → ℝ)) :=
  integrable_dirac (by simp)

/-- The point mass at `0` has second moment `0`. -/
theorem secondMoment_dirac : secondMoment (Measure.dirac (0 : Fin d → ℝ)) = 0 := by
  simp [secondMoment, integral_dirac]

/-- **Exact step error for a point mass.** For `ρ = δ_0` and `0 < a ≤ b`:
`entropyStep δ_0 a b = (d/2)(log(b/a) - (b - a)/b)` (the sandwich `le_entropyStep`,
`entropyStep_le_log` closes at `M = 0`). -/
theorem entropyStep_dirac {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    entropyStep (Measure.dirac (0 : Fin d → ℝ)) a b =
      d / 2 * (Real.log (b / a) - (b - a) / b) := by
  have hb : 0 < b := ha.trans_le hab
  have h1 := le_entropyStep (Measure.dirac (0 : Fin d → ℝ)) integrable_sumSq_dirac ha hab
  have h2 := entropyStep_le_log (Measure.dirac (0 : Fin d → ℝ)) integrable_sumSq_dirac ha hab
  simp only [secondMoment_dirac, zero_add] at h1 h2
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [CharP.cast_eq_zero, zero_div, zero_mul] at h1 h2 ⊢
    linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.log_mul hdpos.ne' hb.ne', Real.log_mul hdpos.ne' ha.ne'] at h1
  rw [show (d : ℝ) * (b - a) / (d * b) = (b - a) / b by field_simp] at h2
  rw [Real.log_div hb.ne' ha.ne'] at h2 ⊢
  linarith


/-! ### Sums over a grid

The telescoping identity `sum_Ioc_sub_pred` is in `Samplers/DiffusionMain.lean`. -/

section Sums

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- **Universal lower bound on the discretisation sum (heat-flow coordinates).** For a
probability `ρ` with finite second moment `M`, `m ≤ N` and a grid with `0 < u_k` for
`m ≤ k ≤ N` and `u_{k-1} ≤ u_k` for `m < k ≤ N`:
`(d/2)(∑_{k=m+1}^N (log(u_k/u_{k-1}) - (u_k - u_{k-1})/u_k) - log(1 + M/(d u_m)))
  ≤ ∑_{k=m+1}^N entropyStep ρ u_{k-1} u_k`.
The first sum is exactly the value for a point mass at the origin (`entropyStep_dirac`); the
correction `log(1 + M/(d u_m))` does not depend on the number of steps. -/
theorem sum_entropyStep_ge (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {u : ℕ → ℝ}
    {m N : ℕ} (hmN : m ≤ N) (hpos : ∀ k ∈ Icc m N, 0 < u k)
    (hmono : ∀ k ∈ Ioc m N, u (k - 1) ≤ u k) :
    d / 2 * (∑ k ∈ Ioc m N, (Real.log (u k / u (k - 1)) - (u k - u (k - 1)) / u k) -
      Real.log (1 + secondMoment ρ / (d * u m))) ≤
      ∑ k ∈ Ioc m N, entropyStep ρ (u (k - 1)) (u k) := by
  have hk1 : ∀ k ∈ Ioc m N, 0 < u (k - 1) := fun k hk => by
    simp only [mem_Ioc] at hk; exact hpos _ (by simp only [mem_Icc]; omega)
  have hkk : ∀ k ∈ Ioc m N, 0 < u k := fun k hk => by
    simp only [mem_Ioc] at hk; exact hpos _ (by simp only [mem_Icc]; omega)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [CharP.cast_eq_zero, zero_div, zero_mul]
    exact Finset.sum_nonneg fun k hk => entropyStep_nonneg ρ hmom (hk1 k hk) (hmono k hk)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set M := secondMoment ρ with hM
  have hM0 : 0 ≤ M := secondMoment_nonneg ρ
  have hum : 0 < u m := hpos m (by simp only [mem_Icc]; omega)
  have huN : 0 < u N := hpos N (by simp only [mem_Icc]; omega)
  have hstep := Finset.sum_le_sum fun k hk => le_entropyStep ρ hmom (hk1 k hk) (hmono k hk)
  refine le_trans ?_ hstep
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : ∑ k ∈ Ioc m N, (Real.log (M + d * u k) - Real.log (M + d * u (k - 1)) -
      (u k - u (k - 1)) / u k) = (Real.log (M + d * u N) - Real.log (M + d * u m)) -
      ∑ k ∈ Ioc m N, (u k - u (k - 1)) / u k := by
    rw [Finset.sum_sub_distrib, sum_Ioc_sub_pred (fun k => Real.log (M + d * u k)) hmN]
  have e2 : ∑ k ∈ Ioc m N, (Real.log (u k / u (k - 1)) - (u k - u (k - 1)) / u k) =
      (Real.log (u N) - Real.log (u m)) - ∑ k ∈ Ioc m N, (u k - u (k - 1)) / u k := by
    rw [Finset.sum_sub_distrib, ← sum_Ioc_sub_pred (fun k => Real.log (u k)) hmN]
    congr 1
    exact sum_congr rfl fun k hk => Real.log_div (hkk k hk).ne' (hk1 k hk).ne'
  rw [e1, e2]
  have e3 : Real.log (1 + M / (d * u m)) =
      Real.log (M + d * u m) - Real.log d - Real.log (u m) := by
    rw [show 1 + M / (d * u m) = (M + d * u m) / (d * u m) by field_simp; ring,
      Real.log_div (by positivity) (by positivity), Real.log_mul hdpos.ne' hum.ne']
    ring
  have h4 : Real.log d + Real.log (u N) ≤ Real.log (M + d * u N) := by
    rw [← Real.log_mul hdpos.ne' huN.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  rw [e3]
  linarith

end Sums

/-- **Tangent-line (Jensen) inequality for `g(x) = x - 1 + e^{-x}`.** For a finite family
`x_i`, `i ∈ s`, with mean `c = (∑ x_i)/|s|`:
`|s| (c - 1 + e^{-c}) ≤ ∑_{i ∈ s} (x_i - 1 + e^{-x_i})`.
-/
theorem card_mul_expGap_le_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (#s : ℝ) * ((∑ i ∈ s, x i) / #s - 1 + Real.exp (-((∑ i ∈ s, x i) / #s))) ≤
      ∑ i ∈ s, (x i - 1 + Real.exp (-x i)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  set c := (∑ i ∈ s, x i) / #s with hc
  have key : ∀ i, c - 1 + Real.exp (-c) + (1 - Real.exp (-c)) * (x i - c) ≤
      x i - 1 + Real.exp (-x i) := by
    intro i
    have h1 := Real.add_one_le_exp (-(x i - c))
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-c)).le
    have e : Real.exp (-x i) = Real.exp (-c) * Real.exp (-(x i - c)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith
  have hz : ∑ i ∈ s, (x i - c) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hc]
    field_simp
    ring
  calc (#s : ℝ) * (c - 1 + Real.exp (-c))
      = ∑ i ∈ s, (c - 1 + Real.exp (-c) + (1 - Real.exp (-c)) * (x i - c)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hz, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => key i

/-! ### Statements about the reverse kernels of the DDPM sampler -/

section Kernels

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]

/-- **The discretisation sum as a real sum** (Theorem A of `DiffusionDiscretizationStep`):
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k
  = ofReal (∑_{k=2}^N entropyStep μ u_{k-1} u_k)`
for data with finite second moment, `t 0 = 0`, `t` strictly increasing. -/
theorem sum_lintegral_klDiv_revKernel_ddpm_eq (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) (N : ℕ) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) =
      ENNReal.ofReal (∑ k ∈ Ioc 1 N, entropyStep μ (heatTime t (k - 1)) (heatTime t k)) := by
  have hA : ∀ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
      (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) =
      ENNReal.ofReal (entropyStep μ (heatTime t (k - 1)) (heatTime t k)) := by
    intro k hk
    simp only [mem_Ioc] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [lintegral_klDiv_revKernel_ddpm_eq μ hμ h0 ht (by omega), Nat.add_sub_cancel]
    rfl
  rw [sum_congr rfl hA, ← ENNReal.ofReal_sum_of_nonneg fun k hk => by
    simp only [mem_Ioc] at hk
    exact entropyStep_nonneg μ hμ (heatTime_pos h0 ht (by omega))
      (heatTime_mono ht.monotone (by omega))]

/-- **Universal lower bound: the `O(1/N)` rate of `DiffusionMain` is the true order, up to a
term depending on the second moment.** For every
data law `μ` with finite second moment `M = ∫ |x|² dμ`, `t 0 = 0`, `t` strictly increasing and
`1 ≤ m ≤ N` (`u = heatTime t`):
`ofReal((d/2)(∑_{k=m+1}^N (log(u_k/u_{k-1}) - (u_k - u_{k-1})/u_k) - log(1 + M/(d u_m))))
  ≤ ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k(y)`.
Each summand `log ρ_k - 1 + 1/ρ_k` (`ρ_k = u_k/u_{k-1}`) is `≈ (ρ_k - 1)²/2`, so on a grid with
ratio `1 + κ` the right side is `≥ ≈ (dκ/4) log(u_N/u_m) - (d/2) log(1 + M/(d u_m))`. -/
theorem sum_lintegral_klDiv_revKernel_ddpm_ge_log (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ)
    {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t) {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ENNReal.ofReal (d / 2 * (∑ k ∈ Ioc m N, (Real.log (heatTime t k / heatTime t (k - 1)) -
        (heatTime t k - heatTime t (k - 1)) / heatTime t k) -
        Real.log (1 + secondMoment μ / (d * heatTime t m)))) ≤
      ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y)
        (Measure.pi fun i => gaussianReal (postMean μ t k y i) (ddpmVar t k)) ∂(fwdLaw μ t k) := by
  rw [sum_lintegral_klDiv_revKernel_ddpm_eq μ hμ h0 ht N]
  refine ENNReal.ofReal_le_ofReal ((sum_entropyStep_ge μ hμ hmN
    (fun k hk => heatTime_pos h0 ht (by simp only [mem_Icc] at hk; omega))
    (fun k hk => heatTime_mono ht.monotone (by omega))).trans ?_)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left hm) fun k hk _ => ?_
  simp only [mem_Ioc] at hk
  exact entropyStep_nonneg μ hμ (heatTime_pos h0 ht (by omega))
    (heatTime_mono ht.monotone (by omega))

end Kernels

/-- **Exact discretisation sum for a point mass.** For `μ = δ_0`, `t 0 = 0`, `t` strictly
increasing and every `N` (`u = heatTime t`):
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k
  = ofReal((d/2) ∑_{k=2}^N (log(u_k/u_{k-1}) - (u_k - u_{k-1})/u_k))`. -/
theorem sum_lintegral_klDiv_revKernel_ddpm_dirac {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) (N : ℕ) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel (Measure.dirac (0 : Fin d → ℝ)) t k y)
        (Measure.pi fun i => gaussianReal (postMean (Measure.dirac 0) t k y i) (ddpmVar t k))
        ∂(fwdLaw (Measure.dirac 0) t k) =
      ENNReal.ofReal (d / 2 * ∑ k ∈ Ioc 1 N, (Real.log (heatTime t k / heatTime t (k - 1)) -
        (heatTime t k - heatTime t (k - 1)) / heatTime t k)) := by
  rw [sum_lintegral_klDiv_revKernel_ddpm_eq _ integrable_sumSq_dirac h0 ht N, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_Ioc] at hk
  exact entropyStep_dirac (heatTime_pos h0 ht (by omega)) (heatTime_mono ht.monotone (by omega))

/-- **No grid beats the geometric one for a point mass.** For `μ = δ_0`, `t 0 = 0`, `t` strictly
increasing and `N ≥ 1` (`u = heatTime t`, `L = log(u_N/u_1)`, `n = N - 1` steps):
`ofReal((d/2) n (L/n - 1 + e^{-L/n})) ≤ ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k`.
Equality holds on the geometric grid (`sum_lintegral_klDiv_revKernel_geomGrid_dirac`). Since
`x - 1 + e^{-x} = x²/2 + O(x³)`, every grid with `N - 1` steps between `u_1` and `u_N` pays
`≈ d L²/(4 (N - 1))` (proof: the tangent-line inequality `card_mul_expGap_le_sum`). -/
theorem sum_lintegral_klDiv_revKernel_ddpm_dirac_ge {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) :
    ENNReal.ofReal (d / 2 * (((N - 1 : ℕ) : ℝ) *
        (Real.log (heatTime t N / heatTime t 1) / ((N - 1 : ℕ) : ℝ) - 1 +
          Real.exp (-(Real.log (heatTime t N / heatTime t 1) / ((N - 1 : ℕ) : ℝ)))))) ≤
      ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel (Measure.dirac (0 : Fin d → ℝ)) t k y)
        (Measure.pi fun i => gaussianReal (postMean (Measure.dirac 0) t k y i) (ddpmVar t k))
        ∂(fwdLaw (Measure.dirac 0) t k) := by
  rw [sum_lintegral_klDiv_revKernel_ddpm_dirac h0 ht N]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  set x : ℕ → ℝ := fun k => Real.log (heatTime t k / heatTime t (k - 1)) with hx
  have hpos : ∀ k ∈ Ioc 1 N, 0 < heatTime t (k - 1) ∧ 0 < heatTime t k := fun k hk => by
    simp only [mem_Ioc] at hk
    exact ⟨heatTime_pos h0 ht (by omega), heatTime_pos h0 ht (by omega)⟩
  have hsum : ∑ k ∈ Ioc 1 N, x k = Real.log (heatTime t N / heatTime t 1) := by
    rw [Real.log_div (heatTime_pos h0 ht hN).ne' (heatTime_pos h0 ht le_rfl).ne',
      ← sum_Ioc_sub_pred (fun k => Real.log (heatTime t k)) hN]
    exact sum_congr rfl fun k hk => Real.log_div (hpos k hk).2.ne' (hpos k hk).1.ne'
  have hterm : ∀ k ∈ Ioc 1 N, Real.log (heatTime t k / heatTime t (k - 1)) -
      (heatTime t k - heatTime t (k - 1)) / heatTime t k = x k - 1 + Real.exp (-x k) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hpos k hk
    simp only [hx]
    rw [Real.exp_neg, Real.exp_log (div_pos h2 h1), inv_div]
    field_simp
    ring
  have hcard : (#(Ioc 1 N) : ℝ) = ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]
  have h := card_mul_expGap_le_sum (Ioc 1 N) x
  rw [hcard, hsum] at h
  rw [sum_congr rfl hterm]
  exact h

/-! ### The geometric grid -/

/-- On the geometric grid, each step has `u_k/u_{k-1} = r`, so the point-mass summand is
`log r - 1 + 1/r` (`2 ≤ k`). -/
theorem geomGrid_term {u1 r : ℝ} (hu1 : 0 < u1) (hr : 0 < r) {k : ℕ} (hk : 2 ≤ k) :
    Real.log (heatTime (geomGrid u1 r) k / heatTime (geomGrid u1 r) (k - 1)) -
        (heatTime (geomGrid u1 r) k - heatTime (geomGrid u1 r) (k - 1)) /
          heatTime (geomGrid u1 r) k = Real.log r - 1 + 1 / r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [heatTime_geomGrid hu1 hr (by omega), heatTime_geomGrid hu1 hr (by omega),
    show j + 2 - 1 - 1 = j by omega, show j + 2 - 1 = j + 1 by omega, pow_succ]
  have hp : 0 < u1 * r ^ j := by positivity
  rw [show u1 * (r ^ j * r) / (u1 * r ^ j) = r by field_simp]
  field_simp
  ring

/-- **Exact value on the geometric grid for a point mass.** For `μ = δ_0`, `u_1 > 0`, `r > 1`:
`∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k = ofReal((d/2)(N-1)(log r - 1 + 1/r))`
on `t = geomGrid u_1 r`. -/
theorem sum_lintegral_klDiv_revKernel_geomGrid_dirac {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r)
    (N : ℕ) :
    ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel (Measure.dirac (0 : Fin d → ℝ)) (geomGrid u1 r) k y)
        (Measure.pi fun i => gaussianReal (postMean (Measure.dirac 0) (geomGrid u1 r) k y i)
          (ddpmVar (geomGrid u1 r) k)) ∂(fwdLaw (Measure.dirac 0) (geomGrid u1 r) k) =
      ENNReal.ofReal (d / 2 * (((N - 1 : ℕ) : ℝ) * (Real.log r - 1 + 1 / r))) := by
  rw [sum_lintegral_klDiv_revKernel_ddpm_dirac (geomGrid_zero u1 r) (geomGrid_strictMono hu1 hr),
    sum_congr rfl fun k hk => geomGrid_term hu1 (zero_lt_one.trans hr)
      (by simp only [mem_Ioc] at hk; omega), Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

/-- **Universal lower bound on the geometric grid.** For data with finite second moment `M`,
`u_1 > 0`, `r > 1` and `1 ≤ m ≤ N`, on `t = geomGrid u_1 r`:
`ofReal((d/2)((N - m)(log r - 1 + 1/r) - log(1 + M/(d u_1 r^{m-1}))))
  ≤ ∑_{k=2}^N ∫ KL(R_k y ‖ N(m*_k(y), (β_k/α_k²) I)) dp_k`. -/
theorem sum_lintegral_klDiv_revKernel_geomGrid_ge (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {u1 r : ℝ}
    (hu1 : 0 < u1) (hr : 1 < r) {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ENNReal.ofReal (d / 2 * (((N - m : ℕ) : ℝ) * (Real.log r - 1 + 1 / r) -
        Real.log (1 + secondMoment μ / (d * (u1 * r ^ (m - 1)))))) ≤
      ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ (geomGrid u1 r) k y)
        (Measure.pi fun i => gaussianReal (postMean μ (geomGrid u1 r) k y i)
          (ddpmVar (geomGrid u1 r) k)) ∂(fwdLaw μ (geomGrid u1 r) k) := by
  have h := sum_lintegral_klDiv_revKernel_ddpm_ge_log μ hμ (geomGrid_zero u1 r)
    (geomGrid_strictMono hu1 hr) hm hmN
  rwa [sum_congr rfl fun k hk => geomGrid_term hu1 (zero_lt_one.trans hr)
      (by simp only [mem_Ioc] at hk; omega), Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
    heatTime_geomGrid hu1 (zero_lt_one.trans hr) hm] at h

/-- **The `DiffusionMain` bound is tight within a factor `2r` (point mass, geometric grid).**
For `u_1 > 0`, `r > 1`, `N ≥ 1`, with `D_N` the discretisation sum of `δ_0` on
`t = geomGrid u_1 r`:
`ofReal((r - 1)(d/2)(1 + (N - 1) log r)) ≤ ofReal(2r) · D_N + ofReal((r - 1) d/2)`.
The left side is the discretisation term of `klDiv_output_le_geomGrid`. Proof: the exact value
`sum_lintegral_klDiv_revKernel_geomGrid_dirac` and `(r - 1) log r ≤ 2r (log r - 1 + 1/r)`, which
is `log r ≥ 2(r - 1)/(r + 1)`. -/
theorem discBound_geomGrid_le_dirac {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r) (N : ℕ) :
    ENNReal.ofReal ((r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r)) ≤
      ENNReal.ofReal (2 * r) *
        (∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel (Measure.dirac (0 : Fin d → ℝ))
          (geomGrid u1 r) k y)
          (Measure.pi fun i => gaussianReal (postMean (Measure.dirac 0) (geomGrid u1 r) k y i)
            (ddpmVar (geomGrid u1 r) k)) ∂(fwdLaw (Measure.dirac 0) (geomGrid u1 r) k)) +
        ENNReal.ofReal ((r - 1) * d / 2) := by
  rw [sum_lintegral_klDiv_revKernel_geomGrid_dirac hu1 hr N]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hlog := two_mul_sub_div_le_log hr.le
  have hg : 0 ≤ Real.log r - 1 + 1 / r := by
    have := Real.one_sub_inv_le_log_of_pos hr0
    rw [one_div]; linarith
  have hkey : (r - 1) * Real.log r ≤ 2 * r * (Real.log r - 1 + 1 / r) := by
    have h1 : 2 * (r - 1) ≤ (r + 1) * Real.log r := by
      rw [div_le_iff₀ (by linarith)] at hlog
      linarith
    have e : 2 * r * (Real.log r - 1 + 1 / r) = 2 * r * Real.log r - 2 * (r - 1) := by
      field_simp; ring
    rw [e]; nlinarith
  have hn : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity)
    (by have : 0 ≤ r - 1 := by linarith
        positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ((N - 1 : ℕ) : ℝ) * d * ((r - 1) * Real.log r) ≤
      ((N - 1 : ℕ) : ℝ) * d * (2 * r * (Real.log r - 1 + 1 / r)) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  nlinarith

end FormalizeSampling.DiffusionDiscretization
