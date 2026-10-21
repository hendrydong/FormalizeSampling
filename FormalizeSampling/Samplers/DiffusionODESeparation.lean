module

public import Mathlib.MeasureTheory.Function.Floor
public import FormalizeSampling.Samplers.DiffusionMain

/-!
# Deterministic versus stochastic reverse samplers under an `L²` score error (separation)

Status: **Verified** (a separation result: it refutes "an `L²(p_k)`-accurate score suffices for
the deterministic sampler", in the setting where it does suffice for DDPM).

Setting of `Samplers/DiffusionSetup.lean`: data law `μ` on `Fin d → ℝ` (`d ≥ 1`) with finite
second moment, grid `0 = t_0 < t_1 < ⋯ < t_N` (`N ≥ 2`), forward marginals `p_k = fwdLaw μ t k`,
true scores `∇ log p_k = score (fwdDensity μ t k)`. A *deterministic* reverse sampler is the
algorithm `algLaw 0 m` of the same file with zero reverse variance (each Gaussian step
`N(m_k(y), 0) = δ_{m_k(y)}` is a Dirac step), with a mean map that is affine in the learned score:
`m_k(y) = A_k(y) + b_k s_k(y)` (`detMean`). This covers DDIM-type and exponential-integrator
discretisations of the probability-flow ODE (example: `pfMean`, `b_k = α_k⁻¹ - 1`) and the Euler
discretisation; only `b_2 ≠ 0` is used.

## The construction (Li–Wei–Chen–Chi)

Following the example of G. Li, Y. Wei, Y. Chen, Y. Chi, *Towards faster non-asymptotic
convergence for diffusion-based generative models* (arXiv:2306.09251, ICLR 2024, §3.2,
"Insufficiency of the score estimation error assumption alone"; stated there for `N(0,1)` data),
keep the true score at every step except the last one `k = 2`, where
`s_2 = ∇ log p_2 - (ε/(d+1)) fract(z / h)` coordinatewise, `z = A_2(y) + b_2 ∇ log p_2(y)` being
the exact deterministic update and `h = b_2 ε / (d + 1)` (`latticeScore`). Then the deterministic
update becomes `h ⌊z / h⌋`, so the output law `q_1` lives on the lattice `(hℤ)^d`, a countable
(hence Lebesgue-null) set, whereas `p_1` has a Lebesgue density.

## Main results

* `sum_sq_latticeScore_sub_le`: uniform accuracy, `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all
  `k`, `y`; hence `integral_sq_latticeScore_sub_le` (`L²(p_k)` error `≤ ε²`) and
  `scoreErr_latticeScore_le` (the DDPM score term is `≤ (β_2/2) ε²`).
* `tvSup_detOutput_latticeScore_eq_one`: the deterministic sampler driven by this score has
  `TV(p_1, q_1^det) = 1`.
* `tvSup_ddpm_latticeScore_le`: DDPM driven by the **same** score has
  `TV(p_1, q_1^DDPM) ≤ √((I + (κ d / 2)(1 + log(u_N/u_1)) + (β_2/2) ε²) / 2)` (from
  `DiffusionDiscretization.tvSup_output_le_ddpm_grid`); `tvSup_ddpm_latticeScore_le_geomGrid`
  is the geometric-grid form. The first two terms are those of the exact-score bound, which can
  be made arbitrarily small (`DiffusionDiscretization.exists_tvSup_output_le`).
* `ddpm_ddim_separation`: the two statements combined, for every `ε > 0`.
* `pf_ddpm_separation_geomGrid`: the same for the exponential-integrator probability-flow step
  `pfMean` (`A_k = α_k⁻¹ id`, `b_k = α_k⁻¹ - 1`, `pfCoeff_two_ne_zero`) on the geometric grid.

## Not proved here

* The learned score is discontinuous (it uses `Int.fract`), so it violates the Jacobian-error /
  Lipschitz assumptions under which deterministic samplers are known to converge. A version
  whose score error is an analytic, globally Lipschitz function of the exact update, with
  `TV ≥ 1 - η` instead of `= 1`, is DF-7 (`Samplers/DiffusionODESmooth.lean`); smoothness of the
  learned score in `y` itself is not formalised.
* No Wasserstein statement here. Pointwise, the perturbed update is within `√d |h|` of the
  exact-score update, so the output is close in transport distance to the exact-score
  deterministic output; closeness to `p_1` would also need the discretisation error of that
  sampler. Couplings of this kind are DF-9 (`Samplers/DiffusionODELipschitz.lean`).
* The geometric-grid corollary is not combined with `DiffusionDiscretization.exists_geomGrid_params`
  into an existence statement (that lemma provides `N ≥ 1`, whereas the construction needs
  `N ≥ 2`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionODESeparation

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionDiscretization

variable {d : ℕ}

/-! ### Deterministic samplers with a score-affine update -/

/-- The mean map of a deterministic reverse step that is affine in the learned score:
`m_k(y) = A_k(y) + b_k s_k(y)`. Used with zero reverse variance, `algLaw 0 (detMean A b s)`. -/
noncomputable def detMean (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ)
    (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (k : ℕ) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => A k y i + b k * s k y i

/-- `detMean A b s k` is measurable when `A k` and `s k` are. -/
theorem measurable_detMean {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k))
    (b : ℕ → ℝ) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hs : ∀ k, Measurable (s k)) (k : ℕ) :
    Measurable (detMean A b s k) :=
  Measurable.of_eval fun i => ((measurable_pi_apply i).comp (hA k)).add
    (measurable_const.mul ((measurable_pi_apply i).comp (hs k)))

/-- The zero reverse variance (`σ_k² = 0` for all `k`). -/
def zeroVar : ℕ → ℝ≥0 := fun _ => 0

/-- The linear part `A_k(y) = α_k⁻¹ y` of the exponential-integrator step. -/
noncomputable def pfLin (t : ℕ → ℝ) (k : ℕ) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (fwdScale t k)⁻¹ * y i

/-- The score coefficient `b_k = α_k⁻¹ - 1` of the exponential-integrator step. -/
noncomputable def pfCoeff (t : ℕ → ℝ) (k : ℕ) : ℝ := (fwdScale t k)⁻¹ - 1

/-- The linear part of the exponential-integrator step is measurable. -/
theorem measurable_pfLin (t : ℕ → ℝ) (k : ℕ) : Measurable (pfLin (d := d) t k) :=
  Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)

/-- **Example: exponential-integrator step of the probability-flow ODE.** For the OU forward
process the reverse probability-flow ODE is `dy/dτ = y + ∇ log p(y)`; freezing the score over
`[t_{k-1}, t_k]` and integrating the linear part exactly gives
`m_k(y) = α_k⁻¹ y + (α_k⁻¹ - 1) s_k(y)` (`α_k = e^{-(t_k - t_{k-1})}`). -/
noncomputable def pfMean (t : ℕ → ℝ) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (k : ℕ)
    (y : Fin d → ℝ) : Fin d → ℝ :=
  detMean (pfLin t) (pfCoeff t) s k y

/-! ### The lattice and the perturbed score -/

/-- The lattice `(hℤ)^d = {x | ∀ i, xᵢ ∈ hℤ}`. -/
def lattice (d : ℕ) (h : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.range fun n : ℤ => h * n}

/-- The lattice is countable. -/
theorem countable_lattice (h : ℝ) : (lattice d h).Countable :=
  Set.countable_pi fun _ => Set.countable_range _

/-- The lattice is measurable. -/
theorem measurableSet_lattice (h : ℝ) : MeasurableSet (lattice d h) :=
  (countable_lattice h).measurableSet

/-- The lattice spacing `h = b_2 ε / (d + 1)`. -/
noncomputable def latticeStep (d : ℕ) (b : ℕ → ℝ) (ε : ℝ) : ℝ := b 2 * ε / (d + 1)

/-- **The Li–Wei–Chen–Chi learned score.** Equal to the true score `∇ log p_k` for `k ≠ 2`; at
`k = 2`, `s_2(y)ᵢ = ∂ᵢ log p_2(y) - (ε / (d + 1)) fract(z_i / h)` with
`z = A_2(y) + b_2 ∇ log p_2(y)` the exact deterministic update and `h = latticeStep d b ε`. -/
noncomputable def latticeScore (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (ε : ℝ) :
    ℕ → (Fin d → ℝ) → Fin d → ℝ :=
  fun k y i => exactScore μ t k y i -
    if k = 2 then ε / (d + 1) *
      Int.fract (detMean A b (exactScore μ t) 2 y i / latticeStep d b ε) else 0

/-- The lattice score is measurable when `A` is. -/
theorem measurable_latticeScore (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) (ε : ℝ)
    (k : ℕ) : Measurable (latticeScore μ t A b ε k) := by
  refine Measurable.of_eval fun i => ?_
  refine ((measurable_pi_apply i).comp (measurable_exactScore μ t k)).sub ?_
  split_ifs
  · exact measurable_const.mul (measurable_fract.comp
      (((measurable_pi_apply i).comp
        (measurable_detMean hA b (measurable_exactScore μ t) 2)).div_const _))
  · exact measurable_const

/-- The lattice score differs from the true score only at `k = 2`, by `-(ε/(d+1)) fract(·)`. -/
theorem latticeScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (ε : ℝ) (k : ℕ) (y : Fin d → ℝ)
    (i : Fin d) :
    latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i =
      -(if k = 2 then ε / (d + 1) *
        Int.fract (detMean A b (exactScore μ t) 2 y i / latticeStep d b ε) else 0) := by
  simp only [latticeScore, exactScore]
  ring

/-- **Uniform accuracy.** For `ε ≥ 0`, every `k` and every `y`:
`∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²`. -/
theorem sum_sq_latticeScore_sub_le (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ)
    (y : Fin d → ℝ) :
    ∑ i, (latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ ε ^ 2 := by
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hterm : ∀ i, (latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i) ^ 2 ≤
      (ε / (d + 1)) ^ 2 := by
    intro i
    rw [latticeScore_sub, neg_sq]
    split_ifs
    · set f := Int.fract (detMean A b (exactScore μ t) 2 y i / latticeStep d b ε)
      have hf0 : 0 ≤ f := Int.fract_nonneg _
      have hf1 : f < 1 := Int.fract_lt_one _
      have hc : 0 ≤ ε / (d + 1) := div_nonneg hε hd.le
      have h1 : ε / (d + 1) * f ≤ ε / (d + 1) := mul_le_of_le_one_right hc hf1.le
      have h0 : 0 ≤ ε / (d + 1) * f := mul_nonneg hc hf0
      nlinarith
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  refine (sum_le_sum fun i _ => hterm i).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have : (d : ℝ) ≤ (d + 1) ^ 2 := by nlinarith
  nlinarith [sq_nonneg ε]

/-- At every `k ≠ 2` the lattice score is exact. -/
theorem sum_sq_latticeScore_sub_of_ne (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) (ε : ℝ) {k : ℕ} (hk : k ≠ 2)
    (y : Fin d → ℝ) :
    ∑ i, (latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i) ^ 2 = 0 := by
  simp [latticeScore_sub, hk]

/-- The score-error integrand of the lattice score is measurable. -/
theorem measurable_sq_latticeScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) (ε : ℝ)
    (k : ℕ) : Measurable fun y =>
      ∑ i, (latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i) ^ 2 :=
  Finset.measurable_sum _ fun i _ =>
    (((measurable_pi_apply i).comp (measurable_latticeScore μ t hA b ε k)).sub
      ((measurable_pi_apply i).comp (measurable_exactScore μ t k))).pow_const 2

/-- The score-error integrand is `ν`-integrable for every probability law `ν` (it is bounded by
`ε²`); in particular hypothesis `hsint` of the DDPM theorems holds. -/
theorem integrable_sq_latticeScore_sub (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (k : ℕ) (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    Integrable (fun y =>
      ∑ i, (latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i) ^ 2) ν := by
  refine Integrable.of_bound
    (measurable_sq_latticeScore_sub μ t hA b ε k).aestronglyMeasurable (ε ^ 2)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (sum_nonneg fun i _ => sq_nonneg _)]
  exact sum_sq_latticeScore_sub_le μ t A b hε k y

/-- **`L²(p_k)` accuracy.** For data `μ` (probability law), `ε ≥ 0` and every `k`:
`∫ ∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² dp_k(y) ≤ ε²`. -/
theorem integral_sq_latticeScore_sub_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ → ℝ) (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (k : ℕ) :
    ∫ y, ∑ i, (latticeScore μ t A b ε k y i - score (fwdDensity μ t k) y i) ^ 2
      ∂(fwdLaw μ t k) ≤ ε ^ 2 := by
  calc _ ≤ ∫ _y, ε ^ 2 ∂(fwdLaw μ t k) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
          sum_nonneg fun i _ => sq_nonneg _) (integrable_const _)
          (Filter.Eventually.of_forall fun y => sum_sq_latticeScore_sub_le μ t A b hε k y)
    _ = ε ^ 2 := by simp

/-- **The DDPM score term.** For `N ≥ 2`, `t_1 ≤ t_2` and `ε ≥ 0`:
`scoreErr μ t s N = ∑_{k=2}^N (β_k/2) ∫ |s_k - ∇ log p_k|² dp_k ≤ (β_2 / 2) ε²` (only step `2`
contributes). -/
theorem scoreErr_latticeScore_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (ht : t 1 ≤ t 2) (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N) :
    scoreErr μ t (latticeScore μ t A b ε) N ≤ fwdVar t 2 / 2 * ε ^ 2 := by
  unfold scoreErr scoreErrW
  rw [sum_eq_single_of_mem 2 (by simp; omega) fun k _ hk => by
    simp [sum_sq_latticeScore_sub_of_ne μ t A b ε hk]]
  have hβ : 0 ≤ fwdVar t 2 := by
    have h1 : fwdScale t 2 ≤ 1 := by
      unfold fwdScale; exact Real.exp_le_one_iff.2 (by norm_num; linarith)
    have h0 : 0 < fwdScale t 2 := Real.exp_pos _
    unfold fwdVar; nlinarith
  exact mul_le_mul_of_nonneg_left (integral_sq_latticeScore_sub_le μ t A b hε 2)
    (by positivity)

/-! ### The deterministic output lives on the lattice -/

/-- **The perturbed deterministic update is lattice-valued.** If `b_2 ≠ 0` and `ε ≠ 0`, then
`A_2(y) + b_2 s_2(y) = h ⌊z / h⌋ ∈ (hℤ)^d` for every `y`. -/
theorem detMean_latticeScore_mem (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) {b : ℕ → ℝ} (hb : b 2 ≠ 0) {ε : ℝ} (hε : ε ≠ 0)
    (y : Fin d → ℝ) :
    detMean A b (latticeScore μ t A b ε) 2 y ∈ lattice d (latticeStep d b ε) := by
  intro i
  set z := detMean A b (exactScore μ t) 2 y i
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  have hh : latticeStep d b ε ≠ 0 := div_ne_zero (mul_ne_zero hb hε) hd
  have hz : detMean A b (latticeScore μ t A b ε) 2 y i =
      z - b 2 * (ε / (d + 1)) * Int.fract (z / latticeStep d b ε) := by
    simp only [detMean, latticeScore, z, ↓reduceIte]
    ring
  have hc : b 2 * (ε / (d + 1)) = latticeStep d b ε := by unfold latticeStep; ring
  refine ⟨⌊z / latticeStep d b ε⌋, ?_⟩
  change latticeStep d b ε * (⌊z / latticeStep d b ε⌋ : ℝ) = _
  rw [hz, hc, ← Int.self_sub_fract]
  field_simp

/-- A deterministic step `y ↦ δ_{m(y)}` with `m` lattice-valued puts no mass off the lattice. -/
theorem gaussKernelPi_zero_compl_lattice {m : (Fin d → ℝ) → Fin d → ℝ} (hm : Measurable m)
    {h : ℝ} (hmem : ∀ y, m y ∈ lattice d h) (y : Fin d → ℝ) :
    gaussKernelPi 0 m hm y (lattice d h)ᶜ = 0 := by
  rw [gaussKernelPi_apply]
  simp_rw [gaussianReal_zero_var]
  have hsub : (lattice d h)ᶜ ⊆ ⋃ i, Function.eval i ⁻¹'
      (Set.range fun n : ℤ => h * n)ᶜ := by
    intro x hx
    simp only [lattice, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine Measure.pi_eval_preimage_null _ ?_
  rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hmem y i)]

/-- **The deterministic output is carried by the lattice.** For `N ≥ 2`, `b_2 ≠ 0`, `ε ≠ 0`
and measurable `A`, the output `q_1 = algLaw 0 (detMean A b s) N 1` of the deterministic
sampler driven by the lattice score gives the complement of `(hℤ)^d` measure `0`. -/
theorem detOutput_compl_lattice (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ}
    (hb : b 2 ≠ 0) {ε : ℝ} (hε : ε ≠ 0) {N : ℕ} (hN : 2 ≤ N) :
    algLaw zeroVar (detMean A b (latticeScore μ t A b ε))
        (measurable_detMean hA b (measurable_latticeScore μ t hA b ε)) N 1
        (lattice d (latticeStep d b ε))ᶜ = 0 := by
  rw [algLaw_of_lt _ _ _ (by omega : 1 < N),
    Measure.bind_apply (measurableSet_lattice _).compl (Kernel.aemeasurable _)]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y => ?_)
  exact gaussKernelPi_zero_compl_lattice _
    (fun y => detMean_latticeScore_mem μ t A hb hε y) y

/-- For `d ≥ 1` and `t_0 < t_1`, the smoothed data law `p_1` (which has a Lebesgue density)
gives every lattice measure `0`. -/
theorem fwdLaw_one_lattice (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ}
    (ht : t 0 < t 1) (hd : 0 < d) (h : ℝ) : fwdLaw μ t 1 (lattice d h) = 0 := by
  rw [fwdLaw_eq_withDensity μ (k := 0) ht]
  refine withDensity_absolutelyContinuous _ _ ?_
  have hsub : lattice d h ⊆ Function.eval (⟨0, hd⟩ : Fin d) ⁻¹'
      (Set.range fun n : ℤ => h * n) := fun x hx => hx _
  refine measure_mono_null hsub ?_
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null _ ((Set.countable_range _).measure_zero _)

/-! ### The separation -/

/-- **The deterministic sampler fails in TV.** Data `μ` (probability law), `d ≥ 1`,
`t_0 < t_1`, `N ≥ 2`, measurable `A`, `b_2 ≠ 0`, `ε ≠ 0`: the deterministic sampler
`algLaw 0 (detMean A b s)` driven by the lattice score `s = latticeScore μ t A b ε` satisfies
`TV(p_1, q_1) = 1`. -/
theorem tvSup_detOutput_latticeScore_eq_one (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    {t : ℕ → ℝ} (ht : t 0 < t 1) (hd : 0 < d) {A : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ} (hb : b 2 ≠ 0) {ε : ℝ} (hε : ε ≠ 0) {N : ℕ}
    (hN : 2 ≤ N) :
    TotalVariation.tvSup (fwdLaw μ t 1)
      (algLaw zeroVar (detMean A b (latticeScore μ t A b ε))
        (measurable_detMean hA b (measurable_latticeScore μ t hA b ε)) N 1) = 1 := by
  set q := algLaw zeroVar (detMean A b (latticeScore μ t A b ε))
    (measurable_detMean hA b (measurable_latticeScore μ t hA b ε)) N 1
  set L := lattice d (latticeStep d b ε)
  have hL : MeasurableSet L := measurableSet_lattice _
  have hp : fwdLaw μ t 1 Lᶜ = 1 :=
    (prob_compl_eq_one_iff hL).2 (fwdLaw_one_lattice μ ht hd _)
  have hq : q Lᶜ = 0 := detOutput_compl_lattice μ t hA hb hε hN
  refine le_antisymm (TotalVariation.tvSup_le_one _ _) ?_
  have h := TotalVariation.abs_measureReal_sub_le_tvSup (μ := fwdLaw μ t 1) (ν := q) hL.compl
  rw [measureReal_def, measureReal_def, hp, hq] at h
  simpa using h

/-- **DDPM with the same score.** Under the hypotheses of `tvSup_output_le_ddpm_grid` (data
with finite second moment, `t 0 = 0`, `t` strictly increasing, grid ratio `κ`) and `N ≥ 2`,
`ε ≥ 0`, measurable `A`: DDPM driven by the lattice score satisfies
`TV(p_1, q_1^DDPM) ≤ √((I + (κ d / 2)(1 + log(u_N/u_1)) + (β_2/2) ε²) / 2)`, `I = initBound`. -/
theorem tvSup_ddpm_latticeScore_le (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {t : ℕ → ℝ} (h0 : t 0 = 0) (ht : StrictMono t)
    {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 2 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw (ddpmVar t) (scoreMean t (latticeScore μ t A b ε))
          (measurable_scoreMean t (measurable_latticeScore μ t hA b ε)) N 1) ≤
      Real.sqrt ((initBound μ t N + κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) +
        fwdVar t 2 / 2 * ε ^ 2) / 2) := by
  refine (tvSup_output_le_ddpm_grid μ hμ h0 ht hκ (by omega) hgrid _
    (measurable_latticeScore μ t hA b ε)
    (fun k _ => integrable_sq_latticeScore_sub μ t hA b hε k _)).trans ?_
  gcongr
  exact scoreErr_latticeScore_le μ (ht.monotone (by norm_num)) A b hε hN

/-- **DDPM with the same score, geometric grid.** For data with finite second moment,
`u_1 > 0`, `r > 1`, `N ≥ 2`, `ε ≥ 0`, measurable `A`, on `t = geomGrid u_1 r`:
`TV(p_1, q_1^DDPM) ≤ √((I + (r - 1) d / 2 (1 + (N - 1) log r) + (β_2/2) ε²) / 2)`. -/
theorem tvSup_ddpm_latticeScore_le_geomGrid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) {u1 r : ℝ} (hu1 : 0 < u1) (hr : 1 < r)
    {N : ℕ} (hN : 2 ≤ N) {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k))
    (b : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r)) (scoreMean (geomGrid u1 r)
          (latticeScore μ (geomGrid u1 r) A b ε))
          (measurable_scoreMean _ (measurable_latticeScore μ _ hA b ε)) N 1) ≤
      Real.sqrt ((initBound μ (geomGrid u1 r) N +
        (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
        fwdVar (geomGrid u1 r) 2 / 2 * ε ^ 2) / 2) := by
  refine (tvSup_output_le_geomGrid μ hμ hu1 hr (by omega) _
    (measurable_latticeScore μ _ hA b ε)
    (fun k _ => integrable_sq_latticeScore_sub μ _ hA b hε k _)).trans ?_
  gcongr
  exact scoreErr_latticeScore_le μ ((geomGrid_strictMono hu1 hr).monotone (by norm_num)) A b
    hε hN

/-- **Separation theorem (DDPM vs deterministic sampler, same learned score).** Let `μ` be a
probability law on `Fin d → ℝ`, `d ≥ 1`, with finite second moment; `t 0 = 0`, `t` strictly
increasing, `N ≥ 2`, grid ratio `κ ≥ 0` as in `tvSup_output_le_ddpm_grid`; and let
`m_k(y) = A_k(y) + b_k s_k(y)` be any deterministic score-affine update with measurable `A` and
`b_2 ≠ 0`. For every `ε > 0` there is a measurable learned score `s` such that

1. `s` is uniformly `ε`-accurate: `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y`;
2. it is `ε`-accurate in `L²(p_k)`: `∫ ∑ᵢ (s_k - ∂ᵢ log p_k)² dp_k ≤ ε²` for all `k`;
3. the deterministic sampler `algLaw 0 (detMean A b s)` has `TV(p_1, q_1) = 1`;
4. DDPM with the same `s` has
   `TV(p_1, q_1) ≤ √((I + (κ d / 2)(1 + log(u_N/u_1)) + (β_2/2) ε²) / 2)`.

The construction is that of Li–Wei–Chen–Chi (arXiv:2306.09251, §3.2). -/
theorem ddpm_ddim_separation (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (hd : 0 < d) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 2 ≤ N)
    (hgrid : ∀ k, 1 ≤ k → k < N → heatTime t (k + 1) - heatTime t k ≤ κ * heatTime t k)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ}
    (hb : b 2 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)),
      (∀ k y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ ε ^ 2) ∧
      (∀ k, ∫ y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ∂(fwdLaw μ t k) ≤
        ε ^ 2) ∧
      TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw zeroVar (detMean A b s) (measurable_detMean hA b hs) N 1) = 1 ∧
      TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw (ddpmVar t) (scoreMean t s) (measurable_scoreMean t hs) N 1) ≤
        Real.sqrt ((initBound μ t N +
          κ * d / 2 * (1 + Real.log (heatTime t N / heatTime t 1)) +
          fwdVar t 2 / 2 * ε ^ 2) / 2) :=
  ⟨latticeScore μ t A b ε, measurable_latticeScore μ t hA b ε,
    sum_sq_latticeScore_sub_le μ t A b hε.le,
    integral_sq_latticeScore_sub_le μ t A b hε.le,
    tvSup_detOutput_latticeScore_eq_one μ (h0 ▸ ht zero_lt_one) hd hA hb hε.ne' hN,
    tvSup_ddpm_latticeScore_le μ hμ h0 ht hκ hN hgrid hA b hε.le⟩

/-- For `t_1 < t_2` the exponential-integrator coefficient `b_2 = α_2⁻¹ - 1` of `pfMean` is
nonzero. -/
theorem pfCoeff_two_ne_zero {t : ℕ → ℝ} (ht : t 1 < t 2) : pfCoeff t 2 ≠ 0 := by
  unfold pfCoeff
  have h : fwdScale t 2 < 1 := by
    have := Real.exp_lt_exp.2 (show -(t 2 - t 1) < 0 by linarith)
    simpa [fwdScale] using this
  have h0 : 0 < fwdScale t 2 := Real.exp_pos _
  have : 1 < (fwdScale t 2)⁻¹ := (one_lt_inv₀ h0).2 h
  linarith

/-- **Example: the probability-flow ODE (exponential integrator) on the geometric grid.** Data
with finite second moment, `d ≥ 1`, `u_1 > 0`, `r > 1`, `N ≥ 2`, `ε > 0`: there is a measurable
learned score, uniformly `ε`-accurate, such that the deterministic sampler with update
`pfMean` has `TV(p_1, q_1) = 1`, while DDPM with the same score has
`TV(p_1, q_1) ≤ √((I + (r - 1) d / 2 (1 + (N - 1) log r) + (β_2/2) ε²) / 2)`. -/
theorem pf_ddpm_separation_geomGrid (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (hd : 0 < d) {u1 r : ℝ} (hu1 : 0 < u1)
    (hr : 1 < r) {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k)),
      (∀ k y, ∑ i, (s k y i - score (fwdDensity μ (geomGrid u1 r) k) y i) ^ 2 ≤ ε ^ 2) ∧
      TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw zeroVar (pfMean (geomGrid u1 r) s)
          (measurable_detMean (measurable_pfLin _) _ hs) N 1) = 1 ∧
      TotalVariation.tvSup (fwdLaw μ (geomGrid u1 r) 1)
        (algLaw (ddpmVar (geomGrid u1 r)) (scoreMean (geomGrid u1 r) s)
          (measurable_scoreMean _ hs) N 1) ≤
        Real.sqrt ((initBound μ (geomGrid u1 r) N +
          (r - 1) * d / 2 * (1 + ((N - 1 : ℕ) : ℝ) * Real.log r) +
          fwdVar (geomGrid u1 r) 2 / 2 * ε ^ 2) / 2) :=
  ⟨latticeScore μ (geomGrid u1 r) (pfLin _) (pfCoeff _) ε,
    measurable_latticeScore μ _ (measurable_pfLin _) _ ε,
    sum_sq_latticeScore_sub_le μ _ _ _ hε.le,
    tvSup_detOutput_latticeScore_eq_one μ (geomGrid_strictMono hu1 hr zero_lt_one) hd
      (measurable_pfLin _)
      (pfCoeff_two_ne_zero (geomGrid_strictMono hu1 hr one_lt_two)) hε.ne' hN,
    tvSup_ddpm_latticeScore_le_geomGrid μ hμ hu1 hr hN (measurable_pfLin _) _ hε.le⟩

end FormalizeSampling.DiffusionODESeparation
