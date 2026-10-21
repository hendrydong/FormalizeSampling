module

public import FormalizeSampling.Flow.OULangevinDecayPi
public import FormalizeSampling.Identities.OUPosteriorScore
public import FormalizeSampling.Kernels.ReverseKernel
public import FormalizeSampling.Foundations.KLChainRule
public import FormalizeSampling.Samplers.ProximalGaussianPi

/-!
# Diffusion models (DDPM-type samplers): forward OU chain, exact reverse kernels, algorithm

Definitions shared by the diffusion-model files `Samplers/Diffusion*.lean`.

## Setting

The state space is `E = Fin d → ℝ`; squared Euclidean distances are written as coordinate sums
`∑ i, (a i - b i) ^ 2` (Mathlib's `‖·‖` on `Fin d → ℝ` is the sup norm and is not used).

* **Data.** A probability measure `μ` on `Fin d → ℝ` (no density is assumed).
* **Time grid.** `t : ℕ → ℝ` with `t 0 = 0`; `t 1 = δ` is the early-stopping time and
  `t N = T` the horizon. No monotonicity is needed for the definitions.
* **Forward OU steps** (`fwdKernel t k`, `k ≥ 1`): `F_k(x) = N(α_k x, β_k I)` with
  `α_k = e^{-(t_k - t_{k-1})}` (`fwdScale`) and `β_k = 1 - α_k²` (`fwdVar`), i.e. the product
  OU kernel `OULangevinDecayPi.ouKernelPi 1 (t_k - t_{k-1})`.
* **Forward marginals** (`fwdLaw μ t k`): `p_0 = μ`, `p_k = F_k ∘ p_{k-1}` (the law at time
  `t_k`).
* **Exact reverse kernels** (`revKernel μ t k`): `R_k = F_k†p_{k-1}`, Mathlib's Bayes posterior
  (`ProbabilityTheory.posterior`) of `x_{k-1}` given `x_k` under the joint law
  `p_{k-1} ⊗ F_k`; its mean is `postMean μ t k y` (coordinatewise Bochner integrals).
* **Algorithm** (`algKernel`, `algLaw`): a Gaussian reverse step
  `Q_k(y) = N(m_k(y), σ_k² I)` with an arbitrary measurable mean map `m_k` and variance
  `σ_k² : ℝ≥0`; the algorithm starts at `q_N = N(0, I)` (`stdGaussianPi`), sets
  `q_{k-1} = Q_k ∘ q_k`, and outputs `q_1 = algLaw σ2 m hm N 1`.
* **Score parametrisation** (`scoreMean`): `m_k(y) = α_k⁻¹ (y + β_k s_k(y))` for a learned
  score `s_k`; the DDPM reverse variance is `ddpmVar t k = β_k / α_k²`.

## Main results

* Basic structure: `fwdLaw_succ`, `isProbabilityMeasure_fwdLaw` (instance),
  `revKernel_comp_fwdLaw` (`R_k ∘ p_k = p_{k-1}`), `algLaw_self`, `algLaw_of_lt`,
  `isProbabilityMeasure_algLaw`, `measurable_postMean`, `measurable_scoreMean`,
  `ddpmVar_ne_zero`.
* Discrete schedules: `betaGrid β` turns a noise schedule `0 < β_k < 1` (`k ≥ 1`) into a
  strictly increasing time grid with `α_k = √(1 - β_k)` and `β_k` as forward variance
  (`fwdScale_betaGrid`, `fwdVar_betaGrid`, `betaGrid_strictMono`).
* Moments: `integrable_sum_sq_fwdLaw` (finite second moments propagate along the forward
  chain) and `integrable_apply_fwdLaw` (integrable coordinates).
* Densities: `fwdKernel_eq_withDensity` (`F_k x` has Lebesgue density
  `y ↦ piGaussKernel √β_k (α_k x) y`), `fwdLaw_eq_withDensity` (for `k ≥ 1` and `t_k > t_{k-1}`,
  `p_k` has Lebesgue density `fwdDensity μ t k = piAffineDensity p_{k-1} α_k √β_k`).

## Not proved here

* That `fwdKernel` is the transition kernel of the OU SDE `dX = -X dt + √2 dB` (it is the
  definition, as in `Flow/OULangevinDecayPi.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace FormalizeSampling.Diffusion

open FormalizeSampling.OU FormalizeSampling.OULangevinDecayPi FormalizeSampling.HeatKernelPi

variable {d : ℕ}

/-! ### Gaussian reference law and the forward chain -/

/-- The standard Gaussian `N(0, I_d) = ⊗ᵢ N(0, 1)` on `Fin d → ℝ`, the initial law of the
algorithm and the stationary law of the forward OU chain. -/
noncomputable def stdGaussianPi (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 1

/-- `N(0, I_d)` is a probability measure. -/
instance isProbabilityMeasure_stdGaussianPi : IsProbabilityMeasure (stdGaussianPi d) := by
  unfold stdGaussianPi; infer_instance

/-- The forward contraction factor of step `k`: `α_k = e^{-(t_k - t_{k-1})}`. -/
noncomputable def fwdScale (t : ℕ → ℝ) (k : ℕ) : ℝ := Real.exp (-(t k - t (k - 1)))

/-- The forward noise variance of step `k`: `β_k = 1 - α_k² = 1 - e^{-2(t_k - t_{k-1})}`. -/
noncomputable def fwdVar (t : ℕ → ℝ) (k : ℕ) : ℝ := 1 - fwdScale t k ^ 2

/-- The DDPM reverse variance of step `k`: `σ_k² = β_k / α_k² = e^{2(t_k - t_{k-1})} - 1`
(as an element of `ℝ≥0`). -/
noncomputable def ddpmVar (t : ℕ → ℝ) (k : ℕ) : ℝ≥0 := (fwdVar t k / fwdScale t k ^ 2).toNNReal

/-- The forward OU step `k` (from time `t_{k-1}` to `t_k`):
`fwdKernel t k x = N(α_k x, β_k I) = ⊗ᵢ OU.ouKernel 1 (t_k - t_{k-1}) (xᵢ)`. -/
noncomputable def fwdKernel (t : ℕ → ℝ) (k : ℕ) : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  ouKernelPi 1 (t k - t (k - 1))

/-- Each forward step is a Markov kernel. -/
instance isMarkovKernel_fwdKernel (t : ℕ → ℝ) (k : ℕ) :
    IsMarkovKernel (fwdKernel (d := d) t k) := by
  unfold fwdKernel; infer_instance

/-- The forward marginals: `p_0 = μ` and `p_{k+1} = F_{k+1} ∘ p_k` (the law at time
`t_{k+1}` of the OU chain started from the data law `μ`). -/
noncomputable def fwdLaw (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) : ℕ → Measure (Fin d → ℝ)
  | 0 => μ
  | k + 1 => fwdKernel t (k + 1) ∘ₘ fwdLaw μ t k

/-- The forward chain starts at the data law: `p_0 = μ`. -/
@[simp] theorem fwdLaw_zero (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) : fwdLaw μ t 0 = μ := rfl

/-- Unfolding the forward chain: `p_{k+1} = F_{k+1} ∘ p_k`. -/
theorem fwdLaw_succ (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (k : ℕ) :
    fwdLaw μ t (k + 1) = fwdKernel t (k + 1) ∘ₘ fwdLaw μ t k := rfl

/-- Every forward marginal of a probability measure is a probability measure. -/
instance isProbabilityMeasure_fwdLaw (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ → ℝ) (k : ℕ) : IsProbabilityMeasure (fwdLaw μ t k) := by
  induction k with
  | zero => simpa using (inferInstance : IsProbabilityMeasure μ)
  | succ k ih => rw [fwdLaw_succ]; infer_instance

/-! ### Exact reverse kernels -/

/-- The exact reverse kernel of step `k`: `R_k = F_k†p_{k-1}`, Mathlib's Bayes posterior of
`x_{k-1}` given `x_k` when `x_{k-1} ∼ p_{k-1}` and `x_k ∼ F_k(x_{k-1})`. It is determined only
up to `p_k`-null sets. -/
noncomputable def revKernel (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (k : ℕ) : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (fwdKernel t k)†(fwdLaw μ t (k - 1))

/-- The exact reverse kernel is a Markov kernel. -/
instance isMarkovKernel_revKernel (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ → ℝ) (k : ℕ) : IsMarkovKernel (revKernel μ t k) := by
  unfold revKernel; infer_instance

/-- **Marginal recovery.** For `k ≥ 1`, the exact reverse step maps the time-`t_k` law back to
the time-`t_{k-1}` law: `R_k ∘ p_k = p_{k-1}`. -/
theorem revKernel_comp_fwdLaw (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (k : ℕ) : revKernel μ t (k + 1) ∘ₘ fwdLaw μ t (k + 1) = fwdLaw μ t k := by
  exact posterior_comp_self

/-- The mean of a measure on `Fin d → ℝ`, coordinatewise: `meanPi ν i = ∫ xᵢ dν(x)`. -/
noncomputable def meanPi (ν : Measure (Fin d → ℝ)) : Fin d → ℝ := fun i => ∫ x, x i ∂ν

/-- The posterior mean of step `k`: `m*_k(y) = E[x_{k-1} | x_k = y]`, the mean of `R_k y`. -/
noncomputable def postMean (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (k : ℕ) (y : Fin d → ℝ) : Fin d → ℝ :=
  meanPi (revKernel μ t k y)

/-- The mean of a kernel is a measurable function of the input: `y ↦ ∫ xᵢ d(κ y)(x)`. -/
theorem measurable_meanPi_kernel (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) :
    Measurable fun y => meanPi (κ y) := by
  refine Measurable.of_eval fun i => ?_
  exact (StronglyMeasurable.integral_kernel (κ := κ)
    (f := fun x : Fin d → ℝ => x i) (measurable_pi_apply i).stronglyMeasurable).measurable

/-- The posterior mean `y ↦ m*_k(y)` is measurable. -/
theorem measurable_postMean (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (k : ℕ) : Measurable (postMean μ t k) :=
  measurable_meanPi_kernel _

/-! ### The algorithm -/

/-- The isotropic Gaussian kernel with measurable mean map `m` and variance `v`:
`gaussKernelPi v m hm y = N(m(y), v I) = ⊗ᵢ N(m(y)ᵢ, v)`. -/
noncomputable def gaussKernelPi (v : ℝ≥0) (m : (Fin d → ℝ) → Fin d → ℝ) (hm : Measurable m) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (heatKernelPi v).comap m hm

/-- Evaluation: `gaussKernelPi v m hm y = ⊗ᵢ N(m(y)ᵢ, v)`. -/
theorem gaussKernelPi_apply (v : ℝ≥0) {m : (Fin d → ℝ) → Fin d → ℝ} (hm : Measurable m)
    (y : Fin d → ℝ) :
    gaussKernelPi v m hm y = Measure.pi fun i => gaussianReal (m y i) v := rfl

/-- The Gaussian kernel is Markov. -/
instance isMarkovKernel_gaussKernelPi (v : ℝ≥0) {m : (Fin d → ℝ) → Fin d → ℝ}
    (hm : Measurable m) : IsMarkovKernel (gaussKernelPi v m hm) := by
  unfold gaussKernelPi; infer_instance

/-- The algorithm's reverse step `k`: `Q_k(y) = N(m_k(y), σ_k² I)`. -/
noncomputable def algKernel (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (k : ℕ) : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  gaussKernelPi (σ2 k) (m k) (hm k)

/-- The algorithm's reverse step is a Markov kernel. -/
instance isMarkovKernel_algKernel (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (k : ℕ) : IsMarkovKernel (algKernel σ2 m hm k) := by
  unfold algKernel; infer_instance

/-- Auxiliary: the algorithm's law after `j` reverse steps started at `q_N = N(0, I)`. -/
noncomputable def algLawAux (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N : ℕ) : ℕ → Measure (Fin d → ℝ)
  | 0 => stdGaussianPi d
  | j + 1 => algKernel σ2 m hm (N - j) ∘ₘ algLawAux σ2 m hm N j

/-- The algorithm's law `q_k` at index `k ≤ N`: `q_N = N(0, I)` and `q_{k-1} = Q_k ∘ q_k`
(`algLaw_self`, `algLaw_of_lt`). The output of the sampler is `q_1`. -/
noncomputable def algLaw (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N k : ℕ) : Measure (Fin d → ℝ) :=
  algLawAux σ2 m hm N (N - k)

/-- The algorithm starts from the standard Gaussian: `q_N = N(0, I)`. -/
theorem algLaw_self (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N : ℕ) : algLaw σ2 m hm N N = stdGaussianPi d := by
  simp [algLaw, algLawAux]

/-- One reverse step of the algorithm: for `k < N`, `q_k = Q_{k+1} ∘ q_{k+1}`. -/
theorem algLaw_of_lt (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N k : ℕ} (hk : k < N) :
    algLaw σ2 m hm N k = algKernel σ2 m hm (k + 1) ∘ₘ algLaw σ2 m hm N (k + 1) := by
  have h : N - k = (N - (k + 1)) + 1 := by omega
  rw [algLaw, h, algLawAux, algLaw, show N - (N - (k + 1)) = k + 1 by omega]

/-- Every law of the algorithm is a probability measure. -/
instance isProbabilityMeasure_algLaw (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N k : ℕ) : IsProbabilityMeasure (algLaw σ2 m hm N k) := by
  unfold algLaw
  induction N - k with
  | zero => simp only [algLawAux]; infer_instance
  | succ j ih => simp only [algLawAux]; unfold algKernel; infer_instance

/-- **Score parametrisation of the reverse mean.** With a learned score `s_k`,
`scoreMean t s k y = α_k⁻¹ (y + β_k s_k(y))`. For the exact score `s_k = ∇ log p_k` and
`t_{k-1} < t_k` this is the posterior mean `m*_k(y)` for `p_k`-a.e. `y` (Tweedie's formula,
`Diffusion.postMean_ae_eq_tweedie`). -/
noncomputable def scoreMean (t : ℕ → ℝ) (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (k : ℕ)
    (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (fwdScale t k)⁻¹ * (y i + fwdVar t k * s k y i)

/-- The score-parametrised mean is measurable when the learned score is. -/
theorem measurable_scoreMean (t : ℕ → ℝ) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hs : ∀ k, Measurable (s k)) (k : ℕ) : Measurable (scoreMean t s k) := by
  refine Measurable.of_eval fun i => ?_
  exact measurable_const.mul ((measurable_pi_apply i).add
    (measurable_const.mul ((measurable_pi_apply i).comp (hs k))))

/-! ### Explicit form of the forward step, moments -/

/-- `α_k² = e^{-2 (t_k - t_{k-1})}`. -/
theorem fwdScale_sq (t : ℕ → ℝ) (k : ℕ) :
    fwdScale t k ^ 2 = Real.exp (-2 * 1 * (t k - t (k - 1))) := by
  rw [fwdScale, ← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `α_k > 0`. -/
theorem fwdScale_pos (t : ℕ → ℝ) (k : ℕ) : 0 < fwdScale t k := Real.exp_pos _

/-- `β_k > 0` as soon as `t_{k-1} < t_k`. -/
theorem fwdVar_pos {t : ℕ → ℝ} {k : ℕ} (hk : t (k - 1) < t k) : 0 < fwdVar t k := by
  rw [fwdVar, fwdScale_sq, sub_pos, Real.exp_lt_one_iff]
  linarith

/-- `σ_k² = β_k/α_k²` (`ddpmVar`) is nonzero for `k ≥ 1` on a strictly increasing grid. -/
theorem ddpmVar_ne_zero {t : ℕ → ℝ} (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    ddpmVar t k ≠ 0 := by
  simpa [ddpmVar] using div_pos (fwdVar_pos (ht (by omega : k - 1 < k)))
    (pow_pos (fwdScale_pos t k) 2)

/-! ### Grids from a discrete noise schedule -/

/-- The OU time grid of a discrete noise schedule `β_k` (Ho et al. 2020): `t_0 = 0` and
`t_k = t_{k-1} - log(1 - β_k) / 2` for `k ≥ 1`, i.e. `e^{-2 (t_k - t_{k-1})} = 1 - β_k`. With
this grid the forward step `k` is `N(√(1 - β_k) x, β_k I)` (`fwdScale_betaGrid`,
`fwdVar_betaGrid`), so the results stated for a time grid `t` apply to the schedule. -/
noncomputable def betaGrid (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => betaGrid β k - Real.log (1 - β (k + 1)) / 2

/-- `betaGrid β 0 = 0`. -/
@[simp] theorem betaGrid_zero (β : ℕ → ℝ) : betaGrid β 0 = 0 := rfl

/-- On `betaGrid β`, the forward contraction factor of step `k + 1` is
`α_{k+1} = √(1 - β_{k+1})`, provided `β_{k+1} < 1`. -/
theorem fwdScale_betaGrid {β : ℕ → ℝ} {k : ℕ} (hβ : β (k + 1) < 1) :
    fwdScale (betaGrid β) (k + 1) = √(1 - β (k + 1)) := by
  have h1 : 0 < 1 - β (k + 1) := by linarith
  rw [fwdScale, Nat.add_sub_cancel, betaGrid,
    show -(betaGrid β k - Real.log (1 - β (k + 1)) / 2 - betaGrid β k)
      = Real.log (1 - β (k + 1)) / 2 by ring,
    Real.sqrt_eq_rpow, ← Real.exp_log h1, ← Real.exp_mul, Real.log_exp]
  congr 1
  ring

/-- On `betaGrid β`, the forward noise variance of step `k + 1` is the schedule value:
`fwdVar (betaGrid β) (k + 1) = β_{k+1}`, provided `β_{k+1} < 1`. -/
theorem fwdVar_betaGrid {β : ℕ → ℝ} {k : ℕ} (hβ : β (k + 1) < 1) :
    fwdVar (betaGrid β) (k + 1) = β (k + 1) := by
  rw [fwdVar, fwdScale_betaGrid hβ, Real.sq_sqrt (by linarith)]
  ring

/-- For a schedule with `0 < β_k < 1` for all `k ≥ 1`, `betaGrid β` is strictly increasing (and
`betaGrid β 0 = 0`), as required by the DDPM theorems. The value `β 0` is not used. -/
theorem betaGrid_strictMono {β : ℕ → ℝ} (hβ0 : ∀ k, 1 ≤ k → 0 < β k)
    (hβ1 : ∀ k, 1 ≤ k → β k < 1) : StrictMono (betaGrid β) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have : Real.log (1 - β (k + 1)) < 0 :=
    Real.log_neg (by linarith [hβ1 (k + 1) (by omega)]) (by linarith [hβ0 (k + 1) (by omega)])
  show betaGrid β k < betaGrid β k - Real.log (1 - β (k + 1)) / 2
  linarith

/-- Evaluation of the forward step: `F_k x = ⊗ᵢ N(α_k xᵢ, β_k)` (for every time grid; if
`t_k < t_{k-1}` the variance is truncated at `0`). -/
theorem fwdKernel_apply (t : ℕ → ℝ) (k : ℕ) (x : Fin d → ℝ) :
    fwdKernel t k x =
      Measure.pi fun i => gaussianReal (fwdScale t k * x i) (fwdVar t k).toNNReal := by
  rw [fwdKernel, ouKernelPi_apply]
  congr 1; funext i
  rw [ouKernel_apply, ouVar, fwdVar, fwdScale_sq, fwdScale, neg_one_mul]

/-- Finite second moments propagate along the forward chain: if `∫ ∑ᵢ xᵢ² dμ < ∞` then
`∫ ∑ᵢ xᵢ² dp_k < ∞` for every `k`. -/
theorem integrable_sum_sq_fwdLaw (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (t : ℕ → ℝ) (k : ℕ) :
    Integrable (fun x => ∑ i, x i ^ 2) (fwdLaw μ t k) := by
  induction k with
  | zero => exact hμ
  | succ k ih =>
    rw [fwdLaw_succ, fwdKernel, ouKernelPi_eq_ouKernelVarPi, ouKernelVarPi_comp_eq]
    exact ProximalSharpGaussianPi.integrable_sum_sq_heatKernelPi_comp _
      (ProximalSharpGaussianPi.integrable_sum_sq_map_scalePi _ ih _) _

/-- A finite second moment gives integrable coordinates: `|xᵢ| ≤ ∑ⱼ xⱼ² + 1`. -/
theorem integrable_apply_of_sum_sq {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (hν : Integrable (fun x => ∑ i, x i ^ 2) ν) (i : Fin d) : Integrable (fun x => x i) ν := by
  refine (hν.add (integrable_const 1)).mono' (measurable_pi_apply i).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- Every forward marginal has integrable coordinates when the data has a finite second
moment. -/
theorem integrable_apply_fwdLaw (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ∑ i, x i ^ 2) μ) (t : ℕ → ℝ) (k : ℕ) (i : Fin d) :
    Integrable (fun x => x i) (fwdLaw μ t k) :=
  integrable_apply_of_sum_sq (integrable_sum_sq_fwdLaw μ hμ t k) i

/-! ### Lebesgue densities of the forward step and of the marginals -/

/-- The Gaussian transition density of step `k`:
`fwdTransDensity t k x y = piGaussKernel √β_k (α_k x) y`, the density at `y` of `N(α_k x, β_k I)`.
-/
noncomputable def fwdTransDensity (t : ℕ → ℝ) (k : ℕ) (x y : Fin d → ℝ) : ℝ :=
  Tweedie.piGaussKernel (Real.sqrt (fwdVar t k)) (fwdScale t k • x) y

/-- The transition density is jointly continuous. -/
theorem continuous_fwdTransDensity (t : ℕ → ℝ) (k : ℕ) :
    Continuous fun z : (Fin d → ℝ) × (Fin d → ℝ) => fwdTransDensity t k z.1 z.2 := by
  have hc : Continuous fun z : (Fin d → ℝ) × (Fin d → ℝ) => (fwdScale t k • z.1, z.2) := by
    fun_prop
  have h := (Tweedie.continuous_piGaussKernel_uncurry (d := d) (Real.sqrt (fwdVar t k))).comp hc
  exact h

/-- The transition density is nonnegative. -/
theorem fwdTransDensity_nonneg (t : ℕ → ℝ) (k : ℕ) (x y : Fin d → ℝ) :
    0 ≤ fwdTransDensity t k x y :=
  Tweedie.piGaussKernel_nonneg _ _ _

/-- The transition density is positive when `t_{k-1} < t_k`. -/
theorem fwdTransDensity_pos {t : ℕ → ℝ} {k : ℕ} (hk : t (k - 1) < t k) (x y : Fin d → ℝ) :
    0 < fwdTransDensity t k x y :=
  Tweedie.piGaussKernel_pos (Real.sqrt_pos.2 (fwdVar_pos hk)).ne' _ _

/-- The transition density is bounded (uniformly in `x, y`). -/
theorem fwdTransDensity_le (t : ℕ → ℝ) (k : ℕ) (x y : Fin d → ℝ) :
    fwdTransDensity t k x y ≤
      ∏ _i : Fin d, (Real.sqrt (2 * Real.pi * Real.sqrt (fwdVar t k) ^ 2))⁻¹ :=
  Tweedie.piGaussKernel_le _ _ _

/-- **Density of the forward step.** If `t_{k-1} < t_k`, then
`F_k x = volume.withDensity (y ↦ piGaussKernel √β_k (α_k x) y)`. -/
theorem fwdKernel_eq_withDensity {t : ℕ → ℝ} {k : ℕ} (hk : t (k - 1) < t k)
    (x : Fin d → ℝ) :
    fwdKernel t k x =
      volume.withDensity fun y => ENNReal.ofReal (fwdTransDensity t k x y) := by
  have hβ := fwdVar_pos hk
  rw [fwdKernel_apply]
  unfold fwdTransDensity
  rw [← Tweedie.pi_gaussianReal_eq_withDensity (Real.sqrt_pos.2 hβ).ne']
  congr 1; funext i
  congr 1
  ext
  simp [Real.sq_sqrt hβ.le, hβ.le]
  rfl

/-- **Density form of the forward step.** If `t_{k-1} < t_k`, the forward step is the density
kernel of `fwdTransDensity t k` with respect to Lebesgue measure. -/
theorem fwdKernel_eq_densityKernel {t : ℕ → ℝ} {k : ℕ} (hk : t (k - 1) < t k) :
    fwdKernel (d := d) t k = ReverseKernel.densityKernel volume
      (fun x y => ENNReal.ofReal (fwdTransDensity t k x y)) := by
  ext1 x
  rw [ReverseKernel.densityKernel_apply, fwdKernel_eq_withDensity hk]
  exact ENNReal.measurable_ofReal.comp (continuous_fwdTransDensity t k).measurable

/-- The Lebesgue density of the forward marginal `p_k` (`k ≥ 1`):
`fwdDensity μ t k y = ∫ piGaussKernel √β_k (α_k x) y dp_{k-1}(x)`
(`= OUPosterior.piAffineDensity p_{k-1} α_k √β_k y`). -/
noncomputable def fwdDensity (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) (k : ℕ) (y : Fin d → ℝ) :
    ℝ :=
  OUPosterior.piAffineDensity (fwdLaw μ t (k - 1)) (fwdScale t k) (Real.sqrt (fwdVar t k)) y

/-- `x ↦ fwdTransDensity t k x y` is integrable under any finite measure. -/
theorem integrable_fwdTransDensity (ν : Measure (Fin d → ℝ)) [IsFiniteMeasure ν] (t : ℕ → ℝ)
    (k : ℕ) (y : Fin d → ℝ) : Integrable (fun x => fwdTransDensity t k x y) ν := by
  refine Integrable.of_bound (C := ∏ _i : Fin d,
    (Real.sqrt (2 * Real.pi * Real.sqrt (fwdVar t k) ^ 2))⁻¹)
    ((continuous_fwdTransDensity t k).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (fwdTransDensity_nonneg t k x y)]
  exact fwdTransDensity_le t k x y

/-- The marginal density of the density-form forward step from `p_{k}` equals `fwdDensity`. -/
theorem marginalDensity_eq_fwdDensity (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ → ℝ) (k : ℕ) (y : Fin d → ℝ) :
    ReverseKernel.marginalDensity (fwdLaw μ t k) 1
        (fun x y => ENNReal.ofReal (fwdTransDensity t (k + 1) x y)) y =
      ENNReal.ofReal (fwdDensity μ t (k + 1) y) := by
  rw [ReverseKernel.marginalDensity, fwdDensity, OUPosterior.piAffineDensity, Nat.add_sub_cancel]
  change _ = ENNReal.ofReal (∫ x, fwdTransDensity t (k + 1) x y ∂(fwdLaw μ t k))
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_fwdTransDensity _ t (k + 1) y)
      (ae_of_all _ fun x => fwdTransDensity_nonneg t (k + 1) x y)]
  simp only [Pi.one_apply, one_mul]

/-- **Density of the forward marginals.** If `t_k < t_{k+1}`, the marginal `p_{k+1}` has
Lebesgue density `fwdDensity μ t (k + 1)`; no density of the data law `μ` is needed. -/
theorem fwdLaw_eq_withDensity (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℕ → ℝ}
    {k : ℕ} (hk : t k < t (k + 1)) :
    fwdLaw μ t (k + 1) =
      volume.withDensity fun y => ENNReal.ofReal (fwdDensity μ t (k + 1) y) := by
  have hk' : t (k + 1 - 1) < t (k + 1) := by rwa [Nat.add_sub_cancel]
  have hmeas : Measurable (Function.uncurry
      fun x y : Fin d → ℝ => ENNReal.ofReal (fwdTransDensity t (k + 1) x y)) :=
    ENNReal.measurable_ofReal.comp (continuous_fwdTransDensity t (k + 1)).measurable
  rw [fwdLaw_succ, fwdKernel_eq_densityKernel hk', ← withDensity_one (μ := fwdLaw μ t k),
    ReverseKernel.densityKernel_comp_withDensity (p := 1) measurable_const hmeas]
  congr 1; funext y
  exact marginalDensity_eq_fwdDensity μ t k y

end FormalizeSampling.Diffusion
