module

public import Mathlib.Topology.UniformSpace.Uniformizable
public import FormalizeSampling.Foundations.VectorCalculus
public import FormalizeSampling.Samplers.MetropolisHastings
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# MALA: the Metropolis-adjusted Langevin algorithm leaves its target invariant

Scope. MALA as an instance of the density-based Metropolis–Hastings kernel of
`Samplers/MetropolisHastings.lean`, with reference measure Lebesgue `volume`, on `Fin d → ℝ`.

## Conventions

* Step size `h : ℝ≥0`; the proposal variance is `2 * h` (Mathlib's `gaussianPDF m v` takes the
  **variance** `v : ℝ≥0`). All theorems that need a genuine Gaussian assume `0 < h`.
* Target: a real function `π` (intended `π ≥ 0`, e.g. `π = exp(-f)`), used through
  `targetDensity π = ENNReal.ofReal ∘ π`; the target law is `volume.withDensity (targetDensity π)`.
  It need not be normalised. A negative value of `π` would be read as `0` by `ENNReal.ofReal`.
* Proposal: `N(x + h ∇ log π(x), 2h I)`, written as the product
  `∏ᵢ N(xᵢ + h ∂ᵢ log π(x), 2h)(yᵢ)` (`prodGaussianPDF`, identified with the product law of
  one-dimensional Gaussians in `withDensity_prodGaussianPDF`).
* Lean's junk values: `fderiv` vanishes where `log π` is not differentiable and
  `Real.log 0 = 0`. At such points the proposal mean is not the Langevin drift, but the
  proposal is still a Gaussian density that is jointly measurable in `(x, y)`
  (`measurable_fderiv_apply_const`), so the MH kernel is still exactly
  `π`-invariant. For positive differentiable `π` the drift is the true `∇ log π`. Hence **no
  smoothness of `π` is needed** for invariance; measurability of `π` is the only hypothesis.
* Acceptance: the exact Metropolis–Hastings rule
  `α(x, y) = min 1 (π(y) q(y, x) / (π(x) q(x, y)))` (`MH.acceptance`).

## Main results (registry ID MH-1)

* `lintegral_prodGaussianPDF`, `withDensity_prodGaussianPDF` (from Tonelli for products,
  `lintegral_prod_ofReal` in `Foundations/MeasureHelpers.lean`): the proposal density is that of
  the product law `⊗ᵢ N(mᵢ, 2h)`.
* `isMarkovKernel_malaKernelPi`, `isReversible_malaKernelPi`, `invariant_malaKernelPi`,
  `bind_malaKernelPi`: for every measurable `π : (Fin d → ℝ) → ℝ` and every `h > 0`, MALA is a
  Markov kernel, reversible with respect to `π(x) dx`, and leaves `π(x) dx` invariant;
  `detailed_balance_pi` is the pointwise off-diagonal identity and `acceptance_pos_pi` shows
  that, for a positive target, no move is rejected with certainty.
* `score_exp_neg`, `proposalMeanPi_exp_neg`, `bind_malaKernelPi_exp_neg`: for `π = exp(-f)` the
  proposal is `N(x - h ∇f(x), 2h I)` and `exp(-f(x)) dx` is invariant (`f` measurable).

**Why the acceptance step matters (CE-03).** The MALA proposal alone is one step of the
unadjusted Langevin algorithm (ULA). For the target `N(0, 1)` (`(log π)'(x) = -x`) it is
`X' = (1 - h) X + √(2h) Z`, which maps `N(0, 1)` to `N(0, 1 + h²)` (counterexample CE-03): ULA is
biased for every `h > 0`. The exact Metropolis–Hastings accept/reject step with the ratio
`α` above is precisely what removes this bias: the theorems here hold for every `h > 0`.

## Not proved here

* Convergence of MALA to `π`, geometric ergodicity, mixing-time bounds or optimal step-size
  scaling (e.g. `h ∝ d^{-1/3}`); only one-step reversibility and invariance are proved.
* Preconditioned MALA (`N(x + h A ∇ log π(x), 2h A)`) or position-dependent metrics.
* The ULA bias itself (that is CE-03, proved elsewhere) and any quantitative comparison
  between MALA and ULA.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FormalizeSampling.MALA

/-! ### Gaussian proposal densities -/

/-- Joint measurability of a Gaussian density whose mean and argument depend measurably on a
parameter: `a ↦ gaussianPDF (m a) v (y a)` is measurable if `m` and `y` are. -/
theorem measurable_gaussianPDF_comp {α : Type*} [MeasurableSpace α] {m y : α → ℝ}
    (hm : Measurable m) (hy : Measurable y) (v : ℝ≥0) :
    Measurable fun a => gaussianPDF (m a) v (y a) := by
  simp only [gaussianPDF, gaussianPDFReal]
  fun_prop

/-! ### Target densities -/

/-- The (unnormalised) target density `x ↦ π(x)` as an `ℝ≥0∞`-valued function
(`ENNReal.ofReal`, so negative values would be read as `0`; for the intended `π ≥ 0` it is
`π` itself). -/
noncomputable def targetDensity {α : Type*} (π : α → ℝ) (x : α) : ℝ≥0∞ :=
  ENNReal.ofReal (π x)

/-- A measurable real `π` gives a measurable `ℝ≥0∞`-valued target density. -/
theorem measurable_targetDensity {α : Type*} [MeasurableSpace α] {π : α → ℝ}
    (hπ : Measurable π) : Measurable (targetDensity π) :=
  ENNReal.measurable_ofReal.comp hπ

/-! ### `d`-dimensional MALA -/

section Multi

variable {d : ℕ}

/-- The product Gaussian density `∏ᵢ N(mᵢ, v)(yᵢ)` on `Fin d → ℝ`, i.e. the density of
`N(m, v I)` with respect to Lebesgue measure. -/
noncomputable def prodGaussianPDF (m : Fin d → ℝ) (v : ℝ≥0) (y : Fin d → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF (m i) v (y i)

/-- For `v ≠ 0` the product Gaussian density has total Lebesgue mass `1`. -/
theorem lintegral_prodGaussianPDF (m : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ y, prodGaussianPDF m v y = 1 := by
  have h := lintegral_prod_ofReal (fun i => gaussianPDFReal (m i) v)
    (fun i => integrable_gaussianPDFReal (m i) v) (fun i t => gaussianPDFReal_nonneg _ _ _)
  simp only [prodGaussianPDF, gaussianPDF]
  rw [h]
  exact Finset.prod_eq_one fun i _ => lintegral_gaussianPDFReal_eq_one _ hv

/-- For `v ≠ 0`, `prodGaussianPDF m v` is the Lebesgue density of the product law
`⊗ᵢ N(mᵢ, v)` (that is, of `N(m, v I)`):
`volume.withDensity (prodGaussianPDF m v) = Measure.pi (fun i ↦ gaussianReal (m i) v)`. -/
theorem withDensity_prodGaussianPDF (m : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    volume.withDensity (prodGaussianPDF m v) = Measure.pi fun i => gaussianReal (m i) v := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : ∀ y : Fin d → ℝ, (Set.univ.pi s).indicator (prodGaussianPDF m v) y
      = ∏ i, ENNReal.ofReal ((s i).indicator (gaussianPDFReal (m i) v) (y i)) := by
    intro y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hy i (Set.mem_univ i))]
      rfl
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [Set.indicator_of_notMem hi])).symm
  simp_rw [hpt]
  rw [lintegral_prod_ofReal _ (fun i => (integrable_gaussianPDFReal _ _).indicator (hs i))
    (fun i t => Set.indicator_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply _ hv, ← lintegral_indicator (hs i)]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ s i
  · simp [Set.indicator_of_mem ht, gaussianPDF]
  · simp [Set.indicator_of_notMem ht]

/-- The `d`-dimensional MALA proposal mean `x + h ∇ log π(x)` (with the shared state score
`score π = ∇ₓ log π`; coordinates where `log π` is not differentiable contribute `0`). -/
noncomputable def proposalMeanPi (π : (Fin d → ℝ) → ℝ) (h : ℝ≥0) (x : Fin d → ℝ) :
    Fin d → ℝ :=
  x + (h : ℝ) • score π x

/-- The `d`-dimensional MALA proposal density `q(x, y) = N(x + h ∇ log π(x), 2h I)(y)`, written
as the product of the `d` one-dimensional Gaussian densities of variance `2 h`. -/
noncomputable def proposalPi (π : (Fin d → ℝ) → ℝ) (h : ℝ≥0) (x y : Fin d → ℝ) : ℝ≥0∞ :=
  prodGaussianPDF (proposalMeanPi π h x) (2 * h) y

variable {π : (Fin d → ℝ) → ℝ} {h : ℝ≥0}

/-- The `d`-dimensional MALA proposal mean is measurable for every `π`. -/
theorem measurable_proposalMeanPi (π : (Fin d → ℝ) → ℝ) (h : ℝ≥0) :
    Measurable (proposalMeanPi π h) :=
  measurable_id.add ((measurable_score π).const_smul (h : ℝ))

/-- The `d`-dimensional MALA proposal density is jointly measurable, for every `π` and `h`. -/
theorem measurable_proposalPi (π : (Fin d → ℝ) → ℝ) (h : ℝ≥0) :
    Measurable (Function.uncurry (proposalPi π h)) := by
  change Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
    ∏ i, gaussianPDF (proposalMeanPi π h p.1 i) (2 * h) (p.2 i)
  refine Finset.measurable_prod _ fun i _ => ?_
  exact measurable_gaussianPDF_comp
    ((measurable_pi_apply i).comp ((measurable_proposalMeanPi π h).comp measurable_fst))
    ((measurable_pi_apply i).comp measurable_snd) _

/-- For `h > 0` the `d`-dimensional MALA proposal density is normalised. -/
theorem lintegral_proposalPi (hh : 0 < h) (x : Fin d → ℝ) : ∫⁻ y, proposalPi π h x y = 1 :=
  lintegral_prodGaussianPDF _ (mul_ne_zero two_ne_zero hh.ne')

/-- All products `π(x) q(x, y)` are finite in the `d`-dimensional case. -/
theorem targetDensity_mul_proposalPi_ne_top (x y : Fin d → ℝ) :
    targetDensity π x * proposalPi π h x y ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
    unfold proposalPi prodGaussianPDF
    exact ENNReal.prod_ne_top fun _ _ => gaussianPDF_ne_top)

/-- The `d`-dimensional MALA kernel: the Metropolis–Hastings kernel (with respect to Lebesgue
measure on `Fin d → ℝ`) for the target density `π` and the proposal `N(x + h ∇ log π(x), 2h I)`.
-/
noncomputable def malaKernelPi (π : (Fin d → ℝ) → ℝ) (hπ : Measurable π) (h : ℝ≥0) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  MH.mhKernel volume (measurable_targetDensity hπ) (measurable_proposalPi π h)

/-- `malaKernelPi` is the Metropolis–Hastings law with the `d`-dimensional Langevin proposal. -/
theorem malaKernelPi_apply (hπ : Measurable π) (x : Fin d → ℝ) :
    malaKernelPi π hπ h x = MH.mhMeasure volume (targetDensity π) (proposalPi π h) x :=
  rfl

/-- For `h > 0` the `d`-dimensional MALA kernel is a Markov kernel. -/
theorem isMarkovKernel_malaKernelPi (hπ : Measurable π) (hh : 0 < h) :
    IsMarkovKernel (malaKernelPi π hπ h) :=
  MH.isMarkovKernel_mhKernel _ _ (lintegral_proposalPi hh)

/-- For a positive target and `h > 0`, every `d`-dimensional MALA move `x → y` is accepted
with positive probability: `0 < α(x, y)`. -/
theorem acceptance_pos_pi (hh : 0 < h) {x y : Fin d → ℝ} (hy : 0 < π y) :
    0 < MH.acceptance (targetDensity π) (proposalPi π h) x y := by
  refine MH.acceptance_pos (targetDensity_mul_proposalPi_ne_top x y)
    (mul_ne_zero (ENNReal.ofReal_pos.2 hy).ne' ?_)
  unfold proposalPi prodGaussianPDF
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    (gaussianPDF_pos _ (mul_ne_zero two_ne_zero hh.ne') _).ne'

/-- **`d`-dimensional MALA off-diagonal detailed balance (MH-1).** For every `π`, `h` and
`x`, `y`: `π(x) q(x, y) α(x, y) = π(y) q(y, x) α(y, x)` with the proposal
`q(x, ·) = N(x + h ∇ log π(x), 2h I)` and the exact Metropolis–Hastings acceptance `α`. -/
theorem detailed_balance_pi (x y : Fin d → ℝ) :
    targetDensity π x * proposalPi π h x y
        * MH.acceptance (targetDensity π) (proposalPi π h) x y
      = targetDensity π y * proposalPi π h y x
        * MH.acceptance (targetDensity π) (proposalPi π h) y x :=
  MH.detailed_balance (targetDensity_mul_proposalPi_ne_top x y)
    (targetDensity_mul_proposalPi_ne_top y x)

/-- **`d`-dimensional MALA reversibility (MH-1).** For every measurable
`π : (Fin d → ℝ) → ℝ` and every `h`, `malaKernelPi π hπ h` is reversible with respect to
`π(x) dx` (`Kernel.IsReversible`). -/
theorem isReversible_malaKernelPi (hπ : Measurable π) :
    (malaKernelPi π hπ h).IsReversible (volume.withDensity (targetDensity π)) :=
  MH.isReversible_mhKernel _ _ targetDensity_mul_proposalPi_ne_top

/-- **`d`-dimensional MALA invariance (MH-1), `Kernel.Invariant` form.** For every measurable
`π : (Fin d → ℝ) → ℝ` and every `h > 0`, `malaKernelPi π hπ h` leaves `π(x) dx` invariant. -/
theorem invariant_malaKernelPi (hπ : Measurable π) (hh : 0 < h) :
    (malaKernelPi π hπ h).Invariant (volume.withDensity (targetDensity π)) :=
  MH.invariant_mhKernel _ _ (lintegral_proposalPi hh) targetDensity_mul_proposalPi_ne_top

/-- **`d`-dimensional MALA leaves its target invariant (MH-1).** For every measurable
`π : (Fin d → ℝ) → ℝ` (no smoothness or positivity assumed) and every step `h > 0`, the
Metropolis–Hastings kernel with proposal `N(x + h ∇ log π(x), 2h I)` and exact acceptance
satisfies `(volume.withDensity π).bind (malaKernelPi π hπ h) = volume.withDensity π`. As in
1D, the exact acceptance step is what removes the ULA bias of CE-03. -/
theorem bind_malaKernelPi (hπ : Measurable π) (hh : 0 < h) :
    (volume.withDensity (targetDensity π)).bind (malaKernelPi π hπ h)
      = volume.withDensity (targetDensity π) :=
  invariant_malaKernelPi hπ hh

/-- For `π = exp(-f)` on `Fin d → ℝ`, the state score is `∇ log π = -∇f` (for every `f`; both
sides use Lean's `fderiv`, which is `0` where `f` is not differentiable). -/
theorem score_exp_neg (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    score (fun y => Real.exp (-f y)) x = -grad f x := by
  ext i
  have hneg : (fun y => -f y) = -f := rfl
  simp only [score, grad, partialDeriv, Real.log_exp, Pi.neg_apply, hneg, fderiv_neg,
    neg_apply]

/-- For `π = exp(-f)` on `Fin d → ℝ`, the MALA proposal mean is `x - h ∇f(x)`. -/
theorem proposalMeanPi_exp_neg (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    proposalMeanPi (fun y => Real.exp (-f y)) h x = x - (h : ℝ) • grad f x := by
  rw [proposalMeanPi, score_exp_neg, smul_neg, sub_eq_add_neg]

/-- **`d`-dimensional MALA for `π = exp(-f)` (MH-1).** For every measurable potential
`f : (Fin d → ℝ) → ℝ` (e.g. any differentiable `f`) and every `h > 0`, the MALA kernel with
proposal `N(x - h ∇f(x), 2h I)` and exact Metropolis–Hastings acceptance leaves the
(unnormalised) law `exp(-f(x)) dx` invariant. -/
theorem bind_malaKernelPi_exp_neg {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (hh : 0 < h) :
    (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-f x)))).bind
        (malaKernelPi (fun x => Real.exp (-f x)) (Real.measurable_exp.comp hf.neg) h)
      = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-f x))) :=
  bind_malaKernelPi _ hh

end Multi

end FormalizeSampling.MALA
