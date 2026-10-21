module

public import FormalizeSampling.Samplers.RGOCouplingWeakDefs
public import FormalizeSampling.Foundations.ConvexSmoothing

/-!
# Approximating the RGO kernel of a convex potential by smooth convex ones

Status: **Verified** (no named hypotheses).

For a convex potential `f : (Fin d → ℝ) → ℝ` and `η > 0` the RGO kernel `rgoKernelPi f η`
(density `∝ exp(-f x - |x - y|² / (2η))`) is the weak limit, at every `y`, of the RGO kernels of
smooth convex potentials with bounded first and second derivatives (`SmoothConvexBdd`). This is
the approximation step of the `1/k` rate for general log-concave targets: weak contractive
couplings (`HasWeakCoupling`) pass to such limits (`Samplers/RGOCouplingWeak.lean`).

The approximants are the mollified Pasch–Hausdorff envelopes of
`Foundations/ConvexSmoothing.lean`. They and `f` are bounded below by one function
`-A - B ‖x‖`, so `exp(-g x - |x - y|² / (2η))` is dominated by a multiple of
`exp(-|x - y|² / (4η))`; dominated convergence gives convergence of the RGO normalisers and of
the integrals of bounded continuous functions.

## Main results

* `integrable_rgoPi_of_lowerBound`, `rgoNormalizerPi_pos_of_lowerBound`,
  `isMarkovKernel_rgoKernelPi_of_lowerBound`: the RGO kernel of a continuous potential with a
  linear lower bound is a Markov kernel, **without** assuming `∫ e^{-h} < ∞` (its density form
  is `rgoKernelPi_apply_of_continuous` in `Samplers/RGOCouplingWeakDefs.lean`).
* `weakTendsto_rgoKernelPi_of_tendsto`: pointwise convergence of continuous potentials with a
  common linear lower bound gives weak convergence of the RGO kernels at every `y`.
* `isMarkovKernel_rgoKernelPi_of_convexOn`: the RGO kernel of a convex potential is Markov.
* `exists_smoothConvexBdd_tendsto_rgoKernelPi`: the approximation theorem.

## Not proved here

* Any rate of convergence, or convergence in a stronger sense (total variation, KL).
* Weak contractive couplings themselves (`Samplers/RGOCouplingLangevin.lean`,
  `Samplers/RGOCouplingWeak.lean`).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology FormalizeSampling.ReverseKernel
open FormalizeSampling.ProximalPi FormalizeSampling.ConvexSmoothing
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingWeak

variable {d : ℕ}

/-- **Gaussian domination of the RGO integrand.** If `h x ≥ -A - B ‖x‖` for all `x`, `B ≥ 0` and
`η > 0`, then `exp(-h x - |x - y|² / (2η)) ≤ exp(A + B ‖y‖ + B² η) exp(-|x - y|² / (4η))`. -/
theorem exp_rgo_le_of_lowerBound {h : (Fin d → ℝ) → ℝ} {A B η : ℝ}
    (hB : 0 ≤ B) (hlow : ∀ x, -A - B * ‖x‖ ≤ h x) (hη : 0 < η) (y x : Fin d → ℝ) :
    Real.exp (-h x - sqDist x y / (2 * η)) ≤
      Real.exp (A + B * ‖y‖ + B ^ 2 * η) * Real.exp (-((4 * η)⁻¹ * sqDist x y)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 := hlow x
  have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have := norm_add_le y (x - y); rwa [add_sub_cancel] at this
  have h3 := sq_norm_sub_le_sqDist x y
  set u := ‖x - y‖
  set s := sqDist x y
  have hs : 0 ≤ s := sqDist_nonneg x y
  -- `B u ≤ u² / (4η) + B² η ≤ s / (4η) + B² η`
  have h4 : B * u ≤ s / (4 * η) + B ^ 2 * η := by
    have : B * u ≤ u ^ 2 / (4 * η) + B ^ 2 * η := by
      have e : u ^ 2 / (4 * η) + B ^ 2 * η - B * u = (u - 2 * B * η) ^ 2 / (4 * η) := by
        field_simp; ring
      have : 0 ≤ (u - 2 * B * η) ^ 2 / (4 * η) := by positivity
      linarith
    have : u ^ 2 / (4 * η) ≤ s / (4 * η) := div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  have e1 : s / (2 * η) = 2 * (s / (4 * η)) := by field_simp; ring
  have e2 : (4 * η)⁻¹ * s = s / (4 * η) := by rw [inv_mul_eq_div]
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h2 hB
  nlinarith

section LowerBound

variable {h : (Fin d → ℝ) → ℝ} {A B η : ℝ}

/-- The Gaussian dominating function of `exp_rgo_le_of_lowerBound` is integrable (`η > 0`). -/
theorem integrable_rgoDominator (hη : 0 < η) (A B : ℝ) (y : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (A + B * ‖y‖ + B ^ 2 * η) * Real.exp (-((4 * η)⁻¹ * sqDist x y))) :=
  (integrable_exp_neg_mul_sqDist (by positivity) y).const_mul _

/-- **Integrability of the RGO integrand without `∫ e^{-h} < ∞`.** For continuous `h` with
`h x ≥ -A - B ‖x‖` (`B ≥ 0`) and `η > 0`, `x ↦ exp(-h x - |x - y|² / (2η))` is integrable for
every `y`. -/
theorem integrable_rgoPi_of_lowerBound (hh : Continuous h) (hB : 0 ≤ B)
    (hlow : ∀ x, -A - B * ‖x‖ ≤ h x) (hη : 0 < η) (y : Fin d → ℝ) :
    Integrable (fun x => Real.exp (-h x - sqDist x y / (2 * η))) := by
  refine (integrable_rgoDominator hη A B y).mono' ?_ (Eventually.of_forall fun x => ?_)
  · have : Continuous fun x : Fin d → ℝ => sqDist x y :=
      continuous_sqDist.comp (continuous_id.prodMk continuous_const)
    exact (by fun_prop : Continuous fun x => Real.exp (-h x - sqDist x y / (2 * η)))
      |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_rgo_le_of_lowerBound hB hlow hη y x

/-- The RGO normaliser is positive under the same assumptions (continuous `h`,
`h ≥ -A - B ‖·‖` with `B ≥ 0`, `η > 0`); `∫ e^{-h} < ∞` is not needed. -/
theorem rgoNormalizerPi_pos_of_lowerBound (hh : Continuous h) (hB : 0 ≤ B)
    (hlow : ∀ x, -A - B * ‖x‖ ≤ h x) (hη : 0 < η) (y : Fin d → ℝ) :
    0 < rgoNormalizerPi h η y :=
  integral_exp_pos (integrable_rgoPi_of_lowerBound hh hB hlow hη y)

/-- **The RGO kernel is Markov without `∫ e^{-h} < ∞`** (continuous `h`, `h ≥ -A - B ‖·‖`
with `B ≥ 0`, `η > 0`). -/
theorem isMarkovKernel_rgoKernelPi_of_lowerBound (hh : Continuous h) (hB : 0 ≤ B)
    (hlow : ∀ x, -A - B * ‖x‖ ≤ h x) (hη : 0 < η) :
    IsMarkovKernel (rgoKernelPi h η) := by
  refine isMarkovKernel_densityKernel (measurable_rgoDensityPi_of_continuous hh) fun y => ?_
  have hint := integrable_rgoPi_of_lowerBound hh hB hlow hη y
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => rgoDensityPi h η y x)
    (by unfold rgoDensityPi; exact hint.div_const _)
    (Eventually.of_forall fun x => rgoDensityPi_nonneg y x)]
  unfold rgoDensityPi
  rw [integral_div, ← rgoNormalizerPi,
    div_self (rgoNormalizerPi_pos_of_lowerBound hh hB hlow hη y).ne', ENNReal.ofReal_one]

/-- **Convergence of weighted RGO integrals.** Let `h n`, `h` be continuous with a common lower
bound `-A - B ‖x‖` (`B ≥ 0`), `h n → h` pointwise, `η > 0`, and `φ` continuous with
`|φ| ≤ N`. Then `∫ φ(x) exp(-h n x - |x - y|²/(2η)) dx → ∫ φ(x) exp(-h x - |x - y|²/(2η)) dx`
(dominated convergence with a Gaussian dominating function). -/
theorem tendsto_integral_mul_exp_rgo {hs : ℕ → (Fin d → ℝ) → ℝ} {h : (Fin d → ℝ) → ℝ}
    {A B η : ℝ} (hcs : ∀ n, Continuous (hs n)) (hB : 0 ≤ B)
    (hlows : ∀ n x, -A - B * ‖x‖ ≤ hs n x) (hlim : ∀ x, Tendsto (fun n => hs n x) atTop (𝓝 (h x)))
    (hη : 0 < η) {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) {N : ℝ} (hN : ∀ x, |φ x| ≤ N)
    (y : Fin d → ℝ) :
    Tendsto (fun n => ∫ x, φ x * Real.exp (-hs n x - sqDist x y / (2 * η))) atTop
      (𝓝 (∫ x, φ x * Real.exp (-h x - sqDist x y / (2 * η)))) := by
  have hsq : Continuous fun x : Fin d → ℝ => sqDist x y :=
    continuous_sqDist.comp (continuous_id.prodMk continuous_const)
  refine tendsto_integral_of_dominated_convergence (fun x => N *
      (Real.exp (A + B * ‖y‖ + B ^ 2 * η) * Real.exp (-((4 * η)⁻¹ * sqDist x y))))
    (fun n => ?_) ((integrable_rgoDominator hη A B y).const_mul N)
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · have := hcs n
    exact (by fun_prop : Continuous fun x => φ x * Real.exp (-hs n x - sqDist x y / (2 * η)))
      |>.aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (hN x) (exp_rgo_le_of_lowerBound hB (hlows n) hη y x)
      (Real.exp_pos _).le ((abs_nonneg _).trans (hN x))
  · refine tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp ?_)
    exact ((hlim x).neg.sub tendsto_const_nhds)

/-- **Weak convergence of RGO kernels.** If continuous `h n → h` pointwise, all with a common
lower bound `-A - B ‖x‖` (`B ≥ 0`), and `η > 0`, then for every `y`,
`rgoKernelPi (h n) η y → rgoKernelPi h η y` weakly (integrals of bounded continuous functions
converge). No integrability of `e^{-h}` is assumed. -/
theorem weakTendsto_rgoKernelPi_of_tendsto {hs : ℕ → (Fin d → ℝ) → ℝ} {h : (Fin d → ℝ) → ℝ}
    {A B η : ℝ} (hcs : ∀ n, Continuous (hs n)) (hc : Continuous h) (hB : 0 ≤ B)
    (hlows : ∀ n x, -A - B * ‖x‖ ≤ hs n x) (hlow : ∀ x, -A - B * ‖x‖ ≤ h x)
    (hlim : ∀ x, Tendsto (fun n => hs n x) atTop (𝓝 (h x))) (hη : 0 < η) (y : Fin d → ℝ) :
    WeakTendsto (fun n => rgoKernelPi (hs n) η y) (rgoKernelPi h η y) := by
  intro φ hφ N hN
  simp_rw [integral_rgoKernelPi_of_continuous (hcs _), integral_rgoKernelPi_of_continuous hc]
  have hZ := tendsto_integral_mul_exp_rgo hcs hB hlows hlim hη (φ := fun _ => 1)
    continuous_const (N := 1) (fun _ => by norm_num) y
  simp only [one_mul] at hZ
  change Tendsto (fun n => rgoNormalizerPi (hs n) η y) atTop (𝓝 (rgoNormalizerPi h η y)) at hZ
  exact (tendsto_integral_mul_exp_rgo hcs hB hlows hlim hη hφ hN y).div hZ
    (rgoNormalizerPi_pos_of_lowerBound hc hB hlow hη y).ne'

end LowerBound

/-! ### Convex potentials -/

/-- **The RGO kernel of a convex potential is Markov.** For `f` convex on `Fin d → ℝ` and
`η > 0`, `rgoKernelPi f η` is a Markov kernel; `∫ e^{-f} < ∞` is not needed (a convex `f` is
continuous and `≥ -A - B ‖x‖`, so the Gaussian factor makes the RGO normaliser finite). -/
theorem isMarkovKernel_rgoKernelPi_of_convexOn {f : (Fin d → ℝ) → ℝ} (hf : ConvexOn ℝ univ f)
    {η : ℝ} (hη : 0 < η) : IsMarkovKernel (rgoKernelPi f η) := by
  obtain ⟨A, B, hB, hlow⟩ := exists_lowerBound_of_convexOn hf
  exact isMarkovKernel_rgoKernelPi_of_lowerBound (continuous_of_convexOn hf) hB hlow hη

/-- **Smooth convex approximation of the RGO kernel.** For `f` convex on `Fin d → ℝ` and
`η > 0` there are potentials `g n`, each convex, `C²`, with bounded gradient and bounded second
derivative (`SmoothConvexBdd`), such that for every `y` the RGO kernels converge weakly:
`rgoKernelPi (g n) η y → rgoKernelPi f η y` (integrals of bounded continuous functions). The
`g n` are mollified Pasch–Hausdorff envelopes of `f`; `∫ e^{-f} < ∞` is not assumed. -/
theorem exists_smoothConvexBdd_tendsto_rgoKernelPi {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ univ f) {η : ℝ} (hη : 0 < η) :
    ∃ g : ℕ → (Fin d → ℝ) → ℝ, (∀ n, SmoothConvexBdd (g n)) ∧
      ∀ y, WeakTendsto (fun n => rgoKernelPi (g n) η y) (rgoKernelPi f η y) := by
  obtain ⟨g, A, B, hg, hglow, hflow, hlim⟩ := exists_smooth_convex_approx hf
  obtain ⟨A', B', hB', -⟩ := exists_lowerBound_of_convexOn hf
  have hB : 0 ≤ max B B' := le_max_of_le_right hB'
  -- enlarge `B` to make it nonnegative
  have hmono : ∀ {u : ℝ}, ∀ x : Fin d → ℝ, -A - B * ‖x‖ ≤ u → -A - max B B' * ‖x‖ ≤ u :=
    fun x hu => le_trans (by nlinarith [le_max_left B B', norm_nonneg x]) hu
  refine ⟨g, fun n => hg n, fun y => ?_⟩
  exact weakTendsto_rgoKernelPi_of_tendsto (fun n => (hg n).2.1.continuous)
    (continuous_of_convexOn hf) hB (fun n x => hmono x (hglow n x)) (fun x => hmono x (hflow x))
    hlim hη y

end FormalizeSampling.RGOCouplingWeak
