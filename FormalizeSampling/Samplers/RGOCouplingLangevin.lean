module

public import FormalizeSampling.Samplers.RGOCouplingLangevinKernel
public import FormalizeSampling.Samplers.RGOCouplingWeak

/-!
# Weak contractive couplings of the RGO kernel of a smooth convex potential

Status: **Verified** (no named hypotheses).

For `g` convex, `C²`, with bounded first and second derivatives (`SmoothConvexBdd g`) and
`η > 0`, the RGO kernel `rgoKernelPi g η` has a weak contractive coupling
(`RGOCouplingWeak.HasWeakCoupling`). Route: the RGO law `RGO(y)` is stationary for the Langevin
dynamics `dX = (-∇g(X) - (X - y)/η) dt + √2 dW`, and the dyadic Euler–Maruyama laws started at
`RGO(y)` converge weakly back to `RGO(y)` (`Samplers/RGOCouplingLangevinStationary.lean`). Two
Euler–Maruyama chains for `y, y'` driven by the same Gaussian increments contract
(`Samplers/RGOCouplingLangevinContraction.lean`), so after `N(y, y')` steps from the
independent coupling the cost is at most `|y - y'|² + ε`
(`Samplers/RGOCouplingLangevinKernel.lean`). Pushing `μ, ν` through the same coupling kernel
does not increase KL (data processing); letting the step `2⁻ⁿ → 0`, Prokhorov
(`RGOCouplingWeak.exists_limit_coupling`) gives exact marginals.

## Main results

* `RGOCouplingLangevin.weakTendsto_comp_of_forall`: mixtures of pointwise weakly convergent
  kernels converge weakly.
* `RGOCouplingLangevin.exists_coupling_add_of_smoothConvexBdd`: approximate couplings with
  cost `≤ ∫ |x - y|² dμ + ε`.
* `RGOCouplingWeak.hasWeakCoupling_rgoKernelPi_of_smoothConvexBdd`:
  `SmoothConvexBdd g → 0 < η → HasWeakCoupling (rgoKernelPi g η)`.

## Not proved here

* A pathwise `1`-Lipschitz representation (`RGOCouplingPi.HasLipRep`) of the RGO kernel.
* Non-smooth convex potentials (they are reached by approximation elsewhere).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcaveRatePi
open FormalizeSampling.RGOCouplingWeak
open FormalizeSampling.FokkerPlanckExistence (emStep emPow stepVar emCurve dyadicStep gridIndex)
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingLangevin

variable {d : ℕ} {g : (Fin d → ℝ) → ℝ} {η : ℝ}

/-- **Mixtures of weakly convergent kernels converge weakly.** If `κₙ p → κ₀ p` weakly for every
`p`, then `κₙ ∘ₘ μ → κ₀ ∘ₘ μ` weakly (dominated convergence; Markov kernels, `μ` a probability
measure). -/
theorem weakTendsto_comp_of_forall {P : Type*} [MeasurableSpace P]
    {κ : ℕ → Kernel P (Fin d → ℝ)} [∀ n, IsMarkovKernel (κ n)] {κ₀ : Kernel P (Fin d → ℝ)}
    [IsMarkovKernel κ₀] (μ : Measure P) [IsProbabilityMeasure μ]
    (h : ∀ p, WeakTendsto (fun n => κ n p) (κ₀ p)) :
    WeakTendsto (fun n => κ n ∘ₘ μ) (κ₀ ∘ₘ μ) := by
  intro f hf N hN
  have hbd : ∀ x, ‖f x‖ ≤ N := fun x => by rw [Real.norm_eq_abs]; exact hN x
  have e : ∀ (κ' : Kernel P (Fin d → ℝ)) [IsMarkovKernel κ'],
      ∫ x, f x ∂(κ' ∘ₘ μ) = ∫ p, ∫ x, f x ∂(κ' p) ∂μ := fun κ' _ => by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp
      (Integrable.of_bound hf.aestronglyMeasurable N (ae_of_all _ hbd)), Kernel.const_apply]
  simp_rw [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => N) (fun n => ?_)
    (integrable_const N) (fun n => ae_of_all _ fun p => ?_) (ae_of_all _ fun p => h p f hf N hN)
  · exact (hf.measurable.stronglyMeasurable.integral_kernel (κ := κ n)).aestronglyMeasurable
  · have := norm_integral_le_of_norm_le_const (μ := κ n p) (ae_of_all _ hbd)
    simpa using this

/-- **Marginals of the coupling with step `2⁻ⁿ`**: the dyadic EM law of `b_y` from `RGO(y)` at
time `T(y, y')`. -/
theorem syncCouplingN_map_fst (hg : SmoothConvexBdd g) (hη : 0 < η) (ε : ℝ) (n : ℕ)
    (hN : Measurable (coupSteps (d := d) g η ε n)) (p : (Fin d → ℝ) × (Fin d → ℝ))
    (hb : Measurable (rgoDrift g η p.1)) :
    (syncCouplingN g η (dyadicStep n) (coupSteps g η ε n) hN p).map Prod.fst =
      emCurve (rgoDrift g η p.1) hb 1 (rgoKernelPi g η p.1) n (coupTime g η ε p) := by
  rw [syncCouplingN_apply, syncCoupling_map_fst _ hg hη _ p hb]
  rfl

/-- Second marginal of the coupling with step `2⁻ⁿ`. -/
theorem syncCouplingN_map_snd (hg : SmoothConvexBdd g) (hη : 0 < η) (ε : ℝ) (n : ℕ)
    (hN : Measurable (coupSteps (d := d) g η ε n)) (p : (Fin d → ℝ) × (Fin d → ℝ))
    (hb : Measurable (rgoDrift g η p.2)) :
    (syncCouplingN g η (dyadicStep n) (coupSteps g η ε n) hN p).map Prod.snd =
      emCurve (rgoDrift g η p.2) hb 1 (rgoKernelPi g η p.2) n (coupTime g η ε p) := by
  rw [syncCouplingN_apply, syncCoupling_map_snd _ hg hη _ p hb]
  rfl

/-- **Approximate synchronous coupling of RGO laws (for a fixed tolerance `ε > 0`).** For `g`
smooth convex with bounded derivatives, `η > 0`, probability laws `μ, ν` on pairs and `ε > 0`,
there are probability laws `μ', ν'` on pairs with marginals `RGO ∘ₘ μ₁, RGO ∘ₘ μ₂` and
`RGO ∘ₘ ν₁, RGO ∘ₘ ν₂`, `KL(μ' ‖ ν') ≤ KL(μ ‖ ν)` and
`∫ |x - y|² dμ' ≤ ∫ |x - y|² dμ + ε`. The laws are limits (Prokhorov) of the synchronous
Euler–Maruyama couplings `syncCouplingN` with steps `2⁻ⁿ` applied to `μ` and `ν`. -/
theorem exists_coupling_add_of_smoothConvexBdd (hg : SmoothConvexBdd g) (hη : 0 < η)
    (μ ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε) :
    ∃ μ' ν' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ' ∧
      IsProbabilityMeasure ν' ∧
      μ'.map Prod.fst = rgoKernelPi g η ∘ₘ μ.map Prod.fst ∧
      μ'.map Prod.snd = rgoKernelPi g η ∘ₘ μ.map Prod.snd ∧
      ν'.map Prod.fst = rgoKernelPi g η ∘ₘ ν.map Prod.fst ∧
      ν'.map Prod.snd = rgoKernelPi g η ∘ₘ ν.map Prod.snd ∧
      klDiv μ' ν' ≤ klDiv μ ν ∧ sqCostPi μ' ≤ sqCostPi μ + ENNReal.ofReal ε := by
  have hK := isMarkovKernel_rgoKernelPi' hg hη
  have hN : ∀ n, Measurable (coupSteps (d := d) g η ε n) := measurable_coupSteps hg hη ε
  set C : ℕ → Kernel ((Fin d → ℝ) × (Fin d → ℝ)) ((Fin d → ℝ) × (Fin d → ℝ)) :=
    fun n => syncCouplingN g η (dyadicStep n) (coupSteps g η ε n) (hN n) with hC
  have hCM : ∀ n, IsMarkovKernel (C n) := fun n => isMarkovKernel_syncCouplingN _ hg hη _ _
  have hb : ∀ y, Measurable (rgoDrift g η y) := fun y =>
    (continuous_rgoDrift hg.2.1 η y).measurable
  have hT : ∀ p, 0 ≤ coupTime g η ε p := fun p => zero_le_one.trans (one_le_coupTime hη hε p)
  -- weak convergence of the marginals
  have hpf : ∀ (ρ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure ρ],
      IsProbabilityMeasure (ρ.map Prod.fst) := fun ρ _ =>
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance
  have hps : ∀ (ρ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure ρ],
      IsProbabilityMeasure (ρ.map Prod.snd) := fun ρ _ =>
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  have hfst : ∀ (ρ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure ρ],
      WeakTendsto (fun n => (C n ∘ₘ ρ).map Prod.fst) (rgoKernelPi g η ∘ₘ ρ.map Prod.fst) := by
    intro ρ _
    have : ∀ n, IsMarkovKernel ((C n).map Prod.fst) := fun n =>
      Kernel.IsMarkovKernel.map _ measurable_fst
    simp_rw [Measure.map_comp _ _ measurable_fst, comp_map_eq _ _ measurable_fst]
    refine weakTendsto_comp_of_forall ρ fun p => ?_
    simp_rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply, hC,
      syncCouplingN_map_fst hg hη ε _ (hN _) p (hb p.1)]
    exact weakTendsto_emCurve_rgoKernelPi hg hη p.1 (hb p.1) (hT p)
  have hsnd : ∀ (ρ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure ρ],
      WeakTendsto (fun n => (C n ∘ₘ ρ).map Prod.snd) (rgoKernelPi g η ∘ₘ ρ.map Prod.snd) := by
    intro ρ _
    have : ∀ n, IsMarkovKernel ((C n).map Prod.snd) := fun n =>
      Kernel.IsMarkovKernel.map _ measurable_snd
    simp_rw [Measure.map_comp _ _ measurable_snd, comp_map_eq _ _ measurable_snd]
    refine weakTendsto_comp_of_forall ρ fun p => ?_
    simp_rw [Kernel.map_apply _ measurable_snd, Kernel.comap_apply, hC,
      syncCouplingN_map_snd hg hη ε _ (hN _) p (hb p.2)]
    exact weakTendsto_emCurve_rgoKernelPi hg hη p.2 (hb p.2) (hT p)
  -- the cost bound, for small steps
  obtain ⟨L, hL0, hL⟩ := exists_fderiv_fderiv_bound hg
  have hL1 : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L + 1 := fun x => (hL x).trans (by linarith)
  have hstep : Tendsto (fun n => dyadicStep n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev1 : ∀ᶠ n in atTop, dyadicStep n < η / 2 := (tendsto_order.1 hstep).2 _ (by positivity)
  have hev2 : ∀ᶠ n in atTop, dyadicStep n < 1 / (L + 1) :=
    (tendsto_order.1 hstep).2 _ (by positivity)
  have hc : ∀ᶠ n in atTop, sqCostPi (C n ∘ₘ μ) ≤ sqCostPi μ + ENNReal.ofReal ε := by
    filter_upwards [hev1, hev2] with n h1 h2
    have hh0 : 0 ≤ dyadicStep n := by unfold dyadicStep; positivity
    have hhL : dyadicStep n * (L + 1) ≤ 1 := by
      rw [lt_div_iff₀ (by linarith)] at h2; exact h2.le
    unfold sqCostPi
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) measurable_ofReal_sqDist.aemeasurable]
    refine (lintegral_mono (g := fun p => ENNReal.ofReal (sqDist p.1 p.2) + ENNReal.ofReal ε)
      fun p => ?_).trans (by rw [lintegral_add_right _ measurable_const, lintegral_const,
        measure_univ, mul_one])
    rw [hC, syncCouplingN_apply]
    refine (lintegral_sqDist_syncCoupling_le _ hg (by linarith) hL1 hη hh0 h1.le hhL _ p).trans ?_
    rw [add_comm]
    exact add_le_add le_rfl (ofReal_pow_mul_indepCost_le hg hη hε (by linarith) p)
  have := hpf μ; have := hps μ; have := hpf ν; have := hps ν
  exact exists_limit_coupling (μ := fun n => C n ∘ₘ μ) (ν := fun n => C n ∘ₘ ν)
    (hfst μ) (hsnd μ) (hfst ν) (hsnd ν) (fun n => klDiv_comp_right_le _ _ (C n)) hc

end FormalizeSampling.RGOCouplingLangevin

namespace FormalizeSampling.RGOCouplingWeak

open FormalizeSampling.RGOCouplingLangevin

variable {d : ℕ} {g : (Fin d → ℝ) → ℝ} {η : ℝ}

/-- **Weak contractive coupling of the RGO kernel of a smooth convex potential.** If `g` is
convex and `C²` on `Fin d → ℝ` with bounded first and second derivatives (`SmoothConvexBdd g`;
no integrability of `e^{-g}` is assumed) and `η > 0`, then the RGO kernel
`y ↦ RGO(y) ∝ exp(-g(x) - |x - y|² / (2η)) dx` has a weak contractive coupling
(`HasWeakCoupling`): for all probability laws `μ, ν` on pairs there are laws `μ', ν'` with the
four marginals pushed through the kernel, `KL(μ' ‖ ν') ≤ KL(μ ‖ ν)` and
`∫ |x - y|² dμ' ≤ ∫ |x - y|² dμ`. -/
theorem hasWeakCoupling_rgoKernelPi_of_smoothConvexBdd (hg : SmoothConvexBdd g) (hη : 0 < η) :
    HasWeakCoupling (rgoKernelPi g η) :=
  hasWeakCoupling_of_forall_pos fun μ ν _ _ _ hε =>
    exists_coupling_add_of_smoothConvexBdd hg hη μ ν hε

end FormalizeSampling.RGOCouplingWeak
