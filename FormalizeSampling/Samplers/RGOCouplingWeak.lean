module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import FormalizeSampling.Samplers.RGOCouplingWeakDefs
public import FormalizeSampling.Foundations.KLJointLowerSemicontinuity
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Weak contractive couplings of a kernel and the `1/k` rate of the proximal sampler

Status: **Verified** (no named hypotheses).

The shifted-composition argument for the `1/k` KL rate only uses a coupling of the kernel
through the marginals of the coupled laws, data processing for KL and monotonicity of the
squared-distance cost. This file runs the argument from the interface `HasWeakCoupling K`
(`Samplers/RGOCouplingWeakDefs.lean`) and proves the closure properties used to establish it.
A pathwise `1`-Lipschitz representation gives a weak coupling
(`hasWeakCoupling_of_hasLipRep`, in `Samplers/ProximalLogConcaveRateGeneralPi.lean`).

## Main results

* `exists_limit_coupling` (compactness): if the four marginal sequences of probability laws
  `μ n, ν n` on `(Fin d → ℝ)²` converge weakly, `KL(μ n ‖ ν n) ≤ B` and eventually
  `∫ |x - y|² dμ n ≤ c`, there are limit laws `μ', ν'` with the limit marginals,
  `KL(μ' ‖ ν') ≤ B` and `∫ |x - y|² dμ' ≤ c`. Ingredients: tightness of convergent sequences,
  Prokhorov's theorem on pairs, joint lower semicontinuity of KL
  (`Foundations/KLJointLowerSemicontinuity.lean`) and lower semicontinuity of the cost.
  `exists_limit_coupling'` only needs the cost bound `c + δ` eventually, for each `δ > 0`.
* `hasWeakCoupling_of_forall_pos`: couplings with cost `≤ ∫ |x - y|² dμ + ε` for every
  `ε > 0` suffice.
* `hasWeakCoupling_of_tendsto`: `HasWeakCoupling` passes to pointwise weak limits of Markov
  kernels.
* `exists_shifted_step_weak`, `klDiv_iterate_le_shifted_of_weak`: shifted composition.
* `klDiv_iteratePi_le_div_of_hasWeakCoupling` (**main theorem**): if
  `HasWeakCoupling (rgoKernelPi f η)`, then for every `k`
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)` for any finite coupling `γ₀` of
  `(ρ 0, π)`.

## Not proved here

* `HasWeakCoupling (rgoKernelPi f η)` for convex `f`: see `Samplers/RGOCouplingLangevin.lean`
  and `Samplers/RGOCouplingApprox.lean`.
* Statements about the Wasserstein distance as an infimum over couplings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcaveRatePi
open scoped ENNReal NNReal BoundedContinuousFunction

namespace FormalizeSampling.RGOCouplingWeak

open FormalizeSampling.MeasureHelpers (integral_comp_markov)

section Abstract

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]

/-- A probability measure as an element of `ProbabilityMeasure`. -/
noncomputable def toPM (μ : Measure X) [IsProbabilityMeasure μ] : ProbabilityMeasure X :=
  ⟨μ, inferInstance⟩

/-- `WeakTendsto` is convergence in the weak topology of `ProbabilityMeasure`. -/
theorem weakTendsto_iff_tendsto {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)]
    {ν : Measure X} [IsProbabilityMeasure ν] :
    WeakTendsto μ ν ↔ Tendsto (fun n => toPM (μ n)) atTop (𝓝 (toPM ν)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f => h f f.continuous ‖f‖ fun x => ?_, fun h f hf N hN => ?_⟩
  · simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  · exact h (BoundedContinuousFunction.ofNormedAddCommGroup f hf N
      (fun x => by simpa [Real.norm_eq_abs] using hN x))

/-- Weak convergence in `ProbabilityMeasure` gives convergence of integrals of bounded
continuous functions, along any filter. -/
theorem forall_tendsto_integral_of_tendsto {ι : Type*} {l : Filter ι}
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} (h : Tendsto μ l (𝓝 ν)) :
    ∀ f : X → ℝ, Continuous f → ∀ N : ℝ, (∀ x, |f x| ≤ N) →
      Tendsto (fun i => ∫ x, f x ∂(μ i : Measure X)) l (𝓝 (∫ x, f x ∂(ν : Measure X))) :=
  fun f hf N hN => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf N
      (fun x => by simpa [Real.norm_eq_abs] using hN x))

variable [CompleteSpace X] [SecondCountableTopology X]

/-- A weakly convergent sequence of probability laws on a complete separable metric space is
tight. -/
theorem isTightMeasureSet_range_of_weakTendsto {μ : ℕ → Measure X}
    [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure X} [IsProbabilityMeasure ν]
    (h : WeakTendsto μ ν) : IsTightMeasureSet (range μ) := by
  have hc := (weakTendsto_iff_tendsto.1 h).isCompact_insert_range
  have := isTightMeasureSet_of_isCompact_closure (by rwa [hc.isClosed.closure_eq])
  refine this.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨toPM (μ n), mem_insert_of_mem _ ⟨n, rfl⟩, rfl⟩

end Abstract
variable {d : ℕ}

/-- Truncated squared distance as a bounded continuous `ℝ≥0`-valued function. -/
noncomputable def truncSqDist (M : ℕ) : ((Fin d → ℝ) × (Fin d → ℝ)) →ᵇ ℝ≥0 :=
  (BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : (Fin d → ℝ) × (Fin d → ℝ) => min (sqDist p.1 p.2) M)
    ((continuous_sqDist.comp (continuous_fst.prodMk continuous_snd)).min continuous_const) M
    (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sqDist_nonneg _ _) (Nat.cast_nonneg _))]
      exact min_le_right _ _)).nnrealPart

/-- Evaluation of the truncated squared distance. -/
theorem coe_truncSqDist (M : ℕ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    ((truncSqDist M p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (min (sqDist p.1 p.2) M) := by
  rfl

/-- The truncations increase to the squared distance. -/
theorem iSup_truncSqDist (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    ⨆ M : ℕ, ((truncSqDist M p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (sqDist p.1 p.2) := by
  simp_rw [coe_truncSqDist]
  refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  obtain ⟨M, hM⟩ := exists_nat_ge (sqDist p.1 p.2)
  exact le_iSup_of_le M (by rw [min_eq_left hM])

/-- **Lower semicontinuity of the squared-distance cost.** If `μ n → x` weakly and for every
`δ > 0` eventually `∫ |p₁ - p₂|² dμ n ≤ c + δ`, then `∫ |p₁ - p₂|² dx ≤ c`. -/
theorem sqCostPi_le_of_tendsto {μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))}
    {x : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))} (hx : Tendsto μ atTop (𝓝 x))
    {c : ℝ≥0∞}
    (hc : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ n in atTop,
      sqCostPi (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ≤ c + δ) :
    sqCostPi (x : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ≤ c := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hmeas : ∀ M : ℕ, Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ((truncSqDist M p : ℝ≥0) : ℝ≥0∞) :=
    fun M => (ENNReal.continuous_coe.comp (truncSqDist M).continuous).measurable
  have hmono : Monotone fun (M : ℕ) (p : (Fin d → ℝ) × (Fin d → ℝ)) =>
      ((truncSqDist M p : ℝ≥0) : ℝ≥0∞) := fun M N hMN p => by
    simp only [coe_truncSqDist]
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hMN))
  unfold sqCostPi
  simp_rw [← iSup_truncSqDist]
  rw [lintegral_iSup hmeas hmono]
  refine iSup_le fun M => ?_
  have hl := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hx (truncSqDist M)
  refine le_of_tendsto hl ((hc δ hδ).mono fun n hn => le_trans ?_ hn)
  refine lintegral_mono fun p => ?_
  rw [coe_truncSqDist]
  exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-- **Limit couplings, approximate cost bound.** As `exists_limit_coupling`, with the cost
hypothesis weakened to: for every `δ > 0`, eventually `∫ |x - y|² dμ n ≤ c + δ`. -/
theorem exists_limit_coupling' {μ ν : ℕ → Measure ((Fin d → ℝ) × (Fin d → ℝ))}
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    {a b a' b' : Measure (Fin d → ℝ)} [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    [IsProbabilityMeasure a'] [IsProbabilityMeasure b']
    (ha : WeakTendsto (fun n => (μ n).map Prod.fst) a)
    (hb : WeakTendsto (fun n => (μ n).map Prod.snd) b)
    (ha' : WeakTendsto (fun n => (ν n).map Prod.fst) a')
    (hb' : WeakTendsto (fun n => (ν n).map Prod.snd) b')
    {B c : ℝ≥0∞} (hKL : ∀ n, klDiv (μ n) (ν n) ≤ B)
    (hc : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ n in atTop, sqCostPi (μ n) ≤ c + δ) :
    ∃ μ' ν' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ' ∧
      IsProbabilityMeasure ν' ∧
      μ'.map Prod.fst = a ∧ μ'.map Prod.snd = b ∧ ν'.map Prod.fst = a' ∧
      ν'.map Prod.snd = b' ∧ klDiv μ' ν' ≤ B ∧ sqCostPi μ' ≤ c := by
  -- tightness of the pair laws
  have tight : ∀ (ρ : ℕ → Measure ((Fin d → ℝ) × (Fin d → ℝ)))
      [∀ n, IsProbabilityMeasure (ρ n)] {a b : Measure (Fin d → ℝ)} [IsProbabilityMeasure a]
      [IsProbabilityMeasure b], WeakTendsto (fun n => (ρ n).map Prod.fst) a →
      WeakTendsto (fun n => (ρ n).map Prod.snd) b →
      IsCompact (closure (range fun n => toPM (ρ n))) := by
    intro ρ _ a b _ _ h1 h2
    refine isCompact_closure_of_isTightMeasureSet ?_
    refine (show IsTightMeasureSet (range ρ) from ?_).subset ?_
    · refine IsTightMeasureSet.prodMk ((isTightMeasureSet_range_of_weakTendsto h1).subset ?_)
        ((isTightMeasureSet_range_of_weakTendsto h2).subset ?_)
      · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
  have hK := (tight μ ha hb).prod (tight ν ha' hb')
  obtain ⟨⟨x, y⟩, -, φ, hφ, hlim⟩ := hK.isSeqCompact (x := fun n => (toPM (μ n), toPM (ν n)))
    fun n => ⟨subset_closure ⟨n, rfl⟩, subset_closure ⟨n, rfl⟩⟩
  have hx : Tendsto (fun k => toPM (μ (φ k))) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hlim
  have hy : Tendsto (fun k => toPM (ν (φ k))) atTop (𝓝 y) := (continuous_snd.tendsto _).comp hlim
  -- identification of the marginals
  have marg : ∀ (ρ : ℕ → Measure ((Fin d → ℝ) × (Fin d → ℝ)))
      [∀ n, IsProbabilityMeasure (ρ n)] {z : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))}
      (f : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ) (hf : Continuous f)
      {a : Measure (Fin d → ℝ)} [IsProbabilityMeasure a],
      Tendsto (fun k => toPM (ρ (φ k))) atTop (𝓝 z) →
      WeakTendsto (fun n => (ρ n).map f) a → (z : Measure _).map f = a := by
    intro ρ _ z f hf a _ hz h
    have : ∀ n, IsProbabilityMeasure ((ρ n).map f) :=
      fun n => (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
    have h1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hz hf
    have h2 := ((weakTendsto_iff_tendsto (μ := fun n => (ρ n).map f)).1 h).comp
      hφ.tendsto_atTop
    have h3 := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique h1 h2)
    simpa [toPM] using h3
  refine ⟨x, y, inferInstance, inferInstance, marg μ _ continuous_fst hx ha,
    marg μ _ continuous_snd hx hb, marg ν _ continuous_fst hy ha',
    marg ν _ continuous_snd hy hb', ?_, ?_⟩
  · refine (KLLowerSemicontinuity.klDiv_le_liminf_of_tendsto_integral₂
      (μ := fun k => μ (φ k)) (π' := fun k => ν (φ k))
      (forall_tendsto_integral_of_tendsto hx) (forall_tendsto_integral_of_tendsto hy)).trans ?_
    exact liminf_le_of_frequently_le' (Frequently.of_forall fun k => hKL _)
  · exact sqCostPi_le_of_tendsto hx fun δ hδ => hφ.tendsto_atTop.eventually (hc δ hδ)

/-- **Limit couplings.** Let `μ n, ν n` be probability laws on `(Fin d → ℝ)²` whose four
marginal sequences converge weakly to probability laws `a, b` (of `μ n`) and `a', b'` (of `ν n`).
If `KL(μ n ‖ ν n) ≤ B` for all `n` and eventually `∫ |x - y|² dμ n ≤ c`, then there are
probability laws `μ', ν'` with marginals `a, b` and `a', b'`, `KL(μ' ‖ ν') ≤ B` and
`∫ |x - y|² dμ' ≤ c`. (Prokhorov for the pair laws, joint lower semicontinuity of KL, lower
semicontinuity of the cost.) -/
theorem exists_limit_coupling {μ ν : ℕ → Measure ((Fin d → ℝ) × (Fin d → ℝ))}
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    {a b a' b' : Measure (Fin d → ℝ)} [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    [IsProbabilityMeasure a'] [IsProbabilityMeasure b']
    (ha : WeakTendsto (fun n => (μ n).map Prod.fst) a)
    (hb : WeakTendsto (fun n => (μ n).map Prod.snd) b)
    (ha' : WeakTendsto (fun n => (ν n).map Prod.fst) a')
    (hb' : WeakTendsto (fun n => (ν n).map Prod.snd) b')
    {B c : ℝ≥0∞} (hKL : ∀ n, klDiv (μ n) (ν n) ≤ B)
    (hc : ∀ᶠ n in atTop, sqCostPi (μ n) ≤ c) :
    ∃ μ' ν' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ' ∧
      IsProbabilityMeasure ν' ∧
      μ'.map Prod.fst = a ∧ μ'.map Prod.snd = b ∧ ν'.map Prod.fst = a' ∧
      ν'.map Prod.snd = b' ∧ klDiv μ' ν' ≤ B ∧ sqCostPi μ' ≤ c :=
  exists_limit_coupling' ha hb ha' hb' hKL fun _ _ => hc.mono fun _ h => le_add_right h

/-- **Approximate couplings suffice.** Let `K` be a kernel on `Fin d → ℝ`. Assume that for all
probability laws `μ, ν` on `(Fin d → ℝ)²` and every real `ε > 0` there are probability laws
`μ', ν'` with marginals `K ∘ₘ μ₁, K ∘ₘ μ₂` and `K ∘ₘ ν₁, K ∘ₘ ν₂`,
`KL(μ' ‖ ν') ≤ KL(μ ‖ ν)` and `∫ |x - y|² dμ' ≤ ∫ |x - y|² dμ + ε`. Then `HasWeakCoupling K`
(the cost bound holds with `ε = 0`). -/
theorem hasWeakCoupling_of_forall_pos {K : Kernel (Fin d → ℝ) (Fin d → ℝ)}
    (h : ∀ μ ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ →
      IsProbabilityMeasure ν → ∀ ε : ℝ, 0 < ε →
      ∃ μ' ν' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ' ∧
        IsProbabilityMeasure ν' ∧
        μ'.map Prod.fst = K ∘ₘ μ.map Prod.fst ∧ μ'.map Prod.snd = K ∘ₘ μ.map Prod.snd ∧
        ν'.map Prod.fst = K ∘ₘ ν.map Prod.fst ∧ ν'.map Prod.snd = K ∘ₘ ν.map Prod.snd ∧
        klDiv μ' ν' ≤ klDiv μ ν ∧ sqCostPi μ' ≤ sqCostPi μ + ENNReal.ofReal ε) :
    HasWeakCoupling K := by
  intro μ ν hμ hν
  choose μ' ν' hμ' hν' h1 h2 h3 h4 hKL hc using
    fun n : ℕ => h μ ν hμ hν (1 / ((n : ℝ) + 1)) (by positivity)
  have : ∀ n, IsProbabilityMeasure (μ' n) := hμ'
  have : ∀ n, IsProbabilityMeasure (ν' n) := hν'
  have hpf : ∀ (ρ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure ρ],
      IsProbabilityMeasure (ρ.map Prod.fst) := fun ρ _ =>
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance
  have hps : ∀ (ρ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure ρ],
      IsProbabilityMeasure (ρ.map Prod.snd) := fun ρ _ =>
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (K ∘ₘ μ.map Prod.fst) := h1 0 ▸ hpf (μ' 0)
  have : IsProbabilityMeasure (K ∘ₘ μ.map Prod.snd) := h2 0 ▸ hps (μ' 0)
  have : IsProbabilityMeasure (K ∘ₘ ν.map Prod.fst) := h3 0 ▸ hpf (ν' 0)
  have : IsProbabilityMeasure (K ∘ₘ ν.map Prod.snd) := h4 0 ▸ hps (ν' 0)
  have wt : ∀ (ρ : ℕ → Measure (Fin d → ℝ)) (κ : Measure (Fin d → ℝ)), (∀ n, ρ n = κ) →
      WeakTendsto ρ κ := fun ρ κ h f _ _ _ => by simp_rw [h]; exact tendsto_const_nhds
  refine exists_limit_coupling' (wt _ _ h1) (wt _ _ h2) (wt _ _ h3) (wt _ _ h4) hKL
    fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (δ : ℝ))
  have hδ' : (0 : ℝ) < δ := hδ
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (hc n).trans (add_le_add_right (ENNReal.ofReal_le_of_le_toReal ?_) _)
  rw [ENNReal.coe_toReal, div_le_iff₀ (by positivity)]
  have h1 : 1 < (N : ℝ) * δ := (div_lt_iff₀ hδ').1 hN
  have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- **Mixtures converge weakly.** If Markov kernels `K n` converge weakly to `K₀` at every
point, then `K n ∘ₘ m → K₀ ∘ₘ m` weakly for every probability law `m` (dominated
convergence). -/
theorem weakTendsto_comp {K : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)}
    [∀ n, IsMarkovKernel (K n)] {K₀ : Kernel (Fin d → ℝ) (Fin d → ℝ)} [IsMarkovKernel K₀]
    (hlim : ∀ y, WeakTendsto (fun n => K n y) (K₀ y)) (m : Measure (Fin d → ℝ))
    [IsProbabilityMeasure m] : WeakTendsto (fun n => K n ∘ₘ m) (K₀ ∘ₘ m) := by
  intro f hf N hN
  simp_rw [integral_comp_markov _ m hf hN]
  have hb : ∀ (κ : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsMarkovKernel κ] (y : Fin d → ℝ),
      ‖∫ x, f x ∂κ y‖ ≤ N := fun κ _ y => by
    have := norm_integral_le_of_norm_le_const (μ := κ y) (C := N)
      (Eventually.of_forall fun x => (Real.norm_eq_abs (f x)).trans_le (hN x))
    simpa using this
  refine tendsto_integral_of_dominated_convergence (fun _ => N)
    (fun n => (hf.stronglyMeasurable.integral_kernel (κ := K n)).aestronglyMeasurable)
    (integrable_const N) (fun n => Eventually.of_forall (hb (K n)))
    (Eventually.of_forall fun y => hlim y f hf N hN)

/-- **Weak limits of kernels.** Let `K n` be Markov kernels on `Fin d → ℝ` with
`HasWeakCoupling (K n)` for every `n`, and `K₀` a Markov kernel with `K n y → K₀ y` weakly for
every `y`. Then `HasWeakCoupling K₀`. -/
theorem hasWeakCoupling_of_tendsto {K : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)}
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, HasWeakCoupling (K n))
    {K₀ : Kernel (Fin d → ℝ) (Fin d → ℝ)} [IsMarkovKernel K₀]
    (hlim : ∀ y, WeakTendsto (fun n => K n y) (K₀ y)) : HasWeakCoupling K₀ := by
  intro μ ν hμ hν
  choose μ' ν' hμ' hν' h1 h2 h3 h4 hKL hc using fun n => hK n μ ν hμ hν
  have : ∀ n, IsProbabilityMeasure (μ' n) := hμ'
  have : ∀ n, IsProbabilityMeasure (ν' n) := hν'
  have hw : ∀ (ρ : ℕ → Measure ((Fin d → ℝ) × (Fin d → ℝ))) (q : Measure (Fin d → ℝ))
      [IsProbabilityMeasure q] (g : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ),
      (∀ n, (ρ n).map g = K n ∘ₘ q) → WeakTendsto (fun n => (ρ n).map g) (K₀ ∘ₘ q) :=
    fun ρ q _ g h => by
      rw [show (fun n => (ρ n).map g) = fun n => K n ∘ₘ q from funext h]
      exact weakTendsto_comp hlim q
  have hpf : IsProbabilityMeasure (μ.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance
  have hps : IsProbabilityMeasure (μ.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  have hpf' : IsProbabilityMeasure (ν.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance
  have hps' : IsProbabilityMeasure (ν.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  exact exists_limit_coupling (hw _ _ _ h1) (hw _ _ _ h2) (hw _ _ _ h3) (hw _ _ _ h4) hKL
    (Eventually.of_forall hc)

section Shifted

open FormalizeSampling.ProximalLogConcavePi FormalizeSampling.ProximalLogConcaveRateGeneralPi

/-- The cost of the shifted noisy pair law: for `(p, n) ∼ Λ ⊗ₘ gaussNoise η c`,
`∫ |x - y|² d(shiftNoise t)_# = (1 - t)² ∫ |x - y|² dΛ`. -/
theorem sqCostPi_map_shiftNoise (η c t : ℝ) (Λ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    [IsFiniteMeasure Λ] :
    sqCostPi ((Λ ⊗ₘ gaussNoise η c).map (shiftNoise t))
      = ENNReal.ofReal ((1 - t) ^ 2) * sqCostPi Λ := by
  unfold sqCostPi
  rw [lintegral_map measurable_ofReal_sqDist (measurable_shiftNoise t)]
  have e : ∀ z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin d → ℝ),
      ENNReal.ofReal (sqDist (shiftNoise t z).1 (shiftNoise t z).2)
        = ENNReal.ofReal ((1 - t) ^ 2) * ENNReal.ofReal (sqDist z.1.1 z.1.2) := fun z => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold sqDist
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [shiftNoise, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  calc _ = ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2) ∂((Λ ⊗ₘ gaussNoise η c).map Prod.fst) :=
        (lintegral_map measurable_ofReal_sqDist measurable_fst).symm
    _ = _ := by rw [← Measure.fst, Measure.fst_compProd]

/-- **One shifted step from a weak coupling.** Let `K` be a kernel on `Fin d → ℝ` with
`HasWeakCoupling K`, `η > 0`, `t : ℝ`, `Λ, Γ` probability laws on `(Fin d → ℝ)²`,
`P = K ∘ₖ N_η`. There are probability laws `Λ', Γ'` with `Λ'₁ = P ∘ₘ Λ₁`, `Γ'₂ = P ∘ₘ Γ₂`,
`Γ'₁ = Γ'₂` if `t = 1`, `KL(Λ' ‖ Γ') ≤ KL(Λ ‖ Γ) + t² / (2η) · ∫⁻ |x - y|² dΛ`, and
`∫⁻ |x - y|² dΛ' ≤ (1 - t)² ∫⁻ |x - y|² dΛ`. -/
theorem exists_shifted_step_weak {K : Kernel (Fin d → ℝ) (Fin d → ℝ)} (hK : HasWeakCoupling K)
    {η : ℝ} (hη : 0 < η) (t : ℝ) (Λ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    [IsProbabilityMeasure Λ] [IsProbabilityMeasure Γ] :
    ∃ Λ' Γ' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure Λ' ∧
      IsProbabilityMeasure Γ' ∧
      Λ'.map Prod.fst = (K ∘ₖ forwardKernelPi η) ∘ₘ Λ.map Prod.fst ∧
      Γ'.map Prod.snd = (K ∘ₖ forwardKernelPi η) ∘ₘ Γ.map Prod.snd ∧
      (t = 1 → Γ'.map Prod.fst = Γ'.map Prod.snd) ∧
      klDiv Λ' Γ' ≤ klDiv Λ Γ + ENNReal.ofReal (t ^ 2 / (2 * η)) * sqCostPi Λ ∧
      sqCostPi Λ' ≤ ENNReal.ofReal ((1 - t) ^ 2) * sqCostPi Λ := by
  have hS := measurable_shiftNoise (d := d) t
  set μΛ := (Λ ⊗ₘ gaussNoise η 0).map (shiftNoise t)
  set μΓ := (Γ ⊗ₘ gaussNoise η t).map (shiftNoise t)
  have : IsProbabilityMeasure μΛ :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure μΓ :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
  obtain ⟨Λ', Γ', hΛ', hΓ', h1, -, h3, h4, hKL, hc⟩ := hK μΛ μΓ inferInstance inferInstance
  refine ⟨Λ', Γ', hΛ', hΓ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, Measure.map_map measurable_fst hS, ← Measure.comp_assoc]
    congr 1
    have e : Prod.fst ∘ shiftNoise (d := d) t =
        fun z => Prod.fst z.1 + z.2 - (0 : ℝ) • (z.1.2 - z.1.1) := by
      funext z
      simp [shiftNoise]
    rw [e]
    exact map_compProd_gaussNoise η Λ 0 measurable_fst
  · rw [h4, Measure.map_map measurable_snd hS, ← Measure.comp_assoc]
    congr 1
    exact map_compProd_gaussNoise η Γ t measurable_snd
  · rintro rfl
    rw [h3, h4, Measure.map_map measurable_fst hS, Measure.map_map measurable_snd hS]
    congr 2
    funext z
    simp only [Function.comp, shiftNoise, one_smul]
    rw [show z.1.2 + z.2 - (z.1.2 - z.1.1) = z.1.1 + z.2 by abel]
  · refine hKL.trans ((klDiv_map_le _ _ hS).trans ?_)
    rw [KL.klDiv_compProd_eq_add_lintegral]
    simp_rw [klDiv_gaussNoise hη t]
    rw [lintegral_const_mul _ measurable_ofReal_sqDist]
    rfl
  · exact hc.trans_eq (sqCostPi_map_shiftNoise η 0 t Λ)

/-- **Shifted composition bound from a weak coupling.** Let `K` be a kernel on `Fin d → ℝ`
with `HasWeakCoupling K`, `η > 0`, `P = K ∘ₖ N_η`, and `Λ, Γ` probability laws on
`(Fin d → ℝ)²`. Then for every `k`:
`KL(P^{k+1} Λ₁ ‖ P^{k+1} Γ₂) ≤ KL(Λ ‖ Γ) + ∫⁻ |x - y|² dΛ / (2 (k + 1) η)`. -/
theorem klDiv_iterate_le_shifted_of_weak {K : Kernel (Fin d → ℝ) (Fin d → ℝ)}
    (hK : HasWeakCoupling K) {η : ℝ} (hη : 0 < η)
    (k : ℕ) (Λ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsProbabilityMeasure Λ]
    [IsProbabilityMeasure Γ] :
    klDiv ((fun ν => (K ∘ₖ forwardKernelPi η) ∘ₘ ν)^[k + 1] (Λ.map Prod.fst))
        ((fun ν => (K ∘ₖ forwardKernelPi η) ∘ₘ ν)^[k + 1] (Γ.map Prod.snd))
      ≤ klDiv Λ Γ + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * sqCostPi Λ := by
  induction k generalizing Λ Γ with
  | zero =>
    obtain ⟨Λ', Γ', hΛ', hΓ', h1, h2, h3, h4, -⟩ := exists_shifted_step_weak hK hη 1 Λ Γ
    simp only [zero_add, Function.iterate_one]
    rw [← h1, ← h2, ← h3 rfl]
    refine (klDiv_map_le _ _ measurable_fst).trans (h4.trans_eq ?_)
    norm_num
  | succ k ih =>
    set t : ℝ := 1 / ((k : ℝ) + 2) with ht
    obtain ⟨Λ', Γ', hΛ', hΓ', h1, h2, -, h4, h5⟩ := exists_shifted_step_weak hK hη t Λ Γ
    rw [Function.iterate_succ_apply _ (k + 1) (Λ.map Prod.fst),
      Function.iterate_succ_apply _ (k + 1) (Γ.map Prod.snd), ← h1, ← h2]
    refine (ih Λ' Γ').trans ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc klDiv Λ' Γ' + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * sqCostPi Λ'
        ≤ (klDiv Λ Γ + ENNReal.ofReal (t ^ 2 / (2 * η)) * sqCostPi Λ)
          + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η))
            * (ENNReal.ofReal ((1 - t) ^ 2) * sqCostPi Λ) := by gcongr
      _ = klDiv Λ Γ + (ENNReal.ofReal (t ^ 2 / (2 * η))
          + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * ENNReal.ofReal ((1 - t) ^ 2))
            * sqCostPi Λ := by ring
      _ = klDiv Λ Γ + ENNReal.ofReal (1 / (2 * (((k + 1 : ℕ) : ℝ) + 1) * η)) * sqCostPi Λ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 3
        rw [ht]
        push_cast
        field_simp
        ring

/-- **`1/k` KL rate of the proximal sampler from a weak RGO coupling.** Let
`f : (Fin d → ℝ) → ℝ` be measurable with `∫ e^{-f} < ∞`, `π = targetPi f`, `η > 0`, and assume
`HasWeakCoupling (rgoKernelPi f η)`. Let `ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k` and `γ₀` be any
finite coupling of `(ρ 0, π)`. Then for every `k`:
`KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`. -/
theorem klDiv_iteratePi_le_div_of_hasWeakCoupling {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hint : Integrable fun x => Real.exp (-f x)) {η : ℝ} (hη : 0 < η)
    (hK : HasWeakCoupling (rgoKernelPi f η))
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi f)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * ((k : ℝ) + 1) * η)) ∂γ₀ := by
  have := isProbabilityMeasure_targetPi hint
  have : IsProbabilityMeasure γ₀ := ⟨by
    have h : (γ₀.map Prod.snd) univ = 1 := by rw [h₂]; exact measure_univ
    rwa [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ] at h⟩
  have hfix : (fun ν => proxKernelPi f η ∘ₘ ν)^[k + 1] (targetPi f) = targetPi f :=
    Function.iterate_fixed (proxKernelPi_comp_targetPi hf hint hη) _
  have h := klDiv_iterate_le_shifted_of_weak hK hη k γ₀ γ₀
  rw [h₁, h₂, klDiv_self, zero_add] at h
  rw [ProximalLogConcaveRate.eq_iterate _ ρ hstep, ← hfix]
  refine h.trans_eq ?_
  rw [sqCostPi, ← lintegral_const_mul _ measurable_ofReal_sqDist]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end Shifted

end FormalizeSampling.RGOCouplingWeak
