module

public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.CDF
public import FormalizeSampling.Samplers.ProximalRegularization

/-!
# The exact proximal sampler for merely log-concave targets on `ℝ`

Status: **Verified** (no named hypotheses).

Setting (as in `Samplers/Proximal.lean`): target `π = target f ∝ e^{-f}` on `ℝ` with `f`
**convex** (no strong convexity, no log-Sobolev inequality) and `∫ e^{-f} < ∞`; step `η > 0`
(the **variance** of the forward Gaussian); `proxKernel f η = rgoKernel f η ∘ₖ forwardKernel η`.
Couplings are expressed without a Wasserstein-space library: a coupling of `(ρ, μ)` is a finite
measure `γ` on `ℝ × ℝ` with `γ.map Prod.fst = ρ`, `γ.map Prod.snd = μ`. Transport costs are
`∫⁻ φ(|x - y|) dγ` for any measurable `φ : ℝ → ℝ≥0∞` monotone on `[0, ∞)` (e.g.
`φ r = ofReal (r² / (2η))`).

## Construction: quantile (monotone) couplings of a stochastically monotone kernel

* `unif` is the uniform law on `(0, 1)`; `qf μ u = inf {t | u ≤ F_μ(t)}` (for `u ∈ (0, 1)`) is the
  quantile function of a probability law `μ` on `ℝ`. `qf_le_iff`: `qf μ u ≤ t ↔ u ≤ F_μ(t)`;
  `map_qf`: `unif.map (qf μ) = μ`; `measurable_qf_kernel`: `(a, u) ↦ qf (κ a) u` is
  measurable (Markov `κ`).
* `CDFShiftMonotone κ`: for `y ≤ y'`, `F_{κ y'} ≤ F_{κ y}` (stochastic monotonicity) and
  `F_{κ y}(t) ≤ F_{κ y'}(t + (y' - y))` (the law moves by at most the input displacement).
  `abs_qf_sub_le`: then `|qf (κ y) u - qf (κ y') u| ≤ |y - y'|` for every `u ∈ (0, 1)`.
* `qCoupling κ γ = (γ ⊗ unif).map ((y, y', u) ↦ (qf (κ y) u, qf (κ y') u))`:
  `exists_coupling_comp` gives a coupling of `(κ ∘ₘ ρ, κ ∘ₘ μ)` whose cost does not exceed that
  of `γ` (`lintegral_qCoupling_le`).

## Main results

* `cdfShiftMonotone_forwardKernel`: the Gaussian forward kernel is `CDFShiftMonotone`.
* `cdfShiftMonotone_rgoKernel` (**convex `f`**): the RGO kernel is `CDFShiftMonotone`. The proof
  is a monotone-likelihood-ratio comparison (`mul_setIntegral_Iic_le`): the RGO densities
  `r_y ∝ e^{-f(x) - (x - y)²/(2η)}` satisfy `r_{y'}/r_y` nondecreasing (any `f`), and
  `r_{y'}(· + h)/r_y` nonincreasing for `h = y' - y ≥ 0` (this uses convexity of `f`:
  `f(s + h) + f(t) ≤ f(s) + f(t + h)` for `s ≤ t`, `add_le_add_of_convexOn`).
* `exists_coupling_proxKernel` (**W-nonexpansiveness**, convex `f`): every coupling `γ` of
  `(ρ, μ)` yields a coupling `γ'` of `(proxKernel f η ∘ₘ ρ, proxKernel f η ∘ₘ μ)` with
  `∫⁻ φ(|x - y|) dγ' ≤ ∫⁻ φ(|x - y|) dγ`.
* `exists_coupling_iterate`: for the iterates `ρ (k + 1) = proxKernel f η ∘ₘ ρ k` and a coupling
  `γ₀` of `(ρ 0, π)`, every `ρ k` admits a coupling with `π` of cost at most that of `γ₀`.
* `klDiv_iterate_le_coupling` (**main theorem**): for every `k`,
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ (x - y)² / (2η) dγ₀(x, y)` (combined with
  `ProximalRegularization.klDiv_proxKernel_comp_le_coupling`).

## Not proved here

* The `1/k` rate `KL(ρ_k ‖ π) ≤ ∫ (x - y)² dγ₀ / (k η)` of Chen–Chewi–Salim–Wibisono (2022) for
  log-concave targets: only the `k`-uniform bound `∫ (x - y)² dγ₀ / (2η)` is proved here. The
  `1/k` rate (constant `1/(2kη)`) is `ProximalLogConcaveRate.klDiv_iterate_le_div`, by shifted
  composition rather than an EVI-type inequality (which is not formalised).
* The `d`-dimensional analogue of the coupling contraction for general convex `f` (the
  quantile coupling is specific to dimension one; a weak contractive coupling is
  `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn`); the
  regularisation bound itself is available in dimension `d`
  (`ProximalRegularization.klDiv_proxKernelPi_comp_le_coupling`).
* Statements about the Wasserstein distance as an infimum over couplings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.Proximal
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcave

/-! ### The uniform law and quantile functions -/

/-- The uniform law on `(0, 1)`: Lebesgue measure restricted to `Ioo 0 1`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Ioo 0 1)

/-- The uniform law on `(0, 1)` is a probability measure. -/
instance isProbabilityMeasure_unif : IsProbabilityMeasure unif :=
  ⟨by simp [unif]⟩

open Classical in
/-- The quantile function of a law `μ` on `ℝ`: `qf μ u = inf {t | u ≤ F_μ(t)}` for
`u ∈ (0, 1)` (with `F_μ = cdf μ`), and `0` otherwise. -/
noncomputable def qf (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then sInf {t | u ≤ cdf μ t} else 0

/-- **Galois property of the quantile function.** For `u ∈ (0, 1)` and every `t`:
`qf μ u ≤ t ↔ u ≤ F_μ(t)`. -/
theorem qf_le_iff (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    qf μ u ≤ t ↔ u ≤ cdf μ t := by
  have hne : {t | u ≤ cdf μ t}.Nonempty := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hu.2)).exists
    exact ⟨b, hb.le⟩
  have hbdd : BddBelow {t | u ≤ cdf μ t} := by
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hu.1)).exists
    refine ⟨a, fun s hs => ?_⟩
    by_contra h
    push Not at h
    have := monotone_cdf μ h.le
    change u ≤ cdf μ s at hs
    linarith
  have hmem : u ≤ cdf μ (sInf {t | u ≤ cdf μ t}) := by
    have hc := ((cdf μ).right_continuous (sInf {t | u ≤ cdf μ t})).mono Ioi_subset_Ici_self
    refine ge_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
    exact hs.trans (monotone_cdf μ hsx.le)
  simp only [qf, hu, ↓reduceIte]
  exact ⟨fun h => hmem.trans (monotone_cdf μ h), fun h => csInf_le hbdd h⟩

/-- Sublevel sets of the quantile function:
`{u | qf μ u ≤ t} = ((0, 1) ∩ {u ≤ F_μ(t)}) ∪ ((0, 1)ᶜ ∩ {u | 0 ≤ t})`. -/
theorem qf_preimage_Iic (μ : Measure ℝ) (t : ℝ) :
    qf μ ⁻¹' Iic t
      = (Ioo 0 1 ∩ {u | u ≤ cdf μ t}) ∪ ((Ioo 0 1)ᶜ ∩ {_u | (0 : ℝ) ≤ t}) := by
  ext u
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · simp [hu, qf_le_iff μ hu]
  · simp [hu, qf]

/-- **Joint measurability of quantiles along a kernel.** For a kernel `κ : Kernel α ℝ`, the map
`(a, u) ↦ qf (κ a) u` is measurable (Markov `κ`). -/
theorem measurable_qf_kernel {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    [IsMarkovKernel κ] :
    Measurable fun p : α × ℝ => qf (κ p.1) p.2 := by
  refine measurable_of_Iic fun t => ?_
  have hF : Measurable fun a => cdf (κ a) t := by
    simp_rw [cdf_eq_real, measureReal_def]
    exact (κ.measurable_coe measurableSet_Iic).ennreal_toReal
  have : (fun p : α × ℝ => qf (κ p.1) p.2) ⁻¹' Iic t
      = ({p | p.2 ∈ Ioo (0 : ℝ) 1} ∩ {p | p.2 ≤ cdf (κ p.1) t})
        ∪ ({p | p.2 ∈ Ioo (0 : ℝ) 1}ᶜ ∩ {_p | (0 : ℝ) ≤ t}) := by
    ext p
    have := congrArg (p.2 ∈ ·) (qf_preimage_Iic (κ p.1) t)
    simpa using this
  rw [this]
  refine (MeasurableSet.inter ?_ ?_).union (MeasurableSet.inter ?_ ?_)
  · exact measurable_snd measurableSet_Ioo
  · exact measurableSet_le measurable_snd (hF.comp measurable_fst)
  · exact (measurable_snd measurableSet_Ioo).compl
  · exact MeasurableSet.const _

/-- Lebesgue measure of `(0, 1) ∩ (-∞, c]` for `c ≤ 1` is `ofReal c`. -/
theorem volume_Ioo_inter_Iic {c : ℝ} (h1 : c ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
  have hsub : Ioo (0 : ℝ) 1 ∩ Iic c ⊆ Ioc 0 c := fun u hu => ⟨hu.1.1, hu.2⟩
  have hsup : Ioo (0 : ℝ) c ⊆ Ioo 0 1 ∩ Iic c := fun u hu =>
    ⟨⟨hu.1, hu.2.trans_le h1⟩, hu.2.le⟩
  refine le_antisymm ((measure_mono hsub).trans (by simp)) ?_
  calc ENNReal.ofReal c = volume (Ioo 0 c) := by simp
    _ ≤ _ := measure_mono hsup

/-- The quantile function of any law is measurable. -/
theorem measurable_qf (μ : Measure ℝ) : Measurable (qf μ) := by
  refine measurable_of_Iic fun t => ?_
  rw [qf_preimage_Iic]
  exact (measurableSet_Ioo.inter (measurableSet_le measurable_id measurable_const)).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

/-- **Quantile representation.** For a probability law `μ` on `ℝ`, the quantile function
pushes the uniform law on `(0, 1)` forward to `μ`: `unif.map (qf μ) = μ`. -/
theorem map_qf (μ : Measure ℝ) [IsProbabilityMeasure μ] : unif.map (qf μ) = μ := by
  refine Measure.ext_of_Iic _ _ fun t => ?_
  have hS : MeasurableSet (qf μ ⁻¹' Iic t) := measurable_qf μ measurableSet_Iic
  rw [Measure.map_apply (measurable_qf μ) measurableSet_Iic, unif, Measure.restrict_apply hS,
    qf_preimage_Iic, ← ofReal_cdf]
  have : ((Ioo 0 1 ∩ {u | u ≤ cdf μ t}) ∪ ((Ioo 0 1)ᶜ ∩ {_u | (0 : ℝ) ≤ t})) ∩ Ioo 0 1
      = Ioo (0 : ℝ) 1 ∩ Iic (cdf μ t) := by
    ext u
    simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_Iic]
    constructor
    · rintro ⟨h | h, hu⟩
      · exact ⟨hu, h.2⟩
      · exact absurd hu h.1
    · rintro ⟨hu, h⟩
      exact ⟨Or.inl ⟨hu, h⟩, hu⟩
  rw [this, volume_Ioo_inter_Iic (cdf_le_one μ t)]

/-! ### Stochastically monotone, 1-Lipschitz kernels and quantile couplings -/

/-- A kernel on `ℝ` is **CDF-shift-monotone** if, for `y ≤ y'`, `κ y'` stochastically dominates
`κ y` (`F_{κ y'} ≤ F_{κ y}`) and is dominated by `κ y` shifted by `y' - y`
(`F_{κ y}(t) ≤ F_{κ y'}(t + (y' - y))`). -/
def CDFShiftMonotone (κ : Kernel ℝ ℝ) : Prop :=
  ∀ y y' t : ℝ, y ≤ y' →
    cdf (κ y') t ≤ cdf (κ y) t ∧ cdf (κ y) t ≤ cdf (κ y') (t + (y' - y))

/-- Quantiles of a CDF-shift-monotone kernel are monotone and move by at most the input shift:
for `y ≤ y'` and `u ∈ (0, 1)`, `qf (κ y) u ≤ qf (κ y') u ≤ qf (κ y) u + (y' - y)`. -/
theorem qf_le_qf_of_le {κ : Kernel ℝ ℝ} (hκ : CDFShiftMonotone κ) {y y' u : ℝ} (h : y ≤ y')
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    qf (κ y) u ≤ qf (κ y') u ∧ qf (κ y') u ≤ qf (κ y) u + (y' - y) := by
  constructor
  · rw [qf_le_iff _ hu]
    exact ((qf_le_iff _ hu _).1 le_rfl).trans (hκ y y' _ h).1
  · rw [qf_le_iff _ hu]
    exact ((qf_le_iff _ hu _).1 le_rfl).trans (hκ y y' _ h).2

/-- **Quantile contraction.** For a CDF-shift-monotone kernel and `u ∈ (0, 1)`:
`|qf (κ y) u - qf (κ y') u| ≤ |y - y'|`. -/
theorem abs_qf_sub_le {κ : Kernel ℝ ℝ} (hκ : CDFShiftMonotone κ) (y y' : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : |qf (κ y) u - qf (κ y') u| ≤ |y - y'| := by
  rcases le_total y y' with h | h
  · obtain ⟨h1, h2⟩ := qf_le_qf_of_le hκ h hu
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h)]
    linarith
  · obtain ⟨h1, h2⟩ := qf_le_qf_of_le hκ h hu
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 h)]
    linarith

/-- The quantile coupling map `((y, y'), u) ↦ (qf (κ y) u, qf (κ y') u)`. -/
noncomputable def qMap (κ : Kernel ℝ ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (qf (κ p.1.1) p.2, qf (κ p.1.2) p.2)

/-- The quantile coupling map is measurable (Markov `κ`). -/
theorem measurable_qMap (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] : Measurable (qMap κ) :=
  ((measurable_qf_kernel κ).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    ((measurable_qf_kernel κ).comp (measurable_fst.snd.prodMk measurable_snd))

/-- The **quantile coupling** driven by a coupling `γ` of the inputs: draw `(y, y') ~ γ` and an
independent `u ~ unif`, output `(qf (κ y) u, qf (κ y') u)`. -/
noncomputable def qCoupling (κ : Kernel ℝ ℝ) (γ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (γ.prod unif).map (qMap κ)

/-- Marginals of the quantile construction: for a finite `γ` on `β`, measurable `g : β → ℝ`
and Markov `κ`, `(γ ⊗ unif).map ((b, u) ↦ qf (κ (g b)) u) = κ ∘ₘ γ.map g`. -/
theorem map_prod_unif_qf {β : Type*} [MeasurableSpace β] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (γ : Measure β) [IsFiniteMeasure γ] {g : β → ℝ} (hg : Measurable g) :
    (γ.prod unif).map (fun p => qf (κ (g p.1)) p.2) = κ ∘ₘ γ.map g := by
  have hm : Measurable fun p : β × ℝ => qf (κ (g p.1)) p.2 :=
    (measurable_qf_kernel κ).comp ((hg.comp measurable_fst).prodMk measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs),
    Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_map (κ.measurable_coe hs) hg]
  refine lintegral_congr fun b => ?_
  rw [← map_qf (κ (g b)), Measure.map_apply (measurable_qf _) hs]
  rfl

/-- First marginal of the quantile coupling: `(qCoupling κ γ).map fst = κ ∘ₘ γ.map fst`. -/
theorem qCoupling_fst (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (γ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ] : (qCoupling κ γ).map Prod.fst = κ ∘ₘ γ.map Prod.fst := by
  rw [qCoupling, Measure.map_map measurable_fst (measurable_qMap κ)]
  exact map_prod_unif_qf κ γ measurable_fst

/-- Second marginal of the quantile coupling: `(qCoupling κ γ).map snd = κ ∘ₘ γ.map snd`. -/
theorem qCoupling_snd (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (γ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ] : (qCoupling κ γ).map Prod.snd = κ ∘ₘ γ.map Prod.snd := by
  rw [qCoupling, Measure.map_map measurable_snd (measurable_qMap κ)]
  exact map_prod_unif_qf κ γ measurable_snd

/-- **Cost of the quantile coupling.** For a CDF-shift-monotone Markov kernel, a finite `γ`, and
a measurable `φ : ℝ → ℝ≥0∞` monotone on `[0, ∞)`:
`∫⁻ φ(|x - y|) d(qCoupling κ γ) ≤ ∫⁻ φ(|x - y|) dγ`. -/
theorem lintegral_qCoupling_le (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (hκ : CDFShiftMonotone κ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : MonotoneOn φ (Ici 0)) :
    ∫⁻ p, φ |p.1 - p.2| ∂(qCoupling κ γ) ≤ ∫⁻ p, φ |p.1 - p.2| ∂γ := by
  have hc : Measurable fun p : ℝ × ℝ => φ |p.1 - p.2| :=
    hφm.comp (measurable_fst.sub measurable_snd).abs
  rw [qCoupling, lintegral_map hc (measurable_qMap κ),
    lintegral_prod (fun z => φ |(qMap κ z).1 - (qMap κ z).2|)
      (hc.comp (measurable_qMap κ)).aemeasurable]
  refine lintegral_mono fun p => ?_
  calc ∫⁻ u, φ |(qMap κ (p, u)).1 - (qMap κ (p, u)).2| ∂unif
      ≤ ∫⁻ _u, φ |p.1 - p.2| ∂unif := by
        refine lintegral_mono_ae ?_
        rw [unif]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact hφ (mem_Ici.2 (abs_nonneg _)) (mem_Ici.2 (abs_nonneg _)) (abs_qf_sub_le hκ p.1 p.2 hu)
    _ = φ |p.1 - p.2| := by simp

/-- **Coupling transfer through a CDF-shift-monotone kernel.** If `γ` is a finite coupling of
`(ρ, μ)` and `κ` is a CDF-shift-monotone Markov kernel, there is a finite coupling `γ'` of
`(κ ∘ₘ ρ, κ ∘ₘ μ)` with `∫⁻ φ(|x - y|) dγ' ≤ ∫⁻ φ(|x - y|) dγ` (measurable `φ` monotone on
`[0, ∞)`). -/
theorem exists_coupling_comp (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (hκ : CDFShiftMonotone κ)
    {ρ μ : Measure ℝ} (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ)
    (h₂ : γ.map Prod.snd = μ) {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : MonotoneOn φ (Ici 0)) :
    ∃ γ' : Measure (ℝ × ℝ), IsFiniteMeasure γ' ∧ γ'.map Prod.fst = κ ∘ₘ ρ ∧
      γ'.map Prod.snd = κ ∘ₘ μ ∧ ∫⁻ p, φ |p.1 - p.2| ∂γ' ≤ ∫⁻ p, φ |p.1 - p.2| ∂γ := by
  refine ⟨qCoupling κ γ, by unfold qCoupling; infer_instance, ?_, ?_,
    lintegral_qCoupling_le κ hκ γ hφm hφ⟩
  · rw [qCoupling_fst, h₁]
  · rw [qCoupling_snd, h₂]

/-! ### The forward kernel is CDF-shift-monotone -/

/-- Distribution function of a translate: `F_{μ.map (· + h)}(t) = F_μ(t - h)`. -/
theorem cdf_map_add (μ : Measure ℝ) [IsProbabilityMeasure μ] (h t : ℝ) :
    cdf (μ.map (· + h)) t = cdf μ (t - h) := by
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (measurable_add_const h) measurableSet_Iic]
  congr 2
  ext x
  simp [le_sub_iff_add_le]

/-- **The Gaussian forward kernel is CDF-shift-monotone** (`η > 0`): `N(y', η)` is the
translate of `N(y, η)` by `y' - y`. -/
theorem cdfShiftMonotone_forwardKernel {η : ℝ} (hη : 0 < η) :
    CDFShiftMonotone (forwardKernel η) := by
  intro y y' t h
  have := isMarkovKernel_forwardKernel hη
  have e : forwardKernel η y' = (forwardKernel η y).map (· + (y' - y)) := by
    rw [forwardKernel_apply hη, forwardKernel_apply hη, gaussianReal_map_add_const]
    congr 1
    ring
  rw [e, cdf_map_add, cdf_map_add]
  exact ⟨monotone_cdf _ (by linarith), le_of_eq (by congr 1; ring)⟩

/-! ### Monotone likelihood ratios and the RGO kernel -/

/-- **Monotone likelihood ratio implies stochastic order (unnormalised).** Let `P > 0` and
`Q ≥ 0` be integrable on `ℝ` with `Q/P` nondecreasing, in the form
`Q s * P t ≤ Q t * P s` for `s ≤ t`. Then for every `t`:
`(∫_{(-∞, t]} Q) * ∫ P ≤ (∫_{(-∞, t]} P) * ∫ Q`. -/
theorem mul_setIntegral_Iic_le {P Q : ℝ → ℝ} (hP : ∀ x, 0 < P x) (hPi : Integrable P)
    (hQi : Integrable Q) (hmlr : ∀ s t, s ≤ t → Q s * P t ≤ Q t * P s) (t : ℝ) :
    (∫ x in Iic t, Q x) * ∫ x, P x ≤ (∫ x in Iic t, P x) * ∫ x, Q x := by
  set r := Q t / P t
  have hA : ∫ x in Iic t, Q x ≤ r * ∫ x in Iic t, P x := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hQi.integrableOn (hPi.integrableOn.const_mul r) measurableSet_Iic
      fun s hs => ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (hP t)]
    exact hmlr s t hs
  have hA' : r * ∫ x in Ioi t, P x ≤ ∫ x in Ioi t, Q x := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hPi.integrableOn.const_mul r) hQi.integrableOn measurableSet_Ioi
      fun s hs => ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (hP t)]
    exact hmlr t s (le_of_lt hs)
  have hQs := integral_add_compl (measurableSet_Iic (a := t)) hQi
  have hPs := integral_add_compl (measurableSet_Iic (a := t)) hPi
  rw [compl_Iic] at hQs hPs
  have hB : 0 ≤ ∫ x in Iic t, P x := setIntegral_nonneg measurableSet_Iic fun x _ => (hP x).le
  have hB' : 0 ≤ ∫ x in Ioi t, P x := setIntegral_nonneg measurableSet_Ioi fun x _ => (hP x).le
  rw [← hQs, ← hPs]
  nlinarith [mul_le_mul_of_nonneg_right hA hB', mul_le_mul_of_nonneg_left hA' hB]

/-- Normalised form of `mul_setIntegral_Iic_le`: if moreover `∫ P, ∫ Q > 0`, then
`(∫_{(-∞, t]} Q) / ∫ Q ≤ (∫_{(-∞, t]} P) / ∫ P`. -/
theorem div_setIntegral_Iic_le {P Q : ℝ → ℝ} (hP : ∀ x, 0 < P x) (hPi : Integrable P)
    (hQi : Integrable Q) (hmlr : ∀ s t, s ≤ t → Q s * P t ≤ Q t * P s)
    (hPpos : 0 < ∫ x, P x) (hQpos : 0 < ∫ x, Q x) (t : ℝ) :
    (∫ x in Iic t, Q x) / ∫ x, Q x ≤ (∫ x in Iic t, P x) / ∫ x, P x := by
  rw [div_le_div_iff₀ hQpos hPpos]
  exact mul_setIntegral_Iic_le hP hPi hQi hmlr t

/-- Translation of a half-line integral: `∫_{(-∞, t]} g(h + x) dx = ∫_{(-∞, t + h]} g`. -/
theorem setIntegral_Iic_add (g : ℝ → ℝ) (h t : ℝ) :
    ∫ x in Iic t, g (h + x) = ∫ x in Iic (t + h), g x := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
    ← integral_add_left_eq_self ((Iic (t + h)).indicator g) h]
  congr 1
  funext x
  have : h + x ≤ t + h ↔ x ≤ t := by constructor <;> intro <;> linarith
  simp only [indicator, mem_Iic, this]

/-- **Convexity as increasing increments.** For `f` convex on `ℝ`, `s ≤ t` and `h ≥ 0`:
`f(h + s) + f(t) ≤ f(s) + f(h + t)`. -/
theorem add_le_add_of_convexOn {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {s t h : ℝ} (hst : s ≤ t)
    (hh : 0 ≤ h) : f (h + s) + f t ≤ f s + f (h + t) := by
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  rcases (add_nonneg hts hh).eq_or_lt with hL | hL
  · have h0 : h = 0 := by linarith
    have hts' : t = s := by linarith
    subst h0 hts'
    exact le_of_eq (add_comm _ _)
  · set L := t - s + h with hLdef
    have ha : 0 ≤ (t - s) / L := div_nonneg hts hL.le
    have hb : 0 ≤ h / L := div_nonneg hh hL.le
    have hab : (t - s) / L + h / L = 1 := by
      rw [← add_div, div_self hL.ne']
    have h1 := hf.2 (mem_univ s) (mem_univ (h + t)) ha hb hab
    have h2 := hf.2 (mem_univ s) (mem_univ (h + t)) hb ha (by rw [add_comm]; exact hab)
    simp only [smul_eq_mul] at h1 h2
    have e1 : (t - s) / L * s + h / L * (h + t) = h + s := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hL.ne', hLdef]
      ring
    have e2 : h / L * s + (t - s) / L * (h + t) = t := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hL.ne', hLdef]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have hsum : (t - s) / L * f s + h / L * f (h + t)
        + (h / L * f s + (t - s) / L * f (h + t)) = f s + f (h + t) := by
      linear_combination (f s + f (h + t)) * hab
    linarith

/-- The unnormalised RGO weight `x ↦ exp(-f x - (x - y)² / (2η))`. -/
noncomputable def rgoWeight (f : ℝ → ℝ) (η y x : ℝ) : ℝ :=
  Real.exp (-f x - (x - y) ^ 2 / (2 * η))

/-- Distribution function of the RGO law: `F_{RGO(y)}(t) = (∫_{(-∞, t]} w_y) / Z_η(y)` with
`w_y = rgoWeight f η y` (measurable `f`, integrable `exp ∘ (-f)`, `η > 0`). -/
theorem cdf_rgoKernel {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) (y t : ℝ) :
    cdf (rgoKernel f η y) t = (∫ x in Iic t, rgoWeight f η y x) / rgoNormalizer f η y := by
  have := isMarkovKernel_rgoKernel hf hint hη
  have hi : Integrable (fun x => rgoDensity f η y x) :=
    (integrable_rgo hint hη y).div_const (rgoNormalizer f η y)
  rw [cdf_eq_real, measureReal_def, rgoKernel_apply hf hint hη,
    withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
      (ae_of_all _ fun x => rgoDensity_nonneg y x),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun x _ => rgoDensity_nonneg y x)]
  unfold rgoDensity
  rw [integral_div]
  rfl

/-- **The RGO kernel is CDF-shift-monotone for convex `f`.** Let `f` be convex on `ℝ` with
integrable `exp ∘ (-f)` and `η > 0`. For `y ≤ y'`: `RGO(y')` stochastically dominates `RGO(y)`
(this part holds for any `f`), and `RGO(y')` is dominated by `RGO(y)` shifted by `y' - y`
(this uses convexity). -/
theorem cdfShiftMonotone_rgoKernel {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) :
    CDFShiftMonotone (rgoKernel f η) := by
  have hf : Measurable f := (continuousOn_univ.1 (hconv.continuousOn isOpen_univ)).measurable
  have hwi : ∀ y, Integrable (rgoWeight f η y) := fun y => integrable_rgo hint hη y
  have hwp : ∀ y x, 0 < rgoWeight f η y x := fun y x => Real.exp_pos _
  have hZ : ∀ y, ∫ x, rgoWeight f η y x = rgoNormalizer f η y := fun y => rfl
  intro y y' t hyy
  constructor
  · rw [cdf_rgoKernel hf hint hη, cdf_rgoKernel hf hint hη, ← hZ, ← hZ]
    refine div_setIntegral_Iic_le (hwp y) (hwi y) (hwi y') (fun s t hst => ?_)
      (rgoNormalizer_pos hint hη y) (rgoNormalizer_pos hint hη y') t
    simp only [rgoWeight, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have key : (-f t - (t - y') ^ 2 / (2 * η) + (-f s - (s - y) ^ 2 / (2 * η)))
        - (-f s - (s - y') ^ 2 / (2 * η) + (-f t - (t - y) ^ 2 / (2 * η)))
        = (t - s) * (y' - y) / η := by
      field_simp
      ring
    have : 0 ≤ (t - s) * (y' - y) / η :=
      div_nonneg (mul_nonneg (sub_nonneg.2 hst) (sub_nonneg.2 hyy)) hη.le
    linarith
  · rw [cdf_rgoKernel hf hint hη, cdf_rgoKernel hf hint hη, ← hZ, ← hZ,
      ← setIntegral_Iic_add, ← integral_add_left_eq_self (rgoWeight f η y') (y' - y)]
    refine div_setIntegral_Iic_le (fun x => hwp y' _) ((hwi y').comp_add_left (y' - y)) (hwi y)
      (fun s t hst => ?_) ?_ (rgoNormalizer_pos hint hη y) t
    · simp only [rgoWeight, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hc := add_le_add_of_convexOn hconv hst (sub_nonneg.2 hyy)
      have e1 : (y' - y + t - y') ^ 2 / (2 * η) = (t - y) ^ 2 / (2 * η) := by ring_nf
      have e2 : (y' - y + s - y') ^ 2 / (2 * η) = (s - y) ^ 2 / (2 * η) := by ring_nf
      linarith
    · rw [integral_add_left_eq_self (rgoWeight f η y') (y' - y)]
      exact rgoNormalizer_pos hint hη y'

/-! ### Coupling contraction of the proximal kernel and the KL bound -/

/-- **Coupling non-expansiveness of the proximal kernel (convex `f`).** Let `f` be convex with
integrable `exp ∘ (-f)` and `η > 0`. For every finite coupling `γ` of `(ρ, μ)` there is a finite
coupling `γ'` of `(proxKernel f η ∘ₘ ρ, proxKernel f η ∘ₘ μ)` with
`∫⁻ φ(|x - y|) dγ' ≤ ∫⁻ φ(|x - y|) dγ` (measurable `φ` monotone on `[0, ∞)`). The forward step
uses the synchronous (common-quantile) Gaussian coupling, the RGO step the monotone quantile
coupling. -/
theorem exists_coupling_proxKernel {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) {ρ μ : Measure ℝ}
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ)
    (h₂ : γ.map Prod.snd = μ) {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : MonotoneOn φ (Ici 0)) :
    ∃ γ' : Measure (ℝ × ℝ), IsFiniteMeasure γ' ∧ γ'.map Prod.fst = proxKernel f η ∘ₘ ρ ∧
      γ'.map Prod.snd = proxKernel f η ∘ₘ μ ∧
      ∫⁻ p, φ |p.1 - p.2| ∂γ' ≤ ∫⁻ p, φ |p.1 - p.2| ∂γ := by
  have hf : Measurable f := (continuousOn_univ.1 (hconv.continuousOn isOpen_univ)).measurable
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_rgoKernel hf hint hη
  obtain ⟨γ₁, hγ₁, a₁, b₁, c₁⟩ := exists_coupling_comp (forwardKernel η)
    (cdfShiftMonotone_forwardKernel hη) γ h₁ h₂ hφm hφ
  obtain ⟨γ₂, hγ₂, a₂, b₂, c₂⟩ := exists_coupling_comp (rgoKernel f η)
    (cdfShiftMonotone_rgoKernel hconv hint hη) γ₁ a₁ b₁ hφm hφ
  refine ⟨γ₂, hγ₂, ?_, ?_, c₂.trans c₁⟩
  · rw [proxKernel, ← Measure.comp_assoc]
    exact a₂
  · rw [proxKernel, ← Measure.comp_assoc]
    exact b₂

/-- **Couplings along the proximal chain (convex `f`).** Let `f` be convex with integrable
`exp ∘ (-f)`, `π = target f`, `η > 0`, `ρ (k + 1) = proxKernel f η ∘ₘ ρ k`, and `γ₀` a finite
coupling of `(ρ 0, π)`. Then for every `k` there is a finite coupling `γ` of `(ρ k, π)` with
`∫⁻ φ(|x - y|) dγ ≤ ∫⁻ φ(|x - y|) dγ₀` (measurable `φ` monotone on `[0, ∞)`). -/
theorem exists_coupling_iterate {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) (ρ : ℕ → Measure ℝ)
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (γ₀ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ₀] (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = target f)
    {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ) (hφ : MonotoneOn φ (Ici 0)) (k : ℕ) :
    ∃ γ : Measure (ℝ × ℝ), IsFiniteMeasure γ ∧ γ.map Prod.fst = ρ k ∧
      γ.map Prod.snd = target f ∧ ∫⁻ p, φ |p.1 - p.2| ∂γ ≤ ∫⁻ p, φ |p.1 - p.2| ∂γ₀ := by
  have hf : Measurable f := (continuousOn_univ.1 (hconv.continuousOn isOpen_univ)).measurable
  induction k with
  | zero => exact ⟨γ₀, inferInstance, h₁, h₂, le_rfl⟩
  | succ k ih =>
    obtain ⟨γ, hγ, a, b, c⟩ := ih
    obtain ⟨γ', hγ', a', b', c'⟩ := exists_coupling_proxKernel hconv hint hη γ a b hφm hφ
    refine ⟨γ', hγ', by rw [hstep]; exact a', ?_, c'.trans c⟩
    rw [b', proxKernel_comp_target hf hint hη]

/-- **KL bound for the proximal sampler with a merely log-concave target (1D).** Let `f` be
convex on `ℝ` with `∫ e^{-f} < ∞`, `π = target f`, `η > 0`, `ρ (k + 1) = proxKernel f η ∘ₘ ρ k`,
and let `γ₀` be any finite coupling of `(ρ 0, π)`. Then for every `k`:
`KL(ρ (k + 1) ‖ π) ≤ ∫⁻ (x - y)² / (2η) dγ₀(x, y)`. In particular `KL(ρ_k ‖ π)` is finite for
`k ≥ 1` whenever `ρ 0` has a coupling with `π` of finite quadratic cost, even if
`KL(ρ 0 ‖ π) = ∞`. -/
theorem klDiv_iterate_le_coupling {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) (ρ : ℕ → Measure ℝ)
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (γ₀ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ₀] (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = target f)
    (k : ℕ) :
    klDiv (ρ (k + 1)) (target f) ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / (2 * η)) ∂γ₀ := by
  have hf : Measurable f := (continuousOn_univ.1 (hconv.continuousOn isOpen_univ)).measurable
  set φ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ 2 / (2 * η)) with hφdef
  have hφm : Measurable φ := by
    rw [hφdef]
    fun_prop
  have hφ : MonotoneOn φ (Ici 0) := fun a ha b _ hab =>
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab 2)
      (by positivity))
  obtain ⟨γ, hγ, a, b, c⟩ := exists_coupling_iterate hconv hint hη ρ hstep γ₀ h₁ h₂ hφm hφ k
  have : IsFiniteMeasure (ρ k) := a ▸ inferInstance
  rw [hstep]
  refine (ProximalRegularization.klDiv_proxKernel_comp_le_coupling hf hint hη γ a b).trans ?_
  simpa only [hφdef, sq_abs] using c

end FormalizeSampling.ProximalLogConcave
