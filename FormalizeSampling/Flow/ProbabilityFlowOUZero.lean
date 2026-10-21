module

public import FormalizeSampling.Flow.ProbabilityFlowOU
public import FormalizeSampling.Foundations.KLLowerSemicontinuity
public import FormalizeSampling.Foundations.KLWarmApprox

/-!
# The OU probability flow down to `t = 0`

Registry IDs: **FL-1 (II)**, **FL-2**, **FL-4** (extension of `Flow/ProbabilityFlowOU.lean` to the
initial time).

Status: **Verified**. `ρ` is any probability law on `Fin d → ℝ`; the continuity at `0⁺` needs
nothing else. The derivative and decay statements also assume `∫ |x|² dρ < ∞`, as in
`ProbabilityFlowOU`. Target `π = N(0, v I)` (`gaussPi d v`), OU marginals
`p_t = ouKernelVarPi v a t ∘ₘ ρ` (`OULangevinDecayPi`), `p_0 = ρ`.

## Main results

* `ouKernelVarPi_comp_eq_map_prod`: `p_t` is the law of `e^{-at} X + √(v (1 - e^{-2at})) Z` with
  `X ∼ ρ` and `Z ∼ N(0, I)` independent.
* `tendsto_integral_ouKernelVarPi_comp`: `∫ f dp_t → ∫ f dρ` as `t → 0` for every bounded
  continuous `f` (weak convergence, by dominated convergence).
* `tendsto_klDiv_ouKernelVarPi_comp_zero` (**right-continuity at `0`, in `ℝ≥0∞`**):
  `KL(p_t‖π) → KL(ρ‖π)` as `t → 0⁺` (within `[0, ∞)`), including the case `KL(ρ‖π) = ∞`.
  The upper bound is data processing: the OU kernel fixes `π`
  (`KLWarmApprox.klDiv_comp_le_of_comp_eq`-style, via Mathlib's `klDiv_comp_right_le`). The lower
  bound is lower semicontinuity of KL under weak convergence
  (`KLLowerSemicontinuity.klDiv_le_liminf_of_tendsto_integral`, a Donsker–Varadhan argument).
* `continuousWithinAt_toReal_klDiv_zero`: the real form when `KL(ρ‖π) < ∞`.
* `hasDerivAt_toReal_klDiv_ouKernelVarPi_comp`: for `t > 0`,
  `d/dt KL(p_t‖π) = -(a v) I(p_t‖π)` with the relative Fisher information
  `I = relFisher (p_t dx) (∇p_t/p_t) (-x/v)`, for the `klDiv` form of the curve.
* `continuousOn_toReal_klDiv_ouKernelVarPi_comp`: the curve `t ↦ KL(p_t‖π)` is continuous on
  `[0, ∞)` when `KL(ρ‖π) < ∞`.
* `toReal_klDiv_ouKernelVarPi_comp_le_zero`: `KL(p_t‖π) ≤ e^{-2at} KL(ρ‖π)` for `t ≥ 0`,
  obtained by letting `s → 0⁺` in `ProbabilityFlowOU.toReal_klDiv_ouKernelVarPi_comp_le_of_le`
  (the probability-flow / LSI route). `toReal_klDiv_ouKernelVarPi_comp_le_of_le_zero` extends
  that theorem to `0 ≤ s ≤ t`.
* `klDiv_ouKernelVarPi_comp_le_zero`: the `ℝ≥0∞` form
  `KL(p_t‖π) ≤ e^{-2at} KL(ρ‖π)`, valid also when `KL(ρ‖π) = ∞`.

## Not proved here

* The continuity equation and the KL derivative at `t = 0` itself (`ρ` may have no density).
  At `0` only right-continuity of the KL curve is proved.
* Continuity at `0` of the Fisher information, or any rate for `KL(p_t‖π) → KL(ρ‖π)`.
* **`TransportKLRegularity` for a general `ρ`** is not treated in this file. It is
  proved for compactly supported `ρ` (`ProbabilityFlowOU.transportKLRegularity_ou`) and under a
  finite fourth moment (`ProbabilityFlowOUMoment.transportKLRegularity_ou_moment`); under a
  third moment it reduces to the `domination` field
  (`ProbabilityFlowOUThirdMoment.transportKLRegularity_ou_iff_domination`), and the moment
  thresholds are shown sharp in `ProbabilityFlowOUCounterexample`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProbabilityFlowOUZero

open FormalizeSampling.OULangevinDecayPi FormalizeSampling.ProbabilityFlowOU
open FormalizeSampling.HeatFlowRegularityPi (gaussPi)
open FormalizeSampling.LogSobolevAlongGaussian FormalizeSampling.KLDecay

variable {d : ℕ}

/-! ### The OU marginal as a law of `e^{-at} X + √s Z` -/

/-- The truncated OU noise standard deviation `√(v (1 - e^{-2at}))⁺`. -/
noncomputable def ouStd (v a t : ℝ) : ℝ := √((v * (1 - Real.exp (-2 * a * t))).toNNReal : ℝ)

/-- `t ↦ ouStd v a t` is continuous. -/
theorem continuous_ouStd (v a : ℝ) : Continuous (ouStd v a) := by
  unfold ouStd
  refine Real.continuous_sqrt.comp (NNReal.continuous_coe.comp
    (continuous_real_toNNReal.comp ?_))
  fun_prop

/-- `ouStd v a 0 = 0`. -/
theorem ouStd_zero (v a : ℝ) : ouStd v a 0 = 0 := by
  simp [ouStd]

/-- The map `(x, z) ↦ e^{-at} x + ouStd z`. -/
noncomputable def ouMap (v a t : ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => Real.exp (-a * t) * p.1 i + ouStd v a t * p.2 i

/-- `ouMap v a t` is continuous. -/
theorem continuous_ouMap (v a t : ℝ) : Continuous (ouMap (d := d) v a t) := by
  unfold ouMap
  fun_prop

/-- A one-dimensional Gaussian is an affine image of the standard one:
`N(m, σ) = N(0, 1).map (z ↦ m + √σ z)`. -/
theorem gaussianReal_eq_map_std (m : ℝ) (σ : ℝ≥0) :
    gaussianReal m σ = (gaussianReal 0 1).map (fun z => m + √(σ : ℝ) * z) := by
  rw [show (fun z => m + √(σ : ℝ) * z) = (m + ·) ∘ (√(σ : ℝ) * ·) from rfl,
    ← Measure.map_map (measurable_const_add m) (measurable_const_mul _),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  congr 1
  · simp
  · ext; simp

/-- `N(0, I)` on `Fin d → ℝ`. -/
noncomputable abbrev stdGauss (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 1

/-- The OU kernel at `x` is the law of `e^{-at} x + ouStd Z`, `Z ∼ N(0, I)`. -/
theorem ouKernelVarPi_apply_eq_map (v a t : ℝ) (x : Fin d → ℝ) :
    ouKernelVarPi v a t x = (stdGauss d).map (fun z => ouMap v a t (x, z)) := by
  rw [ouKernelVarPi_apply]
  have h := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal 0 1)
    (f := fun i z => Real.exp (-a * t) * x i + ouStd v a t * z)
    (fun i => (by fun_prop : Measurable fun z : ℝ =>
      Real.exp (-a * t) * x i + ouStd v a t * z).aemeasurable)
  calc _ = Measure.pi fun i => (gaussianReal 0 1).map
        (fun z => Real.exp (-a * t) * x i + ouStd v a t * z) := by
        congr 1
        funext i
        exact gaussianReal_eq_map_std _ _
    _ = _ := h.symm

/-- **The OU marginal as an independent sum.** `ouKernelVarPi v a t ∘ₘ ρ` is the law of
`e^{-at} X + √(v (1 - e^{-2at}))⁺ Z` with `(X, Z) ∼ ρ ⊗ N(0, I)`. -/
theorem ouKernelVarPi_comp_eq_map_prod (v a t : ℝ) (ρ : Measure (Fin d → ℝ)) [SFinite ρ] :
    ouKernelVarPi v a t ∘ₘ ρ = (ρ.prod (stdGauss d)).map (ouMap v a t) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.map_apply (continuous_ouMap v a t).measurable hs,
    Measure.prod_apply ((continuous_ouMap v a t).measurable hs)]
  refine lintegral_congr fun x => ?_
  rw [ouKernelVarPi_apply_eq_map, Measure.map_apply
    (f := fun z => ouMap v a t (x, z))
    (by have := (continuous_ouMap (d := d) v a t).comp (Continuous.prodMk_right x)
        exact this.measurable) hs]
  rfl

/-- **Weak convergence `p_t → ρ` as `t → 0`.** For a probability law `ρ` and a bounded continuous
`f`, `∫ f d(ouKernelVarPi v a t ∘ₘ ρ) → ∫ f dρ` as `t → 0`. -/
theorem tendsto_integral_ouKernelVarPi_comp (v a : ℝ) (ρ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ] {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {N : ℝ}
    (hN : ∀ x, |f x| ≤ N) :
    Tendsto (fun t => ∫ x, f x ∂(ouKernelVarPi v a t ∘ₘ ρ)) (𝓝 0) (𝓝 (∫ x, f x ∂ρ)) := by
  have e : ∀ t, ∫ x, f x ∂(ouKernelVarPi v a t ∘ₘ ρ) =
      ∫ p, f (ouMap v a t p) ∂(ρ.prod (stdGauss d)) := fun t => by
    rw [ouKernelVarPi_comp_eq_map_prod,
      integral_map (continuous_ouMap v a t).aemeasurable hf.aestronglyMeasurable]
  simp_rw [e]
  have e0 : ∫ x, f x ∂ρ = ∫ p, f p.1 ∂(ρ.prod (stdGauss d)) := by
    rw [integral_fun_fst]; simp
  rw [e0]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => N) ?_ ?_
    (integrable_const N) ?_
  · exact Eventually.of_forall fun t =>
      (hf.comp (continuous_ouMap v a t)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hN _
  · refine ae_of_all _ fun p => ?_
    have hc : Continuous fun t => f (ouMap v a t p) := by
      refine hf.comp (continuous_pi fun i => ?_)
      unfold ouMap
      exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-a * t)).mul continuous_const
        |>.add ((continuous_ouStd v a).mul continuous_const)
    have h0 : ouMap v a 0 p = p.1 := by
      funext i; simp [ouMap, ouStd_zero]
    simpa [h0] using hc.tendsto 0

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- The OU kernel fixes the target: `ouKernelVarPi v a t ∘ₘ N(0, v I) = N(0, v I)`
(`v ≥ 0`, `a, t ≥ 0`). -/
theorem ouKernelVarPi_comp_gaussPi (hv : 0 ≤ v) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ouKernelVarPi v a t ∘ₘ gaussPi d v = gaussPi d v := by
  have h := ouKernelVarPi_comp_pi_gaussianReal (d := d) hv ha ht 0
  simpa using h

/-- **Data processing along the OU flow.** `KL(p_t‖π) ≤ KL(ρ‖π)` for `t ≥ 0`. -/
theorem klDiv_ouKernelVarPi_comp_le_klDiv (hv : 0 ≤ v) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v) ≤ klDiv ρ (gaussPi d v) :=
  KLWarmApprox.klDiv_comp_le_of_comp_eq _ (ouKernelVarPi_comp_gaussPi hv ha ht) ρ

omit [IsProbabilityMeasure ρ] in
/-- `p_0 = ρ`. -/
theorem ouKernelVarPi_comp_zero (v a : ℝ) : ouKernelVarPi v a 0 ∘ₘ ρ = ρ :=
  ouKernelVarPi_comp_of_mul_eq_zero (mul_zero a) ρ

/-- **Right-continuity of the KL at `t = 0` (`ℝ≥0∞`, Verified, no moment or KL hypothesis).**
For a probability law `ρ` on `Fin d → ℝ`, `v > 0` and `a ≥ 0`,
`KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)) → KL(ρ‖N(0, v I))` as `t → 0⁺` (within `[0, ∞)`). This
includes the case `KL(ρ‖N(0, v I)) = ∞`, where the KL along the flow tends to `∞`. -/
theorem tendsto_klDiv_ouKernelVarPi_comp_zero (hv : 0 < v) (ha : 0 ≤ a) :
    Tendsto (fun t => klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)) (𝓝[≥] 0)
      (𝓝 (klDiv ρ (gaussPi d v))) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact KLLowerSemicontinuity.klDiv_le_liminf_of_tendsto_integral fun f hf N hN =>
      (tendsto_integral_ouKernelVarPi_comp v a ρ hf hN).mono_left nhdsWithin_le_nhds
  · refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact klDiv_ouKernelVarPi_comp_le_klDiv ρ hv.le ha ht

/-- **Right-continuity at `t = 0`, real form.** If `KL(ρ‖N(0, v I)) < ∞` (`v > 0`, `a ≥ 0`), the
curve `t ↦ KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)).toReal` is continuous at `0` within `[0, ∞)`,
with value `KL(ρ‖N(0, v I)).toReal`. -/
theorem continuousWithinAt_toReal_klDiv_zero (hv : 0 < v) (ha : 0 ≤ a)
    (hKL : klDiv ρ (gaussPi d v) ≠ ∞) :
    ContinuousWithinAt (fun t => (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal)
      (Ici 0) 0 := by
  show Tendsto _ _ (𝓝 (klDiv (ouKernelVarPi v a 0 ∘ₘ ρ) (gaussPi d v)).toReal)
  rw [ouKernelVarPi_comp_zero]
  exact (ENNReal.tendsto_toReal hKL).comp (tendsto_klDiv_ouKernelVarPi_comp_zero ρ hv ha)

/-- The `klDiv` curve agrees with `gaussKL` of the OU density for `t > 0`. -/
theorem toReal_klDiv_eq_gaussKL (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) :
    (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal = gaussKL (ouDensity ρ v a) v t := by
  rw [gaussKL, lawOf_ouDensity ρ hv ha ht]
  rfl

/-- **FL-1/FL-2 for the `klDiv` curve.** For a probability law `ρ` with finite second moment,
`v, a > 0` and `t > 0`, `t ↦ KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)).toReal` has derivative
`-(a v) I(p_t‖N(0, v I))` at `t`, with `I = relFisher (p_t dx) (∇p_t/p_t) (-x/v)` and
`p_t = ouDensity ρ v a t`. -/
theorem hasDerivAt_toReal_klDiv_ouKernelVarPi_comp (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (ht : 0 < t) :
    HasDerivAt (fun t => (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal)
      (-(a * v) * relFisher (lawOf (ouDensity ρ v a t))
        (densityScore (ouDensity ρ v a t) (ouGrad ρ v a t)) (gaussScore v)) t := by
  refine (hasDerivAt_gaussKL_ouDensity ρ hv ha hmom ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact toReal_klDiv_eq_gaussKL ρ hv ha hu

/-- **Continuity of the KL curve on `[0, ∞)`.** For a probability law `ρ` with finite second
moment and `KL(ρ‖N(0, v I)) < ∞` (`v, a > 0`), `t ↦ KL(ouKernelVarPi v a t ∘ₘ ρ‖N(0, v I)).toReal`
is continuous on `[0, ∞)`. -/
theorem continuousOn_toReal_klDiv_ouKernelVarPi_comp (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hKL : klDiv ρ (gaussPi d v) ≠ ∞) :
    ContinuousOn (fun t => (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal)
      (Ici 0) := by
  intro t ht
  rcases (mem_Ici.1 ht).eq_or_lt with h0 | hpos
  · rw [← h0]; exact continuousWithinAt_toReal_klDiv_zero ρ hv ha.le hKL
  · exact (hasDerivAt_toReal_klDiv_ouKernelVarPi_comp ρ hv ha hmom hpos).continuousAt
      |>.continuousWithinAt

/-- **FL-4 from `t = 0` along the probability flow.** For a probability law `ρ` with finite
second moment and `KL(ρ‖N(0, v I)) < ∞` (`v, a > 0`), for every `t ≥ 0`:
`KL(p_t‖N(0, v I)) < ∞` and `KL(p_t‖N(0, v I)).toReal ≤ e^{-2at} KL(ρ‖N(0, v I)).toReal`,
`p_t = ouKernelVarPi v a t ∘ₘ ρ`. Proved by letting `s → 0⁺` in
`ProbabilityFlowOU.toReal_klDiv_ouKernelVarPi_comp_le_of_le` and using
`continuousWithinAt_toReal_klDiv_zero`. -/
theorem toReal_klDiv_ouKernelVarPi_comp_le_zero (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hKL : klDiv ρ (gaussPi d v) ≠ ∞)
    (ht : 0 ≤ t) :
    klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v) ≠ ∞ ∧
      (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal ≤
        Real.exp (-2 * a * t) * (klDiv ρ (gaussPi d v)).toReal := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, ouKernelVarPi_comp_zero, mul_zero, Real.exp_zero, one_mul]
    exact ⟨hKL, le_rfl⟩
  refine ⟨(toReal_klDiv_ouKernelVarPi_comp_le_of_le ρ hv ha hmom hpos le_rfl).1, ?_⟩
  set F := fun t => (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal
  have hF : Tendsto F (𝓝[>] 0) (𝓝 (klDiv ρ (gaussPi d v)).toReal) := by
    have := (continuousWithinAt_toReal_klDiv_zero ρ hv ha.le hKL).tendsto
    rw [ouKernelVarPi_comp_zero] at this
    exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hE : Tendsto (fun s => Real.exp (-2 * a * (t - s))) (𝓝[>] 0)
      (𝓝 (Real.exp (-2 * a * t))) := by
    have : Continuous fun s => Real.exp (-2 * a * (t - s)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto (hE.mul hF) ?_
  filter_upwards [Ioo_mem_nhdsGT hpos] with s hs
  exact (toReal_klDiv_ouKernelVarPi_comp_le_of_le ρ hv ha hmom hs.1 hs.2.le).2

/-- **`ProbabilityFlowOU.toReal_klDiv_ouKernelVarPi_comp_le_of_le` down to `s = 0`.** For a
probability law `ρ` with finite second moment and `KL(ρ‖N(0, v I)) < ∞` (`v, a > 0`) and
`0 ≤ s ≤ t`: `KL(p_t‖π).toReal ≤ e^{-2a(t - s)} KL(p_s‖π).toReal`, with `p_0 = ρ`. -/
theorem toReal_klDiv_ouKernelVarPi_comp_le_of_le_zero (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (hKL : klDiv ρ (gaussPi d v) ≠ ∞) {s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal ≤
      Real.exp (-2 * a * (t - s)) * (klDiv (ouKernelVarPi v a s ∘ₘ ρ) (gaussPi d v)).toReal := by
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0, ouKernelVarPi_comp_zero, sub_zero]
    exact (toReal_klDiv_ouKernelVarPi_comp_le_zero ρ hv ha hmom hKL (h0 ▸ hst)).2
  · exact (toReal_klDiv_ouKernelVarPi_comp_le_of_le ρ hv ha hmom hpos hst).2

/-- **FL-4 from `t = 0` in `ℝ≥0∞`.** For a probability law `ρ` with finite second moment
(`v, a > 0`, `t ≥ 0`, no KL hypothesis):
`KL(p_t‖N(0, v I)) ≤ e^{-2at} · KL(ρ‖N(0, v I))` in `ℝ≥0∞`; the right side is `∞` when
`KL(ρ‖N(0, v I)) = ∞`. -/
theorem klDiv_ouKernelVarPi_comp_le_zero (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (ht : 0 ≤ t) :
    klDiv (ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v) ≤
      ENNReal.ofReal (Real.exp (-2 * a * t)) * klDiv ρ (gaussPi d v) := by
  by_cases hKL : klDiv ρ (gaussPi d v) = ∞
  · rw [hKL, ENNReal.mul_top (by simpa using Real.exp_pos _)]
    exact le_top
  obtain ⟨hfin, hle⟩ := toReal_klDiv_ouKernelVarPi_comp_le_zero ρ hv ha hmom hKL ht
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hKL,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal hle

end FormalizeSampling.ProbabilityFlowOUZero
