module

public import FormalizeSampling.Samplers.RGOCouplingLangevinContraction

/-!
# The synchronous Euler–Maruyama coupling of RGO laws

Status: **Verified** (no named hypotheses).

For `g` smooth convex with bounded derivatives (`SmoothConvexBdd g`), `η > 0` and a step `h`,
`syncStep` moves `((y, y'), (x, x'))` to `(F_y(x) + √(2h) ξ, F_{y'}(x') + √(2h) ξ)` with one
common Gaussian increment `ξ ∼ N(0, I_d)` (`F_y(x) = x + h b_y(x)`). `syncCoupling g η h k`
runs `k` such steps from the independent coupling `RGO(y) ⊗ RGO(y')`, and `syncCouplingN` lets
the number of steps depend measurably on `(y, y')`.

## Main results

* `syncCoupling_map_fst`, `syncCoupling_map_snd`: the marginals are the `k`-step EM laws of
  `b_y` (resp. `b_{y'}`) started at `RGO(y)` (resp. `RGO(y')`).
* `lintegral_sqDist_syncCoupling_le`: for `0 ≤ h ≤ η/2`, `h L ≤ 1`,
  `E |X_k - X'_k|² ≤ (1 - h/η)^k m(y, y') + |y - y'|²`, `m = indepCost` the cost of the
  independent coupling.
* `indepCost_lt_top`, `measurable_indepCost`: `m` is finite and measurable.
* `coupTime`, `coupSteps`, `ofReal_pow_mul_indepCost_le`: with `N = ⌊T(y, y') 2ⁿ⌋₊` dyadic
  steps, `T = η log(1 + m/ε) + 1`, the extra cost `(1 - 2⁻ⁿ/η)^N m(y, y')` is at most `ε`.

## Not proved here

* Any identification of the coupling with a coupling of SDE paths (no SDE theory).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingWeak
open FormalizeSampling.FokkerPlanckExistence (emStep emPow stepVar emCurve dyadicStep gridIndex)
open FormalizeSampling.ProximalLogConcaveRatePi
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingLangevin

variable {d : ℕ}

/-- Composition with a pushforward: `κ ∘ₘ f_# μ = (κ ∘ f) ∘ₘ μ`. -/
theorem comp_map_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel β γ) (μ : Measure α) {f : α → β} (hf : Measurable f) :
    κ ∘ₘ μ.map f = (κ.comap f hf) ∘ₘ μ := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hs) hf]
  rfl

section Construction

variable (g : (Fin d → ℝ) → ℝ) (η h : ℝ)

/-- The Euler–Maruyama drift map of the RGO Langevin dynamics, `F_y(x) = x + h b_y(x)`. -/
noncomputable def driftMap (y x : Fin d → ℝ) : Fin d → ℝ := x + h • rgoDrift g η y x

/-- The EM noise scale `√(2h)` (as `√(stepVar 1 h)`). -/
noncomputable def noiseScale (h : ℝ) : ℝ := Real.sqrt (stepVar 1 h)

/-- One **synchronous** EM step on the state `((y, y'), (x, x'))` with common Gaussian increment
`ξ`: `(x, x') ↦ (F_y(x) + √(2h) ξ, F_{y'}(x') + √(2h) ξ)`. -/
noncomputable def syncMap (w : (((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ))) ×
    (Fin d → ℝ)) : (Fin d → ℝ) × (Fin d → ℝ) :=
  (driftMap g η h w.1.1.1 w.1.2.1 + noiseScale h • w.2,
    driftMap g η h w.1.1.2 w.1.2.2 + noiseScale h • w.2)

/-- The synchronous EM step as a kernel from (parameters, state) to states. -/
noncomputable def syncStep :
    Kernel (((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ)))
      ((Fin d → ℝ) × (Fin d → ℝ)) :=
  (Kernel.id ×ₖ Kernel.const _ WeakFokkerPlanckOU.stdGauss).map (syncMap g η h)

/-- `k` synchronous EM steps with fixed parameters `(y, y')`. -/
noncomputable def syncPow :
    ℕ → Kernel (((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ)))
      ((Fin d → ℝ) × (Fin d → ℝ))
  | 0 => Kernel.deterministic Prod.snd measurable_snd
  | k + 1 => syncStep g η h ∘ₖ (Kernel.deterministic Prod.fst measurable_fst ×ₖ syncPow k)

/-- The initial law `δ_{(y, y')} ⊗ RGO(y) ⊗ RGO(y')` (independent coupling of the RGO laws). -/
noncomputable def syncInit :
    Kernel ((Fin d → ℝ) × (Fin d → ℝ))
      (((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ))) :=
  Kernel.id ×ₖ ((rgoKernelPi g η).comap Prod.fst measurable_fst ×ₖ
    (rgoKernelPi g η).comap Prod.snd measurable_snd)

/-- The `k`-step synchronous EM coupling started from the independent coupling. -/
noncomputable def syncCoupling (k : ℕ) :
    Kernel ((Fin d → ℝ) × (Fin d → ℝ)) ((Fin d → ℝ) × (Fin d → ℝ)) :=
  syncPow g η h k ∘ₖ syncInit g η

/-- `(k, p) ↦ syncCoupling k p` is measurable. -/
theorem measurable_syncCoupling_uncurry :
    Measurable fun kp : ℕ × ((Fin d → ℝ) × (Fin d → ℝ)) => syncCoupling g η h kp.1 kp.2 := by
  refine measurable_from_prod_countable_right (f := fun kp : ℕ × ((Fin d → ℝ) × (Fin d → ℝ)) =>
    syncCoupling g η h kp.1 kp.2) fun k => ?_
  exact (syncCoupling g η h k).measurable

/-- The synchronous coupling with a number of steps depending on the parameters. -/
noncomputable def syncCouplingN (N : (Fin d → ℝ) × (Fin d → ℝ) → ℕ) (hN : Measurable N) :
    Kernel ((Fin d → ℝ) × (Fin d → ℝ)) ((Fin d → ℝ) × (Fin d → ℝ)) :=
  Kernel.mk (fun p => syncCoupling g η h (N p) p) (by
    have h1 := (measurable_syncCoupling_uncurry g η h).comp (hN.prodMk measurable_id')
    exact h1)

/-- Evaluation of the variable-step coupling. -/
theorem syncCouplingN_apply (N : (Fin d → ℝ) × (Fin d → ℝ) → ℕ) (hN : Measurable N)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    syncCouplingN g η h N hN p = syncCoupling g η h (N p) p := rfl

end Construction

/-! ### Marginals of the synchronous coupling -/

section Marginals

variable {g : (Fin d → ℝ) → ℝ} {η : ℝ} (h : ℝ)

/-- The drift map is jointly continuous for `C²` potentials. -/
theorem continuous_driftMap (hg : ContDiff ℝ 2 g) :
    Continuous fun q : (Fin d → ℝ) × (Fin d → ℝ) => driftMap g η h q.1 q.2 := by
  have := (WeakFokkerPlanckOU.continuous_grad hg)
  unfold driftMap rgoDrift
  fun_prop

/-- The synchronous step map is measurable for `C²` potentials. -/
theorem measurable_syncMap (hg : ContDiff ℝ 2 g) : Measurable (syncMap (d := d) g η h) := by
  have hc := continuous_driftMap (η := η) h hg
  unfold syncMap
  refine Continuous.measurable ?_
  refine Continuous.prodMk ?_ ?_
  · exact (hc.comp ((continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_fst)))).add
      (continuous_snd.const_smul (noiseScale h))
  · exact (hc.comp ((continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_fst)))).add
      (continuous_snd.const_smul (noiseScale h))

/-- Evaluation of the synchronous step: the image of `N(0, I_d)` under the common-noise map. -/
theorem syncStep_apply (hg : ContDiff ℝ 2 g)
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ))) :
    syncStep g η h w = WeakFokkerPlanckOU.stdGauss.map fun ξ => syncMap g η h (w, ξ) := by
  rw [syncStep, Kernel.map_apply _ (measurable_syncMap h hg), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (measurable_syncMap h hg)
    measurable_prodMk_left]
  rfl

/-- The synchronous step is a Markov kernel. -/
theorem isMarkovKernel_syncStep (hg : ContDiff ℝ 2 g) : IsMarkovKernel (syncStep (d := d) g η h) :=
  Kernel.IsMarkovKernel.map _ (measurable_syncMap h hg)

/-- The iterated synchronous steps are Markov kernels. -/
theorem isMarkovKernel_syncPow (hg : ContDiff ℝ 2 g) (k : ℕ) :
    IsMarkovKernel (syncPow (d := d) g η h k) := by
  have := isMarkovKernel_syncStep (η := η) h hg
  induction k with
  | zero => unfold syncPow; infer_instance
  | succ k ih => unfold syncPow; infer_instance

/-- The first marginal of one synchronous step is the EM step of `b_y`. -/
theorem syncStep_map_fst (hg : ContDiff ℝ 2 g)
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ)))
    (hb : Measurable (rgoDrift g η w.1.1)) :
    (syncStep g η h w).map Prod.fst = emStep (rgoDrift g η w.1.1) hb 1 h w.2.1 := by
  have hm : Measurable fun ξ => syncMap g η h (w, ξ) :=
    (measurable_syncMap h hg).comp measurable_prodMk_left
  rw [syncStep_apply h hg, Measure.map_map (f := fun ξ => syncMap g η h (w, ξ)) measurable_fst hm,
    emStep, Kernel.comap_apply, HeatKernelPi.heatKernelPi_apply,
    WeakFokkerPlanckOU.pi_gaussianReal_eq_map]
  rfl

/-- The second marginal of one synchronous step is the EM step of `b_{y'}`. -/
theorem syncStep_map_snd (hg : ContDiff ℝ 2 g)
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ)))
    (hb : Measurable (rgoDrift g η w.1.2)) :
    (syncStep g η h w).map Prod.snd = emStep (rgoDrift g η w.1.2) hb 1 h w.2.2 := by
  have hm : Measurable fun ξ => syncMap g η h (w, ξ) :=
    (measurable_syncMap h hg).comp measurable_prodMk_left
  rw [syncStep_apply h hg, Measure.map_map (f := fun ξ => syncMap g η h (w, ξ)) measurable_snd hm,
    emStep, Kernel.comap_apply, HeatKernelPi.heatKernelPi_apply,
    WeakFokkerPlanckOU.pi_gaussianReal_eq_map]
  rfl

/-- `(δ_p ⊗ κ(p, z))` as a pushforward. -/
theorem deterministic_fst_prod_apply {κ : Kernel (((Fin d → ℝ) × (Fin d → ℝ)) ×
    ((Fin d → ℝ) × (Fin d → ℝ))) ((Fin d → ℝ) × (Fin d → ℝ))} [IsSFiniteKernel κ]
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ))) :
    (Kernel.deterministic Prod.fst measurable_fst ×ₖ κ) w = (κ w).map (Prod.mk w.1) := by
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod]

/-- **First marginal of `k` synchronous steps**: the `k`-step EM kernel of `b_y`. -/
theorem syncPow_map_fst (hg : ContDiff ℝ 2 g) (k : ℕ) (p z : (Fin d → ℝ) × (Fin d → ℝ))
    (hb : Measurable (rgoDrift g η p.1)) :
    (syncPow g η h k (p, z)).map Prod.fst = emPow (rgoDrift g η p.1) hb 1 h k z.1 := by
  have := isMarkovKernel_syncStep (η := η) h hg
  have := isMarkovKernel_syncPow (η := η) h hg
  induction k with
  | zero =>
    rw [syncPow, Kernel.deterministic_apply, Measure.map_dirac' measurable_fst, emPow,
      Kernel.id_apply]
  | succ k ih =>
    rw [syncPow, Kernel.comp_apply, deterministic_fst_prod_apply, Measure.map_comp _ _
      measurable_fst, comp_map_eq _ _ measurable_prodMk_left]
    have e : ((syncStep g η h).map Prod.fst).comap (Prod.mk p) measurable_prodMk_left =
        (emStep (rgoDrift g η p.1) hb 1 h).comap Prod.fst measurable_fst := by
      ext1 z'
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.map_apply _ measurable_fst]
      exact syncStep_map_fst h hg (p, z') hb
    rw [e, ← comp_map_eq, ih, emPow, Kernel.comp_apply]

/-- **Second marginal of `k` synchronous steps**: the `k`-step EM kernel of `b_{y'}`. -/
theorem syncPow_map_snd (hg : ContDiff ℝ 2 g) (k : ℕ) (p z : (Fin d → ℝ) × (Fin d → ℝ))
    (hb : Measurable (rgoDrift g η p.2)) :
    (syncPow g η h k (p, z)).map Prod.snd = emPow (rgoDrift g η p.2) hb 1 h k z.2 := by
  have := isMarkovKernel_syncStep (η := η) h hg
  have := isMarkovKernel_syncPow (η := η) h hg
  induction k with
  | zero =>
    rw [syncPow, Kernel.deterministic_apply, Measure.map_dirac' measurable_snd, emPow,
      Kernel.id_apply]
  | succ k ih =>
    rw [syncPow, Kernel.comp_apply, deterministic_fst_prod_apply, Measure.map_comp _ _
      measurable_snd, comp_map_eq _ _ measurable_prodMk_left]
    have e : ((syncStep g η h).map Prod.snd).comap (Prod.mk p) measurable_prodMk_left =
        (emStep (rgoDrift g η p.2) hb 1 h).comap Prod.snd measurable_snd := by
      ext1 z'
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.map_apply _ measurable_snd]
      exact syncStep_map_snd h hg (p, z') hb
    rw [e, ← comp_map_eq, ih, emPow, Kernel.comp_apply]

end Marginals

section CouplingMarginals

variable {g : (Fin d → ℝ) → ℝ} {η : ℝ} (h : ℝ)

/-- Evaluation of the initial law: `δ_p ⊗ (RGO(y) ⊗ RGO(y'))` as a pushforward. -/
theorem syncInit_apply (hg : SmoothConvexBdd g) (hη : 0 < η) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    syncInit g η p = ((rgoKernelPi g η p.1).prod (rgoKernelPi g η p.2)).map (Prod.mk p) := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  rw [syncInit, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, Kernel.prod_apply,
    Kernel.comap_apply, Kernel.comap_apply]

/-- The initial law is a Markov kernel. -/
theorem isMarkovKernel_syncInit (hg : SmoothConvexBdd g) (hη : 0 < η) :
    IsMarkovKernel (syncInit (d := d) g η) := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  unfold syncInit; infer_instance

/-- The synchronous couplings are Markov kernels. -/
theorem isMarkovKernel_syncCoupling (hg : SmoothConvexBdd g) (hη : 0 < η) (k : ℕ) :
    IsMarkovKernel (syncCoupling (d := d) g η h k) := by
  have := isMarkovKernel_syncInit hg hη
  have := isMarkovKernel_syncPow (η := η) h hg.2.1 k
  unfold syncCoupling; infer_instance

/-- The synchronous couplings with variable step number are Markov kernels. -/
theorem isMarkovKernel_syncCouplingN (hg : SmoothConvexBdd g) (hη : 0 < η)
    (N : (Fin d → ℝ) × (Fin d → ℝ) → ℕ) (hN : Measurable N) :
    IsMarkovKernel (syncCouplingN g η h N hN) :=
  ⟨fun p => (isMarkovKernel_syncCoupling h hg hη (N p)).isProbabilityMeasure p⟩

/-- **First marginal of the `k`-step coupling**: `k` EM steps of `b_y` started at `RGO(y)`. -/
theorem syncCoupling_map_fst (hg : SmoothConvexBdd g) (hη : 0 < η) (k : ℕ)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) (hb : Measurable (rgoDrift g η p.1)) :
    (syncCoupling g η h k p).map Prod.fst =
      emPow (rgoDrift g η p.1) hb 1 h k ∘ₘ rgoKernelPi g η p.1 := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  have := isMarkovKernel_syncPow (η := η) h hg.2.1 k
  rw [syncCoupling, Kernel.comp_apply, syncInit_apply hg hη, Measure.map_comp _ _ measurable_fst,
    comp_map_eq _ _ measurable_prodMk_left]
  have e : ((syncPow g η h k).map Prod.fst).comap (Prod.mk p) measurable_prodMk_left =
      (emPow (rgoDrift g η p.1) hb 1 h k).comap Prod.fst measurable_fst := by
    ext1 z
    rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.map_apply _ measurable_fst]
    exact syncPow_map_fst h hg.2.1 k p z hb
  rw [e, ← comp_map_eq, Measure.map_fst_prod, measure_univ, one_smul]

/-- **Second marginal of the `k`-step coupling**: `k` EM steps of `b_{y'}` started at
`RGO(y')`. -/
theorem syncCoupling_map_snd (hg : SmoothConvexBdd g) (hη : 0 < η) (k : ℕ)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) (hb : Measurable (rgoDrift g η p.2)) :
    (syncCoupling g η h k p).map Prod.snd =
      emPow (rgoDrift g η p.2) hb 1 h k ∘ₘ rgoKernelPi g η p.2 := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  have := isMarkovKernel_syncPow (η := η) h hg.2.1 k
  rw [syncCoupling, Kernel.comp_apply, syncInit_apply hg hη, Measure.map_comp _ _ measurable_snd,
    comp_map_eq _ _ measurable_prodMk_left]
  have e : ((syncPow g η h k).map Prod.snd).comap (Prod.mk p) measurable_prodMk_left =
      (emPow (rgoDrift g η p.2) hb 1 h k).comap Prod.snd measurable_snd := by
    ext1 z
    rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.map_apply _ measurable_snd]
    exact syncPow_map_snd h hg.2.1 k p z hb
  rw [e, ← comp_map_eq, Measure.map_snd_prod, measure_univ, one_smul]

end CouplingMarginals

/-! ### Transport cost of the synchronous coupling -/

section Cost

variable {g : (Fin d → ℝ) → ℝ} {η : ℝ} (h : ℝ)

/-- The common noise cancels: `|(a + c) - (b + c)|² = |a - b|²`. -/
theorem sqDist_add_add (a b c : Fin d → ℝ) : sqDist (a + c) (b + c) = sqDist a b := by
  simp [sqDist]

/-- The cost after one synchronous step is deterministic: the drift maps' squared distance. -/
theorem lintegral_sqDist_syncStep (hg : ContDiff ℝ 2 g)
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) × ((Fin d → ℝ) × (Fin d → ℝ))) :
    ∫⁻ q, ENNReal.ofReal (sqDist q.1 q.2) ∂(syncStep g η h w) =
      ENNReal.ofReal (sqDist (driftMap g η h w.1.1 w.2.1) (driftMap g η h w.1.2 w.2.2)) := by
  have hm : Measurable fun ξ => syncMap g η h (w, ξ) :=
    (measurable_syncMap h hg).comp measurable_prodMk_left
  rw [syncStep_apply h hg, lintegral_map measurable_ofReal_sqDist hm]
  simp only [syncMap, sqDist_add_add]
  rw [lintegral_const, measure_univ, mul_one]

/-- `ofReal a * ofReal x + ofReal y = ofReal (a x + y)` for nonnegative reals. -/
theorem ofReal_mul_add_ofReal {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal a * ENNReal.ofReal x + ENNReal.ofReal y = ENNReal.ofReal (a * x + y) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (mul_nonneg ha hx) hy]

/-- **Cost of `k` synchronous steps.** Under the step-size conditions of `sqDist_step_le`,
with `λ = 1 - h / η`:
`E |X_k - X'_k|² ≤ λ^k |x - x'|² + (1 - λ^k) |y - y'|²` from `(x, x')`. -/
theorem lintegral_sqDist_syncPow_le (hg : SmoothConvexBdd g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) (hη : 0 < η) (hh : 0 ≤ h) (hhη : h ≤ η / 2)
    (hhL : h * L ≤ 1) (k : ℕ) (p z : (Fin d → ℝ) × (Fin d → ℝ)) :
    ∫⁻ q, ENNReal.ofReal (sqDist q.1 q.2) ∂(syncPow g η h k (p, z)) ≤
      ENNReal.ofReal ((1 - h / η) ^ k * sqDist z.1 z.2 +
        (1 - (1 - h / η) ^ k) * sqDist p.1 p.2) := by
  have := isMarkovKernel_syncStep (η := η) h hg.2.1
  have := isMarkovKernel_syncPow (η := η) h hg.2.1
  set a := 1 - h / η with ha
  have hc : h / η ≤ 1 / 2 := by rw [div_le_iff₀ hη]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith [div_nonneg hh hη.le]
  have hr := sqDist_nonneg p.1 p.2
  induction k with
  | zero =>
    rw [syncPow, Kernel.deterministic_apply, lintegral_dirac' _ measurable_ofReal_sqDist]
    simp
  | succ k ih =>
    rw [syncPow, Kernel.lintegral_comp _ _ _ measurable_ofReal_sqDist,
      deterministic_fst_prod_apply, lintegral_map
        (Measurable.lintegral_kernel measurable_ofReal_sqDist) measurable_prodMk_left]
    simp_rw [lintegral_sqDist_syncStep h hg.2.1]
    have hak : 0 ≤ a ^ k := pow_nonneg ha0 k
    have hak1 : a ^ k ≤ 1 := pow_le_one₀ ha0 ha1
    calc ∫⁻ z', ENNReal.ofReal (sqDist (driftMap g η h (p, z').1.1 (p, z').2.1)
          (driftMap g η h (p, z').1.2 (p, z').2.2)) ∂(syncPow g η h k (p, z))
        ≤ ∫⁻ z', ENNReal.ofReal a * ENNReal.ofReal (sqDist z'.1 z'.2) +
            ENNReal.ofReal ((1 - a) * sqDist p.1 p.2) ∂(syncPow g η h k (p, z)) := by
          refine lintegral_mono fun z' => ?_
          rw [ofReal_mul_add_ofReal ha0 (sqDist_nonneg _ _) (by nlinarith)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := sqDist_step_le hg hL0 hL hη hh hhη hhL p.1 p.2 z'.1 z'.2
          rw [show 1 - a = h / η by rw [ha]; ring]
          exact this
      _ = ENNReal.ofReal a * ∫⁻ z', ENNReal.ofReal (sqDist z'.1 z'.2) ∂(syncPow g η h k (p, z))
            + ENNReal.ofReal ((1 - a) * sqDist p.1 p.2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
            measurable_ofReal_sqDist, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal (a ^ k * sqDist z.1 z.2 +
            (1 - a ^ k) * sqDist p.1 p.2) + ENNReal.ofReal ((1 - a) * sqDist p.1 p.2) := by
          gcongr
      _ = ENNReal.ofReal (a ^ (k + 1) * sqDist z.1 z.2 +
            (1 - a ^ (k + 1)) * sqDist p.1 p.2) := by
          rw [ofReal_mul_add_ofReal ha0 (by have := sqDist_nonneg z.1 z.2; nlinarith)
            (by nlinarith)]
          congr 1; ring

/-- The expected squared distance under the independent coupling `RGO(y) ⊗ RGO(y')`. -/
noncomputable def indepCost (g : (Fin d → ℝ) → ℝ) (η : ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (sqDist z.1 z.2) ∂((rgoKernelPi g η p.1).prod (rgoKernelPi g η p.2))

/-- **Cost of the `k`-step coupling**: `E |X_k - X'_k|² ≤ λ^k m(y, y') + |y - y'|²` with
`m = indepCost`. -/
theorem lintegral_sqDist_syncCoupling_le (hg : SmoothConvexBdd g) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) (hη : 0 < η) (hh : 0 ≤ h) (hhη : h ≤ η / 2)
    (hhL : h * L ≤ 1) (k : ℕ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    ∫⁻ q, ENNReal.ofReal (sqDist q.1 q.2) ∂(syncCoupling g η h k p) ≤
      ENNReal.ofReal ((1 - h / η) ^ k) * indepCost g η p +
        ENNReal.ofReal (sqDist p.1 p.2) := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  have hc : h / η ≤ 1 / 2 := by rw [div_le_iff₀ hη]; linarith
  have ha0 : 0 ≤ 1 - h / η := by linarith
  have ha1 : 1 - h / η ≤ 1 := by linarith [div_nonneg hh hη.le]
  have hak : 0 ≤ (1 - h / η) ^ k := pow_nonneg ha0 k
  have hak1 : (1 - h / η) ^ k ≤ 1 := pow_le_one₀ ha0 ha1
  have hr := sqDist_nonneg p.1 p.2
  rw [syncCoupling, Kernel.lintegral_comp _ _ _ measurable_ofReal_sqDist, syncInit_apply hg hη,
    lintegral_map (Measurable.lintegral_kernel measurable_ofReal_sqDist) measurable_prodMk_left,
    indepCost, ← lintegral_const_mul _ measurable_ofReal_sqDist]
  calc ∫⁻ z, ∫⁻ q, ENNReal.ofReal (sqDist q.1 q.2) ∂(syncPow g η h k (p, z))
        ∂((rgoKernelPi g η p.1).prod (rgoKernelPi g η p.2))
      ≤ ∫⁻ z, ENNReal.ofReal ((1 - h / η) ^ k) * ENNReal.ofReal (sqDist z.1 z.2) +
          ENNReal.ofReal (sqDist p.1 p.2)
          ∂((rgoKernelPi g η p.1).prod (rgoKernelPi g η p.2)) := by
        refine lintegral_mono fun z => ?_
        refine (lintegral_sqDist_syncPow_le h hg hL0 hL hη hh hhη hhL k p z).trans ?_
        rw [ofReal_mul_add_ofReal hak (sqDist_nonneg _ _) hr]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

end Cost

/-! ### The independent coupling has finite cost; choice of the number of steps -/

section Steps

variable {g : (Fin d → ℝ) → ℝ} {η : ℝ}

/-- `|x - x'|² ≤ 2d exp ‖x‖ exp ‖x'‖` (Euclidean squared distance vs sup norms). -/
theorem sqDist_le_exp_mul_exp (x x' : Fin d → ℝ) :
    sqDist x x' ≤ 2 * d * (Real.exp ‖x‖ * Real.exp ‖x'‖) := by
  have h1 : sqDist x x' ≤ d * ‖x - x'‖ ^ 2 := by
    unfold sqDist
    calc ∑ i, (x i - x' i) ^ 2 ≤ ∑ _i : Fin d, ‖x - x'‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := norm_le_pi_norm (x - x') i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = d * ‖x - x'‖ ^ 2 := by simp
  have h2 : ‖x - x'‖ ≤ ‖x‖ + ‖x'‖ := norm_sub_le x x'
  have h3 : (‖x‖ + ‖x'‖) ^ 2 ≤ 2 * Real.exp (‖x‖ + ‖x'‖) := by
    have := Real.quadratic_le_exp_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg x'))
    nlinarith [norm_nonneg x, norm_nonneg x']
  rw [← Real.exp_add]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc sqDist x x' ≤ d * ‖x - x'‖ ^ 2 := h1
    _ ≤ d * (‖x‖ + ‖x'‖) ^ 2 := by gcongr
    _ ≤ d * (2 * Real.exp (‖x‖ + ‖x'‖)) := by gcongr
    _ = 2 * d * Real.exp (‖x‖ + ‖x'‖) := by ring

/-- **The independent coupling of two RGO laws has finite quadratic cost.** -/
theorem indepCost_lt_top (hg : SmoothConvexBdd g) (hη : 0 < η)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) : indepCost g η p < ∞ := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  have hb : ∀ z : (Fin d → ℝ) × (Fin d → ℝ), ENNReal.ofReal (sqDist z.1 z.2) ≤
      ENNReal.ofReal (2 * d) * (ENNReal.ofReal (Real.exp ‖z.1‖) *
        ENNReal.ofReal (Real.exp ‖z.2‖)) := fun z => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sqDist_le_exp_mul_exp z.1 z.2)
  refine (lintegral_mono hb).trans_lt ?_
  rw [lintegral_const_mul _ (by fun_prop),
    lintegral_prod_mul (f := fun x => ENNReal.ofReal (Real.exp ‖x‖))
      (g := fun x => ENNReal.ofReal (Real.exp ‖x‖)) (by fun_prop) (by fun_prop)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
    (lintegral_exp_norm_lt_top hg hη p.1) (lintegral_exp_norm_lt_top hg hη p.2))

/-- The cost of the independent coupling is measurable in the parameters. -/
theorem measurable_indepCost (hg : SmoothConvexBdd g) (hη : 0 < η) :
    Measurable (indepCost (d := d) g η) := by
  have := isMarkovKernel_rgoKernelPi' hg hη
  have h := Measurable.lintegral_kernel (κ := (rgoKernelPi g η).comap Prod.fst measurable_fst ×ₖ
    (rgoKernelPi g η).comap Prod.snd measurable_snd) (measurable_ofReal_sqDist (d := d))
  convert h using 1
  funext p
  rw [Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]
  rfl

variable (g η)

/-- The (parameter-dependent) time horizon `T(y, y') = η log(1 + m(y, y') / ε) + 1`, chosen so
that `e^{-(T - 1)/η} m(y, y') ≤ ε`. -/
noncomputable def coupTime (ε : ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ :=
  η * Real.log (1 + (indepCost g η p).toReal / ε) + 1

/-- The number of dyadic EM steps of size `2⁻ⁿ` up to time `T(y, y')`. -/
noncomputable def coupSteps (ε : ℝ) (n : ℕ) (p : (Fin d → ℝ) × (Fin d → ℝ)) : ℕ :=
  gridIndex n (coupTime g η ε p)

variable {g η}

/-- The time horizon is at least one (`η, ε > 0`). -/
theorem one_le_coupTime (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    1 ≤ coupTime g η ε p := by
  unfold coupTime
  have h0 : 0 ≤ (indepCost g η p).toReal / ε := div_nonneg ENNReal.toReal_nonneg hε.le
  have : 0 ≤ Real.log (1 + (indepCost g η p).toReal / ε) := Real.log_nonneg (by linarith)
  have := mul_nonneg hη.le this
  linarith

/-- The number of steps is measurable in the parameters. -/
theorem measurable_coupSteps (hg : SmoothConvexBdd g) (hη : 0 < η) (ε : ℝ) (n : ℕ) :
    Measurable (coupSteps (d := d) g η ε n) := by
  unfold coupSteps gridIndex coupTime
  have := (measurable_indepCost hg hη).ennreal_toReal
  refine Measurable.nat_floor ?_
  fun_prop

/-- **Exponential forgetting of the initial coupling.** If `h ≤ min 1 η`, `m ≥ 0`, `ε > 0`
and `N h ≥ T - h` with `T = η log(1 + m / ε) + 1`, then `(1 - h / η)^N m ≤ ε`. -/
theorem pow_mul_le_of_le {h m ε : ℝ} (hη : 0 < η) (hh1 : h ≤ 1) (hhη : h ≤ η)
    (hm : 0 ≤ m) (hε : 0 < ε) {N : ℕ}
    (hN : η * Real.log (1 + m / ε) + 1 - h ≤ N * h) : (1 - h / η) ^ N * m ≤ ε := by
  have ha0 : 0 ≤ 1 - h / η := by rw [sub_nonneg, div_le_one hη]; exact hhη
  have h1 : (1 - h / η) ^ N ≤ Real.exp (-(N * h) / η) := by
    calc (1 - h / η) ^ N ≤ Real.exp (-(h / η)) ^ N := by
          gcongr
          have := Real.add_one_le_exp (-(h / η)); linarith
      _ = Real.exp (-(N * h) / η) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hq : 0 < 1 + m / ε := by positivity
  have h2 : Real.exp (-(N * h) / η) ≤ (1 + m / ε)⁻¹ := by
    rw [← Real.exp_log hq, ← Real.exp_neg, Real.exp_le_exp, div_le_iff₀ hη]
    nlinarith
  have h3 : (1 + m / ε)⁻¹ * m ≤ ε := by
    rw [inv_mul_le_iff₀ hq, add_mul, one_mul, div_mul_cancel₀ _ hε.ne']
    linarith
  calc (1 - h / η) ^ N * m ≤ (1 + m / ε)⁻¹ * m := by gcongr; exact h1.trans h2
    _ ≤ ε := h3

/-- **The cost added by the coupling is at most `ε`** once the dyadic step `h = 2⁻ⁿ` satisfies
`h ≤ η`: `(1 - h / η)^{N(y, y')} m(y, y') ≤ ε`. -/
theorem ofReal_pow_mul_indepCost_le (hg : SmoothConvexBdd g) (hη : 0 < η) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hhη : dyadicStep n ≤ η) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    ENNReal.ofReal ((1 - dyadicStep n / η) ^ coupSteps g η ε n p) * indepCost g η p ≤
      ENNReal.ofReal ε := by
  have hfin := (indepCost_lt_top hg hη p).ne
  set m := (indepCost g η p).toReal with hm
  have hh : 0 < dyadicStep n := by unfold dyadicStep; positivity
  have hh1 : dyadicStep n ≤ 1 := by unfold dyadicStep; exact pow_le_one₀ (by norm_num) (by norm_num)
  have ha0 : 0 ≤ 1 - dyadicStep n / η := by rw [sub_nonneg, div_le_one hη]; exact hhη
  rw [← ENNReal.ofReal_toReal hfin, ← hm, ← ENNReal.ofReal_mul (pow_nonneg ha0 _)]
  refine ENNReal.ofReal_le_ofReal (pow_mul_le_of_le hη hh1 hhη ENNReal.toReal_nonneg hε ?_)
  -- `N h ≥ T - h` for `N = ⌊T 2ⁿ⌋₊`, `h = 2⁻ⁿ`
  have hT := one_le_coupTime (g := g) hη hε p
  have hfl := Nat.lt_floor_add_one (coupTime g η ε p * 2 ^ n)
  have e : dyadicStep n * 2 ^ n = 1 := by
    unfold dyadicStep; rw [← mul_pow]; norm_num
  unfold coupSteps gridIndex
  have : coupTime g η ε p - dyadicStep n ≤ (⌊coupTime g η ε p * 2 ^ n⌋₊ : ℝ) * dyadicStep n := by
    have h2 : coupTime g η ε p * 2 ^ n - 1 ≤ (⌊coupTime g η ε p * 2 ^ n⌋₊ : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right h2 hh.le
    calc coupTime g η ε p - dyadicStep n
        = (coupTime g η ε p * 2 ^ n - 1) * dyadicStep n := by
          rw [sub_mul, mul_assoc, mul_comm (2 ^ n : ℝ), e]; ring
      _ ≤ _ := this
  exact this

end Steps

end FormalizeSampling.RGOCouplingLangevin
