module

public import Mathlib.Topology.UniformSpace.Dini
public import FormalizeSampling.Flow.FokkerPlanckUniquenessLipschitzStep

/-!
# Uniform tightness of Fokker–Planck solutions and scaled smooth cutoffs

Status: **Verified.** Two auxiliary facts for `Flow/FokkerPlanckUniquenessLipschitz.lean`.

## Main results

* `exists_tail_le`: every curve of probability measures solving `WeakFokkerPlanck ρ b D`
  (any drift, any `D`) is **uniformly tight on compact time intervals**: for `T ≥ 0` and
  `ε > 0` there is `R` with `ρ_s{‖x‖ ≥ R'} ≤ ε` for all `R' ≥ R` and `s ∈ [0, T]`. No moment
  assumption is needed: `s ↦ ∫ χ_n dρ_s` is continuous for the Lipschitz cutoffs `χ_n`
  (`FokkerPlanckExistence.cutoff`), increases to `1` in `n`, and Dini's theorem
  (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) makes the convergence uniform on `[0, T]`.
* `exists_scaled_cutoff`: smooth cutoffs `χ_R(x) = χ₁(x / R)` with `χ_R = 1` on the ball of
  radius `R`, support in the ball of radius `ρ₁ R`, `‖∇χ_R‖ ≤ A₁ / R`, `|Δχ_R| ≤ A₂ / R²`, and
  `∇χ_R = 0`, `Δχ_R = 0` on `‖x‖ < R` (constants independent of `R ≥ 1`).

## Not proved here

* No rate in the tightness statement (no moments are assumed, so none can be given).
-/

public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-- The Lipschitz cutoff is continuous. -/
theorem continuous_cutoff (R : ℝ) : Continuous (cutoff (d := d) R) := by
  unfold cutoff; fun_prop

/-- The Lipschitz cutoff has compact support. -/
theorem hasCompactSupport_cutoff (R : ℝ) : HasCompactSupport (cutoff (d := d) R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) (R + 1)) fun x hx => by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact cutoff_eq_zero hx.le

/-- **Uniform tightness on compact time intervals (Verified).** If `ρ` is a curve of probability
measures on `t ≥ 0` solving `WeakFokkerPlanck ρ b D`, then for every `T` and `ε > 0` there is
`R` such that `ρ_s{x : R' ≤ ‖x‖} ≤ ε` for every `R' ≥ R` and every `s ∈ [0, T]`. -/
theorem exists_tail_le {ρ : ℝ → Measure (Fin d → ℝ)} {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {D : ℝ} (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ R' ≥ R, ∀ s ∈ Icc 0 T, (ρ s).real {x | R' ≤ ‖x‖} ≤ ε := by
  set F : ℕ → ℝ → ℝ := fun n s => ∫ x, cutoff (n : ℝ) x ∂(ρ s) with hF
  have hcont : ∀ n, ContinuousOn (F n) (Icc 0 T) := fun n s hs =>
    ((continuousWithinAt_integral_of_weakFokkerPlanck hprob hρ (continuous_cutoff _)
      (hasCompactSupport_cutoff _) hs.1).mono fun r hr => hr.1)
  have hmono : ∀ s ∈ Icc 0 T, Monotone (F · s) := by
    intro s hs n m hnm
    have := hprob s hs.1
    refine integral_mono ((continuous_cutoff _).integrable_of_hasCompactSupport
      (hasCompactSupport_cutoff _)) ((continuous_cutoff _).integrable_of_hasCompactSupport
      (hasCompactSupport_cutoff _)) fun x => ?_
    simp only [cutoff]
    have : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
    exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
  have hlim : ∀ s ∈ Icc 0 T, Tendsto (F · s) atTop (𝓝 ((fun _ => (1 : ℝ)) s)) := by
    intro s hs
    have := hprob s hs.1
    have h := tendsto_integral_of_dominated_convergence (μ := ρ s)
      (F := fun (n : ℕ) x => cutoff (n : ℝ) x) (f := fun _ => (1 : ℝ)) (fun _ => 1)
      (fun n => (continuous_cutoff _).aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (cutoff_nonneg _ _)]; exact cutoff_le_one _ _)
      (ae_of_all _ fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
        exact (cutoff_eq_one ((Nat.le_ceil _).trans (Nat.cast_le.2 hn))).symm)
    simpa using h
  have hU := Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc hcont hmono
    continuousOn_const hlim
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hU ε hε).exists
  refine ⟨N + 1, fun R' hR' s hs => ?_⟩
  have := hprob s hs.1
  have hd := hN s hs
  rw [Real.dist_eq, abs_lt] at hd
  have hmeas : MeasurableSet {x : Fin d → ℝ | (N : ℝ) + 1 ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hsub : {x : Fin d → ℝ | R' ≤ ‖x‖} ⊆ {x | (N : ℝ) + 1 ≤ ‖x‖} := fun x hx =>
    le_trans hR' hx
  have hle : F N s ≤ 1 - (ρ s).real {x | (N : ℝ) + 1 ≤ ‖x‖} := by
    have hI1 : Integrable ({x : Fin d → ℝ | (N : ℝ) + 1 ≤ ‖x‖}.indicator
        (1 : (Fin d → ℝ) → ℝ)) (ρ s) := (integrable_const (1 : ℝ)).indicator hmeas
    calc F N s ≤ ∫ x, (1 - {x : Fin d → ℝ | (N : ℝ) + 1 ≤ ‖x‖}.indicator 1 x) ∂(ρ s) := by
          refine integral_mono ((continuous_cutoff _).integrable_of_hasCompactSupport
            (hasCompactSupport_cutoff _)) ((integrable_const 1).sub hI1) fun x => ?_
          by_cases hx : (N : ℝ) + 1 ≤ ‖x‖
          · rw [Set.indicator_of_mem (show x ∈ {x : Fin d → ℝ | (N : ℝ) + 1 ≤ ‖x‖} from hx),
              cutoff_eq_zero hx]
            simp
          · rw [Set.indicator_of_notMem (show x ∉ {x : Fin d → ℝ | (N : ℝ) + 1 ≤ ‖x‖} from hx)]
            simpa using cutoff_le_one _ x
      _ = 1 - (ρ s).real {x | (N : ℝ) + 1 ≤ ‖x‖} := by
          rw [integral_sub (integrable_const 1) hI1, integral_indicator_one hmeas]
          simp
  calc (ρ s).real {x | R' ≤ ‖x‖} ≤ (ρ s).real {x | (N : ℝ) + 1 ≤ ‖x‖} :=
        measureReal_mono hsub
    _ ≤ 1 - F N s := by linarith
    _ ≤ ε := by linarith [hd.1]

/-- **Scaled smooth cutoffs (Verified).** There are constants `ρ₁ ≥ 1`, `A₁, A₂ ≥ 0` such that
for every `R ≥ 1` there is a smooth compactly supported `χ` with values in `[0, 1]`, `χ = 1` on
`‖x‖ ≤ R`, `tsupport χ ⊆ closedBall 0 (ρ₁ R)`, `‖∇χ‖ ≤ A₁ / R`, `|Δχ| ≤ A₂ / R²`, and
`∇χ(x) = 0`, `Δχ(x) = 0` whenever `‖x‖ < R`. -/
theorem exists_scaled_cutoff :
    ∃ ρ₁ A₁ A₂ : ℝ, 1 ≤ ρ₁ ∧ 0 ≤ A₁ ∧ 0 ≤ A₂ ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ χ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, ‖x‖ ≤ R → χ x = 1) ∧
        tsupport χ ⊆ closedBall 0 (ρ₁ * R) ∧ (∀ x, ‖grad χ x‖ ≤ A₁ / R) ∧
        (∀ x, |laplacian χ x| ≤ A₂ / R ^ 2) ∧
        ∀ x, ‖x‖ < R → grad χ x = 0 ∧ laplacian χ x = 0 := by
  obtain ⟨χ₁, hχ₁, hχ₁c, hI, h1, -⟩ :=
    exists_smooth_one_on_compact (isCompact_closedBall (0 : Fin d → ℝ) 2) one_pos
  have hχ₂ : ContDiff ℝ 2 χ₁ := hχ₁.of_le (by norm_cast)
  obtain ⟨A₁, hA₁⟩ := (continuous_grad hχ₂).bounded_above_of_compact_support
    (HasCompactSupport.intro hχ₁c.isCompact fun z hz =>
      ContinuityEquation.grad_eq_zero_of_notMem_tsupport hz)
  obtain ⟨A₂, hA₂⟩ := (continuous_laplacian hχ₂).bounded_above_of_compact_support
    (hasCompactSupport_laplacian hχ₁c)
  obtain ⟨r, hr⟩ := hχ₁c.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (norm_nonneg _).trans (hA₂ 0)
  -- derivatives vanish where `χ₁` is locally `1`
  have hloc : ∀ u : Fin d → ℝ, ‖u‖ < 2 → grad χ₁ u = 0 ∧ laplacian χ₁ u = 0 := by
    have hfd : ∀ v : Fin d → ℝ, ‖v‖ < 2 → fderiv ℝ χ₁ v = 0 := by
      intro v hv
      have hev : χ₁ =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_ball.mem_nhds (show v ∈ ball (0 : Fin d → ℝ) 2 by
          rwa [mem_ball, dist_zero_right])] with y hy
        exact h1 y (ball_subset_closedBall hy)
      rw [hev.fderiv_eq, fderiv_const_apply]
    intro u hu
    refine ⟨funext fun i => by simp [grad, partialDeriv, hfd u hu], ?_⟩
    refine Finset.sum_eq_zero fun i _ => ?_
    have hev : partialDeriv i χ₁ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds (show u ∈ ball (0 : Fin d → ℝ) 2 by
        rwa [mem_ball, dist_zero_right])] with y hy
      rw [mem_ball, dist_zero_right] at hy
      simp [partialDeriv, hfd y hy]
    simp only [partialDeriv]
    rw [hev.fderiv_eq, fderiv_const_apply]
    rfl
  refine ⟨max r 1, A₁, A₂, le_max_right _ _, hA₁0, hA₂0, fun R hR => ?_⟩
  have hR0 : 0 < R := one_pos.trans_le hR
  have hRi : R⁻¹ ≠ 0 := inv_ne_zero hR0.ne'
  have hnorm : ∀ x : Fin d → ℝ, ‖R⁻¹ • x‖ = ‖x‖ / R := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0), inv_mul_eq_div]
  refine ⟨fun x => χ₁ (R⁻¹ • x), hχ₁.comp (contDiff_const_smul _),
    hχ₁c.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ hRi), fun x => hI _,
    fun x hx => h1 _ ?_, ?_, fun x => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [mem_closedBall, dist_zero_right, hnorm, div_le_iff₀ hR0]
    linarith
  · intro x hx
    have hx' := tsupport_comp_subset_preimage χ₁ (continuous_const_smul R⁻¹) hx
    have := hr hx'
    rw [mem_closedBall, dist_zero_right, hnorm, div_le_iff₀ hR0] at this
    rw [mem_closedBall, dist_zero_right]
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0.le)
  · rw [grad_comp_smul (hχ₂.differentiable (by norm_num)), norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hR0), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hA₁ _) hR0.le
  · rw [laplacian_comp_smul hχ₂, abs_mul, abs_of_nonneg (by positivity), inv_pow,
      inv_mul_eq_div]
    have hl : |laplacian χ₁ (R⁻¹ • x)| ≤ A₂ := by
      simpa [Real.norm_eq_abs] using hA₂ (R⁻¹ • x)
    exact div_le_div_of_nonneg_right hl (by positivity)
  · have hu : ‖R⁻¹ • x‖ < 2 := by
      rw [hnorm, div_lt_iff₀ hR0]; linarith
    obtain ⟨hg, hl⟩ := hloc _ hu
    refine ⟨?_, ?_⟩
    · rw [grad_comp_smul (hχ₂.differentiable (by norm_num)), hg, smul_zero]
    · rw [laplacian_comp_smul hχ₂, hl, mul_zero]

end FormalizeSampling.FokkerPlanckUniqueness
