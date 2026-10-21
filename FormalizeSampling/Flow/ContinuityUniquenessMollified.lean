module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import FormalizeSampling.Flow.ContinuityUniquenessLipschitz

/-!
# Mollified Euler velocities for the weak continuity equation

Status: **Verified.** Two ingredients of the uniqueness theorems for the named PDE-uniqueness
input `NoiseScore.UniqueWeakContinuity v` of FL-5 (`Flow/NoiseScoreEquivalence.lean`) when the
velocity `v` is only Lipschitz (no differentiability in `x` or `t`); the theorems themselves
are in `Flow/ContinuityUniquenessLocal.lean`.

## Main results

* `exists_contDiff_lipschitz_approx`: an `L`-Lipschitz `f : ℝᵈ → ℝᵈ` has, for every `r > 0`,
  a `C^∞` approximant `g = κ_r ⋆ f` (`κ_r` a normalized `ContDiffBump` of outer radius `r`)
  with `‖Dg‖ ≤ L` and `‖g - f‖ ≤ L r` uniformly.
* `abs_integral_eulerStep_le_of_approx`: one frozen-velocity Euler step with an Euler velocity
  `w_t` (`C³`) different from the solution velocity `v`. With `ψ(s, x) = Ψ(x + (t - s) w_t(x))`
  the transport residual against `v` is `DΨ(y) (v_s(x) - w_t(x) + (t - s) Dw_t(x) v_s(x))`, so
  only `‖v_s - w_t‖ ≤ ε` and `‖Dw_t v_s‖ ≤ B` on the relevant compact set are needed.

## Not proved here

* No uniqueness theorem is stated here: the telescoped estimate and the uniqueness theorems
  (locally Lipschitz velocities of linear growth, and as corollaries the globally Lipschitz
  ones `uniqueWeakContinuity_of_lipschitz_continuous` and
  `uniqueWeakContinuity_of_autonomous_lipschitzWith`) are in
  `Flow/ContinuityUniquenessLocal.lean`.
-/

public section

open MeasureTheory Matrix Set Filter Topology Metric Asymptotics Convolution
open scoped ContDiff

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **Smooth approximation of a Lipschitz map with the same constant (Verified).** If
`f : ℝᵈ → ℝᵈ` satisfies `‖f x - f y‖ ≤ L ‖x - y‖` (`L ≥ 0`) and `r > 0`, there is a `C^∞` map
`g` with `‖Dg(x)‖ ≤ L` and `‖g(x) - f(x)‖ ≤ L r` for all `x`. Construction: `g = κ ⋆ f` with
`κ` the normalized `ContDiffBump` of outer radius `r` (Lebesgue measure); `g` is `L`-Lipschitz
since `κ ≥ 0`, `∫ κ = 1`. -/
theorem exists_contDiff_lipschitz_approx {f : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) {r : ℝ} (hr : 0 < r) :
    ∃ g : (Fin d → ℝ) → Fin d → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L) ∧
      ∀ x, ‖g x - f x‖ ≤ L * r := by
  have hfc : Continuous f := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun y => hf y x) ?_
    have : Tendsto (fun y => L * ‖y - x‖) (𝓝 x) (𝓝 (L * ‖x - x‖)) :=
      ((continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x)
    simpa using this
  set φ : ContDiffBump (0 : Fin d → ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set κ := φ.normed (volume : Measure (Fin d → ℝ))
  set g : (Fin d → ℝ) → Fin d → ℝ := κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hgd : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (hfc.locallyIntegrable)
  have hint : ∀ x, Integrable (fun t => κ t • f (x - t)) volume := fun x =>
    (φ.continuous_normed.smul (hfc.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport φ.hasCompactSupport_normed.smul_right
  have hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ := by
    intro x y
    have e : g x - g y = ∫ t, κ t • (f (x - t) - f (y - t)) := by
      simp only [g, convolution_lsmul, smul_sub]
      rw [integral_sub (hint x) (hint y)]
    rw [e]
    calc ‖∫ t, κ t • (f (x - t) - f (y - t))‖ ≤ ∫ t, κ t * (L * ‖x - y‖) := by
          refine norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
          refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
          simpa using hf (x - t) (y - t)
      _ = L * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]
  refine ⟨g, hgd, fun x => norm_fderiv_le_of_lip' ℝ hL
    (Eventually.of_forall fun y => hlip y x), fun x => ?_⟩
  rw [← dist_eq_norm]
  refine φ.dist_normed_convolution_le hfc.aestronglyMeasurable fun z hz => ?_
  rw [dist_eq_norm]
  refine (hf z x).trans (mul_le_mul_of_nonneg_left ?_ hL)
  rw [← dist_eq_norm]; exact (mem_ball.1 hz).le

/-- **Euler step with a different Euler velocity (Verified).** Let `ρ` be a probability
solution of `WeakContinuity2 ρ v` on `t ≥ 0`, `0 ≤ h ≤ t`, `w_t ∈ C³` (the Euler velocity at
time `t`, unrelated to `v` a priori), `v_s` continuous for `s ∈ [t - h, t]`, `Ψ ∈ C³` with
`‖DΨ‖ ≤ G`. Suppose for `s ∈ [t - h, t]` the point `x + (t - s) w_t(x)` lies outside
`tsupport Ψ` whenever `x ∉ K` (`K` compact), and on `[t - h, t] × K`: `‖v_s(x) - w_t(x)‖ ≤ ε`
and `‖Dw_t(x) v_s(x)‖ ≤ B` (`ε, B ≥ 0`). Then
`|∫ Ψ dρ_t - ∫ Ψ(x + h w_t(x)) dρ_{t-h}(x)| ≤ G (ε + h B) h`. Proof:
`abs_integral_sub_le_of_approx_dual` with `ψ(s, x) = Ψ(x + (t - s) w_t(x))`. -/
theorem abs_integral_eulerStep_le_of_approx {ρ : ℝ → Measure (Fin d → ℝ)}
    {v w : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakContinuity2 ρ v)
    {t h : ℝ} (hh : 0 ≤ h) (ht : h ≤ t) (hwt : ContDiff ℝ 3 (w t))
    (hvcs : ∀ s ∈ Icc (t - h) t, Continuous (v s)) {Ψ : (Fin d → ℝ) → ℝ} (hΨ : ContDiff ℝ 3 Ψ)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hΨK : ∀ s ∈ Icc (t - h) t, ∀ x ∉ K, x + (t - s) • w t x ∉ tsupport Ψ)
    {G ε B : ℝ} (hG : ∀ y, ‖fderiv ℝ Ψ y‖ ≤ G) (hε0 : 0 ≤ ε) (hB0 : 0 ≤ B)
    (hε : ∀ s ∈ Icc (t - h) t, ∀ x ∈ K, ‖v s x - w t x‖ ≤ ε)
    (hB : ∀ s ∈ Icc (t - h) t, ∀ x ∈ K, ‖fderiv ℝ (w t) x (v s x)‖ ≤ B) :
    |∫ x, Ψ x ∂(ρ t) - ∫ x, Ψ (x + h • w t x) ∂(ρ (t - h))| ≤ G * (ε + h * B) * h := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hwd : Differentiable ℝ (w t) := hwt.differentiable (by norm_num)
  have hY : ∀ s, ContDiff ℝ 3 (fun x : Fin d → ℝ => x + (t - s) • w t x) := fun s =>
    contDiff_id.add (hwt.const_smul (t - s))
  set ψ : ℝ → (Fin d → ℝ) → ℝ := fun s x => Ψ (x + (t - s) • w t x) with hψdef
  set g : ℝ → (Fin d → ℝ) → ℝ := fun s x =>
    -(fderiv ℝ Ψ (x + (t - s) • w t x) (w t x)) with hgdef
  have hψ : ∀ s ∈ Icc (t - h) t, TestFunction2 (ψ s) := fun s hs =>
    ⟨(hΨ.comp (hY s)).of_le (by norm_num),
      HasCompactSupport.intro hK fun x hx =>
        show Ψ _ = 0 from image_eq_zero_of_notMem_tsupport (hΨK s hs x hx)⟩
  have hg : ∀ s ∈ Icc (t - h) t, TestFunction2 (g s) := fun s hs =>
    ⟨(((hΨ.fderiv_right (m := 2) (by norm_num)).comp ((hY s).of_le (by norm_num))).clm_apply
        (hwt.of_le (by norm_num))).neg,
      HasCompactSupport.intro hK fun x hx => by
        simp [g, fderiv_of_notMem_tsupport ℝ (hΨK s hs x hx)]⟩
  have hd : ∀ s x, HasDerivAt (fun u => ψ u x) (g s x) s := by
    intro s x
    have hin : HasDerivAt (fun u => x + (t - u) • w t x) ((0 - 1 : ℝ) • w t x) s :=
      (((hasDerivAt_const s t).sub (hasDerivAt_id s)).smul_const (w t x)).const_add x
    refine ((hΨd _).hasFDerivAt.comp_hasDerivAt s hin).congr_deriv ?_
    simp [g]
  have hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) := by
    have hw : Continuous (fun q : ℝ × (Fin d → ℝ) => w t q.2) :=
      hwt.continuous.comp continuous_snd
    have hYc : Continuous (fun q : ℝ × (Fin d → ℝ) => q.2 + (t - q.1) • w t q.2) :=
      continuous_snd.add ((continuous_const.sub continuous_fst).smul hw)
    exact (((hΨ.continuous_fderiv (by norm_num)).comp hYc).clm_apply hw).neg
  have hres : ∀ s ∈ Icc (t - h) t, ∀ x,
      |g s x + v s x ⬝ᵥ grad (ψ s) x| ≤ G * (ε + h * B) := by
    intro s hs x
    have hYd : HasFDerivAt (fun x : Fin d → ℝ => x + (t - s) • w t x)
        (ContinuousLinearMap.id ℝ (Fin d → ℝ) + (t - s) • fderiv ℝ (w t) x) x :=
      (hasFDerivAt_id x).add ((hwd x).hasFDerivAt.const_smul (t - s))
    have hψF : fderiv ℝ (ψ s) x = (fderiv ℝ Ψ (x + (t - s) • w t x)).comp
        (ContinuousLinearMap.id ℝ (Fin d → ℝ) + (t - s) • fderiv ℝ (w t) x) :=
      ((hΨd _).hasFDerivAt.comp x hYd).fderiv
    have hexp : g s x + v s x ⬝ᵥ grad (ψ s) x = fderiv ℝ Ψ (x + (t - s) • w t x)
        ((v s x - w t x) + (t - s) • fderiv ℝ (w t) x (v s x)) := by
      rw [dotProduct_grad, hψF]
      simp only [g, ContinuousLinearMap.comp_apply, _root_.add_apply,
        ContinuousLinearMap.id_apply, _root_.smul_apply, map_add, map_sub,
        map_smul]
      ring
    rw [hexp, ← Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · have hts : 0 ≤ t - s := sub_nonneg.2 hs.2
      have hts' : t - s ≤ h := by linarith [hs.1]
      calc _ ≤ ‖fderiv ℝ Ψ (x + (t - s) • w t x)‖ *
            ‖(v s x - w t x) + (t - s) • fderiv ℝ (w t) x (v s x)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ G * (ε + h * B) := by
          refine mul_le_mul (hG _) ?_ (norm_nonneg _) hG0
          refine (norm_add_le _ _).trans (add_le_add (hε s hs x hx) ?_)
          rw [norm_smul, Real.norm_of_nonneg hts]
          exact mul_le_mul hts' (hB s hs x hx) (norm_nonneg _) hh
    · rw [fderiv_of_notMem_tsupport ℝ (hΨK s hs x hx)]
      simp only [_root_.zero_apply, norm_zero]
      positivity
  have key := abs_integral_sub_le_of_approx_dual hprob hρ (sub_nonneg.2 ht)
    (by linarith) hψ hg hd hgc hK (fun s hs x hx => by
      simp [g, fderiv_of_notMem_tsupport ℝ (hΨK s hs x hx)]) hvcs hres
  simpa [ψ, sub_sub_cancel] using key

end NoiseScore
end FormalizeSampling
