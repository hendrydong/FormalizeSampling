module

public import FormalizeSampling.Flow.FokkerPlanckUniqueness
public import FormalizeSampling.Flow.FokkerPlanckExistenceLinear
public import FormalizeSampling.Flow.FokkerPlanckExistenceDissipative
public import FormalizeSampling.Flow.FokkerPlanckExistenceContinuousTime

/-!
# Uniqueness for the weak Fokker–Planck equation with linearly growing drifts

Status: **Verified.** Extends `Flow/FokkerPlanckUniqueness.lean` (continuous **bounded** drifts)
to the unbounded, linearly growing drifts

  `b_t(x) = -a x + b₀(t, x)`,  `a ≥ 0`, `b₀(t, ·)` continuous with `‖b₀‖ ≤ B`

(hypothesis form: `b t` continuous and `‖b t x + a • x‖ ≤ B` for `t ≥ 0`; no Lipschitz
condition, no regularity in `t`), for `D > 0`, among **all** curves of probability measures on
`t ≥ 0` (no moment or tightness assumption).

## Main results

* `eq_of_weakFokkerPlanck_linear_add_bounded`: uniqueness for the drifts above.
* `existsUnique_weakFokkerPlanck_locallyLipschitz_linear_add_bounded`: well-posedness for
  locally Lipschitz `b` of this form (existence via the dissipative construction,
  `dotProduct_le_of_linear_add_bounded`). For globally Lipschitz drifts, well-posedness and the
  Euler–Maruyama identification hold without the structure `-a x + bounded`
  (`Flow/FokkerPlanckUniquenessLipschitz`).
* Infrastructure: `continuousWithinAt_integral_of_weakFokkerPlanck` (weak continuity on all
  continuous compactly supported tests), `hasDerivWithinAt_integral_fp_of_continuous` (product
  rule with a merely continuous, compactly supported time derivative of the test function).

## Method (rescaling and time change, no new PDE estimate)

The analytic form of "`Y_τ = e^{a t} X_t` with `τ = (e^{2 a t} - 1)/(2 a)`": for `a > 0` put
`θ_a(τ) = log(1 + 2 a τ)/(2 a)` (`ouClock`), `k_a(τ) = e^{a θ_a(τ)} = √(1 + 2 a τ)` (`ouScale`)
and `μ_τ = (x ↦ k_a(τ) x)_# ρ_{θ_a(τ)}` (`ouCurve`). Differentiating `∫ φ(e^{a t} x) dρ_t`
along the solution (`hasDerivWithinAt_integral_comp_exp_smul`; its time derivative
`a e^{a t} x ⬝ ∇φ(e^{a t} x)` is only `C¹_c`, whence the `C⁰_c` product rule) cancels the linear
part of the drift, and the time change `θ_a' = e^{-2 a θ_a}` restores the diffusion constant `D`
(`weakFokkerPlanck_ouCurve`). The new drift `c(τ, y) = k⁻¹ b₀(θ, k⁻¹ y)` (`ouDrift`) is continuous
and bounded by `B` because `k ≥ 1` (`norm_ouDrift_le`), so `eq_of_weakFokkerPlanck` applies to
`μ`; since `θ_a` maps `[0, ∞)` onto `[0, ∞)` and the scaling is invertible, `ρ` is recovered.

## Not proved here

* **General linear growth or dissipative drifts** (`‖b_t(x)‖ ≤ B (1 + ‖x‖)` or
  `x ⬝ b ≤ C (1 + |x|²)` without the structure `-a x + bounded`), e.g. Langevin with a
  quartic or double-well potential. The total-variation Gronwall argument of
  `Flow/FokkerPlanckUniqueness.lean` does not localise: the main duality term
  `χ_R (b ⬝ ∇Q_σ φ)` is bounded only by `d B (1 + 2R) sup|φ| / σ` on the support of the cutoff,
  so the Gronwall constant (and the admissible time step `δ ~ R⁻²`) degenerates as `R → ∞`;
  the tail errors `ρ_t(‖x‖ ≥ R)` (small by tightness or moments) are not multiplied by the
  discrepancy and cannot absorb the loss. A proof would need different input (e.g. a dual
  Kolmogorov equation for regularised drifts, or density/`Lᵖ` regularity of solutions as in
  Bogachev–Röckner–Shaposhnikov), which is not formalised.
* **Expanding linear part `a < 0`**: the time change then maps `[0, ∞)` onto the bounded
  interval `[0, 1/(2|a|))`, while `eq_of_weakFokkerPlanck` is stated for solutions on all of
  `[0, ∞)`; a finite-horizon version of the bounded-drift theorem is not proved here.
* Non-scalar linear parts `A x` (the rescaled diffusion `e^{tA} e^{tAᵀ}` is not a multiple of
  the identity unless `A` is scalar up to a skew part), time-dependent `a`, matrix-valued or
  degenerate (`D = 0`) diffusions.
* No uniqueness statement for the dissipative existence theorem
  `exists_weakFokkerPlanck_dissipative` beyond drifts of the form above; Euler–Maruyama
  identification only for globally Lipschitz `b` (EM diverges for superlinear drifts); no SDE
  theory, only one-time marginals.
-/

@[expose] public section

open MeasureTheory Matrix Set Filter Topology Metric Asymptotics
open scoped ContDiff

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-! ### Continuity in time for continuous compactly supported tests -/

/-- **Weak continuity on `C_c` tests (Verified).** If `ρ` is a curve of probability measures on
`t ≥ 0` solving `WeakFokkerPlanck ρ b D`, then `r ↦ ∫ f dρ_r` is continuous within `[0, ∞)` at
every `t ≥ 0` for every **continuous compactly supported** `f` (not only for `C²_c` tests):
uniform smooth approximation, uniformly in `r` since all `ρ_r` have mass one. -/
theorem continuousWithinAt_integral_of_weakFokkerPlanck {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {t : ℝ}
    (ht : 0 ≤ t) : ContinuousWithinAt (fun r => ∫ x, f x ∂(ρ r)) (Ici 0) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨φ, hφ, hdist, hsupp⟩ :=
    hf.exists_contDiff_approx (n := ⊤) (ε := fun _ => ε / 4) continuous_const
      fun _ => by positivity
  have hφc : HasCompactSupport φ := hfc.mono hsupp
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hcomp : ∀ r, 0 ≤ r → |∫ x, f x ∂(ρ r) - ∫ x, φ x ∂(ρ r)| ≤ ε / 4 := by
    intro r hr
    have := hprob r hr
    rw [← integral_sub (hf.integrable_of_hasCompactSupport hfc)
      (hφ2.continuous.integrable_of_hasCompactSupport hφc)]
    have hb : ∀ x, |f x - φ x| ≤ ε / 4 := fun x => by
      have := (hdist x).le
      rwa [Real.dist_eq, abs_sub_comm] at this
    simpa using abs_integral_le_of_abs_le (μ := ρ r) hb
  have hc := (hρ φ ⟨hφ2, hφc⟩ t ht).continuousWithinAt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun {r} hr hrt => ?_⟩
  have h1 := hδc hr hrt
  rw [Real.dist_eq] at h1 ⊢
  have h2 := hcomp r hr
  have h3 := hcomp t ht
  calc |∫ x, f x ∂(ρ r) - ∫ x, f x ∂(ρ t)|
      ≤ |∫ x, f x ∂(ρ r) - ∫ x, φ x ∂(ρ r)| + |∫ x, φ x ∂(ρ r) - ∫ x, φ x ∂(ρ t)| +
        |∫ x, f x ∂(ρ t) - ∫ x, φ x ∂(ρ t)| := by
        have := abs_add_three (∫ x, f x ∂(ρ r) - ∫ x, φ x ∂(ρ r))
          (∫ x, φ x ∂(ρ r) - ∫ x, φ x ∂(ρ t)) (-(∫ x, f x ∂(ρ t) - ∫ x, φ x ∂(ρ t)))
        rw [abs_neg] at this
        convert this using 2
        ring
    _ < ε := by linarith

/-- **Product rule along a weak Fokker–Planck solution, `C⁰_c` time derivative (Verified).**
The variant of `hasDerivWithinAt_integral_fp` in which the time derivative `g s` of the test
function is only required to be **continuous with compact support** (instead of `C²_c`): for a
probability solution `ρ` of `WeakFokkerPlanck ρ b D` on `t ≥ 0`, `0 ≤ a`, `ψ s ∈ C²_c` with
`∂ₛψ(s, x) = g s x` within `[a, c]`, `g` jointly continuous and all `g s` vanishing outside one
compact `K`, the map `s ↦ ∫ ψ(s) dρ_s` has derivative
`∫ g(s) dρ_s + ∫ (b_s ⬝ ∇ψ(s) + D Δψ(s)) dρ_s` within `[a, c]` at every `s ∈ [a, c]`. -/
theorem hasDerivWithinAt_integral_fp_of_continuous {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    {a c : ℝ} (ha : 0 ≤ a) {ψ g : ℝ → (Fin d → ℝ) → ℝ}
    (hψ : ∀ s ∈ Icc a c, TestFunction2 (ψ s))
    (hd : ∀ s ∈ Icc a c, ∀ x, HasDerivWithinAt (fun u => ψ u x) (g s x) (Icc a c) s)
    (hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hgK : ∀ s ∈ Icc a c, ∀ x ∉ K, g s x = 0)
    {s : ℝ} (hs : s ∈ Icc a c) :
    HasDerivWithinAt (fun r => ∫ x, ψ r x ∂(ρ r))
      (∫ x, g s x ∂(ρ s) + ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂(ρ s))
      (Icc a c) s := by
  have hgs : ∀ u ∈ Icc a c, Continuous (g u) ∧ HasCompactSupport (g u) := fun u hu =>
    ⟨hgc.comp (continuous_const.prodMk continuous_id),
      HasCompactSupport.intro hK fun x hx => hgK u hu x hx⟩
  have hint : ∀ r, 0 ≤ r → ∀ f : (Fin d → ℝ) → ℝ, Continuous f → HasCompactSupport f →
      Integrable f (ρ r) := by
    intro r hr f hf hfc
    have := hprob r hr
    exact hf.integrable_of_hasCompactSupport hfc
  have hs0 : 0 ≤ s := ha.trans hs.1
  have hsub : Icc a c ⊆ Ici 0 := fun r hr => ha.trans hr.1
  set L := 𝓝[Icc a c] s
  have hmem : ∀ᶠ r in L, r ∈ Icc a c := self_mem_nhdsWithin
  set Lψ : ℝ := ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂(ρ s)
  set E1 : ℝ → ℝ := fun r => ∫ x, (ψ r x - ψ s x - (r - s) * g s x) ∂(ρ r)
  set E2 : ℝ → ℝ := fun r => (r - s) * (∫ x, g s x ∂(ρ r) - ∫ x, g s x ∂(ρ s))
  set E3 : ℝ → ℝ := fun r => ∫ x, ψ s x ∂(ρ r) - ∫ x, ψ s x ∂(ρ s) - (r - s) • Lψ
  have h3 : E3 =o[L] fun r => r - s :=
    hasDerivWithinAt_iff_isLittleO.1 ((hρ (ψ s) (hψ s hs) s hs0).mono hsub)
  have h2 : E2 =o[L] fun r => r - s := by
    have ht : Tendsto (fun r => ∫ x, g s x ∂(ρ r) - ∫ x, g s x ∂(ρ s)) L (𝓝 0) := by
      have hc := (continuousWithinAt_integral_of_weakFokkerPlanck hprob hρ (hgs s hs).1
        (hgs s hs).2 hs0).mono hsub
      simpa using hc.tendsto.sub_const (∫ x, g s x ∂(ρ s))
    have := (isBigO_refl (fun r => r - s) L).mul_isLittleO (isLittleO_one_iff ℝ |>.2 ht)
    simpa using this
  have h1 : E1 =o[L] fun r => r - s := by
    rw [isLittleO_iff]
    intro ε hε
    have huc : UniformContinuousOn (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) (Icc a c ×ˢ K) :=
      (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hgc.continuousOn
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    have hbd : ∀ u ∈ Icc a c ∩ ball s δ, ∀ x, ‖g u x - g s x‖ ≤ ε := by
      intro u hu x
      by_cases hx : x ∈ K
      · have := hδu (u, x) ⟨hu.1, hx⟩ (s, x) ⟨hs, hx⟩ (by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hu.2)
        rw [← dist_eq_norm]; exact this.le
      · rw [hgK u hu.1 x hx, hgK s hs x hx, sub_self, norm_zero]; exact hε.le
    filter_upwards [hmem, inter_mem_nhdsWithin (Icc a c) (ball_mem_nhds s hδ)] with r hr hrb
    have := hprob r (ha.trans hr.1)
    have hpt : ∀ x, ‖ψ r x - ψ s x - (r - s) * g s x‖ ≤ ε * ‖r - s‖ := by
      intro x
      have hcvx : Convex ℝ (Icc a c ∩ ball s δ) := (convex_Icc a c).inter (convex_ball s δ)
      have := hcvx.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun u => ψ u x - u * g s x) (f' := fun u => g u x - g s x)
        (fun u hu => ((((hd u hu.1 x).mono inter_subset_left).sub
          ((hasDerivAt_id u).mul_const (g s x)).hasDerivWithinAt).congr_deriv (by simp)))
        (hbd · · x) ⟨hs, mem_ball_self hδ⟩ hrb
      convert this using 2
      ring
    calc ‖E1 r‖ ≤ ε * ‖r - s‖ * (ρ r).real univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
      _ = ε * ‖r - s‖ := by simp
  have hsum : ∀ᶠ r in L, (∫ x, ψ r x ∂(ρ r)) - (∫ x, ψ s x ∂(ρ s)) -
      (r - s) • (∫ x, g s x ∂(ρ s) + Lψ) = E1 r + E2 r + E3 r := by
    filter_upwards [hmem] with r hr
    have hr0 : 0 ≤ r := ha.trans hr.1
    have hE1 : E1 r = ∫ x, ψ r x ∂(ρ r) - ∫ x, ψ s x ∂(ρ r) - (r - s) * ∫ x, g s x ∂(ρ r) := by
      have i1 := hint r hr0 _ (hψ r hr).1.continuous (hψ r hr).2
      have i2 := hint r hr0 _ (hψ s hs).1.continuous (hψ s hs).2
      have i3 := (hint r hr0 _ (hgs s hs).1 (hgs s hs).2).const_mul (r - s)
      have i12 : Integrable (fun x => ψ r x - ψ s x) (ρ r) := i1.sub i2
      simp only [E1]
      rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul]
    simp only [E2, E3, hE1, smul_eq_mul]
    ring
  have := ((h1.add h2).add h3).congr' (hsum.mono fun r hr => hr.symm) EventuallyEq.rfl
  exact hasDerivWithinAt_iff_isLittleO.2 this

/-! ### The Ornstein–Uhlenbeck clock and scaling -/

/-- The **OU clock** `θ_a(τ) = log(1 + 2 a τ) / (2 a)`: the inverse of the time change
`t ↦ τ = (e^{2 a t} - 1) / (2 a)` that turns the diffusion `√(2D) e^{a t} dW` of `e^{a t} X_t`
back into `√(2D) dW` (for `a > 0`). -/
noncomputable def ouClock (a τ : ℝ) : ℝ := Real.log (1 + 2 * a * τ) / (2 * a)

/-- The **OU scaling factor** `k_a(τ) = e^{a θ_a(τ)}` (`= √(1 + 2 a τ)` for `τ ≥ 0`, `a > 0`). -/
noncomputable def ouScale (a τ : ℝ) : ℝ := Real.exp (a * ouClock a τ)

/-- The **rescaled drift**: `c(τ, y) = k⁻¹ (b(θ, k⁻¹ y) + a k⁻¹ y)` with `θ = θ_a(τ)`,
`k = k_a(τ)`. For `b(t, x) = -a x + b₀(t, x)` it is `k⁻¹ b₀(θ, k⁻¹ y)`, bounded when `b₀` is. -/
noncomputable def ouDrift (a : ℝ) (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (τ : ℝ)
    (y : Fin d → ℝ) : Fin d → ℝ :=
  (ouScale a τ)⁻¹ • (b (ouClock a τ) ((ouScale a τ)⁻¹ • y) + a • ((ouScale a τ)⁻¹ • y))

/-- The **rescaled curve** `μ_τ = (x ↦ k_a(τ) x)_# ρ_{θ_a(τ)}` (the law of `e^{a t} X_t` at
`t = θ_a(τ)`). -/
noncomputable def ouCurve (a : ℝ) (ρ : ℝ → Measure (Fin d → ℝ)) (τ : ℝ) :
    Measure (Fin d → ℝ) :=
  (ρ (ouClock a τ)).map (fun x => ouScale a τ • x)

/-- `θ_a(τ) ≥ 0` for `a > 0`, `τ ≥ 0`. -/
theorem ouClock_nonneg {a τ : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) : 0 ≤ ouClock a τ :=
  div_nonneg (Real.log_nonneg (by nlinarith)) (by positivity)

/-- `θ_a(0) = 0`. -/
theorem ouClock_zero (a : ℝ) : ouClock a 0 = 0 := by simp [ouClock]

/-- `e^{2 a θ_a(τ)} = 1 + 2 a τ` for `a > 0`, `τ ≥ 0`. -/
theorem exp_two_mul_ouClock {a τ : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) :
    Real.exp (2 * a * ouClock a τ) = 1 + 2 * a * τ := by
  have h : 2 * a * ouClock a τ = Real.log (1 + 2 * a * τ) := by
    unfold ouClock; field_simp
  rw [h, Real.exp_log (by nlinarith)]

/-- `k_a(τ)² = 1 + 2 a τ` for `a > 0`, `τ ≥ 0`. -/
theorem ouScale_sq {a τ : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) : ouScale a τ ^ 2 = 1 + 2 * a * τ := by
  rw [ouScale, ← Real.exp_nat_mul, ← exp_two_mul_ouClock ha hτ]
  push_cast; ring_nf

/-- `k_a(τ) > 0`. -/
theorem ouScale_pos (a τ : ℝ) : 0 < ouScale a τ := Real.exp_pos _

/-- `k_a(τ) ≥ 1` for `a > 0`, `τ ≥ 0`. -/
theorem one_le_ouScale {a τ : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) : 1 ≤ ouScale a τ :=
  Real.one_le_exp (mul_nonneg ha.le (ouClock_nonneg ha hτ))

/-- `θ_a` inverts the time change: `θ_a((e^{2 a t} - 1)/(2 a)) = t` for `a > 0`. -/
theorem ouClock_inv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ouClock a ((Real.exp (2 * a * t) - 1) / (2 * a)) = t := by
  have h : 1 + 2 * a * ((Real.exp (2 * a * t) - 1) / (2 * a)) = Real.exp (2 * a * t) := by
    field_simp; ring
  rw [ouClock, h, Real.log_exp]
  field_simp

/-- `θ_a` has derivative `1 / (1 + 2 a τ)` at `τ ≥ 0` (`a > 0`). -/
theorem hasDerivAt_ouClock {a τ : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) :
    HasDerivAt (ouClock a) (1 + 2 * a * τ)⁻¹ τ := by
  have hpos : 0 < 1 + 2 * a * τ := by nlinarith
  have h1 : HasDerivAt (fun s => 1 + 2 * a * s) (2 * a) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (2 * a)).const_add 1
  have h2 := (h1.log hpos.ne').div_const (2 * a)
  convert h2 using 1
  · rfl
  · field_simp

/-- `μ_0 = ρ_0` for the rescaled curve. -/
theorem ouCurve_zero (a : ℝ) (ρ : ℝ → Measure (Fin d → ℝ)) : ouCurve a ρ 0 = ρ 0 := by
  simp [ouCurve, ouScale, ouClock_zero]

/-- Undoing the scaling: `(x ↦ c⁻¹ x)_# (x ↦ c x)_# μ = μ` for `c ≠ 0`. -/
theorem map_inv_smul_map_smul (μ : Measure (Fin d → ℝ)) {c : ℝ} (hc : c ≠ 0) :
    (μ.map (fun x => c • x)).map (fun y => c⁻¹ • y) = μ := by
  rw [Measure.map_map (continuous_const_smul _).measurable (continuous_const_smul _).measurable]
  have : ((fun y : Fin d → ℝ => c⁻¹ • y) ∘ fun x => c • x) = id :=
    funext fun x => by simp [inv_smul_smul₀ hc]
  rw [this, Measure.map_id]

/-- `y ↦ c(τ, y)` is continuous for `a > 0`, `τ ≥ 0` if every `b t` (`t ≥ 0`) is. -/
theorem continuous_ouDrift {a : ℝ} {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} (ha : 0 < a)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t)) {τ : ℝ} (hτ : 0 ≤ τ) :
    Continuous (ouDrift a b τ) := by
  have := hbc _ (ouClock_nonneg ha hτ)
  unfold ouDrift
  fun_prop

/-- `c(τ, k y) = k⁻¹ (b(θ, y) + a y)` with `k = k_a(τ)`, `θ = θ_a(τ)`. -/
theorem ouDrift_smul (a : ℝ) (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (τ : ℝ) (x : Fin d → ℝ) :
    ouDrift a b τ (ouScale a τ • x) =
      (ouScale a τ)⁻¹ • (b (ouClock a τ) x + a • x) := by
  simp [ouDrift, inv_smul_smul₀ (ouScale_pos a τ).ne']

/-- `‖c(τ, y)‖ ≤ B` whenever `‖b(t, x) + a x‖ ≤ B` for `t ≥ 0` (`a > 0`, `τ ≥ 0`). -/
theorem norm_ouDrift_le {a B : ℝ} {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} (ha : 0 < a)
    (hB : ∀ t, 0 ≤ t → ∀ x, ‖b t x + a • x‖ ≤ B) {τ : ℝ} (hτ : 0 ≤ τ) (y : Fin d → ℝ) :
    ‖ouDrift a b τ y‖ ≤ B := by
  have hk := one_le_ouScale ha hτ
  have hb := hB _ (ouClock_nonneg ha hτ) ((ouScale a τ)⁻¹ • y)
  rw [ouDrift, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (ouScale_pos a τ))]
  calc (ouScale a τ)⁻¹ * _ ≤ 1 * B :=
        mul_le_mul (inv_le_one_of_one_le₀ hk) hb (norm_nonneg _) zero_le_one
    _ = B := one_mul B

/-! ### The rescaled curve solves a Fokker–Planck equation with bounded drift -/

/-- A continuous function vanishing outside a closed ball is integrable for a finite measure. -/
theorem integrable_of_continuous_of_eq_zero {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ]
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {R : ℝ}
    (h : ∀ x ∉ closedBall (0 : Fin d → ℝ) R, f x = 0) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall 0 R) h)

/-- **Moving test functions `φ(e^{a t} x)` (Verified).** Let `ρ` be a probability solution of
`WeakFokkerPlanck ρ b D` on `t ≥ 0` with every `b t` (`t ≥ 0`) continuous, `a ≥ 0` and
`φ ∈ C²_c`. Then `G(t) = ∫ φ(e^{a t} x) dρ_t` has derivative within `[0, ∞)` at `t ≥ 0`
`∫ (e^{a t} (b_t(x) + a x) ⬝ ∇φ(e^{a t} x) + D e^{2 a t} Δφ(e^{a t} x)) dρ_t`. -/
theorem hasDerivWithinAt_integral_comp_exp_smul {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {a D : ℝ} (ha : 0 ≤ a)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t))
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    {φ : (Fin d → ℝ) → ℝ} (hφ : TestFunction2 φ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => ∫ x, φ (Real.exp (a * r) • x) ∂(ρ r))
      (∫ x, (Real.exp (a * t) * ((b t x + a • x) ⬝ᵥ grad φ (Real.exp (a * t) • x)) +
        D * (Real.exp (a * t) ^ 2 * laplacian φ (Real.exp (a * t) • x))) ∂(ρ t)) (Ici 0) t := by
  have hφ2 := hφ.1
  have hφd : Differentiable ℝ φ := hφ2.differentiable two_ne_zero
  set e : ℝ → ℝ := fun r => Real.exp (a * r) with he
  have he1 : ∀ r, 0 ≤ r → 1 ≤ e r := fun r hr => Real.one_le_exp (mul_nonneg ha hr)
  -- a ball containing the supports of `φ` and `Δφ`
  obtain ⟨R₁, hR₁⟩ := hφ.2.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  obtain ⟨R₂, hR₂⟩ := (hasCompactSupport_laplacian hφ.2).isCompact.isBounded.subset_closedBall
    (0 : Fin d → ℝ)
  set R : ℝ := max R₁ R₂ with hR
  have hout : ∀ r, 0 ≤ r → ∀ x ∉ closedBall (0 : Fin d → ℝ) R,
      grad φ (e r • x) = 0 ∧ laplacian φ (e r • x) = 0 := by
    intro r hr x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    have hn : R < ‖e r • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      nlinarith [he1 r hr, norm_nonneg x]
    refine ⟨ContinuityEquation.grad_eq_zero_of_notMem_tsupport fun h => ?_,
      image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    · have := hR₁ h
      rw [mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R₁ R₂]
    · have := hR₂ h
      rw [mem_closedBall, dist_zero_right] at this
      linarith [le_max_right R₁ R₂]
  set ψ : ℝ → (Fin d → ℝ) → ℝ := fun r x => φ (e r • x) with hψ
  set g : ℝ → (Fin d → ℝ) → ℝ := fun r x => a * e r * (x ⬝ᵥ grad φ (e r • x)) with hg
  have hψT : ∀ r, TestFunction2 (ψ r) := fun r =>
    ⟨hφ2.comp (contDiff_id.const_smul (e r)), hφ.2.comp_smul (Real.exp_pos _).ne'⟩
  have hd : ∀ s ∈ Icc 0 (t + 1), ∀ x,
      HasDerivWithinAt (fun u => ψ u x) (g s x) (Icc 0 (t + 1)) s := by
    intro s _ x
    have h1 : HasDerivAt (fun u => e u • x) ((Real.exp (a * s) * (a * 1)) • x) s :=
      ((Real.hasDerivAt_exp _).comp s ((hasDerivAt_id s).const_mul a)).smul_const x
    have h2 := (hφd (e s • x)).hasFDerivAt.comp_hasDerivAt s h1
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    rw [map_smul, fderiv_apply_eq_grad_dotProduct, smul_eq_mul,
      dotProduct_comm]
    simp only [g, e]
    ring
  have hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) := by
    have hG := continuous_grad hφ2
    have hE : Continuous (fun q : ℝ × (Fin d → ℝ) => e q.1) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_fst)
    exact (continuous_const.mul hE).mul
      (continuous_snd.dotProduct (hG.comp (hE.smul continuous_snd)))
  have hgK : ∀ s ∈ Icc 0 (t + 1), ∀ x ∉ closedBall (0 : Fin d → ℝ) R, g s x = 0 :=
    fun s hs x hx => by simp [g, (hout s hs.1 x hx).1]
  have hmain := hasDerivWithinAt_integral_fp_of_continuous hprob hρ le_rfl
    (fun s _ => hψT s) hd hgc (isCompact_closedBall 0 R) hgK ⟨ht, by linarith⟩
  have hnhds : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  refine (hmain.mono_of_mem_nhdsWithin hnhds).congr_deriv ?_
  -- identify the derivative
  have := hprob t ht
  have hgrad : ∀ x, grad (ψ t) x = e t • grad φ (e t • x) := fun x => grad_comp_smul hφd _ x
  have hlap : ∀ x, laplacian (ψ t) x = e t ^ 2 * laplacian φ (e t • x) := fun x =>
    laplacian_comp_smul hφ2 _ x
  have hL : (fun x => b t x ⬝ᵥ grad (ψ t) x + D * laplacian (ψ t) x) =
      fun x => e t * (b t x ⬝ᵥ grad φ (e t • x)) + D * (e t ^ 2 * laplacian φ (e t • x)) :=
    funext fun x => by rw [hgrad, hlap, dotProduct_smul, smul_eq_mul]
  have hE : Continuous (fun x : Fin d → ℝ => e t • x) := continuous_const_smul _
  have hcL : Continuous (fun x => e t * (b t x ⬝ᵥ grad φ (e t • x)) +
      D * (e t ^ 2 * laplacian φ (e t • x))) :=
    (continuous_const.mul ((hbc t ht).dotProduct ((continuous_grad hφ2).comp hE))).add
      (continuous_const.mul (continuous_const.mul ((continuous_laplacian hφ2).comp hE)))
  have hI1 : Integrable (g t) (ρ t) := integrable_of_continuous_of_eq_zero
    (hgc.comp (continuous_const.prodMk continuous_id)) (hgK t ⟨ht, by linarith⟩)
  have hI2 : Integrable (fun x => e t * (b t x ⬝ᵥ grad φ (e t • x)) +
      D * (e t ^ 2 * laplacian φ (e t • x))) (ρ t) :=
    integrable_of_continuous_of_eq_zero (R := R) hcL fun x hx => by
      simp [(hout t ht x hx).1, (hout t ht x hx).2]
  rw [hL, ← integral_add hI1 hI2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [g, add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

/-- **The rescaled curve solves a Fokker–Planck equation (Verified).** Let `a > 0`, `ρ` a
probability solution of `WeakFokkerPlanck ρ b D` on `t ≥ 0` with every `b t` (`t ≥ 0`)
continuous. Then `μ_τ = (x ↦ k_a(τ) x)_# ρ_{θ_a(τ)}` (`ouCurve`) solves
`WeakFokkerPlanck μ (ouDrift a b) D` on `τ ≥ 0`, with the **same** diffusion constant `D`
and drift `c(τ, y) = k⁻¹ (b(θ, k⁻¹ y) + a k⁻¹ y)`. (Analytic form of "`Y_τ = e^{a t} X_t`,
`τ = (e^{2 a t} - 1)/(2 a)`": the linear part `-a x` of `b` is removed.) -/
theorem weakFokkerPlanck_ouCurve {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {a D : ℝ} (ha : 0 < a)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t))
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D) :
    WeakFokkerPlanck (ouCurve a ρ) (ouDrift a b) D := by
  intro φ hφ τ hτ
  set t := ouClock a τ with htdef
  have ht : 0 ≤ t := ouClock_nonneg ha hτ
  have hG := hasDerivWithinAt_integral_comp_exp_smul ha.le hbc hprob hρ hφ ht
  have hθ : HasDerivWithinAt (ouClock a) (1 + 2 * a * τ)⁻¹ (Ici 0) τ :=
    (hasDerivAt_ouClock ha hτ).hasDerivWithinAt
  have hcomp := hG.scomp τ hθ fun s hs => ouClock_nonneg ha hs
  have hE : ∀ s, Continuous (fun x : Fin d → ℝ => ouScale a s • x) :=
    fun s => continuous_const_smul _
  have hfun : (fun s => ∫ x, φ x ∂(ouCurve a ρ s)) =
      (fun r => ∫ x, φ (Real.exp (a * r) • x) ∂(ρ r)) ∘ ouClock a := by
    funext s
    simp only [ouCurve, Function.comp]
    rw [integral_map (hE s).aemeasurable hφ.1.continuous.aestronglyMeasurable]
    rfl
  rw [hfun]
  refine hcomp.congr_deriv ?_
  -- identify the derivative
  set k := ouScale a τ with hk
  have hk0 : 0 < k := ouScale_pos a τ
  have hk2 : k ^ 2 = 1 + 2 * a * τ := ouScale_sq ha hτ
  have hcont : Continuous (fun y => ouDrift a b τ y ⬝ᵥ grad φ y + D * laplacian φ y) :=
    ((continuous_ouDrift ha hbc hτ).dotProduct (continuous_grad hφ.1)).add
      (continuous_const.mul (continuous_laplacian hφ.1))
  simp only [ouCurve]
  rw [integral_map (hE τ).aemeasurable hcont.aestronglyMeasurable, smul_eq_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hek : Real.exp (a * t) = k := rfl
  simp only [hek, ouDrift_smul, smul_dotProduct, smul_eq_mul]
  rw [← hk, ← htdef, ← hk2]
  field_simp

/-! ### Uniqueness for linear-plus-bounded drifts -/

/-- **Uniqueness for drifts `-a x + (bounded continuous)` (Verified).** Let `D > 0`, `a ≥ 0`
and let the (time-dependent) drift `b` be continuous in `x` for `t ≥ 0` with
`‖b_t(x) + a x‖ ≤ B` (no Lipschitz condition, no regularity in `t`): `b_t(x) = -a x + b₀(t, x)`
with `b₀` bounded, so `b` has **linear growth and is unbounded** for `a > 0`. If `ρ, ρ'` are
curves of probability measures on `t ≥ 0` (no moment assumption) solving
`WeakFokkerPlanck · b D` with `ρ 0 = ρ' 0`, then `ρ t = ρ' t` for all `t ≥ 0`.

Proof: for `a > 0`, the rescaled curves `ouCurve a ρ`, `ouCurve a ρ'` solve the Fokker–Planck
equation with the **bounded** continuous drift `ouDrift a b` (`weakFokkerPlanck_ouCurve`,
`norm_ouDrift_le`) and the same initial law, so they agree by `eq_of_weakFokkerPlanck`; the
time change `θ_a` is onto `[0, ∞)` (`ouClock_inv`) and the scaling is invertible. -/
theorem eq_of_weakFokkerPlanck_linear_add_bounded {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {a B D : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t)) (hB : ∀ t, 0 ≤ t → ∀ x, ‖b t x + a • x‖ ≤ B)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D) (h0 : ρ 0 = ρ' 0) :
    ∀ t, 0 ≤ t → ρ t = ρ' t := by
  rcases ha.eq_or_lt with rfl | ha
  · exact eq_of_weakFokkerPlanck hD hbc (fun t ht x => by simpa using hB t ht x) hprob hprob'
      hρ hρ' h0
  have hpμ : ∀ ν : ℝ → Measure (Fin d → ℝ), (∀ t, 0 ≤ t → IsProbabilityMeasure (ν t)) →
      ∀ τ, 0 ≤ τ → IsProbabilityMeasure (ouCurve a ν τ) := fun ν hν τ hτ => by
    have := hν _ (ouClock_nonneg ha hτ)
    unfold ouCurve; infer_instance
  have heq := eq_of_weakFokkerPlanck hD (fun τ hτ => continuous_ouDrift ha hbc hτ)
    (fun τ hτ => norm_ouDrift_le ha hB hτ) (hpμ ρ hprob) (hpμ ρ' hprob')
    (weakFokkerPlanck_ouCurve ha hbc hprob hρ) (weakFokkerPlanck_ouCurve ha hbc hprob' hρ')
    (by rw [ouCurve_zero, ouCurve_zero, h0])
  intro t ht
  set τ : ℝ := (Real.exp (2 * a * t) - 1) / (2 * a) with hτdef
  have hτ : 0 ≤ τ :=
    div_nonneg (by linarith [Real.one_le_exp (by positivity : 0 ≤ 2 * a * t)]) (by positivity)
  have hθ : ouClock a τ = t := ouClock_inv ha t
  have h := congrArg (fun μ => μ.map (fun y => (ouScale a τ)⁻¹ • y)) (heq τ hτ)
  simp only [ouCurve, map_inv_smul_map_smul _ (ouScale_pos a τ).ne', hθ] at h
  exact h

/-! ### Well-posedness for locally Lipschitz drifts -/

/-- `x ⬝ b x ≤ B (d + 1) (1 + x ⬝ x)` if `‖b x + a x‖ ≤ B` and `a ≥ 0`: linear-plus-bounded
drifts are dissipative in the sense of `exists_weakFokkerPlanck_dissipative`. -/
theorem dotProduct_le_of_linear_add_bounded {b : (Fin d → ℝ) → Fin d → ℝ} {a B : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, ‖b x + a • x‖ ≤ B) (x : Fin d → ℝ) :
    x ⬝ᵥ b x ≤ B * (d + 1) * (1 + x ⬝ᵥ x) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set v := b x + a • x with hv
  have hxx : 0 ≤ x ⬝ᵥ x := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hbx : x ⬝ᵥ b x = x ⬝ᵥ v - a * (x ⬝ᵥ x) := by
    simp [hv, dotProduct_add, dotProduct_smul]
  have hxv : x ⬝ᵥ v ≤ B * d + B * (x ⬝ᵥ x) := by
    have hvi : ∀ i, |v i| ≤ B := fun i =>
      (Real.norm_eq_abs _ ▸ norm_le_pi_norm v i).trans (hB x)
    calc x ⬝ᵥ v = ∑ i, x i * v i := rfl
      _ ≤ ∑ i, B * (1 + x i * x i) := Finset.sum_le_sum fun i _ => by
          have h1 : x i * v i ≤ |x i| * B := by
            calc x i * v i ≤ |x i * v i| := le_abs_self _
              _ = |x i| * |v i| := abs_mul _ _
              _ ≤ |x i| * B := mul_le_mul_of_nonneg_left (hvi i) (abs_nonneg _)
          have h2 : |x i| ≤ 1 + x i * x i := by
            rcases abs_cases (x i) with ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith
          nlinarith [abs_nonneg (x i)]
      _ = B * d + B * (x ⬝ᵥ x) := by
          rw [Finset.sum_congr rfl fun i _ => mul_add B 1 (x i * x i), Finset.sum_add_distrib]
          simp [dotProduct, Finset.mul_sum]
          ring
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [hbx]
  nlinarith [mul_nonneg ha hxx, mul_nonneg hB0 hxx, mul_nonneg (mul_nonneg hB0 hd0) hxx]

/-- **Well-posedness, locally Lipschitz linear-plus-bounded drifts (Verified).** For an
autonomous **locally** Lipschitz drift `b` with `‖b x + a x‖ ≤ B` (`a ≥ 0`), `D > 0` and any
probability measure `ρ₀`, there is a probability solution of `WeakFokkerPlanck ρ (fun _ => b) D`
with `ρ 0 = ρ₀` (`exists_weakFokkerPlanck_dissipative`, via
`dotProduct_le_of_linear_add_bounded`), and every probability solution on `t ≥ 0` with the same
initial law coincides with it on `t ≥ 0`. -/
theorem existsUnique_weakFokkerPlanck_locallyLipschitz_linear_add_bounded
    {b : (Fin d → ℝ) → Fin d → ℝ} (hb : LocallyLipschitz b) {a B : ℝ} (ha : 0 ≤ a)
    (hB : ∀ x, ‖b x + a • x‖ ≤ B) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => b) D ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) → WeakFokkerPlanck ρ' (fun _ => b) D →
          ∀ t, 0 ≤ t → ρ' t = ρ t := by
  obtain ⟨ν, h0, -, hfp⟩ := exists_weakFokkerPlanck_dissipative hb
    (dotProduct_le_of_linear_add_bounded ha hB) hD ρ₀
  refine ⟨fun t => ν t, h0, fun t => inferInstance, hfp, fun ρ' h0' hprob' hfp' => ?_⟩
  exact eq_of_weakFokkerPlanck_linear_add_bounded ha hD (fun _ _ => hb.continuous)
    (fun _ _ => hB) hprob' (fun t _ => inferInstance) hfp' hfp (h0'.trans h0.symm)

end FormalizeSampling.FokkerPlanckUniqueness
