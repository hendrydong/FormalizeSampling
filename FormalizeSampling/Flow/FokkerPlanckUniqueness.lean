module

public import FormalizeSampling.Flow.FokkerPlanckUniquenessDual
public import FormalizeSampling.Flow.FokkerPlanckUniquenessHeat
public import FormalizeSampling.Flow.FokkerPlanckUniquenessGauss
public import FormalizeSampling.Flow.FokkerPlanckUniquenessCutoff

/-!
# Uniqueness and well-posedness for the weak Fokker–Planck equation (`D > 0`)

Status: **Verified.** Discharges the uniqueness half of the named Itô input
`NoiseScore.WeakFokkerPlanck` for nondegenerate diffusion:

* `eq_of_weakFokkerPlanck`: for `D > 0` and a (time-dependent) drift `b_t` that is
  **continuous and bounded** in `x` for `t ≥ 0` (`‖b_t(x)‖ ≤ B`; no Lipschitz condition and no
  regularity in `t`), two curves of probability measures on `t ≥ 0` solving
  `WeakFokkerPlanck · b D` with the same initial law agree for all `t ≥ 0`.
* `eq_of_weakFokkerPlanck_autonomous`: the autonomous special case.

Well-posedness and the identification of solutions with the limit of the dyadic Euler–Maruyama
laws, for globally Lipschitz drifts, are in `Flow/FokkerPlanckUniquenessLipschitz`.

## Method (duality with the heat semigroup, Gronwall in total variation)

Instead of the backward Euler–Maruyama operator suggested by the continuity-equation proof,
the diffusion is used to smooth: with `Q_σ φ(x) = E φ(x + σ Z)` (`heatOp`) and a cutoff `χ`
(`exists_cutoff`), the test function `ψ(s) = χ · Q_{√(2D(t-s))} φ` solves the backward heat
equation exactly, so that along a solution (`hasDerivWithinAt_integral_fp`)

  `d/ds ∫ ψ(s) dρ_s = ∫ χ (b_s ⬝ ∇Q φ) dρ_s + (cutoff terms, ≤ ε')`.

The Gaussian smoothing estimate `|∂ᵢ Q_σ φ| ≤ sup|φ| / σ` (Stein identity,
`abs_integral_partialDeriv_comp_le`) bounds the first integrand by
`d B sup|φ| / √(2D(t - s))`, which is integrable in `s`. For the difference of two solutions
with `ρ_{t₀} = ρ'_{t₀}` and `|∫ g d(ρ_s - ρ'_s)| ≤ M sup|g|` for continuous compactly supported
`g` (`TVBound`) this gives `|∫ φ d(ρ_t - ρ'_t)| ≤ M sup|φ| (2 d B / √(2D)) √(t - t₀)`
(`abs_integral_sub_le_of_tvBound`, by the mean value inequality against the boundary function
`√(t - t₀) - √(t - s)`), first for smooth `φ` and then for all continuous compactly supported
`φ` (`abs_integral_sub_le_of_smooth`). On an interval of length `δ` with
`(2 d B / √(2D)) √δ ≤ 1/2` the bound halves at every iteration (`tvBound_half`), so the two
solutions agree there (`eq_on_Icc_of_eq`); induction over intervals gives all `t ≥ 0`.
No regularity of the dual problem beyond that of the heat semigroup is needed, which is why
neither Lipschitz continuity nor smoothness of `b` enters.

Infrastructure: `Flow/FokkerPlanckUniquenessDual` (product rule along a solution),
`Flow/FokkerPlanckUniquenessHeat` (`heatOp`: `C²` regularity, commuting with `∂ᵢ` and `Δ`),
`Flow/FokkerPlanckUniquenessGauss` (smoothing estimate, heat equation in `τ`),
`Flow/FokkerPlanckUniquenessCutoff` (product rules, cutoffs, smooth approximation).

## Not proved here (in this file)

* Degenerate diffusion `D = 0` is not covered here (see `Flow/ContinuityUniqueness*` for the
  continuity equation); nor are non-constant or matrix-valued diffusions, or
  `PreconditionedWeakFokkerPlanck`.
* Drifts that are unbounded (e.g. linear growth, such as the OU drift `-a x`) or discontinuous
  in `x`; here the bound `‖b_t(x)‖ ≤ B` is used in an essential way (total-variation Gronwall).
  Drifts `-a x + b₀` with `b₀` continuous and bounded are covered by
  `eq_of_weakFokkerPlanck_linear_add_bounded` (`Flow/FokkerPlanckUniquenessUnbounded`).
* Existence is not used here. It is in `Flow/FokkerPlanckExistenceLinear` (globally
  Lipschitz), `Flow/FokkerPlanckExistenceTime` (time-dependent, linear growth),
  `Flow/FokkerPlanckExistenceDissipative` (dissipative, locally Lipschitz) and
  `Flow/FokkerPlanckExistenceContinuousTime` (continuous in time); well-posedness combining
  existence with uniqueness is in `Flow/FokkerPlanckUniquenessUnbounded` and
  `Flow/FokkerPlanckUniquenessLipschitz`.
* No rate of convergence for the Euler–Maruyama scheme, no SDE / Itô theory, and only
  one-time marginals (no path laws).
-/

@[expose] public section

open MeasureTheory Matrix Set Filter Topology Metric
open scoped ContDiff

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-! ### Auxiliary facts -/

/-- Partial derivatives of smooth functions are smooth. -/
theorem contDiff_partialDeriv_top {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin d) :
    ContDiff ℝ ∞ (partialDeriv i φ) :=
  (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The Laplacian of a smooth function is smooth. -/
theorem contDiff_laplacian_top {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (laplacian φ) := by
  show ContDiff ℝ ∞ (fun x => ∑ i, partialDeriv i (partialDeriv i φ) x)
  exact ContDiff.sum fun i _ => contDiff_partialDeriv_top (contDiff_partialDeriv_top hφ i) i

/-- `|v ⬝ w| ≤ d A A'` if all coordinates satisfy `|vᵢ| ≤ A`, `|wᵢ| ≤ A'`. -/
theorem abs_dotProduct_le {v w : Fin d → ℝ} {A A' : ℝ} (hv : ∀ i, |v i| ≤ A)
    (hw : ∀ i, |w i| ≤ A') : |v ⬝ᵥ w| ≤ d * (A * A') := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |v i * w i| ≤ ∑ _i : Fin d, A * A' := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hv i) (hw i) (abs_nonneg _) ((abs_nonneg _).trans (hv i))
    _ = d * (A * A') := by simp

/-- `heatOp 0 f = f`. -/
theorem heatOp_zero (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : heatOp 0 f x = f x := by
  simp [heatOp]

/-- **Bounded-test discrepancy.** `TVBound μ ν M` says `|∫ g dμ - ∫ g dν| ≤ M C` for every
continuous compactly supported `g` with `|g| ≤ C` (so `M/2` bounds the total variation
distance on such tests). -/
def TVBound (μ ν : Measure (Fin d → ℝ)) (M : ℝ) : Prop :=
  ∀ g : (Fin d → ℝ) → ℝ, Continuous g → HasCompactSupport g → ∀ C : ℝ, (∀ x, |g x| ≤ C) →
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ M * C

/-- Two probability measures satisfy `TVBound μ ν 2`. -/
theorem tvBound_two (μ ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : TVBound μ ν 2 := fun g _ _ C hC => by
  have h1 := abs_integral_le_of_abs_le (μ := μ) hC
  have h2 := abs_integral_le_of_abs_le (μ := ν) hC
  calc _ ≤ |∫ x, g x ∂μ| + |∫ x, g x ∂ν| := abs_sub _ _
    _ ≤ 2 * C := by linarith


/-! ### The one-interval estimate -/

/-- **Key estimate (Verified).** Let `ρ, ρ'` be probability solutions of
`WeakFokkerPlanck · b D` on `t ≥ 0` with `D > 0`, `b_s` continuous and `‖b_s‖ ≤ B` for
`s ≥ 0`. Suppose `ρ_{t₀} = ρ'_{t₀}` and `TVBound (ρ s) (ρ' s) M` for `s ∈ [t₀, t)`. Then for
every smooth compactly supported `φ` with `|φ| ≤ C`,
`|∫ φ dρ_t - ∫ φ dρ'_t| ≤ M C (2 d B / √(2D)) √(t - t₀)`.

Proof: duality with `ψ(s) = χ · Q_{√(2D(t-s))} φ` (Gaussian smoothing `Q = heatOp`, cutoff `χ`):
`∂ₛψ + b ⬝ ∇ψ + D Δψ = χ (b ⬝ ∇Q φ) + (cutoff terms)`, the first bounded by
`d B C / √(2D(t-s))` (Gaussian smoothing), the cutoff terms by an arbitrary `ε'`; then the
mean value inequality against the boundary function `√(t - t₀) - √(t - s)`. -/
theorem abs_integral_sub_le_of_tvBound {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D B : ℝ} (hD : 0 < D) (hB0 : 0 ≤ B)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t)) (hB : ∀ t, 0 ≤ t → ∀ x, ‖b t x‖ ≤ B)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D)
    {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (heq : ρ t₀ = ρ' t₀) {M : ℝ}
    (hTV : ∀ s ∈ Ico t₀ t, TVBound (ρ s) (ρ' s) M)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) :
    |∫ x, φ x ∂(ρ t) - ∫ x, φ x ∂(ρ' t)| ≤
      M * C * (2 * d * B / Real.sqrt (2 * D)) * Real.sqrt (t - t₀) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hΔ2 : ContDiff ℝ 2 (laplacian φ) := (contDiff_laplacian_top hφ).of_le (by simp)
  have hΔc : HasCompactSupport (laplacian φ) := hasCompactSupport_laplacian hφc
  obtain ⟨MΔ, hMΔ⟩ := hΔ2.continuous.bounded_above_of_compact_support hΔc
  obtain ⟨G₁, hG₁⟩ := (hφ2.continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have hG₁0 : 0 ≤ G₁ := (norm_nonneg _).trans (hG₁ 0)
  have hpd : ∀ i y, |partialDeriv i φ y| ≤ G₁ := fun i y => by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc _ ≤ G₁ * 1 := mul_le_mul (hG₁ y) (by simp [Pi.norm_single]) (norm_nonneg _) hG₁0
      _ = G₁ := mul_one _
  set K₀ : ℝ := 2 * d * B / Real.sqrt (2 * D) with hK₀
  set A : ℝ := C * d * B + 2 * D * d * G₁ + D * C with hA
  have hA0 : 0 ≤ A := by positivity
  have htt : 0 ≤ t - t₀ := sub_nonneg.2 ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hden : 0 < 2 * A * (t - t₀) + 1 := by positivity
  set ε' : ℝ := ε / (2 * A * (t - t₀) + 1) with hε'
  have hε'0 : 0 < ε' := div_pos hε hden
  obtain ⟨χ, hχ, hχc, hχI, hχ1, hχg, hχl⟩ := exists_cutoff hφc hε'0
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have hχ0 : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hχI x).1], (hχI x).2⟩
  have hχK : ∀ x ∉ tsupport χ, χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  set σ : ℝ → ℝ := fun s => Real.sqrt (2 * D * (t - s)) with hσ
  set u : ℝ → (Fin d → ℝ) → ℝ := fun s => heatOp (σ s) φ with hu
  set ψ : ℝ → (Fin d → ℝ) → ℝ := fun s x => χ x * u s x with hψ
  set g : ℝ → (Fin d → ℝ) → ℝ := fun s x => -(D * (χ x * heatOp (σ s) (laplacian φ) x))
    with hg
  have hu2 : ∀ s, ContDiff ℝ 2 (u s) := fun s => contDiff_heatOp_two hφ2 hφc (σ s)
  have hψT : ∀ s, TestFunction2 (ψ s) := fun s =>
    ⟨hχ2.mul (hu2 s), HasCompactSupport.intro hχc fun x hx => by simp [ψ, hχK x hx]⟩
  have hgT : ∀ s, TestFunction2 (g s) := fun s =>
    ⟨(contDiff_const.mul (hχ2.mul (contDiff_heatOp_two hΔ2 hΔc (σ s)))).neg,
      HasCompactSupport.intro hχc fun x hx => by simp [g, hχK x hx]⟩
  have hgK : ∀ s ∈ Icc t₀ t, ∀ x ∉ tsupport χ, g s x = 0 := fun s _ x hx => by
    simp [g, hχK x hx]
  have hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) := by
    have h1 := continuous_heatOp_joint hΔ2.continuous (M := MΔ)
      (fun y => by simpa [Real.norm_eq_abs] using hMΔ y)
    have h2 : Continuous (fun q : ℝ × (Fin d → ℝ) => (σ q.1, q.2)) :=
      (Real.continuous_sqrt.comp (continuous_const.mul
        (continuous_const.sub continuous_fst))).prodMk continuous_snd
    exact (continuous_const.mul ((hχ.continuous.comp continuous_snd).mul (h1.comp h2))).neg
  have hd : ∀ s ∈ Icc t₀ t, ∀ x, HasDerivWithinAt (fun r => ψ r x) (g s x) (Icc t₀ t) s := by
    intro s hs x
    have h1 := hasDerivWithinAt_integral_sqrt hφ2 hφc hD (sub_nonneg.2 hs.2) x
    have h2 : HasDerivWithinAt (fun r : ℝ => t - r) (-1) (Icc t₀ t) s := by
      simpa using ((hasDerivAt_id s).const_sub t).hasDerivWithinAt
    have h3 := (h1.comp s h2 (fun r hr => mem_Ici.2 (sub_nonneg.2 hr.2))).const_mul (χ x)
    convert h3 using 1
    all_goals first | rfl | (rw [hg]; simp only [heatOp]; ring)
  have hF : ∀ μ : ℝ → Measure (Fin d → ℝ), (∀ t, 0 ≤ t → IsProbabilityMeasure (μ t)) →
      WeakFokkerPlanck μ b D → ∀ s ∈ Icc t₀ t, HasDerivWithinAt (fun r => ∫ x, ψ r x ∂(μ r))
        (∫ x, g s x ∂(μ s) +
          ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂(μ s)) (Icc t₀ t) s :=
    fun μ hμ hfp s hs => hasDerivWithinAt_integral_fp hμ hfp ht₀ (fun s _ => hψT s)
      (fun s _ => hgT s) hd hgc hχc hgK hs
  -- the residual decomposition
  set P : ℝ → (Fin d → ℝ) → ℝ := fun s x => χ x * (b s x ⬝ᵥ grad (u s) x) with hP
  set E : ℝ → (Fin d → ℝ) → ℝ := fun s x => u s x * (b s x ⬝ᵥ grad χ x) +
    2 * D * (grad χ x ⬝ᵥ grad (u s) x) + D * (u s x * laplacian χ x) with hE
  have hres : ∀ s x, g s x + (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) =
      P s x + E s x := by
    intro s x
    have e1 : grad (ψ s) x = χ x • grad (u s) x + u s x • grad χ x :=
      grad_mul (hχ2.differentiable two_ne_zero) ((hu2 s).differentiable two_ne_zero) x
    have e2 : laplacian (ψ s) x = χ x * laplacian (u s) x +
        2 * (grad χ x ⬝ᵥ grad (u s) x) + u s x * laplacian χ x := laplacian_mul hχ2 (hu2 s) x
    have e3 : laplacian (u s) x = heatOp (σ s) (laplacian φ) x := laplacian_heatOp hφ2 hφc _ x
    rw [e1, e2, e3]
    simp only [P, E, g, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have hu0 : ∀ s x, |u s x| ≤ C := fun s x => abs_heatOp_le hC _ x
  have hdu : ∀ s x i, |grad (u s) x i| ≤ G₁ := fun s x i => by
    show |partialDeriv i (heatOp (σ s) φ) x| ≤ G₁
    rw [partialDeriv_heatOp hφ1 hφc]
    exact abs_heatOp_le (hpd i) _ x
  have hbi : ∀ s, 0 ≤ s → ∀ x i, |b s x i| ≤ B := fun s hs x i =>
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm (b s x) i).trans (hB s hs x)
  have hχi : ∀ x i, |grad χ x i| ≤ ε' := fun x i =>
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm (grad χ x) i).trans (hχg x)
  have hEb : ∀ s, 0 ≤ s → ∀ x, |E s x| ≤ ε' * A := by
    intro s hs x
    have e1 : |u s x * (b s x ⬝ᵥ grad χ x)| ≤ C * (d * (B * ε')) := by
      rw [abs_mul]
      exact mul_le_mul (hu0 s x) (abs_dotProduct_le (hbi s hs x) (hχi x)) (abs_nonneg _) hC0
    have e2 : |2 * D * (grad χ x ⬝ᵥ grad (u s) x)| ≤ 2 * D * (d * (ε' * G₁)) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * D)]
      exact mul_le_mul_of_nonneg_left (abs_dotProduct_le (hχi x) (hdu s x)) (by positivity)
    have e3 : |D * (u s x * laplacian χ x)| ≤ D * (C * ε') := by
      rw [abs_mul, abs_of_pos hD, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hu0 s x) (hχl x) (abs_nonneg _) hC0) hD.le
    calc _ ≤ _ := abs_add_three _ _ _
      _ ≤ _ := add_le_add (add_le_add e1 e2) e3
      _ = ε' * A := by rw [hA]; ring
  have hEc : ∀ s, 0 ≤ s → Continuous (E s) := fun s hs =>
    (((hu2 s).continuous.mul ((hbc s hs).dotProduct (continuous_grad hχ2))).add
      (continuous_const.mul ((continuous_grad hχ2).dotProduct (continuous_grad (hu2 s))))).add
      (continuous_const.mul ((hu2 s).continuous.mul (continuous_laplacian hχ2)))
  have hPc : ∀ s, 0 ≤ s → Continuous (P s) := fun s hs =>
    hχ.continuous.mul ((hbc s hs).dotProduct (continuous_grad (hu2 s)))
  have hPK : ∀ s, HasCompactSupport (P s) := fun s =>
    HasCompactSupport.intro hχc fun x hx => by simp [P, hχK x hx]
  -- the derivative in split form
  have hsplit : ∀ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ → ∀ s, 0 ≤ s →
      ∫ x, g s x ∂μ + ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂μ =
        ∫ x, P s x ∂μ + ∫ x, E s x ∂μ := by
    intro μ _ s hs
    have hgI : Integrable (g s) μ :=
      (hgT s).1.continuous.integrable_of_hasCompactSupport (hgT s).2
    have hPI : Integrable (P s) μ := (hPc s hs).integrable_of_hasCompactSupport (hPK s)
    have hEI : Integrable (E s) μ := integrable_of_abs_le (hEc s hs) (hEb s hs)
    have hL : (fun x => b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) =
        fun x => P s x + E s x - g s x := funext fun x => by linarith [hres s x]
    have h1 := integral_sub (μ := μ) (f := fun x => P s x + E s x) (g := g s)
      (hPI.add hEI) hgI
    have h2 := integral_add (μ := μ) (f := P s) (g := E s) hPI hEI
    rw [hL, h1, h2]
    ring
  -- the mean value inequality
  set f : ℝ → ℝ := fun r => ∫ x, ψ r x ∂(ρ r) - ∫ x, ψ r x ∂(ρ' r) with hf
  set f' : ℝ → ℝ := fun s => (∫ x, g s x ∂(ρ s) +
      ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂(ρ s)) -
    (∫ x, g s x ∂(ρ' s) + ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂(ρ' s))
    with hf'
  have hfd : ∀ s ∈ Icc t₀ t, HasDerivWithinAt f (f' s) (Icc t₀ t) s := fun s hs =>
    (hF ρ hprob hρ s hs).sub (hF ρ' hprob' hρ' s hs)
  set Bf : ℝ → ℝ := fun s => M * C * K₀ * (Real.sqrt (t - t₀) - Real.sqrt (t - s)) +
    2 * (ε' * A) * (s - t₀) with hBf
  set Bf' : ℝ → ℝ := fun s => M * C * K₀ / (2 * Real.sqrt (t - s)) + 2 * (ε' * A) with hBf'
  have hBc : ContinuousOn Bf (Icc t₀ t) :=
    ((continuous_const.mul (continuous_const.sub (Real.continuous_sqrt.comp
      (continuous_const.sub continuous_id)))).add
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  have hBd : ∀ s ∈ Ico t₀ t, HasDerivWithinAt Bf (Bf' s) (Ici s) s := by
    intro s hs
    have hts : t - s ≠ 0 := by linarith [hs.2]
    have hsq := ((hasDerivAt_id s).const_sub t).sqrt hts
    have := ((hsq.const_sub (Real.sqrt (t - t₀))).const_mul (M * C * K₀)).add
      (((hasDerivAt_id s).sub_const t₀).const_mul (2 * (ε' * A)))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [Bf', id]
    ring
  have hbound : ∀ s ∈ Ico t₀ t, ‖f' s‖ ≤ Bf' s := by
    intro s hs
    have hs0 : 0 ≤ s := ht₀.trans hs.1
    have hts : 0 < t - s := by linarith [hs.2]
    have hσs : 0 < σ s := Real.sqrt_pos.2 (by positivity)
    have := hprob s hs0
    have := hprob' s hs0
    have hPb : ∀ x, |P s x| ≤ d * (B * (C / σ s)) := by
      intro x
      have hg1 : ∀ i, |grad (u s) x i| ≤ C / σ s := fun i => by
        show |partialDeriv i (heatOp (σ s) φ) x| ≤ C / σ s
        rw [partialDeriv_heatOp hφ1 hφc]
        exact abs_integral_partialDeriv_comp_le hφ1 hφc hC hσs i x
      rw [abs_mul]
      calc |χ x| * |b s x ⬝ᵥ grad (u s) x| ≤ 1 * (d * (B * (C / σ s))) :=
            mul_le_mul (hχ0 x) (abs_dotProduct_le (hbi s hs0 x) hg1) (abs_nonneg _)
              zero_le_one
        _ = _ := one_mul _
    have h1 := hTV s hs (P s) (hPc s hs0) (hPK s) _ hPb
    have h2 := abs_integral_le_of_abs_le (μ := ρ s) (hEb s hs0)
    have h3 := abs_integral_le_of_abs_le (μ := ρ' s) (hEb s hs0)
    have hσeq : σ s = Real.sqrt (2 * D) * Real.sqrt (t - s) :=
      Real.sqrt_mul (by positivity) _
    have hsq2 : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.2 (by positivity)
    have hsqt : 0 < Real.sqrt (t - s) := Real.sqrt_pos.2 hts
    have hkey : M * (d * (B * (C / σ s))) = M * C * K₀ / (2 * Real.sqrt (t - s)) := by
      rw [hσeq, hK₀]
      field_simp
    simp only [f', Real.norm_eq_abs]
    rw [hsplit (ρ s) inferInstance s hs0, hsplit (ρ' s) inferInstance s hs0]
    calc |∫ x, P s x ∂(ρ s) + ∫ x, E s x ∂(ρ s) - (∫ x, P s x ∂(ρ' s) + ∫ x, E s x ∂(ρ' s))|
        ≤ |∫ x, P s x ∂(ρ s) - ∫ x, P s x ∂(ρ' s)| + |∫ x, E s x ∂(ρ s)| +
          |∫ x, E s x ∂(ρ' s)| := by
          have := abs_add_three (∫ x, P s x ∂(ρ s) - ∫ x, P s x ∂(ρ' s))
            (∫ x, E s x ∂(ρ s)) (-∫ x, E s x ∂(ρ' s))
          rw [abs_neg] at this
          convert this using 2
          ring
      _ ≤ M * (d * (B * (C / σ s))) + ε' * A + ε' * A := add_le_add (add_le_add h1 h2) h3
      _ = Bf' s := by rw [hkey]; simp only [Bf']; ring
  have hf0 : ‖f t₀‖ ≤ Bf t₀ := by simp [f, Bf, heq]
  have hfc : ContinuousOn f (Icc t₀ t) := fun s hs => (hfd s hs).continuousWithinAt
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hfc
    (fun s hs => (hfd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) hf0 hBc hBd hbound ⟨ht, le_rfl⟩
  have hψt : ψ t = φ := funext fun x => by
    simp only [ψ, u, σ, sub_self, mul_zero, Real.sqrt_zero, heatOp_zero]
    by_cases hx : x ∈ tsupport φ
    · rw [hχ1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hft : f t = ∫ x, φ x ∂(ρ t) - ∫ x, φ x ∂(ρ' t) := by simp only [f, hψt]
  have hεA : 2 * (ε' * A) * (t - t₀) ≤ ε := by
    rw [hε', show 2 * (ε / (2 * A * (t - t₀) + 1) * A) * (t - t₀) =
      ε * (2 * A * (t - t₀)) / (2 * A * (t - t₀) + 1) by ring, div_le_iff₀ hden]
    nlinarith
  rw [hft, Real.norm_eq_abs] at hmain
  calc _ ≤ Bf t := hmain
    _ ≤ M * C * K₀ * Real.sqrt (t - t₀) + ε := by
      simp only [Bf, sub_self, Real.sqrt_zero, sub_zero]
      linarith

/-! ### Iteration and uniqueness -/

section Uniqueness

variable {ρ ρ' : ℝ → Measure (Fin d → ℝ)} {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D B : ℝ}

/-- **Halving step (Verified).** Under the hypotheses of `abs_integral_sub_le_of_tvBound`, if
`ρ_{t₀} = ρ'_{t₀}`, `(2 d B / √(2D)) √δ ≤ 1/2` and `TVBound (ρ s) (ρ' s) M` on `[t₀, t₀ + δ]`,
then `TVBound (ρ t) (ρ' t) (M / 2)` on `[t₀, t₀ + δ]`. -/
theorem tvBound_half (hD : 0 < D) (hB0 : 0 ≤ B)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t)) (hB : ∀ t, 0 ≤ t → ∀ x, ‖b t x‖ ≤ B)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D)
    {t₀ δ : ℝ} (ht₀ : 0 ≤ t₀)
    (hKδ : 2 * d * B / Real.sqrt (2 * D) * Real.sqrt δ ≤ 1 / 2) (heq : ρ t₀ = ρ' t₀)
    {M : ℝ} (hM : 0 ≤ M) (hTV : ∀ s ∈ Icc t₀ (t₀ + δ), TVBound (ρ s) (ρ' s) M) :
    ∀ t ∈ Icc t₀ (t₀ + δ), TVBound (ρ t) (ρ' t) (M / 2) := by
  intro t ht g hg hgc C hC
  have := hprob t (ht₀.trans ht.1)
  have := hprob' t (ht₀.trans ht.1)
  refine abs_integral_sub_le_of_smooth (by positivity) (fun φ hφ hφc C' hC' => ?_) hg hgc hC
  have hC'0 : 0 ≤ C' := (abs_nonneg _).trans (hC' 0)
  have h := abs_integral_sub_le_of_tvBound hD hB0 hbc hB hprob hprob' hρ hρ' ht₀ ht.1 heq
    (fun s hs => hTV s ⟨hs.1, hs.2.le.trans ht.2⟩) hφ hφc hC'
  have hK0 : 0 ≤ 2 * d * B / Real.sqrt (2 * D) := by positivity
  have hsq : Real.sqrt (t - t₀) ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by linarith [ht.2])
  have h2 : 2 * d * B / Real.sqrt (2 * D) * Real.sqrt (t - t₀) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hsq hK0).trans hKδ
  calc _ ≤ M * C' * (2 * d * B / Real.sqrt (2 * D) * Real.sqrt (t - t₀)) := by
        rw [← mul_assoc]; exact h
    _ ≤ M * C' * (1 / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = M / 2 * C' := by ring

/-- **Uniqueness on one short interval (Verified).** If `ρ_{t₀} = ρ'_{t₀}` and
`(2 d B / √(2D)) √δ ≤ 1/2`, then `ρ_t = ρ'_t` for `t ∈ [t₀, t₀ + δ]`. -/
theorem eq_on_Icc_of_eq (hD : 0 < D) (hB0 : 0 ≤ B)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t)) (hB : ∀ t, 0 ≤ t → ∀ x, ‖b t x‖ ≤ B)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D)
    {t₀ δ : ℝ} (ht₀ : 0 ≤ t₀)
    (hKδ : 2 * d * B / Real.sqrt (2 * D) * Real.sqrt δ ≤ 1 / 2) (heq : ρ t₀ = ρ' t₀) :
    ∀ t ∈ Icc t₀ (t₀ + δ), ρ t = ρ' t := by
  have key : ∀ n : ℕ, ∀ s ∈ Icc t₀ (t₀ + δ), TVBound (ρ s) (ρ' s) (2 / 2 ^ n) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have := hprob s (ht₀.trans hs.1)
      have := hprob' s (ht₀.trans hs.1)
      simpa using tvBound_two (ρ s) (ρ' s)
    | succ n ih =>
      have := tvBound_half hD hB0 hbc hB hprob hprob' hρ hρ' ht₀ hKδ heq (by positivity) ih
      intro s hs
      have e : (2 : ℝ) / 2 ^ (n + 1) = 2 / 2 ^ n / 2 := by rw [pow_succ]; ring
      rw [e]
      exact this s hs
  intro t ht
  have := hprob t (ht₀.trans ht.1)
  have := hprob' t (ht₀.trans ht.1)
  refine ext_of_forall_integral_smooth_eq fun φ hφ hφc => ?_
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hC' : ∀ x, |φ x| ≤ C := fun x => by simpa [Real.norm_eq_abs] using hC x
  have hlim : Tendsto (fun n : ℕ => 2 / 2 ^ n * C) atTop (𝓝 (0 * C)) :=
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).mul_const C
  have hle : |∫ x, φ x ∂(ρ t) - ∫ x, φ x ∂(ρ' t)| ≤ 0 * C :=
    ge_of_tendsto' hlim fun n => key n t ht φ hφ.continuous hφc C hC'
  rw [zero_mul] at hle
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hle)

/-- **Uniqueness for the weak Fokker–Planck equation (Verified).** Let `D > 0` and let the
(time-dependent) drift `b` be continuous in `x` and bounded, `‖b_t(x)‖ ≤ B`, for `t ≥ 0` (no
Lipschitz condition and no regularity in `t`). If `ρ, ρ'` are curves of probability measures on
`t ≥ 0` solving `WeakFokkerPlanck · b D` with `ρ 0 = ρ' 0`, then `ρ t = ρ' t` for all `t ≥ 0`. -/
theorem eq_of_weakFokkerPlanck (hD : 0 < D)
    (hbc : ∀ t, 0 ≤ t → Continuous (b t)) (hB : ∀ t, 0 ≤ t → ∀ x, ‖b t x‖ ≤ B)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D) (h0 : ρ 0 = ρ' 0) :
    ∀ t, 0 ≤ t → ρ t = ρ' t := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl 0)
  set K₀ : ℝ := 2 * d * B / Real.sqrt (2 * D) with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  set δ : ℝ := 1 / (4 * K₀ ^ 2 + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hKδ : K₀ * Real.sqrt δ ≤ 1 / 2 := by
    have hy : 0 ≤ K₀ * Real.sqrt δ := by positivity
    have hsq : (K₀ * Real.sqrt δ) ^ 2 = K₀ ^ 2 * δ := by
      rw [mul_pow, Real.sq_sqrt hδ0.le]
    have h4 : K₀ ^ 2 * δ ≤ 1 / 4 := by
      rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hn : ∀ n : ℕ, ∀ t ∈ Icc 0 (n * δ), ρ t = ρ' t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      rw [this, h0]
    | succ n ih =>
      intro t ht
      by_cases htn : t ≤ n * δ
      · exact ih t ⟨ht.1, htn⟩
      · have hn0 : 0 ≤ (n : ℝ) * δ := by positivity
        refine eq_on_Icc_of_eq hD hB0 hbc hB hprob hprob' hρ hρ' hn0 hKδ
          (ih _ ⟨hn0, le_rfl⟩) t ⟨(not_le.1 htn).le, ?_⟩
        have := ht.2
        push_cast at this
        linarith
  intro t ht
  obtain ⟨n, hn'⟩ := exists_nat_ge (t / δ)
  exact hn n t ⟨ht, by rwa [div_le_iff₀ hδ0] at hn'⟩

end Uniqueness

/-! ### Autonomous drifts -/

/-- **Uniqueness, autonomous form (Verified).** For `b : ℝᵈ → ℝᵈ` continuous and bounded and
`D > 0`, two probability solutions of `WeakFokkerPlanck · (fun _ => b) D` on `t ≥ 0` with the
same initial law agree for all `t ≥ 0`. -/
theorem eq_of_weakFokkerPlanck_autonomous {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {b : (Fin d → ℝ) → Fin d → ℝ} (hb : Continuous b) {B D : ℝ} (hB : ∀ x, ‖b x‖ ≤ B)
    (hD : 0 < D) (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ (fun _ => b) D) (hρ' : WeakFokkerPlanck ρ' (fun _ => b) D)
    (h0 : ρ 0 = ρ' 0) : ∀ t, 0 ≤ t → ρ t = ρ' t :=
  eq_of_weakFokkerPlanck hD (fun _ _ => hb) (fun _ _ => hB) hprob hprob' hρ hρ' h0

end FormalizeSampling.FokkerPlanckUniqueness
