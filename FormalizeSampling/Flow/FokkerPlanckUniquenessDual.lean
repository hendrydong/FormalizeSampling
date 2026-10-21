module

public import FormalizeSampling.Flow.NoiseScoreEquivalence

/-!
# Time derivative along a solution of the weak Fokker–Planck equation

Status: **Verified.** The product rule behind duality arguments for
`NoiseScore.WeakFokkerPlanck`: for a probability solution `ρ` and a time-dependent `C²_c`
test function `ψ(s, ·)` with time derivative `g(s, ·)`,

  `d/ds ∫ ψ(s) dρ_s = ∫ g(s) dρ_s + ∫ (b_s ⬝ ∇ψ(s) + D Δψ(s)) dρ_s`

within `[a, c] ⊆ [0, ∞)` (`hasDerivWithinAt_integral_fp`). This is the Fokker–Planck analogue
of `abs_integral_sub_le_of_approx_dual` (`Flow/ContinuityUniquenessLipschitz`), with the same
proof (split into three `o(r - s)` terms), stated as a derivative so that it can be combined
with non-constant bounds (used in `Flow/FokkerPlanckUniqueness`).

## Not proved here

* Only `C²_c` test functions with jointly continuous, uniformly compactly supported time
  derivative; no extension to test functions without compact support.
* No uniqueness statement; see `Flow/FokkerPlanckUniqueness`.
-/

public section

open MeasureTheory Matrix Set Filter Topology Metric Asymptotics

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore

variable {d : ℕ}

/-- **Product rule along a weak Fokker–Planck solution (Verified).** Let `ρ` be a curve of
probability measures on `t ≥ 0` solving `WeakFokkerPlanck ρ b D`, `0 ≤ a`, and
`ψ, g : ℝ → ℝᵈ → ℝ` with `g s x = ∂ₛψ(s, x)` (derivative within `[a, c]`) for `s ∈ [a, c]`,
`g` jointly continuous, `ψ s` and `g s` in `C²_c` for `s ∈ [a, c]`, and the supports of `g s`
in one compact `K`. Then `s ↦ ∫ ψ(s) dρ_s` has derivative
`∫ g(s) dρ_s + ∫ (b_s ⬝ ∇ψ(s) + D Δψ(s)) dρ_s` within `[a, c]` at every `s ∈ [a, c]`. -/
theorem hasDerivWithinAt_integral_fp {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    {a c : ℝ} (ha : 0 ≤ a) {ψ g : ℝ → (Fin d → ℝ) → ℝ}
    (hψ : ∀ s ∈ Icc a c, TestFunction2 (ψ s)) (hg : ∀ s ∈ Icc a c, TestFunction2 (g s))
    (hd : ∀ s ∈ Icc a c, ∀ x, HasDerivWithinAt (fun u => ψ u x) (g s x) (Icc a c) s)
    (hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hgK : ∀ s ∈ Icc a c, ∀ x ∉ K, g s x = 0)
    {s : ℝ} (hs : s ∈ Icc a c) :
    HasDerivWithinAt (fun r => ∫ x, ψ r x ∂(ρ r))
      (∫ x, g s x ∂(ρ s) + ∫ x, (b s x ⬝ᵥ grad (ψ s) x + D * laplacian (ψ s) x) ∂(ρ s))
      (Icc a c) s := by
  have hint : ∀ r, 0 ≤ r → ∀ f : (Fin d → ℝ) → ℝ, TestFunction2 f → Integrable f (ρ r) := by
    intro r hr f hf
    have := hprob r hr
    exact hf.1.continuous.integrable_of_hasCompactSupport hf.2
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
      have hc := ((hρ (g s) (hg s hs) s hs0).continuousWithinAt).mono hsub
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
    have hE1 : E1 r = ∫ x, ψ r x ∂(ρ r) - ∫ x, ψ s x ∂(ρ r) - (r - s) * ∫ x, g s x ∂(ρ r) := by
      have i1 := hint r (ha.trans hr.1) _ (hψ r hr)
      have i2 := hint r (ha.trans hr.1) _ (hψ s hs)
      have i3 := (hint r (ha.trans hr.1) _ (hg s hs)).const_mul (r - s)
      have i12 : Integrable (fun x => ψ r x - ψ s x) (ρ r) := i1.sub i2
      simp only [E1]
      rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul]
    simp only [E2, E3, hE1, smul_eq_mul]
    ring
  have := ((h1.add h2).add h3).congr' (hsum.mono fun r hr => hr.symm) EventuallyEq.rfl
  exact hasDerivWithinAt_iff_isLittleO.2 this

end FormalizeSampling.FokkerPlanckUniqueness
