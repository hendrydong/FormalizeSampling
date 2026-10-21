module

public import FormalizeSampling.Flow.KLDecay

/-!
# FL-4 with an additive error: exponential KL decay plus an integrated error term

Generalisation of the FL-4 Grönwall step of `FormalizeSampling.Flow.KLDecay` to a differential
inequality with a source term, and its application to transport along an approximate velocity
with an **absolute** weighted-L² velocity error.

## Contents (registry ID FL-4)

* `le_exp_mul_add_integral` (Verified): abstract Grönwall inequality with a source. If
  `K' ≤ -a K + e` on `t ≥ 0`, with `e` continuous on `[0, ∞)` and `a : ℝ` arbitrary, then
  `K t ≤ exp(-a t) K 0 + ∫₀ᵗ exp(-a (t - s)) e(s) ds`.
* `le_exp_mul_add_const` / `le_exp_mul_add_div` (Verified): the constant-source corollary
  `K t ≤ exp(-a t) K 0 + (ε / a)(1 - exp(-a t)) ≤ exp(-a t) K 0 + ε / a` for `a > 0`
  (the second form needs `ε ≥ 0`). No continuity is needed beyond `HasDerivAt K`.
* `exp_decay_absError` (Conditional): along a transport flow with velocity `f t`, under the
  assumed FL-1 first variation, the assumed LSI along the flow and `λ_max(H) ≤ M`,
  `KL(t) ≤ exp(-lam t / M) KL(0) + ½ ∫₀ᵗ exp(-lam (t - s) / M) E(s) ds`,
  where `E(t) = ∫ ‖f t - v⋆_t‖²_H dμ_t` is the absolute velocity error averaged under the
  current law `μ_t`; `E` is assumed continuous on `[0, ∞)`.
* `exp_decay_absError_sup` (Conditional): if `E(s) ≤ ε` for all `s ≥ 0`, then
  `KL(t) ≤ exp(-lam t / M) KL(0) + ε M / (2 lam)`; no continuity of `E` is needed.

## Constants

From FL-3 (`KLDecay.transport_rate_le`), `d/dt KL ≤ -½ D + ½ E` with
`D = ∫ ‖s - sStar‖²_{H⁻¹} dμ`. The spectral bound gives `D ≥ (1/M) I` (`I` the relative Fisher
information) and the LSI gives `I ≥ 2 lam KL`, so `d/dt KL ≤ -(lam / M) KL + ½ E`. The decay rate
is therefore `r = lam / M`, half the ideal-velocity rate `2 lam / M` of
`KLDecay.exp_decay_idealVelocity`: the factor `½` in front of `D` is the price of the
absolute-error form of FL-3.

## Assumed (named hypotheses, Conditional status)

`KLDecay.KLFirstVariation` (FL-1 KL derivative along `f`) and `KLDecay.LogSobolevAlong`
(target LSI evaluated along the flow); neither is proved here.

## What is NOT proved

No PDE well-posedness, no LSI in this file (the Gaussian case is
`LogSobolevAlongGaussian.logSobolevAlong_gaussian`), no bound on `E` itself (that is an
estimation/optimisation question), no discretisation or finite-particle analysis.
-/

public section

open Matrix MeasureTheory

namespace FormalizeSampling
namespace DecayWithError

open SPD KLDecay

variable {d : ℕ}

/-! ### Abstract Grönwall inequality with a source -/

/-- **Grönwall inequality with a source term.** Let `K K' e : ℝ → ℝ` and `a : ℝ` (any sign).
Assume for every `t ≥ 0` that `HasDerivAt K (K' t) t` and `K' t ≤ -a * K t + e t`, and that `e`
is continuous on `[0, ∞)`. Then for every `t ≥ 0`,
`K t ≤ exp(-a t) K 0 + ∫₀ᵗ exp(-a (t - s)) e(s) ds`.
Proof: `g(t) = exp(a t) K t - ∫₀ᵗ exp(a s) e(s) ds` has nonpositive derivative on `(0, T)` and
is continuous on `[0, T]`, hence is antitone there. -/
theorem le_exp_mul_add_integral {K K' e : ℝ → ℝ} {a : ℝ}
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt K (K' t) t)
    (he : ContinuousOn e (Set.Ici 0))
    (hineq : ∀ t, 0 ≤ t → K' t ≤ -a * K t + e t) :
    ∀ t, 0 ≤ t →
      K t ≤ Real.exp (-a * t) * K 0 + ∫ s in (0 : ℝ)..t, Real.exp (-a * (t - s)) * e s := by
  intro T hT
  set w : ℝ → ℝ := fun s => Real.exp (a * s) * e s with hwdef
  have hexp : ∀ t, HasDerivAt (fun t => Real.exp (a * t)) (Real.exp (a * t) * a) t := by
    intro t
    simpa using ((hasDerivAt_id t).const_mul a).exp
  have hwcont : ContinuousOn w (Set.Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul he
  have hsub : Set.uIcc 0 T ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hT]
    exact Set.Icc_subset_Ici_self
  have hwint : ∀ t, 0 ≤ t → IntervalIntegrable w volume 0 t := fun t ht =>
    (hwcont.mono (by rw [Set.uIcc_of_le ht]; exact Set.Icc_subset_Ici_self)).intervalIntegrable
  set g : ℝ → ℝ := fun t => Real.exp (a * t) * K t - ∫ s in (0 : ℝ)..t, w s with hgdef
  have hg : ∀ t, 0 < t →
      HasDerivAt g (Real.exp (a * t) * a * K t + Real.exp (a * t) * K' t - w t) t := by
    intro t ht
    have hmeas : StronglyMeasurableAtFilter w (nhds t) volume :=
      (hwcont.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t ht
    have hca : ContinuousAt w t :=
      hwcont.continuousAt (Ici_mem_nhds ht)
    exact ((hexp t).mul (hderiv t ht.le)).sub
      (intervalIntegral.integral_hasDerivAt_right (hwint t ht.le) hmeas hca)
  have hgcont : ContinuousOn g (Set.Icc 0 T) := by
    refine ContinuousOn.sub ?_ ?_
    · intro t ht
      exact ((hexp t).mul (hderiv t ht.1)).continuousAt.continuousWithinAt
    · have h := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (hwint T hT)
        (a := 0) Set.left_mem_uIcc
      rwa [Set.uIcc_of_le hT] at h
  have hanti : AntitoneOn g (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hg t ht.1).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hg t ht.1).deriv]
      have h1 := hineq t ht.1.le
      have h2 := Real.exp_pos (a * t)
      simp only [hwdef]
      nlinarith
  have hle : g T ≤ g 0 :=
    hanti ⟨le_refl 0, hT⟩ ⟨hT, le_refl T⟩ hT
  simp only [hgdef, mul_zero, Real.exp_zero, one_mul, intervalIntegral.integral_same,
    sub_zero] at hle
  have hK : K T = Real.exp (-a * T) * (Real.exp (a * T) * K T) := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hI : Real.exp (-a * T) * ∫ s in (0 : ℝ)..T, w s =
      ∫ s in (0 : ℝ)..T, Real.exp (-a * (T - s)) * e s := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    simp only [hwdef]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  have hpos := Real.exp_pos (-a * T)
  have h3 : Real.exp (-a * T) * (Real.exp (a * T) * K T) ≤
      Real.exp (-a * T) * (K 0 + ∫ s in (0 : ℝ)..T, w s) := by
    apply mul_le_mul_of_nonneg_left _ hpos.le
    linarith
  rw [hK]
  rw [mul_add, hI] at h3
  exact h3

/-- **Grönwall with a constant source.** Let `a > 0` and `ε : ℝ`. If for every `t ≥ 0`,
`HasDerivAt K (K' t) t` and `K' t ≤ -a * K t + ε`, then for every `t ≥ 0`,
`K t ≤ exp(-a t) K 0 + (ε / a) (1 - exp(-a t))`.
(Proof: apply `le_exp_mul_add_integral` with zero source to `K - ε / a`.) -/
theorem le_exp_mul_add_const {K K' : ℝ → ℝ} {a ε : ℝ} (ha : 0 < a)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt K (K' t) t)
    (hineq : ∀ t, 0 ≤ t → K' t ≤ -a * K t + ε) :
    ∀ t, 0 ≤ t → K t ≤ Real.exp (-a * t) * K 0 + ε / a * (1 - Real.exp (-a * t)) := by
  have h := le_exp_mul_add_integral (K := fun t => K t - ε / a) (K' := K') (e := fun _ => 0)
    (a := a) (fun t ht => (hderiv t ht).sub_const _) continuousOn_const (fun t ht => by
      have h1 := hineq t ht
      have h2 : -a * (K t - ε / a) + 0 = -a * K t + ε := by field_simp; ring
      rw [h2]; exact h1)
  intro t ht
  have h1 := h t ht
  simp only [mul_zero, intervalIntegral.integral_zero, add_zero] at h1
  nlinarith

/-- **Grönwall with a constant nonnegative source, simplified.** Let `a > 0` and `ε ≥ 0`. If for
every `t ≥ 0`, `HasDerivAt K (K' t) t` and `K' t ≤ -a * K t + ε`, then for every `t ≥ 0`,
`K t ≤ exp(-a t) K 0 + ε / a`. -/
theorem le_exp_mul_add_div {K K' : ℝ → ℝ} {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt K (K' t) t)
    (hineq : ∀ t, 0 ≤ t → K' t ≤ -a * K t + ε) :
    ∀ t, 0 ≤ t → K t ≤ Real.exp (-a * t) * K 0 + ε / a := by
  intro t ht
  have h1 := le_exp_mul_add_const ha hderiv hineq t ht
  have h2 : 0 ≤ ε / a := div_nonneg hε ha.le
  have h3 := Real.exp_pos (-a * t)
  nlinarith

/-! ### Application: transport flow with absolute velocity error -/

/-- **Rate bound with absolute velocity error.** Let `H` be positive definite with
`uᵀ H u ≤ M |u|²` (`M > 0`) and `lam > 0`. At a time `t ≥ 0`, assume integrability (under
`μ t`) of `f t ⬝ᵥ (s t - sStar)`, `‖s t - sStar‖²_{H⁻¹}`, `‖f t - v⋆_t‖²_H` and
`|s t - sStar|²`, and the LSI `KL t ≤ relFisher / (2 lam)`. Then
`∫ f t ⬝ᵥ (s t - sStar) dμ_t ≤ -(lam / M) KL t + ½ ∫ ‖f t - v⋆_t‖²_H dμ_t`. -/
theorem rate_le_neg_KL_add_err {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M lam : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hlam : 0 < lam)
    {μ : Measure (Fin d → ℝ)} {f s sStar : (Fin d → ℝ) → Fin d → ℝ} {KLt : ℝ}
    (hrate : Integrable (fun x => f x ⬝ᵥ (s x - sStar x)) μ)
    (hdiss : Integrable (fun x => sqNormH H⁻¹ (s x - sStar x)) μ)
    (herr : Integrable (fun x => sqNormH H (f x - idealVelocity H s sStar x)) μ)
    (hfisher : Integrable (fun x => (s x - sStar x) ⬝ᵥ (s x - sStar x)) μ)
    (hLSI : KLt ≤ relFisher μ s sStar / (2 * lam)) :
    ∫ x, f x ⬝ᵥ (s x - sStar x) ∂μ ≤
      -(lam / M) * KLt + (1 / 2) * ∫ x, sqNormH H (f x - idealVelocity H s sStar x) ∂μ := by
  have h1 := transport_rate_le hH f s sStar hrate hdiss herr
  have h2 := fisher_le_dissipation hH hM hspec hdiss hfisher
  have h3 : 2 * lam * KLt ≤ relFisher μ s sStar := by
    rw [le_div_iff₀ (by positivity)] at hLSI
    linarith
  have h4 : (lam / M) * KLt ≤ (1 / 2) * ((1 / M) * relFisher μ s sStar) := by
    have h5 : (lam / M) * KLt = (1 / 2) * ((1 / M) * (2 * lam * KLt)) := by
      field_simp
    rw [h5]
    have : 0 < 1 / M := by positivity
    nlinarith
  linarith

/-- **FL-4 with absolute velocity error (Conditional).** Let `H` be positive definite with
`uᵀ H u ≤ M |u|²` for all `u` (`M > 0`) and `lam > 0`. Along a law `μ t` with score field `s t`,
target score `sStar`, ideal velocity `v⋆_t = H⁻¹(sStar - s t)` and actual velocity `f t`, let
`E t = ∫ ‖f t - v⋆_t‖²_H dμ_t` (absolute velocity error, averaged under the current law `μ_t`).
Assume for every `t ≥ 0`:
* `KLFirstVariation μ f s sStar KL` (**assumed** FL-1: `d/dt KL = ∫ f t ⬝ᵥ (s t - sStar) dμ_t`);
* integrability under `μ t` of `f t ⬝ᵥ (s t - sStar)`, `‖s t - sStar‖²_{H⁻¹}`,
  `‖f t - v⋆_t‖²_H` and `|s t - sStar|²`;
* `LogSobolevAlong lam μ s sStar KL` (**assumed** LSI along the flow);
* `t ↦ E t` is continuous on `[0, ∞)`.
Then for every `t ≥ 0`,
`KL t ≤ exp(-lam t / M) KL 0 + ½ ∫₀ᵗ exp(-lam (t - s) / M) E(s) ds`.
The rate `lam / M` is half the ideal rate of `exp_decay_idealVelocity`. Status: Conditional. -/
theorem exp_decay_absError {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M lam : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hlam : 0 < lam)
    {μ : ℝ → Measure (Fin d → ℝ)} {f s : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sStar : (Fin d → ℝ) → Fin d → ℝ} {KL : ℝ → ℝ}
    (hKL : KLFirstVariation μ f s sStar KL)
    (hrate : ∀ t, 0 ≤ t → Integrable (fun x => f t x ⬝ᵥ (s t x - sStar x)) (μ t))
    (hdiss : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H⁻¹ (s t x - sStar x)) (μ t))
    (herr : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H (f t x - idealVelocity H (s t) sStar x)) (μ t))
    (hfisher : ∀ t, 0 ≤ t →
      Integrable (fun x => (s t x - sStar x) ⬝ᵥ (s t x - sStar x)) (μ t))
    (hLSI : LogSobolevAlong lam μ s sStar KL)
    (hEcont : ContinuousOn
      (fun t => ∫ x, sqNormH H (f t x - idealVelocity H (s t) sStar x) ∂(μ t)) (Set.Ici 0)) :
    ∀ t, 0 ≤ t → KL t ≤ Real.exp (-(lam * t / M)) * KL 0 +
      (1 / 2) * ∫ r in (0 : ℝ)..t, Real.exp (-(lam * (t - r) / M)) *
        ∫ x, sqNormH H (f r x - idealVelocity H (s r) sStar x) ∂(μ r) := by
  set E : ℝ → ℝ :=
    fun t => ∫ x, sqNormH H (f t x - idealVelocity H (s t) sStar x) ∂(μ t) with hEdef
  have key := le_exp_mul_add_integral (K := KL)
    (K' := fun t => ∫ x, f t x ⬝ᵥ (s t x - sStar x) ∂(μ t)) (e := fun t => (1 / 2) * E t)
    (a := lam / M) hKL (continuousOn_const.mul hEcont) (fun t ht =>
      rate_le_neg_KL_add_err hH hM hspec hlam (hrate t ht) (hdiss t ht) (herr t ht)
        (hfisher t ht) (hLSI t ht))
  intro t ht
  have h := key t ht
  have h1 : -(lam / M) * t = -(lam * t / M) := by ring
  have h2 : ∫ r in (0 : ℝ)..t, Real.exp (-(lam / M) * (t - r)) * ((1 / 2) * E r) =
      (1 / 2) * ∫ r in (0 : ℝ)..t, Real.exp (-(lam * (t - r) / M)) * E r := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    have : -(lam / M) * (t - r) = -(lam * (t - r) / M) := by ring
    rw [this]
    ring
  rw [h1, h2] at h
  exact h

/-- **FL-4 with uniformly bounded absolute velocity error (Conditional).** Same setting as
`exp_decay_absError` but, instead of continuity of `E`, assume the uniform bound
`E t = ∫ ‖f t - v⋆_t‖²_H dμ_t ≤ ε` for every `t ≥ 0` (with `ε ≥ 0`). Then for every `t ≥ 0`,
`KL t ≤ exp(-lam t / M) KL 0 + (ε M / (2 lam)) (1 - exp(-lam t / M))`
`≤ exp(-lam t / M) KL 0 + ε M / (2 lam)`,
i.e. `ε / (2 r)` with rate `r = lam / M`. Status: Conditional (FL-1 and LSI assumed). -/
theorem exp_decay_absError_sup {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {M lam ε : ℝ}
    (hM : 0 < M) (hspec : ∀ u : Fin d → ℝ, sqNormH H u ≤ M * (u ⬝ᵥ u)) (hlam : 0 < lam)
    (hε : 0 ≤ ε)
    {μ : ℝ → Measure (Fin d → ℝ)} {f s : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {sStar : (Fin d → ℝ) → Fin d → ℝ} {KL : ℝ → ℝ}
    (hKL : KLFirstVariation μ f s sStar KL)
    (hrate : ∀ t, 0 ≤ t → Integrable (fun x => f t x ⬝ᵥ (s t x - sStar x)) (μ t))
    (hdiss : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH H⁻¹ (s t x - sStar x)) (μ t))
    (herr : ∀ t, 0 ≤ t →
      Integrable (fun x => sqNormH H (f t x - idealVelocity H (s t) sStar x)) (μ t))
    (hfisher : ∀ t, 0 ≤ t →
      Integrable (fun x => (s t x - sStar x) ⬝ᵥ (s t x - sStar x)) (μ t))
    (hLSI : LogSobolevAlong lam μ s sStar KL)
    (hEbound : ∀ t, 0 ≤ t →
      ∫ x, sqNormH H (f t x - idealVelocity H (s t) sStar x) ∂(μ t) ≤ ε) :
    ∀ t, 0 ≤ t →
      KL t ≤ Real.exp (-(lam * t / M)) * KL 0 +
          ε * M / (2 * lam) * (1 - Real.exp (-(lam * t / M))) ∧
      KL t ≤ Real.exp (-(lam * t / M)) * KL 0 + ε * M / (2 * lam) := by
  have hineq : ∀ t, 0 ≤ t →
      ∫ x, f t x ⬝ᵥ (s t x - sStar x) ∂(μ t) ≤ -(lam / M) * KL t + ε / 2 := by
    intro t ht
    have h := rate_le_neg_KL_add_err hH hM hspec hlam (hrate t ht) (hdiss t ht) (herr t ht)
      (hfisher t ht) (hLSI t ht)
    have := hEbound t ht
    linarith
  have ha : 0 < lam / M := by positivity
  intro t ht
  have h1 := le_exp_mul_add_const ha hKL hineq t ht
  have h2 := le_exp_mul_add_div ha (by linarith) hKL hineq t ht
  have e1 : -(lam / M) * t = -(lam * t / M) := by ring
  have e2 : ε / 2 / (lam / M) = ε * M / (2 * lam) := by field_simp
  rw [e1, e2] at h1 h2
  exact ⟨h1, h2⟩

end DecayWithError
end FormalizeSampling
