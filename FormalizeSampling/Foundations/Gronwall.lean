module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Grönwall-type comparisons for the KL divergence along a heat flow

Status: **Verified** (real analysis on `ℝ`; every hypothesis is explicit).

Two real-function lemmas behind the heat-flow contraction and the Gaussian log-Sobolev
inequality, stated for abstract functions `K, I : ℝ → ℝ` with `K' = -½ I` (the de Bruijn
identity, with `K(t) = KL(ρ_t‖π_t)` and `I(t)` the relative Fisher information). The
dimension-specific statements in `Foundations/HeatFlowDeBruijn(Pi)` and
`Foundations/GaussianLSI(Pi)` are their instances.

## Main results

* `le_div_of_hasDerivAt_Ioc` (**forward Grönwall**): if `K' = -½ I` on `(0, η]`,
  `2 α K ≤ (1 + α t) I` on `(0, η)` (`α ≥ 0`) and `K τ ≤ K 0` on `(0, η)`, then
  `K η ≤ K 0 / (1 + α η)`. No derivative at `0` is needed: the argument runs on `[τ, η]` and
  `τ → 0⁺`.
* `le_of_fisher_decay` (**LSI from Fisher decay**): if `K' = -½ I` on `(0, ∞)`,
  `I s ≤ ((v + t)/(v + s))² I t` for `s > t` (`v, t > 0`), `I t ≥ 0` and `K T ≤ M / (2T)` for
  `T > t`, then `K t ≤ ((v + t)/2) I t`.

## Not proved here

* The backward-in-time variants (weight `1 + α (η - t)`) used for the RGO step are in
  `Samplers/BackwardHeatFlow` and `Samplers/ProximalSharp`; the right-derivative forward variant
  is `ProximalContraction.le_div_of_hasDerivWithinAt_le`.
-/

public section

open Set Filter Topology

namespace FormalizeSampling.Gronwall

/-- **Forward Grönwall comparison.** Let `α ≥ 0`, `η > 0` and `K, I : ℝ → ℝ` with
`K' t = -½ I t` for `t ∈ (0, η]`, `2 α K t ≤ (1 + α t) I t` for `t ∈ (0, η)`, and `K τ ≤ K 0`
for `τ ∈ (0, η)`. Then `K η ≤ K 0 / (1 + α η)`. Proof: `t ↦ (1 + α t) K t` is antitone on every
`[τ, η]`, `τ > 0`; let `τ → 0⁺`. -/
theorem le_div_of_hasDerivAt_Ioc {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) {K I : ℝ → ℝ}
    (hKd : ∀ t ∈ Ioc 0 η, HasDerivAt K (-(1 / 2) * I t) t)
    (hL : ∀ t ∈ Ioo 0 η, 2 * α * K t ≤ (1 + α * t) * I t)
    (h0 : ∀ τ ∈ Ioo 0 η, K τ ≤ K 0) :
    K η ≤ K 0 / (1 + α * η) := by
  set g : ℝ → ℝ := fun t => (1 + α * t) * K t with hg
  have hgd : ∀ t ∈ Ioc 0 η, HasDerivAt g (α * K t + (1 + α * t) * (-(1 / 2) * I t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + α * t) α t := by
      simpa using ((hasDerivAt_id t).const_mul α).const_add 1
    exact h1.mul (hKd t ht)
  have hstep : ∀ τ ∈ Ioo 0 η, g η ≤ (1 + α * τ) * K 0 := by
    intro τ hτ
    have hsub : Icc τ η ⊆ Ioc 0 η := fun t ht => ⟨hτ.1.trans_le ht.1, ht.2⟩
    have hanti : AntitoneOn g (Icc τ η) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc τ η)
        (fun t ht => (hgd t (hsub ht)).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Icc]
        exact fun t ht => (hgd t (hsub (Ioo_subset_Icc_self ht))).differentiableAt
          |>.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hgd t (hsub (Ioo_subset_Icc_self ht))).deriv]
        have := hL t ⟨hτ.1.trans ht.1, ht.2⟩
        linarith
    have h1 := hanti (left_mem_Icc.2 hτ.2.le) (right_mem_Icc.2 hτ.2.le) hτ.2.le
    have hpos : 0 ≤ 1 + α * τ := by nlinarith [hτ.1]
    exact h1.trans (mul_le_mul_of_nonneg_left (h0 τ hτ) hpos)
  have hlim : Tendsto (fun τ : ℝ => (1 + α * τ) * K 0) (𝓝[>] 0) (𝓝 (K 0)) := by
    have : Continuous (fun τ : ℝ => (1 + α * τ) * K 0) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hgη : g η ≤ K 0 := ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT hη) hstep)
  have hpos : 0 < 1 + α * η := by nlinarith
  rw [le_div_iff₀ hpos]
  simpa [hg, mul_comm] using hgη

/-- **Log-Sobolev inequality from Fisher decay.** Let `v, t > 0` and `K, I : ℝ → ℝ` with
`K' s = -½ I s` for every `s > 0`, the decay `I s ≤ ((v + t)/(v + s))² I t` for every `s > t`,
`I t ≥ 0`, and `K T ≤ M / (2T)` for every `T > t`. Then `K t ≤ ((v + t)/2) I t`. Proof:
`s ↦ K s - ½ I t (v + t)² / (v + s)` is nondecreasing on `[t, ∞)`, so
`K t ≤ ½ (v + t) I t + K T` for `T > t`, and `K T ≤ M / (2T) → 0`. -/
theorem le_of_fisher_decay {v t M : ℝ} {K I : ℝ → ℝ} (hv : 0 < v) (ht : 0 < t)
    (hK : ∀ s, 0 < s → HasDerivAt K (-(1 / 2) * I s) s)
    (hdec : ∀ s, t < s → I s ≤ ((v + t) / (v + s)) ^ 2 * I t) (hIt : 0 ≤ I t)
    (hKT : ∀ T, t < T → K T ≤ M / (2 * T)) :
    K t ≤ (v + t) / 2 * I t := by
  set G : ℝ → ℝ := fun s => K s - 1 / 2 * I t * (v + t) ^ 2 * (v + s)⁻¹ with hG
  have hGd : ∀ s, 0 < s → HasDerivAt G
      (-(1 / 2) * I s - 1 / 2 * I t * (v + t) ^ 2 * (-1 / (v + s) ^ 2)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => v + s) 1 s := (hasDerivAt_id s).const_add v
    have h2 := (h1.inv (by linarith : v + s ≠ 0)).const_mul (1 / 2 * I t * (v + t) ^ 2)
    convert (hK s hs).sub h2 using 1
  have hstep : ∀ T, t < T → K t - 1 / 2 * I t * (v + t) ≤ M / (2 * T) := by
    intro T hT
    have hsub : ∀ s ∈ Icc t T, 0 < s := fun s hs => ht.trans_le hs.1
    have hmono : MonotoneOn G (Icc t T) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc t T)
        (fun s hs => (hGd s (hsub s hs)).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Icc]
        exact fun s hs => (hGd s (hsub s (Ioo_subset_Icc_self hs))).differentiableAt
          |>.differentiableWithinAt
      · rw [interior_Icc]
        intro s hs
        rw [(hGd s (hsub s (Ioo_subset_Icc_self hs))).deriv]
        have hdec := hdec s hs.1
        rw [div_pow] at hdec
        have : (v + t) ^ 2 / (v + s) ^ 2 * I t = I t * (v + t) ^ 2 * (1 / (v + s) ^ 2) := by
          ring
        have hI' : I s ≤ I t * (v + t) ^ 2 * (1 / (v + s) ^ 2) := by rw [← this]; exact hdec
        have : -(1 / 2) * I s - 1 / 2 * I t * (v + t) ^ 2 * (-1 / (v + s) ^ 2)
            = 1 / 2 * (I t * (v + t) ^ 2 * (1 / (v + s) ^ 2) - I s) := by ring
        rw [this]
        linarith
    have hGtT := hmono (left_mem_Icc.2 hT.le) (right_mem_Icc.2 hT.le) hT.le
    simp only [hG] at hGtT
    have hvt : 0 < v + t := by linarith
    have e : 1 / 2 * I t * (v + t) ^ 2 * (v + t)⁻¹ = 1 / 2 * I t * (v + t) := by
      field_simp
    have hpos : 0 ≤ 1 / 2 * I t * (v + t) ^ 2 * (v + T)⁻¹ := by
      have : 0 < v + T := by linarith
      positivity
    have := hKT T hT
    linarith
  have hlim : Tendsto (fun T : ℝ => M / (2 * T)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop two_pos)
  have := ge_of_tendsto hlim ((eventually_gt_atTop t).mono hstep)
  linarith

end FormalizeSampling.Gronwall
