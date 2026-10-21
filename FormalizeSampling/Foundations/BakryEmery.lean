module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Probability.CDF
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import FormalizeSampling.Foundations.GaussianFunctionalLSI
public import FormalizeSampling.Foundations.LogSobolevLipschitzMap
public import FormalizeSampling.Foundations.GibbsMeasure

/-!
# Bakry–Émery in dimension one via the monotone (Caffarelli) transport

Status: **Verified** (no named hypothesis).

Notation: `FunctionalLSI μ C` is `Ent_μ(g²) ≤ 2 C ∫ (g')² dμ` for `g ∈ LSIClass`
(`Foundations/LogSobolev.lean`). `densMeasure p = volume.withDensity p` for a Lebesgue density
`p`; `F_p = cdf (densMeasure p)` its distribution function; `quantile b` the inverse of `F_b` on
`(0, 1)`; `transport a b = quantile b ∘ F_a` the monotone transport map. `target f ∝ e^{-f}` and
`gaussPotential α x = α x²/2` are those of `Foundations/GibbsMeasure.lean`
(`target (gaussPotential α) = N(0, 1/α)`).

## Main results

* Distribution functions of positive continuous densities: `hasDerivAt_cdf` (`F_p' = p`),
  `strictMono_cdf`, `cdf_mem_Ioo`, `exists_cdf_eq` (every level in `(0, 1)` is attained).
* The monotone transport (`a, b > 0` continuous probability densities):
  `cdf_transport` (`F_b ∘ T = F_a`), `strictMono_transport`, `surjective_transport`,
  `map_transport` (`T # (a dx) = b dx`), `hasDerivAt_transport` (`T'(x) = a(x) / b(T x)`).
* `le_of_integral_Iic_eq` (**density comparison**): if `a, b > 0` have equal total mass,
  `∫_{(-∞, x]} a = ∫_{(-∞, y]} b`, and `t ↦ log b(y + t) - log a(x + t)` is concave, then
  `a(x) ≤ b(y)`. Elementary proof: otherwise the concave log-ratio is negative at `0`, hence on a
  whole half-line, and the masses of that half-line differ.
* `le_transport`, `abs_deriv_transport_le` (**1D Caffarelli contraction**): under that
  concavity for all `x, y`, `a ≤ b ∘ T`, i.e. `|T'| ≤ 1`; `functionalLSI_of_concave_ratio`:
  then `FunctionalLSI (a dx) C → FunctionalLSI (b dx) C` (`C ≥ 0`), using the Lipschitz
  transport principle `LogSobolevLipschitzMap.functionalLSI_map_of_abs_deriv_le`.
* Strongly convex potentials (`α > 0`, `f - α x²/2` convex on `ℝ`): `continuous_of_convexOn_sub`,
  `integrable_exp_neg_of_convexOn_sub` (`∫ e^{-f} < ∞`), `concave_log_ratio`,
  `exists_contraction_target` (a differentiable `T` with `|T'| ≤ 1` and
  `T # N(0, 1/α) = target f`).
* `functionalLSI_target_of_convexOn_sub` (**Bakry–Émery, 1D**): `FunctionalLSI (target f) (1/α)`;
  variants `functionalLSI_target_of_strongConvexOn` (Mathlib's `StrongConvexOn univ α f`) and
  `functionalLSI_target_of_convexOn_sub_gaussPotential` (`f - gaussPotential α` convex).

## Not proved here

* Multi-dimensional Bakry–Émery for non-separable potentials (the separable case
  `f(x) = ∑ᵢ fᵢ(xᵢ)` on `Fin d → ℝ` is in `BakryEmeryPi`).
* The `Γ₂` / semigroup proof and Caffarelli's theorem beyond dimension one; the transport here is
  the explicit monotone rearrangement `F_b⁻¹ ∘ F_a`, and no regularity of `T` beyond first
  derivatives is established.
* Potentials that are only convex on a subset, or take the value `+∞`: `f : ℝ → ℝ` is finite and
  `f - α x²/2` convex on all of `ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.LogSobolev FormalizeSampling.LogSobolevLipschitzMap
open FormalizeSampling.Proximal FormalizeSampling.ProximalSharp
open FormalizeSampling.GaussianFunctionalLSI

namespace FormalizeSampling.BakryEmery

/-- The probability law with Lebesgue density `p`: `densMeasure p = volume.withDensity p`. -/
noncomputable abbrev densMeasure (p : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (p x)

/-! ### Distribution functions of positive continuous densities -/

section CDF

variable {p : ℝ → ℝ}

/-- Set integrals against `densMeasure p` are Lebesgue set integrals of `p`:
`(densMeasure p).real s = ∫_s p` for measurable `s`, integrable `p ≥ 0`. -/
theorem densMeasure_real (hpi : Integrable p) (hp : ∀ x, 0 ≤ p x) {s : Set ℝ}
    (hs : MeasurableSet s) : (densMeasure p).real s = ∫ t in s, p t := by
  rw [measureReal_def, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hpi.integrableOn (ae_of_all _ fun x => hp x),
    ENNReal.toReal_ofReal (setIntegral_nonneg hs fun x _ => hp x)]

/-- The distribution function of `densMeasure p` is `y ↦ ∫_{(-∞, y]} p`. -/
theorem cdf_densMeasure (hpi : Integrable p) (hp : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (densMeasure p)] (y : ℝ) :
    cdf (densMeasure p) y = ∫ t in Iic y, p t := by
  rw [cdf_eq_real, densMeasure_real hpi hp measurableSet_Iic]

/-- A probability density integrates to one. -/
theorem integral_eq_one (hpi : Integrable p) (hp : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (densMeasure p)] : ∫ t, p t = 1 := by
  have := densMeasure_real hpi hp MeasurableSet.univ
  rw [probReal_univ, setIntegral_univ] at this
  exact this.symm

/-- Increments of the distribution function are interval integrals of the density. -/
theorem cdf_sub_cdf (hpi : Integrable p) (hp : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (densMeasure p)] (y z : ℝ) :
    cdf (densMeasure p) z - cdf (densMeasure p) y = ∫ t in y..z, p t := by
  rw [cdf_densMeasure hpi hp, cdf_densMeasure hpi hp,
    intervalIntegral.integral_Iic_sub_Iic hpi.integrableOn hpi.integrableOn]

/-- For a continuous density, the distribution function has derivative `p y` at `y`. -/
theorem hasDerivAt_cdf (hpc : Continuous p) (hpi : Integrable p) (hp : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (densMeasure p)] (y : ℝ) :
    HasDerivAt (cdf (densMeasure p)) (p y) y := by
  have h : (fun z => cdf (densMeasure p) z) =
      fun z => cdf (densMeasure p) y + ∫ t in y..z, p t := by
    funext z; rw [← cdf_sub_cdf hpi hp]; ring
  rw [show (⇑(cdf (densMeasure p))) = fun z => cdf (densMeasure p) z from rfl, h]
  exact ((hpc.integral_hasStrictDerivAt y y).hasDerivAt).const_add _

/-- For a positive density, the distribution function is strictly increasing. -/
theorem strictMono_cdf (hpi : Integrable p) (hp : ∀ x, 0 < p x)
    [IsProbabilityMeasure (densMeasure p)] : StrictMono (cdf (densMeasure p)) := by
  intro y z hyz
  have h := cdf_sub_cdf hpi (fun x => (hp x).le) y z
  have : 0 < ∫ t in y..z, p t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hpi.intervalIntegrable
      (fun x _ => hp x) hyz
  linarith

/-- For a positive density, the distribution function takes values in `(0, 1)`. -/
theorem cdf_mem_Ioo (hpi : Integrable p) (hp : ∀ x, 0 < p x)
    [IsProbabilityMeasure (densMeasure p)] (y : ℝ) : cdf (densMeasure p) y ∈ Ioo 0 1 :=
  ⟨(cdf_nonneg _ (y - 1)).trans_lt (strictMono_cdf hpi hp (by linarith)),
    (strictMono_cdf hpi hp (by linarith : y < y + 1)).trans_le (cdf_le_one _ _)⟩

/-- For a positive continuous density, every level `q ∈ (0, 1)` is attained by the
distribution function. -/
theorem exists_cdf_eq (hpc : Continuous p) (hpi : Integrable p) (hp : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure (densMeasure p)] {q : ℝ} (hq : q ∈ Ioo 0 1) :
    ∃ y, cdf (densMeasure p) y = q := by
  have hc : Continuous (cdf (densMeasure p)) :=
    continuous_iff_continuousAt.2 fun y => (hasDerivAt_cdf hpc hpi hp y).continuousAt
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (densMeasure p)).eventually
    (gt_mem_nhds hq.1)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (densMeasure p)).eventually
    (lt_mem_nhds hq.2)).exists
  exact mem_range_of_exists_le_of_exists_ge hc ⟨a, ha.le⟩ ⟨b, hb.le⟩

end CDF


/-! ### The monotone transport between two positive continuous densities -/

section Transport

variable {a b : ℝ → ℝ}

open Classical in
/-- The quantile function of `densMeasure b` on `(0, 1)` (an arbitrary value elsewhere):
`quantile b q` is a point `y` with `F_b(y) = q` when such a point exists. -/
noncomputable def quantile (b : ℝ → ℝ) (q : ℝ) : ℝ :=
  if h : ∃ y, cdf (densMeasure b) y = q then h.choose else 0

/-- The monotone transport map `T = F_b⁻¹ ∘ F_a` from `densMeasure a` to `densMeasure b`. -/
noncomputable def transport (a b : ℝ → ℝ) (x : ℝ) : ℝ :=
  quantile b (cdf (densMeasure a) x)

variable (hbc : Continuous b) (hbi : Integrable b) (hb : ∀ x, 0 < b x)
  [IsProbabilityMeasure (densMeasure b)]
include hbc hbi hb

/-- `F_b(quantile b q) = q` for `q ∈ (0, 1)`. -/
theorem cdf_quantile {q : ℝ} (hq : q ∈ Ioo 0 1) :
    cdf (densMeasure b) (quantile b q) = q := by
  have h := exists_cdf_eq hbc hbi (fun x => (hb x).le) hq
  rw [quantile, dite_eq_left h]
  exact h.choose_spec

/-- `quantile b (F_b(y)) = y`. -/
theorem quantile_cdf (y : ℝ) : quantile b (cdf (densMeasure b) y) = y :=
  (strictMono_cdf hbi hb).injective
    (cdf_quantile hbc hbi hb (cdf_mem_Ioo hbi hb y))

/-- The quantile function is continuous at every `q ∈ (0, 1)`. -/
theorem continuousAt_quantile {q : ℝ} (hq : q ∈ Ioo 0 1) : ContinuousAt (quantile b) q := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Ioo 0 1) ?_
    (isOpen_Ioo.mem_nhds hq) ?_
  · intro q₁ h₁ q₂ h₂ h
    rw [← (strictMono_cdf hbi hb).le_iff_le, cdf_quantile hbc hbi hb h₁,
      cdf_quantile hbc hbi hb h₂]
    exact h
  · have : quantile b '' Ioo 0 1 = univ :=
      eq_univ_of_forall fun y => ⟨_, cdf_mem_Ioo hbi hb y, quantile_cdf hbc hbi hb y⟩
    rw [this]
    exact univ_mem

/-- The quantile function has derivative `1 / b(quantile b q)` at `q ∈ (0, 1)`. -/
theorem hasDerivAt_quantile {q : ℝ} (hq : q ∈ Ioo 0 1) :
    HasDerivAt (quantile b) (b (quantile b q))⁻¹ q :=
  HasDerivAt.of_local_left_inverse (continuousAt_quantile hbc hbi hb hq)
    (hasDerivAt_cdf hbc hbi (fun x => (hb x).le) _) (hb _).ne'
    (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hq) fun _ h => cdf_quantile hbc hbi hb h)

variable (hai : Integrable a) (ha : ∀ x, 0 < a x) [IsProbabilityMeasure (densMeasure a)]
include hai ha

/-- The transport map matches distribution functions: `F_b(T x) = F_a(x)`. -/
theorem cdf_transport (x : ℝ) :
    cdf (densMeasure b) (transport a b x) = cdf (densMeasure a) x :=
  cdf_quantile hbc hbi hb (cdf_mem_Ioo hai ha x)

/-- The transport map is strictly increasing. -/
theorem strictMono_transport : StrictMono (transport a b) := by
  intro x y h
  rw [← (strictMono_cdf hbi hb).lt_iff_lt, cdf_transport hbc hbi hb hai ha,
    cdf_transport hbc hbi hb hai ha]
  exact strictMono_cdf hai ha h

/-- The transport map is onto. -/
theorem surjective_transport (hac : Continuous a) : Function.Surjective (transport a b) := by
  intro y
  obtain ⟨x, hx⟩ := exists_cdf_eq hac hai (fun x => (ha x).le) (cdf_mem_Ioo hbi hb y)
  refine ⟨x, (strictMono_cdf hbi hb).injective ?_⟩
  rw [cdf_transport hbc hbi hb hai ha, hx]

/-- The transport map pushes `densMeasure a` forward to `densMeasure b`. -/
theorem map_transport (hac : Continuous a) :
    (densMeasure a).map (transport a b) = densMeasure b := by
  have hT := strictMono_transport hbc hbi hb hai ha
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply hT.monotone.measurable measurableSet_Iic]
  obtain ⟨x₀, rfl⟩ := surjective_transport hbc hbi hb hai ha hac y
  have : transport a b ⁻¹' Iic (transport a b x₀) = Iic x₀ := by
    ext x; simp [hT.le_iff_le]
  rw [this, ← ofReal_cdf, ← ofReal_cdf, cdf_transport hbc hbi hb hai ha]

/-- The transport map is differentiable with `T'(x) = a(x) / b(T x)`. -/
theorem hasDerivAt_transport (hac : Continuous a) (x : ℝ) :
    HasDerivAt (transport a b) (a x / b (transport a b x)) x := by
  have h := (hasDerivAt_quantile hbc hbi hb (cdf_mem_Ioo hai ha x)).comp x
    (hasDerivAt_cdf hac hai (fun x => (ha x).le) x)
  rw [div_eq_inv_mul]
  exact h

end Transport

/-! ### The density comparison along the transport -/

section Comparison

variable {a b : ℝ → ℝ}

/-- Translation invariance of Lebesgue set integrals:
`∫_{(c + ·)⁻¹ S} g(c + t) dt = ∫_S g`. -/
theorem setIntegral_preimage_add (c : ℝ) (g : ℝ → ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫ t in (fun t => c + t) ⁻¹' S, g (c + t) = ∫ t in S, g t := by
  rw [← integral_indicator (measurable_const_add c hS), ← integral_indicator hS,
    ← integral_add_left_eq_self (S.indicator g) c]
  congr 1

/-- A set integral of a function that is positive on a set of positive Lebesgue measure is
positive. -/
theorem setIntegral_pos_of_pos {g : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hvol : volume S ≠ 0) (hg : IntegrableOn g S) (hpos : ∀ t ∈ S, 0 < g t) :
    0 < ∫ t in S, g t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem hS fun t ht => (hpos t ht).le) hg]
  refine lt_of_lt_of_le (pos_iff_ne_zero.2 hvol) (measure_mono fun t ht => ⟨?_, ht⟩)
  exact (hpos t ht).ne'

/-- **Density comparison for equal quantile levels.** Let `a, b > 0` be integrable with
`∫ a = ∫ b`, and let `x, y` have equal lower masses `∫_{(-∞, x]} a = ∫_{(-∞, y]} b`. If
`t ↦ log b(y + t) - log a(x + t)` is concave, then `a(x) ≤ b(y)`.

Proof: otherwise the concave function is negative at `0`, hence negative on a whole half-line
`t > 0` or `t ≤ 0`; there `b(y + ·) < a(x + ·)`, so the corresponding masses differ. -/
theorem le_of_integral_Iic_eq (hai : Integrable a) (hbi : Integrable b) (ha : ∀ x, 0 < a x)
    (hb : ∀ x, 0 < b x) (hab : ∫ t, a t = ∫ t, b t) {x y : ℝ}
    (hxy : ∫ t in Iic x, a t = ∫ t in Iic y, b t)
    (hconc : ConcaveOn ℝ univ fun t => Real.log (b (y + t)) - Real.log (a (x + t))) :
    a x ≤ b y := by
  by_contra hlt
  push Not at hlt
  have hlt' : ∀ t, Real.log (b (y + t)) - Real.log (a (x + t)) < 0 ↔ b (y + t) < a (x + t) :=
    fun t => by rw [sub_neg]; exact Real.log_lt_log_iff (hb _) (ha _)
  have h0 : Real.log (b (y + 0)) - Real.log (a (x + 0)) < 0 :=
    (hlt' 0).2 (by simpa using hlt)
  have hcase : (∀ t, 0 < t → b (y + t) < a (x + t)) ∨ (∀ t, t < 0 → b (y + t) < a (x + t)) := by
    by_contra hc
    push Not at hc
    obtain ⟨⟨t, ht, hφt⟩, ⟨s, hs, hφs⟩⟩ := hc
    have hm := hconc.min_le_of_mem_segment (mem_univ s) (mem_univ t)
      (by rw [segment_eq_Icc (by linarith)]; exact ⟨hs.le, ht.le⟩ : (0 : ℝ) ∈ segment ℝ s t)
    have h1 := (not_congr (hlt' t)).2 (not_lt.2 hφt)
    have h2 := (not_congr (hlt' s)).2 (not_lt.2 hφs)
    push Not at h1 h2
    have : 0 ≤ min (Real.log (b (y + s)) - Real.log (a (x + s)))
        (Real.log (b (y + t)) - Real.log (a (x + t))) := le_min h2 h1
    linarith
  have hgi : Integrable fun t => a (x + t) - b (y + t) :=
    (hai.comp_add_left x).sub (hbi.comp_add_left y)
  have hpre : ∀ c d : ℝ, (fun t => c + t) ⁻¹' Iic (c + d) = Iic d := fun c d => by
    ext t; simp
  have hpre' : ∀ c d : ℝ, (fun t => c + t) ⁻¹' Ioi (c + d) = Ioi d := fun c d => by
    ext t; simp
  rcases hcase with hR | hL
  · have hpos := setIntegral_pos_of_pos measurableSet_Ioi (by simp) hgi.integrableOn
      fun t ht => sub_pos.2 (hR t ht)
    rw [integral_sub (hai.comp_add_left x).integrableOn (hbi.comp_add_left y).integrableOn] at hpos
    have hx := setIntegral_preimage_add x a (measurableSet_Ioi (a := x + 0))
    have hy := setIntegral_preimage_add y b (measurableSet_Ioi (a := y + 0))
    rw [hpre'] at hx hy
    rw [hx, hy, add_zero, add_zero] at hpos
    have hca := integral_add_compl (measurableSet_Iic (a := x)) hai
    have hcb := integral_add_compl (measurableSet_Iic (a := y)) hbi
    rw [compl_Iic] at hca hcb
    linarith
  · have hpos := setIntegral_pos_of_pos measurableSet_Iic (by simp) hgi.integrableOn
      fun t ht => by
        rcases (mem_Iic.1 ht).lt_or_eq with h | rfl
        · exact sub_pos.2 (hL t h)
        · exact sub_pos.2 ((hlt' 0).1 h0)
    rw [integral_sub (hai.comp_add_left x).integrableOn (hbi.comp_add_left y).integrableOn] at hpos
    have hx := setIntegral_preimage_add x a (measurableSet_Iic (a := x + 0))
    have hy := setIntegral_preimage_add y b (measurableSet_Iic (a := y + 0))
    rw [hpre] at hx hy
    rw [hx, hy, add_zero, add_zero] at hpos
    linarith

end Comparison

/-! ### The contraction theorem and its LSI consequence -/

section Contraction

variable {a b : ℝ → ℝ} (hac : Continuous a) (hbc : Continuous b) (ha : ∀ x, 0 < a x)
  (hb : ∀ x, 0 < b x) (hai : Integrable a) (hbi : Integrable b)
  [IsProbabilityMeasure (densMeasure a)] [IsProbabilityMeasure (densMeasure b)]
  (hconc : ∀ x y, ConcaveOn ℝ univ fun t => Real.log (b (y + t)) - Real.log (a (x + t)))
include hac hbc ha hb hai hbi hconc

omit hac in
/-- **1D Caffarelli contraction.** If `log(b(y + ·)/a(x + ·))` is concave for all `x, y`
(e.g. `b` is a log-concave perturbation of the Gaussian density `a`), then the monotone
transport `T = F_b⁻¹ ∘ F_a` satisfies `a(x) ≤ b(T x)`, i.e. `0 < T' ≤ 1`. -/
theorem le_transport : ∀ x, a x ≤ b (transport a b x) := by
  intro x
  refine le_of_integral_Iic_eq hai hbi ha hb ?_ ?_ (hconc x _)
  · rw [integral_eq_one hai (fun x => (ha x).le), integral_eq_one hbi (fun x => (hb x).le)]
  · rw [← cdf_densMeasure hai (fun x => (ha x).le), ← cdf_densMeasure hbi (fun x => (hb x).le),
      cdf_transport hbc hbi hb hai ha]

/-- Under the hypotheses of `le_transport`, the transport map is differentiable with
`|T'| ≤ 1`. -/
theorem abs_deriv_transport_le (x : ℝ) : |deriv (transport a b) x| ≤ 1 := by
  rw [(hasDerivAt_transport hbc hbi hb hai ha hac x).deriv,
    abs_of_nonneg (div_nonneg (ha x).le (hb _).le), div_le_one (hb _)]
  exact le_transport hbc ha hb hai hbi hconc x

/-- **Transport of the LSI along the contraction.** Under the hypotheses of `le_transport`,
`FunctionalLSI (densMeasure a) C` with `C ≥ 0` implies `FunctionalLSI (densMeasure b) C`. -/
theorem functionalLSI_of_concave_ratio {C : ℝ} (hC : 0 ≤ C)
    (hLSI : FunctionalLSI (densMeasure a) C) : FunctionalLSI (densMeasure b) C := by
  have h := functionalLSI_map_of_abs_deriv_le hLSI hC
    (fun x => (hasDerivAt_transport hbc hbi hb hai ha hac x).differentiableAt)
    (abs_deriv_transport_le hac hbc ha hb hai hbi hconc)
  rwa [map_transport hbc hbi hb hai ha hac, one_pow, one_mul] at h

end Contraction

/-! ### Strongly convex potentials -/

section StronglyConvex

variable {α : ℝ} {f : ℝ → ℝ}

/-- A convex function on `ℝ` has the lower bound `h(z) ≥ h(0) - c |z|` with
`c = |h(1) - h(0)| + |h(-1) - h(0)|`. -/
theorem convexOn_lower_bound {h : ℝ → ℝ} (hh : ConvexOn ℝ univ h) (z : ℝ) :
    h 0 - (|h 1 - h 0| + |h (-1) - h 0|) * |z| ≤ h z := by
  have hA := abs_nonneg (h 1 - h 0)
  have hB := abs_nonneg (h (-1) - h 0)
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · set w := 1 / (1 - z) with hw
    have hw0 : 0 < w := by rw [hw]; exact one_div_pos.2 (by linarith)
    have hw1 : (1 - z) * w = 1 := by
      rw [hw, mul_one_div, div_self (by linarith : (1 : ℝ) - z ≠ 0)]
    have hc := hh.2 (mem_univ 1) (mem_univ z)
      (show (0 : ℝ) ≤ -z * w from mul_nonneg (by linarith) hw0.le) hw0.le
      (show -z * w + w = 1 by linear_combination hw1)
    simp only [smul_eq_mul] at hc
    rw [show -z * w * 1 + w * z = 0 by ring] at hc
    have key := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 1 - z)
    have e : (1 - z) * (-z * w * h 1 + w * h z) = -z * h 1 + h z := by
      linear_combination (-z * h 1 + h z) * hw1
    rw [e] at key
    rw [abs_of_neg hz]
    nlinarith [le_abs_self (h 1 - h 0), neg_abs_le (h 1 - h 0)]
  · simp
  · set w := 1 / (1 + z) with hw
    have hw0 : 0 < w := by rw [hw]; exact one_div_pos.2 (by linarith)
    have hw1 : (1 + z) * w = 1 := by
      rw [hw, mul_one_div, div_self (by linarith : (1 : ℝ) + z ≠ 0)]
    have hc := hh.2 (mem_univ (-1)) (mem_univ z)
      (show (0 : ℝ) ≤ z * w from mul_nonneg hz.le hw0.le) hw0.le
      (show z * w + w = 1 by linear_combination hw1)
    simp only [smul_eq_mul] at hc
    rw [show z * w * -1 + w * z = 0 by ring] at hc
    have key := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 1 + z)
    have e : (1 + z) * (z * w * h (-1) + w * h z) = z * h (-1) + h z := by
      linear_combination (z * h (-1) + h z) * hw1
    rw [e] at key
    rw [abs_of_pos hz]
    nlinarith [le_abs_self (h (-1) - h 0), neg_abs_le (h (-1) - h 0)]

/-- `log π(z) = -f(z) - log Z` for the target density with positive normaliser. -/
theorem log_targetDensity {g : ℝ → ℝ} (hZ : 0 < targetNormalizer g) (z : ℝ) :
    Real.log (targetDensity g z) = -g z - Real.log (targetNormalizer g) := by
  rw [targetDensity, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

variable (hα : 0 < α) (hf : ConvexOn ℝ univ fun x => f x - α / 2 * x ^ 2)
include hα hf

omit hα in
/-- An `α`-strongly convex potential (in the form `f - α x²/2` convex) is continuous. -/
theorem continuous_of_convexOn_sub : Continuous f := by
  have h := continuousOn_univ.1 (hf.continuousOn isOpen_univ)
  have : f = fun x => (f x - α / 2 * x ^ 2) + α / 2 * x ^ 2 := by funext x; ring
  rw [this]
  fun_prop

/-- For an `α`-strongly convex potential, `e^{-f}` is Lebesgue integrable. -/
theorem integrable_exp_neg_of_convexOn_sub : Integrable fun x => Real.exp (-f x) := by
  set h := fun x => f x - α / 2 * x ^ 2 with hh
  set c := |h 1 - h 0| + |h (-1) - h 0|
  have hc : 0 ≤ c := by positivity
  refine Integrable.mono' (((integrable_exp_neg_mul_sq (by positivity : 0 < α / 4)).const_mul
    (Real.exp (-h 0 + c ^ 2 / α)))) ((continuous_of_convexOn_sub hf).neg.rexp
      |>.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have hlb : h 0 - c * |z| ≤ h z := convexOn_lower_bound hf z
  have hq : c * |z| - α / 4 * z ^ 2 ≤ c ^ 2 / α := by
    rw [le_div_iff₀ hα, ← sq_abs z]
    nlinarith [sq_nonneg (α / 2 * |z| - c)]
  have hz : h z = f z - α / 2 * z ^ 2 := rfl
  linarith

/-- For an `α`-strongly convex `f`, the log-ratio of the target density of `f` to the Gaussian
density `N(0, 1/α)` is concave along every pair of translates. -/
theorem concave_log_ratio (x y : ℝ) :
    ConcaveOn ℝ univ fun t => Real.log (targetDensity f (y + t)) -
      Real.log (targetDensity (gaussPotential α) (x + t)) := by
  have hZf := targetNormalizer_pos (integrable_exp_neg_of_convexOn_sub hα hf)
  have hZ0 := targetNormalizer_pos (integrable_exp_neg_gaussPotential hα)
  refine ⟨convex_univ, fun u _ v _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul, log_targetDensity hZf, log_targetDensity hZ0, gaussPotential]
  have hc := hf.2 (mem_univ (y + u)) (mem_univ (y + v)) hp hq hpq
  simp only [smul_eq_mul] at hc
  rw [show p * (y + u) + q * (y + v) = y + (p * u + q * v) by linear_combination y * hpq] at hc
  obtain rfl : q = 1 - p := by linarith
  linear_combination hc

/-- **Caffarelli contraction onto a strongly log-concave target (1D).** If `α > 0` and
`f - α x²/2` is convex, there is a differentiable map `T : ℝ → ℝ` with `|T'| ≤ 1` pushing
`target (gaussPotential α) = N(0, 1/α)` forward to `target f` (the monotone transport). -/
theorem exists_contraction_target : ∃ T : ℝ → ℝ, Differentiable ℝ T ∧
    (∀ x, |deriv T x| ≤ 1) ∧ (target (gaussPotential α)).map T = target f := by
  have hint := integrable_exp_neg_of_convexOn_sub hα hf
  have hint0 := integrable_exp_neg_gaussPotential hα
  have hZf := targetNormalizer_pos hint
  have hZ0 := targetNormalizer_pos hint0
  have : IsProbabilityMeasure (densMeasure (targetDensity f)) := isProbabilityMeasure_target hint
  have : IsProbabilityMeasure (densMeasure (targetDensity (gaussPotential α))) :=
    isProbabilityMeasure_target hint0
  have hcont : ∀ g : ℝ → ℝ, Continuous g → Continuous (targetDensity g) := fun g hg => by
    unfold targetDensity; fun_prop
  have hpos : ∀ g : ℝ → ℝ, 0 < targetNormalizer g → ∀ x, 0 < targetDensity g x :=
    fun g hZ x => div_pos (Real.exp_pos _) hZ
  have hac : Continuous (targetDensity (gaussPotential α)) :=
    hcont _ (by unfold gaussPotential; fun_prop)
  have hbc := hcont _ (continuous_of_convexOn_sub hf)
  have hai : Integrable (targetDensity (gaussPotential α)) := hint0.div_const _
  have hbi : Integrable (targetDensity f) := hint.div_const _
  exact ⟨transport (targetDensity (gaussPotential α)) (targetDensity f),
    fun x => (hasDerivAt_transport hbc hbi (hpos _ hZf) hai (hpos _ hZ0) hac x).differentiableAt,
    abs_deriv_transport_le hac hbc (hpos _ hZ0) (hpos _ hZf) hai hbi (concave_log_ratio hα hf),
    map_transport hbc hbi (hpos _ hZf) hai (hpos _ hZ0) hac⟩

/-- **Bakry–Émery in dimension one.** If `α > 0` and `f - α x²/2` is convex on `ℝ`, then the
target `π ∝ e^{-f}` satisfies the functional log-Sobolev inequality with constant `1/α`.

Proof: the monotone transport from `N(0, 1/α)` (Gross's LSI with constant `1/α`) to `π` is
`1`-Lipschitz (`le_transport`), and the LSI is preserved by `1`-Lipschitz push-forward. -/
theorem functionalLSI_target_of_convexOn_sub : FunctionalLSI (target f) (1 / α) := by
  obtain ⟨T, hTd, hTK, hmap⟩ := exists_contraction_target hα hf
  have := isProbabilityMeasure_target (integrable_exp_neg_gaussPotential hα)
  have hLSI : FunctionalLSI (target (gaussPotential α)) (1 / α) := by
    rw [target_gaussPotential hα, one_div]
    exact functionalLSI_gaussianReal α⁻¹ (inv_pos.2 hα)
  have h := functionalLSI_map_of_abs_deriv_le hLSI (one_div_pos.2 hα).le hTd hTK
  rwa [hmap, one_pow, one_mul] at h

end StronglyConvex

/-- **Bakry–Émery in dimension one, `StrongConvexOn` form.** If `f : ℝ → ℝ` is `α`-strongly
convex on `ℝ` (`α > 0`), then `FunctionalLSI (target f) (1 / α)`. -/
theorem functionalLSI_target_of_strongConvexOn {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ}
    (hf : StrongConvexOn univ α f) : FunctionalLSI (target f) (1 / α) := by
  refine functionalLSI_target_of_convexOn_sub hα ?_
  have h := strongConvexOn_iff_convex.1 hf
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- **Bakry–Émery in dimension one, `gaussPotential` form.** If `α > 0` and
`f - gaussPotential α` (i.e. `f(x) - α x²/2`) is convex on `ℝ`, then
`FunctionalLSI (target f) (1 / α)`. This is the hypothesis form of `ProximalGeneralLSI`. -/
theorem functionalLSI_target_of_convexOn_sub_gaussPotential {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ fun x => f x - gaussPotential α x) :
    FunctionalLSI (target f) (1 / α) := by
  refine functionalLSI_target_of_convexOn_sub hα ?_
  convert hf using 2 with x
  unfold gaussPotential
  ring

end FormalizeSampling.BakryEmery
