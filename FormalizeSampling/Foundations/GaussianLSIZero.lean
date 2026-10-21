module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import FormalizeSampling.Foundations.GaussianLSI
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The Gaussian log-Sobolev inequality at time zero

Status: **Verified** under explicit hypotheses: a positive probability density `p` on `ℝ`,
differentiable everywhere with derivative `p'` (no continuity of `p'`), with finite second moment
and finite relative Fisher information (`klDiv_le_fisher0`; the de Bruijn hypotheses
`HeatFlowRegular ρ π (Ioi 0)` are discharged by `Foundations/HeatFlowRegularityPerturbed.lean`).
`KL(ρ‖π) < ∞` is a conclusion, not a hypothesis.

This removes the restriction of `Foundations/GaussianLSI.lean` (where the Gaussian LSI is proved
only for heat-smoothed laws `ρ_t`, `t > 0`) for laws with a differentiable positive density.

Notation: `ρ = volume.withDensity p`, `π = N(0, v) = gaussianReal 0 v` (`v > 0`),
`φ_a = heatDensity a`, `p_t = heatFlowDensity ρ t = p * φ_t`,
`G_0 = relFlux0 p p' v = p' + x p / v` and `G_t = gaussRelFlux ρ v t = p_t' + y p_t / (v + t)`.

## Main results

* `integral_mul_heatDensityD1`: `p_t' = φ_t * p'` (integration by parts; the boundary terms are
  handled by `integral_eq_zero_of_hasDerivAt_of_integrable`).
* `gaussRelFlux_eq_integral`: `G_t = (v/(v+t)) φ_t * G_0`.
* `heatFisher_le_fisher0` (Fisher decay from time zero):
  `I(ρ_t‖N(0, v + t)) ≤ (v/(v+t))² ∫ G_0² / p`.
* `tendsto_mul_heatDensity_one`: `p_t(y) → p(y)` as `t → 0⁺` (Gaussian approximate identity).
* `klDiv_withDensity_eq_lintegral`: `KL(p‖q) = ∫⁻ q klFun(p/q)` for density laws.
* `klDiv_le_fisher0` (**Gaussian LSI at time zero**; also under the name
  `klDiv_le_fisher0_of_moment`): `KL(ρ‖N(0, v)) ≤ (v/2) ∫ p (p'/p + x/v)² dx`, via the LSI
  along the heat flow at `t > 0` and Fatou's lemma as `t → 0⁺` (lower semicontinuity of KL).

## Not proved here

* Densities that are not differentiable everywhere or not everywhere positive (e.g. compactly
  supported `p`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction
open FormalizeSampling.GaussianLSI

namespace FormalizeSampling.GaussianLSIZero

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_of_isProbabilityMeasure)

/-! ### Laws with a density -/

/-- The time-`0` relative score flux of a density `p` (with derivative `p'`) against
`N(0, v)`: `relFlux0 p p' v x = p'(x) + x p(x) / v = p(x) ∂ₓ log(p(x) / φ_v(x))`. -/
noncomputable def relFlux0 (p p' : ℝ → ℝ) (v x : ℝ) : ℝ := p' x + x / v * p x

section Regular

variable {p p' : ℝ → ℝ} {v : ℝ}

/-- `|G| ≤ (p + G² / p) / 2` for `p > 0` (AM–GM). -/
theorem abs_le_add_sq_div {a g : ℝ} (ha : 0 < a) : |g| ≤ (a + g ^ 2 / a) / 2 := by
  have e : g ^ 2 / a * a = g ^ 2 := div_mul_cancel₀ _ ha.ne'
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (g - a), sq_nonneg (g + a), sq_nonneg (g ^ 2 / a)]

/-- If `q > 0` and `q` and `g² / q` are integrable, then the (measurable) `g` is
integrable. -/
theorem integrable_of_sq_div {α : Type*} [MeasurableSpace α] {μ : Measure α} {q g : α → ℝ}
    (hp : ∀ x, 0 < q x) (hpi : Integrable q μ) (hg : AEStronglyMeasurable g μ)
    (hF : Integrable (fun x => g x ^ 2 / q x) μ) : Integrable g μ := by
  refine ((hpi.add hF).div_const 2).mono' hg (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le_add_sq_div (hp x)

/-- With `p ≥ 0` integrable and `x² p` integrable, `x ↦ x p(x)` is integrable. -/
theorem integrable_mul_self {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (hqi : Integrable q)
    (hqm : Continuous q) (hmom : Integrable fun x => x ^ 2 * q x) :
    Integrable fun x => x * q x := by
  refine (hqi.add hmom).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq x)]
  have : |x| ≤ 1 + x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right this (hq x)]

/-- An everywhere derivative is measurable: if `HasDerivAt p (p' x) x` for every `x`, then `p'`
is measurable (it equals `deriv p`). -/
theorem measurable_of_hasDerivAt (hd : ∀ x, HasDerivAt p (p' x) x) : Measurable p' := by
  have : p' = deriv p := funext fun x => (hd x).deriv.symm
  rw [this]
  exact measurable_deriv p

end Regular

/-! ### The heat flow of a law with a differentiable density -/

section HeatFlow

variable {p p' : ℝ → ℝ}

/-- For a measurable density `p ≥ 0` and every `t, y`, the heat-flow density of
`ρ = volume.withDensity p` is `p_t(y) = ∫ p(x) φ_t(y - x) dx`. -/
theorem heatFlowDensity_withDensity (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (t y : ℝ) :
    heatFlowDensity (volume.withDensity fun x => ENNReal.ofReal (p x)) t y
      = ∫ x, p x * heatDensity t (y - x) :=
  integral_withDensity_ofReal hpm hp0 _

/-- For a measurable density `p ≥ 0` and every `t, y`,
`p_t'(y) = ∫ p(x) φ_t'(y - x) dx` (`heatFlowD1`). -/
theorem heatFlowD1_withDensity (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (t y : ℝ) :
    heatFlowD1 (volume.withDensity fun x => ENNReal.ofReal (p x)) t y
      = ∫ x, p x * heatDensityD1 t (y - x) :=
  integral_withDensity_ofReal hpm hp0 _

/-- **Integration by parts at time zero.** If `p` is integrable, differentiable with integrable
derivative `p'`, then for `t > 0` and every `y`:
`∫ p(x) φ_t'(y - x) dx = ∫ φ_t(y - x) p'(x) dx`, i.e. `p_t' = φ_t * p'`. -/
theorem integral_mul_heatDensityD1 (hpi : Integrable p) (hd : ∀ x, HasDerivAt p (p' x) x)
    (hp'i : Integrable p') {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∫ x, p x * heatDensityD1 t (y - x) = ∫ x, heatDensity t (y - x) * p' x := by
  have hderiv : ∀ x, HasDerivAt (fun x => heatDensity t (y - x) * p x)
      (-heatDensityD1 t (y - x) * p x + heatDensity t (y - x) * p' x) x := by
    intro x
    have h1 := (hasDerivAt_heatDensity_x t (y - x)).comp x ((hasDerivAt_id x).const_sub y)
    have := h1.mul (hd x)
    convert this using 1
    · simp only [Function.comp_def]; rfl
    · simp only [Function.comp_apply]; ring
  have hA : Integrable fun x => -heatDensityD1 t (y - x) * p x :=
    hpi.bdd_mul (c := (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹)
      (((continuous_heatDensityD1 ht).comp (by fun_prop)).neg.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_neg]; exact abs_heatDensityD1_le ht _)
  have hB : Integrable fun x => heatDensity t (y - x) * p' x :=
    hp'i.bdd_mul (c := (Real.sqrt (2 * Real.pi * t))⁻¹)
      ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _)
  have hf : Integrable fun x => heatDensity t (y - x) * p x :=
    hpi.bdd_mul (c := (Real.sqrt (2 * Real.pi * t))⁻¹)
      ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hA.add hB) hf
  rw [integral_add hA hB] at h0
  have : ∫ x, -heatDensityD1 t (y - x) * p x = -∫ x, p x * heatDensityD1 t (y - x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  linarith

/-- **Relative score of the smoothed law from the time-`0` flux.** Let `p > 0` be a probability
density, differentiable with integrable derivative `p'`, and
`ρ = volume.withDensity p`. For `v, t > 0` and every `y`, with `G_0 = relFlux0 p p' v`:
`G_t(y) = (v / (v + t)) ∫ φ_t(y - x) G_0(x) dx` (`G_t = gaussRelFlux ρ v t`). -/
theorem gaussRelFlux_eq_integral (hp : ∀ x, 0 < p x) (hpi : Integrable p)
    (hd : ∀ x, HasDerivAt p (p' x) x) (hp'i : Integrable p') {v t : ℝ} (hv : 0 < v)
    (ht : 0 < t) (y : ℝ) :
    gaussRelFlux (volume.withDensity fun x => ENNReal.ofReal (p x)) v t y
      = v / (v + t) * ∫ x, heatDensity t (y - x) * relFlux0 p p' v x := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hB : Integrable fun x => heatDensity t (y - x) * p' x :=
    hp'i.bdd_mul (c := (Real.sqrt (2 * Real.pi * t))⁻¹)
      ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _)
  have hI2 : Integrable fun x => p x * heatDensity t (y - x) :=
    hpi.mul_bdd ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (heatDensity_pos ht _).le]; exact heatDensity_le ht _)
  have hI3 : Integrable fun x => p x * heatDensityD1 t (y - x) :=
    hpi.mul_bdd ((continuous_heatDensityD1 ht).comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_heatDensityD1_le ht _)
  have hpt : ∀ x, heatDensity t (y - x) * relFlux0 p p' v x
      = heatDensity t (y - x) * p' x + (1 / v) *
        (y * (p x * heatDensity t (y - x)) + t * (p x * heatDensityD1 t (y - x))) := by
    intro x
    unfold relFlux0 heatDensityD1
    field_simp
    ring
  have hI23 : Integrable fun x => 1 / v *
      (y * (p x * heatDensity t (y - x)) + t * (p x * heatDensityD1 t (y - x))) :=
    ((hI2.const_mul y).add (hI3.const_mul t)).const_mul _
  simp_rw [hpt]
  rw [integral_add hB hI23, integral_const_mul, integral_add (hI2.const_mul y) (hI3.const_mul t),
    integral_const_mul, integral_const_mul, ← integral_mul_heatDensityD1 hpi hd hp'i ht y]
  unfold gaussRelFlux
  rw [heatFlowD1_withDensity hpc.measurable hp0, heatFlowDensity_withDensity hpc.measurable hp0]
  have : v + t ≠ 0 := by linarith
  field_simp
  ring

end HeatFlow

/-! ### Fisher information decay from time zero -/

section Fisher

variable {p p' : ℝ → ℝ}

/-- **Fisher information decay from time zero (Gaussian target).** Let `p > 0` be a probability
density on `ℝ` (`ρ = volume.withDensity p`), differentiable everywhere with integrable derivative
`p'` (`p'` is automatically measurable, `measurable_of_hasDerivAt`; it need not be continuous),
and let `v, t > 0`. If the time-`0` relative Fisher integrand
`G_0² / p = p (p'/p + x/v)²` (`G_0 = relFlux0 p p' v`) is integrable, then
`I(ρ_t‖N(0, v + t)) ≤ (v / (v + t))² · ∫ G_0² / p` (`heatFisher`). -/
theorem heatFisher_le_fisher0 (hp : ∀ x, 0 < p x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    (hd : ∀ x, HasDerivAt p (p' x) x) (hp'i : Integrable p')
    {v t : ℝ} (hv : 0 < v) (ht : 0 < t)
    (hint : Integrable fun x => relFlux0 p p' v x ^ 2 / p x) :
    heatFisher (volume.withDensity fun x => ENNReal.ofReal (p x)) (gaussianReal 0 v.toNNReal) t
      ≤ (v / (v + t)) ^ 2 * ∫ x, relFlux0 p p' v x ^ 2 / p x := by
  set ρ := volume.withDensity fun x => ENNReal.ofReal (p x) with hρ
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hpi : Integrable p := integrable_of_isProbabilityMeasure hpc.measurable hp0
  set G : ℝ → ℝ := relFlux0 p p' v with hG
  have hGc : Measurable G :=
    (measurable_of_hasDerivAt hd).add ((measurable_id.div_const v).mul hpc.measurable)
  set F : ℝ → ℝ := fun z => G z ^ 2 / p z with hF
  set c := v / (v + t) with hc
  have hF0 : ∀ z, 0 ≤ F z := fun z => div_nonneg (sq_nonneg _) (hp0 z)
  have hFc : Measurable F := (hGc.pow_const 2).div hpc.measurable
  have hPt : ∀ y, 0 < heatFlowDensity ρ t y := heatFlowDensity_pos ρ ht
  -- pointwise bound
  have hpt : ∀ y, gaussRelFlux ρ v t y ^ 2 / heatFlowDensity ρ t y
      ≤ c ^ 2 * ∫ z, heatDensity t (y - z) * F z := by
    intro y
    have hk : ∀ z, 0 ≤ heatDensity t (y - z) := fun z => (heatDensity_pos ht _).le
    have h1 : Integrable fun z => heatDensity t (y - z) * p z :=
      hpi.bdd_mul (c := (Real.sqrt (2 * Real.pi * t))⁻¹)
        ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (hk z)]; exact heatDensity_le ht _)
    have h3 : Integrable fun z => heatDensity t (y - z) * F z :=
      hint.bdd_mul (c := (Real.sqrt (2 * Real.pi * t))⁻¹)
        ((continuous_heatDensity t).comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (hk z)]; exact heatDensity_le ht _)
    have h13 : Integrable fun z => (heatDensity t (y - z) * p z
        + heatDensity t (y - z) * F z) / 2 := (h1.add h3).div_const 2
    have h2 : Integrable fun z => heatDensity t (y - z) * G z := by
      refine h13.mono
        (((continuous_heatDensity t).comp (by fun_prop)).measurable.mul hGc).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      have hamgm : |G z| ≤ (p z + F z) / 2 := abs_le_add_sq_div (hp z)
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (div_nonneg (add_nonneg
        (mul_nonneg (hk z) (hp0 z)) (mul_nonneg (hk z) (hF0 z))) two_pos.le), abs_mul,
        abs_of_nonneg (hk z)]
      calc heatDensity t (y - z) * |G z|
          ≤ heatDensity t (y - z) * ((p z + F z) / 2) :=
            mul_le_mul_of_nonneg_left hamgm (hk z)
        _ = _ := by ring
    have hC : ∫ z, heatDensity t (y - z) * p z = heatFlowDensity ρ t y := by
      rw [hρ, heatFlowDensity_withDensity hpc.measurable hp0]; congr 1; funext z; ring
    have hCS := sq_integral_mul_le hk hp h1 h2 h3 (by rw [hC]; exact hPt y)
    rw [hC] at hCS
    have hca : c * ((v + t) / v) = 1 := by
      rw [hc]; field_simp
    have hGt : gaussRelFlux ρ v t y = c * ∫ z, heatDensity t (y - z) * G z :=
      gaussRelFlux_eq_integral hp hpi hd hp'i hv ht y
    rw [div_le_iff₀ (hPt y), hGt, mul_pow]
    calc c ^ 2 * (∫ z, heatDensity t (y - z) * G z) ^ 2
        ≤ c ^ 2 * (heatFlowDensity ρ t y * ∫ z, heatDensity t (y - z) * F z) :=
          mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = _ := by ring
  -- integrate in `y`
  have hHm : AEStronglyMeasurable (fun q : ℝ × ℝ => heatDensity t (q.1 - q.2) * F q.2)
      (volume.prod volume) :=
    (((continuous_heatDensity t).comp (continuous_fst.sub continuous_snd)).measurable.mul
      (hFc.comp measurable_snd)).aestronglyMeasurable
  have hH : Integrable (fun q : ℝ × ℝ => heatDensity t (q.1 - q.2) * F q.2)
      (volume.prod volume) := by
    refine (integrable_prod_iff' hHm).2 ⟨Eventually.of_forall fun z => by
      simpa only using (integrable_heatDensity_sub ht z).mul_const (F z), ?_⟩
    refine hint.congr (Eventually.of_forall fun z => ?_)
    simp only
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatDensity_pos ht _), abs_of_nonneg (hF0 z)]
    rw [integral_mul_const, integral_heatDensity_sub ht, one_mul]
  have hswap := integral_integral_swap (f := fun y z => heatDensity t (y - z) * F z) hH
  have hinner : ∫ z, ∫ y, heatDensity t (y - z) * F z = ∫ z, F z := by
    congr 1; funext z
    rw [integral_mul_const, integral_heatDensity_sub ht, one_mul]
  unfold heatFisher
  have hFeq : fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity (gaussianReal 0 v.toNNReal))
      (heatFlowD1 ρ) (heatFlowD1 (gaussianReal 0 v.toNNReal)) t
      = fun y => gaussRelFlux ρ v t y ^ 2 / heatFlowDensity ρ t y :=
    funext fun y => fisherIntegrand_gaussianReal ρ hv ht y
  rw [hFeq]
  calc ∫ y, gaussRelFlux ρ v t y ^ 2 / heatFlowDensity ρ t y
      ≤ ∫ y, c ^ 2 * ∫ z, heatDensity t (y - z) * F z :=
        integral_mono_of_nonneg (Eventually.of_forall fun y =>
          div_nonneg (sq_nonneg _) (hPt y).le) (hH.integral_prod_left.const_mul _)
          (Eventually.of_forall hpt)
    _ = c ^ 2 * ∫ z, F z := by rw [integral_const_mul, hswap, hinner]

end Fisher

/-! ### Approximate identity and the KL integrand -/

/-- Rescaling of the standard Gaussian density: for `c > 0`,
`c φ_1(c z) = φ_{c⁻²}(z)` (`φ_a = heatDensity a`). -/
theorem mul_heatDensity_one {c : ℝ} (hc : 0 < c) (z : ℝ) :
    c * heatDensity 1 (c * z) = heatDensity (c ^ 2)⁻¹ z := by
  unfold heatDensity
  have h1 : Real.sqrt (2 * Real.pi * (c ^ 2)⁻¹) = Real.sqrt (2 * Real.pi) * c⁻¹ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq hc.le]
  rw [h1, mul_one]
  have : -(c * z) ^ 2 / (2 * 1) = -z ^ 2 / (2 * (c ^ 2)⁻¹) := by field_simp
  rw [this, mul_inv, inv_inv]
  ring

/-- For `v > 0` and every `y`, `s ↦ heatDensity s y` is continuous at `s = v`. -/
theorem continuousAt_heatDensity_time {v : ℝ} (hv : 0 < v) (y : ℝ) :
    ContinuousAt (fun s => heatDensity s y) v := by
  unfold heatDensity
  have h1 : Real.sqrt (2 * Real.pi * v) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h2 : 2 * v ≠ 0 := by positivity
  refine ContinuousAt.mul ?_ ?_
  · exact (Real.continuous_sqrt.continuousAt.comp (by fun_prop)).inv₀ h1
  · exact Real.continuous_exp.continuousAt.comp (continuousAt_const.div (by fun_prop) h2)

/-- **Gaussian approximate identity.** For an integrable continuous `p` and every `y`,
`∫ p(x) φ_{c⁻²}(y - x) dx → p(y)` as `c → ∞` (from Mathlib's
`tendsto_integral_comp_smul_smul_of_integrable'`). -/
theorem tendsto_mul_heatDensity_one (p : ℝ → ℝ) (hpi : Integrable p) (hpc : Continuous p)
    (y : ℝ) :
    Tendsto (fun c : ℝ => ∫ x, p x * heatDensity (c ^ 2)⁻¹ (y - x)) atTop (𝓝 (p y)) := by
  have hφ0 : ∀ x, 0 ≤ heatDensity 1 x := fun x => (heatDensity_pos one_pos x).le
  have hφ1 : ∫ x, heatDensity 1 x = 1 := by
    simpa using integral_heatDensity_sub one_pos 0
  have hdecay : Tendsto (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * heatDensity 1 x)
      (Bornology.cobounded ℝ) (𝓝 0) := by
    rw [Metric.cobounded_eq_cocompact]
    have := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1 / 2) (by norm_num) 1).const_mul
      (Real.sqrt (2 * Real.pi * 1))⁻¹
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    simp only [Module.finrank_self, pow_one, Real.norm_eq_abs, Real.rpow_one, heatDensity]
    ring_nf
  have h := tendsto_integral_comp_smul_smul_of_integrable' hφ0 hφ1 hdecay hpi
    hpc.continuousAt (x₀ := y)
  refine h.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
  congr 1; funext x
  rw [Module.finrank_self, pow_one, smul_eq_mul, smul_eq_mul, mul_heatDensity_one hc, mul_comm]

/-- **KL divergence of two density laws as a lintegral of a nonnegative integrand.** For
measurable `p ≥ 0`, `q > 0` with finite density measures `P = μ.withDensity p`,
`Q = μ.withDensity q` (`μ` σ-finite): `KL(P‖Q) = ∫⁻ q klFun(p / q)` with
`klFun u = u log u + 1 - u ≥ 0`, i.e. `∫ (p log(p/q) - p + q)` (Mathlib's
`klDiv_eq_lintegral_klFun_of_ac`). -/
theorem klDiv_withDensity_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {p q : α → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    [IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (p x))]
    [IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (q x))] :
    klDiv (μ.withDensity fun x => ENNReal.ofReal (p x))
        (μ.withDensity fun x => ENNReal.ofReal (q x))
      = ∫⁻ x, ENNReal.ofReal (q x * klFun (p x / q x)) ∂μ := by
  set P := μ.withDensity fun x => ENNReal.ofReal (p x) with hP
  set Q := μ.withDensity fun x => ENNReal.ofReal (q x) with hQ
  have hfp : Measurable fun x => ENNReal.ofReal (p x) := hpm.ennreal_ofReal
  have hfq : Measurable fun x => ENNReal.ofReal (q x) := hqm.ennreal_ofReal
  have hvolQ : μ ≪ Q :=
    withDensity_absolutelyContinuous' hfq.aemeasurable
      (Eventually.of_forall fun x => by simp [hq x])
  have hPQ : P ≪ Q := (withDensity_absolutelyContinuous _ _).trans hvolQ
  have h1 : P.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (p x) :=
    Measure.rnDeriv_withDensity _ hfp
  have h2 : P.rnDeriv Q =ᵐ[μ]
      fun x => (ENNReal.ofReal (q x))⁻¹ * P.rnDeriv μ x :=
    Measure.rnDeriv_withDensity_right P μ hfq.aemeasurable
      (Eventually.of_forall fun x => by simp [hq x])
      (Eventually.of_forall fun x => by simp)
  rw [klDiv_eq_lintegral_klFun_of_ac hPQ, hQ,
    lintegral_withDensity_eq_lintegral_mul _ hfq (by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Pi.mul_apply]
  rw [hx2, hx1, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hp0 x),
    ENNReal.toReal_ofReal (hq x).le, inv_mul_eq_div, ← ENNReal.ofReal_mul (hq x).le]

/-! ### The Gaussian log-Sobolev inequality at time zero -/

section LSI

variable {p p' : ℝ → ℝ}

/-- **Gaussian log-Sobolev inequality at time zero.**
Let `v > 0`, `π = N(0, v) = gaussianReal 0 v`, and let `ρ = volume.withDensity p` be a
probability law on `ℝ` whose density `p` is
* positive, `p > 0`, and differentiable everywhere with derivative `p'` (not necessarily
  continuous);
* of finite second moment: `x ↦ x² p(x)` is Lebesgue integrable;
* of finite relative Fisher information
  `I(ρ‖π) = ∫ p (p'/p + x/v)² dx < ∞` (integrability of the integrand).
Then `KL(ρ‖π) < ∞` and `KL(ρ‖π) ≤ (v/2) ∫ p (p'/p + x/v)² dx`. No finiteness of `KL(ρ‖π)` is
assumed.

Proof: the de Bruijn hypotheses `HeatFlowRegular ρ π (Ioi 0)` follow from the second moment
(`HeatFlowRegularity.heatFlowRegular_gaussianReal`). (1) Fisher decay from time zero
(`heatFisher_le_fisher0`): `I(ρ_t‖π_t) ≤ (v/(v+t))² I(ρ‖π)`; (2) the LSI along the heat flow
at positive times (`heatKL_le_heatFisher_gaussianReal`) gives
`KL(ρ_t‖π_t) ≤ ((v+t)/2)(v/(v+t))² I ≤ (v/2) I`; (3) Fatou on
`KL(ρ_t‖π_t) = ∫⁻ q_t klFun(p_t / q_t)` along `t_n = (n+1)⁻² → 0`, using the pointwise
convergences `p_{t_n} → p` (approximate identity) and `q_{t_n} → φ_v`. -/
theorem klDiv_le_fisher0 (hp : ∀ x, 0 < p x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    (hd : ∀ x, HasDerivAt p (p' x) x) {v : ℝ} (hv : 0 < v)
    (hmom : Integrable fun x => x ^ 2 * p x)
    (hfish : Integrable fun x => p x * (p' x / p x + x / v) ^ 2) :
    klDiv (volume.withDensity fun x => ENNReal.ofReal (p x)) (gaussianReal 0 v.toNNReal) ≠ ⊤ ∧
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (gaussianReal 0 v.toNNReal)).toReal
        ≤ v / 2 * ∫ x, p x * (p' x / p x + x / v) ^ 2 := by
  set ρ := volume.withDensity fun x => ENNReal.ofReal (p x) with hρ
  set π := gaussianReal 0 v.toNNReal with hπdef
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hpi : Integrable p := integrable_of_isProbabilityMeasure hpc.measurable hp0
  have hFe : ∀ x, p x * (p' x / p x + x / v) ^ 2 = relFlux0 p p' v x ^ 2 / p x := by
    intro x
    have := (hp x).ne'
    unfold relFlux0
    field_simp
  have hint : Integrable fun x => relFlux0 p p' v x ^ 2 / p x :=
    hfish.congr (Eventually.of_forall hFe)
  have hGc : Measurable (relFlux0 p p' v) :=
    (measurable_of_hasDerivAt hd).add ((measurable_id.div_const v).mul hpc.measurable)
  have hGi : Integrable (relFlux0 p p' v) :=
    integrable_of_sq_div hp hpi hGc.aestronglyMeasurable hint
  have hxp := integrable_mul_self hp0 hpi hpc hmom
  have hp'i : Integrable p' := by
    refine (hGi.sub (hxp.div_const v)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, relFlux0]
    ring
  have hmomρ : Integrable (fun x => x ^ 2) ρ := by
    rw [hρ, integrable_withDensity_iff_integrable_smul' hpc.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hmom.congr (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul, mul_comm]
  have hreg := HeatFlowRegularity.heatFlowRegular_gaussianReal ρ hmomρ hv
  set I0 := ∫ x, relFlux0 p p' v x ^ 2 / p x with hI0def
  have hI0 : 0 ≤ I0 := integral_nonneg fun x => div_nonneg (sq_nonneg _) (hp0 x)
  -- the LSI at positive times, with the time-`0` Fisher information
  have hKt : ∀ t, 0 < t → heatKL ρ π t ≤ v / 2 * I0 := by
    intro t ht
    have h1 := heatKL_le_heatFisher_gaussianReal ρ hv hmomρ ht
    have h2 := heatFisher_le_fisher0 hp hd hp'i hv ht hint
    have hvt : 0 < v + t := by linarith
    have hc1 : v / (v + t) ≤ 1 := (div_le_one hvt).2 (by linarith)
    calc heatKL ρ π t ≤ (v + t) / 2 * heatFisher ρ π t := h1
      _ ≤ (v + t) / 2 * ((v / (v + t)) ^ 2 * I0) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = v / 2 * (v / (v + t)) * I0 := by field_simp
      _ ≤ v / 2 * 1 * I0 := by gcongr
      _ = v / 2 * I0 := by ring
  have hKLt : ∀ t, 0 < t →
      klDiv (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensity ρ t y))
        (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensity π t y))
        ≤ ENNReal.ofReal (v / 2 * I0) := by
    intro t ht
    have := isProbabilityMeasure_withDensity_heatFlowDensity ρ ht
    have := isProbabilityMeasure_withDensity_heatFlowDensity π ht
    have hne := (FormalizeSampling.DeterministicStep.klDiv_withDensity_real
      (continuous_heatFlowDensity ρ ht).measurable (continuous_heatFlowDensity π ht).measurable
      (fun y => (heatFlowDensity_pos ρ ht y).le) (heatFlowDensity_pos π ht)
      (hreg.integrable_kl t ht)).1
    have := hKt t ht
    rw [heatKL, heatKernel_comp_eq_withDensity ρ ht, heatKernel_comp_eq_withDensity π ht] at this
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal this
  -- the Gaussian target as a density measure
  have hπ : π = volume.withDensity fun y => ENNReal.ofReal (heatDensity v y) := by
    have hv' : v.toNNReal ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hv
    rw [hπdef, gaussianReal_of_var_ne_zero _ hv', gaussianPDF_def,
      ← heatDensity_eq_gaussianPDFReal hv]
  -- the smoothing sequence `t_n = (n + 1)⁻²`
  set c : ℕ → ℝ := fun n => (n : ℝ) + 1 with hcdef
  set t : ℕ → ℝ := fun n => (c n ^ 2)⁻¹ with htdef
  have hcpos : ∀ n, 0 < c n := fun n => by positivity
  have htpos : ∀ n, 0 < t n := fun n => by have := hcpos n; positivity
  have hc : Tendsto c atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht0 : Tendsto t atTop (𝓝 0) :=
    ((tendsto_pow_atTop two_ne_zero).comp hc).inv_tendsto_atTop
  have hpn : ∀ y, Tendsto (fun n => heatFlowDensity ρ (t n) y) atTop (𝓝 (p y)) := by
    intro y
    refine ((tendsto_mul_heatDensity_one p hpi hpc y).comp hc).congr fun n => ?_
    simp only [Function.comp_apply, htdef]
    rw [heatFlowDensity_withDensity hpc.measurable hp0]
  have hqn : ∀ y, Tendsto (fun n => heatFlowDensity π (t n) y) atTop
      (𝓝 (heatDensity v y)) := by
    intro y
    have hvt : Tendsto (fun n => v + t n) atTop (𝓝 v) := by
      simpa using (tendsto_const_nhds (x := v)).add ht0
    have h := (continuousAt_heatDensity_time hv y).tendsto.comp hvt
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hπdef, heatFlowDensity_gaussianReal hv (htpos n)]
  -- Fatou's lemma on the nonnegative KL integrand `q klFun (p / q)`
  set f : ℕ → ℝ → ENNReal := fun n y => ENNReal.ofReal (heatFlowDensity π (t n) y *
    klFun (heatFlowDensity ρ (t n) y / heatFlowDensity π (t n) y)) with hfdef
  have hf : ∀ y, Tendsto (fun n => f n y) atTop
      (𝓝 (ENNReal.ofReal (heatDensity v y * klFun (p y / heatDensity v y)))) := fun y =>
    ENNReal.tendsto_ofReal ((hqn y).mul ((continuous_klFun.tendsto _).comp
      ((hpn y).div (hqn y) (heatDensity_pos hv y).ne')))
  have hfm : ∀ n, AEMeasurable (f n) := fun n =>
    (((continuous_heatFlowDensity π (htpos n)).measurable.mul
      (continuous_klFun.measurable.comp ((continuous_heatFlowDensity ρ (htpos n)).measurable.div
        (continuous_heatFlowDensity π (htpos n)).measurable))).ennreal_ofReal).aemeasurable
  have hfn : ∀ n, ∫⁻ y, f n y ≤ ENNReal.ofReal (v / 2 * I0) := by
    intro n
    have := isProbabilityMeasure_withDensity_heatFlowDensity ρ (htpos n)
    have := isProbabilityMeasure_withDensity_heatFlowDensity π (htpos n)
    rw [hfdef, ← klDiv_withDensity_eq_lintegral (continuous_heatFlowDensity ρ (htpos n)).measurable
      (continuous_heatFlowDensity π (htpos n)).measurable
      (fun y => (heatFlowDensity_pos ρ (htpos n) y).le) (heatFlowDensity_pos π (htpos n))]
    exact hKLt _ (htpos n)
  have hkl : klDiv ρ π = ∫⁻ y, ENNReal.ofReal (heatDensity v y * klFun (p y / heatDensity v y))
      := by
    have : IsProbabilityMeasure (volume.withDensity fun y => ENNReal.ofReal (heatDensity v y)) :=
      hπ ▸ inferInstance
    rw [hπ]
    exact klDiv_withDensity_eq_lintegral hpc.measurable (continuous_heatDensity v).measurable hp0
      (heatDensity_pos hv)
  have hle : klDiv ρ π ≤ ENNReal.ofReal (v / 2 * I0) := by
    rw [hkl]
    calc ∫⁻ y, ENNReal.ofReal (heatDensity v y * klFun (p y / heatDensity v y))
        = ∫⁻ y, liminf (fun n => f n y) atTop :=
          lintegral_congr fun y => ((hf y).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ y, f n y) atTop := lintegral_liminf_le' hfm
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hfn)
  have hI0eq : ∫ x, p x * (p' x / p x + x / v) ^ 2 = I0 := by
    rw [hI0def]; congr 1; funext x; exact hFe x
  rw [hI0eq]
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle,
    ENNReal.toReal_le_of_le_ofReal (by positivity) hle⟩

/-- **Gaussian log-Sobolev inequality at time zero.** Alias of `klDiv_le_fisher0`: the same
statement (finite second moment and finite relative Fisher information suffice). -/
alias klDiv_le_fisher0_of_moment := klDiv_le_fisher0

end LSI

end FormalizeSampling.GaussianLSIZero
