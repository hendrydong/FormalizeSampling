module

public import FormalizeSampling.Foundations.GaussianLSIPi
public import FormalizeSampling.Foundations.GaussianLSIZero
public import FormalizeSampling.Foundations.HeatFlowRegularityPi
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The Gaussian log-Sobolev inequality at time zero on `Fin d → ℝ`

Status: **Verified** under explicit hypotheses: a positive probability density `p`, Fréchet
differentiable everywhere (no continuity of the gradient), with finite second moment and finite
relative Fisher information (`klDiv_le_fisher0`; the de Bruijn hypotheses
`HeatFlowRegularPi ρ π (Ioi 0)` are discharged by
`Foundations/HeatFlowRegularityPerturbedPi.lean`). This is the `Fin d → ℝ` version of
`Foundations/GaussianLSIZero.lean`; `KL(ρ‖π) < ∞` is a conclusion.

Notation: `ρ = volume.withDensity p`, `π = N(0, v I)` (`v > 0`), `φ_a = heatDensityPi a`,
`p_t = heatFlowDensityPi ρ t = p * φ_t`, `G_0 = relFlux0Pi p gp v = ∇p + x p / v`,
`G_t = gaussRelFluxPi ρ v t`. Euclidean squares are written `∑ᵢ (·)ᵢ²`.

## Main results

* `integral_mul_heatGradPi`: `∂ᵢp_t = φ_t * ∂ᵢp` (integration by parts, via
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
* `gaussRelFluxPi_eq_integral`: `G_t = (v/(v+t)) φ_t * G_0`.
* `heatFisher_le_fisher0` (Fisher decay from time zero):
  `I(ρ_t‖N(0, (v + t) I)) ≤ (v/(v+t))² ∫ |G_0|² / p`.
* `tendsto_mul_heatDensityPi_one`: `p_t(y) → p(y)` as `t → 0⁺` (Gaussian approximate identity).
* `klDiv_le_fisher0` (**Gaussian LSI at time zero**; also under the name
  `klDiv_le_fisher0_of_moment`): `KL(ρ‖N(0, v I)) ≤ (v/2) ∫ p ∑ᵢ (∂ᵢp/p + xᵢ/v)² dx`.

## Not proved here

* Densities that are not differentiable everywhere or not everywhere positive.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped NNReal ENNReal

namespace FormalizeSampling.GaussianLSIZeroPi

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
open FormalizeSampling.GaussianLSIPi
open FormalizeSampling.HeatFlowDeBruijn (heatDensity heatDensity_pos)
open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_of_isProbabilityMeasure)
open FormalizeSampling.GaussianLSIZero (abs_le_add_sq_div integrable_of_sq_div
  klDiv_withDensity_eq_lintegral mul_heatDensity_one continuousAt_heatDensity_time)

variable {d : ℕ}

/-- The time-`0` relative score flux of a density `p` with gradient `gp` against `N(0, v I)`:
`relFlux0Pi p gp v x i = ∂ᵢp(x) + xᵢ p(x) / v = p(x) ∂ᵢ log(p(x) / φ_v(x))`. -/
noncomputable def relFlux0Pi (p : (Fin d → ℝ) → ℝ) (gp : (Fin d → ℝ) → Fin d → ℝ) (v : ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => gp x i + x i / v * p x

/-- An everywhere gradient is measurable: if `HasFDerivAt p (dotCLM (gp x)) x` for every `x`,
then each coordinate `x ↦ gp x i` is measurable (it equals `x ↦ fderiv ℝ p x eᵢ`). -/
theorem measurable_grad_of_hasFDerivAt {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ}
    (hd : ∀ x, HasFDerivAt p (dotCLM (gp x)) x) (i : Fin d) :
    Measurable fun x => gp x i := by
  have : (fun x => gp x i) = fun x => fderiv ℝ p x (Pi.single i 1) :=
    funext fun x => by rw [(hd x).fderiv, dotCLM_single]
  rw [this]
  fun_prop

/-! ### The heat flow of a law with a differentiable density -/

section HeatFlow

variable {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ}

/-- For a measurable density `p ≥ 0` and every `t, y`, the heat-flow density of
`ρ = volume.withDensity p` is `p_t(y) = ∫ p(x) φ_t(y - x) dx`. -/
theorem heatFlowDensityPi_withDensity (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (t : ℝ)
    (y : Fin d → ℝ) :
    heatFlowDensityPi (volume.withDensity fun x => ENNReal.ofReal (p x)) t y
      = ∫ x, p x * heatDensityPi t (y - x) :=
  integral_withDensity_ofReal hpm hp0 _

/-- For a measurable density `p ≥ 0` and every `t, y, i`,
`∂ᵢp_t(y) = ∫ p(x) ∂ᵢφ_t(y - x) dx` (`heatFlowGradPi`). -/
theorem heatFlowGradPi_withDensity (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (t : ℝ)
    (y : Fin d → ℝ) (i : Fin d) :
    heatFlowGradPi (volume.withDensity fun x => ENNReal.ofReal (p x)) t y i
      = ∫ x, p x * heatGradPi t (y - x) i :=
  integral_withDensity_ofReal hpm hp0 _

/-- **Integration by parts at time zero.** If `p` is integrable and differentiable with gradient
`gp` whose `i`-th coordinate is integrable, then for `t > 0`, every `y` and `i`:
`∫ p(x) ∂ᵢφ_t(y - x) dx = ∫ φ_t(y - x) ∂ᵢp(x) dx`. -/
theorem integral_mul_heatGradPi (hpi : Integrable p)
    (hd : ∀ x, HasFDerivAt p (dotCLM (gp x)) x) {i : Fin d}
    (hgi : Integrable fun x => gp x i) {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    ∫ x, p x * heatGradPi t (y - x) i = ∫ x, heatDensityPi t (y - x) * gp x i := by
  set Ca := (1 + 2 * t) / t * (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d
  set Ct := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d
  have hf : ∀ z, HasFDerivAt (fun z => heatDensityPi t (y - z))
      (dotCLM fun j => -heatGradPi t (y - z) j) z := by
    intro z
    have h := (hasFDerivAt_heatDensityPi t (y - z)).comp z
      ((hasFDerivAt_id z).const_sub y)
    refine h.congr_fderiv (eq_dotCLM_of_apply fun w => ?_)
    simp [dotCLM_apply, dotProduct]
  have hfv : ∀ z, fderiv ℝ (fun z => heatDensityPi t (y - z)) z (Pi.single i 1) =
      -heatGradPi t (y - z) i := fun z => by rw [(hf z).fderiv, dotCLM_single]
  have hgv : ∀ z, fderiv ℝ p z (Pi.single i 1) = gp z i := fun z => by
    rw [(hd z).fderiv, dotCLM_single]
  have hkb : ∀ z, ‖heatDensityPi t (y - z)‖ ≤ Ct := fun z => by
    rw [Real.norm_of_nonneg (heatDensityPi_pos ht _).le]; exact heatDensityPi_le ht _
  have hkc : Continuous fun z => heatDensityPi t (y - z) :=
    (continuous_heatDensityPi t).comp (by fun_prop)
  have hA : Integrable fun z => -heatGradPi t (y - z) i * p z :=
    hpi.bdd_mul (c := Ca)
      ((((continuous_apply i).comp (continuous_heatGradPi t)).comp
        (by fun_prop : Continuous fun z => y - z)).neg.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_neg]; exact abs_heatGradPi_le ht _ i)
  have hB : Integrable fun z => heatDensityPi t (y - z) * gp z i :=
    hgi.bdd_mul (c := Ct) hkc.aestronglyMeasurable (Eventually.of_forall hkb)
  have hC : Integrable fun z => heatDensityPi t (y - z) * p z :=
    hpi.bdd_mul (c := Ct) hkc.aestronglyMeasurable (Eventually.of_forall hkb)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun z => heatDensityPi t (y - z)) (g := p)
    (μ := volume) (v := Pi.single i 1)
    (by simp_rw [hfv]; exact hA) (by simp_rw [hgv]; exact hB) hC
    (fun z _ => (hf z).differentiableAt) (fun z _ => (hd z).differentiableAt)
  simp_rw [hfv, hgv] at h
  rw [h, ← integral_neg]
  congr 1; funext z; ring

/-- **Relative score of the smoothed law from the time-`0` flux.** Let `p > 0` be integrable,
differentiable with gradient `gp` with integrable coordinates, `ρ = volume.withDensity p`. For
`v, t > 0`, every `y` and `i`, with `G_0 = relFlux0Pi p gp v`:
`G_t(y)ᵢ = (v / (v + t)) ∫ φ_t(y - x) G_0(x)ᵢ dx` (`G_t = gaussRelFluxPi ρ v t`). -/
theorem gaussRelFluxPi_eq_integral (hp : ∀ x, 0 < p x) (hpi : Integrable p)
    (hd : ∀ x, HasFDerivAt p (dotCLM (gp x)) x) (hgi : ∀ i, Integrable fun x => gp x i)
    {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (y : Fin d → ℝ) (i : Fin d) :
    gaussRelFluxPi (volume.withDensity fun x => ENNReal.ofReal (p x)) v t y i
      = v / (v + t) * ∫ x, heatDensityPi t (y - x) * relFlux0Pi p gp v x i := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  set Ct := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d
  have hkb : ∀ z, ‖heatDensityPi t (y - z)‖ ≤ Ct := fun z => by
    rw [Real.norm_of_nonneg (heatDensityPi_pos ht _).le]; exact heatDensityPi_le ht _
  have hkc : Continuous fun z => heatDensityPi t (y - z) :=
    (continuous_heatDensityPi t).comp (by fun_prop)
  have hB : Integrable fun x => heatDensityPi t (y - x) * gp x i :=
    (hgi i).bdd_mul (c := Ct) hkc.aestronglyMeasurable (Eventually.of_forall hkb)
  have hI2 : Integrable fun x => p x * heatDensityPi t (y - x) :=
    hpi.mul_bdd hkc.aestronglyMeasurable (Eventually.of_forall hkb)
  have hI3 : Integrable fun x => p x * heatGradPi t (y - x) i :=
    hpi.mul_bdd (((continuous_apply i).comp (continuous_heatGradPi t)).comp
        (by fun_prop : Continuous fun z => y - z)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_heatGradPi_le ht _ i)
  have hpt : ∀ x, heatDensityPi t (y - x) * relFlux0Pi p gp v x i
      = heatDensityPi t (y - x) * gp x i + (1 / v) *
        (y i * (p x * heatDensityPi t (y - x)) + t * (p x * heatGradPi t (y - x) i)) := by
    intro x
    unfold relFlux0Pi heatGradPi
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hI23 : Integrable fun x => 1 / v *
      (y i * (p x * heatDensityPi t (y - x)) + t * (p x * heatGradPi t (y - x) i)) :=
    ((hI2.const_mul (y i)).add (hI3.const_mul t)).const_mul _
  simp_rw [hpt]
  rw [integral_add hB hI23, integral_const_mul,
    integral_add (hI2.const_mul (y i)) (hI3.const_mul t), integral_const_mul,
    integral_const_mul, ← integral_mul_heatGradPi hpi hd (hgi i) ht y]
  unfold gaussRelFluxPi
  rw [heatFlowGradPi_withDensity hpc.measurable hp0,
    heatFlowDensityPi_withDensity hpc.measurable hp0]
  have : v + t ≠ 0 := by linarith
  field_simp
  ring

end HeatFlow

/-! ### Fisher information decay from time zero -/

section Fisher

variable {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ}

/-- **Fisher information decay from time zero (Gaussian target, `Fin d → ℝ`).** Let `p > 0` be a
probability density (`ρ = volume.withDensity p`), differentiable with gradient `gp` with
integrable coordinates (`gp` is automatically measurable, `measurable_grad_of_hasFDerivAt`; it
need not be continuous), and `v, t > 0`. If the time-`0` relative Fisher integrand `|G_0|² / p`
(`G_0 = relFlux0Pi p gp v`) is integrable, then
`I(ρ_t‖N(0, (v + t) I)) ≤ (v / (v + t))² · ∫ |G_0|² / p` (`heatFisher`). -/
theorem heatFisher_le_fisher0 (hp : ∀ x, 0 < p x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    (hd : ∀ x, HasFDerivAt p (dotCLM (gp x)) x)
    (hgi : ∀ i, Integrable fun x => gp x i) {v t : ℝ} (hv : 0 < v) (ht : 0 < t)
    (hint : Integrable fun x => (∑ i, relFlux0Pi p gp v x i ^ 2) / p x) :
    heatFisher (volume.withDensity fun x => ENNReal.ofReal (p x))
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) t
      ≤ (v / (v + t)) ^ 2 * ∫ x, (∑ i, relFlux0Pi p gp v x i ^ 2) / p x := by
  set ρ := volume.withDensity fun x => ENNReal.ofReal (p x) with hρ
  set π := Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal with hπ
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hp0' : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hpi : Integrable p := integrable_of_isProbabilityMeasure hpc.measurable hp0'
  set G := relFlux0Pi p gp v with hG
  set F : (Fin d → ℝ) → ℝ := fun z => (∑ i, G z i ^ 2) / p z with hF
  set c := v / (v + t) with hc
  set Ca := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ d with hCa
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hp z).le
  have hGc : ∀ i, Measurable fun z => G z i := fun i =>
    (measurable_grad_of_hasFDerivAt hd i).add
      (((measurable_pi_apply i).div_const v).mul hpc.measurable)
  have hFc : Measurable F :=
    (Finset.measurable_fun_sum _ fun i _ => (hGc i).pow_const 2).div hpc.measurable
  have hFi : ∀ i z, G z i ^ 2 / p z ≤ F z := fun i z =>
    div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun j => G z j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)) (hp z).le
  have hPt : ∀ y, 0 < heatFlowDensityPi ρ t y := heatFlowDensityPi_pos ρ ht
  have hkc : ∀ y : Fin d → ℝ, Continuous fun z => heatDensityPi t (y - z) := fun y =>
    (continuous_heatDensityPi t).comp (by fun_prop)
  -- pointwise bound
  have hpt : ∀ y, (∑ i, gaussRelFluxPi ρ v t y i ^ 2) / heatFlowDensityPi ρ t y
      ≤ c ^ 2 * ∫ z, heatDensityPi t (y - z) * F z := by
    intro y
    have hk : ∀ z, 0 ≤ heatDensityPi t (y - z) := fun z => (heatDensityPi_pos ht _).le
    have hkb : ∀ z, ‖heatDensityPi t (y - z)‖ ≤ Ca := fun z => by
      rw [Real.norm_of_nonneg (hk z)]; exact heatDensityPi_le ht _
    have h1 : Integrable fun z => heatDensityPi t (y - z) * p z :=
      hpi.bdd_mul (c := Ca) (hkc y).aestronglyMeasurable (Eventually.of_forall hkb)
    have h3F : Integrable fun z => heatDensityPi t (y - z) * F z :=
      hint.bdd_mul (c := Ca) (hkc y).aestronglyMeasurable (Eventually.of_forall hkb)
    have h3 : ∀ i, Integrable fun z => heatDensityPi t (y - z) * (G z i ^ 2 / p z) := by
      intro i
      refine h3F.mono ((hkc y).measurable.mul (((hGc i).pow_const 2).div
        hpc.measurable)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hk z),
        abs_of_nonneg (div_nonneg (sq_nonneg _) (hp z).le), abs_of_nonneg (hF0 z)]
      exact mul_le_mul_of_nonneg_left (hFi i z) (hk z)
    have h2 : ∀ i, Integrable fun z => heatDensityPi t (y - z) * G z i := by
      intro i
      have h13 : Integrable fun z => (heatDensityPi t (y - z) * p z
          + heatDensityPi t (y - z) * (G z i ^ 2 / p z)) / 2 := (h1.add (h3 i)).div_const 2
      refine h13.mono' ((hkc y).measurable.mul (hGc i)).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      have hamgm : |G z i| ≤ (p z + G z i ^ 2 / p z) / 2 := abs_le_add_sq_div (hp z)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk z)]
      calc heatDensityPi t (y - z) * |G z i|
          ≤ heatDensityPi t (y - z) * ((p z + G z i ^ 2 / p z) / 2) :=
            mul_le_mul_of_nonneg_left hamgm (hk z)
        _ = _ := by ring
    have hC : ∫ z, heatDensityPi t (y - z) * p z = heatFlowDensityPi ρ t y := by
      rw [hρ, heatFlowDensityPi_withDensity hpc.measurable hp0']; congr 1; funext z; ring
    have hCSi : ∀ i, gaussRelFluxPi ρ v t y i ^ 2 ≤
        c ^ 2 * (heatFlowDensityPi ρ t y *
          ∫ z, heatDensityPi t (y - z) * (G z i ^ 2 / p z)) := by
      intro i
      have hCS := sq_integral_mul_le hk hp h1 (h2 i) (h3 i) (by rw [hC]; exact hPt y)
      rw [hC] at hCS
      rw [gaussRelFluxPi_eq_integral hp hpi hd hgi hv ht y i, mul_pow]
      exact mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    have hsumF : ∑ i, ∫ z, heatDensityPi t (y - z) * (G z i ^ 2 / p z) =
        ∫ z, heatDensityPi t (y - z) * F z := by
      rw [← integral_finsetSum _ fun i _ => h3 i]
      congr 1; funext z
      rw [← Finset.mul_sum, hF]; simp only; rw [Finset.sum_div]
    rw [div_le_iff₀ (hPt y)]
    calc ∑ i, gaussRelFluxPi ρ v t y i ^ 2
        ≤ ∑ i, c ^ 2 * (heatFlowDensityPi ρ t y *
            ∫ z, heatDensityPi t (y - z) * (G z i ^ 2 / p z)) :=
          Finset.sum_le_sum fun i _ => hCSi i
      _ = c ^ 2 * (∫ z, heatDensityPi t (y - z) * F z) * heatFlowDensityPi ρ t y := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hsumF]; ring
  -- integrate in `y`
  have hHm : AEStronglyMeasurable
      (fun q : (Fin d → ℝ) × (Fin d → ℝ) => heatDensityPi t (q.1 - q.2) * F q.2)
      (volume.prod volume) :=
    (((continuous_heatDensityPi t).comp (continuous_fst.sub continuous_snd)).measurable.mul
      (hFc.comp measurable_snd)).aestronglyMeasurable
  have hH : Integrable
      (fun q : (Fin d → ℝ) × (Fin d → ℝ) => heatDensityPi t (q.1 - q.2) * F q.2)
      (volume.prod volume) := by
    refine (integrable_prod_iff' hHm).2 ⟨Eventually.of_forall fun z => by
      simpa only using (integrable_heatDensityPi_sub ht z).1.mul_const (F z), ?_⟩
    refine hint.congr (Eventually.of_forall fun z => ?_)
    simp only
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (heatDensityPi_pos ht _),
      abs_of_nonneg (hF0 z)]
    rw [integral_mul_const, (integrable_heatDensityPi_sub ht z).2, one_mul]
  have hswap := integral_integral_swap (f := fun y z => heatDensityPi t (y - z) * F z) hH
  have hinner : ∫ z, ∫ y, heatDensityPi t (y - z) * F z = ∫ z, F z := by
    congr 1; funext z
    rw [integral_mul_const, (integrable_heatDensityPi_sub ht z).2, one_mul]
  unfold heatFisher
  have hFeq : fisherIntegrand (heatFlowDensityPi ρ) (heatFlowDensityPi π)
      (heatFlowGradPi ρ) (heatFlowGradPi π) t
      = fun y => (∑ i, gaussRelFluxPi ρ v t y i ^ 2) / heatFlowDensityPi ρ t y :=
    funext fun y => fisherIntegrand_gaussian ρ hv ht y
  rw [hFeq]
  calc ∫ y, (∑ i, gaussRelFluxPi ρ v t y i ^ 2) / heatFlowDensityPi ρ t y
      ≤ ∫ y, c ^ 2 * ∫ z, heatDensityPi t (y - z) * F z :=
        integral_mono_of_nonneg (Eventually.of_forall fun y =>
          div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hPt y).le)
          (hH.integral_prod_left.const_mul _) (Eventually.of_forall hpt)
    _ = c ^ 2 * ∫ z, F z := by rw [integral_const_mul, hswap, hinner]

end Fisher

/-! ### Approximate identity -/

/-- Rescaling of the standard isotropic Gaussian density: for `c > 0`,
`c^d φ_1(c z) = φ_{c⁻²}(z)` (`φ_a = heatDensityPi a`). -/
theorem pow_mul_heatDensityPi_one {c : ℝ} (hc : 0 < c) (z : Fin d → ℝ) :
    c ^ d * heatDensityPi 1 (c • z) = heatDensityPi (c ^ 2)⁻¹ z := by
  unfold heatDensityPi
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_heatDensity_one hc]

/-- Decay of the standard Gaussian: `‖x‖^d φ_1(x) → 0` as `x → ∞` (along `cobounded`). -/
theorem tendsto_norm_pow_mul_heatDensityPi_one :
    Tendsto (fun x : Fin d → ℝ => ‖x‖ ^ d * heatDensityPi 1 x) (Bornology.cobounded _)
      (𝓝 0) := by
  set C := (Real.sqrt (2 * Real.pi * 1))⁻¹ ^ d
  have hg : Tendsto (fun u : ℝ => |u| ^ (d : ℝ) * Real.exp (-(1 / 2) * u ^ 2)) atTop (𝓝 0) :=
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num) _).mono_left
      atTop_le_cocompact
  have h := (hg.comp (tendsto_norm_cobounded_atTop (E := Fin d → ℝ))).const_mul C
  rw [mul_zero] at h
  refine squeeze_zero (fun x => mul_nonneg (by positivity) (heatDensityPi_pos one_pos x).le)
    (fun x => ?_) h
  simp only [Function.comp_apply]
  rw [heatDensityPi_eq_exp, abs_norm, Real.rpow_natCast]
  have h1 : Real.exp (-(∑ i, x i ^ 2) / (2 * 1)) ≤ Real.exp (-(1 / 2) * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.2
    have := sq_norm_le_sum_sq x
    linarith
  have hC : 0 ≤ C := by positivity
  calc ‖x‖ ^ d * (C * Real.exp (-(∑ i, x i ^ 2) / (2 * 1)))
      = C * (‖x‖ ^ d * Real.exp (-(∑ i, x i ^ 2) / (2 * 1))) := by ring
    _ ≤ C * (‖x‖ ^ d * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) := by gcongr

/-- **Gaussian approximate identity on `Fin d → ℝ`.** For an integrable continuous `p` and every
`y`, `∫ p(x) φ_{c⁻²}(y - x) dx → p(y)` as `c → ∞` (from Mathlib's
`tendsto_integral_comp_smul_smul_of_integrable'`). -/
theorem tendsto_mul_heatDensityPi_one (p : (Fin d → ℝ) → ℝ) (hpi : Integrable p)
    (hpc : Continuous p) (y : Fin d → ℝ) :
    Tendsto (fun c : ℝ => ∫ x, p x * heatDensityPi (c ^ 2)⁻¹ (y - x)) atTop (𝓝 (p y)) := by
  have hφ0 : ∀ x : Fin d → ℝ, 0 ≤ heatDensityPi 1 x := fun x => (heatDensityPi_pos one_pos x).le
  have hφ1 : ∫ x : Fin d → ℝ, heatDensityPi 1 x = 1 := by
    simpa using (integrable_heatDensityPi_sub one_pos (0 : Fin d → ℝ)).2
  have hdecay : Tendsto (fun x : Fin d → ℝ => ‖x‖ ^ Module.finrank ℝ (Fin d → ℝ) *
      heatDensityPi 1 x) (Bornology.cobounded _) (𝓝 0) := by
    rw [Module.finrank_fin_fun]; exact tendsto_norm_pow_mul_heatDensityPi_one
  have h := tendsto_integral_comp_smul_smul_of_integrable' hφ0 hφ1 hdecay hpi
    hpc.continuousAt (x₀ := y)
  refine h.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
  congr 1; funext x
  rw [Module.finrank_fin_fun, smul_eq_mul, pow_mul_heatDensityPi_one hc, mul_comm]

/-! ### The Gaussian log-Sobolev inequality at time zero -/

section LSI

variable {p : (Fin d → ℝ) → ℝ} {gp : (Fin d → ℝ) → Fin d → ℝ}

/-- **Gaussian log-Sobolev inequality at time zero on `Fin d → ℝ`.** Let `v > 0`,
`π = N(0, v I) = ⊗ᵢ gaussianReal 0 v`, and let `ρ = volume.withDensity p` be a probability law on
`Fin d → ℝ` whose density `p` is
* positive, `p > 0`, and Fréchet differentiable with gradient `gp` (`HasFDerivAt p
  (dotCLM (gp x)) x`; `gp` need not be continuous);
* of finite second moment: `x ↦ (∑ᵢ xᵢ²) p(x)` is Lebesgue integrable;
* of finite relative Fisher information
  `I(ρ‖π) = ∫ p ∑ᵢ (∂ᵢp/p + xᵢ/v)² dx < ∞` (integrability of the integrand).
Then `KL(ρ‖π) < ∞` and `KL(ρ‖π) ≤ (v/2) ∫ p |∇ log p + x/v|² dx`. No finiteness of `KL(ρ‖π)` is
assumed. The de Bruijn hypotheses `HeatFlowRegularPi ρ π (Ioi 0)` follow from the second moment
(`HeatFlowRegularityPi.heatFlowRegularPi_gaussian`); the proof is that of
`GaussianLSIZero.klDiv_le_fisher0`: Fisher decay from time zero (`heatFisher_le_fisher0`), the LSI
at positive times (`heatKL_le_heatFisher_gaussian`), and Fatou along `t_n = (n+1)⁻² → 0`. -/
theorem klDiv_le_fisher0 (hp : ∀ x, 0 < p x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x))]
    (hd : ∀ x, HasFDerivAt p (dotCLM (gp x)) x)
    {v : ℝ} (hv : 0 < v)
    (hmom : Integrable fun x => (∑ i, x i ^ 2) * p x)
    (hfish : Integrable fun x => p x * ∑ i, (gp x i / p x + x i / v) ^ 2) :
    klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal) ≠ ⊤ ∧
      (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
        (Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal)).toReal
        ≤ v / 2 * ∫ x, p x * ∑ i, (gp x i / p x + x i / v) ^ 2 := by
  set ρ := volume.withDensity fun x => ENNReal.ofReal (p x) with hρ
  set π := Measure.pi fun _ : Fin d => gaussianReal 0 v.toNNReal with hπdef
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hpi : Integrable p := integrable_of_isProbabilityMeasure hpc.measurable hp0
  set G := relFlux0Pi p gp v with hG
  have hFe : ∀ x, p x * ∑ i, (gp x i / p x + x i / v) ^ 2 = (∑ i, G x i ^ 2) / p x := by
    intro x
    have := (hp x).ne'
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hG, relFlux0Pi]
    field_simp
  have hint : Integrable fun x => (∑ i, G x i ^ 2) / p x :=
    hfish.congr (Eventually.of_forall hFe)
  have hGc : ∀ i, Measurable fun z => G z i := fun i =>
    (measurable_grad_of_hasFDerivAt hd i).add
      (((measurable_pi_apply i).div_const v).mul hpc.measurable)
  have hGi : ∀ i, Integrable fun x => G x i := by
    intro i
    refine integrable_of_sq_div hp hpi (hGc i).aestronglyMeasurable
      (hint.mono (((hGc i).pow_const 2).div hpc.measurable).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_))
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hp0 z)),
      Real.norm_of_nonneg (div_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) (hp0 z))]
    exact div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun j => G z j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)) (hp0 z)
  have hxp : ∀ i, Integrable fun x => x i * p x := by
    intro i
    refine (hpi.add hmom).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 x)]
    have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 := Finset.single_le_sum (f := fun j => x j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have : |x i| ≤ 1 + ∑ j, x j ^ 2 := by nlinarith [abs_nonneg (x i), sq_abs (x i)]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_right this (hp0 x)]
  have hgi : ∀ i, Integrable fun x => gp x i := by
    intro i
    refine ((hGi i).sub ((hxp i).div_const v)).congr (Eventually.of_forall fun x => ?_)
    simp only [hG, relFlux0Pi, Pi.sub_apply]
    ring
  have hmomρ : Integrable (fun x => ∑ i, x i ^ 2) ρ := by
    rw [hρ, integrable_withDensity_iff_integrable_smul' hpc.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hmom.congr (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul, mul_comm]
  have hreg := HeatFlowRegularityPi.heatFlowRegularPi_gaussian ρ hmomρ hv
  set I0 := ∫ x, (∑ i, G x i ^ 2) / p x with hI0def
  have hI0 : 0 ≤ I0 :=
    integral_nonneg fun x => div_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) (hp0 x)
  -- the LSI at positive times, with the time-`0` Fisher information
  have hKt : ∀ t, 0 < t → heatKL ρ π t ≤ v / 2 * I0 := by
    intro t ht
    have h1 := heatKL_le_heatFisher_gaussian ρ hv hmomρ ht
    have h2 := heatFisher_le_fisher0 hp hd hgi hv ht hint
    have hvt : 0 < v + t := by linarith
    have hc1 : v / (v + t) ≤ 1 := (div_le_one hvt).2 (by linarith)
    calc heatKL ρ π t ≤ (v + t) / 2 * heatFisher ρ π t := h1
      _ ≤ (v + t) / 2 * ((v / (v + t)) ^ 2 * I0) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = v / 2 * (v / (v + t)) * I0 := by field_simp
      _ ≤ v / 2 * 1 * I0 := by gcongr
      _ = v / 2 * I0 := by ring
  have hKLt : ∀ t, 0 < t →
      klDiv (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensityPi ρ t y))
        (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensityPi π t y))
        ≤ ENNReal.ofReal (v / 2 * I0) := by
    intro t ht
    have := isProbabilityMeasure_withDensity_heatFlowDensityPi ρ ht
    have := isProbabilityMeasure_withDensity_heatFlowDensityPi π ht
    have hne : klDiv (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensityPi ρ t y))
        (volume.withDensity fun y => ENNReal.ofReal (heatFlowDensityPi π t y)) ≠ ⊤ := by
      rw [FormalizeSampling.KLTransport.klDiv_withDensity_eq_integral
        (continuous_heatFlowDensityPi ρ ht).measurable
        (continuous_heatFlowDensityPi π ht).measurable
        (fun y => (heatFlowDensityPi_pos ρ ht y).le) (heatFlowDensityPi_pos π ht)
        (hreg.integrable_kl t ht)]
      exact ENNReal.ofReal_ne_top
    have := hKt t ht
    rw [heatKL, heatKernelPi_comp_eq_withDensity ρ ht,
      heatKernelPi_comp_eq_withDensity π ht] at this
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal this
  -- the Gaussian target as a density measure
  have hπ : π = volume.withDensity fun y => ENNReal.ofReal (heatDensityPi v y) := by
    rw [hπdef, pi_gaussianReal_eq_heatKernelPi, heatKernelPi_eq_withDensity hv]
    simp_rw [sub_zero]
  -- the smoothing sequence `t_n = (n + 1)⁻²`
  set c : ℕ → ℝ := fun n => (n : ℝ) + 1 with hcdef
  set t : ℕ → ℝ := fun n => (c n ^ 2)⁻¹ with htdef
  have hcpos : ∀ n, 0 < c n := fun n => by positivity
  have htpos : ∀ n, 0 < t n := fun n => by have := hcpos n; positivity
  have hc : Tendsto c atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht0 : Tendsto t atTop (𝓝 0) :=
    ((tendsto_pow_atTop two_ne_zero).comp hc).inv_tendsto_atTop
  have hpn : ∀ y, Tendsto (fun n => heatFlowDensityPi ρ (t n) y) atTop (𝓝 (p y)) := by
    intro y
    refine ((tendsto_mul_heatDensityPi_one p hpi hpc y).comp hc).congr fun n => ?_
    simp only [Function.comp_apply, htdef]
    rw [heatFlowDensityPi_withDensity hpc.measurable hp0]
  have hqn : ∀ y, Tendsto (fun n => heatFlowDensityPi π (t n) y) atTop
      (𝓝 (heatDensityPi v y)) := by
    intro y
    have hvt : Tendsto (fun n => v + t n) atTop (𝓝 v) := by
      simpa using (tendsto_const_nhds (x := v)).add ht0
    have h : Tendsto (fun n => heatDensityPi (v + t n) y) atTop (𝓝 (heatDensityPi v y)) :=
      tendsto_finsetProd _ fun i _ => (continuousAt_heatDensity_time hv (y i)).tendsto.comp hvt
    refine h.congr fun n => ?_
    rw [hπdef, heatFlowDensityPi_gaussian hv (htpos n)]
  -- Fatou's lemma on the nonnegative KL integrand `q klFun (p / q)`
  set f : ℕ → (Fin d → ℝ) → ENNReal := fun n y => ENNReal.ofReal (heatFlowDensityPi π (t n) y *
    klFun (heatFlowDensityPi ρ (t n) y / heatFlowDensityPi π (t n) y)) with hfdef
  have hf : ∀ y, Tendsto (fun n => f n y) atTop
      (𝓝 (ENNReal.ofReal (heatDensityPi v y * klFun (p y / heatDensityPi v y)))) := fun y =>
    ENNReal.tendsto_ofReal ((hqn y).mul ((continuous_klFun.tendsto _).comp
      ((hpn y).div (hqn y) (heatDensityPi_pos hv y).ne')))
  have hfm : ∀ n, AEMeasurable (f n) := fun n =>
    (((continuous_heatFlowDensityPi π (htpos n)).measurable.mul
      (continuous_klFun.measurable.comp
        ((continuous_heatFlowDensityPi ρ (htpos n)).measurable.div
        (continuous_heatFlowDensityPi π (htpos n)).measurable))).ennreal_ofReal).aemeasurable
  have hfn : ∀ n, ∫⁻ y, f n y ≤ ENNReal.ofReal (v / 2 * I0) := by
    intro n
    have := isProbabilityMeasure_withDensity_heatFlowDensityPi ρ (htpos n)
    have := isProbabilityMeasure_withDensity_heatFlowDensityPi π (htpos n)
    rw [hfdef, ← klDiv_withDensity_eq_lintegral
      (continuous_heatFlowDensityPi ρ (htpos n)).measurable
      (continuous_heatFlowDensityPi π (htpos n)).measurable
      (fun y => (heatFlowDensityPi_pos ρ (htpos n) y).le) (heatFlowDensityPi_pos π (htpos n))]
    exact hKLt _ (htpos n)
  have hkl : klDiv ρ π
      = ∫⁻ y, ENNReal.ofReal (heatDensityPi v y * klFun (p y / heatDensityPi v y)) := by
    have : IsProbabilityMeasure
        (volume.withDensity fun y => ENNReal.ofReal (heatDensityPi (d := d) v y)) :=
      hπ ▸ inferInstance
    rw [hπ]
    exact klDiv_withDensity_eq_lintegral hpc.measurable (continuous_heatDensityPi v).measurable
      hp0 (heatDensityPi_pos hv)
  have hle : klDiv ρ π ≤ ENNReal.ofReal (v / 2 * I0) := by
    rw [hkl]
    calc ∫⁻ y, ENNReal.ofReal (heatDensityPi v y * klFun (p y / heatDensityPi v y))
        = ∫⁻ y, liminf (fun n => f n y) atTop :=
          lintegral_congr fun y => ((hf y).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ y, f n y) atTop := lintegral_liminf_le' hfm
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hfn)
  have hI0eq : ∫ x, p x * ∑ i, (gp x i / p x + x i / v) ^ 2 = I0 := by
    rw [hI0def]; congr 1; funext x; exact hFe x
  rw [hI0eq]
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle,
    ENNReal.toReal_le_of_le_ofReal (by positivity) hle⟩

/-- **Gaussian log-Sobolev inequality at time zero on `Fin d → ℝ`.** Alias of
`klDiv_le_fisher0`: the same statement (finite second moment and finite relative Fisher
information suffice). -/
alias klDiv_le_fisher0_of_moment := klDiv_le_fisher0

end LSI

end FormalizeSampling.GaussianLSIZeroPi
