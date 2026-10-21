module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import FormalizeSampling.Flow.OULangevinDecayPi
public import FormalizeSampling.Flow.LogSobolevAlongGaussian
public import FormalizeSampling.Flow.KLDissipation
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# The OU probability flow: FL-1/FL-2/FL-4 for a non-stationary flow

Registry IDs: **FL-1 (II)**, **FL-2**, **FL-4**. This is a concrete, non-stationary instance of
the flow hypotheses of `Flow/KLDissipation.lean`, `Flow/KLDecay.lean` and
`Flow/LogSobolevAlongGaussian.lean`.

Status: **Verified**. There are no regularity or functional-inequality hypotheses. The
initial law `ρ` is a probability measure on `Fin d → ℝ` with `∫ |x|² dρ < ∞`.

## Setting

* Target `π = N(0, v I)`, `v > 0`, with Lebesgue density `φ_v = heatDensityPi v`. Its score is
  `∇log φ_v(x) = -x / v` (`score_heatDensityPi`).
* OU rate `a > 0`. Write `c_t = e^{-at}` (`ouC`), `s_t = v (1 - e^{-2at})` (`ouS`) and
  `τ_t = v (e^{2at} - 1)` (`ouTau`), so `s_t = c_t² τ_t`.
* The marginal density is `p_t = ouDensity ρ v a t = (c_t ·)_# ρ * N(0, s_t I)`, the density of
  `e^{-at} X₀ + √(v (1 - e^{-2at})) Z`. Its gradient is `ouGrad`, its Laplacian `ouLap`. Its
  law is the OU marginal of `OULangevinDecayPi`: `p_t dx = ouKernelVarPi v a t ∘ₘ ρ`
  (`lawOf_ouDensity`).
* The velocity is the probability-flow (ideal) velocity
  `ouVelocity = a v (∇log φ_v - ∇log p_t) = idealVelocity ((a v)⁻¹ I) (∇log p_t) (∇log φ_v)`
  (`ouVelocity_eq_idealVelocity`, `ouPrecond`). The flux is `p_t v_t = -a (x p_t + v ∇p_t)`, so
  `-div(p_t v_t) = a (div(x p_t) + v Δp_t)`. This is the OU Fokker–Planck equation
  `∂ₜ p = a (div(x p) + v Δp)`.

## Main results

* `hasDerivAt_ouDensity_t` and `hasDerivAt_ouDensity_continuity`: the strong continuity
  equation `∂ₜ p_t(x) = -div(p_t v_t)(x)` holds for every `t > 0` and every `x`. The proof
  differentiates under the integral sign (`kernel_identity`).
* `gaussianDensityHyp_ouDensity`: `GaussianDensityHyp (p_t) (∇p_t) v` holds for every `t > 0`.
* `gaussKL_ouDensity_eq`: `KL(p_t ‖ π) = heatKL ρ π τ_t`, by scaling invariance of KL.
  `heatFisher_eq` scales the Fisher information: `I_heat(τ_t) = c_t² I(p_t ‖ π)`.
* `klDiv_lawOf_ouDensity` and `gaussKL_eq_klDivDensity` show that the three KL forms agree:
  `klDiv`, `gaussKL`, `KLDecay.klDivDensity` and `∫ p_t log(p_t/φ_v)`. In particular, the KL is
  finite for `t > 0`.
* **FL-1/FL-2, unconditional** (`hasDerivAt_gaussKL_ouDensity`,
  `hasDerivAt_gaussKL_ouDensity_score`, `hasDerivAt_klDivDensity_ouDensity`): for `t > 0`,
  `d/dt KL(p_t ‖ π) = -a v I(p_t ‖ π) = -∫ ‖∇log p_t - ∇log φ_v‖²_{H⁻¹} p_t` with
  `H = (a v)⁻¹ I`. The proof uses de Bruijn's identity `hasDerivAt_heatKL` along the heat
  flow, the regularity `heatFlowRegularPi_gaussian` and the chain rule in `τ_t`.
* `klFirstVariation_ou`: `KLDecay.KLFirstVariation` holds for the flow shifted to start at any
  `s > 0`.
* **FL-4, unconditional** (`gaussKL_ouDensity_le`,
  `toReal_klDiv_ouKernelVarPi_comp_le_of_le`): for `0 < s ≤ t`,
  `KL(p_t ‖ π) ≤ e^{-2a(t-s)} KL(p_s ‖ π)`, and both sides are finite. This applies
  `LogSobolevAlongGaussian.exp_decay_idealVelocity_gaussian` with every hypothesis discharged.
  No `KL(ρ‖π) < ∞` is needed.
* Ingredients of `TransportKLRegularity`, used in `Flow/ProbabilityFlowOUMoment.lean`: the
  integrable Gaussian envelope `envOU` (`integrable_envOU`), the explicit velocity
  (`ouVelocity_apply`, `differentiable_ouVelocity`) and flux derivative
  (`partialDeriv_ouFlux`), and the time shift `transportKLRegularity_shift`.

## Not proved here (in this file)

* **Only `t > 0`.** The continuity equation, the KL derivative and the regularity are not
  proved at `t = 0`, where `ρ` may have no density. The `KLDissipation` theorems are applied
  to the shifted flow `t ↦ p_{s+t}`, which is defined on `(-s, ∞)`. Decay from `t = 0` is
  `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`, which uses data processing and
  assumes `KL(ρ‖π) < ∞`. Continuity of `t ↦ KL(p_t‖π)` at `0⁺` is not proved here; it is
  `ProbabilityFlowOUZero.tendsto_klDiv_ouKernelVarPi_comp_zero`.
* **`TransportKLRegularity`** is not proved in this file. Under a finite fourth moment (in
  particular for compactly supported `ρ`, `transportKLRegularity_ou`) it is
  `ProbabilityFlowOUMoment.transportKLRegularity_ou_moment`, and the FL-2 decay theorem is
  instantiated there (`klDecay_of_idealVelocity_local_ou_moment`); with only a finite second
  (resp. third) moment some of its fields fail, as shown by the counterexamples in
  `ProbabilityFlowOUCounterexample` (`not_integrable_flux_log_rhoGeom`,
  `not_transportKLRegularity_rhoGeom_sixteenth`). The unconditional FL-1/FL-2/FL-4 above for a
  general `ρ` go through the heat flow instead and do not use `TransportKLRegularity`.
* The Lagrangian probability-flow ODE `ẋ = v_t(x)` is not constructed; only the Eulerian
  continuity equation is proved. Uniqueness of the continuity-equation solution, and any link
  to SDE path laws, are not proved. Only the isotropic Gaussian target is treated.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProbabilityFlowOU

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi
open FormalizeSampling.GaussianLSIPi (heatFlowDensityPi_gaussian heatFlowGradPi_gaussian
  heatKernelPi_comp_pi_gaussianReal)
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi
  integrable_sum_sq_map_scalePi)

variable {d : ℕ}

/-! ### The heat kernel along a curve -/

/-- Closed exponential form of the heat kernel for a positive variance. -/
theorem heatDensityPi_eq_exp_log {S : ℝ} (hS : 0 < S) (z : Fin d → ℝ) :
    heatDensityPi S z =
      Real.exp (-(d / 2) * Real.log (2 * Real.pi * S) - (∑ i, z i ^ 2) / (2 * S)) := by
  have hX : 0 < 2 * Real.pi * S := by positivity
  rw [heatDensityPi_eq_exp, sub_eq_add_neg, Real.exp_add]
  congr 1
  · rw [← Real.exp_log (Real.sqrt_pos.2 hX), Real.log_sqrt hX.le, ← Real.exp_neg,
      ← Real.exp_nat_mul]
    congr 1
    ring
  · congr 1
    ring

/-- **Heat kernel along a curve.** If `S` has derivative `S'` at `r` with `S r > 0` and the
curve `z` has derivative `z'` at `r`, then `u ↦ φ_{S u}(z u)` has derivative
`Δφ_{S r}(z r) / 2 · S' + ∇φ_{S r}(z r) ⬝ᵥ z'` at `r`. -/
theorem hasDerivAt_heatDensityPi_comp {S : ℝ → ℝ} {z : ℝ → Fin d → ℝ} {S' r : ℝ}
    {z' : Fin d → ℝ} (hS : HasDerivAt S S' r) (hS0 : 0 < S r) (hz : HasDerivAt z z' r) :
    HasDerivAt (fun u => heatDensityPi (S u) (z u))
      (heatLapPi (S r) (z r) / 2 * S' + heatGradPi (S r) (z r) ⬝ᵥ z') r := by
  have hev : ∀ᶠ u in 𝓝 r, 0 < S u := hS.continuousAt.eventually (lt_mem_nhds hS0)
  have hX : 0 < 2 * Real.pi * S r := by positivity
  have h1 := ((hS.const_mul (2 * Real.pi)).log hX.ne').const_mul (-(d / 2 : ℝ))
  have hzi : ∀ i, HasDerivAt (fun u => z u i ^ 2) (2 * z r i * z' i) r := by
    intro i
    have := ((hasDerivAt_pi.1 hz) i).fun_pow 2
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hzi i
  have h3 := h2.div (hS.const_mul 2) (by positivity)
  have h4 := (h1.sub h3).exp
  refine (h4.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hev] with u hu
    exact heatDensityPi_eq_exp_log hu (z u)
  · simp only [Pi.sub_apply, Pi.div_apply]
    rw [← heatDensityPi_eq_exp_log hS0, heatLapPi_eq]
    set φ := heatDensityPi (S r) (z r)
    have e1 : ∑ i, (z r i ^ 2 / S r ^ 2 - 1 / S r) * φ =
        ((∑ i, z r i ^ 2) / S r ^ 2 - d / S r) * φ := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_div]
      simp [div_eq_mul_inv]
    have e2 : heatGradPi (S r) (z r) ⬝ᵥ z' = -((∑ i, z r i * z' i) / S r) * φ := by
      simp only [dotProduct, heatGradPi, Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∑ i, 2 * z r i * z' i = 2 * ∑ i, z r i * z' i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, e3]
    field_simp
    ring

/-! ### The OU marginals -/

/-- The OU contraction factor `c_t = e^{-at}`. -/
noncomputable def ouC (a t : ℝ) : ℝ := Real.exp (-a * t)

/-- The OU noise variance `s_t = v (1 - e^{-2at})`. -/
noncomputable def ouS (v a t : ℝ) : ℝ := v * (1 - Real.exp (-2 * a * t))

/-- The scaled initial law `ρ.map (c_t • ·)`. -/
noncomputable def ouLaw (ρ : Measure (Fin d → ℝ)) (a t : ℝ) : Measure (Fin d → ℝ) :=
  ρ.map (scalePi (ouC a t))

/-- The OU marginal density `p_t = (c_t ρ) * N(0, s_t I)`, i.e. the law of
`e^{-at} X₀ + √(v (1 - e^{-2at})) Z` with `X₀ ∼ ρ`, `Z ∼ N(0, I)` independent. -/
noncomputable def ouDensity (ρ : Measure (Fin d → ℝ)) (v a t : ℝ) (x : Fin d → ℝ) : ℝ :=
  heatFlowDensityPi (ouLaw ρ a t) (ouS v a t) x

/-- The gradient `∇p_t` of the OU marginal density (`hasFDerivAt_ouDensity`). -/
noncomputable def ouGrad (ρ : Measure (Fin d → ℝ)) (v a t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  heatFlowGradPi (ouLaw ρ a t) (ouS v a t) x

/-- The Laplacian `Δp_t` of the OU marginal density. -/
noncomputable def ouLap (ρ : Measure (Fin d → ℝ)) (v a t : ℝ) (x : Fin d → ℝ) : ℝ :=
  heatFlowLapPi (ouLaw ρ a t) (ouS v a t) x

/-- `c_t > 0`. -/
theorem ouC_pos (a t : ℝ) : 0 < ouC a t := Real.exp_pos _

/-- `s_t > 0` for `v, a, t > 0`. -/
theorem ouS_pos {v a t : ℝ} (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) : 0 < ouS v a t := by
  unfold ouS
  have : Real.exp (-2 * a * t) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  nlinarith

/-- `s_t ≤ v`. -/
theorem ouS_le {v a t : ℝ} (hv : 0 < v) : ouS v a t ≤ v := by
  unfold ouS
  nlinarith [Real.exp_pos (-2 * a * t)]

/-- `t ↦ s_t` is monotone (`v, a > 0`). -/
theorem ouS_mono {v a s t : ℝ} (hv : 0 < v) (ha : 0 < a) (hst : s ≤ t) :
    ouS v a s ≤ ouS v a t := by
  unfold ouS
  have : Real.exp (-2 * a * t) ≤ Real.exp (-2 * a * s) := Real.exp_le_exp.2 (by nlinarith)
  nlinarith

/-- `c_t' = -a c_t`. -/
theorem hasDerivAt_ouC (a t : ℝ) : HasDerivAt (ouC a) (-a * ouC a t) t := by
  have := ((hasDerivAt_id' t).const_mul (-a)).exp
  unfold ouC
  convert this using 1
  ring

/-- `s_t' = 2a (v - s_t)`. -/
theorem hasDerivAt_ouS (v a t : ℝ) : HasDerivAt (ouS v a) (2 * a * (v - ouS v a t)) t := by
  have := (((hasDerivAt_id' t).const_mul (-2 * a)).exp.const_sub 1).const_mul v
  unfold ouS
  convert this using 1
  ring

/-- The scaled law of a probability law is a probability law. -/
instance isProbabilityMeasure_ouLaw (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]
    (a t : ℝ) : IsProbabilityMeasure (ouLaw ρ a t) := by
  unfold ouLaw
  infer_instance

/-- Integrals against the scaled law are integrals against `ρ`. -/
theorem integral_ouLaw (ρ : Measure (Fin d → ℝ)) (a t : ℝ) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) : ∫ w, f w ∂(ouLaw ρ a t) = ∫ y, f (scalePi (ouC a t) y) ∂ρ :=
  integral_map (measurable_scalePi _).aemeasurable hf.aestronglyMeasurable

section Time

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- The pointwise kernel identity behind the OU Fokker–Planck equation: with `z = x - c y`,
`s' = 2a(v - s)` and `z' = a c y`,
`Δφ_s(z)/2 · s' + ∇φ_s(z) ⬝ᵥ z' = a (d φ_s(z) + x ⬝ᵥ ∇φ_s(z) + v Δφ_s(z))`. -/
theorem kernel_identity {v a s c : ℝ} (hs : 0 < s) (x y : Fin d → ℝ) :
    heatLapPi s (x - scalePi c y) / 2 * (2 * a * (v - s)) +
        heatGradPi s (x - scalePi c y) ⬝ᵥ (fun i => a * c * y i) =
      a * (d * heatDensityPi s (x - scalePi c y) + x ⬝ᵥ heatGradPi s (x - scalePi c y) +
        v * heatLapPi s (x - scalePi c y)) := by
  set z := x - scalePi c y with hz
  have hx : ∀ i, x i = z i + c * y i := fun i => by simp [hz, scalePi]
  set φ := heatDensityPi s z
  set A := ∑ i, z i ^ 2
  set B := ∑ i, z i * y i
  have e1 : heatLapPi s z = (A / s ^ 2 - d / s) * φ := by
    rw [heatLapPi_eq, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp [div_eq_mul_inv, A, φ]
  have e2 : heatGradPi s z ⬝ᵥ (fun i => a * c * y i) = -(a * c * B / s) * φ := by
    simp only [dotProduct, heatGradPi, B, Finset.mul_sum, Finset.sum_div, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : x ⬝ᵥ heatGradPi s z = -((A + c * B) / s) * φ := by
    simp only [dotProduct, heatGradPi, A, B, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hx i]; ring
  rw [e1, e2, e3]
  field_simp
  ring

omit [IsProbabilityMeasure ρ] in
/-- `p_t(x) = ∫ φ_{s_t}(x - c_t y) dρ(y)`. -/
theorem ouDensity_eq_integral (v a t : ℝ) (x : Fin d → ℝ) :
    ouDensity ρ v a t x = ∫ y, heatDensityPi (ouS v a t) (x - scalePi (ouC a t) y) ∂ρ :=
  integral_ouLaw ρ a t ((continuous_heatDensityPi _).comp (by fun_prop))

/-- A bounded continuous function composed with a continuous map is `ρ`-integrable. -/
theorem integrable_comp_of_bound {k : (Fin d → ℝ) → ℝ} (hk : Continuous k) {B : ℝ}
    (hB : ∀ z, |k z| ≤ B) {f : (Fin d → ℝ) → Fin d → ℝ} (hf : Continuous f) :
    Integrable (fun y => k (f y)) ρ :=
  Integrable.of_bound (hk.comp hf).aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB _)

/-- Under a finite second moment every coordinate `|yᵢ|` is `ρ`-integrable. -/
theorem integrable_abs_coord (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (i : Fin d) :
    Integrable (fun y : Fin d → ℝ => |y i|) ρ :=
  ((integrable_const (1 : ℝ)).add hmom).mono'
    (continuous_abs.comp (continuous_apply i)).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_le_one_add_sum_sq y i)

/-- **OU Fokker–Planck equation for the marginal densities.** For a probability law `ρ` with
finite second moment, `v, a > 0`, `t > 0` and every `x`,
`∂ₜ p_t(x) = a (d p_t(x) + x ⬝ᵥ ∇p_t(x) + v Δp_t(x)) = a (div(x p_t) + v Δp_t)(x)`. -/
theorem hasDerivAt_ouDensity_t {v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    HasDerivAt (fun s => ouDensity ρ v a s x)
      (a * (d * ouDensity ρ v a t x + x ⬝ᵥ ouGrad ρ v a t x + v * ouLap ρ v a t x)) t := by
  set S₀ := ouS v a (t / 2)
  have hS₀ : 0 < S₀ := ouS_pos hv ha (by linarith)
  have hSge : ∀ u ∈ Ioi (t / 2), S₀ ≤ ouS v a u := fun u hu => ouS_mono hv ha (le_of_lt hu)
  have hSpos : ∀ u ∈ Ioi (t / 2), 0 < ouS v a u := fun u hu => hS₀.trans_le (hSge u hu)
  set F : ℝ → (Fin d → ℝ) → ℝ := fun u y => heatDensityPi (ouS v a u) (x - scalePi (ouC a u) y)
  set F' : ℝ → (Fin d → ℝ) → ℝ := fun u y =>
    heatLapPi (ouS v a u) (x - scalePi (ouC a u) y) / 2 * (2 * a * (v - ouS v a u)) +
      heatGradPi (ouS v a u) (x - scalePi (ouC a u) y) ⬝ᵥ (fun i => a * ouC a u * y i)
  have hz : ∀ u y, HasDerivAt (fun u => x - scalePi (ouC a u) y)
      (fun i => a * ouC a u * y i) u := by
    intro u y
    refine hasDerivAt_pi.2 fun i => ?_
    have := ((hasDerivAt_ouC a u).mul_const (y i)).const_sub (x i)
    convert this using 1
    · funext w; simp [scalePi]
    · ring
  have hderiv : ∀ u ∈ Ioi (t / 2), ∀ y, HasDerivAt (fun u => F u y) (F' u y) u :=
    fun u hu y => hasDerivAt_heatDensityPi_comp (hasDerivAt_ouS v a u) (hSpos u hu) (hz u y)
  set K := gc d S₀
  set bound : (Fin d → ℝ) → ℝ := fun y =>
    d * (3 / S₀ * K) / 2 * (2 * a * v) + ∑ i, (1 + 2 * v) / S₀ * K * (a * |y i|)
  have hK : 0 ≤ K := (gc_pos hS₀).le
  have hbound : ∀ u ∈ Ioi (t / 2), ∀ y, ‖F' u y‖ ≤ bound y := by
    intro u hu y
    have hS := hSpos u hu
    have hS1 := hSge u hu
    have hSv := ouS_le (a := a) (t := u) hv
    have hgc : gc d (ouS v a u) ≤ K := gc_anti hS₀ hS1
    have hc1 : ouC a u ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hu.out, ha])
    have hc0 := (ouC_pos a u).le
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_div, abs_two]
      have h1 := abs_heatLapPi_le hS (x - scalePi (ouC a u) y)
      change |heatLapPi _ _| ≤ d * (3 / ouS v a u * gc d (ouS v a u)) at h1
      have h2 : |2 * a * (v - ouS v a u)| ≤ 2 * a * v := by
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
      have h3 : 3 / ouS v a u * gc d (ouS v a u) ≤ 3 / S₀ * K := by
        gcongr
        exact (gc_pos hS).le
      have h4 : (d : ℝ) * (3 / ouS v a u * gc d (ouS v a u)) ≤ d * (3 / S₀ * K) :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
      have h5 : 0 ≤ |heatLapPi (ouS v a u) (x - scalePi (ouC a u) y)| := abs_nonneg _
      have h6 : 0 ≤ 2 * a * v := by positivity
      exact mul_le_mul (div_le_div_of_nonneg_right (h1.trans h4) two_pos.le) h2 (abs_nonneg _)
        (by positivity)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      have h1 := abs_heatGradPi_le hS (x - scalePi (ouC a u) y) i
      change |heatGradPi _ _ i| ≤ (1 + 2 * ouS v a u) / ouS v a u * gc d (ouS v a u) at h1
      have h3 : (1 + 2 * ouS v a u) / ouS v a u * gc d (ouS v a u) ≤ (1 + 2 * v) / S₀ * K := by
        gcongr
        exact (gc_pos hS).le
      have h4 : |a * ouC a u * y i| ≤ a * |y i| := by
        rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_nonneg hc0]
        calc a * ouC a u * |y i| ≤ a * 1 * |y i| := by gcongr
          _ = a * |y i| := by ring
      exact mul_le_mul (h1.trans h3) h4 (abs_nonneg _) (by positivity)
  have hbint : Integrable bound ρ :=
    (integrable_const _).add (integrable_finsetSum _ fun i _ =>
      ((integrable_abs_coord ρ hmom i).const_mul a).const_mul _)
  have hmemt : t ∈ Ioi (t / 2) := by simp only [mem_Ioi]; linarith
  have hS := hSpos t hmemt
  have hcont : ∀ u, Continuous (F u) := fun u =>
    (continuous_heatDensityPi _).comp (by unfold scalePi; fun_prop)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) (F := F) (F' := F')
    (x₀ := t) (bound := bound) (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall fun u => (hcont u).aestronglyMeasurable)
    (integrable_comp_of_bound ρ (continuous_heatDensityPi _)
      (fun z => by rw [abs_of_pos (heatDensityPi_pos hS z)]; exact heatDensityPi_le hS z)
      (by unfold scalePi; fun_prop))
    (by
      refine Continuous.aestronglyMeasurable ?_
      simp only [F', dotProduct]
      have := continuous_heatLapPi (d := d) (ouS v a t)
      have := continuous_heatGradPi (d := d) (ouS v a t)
      unfold scalePi
      fun_prop)
    (Eventually.of_forall fun y u hu => hbound u hu y) hbint
    (Eventually.of_forall fun y u hu => hderiv u hu y)
  have hfun : (fun s => ouDensity ρ v a s x) = fun u => ∫ y, F u y ∂ρ :=
    funext fun u => ouDensity_eq_integral ρ v a u x
  rw [hfun]
  refine hD.congr_deriv ?_
  -- evaluate the integral of the derivative
  set S := ouS v a t
  set c := ouC a t
  have hφ : Integrable (fun y => heatDensityPi S (x - scalePi c y)) ρ :=
    integrable_comp_of_bound ρ (continuous_heatDensityPi _)
      (fun z => by rw [abs_of_pos (heatDensityPi_pos hS z)]; exact heatDensityPi_le hS z)
      (by unfold scalePi; fun_prop)
  have hG : ∀ i, Integrable (fun y => heatGradPi S (x - scalePi c y) i) ρ := fun i =>
    integrable_comp_of_bound ρ ((continuous_apply i).comp (continuous_heatGradPi S))
      (fun z => abs_heatGradPi_le hS z i) (by unfold scalePi; fun_prop)
  have hH : ∀ i, Integrable (fun y => heatHessPi S (x - scalePi c y) i i) ρ := fun i =>
    integrable_comp_of_bound ρ (continuous_heatHessPi S i i)
      (fun z => abs_heatHessPi_le hS z i i) (by unfold scalePi; fun_prop)
  have e1 : (fun y => F' t y) = fun y =>
      a * (d * heatDensityPi S (x - scalePi c y) +
        ∑ i, x i * heatGradPi S (x - scalePi c y) i +
        v * ∑ i, heatHessPi S (x - scalePi c y) i i) := by
    funext y
    simp only [F']
    rw [kernel_identity hS x y]
    rfl
  have eG : ∀ i, ouGrad ρ v a t x i = ∫ y, heatGradPi S (x - scalePi c y) i ∂ρ := fun i =>
    integral_ouLaw ρ a t (((continuous_apply i).comp (continuous_heatGradPi S)).comp
      (by fun_prop))
  have eH : ∀ i, heatFlowHessPi (ouLaw ρ a t) S x i i =
      ∫ y, heatHessPi S (x - scalePi c y) i i ∂ρ := fun i =>
    integral_ouLaw ρ a t ((continuous_heatHessPi S i i).comp (by fun_prop))
  rw [e1, integral_const_mul, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_finsetSum, integral_finsetSum, ← ouDensity_eq_integral]
  · simp only [integral_const_mul, dotProduct, ouLap, heatFlowLapPi, eG]
    rw [show ouS v a t = S from rfl]
    simp only [eH]
  all_goals first
    | exact fun i _ => hH i
    | exact fun i _ => (hG i).const_mul _
    | exact hφ.const_mul _
    | exact integrable_finsetSum _ fun i _ => (hG i).const_mul _
    | exact (integrable_finsetSum _ fun i _ => hH i).const_mul _
    | exact (hφ.const_mul _).add (integrable_finsetSum _ fun i _ => (hG i).const_mul _)

end Time

/-! ### Space derivatives, the ideal velocity and the continuity equation -/

section Space

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- The ideal (probability-flow) velocity `v_t(x) = a v (∇log π(x) - ∇log p_t(x))` of the OU
dynamics, with `π = N(0, v I)` of density `heatDensityPi v`. -/
noncomputable def ouVelocity (ρ : Measure (Fin d → ℝ)) (v a t : ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ :=
  (a * v) • (score (heatDensityPi v) x - score (ouDensity ρ v a t) x)

/-- `p_t` has gradient `ouGrad` (`t > 0`). -/
theorem hasFDerivAt_ouDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (x : Fin d → ℝ) :
    HasFDerivAt (ouDensity ρ v a t) (dotCLM (ouGrad ρ v a t x)) x :=
  hasFDerivAt_heatFlowDensityPi (ouLaw ρ a t) (ouS_pos hv ha ht) x

/-- Each coordinate of `ouGrad` has gradient the corresponding Hessian row (`t > 0`). -/
theorem hasFDerivAt_ouGrad (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (i : Fin d)
    (x : Fin d → ℝ) :
    HasFDerivAt (fun y => ouGrad ρ v a t y i)
      (dotCLM fun j => heatFlowHessPi (ouLaw ρ a t) (ouS v a t) x i j) x :=
  hasFDerivAt_heatFlowGradPi (ouLaw ρ a t) (ouS_pos hv ha ht) i x

/-- `p_t > 0` (`t > 0`). -/
theorem ouDensity_pos (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (x : Fin d → ℝ) :
    0 < ouDensity ρ v a t x :=
  heatFlowDensityPi_pos (ouLaw ρ a t) (ouS_pos hv ha ht) x

/-- `p_t` is continuous (`t > 0`). -/
theorem continuous_ouDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) :
    Continuous (ouDensity ρ v a t) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_ouDensity ρ hv ha ht x).continuousAt

/-- The coordinates of `∇p_t` are continuous (`t > 0`). -/
theorem continuous_ouGrad (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (i : Fin d) :
    Continuous fun x => ouGrad ρ v a t x i :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_ouGrad ρ hv ha ht i x).continuousAt

/-- The score of `p_t` is `∇p_t / p_t` (`t > 0`). -/
theorem score_ouDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (x : Fin d → ℝ) (i : Fin d) :
    score (ouDensity ρ v a t) x i = ouGrad ρ v a t x i / ouDensity ρ v a t x := by
  rw [score_apply_of_pos (hasFDerivAt_ouDensity ρ hv ha ht x).differentiableAt
    (ouDensity_pos ρ hv ha ht x), partialDeriv, (hasFDerivAt_ouDensity ρ hv ha ht x).fderiv,
    dotCLM_single]

omit [IsProbabilityMeasure ρ] in
/-- The score of `N(0, v I)` is `x ↦ -x / v`. -/
theorem score_heatDensityPi (hv : 0 < v) (x : Fin d → ℝ) (i : Fin d) :
    score (heatDensityPi v) x i = -(x i / v) := by
  rw [score_apply_of_pos (hasFDerivAt_heatDensityPi v x).differentiableAt
    (heatDensityPi_pos hv x), partialDeriv, (hasFDerivAt_heatDensityPi v x).fderiv,
    dotCLM_single, heatGradPi_div hv]

/-- The probability flux: `p_t v_t = -a (x p_t + v ∇p_t)` (`t > 0`). -/
theorem ouDensity_mul_ouVelocity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (x : Fin d → ℝ)
    (i : Fin d) :
    ouDensity ρ v a t x * ouVelocity ρ v a t x i =
      -a * (x i * ouDensity ρ v a t x + v * ouGrad ρ v a t x i) := by
  have hp := ouDensity_pos ρ hv ha ht x
  simp only [ouVelocity, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    score_heatDensityPi hv, score_ouDensity ρ hv ha ht]
  field_simp
  ring

/-- **Divergence of the probability flux.** For `t > 0`,
`div(p_t v_t)(x) = -a (d p_t(x) + x ⬝ᵥ ∇p_t(x) + v Δp_t(x))`. -/
theorem divergence_ouFlux (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (x : Fin d → ℝ) :
    divergence (fun y => ouDensity ρ v a t y • ouVelocity ρ v a t y) x =
      -(a * (d * ouDensity ρ v a t x + x ⬝ᵥ ouGrad ρ v a t x + v * ouLap ρ v a t x)) := by
  have hi : ∀ i, partialDeriv i (fun y => (ouDensity ρ v a t y • ouVelocity ρ v a t y) i) x =
      -a * (ouDensity ρ v a t x + x i * ouGrad ρ v a t x i +
        v * heatFlowHessPi (ouLaw ρ a t) (ouS v a t) x i i) := by
    intro i
    have e : (fun y => (ouDensity ρ v a t y • ouVelocity ρ v a t y) i) =
        fun y => -a * (y i * ouDensity ρ v a t y + v * ouGrad ρ v a t y i) := by
      funext y
      rw [Pi.smul_apply, smul_eq_mul, ouDensity_mul_ouVelocity ρ hv ha ht]
    have h := (((hasFDerivAt_apply (𝕜 := ℝ) i x).mul (hasFDerivAt_ouDensity ρ hv ha ht x)).add
      ((hasFDerivAt_ouGrad ρ hv ha ht i x).const_mul v)).const_mul (-a)
    have h' : HasFDerivAt (fun y => -a * (y i * ouDensity ρ v a t y + v * ouGrad ρ v a t y i))
        _ x := h
    rw [e, partialDeriv, h'.fderiv]
    simp only [smul_apply, add_apply, dotCLM_single,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul]
    ring
  rw [divergence]
  simp only [hi, dotProduct, ouLap, heatFlowLapPi]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- **Strong continuity equation for the OU probability flow (`t > 0`).** For a probability
law `ρ` with finite second moment and `v, a > 0`, the OU marginals solve
`∂ₜ p_t(x) = -div(p_t v_t)(x)` with the ideal velocity `v_t = a v (∇log π - ∇log p_t)`, for every
`t > 0` and `x`. -/
theorem hasDerivAt_ouDensity_continuity (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (ht : 0 < t) (x : Fin d → ℝ) :
    HasDerivAt (fun s => ouDensity ρ v a s x)
      (-(divergence (fun y => ouDensity ρ v a t y • ouVelocity ρ v a t y) x)) t := by
  rw [divergence_ouFlux ρ hv ha ht, neg_neg]
  exact hasDerivAt_ouDensity_t ρ hv ha hmom ht x

end Space

/-! ### The Gaussian-LSI hypotheses along the flow -/

section LSI

open FormalizeSampling.LogSobolevAlongGaussian

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- The residual Gaussian variance `v e^{-2at}`, so that `v e^{-2at} + s_t = v`. -/
theorem add_ouS (v a t : ℝ) : v * Real.exp (-2 * a * t) + ouS v a t = v := by
  unfold ouS; ring

omit [IsProbabilityMeasure ρ] in
/-- Second moment of the scaled initial law. -/
theorem integrable_sum_sq_ouLaw (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (a t : ℝ) :
    Integrable (fun x => ∑ i, x i ^ 2) (ouLaw ρ a t) :=
  integrable_sum_sq_map_scalePi ρ hmom _

/-- The heat-flow regularity of the scaled law against `N(0, v e^{-2at} I)`. -/
theorem heatFlowRegularPi_ouLaw (hv : 0 < v) (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ)
    (a t : ℝ) :
    HeatFlowRegularPi (ouLaw ρ a t)
      (Measure.pi fun _ : Fin d => gaussianReal 0 (v * Real.exp (-2 * a * t)).toNNReal)
      (Ioi 0) :=
  heatFlowRegularPi_gaussian _ (integrable_sum_sq_ouLaw ρ hmom a t) (by positivity)

/-- The relative Fisher integrand of `p_t` against `N(0, v I)` is integrable (`t > 0`). -/
theorem integrable_ouFisher (hv : 0 < v) (ha : 0 < a) (ht : 0 < t)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    Integrable fun x => ouDensity ρ v a t x *
      ∑ i, (ouGrad ρ v a t x i / ouDensity ρ v a t x + x i / v) ^ 2 := by
  have hS := ouS_pos hv ha ht
  have hw : 0 < v * Real.exp (-2 * a * t) := by positivity
  have key := (heatFlowRegularPi_ouLaw ρ hv hmom a t).integrable_fisher (ouS v a t) hS
  refine key.congr (Eventually.of_forall fun x => ?_)
  simp only [fisherIntegrand, relScore, dotProduct, heatFlowDensityPi_gaussian hw hS,
    heatFlowGradPi_gaussian hw hS, add_ouS, ouDensity, ouGrad]
  simp only [heatGradPi_div hv]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The KL integrand `p_t log(p_t / φ_v)` is integrable (`t > 0`). -/
theorem integrable_ouKL (hv : 0 < v) (ha : 0 < a) (ht : 0 < t)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    Integrable fun x => ouDensity ρ v a t x *
      Real.log (ouDensity ρ v a t x / heatDensityPi v x) := by
  have hS := ouS_pos hv ha ht
  have hw : 0 < v * Real.exp (-2 * a * t) := by positivity
  have key := (heatFlowRegularPi_ouLaw ρ hv hmom a t).integrable_kl (ouS v a t) hS
  refine key.congr (Eventually.of_forall fun x => ?_)
  simp only [klIntegrand, heatFlowDensityPi_gaussian hw hS, add_ouS, ouDensity]

/-- `p_t` has a finite second moment (`t > 0`). -/
theorem integrable_ouMoment (hv : 0 < v) (ha : 0 < a) (ht : 0 < t)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    Integrable fun x => (∑ i, x i ^ 2) * ouDensity ρ v a t x := by
  have hS := ouS_pos hv ha ht
  have hm := integrable_sum_sq_ouLaw ρ hmom a t
  refine ((integrable_envBound hm (by positivity : 0 < 2 * ouS v a t)).const_mul
    (2 * 1 * envK d (ouS v a t) (ouS v a t))).mono'
    ((continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2).mul
      (continuous_ouDensity ρ hv ha ht)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have h1 := one_add_mul_heatFlowDensityPi_le hm hS le_rfl le_rfl x
  have h2 := sum_sq_nonneg x
  have h3 := (ouDensity_pos ρ hv ha ht x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h3)]
  change _ ≤ 2 * 1 * envK d (ouS v a t) (ouS v a t) * envBound (ouLaw ρ a t) (2 * ouS v a t) x
  change (1 + ∑ i, x i ^ 2) * ouDensity ρ v a t x ≤ _ at h1
  nlinarith

/-- **`GaussianDensityHyp` along the OU flow (Verified).** For a probability law `ρ` with
finite second moment, `v, a > 0` and every `t > 0`, the OU marginal density `p_t` with its
gradient `ouGrad` satisfies every per-time hypothesis of the Gaussian LSI
(`LogSobolevAlongGaussian.GaussianDensityHyp`) against `N(0, v I)`. -/
theorem gaussianDensityHyp_ouDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    GaussianDensityHyp (ouDensity ρ v a t) (ouGrad ρ v a t) v where
  prob := isProbabilityMeasure_withDensity_heatFlowDensityPi (ouLaw ρ a t) (ouS_pos hv ha ht)
  pos := ouDensity_pos ρ hv ha ht
  hasFDerivAt := hasFDerivAt_ouDensity ρ hv ha ht
  moment := integrable_ouMoment ρ hv ha ht hmom
  fisher := integrable_ouFisher ρ hv ha ht hmom

end LSI

/-! ### Reduction of the KL divergence to the heat flow -/

section KL

open FormalizeSampling.LogSobolevAlongGaussian

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- The heat-flow time `τ_t = v (e^{2at} - 1)`, so that `s_t = c_t² τ_t`. -/
noncomputable def ouTau (v a t : ℝ) : ℝ := v * (Real.exp (2 * a * t) - 1)

/-- `τ_t > 0` for `v, a, t > 0`. -/
theorem ouTau_pos (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) : 0 < ouTau v a t := by
  unfold ouTau
  have : 1 < Real.exp (2 * a * t) := Real.one_lt_exp_iff.2 (by positivity)
  nlinarith

/-- `c_t² = e^{-2at}`. -/
theorem ouC_sq (a t : ℝ) : ouC a t ^ 2 = Real.exp (-2 * a * t) :=
  OULangevinDecay.exp_neg_mul_sq a t

/-- `c_t² e^{2at} = 1`. -/
theorem ouC_sq_mul_exp (a t : ℝ) : ouC a t ^ 2 * Real.exp (2 * a * t) = 1 := by
  rw [ouC_sq, ← Real.exp_add]; simp

/-- `s_t = c_t² τ_t`. -/
theorem ouS_eq (v a t : ℝ) : ouS v a t = ouC a t ^ 2 * ouTau v a t := by
  unfold ouS ouTau
  have := ouC_sq_mul_exp a t
  rw [ouC_sq] at this ⊢
  linear_combination (-v) * this

/-- `c_t² (v + τ_t) = v`. -/
theorem ouC_sq_mul_add_ouTau (v a t : ℝ) : ouC a t ^ 2 * (v + ouTau v a t) = v := by
  unfold ouTau
  have := ouC_sq_mul_exp a t
  linear_combination v * this

/-- `τ_t' = 2 a v e^{2at}`. -/
theorem hasDerivAt_ouTau (v a t : ℝ) :
    HasDerivAt (ouTau v a) (2 * a * v * Real.exp (2 * a * t)) t := by
  have := (((hasDerivAt_id' t).const_mul (2 * a)).exp.sub_const 1).const_mul v
  unfold ouTau
  convert this using 1
  ring

/-- The law of `p_t` is the OU marginal of `OULangevinDecayPi`:
`p_t dx = ouKernelVarPi v a t ∘ₘ ρ` (`t > 0`). -/
theorem lawOf_ouDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) :
    lawOf (ouDensity ρ v a t) = OULangevinDecayPi.ouKernelVarPi v a t ∘ₘ ρ := by
  rw [OULangevinDecayPi.ouKernelVarPi_comp_eq]
  exact (heatKernelPi_comp_eq_withDensity (ouLaw ρ a t) (ouS_pos hv ha ht)).symm

omit [IsProbabilityMeasure ρ] in
/-- Heat flow commutes with scaling: `H_{c² τ} ∘ (c ·)_# μ = (c ·)_# (H_τ ∘ μ)`. -/
theorem heatKernelPi_comp_map_scalePi (c : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (μ : Measure (Fin d → ℝ)) :
    heatKernelPi (c ^ 2 * τ).toNNReal ∘ₘ μ.map (scalePi c) =
      (heatKernelPi τ.toNNReal ∘ₘ μ).map (scalePi c) := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hA) (measurable_scalePi c),
    Measure.map_apply (measurable_scalePi c) hA,
    Measure.bind_apply (measurable_scalePi c hA) (Kernel.aemeasurable _)]
  refine lintegral_congr fun y => ?_
  rw [← Measure.map_apply (measurable_scalePi c) hA, heatKernelPi_apply, heatKernelPi_apply,
    OULangevinDecayPi.pi_gaussianReal_map_scalePi c hτ]
  rfl

omit [IsProbabilityMeasure ρ] in
/-- KL is invariant under a nonzero scaling. -/
theorem klDiv_map_scalePi {c : ℝ} (hc : c ≠ 0) (μ ν : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    klDiv (μ.map (scalePi c)) (ν.map (scalePi c)) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν (measurable_scalePi c)) ?_
  have h := klDiv_map_le (μ.map (scalePi c)) (ν.map (scalePi c)) (measurable_scalePi c⁻¹)
  have hid : scalePi (d := d) c⁻¹ ∘ scalePi c = id := by
    funext x i; simp [scalePi, hc]
  rwa [Measure.map_map (measurable_scalePi _) (measurable_scalePi _),
    Measure.map_map (measurable_scalePi _) (measurable_scalePi _), hid, Measure.map_id,
    Measure.map_id] at h

/-- **KL along the OU flow is the heat-flow KL.** For `t > 0`,
`KL(p_t dx ‖ N(0, v I)) = KL(ρ * N(0, τ_t I) ‖ N(0, v I) * N(0, τ_t I))` with
`τ_t = v (e^{2at} - 1)` (scale both laws by `e^{at}`). -/
theorem gaussKL_ouDensity_eq (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) :
    gaussKL (ouDensity ρ v a) v t = heatKL ρ (gaussPi d v) (ouTau v a t) := by
  have hτ := ouTau_pos hv ha ht
  have hc := ouC_pos a t
  have hlaw : lawOf (ouDensity ρ v a t) =
      (heatKernelPi (ouTau v a t).toNNReal ∘ₘ ρ).map (scalePi (ouC a t)) := by
    rw [lawOf]
    unfold ouDensity
    rw [← heatKernelPi_comp_eq_withDensity (ouLaw ρ a t) (ouS_pos hv ha ht),
      ouS_eq, ouLaw, heatKernelPi_comp_map_scalePi _ hτ.le]
  have htarget : gaussTarget (d := d) v =
      (heatKernelPi (ouTau v a t).toNNReal ∘ₘ gaussPi d v).map (scalePi (ouC a t)) := by
    rw [heatKernelPi_comp_pi_gaussianReal hv.le hτ.le]
    have h := OULangevinDecayPi.pi_gaussianReal_map_scalePi (d := d) (ouC a t)
      (by positivity : 0 ≤ v + ouTau v a t) 0
    simp only [Pi.zero_apply, mul_zero, ouC_sq_mul_add_ouTau] at h
    rw [h]
    rfl
  rw [gaussKL, hlaw, htarget, klDiv_map_scalePi hc.ne', heatKL]

omit [IsProbabilityMeasure ρ] in
/-- Scaling of the heat kernel: `φ_{c² τ}(c z) = c^{-d} φ_τ(z)` (`c, τ > 0`). -/
theorem heatDensityPi_scale {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (z : Fin d → ℝ) :
    heatDensityPi (c ^ 2 * τ) (scalePi c z) = (c ^ d)⁻¹ * heatDensityPi τ z := by
  rw [heatDensityPi_eq_exp, heatDensityPi_eq_exp]
  have hs : Real.sqrt (2 * Real.pi * (c ^ 2 * τ)) = c * Real.sqrt (2 * Real.pi * τ) := by
    rw [show 2 * Real.pi * (c ^ 2 * τ) = c ^ 2 * (2 * Real.pi * τ) by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have he : (∑ i, scalePi c z i ^ 2) / (2 * (c ^ 2 * τ)) = (∑ i, z i ^ 2) / (2 * τ) := by
    simp only [scalePi, mul_pow, ← Finset.mul_sum]
    field_simp
  rw [hs, neg_div, neg_div, he, mul_inv, mul_pow, inv_pow]
  ring

omit [IsProbabilityMeasure ρ] in
/-- Scaling of the heat-kernel gradient: `∇φ_{c² τ}(c z) = c^{-d} c⁻¹ ∇φ_τ(z)`. -/
theorem heatGradPi_scale {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (z : Fin d → ℝ) (i : Fin d) :
    heatGradPi (c ^ 2 * τ) (scalePi c z) i = (c ^ d)⁻¹ * c⁻¹ * heatGradPi τ z i := by
  rw [heatGradPi, heatGradPi, heatDensityPi_scale hc hτ]
  simp only [scalePi]
  field_simp

omit [IsProbabilityMeasure ρ] in
/-- `c y - c y' = c (y - y')`. -/
theorem scalePi_sub (c : ℝ) (y y' : Fin d → ℝ) :
    scalePi c y - scalePi c y' = scalePi c (y - y') := by
  funext i; simp [scalePi, mul_sub]

omit [IsProbabilityMeasure ρ] in
/-- `p_t(c_t y) = c_t^{-d} q_{τ_t}(y)` with `q_τ = ρ * N(0, τ I)` (`t > 0`). -/
theorem ouDensity_scale (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (y : Fin d → ℝ) :
    ouDensity ρ v a t (scalePi (ouC a t) y) =
      (ouC a t ^ d)⁻¹ * heatFlowDensityPi ρ (ouTau v a t) y := by
  rw [ouDensity_eq_integral, heatFlowDensityPi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  simp only
  rw [scalePi_sub, ouS_eq, heatDensityPi_scale (ouC_pos a t) (ouTau_pos hv ha ht)]

omit [IsProbabilityMeasure ρ] in
/-- `∇p_t(c_t y) = c_t^{-d} c_t⁻¹ ∇q_{τ_t}(y)` (`t > 0`). -/
theorem ouGrad_scale (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (y : Fin d → ℝ) (i : Fin d) :
    ouGrad ρ v a t (scalePi (ouC a t) y) i =
      (ouC a t ^ d)⁻¹ * (ouC a t)⁻¹ * heatFlowGradPi ρ (ouTau v a t) y i := by
  have e : ouGrad ρ v a t (scalePi (ouC a t) y) i =
      ∫ y', heatGradPi (ouS v a t) (scalePi (ouC a t) y - scalePi (ouC a t) y') i ∂ρ :=
    integral_ouLaw ρ a t (((continuous_apply i).comp (continuous_heatGradPi _)).comp
      (by fun_prop))
  rw [e, heatFlowGradPi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  simp only
  rw [scalePi_sub, ouS_eq, heatGradPi_scale (ouC_pos a t) (ouTau_pos hv ha ht)]

/-- Scalar algebra of the Fisher scaling. -/
theorem fisher_scale_aux {K c Q G y v w : ℝ} (hK : K ≠ 0) (hc : c ≠ 0) (hQ : Q ≠ 0)
    (hw : w ≠ 0) (hv : v = c ^ 2 * w) :
    (K * c⁻¹ * G / (K * Q) + c * y / v) ^ 2 = c⁻¹ ^ 2 * (G / Q - -(y / w)) ^ 2 := by
  subst hv
  field_simp
  ring

/-- **Fisher information along the OU flow and along the heat flow.** For `t > 0`,
`I(ρ_{τ_t} ‖ π_{τ_t}) = c_t² ∫ p_t ∑ᵢ (∂ᵢp_t/p_t + xᵢ/v)² dx`: the relative Fisher information
of the heat flow at time `τ_t` is `c_t²` times that of `p_t` against `N(0, v I)`. -/
theorem heatFisher_eq (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) :
    heatFisher ρ (gaussPi d v) (ouTau v a t) = ouC a t ^ 2 *
      ∫ x, ouDensity ρ v a t x * ∑ i, (ouGrad ρ v a t x i / ouDensity ρ v a t x + x i / v) ^ 2 := by
  have hτ := ouTau_pos hv ha ht
  have hc := ouC_pos a t
  have hcv := ouC_sq_mul_add_ouTau v a t
  have hvτ : 0 < v + ouTau v a t := by positivity
  have hpt : ∀ y, (fun x => ouDensity ρ v a t x *
      ∑ i, (ouGrad ρ v a t x i / ouDensity ρ v a t x + x i / v) ^ 2) (ouC a t • y) =
      (ouC a t ^ d)⁻¹ * (ouC a t)⁻¹ ^ 2 * fisherIntegrand (heatFlowDensityPi ρ)
      (heatFlowDensityPi (gaussPi d v)) (heatFlowGradPi ρ) (heatFlowGradPi (gaussPi d v))
      (ouTau v a t) y := by
    intro y
    have hq := heatFlowDensityPi_pos ρ hτ y
    simp only [fisherIntegrand, relScore, dotProduct, heatFlowDensityPi_gaussian hv hτ,
      heatFlowGradPi_gaussian hv hτ, heatGradPi_div hvτ, ← sq]
    rw [show ouC a t • y = scalePi (ouC a t) y from rfl, ouDensity_scale ρ hv ha ht]
    simp only [ouGrad_scale ρ hv ha ht]
    have e : ∀ i, ((ouC a t ^ d)⁻¹ * (ouC a t)⁻¹ * heatFlowGradPi ρ (ouTau v a t) y i /
        ((ouC a t ^ d)⁻¹ * heatFlowDensityPi ρ (ouTau v a t) y) + scalePi (ouC a t) y i / v) ^ 2
        = (ouC a t)⁻¹ ^ 2 * (heatFlowGradPi ρ (ouTau v a t) y i / heatFlowDensityPi ρ
          (ouTau v a t) y - -(y i / (v + ouTau v a t))) ^ 2 := fun i =>
      fisher_scale_aux (by positivity) hc.ne' hq.ne' hvτ.ne' hcv.symm
    simp only [e, ← Finset.mul_sum]
    ring
  have hcov := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Fin d → ℝ))
    (fun x => ouDensity ρ v a t x *
      ∑ i, (ouGrad ρ v a t x i / ouDensity ρ v a t x + x i / v) ^ 2) (ouC a t)
  simp only [Module.finrank_fin_fun] at hcov
  rw [funext hpt, integral_const_mul, abs_of_pos (by positivity), smul_eq_mul] at hcov
  rw [heatFisher]
  have hcd : 0 < ouC a t ^ d := by positivity
  have key : ∀ I₁ I₂ : ℝ, (ouC a t ^ d)⁻¹ * (ouC a t)⁻¹ ^ 2 * I₁ = (ouC a t ^ d)⁻¹ * I₂ →
      I₁ = ouC a t ^ 2 * I₂ := by
    intro I₁ I₂ h
    field_simp at h
    linear_combination h
  exact key _ _ hcov

end KL


/-! ### FL-1/FL-2/FL-4 along the OU probability flow -/

section Main

open FormalizeSampling.KLDecay FormalizeSampling.LogSobolevAlongGaussian

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- `N(0, v I)` has Lebesgue density `heatDensityPi v`. -/
theorem gaussTarget_eq_lawOf (hv : 0 < v) :
    gaussTarget (d := d) v = lawOf (heatDensityPi v) := by
  rw [gaussTarget, GaussianLSIPi.pi_gaussianReal_eq_heatKernelPi, heatKernelPi_eq_withDensity hv]
  simp only [sub_zero]
  rfl

/-- **The KL along the flow as a density integral.** For `t > 0`,
`KL(p_t dx ‖ N(0, v I)) = ofReal (∫ p_t log(p_t / φ_v))`; in particular it is finite. -/
theorem klDiv_lawOf_ouDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    klDiv (lawOf (ouDensity ρ v a t)) (gaussTarget (d := d) v) =
      ENNReal.ofReal (∫ x, ouDensity ρ v a t x *
        Real.log (ouDensity ρ v a t x / heatDensityPi v x)) := by
  have : IsProbabilityMeasure (volume.withDensity fun x =>
      ENNReal.ofReal (ouDensity ρ v a t x)) := (gaussianDensityHyp_ouDensity ρ hv ha ht hmom).prob
  have : IsProbabilityMeasure (volume.withDensity fun x : Fin d → ℝ =>
      ENNReal.ofReal (heatDensityPi v x)) := by
    change IsProbabilityMeasure (lawOf (heatDensityPi v))
    rw [← gaussTarget_eq_lawOf hv, gaussTarget]; infer_instance
  rw [gaussTarget_eq_lawOf hv]
  exact KLTransport.klDiv_withDensity_eq_integral (continuous_ouDensity ρ hv ha ht).measurable
    (continuous_heatDensityPi v).measurable (fun x => (ouDensity_pos ρ hv ha ht x).le)
    (heatDensityPi_pos hv) (integrable_ouKL ρ hv ha ht hmom)

/-- The real KL `gaussKL` of `LogSobolevAlongGaussian` along the flow agrees with
`KLDecay.klDivDensity` and with the KL integral `∫ p_t log(p_t / φ_v)` (`t > 0`). -/
theorem gaussKL_eq_klDivDensity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) :
    gaussKL (ouDensity ρ v a) v t = klDivDensity (ouDensity ρ v a t) (heatDensityPi v) ∧
      gaussKL (ouDensity ρ v a) v t =
        ∫ x, ouDensity ρ v a t x * Real.log (ouDensity ρ v a t x / heatDensityPi v x) := by
  have hint : gaussKL (ouDensity ρ v a) v t =
      ∫ x, ouDensity ρ v a t x * Real.log (ouDensity ρ v a t x / heatDensityPi v x) := by
    rw [gaussKL, klDiv_lawOf_ouDensity ρ hv ha ht hmom, ENNReal.toReal_ofReal]
    have : IsProbabilityMeasure (volume.withDensity fun x =>
        ENNReal.ofReal (ouDensity ρ v a t x)) :=
      (gaussianDensityHyp_ouDensity ρ hv ha ht hmom).prob
    have : IsProbabilityMeasure (volume.withDensity fun x : Fin d → ℝ =>
        ENNReal.ofReal (heatDensityPi v x)) := by
      change IsProbabilityMeasure (lawOf (heatDensityPi v))
      rw [← gaussTarget_eq_lawOf hv, gaussTarget]; infer_instance
    have := toReal_klDiv_withDensity_eq_integral (continuous_ouDensity ρ hv ha ht).measurable
      (continuous_heatDensityPi v).measurable (ouDensity_pos ρ hv ha ht) (heatDensityPi_pos hv)
      (integrable_ouKL ρ hv ha ht hmom)
    rw [← this]
    exact ENNReal.toReal_nonneg
  refine ⟨?_, hint⟩
  rw [hint, klDivDensity, densityMeasure, MeasureHelpers.integral_withDensity_ofReal
    (continuous_ouDensity ρ hv ha ht).measurable fun x => (ouDensity_pos ρ hv ha ht x).le]

/-- **FL-1/FL-2 along the OU probability flow (Verified, unconditional).** For a probability
law `ρ` with finite second moment, `v, a > 0` and every `t > 0`,
`d/dt KL(p_t ‖ N(0, v I)) = -a v I(p_t ‖ N(0, v I))`, where
`I = relFisher (p_t dx) (∇p_t/p_t) (-x/v) = ∫ |∇log p_t + x/v|² p_t dx`. The proof reduces the KL
to the heat flow (`gaussKL_ouDensity_eq`), uses de Bruijn's identity
`HeatFlowDeBruijnPi.hasDerivAt_heatKL` with the regularity `heatFlowRegularPi_gaussian`, and the
scaling of the Fisher information (`heatFisher_eq`). -/
theorem hasDerivAt_gaussKL_ouDensity (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (ht : 0 < t) :
    HasDerivAt (gaussKL (ouDensity ρ v a) v)
      (-(a * v) * relFisher (lawOf (ouDensity ρ v a t))
        (densityScore (ouDensity ρ v a t) (ouGrad ρ v a t)) (gaussScore v)) t := by
  have hτ := ouTau_pos hv ha ht
  have h1 := (hasDerivAt_heatKL (heatFlowRegularPi_gaussian ρ hmom hv)
    (show ouTau v a t ∈ Ioi 0 from hτ)).comp t (hasDerivAt_ouTau v a t)
  have h2 := h1.congr_of_eventuallyEq (f₁ := gaussKL (ouDensity ρ v a) v) (by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact gaussKL_ouDensity_eq ρ hv ha hu)
  refine h2.congr_deriv ?_
  rw [heatFisher_eq ρ hv ha ht,
    relFisher_densityScore (gaussianDensityHyp_ouDensity ρ hv ha ht hmom)]
  generalize (∫ x, ouDensity ρ v a t x *
    ∑ i, (ouGrad ρ v a t x i / ouDensity ρ v a t x + x i / v) ^ 2) = I
  have := ouC_sq_mul_exp a t
  linear_combination (-(a * v) * I) * this

/-- The same derivative with the shared score `score (p_t) = ∇ log p_t`:
`d/dt KL(p_t ‖ N(0, v I)) = -a v ∫ |∇log p_t - ∇log π|² p_t dx` (`t > 0`). -/
theorem hasDerivAt_gaussKL_ouDensity_score (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (ht : 0 < t) :
    HasDerivAt (gaussKL (ouDensity ρ v a) v)
      (-(a * v) * relFisher (lawOf (ouDensity ρ v a t)) (score (ouDensity ρ v a t))
        (gaussScore v)) t := by
  rw [score_eq_densityScore (gaussianDensityHyp_ouDensity ρ hv ha ht hmom)]
  exact hasDerivAt_gaussKL_ouDensity ρ hv ha hmom ht

/-- The preconditioner `H = (a v)⁻¹ I` whose ideal PFG velocity is the OU probability-flow
velocity. -/
noncomputable def ouPrecond (d : ℕ) (v a : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (a * v)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- `H⁻¹ = (a v) I`. -/
theorem ouPrecond_inv (hv : 0 < v) (ha : 0 < a) :
    (ouPrecond d v a)⁻¹ = (a * v) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  refine Matrix.inv_eq_left_inv ?_
  have hav : a * v ≠ 0 := by positivity
  rw [ouPrecond, smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hav, one_smul]

/-- `H = (a v)⁻¹ I` is positive definite. -/
theorem ouPrecond_posDef (hv : 0 < v) (ha : 0 < a) : (ouPrecond d v a).PosDef :=
  Matrix.PosDef.one.smul (by positivity)

/-- `‖u‖²_H = (a v)⁻¹ |u|²`, so `λ_max(H) ≤ (a v)⁻¹`. -/
theorem sqNormH_ouPrecond (u : Fin d → ℝ) :
    sqNormH (ouPrecond d v a) u = (a * v)⁻¹ * (u ⬝ᵥ u) := by
  simp [sqNormH, ouPrecond, Matrix.smul_mulVec, dotProduct_smul]

/-- The ideal PFG velocity of `H = (a v)⁻¹ I` is `a v (sStar - s)`. -/
theorem idealVelocity_ouPrecond (hv : 0 < v) (ha : 0 < a)
    (s sStar : (Fin d → ℝ) → Fin d → ℝ) (x : Fin d → ℝ) :
    idealVelocity (ouPrecond d v a) s sStar x = (a * v) • (sStar x - s x) := by
  rw [idealVelocity, ouPrecond_inv hv ha, Matrix.smul_mulVec, Matrix.one_mulVec]

omit [IsProbabilityMeasure ρ] in
/-- The OU probability-flow velocity is the ideal PFG velocity for `H = (a v)⁻¹ I` and the
target density `heatDensityPi v` of `N(0, v I)`. -/
theorem ouVelocity_eq_idealVelocity (hv : 0 < v) (ha : 0 < a) :
    ouVelocity ρ v a t = idealVelocity (ouPrecond d v a) (score (ouDensity ρ v a t))
      (score (heatDensityPi v)) := by
  funext x
  rw [idealVelocity_ouPrecond hv ha, ouVelocity]

/-- **`KLFirstVariation` along the OU probability flow (Verified).** For a probability law `ρ`
with finite second moment, `v, a > 0` and a start time `s > 0`, the shifted flow
`u ↦ p_{s+u}` satisfies the FL-4 hypothesis `KLDecay.KLFirstVariation` along the ideal velocity
`H⁻¹(sStar - ∇p/p)` with `H = (a v)⁻¹ I`, the Gaussian score `sStar = -x/v` and
`KL u = KL(p_{s+u} ‖ N(0, v I))`. -/
theorem klFirstVariation_ou (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {s : ℝ} (hs : 0 < s) :
    KLFirstVariation (fun u => lawOf (ouDensity ρ v a (s + u)))
      (fun u => idealVelocity (ouPrecond d v a)
        (densityScore (ouDensity ρ v a (s + u)) (ouGrad ρ v a (s + u))) (gaussScore v))
      (fun u => densityScore (ouDensity ρ v a (s + u)) (ouGrad ρ v a (s + u))) (gaussScore v)
      (gaussKL (fun u => ouDensity ρ v a (s + u)) v) := by
  intro u hu
  have hsu : 0 < s + u := by linarith
  have h := (hasDerivAt_gaussKL_ouDensity ρ hv ha hmom hsu).comp u
    ((hasDerivAt_id' u).const_add s)
  rw [mul_one] at h
  refine h.congr_deriv ?_
  simp only [idealVelocity_ouPrecond hv ha, smul_dotProduct, smul_eq_mul]
  rw [relFisher, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [show gaussScore v x - densityScore (ouDensity ρ v a (s + u)) (ouGrad ρ v a (s + u)) x =
    -(densityScore (ouDensity ρ v a (s + u)) (ouGrad ρ v a (s + u)) x - gaussScore v x) from
    (neg_sub _ _).symm, neg_dotProduct]
  ring

/-- **FL-4 along the OU probability flow (Verified, unconditional).** For a probability law `ρ`
on `Fin d → ℝ` with finite second moment, `v, a > 0` and `0 < s ≤ t`,
`KL(p_t ‖ N(0, v I)) ≤ e^{-2a(t - s)} KL(p_s ‖ N(0, v I))`, where `p_t` is the OU marginal
density. Obtained from `LogSobolevAlongGaussian.exp_decay_idealVelocity_gaussian` with every
hypothesis discharged: `GaussianDensityHyp` (`gaussianDensityHyp_ouDensity`), `KLFirstVariation`
(`klFirstVariation_ou`) and the dissipation integrability. -/
theorem gaussKL_ouDensity_le (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    gaussKL (ouDensity ρ v a) v t ≤
      Real.exp (-2 * a * (t - s)) * gaussKL (ouDensity ρ v a) v s := by
  have hp : ∀ u, 0 ≤ u → GaussianDensityHyp (ouDensity ρ v a (s + u)) (ouGrad ρ v a (s + u)) v :=
    fun u hu => gaussianDensityHyp_ouDensity ρ hv ha (by linarith) hmom
  have hdiss : ∀ u, 0 ≤ u → Integrable (fun x => sqNormH (ouPrecond d v a)⁻¹
      (densityScore (ouDensity ρ v a (s + u)) (ouGrad ρ v a (s + u)) x - gaussScore v x))
      (lawOf (ouDensity ρ v a (s + u))) := by
    intro u hu
    refine ((integrable_fisher_densityScore (hp u hu)).const_mul (a * v)).congr
      (Eventually.of_forall fun x => ?_)
    simp [ouPrecond_inv hv ha, sqNormH, Matrix.smul_mulVec, dotProduct_smul]
  have hM : 0 < (a * v)⁻¹ := by positivity
  have h := exp_decay_idealVelocity_gaussian hv (ouPrecond_posDef hv ha) hM
    (fun u => (sqNormH_ouPrecond u).le) hp (klFirstVariation_ou ρ hv ha hmom hs) hdiss (t - s)
    (by linarith)
  have e1 : gaussKL (fun u => ouDensity ρ v a (s + u)) v (t - s) =
      gaussKL (ouDensity ρ v a) v t := by
    simp only [gaussKL, add_sub_cancel]
  have e2 : gaussKL (fun u => ouDensity ρ v a (s + u)) v 0 = gaussKL (ouDensity ρ v a) v s := by
    simp only [gaussKL, add_zero]
  have e3 : -2 * (t - s) / (v * (a * v)⁻¹) = -2 * a * (t - s) := by
    field_simp
  rwa [e1, e2, e3] at h

/-- **FL-4 along the OU flow in `klDiv` form.** With the OU marginals `ouKernelVarPi v a t ∘ₘ ρ`
of `OULangevinDecayPi` (probability `ρ`, finite second moment, no KL assumption on `ρ`),
for `0 < s ≤ t`:
`KL(ρ_t ‖ N(0, v I)).toReal ≤ e^{-2a(t - s)} KL(ρ_s ‖ N(0, v I)).toReal`, both finite. -/
theorem toReal_klDiv_ouKernelVarPi_comp_le_of_le (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    klDiv (OULangevinDecayPi.ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v) ≠ ⊤ ∧
      (klDiv (OULangevinDecayPi.ouKernelVarPi v a t ∘ₘ ρ) (gaussPi d v)).toReal ≤
        Real.exp (-2 * a * (t - s)) *
          (klDiv (OULangevinDecayPi.ouKernelVarPi v a s ∘ₘ ρ) (gaussPi d v)).toReal := by
  have ht : 0 < t := hs.trans_le hst
  have h := gaussKL_ouDensity_le ρ hv ha hmom hs hst
  rw [gaussKL, gaussKL, lawOf_ouDensity ρ hv ha ht, lawOf_ouDensity ρ hv ha hs] at h
  refine ⟨?_, h⟩
  rw [← lawOf_ouDensity ρ hv ha ht]
  change klDiv _ (gaussTarget v) ≠ ⊤
  rw [klDiv_lawOf_ouDensity ρ hv ha ht hmom]
  exact ENNReal.ofReal_ne_top

omit [IsProbabilityMeasure ρ] in
/-- The score of the target density is the Gaussian score: `∇log φ_v = gaussScore v`. -/
theorem score_heatDensityPi_eq_gaussScore (hv : 0 < v) :
    score (heatDensityPi (d := d) v) = gaussScore v := by
  funext x i
  rw [score_heatDensityPi hv, gaussScore, Pi.smul_apply, smul_eq_mul]
  ring

/-- **FL-2 along the OU probability flow, in the form of `Flow/KLDissipation.lean`.** For `t > 0`,
`d/dt klDivDensity(p_t, φ_v) = -∫ ‖∇log p_t - ∇log φ_v‖²_{H⁻¹} p_t dx` with `H = (a v)⁻¹ I`, the
conclusion of `KLDissipation.hasDerivAt_klIntegral_of_eq_idealVelocity` for the velocity
`ouVelocity = idealVelocity H (∇log p_t) (∇log φ_v)`, here without `TransportKLRegularity`. -/
theorem hasDerivAt_klDivDensity_ouDensity (hv : 0 < v) (ha : 0 < a)
    (hmom : Integrable (fun x => ∑ i, x i ^ 2) ρ) (ht : 0 < t) :
    HasDerivAt (fun t => klDivDensity (ouDensity ρ v a t) (heatDensityPi v))
      (-∫ x, sqNormH (ouPrecond d v a)⁻¹
        (score (ouDensity ρ v a t) x - score (heatDensityPi v) x) * ouDensity ρ v a t x) t := by
  have h := (hasDerivAt_gaussKL_ouDensity_score ρ hv ha hmom ht).congr_of_eventuallyEq
    (f₁ := fun t => klDivDensity (ouDensity ρ v a t) (heatDensityPi v)) (by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact (gaussKL_eq_klDivDensity ρ hv ha hu hmom).1.symm)
  refine h.congr_deriv ?_
  rw [relFisher, lawOf, MeasureHelpers.integral_withDensity_ofReal
    (continuous_ouDensity ρ hv ha ht).measurable fun x => (ouDensity_pos ρ hv ha ht x).le,
    ← integral_const_mul, ← integral_neg, score_heatDensityPi_eq_gaussScore hv]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ouPrecond_inv hv ha, sqNormH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]
  ring

end Main

/-! ### The Gaussian envelope and the velocity field -/

section Envelope


/-- The integrable envelope `Φ_v(x) = (1 + |x|²)⁴ φ_{2v}(x)`. -/
noncomputable def envOU (v : ℝ) (x : Fin d → ℝ) : ℝ :=
  (1 + ∑ i, x i ^ 2) ^ 4 * heatDensityPi (2 * v) x

/-- `Φ_v` is Lebesgue integrable (two applications of `HeatFlowRegularityPi.envelope`). -/
theorem integrable_envOU {v : ℝ} (hv : 0 < v) : Integrable (envOU (d := d) v) := by
  have h8 : 0 < 8 * v := by positivity
  have hi : Integrable (fun x : Fin d → ℝ => heatDensityPi (2 * (4 * v)) x) := by
    have := (GaussianLSIPi.integrable_heatDensityPi_sub (d := d) (by positivity : 0 < 2 * (4 * v))
      0).1
    simpa using this
  have hK₁ : 0 ≤ gc d (2 * v) * (1 + 8 * (2 * v)) ^ 2 / gc d (2 * (2 * v)) := by
    have := gc_pos (d := d) (by positivity : 0 < 2 * v)
    have := gc_pos (d := d) (by positivity : 0 < 2 * (2 * v)); positivity
  refine (hi.const_mul (gc d (2 * v) * (1 + 8 * (2 * v)) ^ 2 / gc d (2 * (2 * v)) *
    (gc d (4 * v) * (1 + 8 * (4 * v)) ^ 2 / gc d (2 * (4 * v))))).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · unfold envOU
    exact ((continuous_const.add (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).pow 2)).pow 4 |>.mul (continuous_heatDensityPi _)).aestronglyMeasurable
  · have hu : 0 ≤ 1 + ∑ i, x i ^ 2 := by linarith [sum_sq_nonneg x]
    have e1 := envelope (d := d) (by positivity : 0 < 2 * v) le_rfl le_rfl x
    have e2 := envelope (d := d) (by positivity : 0 < 4 * v) le_rfl le_rfl x
    rw [show 2 * (2 * v) = 4 * v by ring] at e1 hK₁
    have hφ := (heatDensityPi_pos (by positivity : 0 < 2 * v) x).le
    rw [Real.norm_of_nonneg (by unfold envOU; positivity), envOU]
    calc (1 + ∑ i, x i ^ 2) ^ 4 * heatDensityPi (2 * v) x
        = (1 + ∑ i, x i ^ 2) ^ 2 * ((1 + ∑ i, x i ^ 2) ^ 2 * heatDensityPi (2 * v) x) := by ring
      _ ≤ (1 + ∑ i, x i ^ 2) ^ 2 * (gc d (2 * v) * (1 + 8 * (2 * v)) ^ 2 / gc d (4 * v) *
            heatDensityPi (4 * v) x) := mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = gc d (2 * v) * (1 + 8 * (2 * v)) ^ 2 / gc d (4 * v) *
            ((1 + ∑ i, x i ^ 2) ^ 2 * heatDensityPi (4 * v) x) := by ring
      _ ≤ gc d (2 * v) * (1 + 8 * (2 * v)) ^ 2 / gc d (4 * v) *
            (gc d (4 * v) * (1 + 8 * (4 * v)) ^ 2 / gc d (2 * (4 * v)) *
              heatDensityPi (2 * (4 * v)) x) := mul_le_mul_of_nonneg_left e2 hK₁
      _ = _ := by rw [show 2 * (2 * v) = 4 * v by ring]; ring

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- Explicit form of the velocity: `v_t(x)ᵢ = -a xᵢ - a v ∂ᵢp_t(x)/p_t(x)` (`t > 0`). -/
theorem ouVelocity_apply (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (x : Fin d → ℝ) (i : Fin d) :
    ouVelocity ρ v a t x i =
      -(a * x i) - a * v * (ouGrad ρ v a t x i / ouDensity ρ v a t x) := by
  simp only [ouVelocity, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, score_heatDensityPi hv,
    score_ouDensity ρ hv ha ht]
  field_simp

/-- The velocity coordinates as functions (`t > 0`). -/
theorem ouVelocity_coord_eq (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (i : Fin d) :
    (fun x => ouVelocity ρ v a t x i) =
      fun x => -(a * x i) - a * v * (ouGrad ρ v a t x i / ouDensity ρ v a t x) :=
  funext fun x => ouVelocity_apply ρ hv ha ht x i

/-- The velocity coordinates are differentiable (`t > 0`). -/
theorem differentiable_ouVelocity (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (i : Fin d) :
    Differentiable ℝ fun x => ouVelocity ρ v a t x i := by
  rw [ouVelocity_coord_eq ρ hv ha ht]
  simp only [div_eq_mul_inv]
  intro x
  have hG := (hasFDerivAt_ouGrad ρ hv ha ht i x).differentiableAt
  have hp := (hasFDerivAt_ouDensity ρ hv ha ht x).differentiableAt
  exact ((differentiableAt_apply i x).const_mul a).neg.sub
    ((hG.mul (hp.inv (ouDensity_pos ρ hv ha ht x).ne')).const_mul (a * v))

/-- `∂ᵢ(p_t vᵢ)(x) = -a (p_t(x) + xᵢ ∂ᵢp_t(x) + v ∂ᵢ²p_t(x))` (`t > 0`). -/
theorem partialDeriv_ouFlux (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (i : Fin d)
    (x : Fin d → ℝ) :
    partialDeriv i (fun y => ouDensity ρ v a t y * ouVelocity ρ v a t y i) x =
      -a * (ouDensity ρ v a t x + x i * ouGrad ρ v a t x i +
        v * heatFlowHessPi (ouLaw ρ a t) (ouS v a t) x i i) := by
  have e : (fun y => ouDensity ρ v a t y * ouVelocity ρ v a t y i) =
      fun y => -a * (y i * ouDensity ρ v a t y + v * ouGrad ρ v a t y i) :=
    funext fun y => ouDensity_mul_ouVelocity ρ hv ha ht y i
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) i x).mul (hasFDerivAt_ouDensity ρ hv ha ht x)).add
    ((hasFDerivAt_ouGrad ρ hv ha ht i x).const_mul v)).const_mul (-a)
  have h' : HasFDerivAt (fun y => -a * (y i * ouDensity ρ v a t y + v * ouGrad ρ v a t y i))
      _ x := h
  rw [e, partialDeriv, h'.fderiv]
  simp only [smul_apply, add_apply, dotCLM_single, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, smul_eq_mul]
  ring

/-- Scalar bound for the flux `-a (xᵢ p + v ∂ᵢp)`. -/
theorem abs_flux_aux {p G y u P A₁ w a : ℝ} (ha : 0 ≤ a) (hu : 1 ≤ u) (hw : 0 ≤ w)
    (hp : |p| ≤ P) (hy : |y| ≤ u) (hG : |G| ≤ A₁ * u * P) :
    |-a * (y * p + w * G)| ≤ a * (1 + w * A₁) * u ^ 1 * P := by
  have h1 : |y * p| ≤ u * P := by
    rw [abs_mul]; exact mul_le_mul hy hp (abs_nonneg _) (by linarith)
  have h2 : |w * G| ≤ w * (A₁ * u * P) := by
    rw [abs_mul, abs_of_nonneg hw]; exact mul_le_mul_of_nonneg_left hG hw
  rw [abs_mul, abs_neg, abs_of_nonneg ha, pow_one]
  have e := abs_add_le (y * p) (w * G)
  have : |y * p + w * G| ≤ (1 + w * A₁) * u * P := by nlinarith
  calc a * |y * p + w * G| ≤ a * ((1 + w * A₁) * u * P) := mul_le_mul_of_nonneg_left this ha
    _ = _ := by ring

/-- Multiplying a bound `K u^k P` by a log factor bounded by `L u`. -/
theorem abs_mul_log_aux {f g u P K L : ℝ} {k : ℕ} (hf : |f| ≤ K * u ^ k * P)
    (hg : |g| ≤ L * u) : |f * g| ≤ K * L * u ^ (k + 1) * P := by
  rw [abs_mul]
  have hK : 0 ≤ K * u ^ k * P := (abs_nonneg _).trans hf
  calc |f| * |g| ≤ (K * u ^ k * P) * (L * u) := mul_le_mul hf hg (abs_nonneg _) hK
    _ = K * L * u ^ (k + 1) * P := by ring

omit [IsProbabilityMeasure ρ] in
/-- **Time shift of `TransportKLRegularity`.** Regularity of `P` at `s + t₀` is regularity of the
shifted flow `t ↦ P (s + t)` (velocity `t ↦ G (s + t)`) at `t₀`. -/
theorem transportKLRegularity_shift {P : ℝ → (Fin d → ℝ) → ℝ} {pStar : (Fin d → ℝ) → ℝ}
    {G : ℝ → (Fin d → ℝ) → Fin d → ℝ} {s t₀ : ℝ}
    (h : KLDissipation.TransportKLRegularity P pStar G (s + t₀)) :
    KLDissipation.TransportKLRegularity (fun t => P (s + t)) pStar (fun t => G (s + t)) t₀ := by
  obtain ⟨ε, hε, bound, hmeas, hb, hbint⟩ := h.domination
  have hmem : ∀ t ∈ Metric.ball t₀ ε, s + t ∈ Metric.ball (s + t₀) ε := fun t ht => by
    rw [Metric.mem_ball, Real.dist_eq] at ht ⊢
    rwa [add_sub_add_left_eq_sub]
  exact ⟨⟨ε, hε, bound, fun t ht => hmeas (s + t) (hmem t ht),
    hb.mono fun x hx t ht => hx (s + t) (hmem t ht), hbint⟩, h.integrable_kl, h.differentiable,
    h.differentiable_velocity, h.integrable_flux, h.integrable_dflux, h.integrable_dflux_log,
    h.integrable_flux_log, h.integrable_flux_score⟩

end Envelope

end FormalizeSampling.ProbabilityFlowOU
