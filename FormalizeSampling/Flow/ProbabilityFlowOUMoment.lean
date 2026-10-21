module

public import Mathlib.Algebra.Order.Chebyshev
public import FormalizeSampling.Flow.ProbabilityFlowOU

/-!
# The OU probability flow: `TransportKLRegularity` under a fourth moment

Registry IDs: **FL-1 (II)**, **FL-2**, **FL-4** (continuation of
`Flow/ProbabilityFlowOU.lean`).

Status: **Verified**. No regularity or functional-inequality hypotheses. The initial law `ρ` is
a probability measure on `Fin d → ℝ` with a finite fourth moment,
`hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ`, i.e. `∫ |y|⁴ dρ(y) < ∞` (a bounded support
implies it, `integrable_moment4_of_bounded`). Setting and notation as in `ProbabilityFlowOU`:
target `π = N(0, v I)` with density `φ_v`, `c_t = e^{-at}`, `s_t = v (1 - e^{-2at})`, OU
marginals `p_t(x) = ∫ φ_{s_t}(x - c_t y) dρ(y)`, ideal velocity `ouVelocity`.

## Method

* **Tonelli for moving kernels** (`integrable_integral_kernel`): if `R ω z ≤ P ω Q z`,
  `(1 + |z|²)^k Q(z)` is Lebesgue integrable and `(1 + |m ω|²)^k P ω` is `ν`-integrable, then
  `x ↦ ∫ (1 + |x|²)^k R ω (x - m ω) dν(ω)` is Lebesgue integrable.
* **Tube estimate** (`heatDensityPi_le_tube`): the fundamental theorem of calculus in the centre
  parameter `c` gives, for `c₁ ≤ c ≤ c₂`,
  `φ_σ(x - c y) ≤ φ_σ(x - c₂ y) + ∫_{(c₁, c₂]} τ_σ(x, y, c') dc'` with
  `τ_σ = ∑ⱼ |yⱼ| |∂ⱼφ_σ(x - c' y)|` (`tubeK`). Integrating in `x` costs one factor `|y|`; this
  replaces the Gaussian majorant uniform in the centre, which would cost `exp(δ|y|²)`.
* **Kernel bound** (`abs_genK_le`): the generator `d p_t + x ⬝ᵥ ∇p_t + v Δp_t` is the
  `ρ`-average of `g_{s_t}(x, c_t y)` (`ouGen_eq_integral`), and
  `|g_s(x, c y)| ≤ A ℓ(y) K φ_{2v}(x - c y)` with `ℓ(y) = 1 + ∑ |yᵢ|` (split `x = (x - c y) + c y`).
  With the time-uniform bound `|log(p_t/π)| ≤ L (1 + |x|²)` (Jensen, second moment;
  `abs_log_ouDensity_div_le_moment`) and the tube estimate, the domination bound on the time ball
  `B(t₀, t₀/2)` is `C (J₁ + J₂)` with `J₁, J₂` Tonelli integrals of `y`-weight
  `(1 + |y|²) ℓ(y)² ≤ 2 (1 + d) (1 + |y|²)²`: here the fourth moment is used.
* **Fixed-time fields** (`integrable_of_le_ouQ`): every integrand at `t₀` is bounded by
  `C (1 + |x|²)² q(x)` with `q(x) = ∫ φ_{2v}(x - w) d(c_{t₀} ρ)(w)` (`ouQ`); Tonelli again
  needs the fourth moment.

## Main results

* `transportKLRegularity_ou_moment`: under `hmom4`, `v, a > 0`, for every `t₀ > 0`,
  `KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a) t₀`.
* `ProbabilityFlowOU.transportKLRegularity_ou`: the bounded-support case
  (`integrable_moment4_of_bounded`).
* `klDecay_of_idealVelocity_local_ou_moment`: PFG's `KLDissipation.klDecay_of_idealVelocity_local`
  on the shifted flow `t ↦ p_{s+t}` (`s > 0`), with every hypothesis (`hce`, `hreg`, `hdiss`,
  `hLSI`) discharged under `hmom4`: for `t ≥ 0`,
  `d/dt klDivDensity(p_{s+t}, φ_v) = -∫ ‖∇log p_{s+t} - ∇log φ_v‖²_{H⁻¹} p_{s+t}`
  (`H = (a v)⁻¹ I`) and `klDivDensity(p_{s+t}, φ_v) ≤ e^{-2at} klDivDensity(p_s, φ_v)`.

## Not proved here

* **Sharpness of the moment** is not treated in this file. Only the fourth moment is used
  here; the domination bound uses `(1 + |y|²) ℓ(y)²`, of order `|y|⁴`. The fixed-time fields
  under a third moment are `ProbabilityFlowOUThirdMoment.transportKLRegularity_ou_of_domination`;
  that a third moment does not suffice for `TransportKLRegularity`, and that a second moment
  does not suffice for the fixed-time fields, are the counterexamples
  `ProbabilityFlowOUCounterexample.not_transportKLRegularity_rhoGeom_sixteenth` and
  `ProbabilityFlowOUCounterexample.not_integrable_flux_log_rhoGeom`.
* **Only `t > 0`.** As in `ProbabilityFlowOU`, the regularity is proved at `t₀ > 0`; the
  `KLDissipation` theorems are applied to the shifted flow `t ↦ p_{s+t}`. Decay from `t = 0`
  remains `ProbabilityFlowOUZero.toReal_klDiv_ouKernelVarPi_comp_le_zero` (data processing /
  limit `s → 0⁺`), not this route.
* Only the isotropic Gaussian target and the OU flow; no Lagrangian ODE, no uniqueness of the
  continuity equation, no SDE path law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProbabilityFlowOUMoment

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi FormalizeSampling.ProbabilityFlowOU
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi)

variable {d : ℕ}

/-! ### A Tonelli lemma for moving Gaussian kernels -/

/-- **Integrability of a kernel average with a polynomial weight.** Let `ν` be an s-finite
measure on `Ω`, `m : Ω → ℝ^d` a measurable centre map and `R ω z ≥ 0` jointly measurable with
`R ω z ≤ P ω Q z`. If `(1 + |z|²)^k Q(z)` is Lebesgue integrable and
`(1 + |m ω|²)^k P ω` is `ν`-integrable, then
`x ↦ ∫ (1 + |x|²)^k R ω (x - m ω) dν(ω)` is Lebesgue integrable (Tonelli, with
`1 + |x|² ≤ 2 (1 + |x - m|²)(1 + |m|²)`). -/
theorem integrable_integral_kernel {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]
    (k : ℕ) {m : Ω → Fin d → ℝ} (hm : Measurable m) {R : Ω → (Fin d → ℝ) → ℝ}
    (hR : Measurable fun q : Ω × (Fin d → ℝ) => R q.1 q.2) (hR0 : ∀ ω z, 0 ≤ R ω z)
    {P : Ω → ℝ} {Q : (Fin d → ℝ) → ℝ} (hRle : ∀ ω z, R ω z ≤ P ω * Q z)
    (hQ : Integrable fun z => (1 + ∑ i, z i ^ 2) ^ k * Q z)
    (hPm : Integrable (fun ω => (1 + ∑ i, m ω i ^ 2) ^ k * P ω) ν) :
    Integrable fun x : Fin d → ℝ => ∫ ω, (1 + ∑ i, x i ^ 2) ^ k * R ω (x - m ω) ∂ν := by
  set F : (Fin d → ℝ) × Ω → ℝ := fun q => (1 + ∑ i, q.1 i ^ 2) ^ k * R q.2 (q.1 - m q.2)
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (hR.comp (measurable_snd.prodMk
      (measurable_fst.sub (hm.comp measurable_snd))))
    exact (measurable_const.add (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_fst).pow_const 2)).pow_const k
  have hF0 : ∀ q, 0 ≤ F q := fun q => mul_nonneg (by positivity) (hR0 _ _)
  have key : ∀ ω x, F (x, ω) ≤ 2 ^ k * ((1 + ∑ i, m ω i ^ 2) ^ k * P ω) *
      ((1 + ∑ i, (x - m ω) i ^ 2) ^ k * Q (x - m ω)) := by
    intro ω x
    have h1 := one_add_sum_sq_le x (m ω)
    have hx : 0 ≤ 1 + ∑ i, x i ^ 2 := by linarith [sum_sq_nonneg x]
    have hpow : (1 + ∑ i, x i ^ 2) ^ k ≤
        2 ^ k * (1 + ∑ i, (x - m ω) i ^ 2) ^ k * (1 + ∑ i, m ω i ^ 2) ^ k := by
      rw [← mul_pow, ← mul_pow]; exact pow_le_pow_left₀ hx h1 k
    have hR' := hRle ω (x - m ω)
    have hPQ : 0 ≤ P ω * Q (x - m ω) := (hR0 _ _).trans hR'
    calc F (x, ω) ≤ (2 ^ k * (1 + ∑ i, (x - m ω) i ^ 2) ^ k * (1 + ∑ i, m ω i ^ 2) ^ k) *
          (P ω * Q (x - m ω)) := mul_le_mul hpow hR' (hR0 _ _) (by positivity)
      _ = _ := by ring
  have hint : ∀ ω, Integrable (fun x => F (x, ω)) := by
    intro ω
    refine ((hQ.comp_sub_right (m ω)).const_mul
      (2 ^ k * ((1 + ∑ i, m ω i ^ 2) ^ k * P ω))).mono'
      (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hF0 _)]
    exact key ω x
  have hF : Integrable F ((volume : Measure (Fin d → ℝ)).prod ν) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hint, ?_⟩
    refine (hPm.const_mul (2 ^ k * ∫ z, (1 + ∑ i, z i ^ 2) ^ k * Q z)).mono'
      (hFm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have e : (fun x => ‖F (x, ω)‖) = fun x => F (x, ω) :=
      funext fun x => Real.norm_of_nonneg (hF0 _)
    rw [e, Real.norm_of_nonneg (integral_nonneg fun x => hF0 _)]
    calc ∫ x, F (x, ω) ≤ ∫ x, 2 ^ k * ((1 + ∑ i, m ω i ^ 2) ^ k * P ω) *
          ((1 + ∑ i, (x - m ω) i ^ 2) ^ k * Q (x - m ω)) :=
          integral_mono (hint ω) ((hQ.comp_sub_right (m ω)).const_mul _) (key ω)
      _ = _ := by
        rw [integral_const_mul, integral_sub_right_eq_self
          (fun z => (1 + ∑ i, z i ^ 2) ^ k * Q z) (m ω)]
        ring
  exact hF.integral_prod_left

/-! ### The tube estimate -/

/-- The tube integrand `τ_σ(x, y, c) = ∑ⱼ |yⱼ| |∂ⱼφ_σ(x - c y)|`, which dominates the
`c`-derivative of `c ↦ φ_σ(x - c y)`. -/
noncomputable def tubeK (σ : ℝ) (x y : Fin d → ℝ) (c : ℝ) : ℝ :=
  ∑ j, |y j| * (|(x - scalePi c y) j| / σ * heatDensityPi σ (x - scalePi c y))

/-- `τ_σ ≥ 0` for `σ > 0`. -/
theorem tubeK_nonneg {σ : ℝ} (hσ : 0 < σ) (x y : Fin d → ℝ) (c : ℝ) : 0 ≤ tubeK σ x y c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _)
    (mul_nonneg (div_nonneg (abs_nonneg _) hσ.le) (heatDensityPi_pos hσ _).le)

/-- `τ_σ` is jointly continuous in `(x, y, c)`. -/
theorem continuous_tubeK (σ : ℝ) :
    Continuous fun q : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => tubeK σ q.1 q.2.1 q.2.2 := by
  unfold tubeK scalePi
  have := continuous_heatDensityPi (d := d) σ
  fun_prop

/-- **Tube estimate (fundamental theorem of calculus in the centre).** For `σ > 0` and
`c₁ ≤ c ≤ c₂`: `φ_σ(x - c y) ≤ φ_σ(x - c₂ y) + ∫_{(c₁, c₂]} τ_σ(x, y, c') dc'`. -/
theorem heatDensityPi_le_tube {σ c₁ c₂ c : ℝ} (hσ : 0 < σ) (h1 : c₁ ≤ c) (h2 : c ≤ c₂)
    (x y : Fin d → ℝ) :
    heatDensityPi σ (x - scalePi c y) ≤
      heatDensityPi σ (x - scalePi c₂ y) + ∫ c' in Ioc c₁ c₂, tubeK σ x y c' := by
  set f : ℝ → ℝ := fun c' => heatDensityPi σ (x - scalePi c' y)
  set f' : ℝ → ℝ := fun c' => heatGradPi σ (x - scalePi c' y) ⬝ᵥ (fun i => -y i)
  have hz : ∀ c', HasDerivAt (fun c' => x - scalePi c' y) (fun i => -y i) c' := by
    intro c'
    refine hasDerivAt_pi.2 fun i => ?_
    have := ((hasDerivAt_id' c').mul_const (y i)).const_sub (x i)
    convert this using 1
    · funext w; simp [scalePi]
    · simp
  have hd : ∀ c', HasDerivAt f (f' c') c' := fun c' => by
    have := (hasFDerivAt_heatDensityPi σ (x - scalePi c' y)).comp_hasDerivAt c' (hz c')
    simpa [f, f', Function.comp_def, dotCLM_apply] using this
  have hf'c : Continuous f' := by
    simp only [f', dotProduct, heatGradPi]
    unfold scalePi
    have := continuous_heatDensityPi (d := d) σ
    fun_prop
  have hτc : Continuous fun c' => tubeK σ x y c' :=
    (continuous_tubeK σ).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hle : ∀ c', |f' c'| ≤ tubeK σ x y c' := by
    intro c'
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_neg, mul_comm, heatGradPi, abs_mul, abs_neg, abs_div, abs_of_pos hσ,
      abs_of_pos (heatDensityPi_pos hσ _)]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := c) (b := c₂)
    (fun c' _ => hd c') (hf'c.intervalIntegrable _ _)
  have habs := intervalIntegral.abs_integral_le_integral_abs (f := f') (μ := volume) h2
  have hmono : ∫ c' in c..c₂, |f' c'| ≤ ∫ c' in c..c₂, tubeK σ x y c' :=
    intervalIntegral.integral_mono_on h2 (hf'c.abs.intervalIntegrable _ _)
      (hτc.intervalIntegrable _ _) fun c' _ => hle c'
  have hint : ∫ c' in c..c₂, tubeK σ x y c' ≤ ∫ c' in c₁..c₂, tubeK σ x y c' :=
    intervalIntegral.integral_mono_interval h1 h2 le_rfl
      (Eventually.of_forall fun c' => tubeK_nonneg hσ x y c') (hτc.intervalIntegrable _ _)
  rw [← intervalIntegral.integral_of_le (h1.trans h2)]
  have : f c = f c₂ - ∫ c' in c..c₂, f' c' := by rw [hftc]; ring
  change f c ≤ f c₂ + _
  rw [this]
  linarith [neg_abs_le (∫ c' in c..c₂, f' c')]

/-! ### Weights and kernel bounds -/

/-- The linear weight `ℓ(y) = 1 + ∑ᵢ |yᵢ|`. -/
noncomputable def ell (y : Fin d → ℝ) : ℝ := 1 + ∑ i, |y i|

/-- `ℓ(y) ≥ 1`. -/
theorem one_le_ell (y : Fin d → ℝ) : 1 ≤ ell y := by
  unfold ell
  linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (y i)]

/-- `ℓ` is continuous. -/
theorem continuous_ell : Continuous (ell (d := d)) := by
  unfold ell; fun_prop

/-- `ℓ(y)² ≤ 2 (1 + d)(1 + |y|²)` (Cauchy–Schwarz). -/
theorem ell_sq_le (y : Fin d → ℝ) : ell y ^ 2 ≤ 2 * (1 + d) * (1 + ∑ i, y i ^ 2) := by
  unfold ell
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |y i|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h1
  have hS := sum_sq_nonneg y
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [sq_nonneg (1 - ∑ i, |y i|), mul_nonneg hd hS]

/-- `|c y|² = c² |y|²`. -/
theorem sum_sq_scalePi (c : ℝ) (y : Fin d → ℝ) :
    ∑ i, scalePi c y i ^ 2 = c ^ 2 * ∑ i, y i ^ 2 := by
  simp only [scalePi, mul_pow, Finset.mul_sum]

/-- `1 + |c y|² ≤ (1 + c²)(1 + |y|²)`. -/
theorem one_add_sum_sq_scalePi_le (c : ℝ) (y : Fin d → ℝ) :
    1 + ∑ i, scalePi c y i ^ 2 ≤ (1 + c ^ 2) * (1 + ∑ i, y i ^ 2) := by
  rw [sum_sq_scalePi]
  nlinarith [sum_sq_nonneg y, sq_nonneg c]

/-- `1 + |c y|² ≤ 1 + |y|²` for `c² ≤ 1`. -/
theorem one_add_sum_sq_scalePi_le_of_sq_le {c : ℝ} (hc : c ^ 2 ≤ 1) (y : Fin d → ℝ) :
    1 + ∑ i, scalePi c y i ^ 2 ≤ 1 + ∑ i, y i ^ 2 := by
  rw [sum_sq_scalePi]
  nlinarith [sum_sq_nonneg y]

section Kernel

variable {S₀ s v : ℝ}

/-- `(1 + |z|²) φ_s(z) ≤ K φ_{2v}(z)` for `0 < S₀ ≤ s ≤ v`, `K = envK d S₀ v`. -/
theorem one_add_mul_heatDensityPi_le_envK (hS₀ : 0 < S₀) (h1 : S₀ ≤ s) (h2 : s ≤ v)
    (z : Fin d → ℝ) :
    (1 + ∑ i, z i ^ 2) * heatDensityPi s z ≤ envK d S₀ v * heatDensityPi (2 * v) z := by
  have he := envelope hS₀ h1 h2 z
  have hu : 1 ≤ 1 + ∑ i, z i ^ 2 := by linarith [sum_sq_nonneg z]
  have hφ := (heatDensityPi_pos (hS₀.trans_le h1) z).le
  calc (1 + ∑ i, z i ^ 2) * heatDensityPi s z ≤ (1 + ∑ i, z i ^ 2) ^ 2 * heatDensityPi s z := by
        gcongr; nlinarith
    _ ≤ _ := he

/-- `φ_s(z) ≤ K φ_{2v}(z)` for `0 < S₀ ≤ s ≤ v`. -/
theorem heatDensityPi_le_envK (hS₀ : 0 < S₀) (h1 : S₀ ≤ s) (h2 : s ≤ v) (z : Fin d → ℝ) :
    heatDensityPi s z ≤ envK d S₀ v * heatDensityPi (2 * v) z := by
  refine le_trans ?_ (one_add_mul_heatDensityPi_le_envK hS₀ h1 h2 z)
  have hφ := (heatDensityPi_pos (hS₀.trans_le h1) z).le
  nlinarith [sum_sq_nonneg z]

/-- `|∂ᵢφ_s(z)| ≤ (1/S₀) K φ_{2v}(z)` for `0 < S₀ ≤ s ≤ v`. -/
theorem abs_heatGradPi_le_envK (hS₀ : 0 < S₀) (h1 : S₀ ≤ s) (h2 : s ≤ v) (z : Fin d → ℝ)
    (i : Fin d) :
    |heatGradPi s z i| ≤ 1 / S₀ * (envK d S₀ v * heatDensityPi (2 * v) z) := by
  have hs : 0 < s := hS₀.trans_le h1
  have hφ := heatDensityPi_pos hs z
  have hz := abs_le_one_add_sum_sq z i
  rw [heatGradPi, abs_mul, abs_neg, abs_div, abs_of_pos hs, abs_of_pos hφ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (one_add_mul_heatDensityPi_le_envK hS₀ h1 h2 z) (by positivity))
  rw [div_mul_eq_mul_div, one_div_mul_eq_div]
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hz hφ.le) hS₀ h1

/-- `|∂ᵢ²φ_s(z)| ≤ (1/S₀² + 1/S₀) K φ_{2v}(z)` for `0 < S₀ ≤ s ≤ v`. -/
theorem abs_heatHessPi_le_envK (hS₀ : 0 < S₀) (h1 : S₀ ≤ s) (h2 : s ≤ v) (z : Fin d → ℝ)
    (i : Fin d) :
    |heatHessPi s z i i| ≤ (1 / S₀ ^ 2 + 1 / S₀) * (envK d S₀ v * heatDensityPi (2 * v) z) := by
  have hs : 0 < s := hS₀.trans_le h1
  have hφ := heatDensityPi_pos hs z
  have hzi := sq_le_sum_sq z i
  have hu : 1 ≤ 1 + ∑ j, z j ^ 2 := by linarith [sum_sq_nonneg z]
  have hq : |z i * z i / s ^ 2 - (if i = i then 1 / s else 0)| ≤
      (1 / S₀ ^ 2 + 1 / S₀) * (1 + ∑ j, z j ^ 2) := by
    simp only [↓reduceIte]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (div_nonneg (mul_self_nonneg _) (by positivity)),
      abs_of_pos (one_div_pos.2 hs), ← sq]
    have e1 : z i ^ 2 / s ^ 2 ≤ (1 + ∑ j, z j ^ 2) / S₀ ^ 2 :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ hS₀.le h1 2)
    have e2 : 1 / s ≤ 1 / S₀ * (1 + ∑ j, z j ^ 2) :=
      (one_div_le_one_div_of_le hS₀ h1).trans (le_mul_of_one_le_right (by positivity) hu)
    calc _ ≤ (1 + ∑ j, z j ^ 2) / S₀ ^ 2 + 1 / S₀ * (1 + ∑ j, z j ^ 2) := add_le_add e1 e2
      _ = _ := by ring
  rw [heatHessPi, abs_mul, abs_of_pos hφ]
  calc _ ≤ (1 / S₀ ^ 2 + 1 / S₀) * (1 + ∑ j, z j ^ 2) * heatDensityPi s z :=
        mul_le_mul_of_nonneg_right hq hφ.le
    _ = (1 / S₀ ^ 2 + 1 / S₀) * ((1 + ∑ j, z j ^ 2) * heatDensityPi s z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_add_mul_heatDensityPi_le_envK hS₀ h1 h2 z)
        (by positivity)

/-- The generator kernel `g_s(x, w) = d φ_s(x - w) + x ⬝ᵥ ∇φ_s(x - w) + v Δφ_s(x - w)`, whose
`ρ`-average (with `w = c_t y`) is `d p_t + x ⬝ᵥ ∇p_t + v Δp_t`. -/
noncomputable def genK (s v : ℝ) (x w : Fin d → ℝ) : ℝ :=
  d * heatDensityPi s (x - w) + x ⬝ᵥ heatGradPi s (x - w) + v * heatLapPi s (x - w)

/-- The constant `A = d + 1/S₀ + v (1/S₀² + d/S₀)` of `abs_genK_le`. -/
noncomputable def genA (d : ℕ) (S₀ v : ℝ) : ℝ := d + 1 / S₀ + v * (1 / S₀ ^ 2 + d / S₀)

/-- **Moving-centre generator kernel bound.** For `0 < S₀ ≤ s ≤ v`, `0 ≤ c ≤ 1`:
`|g_s(x, c y)| ≤ A ℓ(y) K φ_{2v}(x - c y)`. The factor `x` of `x ⬝ᵥ ∇φ` is split as
`x = (x - c y) + c y`, so only the linear weight `ℓ(y)` appears. -/
theorem abs_genK_le (hS₀ : 0 < S₀) (h1 : S₀ ≤ s) (h2 : s ≤ v) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (x y : Fin d → ℝ) :
    |genK s v x (scalePi c y)| ≤
      genA d S₀ v * ell y * (envK d S₀ v * heatDensityPi (2 * v) (x - scalePi c y)) := by
  have hs : 0 < s := hS₀.trans_le h1
  have hv : 0 < v := hs.trans_le h2
  set z := x - scalePi c y with hz
  have hx : ∀ i, x i = z i + c * y i := fun i => by simp [hz, scalePi]
  set φ := heatDensityPi s z
  set u := 1 + ∑ i, z i ^ 2
  have hφ : 0 < φ := heatDensityPi_pos hs z
  have hS0 := sum_sq_nonneg z
  have hu : 1 ≤ u := by linarith
  have hℓ := one_le_ell y
  have henv := one_add_mul_heatDensityPi_le_envK hS₀ h1 h2 z
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdot : x ⬝ᵥ heatGradPi s z = -((∑ i, x i * z i) / s) * φ := by
    simp only [dotProduct, heatGradPi, Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hxz : |∑ i, x i * z i| ≤ ell y * u := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hi : ∀ i, |x i * z i| ≤ z i ^ 2 + |y i| * u := by
      intro i
      rw [hx i, abs_mul]
      have h3 : |z i + c * y i| ≤ |z i| + |y i| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hc0]
        nlinarith [abs_nonneg (y i)]
      have h4 : |z i| ≤ u := abs_le_one_add_sum_sq z i
      calc |z i + c * y i| * |z i| ≤ (|z i| + |y i|) * |z i| :=
            mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        _ = z i ^ 2 + |y i| * |z i| := by rw [add_mul, ← sq, sq_abs]
        _ ≤ z i ^ 2 + |y i| * u := by gcongr
    calc ∑ i, |x i * z i| ≤ ∑ i, (z i ^ 2 + |y i| * u) := Finset.sum_le_sum fun i _ => hi i
      _ = ∑ i, z i ^ 2 + (∑ i, |y i|) * u := by rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ u + (∑ i, |y i|) * u := by linarith
      _ = ell y * u := by unfold ell; ring
  have hlap : |heatLapPi s z| ≤ (1 / S₀ ^ 2 + d / S₀) * u * φ := by
    rw [heatLapPi_eq, ← Finset.sum_mul, abs_mul, abs_of_pos hφ]
    refine mul_le_mul_of_nonneg_right ?_ hφ.le
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have e1 : (∑ i, z i ^ 2) / s ^ 2 ≤ u / S₀ ^ 2 :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ hS₀.le h1 2)
    have e2 : (d : ℝ) * (1 / s) ≤ d / S₀ * u := by
      rw [mul_one_div]
      exact (div_le_div_of_nonneg_left hd hS₀ h1).trans (le_mul_of_one_le_right (by positivity) hu)
    have e3 : u / S₀ ^ 2 = 1 / S₀ ^ 2 * u := by ring
    nlinarith
  have hxzφ : |x ⬝ᵥ heatGradPi s z| ≤ ell y / S₀ * (u * φ) := by
    rw [hdot, abs_mul, abs_neg, abs_div, abs_of_pos hs, abs_of_pos hφ]
    calc |∑ i, x i * z i| / s * φ ≤ ell y * u / S₀ * φ := by
          gcongr
      _ = _ := by ring
  have hgen : |genK s v x (scalePi c y)| ≤ genA d S₀ v * ell y * (u * φ) := by
    unfold genK
    rw [← hz]
    have t1 : |(d : ℝ) * φ| ≤ d * (u * φ) := by
      rw [abs_mul, abs_of_nonneg hd, abs_of_pos hφ]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hφ.le hu) hd
    have t3 : |v * heatLapPi s z| ≤ v * (1 / S₀ ^ 2 + d / S₀) * (u * φ) := by
      rw [abs_mul, abs_of_pos hv]
      calc v * |heatLapPi s z| ≤ v * ((1 / S₀ ^ 2 + d / S₀) * u * φ) :=
            mul_le_mul_of_nonneg_left hlap hv.le
        _ = _ := by ring
    have hP : 0 ≤ u * φ := by positivity
    have hB : 0 ≤ v * (1 / S₀ ^ 2 + d / S₀) := by positivity
    have e := abs_add_le ((d : ℝ) * φ + x ⬝ᵥ heatGradPi s z) (v * heatLapPi s z)
    have e' := abs_add_le ((d : ℝ) * φ) (x ⬝ᵥ heatGradPi s z)
    have k1 : (d : ℝ) * (u * φ) ≤ d * ell y * (u * φ) := by
      have := mul_le_mul_of_nonneg_left hℓ hd
      nlinarith
    have k3 : v * (1 / S₀ ^ 2 + d / S₀) * (u * φ) ≤
        v * (1 / S₀ ^ 2 + d / S₀) * ell y * (u * φ) := by
      have := mul_le_mul_of_nonneg_left hℓ hB
      nlinarith
    have k2 : ell y / S₀ * (u * φ) = 1 / S₀ * ell y * (u * φ) := by ring
    unfold genA
    nlinarith
  refine hgen.trans (mul_le_mul_of_nonneg_left henv ?_)
  unfold genA
  have := one_le_ell y
  positivity

end Kernel

/-- For `v > 0` and `k ≤ 4`, `(1 + |z|²)^k φ_{2v}(z)` is Lebesgue integrable. -/
theorem integrable_pow_mul_heatDensityPi {v : ℝ} (hv : 0 < v) {k : ℕ} (hk : k ≤ 4) :
    Integrable fun z : Fin d → ℝ => (1 + ∑ i, z i ^ 2) ^ k * heatDensityPi (2 * v) z := by
  refine (integrable_envOU (d := d) hv).mono' ?_ (Eventually.of_forall fun z => ?_)
  · have := continuous_heatDensityPi (d := d) (2 * v)
    exact (by fun_prop : Continuous fun z : Fin d → ℝ =>
      (1 + ∑ i, z i ^ 2) ^ k * heatDensityPi (2 * v) z).aestronglyMeasurable
  · have hu : 1 ≤ 1 + ∑ i, z i ^ 2 := by linarith [sum_sq_nonneg z]
    have hφ := (heatDensityPi_pos (by positivity : 0 < 2 * v) z).le
    rw [Real.norm_of_nonneg (by positivity), envOU]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hu hk) hφ

/-! ### Moments, fixed-time bounds and the logarithm -/

section Flow

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a : ℝ}

/-- A fourth moment gives `(1 + |y|²)²` integrable. -/
theorem integrable_one_add_sq_sq (hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ) :
    Integrable (fun y => (1 + ∑ i, y i ^ 2) ^ 2) ρ := by
  refine ((integrable_const (2 : ℝ)).add (hmom4.const_mul 2)).mono'
    (by fun_prop : Continuous fun y : Fin d → ℝ => (1 + ∑ i, y i ^ 2) ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  change _ ≤ 2 + 2 * (∑ i, y i ^ 2) ^ 2
  nlinarith [sq_nonneg (1 - ∑ i, y i ^ 2)]

/-- A fourth moment gives a second moment. -/
theorem integrable_sum_sq_of_moment4 (hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ) :
    Integrable (fun y => ∑ i, y i ^ 2) ρ := by
  refine (integrable_one_add_sq_sq ρ hmom4).mono'
    (by fun_prop : Continuous fun y : Fin d → ℝ => ∑ i, y i ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have := sum_sq_nonneg y
  rw [Real.norm_of_nonneg this]
  nlinarith

/-- `ℓ` is `ρ`-integrable under a second moment. -/
theorem integrable_ell (hmom : Integrable (fun y => ∑ i, y i ^ 2) ρ) : Integrable ell ρ :=
  (integrable_const 1).add (integrable_finsetSum _ fun i _ => integrable_abs_coord ρ hmom i)

/-- `ℓ²` is `ρ`-integrable under a second moment. -/
theorem integrable_ell_sq (hmom : Integrable (fun y => ∑ i, y i ^ 2) ρ) :
    Integrable (fun y => ell y ^ 2) ρ :=
  (((integrable_const 1).add hmom).const_mul (2 * (1 + d))).mono'
    (continuous_ell.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (by positivity)]; exact ell_sq_le y)

/-- `c_t² ≤ 1` for `a, t ≥ 0`. -/
theorem ouC_sq_le_one (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t) : ouC a t ^ 2 ≤ 1 := by
  rw [ouC_sq]; exact Real.exp_le_one_iff.2 (by nlinarith)

/-- **The generator as a `ρ`-average.** For `t > 0`,
`d p_t(x) + x ⬝ᵥ ∇p_t(x) + v Δp_t(x) = ∫ g_{s_t}(x, c_t y) dρ(y)`. -/
theorem ouGen_eq_integral (hv : 0 < v) (ha : 0 < a) {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    d * ouDensity ρ v a t x + x ⬝ᵥ ouGrad ρ v a t x + v * ouLap ρ v a t x =
      ∫ y, genK (ouS v a t) v x (scalePi (ouC a t) y) ∂ρ := by
  have hS := ouS_pos hv ha ht
  have hφ : Integrable (fun w => heatDensityPi (ouS v a t) (x - w)) (ouLaw ρ a t) :=
    integrable_comp_of_bound _ (continuous_heatDensityPi _)
      (fun z => by rw [abs_of_pos (heatDensityPi_pos hS z)]; exact heatDensityPi_le hS z)
      (by fun_prop)
  have hG : ∀ i, Integrable (fun w => heatGradPi (ouS v a t) (x - w) i) (ouLaw ρ a t) :=
    fun i => integrable_comp_of_bound _ ((continuous_apply i).comp (continuous_heatGradPi _))
      (fun z => abs_heatGradPi_le hS z i) (by fun_prop)
  have hH : ∀ i, Integrable (fun w => heatHessPi (ouS v a t) (x - w) i i) (ouLaw ρ a t) :=
    fun i => integrable_comp_of_bound _ (continuous_heatHessPi _ i i)
      (fun z => abs_heatHessPi_le hS z i i) (by fun_prop)
  have hc : Continuous fun w => genK (ouS v a t) v x w := by
    unfold genK
    have := continuous_heatDensityPi (d := d) (ouS v a t)
    have := continuous_heatGradPi (d := d) (ouS v a t)
    have := continuous_heatLapPi (d := d) (ouS v a t)
    simp only [dotProduct]
    fun_prop
  rw [← integral_ouLaw ρ a t hc]
  have e : (fun w => genK (ouS v a t) v x w) = fun w =>
      d * heatDensityPi (ouS v a t) (x - w) + ∑ i, x i * heatGradPi (ouS v a t) (x - w) i +
        v * ∑ i, heatHessPi (ouS v a t) (x - w) i i := funext fun w => rfl
  rw [e, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_finsetSum,
    integral_finsetSum]
  · simp only [integral_const_mul]
    rfl
  all_goals first
    | exact fun i _ => hH i
    | exact fun i _ => (hG i).const_mul _
    | exact hφ.const_mul _
    | exact integrable_finsetSum _ fun i _ => (hG i).const_mul _
    | exact (integrable_finsetSum _ fun i _ => hH i).const_mul _
    | exact (hφ.const_mul _).add (integrable_finsetSum _ fun i _ => (hG i).const_mul _)

/-- The fixed-time comparison density `q_t(x) = ∫ φ_{2v}(x - w) d(c_t ρ)(w)`. -/
noncomputable def ouQ (ρ : Measure (Fin d → ℝ)) (v a t : ℝ) (x : Fin d → ℝ) : ℝ :=
  heatFlowDensityPi (ouLaw ρ a t) (2 * v) x

section Fixed

variable {t S₀ : ℝ}

omit [IsProbabilityMeasure ρ] in
/-- `q_t ≥ 0`. -/
theorem ouQ_nonneg (hv : 0 < v) (x : Fin d → ℝ) : 0 ≤ ouQ ρ v a t x :=
  integral_nonneg fun w => (heatDensityPi_pos (by positivity : 0 < 2 * v) _).le

/-- `x ↦ φ_{2v}(x - w)` is `c_t ρ`-integrable. -/
theorem integrable_heatDensityPi_two (hv : 0 < v) (x : Fin d → ℝ) :
    Integrable (fun w => heatDensityPi (2 * v) (x - w)) (ouLaw ρ a t) :=
  integrable_comp_of_bound _ (continuous_heatDensityPi _)
    (fun z => by
      rw [abs_of_pos (heatDensityPi_pos (by positivity) z)]
      exact heatDensityPi_le (by positivity) z)
    (by fun_prop)

/-- `p_t(x) ≤ K q_t(x)` for `0 < S₀ ≤ s_t`. -/
theorem ouDensity_le_ouQ (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) (hS₀ : 0 < S₀)
    (h1 : S₀ ≤ ouS v a t) (x : Fin d → ℝ) :
    ouDensity ρ v a t x ≤ envK d S₀ v * ouQ ρ v a t x := by
  have hS := ouS_pos hv ha ht
  unfold ouDensity ouQ heatFlowDensityPi
  rw [← integral_const_mul]
  exact integral_mono (integrable_comp_of_bound _ (continuous_heatDensityPi _)
      (fun z => by rw [abs_of_pos (heatDensityPi_pos hS z)]; exact heatDensityPi_le hS z)
      (by fun_prop))
    ((integrable_heatDensityPi_two ρ hv x).const_mul _)
    fun w => heatDensityPi_le_envK hS₀ h1 (ouS_le hv) _

/-- `|∂ᵢp_t(x)| ≤ (1/S₀) K q_t(x)` for `0 < S₀ ≤ s_t`. -/
theorem abs_ouGrad_le_ouQ (hv : 0 < v) (hS₀ : 0 < S₀)
    (h1 : S₀ ≤ ouS v a t) (x : Fin d → ℝ) (i : Fin d) :
    |ouGrad ρ v a t x i| ≤ 1 / S₀ * (envK d S₀ v * ouQ ρ v a t x) := by
  unfold ouGrad heatFlowGradPi ouQ heatFlowDensityPi
  rw [← integral_const_mul, ← integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    (((integrable_heatDensityPi_two ρ hv x).const_mul _).const_mul _)
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact abs_heatGradPi_le_envK hS₀ h1 (ouS_le hv) _ i)

/-- `|∂ᵢ²p_t(x)| ≤ (1/S₀² + 1/S₀) K q_t(x)` for `0 < S₀ ≤ s_t`. -/
theorem abs_ouHess_le_ouQ (hv : 0 < v) (hS₀ : 0 < S₀)
    (h1 : S₀ ≤ ouS v a t) (x : Fin d → ℝ) (i : Fin d) :
    |heatFlowHessPi (ouLaw ρ a t) (ouS v a t) x i i| ≤
      (1 / S₀ ^ 2 + 1 / S₀) * (envK d S₀ v * ouQ ρ v a t x) := by
  unfold heatFlowHessPi ouQ heatFlowDensityPi
  rw [← integral_const_mul, ← integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    (((integrable_heatDensityPi_two ρ hv x).const_mul _).const_mul _)
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact abs_heatHessPi_le_envK hS₀ h1 (ouS_le hv) _ i)

/-- **Fixed-time integrability (fourth moment).** If `f` is continuous and
`|f(x)| ≤ C (1 + |x|²)^k K q_t(x)` with `k ≤ 2`, `C, K ≥ 0`, `t ≥ 0`, then `f` is Lebesgue
integrable (Tonelli via `integrable_integral_kernel`). -/
theorem integrable_of_le_ouQ (hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ) (hv : 0 < v)
    (ha : 0 < a) (ht : 0 ≤ t) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) {k : ℕ} (hk : k ≤ 2)
    (h : ∀ x, |f x| ≤ C * (1 + ∑ i, x i ^ 2) ^ k * (K * ouQ ρ v a t x)) : Integrable f := by
  have hv2 : 0 < 2 * v := by positivity
  have hPm : Integrable (fun w : Fin d → ℝ => (1 + ∑ i, id w i ^ 2) ^ 2 * 1) (ouLaw ρ a t) := by
    have hc : Continuous fun w : Fin d → ℝ => (1 + ∑ i, id w i ^ 2) ^ 2 * 1 := by fun_prop
    rw [ouLaw, integrable_map_measure hc.aestronglyMeasurable
      (measurable_scalePi _).aemeasurable]
    refine (integrable_one_add_sq_sq ρ hmom4).mono' (hc.comp (by unfold scalePi; fun_prop)
      |>.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    have h2 := one_add_sum_sq_scalePi_le_of_sq_le (ouC_sq_le_one ha.le ht) y
    simp only [Function.comp_apply, id, mul_one]
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by linarith [sum_sq_nonneg (scalePi (ouC a t) y)]) h2 2
  have hI := integrable_integral_kernel (ν := ouLaw ρ a t) 2 measurable_id
    (R := fun _ z => heatDensityPi (2 * v) z)
    ((continuous_heatDensityPi _).measurable.comp measurable_snd)
    (fun _ z => (heatDensityPi_pos hv2 z).le) (P := fun _ => 1) (Q := heatDensityPi (2 * v))
    (fun _ z => by simp) (integrable_pow_mul_heatDensityPi hv (by norm_num)) hPm
  refine (hI.const_mul (C * K)).mono' hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (h x).trans ?_
  have hu : 1 ≤ 1 + ∑ i, x i ^ 2 := by linarith [sum_sq_nonneg x]
  have hq := ouQ_nonneg (a := a) (t := t) ρ hv x
  have e : ∫ w, (1 + ∑ i, x i ^ 2) ^ 2 * heatDensityPi (2 * v) (x - id w) ∂(ouLaw ρ a t) =
      (1 + ∑ i, x i ^ 2) ^ 2 * ouQ ρ v a t x := by
    rw [integral_const_mul]; rfl
  rw [e]
  calc C * (1 + ∑ i, x i ^ 2) ^ k * (K * ouQ ρ v a t x)
      ≤ C * (1 + ∑ i, x i ^ 2) ^ 2 * (K * ouQ ρ v a t x) := by
        gcongr
    _ = _ := by ring

end Fixed

/-- The constant of the moment log-ratio bound `abs_log_ouDensity_div_le_moment`. -/
noncomputable def logLM (ρ : Measure (Fin d → ℝ)) (d : ℕ) (S₀ v : ℝ) : ℝ :=
  d * (|Real.log (2 * Real.pi * S₀)| + |Real.log (2 * Real.pi * v)|) +
    (1 + ∫ y, ∑ i, y i ^ 2 ∂ρ) / S₀ + |Real.log (gc d v)| + 1 / (2 * v)

omit [IsProbabilityMeasure ρ] in
/-- `logLM ≥ 0`. -/
theorem logLM_nonneg {S₀ : ℝ} (hS₀ : 0 < S₀) (hv : 0 < v) : 0 ≤ logLM ρ d S₀ v := by
  unfold logLM
  have : 0 ≤ ∫ y, ∑ i, y i ^ 2 ∂ρ := integral_nonneg fun y => sum_sq_nonneg y
  positivity

/-- **Time-uniform log-ratio bound under a second moment.** For `t > 0` with
`0 < S₀ ≤ s_t`: `|log(p_t(x)/φ_v(x))| ≤ L (1 + |x|²)`, `L = logLM ρ d S₀ v` (Jensen's lower
bound `abs_log_heatFlowDensityPi_le` for `p_t`, and `∫ |c_t y|² dρ ≤ ∫ |y|² dρ`). -/
theorem abs_log_ouDensity_div_le_moment (hmom : Integrable (fun y => ∑ i, y i ^ 2) ρ)
    (hv : 0 < v) (ha : 0 < a) {t S₀ : ℝ} (ht : 0 < t) (hS₀ : 0 < S₀) (h1 : S₀ ≤ ouS v a t)
    (x : Fin d → ℝ) :
    |Real.log (ouDensity ρ v a t x / heatDensityPi v x)| ≤
      logLM ρ d S₀ v * (1 + ∑ i, x i ^ 2) := by
  have hS := ouS_pos hv ha ht
  have hp := ouDensity_pos ρ hv ha ht x
  have hφ := heatDensityPi_pos hv x
  rw [Real.log_div hp.ne' hφ.ne']
  have hlp := abs_log_heatFlowDensityPi_le (ρ := ouLaw ρ a t) (integrable_sum_sq_ouLaw ρ hmom a t)
    hS x
  change |Real.log (ouDensity ρ v a t x)| ≤ _ at hlp
  have hgc := abs_log_gc_le (d := d) hS₀ h1 (ouS_le hv)
  set M := ∫ y, ∑ i, y i ^ 2 ∂ρ
  set X := ∑ i, x i ^ 2
  have hX := sum_sq_nonneg x
  have hM0 : 0 ≤ M := integral_nonneg fun y => sum_sq_nonneg y
  have hMt : ∫ w, ∑ i, w i ^ 2 ∂(ouLaw ρ a t) ≤ M := by
    rw [integral_ouLaw ρ a t (by fun_prop)]
    have hsc : Integrable (fun y => ∑ i, scalePi (ouC a t) y i ^ 2) ρ :=
      (hmom.const_mul (ouC a t ^ 2)).congr (Eventually.of_forall fun y => by
        simp only [sum_sq_scalePi])
    refine integral_mono hsc hmom fun y => ?_
    simp only [sum_sq_scalePi]
    have := ouC_sq_le_one ha.le ht.le
    nlinarith [sum_sq_nonneg y]
  have hMt0 : 0 ≤ ∫ w, ∑ i, w i ^ 2 ∂(ouLaw ρ a t) := integral_nonneg fun w => sum_sq_nonneg w
  have k1 : (X + ∫ w, ∑ i, w i ^ 2 ∂(ouLaw ρ a t)) / ouS v a t ≤ (1 + M) / S₀ * (1 + X) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (by positivity) (by nlinarith) hS₀ h1
  have hlogφ := abs_log_heatDensityPi_le (d := d) hv x
  have k2 : X / (2 * v) ≤ 1 / (2 * v) * (1 + X) := by
    rw [div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hA : 0 ≤ (d : ℝ) * (|Real.log (2 * Real.pi * S₀)| + |Real.log (2 * Real.pi * v)|) := by
    positivity
  have hB : 0 ≤ |Real.log (gc d v)| := abs_nonneg _
  have k3 : (d : ℝ) * (|Real.log (2 * Real.pi * S₀)| + |Real.log (2 * Real.pi * v)|) ≤
      (d : ℝ) * (|Real.log (2 * Real.pi * S₀)| + |Real.log (2 * Real.pi * v)|) * (1 + X) :=
    le_mul_of_one_le_right hA (by linarith)
  have k4 : |Real.log (gc d v)| ≤ |Real.log (gc d v)| * (1 + X) :=
    le_mul_of_one_le_right hB (by linarith)
  refine (abs_sub _ _).trans ?_
  unfold logLM
  nlinarith

/-! ### `TransportKLRegularity` under a fourth moment -/

/-- Scalar bound `|p + y G + w H| ≤ (1 + A₁ + w A₂) u P` from `|p| ≤ P`, `|y| ≤ u`,
`|G| ≤ A₁ P`, `|H| ≤ A₂ P`, `u ≥ 1`. -/
theorem abs_dflux_le {p G H y u P A₁ A₂ w : ℝ} (hu : 1 ≤ u) (hP : 0 ≤ P)
    (hA₂ : 0 ≤ A₂) (hw : 0 ≤ w) (hp : |p| ≤ P) (hy : |y| ≤ u) (hG : |G| ≤ A₁ * P)
    (hH : |H| ≤ A₂ * P) : |p + y * G + w * H| ≤ (1 + A₁ + w * A₂) * u ^ 1 * P := by
  have h1 : |y * G| ≤ A₁ * u * P := by
    rw [abs_mul]
    calc |y| * |G| ≤ u * (A₁ * P) := mul_le_mul hy hG (abs_nonneg _) (by linarith)
      _ = A₁ * u * P := by ring
  have h2 : |w * H| ≤ w * (A₂ * u * P) := by
    rw [abs_mul, abs_of_nonneg hw]
    refine mul_le_mul_of_nonneg_left (hH.trans ?_) hw
    have := mul_le_mul_of_nonneg_left hu hA₂
    nlinarith
  have h3 : P ≤ u * P := le_mul_of_one_le_left hP hu
  have e1 := abs_add_le (p + y * G) (w * H)
  have e2 := abs_add_le p (y * G)
  rw [pow_one]
  nlinarith

/-- **`TransportKLRegularity` along the OU probability flow under a fourth moment
(Verified).** Let `ρ` be a probability law on `Fin d → ℝ` with `∫ |y|⁴ dρ(y) < ∞`
(`hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ`), and `v, a > 0`. Then for every `t₀ > 0`,
`KLDissipation.TransportKLRegularity p π vel t₀` holds for the OU marginal densities
`p = ouDensity ρ v a`, the target density `π = heatDensityPi v` of `N(0, v I)` and the ideal
velocity `vel = ouVelocity ρ v a`. The time-uniform domination on `B(t₀, t₀/2)` uses the tube
estimate `heatDensityPi_le_tube` in the moving centre `c_t y`, `c_t = e^{-at}`; the fixed-time
fields use `integrable_of_le_ouQ`. -/
theorem transportKLRegularity_ou_moment
    (hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ) (hv : 0 < v) (ha : 0 < a) {t₀ : ℝ}
    (ht₀ : 0 < t₀) :
    KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a)
      t₀ := by
  have hmom := integrable_sum_sq_of_moment4 ρ hmom4
  have hN2 := integrable_one_add_sq_sq ρ hmom4
  have hv2 : 0 < 2 * v := by positivity
  set S₀ := ouS v a (t₀ / 2)
  have hS₀ : 0 < S₀ := ouS_pos hv ha (by positivity)
  set K := envK d S₀ v
  have hK : 0 ≤ K := envK_nonneg hS₀ hv
  set L := logLM ρ d S₀ v
  have hL : 0 ≤ L := logLM_nonneg ρ hS₀ hv
  set A₁ := 1 / S₀
  set A₂ := 1 / S₀ ^ 2 + 1 / S₀
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  have h1 : S₀ ≤ ouS v a t₀ := ouS_mono hv ha (by linarith)
  have hS := ouS_pos hv ha ht₀
  -- fixed-time pointwise ingredients
  have hP : ∀ x, 0 ≤ K * ouQ ρ v a t₀ x := fun x => mul_nonneg hK (ouQ_nonneg ρ hv x)
  have hu : ∀ x : Fin d → ℝ, 1 ≤ 1 + ∑ i, x i ^ 2 := fun x => by linarith [sum_sq_nonneg x]
  have hp : ∀ x, |ouDensity ρ v a t₀ x| ≤ K * ouQ ρ v a t₀ x := fun x => by
    rw [abs_of_pos (ouDensity_pos ρ hv ha ht₀ x)]
    exact ouDensity_le_ouQ ρ hv ha ht₀ hS₀ h1 x
  have hG := abs_ouGrad_le_ouQ ρ hv hS₀ h1
  have hH := abs_ouHess_le_ouQ ρ hv hS₀ h1
  have hlog := abs_log_ouDensity_div_le_moment ρ hmom hv ha ht₀ hS₀ h1
  have hpc := continuous_ouDensity ρ hv ha ht₀
  have hGc := continuous_ouGrad ρ hv ha ht₀
  have hHc : ∀ i, Continuous fun x => heatFlowHessPi (ouLaw ρ a t₀) (ouS v a t₀) x i i :=
    fun i => continuous_heatFlowHessPi (ρ := ouLaw ρ a t₀) hS i i
  have hlc : Continuous fun x => Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x) :=
    (hpc.div (continuous_heatDensityPi v) fun x => (heatDensityPi_pos hv x).ne').log
      fun x => (div_pos (ouDensity_pos ρ hv ha ht₀ x) (heatDensityPi_pos hv x)).ne'
  have eflux : ∀ i, (fun x => ouDensity ρ v a t₀ x * ouVelocity ρ v a t₀ x i) =
      fun x => -a * (x i * ouDensity ρ v a t₀ x + v * ouGrad ρ v a t₀ x i) := fun i =>
    funext fun x => ouDensity_mul_ouVelocity ρ hv ha ht₀ x i
  have edflux : ∀ i, (fun x => partialDeriv i
      (fun y => ouDensity ρ v a t₀ y * ouVelocity ρ v a t₀ y i) x) =
      fun x => -a * (ouDensity ρ v a t₀ x + x i * ouGrad ρ v a t₀ x i +
        v * heatFlowHessPi (ouLaw ρ a t₀) (ouS v a t₀) x i i) := fun i =>
    funext fun x => partialDeriv_ouFlux ρ hv ha ht₀ i x
  have hdfluxb : ∀ i x, |-a * (ouDensity ρ v a t₀ x + x i * ouGrad ρ v a t₀ x i +
      v * heatFlowHessPi (ouLaw ρ a t₀) (ouS v a t₀) x i i)| ≤
      a * (1 + A₁ + v * A₂) * (1 + ∑ j, x j ^ 2) ^ 1 * (K * ouQ ρ v a t₀ x) := by
    intro i x
    rw [abs_mul, abs_neg, abs_of_pos ha, mul_assoc a, mul_assoc a]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    exact abs_dflux_le (hu x) (hP x) hA₂ hv.le (hp x) (abs_le_one_add_sum_sq x i)
      (hG x i) (hH x i)
  have hfluxb : ∀ i x, |-a * (x i * ouDensity ρ v a t₀ x + v * ouGrad ρ v a t₀ x i)| ≤
      a * (1 + v * A₁) * (1 + ∑ j, x j ^ 2) ^ 1 * (K * ouQ ρ v a t₀ x) := fun i x =>
    abs_flux_aux ha.le (hu x) hv.le (hp x) (abs_le_one_add_sum_sq x i)
      ((hG x i).trans (by
        have := mul_le_mul_of_nonneg_left (hu x) (mul_nonneg hA₁ (hP x))
        nlinarith))
  -- the time-uniform domination: the moving-centre tube
  set cm := ouC a (3 * t₀ / 2)
  set cp := ouC a (t₀ / 2)
  have hcp : cp ^ 2 ≤ 1 := ouC_sq_le_one ha.le (by positivity)
  have : IsFiniteMeasure (volume.restrict (Ioc cm cp)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set ν := ρ.prod (volume.restrict (Ioc cm cp))
  set J₁ : (Fin d → ℝ) → ℝ := fun x =>
    ∫ y, (1 + ∑ i, x i ^ 2) ^ 1 * (ell y * heatDensityPi (2 * v) (x - scalePi cp y)) ∂ρ
  set J₂ : (Fin d → ℝ) → ℝ := fun x =>
    ∫ ω, (1 + ∑ i, x i ^ 2) ^ 1 * (ell ω.1 * tubeK (2 * v) x ω.1 ω.2) ∂ν
  have hJ₁ : Integrable J₁ := by
    refine integrable_integral_kernel (ν := ρ) 1 (measurable_scalePi cp)
      (R := fun y z => ell y * heatDensityPi (2 * v) z) ?_
      (fun y z => mul_nonneg (by linarith [one_le_ell y]) (heatDensityPi_pos hv2 z).le)
      (P := ell) (Q := heatDensityPi (2 * v)) (fun _ _ => le_rfl)
      (integrable_pow_mul_heatDensityPi hv (by norm_num)) ?_
    · have := continuous_heatDensityPi (d := d) (2 * v)
      exact ((continuous_ell.comp continuous_fst).mul (this.comp continuous_snd)).measurable
    · refine (hN2.const_mul (2 * (1 + d))).mono' ((by unfold scalePi; fun_prop :
        Continuous fun y : Fin d → ℝ => (1 + ∑ i, scalePi cp y i ^ 2) ^ 1).mul
          continuous_ell).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      have h2 := one_add_sum_sq_scalePi_le_of_sq_le hcp y
      have h3 := ell_sq_le y
      have h4 := one_le_ell y
      have h5 := sum_sq_nonneg (scalePi cp y)
      have h6 := sum_sq_nonneg y
      rw [Real.norm_of_nonneg (by positivity), pow_one]
      have h7 : ell y ≤ 2 * (1 + d) * (1 + ∑ i, y i ^ 2) := by nlinarith
      calc (1 + ∑ i, scalePi cp y i ^ 2) * ell y
          ≤ (1 + ∑ i, y i ^ 2) * (2 * (1 + d) * (1 + ∑ i, y i ^ 2)) :=
            mul_le_mul h2 h7 (by linarith) (by linarith)
        _ = _ := by ring
  have hJ₂ : Integrable J₂ := by
    refine integrable_integral_kernel (ν := ν) 1 (m := fun ω => scalePi ω.2 ω.1)
      (by unfold scalePi; fun_prop)
      (R := fun ω z => ell ω.1 * ∑ j, |ω.1 j| * (|z j| / (2 * v) * heatDensityPi (2 * v) z))
      ?_ ?_ (P := fun ω => ell ω.1 ^ 2)
      (Q := fun z => (1 + ∑ i, z i ^ 2) / (2 * v) * heatDensityPi (2 * v) z) ?_ ?_ ?_
    · have := continuous_heatDensityPi (d := d) (2 * v)
      have := continuous_ell (d := d)
      exact Continuous.measurable (by fun_prop)
    · intro ω z
      have := one_le_ell ω.1
      refine mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => ?_)
      have := heatDensityPi_pos hv2 z
      positivity
    · intro ω z
      have hφ := heatDensityPi_pos hv2 z
      have hℓ := one_le_ell ω.1
      have hsum : ∑ j, |ω.1 j| * (|z j| / (2 * v) * heatDensityPi (2 * v) z) ≤
          ell ω.1 * ((1 + ∑ i, z i ^ 2) / (2 * v) * heatDensityPi (2 * v) z) := by
        calc ∑ j, |ω.1 j| * (|z j| / (2 * v) * heatDensityPi (2 * v) z)
            ≤ ∑ j, |ω.1 j| * ((1 + ∑ i, z i ^ 2) / (2 * v) * heatDensityPi (2 * v) z) := by
              refine Finset.sum_le_sum fun j _ => ?_
              gcongr
              exact abs_le_one_add_sum_sq z j
          _ = (∑ j, |ω.1 j|) * ((1 + ∑ i, z i ^ 2) / (2 * v) * heatDensityPi (2 * v) z) := by
              rw [Finset.sum_mul]
          _ ≤ _ := by
              have : 0 ≤ (1 + ∑ i, z i ^ 2) / (2 * v) * heatDensityPi (2 * v) z := by
                have := sum_sq_nonneg z; positivity
              gcongr
              unfold ell; linarith
      calc ell ω.1 * ∑ j, |ω.1 j| * (|z j| / (2 * v) * heatDensityPi (2 * v) z)
          ≤ ell ω.1 * (ell ω.1 * ((1 + ∑ i, z i ^ 2) / (2 * v) * heatDensityPi (2 * v) z)) :=
            mul_le_mul_of_nonneg_left hsum (by linarith)
        _ = _ := by ring
    · refine ((integrable_pow_mul_heatDensityPi (k := 2) hv (by norm_num)).div_const (2 * v)).congr
        (Eventually.of_forall fun z => ?_)
      simp only
      ring
    · have hc2 : Integrable (fun c : ℝ => 1 + c ^ 2) (volume.restrict (Ioc cm cp)) :=
        (by fun_prop : Continuous fun c : ℝ => 1 + c ^ 2).integrableOn_Ioc
      refine ((hN2.const_mul (2 * (1 + d))).mul_prod hc2).mono' ?_
        (Eventually.of_forall fun ω => ?_)
      · have := continuous_ell (d := d)
        exact Continuous.aestronglyMeasurable (by unfold scalePi; fun_prop)
      · have h2 := one_add_sum_sq_scalePi_le ω.2 ω.1
        have h3 := ell_sq_le ω.1
        have h5 := sum_sq_nonneg (scalePi ω.2 ω.1)
        have h6 := sum_sq_nonneg ω.1
        rw [Real.norm_of_nonneg (by positivity), pow_one]
        calc (1 + ∑ i, scalePi ω.2 ω.1 i ^ 2) * ell ω.1 ^ 2
            ≤ ((1 + ω.2 ^ 2) * (1 + ∑ i, ω.1 i ^ 2)) * (2 * (1 + d) * (1 + ∑ i, ω.1 i ^ 2)) :=
              mul_le_mul h2 h3 (by positivity) (by positivity)
          _ = _ := by ring
  have hball : ∀ t ∈ Metric.ball t₀ (t₀ / 2), t₀ / 2 < t ∧ t < 3 * t₀ / 2 := fun t ht => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht; constructor <;> linarith
  refine ⟨⟨t₀ / 2, by positivity, fun x => a * (genA d S₀ v * K) * (L + 1) * (J₁ x + J₂ x),
      fun t ht => ?_, Eventually.of_forall fun x t ht => ?_,
      (hJ₁.add hJ₂).const_mul _⟩, integrable_ouKL ρ hv ha ht₀ hmom,
    fun x => (hasFDerivAt_ouDensity ρ hv ha ht₀ x).differentiableAt,
    differentiable_ouVelocity ρ hv ha ht₀, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_⟩
  · -- measurability near `t₀`
    obtain ⟨h2, -⟩ := hball t ht
    exact (continuous_ouDensity ρ hv ha (by linarith)).aestronglyMeasurable
  · -- time-uniform domination
    obtain ⟨htt, htt'⟩ := hball t ht
    have ht0 : 0 < t := by linarith
    have h1t : S₀ ≤ ouS v a t := ouS_mono hv ha htt.le
    have hc0 : 0 ≤ ouC a t := (ouC_pos a t).le
    have hc1 : ouC a t ≤ 1 := by have := ouC_sq_le_one ha.le ht0.le; nlinarith
    have hcm : cm ≤ ouC a t := by
      simp only [cm, ouC]; exact Real.exp_le_exp.2 (by nlinarith)
    have hcp' : ouC a t ≤ cp := by
      simp only [cp, ouC]; exact Real.exp_le_exp.2 (by nlinarith)
    have hgc := gc_pos (d := d) hv2
    have hell := integrable_ell ρ hmom
    have hint1 : ∀ c' : ℝ,
        Integrable (fun y => ell y * heatDensityPi (2 * v) (x - scalePi c' y)) ρ := by
      intro c'
      refine (hell.const_mul (gc d (2 * v))).mono' ?_ (Eventually.of_forall fun y => ?_)
      · have := continuous_heatDensityPi (d := d) (2 * v)
        have := continuous_ell (d := d)
        exact Continuous.aestronglyMeasurable (by unfold scalePi; fun_prop)
      · have hℓ := one_le_ell y
        rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (heatDensityPi_pos hv2 _).le),
          mul_comm]
        exact mul_le_mul_of_nonneg_right (heatDensityPi_le hv2 _) (by linarith)
    have htb : ∀ y c', tubeK (2 * v) x y c' ≤
        (1 + 2 * (2 * v)) / (2 * v) * gc d (2 * v) * ell y := by
      intro y c'
      have hB : 0 ≤ (1 + 2 * (2 * v)) / (2 * v) * gc d (2 * v) := by positivity
      unfold tubeK
      calc ∑ j, |y j| * (|(x - scalePi c' y) j| / (2 * v) *
            heatDensityPi (2 * v) (x - scalePi c' y))
          ≤ ∑ j, |y j| * ((1 + 2 * (2 * v)) / (2 * v) * gc d (2 * v)) := by
            refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            have := abs_heatGradPi_le hv2 (x - scalePi c' y) j
            rwa [heatGradPi, abs_mul, abs_neg, abs_div, abs_of_pos hv2,
              abs_of_pos (heatDensityPi_pos hv2 _)] at this
        _ = (∑ j, |y j|) * ((1 + 2 * (2 * v)) / (2 * v) * gc d (2 * v)) := by
            rw [Finset.sum_mul]
        _ ≤ _ := by
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ hB
            unfold ell; linarith
    have hint2 : Integrable (fun ω : (Fin d → ℝ) × ℝ => ell ω.1 * tubeK (2 * v) x ω.1 ω.2) ν := by
      refine (((integrable_ell_sq ρ hmom).comp_fst (volume.restrict (Ioc cm cp))).const_mul
        ((1 + 2 * (2 * v)) / (2 * v) * gc d (2 * v))).mono' ?_
        (Eventually.of_forall fun ω => ?_)
      · exact ((continuous_ell.comp continuous_fst).mul ((continuous_tubeK (2 * v)).comp
          (continuous_const.prodMk (continuous_fst.prodMk continuous_snd)))).aestronglyMeasurable
      · have hℓ := one_le_ell ω.1
        rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (tubeK_nonneg hv2 _ _ _))]
        calc ell ω.1 * tubeK (2 * v) x ω.1 ω.2
            ≤ ell ω.1 * ((1 + 2 * (2 * v)) / (2 * v) * gc d (2 * v) * ell ω.1) :=
              mul_le_mul_of_nonneg_left (htb _ _) (by linarith)
          _ = _ := by ring
    have hA : 0 ≤ genA d S₀ v := by unfold genA; positivity
    have hGb : |d * ouDensity ρ v a t x + x ⬝ᵥ ouGrad ρ v a t x + v * ouLap ρ v a t x| ≤
        genA d S₀ v * K * ((∫ y, ell y * heatDensityPi (2 * v) (x - scalePi cp y) ∂ρ) +
          ∫ ω, ell ω.1 * tubeK (2 * v) x ω.1 ω.2 ∂ν) := by
      rw [ouGen_eq_integral ρ hv ha ht0 x, ← Real.norm_eq_abs]
      calc ‖∫ y, genK (ouS v a t) v x (scalePi (ouC a t) y) ∂ρ‖
          ≤ ∫ y, genA d S₀ v * K * (ell y * heatDensityPi (2 * v) (x - scalePi (ouC a t) y))
              ∂ρ :=
            norm_integral_le_of_norm_le ((hint1 _).const_mul _)
              (Eventually.of_forall fun y => by
                rw [Real.norm_eq_abs]
                refine (abs_genK_le hS₀ h1t (ouS_le hv) hc0 hc1 x y).trans (le_of_eq ?_)
                ring)
        _ ≤ ∫ y, genA d S₀ v * K * (ell y * heatDensityPi (2 * v) (x - scalePi cp y) +
              ∫ c', ell y * tubeK (2 * v) x y c' ∂(volume.restrict (Ioc cm cp))) ∂ρ := by
            refine integral_mono ((hint1 _).const_mul _)
              (((hint1 cp).add hint2.integral_prod_left).const_mul _) fun y => ?_
            have htube := heatDensityPi_le_tube hv2 hcm hcp' x y
            have hℓ := one_le_ell y
            simp only
            rw [integral_const_mul, ← mul_add]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htube (by linarith))
              (mul_nonneg hA hK)
        _ = _ := by
            rw [integral_const_mul, integral_add (hint1 cp) hint2.integral_prod_left,
              integral_prod _ hint2]
    have hl1 : |Real.log (ouDensity ρ v a t x / heatDensityPi v x) + 1| ≤
        (L + 1) * (1 + ∑ i, x i ^ 2) := by
      have hlt := abs_log_ouDensity_div_le_moment ρ hmom hv ha ht0 hS₀ h1t x
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      nlinarith [hu x]
    have eJ₁ : J₁ x = (1 + ∑ i, x i ^ 2) *
        ∫ y, ell y * heatDensityPi (2 * v) (x - scalePi cp y) ∂ρ := by
      simp only [J₁, pow_one, integral_const_mul]
    have eJ₂ : J₂ x = (1 + ∑ i, x i ^ 2) * ∫ ω, ell ω.1 * tubeK (2 * v) x ω.1 ω.2 ∂ν := by
      simp only [J₂, pow_one, integral_const_mul]
    have hI₁ : 0 ≤ ∫ y, ell y * heatDensityPi (2 * v) (x - scalePi cp y) ∂ρ :=
      integral_nonneg fun y =>
        mul_nonneg (by linarith [one_le_ell y]) (heatDensityPi_pos hv2 _).le
    have hI₂ : 0 ≤ ∫ ω, ell ω.1 * tubeK (2 * v) x ω.1 ω.2 ∂ν :=
      integral_nonneg fun ω => mul_nonneg (by linarith [one_le_ell ω.1]) (tubeK_nonneg hv2 _ _ _)
    rw [divergence_ouFlux ρ hv ha ht0, neg_neg, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos ha]
    beta_reduce
    rw [eJ₁, eJ₂]
    calc a * |d * ouDensity ρ v a t x + x ⬝ᵥ ouGrad ρ v a t x + v * ouLap ρ v a t x| *
          |Real.log (ouDensity ρ v a t x / heatDensityPi v x) + 1|
        ≤ a * (genA d S₀ v * K * ((∫ y, ell y * heatDensityPi (2 * v) (x - scalePi cp y) ∂ρ) +
            ∫ ω, ell ω.1 * tubeK (2 * v) x ω.1 ω.2 ∂ν)) * ((L + 1) * (1 + ∑ i, x i ^ 2)) := by
          gcongr
      _ = _ := by ring
  · -- `p vᵢ`
    rw [eflux i]
    exact integrable_of_le_ouQ ρ hmom4 hv ha ht₀.le (by fun_prop) (by positivity) hK
      (by norm_num) (hfluxb i)
  · -- `∂ᵢ(p vᵢ)`
    rw [edflux i]
    have := hHc i
    exact integrable_of_le_ouQ ρ hmom4 hv ha ht₀.le (by fun_prop) (by positivity) hK
      (by norm_num) (hdfluxb i)
  · -- `∂ᵢ(p vᵢ) log(p/π)`
    have e : (fun x => partialDeriv i (fun y => ouDensity ρ v a t₀ y * ouVelocity ρ v a t₀ y i) x *
        Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)) =
        fun x => -a * (ouDensity ρ v a t₀ x + x i * ouGrad ρ v a t₀ x i +
          v * heatFlowHessPi (ouLaw ρ a t₀) (ouS v a t₀) x i i) *
          Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x) :=
      funext fun x => by rw [partialDeriv_ouFlux ρ hv ha ht₀ i x]
    rw [e]
    have := hHc i
    exact integrable_of_le_ouQ ρ hmom4 hv ha ht₀.le (by fun_prop) (by positivity) hK
      (by norm_num) (fun x => abs_mul_log_aux (hdfluxb i x) (hlog x))
  · -- `p vᵢ log(p/π)`
    have e : (fun x => ouDensity ρ v a t₀ x * ouVelocity ρ v a t₀ x i *
        Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)) =
        fun x => -a * (x i * ouDensity ρ v a t₀ x + v * ouGrad ρ v a t₀ x i) *
          Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x) :=
      funext fun x => by rw [ouDensity_mul_ouVelocity ρ hv ha ht₀ x i]
    rw [e]
    exact integrable_of_le_ouQ ρ hmom4 hv ha ht₀.le (by fun_prop) (by positivity) hK
      (by norm_num) (fun x => abs_mul_log_aux (hfluxb i x) (hlog x))
  · -- `vᵢ (∇log p - ∇log π)ᵢ p`
    have e : (fun x => ouVelocity ρ v a t₀ x i *
        (score (ouDensity ρ v a t₀) x i - score (heatDensityPi v) x i) * ouDensity ρ v a t₀ x) =
        fun x => -(a * v) * (ouDensity ρ v a t₀ x *
          (ouGrad ρ v a t₀ x i / ouDensity ρ v a t₀ x + x i / v) ^ 2) := by
      funext x
      have hpx := (ouDensity_pos ρ hv ha ht₀ x).ne'
      rw [ouVelocity_apply ρ hv ha ht₀, score_ouDensity ρ hv ha ht₀, score_heatDensityPi hv]
      field_simp
      ring
    rw [e]
    have hfis := integrable_ouFisher ρ hv ha ht₀ hmom
    have hcont : Continuous fun x => -(a * v) * (ouDensity ρ v a t₀ x *
        (ouGrad ρ v a t₀ x i / ouDensity ρ v a t₀ x + x i / v) ^ 2) :=
      continuous_const.mul (hpc.mul ((((hGc i).div hpc fun x =>
        (ouDensity_pos ρ hv ha ht₀ x).ne').add ((continuous_apply i).div_const v)).pow 2))
    refine (hfis.const_mul (a * v)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hpx := (ouDensity_pos ρ hv ha ht₀ x).le
    have hsum : (ouGrad ρ v a t₀ x i / ouDensity ρ v a t₀ x + x i / v) ^ 2 ≤
        ∑ j, (ouGrad ρ v a t₀ x j / ouDensity ρ v a t₀ x + x j / v) ^ 2 :=
      Finset.single_le_sum (f := fun j => (ouGrad ρ v a t₀ x j / ouDensity ρ v a t₀ x +
        x j / v) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity),
      abs_of_nonneg (mul_nonneg hpx (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hpx) (by positivity)

open FormalizeSampling.KLDecay FormalizeSampling.LogSobolevAlongGaussian in
/-- **PFG FL-2/FL-4 (`KLDissipation.klDecay_of_idealVelocity_local`) on the OU probability
flow under a fourth moment (Verified, every hypothesis discharged).** Let `ρ` be a probability
law on `Fin d → ℝ` with `∫ |y|⁴ dρ(y) < ∞` (`hmom4`), `v, a > 0` and `s > 0`. For the shifted
flow `t ↦ p_{s+t}` (defined for `t > -s`) with velocity `t ↦ v_{s+t}`, target density `φ_v` of
`N(0, v I)` and `H = (a v)⁻¹ I`: for every `t ≥ 0`,
`d/dt klDivDensity(p_{s+t}, φ_v) = -∫ ‖∇log p_{s+t} - ∇log φ_v‖²_{H⁻¹} p_{s+t}` and
`klDivDensity(p_{s+t}, φ_v) ≤ e^{-2at} klDivDensity(p_s, φ_v)`. The hypotheses `hce`, `hreg`
(`TransportKLRegularity`, from `transportKLRegularity_ou_moment`), `hdiss` and `hLSI` of the
PFG theorem are all proved here. -/
theorem klDecay_of_idealVelocity_local_ou_moment
    (hmom4 : Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ) (hv : 0 < v) (ha : 0 < a) {s : ℝ}
    (hs : 0 < s) :
    (∀ t, 0 ≤ t → HasDerivAt (fun t => klDivDensity (ouDensity ρ v a (s + t)) (heatDensityPi v))
        (-∫ x, sqNormH (ouPrecond d v a)⁻¹ (score (ouDensity ρ v a (s + t)) x -
          score (heatDensityPi v) x) * ouDensity ρ v a (s + t) x) t) ∧
    ∀ t, 0 ≤ t → klDivDensity (ouDensity ρ v a (s + t)) (heatDensityPi v) ≤
      Real.exp (-2 * a * t) * klDivDensity (ouDensity ρ v a s) (heatDensityPi v) := by
  have hmom := integrable_sum_sq_of_moment4 ρ hmom4
  have hpos : ∀ t, -s < t → ∀ x, 0 < ouDensity ρ v a (s + t) x := fun t ht x =>
    ouDensity_pos ρ hv ha (by linarith) x
  have hce : ∀ t, -s < t → ∀ x, HasDerivAt (fun r => ouDensity ρ v a (s + r) x)
      (-(divergence (fun y => ouDensity ρ v a (s + t) y • ouVelocity ρ v a (s + t) y) x)) t := by
    intro t ht x
    have h := (hasDerivAt_ouDensity_continuity ρ hv ha hmom (by linarith : 0 < s + t) x).comp t
      ((hasDerivAt_id' t).const_add s)
    rw [mul_one] at h
    exact h
  have hg : ∀ t, 0 ≤ t → ouVelocity ρ v a (s + t) = idealVelocity (ouPrecond d v a)
      (score (ouDensity ρ v a (s + t))) (score (heatDensityPi v)) := fun t _ =>
    ouVelocity_eq_idealVelocity ρ hv ha
  have hreg : ∀ t, 0 ≤ t → KLDissipation.TransportKLRegularity
      (fun t => ouDensity ρ v a (s + t)) (heatDensityPi v) (fun t => ouVelocity ρ v a (s + t)) t :=
    fun t ht => transportKLRegularity_shift
      (transportKLRegularity_ou_moment ρ hmom4 hv ha (by linarith))
  have hdiss : ∀ t, 0 ≤ t → Integrable (fun x => sqNormH (ouPrecond d v a)⁻¹
      (score (ouDensity ρ v a (s + t)) x - score (heatDensityPi v) x) *
        ouDensity ρ v a (s + t) x) := by
    intro t ht
    have hst : 0 < s + t := by linarith
    refine ((integrable_ouFisher ρ hv ha hst hmom).const_mul (a * v)).congr
      (Eventually.of_forall fun x => ?_)
    have hpx := (ouDensity_pos ρ hv ha hst x).ne'
    simp only [ouPrecond_inv hv ha, sqNormH, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, score_ouDensity ρ hv ha hst,
      score_heatDensityPi hv]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hLSI : LogSobolevAlong (1 / v) (fun t => densityMeasure (ouDensity ρ v a (s + t)))
      (fun t => score (ouDensity ρ v a (s + t))) (score (heatDensityPi v))
      (fun t => klDivDensity (ouDensity ρ v a (s + t)) (heatDensityPi v)) := by
    intro t ht
    have hst : 0 < s + t := by linarith
    have h := logSobolevAlong_gaussian_score hv
      (p := fun t => ouDensity ρ v a (s + t)) (gp := fun t => ouGrad ρ v a (s + t))
      (fun t ht => gaussianDensityHyp_ouDensity ρ hv ha (by linarith) hmom) t ht
    rw [score_heatDensityPi_eq_gaussScore hv]
    simp only at h ⊢
    rw [← (gaussKL_eq_klDivDensity ρ hv ha hst hmom).1]
    exact h
  have hm : 0 < (a * v)⁻¹ := by positivity
  obtain ⟨hD, hK⟩ := KLDissipation.klDecay_of_idealVelocity_local (ouPrecond_posDef hv ha) hm
    (fun u => (sqNormH_ouPrecond u).le) (by positivity : (0 : ℝ) < 1 / v) hs
    (p := fun t => ouDensity ρ v a (s + t)) (pStar := heatDensityPi v)
    (g := fun t => ouVelocity ρ v a (s + t)) hpos (heatDensityPi_pos hv)
    (fun x => (hasFDerivAt_heatDensityPi v x).differentiableAt) hce hg hreg hdiss hLSI
  refine ⟨hD, fun t ht => ?_⟩
  have h := hK t ht
  have e : -2 * (1 / v) * t / (a * v)⁻¹ = -2 * a * t := by field_simp
  rw [e, add_zero] at h
  exact h

/-- **Bounded support implies the fourth moment.** If `|y|² ≤ R²` for `ρ`-a.e. `y`, then
`∫ |y|⁴ dρ < ∞`; so `transportKLRegularity_ou_moment` covers the bounded-support case
`ProbabilityFlowOU.transportKLRegularity_ou`. -/
theorem integrable_moment4_of_bounded {R : ℝ} (hR : ∀ᵐ y ∂ρ, ∑ i, y i ^ 2 ≤ R ^ 2) :
    Integrable (fun y => (∑ i, y i ^ 2) ^ 2) ρ :=
  Integrable.of_bound (by fun_prop : Continuous fun y : Fin d → ℝ =>
    (∑ i, y i ^ 2) ^ 2).aestronglyMeasurable ((R ^ 2) ^ 2) (by
    filter_upwards [hR] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (sum_sq_nonneg y) hy 2)

/-- **`TransportKLRegularity` along the OU probability flow, bounded support (Verified).** Let
`ρ` be a probability law on `Fin d → ℝ` supported in the ball `|y|² ≤ R²` (a.e.), `v, a > 0`.
Then for every `t₀ > 0` the explicit FL-1 (II) regularity
`KLDissipation.TransportKLRegularity p π vel t₀` holds for the OU marginal densities
`p = ouDensity ρ v a`, the target density `π = heatDensityPi v` of `N(0, v I)` and the ideal
velocity `vel = ouVelocity ρ v a`. The case `integrable_moment4_of_bounded` of
`transportKLRegularity_ou_moment`. -/
theorem _root_.FormalizeSampling.ProbabilityFlowOU.transportKLRegularity_ou {R : ℝ}
    (hR : ∀ᵐ y ∂ρ, ∑ i, y i ^ 2 ≤ R ^ 2) (hv : 0 < v) (ha : 0 < a) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a)
      t₀ :=
  transportKLRegularity_ou_moment ρ (integrable_moment4_of_bounded ρ hR) hv ha ht₀

end Flow

end FormalizeSampling.ProbabilityFlowOUMoment
