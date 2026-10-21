module

public import FormalizeSampling.Flow.ProbabilityFlowOUMoment

/-!
# The OU probability flow: the fixed-time regularity under a third moment

Registry IDs: **FL-1 (II)**, **FL-2** (sharpening of `Flow/ProbabilityFlowOUMoment.lean`).

Status: **Verified**. Setting and notation as in `ProbabilityFlowOU` and
`ProbabilityFlowOUMoment`: `ρ` a probability law on `Fin d → ℝ`, target `π = N(0, v I)` with
density `φ_v`, OU marginals `p_t(x) = ∫ φ_{s_t}(x - c_t y) dρ(y)`, ideal velocity `ouVelocity`.
The moment hypothesis is `hmom3 : Integrable (fun y => ‖y‖ ^ 3) ρ` (`‖·‖` the sup norm of
`Fin d → ℝ`, equivalent to the Euclidean norm up to a factor `√d`).

## Method

`KLDissipation.TransportKLRegularity` has one time-uniform field (`domination`, a bound on
`sup_{|t - t₀| < ε} |div(p_t v_t)| |log(p_t/π) + 1|`) and eight fixed-time fields. The fixed-time
integrands are bounded by `C W(x) q(x)` with the cubic weight `W(x) = (1 + |x|²) ℓ(x)`,
`ℓ(x) = 1 + ∑ |xᵢ|`, instead of the quartic `(1 + |x|²)²` of `ProbabilityFlowOUMoment`: in
`∂ᵢ(p vᵢ) = -a (p + xᵢ ∂ᵢp + v ∂ᵢ²p)` and `p vᵢ = -a (xᵢ p + v ∂ᵢp)` the factor `xᵢ` costs only
`ℓ(x)`, and the log-ratio costs `1 + |x|²` (`abs_log_ouDensity_div_le_moment`). Since
`W(x) ≤ 2 W(x - w) W(w)`, the weighted Tonelli lemma `integrable_integral_kernel_weight`
moves `W` onto `ρ`, where it is integrable under a third moment.

## Main results

* `integrable_integral_kernel_weight`: Tonelli for moving kernels with a general submultiplicative
  weight (the fixed-power `ProbabilityFlowOUMoment.integrable_integral_kernel` is a special case).
* `integrable_of_le_ouQ_weight`: a continuous `f` with `|f| ≤ C W K q_t` is Lebesgue integrable
  whenever the weight `W` is submultiplicative, `W φ_{2v}` is integrable and `W(c_t ·)` is
  `ρ`-integrable. Instances: `integrable_of_le_ouQ_cubic` (third moment, `W = (1 + |x|²) ℓ`) and
  `integrable_of_le_ouQ_sq` (second moment, `W = 1 + |x|²`).
* `OUDomination ρ v a t₀`: the `domination` field of `TransportKLRegularity` for the OU flow.
* `transportKLRegularity_ou_of_domination`: under a third moment, `OUDomination ρ v a t₀`
  implies `TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a) t₀`;
  `transportKLRegularity_ou_iff_domination` is the equivalence. So under a third moment every
  fixed-time field holds and the regularity is exactly the time-uniform domination.
* `integrable_ouGrad_mul_log`: under a second moment, `∂ᵢp_t log(p_t/π)` is integrable (used by
  the counterexample of `ProbabilityFlowOUCounterexample`).

## Sharpness (see `ProbabilityFlowOUCounterexample`)

* The third moment is the right threshold for the fixed-time fields: for the law with atoms at
  `2^k` and weights `∝ 8^{-k}` (moments of every order `< 3`, infinite third moment), the field
  `integrable_flux_log` fails at every `t₀ > 0`.
* The domination field genuinely needs the fourth moment: for atoms at `2^k` with weights
  `∝ 16^{-k}` (finite third moment, moments of every order `< 4`, infinite fourth moment),
  `OUDomination` fails at every `t₀ > 0`, so `TransportKLRegularity` fails although all its
  fixed-time fields hold. The fourth-moment theorem
  `ProbabilityFlowOUMoment.transportKLRegularity_ou_moment` is therefore sharp on the scale of
  polynomial moments.

## Not proved here

* **No third-moment `TransportKLRegularity`.** It is false in general (see above); the decay
  `klDecay_of_idealVelocity_local_ou_moment` is therefore not extended to a third moment along
  this route. A finer, non-polynomial characterisation of the domination field (it behaves like
  `∑ₖ wₖ |yₖ|⁴` for well-separated atoms) is not formalised.
* Only `t₀ > 0`, the isotropic Gaussian target and the OU flow, as in `ProbabilityFlowOU`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProbabilityFlowOUThirdMoment

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi FormalizeSampling.ProbabilityFlowOU
  FormalizeSampling.ProbabilityFlowOUMoment
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi)

variable {d : ℕ}

/-! ### Tonelli with a general weight -/

/-- **Integrability of a kernel average with a general weight.** Let `ν` be s-finite on `Ω`,
`m : Ω → ℝ^d` measurable, `R ω z ≥ 0` jointly measurable with `R ω z ≤ P ω Q z`, and `W`
measurable with `0 ≤ W x ≤ U(x - w) V(w)` for all `x, w`. If `U Q` is Lebesgue integrable and
`V(m ω) P ω` is `ν`-integrable, then `x ↦ ∫ W(x) R ω (x - m ω) dν(ω)` is Lebesgue integrable. -/
theorem integrable_integral_kernel_weight {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [SFinite ν] {W U V : (Fin d → ℝ) → ℝ} (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWUV : ∀ x w, W x ≤ U (x - w) * V w) {m : Ω → Fin d → ℝ} (hm : Measurable m)
    {R : Ω → (Fin d → ℝ) → ℝ} (hR : Measurable fun q : Ω × (Fin d → ℝ) => R q.1 q.2)
    (hR0 : ∀ ω z, 0 ≤ R ω z) {P : Ω → ℝ} {Q : (Fin d → ℝ) → ℝ}
    (hRle : ∀ ω z, R ω z ≤ P ω * Q z) (hQ : Integrable fun z => U z * Q z)
    (hPm : Integrable (fun ω => V (m ω) * P ω) ν) :
    Integrable fun x : Fin d → ℝ => ∫ ω, W x * R ω (x - m ω) ∂ν := by
  set F : (Fin d → ℝ) × Ω → ℝ := fun q => W q.1 * R q.2 (q.1 - m q.2)
  have hFm : Measurable F :=
    (hWm.comp measurable_fst).mul (hR.comp (measurable_snd.prodMk
      (measurable_fst.sub (hm.comp measurable_snd))))
  have hF0 : ∀ q, 0 ≤ F q := fun q => mul_nonneg (hW0 _) (hR0 _ _)
  have key : ∀ ω x, F (x, ω) ≤ (V (m ω) * P ω) * (U (x - m ω) * Q (x - m ω)) := by
    intro ω x
    have hR' := hRle ω (x - m ω)
    have hPQ : 0 ≤ P ω * Q (x - m ω) := (hR0 _ _).trans hR'
    calc F (x, ω) ≤ (U (x - m ω) * V (m ω)) * (P ω * Q (x - m ω)) :=
          mul_le_mul (hWUV x (m ω)) hR' (hR0 _ _) ((hW0 x).trans (hWUV x (m ω)))
      _ = _ := by ring
  have hint : ∀ ω, Integrable (fun x => F (x, ω)) := by
    intro ω
    refine ((hQ.comp_sub_right (m ω)).const_mul (V (m ω) * P ω)).mono'
      (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hF0 _)]
    exact key ω x
  have hF : Integrable F ((volume : Measure (Fin d → ℝ)).prod ν) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hint, ?_⟩
    refine (hPm.mul_const (∫ z, U z * Q z)).mono'
      (hFm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have e : (fun x => ‖F (x, ω)‖) = fun x => F (x, ω) :=
      funext fun x => Real.norm_of_nonneg (hF0 _)
    rw [e, Real.norm_of_nonneg (integral_nonneg fun x => hF0 _)]
    calc ∫ x, F (x, ω) ≤ ∫ x, (V (m ω) * P ω) * (U (x - m ω) * Q (x - m ω)) :=
          integral_mono (hint ω) ((hQ.comp_sub_right (m ω)).const_mul _) (key ω)
      _ = _ := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun z => U z * Q z) (m ω)]
  exact hF.integral_prod_left

/-! ### Weights -/

/-- The cubic weight `W(x) = (1 + |x|²) ℓ(x)`, `ℓ(x) = 1 + ∑ |xᵢ|`. -/
noncomputable def cubW (x : Fin d → ℝ) : ℝ := (1 + ∑ i, x i ^ 2) * ell x

/-- `W ≥ 1`. -/
theorem one_le_cubW (x : Fin d → ℝ) : 1 ≤ cubW x := by
  unfold cubW
  have h1 := one_le_ell x
  have h2 := sum_sq_nonneg x
  nlinarith

/-- `W` is continuous. -/
theorem continuous_cubW : Continuous (cubW (d := d)) := by
  unfold cubW ell; fun_prop

/-- `ℓ` is subadditive up to the constant: `ℓ(x) ≤ ℓ(x - w) ℓ(w)`. -/
theorem ell_le_mul (x w : Fin d → ℝ) : ell x ≤ ell (x - w) * ell w := by
  have h1 : ell x ≤ ell (x - w) + ell w - 1 := by
    unfold ell
    have : ∑ i, |x i| ≤ ∑ i, |(x - w) i| + ∑ i, |w i| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := abs_add_le ((x - w) i) (w i)
      simpa using this
    linarith
  have h2 := one_le_ell (x - w)
  have h3 := one_le_ell w
  nlinarith

/-- `W(x) ≤ 2 W(x - w) W(w)`. -/
theorem cubW_le_mul (x w : Fin d → ℝ) : cubW x ≤ 2 * cubW (x - w) * cubW w := by
  unfold cubW
  have h1 := one_add_sum_sq_le x w
  have h2 := ell_le_mul x w
  have h3 := one_le_ell x
  have hx := sum_sq_nonneg x
  calc (1 + ∑ i, x i ^ 2) * ell x ≤ (2 * (1 + ∑ i, (x - w) i ^ 2) * (1 + ∑ i, w i ^ 2)) *
        (ell (x - w) * ell w) := mul_le_mul h1 h2 (by linarith) (by
          have := sum_sq_nonneg (x - w); have := sum_sq_nonneg w; positivity)
    _ = _ := by ring

/-- `W(c y) ≤ W(y)` for `c² ≤ 1`. -/
theorem cubW_scalePi_le {c : ℝ} (hc : c ^ 2 ≤ 1) (y : Fin d → ℝ) :
    cubW (scalePi c y) ≤ cubW y := by
  unfold cubW
  have h1 := one_add_sum_sq_scalePi_le_of_sq_le hc y
  have h2 : ell (scalePi c y) ≤ ell y := by
    unfold ell
    have hc' : |c| ≤ 1 := by
      rw [← abs_one, ← sq_le_sq]; simpa using hc
    have : ∑ i, |scalePi c y i| ≤ ∑ i, |y i| := Finset.sum_le_sum fun i _ => by
      simp only [scalePi, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hc'
    linarith
  have := one_le_ell (scalePi c y)
  have := sum_sq_nonneg (scalePi c y)
  exact mul_le_mul h1 h2 (by linarith) (by linarith [sum_sq_nonneg y])

/-- `W φ_{2v}` is Lebesgue integrable (`W ≤ 2 (1 + d) (1 + |x|²)²`). -/
theorem integrable_cubW_mul_heatDensityPi {v : ℝ} (hv : 0 < v) :
    Integrable fun z : Fin d → ℝ => cubW z * heatDensityPi (2 * v) z := by
  refine ((integrable_pow_mul_heatDensityPi (d := d) (k := 2) hv (by norm_num)).const_mul
    (2 * (1 + d))).mono' ?_ (Eventually.of_forall fun z => ?_)
  · have := continuous_heatDensityPi (d := d) (2 * v)
    exact (continuous_cubW.mul this).aestronglyMeasurable
  · have hφ := (heatDensityPi_pos (by positivity : 0 < 2 * v) z).le
    have hW := one_le_cubW z
    rw [Real.norm_of_nonneg (by positivity)]
    have h3 := ell_sq_le z
    have h4 := one_le_ell z
    have h5 := sum_sq_nonneg z
    have hell : ell z ≤ 2 * (1 + d) * (1 + ∑ i, z i ^ 2) := by nlinarith
    have : cubW z ≤ 2 * (1 + d) * (1 + ∑ i, z i ^ 2) ^ 2 := by
      unfold cubW
      calc (1 + ∑ i, z i ^ 2) * ell z ≤ (1 + ∑ i, z i ^ 2) * (2 * (1 + d) * (1 + ∑ i, z i ^ 2)) :=
            mul_le_mul_of_nonneg_left hell (by linarith)
        _ = _ := by ring
    calc cubW z * heatDensityPi (2 * v) z ≤ 2 * (1 + d) * (1 + ∑ i, z i ^ 2) ^ 2 *
          heatDensityPi (2 * v) z := mul_le_mul_of_nonneg_right this hφ
      _ = _ := by ring

/-- `(1 + |x|²) φ_{2v}` is Lebesgue integrable. -/
theorem integrable_sq_weight_mul_heatDensityPi {v : ℝ} (hv : 0 < v) :
    Integrable fun z : Fin d → ℝ => (1 + ∑ i, z i ^ 2) * heatDensityPi (2 * v) z :=
  (integrable_pow_mul_heatDensityPi (d := d) (k := 1) hv (by norm_num)).congr
    (Eventually.of_forall fun z => by simp)

/-! ### Moments -/

section Moments

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ]

/-- `|yᵢ| ≤ ‖y‖` (sup norm). -/
theorem abs_le_norm (y : Fin d → ℝ) (i : Fin d) : |y i| ≤ ‖y‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y i

/-- A third moment gives a second moment. -/
theorem integrable_sum_sq_of_moment3 (hmom3 : Integrable (fun y => ‖y‖ ^ 3) ρ) :
    Integrable (fun y => ∑ i, y i ^ 2) ρ := by
  refine ((integrable_const (d : ℝ)).add (hmom3.const_mul d)).mono'
    (by fun_prop : Continuous fun y : Fin d → ℝ => ∑ i, y i ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (sum_sq_nonneg y)]
  have hn := norm_nonneg y
  have h : ∑ i, y i ^ 2 ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_norm y i) 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : ‖y‖ ^ 2 ≤ 1 + ‖y‖ ^ 3 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  change _ ≤ (d : ℝ) + d * ‖y‖ ^ 3
  nlinarith

/-- A third moment gives `W` integrable: `W(y) ≤ 3 (1 + d)² (1 + ‖y‖³)`. -/
theorem integrable_cubW (hmom3 : Integrable (fun y => ‖y‖ ^ 3) ρ) : Integrable cubW ρ := by
  refine ((integrable_const (1 : ℝ)).add hmom3).const_mul (3 * (1 + d) ^ 2) |>.mono'
    continuous_cubW.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by linarith [one_le_cubW y])]
  set u := ‖y‖
  have hu : 0 ≤ u := norm_nonneg y
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : ∑ i, y i ^ 2 ≤ d * u ^ 2 := by
    have h : ∑ i, y i ^ 2 ≤ ∑ _i : Fin d, u ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_norm y i) 2
    simpa using h
  have hl : ell y ≤ 1 + d * u := by
    unfold ell
    have h : ∑ i, |y i| ≤ ∑ _i : Fin d, u := Finset.sum_le_sum fun i _ => abs_le_norm y i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    linarith
  have h1 : 1 + ∑ i, y i ^ 2 ≤ (1 + d) * (1 + u ^ 2) := by nlinarith
  have h2 : ell y ≤ (1 + d) * (1 + u) := by nlinarith
  have h3 : (1 + u ^ 2) * (1 + u) ≤ 3 * (1 + u ^ 3) := by
    nlinarith [sq_nonneg (u - 1), mul_nonneg hu (sq_nonneg (u - 1))]
  have h0 : 0 ≤ 1 + ∑ i, y i ^ 2 := by linarith [sum_sq_nonneg y]
  change (1 + ∑ i, y i ^ 2) * ell y ≤ 3 * (1 + d) ^ 2 * (1 + u ^ 3)
  calc (1 + ∑ i, y i ^ 2) * ell y ≤ ((1 + d) * (1 + u ^ 2)) * ((1 + d) * (1 + u)) :=
        mul_le_mul h1 h2 (by linarith [one_le_ell y]) (by positivity)
    _ = (1 + d) ^ 2 * ((1 + u ^ 2) * (1 + u)) := by ring
    _ ≤ (1 + d) ^ 2 * (3 * (1 + u ^ 3)) := by gcongr
    _ = _ := by ring

end Moments

/-! ### Fixed-time integrability with a general weight -/

section Fixed

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a t : ℝ}

/-- **Fixed-time integrability with a weight.** Let `W ≥ 0` be continuous with
`W(x) ≤ B W(x - w) W(w)`, `W φ_{2v}` Lebesgue integrable and `W(c_t ·)` `ρ`-integrable. If `f`
is continuous with `|f(x)| ≤ C W(x) K q_t(x)`, then `f` is Lebesgue integrable. -/
theorem integrable_of_le_ouQ_weight {W : (Fin d → ℝ) → ℝ} (hWc : Continuous W)
    (hW0 : ∀ x, 0 ≤ W x) {B : ℝ} (hWB : ∀ x w, W x ≤ B * W (x - w) * W w)
    (hWφ : Integrable fun z => W z * heatDensityPi (2 * v) z)
    (hWρ : Integrable (fun y => W (scalePi (ouC a t) y)) ρ) (hv : 0 < v)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {C K : ℝ}
    (h : ∀ x, |f x| ≤ C * W x * (K * ouQ ρ v a t x)) : Integrable f := by
  have hv2 : 0 < 2 * v := by positivity
  have hPm : Integrable (fun w : Fin d → ℝ => W (id w) * 1) (ouLaw ρ a t) := by
    have hc : Continuous fun w : Fin d → ℝ => W (id w) * 1 := by simpa using hWc
    rw [ouLaw, integrable_map_measure hc.aestronglyMeasurable
      (measurable_scalePi _).aemeasurable]
    exact hWρ.congr (Eventually.of_forall fun y => by simp)
  have hI := integrable_integral_kernel_weight (ν := ouLaw ρ a t) hWc.measurable hW0
    (U := fun z => B * W z) (V := W) (fun x w => hWB x w)
    measurable_id (R := fun _ z => heatDensityPi (2 * v) z)
    ((continuous_heatDensityPi _).measurable.comp measurable_snd)
    (fun _ z => (heatDensityPi_pos hv2 z).le) (P := fun _ => 1) (Q := heatDensityPi (2 * v))
    (fun _ z => by simp) ((hWφ.const_mul B).congr (Eventually.of_forall fun z => by
      simp only; ring)) hPm
  refine (hI.const_mul (C * K)).mono' hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (h x).trans (le_of_eq ?_)
  have e : ∫ w, W x * heatDensityPi (2 * v) (x - id w) ∂(ouLaw ρ a t) = W x * ouQ ρ v a t x := by
    rw [integral_const_mul]; rfl
  rw [e]; ring

/-- **Fixed-time integrability, cubic weight (third moment).** If `∫ ‖y‖³ dρ < ∞`, `t ≥ 0`, `f`
is continuous and `|f(x)| ≤ C (1 + |x|²) ℓ(x) K q_t(x)`, then `f` is Lebesgue integrable. -/
theorem integrable_of_le_ouQ_cubic (hmom3 : Integrable (fun y => ‖y‖ ^ 3) ρ) (hv : 0 < v)
    (ha : 0 < a) (ht : 0 ≤ t) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {C K : ℝ}
    (h : ∀ x, |f x| ≤ C * cubW x * (K * ouQ ρ v a t x)) :
    Integrable f := by
  refine integrable_of_le_ouQ_weight ρ continuous_cubW (fun x => by linarith [one_le_cubW x])
    cubW_le_mul (integrable_cubW_mul_heatDensityPi hv) ?_ hv hf h
  refine (integrable_cubW ρ hmom3).mono' (continuous_cubW.comp
    (by unfold scalePi; fun_prop : Continuous fun y : Fin d → ℝ => scalePi (ouC a t) y)
    |>.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by linarith [one_le_cubW (scalePi (ouC a t) y)])]
  exact cubW_scalePi_le (ouC_sq_le_one ha.le ht) y

/-- **Fixed-time integrability, quadratic weight (second moment).** If `∫ |y|² dρ < ∞`, `t ≥ 0`,
`f` is continuous and `|f(x)| ≤ C (1 + |x|²) K q_t(x)`, then `f` is Lebesgue integrable. -/
theorem integrable_of_le_ouQ_sq (hmom : Integrable (fun y => ∑ i, y i ^ 2) ρ) (hv : 0 < v)
    (ha : 0 < a) (ht : 0 ≤ t) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {C K : ℝ}
    (h : ∀ x, |f x| ≤ C * (1 + ∑ i, x i ^ 2) * (K * ouQ ρ v a t x)) : Integrable f := by
  refine integrable_of_le_ouQ_weight ρ (W := fun x => 1 + ∑ i, x i ^ 2) (by fun_prop)
    (fun x => by linarith [sum_sq_nonneg x]) one_add_sum_sq_le
    (integrable_sq_weight_mul_heatDensityPi hv) ?_ hv hf h
  refine ((integrable_const (1 : ℝ)).add hmom).mono' (by unfold scalePi; fun_prop :
    Continuous fun y : Fin d → ℝ => 1 + ∑ i, scalePi (ouC a t) y i ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by linarith [sum_sq_nonneg (scalePi (ouC a t) y)])]
  exact one_add_sum_sq_scalePi_le_of_sq_le (ouC_sq_le_one ha.le ht) y

/-- **`∂ᵢp_t log(p_t/π)` is integrable under a second moment** (`t > 0`): `|∂ᵢp_t| ≤ A₁ K q_t`
and `|log(p_t/π)| ≤ L (1 + |x|²)`. -/
theorem integrable_ouGrad_mul_log (hmom : Integrable (fun y => ∑ i, y i ^ 2) ρ) (hv : 0 < v)
    (ha : 0 < a) (ht : 0 < t) (i : Fin d) :
    Integrable fun x =>
      ouGrad ρ v a t x i * Real.log (ouDensity ρ v a t x / heatDensityPi v x) := by
  set S₀ := ouS v a t
  have hS₀ : 0 < S₀ := ouS_pos hv ha ht
  have hK := envK_nonneg (d := d) hS₀ hv
  have hL := logLM_nonneg ρ hS₀ hv
  have hpc := continuous_ouDensity ρ hv ha ht
  have hlc : Continuous fun x => Real.log (ouDensity ρ v a t x / heatDensityPi v x) :=
    (hpc.div (continuous_heatDensityPi v) fun x => (heatDensityPi_pos hv x).ne').log
      fun x => (div_pos (ouDensity_pos ρ hv ha ht x) (heatDensityPi_pos hv x)).ne'
  refine integrable_of_le_ouQ_sq ρ hmom hv ha ht.le ((continuous_ouGrad ρ hv ha ht i).mul hlc)
    (C := 1 / S₀ * logLM ρ d S₀ v) (K := envK d S₀ v) (fun x => ?_)
  have hG := abs_ouGrad_le_ouQ ρ hv hS₀ le_rfl x i
  have hl := abs_log_ouDensity_div_le_moment ρ hmom hv ha ht hS₀ le_rfl x
  rw [abs_mul]
  have hq := mul_nonneg hK (ouQ_nonneg (a := a) (t := t) ρ hv x)
  calc |ouGrad ρ v a t x i| * |Real.log (ouDensity ρ v a t x / heatDensityPi v x)|
      ≤ (1 / S₀ * (envK d S₀ v * ouQ ρ v a t x)) * (logLM ρ d S₀ v * (1 + ∑ i, x i ^ 2)) :=
        mul_le_mul hG hl (abs_nonneg _) (by positivity)
    _ = _ := by ring

end Fixed

/-! ### `TransportKLRegularity` = domination, under a third moment -/

section Regularity

variable (ρ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ] {v a : ℝ}

/-- The `domination` field of `KLDissipation.TransportKLRegularity` for the OU flow at `t₀`:
some `ε > 0` and a Lebesgue-integrable `bound` with
`|div(p_t v_t)(x)| |log(p_t(x)/φ_v(x)) + 1| ≤ bound(x)` for a.e. `x` and all `|t - t₀| < ε`, plus
measurability of `p_t` there. -/
def OUDomination (ρ : Measure (Fin d → ℝ)) (v a t₀ : ℝ) : Prop :=
  ∃ ε > 0, ∃ bound : (Fin d → ℝ) → ℝ,
    (∀ t ∈ Metric.ball t₀ ε, AEStronglyMeasurable (ouDensity ρ v a t)) ∧
    (∀ᵐ x, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => ouDensity ρ v a t y • ouVelocity ρ v a t y) x) *
        (Real.log (ouDensity ρ v a t x / heatDensityPi v x) + 1)‖ ≤ bound x) ∧
    Integrable bound

/-- Scalar step: a bound `C ℓ P` times a log bound `L (1 + |x|²)` is `C L W P`. -/
theorem abs_mul_log_cubW_le {f g C P L : ℝ} {x : Fin d → ℝ} (hf : |f| ≤ C * ell x * P)
    (hg : |g| ≤ L * (1 + ∑ i, x i ^ 2)) : |f * g| ≤ C * L * cubW x * P := by
  rw [abs_mul]
  have h0 : 0 ≤ C * ell x * P := (abs_nonneg _).trans hf
  calc |f| * |g| ≤ (C * ell x * P) * (L * (1 + ∑ i, x i ^ 2)) :=
        mul_le_mul hf hg (abs_nonneg _) h0
    _ = C * L * cubW x * P := by unfold cubW; ring

/-- Scalar step: `C ℓ P ≤ C W P` for `C P ≥ 0`. -/
theorem ell_mul_le_cubW {C P : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (x : Fin d → ℝ) :
    C * ell x * P ≤ C * cubW x * P := by
  have : ell x ≤ cubW x := by
    unfold cubW
    exact le_mul_of_one_le_left (by linarith [one_le_ell x]) (by linarith [sum_sq_nonneg x])
  gcongr

/-- `|xᵢ| ≤ ℓ(x)`. -/
theorem abs_le_ell (x : Fin d → ℝ) (i : Fin d) : |x i| ≤ ell x := by
  unfold ell
  have := Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  linarith

/-- **The fixed-time fields under a third moment (Verified).** Let `ρ` be a probability law on
`Fin d → ℝ` with `∫ ‖y‖³ dρ(y) < ∞` (sup norm on `Fin d → ℝ`; equivalent to the Euclidean
third moment), `v, a > 0`, `t₀ > 0`. If the time-uniform domination
`OUDomination ρ v a t₀` holds, then
`KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a) t₀`:
every other (fixed-time) field is proved here, with the cubic weight `(1 + |x|²) ℓ(x)`. -/
theorem transportKLRegularity_ou_of_domination (hmom3 : Integrable (fun y => ‖y‖ ^ 3) ρ)
    (hv : 0 < v) (ha : 0 < a) {t₀ : ℝ} (ht₀ : 0 < t₀) (hdom : OUDomination ρ v a t₀) :
    KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a)
      t₀ := by
  have hmom := integrable_sum_sq_of_moment3 ρ hmom3
  set S₀ := ouS v a t₀
  have hS₀ : 0 < S₀ := ouS_pos hv ha ht₀
  set K := envK d S₀ v
  have hK : 0 ≤ K := envK_nonneg hS₀ hv
  set L := logLM ρ d S₀ v
  have hL : 0 ≤ L := logLM_nonneg ρ hS₀ hv
  set A₁ := 1 / S₀
  set A₂ := 1 / S₀ ^ 2 + 1 / S₀
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  have hP : ∀ x, 0 ≤ K * ouQ ρ v a t₀ x := fun x => mul_nonneg hK (ouQ_nonneg ρ hv x)
  have hu : ∀ x : Fin d → ℝ, 1 ≤ ell x := one_le_ell
  have hp : ∀ x, |ouDensity ρ v a t₀ x| ≤ K * ouQ ρ v a t₀ x := fun x => by
    rw [abs_of_pos (ouDensity_pos ρ hv ha ht₀ x)]
    exact ouDensity_le_ouQ ρ hv ha ht₀ hS₀ le_rfl x
  have hG := abs_ouGrad_le_ouQ ρ hv hS₀ (le_refl S₀)
  have hH := abs_ouHess_le_ouQ ρ hv hS₀ (le_refl S₀)
  have hlog := abs_log_ouDensity_div_le_moment ρ hmom hv ha ht₀ hS₀ le_rfl
  have hpc := continuous_ouDensity ρ hv ha ht₀
  have hGc := continuous_ouGrad ρ hv ha ht₀
  have hHc : ∀ i, Continuous fun x => heatFlowHessPi (ouLaw ρ a t₀) (ouS v a t₀) x i i :=
    fun i => continuous_heatFlowHessPi (ρ := ouLaw ρ a t₀) hS₀ i i
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
      a * (1 + A₁ + v * A₂) * ell x * (K * ouQ ρ v a t₀ x) := by
    intro i x
    rw [abs_mul, abs_neg, abs_of_pos ha, mul_assoc a, mul_assoc a]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    have := abs_dflux_le (hu x) (hP x) hA₂ hv.le (hp x) (abs_le_ell x i) (hG x i) (hH x i)
    rwa [pow_one] at this
  have hfluxb : ∀ i x, |-a * (x i * ouDensity ρ v a t₀ x + v * ouGrad ρ v a t₀ x i)| ≤
      a * (1 + v * A₁) * ell x * (K * ouQ ρ v a t₀ x) := fun i x => by
    have := abs_flux_aux (A₁ := A₁) ha.le (hu x) hv.le (hp x) (abs_le_ell x i)
      ((hG x i).trans (by
        have := mul_le_mul_of_nonneg_left (hu x) (mul_nonneg hA₁ (hP x))
        nlinarith))
    rwa [pow_one] at this
  have hC1 : 0 ≤ a * (1 + A₁ + v * A₂) := by positivity
  have hC2 : 0 ≤ a * (1 + v * A₁) := by positivity
  obtain ⟨ε, hε, bound, hmeas, hb, hbint⟩ := hdom
  refine ⟨⟨ε, hε, bound, hmeas, hb, hbint⟩, integrable_ouKL ρ hv ha ht₀ hmom,
    fun x => (hasFDerivAt_ouDensity ρ hv ha ht₀ x).differentiableAt,
    differentiable_ouVelocity ρ hv ha ht₀, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_⟩
  · -- `p vᵢ`
    rw [eflux i]
    exact integrable_of_le_ouQ_cubic ρ hmom3 hv ha ht₀.le (by fun_prop)
      (fun x => (hfluxb i x).trans (ell_mul_le_cubW hC2 (hP x) x))
  · -- `∂ᵢ(p vᵢ)`
    rw [edflux i]
    have := hHc i
    exact integrable_of_le_ouQ_cubic ρ hmom3 hv ha ht₀.le (by fun_prop)
      (fun x => (hdfluxb i x).trans (ell_mul_le_cubW hC1 (hP x) x))
  · -- `∂ᵢ(p vᵢ) log(p/π)`
    have e : (fun x => partialDeriv i (fun y => ouDensity ρ v a t₀ y * ouVelocity ρ v a t₀ y i) x *
        Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)) =
        fun x => -a * (ouDensity ρ v a t₀ x + x i * ouGrad ρ v a t₀ x i +
          v * heatFlowHessPi (ouLaw ρ a t₀) (ouS v a t₀) x i i) *
          Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x) :=
      funext fun x => by rw [partialDeriv_ouFlux ρ hv ha ht₀ i x]
    rw [e]
    have := hHc i
    exact integrable_of_le_ouQ_cubic ρ hmom3 hv ha ht₀.le (by fun_prop)
      (fun x => abs_mul_log_cubW_le (hdfluxb i x) (hlog x))
  · -- `p vᵢ log(p/π)`
    have e : (fun x => ouDensity ρ v a t₀ x * ouVelocity ρ v a t₀ x i *
        Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)) =
        fun x => -a * (x i * ouDensity ρ v a t₀ x + v * ouGrad ρ v a t₀ x i) *
          Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x) :=
      funext fun x => by rw [ouDensity_mul_ouVelocity ρ hv ha ht₀ x i]
    rw [e]
    exact integrable_of_le_ouQ_cubic ρ hmom3 hv ha ht₀.le (by fun_prop)
      (fun x => abs_mul_log_cubW_le (hfluxb i x) (hlog x))
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

/-- **Under a third moment, `TransportKLRegularity` is exactly the domination (Verified).**
For `ρ` with `∫ ‖y‖³ dρ < ∞` (sup norm on `Fin d → ℝ`; equivalent to the Euclidean third
moment), `v, a > 0` and `t₀ > 0`:
`TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a) t₀ ↔
OUDomination ρ v a t₀`. -/
theorem transportKLRegularity_ou_iff_domination (hmom3 : Integrable (fun y => ‖y‖ ^ 3) ρ)
    (hv : 0 < v) (ha : 0 < a) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a)
      t₀ ↔ OUDomination ρ v a t₀ :=
  ⟨fun h => h.domination, transportKLRegularity_ou_of_domination ρ hmom3 hv ha ht₀⟩

end Regularity

end FormalizeSampling.ProbabilityFlowOUThirdMoment
