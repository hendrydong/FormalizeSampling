module

public import Mathlib.Order.SuccPred.IntervalSucc
public import FormalizeSampling.Flow.ProbabilityFlowOUThirdMoment

/-!
# The OU probability flow: moment thresholds for `TransportKLRegularity` (counterexamples)

Registry IDs: **FL-1 (II)**, **FL-2** (sharpness of `Flow/ProbabilityFlowOUMoment.lean` and
`Flow/ProbabilityFlowOUThirdMoment.lean`).

Status: **Counterexample** (Lean-verified refutations). Setting as in `ProbabilityFlowOU`, in
dimension `d = 1` (`Fin 1 → ℝ`): target `π = N(0, v)`, OU marginals
`p_t(x) = ∫ φ_{s_t}(x - c_t y) dρ(y)`, ideal velocity `ouVelocity`, `v, a > 0`.

## The laws

`rhoGeom r = ∑ₖ (1 - r) rᵏ δ_{2ᵏ}` (`0 ≤ r < 1`), a probability law on `Fin 1 → ℝ`. Its moment
of order `n` is `(1 - r) ∑ₖ (2ⁿ r)ᵏ`, finite iff `2ⁿ r < 1`.

* `r = 1/16`: finite moments of every order `< 4`, in particular a finite third moment
  (`integrable_norm_pow_rhoGeom`), and an infinite fourth moment
  (`not_integrable_norm_pow_four_rhoGeom_sixteenth`).
* `r = 1/8`: finite moments of every order `< 3`, in particular a finite second moment, and an
  infinite third moment (`not_integrable_norm_pow_three_rhoGeom_eighth`).

## Main results

* `not_ouDomination_rhoGeom`: for `1/16 ≤ r < 1/2` and every `t₀ > 0`, the time-uniform
  `domination` field of `KLDissipation.TransportKLRegularity` fails for the OU flow from
  `rhoGeom r`. Hence (`not_transportKLRegularity_rhoGeom_sixteenth`) for `ρ = rhoGeom (1/16)`,
  which has a finite third moment, `TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v)
  (ouVelocity ρ v a) t₀` fails at every `t₀ > 0`, although all its fixed-time fields hold
  (`ProbabilityFlowOUThirdMoment.transportKLRegularity_ou_iff_domination`). With
  `ProbabilityFlowOUMoment.transportKLRegularity_ou_moment`, the fourth moment is sharp on the
  scale of polynomial moments.
* `not_integrable_flux_log_rhoGeom`: for `1/8 ≤ r < 1/4` and every `t₀ > 0`, the fixed-time field
  `integrable_flux_log` (`p_{t₀} v₀ log(p_{t₀}/π)` integrable) fails. For `ρ = rhoGeom (1/8)`
  (finite second moment) this refutes the second-moment version of the fixed-time fields; with
  `ProbabilityFlowOUThirdMoment.transportKLRegularity_ou_of_domination` the third moment is sharp
  for them.

## Method

Near the atom `c_t 2ᵏ` the density is at least `wₖ φ_{s_t}(x - c_t 2ᵏ)` with `wₖ = (1 - r) rᵏ`,
so `log(p_t/π)(x) ≥ x²/(4v)` once `x² ≫ k`, and the generator `p + x ∂p + v ∂²p` is at least
`wₖ m₀ x/(4v)` at `x = c_t 2ᵏ - 3/4`; the other atoms are at distance `≳ c_t 2ᵏ`, and their
contribution `≲ exp(-c² 4ᵏ/(64 v))` is negligible (`abs_genK_le`). For the domination the
centre `c_t 2ᵏ` sweeps an interval of length `≍ 2ᵏ` as `t` runs through `[t₀, t₀ + δ]`, so any
bound integrates to at least `≍ wₖ 2ᵏ (2ᵏ)³ = (1 - r)(16 r)ᵏ` over the `k`-th interval; these
intervals are disjoint (`not_integrable_of_disjoint`). For the flux, `∂₀p log(p/π)` is integrable
under a second moment (`ProbabilityFlowOUThirdMoment.integrable_ouGrad_mul_log`), so
`x p log(p/π)` would be integrable; it is at least `≍ wₖ (2ᵏ)³ = (1 - r)(8 r)ᵏ` on unit
intervals near the atoms.

## Not proved here

* Only dimension one and these specific laws; no characterisation of the laws for which the
  domination holds (heuristically `∑ₖ wₖ |yₖ|⁴ < ∞` for well-separated atoms).
* Whether the KL derivative formula itself (rather than its sufficient condition
  `TransportKLRegularity`) holds for these laws is not addressed; the unconditional heat-flow
  route of `ProbabilityFlowOU` does not use `TransportKLRegularity`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.ProbabilityFlowOUCounterexample

open FormalizeSampling.HeatKernelPi FormalizeSampling.HeatFlowDeBruijnPi
  FormalizeSampling.HeatFlowRegularityPi FormalizeSampling.ProbabilityFlowOU
  FormalizeSampling.ProbabilityFlowOUMoment FormalizeSampling.ProbabilityFlowOUThirdMoment
open FormalizeSampling.ProximalSharpGaussianPi (scalePi measurable_scalePi)

/-! ### The discrete laws -/

/-- The atom `2ᵏ ∈ Fin 1 → ℝ`. -/
noncomputable def atom (k : ℕ) : Fin 1 → ℝ := fun _ => 2 ^ k

/-- The geometric weight `wₖ = (1 - r) rᵏ`. -/
noncomputable def geomW (r : ℝ) (k : ℕ) : ℝ := (1 - r) * r ^ k

/-- The law `∑ₖ (1 - r) rᵏ δ_{2ᵏ}` on `Fin 1 → ℝ`. -/
noncomputable def rhoGeom (r : ℝ) : Measure (Fin 1 → ℝ) :=
  Measure.sum fun k => ENNReal.ofReal (geomW r k) • Measure.dirac (atom k)

/-- `wₖ ≥ 0` for `0 ≤ r ≤ 1`. -/
theorem geomW_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (k : ℕ) : 0 ≤ geomW r k :=
  mul_nonneg (by linarith) (pow_nonneg h0 k)

/-- `∑ₖ wₖ (2ⁿ)ᵏ` converges when `0 ≤ r` and `2ⁿ r < 1`. -/
theorem summable_geomW_mul_pow {r : ℝ} (h0 : 0 ≤ r) {q : ℝ} (hq0 : 0 ≤ q) (hq : q * r < 1) :
    Summable fun k => geomW r k * q ^ k := by
  have := (summable_geometric_of_lt_one (by positivity) hq).mul_left (1 - r)
  refine this.congr fun k => ?_
  unfold geomW; rw [mul_pow]; ring

/-- `∑ₖ wₖ = 1` for `0 ≤ r < 1`. -/
theorem hasSum_geomW {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : HasSum (geomW r) 1 := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - r)
  rwa [mul_inv_cancel₀ (by linarith)] at this

/-- `rhoGeom r` is a probability measure for `0 ≤ r < 1`. -/
theorem isProbabilityMeasure_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    IsProbabilityMeasure (rhoGeom r) := by
  constructor
  rw [rhoGeom, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (geomW_nonneg h0 h1.le) (hasSum_geomW h0 h1).summable,
    (hasSum_geomW h0 h1).tsum_eq, ENNReal.ofReal_one]

/-- **Integrability against `rhoGeom r`.** A measurable `f` with `∑ₖ wₖ |f(2ᵏ)| < ∞` is
`rhoGeom r`-integrable (`0 ≤ r ≤ 1`). -/
theorem integrable_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {f : (Fin 1 → ℝ) → ℝ}
    (hf : Measurable f) (hs : Summable fun k => geomW r k * |f (atom k)|) :
    Integrable f (rhoGeom r) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, rhoGeom, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have e : ∀ k, ENNReal.ofReal (geomW r k) * ‖f (atom k)‖ₑ =
      ENNReal.ofReal (geomW r k * |f (atom k)|) := fun k => by
    rw [ENNReal.ofReal_mul (geomW_nonneg h0 h1 k), Real.enorm_eq_ofReal_abs]
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (geomW_nonneg h0 h1 k)
    (abs_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

/-- **Integrals against `rhoGeom r` are series.** For `f` integrable,
`∑ₖ wₖ f(2ᵏ) = ∫ f d(rhoGeom r)` (`0 ≤ r ≤ 1`). -/
theorem hasSum_integral_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {f : (Fin 1 → ℝ) → ℝ}
    (hf : Integrable f (rhoGeom r)) :
    HasSum (fun k => geomW r k * f (atom k)) (∫ y, f y ∂rhoGeom r) := by
  have := hasSum_integral_measure hf
  refine this.congr_fun fun k => ?_
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (geomW_nonneg h0 h1 k)]

/-- The sup norm of the atom: `‖2ᵏ‖ = 2ᵏ`. -/
theorem norm_atom (k : ℕ) : ‖atom k‖ = 2 ^ k := by
  change ‖(fun _ : Fin 1 => (2 : ℝ) ^ k)‖ = _
  rw [pi_norm_const, Real.norm_of_nonneg (by positivity)]

/-- **Moments of `rhoGeom r`.** If `0 ≤ r` and `2ⁿ r < 1`, then `∫ ‖y‖ⁿ d(rhoGeom r) < ∞`. -/
theorem integrable_norm_pow_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (n : ℕ)
    (h : (2 : ℝ) ^ n * r < 1) : Integrable (fun y => ‖y‖ ^ n) (rhoGeom r) := by
  refine integrable_rhoGeom h0 h1 (by fun_prop) ?_
  refine (summable_geomW_mul_pow h0 (by positivity) h).congr fun k => ?_
  rw [norm_atom, abs_of_nonneg (by positivity), ← pow_mul, ← pow_mul, mul_comm n k]

/-- A finite moment of order `n` forces `∑ₖ wₖ 2^{nk} < ∞`. -/
theorem summable_of_integrable_norm_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {n : ℕ}
    (h : Integrable (fun y => ‖y‖ ^ n) (rhoGeom r)) :
    Summable fun k => geomW r k * ((2 : ℝ) ^ n) ^ k := by
  refine (hasSum_integral_rhoGeom h0 h1 h).summable.congr fun k => ?_
  rw [norm_atom, ← pow_mul, ← pow_mul, mul_comm n k]

/-- `rhoGeom (1/16)` has an infinite fourth moment. -/
theorem not_integrable_norm_pow_four_rhoGeom_sixteenth :
    ¬ Integrable (fun y => ‖y‖ ^ 4) (rhoGeom (1 / 16)) := by
  intro h
  have hs := summable_of_integrable_norm_pow (by norm_num) (by norm_num) h
  have e : (fun k => geomW (1 / 16) k * ((2 : ℝ) ^ 4) ^ k) = fun _ => (15 / 16 : ℝ) := by
    funext k; unfold geomW; rw [mul_assoc, ← mul_pow]; norm_num
  rw [e, summable_const_iff] at hs
  norm_num at hs

/-- `rhoGeom (1/8)` has an infinite third moment. -/
theorem not_integrable_norm_pow_three_rhoGeom_eighth :
    ¬ Integrable (fun y => ‖y‖ ^ 3) (rhoGeom (1 / 8)) := by
  intro h
  have hs := summable_of_integrable_norm_pow (by norm_num) (by norm_num) h
  have e : (fun k => geomW (1 / 8) k * ((2 : ℝ) ^ 3) ^ k) = fun _ => (7 / 8 : ℝ) := by
    funext k; unfold geomW; rw [mul_assoc, ← mul_pow]; norm_num
  rw [e, summable_const_iff] at hs
  norm_num at hs

/-- `rhoGeom r` has a finite second moment `∫ |y|² < ∞` for `0 ≤ r < 1/4`. -/
theorem integrable_sum_sq_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1 / 4) :
    Integrable (fun y : Fin 1 → ℝ => ∑ i, y i ^ 2) (rhoGeom r) := by
  refine integrable_rhoGeom h0 (by linarith) (by fun_prop) ?_
  refine (summable_geomW_mul_pow h0 (q := 4) (by norm_num) (by linarith)).congr fun k => ?_
  simp only [atom, Fin.sum_univ_one]
  rw [abs_of_nonneg (by positivity), ← pow_mul, mul_comm k 2, pow_mul]
  norm_num

/-- `ℓ` is `rhoGeom r`-integrable for `0 ≤ r < 1/2`, with `ℓ(2ᵏ) = 1 + 2ᵏ`. -/
theorem integrable_ell_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1 / 2) :
    Integrable ell (rhoGeom r) := by
  refine integrable_rhoGeom h0 (by linarith) continuous_ell.measurable ?_
  refine ((summable_geomW_mul_pow h0 (q := 1) (by norm_num) (by linarith)).add
    (summable_geomW_mul_pow h0 (q := 2) (by norm_num) (by linarith))).congr fun k => ?_
  simp only [ell, atom, Fin.sum_univ_one, one_pow, mul_one]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  ring

/-- **One atom bounds a nonnegative integral.** For `f ≥ 0` integrable against `rhoGeom r`,
`wₖ f(2ᵏ) ≤ ∫ f d(rhoGeom r)`. -/
theorem le_integral_rhoGeom {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {f : (Fin 1 → ℝ) → ℝ}
    (hf : Integrable f (rhoGeom r)) (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) :
    geomW r k * f (atom k) ≤ ∫ y, f y ∂rhoGeom r :=
  le_hasSum (hasSum_integral_rhoGeom h0 h1 hf) k fun j _ =>
    mul_nonneg (geomW_nonneg h0 h1 j) (hf0 _)

/-- **One atom minus a tail.** If `f` is `rhoGeom r`-integrable, `E ≥ 0` and
`f(2ʲ) ≥ -E ℓ(2ʲ)` for `j ≠ k`, then `wₖ f(2ᵏ) - E ∫ ℓ d(rhoGeom r) ≤ ∫ f d(rhoGeom r)`
(`0 ≤ r < 1/2`). -/
theorem integral_rhoGeom_ge {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1 / 2) {f : (Fin 1 → ℝ) → ℝ}
    (hf : Integrable f (rhoGeom r)) {E : ℝ} (hE : 0 ≤ E) (k : ℕ)
    (hj : ∀ j, j ≠ k → -(E * ell (atom j)) ≤ f (atom j)) :
    geomW r k * f (atom k) - E * ∫ y, ell y ∂rhoGeom r ≤ ∫ y, f y ∂rhoGeom r := by
  have h1' : r ≤ 1 := by linarith
  have hell := (hasSum_integral_rhoGeom h0 h1' (integrable_ell_rhoGeom h0 h1)).mul_left E
  have hg := (hasSum_ite_eq k (geomW r k * f (atom k))).sub hell
  refine hasSum_le (fun j => ?_) hg (hasSum_integral_rhoGeom h0 h1' hf)
  have hw := geomW_nonneg h0 h1' j
  have hl := one_le_ell (atom j)
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte]
    have : 0 ≤ E * (geomW r j * ell (atom j)) := by positivity
    linarith
  · simp only [hjk, ↓reduceIte, zero_sub]
    have := mul_le_mul_of_nonneg_left (hj j hjk) hw
    linarith

/-- **Disjoint pieces of mass.** If `B : ℝ → ℝ` has `∫_{I k} |B| ≥ m > 0` for all `k ≥ K`, with
the `I k` measurable and pairwise disjoint, then `B` is not Lebesgue integrable. -/
theorem not_integrable_of_disjoint {B : ℝ → ℝ} {I : ℕ → Set ℝ} (hI : ∀ k, MeasurableSet (I k))
    (hd : Pairwise (Function.onFun Disjoint I)) {m : ℝ} (hm : 0 < m) {K : ℕ}
    (hlow : ∀ k, K ≤ k → m ≤ ∫ x in I k, |B x|) : ¬ Integrable B := by
  intro hB
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x, |B x|) / m)
  have hsum : ∑ k ∈ Finset.Ico K (K + N), ∫ x in I k, |B x| ≤ ∫ x, |B x| := by
    rw [← integral_biUnion_finset _ (fun k _ => hI k) (hd.set_pairwise _)
      fun k _ => hB.abs.integrableOn]
    exact setIntegral_le_integral hB.abs (Eventually.of_forall fun x => abs_nonneg _)
  have hlow' : (N : ℝ) * m ≤ ∑ k ∈ Finset.Ico K (K + N), ∫ x in I k, |B x| := by
    have := Finset.card_nsmul_le_sum (Finset.Ico K (K + N)) (fun k => ∫ x in I k, |B x|) m
      (fun k hk => hlow k (Finset.mem_Ico.1 hk).1)
    simpa using this
  rw [div_lt_iff₀ hm] at hN
  linarith

/-! ### The heat kernel in dimension one -/

/-- `φ_s(z) = gc 1 s · exp(-z² / (2s))` in dimension one. -/
theorem heatDensityPi_fin1 (s z : ℝ) :
    heatDensityPi s (fun _ : Fin 1 => z) = gc 1 s * Real.exp (-z ^ 2 / (2 * s)) := by
  rw [heatDensityPi_eq]; simp

/-- `x - c 2ʲ` as a point of `Fin 1 → ℝ`. -/
theorem const_sub_scalePi_atom (x c : ℝ) (j : ℕ) :
    (fun _ : Fin 1 => x) - scalePi c (atom j) = fun _ => x - c * 2 ^ j := by
  funext i; simp [scalePi, atom]

/-- The generator kernel in dimension one: if `x - w = z`, then
`g_s(x, w) = φ_s(z) (1 - x z / s + v (z² / s² - 1 / s))`. -/
theorem genK_fin1 {s v x z : ℝ} (W : Fin 1 → ℝ) (hz : (fun _ : Fin 1 => x) - W = fun _ => z) :
    genK s v (fun _ => x) W =
      gc 1 s * Real.exp (-z ^ 2 / (2 * s)) * (1 - x * z / s + v * (z ^ 2 / s ^ 2 - 1 / s)) := by
  unfold genK
  rw [hz, heatLapPi_eq]
  simp [dotProduct, heatGradPi, heatDensityPi_fin1]
  ring

/-- The lower bound `m₀ = gc 1 v · exp(-(9/16) / (2 S₀))` of `φ_s(3/4)` for `S₀ ≤ s ≤ v`. -/
noncomputable def mZero (S₀ v : ℝ) : ℝ := gc 1 v * Real.exp (-(9 / 16) / (2 * S₀))

/-- `m₀ > 0`. -/
theorem mZero_pos {S₀ v : ℝ} (hv : 0 < v) : 0 < mZero S₀ v :=
  mul_pos (gc_pos hv) (Real.exp_pos _)

/-- `m₀ ≤ φ_s(± 3/4)` for `0 < S₀ ≤ s ≤ v`. -/
theorem mZero_le {S₀ s v : ℝ} (hS₀ : 0 < S₀) (h1 : S₀ ≤ s) (h2 : s ≤ v) :
    mZero S₀ v ≤ gc 1 s * Real.exp (-(-3 / 4 : ℝ) ^ 2 / (2 * s)) := by
  have hs : 0 < s := hS₀.trans_le h1
  unfold mZero
  refine mul_le_mul (gc_anti hs h2) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    (gc_pos hs).le
  rw [neg_div, neg_div, neg_le_neg_iff]
  norm_num
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- `log φ_v(x) = log (gc 1 v) - x² / (2v)` in dimension one. -/
theorem log_heatDensityPi_fin1 {v : ℝ} (hv : 0 < v) (x : ℝ) :
    Real.log (heatDensityPi v (fun _ : Fin 1 => x)) = Real.log (gc 1 v) - x ^ 2 / (2 * v) := by
  rw [heatDensityPi_fin1, Real.log_mul (gc_pos hv).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-! ### The domination fails below the fourth moment -/

section Domination

variable {r v a : ℝ}

/-- **Pointwise lower bound for the domination integrand.** Let `0 < r < 1/2`, `v, a > 0`,
`t > 0` with `0 < S₀ ≤ s_t`, and `x = c_t 2ᵏ - 3/4` with `x ≥ 8v²/S₀`. Let
`0 ≤ D ≤ c_t 2ᵏ/2 - 3/4` (a lower bound for the distance from `x` to the other centres), and
assume the tail and log conditions `htail`, `hlog`. Then for `ρ = rhoGeom r`,
`a (wₖ m₀ x / (4v)) (x² / (4v)) ≤ |div(p_t v_t)(x)| |log(p_t(x)/φ_v(x)) + 1|`. -/
theorem domination_integrand_ge (hr : 0 < r) (h1 : r < 1 / 2) (hv : 0 < v) (ha : 0 < a)
    {S₀ t : ℝ} (hS₀ : 0 < S₀) (ht : 0 < t) (hSt : S₀ ≤ ouS v a t) {k : ℕ} {x D : ℝ}
    (hxk : x = ouC a t * 2 ^ k - 3 / 4) (hx : 8 * v ^ 2 / S₀ ≤ x) (hD0 : 0 ≤ D)
    (hD : D ≤ ouC a t * 2 ^ k / 2 - 3 / 4)
    (htail : (∫ y, ell y ∂rhoGeom r) * (genA 1 S₀ v * envK 1 S₀ v * gc 1 (2 * v)) *
      Real.exp (-D ^ 2 / (4 * v)) ≤ geomW r k * mZero S₀ v * x / (4 * v))
    (hlog : 0 ≤ Real.log (geomW r k * mZero S₀ v) - Real.log (gc 1 v) + 1 + x ^ 2 / (4 * v)) :
    a * (geomW r k * mZero S₀ v * x / (4 * v)) * (x ^ 2 / (4 * v)) ≤
      ‖-(divergence (fun y => ouDensity (rhoGeom r) v a t y • ouVelocity (rhoGeom r) v a t y)
        (fun _ : Fin 1 => x)) * (Real.log (ouDensity (rhoGeom r) v a t (fun _ : Fin 1 => x) /
          heatDensityPi v (fun _ : Fin 1 => x)) + 1)‖ := by
  have h0 := hr.le
  have := isProbabilityMeasure_rhoGeom h0 (by linarith : r < 1)
  have h1' : r ≤ 1 := by linarith
  set ρ := rhoGeom r
  set s := ouS v a t
  set c := ouC a t
  set X : Fin 1 → ℝ := fun _ => x
  have hs : 0 < s := ouS_pos hv ha ht
  have hsv : s ≤ v := ouS_le hv
  have hc0 : 0 < c := ouC_pos a t
  have hc1 : c ≤ 1 := (sq_le_one_iff₀ hc0.le).1 (ouC_sq_le_one ha.le ht.le)
  have hm0 := mZero_pos (S₀ := S₀) hv
  have hm0s := mZero_le hS₀ hSt hsv
  have hxpos : 0 < x := by have : 0 < 8 * v ^ 2 / S₀ := by positivity
                           linarith
  have hw := geomW_nonneg h0 h1' k
  set A := genA 1 S₀ v
  set Kc := envK 1 S₀ v
  set g2 := gc 1 (2 * v)
  have hA : 0 ≤ A := by simp only [A, genA]; positivity
  have hKc : 0 ≤ Kc := envK_nonneg hS₀ hv
  have hg2 : 0 < g2 := gc_pos (by positivity)
  set E := A * Kc * g2 * Real.exp (-D ^ 2 / (4 * v))
  have hE : 0 ≤ E := by positivity
  -- the generator kernel
  have hgenc : Continuous fun y => genK s v X (scalePi c y) := by
    have hc : Continuous fun w => genK s v X w := by
      unfold genK
      have := continuous_heatDensityPi (d := 1) s
      have := continuous_heatGradPi (d := 1) s
      have := continuous_heatLapPi (d := 1) s
      simp only [dotProduct]
      fun_prop
    exact hc.comp (by unfold scalePi; fun_prop)
  have hgenb : ∀ y, |genK s v X (scalePi c y)| ≤ A * Kc * g2 * ell y := by
    intro y
    refine (abs_genK_le hS₀ hSt hsv hc0.le hc1 X y).trans ?_
    have hφ := heatDensityPi_le (by positivity : 0 < 2 * v) (X - scalePi c y)
    have hℓ := one_le_ell y
    calc A * ell y * (Kc * heatDensityPi (2 * v) (X - scalePi c y))
        ≤ A * ell y * (Kc * g2) := by gcongr; exact hφ
      _ = _ := by ring
  have hgeni : Integrable (fun y => genK s v X (scalePi c y)) ρ :=
    ((integrable_ell_rhoGeom h0 h1).const_mul (A * Kc * g2)).mono' hgenc.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgenb y)
  have hk : mZero S₀ v * (x / (2 * v)) ≤ genK s v X (scalePi c (atom k)) := by
    rw [genK_fin1 (z := -3 / 4) _ (by rw [const_sub_scalePi_atom]; funext; rw [hxk]; ring)]
    · have hb : x / (2 * v) ≤ 1 - x * (-3 / 4) / s + v * ((-3 / 4) ^ 2 / s ^ 2 - 1 / s) := by
        have e1 : x / v ≤ x / s := div_le_div_of_nonneg_left hxpos.le hs hsv
        have e2 : v / s ≤ v / S₀ := div_le_div_of_nonneg_left hv.le hS₀ hSt
        have e3 : 0 ≤ v * ((-3 / 4 : ℝ) ^ 2 / s ^ 2) := by positivity
        have e4 : v / S₀ ≤ x / (8 * v) := by
          rw [div_le_div_iff₀ hS₀ (by positivity)]
          rw [div_le_iff₀ hS₀] at hx
          linarith
        have e5 : x / (2 * v) = (3 / 4) * (x / v) - x / (8 * v) - x / (8 * v) := by
          field_simp; ring
        have e6 : 1 - x * (-3 / 4) / s + v * ((-3 / 4) ^ 2 / s ^ 2 - 1 / s) =
            1 + (3 / 4) * (x / s) + v * ((-3 / 4 : ℝ) ^ 2 / s ^ 2) - v / s := by ring
        rw [e5, e6]
        have : 0 ≤ x / (8 * v) := by positivity
        linarith
      exact mul_le_mul hm0s hb (by positivity) (mul_pos (gc_pos hs) (Real.exp_pos _)).le
  have hj : ∀ j, j ≠ k → -(E * ell (atom j)) ≤ genK s v X (scalePi c (atom j)) := by
    intro j hjk
    have hb := abs_genK_le hS₀ hSt hsv hc0.le hc1 X (atom j)
    rw [const_sub_scalePi_atom, heatDensityPi_fin1] at hb
    have hdist : D ≤ |x - c * 2 ^ j| := by
      rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
      · have h2 : (2 : ℝ) ^ j * 2 ≤ 2 ^ k := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hlt
        have h3 := mul_le_mul_of_nonneg_left h2 hc0.le
        have h4 : x - c * 2 ^ j ≥ D := by rw [hxk]; linarith
        rw [abs_of_nonneg (by linarith)]
        exact h4
      · have h2 : (2 : ℝ) ^ k * 2 ≤ 2 ^ j := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hgt
        have h3 := mul_le_mul_of_nonneg_left h2 hc0.le
        have h5 : 0 ≤ c * 2 ^ k := by positivity
        have h4 : c * 2 ^ j - x ≥ D := by rw [hxk]; linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
    have hsq : D ^ 2 ≤ (x - c * 2 ^ j) ^ 2 := by
      rw [← sq_abs (x - c * 2 ^ j)]; exact pow_le_pow_left₀ hD0 hdist 2
    have hexp : Real.exp (-(x - c * 2 ^ j) ^ 2 / (2 * (2 * v))) ≤
        Real.exp (-D ^ 2 / (4 * v)) := by
      refine Real.exp_le_exp.2 ?_
      rw [show 2 * (2 * v) = 4 * v by ring, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    have hℓ := one_le_ell (atom j)
    have : |genK s v X (scalePi c (atom j))| ≤ E * ell (atom j) := by
      refine hb.trans ?_
      calc A * ell (atom j) * (Kc * (gc 1 (2 * v) *
            Real.exp (-(x - c * 2 ^ j) ^ 2 / (2 * (2 * v)))))
          ≤ A * ell (atom j) * (Kc * (g2 * Real.exp (-D ^ 2 / (4 * v)))) := by gcongr
        _ = _ := by ring
    linarith [neg_abs_le (genK s v X (scalePi c (atom j)))]
  have hgen := integral_rhoGeom_ge h0 h1 hgeni hE k hj
  have hG : geomW r k * mZero S₀ v * x / (4 * v) ≤ ∫ y, genK s v X (scalePi c y) ∂ρ := by
    have e : E * ∫ y, ell y ∂ρ = (∫ y, ell y ∂rhoGeom r) * (A * Kc * g2) *
        Real.exp (-D ^ 2 / (4 * v)) := by simp only [E, ρ]; ring
    have := mul_le_mul_of_nonneg_left hk hw
    have e2 : geomW r k * (mZero S₀ v * (x / (2 * v))) =
        2 * (geomW r k * mZero S₀ v * x / (4 * v)) := by field_simp; ring
    linarith
  -- the density and the log
  have hp : geomW r k * mZero S₀ v ≤ ouDensity ρ v a t X := by
    rw [ouDensity_eq_integral]
    have hint : Integrable (fun y => heatDensityPi s (X - scalePi c y)) ρ :=
      integrable_comp_of_bound ρ (continuous_heatDensityPi s)
        (fun z => by rw [abs_of_pos (heatDensityPi_pos hs z)]; exact heatDensityPi_le hs z)
        (by unfold scalePi; fun_prop)
    refine le_trans ?_ (le_integral_rhoGeom h0 h1' hint (fun y => (heatDensityPi_pos hs _).le) k)
    refine mul_le_mul_of_nonneg_left ?_ hw
    have e : X - scalePi c (atom k) = fun _ => (-3 / 4 : ℝ) := by
      rw [const_sub_scalePi_atom]; funext; rw [hxk]; ring
    rw [e, heatDensityPi_fin1]
    exact hm0s
  have hwpos : 0 < geomW r k * mZero S₀ v :=
    mul_pos (mul_pos (by linarith) (pow_pos hr k)) hm0
  have hpos := ouDensity_pos ρ hv ha ht X
  have hL : x ^ 2 / (4 * v) ≤ Real.log (ouDensity ρ v a t X / heatDensityPi v X) + 1 := by
    rw [Real.log_div hpos.ne' (heatDensityPi_pos hv X).ne', log_heatDensityPi_fin1 hv]
    have := Real.log_le_log hwpos hp
    have e : x ^ 2 / (2 * v) = x ^ 2 / (4 * v) + x ^ 2 / (4 * v) := by field_simp; ring
    linarith
  rw [divergence_ouFlux ρ hv ha ht, ouGen_eq_integral ρ hv ha ht X, neg_neg, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos ha]
  have hx2 : 0 ≤ x ^ 2 / (4 * v) := by positivity
  have hG0 : 0 ≤ geomW r k * mZero S₀ v * x / (4 * v) := by positivity
  calc a * (geomW r k * mZero S₀ v * x / (4 * v)) * (x ^ 2 / (4 * v))
      ≤ a * |∫ y, genK s v X (scalePi c y) ∂ρ| *
          |Real.log (ouDensity ρ v a t X / heatDensityPi v X) + 1| := by
        gcongr
        · exact hG.trans (le_abs_self _)
        · exact hL.trans (le_abs_self _)
    _ = _ := rfl

/-- The tail constant `T = (∫ ℓ dρ) A K gc(2v)` of the far atoms. -/
noncomputable def tailT (r S₀ v : ℝ) : ℝ :=
  (∫ y, ell y ∂rhoGeom r) * (genA 1 S₀ v * envK 1 S₀ v * gc 1 (2 * v))

/-- The constant `C₄ = |log(1 - r)| + |log m₀| + |log gc(v)| + 1` of the log condition. -/
noncomputable def logC (r S₀ v : ℝ) : ℝ :=
  |Real.log (1 - r)| + |Real.log (mZero S₀ v)| + |Real.log (gc 1 v)| + 1

/-- `T ≥ 0`. -/
theorem tailT_nonneg {r S₀ v : ℝ} (hS₀ : 0 < S₀) (hv : 0 < v) :
    0 ≤ tailT r S₀ v := by
  unfold tailT
  have h1 : 0 ≤ ∫ y, ell y ∂rhoGeom r :=
    integral_nonneg fun y => by simp only [Pi.zero_apply]; linarith [one_le_ell y]
  have h2 : 0 ≤ genA 1 S₀ v := by unfold genA; positivity
  have h3 := envK_nonneg (d := 1) hS₀ hv
  have h4 := gc_pos (d := 1) (by positivity : 0 < 2 * v)
  positivity

/-- `rᵏ ≥ exp(-log 16 · 2ᵏ)` for `r ≥ 1/16`. -/
theorem pow_ge_exp {r : ℝ} (hr16 : 1 / 16 ≤ r) (k : ℕ) :
    Real.exp (-(Real.log 16 * 2 ^ k)) ≤ r ^ k := by
  have hk : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hβ : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  calc Real.exp (-(Real.log 16 * 2 ^ k)) ≤ Real.exp (k * -Real.log 16) :=
        Real.exp_le_exp.2 (by nlinarith)
    _ = (1 / 16) ^ k := by
        rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    _ ≤ r ^ k := pow_le_pow_left₀ (by norm_num) hr16 k

/-- **The lower bound on the `k`-th interval.** Let `1/16 ≤ r < 1/2`, `v, a, t₀ > 0`,
`c₀ = c_{t₀}`, `c₁ = c_{t₀+δ}`, `S₀ = s_{t₀}`, `u = 2ᵏ`, and assume the largeness conditions
`4 ≤ c₁ u`, `16 v²/S₀ ≤ c₁ u`, `log 16 + |log(γ/(T + 1))| ≤ α u`, `log 16 + C₄ ≤ 4 α u`
(`α = c₁²/(64 v)`, `γ = (1 - r) m₀/(4v)`). For every `x ∈ (c₁ u - 3/4, c₀ u - 3/4)` there is
`t ∈ (t₀, t₀ + δ)` with `a wₖ m₀ (c₁u/2)³/(16 v²) ≤ |div(p_t v_t)(x)| |log(p_t(x)/φ_v(x)) + 1|`
for `ρ = rhoGeom r`. -/
theorem exists_time_ge (hr16 : 1 / 16 ≤ r) (h1 : r < 1 / 2) (hv : 0 < v) (ha : 0 < a)
    {t₀ δ : ℝ} (ht₀ : 0 < t₀) {k : ℕ}
    (hA : 4 ≤ ouC a (t₀ + δ) * 2 ^ k)
    (hB : 16 * v ^ 2 / ouS v a t₀ ≤ ouC a (t₀ + δ) * 2 ^ k)
    (hD : Real.log 16 + |Real.log ((1 - r) * mZero (ouS v a t₀) v / (4 * v) /
      (tailT r (ouS v a t₀) v + 1))| ≤ ouC a (t₀ + δ) ^ 2 / (64 * v) * 2 ^ k)
    (hE : Real.log 16 + logC r (ouS v a t₀) v ≤ 4 * (ouC a (t₀ + δ) ^ 2 / (64 * v)) * 2 ^ k)
    {x : ℝ} (hx : x ∈ Ioo (ouC a (t₀ + δ) * 2 ^ k - 3 / 4) (ouC a t₀ * 2 ^ k - 3 / 4)) :
    ∃ t ∈ Ioo t₀ (t₀ + δ), a * (geomW r k * mZero (ouS v a t₀) v *
        (ouC a (t₀ + δ) * 2 ^ k / 2) ^ 3 / (16 * v ^ 2)) ≤
      ‖-(divergence (fun y => ouDensity (rhoGeom r) v a t y • ouVelocity (rhoGeom r) v a t y)
        (fun _ : Fin 1 => x)) * (Real.log (ouDensity (rhoGeom r) v a t (fun _ : Fin 1 => x) /
          heatDensityPi v (fun _ : Fin 1 => x)) + 1)‖ := by
  have hr : 0 < r := by linarith
  set c₀ := ouC a t₀
  set c₁ := ouC a (t₀ + δ)
  set S₀ := ouS v a t₀
  set u : ℝ := 2 ^ k
  set m₀ := mZero S₀ v
  set T := tailT r S₀ v
  set α := c₁ ^ 2 / (64 * v)
  set β := Real.log 16
  set γ := (1 - r) * m₀ / (4 * v)
  have hS₀ : 0 < S₀ := ouS_pos hv ha ht₀
  have hm₀ : 0 < m₀ := mZero_pos hv
  have hT : 0 ≤ T := tailT_nonneg hS₀ hv
  have hc₁ : 0 < c₁ := ouC_pos _ _
  have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hα : 0 < α := by positivity
  have hβ : 0 ≤ β := Real.log_nonneg (by norm_num)
  have hγ : 0 < γ := by have : 0 < 1 - r := by linarith
                        positivity
  obtain ⟨hx1, hx2⟩ := hx
  -- the time
  set c := (x + 3 / 4) / u
  have hcu : c * u = x + 3 / 4 := by simp only [c]; field_simp
  have hc₁c : c₁ < c := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hcc₀ : c < c₀ := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hc : 0 < c := hc₁.trans hc₁c
  set t := -Real.log c / a
  have hct : ouC a t = c := by
    simp only [ouC, t]; rw [show -a * (-Real.log c / a) = Real.log c by field_simp]
    exact Real.exp_log hc
  have htt₀ : t₀ < t := by
    have : Real.log c < -a * t₀ := by
      rw [← Real.log_exp (-a * t₀)]; exact Real.log_lt_log hc hcc₀
    simp only [t]; rw [lt_div_iff₀ ha]; linarith
  have htδ : t < t₀ + δ := by
    have : -a * (t₀ + δ) < Real.log c := by
      rw [← Real.log_exp (-a * (t₀ + δ))]; exact Real.log_lt_log hc₁ hc₁c
    simp only [t]; rw [div_lt_iff₀ ha]; linarith
  refine ⟨t, ⟨htt₀, htδ⟩, ?_⟩
  have ht : 0 < t := ht₀.trans htt₀
  have hSt : S₀ ≤ ouS v a t := ouS_mono hv ha htt₀.le
  -- the point
  have hxk : x = ouC a t * 2 ^ k - 3 / 4 := by rw [hct]; linarith
  have hxlow : c₁ * u / 2 ≤ x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hxS : 8 * v ^ 2 / S₀ ≤ x := by
    have : 8 * v ^ 2 / S₀ = (16 * v ^ 2 / S₀) / 2 := by ring
    linarith
  have hDle : c₁ * u / 4 ≤ ouC a t * 2 ^ k / 2 - 3 / 4 := by
    rw [hct]
    have := mul_le_mul_of_nonneg_right hc₁c.le (by positivity : (0 : ℝ) ≤ u)
    linarith
  have hw : 0 ≤ geomW r k := geomW_nonneg hr.le (by linarith) k
  -- the tail condition
  have htail : T * Real.exp (-(c₁ * u / 4) ^ 2 / (4 * v)) ≤ geomW r k * m₀ * x / (4 * v) := by
    have e1 : -(c₁ * u / 4) ^ 2 / (4 * v) = -(α * u ^ 2) := by simp only [α]; field_simp; ring
    have hab := neg_le_abs (Real.log (γ / (T + 1)))
    have hlogγ : -Real.log (γ / (T + 1)) ≤ α * u - β := by linarith
    have hsplit : α * u - β ≤ α * u ^ 2 - β * u := by
      have h0' : 0 ≤ α * u - β := by linarith [abs_nonneg (Real.log (γ / (T + 1)))]
      have := mul_le_mul_of_nonneg_left hu h0'
      calc α * u - β = (α * u - β) * 1 := by ring
        _ ≤ (α * u - β) * u := this
        _ = _ := by ring
    have hexp : Real.exp (-(α * u ^ 2)) ≤ γ / (T + 1) * Real.exp (-(β * u)) := by
      rw [← Real.exp_log (by positivity : 0 < γ / (T + 1)), ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hpow := pow_ge_exp hr16 k
    have hwk : (1 - r) * Real.exp (-(β * u)) ≤ geomW r k := by
      unfold geomW
      exact mul_le_mul_of_nonneg_left (by simpa [β, u, mul_comm] using hpow) (by linarith)
    rw [e1]
    calc T * Real.exp (-(α * u ^ 2)) ≤ (T + 1) * Real.exp (-(α * u ^ 2)) := by
          gcongr; linarith
      _ ≤ (T + 1) * (γ / (T + 1) * Real.exp (-(β * u))) := by gcongr
      _ = γ * Real.exp (-(β * u)) := by field_simp
      _ = (1 - r) * Real.exp (-(β * u)) * m₀ * 1 / (4 * v) := by simp only [γ]; ring
      _ ≤ geomW r k * m₀ * x / (4 * v) := by gcongr
  -- the log condition
  have hlogc : 0 ≤ Real.log (geomW r k * m₀) - Real.log (gc 1 v) + 1 + x ^ 2 / (4 * v) := by
    have h1r : 0 < 1 - r := by linarith
    rw [geomW, Real.log_mul (by positivity) hm₀.ne', Real.log_mul h1r.ne' (by positivity),
      Real.log_pow]
    have hlr : -β ≤ Real.log r := by
      rw [← Real.log_inv, show (16 : ℝ)⁻¹ = 1 / 16 by norm_num]
      exact Real.log_le_log (by norm_num) hr16
    have hk : (k : ℝ) ≤ u := by simp only [u]; exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hkl : -(β * u) ≤ k * Real.log r := by
      have h1' := mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg k)
      have h2' := mul_le_mul_of_nonneg_right hk hβ
      linarith
    have hx2' : 4 * α * u ^ 2 ≤ x ^ 2 / (4 * v) := by
      have : (c₁ * u / 2) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hxlow 2
      have e : 4 * α * u ^ 2 = (c₁ * u / 2) ^ 2 / (4 * v) := by simp only [α]; field_simp; ring
      rw [e]; exact div_le_div_of_nonneg_right this (by positivity)
    have hC : β * u + logC r S₀ v ≤ 4 * α * u ^ 2 := by
      have hC0 : 0 ≤ logC r S₀ v := by unfold logC; positivity
      have h1' := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ u)
      have h2' := mul_le_mul_of_nonneg_left hu hC0
      have e : u * (4 * α * u) = 4 * α * u ^ 2 := by ring
      linarith
    unfold logC at hC
    linarith [neg_abs_le (Real.log (1 - r)), neg_abs_le (Real.log m₀),
      le_abs_self (Real.log (gc 1 v))]
  have key := domination_integrand_ge hr h1 hv ha hS₀ ht hSt hxk hxS (by positivity) hDle
    htail hlogc
  refine le_trans ?_ key
  have hx3 : (c₁ * u / 2) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) hxlow 3
  have e : a * (geomW r k * m₀ * x / (4 * v)) * (x ^ 2 / (4 * v)) =
      a * (geomW r k * m₀ * x ^ 3 / (16 * v ^ 2)) := by field_simp; ring
  rw [e]
  gcongr

/-- **The domination field fails (Counterexample).** For `1/16 ≤ r < 1/2`, `v, a > 0` and every
`t₀ > 0`, `OUDomination (rhoGeom r) v a t₀` is false: no Lebesgue-integrable `bound` dominates
`|div(p_t v_t)| |log(p_t/π) + 1|` uniformly for `t` near `t₀`. The `k`-th atom contributes at
least `≍ (1 - r)(16 r)ᵏ ≥ 1 - r` to the integral of any such bound. -/
theorem not_ouDomination_rhoGeom (hr16 : 1 / 16 ≤ r) (h1 : r < 1 / 2) (hv : 0 < v)
    (ha : 0 < a) {t₀ : ℝ} (ht₀ : 0 < t₀) : ¬ OUDomination (rhoGeom r) v a t₀ := by
  have hr : 0 < r := by linarith
  rintro ⟨ε, hε, bound, -, hb, hbint⟩
  set δ := min (ε / 2) (Real.log 2 / a)
  have hδ : 0 < δ := lt_min (by linarith) (div_pos (Real.log_pos (by norm_num)) ha)
  set c₀ := ouC a t₀
  set c₁ := ouC a (t₀ + δ)
  have hc₁ : 0 < c₁ := ouC_pos _ _
  have hc₁₀ : c₁ < c₀ := Real.exp_lt_exp.2 (by nlinarith)
  have hc₀₁ : c₀ ≤ 2 * c₁ := by
    have e : c₀ = c₁ * Real.exp (a * δ) := by
      simp only [c₀, c₁, ouC]; rw [← Real.exp_add]; ring_nf
    have : Real.exp (a * δ) ≤ 2 := by
      calc Real.exp (a * δ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by
            have := min_le_right (ε / 2) (Real.log 2 / a)
            rw [le_div_iff₀ ha] at this; linarith)
        _ = 2 := Real.exp_log (by norm_num)
    rw [e]; nlinarith
  set S₀ := ouS v a t₀
  have hS₀ : 0 < S₀ := ouS_pos hv ha ht₀
  set m₀ := mZero S₀ v
  have hm₀ : 0 < m₀ := mZero_pos hv
  set α := c₁ ^ 2 / (64 * v)
  have hα : 0 < α := by positivity
  set U := 4 / c₁ + 16 * v ^ 2 / S₀ / c₁ +
    (Real.log 16 + |Real.log ((1 - r) * m₀ / (4 * v) / (tailT r S₀ v + 1))|) / α +
    (Real.log 16 + logC r S₀ v) / (4 * α)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt U (by norm_num : (1 : ℝ) < 2)
  set m := a * ((1 - r) * m₀ * (c₁ / 2) ^ 3 / (16 * v ^ 2)) * (c₀ - c₁)
  have hm : 0 < m := by
    have : 0 < 1 - r := by linarith
    have : 0 < c₀ - c₁ := by linarith
    positivity
  -- transfer to `ℝ`
  set e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hsymm : ∀ x : ℝ, e.symm x = fun _ => x := fun x => by
    funext i; rw [Subsingleton.elim i default]; rfl
  set B : ℝ → ℝ := fun x => bound (fun _ => x)
  have hB : Integrable B := by
    have := (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hbint
    exact this.congr (Eventually.of_forall fun x => by
      change bound (e.symm x) = bound (fun _ => x); rw [hsymm])
  have hbB : ∀ᵐ x : ℝ, ∀ t ∈ Metric.ball t₀ ε,
      ‖-(divergence (fun y => ouDensity (rhoGeom r) v a t y • ouVelocity (rhoGeom r) v a t y)
        (fun _ : Fin 1 => x)) * (Real.log (ouDensity (rhoGeom r) v a t (fun _ : Fin 1 => x) /
          heatDensityPi v (fun _ : Fin 1 => x)) + 1)‖ ≤ B x := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hb] with x hx
    rw [hsymm] at hx
    exact hx
  set I : ℕ → Set ℝ := fun k => Ioo (c₁ * 2 ^ k - 3 / 4) (c₀ * 2 ^ k - 3 / 4)
  refine not_integrable_of_disjoint (B := B) (I := I) (fun k => measurableSet_Ioo) ?_ hm
    (K := K) (fun k hk => ?_) hB
  · -- disjointness
    have hmono : Monotone fun k : ℕ => c₁ * 2 ^ k - 3 / 4 := fun i j hij => by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij
      simp only; nlinarith
    refine (hmono.pairwise_disjoint_on_Ico_succ).mono fun i j h => h.mono ?_ ?_
    · refine Ioo_subset_Ico_self.trans (Ico_subset_Ico_right ?_)
      simp only [Order.succ_eq_add_one, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]
    · refine Ioo_subset_Ico_self.trans (Ico_subset_Ico_right ?_)
      simp only [Order.succ_eq_add_one, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
  · -- the mass of the `k`-th interval
    set u : ℝ := 2 ^ k
    have hu : U < u := hK.trans_le (pow_le_pow_right₀ (by norm_num) hk)
    have hT := tailT_nonneg (r := r) hS₀ hv
    have hC := (by unfold logC; positivity : 0 ≤ logC r S₀ v)
    have hq1 : 0 ≤ 16 * v ^ 2 / S₀ / c₁ := by positivity
    have hq2 : 0 ≤ (Real.log 16 + |Real.log ((1 - r) * m₀ / (4 * v) / (tailT r S₀ v + 1))|) /
        α := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16); positivity
    have hq3 : 0 ≤ (Real.log 16 + logC r S₀ v) / (4 * α) := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16); positivity
    have hq0 : 0 ≤ 4 / c₁ := by positivity
    have hA : 4 ≤ c₁ * u := by
      have : 4 / c₁ ≤ u := by simp only [U] at hu; linarith
      rw [div_le_iff₀ hc₁] at this
      linarith
    have hB' : 16 * v ^ 2 / S₀ ≤ c₁ * u := by
      have : 16 * v ^ 2 / S₀ / c₁ ≤ u := by simp only [U] at hu; linarith
      rw [div_le_iff₀ hc₁] at this
      linarith
    have hD : Real.log 16 + |Real.log ((1 - r) * m₀ / (4 * v) / (tailT r S₀ v + 1))| ≤
        α * u := by
      have : (Real.log 16 + |Real.log ((1 - r) * m₀ / (4 * v) / (tailT r S₀ v + 1))|) / α ≤ u :=
        by simp only [U] at hu; linarith
      rw [div_le_iff₀ hα] at this
      linarith
    have hE : Real.log 16 + logC r S₀ v ≤ 4 * α * u := by
      have : (Real.log 16 + logC r S₀ v) / (4 * α) ≤ u := by simp only [U] at hu; linarith
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    set M := a * (geomW r k * m₀ * (c₁ * u / 2) ^ 3 / (16 * v ^ 2))
    have hpt : ∀ᵐ x ∂(volume.restrict (I k)), M ≤ |B x| := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hbB] with x hx hxI
      obtain ⟨t, ⟨ht1, ht2⟩, hle⟩ := exists_time_ge hr16 h1 hv ha ht₀ hA hB' hD hE hxI
      refine hle.trans ((hx t ?_).trans (le_abs_self _))
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left (ε / 2) (Real.log 2 / a)]
    have hvol : volume.real (I k) = (c₀ - c₁) * u := by
      simp only [I, Measure.real, Real.volume_Ioo]
      rw [ENNReal.toReal_ofReal (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k])]
      simp only [u]; ring
    have hint : M * (c₀ - c₁) * u ≤ ∫ x in I k, |B x| := by
      have := integral_mono_ae (integrable_const M) hB.abs.integrableOn hpt
      rw [setIntegral_const, hvol, smul_eq_mul] at this
      linarith
    refine le_trans ?_ hint
    -- `wₖ u⁴ = (1 - r)(16 r)ᵏ ≥ 1 - r`
    have h16 : 1 ≤ (16 * r) ^ k := one_le_pow₀ (by linarith)
    have hu4 : geomW r k * u ^ 4 = (1 - r) * (16 * r) ^ k := by
      simp only [geomW, u, mul_pow, ← pow_mul]; rw [mul_comm k 4, pow_mul]; norm_num; ring
    have e : M * (c₀ - c₁) * u = m * (geomW r k * u ^ 4) / (1 - r) := by
      have : (1 - r) ≠ 0 := by linarith
      simp only [M, m]; field_simp
    rw [e, hu4, mul_div_assoc, mul_div_cancel_left₀ _ (by linarith : (1 - r) ≠ 0)]
    exact le_mul_of_one_le_right hm.le h16

/-- **A finite third moment does not give `TransportKLRegularity` (Counterexample).** For
`ρ = rhoGeom (1/16)` on `Fin 1 → ℝ` (atoms `2ᵏ`, weights `(15/16) 16^{-k}`; `∫ ‖y‖³ dρ < ∞` by
`integrable_norm_pow_rhoGeom`, `∫ ‖y‖⁴ dρ = ∞` by
`not_integrable_norm_pow_four_rhoGeom_sixteenth`), `v, a > 0` and every `t₀ > 0`,
`KLDissipation.TransportKLRegularity (ouDensity ρ v a) (heatDensityPi v) (ouVelocity ρ v a) t₀`
fails (its `domination` field fails, `not_ouDomination_rhoGeom`). -/
theorem not_transportKLRegularity_rhoGeom_sixteenth (hv : 0 < v) (ha : 0 < a) {t₀ : ℝ}
    (ht₀ : 0 < t₀) :
    ¬ KLDissipation.TransportKLRegularity (ouDensity (rhoGeom (1 / 16)) v a) (heatDensityPi v)
      (ouVelocity (rhoGeom (1 / 16)) v a) t₀ := fun h =>
  not_ouDomination_rhoGeom (by norm_num) (by norm_num) hv ha ht₀ h.domination

/-- `rhoGeom (1/16)` has a finite third moment, `∫ ‖y‖³ d(rhoGeom (1/16)) < ∞`. -/
theorem integrable_norm_pow_three_rhoGeom_sixteenth :
    Integrable (fun y => ‖y‖ ^ 3) (rhoGeom (1 / 16)) :=
  integrable_norm_pow_rhoGeom (by norm_num) (by norm_num) 3 (by norm_num)

end Domination

/-! ### The flux field fails below the third moment -/

section Flux

variable {r v a : ℝ}

/-- **Pointwise lower bound for `x p log(p/π)`.** Let `1/8 ≤ r < 1`, `v, a, t₀ > 0`,
`c = c_{t₀}`, `S₀ = s_{t₀}`, `u = 2ⁿ` with `4 ≤ c u` and `log 8 + C₄ ≤ c² u / (16 v)`. Then for
`ρ = rhoGeom r` and `|x - c u| < 3/4`,
`wₙ m₀ (c u / 2)³ / (4v) ≤ x p_{t₀}(x) log(p_{t₀}(x)/φ_v(x))`. -/
theorem flux_integrand_ge (hr8 : 1 / 8 ≤ r) (h1 : r < 1) (hv : 0 < v) (ha : 0 < a) {t₀ : ℝ}
    (ht₀ : 0 < t₀) {n : ℕ} (hA : 4 ≤ ouC a t₀ * 2 ^ n)
    (hE : Real.log 8 + logC r (ouS v a t₀) v ≤ ouC a t₀ ^ 2 / (16 * v) * 2 ^ n) {x : ℝ}
    (hx : x ∈ Ioo (ouC a t₀ * 2 ^ n - 3 / 4) (ouC a t₀ * 2 ^ n + 3 / 4)) :
    geomW r n * mZero (ouS v a t₀) v * (ouC a t₀ * 2 ^ n / 2) ^ 3 / (4 * v) ≤
      x * ouDensity (rhoGeom r) v a t₀ (fun _ : Fin 1 => x) *
        Real.log (ouDensity (rhoGeom r) v a t₀ (fun _ : Fin 1 => x) /
          heatDensityPi v (fun _ : Fin 1 => x)) := by
  have hr : 0 < r := by linarith
  have := isProbabilityMeasure_rhoGeom hr.le h1
  set ρ := rhoGeom r
  set c := ouC a t₀
  set S₀ := ouS v a t₀
  set u : ℝ := 2 ^ n
  set m₀ := mZero S₀ v
  set X : Fin 1 → ℝ := fun _ => x
  have hS₀ : 0 < S₀ := ouS_pos hv ha ht₀
  have hm₀ : 0 < m₀ := mZero_pos hv
  have hc : 0 < c := ouC_pos _ _
  have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
  obtain ⟨hx1, hx2⟩ := hx
  have hxlow : c * u / 2 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hw : 0 < geomW r n := mul_pos (by linarith) (pow_pos hr n)
  -- the density
  have hp : geomW r n * m₀ ≤ ouDensity ρ v a t₀ X := by
    rw [ouDensity_eq_integral]
    have hs := ouS_pos hv ha ht₀
    have hint : Integrable (fun y => heatDensityPi S₀ (X - scalePi c y)) ρ :=
      integrable_comp_of_bound ρ (continuous_heatDensityPi S₀)
        (fun z => by rw [abs_of_pos (heatDensityPi_pos hs z)]; exact heatDensityPi_le hs z)
        (by unfold scalePi; fun_prop)
    refine le_trans ?_ (le_integral_rhoGeom hr.le h1.le hint
      (fun y => (heatDensityPi_pos hs _).le) n)
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    rw [const_sub_scalePi_atom, heatDensityPi_fin1]
    have hz : (x - c * 2 ^ n) ^ 2 ≤ (-3 / 4 : ℝ) ^ 2 := by nlinarith
    refine (mZero_le hS₀ le_rfl (ouS_le hv)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (gc_pos hs).le
    exact div_le_div_of_nonneg_right (neg_le_neg hz) (by positivity)
  have hpm : 0 < geomW r n * m₀ := mul_pos hw hm₀
  have hpos := ouDensity_pos ρ hv ha ht₀ X
  -- the log
  have hL : x ^ 2 / (4 * v) ≤ Real.log (ouDensity ρ v a t₀ X / heatDensityPi v X) := by
    rw [Real.log_div hpos.ne' (heatDensityPi_pos hv X).ne', log_heatDensityPi_fin1 hv]
    have hlp := Real.log_le_log hpm hp
    have h1r : 0 < 1 - r := by linarith
    rw [geomW, Real.log_mul (by positivity) hm₀.ne', Real.log_mul h1r.ne' (by positivity),
      Real.log_pow] at hlp
    have hβ : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hlr : -Real.log 8 ≤ Real.log r := by
      rw [← Real.log_inv, show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
      exact Real.log_le_log (by norm_num) hr8
    have hk : (n : ℝ) ≤ u := by simp only [u]; exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have hkl : -(Real.log 8 * u) ≤ n * Real.log r := by
      have h1' := mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg n)
      have h2' := mul_le_mul_of_nonneg_right hk hβ
      linarith
    have hx2' : c ^ 2 / (16 * v) * u ^ 2 ≤ x ^ 2 / (4 * v) := by
      have : (c * u / 2) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hxlow 2
      have e : c ^ 2 / (16 * v) * u ^ 2 = (c * u / 2) ^ 2 / (4 * v) := by field_simp; norm_num
      rw [e]; exact div_le_div_of_nonneg_right this (by positivity)
    have hC : Real.log 8 * u + logC r S₀ v ≤ c ^ 2 / (16 * v) * u ^ 2 := by
      have hC0 : 0 ≤ logC r S₀ v := by unfold logC; positivity
      have h1' := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ u)
      have h2' := mul_le_mul_of_nonneg_left hu hC0
      have e : u * (c ^ 2 / (16 * v) * u) = c ^ 2 / (16 * v) * u ^ 2 := by ring
      linarith
    unfold logC at hC
    have e : x ^ 2 / (2 * v) = x ^ 2 / (4 * v) + x ^ 2 / (4 * v) := by field_simp; ring
    linarith [neg_abs_le (Real.log (1 - r)), neg_abs_le (Real.log m₀),
      le_abs_self (Real.log (gc 1 v))]
  have hx3 : (c * u / 2) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) hxlow 3
  calc geomW r n * m₀ * (c * u / 2) ^ 3 / (4 * v) ≤ geomW r n * m₀ * x ^ 3 / (4 * v) := by
        gcongr
    _ = x * (geomW r n * m₀) * (x ^ 2 / (4 * v)) := by field_simp
    _ ≤ x * ouDensity ρ v a t₀ X * Real.log (ouDensity ρ v a t₀ X / heatDensityPi v X) := by
        gcongr

/-- **The flux field fails without a third moment (Counterexample).** For `1/8 ≤ r < 1/4`
(finite second moment, `integrable_sum_sq_rhoGeom`), `v, a > 0` and every `t₀ > 0`, the
fixed-time field `integrable_flux_log` of `TransportKLRegularity` fails for the OU flow from
`ρ = rhoGeom r`: `x ↦ p_{t₀}(x) v_{t₀}(x)₀ log(p_{t₀}(x)/φ_v(x))` is not Lebesgue integrable.
(`∂₀p log(p/π)` is integrable under the second moment, so `x p log(p/π)` would be; near the
atom `c 2ⁿ` it is `≳ wₙ (c 2ⁿ)³`, and `∑ₙ wₙ 8ⁿ = ∞`.) -/
theorem not_integrable_flux_log_rhoGeom (hr8 : 1 / 8 ≤ r) (h1 : r < 1 / 4) (hv : 0 < v)
    (ha : 0 < a) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ¬ Integrable (fun x => ouDensity (rhoGeom r) v a t₀ x * ouVelocity (rhoGeom r) v a t₀ x 0 *
      Real.log (ouDensity (rhoGeom r) v a t₀ x / heatDensityPi v x)) := by
  intro hF
  have hr : 0 < r := by linarith
  have := isProbabilityMeasure_rhoGeom hr.le (by linarith : r < 1)
  set ρ := rhoGeom r
  have hmom := integrable_sum_sq_rhoGeom hr.le h1
  have hG := integrable_ouGrad_mul_log ρ hmom hv ha ht₀ 0
  -- `x₀ p log(p/π) = -(1/a) F - v G`
  set H : (Fin 1 → ℝ) → ℝ := fun x => x 0 * ouDensity ρ v a t₀ x *
    Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)
  have hH : Integrable H := by
    refine ((hF.const_mul (-(1 / a))).sub (hG.const_mul v)).congr
      (Eventually.of_forall fun x => ?_)
    change -(1 / a) * (ouDensity ρ v a t₀ x * ouVelocity ρ v a t₀ x 0 *
      Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)) - v * (ouGrad ρ v a t₀ x 0 *
      Real.log (ouDensity ρ v a t₀ x / heatDensityPi v x)) = H x
    rw [ouDensity_mul_ouVelocity ρ hv ha ht₀ x 0]
    simp only [H]
    field_simp
    ring
  -- transfer to `ℝ`
  set e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hsymm : ∀ x : ℝ, e.symm x = fun _ => x := fun x => by
    funext i; rw [Subsingleton.elim i default]; rfl
  set h : ℝ → ℝ := fun x => H (fun _ => x)
  have hh : Integrable h := by
    have := (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hH
    exact this.congr (Eventually.of_forall fun x => by
      change H (e.symm x) = H (fun _ => x); rw [hsymm])
  -- constants
  set c := ouC a t₀
  set S₀ := ouS v a t₀
  set m₀ := mZero S₀ v
  have hc : 0 < c := ouC_pos _ _
  have hS₀ : 0 < S₀ := ouS_pos hv ha ht₀
  have hm₀ : 0 < m₀ := mZero_pos hv
  have hC := (by unfold logC; positivity : 0 ≤ logC r S₀ v)
  set U := 4 / c + (Real.log 8 + logC r S₀ v) / (c ^ 2 / (16 * v))
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt U (by norm_num : (1 : ℝ) < 2)
  have hU0 : 0 ≤ (Real.log 8 + logC r S₀ v) / (c ^ 2 / (16 * v)) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8); positivity
  have hcK : 4 ≤ c * 2 ^ K := by
    have : 4 / c ≤ 2 ^ K := by simp only [U] at hK; linarith
    rw [div_le_iff₀ hc] at this; linarith
  set m := (1 - r) * m₀ * c ^ 3 / (32 * v) * (3 / 2)
  have hm : 0 < m := by have : 0 < 1 - r := by linarith
                        positivity
  set I : ℕ → Set ℝ := fun k => Ioo (c * 2 ^ (k + K) - 3 / 4) (c * 2 ^ (k + K) + 3 / 4)
  refine not_integrable_of_disjoint (B := h) (I := I) (fun k => measurableSet_Ioo) ?_ hm
    (K := 0) (fun k _ => ?_) hh
  · have hmono : Monotone fun k : ℕ => c * 2 ^ (k + K) - 3 / 4 := fun i j hij => by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.add_le_add_right hij K)
      simp only; nlinarith
    refine (hmono.pairwise_disjoint_on_Ico_succ).mono fun i j hij => hij.mono ?_ ?_
    · refine Ioo_subset_Ico_self.trans (Ico_subset_Ico_right ?_)
      simp only [Order.succ_eq_add_one, show i + 1 + K = (i + K) + 1 by ring, pow_succ]
      have : (2 : ℝ) ^ K ≤ 2 ^ (i + K) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    · refine Ioo_subset_Ico_self.trans (Ico_subset_Ico_right ?_)
      simp only [Order.succ_eq_add_one, show j + 1 + K = (j + K) + 1 by ring, pow_succ]
      have : (2 : ℝ) ^ K ≤ 2 ^ (j + K) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
  · set n := k + K
    set u : ℝ := 2 ^ n
    have hu : U < u := hK.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
    have hq0 : 0 ≤ 4 / c := by positivity
    have hA : 4 ≤ c * u := by
      have : 4 / c ≤ u := by simp only [U] at hu; linarith
      rw [div_le_iff₀ hc] at this; linarith
    have hE : Real.log 8 + logC r S₀ v ≤ c ^ 2 / (16 * v) * u := by
      have : (Real.log 8 + logC r S₀ v) / (c ^ 2 / (16 * v)) ≤ u := by
        simp only [U] at hu; linarith
      rw [div_le_iff₀ (by positivity)] at this; linarith
    set M := geomW r n * m₀ * (c * u / 2) ^ 3 / (4 * v)
    have hpt : ∀ᵐ x ∂(volume.restrict (I k)), M ≤ |h x| := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Eventually.of_forall fun x hxI => ?_
      exact (flux_integrand_ge hr8 (by linarith) hv ha ht₀ hA hE hxI).trans (le_abs_self _)
    have hvol : volume.real (I k) = 3 / 2 := by
      simp only [I, Measure.real, Real.volume_Ioo]
      rw [ENNReal.toReal_ofReal (by norm_num)]; ring
    have hint : M * (3 / 2) ≤ ∫ x in I k, |h x| := by
      have := integral_mono_ae (integrable_const M) hh.abs.integrableOn hpt
      rw [setIntegral_const, hvol, smul_eq_mul] at this
      linarith
    refine le_trans ?_ hint
    have h8 : 1 ≤ (8 * r) ^ n := one_le_pow₀ (by linarith)
    have h83 : ((2 : ℝ) ^ n) ^ 3 = 8 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e : M * (3 / 2) = m * (8 * r) ^ n := by
      simp only [M, m, geomW, u, div_pow, mul_pow, h83]
      field_simp
      ring
    rw [e]
    exact le_mul_of_one_le_right hm.le h8

end Flux

end FormalizeSampling.ProbabilityFlowOUCounterexample
