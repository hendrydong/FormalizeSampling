module

public import FormalizeSampling.Foundations.HeatFlowRegularity
public import FormalizeSampling.Foundations.GibbsMeasure

/-!
# Regularity of the heat flow from a posterior second-moment bound

Status: **Verified**. For a probability measure `ρ` on `ℝ` with finite second moment and a
target `π` satisfying a *posterior second-moment bound* (`PosteriorSecondMomentBound`), every
field of `HeatFlowDeBruijn.HeatFlowRegular ρ π (Ioi 0)` is proved. The posterior bound is proved
for Gaussian targets.

Notation (as in `HeatFlowDeBruijn`, `HeatFlowRegularity`): `φ_r = heatDensity r`,
`p_r = heatFlowDensity ρ r = ρ * φ_r`, `q_r = heatFlowDensity π r = π * φ_r`, with space
derivatives `q_r' = heatFlowD1 π r`, `q_r'' = heatFlowD2 π r`, and
`M_r(y) = heatFlowM2 π r y = ∫ (y - x)² φ_r(y - x) dπ(x)`, so that
`M_r(y) / q_r(y) = E[(X - y)² | X + √r Z = y]` is the posterior second moment of the noise.

Proof strategy:
* `PosteriorSecondMomentBound π`: for `0 < a ≤ b` there is `A` with
  `M_r(y) ≤ A (1 + y²) q_r(y)` for `r ∈ [a, b]`.
* Identities `q_r'' = M_r / r² - q_r / r` (`heatFlowD2_eq`) and Cauchy–Schwarz
  `q_r'² / q_r ≤ M_r / r²` (`sq_heatFlowD1_div_le_heatFlowM2`) give the ratio bounds
  `(q_r'/q_r)² ≤ B (1 + y²)` and `|q_r''/q_r| ≤ B (1 + y²)` (`exists_ratio_le`).
* With these ratio bounds and the `ρ`-side bounds of `HeatFlowRegularity` every de Bruijn
  integrand is dominated (`|log q_r| ≤ A (1 + y²)` holds for every probability `π`).
* For `π₀ = N(0, v)`, `M_r = r² (y²/(v + r)² - 1/(v + r) + 1/r) q_r ≤ (b + 1)(1 + y²) q_r`.

## Main results

* `heatFlowRegular_of_posteriorSecondMomentBound`: `HeatFlowRegular ρ π (Ioi 0)` for
  probabilities `ρ, π` with `∫ x² dρ < ∞` and `PosteriorSecondMomentBound π`.
* `posteriorSecondMomentBound_gaussianReal`: the bound for `N(0, v)`, `v > 0`.
* Gaussian targets (in the namespace `HeatFlowRegularity`): `heatFlowRegular_gaussianReal`
  (`HeatFlowRegular ρ N(0, v) (Ioi 0)` for `v > 0` and `∫ x² dρ < ∞`),
  `heatFlowRegular_gaussPotential` (the same for `target (gaussPotential α)`, `α > 0`) and
  `klDiv_heatKernel_comp_ne_top_of_moment` (`KL(ρ_t‖π_t) < ∞` for `π = N(0, v)`, `t > 0`).

## Not proved here

* Targets whose posterior second moment grows faster than `1 + y²` (e.g. heavy-tailed `π`);
  the posterior bound is only verified for Gaussians. The proximal sampler for bounded
  perturbations of a Gaussian (PX-4, `Samplers/ProximalPerturbedGaussian.lean`) needs no
  forward regularity of this kind: it uses the final form of PX-2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.GaussianLSI
open FormalizeSampling.HeatFlowRegularity

namespace FormalizeSampling.HeatFlowRegularityPerturbed

/-! ### The posterior second moment -/

/-- The unnormalised posterior second moment of the noise,
`M_t(y) = ∫ (y - x)² φ_t(y - x) dπ(x)`; `M_t(y) / q_t(y) = E[(X - y)² | X + √t Z = y]`. -/
noncomputable def heatFlowM2 (π : Measure ℝ) (t y : ℝ) : ℝ :=
  ∫ x, (y - x) ^ 2 * heatDensity t (y - x) ∂π

/-- **Posterior second-moment bound.** For every `0 < a ≤ b` there is `A` with
`M_r(y) ≤ A (1 + y²) q_r(y)` for all `r ∈ [a, b]` and `y`, i.e. the posterior second moment
`E[(X - y)² | X + √r Z = y]` grows at most quadratically in `y`, locally uniformly in `r`. -/
def PosteriorSecondMomentBound (π : Measure ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∃ A, ∀ r ∈ Icc a b, ∀ y,
    heatFlowM2 π r y ≤ A * (1 + y ^ 2) * heatFlowDensity π r y

section Posterior

variable (π : Measure ℝ) [IsProbabilityMeasure π]

/-- For `t > 0` and fixed `y`, `x ↦ (y - x)² φ_t(y - x)` is `π`-integrable. -/
theorem integrable_sq_mul_heatDensity {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun x => (y - x) ^ 2 * heatDensity t (y - x)) π := by
  refine (integrable_one_add_sq_mul_heatDensity π ht y).mono'
    ((by fun_prop : Continuous fun x : ℝ => (y - x) ^ 2).mul
      ((continuous_heatDensity t).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hφ := (heatDensity_pos ht (y - x)).le
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hφ)]
  nlinarith

omit [IsProbabilityMeasure π] in
/-- `M_t(y) ≥ 0`. -/
theorem heatFlowM2_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) : 0 ≤ heatFlowM2 π t y :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (heatDensity_pos ht _).le

/-- `q_t'' = M_t / t² - q_t / t` for `t > 0`. -/
theorem heatFlowD2_eq {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatFlowD2 π t y = heatFlowM2 π t y / t ^ 2 - heatFlowDensity π t y / t := by
  unfold heatFlowD2 heatFlowM2 heatFlowDensity
  rw [← integral_div, ← integral_div, ← integral_sub
    ((integrable_sq_mul_heatDensity π ht y).div_const _)
    ((integrable_heatDensity_sub_left π ht y).div_const _)]
  congr 1
  funext x
  unfold heatDensityD2
  ring

/-- Cauchy–Schwarz: `q_t'(y)² / q_t(y) ≤ M_t(y) / t²` for `t > 0`. -/
theorem sq_heatFlowD1_div_le_heatFlowM2 {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatFlowD1 π t y ^ 2 / heatFlowDensity π t y ≤ heatFlowM2 π t y / t ^ 2 := by
  have h := sq_heatFlowD1_div_le π ht y
  have e : ∫ x, ((y - x) / t) ^ 2 * heatDensity t (y - x) ∂π = heatFlowM2 π t y / t ^ 2 := by
    unfold heatFlowM2
    rw [← integral_div]
    congr 1
    funext x
    ring
  rwa [e] at h

/-- The constant of a posterior second-moment bound is nonnegative. -/
theorem nonneg_of_heatFlowM2_le {a A : ℝ} (ha : 0 < a)
    (h : heatFlowM2 π a 0 ≤ A * (1 + 0 ^ 2) * heatFlowDensity π a 0) : 0 ≤ A := by
  have hM := heatFlowM2_nonneg π ha 0
  have hq := heatFlowDensity_pos π ha 0
  by_contra hneg
  push Not at hneg
  have : A * (1 + 0 ^ 2) * heatFlowDensity π a 0 < 0 := by
    have : A * (1 + 0 ^ 2) < 0 := by norm_num; exact hneg
    exact mul_neg_of_neg_of_pos this hq
  linarith

/-- **Ratio bounds from the posterior bound.** If `PosteriorSecondMomentBound π`, then for
`0 < a ≤ b` there is `B ≥ 0` with `(q_r'/q_r)² ≤ B (1 + y²)` and `|q_r''/q_r| ≤ B (1 + y²)` for
all `r ∈ [a, b]` and `y`. -/
theorem exists_ratio_le (hπ : PosteriorSecondMomentBound π) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : ∃ B, 0 ≤ B ∧ ∀ r ∈ Icc a b, ∀ y,
      (heatFlowD1 π r y / heatFlowDensity π r y) ^ 2 ≤ B * (1 + y ^ 2) ∧
      |heatFlowD2 π r y / heatFlowDensity π r y| ≤ B * (1 + y ^ 2) := by
  obtain ⟨A, hA⟩ := hπ a b ha hab
  have hA0 := nonneg_of_heatFlowM2_le π ha (hA a ⟨le_rfl, hab⟩ 0)
  refine ⟨A / a ^ 2 + 1 / a, by positivity, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hq := heatFlowDensity_pos π hr0 y
  set q := heatFlowDensity π r y
  set M := heatFlowM2 π r y
  set m := M / q with hm
  have hy : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have hm0 : 0 ≤ m := div_nonneg (heatFlowM2_nonneg π hr0 y) hq.le
  have hmA : m ≤ A * (1 + y ^ 2) := by
    rw [hm, div_le_iff₀ hq]; exact hA r hr y
  have hmr : m / r ^ 2 ≤ A / a ^ 2 * (1 + y ^ 2) := by
    calc m / r ^ 2 ≤ m / a ^ 2 :=
          div_le_div_of_nonneg_left hm0 (by positivity) (by nlinarith [hr.1])
      _ ≤ A * (1 + y ^ 2) / a ^ 2 := by gcongr
      _ = _ := by ring
  have h1r : 1 / r ≤ 1 / a := one_div_le_one_div_of_le ha hr.1
  have hia : 0 ≤ 1 / a := by positivity
  constructor
  · have hcs := sq_heatFlowD1_div_le_heatFlowM2 π hr0 y
    have e : (heatFlowD1 π r y / q) ^ 2 = heatFlowD1 π r y ^ 2 / q / q := by
      field_simp
    have h2 : heatFlowD1 π r y ^ 2 / q / q ≤ M / r ^ 2 / q := by gcongr
    have e2 : M / r ^ 2 / q = m / r ^ 2 := by rw [hm]; ring
    rw [e]
    nlinarith
  · have e : heatFlowD2 π r y / q = m / r ^ 2 - 1 / r := by
      rw [heatFlowD2_eq π hr0 y, hm]
      field_simp
      rfl
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith

end Posterior

/-! ### De Bruijn regularity under the posterior bound -/

section Regular

variable (ρ π : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]

/-- Field `dominated` under `PosteriorSecondMomentBound π`: for `t > 0` the KL time derivative
`klRate` is dominated, uniformly for `r` near `t`, by `M (1 + y²) p_{4t}(y)`. -/
theorem dominated_klRate (hπ : PosteriorSecondMomentBound π)
    (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ᶠ r in 𝓝 t, ∀ y,
      |klRate (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD2 ρ) (heatFlowD2 π) r y|
        ≤ bound y := by
  set a := t / 2
  set b := 2 * t
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by simp only [a, b]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_heatFlow_le ρ ha hab
  obtain ⟨Ap, hAp⟩ := exists_abs_log_heatFlowDensity_le ρ ha hab
  obtain ⟨Aq, hAq⟩ := exists_abs_log_heatFlowDensity_le π ha hab
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le π hπ ha hab
  have hAp0 := nonneg_of_abs_log_le (hAp a ⟨le_rfl, hab⟩ 0)
  have hAq0 := nonneg_of_abs_log_le (hAq a ⟨le_rfl, hab⟩ 0)
  set M := K * (Ap + Aq + 1 + B)
  refine ⟨fun y => M * ((1 + y ^ 2) * heatFlowDensity ρ (2 * b) y),
    (integrable_one_add_sq_mul_heatFlowDensity ρ hmom (by positivity)).const_mul M, ?_⟩
  filter_upwards [Icc_mem_nhds (show a < t by simp only [a]; linarith)
    (show t < b by simp only [b]; linarith)] with r hr y
  have hr0 : 0 < r := ha.trans_le hr.1
  have hp := heatFlowDensity_pos ρ hr0 y
  have hq := heatFlowDensity_pos π hr0 y
  obtain ⟨hK1, -, hK3⟩ := hK r hr y
  have hL := abs_log_div_add_one_le hp hq (hAp r hr y) (hAq r hr y)
  set P4 := heatFlowDensity ρ (2 * b) y
  have hP4 : 0 ≤ P4 := (heatFlowDensity_pos ρ (by positivity) y).le
  have hy : 0 ≤ 1 + y ^ 2 := by positivity
  have T1 : |heatFlowD2 ρ r y * (Real.log (heatFlowDensity ρ r y / heatFlowDensity π r y) + 1)|
      ≤ K * P4 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul hK3 hL (abs_nonneg _) (by positivity)
  have T2 : |heatFlowDensity ρ r y / heatFlowDensity π r y * heatFlowD2 π r y|
      ≤ K * P4 * (B * (1 + y ^ 2)) := by
    have e : heatFlowDensity ρ r y / heatFlowDensity π r y * heatFlowD2 π r y
        = heatFlowDensity ρ r y * (heatFlowD2 π r y / heatFlowDensity π r y) := by ring
    rw [e, abs_mul, abs_of_pos hp]
    exact mul_le_mul hK1 (hB r hr y).2 (abs_nonneg _) (by positivity)
  unfold klRate
  rw [abs_div, abs_two]
  have := abs_sub (heatFlowD2 ρ r y * (Real.log (heatFlowDensity ρ r y /
    heatFlowDensity π r y) + 1)) (heatFlowDensity ρ r y / heatFlowDensity π r y *
    heatFlowD2 π r y)
  have e : M * ((1 + y ^ 2) * P4) = K * P4 * ((Ap + Aq + 1) * (1 + y ^ 2))
      + K * P4 * (B * (1 + y ^ 2)) := by simp only [M]; ring
  have : 0 ≤ K * P4 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by positivity
  have : 0 ≤ K * P4 * (B * (1 + y ^ 2)) := by positivity
  rw [e]
  linarith

/-- Field `integrable_fisher` under `PosteriorSecondMomentBound π`: for `t > 0` the relative
Fisher integrand `p_t (p_t'/p_t - q_t'/q_t)²` is Lebesgue integrable. -/
theorem integrable_fisherIntegrand (hπ : PosteriorSecondMomentBound π)
    (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    Integrable (fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t) := by
  obtain ⟨K, hK0, hK⟩ := exists_sq_heatFlowD1_div_le ρ ht
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le π hπ ht le_rfl
  have hc : Continuous (fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t) := by
    unfold fisherIntegrand relScore
    exact (continuous_heatFlowDensity ρ ht).mul ((((continuous_heatFlowD1 ρ ht).div
      (continuous_heatFlowDensity ρ ht) fun y => (heatFlowDensity_pos ρ ht y).ne').sub
      ((continuous_heatFlowD1 π ht).div (continuous_heatFlowDensity π ht)
        fun y => (heatFlowDensity_pos π ht y).ne')).pow 2)
  refine (((integrable_heatFlowDensity ρ (show 0 < 2 * t by linarith)).const_mul (2 * K)).add
    ((integrable_one_add_sq_mul_heatFlowDensity ρ hmom ht).const_mul (2 * B))).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hp := heatFlowDensity_pos ρ ht y
  set p := heatFlowDensity ρ t y
  set d := heatFlowD1 ρ t y
  set w := heatFlowD1 π t y / heatFlowDensity π t y
  have hw := (hB t ⟨le_rfl, le_rfl⟩ y).1
  have e : fisherIntegrand (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ)
      (heatFlowD1 π) t y = p * (d / p - w) ^ 2 := rfl
  rw [e, Real.norm_of_nonneg (mul_nonneg hp.le (sq_nonneg _))]
  simp only [Pi.add_apply]
  have h1 : p * (d / p - w) ^ 2 ≤ 2 * (d ^ 2 / p) + 2 * (p * w ^ 2) := by
    have e1 : p * (d / p) ^ 2 = d ^ 2 / p := by field_simp
    nlinarith [mul_nonneg hp.le (sq_nonneg (d / p + w))]
  have h2 : p * w ^ 2 ≤ B * ((1 + y ^ 2) * p) := by
    calc p * w ^ 2 ≤ p * (B * (1 + y ^ 2)) := mul_le_mul_of_nonneg_left hw hp.le
      _ = _ := by ring
  have h3 := hK y
  have e2 : 2 * B * ((1 + y ^ 2) * p) = 2 * (B * ((1 + y ^ 2) * p)) := by ring
  rw [e2]
  linarith

/-- Fields `tendsto_atBot` / `tendsto_atTop` under `PosteriorSecondMomentBound π`: for `t > 0`
the boundary flux `p_t'(log(p_t/q_t) + 1) - (p_t/q_t) q_t'` tends to `0` along any filter on
which `(y - x)² → ∞` for every `x`. -/
theorem tendsto_klFlux (hπ : PosteriorSecondMomentBound π)
    (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) {l : Filter ℝ}
    [l.IsCountablyGenerated] (hl : ∀ x, Tendsto (fun y => (y - x) ^ 2) l atTop) :
    Tendsto (klFlux (heatFlowDensity ρ) (heatFlowDensity π) (heatFlowD1 ρ) (heatFlowD1 π) t) l
      (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_heatFlow_le ρ ht le_rfl
  obtain ⟨Ap, hAp⟩ := exists_abs_log_heatFlowDensity_le ρ ht le_rfl
  obtain ⟨Aq, hAq⟩ := exists_abs_log_heatFlowDensity_le π ht le_rfl
  obtain ⟨B, hB0, hB⟩ := exists_ratio_le π hπ ht le_rfl
  have hAp0 := nonneg_of_abs_log_le (hAp t ⟨le_rfl, le_rfl⟩ 0)
  have hAq0 := nonneg_of_abs_log_le (hAq t ⟨le_rfl, le_rfl⟩ 0)
  set M := K * (Ap + Aq + 1 + (B + 1))
  have hlim := (tendsto_one_add_sq_mul_heatFlowDensity ρ hmom (show 0 < 2 * t by linarith)
    hl).const_mul M
  rw [mul_zero] at hlim
  refine squeeze_zero_norm (fun y => ?_) hlim
  have hp := heatFlowDensity_pos ρ ht y
  have hq := heatFlowDensity_pos π ht y
  obtain ⟨hK1, hK2, -⟩ := hK t ⟨le_rfl, le_rfl⟩ y
  have hL := abs_log_div_add_one_le hp hq (hAp t ⟨le_rfl, le_rfl⟩ y) (hAq t ⟨le_rfl, le_rfl⟩ y)
  set P2 := heatFlowDensity ρ (2 * t) y
  have hP2 : 0 ≤ P2 := (heatFlowDensity_pos ρ (by positivity) y).le
  have hy : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have T1 : |heatFlowD1 ρ t y * (Real.log (heatFlowDensity ρ t y / heatFlowDensity π t y) + 1)|
      ≤ K * P2 * ((Ap + Aq + 1) * (1 + y ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul hK2 hL (abs_nonneg _) (by positivity)
  have T2 : |heatFlowDensity ρ t y / heatFlowDensity π t y * heatFlowD1 π t y|
      ≤ K * P2 * ((B + 1) * (1 + y ^ 2)) := by
    set w := heatFlowD1 π t y / heatFlowDensity π t y
    have e : heatFlowDensity ρ t y / heatFlowDensity π t y * heatFlowD1 π t y
        = heatFlowDensity ρ t y * w := by simp only [w]; ring
    have hw := (hB t ⟨le_rfl, le_rfl⟩ y).1
    have hw' : |w| ≤ (B + 1) * (1 + y ^ 2) := by
      have : |w| ≤ 1 + w ^ 2 := by nlinarith [abs_nonneg w, sq_abs w, sq_nonneg (|w| - 1)]
      nlinarith
    rw [e, abs_mul, abs_of_pos hp]
    exact mul_le_mul hK1 hw' (abs_nonneg _) (by positivity)
  rw [Real.norm_eq_abs]
  unfold klFlux
  have := abs_sub (heatFlowD1 ρ t y * (Real.log (heatFlowDensity ρ t y /
    heatFlowDensity π t y) + 1)) (heatFlowDensity ρ t y / heatFlowDensity π t y *
    heatFlowD1 π t y)
  have e : M * ((1 + y ^ 2) * P2) = K * P2 * ((Ap + Aq + 1) * (1 + y ^ 2))
      + K * P2 * ((B + 1) * (1 + y ^ 2)) := by simp only [M]; ring
  rw [e]
  linarith

/-- **De Bruijn regularity under a posterior second-moment bound.** For probability measures
`ρ, π` on `ℝ` with `∫ x² dρ < ∞` and `PosteriorSecondMomentBound π`, all hypotheses of
`HeatFlowRegular` hold at every positive time: `HeatFlowRegular ρ π (Ioi 0)`. -/
theorem heatFlowRegular_of_posteriorSecondMomentBound (hπ : PosteriorSecondMomentBound π)
    (hmom : Integrable (fun x => x ^ 2) ρ) : HeatFlowRegular ρ π (Ioi 0) where
  isOpen := isOpen_Ioi
  subset_Ioi := subset_rfl
  integrable_kl _ ht := integrable_klIntegrand ρ π hmom ht
  dominated _ ht := dominated_klRate ρ π hπ hmom ht
  integrable_fisher _ ht := integrable_fisherIntegrand ρ π hπ hmom ht
  tendsto_atBot _ ht := tendsto_klFlux ρ π hπ hmom ht tendsto_sq_sub_atBot
  tendsto_atTop _ ht := tendsto_klFlux ρ π hπ hmom ht tendsto_sq_sub_atTop

end Regular

/-! ### Gaussian targets and two-sided comparison -/

/-- **Gaussian targets satisfy the posterior bound.** For `v > 0`, `N(0, v)` satisfies
`PosteriorSecondMomentBound` with `A = b + 1` on `[a, b]`: explicitly
`M_r(y) = r² (y²/(v + r)² - 1/(v + r) + 1/r) φ_{v + r}(y)`. -/
theorem posteriorSecondMomentBound_gaussianReal {v : ℝ} (hv : 0 < v) :
    PosteriorSecondMomentBound (gaussianReal 0 v.toNNReal) := by
  intro a b ha hab
  refine ⟨b + 1, fun r hr y => ?_⟩
  have hr0 : 0 < r := ha.trans_le hr.1
  have hs : 0 < v + r := by linarith
  have hD := heatFlowD2_eq (gaussianReal 0 v.toNNReal) hr0 y
  rw [heatFlowD2_gaussianReal hv hr0, heatFlowDensity_gaussianReal hv hr0] at hD
  rw [heatFlowDensity_gaussianReal hv hr0]
  set M := heatFlowM2 (gaussianReal 0 v.toNNReal) r y
  set φ := heatDensity (v + r) y
  have hφ : 0 < φ := heatDensity_pos hs y
  have hM : M = r ^ 2 * (y ^ 2 / (v + r) ^ 2 - 1 / (v + r) + 1 / r) * φ := by
    unfold heatDensityD2 at hD
    have : M / r ^ 2 = (y ^ 2 / (v + r) ^ 2 - 1 / (v + r)) * φ + φ / r := by
      simp only [φ] at hD ⊢; linarith
    field_simp at this ⊢
    linarith
  have h1 : r ^ 2 * (y ^ 2 / (v + r) ^ 2) ≤ y ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : r ^ 2 ≤ (v + r) ^ 2 := by nlinarith
    nlinarith [sq_nonneg y]
  have h2 : 0 ≤ r ^ 2 * (1 / (v + r)) := by positivity
  have h3 : r ^ 2 * (1 / r) ≤ b := by
    rw [mul_one_div, pow_two, mul_self_div_self]; exact hr.2
  have hpoly : r ^ 2 * (y ^ 2 / (v + r) ^ 2 - 1 / (v + r) + 1 / r) ≤ (b + 1) * (1 + y ^ 2) := by
    have e : r ^ 2 * (y ^ 2 / (v + r) ^ 2 - 1 / (v + r) + 1 / r)
        = r ^ 2 * (y ^ 2 / (v + r) ^ 2) - r ^ 2 * (1 / (v + r)) + r ^ 2 * (1 / r) := by ring
    have hb : 0 ≤ b := ha.le.trans hab
    nlinarith [sq_nonneg y]
  rw [hM]
  exact mul_le_mul_of_nonneg_right hpoly hφ.le

end FormalizeSampling.HeatFlowRegularityPerturbed

/-! ### The Gaussian target (statements in the namespace `HeatFlowRegularity`) -/

namespace FormalizeSampling.HeatFlowRegularity

open FormalizeSampling.HeatFlowRegularityPerturbed

/-- **De Bruijn regularity for a Gaussian target.** For a probability measure `ρ` on `ℝ` with
finite second moment `∫ x² dρ < ∞` and `v > 0`, all hypotheses of `HeatFlowRegular` hold for
`ρ` against `π = N(0, v)` at every positive time: `HeatFlowRegular ρ N(0, v) (Ioi 0)`. This is
`heatFlowRegular_of_posteriorSecondMomentBound` with `posteriorSecondMomentBound_gaussianReal`. -/
theorem heatFlowRegular_gaussianReal (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hmom : Integrable (fun x => x ^ 2) ρ) {v : ℝ} (hv : 0 < v) :
    HeatFlowRegular ρ (gaussianReal 0 v.toNNReal) (Ioi 0) :=
  heatFlowRegular_of_posteriorSecondMomentBound ρ _ (posteriorSecondMomentBound_gaussianReal hv)
    hmom

/-- **KL is finite along the heat flow for a Gaussian target.** For a probability measure `ρ`
on `ℝ` with `∫ x² dρ < ∞`, `π = N(0, v)` (`v > 0`) and `t > 0`,
`KL(ρ_t‖π_t) = KL(heatKernel t ∘ₘ ρ‖heatKernel t ∘ₘ N(0, v)) ≠ ∞`. Hence `heatKL ρ π t` is the
real value of a finite divergence. -/
theorem klDiv_heatKernel_comp_ne_top_of_moment (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {v : ℝ} (hv : 0 < v) (hmom : Integrable (fun x => x ^ 2) ρ) {t : ℝ} (ht : 0 < t) :
    klDiv (FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ ρ)
      (FormalizeSampling.OU.heatKernel t.toNNReal ∘ₘ gaussianReal 0 v.toNNReal) ≠ ⊤ :=
  GaussianLSI.klDiv_heatKernel_comp_ne_top_of_regular (heatFlowRegular_gaussianReal ρ hmom hv)
    (show t ∈ Ioi 0 from ht)

/-- `HeatFlowRegular` for the Gaussian potential target: for `α > 0` and a probability `ρ` with
`∫ x² dρ < ∞`, `HeatFlowRegular ρ (target (gaussPotential α)) (Ioi 0)`. -/
theorem heatFlowRegular_gaussPotential {α : ℝ} (hα : 0 < α) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hmom : Integrable (fun x => x ^ 2) ρ) :
    HeatFlowRegular ρ (Proximal.target (ProximalSharp.gaussPotential α)) (Ioi 0) := by
  rw [ProximalSharp.target_gaussPotential hα]
  exact heatFlowRegular_gaussianReal ρ hmom (inv_pos.2 hα)

end FormalizeSampling.HeatFlowRegularity
