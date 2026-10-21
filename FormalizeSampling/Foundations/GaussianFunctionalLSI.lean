module

public import FormalizeSampling.Foundations.GaussianLSIZero
public import FormalizeSampling.Foundations.LogSobolev
public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.HeatKernel

/-!
# The Gaussian functional log-Sobolev inequality (Gross's inequality, 1D)

Status: **Verified** (no hypothesis beyond `t > 0` for the Gaussian functional LSI, and beyond
the functional LSI of `π` for its convolution corollary).

Notation: `γ_t = N(0, t) = gaussianReal 0 t` with Lebesgue density `φ_t = heatDensity t`;
`Ent`, `LSIClass`, `FunctionalLSI` are those of `Foundations/LogSobolev.lean`.

Route: for `g ∈ LSIClass` put `Z = ∫ g² dγ_t > 0` and `p = g² φ_t / Z`, a positive probability
density, differentiable with `p' = (2 g g' φ_t + g² φ_t') / Z`. Then
`KL(p‖γ_t) = Ent_{γ_t}(g²) / Z` (Mathlib's `klDiv` via `∫⁻ φ_t klFun(p / φ_t)`,
`GaussianLSIZero.klDiv_withDensity_eq_lintegral`) and
`p (p'/p + x/t)² = 4 (g')² φ_t / Z`, so the KL-form time-zero Gaussian LSI
`KL ≤ (t/2) ∫ p (p'/p + x/t)²` gives `Ent_{γ_t}(g²) ≤ 2 t ∫ (g')² dγ_t`. The time-zero LSI
of `Foundations/GaussianLSIZero.lean` needs no continuity of `p'`, which matters because
`deriv g` is only measurable (not continuous) for `g ∈ LSIClass`.

## Main results

* `klDiv_le_fisher0_of_hasDerivAt` (alias of `GaussianLSIZero.klDiv_le_fisher0`): the
  time-zero Gaussian LSI `KL(ρ‖N(0, v)) ≤ (v/2) ∫ p (p'/p + x/v)²` for a positive probability
  density `p` differentiable everywhere (no continuity of `p'`), with finite second moment and
  finite relative Fisher information.
* `functionalLSI_gaussianReal` (**Gross's inequality**, 1D):
  `∀ t > 0, FunctionalLSI (gaussianReal 0 t.toNNReal) t`, i.e.
  `Ent_{N(0,t)}(g²) ≤ 2 t ∫ (g')² dN(0, t)` for every `g ∈ LSIClass`.
* `functionalLSI_gaussianReal_of_nonneg`: the same for `t ≥ 0` (`t = 0` is the Dirac case).
* `heatKernel_comp_eq_map_add`: `heatKernel s ∘ₘ π` is the push-forward of `π ⊗ N(0, s)` under
  `(x, z) ↦ x + z`.
* `functionalLSI_heatKernel_comp_of_targetLSI` (**convolution with the heat kernel**):
  `FunctionalLSI π C ⇒ FunctionalLSI π_t (C + t)` for `t ≥ 0`, `π_t = π * N(0, t)` (from
  `LogSobolev.functionalLSI_map_add` and Gross's inequality).

## Not proved here

* Gross's inequality for test functions outside `LSIClass` (unbounded `g`, `g` vanishing
  somewhere), (the multi-dimensional Gaussian LSI is in `GaussianFunctionalLSIPi`).
* The passage from the functional LSI of `π_t` to the KL/Fisher inequality along the heat flow
  is in `LogSobolevExtension` (`heatFlowLSI_of_targetLSI`) and the PX-2 forward step in
  `ProximalHeatFlow` (`toReal_klDiv_proxKernel_comp_le_of_targetLSI`); bounded perturbations of
  Gaussians are handled completely in `ProximalPerturbedGaussian`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open FormalizeSampling.HeatFlowDeBruijn FormalizeSampling.ProximalContraction
open FormalizeSampling.GaussianLSI FormalizeSampling.GaussianLSIZero
open FormalizeSampling.LogSobolev
open scoped FormalizeSampling.OU

namespace FormalizeSampling.GaussianFunctionalLSI

open FormalizeSampling.MeasureHelpers (integral_withDensity_ofReal
  integrable_of_isProbabilityMeasure)

/-! ### The time-zero Gaussian LSI -/

/-- **Gaussian LSI at time zero for a differentiable density.** Alias of
`GaussianLSIZero.klDiv_le_fisher0`: the same statement. For `v > 0` and a probability law
`ρ = volume.withDensity p` on `ℝ` with `p > 0` differentiable everywhere with derivative `p'`
(no continuity of `p'`), finite second moment `∫ x² p < ∞` and finite relative Fisher information
`∫ p (p'/p + x/v)² < ∞`: `KL(ρ‖N(0, v)) < ∞` and `KL(ρ‖N(0, v)) ≤ (v/2) ∫ p (p'/p + x/v)² dx`. -/
alias klDiv_le_fisher0_of_hasDerivAt := GaussianLSIZero.klDiv_le_fisher0

/-! ### The functional Gaussian LSI -/

section Functional

/-- For `t > 0`, `N(0, t)` is the Lebesgue density law of `heatDensity t`. -/
theorem gaussianReal_eq_withDensity {t : ℝ} (ht : 0 < t) :
    gaussianReal 0 t.toNNReal = volume.withDensity fun y => ENNReal.ofReal (heatDensity t y) := by
  have ht' : t.toNNReal ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact ht
  rw [gaussianReal_of_var_ne_zero _ ht', gaussianPDF_def, ← heatDensity_eq_gaussianPDFReal ht]

/-- For `t > 0`, integrals against `N(0, t)` are Lebesgue integrals weighted by `heatDensity t`:
`∫ h dN(0, t) = ∫ φ_t(y) h(y) dy` (both sides Bochner integrals). -/
theorem integral_gaussianReal_eq {t : ℝ} (ht : 0 < t) (h : ℝ → ℝ) :
    ∫ y, h y ∂(gaussianReal 0 t.toNNReal) = ∫ y, heatDensity t y * h y := by
  rw [gaussianReal_eq_withDensity ht]
  exact integral_withDensity_ofReal (continuous_heatDensity t).measurable
    (fun y => (heatDensity_pos ht y).le) h

/-- For `t > 0`, `heatDensity t` is Lebesgue integrable with integral `1`. -/
theorem integrable_heatDensity {t : ℝ} (ht : 0 < t) : Integrable (heatDensity t) := by
  simpa using integrable_heatDensity_sub ht 0

/-- For `t > 0`, `∫ heatDensity t = 1`. -/
theorem integral_heatDensity {t : ℝ} (ht : 0 < t) : ∫ y, heatDensity t y = 1 := by
  simpa using integral_heatDensity_sub ht 0

/-- For `t > 0`, `y ↦ y² φ_t(y)` is Lebesgue integrable (second moment of `N(0, t)`). -/
theorem integrable_sq_mul_heatDensity {t : ℝ} (ht : 0 < t) :
    Integrable fun y => y ^ 2 * heatDensity t y := by
  have h : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 t.toNNReal) :=
    (memLp_id_gaussianReal 2).integrable_sq
  rw [gaussianReal_eq_withDensity ht, integrable_withDensity_iff_integrable_smul'
    (continuous_heatDensity t).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (heatDensity_pos ht y).le, smul_eq_mul, mul_comm]

/-- If `|f| ≤ K` and `f` is measurable, then `φ_t f` is Lebesgue integrable (`t > 0`). -/
theorem integrable_heatDensity_mul {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Measurable f)
    (K : ℝ) (hK : ∀ y, |f y| ≤ K) : Integrable fun y => heatDensity t y * f y :=
  (integrable_heatDensity ht).mul_bdd (c := K) hf.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hK y)

/-- **Gaussian functional log-Sobolev inequality (Gross).** For every `t > 0`, the Gaussian
`N(0, t) = gaussianReal 0 t` satisfies `FunctionalLSI N(0, t) t`:
`Ent_{N(0,t)}(g²) ≤ 2 t ∫ (g')² dN(0, t)` for every `g ∈ LSIClass`.

Proof: with `φ = φ_t`, `Z = ∫ g² φ > 0` and the probability density `p = g² φ / Z`, one has
`KL(p‖N(0, t)) = Ent_{N(0,t)}(g²) / Z` and `p (p'/p + x/t)² = 4 (g')² φ / Z`, so the KL-form
time-zero LSI `klDiv_le_fisher0_of_hasDerivAt` gives the claim after multiplying by `Z`. -/
theorem functionalLSI_gaussianReal : ∀ t > 0, FunctionalLSI (gaussianReal 0 t.toNNReal) t := by
  intro t ht g hg
  set φ := heatDensity t with hφdef
  set g' := deriv g with hg'def
  have hφ : ∀ x, 0 < φ x := heatDensity_pos ht
  have hφc : Continuous φ := continuous_heatDensity t
  have hgd : ∀ x, HasDerivAt g (g' x) x := fun x => (hg.differentiable x).hasDerivAt
  have hgc : Continuous g := hg.differentiable.continuous
  have hg'm : Measurable g' := measurable_deriv g
  obtain ⟨M, hM⟩ := hg.bounded
  obtain ⟨K, hK⟩ := hg.bounded_deriv
  obtain ⟨c, hc, hcg⟩ := hg.pos
  have hg0 : ∀ x, 0 < g x := fun x => hc.trans_le (hcg x)
  have hg2M : ∀ x, |g x ^ 2| ≤ M ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have hg'2K : ∀ x, |g' x ^ 2| ≤ K ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
  have hlogM : ∀ x, |g x ^ 2 * Real.log (g x ^ 2)| ≤ (M ^ 2) ^ 2 + 1 := fun x =>
    (abs_mul_log_le (sq_nonneg _)).trans (by
      have := hg2M x; rw [abs_of_nonneg (sq_nonneg _)] at this; gcongr)
  -- integrals against `N(0, t)` as Lebesgue integrals
  have hI1 : Integrable fun x => φ x * g x ^ 2 :=
    integrable_heatDensity_mul ht (hgc.measurable.pow_const 2) _ hg2M
  have hI2 : Integrable fun x => φ x * (g x ^ 2 * Real.log (g x ^ 2)) :=
    integrable_heatDensity_mul ht
      ((hgc.measurable.pow_const 2).mul (hgc.measurable.pow_const 2).log) _ hlogM
  have hI3 : Integrable fun x => φ x * g' x ^ 2 :=
    integrable_heatDensity_mul ht (hg'm.pow_const 2) _ hg'2K
  set Z := ∫ x, φ x * g x ^ 2 with hZdef
  have hZ : 0 < Z := by
    have h1 : ∫ x, φ x * c ^ 2 ≤ Z := integral_mono ((integrable_heatDensity ht).mul_const _) hI1
      fun x => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le (hcg x) 2) (hφ x).le
    rw [integral_mul_const, integral_heatDensity ht, one_mul] at h1
    exact (pow_pos hc 2).trans_le h1
  -- the probability density `p = g² φ / Z`
  set p : ℝ → ℝ := fun x => g x ^ 2 * φ x / Z with hpdef
  set p' : ℝ → ℝ := fun x => (2 * g x * g' x * φ x + g x ^ 2 * heatDensityD1 t x) / Z
    with hp'def
  have hp : ∀ x, 0 < p x := fun x => div_pos (mul_pos (pow_pos (hg0 x) 2) (hφ x)) hZ
  have hpd : ∀ x, HasDerivAt p (p' x) x := by
    intro x
    have := (((hgd x).pow 2).mul (hasDerivAt_heatDensity_x t x)).div_const Z
    convert this using 1
    simp only [hp'def, Nat.cast_ofNat, Pi.pow_apply, hφdef]
    ring
  have hpc : Continuous p := ((hgc.pow 2).mul hφc).div_const Z
  have hpint : ∫ x, p x = 1 := by
    simp only [hpdef]
    rw [integral_div]
    simp_rw [mul_comm (g _ ^ 2)]
    exact div_self hZ.ne'
  have hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (p x)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal _ (Eventually.of_forall fun x => (hp x).le), hpint,
      ENNReal.ofReal_one]
    exact (hI1.div_const Z).congr (Eventually.of_forall fun x => by simp only [hpdef]; ring)
  -- second moment and Fisher information
  have hmom : Integrable fun x => x ^ 2 * p x := by
    refine ((integrable_sq_mul_heatDensity ht).mul_bdd (c := M ^ 2 / Z)
      ((hgc.measurable.pow_const 2).div_const Z).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)).congr (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos hZ]
      exact div_le_div_of_nonneg_right (hg2M x) hZ.le
    · simp only [hpdef]; ring
  have hfe : ∀ x, p x * (p' x / p x + x / t) ^ 2 = 4 / Z * (φ x * g' x ^ 2) := by
    intro x
    have h1 := (hg0 x).ne'
    have h2 := (hφ x).ne'
    simp only [hpdef, hp'def, heatDensityD1, ← hφdef]
    field_simp
    ring
  have hfish : Integrable fun x => p x * (p' x / p x + x / t) ^ 2 :=
    (hI3.const_mul (4 / Z)).congr (Eventually.of_forall fun x => (hfe x).symm)
  obtain ⟨-, hlsi⟩ := klDiv_le_fisher0_of_hasDerivAt hp hpd ht hmom hfish
  -- the KL divergence is `Ent / Z`
  have hkl : (klDiv (volume.withDensity fun x => ENNReal.ofReal (p x))
      (gaussianReal 0 t.toNNReal)).toReal
      = ent (gaussianReal 0 t.toNNReal) (fun x => g x ^ 2) / Z := by
    have : IsProbabilityMeasure (volume.withDensity fun y => ENNReal.ofReal (φ y)) :=
      gaussianReal_eq_withDensity ht ▸ inferInstance
    have hent : ent (gaussianReal 0 t.toNNReal) (fun x => g x ^ 2)
        = (∫ x, φ x * (g x ^ 2 * Real.log (g x ^ 2))) - Z * Real.log Z := by
      unfold ent
      rw [integral_gaussianReal_eq ht, integral_gaussianReal_eq ht]
    have hφ1 : ∫ x, φ x = 1 := integral_heatDensity ht
    rw [hent, gaussianReal_eq_withDensity ht, klDiv_withDensity_eq_lintegral hpc.measurable
      hφc.measurable (fun x => (hp x).le) hφ]
    have hpt : ∀ x, φ x * klFun (p x / φ x) = 1 / Z * (φ x * (g x ^ 2 * Real.log (g x ^ 2)))
        - Real.log Z / Z * (φ x * g x ^ 2) + φ x - 1 / Z * (φ x * g x ^ 2) := by
      intro x
      have h1 : p x / φ x = g x ^ 2 / Z := by
        simp only [hpdef]; field_simp [(hφ x).ne']
      rw [h1, klFun_apply, Real.log_div (pow_pos (hg0 x) 2).ne' hZ.ne']
      field_simp
    have hint : Integrable fun x => φ x * klFun (p x / φ x) := by
      refine ((((hI2.const_mul (1 / Z)).sub (hI1.const_mul (Real.log Z / Z))).add
        (integrable_heatDensity ht)).sub (hI1.const_mul (1 / Z))).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
      mul_nonneg (hφ x).le (klFun_nonneg (div_pos (hp x) (hφ x)).le)),
      ENNReal.toReal_ofReal (integral_nonneg fun x =>
        mul_nonneg (hφ x).le (klFun_nonneg (div_pos (hp x) (hφ x)).le))]
    simp_rw [hpt]
    rw [integral_sub ?_ (hI1.const_mul _), integral_add ?_ (integrable_heatDensity ht),
      integral_sub (hI2.const_mul _) (hI1.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, hφ1, ← hZdef]
    · field_simp
      ring
    · exact (hI2.const_mul _).sub (hI1.const_mul _)
    · exact ((hI2.const_mul _).sub (hI1.const_mul _)).add (integrable_heatDensity ht)
  have hfi : ∫ x, p x * (p' x / p x + x / t) ^ 2
      = 4 / Z * ∫ x, deriv g x ^ 2 ∂(gaussianReal 0 t.toNNReal) := by
    rw [integral_gaussianReal_eq ht, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hfe)
  rw [hkl, hfi, div_le_iff₀ hZ] at hlsi
  have : t / 2 * (4 / Z * ∫ x, deriv g x ^ 2 ∂(gaussianReal 0 t.toNNReal)) * Z
      = 2 * t * ∫ x, deriv g x ^ 2 ∂(gaussianReal 0 t.toNNReal) := by
    field_simp; ring
  linarith

/-- **Gaussian functional LSI for every `t ≥ 0`.** `FunctionalLSI N(0, t) t` for `t ≥ 0`; at
`t = 0`, `N(0, 0) = δ₀` and the inequality is `0 ≤ 0` (`functionalLSI_dirac`). -/
theorem functionalLSI_gaussianReal_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    FunctionalLSI (gaussianReal 0 t.toNNReal) t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [Real.toNNReal_zero, gaussianReal_zero_var]
    exact functionalLSI_dirac 0 le_rfl
  · exact functionalLSI_gaussianReal t ht

end Functional

/-! ### Convolution with the heat kernel -/

section Convolution

/-- **Heat flow as a convolution.** For a probability measure `π` on `ℝ` and `s ≥ 0`,
`heatKernel s ∘ₘ π = (π ⊗ N(0, s)).map (x, z ↦ x + z)` (equality of laws). -/
theorem heatKernel_comp_eq_map_add (π : Measure ℝ) [IsProbabilityMeasure π] (s : NNReal) :
    OU.heatKernel s ∘ₘ π = (π.prod (gaussianReal 0 s)).map (fun p : ℝ × ℝ => p.1 + p.2) := by
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  ext A hA
  rw [Measure.bind_apply hA (OU.heatKernel s).aemeasurable, Measure.map_apply hadd hA,
    Measure.prod_apply (hadd hA)]
  refine lintegral_congr fun x => ?_
  have hx : gaussianReal x s = (gaussianReal 0 s).map (· + x) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [OU.heatKernel_apply, hx, Measure.map_apply (measurable_add_const x) hA]
  congr 1
  ext z
  simp [add_comm]

/-- **LSI along the heat flow, functional form.** For a probability measure `π` on `ℝ` with
`FunctionalLSI π C` and `t ≥ 0`, the heat-smoothed law `π_t = heatKernel t ∘ₘ π = π * N(0, t)`
satisfies `FunctionalLSI π_t (C + t)` (convolution stability and Gross's inequality). -/
theorem functionalLSI_heatKernel_comp_of_targetLSI (π : Measure ℝ) [IsProbabilityMeasure π]
    {C t : ℝ} (ht : 0 ≤ t) (hπ : FunctionalLSI π C) :
    FunctionalLSI (OU.heatKernel t.toNNReal ∘ₘ π) (C + t) := by
  rw [heatKernel_comp_eq_map_add]
  exact functionalLSI_map_add hπ (functionalLSI_gaussianReal_of_nonneg ht) ht

end Convolution

end FormalizeSampling.GaussianFunctionalLSI
