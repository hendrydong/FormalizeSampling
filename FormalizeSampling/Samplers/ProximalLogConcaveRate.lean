module

public import FormalizeSampling.Samplers.ProximalLogConcave
public import FormalizeSampling.Samplers.ShiftedCompositionPi

/-!
# The `1/k` KL rate of the exact proximal sampler for log-concave targets on `ℝ`

Status: **Verified** (no named hypotheses).

Setting (as in `Samplers/ProximalLogConcave.lean`): target `π = target f ∝ e^{-f}` on `ℝ` with
`f` **convex** and `∫ e^{-f} < ∞`, step `η > 0` (the **variance** of the forward Gaussian),
`proxKernel f η = rgoKernel f η ∘ₖ forwardKernel η`, iterates `ρ (k + 1) = proxKernel f η ∘ₘ ρ k`.
A coupling of `(ρ 0, π)` is a finite measure `γ₀` on `ℝ × ℝ` with these marginals.

## Main results

* `klDiv_iterate_le_div` (**main theorem**): for every `k`,
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ (x - y)² / (2 (k + 1) η) dγ₀(x, y)`, and `klDiv_iterate_le_div'`:
  `KL(ρ k ‖ π) ≤ ∫⁻ (x - y)² / (2 k η) dγ₀` for `k ≥ 1`. This is the `1/k` rate of
  Chen–Chewi–Salim–Wibisono (2022, log-concave case), here with the constant `1/(2kη)` (their
  statement has `1/(kη)`; `1/(2kη)` is what the shifted-composition argument below gives, and it
  is stated for `C²` potentials by Pedrotti, 2026, arXiv:2601.13259, Cor. 3.5), for every
  coupling, in particular for the quantile coupling.
* `klDiv_proxKernel_comp_le_self`: `KL(P ρ ‖ π) ≤ KL(ρ ‖ π)` (data processing).

## Method: shifted composition (no EVI)

The proof does not go through an evolution-variational inequality. It is a *shifted
composition* argument (Altschuler–Chewi 2023; it builds on privacy amplification by iteration,
Feldman–Mironov–Talwar–Thakurta 2018), which only uses that the proximal step is "Gaussian noise
followed by a pathwise 1-Lipschitz map". For a Markov kernel `κ` that is
`CDFShiftMonotone` (the RGO kernel for convex `f`, `cdfShiftMonotone_rgoKernel`) the quantile
representation `x' = qf (κ y) u`, `u ~ unif`, is pathwise 1-Lipschitz in `y`
(`abs_qf_sub_le_all`). Run two coupled copies `(x, y)` with common noise `(n, u)`,
`x' = qf (κ (x + n)) u`, `y' = qf (κ (y + n - t (y - x))) u` (`shiftMap`): `y` is pushed
towards `x` by a fraction `t` of the gap. Under the noise law `N(0, η) ⊗ unif` the first coordinate
performs an unshifted proximal step; under `N(t (y - x), η) ⊗ unif` the second one does. The
chain rule for KL charges `t² (x - y)² / (2η)` per step (`exists_shifted_step`), and the gap
contracts by `1 - t`. Choosing `t = 1/(k + 1), 1/k, …, 1` merges the two chains after `k + 1`
steps and the costs add up to `(x - y)² / (2 (k + 1) η)` (`klDiv_iterate_le_shifted`):

  `KL(P^{k+1} Λ₁ ‖ P^{k+1} Γ₂) ≤ KL(Λ ‖ Γ) + ∫⁻ (x - y)² dΛ / (2 (k + 1) η)`

for **any** probability laws `Λ, Γ` on `ℝ × ℝ` (`Λ₁` first marginal of `Λ`, `Γ₂` second
marginal of `Γ`) and any CDF-shift-monotone Markov kernel `κ`, with `P = κ ∘ₖ N_η`. Taking
`Λ = Γ = γ₀` and using `P π = π` gives the main theorem.

## Not proved here

* An EVI / displacement-convexity inequality for KL along quantile interpolations; it is not
  needed by the argument above and is not formalised.
* The `d`-dimensional `1/k` rate (in this file); for every convex `f` on `Fin d → ℝ` it is
  `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn`.
* Statements about the Wasserstein distance as an infimum over couplings (the bound holds for
  every coupling, hence for the infimum, but the infimum is not formalised).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.Proximal FormalizeSampling.ProximalLogConcave
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcaveRate

/-! ### Pathwise contraction of quantiles -/

/-- **Pathwise quantile contraction (all `u`).** For a CDF-shift-monotone kernel `κ` and every
`u : ℝ` (the quantile function is `0` off `(0, 1)`): `|qf (κ y) u - qf (κ y') u| ≤ |y - y'|`. -/
theorem abs_qf_sub_le_all {κ : Kernel ℝ ℝ} (hκ : CDFShiftMonotone κ) (y y' u : ℝ) :
    |qf (κ y) u - qf (κ y') u| ≤ |y - y'| := by
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · exact abs_qf_sub_le hκ y y' hu
  · simp [qf, hu]

/-! ### Shifted noise kernels -/

/-- The noise kernel `(x, y) ↦ N(c (y - x), η) ⊗ unif` on `ℝ × ℝ`: a Gaussian increment with mean
`c (y - x)` (variance `η`) together with an independent uniform variable on `(0, 1)`. -/
noncomputable def noiseKernel (η c : ℝ) : Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  (forwardKernel η).comap (fun p : ℝ × ℝ => c * (p.2 - p.1)) (by fun_prop)
    ×ₖ Kernel.const (ℝ × ℝ) unif

/-- Evaluation of the noise kernel: `noiseKernel η c (x, y) = N(c (y - x), η) ⊗ unif`, with
`N(m, η) = forwardKernel η m`. -/
theorem noiseKernel_apply (η c : ℝ) (p : ℝ × ℝ) :
    noiseKernel η c p = (forwardKernel η (c * (p.2 - p.1))).prod unif := by
  have := isFiniteKernel_forwardKernel η
  rw [noiseKernel, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply]

/-- For `η > 0` the noise kernel is a Markov kernel. -/
theorem isMarkovKernel_noiseKernel {η : ℝ} (hη : 0 < η) (c : ℝ) :
    IsMarkovKernel (noiseKernel η c) := by
  have := isMarkovKernel_forwardKernel hη
  unfold noiseKernel
  infer_instance

/-- **KL between shifted noise laws.** For `η > 0`:
`KL(noiseKernel η 0 (x, y) ‖ noiseKernel η t (x, y)) = t² (x - y)² / (2η)`. -/
theorem klDiv_noiseKernel {η : ℝ} (hη : 0 < η) (t : ℝ) (p : ℝ × ℝ) :
    klDiv (noiseKernel η 0 p) (noiseKernel η t p)
      = ENNReal.ofReal (t ^ 2 / (2 * η)) * ENNReal.ofReal ((p.1 - p.2) ^ 2) := by
  have := isMarkovKernel_forwardKernel hη
  rw [noiseKernel_apply, noiseKernel_apply, GaussianIncrement.klDiv_prod_prod, klDiv_self,
    add_zero, ProximalRegularization.klDiv_forwardKernel_apply hη,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ### The shifted synchronous step -/

/-- The shifted synchronous quantile map
`((x, y), (n, u)) ↦ (qf (κ (x + n)) u, qf (κ (y + n - t (y - x))) u)`. -/
noncomputable def shiftMap (κ : Kernel ℝ ℝ) (t : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (qf (κ (z.1.1 + z.2.1)) z.2.2, qf (κ (z.1.2 + z.2.1 - t * (z.1.2 - z.1.1))) z.2.2)

/-- The shifted synchronous quantile map is measurable (Markov `κ`). -/
theorem measurable_shiftMap (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (t : ℝ) :
    Measurable (shiftMap κ t) :=
  ((measurable_qf_kernel κ).comp
      ((measurable_fst.fst.add measurable_snd.fst).prodMk measurable_snd.snd)).prodMk
    ((measurable_qf_kernel κ).comp
      (((measurable_fst.snd.add measurable_snd.fst).sub
        (measurable_const.mul (measurable_fst.snd.sub measurable_fst.fst))).prodMk
          measurable_snd.snd))

/-- The squared quadratic transport cost `∫⁻ (x - y)² dΛ(x, y)` of a measure on `ℝ × ℝ`. -/
noncomputable def sqCost (Λ : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂Λ

/-- The squared distance is a measurable function on `ℝ × ℝ`. -/
theorem measurable_sqDist₁ :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2) := by
  fun_prop

/-- **Marginals of a shifted noisy quantile step.** For `η > 0`, a Markov kernel `κ`, a finite
`Λ` on `ℝ × ℝ`, a shift coefficient `c` and a measurable `b : ℝ × ℝ → ℝ`: if
`(p, (n, u)) ~ Λ ⊗ₘ noiseKernel η c`, then `qf (κ (b p + n - c (p.2 - p.1))) u` has law
`(κ ∘ₖ N_η) ∘ₘ Λ.map b` (the shift is exactly compensated by the mean of `n`). -/
theorem map_compProd_noiseKernel {η : ℝ} (hη : 0 < η) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (Λ : Measure (ℝ × ℝ)) [IsFiniteMeasure Λ] (c : ℝ) {b : ℝ × ℝ → ℝ} (hb : Measurable b) :
    (Λ ⊗ₘ noiseKernel η c).map
        (fun z => qf (κ (b z.1 + z.2.1 - c * (z.1.2 - z.1.1))) z.2.2)
      = (κ ∘ₖ forwardKernel η) ∘ₘ Λ.map b := by
  have := isMarkovKernel_forwardKernel hη
  have := isMarkovKernel_noiseKernel hη c
  have hm : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      qf (κ (b z.1 + z.2.1 - c * (z.1.2 - z.1.1))) z.2.2 :=
    (measurable_qf_kernel κ).comp
      ((((hb.comp measurable_fst).add measurable_snd.fst).sub
        (measurable_const.mul (measurable_fst.snd.sub measurable_fst.fst))).prodMk
          measurable_snd.snd)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map ((κ ∘ₖ forwardKernel η).measurable_coe hs) hb]
  refine lintegral_congr fun p => ?_
  set m := c * (p.2 - p.1)
  rw [noiseKernel_apply, Measure.prod_apply (measurable_prodMk_left (hm hs)),
    Kernel.comp_apply' _ _ _ hs, forwardKernel_apply hη, forwardKernel_apply hη]
  have e : ∀ n, unif (Prod.mk n ⁻¹' (Prod.mk p ⁻¹'
      ((fun z : (ℝ × ℝ) × (ℝ × ℝ) => qf (κ (b z.1 + z.2.1 - c * (z.1.2 - z.1.1))) z.2.2) ⁻¹' s)))
      = κ (b p + n - m) s := by
    intro n
    rw [← map_qf (κ (b p + n - m)), Measure.map_apply (measurable_qf _) hs]
    rfl
  simp_rw [e]
  have hg : gaussianReal (b p) η.toNNReal
      = (gaussianReal m η.toNNReal).map (· + (b p - m)) := by
    rw [gaussianReal_map_add_const]
    congr 1
    ring
  rw [hg, lintegral_map (κ.measurable_coe hs) (measurable_add_const _)]
  refine lintegral_congr fun n => ?_
  rw [show b p + n - m = n + (b p - m) by ring]

/-- **One shifted synchronous step.** Let `κ` be a CDF-shift-monotone Markov kernel, `η > 0`,
`t : ℝ`, and `Λ, Γ` probability laws on `ℝ × ℝ`; write `P = κ ∘ₖ N_η`. There are probability laws
`Λ', Γ'` on `ℝ × ℝ` with
* `Λ'₁ = P ∘ₘ Λ₁` and `Γ'₂ = P ∘ₘ Γ₂` (marginals);
* if `t = 1`, `Γ'₁ = Γ'₂` (the two coordinates are merged);
* `KL(Λ' ‖ Γ') ≤ KL(Λ ‖ Γ) + t² / (2η) · ∫⁻ (x - y)² dΛ`;
* `∫⁻ (x - y)² dΛ' ≤ (1 - t)² ∫⁻ (x - y)² dΛ`.
(`Λ' = (Λ ⊗ₘ noiseKernel η 0).map (shiftMap κ t)`,
`Γ' = (Γ ⊗ₘ noiseKernel η t).map (shiftMap κ t)`.)
-/
theorem exists_shifted_step {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (hκ : CDFShiftMonotone κ)
    {η : ℝ} (hη : 0 < η) (t : ℝ) (Λ Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Λ]
    [IsProbabilityMeasure Γ] :
    ∃ Λ' Γ' : Measure (ℝ × ℝ), IsProbabilityMeasure Λ' ∧ IsProbabilityMeasure Γ' ∧
      Λ'.map Prod.fst = (κ ∘ₖ forwardKernel η) ∘ₘ Λ.map Prod.fst ∧
      Γ'.map Prod.snd = (κ ∘ₖ forwardKernel η) ∘ₘ Γ.map Prod.snd ∧
      (t = 1 → Γ'.map Prod.fst = Γ'.map Prod.snd) ∧
      klDiv Λ' Γ' ≤ klDiv Λ Γ + ENNReal.ofReal (t ^ 2 / (2 * η)) * sqCost Λ ∧
      sqCost Λ' ≤ ENNReal.ofReal ((1 - t) ^ 2) * sqCost Λ := by
  have := isMarkovKernel_noiseKernel hη 0
  have := isMarkovKernel_noiseKernel hη t
  have hG := measurable_shiftMap κ t
  refine ⟨(Λ ⊗ₘ noiseKernel η 0).map (shiftMap κ t), (Γ ⊗ₘ noiseKernel η t).map (shiftMap κ t),
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance,
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hG]
    have e : Prod.fst ∘ shiftMap κ t =
        fun z => qf (κ (Prod.fst z.1 + z.2.1 - 0 * (z.1.2 - z.1.1))) z.2.2 := by
      funext z
      simp [shiftMap]
    rw [e]
    exact map_compProd_noiseKernel hη κ Λ 0 measurable_fst
  · rw [Measure.map_map measurable_snd hG]
    exact map_compProd_noiseKernel hη κ Γ t measurable_snd
  · rintro rfl
    rw [Measure.map_map measurable_fst hG, Measure.map_map measurable_snd hG]
    congr 1
    funext z
    simp only [Function.comp, shiftMap]
    rw [show z.1.2 + z.2.1 - 1 * (z.1.2 - z.1.1) = z.1.1 + z.2.1 by ring]
  · refine (klDiv_map_le _ _ hG).trans ?_
    rw [KL.klDiv_compProd_eq_add_lintegral]
    simp_rw [klDiv_noiseKernel hη t]
    rw [lintegral_const_mul _ measurable_sqDist₁]
    rfl
  · unfold sqCost
    rw [lintegral_map measurable_sqDist₁ hG]
    calc ∫⁻ z, ENNReal.ofReal (((shiftMap κ t z).1 - (shiftMap κ t z).2) ^ 2)
          ∂(Λ ⊗ₘ noiseKernel η 0)
        ≤ ∫⁻ z, ENNReal.ofReal ((1 - t) ^ 2) * ENNReal.ofReal ((z.1.1 - z.1.2) ^ 2)
          ∂(Λ ⊗ₘ noiseKernel η 0) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h := abs_qf_sub_le_all hκ (z.1.1 + z.2.1)
            (z.1.2 + z.2.1 - t * (z.1.2 - z.1.1)) z.2.2
          have e : z.1.1 + z.2.1 - (z.1.2 + z.2.1 - t * (z.1.2 - z.1.1))
              = (1 - t) * (z.1.1 - z.1.2) := by ring
          rw [e] at h
          rw [← mul_pow]
          exact sq_le_sq.2 h
      _ = ENNReal.ofReal ((1 - t) ^ 2) * ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂Λ := by
          rw [lintegral_const_mul _ (by fun_prop)]
          congr 1
          calc _ = ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2)
                ∂((Λ ⊗ₘ noiseKernel η 0).map Prod.fst) :=
                (lintegral_map measurable_sqDist₁ measurable_fst).symm
            _ = _ := by rw [← Measure.fst, Measure.fst_compProd]

/-! ### Iterating the shifted step -/

/-- **Shifted composition bound.** Let `κ` be a CDF-shift-monotone Markov kernel, `η > 0`,
`P = κ ∘ₖ N_η`, and `Λ, Γ` probability laws on `ℝ × ℝ` with first marginal `Λ₁` of `Λ` and
second marginal `Γ₂` of `Γ`. Then for every `k`:
`KL(P^{k+1} Λ₁ ‖ P^{k+1} Γ₂) ≤ KL(Λ ‖ Γ) + ∫⁻ (x - y)² dΛ / (2 (k + 1) η)`
(`P^{k+1} ν` is the `(k + 1)`-fold iterate of `ν ↦ P ∘ₘ ν`). -/
theorem klDiv_iterate_le_shifted {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (hκ : CDFShiftMonotone κ)
    {η : ℝ} (hη : 0 < η) (k : ℕ) (Λ Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Λ]
    [IsProbabilityMeasure Γ] :
    klDiv ((fun ν => (κ ∘ₖ forwardKernel η) ∘ₘ ν)^[k + 1] (Λ.map Prod.fst))
        ((fun ν => (κ ∘ₖ forwardKernel η) ∘ₘ ν)^[k + 1] (Γ.map Prod.snd))
      ≤ klDiv Λ Γ + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * sqCost Λ := by
  induction k generalizing Λ Γ with
  | zero =>
    obtain ⟨Λ', Γ', hΛ', hΓ', h1, h2, h3, h4, -⟩ := exists_shifted_step hκ hη 1 Λ Γ
    simp only [zero_add, Function.iterate_one]
    rw [← h1, ← h2, ← h3 rfl]
    refine (klDiv_map_le _ _ measurable_fst).trans (h4.trans_eq ?_)
    norm_num
  | succ k ih =>
    set t : ℝ := 1 / ((k : ℝ) + 2) with ht
    obtain ⟨Λ', Γ', hΛ', hΓ', h1, h2, -, h4, h5⟩ := exists_shifted_step hκ hη t Λ Γ
    rw [Function.iterate_succ_apply _ (k + 1) (Λ.map Prod.fst),
      Function.iterate_succ_apply _ (k + 1) (Γ.map Prod.snd), ← h1, ← h2]
    refine (ih Λ' Γ').trans ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc klDiv Λ' Γ' + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * sqCost Λ'
        ≤ (klDiv Λ Γ + ENNReal.ofReal (t ^ 2 / (2 * η)) * sqCost Λ)
          + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η))
            * (ENNReal.ofReal ((1 - t) ^ 2) * sqCost Λ) := by gcongr
      _ = klDiv Λ Γ + (ENNReal.ofReal (t ^ 2 / (2 * η))
          + ENNReal.ofReal (1 / (2 * ((k : ℝ) + 1) * η)) * ENNReal.ofReal ((1 - t) ^ 2))
            * sqCost Λ := by ring
      _ = klDiv Λ Γ + ENNReal.ofReal (1 / (2 * (((k + 1 : ℕ) : ℝ) + 1) * η)) * sqCost Λ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 3
        rw [ht]
        push_cast
        field_simp
        ring

/-! ### The proximal sampler -/

/-- **`1/k` KL rate of the proximal sampler for a log-concave target (1D).** Let `f` be convex
on `ℝ` with `∫ e^{-f} < ∞`, `π = target f`, `η > 0`, `ρ (k + 1) = proxKernel f η ∘ₘ ρ k`, and
let `γ₀` be any finite coupling of `(ρ 0, π)`. Then for every `k`:
`KL(ρ (k + 1) ‖ π) ≤ ∫⁻ (x - y)² / (2 (k + 1) η) dγ₀(x, y)`. -/
theorem klDiv_iterate_le_div {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) (ρ : ℕ → Measure ℝ)
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (γ₀ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ₀] (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = target f)
    (k : ℕ) :
    klDiv (ρ (k + 1)) (target f)
      ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / (2 * ((k : ℝ) + 1) * η)) ∂γ₀ := by
  have hf : Measurable f := (continuousOn_univ.1 (hconv.continuousOn isOpen_univ)).measurable
  have := isMarkovKernel_rgoKernel hf hint hη
  have := isProbabilityMeasure_target hint
  have : IsProbabilityMeasure γ₀ := ⟨by
    have h : (γ₀.map Prod.snd) univ = 1 := by rw [h₂]; exact measure_univ
    rwa [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ] at h⟩
  have hfix : (fun ν => proxKernel f η ∘ₘ ν)^[k + 1] (target f) = target f :=
    Function.iterate_fixed (proxKernel_comp_target hf hint hη) _
  have h := klDiv_iterate_le_shifted (cdfShiftMonotone_rgoKernel hconv hint hη) hη k γ₀ γ₀
  rw [h₁, h₂, klDiv_self, zero_add] at h
  rw [eq_iterate _ ρ hstep, ← hfix]
  refine h.trans_eq ?_
  rw [sqCost, ← lintegral_const_mul _ measurable_sqDist₁]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **`1/k` KL rate, `k ≥ 1` form.** Under the hypotheses of `klDiv_iterate_le_div`, for every
`k ≥ 1`: `KL(ρ k ‖ π) ≤ ∫⁻ (x - y)² / (2 k η) dγ₀(x, y)`. -/
theorem klDiv_iterate_le_div' {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) (ρ : ℕ → Measure ℝ)
    (hstep : ∀ k, ρ (k + 1) = proxKernel f η ∘ₘ ρ k) (γ₀ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ₀] (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = target f)
    {k : ℕ} (hk : 0 < k) :
    klDiv (ρ k) (target f) ≤ ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2 / (2 * k * η)) ∂γ₀ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := klDiv_iterate_le_div hconv hint hη ρ hstep γ₀ h₁ h₂ j
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- **Monotonicity of KL along the proximal chain** (data processing; measurable `f` with
`∫ e^{-f} < ∞`, `η > 0`, no convexity): for every finite `ρ`,
`KL(proxKernel f η ∘ₘ ρ ‖ π) ≤ KL(ρ ‖ π)`; hence `KL(ρ_k ‖ π)` is nonincreasing in `k`. -/
theorem klDiv_proxKernel_comp_le_self {f : ℝ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-f x))) {η : ℝ} (hη : 0 < η) (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] :
    klDiv (proxKernel f η ∘ₘ ρ) (target f) ≤ klDiv ρ (target f) :=
  ProximalContraction.klDiv_proxKernel_comp_le hf hint hη ρ

end FormalizeSampling.ProximalLogConcaveRate
