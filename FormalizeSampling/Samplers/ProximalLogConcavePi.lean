module

public import FormalizeSampling.Samplers.ProximalLogConcaveRate
public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.BakryEmeryGeneralPi
public import FormalizeSampling.Samplers.ProximalSharpPi

/-!
# Coupling contraction of the proximal sampler on `Fin d → ℝ`: separable log-concave targets

Status: **Verified** (no named hypotheses).

Setting (as in `Samplers/ProximalPi.lean`): target `π = targetPi f ∝ e^{-f}` on `Fin d → ℝ`, step
`η > 0` (the **variance** of the forward Gaussian), `proxKernelPi f η = rgoKernelPi f η ∘ₖ
forwardKernelPi η`. A coupling of `(ρ, μ)` is a finite measure `γ` on
`(Fin d → ℝ) × (Fin d → ℝ)` with `γ.map Prod.fst = ρ`, `γ.map Prod.snd = μ`; transport costs are
`∫⁻ φ(|x - y|²) dγ` with `|x - y|² = sqDist x y` and `φ : ℝ → ℝ≥0∞` measurable and monotone on
`[0, ∞)`.

## Main results

* `exists_coupling_forwardKernelPi` (**forward step**, any `η`): the synchronous coupling
  `(x + ξ, y + ξ)`, `ξ ~ N(0, η I)`, transports a coupling of `(ρ, μ)` to a coupling of
  `(N_η ∘ₘ ρ, N_η ∘ₘ μ)` with the **same** cost.
* `exists_coupling_pi` (**product kernels**): if `K y = ⊗ᵢ κᵢ (yᵢ)` with each `κᵢ`
  CDF-shift-monotone (`ProximalLogConcave.CDFShiftMonotone`), the coordinatewise quantile coupling
  with a common uniform vector `u ∈ (0, 1)^d` does not increase the cost.
* `rgoKernelPi_eq_pi` (**separable RGO**): if `f x = ∑ᵢ gᵢ(xᵢ)` then
  `RGO_f(y) = ⊗ᵢ RGO_{gᵢ}(yᵢ)`; `integrable_exp_neg_sum`: `∫ e^{-f} < ∞` if every `∫ e^{-gᵢ} < ∞`.
* `exists_coupling_proxKernelPi_separable` (**W-nonexpansiveness**, separable convex `f`): every
  coupling `γ` of `(ρ, μ)` yields a coupling of `(P ∘ₘ ρ, P ∘ₘ μ)` of no larger cost.
* `exists_coupling_iteratePi` and `klDiv_iteratePi_le_coupling` (**main theorem**): for separable
  convex `f = ∑ᵢ gᵢ(xᵢ)`, iterates `ρ (k + 1) = P ∘ₘ ρ k` and a coupling `γ₀` of `(ρ 0, π)`:
  `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2η) dγ₀` for every `k`.

## Not proved here

* The coupling contraction of the RGO kernel for a **general** (non-separable) convex `f` on
  `Fin d → ℝ`. A Knothe–Rosenblatt (triangular) quantile coupling built from one-dimensional
  conditional quantiles is *not* obviously contractive for the Euclidean cost (the conditional
  laws of later coordinates depend on the earlier ones, and the 1D estimate only controls each
  conditional by the shift of the conditioning variables in a non-Euclidean way). The standard
  proof uses a synchronous coupling of two Langevin diffusions with potentials
  `f + |· - y|² / (2η)` and `f + |· - y'|² / (2η)`, which is not formalised.
* The `1/k` rate is not proved in this file; for separable `f` it is
  `ProximalLogConcaveRatePi.klDiv_iteratePi_le_div`. For any `f` whose RGO kernel
  has a pathwise `1`-Lipschitz representation it is
  `ProximalLogConcaveRateGeneralPi.klDiv_iteratePi_le_div_of_hasLipRep`; such representations are
  constructed for separable convex plus positive semidefinite quadratic potentials
  (`Samplers/RGOCouplingQuadraticPi.lean`) and their rotations
  (`Samplers/RGOCouplingRotationPi.lean`). For general convex `f` in dimension `d` the rate is
  `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn` (through a weak
  coupling instead of a pathwise one).
* Statements about the Wasserstein distance as an infimum over couplings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.Proximal FormalizeSampling.ProximalPi FormalizeSampling.ProximalLogConcave
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcavePi

open FormalizeSampling.MeasureHelpers (pi_withDensity_ofReal)

variable {d : ℕ}

/-- The squared-distance cost `φ(|x - y|²)` is measurable for measurable `φ`. -/
theorem measurable_cost {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => φ (sqDist p.1 p.2) :=
  hφm.comp continuous_sqDist.measurable

/-! ### Forward step: synchronous Gaussian coupling -/

/-- The centred isotropic Gaussian `N(0, η I) = ⊗ᵢ N(0, η)` on `Fin d → ℝ`. -/
noncomputable def gaussPi (η : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 η.toNNReal

/-- The centred isotropic Gaussian is a probability measure. -/
instance isProbabilityMeasure_gaussPi (η : ℝ) : IsProbabilityMeasure (gaussPi (d := d) η) := by
  unfold gaussPi
  infer_instance

/-- **Forward step as a translation.** For a finite `γ` on `β` and measurable
`b : β → Fin d → ℝ`: if `z ~ γ` and `ξ ~ N(0, η I)` independent, then `ξ + b z` has law
`forwardKernelPi η ∘ₘ γ.map b`. -/
theorem map_prod_gaussPi {β : Type*} [MeasurableSpace β] (η : ℝ) (γ : Measure β)
    [IsFiniteMeasure γ] {b : β → Fin d → ℝ} (hb : Measurable b) :
    (γ.prod (gaussPi η)).map (fun z => z.2 + b z.1) = forwardKernelPi η ∘ₘ γ.map b := by
  have hm : Measurable fun z : β × (Fin d → ℝ) => z.2 + b z.1 :=
    measurable_snd.add (hb.comp measurable_fst)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map ((forwardKernelPi η).measurable_coe hs) hb]
  refine lintegral_congr fun x => ?_
  rw [forwardKernelPi_apply, GaussianIncrement.pi_gaussianReal_eq_map,
    Measure.map_apply (by fun_prop) hs]
  rfl

/-- **Synchronous coupling of the forward step** (any `η`). If `γ` is a finite coupling of
`(ρ, μ)` on `Fin d → ℝ`, then `γ' = law of (x + ξ, y + ξ)` with `(x, y) ~ γ`, `ξ ~ N(0, η I)`
independent, is a finite coupling of `(N_η ∘ₘ ρ, N_η ∘ₘ μ)` with
`∫⁻ φ(|x - y|²) dγ' = ∫⁻ φ(|x - y|²) dγ` for every measurable `φ`. -/
theorem exists_coupling_forwardKernelPi (η : ℝ) {ρ μ : Measure (Fin d → ℝ)}
    (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ)
    (h₂ : γ.map Prod.snd = μ) {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ) :
    ∃ γ' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsFiniteMeasure γ' ∧
      γ'.map Prod.fst = forwardKernelPi η ∘ₘ ρ ∧ γ'.map Prod.snd = forwardKernelPi η ∘ₘ μ ∧
      ∫⁻ p, φ (sqDist p.1 p.2) ∂γ' = ∫⁻ p, φ (sqDist p.1 p.2) ∂γ := by
  set G : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin d → ℝ) → (Fin d → ℝ) × (Fin d → ℝ) :=
    fun z => (z.2 + z.1.1, z.2 + z.1.2) with hGdef
  have hG : Measurable G :=
    (measurable_snd.add measurable_fst.fst).prodMk (measurable_snd.add measurable_fst.snd)
  refine ⟨(γ.prod (gaussPi η)).map G, by infer_instance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hG, ← h₁]
    exact map_prod_gaussPi η γ measurable_fst
  · rw [Measure.map_map measurable_snd hG, ← h₂]
    exact map_prod_gaussPi η γ measurable_snd
  · rw [lintegral_map (measurable_cost hφm) hG,
      lintegral_prod (fun z => φ (sqDist (G z).1 (G z).2))
        ((measurable_cost hφm).comp hG).aemeasurable]
    refine lintegral_congr fun p => ?_
    simp only [hGdef, sqDist_add_add, lintegral_const, measure_univ, mul_one]

/-! ### Product kernels: coordinatewise quantile coupling -/

/-- The uniform law on the cube `(0, 1)^d`. -/
noncomputable def unifPi : Measure (Fin d → ℝ) := Measure.pi fun _ => unif

/-- The uniform law on the cube is a probability measure. -/
instance isProbabilityMeasure_unifPi : IsProbabilityMeasure (unifPi (d := d)) := by
  unfold unifPi
  infer_instance

/-- The coordinatewise quantile map `u ↦ (qf (κᵢ (yᵢ)) uᵢ)ᵢ` of a family of kernels on `ℝ`. -/
noncomputable def qfPi (κ : Fin d → Kernel ℝ ℝ) (y u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => qf (κ i (y i)) (u i)

/-- The coordinatewise quantile map is jointly measurable in `(y, u)` (Markov kernels). -/
theorem measurable_qfPi (κ : Fin d → Kernel ℝ ℝ) [∀ i, IsMarkovKernel (κ i)] :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => qfPi κ p.1 p.2 :=
  measurable_pi_iff.2 fun i => by
    unfold qfPi
    exact (measurable_qf_kernel (κ i)).comp
      (by fun_prop : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => (p.1 i, p.2 i))

/-- **Product quantile representation.** For Markov kernels `κᵢ` and `y : Fin d → ℝ`, the
coordinatewise quantile map pushes the uniform law on the cube to `⊗ᵢ κᵢ (yᵢ)`. -/
theorem map_qfPi (κ : Fin d → Kernel ℝ ℝ) [∀ i, IsMarkovKernel (κ i)] (y : Fin d → ℝ) :
    unifPi.map (qfPi κ y) = Measure.pi fun i => κ i (y i) := by
  have : ∀ i, SigmaFinite (unif.map (qf (κ i (y i)))) := fun i => by
    rw [map_qf]
    infer_instance
  rw [unifPi, show qfPi κ y = fun u i => qf (κ i (y i)) (u i) from rfl,
    Measure.pi_map_pi fun i => (measurable_qf _).aemeasurable]
  congr 1
  funext i
  exact map_qf _

/-- **Marginals of the product quantile construction.** Let `K` be a kernel on `Fin d → ℝ` with
`K y = ⊗ᵢ κᵢ (yᵢ)` for Markov kernels `κᵢ`, `γ` finite on `β` and `b : β → Fin d → ℝ`
measurable. Then `(z, u) ↦ qfPi κ (b z) u` maps `γ ⊗ unifPi` to `K ∘ₘ γ.map b`. -/
theorem map_prod_unifPi_qfPi {β : Type*} [MeasurableSpace β] (κ : Fin d → Kernel ℝ ℝ)
    [∀ i, IsMarkovKernel (κ i)] (K : Kernel (Fin d → ℝ) (Fin d → ℝ))
    (hK : ∀ y, K y = Measure.pi fun i => κ i (y i)) (γ : Measure β) [IsFiniteMeasure γ]
    {b : β → Fin d → ℝ} (hb : Measurable b) :
    (γ.prod unifPi).map (fun z => qfPi κ (b z.1) z.2) = K ∘ₘ γ.map b := by
  have hm : Measurable fun z : β × (Fin d → ℝ) => qfPi κ (b z.1) z.2 :=
    (measurable_qfPi κ).comp ((hb.comp measurable_fst).prodMk measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs),
    Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_map (K.measurable_coe hs) hb]
  refine lintegral_congr fun x => ?_
  have hq : Measurable (qfPi κ (b x)) := (measurable_qfPi κ).comp measurable_prodMk_left
  rw [hK, ← map_qfPi κ (b x), Measure.map_apply hq hs]
  rfl

/-- **Pathwise contraction of the coordinatewise quantile coupling.** If every `κᵢ` is
CDF-shift-monotone, then `|qfPi κ y u - qfPi κ y' u|² ≤ |y - y'|²` for all `y, y', u`. -/
theorem sqDist_qfPi_le {κ : Fin d → Kernel ℝ ℝ} (hκ : ∀ i, CDFShiftMonotone (κ i))
    (y y' u : Fin d → ℝ) : sqDist (qfPi κ y u) (qfPi κ y' u) ≤ sqDist y y' :=
  Finset.sum_le_sum fun i _ =>
    sq_le_sq.2 (ProximalLogConcaveRate.abs_qf_sub_le_all (hκ i) (y i) (y' i) (u i))

/-- **Coupling transfer through a product of CDF-shift-monotone kernels.** Let `K` be a kernel on
`Fin d → ℝ` with `K y = ⊗ᵢ κᵢ (yᵢ)`, each `κᵢ` a CDF-shift-monotone Markov kernel on `ℝ`. If `γ`
is a finite coupling of `(ρ, μ)`, there is a finite coupling `γ'` of `(K ∘ₘ ρ, K ∘ₘ μ)` with
`∫⁻ φ(|x - y|²) dγ' ≤ ∫⁻ φ(|x - y|²) dγ` (measurable `φ` monotone on `[0, ∞)`). -/
theorem exists_coupling_pi (κ : Fin d → Kernel ℝ ℝ) [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, CDFShiftMonotone (κ i)) (K : Kernel (Fin d → ℝ) (Fin d → ℝ))
    (hK : ∀ y, K y = Measure.pi fun i => κ i (y i)) {ρ μ : Measure (Fin d → ℝ)}
    (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ] (h₁ : γ.map Prod.fst = ρ)
    (h₂ : γ.map Prod.snd = μ) {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : MonotoneOn φ (Ici 0)) :
    ∃ γ' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsFiniteMeasure γ' ∧
      γ'.map Prod.fst = K ∘ₘ ρ ∧ γ'.map Prod.snd = K ∘ₘ μ ∧
      ∫⁻ p, φ (sqDist p.1 p.2) ∂γ' ≤ ∫⁻ p, φ (sqDist p.1 p.2) ∂γ := by
  set G : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin d → ℝ) → (Fin d → ℝ) × (Fin d → ℝ) :=
    fun z => (qfPi κ z.1.1 z.2, qfPi κ z.1.2 z.2) with hGdef
  have hG : Measurable G :=
    ((measurable_qfPi κ).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      ((measurable_qfPi κ).comp (measurable_fst.snd.prodMk measurable_snd))
  refine ⟨(γ.prod unifPi).map G, by infer_instance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hG, ← h₁]
    exact map_prod_unifPi_qfPi κ K hK γ measurable_fst
  · rw [Measure.map_map measurable_snd hG, ← h₂]
    exact map_prod_unifPi_qfPi κ K hK γ measurable_snd
  · rw [lintegral_map (measurable_cost hφm) hG,
      lintegral_prod (fun z => φ (sqDist (G z).1 (G z).2))
        ((measurable_cost hφm).comp hG).aemeasurable]
    refine lintegral_mono fun p => ?_
    calc ∫⁻ u, φ (sqDist (G (p, u)).1 (G (p, u)).2) ∂unifPi
        ≤ ∫⁻ _u, φ (sqDist p.1 p.2) ∂(unifPi (d := d)) :=
          lintegral_mono fun u => hφ (mem_Ici.2 (sqDist_nonneg _ _))
            (mem_Ici.2 (sqDist_nonneg _ _)) (sqDist_qfPi_le hκ p.1 p.2 u)
      _ = φ (sqDist p.1 p.2) := by simp

/-! ### Separable potentials: the RGO kernel is a product -/

/-- **Separable potentials have integrable `exp ∘ (-f)`.** If `f x = ∑ᵢ gᵢ(xᵢ)` and every
`exp ∘ (-gᵢ)` is integrable on `ℝ`, then `exp ∘ (-f)` is integrable on `Fin d → ℝ`. -/
theorem integrable_exp_neg_sum {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hint : ∀ i, Integrable fun x => Real.exp (-g i x)) :
    Integrable fun x => Real.exp (-f x) := by
  have e : (fun x => Real.exp (-f x)) = fun x : Fin d → ℝ => ∏ i, Real.exp (-g i (x i)) := by
    funext x
    rw [hfg, ← Finset.sum_neg_distrib, Real.exp_sum]
  rw [e]
  exact Integrable.fintype_prod hint

/-- **The RGO kernel of a separable potential is a product.** If `f x = ∑ᵢ gᵢ(xᵢ)` with each
`gᵢ` measurable and `exp ∘ (-gᵢ)` integrable, and `η > 0`, then for every `y`:
`RGO_f(y) = ⊗ᵢ RGO_{gᵢ}(yᵢ)`, i.e.
`rgoKernelPi f η y = Measure.pi fun i => rgoKernel (g i) η (y i)`. -/
theorem rgoKernelPi_eq_pi {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hg : ∀ i, Measurable (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x)) {η : ℝ} (hη : 0 < η)
    (y : Fin d → ℝ) :
    rgoKernelPi f η y = Measure.pi fun i => rgoKernel (g i) η (y i) := by
  have hf : Measurable f := by
    have : f = fun x => ∑ i, g i (x i) := funext hfg
    rw [this]
    exact Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)
  have hexp : ∀ x : Fin d → ℝ, Real.exp (-f x - sqDist x y / (2 * η))
      = ∏ i, Real.exp (-g i (x i) - (x i - y i) ^ 2 / (2 * η)) := by
    intro x
    rw [← Real.exp_sum, hfg, sqDist, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_div]
  have hZ : rgoNormalizerPi f η y = ∏ i, rgoNormalizer (g i) η (y i) := by
    rw [rgoNormalizerPi]
    simp_rw [hexp]
    exact integral_fintype_prod_volume_eq_prod
      (fun i x => Real.exp (-g i x - (x - y i) ^ 2 / (2 * η)))
  have hdens : ∀ x, rgoDensityPi f η y x = ∏ i, rgoDensity (g i) η (y i) (x i) := by
    intro x
    rw [rgoDensityPi, hexp, hZ, ← Finset.prod_div_distrib]
    rfl
  rw [rgoKernelPi_apply hf (integrable_exp_neg_sum hfg hint) hη]
  simp_rw [hdens]
  rw [← pi_withDensity_ofReal (g := fun i => rgoDensity (g i) η (y i))
    (fun i => (integrable_rgo (hint i) hη (y i)).div_const _) (fun i x => rgoDensity_nonneg _ x)]
  congr 1
  funext i
  rw [rgoKernel_apply (hg i) (hint i) hη]

/-! ### The proximal sampler for separable convex potentials -/

/-- **Coupling non-expansiveness of the proximal kernel, separable convex `f`.** Let
`f x = ∑ᵢ gᵢ(xᵢ)` with each `gᵢ` convex on `ℝ` and `∫ e^{-gᵢ} < ∞`, and `η > 0`. For every finite
coupling `γ` of `(ρ, μ)` there is a finite coupling `γ'` of
`(proxKernelPi f η ∘ₘ ρ, proxKernelPi f η ∘ₘ μ)` with `∫⁻ φ(|x - y|²) dγ' ≤ ∫⁻ φ(|x - y|²) dγ`
(measurable `φ` monotone on `[0, ∞)`). -/
theorem exists_coupling_proxKernelPi_separable {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x)) {η : ℝ} (hη : 0 < η)
    {ρ μ : Measure (Fin d → ℝ)} (γ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ]
    (h₁ : γ.map Prod.fst = ρ) (h₂ : γ.map Prod.snd = μ) {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : MonotoneOn φ (Ici 0)) :
    ∃ γ' : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsFiniteMeasure γ' ∧
      γ'.map Prod.fst = proxKernelPi f η ∘ₘ ρ ∧ γ'.map Prod.snd = proxKernelPi f η ∘ₘ μ ∧
      ∫⁻ p, φ (sqDist p.1 p.2) ∂γ' ≤ ∫⁻ p, φ (sqDist p.1 p.2) ∂γ := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have := fun i => isMarkovKernel_rgoKernel (hg i) (hint i) hη
  obtain ⟨γ₁, hγ₁, a₁, b₁, c₁⟩ := exists_coupling_forwardKernelPi η γ h₁ h₂ hφm
  obtain ⟨γ₂, hγ₂, a₂, b₂, c₂⟩ := exists_coupling_pi (fun i => rgoKernel (g i) η)
    (fun i => cdfShiftMonotone_rgoKernel (hconv i) (hint i) hη) (rgoKernelPi f η)
    (rgoKernelPi_eq_pi hfg hg hint hη) γ₁ a₁ b₁ hφm hφ
  refine ⟨γ₂, hγ₂, ?_, ?_, c₂.trans c₁.le⟩
  · rw [proxKernelPi, ← Measure.comp_assoc]
    exact a₂
  · rw [proxKernelPi, ← Measure.comp_assoc]
    exact b₂

/-- **Couplings along the proximal chain, separable convex `f`.** Under the hypotheses of
`exists_coupling_proxKernelPi_separable`, let `π = targetPi f`, `ρ (k + 1) = proxKernelPi f η ∘ₘ
ρ k` and `γ₀` a finite coupling of `(ρ 0, π)`. Then for every `k` there is a finite coupling `γ`
of `(ρ k, π)` with `∫⁻ φ(|x - y|²) dγ ≤ ∫⁻ φ(|x - y|²) dγ₀`. -/
theorem exists_coupling_iteratePi {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x)) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) {φ : ℝ → ℝ≥0∞}
    (hφm : Measurable φ) (hφ : MonotoneOn φ (Ici 0)) (k : ℕ) :
    ∃ γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsFiniteMeasure γ ∧ γ.map Prod.fst = ρ k ∧
      γ.map Prod.snd = targetPi f ∧
      ∫⁻ p, φ (sqDist p.1 p.2) ∂γ ≤ ∫⁻ p, φ (sqDist p.1 p.2) ∂γ₀ := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have hf : Measurable f := by
    have : f = fun x => ∑ i, g i (x i) := funext hfg
    rw [this]
    exact Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)
  induction k with
  | zero => exact ⟨γ₀, inferInstance, h₁, h₂, le_rfl⟩
  | succ k ih =>
    obtain ⟨γ, hγ, a, b, c⟩ := ih
    obtain ⟨γ', hγ', a', b', c'⟩ :=
      exists_coupling_proxKernelPi_separable hfg hconv hint hη γ a b hφm hφ
    refine ⟨γ', hγ', by rw [hstep]; exact a', ?_, c'.trans c⟩
    rw [b', proxKernelPi_comp_targetPi hf (integrable_exp_neg_sum hfg hint) hη]

/-- **KL bound for the proximal sampler with a separable log-concave target on `Fin d → ℝ`.**
Let `f x = ∑ᵢ gᵢ(xᵢ)` with each `gᵢ` convex on `ℝ` and `∫ e^{-gᵢ} < ∞`, `π = targetPi f`,
`η > 0`, `ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k`, and `γ₀` any finite coupling of `(ρ 0, π)`.
Then for every `k`: `KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2η) dγ₀(x, y)`. -/
theorem klDiv_iteratePi_le_coupling {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ}
    (hfg : ∀ x, f x = ∑ i, g i (x i)) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x)) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi f) ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * η)) ∂γ₀ := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have hf : Measurable f := by
    have : f = fun x => ∑ i, g i (x i) := funext hfg
    rw [this]
    exact Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)
  set φ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r / (2 * η)) with hφdef
  have hφm : Measurable φ := by
    rw [hφdef]
    fun_prop
  have hφ : MonotoneOn φ (Ici 0) := fun a _ b _ hab =>
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hab (by positivity))
  obtain ⟨γ, hγ, a, b, c⟩ :=
    exists_coupling_iteratePi hfg hconv hint hη ρ hstep γ₀ h₁ h₂ hφm hφ k
  have : IsFiniteMeasure (ρ k) := a ▸ inferInstance
  rw [hstep]
  exact (ProximalRegularization.klDiv_proxKernelPi_comp_le_coupling hf
    (integrable_exp_neg_sum hfg hint) hη γ a b).trans c

end FormalizeSampling.ProximalLogConcavePi
