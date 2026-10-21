module

public import FormalizeSampling.Samplers.ProximalLogConcaveRateGeneralPi

/-!
# Rotation invariance of pathwise Lipschitz RGO representations

Status: **Verified** (no named hypotheses).

Let `U : Matrix (Fin d) (Fin d) ℝ` be orthogonal (`Uᵀ U = 1`). Lebesgue measure and the
Euclidean distance are invariant under `x ↦ U x`, so the RGO kernel of the rotated potential
`x ↦ h (U x)` is the push-forward of the RGO kernel of `h` (`rgoKernelPi_comp_orth`):

  `RGO_{h ∘ U}(y) = (RGO_h(U y)).map (x ↦ Uᵀ x)`.

Consequently a pathwise `1`-Lipschitz representation `G` of `RGO_h` gives one of `RGO_{h ∘ U}`,
namely `G'(y, ω) = Uᵀ G(U y, ω)` (`hasLipRep_rgoKernelPi_comp_orth`).

## Main results

* `hasLipRep_rgoKernelPi_comp_orth`: `HasLipRep` is preserved under orthogonal changes of
  coordinates of the potential.
* `hasLipRep_rgoKernelPi_rotated_separable_add_quadratic`: potentials
  `f x = ∑ᵢ gᵢ((U x)ᵢ) + λ |x|²/2 - |B x|²/2` with `gᵢ` convex, `∫ e^{-gᵢ} < ∞`, `U` orthogonal
  and `|B z|² ≤ λ |z|²` (separable in a rotated basis, plus a positive semidefinite quadratic).
* `klDiv_iteratePi_le_div_rotated_separable_add_quadratic`: the `1/k` KL rate
  `KL(ρ_{k+1} ‖ π) ≤ ∫ |x - y|² dγ₀ / (2 (k + 1) η)` of the proximal sampler for these targets.

## Not proved here

* Pathwise representations for general (not rotated-separable plus quadratic) convex potentials;
  the weak coupling that the `1/k` rate needs is
  `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingPi
open FormalizeSampling.RGOCouplingQuadraticPi FormalizeSampling.ProximalLogConcaveRateGeneralPi
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingRotationPi

variable {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ}

/-- An orthogonal matrix (`Uᵀ U = 1`) also satisfies `U Uᵀ = 1`. -/
theorem mul_transpose_eq_one (hU : Uᵀ * U = 1) : U * Uᵀ = 1 :=
  mul_eq_one_comm.1 hU

/-- The transpose of an orthogonal matrix is orthogonal. -/
theorem transpose_orth (hU : Uᵀ * U = 1) : Uᵀᵀ * Uᵀ = 1 := by
  rw [transpose_transpose]
  exact mul_transpose_eq_one hU

/-- `Uᵀ (U x) = x` for orthogonal `U`. -/
theorem transpose_mulVec_mulVec (hU : Uᵀ * U = 1) (x : Fin d → ℝ) : Uᵀ *ᵥ (U *ᵥ x) = x := by
  rw [mulVec_mulVec, hU, one_mulVec]

/-- Orthogonal matrices preserve the dot product. -/
theorem dot_mulVec_orth (hU : Uᵀ * U = 1) (a b : Fin d → ℝ) :
    (U *ᵥ a) ⬝ᵥ (U *ᵥ b) = a ⬝ᵥ b := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_mulVec_mulVec hU]

/-- Orthogonal matrices preserve the squared Euclidean distance. -/
theorem sqDist_mulVec_orth (hU : Uᵀ * U = 1) (a b : Fin d → ℝ) :
    sqDist (U *ᵥ a) (U *ᵥ b) = sqDist a b := by
  rw [sqDist_expand, sqDist_expand, dot_mulVec_orth hU, dot_mulVec_orth hU, dot_mulVec_orth hU]

/-- The measurable equivalence `x ↦ U x` of an orthogonal matrix (inverse `x ↦ Uᵀ x`). -/
noncomputable def orthEquiv (hU : Uᵀ * U = 1) : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) where
  toFun x := U *ᵥ x
  invFun x := Uᵀ *ᵥ x
  left_inv x := transpose_mulVec_mulVec hU x
  right_inv x := by
    simpa using transpose_mulVec_mulVec (transpose_orth hU) x
  measurable_toFun := (continuous_mulVec U).measurable
  measurable_invFun := (continuous_mulVec Uᵀ).measurable

/-- `orthEquiv hU x = U x`. -/
theorem orthEquiv_apply (hU : Uᵀ * U = 1) (x : Fin d → ℝ) : orthEquiv hU x = U *ᵥ x := rfl

/-- `x ↦ U x` preserves Lebesgue measure for orthogonal `U` (`|det U| = 1`). -/
theorem measurePreserving_orth (hU : Uᵀ * U = 1) :
    MeasurePreserving (orthEquiv hU) volume volume := by
  have hdet : U.det * U.det = 1 := by
    have := congrArg det hU
    rwa [det_mul, det_transpose, det_one] at this
  have habs : |U.det| = 1 := by
    have h2 : |U.det| * |U.det| = 1 := by rw [← abs_mul, hdet, abs_one]
    nlinarith [abs_nonneg U.det]
  have hne : U.det ≠ 0 := fun h => by simp [h] at hdet
  refine ⟨(orthEquiv hU).measurable, ?_⟩
  have e : (⇑(orthEquiv hU)) = ⇑(toLin' U) := funext fun x => (toLin'_apply U x).symm
  rw [e, Real.map_matrix_volume_pi_eq_smul_volume_pi hne, abs_inv, habs, inv_one,
    ENNReal.ofReal_one, one_smul]

variable {h : (Fin d → ℝ) → ℝ}

/-- `x ↦ e^{-h(U x)}` is integrable when `x ↦ e^{-h x}` is. -/
theorem integrable_exp_neg_comp_orth (hU : Uᵀ * U = 1) (hh : Measurable h)
    (hint : Integrable fun x => Real.exp (-h x)) :
    Integrable fun x => Real.exp (-h (U *ᵥ x)) :=
  ((measurePreserving_orth hU).integrable_comp
    (hh.neg.exp.aestronglyMeasurable)).2 hint

/-- The RGO normaliser is rotation invariant: `Z_{h ∘ U}(y) = Z_h(U y)`. -/
theorem rgoNormalizerPi_comp_orth (hU : Uᵀ * U = 1) (η : ℝ) (y : Fin d → ℝ) :
    rgoNormalizerPi (fun x => h (U *ᵥ x)) η y = rgoNormalizerPi h η (U *ᵥ y) := by
  unfold rgoNormalizerPi
  have := (measurePreserving_orth hU).integral_comp'
    (fun x => Real.exp (-h x - sqDist x (U *ᵥ y) / (2 * η)))
  simp only [orthEquiv_apply, sqDist_mulVec_orth hU] at this
  exact this

/-- The RGO density is rotation invariant: `p_{h ∘ U}(y, x) = p_h(U y, U x)`. -/
theorem rgoDensityPi_comp_orth (hU : Uᵀ * U = 1) (η : ℝ) (y x : Fin d → ℝ) :
    rgoDensityPi (fun x => h (U *ᵥ x)) η y x = rgoDensityPi h η (U *ᵥ y) (U *ᵥ x) := by
  unfold rgoDensityPi
  rw [rgoNormalizerPi_comp_orth hU, sqDist_mulVec_orth hU]

/-- **Rotation of the RGO kernel.** For orthogonal `U`:
`RGO_{h ∘ U}(y) = (RGO_h(U y)).map (x ↦ Uᵀ x)`. -/
theorem rgoKernelPi_comp_orth (hU : Uᵀ * U = 1) (hh : Measurable h)
    (hint : Integrable fun x => Real.exp (-h x)) {η : ℝ} (hη : 0 < η) (y : Fin d → ℝ) :
    rgoKernelPi (fun x => h (U *ᵥ x)) η y
      = (rgoKernelPi h η (U *ᵥ y)).map fun x => Uᵀ *ᵥ x := by
  have hhU : Measurable fun x => h (U *ᵥ x) := hh.comp (continuous_mulVec U).measurable
  rw [rgoKernelPi_apply hhU (integrable_exp_neg_comp_orth hU hh hint) hη,
    rgoKernelPi_apply hh hint hη]
  ext s hs
  have hT : Measurable fun x : Fin d → ℝ => Uᵀ *ᵥ x := (continuous_mulVec Uᵀ).measurable
  rw [Measure.map_apply hT hs, withDensity_apply _ hs, withDensity_apply _ (hT hs)]
  simp_rw [rgoDensityPi_comp_orth hU]
  have := (measurePreserving_orth hU).setLIntegral_comp_emb
    (orthEquiv hU).measurableEmbedding
    (fun x => ENNReal.ofReal (rgoDensityPi h η (U *ᵥ y) x)) s
  simp only [orthEquiv_apply] at this
  rw [this]
  congr 2
  ext x
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [orthEquiv_apply, transpose_mulVec_mulVec hU]
  · intro hx
    exact ⟨Uᵀ *ᵥ x, hx, by
      rw [orthEquiv_apply, mulVec_mulVec, mul_transpose_eq_one hU, one_mulVec]⟩

/-- **Rotation invariance of `HasLipRep`.** If `rgoKernelPi h η` has a pathwise `1`-Lipschitz
representation and `U` is orthogonal, so does the RGO kernel of `f = h ∘ U`. -/
theorem hasLipRep_rgoKernelPi_comp_orth {f : (Fin d → ℝ) → ℝ} (hU : Uᵀ * U = 1)
    (hfU : ∀ x, f x = h (U *ᵥ x)) (hh : Measurable h)
    (hint : Integrable fun x => Real.exp (-h x)) {η : ℝ} (hη : 0 < η)
    (hrep : HasLipRep (rgoKernelPi h η)) : HasLipRep (rgoKernelPi f η) := by
  obtain rfl : f = fun x => h (U *ᵥ x) := funext hfU
  obtain ⟨Ω, _, P, G, hP, hG, hGK, hlip⟩ := hrep
  have hU' : Measurable fun x : Fin d → ℝ => U *ᵥ x := (continuous_mulVec U).measurable
  have hT : Measurable fun x : Fin d → ℝ => Uᵀ *ᵥ x := (continuous_mulVec Uᵀ).measurable
  refine ⟨Ω, inferInstance, P, fun y ω => Uᵀ *ᵥ G (U *ᵥ y) ω, hP, ?_, fun y => ?_,
    fun y y' ω => ?_⟩
  · exact hT.comp (hG.comp ((hU'.comp measurable_fst).prodMk measurable_snd))
  · have hGy : Measurable (G (U *ᵥ y)) := hG.comp (measurable_const.prodMk measurable_id)
    rw [rgoKernelPi_comp_orth hU hh hint hη, ← hGK, Measure.map_map hT hGy]
    rfl
  · calc sqDist (Uᵀ *ᵥ G (U *ᵥ y) ω) (Uᵀ *ᵥ G (U *ᵥ y') ω)
        = sqDist (G (U *ᵥ y) ω) (G (U *ᵥ y') ω) := sqDist_mulVec_orth (transpose_orth hU) _ _
      _ ≤ sqDist (U *ᵥ y) (U *ᵥ y') := hlip _ _ _
      _ = sqDist y y' := sqDist_mulVec_orth hU y y'

/-- **Rotated separable plus quadratic potentials.** Let `U` be orthogonal, `gᵢ` convex with
`∫ e^{-gᵢ} < ∞`, `λ ≥ 0`, `|B z|² ≤ λ |z|²` and `f x = ∑ᵢ gᵢ((U x)ᵢ) + λ |x|²/2 - |B x|²/2`.
Then `rgoKernelPi f η` has a pathwise `1`-Lipschitz representation for every `η > 0`. -/
theorem hasLipRep_rgoKernelPi_rotated_separable_add_quadratic {k : ℕ}
    {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ} {B : Matrix (Fin k) (Fin d) ℝ} {lam : ℝ}
    (hU : Uᵀ * U = 1) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x))
    (hf : ∀ x, f x = ∑ i, g i ((U *ᵥ x) i) + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2)
    (hl : 0 ≤ lam) (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) {η : ℝ} (hη : 0 < η) :
    HasLipRep (rgoKernelPi f η) := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have hsm : Measurable fun z : Fin d → ℝ => ∑ i, g i (z i) :=
    Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)
  have hsint := ProximalLogConcavePi.integrable_exp_neg_sum
    (f := fun z : Fin d → ℝ => ∑ i, g i (z i)) (fun z => rfl) hint
  have hηq : 0 < innerStep η lam := by unfold innerStep; positivity
  have hhm : Measurable fun x => ∑ i, g i ((U *ᵥ x) i) :=
    hsm.comp (continuous_mulVec U).measurable
  refine hasLipRep_rgoKernelPi_add_quadratic hhm
    (integrable_exp_neg_comp_orth hU hsm hsint) hf hl hB hη ?_
  exact hasLipRep_rgoKernelPi_comp_orth hU (fun x => rfl) hsm hsint hηq
    (hasLipRep_rgoKernelPi_separable (fun z => rfl) hconv hint hηq)

/-- **`1/k` KL rate for rotated separable plus quadratic potentials.** With `f` as in
`hasLipRep_rgoKernelPi_rotated_separable_add_quadratic`, iterates
`ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k` and a finite coupling `γ₀` of `(ρ 0, π)`:
`KL(ρ (k + 1) ‖ π) ≤ ∫⁻ |x - y|² / (2 (k + 1) η) dγ₀(x, y)`. -/
theorem klDiv_iteratePi_le_div_rotated_separable_add_quadratic {k' : ℕ}
    {f : (Fin d → ℝ) → ℝ} {g : Fin d → ℝ → ℝ} {B : Matrix (Fin k') (Fin d) ℝ} {lam : ℝ}
    (hU : Uᵀ * U = 1) (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x))
    (hf : ∀ x, f x = ∑ i, g i ((U *ᵥ x) i) + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2)
    (hl : 0 ≤ lam) (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) {η : ℝ} (hη : 0 < η)
    (ρ : ℕ → Measure (Fin d → ℝ)) (hstep : ∀ k, ρ (k + 1) = proxKernelPi f η ∘ₘ ρ k)
    (γ₀ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) [IsFiniteMeasure γ₀]
    (h₁ : γ₀.map Prod.fst = ρ 0) (h₂ : γ₀.map Prod.snd = targetPi f) (k : ℕ) :
    klDiv (ρ (k + 1)) (targetPi f)
      ≤ ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2 / (2 * ((k : ℝ) + 1) * η)) ∂γ₀ := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have hsm : Measurable fun z : Fin d → ℝ => ∑ i, g i (z i) :=
    Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)
  have hsint := ProximalLogConcavePi.integrable_exp_neg_sum
    (f := fun z : Fin d → ℝ => ∑ i, g i (z i)) (fun z => rfl) hint
  have hhm : Measurable fun x => ∑ i, g i ((U *ᵥ x) i) :=
    hsm.comp (continuous_mulVec U).measurable
  have hhint := integrable_exp_neg_comp_orth hU hsm hsint
  exact klDiv_iteratePi_le_div_of_hasLipRep (measurable_of_quad hhm hf)
    (integrable_of_quad hhm hhint hf hB) hη
    (hasLipRep_rgoKernelPi_rotated_separable_add_quadratic hU hconv hint hf hl hB hη)
    ρ hstep γ₀ h₁ h₂ k

end FormalizeSampling.RGOCouplingRotationPi
