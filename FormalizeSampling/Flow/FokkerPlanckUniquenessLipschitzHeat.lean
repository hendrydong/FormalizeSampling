module

public import FormalizeSampling.Flow.FokkerPlanckUniqueness

/-!
# Gaussian smoothing of bounded `C²` functions (no compact support)

Status: **Verified.** Infrastructure for the uniqueness proof of the weak Fokker–Planck equation
with globally Lipschitz drift (`Flow/FokkerPlanckUniquenessLipschitz.lean`). The dual test
functions used there are Gaussian smoothings of non-compactly supported functions, so the
compact-support lemmas of `Flow/FokkerPlanckUniquenessHeat.lean` are extended to the class
`BddC2` of `C²` functions `f : ℝᵈ → ℝ` with `f`, `Df` and `D²f` bounded.

## Main results

* `hasFDerivAt_heatOp_of_bdd`, `continuous_heatOp_of_bdd`: differentiation under the Gaussian
  integral for `C¹` functions with bounded derivative (any normed target).
* `bddC2_heatOp`: `heatOp σ f ∈ BddC2` for `f ∈ BddC2`, with
  `fderiv (heatOp σ f) = heatOp σ (fderiv f)` (`fderiv_heatOp_of_bdd`) and the sup bounds
  `|heatOp σ f| ≤ sup|f|`, `‖D heatOp σ f‖ ≤ sup‖Df‖`.
* `integral_coord_mul_eq_of_bdd`, `integral_coord_mul_comp_of_bdd`: the Gaussian Stein identity
  `E[Zᵢ g(x + σ Z)] = σ E[∂ᵢ g(x + σ Z)]` for bounded `C¹` `g` with bounded `∂ᵢ g`.
* `integral_fderiv_apply_eq_laplacian`: the **heat identity**
  `E[Df(x + σ Z) Z] = σ Δ(heatOp σ f)(x)` for `f ∈ BddC2` (Stein in each coordinate plus
  `laplacian_heatOp_of_bdd`).
* `bddC2_comp_add_smul`: `y ↦ Θ(y + τ w(y))` is in `BddC2` when `Θ ∈ BddC2` and `w` is `C²` with
  bounded first and second derivatives, with `‖D(Θ ∘ (id + τ w))‖ ≤ G (1 + |τ| L)`
  (`norm_fderiv_comp_add_smul_le`).
* `abs_heatOp_sub_le`: `|heatOp a Θ - Θ| ≤ G a d` for `‖DΘ‖ ≤ G`, `a ≥ 0`.

## Not proved here

* Only the first two derivatives are tracked; no `C^k_b` statement for `k ≥ 3` and no smoothing
  estimate for merely bounded data (the Stein identity is used with a bounded derivative).
* The second-derivative bound of a composition is qualitative (from
  `norm_iteratedFDeriv_comp_le`); only the first-derivative bound is quantitative.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Differentiation under the Gaussian integral for bounded data -/

/-- For a continuous `f` with `‖f‖ ≤ M` (any normed target), `heatOp σ f` is continuous. -/
theorem continuous_heatOp_of_bdd {f : (Fin d → ℝ) → E} (hf : Continuous f) {M : ℝ}
    (hM : ∀ y, ‖f y‖ ≤ M) (σ : ℝ) : Continuous (heatOp σ f) :=
  continuous_of_dominated (bound := fun _ => M)
    (fun x => (hf.comp (by fun_prop)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun z => hM _)
    (integrable_const M) (ae_of_all _ fun z => hf.comp (by fun_prop))

omit [NormedSpace ℝ E] in
/-- A continuous bounded `f` composed with `z ↦ x + σ z` is `stdGauss`-integrable. -/
theorem integrable_comp_shift_of_bdd {f : (Fin d → ℝ) → E} (hf : Continuous f) {M : ℝ}
    (hM : ∀ y, ‖f y‖ ≤ M) (σ : ℝ) (x : Fin d → ℝ) :
    Integrable (fun z => f (x + σ • z)) stdGauss :=
  Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable M (ae_of_all _ fun z => hM _)

/-- `‖heatOp σ f x‖ ≤ M` if `‖f‖ ≤ M` (any normed target). -/
theorem norm_heatOp_le {f : (Fin d → ℝ) → E} {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) (σ : ℝ)
    (x : Fin d → ℝ) : ‖heatOp σ f x‖ ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := stdGauss) (f := fun z => f (x + σ • z))
    (C := M) (ae_of_all _ fun z => hM _)
  simpa [heatOp] using h

/-- **Differentiation under the Gaussian integral (bounded data).** For `f` of class `C¹`
(any complete target) with `‖f‖ ≤ M` and `‖Df‖ ≤ C`, `heatOp σ f` has derivative
`heatOp σ (Df)` at every point. -/
theorem hasFDerivAt_heatOp_of_bdd {f : (Fin d → ℝ) → E} (hf : ContDiff ℝ 1 f) {M C : ℝ}
    (hM : ∀ y, ‖f y‖ ≤ M) (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C) (σ : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (heatOp σ f) (heatOp σ (fderiv ℝ f) x) x := by
  have hf' : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun y z => fderiv ℝ f (y + σ • z)) univ_mem
    (Eventually.of_forall fun y => (hf.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_shift_of_bdd hf.continuous hM σ x)
    (hf'.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z y _ => hC _) (integrable_const C)
    (ae_of_all _ fun z y _ => ?_)
  exact (hfd (y + σ • z)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const (σ • z))

/-! ### The class `BddC2` -/

/-- `f : ℝᵈ → ℝ` is `C²` with `f`, `Df` and `D²f` bounded. -/
def BddC2 (f : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ (∃ M, ∀ y, ‖f y‖ ≤ M) ∧ (∃ M, ∀ y, ‖fderiv ℝ f y‖ ≤ M) ∧
    ∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M

/-- `C²` functions with compact support are in `BddC2`. -/
theorem BddC2.of_testFunction {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : BddC2 f := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  refine ⟨hf, hf.continuous.bounded_above_of_compact_support hfc,
    (hf.continuous_fderiv two_ne_zero).bounded_above_of_compact_support (hfc.fderiv (𝕜 := ℝ)),
    (h1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((hfc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))⟩

/-- For `f ∈ BddC2`, `D(heatOp σ f) = heatOp σ (Df)`. -/
theorem fderiv_heatOp_of_bdd {f : (Fin d → ℝ) → ℝ} (hf : BddC2 f) (σ : ℝ) :
    fderiv ℝ (heatOp σ f) = heatOp σ (fderiv ℝ f) := by
  obtain ⟨h2, ⟨M, hM⟩, ⟨M1, hM1⟩, -⟩ := hf
  funext x
  exact (hasFDerivAt_heatOp_of_bdd (h2.of_le (by norm_num)) hM hM1 σ x).fderiv

/-- `BddC2` is preserved by Gaussian smoothing. -/
theorem bddC2_heatOp {f : (Fin d → ℝ) → ℝ} (hf : BddC2 f) (σ : ℝ) :
    BddC2 (heatOp σ f) := by
  obtain ⟨h2, ⟨M, hM⟩, ⟨M1, hM1⟩, ⟨M2, hM2⟩⟩ := hf
  have h1 : ContDiff ℝ 1 f := h2.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := h2.fderiv_right (m := 1) (by norm_num)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ f)) := hD.continuous_fderiv one_ne_zero
  have e1 : fderiv ℝ (heatOp σ f) = heatOp σ (fderiv ℝ f) :=
    funext fun x => (hasFDerivAt_heatOp_of_bdd h1 hM hM1 σ x).fderiv
  have e2 : fderiv ℝ (heatOp σ (fderiv ℝ f)) = heatOp σ (fderiv ℝ (fderiv ℝ f)) :=
    funext fun x => (hasFDerivAt_heatOp_of_bdd hD hM1 hM2 σ x).fderiv
  have hc2 : ContDiff ℝ 2 (heatOp σ f) := by
    have h2' : (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
    rw [h2']
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨heatOp σ (fderiv ℝ f), ?_,
      fun x => hasFDerivAt_heatOp_of_bdd h1 hM hM1 σ x⟩
    refine contDiff_one_iff_hasFDerivAt.2 ⟨heatOp σ (fderiv ℝ (fderiv ℝ f)), ?_,
      fun x => hasFDerivAt_heatOp_of_bdd hD hM1 hM2 σ x⟩
    exact continuous_heatOp_of_bdd hDD hM2 σ
  refine ⟨hc2, ⟨M, norm_heatOp_le hM σ⟩, ⟨M1, fun x => ?_⟩, ⟨M2, fun x => ?_⟩⟩
  · rw [e1]; exact norm_heatOp_le hM1 σ x
  · rw [e1, e2]; exact norm_heatOp_le hM2 σ x

/-- Partial derivatives commute with Gaussian smoothing on `BddC2`. -/
theorem partialDeriv_heatOp_of_bdd {f : (Fin d → ℝ) → ℝ} (hf : BddC2 f) (σ : ℝ)
    (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (heatOp σ f) x = heatOp σ (partialDeriv i f) x := by
  have hf2 := hf
  obtain ⟨h2, -, ⟨M1, hM1⟩, -⟩ := hf2
  have hf' : Continuous (fderiv ℝ f) := h2.continuous_fderiv two_ne_zero
  rw [partialDeriv, fderiv_heatOp_of_bdd hf, heatOp,
    ContinuousLinearMap.integral_apply (integrable_comp_shift_of_bdd hf' hM1 σ x)]
  rfl

/-- The partial derivative of `f ∈ BddC2` is `C¹`, bounded, with bounded derivative. -/
theorem bddC2_partialDeriv {f : (Fin d → ℝ) → ℝ} (hf : BddC2 f) (i : Fin d) :
    ContDiff ℝ 1 (partialDeriv i f) ∧ (∃ M, ∀ y, ‖partialDeriv i f y‖ ≤ M) ∧
      ∃ M, ∀ y, ‖fderiv ℝ (partialDeriv i f) y‖ ≤ M := by
  obtain ⟨h2, -, ⟨M1, hM1⟩, ⟨M2, hM2⟩⟩ := hf
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := h2.fderiv_right (m := 1) (by norm_num)
  have he : ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
    rw [Pi.norm_single]; simp
  set A : (((Fin d → ℝ) →L[ℝ] ℝ)) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ) : Fin d → ℝ)
  have hA : ‖A‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => by
      simpa [A] using (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg L)))
  have e : partialDeriv i f = fun y => A (fderiv ℝ f y) := rfl
  have hfd : Differentiable ℝ (fderiv ℝ f) := hD.differentiable one_ne_zero
  refine ⟨?_, ⟨M1, fun y => ?_⟩, ⟨M2, fun y => ?_⟩⟩
  · rw [e]; exact A.contDiff.comp hD
  · rw [e]
    exact (A.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hA).trans (hM1 y))
  · rw [e, show (fun y => A (fderiv ℝ f y)) = A ∘ fderiv ℝ f from rfl,
      fderiv_comp y A.differentiableAt (hfd y), A.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans (hM2 y)

/-- The Laplacian commutes with Gaussian smoothing on `BddC2`. -/
theorem laplacian_heatOp_of_bdd {f : (Fin d → ℝ) → ℝ} (hf : BddC2 f) (σ : ℝ)
    (x : Fin d → ℝ) : laplacian (heatOp σ f) x = heatOp σ (laplacian f) x := by
  have hstep : ∀ i : Fin d, partialDeriv i (partialDeriv i (heatOp σ f)) x =
      heatOp σ (partialDeriv i (partialDeriv i f)) x := by
    intro i
    obtain ⟨hp1, ⟨Mp, hMp⟩, ⟨Mp', hMp'⟩⟩ := bddC2_partialDeriv hf i
    have e : partialDeriv i (heatOp σ f) = heatOp σ (partialDeriv i f) :=
      funext (partialDeriv_heatOp_of_bdd hf σ i)
    rw [e, partialDeriv, (hasFDerivAt_heatOp_of_bdd hp1 hMp hMp' σ x).fderiv, heatOp,
      ContinuousLinearMap.integral_apply (integrable_comp_shift_of_bdd
        (hp1.continuous_fderiv one_ne_zero) hMp' σ x)]
    rfl
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun z => partialDeriv i (partialDeriv i f) (x + σ • z)) stdGauss := by
    intro i _
    obtain ⟨hp1, -, ⟨Mp', hMp'⟩⟩ := bddC2_partialDeriv hf i
    exact integrable_comp_shift_of_bdd
      ((hp1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (fun y => by
        have := (ContinuousLinearMap.le_opNorm (fderiv ℝ (partialDeriv i f) y)
          (Pi.single i 1)).trans (mul_le_of_le_one_right (norm_nonneg _)
            (by rw [Pi.norm_single]; simp))
        exact this.trans (hMp' y)) σ x
  simp only [laplacian, hstep, heatOp]
  rw [← integral_finsetSum _ hint]

/-! ### Gaussian Stein identity and the heat identity for bounded data -/

/-- **Stein identity, bounded data.** For `φ : ℝᵈ → ℝ` of class `C¹` with `|φ| ≤ M` and
`|∂ᵢφ| ≤ M'`, `E[Zᵢ φ(Z)] = E[∂ᵢφ(Z)]` for `Z ∼ N(0, I_d)`. (Same proof as
`GaussianStein.integral_coord_mul_eq_integral_partialDeriv`, with the bounds replacing compact
support.) -/
theorem integral_coord_mul_eq_of_bdd {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) {M M' : ℝ}
    (hM : ∀ y, |φ y| ≤ M) (i : Fin d) (hM' : ∀ y, |partialDeriv i φ y| ≤ M') :
    ∫ z, z i * φ z ∂stdGauss = ∫ z, partialDeriv i φ z ∂stdGauss := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  set μ : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  set P : Measure (Fin (n + 1) → ℝ) := Measure.pi fun _ => μ
  set Q : Measure (Fin n → ℝ) := Measure.pi fun _ => μ
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).symm
  have fub : ∀ F : (Fin (n + 1) → ℝ) → ℝ, Integrable F P →
      ∫ z, F z ∂P = ∫ y, ∫ t, F (Fin.insertNth i t y) ∂μ ∂Q := by
    intro F hF
    rw [← he.integral_comp' F, integral_prod_symm]
    · rfl
    · exact (he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  have hdiff := hφ.differentiable one_ne_zero
  have hcont' : Continuous (partialDeriv i φ) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint1 : Integrable (fun z : Fin (n + 1) → ℝ => z i * φ z) P := by
    refine ((integrable_coord (d := n + 1) i).abs.mul_const M).mono'
      ((continuous_apply i).mul hφ.continuous).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM z) (abs_nonneg _)
  have hint2 : Integrable (partialDeriv i φ) P :=
    Integrable.of_bound hcont'.aestronglyMeasurable M' (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hM' z)
  show ∫ z, z i * φ z ∂P = ∫ z, partialDeriv i φ z ∂P
  rw [fub _ hint1, fub _ hint2]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hder : ∀ t, HasDerivAt (fun s => φ (Fin.insertNth i s y))
      (partialDeriv i φ (Fin.insertNth i t y)) t :=
    fun t => (hdiff _).hasFDerivAt.comp_hasDerivAt t
      (GaussianStein.hasDerivAt_insertNth i y t)
  have := GaussianStein.integral_sub_mul_eq_of_bounded (m := 0) (v := 1) hder
    ⟨M, fun t => by simpa using hM _⟩ ⟨M', fun t => by simpa using hM' _⟩
  simpa using this

/-- **Scaled Stein identity, bounded data.** For `g` of class `C¹` with `|g| ≤ M`,
`|∂ᵢ g| ≤ M'`, `w : ℝᵈ` and `σ : ℝ`: `E[Zᵢ g(w + σ Z)] = σ E[∂ᵢ g(w + σ Z)]`. -/
theorem integral_coord_mul_comp_of_bdd {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ 1 g) {M M' : ℝ}
    (hM : ∀ y, |g y| ≤ M) (i : Fin d) (hM' : ∀ y, |partialDeriv i g y| ≤ M')
    (w : Fin d → ℝ) (σ : ℝ) :
    ∫ z, z i * g (w + σ • z) ∂stdGauss = σ * ∫ z, partialDeriv i g (w + σ • z) ∂stdGauss := by
  have hh : ContDiff ℝ 1 (fun z => g (w + σ • z)) :=
    hg.comp (contDiff_const.add (contDiff_id.const_smul σ))
  have hpd : ∀ z, partialDeriv i (fun z => g (w + σ • z)) z =
      σ * partialDeriv i g (w + σ • z) := by
    intro z
    have hA : HasFDerivAt (fun z : Fin d → ℝ => w + σ • z)
        (σ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) z :=
      ((hasFDerivAt_id z).const_smul σ).const_add w
    have := ((hg.differentiable one_ne_zero _).hasFDerivAt.comp z hA).fderiv
    simp only [partialDeriv]
    rw [show (fun z => g (w + σ • z)) = g ∘ (fun z => w + σ • z) from rfl, this]
    simp
  have key := integral_coord_mul_eq_of_bdd hh (fun z => hM _) i
    (M' := |σ| * M') (fun z => by
      rw [hpd, abs_mul]; exact mul_le_mul_of_nonneg_left (hM' _) (abs_nonneg _))
  rw [key]
  simp_rw [hpd]
  exact integral_const_mul _ _

/-- `E‖Z‖ ≤ d` for `Z ∼ N(0, I_d)` (sup norm, `‖z‖ ≤ ∑ᵢ |zᵢ|`, `E|Zᵢ| ≤ 1`). -/
theorem integral_norm_stdGauss_le : ∫ z, ‖z‖ ∂(stdGauss (d := d)) ≤ d := by
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun z : Fin d → ℝ => |z i|) stdGauss := fun i _ => (integrable_coord i).abs
  calc ∫ z, ‖z‖ ∂(stdGauss (d := d)) ≤ ∫ z, ∑ i, |z i| ∂(stdGauss (d := d)) := by
        refine integral_mono integrable_norm_stdGauss (integrable_finsetSum _ hint) fun z => ?_
        refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2
          fun i => ?_
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ = ∑ i, ∫ z, |z i| ∂(stdGauss (d := d)) := integral_finsetSum _ hint
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => integral_abs_coord_le_one i
    _ = d := by simp

/-- **Heat identity.** For `f ∈ BddC2` and `σ : ℝ`,
`E[Df(x + σ Z) Z] = σ Δ(heatOp σ f)(x)`, `Z ∼ N(0, I_d)`. This is the heat equation in the form
used by the dual test functions: `∂_σ heatOp σ f = σ Δ heatOp σ f`. -/
theorem integral_fderiv_apply_eq_laplacian {f : (Fin d → ℝ) → ℝ} (hf : BddC2 f) (σ : ℝ)
    (x : Fin d → ℝ) :
    ∫ z, fderiv ℝ f (x + σ • z) z ∂stdGauss = σ * laplacian (heatOp σ f) x := by
  have hpd : ∀ i, ContDiff ℝ 1 (partialDeriv i f) ∧ (∃ M, ∀ y, |partialDeriv i f y| ≤ M) ∧
      ∃ M, ∀ y, |partialDeriv i (partialDeriv i f) y| ≤ M := by
    intro i
    obtain ⟨h1, ⟨M, hM⟩, ⟨M', hM'⟩⟩ := bddC2_partialDeriv hf i
    refine ⟨h1, ⟨M, fun y => by simpa [Real.norm_eq_abs] using hM y⟩, ⟨M', fun y => ?_⟩⟩
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact (mul_le_of_le_one_right (norm_nonneg _) (by rw [Pi.norm_single]; simp)).trans (hM' y)
  have e1 : ∀ z, fderiv ℝ f (x + σ • z) z = ∑ i, z i * partialDeriv i f (x + σ • z) := by
    intro z
    rw [← dotProduct_grad]
    rfl
  have hint1 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun z => z i * partialDeriv i f (x + σ • z)) stdGauss := by
    intro i _
    obtain ⟨h1, ⟨M, hM⟩, -⟩ := hpd i
    refine ((integrable_coord i).abs.mul_const M).mono'
      ((continuous_apply i).mul (h1.continuous.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun z => partialDeriv i (partialDeriv i f) (x + σ • z)) stdGauss := by
    intro i _
    obtain ⟨h1, -, ⟨M', hM'⟩⟩ := hpd i
    exact integrable_comp_shift_of_bdd
      ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (fun y => by rw [Real.norm_eq_abs]; exact hM' y) σ x
  simp_rw [e1]
  rw [integral_finsetSum _ hint1, laplacian_heatOp_of_bdd hf, heatOp]
  simp only [laplacian]
  rw [integral_finsetSum _ hint2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, ⟨M, hM⟩, ⟨M', hM'⟩⟩ := hpd i
  exact integral_coord_mul_comp_of_bdd h1 hM i hM' x σ

/-! ### Composition with a near-identity map -/

/-- `‖D²f(x)‖ = ‖iteratedFDeriv ℝ 2 f x‖`. -/
theorem norm_fderiv_fderiv_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (Fin d → ℝ) → F) (x : Fin d → ℝ) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- The derivative of `y ↦ y + τ w(y)` is `id + τ Dw(y)`. -/
theorem fderiv_add_smul {w : (Fin d → ℝ) → Fin d → ℝ} (hw : Differentiable ℝ w) (τ : ℝ) :
    fderiv ℝ (fun y => y + τ • w y) =
      fun y => ContinuousLinearMap.id ℝ (Fin d → ℝ) + τ • fderiv ℝ w y := by
  funext y
  exact ((hasFDerivAt_id y).add ((hw y).hasFDerivAt.const_smul τ)).fderiv

/-- `‖id + τ Dw(y)‖ ≤ 1 + |τ| L` if `‖Dw‖ ≤ L`. -/
theorem norm_id_add_smul_le {A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L : ℝ} (hA : ‖A‖ ≤ L)
    (τ : ℝ) : ‖ContinuousLinearMap.id ℝ (Fin d → ℝ) + τ • A‖ ≤ 1 + |τ| * L := by
  refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)

/-- **Gradient bound for `Θ ∘ (id + τ w)`.** If `‖DΘ‖ ≤ G` and `‖Dw‖ ≤ L` then
`‖D(y ↦ Θ(y + τ w(y)))‖ ≤ G (1 + |τ| L)`. -/
theorem norm_fderiv_comp_add_smul_le {Θ : (Fin d → ℝ) → ℝ} (hΘ : Differentiable ℝ Θ) {G : ℝ}
    (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) {w : (Fin d → ℝ) → Fin d → ℝ} (hw : Differentiable ℝ w)
    {L : ℝ} (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (τ : ℝ) (y : Fin d → ℝ) :
    ‖fderiv ℝ (fun y => Θ (y + τ • w y)) y‖ ≤ G * (1 + |τ| * L) := by
  have hF : HasFDerivAt (fun y => y + τ • w y)
      (ContinuousLinearMap.id ℝ (Fin d → ℝ) + τ • fderiv ℝ w y) y :=
    (hasFDerivAt_id y).add ((hw y).hasFDerivAt.const_smul τ)
  rw [show (fun y => Θ (y + τ • w y)) = Θ ∘ (fun y => y + τ • w y) from rfl,
    ((hΘ _).hasFDerivAt.comp y hF).fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul (hG _) (norm_id_add_smul_le (hL y) τ) (norm_nonneg _)
    ((norm_nonneg _).trans (hG 0))

/-- **`BddC2` is preserved by `Θ ↦ Θ ∘ (id + τ w)`** when `w` is `C²` with `‖Dw‖ ≤ L` and
`‖D²w‖ ≤ M` (the second-derivative bound is qualitative, via `norm_iteratedFDeriv_comp_le`). -/
theorem bddC2_comp_add_smul {Θ : (Fin d → ℝ) → ℝ} (hΘ : BddC2 Θ)
    {w : (Fin d → ℝ) → Fin d → ℝ} (hw : ContDiff ℝ 2 w) {L M : ℝ}
    (hL : ∀ y, ‖fderiv ℝ w y‖ ≤ L) (hM : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) (τ : ℝ) :
    BddC2 (fun y => Θ (y + τ • w y)) := by
  obtain ⟨h2, ⟨M0, hM0⟩, ⟨M1, hM1⟩, ⟨M2, hM2⟩⟩ := hΘ
  have hwd : Differentiable ℝ w := hw.differentiable two_ne_zero
  have hF2 : ContDiff ℝ 2 (fun y => y + τ • w y) := contDiff_id.add (hw.const_smul τ)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hMn : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ w) 0)) (hM 0)
  refine ⟨h2.comp hF2, ⟨M0, fun y => hM0 _⟩,
    ⟨M1 * (1 + |τ| * L), norm_fderiv_comp_add_smul_le (h2.differentiable two_ne_zero) hM1
      hwd hL τ⟩, ?_⟩
  set D₀ : ℝ := 1 + |τ| * L + |τ| * M with hD₀
  have hD1 : 1 ≤ D₀ := by
    have := abs_nonneg τ; have := mul_nonneg this hL0; have := mul_nonneg (abs_nonneg τ) hMn
    linarith
  refine ⟨2 * (M0 + M1 + M2) * D₀ ^ 2, fun y => ?_⟩
  rw [norm_fderiv_fderiv_eq,
    show (fun y => Θ (y + τ • w y)) = Θ ∘ (fun y => y + τ • w y) from rfl]
  have hcomp := norm_iteratedFDeriv_comp_le (n := 2) (N := 2) h2 hF2 le_rfl y
    (C := M0 + M1 + M2) (D := D₀) ?_ ?_
  · simpa using hcomp
  · have h00 : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
    have h10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
    have h20 : 0 ≤ M2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ Θ) 0)) (hM2 0)
    intro i hi
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]; linarith [hM0 (y + τ • w y)]
    · rw [norm_iteratedFDeriv_one]; linarith [hM1 (y + τ • w y)]
    · rw [← norm_fderiv_fderiv_eq]; linarith [hM2 (y + τ • w y)]
  · intro i hi1 hi2
    have hfd := fderiv_add_smul hwd τ
    interval_cases i
    · rw [norm_iteratedFDeriv_one, hfd, pow_one]
      exact (norm_id_add_smul_le (hL y) τ).trans (by
        have := mul_nonneg (abs_nonneg τ) hMn; linarith)
    · rw [← norm_fderiv_fderiv_eq, hfd]
      have hwd2 : DifferentiableAt ℝ (fderiv ℝ w) y :=
        (hw.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y
      have hsm : HasFDerivAt (fun y => τ • fderiv ℝ w y) (τ • fderiv ℝ (fderiv ℝ w) y) y :=
        hwd2.hasFDerivAt.const_smul τ
      rw [fderiv_const_add, hsm.fderiv]
      refine (ContinuousLinearMap.opNorm_smul_le τ (fderiv ℝ (fderiv ℝ w) y)).trans ?_
      rw [Real.norm_eq_abs]
      calc |τ| * ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ |τ| * M :=
            mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)
        _ ≤ D₀ := by have := mul_nonneg (abs_nonneg τ) hL0; linarith
        _ ≤ D₀ ^ 2 := by nlinarith

/-- **Smoothing error.** If `|Θ| ≤ M` and `‖DΘ‖ ≤ G`, then `|heatOp a Θ x - Θ x| ≤ G |a| d`. -/
theorem abs_heatOp_sub_le {Θ : (Fin d → ℝ) → ℝ} (hΘ : Differentiable ℝ Θ) {M G : ℝ}
    (hM : ∀ y, |Θ y| ≤ M) (hG : ∀ y, ‖fderiv ℝ Θ y‖ ≤ G) (a : ℝ) (x : Fin d → ℝ) :
    |heatOp a Θ x - Θ x| ≤ G * |a| * d := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hint : Integrable (fun z => Θ (x + a • z)) stdGauss :=
    integrable_comp_shift_of_bdd hΘ.continuous (fun y => by rw [Real.norm_eq_abs]; exact hM y)
      a x
  have hlip : ∀ z, |Θ (x + a • z) - Θ x| ≤ G * |a| * ‖z‖ := by
    intro z
    have := (convex_univ : Convex ℝ (univ : Set (Fin d → ℝ))).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hΘ y)) (fun y _ => hG y) (mem_univ x) (mem_univ (x + a • z))
    rw [Real.norm_eq_abs, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
    linarith
  have e : heatOp a Θ x - Θ x = ∫ z, (Θ (x + a • z) - Θ x) ∂stdGauss := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [heatOp]
  rw [e]
  calc |∫ z, (Θ (x + a • z) - Θ x) ∂stdGauss| ≤ ∫ z, G * |a| * ‖z‖ ∂stdGauss := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (integrable_norm_stdGauss.const_mul _)
          (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hlip z)
    _ = G * |a| * ∫ z, ‖z‖ ∂stdGauss := integral_const_mul _ _
    _ ≤ G * |a| * d := mul_le_mul_of_nonneg_left integral_norm_stdGauss_le (by positivity)

end FormalizeSampling.FokkerPlanckUniqueness
