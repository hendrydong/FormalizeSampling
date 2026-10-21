module

public import FormalizeSampling.Flow.WeakFokkerPlanckOU

/-!
# Euler–Maruyama steps for the Fokker–Planck existence construction

Status: **Verified.** Infrastructure for the `Flow/FokkerPlanckExistence*.lean` files: the
Euler–Maruyama (EM) transition kernel of `dX = b(X) dt + √(2D) dW` with step `h`,

  `emStep b hb D h x = N(x + h b(x), 2 D h I)`,

its action on test functions `emOp b D h f x = E f(x + h b(x) + √(2Dh) Z)` (`Z ∼ N(0, I_d)`),
the `k`-step kernels `emPow`, and the dyadic EM laws `emCurve` (step `2⁻ⁿ`, piecewise constant
in time on the grid). Operator estimates proved here:

* `abs_emOp_le`, `emOp_sub`, `continuous_emOp`: `emOp` is a linear sup-norm contraction that
  preserves bounded continuous functions;
* `emOp_lipschitz`: a `C`-Lipschitz `f` is mapped to a `C (1 + h L)`-Lipschitz function when `b`
  is `L`-Lipschitz;
* `abs_emOp_sub_le`: `|emOp f - f| ≤ C (h B + √(2Dh) E‖Z‖)` for `‖b‖ ≤ B`;
* `integral_integral_stdGauss_add`: the heat semigroup law `N(0, Dh) * N(0, Dh) = N(0, 2Dh)` in
  integral form (used to compare two half steps with one full step, without coupling paths);
* `integral_emStep`: integrals against one EM step are given by `emOp`.

## Not proved here

* Nothing about SDEs: `emStep` is a kernel, not the transition of a process.
* The generator expansion of `emOp` is in `Flow/FokkerPlanckExistenceGenerator` and
  `Flow/FokkerPlanckExistenceLyap`; tightness of the EM laws in
  `Flow/FokkerPlanckExistenceTimeOp`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal

namespace FormalizeSampling.FokkerPlanckExistence
open FormalizeSampling.HeatKernelPi FormalizeSampling.WeakFokkerPlanckOU

variable {d : ℕ}

/-- The EM noise variance `2 D h` as an element of `ℝ≥0` (truncated at `0`). -/
noncomputable def stepVar (D h : ℝ) : ℝ≥0 := (2 * D * h).toNNReal

/-- The **EM operator** with drift `b`, diffusion `D` and step `h`:
`emOp b D h f x = E f(x + h b(x) + √(2Dh) Z)` with `Z ∼ N(0, I_d)` (`stdGauss`). -/
noncomputable def emOp (b : (Fin d → ℝ) → Fin d → ℝ) (D h : ℝ) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∫ z, f (x + h • b x + Real.sqrt (2 * D * h) • z) ∂stdGauss

/-- The Gaussian constant `E‖Z‖` (sup norm), `Z ∼ N(0, I_d)`. -/
noncomputable def gaussNormMean : ℝ := ∫ z, ‖z‖ ∂(stdGauss (d := d))

/-- The **EM kernel** `x ↦ N(x + h b(x), 2 D h I)`: the heat kernel with variance `2Dh`
precomposed with the drift map `x ↦ x + h b(x)`. -/
noncomputable def emStep (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D h : ℝ) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (heatKernelPi (stepVar D h)).comap (fun x => x + h • b x)
    (measurable_id.add (hb.const_smul h))

/-- `emStep` is a Markov kernel. -/
instance isMarkovKernel_emStep (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D h : ℝ) :
    IsMarkovKernel (emStep b hb D h) := by
  unfold emStep; infer_instance

/-- The `k`-step EM kernel: `emPow 0 = id`, `emPow (k + 1) = emStep ∘ₖ emPow k`. -/
noncomputable def emPow (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D h : ℝ) :
    ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)
  | 0 => Kernel.id
  | k + 1 => emStep b hb D h ∘ₖ emPow b hb D h k

/-- `emPow k` is a Markov kernel. -/
instance isMarkovKernel_emPow (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D h : ℝ)
    (k : ℕ) : IsMarkovKernel (emPow b hb D h k) := by
  induction k with
  | zero => unfold emPow; infer_instance
  | succ k ih => unfold emPow; infer_instance

/-- The dyadic step `2⁻ⁿ`. -/
noncomputable def dyadicStep (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- The number of completed dyadic steps at time `t`: `⌊t 2ⁿ⌋₊` (`= 0` for `t ≤ 0`). -/
noncomputable def gridIndex (n : ℕ) (t : ℝ) : ℕ := ⌊t * 2 ^ n⌋₊

/-- The **dyadic EM law** at level `n` and time `t`: `ρ₀` pushed through `⌊t 2ⁿ⌋₊` EM steps of
size `2⁻ⁿ` (piecewise constant in `t`; equal to `ρ₀` for `t < 2⁻ⁿ`). -/
noncomputable def emCurve (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (D : ℝ)
    (ρ₀ : Measure (Fin d → ℝ)) (n : ℕ) (t : ℝ) : Measure (Fin d → ℝ) :=
  emPow b hb D (dyadicStep n) (gridIndex n t) ∘ₘ ρ₀

/-- The dyadic EM laws of a probability measure are probability measures. -/
instance isProbabilityMeasure_emCurve (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b)
    (D : ℝ) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (n : ℕ) (t : ℝ) :
    IsProbabilityMeasure (emCurve b hb D ρ₀ n t) := by
  unfold emCurve; infer_instance

section Operator

variable {b : (Fin d → ℝ) → Fin d → ℝ} {D h : ℝ} {f g : (Fin d → ℝ) → ℝ}

/-- A bounded continuous function of an affine image `m + c z` is integrable under
`N(0, I_d)`. -/
theorem integrable_comp_affine (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M)
    (m : Fin d → ℝ) (c : ℝ) : Integrable (fun z => f (m + c • z)) stdGauss :=
  Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable M
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM _)

/-- A Gaussian expectation of a function bounded by `M` is bounded by `M`. -/
theorem abs_integral_stdGauss_le {F : (Fin d → ℝ) → ℝ} {M : ℝ} (hM : ∀ y, |F y| ≤ M) :
    |∫ z, F z ∂stdGauss| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := stdGauss) (f := F) (C := M)
    (ae_of_all _ fun _ => by rw [Real.norm_eq_abs]; exact hM _)
  simpa [Real.norm_eq_abs] using this

/-- Integral against the heat kernel as a Gaussian expectation:
`∫ g dN(m, v I) = E g(m + √v Z)` for continuous `g`. -/
theorem integral_heatKernelPi (hg : Continuous g) (v : ℝ≥0) (m : Fin d → ℝ) :
    ∫ y, g y ∂(heatKernelPi v m) = ∫ z, g (m + Real.sqrt v • z) ∂stdGauss := by
  rw [heatKernelPi_apply, pi_gaussianReal_eq_map,
    integral_map (by fun_prop : Measurable fun z : Fin d → ℝ => m + Real.sqrt v • z).aemeasurable
      hg.aestronglyMeasurable]

/-- `y ↦ E g(y + c Z)` is continuous for bounded continuous `g` (dominated convergence). -/
theorem continuous_integral_shift (hg : Continuous g) {M : ℝ} (hM : ∀ y, |g y| ≤ M) (c : ℝ) :
    Continuous fun y : Fin d → ℝ => ∫ z, g (y + c • z) ∂stdGauss :=
  continuous_of_dominated (bound := fun _ => M)
    (fun y => (hg.comp (by fun_prop)).aestronglyMeasurable)
    (fun y => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM _)
    (integrable_const M) (ae_of_all _ fun z => hg.comp (by fun_prop))

/-- Comparison of two Gaussian expectations under an affine pointwise bound: if `F, G` are
integrable under `N(0, I_d)` and `|F z - G z| ≤ K₁ + K₂ ‖z‖`, then
`|E F - E G| ≤ K₁ + K₂ E‖Z‖`. -/
theorem abs_integral_sub_le {F G : (Fin d → ℝ) → ℝ} (hF : Integrable F stdGauss)
    (hG : Integrable G stdGauss) {K₁ K₂ : ℝ} (hFG : ∀ z, |F z - G z| ≤ K₁ + K₂ * ‖z‖) :
    |∫ z, F z ∂stdGauss - ∫ z, G z ∂stdGauss| ≤ K₁ + K₂ * gaussNormMean (d := d) := by
  rw [← integral_sub hF hG]
  refine abs_integral_le_integral_abs.trans ?_
  have hb : Integrable (fun z : Fin d → ℝ => K₁ + K₂ * ‖z‖) stdGauss :=
    (integrable_const K₁).add (integrable_norm_stdGauss.const_mul K₂)
  refine (integral_mono (hF.sub hG).abs hb hFG).trans (le_of_eq ?_)
  rw [integral_add (integrable_const K₁) (integrable_norm_stdGauss.const_mul K₂),
    integral_const_mul, integral_const]
  simp [gaussNormMean]

/-- **Gaussian sum rule.** For bounded continuous `g`, `v : ℝ≥0` and `m`,
`E g(m + √v Z₁ + √v Z₂) = E g(m + √(2v) Z)` with `Z₁, Z₂, Z` standard Gaussians (`Z₁ ⊥ Z₂`);
this is the heat semigroup law `N(0, v I) * N(0, v I) = N(0, 2v I)`. -/
theorem integral_integral_stdGauss_add (hg : Continuous g) {M : ℝ} (hM : ∀ y, |g y| ≤ M)
    (v : ℝ≥0) (m : Fin d → ℝ) :
    ∫ z₁, ∫ z₂, g (m + Real.sqrt v • z₁ + Real.sqrt v • z₂) ∂stdGauss ∂stdGauss =
      ∫ z, g (m + Real.sqrt ((v + v : ℝ≥0) : ℝ) • z) ∂stdGauss := by
  have hint : Integrable g ((heatKernelPi v ∘ₖ heatKernelPi v) m) :=
    Integrable.of_bound hg.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)
  calc _ = ∫ y, ∫ z, g (y + Real.sqrt v • z) ∂stdGauss ∂(heatKernelPi v m) := by
        rw [integral_heatKernelPi (continuous_integral_shift hg hM _)]
    _ = ∫ y, ∫ w, g w ∂(heatKernelPi v y) ∂(heatKernelPi v m) := by
        congr 1; funext y; exact (integral_heatKernelPi hg v y).symm
    _ = ∫ w, g w ∂((heatKernelPi v ∘ₖ heatKernelPi v) m) := (Kernel.integral_comp hint).symm
    _ = _ := by rw [heatKernelPi_comp_heatKernelPi, integral_heatKernelPi hg]

/-- Integrals against the EM kernel are values of the EM operator (`D, h ≥ 0`, `f` continuous). -/
theorem integral_emStep (hb : Measurable b) (hD : 0 ≤ D) (hh : 0 ≤ h) (hf : Continuous f)
    (x : Fin d → ℝ) : ∫ y, f y ∂(emStep b hb D h x) = emOp b D h f x := by
  rw [emStep, Kernel.comap_apply, integral_heatKernelPi hf, emOp, stepVar,
    Real.coe_toNNReal _ (by positivity)]

/-- `emOp` is a sup-norm contraction: `|f| ≤ M` implies `|emOp f| ≤ M` (`f` continuous). -/
theorem abs_emOp_le (_hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) (x : Fin d → ℝ) :
    |emOp b D h f x| ≤ M :=
  abs_integral_stdGauss_le fun _ => hM _

/-- Linearity of `emOp` on bounded continuous functions: `emOp (f - g) = emOp f - emOp g`. -/
theorem emOp_sub (hf : Continuous f) (hg : Continuous g) {M N : ℝ} (hM : ∀ y, |f y| ≤ M)
    (hN : ∀ y, |g y| ≤ N) (x : Fin d → ℝ) :
    emOp b D h (fun y => f y - g y) x = emOp b D h f x - emOp b D h g x :=
  integral_sub (integrable_comp_affine hf hM _ _) (integrable_comp_affine hg hN _ _)

/-- For continuous `b` and bounded continuous `f`, `emOp b D h f` is continuous (dominated
convergence). -/
theorem continuous_emOp (hb : Continuous b) (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    Continuous (emOp b D h f) :=
  (continuous_integral_shift hf hM (Real.sqrt (2 * D * h))).comp
    (continuous_id.add (hb.const_smul h))

/-- **Lipschitz propagation.** If `b` is `L`-Lipschitz, `h ≥ 0`, and `f` is bounded, continuous
and `C`-Lipschitz, then `emOp b D h f` is `C (1 + h L)`-Lipschitz (synchronous coupling of the
noise). -/
theorem emOp_lipschitz {L : ℝ≥0} (hL : LipschitzWith L b) (hh : 0 ≤ h) (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ} (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖)
    (x y : Fin d → ℝ) :
    |emOp b D h f x - emOp b D h f y| ≤ C * (1 + h * L) * ‖x - y‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hC0 : 0 ≤ C := by
    have h2 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    by_contra hneg
    replace hneg := not_le.1 hneg
    linarith [hC x y, abs_nonneg (f x - f y), mul_neg_of_neg_of_pos hneg h2]
  set s := Real.sqrt (2 * D * h)
  have hpt : ∀ z : Fin d → ℝ, |f (x + h • b x + s • z) - f (y + h • b y + s • z)| ≤
      C * (1 + h * L) * ‖x - y‖ + 0 * ‖z‖ := by
    intro z
    rw [zero_mul, add_zero]
    refine (hC _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have e : x + h • b x + s • z - (y + h • b y + s • z) = (x - y) + h • (b x - b y) := by
      rw [smul_sub]; abel
    rw [e]
    calc ‖(x - y) + h • (b x - b y)‖ ≤ ‖x - y‖ + h * ‖b x - b y‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hh]
      _ ≤ ‖x - y‖ + h * (L * ‖x - y‖) := by gcongr; exact hL.norm_sub_le _ _
      _ = (1 + h * L) * ‖x - y‖ := by ring
  have key := abs_integral_sub_le (integrable_comp_affine hf hM (x + h • b x) s)
    (integrable_comp_affine hf hM (y + h • b y) s) hpt
  simpa [emOp] using key

/-- **One step moves Lipschitz test functions by `O(√h)`.** If `‖b‖ ≤ B`, `D, h ≥ 0` and `f` is
bounded, continuous and `C`-Lipschitz with `C ≥ 0`, then
`|emOp f x - f x| ≤ C (h B + √(2Dh) E‖Z‖)`. -/
theorem abs_emOp_sub_le {B : ℝ} (hB : ∀ x, ‖b x‖ ≤ B) (_hD : 0 ≤ D) (hh : 0 ≤ h)
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ}
    (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C) (x : Fin d → ℝ) :
    |emOp b D h f x - f x| ≤ C * (h * B + Real.sqrt (2 * D * h) * gaussNormMean (d := d)) := by
  set s := Real.sqrt (2 * D * h)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpt : ∀ z : Fin d → ℝ, |f (x + h • b x + s • z) - f x| ≤
      C * (h * B) + C * s * ‖z‖ := by
    intro z
    refine (hC _ _).trans ?_
    have e : x + h • b x + s • z - x = h • b x + s • z := by abel
    rw [e, mul_assoc, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hh, Real.norm_of_nonneg hs0]
    gcongr
    exact hB x
  have key := abs_integral_sub_le (integrable_comp_affine hf hM (x + h • b x) s)
    (integrable_const (f x)) hpt
  have e : f x = ∫ _z, f x ∂(stdGauss (d := d)) := by simp
  rw [emOp]
  conv_lhs => rw [e]
  refine key.trans (le_of_eq ?_)
  ring

end Operator

end FormalizeSampling.FokkerPlanckExistence
