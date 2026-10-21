module

public import FormalizeSampling.Samplers.RGOCouplingChainPi

/-!
# Pathwise Lipschitz RGO for a potential plus a positive semidefinite quadratic form

Status: **Verified** (no named hypotheses).

Let `h : (Fin d → ℝ) → ℝ` be measurable with `∫ e^{-h} < ∞`, `B : Matrix (Fin k) (Fin d) ℝ`
and `λ ≥ 0` with `|B z|² ≤ λ |z|²` for all `z`, and

  `f x = h x + λ |x|² / 2 - |B x|² / 2`,

i.e. `f = h + q` with the positive semidefinite quadratic form `q(x) = xᵀ (λ I - BᵀB) x / 2`.
Every positive semidefinite `Q` is of the form `λ I - BᵀB` for `λ ≥ ‖Q‖`.

**Theorem** (`hasLipRep_rgoKernelPi_add_quadratic`). If the RGO kernel of `h` with step
`η' = η / (1 + λ η)` has a pathwise `1`-Lipschitz representation, then so does the RGO kernel of
`f` with step `η`. Combined with the separable case this gives the pathwise representation, hence
the `1/k` KL rate (`Samplers/ProximalLogConcaveRateGeneralPi.lean`), for
**separable convex plus positive semidefinite quadratic** potentials
`f x = ∑ᵢ gᵢ(xᵢ) + xᵀ Q x / 2` (`hasLipRep_rgoKernelPi_separable_add_quadratic`), which are not
separable when `Q` is not diagonal.

## Method: an exact Gibbs chain with Gaussian auxiliary variable

The RGO law `R_y ∝ e^{-f(x) - |x - y|² / (2η)}` is the `x`-marginal of the joint density

  `p(x, v) ∝ e^{-h(x) - λ|x|²/2 - |x - y|²/(2η) + ⟨B x, v⟩ - |v|²/2}`, `v ∈ ℝᵏ`

(Hubbard–Stratonovich: `∫ e^{⟨Bx, v⟩ - |v|²/2} dv ∝ e^{|Bx|²/2}`). Its conditionals are

* `v | x ∼ N(B x, I_k)` (`Nvx`);
* `x | v ∼ RGO_h^{η'}(c(y, v))` with centre `c(y, v) = η' (y / η + Bᵀ v)` (`Kxv`).

The two-step Gibbs chain `x ↦ v = B x + ξ ↦ x' = G_h(c(y, v), ω)` (with `ξ ∼ N(0, I_k)` and
`(Ω, P, G_h)` the representation of `RGO_h^{η'}`) leaves `R_y` invariant
(`gibbs_stationary`, via the Bayes reverse-kernel identity of `Kernels/ReverseKernel.lean`), and
is a synchronous contraction: since `‖BᵀB‖ ≤ λ`,

  `|x'₁ - x'₂| ≤ |c(y₁, v₁) - c(y₂, v₂)| ≤ (1 - θ) |x₁ - x₂| + θ |y₁ - y₂|`, `θ = 1 / (1 + λη)`.

`RGOCouplingChainPi.hasLipRep_of_contraction` (backward iteration) then produces the
representation of `R_y`. The first-moment condition holds because Gaussian vectors and RGO laws
of `h` have finite first moments (`lintegral_eDist_rgoKernelPi_lt_top`).

## Not proved here

* General (non-separable, non-quadratic) convex `f`: the Gibbs construction needs an exactly
  Gaussian factor to integrate out; for general `f` one would need the long-time convergence of
  a Langevin-type chain, which is not available.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingPi
open FormalizeSampling.RGOCouplingChainPi FormalizeSampling.ReverseKernel
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingQuadraticPi

variable {d k : ℕ}

/-! ### Euclidean algebra -/

/-- Cauchy–Schwarz: `(a ⬝ b)² ≤ (a ⬝ a) (b ⬝ b)`. -/
theorem dot_sq_le (a b : Fin d → ℝ) : (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simpa [dotProduct, sq] using this

/-- The Euclidean norm of `x` is `|x - 0|`. -/
theorem eDist_zero_eq_norm (x : Fin d → ℝ) :
    eDist x 0 = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [eDist_eq_dist, WithLp.toLp_zero, dist_zero_right]

/-- `|x - y| = |(x - y) - 0|`. -/
theorem eDist_eq_eDist_sub (x y : Fin d → ℝ) : eDist x y = eDist (x - y) 0 := by
  rw [eDist_eq_dist, eDist_zero_eq_norm, dist_eq_norm, WithLp.toLp_sub]

/-- Triangle inequality for the Euclidean norm. -/
theorem eDist_add_le (a b : Fin d → ℝ) : eDist (a + b) 0 ≤ eDist a 0 + eDist b 0 := by
  simp only [eDist_zero_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

/-- Homogeneity of the Euclidean norm. -/
theorem eDist_smul (r : ℝ) (a : Fin d → ℝ) : eDist (r • a) 0 = |r| * eDist a 0 := by
  simp only [eDist_zero_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- If `a ⬝ a ≤ c² (b ⬝ b)` with `c ≥ 0`, then `|a| ≤ c |b|`. -/
theorem eDist_le_of_dot_le {a : Fin d → ℝ} {b : Fin k → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : a ⬝ᵥ a ≤ c ^ 2 * (b ⬝ᵥ b)) : eDist a 0 ≤ c * eDist b 0 := by
  rw [eDist, eDist, sqDist_zero_right, sqDist_zero_right, ← Real.sqrt_sq hc,
    ← Real.sqrt_mul (sq_nonneg c)]
  exact Real.sqrt_le_sqrt h

variable {B : Matrix (Fin k) (Fin d) ℝ} {lam : ℝ}

/-- `‖Bᵀ‖² ≤ λ` from `‖B‖² ≤ λ`: `|Bᵀ ξ|² ≤ λ |ξ|²`. -/
theorem dot_transpose_le (hl : 0 ≤ lam) (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z))
    (ξ : Fin k → ℝ) :
    (Bᵀ *ᵥ ξ) ⬝ᵥ (Bᵀ *ᵥ ξ) ≤ lam * (ξ ⬝ᵥ ξ) := by
  set u := Bᵀ *ᵥ ξ
  have e : u ⬝ᵥ u = (B *ᵥ u) ⬝ᵥ ξ := by
    conv_lhs => rw [show u ⬝ᵥ u = u ⬝ᵥ (Bᵀ *ᵥ ξ) from rfl]
    rw [dotProduct_mulVec, vecMul_transpose]
  have h1 := dot_sq_le (B *ᵥ u) ξ
  rw [← e] at h1
  have h2 := hB u
  have hu := dot_self_nonneg u
  have hξ := dot_self_nonneg ξ
  rcases hu.lt_or_eq with hpos | hzero
  · have : (u ⬝ᵥ u) ^ 2 ≤ lam * (u ⬝ᵥ u) * (ξ ⬝ᵥ ξ) := by nlinarith
    nlinarith
  · rw [← hzero]
    positivity

/-- `‖BᵀB‖ ≤ λ`: `|BᵀB z| ≤ λ |z|`. -/
theorem eDist_transpose_mul_le (hl : 0 ≤ lam)
    (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) (z : Fin d → ℝ) :
    eDist (Bᵀ *ᵥ (B *ᵥ z)) 0 ≤ lam * eDist z 0 := by
  refine eDist_le_of_dot_le hl ?_
  have h1 := dot_transpose_le hl hB (B *ᵥ z)
  have h2 := hB z
  calc _ ≤ lam * ((B *ᵥ z) ⬝ᵥ (B *ᵥ z)) := h1
    _ ≤ lam * (lam * (z ⬝ᵥ z)) := mul_le_mul_of_nonneg_left h2 hl
    _ = lam ^ 2 * (z ⬝ᵥ z) := by ring

/-! ### The Gibbs chain -/

/-- The inner step `η' = η / (1 + λ η)`. -/
noncomputable def innerStep (η lam : ℝ) : ℝ := η / (1 + lam * η)

/-- The centre `c(y, v) = η' (y / η + Bᵀ v)` of the conditional law of `x` given `v`. -/
noncomputable def center (B : Matrix (Fin k) (Fin d) ℝ) (η lam : ℝ) (y : Fin d → ℝ)
    (v : Fin k → ℝ) : Fin d → ℝ :=
  innerStep η lam • (η⁻¹ • y + Bᵀ *ᵥ v)

/-- The centre map is continuous in `(y, v)`. -/
theorem continuous_center (B : Matrix (Fin k) (Fin d) ℝ) (η lam : ℝ) :
    Continuous fun p : (Fin d → ℝ) × (Fin k → ℝ) => center B η lam p.1 p.2 := by
  unfold center
  have h1 : Continuous fun p : (Fin d → ℝ) × (Fin k → ℝ) => Bᵀ *ᵥ p.2 :=
    continuous_const.matrix_mulVec continuous_snd
  have h2 : Continuous fun p : (Fin d → ℝ) × (Fin k → ℝ) => η⁻¹ • p.1 :=
    by fun_prop
  exact (h2.add h1).const_smul (innerStep η lam)

/-- The Gibbs map `H(y, x, (ξ, ω)) = G(c(y, B x + ξ), ω)`. -/
noncomputable def gibbsMap {Ω : Type} (G : (Fin d → ℝ) → Ω → Fin d → ℝ)
    (B : Matrix (Fin k) (Fin d) ℝ) (η lam : ℝ) (y x : Fin d → ℝ) (q : (Fin k → ℝ) × Ω) :
    Fin d → ℝ :=
  G (center B η lam y (B *ᵥ x + q.1)) q.2

/-- **Synchronous contraction of the Gibbs map.** If `G` is pathwise `1`-Lipschitz, `λ ≥ 0`,
`η > 0` and `‖B‖² ≤ λ`, then with `θ = 1 / (1 + λη)`:
`|H(y, x, q) - H(y', x', q)| ≤ (1 - θ) |x - x'| + θ |y - y'|`. -/
theorem eDist_gibbsMap_le {Ω : Type} {G : (Fin d → ℝ) → Ω → Fin d → ℝ}
    (hlip : ∀ y y' ω, sqDist (G y ω) (G y' ω) ≤ sqDist y y') (hl : 0 ≤ lam) {η : ℝ}
    (hη : 0 < η) (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z))
    (y y' x x' : Fin d → ℝ) (q : (Fin k → ℝ) × Ω) :
    eDist (gibbsMap G B η lam y x q) (gibbsMap G B η lam y' x' q)
      ≤ (1 - 1 / (1 + lam * η)) * eDist x x' + 1 / (1 + lam * η) * eDist y y' := by
  have h1 : eDist (gibbsMap G B η lam y x q) (gibbsMap G B η lam y' x' q)
      ≤ eDist (center B η lam y (B *ᵥ x + q.1)) (center B η lam y' (B *ᵥ x' + q.1)) :=
    Real.sqrt_le_sqrt (hlip _ _ _)
  refine h1.trans ?_
  have hpos : 0 < 1 + lam * η := by positivity
  have e : center B η lam y (B *ᵥ x + q.1) - center B η lam y' (B *ᵥ x' + q.1)
      = innerStep η lam • (η⁻¹ • (y - y') + Bᵀ *ᵥ (B *ᵥ (x - x'))) := by
    simp only [center, mulVec_add, mulVec_sub, smul_sub, smul_add]
    abel
  rw [eDist_eq_eDist_sub, e, eDist_smul, eDist_eq_eDist_sub x x', eDist_eq_eDist_sub y y']
  have hs : 0 ≤ innerStep η lam := by unfold innerStep; positivity
  rw [abs_of_nonneg hs]
  have h2 := eDist_add_le (η⁻¹ • (y - y')) (Bᵀ *ᵥ (B *ᵥ (x - x')))
  rw [eDist_smul, abs_of_pos (inv_pos.2 hη)] at h2
  have h3 := eDist_transpose_mul_le hl hB (x - x')
  calc innerStep η lam * eDist (η⁻¹ • (y - y') + Bᵀ *ᵥ (B *ᵥ (x - x'))) 0
      ≤ innerStep η lam * (η⁻¹ * eDist (y - y') 0 + lam * eDist (x - x') 0) := by
        gcongr
        exact h2.trans (by linarith)
    _ = (1 - 1 / (1 + lam * η)) * eDist (x - x') 0 + 1 / (1 + lam * η) * eDist (y - y') 0 := by
        unfold innerStep
        field_simp
        ring

/-! ### Invariance of the RGO law under the Gibbs chain -/

/-- The constant `C(y, v) = |c|² / (2η') - |y|² / (2η) - |v|² / 2` of the Gibbs identity. -/
noncomputable def gibbsConst (B : Matrix (Fin k) (Fin d) ℝ) (η lam : ℝ) (y : Fin d → ℝ)
    (v : Fin k → ℝ) : ℝ :=
  center B η lam y v ⬝ᵥ center B η lam y v / (2 * innerStep η lam) - y ⬝ᵥ y / (2 * η)
    - v ⬝ᵥ v / 2

/-- **The Gibbs exponent identity.** If `f x = h x + λ |x|² / 2 - |B x|² / 2`, then
`-f(x) - |x - y|²/(2η) - |B x - v|²/2 = C(y, v) - h(x) - |x - c(y, v)|²/(2η')`. -/
theorem gibbs_exponent {h f : (Fin d → ℝ) → ℝ}
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2) (hl : 0 ≤ lam)
    {η : ℝ} (hη : 0 < η) (y x : Fin d → ℝ) (v : Fin k → ℝ) :
    (-f x - sqDist x y / (2 * η)) + -sqDist (B *ᵥ x) v / (2 * 1)
      = gibbsConst B η lam y v
        + (-h x - sqDist x (center B η lam y v) / (2 * innerStep η lam)) := by
  have hxc : x ⬝ᵥ center B η lam y v
      = innerStep η lam * (η⁻¹ * (x ⬝ᵥ y) + (B *ᵥ x) ⬝ᵥ v) := by
    rw [center, dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_mulVec,
      vecMul_transpose, dotProduct_comm (B *ᵥ x) v]
    simp [smul_eq_mul]
  rw [hf, sqDist_expand x y, sqDist_expand (B *ᵥ x) v, sqDist_expand x (center B η lam y v), hxc,
    gibbsConst]
  unfold innerStep
  have hpos : 0 < 1 + lam * η := by positivity
  field_simp
  ring

/-- The forward Gaussian density in closed form: for `η > 0`,
`forwardDensityPi η m v = ofReal ((2πη)^{-k/2} exp(-|m - v|² / (2η)))`. -/
theorem forwardDensityPi_eq_ofReal {η : ℝ} (hη : 0 < η) (m v : Fin k → ℝ) :
    forwardDensityPi η m v = ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi * η))⁻¹ ^ k * Real.exp (-(sqDist m v) / (2 * η))) := by
  rw [← prod_gaussianPDFReal hη, forwardDensityPi, MALA.prodGaussianPDF,
    ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]
  rfl

/-- The constant `A(y, v) = (2π)^{-k/2} e^{C(y, v)} / Z_f(y)` of the Gibbs identity. -/
noncomputable def gibbsAmp (f : (Fin d → ℝ) → ℝ) (B : Matrix (Fin k) (Fin d) ℝ) (η lam : ℝ)
    (y : Fin d → ℝ) (v : Fin k → ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * 1))⁻¹ ^ k * Real.exp (gibbsConst B η lam y v) / rgoNormalizerPi f η y

/-- **Joint density factorisation.** Prior density times forward density equals
`A(y, v) · e^{-h(x) - |x - c(y, v)|²/(2η')}`. -/
theorem rgoDensityPi_mul_forward {h f : (Fin d → ℝ) → ℝ}
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2) (hl : 0 ≤ lam)
    {η : ℝ} (hη : 0 < η) (y x : Fin d → ℝ) (v : Fin k → ℝ) :
    rgoDensityPi f η y x * ((Real.sqrt (2 * Real.pi * 1))⁻¹ ^ k
        * Real.exp (-(sqDist (B *ᵥ x) v) / (2 * 1)))
      = gibbsAmp f B η lam y v
        * Real.exp (-h x - sqDist x (center B η lam y v) / (2 * innerStep η lam)) := by
  have e := congrArg Real.exp (gibbs_exponent (k := k) hf hl hη y x v)
  rw [Real.exp_add, Real.exp_add] at e
  have : Real.exp (-f x - sqDist x y / (2 * η)) * ((Real.sqrt (2 * Real.pi * 1))⁻¹ ^ k
      * Real.exp (-sqDist (B *ᵥ x) v / (2 * 1)))
      = (Real.sqrt (2 * Real.pi * 1))⁻¹ ^ k * Real.exp (gibbsConst B η lam y v)
        * Real.exp (-h x - sqDist x (center B η lam y v) / (2 * innerStep η lam)) := by
    linear_combination (Real.sqrt (2 * Real.pi * 1))⁻¹ ^ k * e
  rw [rgoDensityPi, gibbsAmp, div_mul_eq_mul_div, div_mul_eq_mul_div, this]

variable {h f : (Fin d → ℝ) → ℝ}

/-- `x ↦ B x` is continuous. -/
theorem continuous_mulVec (B : Matrix (Fin k) (Fin d) ℝ) : Continuous fun x : Fin d → ℝ => B *ᵥ x :=
  continuous_const.matrix_mulVec continuous_id

/-- `h ≤ f` when `f = h + λ |x|²/2 - |Bx|²/2` and `‖B‖² ≤ λ`. -/
theorem le_of_quad (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2)
    (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) (x : Fin d → ℝ) : h x ≤ f x := by
  rw [hf]
  linarith [hB x]

/-- `f = h + λ |x|²/2 - |Bx|²/2` is measurable if `h` is. -/
theorem measurable_of_quad (hh : Measurable h)
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2) : Measurable f := by
  have e : f = fun x => h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2 := funext hf
  rw [e]
  have h1 : Continuous fun x : Fin d → ℝ => x ⬝ᵥ x := continuous_id.dotProduct continuous_id
  have h2 : Continuous fun x : Fin d → ℝ => (B *ᵥ x) ⬝ᵥ (B *ᵥ x) :=
    (continuous_mulVec B).dotProduct (continuous_mulVec B)
  exact (hh.add (measurable_const.mul h1.measurable)).sub (h2.measurable.div_const 2)

/-- `e^{-f}` is integrable if `e^{-h}` is (since `f ≥ h`). -/
theorem integrable_of_quad (hh : Measurable h) (hinth : Integrable fun x => Real.exp (-h x))
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2)
    (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) :
    Integrable fun x => Real.exp (-f x) := by
  refine hinth.mono' (Real.measurable_exp.comp (measurable_of_quad hh hf).neg).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (neg_le_neg (le_of_quad hf hB x))

/-- The forward density `(x, v) ↦ N(v; B x, I_k)` is jointly measurable. -/
theorem measurable_fwdB_density (B : Matrix (Fin k) (Fin d) ℝ) :
    Measurable (Function.uncurry fun x v => forwardDensityPi (d := k) 1 (B *ᵥ x) v) := by
  have e : (Function.uncurry fun x v => forwardDensityPi (d := k) 1 (B *ᵥ x) v)
      = Function.uncurry (forwardDensityPi (d := k) 1) ∘ Prod.map (fun x => B *ᵥ x) id := rfl
  rw [e]
  exact (measurable_forwardDensityPi 1).comp
    ((continuous_mulVec B).measurable.prodMap measurable_id)

/-- The density kernel `x ↦ N(B x, I_k)` is the forward kernel at `B x`. -/
theorem densityKernel_fwdB_apply (B : Matrix (Fin k) (Fin d) ℝ) (x : Fin d → ℝ) :
    densityKernel volume (fun x v => forwardDensityPi (d := k) 1 (B *ᵥ x) v) x
      = forwardKernelPi 1 (B *ᵥ x) := by
  rw [densityKernel_apply (measurable_fwdB_density B), forwardKernelPi_eq_densityKernel one_pos,
    densityKernel_apply (measurable_forwardDensityPi 1)]

/-- **The Bayes reverse kernel is the inner RGO.** For the prior `RGO_f^η(y)` and the forward
kernel `x ↦ N(B x, I_k)`, the reverse density kernel at `v` is `RGO_h^{η'}(c(y, v))`. -/
theorem reverse_eq_rgo (hh : Measurable h) (hinth : Integrable fun x => Real.exp (-h x))
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2) (hl : 0 ≤ lam)
    (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) {η : ℝ} (hη : 0 < η)
    (y : Fin d → ℝ) (v : Fin k → ℝ) :
    densityKernel volume (reverseDensity volume (fun x => ENNReal.ofReal (rgoDensityPi f η y x))
        (fun x v => forwardDensityPi (d := k) 1 (B *ᵥ x) v)) v
      = rgoKernelPi h (innerStep η lam) (center B η lam y v) := by
  have hηq : 0 < innerStep η lam := by unfold innerStep; positivity
  have hfm := measurable_of_quad hh hf
  have hintf := integrable_of_quad hh hinth hf hB
  have hp : Measurable fun x => ENNReal.ofReal (rgoDensityPi f η y x) :=
    (measurable_rgoDensityPi hfm hintf hη).comp measurable_prodMk_left
  rw [densityKernel_apply (measurable_reverseDensity hp (measurable_fwdB_density B)),
    rgoKernelPi_apply hh hinth hηq]
  congr 1
  funext x
  have hA : 0 < gibbsAmp f B η lam y v := by
    unfold gibbsAmp
    have := rgoNormalizerPi_pos hintf hη y
    positivity
  have hpk : ∀ x, ENNReal.ofReal (rgoDensityPi f η y x) * forwardDensityPi 1 (B *ᵥ x) v
      = ENNReal.ofReal (gibbsAmp f B η lam y v)
        * ENNReal.ofReal (Real.exp (-h x - sqDist x (center B η lam y v)
          / (2 * innerStep η lam))) := by
    intro x
    rw [forwardDensityPi_eq_ofReal one_pos, ← ENNReal.ofReal_mul (rgoDensityPi_nonneg _ _),
      rgoDensityPi_mul_forward hf hl hη, ENNReal.ofReal_mul hA.le]
  have hE : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp (-h x
      - sqDist x (center B η lam y v) / (2 * innerStep η lam))) := by
    have : Measurable fun x : Fin d → ℝ => sqDist x (center B η lam y v) :=
      (continuous_sqDist.comp (continuous_id.prodMk continuous_const)).measurable
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hh.neg).sub
      (this.div_const _)))
  unfold reverseDensity marginalDensity
  simp_rw [hpk]
  rw [lintegral_const_mul _ hE, lintegral_rgoPi hinth hηq,
    ENNReal.mul_div_mul_left _ _ (by simpa using hA) ENNReal.ofReal_ne_top, rgoDensityPi,
    ENNReal.ofReal_div_of_pos (rgoNormalizerPi_pos hinth hηq _)]

/-- **Invariance of `RGO_f^η(y)` under the Gibbs chain.** Let `(Ω, P, G)` represent
`RGO_h^{η'}` (`G(z, ·)_# P = RGO_h^{η'}(z)`). If `x ∼ RGO_f^η(y)`, `ξ ∼ N(0, I_k)` and `ω ∼ P`
are independent, then `G(c(y, B x + ξ), ω) ∼ RGO_f^η(y)`. -/
theorem gibbs_stationary (hh : Measurable h) (hinth : Integrable fun x => Real.exp (-h x))
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2) (hl : 0 ≤ lam)
    (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) {η : ℝ} (hη : 0 < η)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : (Fin d → ℝ) → Ω → Fin d → ℝ} (hG : Measurable (Function.uncurry G))
    (hGK : ∀ z, P.map (G z) = rgoKernelPi h (innerStep η lam) z) (y : Fin d → ℝ) :
    ((rgoKernelPi f η y).prod ((Measure.pi fun _ : Fin k => gaussianReal 0 1).prod P)).map
      (fun q => gibbsMap G B η lam y q.1 q.2) = rgoKernelPi f η y := by
  have hηq : 0 < innerStep η lam := by unfold innerStep; positivity
  have hfm := measurable_of_quad hh hf
  have hintf := integrable_of_quad hh hinth hf hB
  have := isMarkovKernel_rgoKernelPi hfm hintf hη
  have := isMarkovKernel_rgoKernelPi hh hinth hηq
  set p : (Fin d → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (rgoDensityPi f η y x) with hpdef
  set kf : (Fin d → ℝ) → (Fin k → ℝ) → ℝ≥0∞ := fun x v => forwardDensityPi 1 (B *ᵥ x) v
    with hkfdef
  have hp : Measurable p := (measurable_rgoDensityPi hfm hintf hη).comp measurable_prodMk_left
  have hk : Measurable (Function.uncurry kf) := measurable_fwdB_density B
  have hk1 : ∀ x, ∫⁻ v, kf x v = 1 := fun x => lintegral_forwardDensityPi one_pos _
  have hKy : rgoKernelPi f η y = volume.withDensity p := rgoKernelPi_apply hfm hintf hη y
  have hpfin : ∫⁻ x, p x ≠ ⊤ := by
    have h1 := measure_univ (μ := rgoKernelPi f η y)
    rw [hKy, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    rw [h1]
    exact ENNReal.one_ne_top
  have hrev := isReverseKernel_densityKernel (ν := volume) (ρ := volume) hp hk hk1 hpfin
  have := isMarkovKernel_densityKernel (ρ := volume) hk hk1
  have := isFiniteKernel_densityKernel_reverseDensity (ν := volume) hp hk
  have hmarg := hrev.comp_marginal
  rw [← hKy] at hmarg
  refine Eq.trans ?_ hmarg
  set μ := rgoKernelPi f η y
  have hc : Measurable fun v : Fin k → ℝ => center B η lam y v :=
    (continuous_center B η lam).measurable.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable fun q : (Fin d → ℝ) × ((Fin k → ℝ) × Ω) => gibbsMap G B η lam y q.1 q.2 :=
    hG.comp ((hc.comp (((continuous_mulVec B).measurable.comp measurable_fst).add
      measurable_snd.fst)).prodMk measurable_snd.snd)
  ext s hs
  have hRs : Measurable fun v => rgoKernelPi h (innerStep η lam) (center B η lam y v) s :=
    ((rgoKernelPi h (innerStep η lam)).measurable_coe hs).comp hc
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.lintegral_bind (Kernel.aemeasurable _)
      ((Kernel.measurable_coe _ hs).aemeasurable)]
  have hrv : ∀ v, densityKernel volume (reverseDensity volume p kf) v
      = rgoKernelPi h (innerStep η lam) (center B η lam y v) := fun v =>
    reverse_eq_rgo hh hinth hf hl hB hη y v
  refine lintegral_congr fun x => ?_
  simp_rw [hrv]
  rw [densityKernel_fwdB_apply, forwardKernelPi_apply, Real.toNNReal_one,
    GaussianIncrement.pi_gaussianReal_eq_map (B *ᵥ x), lintegral_map hRs (by fun_prop),
    Measure.prod_apply (measurable_prodMk_left (hF hs))]
  refine lintegral_congr fun ξ => ?_
  have hGc : Measurable (G (center B η lam y (B *ᵥ x + ξ))) := hG.comp measurable_prodMk_left
  have e : (fun i => ξ i + (B *ᵥ x) i) = B *ᵥ x + ξ := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [e, ← hGK, Measure.map_apply hGc hs]
  rfl

/-! ### First moments -/

/-- `√s e^{-s/a} ≤ 1 + a` for `s ≥ 0`, `a > 0`. -/
theorem sqrt_mul_exp_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) :
    √s * Real.exp (-(s / a)) ≤ 1 + a := by
  have h1 : √s ≤ 1 + s := by nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg s]
  have h2 : 1 + s / a ≤ Real.exp (s / a) := by linarith [Real.add_one_le_exp (s / a)]
  have h3 : Real.exp (-(s / a)) * Real.exp (s / a) = 1 := by rw [← Real.exp_add]; simp
  have h4 : 1 + s ≤ (1 + a) * (1 + s / a) := by
    have : (1 + a) * (1 + s / a) = 1 + s + a + s / a := by field_simp; ring
    rw [this]
    have : 0 ≤ s / a := div_nonneg hs ha.le
    linarith
  have he : 0 < Real.exp (-(s / a)) := Real.exp_pos _
  calc √s * Real.exp (-(s / a)) ≤ (1 + s) * Real.exp (-(s / a)) := by gcongr
    _ ≤ (1 + a) * (1 + s / a) * Real.exp (-(s / a)) := by gcongr
    _ ≤ (1 + a) * Real.exp (s / a) * Real.exp (-(s / a)) := by gcongr
    _ = 1 + a := by rw [mul_assoc, mul_comm (Real.exp (s / a)), h3, mul_one]

/-- **First moment of an RGO law.** If `h` is measurable with `∫ e^{-h} < ∞` and `a > 0`, then
`∫ |x| dRGO_h^a(0)(x) < ∞`. -/
theorem lintegral_eDist_rgoKernelPi_lt_top (hh : Measurable h)
    (hinth : Integrable fun x => Real.exp (-h x)) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (eDist x 0) ∂(rgoKernelPi h a 0) ≠ ⊤ := by
  have hZ := rgoNormalizerPi_pos hinth ha 0
  have hdm : Measurable fun x => ENNReal.ofReal (rgoDensityPi h a 0 x) :=
    (measurable_rgoDensityPi hh hinth ha).comp measurable_prodMk_left
  have hem : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (eDist x 0) :=
    ENNReal.measurable_ofReal.comp (continuous_eDist.comp
      (continuous_id.prodMk continuous_const)).measurable
  rw [rgoKernelPi_apply hh hinth ha, lintegral_withDensity_eq_lintegral_mul _ hdm hem]
  refine (lt_of_le_of_lt (lintegral_mono fun x => ?_)
    ((hinth.const_mul ((1 + 2 * a) / rgoNormalizerPi h a 0)).lintegral_lt_top)).ne
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (rgoDensityPi_nonneg _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := sqrt_mul_exp_le (sqDist_nonneg x 0) (by positivity : 0 < 2 * a)
  rw [rgoDensityPi, eDist]
  have e : Real.exp (-h x - sqDist x 0 / (2 * a)) / rgoNormalizerPi h a 0 * √(sqDist x 0)
      = Real.exp (-h x) / rgoNormalizerPi h a 0 * (√(sqDist x 0)
        * Real.exp (-(sqDist x 0 / (2 * a)))) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [e]
  calc Real.exp (-h x) / rgoNormalizerPi h a 0 * (√(sqDist x 0)
        * Real.exp (-(sqDist x 0 / (2 * a))))
      ≤ Real.exp (-h x) / rgoNormalizerPi h a 0 * (1 + 2 * a) := by gcongr
    _ = (1 + 2 * a) / rgoNormalizerPi h a 0 * Real.exp (-h x) := by ring

/-- `|ξ| ≤ ∑ⱼ |ξⱼ|`. -/
theorem eDist_zero_le_sum_abs (ξ : Fin k → ℝ) : eDist ξ 0 ≤ ∑ j, |ξ j| := by
  rw [eDist, ← Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg (ξ j))]
  refine Real.sqrt_le_sqrt ?_
  calc sqDist ξ 0 = ∑ j, |ξ j| ^ 2 := by simp [sqDist, sq_abs]
    _ ≤ (∑ j, |ξ j|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _

/-- **First moment of the standard Gaussian on `Fin k → ℝ`.** -/
theorem lintegral_eDist_gauss_lt_top :
    ∫⁻ ξ, ENNReal.ofReal (eDist ξ 0) ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) ≠ ⊤ := by
  have hint : Integrable (fun ξ : Fin k → ℝ => ∑ j, |ξ j|)
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
    refine integrable_finsetSum _ fun j _ => ?_
    have h1 : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) :=
      ((memLp_id_gaussianReal 1).integrable le_rfl).abs
    exact ((measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j).integrable_comp
      h1.aestronglyMeasurable).2 h1
  refine (lt_of_le_of_lt (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal
    (eDist_zero_le_sum_abs ξ)) hint.lintegral_lt_top).ne

/-! ### The main theorem -/

/-- **Pathwise Lipschitz RGO for a potential plus a PSD quadratic form.** Let `h` be measurable
with `∫ e^{-h} < ∞`, `λ ≥ 0`, `B : Matrix (Fin k) (Fin d) ℝ` with `|B z|² ≤ λ |z|²` for all `z`,
`f x = h x + λ |x|²/2 - |B x|²/2` and `η > 0`. If `rgoKernelPi h (η / (1 + λη))` has a pathwise
`1`-Lipschitz representation, so does `rgoKernelPi f η`. -/
theorem hasLipRep_rgoKernelPi_add_quadratic (hh : Measurable h)
    (hinth : Integrable fun x => Real.exp (-h x))
    (hf : ∀ x, f x = h x + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2) (hl : 0 ≤ lam)
    (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) {η : ℝ} (hη : 0 < η)
    (hrep : HasLipRep (rgoKernelPi h (innerStep η lam))) : HasLipRep (rgoKernelPi f η) := by
  obtain ⟨Ω, _, P, G, hP, hG, hGK, hlip⟩ := hrep
  have hηq : 0 < innerStep η lam := by unfold innerStep; positivity
  have hfm := measurable_of_quad hh hf
  have hintf := integrable_of_quad hh hinth hf hB
  have := isMarkovKernel_rgoKernelPi hfm hintf hη
  have hθ0 : 0 < 1 / (1 + lam * η) := by positivity
  have hθ1 : 1 / (1 + lam * η) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [mul_nonneg hl hη.le]
  have hc : Continuous fun p : (Fin d → ℝ) × (Fin k → ℝ) => center B η lam p.1 p.2 :=
    continuous_center B η lam
  refine hasLipRep_of_contraction (rgoKernelPi f η)
    ((Measure.pi fun _ : Fin k => gaussianReal 0 1).prod P)
    (H := fun y x q => gibbsMap G B η lam y x q) ?_ hθ0 hθ1
    (eDist_gibbsMap_le hlip hl hη hB) (gibbs_stationary hh hinth hf hl hB hη P hG hGK) ?_
  · exact hG.comp ((hc.measurable.comp (measurable_fst.fst.prodMk
      (((continuous_mulVec B).measurable.comp measurable_fst.snd).add
        measurable_snd.fst))).prodMk measurable_snd.snd)
  · -- first moment
    set c := innerStep η lam * √lam
    have hG0 : Measurable (G 0) := hG.comp measurable_prodMk_left
    have hpt : ∀ q : (Fin k → ℝ) × Ω, ENNReal.ofReal (eDist (gibbsMap G B η lam 0 0 q) 0)
        ≤ ENNReal.ofReal c * ENNReal.ofReal (eDist q.1 0)
          + ENNReal.ofReal (eDist (G 0 q.2) 0) := by
      intro q
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by
        have := eDist_nonneg q.1 0; positivity) (eDist_nonneg _ _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have e : center B η lam 0 (B *ᵥ 0 + q.1) = innerStep η lam • (Bᵀ *ᵥ q.1) := by
        simp [center]
      have h1 := eDist_triangle (gibbsMap G B η lam 0 0 q) (G 0 q.2) 0
      have h2 : eDist (gibbsMap G B η lam 0 0 q) (G 0 q.2)
          ≤ eDist (center B η lam 0 (B *ᵥ 0 + q.1)) 0 := Real.sqrt_le_sqrt (hlip _ _ _)
      have h3 : eDist (Bᵀ *ᵥ q.1) 0 ≤ √lam * eDist q.1 0 :=
        eDist_le_of_dot_le (Real.sqrt_nonneg _) (by
          rw [Real.sq_sqrt hl]; exact dot_transpose_le hl hB q.1)
      rw [e, eDist_smul, abs_of_pos hηq] at h2
      have h4 : innerStep η lam * eDist (Bᵀ *ᵥ q.1) 0 ≤ c * eDist q.1 0 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h3 hηq.le
      linarith
    have hm0 : Measurable fun q : (Fin k → ℝ) × Ω => ENNReal.ofReal (eDist q.1 0) :=
      ENNReal.measurable_ofReal.comp ((continuous_eDist.comp
        (continuous_id.prodMk continuous_const)).measurable.comp measurable_fst)
    have hm1 : Measurable fun q : (Fin k → ℝ) × Ω => ENNReal.ofReal c * ENNReal.ofReal
        (eDist q.1 0) := measurable_const.mul hm0
    refine (lt_of_le_of_lt (lintegral_mono hpt) ?_).ne
    rw [lintegral_add_left hm1, lintegral_const_mul _ hm0]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ?_⟩
    · have := lintegral_map (μ := (Measure.pi fun _ : Fin k => gaussianReal 0 1).prod P)
        (f := fun ξ : Fin k → ℝ => ENNReal.ofReal (eDist ξ 0)) (ENNReal.measurable_ofReal.comp
          (continuous_eDist.comp (continuous_id.prodMk continuous_const)).measurable)
          measurable_fst
      rw [Measure.map_fst_prod, measure_univ, one_smul] at this
      rw [← this]
      exact lintegral_eDist_gauss_lt_top.lt_top
    · have := lintegral_map (μ := (Measure.pi fun _ : Fin k => gaussianReal 0 1).prod P)
        (f := fun ω => ENNReal.ofReal (eDist (G 0 ω) 0)) (ENNReal.measurable_ofReal.comp
          ((continuous_eDist.comp (continuous_id.prodMk continuous_const)).measurable.comp hG0))
          measurable_snd
      rw [Measure.map_snd_prod, measure_univ, one_smul] at this
      have hE : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (eDist x 0) :=
        ENNReal.measurable_ofReal.comp (continuous_eDist.comp
          (continuous_id.prodMk continuous_const)).measurable
      have h2 := lintegral_map (μ := P) hE hG0
      rw [hGK] at h2
      rw [← this, ← h2]
      exact (lintegral_eDist_rgoKernelPi_lt_top hh hinth hηq).lt_top

/-- **Separable convex plus PSD quadratic potentials.** Let `f x = ∑ᵢ gᵢ(xᵢ) + λ|x|²/2 - |Bx|²/2`
with each `gᵢ` convex on `ℝ`, `∫ e^{-gᵢ} < ∞`, `λ ≥ 0`, `|B z|² ≤ λ |z|²`, and `η > 0`. Then
`rgoKernelPi f η` has a pathwise `1`-Lipschitz representation. -/
theorem hasLipRep_rgoKernelPi_separable_add_quadratic {g : Fin d → ℝ → ℝ}
    (hconv : ∀ i, ConvexOn ℝ univ (g i))
    (hint : ∀ i, Integrable fun x => Real.exp (-g i x))
    (hf : ∀ x, f x = ∑ i, g i (x i) + lam / 2 * (x ⬝ᵥ x) - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) / 2)
    (hl : 0 ≤ lam) (hB : ∀ z, (B *ᵥ z) ⬝ᵥ (B *ᵥ z) ≤ lam * (z ⬝ᵥ z)) {η : ℝ} (hη : 0 < η) :
    HasLipRep (rgoKernelPi f η) := by
  have hg : ∀ i, Measurable (g i) := fun i =>
    (continuousOn_univ.1 ((hconv i).continuousOn isOpen_univ)).measurable
  have hhm : Measurable fun x : Fin d → ℝ => ∑ i, g i (x i) :=
    Finset.measurable_sum _ fun i _ => (hg i).comp (measurable_pi_apply i)
  have hηq : 0 < innerStep η lam := by unfold innerStep; positivity
  exact hasLipRep_rgoKernelPi_add_quadratic (h := fun x => ∑ i, g i (x i)) hhm
    (ProximalLogConcavePi.integrable_exp_neg_sum (fun x => rfl) hint) hf hl hB hη
    (hasLipRep_rgoKernelPi_separable (fun x => rfl) hconv hint hηq)

end FormalizeSampling.RGOCouplingQuadraticPi
