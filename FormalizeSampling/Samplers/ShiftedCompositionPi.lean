module

public import FormalizeSampling.Samplers.ProximalRegularization
public import FormalizeSampling.Foundations.BakryEmeryGeneralPi

/-!
# Shifted composition on `Fin d → ℝ`: distances, transport cost and Gaussian noise

Status: **Verified** (elementary facts; no hypotheses beyond those stated).

The basic objects of the shifted-composition argument (Altschuler–Chewi 2023) for the `1/k` KL
rate of the proximal sampler on `Fin d → ℝ` (PX-5): the Euclidean distance, the quadratic
transport cost of a coupling, and the Gaussian noise kernel with its shift. The declarations live
in the namespaces `ProximalLogConcaveRate`, `ProximalLogConcavePi`, `ProximalLogConcaveRatePi`,
`ProximalLogConcaveRateGeneralPi`, `RGOCouplingChainPi` and `RGOCouplingQuadraticPi`. The
weak-coupling route (`RGOCouplingWeak`) and the deterministic-sampler couplings
(`DiffusionODELipschitz`) import this module and not the pathwise-coupling modules.

## Main results

* `ProximalLogConcaveRate.eq_iterate`: a Markov chain is the iterate of `ν ↦ P ∘ₘ ν`.
* `ProximalLogConcavePi.sqDist_add_add`: `|(ξ + x) - (ξ + y)|² = |x - y|²`.
* `ProximalLogConcaveRatePi.sqCostPi Λ = ∫⁻ |x - y|² dΛ` and `measurable_ofReal_sqDist`.
* `ProximalLogConcaveRateGeneralPi.gaussNoise η c`: the kernel `(x, y) ↦ N(c (y - x), η I)`;
  `klDiv_gaussNoise` (`KL = t² |x - y|² / (2η)` between the shifted and unshifted noise),
  `shiftNoise` and `map_compProd_gaussNoise` (marginals of a shifted noisy step).
* `RGOCouplingChainPi.eDist`: the Euclidean distance `|x - y|`, with the triangle inequality,
  continuity and `dist ≤ eDist` (sup distance).
* `RGOCouplingQuadraticPi.sqDist_expand`: `|a - b|² = a ⬝ a - 2 a ⬝ b + b ⬝ b`, and
  `dot_self_nonneg`.

## Not proved here

* The shifted-composition bounds themselves: `RGOCouplingWeak` (weak contractive couplings on
  `Fin d → ℝ`) and `ProximalLogConcaveRate` (dimension one).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Set
open FormalizeSampling.ProximalPi
open scoped ENNReal NNReal

namespace FormalizeSampling.ProximalLogConcaveRate

/-- The iterates of a Markov chain are the iterates of `ν ↦ P ∘ₘ ν`:
if `ρ (k + 1) = P ∘ₘ ρ k` for all `k`, then `ρ k = (ν ↦ P ∘ₘ ν)^[k] (ρ 0)`. -/
theorem eq_iterate {α : Type*} [MeasurableSpace α] (P : Kernel α α) (ρ : ℕ → Measure α)
    (hstep : ∀ k, ρ (k + 1) = P ∘ₘ ρ k) (k : ℕ) :
    ρ k = (fun ν => P ∘ₘ ν)^[k] (ρ 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih, hstep]

end FormalizeSampling.ProximalLogConcaveRate

namespace FormalizeSampling.ProximalLogConcavePi

variable {d : ℕ}

/-- `|(x + ξ) - (y + ξ)|² = |x - y|²`. -/
theorem sqDist_add_add (ξ x y : Fin d → ℝ) : sqDist (ξ + x) (ξ + y) = sqDist x y := by
  unfold sqDist
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, add_sub_add_left_eq_sub]

end FormalizeSampling.ProximalLogConcavePi

namespace FormalizeSampling.ProximalLogConcaveRatePi

variable {d : ℕ}

/-- The quadratic transport cost `∫⁻ |x - y|² dΛ(x, y)` on `(Fin d → ℝ)²`. -/
noncomputable def sqCostPi (Λ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (sqDist p.1 p.2) ∂Λ

/-- The squared Euclidean distance (as an `ℝ≥0∞`-valued cost) is measurable. -/
theorem measurable_ofReal_sqDist :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => ENNReal.ofReal (sqDist p.1 p.2) :=
  ENNReal.measurable_ofReal.comp continuous_sqDist.measurable

end FormalizeSampling.ProximalLogConcaveRatePi

namespace FormalizeSampling.ProximalLogConcaveRateGeneralPi

variable {d : ℕ}

/-- The Gaussian noise kernel `(x, y) ↦ N(c (y - x), η I)` on `(Fin d → ℝ)²`. -/
noncomputable def gaussNoise (η c : ℝ) : Kernel ((Fin d → ℝ) × (Fin d → ℝ)) (Fin d → ℝ) :=
  (forwardKernelPi η).comap (fun p : (Fin d → ℝ) × (Fin d → ℝ) => c • (p.2 - p.1))
    (by fun_prop)

/-- The Gaussian noise kernel is a Markov kernel. -/
instance isMarkovKernel_gaussNoise (η c : ℝ) : IsMarkovKernel (gaussNoise (d := d) η c) := by
  unfold gaussNoise
  infer_instance

/-- **KL between shifted noise laws.** For `η > 0`:
`KL(gaussNoise η 0 (x, y) ‖ gaussNoise η t (x, y)) = t² |x - y|² / (2η)`. -/
theorem klDiv_gaussNoise {η : ℝ} (hη : 0 < η) (t : ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    klDiv (gaussNoise η 0 p) (gaussNoise η t p)
      = ENNReal.ofReal (t ^ 2 / (2 * η)) * ENNReal.ofReal (sqDist p.1 p.2) := by
  rw [gaussNoise, gaussNoise, Kernel.comap_apply, Kernel.comap_apply,
    ProximalRegularization.klDiv_forwardKernelPi_apply hη, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold sqDist
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The shifted synchronous Gaussian map `((x, y), n) ↦ (x + n, y + n - t (y - x))`. -/
def shiftNoise (t : ℝ) (z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin d → ℝ)) :
    (Fin d → ℝ) × (Fin d → ℝ) :=
  (z.1.1 + z.2, z.1.2 + z.2 - t • (z.1.2 - z.1.1))

/-- The shifted synchronous Gaussian map is measurable. -/
theorem measurable_shiftNoise (t : ℝ) : Measurable (shiftNoise (d := d) t) := by
  unfold shiftNoise
  fun_prop

/-- **Marginals of a shifted noisy step.** Let `Λ` be finite on `(Fin d → ℝ)²`, `c : ℝ` and `b`
measurable. If `(p, n) ∼ Λ ⊗ₘ gaussNoise η c`, then `b p + n - c (p.2 - p.1)` has law
`N_η ∘ₘ Λ.map b`. -/
theorem map_compProd_gaussNoise (η : ℝ) (Λ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    [IsFiniteMeasure Λ] (c : ℝ) {b : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ}
    (hb : Measurable b) :
    (Λ ⊗ₘ gaussNoise η c).map (fun z => b z.1 + z.2 - c • (z.1.2 - z.1.1))
      = forwardKernelPi η ∘ₘ Λ.map b := by
  have hm : Measurable fun z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin d → ℝ) =>
      b z.1 + z.2 - c • (z.1.2 - z.1.1) :=
    ((hb.comp measurable_fst).add measurable_snd).sub
      ((measurable_fst.snd.sub measurable_fst.fst).const_smul c)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map ((forwardKernelPi η).measurable_coe hs) hb]
  refine lintegral_congr fun p => ?_
  set m := c • (p.2 - p.1)
  have hT : Measurable fun n : Fin d → ℝ => b p + n - m := by fun_prop
  have e : (forwardKernelPi η m).map (fun n => b p + n - m) = forwardKernelPi η (b p) := by
    rw [forwardKernelPi_apply, forwardKernelPi_apply, GaussianIncrement.pi_gaussianReal_eq_map m,
      GaussianIncrement.pi_gaussianReal_eq_map (b p), Measure.map_map hT (by fun_prop)]
    congr 1
    funext y i
    simp only [Function.comp, Pi.add_apply, Pi.sub_apply]
    ring
  rw [gaussNoise, Kernel.comap_apply, ← e, Measure.map_apply hT hs]
  rfl

end FormalizeSampling.ProximalLogConcaveRateGeneralPi

namespace FormalizeSampling.RGOCouplingChainPi

variable {d : ℕ}

/-! ### The Euclidean distance on `Fin d → ℝ` -/

/-- The Euclidean distance `|x - y| = √(∑ᵢ (xᵢ - yᵢ)²)` on `Fin d → ℝ`. -/
noncomputable def eDist (x y : Fin d → ℝ) : ℝ := √(sqDist x y)

/-- The Euclidean distance is the distance of `EuclideanSpace ℝ (Fin d)`. -/
theorem eDist_eq_dist (x y : Fin d → ℝ) :
    eDist x y = dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y) := by
  rw [EuclideanSpace.dist_eq, eDist, sqDist]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.dist_eq, sq_abs]

/-- `0 ≤ |x - y|`. -/
theorem eDist_nonneg (x y : Fin d → ℝ) : 0 ≤ eDist x y := Real.sqrt_nonneg _

/-- `|x - y|² = sqDist x y`. -/
theorem eDist_sq (x y : Fin d → ℝ) : eDist x y ^ 2 = sqDist x y :=
  Real.sq_sqrt (sqDist_nonneg x y)

/-- `|x - x| = 0`. -/
theorem eDist_self (x : Fin d → ℝ) : eDist x x = 0 := by
  simp [eDist, sqDist]

/-- Triangle inequality for the Euclidean distance. -/
theorem eDist_triangle (x y z : Fin d → ℝ) : eDist x z ≤ eDist x y + eDist y z := by
  rw [eDist_eq_dist, eDist_eq_dist, eDist_eq_dist]
  exact dist_triangle _ _ _

/-- Symmetry of the Euclidean distance. -/
theorem eDist_comm (x y : Fin d → ℝ) : eDist x y = eDist y x := by
  rw [eDist_eq_dist, eDist_eq_dist, dist_comm]

/-- The Euclidean distance is jointly continuous. -/
theorem continuous_eDist : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) => eDist p.1 p.2 :=
  continuous_sqDist.sqrt

/-- The sup distance is at most the Euclidean distance. -/
theorem dist_le_eDist (x y : Fin d → ℝ) : dist x y ≤ eDist x y := by
  refine (dist_pi_le_iff (eDist_nonneg x y)).2 fun i => ?_
  rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Comparison of squared distances from comparison of distances. -/
theorem sqDist_le_of_eDist_le {a b c e : Fin d → ℝ} (h : eDist a b ≤ eDist c e) :
    sqDist a b ≤ sqDist c e := by
  rw [← eDist_sq, ← eDist_sq]
  exact pow_le_pow_left₀ (eDist_nonneg a b) h 2

end FormalizeSampling.RGOCouplingChainPi

namespace FormalizeSampling.RGOCouplingQuadraticPi

variable {d : ℕ}

/-! ### Euclidean algebra -/

/-- Expansion `|a - b|² = a ⬝ a - 2 a ⬝ b + b ⬝ b`. -/
theorem sqDist_expand (a b : Fin d → ℝ) :
    sqDist a b = a ⬝ᵥ a - 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
  simp only [sqDist, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|a - 0|² = a ⬝ a`. -/
theorem sqDist_zero_right (a : Fin d → ℝ) : sqDist a 0 = a ⬝ᵥ a := by
  rw [sqDist_expand]
  simp

/-- `a ⬝ a ≥ 0`. -/
theorem dot_self_nonneg (a : Fin d → ℝ) : 0 ≤ a ⬝ᵥ a := by
  rw [← sqDist_zero_right]
  exact sqDist_nonneg _ _

end FormalizeSampling.RGOCouplingQuadraticPi
