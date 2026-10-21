module

public import FormalizeSampling.Foundations.VectorCalculus
public import FormalizeSampling.Foundations.HeatKernel

/-!
# Exact Gaussian transition laws of the heat and Ornstein–Uhlenbeck semigroups

**No stochastic calculus is formalised here.** The Ornstein–Uhlenbeck (OU) process
`dXₜ = -a Xₜ dt + √(2a) dWₜ` (overdamped preconditioned Langevin dynamics for the target
`N(0, 1)` with scalar preconditioner `a > 0`) is *represented* by its exact Gaussian (Mehler)
transition law
`Law(Xₜ | X₀ = x) = N(e^{-at} x, 1 - e^{-2at})`,
which is taken here as the **definition** `ouKernel a t`. Nothing in this file proves that an
SDE solution has this transition law; the link to an SDE is modelling, not a theorem.
Likewise the heat semigroup is represented by its Gaussian kernel `heatKernel s x = N(x, s)`,
defined with the mixing law `bind_affineGaussian` and the heat semigroup law (`bind_heat`,
`heatKernel_comp_heatKernel`) in `Foundations/HeatKernel.lean`.

## Conventions

* Mathlib's `gaussianReal m v` takes the **variance** `v : ℝ≥0`.
* The OU transition variance `1 - e^{-2at}` is stored as `Real.toNNReal (1 - e^{-2at})`.
  It is nonnegative (and the truncation is invisible) exactly when `a * t ≥ 0`; every theorem
  below that uses the OU variance assumes `0 ≤ a` and `0 ≤ t` (and `0 < a`, `0 < t` where
  positivity is needed), and `coe_ouVar` records that the truncation is then the identity.
  (`ouKernel_zero` holds for every `a`, since the variance at `t = 0` is `0`.)
* `μ.bind κ` (also written `κ ∘ₘ μ`) is the law of the endpoint of one transition started
  from `μ`; `μ ⊗ₘ κ` is the joint law of `(X₀, Xₜ)`.
* The `IsMarkovKernel` instances for `affineGaussianKernel`, `ouKernel` and `heatKernel` are
  `scoped` to `FormalizeSampling.OU` (no global instances are declared).

## Main results (registry IDs)

* `map_affine_add_noise`: for independent `X`, `Z ∼ N(0,1)` the law of `c X + √w Z` is
  `Law(X).bind (x ↦ N(c x, w)) = (c · Law(X)) ∗ N(0, w)` (`bind_affineGaussian`).
* `bind_ouKernel_gaussianReal`: Gaussian marginals of OU,
  `N(m₀, v₀).bind (ouKernel a t) = N(e^{-at} m₀, 1 + (v₀ - 1) e^{-2at})`.
* Semigroup laws: `bind_ouKernel_ouKernel` / `ouKernel_comp_ouKernel` (OU Chapman–Kolmogorov law),
  `bind_ouKernel_stdGaussian` (invariance of `N(0, 1)`), `ouKernel_zero` (`ouKernel a 0 = id`).
* CE-01-continuous (OU half): `compProd_ouKernel_graph_eq_zero` and
  `map_graph_ne_compProd_ouKernel`: for `a, t > 0` the OU two-time law `μ ⊗ₘ ouKernel a t`
  gives measure zero to the graph of *every* measurable map, hence differs from the two-time
  law of any deterministic flow. The PFG half is in `Examples/GaussianFlowVsOU.lean`.

## Not proved here

* That an OU/Langevin SDE solution (Itô calculus, existence, uniqueness) has the transition
  law `ouKernel a t`, or any Fokker–Planck statement; those are modelling inputs.
* Multi-dimensional or matrix-preconditioned OU kernels; only the scalar case on `ℝ` is done.
* Path-space (more-than-two-time) laws and the Markov process built from these kernels.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FormalizeSampling.OU

/-! ### Affine Gaussian kernels `x ↦ N(c x, w)` -/

/-- The Markov kernel `x ↦ N(c x, w)` on `ℝ` (mean `c x`, variance `w`). -/
noncomputable def affineGaussianKernel (c : ℝ) (w : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := gaussianReal (c * x) w
  measurable' := measurable_gaussianReal_affine c w

/-- Evaluation of the affine Gaussian kernel: `affineGaussianKernel c w x = N(c x, w)`. -/
theorem affineGaussianKernel_apply (c : ℝ) (w : ℝ≥0) (x : ℝ) :
    affineGaussianKernel c w x = gaussianReal (c * x) w := rfl

/-- `affineGaussianKernel c w` is a Markov kernel (each `N(c x, w)` is a probability measure).
Scoped to `FormalizeSampling.OU`. -/
scoped instance isMarkovKernel_affineGaussianKernel (c : ℝ) (w : ℝ≥0) :
    IsMarkovKernel (affineGaussianKernel c w) :=
  ⟨fun x => by rw [affineGaussianKernel_apply]; infer_instance⟩

/-- Probabilistic reading of `bind_affineGaussian`: if `X` and `Z` are independent real random
variables on a probability space, `Z ∼ N(0, 1)`, then for `c : ℝ`, `w : ℝ≥0` the law of
`c X + √w Z` is `Law(X).bind (x ↦ N(c x, w))`. Assumptions: `X`, `Z` measurable. -/
theorem map_affine_add_noise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hZlaw : P.map Z = gaussianReal 0 1) (c : ℝ) (w : ℝ≥0) :
    P.map (fun ω => c * X ω + Real.sqrt w * Z ω) =
      (P.map X).bind (fun x => gaussianReal (c * x) w) := by
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have hind : IndepFun (fun ω => c * X ω) (fun ω => Real.sqrt w * Z ω) P :=
    hXZ.comp (measurable_const_mul c) (measurable_const_mul _)
  have hadd := hind.map_add_eq_map_conv_map (hX.const_mul c) (hZ.const_mul _)
  have hZ' : P.map (fun ω => Real.sqrt w * Z ω) = gaussianReal 0 w := by
    change P.map ((fun x => Real.sqrt w * x) ∘ Z) = gaussianReal 0 w
    rw [← Measure.map_map (measurable_const_mul _) hZ, hZlaw, gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp [Real.sq_sqrt w.coe_nonneg]
  rw [bind_affineGaussian, Measure.map_map (measurable_const_mul c) hX, ← hZ']
  exact hadd

/-! ### The OU kernel -/

/-- The OU transition variance `1 - e^{-2at}`, stored in `ℝ≥0` via `Real.toNNReal`
(the truncation at `0` is the identity when `a t ≥ 0`, see `coe_ouVar`). -/
noncomputable def ouVar (a t : ℝ) : ℝ≥0 := Real.toNNReal (1 - Real.exp (-2 * a * t))

/-- For `0 ≤ a` and `0 ≤ t` the OU transition variance is exactly `1 - e^{-2at}`. -/
theorem coe_ouVar {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (ouVar a t : ℝ) = 1 - Real.exp (-2 * a * t) := by
  rw [ouVar, Real.coe_toNNReal]
  rw [sub_nonneg, Real.exp_le_one_iff]
  nlinarith [mul_nonneg ha ht]

/-- For `0 < a` and `0 < t` the OU transition variance is strictly positive. -/
theorem ouVar_ne_zero {a t : ℝ} (ha : 0 < a) (ht : 0 < t) : ouVar a t ≠ 0 := by
  rw [ouVar, ne_eq, Real.toNNReal_eq_zero, not_le, sub_pos, Real.exp_lt_one_iff]
  nlinarith [mul_pos ha ht]

/-- The OU (Mehler) transition kernel with rate `a`: `ouKernel a t x = N(e^{-at} x, 1 - e^{-2at})`.
It is the exact transition law of `dX = -a X dt + √(2a) dW` (overdamped Langevin for `N(0,1)`
with preconditioner `a`), but here it is a **definition**; no SDE is formalised. Intended
for `0 ≤ a`, `0 ≤ t`. -/
noncomputable def ouKernel (a t : ℝ) : Kernel ℝ ℝ :=
  affineGaussianKernel (Real.exp (-a * t)) (ouVar a t)

/-- Evaluation of the OU kernel: `ouKernel a t x = N(e^{-at} x, ouVar a t)`. -/
theorem ouKernel_apply (a t x : ℝ) :
    ouKernel a t x = gaussianReal (Real.exp (-a * t) * x) (ouVar a t) := rfl

/-- `ouKernel a t` is a Markov kernel. Scoped to `FormalizeSampling.OU`. -/
scoped instance isMarkovKernel_ouKernel (a t : ℝ) : IsMarkovKernel (ouKernel a t) := by
  unfold ouKernel; infer_instance

/-- At time `0` the OU kernel is the identity: `ouKernel a 0 x = δₓ`. -/
theorem ouKernel_zero (a x : ℝ) : ouKernel a 0 x = Measure.dirac x := by
  simp [ouKernel_apply, ouVar, gaussianReal_zero_var]

/-! ### Gaussian marginals and the semigroup laws -/

/-- **Gaussian marginals of OU.** For `0 ≤ a`, `0 ≤ t`, mean `m₀` and variance `v₀ : ℝ≥0`,
`N(m₀, v₀).bind (ouKernel a t) = N(e^{-at} m₀, 1 + (v₀ - 1) e^{-2at})`
(the variance is computed in `ℝ` and is nonnegative, so `Real.toNNReal` does not truncate). -/
theorem bind_ouKernel_gaussianReal {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (m₀ : ℝ) (v₀ : ℝ≥0) :
    (gaussianReal m₀ v₀).bind (ouKernel a t) =
      gaussianReal (Real.exp (-a * t) * m₀)
        (Real.toNNReal (1 + ((v₀ : ℝ) - 1) * Real.exp (-2 * a * t))) := by
  have h : (ouKernel a t : ℝ → Measure ℝ) =
      fun x => gaussianReal (Real.exp (-a * t) * x) (ouVar a t) := rfl
  rw [h, bind_affineGaussian, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal,
    add_zero]
  congr 1
  have he : Real.exp (-2 * a * t) = Real.exp (-a * t) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hpos : 0 ≤ 1 + ((v₀ : ℝ) - 1) * Real.exp (-2 * a * t) := by
    have := coe_ouVar ha ht
    have h1 : 0 ≤ 1 - Real.exp (-2 * a * t) := this ▸ (ouVar a t).coe_nonneg
    nlinarith [v₀.coe_nonneg, Real.exp_pos (-2 * a * t)]
  ext
  rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, coe_ouVar ha ht, Real.coe_toNNReal _ hpos,
    he]
  ring

/-- **Invariance of the target.** For `0 ≤ a`, `0 ≤ t`, the standard Gaussian `N(0, 1)` is
invariant under the OU kernel: `N(0, 1).bind (ouKernel a t) = N(0, 1)`. -/
theorem bind_ouKernel_stdGaussian {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (gaussianReal 0 1).bind (ouKernel a t) = gaussianReal 0 1 := by
  rw [bind_ouKernel_gaussianReal ha ht]
  simp

/-- **OU semigroup law, pointwise form.** For `0 ≤ a`, `0 ≤ s`, `0 ≤ t` and `x : ℝ`,
running OU for time `t` and then for time `s` is running it for time `s + t`:
`(ouKernel a t x).bind (ouKernel a s) = ouKernel a (s + t) x`. -/
theorem bind_ouKernel_ouKernel {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ℝ) :
    (ouKernel a t x).bind (ouKernel a s) = ouKernel a (s + t) x := by
  rw [ouKernel_apply a t x, bind_ouKernel_gaussianReal ha hs, ouKernel_apply]
  congr 1
  · rw [← mul_assoc, ← Real.exp_add]; ring_nf
  · rw [coe_ouVar ha ht, ouVar]
    congr 1
    have h : Real.exp (-2 * a * (s + t)) = Real.exp (-2 * a * t) * Real.exp (-2 * a * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [h]
    ring

/-- **OU semigroup law, kernel form** (Chapman–Kolmogorov): for `0 ≤ a`, `0 ≤ s`,
`0 ≤ t`, `ouKernel a s ∘ₖ ouKernel a t = ouKernel a (s + t)`. -/
theorem ouKernel_comp_ouKernel {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ouKernel a s ∘ₖ ouKernel a t = ouKernel a (s + t) := by
  ext1 x
  rw [Kernel.comp_apply, bind_ouKernel_ouKernel ha hs ht]

/-! ### OU two-time laws charge no graph (CE-01-continuous, OU half) -/

/-- For `0 < a`, `0 < t`, every s-finite initial law `μ` and every measurable map `f : ℝ → ℝ`,
the OU two-time law `μ ⊗ₘ ouKernel a t` of `(X₀, Xₜ)` gives measure `0` to the graph
`{(y, f y)}`: given `X₀`, `Xₜ` is Gaussian with positive variance, hence has no atoms. -/
theorem compProd_ouKernel_graph_eq_zero {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (μ : Measure ℝ)
    [SFinite μ] {f : ℝ → ℝ} (hf : Measurable f) :
    (μ ⊗ₘ ouKernel a t) {p : ℝ × ℝ | p.2 = f p.1} = 0 := by
  have hG : MeasurableSet {p : ℝ × ℝ | p.2 = f p.1} :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  rw [Measure.compProd_apply hG]
  have h0 : ∀ x, ouKernel a t x (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 = f p.1}) = 0 := by
    intro x
    have : NullSingletonClass (ouKernel a t x) := by
      rw [ouKernel_apply]; exact nullSingletonClass_gaussianReal (ouVar_ne_zero ha ht)
    have hset : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 = f p.1} = {f x} := by
      ext z; simp
    rw [hset]
    exact measure_singleton _
  simp_rw [h0]
  exact lintegral_zero

/-- The two-time law `(Y₀, f Y₀)` of a deterministic measurable map `f`, started from a
probability measure `μ`, gives measure `1` to the graph `{(y, f y)}`. -/
theorem map_graph_apply_graph (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) :
    (μ.map (fun y => (y, f y))) {p : ℝ × ℝ | p.2 = f p.1} = 1 := by
  have hG : MeasurableSet {p : ℝ × ℝ | p.2 = f p.1} :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  have hm : Measurable fun y : ℝ => (y, f y) := measurable_id.prodMk hf
  rw [Measure.map_apply hm hG]
  have hpre : (fun y => (y, f y)) ⁻¹' {p : ℝ × ℝ | p.2 = f p.1} = Set.univ := by
    ext y; simp
  rw [hpre, measure_univ]

/-- **No deterministic map reproduces the OU two-time law.** For `0 < a`, `0 < t`, every
probability measure `μ` on `ℝ` and every measurable `f : ℝ → ℝ`, the joint law of `(Y₀, f Y₀)`
with `Y₀ ∼ μ` differs from the OU joint law `μ ⊗ₘ ouKernel a t` of `(X₀, Xₜ)`; the graph of
`f` has measure `1` under the former and `0` under the latter. -/
theorem map_graph_ne_compProd_ouKernel {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : Measurable f) :
    μ.map (fun y => (y, f y)) ≠ μ ⊗ₘ ouKernel a t := by
  intro h
  have h1 := map_graph_apply_graph μ hf
  rw [h, compProd_ouKernel_graph_eq_zero ha ht μ hf] at h1
  exact zero_ne_one h1

end FormalizeSampling.OU
