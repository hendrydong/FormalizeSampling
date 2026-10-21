module

public import FormalizeSampling.Samplers.DiffusionODESmooth
public import FormalizeSampling.Samplers.DiffusionGaussianOutput
public import FormalizeSampling.Samplers.ShiftedCompositionPi
public import FormalizeSampling.Foundations.MeasureHelpers
public import FormalizeSampling.Foundations.BakryEmeryGeneralPi

/-!
# Deterministic reverse samplers are stable in transport distance (not in TV)

Status: **Verified** (no named hypotheses; the Lipschitz and accuracy assumptions are explicit
regularity assumptions, satisfiable e.g. for Gaussian data, `pf_isoGauss_coupling`).

Setting of `Samplers/DiffusionODESeparation.lean`: deterministic reverse samplers
`algLaw 0 m` (zero reverse variance, `zeroVar`) started at `q_N = N(0, I)` on `Fin d → ℝ`, whose
reverse step `k` is the Dirac kernel `y ↦ δ_{m_k(y)}`. Such a sampler is the push-forward of
`N(0, I)` by the composed map `Φ_k = m_{k+1} ∘ ⋯ ∘ m_N` (`detFlow`, `algLaw_zeroVar_eq_map`).
Distances are Euclidean: `eDist x y = |x - y| = √(sqDist x y)` (`RGOCouplingChainPi.eDist`); the
quadratic transport cost of a coupling `Γ` is `sqCostPi Γ = ∫⁻ |x - y|² dΓ`
(`ProximalLogConcaveRatePi.sqCostPi`).

## Main results

* `eDist_detFlow_le` (**synchronous coupling, pointwise**): compare a learned deterministic
  sampler `m` with a reference one `m'` (e.g. the same discretisation driven by the exact score).
  If on steps `k < i ≤ N` the reference map is `L_i`-Lipschitz (Euclidean, `L_i ≥ 0`) and
  `|m_i(y) - m'_i(y)| ≤ δ_i` for all `y`, then for **every** starting point `y`
  `|Φ_k(y) - Φ'_k(y)| ≤ B_k := ∑_{k < i ≤ N} (∏_{k < j < i} L_j) δ_i` (`lipBound`).
* `exists_coupling_detOutput`: hence there is a coupling `Γ` of the two output laws
  `q_k = algLaw 0 m N k`, `q'_k = algLaw 0 m' N k` (the image of `N(0, I)` under
  `y ↦ (Φ_k(y), Φ'_k(y))`) with `|x - x'| ≤ B_k` `Γ`-a.s. (so `W_∞(q_k, q'_k) ≤ B_k`) and
  `∫ |x - x'|² dΓ ≤ B_k²` (so `W_2(q_k, q'_k) ≤ B_k`).
* `exists_coupling_detMean` (**score-affine samplers**): for `m_i = A_i + b_i s_i` (`detMean`)
  with learned score `s` uniformly `ε_i`-accurate,
  `∑ⱼ (s_i(y)ⱼ - ∂ⱼ log p_i(y))² ≤ ε_i²`, and the **exact-score** map
  `A_i + b_i ∇ log p_i` `L_i`-Lipschitz, the output is coupled with the exact-score deterministic
  output within `∑_i (∏_{1 < j < i} L_j) |b_i| ε_i` (a.s. and in `L²`). No regularity of the
  learned score or of the score error is required.
* `pf_isoGauss_coupling` (**example**): Gaussian data `N(0, v I)` and the exponential-integrator
  probability-flow step `pfMean`. The exact map is `y ↦ g_k y` (`pfMean_trueScore_isoGauss`,
  `g_k = α_k⁻¹ - (α_k⁻¹ - 1)/s_k`, `pfGain`), so for every uniformly `ε_i`-accurate learned score
  the output is coupled with `N(0, w_1 I)` (`w = algVar g 0`, the exact-score output) within
  `∑_i (∏_{1 < j < i} |g_j|) |α_i⁻¹ - 1| ε_i`.
* `smooth_separation_tv_far_w2_close` (**TV versus transport, with DF-7**): for every `ε, η > 0`
  the analytic, uniformly `ε`-accurate learned score of `Samplers/DiffusionODESmooth.lean` makes
  the deterministic output `q_1` satisfy `TV(p_1, q_1) ≥ 1 - η`, **and** `q_1` is coupled with
  the exact-score deterministic output `q*_1` with `|x - x*| ≤ |b_2| ε` almost surely
  (`W_∞, W_2 ≤ |b_2| ε`). Uniform score accuracy controls the deterministic sampler in transport
  distance, not in TV.

Relation to the literature: the pairing is implicit in the example of Li–Wei–Chen–Chi (2023,
arXiv:2306.09251, §3.2), who suggest a Wasserstein metric as a way around their TV counterexample.
The coupling bound is a discrete Grönwall-type stability estimate; for the continuous-time ODE and
Lipschitz test functions, compare Beltran-Velez et al. (2026, arXiv:2606.19162, Prop. 3.2).

## Not proved here

* No statement about `W_2(p_1, q*_1)` (the discretisation error of the exact-score deterministic
  sampler), so no end-to-end `W_2(p_1, q_1)` bound; and no triangle inequality for `W_2` is
  formalised (only explicit couplings are given; `W_2` itself is not defined in the library).
* In `smooth_separation_tv_far_w2_close` the TV lower bound is against the data marginal `p_1`,
  not against `q*_1` (that would need `q*_1 ≪ Lebesgue`, i.e. non-singular exact maps).
* The Lipschitz constant of the exact-score map is a hypothesis; that it holds for general data
  (e.g. bounded `∇² log p_k` for compactly supported data at positive noise level) is not proved,
  only the Gaussian example is.
* No TV or KL bound under a `C¹`-closeness assumption on the learned maps (change of variables
  for the perturbed flow); see `Flow/DeterministicStepPi.lean` for the one-step density formula.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionODELipschitz

open FormalizeSampling.MeasureHelpers (pi_dirac)

open FormalizeSampling.Diffusion FormalizeSampling.DiffusionODESeparation
open FormalizeSampling.DiffusionODESmooth FormalizeSampling.DiffusionGaussian
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingChainPi
open FormalizeSampling.ProximalLogConcaveRatePi (sqCostPi)
open FormalizeSampling.ProximalSharpGaussianPi (scalePi)
open FormalizeSampling.DiffusionDiscretization (exactScore measurable_exactScore)

variable {d : ℕ}

/-! ### Deterministic samplers are push-forwards -/

/-- A zero-variance Gaussian step is a Dirac step: `N(m(y), 0 · I) = δ_{m(y)}`. -/
theorem gaussKernelPi_zero_apply {m : (Fin d → ℝ) → Fin d → ℝ} (hm : Measurable m)
    (y : Fin d → ℝ) : gaussKernelPi 0 m hm y = Measure.dirac (m y) := by
  rw [gaussKernelPi_apply]
  simp_rw [gaussianReal_zero_var]
  exact pi_dirac _

/-- Auxiliary: the composition of the first `j` deterministic reverse maps from index `N`,
`m_{N-j+1} ∘ ⋯ ∘ m_N`. -/
noncomputable def detFlowAux (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) :
    ℕ → (Fin d → ℝ) → Fin d → ℝ
  | 0 => id
  | j + 1 => m (N - j) ∘ detFlowAux m N j

/-- The deterministic reverse flow from index `N` to index `k ≤ N`:
`Φ_k = m_{k+1} ∘ ⋯ ∘ m_N` (`detFlow_self`, `detFlow_of_lt`). -/
noncomputable def detFlow (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (N k : ℕ) :
    (Fin d → ℝ) → Fin d → ℝ :=
  detFlowAux m N (N - k)

/-- The auxiliary flow is measurable when every `m_k` is. -/
theorem measurable_detFlowAux {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hm : ∀ k, Measurable (m k))
    (N j : ℕ) : Measurable (detFlowAux m N j) := by
  induction j with
  | zero => exact measurable_id
  | succ j ih => exact (hm _).comp ih

/-- The deterministic flow is measurable when every `m_k` is. -/
theorem measurable_detFlow {m : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hm : ∀ k, Measurable (m k))
    (N k : ℕ) : Measurable (detFlow m N k) :=
  measurable_detFlowAux hm N (N - k)

/-- `Φ_N = id`. -/
theorem detFlow_self (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) : detFlow m N N = id := by
  simp [detFlow, detFlowAux]

/-- For `k < N`: `Φ_k = m_{k+1} ∘ Φ_{k+1}`. -/
theorem detFlow_of_lt (m : ℕ → (Fin d → ℝ) → Fin d → ℝ) {N k : ℕ} (hk : k < N) :
    detFlow m N k = m (k + 1) ∘ detFlow m N (k + 1) := by
  have h : N - k = (N - (k + 1)) + 1 := by omega
  rw [detFlow, h, detFlowAux, detFlow, show N - (N - (k + 1)) = k + 1 by omega]

/-- `Φ_k` depends only on the maps `m_i`, `k < i ≤ N`. -/
theorem detFlow_congr {m m' : ℕ → (Fin d → ℝ) → Fin d → ℝ} {N k : ℕ} (hk : k ≤ N)
    (h : ∀ i, k < i → i ≤ N → m i = m' i) : detFlow m N k = detFlow m' N k := by
  induction hn : N - k generalizing k with
  | zero =>
    obtain rfl : k = N := by omega
    rw [detFlow_self, detFlow_self]
  | succ n ih =>
    have hlt : k < N := by omega
    rw [detFlow_of_lt m hlt, detFlow_of_lt m' hlt, h (k + 1) (by omega) (by omega),
      ih (by omega) (fun i hi hiN => h i (by omega) hiN) (by omega)]

/-- Auxiliary form of `algLaw_zeroVar_eq_map`. -/
theorem algLawAux_zeroVar_eq_map {m : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hm : ∀ k, Measurable (m k)) (N j : ℕ) :
    algLawAux zeroVar m hm N j = (stdGaussianPi d).map (detFlowAux m N j) := by
  induction j with
  | zero => simp [algLawAux, detFlowAux]
  | succ j ih =>
    rw [algLawAux, ih]
    have : algKernel zeroVar m hm (N - j) = Kernel.deterministic (m (N - j)) (hm _) := by
      ext y : 1
      rw [Kernel.deterministic_apply]
      exact gaussKernelPi_zero_apply _ y
    rw [this, Measure.deterministic_comp_eq_map, Measure.map_map (hm _)
      (measurable_detFlowAux hm N j)]
    rfl

/-- **A deterministic sampler is a push-forward.** With zero reverse variance, the algorithm's
law at index `k` is the image of `N(0, I)` under the composed reverse map:
`algLaw 0 m N k = Φ_k # N(0, I)` (law equality). -/
theorem algLaw_zeroVar_eq_map {m : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hm : ∀ k, Measurable (m k)) (N k : ℕ) :
    algLaw zeroVar m hm N k = (stdGaussianPi d).map (detFlow m N k) :=
  algLawAux_zeroVar_eq_map hm N (N - k)

/-! ### The stability bound -/

/-- The error-propagation bound `B_k = ∑_{k < i ≤ N} (∏_{k < j < i} L_j) δ_i`: the one-step
error `δ_i` made at step `i` is amplified by the Lipschitz constants of the later steps
`i - 1, …, k + 1` of the reference sampler. -/
noncomputable def lipBound (L δ : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc k N, (∏ j ∈ Finset.Ioo k i, L j) * δ i

/-- `B_N = 0`. -/
theorem lipBound_self (L δ : ℕ → ℝ) (N : ℕ) : lipBound L δ N N = 0 := by
  simp [lipBound]

/-- The recursion `B_k = L_{k+1} B_{k+1} + δ_{k+1}` for `k < N`. -/
theorem lipBound_of_lt (L δ : ℕ → ℝ) {N k : ℕ} (hk : k < N) :
    lipBound L δ N k = L (k + 1) * lipBound L δ N (k + 1) + δ (k + 1) := by
  unfold lipBound
  rw [← Finset.Icc_add_one_left_eq_Ioc, ← Finset.Ioc_insert_left (by omega : k + 1 ≤ N),
    Finset.sum_insert (by simp), Finset.mul_sum]
  have h0 : Finset.Ioo k (k + 1) = ∅ := by
    ext j; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
  rw [h0, Finset.prod_empty, one_mul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioc] at hi
  rw [← Finset.Ico_add_one_left_eq_Ioo, ← Finset.Ioo_insert_left (by omega : k + 1 < i),
    Finset.prod_insert (by simp), mul_assoc]

/-- **Synchronous-coupling stability of deterministic samplers (pointwise).** Let `m, m'` be
two families of reverse maps (learned and reference), `k ≤ N`, and for `k < i ≤ N`:
`L_i ≥ 0`, the reference map `m'_i` is `L_i`-Lipschitz for the Euclidean distance, and
`|m_i(y) - m'_i(y)| ≤ δ_i` for all `y`. Then for every `y`,
`|Φ_k(y) - Φ'_k(y)| ≤ ∑_{k < i ≤ N} (∏_{k < j < i} L_j) δ_i`. No regularity of `m` is needed. -/
theorem eDist_detFlow_le {m m' : ℕ → (Fin d → ℝ) → Fin d → ℝ} {L δ : ℕ → ℝ} {N k : ℕ}
    (hk : k ≤ N) (hL0 : ∀ i, k < i → i ≤ N → 0 ≤ L i)
    (hLip : ∀ i, k < i → i ≤ N → ∀ x y, eDist (m' i x) (m' i y) ≤ L i * eDist x y)
    (hδ : ∀ i, k < i → i ≤ N → ∀ y, eDist (m i y) (m' i y) ≤ δ i) (y : Fin d → ℝ) :
    eDist (detFlow m N k y) (detFlow m' N k y) ≤ lipBound L δ N k := by
  induction hn : N - k generalizing k with
  | zero =>
    obtain rfl : k = N := by omega
    simp [detFlow_self, lipBound_self, eDist_self]
  | succ n ih =>
    have hlt : k < N := by omega
    have ih' := ih (k := k + 1) (by omega) (fun i hi hiN => hL0 i (by omega) hiN)
      (fun i hi hiN => hLip i (by omega) hiN) (fun i hi hiN => hδ i (by omega) hiN) (by omega)
    rw [detFlow_of_lt m hlt, detFlow_of_lt m' hlt, lipBound_of_lt L δ hlt]
    set u := detFlow m N (k + 1) y
    set u' := detFlow m' N (k + 1) y
    calc eDist (m (k + 1) u) (m' (k + 1) u')
        ≤ eDist (m (k + 1) u) (m' (k + 1) u) + eDist (m' (k + 1) u) (m' (k + 1) u') :=
          eDist_triangle _ _ _
      _ ≤ δ (k + 1) + L (k + 1) * eDist u u' :=
          add_le_add (hδ _ (by omega) (by omega) u) (hLip _ (by omega) (by omega) u u')
      _ ≤ δ (k + 1) + L (k + 1) * lipBound L δ N (k + 1) := by
          gcongr
          exact hL0 _ (by omega) (by omega)
      _ = L (k + 1) * lipBound L δ N (k + 1) + δ (k + 1) := by ring

/-- **A coupling with uniformly bounded displacement.** If `ν` is a probability measure and
`|f(y) - g(y)| ≤ B` for all `y` (`f, g` measurable), then `Γ = (f, g) # ν` is a probability
measure with marginals `f # ν` and `g # ν`, `|x - x'| ≤ B` `Γ`-a.s., and
`∫⁻ |x - x'|² dΓ ≤ B²`. -/
theorem exists_coupling_of_eDist_le (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    {f g : (Fin d → ℝ) → Fin d → ℝ} (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hB : ∀ y, eDist (f y) (g y) ≤ B) :
    ∃ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure Γ ∧
      Γ.map Prod.fst = ν.map f ∧ Γ.map Prod.snd = ν.map g ∧
      (∀ᵐ p ∂Γ, eDist p.1 p.2 ≤ B) ∧ sqCostPi Γ ≤ ENNReal.ofReal (B ^ 2) := by
  have hfg : Measurable fun y => (f y, g y) := hf.prodMk hg
  refine ⟨ν.map fun y => (f y, g y), inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hfg]; rfl
  · rw [Measure.map_map measurable_snd hfg]; rfl
  · rw [ae_map_iff hfg.aemeasurable (measurableSet_le continuous_eDist.measurable
      measurable_const)]
    exact Filter.Eventually.of_forall hB
  · unfold sqCostPi
    rw [lintegral_map ProximalLogConcaveRatePi.measurable_ofReal_sqDist hfg]
    calc ∫⁻ y, ENNReal.ofReal (sqDist (f y) (g y)) ∂ν
        ≤ ∫⁻ _, ENNReal.ofReal (B ^ 2) ∂ν := by
          refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
          rw [← eDist_sq]
          exact pow_le_pow_left₀ (eDist_nonneg _ _) (hB y) 2
      _ = ENNReal.ofReal (B ^ 2) := by simp

/-- **Stability of deterministic samplers in `W_∞` and `W_2`.** Under the hypotheses of
`eDist_detFlow_le` (measurable maps; for `k < i ≤ N`: `L_i ≥ 0`, `m'_i` Euclidean
`L_i`-Lipschitz, `sup_y |m_i(y) - m'_i(y)| ≤ δ_i`), there is a coupling `Γ` of the deterministic
outputs `q_k = algLaw 0 m N k` and `q'_k = algLaw 0 m' N k` (both started at `N(0, I)`) with
`|x - x'| ≤ B_k` `Γ`-a.s. and `∫⁻ |x - x'|² dΓ ≤ B_k²`, `B_k = lipBound L δ N k`. -/
theorem exists_coupling_detOutput {m m' : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hm : ∀ k, Measurable (m k)) (hm' : ∀ k, Measurable (m' k)) {L δ : ℕ → ℝ} {N k : ℕ}
    (hk : k ≤ N) (hL0 : ∀ i, k < i → i ≤ N → 0 ≤ L i)
    (hLip : ∀ i, k < i → i ≤ N → ∀ x y, eDist (m' i x) (m' i y) ≤ L i * eDist x y)
    (hδ : ∀ i, k < i → i ≤ N → ∀ y, eDist (m i y) (m' i y) ≤ δ i) :
    ∃ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure Γ ∧
      Γ.map Prod.fst = algLaw zeroVar m hm N k ∧ Γ.map Prod.snd = algLaw zeroVar m' hm' N k ∧
      (∀ᵐ p ∂Γ, eDist p.1 p.2 ≤ lipBound L δ N k) ∧
      sqCostPi Γ ≤ ENNReal.ofReal (lipBound L δ N k ^ 2) := by
  rw [algLaw_zeroVar_eq_map, algLaw_zeroVar_eq_map]
  exact exists_coupling_of_eDist_le _ (measurable_detFlow hm N k) (measurable_detFlow hm' N k)
    (eDist_detFlow_le hk hL0 hLip hδ)

/-! ### Score-affine deterministic samplers -/

/-- **One score-affine step.** If `∑ⱼ (s_k(y)ⱼ - s'_k(y)ⱼ)² ≤ ε²` with `ε ≥ 0`, then
`|(A_k(y) + b_k s_k(y)) - (A_k(y) + b_k s'_k(y))| ≤ |b_k| ε`. -/
theorem eDist_detMean_le (A : ℕ → (Fin d → ℝ) → Fin d → ℝ) (b : ℕ → ℝ)
    (s s' : ℕ → (Fin d → ℝ) → Fin d → ℝ) (k : ℕ) (y : Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∑ j, (s k y j - s' k y j) ^ 2 ≤ ε ^ 2) :
    eDist (detMean A b s k y) (detMean A b s' k y) ≤ |b k| * ε := by
  have e : sqDist (detMean A b s k y) (detMean A b s' k y) =
      b k ^ 2 * ∑ j, (s k y j - s' k y j) ^ 2 := by
    rw [sqDist, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [detMean]; ring
  rw [eDist, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have h' : √(∑ j, (s k y j - s' k y j) ^ 2) ≤ ε := by
    simpa [Real.sqrt_sq hε] using Real.sqrt_le_sqrt h
  exact mul_le_mul_of_nonneg_left h' (abs_nonneg _)

/-- **Stability of score-affine deterministic samplers.** Data `μ`, grid `t`, measurable
`A` and learned score `s`, deterministic update `m_i(y) = A_i(y) + b_i s_i(y)` (`detMean`),
`k ≤ N`. Assume for `k < i ≤ N`:
* uniform score accuracy `∑ⱼ (s_i(y)ⱼ - ∂ⱼ log p_i(y))² ≤ ε_i²` for all `y`, `ε_i ≥ 0`;
* the **exact-score** update `y ↦ A_i(y) + b_i ∇ log p_i(y)` is Euclidean `L_i`-Lipschitz,
  `L_i ≥ 0`.
Then there is a coupling `Γ` of the learned deterministic output `q_k = algLaw 0 (detMean A b s)`
and the exact-score deterministic output `q*_k = algLaw 0 (detMean A b ∇ log p)` with
`|x - x*| ≤ B` `Γ`-a.s. and `∫⁻ |x - x*|² dΓ ≤ B²`,
`B = ∑_{k < i ≤ N} (∏_{k < j < i} L_j) |b_i| ε_i`. -/
theorem exists_coupling_detMean (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ)
    {A : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hA : ∀ k, Measurable (A k)) (b : ℕ → ℝ)
    {s : ℕ → (Fin d → ℝ) → Fin d → ℝ} (hs : ∀ k, Measurable (s k)) {ε L : ℕ → ℝ} {N k : ℕ}
    (hk : k ≤ N) (hε0 : ∀ i, k < i → i ≤ N → 0 ≤ ε i)
    (hacc : ∀ i, k < i → i ≤ N → ∀ y,
      ∑ j, (s i y j - score (fwdDensity μ t i) y j) ^ 2 ≤ ε i ^ 2)
    (hL0 : ∀ i, k < i → i ≤ N → 0 ≤ L i)
    (hLip : ∀ i, k < i → i ≤ N → ∀ x y,
      eDist (detMean A b (exactScore μ t) i x) (detMean A b (exactScore μ t) i y) ≤
        L i * eDist x y) :
    ∃ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure Γ ∧
      Γ.map Prod.fst = algLaw zeroVar (detMean A b s) (measurable_detMean hA b hs) N k ∧
      Γ.map Prod.snd = algLaw zeroVar (detMean A b (exactScore μ t))
        (measurable_detMean hA b (measurable_exactScore μ t)) N k ∧
      (∀ᵐ p ∂Γ, eDist p.1 p.2 ≤ lipBound L (fun i => |b i| * ε i) N k) ∧
      sqCostPi Γ ≤ ENNReal.ofReal (lipBound L (fun i => |b i| * ε i) N k ^ 2) :=
  exists_coupling_detOutput _ _ hk hL0 hLip fun i hi hiN y =>
    eDist_detMean_le A b s (exactScore μ t) i y (hε0 i hi hiN) (hacc i hi hiN y)

/-! ### Example: Gaussian data and the probability-flow step -/

/-- The gain `g_k = α_k⁻¹ - (α_k⁻¹ - 1)/s_k` of the exact-score probability-flow step for
Gaussian data `N(0, v I)` (`s_k = gaussVar v t k`). -/
noncomputable def pfGain (v : ℝ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  (fwdScale t k)⁻¹ - pfCoeff t k / gaussVar v t k

/-- **The exact-score probability-flow step is linear for Gaussian data.** For `v > 0`,
`t 0 = 0`, `t` strictly increasing and `k ≥ 1`:
`pfMean t (∇ log p) k y = α_k⁻¹ y + (α_k⁻¹ - 1)(-y/s_k) = g_k y`. -/
theorem pfMean_trueScore_isoGauss {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {k : ℕ} (hk : 1 ≤ k) :
    pfMean t (exactScore (isoGauss d v) t) k = scalePi (pfGain v t k) := by
  have he : exactScore (isoGauss d v) t k = fun y => (-(gaussVar v t k)⁻¹) • y :=
    exactScore_isoGauss hv h0 ht hk
  funext y i
  simp only [pfMean, detMean, pfLin, he, scalePi, pfGain, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scaling by `c` is `|c|`-Lipschitz for the Euclidean distance (with equality). -/
theorem eDist_scalePi (c : ℝ) (x y : Fin d → ℝ) :
    eDist (scalePi c x) (scalePi c y) = |c| * eDist x y := by
  have e : sqDist (scalePi c x) (scalePi c y) = c ^ 2 * sqDist x y := by
    rw [sqDist, sqDist, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [scalePi]; ring
  rw [eDist, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, eDist]

/-- **Example (Gaussian data, probability-flow sampler).** Data `N(0, v I)` with `v > 0`,
`t 0 = 0`, `t` strictly increasing, `1 ≤ N`, learned score `s` measurable and uniformly accurate
on steps `2 ≤ i ≤ N`: `∑ⱼ (s_i(y)ⱼ - ∂ⱼ log p_i(y))² ≤ ε_i²`, `ε_i ≥ 0`. Then the deterministic
probability-flow output `q_1 = algLaw 0 (pfMean t s) N 1` is coupled with the exact-score output
`N(0, w_1 I)` (`w_1 = algVar g 0 N 1`, `g = pfGain v t`) by some `Γ` with
`|x - x*| ≤ B` a.s. and `∫⁻ |x - x*|² dΓ ≤ B²`,
`B = ∑_{1 < i ≤ N} (∏_{1 < j < i} |g_j|) |α_i⁻¹ - 1| ε_i`. -/
theorem pf_isoGauss_coupling {v : ℝ} (hv : 0 < v) {t : ℕ → ℝ} (h0 : t 0 = 0)
    (ht : StrictMono t) {N : ℕ} (hN : 1 ≤ N) {s : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hs : ∀ k, Measurable (s k)) {ε : ℕ → ℝ} (hε0 : ∀ i, 1 < i → i ≤ N → 0 ≤ ε i)
    (hacc : ∀ i, 1 < i → i ≤ N → ∀ y,
      ∑ j, (s i y j - score (fwdDensity (isoGauss d v) t i) y j) ^ 2 ≤ ε i ^ 2) :
    ∃ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure Γ ∧
      Γ.map Prod.fst = algLaw zeroVar (pfMean t s) (measurable_detMean (measurable_pfLin t) _ hs)
        N 1 ∧
      Γ.map Prod.snd = isoGauss d (algVar (pfGain v t) zeroVar N 1) ∧
      (∀ᵐ p ∂Γ, eDist p.1 p.2 ≤
        lipBound (fun i => |pfGain v t i|) (fun i => |pfCoeff t i| * ε i) N 1) ∧
      sqCostPi Γ ≤ ENNReal.ofReal
        (lipBound (fun i => |pfGain v t i|) (fun i => |pfCoeff t i| * ε i) N 1 ^ 2) := by
  obtain ⟨Γ, hΓ, h1, h2, h3, h4⟩ := exists_coupling_detMean (isoGauss d v) t
    (measurable_pfLin t) (pfCoeff t) hs (L := fun i => |pfGain v t i|) hN hε0 hacc
    (fun _ _ _ => abs_nonneg _) (fun i hi _ x y => by
      change eDist (pfMean t _ i x) (pfMean t _ i y) ≤ _
      rw [pfMean_trueScore_isoGauss hv h0 ht (by omega), eDist_scalePi])
  refine ⟨Γ, hΓ, h1, ?_, h3, h4⟩
  rw [h2]
  exact algLaw_eq_isoGauss (pfGain v t) zeroVar _ _
    (fun i hi _ => pfMean_trueScore_isoGauss hv h0 ht (by omega)) le_rfl hN

/-! ### TV-far but transport-close: the smooth counterexample revisited -/

/-- **One perturbed step.** If `m_i = m'_i` for `k + 1 < i ≤ N` and `|m_{k+1}(y) - m'_{k+1}(y)| ≤ δ`
for all `y` (`k < N`), then `|Φ_k(y) - Φ'_k(y)| ≤ δ` for all `y` (no Lipschitz assumption). -/
theorem eDist_detFlow_le_of_last {m m' : ℕ → (Fin d → ℝ) → Fin d → ℝ} {N k : ℕ} (hk : k < N)
    (heq : ∀ i, k + 1 < i → i ≤ N → m i = m' i) {δ : ℝ}
    (hδ : ∀ y, eDist (m (k + 1) y) (m' (k + 1) y) ≤ δ) (y : Fin d → ℝ) :
    eDist (detFlow m N k y) (detFlow m' N k y) ≤ δ := by
  rw [detFlow_of_lt m hk, detFlow_of_lt m' hk, detFlow_congr (by omega) heq]
  exact hδ _

/-- **Deterministic sampler with an analytic uniformly accurate score: TV-far, `W_2`-close.**
Data `μ` (probability law), `d ≥ 1`, `t_0 < t_1`, `N ≥ 2`, measurable `A`, `b_2 ≠ 0`, `ε > 0`,
`η > 0`. There are a measurable learned score `s` and an analytic field `E` (the construction
of `Samplers/DiffusionODESmooth.lean`) with
1. `∑ᵢ E(z)ᵢ² ≤ ε²` for all `z`, `s_k = ∇ log p_k` for `k ≠ 2`,
   `s_2(y) = ∇ log p_2(y) + E(z(y))` (`z` the exact update);
2. uniform accuracy `∑ᵢ (s_k(y)ᵢ - ∂ᵢ log p_k(y))² ≤ ε²` for all `k`, `y`;
3. the deterministic output `q_1 = algLaw 0 (detMean A b s) N 1` has `TV(p_1, q_1) ≥ 1 - η`;
4. `q_1` and the exact-score deterministic output `q*_1 = algLaw 0 (detMean A b ∇ log p) N 1`
   admit a coupling `Γ` with `|x - x*| ≤ |b_2| ε` `Γ`-a.s. and `∫⁻ |x - x*|² dΓ ≤ (|b_2| ε)²`.
Note: `TV` is measured against the data marginal `p_1`, `W_2` against `q*_1`. -/
theorem smooth_separation_tv_far_w2_close (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hd : 0 < d) {t : ℕ → ℝ} (ht : t 0 < t 1) {A : ℕ → (Fin d → ℝ) → Fin d → ℝ}
    (hA : ∀ k, Measurable (A k)) {b : ℕ → ℝ} (hb : b 2 ≠ 0) {N : ℕ} (hN : 2 ≤ N) {ε : ℝ}
    (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ (s : ℕ → (Fin d → ℝ) → Fin d → ℝ) (hs : ∀ k, Measurable (s k))
      (E : (Fin d → ℝ) → Fin d → ℝ),
      ContDiff ℝ ⊤ E ∧ (∀ z, ∑ i, E z i ^ 2 ≤ ε ^ 2) ∧
      (∀ k, k ≠ 2 → ∀ y, s k y = score (fwdDensity μ t k) y) ∧
      (∀ y, s 2 y = score (fwdDensity μ t 2) y + E (detMean A b (exactScore μ t) 2 y)) ∧
      (∀ k y, ∑ i, (s k y i - score (fwdDensity μ t k) y i) ^ 2 ≤ ε ^ 2) ∧
      1 - η ≤ TotalVariation.tvSup (fwdLaw μ t 1)
        (algLaw zeroVar (detMean A b s) (measurable_detMean hA b hs) N 1) ∧
      ∃ Γ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure Γ ∧
        Γ.map Prod.fst = algLaw zeroVar (detMean A b s) (measurable_detMean hA b hs) N 1 ∧
        Γ.map Prod.snd = algLaw zeroVar (detMean A b (exactScore μ t))
          (measurable_detMean hA b (measurable_exactScore μ t)) N 1 ∧
        (∀ᵐ p ∂Γ, eDist p.1 p.2 ≤ |b 2| * ε) ∧
        sqCostPi Γ ≤ ENNReal.ofReal ((|b 2| * ε) ^ 2) := by
  set i₀ : Fin d := ⟨0, hd⟩
  set h := 2 * |b 2| * ε
  have hh : 0 < h := by have := abs_pos.2 hb; positivity
  have hεh : |(b 2)⁻¹| * h / 2 ≤ ε := (abs_inv_mul_step (b 2) hb hε).le
  obtain ⟨θ, m, hTV⟩ := exists_tvSup_detOutput_smoothScore_ge μ ht hA hb i₀ hh.ne' hN hη
  have hs := measurable_smoothScore μ t hA b i₀ h θ m
  have hacc := sum_sq_smoothScore_sub_le μ t A b i₀ hh θ m hεh
  refine ⟨smoothScore μ t A b i₀ h θ m, hs, smoothErr i₀ (b 2)⁻¹ h θ m,
    contDiff_smoothErr i₀ _ h θ m, sum_sq_smoothErr_le i₀ hh θ m hεh, fun k hk y => ?_,
    fun y => ?_, hacc, hTV, ?_⟩
  · funext i; simp [smoothScore, exactScore, hk]
  · funext i; simp [smoothScore, exactScore]
  rw [algLaw_zeroVar_eq_map, algLaw_zeroVar_eq_map]
  refine exists_coupling_of_eDist_le _ (measurable_detFlow (measurable_detMean hA b hs) N 1)
    (measurable_detFlow (measurable_detMean hA b (measurable_exactScore μ t)) N 1)
    (eDist_detFlow_le_of_last (by omega) (fun i hi _ => ?_)
      (fun y => eDist_detMean_le A b _ (exactScore μ t) 2 y hε.le (hacc 2 y)))
  funext y j
  simp [detMean, smoothScore, exactScore, show i ≠ 2 by omega]

end FormalizeSampling.DiffusionODELipschitz
