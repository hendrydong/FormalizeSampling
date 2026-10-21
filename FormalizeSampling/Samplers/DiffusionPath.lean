module

public import FormalizeSampling.Samplers.DiffusionSetup

/-!
# Path-space KL for DDPM-type samplers: the chain-rule equality and the time reversal

Status: **Verified**.

Setting of `Samplers/DiffusionSetup.lean`: data law `μ` on `Fin d → ℝ` (a probability measure;
no moment, density or grid assumption is needed in this file), time grid `t`, forward OU steps
`F_k`, forward marginals `p_k = fwdLaw μ t k`, exact reverse kernels `R_k = F_k†p_{k-1}`
(`revKernel`, Bayes posterior), and the algorithm `q_N = N(0, I)`, `q_{k-1} = Q_k ∘ q_k` with
`Q_k = algKernel σ2 m hm k` (arbitrary variances and measurable mean maps).

## Path spaces

`PathSp E j` is the space of paths with `j + 1` coordinates, as nested pairs
`PathSp E 0 = E`, `PathSp E (j+1) = PathSp E j × E`; the coordinate added last is `last j`, the
oldest one is `first j`. For an initial law `μ₀` and Markov kernels `κ i : Kernel E E`,
`pathLaw μ₀ κ j` is the law of a Markov chain `(X₀, X₁, …, X_j)` with `X₀ ∼ μ₀` and
`X_{i+1} ∼ κ i (X_i)`, built as the iterated `compProd`
`pathLaw μ₀ κ (j+1) = pathLaw μ₀ κ j ⊗ₘ (κ j ∘ last j)`; `chainLaw μ₀ κ j` is the law of `X_j`.

For the sampler (reverse time, `N` steps from index `N` down to `1`):

* `truePath μ t N j`: `x_N ∼ p_N`, then `x_{N-1} ∼ R_N(x_N)`, …, `x_{N-j} ∼ R_{N-j+1}(x_{N-j+1})`.
  The full reverse path is `truePath μ t N (N - 1)` (coordinates `x_N, …, x_1`).
* `algPath σ2 m hm N j`: `y_N ∼ N(0, I)`, then `y_{k-1} ∼ Q_k(y_k)`; full path at `j = N - 1`.
* `fwdPath μ t n`: the law of the **forward** chain `(x_1, …, x_{n+1})` (`x_1 ∼ p_1`,
  `x_{k+1} ∼ F_{k+1}(x_k)`), stored in the same coordinate order as `truePath`
  (`x_{n+1}` first, `x_1` last).

## Main results

* `klDiv_pathLaw` (general chain rule, equality in `ℝ≥0∞`): for probability measures `μ₀ ν₀` and
  Markov kernels on a countably generated space,
  `KL(pathLaw μ₀ κ j ‖ pathLaw ν₀ η j)
    = KL(μ₀ ‖ ν₀) + ∑_{i<j} ∫ KL(κ i y ‖ η i y) d(chainLaw μ₀ κ i)`.
* `map_last_pathLaw`: the last-coordinate marginal of `pathLaw μ₀ κ j` is `chainLaw μ₀ κ j`.
* `klDiv_truePath_algPath` (**path-space chain rule for the sampler**, equality):
  `KL(truePath ‖ algPath) = KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ Q_k y) dp_k(y)`.
* `map_last_truePath`, `map_last_algPath`: the last coordinates have laws `p_{N-j}` and
  `q_{N-j}`; hence `klDiv_output_le_path`: `KL(p_1 ‖ q_1) ≤ KL(truePath ‖ algPath)`.
* **Time reversal** (reverse Markov property of the forward chain):
  `compProd_revKernel_eq_map_swap` (`p_{k+1} ⊗ R_{k+1}` is the law of `(x_{k+1}, x_k)`),
  `truePath_succ_succ`, and `fwdPath_eq_truePath`: the law of the forward path
  `(x_{n+1}, …, x_1)` **equals** the iterated posterior construction `truePath μ t (n+1) n`.
  Consequently `klDiv_fwdPath_algPath`: the KL between the law of the forward path (reversed)
  and the sampler's path law is `KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ Q_k y) dp_k(y)`.

The output bounds of `Samplers/Diffusion.lean` (`Diffusion.klDiv_output_le_chain`,
`Diffusion.klDiv_output_le`, …) are derived from these identities and `klDiv_output_le_path`.
The path forms of `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le` and
`DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_ge` are in
`Samplers/DiffusionMain.lean` and `Samplers/DiffusionVarianceMain.lean`.

## Not proved here

* Path laws are finite-dimensional (`N` coordinates `x_N, …, x_1`); the data coordinate `x_0`
  and the continuous-time path measure of the OU SDE are not treated.
* The forward path is started at `x_1 ∼ p_1`; that it is the `(x_1, …, x_N)`-marginal of the
  chain started at `x_0 ∼ μ` is immediate from the Markov property but not stated.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

namespace FormalizeSampling.DiffusionPath

universe u

/-- The path space with `j + 1` coordinates in `E`, as nested pairs:
`PathSp E 0 = E` and `PathSp E (j + 1) = PathSp E j × E`. -/
@[reducible] def PathSp (E : Type u) : ℕ → Type u
  | 0 => E
  | j + 1 => PathSp E j × E

/-- The product σ-algebra on `PathSp E j`. -/
instance PathSp.instMeasurableSpace (E : Type u) [MeasurableSpace E] :
    (j : ℕ) → MeasurableSpace (PathSp E j)
  | 0 => inferInstanceAs (MeasurableSpace E)
  | j + 1 => @Prod.instMeasurableSpace (PathSp E j) E (PathSp.instMeasurableSpace E j) _

variable {E : Type u} [MeasurableSpace E]

namespace PathSp

/-- The most recently appended coordinate of a path (`x_j` for a path `(x_0, …, x_j)`). -/
def last : (j : ℕ) → PathSp E j → E
  | 0 => fun x => (x : E)
  | j + 1 => fun x : PathSp E j × E => x.2

/-- The last coordinate is measurable. -/
theorem measurable_last : (j : ℕ) → Measurable (last (E := E) j)
  | 0 => measurable_id
  | j + 1 => measurable_snd (α := PathSp E j) (β := E)

/-- The oldest coordinate of a path (`x_0` for a path `(x_0, …, x_j)`). -/
def first : (j : ℕ) → PathSp E j → E
  | 0 => fun x => (x : E)
  | j + 1 => fun x : PathSp E j × E => first j x.1

/-- The first coordinate is measurable. -/
theorem measurable_first : (j : ℕ) → Measurable (first (E := E) j)
  | 0 => measurable_id
  | j + 1 => (measurable_first j).comp (measurable_fst (α := PathSp E j) (β := E))

/-- Prepend a coordinate: `consFront j ((x_0, …, x_j), a) = (a, x_0, …, x_j)`. -/
def consFront : (j : ℕ) → PathSp E j × E → PathSp E (j + 1)
  | 0 => fun z => ((z.2 : E), (z.1 : E))
  | j + 1 => fun z : (PathSp E j × E) × E =>
      ((consFront j (z.1.1, z.2), z.1.2) : PathSp E (j + 1) × E)

/-- Prepending is measurable. -/
theorem measurable_consFront : (j : ℕ) → Measurable (consFront (E := E) j)
  | 0 => measurable_snd.prodMk measurable_fst
  | j + 1 => by
    change Measurable fun z : (PathSp E j × E) × E =>
      ((consFront j (z.1.1, z.2), z.1.2) : PathSp E (j + 1) × E)
    exact ((measurable_consFront j).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)

omit [MeasurableSpace E] in
/-- Prepending does not change the last coordinate. -/
theorem last_consFront :
    (j : ℕ) → ∀ z : PathSp E j × E, last (j + 1) (consFront j z) = last j z.1
  | 0, _ => rfl
  | _ + 1, _ => rfl

end PathSp

open PathSp

/-! ### Path laws of Markov chains and the general chain rule -/

/-- The path law of a Markov chain: `X₀ ∼ μ₀`, `X_{i+1} ∼ κ i (X_i)`; `pathLaw μ₀ κ j` is the
law of `(X₀, …, X_j)` on `PathSp E j`, defined by
`pathLaw μ₀ κ (j + 1) = pathLaw μ₀ κ j ⊗ₘ (κ j ∘ last j)`. -/
noncomputable def pathLaw (μ0 : Measure E) (κ : ℕ → Kernel E E) :
    (j : ℕ) → Measure (PathSp E j)
  | 0 => μ0
  | j + 1 => (pathLaw μ0 κ j ⊗ₘ (κ j).comap (last j) (measurable_last j) :
      Measure (PathSp E j × E))

/-- Unfolding the path law: `pathLaw μ₀ κ (j + 1) = pathLaw μ₀ κ j ⊗ₘ (κ j ∘ last j)`. -/
theorem pathLaw_succ (μ0 : Measure E) (κ : ℕ → Kernel E E) (j : ℕ) :
    pathLaw μ0 κ (j + 1) =
      (pathLaw μ0 κ j ⊗ₘ (κ j).comap (last j) (measurable_last j) :
        Measure (PathSp E j × E)) := rfl

/-- The path law of a Markov chain with probability initial law and Markov kernels is a
probability measure. -/
instance isProbabilityMeasure_pathLaw (μ0 : Measure E) [IsProbabilityMeasure μ0]
    (κ : ℕ → Kernel E E) [∀ j, IsMarkovKernel (κ j)] (j : ℕ) :
    IsProbabilityMeasure (pathLaw μ0 κ j) := by
  induction j with
  | zero => exact (inferInstance : IsProbabilityMeasure μ0)
  | succ j ih => rw [pathLaw_succ]; infer_instance

/-- The one-time marginals of the chain: `chainLaw μ₀ κ 0 = μ₀`,
`chainLaw μ₀ κ (j + 1) = κ j ∘ₘ chainLaw μ₀ κ j`. -/
noncomputable def chainLaw (μ0 : Measure E) (κ : ℕ → Kernel E E) : ℕ → Measure E
  | 0 => μ0
  | j + 1 => κ j ∘ₘ chainLaw μ0 κ j

/-- Composition with a pulled-back kernel: `(κ ∘ f) ∘ₘ P = κ ∘ₘ f_* P` for measurable `f`. -/
theorem comp_comap_eq_comp_map {X : Type*} [MeasurableSpace X] (P : Measure X)
    (κ : Kernel E E) {f : X → E} (hf : Measurable f) :
    κ.comap f hf ∘ₘ P = κ ∘ₘ P.map f := by
  rw [Measure.bind_map hf.aemeasurable κ.aemeasurable]
  rfl

/-- **Last-coordinate marginal.** The law of the last coordinate `X_j` under
`pathLaw μ₀ κ j` is `chainLaw μ₀ κ j`. -/
theorem map_last_pathLaw (μ0 : Measure E) [IsProbabilityMeasure μ0] (κ : ℕ → Kernel E E)
    [∀ j, IsMarkovKernel (κ j)] (j : ℕ) :
    (pathLaw μ0 κ j).map (last j) = chainLaw μ0 κ j := by
  induction j with
  | zero => exact Measure.map_id
  | succ j ih =>
    rw [chainLaw, ← ih, ← comp_comap_eq_comp_map _ _ (measurable_last j),
      ← Measure.snd_compProd]
    rfl

/-- **Appending and prepending commute** (conditional independence of the two new coordinates
given the path). For a probability law `P` on `PathSp E j` and Markov kernels `κ η`, attaching
`b ∼ κ(last x)` at the end of `(a ∼ η(first x)) :: x` gives the same law as attaching
`a ∼ η(first x)` at the front of `x ++ [b ∼ κ(last x)]`. -/
theorem compProd_consFront_comm (j : ℕ) (P : Measure (PathSp E j)) [IsProbabilityMeasure P]
    (κ η : Kernel E E) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (P ⊗ₘ η.comap (first j) (measurable_first j)).map (consFront j) ⊗ₘ
        κ.comap (last (j + 1)) (measurable_last (j + 1)) =
      ((P ⊗ₘ κ.comap (last j) (measurable_last j) : Measure (PathSp E (j + 1))) ⊗ₘ
        η.comap (first (j + 1)) (measurable_first (j + 1))).map (consFront (j + 1)) := by
  ext s hs
  have hf : Measurable (s.indicator (1 : PathSp E (j + 1 + 1) → ℝ≥0∞)) :=
    measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs,
    Measure.lintegral_compProd hf,
    lintegral_map (Measurable.lintegral_kernel_prod_right' (κ := κ.comap (last (j + 1))
      (measurable_last (j + 1))) hf) (measurable_consFront j),
    Measure.lintegral_compProd (f := fun a => ∫⁻ b, s.indicator 1 (consFront j a, b)
      ∂(κ.comap (last (j + 1)) (measurable_last (j + 1)) (consFront j a)))
      ((Measurable.lintegral_kernel_prod_right' (κ := κ.comap (last (j + 1))
      (measurable_last (j + 1))) hf).comp (measurable_consFront j)),
    lintegral_map hf (measurable_consFront (j + 1)),
    Measure.lintegral_compProd (f := fun w => s.indicator 1 (consFront (j + 1) w))
      (hf.comp (measurable_consFront (j + 1))),
    Measure.lintegral_compProd (f := fun y => ∫⁻ a, s.indicator 1 (consFront (j + 1) (y, a))
      ∂(η.comap (first (j + 1)) (measurable_first (j + 1)) y))
      (Measurable.lintegral_kernel_prod_right' (κ := η.comap (first (j + 1))
      (measurable_first (j + 1))) (hf.comp (measurable_consFront (j + 1))))]
  refine lintegral_congr fun x => ?_
  simp only [Kernel.comap_apply, last_consFront]
  rw [lintegral_lintegral_swap]
  · rfl
  · exact (hf.comp (((measurable_consFront j).comp
      (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)).aemeasurable

variable [MeasurableSpace.CountablyGenerated E]

/-- **KL chain rule on path space (equality).** For probability measures `μ₀ ν₀` and Markov
kernels `κ i, η i` on a countably generated measurable space `E` (e.g. `Fin d → ℝ`),
`KL(pathLaw μ₀ κ j ‖ pathLaw ν₀ η j) = KL(μ₀ ‖ ν₀) + ∑_{i<j} ∫ KL(κ i y ‖ η i y) dρ_i(y)`,
an identity in `ℝ≥0∞`, where `ρ_i = chainLaw μ₀ κ i` is the law of `X_i` under the **first**
chain. -/
theorem klDiv_pathLaw (μ0 ν0 : Measure E) [IsProbabilityMeasure μ0] [IsProbabilityMeasure ν0]
    (κ η : ℕ → Kernel E E) [∀ j, IsMarkovKernel (κ j)] [∀ j, IsMarkovKernel (η j)] (j : ℕ) :
    klDiv (pathLaw μ0 κ j) (pathLaw ν0 η j) =
      klDiv μ0 ν0 + ∑ i ∈ range j, ∫⁻ y, klDiv (κ i y) (η i y) ∂(chainLaw μ0 κ i) := by
  induction j with
  | zero => simp [pathLaw]
  | succ j ih =>
    rw [pathLaw_succ, pathLaw_succ, KL.klDiv_compProd_eq_add_lintegral, ih, sum_range_succ,
      add_assoc, ← map_last_pathLaw,
      lintegral_map (KL.measurable_klDiv_kernel (κ j) (η j)) (measurable_last j)]
    rfl

/-! ### The DDPM sampler on path space -/

section DDPM

open FormalizeSampling.Diffusion

variable {d : ℕ}

/-- **One-step time reversal.** `p_{k+1} ⊗ R_{k+1}` is the law of `(x_{k+1}, x_k)` under the
forward chain: `p_{k+1} ⊗ₘ R_{k+1} = (p_k ⊗ₘ F_{k+1}).map swap` (Mathlib's
`compProd_posterior_eq_map_swap`). No assumption on `μ` or `t`. -/
theorem compProd_revKernel_eq_map_swap (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ → ℝ) (k : ℕ) :
    fwdLaw μ t (k + 1) ⊗ₘ revKernel μ t (k + 1) =
      (fwdLaw μ t k ⊗ₘ fwdKernel t (k + 1)).map Prod.swap :=
  compProd_posterior_eq_map_swap

/-- The reverse path law of the true process after `j` reverse steps from index `N`:
`x_N ∼ p_N`, then `x_{N-i-1} ∼ R_{N-i}(x_{N-i})` for `i < j`. The full reverse path
`(x_N, …, x_1)` is `truePath μ t N (N - 1)`. -/
noncomputable def truePath (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)
    (N : ℕ) : (j : ℕ) → Measure (PathSp (Fin d → ℝ) j) :=
  pathLaw (fwdLaw μ t N) fun i => revKernel μ t (N - i)

/-- The path law of the algorithm after `j` steps: `y_N ∼ N(0, I)`, then
`y_{N-i-1} ∼ Q_{N-i}(y_{N-i})`. The full sampler path `(y_N, …, y_1)` is
`algPath σ2 m hm N (N - 1)`. -/
noncomputable def algPath (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N : ℕ) : (j : ℕ) → Measure (PathSp (Fin d → ℝ) j) :=
  pathLaw (stdGaussianPi d) fun i => algKernel σ2 m hm (N - i)

/-- The law of the forward chain path `(x_1, …, x_{n+1})` (`x_1 ∼ p_1`,
`x_{k+1} ∼ F_{k+1}(x_k)`), stored in reverse-time order `(x_{n+1}, …, x_1)`: each new forward
coordinate is prepended with `consFront`. -/
noncomputable def fwdPath (μ : Measure (Fin d → ℝ)) (t : ℕ → ℝ) :
    (n : ℕ) → Measure (PathSp (Fin d → ℝ) n)
  | 0 => fwdLaw μ t 1
  | n + 1 => (fwdPath μ t n ⊗ₘ (fwdKernel t (n + 2)).comap (first n) (measurable_first n)).map
      (consFront n)

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (t : ℕ → ℝ)

/-- The true reverse path law is a probability measure. -/
instance isProbabilityMeasure_truePath (N j : ℕ) : IsProbabilityMeasure (truePath μ t N j) := by
  unfold truePath; infer_instance

omit [IsProbabilityMeasure μ] in
/-- The algorithm's path law is a probability measure. -/
instance isProbabilityMeasure_algPath (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N j : ℕ) : IsProbabilityMeasure (algPath σ2 m hm N j) := by
  unfold algPath; infer_instance

/-- **Reverse Markov property, inductive step.** Extending the horizon from `N` to `N + 1`
prepends `x_{N+1} ∼ F_{N+1}(x_N)` to the reverse path:
`truePath μ t (N+1) (j+1) = consFront_*(truePath μ t N j ⊗ₘ (F_{N+1} ∘ first))`. No assumption
on `μ` or `t`. -/
theorem truePath_succ_succ (N j : ℕ) :
    truePath μ t (N + 1) (j + 1) =
      (truePath μ t N j ⊗ₘ (fwdKernel t (N + 1)).comap (first j) (measurable_first j)).map
        (consFront j) := by
  induction j with
  | zero => exact compProd_revKernel_eq_map_swap μ t N
  | succ j ih =>
    rw [truePath, pathLaw_succ, ← truePath, ih, show N + 1 - (j + 1) = N - j by omega,
      compProd_consFront_comm]
    rfl

/-- **Time reversal of the forward chain (path-law equality).** The law of the forward path
`(x_{n+1}, …, x_1)` equals the reverse path law built from `p_{n+1}` and the Bayes posteriors
`R_{n+1}, …, R_2`: `fwdPath μ t n = truePath μ t (n + 1) n`. No assumption on `μ` or `t`. -/
theorem fwdPath_eq_truePath (n : ℕ) : fwdPath μ t n = truePath μ t (n + 1) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fwdPath, ih, truePath_succ_succ]

/-- The one-time marginals of the reverse chain: for `j ≤ N`, `x_{N-j} ∼ p_{N-j}`. -/
theorem chainLaw_revKernel {N j : ℕ} (hj : j ≤ N) :
    chainLaw (fwdLaw μ t N) (fun i => revKernel μ t (N - i)) j = fwdLaw μ t (N - j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [chainLaw, ih (by omega)]
    have h := revKernel_comp_fwdLaw μ t (N - (j + 1))
    rwa [show N - (j + 1) + 1 = N - j by omega] at h

omit [IsProbabilityMeasure μ] in
/-- The one-time marginals of the algorithm's chain: for `j ≤ N`, `y_{N-j} ∼ q_{N-j}`. -/
theorem chainLaw_algKernel (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N j : ℕ} (hj : j ≤ N) :
    chainLaw (stdGaussianPi d) (fun i => algKernel σ2 m hm (N - i)) j =
      algLaw σ2 m hm N (N - j) := by
  induction j with
  | zero => rw [Nat.sub_zero, algLaw_self]; rfl
  | succ j ih =>
    rw [chainLaw, ih (by omega), algLaw_of_lt σ2 m hm (show N - (j + 1) < N by omega),
      show N - (j + 1) + 1 = N - j by omega]

/-- **Last marginal of the true path.** For `j ≤ N`, the last coordinate of
`truePath μ t N j` has law `p_{N-j}`; in particular the full path ends at `p_1`. -/
theorem map_last_truePath {N j : ℕ} (hj : j ≤ N) :
    (truePath μ t N j).map (last j) = fwdLaw μ t (N - j) := by
  rw [truePath, map_last_pathLaw, chainLaw_revKernel μ t hj]

omit [IsProbabilityMeasure μ] in
/-- **Last marginal of the algorithm's path.** For `j ≤ N`, the last coordinate of
`algPath σ2 m hm N j` has law `q_{N-j}`; in particular the full path ends at the output `q_1`. -/
theorem map_last_algPath (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N j : ℕ} (hj : j ≤ N) :
    (algPath σ2 m hm N j).map (last j) = algLaw σ2 m hm N (N - j) := by
  rw [algPath, map_last_pathLaw, chainLaw_algKernel σ2 m hm hj]

/-- **Path-space chain rule for DDPM-type samplers (equality).** For every probability data
law `μ`, time grid `t`, variances `σ2`, measurable mean maps `m` and `N`:
`KL(truePath μ t N (N-1) ‖ algPath σ2 m hm N (N-1))
  = KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ Q_k y) dp_k(y)`,
an identity in `ℝ≥0∞` (both sides may be `∞`). The per-step errors are averaged under the true
marginals `p_k`. -/
theorem klDiv_truePath_algPath (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) (N : ℕ) :
    klDiv (truePath μ t N (N - 1)) (algPath σ2 m hm N (N - 1)) =
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y) (algKernel σ2 m hm k y)
          ∂(fwdLaw μ t k) := by
  rw [truePath, algPath, klDiv_pathLaw]
  congr 1
  refine Finset.sum_nbij' (fun i => N - i) (fun k => N - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range, mem_Ioc] at hi ⊢; omega
  · intro k hk; simp only [mem_range, mem_Ioc] at hk ⊢; omega
  · intro i hi; simp only [mem_range] at hi; omega
  · intro k hk; simp only [mem_Ioc] at hk; omega
  · intro i hi
    simp only [mem_range] at hi
    rw [chainLaw_revKernel μ t (by omega)]

/-- **Path-space chain rule for the forward path (equality).** For `N ≥ 1`, the KL between the
law of the forward chain path `(x_N, …, x_1)` and the sampler's path law is
`KL(fwdPath μ t (N-1) ‖ algPath σ2 m hm N (N-1))
  = KL(p_N ‖ N(0,I)) + ∑_{k=2}^N ∫ KL(R_k y ‖ Q_k y) dp_k(y)`. -/
theorem klDiv_fwdPath_algPath (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N : ℕ} (hN : 1 ≤ N) :
    klDiv (fwdPath μ t (N - 1)) (algPath σ2 m hm N (N - 1)) =
      klDiv (fwdLaw μ t N) (stdGaussianPi d) +
        ∑ k ∈ Ioc 1 N, ∫⁻ y, klDiv (revKernel μ t k y) (algKernel σ2 m hm k y)
          ∂(fwdLaw μ t k) := by
  rw [fwdPath_eq_truePath, show N - 1 + 1 = N by omega, klDiv_truePath_algPath]

/-- **Output KL ≤ path KL.** For `N ≥ 1`, `KL(p_1 ‖ q_1) ≤ KL(truePath ‖ algPath)` (data
processing for the last-coordinate projection). -/
theorem klDiv_output_le_path (σ2 : ℕ → ℝ≥0) (m : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hm : ∀ k, Measurable (m k)) {N : ℕ} (hN : 1 ≤ N) :
    klDiv (fwdLaw μ t 1) (algLaw σ2 m hm N 1) ≤
      klDiv (truePath μ t N (N - 1)) (algPath σ2 m hm N (N - 1)) := by
  have h1 := map_last_truePath μ t (N := N) (j := N - 1) (by omega)
  have h2 := map_last_algPath σ2 m hm (N := N) (j := N - 1) (by omega)
  rw [show N - (N - 1) = 1 by omega] at h1 h2
  rw [← h1, ← h2]
  exact klDiv_map_le _ _ (measurable_last _)

end DDPM

end FormalizeSampling.DiffusionPath
