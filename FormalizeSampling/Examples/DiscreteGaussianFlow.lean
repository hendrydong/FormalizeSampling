module

public import FormalizeSampling.Examples.GaussianFlowVsOU
public import FormalizeSampling.Counterexamples.ULADiscretization
public import FormalizeSampling.Foundations.GaussianKL

/-!
# Discrete-time population PFG on Gaussians (PFG App. A.6, Eqs. (33)-(35))

Registry ID: **EX-2** (discrete population Gaussian flow, PFG App. A.6: discrete Gaussian
contraction); discretisation
layer, population case only.

## Setting (one dimension; the diagonal case is a product of such problems)

Target `p⋆ = N(μ⋆, σ⋆²)`, scalar preconditioner `h > 0`, step size `η > 0`, current population
law `p_k = N(μ_k, s_k²)` with `s_k > 0`. In App. A.6 the velocity class is the exact linear
class: it contains the ideal PFG velocity `v⋆ = h⁻¹ (∂ log p⋆ - ∂ log p_k)`, which is affine for
a Gaussian `p_k`. The population Euler step is the map (`eulerMap`)

`T_k x = x + (η / h) ((μ⋆ - x) / σ⋆² + (x - μ_k) / s_k²)`.

`eulerMap_eq_add_score` checks `T_k x = x + η h⁻¹ (∂ log p⋆ - ∂ log p_k)(x)` with the state
scores `score1` of the actual Gaussian densities (reusing
`FormalizeSampling.score1_gaussianPDFReal`).

The paper's diagonal case `Σ⋆ = diag(σᵢ²)`, `H = diag(hᵢ)`, `Σ_k = diag(sᵢ²(k))` is a product
of independent one-dimensional problems: `map_flowEulerStep_diagonal` proves that the matrix update
`x ↦ x + η H⁻¹ (Σ⋆⁻¹ (μ⋆ - x) + Σ_k⁻¹ (x - μ_k))` pushes `⊗ᵢ N(μ_{k,i}, sᵢ²(k))` forward to
`⊗ᵢ N(μ_{k+1,i}, sᵢ²(k+1))`, coordinatewise by the one-dimensional recursions. Only the
diagonal case is formalised (when `H Σ⋆ = Σ⋆ H`, an orthogonal change of coordinates reduces
the general case to it; this reduction is not formalised).

## Conventions

* Variances are passed as variances: `σ2 = σ⋆²` (target) and `s2 = s_k²` (current law). The
  specification's map written with standard deviations is
  `eulerMap η h μ⋆ (σ⋆ ^ 2) μ_k (s_k ^ 2)` (`map_eulerMap_gaussianReal_sq`).
* Mathlib's `gaussianReal m v` takes the **variance** `v : ℝ≥0`. The recursions `nextMean`
  (Eq. (34)) and `nextVar` (Eq. (35), factored form) are real-valued (no truncated `ℝ≥0`
  subtraction); `nextVarNN` packages the nonnegative variance for `gaussianReal`.
* The contraction factor `α = η / (h σ⋆²)` is written out in every statement.
* The paper's iteration index is `t`; here it is `k`.
* Population iteration (`popLaw`): each step pushes the current law `ρ` forward by the Euler map
  whose velocity is built from the current law's own mean `∫ x dρ` and variance `Var[id; ρ]`
  (`popMap`). For a Gaussian law these are its parameters (`popMap_gaussianReal`), so the closed
  form `popLaw_gaussianReal` (law at step `k` is `N(μ_k, s_k²)` with the recursions (34)-(35))
  is a theorem, not a definition. (For non-Gaussian `ρ` the map `popMap` is only a definition;
  nothing is claimed about it.)
* Junk values: the identities of part (a) hold for all real parameters (they are affine
  pushforward identities); their PFG meaning needs `η, h, σ⋆², s_k² > 0`. All inequalities
  assume the positivity they need explicitly.
* Degenerate parameters are junk-value artefacts of Lean's `x / 0 = 0`, **not** PFG steps.
  For `h = 0` the map `eulerMap η 0 …` is the identity (`η / 0 = 0`; then `nextMean = μ_k` and
  `nextVar = s_k²`). For `s_k² = 0` the current law `N(μ_k, 0)` is a point mass with no score,
  the term `(x - μ_k) / s_k²` is `0`, the map is `x ↦ x + (η/h) (μ⋆ - x)/σ⋆²` and
  `nextVar … 0 = 0`. (Likewise `σ⋆² = 0` drops the target term and makes `α = 0`.) The
  statements that hold for all real parameters remain true in these cases but say nothing
  about PFG.

## Paper statements and their Lean counterparts

* **(a) Eqs. (34)-(35).** `map_eulerMap_gaussianReal`, `map_eulerMap_gaussianReal_sq`:
  `T_k # N(μ_k, s_k²) = N(μ_{k+1}, s_{k+1}²)` with
  `μ_{k+1} = (1 - η/(h σ⋆²)) μ_k + (η/(h σ⋆²)) μ⋆` (34) and
  `s_{k+1}² = s_k² (1 + (η/h)(1/s_k² - 1/σ⋆²))²`; `nextVar_eq_expanded` is the paper's
  expanded form (35). `popLaw_gaussianReal` iterates it; `map_flowEulerStep_diagonal` is the
  diagonal `d`-dimensional version.
* **(b)(i)** "`η ≤ h σ⋆²/2` and `s_0² ≥ σ⋆²` imply `s_k² ≥ σ⋆²` for all `k`"
  (`le_nextVar`, `le_varSeq`, `le_variance_popLaw`). The step-size threshold is sharp:
  for every `η > h σ⋆²/2` some `s² > σ⋆²` has `s'² < σ⋆²` (`exists_nextVar_lt_of_lt`).
* **(b)(ii)** mean gap: `|μ_{k+1} - μ⋆| = |1 - η/(h σ⋆²)| |μ_k - μ⋆|`, an exact
  identity for all parameters (`nextMean_sub`, `abs_nextMean_sub`, `meanSeq_sub`,
  `abs_meanSeq_sub`).
* **(b)(iii)** relative variance gap `(s_{k+1}² - σ⋆²)/σ⋆² ≤ (1 - α) (s_k² - σ⋆²)/σ⋆²`
  under the paper's conditions (`relGap_nextVar_le`, whose step-size hypothesis is
  `0 ≤ η ≤ h σ⋆²`, and the absolute-value form `abs_relGap_nextVar_le`). The bound is also
  proved with the factor `(1 - α)²` (`relGap_nextVar_le_sq`), from the exact identity
  `s'² - σ⋆² = (1 - α)² (s² - σ⋆²) - α² σ⋆² (s² - σ⋆²) / s²` (`nextVar_sub_eq_upper`).
  With `g = (s² - σ⋆²)/σ⋆²` and `g' = (s'² - σ⋆²)/σ⋆²`, for `0 < σ⋆² ≤ s²` and any real `η`, `h`
  there are two-sided bounds `(1 - 2α) g ≤ g' ≤ (1 - α)² g`: the lower one is
  `relGap_nextVar_ge` (which only needs `σ⋆² > 0`, `s² > 0`), the upper one
  `relGap_nextVar_le_sq` (which needs `0 < σ⋆² ≤ s²`). The two factors are different,
  `(1 - α)² = (1 - 2α) + α²`, and their ratio `(1 - α)²/(1 - 2α) = 1 + α²/(1 - 2α)` (for
  `α < 1/2`) equals `1` only to first order in `α`; the bounds do not pin down the one-step
  rate. (By the exact identity `nextVar_sub_eq_lower`, `g'` exceeds the lower bound by
  `α² (s² - σ⋆²)² / (s² σ⋆²) ≥ 0`, quadratic in the gap; no statement about the limit
  `s² → σ⋆²` is formalised.) The Lean upper bounds state the hypothesis `s_k² ≥ σ⋆²`
  explicitly, and it is necessary for them: for `η = 1/2`, `h = 1`, `σ⋆² = 1`, `s² = 1/4` both
  the one-sided and the absolute-value contraction fail (`nextVar_example_below`,
  `not_forall_relGap_contraction`, `not_forall_abs_relGap_contraction`). In the setting of
  App. A.6, `s_0² = 1 ≥ σᵢ²`, and (b)(i) gives `s_k² ≥ σ⋆²` for every `k`. Iterated:
  `relGap_varSeq_le`, `relGap_varSeq_le_sq`.
* **(c) Fixed point.** The target is preserved exactly: `eulerMap_target` (the Euler map at
  the target is the identity), `map_eulerMap_target`, `popLaw_target`. Unlike ULA
  (`Counterexamples/ULADiscretization.lean`), the population PFG Euler step has no
  discretisation bias at the target (`flow_exact_ula_biased`). For `0 < η ≤ 2 h σ⋆²` the target
  is the only Gaussian fixed point (`nextMean_eq_self_iff`, `nextVar_eq_self_iff`,
  `map_popMap_eq_self_iff`); for large steps spurious fixed points exist
  (`spurious_fixedPoint`: `η = 4`, `h = σ⋆² = 1`, `μ⋆ = 0` fixes `N(0, 2)`, the map being
  `x ↦ -x`).
* **Eq. (33), one dimension.** `klDiv_gaussianReal_gaussianReal` (closed-form Gaussian KL, in
  `Foundations/GaussianKL.lean`), `klDiv_gaussianReal_le` (`x - log(1 + x) ≤ x²/2`) and
  `klDiv_popLaw_le`:
  `KL(p_k ‖ p⋆) ≤ (1 - α)^{2k} C_0` with
  `C_0 = ½ ((μ_0 - μ⋆)²/σ⋆² + ½ ((s_0² - σ⋆²)/σ⋆²)²)`, under `0 ≤ η ≤ h σ⋆²/2`, `h > 0`,
  `s_0² ≥ σ⋆²` (the paper's `C_0` has `s_0² = 1`). `klDiv_popLaw_le_quarter` is the paper's
  special case `h = σ⋆⁻²`, `η = 1/2` (rate `4^{-k}`).

## Not proved here

* Only the **population** (infinitely many particles) dynamics with the exact linear velocity
  `v⋆` is treated. Finite particles, an estimated or time-varying preconditioner `H`, and the
  inner optimisation (finite `T'`, stochastic gradients, Hutchinson divergence) are not
  covered.
* That PFG's projection (Proposition 1) over the linear class returns `v⋆` is not re-proved
  here: the exact velocity is the model, justified because `v⋆` is affine (`eulerMap_eq_affine`)
  and hence lies in the class.
* The non-diagonal (non-commuting `H`, `Σ⋆`) case; non-Gaussian initial laws.
* The `d`-dimensional KL bound (33) (it needs additivity of `klDiv` over product measures and a
  maximum over coordinates); only the one-dimensional version and the diagonal pushforward are
  proved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal Matrix

namespace FormalizeSampling.DiscreteGaussianFlow

/-! ### The Euler map and the recursions (34)-(35) -/

/-- The population PFG Euler map (App. A.6, one coordinate): for target `N(μ⋆, σ⋆²)` with
`σ2 = σ⋆²`, current law `N(m, s2)` (`m = μ_k`, `s2 = s_k²`), preconditioner `h` and step `η`,
`T x = x + (η / h) ((μ⋆ - x) / σ⋆² + (x - μ_k) / s_k²)`. For `h = 0` or `s_k² = 0` (or
`σ⋆² = 0`) the divisions by `0` make this a junk-value map, not a PFG step. -/
noncomputable def eulerMap (η h μStar σ2 m s2 : ℝ) (x : ℝ) : ℝ :=
  x + η / h * ((μStar - x) / σ2 + (x - m) / s2)

/-- The mean recursion, Eq. (34):
`μ_{k+1} = (1 - η / (h σ⋆²)) μ_k + (η / (h σ⋆²)) μ⋆`. -/
noncomputable def nextMean (η h μStar σ2 m : ℝ) : ℝ :=
  (1 - η / (h * σ2)) * m + η / (h * σ2) * μStar

/-- The variance recursion, Eq. (35) in factored form:
`s_{k+1}² = s_k² (1 + (η / h) (1 / s_k² - 1 / σ⋆²))²` (computed in `ℝ`). -/
noncomputable def nextVar (η h σ2 s2 : ℝ) : ℝ :=
  s2 * (1 + η / h * (1 / s2 - 1 / σ2)) ^ 2

/-- The variance recursion preserves nonnegativity: `0 ≤ s2` implies `0 ≤ nextVar η h σ2 s2`
(no other assumption). -/
theorem nextVar_nonneg (η h σ2 : ℝ) {s2 : ℝ} (hs : 0 ≤ s2) : 0 ≤ nextVar η h σ2 s2 := by
  unfold nextVar; positivity

/-- The variance recursion (35) as a nonnegative real, for use as a `gaussianReal` variance. -/
noncomputable def nextVarNN (η h σ2 : ℝ) (s2 : ℝ≥0) : ℝ≥0 :=
  ⟨nextVar η h σ2 s2, nextVar_nonneg η h σ2 s2.coe_nonneg⟩

/-- **Eq. (35), expanded form.** For all real parameters,
`s_k² (1 + (η/h)(1/s_k² - 1/σ⋆²))² = s_k² + (2η s_k²/h)(1/s_k² - 1/σ⋆²)
+ (η² s_k²/h²)(1/s_k² - 1/σ⋆²)²`, i.e. the factored recursion `nextVar` is exactly the
paper's displayed formula. -/
theorem nextVar_eq_expanded (η h σ2 s2 : ℝ) :
    nextVar η h σ2 s2 = s2 + 2 * η * s2 / h * (1 / s2 - 1 / σ2)
      + η ^ 2 * s2 / h ^ 2 * (1 / s2 - 1 / σ2) ^ 2 := by
  unfold nextVar; ring

/-- The Euler map is affine: `T x = (1 + (η/h)(1/s_k² - 1/σ⋆²)) x + (η/h)(μ⋆/σ⋆² - μ_k/s_k²)`
(for all real parameters). In particular the exact velocity `v⋆` lies in the linear class. -/
theorem eulerMap_eq_affine (η h μStar σ2 m s2 : ℝ) :
    eulerMap η h μStar σ2 m s2 =
      (fun y => y + η / h * (μStar / σ2 - m / s2)) ∘
        (fun x => (1 + η / h * (1 / s2 - 1 / σ2)) * x) := by
  funext x; simp only [eulerMap, Function.comp_apply]; ring

/-- The Euler map is measurable (it is affine). -/
theorem measurable_eulerMap (η h μStar σ2 m s2 : ℝ) :
    Measurable (eulerMap η h μStar σ2 m s2) := by
  unfold eulerMap; fun_prop

/-- **The Euler map is the exact PFG velocity step.** For nonzero variances `σ⋆²`, `s_k²`,
`T x = x + η h⁻¹ (∂ log p⋆(x) - ∂ log p_k(x))` where `p⋆ = N(μ⋆, σ⋆²)`, `p_k = N(μ_k, s_k²)` and
`∂ log` is the state score `score1` of the Gaussian densities. -/
theorem eulerMap_eq_add_score (η h μStar m : ℝ) {σ2 s2 : ℝ≥0} (hσ : σ2 ≠ 0) (hs : s2 ≠ 0)
    (x : ℝ) :
    eulerMap η h μStar σ2 m s2 x =
      x + η * (h⁻¹ *
        (score1 (gaussianPDFReal μStar σ2) x - score1 (gaussianPDFReal m s2) x)) := by
  rw [score1_gaussianPDFReal _ hσ, score1_gaussianPDFReal _ hs,
    eulerMap]
  ring

/-- **(a) Pushforward, Eqs. (34)-(35).** One population PFG Euler step maps the Gaussian
`N(μ_k, s_k²)` to the Gaussian `N(μ_{k+1}, s_{k+1}²)`:
`T_k # N(μ_k, s_k²) = N(nextMean, nextVar)`. This is an exact one-time law identity and holds
for all real `η, h, μ⋆, σ⋆², μ_k` and every variance `s_k²` (affine pushforward); its PFG
meaning needs `η, h, σ⋆², s_k² > 0`. -/
theorem map_eulerMap_gaussianReal (η h μStar σ2 m : ℝ) (s2 : ℝ≥0) :
    (gaussianReal m s2).map (eulerMap η h μStar σ2 m s2) =
      gaussianReal (nextMean η h μStar σ2 m) (nextVarNN η h σ2 s2) := by
  rw [eulerMap_eq_affine, ← Measure.map_map (measurable_add_const _) (measurable_const_mul _),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  congr 1
  · unfold nextMean; ring
  · ext
    change _ = nextVar η h σ2 s2
    simp only [NNReal.coe_mul, NNReal.coe_mk, nextVar]
    ring

/-- **(a) Pushforward, standard-deviation form.** With target standard deviation `σ⋆` and
current standard deviation `s_k` (for every real `s_k`, in particular `s_k > 0`),
`T_k # N(μ_k, s_k²) = N((1 - η/(h σ⋆²)) μ_k + (η/(h σ⋆²)) μ⋆,
s_k² (1 + (η/h)(1/s_k² - 1/σ⋆²))²)`, with
`T_k x = x + (η / h) ((μ⋆ - x) / σ⋆² + (x - μ_k) / s_k²)`. -/
theorem map_eulerMap_gaussianReal_sq (η h μStar σStar m s : ℝ) :
    (gaussianReal m ⟨s ^ 2, sq_nonneg s⟩).map (eulerMap η h μStar (σStar ^ 2) m (s ^ 2)) =
      gaussianReal ((1 - η / (h * σStar ^ 2)) * m + η / (h * σStar ^ 2) * μStar)
        ⟨s ^ 2 * (1 + η / h * (1 / s ^ 2 - 1 / σStar ^ 2)) ^ 2, by positivity⟩ :=
  map_eulerMap_gaussianReal η h μStar (σStar ^ 2) m ⟨s ^ 2, sq_nonneg s⟩

/-! ### The population iteration -/

/-- The population Euler map determined by the current law `ρ`: the PFG Euler map whose
velocity uses `ρ`'s mean `∫ x dρ` and variance `Var[id; ρ]`. For Gaussian `ρ` this is the
exact PFG step (`popMap_gaussianReal`, `popMap_gaussianReal_eq_score`). -/
noncomputable def popMap (η h μStar σ2 : ℝ) (ρ : Measure ℝ) : ℝ → ℝ :=
  eulerMap η h μStar σ2 (∫ x, x ∂ρ) (variance id ρ)

/-- The population PFG iteration: `ρ_0 = ρ₀`, `ρ_{k+1} = (popMap ρ_k) # ρ_k` (infinitely many
particles, exact linear velocity class). -/
noncomputable def popLaw (η h μStar σ2 : ℝ) (ρ₀ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => ρ₀
  | k + 1 => (popLaw η h μStar σ2 ρ₀ k).map (popMap η h μStar σ2 (popLaw η h μStar σ2 ρ₀ k))

/-- The mean sequence `μ_k` of the recursion (34), started at `μ_0 = m₀`. -/
noncomputable def meanSeq (η h μStar σ2 m₀ : ℝ) (k : ℕ) : ℝ := (nextMean η h μStar σ2)^[k] m₀

/-- The variance sequence `s_k²` of the recursion (35), started at `s_0² = s2₀`. -/
noncomputable def varSeq (η h σ2 s2₀ : ℝ) (k : ℕ) : ℝ := (nextVar η h σ2)^[k] s2₀

/-- `s_0² = s2₀`. -/
theorem varSeq_zero (η h σ2 s2₀ : ℝ) : varSeq η h σ2 s2₀ 0 = s2₀ := rfl

/-- `s_{k+1}² = nextVar (s_k²)`. -/
theorem varSeq_succ (η h σ2 s2₀ : ℝ) (k : ℕ) :
    varSeq η h σ2 s2₀ (k + 1) = nextVar η h σ2 (varSeq η h σ2 s2₀ k) := by
  rw [varSeq, varSeq, Function.iterate_succ_apply']

/-- `μ_0 = m₀`. -/
theorem meanSeq_zero (η h μStar σ2 m₀ : ℝ) : meanSeq η h μStar σ2 m₀ 0 = m₀ := rfl

/-- `μ_{k+1} = nextMean (μ_k)`. -/
theorem meanSeq_succ (η h μStar σ2 m₀ : ℝ) (k : ℕ) :
    meanSeq η h μStar σ2 m₀ (k + 1) = nextMean η h μStar σ2 (meanSeq η h μStar σ2 m₀ k) := by
  rw [meanSeq, meanSeq, Function.iterate_succ_apply']

/-- The variance sequence stays nonnegative when `s_0² ≥ 0`. -/
theorem varSeq_nonneg (η h σ2 : ℝ) {s2₀ : ℝ} (hs : 0 ≤ s2₀) (k : ℕ) :
    0 ≤ varSeq η h σ2 s2₀ k := by
  induction k with
  | zero => exact hs
  | succ k ih => rw [varSeq_succ]; exact nextVar_nonneg η h σ2 ih

/-- On a Gaussian law `N(m, s2)` the population map uses the law's own parameters:
`popMap (N(m, s2)) = eulerMap … m s2` (Mathlib's `integral_id_gaussianReal`,
`variance_id_gaussianReal`). -/
theorem popMap_gaussianReal (η h μStar σ2 m : ℝ) (s2 : ℝ≥0) :
    popMap η h μStar σ2 (gaussianReal m s2) = eulerMap η h μStar σ2 m s2 := by
  rw [popMap, integral_id_gaussianReal, variance_id_gaussianReal]

/-- On a Gaussian law `p = N(m, s2)` with `s2 ≠ 0` and target `p⋆ = N(μ⋆, σ⋆²)`, `σ⋆² ≠ 0`, the
population map is the exact PFG Euler step `x ↦ x + η h⁻¹ (∂ log p⋆ - ∂ log p)(x)`. -/
theorem popMap_gaussianReal_eq_score (η h μStar m : ℝ) {σ2 s2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (hs : s2 ≠ 0) (x : ℝ) :
    popMap η h μStar σ2 (gaussianReal m s2) x =
      x + η * (h⁻¹ *
        (score1 (gaussianPDFReal μStar σ2) x - score1 (gaussianPDFReal m s2) x)) := by
  rw [popMap_gaussianReal, eulerMap_eq_add_score η h μStar m hσ hs]

/-- **(a) iterated: the population law at step `k` is Gaussian.** Starting from
`N(μ_0, s_0²)`, the population PFG iteration satisfies `ρ_k = N(μ_k, s_k²)` for every `k`, where
`μ_k`, `s_k²` follow the recursions (34)-(35). No assumption on the parameters. -/
theorem popLaw_gaussianReal (η h μStar σ2 m₀ : ℝ) (s2₀ : ℝ≥0) (k : ℕ) :
    popLaw η h μStar σ2 (gaussianReal m₀ s2₀) k =
      gaussianReal (meanSeq η h μStar σ2 m₀ k)
        ⟨varSeq η h σ2 s2₀ k, varSeq_nonneg η h σ2 s2₀.coe_nonneg k⟩ := by
  change _ = gaussianReal _ (NNReal.mk _ _)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [popLaw, ih, popMap_gaussianReal, map_eulerMap_gaussianReal]
    congr 1
    · rw [meanSeq_succ]
    · ext; simp [nextVarNN, varSeq_succ]; rfl

/-- The mean of the population law at step `k` is `μ_k`. -/
theorem integral_id_popLaw (η h μStar σ2 m₀ : ℝ) (s2₀ : ℝ≥0) (k : ℕ) :
    ∫ x, x ∂(popLaw η h μStar σ2 (gaussianReal m₀ s2₀) k) = meanSeq η h μStar σ2 m₀ k := by
  rw [popLaw_gaussianReal]; exact integral_id_gaussianReal

/-- The variance of the population law at step `k` is `s_k²`. -/
theorem variance_id_popLaw (η h μStar σ2 m₀ : ℝ) (s2₀ : ℝ≥0) (k : ℕ) :
    Var[id; popLaw η h μStar σ2 (gaussianReal m₀ s2₀) k] = varSeq η h σ2 s2₀ k := by
  rw [popLaw_gaussianReal]; exact variance_id_gaussianReal

/-! ### (b)(ii) Mean-gap contraction -/

/-- **(b)(ii), one step.** `μ_{k+1} - μ⋆ = (1 - η/(h σ⋆²)) (μ_k - μ⋆)`, for all real
parameters. -/
theorem nextMean_sub (η h μStar σ2 m : ℝ) :
    nextMean η h μStar σ2 m - μStar = (1 - η / (h * σ2)) * (m - μStar) := by
  unfold nextMean; ring

/-- **(b)(ii), one step, absolute value.**
`|μ_{k+1} - μ⋆| = |1 - η/(h σ⋆²)| |μ_k - μ⋆|`, for all real parameters. -/
theorem abs_nextMean_sub (η h μStar σ2 m : ℝ) :
    |nextMean η h μStar σ2 m - μStar| = |1 - η / (h * σ2)| * |m - μStar| := by
  rw [nextMean_sub, abs_mul]

/-- **(b)(ii), iterated.** `μ_k - μ⋆ = (1 - η/(h σ⋆²))^k (μ_0 - μ⋆)`. -/
theorem meanSeq_sub (η h μStar σ2 m₀ : ℝ) (k : ℕ) :
    meanSeq η h μStar σ2 m₀ k - μStar = (1 - η / (h * σ2)) ^ k * (m₀ - μStar) := by
  induction k with
  | zero => simp [meanSeq_zero]
  | succ k ih => rw [meanSeq_succ, nextMean_sub, ih]; ring

/-- **(b)(ii), iterated, absolute value.**
`|μ_k - μ⋆| = |1 - η/(h σ⋆²)|^k |μ_0 - μ⋆|`. -/
theorem abs_meanSeq_sub (η h μStar σ2 m₀ : ℝ) (k : ℕ) :
    |meanSeq η h μStar σ2 m₀ k - μStar| = |1 - η / (h * σ2)| ^ k * |m₀ - μStar| := by
  rw [meanSeq_sub, abs_mul, abs_pow]

/-! ### (b)(i), (b)(iii) Variance -/

/-- The paper's step-size condition `η ≤ h σ⋆²/2` (with `h, σ⋆² > 0`) means
`α = η/(h σ⋆²) ≤ 1/2`. -/
theorem stepRatio_le_half {η h σ2 : ℝ} (hh : 0 < h) (hσ : 0 < σ2) (hη : η ≤ h * σ2 / 2) :
    η / (h * σ2) ≤ 1 / 2 := by
  rw [div_le_iff₀ (mul_pos hh hσ)]; linarith

/-- **Exact variance-gap identity (lower form).** For `σ⋆² ≠ 0`, `s² ≠ 0` and `α = η/(h σ⋆²)`,
`s'² - σ⋆² = (1 - 2α)(s² - σ⋆²) + α² (s² - σ⋆²)² / s²`, where `s'² = nextVar η h σ⋆² s²`. -/
theorem nextVar_sub_eq_lower (η h : ℝ) {σ2 s2 : ℝ} (hσ : σ2 ≠ 0) (hs : s2 ≠ 0) :
    nextVar η h σ2 s2 - σ2 =
      (1 - 2 * (η / (h * σ2))) * (s2 - σ2) + (η / (h * σ2)) ^ 2 * (s2 - σ2) ^ 2 / s2 := by
  have hη : η / h = η / (h * σ2) * σ2 := by
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ hσ]
  unfold nextVar
  rw [hη]
  field_simp
  ring

/-- **Exact variance-gap identity (upper form).** For `σ⋆² ≠ 0`, `s² ≠ 0` and `α = η/(h σ⋆²)`,
`s'² - σ⋆² = (1 - α)² (s² - σ⋆²) - α² σ⋆² (s² - σ⋆²) / s²`. -/
theorem nextVar_sub_eq_upper (η h : ℝ) {σ2 s2 : ℝ} (hσ : σ2 ≠ 0) (hs : s2 ≠ 0) :
    nextVar η h σ2 s2 - σ2 =
      (1 - η / (h * σ2)) ^ 2 * (s2 - σ2) - (η / (h * σ2)) ^ 2 * σ2 * (s2 - σ2) / s2 := by
  rw [nextVar_sub_eq_lower η h hσ hs]
  field_simp
  ring

/-- Lower bound on the new variance gap: for `σ⋆² ≠ 0` and `s² > 0` (any `η`, `h`),
`(1 - 2α)(s² - σ⋆²) ≤ s'² - σ⋆²`. -/
theorem nextVar_sub_ge (η h : ℝ) {σ2 s2 : ℝ} (hσ : σ2 ≠ 0) (hs : 0 < s2) :
    (1 - 2 * (η / (h * σ2))) * (s2 - σ2) ≤ nextVar η h σ2 s2 - σ2 := by
  rw [nextVar_sub_eq_lower η h hσ hs.ne']
  have : 0 ≤ (η / (h * σ2)) ^ 2 * (s2 - σ2) ^ 2 / s2 := by positivity
  linarith

/-- Upper bound on the new variance gap: for `0 < σ⋆² ≤ s²` (any `η`, `h`),
`s'² - σ⋆² ≤ (1 - α)² (s² - σ⋆²)`. -/
theorem nextVar_sub_le (η h : ℝ) {σ2 s2 : ℝ} (hσ : 0 < σ2) (hs : σ2 ≤ s2) :
    nextVar η h σ2 s2 - σ2 ≤ (1 - η / (h * σ2)) ^ 2 * (s2 - σ2) := by
  have hs0 : 0 < s2 := hσ.trans_le hs
  rw [nextVar_sub_eq_upper η h hσ.ne' hs0.ne']
  have hd : 0 ≤ s2 - σ2 := sub_nonneg.mpr hs
  have : 0 ≤ (η / (h * σ2)) ^ 2 * σ2 * (s2 - σ2) / s2 := by positivity
  linarith

/-- **(b)(i), one step.** If `h > 0`, `σ⋆² > 0`, `η ≤ h σ⋆²/2` and `s² ≥ σ⋆²`, then
`s'² = nextVar η h σ⋆² s² ≥ σ⋆²`. -/
theorem le_nextVar {η h σ2 s2 : ℝ} (hh : 0 < h) (hη : η ≤ h * σ2 / 2) (hσ : 0 < σ2)
    (hs : σ2 ≤ s2) : σ2 ≤ nextVar η h σ2 s2 := by
  have hα := stepRatio_le_half hh hσ hη
  have h1 := nextVar_sub_ge η h hσ.ne' (hσ.trans_le hs)
  have : 0 ≤ (1 - 2 * (η / (h * σ2))) * (s2 - σ2) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hs)
  linarith

/-- **(b)(i), all steps.** If `h > 0`, `σ⋆² > 0`, `η ≤ h σ⋆²/2` and
`s_0² ≥ σ⋆²`, then `s_k² ≥ σ⋆²` for every `k`. -/
theorem le_varSeq {η h σ2 s2₀ : ℝ} (hh : 0 < h) (hη : η ≤ h * σ2 / 2) (hσ : 0 < σ2)
    (hs : σ2 ≤ s2₀) (k : ℕ) : σ2 ≤ varSeq η h σ2 s2₀ k := by
  induction k with
  | zero => exact hs
  | succ k ih => rw [varSeq_succ]; exact le_nextVar hh hη hσ ih

/-- **(b)(i) at the level of laws.** Under `h > 0`, `σ⋆² > 0`, `η ≤ h σ⋆²/2`, `s_0² ≥ σ⋆²`,
every population law `ρ_k` started at `N(μ_0, s_0²)` has variance at least `σ⋆²`. -/
theorem le_variance_popLaw {η h σ2 : ℝ} (hh : 0 < h) (hη : η ≤ h * σ2 / 2) (hσ : 0 < σ2)
    (μStar m₀ : ℝ) {s2₀ : ℝ≥0} (hs : σ2 ≤ s2₀) (k : ℕ) :
    σ2 ≤ Var[id; popLaw η h μStar σ2 (gaussianReal m₀ s2₀) k] := by
  rw [variance_id_popLaw]; exact le_varSeq hh hη hσ hs k

/-- **Sharpness of the step-size condition in (b)(i).** If `h > 0`, `σ⋆² > 0` and
`η > h σ⋆²/2`, there is a variance `s² > σ⋆²` whose image `s'² = nextVar η h σ⋆² s²` is strictly
below `σ⋆²`. So `η ≤ h σ⋆²/2` cannot be weakened in (b)(i). -/
theorem exists_nextVar_lt_of_lt {η h σ2 : ℝ} (hh : 0 < h) (hσ : 0 < σ2)
    (hη : h * σ2 / 2 < η) : ∃ s2, σ2 < s2 ∧ nextVar η h σ2 s2 < σ2 := by
  set α := η / (h * σ2) with hα_def
  have hα : 1 / 2 < α := by
    rw [hα_def, lt_div_iff₀ (mul_pos hh hσ)]; linarith
  have hα0 : 0 < α := by linarith
  set d := (2 * α - 1) * σ2 / α ^ 2 with hd_def
  have hd : 0 < d := by
    rw [hd_def]; exact div_pos (mul_pos (by linarith) hσ) (by positivity)
  refine ⟨σ2 + d, by linarith, ?_⟩
  have hs : 0 < σ2 + d := by linarith
  have key := nextVar_sub_eq_lower η h hσ.ne' hs.ne'
  rw [← hα_def, show σ2 + d - σ2 = d by ring] at key
  have h1 : α ^ 2 * d ^ 2 / (σ2 + d) = (2 * α - 1) * d * (σ2 / (σ2 + d)) := by
    rw [hd_def]; field_simp
  have h2 : σ2 / (σ2 + d) < 1 := by rw [div_lt_one hs]; linarith
  have h3 : (2 * α - 1) * d * (σ2 / (σ2 + d)) < (2 * α - 1) * d := by
    have : 0 < (2 * α - 1) * d := mul_pos (by linarith) hd
    nlinarith
  linarith

/-- **(b)(iii), squared factor.** For `0 < σ⋆² ≤ s²` (any `η`, `h`), the relative variance gap
contracts with factor `(1 - α)²`:
`(s'² - σ⋆²)/σ⋆² ≤ (1 - η/(h σ⋆²))² (s² - σ⋆²)/σ⋆²`. -/
theorem relGap_nextVar_le_sq (η h : ℝ) {σ2 s2 : ℝ} (hσ : 0 < σ2) (hs : σ2 ≤ s2) :
    (nextVar η h σ2 s2 - σ2) / σ2 ≤ (1 - η / (h * σ2)) ^ 2 * ((s2 - σ2) / σ2) := by
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (nextVar_sub_le η h hσ hs) hσ.le

/-- **Lower bound for the relative gap.** For `σ⋆² > 0`, `s² > 0` (any real `η`, `h`) and
`α = η/(h σ⋆²)`, `(1 - 2α)(s² - σ⋆²)/σ⋆² ≤ (s'² - σ⋆²)/σ⋆²`. Together with
`relGap_nextVar_le_sq` (which needs `0 < σ⋆² ≤ s²`) this gives, for `0 < σ⋆² ≤ s²`, the
two-sided bounds `(1 - 2α) g ≤ g' ≤ (1 - α)² g` on the relative gaps
`g = (s² - σ⋆²)/σ⋆²`, `g' = (s'² - σ⋆²)/σ⋆²`. The two factors differ by `α²`
(`(1 - α)² = (1 - 2α) + α²`), so they agree only to first order in `α`; the bounds do not pin
down the one-step rate. -/
theorem relGap_nextVar_ge (η h : ℝ) {σ2 s2 : ℝ} (hσ : 0 < σ2) (hs : 0 < s2) :
    (1 - 2 * (η / (h * σ2))) * ((s2 - σ2) / σ2) ≤ (nextVar η h σ2 s2 - σ2) / σ2 := by
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (nextVar_sub_ge η h hσ.ne' hs) hσ.le

/-- **(b)(iii).** If `0 ≤ η`, `h > 0`, `η ≤ h σ⋆²` (implied by the
paper's `η ≤ h σ⋆²/2`), `σ⋆² > 0` and `s² ≥ σ⋆²`, then
`(s'² - σ⋆²)/σ⋆² ≤ (1 - η/(h σ⋆²)) (s² - σ⋆²)/σ⋆²`. -/
theorem relGap_nextVar_le {η h σ2 s2 : ℝ} (hη0 : 0 ≤ η) (hh : 0 < h) (hη : η ≤ h * σ2)
    (hσ : 0 < σ2) (hs : σ2 ≤ s2) :
    (nextVar η h σ2 s2 - σ2) / σ2 ≤ (1 - η / (h * σ2)) * ((s2 - σ2) / σ2) := by
  have hα0 : 0 ≤ η / (h * σ2) := by positivity
  have hα1 : η / (h * σ2) ≤ 1 := by rw [div_le_one (mul_pos hh hσ)]; exact hη
  have hg : 0 ≤ (s2 - σ2) / σ2 := div_nonneg (sub_nonneg.mpr hs) hσ.le
  refine (relGap_nextVar_le_sq η h hσ hs).trans ?_
  apply mul_le_mul_of_nonneg_right _ hg
  nlinarith

/-- **(b)(iii), absolute-value form.** If `0 ≤ η`, `h > 0`,
`η ≤ h σ⋆²/2`, `σ⋆² > 0` and `s² ≥ σ⋆²`, then
`|(s'² - σ⋆²)/σ⋆²| ≤ (1 - η/(h σ⋆²)) |(s² - σ⋆²)/σ⋆²|`. -/
theorem abs_relGap_nextVar_le {η h σ2 s2 : ℝ} (hη0 : 0 ≤ η) (hh : 0 < h)
    (hη : η ≤ h * σ2 / 2) (hσ : 0 < σ2) (hs : σ2 ≤ s2) :
    |(nextVar η h σ2 s2 - σ2) / σ2| ≤ (1 - η / (h * σ2)) * |(s2 - σ2) / σ2| := by
  have hg : 0 ≤ (s2 - σ2) / σ2 := div_nonneg (sub_nonneg.mpr hs) hσ.le
  have hg' : 0 ≤ (nextVar η h σ2 s2 - σ2) / σ2 :=
    div_nonneg (sub_nonneg.mpr (le_nextVar hh hη hσ hs)) hσ.le
  rw [abs_of_nonneg hg, abs_of_nonneg hg']
  exact relGap_nextVar_le hη0 hh (by nlinarith [mul_pos hh hσ]) hσ hs

/-- **(b)(iii), iterated, squared factor.** If `h > 0`, `η ≤ h σ⋆²/2`, `σ⋆² > 0` and
`s_0² ≥ σ⋆²`, then `(s_k² - σ⋆²)/σ⋆² ≤ (1 - α)^{2k} (s_0² - σ⋆²)/σ⋆²`. -/
theorem relGap_varSeq_le_sq {η h σ2 s2₀ : ℝ} (hh : 0 < h) (hη : η ≤ h * σ2 / 2)
    (hσ : 0 < σ2) (hs : σ2 ≤ s2₀) (k : ℕ) :
    (varSeq η h σ2 s2₀ k - σ2) / σ2 ≤ (1 - η / (h * σ2)) ^ (2 * k) * ((s2₀ - σ2) / σ2) := by
  induction k with
  | zero => simp [varSeq_zero]
  | succ k ih =>
    rw [varSeq_succ]
    refine (relGap_nextVar_le_sq η h hσ (le_varSeq hh hη hσ hs k)).trans ?_
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left ih (sq_nonneg _)

/-- **(b)(iii), iterated, paper's rate.** If `0 ≤ η`, `h > 0`, `η ≤ h σ⋆²/2`, `σ⋆² > 0` and
`s_0² ≥ σ⋆²`, then `(s_k² - σ⋆²)/σ⋆² ≤ (1 - α)^k (s_0² - σ⋆²)/σ⋆²` (and the left side is
nonnegative by `le_varSeq`). -/
theorem relGap_varSeq_le {η h σ2 s2₀ : ℝ} (hη0 : 0 ≤ η) (hh : 0 < h) (hη : η ≤ h * σ2 / 2)
    (hσ : 0 < σ2) (hs : σ2 ≤ s2₀) (k : ℕ) :
    (varSeq η h σ2 s2₀ k - σ2) / σ2 ≤ (1 - η / (h * σ2)) ^ k * ((s2₀ - σ2) / σ2) := by
  have hα0 : 0 ≤ η / (h * σ2) := by positivity
  have hα1 := stepRatio_le_half hh hσ hη
  have hg : 0 ≤ (s2₀ - σ2) / σ2 := div_nonneg (sub_nonneg.mpr hs) hσ.le
  refine (relGap_varSeq_le_sq hh hη hσ hs k).trans ?_
  apply mul_le_mul_of_nonneg_right _ hg
  rw [pow_mul]
  apply pow_le_pow_left₀ (sq_nonneg _)
  nlinarith

/-! ### The hypothesis `s² ≥ σ⋆²` of the Lean variance-gap bounds is necessary -/

/-- Witness values: `η = 1/2`, `h = 1`, `σ⋆² = 1`, `s² = 1/4` give `s'² = 25/16`. -/
theorem nextVar_example_below : nextVar (1 / 2) 1 1 (1 / 4) = 25 / 16 := by
  norm_num [nextVar]

/-- **Necessity of `s² ≥ σ⋆²` in `relGap_nextVar_le` (one-sided form).** The relative variance-gap
contraction `(s'² - σ⋆²)/σ⋆² ≤ (1 - α)(s² - σ⋆²)/σ⋆²` is false in general when `s² < σ⋆²`, even
with `η > 0`, `h > 0` and the step-size condition `η ≤ h σ⋆²/2`: at `η = 1/2`, `h = σ⋆² = 1`,
`s² = 1/4` the left side is `9/16` and the right side `-3/8`. -/
theorem not_forall_relGap_contraction :
    ¬ ∀ η h σ2 s2 : ℝ, 0 < η → 0 < h → 0 < σ2 → 0 < s2 → η ≤ h * σ2 / 2 →
      (nextVar η h σ2 s2 - σ2) / σ2 ≤ (1 - η / (h * σ2)) * ((s2 - σ2) / σ2) := by
  intro H
  have := H (1 / 2) 1 1 (1 / 4) (by norm_num) one_pos one_pos (by norm_num) (by norm_num)
  rw [nextVar_example_below] at this
  norm_num at this

/-- **Necessity of `s² ≥ σ⋆²` in `abs_relGap_nextVar_le` (absolute-value form).** The contraction
`|(s'² - σ⋆²)/σ⋆²| ≤ (1 - α) |(s² - σ⋆²)/σ⋆²|` is false in general when `s² < σ⋆²` (same
witness: `9/16 > 3/8`): the variance overshoots the target. -/
theorem not_forall_abs_relGap_contraction :
    ¬ ∀ η h σ2 s2 : ℝ, 0 < η → 0 < h → 0 < σ2 → 0 < s2 → η ≤ h * σ2 / 2 →
      |(nextVar η h σ2 s2 - σ2) / σ2| ≤ (1 - η / (h * σ2)) * |(s2 - σ2) / σ2| := by
  intro H
  have := H (1 / 2) 1 1 (1 / 4) (by norm_num) one_pos one_pos (by norm_num) (by norm_num)
  rw [nextVar_example_below] at this
  norm_num [abs_of_pos, abs_of_neg] at this

/-! ### (c) The target is an exact fixed point -/

/-- At the target (`μ_k = μ⋆`, `s_k² = σ⋆²`) the Euler map is the identity: the velocity
`(μ⋆ - x)/σ⋆² + (x - μ⋆)/σ⋆²` vanishes identically (all real parameters). -/
theorem eulerMap_target (η h μStar σ2 : ℝ) : eulerMap η h μStar σ2 μStar σ2 = id := by
  funext x; simp only [eulerMap, id]; ring

/-- The mean recursion fixes `μ⋆`. -/
theorem nextMean_target (η h μStar σ2 : ℝ) : nextMean η h μStar σ2 μStar = μStar := by
  unfold nextMean; ring

/-- The variance recursion fixes `σ⋆²`. -/
theorem nextVar_target (η h σ2 : ℝ) : nextVar η h σ2 σ2 = σ2 := by
  simp [nextVar]

/-- **(c) Exactness at the target.** One population PFG Euler step from the target returns
the target exactly: `T # N(μ⋆, σ⋆²) = N(μ⋆, σ⋆²)` for every step size and preconditioner. -/
theorem map_eulerMap_target (η h μStar : ℝ) (σ2 : ℝ≥0) :
    (gaussianReal μStar σ2).map (eulerMap η h μStar σ2 μStar σ2) = gaussianReal μStar σ2 := by
  rw [eulerMap_target, Measure.map_id]

/-- **(c) Exactness at the target, iterated.** The population iteration started at the
target stays there: `ρ_k = N(μ⋆, σ⋆²)` for all `k`. -/
theorem popLaw_target (η h μStar : ℝ) (σ2 : ℝ≥0) (k : ℕ) :
    popLaw η h μStar σ2 (gaussianReal μStar σ2) k = gaussianReal μStar σ2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popLaw, ih, popMap_gaussianReal, map_eulerMap_target]

/-- **(c) PFG versus ULA at the target `N(0, 1)`.** For every `η`, `h`, one population PFG
Euler step from `N(0, 1)` returns `N(0, 1)`, while one ULA step with step size `hU > 0` does not
(`Counterexamples.ULADiscretization.ulaStep_standardGaussian_ne`). -/
theorem flow_exact_ula_biased (η h : ℝ) {hU : ℝ} (hU0 : 0 < hU) :
    (gaussianReal 0 1).map (popMap η h 0 1 (gaussianReal 0 1)) = gaussianReal 0 1 ∧
      Counterexamples.ULADiscretization.ulaStep hU (gaussianReal 0 1) ≠ gaussianReal 0 1 := by
  refine ⟨?_, Counterexamples.ULADiscretization.ulaStep_standardGaussian_ne hU0⟩
  have := popLaw_target η h 0 1 1
  simpa [popLaw] using this

/-- Uniqueness of the mean fixed point: for `η, h, σ⋆² ≠ 0`, `nextMean m = m ↔ m = μ⋆`. -/
theorem nextMean_eq_self_iff {η h σ2 : ℝ} (hη : η ≠ 0) (hh : h ≠ 0) (hσ : σ2 ≠ 0)
    (μStar m : ℝ) : nextMean η h μStar σ2 m = m ↔ m = μStar := by
  have hα : η / (h * σ2) ≠ 0 := div_ne_zero hη (mul_ne_zero hh hσ)
  constructor
  · intro heq
    have e : nextMean η h μStar σ2 m - m = η / (h * σ2) * (μStar - m) := by
      unfold nextMean; ring
    have : η / (h * σ2) * (μStar - m) = 0 := by rw [← e, heq, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hα
    · linarith
  · rintro rfl; exact nextMean_target η h m σ2

/-- Uniqueness of the variance fixed point: for `η, h, σ⋆², s² > 0` and `η ≤ 2 h σ⋆²`,
`nextVar s² = s² ↔ s² = σ⋆²`. -/
theorem nextVar_eq_self_iff {η h σ2 s2 : ℝ} (hη : 0 < η) (hh : 0 < h) (hσ : 0 < σ2)
    (hs : 0 < s2) (hη2 : η ≤ 2 * h * σ2) : nextVar η h σ2 s2 = s2 ↔ s2 = σ2 := by
  constructor
  · intro heq
    set c := η / h * (1 / s2 - 1 / σ2) with hc_def
    have h1 : s2 * (c * (c + 2)) = 0 := by
      have : nextVar η h σ2 s2 = s2 * (1 + c) ^ 2 := rfl
      linear_combination heq - this
    have h2 : c * (c + 2) = 0 := (mul_eq_zero.mp h1).resolve_left hs.ne'
    have hc2 : 0 < c + 2 := by
      have e1 : η / h * (1 / σ2) ≤ 2 := by
        rw [mul_one_div, div_div, div_le_iff₀ (mul_pos hh hσ)]; linarith
      have e2 : 0 < η / h * (1 / s2) := by positivity
      rw [hc_def, mul_sub]; linarith
    have h3 : c = 0 := (mul_eq_zero.mp h2).resolve_right hc2.ne'
    have h4 : 1 / s2 - 1 / σ2 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (div_pos hη hh).ne'
    have h5 : 1 / s2 = 1 / σ2 := sub_eq_zero.mp h4
    rwa [one_div, one_div, inv_inj] at h5
  · rintro rfl; exact nextVar_target η h s2

/-- **(c) The target is the only Gaussian fixed point for moderate steps.** For `η, h > 0`,
`σ⋆² > 0`, `η ≤ 2 h σ⋆²` and `s² ≠ 0`, one population step fixes `N(m, s²)` if and only if
`m = μ⋆` and `s² = σ⋆²`. -/
theorem map_popMap_eq_self_iff {η h σ2 : ℝ} (hη : 0 < η) (hh : 0 < h) (hσ : 0 < σ2)
    (hη2 : η ≤ 2 * h * σ2) (μStar m : ℝ) {s2 : ℝ≥0} (hs : s2 ≠ 0) :
    (gaussianReal m s2).map (popMap η h μStar σ2 (gaussianReal m s2)) = gaussianReal m s2 ↔
      m = μStar ∧ (s2 : ℝ) = σ2 := by
  rw [popMap_gaussianReal, map_eulerMap_gaussianReal, gaussianReal_ext_iff,
    nextMean_eq_self_iff hη.ne' hh.ne' hσ.ne', ← NNReal.coe_inj]
  change m = μStar ∧ nextVar η h σ2 s2 = s2 ↔ _
  rw [nextVar_eq_self_iff hη hh hσ (by positivity) hη2]

/-- **Counterexample: spurious fixed point for a large step.** With `η = 4`, `h = 1`, target
`N(0, 1)`, the population step fixes `N(0, 2) ≠ N(0, 1)` (the Euler map is `x ↦ -x`). So some
step-size restriction (e.g. `η ≤ 2 h σ⋆²` in `map_popMap_eq_self_iff`) is needed for the target
to be the unique fixed point. -/
theorem spurious_fixedPoint :
    (gaussianReal 0 2).map (popMap 4 1 0 1 (gaussianReal 0 2)) = gaussianReal 0 2 ∧
      gaussianReal (0 : ℝ) 2 ≠ gaussianReal 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [popMap_gaussianReal, map_eulerMap_gaussianReal]
    congr 1
    · norm_num [nextMean]
    · ext; norm_num [nextVarNN, nextVar]; rfl
  · intro heq
    have := (gaussianReal_ext_iff.mp heq).2
    norm_num at this

/-! ### The diagonal `d`-dimensional case is a product of one-dimensional problems -/

/-- **Diagonal case, coordinate form.** The coordinatewise Euler map pushes the product
Gaussian `⊗ᵢ N(mᵢ, s2ᵢ)` forward to `⊗ᵢ N(nextMeanᵢ, nextVarᵢ)` (all real parameters). -/
theorem map_eulerMap_pi {d : ℕ} (η : ℝ) (h μStar σ2 m : Fin d → ℝ) (s2 : Fin d → ℝ≥0) :
    (Measure.pi fun i => gaussianReal (m i) (s2 i)).map
        (fun x i => eulerMap η (h i) (μStar i) (σ2 i) (m i) (s2 i) (x i)) =
      Measure.pi fun i => gaussianReal (nextMean η (h i) (μStar i) (σ2 i) (m i))
        (nextVarNN η (h i) (σ2 i) (s2 i)) := by
  have : ∀ i, SigmaFinite ((gaussianReal (m i) (s2 i)).map
      (eulerMap η (h i) (μStar i) (σ2 i) (m i) (s2 i))) := by
    intro i; rw [map_eulerMap_gaussianReal]; infer_instance
  rw [Measure.pi_map_pi (fun i => (measurable_eulerMap _ _ _ _ _ _).aemeasurable)]
  simp_rw [map_eulerMap_gaussianReal]

/-- The inverse of an invertible diagonal matrix: if all `vᵢ ≠ 0` then
`(diagonal v)⁻¹ = diagonal (fun i => vᵢ⁻¹)`. -/
theorem inv_diagonal_eq {d : ℕ} {v : Fin d → ℝ} (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal fun i => (v i)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; exact inv_mul_cancel₀ (hv i)

/-- The paper's matrix update `x + η H⁻¹ (Σ⋆⁻¹ (μ⋆ - x) + Σ_k⁻¹ (x - μ_k))` with diagonal
`H = diag(h)`, `Σ⋆ = diag(σ2)`, `Σ_k = diag(s2)` (all diagonal entries nonzero) acts
coordinatewise by the one-dimensional Euler maps. -/
theorem eulerMap_pi_eq_matrix {d : ℕ} (η : ℝ) {h σ2 s2 : Fin d → ℝ} (hh : ∀ i, h i ≠ 0)
    (hσ : ∀ i, σ2 i ≠ 0) (hs : ∀ i, s2 i ≠ 0) (μStar m x : Fin d → ℝ) :
    (fun i => eulerMap η (h i) (μStar i) (σ2 i) (m i) (s2 i) (x i)) =
      x + η • ((Matrix.diagonal h)⁻¹ *ᵥ ((Matrix.diagonal σ2)⁻¹ *ᵥ (μStar - x) +
        (Matrix.diagonal s2)⁻¹ *ᵥ (x - m))) := by
  rw [inv_diagonal_eq hh, inv_diagonal_eq hσ, inv_diagonal_eq hs]
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    eulerMap]
  ring

/-- **(a), diagonal `d`-dimensional case (App. A.6).** For diagonal `H = diag(h)`,
`Σ⋆ = diag(σ2)` and current law `⊗ᵢ N(mᵢ, s2ᵢ)` (all diagonal entries nonzero), the population
PFG step `x ↦ x + η H⁻¹ (Σ⋆⁻¹ (μ⋆ - x) + Σ_k⁻¹ (x - μ_k))` maps the current law to
`⊗ᵢ N(nextMeanᵢ, nextVarᵢ)`: the problem is a product of independent one-dimensional ones. -/
theorem map_flowEulerStep_diagonal {d : ℕ} (η : ℝ) {h σ2 : Fin d → ℝ} (hh : ∀ i, h i ≠ 0)
    (hσ : ∀ i, σ2 i ≠ 0) (μStar m : Fin d → ℝ) {s2 : Fin d → ℝ≥0} (hs : ∀ i, s2 i ≠ 0) :
    (Measure.pi fun i => gaussianReal (m i) (s2 i)).map
        (fun x => x + η • ((Matrix.diagonal h)⁻¹ *ᵥ ((Matrix.diagonal σ2)⁻¹ *ᵥ (μStar - x) +
          (Matrix.diagonal fun i => (s2 i : ℝ))⁻¹ *ᵥ (x - m)))) =
      Measure.pi fun i => gaussianReal (nextMean η (h i) (μStar i) (σ2 i) (m i))
        (nextVarNN η (h i) (σ2 i) (s2 i)) := by
  have hs' : ∀ i, (s2 i : ℝ) ≠ 0 := fun i => NNReal.coe_ne_zero.mpr (hs i)
  have : (fun x : Fin d → ℝ => x + η • ((Matrix.diagonal h)⁻¹ *ᵥ ((Matrix.diagonal σ2)⁻¹ *ᵥ
      (μStar - x) + (Matrix.diagonal fun i => (s2 i : ℝ))⁻¹ *ᵥ (x - m)))) =
      fun x i => eulerMap η (h i) (μStar i) (σ2 i) (m i) (s2 i) (x i) := by
    funext x
    exact (eulerMap_pi_eq_matrix η hh hσ hs' μStar m x).symm
  rw [this, map_eulerMap_pi]

/-! ### Eq. (33) in one dimension: KL contraction -/

/-- The elementary inequality used for Eq. (33): `x - log(1 + x) ≤ x²/2` for `x ≥ 0` (from
Mathlib's `Real.le_log_one_add_of_nonneg`, `2x/(x + 2) ≤ log(1 + x)`). -/
theorem sub_log_one_add_le {x : ℝ} (hx : 0 ≤ x) : x - Real.log (1 + x) ≤ x ^ 2 / 2 := by
  have h := Real.le_log_one_add_of_nonneg hx
  have e : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by field_simp; ring
  have h2 : x ^ 2 / (x + 2) ≤ x ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg x) two_pos (by linarith)
  linarith

/-- **One-coordinate KL bound behind Eq. (33).** If `σ⋆² ≠ 0` and `v ≥ σ⋆²`, then
`KL(N(m, v) ‖ N(μ⋆, σ⋆²)) ≤ ½ ((m - μ⋆)²/σ⋆² + ½ ((v - σ⋆²)/σ⋆²)²)`. -/
theorem klDiv_gaussianReal_le (m μStar : ℝ) {v σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (hs : σ2 ≤ v) :
    klDiv (gaussianReal m v) (gaussianReal μStar σ2) ≤
      ENNReal.ofReal
        ((1 / 2) * ((m - μStar) ^ 2 / σ2 + (1 / 2) * (((v : ℝ) - σ2) / σ2) ^ 2)) := by
  have hσ' : 0 < (σ2 : ℝ) := by positivity
  have hv : v ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr hσ) hs).ne'
  rw [klDiv_gaussianReal_gaussianReal m μStar hv hσ]
  apply ENNReal.ofReal_le_ofReal
  have hg : 0 ≤ ((v : ℝ) - σ2) / σ2 :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hs)) hσ'.le
  have hvg : (v : ℝ) / σ2 = 1 + ((v : ℝ) - σ2) / σ2 := by field_simp; ring
  have key := sub_log_one_add_le hg
  rw [← hvg] at key
  have : (v : ℝ) / σ2 - 1 = ((v : ℝ) - σ2) / σ2 := by rw [hvg]; ring
  nlinarith

/-- **Eq. (33), one dimension.** If `0 ≤ η`, `h > 0`, `σ⋆² ≠ 0`, `η ≤ h σ⋆²/2` and
`s_0² ≥ σ⋆²`, the population PFG iteration started at `N(μ_0, s_0²)` satisfies, for all `k`,
`KL(ρ_k ‖ N(μ⋆, σ⋆²)) ≤ (1 - η/(h σ⋆²))^{2k} C_0` with
`C_0 = ½ ((μ_0 - μ⋆)²/σ⋆² + ½ ((s_0² - σ⋆²)/σ⋆²)²)`. -/
theorem klDiv_popLaw_le {η h : ℝ} {σ2 s2₀ : ℝ≥0} (hη0 : 0 ≤ η) (hh : 0 < h) (hσ : σ2 ≠ 0)
    (hη : η ≤ h * σ2 / 2) (hs : σ2 ≤ s2₀) (μStar m₀ : ℝ) (k : ℕ) :
    klDiv (popLaw η h μStar σ2 (gaussianReal m₀ s2₀) k) (gaussianReal μStar σ2) ≤
      ENNReal.ofReal ((1 - η / (h * σ2)) ^ (2 * k) *
        ((1 / 2) * ((m₀ - μStar) ^ 2 / σ2 + (1 / 2) * (((s2₀ : ℝ) - σ2) / σ2) ^ 2))) := by
  have hσ' : 0 < (σ2 : ℝ) := by positivity
  have hs' : (σ2 : ℝ) ≤ s2₀ := by exact_mod_cast hs
  have hV := le_varSeq hh hη hσ' hs' k
  rw [popLaw_gaussianReal]
  change klDiv (gaussianReal _ (NNReal.mk _ _)) _ ≤ _
  refine (klDiv_gaussianReal_le _ _ hσ ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [← NNReal.coe_le_coe]; exact hV
  · simp only [NNReal.coe_mk]
    have hα0 : 0 ≤ η / (h * σ2) := by positivity
    have hα1 : η / (h * σ2) ≤ 1 / 2 := stepRatio_le_half hh hσ' hη
    have hm := meanSeq_sub η h μStar σ2 m₀ k
    have hG0 : 0 ≤ (varSeq η h σ2 s2₀ k - σ2) / σ2 := div_nonneg (sub_nonneg.mpr hV) hσ'.le
    have hG := relGap_varSeq_le hη0 hh hη hσ' hs' k
    have hG2 : ((varSeq η h σ2 s2₀ k - σ2) / σ2) ^ 2 ≤
        (1 - η / (h * σ2)) ^ (2 * k) * (((s2₀ : ℝ) - σ2) / σ2) ^ 2 := by
      calc ((varSeq η h σ2 s2₀ k - σ2) / σ2) ^ 2
          ≤ ((1 - η / (h * σ2)) ^ k * (((s2₀ : ℝ) - σ2) / σ2)) ^ 2 :=
            pow_le_pow_left₀ hG0 hG 2
        _ = (1 - η / (h * σ2)) ^ (2 * k) * (((s2₀ : ℝ) - σ2) / σ2) ^ 2 := by ring
    have hA : (meanSeq η h μStar σ2 m₀ k - μStar) ^ 2 / σ2 =
        (1 - η / (h * σ2)) ^ (2 * k) * ((m₀ - μStar) ^ 2 / σ2) := by
      rw [hm]; ring
    rw [hA]
    nlinarith

/-- **Eq. (33), the paper's special case `h = σ⋆⁻²`, `η = 1/2` (one dimension).** For
`σ⋆² ≠ 0` and `s_0² ≥ σ⋆²`, `KL(ρ_k ‖ N(μ⋆, σ⋆²)) ≤ 4^{-k} C_0`. -/
theorem klDiv_popLaw_le_quarter {σ2 s2₀ : ℝ≥0} (hσ : σ2 ≠ 0) (hs : σ2 ≤ s2₀) (μStar m₀ : ℝ)
    (k : ℕ) :
    klDiv (popLaw (1 / 2) (1 / (σ2 : ℝ)) μStar σ2 (gaussianReal m₀ s2₀) k)
        (gaussianReal μStar σ2) ≤
      ENNReal.ofReal ((1 / 4) ^ k *
        ((1 / 2) * ((m₀ - μStar) ^ 2 / σ2 + (1 / 2) * (((s2₀ : ℝ) - σ2) / σ2) ^ 2))) := by
  have hσ' : 0 < (σ2 : ℝ) := by positivity
  have h := klDiv_popLaw_le (η := 1 / 2) (h := 1 / (σ2 : ℝ)) (by norm_num) (by positivity) hσ
    (by field_simp; norm_num) hs μStar m₀ k
  have hα : (1 - 1 / 2 / (1 / (σ2 : ℝ) * σ2)) ^ (2 * k) = (1 / 4) ^ k := by
    rw [one_div_mul_cancel hσ'.ne', pow_mul]; norm_num
  rwa [hα] at h

end FormalizeSampling.DiscreteGaussianFlow
