module

public import FormalizeSampling.Flow.FokkerPlanckUniquenessLipschitzTight
public import FormalizeSampling.Flow.ContinuityUniquenessMollified

/-!
# Uniqueness for the weak Fokker–Planck equation with globally Lipschitz drift

Status: **Verified.** For `D > 0` and a drift `b : ℝ → ℝᵈ → ℝᵈ` that is jointly continuous and
**globally Lipschitz in `x`** (uniformly on bounded time intervals; hence of linear growth,
unbounded in general), two curves of probability measures on `t ≥ 0` solving
`WeakFokkerPlanck · b D` with the same initial law agree at every `t ≥ 0`. **No moment, density
or tightness assumption** is made on the solutions (uniform tightness on compact time intervals
is proved, `exists_tail_le`). This removes the restriction of `Flow/FokkerPlanckUniqueness`
(bounded drift) and `Flow/FokkerPlanckUniquenessUnbounded` (`-a x + bounded`). A globally
Lipschitz drift satisfies `⟨b(t, x), x⟩ ≤ C + C |x|²` on each bounded time interval, so the
uniqueness statement is a case of the classical theorem of Bogachev–Krylov–Röckner–Shaposhnikov
(2015, Ch. 9); the proof here is a formal one.

## Main results

* `integral_eq_of_weakFokkerPlanck_of_approx`: uniqueness (on test functions) when `b` is
  jointly continuous, of linear growth on every `[0, T] × ℝᵈ`, and every `b_t` (`t ∈ [0, T]`)
  is uniformly approximable by `C²` fields `w` with `‖Dw‖ ≤ L_T` and bounded `D²w`.
* Auxiliary arithmetic: `pow_growth_le`, `cutoff_terms_le`, `lip_error_arith`; the dual
  `lipDual` with `lipDual_props` and the telescoped estimate `abs_integral_sub_lipDual_le`.
* `exists_contDiff_lipschitz_approx_two`: mollification of an `L`-Lipschitz map gives such `w`
  (`C^∞`, `‖Dw‖ ≤ L`, `‖D²w‖ ≤ L ∫ ‖Dκ‖`, `‖w - f‖ ≤ L r`).
* `eq_of_weakFokkerPlanck_lipschitz`: **uniqueness for jointly continuous drifts, Lipschitz in
  `x` uniformly on every `[0, T]`**; `eq_of_weakFokkerPlanck_lipschitzWith` (autonomous).
* Well-posedness (with the existence theorems of `Flow/FokkerPlanckExistence*.lean`):
  `existsUnique_weakFokkerPlanck_lipschitz` (autonomous `L`-Lipschitz `b`, any initial law;
  the solution is the weak limit of the dyadic Euler–Maruyama laws),
  `existsUnique_weakFokkerPlanck_lipschitz_continuousTime` (time-dependent),
  `existsUnique_weakFokkerPlanck_langevin_lipschitz` (`b = -∇U`, `∇U` Lipschitz).
* `tendsto_emCurveP_of_weakFokkerPlanck_lipschitz`: for autonomous Lipschitz `b`, **every**
  probability solution is, at every `t ≥ 0`, the weak limit of the dyadic Euler–Maruyama laws
  started at `ρ 0`.
* Special cases stated with additional hypotheses that the proofs do not use:
  `existsUnique_weakFokkerPlanck` and `tendsto_emCurveP_of_weakFokkerPlanck` (bounded `b`),
  `existsUnique_weakFokkerPlanck_ou` (`b x = -a x`, `a ≥ 0`) and
  `existsUnique_weakFokkerPlanck_langevin_linear_add_bounded` (`‖∇U(x) - a x‖ ≤ B`).

## Method (approximate Kolmogorov duality by splitting)

For a smooth compactly supported `φ` and `T > 0`, with `h = T / N`, define backwards
`Ξ_0 = φ`, `Ξ_{j+1} = U_j(h)` (`lipDual`), where `U_j(τ) = stepDual D κ Ξ_j w_j τ` is a frozen
Euler transport step with a smooth approximant `w_j ≈ b_{T - j h}` followed by exact Gaussian
smoothing (`Flow/FokkerPlanckUniquenessLipschitzStep`). Then

* `‖DΞ_j‖ ≤ (1 + h L)^j ‖Dφ‖ ≤ e^{LT} ‖Dφ‖` and `|Ξ_j| ≤ sup |φ|` — the only quantitative
  regularity used; it needs `L`, not a bound on `b`;
* along any solution, `ψ(s) = χ_R U_j(T - j h - s)` satisfies the backward Kolmogorov equation
  up to `G (‖b_s - w_j‖ + L S d + h L ‖b_s‖)` on the support of the cutoff `χ_R` plus cutoff
  terms supported in `{‖x‖ ≥ R}`, which are bounded (`‖b‖ ‖∇χ_R‖ ≤ K (1 + ρ₁ R) A₁ / R`) and
  hence small after integration against `ρ_s`, by uniform tightness;
* telescoping over `N` steps (`abs_integral_sub_lipDual_le`), the smoothing defect
  `|Q_{√(2Dκ)} Ξ - Ξ| ≤ G √(2Dκ) d` at each step, and `R → ∞`, `h → 0`, `κ → 0` give
  `∫ φ dρ_T = ∫ φ dρ'_T` for two solutions with `ρ_0 = ρ'_0`.

## Not proved here

* **Locally Lipschitz or merely dissipative drifts** (e.g. `-∇U` with `U` quartic or double
  well): the gradient bound `‖DΞ_j‖ ≤ e^{LT}‖Dφ‖` needs a global Lipschitz constant, and the
  cutoff error `D ∇χ_R ⬝ ∇Ξ` is only small when that gradient bound does not depend on `R`.
  Uniqueness of probability solutions for such drifts is classical under
  `⟨b(t, x), x⟩ ≤ C + C |x|²` (Bogachev–Krylov–Röckner–Shaposhnikov, *Fokker–Planck–Kolmogorov
  Equations*, AMS 2015, Ch. 9) but is not formalised here; without such a growth condition it can
  fail in every dimension `d ≥ 2` (Bogachev–Krasovitskii–Shaposhnikov 2021, Sb. Math. 212:6).
  Existence is in `Flow/FokkerPlanckExistenceDissipative`.
* Drifts that are discontinuous in `t` (joint continuity gives the time modulus on compacts),
  degenerate (`D = 0`) or non-constant/matrix diffusions, `PreconditionedWeakFokkerPlanck`.
* No rate for the Euler–Maruyama approximation, no SDE theory, only one-time marginals.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Convolution
open scoped ContDiff

namespace FormalizeSampling.FokkerPlanckUniqueness
open NoiseScore FormalizeSampling.WeakFokkerPlanckOU FormalizeSampling.FokkerPlanckExistence

variable {d : ℕ}

/-! ### The backward dual -/

/-- **The approximate Kolmogorov dual.** `Ξ_0 = φ` and `Ξ_{j+1} = stepDual D κ Ξ_j (W (T - j h)) h`:
`j` backward steps of length `h` from time `T`, each a frozen Euler transport with the field
`W (T - j h)` followed by Gaussian smoothing of variance `2D(h + κ)`. -/
noncomputable def lipDual (D κ h T : ℝ) (W : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (φ : (Fin d → ℝ) → ℝ) : ℕ → (Fin d → ℝ) → ℝ
  | 0 => φ
  | j + 1 => stepDual D κ (lipDual D κ h T W φ j) (W (T - j * h)) h

/-- **Regularity of the dual (Verified).** If `φ ∈ BddC2` with `|φ| ≤ C₀`, `‖Dφ‖ ≤ G₀`, `h ≥ 0`,
and every `W t` is `C²` with `‖DW t‖ ≤ L` and bounded `D²W t`, then every `Ξ_j ∈ BddC2`,
`|Ξ_j| ≤ C₀` and `‖DΞ_j‖ ≤ G₀ (1 + h L)^j`. -/
theorem lipDual_props {D κ h T : ℝ} (hh : 0 ≤ h) {W : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ}
    (hW : ∀ t, ContDiff ℝ 2 (W t) ∧ (∀ y, ‖fderiv ℝ (W t) y‖ ≤ L) ∧
      ∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ (W t)) y‖ ≤ M)
    {φ : (Fin d → ℝ) → ℝ} (hφ : BddC2 φ) {C₀ G₀ : ℝ} (hC₀ : ∀ y, |φ y| ≤ C₀)
    (hG₀ : ∀ y, ‖fderiv ℝ φ y‖ ≤ G₀) (j : ℕ) :
    BddC2 (lipDual D κ h T W φ j) ∧ (∀ y, |lipDual D κ h T W φ j y| ≤ C₀) ∧
      ∀ y, ‖fderiv ℝ (lipDual D κ h T W φ j) y‖ ≤ G₀ * (1 + h * L) ^ j := by
  induction j with
  | zero => exact ⟨hφ, hC₀, fun y => by simpa [lipDual] using hG₀ y⟩
  | succ j ih =>
    obtain ⟨hb, hC, hG⟩ := ih
    obtain ⟨hw, hL, Mw, hMw⟩ := hW (T - j * h)
    refine ⟨bddC2_stepDual hb hw hL hMw D κ h, fun y => abs_stepDual_le hC D κ _ h y,
      fun y => ?_⟩
    refine (norm_fderiv_stepDual_le hb hG hw hL hMw D κ h y).trans (le_of_eq ?_)
    rw [abs_of_nonneg hh, pow_succ]
    ring

/-- `stepDual D κ Θ w 0 = heatOp √(2Dκ) Θ`. -/
theorem stepDual_zero (D κ : ℝ) (Θ : (Fin d → ℝ) → ℝ) (w : (Fin d → ℝ) → Fin d → ℝ) :
    stepDual D κ Θ w 0 = heatOp (Real.sqrt (2 * D * κ)) Θ := by
  funext x
  simp [stepDual, stepSigma]

/-- **Quantitative estimate along one solution (Verified).** Let `ρ` solve
`WeakFokkerPlanck ρ b D` (`D > 0`, `b s` continuous for `s ≥ 0`), `κ, h > 0`, `N h = T`. Let the
fields `W t` be `C²` with `‖DW t‖ ≤ L`, bounded `D²W t`; `φ ∈ BddC2` with `|φ| ≤ C₀`,
`‖Dφ‖ ≤ G₀`; `χ` a `C²_c` cutoff (`|χ| ≤ 1`, `‖∇χ‖ ≤ g₁`, `|Δχ| ≤ g₂`, derivatives vanishing
outside `Tl`, `ρ_s(Tl) ≤ θ` on `[0, T]`); and on `tsupport χ`: `‖b_s - W_{T - j h}‖ ≤ ε₁` for
`s ∈ [T - (j+1) h, T - j h]`, `‖b_s‖ ≤ B₁` for `s ∈ [0, T]`. With `G' = G₀ (1 + h L)^N`:

  `|∫ χ φ dρ_T - ∫ χ Ξ_N dρ_0| ≤ N (G' √(2Dκ) d + h (G' (ε₁ + L S(h) d + h L B₁) +`
  `  θ (C₀ d B₁ g₁ + 2 D d g₁ G' (1 + h L) + D C₀ g₂)))`. -/
theorem abs_integral_sub_lipDual_le {ρ : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D κ : ℝ} (hD : 0 < D) (hκ : 0 < κ)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakFokkerPlanck ρ b D)
    (hbc : ∀ s, 0 ≤ s → Continuous (b s)) {h T : ℝ} (hh : 0 < h) {N : ℕ} (hN : N * h = T)
    {W : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ}
    (hW : ∀ t, ContDiff ℝ 2 (W t) ∧ (∀ y, ‖fderiv ℝ (W t) y‖ ≤ L) ∧
      ∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ (W t)) y‖ ≤ M)
    {φ : (Fin d → ℝ) → ℝ} (hφ : BddC2 φ) {C₀ G₀ : ℝ} (hC₀ : ∀ y, |φ y| ≤ C₀)
    (hG₀ : ∀ y, ‖fderiv ℝ φ y‖ ≤ G₀)
    {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ x, |χ x| ≤ 1) {g₁ g₂ : ℝ} (hg₁ : ∀ x, ‖grad χ x‖ ≤ g₁)
    (hg₂ : ∀ x, |laplacian χ x| ≤ g₂) {Tl : Set (Fin d → ℝ)} (hTl : MeasurableSet Tl)
    (hTχ : ∀ x ∉ Tl, grad χ x = 0 ∧ laplacian χ x = 0) {θ : ℝ}
    (hθ : ∀ s ∈ Icc 0 T, (ρ s).real Tl ≤ θ) {ε₁ B₁ : ℝ} (hε₀ : 0 ≤ ε₁) (hB₀ : 0 ≤ B₁)
    (hε₁ : ∀ j < N, ∀ s ∈ Icc (T - (j + 1) * h) (T - j * h), ∀ x ∈ tsupport χ,
      ‖b s x - W (T - j * h) x‖ ≤ ε₁)
    (hB₁ : ∀ s ∈ Icc 0 T, ∀ x ∈ tsupport χ, ‖b s x‖ ≤ B₁) :
    |∫ x, χ x * φ x ∂(ρ T) - ∫ x, χ x * lipDual D κ h T W φ N x ∂(ρ 0)| ≤
      N * (G₀ * (1 + h * L) ^ N * Real.sqrt (2 * D * κ) * d +
        h * (G₀ * (1 + h * L) ^ N * (ε₁ + L * stepSigma D κ h * d + h * L * B₁) +
          θ * (C₀ * (d * B₁ * g₁) + 2 * D * (d * g₁ * (G₀ * (1 + h * L) ^ N * (1 + h * L))) +
            D * C₀ * g₂))) := by
  set G' : ℝ := G₀ * (1 + h * L) ^ N with hG'
  set E : ℝ := G' * Real.sqrt (2 * D * κ) * d +
    h * (G' * (ε₁ + L * stepSigma D κ h * d + h * L * B₁) +
      θ * (C₀ * (d * B₁ * g₁) + 2 * D * (d * g₁ * (G' * (1 + h * L))) + D * C₀ * g₂)) with hE
  have hL0 : 0 ≤ L := (norm_nonneg _).trans ((hW 0).2.1 0)
  have hG₀0 : 0 ≤ G₀ := (norm_nonneg _).trans (hG₀ 0)
  have hC₀0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0)
  have hg₁0 : 0 ≤ g₁ := (norm_nonneg _).trans (hg₁ 0)
  have hθ0 : 0 ≤ θ := measureReal_nonneg.trans (hθ 0 ⟨le_rfl, by rw [← hN]; positivity⟩)
  have hq : 1 ≤ 1 + h * L := by nlinarith
  set Ξ := lipDual D κ h T W φ with hΞ
  have hprops := lipDual_props (D := D) (κ := κ) (T := T) hh.le hW hφ hC₀ hG₀
  have hcχ : ∀ f : (Fin d → ℝ) → ℝ, Continuous f → ∀ μ : Measure (Fin d → ℝ),
      IsProbabilityMeasure μ → Integrable (fun x => χ x * f x) μ := by
    intro f hf μ _
    exact (hχ.continuous.mul hf).integrable_of_hasCompactSupport hχc.mul_right
  -- one step
  have hstep : ∀ j < N, |∫ x, χ x * Ξ j x ∂(ρ (T - j * h)) -
      ∫ x, χ x * Ξ (j + 1) x ∂(ρ (T - (j + 1) * h))| ≤ E := by
    intro j hj
    obtain ⟨hb, hC, hG⟩ := hprops j
    obtain ⟨hw, hLw, Mw, hMw⟩ := hW (T - j * h)
    have hGj : G₀ * (1 + h * L) ^ j ≤ G' :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hj.le) hG₀0
    have hjN : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hj
    have ha : 0 ≤ T - (j + 1) * h := by rw [← hN]; nlinarith
    have hac : T - (j + 1) * h ≤ T - j * h := by nlinarith
    have hca : T - j * h - (T - (j + 1) * h) = h := by ring
    have hsub : Icc (T - (j + 1) * h) (T - j * h) ⊆ Icc 0 T := fun s hs =>
      ⟨ha.trans hs.1, hs.2.trans (by nlinarith)⟩
    have hcpos : 0 ≤ T - j * h := ha.trans hac
    have := hprob _ hcpos
    -- smoothing defect
    have h1 : |∫ x, χ x * Ξ j x ∂(ρ (T - j * h)) -
        ∫ x, χ x * stepDual D κ (Ξ j) (W (T - j * h)) 0 x ∂(ρ (T - j * h))| ≤
        G' * Real.sqrt (2 * D * κ) * d := by
      rw [stepDual_zero]
      obtain ⟨M0, hM0⟩ := hb.2.1
      rw [← integral_sub (hcχ _ hb.1.continuous _ inferInstance)
        (hcχ _ (continuous_heatOp_of_bdd hb.1.continuous hM0 _) _ inferInstance)]
      refine abs_integral_le_of_abs_le (μ := ρ (T - j * h)) fun x => ?_
      rw [← mul_sub, abs_mul]
      have hd := abs_heatOp_sub_le (hb.1.differentiable two_ne_zero) hC hG
        (Real.sqrt (2 * D * κ)) x
      rw [abs_sub_comm, abs_of_nonneg (Real.sqrt_nonneg _)] at hd
      calc |χ x| * |Ξ j x - heatOp (Real.sqrt (2 * D * κ)) (Ξ j) x|
          ≤ 1 * (G₀ * (1 + h * L) ^ j * Real.sqrt (2 * D * κ) * d) :=
            mul_le_mul (hχ1 x) hd (abs_nonneg _) zero_le_one
        _ ≤ G' * Real.sqrt (2 * D * κ) * d := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGj
              (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
    -- the duality step
    have h2 := abs_integral_step_le hD hκ hprob hρ ha hac (fun s hs => hbc s (ha.trans hs.1))
      hb hC hG hw hLw hMw hχ hχc hχ1 hg₁ hg₂ hTl hTχ (fun s hs => hθ s (hsub hs)) hε₀ hB₀
      (fun s hs x hx => hε₁ j hj s hs x hx) (fun s hs x hx => hB₁ s (hsub hs) x hx)
    rw [hca] at h2
    have e2 : stepDual D κ (Ξ j) (W (T - j * h)) h = Ξ (j + 1) := rfl
    rw [e2] at h2
    have h2' : |∫ x, χ x * stepDual D κ (Ξ j) (W (T - j * h)) 0 x ∂(ρ (T - j * h)) -
        ∫ x, χ x * Ξ (j + 1) x ∂(ρ (T - (j + 1) * h))| ≤
        h * (G' * (ε₁ + L * stepSigma D κ h * d + h * L * B₁) +
          θ * (C₀ * (d * B₁ * g₁) + 2 * D * (d * g₁ * (G' * (1 + h * L))) + D * C₀ * g₂)) := by
      refine h2.trans (mul_le_mul_of_nonneg_left ?_ hh.le)
      have hS0 : 0 ≤ stepSigma D κ h := Real.sqrt_nonneg _
      gcongr
    calc _ ≤ |∫ x, χ x * Ξ j x ∂(ρ (T - j * h)) -
          ∫ x, χ x * stepDual D κ (Ξ j) (W (T - j * h)) 0 x ∂(ρ (T - j * h))| +
          |∫ x, χ x * stepDual D κ (Ξ j) (W (T - j * h)) 0 x ∂(ρ (T - j * h)) -
          ∫ x, χ x * Ξ (j + 1) x ∂(ρ (T - (j + 1) * h))| := abs_sub_le _ _ _
      _ ≤ E := by rw [hE]; linarith
  -- telescoping
  have htel : ∀ j ≤ N, |∫ x, χ x * φ x ∂(ρ T) -
      ∫ x, χ x * Ξ j x ∂(ρ (T - j * h))| ≤ j * E := by
    intro j
    induction j with
    | zero => intro _; simp [hΞ, lipDual]
    | succ j ih =>
      intro hj
      have := ih (Nat.le_of_succ_le hj)
      have hs := hstep j (Nat.lt_of_succ_le hj)
      push_cast
      calc _ ≤ |∫ x, χ x * φ x ∂(ρ T) - ∫ x, χ x * Ξ j x ∂(ρ (T - j * h))| +
            |∫ x, χ x * Ξ j x ∂(ρ (T - j * h)) -
              ∫ x, χ x * Ξ (j + 1) x ∂(ρ (T - (j + 1) * h))| := abs_sub_le _ _ _
        _ ≤ j * E + E := add_le_add this hs
        _ = (j + 1) * E := by ring
  have hfin := htel N le_rfl
  rw [hN, sub_self] at hfin
  exact hfin

/-! ### Uniqueness from smooth approximability -/

/-- Elementary bound: `G₀ (1 + h L)^N ≤ G₀ e^{L T}` when `N h = T` and `G₀, h, L ≥ 0`. -/
theorem pow_growth_le {G₀ h L T : ℝ} (hG₀ : 0 ≤ G₀) (hh : 0 ≤ h) (hL : 0 ≤ L) {N : ℕ}
    (hNh : (N : ℝ) * h = T) : G₀ * (1 + h * L) ^ N ≤ G₀ * Real.exp (L * T) := by
  refine mul_le_mul_of_nonneg_left ?_ hG₀
  calc (1 + h * L) ^ N ≤ Real.exp (h * L) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (h * L)]) N
    _ = Real.exp (L * T) := by rw [← Real.exp_nat_mul, ← hNh]; ring_nf

/-- Elementary bound on the cutoff terms of `abs_integral_sub_lipDual_le` for the scaled
cutoffs of `exists_scaled_cutoff` (`g₁ = A₁ / R`, `g₂ = A₂ / R²`, `R ≥ 1`) and
`B₁ = K (1 + ρ₁ R)`. The right side does not depend on `R`. -/
theorem cutoff_terms_le {C₀ d K ρ₁ R A₁ A₂ D G' Gs h L : ℝ} (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d)
    (hK : 0 ≤ K) (hρ₁ : 0 ≤ ρ₁) (hR : 1 ≤ R) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hD : 0 ≤ D)
    (hG'0 : 0 ≤ G') (hG' : G' ≤ Gs) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hL : 0 ≤ L) :
    C₀ * (d * (K * (1 + ρ₁ * R)) * (A₁ / R)) + 2 * D * (d * (A₁ / R) * (G' * (1 + h * L))) +
        D * C₀ * (A₂ / R ^ 2) ≤
      C₀ * (d * (K * (1 + ρ₁)) * A₁) + 2 * D * (d * A₁ * (Gs * (1 + L))) + D * C₀ * A₂ := by
  have hR0 : 0 < R := one_pos.trans_le hR
  have hb1 : K * (1 + ρ₁ * R) * (A₁ / R) ≤ K * (1 + ρ₁) * A₁ := by
    rw [show K * (1 + ρ₁ * R) * (A₁ / R) = K * A₁ * (1 / R + ρ₁) by field_simp]
    have : 1 / R ≤ 1 := (div_le_one hR0).2 hR
    have hKA : 0 ≤ K * A₁ := mul_nonneg hK hA₁
    calc K * A₁ * (1 / R + ρ₁) ≤ K * A₁ * (1 + ρ₁) :=
          mul_le_mul_of_nonneg_left (by linarith) hKA
      _ = K * (1 + ρ₁) * A₁ := by ring
  have hb2 : A₁ / R ≤ A₁ := div_le_self hA₁ hR
  have hb3 : A₂ / R ^ 2 ≤ A₂ := div_le_self hA₂ (one_le_pow₀ hR)
  have hGs0 : 0 ≤ Gs := hG'0.trans hG'
  have hhL : h * L ≤ L := by nlinarith
  have hb4 : G' * (1 + h * L) ≤ Gs * (1 + L) :=
    mul_le_mul hG' (by linarith) (by positivity) hGs0
  have e1 : C₀ * (d * (K * (1 + ρ₁ * R)) * (A₁ / R)) =
      C₀ * d * (K * (1 + ρ₁ * R) * (A₁ / R)) := by ring
  have e2 : C₀ * (d * (K * (1 + ρ₁)) * A₁) = C₀ * d * (K * (1 + ρ₁) * A₁) := by ring
  rw [e1, e2]
  have hCd : 0 ≤ C₀ * d := mul_nonneg hC₀ hd
  have t1 := mul_le_mul_of_nonneg_left hb1 hCd
  have t2 : 2 * D * (d * (A₁ / R) * (G' * (1 + h * L))) ≤
      2 * D * (d * A₁ * (Gs * (1 + L))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hb2 hd) hb4
      (by positivity) (by positivity)) (by positivity)
  have t3 : D * C₀ * (A₂ / R ^ 2) ≤ D * C₀ * A₂ :=
    mul_le_mul_of_nonneg_left hb3 (mul_nonneg hD hC₀)
  linarith

/-- Elementary bound on the total error of `abs_integral_sub_lipDual_le` for the parameter
choices of `integral_eq_of_weakFokkerPlanck_of_approx`: with `N h = T`,
`κ ≤ min h ((ε / (8 (N Gs d + 1)))² / (2D))`, `e = ε / (24 (T + 1)(Gs + 1))`,
`h ≤ (e / (L d + 1))² / (4D)`, `h ≤ e / (L B₁ + 1)`, `G' ≤ Gs`, `X ≤ Bb` and
`θ = ε / (4 (T Bb + 1))`, the error is at most `ε / 2`. -/
theorem lip_error_arith {ε T D L d Gs G' e h κ N B₁ θ X Bb : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (hD : 0 < D) (hL : 0 ≤ L) (hd : 0 ≤ d) (hG'0 : 0 ≤ G') (hG' : G' ≤ Gs) (hN : 0 ≤ N)
    (hh : 0 < h) (hNh : N * h = T) (hκh : κ ≤ h)
    (hκ : κ ≤ (ε / (8 * (N * Gs * d + 1))) ^ 2 / (2 * D))
    (he : e = ε / (24 * (T + 1) * (Gs + 1))) (hhS : h ≤ (e / (L * d + 1)) ^ 2 / (4 * D))
    (hB₁ : 0 ≤ B₁) (hhB : h ≤ e / (L * B₁ + 1)) (hBb : 0 ≤ Bb)
    (hθ : θ = ε / (4 * (T * Bb + 1))) (hX : X ≤ Bb) :
    N * (G' * Real.sqrt (2 * D * κ) * d +
      h * (G' * (e + L * stepSigma D κ h * d + h * L * B₁) + θ * X)) ≤ ε / 2 := by
  have hGs0 : 0 ≤ Gs := hG'0.trans hG'
  have he0 : 0 < e := by rw [he]; positivity
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  -- smoothing defect
  have hk1 : N * (G' * Real.sqrt (2 * D * κ) * d) ≤ ε / 8 := by
    have hsq : Real.sqrt (2 * D * κ) ≤ ε / (8 * (N * Gs * d + 1)) := by
      rw [Real.sqrt_le_left (by positivity)]
      calc 2 * D * κ ≤ 2 * D * ((ε / (8 * (N * Gs * d + 1))) ^ 2 / (2 * D)) :=
            mul_le_mul_of_nonneg_left hκ (by positivity)
        _ = _ := by field_simp
    have hNG : N * G' ≤ N * Gs := mul_le_mul_of_nonneg_left hG' hN
    calc N * (G' * Real.sqrt (2 * D * κ) * d) = (N * G' * d) * Real.sqrt (2 * D * κ) := by
          ring
      _ ≤ (N * Gs * d) * (ε / (8 * (N * Gs * d + 1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hNG hd) hsq (Real.sqrt_nonneg _)
            (by positivity)
      _ = ε / 8 * (N * Gs * d / (N * Gs * d + 1)) := by field_simp
      _ ≤ ε / 8 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (by linarith))
  -- transport defect
  have hS : L * stepSigma D κ h * d ≤ e := by
    have hSh : stepSigma D κ h ≤ e / (L * d + 1) := by
      rw [stepSigma, Real.sqrt_le_left (by positivity)]
      calc 2 * D * (h + κ) ≤ 2 * D * (2 * h) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * D * h := by ring
        _ ≤ 4 * D * ((e / (L * d + 1)) ^ 2 / (4 * D)) :=
            mul_le_mul_of_nonneg_left hhS (by positivity)
        _ = (e / (L * d + 1)) ^ 2 := by field_simp
    calc L * stepSigma D κ h * d = (L * d) * stepSigma D κ h := by ring
      _ ≤ (L * d) * (e / (L * d + 1)) := mul_le_mul_of_nonneg_left hSh (by positivity)
      _ = e * (L * d / (L * d + 1)) := by field_simp
      _ ≤ e := mul_le_of_le_one_right he0.le ((div_le_one (by positivity)).2 (by linarith))
  have hBh : h * L * B₁ ≤ e := by
    calc h * L * B₁ = h * (L * B₁) := by ring
      _ ≤ e / (L * B₁ + 1) * (L * B₁) := mul_le_mul_of_nonneg_right hhB (by positivity)
      _ = e * (L * B₁ / (L * B₁ + 1)) := by field_simp
      _ ≤ e := mul_le_of_le_one_right he0.le ((div_le_one (by positivity)).2 (by linarith))
  have hk2 : T * (G' * (e + L * stepSigma D κ h * d + h * L * B₁)) ≤ ε / 8 := by
    have h3 : e + L * stepSigma D κ h * d + h * L * B₁ ≤ 3 * e := by linarith
    have hS0 : 0 ≤ e + L * stepSigma D κ h * d + h * L * B₁ := by
      have : 0 ≤ stepSigma D κ h := Real.sqrt_nonneg _
      positivity
    calc T * (G' * (e + L * stepSigma D κ h * d + h * L * B₁)) ≤ T * (Gs * (3 * e)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hG' h3 hS0 hGs0) hT
      _ = ε / 8 * (T / (T + 1)) * (Gs / (Gs + 1)) := by rw [he]; field_simp; ring
      _ ≤ ε / 8 * 1 * 1 := by
          have a1 : T / (T + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
          have a2 : Gs / (Gs + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
          have a3 : 0 ≤ T / (T + 1) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left a1 (by positivity)) a2
            (by positivity) (by positivity)
      _ = ε / 8 := by ring
  -- cutoff defect
  have hθB : T * θ * Bb ≤ ε / 4 := by
    rw [hθ, show T * (ε / (4 * (T * Bb + 1))) * Bb = ε / 4 * (T * Bb / (T * Bb + 1)) by
      field_simp]
    exact mul_le_of_le_one_right (by positivity)
      ((div_le_one (by positivity)).2 (by linarith))
  have hk3 : T * (θ * X) ≤ ε / 4 := by
    calc T * (θ * X) ≤ T * (θ * Bb) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hθ0) hT
      _ = T * θ * Bb := by ring
      _ ≤ ε / 4 := hθB
  have hsplit : N * (G' * Real.sqrt (2 * D * κ) * d +
      h * (G' * (e + L * stepSigma D κ h * d + h * L * B₁) + θ * X)) =
      N * (G' * Real.sqrt (2 * D * κ) * d) +
        (N * h) * (G' * (e + L * stepSigma D κ h * d + h * L * B₁)) + (N * h) * (θ * X) := by
    ring
  rw [hsplit, hNh]
  linarith

/-- **Uniqueness on test functions at a fixed time (Verified).** Let `D > 0`, `T ≥ 0`, `b` jointly
continuous with `‖b_s(x)‖ ≤ K (1 + ‖x‖)` for `s ∈ [0, T]`, and suppose every `b_t`, `t ∈ [0, T]`,
is uniformly approximable by `C²` fields `w` with `‖Dw‖ ≤ L` (one `L` for all `t`) and bounded
`D²w`. If `ρ, ρ'` are curves of probability measures on `t ≥ 0` solving
`WeakFokkerPlanck · b D` with `ρ 0 = ρ' 0`, then `∫ φ dρ_T = ∫ φ dρ'_T` for every smooth
compactly supported `φ`. No moment or tightness assumption on `ρ, ρ'`. -/
theorem integral_eq_of_weakFokkerPlanck_of_approx {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} (hD : 0 < D)
    (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2) {T : ℝ} (hT : 0 ≤ T) {K L : ℝ}
    (hK : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ K * (1 + ‖x‖))
    (happ : ∀ t ∈ Icc 0 T, ∀ η > 0, ∃ w : (Fin d → ℝ) → Fin d → ℝ, ContDiff ℝ 2 w ∧
      (∀ y, ‖fderiv ℝ w y‖ ≤ L) ∧ (∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) ∧
      ∀ y, ‖w y - b t y‖ ≤ η)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D) (h0 : ρ 0 = ρ' 0)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x ∂(ρ T) = ∫ x, φ x ∂(ρ' T) := by
  rcases hT.eq_or_lt with rfl | hT0
  · rw [h0]
  have hbs : ∀ s, 0 ≤ s → Continuous (b s) := fun s _ =>
    hbc.comp (continuous_const.prodMk continuous_id)
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩ 0); simpa using this
  have hL0 : 0 ≤ L := by
    obtain ⟨w, -, hw, -⟩ := happ 0 ⟨le_rfl, hT⟩ 1 one_pos
    exact (norm_nonneg _).trans (hw 0)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hφb : BddC2 φ := BddC2.of_testFunction hφ2 hφc
  obtain ⟨C₀, hC₀⟩ := hφb.2.1
  obtain ⟨G₀, hG₀⟩ := hφb.2.2.1
  have hC₀' : ∀ y, |φ y| ≤ C₀ := fun y => by rw [← Real.norm_eq_abs]; exact hC₀ y
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0)
  have hG₀0 : 0 ≤ G₀ := (norm_nonneg _).trans (hG₀ 0)
  obtain ⟨ρ₁, A₁, A₂, hρ₁, hA₁, hA₂, hcut⟩ := exists_scaled_cutoff (d := d)
  set Gs : ℝ := G₀ * Real.exp (L * T) with hGs
  have hGs0 : 0 ≤ Gs := by positivity
  set Bb : ℝ := C₀ * (d * (K * (1 + ρ₁)) * A₁) + 2 * D * (d * A₁ * (Gs * (1 + L))) + D * C₀ * A₂
    with hBb
  have hBb0 : 0 ≤ Bb := by positivity
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [Real.dist_eq]
  -- choice of the cutoff radius
  set θ : ℝ := ε / (4 * (T * Bb + 1)) with hθdef
  have hθ0 : 0 < θ := by positivity
  obtain ⟨R₁, hR₁⟩ := exists_tail_le hprob hρ T hθ0
  obtain ⟨R₂, hR₂⟩ := exists_tail_le hprob' hρ' T hθ0
  obtain ⟨Rφ, hRφ⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  set R : ℝ := max (max R₁ R₂) (max Rφ 1) with hRdef
  have hR1 : 1 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hR0 : 0 < R := one_pos.trans_le hR1
  obtain ⟨χ, hχ, hχc, hχI, hχ1, hχs, hχg, hχl, hχ0⟩ := hcut R hR1
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
  have hχabs : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hχI x).1], (hχI x).2⟩
  have hχφ : ∀ x, χ x * φ x = φ x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hxR : ‖x‖ ≤ R := by
        have := hRφ hx
        rw [mem_closedBall, dist_zero_right] at this
        exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
      rw [hχ1 x hxR, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  set Tl : Set (Fin d → ℝ) := {x | R ≤ ‖x‖} with hTl
  have hTlm : MeasurableSet Tl := measurableSet_le measurable_const measurable_norm
  have hTχ : ∀ x ∉ Tl, grad χ x = 0 ∧ laplacian χ x = 0 := fun x hx =>
    hχ0 x (not_le.1 hx)
  have hθρ : ∀ s ∈ Icc 0 T, (ρ s).real Tl ≤ θ := fun s hs =>
    hR₁ R ((le_max_left _ _).trans (le_max_left _ _)) s hs
  have hθρ' : ∀ s ∈ Icc 0 T, (ρ' s).real Tl ≤ θ := fun s hs =>
    hR₂ R ((le_max_right _ _).trans (le_max_left _ _)) s hs
  set B₁ : ℝ := K * (1 + ρ₁ * R) with hB₁def
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₁ : ∀ s ∈ Icc 0 T, ∀ x ∈ tsupport χ, ‖b s x‖ ≤ B₁ := by
    intro s hs x hx
    have hx' := hχs hx
    rw [mem_closedBall, dist_zero_right] at hx'
    exact (hK s hs x).trans (mul_le_mul_of_nonneg_left (by linarith) hK0)
  -- accuracy for the drift approximation
  set e : ℝ := ε / (24 * (T + 1) * (Gs + 1)) with hedef
  have he0 : 0 < e := by positivity
  have hcomp : IsCompact (Icc 0 T ×ˢ closedBall (0 : Fin d → ℝ) (ρ₁ * R)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ₁, hδ₁, hδ₁u⟩ := Metric.uniformContinuousOn_iff.1
    (hcomp.uniformContinuousOn_of_continuous hbc.continuousOn) (e / 2) (by positivity)
  set δh : ℝ := min (min (δ₁ / 2) 1) (min ((e / (L * d + 1)) ^ 2 / (4 * D)) (e / (L * B₁ + 1)))
    with hδhdef
  have hδh0 : 0 < δh := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δh)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  set h : ℝ := T / N with hhdef
  have hh0 : 0 < h := by positivity
  have hNh : (N : ℝ) * h = T := by rw [hhdef]; field_simp
  have hhδ : h ≤ δh := by
    rw [hhdef, div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hδh0] at hN
    linarith
  have hh1 : h ≤ 1 := hhδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhδ₁ : h < δ₁ := lt_of_le_of_lt (hhδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (by linarith)
  have hhS : h ≤ (e / (L * d + 1)) ^ 2 / (4 * D) :=
    hhδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhB : h ≤ e / (L * B₁ + 1) := hhδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  set κ : ℝ := min h ((ε / (8 * (N * Gs * d + 1))) ^ 2 / (2 * D)) with hκdef
  have hκ0 : 0 < κ := by positivity
  -- the smooth fields
  set η : ℝ := e / 2 with hηdef
  have hη0 : 0 < η := by positivity
  set W : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun t =>
    if ht : t ∈ Icc 0 T then Classical.choose (happ t ht η hη0) else 0 with hWdef
  have hW : ∀ t, ContDiff ℝ 2 (W t) ∧ (∀ y, ‖fderiv ℝ (W t) y‖ ≤ L) ∧
      ∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ (W t)) y‖ ≤ M := by
    intro t
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨h1, h2, h3, -⟩ := Classical.choose_spec (happ t ht η hη0)
      simp only [hWdef, ht, ↓reduceDIte]
      exact ⟨h1, h2, h3⟩
    · simp only [hWdef, ht, ↓reduceDIte]
      refine ⟨contDiff_const, fun y => ?_, ⟨0, fun y => ?_⟩⟩
      · simp [hL0]
      · simp only [fderiv_zero, Pi.zero_apply]
        exact le_of_eq ContinuousLinearMap.opNorm_zero
  have hWb : ∀ t ∈ Icc 0 T, ∀ y, ‖W t y - b t y‖ ≤ η := by
    intro t ht y
    obtain ⟨-, -, -, h4⟩ := Classical.choose_spec (happ t ht η hη0)
    simp only [hWdef, ht, ↓reduceDIte]
    exact h4 y
  have hε₁ : ∀ j < N, ∀ s ∈ Icc (T - (j + 1) * h) (T - j * h), ∀ x ∈ tsupport χ,
      ‖b s x - W (T - j * h) x‖ ≤ e := by
    intro j hj s hs x hx
    have hjN : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hj
    have hm1 : ((j : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hjN hh0.le
    have hm2 : 0 ≤ (j : ℝ) * h := by positivity
    have hc : T - j * h ∈ Icc 0 T := ⟨by linarith, by linarith⟩
    have hs0 : s ∈ Icc 0 T := ⟨by linarith [hs.1], hs.2.trans hc.2⟩
    have hx' := hχs hx
    have hsc : |s - (T - j * h)| ≤ h := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hdist : dist (s, x) (T - j * h, x) < δ₁ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
      exact hsc.trans_lt hhδ₁
    have h1 := hδ₁u (s, x) ⟨hs0, hx'⟩ (T - j * h, x) ⟨hc, hx'⟩ hdist
    rw [dist_eq_norm] at h1
    have h2 := hWb _ hc x
    calc ‖b s x - W (T - j * h) x‖
        ≤ ‖b s x - b (T - j * h) x‖ + ‖W (T - j * h) x - b (T - j * h) x‖ := by
          rw [← norm_neg (W (T - j * h) x - b (T - j * h) x)]
          refine (norm_add_le _ _).trans_eq' ?_
          congr 1; abel
      _ ≤ e := by linarith
  -- the estimate for each solution
  have hest := fun (μ : ℝ → Measure (Fin d → ℝ)) (hμ : ∀ t, 0 ≤ t → IsProbabilityMeasure (μ t))
      (hfp : WeakFokkerPlanck μ b D) (hθμ : ∀ s ∈ Icc 0 T, (μ s).real Tl ≤ θ) =>
    abs_integral_sub_lipDual_le hD hκ0 hμ hfp hbs hh0 hNh hW hφb hC₀' hG₀ hχ2 hχc hχabs hχg hχl
      hTlm hTχ hθμ he0.le hB₁0 hε₁ hB₁
  have h1 := hest ρ hprob hρ hθρ
  have h2 := hest ρ' hprob' hρ' hθρ'
  simp only [hχφ] at h1 h2
  rw [h0] at h1
  -- bounding the error terms
  have hG' := pow_growth_le hG₀0 hh0.le hL0 hNh
  have hX := cutoff_terms_le (h := h) (L := L) (G' := G₀ * (1 + h * L) ^ N) hC₀0
    (Nat.cast_nonneg d) hK0 (by linarith : (0 : ℝ) ≤ ρ₁) hR1 hA₁ hA₂ hD.le (by positivity) hG'
    hh0.le hh1 hL0
  have hQ := lip_error_arith hε hT hD hL0 (Nat.cast_nonneg d) (by positivity) hG'
    hNpos.le hh0 hNh (min_le_left _ _) (min_le_right _ _) hedef hhS hB₁0 hhB hBb0
    hθdef hX
  have h1' := h1.trans hQ
  have h2' := h2.trans hQ
  calc |∫ x, φ x ∂(ρ T) - ∫ x, φ x ∂(ρ' T)|
      ≤ |∫ x, φ x ∂(ρ T) - ∫ x, χ x * lipDual D κ h T W φ N x ∂(ρ' 0)| +
        |∫ x, φ x ∂(ρ' T) - ∫ x, χ x * lipDual D κ h T W φ N x ∂(ρ' 0)| := by
        rw [abs_sub_comm (∫ x, φ x ∂(ρ' T))]; exact abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-! ### Smooth approximants of Lipschitz fields with bounded second derivative -/

/-- **Smooth approximation with bounded second derivative (Verified).** If `f : ℝᵈ → ℝᵈ`
satisfies `‖f x - f y‖ ≤ L ‖x - y‖` (`L ≥ 0`) and `r > 0`, there is a `C^∞` map `g` with
`‖Dg(x)‖ ≤ L`, `‖D²g(x)‖ ≤ M` for some `M` (namely `M = L ∫ ‖Dκ‖`), and `‖g(x) - f(x)‖ ≤ L r`.
Construction as in `NoiseScore.exists_contDiff_lipschitz_approx`: `g = κ ⋆ f` with `κ` the
normalized `ContDiffBump` of outer radius `r`; `Dg = Dκ ⋆ f` is `L ∫ ‖Dκ‖`-Lipschitz. -/
theorem exists_contDiff_lipschitz_approx_two {f : (Fin d → ℝ) → Fin d → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) {r : ℝ} (hr : 0 < r) :
    ∃ g : (Fin d → ℝ) → Fin d → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L) ∧
      (∃ M, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) ∧ ∀ x, ‖g x - f x‖ ≤ L * r := by
  have hfc : Continuous f := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun y => hf y x) ?_
    have : Tendsto (fun y => L * ‖y - x‖) (𝓝 x) (𝓝 (L * ‖x - x‖)) :=
      ((continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x)
    simpa using this
  set φ : ContDiffBump (0 : Fin d → ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set κ := φ.normed (volume : Measure (Fin d → ℝ))
  set g : (Fin d → ℝ) → Fin d → ℝ := κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hgd : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (hfc.locallyIntegrable)
  have hint : ∀ x, Integrable (fun t => κ t • f (x - t)) volume := fun x =>
    (φ.continuous_normed.smul (hfc.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport φ.hasCompactSupport_normed.smul_right
  have hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ := by
    intro x y
    have e : g x - g y = ∫ t, κ t • (f (x - t) - f (y - t)) := by
      simp only [g, convolution_lsmul, smul_sub]
      rw [integral_sub (hint x) (hint y)]
    rw [e]
    calc ‖∫ t, κ t • (f (x - t) - f (y - t))‖ ≤ ∫ t, κ t * (L * ‖x - y‖) := by
          refine norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
          refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
          simpa using hf (x - t) (y - t)
      _ = L * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]
  -- the second derivative
  set B := (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] (Fin d → ℝ) →L[ℝ] Fin d → ℝ).precompL (Fin d → ℝ)
  have hκ1 : ContDiff ℝ 1 κ := φ.contDiff_normed
  have hD : ∀ x, fderiv ℝ g x = (fderiv ℝ κ ⋆[B, volume] f) x := fun x =>
    (φ.hasCompactSupport_normed.hasFDerivAt_convolution_left _ hκ1 hfc.locallyIntegrable
      x).fderiv
  have hκ'c : Continuous (fderiv ℝ κ) := hκ1.continuous_fderiv one_ne_zero
  have hκ's : HasCompactSupport (fderiv ℝ κ) := φ.hasCompactSupport_normed.fderiv (𝕜 := ℝ)
  set C := ∫ t, ‖fderiv ℝ κ t‖
  have hBn : ∀ (a : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ), ‖B a v‖ ≤ ‖a‖ * ‖v‖ := by
    intro a v
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    have : B a v u = a u • v := rfl
    rw [this, norm_smul]
    calc ‖a u‖ * ‖v‖ ≤ ‖a‖ * ‖u‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (a.le_opNorm u) (norm_nonneg _)
      _ = ‖a‖ * ‖v‖ * ‖u‖ := by ring
  have hint' : ∀ x, Integrable (fun t => B (fderiv ℝ κ t) (f (x - t))) volume := fun x =>
    (B.continuous₂.comp₂ hκ'c (hfc.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport (by
        refine hκ's.mono ?_
        intro t ht; simp only [Function.mem_support] at ht ⊢
        intro h0; apply ht; simp [h0])
  have hlip' : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ (C * L) * ‖x - y‖ := by
    intro x y
    rw [hD, hD, convolution_def, convolution_def, ← integral_sub (hint' x) (hint' y)]
    calc ‖∫ t, (B (fderiv ℝ κ t) (f (x - t)) - B (fderiv ℝ κ t) (f (y - t)))‖
        ≤ ∫ t, ‖fderiv ℝ κ t‖ * (L * ‖x - y‖) := by
          refine norm_integral_le_of_norm_le
            ((hκ'c.norm.integrable_of_hasCompactSupport hκ's.norm).mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [← map_sub]
          refine (hBn _ _).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          simpa using hf (x - t) (y - t)
      _ = (C * L) * ‖x - y‖ := by rw [integral_mul_const]; ring
  have hCL : 0 ≤ C * L := mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hL
  refine ⟨g, hgd, fun x => norm_fderiv_le_of_lip' ℝ hL
    (Eventually.of_forall fun y => hlip y x),
    ⟨C * L, fun x => norm_fderiv_le_of_lip' ℝ hCL (Eventually.of_forall fun y => hlip' y x)⟩,
    fun x => ?_⟩
  rw [← dist_eq_norm]
  refine φ.dist_normed_convolution_le hfc.aestronglyMeasurable fun z hz => ?_
  rw [dist_eq_norm]
  refine (hf z x).trans (mul_le_mul_of_nonneg_left ?_ hL)
  rw [← dist_eq_norm]; exact (mem_ball.1 hz).le

/-! ### Uniqueness for globally Lipschitz drifts -/

/-- **Uniqueness for the weak Fokker–Planck equation with Lipschitz drift (Verified).** Let
`D > 0` and let `b : ℝ → ℝᵈ → ℝᵈ` be jointly continuous in `(t, x)` and, on every `[0, T]`,
Lipschitz in `x` with a constant uniform in `t ∈ [0, T]` (so `b` has linear growth and is in
general unbounded, e.g. `b_t(x) = -A(t) x + c(t)`). If `ρ, ρ'` are curves of probability
measures on `t ≥ 0` solving `WeakFokkerPlanck · b D` with `ρ 0 = ρ' 0`, then `ρ t = ρ' t` for
all `t ≥ 0`. No moment, density or tightness assumption on `ρ, ρ'`. -/
theorem eq_of_weakFokkerPlanck_lipschitz {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D : ℝ} (hD : 0 < D)
    (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (hL : ∀ T, ∃ L : NNReal, ∀ t ∈ Icc 0 T, LipschitzWith L (b t))
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ b D) (hρ' : WeakFokkerPlanck ρ' b D) (h0 : ρ 0 = ρ' 0) :
    ∀ t, 0 ≤ t → ρ t = ρ' t := by
  intro T hT
  obtain ⟨L, hLT⟩ := hL T
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun s => b s 0)
    (s := Icc 0 T) (hbc.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hK : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ ((L : ℝ) + M) * (1 + ‖x‖) := by
    intro s hs x
    have h1 := norm_le_of_lipschitzWith (hLT s hs) x
    have h2 : ((L : ℝ) + ‖b s 0‖) ≤ L + M := by linarith [hM s hs]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  have happ : ∀ t ∈ Icc 0 T, ∀ η > 0, ∃ w : (Fin d → ℝ) → Fin d → ℝ, ContDiff ℝ 2 w ∧
      (∀ y, ‖fderiv ℝ w y‖ ≤ L) ∧ (∃ M, ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) ∧
      ∀ y, ‖w y - b t y‖ ≤ η := by
    intro t ht η hη
    obtain ⟨g, hg, hg1, hg2, hg3⟩ := exists_contDiff_lipschitz_approx_two (L := (L : ℝ))
      L.2 (fun x y => (hLT t ht).norm_sub_le x y) (r := η / (L + 1)) (by positivity)
    refine ⟨g, hg.of_le (by norm_cast), hg1, hg2, fun y => (hg3 y).trans ?_⟩
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := hprob T hT
  have := hprob' T hT
  exact ext_of_forall_integral_smooth_eq fun φ hφ hφc =>
    integral_eq_of_weakFokkerPlanck_of_approx hD hbc hT hK happ hprob hprob' hρ hρ' h0 hφ hφc

/-- **Uniqueness, autonomous Lipschitz drift (Verified).** For `b : ℝᵈ → ℝᵈ` `L`-Lipschitz
(unbounded in general) and `D > 0`, two probability solutions of
`WeakFokkerPlanck · (fun _ => b) D` on `t ≥ 0` with the same initial law agree for all
`t ≥ 0`. -/
theorem eq_of_weakFokkerPlanck_lipschitzWith {ρ ρ' : ℝ → Measure (Fin d → ℝ)}
    {b : (Fin d → ℝ) → Fin d → ℝ} {L : NNReal} (hL : LipschitzWith L b) {D : ℝ} (hD : 0 < D)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hprob' : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t))
    (hρ : WeakFokkerPlanck ρ (fun _ => b) D) (hρ' : WeakFokkerPlanck ρ' (fun _ => b) D)
    (h0 : ρ 0 = ρ' 0) : ∀ t, 0 ≤ t → ρ t = ρ' t :=
  eq_of_weakFokkerPlanck_lipschitz hD (hL.continuous.comp continuous_snd)
    (fun _ => ⟨L, fun _ _ => hL⟩) hprob hprob' hρ hρ' h0

/-! ### Well-posedness and Euler–Maruyama identification -/

/-- **Well-posedness, autonomous Lipschitz drift (Verified, no Itô input).** For an
`L`-Lipschitz drift `b : ℝᵈ → ℝᵈ` (no boundedness), `D > 0` and any probability measure `ρ₀`
(no moment assumption), there is a curve of probability measures `ρ` with `ρ 0 = ρ₀` solving
`WeakFokkerPlanck ρ (fun _ => b) D`, it is the weak limit at every time of the dyadic
Euler–Maruyama laws `emCurveP b _ D ρ₀ n t`, and every probability solution on `t ≥ 0` with
initial law `ρ₀` coincides with it on `t ≥ 0`. -/
theorem existsUnique_weakFokkerPlanck_lipschitz {b : (Fin d → ℝ) → Fin d → ℝ} {L : NNReal}
    (hL : LipschitzWith L b) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => b) D ∧
      (∀ t (h : IsProbabilityMeasure (ρ t)),
        Tendsto (fun n => emCurveP b hL.continuous.measurable D ρ₀ n t) atTop
          (𝓝 ⟨ρ t, h⟩)) ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) → WeakFokkerPlanck ρ' (fun _ => b) D →
          ∀ t, 0 ≤ t → ρ' t = ρ t := by
  obtain ⟨ν, h0, -, hfp, hν⟩ := exists_weakFokkerPlanck_lipschitz hL hD ρ₀
  refine ⟨fun t => ν t, h0, fun t => inferInstance, hfp, fun t _ => hν t,
    fun ρ' h0' hprob' hfp' => ?_⟩
  exact eq_of_weakFokkerPlanck_lipschitzWith hL hD hprob' (fun t _ => inferInstance) hfp' hfp
    (h0'.trans h0.symm)

/-- **Well-posedness, time-dependent Lipschitz drift (Verified, no Itô input).** Let
`b : ℝ → ℝᵈ → ℝᵈ` be jointly continuous and Lipschitz in `x` uniformly on every `[0, T]`. For
`D > 0` and any probability measure `ρ₀` there is a probability solution of
`WeakFokkerPlanck ρ b D` with `ρ 0 = ρ₀` (`exists_weakFokkerPlanck_continuousTime`), and every
probability solution on `t ≥ 0` with the same initial law coincides with it on `t ≥ 0`. -/
theorem existsUnique_weakFokkerPlanck_lipschitz_continuousTime
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} (hbc : Continuous fun p : ℝ × (Fin d → ℝ) => b p.1 p.2)
    (hL : ∀ T, ∃ L : NNReal, ∀ t ∈ Icc 0 T, LipschitzWith L (b t)) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ b D ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) → WeakFokkerPlanck ρ' b D →
          ∀ t, 0 ≤ t → ρ' t = ρ t := by
  obtain ⟨ν, h0, -, hfp⟩ := exists_weakFokkerPlanck_continuousTime hbc hL hD ρ₀
  refine ⟨fun t => ν t, h0, fun t => inferInstance, hfp, fun ρ' h0' hprob' hfp' => ?_⟩
  exact eq_of_weakFokkerPlanck_lipschitz hD hbc hL hprob' (fun t _ => inferInstance) hfp' hfp
    (h0'.trans h0.symm)

/-- **Well-posedness for overdamped Langevin with Lipschitz gradient (Verified).** Let `U` have
an `L`-Lipschitz gradient (e.g. `U` quadratic plus a `C²` function with bounded Hessian; no
convexity). For `D > 0` and any probability measure `ρ₀`, the weak Fokker–Planck equation of
`dX = -∇U(X) dt + √(2D) dW` has exactly one probability solution on `t ≥ 0` with initial law
`ρ₀`, the weak limit at every time of the dyadic Euler–Maruyama laws (unadjusted Langevin
algorithm with step `2⁻ⁿ`). -/
theorem existsUnique_weakFokkerPlanck_langevin_lipschitz {U : (Fin d → ℝ) → ℝ} {L : NNReal}
    (hU : LipschitzWith L (grad U)) {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ x => -grad U x) D ∧
      (∀ t (h : IsProbabilityMeasure (ρ t)),
        Tendsto (fun n => emCurveP (fun x => -grad U x)
          (lipschitzWith_neg_grad hU).continuous.measurable D ρ₀ n t) atTop (𝓝 ⟨ρ t, h⟩)) ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) →
          WeakFokkerPlanck ρ' (fun _ x => -grad U x) D → ∀ t, 0 ≤ t → ρ' t = ρ t :=
  existsUnique_weakFokkerPlanck_lipschitz (lipschitzWith_neg_grad hU) hD ρ₀

/-- **Every solution is the Euler–Maruyama limit, Lipschitz drift (Verified).** For an
autonomous `L`-Lipschitz drift `b` (unbounded in general) and `D > 0`, let `ρ` be any curve of
probability measures on `t ≥ 0` solving `WeakFokkerPlanck ρ (fun _ => b) D` (no moment
assumption). Then for every `t ≥ 0` the dyadic Euler–Maruyama laws `emCurveP b _ D (ρ 0) n t`
(step `2⁻ⁿ`) converge weakly to `ρ t`. -/
theorem tendsto_emCurveP_of_weakFokkerPlanck_lipschitz {b : (Fin d → ℝ) → Fin d → ℝ}
    {L : NNReal} (hL : LipschitzWith L b) {D : ℝ} (hD : 0 < D) {ρ : ℝ → Measure (Fin d → ℝ)}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : WeakFokkerPlanck ρ (fun _ => b) D) {t : ℝ} (ht : 0 ≤ t) :
    letI := hprob 0 le_rfl
    Tendsto (fun n => emCurveP b hL.continuous.measurable D (ρ 0) n t) atTop
      (𝓝 ⟨ρ t, hprob t ht⟩) := by
  have := hprob 0 le_rfl
  obtain ⟨ν, h0, -, hfp, hν⟩ := exists_weakFokkerPlanck_lipschitz hL hD (ρ 0)
  have heq := eq_of_weakFokkerPlanck_lipschitzWith hL hD
    (fun t _ => (inferInstance : IsProbabilityMeasure (ν t : Measure (Fin d → ℝ)))) hprob hfp
    hρ h0 t ht
  have e : ν t = ⟨ρ t, hprob t ht⟩ := Subtype.ext heq
  rw [← e]
  exact hν t

/-! ### Special cases: bounded, Ornstein–Uhlenbeck and linear-plus-bounded drifts -/

/-- **Well-posedness, Lipschitz bounded drift (Verified, no Itô input).** For
`b : ℝᵈ → ℝᵈ` Lipschitz and bounded, `D > 0` and any probability measure `ρ₀` on `Fin d → ℝ`,
there is a curve of probability measures `ρ` with `ρ 0 = ρ₀` solving
`WeakFokkerPlanck ρ (fun _ => b) D`, and every probability solution `ρ'` on `t ≥ 0` with
`ρ' 0 = ρ₀` coincides with it on `t ≥ 0`. The bound on `b` is not needed: this is part of
`existsUnique_weakFokkerPlanck_lipschitz`. -/
theorem existsUnique_weakFokkerPlanck {b : (Fin d → ℝ) → Fin d → ℝ} {L : NNReal}
    (hL : LipschitzWith L b) {B : ℝ} (_hB : ∀ x, ‖b x‖ ≤ B) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => b) D ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) → WeakFokkerPlanck ρ' (fun _ => b) D →
          ∀ t, 0 ≤ t → ρ' t = ρ t := by
  obtain ⟨ρ, h0, hprob, hfp, -, huniq⟩ := existsUnique_weakFokkerPlanck_lipschitz hL hD ρ₀
  exact ⟨ρ, h0, hprob, hfp, huniq⟩

/-- **Every solution is the Euler–Maruyama limit, bounded Lipschitz drift (Verified).** For `b`
Lipschitz and bounded and `D > 0`, let `ρ` be any curve of probability measures on `t ≥ 0`
solving `WeakFokkerPlanck ρ (fun _ => b) D`. Then for every `t ≥ 0` the dyadic Euler–Maruyama
laws `emCurve b _ D (ρ 0) n t` (step `2⁻ⁿ`) converge weakly to `ρ t` as `n → ∞`. The bound on
`b` is not needed: this is `tendsto_emCurveP_of_weakFokkerPlanck_lipschitz`. -/
theorem tendsto_emCurveP_of_weakFokkerPlanck {b : (Fin d → ℝ) → Fin d → ℝ} {L : NNReal}
    (hL : LipschitzWith L b) {B : ℝ} (_hB : ∀ x, ‖b x‖ ≤ B) {D : ℝ} (hD : 0 < D)
    {ρ : ℝ → Measure (Fin d → ℝ)} (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t))
    (hρ : WeakFokkerPlanck ρ (fun _ => b) D) {t : ℝ} (ht : 0 ≤ t) :
    letI := hprob 0 le_rfl
    Tendsto (fun n => emCurveP b hL.continuous.measurable D (ρ 0) n t) atTop
      (𝓝 ⟨ρ t, hprob t ht⟩) :=
  tendsto_emCurveP_of_weakFokkerPlanck_lipschitz hL hD hprob hρ ht

/-- **Well-posedness for the Ornstein–Uhlenbeck equation (Verified).** For `a ≥ 0`, `D > 0`
and any probability measure `ρ₀` (no moment assumption), the weak Fokker–Planck equation of
`dX = -a X dt + √(2D) dW` has exactly one probability solution on `t ≥ 0` with initial law
`ρ₀`, and it is the weak limit at every time of the dyadic Euler–Maruyama laws: for every `t`,
`emCurveP (fun x => (-a) • x) _ D ρ₀ n t → ρ t` as `n → ∞` (step `2⁻ⁿ`, convergence in
`ProbabilityMeasure`, i.e. weak convergence). The sign condition `a ≥ 0` is not needed: this is
`existsUnique_weakFokkerPlanck_lipschitz` for the Lipschitz drift `x ↦ -a x`. -/
theorem existsUnique_weakFokkerPlanck_ou {a : ℝ} (_ha : 0 ≤ a) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ x => (-a) • x) D ∧
      (∀ t (h : IsProbabilityMeasure (ρ t)),
        Tendsto (fun n => emCurveP (fun x => (-a) • x)
          (lipschitzWith_smul (-a)).continuous.measurable D ρ₀ n t) atTop (𝓝 ⟨ρ t, h⟩)) ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) →
          WeakFokkerPlanck ρ' (fun _ x => (-a) • x) D → ∀ t, 0 ≤ t → ρ' t = ρ t :=
  existsUnique_weakFokkerPlanck_lipschitz (lipschitzWith_smul (-a)) hD ρ₀

/-- **Well-posedness for overdamped Langevin with a quadratic-plus-bounded-gradient potential
(Verified).** Let `U` have an `L`-Lipschitz gradient with `‖∇U(x) - a x‖ ≤ B`, `a ≥ 0` (e.g.
`U(x) = a |x|²/2 + U₀(x)` with `∇U₀` bounded and Lipschitz). For `D > 0` and any probability
measure `ρ₀`, the weak Fokker–Planck equation of `dX = -∇U(X) dt + √(2D) dW` has exactly one
probability solution on `t ≥ 0` with initial law `ρ₀`. Only the Lipschitz bound is needed: this
is part of `existsUnique_weakFokkerPlanck_langevin_lipschitz`. -/
theorem existsUnique_weakFokkerPlanck_langevin_linear_add_bounded
    {U : (Fin d → ℝ) → ℝ} {L : NNReal} (hU : LipschitzWith L (grad U)) {a B : ℝ}
    (_ha : 0 ≤ a) (_hB : ∀ x, ‖grad U x - a • x‖ ≤ B) {D : ℝ} (hD : 0 < D)
    (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ x => -grad U x) D ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) →
          WeakFokkerPlanck ρ' (fun _ x => -grad U x) D → ∀ t, 0 ≤ t → ρ' t = ρ t := by
  obtain ⟨ρ, h0, hprob, hfp, -, huniq⟩ :=
    existsUnique_weakFokkerPlanck_langevin_lipschitz hU hD ρ₀
  exact ⟨ρ, h0, hprob, hfp, huniq⟩

end FormalizeSampling.FokkerPlanckUniqueness
