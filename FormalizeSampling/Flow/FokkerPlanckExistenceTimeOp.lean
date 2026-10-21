module

public import Mathlib.MeasureTheory.Measure.Tight
public import FormalizeSampling.Flow.FokkerPlanckExistenceLyap
public import FormalizeSampling.Flow.FokkerPlanckExistenceCauchy
public import FormalizeSampling.Foundations.MeasureHelpers

/-!
# Time-dependent Euler–Maruyama chains with linearly growing drift: Cauchy property, tightness

Status: **Verified.** For a time-dependent drift `b : ℝ → ℝᵈ → ℝᵈ` with, for **all** `t, s`,

* `b t` is `L`-Lipschitz,
* linear growth `‖b t x‖ ≤ B (1 + ‖x‖)`,
* Hölder-`½` time regularity `‖b t x - b s x‖ ≤ K √|t - s| (1 + ‖x‖)`,

this file builds the time-dependent EM chain of `dX = b_t(X) dt + √(2D) dW` with step `h`
(the `j`-th step uses the drift frozen at the grid time `j h`):

* `tdOp b D h s k f`: the backward operator `P_s P_{s+h} ⋯ P_{s+(k-1)h} f`,
  `P_τ = emOp (b τ) D h`;
* `tdPow b hb D h k`: the `k`-step kernel started at time `0`, and the dyadic laws
  `tdCurve b hb D ρ₀ n t = tdPow (step 2⁻ⁿ) ⌊t 2ⁿ⌋₊ ∘ₘ ρ₀`.

Main estimates (all **weighted** by `lyap y = 1 + |y|²`, since `b` is unbounded):

* `abs_tdOp_dyadic_succ_sub_le`: for a bounded, continuous, `C`-Lipschitz `f`,
  `|tdOp_{n+1} f x - tdOp_n f x| ≤ C Λ(T) lyap(x) (√(1/2))ⁿ` (dyadic level `n`, time `t ≤ T`);
* `tendsto_tdOp_dyadic`, `exists_tendsto_integral_tdCurve`: pointwise convergence in `x`, and
  convergence of `∫ f d(tdCurve n t)` for **any** probability measure `ρ₀` (dominated
  convergence in `x`; no moment assumption on `ρ₀`);
* `lintegral_lyap_tdPow_le`, `isTightMeasureSet_tdCurve`: Lyapunov bound
  `E lyap(X_k) ≤ (1 + c h)^k lyap(x)` from a Dirac start, and tightness of the dyadic laws
  on bounded time sets.

## Not proved here

* The limit and the Fokker–Planck equation: `Flow/FokkerPlanckExistenceTime.lean`.
* Drifts that are only continuous in time (the Cauchy rate uses the Hölder-`½` bound; see
  `Flow/FokkerPlanckExistenceContinuousTime`), locally Lipschitz or superlinear drifts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace FormalizeSampling.FokkerPlanckExistence

open FormalizeSampling.MeasureHelpers (integral_comp_markov)
open FormalizeSampling.HeatKernelPi FormalizeSampling.WeakFokkerPlanckOU NoiseScore

variable {d : ℕ}

/-! ### The time-dependent EM operator -/

/-- The **time-dependent EM operator**: `tdOp b D h s k f = P_s P_{s+h} ⋯ P_{s+(k-1)h} f` with
`P_τ = emOp (b τ) D h` (outermost step at time `s`). -/
noncomputable def tdOp (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (D h : ℝ) :
    ℝ → ℕ → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | _, 0, f => f
  | s, k + 1, f => emOp (b s) D h (tdOp b D h (s + h) k f)

section Op

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D h : ℝ} {f g : (Fin d → ℝ) → ℝ}

/-- `tdOp` with zero steps is the identity. -/
@[simp] theorem tdOp_zero (s : ℝ) : tdOp b D h s 0 f = f := rfl

/-- Outer recursion: `tdOp s (k + 1) f = P_s (tdOp (s + h) k f)`. -/
theorem tdOp_succ (s : ℝ) (k : ℕ) :
    tdOp b D h s (k + 1) f = emOp (b s) D h (tdOp b D h (s + h) k f) := rfl

/-- Inner recursion: `tdOp s (k + 1) f = tdOp s k (P_{s + k h} f)`. -/
theorem tdOp_succ' (s : ℝ) (k : ℕ) :
    tdOp b D h s (k + 1) f = tdOp b D h s k (emOp (b (s + k * h)) D h f) := by
  induction k generalizing s with
  | zero => simp [tdOp]
  | succ k ih =>
    rw [tdOp_succ, ih (s + h), tdOp_succ]
    have e : s + h + (k : ℝ) * h = s + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
    rw [e]

/-- For continuous `b τ`, `tdOp` preserves bounded continuous functions (same bound `M`). -/
theorem tdOp_cont (hbc : ∀ t, Continuous (b t)) (hf : Continuous f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) (s : ℝ) (k : ℕ) :
    Continuous (tdOp b D h s k f) ∧ ∀ y, |tdOp b D h s k f y| ≤ M := by
  induction k generalizing s with
  | zero => exact ⟨hf, hM⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (s + h)
    exact ⟨continuous_emOp (hbc s) h1 h2, abs_emOp_le h1 h2⟩

/-- **Lipschitz propagation.** If every `b t` is `L`-Lipschitz, `h ≥ 0` and `f` is bounded,
continuous and `C`-Lipschitz, then `tdOp s k f` is `C (1 + h L)^k`-Lipschitz. -/
theorem tdOp_lip {L : ℝ≥0} (hL : ∀ t, LipschitzWith L (b t)) (hh : 0 ≤ h) (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ} (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (s : ℝ)
    (k : ℕ) (x y : Fin d → ℝ) :
    |tdOp b D h s k f x - tdOp b D h s k f y| ≤ C * (1 + h * L) ^ k * ‖x - y‖ := by
  induction k generalizing s x y with
  | zero => simpa using hC x y
  | succ k ih =>
    obtain ⟨h1, h2⟩ := tdOp_cont (D := D) (h := h) (fun t => (hL t).continuous) hf hM (s + h) k
    have := emOp_lipschitz (D := D) (hL s) hh h1 h2 (ih (s + h)) x y
    refine this.trans (le_of_eq ?_)
    ring

/-- **Weighted stability.** Under linear growth `‖b t y‖ ≤ B (1 + ‖y‖)` and Lipschitz `b t`,
`D ≥ 0`, `0 ≤ h ≤ 1`: if `f, g` are bounded continuous with `|f - g| ≤ A lyap`, then
`|tdOp s k f - tdOp s k g| ≤ A (1 + c h)^k lyap`, `c = lyapConst d B D`. -/
theorem abs_tdOp_sub_le_lyap {L : ℝ≥0} (hL : ∀ t, LipschitzWith L (b t)) {B : ℝ}
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hf : Continuous f) (hg : Continuous g) {M N : ℝ} (hM : ∀ y, |f y| ≤ M)
    (hN : ∀ y, |g y| ≤ N) {A : ℝ} (hA : 0 ≤ A) (hfg : ∀ y, |f y - g y| ≤ A * lyap y)
    (s : ℝ) (k : ℕ) (x : Fin d → ℝ) :
    |tdOp b D h s k f x - tdOp b D h s k g x| ≤
      A * (1 + lyapConst d B D * h) ^ k * lyap x := by
  have hc : 0 ≤ 1 + lyapConst d B D * h := by
    have := lyapConst_nonneg (d := d) B hD; positivity
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  induction k generalizing s x with
  | zero => simpa using hfg x
  | succ k ih =>
    obtain ⟨f1, f2⟩ := tdOp_cont (D := D) (h := h) hbc hf hM (s + h) k
    obtain ⟨g1, g2⟩ := tdOp_cont (D := D) (h := h) hbc hg hN (s + h) k
    rw [tdOp_succ, tdOp_succ, ← emOp_sub f1 g1 f2 g2]
    have hb : ∀ y, |tdOp b D h (s + h) k f y - tdOp b D h (s + h) k g y| ≤ M + N := by
      intro y
      have a1 := f2 y
      have a2 := g2 y
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith
    have := abs_emOp_le_lyap (b := b s) (hbc s).measurable (hB s) hD hh0 hh1 (f1.sub g1) hb
      (A := A * (1 + lyapConst d B D * h) ^ k) (by positivity) (ih (s + h)) x
    refine this.trans (le_of_eq ?_)
    ring

end Op

/-! ### Half steps versus full steps -/

/-- The constant `Γ = K + (K + L) (B + √D E‖Z‖)` of the two-half-steps defect. -/
noncomputable def halfConst (d : ℕ) (L : ℝ≥0) (B K D : ℝ) : ℝ :=
  K + (K + L) * (B + Real.sqrt D * gaussNormMean (d := d))

section Half

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0} {B K D h : ℝ} {f : (Fin d → ℝ) → ℝ}

/-- `0 ≤ B` follows from a linear growth bound. -/
theorem nonneg_of_linGrowth (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) : 0 ≤ B := by
  have := (norm_nonneg _).trans (hB 0 0)
  simpa using this

/-- `0 ≤ halfConst`. -/
theorem halfConst_nonneg (hB0 : 0 ≤ B) (hK0 : 0 ≤ K) :
    0 ≤ halfConst d L B K D := by
  have hE : 0 ≤ gaussNormMean (d := d) := integral_nonneg fun _ => norm_nonneg _
  unfold halfConst; positivity

/-- **Two half steps versus one step, time-dependent and weighted.** Under the standing
hypotheses (`b t` `L`-Lipschitz, `‖b t y‖ ≤ B (1 + ‖y‖)`,
`‖b t y - b s y‖ ≤ K √|t - s| (1 + ‖y‖)`, `K ≥ 0`), for `D ≥ 0`, `0 ≤ h ≤ 1` and `g` bounded,
continuous and `C`-Lipschitz (`C ≥ 0`):
`|P_s^{h/2} P_{s+h/2}^{h/2} g x - P_s^h g x| ≤ C h √h Γ lyap(x)`, `Γ = halfConst d L B K D`. -/
theorem abs_tdHalf_sub_le (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hK0 : 0 ≤ K)
    (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, |g y| ≤ M) {C : ℝ} (hC : ∀ x y, |g x - g y| ≤ C * ‖x - y‖)
    (hC0 : 0 ≤ C) (s : ℝ) (x : Fin d → ℝ) :
    |emOp (b s) D (h / 2) (emOp (b (s + h / 2)) D (h / 2) g) x - emOp (b s) D h g x| ≤
      C * (h * Real.sqrt h * halfConst d L B K D) * lyap x := by
  have hB0 := nonneg_of_linGrowth hB
  set η := K * Real.sqrt (h / 2) with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hη : ∀ y, ‖b (s + h / 2) y - b s y‖ ≤ η * (1 + ‖y‖) := by
    intro y
    have := hK s (s + h / 2) y
    rwa [show s + h / 2 - s = h / 2 by ring, abs_of_nonneg (by positivity)] at this
  have key := abs_emOp_two_sub_le (hL s) (hL (s + h / 2)).continuous hη0 hη hD hh0 hg hM hC
    hC0 x
  refine key.trans ?_
  set E := gaussNormMean (d := d) with hEdef
  have hE : 0 ≤ E := integral_nonneg fun _ => norm_nonneg _
  set r := Real.sqrt h with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := by rw [hr, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hh1
  have hrr : r * r = h := Real.mul_self_sqrt hh0
  have hhr : h ≤ r := by nlinarith
  have hη1 : η ≤ K * r := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hK0
  have hη2 : η ≤ K := hη1.trans (by nlinarith)
  set lam := lyap x with hlam
  have hl1 : 1 ≤ lam := one_le_lyap x
  have hxl := one_add_norm_le_lyap x
  have hbx : ‖b s x‖ ≤ 2 * B * lam := (hB s x).trans (by nlinarith)
  have hsD : Real.sqrt (D * h) = Real.sqrt D * r := Real.sqrt_mul hD h
  have hsD0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have inner : h / 2 * ‖b s x‖ + Real.sqrt (D * h) * E ≤ r * (B + Real.sqrt D * E) * lam := by
    rw [hsD]
    have a1 : h / 2 * ‖b s x‖ ≤ r * B * lam := by
      have : h / 2 * ‖b s x‖ ≤ h / 2 * (2 * B * lam) := mul_le_mul_of_nonneg_left hbx (by linarith)
      nlinarith [mul_nonneg hB0 (by linarith : (0 : ℝ) ≤ lam)]
    have a2 : Real.sqrt D * r * E ≤ r * Real.sqrt D * E * lam := by
      have : 0 ≤ r * Real.sqrt D * E := by positivity
      nlinarith
    nlinarith
  have hin0 : 0 ≤ h / 2 * ‖b s x‖ + Real.sqrt (D * h) * E := by positivity
  have t1 : η * (1 + ‖x‖) ≤ K * r * (2 * lam) := by
    have := mul_le_mul hη1 hxl (by positivity) (by positivity)
    linarith
  have t2 : (η + L) * (h / 2 * ‖b s x‖ + Real.sqrt (D * h) * E) ≤
      (K + L) * (r * (B + Real.sqrt D * E) * lam) :=
    mul_le_mul (by linarith) inner hin0 (by positivity)
  have hC2 : 0 ≤ C * (h / 2) := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hC2
  refine this.trans ?_
  unfold halfConst
  rw [← hEdef]
  have hX : 0 ≤ (K + L) * (B + Real.sqrt D * E) := by positivity
  have : C * (h / 2) * (K * r * (2 * lam) + (K + L) * (r * (B + Real.sqrt D * E) * lam)) =
      C * h * r * lam * (K + (K + L) * (B + Real.sqrt D * E) / 2) := by ring
  rw [this]
  have : C * (h * r * (K + (K + L) * (B + Real.sqrt D * E))) * lam =
      C * h * r * lam * (K + (K + L) * (B + Real.sqrt D * E)) := by ring
  rw [this]
  have hCh : 0 ≤ C * h * r * lam := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hCh

/-- **Half-step chain versus full-step chain (weighted).** Under the standing hypotheses, for
`D ≥ 0`, `0 ≤ h ≤ 1` and `f` bounded, continuous, `C`-Lipschitz (`C ≥ 0`):
`|tdOp_{h/2} s (2k) f x - tdOp_h s k f x| ≤
  k C (1 + (h/2) L)^{2k} h √h Γ (1 + c h)^k lyap(x)`. -/
theorem abs_tdOp_half_sub_le (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hK0 : 0 ≤ K)
    (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hf : Continuous f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {C : ℝ} (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C)
    (k : ℕ) (s : ℝ) (x : Fin d → ℝ) :
    |tdOp b D (h / 2) s (2 * k) f x - tdOp b D h s k f x| ≤
      k * (C * (1 + h / 2 * L) ^ (2 * k) * (h * Real.sqrt h * halfConst d L B K D)) *
        (1 + lyapConst d B D * h) ^ k * lyap x := by
  have hB0 := nonneg_of_linGrowth hB
  have hΓ := halfConst_nonneg (d := d) (L := L) (D := D) hB0 hK0
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  have hc : 1 ≤ 1 + lyapConst d B D * h :=
    le_add_of_nonneg_right (mul_nonneg (lyapConst_nonneg B hD) hh0)
  have hh2 : 0 ≤ h / 2 := by positivity
  set δ := h * Real.sqrt h * halfConst d L B K D with hδ
  have hδ0 : 0 ≤ δ := by positivity
  induction k generalizing s x with
  | zero => simp
  | succ k ih =>
    have e1 : tdOp b D (h / 2) s (2 * (k + 1)) f = emOp (b s) D (h / 2)
        (emOp (b (s + h / 2)) D (h / 2) (tdOp b D (h / 2) (s + h) (2 * k) f)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, tdOp_succ, tdOp_succ,
        show s + h / 2 + h / 2 = s + h by ring]
    rw [e1, tdOp_succ]
    set g := tdOp b D (h / 2) (s + h) (2 * k) f with hg
    set p := tdOp b D h (s + h) k f with hp
    obtain ⟨g1, g2⟩ := tdOp_cont (D := D) (h := h / 2) hbc hf hM (s + h) (2 * k)
    obtain ⟨p1, p2⟩ := tdOp_cont (D := D) (h := h) hbc hf hM (s + h) k
    have g3 := tdOp_lip (D := D) hL hh2 hf hM hC (s + h) (2 * k)
    set Cg := C * (1 + h / 2 * L) ^ (2 * k) with hCg
    set Cg' := C * (1 + h / 2 * L) ^ (2 * (k + 1)) with hCg'
    have hCg0 : 0 ≤ Cg := by positivity
    have hCgle : Cg ≤ Cg' :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity))
        (by omega)) hC0
    have t1 := abs_tdHalf_sub_le (D := D) hL hB hK hK0 hD hh0 hh1 g1 g2 g3 hCg0 s x
    set W := (1 + lyapConst d B D * h) with hW
    set A := (k : ℝ) * (Cg * δ) * W ^ k with hA
    have hA0 : 0 ≤ A := by positivity
    have hgp : ∀ y, |g y - p y| ≤ A * lyap y := fun y => ih (s + h) y
    have hgpM : ∀ y, |g y - p y| ≤ M + M := by
      intro y
      have a1 := g2 y
      have a2 := p2 y
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith
    have t2 : |emOp (b s) D h g x - emOp (b s) D h p x| ≤ A * (W * lyap x) := by
      rw [← emOp_sub g1 p1 g2 p2]
      exact abs_emOp_le_lyap (hbc s).measurable (hB s) hD hh0 hh1 (g1.sub p1) hgpM hA0 hgp x
    have hl := lyap_pos x
    have hW1 : 1 ≤ W ^ (k + 1) := one_le_pow₀ hc
    have a1 : Cg * δ * lyap x ≤ Cg' * δ * W ^ (k + 1) * lyap x := by
      refine mul_le_mul_of_nonneg_right ?_ hl.le
      exact (mul_le_mul_of_nonneg_right hCgle hδ0).trans
        (le_mul_of_one_le_right (by positivity) hW1)
    have a2 : A * (W * lyap x) ≤ k * (Cg' * δ) * W ^ (k + 1) * lyap x := by
      have e : A * (W * lyap x) = k * (Cg * δ) * W ^ (k + 1) * lyap x := by
        rw [hA, pow_succ]; ring
      rw [e]
      gcongr
    have e3 : ((k + 1 : ℕ) : ℝ) * (Cg' * δ) * W ^ (k + 1) * lyap x =
        Cg' * δ * W ^ (k + 1) * lyap x + k * (Cg' * δ) * W ^ (k + 1) * lyap x := by
      push_cast; ring
    calc _ ≤ |emOp (b s) D (h / 2) (emOp (b (s + h / 2)) D (h / 2) g) x -
          emOp (b s) D h g x| + |emOp (b s) D h g x - emOp (b s) D h p x| := abs_sub_le _ _ _
      _ ≤ Cg * δ * lyap x + A * (W * lyap x) := add_le_add t1 t2
      _ ≤ _ := by rw [e3]; linarith

/-- **One extra half step (weighted).** Under linear growth and Lipschitz `b t`, `D ≥ 0`,
`0 ≤ h ≤ 1`, and `f` bounded, continuous, `C`-Lipschitz (`C ≥ 0`):
`|tdOp_{h/2} s (2k+1) f x - tdOp_{h/2} s (2k) f x| ≤
  C √h (B + √D E‖Z‖) (1 + c h/2)^{2k} lyap(x)`. -/
theorem abs_tdOp_extra_le (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ}
    (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C) (k : ℕ) (s : ℝ) (x : Fin d → ℝ) :
    |tdOp b D (h / 2) s (2 * k + 1) f x - tdOp b D (h / 2) s (2 * k) f x| ≤
      C * (Real.sqrt h * (B + Real.sqrt D * gaussNormMean (d := d))) *
        (1 + lyapConst d B D * (h / 2)) ^ (2 * k) * lyap x := by
  have hB0 := nonneg_of_linGrowth hB
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  have hh2 : 0 ≤ h / 2 := by positivity
  have hh21 : h / 2 ≤ 1 := by linarith
  set E := gaussNormMean (d := d) with hEdef
  have hE : 0 ≤ E := integral_nonneg fun _ => norm_nonneg _
  have hstep : ∀ τ y, |emOp (b τ) D (h / 2) f y - f y| ≤
      C * (Real.sqrt h * (B + Real.sqrt D * E)) * lyap y := by
    intro τ y
    refine (abs_emOp_sub_le_pt (b τ) hD hh2 hf hM hC hC0 y).trans ?_
    set r := Real.sqrt h with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrr : r * r = h := Real.mul_self_sqrt hh0
    have hr1 : r ≤ 1 := by rw [hr, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hh1
    have hhr : h ≤ r := by nlinarith
    have hl1 := one_le_lyap y
    have hyl := one_add_norm_le_lyap y
    have hby : ‖b τ y‖ ≤ 2 * B * lyap y := (hB τ y).trans (by nlinarith)
    have hsD : Real.sqrt (2 * D * (h / 2)) = Real.sqrt D * r := by
      rw [show 2 * D * (h / 2) = D * h by ring]; exact Real.sqrt_mul hD h
    rw [hsD]
    have a1 : h / 2 * ‖b τ y‖ ≤ r * B * lyap y := by
      have : h / 2 * ‖b τ y‖ ≤ h / 2 * (2 * B * lyap y) :=
        mul_le_mul_of_nonneg_left hby hh2
      nlinarith [mul_nonneg hB0 (by linarith : (0 : ℝ) ≤ lyap y)]
    have a2 : Real.sqrt D * r * E ≤ r * Real.sqrt D * E * lyap y := by
      have : 0 ≤ r * Real.sqrt D * E := by positivity
      nlinarith
    have : h / 2 * ‖b τ y‖ + Real.sqrt D * r * E ≤ r * (B + Real.sqrt D * E) * lyap y := by
      nlinarith
    calc C * (h / 2 * ‖b τ y‖ + Real.sqrt D * r * E)
        ≤ C * (r * (B + Real.sqrt D * E) * lyap y) := mul_le_mul_of_nonneg_left this hC0
      _ = _ := by ring
  rw [tdOp_succ']
  exact abs_tdOp_sub_le_lyap hL hB hD hh2 hh21 (continuous_emOp (hbc _) hf hM) hf
    (abs_emOp_le hf hM) hM (by positivity) (hstep _) s (2 * k) x

end Half

/-! ### Dyadic levels -/

/-- The constant `Λ(T) = (T Γ e^{LT} + B + √D E‖Z‖) e^{cT}` of the dyadic Cauchy estimate. -/
noncomputable def cauchyConst (d : ℕ) (L : ℝ≥0) (B K D T : ℝ) : ℝ :=
  (T * halfConst d L B K D * Real.exp (L * T) + (B + Real.sqrt D * gaussNormMean (d := d))) *
    Real.exp (lyapConst d B D * T)

section Dyadic

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {L : ℝ≥0} {B K D : ℝ} {f : (Fin d → ℝ) → ℝ}

/-- **Dyadic Cauchy estimate (weighted).** Under the standing hypotheses (`b t` `L`-Lipschitz,
`‖b t y‖ ≤ B (1 + ‖y‖)`, `‖b t y - b s y‖ ≤ K √|t - s| (1 + ‖y‖)`, `K ≥ 0`), `D ≥ 0`,
`f` bounded, continuous, `C`-Lipschitz (`C ≥ 0`), `0 ≤ T`, `t ≤ T`:
`|tdOp_{2^{-(n+1)}} 0 ⌊t 2^{n+1}⌋₊ f x - tdOp_{2^{-n}} 0 ⌊t 2ⁿ⌋₊ f x| ≤
  C Λ(T) lyap(x) (√(1/2))ⁿ`. -/
theorem abs_tdOp_dyadic_succ_sub_le (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hK0 : 0 ≤ K)
    (hD : 0 ≤ D) (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ}
    (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    {t : ℝ} (ht : t ≤ T) (x : Fin d → ℝ) :
    |tdOp b D (dyadicStep (n + 1)) 0 (gridIndex (n + 1) t) f x -
        tdOp b D (dyadicStep n) 0 (gridIndex n t) f x| ≤
      C * cauchyConst d L B K D T * lyap x * Real.sqrt (1 / 2) ^ n := by
  have hB0 := nonneg_of_linGrowth hB
  rw [dyadicStep_succ]
  set h := dyadicStep n with hhdef
  set k := gridIndex n t with hk
  have hh0 : 0 ≤ h := (dyadicStep_pos n).le
  have hh1 : h ≤ 1 := dyadicStep_le_one n
  have hkh : (k : ℝ) * h ≤ T := (gridIndex_mul_le n t).trans (max_le ht hT)
  have hk0 : 0 ≤ (k : ℝ) * h := by positivity
  set E := gaussNormMean (d := d) with hEdef
  have hE : 0 ≤ E := integral_nonneg fun _ => norm_nonneg _
  set c := lyapConst d B D with hcdef
  have hc0 : 0 ≤ c := lyapConst_nonneg B hD
  set Γ := halfConst d L B K D with hΓdef
  have hΓ : 0 ≤ Γ := halfConst_nonneg hB0 hK0
  set r := Real.sqrt h with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrn : r = Real.sqrt (1 / 2) ^ n := sqrt_dyadicStep n
  have hl := lyap_pos x
  have hexpL : (1 + h / 2 * L) ^ (2 * k) ≤ Real.exp (L * T) := by
    refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.2 ?_)
    push_cast
    nlinarith [L.coe_nonneg]
  have hexpc : (1 + c * h) ^ k ≤ Real.exp (c * T) := by
    refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.2 ?_)
    nlinarith
  have hexpc' : (1 + c * (h / 2)) ^ (2 * k) ≤ Real.exp (c * T) := by
    refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.2 ?_)
    push_cast
    nlinarith
  have main : |tdOp b D (h / 2) 0 (2 * k) f x - tdOp b D h 0 k f x| ≤
      C * (T * Γ * Real.exp (L * T) * Real.exp (c * T)) * lyap x * r := by
    refine (abs_tdOp_half_sub_le hL hB hK hK0 hD hh0 hh1 hf hM hC hC0 k 0 x).trans ?_
    have e : (k : ℝ) * (C * (1 + h / 2 * L) ^ (2 * k) * (h * r * Γ)) * (1 + c * h) ^ k *
        lyap x = C * ((k * h) * Γ * (1 + h / 2 * L) ^ (2 * k) * (1 + c * h) ^ k) *
          lyap x * r := by ring
    rw [e]
    gcongr
  have extra : |tdOp b D (h / 2) 0 (2 * k + 1) f x - tdOp b D (h / 2) 0 (2 * k) f x| ≤
      C * ((B + Real.sqrt D * E) * Real.exp (c * T)) * lyap x * r := by
    refine (abs_tdOp_extra_le hL hB hD hh0 hh1 hf hM hC hC0 k 0 x).trans ?_
    have e : C * (r * (B + Real.sqrt D * E)) * (1 + c * (h / 2)) ^ (2 * k) * lyap x =
        C * ((B + Real.sqrt D * E) * (1 + c * (h / 2)) ^ (2 * k)) * lyap x * r := by ring
    rw [e]
    gcongr
  have hsplit : C * cauchyConst d L B K D T * lyap x * Real.sqrt (1 / 2) ^ n =
      C * (T * Γ * Real.exp (L * T) * Real.exp (c * T)) * lyap x * r +
        C * ((B + Real.sqrt D * E) * Real.exp (c * T)) * lyap x * r := by
    rw [← hrn, cauchyConst]; ring
  have hX : 0 ≤ C * ((B + Real.sqrt D * E) * Real.exp (c * T)) * lyap x * r := by positivity
  rw [hsplit]
  rcases gridIndex_succ n t with h2k | h2k
  · rw [← hk] at h2k
    rw [h2k]
    linarith
  · rw [← hk] at h2k
    rw [h2k]
    calc _ ≤ |tdOp b D (h / 2) 0 (2 * k + 1) f x - tdOp b D (h / 2) 0 (2 * k) f x| +
          |tdOp b D (h / 2) 0 (2 * k) f x - tdOp b D h 0 k f x| := abs_sub_le _ _ _
      _ ≤ _ := by linarith

/-- **Pointwise convergence of the dyadic EM operators.** Under the hypotheses of
`abs_tdOp_dyadic_succ_sub_le`, for every `t` and `x` the sequence
`n ↦ tdOp_{2⁻ⁿ} 0 ⌊t 2ⁿ⌋₊ f x` converges. -/
theorem tendsto_tdOp_dyadic (hL : ∀ t, LipschitzWith L (b t))
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hK0 : 0 ≤ K)
    (hD : 0 ≤ D) (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ}
    (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖) (hC0 : 0 ≤ C) (t : ℝ) (x : Fin d → ℝ) :
    ∃ a, Tendsto (fun n => tdOp b D (dyadicStep n) 0 (gridIndex n t) f x) atTop (𝓝 a) := by
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (Real.sqrt (1 / 2))
    (C * cauchyConst d L B K D (max t 0) * lyap x) ?_ fun n => ?_)
  · rw [Real.sqrt_lt' one_pos]; norm_num
  · rw [Real.dist_eq, abs_sub_comm]
    exact abs_tdOp_dyadic_succ_sub_le hL hB hK hK0 hD hf hM hC hC0 (le_max_right t 0) n
      (le_max_left t 0) x

end Dyadic

/-! ### Kernels and laws -/

/-- The `k`-step **time-dependent EM kernel** from time `0` with step `h`:
`tdPow 0 = id`, `tdPow (k + 1) = emStep (b (k h)) ∘ₖ tdPow k`. -/
noncomputable def tdPow (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ t, Measurable (b t))
    (D h : ℝ) : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)
  | 0 => Kernel.id
  | k + 1 => emStep (b (k * h)) (hb _) D h ∘ₖ tdPow b hb D h k

/-- `tdPow k` is a Markov kernel. -/
instance isMarkovKernel_tdPow (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ t, Measurable (b t))
    (D h : ℝ) (k : ℕ) : IsMarkovKernel (tdPow b hb D h k) := by
  induction k with
  | zero => unfold tdPow; infer_instance
  | succ k ih => unfold tdPow; infer_instance

/-- The **dyadic time-dependent EM law** at level `n` and time `t`: `ρ₀` pushed through
`⌊t 2ⁿ⌋₊` EM steps of size `2⁻ⁿ`, the `j`-th step using the drift `b (j 2⁻ⁿ)`. -/
noncomputable def tdCurve (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ t, Measurable (b t))
    (D : ℝ) (ρ₀ : Measure (Fin d → ℝ)) (n : ℕ) (t : ℝ) : Measure (Fin d → ℝ) :=
  tdPow b hb D (dyadicStep n) (gridIndex n t) ∘ₘ ρ₀

/-- The dyadic time-dependent EM laws of a probability measure are probability measures. -/
instance isProbabilityMeasure_tdCurve (b : ℝ → (Fin d → ℝ) → Fin d → ℝ)
    (hb : ∀ t, Measurable (b t)) (D : ℝ) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀]
    (n : ℕ) (t : ℝ) : IsProbabilityMeasure (tdCurve b hb D ρ₀ n t) := by
  unfold tdCurve; infer_instance

section Laws

variable {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {D h : ℝ} {f : (Fin d → ℝ) → ℝ}

/-- **Kernel integrals are operator values.** For continuous `b t`, `D, h ≥ 0` and `f` bounded
continuous: `∫ f d(tdPow k x) = tdOp b D h 0 k f x`. -/
theorem integral_tdPow (hb : ∀ t, Measurable (b t)) (hbc : ∀ t, Continuous (b t))
    (hD : 0 ≤ D) (hh : 0 ≤ h) (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) (k : ℕ)
    (x : Fin d → ℝ) : ∫ y, f y ∂(tdPow b hb D h k x) = tdOp b D h 0 k f x := by
  induction k generalizing f M with
  | zero =>
    simp only [tdPow, Kernel.id_apply, tdOp_zero]
    exact integral_dirac f x
  | succ k ih =>
    show ∫ y, f y ∂((emStep (b (k * h)) (hb _) D h ∘ₖ tdPow b hb D h k) x) = _
    rw [Kernel.integral_comp (Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y))]
    simp_rw [integral_emStep (hb _) hD hh hf]
    rw [ih (continuous_emOp (hbc _) hf hM) (abs_emOp_le hf hM), tdOp_succ', zero_add]

/-- Integrals against the dyadic laws are integrals of the EM operator against `ρ₀`. -/
theorem integral_tdCurve (hb : ∀ t, Measurable (b t)) (hbc : ∀ t, Continuous (b t))
    (hD : 0 ≤ D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) (n : ℕ) (t : ℝ) :
    ∫ y, f y ∂(tdCurve b hb D ρ₀ n t) =
      ∫ x, tdOp b D (dyadicStep n) 0 (gridIndex n t) f x ∂ρ₀ := by
  rw [tdCurve, integral_comp_markov _ ρ₀ hf hM]
  exact integral_congr_ae (ae_of_all _ fun x =>
    integral_tdPow hb hbc hD (dyadicStep_pos n).le hf hM _ x)

/-- **Convergence of Lipschitz integrals along the dyadic laws.** Under the standing hypotheses
(`b t` `L`-Lipschitz, linear growth, Hölder-`½` in time), `D ≥ 0`, **any** probability measure
`ρ₀` and `f` bounded, continuous, `C`-Lipschitz (`C ≥ 0`), the sequence
`n ↦ ∫ f d(tdCurve b hb D ρ₀ n t)` converges for every `t`. -/
theorem exists_tendsto_integral_tdCurve (hb : ∀ t, Measurable (b t)) {L : ℝ≥0}
    (hL : ∀ t, LipschitzWith L (b t)) {B K : ℝ} (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖))
    (hK : ∀ s t y, ‖b t y - b s y‖ ≤ K * Real.sqrt |t - s| * (1 + ‖y‖)) (hK0 : 0 ≤ K)
    (hD : 0 ≤ D) (ρ₀ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ρ₀] (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) {C : ℝ} (hC : ∀ x y, |f x - f y| ≤ C * ‖x - y‖)
    (hC0 : 0 ≤ C) (t : ℝ) :
    ∃ c, Tendsto (fun n => ∫ y, f y ∂(tdCurve b hb D ρ₀ n t)) atTop (𝓝 c) := by
  have hbc : ∀ t, Continuous (b t) := fun t => (hL t).continuous
  choose a ha using fun x => tendsto_tdOp_dyadic hL hB hK hK0 hD hf hM hC hC0 t x
  refine ⟨∫ x, a x ∂ρ₀, ?_⟩
  have e : (fun n => ∫ y, f y ∂(tdCurve b hb D ρ₀ n t)) =
      fun n => ∫ x, tdOp b D (dyadicStep n) 0 (gridIndex n t) f x ∂ρ₀ :=
    funext fun n => integral_tdCurve hb hbc hD ρ₀ hf hM n t
  rw [e]
  exact tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => (tdOp_cont hbc hf hM 0 _).1.aestronglyMeasurable) (integrable_const M)
    (fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact (tdOp_cont hbc hf hM 0 _).2 x)
    (ae_of_all _ ha)

/-- **Lyapunov bound from a Dirac start.** Under linear growth `‖b t y‖ ≤ B (1 + ‖y‖)`,
`D ≥ 0`, `0 ≤ h ≤ 1`: `E lyap(X_k) ≤ (1 + c h)^k lyap(x)` for `X_k ∼ tdPow k x`. -/
theorem lintegral_lyap_tdPow_le (hb : ∀ t, Measurable (b t)) {B : ℝ}
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (x : Fin d → ℝ) (k : ℕ) :
    ∫⁻ z, ENNReal.ofReal (lyap z) ∂(tdPow b hb D h k x) ≤
      ENNReal.ofReal ((1 + lyapConst d B D * h) ^ k * lyap x) := by
  have hm : Measurable fun z : Fin d → ℝ => ENNReal.ofReal (lyap z) :=
    ENNReal.measurable_ofReal.comp continuous_lyap.measurable
  have hc : 0 ≤ 1 + lyapConst d B D * h := by
    have := lyapConst_nonneg (d := d) B hD; positivity
  induction k with
  | zero =>
    simp only [tdPow, Kernel.id_apply]
    rw [lintegral_dirac' _ hm]
    simp
  | succ k ih =>
    show ∫⁻ z, ENNReal.ofReal (lyap z) ∂((emStep (b (k * h)) (hb _) D h ∘ₖ
      tdPow b hb D h k) x) ≤ _
    rw [Kernel.lintegral_comp _ _ _ hm]
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (1 + lyapConst d B D * h) * ENNReal.ofReal (lyap y)
          ∂(tdPow b hb D h k x) := by
          refine lintegral_mono fun y => ?_
          refine (lintegral_lyap_emStep_le (hb _) hD hh0 hh1 (hB _ y)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul hc]
      _ = ENNReal.ofReal (1 + lyapConst d B D * h) *
            ∫⁻ y, ENNReal.ofReal (lyap y) ∂(tdPow b hb D h k x) := lintegral_const_mul _ hm
      _ ≤ ENNReal.ofReal (1 + lyapConst d B D * h) *
            ENNReal.ofReal ((1 + lyapConst d B D * h) ^ k * lyap x) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hc, pow_succ]; ring_nf

/-- **Weighted integral bound along the chain.** Under linear growth, `D ≥ 0`, `0 ≤ h ≤ 1`:
if `F` is integrable for `tdPow k x` and `|F| ≤ A lyap` (`A ≥ 0`), then
`|∫ F d(tdPow k x)| ≤ A (1 + c h)^k lyap(x)`. -/
theorem abs_integral_tdPow_le (hb : ∀ t, Measurable (b t)) {B : ℝ}
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    {k : ℕ} {x : Fin d → ℝ} {F : (Fin d → ℝ) → ℝ} (hF : Integrable F (tdPow b hb D h k x))
    {A : ℝ} (hA : 0 ≤ A) (hFV : ∀ y, |F y| ≤ A * lyap y) :
    |∫ y, F y ∂(tdPow b hb D h k x)| ≤ A * ((1 + lyapConst d B D * h) ^ k * lyap x) := by
  have hc : 0 ≤ 1 + lyapConst d B D * h := by
    have := lyapConst_nonneg (d := d) B hD; positivity
  exact abs_integral_le_of_le_lyap hF hA (by have := lyap_pos x; positivity) hFV
    (lintegral_lyap_tdPow_le hb hB hD hh0 hh1 x k)

/-- **Tightness of the dyadic time-dependent EM laws.** Under linear growth
`‖b t y‖ ≤ B (1 + ‖y‖)` (all `t`), `D ≥ 0`, any probability measure `ρ₀` and `T : ℝ`, the laws
`tdCurve b hb D ρ₀ n t` over all levels `n` and times `t ≤ T` form a tight set. -/
theorem isTightMeasureSet_tdCurve (hb : ∀ t, Measurable (b t)) {B : ℝ}
    (hB : ∀ t y, ‖b t y‖ ≤ B * (1 + ‖y‖)) (hD : 0 ≤ D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] (T : ℝ) :
    IsTightMeasureSet {μ | ∃ n : ℕ, ∃ t ≤ T, μ = tdCurve b hb D ρ₀ n t} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K₀, hK₀, hρK₀⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := ρ₀)) (ε / 2) hε2
  have hρ : ρ₀ K₀ᶜ ≤ ε / 2 := hρK₀ ρ₀ rfl
  obtain ⟨Λ₀, hΛ₀⟩ := hK₀.exists_bound_of_continuousOn continuous_lyap.continuousOn
  obtain ⟨η, hη0, hη1, hη2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε2
  have hη : 0 < η := ENNReal.ofReal_pos.1 hη1
  set T' := max T 0
  set c := lyapConst d B D with hcdef
  have hc0 : 0 ≤ c := lyapConst_nonneg B hD
  set C' : ℝ := Real.exp (c * T') * |Λ₀| with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set r : ℝ := Real.sqrt (C' / η) + 1 with hr
  have hr0 : 0 < r := by positivity
  have hCr : ENNReal.ofReal C' / ENNReal.ofReal (r ^ 2) ≤ ε / 2 := by
    refine (ENNReal.div_le_of_le_mul ?_).trans hη2.le
    rw [← ENNReal.ofReal_mul hη.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.sqrt (C' / η) ≤ r := by linarith
    have h2 : C' / η ≤ r ^ 2 := by
      calc C' / η = Real.sqrt (C' / η) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [div_le_iff₀ hη] at h2
    linarith
  refine ⟨closedBall 0 r, isCompact_closedBall _ _, ?_⟩
  rintro μ ⟨n, t, ht, rfl⟩
  have hh0 : 0 ≤ dyadicStep n := (dyadicStep_pos n).le
  have hh1 : dyadicStep n ≤ 1 := dyadicStep_le_one n
  have hT := dyadic_grid_bound n ht
  have hsub : (closedBall (0 : Fin d → ℝ) r)ᶜ ⊆
      {z | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (lyap z)} := by
    intro z hz
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
    have := one_add_sq_norm_le_lyap z
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  unfold tdCurve
  rw [Measure.bind_apply measurableSet_closedBall.compl (Kernel.aemeasurable _)]
  calc ∫⁻ x, tdPow b hb D (dyadicStep n) (gridIndex n t) x (closedBall 0 r)ᶜ ∂ρ₀
      ≤ ∫⁻ x, (ε / 2 + K₀ᶜ.indicator 1 x) ∂ρ₀ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K₀
        · refine le_trans ?_ (hCr.trans le_self_add)
          refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
            (ENNReal.measurable_ofReal.comp continuous_lyap.measurable).aemeasurable
            (by simp; positivity) ENNReal.ofReal_ne_top).trans ?_)
          gcongr
          refine (lintegral_lyap_tdPow_le hb hB hD hh0 hh1 x _).trans
            (ENNReal.ofReal_le_ofReal ?_)
          have hp : (1 + c * dyadicStep n) ^ gridIndex n t ≤ Real.exp (c * T') := by
            refine (one_add_pow_le_exp (by positivity) _).trans (Real.exp_le_exp.2 ?_)
            nlinarith
          have hlx : lyap x ≤ |Λ₀| := by
            have := hΛ₀ x hx
            rw [Real.norm_eq_abs, abs_of_pos (lyap_pos x)] at this
            exact this.trans (le_abs_self _)
          calc (1 + c * dyadicStep n) ^ gridIndex n t * lyap x ≤
              Real.exp (c * T') * lyap x :=
                mul_le_mul_of_nonneg_right hp (lyap_pos x).le
            _ ≤ C' := mul_le_mul_of_nonneg_left hlx (by positivity)
        · rw [indicator_of_mem (mem_compl hx)]
          exact prob_le_one.trans le_add_self
    _ = ε / 2 + ρ₀ K₀ᶜ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_one hK₀.isClosed.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

end Laws

end FormalizeSampling.FokkerPlanckExistence
