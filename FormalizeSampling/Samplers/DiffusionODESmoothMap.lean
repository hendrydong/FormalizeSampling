module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# An analytic circle map that collapses almost every point onto an integer

Helper for `Samplers/DiffusionODESmooth.lean`. Status: **Verified** (elementary real analysis).

`ψ(u) = u - sin(2πu)/(2π)` (`sinStep`) and its iterates `Φ_m = ψ^[m]` (`cellMap`).

## Main results

* `contDiff_cellMap`: `Φ_m` is `ContDiff ℝ ⊤` (analytic).
* `cellMap_add_int`, `cellMap_neg`: `Φ_m(u + n) = Φ_m(u) + n`, `Φ_m` odd.
* `abs_cellMap_le`, `abs_cellMap_sub_le`: on `[-1/2, 1/2]` `Φ_m v` lies between `0` and `v`;
  globally `|Φ_m(u) - u| ≤ 1/2`.
* `tendsto_cellMap_of_nonneg`, `exists_abs_cellMap_le`: for `|v| < 1/2`, `Φ_m v → 0`.
* `lipschitzWith_cellMap`, `hasDerivAt_cellMap_half`: `Φ_m` is `2^m`-Lipschitz and
  `Φ_m'(1/2) = 2^m` (so `2^m` is its exact Lipschitz constant).

## Not proved here

* No convergence rate of `Φ_m v → 0` (the number of iterations needed near `±1/2` grows like
  `log₂ (1 / (1/2 - |v|))`).
-/

@[expose] public section

open Filter Topology

namespace FormalizeSampling.DiffusionODESmooth

/-- The smooth circle map `ψ(u) = u - sin(2πu)/(2π)` (`C^ω`). Its fixed points are `½ℤ`; the
integers are superattracting (`ψ' = 1 - cos(2πu) = 0`), the half-integers repelling (`ψ' = 2`). -/
noncomputable def sinStep (u : ℝ) : ℝ := u - Real.sin (2 * Real.pi * u) / (2 * Real.pi)

/-- The `m`-fold iterate `Φ_m = ψ^[m]` of `sinStep`. -/
noncomputable def cellMap (m : ℕ) : ℝ → ℝ := sinStep^[m]

/-- `ψ` is analytic (`ContDiff ℝ ⊤`, i.e. `C^ω`). -/
theorem contDiff_sinStep : ContDiff ℝ ⊤ sinStep := by
  unfold sinStep
  fun_prop

/-- `Φ_m` is analytic (`ContDiff ℝ ⊤`) for every `m`. -/
theorem contDiff_cellMap (m : ℕ) : ContDiff ℝ ⊤ (cellMap m) := by
  induction m with
  | zero => simpa [cellMap] using contDiff_id
  | succ m ih =>
    have : cellMap (m + 1) = sinStep ∘ cellMap m := by
      unfold cellMap; rw [Function.iterate_succ']
    rw [this]; exact contDiff_sinStep.comp ih

/-- `ψ` commutes with integer translations: `ψ(u + n) = ψ(u) + n`. -/
theorem sinStep_add_int (u : ℝ) (n : ℤ) : sinStep (u + n) = sinStep u + n := by
  unfold sinStep
  have : 2 * Real.pi * (u + n) = 2 * Real.pi * u + n * (2 * Real.pi) := by ring
  rw [this, Real.sin_add_int_mul_two_pi]; ring

/-- `Φ_m(u + n) = Φ_m(u) + n` for `n ∈ ℤ`. -/
theorem cellMap_add_int (m : ℕ) (u : ℝ) (n : ℤ) : cellMap m (u + n) = cellMap m u + n := by
  induction m generalizing u with
  | zero => simp [cellMap]
  | succ m ih =>
    simp only [cellMap, Function.iterate_succ_apply] at ih ⊢
    rw [sinStep_add_int, ih]

/-- `ψ` is odd. -/
theorem sinStep_neg (u : ℝ) : sinStep (-u) = -sinStep u := by
  unfold sinStep; rw [mul_neg, Real.sin_neg]; ring

/-- `Φ_m` is odd. -/
theorem cellMap_neg (m : ℕ) (u : ℝ) : cellMap m (-u) = -cellMap m u := by
  induction m generalizing u with
  | zero => simp [cellMap]
  | succ m ih =>
    simp only [cellMap, Function.iterate_succ_apply] at ih ⊢
    rw [sinStep_neg, ih]

/-- For `0 ≤ v ≤ 1/2`: `0 ≤ ψ(v) ≤ v`. -/
theorem sinStep_mem {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) : 0 ≤ sinStep v ∧ sinStep v ≤ v := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hs0 : 0 ≤ Real.sin (2 * Real.pi * v) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hs1 : Real.sin (2 * Real.pi * v) ≤ 2 * Real.pi * v := Real.sin_le (by positivity)
  unfold sinStep
  constructor
  · rw [sub_nonneg, div_le_iff₀ hpi]; linarith
  · have : 0 ≤ Real.sin (2 * Real.pi * v) / (2 * Real.pi) := div_nonneg hs0 hpi.le
    linarith

/-- For `0 ≤ v ≤ 1/2`: `0 ≤ Φ_m(v) ≤ v`. -/
theorem cellMap_mem (m : ℕ) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) :
    0 ≤ cellMap m v ∧ cellMap m v ≤ v := by
  induction m with
  | zero => simpa [cellMap] using h0
  | succ m ih =>
    have he : cellMap (m + 1) v = sinStep (cellMap m v) := by
      simp only [cellMap]; rw [Function.iterate_succ_apply']
    rw [he]
    have := sinStep_mem ih.1 (ih.2.trans h1)
    exact ⟨this.1, this.2.trans ih.2⟩

/-- For `|v| ≤ 1/2`: `|Φ_m v| ≤ |v|` and `|Φ_m v - v| ≤ |v|` (`Φ_m v` lies between `0` and
`v`). -/
theorem abs_cellMap_le (m : ℕ) {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |cellMap m v| ≤ |v| ∧ |cellMap m v - v| ≤ |v| := by
  rcases le_total 0 v with h | h
  · obtain ⟨a, b⟩ := cellMap_mem m h (by simpa [abs_of_nonneg h] using hv)
    rw [abs_of_nonneg h, abs_of_nonneg a, abs_of_nonpos (by linarith)]
    constructor <;> linarith
  · have h' : 0 ≤ -v := by linarith
    obtain ⟨a, b⟩ := cellMap_mem m h' (by simpa [abs_of_nonpos h] using hv)
    rw [cellMap_neg] at a b
    rw [abs_of_nonpos h, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    constructor <;> linarith

/-- `Φ_m(u) = round(u) + Φ_m(u - round u)`. -/
theorem cellMap_eq_round (m : ℕ) (u : ℝ) :
    cellMap m u = round u + cellMap m (u - round u) := by
  rw [add_comm, ← cellMap_add_int, sub_add_cancel]

/-- **Uniform displacement bound.** `|Φ_m(u) - u| ≤ 1/2` for all `u` and `m`. -/
theorem abs_cellMap_sub_le (m : ℕ) (u : ℝ) : |cellMap m u - u| ≤ 1 / 2 := by
  have hv := abs_sub_round u
  have := (abs_cellMap_le m hv).2
  rw [cellMap_eq_round]
  calc |(round u : ℝ) + cellMap m (u - round u) - u|
      = |cellMap m (u - round u) - (u - round u)| := by ring_nf
    _ ≤ 1 / 2 := this.trans hv

/-- For `0 ≤ v < 1/2`, `Φ_m(v) → 0` as `m → ∞` (monotone convergence to the only fixed point
of `ψ` in `[0, 1/2)`). -/
theorem tendsto_cellMap_of_nonneg {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1 / 2) :
    Tendsto (fun m => cellMap m v) atTop (𝓝 0) := by
  have hmem := fun m => cellMap_mem m h0 h1.le
  have hsucc : ∀ m, cellMap (m + 1) v = sinStep (cellMap m v) := fun m => by
    simp only [cellMap]; rw [Function.iterate_succ_apply']
  have hanti : Antitone fun m => cellMap m v := by
    refine antitone_nat_of_succ_le fun m => ?_
    rw [hsucc]
    exact (sinStep_mem (hmem m).1 ((hmem m).2.trans h1.le)).2
  have hbdd : BddBelow (Set.range fun m => cellMap m v) := ⟨0, by
    rintro _ ⟨m, rfl⟩; exact (hmem m).1⟩
  set L := ⨅ m, cellMap m v
  have hT : Tendsto (fun m => cellMap m v) atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hL0 : 0 ≤ L := le_ciInf fun m => (hmem m).1
  have hL1 : L ≤ v := (ciInf_le hbdd 0).trans (by simp [cellMap])
  have hfix : sinStep L = L := by
    have h1 : Tendsto (fun m => cellMap (m + 1) v) atTop (𝓝 L) :=
      hT.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun m => cellMap (m + 1) v) atTop (𝓝 (sinStep L)) := by
      simp_rw [hsucc]
      exact (contDiff_sinStep.continuous.tendsto L).comp hT
    exact tendsto_nhds_unique h2 h1
  have hsin : Real.sin (2 * Real.pi * L) = 0 := by
    unfold sinStep at hfix
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : Real.sin (2 * Real.pi * L) / (2 * Real.pi) = 0 := by linarith
    simpa [hpi] using this
  have hL : L = 0 := by
    by_contra hne
    have hpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
    have : 0 < Real.sin (2 * Real.pi * L) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    linarith
  rwa [hL] at hT

/-- For `|v| < 1/2` and `r > 0` there is `m` with `|Φ_m v| ≤ r`. -/
theorem exists_abs_cellMap_le {v : ℝ} (hv : |v| < 1 / 2) {r : ℝ} (hr : 0 < r) :
    ∃ m, |cellMap m v| ≤ r := by
  have h0 : 0 ≤ |v| := abs_nonneg v
  obtain ⟨m, hm⟩ := ((tendsto_cellMap_of_nonneg h0 hv).eventually
    (Metric.closedBall_mem_nhds 0 hr)).exists
  refine ⟨m, ?_⟩
  rcases le_total 0 v with h | h
  · simpa [abs_of_nonneg h, Real.dist_eq] using hm
  · have : cellMap m |v| = -cellMap m v := by rw [abs_of_nonpos h, cellMap_neg]
    rw [this, Real.dist_eq] at hm
    simpa [abs_neg] using hm


/-- `ψ'(u) = 1 - cos(2πu)`. -/
theorem hasDerivAt_sinStep (u : ℝ) :
    HasDerivAt sinStep (1 - Real.cos (2 * Real.pi * u)) u := by
  have h1 : HasDerivAt (fun u : ℝ => 2 * Real.pi * u) (2 * Real.pi) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * Real.pi)
  have h2 := ((Real.hasDerivAt_sin _).comp u h1).div_const (2 * Real.pi)
  have h3 := (hasDerivAt_id u).sub h2
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  convert h3 using 1
  · funext x; simp [sinStep]
  · field_simp

/-- `ψ` is `2`-Lipschitz (`|ψ'| ≤ 2`). -/
theorem lipschitzWith_sinStep : LipschitzWith 2 sinStep := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun u => (hasDerivAt_sinStep u).differentiableAt)
    fun u => ?_
  rw [(hasDerivAt_sinStep u).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  have := Real.neg_one_le_cos (2 * Real.pi * u)
  have := Real.cos_le_one (2 * Real.pi * u)
  rw [abs_le]; push_cast; constructor <;> linarith

/-- `Φ_m` is `2^m`-Lipschitz. -/
theorem lipschitzWith_cellMap (m : ℕ) : LipschitzWith (2 ^ m) (cellMap m) :=
  lipschitzWith_sinStep.iterate m

/-- `1/2` is a fixed point of `ψ`. -/
theorem sinStep_half : sinStep (1 / 2) = 1 / 2 := by
  unfold sinStep
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.sin_pi]; simp

/-- At the repelling fixed point `1/2`, `Φ_m'(1/2) = 2^m`; hence the Lipschitz constant of
`Φ_m` is exactly `2^m`. -/
theorem hasDerivAt_cellMap_half (m : ℕ) : HasDerivAt (cellMap m) (2 ^ m) (1 / 2) := by
  have h := hasDerivAt_sinStep (1 / 2)
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi] at h
  norm_num at h
  exact HasDerivAt.iterate (1 / 2) h sinStep_half m

end FormalizeSampling.DiffusionODESmooth
