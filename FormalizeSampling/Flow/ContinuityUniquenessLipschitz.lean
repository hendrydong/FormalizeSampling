module

public import FormalizeSampling.Flow.ContinuityUniquenessAffine

/-!
# Approximate duality and backward Euler test functions for the weak continuity equation

Status: **Verified.** The common toolkit of the Euler duality proofs of the named
PDE-uniqueness input `NoiseScore.UniqueWeakContinuity v` of FL-5
(`Flow/NoiseScoreEquivalence.lean`) for nonlinear velocities `v : ℝ → ℝᵈ → ℝᵈ`. The uniqueness
theorems themselves are in `Flow/ContinuityUniquenessLocal.lean` (locally Lipschitz velocities
of linear growth, with the globally Lipschitz and `C³` cases as corollaries).

## Method (approximate duality with backward Euler test functions)

Mathlib v4.35 has no smooth (or even `C¹`) dependence of ODE flows on initial data, so the dual
solution `φ ∘ X_{s→T}` of the affine proof (`Flow/ContinuityUniquenessAffine.lean`) is not
available. Instead the backward transport equation `∂ₛψ + v_s ⬝ ∇ψ = 0` is solved only
approximately, by explicit Euler steps with frozen velocity, which are smooth in `x` for free:

1. `abs_integral_sub_le_of_approx_dual`: the duality step of `integral_eq_of_dual` with an
   error term: if `|∂ₛψ + v_s ⬝ ∇ψ| ≤ δ` on `[a, b] × ℝᵈ` then
   `|∫ ψ(b) dρ_b - ∫ ψ(a) dρ_a| ≤ δ (b - a)` for every solution `ρ`.
2. `eulerBack`: for a `C³` Euler velocity `w`, iterate `Ψ_0 = φ`,
   `Ψ_{j+1}(x) = Ψ_j(x + h w_{T - j h}(x))`. Uniformly in the number of steps `N = T / h`:
   `Ψ_j` is `C³` (`contDiff_eulerBack`), `‖DΨ_j‖ ≤ (1 + hL)^j ‖Dφ‖ ≤ e^{LT} ‖Dφ‖` when
   `‖Dw‖ ≤ L` (`norm_fderiv_eulerBack_le`), and all supports stay in one ball of radius
   `(R + c) e^{2AT}` when `‖w_t(x)‖ ≤ A (‖x‖ + c)` and `hA ≤ 1/2` (`eulerBack_eq_zero`).
3. Elementary estimates for the telescoping: `exp_neg_le_pow_one_sub`, `pow_one_add_le_exp`,
   `one_sub_mul_le_norm_add_smul`.

The one-step estimate and the telescoping are `abs_integral_eulerStep_le_of_approx`
(`Flow/ContinuityUniquenessMollified.lean`) and
`abs_integral_sub_integral_eulerBack_le_of_localApprox` (`Flow/ContinuityUniquenessLocal.lean`).
Only the half-line form of `WeakContinuity2` is used (derivatives within `[a, b] ⊆ [0, ∞)`).

## Main results

* `abs_integral_sub_le_of_approx_dual`: approximate duality (any `v`).
* `eulerBack`, `contDiff_eulerBack`, `eulerBack_eq_zero`, `norm_fderiv_eulerBack_le`.

## Not proved here

* No uniqueness theorem is stated here (see `Flow/ContinuityUniquenessLocal.lean`); no flow
  map is constructed, and nothing about (smooth) dependence of ODE flows on initial data,
  which Mathlib v4.35 lacks.
-/

@[expose] public section

open MeasureTheory Matrix Set Filter Topology Metric Asymptotics

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- **Approximate duality step for `WeakContinuity2` (Verified).** Let `ρ` be a curve of
probability measures on `t ≥ 0` solving `WeakContinuity2 ρ v`, and `0 ≤ a ≤ b`. Let
`ψ, g : ℝ → ℝᵈ → ℝ` with `g s x = ∂ₛψ(s, x)` for all `s, x`, `g` jointly continuous, `ψ s` and
`g s` `C²_c` for `s ∈ [a, b]` with the supports of `g s` in one compact `K`, and `v s`
continuous for `s ∈ [a, b]`. If the transport residual satisfies
`|∂ₛψ(s, x) + v_s(x) ⬝ ∇ψ(s, x)| ≤ δ` for `s ∈ [a, b]` and all `x`, then
`|∫ ψ(b) dρ_b - ∫ ψ(a) dρ_a| ≤ δ (b - a)`. (With `δ = 0`, `a = 0` this is
`integral_eq_of_dual`; same proof, plus the mean value inequality.) -/
theorem abs_integral_sub_le_of_approx_dual {ρ : ℝ → Measure (Fin d → ℝ)}
    {v : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (ρ t)) (hρ : WeakContinuity2 ρ v)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {ψ g : ℝ → (Fin d → ℝ) → ℝ}
    (hψ : ∀ s ∈ Icc a b, TestFunction2 (ψ s)) (hg : ∀ s ∈ Icc a b, TestFunction2 (g s))
    (hd : ∀ s x, HasDerivAt (fun u => ψ u x) (g s x) s)
    (hgc : Continuous (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hgK : ∀ s ∈ Icc a b, ∀ x ∉ K, g s x = 0)
    (hvc : ∀ s ∈ Icc a b, Continuous (v s)) {δ : ℝ}
    (hres : ∀ s ∈ Icc a b, ∀ x, |g s x + v s x ⬝ᵥ grad (ψ s) x| ≤ δ) :
    |∫ x, ψ b x ∂(ρ b) - ∫ x, ψ a x ∂(ρ a)| ≤ δ * (b - a) := by
  set G : ℝ → ℝ := fun s => ∫ x, ψ s x ∂(ρ s) with hG
  set D : ℝ → ℝ := fun s => ∫ x, g s x ∂(ρ s) + ∫ x, v s x ⬝ᵥ grad (ψ s) x ∂(ρ s) with hD
  have hint : ∀ r, 0 ≤ r → ∀ f : (Fin d → ℝ) → ℝ, TestFunction2 f → Integrable f (ρ r) := by
    intro r hr f hf
    have := hprob r hr
    exact hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hderiv : ∀ s ∈ Icc a b, HasDerivWithinAt G (D s) (Icc a b) s := by
    intro s hs
    have hs0 : 0 ≤ s := ha.trans hs.1
    have hsub : Icc a b ⊆ Ici 0 := fun r hr => ha.trans hr.1
    set L := 𝓝[Icc a b] s
    have hmem : ∀ᶠ r in L, r ∈ Icc a b := self_mem_nhdsWithin
    set E1 : ℝ → ℝ := fun r => ∫ x, (ψ r x - ψ s x - (r - s) * g s x) ∂(ρ r)
    set E2 : ℝ → ℝ := fun r => (r - s) * (∫ x, g s x ∂(ρ r) - ∫ x, g s x ∂(ρ s))
    set E3 : ℝ → ℝ := fun r => ∫ x, ψ s x ∂(ρ r) - ∫ x, ψ s x ∂(ρ s) -
      (r - s) • ∫ x, v s x ⬝ᵥ grad (ψ s) x ∂(ρ s)
    have h3 : E3 =o[L] fun r => r - s :=
      hasDerivWithinAt_iff_isLittleO.1 ((hρ (ψ s) (hψ s hs) s hs0).mono hsub)
    have h2 : E2 =o[L] fun r => r - s := by
      have ht : Tendsto (fun r => ∫ x, g s x ∂(ρ r) - ∫ x, g s x ∂(ρ s)) L (𝓝 0) := by
        have hc := ((hρ (g s) (hg s hs) s hs0).continuousWithinAt).mono hsub
        simpa using hc.tendsto.sub_const (∫ x, g s x ∂(ρ s))
      have := (isBigO_refl (fun r => r - s) L).mul_isLittleO (isLittleO_one_iff ℝ |>.2 ht)
      simpa using this
    have h1 : E1 =o[L] fun r => r - s := by
      rw [isLittleO_iff]
      intro ε hε
      have huc : UniformContinuousOn (fun q : ℝ × (Fin d → ℝ) => g q.1 q.2) (Icc a b ×ˢ K) :=
        (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hgc.continuousOn
      obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
      have hbd : ∀ u ∈ Icc a b ∩ ball s δ, ∀ x, ‖g u x - g s x‖ ≤ ε := by
        intro u hu x
        by_cases hx : x ∈ K
        · have := hδu (u, x) ⟨hu.1, hx⟩ (s, x) ⟨hs, hx⟩ (by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hu.2)
          rw [← dist_eq_norm]; exact this.le
        · rw [hgK u hu.1 x hx, hgK s hs x hx, sub_self, norm_zero]; exact hε.le
      filter_upwards [hmem, inter_mem_nhdsWithin (Icc a b) (ball_mem_nhds s hδ)] with r hr hrb
      have := hprob r (ha.trans hr.1)
      have hpt : ∀ x, ‖ψ r x - ψ s x - (r - s) * g s x‖ ≤ ε * ‖r - s‖ := by
        intro x
        have hcvx : Convex ℝ (Icc a b ∩ ball s δ) := (convex_Icc a b).inter (convex_ball s δ)
        have := hcvx.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun u => ψ u x - u * g s x) (f' := fun u => g u x - g s x)
          (fun u _ => (((hd u x).sub ((hasDerivAt_id u).mul_const (g s x))).congr_deriv
            (by simp)).hasDerivWithinAt) (hbd · · x) ⟨hs, mem_ball_self hδ⟩ hrb
        convert this using 2
        ring
      calc ‖E1 r‖ ≤ ε * ‖r - s‖ * (ρ r).real univ :=
            norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
        _ = ε * ‖r - s‖ := by simp
    have hsum : ∀ᶠ r in L, G r - G s - (r - s) • D s = E1 r + E2 r + E3 r := by
      filter_upwards [hmem] with r hr
      have hE1 : E1 r = ∫ x, ψ r x ∂(ρ r) - ∫ x, ψ s x ∂(ρ r) - (r - s) * ∫ x, g s x ∂(ρ r) := by
        have i1 := hint r (ha.trans hr.1) _ (hψ r hr)
        have i2 := hint r (ha.trans hr.1) _ (hψ s hs)
        have i3 := (hint r (ha.trans hr.1) _ (hg s hs)).const_mul (r - s)
        have i12 : Integrable (fun x => ψ r x - ψ s x) (ρ r) := i1.sub i2
        simp only [E1]
        rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul]
      simp only [E2, E3, hE1, hG, hD, smul_eq_mul]
      ring
    have := ((h1.add h2).add h3).congr' (hsum.mono fun r hr => hr.symm) EventuallyEq.rfl
    exact hasDerivWithinAt_iff_isLittleO.2 this
  have hbound : ∀ s ∈ Ico a b, ‖D s‖ ≤ δ := by
    intro s hs
    have hs' : s ∈ Icc a b := Ico_subset_Icc_self hs
    have := hprob s (ha.trans hs.1)
    have hψ1 : ContDiff ℝ 1 (ψ s) := (hψ s hs').1.of_le (by norm_num)
    have hvg : Integrable (fun x => v s x ⬝ᵥ grad (ψ s) x) (ρ s) := by
      have hc : Continuous (fun x => fderiv ℝ (ψ s) x (v s x)) :=
        (hψ1.continuous_fderiv (by norm_num)).clm_apply (hvc s hs')
      have hcs : HasCompactSupport (fun x => fderiv ℝ (ψ s) x (v s x)) :=
        HasCompactSupport.intro (hψ s hs').2.isCompact fun x hx => by
          simp [fderiv_of_notMem_tsupport ℝ hx]
      simpa only [dotProduct_grad] using hc.integrable_of_hasCompactSupport hcs
    have hgi := hint s (ha.trans hs.1) _ (hg s hs')
    simp only [D]
    rw [← integral_add hgi hvg, Real.norm_eq_abs]
    calc |∫ x, (g s x + v s x ⬝ᵥ grad (ψ s) x) ∂(ρ s)|
        ≤ δ * (ρ s).real univ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le_const
            (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hres s hs' x)
      _ = δ := by simp
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨hab, le_rfl⟩
  simpa [G, Real.norm_eq_abs] using this

/-! ### Elementary estimates -/

/-- `e^{-2x} ≤ 1 - x` for `0 ≤ x ≤ 1/2`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h1 : 2 * x + 1 ≤ Real.exp (2 * x) := Real.add_one_le_exp _
  have h2 : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  nlinarith

/-- `e^{-2LT} ≤ (1 - hL)^j` if `h, L ≥ 0`, `hL ≤ 1/2` and `j h ≤ T`. -/
theorem exp_neg_le_pow_one_sub {h L T : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) (hhL : h * L ≤ 1 / 2)
    {j : ℕ} (hj : j * h ≤ T) : Real.exp (-(2 * L * T)) ≤ (1 - h * L) ^ j := by
  calc Real.exp (-(2 * L * T)) ≤ Real.exp (-(2 * (h * L))) ^ j := by
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.2 (by nlinarith)
    _ ≤ (1 - h * L) ^ j :=
        pow_le_pow_left₀ (Real.exp_pos _).le
          (exp_neg_two_mul_le_one_sub (mul_nonneg hh hL) hhL) j

/-- `(1 + hL)^j ≤ e^{LT}` if `h, L ≥ 0` and `j h ≤ T`. -/
theorem pow_one_add_le_exp {h L T : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {j : ℕ} (hj : j * h ≤ T) :
    (1 + h * L) ^ j ≤ Real.exp (L * T) := by
  calc (1 + h * L) ^ j ≤ Real.exp (h * L) ^ j :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (h * L)]) j
    _ = Real.exp (j * (h * L)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (L * T) := Real.exp_le_exp.2 (by nlinarith)

/-- If `‖w x‖ ≤ L (‖x‖ + c)` and `τ ≥ 0`, then `(1 - τ L)(‖x‖ + c) ≤ ‖x + τ w(x)‖ + c`. -/
theorem one_sub_mul_le_norm_add_smul {w : (Fin d → ℝ) → Fin d → ℝ} {L c τ : ℝ}
    (hτ : 0 ≤ τ) (x : Fin d → ℝ) (hw : ‖w x‖ ≤ L * (‖x‖ + c)) :
    (1 - τ * L) * (‖x‖ + c) ≤ ‖x + τ • w x‖ + c := by
  have h1 : ‖x‖ ≤ ‖x + τ • w x‖ + ‖τ • w x‖ := by
    simpa using norm_sub_le (x + τ • w x) (τ • w x)
  rw [norm_smul, Real.norm_of_nonneg hτ] at h1
  nlinarith

/-! ### Backward Euler approximations of the dual solution -/

/-- **Backward Euler test functions.** For a velocity `v`, final time `T`, step `h` and final
test function `φ`, `eulerBack v T h φ j` approximates `φ ∘ X_{T - j h → T}`:
`eulerBack 0 = φ` and `eulerBack (j + 1) x = eulerBack j (x + h v_{T - j h}(x))`, i.e. one
explicit Euler step of `ẋ = v_t(x)` from time `T - (j + 1) h` to `T - j h` (with the velocity
frozen at the later time). -/
noncomputable def eulerBack (v : ℝ → (Fin d → ℝ) → Fin d → ℝ) (T h : ℝ)
    (φ : (Fin d → ℝ) → ℝ) : ℕ → (Fin d → ℝ) → ℝ
  | 0 => φ
  | j + 1 => fun x => eulerBack v T h φ j (x + h • v (T - j * h) x)

section Euler

variable {v : ℝ → (Fin d → ℝ) → Fin d → ℝ} {T h : ℝ} {φ : (Fin d → ℝ) → ℝ} {N : ℕ}

/-- The Euler times `T - j h`, `j ≤ N`, lie in `[0, T]` when `N h = T`, `h ≥ 0`. -/
theorem sub_mul_mem_Icc (hh : 0 ≤ h) (hNh : (N : ℝ) * h = T) {j : ℕ} (hj : j ≤ N) :
    T - j * h ∈ Icc 0 T := by
  have : (j : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- The backward Euler test functions are `C³` if `φ` and the velocities `v_t`, `t ∈ [0, T]`,
are. -/
theorem contDiff_eulerBack (hh : 0 ≤ h) (hNh : (N : ℝ) * h = T)
    (hv : ∀ t ∈ Icc 0 T, ContDiff ℝ 3 (v t)) (hφ : ContDiff ℝ 3 φ) :
    ∀ j ≤ N, ContDiff ℝ 3 (eulerBack v T h φ j)
  | 0, _ => hφ
  | j + 1, hj => by
      have ih := contDiff_eulerBack hh hNh hv hφ j (by omega)
      exact ih.comp (contDiff_id.add
        ((hv _ (sub_mul_mem_Icc hh hNh (by omega : j ≤ N))).const_smul h))

/-- Support of the backward Euler test functions: if `φ` vanishes for `‖x‖ > R` and
`‖v_t(x)‖ ≤ L (‖x‖ + c)` on `[0, T]`, then `eulerBack j x = 0` whenever
`R + c < (‖x‖ + c) (1 - hL)^j`. -/
theorem eulerBack_eq_zero (hh : 0 ≤ h) (hNh : (N : ℝ) * h = T) {L c R : ℝ} (hc : 0 ≤ c)
    (hhL : h * L ≤ 1) (hgr : ∀ t ∈ Icc 0 T, ∀ x, ‖v t x‖ ≤ L * (‖x‖ + c))
    (hφR : ∀ x, R < ‖x‖ → φ x = 0) :
    ∀ j ≤ N, ∀ x, R + c < (‖x‖ + c) * (1 - h * L) ^ j → eulerBack v T h φ j x = 0
  | 0, _, x, hx => hφR x (by simpa using hx)
  | j + 1, hj, x, hx => by
      have ih := eulerBack_eq_zero hh hNh hc hhL hgr hφR j (by omega)
      refine ih _ ?_
      have h1 := one_sub_mul_le_norm_add_smul (w := v (T - j * h)) hh x
        (hgr _ (sub_mul_mem_Icc hh hNh (by omega : j ≤ N)) x)
      have hq : 0 ≤ (1 - h * L) ^ j := pow_nonneg (by linarith) j
      calc R + c < (‖x‖ + c) * (1 - h * L) ^ (j + 1) := hx
        _ = (1 - h * L) * (‖x‖ + c) * (1 - h * L) ^ j := by ring
        _ ≤ (‖x + h • v (T - j * h) x‖ + c) * (1 - h * L) ^ j :=
          mul_le_mul_of_nonneg_right h1 hq

/-- Gradient bound for the backward Euler test functions:
`‖D eulerBack j‖ ≤ (1 + hL)^j G` if `‖Dφ‖ ≤ G` and `‖D v_t‖ ≤ L` on `[0, T]`. -/
theorem norm_fderiv_eulerBack_le (hh : 0 ≤ h) (hNh : (N : ℝ) * h = T)
    (hv : ∀ t ∈ Icc 0 T, ContDiff ℝ 3 (v t)) (hφ : ContDiff ℝ 3 φ) {L G : ℝ}
    (hL : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (v t) x‖ ≤ L) (hG : ∀ x, ‖fderiv ℝ φ x‖ ≤ G) :
    ∀ j ≤ N, ∀ x, ‖fderiv ℝ (eulerBack v T h φ j) x‖ ≤ (1 + h * L) ^ j * G
  | 0, _, x => by simpa [eulerBack] using hG x
  | j + 1, hj, x => by
      have hj' : j ≤ N := by omega
      have ih := norm_fderiv_eulerBack_le hh hNh hv hφ hL hG j hj'
      have hmem := sub_mul_mem_Icc hh hNh hj'
      have hE := contDiff_eulerBack hh hNh hv hφ j hj'
      have hwd : DifferentiableAt ℝ (v (T - j * h)) x :=
        ((hv _ hmem).differentiable (by norm_num)) x
      have hY : HasFDerivAt (fun x : Fin d → ℝ => x + h • v (T - j * h) x)
          (ContinuousLinearMap.id ℝ (Fin d → ℝ) + h • fderiv ℝ (v (T - j * h)) x) x :=
        (hasFDerivAt_id x).add (hwd.hasFDerivAt.const_smul h)
      have hF : fderiv ℝ (eulerBack v T h φ (j + 1)) x =
          (fderiv ℝ (eulerBack v T h φ j) (x + h • v (T - j * h) x)).comp
            (ContinuousLinearMap.id ℝ (Fin d → ℝ) + h • fderiv ℝ (v (T - j * h)) x) :=
        ((hE.differentiable (by norm_num) _).hasFDerivAt.comp x hY).fderiv
      have hA : ‖ContinuousLinearMap.id ℝ (Fin d → ℝ) + h • fderiv ℝ (v (T - j * h)) x‖ ≤
          1 + h * L := by
        refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le) ?_)
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left (hL _ hmem x) hh
      have hG0 : 0 ≤ (1 + h * L) ^ j * G :=
        (norm_nonneg _).trans (ih (x + h • v (T - j * h) x))
      rw [hF]
      calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (1 + h * L) ^ j * G * (1 + h * L) :=
          mul_le_mul (ih _) hA (norm_nonneg _) hG0
        _ = (1 + h * L) ^ (j + 1) * G := by ring

end Euler

end NoiseScore
end FormalizeSampling
