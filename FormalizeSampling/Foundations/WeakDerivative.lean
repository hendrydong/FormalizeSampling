module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Weak partial derivatives on `Fin d → ℝ`, mollification, and `W^{1,∞}` = Lipschitz

Status: **Verified.** Minimal Sobolev infrastructure on the state space `Fin d → ℝ` (Lebesgue
`volume`), built directly on test-function integration by parts rather than on Mathlib's
distribution API (which does not provide `W^{1,p}_loc` as a space of functions).

## Definitions

* `HasWeakPartialDeriv u i g`: `u, g` are locally integrable and
  `∫ u ∂ᵢφ = -∫ g φ` for every `φ ∈ C_c^∞(ℝᵈ)`.
* `HasWeakJacobian v Dv`: every component `v_j` of a vector field has weak partial derivatives
  `∂ᵢ v_j = Dv · j i` (so `v ∈ W^{1,1}_loc` with weak Jacobian `Dv`).
* `weakDiv Dv x = ∑ᵢ Dv x i i`, the weak divergence.
* `MemW11locBddDiv v`: `v ∈ W^{1,1}_loc` and its weak divergence is essentially bounded
  (the DiPerna–Lions class, without the growth condition).

## Main results

* `hasWeakPartialDeriv_of_contDiff`: a `C¹` function has its classical partial derivative as
  weak partial derivative (consistency of the definition).
* `HasWeakPartialDeriv.ae_eq`: weak partial derivatives are unique almost everywhere.
* `HasWeakPartialDeriv.fderiv_convolution_apply`: for a smooth compactly supported kernel `κ`,
  `∂ᵢ (κ ⋆ u) = κ ⋆ ∂ᵢ u` **pointwise** (the mollification commutes with weak derivatives);
  `κ ⋆ u` is smooth by Mathlib's `HasCompactSupport.contDiff_convolution_left`.
* `abs_convolution_le_of_ae_bound`: `|κ ⋆ g| ≤ G` for a probability kernel and `|g| ≤ G` a.e.
* `mollBump`, `tendsto_mollBump_rOut`: a standard mollifier sequence (radii `1/(n+1)`,
  `2/(n+1)`), along which `κ_n ⋆ u → u` a.e. for locally integrable `u` (Lebesgue
  differentiation, Mathlib's `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`).
* `exists_lipschitzWith_ae_eq_of_hasWeakPartialDeriv`: **`W^{1,∞}` ⊆ Lipschitz.** A locally
  integrable `u` whose weak partial derivatives satisfy `|∂ᵢ u| ≤ G` a.e. has a
  `(d G)`-Lipschitz representative.
* `exists_lipschitzWith_ae_eq_of_hasWeakJacobian`: the same for vector fields.
* `exists_locallyLipschitz_ae_eq_of_hasWeakPartialDeriv`,
  `exists_locallyLipschitz_ae_eq_of_hasWeakJacobian`: **`W^{1,∞}_loc` ⊆ locally Lipschitz**
  (continuous representative, Lipschitz on every ball), via
  `exists_locallyLipschitz_of_tendsto_of_dense` (locally equi-Lipschitz sequences converging
  on a dense set converge everywhere).
* `exists_lipschitzWith_ae_eq_of_weakDiv_le_one_dim`: in dimension one, a `W^{1,1}_loc` field
  with essentially bounded weak divergence (`= v'`) has a Lipschitz representative.

## Not proved here

* `L¹_loc` (as opposed to a.e.) convergence `κ_ε ⋆ u → u`, and density of `C^∞` in
  `W^{1,1}_loc` (the Meyers–Serrin/Friedrichs approximation `κ_ε ⋆ v → v` in `W^{1,1}_loc`).
* Anything about `W^{1,p}` norms, traces, Sobolev embeddings, or chain rules.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff Convolution NNReal

namespace FormalizeSampling

variable {d : ℕ}

/-- **Weak partial derivative.** `g` is a weak `i`-th partial derivative of `u` on `ℝᵈ` if both
are locally integrable (Lebesgue measure) and `∫ u ∂ᵢφ = -∫ g φ` for every smooth compactly
supported test function `φ`. -/
def HasWeakPartialDeriv (u : (Fin d → ℝ) → ℝ) (i : Fin d) (g : (Fin d → ℝ) → ℝ) : Prop :=
  LocallyIntegrable u ∧ LocallyIntegrable g ∧
    ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, u x * partialDeriv i φ x = -∫ x, g x * φ x

/-- **Weak Jacobian (`W^{1,1}_loc` vector fields).** `Dv x j i` is a weak partial derivative
`∂ᵢ v_j` of the `j`-th component of `v`, for all `i, j`. -/
def HasWeakJacobian (v : (Fin d → ℝ) → Fin d → ℝ) (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) :
    Prop :=
  ∀ j i, HasWeakPartialDeriv (fun x => v x j) i (fun x => Dv x j i)

/-- The **weak divergence** `∑ᵢ ∂ᵢ vᵢ` computed from a weak Jacobian `Dv`. -/
def weakDiv (Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, Dv x i i

/-- **The DiPerna–Lions velocity class (without growth condition):** `v ∈ W^{1,1}_loc` has a
weak Jacobian whose weak divergence is essentially bounded. -/
def MemW11locBddDiv (v : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∃ Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ, HasWeakJacobian v Dv ∧
    ∃ C : ℝ, ∀ᵐ x, |weakDiv Dv x| ≤ C

/-- **Smooth functions (Verified).** If `u` is `C¹`, then its classical partial derivative
`∂ᵢ u` is a weak `i`-th partial derivative of `u`. -/
theorem hasWeakPartialDeriv_of_contDiff {u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (i : Fin d) : HasWeakPartialDeriv u i (partialDeriv i u) := by
  have hcd : Continuous (partialDeriv i u) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨hu.continuous.locallyIntegrable, hcd.locallyIntegrable, fun φ hφ hφc => ?_⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hpφ : Continuous (partialDeriv i φ) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpc : HasCompactSupport (partialDeriv i φ) :=
    (hφc.fderiv ℝ).mono' fun x hx => by
      contrapose! hx
      simp [partialDeriv, image_eq_zero_of_notMem_tsupport hx]
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := u)
    (g := φ) (v := Pi.single i 1)
    ((hcd.mul hφ1.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    ((hu.continuous.mul hpφ).integrable_of_hasCompactSupport hpc.mul_left)
    ((hu.continuous.mul hφ1.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hu.differentiable one_ne_zero) x) (fun x _ => (hφ1.differentiable one_ne_zero) x)
  exact h

/-- **Uniqueness of weak derivatives (Verified).** Two weak `i`-th partial derivatives of the
same function agree almost everywhere. -/
theorem HasWeakPartialDeriv.ae_eq {u g g' : (Fin d → ℝ) → ℝ} {i : Fin d}
    (h : HasWeakPartialDeriv u i g) (h' : HasWeakPartialDeriv u i g') : g =ᵐ[volume] g' := by
  have hz : ∀ᵐ x, (g - g') x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (h.2.1.sub h'.2.1) fun φ hφ hφc => ?_
    have e1 := h.2.2 φ hφ hφc
    have e2 := h'.2.2 φ hφ hφc
    have i1 : Integrable fun x => g x * φ x := by
      simpa [mul_comm] using h.2.1.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have i2 : Integrable fun x => g' x * φ x := by
      simpa [mul_comm] using h'.2.1.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub (by simpa [mul_comm] using i1) (by simpa [mul_comm] using i2)]
    simp_rw [mul_comm (φ _)]
    linarith
  filter_upwards [hz] with x hx using sub_eq_zero.1 hx

/-- **Mollification commutes with weak derivatives (Verified).** If `g` is a weak `i`-th
partial derivative of `u` and `κ` is smooth with compact support, then the convolution
`(κ ⋆ u)(x) = ∫ κ(x - y) u(y) dy` (which is smooth) satisfies `∂ᵢ (κ ⋆ u) = κ ⋆ g`
pointwise. -/
theorem HasWeakPartialDeriv.fderiv_convolution_apply {u g : (Fin d → ℝ) → ℝ} {i : Fin d}
    (h : HasWeakPartialDeriv u i g) {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hκc : HasCompactSupport κ) (x : Fin d → ℝ) :
    fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x (Pi.single i 1) =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hd := hκc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hκ.of_le (by simp)) h.1 x
  rw [hd.fderiv, convolution_eq_swap, convolution_lsmul_swap]
  have hex := (hκc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Fin d → ℝ))
    (hκ.continuous_fderiv (by simp)) h.1 x
  rw [ContinuousLinearMap.integral_apply hex.integrable_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  set ψ : (Fin d → ℝ) → ℝ := fun y => κ (x - y) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hκc.comp_homeomorph (Homeomorph.subLeft x)
  have hDψ : ∀ y, partialDeriv i ψ y = -fderiv ℝ κ (x - y) (Pi.single i 1) := by
    intro y
    have h1 : HasFDerivAt (fun y : Fin d → ℝ => x - y)
        (-ContinuousLinearMap.id ℝ (Fin d → ℝ)) y := by
      simpa using (hasFDerivAt_const x y).sub (hasFDerivAt_id (𝕜 := ℝ) y)
    have h2 := ((hκ.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    rw [partialDeriv, show ψ = κ ∘ HSub.hSub x from rfl, h2.fderiv]
    simp
  have hw := h.2.2 ψ hψs hψc
  simp only [hDψ, mul_neg, integral_neg, neg_inj] at hw
  simp only [hψ] at hw
  simp_rw [mul_comm (fderiv ℝ κ _ _), mul_comm (κ _)]
  exact hw

/-- **Mollification of a bounded function (Verified).** If `κ ≥ 0` is integrable with
`∫ κ = 1` and `|g| ≤ G` almost everywhere, then `|(κ ⋆ g)(x)| ≤ G` for every `x`. -/
theorem abs_convolution_le_of_ae_bound {κ g : (Fin d → ℝ) → ℝ} (hκ0 : ∀ x, 0 ≤ κ x)
    (hκi : Integrable κ) (hκ1 : ∫ x, κ x = 1) {G : ℝ} (hg : ∀ᵐ x, |g x| ≤ G)
    (x : Fin d → ℝ) : |(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x| ≤ G := by
  rw [convolution_lsmul_swap, ← Real.norm_eq_abs]
  have hint : Integrable (fun y => G * κ (x - y)) := (hκi.comp_sub_left x).const_mul G
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq ?_)
  · filter_upwards [hg] with y hy
    rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg (hκ0 _), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hy (hκ0 _)
  · rw [integral_const_mul, integral_sub_left_eq_self (fun y => κ y) volume x, hκ1, mul_one]

/-- The `n`-th **standard mollifier bump** on `ℝᵈ`: a `ContDiffBump` centred at `0` with inner
radius `1/(n+1)` and outer radius `2/(n+1)`. Its normalization `(mollBump d n).normed volume`
is a smooth probability kernel supported in the ball of radius `2/(n+1)`. -/
noncomputable def mollBump (d n : ℕ) : ContDiffBump (0 : Fin d → ℝ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

/-- The outer radii of the standard mollifier bumps tend to `0`. -/
theorem tendsto_mollBump_rOut : Tendsto (fun n => (mollBump d n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  simp only [mollBump]; ring

/-- **Mollifications converge almost everywhere (Verified).** For locally integrable `u`,
`(κ_n ⋆ u)(x) → u(x)` for almost every `x`, where `κ_n = (mollBump d n).normed volume`
(Lebesgue differentiation theorem). -/
theorem ae_tendsto_mollBump_convolution {u : (Fin d → ℝ) → ℝ} (hu : LocallyIntegrable u) :
    ∀ᵐ x, Tendsto (fun n => ((mollBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] u) x) atTop (𝓝 (u x)) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (K := 2)
    tendsto_mollBump_rOut (Eventually.of_forall fun n => by simp [mollBump]; ring_nf; rfl) hu

/-- **`W^{1,∞}` functions are Lipschitz (Verified).** Let `u : ℝᵈ → ℝ` be locally integrable
with weak partial derivatives `∂ᵢ u = gᵢ` satisfying `|gᵢ| ≤ G` almost everywhere. Then `u`
agrees almost everywhere with a `(d G)`-Lipschitz function (for the sup norm on `ℝᵈ`).
Proof: the mollifications `κ_n ⋆ u` are smooth with `∂ᵢ (κ_n ⋆ u) = κ_n ⋆ gᵢ`, hence uniformly
`(d G)`-Lipschitz; they converge to `u` on a full-measure set `S`, so `u` is `(d G)`-Lipschitz
on `S`, and McShane's extension gives the representative. -/
theorem exists_lipschitzWith_ae_eq_of_hasWeakPartialDeriv {u : (Fin d → ℝ) → ℝ}
    (hu : LocallyIntegrable u) {g : Fin d → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, HasWeakPartialDeriv u i (g i)) {G : ℝ≥0} (hG : ∀ i, ∀ᵐ x, |g i x| ≤ G) :
    ∃ w : (Fin d → ℝ) → ℝ, LipschitzWith (d * G) w ∧ w =ᵐ[volume] u := by
  set κ : ℕ → (Fin d → ℝ) → ℝ := fun n => (mollBump d n).normed volume with hκ
  set m : ℕ → (Fin d → ℝ) → ℝ := fun n => κ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
    with hm
  have hlip : ∀ n, LipschitzWith (d * G) (m n) := by
    intro n
    have hsm : ContDiff ℝ ∞ (κ n) := (mollBump d n).contDiff_normed
    have hcs : HasCompactSupport (κ n) := (mollBump d n).hasCompactSupport_normed
    have hdiff : Differentiable ℝ (m n) :=
      (hcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1)
        (hsm.of_le (by simp)) hu).differentiable (by simp)
    refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast]
    refine norm_le_of_abs_apply_single_le _ G.2 fun i => ?_
    rw [(hg i).fderiv_convolution_apply hsm hcs x]
    exact abs_convolution_le_of_ae_bound (mollBump d n).nonneg_normed
      (mollBump d n).integrable_normed (mollBump d n).integral_normed (hG i) x
  have hae : ∀ᵐ x, Tendsto (fun n => m n x) atTop (𝓝 (u x)) :=
    ae_tendsto_mollBump_convolution hu
  set S := {x | Tendsto (fun n => m n x) atTop (𝓝 (u x))}
  have hS : LipschitzOnWith (d * G) u S := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    exact le_of_tendsto (hx.dist hy) (Eventually.of_forall fun n => (hlip n).dist_le_mul x y)
  obtain ⟨w, hw, hwS⟩ := hS.extend_real
  refine ⟨w, hw, ?_⟩
  filter_upwards [hae] with x hx using (hwS hx).symm

/-- **`W^{1,∞}` vector fields are Lipschitz (Verified).** If `v : ℝᵈ → ℝᵈ` has a weak
Jacobian `Dv` with `|Dv x j i| ≤ G` almost everywhere for all `i, j`, then `v` agrees almost
everywhere with a `(d G)`-Lipschitz vector field (sup norms). -/
theorem exists_lipschitzWith_ae_eq_of_hasWeakJacobian {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv) {G : ℝ≥0}
    (hG : ∀ j i, ∀ᵐ x, |Dv x j i| ≤ G) :
    ∃ w : (Fin d → ℝ) → Fin d → ℝ, LipschitzWith (d * G) w ∧ w =ᵐ[volume] v := by
  have hex : ∀ j : Fin d, ∃ w : (Fin d → ℝ) → ℝ, LipschitzWith (d * G) w ∧
      w =ᵐ[volume] fun x => v x j := fun j =>
    exists_lipschitzWith_ae_eq_of_hasWeakPartialDeriv (hv j j).1 (hv j) (hG j)
  choose w hwl hwe using hex
  refine ⟨fun x j => w j x, LipschitzWith.of_dist_le_mul fun x y => ?_, ?_⟩
  · exact (dist_pi_le_iff (by positivity)).2 fun j => (hwl j).dist_le_mul x y
  · filter_upwards [ae_all_iff.2 hwe] with x hx
    funext j
    exact hx j

/-- **One-dimensional DiPerna–Lions regularity (Verified).** On `ℝ = Fin 1 → ℝ`, a vector
field `v ∈ W^{1,1}_loc` (weak Jacobian `Dv`) whose weak divergence is essentially bounded,
`|div v| ≤ G` a.e., agrees almost everywhere with a `G`-Lipschitz field: in one dimension the
divergence is the whole derivative `v'`. -/
theorem exists_lipschitzWith_ae_eq_of_weakDiv_le_one_dim {v : (Fin 1 → ℝ) → Fin 1 → ℝ}
    {Dv : (Fin 1 → ℝ) → Fin 1 → Fin 1 → ℝ} (hv : HasWeakJacobian v Dv) {G : ℝ≥0}
    (hG : ∀ᵐ x, |weakDiv Dv x| ≤ G) :
    ∃ w : (Fin 1 → ℝ) → Fin 1 → ℝ, LipschitzWith G w ∧ w =ᵐ[volume] v := by
  have hG' : ∀ j i, ∀ᵐ x, |Dv x j i| ≤ G := by
    intro j i
    filter_upwards [hG] with x hx
    rw [Subsingleton.elim j 0, Subsingleton.elim i 0]
    simpa [weakDiv] using hx
  obtain ⟨w, hw, hwe⟩ := exists_lipschitzWith_ae_eq_of_hasWeakJacobian hv hG'
  exact ⟨w, by simpa using hw, hwe⟩

/-- **The one-dimensional DiPerna–Lions class is the Lipschitz class (Verified).** On
`ℝ = Fin 1 → ℝ`, every `v` with `MemW11locBddDiv v` agrees almost everywhere with a globally
Lipschitz field. -/
theorem MemW11locBddDiv.exists_lipschitzWith_ae_eq_one_dim {v : (Fin 1 → ℝ) → Fin 1 → ℝ}
    (hv : MemW11locBddDiv v) :
    ∃ (K : ℝ≥0) (w : (Fin 1 → ℝ) → Fin 1 → ℝ), LipschitzWith K w ∧ w =ᵐ[volume] v := by
  obtain ⟨Dv, hDv, C, hC⟩ := hv
  obtain ⟨w, hw, hwe⟩ := exists_lipschitzWith_ae_eq_of_weakDiv_le_one_dim hDv
    (G := C.toNNReal) (hC.mono fun x hx => hx.trans (Real.le_coe_toNNReal C))
  exact ⟨_, w, hw, hwe⟩

/-! ### Local versions -/

/-- **Local bound for a mollification (Verified).** If `κ ≥ 0` is integrable with `∫ κ = 1`
and `|g(y)| ≤ G` for almost every `y` with `κ(x - y) ≠ 0`, then `|(κ ⋆ g)(x)| ≤ G`. -/
theorem abs_convolution_le_of_ae_bound_on_support {κ g : (Fin d → ℝ) → ℝ}
    (hκ0 : ∀ x, 0 ≤ κ x) (hκi : Integrable κ) (hκ1 : ∫ x, κ x = 1) {G : ℝ}
    {x : Fin d → ℝ} (hg : ∀ᵐ y, κ (x - y) ≠ 0 → |g y| ≤ G) :
    |(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x| ≤ G := by
  rw [convolution_lsmul_swap, ← Real.norm_eq_abs]
  have hint : Integrable (fun y => G * κ (x - y)) := (hκi.comp_sub_left x).const_mul G
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq ?_)
  · filter_upwards [hg] with y hy
    rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg (hκ0 _), Real.norm_eq_abs, mul_comm]
    by_cases h0 : κ (x - y) = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (hy h0) (hκ0 _)
  · rw [integral_const_mul, integral_sub_left_eq_self (fun y => κ y) volume x, hκ1, mul_one]

/-- **Limits of locally equi-Lipschitz sequences (Verified).** Let `m n : ℝᵈ → ℝ` be
Lipschitz on every closed ball `closedBall 0 R` with a constant `L_R` independent of `n`, and
let `m n x → f x` for `x` in a dense set `S`. Then `m n x` converges for **every** `x`, and the
limit `w` is continuous, Lipschitz with constant `L_R` on each `closedBall 0 R`, and `w = f`
on `S`. -/
theorem exists_locallyLipschitz_of_tendsto_of_dense {m : ℕ → (Fin d → ℝ) → ℝ}
    {f : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} (hS : Dense S)
    (hconv : ∀ x ∈ S, Tendsto (fun n => m n x) atTop (𝓝 (f x)))
    (hlip : ∀ R : ℝ, ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (m n) (closedBall 0 R)) :
    ∃ w : (Fin d → ℝ) → ℝ, Continuous w ∧
      (∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L w (closedBall 0 R)) ∧ EqOn w f S := by
  have hcauchy : ∀ x, CauchySeq fun n => m n x := by
    intro x
    obtain ⟨L, hL⟩ := hlip (‖x‖ + 1)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set δ := min 1 (ε / (4 * ((L : ℝ) + 1))) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    obtain ⟨s, hsS, hsx⟩ := hS.exists_dist_lt x hδ0
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hconv s hsS).cauchySeq (ε / 2) (by positivity)
    refine ⟨N, fun a ha b hb => ?_⟩
    have hxB : x ∈ closedBall (0 : Fin d → ℝ) (‖x‖ + 1) := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have hsB : s ∈ closedBall (0 : Fin d → ℝ) (‖x‖ + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have h1 := norm_le_insert' s x
      rw [← dist_eq_norm, dist_comm] at h1
      linarith [min_le_left 1 (ε / (4 * ((L : ℝ) + 1)))]
    have hLδ : (L : ℝ) * dist x s ≤ ε / 4 := by
      have h1 : dist x s ≤ ε / (4 * ((L : ℝ) + 1)) := hsx.le.trans (min_le_right _ _)
      calc (L : ℝ) * dist x s ≤ ((L : ℝ) + 1) * (ε / (4 * ((L : ℝ) + 1))) :=
            mul_le_mul (by linarith) h1 dist_nonneg (by positivity)
        _ = ε / 4 := by field_simp
    have e1 := (hL a).dist_le_mul x hxB s hsB
    have e2 := (hL b).dist_le_mul s hsB x hxB
    rw [dist_comm s x] at e2
    have e3 := hN a ha b hb
    calc dist (m a x) (m b x) ≤ dist (m a x) (m a s) + dist (m a s) (m b s) +
          dist (m b s) (m b x) := dist_triangle4 _ _ _ _
      _ < ε := by linarith
  have htend : ∀ x, Tendsto (fun n => m n x) atTop (𝓝 (limUnder atTop fun n => m n x)) :=
    fun x => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy x))
  set w : (Fin d → ℝ) → ℝ := fun x => limUnder atTop fun n => m n x with hw
  have hwl : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L w (closedBall 0 R) := by
    intro R
    obtain ⟨L, hL⟩ := hlip R
    refine ⟨L, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    exact le_of_tendsto ((htend x).dist (htend y))
      (Eventually.of_forall fun n => (hL n).dist_le_mul x hx y hy)
  refine ⟨w, continuous_iff_continuousAt.2 fun x => ?_, hwl, fun x hx => ?_⟩
  · obtain ⟨L, hL⟩ := hwl (‖x‖ + 1)
    refine hL.continuousOn.continuousAt (closedBall_mem_nhds_of_mem ?_)
    rw [mem_ball, dist_zero_right]; linarith
  · exact tendsto_nhds_unique (htend x) (hconv x hx)


/-- **`W^{1,∞}_loc` functions are locally Lipschitz (Verified).** Let `u : ℝᵈ → ℝ` be locally
integrable with weak partial derivatives `∂ᵢ u = gᵢ` such that for every `R` there is `G_R`
with `|gᵢ(x)| ≤ G_R` for a.e. `x` with `‖x‖ ≤ R`. Then `u` agrees almost everywhere with a
continuous function `w` that is Lipschitz on every closed ball `closedBall 0 R` (constant
`d G_{R+2}`). Proof: the mollifications `κ_n ⋆ u` are uniformly Lipschitz on each ball and
converge on a dense full-measure set; `exists_locallyLipschitz_of_tendsto_of_dense`. -/
theorem exists_locallyLipschitz_ae_eq_of_hasWeakPartialDeriv {u : (Fin d → ℝ) → ℝ}
    (hu : LocallyIntegrable u) {g : Fin d → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, HasWeakPartialDeriv u i (g i))
    (hG : ∀ R : ℝ, ∃ G : ℝ≥0, ∀ i, ∀ᵐ x, ‖x‖ ≤ R → |g i x| ≤ G) :
    ∃ w : (Fin d → ℝ) → ℝ, Continuous w ∧
      (∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L w (closedBall 0 R)) ∧ w =ᵐ[volume] u := by
  set κ : ℕ → (Fin d → ℝ) → ℝ := fun n => (mollBump d n).normed volume with hκ
  set m : ℕ → (Fin d → ℝ) → ℝ := fun n => κ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
    with hm
  have hlip : ∀ R : ℝ, ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (m n) (closedBall 0 R) := by
    intro R
    obtain ⟨G, hGR⟩ := hG (R + 2)
    refine ⟨d * G, fun n => ?_⟩
    have hsm : ContDiff ℝ ∞ (κ n) := (mollBump d n).contDiff_normed
    have hcs : HasCompactSupport (κ n) := (mollBump d n).hasCompactSupport_normed
    have hdiff : Differentiable ℝ (m n) :=
      (hcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1)
        (hsm.of_le (by simp)) hu).differentiable (by simp)
    refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hdiff x) (fun x hx => ?_)
      (convex_closedBall 0 R)
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast]
    refine norm_le_of_abs_apply_single_le _ G.2 fun i => ?_
    rw [(hg i).fderiv_convolution_apply hsm hcs x]
    refine abs_convolution_le_of_ae_bound_on_support (mollBump d n).nonneg_normed
      (mollBump d n).integrable_normed (mollBump d n).integral_normed ?_
    filter_upwards [hGR i] with y hy hne
    refine hy ?_
    have hsupp : x - y ∈ Function.support (κ n) := hne
    rw [hκ, (mollBump d n).support_normed_eq, mem_ball, dist_zero_right] at hsupp
    have hr : (mollBump d n).rOut ≤ 2 := by
      simp only [mollBump]
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [mem_closedBall, dist_zero_right] at hx
    have h1 := norm_le_insert' y x
    rw [norm_sub_rev] at h1
    linarith
  have hae : ∀ᵐ x, Tendsto (fun n => m n x) atTop (𝓝 (u x)) :=
    ae_tendsto_mollBump_convolution hu
  obtain ⟨w, hwc, hwl, hwS⟩ := exists_locallyLipschitz_of_tendsto_of_dense
    (Measure.dense_of_ae hae) (fun x hx => hx) hlip
  refine ⟨w, hwc, hwl, ?_⟩
  filter_upwards [hae] with x hx using hwS hx


/-- **`W^{1,∞}_loc` vector fields are locally Lipschitz (Verified).** If `v : ℝᵈ → ℝᵈ` has a
weak Jacobian `Dv` that is essentially bounded on every ball (`|Dv x j i| ≤ G_R` for a.e.
`‖x‖ ≤ R`), then `v` agrees almost everywhere with a continuous field that is Lipschitz on
every closed ball `closedBall 0 R`. -/
theorem exists_locallyLipschitz_ae_eq_of_hasWeakJacobian {v : (Fin d → ℝ) → Fin d → ℝ}
    {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ} (hv : HasWeakJacobian v Dv)
    (hG : ∀ R : ℝ, ∃ G : ℝ≥0, ∀ j i, ∀ᵐ x, ‖x‖ ≤ R → |Dv x j i| ≤ G) :
    ∃ w : (Fin d → ℝ) → Fin d → ℝ, Continuous w ∧
      (∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L w (closedBall 0 R)) ∧ w =ᵐ[volume] v := by
  have hex : ∀ j : Fin d, ∃ w : (Fin d → ℝ) → ℝ, Continuous w ∧
      (∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L w (closedBall 0 R)) ∧
      w =ᵐ[volume] fun x => v x j := by
    intro j
    refine exists_locallyLipschitz_ae_eq_of_hasWeakPartialDeriv (hv j j).1 (hv j) fun R => ?_
    obtain ⟨G, hGR⟩ := hG R
    exact ⟨G, hGR j⟩
  choose w hwc hwl hwe using hex
  refine ⟨fun x j => w j x, continuous_pi hwc, fun R => ?_, ?_⟩
  · choose L hL using fun j => hwl j R
    refine ⟨Finset.univ.sup L, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
    exact ((hL j).weaken (Finset.le_sup (Finset.mem_univ j))).dist_le_mul x hx y hy
  · filter_upwards [ae_all_iff.2 hwe] with x hx
    funext j
    exact hx j

end FormalizeSampling
