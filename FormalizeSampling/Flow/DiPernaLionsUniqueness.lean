module

public import FormalizeSampling.Foundations.WeakDerivative
public import FormalizeSampling.Flow.ContinuityUniquenessLocal

/-!
# Uniqueness of density solutions of the continuity equation for Sobolev velocities

Status: **Verified** for (i) velocities with a locally essentially bounded weak Jacobian and
linear growth (`W^{1,∞}_loc`, any dimension) and (ii) the **one-dimensional DiPerna–Lions class**
`v ∈ W^{1,1}_loc(ℝ)` with essentially bounded weak divergence. Both are reduced to the
locally Lipschitz uniqueness theorem `uniqueWeakContinuity_of_locallyLipschitz`
(`Flow/ContinuityUniquenessLocal.lean`) through the Sobolev infrastructure of
`Foundations/WeakDerivative.lean`.

## Weak formulation for densities

A velocity `v : ℝᵈ → ℝᵈ` in a Sobolev class is only defined almost everywhere, so the
measure formulation `WeakContinuity2` (which evaluates `v` against arbitrary measures) is not
invariant under changing `v` on a null set. For density curves `ρ_t = u_t dx` the natural
formulation is `WeakContinuityDensity u v`: for every `C²_c` test function `φ` and `t ≥ 0`,

  `d/dt ∫ u_t φ dx = ∫ u_t (v ⬝ ∇φ) dx`   (one-sided derivative within `[0, ∞)`),

which only sees the a.e. class of `v`. `weakContinuity2_densityMeasure` shows that a curve of
probability densities solving it gives a `WeakContinuity2` solution `ρ_t = u_t dx` for **any**
representative `w =ᵐ v`, in particular for a Lipschitz representative when one exists.

## Main results

* `densityMeasure`, `IsProbDensity`, `integral_densityMeasure`,
  `isProbabilityMeasure_densityMeasure`.
* `WeakContinuityDensity` and `weakContinuity2_densityMeasure` (connection to
  `WeakContinuity2`).
* `ae_eq_of_weakContinuityDensity_of_unique`: measure uniqueness for an a.e.-representative
  `w` of `v` gives uniqueness of density solutions.
* `ae_eq_of_weakContinuityDensity_of_locallyLipschitz`,
  `ae_eq_of_weakContinuityDensity_of_lipschitz`: uniqueness when `v` has a (locally)
  Lipschitz representative (of linear growth).
* `ae_eq_of_weakContinuityDensity_of_hasWeakJacobian`: uniqueness for `v` with
  `|∂ᵢ v_j| ≤ G` a.e. (weak Jacobian), any `d`.
* `ae_eq_of_weakContinuityDensity_of_hasWeakJacobian_loc`: uniqueness for `v ∈ W^{1,∞}_loc`
  (weak Jacobian essentially bounded on balls) with a.e. linear growth, any `d`.
* `ae_eq_of_weakContinuityDensity_one_dim`: **one-dimensional DiPerna–Lions uniqueness** —
  for `v ∈ W^{1,1}_loc(ℝ)` with `div v ∈ L^∞` (`MemW11locBddDiv v`), two probability density
  solutions with a.e. equal initial densities have a.e. equal densities at every `t ≥ 0`.
  No growth condition is needed (it follows from `v' ∈ L^∞`).

## Not proved here

The `d ≥ 2` theorem for autonomous `v ∈ W^{1,1}_loc` with bounded divergence and
probability-density solutions is proved elsewhere:
`ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth` (`Flow/DiPernaLionsLinearGrowth.lean`,
linear growth, bounded densities; bounded `v` is `ae_eq_of_weakContinuityDensity_diPernaLions`),
with the commutator lemma in `Flow/DiPernaLionsCommutatorL1.lean` and renormalisation in
`Flow/DiPernaLionsRenormalizationBeta.lean`, and `ae_eq_of_weakContinuityDensity_diPernaLions_Lp`
(`Flow/DiPernaLionsLp.lean`, `L^p` densities).
The list below records what this file alone does not prove; still open overall: time-dependent
velocities, signed solutions, `L¹` densities, growth `v/(1+|x|) ∈ L¹ + L^∞`.

* **DiPerna–Lions in dimension `d ≥ 2`** (`v ∈ W^{1,1}_loc`, `div v ∈ L^∞`, linear growth).
  There `Dv` need not be bounded, `v` need not be Lipschitz, and the proof genuinely requires
  the commutator lemma (`r_ε → 0` in `L¹_loc`), renormalization and a Gronwall argument with
  cut-offs; none of these is used in this file (see the paragraph above for where they are
  proved: the strong `L¹_loc` convergence of the kernel-form commutator `dlCommutator` is
  `tendsto_lintegral_dlCommutator_sub` in `Flow/DiPernaLionsCommutatorL1.lean`, the
  renormalization and Gronwall steps are in `Flow/DiPernaLionsRenormalizationBeta.lean` and
  `Flow/DiPernaLionsLinearGrowth.lean`).
* **Signed or merely `L^∞` solutions.** Only curves of *probability* densities are compared,
  because the Lipschitz theorem used is stated for probability measures. Boundedness of the
  densities is not needed for this class.
* **Time-dependent Sobolev velocities.** Only autonomous `v` is treated (the Lipschitz
  theorem needs joint continuity in `(t, x)`, which a.e.-defined representatives chosen
  separately for each `t` do not provide).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal ENNReal

namespace FormalizeSampling
namespace NoiseScore

variable {d : ℕ}

/-- The measure `f(x) dx` on `ℝᵈ` with density `f⁺ = max f 0` w.r.t. Lebesgue measure. It is
the same measure as `KLDecay.densityMeasure` (`densityMeasure_eq_klDecay_densityMeasure`). -/
noncomputable def densityMeasure (f : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

/-- The density measure of this file coincides with `KLDecay.densityMeasure` (both are
`volume.withDensity (ofReal ∘ f)`), so lemmas about either apply to both. -/
theorem densityMeasure_eq_klDecay_densityMeasure (f : (Fin d → ℝ) → ℝ) :
    densityMeasure f = KLDecay.densityMeasure f := rfl

/-- `f` is a **probability density** on `ℝᵈ`: integrable, a.e. nonnegative, total mass `1`. -/
def IsProbDensity (f : (Fin d → ℝ) → ℝ) : Prop :=
  Integrable f ∧ 0 ≤ᵐ[volume] f ∧ ∫ x, f x = 1

/-- **Integrals against a density measure (Verified).** For an integrable, a.e. nonnegative
density `f` and any `g`, `∫ g d(f dx) = ∫ f g dx`. -/
theorem integral_densityMeasure {f : (Fin d → ℝ) → ℝ} (hf : Integrable f)
    (hf0 : 0 ≤ᵐ[volume] f) (g : (Fin d → ℝ) → ℝ) :
    ∫ x, g x ∂densityMeasure f = ∫ x, f x * g x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hf.aemeasurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hf0] with x hx
  simp [ENNReal.toReal_ofReal hx]

/-- **Probability densities give probability measures (Verified).** -/
theorem isProbabilityMeasure_densityMeasure {f : (Fin d → ℝ) → ℝ} (hf : IsProbDensity f) :
    IsProbabilityMeasure (densityMeasure f) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf.1 hf.2.1, hf.2.2, ENNReal.ofReal_one]

/-- **Weak continuity equation for density curves.** `u : ℝ → ℝᵈ → ℝ` solves
`∂ₜ u + div(u v) = 0` weakly on `t ≥ 0` if for every `C²_c` test function `φ` and `t ≥ 0`,
`s ↦ ∫ u_s φ dx` has derivative `∫ u_t (v ⬝ ∇φ) dx` at `t` within `[0, ∞)`. The formulation
depends on `v` only through its Lebesgue-a.e. class (when the `u_t` are integrable). -/
def WeakContinuityDensity (u : ℝ → (Fin d → ℝ) → ℝ) (v : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  ∀ φ : (Fin d → ℝ) → ℝ, TestFunction2 φ → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => ∫ x, u s x * φ x) (∫ x, u t x * (v x ⬝ᵥ grad φ x)) (Ici 0) t

/-- **From density solutions to `WeakContinuity2` (Verified).** If `u_t` is a probability
density for each `t ≥ 0` and `u` solves `WeakContinuityDensity u v`, then for every vector
field `w` with `w = v` Lebesgue-a.e., the measures `ρ_t = u_t dx` solve `WeakContinuity2` with
the autonomous velocity `w`. -/
theorem weakContinuity2_densityMeasure {u : ℝ → (Fin d → ℝ) → ℝ}
    {v w : (Fin d → ℝ) → Fin d → ℝ} (hu : ∀ t, 0 ≤ t → IsProbDensity (u t))
    (hwv : w =ᵐ[volume] v) (h : WeakContinuityDensity u v) :
    WeakContinuity2 (fun t => densityMeasure (u t)) (fun _ => w) := by
  intro φ hφ t ht
  have hd := h φ hφ t ht
  have hval : ∫ x, w x ⬝ᵥ grad φ x ∂densityMeasure (u t) = ∫ x, u t x * (v x ⬝ᵥ grad φ x) := by
    rw [integral_densityMeasure (hu t ht).1 (hu t ht).2.1]
    refine integral_congr_ae ?_
    filter_upwards [hwv] with x hx
    rw [hx]
  rw [hval]
  refine hd.congr (fun s hs => ?_) ?_
  · exact integral_densityMeasure (hu s hs).1 (hu s hs).2.1 φ
  · exact integral_densityMeasure (hu t ht).1 (hu t ht).2.1 φ

/-- **Uniqueness for density solutions from measure uniqueness (Verified).** Let `w = v`
a.e. and assume `UniqueWeakContinuity` for the autonomous velocity `w`. Let `u, u'` be curves
of probability densities on `t ≥ 0` solving `WeakContinuityDensity` with velocity `v`, with
`u_0 = u'_0` a.e. Then `u_t = u'_t` a.e. for every `t ≥ 0`. -/
theorem ae_eq_of_weakContinuityDensity_of_unique {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v w : (Fin d → ℝ) → Fin d → ℝ} (huniq : UniqueWeakContinuity fun _ => w)
    (hwv : w =ᵐ[volume] v) (hu : ∀ t, 0 ≤ t → IsProbDensity (u t))
    (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t)) (h : WeakContinuityDensity u v)
    (h' : WeakContinuityDensity u' v) (h0 : u 0 =ᵐ[volume] u' 0) :
    ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  intro t ht
  have hρ := huniq _ _ (fun s hs => isProbabilityMeasure_densityMeasure (hu s hs))
    (fun s hs => isProbabilityMeasure_densityMeasure (hu' s hs))
    (weakContinuity2_densityMeasure hu hwv h) (weakContinuity2_densityMeasure hu' hwv h')
    (withDensity_congr_ae (h0.fun_comp ENNReal.ofReal)) t ht
  have hae := (withDensity_eq_iff_of_sigmaFinite (hu t ht).1.aemeasurable.ennreal_ofReal
    (hu' t ht).1.aemeasurable.ennreal_ofReal).1 hρ
  filter_upwards [hae, (hu t ht).2.1, (hu' t ht).2.1] with x hx h1 h2
  exact (ENNReal.ofReal_eq_ofReal_iff h1 h2).1 hx

/-- **Uniqueness for density solutions with a locally Lipschitz representative (Verified).**
Let `w` be continuous, Lipschitz on every closed ball `closedBall 0 R`, of linear growth
`‖w(x)‖ ≤ M (1 + ‖x‖)`, and `w = v` a.e. Then probability density solutions of
`WeakContinuityDensity` with velocity `v` and a.e. equal initial densities agree a.e. at
every `t ≥ 0`. -/
theorem ae_eq_of_weakContinuityDensity_of_locallyLipschitz {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v w : (Fin d → ℝ) → Fin d → ℝ} (hwc : Continuous w)
    (hwl : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L w (Metric.closedBall 0 R)) {M : ℝ}
    (hM : ∀ x, ‖w x‖ ≤ M * (1 + ‖x‖)) (hwv : w =ᵐ[volume] v)
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  refine ae_eq_of_weakContinuityDensity_of_unique ?_ hwv hu hu' h h' h0
  refine uniqueWeakContinuity_of_locallyLipschitz (hwc.comp continuous_snd).continuousOn
    (fun T _ => ⟨M, fun t _ x => hM x⟩) (fun T _ R => ?_)
  obtain ⟨L, hL⟩ := hwl R
  refine ⟨L, fun t _ x y hx hy => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hy' : y ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have := hL.dist_le_mul x hx' y hy'
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- **Uniqueness for density solutions with a Lipschitz representative (Verified).** Let
`w` be `K`-Lipschitz with `w = v` a.e. Let `u, u'` be curves of probability densities on
`t ≥ 0` solving `WeakContinuityDensity` with velocity `v`, with `u_0 = u'_0` a.e. Then
`u_t = u'_t` a.e. for every `t ≥ 0`. -/
theorem ae_eq_of_weakContinuityDensity_of_lipschitz {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v w : (Fin d → ℝ) → Fin d → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hwv : w =ᵐ[volume] v) (hu : ∀ t, 0 ≤ t → IsProbDensity (u t))
    (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t)) (h : WeakContinuityDensity u v)
    (h' : WeakContinuityDensity u' v) (h0 : u 0 =ᵐ[volume] u' 0) :
    ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  refine ae_eq_of_weakContinuityDensity_of_locallyLipschitz hw.continuous
    (fun _ => ⟨K, hw.lipschitzOnWith⟩) (M := ‖w 0‖ + K) (fun x => ?_) hwv hu hu' h h' h0
  have h1 : ‖w x - w 0‖ ≤ K * ‖x - 0‖ := hw.norm_sub_le x 0
  rw [sub_zero] at h1
  have h2 : ‖w x‖ ≤ ‖w 0‖ + K * ‖x‖ := by
    have := norm_le_insert' (w x) (w 0)
    linarith [norm_sub_rev (w x) (w 0)]
  have hK : (0 : ℝ) ≤ K := K.2
  nlinarith [norm_nonneg x, norm_nonneg (w 0)]

/-- **Uniqueness for velocities with bounded weak Jacobian (Verified, `W^{1,∞}`, any `d`).**
Let `v : ℝᵈ → ℝᵈ` have a weak Jacobian `Dv` with `|Dv x j i| ≤ G` a.e. Then two curves of
probability densities solving `WeakContinuityDensity` with velocity `v` and with a.e. equal
initial densities agree a.e. at every `t ≥ 0`. -/
theorem ae_eq_of_weakContinuityDensity_of_hasWeakJacobian {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv) {G : ℝ≥0} (hG : ∀ j i, ∀ᵐ x, |Dv x j i| ≤ G)
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  obtain ⟨w, hw, hwv⟩ := exists_lipschitzWith_ae_eq_of_hasWeakJacobian hv hG
  exact ae_eq_of_weakContinuityDensity_of_lipschitz hw hwv hu hu' h h' h0

/-- **One-dimensional DiPerna–Lions uniqueness (Verified).** On `ℝ = Fin 1 → ℝ`, let
`v ∈ W^{1,1}_loc` have essentially bounded weak divergence (`MemW11locBddDiv v`). Then two
curves of probability densities solving `WeakContinuityDensity` with velocity `v`, with a.e.
equal initial densities, have a.e. equal densities at every `t ≥ 0`. (In one dimension
`div v = v' ∈ L^∞` makes `v` a.e. equal to a Lipschitz field, so no growth assumption is
needed; see `MemW11locBddDiv.exists_lipschitzWith_ae_eq_one_dim`.) -/
theorem ae_eq_of_weakContinuityDensity_one_dim {u u' : ℝ → (Fin 1 → ℝ) → ℝ}
    {v : (Fin 1 → ℝ) → Fin 1 → ℝ} (hv : MemW11locBddDiv v)
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  obtain ⟨K, w, hw, hwv⟩ := hv.exists_lipschitzWith_ae_eq_one_dim
  exact ae_eq_of_weakContinuityDensity_of_lipschitz hw hwv hu hu' h h' h0



/-- **Uniqueness for `W^{1,∞}_loc` velocities of linear growth (Verified, any `d`).** Let
`v : ℝᵈ → ℝᵈ` have a weak Jacobian `Dv` that is essentially bounded on every ball
(`|Dv x j i| ≤ G_R` for a.e. `‖x‖ ≤ R`) and satisfy `‖v(x)‖ ≤ M (1 + ‖x‖)` for a.e. `x`.
Then two curves of probability densities solving `WeakContinuityDensity` with velocity `v`,
with a.e. equal initial densities, agree a.e. at every `t ≥ 0`. -/
theorem ae_eq_of_weakContinuityDensity_of_hasWeakJacobian_loc {u u' : ℝ → (Fin d → ℝ) → ℝ}
    {v : (Fin d → ℝ) → Fin d → ℝ} {Dv : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    (hv : HasWeakJacobian v Dv)
    (hG : ∀ R : ℝ, ∃ G : ℝ≥0, ∀ j i, ∀ᵐ x, ‖x‖ ≤ R → |Dv x j i| ≤ G) {M : ℝ}
    (hM : ∀ᵐ x, ‖v x‖ ≤ M * (1 + ‖x‖))
    (hu : ∀ t, 0 ≤ t → IsProbDensity (u t)) (hu' : ∀ t, 0 ≤ t → IsProbDensity (u' t))
    (h : WeakContinuityDensity u v) (h' : WeakContinuityDensity u' v)
    (h0 : u 0 =ᵐ[volume] u' 0) : ∀ t, 0 ≤ t → u t =ᵐ[volume] u' t := by
  obtain ⟨w, hwc, hwl, hwv⟩ := exists_locallyLipschitz_ae_eq_of_hasWeakJacobian hv hG
  have hclosed : IsClosed {x | ‖w x‖ ≤ M * (1 + ‖x‖)} :=
    isClosed_le hwc.norm (continuous_const.mul (continuous_const.add continuous_norm))
  have hdense : Dense {x | ‖w x‖ ≤ M * (1 + ‖x‖)} := by
    have hae : ∀ᵐ x, ‖w x‖ ≤ M * (1 + ‖x‖) := by
      filter_upwards [hM, hwv] with x hx hx'
      rwa [hx']
    exact Measure.dense_of_ae hae
  have hall : ∀ x, ‖w x‖ ≤ M * (1 + ‖x‖) := by
    intro x
    have : x ∈ closure {x | ‖w x‖ ≤ M * (1 + ‖x‖)} := by rw [hdense.closure_eq]; trivial
    rwa [hclosed.closure_eq] at this
  exact ae_eq_of_weakContinuityDensity_of_locallyLipschitz hwc hwl hall hwv hu hu' h h' h0

end NoiseScore
end FormalizeSampling
