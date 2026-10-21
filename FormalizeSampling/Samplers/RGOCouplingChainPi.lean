module

public import Mathlib.Probability.Independence.InfinitePi
public import FormalizeSampling.Samplers.RGOCouplingPi

/-!
# Pathwise Lipschitz representations from contracting stationary chains

Status: **Verified** (no named hypotheses).

Let `K` be a Markov kernel on `Fin d → ℝ` (in the application, `y ↦ RGO(y)`). Suppose that for
every `y` there is a Markov chain on `Fin d → ℝ`, driven by i.i.d. noise `ω ∼ P₀`,
`x ↦ H(y, x, ω)`, which

* leaves `K y` invariant: if `x ∼ K y` and `ω ∼ P₀` are independent, then `H(y, x, ω) ∼ K y`;
* is a synchronous contraction, jointly in the state and the parameter:
  `|H(y, x, ω) - H(y', x', ω)| ≤ (1 - θ) |x - x'| + θ |y - y'|` (Euclidean) for some
  `θ ∈ (0, 1]`;
* has a first moment from one point: `E |H(0, 0, ω)| < ∞`.

Then `K` has a pathwise `1`-Lipschitz representation (`RGOCouplingPi.HasLipRep`). The
representation is built by **backward iteration** (coupling from the past) on the infinite
product `Ω = ℕ → Ω₀` with `P = P₀^⊗ℕ`:
`Yₙ(y, ω) = H(y, ·, ω₀) ∘ H(y, ·, ω₁) ∘ ⋯ ∘ H(y, ·, ωₙ₋₁)(0)` converges for `P`-a.e. `ω`
(the increments are bounded by `(1 - θ)ⁿ (|H(0, 0, ωₙ)| + θ |y|)`, summable a.s. by the moment
assumption), on a full-measure set that does **not** depend on `y`. The limit `G(y, ω)` satisfies
`|G(y, ω) - G(y', ω)| ≤ |y - y'|` for **all** `ω` (the bound holds for every `Yₙ`), and has law
`K y`: started from an independent `x ∼ K y` instead of `0`, the backward iterates have law
`K y` for every `n` (invariance) and differ from `Yₙ` by at most `(1 - θ)ⁿ |x|`.

## Main results

Distances are Euclidean (`eDist`, in `Samplers/ShiftedCompositionPi.lean`).

* `map_head_shift`: under `P₀^⊗ℕ`, `ω₀` and the shifted sequence `(ωₙ₊₁)ₙ` are independent with
  laws `P₀` and `P₀^⊗ℕ`.
* `map_bw_prod`: invariance of `K y` along the backward iteration.
* `hasLipRep_of_contraction` (**main theorem**).

## Not proved here

* Rates of convergence of the backward iteration; uniqueness of the invariant law (not needed).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FormalizeSampling.ProximalPi FormalizeSampling.RGOCouplingPi
open scoped ENNReal NNReal

namespace FormalizeSampling.RGOCouplingChainPi

variable {d : ℕ}

/-! ### Head and tail of an i.i.d. sequence -/

variable {Ω₀ : Type} [MeasurableSpace Ω₀]

/-- The shift `(ωₙ)ₙ ↦ (ωₙ₊₁)ₙ` of a sequence. -/
def shiftSeq (ω : ℕ → Ω₀) : ℕ → Ω₀ := fun n => ω (n + 1)

/-- The shift is measurable. -/
theorem measurable_shiftSeq : Measurable (shiftSeq (Ω₀ := Ω₀)) :=
  measurable_pi_iff.2 fun n => measurable_pi_apply (n + 1)

/-- **Head and tail of an i.i.d. sequence.** Under `P₀^⊗ℕ`, `(ω₀, (ωₙ₊₁)ₙ)` has law
`P₀ ⊗ P₀^⊗ℕ`. -/
theorem map_head_shift (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] :
    (Measure.infinitePi fun _ : ℕ => P₀).map (fun ω => (ω 0, shiftSeq ω))
      = P₀.prod (Measure.infinitePi fun _ : ℕ => P₀) := by
  set P := Measure.infinitePi fun _ : ℕ => P₀
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ => P₀) (X := fun _ ω => ω)
    (fun _ => measurable_id)).iIndep
  have hdis : Disjoint ({0} : Set ℕ) {i | i ≠ 0} := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact hb ha
  have h2 := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) h hdis
  have hind : IndepFun (fun ω : ℕ → Ω₀ => ω 0) shiftSeq P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le h2 ?_ ?_
    · exact le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
        MeasurableSpace.comap (fun ω : ℕ → Ω₀ => ω i) inferInstance) 0 rfl
    · show MeasurableSpace.comap shiftSeq MeasurableSpace.pi ≤ _
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun n => ?_
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | i ≠ 0}) =>
        MeasurableSpace.comap (fun ω : ℕ → Ω₀ => ω i) inferInstance) (n + 1)
          (Nat.succ_ne_zero n)
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    measurable_shiftSeq.aemeasurable, Measure.infinitePi_map_eval]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => P₀)
    (f := fun n => n + 1) (fun a b h => Nat.succ_injective h)

/-- Rearranging a triple product: `(a, (b, c)) ↦ ((a, c), b)` maps `μ ⊗ (ν ⊗ τ)` to
`(μ ⊗ τ) ⊗ ν`. -/
theorem map_prod_prod_rearrange {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ]
    [SigmaFinite ν] [SigmaFinite τ] :
    (μ.prod (ν.prod τ)).map (fun s => ((s.1, s.2.2), s.2.1)) = (μ.prod τ).prod ν := by
  have e : (fun s : α × β × γ => ((s.1, s.2.2), s.2.1)) =
      (MeasurableEquiv.prodAssoc.symm : α × γ × β → (α × γ) × β) ∘ Prod.map id Prod.swap := by
    funext s
    rfl
  rw [e, ← Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap measurable_swap),
    ← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id, Measure.prod_swap,
    ← Measure.prodAssoc_prod, Measure.map_map (MeasurableEquiv.measurable _)
      (MeasurableEquiv.measurable _), MeasurableEquiv.symm_comp_self, Measure.map_id]

/-! ### Backward iteration -/

/-- The backward iterates `bw H y n x ω = H(y, ·, ω₀) ∘ ⋯ ∘ H(y, ·, ωₙ₋₁)(x)`. -/
def bw (H : (Fin d → ℝ) → (Fin d → ℝ) → Ω₀ → Fin d → ℝ) (y : Fin d → ℝ) :
    ℕ → (Fin d → ℝ) → (ℕ → Ω₀) → Fin d → ℝ
  | 0, x, _ => x
  | n + 1, x, ω => H y (bw H y n x (shiftSeq ω)) (ω 0)

variable {H : (Fin d → ℝ) → (Fin d → ℝ) → Ω₀ → Fin d → ℝ}

/-- The backward iterates are jointly measurable in `((y, x), ω)`. -/
theorem measurable_bw (hH : Measurable fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × Ω₀ =>
    H q.1.1 q.1.2 q.2) (n : ℕ) :
    Measurable fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × (ℕ → Ω₀) => bw H q.1.1 n q.1.2 q.2 := by
  induction n with
  | zero => exact measurable_fst.snd
  | succ n ih =>
    have e : (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × (ℕ → Ω₀) => bw H q.1.1 (n + 1) q.1.2 q.2)
        = fun q => H q.1.1 (bw H q.1.1 n q.1.2 (shiftSeq q.2)) (q.2 0) := rfl
    rw [e]
    exact hH.comp ((measurable_fst.fst.prodMk (ih.comp (measurable_fst.prodMk
      (measurable_shiftSeq.comp measurable_snd)))).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))

omit [MeasurableSpace Ω₀] in
/-- **Synchronous contraction of the backward iterates.** If
`|H(y, x, ω) - H(y', x', ω)| ≤ (1 - θ) |x - x'| + θ |y - y'|` with `θ ≤ 1`, then
`|Yₙ(y, x) - Yₙ(y', x')| ≤ (1 - θ)ⁿ |x - x'| + (1 - (1 - θ)ⁿ) |y - y'|`. -/
theorem eDist_bw_le {θ : ℝ} (hθ1 : θ ≤ 1)
    (hcontr : ∀ y y' x x' ω, eDist (H y x ω) (H y' x' ω)
      ≤ (1 - θ) * eDist x x' + θ * eDist y y') (n : ℕ) (y y' x x' : Fin d → ℝ)
    (ω : ℕ → Ω₀) :
    eDist (bw H y n x ω) (bw H y' n x' ω)
      ≤ (1 - θ) ^ n * eDist x x' + (1 - (1 - θ) ^ n) * eDist y y' := by
  induction n generalizing ω with
  | zero => simp [bw]
  | succ n ih =>
    have h1 := hcontr y y' (bw H y n x (shiftSeq ω)) (bw H y' n x' (shiftSeq ω)) (ω 0)
    have h2 := ih (shiftSeq ω)
    have hθ : 0 ≤ 1 - θ := by linarith
    calc eDist (bw H y (n + 1) x ω) (bw H y' (n + 1) x' ω)
        ≤ (1 - θ) * eDist (bw H y n x (shiftSeq ω)) (bw H y' n x' (shiftSeq ω))
          + θ * eDist y y' := h1
      _ ≤ (1 - θ) * ((1 - θ) ^ n * eDist x x' + (1 - (1 - θ) ^ n) * eDist y y')
          + θ * eDist y y' := by gcongr
      _ = (1 - θ) ^ (n + 1) * eDist x x' + (1 - (1 - θ) ^ (n + 1)) * eDist y y' := by ring

omit [MeasurableSpace Ω₀] in
/-- **Increments of the backward iterates.**
`|Yₙ₊₁(y, x, ω) - Yₙ(y, x, ω)| ≤ (1 - θ)ⁿ |H(y, x, ωₙ) - x|`. -/
theorem eDist_bw_succ_le {θ : ℝ} (hθ1 : θ ≤ 1)
    (hcontr : ∀ y y' x x' ω, eDist (H y x ω) (H y' x' ω)
      ≤ (1 - θ) * eDist x x' + θ * eDist y y') (n : ℕ) (y x : Fin d → ℝ) (ω : ℕ → Ω₀) :
    eDist (bw H y (n + 1) x ω) (bw H y n x ω) ≤ (1 - θ) ^ n * eDist (H y x (ω n)) x := by
  induction n generalizing ω with
  | zero => simp [bw]
  | succ n ih =>
    have h1 := hcontr y y (bw H y (n + 1) x (shiftSeq ω)) (bw H y n x (shiftSeq ω)) (ω 0)
    rw [eDist_self, mul_zero, add_zero] at h1
    have h2 := ih (shiftSeq ω)
    have hθ : 0 ≤ 1 - θ := by linarith
    calc eDist (bw H y (n + 1 + 1) x ω) (bw H y (n + 1) x ω)
        ≤ (1 - θ) * eDist (bw H y (n + 1) x (shiftSeq ω)) (bw H y n x (shiftSeq ω)) := h1
      _ ≤ (1 - θ) * ((1 - θ) ^ n * eDist (H y x (shiftSeq ω n)) x) := by gcongr
      _ = (1 - θ) ^ (n + 1) * eDist (H y x (ω (n + 1))) x := by
        rw [shiftSeq]
        ring

/-- **Invariance along the backward iteration.** If `x ∼ K y` and `ω ∼ P₀` independent give
`H(y, x, ω) ∼ K y`, then for `x ∼ K y` independent of `ω ∼ P₀^⊗ℕ`, the backward iterate
`Yₙ(y, x, ω)` has law `K y` for every `n`. -/
theorem map_bw_prod (hH : Measurable fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × Ω₀ =>
    H q.1.1 q.1.2 q.2) (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (y : Fin d → ℝ)
    (hstat : (μ.prod P₀).map (fun q => H y q.1 q.2) = μ) (n : ℕ) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => P₀)).map (fun q => bw H y n q.1 q.2) = μ := by
  set P := Measure.infinitePi fun _ : ℕ => P₀
  have hHy : Measurable fun q : (Fin d → ℝ) × Ω₀ => H y q.1 q.2 :=
    hH.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hbw : ∀ n, Measurable fun q : (Fin d → ℝ) × (ℕ → Ω₀) => bw H y n q.1 q.2 := fun n =>
    (measurable_bw hH n).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  induction n with
  | zero =>
    show (μ.prod P).map Prod.fst = μ
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  | succ n ih =>
    have e : (fun q : (Fin d → ℝ) × (ℕ → Ω₀) => bw H y (n + 1) q.1 q.2) =
        (fun r : (Fin d → ℝ) × Ω₀ => H y r.1 r.2) ∘
          ((Prod.map (fun r : (Fin d → ℝ) × (ℕ → Ω₀) => bw H y n r.1 r.2) id) ∘
            (fun s : (Fin d → ℝ) × (Ω₀ × (ℕ → Ω₀)) => ((s.1, s.2.2), s.2.1)) ∘
              Prod.map id (fun ω : ℕ → Ω₀ => (ω 0, shiftSeq ω))) := by
      funext q
      rfl
    have hs : Measurable fun ω : ℕ → Ω₀ => (ω 0, shiftSeq ω) :=
      (measurable_pi_apply 0).prodMk measurable_shiftSeq
    have hr : Measurable fun s : (Fin d → ℝ) × (Ω₀ × (ℕ → Ω₀)) => ((s.1, s.2.2), s.2.1) :=
      (measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst
    rw [e, ← Measure.map_map hHy (((hbw n).prodMap measurable_id).comp (hr.comp
        (measurable_id.prodMap hs))),
      ← Measure.map_map ((hbw n).prodMap measurable_id) (hr.comp (measurable_id.prodMap hs)),
      ← Measure.map_map hr (measurable_id.prodMap hs),
      ← Measure.map_prod_map _ _ measurable_id hs, Measure.map_id, map_head_shift,
      map_prod_prod_rearrange, ← Measure.map_prod_map _ _ (hbw n) measurable_id, Measure.map_id,
      ih, hstat]

/-! ### The main theorem -/

/-- **Pathwise Lipschitz representation from a contracting invariant chain.** Let `K` be a
Markov kernel on `Fin d → ℝ`, `(Ω₀, P₀)` a probability space, `θ ∈ (0, 1]` and
`H : (Fin d → ℝ) → (Fin d → ℝ) → Ω₀ → Fin d → ℝ` jointly measurable with

* `|H(y, x, ω) - H(y', x', ω)| ≤ (1 - θ) |x - x'| + θ |y - y'|` for all `y, y', x, x', ω`;
* `K y` invariant: `((K y) ⊗ P₀).map (H y) = K y` for every `y`;
* `∫⁻ |H(0, 0, ω)| dP₀ < ∞`.

Then `K` has a pathwise `1`-Lipschitz representation. -/
theorem hasLipRep_of_contraction (K : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsMarkovKernel K]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (hH : Measurable fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × Ω₀ => H q.1.1 q.1.2 q.2)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcontr : ∀ y y' x x' ω, eDist (H y x ω) (H y' x' ω)
      ≤ (1 - θ) * eDist x x' + θ * eDist y y')
    (hstat : ∀ y, ((K y).prod P₀).map (fun q => H y q.1 q.2) = K y)
    (hmom : ∫⁻ ω, ENNReal.ofReal (eDist (H 0 0 ω) 0) ∂P₀ ≠ ⊤) :
    HasLipRep K := by
  classical
  set P := Measure.infinitePi fun _ : ℕ => P₀ with hPdef
  have hθ : 0 ≤ 1 - θ := by linarith
  have hθ' : 1 - θ < 1 := by linarith
  -- the moment variable and the a.s. finite weighted sum
  set V : Ω₀ → ℝ := fun a => eDist (H 0 0 a) 0 with hVdef
  have hV : Measurable V := continuous_eDist.measurable.comp
    ((hH.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id)).prodMk
      measurable_const)
  set S : (ℕ → Ω₀) → ℝ≥0∞ := fun ω =>
    ∑' n, ENNReal.ofReal ((1 - θ) ^ n) * ENNReal.ofReal (V (ω n)) with hSdef
  have hSm : Measurable S := Measurable.tsum fun n =>
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hV.comp (measurable_pi_apply n)))
  have hSint : ∫⁻ ω, S ω ∂P ≠ ⊤ := by
    show ∫⁻ ω, ∑' n, ENNReal.ofReal ((1 - θ) ^ n) * ENNReal.ofReal (V (ω n)) ∂P ≠ ⊤
    have hmeas : ∀ n, AEMeasurable (fun ω : ℕ → Ω₀ =>
        ENNReal.ofReal ((1 - θ) ^ n) * ENNReal.ofReal (V (ω n))) P := fun n =>
      (measurable_const.mul (ENNReal.measurable_ofReal.comp
        (hV.comp (measurable_pi_apply n)))).aemeasurable
    rw [lintegral_tsum hmeas]
    have e : ∀ n, ∫⁻ ω, ENNReal.ofReal ((1 - θ) ^ n) * ENNReal.ofReal (V (ω n)) ∂P
        = ENNReal.ofReal (1 - θ) ^ n * ∫⁻ a, ENNReal.ofReal (V a) ∂P₀ := by
      intro n
      have hev : Measurable fun ω : ℕ → Ω₀ => ω n := measurable_pi_apply n
      have hm : Measurable fun ω : ℕ → Ω₀ => ENNReal.ofReal (V (ω n)) :=
        ENNReal.measurable_ofReal.comp (hV.comp (measurable_pi_apply n))
      rw [lintegral_const_mul _ hm, ENNReal.ofReal_pow hθ,
        ← Measure.infinitePi_map_eval (fun _ : ℕ => P₀) n,
        lintegral_map (f := fun a => ENNReal.ofReal (V a)) (ENNReal.measurable_ofReal.comp hV)
          hev]
    simp_rw [e]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ?_) hmom
    have : ENNReal.ofReal (1 - θ) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hθ'
    exact (tsub_pos_of_lt this).ne'
  set E : Set (ℕ → Ω₀) := {ω | S ω < ⊤} with hEdef
  have hE : MeasurableSet E := measurableSet_lt hSm measurable_const
  have hPE : P Eᶜ = 0 := by
    have := ae_lt_top hSm hSint
    rwa [ae_iff] at this
  -- convergence of the backward iterates on `E`
  have hbound : ∀ y (ω : ℕ → Ω₀) n, dist (bw H y n 0 ω) (bw H y (n + 1) 0 ω)
      ≤ (1 - θ) ^ n * V (ω n) + (1 - θ) ^ n * (θ * eDist y 0) := by
    intro y ω n
    rw [dist_comm]
    refine (dist_le_eDist _ _).trans ((eDist_bw_succ_le hθ1 hcontr n y 0 ω).trans ?_)
    have h1 := hcontr y 0 0 0 (ω n)
    rw [eDist_self, mul_zero, zero_add] at h1
    have h2 := eDist_triangle (H y 0 (ω n)) (H 0 0 (ω n)) 0
    calc (1 - θ) ^ n * eDist (H y 0 (ω n)) 0
        ≤ (1 - θ) ^ n * (θ * eDist y 0 + V (ω n)) := by gcongr; linarith
      _ = _ := by ring
  have hcauchy : ∀ y, ∀ ω ∈ E, CauchySeq fun n => bw H y n 0 ω := by
    intro y ω hω
    refine cauchySeq_of_dist_le_of_summable _ (hbound y ω) ?_
    refine Summable.add ?_ ((summable_geometric_of_lt_one hθ hθ').mul_right _)
    have h := ENNReal.summable_toReal hω.ne
    refine h.congr fun n => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hθ n),
      ENNReal.toReal_ofReal (eDist_nonneg _ _)]
  obtain ⟨G, hGdef⟩ : ∃ G : (Fin d → ℝ) → (ℕ → Ω₀) → Fin d → ℝ, G = fun y ω =>
      if ω ∈ E then limUnder atTop (fun n => bw H y n 0 ω) else 0 := ⟨_, rfl⟩
  have hGlim : ∀ y, ∀ ω ∈ E, Tendsto (fun n => bw H y n 0 ω) atTop (𝓝 (G y ω)) := by
    intro y ω hω
    rw [hGdef]
    simp only [hω, ↓reduceIte]
    exact (hcauchy y ω hω).tendsto_limUnder
  have hG0 : ∀ y, ∀ ω ∉ E, G y ω = 0 := by
    intro y ω hω
    rw [hGdef]
    simp only [hω, ↓reduceIte]
  have hGm : Measurable (Function.uncurry G) := by
    refine measurable_of_tendsto_metrizable (f := fun n (p : (Fin d → ℝ) × (ℕ → Ω₀)) =>
      if p.2 ∈ E then bw H p.1 n 0 p.2 else 0) (fun n => ?_) ?_
    · refine Measurable.ite (hE.preimage measurable_snd) ?_ measurable_const
      exact (measurable_bw hH n).comp ((measurable_fst.prodMk measurable_const).prodMk
        measurable_snd)
    · refine tendsto_pi_nhds.2 fun p => ?_
      by_cases hp : p.2 ∈ E
      · simp only [hp, ↓reduceIte]
        exact hGlim p.1 p.2 hp
      · simp only [hp, ↓reduceIte, Function.uncurry]
        rw [hG0 p.1 p.2 hp]
        exact tendsto_const_nhds
  refine ⟨ℕ → Ω₀, inferInstance, P, G, inferInstance, hGm, fun y => ?_, fun y y' ω => ?_⟩
  · -- the law of `G y`
    have hGy : Measurable (G y) := hGm.comp measurable_prodMk_left
    refine (ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_).symm
    set μ := K y
    have hbwy : ∀ n, Measurable fun q : (Fin d → ℝ) × (ℕ → Ω₀) => bw H y n q.1 q.2 :=
      fun n => (measurable_bw hH n).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hf : Measurable fun x : Fin d → ℝ => (f x : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp f.continuous.measurable
    have hconst : ∀ n, ∫⁻ x, (f x : ℝ≥0∞) ∂μ
        = ∫⁻ q, (f (bw H y n q.1 q.2) : ℝ≥0∞) ∂(μ.prod P) := by
      intro n
      conv_lhs => rw [← map_bw_prod hH P₀ μ y (hstat y) n]
      rw [lintegral_map hf (hbwy n)]
    have hlim : Tendsto (fun n => ∫⁻ q, (f (bw H y n q.1 q.2) : ℝ≥0∞) ∂(μ.prod P)) atTop
        (𝓝 (∫⁻ q, (f (G y q.2) : ℝ≥0∞) ∂(μ.prod P))) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => ((nndist f 0 : ℝ≥0) : ℝ≥0∞))
        (fun n => hf.comp (hbwy n)) (fun n => ae_of_all _ fun q => ?_) ?_ ?_
      · exact ENNReal.coe_le_coe.2 (BoundedContinuousFunction.NNReal.upper_bound f _)
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
      · have hae : ∀ᵐ q ∂(μ.prod P), q.2 ∈ E := by
          rw [ae_iff]
          have : {q : (Fin d → ℝ) × (ℕ → Ω₀) | ¬ q.2 ∈ E} = univ ×ˢ Eᶜ := by
            ext q
            simp
          rw [this, Measure.prod_prod, hPE, mul_zero]
        filter_upwards [hae] with q hq
        refine ((ENNReal.continuous_coe.comp f.continuous).tendsto _).comp ?_
        refine (hGlim y q.2 hq).congr_dist ?_
        refine squeeze_zero (fun n => dist_nonneg) (fun n => (dist_le_eDist _ _).trans ?_)
          (?_ : Tendsto (fun n => (1 - θ) ^ n * eDist 0 q.1) atTop (𝓝 0))
        · have := eDist_bw_le hθ1 hcontr n y y 0 q.1 q.2
          rw [eDist_self, mul_zero, add_zero] at this
          exact this
        · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ').mul_const (eDist 0 q.1)
    have hfinal : ∫⁻ q, (f (G y q.2) : ℝ≥0∞) ∂(μ.prod P) = ∫⁻ x, (f x : ℝ≥0∞) ∂(P.map (G y)) := by
      rw [lintegral_map hf hGy]
      have := lintegral_map (μ := μ.prod P) (f := fun ω => (f (G y ω) : ℝ≥0∞)) (hf.comp hGy)
        measurable_snd
      rw [Measure.map_snd_prod, measure_univ, one_smul] at this
      exact this.symm
    rw [← hfinal]
    exact tendsto_nhds_unique (tendsto_const_nhds.congr hconst) hlim
  · -- the pathwise Lipschitz bound
    by_cases hω : ω ∈ E
    · refine sqDist_le_of_eDist_le (le_of_tendsto' ((continuous_eDist.tendsto _).comp
        ((hGlim y ω hω).prodMk_nhds (hGlim y' ω hω))) fun n => ?_)
      have := eDist_bw_le hθ1 hcontr n y y' 0 0 ω
      rw [eDist_self, mul_zero, zero_add] at this
      refine this.trans ?_
      have h0 : 0 ≤ (1 - θ) ^ n := pow_nonneg hθ n
      nlinarith [eDist_nonneg y y']
    · rw [hG0 y ω hω, hG0 y' ω hω, show sqDist (0 : Fin d → ℝ) 0 = 0 by simp [sqDist]]
      exact sqDist_nonneg _ _

end FormalizeSampling.RGOCouplingChainPi
