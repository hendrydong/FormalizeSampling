module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# A particle system has no density and no state score (CE-05)

For `n ≥ 1` points `x : Fin n → (Fin d → ℝ)` the empirical measure
`μ̂ = (1/n) ∑ᵢ δ_{xᵢ}` is concentrated on the finite set `{x₁, …, xₙ}`, which has Lebesgue
measure `0` when `d ≥ 1`. Hence `μ̂` is mutually singular with respect to `volume`, is not
absolutely continuous with respect to it, and has no Lebesgue density: there is no
`f` with `μ̂ = volume.withDensity f`, and no real `p ≥ 0` with
`μ̂ = volume.withDensity (ofReal ∘ p)`.

Consequently the state score `∇ₓ log p` of the particle system is undefined: the score of a
law is a derivative of its Lebesgue density `p`, and no such `p` exists for `μ̂`. This contrasts
with *population* laws such as `N(m, v)`, `v ≠ 0`, which are `volume.withDensity` of a smooth
positive density (`gaussianReal_of_var_ne_zero`), so `score1`/`score` is meaningful for them.
Particle methods that use a "score" must therefore use the score of some other, absolutely
continuous object (the population law, a kernel-smoothed empirical measure, a model); they
never differentiate the empirical measure itself.

## Conventions

* `empirical x := (n : ℝ≥0∞)⁻¹ • ∑ i, dirac (x i)`.
* The generic results hold for any reference measure `ν` without atoms on a space with
  measurable singletons; the corollaries specialise to `volume` on `Fin d → ℝ` (`d ≥ 1`) and
  on `ℝ`.
* The hypothesis `d ≥ 1` is necessary: for `d = 0` the space `Fin 0 → ℝ` is a single point,
  `volume` is the Dirac mass there and the empirical measure *equals* `volume`
  (`empirical_eq_volume_of_dim_zero`).

## Registry IDs

* `CE-05`: `empirical_singleton_pos`, `empirical_mutuallySingular`,
  `not_empirical_absolutelyContinuous`, `not_exists_withDensity_eq_empirical`,
  `not_exists_real_density_eq_empirical`, `empirical_mutuallySingular_volume`,
  `not_empirical_absolutelyContinuous_volume`, `empirical_has_no_density`,
  `empirical_has_no_real_density`, `empirical_has_no_density_real`,
  `empirical_eq_volume_of_dim_zero`.

## Not proved here

* No statement about kernel-smoothed empirical measures (`μ̂ ∗ N(0, ε I)` does have a density)
  or about the convergence of particle approximations to the population law is formalised.
* "No state score" is expressed as the non-existence of a Lebesgue density; no separate
  distributional notion of score is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FormalizeSampling.Counterexamples.ParticleVsPopulation

variable {α : Type*} [MeasurableSpace α]

/-- The empirical measure `μ̂ = (1/n) ∑ᵢ δ_{xᵢ}` of `n` particles `x : Fin n → α`. -/
noncomputable def empirical {n : ℕ} (x : Fin n → α) : Measure α :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- Every particle is an atom of the empirical measure: `0 < μ̂ {xᵢ}` (indeed `μ̂ {xᵢ} ≥ 1/n`).
-/
theorem empirical_singleton_pos {n : ℕ} (x : Fin n → α) (i : Fin n) :
    0 < empirical x {x i} := by
  rw [empirical, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)) ?_
  refine (Finset.sum_pos_iff.2 ⟨i, Finset.mem_univ i, ?_⟩).ne'
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)]
  exact one_pos

/-- **The empirical measure is singular.** For any reference measure `ν` without atoms on a
space with measurable singletons, `μ̂ ⟂ ν`: `μ̂` lives on the finite set `{x₁, …, xₙ}`, which is
`ν`-null. -/
theorem empirical_mutuallySingular [MeasurableSingletonClass α] {n : ℕ} (x : Fin n → α)
    (ν : Measure α) [NullSingletonClass ν] : empirical x ⟂ₘ ν := by
  have hfin : (Set.range x).Finite := Set.finite_range x
  refine ⟨(Set.range x)ᶜ, hfin.measurableSet.compl, ?_, ?_⟩
  · rw [empirical, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    have : ∀ i, Measure.dirac (x i) (Set.range x)ᶜ = 0 := by
      intro i
      rw [Measure.dirac_apply' _ hfin.measurableSet.compl]
      simp
    simp [this]
  · rw [compl_compl]
    exact hfin.measure_zero ν

/-- **The empirical measure is not absolutely continuous.** For `n ≥ 1` particles and any
reference measure `ν` without atoms, `¬ (μ̂ ≪ ν)`. -/
theorem not_empirical_absolutelyContinuous {n : ℕ} (hn : 0 < n) (x : Fin n → α)
    (ν : Measure α) [NullSingletonClass ν] : ¬ empirical x ≪ ν := by
  intro hac
  have h0 : ν {x ⟨0, hn⟩} = 0 := measure_singleton _
  exact (empirical_singleton_pos x ⟨0, hn⟩).ne' (hac h0)

/-- **The empirical measure has no density.** For `n ≥ 1` particles and any reference measure
`ν` without atoms, there is no `f : α → ℝ≥0∞` with `μ̂ = ν.withDensity f`. -/
theorem not_exists_withDensity_eq_empirical {n : ℕ} (hn : 0 < n) (x : Fin n → α)
    (ν : Measure α) [NullSingletonClass ν] : ¬ ∃ f : α → ℝ≥0∞, empirical x = ν.withDensity f := by
  rintro ⟨f, hf⟩
  exact not_empirical_absolutelyContinuous hn x ν
    (hf ▸ withDensity_absolutelyContinuous ν f)

/-- **No real density, hence no score.** For `n ≥ 1` particles and any reference measure `ν`
without atoms, there is no real function `p` with `μ̂ = ν.withDensity (ofReal ∘ p)`; in
particular there is no density `p` whose state score `∇ log p` could serve as the score of
`μ̂`. -/
theorem not_exists_real_density_eq_empirical {n : ℕ} (hn : 0 < n) (x : Fin n → α)
    (ν : Measure α) [NullSingletonClass ν] :
    ¬ ∃ p : α → ℝ, empirical x = ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  rintro ⟨p, hp⟩
  exact not_exists_withDensity_eq_empirical hn x ν ⟨_, hp⟩

section Euclidean

variable {d : ℕ}

private lemma noAtoms_volume_pi (hd : 0 < d) :
    NullSingletonClass (volume : Measure (Fin d → ℝ)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

/-- **CE-05, singularity on `ℝ^d`.** For `d ≥ 1` and any particles
`x : Fin n → (Fin d → ℝ)`, the empirical measure is mutually singular with Lebesgue measure. -/
theorem empirical_mutuallySingular_volume (hd : 0 < d) {n : ℕ} (x : Fin n → (Fin d → ℝ)) :
    empirical x ⟂ₘ (volume : Measure (Fin d → ℝ)) := by
  have := noAtoms_volume_pi hd
  exact empirical_mutuallySingular x volume

/-- **CE-05 on `ℝ^d`.** For `d ≥ 1` and `n ≥ 1` particles `x : Fin n → (Fin d → ℝ)`, the
empirical measure is not absolutely continuous with respect to Lebesgue measure. -/
theorem not_empirical_absolutelyContinuous_volume (hd : 0 < d) {n : ℕ} (hn : 0 < n)
    (x : Fin n → (Fin d → ℝ)) : ¬ empirical x ≪ (volume : Measure (Fin d → ℝ)) := by
  have := noAtoms_volume_pi hd
  exact not_empirical_absolutelyContinuous hn x volume

/-- **CE-05: a particle system has no Lebesgue density on `ℝ^d`.** For `d ≥ 1` and `n ≥ 1`
particles `x : Fin n → (Fin d → ℝ)`, there is no `f` with `μ̂ = volume.withDensity f`. -/
theorem empirical_has_no_density (hd : 0 < d) {n : ℕ} (hn : 0 < n)
    (x : Fin n → (Fin d → ℝ)) :
    ¬ ∃ f : (Fin d → ℝ) → ℝ≥0∞, empirical x = (volume : Measure (Fin d → ℝ)).withDensity f := by
  have := noAtoms_volume_pi hd
  exact not_exists_withDensity_eq_empirical hn x volume

/-- **CE-05: no real density, hence no state score on `ℝ^d`.** For `d ≥ 1` and `n ≥ 1`
particles, there is no real `p : (Fin d → ℝ) → ℝ` with
`μ̂ = volume.withDensity (ofReal ∘ p)`, so `FormalizeSampling.score p` is not the score of `μ̂`
for any `p`: the empirical measure has no state score. -/
theorem empirical_has_no_real_density (hd : 0 < d) {n : ℕ} (hn : 0 < n)
    (x : Fin n → (Fin d → ℝ)) :
    ¬ ∃ p : (Fin d → ℝ) → ℝ, empirical x =
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ENNReal.ofReal (p y)) := by
  have := noAtoms_volume_pi hd
  exact not_exists_real_density_eq_empirical hn x volume

/-- **The hypothesis `d ≥ 1` is necessary.** For `d = 0` the state space `Fin 0 → ℝ` is a single
point, Lebesgue measure on it is the unit Dirac mass, and the empirical measure of any `n ≥ 1`
particles equals `volume` (so it trivially has density `1`). -/
theorem empirical_eq_volume_of_dim_zero {n : ℕ} (hn : 0 < n) (x : Fin n → (Fin 0 → ℝ)) :
    empirical x = (volume : Measure (Fin 0 → ℝ)) := by
  have hx : ∀ i, x i = (isEmptyElim : (i : Fin 0) → ℝ) := fun i => Subsingleton.elim _ _
  rw [empirical, MeasureTheory.volume_pi, Measure.pi_of_empty]
  simp only [hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n), one_smul]

end Euclidean

/-- **CE-05 on `ℝ`.** For `n ≥ 1` real particles `x : Fin n → ℝ`, the empirical measure has no
Lebesgue density: there is no `f` with `μ̂ = volume.withDensity f`. -/
theorem empirical_has_no_density_real {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ¬ ∃ f : ℝ → ℝ≥0∞, empirical x = (volume : Measure ℝ).withDensity f :=
  not_exists_withDensity_eq_empirical hn x volume

end FormalizeSampling.Counterexamples.ParticleVsPopulation
