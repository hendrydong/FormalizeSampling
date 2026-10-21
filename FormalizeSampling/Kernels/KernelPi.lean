module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Defs

/-!
# Finite products of kernels

Status: **Verified** (no hypotheses beyond finiteness of the kernels).

Mathlib v4.35 has the product `Measure.pi` of finitely many measures and the binary product
`Kernel.prod`, but no product of a finite family of kernels. This file constructs it: for
finite kernels `κ i : Kernel X (Y i)` (`i` in a `Fintype`),
`KernelPi.pi κ x = Measure.pi (fun i => κ i x)`, the law of independent draws `yᵢ ~ κ i x`
given the common input `x`. The special case `piConst N κ x = (κ x)^{⊗N}` (`N` i.i.d. draws
from one kernel, with a state-dependent law) is what the Monte Carlo oracle of
`Samplers/RandomScoreOracle.lean` needs.

## Main results

* `KernelPi.measurable_measure_pi`: `x ↦ Measure.pi (fun i => κ i x)` is measurable (boxes form
  a generating π-system; on a box the product measure is the finite product `∏ᵢ κ i x (sᵢ)`).
* `KernelPi.pi`, `KernelPi.pi_apply`, `KernelPi.pi_apply_pi`: the product kernel, its
  evaluation, and its value on boxes.
* `KernelPi.piConst`, `KernelPi.piConst_apply`: the `N`-fold i.i.d. power
  `piConst N κ x = Measure.pi (fun _ : Fin N => κ x)`.
* Instances: `pi κ` / `piConst N κ` are finite (resp. Markov) when the `κ i` are.

## Not proved here

* Products of s-finite (non-finite) kernels: the π-system argument uses finiteness.
* Countable/infinite products (Mathlib's `Measure.infinitePi` is not lifted to kernels).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace FormalizeSampling.KernelPi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι] {Y : ι → Type*}
  [∀ i, MeasurableSpace (Y i)]

/-- For finite kernels `κ i : Kernel X (Y i)` over a finite index type, the map
`x ↦ Measure.pi (fun i => κ i x)` is measurable. Proof: boxes `∏ᵢ sᵢ` form a π-system
generating the product σ-algebra, and on a box the measure is `∏ᵢ κ i x (sᵢ)`, a finite
product of measurable functions of `x`. -/
theorem measurable_measure_pi (κ : (i : ι) → Kernel X (Y i)) [∀ i, IsFiniteKernel (κ i)] :
    Measurable fun x => Measure.pi fun i => κ i x := by
  refine Measurable.measure_of_isPiSystem generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ => Kernel.measurable_coe _ (hs i (mem_univ i))
  · rw [show (univ : Set ((i : ι) → Y i)) = univ.pi fun _ => univ from (pi_univ _).symm]
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ => Kernel.measurable_coe _ MeasurableSet.univ

/-- The **product kernel** of a finite family of finite kernels `κ i : Kernel X (Y i)`:
`pi κ x = Measure.pi (fun i => κ i x)`, the joint law of independent draws `yᵢ ~ κ i x`
given the common input `x`. -/
noncomputable def pi (κ : (i : ι) → Kernel X (Y i)) [∀ i, IsFiniteKernel (κ i)] :
    Kernel X ((i : ι) → Y i) where
  toFun x := Measure.pi fun i => κ i x
  measurable' := measurable_measure_pi κ

/-- Evaluation of the product kernel: `pi κ x = Measure.pi (fun i => κ i x)`. -/
theorem pi_apply (κ : (i : ι) → Kernel X (Y i)) [∀ i, IsFiniteKernel (κ i)] (x : X) :
    pi κ x = Measure.pi fun i => κ i x := rfl

/-- The product kernel on a box: `pi κ x (∏ᵢ sᵢ) = ∏ᵢ κ i x (sᵢ)`. -/
theorem pi_apply_pi (κ : (i : ι) → Kernel X (Y i)) [∀ i, IsFiniteKernel (κ i)] (x : X)
    (s : (i : ι) → Set (Y i)) : pi κ x (univ.pi s) = ∏ i, κ i x (s i) := by
  rw [pi_apply, Measure.pi_pi]

/-- The product of finite kernels is a finite kernel. -/
instance isFiniteKernel_pi (κ : (i : ι) → Kernel X (Y i)) [∀ i, IsFiniteKernel (κ i)] :
    IsFiniteKernel (pi κ) := by
  refine ⟨⟨∏ i, (κ i).bound, ENNReal.prod_lt_top fun i _ => (κ i).bound_lt_top,
    fun x => ?_⟩⟩
  rw [← pi_univ, pi_apply_pi]
  exact Finset.prod_le_prod fun i _ => (κ i).measure_le_bound x univ

/-- The product of Markov kernels is a Markov kernel. -/
instance isMarkovKernel_pi (κ : (i : ι) → Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (pi κ) :=
  ⟨fun x => by rw [pi_apply]; infer_instance⟩

variable {Y' : Type*} [MeasurableSpace Y']

/-- The **`N`-fold i.i.d. power** of a finite kernel `κ : Kernel X Y'`:
`piConst N κ x = (κ x)^{⊗N}`, the law of `N` independent draws from `κ x` (the law may depend
on the input `x`). -/
noncomputable def piConst (N : ℕ) (κ : Kernel X Y') [IsFiniteKernel κ] :
    Kernel X (Fin N → Y') :=
  pi fun _ : Fin N => κ

/-- Evaluation of the i.i.d. power: `piConst N κ x = Measure.pi (fun _ : Fin N => κ x)`. -/
theorem piConst_apply (N : ℕ) (κ : Kernel X Y') [IsFiniteKernel κ] (x : X) :
    piConst N κ x = Measure.pi fun _ : Fin N => κ x := rfl

/-- The `N`-fold power of a finite kernel is a finite kernel. -/
instance isFiniteKernel_piConst (N : ℕ) (κ : Kernel X Y') [IsFiniteKernel κ] :
    IsFiniteKernel (piConst N κ) :=
  isFiniteKernel_pi _

/-- The `N`-fold power of a Markov kernel is a Markov kernel. -/
instance isMarkovKernel_piConst (N : ℕ) (κ : Kernel X Y') [IsMarkovKernel κ] :
    IsMarkovKernel (piConst N κ) :=
  isMarkovKernel_pi _

end FormalizeSampling.KernelPi
