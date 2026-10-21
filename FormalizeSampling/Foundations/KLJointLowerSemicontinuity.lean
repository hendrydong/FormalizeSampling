module

public import FormalizeSampling.Foundations.KLLowerSemicontinuity

/-!
# Joint lower semicontinuity of the KL divergence under weak convergence

Status: **Verified** (no named hypotheses).

Let `ρ, π` and `μ_i, π_i` be probability laws on a pseudo-metric Borel space `α`. If
`∫ f dμ_i → ∫ f dρ` and `∫ f dπ_i → ∫ f dπ` for every bounded continuous `f` (weak convergence
of both arguments), then `KL(ρ‖π) ≤ liminf_i KL(μ_i‖π_i)` in `ℝ≥0∞`.

## Main results

* `klDiv_le_liminf_of_tendsto_integral₂`: joint lower semicontinuity of KL.

The proof is the Donsker–Varadhan argument of `Foundations/KLLowerSemicontinuity.lean`: for a
bounded continuous `f`, `∫ e^f dπ_i → ∫ e^f dπ > 0`, so the Donsker–Varadhan functional
`∫ f dμ_i - log ∫ e^f dπ_i` converges to `∫ f dρ - log ∫ e^f dπ`.

## Not proved here

* The Donsker–Varadhan variational formula as an equality.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FormalizeSampling.KLLowerSemicontinuity

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]

/-- **Joint lower semicontinuity of KL under weak convergence.** On a pseudo-metric Borel space,
let `ρ, π`, `μ_i` and `π_i` be probability laws. If `∫ f dμ_i → ∫ f dρ` and
`∫ f dπ_i → ∫ f dπ` along a filter `l` for every bounded continuous `f`, then
`KL(ρ‖π) ≤ liminf_l KL(μ_i‖π_i)` in `ℝ≥0∞` (including `KL(ρ‖π) = ∞`). -/
theorem klDiv_le_liminf_of_tendsto_integral₂ {ρ π : Measure α} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure π] {ι : Type*} {l : Filter ι} {μ π' : ι → Measure α}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (π' i)]
    (h : ∀ f : α → ℝ, Continuous f → ∀ N : ℝ, (∀ x, |f x| ≤ N) →
      Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ρ)))
    (h' : ∀ f : α → ℝ, Continuous f → ∀ N : ℝ, (∀ x, |f x| ≤ N) →
      Tendsto (fun i => ∫ x, f x ∂π' i) l (𝓝 (∫ x, f x ∂π))) :
    klDiv ρ π ≤ liminf (fun i => klDiv (μ i) (π' i)) l := by
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨q, hcq, hqK⟩ := exists_between hc
  have hq : q ≠ ∞ := ne_top_of_lt hqK
  have hb : ENNReal.ofReal q.toReal < klDiv ρ π := by rwa [ENNReal.ofReal_toReal hq]
  obtain ⟨f, N, hf, -, hfN, hlt⟩ := exists_continuous_lt_dvValue hb
  have hexpN : ∀ x, |Real.exp (f x)| ≤ Real.exp N := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_of_abs_le (hfN x))
  have hpos : 0 < ∫ x, Real.exp (f x) ∂π :=
    integral_exp_pos (integrable_exp_of_abs_le hf.measurable hfN)
  have hlog : Tendsto (fun i => Real.log (∫ x, Real.exp (f x) ∂π' i)) l
      (𝓝 (Real.log (∫ x, Real.exp (f x) ∂π))) :=
    (h' _ (Real.continuous_exp.comp hf) _ hexpN).log hpos.ne'
  have hev : ∀ᶠ i in l, q.toReal < dvValue (μ i) (π' i) f :=
    ((h f hf N hfN).sub hlog).eventually (lt_mem_nhds hlt)
  refine hcq.trans_le (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [hev] with i hi
  rw [← ENNReal.ofReal_toReal hq]
  exact (ENNReal.ofReal_le_ofReal hi.le).trans (ofReal_dvValue_le_klDiv hf.measurable hfN)

end FormalizeSampling.KLLowerSemicontinuity
