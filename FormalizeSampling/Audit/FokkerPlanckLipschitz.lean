module

public import FormalizeSampling.Flow.FokkerPlanckUniquenessLipschitz

/-!
# Statement audit: Fokker–Planck well-posedness for globally Lipschitz drift (FL-6)

Non-vacuity witnesses for `FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_lipschitz` and
`FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_lipschitz_continuousTime`. Every
hypothesis (global Lipschitz bound, joint continuity, `D > 0`, a probability initial law) is
proved for concrete drifts on `Fin d → ℝ` (sup norm):

* `sinDrift x = -x + sin x` (coordinatewise): smooth, `2`-Lipschitz, **unbounded** for `d ≥ 1`
  (`not_bounded_sinDrift`), so the bounded-drift uniqueness theorem does not apply to it;
* `kinkDrift x = |x| - 2x` (coordinatewise): `3`-Lipschitz, not differentiable at `0`, and
  **not of the form `-a x + bounded`** for any real `a` (`not_linear_add_bounded_kinkDrift`),
  so the rescaling argument for `-a x + b₀` drifts does not apply either;
* `timeDrift t x = -x + sin (t + x)`: time-dependent, jointly continuous, `2`-Lipschitz in `x`.

## Main results

* `lipschitzWith_sinDrift`, `not_bounded_sinDrift`, `sinDrift_wellPosed`: for every `D > 0` and
  every initial probability law, the weak Fokker–Planck equation with drift `-x + sin x` has a
  probability solution, the weak limit of the dyadic Euler–Maruyama laws, and it is the only
  probability solution on `t ≥ 0`.
* `lipschitzWith_kinkDrift`, `not_linear_add_bounded_kinkDrift`, `kinkDrift_wellPosed_dirac`:
  the same for `|x| - 2x` started at the point mass `δ_0` (no Lebesgue density) with `D = 1`.
* `continuous_timeDrift`, `lipschitzWith_timeDrift`, `timeDrift_wellPosed`: the time-dependent
  statement for `-x + sin (t + x)`.

## Not proved here

* No property of the solution beyond what the headline theorems give (no closed form, no
  moment or density statement); the witness only shows that the hypotheses are satisfiable by
  drifts outside the bounded class (`sinDrift`) and outside the `-a x + bounded` class
  (`kinkDrift`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace FormalizeSampling.Audit.FokkerPlanckLipschitz

open FormalizeSampling.NoiseScore FormalizeSampling.FokkerPlanckExistence
  FormalizeSampling.FokkerPlanckUniqueness

variable {d : ℕ}

/-- The drift `b(x)ᵢ = -xᵢ + sin xᵢ` on `Fin d → ℝ`. -/
noncomputable def sinDrift (x : Fin d → ℝ) : Fin d → ℝ := fun i => -x i + Real.sin (x i)

/-- The drift `b(x)ᵢ = |xᵢ| - 2 xᵢ` on `Fin d → ℝ` (`-x` for `xᵢ > 0`, `-3x` for `xᵢ < 0`). -/
noncomputable def kinkDrift (x : Fin d → ℝ) : Fin d → ℝ := fun i => |x i| - 2 * x i

/-- The time-dependent drift `b(t, x)ᵢ = -xᵢ + sin (t + xᵢ)`. -/
noncomputable def timeDrift (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => -x i + Real.sin (t + x i)

/-- A coordinatewise map is `K`-Lipschitz for the sup norm when every coordinate is:
`|f(x)ᵢ - f(y)ᵢ| ≤ K |xᵢ - yᵢ|`. -/
theorem lipschitzWith_of_coord {f : (Fin d → ℝ) → Fin d → ℝ} {K : NNReal}
    (h : ∀ x y i, |f x i - f y i| ≤ K * |x i - y i|) : LipschitzWith K f :=
  LipschitzWith.of_dist_le_mul fun x y => (dist_pi_le_iff (by positivity)).2 fun i => by
    rw [Real.dist_eq]
    exact (h x y i).trans (mul_le_mul_of_nonneg_left
      (by rw [← Real.dist_eq]; exact dist_le_pi_dist x y i) K.2)

/-- `-x + sin x` is `2`-Lipschitz (`|sin x - sin y| ≤ |x - y|`). -/
theorem lipschitzWith_sinDrift : LipschitzWith 2 (sinDrift (d := d)) :=
  lipschitzWith_of_coord fun x y i => by
    simp only [sinDrift, NNReal.coe_ofNat]
    have := Real.abs_sin_sub_sin_le (x i) (y i)
    calc |-x i + Real.sin (x i) - (-y i + Real.sin (y i))|
        = |-(x i - y i) + (Real.sin (x i) - Real.sin (y i))| := by ring_nf
      _ ≤ |-(x i - y i)| + |Real.sin (x i) - Real.sin (y i)| := abs_add_le _ _
      _ ≤ 2 * |x i - y i| := by rw [abs_neg]; linarith

/-- `-x + sin x` is unbounded on `Fin d → ℝ` for `d ≥ 1`: no `C` bounds `‖b(x)‖`. -/
theorem not_bounded_sinDrift (hd : 0 < d) : ¬ ∃ C : ℝ, ∀ x, ‖sinDrift (d := d) x‖ ≤ C := by
  rintro ⟨C, hC⟩
  set i₀ : Fin d := ⟨0, hd⟩
  have h := (norm_le_pi_norm (sinDrift (fun _ => -(|C| + 2)) ) i₀).trans
    (hC fun _ => -(|C| + 2))
  simp only [sinDrift, neg_neg, Real.norm_eq_abs] at h
  have h1 := Real.sin_le_one (-(|C| + 2))
  have h2 := Real.neg_one_le_sin (-(|C| + 2))
  have h3 : |C| + 2 + Real.sin (-(|C| + 2)) ≤ C := (le_abs_self _).trans h
  linarith [le_abs_self C]

/-- `|x| - 2x` is `3`-Lipschitz. -/
theorem lipschitzWith_kinkDrift : LipschitzWith 3 (kinkDrift (d := d)) :=
  lipschitzWith_of_coord fun x y i => by
    simp only [kinkDrift, NNReal.coe_ofNat]
    have := abs_abs_sub_abs_le_abs_sub (x i) (y i)
    calc |(|x i| - 2 * x i) - (|y i| - 2 * y i)|
        = |(|x i| - |y i|) + (-2) * (x i - y i)| := by ring_nf
      _ ≤ |(|x i| - |y i|)| + |(-2) * (x i - y i)| := abs_add_le _ _
      _ ≤ 3 * |x i - y i| := by rw [abs_mul]; norm_num; linarith

/-- `|x| - 2x` is not a linear drift plus a bounded one: for `d ≥ 1` there are no `a, C` with
`‖b(x) + a x‖ ≤ C` for all `x` (on `x > 0` this needs `a = 1`, on `x < 0` it needs `a = 3`). -/
theorem not_linear_add_bounded_kinkDrift (hd : 0 < d) :
    ¬ ∃ a C : ℝ, ∀ x : Fin d → ℝ, ‖kinkDrift x + a • x‖ ≤ C := by
  rintro ⟨a, C, hC⟩
  set i₀ : Fin d := ⟨0, hd⟩
  set M : ℝ := |C| + 1
  have hM : 0 < M := by positivity
  have key : ∀ c : ℝ, |(|c| - 2 * c + a * c)| ≤ C := fun c => by
    have := (norm_le_pi_norm (kinkDrift (fun _ => c) + a • fun _ => c) i₀).trans
      (hC fun _ => c)
    simpa [kinkDrift] using this
  have hp := key M
  have hn := key (-M)
  rw [abs_of_pos hM, show M - 2 * M + a * M = (a - 1) * M by ring, abs_mul,
    abs_of_pos hM] at hp
  rw [abs_neg, abs_of_pos hM, show M - 2 * -M + a * -M = (3 - a) * M by ring, abs_mul,
    abs_of_pos hM] at hn
  have htri : 2 ≤ |a - 1| + |3 - a| := by
    have := abs_add_le (a - 1) (3 - a)
    rw [show a - 1 + (3 - a) = 2 by ring, abs_two] at this
    exact this
  have : 2 * M ≤ 2 * C := by nlinarith
  linarith [le_abs_self C]

/-- The time-dependent drift `-x + sin (t + x)` is jointly continuous in `(t, x)`. -/
theorem continuous_timeDrift :
    Continuous fun p : ℝ × (Fin d → ℝ) => timeDrift p.1 p.2 :=
  continuous_pi fun i => by
    unfold timeDrift
    fun_prop

/-- `-x + sin (t + x)` is `2`-Lipschitz in `x` for every `t`. -/
theorem lipschitzWith_timeDrift (t : ℝ) : LipschitzWith 2 (timeDrift (d := d) t) :=
  lipschitzWith_of_coord fun x y i => by
    simp only [timeDrift, NNReal.coe_ofNat]
    have := Real.abs_sin_sub_sin_le (t + x i) (t + y i)
    rw [show t + x i - (t + y i) = x i - y i by ring] at this
    calc |-x i + Real.sin (t + x i) - (-y i + Real.sin (t + y i))|
        = |-(x i - y i) + (Real.sin (t + x i) - Real.sin (t + y i))| := by ring_nf
      _ ≤ |-(x i - y i)| + |Real.sin (t + x i) - Real.sin (t + y i)| := abs_add_le _ _
      _ ≤ 2 * |x i - y i| := by rw [abs_neg]; linarith

/-- **Witness, drift `-x + sin x`.** For every `D > 0` and every initial probability law `ρ₀`
on `Fin d → ℝ`: there is a curve of probability laws `ρ` with `ρ 0 = ρ₀` solving the weak
Fokker–Planck equation of `dX = (-X + sin X) dt + √(2D) dW`, it is the weak limit at every time
of the dyadic Euler–Maruyama laws, and every probability solution on `t ≥ 0` with the same
initial law equals it on `t ≥ 0`. For `d ≥ 1` the drift is unbounded. -/
theorem sinDrift_wellPosed {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    (0 < d → ¬ ∃ C : ℝ, ∀ x, ‖sinDrift (d := d) x‖ ≤ C) ∧
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => sinDrift) D ∧
      (∀ t (h : IsProbabilityMeasure (ρ t)),
        Tendsto (fun n => emCurveP sinDrift lipschitzWith_sinDrift.continuous.measurable D
          ρ₀ n t) atTop (𝓝 ⟨ρ t, h⟩)) ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) → WeakFokkerPlanck ρ' (fun _ => sinDrift) D →
          ∀ t, 0 ≤ t → ρ' t = ρ t :=
  ⟨not_bounded_sinDrift, existsUnique_weakFokkerPlanck_lipschitz lipschitzWith_sinDrift hD ρ₀⟩

/-- **Witness, drift `|x| - 2x` from a point mass.** With `D = 1` and `ρ₀ = δ_0` on
`Fin d → ℝ`, `d ≥ 1`: the drift is neither bounded nor linear plus bounded, and the weak
Fokker–Planck equation has exactly one probability solution on `t ≥ 0` started at `δ_0`, the
weak limit of the dyadic Euler–Maruyama laws. -/
theorem kinkDrift_wellPosed_dirac (hd : 0 < d) :
    (¬ ∃ a C : ℝ, ∀ x : Fin d → ℝ, ‖kinkDrift x + a • x‖ ≤ C) ∧
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = Measure.dirac 0 ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ (fun _ => kinkDrift) 1 ∧
      (∀ t (h : IsProbabilityMeasure (ρ t)),
        Tendsto (fun n => emCurveP kinkDrift lipschitzWith_kinkDrift.continuous.measurable 1
          (Measure.dirac 0) n t) atTop (𝓝 ⟨ρ t, h⟩)) ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = Measure.dirac 0 →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) →
          WeakFokkerPlanck ρ' (fun _ => kinkDrift) 1 → ∀ t, 0 ≤ t → ρ' t = ρ t :=
  ⟨not_linear_add_bounded_kinkDrift hd,
    existsUnique_weakFokkerPlanck_lipschitz lipschitzWith_kinkDrift one_pos _⟩

/-- **Witness, time-dependent drift `-x + sin (t + x)`.** For every `D > 0` and every initial
probability law `ρ₀`, the weak Fokker–Planck equation with this drift has a probability solution
with `ρ 0 = ρ₀`, and every probability solution on `t ≥ 0` with initial law `ρ₀` equals it on
`t ≥ 0`. -/
theorem timeDrift_wellPosed {D : ℝ} (hD : 0 < D) (ρ₀ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ρ₀] :
    ∃ ρ : ℝ → Measure (Fin d → ℝ), ρ 0 = ρ₀ ∧ (∀ t, IsProbabilityMeasure (ρ t)) ∧
      WeakFokkerPlanck ρ timeDrift D ∧
      ∀ ρ' : ℝ → Measure (Fin d → ℝ), ρ' 0 = ρ₀ →
        (∀ t, 0 ≤ t → IsProbabilityMeasure (ρ' t)) → WeakFokkerPlanck ρ' timeDrift D →
          ∀ t, 0 ≤ t → ρ' t = ρ t :=
  existsUnique_weakFokkerPlanck_lipschitz_continuousTime continuous_timeDrift
    (fun _ => ⟨2, fun t _ => lipschitzWith_timeDrift t⟩) hD ρ₀

end FormalizeSampling.Audit.FokkerPlanckLipschitz
