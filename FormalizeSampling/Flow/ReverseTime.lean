module

public import Mathlib.Order.CompletePartialOrder
public import FormalizeSampling.Foundations.VectorCalculus

/-!
# Reverse-time Fokker–Planck equations and probability-flow rewriting (strong form)

Registry IDs: **S06** (reverse-time score identities) and **FS-PF-strong** (pointwise
probability-flow rewriting of the Fokker–Planck right-hand side).

This file proves *pointwise* (strong-form) PDE identities. It contains no SDE theory, no
integrals and no measure theory: every statement is an identity between derivatives of
explicitly given functions, with every derivative hypothesis stated explicitly.

## Conventions

* Time is the first argument: `p t x = p(t, x)`, `b t x = b(t, x)`.
* **Forward Fokker–Planck equation, scalar diffusion (1D).** For
  `dX = b(t, X) dt + g(t) dW` the (strong) forward equation is
  `∂ₜ p = -∂ₓ (b p) + (g² / 2) ∂ₓₓ p`. Its right-hand side is `fpRHS1 b g p t x`, written with
  `deriv`. "`p` satisfies the forward equation" is the explicit hypothesis
  `∀ t x, HasDerivAt (fun t => p t x) (fpRHS1 b g p t x) t`; it is a modelling assumption
  (we never derive it from an SDE).
* **Time reversal.** For a horizon `T`, reverse time is `s = T - t` and the reversed density
  is `q(s, x) = p(T - s, x)` (`timeReversal T p`). The reverse diffusion coefficient is
  `ḡ(s) = g(T - s)` and the reverse drift is
  `b̄(s, x) = -b(T - s, x) + g(T - s)² · (log p(T - s, ·))'(x)` (`reverseDrift1`).
  Note both signs: the forward drift enters with a minus sign, the score correction with a
  plus sign and the *full* factor `g²` (not `g² / 2`).
* **Probability-flow velocity.** `v(t, x) = b(t, x) - (g(t)² / 2) · (log p(t, ·))'(x)`
  (`pfVelocity1`); the Fokker–Planck right-hand side equals `-∂ₓ (v p)` (a continuity
  equation), see `fpRHS1_eq_neg_deriv_pfVelocity1`.
* **State-dependent diffusion (1D).** For `dX = b(t, X) dt + σ(t, X) dW` with `a = σ²` the
  forward equation is `∂ₜ p = -∂ₓ (b p) + (1/2) ∂ₓₓ (a p)` (`fpRHSStateDep1`). The reverse
  drift is `-b + ∂ₓ (a p) / p = -b + ∂ₓ a + a · (log p)'` (`reverseDriftFlux1`,
  `reverseDriftStateDep1`); the extra divergence term `∂ₓ a` vanishes when `a` does not
  depend on the state (`reverseDriftStateDep1_of_const`).
* **d dimensions, scalar diffusion.** On `Fin d → ℝ` the forward right-hand side is
  `-div (b p) + (g² / 2) Δ p` (`fpRHS`), with `divergence`, `laplacian`, `partialDeriv` and
  the state score `score p = ∇ₓ log p` from `FormalizeSampling.Foundations.VectorCalculus`.
  The reverse drift is `b̄(s, x) = -b(T - s, x) + g(T - s)² ∇ₓ log p(T - s, x)`
  (`reverseDrift`).

Positivity of `p` is assumed wherever `log p` is used (so the Lean junk value `Real.log 0 = 0`
never enters); differentiability is assumed wherever `deriv`/`fderiv` is used (so the junk
value "derivative of a non-differentiable function is `0`" never enters). Local
(`∀ᶠ y in 𝓝 x`) versions are proved first; global corollaries follow.

## Main results

* `probFlow_rewrite1`, `fpRHS1_eq_neg_deriv_pfVelocity1` (FS-PF-strong, 1D):
  `-∂ₓ(b p) + (g²/2) ∂ₓₓ p = -∂ₓ((b - (g²/2) (log p)') p)`.
* `reverse_fokkerPlanck1_at`, `reverse_fokkerPlanck1` (S06, 1D): if `p` solves the forward
  equation then `q(s, x) = p(T - s, x)` solves `∂ₛ q = -∂ₓ(b̄ q) + (ḡ²/2) ∂ₓₓ q`.
* `reverseDrift1_reverseDrift1`, `timeReversal_timeReversal`: reversing twice gives back
  the forward drift and the forward density; `reverse_fokkerPlanck1_iff`: under the same
  spatial hypotheses the forward and reverse equations are equivalent.
* `deriv_mul_div_eq_add_score1`, `reverseDriftFlux1_eq_reverseDriftStateDep1`,
  `probFlow_rewriteStateDep1`, `reverse_fokkerPlanckStateDep1_at`,
  `reverse_fokkerPlanckStateDep1`, `reverse_fokkerPlanckStateDep1_flux` (S06,
  state-dependent diffusion, 1D).
* `fpRHSStateDep1_of_const`, `reverseDriftStateDep1_of_const`: consistency with the scalar
  case `a(t, x) = g(t)²`.
* `probFlow_rewrite`, `probFlow_rewrite_of_contDiff`, `fpRHS_eq_neg_divergence_pfVelocity`
  (FS-PF-strong, d-dim, scalar `g`).
* `reverse_fokkerPlanck_at`, `reverse_fokkerPlanck`, `reverseDrift_reverseDrift`,
  `reverse_fokkerPlanck_iff` (S06, d-dim, scalar `g`).
* `ouDensity_fokkerPlanck`, `ou_reverse_fokkerPlanck`, `ou_reverseDrift1_eq` (sanity
  example): the stationary Ornstein–Uhlenbeck density `exp(-x²/2)` with `b = -x/2`, `g = 1`
  satisfies every hypothesis of `reverse_fokkerPlanck1`, so those hypotheses are jointly
  satisfiable, and its reverse drift equals the forward drift (reversibility).

## What is NOT proved here

* No stochastic calculus: nothing about SDEs, Brownian motion, path laws or a *pathwise*
  reverse-SDE theorem (Anderson / Haussmann–Pardoux). The results are the marginal
  (Fokker–Planck) statements behind the reverse SDE and the probability-flow ODE only.
* The forward Fokker–Planck equation is a hypothesis; we do not derive it from an SDE.
* No weak / integral form, no boundary or decay conditions, no existence, uniqueness or
  well-posedness of any PDE, and no statement that the law of a reverse process is `q`.
* No conservation of mass or normalisation of `p` (the identities do not need it).
* State-dependent (matrix) diffusion is treated only in 1D; the d-dimensional results use a
  scalar, state-independent diffusion coefficient `g(t)`.
* Joint (space-time) regularity is never needed or proved: only the time derivative at each
  fixed `x` and spatial derivatives at each fixed `t` appear.
* The global theorems quantify over all `t : ℝ` and assume `p > 0` on the whole state space;
  for a solution living only on a time interval (e.g. `(0, T)`) use the pointwise `_at`
  versions, which need the hypotheses only at the single time `T - s` and near `x`.
* Ellipticity `a > 0` of the state-dependent diffusion is *not* assumed: the identities are
  algebraic and hold without it (it matters only for well-posedness, which is not treated).
* The only discharged example is the *stationary* OU density; no time-dependent closed-form
  solution (e.g. a Gaussian heat kernel) is verified here.
-/

@[expose] public section

open Filter Topology

namespace FormalizeSampling

namespace ReverseTime

/-! ## Private calculus helpers -/

private lemma deriv_lincomb {f h : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (c₁ c₂ : ℝ) :
    deriv (fun y => c₁ * f y + c₂ * h y) x = c₁ * deriv f x + c₂ * deriv h x := by
  rw [deriv_fun_add (hf.const_mul c₁) (hh.const_mul c₂), deriv_const_mul _ hf,
    deriv_const_mul _ hh]

private lemma score1_mul_self {p : ℝ → ℝ} {y : ℝ} (hp : DifferentiableAt ℝ p y)
    (hpos : 0 < p y) : score1 p y * p y = deriv p y := by
  rw [score1_of_pos hp hpos]; field_simp

/-! ## Definitions (1D) -/

/-- Time reversal with horizon `T`: `timeReversal T p s x = p (T - s) x`, i.e. the reversed
function `q(s, x) = p(T - s, x)` in reverse time `s = T - t`. -/
def timeReversal {α β : Type*} (T : ℝ) (p : ℝ → α → β) (s : ℝ) : α → β :=
  p (T - s)

/-- Right-hand side of the 1D forward Fokker–Planck equation for
`dX = b(t, X) dt + g(t) dW`:
`fpRHS1 b g p t x = -∂ₓ (b(t, ·) p(t, ·))(x) + (g(t)² / 2) ∂ₓₓ p(t, x)`,
with derivatives written via `deriv` (meaningful where the functions are differentiable). -/
noncomputable def fpRHS1 (b : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (p : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -deriv (fun y => b t y * p t y) x + g t ^ 2 / 2 * deriv (deriv (p t)) x

/-- The 1D reverse-time drift with horizon `T`:
`b̄(s, x) = -b(T - s, x) + g(T - s)² · (log p(T - s, ·))'(x)`. -/
noncomputable def reverseDrift1 (T : ℝ) (b : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (p : ℝ → ℝ → ℝ)
    (s x : ℝ) : ℝ :=
  -b (T - s) x + g (T - s) ^ 2 * score1 (p (T - s)) x

/-- The 1D probability-flow velocity `v(t, x) = b(t, x) - (g(t)² / 2) · (log p(t, ·))'(x)`. -/
noncomputable def pfVelocity1 (b : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (p : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  b t x - g t ^ 2 / 2 * score1 (p t) x

/-! ## (a) Probability-flow rewriting, 1D -/

/-- **Probability-flow rewriting (1D, one time slice).** Let `p b : ℝ → ℝ` and `g : ℝ`.
Assume that on a neighbourhood of `x` the function `p` is differentiable and positive, that
`p'` is differentiable at `x`, and that `b` is differentiable at `x`. Then
`-(b p)'(x) + (g² / 2) p''(x) = -((b - (g² / 2) (log p)') p)'(x)`. -/
theorem probFlow_rewrite1 {p b : ℝ → ℝ} {x : ℝ} (g : ℝ)
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ p y ∧ 0 < p y)
    (hp' : DifferentiableAt ℝ (deriv p) x) (hb : DifferentiableAt ℝ b x) :
    -deriv (fun y => b y * p y) x + g ^ 2 / 2 * deriv (deriv p) x
      = -deriv (fun y => (b y - g ^ 2 / 2 * score1 p y) * p y) x := by
  have hev : (fun y => (b y - g ^ 2 / 2 * score1 p y) * p y)
      =ᶠ[𝓝 x] fun y => 1 * (b y * p y) + (-(g ^ 2 / 2)) * deriv p y :=
    hp.mono fun y hy => by
      have h := score1_mul_self hy.1 hy.2
      linear_combination (-(g ^ 2 / 2)) * h
  rw [hev.deriv_eq, deriv_lincomb (hb.fun_mul hp.self_of_nhds.1) hp']
  ring

/-- **Probability-flow form of the 1D Fokker–Planck right-hand side.** If, at time `t`,
`p(t, ·)` is differentiable and positive near `x`, `∂ₓ p(t, ·)` is differentiable at `x` and
`b(t, ·)` is differentiable at `x`, then
`fpRHS1 b g p t x = -∂ₓ (v(t, ·) p(t, ·))(x)` with `v = pfVelocity1 b g p`
(`v = b - (g²/2) (log p)'`). -/
theorem fpRHS1_eq_neg_deriv_pfVelocity1 {p b : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {t x : ℝ}
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (p t) y ∧ 0 < p t y)
    (hp' : DifferentiableAt ℝ (deriv (p t)) x) (hb : DifferentiableAt ℝ (b t) x) :
    fpRHS1 b g p t x = -deriv (fun y => pfVelocity1 b g p t y * p t y) x :=
  probFlow_rewrite1 (g t) hp hp' hb

/-! ## (b) Reverse-time Fokker–Planck equation, 1D, scalar diffusion -/

/-- **Reverse-time Fokker–Planck equation (1D, pointwise version).** Fix `T, s, x` and put
`t = T - s`. Assume the forward equation holds at `(t, x)`:
`HasDerivAt (fun t => p t x) (fpRHS1 b g p t x) t`; that `p(t, ·)` is differentiable and
positive near `x`; that `∂ₓ p(t, ·)` and `b(t, ·)` are differentiable at `x`. Then
`q = timeReversal T p` (`q(s, x) = p(T - s, x)`) satisfies, at `(s, x)`,
`∂ₛ q = -∂ₓ (b̄ q) + (ḡ² / 2) ∂ₓₓ q` with `b̄ = reverseDrift1 T b g p`
(`b̄(s, x) = -b(T - s, x) + g(T - s)² (log p(T - s, ·))'(x)`) and `ḡ(s) = g(T - s)`. -/
theorem reverse_fokkerPlanck1_at {p b : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {T s x : ℝ}
    (hFP : HasDerivAt (fun t => p t x) (fpRHS1 b g p (T - s) x) (T - s))
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (p (T - s)) y ∧ 0 < p (T - s) y)
    (hp' : DifferentiableAt ℝ (deriv (p (T - s))) x)
    (hb : DifferentiableAt ℝ (b (T - s)) x) :
    HasDerivAt (fun s => timeReversal T p s x)
      (fpRHS1 (reverseDrift1 T b g p) (fun s => g (T - s)) (timeReversal T p) s x) s := by
  convert hFP.comp_const_sub T s using 1
  · rfl
  have hev : (fun y => (-b (T - s) y + g (T - s) ^ 2 * score1 (p (T - s)) y) * p (T - s) y)
      =ᶠ[𝓝 x] fun y => (-1) * (b (T - s) y * p (T - s) y)
        + g (T - s) ^ 2 * deriv (p (T - s)) y :=
    hp.mono fun y hy => by
      have h := score1_mul_self hy.1 hy.2
      linear_combination g (T - s) ^ 2 * h
  simp only [fpRHS1, reverseDrift1, timeReversal]
  rw [hev.deriv_eq, deriv_lincomb (hb.fun_mul hp.self_of_nhds.1) hp']
  ring

/-- **Reverse-time Fokker–Planck equation (1D, global version).** Assume `p` satisfies the
forward equation `∂ₜ p = -∂ₓ (b p) + (g² / 2) ∂ₓₓ p` strongly at every `(t, x)`, that every
`p(t, ·)` is positive and differentiable with differentiable derivative `∂ₓ p(t, ·)`, and
that every `b(t, ·)` is differentiable. Then for every horizon `T`, the reversed function
`q(s, x) = p(T - s, x)` satisfies at every `(s, x)`
`∂ₛ q = -∂ₓ (b̄ q) + (ḡ² / 2) ∂ₓₓ q`, with
`b̄(s, x) = -b(T - s, x) + g(T - s)² (log p(T - s, ·))'(x)` and `ḡ(s) = g(T - s)`.
This is the marginal (Fokker–Planck) statement behind the reverse SDE, not a pathwise
theorem. -/
theorem reverse_fokkerPlanck1 {p b : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (T : ℝ)
    (hFP : ∀ t x, HasDerivAt (fun t => p t x) (fpRHS1 b g p t x) t)
    (hp : ∀ t, Differentiable ℝ (p t)) (hpos : ∀ t y, 0 < p t y)
    (hp' : ∀ t, Differentiable ℝ (deriv (p t))) (hb : ∀ t, Differentiable ℝ (b t)) :
    ∀ s x, HasDerivAt (fun s => timeReversal T p s x)
      (fpRHS1 (reverseDrift1 T b g p) (fun s => g (T - s)) (timeReversal T p) s x) s :=
  fun s x => reverse_fokkerPlanck1_at (hFP (T - s) x)
    (Eventually.of_forall fun y => ⟨hp (T - s) y, hpos (T - s) y⟩) (hp' (T - s) x)
    (hb (T - s) x)

/-- **Reversing twice gives back the forward drift (1D).** For any `b, g, p` (no hypotheses),
the reverse drift of the reversed data `(b̄, ḡ, q) = (reverseDrift1 T b g p, g(T - ·),
timeReversal T p)` is `b` again: the score corrections `∓ g² (log p)'` cancel exactly. -/
theorem reverseDrift1_reverseDrift1 (T : ℝ) (b : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (p : ℝ → ℝ → ℝ) :
    reverseDrift1 T (reverseDrift1 T b g p) (fun s => g (T - s)) (timeReversal T p) = b := by
  funext t x
  simp [reverseDrift1, timeReversal, sub_sub_cancel]

/-- **Time reversal is an involution.** `q(s) = p(T - s)` reversed again with the same
horizon `T` is `p`: `timeReversal T (timeReversal T p) = p`. -/
theorem timeReversal_timeReversal {α β : Type*} (T : ℝ) (p : ℝ → α → β) :
    timeReversal T (timeReversal T p) = p := by
  funext t
  simp [timeReversal, sub_sub_cancel]

/-- Under positivity and differentiability of `p` and `p'`, the 1D score `(log p)'` is the
differentiable function `p' / p`, hence the reverse drift is differentiable in space. -/
private lemma differentiable_reverseDrift1 {p b : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (T s : ℝ)
    (hp : ∀ t, Differentiable ℝ (p t)) (hpos : ∀ t y, 0 < p t y)
    (hp' : ∀ t, Differentiable ℝ (deriv (p t))) (hb : ∀ t, Differentiable ℝ (b t)) :
    Differentiable ℝ (reverseDrift1 T b g p s) := by
  have hscore : score1 (p (T - s)) = fun y => deriv (p (T - s)) y / p (T - s) y :=
    funext fun y => score1_of_pos (hp (T - s) y) (hpos (T - s) y)
  have hd : Differentiable ℝ (fun y => deriv (p (T - s)) y / p (T - s) y) :=
    (hp' (T - s)).div (hp (T - s)) fun y => (hpos (T - s) y).ne'
  unfold reverseDrift1
  rw [hscore]
  exact ((hb (T - s)).neg).add (hd.const_mul _)

/-- **Forward and reverse 1D Fokker–Planck equations are equivalent.** Under the global
spatial hypotheses of `reverse_fokkerPlanck1` (every `p(t, ·)` positive and differentiable
with differentiable `∂ₓ p(t, ·)`, every `b(t, ·)` differentiable), `p` satisfies
`∂ₜ p = -∂ₓ (b p) + (g² / 2) ∂ₓₓ p` at every `(t, x)` **if and only if**
`q(s, x) = p(T - s, x)` satisfies `∂ₛ q = -∂ₓ (b̄ q) + (ḡ² / 2) ∂ₓₓ q` at every `(s, x)`,
with `b̄ = reverseDrift1 T b g p` and `ḡ(s) = g(T - s)`. The converse direction applies the
forward-to-reverse theorem to `q` and uses `reverseDrift1_reverseDrift1`. -/
theorem reverse_fokkerPlanck1_iff {p b : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (T : ℝ)
    (hp : ∀ t, Differentiable ℝ (p t)) (hpos : ∀ t y, 0 < p t y)
    (hp' : ∀ t, Differentiable ℝ (deriv (p t))) (hb : ∀ t, Differentiable ℝ (b t)) :
    (∀ t x, HasDerivAt (fun t => p t x) (fpRHS1 b g p t x) t) ↔
      ∀ s x, HasDerivAt (fun s => timeReversal T p s x)
        (fpRHS1 (reverseDrift1 T b g p) (fun s => g (T - s)) (timeReversal T p) s x) s := by
  refine ⟨fun hFP => reverse_fokkerPlanck1 T hFP hp hpos hp' hb, fun hRev => ?_⟩
  have h := reverse_fokkerPlanck1 (p := timeReversal T p) (b := reverseDrift1 T b g p)
    (g := fun s => g (T - s)) T hRev (fun s => hp (T - s)) (fun s => hpos (T - s))
    (fun s => hp' (T - s)) (fun s => differentiable_reverseDrift1 T s hp hpos hp' hb)
  rw [reverseDrift1_reverseDrift1, timeReversal_timeReversal] at h
  simpa only [sub_sub_cancel] using h

/-! ## (c) State-dependent diffusion, 1D -/

/-- Right-hand side of the 1D forward Fokker–Planck equation with state-dependent diffusion,
for `dX = b(t, X) dt + σ(t, X) dW` and `a = σ²`:
`fpRHSStateDep1 b a p t x = -∂ₓ (b p)(t, x) + (1/2) ∂ₓₓ (a p)(t, x)`. -/
noncomputable def fpRHSStateDep1 (b a p : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -deriv (fun y => b t y * p t y) x + 1 / 2 * deriv (deriv (fun y => a t y * p t y)) x

/-- The 1D reverse drift with state-dependent diffusion in *flux form*:
`b̄(s, x) = -b(T - s, x) + ∂ₓ (a p)(T - s, x) / p(T - s, x)`. -/
noncomputable def reverseDriftFlux1 (T : ℝ) (b a p : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  -b (T - s) x + deriv (fun y => a (T - s) y * p (T - s) y) x / p (T - s) x

/-- The 1D reverse drift with state-dependent diffusion in *score form*:
`b̄(s, x) = -b(T - s, x) + ∂ₓ a(T - s, x) + a(T - s, x) · (log p(T - s, ·))'(x)`.
The middle term `∂ₓ a` is the extra divergence term that is absent for state-independent
diffusion. -/
noncomputable def reverseDriftStateDep1 (T : ℝ) (b a p : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  -b (T - s) x + deriv (a (T - s)) x + a (T - s) x * score1 (p (T - s)) x

/-- **Flux over density equals divergence term plus score term.** If `a` and `p` are
differentiable at `x` and `p x > 0`, then `(a p)'(x) / p(x) = a'(x) + a(x) (log p)'(x)`. -/
theorem deriv_mul_div_eq_add_score1 {a p : ℝ → ℝ} {x : ℝ} (ha : DifferentiableAt ℝ a x)
    (hp : DifferentiableAt ℝ p x) (hpos : 0 < p x) :
    deriv (fun y => a y * p y) x / p x = deriv a x + a x * score1 p x := by
  rw [deriv_fun_mul ha hp, score1_of_pos hp hpos]
  field_simp

/-- **Flux form equals score form of the state-dependent reverse drift.** If, at time
`t = T - s`, the functions `a(t, ·)` and `p(t, ·)` are differentiable at `x` and
`p(t, x) > 0`, then
`-b + ∂ₓ (a p) / p = -b + ∂ₓ a + a (log p)'` at `(s, x)`. -/
theorem reverseDriftFlux1_eq_reverseDriftStateDep1 {b a p : ℝ → ℝ → ℝ} {T s x : ℝ}
    (ha : DifferentiableAt ℝ (a (T - s)) x) (hp : DifferentiableAt ℝ (p (T - s)) x)
    (hpos : 0 < p (T - s) x) :
    reverseDriftFlux1 T b a p s x = reverseDriftStateDep1 T b a p s x := by
  rw [reverseDriftFlux1, reverseDriftStateDep1, deriv_mul_div_eq_add_score1 ha hp hpos]
  ring

/-- **Probability-flow rewriting with state-dependent diffusion (1D, one time slice).**
Assume that near `x` the functions `p` and `a` are differentiable and `p > 0`, that
`(a p)'` is differentiable at `x`, and that `b` is differentiable at `x`. Then
`-(b p)'(x) + (1/2) (a p)''(x) = -((b - (1/2) (a' + a (log p)')) p)'(x)`.
Positivity of `a` is not needed for this identity. -/
theorem probFlow_rewriteStateDep1 {p a b : ℝ → ℝ} {x : ℝ}
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ p y ∧ 0 < p y)
    (ha : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ a y)
    (hap : DifferentiableAt ℝ (deriv (fun y => a y * p y)) x) (hb : DifferentiableAt ℝ b x) :
    -deriv (fun y => b y * p y) x + 1 / 2 * deriv (deriv (fun y => a y * p y)) x
      = -deriv (fun y => (b y - 1 / 2 * (deriv a y + a y * score1 p y)) * p y) x := by
  have hev : (fun y => (b y - 1 / 2 * (deriv a y + a y * score1 p y)) * p y)
      =ᶠ[𝓝 x] fun y => 1 * (b y * p y) + (-(1 / 2)) * deriv (fun z => a z * p z) y :=
    (hp.and ha).mono fun y hy => by
      have h := score1_mul_self hy.1.1 hy.1.2
      beta_reduce
      rw [deriv_fun_mul hy.2 hy.1.1]
      linear_combination (-(1 / 2) * a y) * h
  rw [hev.deriv_eq, deriv_lincomb (hb.fun_mul hp.self_of_nhds.1) hap]
  ring

/-- **Reverse-time Fokker–Planck equation with state-dependent diffusion (1D, pointwise).**
Fix `T, s, x`, put `t = T - s`, and assume the forward equation
`∂ₜ p = -∂ₓ (b p) + (1/2) ∂ₓₓ (a p)` holds at `(t, x)`; that `p(t, ·)` is differentiable and
positive near `x`; that `a(t, ·)` is differentiable near `x`; that `∂ₓ (a(t, ·) p(t, ·))` and
`b(t, ·)` are differentiable at `x`. Then `q(s, x) = p(T - s, x)` satisfies at `(s, x)`
`∂ₛ q = -∂ₓ (b̄ q) + (1/2) ∂ₓₓ (ā q)` with `ā(s, x) = a(T - s, x)` and
`b̄ = reverseDriftStateDep1 T b a p`, i.e. `b̄ = -b + ∂ₓ a + a (log p)'` evaluated at
`(T - s, x)`; the term `∂ₓ a` is the extra divergence term. Positivity of `a` is not needed
for this identity. -/
theorem reverse_fokkerPlanckStateDep1_at {p a b : ℝ → ℝ → ℝ} {T s x : ℝ}
    (hFP : HasDerivAt (fun t => p t x) (fpRHSStateDep1 b a p (T - s) x) (T - s))
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (p (T - s)) y ∧ 0 < p (T - s) y)
    (ha : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (a (T - s)) y)
    (hap : DifferentiableAt ℝ (deriv (fun y => a (T - s) y * p (T - s) y)) x)
    (hb : DifferentiableAt ℝ (b (T - s)) x) :
    HasDerivAt (fun s => timeReversal T p s x)
      (fpRHSStateDep1 (reverseDriftStateDep1 T b a p) (timeReversal T a) (timeReversal T p)
        s x) s := by
  convert hFP.comp_const_sub T s using 1
  · rfl
  have hev : (fun y => (-b (T - s) y + deriv (a (T - s)) y
        + a (T - s) y * score1 (p (T - s)) y) * p (T - s) y)
      =ᶠ[𝓝 x] fun y => (-1) * (b (T - s) y * p (T - s) y)
        + 1 * deriv (fun z => a (T - s) z * p (T - s) z) y :=
    (hp.and ha).mono fun y hy => by
      have h := score1_mul_self hy.1.1 hy.1.2
      beta_reduce
      rw [deriv_fun_mul hy.2 hy.1.1]
      linear_combination a (T - s) y * h
  simp only [fpRHSStateDep1, reverseDriftStateDep1, timeReversal]
  rw [hev.deriv_eq, deriv_lincomb (hb.fun_mul hp.self_of_nhds.1) hap]
  ring

/-- **Reverse-time Fokker–Planck equation with state-dependent diffusion (1D, global).**
Assume `∂ₜ p = -∂ₓ (b p) + (1/2) ∂ₓₓ (a p)` holds strongly at every `(t, x)`, every
`p(t, ·)` is positive and differentiable, every `a(t, ·)` and `b(t, ·)` is differentiable and
every `∂ₓ (a(t, ·) p(t, ·))` is differentiable. Then `q(s, x) = p(T - s, x)` satisfies
`∂ₛ q = -∂ₓ (b̄ q) + (1/2) ∂ₓₓ (ā q)` everywhere, with `ā(s, x) = a(T - s, x)` and
`b̄(s, x) = -b(T - s, x) + ∂ₓ a(T - s, x) + a(T - s, x) (log p(T - s, ·))'(x)`. -/
theorem reverse_fokkerPlanckStateDep1 {p a b : ℝ → ℝ → ℝ} (T : ℝ)
    (hFP : ∀ t x, HasDerivAt (fun t => p t x) (fpRHSStateDep1 b a p t x) t)
    (hp : ∀ t, Differentiable ℝ (p t)) (hpos : ∀ t y, 0 < p t y)
    (ha : ∀ t, Differentiable ℝ (a t))
    (hap : ∀ t, Differentiable ℝ (deriv (fun y => a t y * p t y)))
    (hb : ∀ t, Differentiable ℝ (b t)) :
    ∀ s x, HasDerivAt (fun s => timeReversal T p s x)
      (fpRHSStateDep1 (reverseDriftStateDep1 T b a p) (timeReversal T a) (timeReversal T p)
        s x) s :=
  fun s x => reverse_fokkerPlanckStateDep1_at (hFP (T - s) x)
    (Eventually.of_forall fun y => ⟨hp (T - s) y, hpos (T - s) y⟩)
    (Eventually.of_forall fun y => ha (T - s) y) (hap (T - s) x) (hb (T - s) x)

/-- **Reverse-time equation with state-dependent diffusion, flux form of the drift (1D,
global).** Under the hypotheses of `reverse_fokkerPlanckStateDep1`, the reversed function
`q(s, x) = p(T - s, x)` satisfies `∂ₛ q = -∂ₓ (b̄ q) + (1/2) ∂ₓₓ (ā q)` everywhere with the
drift written as `b̄(s, x) = -b(T - s, x) + ∂ₓ (a p)(T - s, x) / p(T - s, x)`
(`reverseDriftFlux1`), which coincides with the score form `-b + ∂ₓ a + a (log p)'`. -/
theorem reverse_fokkerPlanckStateDep1_flux {p a b : ℝ → ℝ → ℝ} (T : ℝ)
    (hFP : ∀ t x, HasDerivAt (fun t => p t x) (fpRHSStateDep1 b a p t x) t)
    (hp : ∀ t, Differentiable ℝ (p t)) (hpos : ∀ t y, 0 < p t y)
    (ha : ∀ t, Differentiable ℝ (a t))
    (hap : ∀ t, Differentiable ℝ (deriv (fun y => a t y * p t y)))
    (hb : ∀ t, Differentiable ℝ (b t)) :
    ∀ s x, HasDerivAt (fun s => timeReversal T p s x)
      (fpRHSStateDep1 (reverseDriftFlux1 T b a p) (timeReversal T a) (timeReversal T p)
        s x) s := by
  have h : reverseDriftFlux1 T b a p = reverseDriftStateDep1 T b a p :=
    funext fun s => funext fun x => reverseDriftFlux1_eq_reverseDriftStateDep1
      (ha (T - s) x) (hp (T - s) x) (hpos (T - s) x)
  rw [h]
  exact reverse_fokkerPlanckStateDep1 T hFP hp hpos ha hap hb

/-- **State-independent diffusion is a special case (forward operator).** If
`a(t, x) = g(t)²` for all `t, x`, then `fpRHSStateDep1 b a p = fpRHS1 b g p` (no regularity
hypotheses are needed: constant factors commute with `deriv` unconditionally). -/
theorem fpRHSStateDep1_of_const {b a p : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    (ha : ∀ t y, a t y = g t ^ 2) : fpRHSStateDep1 b a p = fpRHS1 b g p := by
  funext t x
  have h : (fun y => a t y * p t y) = fun y => g t ^ 2 * p t y := funext fun y => by rw [ha]
  simp only [fpRHSStateDep1, fpRHS1, h, deriv_const_mul_field', deriv_const_mul_field]
  ring

/-- **State-independent diffusion is a special case (reverse drift).** If `a(t, x) = g(t)²`
for all `t, x`, the extra divergence term vanishes and
`reverseDriftStateDep1 T b a p = reverseDrift1 T b g p`. -/
theorem reverseDriftStateDep1_of_const {b a p : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (T : ℝ)
    (ha : ∀ t y, a t y = g t ^ 2) : reverseDriftStateDep1 T b a p = reverseDrift1 T b g p := by
  funext s x
  have h : a (T - s) = fun _ => g (T - s) ^ 2 := funext fun y => ha _ y
  simp only [reverseDriftStateDep1, reverseDrift1, h, deriv_const, add_zero]

/-! ## (d) d dimensions, scalar diffusion -/

variable {d : ℕ}

private lemma partialDeriv_lincomb {f h : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (i : Fin d)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (c₁ c₂ : ℝ) :
    partialDeriv i (fun y => c₁ * f y + c₂ * h y) x
      = c₁ * partialDeriv i f x + c₂ * partialDeriv i h x := by
  unfold partialDeriv
  rw [fderiv_fun_add (hf.const_mul c₁) (hh.const_mul c₂), fderiv_const_mul hf,
    fderiv_const_mul hh]
  simp

private lemma partialDeriv_congr {f h : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (i : Fin d)
    (hfh : f =ᶠ[𝓝 x] h) : partialDeriv i f x = partialDeriv i h x := by
  unfold partialDeriv; rw [hfh.fderiv_eq]

private lemma differentiable_partialDeriv {p : (Fin d → ℝ) → ℝ} (hp : ContDiff ℝ 2 p)
    (i : Fin d) : Differentiable ℝ (partialDeriv i p) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ p) := hp.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiff_const).differentiable one_ne_zero

/-- Right-hand side of the d-dimensional forward Fokker–Planck equation for
`dX = b(t, X) dt + g(t) dW` (scalar diffusion):
`fpRHS b g p t x = -div (b(t, ·) p(t, ·))(x) + (g(t)² / 2) Δ p(t, ·)(x)`. -/
noncomputable def fpRHS (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (g : ℝ → ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  -divergence (fun y i => b t y i * p t y) x + g t ^ 2 / 2 * laplacian (p t) x

/-- The d-dimensional reverse-time drift with horizon `T`:
`b̄(s, x) = -b(T - s, x) + g(T - s)² ∇ₓ log p(T - s, x)`. -/
noncomputable def reverseDrift (T : ℝ) (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (g : ℝ → ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) (s : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => -b (T - s) x i + g (T - s) ^ 2 * score (p (T - s)) x i

/-- The d-dimensional probability-flow velocity
`v(t, x) = b(t, x) - (g(t)² / 2) ∇ₓ log p(t, x)`. -/
noncomputable def pfVelocity (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (g : ℝ → ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => b t x i - g t ^ 2 / 2 * score (p t) x i

/-- **Probability-flow rewriting (d-dim, scalar diffusion, one time slice).** Let
`p : (Fin d → ℝ) → ℝ`, `b : (Fin d → ℝ) → Fin d → ℝ` and `g : ℝ`. Assume `p` is
differentiable and positive near `x`, every partial derivative `∂ᵢ p` is differentiable at
`x`, and `b` is differentiable at `x`. Then
`-div (b p)(x) + (g² / 2) Δp(x) = -div ((b - (g² / 2) ∇ log p) p)(x)`. -/
theorem probFlow_rewrite {p : (Fin d → ℝ) → ℝ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {x : Fin d → ℝ} (g : ℝ) (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ p y ∧ 0 < p y)
    (hp' : ∀ i, DifferentiableAt ℝ (partialDeriv i p) x) (hb : DifferentiableAt ℝ b x) :
    -divergence (fun y i => b y i * p y) x + g ^ 2 / 2 * laplacian p x
      = -divergence (fun y i => (b y i - g ^ 2 / 2 * score p y i) * p y) x := by
  have key : ∀ i, partialDeriv i (fun y => (b y i - g ^ 2 / 2 * score p y i) * p y) x
      = 1 * partialDeriv i (fun y => b y i * p y) x
        + (-(g ^ 2 / 2)) * partialDeriv i (partialDeriv i p) x := by
    intro i
    have hev : (fun y => (b y i - g ^ 2 / 2 * score p y i) * p y)
        =ᶠ[𝓝 x] fun y => 1 * (b y i * p y) + (-(g ^ 2 / 2)) * partialDeriv i p y :=
      hp.mono fun y hy => by
        have h := score_mul_self_of_pos hy.1 hy.2 i
        linear_combination (-(g ^ 2 / 2)) * h
    rw [partialDeriv_congr i hev,
      partialDeriv_lincomb i ((differentiableAt_pi.1 hb i).fun_mul hp.self_of_nhds.1) (hp' i)]
  simp only [divergence, laplacian, key, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Probability-flow rewriting for `C²` positive densities (d-dim).** If `p` is `C²` and
everywhere positive and `b` is differentiable at `x`, then
`-div (b p)(x) + (g² / 2) Δp(x) = -div ((b - (g² / 2) ∇ log p) p)(x)`. -/
theorem probFlow_rewrite_of_contDiff {p : (Fin d → ℝ) → ℝ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {x : Fin d → ℝ} (g : ℝ) (hp : ContDiff ℝ 2 p) (hpos : ∀ y, 0 < p y)
    (hb : DifferentiableAt ℝ b x) :
    -divergence (fun y i => b y i * p y) x + g ^ 2 / 2 * laplacian p x
      = -divergence (fun y i => (b y i - g ^ 2 / 2 * score p y i) * p y) x :=
  probFlow_rewrite g
    (Eventually.of_forall fun y => ⟨(hp.differentiable (by norm_num)) y, hpos y⟩)
    (fun i => differentiable_partialDeriv hp i x) hb

/-- **Probability-flow form of the d-dimensional Fokker–Planck right-hand side.** If, at
time `t`, `p(t, ·)` is differentiable and positive near `x`, each `∂ᵢ p(t, ·)` is
differentiable at `x` and `b(t, ·)` is differentiable at `x`, then
`fpRHS b g p t x = -div (v(t, ·) p(t, ·))(x)` with `v = pfVelocity b g p`
(`v = b - (g²/2) ∇ log p`). -/
theorem fpRHS_eq_neg_divergence_pfVelocity {p : ℝ → (Fin d → ℝ) → ℝ}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {g : ℝ → ℝ} {t : ℝ} {x : Fin d → ℝ}
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (p t) y ∧ 0 < p t y)
    (hp' : ∀ i, DifferentiableAt ℝ (partialDeriv i (p t)) x)
    (hb : DifferentiableAt ℝ (b t) x) :
    fpRHS b g p t x = -divergence (fun y i => pfVelocity b g p t y i * p t y) x :=
  probFlow_rewrite (g t) hp hp' hb

/-- **Reverse-time Fokker–Planck equation (d-dim, scalar diffusion, pointwise).** Fix
`T, s, x` and put `t = T - s`. Assume the forward equation
`∂ₜ p = -div (b p) + (g² / 2) Δp` holds at `(t, x)`, that `p(t, ·)` is differentiable and
positive near `x`, that every `∂ᵢ p(t, ·)` is differentiable at `x` and that `b(t, ·)` is
differentiable at `x`. Then `q(s, x) = p(T - s, x)` satisfies at `(s, x)`
`∂ₛ q = -div (b̄ q) + (ḡ² / 2) Δq` with `ḡ(s) = g(T - s)` and
`b̄(s, x) = -b(T - s, x) + g(T - s)² ∇ₓ log p(T - s, x)` (`reverseDrift`). -/
theorem reverse_fokkerPlanck_at {p : ℝ → (Fin d → ℝ) → ℝ} {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {g : ℝ → ℝ} {T s : ℝ} {x : Fin d → ℝ}
    (hFP : HasDerivAt (fun t => p t x) (fpRHS b g p (T - s) x) (T - s))
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (p (T - s)) y ∧ 0 < p (T - s) y)
    (hp' : ∀ i, DifferentiableAt ℝ (partialDeriv i (p (T - s))) x)
    (hb : DifferentiableAt ℝ (b (T - s)) x) :
    HasDerivAt (fun s => timeReversal T p s x)
      (fpRHS (reverseDrift T b g p) (fun s => g (T - s)) (timeReversal T p) s x) s := by
  convert hFP.comp_const_sub T s using 1
  · rfl
  have key : ∀ i, partialDeriv i
        (fun y => (-b (T - s) y i + g (T - s) ^ 2 * score (p (T - s)) y i) * p (T - s) y) x
      = (-1) * partialDeriv i (fun y => b (T - s) y i * p (T - s) y) x
        + g (T - s) ^ 2 * partialDeriv i (partialDeriv i (p (T - s))) x := by
    intro i
    have hev : (fun y => (-b (T - s) y i + g (T - s) ^ 2 * score (p (T - s)) y i)
          * p (T - s) y)
        =ᶠ[𝓝 x] fun y => (-1) * (b (T - s) y i * p (T - s) y)
          + g (T - s) ^ 2 * partialDeriv i (p (T - s)) y :=
      hp.mono fun y hy => by
        have h := score_mul_self_of_pos hy.1 hy.2 i
        linear_combination g (T - s) ^ 2 * h
    rw [partialDeriv_congr i hev,
      partialDeriv_lincomb i ((differentiableAt_pi.1 hb i).fun_mul hp.self_of_nhds.1) (hp' i)]
  simp only [fpRHS, reverseDrift, timeReversal, divergence, laplacian, key,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Reverse-time Fokker–Planck equation (d-dim, scalar diffusion, global).** Assume `p`
satisfies `∂ₜ p = -div (b p) + (g² / 2) Δp` strongly at every `(t, x)`, every `p(t, ·)` is
`C²` and everywhere positive, and every `b(t, ·)` is differentiable. Then for every horizon
`T`, `q(s, x) = p(T - s, x)` satisfies `∂ₛ q = -div (b̄ q) + (ḡ² / 2) Δq` at every `(s, x)`,
with `ḡ(s) = g(T - s)` and `b̄(s, x) = -b(T - s, x) + g(T - s)² ∇ₓ log p(T - s, x)`.
This is a marginal (Fokker–Planck) statement, not a pathwise reverse-SDE theorem. -/
theorem reverse_fokkerPlanck {p : ℝ → (Fin d → ℝ) → ℝ} {b : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {g : ℝ → ℝ} (T : ℝ) (hFP : ∀ t x, HasDerivAt (fun t => p t x) (fpRHS b g p t x) t)
    (hp : ∀ t, ContDiff ℝ 2 (p t)) (hpos : ∀ t y, 0 < p t y)
    (hb : ∀ t, Differentiable ℝ (b t)) :
    ∀ s x, HasDerivAt (fun s => timeReversal T p s x)
      (fpRHS (reverseDrift T b g p) (fun s => g (T - s)) (timeReversal T p) s x) s :=
  fun s x => reverse_fokkerPlanck_at (hFP (T - s) x)
    (Eventually.of_forall fun y =>
      ⟨((hp (T - s)).differentiable (by norm_num)) y, hpos (T - s) y⟩)
    (fun i => differentiable_partialDeriv (hp (T - s)) i x) (hb (T - s) x)

/-- **Reversing twice gives back the forward drift (d-dim).** For any `b, g, p` (no
hypotheses), `reverseDrift T (reverseDrift T b g p) (g(T - ·)) (timeReversal T p) = b`. -/
theorem reverseDrift_reverseDrift (T : ℝ) (b : ℝ → (Fin d → ℝ) → Fin d → ℝ) (g : ℝ → ℝ)
    (p : ℝ → (Fin d → ℝ) → ℝ) :
    reverseDrift T (reverseDrift T b g p) (fun s => g (T - s)) (timeReversal T p) = b := by
  funext t x i
  simp [reverseDrift, timeReversal, sub_sub_cancel]

/-- Under positivity and `C²` regularity of `p`, the score `∇ log p` is the differentiable
field `∇p / p`, hence the d-dimensional reverse drift is differentiable in space. -/
private lemma differentiable_reverseDrift {p : ℝ → (Fin d → ℝ) → ℝ}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {g : ℝ → ℝ} (T s : ℝ)
    (hp : ∀ t, ContDiff ℝ 2 (p t)) (hpos : ∀ t y, 0 < p t y)
    (hb : ∀ t, Differentiable ℝ (b t)) :
    Differentiable ℝ (reverseDrift T b g p s) := by
  have hp1 : Differentiable ℝ (p (T - s)) := (hp (T - s)).differentiable (by norm_num)
  refine differentiable_pi.2 fun i => ?_
  have h : (fun x => reverseDrift T b g p s x i) = fun x => -b (T - s) x i
      + g (T - s) ^ 2 * (partialDeriv i (p (T - s)) x * (p (T - s) x)⁻¹) :=
    funext fun x => by
      simp only [reverseDrift]
      rw [score_apply_of_pos (hp1 x) (hpos (T - s) x), div_eq_mul_inv]
  rw [h]
  exact ((differentiable_pi.1 (hb (T - s)) i).neg).add
    (((differentiable_partialDeriv (hp (T - s)) i).fun_mul
      (hp1.fun_inv fun y => (hpos (T - s) y).ne')).const_mul _)

/-- **Forward and reverse d-dimensional Fokker–Planck equations are equivalent.** Assume
every `p(t, ·)` is `C²` and everywhere positive and every `b(t, ·)` is differentiable. Then
`p` satisfies `∂ₜ p = -div (b p) + (g² / 2) Δp` at every `(t, x)` **if and only if**
`q(s, x) = p(T - s, x)` satisfies `∂ₛ q = -div (b̄ q) + (ḡ² / 2) Δq` at every `(s, x)`,
with `b̄ = reverseDrift T b g p` and `ḡ(s) = g(T - s)`. -/
theorem reverse_fokkerPlanck_iff {p : ℝ → (Fin d → ℝ) → ℝ}
    {b : ℝ → (Fin d → ℝ) → Fin d → ℝ} {g : ℝ → ℝ} (T : ℝ)
    (hp : ∀ t, ContDiff ℝ 2 (p t)) (hpos : ∀ t y, 0 < p t y)
    (hb : ∀ t, Differentiable ℝ (b t)) :
    (∀ t x, HasDerivAt (fun t => p t x) (fpRHS b g p t x) t) ↔
      ∀ s x, HasDerivAt (fun s => timeReversal T p s x)
        (fpRHS (reverseDrift T b g p) (fun s => g (T - s)) (timeReversal T p) s x) s := by
  refine ⟨fun hFP => reverse_fokkerPlanck T hFP hp hpos hb, fun hRev => ?_⟩
  have h := reverse_fokkerPlanck (p := timeReversal T p) (b := reverseDrift T b g p)
    (g := fun s => g (T - s)) T hRev (fun s => hp (T - s)) (fun s => hpos (T - s))
    (fun s => differentiable_reverseDrift T s hp hpos hb)
  rw [reverseDrift_reverseDrift, timeReversal_timeReversal] at h
  simpa only [sub_sub_cancel] using h

/-! ## Sanity example: the stationary Ornstein–Uhlenbeck process (1D)

For `dX = -(X / 2) dt + dW` (drift `b(t, x) = -x / 2`, diffusion `g = 1`) the standard
Gaussian is stationary. We use the unnormalised density `exp(-x² / 2)`; the identities are
linear in `p`, so normalisation plays no role. This example shows that the hypotheses of
`reverse_fokkerPlanck1` are jointly satisfiable. -/

/-- The unnormalised standard Gaussian density `x ↦ exp(-x² / 2)` (positive, smooth). -/
noncomputable def ouDensity (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

private lemma ouDensity_pos (x : ℝ) : 0 < ouDensity x := Real.exp_pos _

private lemma hasDerivAt_ouDensity (x : ℝ) : HasDerivAt ouDensity (-x * ouDensity x) x := by
  have h := ((hasDerivAt_pow 2 x).neg.div_const 2).exp
  convert h using 1
  · rfl
  simp only [ouDensity, Pi.neg_apply]; push_cast; ring

private lemma deriv_ouDensity : deriv ouDensity = fun x => -x * ouDensity x :=
  funext fun x => (hasDerivAt_ouDensity x).deriv

private lemma differentiable_ouDensity : Differentiable ℝ ouDensity :=
  fun x => (hasDerivAt_ouDensity x).differentiableAt

private lemma hasDerivAt_deriv_ouDensity (x : ℝ) :
    HasDerivAt (deriv ouDensity) ((x ^ 2 - 1) * ouDensity x) x := by
  rw [deriv_ouDensity]
  have h := ((hasDerivAt_id x).neg).mul (hasDerivAt_ouDensity x)
  convert h using 1
  · rfl
  simp; ring

private lemma hasDerivAt_ou_flux (x : ℝ) :
    HasDerivAt (fun y => -y / 2 * ouDensity y) ((x ^ 2 - 1) / 2 * ouDensity x) x := by
  have h := (((hasDerivAt_id x).neg).div_const 2).mul (hasDerivAt_ouDensity x)
  convert h using 1
  · rfl
  simp; ring

/-- **The stationary OU density solves the forward equation.** With `p(t, x) = exp(-x²/2)`,
`b(t, x) = -x / 2` and `g = 1`, the forward Fokker–Planck right-hand side vanishes, so
`∂ₜ p = 0 = -∂ₓ (b p) + (1/2) ∂ₓₓ p` holds strongly at every `(t, x)`. -/
theorem ouDensity_fokkerPlanck (t x : ℝ) :
    HasDerivAt (fun t => (fun _ : ℝ => ouDensity) t x)
      (fpRHS1 (fun _ y => -y / 2) (fun _ => 1) (fun _ => ouDensity) t x) t := by
  have h0 : fpRHS1 (fun _ y => -y / 2) (fun _ => 1) (fun _ => ouDensity) t x = 0 := by
    simp only [fpRHS1]
    rw [(hasDerivAt_ou_flux x).deriv, (hasDerivAt_deriv_ouDensity x).deriv]
    ring
  rw [h0]
  exact hasDerivAt_const t (ouDensity x)

/-- **Reverse-time equation for the stationary OU example.** All hypotheses of
`reverse_fokkerPlanck1` hold for `p(t, x) = exp(-x²/2)`, `b(t, x) = -x / 2`, `g = 1`, so for
every horizon `T` the reversed density satisfies `∂ₛ q = -∂ₓ (b̄ q) + (1/2) ∂ₓₓ q` with
`b̄ = reverseDrift1 T b g p`. -/
theorem ou_reverse_fokkerPlanck (T : ℝ) :
    ∀ s x, HasDerivAt (fun s => timeReversal T (fun _ : ℝ => ouDensity) s x)
      (fpRHS1 (reverseDrift1 T (fun _ y => -y / 2) (fun _ => 1) (fun _ => ouDensity))
        (fun _ => 1) (timeReversal T (fun _ : ℝ => ouDensity)) s x) s :=
  reverse_fokkerPlanck1 T ouDensity_fokkerPlanck (fun _ => differentiable_ouDensity)
    (fun _ => ouDensity_pos) (fun _ x => (hasDerivAt_deriv_ouDensity x).differentiableAt)
    (fun _ => (differentiable_id.neg).div_const 2)

/-- **The stationary OU process is reversible.** For `p(t, x) = exp(-x²/2)`, `b(t, x) = -x/2`
and `g = 1`, the reverse drift `-b + g² (log p)' = x/2 - x = -x/2` equals the forward drift:
`reverseDrift1 T b g p = b` for every horizon `T`. -/
theorem ou_reverseDrift1_eq (T : ℝ) :
    reverseDrift1 T (fun _ y => -y / 2) (fun _ => 1) (fun _ => ouDensity)
      = fun _ y => -y / 2 := by
  funext s x
  simp only [reverseDrift1]
  rw [score1_of_pos (differentiable_ouDensity x) (ouDensity_pos x),
    (hasDerivAt_ouDensity x).deriv]
  field_simp [(ouDensity_pos x).ne']
  ring

end ReverseTime

end FormalizeSampling
