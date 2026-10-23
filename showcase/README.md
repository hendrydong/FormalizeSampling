# Showcase: numerical pictures of the formal theorems

> **These are illustrations, not proofs.** Every number here comes from floating-point
> arithmetic, sometimes with Monte Carlo sampling, at a few chosen parameter values. A figure
> can make a theorem believable or show how tight it is. It does not prove anything, it does not
> discharge a hypothesis of a Lean theorem, and it does not change any status in
> `docs/theorem_registry.md`. The Lean library `FormalizeSampling/` is the only source of
> verified results.

| result ID | script | figure |
|---|---|---|
| DF-1 | `ddpm_bound.py` | `figures/ddpm_bound.png` |
| DF-2 | `memorization.py` | `figures/memorization.png` |
| DF-3 | `ode_vs_sde.py` | `figures/ode_vs_sde.png` |
| DF-3, DF-10 (numerical variant) | `ode_third_mode.py` | `figures/ode_third_mode.png` |
| DF-4 | `ddpm_variance.py` | `figures/ddpm_variance.png` |
| DF-5 | `path_kl.py` | `figures/path_kl.png` |
| DF-6 | `ddpm_rate.py` | `figures/ddpm_rate.png` |
| DF-7 | `ode_smooth.py` | `figures/ode_smooth.png` |
| DF-8 | `gauss_output.py` | `figures/gauss_output.png` |
| DF-8 | `gauss_output_ext.py` | `figures/gauss_output_ext.png` |
| DF-9 | `ode_lipschitz.py` | `figures/ode_lipschitz.png` |
| CE-08 | `step_counterexample.py` | `figures/step_counterexample.png` |
| EX-3, GI-1 | `tv_vs_kl.py` | `figures/tv_vs_kl.png` |
| FL-6 | `fp_uniqueness.py` | `figures/fp_uniqueness.png` |
| PX-5 | `proximal_logconcave.py` | `figures/proximal_logconcave.png` |
| PX-3, PX-4 (PX-2) | `proximal_sharp_rate.py` | `figures/proximal_sharp_rate.png` |
| FL-4, KL-5 | `ou_decay.py` | `figures/ou_decay.png` |

The scripts need numpy and matplotlib. CI has neither: it checks their style with `ruff` but does
not run them, and nothing in `tests/` imports this directory (the stdlib-only checks live in
`experiments/`). Run them from the repository root:

```bash
for script in showcase/[a-z]*.py; do
  uv run --no-project --with numpy --with matplotlib python "$script"
done
```

Each script uses fixed seeds, prints its key numbers, writes a PNG to `showcase/figures/`, and
runs in under about a minute on a CPU. Shared code is in `_style.py` (plot style, the geometric
time grid) and `_gauss_ddpm.py` (closed-form DDPM on Gaussian data).

**Conventions** follow `FormalizeSampling/Samplers/DiffusionSetup.lean`. The forward noising process
is Ornstein–Uhlenbeck, sampled on a time grid $`0 = t_0 \lt t_1 = \delta \lt \cdots \lt t_N = T`$,
with $`\alpha_k = e^{-(t_k - t_{k-1})}`$ and $`\beta_k = 1 - \alpha_k^2`$. The sampler starts from
$`\mathcal{N}(0, I)`$ and runs $`x \leftarrow (x + \beta_k s_k(x))/\alpha_k + \sigma_k \xi`$ for
$`k = N, \ldots, 2`$, with $`\sigma_k^2 = \beta_k / \alpha_k^2`$ unless stated otherwise. Its output
$`q_1`$ is compared with $`p_1`$, the data smoothed up to time $`\delta`$. The geometric grid is
$`u_k = e^{2 t_k} - 1 = u_1 r^{k-1}`$.

---

## 1. Exact empirical scores at small terminal noise (`memorization.py` → `figures/memorization.png`)

**What you see.** There are 20 training points on a ring. In panel (a) the diffusion sampler
uses the *exact* score of the training set. The training set is a finite list of points, so its
noised versions are Gaussian mixtures with a closed-form score. Every sample lands on top of a
training point. In panel (b) the same sampler uses a score learned by a small neural network
(pure numpy, trained by denoising score matching). The samples now spread along the whole ring:
they are new points that look like the data. Panel (c) is a histogram of each sample's distance
to its nearest training point. Panel (d) shows the fraction of samples within ρ = 0.1 of a
training point as the stopping time δ shrinks. With the exact score this fraction tracks the
grey curve, which is the fraction for $`p_1`$ itself (the training points blurred by
$`\sqrt{1-e^{-2\delta}}`$), and it reaches 1.000 at δ = 1e-4. The network stays at about 0.35.

**Key numbers.** At δ = 1e-3 (N = 200, T = 6), 2000 samples:

| score | median distance to nearest training point | fraction within ρ = 0.1 |
|---|---|---|
| exact | 0.054 | 0.89 |
| MLP | 0.139 | 0.34 |

**Which theorem.** The DDPM bound
`FormalizeSampling.DiffusionDiscretization.klDiv_output_le_geomGrid` does not need the data to have
a density. `DiffusionDiscretization.exists_klDiv_output_le` and `exists_tvSup_output_le`
(`FormalizeSampling/Samplers/DiffusionMain.lean`), with the Dirac and two-point witnesses
`dirac_tvSup_output_le`, `twoPoint_tvSup_output_le` in `FormalizeSampling/Audit/Diffusion.lean`,
show that with the exact score, the output $`q_1`$ gets arbitrarily close to $`p_1`$ even for
point-mass data. Here $`p_1`$ is a set of tiny blobs around the training points, so the exact-score
sampler copies the training set. The memorisation statement itself is registry entry DF-2,
`FormalizeSampling.DiffusionMemorization.output_concentrates_on_training_set`: for every ρ, ε > 0
there are sampler parameters with $`q_1(\bigcup_i B(x_i, \rho)) \ge 1 - \varepsilon`$. See also
`output_outside_nhds_le` and `tendsto_output_outside_nhds` in
`FormalizeSampling/Samplers/DiffusionMemorization.lean`. Panel (d) is the numerical version of that
limit: **exact empirical scores concentrate near the training set as terminal noise vanishes,
with discretisation and initialisation controlled.** This does not identify the source of
generalisation at fixed positive noise or with a population score. Panel (b) is only a
demonstration; the library does not prove that the network generalises. The memorisation of the
exact empirical score is known for the continuous-time sampler (Pidstrigach, arXiv:2206.01018,
Cor. 1; Li, Chen and Li, arXiv:2401.04856, Thm 4.3; see also Gu et al., arXiv:2310.02664); DF-2 is
the version for the discretised sampler.

## 2. Theory vs reality for the DDPM bound (`ddpm_bound.py` → `figures/ddpm_bound.png`)

**What you see.** The data is Gaussian, $`\mathcal{N}(m, \mathrm{diag}\, v)`$ in dimension $`d`$.
Every law in the sampler is then Gaussian, so the true error $`\mathrm{KL}(p_1 \Vert q_1)`$ of the
exact-score sampler can be computed exactly. The figure compares it with the right-hand side of the
formal bound, $`\mathrm{initBound} + (r - 1) \, \tfrac{d}{2} \, (1 + (N - 1) \log r)`$ (the
score-error term is zero). Panel (i): both the truth and the bound grow linearly in the dimension
(fitted log-log slopes 1.01 and 1.00). Panel (ii): as the number of steps $`N`$ grows, the bound
always stays above the truth. The bound decays like $`1/N`$; over the range shown the truth decays
like $`1/N^2`$ (fitted). This data is not $`\mathcal{N}(0, I)`$, so at fixed $`T`$ the truth keeps a
small initialisation floor as $`N \to \infty`$.

**Key numbers** (δ = 0.01, T = 5, d = 10): at N = 100 the true KL is 0.017 and the bound is 12.4.
At N = 10⁴ the true KL is 1.4e-6 and the bound is 0.105. The bound is safe but loose, by a factor
of about 200 at N ≈ 10 and about 7·10⁴ at N = 10⁴. Fitted decay exponents for N ≥ 300 are −2.00
(truth) and −1.01 (bound). The initialisation term is 9e-4, and the discretisation term
dominates.

**Which theorem.** `FormalizeSampling.DiffusionDiscretization.klDiv_output_le_geomGrid` (proved for
the reverse variance $`\sigma^2 = \beta/\alpha^2`$ used here), with `initBound_geomGrid`
(`FormalizeSampling/Samplers/DiffusionMain.lean`). The $`1/N`$ vs $`1/N^2`$ gap is numerical here;
section 11 sees it also for a point mass and a two-point law, and Lean proves the faster output rate
only for $`\mathcal{N}(0, I)`$ data (DF-8). The bound is a worst case over all data with a finite
second moment.

## 3. Which reverse noise variance? (`ddpm_variance.py` → `figures/ddpm_variance.png`)

**What you see.** This is the same exact computation as in section 2, run with three reverse
variances: $`\beta/\alpha^2`$ (the one in the DF-1 bound, `ddpmVar`), $`\beta`$ (one of the two DDPM
choices) and the posterior variance
$`\tilde{\beta} = \beta (1 - \bar{\alpha}_{k-1})/(1 - \bar{\alpha}_k)`$ (the other DDPM choice).

* Top row, error of the output samples. (a) For this d = 10 Gaussian, $`\beta`$ is about 4× better
  than $`\beta/\alpha^2`$ at every N, and $`\tilde{\beta}`$ sits in between. All three decay like
  $`1/N^2`$ over this range of $`N`$. (b) At a fixed budget of N = 100 steps there is a best
  horizon, T ≈ 2. A longer horizon spreads the same steps more coarsely. (c) The winner depends on
  the data. For $`\mathcal{N}(0, 1)`$ data, $`\sigma^2 = \beta`$ reverses the process exactly
  (KL = 0). For nearly point-like data (variance 1e-3) the posterior variance wins by three orders
  of magnitude.
* Bottom row, the horizon $`T`$ at fixed grid resolution, plus the *path-space* KL. The path-space
  KL is the chain-rule quantity that proofs like `klDiv_output_le_ddpm_grid` actually control. (d)
  On a geometric grid with fixed ratio (κ = 0.1, so N grows with T), the path KL of
  $`\beta/\alpha^2`$ grows linearly in T (1.0 → 3.8 → 7.4 at T = 2, 8, 16). The path KL of $`\beta`$
  and $`\tilde{\beta}`$ stays flat (0.10 and 0.46). Even for $`\beta/\alpha^2`$, the **output** KL
  stays flat at 0.0069. The growth in T is a path-level artefact. (e) If the stretch from t ≈ 1.2 to
  T is covered by **one long step**, $`\beta`$ and $`\tilde{\beta}`$ are unaffected (output KL
  0.0019 and 0.0056 for every T up to 16). $`\beta/\alpha^2`$ breaks down even at the output (KL 46
  at T = 8, 126 at T = 16), because its last-step variance $`e^{2h}-1`$ explodes. (f) Per step, for
  data $`\mathcal{N}(0, 0.5 \cdot I)`$ (so $`\mathbb{E} \Vert X \Vert^2 \le d`$), $`\beta`$ has the
  smallest per-step KL at every step (total 0.019, against 0.56 for $`\tilde{\beta}`$ and 2.7 for
  $`\beta/\alpha^2`$).

**Honest summary.** For this Gaussian data the DF-1 variance $`\beta/\alpha^2`$ is never the best of
the three, though the margin at the output is a constant factor. Its path-level KL grows with T
while its output KL does not. A single long final step does break it. No choice wins for all data.

**Which theorem.** `klDiv_output_le_ddpm_grid` / `klDiv_output_le_geomGrid` are proved for
$`\sigma^2 = \beta/\alpha^2`$. Panels (d) and (e) for $`\sigma^2 = \beta`$ illustrate the
heat-coordinate lemmas in `FormalizeSampling/Samplers/DiffusionVarianceHeat.lean`. In particular,
`DiffusionDiscretization.sum_betaStep_le` bounds the sum of $`\sigma^2 = \beta`$ per-step terms
independently of the number of steps and of the horizon, even when the grid is arbitrary after some
index (one long final step). `betaStep_le_entropyStep` covers the per-step comparison with
$`\beta/\alpha^2`$ for data with $`\mathbb{E} \Vert X \Vert^2 \le d`$, and `klDiv_output_le_betaVar`
is the end-to-end bound for $`\sigma^2 = \beta`$ (DF-4). The panel values of output KL, and
everything about $`\tilde{\beta}`$, are numerical only. Bounds for $`\sigma^2 = \beta`$ with no
term growing in $`T`$ are in Koike (arXiv:2605.18040, Thm 3.1 and Remark 3.2), for the DDPM sampler
as the Euler–Maruyama scheme of the Föllmer process, and in Conforti, Durmus and Gentiloni Silveri
(arXiv:2308.12240, Cor. 1), for an exponential-integrator scheme with step variance $`\beta`$. Bao,
Li, Zhu and Zhang (arXiv:2201.06503, App. D, Cor. 3) show that the optimal variance lies between
$`\tilde{\beta}`$ and $`\beta/\alpha^2`$.

## 4. Same score, stochastic sampler right, deterministic sampler wrong (`ode_vs_sde.py` → `figures/ode_vs_sde.png`)

**What you see.** The data is $`\mathcal{N}(0, 1)`$ and the exact score is $`-x`$. The score is
perturbed by a tiny smooth wiggle, $`e(x) = -\frac{\lambda h}{2\pi} \sin(2\pi x/h)`$ with h = 0.1,
λ = 3. The largest error is 0.048, and in panel (a) the two scores are hard to tell apart. Both
samplers run with this same score from $`\mathcal{N}(0, 1)`$ for time T = 2. (b) The stochastic
sampler (DDPM) reproduces $`\mathcal{N}(0, 1)`$. Its histogram distance (0.020) equals the
sampling-noise floor of exact $`\mathcal{N}(0, 1)`$ samples (0.020). For the corresponding
continuous-time SDE, started from its exact terminal law $`\mathcal{N}(0, 1)`$, the
Girsanov + Pinsker bound gives TV ≤ 0.034. This bound does not certify the finite-step DDPM
simulation; that requires a discretisation term as well. (c) The deterministic probability-flow
ODE (the continuous-time version of DDIM) squeezes each cell of width h onto the lattice point
inside it, so the output is a comb. Its exact total variation to $`\mathcal{N}(0, 1)`$ is **0.94**.
(d) Across the integrated Lipschitz constant λT, the ODE's TV follows
$`1 - (4/\pi) \arctan(e^{-\lambda T/2})`$,
the small-h limit, which matches quadrature to 4 digits. It stays above the lower bound
$`1 - (4/\pi) e^{-\lambda T/2} - \sqrt{2/\pi} \, h`$ and approaches 1. The continuous-time SDE
bound stays below 0.06.

**Checks.** The closed-form flow $`\tan(\pi \Phi_T(x)/h) = e^{-\lambda T} \tan(\pi x/h)`$ agrees
with RK4 integration of the ODE to 1.4e-12. At λT = 6 the quadrature TV is 0.9367, the small-h
formula gives 0.9367, and the (unformalised) lower bound is 0.857. A histogram with bins of width
h/10 underestimates the spiky ODE output (0.795), as expected.

**Which theorem.** Registry entry DF-3,
`FormalizeSampling.DiffusionODESeparation.ddpm_ddim_separation` (and `pf_ddpm_separation_geomGrid`
for the probability-flow step). For every ε > 0 there is a uniformly ε-accurate score for which the
deterministic sampler has TV = 1 (`tvSup_detOutput_latticeScore_eq_one`), while DDPM with the same
score obeys the DF-1 bound `tvSup_ddpm_latticeScore_le`, which is small for small ε on a long run
with fine enough steps. The Lean theorem uses the *discontinuous* (floor-function) lattice
perturbation of Li, Wei, Chen and Chi (arXiv:2306.09251); credit for the example is theirs. The
*smooth* sine variant in this figure (TV ≈ 0.94 < 1, closed-form flow, lower bound) is **numerical
only** and is not formalised. For the continuous-time ODE, Li, Di and Gu (arXiv:2410.14237, Thm 3.1)
prove a TV lower bound, uniform in ε, for a different smooth, uniformly ε-accurate score error. A
different construction, whose score error is an analytic function of the exact update, with
$`\mathrm{TV} \ge 1 - \eta`$, is formalised as DF-7 (section 12). The DDPM side is the kind of
guarantee in `DiffusionDiscretization.tvSup_output_le_ddpm_grid`, where the score enters only
through its L² error.

## 5. One ideal-velocity step can make things worse (`step_counterexample.py` → `figures/step_counterexample.png`)

**What you see.** The target is $`\mathcal{N}(0, 1)`$ and the current law is $`\mathcal{N}(0, s)`$.
One deterministic step moves every point along the ideal velocity
$`v = -(\log(\rho/\pi))' = (1/s - 1)x`$ with step size η. The left panel shows the KL to the target
before and after the step. The right panel shows their ratio, with the region where the KL goes *up*
shaded. Every step size η has a failure region: the narrower the current law, the more violently the
step overshoots.

**Key numbers.** The KL increases for $`s`$ below about 2.3e-4 (η = 0.05), 5.9e-3 (η = 0.2),
6.8e-2 (η = 0.5), and for every s < 1 at η = 1. For example, at η = 0.5 and s = 6.8e-3 the KL goes
from 2.0 to 16.4.

**Which theorem.** `FormalizeSampling.IdealVelocityStep.exists_klDiv_map_step_idealVel_gt`
(counterexample CE-08): for every η > 0 there is an s > 0 at which the step strictly increases the
KL. So the descent lemma needs a step size that depends on the current law. For η = 1 the increase
happens even where $`\eta \lvert 1/s - 1 \rvert`$ is small. The theorem only claims existence, and
the picture shows how large the failure region is. The Gaussian recursion for this step is
Example 4 of Wibisono (arXiv:1802.08089), from which the counterexample follows.

## 6. Add up errors in KL, not in TV (`tv_vs_kl.py` → `figures/tv_vs_kl.png`)

**What you see.** Two Gaussian random walks (Euler–Maruyama chains) start from the same point.
One has drift 0 and the other has a constant wrong drift Δ = 0.5, with step h = 0.01. The figure
compares the true distance between them after n steps with two ways of bounding it:

* adding up the per-step TV errors, which grows like $`n`$ and passes the trivial value 1 at
  n ≈ 70;
* adding up the per-step KL errors and converting once with Pinsker, $`\sqrt{\mathrm{KL}/2}`$, which
  grows like $`\sqrt{n}`$ and stays within a factor of about 1.25 of the truth until TV saturates.

The ratio of the two bounds is exactly $`\sqrt{2n/\pi}`$.

**Key numbers.** At n = 1000: true TV 0.42, KL route 0.56, TV route 14.1 (33× too big). At n = 10⁴:
0.92, 1.77 and 141. The KL after n steps equals $`n h \Delta^2/4`$ exactly, which is the budget of
the KL bound, so that bound is attained.

**Which theorem.** EX-3, `FormalizeSampling.GaussianIncrementTight.klDiv_const_chain_eq_bound` (the
KL bound `GaussianIncrement.klDiv_emChain_le_sum` is attained) and
`GaussianIncrementTight.sqrt_mul_tvSup_le_telescoped` (TV telescoping, as in
`GaussianIncrement.tvSup_emChain_le_sum`, overshoots by at least $`\sqrt{2n/\pi}`$). The
$`d`$-dimensional version is `GaussianIncrementTightPiTV.sqrt_mul_tvSup_le_telescoped`.

## 7. Proximal sampler, non-smooth log-concave target, cold start (`proximal_logconcave.py` → `figures/proximal_logconcave.png`)

**What you see.** The target is the Laplace law $`\pi \propto e^{-\lvert x \rvert}`$:
$`f(x) = \lvert x \rvert`$ is convex but not differentiable, and $`\pi`$ has no log-Sobolev
inequality. The chain starts from a point mass $`\rho_0 = \delta_{x_0}`$, so
$`\mathrm{KL}(\rho_0 \Vert \pi) = \infty`$. One step is the exact proximal sampler of Lee, Shen and
Tian (2021), `Proximal.proxKernel f η`: $`y \sim \mathcal{N}(x, \eta)`$, then
$`x' \sim \mathrm{RGO}(y) \propto e^{-\lvert x' \rvert - (x' - y)^2/(2\eta)}`$, with η = 1. The laws
$`\rho_k`$ are propagated exactly on a grid (step 0.025 on [-42, 42]) and checked against an exact
RGO sampler (rejection from $`\mathcal{N}(y - s\eta, \eta)`$, $`s = \mathrm{sign} \, y`$, using
$`\lvert x \rvert \ge sx`$). (a) The densities $`\rho_k`$ for x₀ = 10 (lines: grid; dots: 2·10⁵
exact-sampler chains). The chain walks toward 0 at about η per step and then fills in the kink. (b)
$`\mathrm{KL}(\rho_k \Vert \pi)`$ for x₀ = 3, 10, 25 with the Lean bound $`(x_0^2 + 2)/(2k\eta)`$.
(c) The fraction of the bound used, against $`k\eta/x_0`$.

**Which theorem.** PX-5, `FormalizeSampling.ProximalLogConcaveRate.klDiv_iterate_le_div'`: for
convex $`f`$ with $`\int e^{-f} \lt \infty`$, any $`\eta \gt 0`$, any coupling $`\gamma_0`$ of
$`(\rho_0, \pi)`$ and every $`k \ge 1`$,
$`\mathrm{KL}(\rho_k \Vert \pi) \le \int (x - y)^2 \, d\gamma_0 / (2k\eta)`$ (the registry writes
the same bound as $`\mathrm{KL}(\rho_{k+1} \Vert \pi) \le \ldots / (2(k+1)\eta)`$,
`klDiv_iterate_le_div`). For a point mass the only coupling is $`\delta_{x_0} \otimes \pi`$, so the
right-hand side is $`(x_0^2 + \mathbb{E}_\pi Y^2)/(2k\eta) = (x_0^2 + 2)/(2k\eta)`$. No finite
initial KL is needed, and the figure starts from $`\mathrm{KL} = \infty`$. The proof uses the
shifted-composition argument of Altschuler and Chewi (arXiv:2311.14520). The $`1/k`$ rate is that
of Chen, Chewi, Salim and Wibisono (arXiv:2202.06386, Thm 2); the constant $`1/(2k\eta)`$ is the
one the shifted-composition argument gives, as in the log-concave case of Pedrotti
(arXiv:2601.13259, Cor. 3.5). PX-5 holds for every convex $`f`$, such as the non-differentiable
$`\lvert x \rvert`$ here.

**Key numbers.** The bound holds at every k ≤ 200 for all three starts (asserted), and KL is
nonincreasing (asserted; `klDiv_proxKernel_comp_le_self`). At k = 1: KL = 1.13, 7.93, 22.9
against bounds 5.5, 51, 313.5. The largest fraction of the bound used is 0.21 (x₀ = 3, k = 1),
0.34 (x₀ = 10, k = 4) and 0.41 (x₀ = 25, k = 11). Grid vs exact sampler: binned TV ≤ 0.007 at
k = 1, 2, 5, 10, 20. Grid invariance $`\Vert \pi P - \pi \Vert_\infty`$ = 3e-14.

**Caveats.** For a fixed log-concave target the KL eventually decays exponentially (here the Laplace
law has a Poincaré inequality), so the $`1/k`$ bound is very loose for large k. Its value is that it
is uniform over all convex $`f`$ and all starts. The fraction used grows with x₀: a heuristic
(KL ≈ distance still to travel, $`x_0 - k\eta`$, while the bound is $`\approx x_0^2/(2k\eta)`$)
suggests a limit of 1/2 at $`k\eta \approx x_0/2`$ as x₀ → ∞, so the bound is tight within a factor
of about 2 for far cold starts. That limit is not proved. The 1D grid is a discretisation; the
Monte Carlo check uses the exact continuous RGO.

## 8. The sharp proximal rate $`(1 + \alpha\eta)^{-2k}`$, Gaussian and perturbed targets (`proximal_sharp_rate.py` → `figures/proximal_sharp_rate.png`)

**What you see.** α = 1, η = 0.5. Two 1D targets: the Gaussian $`\mathcal{N}(0, 1/\alpha)`$
(`f = gaussPotential α = αx²/2`) and the perturbed $`\pi \propto e^{-\alpha x^2/2 - W}`$ with
$`W(x) = 0.5 \cos 3x`$, so $`a = -0.5 \le W \le b = 0.5`$. The perturbed potential has
$`f'' = 1 - 4.5 \cos 3x`$, so $`\pi`$ is bimodal and not log-concave (panel a, with the chain from
$`\mathcal{N}(3, 1)`$). Each target is run from three starts: $`\mathcal{N}(3, 1)`$ (mean shift),
$`\mathcal{N}(0, 0.05)`$ and $`\mathcal{N}(-2, 0.1)`$. Panel (b) shows
$`\mathrm{KL}(\rho_k \Vert \pi)/\mathrm{KL}(\rho_0 \Vert \pi)`$ (dots: Gaussian target; lines:
perturbed target) with the PX-3 and PX-4 bounds. Panel (c) shows the per-step factor
$`\mathrm{KL}_k / \mathrm{KL}_{k-1}`$ with $`(1 + \alpha\eta)^{-2} = 0.444`$, the Holley–Stroock
$`(1 + \alpha'\eta)^{-2} = 0.713`$ ($`\alpha' = \alpha e^{-(b-a)} = 0.368`$) and the non-sharp
one-step LSI factor $`(1 + \alpha\eta)^{-1} = 0.667`$ of PX-2.

**Which theorem.** PX-3, `ProximalGaussianUnconditional.toReal_klDiv_iterate_le_sq_of_ne_top`:
$`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1 + \alpha\eta)^{2k}`$ for the
Gaussian target. PX-4, `ProximalSharpPerturbedCold.toReal_klDiv_iterate_le_sq_perturbed_of_ne_top`:
$`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1 + \alpha e^{-(b-a)} \eta)^{2k}`$
for $`f = \alpha x^2/2 + W`$ with $`W`$ measurable and $`a \le W \le b`$, every start with finite
KL. For the Gaussian target the chain is linear: the mean contracts by $`c = 1/(1 + \alpha\eta)`$
per step and the variance gap $`s - 1/\alpha`$ by $`c^2`$. So a mean-shifted start
$`\mathcal{N}(m, 1/\alpha)`$ has $`\mathrm{KL}_k = \alpha c^{2k} m^2/2`$, **equality** in PX-3 at
every k (the same sharpness as EX-3). The rate is the KL part of Theorem 3 of Chen, Chewi, Salim
and Wibisono (arXiv:2202.06386), whose §4.4 observes this sharpness on Gaussians (see also Mitra and
Wibisono, arXiv:2410.10699, App. G.2); PX-4 combines that KL bound with the Holley–Stroock lemma.

**Key numbers.** Grid vs closed form on the Gaussian target: relative error ≤ 3e-7. Mean shift:
$`\mathrm{KL}_k/\text{bound} = 1`$ to 1e-12 (asserted). $`\mathcal{N}(0, 0.05)`$: variance mode
only, per-step factor → $`c^4`$ (0.197), $`\mathrm{KL}_{10}/\text{bound}`$ = 7e-5.
$`\mathcal{N}(-2, 0.1)`$: $`\mathrm{KL}_k/\text{bound} \to 0.74`$. Perturbed target, all bounds hold
(asserted). $`\mathrm{KL}_k/\text{bound}`$ at k = 10 is 0.012 (from $`\mathcal{N}(3, 1)`$) and 0.008
(from $`\mathcal{N}(-2, 0.1)`$). The late per-step factor is 0.468, close to the
Gaussian 0.444 and well below the factor 0.713 of the PX-4 bound (Holley–Stroock constant).

**Caveats.** As the registry says, $`\alpha e^{-(b-a)}`$ is not the optimal constant in general; in
this example the observed contraction is much faster than the PX-4 bound. The symmetric start
$`\mathcal{N}(0, 0.05)`$ excites only even modes and decays faster (factor 0.17). Computations are on a grid (step 0.01 on [-14, 14]); KL values
below 1e-12 are rounding noise and are not plotted.

## 9. Langevin (OU) KL decay and the Gaussian log-Sobolev inequality (`ou_decay.py` → `figures/ou_decay.png`)

**What you see.** Target $`\pi = \mathcal{N}(0, v)`$ with v = 1, OU rate a = 1, i.e. the kernel
`OULangevinDecay.ouKernelVar v a t`: $`x \mapsto \mathcal{N}(e^{-at} x, v(1 - e^{-2at}))`$. Four
starts, all Gaussian mixtures, so $`\mathrm{OU}_t \rho`$ is a Gaussian mixture in closed form:
$`\mathcal{N}(2, 1)`$ (mean shift), $`\mathcal{N}(0, 0.05)`$, $`\mathcal{N}(0, 6)`$ and
$`\tfrac{1}{2} \mathcal{N}(\pm 2.5, 0.1)`$. (a) The bimodal start flowing to $`\mathcal{N}(0, 1)`$.
(b) $`\mathrm{KL}(\mathrm{OU}_t \rho \Vert \pi)/\mathrm{KL}(\rho \Vert \pi)`$ against $`e^{-2at}`$.
The mean shift lies on the line; the other starts decay faster. (c) The log-Sobolev ratio
$`\mathrm{KL}/((v/2) I)`$, with $`I = \int \lvert \partial_x \log(\rho_t/\pi) \rvert^2 \, d\rho_t`$.
It is 1 for the mean shift and below 1 for the others, tending to 1/2 for the centred starts.

**Which theorem.** FL-4, `OULangevinDecay.toReal_klDiv_ouKernelVar_comp_le`:
$`\mathrm{KL}(\mathrm{OU}_t \rho \Vert \mathcal{N}(0, v)) \le e^{-2at} \mathrm{KL}(\rho \Vert \mathcal{N}(0, v))`$
for finite KL and second moment; `toReal_klDiv_ouKernelVar_comp_gaussianReal`: equality for
$`\rho = \mathcal{N}(m, v)`$, value $`e^{-2at} m^2/(2v)`$. KL-5(b),
`GaussianLSIZero.klDiv_le_fisher0`:
$`\mathrm{KL}(\rho \Vert \mathcal{N}(0, v)) \le (v/2) \, I(\rho \Vert \mathcal{N}(0, v))`$. The
script also checks the FL-4 probability-flow identity
$`\tfrac{d}{dt} \mathrm{KL}(\rho_t \Vert \pi) = -(av) \, I(\rho_t \Vert \pi)`$
(`ProbabilityFlowOU.hasDerivAt_gaussKL_ouDensity`) by central differences at t = 0.25, 1, 2.
Together, $`d\mathrm{KL}/dt = -avI \le -2a \, \mathrm{KL}`$ is the Grönwall argument behind the
decay.

**Key numbers.** At t = 1, $`\mathrm{KL}/(e^{-2at} \mathrm{KL}_0)`$ = 1.0000 (mean shift; the closed
form matches quadrature to 1e-12), 0.033 ($`\mathcal{N}(0, 0.05)`$), 0.37 ($`\mathcal{N}(0, 6)`$)
and 0.23 (bimodal). The largest LSI ratio over t ∈ [0, 3] is 1.0000, 0.50, 0.77 and 0.62. All
inequalities asserted on a grid of 121 times.

**Caveats.** Quadrature on [-14, 14] with 56001 points; all starts are smooth Gaussian mixtures
(the KL-5(b) hypotheses: positive differentiable density, finite second moment and Fisher
information). The ratio 1/2 for centred starts reflects that their slowest mode is the variance,
which decays like $`e^{-4at}`$. This is a property of these examples, not a theorem in the library.

## 10. Path KL vs output KL (`path_kl.py` → `figures/path_kl.png`)

**What you see.** For Gaussian data the KL between the true reverse path and the sampler path is
computed in closed form and compared with the right-hand side of the chain rule. Panel (a): with
$`\sigma^2 = \beta/\alpha^2`$ the path KL grows linearly in the horizon $`T`$ while the output KL
stays flat. Panel (b): with $`\sigma^2 = \beta`$ both stay bounded.

**Lean theorems.** `DiffusionPath.klDiv_truePath_algPath` (exact chain rule, DF-5),
`DiffusionPath.klDiv_truePath_ddpm_ge_uniform` (linear-in-$`T`$ lower bound),
`DiffusionPath.klDiv_truePath_betaVar_le_explicit` (exact-score upper bound, uniform in $`N`$ and
$`T`$ at fixed $`t_1, \kappa, d, M`$; the learned-score form `klDiv_truePath_betaVar_le` adds the
score-error sum).

**Key numbers.** The chain-rule equality holds to relative error `2e-11` on three grids and both
variance rules. Data $`\mathcal{N}(0, 0.5)`$, $`h = 0.05`$: the $`\beta/\alpha^2`$ path KL is 0.085,
0.280, 0.522, 1.006 at $`T`$ = 1, 5, 10, 20, while its output KL stays at `5.2e-3`. The path-KL
slope 0.04837 matches the slope of the Lean lower bound to five digits.

**Caveats.** The $`\sigma^2 = \beta`$ upper bound holds but is loose (about 16 against 0.007).

**Prior work.** That the path KL of this sampler is of the order of the step size in the worst case,
so that path-based analyses stop at that order while the output can be closer, is noted by Benton,
De Bortoli, Doucet and Deligiannidis (arXiv:2308.03686, §4) and by Li and Yan (arXiv:2409.18959,
§3.1), after Chen et al. (arXiv:2209.11215, Thm 7) for the critically damped Langevin sampler.
DF-5 proves the lower bound for every data law with $`\mathbb{E} \Vert X \Vert^2 \le d`$ and every
mean map.

## 11. The $`1/N`$ rate is sharp for the path, not for the output (`ddpm_rate.py` → `figures/ddpm_rate.png`)

**What you see.** Left: the per-step KL sum $`D_N`$ (the path quantity) for the point mass
$`\delta_0`$, $`\mathcal{N}(0, 1)`$ and the two-point law $`\pm 1`$, with the Lean upper bound
(DF-1), the Lean universal lower bound and the exact point-mass formula; the output KL for the same
data. Right: $`D_N`$ for $`\delta_0`$ on 2000 random 40-step grids with the same endpoints
$`u_1, u_N`$, against the geometric grid.

**Lean theorems.** `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_ge_log`,
`sum_lintegral_klDiv_revKernel_ddpm_dirac`, `sum_lintegral_klDiv_revKernel_ddpm_dirac_ge`,
`discBound_geomGrid_le_dirac` (DF-6).

**Key numbers.** Fitted exponents for $`N`$ = 40…320: path $`D_N`$ about $`-0.96`$, output KL about
$`-2.0`$, for all three data laws. At $`N = 320`$ the DF-1 bound is 2.2 times the exact point-mass
sum. The best of 2000 random grids gives 1.121 against 1.104 for the geometric grid.

**Caveats.** With the per-step optimal (Analytic-DPM) variance the two-point path sum is still
of order $`1/N`$ numerically; this is not a Lean statement.

## 12. An analytic score error that breaks the deterministic sampler (`ode_smooth.py` → `figures/ode_smooth.png`)

**What you see.** The Lean construction of DF-7 with $`\varepsilon = 0.1`$: a score error $`E`$ with
$`\lvert E \rvert \le \varepsilon`$ that is an analytic function of the exact update (here affine in
$`y`$), built from iterates of $`u \mapsto u - \sin(2\pi u)/(2\pi)`$, the outputs of DDPM and of the
deterministic sampler inside a lattice cell, the mass of the Lean test set, and the price
$`b_2 \cdot \mathrm{Lip}(E)`$ against $`1/\eta`$.

**Lean theorems.** `DiffusionODESmooth.ddpm_ddim_smooth_separation`,
`pf_ddpm_smooth_separation_geomGrid`, `le_of_lipschitzWith_errProfile` (DF-7).

**Key numbers.** At $`\eta = 0.05`$: the test set has mass 0.025 under $`p_1`$ and under DDPM, and
0.986 under the deterministic sampler, so $`\mathrm{TV} \ge 0.961 \ge 1 - \eta`$. The certified
bound holds for every $`\eta`$ from 0.5 down to 0.001. $`b_2 \cdot \mathrm{Lip}(E) \approx 2^m`$
grows roughly like $`1/\eta`$.

**Caveats.** The growth of the Lipschitz constant as $`\eta \to 0`$ is numerical; Lean proves only
the two-sided bound for this construction.

**Prior work.** A related result is Li, Di and Gu (arXiv:2410.14237, Thm 3.1): a smooth score
within ε of the true score everywhere for which the continuous-time probability-flow ODE stays a
fixed TV distance away from $`\mathcal{N}(0, 1)`$, however small ε is.

## 13. Fokker–Planck with a Lipschitz, unbounded drift (`fp_uniqueness.py` → `figures/fp_uniqueness.png`)

**What you see.** Drift $`b(x) = -x + 2 \sin 3x`$, $`D = 1/2`$, Cauchy initial law (no mean). Left:
the law at $`t = 1`$ from a finite-volume PDE solver and from Euler–Maruyama with two step sizes.
Right: the distance between the two against the step size.

**Lean theorems.** `FokkerPlanckUniqueness.eq_of_weakFokkerPlanck_lipschitz`,
`existsUnique_weakFokkerPlanck_lipschitz`, `tendsto_emCurveP_of_weakFokkerPlanck_lipschitz` (FL-6).

**Key numbers.** The window Kolmogorov distance falls from 0.251 ($`h = 2^{-1}`$) to 0.0045
($`h = 2^{-7}`$), roughly like $`h`$. Halving the PDE mesh changes its solution by `8e-5`.

**Caveats.** Lean proves convergence without a rate; the $`O(h)`$ rate is numerical.

**Prior work.** Uniqueness for such drifts is classical: it is covered by the theorem for drifts
with $`\langle b(t, x), x \rangle \le C + C \lvert x \rvert^2`$ in Bogachev, Krylov, Röckner and
Shaposhnikov, *Fokker–Planck–Kolmogorov Equations* (AMS, 2015, Ch. 9). FL-6 is a formal proof.

## 14. Gaussian output and path KL: bounds and finite-grid rates (`gauss_output.py` → `figures/gauss_output.png`)

**What you see.** For data $`\mathcal{N}(0, vI)`$ and the exact score, the exact output KL, the Lean
output bound retaining initialisation, the exact path KL and the Lean path lower bound, against the
number of steps, for $`v \in \{0.1, 0.5, 1\}`$.

**Lean theorems.** `DiffusionGaussian.gaussian_output_path_separation`,
`klDiv_output_isoGauss_ddpm_le`, `klDiv_truePath_isoGauss_ddpm_ge`, `klDiv_output_isoGauss_eq`
(DF-8).

**Key numbers.** $`t_1 = 0.01`$, $`T = 5`$, uniform grid, $`N`$ = 10…1280. Fitted slopes: output
about $`-2.0`$, path about $`-0.99`$. At $`N = 1280`$ the output bound is 1.01, 1.77 and 3.24 times
the truth ($`v`$ = 1, 0.5, 0.1) and the path KL is 1.00, 1.16 and 1.96 times its Lean lower bound.

**Caveats.** The output bound is loose at small $`N`$ (ratio 77 at $`v = 0.1`$, $`N = 10`$). For
$`v \lt 1`$, initialisation leaves a nonzero error at fixed horizon as $`N \to \infty`$; the fitted
slopes describe the displayed finite grid. Pure quadratic output decay at fixed horizon holds for
$`v = 1`$. This script covers $`v \le 1`$; the next Gaussian example includes the $`v \gt 1`$
extension. Non-isotropic output rates are not covered by these Lean results.

**Prior work.** Jiao, Zhou and Li (arXiv:2510.27562, Thm 2) prove an output lower bound of order
$`d/N^2`$ for $`\mathcal{N}(0, \lambda I)`$ data with $`\lambda \ge 2`$ on their schedule; DF-8
covers $`v = 1`$ on a uniform grid over a fixed interval, with explicit constants on both sides.

## 15. Deterministic samplers: close in transport, far in TV (`ode_lipschitz.py` → `figures/ode_lipschitz.png`)

**What you see.** (a, b) The DF-7 construction for $`\varepsilon`$ from 0.3 to 0.003: the sup and
$`W_2`$ distances between the learned-score and exact-score deterministic outputs against the Lean
bound $`\lvert b_2 \rvert \cdot \varepsilon`$, next to the certified TV. (c) Gaussian data with 200
probability-flow steps.

**Lean theorems.** `DiffusionODELipschitz.exists_coupling_detMean`, `pf_isoGauss_coupling`,
`smooth_separation_tv_far_w2_close` (DF-9).

**Key numbers.** The sup distance is 0.978 times the Lean bound and $`W_2`$ about 0.57 times. At
$`\varepsilon = 0.1`$: $`W_2`$ = 2.8e-5 while $`\mathrm{TV}(p_1, q_1) \ge 0.961`$. In panel (c) a
constant error gives $`W_2 = W_\infty = B`$ numerically, equal to the bound; Lean does not prove
this tightness.

**Caveats.** The comparison is with the exact-score deterministic output, not with the data.

**Prior work.** Li, Wei, Chen and Chi (arXiv:2306.09251, §3.2) suggest a Wasserstein metric for
their TV counterexample. The transport half is a Grönwall-type stability estimate; for the
continuous-time ODE and Lipschitz test functions see Beltran-Velez et al.
(arXiv:2606.19162, Prop. 3.2).

## 16. Gaussian data: output bounds for several $`v`$, and $`\sigma^2 = \beta`$ (`gauss_output_ext.py` → `figures/gauss_output_ext.png`)

**What you see.** The exact output KL between the Lean lower and upper bounds against the number
of steps, for $`v \in \{0.5, 1, 2, 5\}`$, $`d = 10`$, and the $`\sigma^2 = \beta`$ sampler.

**Lean theorems.** `DiffusionGaussian.gaussian_output_two_sided`,
`klDiv_output_isoGauss_ddpm_ge` (the plotted $`v \le 1`$ lower bound; the $`/3`$ form in
`gaussian_output_two_sided` is about 3 times smaller for small $`h`$),
`klDiv_output_isoGauss_ddpm_le_of_one_le`, `klDiv_output_isoGauss_ddpm_ge_of_one_le`,
`klDiv_output_isoGauss_beta_le`, `klDiv_output_isoGauss_beta_one` (DF-8).

**Key numbers.** At $`N = 1280`$ the upper bound over the exact KL is 1.77, 1.01, 1.78, 2.79 and the
exact KL over the lower bound is 2.19, 1.00, 2.21, 8.71 ($`v`$ = 0.5, 1, 2, 5). The output KL has
slope 1.99–2.00 in $`h`$ for every $`v`$. For $`\sigma^2 = \beta`$, $`\mathrm{KL}/h^2`$ is about
0.23, 0.061, 0.159 and exactly 0 at $`v = 1`$.

**Caveats.** Constants are not matched; there is no Lean lower bound for $`\sigma^2 = \beta`$. The
fitted slopes describe the displayed grids, where initialisation error is small. For $`v \ne 1`$,
the fixed-horizon bounds retain initialisation; the $`v \gt 1`$ lower bound is useful only when its
discretisation excess dominates that allowance.

## 17. Two modes: a tiny score error and a third mode in the deterministic output (`ode_third_mode.py` → `figures/ode_third_mode.png`)

**What you see.** The data is $`\tfrac{1}{2} \mathcal{N}(-2, \tfrac{1}{4}) + \tfrac{1}{2} \mathcal{N}(2, \tfrac{1}{4})`$,
so the exact score $`s_t(x) = (-x + m_t \tanh(m_t x/v_t))/v_t`$ is explicit. At every noise level
the score is perturbed by $`e(x) = -\frac{\lambda h}{2\pi} \sin(2\pi x/h)`$ for
$`\lvert x \rvert \le h/2`$ and $`e(x) = 0`$ otherwise, with $`h = 0.6`$ and $`\lambda = 0.7`$: the
largest error is 0.067, and in panel (a) the two scores are hard to tell apart. Both samplers run
with this score from $`\mathcal{N}(0, 1)`$ at $`T = 10`$ down to $`\delta = 0.01`$. (b) DDPM puts
3.3% of its output in the gap $`\lvert x \rvert \lt 1`$, against 2.8% for the target. The
continuous-time Girsanov + Pinsker score-error term
$`\sqrt{\int_\delta^T \mathbb{E}_{p_t} e^2 \, dt / 2}`$ is 0.050. This is not a total-output
TV bound: the start $`\mathcal{N}(0, 1)`$ differs from $`p_T`$, so a guarantee also needs an
initialisation term and, for finite-step DDPM, discretisation control. (c) The probability-flow ODE
puts 23.5% there, in a third mode at 0, and its TV to the target is 0.23. (d) The mechanism. While
the noised law is close to $`\mathcal{N}(0, 1)`$ the exact velocity is tiny, and $`e`$ pulls the
samples that start in $`\lvert x \rvert \lt h/2`$ onto the midpoint. Near the end the exact flow pushes away
from the midpoint, but these samples are too close to it to reach either mode in time. DDPM's
injected noise moves samples off the midpoint, so the error is forgotten.

**Prior work.** The mechanism is known. Li, Di and Gu (arXiv:2410.14237, Thm 3.1) use that the
probability-flow velocity vanishes for Gaussian data, so that the flow does not correct a uniformly
small score error. Nie et al. (arXiv:2311.01410, Thms 3.1–3.2) prove that noise contracts the KL
divergence between two runs while a deterministic flow keeps it fixed. Ashiq et al.
(arXiv:2605.06831, Props. 4.7, 5.1 and C.5) show that, late in sampling, deterministic trajectories
near the midpoint between two modes stay trapped there while DDPM escapes, and that a score error
with the right directional structure can make the equilibrium near the midpoint instantaneously
stable. Zhang, Liao, Wu and Zou (arXiv:2508.16154) observe that deterministic samplers
over-concentrate, that this starts at high noise from an oscillating velocity error, and that the
error is retained along the run. Beltran-Velez et al. (arXiv:2606.19162, Prop. 3.1) show that a
velocity with small training error can send almost all of the probability-flow ODE's output into a
chosen region. This figure is a concrete one-dimensional instance, with an error of sup norm 0.067
and Lipschitz constant 0.7.

**Checks.** The ODE output is the push-forward of $`\mathcal{N}(0, 1)`$ by a monotone map, so its
gap mass and TV are computed by quadrature through that map, not by sampling; doubling the number
of RK4 steps changes neither in the fourth digit. The DDPM numbers are Monte Carlo
($`n = 100{,}000`$).

**Which theorem.** This construction is **numerical only**. The formal statements that a uniformly
small score error can leave the deterministic sampler far from the target in TV, while DDPM keeps
its guarantee, are DF-3 (section 4) and DF-7 (section 12). Their errors act at the last step, and
DF-9 (section 15) bounds how far such an error moves mass from the exact-score output. Here the
error acts throughout the run, and the exact flow between the modes amplifies it into a visible
displacement of mass. DF-10 (`DiffusionODEMidpoint.pf_ddpm_midpoint_separation`) proves a version
with its own construction: two atoms $`(\delta_{-a} + \delta_a)/2`$, an error
$`-(\varepsilon/R) \, \mathrm{clip}_R(x)`$ for some $`R \ge 1`$, with $`\mathrm{clip}_R`$ the clamp
to $`[-R, R]`$ (at most $`\varepsilon`$, $`\varepsilon`$-Lipschitz), switched on at high noise,
discrete steps on a geometric grid and a horizon of at most $`A/\varepsilon`$ ($`A`$ independent of
$`\varepsilon`$). There the deterministic output collapses onto the midpoint (mass $`\ge 1 - \eta`$
on a slab where $`p_1`$ puts mass $`\le \eta`$) instead of adding a third mode, while DDPM with the
same score stays within TV $`\eta`$.

**Caveats.** The TV here (0.23) is far from 1; the point of the figure is the shape of the output.
The error is Lipschitz but not smooth at $`\lvert x \rvert = h/2`$.
