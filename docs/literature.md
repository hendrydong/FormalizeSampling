# Literature map

Sampling algorithms in the literature look heterogeneous, but their analyses reuse a few moves. This
document takes published analyses one at a time and decomposes each into the moves of [How the
library is organised](../README.md#how-the-library-is-organised), step by step, saying for each step
what is formalised here and with which status. The [README](../README.md#literature-map) summarises
it in one table.

The moves, as defined in the [README](../README.md#how-the-library-is-organised); the bold word is
the name used in the tables:

- **Comparison** of laws: Pinsker, the two TV normalisations, KL chain rule and data processing,
  tensorisation, Gaussian KL, lower semicontinuity, extension from warm starts.
- **Error accumulation**: compare the algorithm's chain with an exact chain step by step
  (TV telescoping, KL chain rule and one Pinsker step, couplings).
- **Contraction**: log-Sobolev inequalities, KL contraction from an LSI along the heat flow,
  couplings and shifted composition.
- **Differentiation** along a curve: KL first variation and dissipation, de Bruijn along the heat
  flow, Grönwall, one-step descent for deterministic maps.
- **Identification** of the law: Bayes reverse kernels, invariance, weak Fokker–Planck and continuity
  equations, equal one-time marginals.
- **Score** representation and estimation: Tweedie and posterior scores, Stein/Hyvärinen objectives,
  Monte Carlo and inner-sampler errors.
- **Exact computation**: Gaussian closed forms and explicit constructions that attain a bound,
  bound it from below, or separate two samplers.

In the tables, "setting" marks the definitions of an algorithm or forward process, and "—" a step
outside these moves. Declarations are named without the `FormalizeSampling.` prefix; the
[declaration index](declaration_index.md) gives the file and docstring of every theorem, and the
[registry](theorem_registry.md) the exact hypotheses of every registry ID. A status names the
registry ID whose development contains the step: "formalises" means the statement as in the paper,
"proves a version of" the same statement under different hypotheses or constants, "special case" and
"component of" a part of it, "related statement" a different statement about the same quantity; "not
formalised" means no Lean statement.

Contents:

1. [Diffusion models: guarantees](#diffusion-models-guarantees): Ho–Jain–Abbeel (2020), Bao et al.
   (2022), Chen et al. (2023), Chen–Lee–Lu (2023), Benton–De Bortoli–Doucet–Deligiannidis (2024),
   Conforti–Durmus–Gentiloni Silveri (2023), Koike (2026), Li–Yan (2024), Jiao–Zhou–Li (2025),
   Li–Cai (2024), Sun–Poor–Zhang (2026)
2. [Diffusion models: deterministic samplers and
   memorisation](#diffusion-models-deterministic-samplers-and-memorisation): Li–Wei–Chen–Chi (2023),
   Li–Di–Gu (2024), Nie et al. (2024), Ashiq et al. (2026), Pidstrigach (2022), Li–Chen–Li (2024),
   Gu et al. (2023)
3. [Proximal sampler](#proximal-sampler): Lee–Shen–Tian (2021), Chen–Chewi–Salim–Wibisono (2022),
   Altschuler–Chewi (2023), Pedrotti (2026), Mitra–Wibisono (2025), Gross (1975), Holley–Stroock
   (1987), Bakry–Émery (1985)
4. [Flows and particle methods](#flows-and-particle-methods): DiPerna–Lions (1989),
   Bogachev–Krylov–Röckner–Shaposhnikov (2015), SVGD, Wibisono (2018), PFG
5. [Score-based Monte Carlo samplers](#score-based-monte-carlo-samplers): rdMC, RS-DMC, SPS, RTK

## Diffusion models: guarantees

### Ho–Jain–Abbeel (2020)

Jonathan Ho, Ajay Jain, Pieter Abbeel. Denoising Diffusion Probabilistic Models. NeurIPS 2020.
[arXiv:2006.11239](https://arxiv.org/abs/2006.11239).

**Algorithm.** Forward chain
$`q(x_t \mid x_{t-1}) = \mathcal{N}(\sqrt{1 - \beta_t}\, x_{t-1}, \beta_t I)`$. This is
`Diffusion.fwdKernel` on the grid `Diffusion.betaGrid`; Ho's $`\beta_t`$ is the library's
$`\beta_k`$ and Ho's $`\alpha_t`$ is the library's $`\alpha_k^2`$. Sampler (Algorithm 2): Gaussian
reverse kernel $`\mathcal{N}(\mu_\theta(x_t, t), \sigma_t^2 I)`$ started at $`\mathcal{N}(0, I)`$.
With the noise-predicted mean written as a score, and $`\sigma_t^2 = \beta_t`$, this is
`Diffusion.algKernel` with mean `Diffusion.scoreMean` and variance
`DiffusionDiscretization.betaVar`. The library stops at $`x_1`$ (law $`p_{t_1}`$) and has no decoder
$`p_\theta(x_0 \mid x_1)`$.

**Main result.** Eq. (5): variational bound $`L = L_T + \sum_{t \gt 1} L_{t-1} + L_0`$, with
Gaussian posteriors $`q(x_{t-1} \mid x_t, x_0)`$ (Eqs. (6)–(7)). Eq. (8): each $`L_{t-1}`$ is a
weighted mean-squared error between means. Eqs. (11)–(12): the noise-prediction parameterisation
turns this into a weighted denoising score-matching objective; Eq. (14) is the simplified loss.
§3.2: $`\sigma_t^2 = \beta_t`$ is optimal for $`x_0 \sim \mathcal{N}(0, I)`$ and
$`\sigma_t^2 = \tilde\beta_t`$ for deterministic $`x_0`$. The empirical result is FID 3.17 on
unconditional CIFAR10.

| Step | Move | Library | Status |
|---|---|---|---|
| Forward chain and closed-form marginal $`q(x_t \mid x_0)`$ (Eq. (4)) | setting | DF-1 setting: `Diffusion.fwdKernel`, `Diffusion.fwdLaw`, `Diffusion.betaGrid`, `Diffusion.fwdScale_betaGrid`, `Diffusion.fwdVar_betaGrid`, `DiffusionDiscretization.fwdLaw_eq_ouKernelVarPi_comp` | Verified (DF-1) |
| Variational bound as a sum of per-step KL terms (Eq. (5); rewritten form Eq. (16), App. A) | error accumulation | DF-5: `DiffusionPath.klDiv_truePath_algPath` gives the path KL as the initial KL plus the sum of per-step KLs from the Bayes reverse kernel to the sampler kernel. Also `DiffusionPath.klDiv_output_le_path`. KL-2: `KL.klDiv_chain_le_sum` | Related statement (DF-5, Verified): a population KL between path laws with per-step terms conditioned on $`x_k`$ only, the form of Ho et al. Eq. (16) without the constant $`H(x_0)`$ (on the library grid, ending at $`t_1 \gt 0`$); Eq. (5) conditions on $`(x_k, x_0)`$ and has the $`L_0`$ term |
| Per-step term as a squared mean difference (Eq. (8)) | comparison | KL-3: `GaussianIncrement.klDiv_pi_gaussianReal`. DF-1 mean-shift identity: `Diffusion.klDiv_pi_gaussianReal_eq_add`, `Diffusion.klDiv_pi_gaussianReal_mean_le`, `Diffusion.lintegral_klDiv_revKernel_eq` | Verified (KL-3, DF-1). Proves a version of Eq. (8): an exact split of the KL from the (non-Gaussian) Bayes posterior to $`\mathcal{N}(m, \sigma^2 I)`$ into the KL at the posterior mean plus $`\Vert m - m^* \Vert^2/(2\sigma^2)`$ |
| Mean written through the noise predictor / score (Eq. (11)) | score | Tweedie: `Diffusion.postMean_ae_eq_tweedie` (DF-1), `Tweedie.tweedie` and `OUPosterior.ouPosteriorScore_pi` (SE-3). CE-02: `Counterexamples.ScoreNotNoise.law_noiseTarget_ne_law_scoreOfNoisy` | Verified (DF-1, SE-3) in posterior-mean form; the noise form $`\mathbb{E}[\varepsilon \mid x_t]`$ is not stated. The library states explicitly that the noise target and the score agree in conditional expectation but not in law (CE-02) |
| Weighted denoising objective as a score error (Eq. (12)) | score | `Diffusion.lintegral_meanError_eq_scoreError` (the mean error of the sampler is a weighted score error averaged under $`p_k`$), `Diffusion.klDiv_output_le_score`. Related Hyvärinen form: `SteinObjective.steinObjective_eq` (SE-1) | Verified (DF-1) for the population identity; regression on the noise and training are not formalised |
| Choice of reverse variance $`\sigma_t^2 \in \{\beta_t, \tilde\beta_t\}`$ (§3.2) | exact computation | DF-8: `DiffusionGaussian.klDiv_output_isoGauss_beta_one` (for $`\sigma^2 = \beta`$, $`\mathcal{N}(0, I)`$ data and the exact score, the output KL is 0), `DiffusionGaussian.klDiv_output_isoGauss_beta_le`. DF-4: `DiffusionDiscretization.varStep_eq_opt` (per-step optimal isotropic variance for every data law) | Verified (DF-8, DF-4) for $`\sigma^2 = \beta`$ with standard Gaussian data. The optimality of $`\tilde\beta_t`$ for a point mass is not stated as a theorem |
| Training (Algorithm 1), simplified loss (Eq. (14)), discrete decoder $`L_0`$ (Eq. (13)) | — | not formalised | Not formalised |

### Bao et al. (2022)

Fan Bao, Chongxuan Li, Jun Zhu, Bo Zhang. Analytic-DPM: an Analytic Estimate of the Optimal Reverse
Variance in Diffusion Probabilistic Models. ICLR 2022.
[arXiv:2201.06503](https://arxiv.org/abs/2201.06503).

**Algorithm.** Same forward chain, `Diffusion.fwdKernel`; Bao's $`\alpha_n = 1 - \beta_n`$ is the
library's $`\alpha_k^2`$. The reverse kernel is Gaussian, $`\mathcal{N}(\mu_n(x_n), \sigma_n^2 I)`$,
with the KL-optimal mean and an isotropic variance estimated from the score model by Monte Carlo. In
the library: `Diffusion.algKernel` with mean `Diffusion.scoreMean` and reverse variance $`v`$. The
averaged one-step KL as a function of $`v`$ is `DiffusionDiscretization.varStep`. Its minimiser is
$`v^* = C/d`$, with $`C`$ = `DiffusionDiscretization.postVarHeat`.

**Main result.** Theorem 1: among Gaussian reverse kernels with isotropic covariance, the KL-optimal
mean and variance have closed forms in terms of the score (Eqs. (6)–(7)). In DDPM form (Corollary
2): $`\mu^*_n(x) = \alpha_n^{-1/2}(x + \beta_n \nabla \log q_n(x))`$ and
$`\sigma_n^{*2} = (\beta_n/\alpha_n)(1 - \beta_n \mathbb{E}\Vert \nabla \log q_n \Vert^2/d)`$.
Theorem 2 and Corollary 3: two-sided bounds on the optimal variance, including
$`\tilde\beta_n \le \sigma_n^{*2} \le \beta_n/\alpha_n`$, and a bound for data with bounded support.
Theorem 3: the optimal KL along a trajectory decomposes, so the best trajectory is found by dynamic
programming. A Monte Carlo estimate of the averaged score norm (Eqs. (8)–(10)) gives a training-free
variance.

| Step | Move | Library | Status |
|---|---|---|---|
| Forward chain, Bayes reverse kernel and Gaussian reverse family | setting | `Diffusion.fwdKernel`, `Diffusion.betaGrid`, `Diffusion.revKernel`, `Diffusion.revKernel_comp_fwdLaw`, `Diffusion.algKernel` | Verified (DF-1) |
| KL-optimal mean equals the posterior mean, written through the score (Theorem 1, Eq. (6); Corollary 2) | comparison, score | Mean-shift identity: `Diffusion.klDiv_pi_gaussianReal_eq_add`, `Diffusion.klDiv_pi_gaussianReal_mean_le`. Tweedie: `Diffusion.postMean_ae_eq_tweedie`, giving $`m^*_k(y) = \alpha_k^{-1}(y + \beta_k \nabla \log p_k(y))`$ | Verified (DF-1). Proves a version of the mean part of Theorem 1: DDPM forward process, isotropic Gaussian reverse kernels, per step |
| KL-optimal isotropic variance in terms of the averaged score norm (Theorem 1, Eq. (7); Corollary 2) | differentiation, score | DF-4: `DiffusionDiscretization.lintegral_klDiv_revKernel_var_eq` (exact averaged one-step KL for every variance $`v`$ with the exact mean), `DiffusionDiscretization.varStep_eq_opt` (excess $`(d/2)(\log(v/v^*) + v^*/v - 1)`$), `DiffusionDiscretization.varStep_opt_le`, `DiffusionDiscretization.postVarHeat`, `DiffusionDiscretization.postVarHeat_pos`, `DiffusionDiscretization.ouFisherInfo_eq` | Verified (DF-4). Proves a version of Corollary 2 for data with finite second moment: $`v^* = C/d`$ with $`C = (d\beta_k - \beta_k^2 J(p_k))/\alpha_k^2`$, which is Bao's $`\sigma_n^{*2}`$ after the change of notation. The excess over the optimum is exact |
| Two-sided bounds on the optimal variance (Theorem 2; Corollary 3) | differentiation | Ingredients only: `DiffusionDiscretization.heatFisherInfo_le` ($`J(u) \le d/u`$) and `DiffusionDiscretization.postVarHeat_pos` | Not formalised as a theorem. The bounds $`\tilde\beta_k \le v^* \le \beta_k/\alpha_k^2`$ follow from $`0 \le J \le d/u`$, but only $`C \gt 0`$ is stated. The bounded-support bound is not formalised |
| Monte Carlo estimate of the averaged score norm (Eqs. (8)–(10)) | score | not formalised; SE-4 treats a different Monte Carlo estimator (the posterior mean) | Not formalised |
| Optimal trajectory by dynamic programming (Theorem 3) | — | not formalised | Not formalised |

### Chen et al. (2023)

Sitan Chen, Sinho Chewi, Jerry Li, Yuanzhi Li, Adil Salim, Anru R. Zhang. Sampling is as easy as
learning the score: theory for diffusion models with minimal data assumptions. ICLR 2023.
[arXiv:2209.11215](https://arxiv.org/abs/2209.11215).

**Algorithm.** OU forward process $`dX_t = -X_t\,dt + \sqrt{2}\,dB_t`$. The library defines its
discrete skeleton `Diffusion.fwdKernel` directly; the SDE is not defined. Sampler (2.8): exponential
integrator for the reverse SDE, with the score frozen at the left grid point, started at
$`\mathcal{N}(0, I)`$. As a Gaussian kernel its mean is $`e^h y + 2(e^h - 1)s(y)`$ and its variance
is $`e^{2h} - 1`$. The library sampler `Diffusion.algKernel`, with `Diffusion.scoreMean` and
`Diffusion.ddpmVar`, has the same variance and mean $`e^h y + (e^h - e^{-h})s(y)`$. Also treated:
the critically damped Langevin diffusion (CLD).

**Main result.** Theorem 2 assumes $`L`$-Lipschitz scores (A1), finite second moment $`m_2^2`$ (A2)
and an $`L^2(q_{kh})`$ score error $`\varepsilon_{\mathrm{score}}`$ (A3). For $`h \lesssim 1/L`$:
```math
\mathrm{TV}(p_T, q) \lesssim \sqrt{\mathrm{KL}(q \Vert \gamma^d)}\,e^{-T} + (L\sqrt{dh} + L m_2
h)\sqrt{T} + \varepsilon_{\mathrm{score}}\sqrt{T}.
```
Corollaries 3–5 cover bounded support, early stopping and $`W_2`$. Theorem 6 treats CLD. Theorem 7:
for CLD with standard Gaussian data, exact scores and $`h \le 1/10`$, the path-space KL is at least
$`dhT`$. The proofs use Girsanov's theorem (Theorem 8) and a discretisation bound (Theorem 9) built
on moment and movement bounds (Lemmas 10–11).

| Step | Move | Library | Status |
|---|---|---|---|
| Forward process and its time reversal (§2) | identification | `Diffusion.fwdKernel`, `Diffusion.revKernel`. DF-5: `DiffusionPath.fwdPath_eq_truePath`. KR-2: `ReverseKernel.isReverseKernel_posterior`, `ReverseKernel.reverseChain_comp_forwardMarginal`. ID-4: `ReverseTime.reverse_fokkerPlanck` | Verified (DF-1, DF-5, KR-2, ID-4) in discrete time and as a strong-form PDE identity; the reverse SDE is not formalised |
| Denoising score matching equivalence (App. A) | score | Related: `Diffusion.postMean_ae_eq_tweedie` (DF-1), `Tweedie.tweedie` (SE-3), `SteinObjective.steinObjective_eq` (SE-1, Hyvärinen form) | Not formalised; the related statements are Verified |
| Path KL by Girsanov, split into score error and discretisation (Theorem 8; Eq. (5.6)) | error accumulation | DF-5: `DiffusionPath.klDiv_truePath_algPath`, `DiffusionPath.klDiv_truePath_eq_disc_add_meanErr`. DF-1: `Diffusion.lintegral_klDiv_revKernel_eq`. GI-1: `GaussianIncrement.klDiv_emKernelPi`, `GaussianIncrement.klDiv_emChainPi_le_sum` (frozen-drift chains, per-step integrand $`h \Vert b - \hat{b} \Vert^2/4`$) | Related statement (DF-5, DF-1, GI-1; Verified): a discrete-time chain rule, and the split is an equality. Girsanov's theorem is not formalised |
| Score-error term (A3) | error accumulation, score | `Diffusion.lintegral_meanError_eq_scoreError`, `Diffusion.klDiv_output_le_score` | Verified (DF-1), with the error averaged under $`p_k`$ |
| Discretisation bound under Lipschitz scores (Theorem 9; Lemmas 10–11) | differentiation | not formalised. Different route: `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le` (DF-1) bounds the discretisation term without smoothness assumptions | Not formalised |
| Initialisation: OU convergence in KL plus data processing | contraction | `Diffusion.klDiv_fwdLaw_le_init`, `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`, `KL.klDiv_comp_le_compProd`, `DiffusionPath.klDiv_output_le_path` | Verified (DF-1, DF-5, KL-2); the OU decay used is listed under FL-4 (Conditional overall) and has no named hypothesis |
| KL to TV: Pinsker and the triangle inequality over three chains | comparison | KL-1: `Pinsker.tvSup_le_sqrt_klDiv`. KR-1: `ErrorDecomposition.tvSup_le_three_chain`. DF-1: `DiffusionDiscretization.tvSup_output_le_ddpm_grid` | Verified (KL-1, KR-1, DF-1) |
| Lower bound on the path KL for Gaussian data (Theorem 7, CLD) | exact computation | DF-8: `DiffusionGaussian.klDiv_truePath_isoGauss_ddpm_ge`, giving at least $`d(t_N - t_1)h/(1+h)`$ for $`\mathcal{N}(0, vI)`$ with $`v \le 1`$, the uniform grid and every mean map. DF-5: `DiffusionPath.klDiv_truePath_ddpm_ge` | Related statement (DF-8, DF-5; Verified), for the DDPM chain instead of CLD |
| Wasserstein corollaries and CLD analysis (Corollary 5, Theorem 6) | — | not formalised. $`W_2`$ is not defined, and there are no kinetic models. Early stopping is built into the library's target $`p_{t_1}`$ | Not formalised |

### Chen–Lee–Lu (2023)

Hongrui Chen, Holden Lee, Jianfeng Lu. Improved Analysis of Score-based Generative Modeling:
User-Friendly Bounds under Minimal Smoothness Assumptions. ICML 2023.
[arXiv:2211.01916](https://arxiv.org/abs/2211.01916).

**Algorithm.** OU forward process with $`f = -x/2`$ and $`g = 1`$, whose time is twice the
library's. Two schemes for the reverse SDE with a score estimate frozen on each step: exponential
integrator (Eq. (6)) and Euler–Maruyama (Eq. (5)). Both start at $`\mathcal{N}(0, I)`$ and stop at
$`\delta`$. In library time the exponential-integrator step is a Gaussian kernel with the variance
of `Diffusion.ddpmVar` and score coefficient $`2(e^h - 1)`$. The library sampler
`Diffusion.algKernel` with `Diffusion.scoreMean` uses $`e^h - e^{-h}`$.

**Main result.** Theorem 1 (Lipschitz score, uniform steps):
$`\mathrm{KL} \lesssim (M_2 + d)e^{-T} + T\varepsilon_0^2 + dT^2L^2/N`$ for the exponential
integrator, plus a $`T^3 M_2/N^2`$ term for Euler–Maruyama. Theorem 2 (finite second moment only,
early stopping, steps with $`h_k/\sigma_{t_{k-1}}^2 \le 1/(Kd)`$):
```math
\mathrm{KL}(p_\delta \Vert \hat{q}_{T-\delta}) \lesssim (d + M_2)e^{-T} + T\varepsilon_0^2 + d^2\Pi,
```
with $`\Pi = \sum_k h_k^2/\sigma_{t_{k-1}}^4`$. Exponentially decaying steps give
$`\tilde{O}(d^2 \log^2(1/\delta)/\varepsilon_0^2)`$ steps. Corollaries 3–4 combine Wasserstein and
KL bounds; Theorem 5 treats smooth data.

| Step | Move | Library | Status |
|---|---|---|---|
| KL chain rule over steps; Girsanov / differential inequality along the path (§3.1, Lemmas 6–7, Proposition 8) | error accumulation | DF-5: `DiffusionPath.klDiv_pathLaw`, `DiffusionPath.klDiv_truePath_algPath`. KL-2: `KL.klDiv_chain_le_sum`. GI-1: `GaussianIncrement.klDiv_emChainPi_le_sum` | Verified (DF-5, KL-2, GI-1) as a discrete-time chain rule; the continuous-time Girsanov or differential-inequality form is not formalised |
| Initialisation error (Lemma 9) | contraction | `Diffusion.klDiv_fwdLaw_le_init`, `Diffusion.klDiv_fwdLaw_one_le`, `Diffusion.toReal_klDiv_fwdLaw_le`, via `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le` | Verified (DF-1). Proves a version with a factor depending on $`t_1`$; the OU decay used is listed under FL-4 (Conditional overall) and has no named hypothesis |
| Split of the per-step error into score error (term (2)) and discretisation (term (3)) by the triangle inequality (§3.1) | error accumulation | `Diffusion.lintegral_klDiv_revKernel_eq`, `Diffusion.lintegral_meanError_eq_scoreError` (DF-1); `DiffusionPath.klDiv_truePath_eq_disc_add_meanErr` (DF-5) | Verified (DF-1, DF-5): an equality, with the score error averaged under $`p_k`$ |
| Discretisation bound under finite second moment: reduction of term (3) to a space term (Lemma 11), Hessian bounds and change of measure (§3.2, Lemmas 12–13) | differentiation | Library route: the per-step identity `DiffusionDiscretization.lintegral_klDiv_revKernel_ddpm_eq` and the summed entropy increments `DiffusionDiscretization.sum_entropyStep_le`, from the de Bruijn identity `DiffusionDiscretization.hasDerivAt_heatNegEntropy`, Fisher monotonicity `DiffusionDiscretization.heatFisherInfo_anti` and $`J(u) \le d/u`$ `DiffusionDiscretization.heatFisherInfo_le`. End-to-end: `DiffusionDiscretization.klDiv_output_le_ddpm_grid` | Lemmas 11–13 are not formalised. The library proves a related bound, linear in $`d`$ (DF-1, Verified) |
| Lipschitz-score bound (Theorem 1) and the Euler–Maruyama comparison | differentiation | not formalised | Not formalised |
| Exponentially decaying steps minimise the bound (App. B) | exact computation | DF-6: `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_dirac`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_dirac_ge` (for a point mass, the geometric grid minimises the exact per-step sum). DF-1: `DiffusionDiscretization.klDiv_output_le_geomGrid` | Related statement (DF-6, DF-1; Verified) for a different objective, the exact per-step sum for a point mass; the argument of App. B is not formalised |
| KL to TV and Wasserstein corollaries (Corollaries 3–4) | comparison | KL-1: `Pinsker.tvSup_le_sqrt_klDiv`; $`W_2`$ is not defined | Pinsker Verified (KL-1); the Wasserstein part is not formalised |

### Benton–De Bortoli–Doucet–Deligiannidis (2024)

Joe Benton, Valentin De Bortoli, Arnaud Doucet, George Deligiannidis. Nearly d-Linear Convergence
Bounds for Diffusion Models via Stochastic Localization. ICLR 2024.
[arXiv:2308.03686](https://arxiv.org/abs/2308.03686).

**Algorithm.** OU forward process with early stopping at $`\delta`$. The sampler is an exponential
integrator (Eq. (4)) for the reverse SDE, with the score frozen on each step and steps
$`\gamma_k \le \kappa \min\{1, T - t_{k+1}\}`$. The library's DF-1 sampler, `Diffusion.algKernel`
with mean `Diffusion.scoreMean` and variance `Diffusion.ddpmVar`, has the same variance
$`e^{2h} - 1`$. Its score coefficient is $`e^h - e^{-h}`$ instead of $`2(e^h - 1)`$. The library's
grid condition is $`u_{k+1} - u_k \le \kappa u_k`$ in heat time $`u = e^{2t} - 1`$
(`DiffusionDiscretization.heatTime`).

**Main result.** Theorem 1 (data with identity covariance):
```math
\mathrm{KL}(q_\delta \Vert p_{t_N}) \lesssim \varepsilon^2 + \kappa^2 dN + \kappa dT + de^{-2T}.
```
Theorem 2 (finite second moment $`M_2`$) adds $`\kappa M_2 + (d + M_2)e^{-2T}`$. Corollary 1: a
number of steps nearly linear in $`d`$ suffices. The discretisation bound (Lemma 2) is proved with
stochastic localisation (Lemma 1) and Itô calculus. §4 notes that the path-space KL is of order
$`d\kappa`$ in the worst case, and App. H shows that linear dependence on $`d`$ cannot be improved,
by tensorisation.

| Step | Move | Library | Status |
|---|---|---|---|
| Path KL via Girsanov; change of initial law and data processing (Lemma 8; Eq. (17)) | error accumulation | DF-5: `DiffusionPath.klDiv_truePath_algPath`, `DiffusionPath.klDiv_output_le_path`. KL-2: `KL.klDiv_comp_le_compProd`, `KL.klDiv_chain_le_sum` | Related statement (DF-5, KL-2; Verified): a discrete-time chain rule; Girsanov's theorem is not formalised |
| Score as posterior mean; Hessian as posterior covariance (Lemma 5) | score | (i) `Diffusion.postMean_ae_eq_tweedie` (DF-1), `OUPosterior.ouPosteriorScore_pi` (SE-3). (ii) not formalised | (i) Verified (DF-1, SE-3); (ii) not formalised |
| Discretisation error $`\kappa^2 dN + \kappa dT`$ (Lemma 2) via stochastic localisation (Lemma 1) and Itô calculus (Lemmas 3–4, 6–7) | differentiation | The per-step identity `DiffusionDiscretization.lintegral_klDiv_revKernel_ddpm_eq` (exact per-step KL as an entropy increment of the heat flow) and the summed entropy increments `DiffusionDiscretization.sum_entropyStep_le`, from `DiffusionDiscretization.hasDerivAt_heatNegEntropy` (de Bruijn), `DiffusionDiscretization.heatFisherInfo_anti` and `DiffusionDiscretization.heatFisherInfo_le`. Sum: `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le` | Verified (DF-1). Proves a version for the Tweedie-mean sampler: $`(\kappa d/2)(1 + \log(u_N/u_1))`$. Stochastic localisation and Itô calculus are not formalised |
| Score-error term (Assumption 1) | error accumulation, score | `Diffusion.lintegral_meanError_eq_scoreError`, `Diffusion.klDiv_output_le_score` | Verified (DF-1): weight $`\beta_k/2`$ per step, with the error averaged under $`p_k`$ |
| Initialisation: OU convergence in KL (Propositions 4–5) | contraction | `Diffusion.klDiv_fwdLaw_one_le`, `Diffusion.toReal_klDiv_fwdLaw_le`, `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le` | Verified (DF-1). Proves a version with a factor depending on $`t_1`$; the OU decay used is listed under FL-4 (Conditional overall) and has no named hypothesis |
| End-to-end bound (Theorem 2) | error accumulation | `Diffusion.klDiv_output_le_explicit`, `DiffusionDiscretization.klDiv_output_le_ddpm_grid`, `DiffusionDiscretization.klDiv_output_le_ddpm_grid_explicit`, `DiffusionDiscretization.tvSup_output_le_ddpm_grid` | Verified (DF-1). Proves a version of Theorem 2 for the Tweedie-mean sampler with explicit constants: initialisation term $`+ (\kappa d/2)(1 + \log(u_N/u_1)) + \sum_k (\beta_k/2)\mathbb{E}\Vert \hat{s}_k - \nabla \log p_k \Vert^2`$ |
| Step schedule and iteration count (Corollary 1, App. D) | differentiation | `DiffusionDiscretization.geomGrid`, `DiffusionDiscretization.klDiv_output_le_geomGrid`, `DiffusionDiscretization.explicit_geomGrid_params`, `DiffusionDiscretization.klDiv_output_le_geomGrid_steps`, `DiffusionDiscretization.tvSup_output_le_geomGrid_steps`, `DiffusionDiscretization.exists_klDiv_output_le` | Verified (DF-1): proves a version of Corollary 1 with an explicit step count, for the Tweedie-mean sampler on geometric grids and with the score error as an input |
| Path KL of order $`d\kappa`$ in the worst case (§4) | exact computation | DF-5: `DiffusionPath.klDiv_truePath_ddpm_ge`, `DiffusionPath.klDiv_truePath_ddpm_ge_uniform`. DF-6: `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_dirac`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_geomGrid_ge` | Related statement (DF-5, DF-6; Verified). The DF-5 lower bound holds for every measurable mean map, so it covers the exponential-integrator step as a discrete path |
| Linear dependence on $`d`$ is optimal, by tensorisation (App. H) | comparison, exact computation | KL-4: `GaussianIncrement.klDiv_pi_pi` | Component only (KL-4, Verified); the argument itself is not formalised |

### Conforti–Durmus–Gentiloni Silveri (2023)

Giovanni Conforti, Alain Durmus, Marta Gentiloni Silveri. KL Convergence Guarantees for Score
Diffusion Models under Minimal Data Assumptions.
[arXiv:2308.12240](https://arxiv.org/abs/2308.12240) (numbering as in the current arXiv version).

**Algorithm.** OU forward process. The sampler (Eq. (9)) is an exponential integrator on the
relative score $`\tilde{s} \approx 2(x + \nabla \log p)`$: a Gaussian step with mean
$`e^{-h}y + (1 - e^{-h})\tilde{s}(y)`$ and variance $`1 - e^{-2h} = \beta`$. In the library:
`Diffusion.algKernel` with mean `Diffusion.scoreMean` and variance
`DiffusionDiscretization.betaVar`. The step variance $`\beta_k`$ is the same; the mean is in Tweedie
form. Also treated: the kinetic OU process.

**Main result.** Theorem 1 (constant step $`h \le 1`$, finite relative Fisher information, no early
stopping):
```math
\mathrm{KL}(\mu^\star \vert p_T) \lesssim e^{-2T}\mathrm{KL}(\mu^\star \vert \gamma) +
T\varepsilon^2 + h I(\mu^\star \vert \gamma).
```
Theorem 2 uses a relative score error; Theorem 3 uses exponential-then-constant steps. Corollary 1
(finite second moment, early stopping at $`\delta`$): the discretisation term is
$`c(d + M_2^2)(\log(d + M_2^2) + \log \delta^{-1} + 1)`$, where $`c`$ is the step-size parameter,
and does not grow with $`T`$. Theorems 4–5 treat the kinetic OU process.

| Step | Move | Library | Status |
|---|---|---|---|
| Path KL via Girsanov and data processing | error accumulation | DF-5: `DiffusionPath.klDiv_truePath_algPath`, `DiffusionPath.klDiv_truePath_betaVar_le`, `DiffusionPath.klDiv_output_le_path` | Related statement (DF-5, Verified): a discrete-time chain rule; Girsanov's theorem is not formalised |
| Initialisation via OU contraction and the Gaussian log-Sobolev inequality | contraction | `Diffusion.klDiv_fwdLaw_le_init`, `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`; Gaussian LSI is KL-5 | Verified (DF-1, KL-5); the OU decay used is listed under FL-4 (Conditional overall) and has no named hypothesis |
| Fisher-information decay along the OU flow (Proposition 3) | differentiation | KL-5: `GaussianLSIPi.heatFisher_gaussian_le`, i.e. $`I(t + a) \le ((v+t)/(v+t+a))^2 I(t)`$ along the heat flow. With $`v = 1`$ and $`1 + u = e^{2t}`$ this is the OU-time statement | Verified (KL-5) in heat-flow time; the OU-time form is not stated separately |
| Discretisation error bounded by Fisher information via Itô's formula for the relative score (Proposition 2, Lemma 2) | differentiation | DF-4: `DiffusionDiscretization.lintegral_klDiv_revKernel_fwdVar_eq` (exact per-step formula for $`\sigma^2 = \beta`$), `DiffusionDiscretization.sq_le_mul_heatFisherInfo` (trace Cramér–Rao $`d^2 \le (M + du)J(u)`$), `DiffusionDiscretization.mul_fisherGap_le`, `DiffusionDiscretization.sum_betaStep_le_of_le_mul`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_betaVar_le_of_le_mul` | Related statement (DF-4, Verified). With early stopping and grids that are geometric up to a factor $`m`$, the discretisation term is independent of $`T`$ and $`N`$. No Itô calculus is used. Theorem 1 without early stopping is not formalised |
| Fisher information after smoothing, $`I(\mu P_\delta \vert \gamma) \lesssim d/\delta + M_2^2`$ (Lemma 5) | differentiation | Related: `DiffusionDiscretization.heatFisherInfo_le` ($`J(u) \le d/u`$ for the Fisher information of the smoothed law) | Related statement Verified (DF-1 ingredient); the relative Fisher information bound is not stated |
| End-to-end bound with early stopping (Corollary 1) | error accumulation | DF-4: `DiffusionDiscretization.klDiv_output_le_betaVar`, `DiffusionDiscretization.klDiv_output_le_betaVar_explicit`, `DiffusionDiscretization.tvSup_output_le_betaVar` | Related statement (DF-4, Verified): same step variance, with a Tweedie-form mean instead of the exponential-integrator mean |
| Kinetic OU process (Theorems 4–5) | — | not formalised | Not formalised |

### Koike (2026)

Yuta Koike. Connections between the Föllmer process and the denoising diffusion probabilistic model.
[arXiv:2605.18040](https://arxiv.org/abs/2605.18040) (v2, 2026).

**Algorithm.** The Föllmer process on $`[0, 1]`$ and its Euler–Maruyama discretisation (§3.1). After
rescaling, Koike identifies the discretisation with a DDPM sampler (Eq. (3.12)) with
$`\alpha_i = t_i/t_{i+1}`$. In library terms this is `Diffusion.algKernel` with mean
`Diffusion.scoreMean` and step variance $`\beta_k = 1 - \alpha_k^2`$
(`DiffusionDiscretization.betaVar`), with library $`\alpha_k^2 = t_i/t_{i+1}`$.

**Main result.** Theorem 2.1: the Föllmer process exists as a weak solution, with no assumptions on
the target. Proposition 3.1: a time change turns it into the DDPM reverse SDE. Theorem 3.1 assumes
the grid condition [A1] $`h_i \le \kappa(1 - t_{i+1})`$, the score error [A2] and $`t_0 \le 1/2`$.
It gives
```math
H(P^{X_{t_N}} \vert P^{X^{\mathrm{EM}}_{t_N}}) \le \varepsilon_{\mathrm{score}}^2 + \kappa d \log((1
- t_0)/\delta) + 2\kappa \mathbb{E}\vert X_1 \vert^2 + (t_0/2)(d + \mathbb{E}\vert X_1 \vert^2),
```
with no $`\kappa dT`$ term (Remark 3.2). Corollary 3.2 gives the number of steps for a target TV
error. Theorem 3.2 assumes finite Fisher information and needs no early stopping. Theorems 3.3–3.4
give intrinsic-dimension bounds.

| Step | Move | Library | Status |
|---|---|---|---|
| Föllmer process, stochastic localisation and the time change to the DDPM reverse SDE (Theorem 2.1, Propositions 2.1–2.9, 3.1) | — | not formalised (no SDEs) | Not formalised |
| DDPM sampler as the Euler–Maruyama discretisation (§3.1) | setting | `Diffusion.algKernel`, `Diffusion.scoreMean`, `DiffusionDiscretization.betaVar`, `Diffusion.betaGrid` | Verified as definitions (DF-4 setting); the identification with the Föllmer discretisation is not formalised |
| Data processing and Girsanov for the path KL (Lemmas A.4–A.5) | error accumulation | DF-5: `DiffusionPath.klDiv_truePath_algPath`, `DiffusionPath.klDiv_output_le_path`, `DiffusionPath.klDiv_truePath_betaVar_le` | Related statement (DF-5, Verified): a discrete-time chain rule; Girsanov's theorem is not formalised |
| Discretisation bound via martingale increments of $`v_t`$ and summation by parts (§A.7) | differentiation | DF-4: `DiffusionDiscretization.lintegral_klDiv_revKernel_fwdVar_eq`, `DiffusionDiscretization.sq_le_mul_heatFisherInfo`, `DiffusionDiscretization.sum_betaStep_le_of_le_mul`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_betaVar_le_of_le_mul` | Proves a version (DF-4, Verified) by an exact per-step formula and the trace Cramér–Rao bound, not by martingale arguments |
| End-to-end bound (Theorem 3.1, Corollary 3.1), with TV by Pinsker | error accumulation | `DiffusionDiscretization.klDiv_output_le_betaVar`, `DiffusionDiscretization.klDiv_output_le_betaVar_explicit`, `DiffusionDiscretization.tvSup_output_le_betaVar` (DF-4); `DiffusionPath.klDiv_truePath_betaVar_le_explicit` (DF-5) | Verified (DF-4, DF-5). Proves a version of Theorem 3.1 for the same sampler, with a different grid condition and constants |
| No $`\kappa dT`$ term compared with the variance $`\beta/\alpha^2`$ (Remark 3.2) | exact computation | For $`\sigma^2 = \beta/\alpha^2`$ and $`M \le d`$, the per-step sum is at least $`(d/2)\sum_k (2h_k - \beta_k)`$ (`DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_ge`), and on uniform grids the path KL grows linearly in $`t_N - t_1`$ (`DiffusionPath.klDiv_truePath_ddpm_ge_uniform`) | Related statement (DF-4, DF-5; Verified) |
| Step count for a target TV error (Corollary 3.2) | — | not formalised; the TV bound itself is `DiffusionDiscretization.tvSup_output_le_betaVar` (DF-4) | Not formalised as a theorem |
| Finite Fisher information without early stopping (Theorem 3.2), intrinsic dimension (§3.2), score-matching identity (Remark 3.1) | — | not formalised | Not formalised |

### Li–Yan (2024)

Gen Li, Yuling Yan. O(d/T) Convergence Theory for Diffusion Probabilistic Models under Minimal
Assumptions. [arXiv:2409.18959](https://arxiv.org/abs/2409.18959).

**Algorithm.** Forward chain (Eq. (2.1)) with the learning-rate schedule of Eq. (2.3). Sampler (Eq.
(2.4)): $`Y_{t-1} = \alpha_t^{-1/2}(Y_t + \eta_t s_t(Y_t) + \sigma_t Z_t)`$ with
$`\eta_t = \sigma_t^2 = 1 - \alpha_t`$. Their $`\alpha_t`$ is the library's $`\alpha_k^2`$. In
library terms: `Diffusion.algKernel` with mean `Diffusion.scoreMean` and variance
`Diffusion.ddpmVar`, on the grid `Diffusion.betaGrid`.

**Main result.** Theorem 1 assumes $`\mathbb{E}\Vert X_0 \Vert \le T^{c_M}`$ and an $`L^2`$ score
error $`\varepsilon_{\mathrm{score}}`$, and gives
$`\mathrm{TV}(q_1, p_1) \le c\, d \log^3 T/T + c\, \varepsilon_{\mathrm{score}} \sqrt{\log T}`$.
Theorem 2 gives $`O(k/T)`$ for data of intrinsic dimension $`k`$. §3.1 explains that the route
$`\mathrm{TV}^2 \le \mathrm{KL}/2 \le \mathrm{KL}(\text{path})/2`$ (Eq. (3.3)) stops at
$`O(\sqrt{d/T})`$, because the path KL can be of order $`d/T`$. The proof (§4) instead runs a direct
recursion for TV with auxiliary sequences (Lemmas 1–2).

| Step | Move | Library | Status |
|---|---|---|---|
| Forward chain and sampler (Eqs. (2.1), (2.4)) | setting | `Diffusion.fwdKernel`, `Diffusion.betaGrid`, `Diffusion.algKernel`, `Diffusion.scoreMean`, `Diffusion.ddpmVar` | Verified (DF-1) |
| Score in Tweedie form and the score-error term | error accumulation, score | `Diffusion.postMean_ae_eq_tweedie`, `Diffusion.lintegral_meanError_eq_scoreError` | Verified (DF-1) |
| KL route: Pinsker and data processing from the path KL (Eq. (3.3)) | comparison | KL-1: `Pinsker.tvSup_le_sqrt_klDiv`. DF-5: `DiffusionPath.klDiv_output_le_path` | Verified (KL-1, DF-5) |
| The path KL is of order $`d/T`$, so the KL route stops at $`O(\sqrt{d/T})`$ (§3.1) | exact computation | DF-5: `DiffusionPath.klDiv_truePath_ddpm_ge`, `DiffusionPath.klDiv_truePath_ddpm_ge_uniform`. DF-6: `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_ge_log`. DF-8: `DiffusionGaussian.klDiv_truePath_isoGauss_ddpm_ge` | Verified (DF-5, DF-6, DF-8). Formalises a version for this sampler: on uniform grids with $`M \le d`$ the path KL is at least of order $`dh(t_N - t_1)`$, for every mean map |
| Direct TV recursion with auxiliary sequences (§4, Lemmas 1–2); Theorems 1–2 | error accumulation | not formalised. For the same sampler, DF-1 gives a KL/TV bound of a different order (`DiffusionDiscretization.tvSup_output_le_ddpm_grid`) | Not formalised |

### Jiao–Zhou–Li (2025)

Yuchen Jiao, Yuchen Zhou, Gen Li. Optimal Convergence Analysis of DDPM for General Distributions.
[arXiv:2510.27562](https://arxiv.org/abs/2510.27562).

**Algorithm.** Forward chain with the learning-rate schedule of Eq. (10). Sampler (Eq. (8)):
$`Y_{t-1} = \alpha_t^{-1/2}(Y_t + \eta_t s_t(Y_t) + \sigma_t Z_t)`$ with $`\eta_t = 1 - \alpha_t`$.
Their $`\alpha_t`$ is the library's $`\alpha_k^2`$. With $`\sigma_t^2 = 1 - \alpha_t`$ this is
`Diffusion.algKernel` with mean `Diffusion.scoreMean` and variance `Diffusion.ddpmVar`. With
$`\sigma_t^2 = (1 - \alpha_t)\alpha_t`$ the variance is `DiffusionDiscretization.betaVar`. The
analysis uses an auxiliary reverse process (Eq. (18)) built from the probability-flow map plus
Gaussian noise, which has the forward marginals.

**Main result.** Theorem 1 assumes a second moment at most $`T^{c_R}`$ (Assumption 1) and a weighted
score error (Assumption 2); $`L`$ is the non-uniform Lipschitz constant of Definition 1. It gives
```math
\mathrm{TV} \le \sqrt{\mathrm{KL}/2} \le C\sqrt{d}\min\{\sqrt{d}, L\}\log^2 T/T +
C\varepsilon_{\mathrm{score}}\sqrt{\log T},
```
so KL is of order $`d\min\{d, L^2\}/T^2`$ up to logarithms. Theorem 2 covers data
$`\mathcal{N}(0, \lambda I_d)`$ with $`\lambda \ge 2`$, oracle scores, schedule (10), and three
reverse-variance choices including $`\sigma_t^2 = 1 - \alpha_t`$ and
$`\sigma_t^2 = (1 - \alpha_t)\alpha_t`$. In that setting
$`\mathrm{KL}(p_{X_1} \Vert p_{Y_1}) \ge c_{\mathrm{low}} d/T^2`$.

| Step | Move | Library | Status |
|---|---|---|---|
| Forward chain and sampler (Eqs. (8), (10)) | setting | `Diffusion.betaGrid`, `Diffusion.algKernel`, `Diffusion.scoreMean`, `Diffusion.ddpmVar`, `DiffusionDiscretization.betaVar` | Verified (DF-1, DF-4 setting) |
| Score in Tweedie form | score | `Diffusion.postMean_ae_eq_tweedie` (DF-1), `OUPosterior.ouPosteriorScore_pi` (SE-3) | Verified (DF-1, SE-3) |
| Auxiliary reverse process with the forward marginals via the probability-flow map (Eqs. (16)–(18), Lemma 1) | identification | not formalised. Related: the library's reverse chain is the Bayes-posterior chain (`DiffusionPath.fwdPath_eq_truePath`, DF-5). The continuous-time fact that probability-flow transport and the Langevin / Fokker–Planck evolution share one-time marginals is FL-5 | Not formalised; FL-5 is Conditional (on `WeakFokkerPlanck` and `UniqueWeakContinuity`) |
| Pinsker and the chain rule along the auxiliary chain (Eq. (20)) | comparison, error accumulation | KL-1: `Pinsker.tvSup_le_sqrt_klDiv`. KL-2: `KL.klDiv_chain_le_sum`. DF-5: `DiffusionPath.klDiv_pathLaw` (chain rule for any two Markov chains), `DiffusionPath.klDiv_output_le_path` | Verified as generic statements (KL-1, KL-2, DF-5); not instantiated for the auxiliary chain |
| Per-step bound via the conditional covariance of the noise (Lemma 2), summation under the schedule (Lemma 3), Theorem 1 | differentiation | not formalised. Related: DF-5 shows that the chain rule along the true reverse chain cannot give order $`1/N^2`$ through the full path KL when $`M \le d`$ on uniform grids (`DiffusionPath.klDiv_truePath_ddpm_ge_uniform`) | Not formalised; the related lower bound is Verified (DF-5) |
| Lower bound for Gaussian data (Theorem 2) | exact computation | DF-8. `DiffusionGaussian.klDiv_output_isoGauss_eq`: exact output KL for $`\mathcal{N}(0, vI)`$ data, exact score and any reverse variances. `DiffusionGaussian.gaussian_output_two_sided` and `DiffusionGaussian.klDiv_output_isoGauss_ddpm_ge_sq`: for $`\sigma^2 = \beta/\alpha^2`$, $`v \le 1`$ and a uniform grid with $`e^{2h} \le 2`$, $`\mathrm{KL} \ge dh^2(1 - e^{-2(t_N - t_1)})^2/3`$. `DiffusionGaussian.klDiv_output_isoGauss_ddpm_ge_of_one_le` covers $`v \ge 1`$ under an initialisation condition. `DiffusionGaussian.klDiv_output_isoGauss_beta_one`: for $`\sigma^2 = \beta`$ and $`v = 1`$, KL is 0 | Related statement (DF-8, Verified): the same order $`dh^2`$ for $`v \le 1`$ on uniform grids. The case $`\lambda \ge 2`$ on schedule (10) is not covered as stated |

### Li–Cai (2024)

Gen Li, Changxiao Cai. Provable Acceleration for Diffusion Models under Minimal Assumptions.
[arXiv:2410.23285](https://arxiv.org/abs/2410.23285).

**Algorithm.** A training-free accelerated stochastic sampler (Eq. (11)) with an intermediate point
and a clipped second-order score correction. The analysis uses an auxiliary process (Eq. (19)) built
from probability-flow maps $`\Phi_t`$ plus Gaussian noise, which has the forward marginals (Lemma
3). The library defines neither.

**Main result.** Theorem 1 assumes a finite second moment and an $`L^2`$ score error. It gives
```math
\mathrm{TV}(p_{X_1}, p_{Y_1}) \le \sqrt{\mathrm{KL}(p_{X_1} \Vert p_{Y_1})} \le C(d^{5/2}\log^5
T/T^2 + (1 + d^{3/2}\log^3 T/T)\varepsilon_{\mathrm{score}}\sqrt{\log T}).
```
Hence $`\tilde{O}(d^{5/4}/\sqrt{\varepsilon} + d^{3/2})`$ iterations (the second term a burn-in
cost) reach TV accuracy $`\varepsilon \ge \varepsilon_{\mathrm{score}}\sqrt{\log T}`$. The proof
decomposes the KL along the auxiliary chain (Eq. (20)) with Pinsker, data processing and the chain
rule.

| Step | Move | Library | Status |
|---|---|---|---|
| Accelerated sampler, auxiliary-chain decomposition (Eq. (20)) and Theorem 1 | error accumulation | The library cites the paper only for the device of applying the chain rule along an auxiliary reverse chain with the forward marginals. The generic steps of Eq. (20) are KL-1 (`Pinsker.tvSup_le_sqrt_klDiv`), KL-2 (`KL.klDiv_chain_le_sum`) and DF-5 (`DiffusionPath.klDiv_pathLaw`). They hold for any pair of Markov chains but are not instantiated for this chain | Not formalised |

### Sun–Poor–Zhang (2026)

Qiang Sun, H. Vincent Poor, Wenyi Zhang. A Gaussian Perspective for Distributional Discrepancy in
Generative Diffusion Models. [arXiv:2601.13602](https://arxiv.org/abs/2601.13602) (v3, 2026).

**Algorithm.** Gaussian source $`\mathcal{N}(0, \Sigma_x)`$ with forward process
$`x_t = \alpha_t x_0 + \sigma_t \epsilon`$. Section III uses the deterministic reverse update (Eq.
(5), DDIM) with the optimal denoiser to get the closed-form KL. Section IV analyses the path space
of the reverse SDE with the denoiser frozen on each step (Eq. (11)). Library: forward kernel
`Diffusion.fwdKernel` (VP, isotropic). For isotropic Gaussian data, the sampler laws are exactly
Gaussian for any linear reverse means and any variances (`DiffusionGaussian.algLaw_eq_isoGauss`).

**Main result.** Proposition 1: closed-form terminal KL for a Gaussian source under the
deterministic sampler (5) with the optimal denoiser. Proposition 2: on uniform grids it expands as
$`(1/N^2)\sum_\ell E_\ell^2 + O(1/N^3)`$ (Euler–Maclaurin). Proposition 3 gives the $`W_2`$
counterpart. Theorems 1–2: tangent-law noise schedules minimise the leading term. Proposition 5:
asymptotic Girsanov expansion of the path-space KL of the frozen-denoiser reverse SDE. Theorem 3
assumes optimal denoising, equal covariance and sufficiently fine discretisation, and gives
```math
D_{\mathrm{KL}}(Q \Vert \hat{P}_\theta) \ge D_{\mathrm{KL}}(Q_G \Vert \hat{P}_G) \ge
D_{\mathrm{KL}}(q_{G,0} \Vert \hat{p}_{G,0}),
```
so the Gaussian source is extremal for the path-space KL.

| Step | Move | Library | Status |
|---|---|---|---|
| Gaussian evolution and closed-form terminal KL (Proposition 1) | exact computation | DF-8 for centred isotropic Gaussian data. `DiffusionGaussian.fwdLaw_isoGauss`: forward laws are $`\mathcal{N}(0, s_k I)`$. `DiffusionGaussian.exactScore_isoGauss`: the exact score is $`-y/s_k`$. `DiffusionGaussian.algLaw_eq_isoGauss`: sampler laws for any linear means. `DiffusionGaussian.klDiv_output_isoGauss_eq`: $`\mathrm{KL}(p_1 \Vert q_1) = d(s_1/w_1 - 1 - \log(s_1/w_1))/2`$ for the Tweedie-mean sampler with any reverse variances. `DiffusionGaussian.klDiv_isoGauss` | Related statement (DF-8, Verified): isotropic covariance and the stochastic Tweedie-mean sampler. The DDIM update and anisotropic covariances are not covered by the KL formula |
| Asymptotic expansion in $`1/N`$ (Proposition 2) | exact computation | `DiffusionGaussian.gaussian_output_two_sided`, `DiffusionGaussian.klDiv_output_isoGauss_ddpm_ge_sq`: two-sided bounds of order $`dh^2`$ for $`\sigma^2 = \beta/\alpha^2`$, $`v = 1`$, uniform grid | Related statement (DF-8, Verified); the expansion itself is not formalised |
| $`W_2`$ asymptotics (Proposition 3) | exact computation | not formalised ($`W_2`$ is not defined) | Not formalised |
| Tangent-law schedules (Theorems 1–2, Corollaries 2–4) | — | not formalised. Related: for point-mass data the geometric grid minimises the exact per-step sum (`DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_dirac_ge`, DF-6), which is a different objective | Not formalised |
| Path-space KL of the frozen-denoiser reverse SDE (Proposition 5) | error accumulation | DF-5: `DiffusionPath.klDiv_truePath_algPath` (discrete-time chain rule as an equality), `DiffusionPath.klDiv_output_le_path` | Related statement (DF-5, Verified); no Girsanov theorem and no asymptotic expansion |
| Gaussian extremality of the path KL via maximum entropy and the Cramér–Rao bound (Theorem 3) | differentiation | DF-6: `DiffusionDiscretization.le_entropyStep`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_ge_log` (lower bound on the per-step discretisation sum for every data law with second moment $`M`$), from de Bruijn and the trace Cramér–Rao bound $`d^2 \le (M + du)J(u)`$ (`DiffusionDiscretization.sq_le_mul_heatFisherInfo`). DF-5 path lower bound: `DiffusionPath.klDiv_truePath_ddpm_ge` | Related statement (DF-6, DF-5; Verified): a lower bound for every data law, not a comparison with the Gaussian path KL |

## Diffusion models: deterministic samplers and memorisation

### Li–Wei–Chen–Chi (2023)

Gen Li, Yuting Wei, Yuxin Chen, Yuejie Chi. Towards Faster Non-Asymptotic Convergence for
Diffusion-Based Generative Models. [arXiv:2306.09251](https://arxiv.org/abs/2306.09251) (v1 June
2023, v3 March 2024); accepted in part to ICLR 2024.

**Algorithm.** Forward OU chain `Diffusion.fwdKernel`,
$`x \mapsto \mathcal{N}(\alpha_k x, \beta_k I)`$ (their per-step $`\alpha_t`$ is $`\alpha_k^2`$
here, their $`\beta_t`$ is $`\beta_k`$), and two reverse samplers started at $`\mathcal{N}(0, I)`$
with output compared with $`p_1`$, the data noised to the first grid time. Deterministic sampler
(23): Dirac kernels $`y \mapsto \delta_{m_k(y)}`$ with
$`m_k(y) = y/\alpha_k + (\beta_k/(2\alpha_k)) s_k(y)`$, i.e. `algLaw zeroVar (detMean A b s)` with
$`A_k = \alpha_k^{-1} \mathrm{id}`$, $`b_k = \beta_k/(2\alpha_k)`$. Stochastic (DDPM-type) sampler
(30): Gaussian kernels
$`y \mapsto \mathcal{N}((y + \beta_k s_k(y))/\alpha_k, (\beta_k/\alpha_k^2) I)`$, i.e.
`algLaw (ddpmVar t) (scoreMean t s)`.

**Main result.** Thm 1: under an $`\ell_2`$ score error $`\varepsilon_{\mathrm{score}}`$ (Assumption
1) and a Jacobian error $`\varepsilon_{\mathrm{Jacobi}}`$ (Assumption 2), the probability-flow
sampler (23) with schedule (22) satisfies
```math
\mathrm{TV}(q_1, p_1) \lesssim d^2 \log^4 T/T + d^6 \log^6 T/T^2 + \sqrt{d \log^3 T} \,
\varepsilon_{\mathrm{score}} + d \log T \, \varepsilon_{\mathrm{Jacobi}}.
```
Thm 2: an accelerated deterministic sampler with exact scores reaches $`d^6 \log^6 T/T^2`$. Thm 3:
the DDPM-type sampler (30) satisfies
```math
\mathrm{TV} \le \sqrt{\mathrm{KL}/2} \lesssim d^2 \log^3 T/\sqrt{T} + \sqrt{d} \,
\varepsilon_{\mathrm{score}} \log^2 T.
```
Thm 4: an accelerated stochastic sampler reaches $`\sqrt{d^3 \log^{4.5} T/T}`$. §3.2 (insufficiency
of the score error assumption alone): for $`\mathcal{N}(0, 1)`$ data, a floor-function perturbation
of the last-step score with arbitrarily small $`L^2`$ error gives $`\mathrm{TV}(Y_1, X_1) = 1`$; the
authors suggest a Wasserstein metric as a way to avoid Assumption 2.

| Step | Move | Library | Status |
|---|---|---|---|
| §3.2 example: a last-step score perturbation with small $`L^2`$ error (floor function) puts the deterministic output on a lattice, at TV distance 1 from $`X_1`$ | exact computation, comparison | DF-3: `DiffusionODESeparation.ddpm_ddim_separation`, `DiffusionODESeparation.tvSup_detOutput_latticeScore_eq_one`, `DiffusionODESeparation.sum_sq_latticeScore_sub_le`, `DiffusionODESeparation.latticeScore` | Verified (DF-3). Proves a version for every data law with finite second moment, $`d \ge 1`$, and every score-affine deterministic update with $`b_2 \ne 0`$ (this covers their update (23)), with a uniformly $`\varepsilon`$-accurate score (hence $`L^2(p_k)`$-accurate) and $`\mathrm{TV}(p_1, q_1) = 1`$; the paper states the example for $`\mathcal{N}(0, 1)`$ data |
| Contrast with the stochastic sampler: the same small score error leaves DDPM accurate | error accumulation | DF-3: `DiffusionODESeparation.tvSup_ddpm_latticeScore_le`, `DiffusionODESeparation.pf_ddpm_separation_geomGrid`; through DF-1 `DiffusionDiscretization.tvSup_output_le_ddpm_grid` | Verified (DF-3): with the same score, DDPM with $`\sigma_k^2 = \beta_k/\alpha_k^2`$ (their sampler (30)) satisfies the DF-1 bound, whose score term is $`(\beta_2/2) \varepsilon^2`$ |
| Suggested remedy: measure the deterministic sampler in a Wasserstein metric instead of TV | error accumulation | DF-9: `DiffusionODELipschitz.eDist_detFlow_le`, `DiffusionODELipschitz.exists_coupling_detMean`, `DiffusionODELipschitz.smooth_separation_tv_far_w2_close` | Related statement (Verified, DF-9): if the exact-score step maps are Lipschitz, a uniformly accurate score keeps the deterministic output within an explicit distance of the exact-score deterministic output under a coupling ($`W_\infty`$ and $`W_2`$ bounds stated as couplings). An end-to-end Wasserstein bound to the data is not formalised, and $`W_2`$ is not defined in the library |
| Thm 1: density-ratio tracking along the deterministic trajectory (change of variables, Lemma 4) and a TV split over typical points, under score and Jacobian errors | differentiation | not formalised for diffusion samplers. Related component in another setting: DT-1 one-step push-forward density and log-determinant bounds for maps $`\mathrm{id} + \eta v`$, `DeterministicStepPi.map_withDensity_step`, `DeterministicStepPi.klDiv_map_step_le` (KL to a fixed target) | Not formalised (DT-1 is Verified but concerns a different quantity); the library does not prove that derivative-accurate scores give small TV for deterministic samplers |
| Role of derivative control of the score error (Assumption 2) | exact computation | DF-7: `DiffusionODESmooth.ddpm_ddim_smooth_separation`, `DiffusionODESmooth.le_of_lipschitzWith_errProfile` | Related statement (Verified, DF-7): an analytic, uniformly $`\varepsilon`$-accurate error at one step still gives $`\mathrm{TV}(p_1, q_1) \ge 1 - \eta`$, and its Lipschitz constant is at least $`(2^m - 1)/\lvert b_2 \rvert`$; uniform accuracy without Lipschitz control does not suffice for deterministic samplers |
| Thm 3, Step 1: chain rule for the KL between the forward and reverse Markov chains, then Pinsker | comparison, error accumulation | DF-1, DF-5, KL-1, KL-2: `Diffusion.klDiv_output_le`, `DiffusionPath.klDiv_pathLaw`, `DiffusionPath.klDiv_output_le_path`, `KL.klDiv_chain_le_sum`, `Pinsker.tvSup_le_sqrt_klDiv` | Verified, for the same sampler (their (30) is `scoreMean` with `ddpmVar`) and every data law with finite second moment (no density assumed); the path-space form is an equality in $`[0, \infty]`$ |
| Thm 3, Steps 2–3: per-step KL between the true reverse transition and the exact-score Gaussian step | differentiation | DF-1: `DiffusionDiscretization.lintegral_klDiv_revKernel_ddpm_eq`, `DiffusionDiscretization.heatFisherInfo_le`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le`; lower bounds DF-6 | Related statement (Verified, DF-1): the same per-step quantity is an entropy increment of the heat flow, and the sum is at most $`(\kappa d/2)(1 + \log(u_N/u_1))`$ on grids with $`u_{k+1} - u_k \le \kappa u_k`$; the paper's typical-set estimates and its schedule (22) are not formalised |
| Thm 3, Step 4: effect of the score error (Lemma 10) | error accumulation, score | DF-1, KL-3, SE-3: `Diffusion.klDiv_output_le`, `Diffusion.postMean_ae_eq_tweedie`, `GaussianIncrement.klDiv_pi_gaussianReal` | Verified, in a different form: the score error enters as the additive term $`\sum_k (\beta_k/2) \int \Vert s_k - \nabla \log p_k \Vert^2 \, dp_k`$ |
| Initialisation term $`\mathrm{KL}(p_{X_T} \Vert p_{Y_T})`$ (Lemma 3) | contraction | DF-1: `Diffusion.klDiv_fwdLaw_le_init`, `DiffusionDiscretization.klDiv_output_le_ddpm_grid_explicit` | Verified (DF-1): bounded by $`e^{-2(t_N - t_1)}`$ times an explicit expression in the second moment of the data |
| Thms 2 and 4: accelerated deterministic and stochastic samplers using additional learned objects (Assumptions 3–4) | error accumulation | not formalised | Not formalised |

### Li–Di–Gu (2024)

Runjia Li, Qiwei Di, Quanquan Gu. Unified Convergence Analysis for Score-Based Diffusion Models with
Deterministic Samplers. [arXiv:2410.14237](https://arxiv.org/abs/2410.14237) (v1, October 2024).

**Algorithm.** Continuous-time probability-flow ODE of the OU process,
$`dy_t = (y_t + s_\theta(T - t, y_t)) \, dt`$, and its discretisations. VP + exponential integrator:
$`y \mapsto \alpha_k^{-1} y + (\alpha_k^{-1} - 1) s_k(y)`$, which is `DiffusionODESeparation.pfMean`
run as `algLaw zeroVar` (Dirac reverse kernels from $`\mathcal{N}(0, I)`$). VE + DDIM is outside the
library, whose forward chain is OU only.

**Main result.** Thm 3.1: for the 1D OU process started at $`\mathcal{N}(0, 1)`$ and every
$`\varepsilon \gt 0`$ there is a smooth score within $`\varepsilon`$ of the true score at every time
and point for which the continuous-time probability-flow ODE ends a fixed TV distance away from the
data (Remark 3.2: smoothness of the score alone does not suffice; construction in App. B). Lemma 4.2:
time derivative of TV between two ODE flows. Thm 4.4: continuous-time TV bound under score error
(Assumption 4.1) and divergence error (Assumption 4.3). Thm 5.3: TV bound for general forward
processes and discretisations. Thms 6.5, 6.9 and Cors. 6.7, 6.11: VP + exponential integrator with
iteration complexity $`\tilde{O}(d^2/\varepsilon)`$ for bounded-support data and Lipschitz learned
scores, and polynomial complexity for VE + DDIM.

| Step | Move | Library | Status |
|---|---|---|---|
| Thm 3.1: a smooth, uniformly $`\varepsilon`$-accurate score whose deterministic output stays TV-far from the data (continuous time, Gaussian data) | exact computation, error accumulation | DF-7: `DiffusionODESmooth.ddpm_ddim_smooth_separation`, `DiffusionODESmooth.pf_ddpm_smooth_separation_geomGrid`, `DiffusionODESmooth.exists_tvSup_detOutput_smoothScore_ge`, `DiffusionODESmooth.contDiff_smoothErr`, `DiffusionODESmooth.le_of_lipschitzWith_errProfile`; DF-10: `DiffusionODELongHorizon.pf_ddpm_longHorizon_separation`, `DiffusionODEMidpoint.pf_ddpm_midpoint_separation` | Related statement (Verified, DF-7): discrete time, every data law with finite second moment, $`d \ge 1`$, every score-affine deterministic step (including `pfMean`); the error acts at one step and is an analytic function of the exact update with sup norm $`\le \varepsilon`$; $`\mathrm{TV}(p_1, q_1) \ge 1 - \eta`$ while DDPM with the same score keeps the DF-1 bound; Lipschitz constant between $`(2^m - 1)/\lvert b_2 \rvert`$ and $`(2^m + 1)/\lvert b_2 \rvert`$. The continuous-time ODE and smoothness of the score in $`y`$ are not formalised. Related statement (Verified, DF-10): the setting of Thm 3.1 (Gaussian data, stationary forward process, vanishing exact probability-flow velocity) for discrete steps, with a clamp error acting at every step over a horizon of order $`1/\varepsilon`$: the deterministic output separates from the data while DDPM with the same score stays close, and for two atoms, with the error switched on at high noise, the deterministic output collapses onto the midpoint. The continuous-time ODE and a smooth error profile are not formalised |
| Lemma 4.2: time derivative of TV between two ODE flows through the divergence of the drifts | differentiation | not formalised. FL-1 `KLTransport.hasDerivAt_klIntegral` gives the first variation of KL, not TV, along a continuity equation against a fixed reference law | Not formalised (FL-1, Verified, concerns a different divergence with a fixed second argument) |
| Thm 4.4: continuous-time TV bound under score and divergence errors | error accumulation | not formalised | Not formalised |
| Thm 5.3 and Thms 6.5, 6.9 (Cors. 6.7, 6.11): discretised TV bounds for VP + exponential integrator and VE + DDIM under Lipschitz learned scores | error accumulation | not formalised as TV bounds. For the VP + exponential-integrator step `DiffusionODESeparation.pfMean` the library proves a transport-distance coupling bound to the exact-score deterministic output under Lipschitz exact-score maps and sup-norm score error: DF-9 `DiffusionODELipschitz.exists_coupling_detMean`, and for Gaussian data `DiffusionODELipschitz.pf_isoGauss_coupling` | Not formalised (DF-9, Verified, concerns transport distance to the exact-score output, not TV to the data); VE forward processes are not in the library |

### Nie et al. (2024)

Shen Nie, Hanzhong Allan Guo, Cheng Lu, Yuhao Zhou, Chenyu Zheng, Chongxuan Li. The Blessing of
Randomness: SDE Beats ODE in General Diffusion-based Image Editing. ICLR 2024.
[arXiv:2311.01410](https://arxiv.org/abs/2311.01410) (v2, February 2024).

**Algorithm.** Two runs of the same reverse dynamics (SDE, probability-flow ODE, or Cycle-SDE) from
different initial laws $`\tilde{p}_t`$ and $`p_t`$. In library terms: two laws pushed through a
common Markov kernel (KL data processing), through the heat semigroup or the OU semigroup (de
Bruijn), or through a common deterministic map (push-forward).

**Main result.** Thm 3.1 (SDEs):
```math
D_{\mathrm{KL}}(\tilde{p}_s \Vert p_s) = D_{\mathrm{KL}}(\tilde{p}_t \Vert p_t) - \int_s^t g(\tau)^2
D_{\mathrm{Fisher}}(\tilde{p}_\tau \Vert p_\tau) \, d\tau \lt D_{\mathrm{KL}}(\tilde{p}_t \Vert p_t)
```
for $`\tilde{p}_t \ne p_t`$, under the regularity conditions of Lu et al. (2022, Assumption A.1).
Thm 3.2 (ODEs): $`D_{\mathrm{KL}}(\tilde{p}_s \Vert p_s) = D_{\mathrm{KL}}(\tilde{p}_t \Vert p_t)`$.
Thm 3.3 (Cycle-SDE): strict decrease, via the KL chain rule. Prop. D.1: exponential contraction when
the data law satisfies a log-Sobolev inequality. The results motivate SDE-based image editing
(SDE-Drag, DragBench).

| Step | Move | Library | Status |
|---|---|---|---|
| Thm 3.1: the KL derivative between two runs of the same SDE is minus a Fisher divergence (Fokker–Planck computation) | differentiation | Special cases. Heat flow (zero drift): `HeatFlowDeBruijn.hasDerivAt_heatKL`, `HeatFlowDeBruijnPi.hasDerivAt_heatKL`, $`\frac{d}{dt} \mathrm{KL}(\rho * \mathcal{N}(0, t) \Vert \pi * \mathcal{N}(0, t)) = -\tfrac{1}{2} I(\rho_t \Vert \pi_t)`$ for two probability laws (used in KL-5 and PX-2). OU run against its stationary law: `ProbabilityFlowOU.hasDerivAt_gaussKL_ouDensity` (FL-4 row) | The heat-flow identity holds under the explicit regularity hypothesis `HeatFlowRegular` / `HeatFlowRegularPi`, discharged when the second law is Gaussian and the first has finite second moment (`HeatFlowRegularity.heatFlowRegular_gaussianReal`, `HeatFlowRegularityPi.heatFlowRegularPi_gaussian`) and for warm pairs (`HeatFlowRegularityWarmPi.heatFlowRegularPi_of_warm`); the OU instance has every hypothesis discharged (listed under FL-4, Conditional overall). Reverse-time SDEs with a learned drift and the strict inequality are not formalised |
| Prop. D.1: exponential KL contraction from a log-Sobolev inequality | contraction | Discrete heat step: `ProximalSharpLSIPi.toReal_klDiv_forwardKernelPi_le_of_targetLSIPi`, $`\mathrm{KL}(\rho * \mathcal{N}(0, \eta I) \Vert \pi * \mathcal{N}(0, \eta I)) \le \mathrm{KL}(\rho \Vert \pi)/(1 + \alpha \eta)`$ (component of PX-2). OU against its Gaussian stationary law: `ProbabilityFlowOU.gaussKL_ouDensity_le` (instance of FL-4) | The forward-step contraction is a component of PX-2 (Conditional on a functional LSI of $`\pi`$), under `HeatFlowRegularPi`; FL-4 is Conditional in general, and its OU instance `ProbabilityFlowOU.gaussKL_ouDensity_le` has every hypothesis discharged; reverse-time SDEs are not formalised |
| Thm 3.2: the KL between two runs of the same ODE is constant | comparison | KL-4 `GaussianIncrement.klDiv_map_measurableEquiv` (KL is invariant under a measurable equivalence); a zero-variance sampler is a push-forward, `DiffusionODELipschitz.algLaw_zeroVar_eq_map` | Component (Verified, KL-4); that the probability-flow map is a measurable equivalence, and the continuous-time derivative computation, are not formalised |
| Thm 3.3: Cycle-SDE contraction via the KL chain rule (data processing), strictness via Lemma D.1 | comparison | KL-2: `KL.klDiv_compProd_eq_add_lintegral`, `KL.klDiv_comp_comp_le` (with a common kernel $`K`$, $`\mathrm{KL}(K\nu \Vert K\mu) \le \mathrm{KL}(\nu \Vert \mu)`$) | Non-strict data processing Verified (KL-2); the strict inequality and the Cycle-SDE kernels are not formalised |
| Premise of §3.2: the SDE and the probability-flow ODE share one-time marginals | identification | FL-5: `NoiseScore.map_flow_eq_of_weakFokkerPlanck`, `NoiseScoreOUUnconditional.map_flow_eq_ouLaw`; EX-1: `GaussianFlowVsOU.marginal_eq_and_twoTime_ne` (equal one-time marginals, different two-time laws) | FL-5 Conditional on `WeakFokkerPlanck` and `UniqueWeakContinuity` (both discharged for OU from an isotropic Gaussian initial law); EX-1 Verified (1D Gaussian); both concern forward Langevin/OU dynamics, not the learned reverse dynamics |

### Ashiq et al. (2026)

Muhammad H. Ashiq, Samanyu Arora, Abhinav N. Harish, Ishaan Kharbanda, Hung Yun Tseng, Grigorios G.
Chrysos. Why DDIM Hallucinates More Than DDPM: A Theoretical Analysis of Reverse Dynamics. ICML 2026
(PMLR 306). [arXiv:2605.06831](https://arxiv.org/abs/2605.06831) (v2, May 2026).

**Algorithm.** DDIM (probability-flow ODE) and DDPM (reverse SDE) in continuous time for
Gaussian-mixture data. The library's discrete samplers are `algLaw zeroVar (detMean A b s)` and
`algLaw (ddpmVar t) (scoreMean t s)`; no Gaussian-mixture analysis is formalised.

**Main result.** Thm 4.2 and Cor. 4.3: under two-mode dominance (Assumption 4.1), DDIM trajectories
converge exponentially fast to, and then stay in, a tube around the segment joining the two nearest
modes. Prop. 4.5 and Cor. 4.6: stable equilibria near the modes. Prop. 4.7: the midpoint is an
instantaneously unstable equilibrium of the parallel dynamics, and trajectories close enough to it
stay within a neighbourhood of radius $`\vartheta`$ for the remaining time. Prop. 5.1: DDPM ends in
that neighbourhood with exponentially small probability. Props. C.4–C.6: under a bounded, Lipschitz
score error the saddle moves, a score error with suitable directional structure can make it
instantaneously stable (C.5), and the DDPM escape bound persists (C.6).

| Step | Move | Library | Status |
|---|---|---|---|
| Reverse dynamics near the midpoint between two modes (Thm 4.2, Props. 4.5, 4.7, 5.1, C.4–C.6) | — | not formalised. The README cites the paper as prior work for a numerical one-dimensional two-mode figure whose construction is not formalised; the formal separation results DF-3 and DF-7 use an error at the last step, and DF-9 bounds transport distance, a different mechanism. DF-10 (`DiffusionODEMidpoint.pf_ddpm_midpoint_separation`) proves, for two atoms in dimension one, that the deterministic output collapses onto the midpoint under a clamp error switched on at high noise while DDPM with the same score stays close; it uses the nearly vanishing exact velocity at high noise, not the dynamics near the midpoint analysed here, and none of the paper's propositions are formalised | Not formalised |

### Pidstrigach (2022)

Jakiw Pidstrigach. Score-Based Generative Models Detect Manifolds.
[arXiv:2206.01018](https://arxiv.org/abs/2206.01018) (v1 June 2022, v3 October 2022).

**Algorithm.** Continuous-time reverse SDE with exact or approximate score, started from a prior and
run to the data time (no early stopping); for memorisation the data law is the empirical measure of
the training set. Library counterpart: the discretised DDPM
`DiffusionMemorization.exactScoreOutput (empirical x) u1 r N`, i.e.
`algLaw (ddpmVar t) (scoreMean t (exactScore (empirical x) t))` on a geometric grid, stopped at
$`t_1 \gt 0`$.

**Main result.** Thm 1: with the exact score of the forward marginals $`\pi_t`$ and
$`\mu_{\mathrm{prior}} \ll \pi_T`$, the reverse SDE has a terminal limit whose law
$`\mu_{\mathrm{sample}}`$ is absolutely continuous with respect to $`\pi_0`$ (equivalent when
$`\pi_T`$ and $`\mu_{\mathrm{prior}}`$ are), and
$`D_f(\mu_{\mathrm{sample}} \mid \pi_0) \le D_f(\mu_{\mathrm{prior}} \mid \pi_T)`$ for every
$`f`$-divergence, together with the reverse-order inequality. Thm 2: a drift error whose Girsanov
weights form a uniformly integrable martingale (for instance a bounded error) preserves this
equivalence. Cor. 1: if the score error with respect to the empirical score is exponentially
integrable along the forward process, the model has memorised its training data; generalisation
therefore requires this exponential error to be infinite.

| Step | Move | Library | Status |
|---|---|---|---|
| Thm 1(ii): data processing along the exact reverse dynamics; the divergence of the output is bounded by that of the prior | comparison | KL-2 `KL.klDiv_comp_comp_le`, KR-2 `ReverseKernel.reverseChain_comp_forwardMarginal`, `Diffusion.revKernel_comp_fwdLaw` ($`R_k \circ p_k = p_{k-1}`$); the same quantity is the initialisation term $`\mathrm{KL}(p_N \Vert \mathcal{N}(0, I))`$ of DF-1 `Diffusion.klDiv_output_le` | Verified components, for KL and the discrete chain of exact Bayes reverse kernels; general $`f`$-divergences and the continuous-time reverse SDE are not formalised |
| Thm 1(i): existence of the terminal limit and absolute continuity or equivalence of the sample law with the data law | — | not formalised; the library's samplers stop at $`t_1 \gt 0`$, and `DiffusionMemorization.empirical_not_ac` records that the empirical measure has no Lebesgue density | Not formalised |
| Thm 2: Girsanov change of measure for a perturbed drift | error accumulation | not formalised; there is no Girsanov theorem in the library. Its discrete analogue is the KL chain rule with Gaussian steps (GI-1, DF-1), which bounds KL and does not give equivalence of laws | Not formalised |
| Cor. 1: memorisation of the training set | error accumulation, exact computation | DF-2: `DiffusionMemorization.output_concentrates_on_training_set`, `DiffusionMemorization.output_outside_nhds_le`, `DiffusionMemorization.tendsto_output_outside_nhds`, `DiffusionMemorization.fwdLaw_one_outside_le`, `DiffusionDiscretization.exists_tvSup_output_le` | Related statement (Verified, DF-2): for the discretised DDPM with the exact empirical score (zero score error) and early stopping, for every $`\rho, \varepsilon \gt 0`$ some parameters give output mass $`\ge 1 - \varepsilon`$ within distance $`\rho`$ of the training points; exact support equality and nonzero score errors are not formalised |

### Li–Chen–Li (2024)

Sixu Li, Shi Chen, Qin Li. A Good Score Does not Lead to A Good Generative Model.
[arXiv:2401.04856](https://arxiv.org/abs/2401.04856) (v1 January 2024, v2 January 2024).

**Algorithm.** Continuous-time reverse SDE (DDPM) with the empirical optimal score $`s^N`$, which is
the exact score of the noised empirical measure, started at $`\mathcal{N}(0, I)`$ and stopped at
$`T - \delta`$. Library counterpart: the discretised DDPM with the exact score of
`DiffusionMemorization.empirical x`, `DiffusionMemorization.exactScoreOutput`, stopped at $`t_1`$.

**Main result.** Thm 2.3 (a modified form of Benton et al., Thm 1, with the discretisation error
omitted):
```math
\mathrm{TV}(\bar{q}_{T-\delta}, p_\delta) \lesssim \varepsilon_{\mathrm{score}} + \sqrt{d} \,
e^{-T}.
```
Thm 3.1: with $`N \ge N(\varepsilon_{\mathrm{score}}, \delta, \tau)`$ samples the empirical optimal
score is within $`\varepsilon_{\mathrm{score}}`$ of the true score in $`L^2(dt, p_t \, dx)`$ with
probability at least $`1 - \tau`$ (Gaussian or bounded-support data). Props. 4.1–4.2 and Thm 4.3:
with the empirical optimal score the sampler returns, with early stopping, a law within
$`\varepsilon`$ in TV of a Gaussian kernel density estimate of the training set, and without early
stopping ($`T \to \infty`$, $`\delta = 0`$) the empirical measure itself.

| Step | Move | Library | Status |
|---|---|---|---|
| Thm 2.3: end-to-end TV bound for DDPM under an $`L^2`$ score error | error accumulation | DF-1: `DiffusionDiscretization.klDiv_output_le_ddpm_grid_explicit`, `DiffusionDiscretization.tvSup_output_le_ddpm_grid`, `DiffusionDiscretization.tvSup_output_le_geomGrid` | Related discrete-time statement (Verified, DF-1): KL and TV bounds for the discretised DDPM with the discretisation term kept, for every data law with finite second moment |
| Closed-form empirical optimal score (Eq. (12), Prop. B.2) as the exact score of the noised empirical measure | score | SE-3 `Tweedie.tweedie_pi`, `Diffusion.postMean_ae_eq_tweedie` (Tweedie for every data law, the empirical measure included); DF-2 uses `DiffusionDiscretization.exactScore` of `DiffusionMemorization.empirical` | Verified as a representation (SE-3, DF-1); minimisation of the score-matching objective and the explicit weighted-average formula are not formalised |
| Thm 3.1: sample complexity of the empirical optimal score (Markov inequality and the mean-error estimate of Lemma C.2) | score | not formalised. SE-4 (`MonteCarlo.integral_sq_scoreEstimate_sub`, `MonteCarlo.meas_abs_scoreEstimate_sub_ge_le`) treats a different estimator: a plain Monte Carlo average of exact posterior draws (mean-square error variance$`/n`$, Chebyshev tail), with the score form in one dimension | Not formalised (SE-4, Verified, concerns a different estimator) |
| Prop. 4.1: the forward process from the empirical measure is a Gaussian mixture centred at the scaled training points, close to a Gaussian kernel density estimate | exact computation | inside DF-2: `DiffusionMemorization.fwdLaw_one_outside_le` (Markov tail of the noised empirical law $`p_1`$, a mixture of $`\mathcal{N}(\alpha_1 x_i, \beta_1 I)`$, away from the training points) | Verified for the tail bound used in DF-2; the TV comparison with the unscaled kernel density estimate $`p_*^\gamma`$ is not formalised |
| Prop. 4.2 and Thm 4.3 with early stopping: the sampler with the empirical optimal score outputs the noised empirical law up to a small TV error (data processing, triangle inequality) | error accumulation | `DiffusionDiscretization.exists_tvSup_output_le` applied to the empirical measure (DF-1 with zero score error; finite second moment by `DiffusionMemorization.integrable_sqNorm_empirical`); DF-2 `DiffusionMemorization.exists_output_near_training_set`, `DiffusionMemorization.output_concentrates_on_training_set` | Related statement (Verified, DF-1, DF-2): for the discretised sampler, $`\mathrm{TV}(p_1, q_1) \le \varepsilon`$ for a suitable grid and horizon (discretisation included), and the consequence that output mass $`\ge 1 - \varepsilon`$ lies within $`\rho`$ of the training set; a TV rate to the kernel density estimate in terms of $`\delta`$ is not stated |
| Thm 4.3 without early stopping: the limit law is the empirical measure | error accumulation | DF-2 limit form `DiffusionMemorization.tendsto_output_outside_nhds` (mass outside any neighbourhood of the training points tends to 0 along a sequence of parameters) | Related statement (Verified, DF-2): concentration along a parameter sequence, not identification of the limit law with the empirical measure (the weights $`1/n`$ are not stated) |

### Gu et al. (2023)

Xiangming Gu, Chao Du, Tianyu Pang, Chongxuan Li, Min Lin, Ye Wang. On Memorization in Diffusion
Models. Transactions on Machine Learning Research (TMLR), 2025.
[arXiv:2310.02664](https://arxiv.org/abs/2310.02664) (v1 October 2023, v2 February 2025).

**Algorithm.** Denoising score matching on a training set; its minimiser $`s^*`$ (Eq. (2)) is the
score of the noised empirical measure; sampling by the reverse SDE or by the Euler discretisation of
the probability-flow ODE (App. A.2). Library counterpart: the exact score `exactScore (empirical x)`
used in the discretised DDPM `DiffusionMemorization.exactScoreOutput` (stochastic sampler only).

**Main result.** Eq. (2) and App. A.1: closed-form minimiser of the empirical denoising
score-matching objective, a softmax-weighted average of $`(\alpha_t x_n - z_t)/\sigma_t^2`$. App.
A.2: with this score, the final Euler probability-flow step returns a convex combination of training
points, which tends to the nearest training point as the stopping time tends to 0, so the optimal
model reproduces training data. Def. 2.1: effective model memorisation (EMM). The main body is an
empirical study of how data distribution, model configuration and training procedure affect EMM,
including that conditioning on uninformative random labels can trigger memorisation.

| Step | Move | Library | Status |
|---|---|---|---|
| Closed-form optimum of the empirical denoising score-matching objective (pointwise convex minimisation, App. A.1) | score | SE-3: `Tweedie.tweedie_pi` and `Diffusion.postMean_ae_eq_tweedie` express the score of a noised law through the posterior mean for every prior, the empirical measure included; `Tweedie.tweedie_noise_condExp` identifies the score as the conditional expectation of the noise target (1D); CE-02 `Counterexamples.ScoreNotNoise.not_noiseTarget_ae_eq_scoreOfNoisy` shows the noise target itself is not the score | Tweedie representation Verified (SE-3); that the score-matching objective is minimised by this conditional expectation, and the explicit softmax formula, are not formalised |
| App. A.2: the last Euler probability-flow step with the optimal score is the posterior mean, a convex combination of training points, with a nearest-neighbour limit | score | Tweedie for the reverse-step mean, `Diffusion.postMean_ae_eq_tweedie`; deterministic samplers (`DiffusionODESeparation.detMean`) are not analysed with the empirical score | Not formalised for deterministic samplers; the library's samplers stop at $`t_1`$, without a final denoising step |
| Memorisation: the optimal score reproduces the training data | error accumulation, exact computation | DF-2: `DiffusionMemorization.output_concentrates_on_training_set`, `DiffusionMemorization.tendsto_output_outside_nhds` | Related statement (Verified, DF-2) for the stochastic DDPM sampler with the exact empirical score: output mass $`\ge 1 - \varepsilon`$ within $`\rho`$ of the training set for suitable early stopping and grid; the paper's derivation uses the deterministic Euler sampler |
| Effective model memorisation (Def. 2.1) and the empirical study | — | not formalised | Not formalised |

## Proximal sampler

### Lee–Shen–Tian (2021)

Yin Tat Lee, Ruoqi Shen, Kevin Tian. Structured logconcave sampling with a restricted Gaussian
oracle. Proceedings of the 34th Conference on Learning Theory (COLT 2021), PMLR 134, pp. 2993–3050.
[arXiv:2010.03106](https://arxiv.org/abs/2010.03106) (v4, 22 Oct 2021).

**Algorithm.** Alternating sampler (Algorithm 1, AlternateSample) on the augmented law
$`\hat\pi(x, y) \propto e^{-f(x) - \Vert x - y \Vert^2/(2\eta)}`$: forward step
$`y \sim \mathcal{N}(x, \eta I)`$, then backward step $`x' \sim \mathrm{RGO}(y)`$ with density
$`\propto e^{-f(x) - \Vert x - y \Vert^2/(2\eta)}`$ (restricted Gaussian oracle, Definition 1). In
the library: `Proximal.proxKernel` (1D), `ProximalPi.proxKernelPi` (`Fin d → ℝ`, Euclidean distance)
and `EuclideanTransfer.proxKernelEuclid`, each the composition of the Gaussian forward kernel
(`Proximal.forwardKernel`, $`\eta`$ is the variance) and the RGO kernel (`Proximal.rgoKernel`,
`ProximalPi.rgoKernelPi`); target $`\pi \propto e^{-f}`$ (Mathlib's `volume.tilted (-f)`); iterates
$`\rho_{k+1} = P_{\mathrm{prox}} \rho_k`$; the RGO is sampled exactly.

**Main result.** Theorem 1 (proximal reduction framework): for $`\mu`$-strongly convex $`f`$,
$`\eta \le 1/\mu`$ and an $`\eta`$-RGO, Algorithm 1 started at the minimiser reaches total-variation
distance $`\varepsilon`$ after $`T = O((\eta\mu)^{-1} \log(d/(\eta\mu\varepsilon)))`$ iterations.
The proof (Section 3) combines Lemma 1 (alternating marginal sampling leaves $`\hat\pi`$ invariant
and is reversible), Lemma 2 ($`W_2^2(\pi_{k+1}, \pi) \le W_2^2(\pi_k, \pi)/(1 + \eta\mu)^2`$, via
Talagrand's inequality and the LSI of the RGO), Lemma 3 (KL between mixtures is at most the averaged
KL), Lemma 4 ($`W_2(\pi_k, \pi) \le \Delta`$ gives
$`\mathrm{KL}(\pi_{k+1} \Vert \pi) \le \Delta^2/(2\eta)`$) and Pinsker's inequality. Theorems 2–3
and Corollaries 1–5 instantiate the framework for composite, finite-sum and well-conditioned
densities with concrete RGO implementations.

| Step | Move | Library | Status |
|---|---|---|---|
| Augmented law, Gaussian forward step and RGO (Definition 1, Algorithm 1) | setting | PX-1: `Proximal.forwardKernel`, `Proximal.rgoKernel`, `Proximal.proxKernel`, `Proximal.augmentedJoint`, `ProximalPi.rgoKernelPi`, `ProximalPi.proxKernelPi`; Markov property from $`\int e^{-f} \lt \infty`$ alone: `Proximal.isMarkovKernel_rgoKernel` | Verified (PX-1); 1D, `Fin d → ℝ` and `EuclideanSpace ℝ (Fin d)`; any measurable $`f`$ with $`\int e^{-f} \lt \infty`$, no convexity |
| Lemma 1: alternating marginal sampling leaves the target invariant (and is reversible) | identification | PX-1, KR-2: `Proximal.reverseDensity_eq_rgoDensity`, `Proximal.isReverseKernel_rgoKernel`, `Proximal.augmentedJoint_map_swap`, `Proximal.proxKernel_comp_target`, `ProximalPi.isReverseKernel_rgoKernelPi`, `ProximalPi.proxKernelPi_comp_targetPi`, `EuclideanTransfer.proxKernelEuclid_comp_tilted`, `ReverseKernel.isReverseKernel_posterior` | Verified for invariance (PX-1, KR-2): the RGO is the Bayes reverse kernel of the forward step at every point; reversibility of the x-chain is not formalised |
| Lemma 2: $`W_2`$ contraction by $`(1 + \eta\mu)^{-1}`$ for $`\mu`$-strongly convex $`f`$ (Talagrand inequality and LSI of the RGO) | contraction | PX-5 (case $`\mu = 0`$): `ProximalLogConcave.exists_coupling_proxKernel` (1D, quantile coupling, every monotone cost), `ProximalLogConcavePi.exists_coupling_proxKernelPi_separable` (separable potentials), `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn` (every finite convex $`f`$ on `Fin d → ℝ`: the RGO maps a coupling to one whose squared-distance cost is not larger) | Related statement: non-expansiveness of coupling costs for convex $`f`$ ($`\mu = 0`$), Verified (PX-5); the factor $`(1 + \eta\mu)^{-1}`$ for $`\mu \gt 0`$ and Talagrand's inequality are not formalised |
| Lemma 3: KL between mixtures is at most the averaged KL | comparison | KL-2: `KL.klDiv_comp_le_compProd`, `KL.klDiv_compProd_eq_add_lintegral`; coupled-kernel form `ProximalRegularization.klDiv_comp_map_le_lintegral` | Verified (KL-2); Markov kernels on countably generated spaces |
| Lemma 4: one proximal step turns $`W_2(\pi_k, \pi) \le \Delta`$ into $`\mathrm{KL}(\pi_{k+1} \Vert \pi) \le \Delta^2/(2\eta)`$ | contraction | PX-2 (coupling form): `ProximalRegularization.klDiv_proxKernel_comp_le_coupling` (1D), `ProximalRegularization.klDiv_proxKernelPi_comp_le_coupling` (`Fin d → ℝ`); Gaussian KL (KL-3) `GaussianIncrement.klDiv_gaussianReal_gaussianReal`, `GaussianIncrement.klDiv_pi_gaussianReal`; RGO step by data processing `ProximalContraction.klDiv_proxKernel_comp_le_forward` | No named hypothesis (listed under PX-2, which is Conditional overall): $`\mathrm{KL}(\rho P_{\mathrm{prox}} \Vert \pi) \le \int \Vert x - y \Vert^2/(2\eta) \, d\gamma`$ for every coupling $`\gamma`$ of $`(\rho, \pi)`$ and every measurable $`f`$ with $`\int e^{-f} \lt \infty`$, proved from the Gaussian KL of the forward step and data processing through the RGO; the infimum over couplings is not formed |
| Proof of Theorem 1: Lemmas 2 and 4, then Pinsker, from the minimiser | comparison, contraction | KL-1: `Pinsker.tvSup_le_sqrt_klDiv`; PX-6: `ProximalStronglyLogConcaveGeneralPi.tvSupPi_iterate_le_sq_of_stronglyLogConcave`; PX-5 for point-mass starts: `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn` | Pinsker Verified (KL-1). The end-to-end statement of Theorem 1 (start at the minimiser, $`W_2^2(\delta_{x^\star}, \pi) \le d/\mu`$, iteration count) is not formalised; PX-6 (Verified) gives TV through the KL rate $`(1 + \mu\eta)^{-2k}`$ from starts with finite KL, and PX-5 (Verified) covers point-mass starts with a $`1/k`$ rate |
| Inexact RGO (robustness remark after Theorem 1) | error accumulation | KR-1: `ErrorDecomposition.tvSup_le_three_chain`; proximal instance `ErrorDecomposition.tvSup_inexactProx_le_along` (1D) | KR-1 Verified; the proximal instance is Conditional on a TV contraction along the algorithm's laws (hypothesis `hAlong`), which holds with factor 1, in which case the per-step RGO errors add up |
| RGO implementations and applications (Theorems 2–3, Corollaries 1–5) | — | not formalised | Not formalised |

### Chen–Chewi–Salim–Wibisono (2022)

Yongxin Chen, Sinho Chewi, Adil Salim, Andre Wibisono. Improved analysis for a proximal algorithm
for sampling. Proceedings of the 35th Conference on Learning Theory (COLT 2022), PMLR 178, pp.
2984–3014. [arXiv:2202.06386](https://arxiv.org/abs/2202.06386).

**Algorithm.** The proximal sampler of Lee–Shen–Tian: forward step $`y \sim \mathcal{N}(x, \eta I)`$
(heat flow for time $`\eta`$), then the RGO; analysed along the forward heat flow and a backward
heat flow whose endpoint kernel is the RGO (Doob $`h`$-transform channels $`Q^-_t`$). Library:
`Proximal.proxKernel`, `ProximalPi.proxKernelPi`, `EuclideanTransfer.proxKernelEuclid`; the backward
flow is realised by explicit posterior kernels `ProximalSharpLSI.bwdKernel` (Bayes posteriors of
Gaussian channels), with no SDE.

**Main result.** Theorem 1 (from Lee–Shen–Tian, Lemma 2):
$`W_2(\rho_k, \bar\rho_k) \le W_2(\rho_0, \bar\rho_0)/(1 + \alpha\eta)^k`$ for $`\alpha`$-strongly
log-concave targets. Theorem 2: for log-concave targets,
$`\mathrm{KL}(\rho_k \Vert \pi) \le W_2^2(\rho_0, \pi)/(k\eta)`$. Theorem 3: under $`\alpha`$-LSI,
$`\mathrm{KL}(\rho_k \Vert \pi) \le \mathrm{KL}(\rho_0 \Vert \pi)/(1 + \alpha\eta)^{2k}`$ and
$`R_q(\rho_k \Vert \pi) \le R_q(\rho_0 \Vert \pi)/(1 + \alpha\eta)^{2k/q}`$. Theorems 4–5:
$`\chi^2`$ and Rényi rates under Poincaré and Latała–Oleszkiewicz inequalities. Corollaries 6–8:
complexity bounds with a rejection-sampling RGO. Theorems 9–11: relations with the proximal point
method. Section 4.4: closed-form Gaussian iterates, showing that the factor
$`(1 + \alpha\eta)^{-2}`$ of Theorem 3 is sharp. Proof ingredients (Appendix A): Lemma 12 (de Bruijn
identity along the simultaneous heat flow), Lemma 15 (its backward version via the Doob
$`h`$-transform), strategy of Section A.1.4.

| Step | Move | Library | Status |
|---|---|---|---|
| Lemma 12 (forward step): $`\partial_t \mathrm{KL}(\rho Q_t \Vert \pi Q_t) = -\tfrac12 J(\rho Q_t \Vert \pi Q_t)`$ | differentiation | PX-2, KL-5: `HeatFlowDeBruijn.hasDerivAt_heatKL`, `HeatFlowDeBruijnPi.hasDerivAt_heatKL`; regularity for warm starts `HeatFlowRegularityWarm.heatFlowRegular_of_warm`, `HeatFlowRegularityWarmPi.heatFlowRegularPi_of_warm` | Holds for KL under the explicit regularity hypothesis `HeatFlowRegular` (integrability, domination, vanishing boundary flux, $`t \gt 0`$), which is proved for warm starts when $`\pi`$ has a finite second moment (used in KL-5 and PX-2); general $`\varphi`$-divergences and Rényi divergences not formalised |
| LSI of $`\pi * \mathcal{N}(0, tI)`$ with constant $`1/\alpha + t`$ | contraction | KL-6: `GaussianFunctionalLSI.functionalLSI_heatKernel_comp_of_targetLSI`, `LogSobolevTensorPi.functionalLSIPi_heatKernelPi_comp`, from `LogSobolev.functionalLSI_map_add`, `LogSobolevTensorPi.functionalLSIPi_map_add` and Gross's inequality `GaussianFunctionalLSI.functionalLSI_gaussianReal`, `GaussianFunctionalLSIPi.functionalLSIPi_gaussian`; KL/Fisher form `LogSobolevExtension.heatKL_le_of_functionalLSI_of_integrable` | Verified (KL-6); functional LSI on the test class `LSIClass` (extended to positive $`C^1`$ functions with integrability); the KL/Fisher form needs integrable KL and Fisher integrands at time $`t`$ |
| Forward-step contraction $`\mathrm{KL}(\rho Q_\eta \Vert \pi Q_\eta) \le \mathrm{KL}(\rho \Vert \pi)/(1 + \alpha\eta)`$ (Grönwall) | contraction, differentiation | PX-2: `ProximalContraction.le_div_of_hasDerivWithinAt_le`, `HeatFlowDeBruijn.heatKL_le_div_of_regular`, `HeatFlowDeBruijn.toReal_klDiv_forwardKernel_le_of_regular`, `ProximalSharpLSIPi.toReal_klDiv_forwardKernelPi_le_of_targetLSIPi` | Conditional (PX-2) on the LSI of $`\pi`$ and `HeatFlowRegular`; the LSI is used only at times $`t \in (0, \eta)`$ |
| Lemma 15 and backward step: RGO as endpoint of a backward heat flow, de Bruijn along it, LSI of $`\pi * \mathcal{N}(0, (\eta - t)I)`$, contraction by $`(1 + \alpha\eta)^{-1}`$ | contraction, differentiation | PX-2: `ProximalSharpLSI.klDiv_rgoKernel_comp_le_bwd`, `ProximalSharpLSI.klDiv_bwd_le`; backward de Bruijn `BackwardHeatFlow.hasDerivAt_integral_bklIntegrand`, `BackwardHeatFlowPi.hasDerivAt_integral_bklIntegrandPi`; LSI bridge `BackwardHeatFlow.integral_mul_log_le_of_functionalLSI`; interior Grönwall `BackwardHeatFlow.le_div_of_hasDerivAt_interior`; result `ProximalSharpLSI.toReal_klDiv_rgoKernel_comp_le_of_targetLSI`, `ProximalSharpLSIPi.toReal_klDiv_rgoKernelPi_comp_le_of_targetLSIPi`; regularity `ProximalSharpPerturbed.backwardHeatFlowRegular_of_warm`, `ProximalSharpPerturbedPi.backwardHeatFlowRegularPi_of_warm` | Conditional (PX-2) on the LSI of $`\pi`$ and the explicit regularity `BackwardHeatFlowRegular`, which is proved for warm inputs and targets with a Gaussian upper envelope; the backward flow is built from posterior kernels (no SDE, no Doob $`h`$-transform) and its endpoints are controlled by data processing |
| Theorem 3, KL part: composition of the two steps, iteration, every start with finite KL, TV by Pinsker | contraction, comparison | PX-2 final form: `ProximalGeneralLSI.toReal_klDiv_iterate_le_sq_general`, `ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general`, `ProximalGeneralLSIPi.tvSupPi_iterate_le_sq_general`; warm-start removal (KL-2) `KLWarmApprox.klDiv_comp_le_of_warm`, `KLWarmApprox.klDiv_iterate_le_of_forall` | Conditional (PX-2) on the LSI of $`\pi`$; the library states a Gaussian upper envelope $`\pi \le C \cdot \mathcal{N}(0, vI)`$ explicitly as a hypothesis of this general form; no other hypotheses, every $`\rho_0`$ with finite KL, 1D and `Fin d → ℝ` |
| Theorem 3 for targets whose LSI is proved | contraction | PX-6: `ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave`, `EuclideanTransfer.toReal_klDiv_iterateEuclid_le_sq_of_stronglyLogConcave` (Bakry–Émery); PX-4: `ProximalSharpPerturbedPi.toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top` (Holley–Stroock); PX-3: `ProximalGaussianUnconditional.toReal_klDiv_iteratePi_le_sq_of_ne_top` | Verified (PX-6, PX-4, PX-3), no named hypotheses: strongly log-concave targets; $`\pi \propto e^{-\alpha \Vert x \Vert^2/2 - W}`$ with $`a \le W \le b`$ at rate $`(1 + \alpha e^{-(b-a)}\eta)^{-2k}`$; isotropic Gaussians |
| Theorem 3, Rényi bound (4); Theorems 4–5 (Poincaré, Latała–Oleszkiewicz) | contraction | not formalised | Not formalised (only KL is treated) |
| Theorem 2: $`\mathrm{KL}(\rho_k \Vert \pi) \le W_2^2(\rho_0, \pi)/(k\eta)`$ for log-concave targets | contraction | PX-5: `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn` (`Fin d → ℝ`), `ProximalLogConcaveRate.klDiv_iterate_le_div'` (1D) | Verified (PX-5); proves a version for every finite convex $`f`$ with $`\int e^{-f} \lt \infty`$ and every coupling $`\gamma_0`$ of $`(\rho_0, \pi)`$ (the infimum over couplings is not formed), via shifted composition (Altschuler–Chewi) rather than the argument of Appendix A.3 |
| Appendix A.3 ingredients of Theorem 2: KL along Wasserstein geodesics (inequality (27)), $`W_2`$ monotone along the forward and backward heat flows | differentiation | not formalised (no EVI or displacement-convexity inequality; the library's route to Theorem 2 does not use them) | Not formalised |
| Theorem 1: $`W_2`$ contraction by $`(1 + \alpha\eta)^{-1}`$ per step | contraction | PX-5: `ProximalLogConcave.exists_coupling_proxKernel`, `ProximalLogConcavePi.exists_coupling_proxKernelPi_separable`, `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn` | Related statement: the case $`\alpha = 0`$ (coupling costs do not increase), Verified (PX-5); the factor for $`\alpha \gt 0`$ and the Wasserstein subdifferential argument of Appendix A.2 are not formalised |
| Section 4.4: Gaussian iterates and sharpness of $`(1 + \alpha\eta)^{-2}`$ | exact computation | EX-3, PX-3: `ProximalSharp.rgoKernel_gaussPotential_apply`, `ProximalSharp.proxKernel_comp_gaussianReal_invVar`, `ProximalSharp.klDiv_proxKernel_comp_gaussTarget`, `ProximalSharp.not_exists_rate_lt`, `ProximalSharpPi.klDiv_proxKernelPi_comp_gaussTarget`, `ProximalSharpPi.not_exists_rate_lt_pi` | Verified (EX-3); a related instance: for $`\pi = \mathcal{N}(0, \alpha^{-1} I)`$ and starts $`\mathcal{N}(m, \alpha^{-1} I)`$ one step divides KL by exactly $`(1 + \alpha\eta)^2`$, so no smaller factor holds; the general covariance recursion of Section 4.4 and its variance example are not formalised |
| Corollaries 6–8 and Theorems 9–11 (rejection-sampling RGO, complexity, proximal point limits) | — | not formalised | Not formalised |

### Altschuler–Chewi (2023)

Jason M. Altschuler, Sinho Chewi. Shifted composition I: Harnack and reverse transport inequalities.
[arXiv:2311.14520](https://arxiv.org/abs/2311.14520) (24 Nov 2023); IEEE Transactions on Information
Theory 71(1), 2025.

**Algorithm.** Shifted composition for a Markov kernel $`P`$ on $`\mathbb{R}^d`$: two chains coupled
synchronously, the second moved towards the first by a fraction $`\eta_n`$ of their distance at each
step. In the library $`P = K \circ \mathcal{N}_\eta`$ (Gaussian convolution of variance $`\eta`$
followed by a kernel $`K`$), the shift is applied to the mean of the Gaussian noise, and $`K`$ is
CDF-shift-monotone on $`\mathbb{R}`$ or has a weak contractive coupling
(`RGOCouplingWeak.HasWeakCoupling`) on `Fin d → ℝ`; instantiated with $`K`$ the RGO of a convex
potential, so $`P`$ is the proximal kernel.

**Main result.** Theorem 3.1 (shifted composition rule):
```math
\mathrm{KL}(\mu^Y \Vert \nu^Y) \le \mathrm{KL}(\mu^{X'} \Vert \nu^X) + \inf_\gamma \int
\mathrm{KL}(\mu^{Y \mid X = x} \Vert \nu^{Y \mid X = x'}) \, \gamma(dx, dx')
```
over couplings $`\gamma`$ of $`(\mu^X, \mu^{X'})`$, and a Rényi analogue. Theorem 3.2: if
$`R_q(\delta_x P \Vert \delta_y P) \le c \Vert x - y \Vert^2`$ and $`P`$ is $`W_\infty`$-Lipschitz
with constant $`L`$ ($`W_2`$ suffices for KL, Remark 3.4), then
```math
R_q(\delta_x P^N \Vert \delta_y P^N) \le c \, \frac{L^{-2} - 1}{L^{-2N} - 1} \Vert x - y \Vert^2
```
(for $`L = 1`$ the factor is $`c/N`$). Lemma 3.6 (convexity principle) and Theorem 3.7 pass to
arbitrary initial laws through couplings. Further results: Langevin regularity (Theorem 3.10,
Corollary 3.11), continuous-time couplings (Section 4), Harnack and reverse Harnack inequalities
(Section 6).

| Step | Move | Library | Status |
|---|---|---|---|
| One shifted step: shifting the Gaussian noise of the second chain costs $`t^2 \Vert x - y \Vert^2/(2\eta)`$ in KL (use of the shifted chain rule, Theorem 3.1(1)) | comparison, contraction | PX-5: `ProximalLogConcaveRate.exists_shifted_step` (1D), `RGOCouplingWeak.exists_shifted_step_weak` (`Fin d → ℝ`); shifted-noise KL `ProximalLogConcaveRate.klDiv_noiseKernel`, `ProximalLogConcaveRateGeneralPi.klDiv_gaussNoise`; KL-2 `KL.klDiv_compProd_eq_add_lintegral`, `KL.klDiv_comp_le_compProd` | Verified (PX-5, KL-2); component of Theorem 3.1(1): the one-step bound is proved for this Gaussian-shift construction from the KL chain rule and data processing; the general rule (arbitrary $`X, X', Y`$, infimum over couplings) and its Rényi part are not stated |
| Assumption (a): one-step regularity with $`c = 1/(2\eta)`$ | comparison | KL-3: `GaussianIncrement.klDiv_gaussianReal_gaussianReal`, `GaussianIncrement.klDiv_pi_gaussianReal`; PX-2: `ProximalRegularization.klDiv_forwardKernelPi_comp_map_le` | Verified (KL-3); the PX-2 coupling bound has no named hypotheses |
| Assumption (b): Lipschitz constant $`L = 1`$ for the kernel applied after the noise | contraction, identification | PX-5: 1D pathwise `ProximalLogConcave.cdfShiftMonotone_rgoKernel`, `ProximalLogConcaveRate.abs_qf_sub_le_all`; `Fin d → ℝ`: `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn`, built from `RGOCouplingLangevin.sqDist_step_le`, `RGOCouplingLangevin.weakTendsto_emCurve_rgoKernelPi` (Fokker–Planck uniqueness, FL-6), `RGOCouplingWeak.exists_smoothConvexBdd_tendsto_rgoKernelPi`, `RGOCouplingWeak.hasWeakCoupling_of_tendsto`, `KLLowerSemicontinuity.klDiv_le_liminf_of_tendsto_integral₂` | Verified (PX-5): a squared-distance ($`W_2`$-type) non-expansive coupling of the RGO of every finite convex $`f`$, via synchronous Euler–Maruyama chains of the Langevin dynamics, smooth approximation and compactness (no SDE theory); $`L \ne 1`$ and $`W_\infty`$ couplings not formalised |
| Theorem 3.2 for KL with $`L = 1`$ (shifts $`1/(k+1), 1/k, \ldots, 1`$) | contraction | PX-5: `ProximalLogConcaveRate.klDiv_iterate_le_shifted` (1D), `RGOCouplingWeak.klDiv_iterate_le_shifted_of_weak` (`Fin d → ℝ`) | Verified (PX-5); proves a version of Theorem 3.2 for KL with $`L = 1`$: $`\mathrm{KL}(P^{k+1}\Lambda_1 \Vert P^{k+1}\Gamma_2) \le \mathrm{KL}(\Lambda \Vert \Gamma) + \int \Vert x - y \Vert^2 \, d\Lambda/(2(k+1)\eta)`$ for any probability laws $`\Lambda, \Gamma`$ on the product space, for kernels $`P = K \circ \mathcal{N}_\eta`$; Rényi divergences, $`L \ne 1`$ and general kernels not formalised |
| Convexity principle (Lemma 3.6, Theorem 3.7(1)) for KL | comparison | `ProximalRegularization.klDiv_comp_map_le_lintegral`; in the multi-step bound arbitrary initial laws enter through $`\mathrm{KL}(\Lambda \Vert \Gamma)`$ | No named hypothesis (listed under PX-2, Conditional overall), for KL and each coupling (the infimum is not formed); Rényi part not formalised |
| Application to the proximal sampler with second law $`\pi`$ | contraction | PX-5: `RGOCouplingWeak.klDiv_iteratePi_le_div_of_hasWeakCoupling`, `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn`, `ProximalLogConcaveRate.klDiv_iterate_le_div` | Verified (PX-5): $`\mathrm{KL}(\rho_{k+1} \Vert \pi) \le \int \Vert x - y \Vert^2 \, d\gamma_0/(2(k+1)\eta)`$ for every finite convex $`f`$ with $`\int e^{-f} \lt \infty`$, obtained by combining the argument of Theorem 3.2 with the RGO couplings above |
| Refined Rényi bounds, Langevin regularity (Theorems 3.9–3.14), continuous-time couplings (Section 4), Harnack and reverse Harnack inequalities (Section 6) | — | not formalised | Not formalised |

### Pedrotti (2026)

Francesco Pedrotti. Entropy-Wasserstein regularization, defective local concentration and a cutoff
criterion beyond non-negative curvature. [arXiv:2601.13259](https://arxiv.org/abs/2601.13259) (v1 19
Jan 2026, v3 19 Jul 2026).

**Algorithm.** Proximal Sampler $`P^{\mathrm{PS}}_h`$ (forward step $`\mathcal{N}(x, hI)`$, $`h`$
the variance, then the backward RGO step) for $`\pi \propto e^{-U}`$, $`U = V + H`$ with
$`V, H \in C^2`$, $`\nabla^2 V \succeq \alpha I`$, $`\Vert \nabla H \Vert \le L`$ (Assumption 1.3);
also Langevin dynamics and LMC. Library: `ProximalPi.proxKernelPi` with $`\eta = h`$, for $`U = f`$
finite and convex ($`\alpha = 0`$, $`L = 0`$).

**Main result.** Theorem 2.4: propagation of a defective transport-entropy inequality under the weak
curvature condition $`W_p(\delta_x P, \delta_y P) \le K d(x, y) + M`$ (Assumption 1.1). Theorem 3.2
(entropy-Wasserstein regularization): under Assumption 1.1 with $`p = 2`$ and
$`\mathrm{KL}(\delta_x P \Vert \delta_y P) \le C \Vert x - y \Vert^2`$ (Assumption 3.1), for
$`K = 1`$, $`M = 0`$ the bound is $`\mathrm{KL}(\mu P^N \Vert \nu P^N) \le C \, W_2^2(\mu, \nu)/N`$,
with explicit bounds for $`M \gt 0`$ and $`K \lt 1`$. Corollary 2.7 (Proximal Sampler under
Assumption 1.3) propagates the defective transport-entropy inequality $`T_2H`$ along the chain.
Corollary 3.5 (same setting): for $`\alpha = 0`$,
$`\mathrm{KL}(\mu P^N \Vert \nu P^N) \le (W_2(\mu, \nu) + 2LNh)^2/(2Nh)`$ for all
$`\mu, \nu \in \mathcal{P}_2`$, and an explicit bound for $`\alpha \gt 0`$. Section 4: mixing-window
bounds for Langevin and the Proximal Sampler (Theorem 4.3 for Langevin, Theorem 4.6 for the Proximal
Sampler) and Example 4.5 (cutoff beyond log-concavity).

| Step | Move | Library | Status |
|---|---|---|---|
| Assumption 3.1 for the proximal kernel: $`\mathrm{KL}(\delta_x P \Vert \delta_y P) \le \Vert x - y \Vert^2/(2h)`$ (Gaussian KL and data processing) | comparison | KL-3: `GaussianIncrement.klDiv_pi_gaussianReal`; PX-2: `ProximalRegularization.klDiv_forwardKernelPi_comp_map_le` (any two laws, forward step), `ProximalRegularization.klDiv_proxKernelPi_comp_le_coupling` (second law $`\pi`$) | Verified (KL-3); the coupling forms have no named hypothesis (listed under PX-2), for every measurable $`f`$ with $`\int e^{-f} \lt \infty`$; the RGO step enters through data processing |
| Lemma 1.5(2): $`W_2(\mu P, \nu P) \le W_2(\mu, \nu)/(1 + \alpha h) + 2Lh/(1 + \alpha h)`$ | contraction | PX-5: `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn`, `ProximalLogConcave.exists_coupling_proxKernel` (1D) | Related statement: the case $`\alpha = 0`$, $`L = 0`$ (a coupling with squared-distance cost and KL between coupled pairs not increased) is Verified (PX-5); $`\alpha \gt 0`$ and $`L \gt 0`$ are not formalised |
| Theorem 3.2 with $`K = 1`$, $`M = 0`$ (shifted composition along the chain) | contraction | PX-5: `RGOCouplingWeak.klDiv_iterate_le_shifted_of_weak`, `ProximalLogConcaveRate.klDiv_iterate_le_shifted` | Verified (PX-5) for $`K = 1`$, $`M = 0`$ and kernels of the form Gaussian convolution followed by a kernel with a weak contractive coupling; $`M \gt 0`$ and $`K \lt 1`$ not formalised |
| Corollary 3.5 with $`\alpha = 0`$, $`L = 0`$: $`\mathrm{KL}(\mu P^N \Vert \nu P^N) \le W_2^2(\mu, \nu)/(2Nh)`$ | contraction | PX-5: `ProximalLogConcaveRateConvexPi.klDiv_iteratePi_le_div_of_convexOn`; two-law ingredients `RGOCouplingWeak.klDiv_iterate_le_shifted_of_weak`, `ProximalLogConcaveRateConvexPi.hasWeakCoupling_rgoKernelPi_of_convexOn` | Verified (PX-5), special case $`\nu = \pi`$: every finite convex $`f`$ with $`\int e^{-f} \lt \infty`$, every coupling of $`(\rho_0, \pi)`$, any initial law; the form with two arbitrary initial laws follows from the two listed ingredients but is not stated as a separate theorem |
| Corollary 3.5 for $`L \gt 0`$ or $`\alpha \gt 0`$; Theorem 2.4 and Corollary 2.7 (defective transport-entropy inequalities); Section 4 (mixing windows, cutoff) | — | not formalised | Not formalised |

### Mitra–Wibisono (2025)

Siddharth Mitra, Andre Wibisono. Fast convergence of Φ-divergence along the unadjusted Langevin
algorithm and proximal sampler. Algorithmic Learning Theory (ALT) 2025.
[arXiv:2410.10699](https://arxiv.org/abs/2410.10699) (v2, 12 Feb 2025).

**Algorithm.** Proximal Sampler $`P_{\mathrm{prox}} = P^+_{\mathrm{prox}} P^-_{\mathrm{prox}}`$
(forward Gaussian channel, backward RGO channel) and ULA, analysed through contraction coefficients
of strong data-processing inequalities for $`\Phi`$-divergences. Library: KL only
($`\Phi(x) = x \log x`$), `Proximal.proxKernel`, `ProximalPi.proxKernelPi`; ULA only as the Gaussian
step of CE-03.

**Main result.** Theorem 1 (ULA): under a $`\Phi`$-Sobolev inequality of the biased limit
$`\nu^\eta`$ and $`L`$-smoothness,
```math
D_\Phi(\rho_k \Vert \nu^\eta) \le (1 + 2\alpha\eta/(1 + \eta L)^2)^{-k} D_\Phi(\rho_0 \Vert
\nu^\eta).
```
Theorem 2 (Proximal Sampler): under a $`\Phi`$-Sobolev inequality with constant $`\alpha`$,
$`D_\Phi(\rho_k \Vert \nu) \le D_\Phi(\rho_0 \Vert \nu)/(1 + \alpha\eta)^{2k}`$ (for KL, the rate of
Theorem 3 of Chen–Chewi–Salim–Wibisono), proved from Lemma 7 (contraction coefficient of a
composition), Lemma 8 (forward step) and Lemma 9 (backward step), with Lemmas 1–4 (Lipschitz
push-forward, convolution, strong log-concavity, de Bruijn-type identity). Corollary 1: complexity
with a rejection-sampling RGO. Appendix G: Propositions 1–2 compute the Gaussian iterates of ULA and
of the Proximal Sampler and show that Theorems 1–2 are tight for KL on Gaussian targets.

| Step | Move | Library | Status |
|---|---|---|---|
| Lemma 8 (forward step contracts by $`(1 + \alpha\eta)^{-1}`$), KL case | contraction, differentiation | PX-2: `HeatFlowDeBruijn.hasDerivAt_heatKL`, `HeatFlowDeBruijnPi.hasDerivAt_heatKL`, `HeatFlowDeBruijn.toReal_klDiv_forwardKernel_le_of_regular`, `ProximalSharpLSIPi.toReal_klDiv_forwardKernelPi_le_of_targetLSIPi` | Conditional (PX-2) on the LSI of the target and `HeatFlowRegular`; other $`\Phi`$ not formalised |
| Lemma 9 (backward step contracts by $`(1 + \alpha\eta)^{-1}`$), KL case | contraction, differentiation | PX-2: `ProximalSharpLSI.toReal_klDiv_rgoKernel_comp_le_of_targetLSI`, `ProximalSharpLSIPi.toReal_klDiv_rgoKernelPi_comp_le_of_targetLSIPi`, `BackwardHeatFlowPi.hasDerivAt_integral_bklIntegrandPi` | Conditional (PX-2) on the LSI and `BackwardHeatFlowRegular`; the backward flow is built from posterior kernels rather than the time reversal of an SDE; other $`\Phi`$ not formalised |
| Lemma 7 (contraction coefficient of the composition) | contraction | PX-2: `ProximalSharpLSI.toReal_klDiv_proxKernel_comp_le_sq_of_targetLSI`, `ProximalSharpLSIPi.toReal_klDiv_proxKernelPi_comp_le_sq_of_targetLSIPi` | Conditional (PX-2); the two one-step KL bounds are composed along the chain; contraction coefficients as suprema over inputs are not formed |
| Lemma 4 (de Bruijn-type identity), KL case | differentiation | `HeatFlowDeBruijn.hasDerivAt_heatKL`, `HeatFlowDeBruijnPi.hasDerivAt_heatKL`, `BackwardHeatFlow.hasDerivAt_integral_bklIntegrand`, `BackwardHeatFlowPi.hasDerivAt_integral_bklIntegrandPi` | Holds for KL along the heat flow (drift $`b = 0`$) and along the backward heat flow under explicit regularity hypotheses (listed under PX-2, Conditional overall; the heat-flow identity is also used in KL-5); general drifts and general $`\Phi`$ not formalised |
| Lemmas 1–3 ($`\Phi`$-Sobolev constants under Lipschitz push-forward, convolution, strong log-concavity), LSI case | contraction | KL-6: `LogSobolevLipschitzMap.functionalLSI_map_of_abs_deriv_le` (1D, $`\vert T' \vert \le K`$), `LogSobolev.functionalLSI_map_add`, `LogSobolevTensorPi.functionalLSIPi_map_add`, `BakryEmery.functionalLSI_target_of_convexOn_sub`, `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn` | Verified for the LSI (KL-6); Lipschitz push-forward only in 1D (and coordinatewise maps with $`\vert T_i' \vert \le 1`$ on `Fin d → ℝ`); other $`\Phi`$ not formalised |
| Theorem 2, KL case | contraction | PX-2: `ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general`; PX-6, PX-4, PX-3 for concrete targets | Conditional (PX-2) on the LSI, with a Gaussian upper envelope stated explicitly; Verified for strongly log-concave targets, bounded perturbations of Gaussians and Gaussians (PX-6, PX-4, PX-3); $`\chi^2`$, Hellinger and other $`\Phi`$-divergences not formalised |
| Appendix G.2 (Proposition 2): Gaussian iterates of the Proximal Sampler, tightness | exact computation | EX-3: `ProximalSharpPi.klDiv_proxKernelPi_comp_gaussTarget`, `ProximalSharpPi.not_exists_rate_lt_pi`, `ProximalSharp.klDiv_proxKernel_comp_gaussTarget` | Verified (EX-3); a related instance: starts $`\mathcal{N}(m, \alpha^{-1} I)`$ with exact factor $`(1 + \alpha\eta)^{-2}`$ per step and no smaller factor; the start $`\mathcal{N}(\mathbf{1}, I)`$ with a covariance mismatch is not formalised |
| Appendix G.1: biased limit of ULA on Gaussian targets | exact computation | CE-03: `Counterexamples.ULADiscretization.ulaStep_biasedGaussian`, `Counterexamples.ULADiscretization.ulaStep_gaussianReal_eq_self_iff` | Special case (CE-03, Counterexample status: ULA is biased): 1D standard Gaussian target, where the ULA-invariant centred Gaussian is $`\mathcal{N}(0, 2/(2 - h))`$; Proposition 1's KL rate not formalised |
| Theorem 1 (ULA under a $`\Phi`$-Sobolev inequality), Corollaries 1–2 | contraction | not formalised | Not formalised |

### Gross (1975)

Leonard Gross. Logarithmic Sobolev inequalities. American Journal of Mathematics 97 (1975),
1061–1083. [doi:10.2307/2373688](https://doi.org/10.2307/2373688) (not on arXiv).

**Setting.** Not an algorithm: the log-Sobolev inequality of a Gaussian measure. It enters the
proximal sampler through the forward (heat-flow) step, whose law inherits a log-Sobolev inequality
by convolution (PX-2), and, with the Holley–Stroock lemma, through the perturbed Gaussian targets
(PX-4).

**Main result, as used here.** For the standard Gaussian measure $`\gamma`$ on $`\mathbb{R}^n`$,
$`\int f^2 \log \lvert f \rvert \, d\gamma \le \int \Vert \nabla f \Vert^2 \, d\gamma + \Vert f \Vert_2^2 \log \Vert f \Vert_2`$,
that is $`\mathrm{Ent}_\gamma(f^2) \le 2 \int \Vert \nabla f \Vert^2 \, d\gamma`$, with a constant
that does not depend on $`n`$. The paper obtains it from an inequality on the two-point space,
passing to the Gaussian limit with the central limit theorem, and it shows that log-Sobolev
inequalities are equivalent to Nelson's hypercontractivity inequalities.

| Step | Move | Library | Status |
|---|---|---|---|
| Gaussian log-Sobolev inequality, functional form, for $`\mathcal{N}(0, tI)`$ and every $`t \gt 0`$ | contraction | KL-6: `GaussianFunctionalLSI.functionalLSI_gaussianReal` (1D), `GaussianFunctionalLSIPi.functionalLSIPi_gaussian` (`Fin d → ℝ`); unbounded test functions: `LogSobolevExtensionPi.ent_sq_le_of_functionalLSIPi` | Verified (KL-6); proves a version of the inequality for test functions in `LSIClass` / `LSIClassPi` (differentiable, bounded, with bounded gradient and a positive lower bound), extended to positive $`C^1`$ functions with $`g^2`$, $`g^2 \log g^2`$ and $`\Vert \nabla g \Vert^2`$ integrable |
| The same in KL–Fisher form: $`\mathrm{KL}(\rho \Vert \mathcal{N}(0, vI)) \le (v/2) \, I(\rho \Vert \mathcal{N}(0, vI))`$ | differentiation | KL-5: `GaussianLSIZero.klDiv_le_fisher0` (1D), `GaussianLSIZeroPi.klDiv_le_fisher0` (`Fin d → ℝ`); along the heat flow `GaussianLSIPi.heatKL_le_heatFisher_gaussian`, `GaussianLSIPi.heatFisher_gaussian_le` | Verified (KL-5): for $`\rho`$ with a positive differentiable density, finite second moment and finite relative Fisher information, and along the heat flow from every law with finite second moment |
| Proof from the two-point space by the central limit theorem | — | not formalised; the library derives the functional form from the KL–Fisher form (density $`\propto g^2 \varphi_t`$), which it proves from the de Bruijn identity and the decay of Fisher information along the heat flow | Not formalised (the paper's route); the conclusion is proved by another route (previous rows) |
| Use for the proximal sampler: $`\mathrm{LSI}(\pi, C)`$ gives $`\mathrm{LSI}(\pi * \mathcal{N}(0, tI), C + t)`$; with Holley–Stroock, the perturbed Gaussian targets | contraction | KL-6: `GaussianFunctionalLSI.functionalLSI_heatKernel_comp_of_targetLSI` (1D), `LogSobolevTensorPi.functionalLSIPi_map_add` (`Fin d → ℝ`); PX-4: `GaussianFunctionalLSIPi.functionalLSIPi_targetPi_gaussPotentialPi_add` | Verified (KL-6, PX-4); the first gives the forward-step contraction of PX-2 |
| Equivalence of log-Sobolev inequalities with hypercontractivity | contraction | not formalised | Not formalised |

### Holley–Stroock (1987)

Richard Holley, Daniel Stroock. Logarithmic Sobolev inequalities and stochastic Ising models.
Journal of Statistical Physics 46 (1987), 1159–1194.
[doi:10.1007/BF01011161](https://doi.org/10.1007/BF01011161) (not on arXiv).

**Setting.** Not an algorithm: the bounded perturbation $`\mu \mapsto e^{-W}\mu/Z`$
(`HolleyStroock.tilt`, Mathlib's `μ.tilted (-W)`) of a reference law with a log-Sobolev inequality;
used for the proximal-sampler targets $`\pi \propto e^{-\alpha \Vert x \Vert^2/2 - W}`$ (PX-4).

**Main result, as used here.** The bounded-perturbation lemma: if $`\mu`$ satisfies a log-Sobolev
inequality with constant $`C`$ and $`W`$ is bounded, then $`e^{-W}\mu/Z`$ satisfies one with
constant $`C e^{\mathrm{osc}\,W}`$. The paper's main subject is log-Sobolev inequalities for
stochastic Ising models.

| Step | Move | Library | Status |
|---|---|---|---|
| Variational formula $`\mathrm{Ent}_\mu(h) = \inf_{c \gt 0} \int \psi_c(h) \, d\mu`$ | contraction | KL-6: `HolleyStroock.integral_psi_eq`, `HolleyStroock.isGLB_integral_psi` | Verified (KL-6) |
| Perturbation lemma, density form: $`0 \lt m \le d\nu/d\mu \le M`$ gives constant $`C M/m`$ | contraction | KL-6: `HolleyStroock.functionalLSI_withDensity` | Verified (KL-6) |
| Perturbation lemma, tilt form: $`a \le W \le b`$ gives $`\mathrm{LSI}(e^{-W}\mu/Z, C e^{b-a})`$ | contraction | KL-6: `HolleyStroock.functionalLSI_tilt` (1D), `GaussianFunctionalLSIPi.functionalLSIPi_tilt` (`Fin d → ℝ`) | Verified (KL-6); pointwise bounds $`a \le W \le b`$ (not an essential oscillation); functional LSI on the test classes `LSIClass` / `LSIClassPi` |
| Use for the proximal sampler | contraction | PX-4: `HolleyStroock.functionalLSI_target_gaussPotential_add`, `GaussianFunctionalLSIPi.functionalLSIPi_targetPi_gaussPotentialPi_add`, `ProximalSharpPerturbedPi.toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top`; strongly log-concave reference: `ProximalPerturbedGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave_add` | Verified (PX-4): rate $`(1 + \alpha e^{-(b-a)}\eta)^{-2k}`$ from every start with finite KL; the same with a strongly log-concave reference potential is also Verified |
| Log-Sobolev inequalities for stochastic Ising models (main results of the paper) | — | not formalised | Not formalised |

### Bakry–Émery (1985)

Dominique Bakry, Michel Émery. Diffusions hypercontractives. Séminaire de probabilités XIX, 1983/84,
Lecture Notes in Mathematics 1123, Springer, 1985, pp. 177–206. [Numdam
SPS_1985__19__177_0](https://www.numdam.org/item/SPS_1985__19__177_0/) (not on arXiv).

**Setting.** Not an algorithm: the log-Sobolev inequality of a target $`\pi \propto e^{-f}`$ with
$`f - \alpha \Vert x \Vert^2/2`$ convex (`LogSobolevPi.FunctionalLSIPi`), used for the proximal
sampler (PX-6).

**Main result, as used here.** Corollaire 2 (with Proposition 4): if
$`\Gamma_2(f, f) \ge \lambda \Gamma(f, f)`$ for all $`f`$ in the algebra $`\mathcal{A}`$,
hypercontractivity holds with constant $`\lambda`$, equivalently (Proposition 4, Gross's theorem) a
log-Sobolev inequality; for $`L = \Delta - \nabla f \cdot \nabla`$ the condition reads
$`\nabla^2 f \succeq \lambda I`$. Used here only through this consequence.

| Step | Move | Library | Status |
|---|---|---|---|
| Curvature condition $`\Gamma_2 \ge \lambda \Gamma`$ and the semigroup argument | contraction | not formalised; the library's hypothesis is convexity of $`f - \alpha \Vert x \Vert^2/2`$ on the whole space, $`f`$ finite, no smoothness | Not formalised (the $`\Gamma_2`$ / semigroup route); the conclusion is proved by other routes (next steps) |
| Conclusion $`\mathrm{LSI}(1/\alpha)`$ in dimension one | contraction | KL-6: `BakryEmery.exists_contraction_target` (monotone transport from $`\mathcal{N}(0, 1/\alpha)`$ with $`\vert T' \vert \le 1`$), `LogSobolevLipschitzMap.functionalLSI_map_of_abs_deriv_le`, `GaussianFunctionalLSI.functionalLSI_gaussianReal`, `BakryEmery.functionalLSI_target_of_convexOn_sub` | Verified (KL-6); the conclusion is proved by a different route (one-dimensional Caffarelli contraction) |
| Conclusion $`\mathrm{LSI}(1/\alpha)`$ on `Fin d → ℝ` | contraction | KL-6: `PrekopaLeindler.prekopa_leindler`, `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`; separable case `BakryEmeryPi.functionalLSIPi_targetPi_sepPotential` | Verified (KL-6), by the Bobkov–Ledoux route through Prékopa–Leindler |
| Use for the proximal sampler | contraction | PX-6: `ProximalStronglyLogConcaveGeneralPi.functionalLSIPi_targetPi_of_stronglyLogConcave`, `EuclideanTransfer.ent_sq_le_of_stronglyLogConcave`, `ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave` | Verified (PX-6): rate $`(1 + \alpha\eta)^{-2k}`$ from every start with finite KL, no named hypotheses |
| Proposition 4: equivalence of log-Sobolev inequalities and hypercontractivity | contraction | not formalised | Not formalised |

## Flows and particle methods

### DiPerna–Lions (1989)

Ronald J. DiPerna, Pierre-Louis Lions. Ordinary differential equations, transport theory and Sobolev
spaces. Inventiones Mathematicae 98(3), 511–547, 1989.
[doi:10.1007/BF01393835](https://doi.org/10.1007/BF01393835) (not on arXiv).

**Setting.** Continuity equation $`\partial_t u_t + \nabla \cdot (u_t v) = 0`$ for curves of
probability densities $`u_t`$ and an autonomous velocity $`v \in W^{1,1}_{\mathrm{loc}}`$ with
bounded divergence (`NoiseScore.WeakContinuityDensity`); in DiPerna–Lions it is the case $`b = -v`$,
$`c = \mathrm{div}\, v`$ of the linear transport equation (11). In the library it is a
PDE-uniqueness input of the noise–score equivalence (FL-5).

**Main result.** Section II: Proposition II.1 (existence of solutions of (11) in
$`L^\infty(0, T; L^p)`$); Theorem II.1 with Lemma II.1 (mollified solutions satisfy (11) up to a
commutator error $`r_\varepsilon \to 0`$ in $`L^1(0, T; L^\beta_{\mathrm{loc}})`$ for
$`b \in L^1(0, T; W^{1,\alpha}_{\mathrm{loc}})`$); Theorem II.2 (uniqueness in
$`L^\infty(0, T; L^p)`$ when $`c, \mathrm{div}\, b \in L^1(0, T; L^\infty)`$,
$`b \in L^1(0, T; W^{1,q}_{\mathrm{loc}})`$ and
$`b/(1 + \vert x \vert) \in L^1(0, T; L^1) + L^1(0, T; L^\infty)`$); Corollary II.2 (renormalised
equation); Theorem II.4 (stability). Section III: flows of ODEs with Sobolev coefficients.

| Step | Move | Library | Status |
|---|---|---|---|
| Weak formulation for density solutions with an a.e.-defined Sobolev velocity | identification | `NoiseScore.WeakContinuityDensity`, `MemW11locBddDiv` (definitions, FL-5 row) | Definitions: continuity equation in conservative form, $`C^2_c`$ test functions, $`t \ge 0`$, curves of probability densities, autonomous velocity |
| Regularisation: the mollified equation with a commutator error (Theorem II.1) and the commutator lemma (Lemma II.1 (i)) | identification | FL-5 row: `NoiseScore.hasDerivWithinAt_convolution_eq_transport_add_commutator`, `NoiseScore.dlCommutator_eq`, `NoiseScore.tendsto_lintegral_dlCommutator_sub`, `NoiseScore.tendsto_lintegral_dlCommutator_sub_Lp` | No named hypothesis, every dimension; listed under FL-5, which is Conditional overall. Proves a version for autonomous $`v`$ with convergence in $`L^1_{\mathrm{loc}}`$: $`w \in L^\infty`$ with $`v \in W^{1,1}_{\mathrm{loc}}`$, and $`w \in L^1 \cap L^p`$ with $`v \in W^{1,q}_{\mathrm{loc}}`$ of linear growth ($`1 \lt p, q \lt \infty`$ conjugate); the time-dependent part (ii) is not formalised |
| Renormalisation (proof of Theorem II.2; Corollary II.2, Eq. (24)) | identification | FL-5 row: `NoiseScore.energy_identity_of_weakContinuityDensity`, `NoiseScore.renormalized_identity_of_linearGrowth` | No named hypothesis; listed under FL-5 (Conditional overall). Proved for $`\beta(s) = s^2`$ with bounded $`v`$, and for smooth $`\beta`$ with $`\beta, \beta'`$ bounded under linear growth (the commutator convergence is an explicit hypothesis, discharged by the lemmas above); unbounded $`\beta`$ under linear growth and time-dependent velocities are not formalised |
| Uniqueness (Theorem II.2) | identification | FL-5 row: `NoiseScore.ae_eq_of_weakContinuityDensity_diPernaLions`, `NoiseScore.ae_eq_of_weakContinuityDensity_diPernaLions_linearGrowth`, `NoiseScore.ae_eq_of_weakContinuityDensity_diPernaLions_Lp`, `NoiseScore.ae_eq_of_weakContinuityDensity_one_dim`, `NoiseScore.ae_eq_of_weakContinuityDensity_of_hasWeakJacobian_loc` | No named hypothesis; listed under FL-5 (Conditional overall). Proves a version of Theorem II.2: autonomous $`v \in W^{1,1}_{\mathrm{loc}}`$ with bounded divergence and a.e. linear growth, probability-density solutions that are uniformly bounded, or in $`L^\infty_t L^p_x`$ with $`v \in W^{1,q}_{\mathrm{loc}}`$ ($`1 \lt p \lt \infty`$); one dimension and $`W^{1,\infty}_{\mathrm{loc}}`$ by reduction to Lipschitz uniqueness. Time-dependent $`v`$, signed solutions and the growth condition $`v/(1 + \vert x \vert) \in L^1 + L^\infty`$ are not formalised |
| Existence (Proposition II.1), stability (Theorem II.4), the $`L^1`$ theory with $`W^{1,1}_{\mathrm{loc}}`$ velocities, and the ODE flows of Section III | identification | not formalised | Not formalised; for locally Lipschitz velocities of linear growth the library proves continuity-equation uniqueness without flow maps (`NoiseScore.uniqueWeakContinuity_of_locallyLipschitz`, FL-5 row) |

### Bogachev–Krylov–Röckner–Shaposhnikov (2015)

Vladimir I. Bogachev, Nicolai V. Krylov, Michael Röckner, Stanislav V. Shaposhnikov.
Fokker–Planck–Kolmogorov Equations. Mathematical Surveys and Monographs 207, American Mathematical
Society, 2015. [doi:10.1090/surv/207](https://doi.org/10.1090/surv/207) (a book, not on arXiv).

**Setting.** Law curves $`(\rho_t)_{t \ge 0}`$ of $`dX_t = b_t(X_t) \, dt + \sqrt{2D} \, dW_t`$ as
probability solutions of the weak Fokker–Planck–Kolmogorov equation
$`\tfrac{d}{dt} \rho_t(\varphi) = \rho_t(b_t \cdot \nabla \varphi + D \Delta \varphi)`$ for
$`\varphi \in C^2_c`$ and $`t \ge 0`$ (`NoiseScore.WeakFokkerPlanck`, constant scalar $`D \gt 0`$).
The library constructs them as weak limits of Euler–Maruyama laws, with no SDE theory.

**Main result, as used here.** Chapter 9 (Uniqueness of solutions to Fokker–Planck–Kolmogorov
equations) gives uniqueness of probability solutions of the Cauchy problem; the library cites it for
drifts with $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$, a class that contains the
globally Lipschitz drifts of FL-6 and the dissipative drifts of quartic and double-well Langevin
dynamics.

| Step | Move | Library | Status |
|---|---|---|---|
| Weak formulation: probability-measure curves solving the Fokker–Planck–Kolmogorov equation against test functions | identification | `NoiseScore.WeakFokkerPlanck` (definition); FL-5, FL-6 | Definition: $`C^2_c`$ test functions, times $`t \ge 0`$, constant scalar diffusion $`D`$; matrix and degenerate diffusions are not covered |
| Ch. 9 uniqueness, globally Lipschitz case: drifts with $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$ include drifts Lipschitz in $`x`$ | identification | FL-6: `FokkerPlanckUniqueness.eq_of_weakFokkerPlanck_lipschitz`, `FokkerPlanckUniqueness.eq_of_weakFokkerPlanck_lipschitzWith`, `FokkerPlanckUniqueness.integral_eq_of_weakFokkerPlanck_of_approx`, `FokkerPlanckUniqueness.exists_tail_le` | Verified (FL-6), special case: $`D \gt 0`$, drift jointly continuous and Lipschitz in $`x`$ uniformly on each $`[0, T]`$, no moment, density or tightness assumption (uniform tightness is proved). The proof is an approximate Kolmogorov duality (frozen Euler transport steps and Gaussian smoothing) |
| Further cases of the same growth condition: bounded continuous drifts, and $`-ax`$ plus a bounded continuous drift | identification | FL-5 row: `FokkerPlanckUniqueness.eq_of_weakFokkerPlanck`, `FokkerPlanckUniqueness.eq_of_weakFokkerPlanck_linear_add_bounded` | No named hypothesis (heat-semigroup duality; space–time rescaling for $`-ax`$ plus bounded); listed under FL-5, which is Conditional overall |
| Uniqueness for dissipative drifts that are not globally Lipschitz (quartic and double-well Langevin) | identification | not formalised; existence only: `FokkerPlanckExistence.exists_weakFokkerPlanck_dissipative`, `FokkerPlanckExistence.exists_weakFokkerPlanck_doubleWell` (FL-5 row) | Uniqueness not formalised; existence for locally Lipschitz dissipative drifts is proved (listed under FL-5, Conditional overall). The library states that without a growth condition uniqueness can fail for $`d \ge 2`$ (Bogachev–Krasovitskii–Shaposhnikov 2021, cited, not formalised) |
| Existence and well-posedness of probability solutions | identification | FL-6: `FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_lipschitz`, `FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_lipschitz_continuousTime`, `FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_langevin_lipschitz`, `FokkerPlanckUniqueness.tendsto_emCurveP_of_weakFokkerPlanck_lipschitz`; FL-5 row: `FokkerPlanckExistence.exists_weakFokkerPlanck_lipschitz`, `FokkerPlanckExistence.exists_weakFokkerPlanck_continuousTime` | Verified (FL-6): existence and uniqueness for autonomous and time-dependent Lipschitz drifts and for Langevin with Lipschitz $`\nabla U`$; for autonomous drifts every solution is the weak limit of the dyadic Euler–Maruyama laws, with no rate. Existence is proved by Euler–Maruyama limits, tightness and Prokhorov's theorem; the library cites the book for uniqueness only |
| Use in the library: the Langevin law curve supplies the weak Fokker–Planck input of the noise–score equivalence | identification | FL-5: `FokkerPlanckExistence.exists_langevin_law_fl5`, `NoiseScoreOUUnconditional.map_flow_eq_ouLaw` | No named hypothesis for Lipschitz $`\nabla U`$; FL-5 is Conditional overall (continuity-equation uniqueness for the probability-flow velocity remains a named input outside the proved classes); unconditional for OU from $`\mathcal{N}(m, v_0 I)`$ |

### SVGD: Liu–Wang (2016)

Qiang Liu, Dilin Wang. Stein Variational Gradient Descent: A General Purpose Bayesian Inference
Algorithm. NIPS 2016. [arXiv:1608.04471](https://arxiv.org/abs/1608.04471) (v3, 9 Sep 2019).

**Algorithm.** Stein variational gradient descent (SVGD), a deterministic transport:
$`q_{\ell+1} = (\mathrm{id} + \epsilon_\ell \phi^\star_{q_\ell, p})_\# q_\ell`$ with
```math
\phi^\star_{q,p} = \mathbb{E}_{x \sim q}[k(x, \cdot) \nabla \log p(x) + \nabla_x k(x, \cdot)];
```
Algorithm 1 applies the same map to the empirical measure of $`n`$ particles (Eq. (8)). The library
treats only finite feature kernels $`k(x, y) = \psi(x)^\top \psi(y)`$, as in §3.2.1 of
Dong–Wang–Lin–Zhang (2023).

**Main result.** Theorem 3.1: for $`T(x) = x + \epsilon \phi(x)`$,
$`\nabla_\epsilon \mathrm{KL}(q_{[T]} \Vert p)`$ at $`\epsilon = 0`$ equals
$`-\mathbb{E}_{x \sim q}[\mathrm{trace}(\mathcal{A}_p \phi(x))]`$, with the Stein operator
$`\mathcal{A}_p \phi = \nabla \log p \, \phi^\top + \nabla \phi`$. Lemma 3.2: over the RKHS ball of
radius $`\mathbb{S}(q, p)^{1/2}`$ the steepest-descent direction is $`\phi^\star_{q,p}`$ (Eq. (6)),
and the derivative equals $`-\mathbb{S}(q, p)`$, the kernel Stein discrepancy. Theorem 3.3:
$`-\phi^\star_{q,p}`$ is the RKHS functional gradient of the KL at $`f = 0`$. Algorithm 1 (Eq. (8)):
the particle update.

| Step | Move | Library | Status |
|---|---|---|---|
| Theorem 3.1: the derivative of $`\mathrm{KL}((\mathrm{id} + \epsilon\phi)_\# q \Vert p)`$ at $`\epsilon = 0`$ is $`-\mathbb{E}_q[\mathrm{trace}(\mathcal{A}_p \phi)]`$ | differentiation | DT-1: `DeterministicStep.klDiv_map_step_le`, `DeterministicStepPi.klDiv_map_step_le`, `DeterministicStepGeneral.klDiv_map_step_le`; FL-1: `KLTransport.hasDerivAt_klIntegral_stein_form` | Related statement. DT-1 (Verified): $`\mathrm{KL}((\mathrm{id} + \eta v)_\# \rho \Vert \pi) \le \mathrm{KL}(\rho \Vert \pi) - \eta \int p \, (\mathrm{div}\, v - \nabla U \cdot v) + \eta^2 R`$ with an explicit second-order term $`R`$, under Lipschitz and Hessian bounds; its first-order term is the Stein term of Theorem 3.1. FL-1 (Verified): the exact derivative along a continuity equation. The $`\epsilon`$-derivative at $`\epsilon = 0`$ is not stated as such |
| Lemma 3.2, Eq. (6): the steepest-descent direction $`\phi^\star_{q,p} = \mathbb{E}_{x \sim q}[k(x, \cdot) \nabla \log p(x) + \nabla_x k(x, \cdot)]`$ | score | SE-2: `FeatureClass.svgdPopObjective_isMinimiser_iff`, `FeatureClass.svgdPopMatrix_mulVec_apply` | Special case, Verified (SE-2): for a finite feature kernel $`k(x, y) = \psi(x)^\top \psi(y)`$, the Stein term plus the penalty $`(\lambda/2) \Vert W \Vert_F^2`$ ($`\lambda \gt 0`$) has a unique minimiser, whose field is $`\frac{1}{\lambda} \mathbb{E}_\mu[k(y, \cdot) \, s_\star(y) + \nabla_y k(y, \cdot)]`$ (stated coordinatewise). The ball-constrained form, general RKHS and the identity with the kernel Stein discrepancy are not formalised |
| Theorem 3.3: $`-\phi^\star_{q,p}`$ as the RKHS functional gradient of $`f \mapsto \mathrm{KL}(q_{[\mathrm{id} + f]} \Vert p)`$ at $`f = 0`$ | score | not formalised | Not formalised (no RKHS theory in the library) |
| Algorithm 1, Eq. (8): the empirical direction on $`n`$ particles and the update $`x_i \mapsto x_i + \epsilon_\ell \hat\phi^\star(x_i)`$ | identification, score | SE-2: `FeatureClass.svgdFeatureObjective_isMinimiser_iff`, `FeatureClass.svgdMatrix_mulVec`; PT-1: `Particles.map_eulerStep_empirical`, `Particles.empirical_eulerParticles` | Special case, Verified: for a finite feature kernel the empirical penalised objective has a unique minimiser, whose field is $`\frac{1}{\lambda n} \sum_j (k(y_j, \cdot) \, s_\star(y_j) + \nabla_y k(y_j, \cdot))`$, Eq. (8) at $`\lambda = 1`$ (SE-2); Euler steps push the empirical measure forward exactly (PT-1). Mean-field limits and propagation of chaos are not formalised |
| SVGD as a special case of PFG (Dong–Wang–Lin–Zhang 2023, §3.2.1) | score | SE-2: `FeatureClass.featureSteinObjective_eq_svgdFeatureObjective`, `FeatureClass.featureStein_isMinimiser_iff_eq_svgdMatrix` | Verified (SE-2): when $`\Sigma_\psi = I`$ and $`H = \lambda I`$ the empirical PFG objective equals the SVGD objective and the SVGD matrix minimises it; only this sufficient condition is proved |

### Wibisono (2018)

Andre Wibisono. Sampling as optimization in the space of measures: The Langevin dynamics as a
composite optimization problem. COLT 2018, PMLR 75.
[arXiv:1802.08089](https://arxiv.org/abs/1802.08089) (v2, 6 Jun 2018).

**Algorithm.** ULA: the Markov kernel
$`x \mapsto \mathcal{N}(x - \epsilon \nabla f(x), 2\epsilon I)`$, i.e. the pushforward by
$`I - \epsilon \nabla f`$ followed by the heat kernel; the Langevin/Fokker–Planck flow as the
gradient flow of $`\mathrm{KL}(\cdot \Vert \nu)`$; the forward method, a deterministic step
$`\rho \mapsto (I - \epsilon \nabla \log(\rho/\nu))_\# \rho`$; SLA, ULA composed with a proximal
step.

**Main result.** Example 2: for $`\nu = \mathcal{N}(\mu, \Sigma)`$ and
$`0 \lt \epsilon \lt 2\lambda_{\min}(\Sigma)`$, ULA converges to
$`\nu_\epsilon = \mathcal{N}(\mu, \Sigma (I - \tfrac{\epsilon}{2} \Sigma^{-1})^{-1}) \ne \nu`$.
§2.2.2: ULA is the Forward-Flow discretisation of $`H_\nu(\rho) = \mathbb{E}_\rho[f] - H(\rho)`$.
Example 3: the symmetrized Langevin algorithm (SLA) is consistent for Gaussian targets. Lemmas 1 and
3: $`W_2`$ contraction of ULA and SLA under strong log-concavity and smoothness; Lemma 2: an
$`O(\epsilon)`$ $`W_2`$ bias bound for ULA (from Dalalyan–Karagulyan). §3.1.2: under $`\alpha`$-LSI,
$`H_\nu(\rho_t) \le e^{-2\alpha t} H_\nu(\rho_0)`$ along the Fokker–Planck flow. Examples 4, 5, 8,
9: the forward, backward, Forward-Backward and Backward-Forward methods for OU with Gaussian data
are consistent.

| Step | Move | Library | Status |
|---|---|---|---|
| §2.1, §3.1.2: the Fokker–Planck equation (Eqs. (3), (10)) as the Wasserstein gradient flow of $`H_\nu`$, a continuity equation with velocity $`-\nabla \log(\rho_t/\nu)`$, implemented by the Langevin SDE (4) | identification | FL-5: `NoiseScore.map_flow_eq_of_weakFokkerPlanck`, `NoiseScore.weakContinuity2_of_weakFokkerPlanck`, `NoiseScoreOUUnconditional.map_flow_eq_ouLaw`, `FokkerPlanckExistence.exists_langevin_law_fl5`; ID-3: `ScoreFlowWeak.integral_generator_eq_score_flow_generator` | Conditional (FL-5): the weak Fokker–Planck law curve and the transport by the probability-flow velocity have the same one-time marginals, given the weak Fokker–Planck equation (Itô input) and continuity-equation uniqueness; ID-3 Verified; for OU from $`\mathcal{N}(m, v_0 I)`$ the equality holds with no named hypothesis, and for Lipschitz $`\nabla U`$ a Langevin law curve solving the weak equation is constructed. The SDE and the Wasserstein gradient-flow structure are not formalised |
| Example 1: exact Gaussian solution of the OU process | identification | FL-5 row: `WeakFokkerPlanckOU.weakFokkerPlanck_ou`, `WeakFokkerPlanckOU.weakFokkerPlanck_ouVar`, `FokkerPlanckUniqueness.existsUnique_weakFokkerPlanck_ou` | Special case (centred isotropic target $`\mathcal{N}(0, vI)`$): the Gaussian transition kernel is the definition of the flow; its law curve solves the weak Fokker–Planck equation from every initial law, and that solution is unique. These theorems have no named hypothesis; they are listed under FL-5, which is Conditional overall. The Itô solution is not formalised |
| §3.1.2: under $`\alpha`$-LSI, $`\frac{d}{dt} H_\nu(\rho_t) = -J_\nu(\rho_t) \le -2\alpha H_\nu(\rho_t)`$, hence $`H_\nu(\rho_t) \le e^{-2\alpha t} H_\nu(\rho_0)`$ | contraction, differentiation | FL-4: `KLDecay.exp_decay_of_lsi`, `KLDissipation.klDecay_of_idealVelocity`, `OULangevinDecay.toReal_klDiv_ouKernelVar_comp_le`, `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`, `OULangevinDecay.toReal_klDiv_ouKernelVar_comp_gaussianReal` | Conditional (FL-4) in general: the Grönwall step is proved, the LSI along the flow is the named hypothesis `LogSobolevAlong`, and the flow is modelled in transport form. For the target $`\mathcal{N}(0, vI)`$ and drift $`-ax`$ (Wibisono's normalisation is $`a = \alpha = 1/v`$), $`\mathrm{KL}(\rho_t \Vert \pi) \le e^{-2at} \mathrm{KL}(\rho_0 \Vert \pi)`$ is proved from every initial law with finite KL and second moment, by a heat-flow contraction with no LSI hypothesis, with equality for $`\mathcal{N}(m, vI)`$. The Talagrand step to $`W_2`$ is not formalised |
| §2.2.2: ULA (5) as the Forward-Flow composition (7a)–(7b): pushforward by $`I - \epsilon \nabla f`$, then convolution with $`\mathcal{N}(0, 2\epsilon I)`$ | identification | GI-1 kernels: `GaussianIncrement.emKernel_apply`, `GaussianIncrement.emKernelPi_apply`; CE-03: `Counterexamples.ULADiscretization.law_ulaUpdate` | Definitions and law identities (GI-1 Verified, CE-03 module): the Gaussian-increment kernel $`x \mapsto \mathcal{N}(x + h b(x), 2hI)`$ is ULA for $`b = \nabla \log \pi`$; for $`\mathcal{N}(0, 1)`$ the ULA law is written as this pushforward followed by a Gaussian convolution and matched to the random-variable update. The composite-optimisation reading is not formalised |
| Example 2: ULA for OU is biased, with limit $`\mathcal{N}(\mu, \Sigma (I - \tfrac{\epsilon}{2} \Sigma^{-1})^{-1})`$ and $`W_2`$ bias $`\tfrac{\epsilon}{4} \sqrt{\mathrm{Tr}\, \Sigma^{-1}} + O(\epsilon^2)`$ | exact computation | CE-03: `Counterexamples.ULADiscretization.ulaStep_gaussianReal`, `Counterexamples.ULADiscretization.ulaStep_standardGaussian_ne`, `Counterexamples.ULADiscretization.ulaStep_biasedGaussian`, `Counterexamples.ULADiscretization.ulaStep_gaussianReal_eq_self_iff`, `Counterexamples.ULADiscretization.ulaStep_iterate_gaussianReal`, `Counterexamples.ULADiscretization.ulaStep_iterate_var_tendsto` | Special case (CE-03, Counterexample status: ULA is biased): target $`\mathcal{N}(0, 1)`$ in one dimension, centred Gaussian initial laws. One step maps $`\mathcal{N}(0, 1)`$ to $`\mathcal{N}(0, 1 + h^2)`$; for $`0 \lt h \lt 2`$ the only invariant centred Gaussian is $`\mathcal{N}(0, 2/(2 - h))`$ (Example 2 at $`\Sigma = 1`$), and the variances of the iterates converge to it. Convergence of the laws (weak, TV or $`W_2`$) and the $`W_2`$ bias expansion are not formalised |
| Lemma 1 ($`W_2`$ contraction of ULA by synchronous coupling) and Lemma 2 ($`O(\epsilon)`$ bias of ULA) | contraction | not formalised | Not formalised |
| §2.4: the symmetrized Langevin algorithm (Eq. (8)), Example 3 (consistent for OU) and Lemma 3 ($`W_2`$ contraction) | contraction, exact computation | not formalised | Not formalised |
| Example 4: forward method (11), $`\rho_{k+1} = (I - \epsilon \nabla \log(\rho_k/\nu))_\# \rho_k`$, for OU with Gaussian data, $`\Sigma_{k+1} = \Sigma_k (I + \epsilon(\Sigma_k^{-1} - \Sigma^{-1}))^2`$ | exact computation, differentiation | CE-08: `IdealVelocityStep.exists_klDiv_map_step_idealVel_gt`, `IdealVelocityStepPi.exists_klDiv_map_step_idealVel_gt`; DT-1: `IdealVelocityStep.klDiv_map_step_idealVel_le`, `IdealVelocityStepPi.klDiv_map_step_idealVel_le`; EX-2: `DiscreteGaussianFlow.map_eulerMap_gaussianReal`, `DiscreteGaussianFlow.nextVar_eq_self_iff` | CE-08 (Counterexample status: no fixed step size makes the ideal-velocity step a KL descent for all laws): for every step $`\eta \gt 0`$ some $`\mathcal{N}(0, s)`$ (also $`\mathcal{N}(0, sI)`$) has its KL to the standard Gaussian increased by one step; the library states this as a consequence of the Example 4 recursion. DT-1 Verified: one-step descent with a step size that depends on the current law. EX-2 Verified: in one dimension the PFG Euler map with $`\epsilon = \eta/h`$ coincides with this forward method (with a general mean), and for $`0 \lt \eta \le 2h\sigma_\star^2`$ the target is its only Gaussian fixed point |
| Example 5 (backward method for OU), Examples 6–7 (forward and backward methods for the heat flow), Examples 8–9 (Forward-Backward and Backward-Forward for OU with Gaussian data) | exact computation | not formalised | Not formalised |

### PFG: Dong–Wang–Lin–Zhang (2023)

Hanze Dong, Xi Wang, Yong Lin, Tong Zhang. Particle-based Variational Inference with Preconditioned
Functional Gradient Flow. ICLR 2023. [arXiv:2211.13954](https://arxiv.org/abs/2211.13954) (v2, 18
Apr 2023; numbering of v2).

**Algorithm.** Preconditioned functional gradient flow (PFG), a deterministic transport. Continuous
time: $`\partial_t p_t = -\nabla \cdot (p_t g_t)`$ with $`g_t`$ a minimiser over a class
$`\mathcal{F}`$ of
$`J_t(f) = -\mathbb{E}_{p_t}[\nabla \cdot f + f \cdot \nabla \ln p_\star] + Q(f)`$,
$`Q(f) = \tfrac12 \mathbb{E}_{p_t} \Vert f \Vert_H^2`$, whose unrestricted minimiser is the ideal
velocity $`v_\star = H^{-1} \nabla \ln(p_\star/p_t)`$. Discrete time (Algorithm 1): the
deterministic kernel $`x \mapsto \delta_{x + \eta f_{\hat\theta_k}(x)}`$ applied to the empirical
measure of the particles, with $`\hat\theta_k`$ from an inner stochastic-gradient loop on the Monte
Carlo objective (Eq. (8)).

**Main result.** Proposition 1: with $`Q(f) = \tfrac12 \int p_t \Vert f \Vert_H^2`$ (Eq. (6)) the
regularised functional gradient of Eq. (4) minimises
$`\tfrac12 \mathbb{E}_{p_t} \Vert f - H^{-1} \nabla \ln(p_\star/p_t) \Vert_H^2`$ over
$`\mathcal{F}`$ (Eq. (7)). Proposition 2: under [A1]–[A2],
$`-\infty \lt \frac{d}{dt} D_{\mathrm{KL}} \lt 0`$ whenever $`p_t \ne p_\star`$. Theorem 1: under
[A1]–[A4] with $`\lambda_{\max}(H) = m`$,
$`\frac{d}{dt} D_{\mathrm{KL}} \le -\frac{1-\epsilon}{2} I_{H^{-1}}(t)`$ with
$`I_{H^{-1}}(t) = \mathbb{E}_{p_t} \Vert \nabla \ln(p_t/p_\star) \Vert_{H^{-1}}^2`$, and
$`D_{\mathrm{KL}}(t) \le e^{-(1-\epsilon)\mu t/m} D_{\mathrm{KL}}(0)`$. §3.2.1: finite-feature SVGD
is the case $`Q(f) = \tfrac12 \Vert W \Vert_F^2`$ (Eqs. (9)–(10); infinite-dimensional case App.
A.7). App. A.6: in the discrete Gaussian case,
$`D_{\mathrm{KL}}(t) \le \max_i (1 - \eta/(h_i \sigma_i^2))^{2t} C_0`$ for
$`\eta \le \min_i h_i \sigma_i^2/2`$.

| Step | Move | Library | Status |
|---|---|---|---|
| Continuity equation (Eq. (1)) and KL first variation, Eq. (3) (proof App. A.1) | differentiation | FL-1: `KLTransport.hasDerivAt_klIntegral`, `KLTransport.hasDerivAt_klIntegral_stein_form`, `KLDissipation.TransportKLRegularity.hasDerivAt_klDivDensity_stein_form`, `KLDissipation.klFirstVariation_of_regularity` | Verified (FL-1), relative to a modelled flow: positive $`C^1`$ densities that satisfy the strong continuity equation pointwise, with explicit domination hypotheses; existence of the flow is not formalised |
| Regularised functional gradient, Eqs. (4) and (6); Proposition 1, Eq. (7) (proof App. A.3, Eqs. (15)–(18)) | score | SE-1: `SteinObjective.steinObjective_eq`, `SteinObjective.isMinOn_steinObjective_iff`, `SteinObjective.neg_half_le_steinObjective`, `SteinObjective.isMinOn_iff_ae_eq_idealVelocity` | Verified (SE-1). Formalises Proposition 1 over any class of admissible fields, constant SPD $`H`$; the Stein integration by parts under $`p_t`$ is an explicit hypothesis (`Admissible`); existence of a minimiser is not claimed |
| Linear function class: the regularised gradient is the weighted $`L^2(p_t)`$ projection of $`v_\star = H^{-1}\nabla\ln(p_\star/p_t)`$ (the class used in Example 1, cases (3)–(4), and App. A.6) | score | SE-2: `FeatureClass.popStein_isMinimiser_iff_normalEq`, `FeatureClass.featureStein_isMinimiser_iff_normalEq`, `SteinObjective.featureField_isMinimiser_iff_projection` | Verified (SE-2): for a finite feature dictionary, minimisers are exactly the solutions of the normal equations $`H W \Sigma_\psi = G`$ (population and empirical), i.e. the weighted least-squares projection of $`v_\star`$ |
| SVGD as a special case, §3.2.1, Eqs. (9)–(10) (finite feature map, $`Q(f) = \tfrac12 \Vert W \Vert_F^2`$) | score | SE-2: `FeatureClass.svgdFeatureObjective_isMinimiser_iff`, `FeatureClass.svgdMatrix_mulVec`, `FeatureClass.svgdPopObjective_isMinimiser_iff`, `FeatureClass.svgdPopMatrix_mulVec_apply`, `FeatureClass.featureSteinObjective_eq_svgdFeatureObjective`, `FeatureClass.featureStein_isMinimiser_iff_eq_svgdMatrix` | Verified (SE-2). Formalises Eqs. (9)–(10) with the penalty $`(\lambda/2)\Vert W \Vert_F^2`$ for every $`\lambda \gt 0`$, empirical and population (population coordinatewise); the empirical PFG and SVGD objectives coincide when $`\Sigma_\psi = I`$ and $`H = \lambda I`$; the identification of $`\Vert W \Vert_F`$ with an RKHS norm is not formalised |
| Infinite-dimensional RKHS case (App. A.7, Eqs. (36)–(38)) | score | not formalised | Not formalised (no RKHS or Mercer theory in the library) |
| Proposition 2 (App. A.4, with Lemma 1): $`-\infty \lt \frac{d}{dt} D_{\mathrm{KL}} \lt 0`$ whenever $`p_t \ne p_\star`$ | differentiation | FL-3 (c): `ApproximateVelocity.transport_rate_eq_of_isMinOn`, `ApproximateVelocity.transport_rate_nonpos_of_isMinOn` | Related statement (Verified, FL-3): at one time, for a minimiser $`g`$ over a class closed under real scaling, the rate equals $`-\int \Vert g \Vert_H^2 \, d\rho \le 0`$. The strict inequality for $`p_t \ne p_\star`$, the finiteness of the rate and Lemma 1 are not formalised |
| Exact dissipation at the ideal velocity $`v_\star`$ (the computation of App. A.5 with no velocity error) | differentiation | FL-2: `KLDissipation.hasDerivAt_klIntegral_of_eq_idealVelocity`, `KLDissipation.hasDerivAt_klIntegral_idealVelocity`, `KLDissipation.TransportKLRegularity.hasDerivAt_klDivDensity_of_eq_idealVelocity_local`, `KLDecay.ideal_rate_le_neg_fisher` | Verified (FL-2): $`\frac{d}{dt} \mathrm{KL} = -\int \Vert \nabla \log(\rho/\pi) \Vert_{H^{-1}}^2 \, d\rho`$ for constant SPD $`H`$, with the flow regularity packaged in `TransportKLRegularity` |
| First claim of Theorem 1 at one time: Cauchy–Schwarz and [A3] give $`\frac{d}{dt} D_{\mathrm{KL}} \le -\frac{1-\epsilon}{2} \mathbb{E}_{p_t} \Vert \nabla \ln(p_t/p_\star) \Vert_{H^{-1}}^2`$ (App. A.5) | differentiation | FL-3: `KLDissipation.rate_le_of_approx`, `KLDecay.transport_rate_le`, `KLDecay.transport_rate_le_objective_gap`; [A3] passed to the minimiser through Proposition 1: `KLDissipation.a3_of_isMinOn` | Verified (FL-3): the paper's constant and the bound $`-\tfrac12 I + \tfrac12 E`$ of the proof (velocity error $`E`$, weighted Fisher information $`I`$) |
| Second claim of Theorem 1: [A4] ($`\mu`$-LSI) and $`\lambda_{\max}(H) \le m`$ give Eq. (32), and Grönwall gives $`D_{\mathrm{KL}}(t) \le e^{-(1-\epsilon)\mu t/m} D_{\mathrm{KL}}(0)`$ | contraction, differentiation | FL-4: `KLDissipation.klDecay_of_steinMinimiser`, `KLDissipation.klDecay_of_approxVelocity`, `KLDissipation.klDecay_of_approxVelocity_timeDependent`, `KLDissipation.klDecay_of_idealVelocity`, `KLDecay.exp_decay_of_lsi`, `DecayWithError.le_exp_mul_add_integral` | Conditional (FL-4), with the paper's constants: on [A3] (`hA3`, stated with one $`\epsilon \lt 1`$ for all $`t \ge 0`$), [A4] (`LogSobolevAlong`) and, in the minimiser form, an assumed argmin (`hmin`); the flow, its continuity equation and `TransportKLRegularity` are hypotheses. Time-dependent, state-independent $`H_t`$ is covered; the estimated preconditioner of §3.1 is not formalised |
| Theorem 1 on non-degenerate flows: Gaussian target, where [A4] holds, and the ideal flow towards $`\mathcal{N}(0, vI)`$ | contraction, differentiation | FL-4: `LogSobolevAlongGaussian.logSobolevAlong_gaussian`, `LogSobolevAlongGaussian.exp_decay_idealVelocity_gaussian_one`, `ProbabilityFlowOU.hasDerivAt_gaussKL_ouDensity`, `ProbabilityFlowOUMoment.klDecay_of_idealVelocity_local_ou_moment`; KL-5 (Gaussian LSI) | FL-4 row Conditional. For the target $`\mathcal{N}(0, vI)`$ the LSI along the flow is proved from KL-5, leaving the first-variation formula and per-time density regularity as hypotheses. For the OU probability flow (the ideal flow with $`H = (av)^{-1} I`$) the identity $`\frac{d}{dt}\mathrm{KL} = -av \, I`$ ($`t \gt 0`$) and the decay hold from every initial law with finite second moment, with every hypothesis discharged; `TransportKLRegularity` and the generic FL-2 decay theorem hold under a finite fourth moment |
| Example 1 (App. A.2): Gaussian target and initial law in continuous time, effect of the regulariser | exact computation | EX-1: `GaussianFlowVsOU.hasDerivAt_flow`, `GaussianFlowVsOU.marginal_eq_and_twoTime_ne`, `GaussianFlowVsOU.hasDerivAt_klDiv_marginal_closedForm`; FL-5 instance: `NoiseScorePreconditioned.map_diagFlow_eq_diagLaw` | Special case, Verified (EX-1): one dimension, target $`\mathcal{N}(0, 1)`$, scalar preconditioner, with explicit flow map, closed-form KL dissipation, and the same one-time marginals as OU but different two-time laws; a diagonal preconditioner from $`\mathcal{N}(m, I)`$ to $`\mathcal{N}(0, I)`$ is an FL-5 instance with every hypothesis discharged. The SVGD velocities with linear and RBF kernels (Eqs. (11)–(12)) and general $`\Sigma_\star`$ are not formalised |
| Algorithm 1 (§3.1, Eq. (8)): parametric class, Monte Carlo inner objective on the particles, update $`x \mapsto x + \eta f_{\hat\theta}(x)`$ | identification, score | PT-1: `Particles.map_eulerStep_empirical`, `Particles.empirical_eulerParticles`, `Particles.weakContinuityEquation_empirical_flow` | PT-1 Verified: Euler steps push the empirical measure forward exactly, with the velocity as an input. Neural-network classes, the inner SGD loop, finite-particle and time-discretisation errors are not formalised |
| Discrete Gaussian case (App. A.6, Eqs. (33)–(35)): pushforward recursions, step size $`\eta \le \min_i h_i \sigma_i^2/2`$, mean and variance contraction, KL bound, and the case $`h_i = \sigma_i^{-2}`$, $`\eta = 1/2`$ | exact computation | EX-2: `DiscreteGaussianFlow.map_eulerMap_gaussianReal`, `DiscreteGaussianFlow.nextVar_eq_expanded`, `DiscreteGaussianFlow.popLaw_gaussianReal`, `DiscreteGaussianFlow.le_varSeq`, `DiscreteGaussianFlow.abs_meanSeq_sub`, `DiscreteGaussianFlow.relGap_varSeq_le`, `DiscreteGaussianFlow.klDiv_popLaw_le`, `DiscreteGaussianFlow.klDiv_popLaw_le_quarter`, `DiscreteGaussianFlow.map_flowEulerStep_diagonal` | Verified (EX-2), population dynamics with the exact linear velocity: KL bound in one dimension (for any $`s_0^2 \ge \sigma_\star^2`$), pushforward in the diagonal $`d`$-dimensional case; the $`d`$-dimensional KL bound of App. A.6 (with $`C_0`$ from Eq. (33)) is not formalised. The library also shows that the step-size threshold is sharp (`DiscreteGaussianFlow.exists_nextVar_lt_of_lt`) and gives the factor $`(1-\alpha)^2`$ (`DiscreteGaussianFlow.relGap_varSeq_le_sq`) |
| App. B.7: Euler discretisation of the full Wasserstein gradient versus the Forward-Flow discretisation (ULA); deterministic versus Langevin particles | exact computation, identification | EX-2: `DiscreteGaussianFlow.flow_exact_ula_biased`, `DiscreteGaussianFlow.popLaw_target`; CE-03; FL-5: `NoiseScore.map_flow_eq_of_klFlow`, `NoiseScore.map_flow_eq_of_preconditionedWeakFokkerPlanck` | EX-2 Verified: one population PFG Euler step fixes $`\mathcal{N}(0, 1)`$, one ULA step does not. FL-5 Conditional: preconditioned Langevin and the PFG transport have the same one-time marginals, given the weak Fokker–Planck equation and continuity-equation uniqueness (both discharged in the Gaussian instances `NoiseScorePreconditioned.map_diagFlow_eq_diagLaw` and `NoiseScorePreconditioned.nonscalar_example`) |

## Score-based Monte Carlo samplers

### rdMC: Huang–Dong–Hao–Ma–Zhang (2024)

Xunpeng Huang, Hanze Dong, Yifan Hao, Yi-An Ma, Tong Zhang. Reverse Diffusion Monte Carlo.
International Conference on Learning Representations (ICLR), 2024.
[arXiv:2307.02037](https://arxiv.org/abs/2307.02037) (v3, 13 March 2024).

**Algorithm.** Outer chain (Algorithm 1) on $`\mathbb{R}^d`$ from $`\tilde{p}_0 \approx p_T`$
($`\mathcal{N}(0, I)`$ for large $`T`$, or a ULA warm start, Algorithm 3): at step $`k`$, from
$`x`$, draw $`n`$ samples from an approximation $`q'_{T-k\eta}(\cdot \mid x)`$ of the posterior
```math
q_{T-k\eta}(x_0 \mid x) \propto \exp(-f_*(x_0) - \Vert x - e^{-(T-k\eta)} x_0 \Vert^2/(2(1 -
e^{-2(T-k\eta)})))
```
(inner ULA, Algorithm 2), set $`v_k`$ to the Monte Carlo estimate of Eq. (5) (twice the
posterior-mean score), and move to
$`\mathcal{N}(e^{\eta} x + (e^{\eta} - 1) v_k, (e^{2\eta} - 1) I)`$. In library terms the outer step
is a Gaussian reverse kernel with measurable mean and variance $`\beta/\alpha^2 = e^{2\eta} - 1`$
(`Diffusion.algKernel`), equivalently the Gaussian-increment kernel `GaussianIncrement.emKernelPi`
with step $`h = (e^{2\eta} - 1)/2`$ and drift $`(e^{\eta} - 1)(x + v_k)/h`$; re-estimating $`v_k`$
from fresh draws at every step is the random-oracle kernel `GaussianIncrement.randomEmKernel` with
draw kernel $`R_k(x) = q'_k(\cdot \mid x)^{\otimes n}`$ (`KernelPi.piConst`).

**Main result.** Lemma 1 (§3.1, Eq. (4); proof in App. C.1): for the OU forward process of Eq. (1),
```math
\nabla \ln p_{T-t}(x) = \mathbb{E}_{x_0 \sim q_{T-t}(\cdot \mid x)}[(e^{-(T-t)} x_0 - x)/(1 -
e^{-2(T-t)})].
```
Theorem 1 (§4.1): under [A1] (every $`\nabla \ln p_t`$ is $`L`$-Lipschitz), [A2] (second moment
$`m_2^2`$), an LSI with constant $`\mu_k`$ for each $`q_{T-k\eta}`$ and
$`\mathrm{KL}(p_T \Vert \tilde{p}_0) \lt \epsilon`$, with $`\eta = C_1 (d + m_2^2)^{-1} \epsilon^2`$
and the sample sizes $`n_k`$ and inner KL tolerances $`E_k`$ of Eq. (6), Algorithm 1 reaches TV
error $`\tilde{O}(\epsilon)`$ with probability at least $`1 - \delta`$. Lemmas 2–3 bound the LSI
constants of $`q_t`$; Propositions 1–2 give gradient complexities under [A3] (strong convexity
outside a ball) and [A4] (tails growing slower than quadratically).

| Step | Move | Library | Status |
|---|---|---|---|
| OU posterior score identity (Lemma 1, Eq. (4)), and its ratio form, the identity behind the importance-weighted estimator of §3.3 | score | SE-3: `OUPosterior.ouPosteriorScore` (1D), `OUPosterior.ouPosteriorScore_pi` (`Fin d → ℝ`), `OUPosterior.ouPosteriorScore_density` and `OUPosterior.ouPosteriorScore_ratio` (1D), all corollaries of `Tweedie.tweedie` | Verified (SE-3). Formalises Lemma 1 in forward time $`s = T - t \gt 0`$ for every law of $`X_0`$ (no density or moment assumption); the library states $`s \gt 0`$ explicitly. The density and unnormalised-ratio forms are 1D only. The forward OU marginal is defined as the Gaussian kernel, not derived from Eq. (1). The importance-weighted estimator and its sample complexity are not formalised |
| Monte Carlo score estimate from exact posterior draws (Eq. (5)): mean and mean-square error | score | SE-4: `MonteCarlo.integral_scoreEstimate`, `MonteCarlo.integral_sq_scoreEstimate_sub`, `MonteCarlo.meas_abs_scoreEstimate_sub_ge_le`; vector sample mean `MonteCarlo.integral_dotProduct_vecSampleMean_sub` | Verified (SE-4). Proves a version: in 1D the estimate $`(a \bar{x} - y)/\sigma^2`$ (half of rdMC's $`v_k`$) has mean $`(am - y)/\sigma^2`$, mean-square error $`a^2 v/(n \sigma^4)`$ and a Chebyshev tail, for pairwise independent exact draws; in $`d`$ dimensions the mean-square error of the sample mean is the trace of the covariance over $`n`$. The high-probability bound of Lemma 8 is not formalised |
| Score error split into Monte Carlo deviation (Term 2.1) and inner-sampler bias (Term 2.2), Eq. (17); bias bounded by Jensen over a coupling and then by the inner KL error, Eq. (18) | score | GI-2: `GaussianIncrement.integral_sq_empMean_sub_biased` ($`\mathbb{E}\Vert \hat{m} - m \Vert^2 = \Vert \mathrm{bias} \Vert^2 + V/N`$), `InnerSamplerAveraged.sum_sq_bias_le_of_coupling` (Jensen over a coupling), `InnerSamplerBias.sum_sq_bias_le` ($`\Vert \mathrm{bias} \Vert^2 \le 2\sigma^2 \, \mathrm{KL}(\text{inner} \Vert \text{exact})`$ for a $`\sigma^2`$-sub-Gaussian exact posterior) | Verified (GI-2). Proves an in-expectation counterpart: an exact bias–variance identity, and a transport inequality from sub-Gaussianity of the exact posterior, which is assumed as a hypothesis. The high-probability bound, and deriving the transport inequality from an LSI of the exact posterior (Talagrand's inequality), are not formalised |
| Propagation of the per-step score error to the output law: Girsanov on path space (Lemma 12, Corollary 2) and Pinsker (Eqs. (15), (19)) | error accumulation, comparison | KL-1, KL-2, GI-1, GI-2: `KL.klDiv_chain_le_sum`, `Pinsker.tvSup_le_sqrt_klDiv`, `GaussianIncrement.klDiv_randomEmKernel_le`, `GaussianIncrement.tvSup_biasedMonteCarloChain_le_sqrt`, `InnerSamplerBias.tvSup_biasedMonteCarloChain_le_sqrt_of_klDiv`, `InnerSamplerAveraged.tvSup_biasedMonteCarloChain_le_sqrt_of_lintegral_klDiv_le` | Verified (KL-1, KL-2, GI-1, GI-2). Proves a discrete-time version: the KL chain rule along Markov kernels replaces Girsanov, and the one-step KL $`h \Vert \Delta b \Vert^2/4`$ of two Gaussian steps replaces the frozen-drift Girsanov integrand. GI-2 compares the chain driven by Monte Carlo scores from an inexact inner sampler with the same chain driven by exact scores: `tvSup` $`\le \sqrt{\mathrm{KL}_0/2 + \sum_k (h_k c_k^2/8)(2\sigma_k^2 \delta_k + \int V_k \, d\nu_k/N)}`$, errors averaged under the algorithm's laws. Continuous-time Girsanov is not formalised |
| Discretisation error of the reverse process (Lemma 7, under [A1]) | differentiation | DF-1, DF-5: `Diffusion.klDiv_output_le`, `DiffusionPath.klDiv_truePath_algPath`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le` | Related statement (Verified, DF-1, DF-5). For any Gaussian reverse kernel with measurable mean $`m_k`$, `Diffusion.klDiv_output_le` splits $`\mathrm{KL}(p_{t_1} \Vert q_1)`$ (output at the early-stopping time $`t_1 \gt 0`$) into initialisation, the per-step KL to $`\mathcal{N}(m^*_k(y), \sigma_k^2 I)`$ with $`m^*_k`$ the posterior mean, and $`\int \Vert m^*_k - m_k \Vert^2/(2\sigma_k^2) \, dp_k`$; with $`\sigma_k^2 = e^{2\eta} - 1`$ (rdMC's step variance) the discretisation sum is at most $`(\kappa d/2)(1 + \log(u_N/u_1))`$ by heat-flow entropy increments, with no Lipschitz assumption. The posterior mean $`m^*_k = e^{\eta} y + (e^{\eta} - e^{-\eta}) \nabla \log p_k(y)`$ has score coefficient $`e^{\eta} - e^{-\eta}`$ and rdMC's step uses $`2(e^{\eta} - 1)`$; the resulting mean difference is not bounded in the library. Lemma 7 itself is not formalised |
| Initialisation error: OU convergence of $`p_T`$ to $`\mathcal{N}(0, I)`$ (Lemma 21; Term 1 of Eq. (19)) | contraction | FL-4: `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`; DF-1 explicit initialisation term: `Diffusion.klDiv_output_le_explicit` | FL-4 is a Conditional row; the OU decay used here is proved with no named hypothesis: $`\mathrm{KL}(p_T \Vert \mathcal{N}(0, I)) \le e^{-2T} \mathrm{KL}(p_0 \Vert \mathcal{N}(0, I))`$ for $`p_0`$ with finite KL and second moment; Lemma 21 itself is not formalised. DF-1 (Verified) gives an explicit initialisation term from the second moment for the smoothed data $`p_{t_1}`$. The ULA initialisation of Algorithm 3 is not formalised |
| LSI constants of $`q_t`$ and $`p_T`$ (Lemmas 2–3, via Lemma 6 (Ma et al. 2019) and Lemma 16 (LSI of convolutions)) | contraction | KL-6 components: Bakry–Émery `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn`, Holley–Stroock `GaussianFunctionalLSIPi.functionalLSIPi_tilt`, LSI under convolution `LogSobolevTensorPi.functionalLSIPi_map_add` | Components Verified (KL-6); Lemmas 2–3 themselves are not formalised |
| Inner ULA convergence to $`q_{T-k\eta}(\cdot \mid x)`$ under LSI (Algorithm 2, Lemmas 9–10, Lemma 19 after Vempala–Wibisono) and the complexity counts (Theorem 1, Propositions 1–2) | contraction | not formalised | Not formalised; the inner sampler enters GI-2 only through a KL budget $`\delta_k`$ or a coupling cost |

### RS-DMC: Huang–Zou–Dong–Ma–Zhang (2024)

Xunpeng Huang, Difan Zou, Hanze Dong, Yi-An Ma, Tong Zhang. Faster Sampling without Isoperimetry via
Diffusion-based Monte Carlo. Conference on Learning Theory (COLT), 2024, PMLR 247:2438–2493.
[arXiv:2401.06325](https://arxiv.org/abs/2401.06325) (v1, 12 January 2024).

**Algorithm.** Algorithm 2: from $`\mathcal{N}(0, I)`$, run the reverse OU process in $`K`$ segments
of length $`S = \tfrac12 \log(1 + 1/(2L))`$ with steps
$`x \mapsto \mathcal{N}(e^{\eta} x + (e^{\eta} - 1) v', (e^{2\eta} - 1) I)`$, where $`v'`$ is
returned by recursive score estimation (Algorithm 1, RSE): the empirical posterior-mean score over
$`n_{k,r}`$ inner ULA chains targeting
```math
q_{k,S-r\eta}(x' \mid x) \propto p_{k,0}(x') \exp(-\Vert x - e^{-(S-r\eta)} x' \Vert^2/(2(1 -
e^{-2(S-r\eta)}))),
```
whose drift needs $`\nabla \log p_{k,0} = \nabla \log p_{k-1,S}`$, estimated by a recursive call of
RSE (down to $`-\nabla f_*`$). In library terms the outer step is `Diffusion.algKernel` with
variance $`\beta/\alpha^2`$ (equivalently `GaussianIncrement.emKernelPi` with
$`h = (e^{2\eta} - 1)/2`$), and one RSE call with given inner drift is the random oracle
`GaussianIncrement.randomEmKernel`; the nested recursion has no library counterpart.

**Main result.** Theorem 4.1 (PMLR Theorem 2; formal version Theorem B.1, PMLR Theorem 5): under
[A1] (every segment score $`\nabla \log p_{k,t}`$ is $`L`$-Lipschitz) and [A2] (second moment
$`M`$), with suitable $`n_{k,r}, m_{k,r}, \tau_r, \eta, l_{k,r}, l`$, the output law satisfies
$`\mathrm{KL}(p_* \Vert p^{\leftarrow}_{0,S}) = \tilde{O}(\epsilon)`$ with probability at least
$`1 - \epsilon`$, at gradient complexity
$`\exp(O(L^3 \log^3((Ld + M)/\epsilon) \max\{\log\log Z^2, 1\}))`$, quasi-polynomial in
$`1/\epsilon`$. Lemma 2.1 (PMLR Lemma 1, which is rdMC Lemma 1) and Lemma E.1 (PMLR Lemma 14) write
each segment score as a posterior expectation.

| Step | Move | Library | Status |
|---|---|---|---|
| Segment score identity (Lemma 2.1, Lemma E.1) with prior $`p_{k,0}`$ and time gap $`S - t`$ | score | SE-3: `ScorePropagation.score1_ouDensity_tweedie` (1D, prior density, gap $`\tau \gt 0`$), `OUPosterior.ouPosteriorScore_pi` (`Fin d → ℝ`, any prior law); the related identity $`\nabla \log p_t(y) = e^{t-s} \mathbb{E}[\nabla \log p_s(X_s) \mid X_t = y]`$, which Algorithm 1 does not use, is `ScorePropagation.score1_ouDensity` (1D) | Verified (SE-3). Formalises the identity for a positive time gap, stated explicitly (1D with a prior density; `Fin d → ℝ` for any prior law) |
| Strong log-concavity of the inner targets for $`S \le \tfrac12 \log(1 + 1/(2L))`$ (Eq. (4), Lemma E.2) and LSI from strong log-concavity (Lemma F.8) | contraction | KL-6: `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn` ($`f - \alpha \Vert x \Vert^2/2`$ convex gives the LSI with constant $`1/\alpha`$) | Component Verified (KL-6); the Hessian bound of Lemma E.2 is not formalised |
| Inner ULA with an estimated drift: one-step KL recursion and convergence to the posterior (Lemma E.4, Corollary E.6) | error accumulation, contraction | GI-1: `GaussianIncrement.klDiv_emChainPi_le_sum` (cost of a drift error between two Gaussian-increment chains) | Related statement (Verified, GI-1): the KL between the chains with estimated and exact drift, not contraction of ULA toward its target; Lemma E.4 and Corollary E.6 are not formalised |
| Score-estimate error of one call (Lemma E.7): Monte Carlo deviation (Term 3.1, Lemma E.3, high probability from the LSI of the inner output law) and inner-sampler bias (Term 3.2, through $`\mathrm{KL}(q' \Vert q)`$) | score | SE-4: `MonteCarlo.integral_sq_scoreEstimate_sub`, `MonteCarlo.meas_abs_scoreEstimate_sub_ge_le`; GI-2: `GaussianIncrement.integral_sq_empMean_sub_biased`, `InnerSamplerBias.sum_sq_bias_le`, `InnerSamplerAveraged.sum_sq_bias_le_of_coupling` | Verified (SE-4, GI-2) for the in-expectation counterpart with independent draws (Chebyshev tail in 1D); sub-Gaussianity of the exact posterior is assumed as a hypothesis, and concentration from an LSI is not formalised |
| Recursive estimation and its error propagation across segments (Algorithm 1, Lemma E.8, Corollary E.9, Lemma E.10) | score | not formalised (the `ScorePropagation` module states that nested estimators are outside its scope) | Not formalised |
| Output decomposition (§4.2): $`\mathrm{KL}(p_* \Vert p^{\leftarrow}_{0,S})`$ bounded by initialisation (Term 1), discretisation (Term 2) and score error (Term 3), via Girsanov (Lemmas F.1–F.3) | error accumulation | DF-1, DF-5, KL-2: `Diffusion.klDiv_output_le_chain`, `Diffusion.klDiv_output_le`, `DiffusionPath.klDiv_truePath_algPath`, `KL.klDiv_chain_le_sum` | Discrete-time version (Verified, DF-1, DF-5): for any data law with finite second moment and Gaussian reverse kernels with any variances and measurable means, $`\mathrm{KL}(p_{t_1} \Vert q_1) \le \mathrm{KL}(p_T \Vert \mathcal{N}(0, I))`$ plus discretisation plus mean error, with the data law first and errors under the true marginals as in RS-DMC; output at the early-stopping time $`t_1 \gt 0`$; continuous-time Girsanov is not formalised |
| Initialisation term (Term 1, Lemma C.3): OU convergence of $`p_T`$ to $`\mathcal{N}(0, I)`$ | contraction | FL-4: `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`; DF-1: `Diffusion.klDiv_output_le_explicit` | FL-4 is a Conditional row; this OU decay is proved with no named hypothesis ($`\mathrm{KL}(p_T \Vert \mathcal{N}(0, I)) \le e^{-2T} \mathrm{KL}(p_0 \Vert \mathcal{N}(0, I))`$), a related statement to Lemma C.3; the bound of the initial KL by $`Ld + M`$ is not formalised; DF-1 (Verified) gives an explicit initialisation term from the second moment for the smoothed data |
| Discretisation term (Term 2, Lemma D.4, after Chen et al. 2023) | differentiation | DF-1: `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le`, `DiffusionDiscretization.klDiv_output_le_ddpm_grid` | Related statement (Verified, DF-1): with reverse variance $`\beta/\alpha^2 = e^{2\eta} - 1`$ (the variance of RS-DMC's step) the per-step discretisation sum is at most $`(\kappa d/2)(1 + \log(u_N/u_1))`$ by heat-flow entropy increments, with no Lipschitz assumption; Lemma D.4 (continuous time, under [A1]) is not formalised |

### SPS: Huang–Zou–Dong–Ma–Zhang (2024)

Xunpeng Huang, Difan Zou, Hanze Dong, Yi-An Ma, Tong Zhang. Faster Sampling via Stochastic Gradient
Proximal Sampler. International Conference on Machine Learning (ICML), 2024, PMLR 235:20559–20596.
[arXiv:2405.16734](https://arxiv.org/abs/2405.16734) (v1, 27 May 2024; the arXiv version lists the
authors in the order Huang, Zou, Ma, Dong, Zhang).

**Algorithm.** Algorithm 1: from $`\hat{x}_0 \sim \mathcal{N}(0, I)`$, alternate the exact forward
step $`x_{k+1/2} \sim \mathcal{N}(x_k, \eta_k I)`$ and, for a random mini-batch $`b_k`$, an
approximate sample from the mini-batch RGO
$`p_{k+1 \mid k+1/2, b}(x' \mid x) \propto \exp(-f_b(x') - \Vert x' - x \Vert^2/(2\eta_k))`$ with
$`\mathrm{KL}(\hat{p} \Vert p) \le \delta_k`$ (Eq. (7)), produced by inner SGLD (Algorithm 2,
SPS-SGLD) or warm-started MALA (Algorithms 3–4, SPS-MALA). In library terms: the exact proximal
kernel `Proximal.proxKernel` / `ProximalPi.proxKernelPi` (forward Gaussian step, then
`Proximal.rgoKernel`), with the RGO replaced by an inexact Markov kernel $`R'_k`$
(`ErrorDecomposition.tvSup_inexactProx_le_along`); the mini-batch is not modelled.

**Main result.** Theorem 3.1: under [A1] (each $`\nabla f_i`$ is $`L`$-Lipschitz), [A2] (LSI with
constant $`\alpha_*`$), [A3] (gradient variance at most $`\sigma^2`$), $`\eta_k \le 1/(2L)`$,
$`\hat{x}_0 \sim \mathcal{N}(0, I)`$ and inner accuracy $`\delta_k`$,
```math
\mathrm{TV}(\hat{p}_K, p_*) \le \sqrt{\tfrac12 \sum_{i \lt K} \delta_i} + \sigma \sqrt{\sum_{i \lt
K} \eta_i/(2\lvert b_i \rvert)} + \sqrt{(1 + L^2)d/(4\alpha_*)} \prod_{i \lt K} (1 + \alpha_*
\eta_i)^{-1}
```
(Eq. (8)). Lemma 3.2 bounds the second moments along the chain. Theorems 4.1 and 4.2: SPS-SGLD and
SPS-MALA reach TV error $`3\epsilon`$ with expected gradient complexity
$`\tilde{\Theta}(\kappa^3 (d + \sigma^2) \epsilon^{-2})`$ and
$`\tilde{\Theta}(\kappa^3 d^{1/2} \sigma^2 \epsilon^{-2})`$, where $`\kappa = L/\alpha_*`$.

| Step | Move | Library | Status |
|---|---|---|---|
| Exact parent kernel: forward Gaussian step and restricted Gaussian oracle; the RGO is the Bayes reverse kernel of the forward step and the target is invariant (Eqs. (4)–(6)) | identification | PX-1: `Proximal.isReverseKernel_rgoKernel`, `Proximal.proxKernel_comp_target`, `ProximalPi.isReverseKernel_rgoKernelPi`, `ProximalPi.proxKernelPi_comp_targetPi` | Verified (PX-1) for a fixed potential, 1D and `Fin d → ℝ`; for a fixed mini-batch it applies with $`f = f_b`$; the kernel with a random mini-batch is not formalised |
| KL chain rule and data processing (Lemma B.1) | comparison | KL-2: `KL.klDiv_compProd_eq_add_lintegral`, `KL.klDiv_comp_le_compProd`, `KL.klDiv_comp_comp_le` | Verified (KL-2) |
| Inner-sampler error (Lemma B.5): $`\mathrm{KL}(\hat{p}_{k+1} \Vert p_{k+1}) \le \mathrm{KL}(\hat{p}_k \Vert p_k) + \delta_k`$, hence $`\mathrm{TV}(\hat{p}_K, p_K) \le \sqrt{\tfrac12 \sum_k \delta_k}`$ with one Pinsker step | error accumulation | KL-1, KL-2: `KL.klDiv_chain_le_sum`, `ErrorPropagation.tvSup_chain_le_sqrt_klDiv_add_sum` | Verified (KL-1, KL-2). Proves the generic statement for Markov kernels, with per-step KL errors averaged under the inexact chain's laws (implied by the uniform condition (7)); not instantiated with the SPS kernels in Lean |
| TV variant of the outer framework: per-step TV oracle errors and a TV contraction of the exact step along the algorithm's laws | error accumulation | `ErrorDecomposition.tvSup_le_of_contraction_along`, `ErrorDecomposition.tvSup_inexactProx_le_along`, `ErrorDecomposition.tvSup_inexactProx_le` (1D proximal instance); CE-07: `ErrorDecomposition.not_tvContraction_resetKernel` | Conditional on the named hypothesis `hAlong`; these declarations have no registry row of their own (CE-07, Counterexample: contraction along a chain does not give a uniform TV contraction). A TV analogue of the KL route of the paper; with contraction factor $`1`$ the hypothesis holds by PX-1 and the bound is additive |
| Mini-batch error (Lemmas B.3–B.4, E.1): KL between the mini-batch and full-batch RGO from the LSI of the strongly log-concave RGO (Lemmas B.2, E.2), and $`\mathbb{E}_b \Vert \nabla f_b - \nabla f \Vert^2 \le \sigma^2/\lvert b \rvert`$ | contraction, score | components: KL-6 `BakryEmeryGeneralPi.functionalLSIPi_targetPi_of_convexOn` (LSI of a strongly log-concave law); SE-4 `MonteCarlo.integral_dotProduct_vecSampleMean_sub` (mean-square error of the sample mean of pairwise independent vectors, which covers Lemma E.1 when the mini-batch indices are drawn independently) | Not formalised as a step (components Verified: KL-6, SE-4) |
| Exact proximal sampler contraction under LSI (Lemma E.3, Theorem 3 of Chen–Chewi–Salim–Wibisono 2022), giving the last term of Eq. (8) (Lemma B.6) | contraction | PX-2: `ProximalGeneralLSIPi.toReal_klDiv_proxKernelPi_comp_le_sq_general`, `ProximalGeneralLSIPi.toReal_klDiv_iteratePi_le_sq_general`, `ProximalGeneralLSIPi.tvSupPi_iterate_le_sq_general`; PX-6: `ProximalStronglyLogConcaveGeneralPi.toReal_klDiv_iteratePi_le_sq_of_stronglyLogConcave`; PX-4: `ProximalSharpPerturbedPi.toReal_klDiv_iteratePi_le_sq_perturbed_of_ne_top` | Conditional (PX-2): $`\mathrm{KL}(\rho P \Vert \pi) \le \mathrm{KL}(\rho \Vert \pi)/(1 + \alpha\eta)^2`$ for every $`\eta \gt 0`$ and every start with finite KL, and iterates at a constant step, with the functional LSI of $`\pi`$ a named hypothesis and a Gaussian upper envelope $`\pi \le C \cdot \mathcal{N}(0, vI)`$ stated explicitly; Verified with no further hypothesis for strongly log-concave targets (PX-6) and bounded perturbations of Gaussians (PX-4) |
| Initial KL from $`\mathcal{N}(0, I)`$ under LSI and smoothness (Lemma E.4), and the triangle inequality across the inexact, mini-batch and exact chains (proof of Theorem 3.1) | error accumulation | KR-1: `ErrorDecomposition.tvSup_le_three_chain` (three-chain TV separation with per-step TV errors); Lemma E.4 not formalised | Related statement (Verified, KR-1) for the three-chain split; Lemma E.4 and Theorem 3.1 are not formalised |
| Inner samplers on strongly log-concave targets: SGLD with trajectory averaging (Algorithm 2, Lemmas C.1–C.3, Theorem 4.1) and MALA warm-started by ULD (Algorithms 3–4, Lemma C.6, Theorem 4.2); second moments along the chain (Lemma 3.2) | contraction | MH-1: `MALA.invariant_malaKernelPi` (invariance of MALA only) | Not formalised (MH-1, Verified, is a component; the inner accuracy enters the library only as a per-step KL or TV budget) |

### RTK: Huang–Zou–Dong–Zhang–Ma–Zhang (2024)

Xunpeng Huang, Difan Zou, Hanze Dong, Yi Zhang, Yi-An Ma, Tong Zhang. Reverse Transition Kernel: A
Flexible Framework to Accelerate Diffusion Inference. Advances in Neural Information Processing
Systems 37 (NeurIPS 2024). [arXiv:2405.16387](https://arxiv.org/abs/2405.16387) (v1, 26 May 2024).

**Algorithm.** Algorithm 1: from $`\hat{x}_0 \sim \mathcal{N}(0, I)`$, for $`k = 0, \ldots, K-1`$
draw $`\hat{x}_{(k+1)\eta}`$ by an inner MCMC run targeting the reverse transition kernel
```math
p^{\leftarrow}_{(k+1)\eta \mid k\eta}(z \mid x) \propto \exp(-f_{(K-k-1)\eta}(z) - \Vert x -
e^{-\eta} z \Vert^2/(2(1 - e^{-2\eta})))
```
(Eq. (8)), with a learned score $`s_\theta`$ in place of $`\nabla f_t`$: MALA (Algorithm 2,
RTK-MALA) or underdamped Langevin (Algorithm 3, RTK-ULD), with $`\eta = \tfrac12 \log(1 + 1/(2L))`$.
In library terms: a Markov chain whose exact kernels are the Bayes posteriors of the OU forward step
(`Diffusion.revKernel`, `Kernels/ReverseKernel`), run with inexact Markov kernels; DDPM is the case
of the Gaussian kernel $`\mathcal{N}(e^{\eta} x + 2(e^{\eta} - 1) s_\theta(x), (e^{2\eta} - 1) I)`$
(Eq. (6); `Diffusion.algKernel`).

**Main result.** Lemma 3.1: closed form of the reverse transition kernel of the OU process by Bayes'
rule. Lemma 3.2:
```math
\mathrm{TV}(\hat{p}_{K\eta}, p_*) \le \sqrt{(1 + L^2)d + \Vert \nabla f_*(0) \Vert^2} \, e^{-K\eta}
+ \sqrt{\tfrac12 \sum_{k \lt K} \mathbb{E}_{\hat{x} \sim \hat{p}_{k\eta}}
\mathrm{KL}(\hat{p}_{(k+1)\eta \mid k\eta}(\cdot \mid \hat{x}) \Vert p^{\leftarrow}_{(k+1)\eta \mid
k\eta}(\cdot \mid \hat{x}))},
```
from the KL chain rule (Eq. (7)). Theorem 4.1 (informal version of Theorem C.17) and Corollary 4.2
(Corollary C.19): RTK-MALA reaches TV error $`\tilde{O}(\epsilon)`$ with
$`O(L^4 d^2 \log(d/\epsilon))`$ score calls (Table 1) under score [E1] and energy-difference [E2]
accuracy; Corollary 4.3: score-only RTK-MALA; Theorem 4.4: RTK-ULD with
$`\tilde{O}(L^2 d^{1/2} \epsilon^{-1})`$ score calls under [A1], [A2], [E3].

| Step | Move | Library | Status |
|---|---|---|---|
| Reverse transition kernel in closed form (Lemma 3.1, Bayes' rule), and the exact reverse chain from $`p_T`$ reproducing the forward marginals | identification | KR-2: `ReverseKernel.isReverseKernel_posterior`, `ReverseKernel.joint_density_eq_mul_reverseDensity`, `ReverseKernel.reverseChain_comp_forwardMarginal`; OU instance: `Diffusion.revKernel_comp_fwdLaw`, `DiffusionPath.fwdPath_eq_truePath`; Gaussian forward step $`\mathcal{N}(x, \eta)`$: `Proximal.reverseDensity_eq_rgoDensity` (PX-1) | Verified (KR-2, PX-1). Formalises Lemma 3.1 as a statement about Mathlib's posterior of the OU forward step for any data law (reverse kernel, marginal recovery, reverse-path law equal to the forward-path law), with the density form $`p(x) k(x, y)/m(y)`$ for a generic forward density; the explicit Gibbs density is written out for the forward step $`\mathcal{N}(x, \eta)`$ (the restricted Gaussian oracle) |
| KL chain rule (Lemma B.4) and the error decomposition of Lemma 3.2: per-step $`\mathrm{KL}(\text{inexact} \Vert \text{exact})`$ averaged under the algorithm's laws, then one Pinsker step | comparison, error accumulation | KL-1, KL-2: `KL.klDiv_compProd_eq_add_lintegral`, `KL.klDiv_chain_le_sum`, `ErrorPropagation.tvSup_chain_le_sqrt_klDiv_add_sum`, `Pinsker.tvSup_le_sqrt_klDiv` | Verified (KL-1, KL-2). Formalises the chain-rule part of Lemma 3.2 for Markov kernels on any countably generated space: `tvSup` $`\le \sqrt{(\mathrm{KL}(\nu_0 \Vert \mu_0) + \sum_k c_k)/2}`$ when $`\int \mathrm{KL}(\hat{P}_k(x) \Vert P_k(x)) \, d\nu_k \le c_k`$, with the same divergence direction and averaging law; with the Bayes reverse kernels as exact kernels the exact chain's laws are the forward marginals (KR-2) |
| TV chain rule variant (Lemmas B.1–B.2, Corollary B.3): per-step TV errors averaged under the algorithm's laws | error accumulation | KR-1: `ErrorPropagation.tvSup_chain_le_sum_integral_approx` | Verified (KR-1); formalises the telescoped TV bound |
| Initialisation term: OU convergence to $`\mathcal{N}(0, I)`$ (Lemma E.1 with the LSI of $`\mathcal{N}(0, I)`$) and the bound on the initial KL (Lemma E.2) | contraction | FL-4: `OULangevinDecayPi.toReal_klDiv_ouKernelVarPi_comp_le`; KL-5 (Gaussian LSI) | FL-4 is a Conditional row; the OU decay $`\mathrm{KL}(p_T \Vert \mathcal{N}(0, I)) \le e^{-2T} \mathrm{KL}(p_0 \Vert \mathcal{N}(0, I))`$ used in the proof of Lemma B.2 is proved with no named hypothesis; Lemma E.2 is not formalised |
| DDPM as the Gaussian special case (Eqs. (6)–(7)) | error accumulation | DF-1, DF-5: `DiffusionPath.klDiv_truePath_algPath`, `Diffusion.klDiv_output_le`, `DiffusionDiscretization.sum_lintegral_klDiv_revKernel_ddpm_le` | Verified (DF-1, DF-5). The library's diffusion results put the true reverse path first ($`\mathrm{KL}(\text{true} \Vert \text{sampler})`$, errors under the true marginals), the reverse of the direction of Eq. (7), which is the generic KL-2 statement above; the discretisation bound of DF-1 holds for variance $`e^{2\eta} - 1`$ and any mean map, and its score-error form is stated for the mean $`(y + \beta s)/\alpha`$ |
| Strong log-concavity and $`3L`$-smoothness of the kernel targets for $`\eta = \tfrac12 \log(1 + 1/(2L))`$ (§3) | contraction | not formalised | Not formalised |
| Inner MALA (Algorithm 2): convergence through the Cheeger constant of the truncated target, projected variant, estimated score [E1] and energy difference [E2] (Theorem 4.1 / C.17, Corollaries 4.2–4.3) | contraction, identification | MH-1: `MH.detailed_balance`, `MH.invariant_mhKernel`, `MALA.invariant_malaKernelPi` | Component Verified (MH-1): with the exact acceptance ratio the Metropolis–Hastings kernel leaves its target invariant for any normalised proposal; mixing bounds, the projection and the estimated energy difference [E2] are not formalised |
| Inner underdamped Langevin (Algorithm 3, Theorem 4.4) | contraction | not formalised | Not formalised |
