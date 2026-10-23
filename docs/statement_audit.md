# Statement audit

A proof checker certifies that a proof matches its statement, not that the statement says what
its docstring and the registry claim. The statement audit checks the statements themselves for
every row of [`theorem_registry.md`](theorem_registry.md). It asks four questions:

1. **Non-vacuity.** Can the hypotheses be satisfied by a non-degenerate instance? For every registry
   row, theorems of the row, or library corollaries whose proofs apply them, are applied in Lean to
   explicit instances with every hypothesis discharged (for example non-Gaussian and non-log-concave
   targets where the row claims that generality, $`d \ge 1`$, $`\eta \gt 0`$,
   $`\mathrm{KL}(\rho_0 \Vert \pi) \gt 0`$, non-stationary flows). The guarantee is per row, not per
   declaration: some cited declarations are exercised only through the theorems that use them, and a
   few only on stationary instances.
2. **Encoding.** Are there junk-value effects? Examples are `(klDiv …).toReal` with
   $`\mathrm{KL} = \top`$, Bochner integrals of non-integrable functions, TV normalisation, the sup
   norm on `Fin d → ℝ` against Euclidean squares, variance against standard deviation, and
   hypotheses that restate the conclusion.
3. **Fidelity.** How does the statement compare with the literature result it formalises?
   Where the hypotheses or conclusions differ from the source, the difference is stated in the
   registry row.
4. **Documentation.** Do the docstrings and registry text describe the Lean statement
   accurately?

## Witness modules

The witnesses are Lean code under `FormalizeSampling/Audit/`: they are built and axiom-audited
with the rest of the library. Each module applies theorems of its rows to concrete instances,
discharges every hypothesis and, where cheap, shows that the conclusion is not a junk value.
Its module docstring lists the witnesses and the main gaps, such as cited declarations without
a witness of their own or with only stationary ones.

The [declaration index](declaration_index.md#audit) lists the witness modules with the registry
rows each one covers, generated from the title and the `Rows:` line of each module docstring;
`scripts/AxiomAudit.lean` checks that every module uses, directly or through library theorems, a
declaration cited by each of its rows.

## Method

For each registry row the audit checks the witnesses, the encoding pitfalls below, the
comparison with the literature, and whether the docstrings and registry text match the Lean
statements. Every row has a witness on an explicit instance; the witnesses are Lean code, while
the other three checks are a reading of the statements, not a kernel guarantee.

### Encoding checks

- Every TV bound obtained through `klDiv(…).toReal` assumes $`\mathrm{KL} \ne \top`$, or finiteness
  of the whole error budget. Where a bound is stated on `heatKL = (klDiv …).toReal`, companion
  $`\ne \top`$ lemmas state that the KL is finite.
- TV is $`\sup_A \lvert \mu(A) - \nu(A) \rvert`$ and Pinsker is applied as $`\sqrt{\mathrm{KL}/2}`$.
- Squared distances on `Fin d → ℝ` are Euclidean ($`\sum_i x_i^2`$, `⬝ᵥ`), not the sup norm.
- `gaussianReal m v` and the proximal $`\eta`$ are variances.
- No hypothesis restates its conclusion. The named PX-2 backward hypotheses
  `BackwardHeatFlowDissipation`/`BackwardHeatFlowLSI` are equivalent to the backward
  contraction (`ProximalSharpLSI.exists_backwardHeatFlow_of_le`); they are derived from the
  concrete `BackwardHeatFlowRegular`, and the final PX-2 forms do not use them.
- $`d = 0`$ is allowed in the `Fin d → ℝ` statements and is harmless there. Every witness uses
  $`d \ge 1`$.

### Scope relative to the literature

Differences from the literature are stated in the registry rows. The main ones:

- **Proximal sampler.** The general LSI case assumes a Gaussian upper envelope in addition to the
  LSI, compared with Chen–Chewi–Salim–Wibisono (2022). The log-concave $`1/k`$ rate (PX-5) has
  constant $`W^2/(2k\eta)`$ rather than their $`W^2/(k\eta)`$; this is the constant that the
  shifted-composition argument of Altschuler–Chewi (2023) gives, stated for $`C^2`$ potentials by
  Pedrotti (2026, Cor. 3.5), and PX-5 proves it for every finite convex $`f`$. PX-4 uses the
  pointwise oscillation of $`W`$ rather than its essential oscillation; the rate
  $`(1 + \alpha' \eta)^{-2}`$ is proved with the squared exponent (attained for constant $`W`$), and
  the Holley–Stroock constant $`\alpha' = \alpha e^{-\mathrm{osc}\,W}`$ is not optimal in general.
- **KL-6.** Functional LSIs are stated on a smooth bounded test class and extended to positive
  $`C^1`$ test functions with the needed integrability. The KL/Fisher bridge
  `heatKL_le_of_functionalLSI_of_integrable` needs $`C \ge 0`$ and integrable KL and Fisher
  integrands at time $`t`$, not bounds on $`p_t/q_t`$.
- **ID-1.** The $`d`$-dimensional Stein identity is stated for $`\mathcal{N}(0, I_d)`$ and $`C^1_c`$
  test functions.
- **Moment hypotheses.** The PX-3 and PX-4 rates need no moment hypothesis, only
  $`\mathrm{KL}(\rho_0 \Vert \pi) \lt \infty`$.
- **GI-2.** The Monte Carlo bounds use the product of finitely many kernels
  (`Kernels/KernelPi`, `KernelPi.pi`, `piConst`) and hold for state-dependent posteriors, end
  to end for $`\mathrm{post}_k(x) = \mathcal{N}(x, t_k I)`$ (`Samplers/RandomScoreOracleKernel`).
- **FL-5.** DiPerna–Lions is proved for autonomous velocities and probability-density
  solutions. This is weaker than DiPerna–Lions (1989), Thm II.2, which allows time-dependent
  $`v`$, signed solutions and growth in $`L^1 + L^\infty`$.
- **Fokker–Planck uniqueness.** It is proved for bounded continuous drifts, for $`-a x`$ plus a
  bounded drift, and for jointly continuous drifts globally Lipschitz in $`x`$ uniformly on each
  $`[0, T]`$ (FL-6). Uniqueness for dissipative drifts that are not globally Lipschitz (quartic or
  double-well Langevin) is classical under $`\langle b(t, x), x \rangle \le C + C \Vert x \Vert^2`$
  (Bogachev–Krylov–Röckner–Shaposhnikov 2015, Ch. 9), a theorem that also covers FL-6, but is not
  formalised here; without such a growth condition it can fail in every dimension $`d \ge 2`$
  (Bogachev–Krasovitskii–Shaposhnikov 2021).
- **Preconditioned noise–score equivalence.** `Examples/NoiseScorePreconditioned` gives
  non-stationary instances of `map_flow_eq_of_preconditionedWeakFokkerPlanck` and
  `map_flow_eq_of_klFlow` with every hypothesis discharged, for diagonal non-scalar $`A`$ and for
  $`a \cdot I`$. Non-diagonal $`A`$ would need matrix exponentials and an OU kernel for general
  $`A`$.
