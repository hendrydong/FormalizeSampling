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
