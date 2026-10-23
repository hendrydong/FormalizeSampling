# Contributing to FormalizeSampling

## Rules

- The certified library is `FormalizeSampling/`, exported through `FormalizeSampling.lean`. It
  contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or other
  trust-boundary overrides; `scripts/check_contracts.py` enforces this.
- Every public theorem has a docstring stating its mathematics and assumptions. Core results
  have a row in `docs/theorem_registry.md`, which assigns the IDs (numbered 1, 2, ... within each
  prefix), in the section of their area; the Statement cell starts with a bold short title. Each
  row has one bullet in `docs/results.md`, in the same section and order, led by the title and
  the ID and marked `*Conditional*` if the row is, and a witness in a module of
  `FormalizeSampling/Audit/` whose docstring starts with the title `# Statement audit: <summary>`
  and lists the row on its `Rows:` line (unindented, on one line).
- `docs/declaration_index.md` and the coverage and Layout blocks of the README are generated:
  after changing a documented theorem, a registry row, the docstring of an Audit module or the
  directory descriptions (`GROUPS` and `LAYERS` in `scripts/check_contracts.py`), run
  `python3 scripts/check_contracts.py --write`; the checker rejects stale output.
- Library Lean files have lines of at most 100 characters; they, the Markdown files at the top
  level and in `docs/`, and `showcase/README.md` and `experiments/README.md` have no trailing
  whitespace.
- A module imports only modules of its own or a lower layer, in the order given under
  [Layout](README.md#layout). A tool needed by a lower layer goes into that layer. A new module
  is imported by `FormalizeSampling.lean` and, if it lies in a layer of the core, by
  `FormalizeSampling/Core.lean`; `scripts/check_contracts.py` enforces all of this.
- Every file is a Lean module with Mathlib's header conventions: `module`, the `public import`s
  (the Mathlib modules the file uses, not the whole of `Mathlib`), the module docstring, then
  `@[expose] public section` (`public section` in a file without definitions).
- Results are stated for a general algorithm class; a specific published algorithm appears
  only as an example.
- Python code in `experiments/` and `showcase/` gives exact or numerical illustrations; it
  never replaces a Lean proof. Python code passes `ruff check` and `ruff format --check`, with
  the version pinned in `requirements-dev.txt`.

## Conventions

The [glossary](docs/glossary.md) fixes the vocabulary (scores, the notions of "the same
dynamics", distances and divergences). In Lean:

- The state space is `Fin d → ℝ` with Lebesgue `volume`; inner products use `dotProduct`
  (`⬝ᵥ`) and `Matrix.mulVec` (`*ᵥ`). Shared calculus (`partialDeriv`, `grad`, `divergence`,
  `laplacian`, `weightedLaplacian`, `score`, `score1`, `sqNormH`) lives in
  `FormalizeSampling/Foundations/VectorCalculus.lean`. `Foundations/Euclidean.lean` relates the
  state space, its distances, Gaussians, KL, `tvSup` and gradients to Mathlib's
  `EuclideanSpace ℝ (Fin d)` through `WithLp.toLp 2` and `WithLp.ofLp`.
- `score p` $`= \nabla_x \log p`$ is a state score, never a parameter score
  $`\nabla_\theta \log \pi_\theta`$.
- Mathlib's `gaussianReal m v` takes the **variance** `v : ℝ≥0`, not the standard deviation;
  `gaussianPDFReal m v x` is its Lebesgue density. Constants are written exactly (`σ ^ 2`,
  `2 * h`).
- Weak (expectation-level) equality, one-time marginal law equality, finite-dimensional law
  equality, path-law equality and pointwise generator equality are different notions; each
  theorem names the one it proves.
- The library's TV distance is `TotalVariation.tvSup μ ν`
  $`= \sup_A \lvert \mu(A) - \nu(A) \rvert`$. For probability measures it is
  $`\tfrac{1}{2} \Vert \mu - \nu \Vert_1`$, half of Mathlib's `MeasureTheory.tvDist`
  (`TotalVariation.measureTheory_tvDist_eq_two_mul`). KL is Mathlib's `klDiv`.
- Files whose names end in `Pi` work on `Fin d → ℝ`; most have a one-dimensional counterpart
  without the suffix, which is a separate proof on `ℝ`, not the `Pi` form at $`d = 1`$. Many
  files without the suffix (flow, diffusion) are also on `Fin d → ℝ`. New results should be
  stated on `Fin d → ℝ`.

## Statuses

See [README, Statuses](README.md#statuses).
