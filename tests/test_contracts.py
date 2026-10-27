"""Regression tests for scripts/check_contracts.py (source hygiene and registry contract)."""

import contextlib
import io
import re
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import check_contracts

HEADER = "module\n\npublic import Mathlib.Logic.Basic\n\n"

MODULE = (
    HEADER + "/-! Example module. -/\n\n"
    "@[expose] public section\n\n"
    "namespace FormalizeSampling\n\n"
    "/-- First public identity. -/\n"
    "@[simp] theorem first : True := by simp [True]\n\n"
    "/-- Second public identity. -/\n"
    "theorem second : True := by trivial\n\n"
    "private theorem helper : True := trivial\n\n"
    "end FormalizeSampling\n"
)


SCOPED = (
    HEADER + "/-! Example module with nested scopes. -/\n\n"
    "public section\n\n"
    "namespace FormalizeSampling.A\n\n"
    "section S\n\n"
    "namespace B\n\n"
    "/-- Dotted name inside nested namespaces. -/\n"
    "theorem C.d : True := trivial\n\n"
    "end B\n\n"
    "end S\n\n"
    "/-- Protected theorem. -/\n"
    "protected theorem e : True := trivial\n\n"
    "/-- Root name. -/\n"
    "theorem _root_.FormalizeSampling.f : True := trivial\n\n"
    "noncomputable section\n\n"
    "/-- Inside a noncomputable section. -/\n"
    "theorem h : True := trivial\n\n"
    "end\n\n"
    "end FormalizeSampling.A\n\n"
    "/-- Outside every namespace. -/\n"
    "theorem g : True := trivial\n"
)


def leaf(doc: str, imports: str = "public import Mathlib.Logic.Basic\n") -> str:
    """A small library module with the given imports and module docstring."""
    return f"module\n\n{imports}\n/-! {doc} -/\n\npublic section\n"


# Registry IDs of the fixtures, with their registry sections.
FIXTURE_IDS = ("KL-1", "KL-2", "KL-3", "CE-01")
SECTIONS = {"KL": "Foundations", "CE": "Counterexamples"}
WITNESS = "Audit/Witness.lean"


def audit_module(ids: tuple[str, ...], title: str = "fixture witnesses") -> str:
    """A witness module whose docstring header lists `ids` on its `Rows:` line."""
    return (
        f"module\n\npublic import Mathlib.Logic.Basic\n\n/-!\n# Statement audit: {title}\n\n"
        f"Rows: {', '.join(ids)}.\n\nWitnesses.\n-/\n\npublic section\n"
    )


def generated_blocks(*names: str) -> list[str]:
    """Empty generated blocks (their markers), filled by `--write`."""
    return [
        line
        for name in names
        for line in (f"<!-- BEGIN GENERATED: {name} -->", f"<!-- END GENERATED: {name} -->", "")
    ]


def registry(rows: dict[str, tuple[str, ...]], ids: tuple[str, ...] = FIXTURE_IDS) -> str:
    """A registry with one row per ID: `rows[rid]` is (status, declarations[, modules]); rows not
    given are Open and cite nothing. Every row has the title `**Result.**` and lists the module
    `Foundations/Example`."""
    lines, area = ["# Registry"], ""
    for rid in ids:
        status, decl, module = (*rows.get(rid, ("Open", "—")), "`Foundations/Example`")[:3]
        if SECTIONS[rid.split("-")[0]] != area:
            area = SECTIONS[rid.split("-")[0]]
            lines += ["", f"## {area}", ""]
        lines.append(f"| {rid} | {status} | **Result.** statement | {decl} | scope | {module} |")
    return "\n".join(lines) + "\n"


def fixture_docs(
    rows: dict[str, tuple[str, ...]], ids: tuple[str, ...] = FIXTURE_IDS
) -> dict[str, str]:
    """Minimal README, docs/results.md and docs/literature.md that agree with `registry(rows)`:
    the counts sentence (the fixtures have under 1000 lines and 100 theorems), a moves table
    with every ID once (ranges per prefix), a literature map with one work citing the first ID,
    the Statuses section, one results bullet per ID under its registry section (marked
    `*Conditional*` for Conditional rows), and links."""
    statuses = [rows.get(rid, ("Open",))[0] for rid in ids]
    by_prefix: dict[str, list[str]] = {}
    for rid in ids:
        by_prefix.setdefault(rid.split("-")[0], []).append(rid)
    ranges = [
        group[0] if len(group) == 1 else f"{group[0]} … {group[-1]}" for group in by_prefix.values()
    ]
    moves = [f"| Move {n} | tools | — | {cell} |" for n, cell in enumerate(ranges)]
    readme = [
        "# Fixture",
        "",
        f"About 0 lines of Lean, 0 documented theorems and {len(ids)} core results: "
        f"{statuses.count('Verified')} Verified, {statuses.count('Counterexample')} formal "
        f"counterexamples, {statuses.count('Conditional')} Conditional.",
        "",
        "| Move | What it provides | Main modules | Registry IDs |",
        "|---|---|---|---|",
        *moves,
        "",
        "Results by area: [`docs/results.md`](docs/results.md#foundations).",
        "",
        *generated_blocks("coverage", "layout"),
        "## Literature map",
        "",
        "| Work | Algorithm | What is formalised here | Status |",
        "|---|---|---|---|",
        f"| [Author (2020)](https://example.org/a) | a sampler | a step | {ids[0]} |",
        "",
        "## Statuses",
        "",
        *(f"- `{status}`: meaning." for status in sorted(check_contracts.STATUSES)),
    ]
    results = ["# Results", "", "Hypotheses: [registry](theorem_registry.md)."]
    area = ""
    for rid in ids:
        if SECTIONS[rid.split("-")[0]] != area:
            area = SECTIONS[rid.split("-")[0]]
            results += ["", f"## {area}", ""]
        mark = (
            " *Conditional* on a hypothesis."
            if rows.get(rid, ("Open",))[0] == "Conditional"
            else ""
        )
        results.append(f"- **Result ({rid}).** Statement.{mark}")
    literature = [
        "# Literature",
        "",
        "## Area",
        "",
        "### Author (2020)",
        "",
        "Author. Title. [example.org/a](https://example.org/a).",
        "",
        f"| step | comparison | `first` | {ids[0]} |",
    ]
    return {
        "README.md": "\n".join(readme) + "\n",
        "docs/results.md": "\n".join(results) + "\n",
        "docs/literature.md": "\n".join(literature) + "\n",
    }


def module_name(relative: str) -> str:
    """Module name of a file path relative to `FormalizeSampling/`."""
    return "FormalizeSampling." + relative.removesuffix(".lean").replace("/", ".")


def import_line(relative: str) -> str:
    return f"public import {module_name(relative)}\n"


def aggregator(imports: str, doc: str | None = None) -> str:
    """The root or core module: public imports only."""
    return "module\n\n" + imports + (f"\n/-! {doc} -/\n" if doc else "")


@contextlib.contextmanager
def synthetic_repo(
    module: str,
    rows: dict[str, tuple[str, ...]],
    extra: dict[str, str | None] | None = None,
    core: bool = True,
    public_root: bool = True,
    docs: dict[str, str | None] | None = None,
    ids: tuple[str, ...] = FIXTURE_IDS,
):
    """A temporary repository: the library files (`module` as Foundations/Example.lean, a
    witness module listing `ids`, plus `extra`, where `None` omits a file), the root and core
    modules, the registry of `ids` and `rows`, and the fixture documents updated by `docs`."""
    files = {"Foundations/Example.lean": module, WITNESS: audit_module(ids), **(extra or {})}
    files = {relative: text for relative, text in files.items() if text is not None}
    if core and "Core.lean" not in files:
        levels = {relative: check_contracts.layer(module_name(relative)) for relative in files}
        lower = [
            relative
            for relative, level in levels.items()
            if level is not None and level <= check_contracts.CORE_LAYER
        ]
        files["Core.lean"] = aggregator("".join(map(import_line, lower)), "The core.")
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "docs").mkdir()
        for relative, text in files.items():
            path = root / "FormalizeSampling" / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        root_imports = "".join(map(import_line, files))
        if not public_root:
            root_imports = root_imports.replace("public import", "import")
        (root / "FormalizeSampling.lean").write_text(aggregator(root_imports))
        (root / "docs/theorem_registry.md").write_text(registry(rows, ids))
        for relative, text in {**fixture_docs(rows, ids), **(docs or {})}.items():
            if text is not None:
                (root / relative).parent.mkdir(parents=True, exist_ok=True)
                (root / relative).write_text(text)
        yield root


def invoke(root: Path, *args: str) -> tuple[int, str]:
    """Run the checker on the repository `root` with command-line `args`."""
    out, err = io.StringIO(), io.StringIO()
    with (
        patch.object(check_contracts, "ROOT", root),
        patch("sys.argv", ["check_contracts.py", *args]),
        contextlib.redirect_stdout(out),
        contextlib.redirect_stderr(err),
    ):
        code = check_contracts.main()
    return code, out.getvalue() + err.getvalue()


class ContractTests(unittest.TestCase):
    def run_checker(
        self,
        module: str,
        rows: dict[str, tuple[str, ...]],
        write_index: bool,
        extra: dict[str, str | None] | None = None,
        core: bool = True,
        public_root: bool = True,
        docs: dict[str, str | None] | None = None,
        ids: tuple[str, ...] = FIXTURE_IDS,
        args: tuple[str, ...] = (),
    ) -> tuple[int, str]:
        """Run the checker once on a `synthetic_repo` (with `--write-index` if asked); the output
        is followed by the declaration index."""
        with synthetic_repo(module, rows, extra, core, public_root, docs, ids) as root:
            code, output = invoke(root, *args, *(["--write-index"] if write_index else []))
            index = root / "docs/declaration_index.md"
            return code, output + (index.read_text() if index.exists() else "")

    def test_clean_module_passes_and_indexes_public_theorems(self):
        rows = {"KL-1": ("Verified", "`FormalizeSampling.first`")}
        code, output = self.run_checker(MODULE, rows, write_index=True)
        self.assertEqual(code, 0, output)
        self.assertIn("## Foundations", output)
        self.assertIn(
            "| `FormalizeSampling.first` | First public identity. | "
            "[Example:12](../FormalizeSampling/Foundations/Example.lean#L12) |",
            output,
        )
        self.assertIn("| `FormalizeSampling.second` | Second public identity. |", output)
        self.assertNotIn("FormalizeSampling.helper", output)
        self.assertIn("2 documented theorems", output)

    def test_index_uses_fully_qualified_names(self):
        code, output = self.run_checker(SCOPED, {}, write_index=True)
        self.assertEqual(code, 0, output)
        for name in (
            "FormalizeSampling.A.B.C.d",
            "FormalizeSampling.A.e",
            "FormalizeSampling.f",
            "FormalizeSampling.A.h",
            "g",
        ):
            self.assertIn(f"| `{name}` |", output)

    def test_unmatched_end_is_reported(self):
        code, output = self.run_checker(MODULE + "end FormalizeSampling\n", {}, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn("Unmatched `end`", output)

    def test_summary_is_the_opening_of_the_docstring(self):
        summary = check_contracts.summary
        self.assertEqual(summary("Plain statement for `μ`. More."), "Plain statement for `μ`.")
        self.assertEqual(
            summary("**Pinsker.** For all `μ`, a bound. More."), "Pinsker. For all `μ`, a bound."
        )
        self.assertEqual(summary("**Pinsker.**"), "Pinsker.")
        self.assertEqual(
            summary("Uses `KL.klDiv_chain_le_sum`, e.g. for chains.\nSecond sentence."),
            "Uses `KL.klDiv_chain_le_sum`, e.g. for chains.",
        )
        self.assertEqual(summary("Bound `|x| ≤ 1` holds. Next."), "Bound `\\|x\\| ≤ 1` holds.")
        long = summary("Word " * 40 + "`code with spaces " * 3 + "end`.")
        self.assertTrue(long.endswith(" …"))
        self.assertLessEqual(len(long), check_contracts.SUMMARY_LENGTH + 2)
        self.assertEqual(long.count("`") % 2, 0)
        unbreakable = "`" + "x" * 200 + "`."
        self.assertEqual(summary(unbreakable), unbreakable)

    def test_sorry_and_missing_docstring_are_rejected(self):
        bad = MODULE.replace("/-- Second public identity. -/\n", "").replace(
            "by trivial", "by sorry"
        )
        code, output = self.run_checker(bad, {}, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn("Uncertified construct", output)
        self.assertIn("without adjacent docstring", output)

    def test_sorry_inside_comment_is_allowed(self):
        commented = MODULE.replace("/-! Example module. -/", "/-! Example; no sorry here. -/")
        code, output = self.run_checker(commented, {}, write_index=True)
        self.assertEqual(code, 0, output)

    def test_certified_row_needs_declaration_and_open_row_must_not_cite_one(self):
        rows = {
            "KL-1": ("Verified", "—"),
            "KL-2": ("Open", "`FormalizeSampling.first`"),
        }
        code, output = self.run_checker(MODULE, rows, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn("Verified row without a Lean declaration: KL-1", output)
        self.assertIn("Open row must not cite certified declarations: KL-2", output)

    def test_upward_import_is_rejected(self):
        sampler = leaf("A sampler.")
        upward = MODULE.replace(
            "public import Mathlib.Logic.Basic\n",
            "public import Mathlib.Logic.Basic\nimport FormalizeSampling.Samplers.Sampler\n",
        )
        code, output = self.run_checker(
            upward, {}, write_index=True, extra={"Samplers/Sampler.lean": sampler}
        )
        self.assertEqual(code, 1)
        self.assertIn(
            "Upward import (layer 0 -> 3): FormalizeSampling.Foundations.Example imports "
            "FormalizeSampling.Samplers.Sampler",
            output,
        )

    def test_downward_import_and_core_pass(self):
        sampler = leaf("A sampler.", import_line("Foundations/Example.lean"))
        core = aggregator(import_line("Foundations/Example.lean"), "The core.")
        extra = {"Samplers/Sampler.lean": sampler, "Core.lean": core}
        code, output = self.run_checker(MODULE, {}, write_index=True, extra=extra)
        self.assertEqual(code, 0, output)

    def test_core_must_import_exactly_the_lower_layers(self):
        identity = leaf("An identity.")
        sampler = leaf("A sampler.")
        core = aggregator(
            import_line("Foundations/Example.lean") + import_line("Samplers/Sampler.lean"),
            "The core.",
        )
        extra = {
            "Identities/Identity.lean": identity,
            "Samplers/Sampler.lean": sampler,
            "Core.lean": core,
        }
        code, output = self.run_checker(MODULE, {}, write_index=True, extra=extra)
        self.assertEqual(code, 1)
        self.assertIn(
            "Core mismatch: missing=['FormalizeSampling.Identities.Identity'], "
            "extra=['FormalizeSampling.Samplers.Sampler']",
            output,
        )

    def test_missing_core_is_rejected(self):
        code, output = self.run_checker(MODULE, {}, write_index=True, core=False)
        self.assertEqual(code, 1)
        self.assertIn("Missing core module FormalizeSampling/Core.lean", output)

    def test_module_outside_the_layers_is_rejected(self):
        extra = {"Misc/Stray.lean": leaf("Stray.")}
        code, output = self.run_checker(MODULE, {}, write_index=True, extra=extra)
        self.assertEqual(code, 1)
        self.assertIn(
            "Module outside the layered directories: FormalizeSampling.Misc.Stray", output
        )

    def test_non_module_file_is_rejected(self):
        legacy = "import Mathlib\n\n/-! A file without a module header. -/\n"
        code, output = self.run_checker(
            MODULE, {}, write_index=True, extra={"Identities/Legacy.lean": legacy}
        )
        self.assertEqual(code, 1)
        self.assertIn(
            "Not a Lean module (the file must start with `module`): "
            "FormalizeSampling/Identities/Legacy.lean",
            output,
        )

    def test_module_without_public_section_is_rejected(self):
        hidden = MODULE.replace("@[expose] public section\n\n", "")
        code, output = self.run_checker(hidden, {}, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn(
            "Module without `@[expose] public section` or `public section`: "
            "FormalizeSampling/Foundations/Example.lean",
            output,
        )

    def test_core_must_reexport_with_public_import(self):
        core = aggregator("import FormalizeSampling.Foundations.Example\n", "The core.")
        code, output = self.run_checker(MODULE, {}, write_index=True, extra={"Core.lean": core})
        self.assertEqual(code, 1)
        self.assertIn("Core mismatch: missing=['FormalizeSampling.Foundations.Example']", output)

    def test_root_must_reexport_with_public_import(self):
        code, output = self.run_checker(MODULE, {}, write_index=True, public_root=False)
        self.assertEqual(code, 1)
        self.assertIn(
            "Export mismatch (public imports of FormalizeSampling.lean): "
            "missing=['FormalizeSampling.Audit.Witness', 'FormalizeSampling.Core', "
            "'FormalizeSampling.Foundations.Example']",
            output,
        )

    def test_public_section_closed_by_end_is_tracked(self):
        closed = (
            MODULE.replace("@[expose] public section\n\n", "")
            .replace(
                "namespace FormalizeSampling\n\n",
                "namespace FormalizeSampling\n\n@[expose] public noncomputable section\n\n",
            )
            .replace("end FormalizeSampling\n", "end\n\nend FormalizeSampling\n")
        )
        code, output = self.run_checker(closed, {}, write_index=True)
        self.assertEqual(code, 0, output)
        self.assertIn("| `FormalizeSampling.second` | Second public identity. |", output)

    def test_definitions_require_expose(self):
        plain = MODULE.replace("@[expose] public section", "public section").replace(
            "end FormalizeSampling\n", "/-- One. -/\ndef one : Nat := 1\n\nend FormalizeSampling\n"
        )
        code, output = self.run_checker(plain, {}, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn(
            "Module with definitions but without `@[expose] public section`: "
            "FormalizeSampling/Foundations/Example.lean",
            output,
        )
        code, output = self.run_checker(
            plain.replace("def one", "private def one"), {}, write_index=True
        )
        self.assertEqual(code, 0, output)

    def test_whole_mathlib_import_is_rejected(self):
        whole = MODULE.replace("public import Mathlib.Logic.Basic\n", "public import Mathlib\n")
        code, output = self.run_checker(whole, {}, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn(
            "Whole-library `import Mathlib` (import the modules used instead): "
            "FormalizeSampling/Foundations/Example.lean",
            output,
        )

    def test_public_modifier_is_indexed(self):
        explicit = MODULE.replace(
            "theorem second : True := by trivial", "public theorem second : True := by trivial"
        )
        code, output = self.run_checker(explicit, {}, write_index=True)
        self.assertEqual(code, 0, output)
        self.assertIn("| `FormalizeSampling.second` | Second public identity. |", output)

    def test_imports_in_comments_are_ignored(self):
        documented = MODULE.replace(
            "/-! Example module. -/",
            "/-! Example module.\nimport FormalizeSampling.Samplers.Sampler\n-/",
        )
        code, output = self.run_checker(documented, {}, write_index=True)
        self.assertEqual(code, 0, output)

    # Documentation checks. Each test has a passing and a failing case.

    def readme(self, rows=None, ids=FIXTURE_IDS) -> str:
        return fixture_docs(rows or {}, ids)["README.md"]

    def test_registry_ids_are_numbered_contiguously_per_prefix(self):
        code, output = self.run_checker(MODULE, {}, write_index=True)
        self.assertEqual(code, 0, output)
        gap = ("KL-1", "KL-3", "CE-01")
        code, output = self.run_checker(MODULE, {}, write_index=True, ids=gap)
        self.assertEqual(code, 1)
        self.assertIn("Registry IDs KL-* are not numbered 1 to 2: [1, 3]", output)

    def test_readme_counts_sentence_matches_registry_and_sources(self):
        rows = {"KL-1": ("Verified", "`FormalizeSampling.first`")}
        code, output = self.run_checker(MODULE, rows, write_index=True)
        self.assertEqual(code, 0, output)
        stale = self.readme().replace("0 Verified", "1 Verified")
        code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": stale})
        self.assertEqual(code, 1)
        self.assertIn("Stale README.md counts sentence: 1 Verified, expected 0", output)
        code, output = self.run_checker(
            MODULE, {}, write_index=True, docs={"README.md": stale.replace("About", "Some")}
        )
        self.assertIn("No counts sentence", output)

    def test_counts_are_floored_and_may_wrap(self):
        sentence = (
            "About 94,000 lines of Lean, 4,000 documented\ntheorems and 3 core results: "
            "1 Verified, 1 formal counterexamples, 1 Conditional."
        )
        statuses = ["Verified", "Counterexample", "Conditional"]
        self.assertEqual(check_contracts.counts_errors(sentence, statuses, 94324, 4099), [])
        self.assertEqual(
            check_contracts.counts_errors(sentence, statuses, 95000, 3999),
            [
                "Stale README.md counts sentence: 94,000 lines, expected 95,000",
                "Stale README.md counts sentence: 4,000 theorems, expected 3,900",
            ],
        )

    def test_unknown_registry_ids_are_rejected(self):
        results = fixture_docs({})["docs/results.md"]
        harmless = results + "\nLegacy FS-006; KL-1 … CE-01 spans prefixes; KL-1 … KL-3.\n"
        code, output = self.run_checker(
            MODULE, {}, write_index=True, docs={"docs/results.md": harmless}
        )
        self.assertEqual(code, 0, output)
        documented = MODULE.replace("/-! Example module. -/", "/-! Example module (CE-02). -/")
        code, output = self.run_checker(
            documented,
            {},
            write_index=True,
            docs={"docs/results.md": results + "\nSee KL-9.\n"},
        )
        self.assertEqual(code, 1)
        self.assertIn("Unknown registry ID KL-9 in docs/results.md", output)
        self.assertIn(
            "Unknown registry ID CE-02 in FormalizeSampling/Foundations/Example.lean", output
        )

    def test_unknown_ids_in_the_python_illustrations_are_rejected(self):
        clean = {"showcase/plot.py": '"""KL-1: theory vs reality; legacy FS-006."""\n'}
        code, output = self.run_checker(MODULE, {}, write_index=True, docs=clean)
        self.assertEqual(code, 0, output)
        stale = {
            "showcase/plot.py": '"""KL-9: theory vs reality."""\n',
            "experiments/check.py": "# See CE-02.\n",
        }
        code, output = self.run_checker(MODULE, {}, write_index=True, docs=stale)
        self.assertEqual(code, 1)
        self.assertIn("Unknown registry ID KL-9 in showcase/plot.py", output)
        self.assertIn("Unknown registry ID CE-02 in experiments/check.py", output)

    def test_ids_and_ranges(self):
        pattern = check_contracts.id_pattern(["KL-1", "CE-01"])
        self.assertEqual(
            sorted(check_contracts.cited_ids("KL-1 … KL-4, CE-01...CE-03, FS-006, KL-2a", pattern)),
            ["CE-01", "CE-02", "CE-03", "KL-1", "KL-2", "KL-3", "KL-4"],
        )
        self.assertEqual(check_contracts.cited_ids("KL-1 … CE-08", pattern), ["KL-1", "CE-08"])

    def test_moves_table_lists_every_id_once(self):
        readme = self.readme()
        self.assertIn("KL-1 … KL-3", readme)
        twice = readme.replace("| CE-01 |", "| KL-2 |")
        code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": twice})
        self.assertEqual(code, 1)
        self.assertIn("README.md moves table lists KL-2 2 times, not once", output)
        self.assertIn("README.md moves table lists CE-01 0 times, not once", output)

    def test_results_bullets_follow_the_registry(self):
        results = fixture_docs({})["docs/results.md"]
        wrong = (
            results.replace("- **Result (KL-3).** Statement.\n", "")
            .replace("- **Result (KL-2).**", "- **Result (KL-1, CE-01).**")
            .replace(
                "- **Result (CE-01).** Statement.",
                "- **Result (CE-01).** One.\n- **Result (KL-2).** Misplaced.",
            )
        )
        code, output = self.run_checker(MODULE, {}, write_index=True)
        self.assertEqual(code, 0, output)
        code, output = self.run_checker(
            MODULE, {}, write_index=True, docs={"docs/results.md": wrong}
        )
        self.assertEqual(code, 1)
        self.assertIn("docs/results.md bullet led by several IDs: CE-01, KL-1", output)
        self.assertIn("docs/results.md has 2 bullets led by KL-1, not one", output)
        self.assertIn("docs/results.md has 0 bullets led by KL-3, not one", output)
        self.assertIn(
            "docs/results.md bullet KL-2 is under 'Counterexamples', not 'Foundations'", output
        )

    def test_results_bullets_carry_the_registry_titles_order_and_marks(self):
        rows = {
            "KL-1": ("Verified", "`FormalizeSampling.first`"),
            "KL-2": ("Conditional", "`FormalizeSampling.first`"),
            "CE-01": ("Counterexample", "`FormalizeSampling.second`"),
        }
        results = fixture_docs(rows)["docs/results.md"]
        self.assertIn("- **Result (KL-2).** Statement. *Conditional* on a hypothesis.", results)
        code, output = self.run_checker(MODULE, rows, write_index=True)
        self.assertEqual(code, 0, output)
        cases = {
            "docs/results.md bullet KL-1 is led by 'Other (KL-1).', not by the registry title "
            "'Result (KL-1).'": results.replace("**Result (KL-1).**", "**Other (KL-1).**"),
            "docs/results.md bullet KL-2 is out of registry order (KL-1 first)": results.replace(
                "- **Result (KL-1).** Statement.\n- **Result (KL-2).** Statement. *Conditional* "
                "on a hypothesis.",
                "- **Result (KL-2).** Statement. *Conditional* on a hypothesis.\n"
                "- **Result (KL-1).** Statement.",
            ),
            "docs/results.md bullet KL-2 lacks the mark *Conditional*; the registry says "
            "Conditional": results.replace("*Conditional* on", "*Verified* for"),
            "docs/results.md bullet KL-2 is marked *Verified*; the registry says Conditional": (
                results.replace("*Conditional* on", "*Verified* for")
            ),
            "docs/results.md bullet KL-1 has the mark *Conditional*; the registry says Verified": (
                results.replace(
                    "- **Result (KL-1).** Statement.", "- **Result (KL-1).** S.\n  *Conditional*."
                )
            ),
        }
        for message, text in cases.items():
            code, output = self.run_checker(
                MODULE, rows, write_index=True, docs={"docs/results.md": text}
            )
            self.assertEqual(code, 1, message)
            self.assertIn(message, output)
        flipped = {**rows, "CE-01": ("Verified", "`FormalizeSampling.second`")}
        code, output = self.run_checker(
            MODULE, flipped, write_index=True, docs={"docs/results.md": results}
        )
        self.assertEqual(code, 1)
        self.assertIn(
            "docs/results.md bullet CE-01 is under 'Counterexamples'; the registry says Verified",
            output,
        )
        moved = {**rows, "KL-3": ("Counterexample", "`FormalizeSampling.second`")}
        code, output = self.run_checker(MODULE, moved, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn(
            "docs/results.md Counterexample bullet KL-3 is not under 'Counterexamples'", output
        )
        with synthetic_repo(MODULE, rows) as root:
            path = root / "docs/theorem_registry.md"
            path.write_text(
                path.read_text().replace("| **Result.** statement |", "| statement |", 1)
            )
            code, output = invoke(root, "--write")
        self.assertEqual(code, 1)
        self.assertIn("Verified row whose Statement does not start with **<title>.**: KL-1", output)

    def test_status_words_next_to_ids_match_the_registry(self):
        rows = {"KL-1": ("Verified", "`FormalizeSampling.first`")}
        results = fixture_docs(rows)["docs/results.md"]
        agreeing = results + "\nKL-1 is Verified; KL-2, KL-3 (*Open*); CE-01 for KL-1.\n"
        code, output = self.run_checker(
            MODULE, rows, write_index=True, docs={"docs/results.md": agreeing}
        )
        self.assertEqual(code, 0, output)
        wrong = results + "\nKL-1 … KL-2 Verified. *Conditional on an LSI (KL-3).*\n"
        code, output = self.run_checker(
            MODULE, rows, write_index=True, docs={"docs/results.md": wrong}
        )
        self.assertEqual(code, 1)
        self.assertNotIn("calls KL-1", output)
        self.assertIn("docs/results.md calls KL-2 Verified; the registry says Open", output)
        self.assertIn("docs/results.md calls KL-3 Conditional; the registry says Open", output)

    def test_literature_map_matches_the_literature_sections(self):
        readme = self.readme()
        literature = fixture_docs({})["docs/literature.md"]
        unmatched = readme.replace(
            "https://example.org/a) | a sampler | a step | KL-1 |",
            "https://example.org/b) | a sampler | a step | KL-2 |",
        )
        code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": unmatched})
        self.assertEqual(code, 1)
        self.assertIn(
            "README.md literature map lists https://example.org/b, which has no section", output
        )
        self.assertIn("docs/literature.md section of https://example.org/a has no row", output)
        self.assertIn("is not in its works", output)
        two = literature + "\n### Other (2021)\n\n[x](https://example.org/b). KL-2\n"
        both = readme.replace(
            "[Author (2020)](https://example.org/a)",
            "[Author (2020)](https://example.org/a); [Other (2021)](https://example.org/b)",
        ).replace("| a step | KL-1 |", "| a step | KL-1, KL-2 |")
        code, output = self.run_checker(
            MODULE, {}, write_index=True, docs={"README.md": both, "docs/literature.md": two}
        )
        self.assertEqual(code, 0, output)

    def test_registry_cites_documented_theorems_and_their_modules(self):
        rows = {"KL-1": ("Verified", "`FormalizeSampling.first`", "`Foundations/Ex*`")}
        code, output = self.run_checker(MODULE, rows, write_index=True)
        self.assertEqual(code, 0, output)
        rows = {
            "KL-1": ("Verified", "`FormalizeSampling.first`", "`Identities/Missing`"),
            "KL-2": ("Verified", "`FormalizeSampling.helper`"),
        }
        code, output = self.run_checker(MODULE, rows, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn(
            "KL-1: Module column lists Identities/Missing, which is no library file", output
        )
        self.assertIn(
            "KL-1: Module column misses Foundations/Example (declares FormalizeSampling.first)",
            output,
        )
        self.assertIn("KL-2: FormalizeSampling.helper is not a documented public theorem", output)

    def test_missing_readme_tables_and_sections_are_reported(self):
        readme = self.readme()
        cases = {
            "No moves table (| Move | ... | Registry IDs |) in README.md": readme.replace(
                "| Move | What it provides |", "| Step | What it provides |"
            ),
            "No literature map table (## Literature map, | Work | ...) in README.md": (
                readme.replace("| Work | Algorithm |", "| Paper | Algorithm |")
            ),
            "No ## Statuses section in README.md": readme.replace("## Statuses", "## Status"),
        }
        for message, text in cases.items():
            code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": text})
            self.assertEqual(code, 1, message)
            self.assertIn(message, output)

    def test_literature_sections_need_distinct_urls(self):
        readme = self.readme()
        literature = fixture_docs({})["docs/literature.md"]
        cases = {
            "docs/literature.md section 'Plain (2021)' has no URL": (
                readme,
                literature + "\n### Plain (2021)\n\nNo link here.\n",
            ),
            "docs/literature.md sections share the URL https://example.org/a": (
                readme,
                literature + "\n### Again (2021)\n\n[a](https://example.org/a).\n",
            ),
            "README.md literature map lists https://example.org/a twice": (
                readme.replace(
                    "[Author (2020)](https://example.org/a)",
                    "[Author (2020)](https://example.org/a); [Same](https://example.org/a)",
                ),
                literature,
            ),
        }
        for message, (text, sections) in cases.items():
            code, output = self.run_checker(
                MODULE,
                {},
                write_index=True,
                docs={"README.md": text, "docs/literature.md": sections},
            )
            self.assertEqual(code, 1, message)
            self.assertIn(message, output)

    def test_statuses_section_lists_every_status(self):
        readme = self.readme()
        self.assertIn("## Statuses", readme)
        partial = readme.replace("- `Open`: meaning.\n", "")
        code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": partial})
        self.assertEqual(code, 1)
        self.assertIn("README.md Statuses section lists", output)

    def test_relative_links_and_anchors_resolve(self):
        readme = self.readme() + (
            '\n## What "Verified" means\n\nSee [above](#what-verified-means), '
            "[the registry](docs/theorem_registry.md#foundations) and "
            "![a figure](FormalizeSampling/Core.lean).\n"
        )
        code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": readme})
        self.assertEqual(code, 0, output)
        broken = readme + (
            "\n[gone](docs/missing.md), [no anchor](docs/results.md#nowhere), "
            "[outside](../outside.md), [web](https://example.org/x#y).\n"
        )
        code, output = self.run_checker(MODULE, {}, write_index=True, docs={"README.md": broken})
        self.assertEqual(code, 1)
        self.assertIn("Broken link in README.md: docs/missing.md", output)
        self.assertIn("Broken anchor in README.md: docs/results.md#nowhere", output)
        self.assertIn("Broken link in README.md: ../outside.md", output)
        self.assertNotIn("example.org/x", output)

    def test_heading_slugs_follow_github(self):
        slug = check_contracts.slug
        self.assertEqual(slug('What "Verified" means'), "what-verified-means")
        self.assertEqual(
            slug("Diffusion models: deterministic samplers"),
            "diffusion-models-deterministic-samplers",
        )
        self.assertEqual(
            slug("1. Scores (`memorization.py` → `figures/x.png`)"),
            "1-scores-memorizationpy--figuresxpng",
        )
        self.assertEqual(slug("Fokker–Planck uniqueness"), "fokkerplanck-uniqueness")
        self.assertEqual(
            check_contracts.anchors("# A\n\n## A\n\n```\n# not a heading\n```\n"), {"a", "a-1"}
        )

    def test_whitespace_scan_covers_showcase_and_experiments(self):
        clean = {"showcase/README.md": "# Showcase\n", "experiments/README.md": "# Experiments\n"}
        code, output = self.run_checker(MODULE, {}, write_index=True, docs=clean)
        self.assertEqual(code, 0, output)
        dirty = {
            "showcase/README.md": "# Showcase \n",
            "experiments/README.md": "# Experiments\t\n",
        }
        code, output = self.run_checker(MODULE, {}, write_index=True, docs=dirty)
        self.assertEqual(code, 1)
        self.assertIn("Trailing whitespace: showcase/README.md:1", output)
        self.assertIn("Trailing whitespace: experiments/README.md:1", output)

    def test_banned_phrases_are_rejected_in_documents_and_sources(self):
        allowed = {
            "README.md": self.readme() + "\nA version of Theorem 1, rather than the prior one.\n",
            "docs/archive/notes.md": "We have not found this stated elsewhere.\n",
        }
        code, output = self.run_checker(MODULE, {}, write_index=True, docs=allowed)
        self.assertEqual(code, 0, output)
        banned = {
            "README.md": self.readme() + "\nA novel bound.\n",
            "docs/notes.md": "The exact sum, rather than the\npaper's bound.\n",
            "experiments/README.md": "To our knowledge this is stated here only.\n",
        }
        module = MODULE.replace("/-! Example module. -/", "/-! Example; we have NOT found it. -/")
        code, output = self.run_checker(module, {}, write_index=True, docs=banned)
        self.assertEqual(code, 1)
        self.assertIn("Banned phrase 'novel': README.md:", output)
        self.assertIn("Banned phrase 'rather than the paper': docs/notes.md:1", output)
        self.assertIn("Banned phrase 'To our knowledge': experiments/README.md:1", output)
        self.assertIn(
            "Banned phrase 'we have NOT found': FormalizeSampling/Foundations/Example.lean:5",
            output,
        )

    def test_required_documents_must_exist(self):
        code, output = self.run_checker(
            MODULE, {}, write_index=True, docs={"README.md": None, "docs/literature.md": None}
        )
        self.assertEqual(code, 1)
        self.assertIn("Missing documentation file: README.md", output)
        self.assertIn("Missing documentation file: docs/literature.md", output)

    def test_axiom_audit_resolves_names_in_the_same_documents(self):
        source = (check_contracts.ROOT / "scripts/AxiomAudit.lean").read_text()
        listed = source.split("def docFiles : List String :=", 1)[1].split("]", 1)[0]
        self.assertEqual(re.findall(r'"([^"]+)"', listed), list(check_contracts.DOC_FILES))

    def test_readme_examples_are_extracted(self):
        readme = self.readme() + (
            "\n```lean\nrequire «x» from git\n```\n\n"
            "```lean\nimport A\n\nexample : True := trivial\n```\n"
            "\n```lean\nimport B\n```\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory, "examples")
            code, output = self.run_checker(
                MODULE,
                {},
                write_index=False,
                docs={"README.md": readme},
                args=("--extract-examples", str(target)),
            )
            self.assertEqual(code, 0, output)
            self.assertEqual(
                sorted(p.name for p in target.iterdir()),
                ["ReadmeExample1.lean", "ReadmeExample2.lean"],
            )
            self.assertEqual(
                (target / "ReadmeExample1.lean").read_text(),
                "import A\n\nexample : True := trivial\n",
            )
        code, output = self.run_checker(
            MODULE, {}, write_index=False, args=("--extract-examples", "unused")
        )
        self.assertEqual(code, 1)
        self.assertIn("No ```lean block starting with `import` in README.md", output)

    # Generated documentation: the README coverage and Layout blocks and the witness table.

    def test_id_ranges(self):
        ranges = check_contracts.id_ranges
        self.assertEqual(ranges([f"DF-{n}" for n in range(1, 11)]), "DF-1 … DF-10")
        self.assertEqual(ranges(["GI-1", "GI-2"]), "GI-1, GI-2")
        self.assertEqual(ranges(["DF-4", "DF-5", "DF-6", "DF-8"]), "DF-4 … DF-6, DF-8")
        self.assertEqual(
            ranges(["FL-1", "FL-2", "FL-3", "DT-1", "CE-01", "CE-02", "CE-03"]),
            "FL-1 … FL-3, DT-1, CE-01 … CE-03",
        )
        self.assertEqual(ranges([]), "")

    def test_registry_rows_sit_in_sections(self):
        areas, errors = check_contracts.registry_areas(registry({}))
        self.assertEqual(
            areas, [("Foundations", ["KL-1", "KL-2", "KL-3"]), ("Counterexamples", ["CE-01"])]
        )
        self.assertEqual(errors, [])
        broken = "| KL-1 | Open | s | — | s | m |\n## A\n\n## B\n| CE-01 | Open |\n## B\n"
        _, errors = check_contracts.registry_areas(broken)
        self.assertEqual(
            errors,
            [
                "Registry row KL-1 is not under a `## ` section",
                "Registry section 'B' appears twice",
                "Registry section 'A' has no rows",
                "Registry section 'B' has no rows",
            ],
        )

    def test_readme_blocks_are_generated_and_round_trip(self):
        rows = {
            "KL-1": ("Verified", "`FormalizeSampling.first`"),
            "CE-01": ("Counterexample", "`FormalizeSampling.second`"),
        }
        with synthetic_repo(MODULE, rows) as root:
            readme = root / "README.md"
            code, output = invoke(root)
            self.assertEqual(code, 1)
            for what in (
                "docs/declaration_index.md",
                "the coverage block of README.md",
                "the layout block of README.md",
            ):
                self.assertIn(f"Stale generated documentation: {what}; run with --write", output)
            code, output = invoke(root, "--write")
            self.assertEqual(code, 0, output)
            written = readme.read_text()
            self.assertIn(
                "<!-- BEGIN GENERATED: coverage -->\n\n"
                "| Area | Registry rows | Status |\n|---|---|---|\n"
                "| Foundations | KL-1 … KL-3 | 1 Verified, 2 Open |\n"
                "| Counterexamples | CE-01 | 1 Counterexample |\n\n"
                "<!-- END GENERATED: coverage -->",
                written,
            )
            self.assertIn("| `FormalizeSampling/Kernels/` | TV error propagation", written)
            self.assertIn(
                "in the order\n`Foundations` < `Identities`, `Kernels` < `Flow`, "
                "`ScoreEstimation` < `Samplers` < `Examples`,\n`Counterexamples` < `Audit`",
                written,
            )
            self.assertTrue(
                all(
                    len(line) <= 100
                    for line in written.split("<!-- BEGIN GENERATED: layout")[1].splitlines()
                    if not line.startswith("|")
                )
            )
            index = (root / "docs/declaration_index.md").read_text()
            code, output = invoke(root, "--write")  # idempotent
            self.assertEqual(code, 0, output)
            self.assertEqual(readme.read_text(), written)
            self.assertEqual((root / "docs/declaration_index.md").read_text(), index)
            code, output = invoke(root)
            self.assertEqual(code, 0, output)
            readme.write_text(written.replace("1 Verified, 2 Open", "3 Verified"))
            code, output = invoke(root)
            self.assertEqual(code, 1)
            self.assertIn("Stale generated documentation: the coverage block of README.md", output)
            self.assertNotIn("layout block", output)
            readme.write_text(written.replace("<!-- END GENERATED: layout -->", ""))
            code, output = invoke(root, "--write")
            self.assertEqual(code, 1)
            self.assertIn("No generated layout block (<!-- BEGIN GENERATED: layout --> ...", output)

    def test_layout_comes_from_groups_and_layers(self):
        block = check_contracts.layout_block()
        for group, text in check_contracts.GROUPS.items():
            self.assertIn(f"| `FormalizeSampling/{group}/` | {text.removesuffix('.')} |", block)
        self.assertIn("(`Foundations`, `Identities`, `Kernels`, `Flow`, `ScoreEstimation`)", block)
        self.assertIn("(the\nthree lowest layers)", block)
        groups = {**check_contracts.GROUPS, "Extra": "A directory without a layer."}
        with patch.object(check_contracts, "GROUPS", groups):
            code, output = self.run_checker(MODULE, {}, write_index=True)
        self.assertEqual(code, 1)
        self.assertIn("GROUPS and LAYERS list different directories: ['Extra']", output)

    def test_wrap_keeps_code_spans_whole(self):
        words = "word " * 17
        self.assertEqual(
            check_contracts.wrap(words + "`a code span` end"), words + "`a code span`\nend"
        )
        self.assertEqual(
            check_contracts.wrap("word " + words + "`a code span` end"),
            "word " + words.rstrip() + "\n`a code span` end",
        )
        self.assertEqual(check_contracts.wrap("`" + "x " * 60 + "`", 20).count("\n"), 0)

    def test_witness_table_heads_the_audit_section(self):
        extra = {
            "Audit/Counter.lean": audit_module(("CE-01",), "a counterexample | instance"),
            WITNESS: audit_module(("KL-3", "KL-1", "KL-2")),
        }
        code, output = self.run_checker(MODULE, {}, write_index=True, extra=extra)
        self.assertEqual(code, 0, output)
        self.assertIn(
            "## Audit\n\nStatement audit: Lean witnesses on non-degenerate instances for every "
            "registry row.\n\nWitness modules,",
            output,
        )
        self.assertIn(
            "| Module | Rows | Summary |\n| --- | --- | --- |\n"
            "| [Witness](../FormalizeSampling/Audit/Witness.lean) | KL-1 … KL-3 | "
            "fixture witnesses |\n"
            "| [Counter](../FormalizeSampling/Audit/Counter.lean) | CE-01 | "
            "a counterexample \\| instance |\n",
            output,
        )

    def test_witness_rows_cover_the_registry(self):
        extra = {
            WITNESS: audit_module(("KL-1", "KL-2", "KL-2", "KL-9", "KL")),
            "Audit/Untitled.lean": leaf("Witnesses without the fixed header."),
        }
        code, output = self.run_checker(MODULE, {}, write_index=True, extra=extra)
        self.assertEqual(code, 1)
        self.assertIn("FormalizeSampling/Audit/Witness.lean: Rows line lists KL-2 twice", output)
        self.assertIn("Rows line lists 'KL-9', which is no registry row", output)
        self.assertIn("Rows line lists 'KL', which is no registry row", output)
        self.assertIn("Registry row KL-3 is in no witness module's Rows line", output)
        self.assertIn("Registry row CE-01 is in no witness module's Rows line", output)
        self.assertIn(
            "Witness module docstring without the title `# Statement audit: <summary>` and one "
            "unindented, one-line `Rows: <IDs>.` line: FormalizeSampling/Audit/Untitled.lean",
            output,
        )

    def test_rows_line_is_unindented_and_on_one_line(self):
        witness = audit_module(FIXTURE_IDS)
        self.assertIn("\nRows: KL-1, KL-2, KL-3, CE-01.\n", witness)
        cases = {
            "indented": witness.replace("\nRows: ", "\n  Rows: "),
            "wrapped": witness.replace("KL-2, KL-3", "KL-2,\nKL-3"),
            "unterminated": witness.replace("CE-01.", "CE-01"),
            "repeated": witness.replace("\nWitnesses.", "\nRows: KL-1.\nWitnesses."),
        }
        for name, text in cases.items():
            code, output = self.run_checker(MODULE, {}, write_index=True, extra={WITNESS: text})
            self.assertEqual(code, 1, name)
            self.assertIn(
                "one unindented, one-line `Rows: <IDs>.` line: FormalizeSampling/Audit/Witness.lean",
                output,
            )
        later = witness + "\n/-! Rows: KL-1. -/\n"
        code, output = self.run_checker(MODULE, {}, write_index=True, extra={WITNESS: later})
        self.assertEqual(code, 0, output)

    def test_stale_witness_table_is_rejected(self):
        with synthetic_repo(MODULE, {}) as root:
            self.assertEqual(invoke(root, "--write")[0], 0)
            witness = root / "FormalizeSampling" / WITNESS
            witness.write_text(audit_module(FIXTURE_IDS, "renamed witnesses"))
            code, output = invoke(root)
            self.assertEqual(code, 1)
            self.assertEqual(
                output.strip(),
                "Stale generated documentation: docs/declaration_index.md; run with --write",
            )
            self.assertEqual(invoke(root, "--write-index")[0], 0)  # the old flag is an alias
            self.assertIn("| renamed witnesses |", (root / "docs/declaration_index.md").read_text())


if __name__ == "__main__":
    unittest.main()
