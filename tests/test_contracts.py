"""Regression tests for scripts/check_contracts.py (source hygiene and registry contract)."""

import contextlib
import io
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


def registry(rows: dict[str, str]) -> str:
    lines = []
    for rid in sorted(check_contracts.REQUIRED_IDS):
        status, decl = rows.get(rid, ("Open", "—"))
        lines.append(f"| {rid} | {status} | statement | {decl} | scope | module |")
    return "\n".join(lines) + "\n"


def module_name(relative: str) -> str:
    """Module name of a file path relative to `FormalizeSampling/`."""
    return "FormalizeSampling." + relative.removesuffix(".lean").replace("/", ".")


def import_line(relative: str) -> str:
    return f"public import {module_name(relative)}\n"


def aggregator(imports: str, doc: str | None = None) -> str:
    """The root or core module: public imports only."""
    return "module\n\n" + imports + (f"\n/-! {doc} -/\n" if doc else "")


class ContractTests(unittest.TestCase):
    def run_checker(
        self,
        module: str,
        rows: dict[str, str],
        write_index: bool,
        extra: dict[str, str] | None = None,
        core: bool = True,
        public_root: bool = True,
    ) -> tuple[int, str]:
        files = {"Foundations/Example.lean": module, **(extra or {})}
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
            (root / "docs/theorem_registry.md").write_text(registry(rows))
            argv = ["check_contracts.py"] + (["--write-index"] if write_index else [])
            out, err = io.StringIO(), io.StringIO()
            with (
                patch.object(check_contracts, "ROOT", root),
                patch("sys.argv", argv),
                contextlib.redirect_stdout(out),
                contextlib.redirect_stderr(err),
            ):
                code = check_contracts.main()
            index = root / "docs/declaration_index.md"
            text = index.read_text() if index.exists() else ""
            return code, out.getvalue() + err.getvalue() + text

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
            "missing=['FormalizeSampling.Core', 'FormalizeSampling.Foundations.Example']",
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


if __name__ == "__main__":
    unittest.main()
