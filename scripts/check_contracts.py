#!/usr/bin/env python3
"""Check proof-source hygiene, module headers, complete exports, the import layering, and the
theorem registry.

Every library file is a Lean module (`module` header, Mathlib's conventions); the root
`FormalizeSampling.lean` and `FormalizeSampling/Core.lean` re-export their modules with
`public import`. This source checker complements the Lean kernel and the transitive axiom audit
(scripts/AxiomAudit.lean); it replaces neither. --write-index refreshes
docs/declaration_index.md (fully qualified theorem names with the opening of their docstrings,
grouped by top-level directory).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "FormalizeSampling"
REGISTRY = "docs/theorem_registry.md"
INDEX = "docs/declaration_index.md"
# Core theorem IDs from docs/blueprint.md, section 4, and the counterexample library.
REQUIRED_IDS = (
    {f"KL-{i}" for i in range(1, 7)}
    | {f"ID-{i}" for i in range(1, 5)}
    | {f"FL-{i}" for i in range(1, 6)}
    | {f"SE-{i}" for i in range(1, 5)}
    | {f"KR-{i}" for i in range(1, 3)}
    | {
        "GI-1",
        "GI-2",
        "MH-1",
        "PX-1",
        "PX-2",
        "PX-3",
        "PX-4",
        "PT-1",
        "DT-1",
        "EX-1",
        "EX-2",
        "EX-3",
    }
    | {f"CE-{i:02d}" for i in range(1, 9)}
)
EXTRA_ID = re.compile(r"^(?:[A-Z]{2}-\d+|CE-\d{2})$")  # further core results and counterexamples
ROW_ID = re.compile(r"^\| (?P<id>(?:[A-Z]{2}-\d+|CE-\d{2})) \|")
STATUSES = {"Verified", "Conditional", "Counterexample", "Planned", "Open"}
CERTIFIED = {"Verified", "Conditional", "Counterexample"}
COLUMNS = 6  # ID | Status | Statement | Lean declarations | Assumptions and scope | Module
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
OVERRIDES = re.compile(r"skipKernelTC|implemented_by|\bextern\b|debug\.skipKernelTC")
PUBLIC = re.compile(
    r"(?m)^(?:@\[[^\n]*?\]\s*)?(?:(?P<private>private\s+)|public\s+)?(?:protected\s+)?"
    r"(?:noncomputable\s+)?(?:theorem|lemma)\s+(?P<name>[\w.'₀-₉]+)"
)
SCOPE = re.compile(
    r"(?m)^(?:@\[[^\]\n]*\][ \t]+)?(?:public[ \t]+)?(?:noncomputable[ \t]+)?"
    r"(?P<kind>namespace|section|end)\b[ \t]*(?P<name>\S*)"
)
DOCSTRING = re.compile(r"/--(?P<text>(?:(?!-/).)*)-/\s*$", re.S)
# Module system: the header starts with `module`; `public import` re-exports the imported module.
MODULE_HEADER = re.compile(r"\s*module\b")
IMPORT = re.compile(
    r"(?m)^(?P<public>public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(?P<module>[\w.'₀-₉]+)"
)
PUBLIC_SECTION = re.compile(
    r"(?m)^(?P<expose>@\[expose\][ \t]+)?public[ \t]+(?:noncomputable[ \t]+)?section\b"
)
# A definition whose body downstream modules may unfold (not `private`).
DEFINITION = re.compile(
    r"(?m)^(?:@\[[^\n]*?\]\s*)?(?:public\s+)?(?:protected\s+)?(?:noncomputable\s+)?"
    r"(?:(?:scoped|local)\s+)?(?:def|abbrev|instance)\b"
)
# Top-level directories of the library, in index order, with a one-line description.
GROUPS = {
    "Foundations": "Vector calculus and scores, total variation, KL tools, Gaussian KL formulas, "
    "Gibbs measures, heat kernels, de Bruijn identity and Gaussian log-Sobolev inequality along "
    "the heat flow, log-Sobolev inequalities, Bakry–Émery, Prékopa–Leindler, weak derivatives, "
    "the bridge to Mathlib's `EuclideanSpace ℝ (Fin d)`.",
    "Identities": "Stein and Tweedie identities, weak generators, score propagation.",
    "Kernels": "Error propagation (per-step errors in TV or KL) and decomposition for inexact "
    "kernels, reverse kernels, Gaussian and OU kernels.",
    "Flow": "Continuity and Fokker–Planck equations (existence, uniqueness), reverse-time "
    "rewriting, KL dissipation and decay, OU flows, deterministic steps.",
    "ScoreEstimation": "Stein/Hyvärinen objective, feature classes, Monte Carlo posterior means.",
    "Samplers": "Gaussian-increment chains, MH/MALA, proximal sampler (also on "
    "`EuclideanSpace ℝ (Fin d)`), diffusion models (DDPM/DDIM), particles.",
    "Examples": "Closed-form Gaussian instances and tightness examples.",
    "Counterexamples": "Refutations of tempting general claims.",
    "Audit": "Statement audit: witnesses on non-degenerate instances for the registry rows.",
}
# Import layers: a module may import modules of its own or a lower layer only.
LAYERS = {
    "Foundations": 0,
    "Identities": 1,
    "Kernels": 1,
    "Flow": 2,
    "ScoreEstimation": 2,
    "Samplers": 3,
    "Examples": 4,
    "Counterexamples": 4,
    "Audit": 5,
}
CORE = "Core"  # FormalizeSampling/Core.lean imports exactly the modules of layers 0-2
CORE_LAYER = 2
SUMMARY_LENGTH = 140  # characters of a docstring kept in the index
# Tokens after which a period does not end a sentence.
ABBREVIATIONS = {"e.g", "i.e", "cf", "resp", "vs", "w.r.t", "a.e", "a.s", "al", "eq", "eqs"}


def without_comments(source: str) -> str:
    """Blank out nested Lean comments while preserving offsets and newlines."""
    result = list(source)
    depth, i = 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result[i : i + 2] = "  "
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result[i : i + 2] = "  "
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
        else:
            if depth and source[i] != "\n":
                result[i] = " "
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(result)


def qualified_names(clean: str) -> dict[int, str]:
    """Map the offset of each theorem or lemma in comment-free source to its full name.

    Tracks `namespace`/`section`/`end` blocks (dotted and nested namespaces, named, anonymous and
    `public` sections), declarations with dotted names (`theorem A.b` inside `namespace N` is
    `N.A.b`) and `_root_.` names. As in Lean, `namespace A.B` opens one scope per component and
    `end A.B` must close them; an `end` whose name does not match the open scopes is an error.
    """
    events = sorted(
        [(m.start(), "scope", m) for m in SCOPE.finditer(clean)]
        + [(m.start(), "decl", m) for m in PUBLIC.finditer(clean)],
        key=lambda event: event[0],
    )
    # Each open scope: (its name component, whether it is a namespace).
    stack: list[tuple[str, bool]] = []
    names: dict[int, str] = {}
    for start, kind, match in events:
        if kind == "decl":
            name = match["name"]
            if name.startswith("_root_."):
                names[start] = name.removeprefix("_root_.")
            else:
                prefix = [part for part, is_namespace in stack if is_namespace]
                names[start] = ".".join(prefix + [name])
        elif match["kind"] in ("namespace", "section"):
            parts = match["name"].split(".") if match["name"] else [""]
            stack += [(part, match["kind"] == "namespace") for part in parts]
        else:
            parts = match["name"].split(".") if match["name"] else [""]
            for part in reversed(parts):
                if not stack or stack[-1][0] != part:
                    raise ValueError(f"Unmatched `end` at offset {start}")
                stack.pop()
    return names


def sentence_end(text: str) -> int:
    """Offset just past the first sentence of `text`.

    Periods inside code spans, after abbreviations or not followed by a space do not end it.
    """
    in_code = False
    for i, char in enumerate(text):
        if char == "`":
            in_code = not in_code
        elif char == "." and not in_code:
            j = i + 1
            while j < len(text) and text[j] in "*_)":
                j += 1
            token = text[:i].rsplit(" ", 1)[-1].lstrip("([*").split("-")[-1].lower()
            if (j == len(text) or text[j] == " ") and token not in ABBREVIATIONS:
                return j
    return len(text)


def summary(doc: str, limit: int = SUMMARY_LENGTH) -> str:
    """Opening of a docstring for a table cell.

    The first sentence, followed by the second when the first is a bold heading
    (`**Pinsker's inequality.** For ...`); emphasis is removed, the text is shortened at a space
    outside code spans and `|` is escaped.
    """
    text = " ".join(doc.split())
    end = sentence_end(text)
    sentence = text[:end]
    if sentence.startswith("**") and sentence.endswith("**") and end < len(text):
        rest = text[end:].lstrip()
        sentence += " " + rest[: sentence_end(rest)]
    sentence = sentence.replace("**", "")
    if len(sentence) > limit:
        in_code, cut = False, 0
        for i, char in enumerate(sentence[:limit]):
            if char == "`":
                in_code = not in_code
            elif char == " " and not in_code:
                cut = i
        if cut:
            sentence = sentence[:cut].rstrip(" ,;:") + " …"
    return sentence.replace("|", "\\|")


def write_index(declarations: list[tuple[str, str, int, str]]) -> str:
    """Render docs/declaration_index.md, one table per top-level directory."""
    lines = [
        "# Declaration index",
        "",
        "Generated by `python3 scripts/check_contracts.py --write-index`. Every public theorem of",
        "the library, by fully qualified name, with the opening of its docstring (the first",
        "sentence, and the next one after a bold heading); the docstrings and signatures carry",
        "the exact hypotheses, and the [registry](theorem_registry.md) maps core theorem IDs to",
        "declarations. Reusable helper theorems are included.",
    ]
    groups: dict[str, list[tuple[str, str, int, str]]] = {}
    for declaration in declarations:
        parts = Path(declaration[0]).parts
        groups.setdefault(parts[1] if len(parts) > 2 else "", []).append(declaration)
    order = [g for g in GROUPS if g in groups] + sorted(set(groups) - set(GROUPS))
    for group in order:
        lines += ["", f"## {group or 'Top-level modules'}", ""]
        if group in GROUPS:
            lines += [GROUPS[group], ""]
        lines += ["| Declaration | Summary | Source |", "| --- | --- | --- |"]
        for path, name, line, text in groups[group]:
            label = Path(path).relative_to(Path(LIBRARY, group)).with_suffix("")
            lines.append(f"| `{name}` | {text} | [{label}:{line}](../{path}#L{line}) |")
    return "\n".join(lines) + "\n"


def imports_of(source: str, public_only: bool = False) -> list[str]:
    """Modules imported by a Lean source file (comments ignored); `public import`s only if asked."""
    try:
        clean = without_comments(source)
    except ValueError:
        clean = source
    return [m["module"] for m in IMPORT.finditer(clean) if m["public"] or not public_only]


def module_errors(relative: str, source: str, aggregator: bool) -> list[str]:
    """A library file must be a module; one with declarations must open a public section.

    In a module, declarations outside a `public section` (or without `public`) are private, so a
    missing `@[expose] public section` would hide the whole file from downstream modules; and
    the body of a definition outside an `@[expose]` section cannot be unfolded downstream, so a
    file with non-private definitions must use `@[expose] public section`. Files import the
    Mathlib modules they use rather than the whole of `Mathlib`.
    `aggregator` marks files that only re-export imports (the root and the core module).
    """
    try:
        clean = without_comments(source)
    except ValueError:
        return []  # reported with the other per-file checks
    if not MODULE_HEADER.match(clean):
        return [f"Not a Lean module (the file must start with `module`): {relative}"]
    if "Mathlib" in imports_of(source):
        return [f"Whole-library `import Mathlib` (import the modules used instead): {relative}"]
    if aggregator:
        return []
    sections = list(PUBLIC_SECTION.finditer(clean))
    if not sections:
        return [f"Module without `@[expose] public section` or `public section`: {relative}"]
    if DEFINITION.search(clean) and not any(m["expose"] for m in sections):
        return [f"Module with definitions but without `@[expose] public section`: {relative}"]
    return []


def layer(module: str) -> int | None:
    """Layer of a library module `FormalizeSampling.<Directory>.<Name>`, or `None`."""
    parts = module.split(".")
    if len(parts) < 3 or parts[0] != LIBRARY:
        return None
    return LAYERS.get(parts[1])


def layering_errors(imports: dict[str, list[str]]) -> list[str]:
    """Imports of a higher layer, and modules in directories without a layer."""
    errors = []
    for module, imported in sorted(imports.items()):
        if module == f"{LIBRARY}.{CORE}":
            continue
        own = layer(module)
        if own is None:
            errors.append(f"Module outside the layered directories: {module}")
            continue
        for target in imported:
            other = layer(target)
            if other is not None and other > own:
                errors.append(f"Upward import (layer {own} -> {other}): {module} imports {target}")
    return errors


def registry_rows(text: str) -> list[list[str]]:
    rows = []
    for line in text.splitlines():
        if ROW_ID.match(line):
            rows.append([cell.strip() for cell in line.split("|")[1:-1]])
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-index", action="store_true")
    args = parser.parse_args()
    errors: list[str] = []

    modules = sorted((ROOT / LIBRARY).rglob("*.lean"))
    module_names = {p: str(p.relative_to(ROOT).with_suffix("")).replace("/", ".") for p in modules}
    expected = set(module_names.values())
    root_file = ROOT / f"{LIBRARY}.lean"
    root_source = root_file.read_text()
    core = f"{LIBRARY}.{CORE}"
    errors += module_errors(root_file.name, root_source, aggregator=True)
    for path in modules:
        errors += module_errors(
            str(path.relative_to(ROOT)), path.read_text(), aggregator=module_names[path] == core
        )
    imports = set(imports_of(root_source, public_only=True))
    if imports != expected:
        errors.append(
            f"Export mismatch (public imports of {root_file.name}): "
            f"missing={sorted(expected - imports)}, extra={sorted(imports - expected)}"
        )

    module_imports = {module_names[p]: imports_of(p.read_text()) for p in modules}
    errors += layering_errors(module_imports)
    if core not in module_imports:
        errors.append(f"Missing core module {LIBRARY}/{CORE}.lean")
    else:
        lower = {m for m in expected if (layer(m) is not None and layer(m) <= CORE_LAYER)}
        core_path = ROOT / LIBRARY / f"{CORE}.lean"
        core_imports = set(imports_of(core_path.read_text(), public_only=True))
        if core_imports != lower:
            errors.append(
                f"Core mismatch: missing={sorted(lower - core_imports)}, "
                f"extra={sorted(core_imports - lower)}"
            )

    declarations: list[tuple[str, str, int, str]] = []
    for path in modules:
        source = path.read_text()
        relative = str(path.relative_to(ROOT))
        clean = without_comments(source)
        if FORBIDDEN.search(clean):
            errors.append(f"Uncertified construct in {relative}")
        if OVERRIDES.search(clean):
            errors.append(f"Trust-boundary override in {relative}")
        if "/-!" not in source:
            errors.append(f"Missing module docstring: {relative}")
        try:
            names = qualified_names(clean)
        except ValueError as error:
            errors.append(f"{error} in {relative}")
            continue
        for match in PUBLIC.finditer(clean):
            if match["private"]:
                continue
            line = source.count("\n", 0, match.start()) + 1
            doc = DOCSTRING.search(source[: match.start()])
            if not doc:
                errors.append(f"Public theorem without adjacent docstring: {relative}:{line}")
            summary_text = summary(doc["text"]) if doc else ""
            declarations.append((relative, names[match.start()], line, summary_text))

    registry_path = ROOT / REGISTRY
    rows = registry_rows(registry_path.read_text()) if registry_path.exists() else []
    if not rows:
        errors.append(f"No registry rows found in {REGISTRY}")
    ids = [row[0] for row in rows]
    duplicates = sorted({i for i in ids if ids.count(i) > 1})
    if duplicates:
        errors.append(f"Duplicate registry IDs: {duplicates}")
    missing = sorted(REQUIRED_IDS - set(ids))
    if missing:
        errors.append(f"Registry is missing roadmap IDs: {missing}")
    for row in rows:
        if len(row) != COLUMNS:
            errors.append(f"Registry row must have {COLUMNS} columns: {row[0]}")
            continue
        if row[0] not in REQUIRED_IDS and not EXTRA_ID.match(row[0]):
            errors.append(f"Unknown registry ID: {row[0]}")
        status = row[1]
        if status not in STATUSES:
            errors.append(f"Invalid status {status!r}: {row[0]}")
        names = re.findall(rf"`({LIBRARY}\.[\w.'₀-₉]+)`", row[3])
        if status in CERTIFIED and not names:
            errors.append(f"{status} row without a Lean declaration: {row[0]}")
        if status not in CERTIFIED and names:
            errors.append(f"{status} row must not cite certified declarations: {row[0]}")
        # AxiomAudit.lean resolves every cited name in Lean's environment.

    expected_index = write_index(declarations)
    index_path = ROOT / INDEX
    if args.write_index:
        index_path.write_text(expected_index)
    elif not index_path.exists() or index_path.read_text() != expected_index:
        errors.append("Declaration index is stale; run with --write-index")

    texts = [*modules, *ROOT.glob("*.md"), *ROOT.joinpath("docs").rglob("*.md")]
    for path in texts:
        for line, text in enumerate(path.read_text().splitlines(), 1):
            if text.rstrip() != text:
                errors.append(f"Trailing whitespace: {path.relative_to(ROOT)}:{line}")
    for path in modules:
        for line, text in enumerate(path.read_text().splitlines(), 1):
            if len(text) > 100:
                errors.append(f"Line longer than 100 characters: {path.relative_to(ROOT)}:{line}")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    certified = sum(1 for row in rows if len(row) == COLUMNS and row[1] in CERTIFIED)
    print(
        f"Contracts passed: {len(modules)} exported modules, {len(declarations)} documented "
        f"theorems, {len(rows)} registry rows ({certified} certified)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
