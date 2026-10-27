#!/usr/bin/env python3
"""Check proof-source hygiene, module headers, complete exports, the import layering, the
theorem registry, and the public documentation against the registry and the sources.

Every library file is a Lean module (`module` header, Mathlib's conventions); the root
`FormalizeSampling.lean` and `FormalizeSampling/Core.lean` re-export their modules with
`public import`. This source checker complements the Lean kernel and the transitive axiom audit
(scripts/AxiomAudit.lean, which also resolves the Lean names cited in the documentation); it
replaces neither. --extract-examples DIR writes the README's Lean examples (the ```lean blocks
that start with `import`) to DIR, one file each, so that they can be compiled with `lake env lean`.

Generated documentation; a stale copy is an error, and --write (alias --write-index) refreshes it:
- docs/declaration_index.md: fully qualified theorem names with the opening of their docstrings,
  grouped by top-level directory, and at the head of its Audit section a table of the witness
  modules with the registry rows each covers (the `Rows:` line of the module docstring) and the
  docstring title;
- the README coverage table, one row per `## ` section of the registry, with the row IDs and
  status counts;
- the README Layout table of the library directories and the layering paragraph, from GROUPS,
  LAYERS and CORE_LAYER.
The README blocks lie between `<!-- BEGIN GENERATED: name -->` and `<!-- END GENERATED: name -->`.

The documentation checks read an explicit list of public files (DOC_FILES): registry IDs are
contiguous per prefix and every ID mentioned exists (in the documents, the library and the Python
illustrations); status words next to IDs agree with the registry; the README counts sentence,
moves table, literature map and Statuses section agree with the registry, the sources and
docs/literature.md; docs/results.md has one bullet per registry row, in registry order, with the
row's title and status mark; registry rows start with a bold title, cite documented theorems and
list their modules; relative links and their anchors resolve. No phrase of BANNED_PHRASES (the
wording rules) occurs in these files, in the other docs/*.md files except the declaration index,
or in the Lean sources.
"""

from __future__ import annotations

import argparse
import re
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "FormalizeSampling"
REGISTRY = "docs/theorem_registry.md"
INDEX = "docs/declaration_index.md"
README = "README.md"
RESULTS = "docs/results.md"
LITERATURE = "docs/literature.md"
# The public Markdown files checked against the registry, the sources and each other (a missing
# file is skipped); scripts/AxiomAudit.lean resolves their Lean names. Other Markdown files, such
# as notes kept outside the public repository, are not read.
DOC_FILES = (
    README,
    "CONTRIBUTING.md",
    RESULTS,
    LITERATURE,
    "docs/statement_audit.md",
    "docs/glossary.md",
    REGISTRY,
    "showcase/README.md",
    "experiments/README.md",
)
REQUIRED_DOCS = (README, RESULTS, LITERATURE)
# The directories of the Python illustrations, whose IDs are checked like those of the documents.
ILLUSTRATIONS = ("showcase", "experiments")
# Registry IDs: a two-letter prefix and a number, numbered 1, 2, ... within each prefix.
ROW_ID = re.compile(r"^\| (?P<id>(?:[A-Z]{2}-\d+|CE-\d{2})) \|")
# docs/results.md has one bullet per registry ID, in registry order, under the `## ` heading of
# the ID's registry section, led by the row's bold title and the ID (`- **Pinsker (KL-1).** ...`
# for the Statement cell `**Pinsker.** ...`).
RESULTS_ONE_BULLET_PER_ID = True
BULLET_LEAD = re.compile(r"^- \*\*(?P<lead>.+?)\*\*")
# The bold short title that starts the Statement cell of every certified registry row.
REGISTRY_TITLE = re.compile(r"\*\*(?P<title>[^*]+?)\.\*\*")
# The section, in the registry and in docs/results.md, of the Counterexample rows.
COUNTEREXAMPLES = "Counterexamples"
# The README counts sentence; every space may be a line break.
COUNTS = re.compile(
    r"About\s+(?P<lines>[\d,]+)\s+lines\s+of\s+Lean,\s+(?P<theorems>[\d,]+)\s+documented\s+"
    r"theorems\s+and\s+(?P<rows>\d+)\s+core\s+results:\s+(?P<Verified>\d+)\s+Verified,\s+"
    r"(?P<Counterexample>\d+)\s+formal\s+counterexamples,\s+(?P<Conditional>\d+)\s+Conditional\."
)
URL = re.compile(r"https?://[^\s)\]>]+")
LINK = re.compile(r"\]\((?P<target>[^)\s]+)(?:\s+\"[^\"]*\")?\)")  # inline links and images
STATUSES = ("Verified", "Conditional", "Counterexample", "Planned", "Open")  # in display order
CERTIFIED = {"Verified", "Conditional", "Counterexample"}
# A status word in italics (`*Conditional*`), the way docs/results.md marks a bullet.
STATUS_MARK = re.compile(rf"\*({'|'.join(STATUSES)})\*")
# Phrases that the wording rules exclude from the public text and the Lean sources (docstrings and
# comments): a cited work is credited only for what is formalised, with no priority claims.
# Matched case-insensitively; every space may be a line break.
BANNED_PHRASES = (
    "we have not found",
    "not found before",
    "to our knowledge",
    "rather than the paper",
    "paper states none",
    "stronger than the paper",
    "weaker than the paper",
    "novel",
)
BANNED = re.compile(
    "|".join(r"\s+".join(map(re.escape, phrase.split())) for phrase in BANNED_PHRASES), re.I
)
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
# Top-level directories of the library, in index order, with a one-line description: the only
# source of these descriptions (the index headings and the README Layout table).
GROUPS = {
    "Foundations": "Vector calculus and scores, total variation, KL tools, Gaussian KL formulas, "
    "Gibbs measures, heat kernels, de Bruijn identity and Gaussian log-Sobolev inequality along "
    "the heat flow, log-Sobolev inequalities, Bakry–Émery, Prékopa–Leindler, weak derivatives, "
    "the bridge to Mathlib's `EuclideanSpace ℝ (Fin d)`.",
    "Identities": "Gaussian and density Stein identities, Tweedie's formula and posterior scores, "
    "weak generators, score propagation, first variation of KL under transport.",
    "Kernels": "TV error propagation (per-step errors in TV or KL) and decomposition for inexact "
    "kernels, reverse (Bayes) kernels, Gaussian and OU kernels, finite products of kernels.",
    "Flow": "Continuity and Fokker–Planck equations (existence, uniqueness), reverse-time "
    "rewriting, KL dissipation and decay, OU flows, deterministic steps.",
    "ScoreEstimation": "Stein/Hyvärinen objective, feature classes, Monte Carlo posterior means.",
    "Samplers": "Gaussian-increment chains and random score oracles, MH/MALA, proximal sampler "
    "(heat-flow and backward analysis; also on `EuclideanSpace ℝ (Fin d)`), diffusion models "
    "(DDPM/DDIM), particles.",
    "Examples": "Closed-form Gaussian instances and tightness examples.",
    "Counterexamples": "Refutations of tempting general claims.",
    "Audit": "Statement audit: Lean witnesses on non-degenerate instances for every registry row.",
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
NUMBERS = ("no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine")
# The witness modules. Each module docstring starts with the title `# Statement audit: <summary>`
# and has a line `Rows: KL-1, KL-2.` listing the registry rows the module witnesses.
AUDIT = "Audit"
AUDIT_TITLE = re.compile(r"# Statement audit: (?P<summary>\S.*)")
# The `Rows:` line starts at column 0 and ends with a period, with the IDs separated by `, `, as
# scripts/AxiomAudit.lean reads it (`rowsLine`).
AUDIT_ROWS = re.compile(r"Rows: (?P<ids>[^,.\s]+(?:, [^,.\s]+)*)\.")
# Marker lines around the generated blocks of the README.
MARKER = "<!-- {} GENERATED: {} -->"
WIDTH = 100  # line width of generated paragraphs
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


def write_index(
    declarations: list[tuple[str, str, int, str]], witnesses: list[str] | None = None
) -> str:
    """Render docs/declaration_index.md, one table per top-level directory; the Audit section
    starts with the table `witnesses` of the witness modules (see `audit_table`)."""
    lines = [
        "# Declaration index",
        "",
        "Generated by `python3 scripts/check_contracts.py --write`. Every public theorem of",
        "the library, by fully qualified name, with the opening of its docstring (the first",
        "sentence, and the next one after a bold heading); the docstrings and signatures carry",
        "the exact hypotheses, and the [registry](theorem_registry.md) maps core theorem IDs to",
        "declarations. Reusable helper theorems are included. The [Audit](#audit) section",
        "starts with the witness modules of the statement audit and the rows each one covers.",
    ]
    groups: dict[str, list[tuple[str, str, int, str]]] = {}
    for declaration in declarations:
        parts = Path(declaration[0]).parts
        groups.setdefault(parts[1] if len(parts) > 2 else "", []).append(declaration)
    if witnesses:
        groups.setdefault(AUDIT, [])
    order = [g for g in GROUPS if g in groups] + sorted(set(groups) - set(GROUPS))
    for group in order:
        lines += ["", f"## {group or 'Top-level modules'}", ""]
        if group in GROUPS:
            lines += [GROUPS[group], ""]
        if group == AUDIT and witnesses:
            lines += [
                "Witness modules, with the registry rows each one covers (the `Rows:` line of its",
                "module docstring) and the title of that docstring:",
                "",
                *witnesses,
                "",
            ]
        if not groups[group]:
            lines.pop()  # no declarations: drop the blank line before the table
            continue
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


def id_pattern(ids: list[str]) -> str:
    """Regex of ID tokens with a registry prefix; tokens with other prefixes are not IDs."""
    prefixes = sorted({rid.split("-")[0] for rid in ids})
    return rf"\b(?:{'|'.join(prefixes) or '(?!)'})-\d+\b"


def cited_ids(text: str, pattern: str) -> list[str]:
    """ID tokens of `text`, plus the IDs inside same-prefix ranges such as `KL-1 … KL-4`."""
    found = re.findall(pattern, text)
    for first, last in re.findall(rf"({pattern})\s*(?:…|\.\.\.?|–)\s*({pattern})", text):
        prefix, start = first.split("-")
        other, stop = last.split("-")
        if other == prefix:
            found += [f"{prefix}-{i:0{len(start)}d}" for i in range(int(start) + 1, int(stop))]
    return found


def contiguity_errors(ids: list[str]) -> list[str]:
    """Within each prefix the registry numbers its rows 1, 2, ..., n."""
    numbers: dict[str, list[int]] = {}
    for rid in ids:
        prefix, number = rid.split("-")
        numbers.setdefault(prefix, []).append(int(number))
    return [
        f"Registry IDs {prefix}-* are not numbered 1 to {len(found)}: {sorted(found)}"
        for prefix, found in sorted(numbers.items())
        if sorted(found) != list(range(1, len(found) + 1))
    ]


def id_ranges(ids: list[str]) -> str:
    """IDs as ranges: runs of three or more consecutive numbers of one prefix become
    `KL-1 … KL-4`, shorter runs are listed (`GI-1, GI-2`)."""
    runs: list[list[str]] = []
    for rid in ids:
        prefix, number = rid.split("-")
        last = runs[-1][-1].split("-") if runs else None
        if last and last[0] == prefix and int(last[1]) + 1 == int(number):
            runs[-1].append(rid)
        else:
            runs.append([rid])
    return ", ".join(f"{run[0]} … {run[-1]}" if len(run) > 2 else ", ".join(run) for run in runs)


def registry_areas(text: str) -> tuple[list[tuple[str, list[str]]], list[str]]:
    """The `## ` sections of the registry, in order, with the IDs of their rows; and errors for
    rows outside a section, empty sections and repeated headings."""
    areas: list[tuple[str, list[str]]] = []
    errors = []
    for line in text.splitlines():
        if line.startswith("## "):
            heading = line[3:].strip()
            if any(heading == area for area, _ in areas):
                errors.append(f"Registry section {heading!r} appears twice")
            areas.append((heading, []))
        match = ROW_ID.match(line)
        if match and not areas:
            errors.append(f"Registry row {match['id']} is not under a `## ` section")
        elif match:
            areas[-1][1].append(match["id"])
    errors += [f"Registry section {area!r} has no rows" for area, ids in areas if not ids]
    return areas, errors


def coverage_table(areas: list[tuple[str, list[str]]], statuses: dict[str, str]) -> str:
    """The README coverage table: one row per registry section, with its IDs and status counts."""
    lines = ["| Area | Registry rows | Status |", "|---|---|---|"]
    for area, ids in areas:
        found = [statuses.get(rid) for rid in ids]
        counts = ", ".join(
            f"{found.count(status)} {status}" for status in STATUSES if status in found
        )
        lines.append(f"| {area} | {id_ranges(ids)} | {counts} |")
    return "\n".join(lines)


def wrap(text: str, width: int = WIDTH) -> str:
    """Fill a paragraph to `width` columns, breaking only at spaces outside code spans."""
    words, word, in_code = [], "", False
    for char in text:
        in_code ^= char == "`"
        if char == " " and not in_code:
            words += [word] if word else []
            word = ""
        else:
            word += char
    lines = [""]
    for word in [*words, word] if word else words:
        if lines[-1] and len(lines[-1]) + 1 + len(word) > width:
            lines.append(word)
        else:
            lines[-1] = f"{lines[-1]} {word}" if lines[-1] else word
    return "\n".join(lines)


def layout_block() -> str:
    """The README Layout table of the library directories and the layering paragraph, from
    GROUPS, LAYERS and CORE_LAYER."""
    core = [group for group in GROUPS if LAYERS.get(group, CORE_LAYER + 1) <= CORE_LAYER]
    names = [f"`{group}`" for group in core]
    listed = " and ".join([", ".join(names[:-1]), names[-1]] if len(names) > 1 else names)
    entry = (
        "Entry points: the first imports the whole library, the second the sampler-independent "
        f"core ({', '.join(names)})"
    )
    rows = [
        "| Directory | Contents |",
        "|---|---|",
        f"| `{LIBRARY}.lean`, `{LIBRARY}/{CORE}.lean` | {entry} |",
        *(f"| `{LIBRARY}/{group}/` | {text.removesuffix('.')} |" for group, text in GROUPS.items()),
    ]
    levels = sorted(set(LAYERS.values()))
    order = " < ".join(
        ", ".join(f"`{group}`" for group in GROUPS if LAYERS.get(group) == level)
        for level in levels
    )
    lowest = NUMBERS[len([level for level in levels if level <= CORE_LAYER])]
    paragraph = (
        "The directories are layered: a module imports only modules of its own or a lower layer, "
        f"in the order {order} (checked by `scripts/check_contracts.py`). `{LIBRARY}/{CORE}.lean` "
        f"imports every module of {listed} (the {lowest} lowest layers), the sampler-independent "
        f"core; `{LIBRARY}.lean` imports everything. Every file is a Lean module, so both modules "
        f"(`public import {LIBRARY}.{CORE}`) and ordinary Lean files can import the library."
    )
    return "\n".join(rows) + "\n\n" + wrap(paragraph)


def replace_block(text: str, name: str, body: str) -> str | None:
    """`text` with the generated block `name` (between its marker lines) set to `body`; `None`
    if the markers are missing, repeated or out of order."""
    begin, end = MARKER.format("BEGIN", name), MARKER.format("END", name)
    if text.count(begin) != 1 or text.count(end) != 1:
        return None
    start, stop = text.index(begin) + len(begin), text.index(end)
    if stop < start:
        return None
    return f"{text[:start]}\n\n{body}\n\n{text[stop:]}"


def audit_header(source: str) -> tuple[str, list[str]] | None:
    """The fixed header of a witness module's docstring (the first `/-! ... -/` block): the
    summary of its title `# Statement audit: <summary>` (the first line) and the IDs of its one
    `Rows:` line, which must start at column 0 and fit on one line, as scripts/AxiomAudit.lean
    reads it."""
    doc = re.search(r"/-!(.*?)-/", source, re.S)
    lines = doc[1].strip().splitlines() if doc else []
    title = AUDIT_TITLE.fullmatch(lines[0].strip()) if lines else None
    rows = [line.rstrip() for line in lines if line.lstrip().startswith("Rows:")]
    match = AUDIT_ROWS.fullmatch(rows[0]) if len(rows) == 1 else None
    if not title or not match:
        return None
    return title["summary"], match["ids"].split(", ")


def audit_errors(headers: dict[str, tuple[str, list[str]] | None], ids: list[str]) -> list[str]:
    """Every witness module has the fixed header, its `Rows:` line lists registry IDs, and every
    registry ID is listed by some witness module."""
    errors, listed = [], set()
    for relative, header in headers.items():
        if header is None:
            errors.append(
                "Witness module docstring without the title `# Statement audit: <summary>` and "
                f"one unindented, one-line `Rows: <IDs>.` line: {relative}"
            )
            continue
        for rid in sorted(set(header[1])):
            if rid not in ids:
                errors.append(f"{relative}: Rows line lists {rid!r}, which is no registry row")
            elif header[1].count(rid) > 1:
                errors.append(f"{relative}: Rows line lists {rid} twice")
        listed |= set(header[1])
    errors += [
        f"Registry row {rid} is in no witness module's Rows line"
        for rid in ids
        if rid not in listed
    ]
    return errors


def audit_table(headers: dict[str, tuple[str, list[str]]], ids: list[str]) -> list[str]:
    """The table of the witness modules (Module | Rows | Summary), ordered by the registry
    position of each module's first row."""
    position = {rid: i for i, rid in enumerate(ids)}

    def order(relative: str) -> tuple[int, str]:
        first = min((position.get(rid, len(ids)) for rid in headers[relative][1]), default=0)
        return first, relative

    lines = ["| Module | Rows | Summary |", "| --- | --- | --- |"]
    for relative in sorted(headers, key=order):
        title, listed = headers[relative]
        known = sorted((rid for rid in set(listed) if rid in position), key=position.__getitem__)
        label = Path(relative).relative_to(Path(LIBRARY, AUDIT)).with_suffix("")
        cell = title.replace("|", "\\|")
        lines.append(f"| [{label}](../{relative}) | {id_ranges(known)} | {cell} |")
    return lines


def without_fences(text: str) -> str:
    """Blank out fenced code blocks, keeping line numbers."""
    lines, fenced = [], False
    for line in text.splitlines():
        fence = line.lstrip().startswith("```")
        lines.append("" if fenced or fence else line)
        fenced ^= fence
    return "\n".join(lines)


def heading_level(line: str) -> int:
    """Level of an ATX heading line (`## Title` is 2), or 0."""
    level = len(line) - len(line.lstrip("#"))
    return level if 0 < level <= 6 and line[level : level + 1] == " " else 0


def section(text: str, heading: str) -> str | None:
    """Body of the section with heading line `heading` (such as `## Statuses`), up to the next
    heading of the same or a higher level; `None` if there is no such heading."""
    lines = without_fences(text).splitlines()
    if heading not in lines:
        return None
    body = []
    for line in lines[lines.index(heading) + 1 :]:
        if 0 < heading_level(line) <= heading_level(heading):
            break
        body.append(line)
    return "\n".join(body)


def table_cells(line: str) -> list[str]:
    """Cells of a Markdown table row, split at each `|` that is not escaped or in code."""
    cells, cell, in_code, previous = [], "", False, ""
    for char in line.strip().removeprefix("|").removesuffix("|"):
        in_code ^= char == "`"
        if char == "|" and not in_code and previous != "\\":
            cells.append(cell.strip())
            cell = ""
        else:
            cell += char
        previous = char
    return [*cells, cell.strip()]


def table_rows(text: str, header: str) -> list[list[str]] | None:
    """Cells of the body rows of the first table whose header row starts with `header`."""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith(header):
            rows = []
            for row in lines[i + 2 :]:
                if not row.startswith("|"):
                    break
                rows.append(table_cells(row))
            return rows
    return None


def counts_errors(readme: str, statuses: list[str], lines: int, theorems: int) -> list[str]:
    """The README counts sentence: Lean lines floored to a multiple of 1000, documented theorems
    floored to a multiple of 100, and the exact numbers of registry rows and of each status."""
    match = COUNTS.search(readme)
    if not match:
        return [f"No counts sentence (About N lines of Lean, ...) in {README}"]
    expected = {
        "lines": lines // 1000 * 1000,
        "theorems": theorems // 100 * 100,
        "rows": len(statuses),
        **{status: statuses.count(status) for status in sorted(CERTIFIED)},
    }
    claimed = {key: int(value.replace(",", "")) for key, value in match.groupdict().items()}
    return [
        f"Stale {README} counts sentence: {claimed[key]:,} {key}, expected {value:,}"
        for key, value in expected.items()
        if claimed[key] != value
    ]


def unknown_id_errors(texts: dict[str, str], ids: list[str], pattern: str) -> list[str]:
    """Every ID token (with a registry prefix) names a registry row."""
    return [
        f"Unknown registry ID {rid} in {relative}"
        for relative, text in texts.items()
        for rid in sorted(set(cited_ids(text, pattern)) - set(ids))
    ]


def moves_table_errors(readme: str, ids: list[str], pattern: str) -> list[str]:
    """Every registry ID appears exactly once in the last column of the README moves table."""
    rows = table_rows(readme, "| Move |")
    if rows is None:
        return [f"No moves table (| Move | ... | Registry IDs |) in {README}"]
    seen = [rid for row in rows for rid in set(cited_ids(row[-1], pattern))]
    return [
        f"{README} moves table lists {rid} {seen.count(rid)} times, not once"
        for rid in ids
        if seen.count(rid) != 1
    ]


def results_bullets(results: str) -> list[tuple[str, str, str]]:
    """The bullets of docs/results.md with a bold lead (`- **Pinsker (KL-1).** ...`), in order:
    the `## ` heading above the bullet, the lead, and the bullet's text up to the next unindented
    or blank line."""
    bullets: list[list[str]] = []
    heading, current = "", None
    for line in without_fences(results).splitlines():
        if heading_level(line) == 2:
            heading = line[3:].strip()
        match = BULLET_LEAD.match(line)
        if match:
            current = [heading, match["lead"], line]
            bullets.append(current)
        elif current is not None and line.startswith(" ") and line.strip():
            current[2] += "\n" + line
        else:
            current = None
    return [(heading, lead, text) for heading, lead, text in bullets]


def results_bullet_errors(
    results: str, rows: list[list[str]], sections: dict[str, str], pattern: str
) -> list[str]:
    """docs/results.md has one bullet per registry ID, in registry order, under the `## ` heading
    of the ID's registry section, led by the row's bold title and the ID alone (`- **Pinsker
    (KL-1).** ...` for the Statement cell `**Pinsker.** ...`). Status marks follow the registry:
    a bullet says `*Conditional*` exactly when its row is Conditional, names no other status in
    italics, and sits under `## Counterexamples` if its row is a Counterexample; no Verified or
    Conditional row does."""
    status = {row[0]: row[1] for row in rows}
    titles = {row[0]: match["title"] for row in rows if (match := REGISTRY_TITLE.match(row[2]))}
    errors, placed, order = [], {}, []
    for heading, lead, text in results_bullets(results):
        leads = sorted(set(cited_ids(lead, pattern)))
        if len(leads) > 1:
            errors.append(f"{RESULTS} bullet led by several IDs: {', '.join(leads)}")
        for rid in leads:
            placed.setdefault(rid, []).append(heading)
        if len(leads) != 1 or leads[0] not in status:
            continue
        rid = leads[0]
        order.append(rid)
        if rid in titles and lead != f"{titles[rid]} ({rid}).":
            errors.append(
                f"{RESULTS} bullet {rid} is led by {lead!r}, not by the registry title "
                f"{titles[rid] + f' ({rid}).'!r}"
            )
        marks = set(STATUS_MARK.findall(text))
        if (status[rid] == "Conditional") != ("Conditional" in marks):
            errors.append(
                f"{RESULTS} bullet {rid} {'lacks' if status[rid] == 'Conditional' else 'has'} "
                f"the mark *Conditional*; the registry says {status[rid]}"
            )
        errors += [
            f"{RESULTS} bullet {rid} is marked *{word}*; the registry says {status[rid]}"
            for word in sorted(marks - {"Conditional", status[rid]})
        ]
        if status[rid] == "Counterexample" and heading != COUNTEREXAMPLES:
            errors.append(f"{RESULTS} Counterexample bullet {rid} is not under {COUNTEREXAMPLES!r}")
        if status[rid] in {"Verified", "Conditional"} and heading == COUNTEREXAMPLES:
            errors.append(
                f"{RESULTS} bullet {rid} is under {COUNTEREXAMPLES!r}; "
                f"the registry says {status[rid]}"
            )
    for rid, area in sections.items():
        found = placed.get(rid, [])
        if len(found) != 1:
            errors.append(f"{RESULTS} has {len(found)} bullets led by {rid}, not one")
        elif found[0] != area:
            errors.append(f"{RESULTS} bullet {rid} is under {found[0]!r}, not {area!r}")
    first = list(dict.fromkeys(order))
    expected = [row[0] for row in rows if row[0] in first]
    for listed, wanted in zip(first, expected):
        if listed != wanted:
            errors.append(f"{RESULTS} bullet {listed} is out of registry order ({wanted} first)")
            break
    return errors


def status_word_errors(texts: dict[str, str], statuses: dict[str, str], pattern: str) -> list[str]:
    """Status words next to IDs agree with the registry: `KL-1, KL-2 Verified`,
    `PX-3 … PX-6 (Verified)`, `FL-4 is Conditional`, `Conditional on the LSI (PX-2)`."""
    words = "|".join(sorted(CERTIFIED))
    ids = rf"{pattern}(?:(?:,\s+|\s+and\s+|\s*…\s*|,\s+and\s+){pattern})*"
    after = re.compile(rf"({ids})\s*(?:is\s+)?\(?\*?({words})\b")
    before = re.compile(rf"\b({words})[^|\n]{{0,12}}?\(({ids})")
    errors = []
    for relative, text in texts.items():
        pairs = [(m[1], m[2]) for m in after.finditer(text)]
        pairs += [(m[2], m[1]) for m in before.finditer(text)]
        for listed, word in pairs:
            for rid in sorted(set(cited_ids(listed, pattern))):
                if rid in statuses and statuses[rid] != word:
                    errors.append(
                        f"{relative} calls {rid} {word}; the registry says {statuses[rid]}"
                    )
    return errors


def literature_map_errors(readme: str, literature: str, pattern: str) -> list[str]:
    """The README literature map and the `### ` sections of docs/literature.md correspond one to
    one by URL (the first URL of each section), and each ID in a map row's status cell occurs
    in the sections of its works."""
    body = section(readme, "## Literature map")
    rows = table_rows(body or "", "| Work |")
    if rows is None:
        return [f"No literature map table (## Literature map, | Work | ...) in {README}"]
    errors, sections = [], {}
    parts = re.split(r"(?m)^(?=#{1,3} )", without_fences(literature))
    for part in (part.removeprefix("### ") for part in parts if part.startswith("### ")):
        title = part.splitlines()[0]
        url = URL.search(part)
        if not url:
            errors.append(f"{LITERATURE} section {title!r} has no URL")
        elif url[0] in sections:
            errors.append(f"{LITERATURE} sections share the URL {url[0]}")
        else:
            sections[url[0]] = set(cited_ids(part, pattern))
    mapped = []
    for row in rows:
        urls = URL.findall(row[0])
        mapped += urls
        allowed = set().union(*(sections.get(url, set()) for url in urls))
        for rid in sorted(set(cited_ids(row[-1], pattern)) - allowed):
            errors.append(f"{README} literature map row {row[0][:40]!r}: {rid} is not in its works")
    errors += [
        f"{README} literature map lists {url} twice"
        for url in sorted({url for url in mapped if mapped.count(url) > 1})
    ]
    errors += [
        f"{README} literature map lists {url}, which has no section in {LITERATURE}"
        for url in sorted(set(mapped) - set(sections))
    ]
    errors += [
        f"{LITERATURE} section of {url} has no row in the {README} literature map"
        for url in sorted(set(sections) - set(mapped))
    ]
    return errors


def registry_declaration_errors(rows: list[list[str]], declared_in: dict[str, str]) -> list[str]:
    """Registry rows cite documented public theorems (listed in the declaration index), and
    their Module column lists, as paths under FormalizeSampling/ without `.lean` (globs such as
    `Samplers/DiffusionVariance*` allowed), existing files that include the source file of every
    cited declaration."""
    errors = []
    for row in rows:
        listed: set[str] = set()
        for entry in re.findall(r"`([^`]+)`", row[5]):
            found = sorted((ROOT / LIBRARY).glob(f"{entry}.lean"))
            if not found:
                errors.append(f"{row[0]}: Module column lists {entry}, which is no library file")
            listed |= {str(path.relative_to(ROOT)) for path in found}
        for name in re.findall(rf"`({LIBRARY}\.[\w.'₀-₉]+)`", row[3]):
            if name not in declared_in:
                errors.append(f"{row[0]}: {name} is not a documented public theorem")
            elif declared_in[name] not in listed:
                module = Path(declared_in[name]).relative_to(LIBRARY).with_suffix("")
                errors.append(f"{row[0]}: Module column misses {module} (declares {name})")
    return errors


def statuses_section_errors(readme: str) -> list[str]:
    """The README `## Statuses` section defines exactly STATUSES, as `` - `Name`: ... `` items."""
    body = section(readme, "## Statuses")
    if body is None:
        return [f"No ## Statuses section in {README}"]
    listed = re.findall(r"(?m)^- `(\w+)`", body)
    if sorted(listed) != sorted(STATUSES):
        return [f"{README} Statuses section lists {listed}, not {sorted(STATUSES)}"]
    return []


def slug(heading: str) -> str:
    """GitHub's anchor for a heading: the rendered text in lower case, keeping letters, digits,
    `_`, `-` and spaces, with spaces turned into `-`."""
    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", heading)
    text = text.replace("`", "").replace("*", "").replace("$", "").lower()
    kept = (c for c in text if c in " -_" or unicodedata.category(c)[0] in "LMN")
    return "".join(kept).replace(" ", "-")


def anchors(text: str) -> set[str]:
    """Anchors of the headings of a Markdown text; repeated slugs get `-1`, `-2`, ..."""
    found: set[str] = set()
    for line in without_fences(text).splitlines():
        level = heading_level(line)
        if level:
            base = slug(line[level:].strip().rstrip("#").strip())
            anchor, n = base, 0
            while anchor in found:
                n += 1
                anchor = f"{base}-{n}"
            found.add(anchor)
    return found


def link_errors(texts: dict[str, str]) -> list[str]:
    """Relative links resolve to files of the repository, and their `#anchors` to headings."""
    errors = []
    for relative, text in texts.items():
        for match in LINK.finditer(without_fences(text)):
            target = match["target"]
            if re.match(r"[a-z]+:", target):
                continue
            path, _, anchor = target.partition("#")
            file = ((ROOT / relative).parent / path if path else ROOT / relative).resolve()
            if not file.is_relative_to(ROOT.resolve()) or not file.exists():
                errors.append(f"Broken link in {relative}: {target}")
            elif anchor and file.suffix == ".md" and anchor not in anchors(file.read_text()):
                errors.append(f"Broken anchor in {relative}: {target}")
    return errors


def banned_phrase_errors(texts: dict[str, str]) -> list[str]:
    """No text contains a phrase of BANNED_PHRASES, in any case, also across a line break."""
    errors = []
    for relative, text in texts.items():
        for match in BANNED.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            errors.append(f"Banned phrase {' '.join(match[0].split())!r}: {relative}:{line}")
    return errors


def readme_examples(readme: str) -> list[str]:
    """The README's ```lean blocks that start with `import`: complete Lean files."""
    blocks = re.findall(r"(?ms)^```lean\n(.*?)^```", readme)
    return [block for block in blocks if block.startswith("import ")]


def extract_examples(directory: Path) -> int:
    """Write the README's Lean examples to `directory` as `ReadmeExample<n>.lean`."""
    examples = readme_examples((ROOT / README).read_text())
    if not examples:
        print(f"No ```lean block starting with `import` in {README}", file=sys.stderr)
        return 1
    directory.mkdir(parents=True, exist_ok=True)
    for number, example in enumerate(examples, 1):
        path = directory / f"ReadmeExample{number}.lean"
        path.write_text(example)
        print(path)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", "--write-index", action="store_true", dest="write")
    parser.add_argument("--extract-examples", metavar="DIR", type=Path)
    args = parser.parse_args()
    if args.extract_examples:
        return extract_examples(args.extract_examples)
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
    registry = registry_path.read_text() if registry_path.exists() else ""
    rows = registry_rows(registry)
    if not rows:
        errors.append(f"No registry rows found in {REGISTRY}")
    ids = [row[0] for row in rows]
    duplicates = sorted({i for i in ids if ids.count(i) > 1})
    if duplicates:
        errors.append(f"Duplicate registry IDs: {duplicates}")
    errors += contiguity_errors(ids)
    complete = [row for row in rows if len(row) == COLUMNS]
    for row in rows:
        if len(row) != COLUMNS:
            errors.append(f"Registry row must have {COLUMNS} columns: {row[0]}")
            continue
        status = row[1]
        if status not in STATUSES:
            errors.append(f"Invalid status {status!r}: {row[0]}")
        names = re.findall(rf"`({LIBRARY}\.[\w.'₀-₉]+)`", row[3])
        if status in CERTIFIED and not names:
            errors.append(f"{status} row without a Lean declaration: {row[0]}")
        if status not in CERTIFIED and names:
            errors.append(f"{status} row must not cite certified declarations: {row[0]}")
        if status in CERTIFIED and not REGISTRY_TITLE.match(row[2]):
            errors.append(
                f"{status} row whose Statement does not start with **<title>.**: {row[0]}"
            )
        # AxiomAudit.lean resolves every cited name in Lean's environment.
    errors += registry_declaration_errors(complete, {d[1]: d[0] for d in declarations})
    areas, area_errors = registry_areas(registry)
    errors += area_errors
    if set(GROUPS) != set(LAYERS):
        errors.append(
            f"GROUPS and LAYERS list different directories: {sorted(set(GROUPS) ^ set(LAYERS))}"
        )

    # Generated documentation: the witness table, the declaration index and the README blocks.
    headers = {
        str(path.relative_to(ROOT)): audit_header(path.read_text())
        for path in modules
        if path.parent == ROOT / LIBRARY / AUDIT
    }
    errors += audit_errors(headers, ids)
    complete_headers = {relative: header for relative, header in headers.items() if header}
    generated = {INDEX: write_index(declarations, audit_table(complete_headers, ids))}
    index = ROOT / INDEX
    stale = [] if index.exists() and index.read_text() == generated[INDEX] else [INDEX]
    if (ROOT / README).exists():
        text = (ROOT / README).read_text()
        row_status = {row[0]: row[1] for row in rows if len(row) > 1}
        blocks = {"coverage": coverage_table(areas, row_status), "layout": layout_block()}
        for name, body in blocks.items():
            replaced = replace_block(text, name, body)
            if replaced is None:
                errors.append(
                    f"No generated {name} block ({MARKER.format('BEGIN', name)} ... "
                    f"{MARKER.format('END', name)}, once each) in {README}"
                )
            elif replaced != text:
                stale.append(f"the {name} block of {README}")
                text = replaced
        generated[README] = text
    if args.write:
        for relative, text in generated.items():
            if not (ROOT / relative).exists() or (ROOT / relative).read_text() != text:
                (ROOT / relative).write_text(text)
    else:
        errors += [f"Stale generated documentation: {what}; run with --write" for what in stale]

    # The public documentation against the registry, the sources and each other.
    texts = {name: (ROOT / name).read_text() for name in DOC_FILES if (ROOT / name).exists()}
    errors += [f"Missing documentation file: {name}" for name in REQUIRED_DOCS if name not in texts]
    pattern = id_pattern(ids)
    sources = {str(path.relative_to(ROOT)): path.read_text() for path in modules}
    # The illustrations cite registry IDs in their docstrings and comments.
    scripts = {
        str(path.relative_to(ROOT)): path.read_text()
        for directory in ILLUSTRATIONS
        for path in sorted((ROOT / directory).glob("*.py"))
    }
    errors += unknown_id_errors({**texts, **sources, **scripts}, ids, pattern)
    errors += status_word_errors(texts, {row[0]: row[1] for row in complete}, pattern)
    errors += link_errors(texts)
    # The wording rules also cover the other docs/*.md files (not the generated index).
    others = {
        str(path.relative_to(ROOT)): path.read_text()
        for path in sorted(ROOT.joinpath("docs").glob("*.md"))
        if path != ROOT / INDEX
    }
    errors += banned_phrase_errors({**others, **texts, **sources})
    if README in texts:
        readme = texts[README]
        lines = sum(len(source.splitlines()) for source in sources.values())
        statuses = [row[1] if len(row) > 1 else "" for row in rows]
        errors += counts_errors(readme, statuses, lines, len(declarations))
        errors += moves_table_errors(readme, ids, pattern)
        errors += statuses_section_errors(readme)
        if LITERATURE in texts:
            errors += literature_map_errors(readme, texts[LITERATURE], pattern)
    if RESULTS_ONE_BULLET_PER_ID and RESULTS in texts:
        sections = {rid: area for area, area_ids in areas for rid in area_ids}
        errors += results_bullet_errors(texts[RESULTS], complete, sections, pattern)

    scanned = {*modules, *ROOT.glob("*.md"), *ROOT.joinpath("docs").rglob("*.md")}
    for path in sorted(scanned | {ROOT / name for name in texts}):
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
