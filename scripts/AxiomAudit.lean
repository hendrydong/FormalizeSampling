import FormalizeSampling
import Lean.Util.CollectAxioms

/-!
# Transitive axiom audit and documentation names

Every declaration whose origin module lies under `FormalizeSampling` (including private
helpers) is checked transitively: the only axioms allowed are Lean's standard
`propext`, `Classical.choice` and `Quot.sound`. This file is not a module, so importing the
library loads the private part of every module (private declarations and all proofs) as well.
Every fully qualified `FormalizeSampling.` name cited in `docs/theorem_registry.md`, and every
declaration listed in `docs/declaration_index.md`, must resolve in the elaborated environment.

The public Markdown files (`docFiles`) are checked against the environment too:
* every backticked dotted name outside fenced code blocks and inline math, such as
  `Pinsker.tvSup_le_sqrt_klDiv`, `MeasureTheory.tvDist` or `FormalizeSampling.Core`, must be a
  declaration, with or without the `FormalizeSampling.` prefix, or a module; file names such as
  `Core.lean` and Python names such as `fractions.Fraction` are skipped;
* no such declaration may be deprecated;
* every registry row that cites declarations must cite one that the statement audit uses: one in
  the transitive closure, through the library's own declarations, of the constants used in the
  types and proofs of the declarations of the `FormalizeSampling.Audit` modules.
-/

open Lean Elab Command

namespace AxiomAudit

/-- The public Markdown files whose code spans are resolved (a missing file is skipped); the same
list as `DOC_FILES` in `scripts/check_contracts.py`. -/
def docFiles : List String :=
  ["README.md", "CONTRIBUTING.md", "docs/results.md", "docs/literature.md",
    "docs/statement_audit.md", "docs/glossary.md", "docs/theorem_registry.md",
    "showcase/README.md", "experiments/README.md"]

/-- Last components of code spans that name files rather than declarations. -/
def fileExtensions : List String := ["lean", "md", "py", "png", "toml", "json", "txt", "yml"]

/-- First components of code spans that name Python objects (the illustrations' libraries). -/
def pythonModules : List String := ["fractions", "math", "numpy", "np", "scipy", "matplotlib"]

/-- A character of an identifier component (letters, digits, subscripts, `_`, `'`, `!`, `?`). -/
def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || isLetterLike c ||
    isSubScriptAlnum c

/-- The name written in a code span, if the span is a dotted identifier such as `A.b` (and not a
file name such as `Core.lean` or a Python name such as `fractions.Fraction`). -/
def dottedName? (span : String) : Option Name :=
  let parts := span.splitOn "."
  if parts.length < 2 || fileExtensions.contains parts.getLast! ||
      pythonModules.contains parts.head! then none
  else if parts.all (fun p => !p.isEmpty && !p.front.isDigit && p.all isNameChar) then
    some span.toName
  else none

/-- The code spans of a line: every second fragment between backticks, unless the span is inline
math ($`…`$). -/
def lineSpans (line : String) : Array String := Id.run do
  let parts := (line.splitOn "`").toArray
  let mut spans := #[]
  for i in [1:parts.size - 1:2] do
    unless parts[i - 1]!.endsWith "$" do
      spans := spans.push parts[i]!
  return spans

/-- The code spans of a Markdown text outside fenced code blocks. -/
def codeSpans (text : String) : Array String := Id.run do
  let mut spans := #[]
  let mut fenced := false
  for line in text.splitOn "\n" do
    if (line.dropWhile (· == ' ')).startsWith "```" then
      fenced := !fenced
    else if !fenced then
      spans := spans ++ lineSpans line
  return spans

/-- Registry row IDs: two capital letters, a hyphen and digits (`KL-1`, `CE-01`). -/
def isRowId (id : String) : Bool :=
  match id.splitOn "-" with
  | [p, n] => p.length == 2 && p.all Char.isUpper && !n.isEmpty && n.all Char.isDigit
  | _ => false

/-- Constants used in the type and the value (proof or body) of a declaration. -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]

end AxiomAudit

open AxiomAudit in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let underModule (pre : Name) (name : Name) : Bool := match env.getModuleIdxFor? name with
    | some idx => pre.isPrefixOf moduleNames[idx.toNat]!
    | none => false
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut project : Array Name := #[]
  for (name, _) in env.constants.toList do
    if underModule `FormalizeSampling name then
      project := project.push name
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  if project.isEmpty then
    throwError "No project declarations were imported"
  logInfo m!"Axiom audit passed for {project.size} declarations; allowlist: {allowed}"
  let registry ← liftIO <| IO.FS.readFile "docs/theorem_registry.md"
  let mut references : Nat := 0
  for fragment in registry.splitOn "`" do
    if fragment.startsWith "FormalizeSampling." then
      let name := fragment.toName
      unless env.contains name do
        throwError "Registry references missing declaration: {name}"
      references := references + 1
  logInfo m!"Resolved {references} fully qualified registry references"
  let index ← liftIO <| IO.FS.readFile "docs/declaration_index.md"
  let mut indexed : Nat := 0
  for line in index.splitOn "\n" do
    if line.startsWith "| `" then
      let name := ((line.splitOn "`")[1]!).toName
      unless env.contains name do
        throwError "Declaration index lists missing declaration: {name}"
      indexed := indexed + 1
  logInfo m!"Resolved {indexed} declaration index entries"
  -- Backticked dotted names in the public Markdown files: declarations (with or without the
  -- `FormalizeSampling.` prefix) that are not deprecated, or modules.
  let modules : NameSet := moduleNames.foldl (·.insert ·) {}
  let mut unresolved : Array String := #[]
  let mut deprecated : Array String := #[]
  let mut spans : Nat := 0
  for file in docFiles do
    unless ← liftIO <| System.FilePath.pathExists file do continue
    for span in codeSpans (← liftIO <| IO.FS.readFile file) do
      let some name := dottedName? span | continue
      spans := spans + 1
      let full := (`FormalizeSampling).append name
      match [name, full].find? env.contains with
      | some found =>
        if Linter.isDeprecated env found then
          deprecated := deprecated.push s!"{file}: {span}"
      | none =>
        unless modules.contains name || modules.contains full do
          unresolved := unresolved.push s!"{file}: {span}"
  unless unresolved.isEmpty do
    throwError "Documentation cites names that are neither declarations nor modules:\n\
      {"\n".intercalate unresolved.toList}"
  unless deprecated.isEmpty do
    throwError "Documentation cites deprecated declarations:\n\
      {"\n".intercalate deprecated.toList}"
  logInfo m!"Resolved {spans} dotted names in the documentation; none is deprecated"
  -- Witness reachability: the closure, through project declarations, of the constants used by
  -- the declarations of the audit modules.
  let mut reached : NameSet := {}
  let mut stack : Array Name := #[]
  for name in project do
    if underModule `FormalizeSampling.Audit name then
      reached := reached.insert name
      stack := stack.push name
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    let some ci := env.find? name | continue
    for used in usedConstants ci do
      if !reached.contains used && underModule `FormalizeSampling used then
        reached := reached.insert used
        stack := stack.push used
  let mut rows : Nat := 0
  let mut unwitnessed : Array String := #[]
  for line in registry.splitOn "\n" do
    let cells := line.splitOn "|"
    let id := (cells.getD 1 "").replace " " ""
    if line.startsWith "| " && cells.length > 4 && isRowId id then
      let cited := (lineSpans cells[4]!).filter (·.startsWith "FormalizeSampling.")
      unless cited.isEmpty do
        rows := rows + 1
        unless cited.any (reached.contains ·.toName) do
          unwitnessed := unwitnessed.push id
  unless unwitnessed.isEmpty do
    throwError "Registry rows whose cited declarations the statement audit never uses: \
      {unwitnessed}"
  logInfo m!"Every registry row with Lean declarations ({rows}) cites one used by the \
    statement audit ({reached.size} declarations reached from the audit modules)"
