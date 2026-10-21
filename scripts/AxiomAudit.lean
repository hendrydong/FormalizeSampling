import FormalizeSampling
import Lean.Util.CollectAxioms

/-!
# Transitive axiom audit

Every declaration whose origin module lies under `FormalizeSampling` (including private
helpers) is checked transitively: the only axioms allowed are Lean's standard
`propext`, `Classical.choice` and `Quot.sound`. This file is not a module, so importing the
library loads the private part of every module (private declarations and all proofs) as well.
Every fully qualified `FormalizeSampling.` name cited in `docs/theorem_registry.md`, and every
declaration listed in `docs/declaration_index.md`, must resolve in the elaborated environment.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let isProject := match env.getModuleIdxFor? name with
      | some idx => (`FormalizeSampling).isPrefixOf moduleNames[idx.toNat]!
      | none => false
    if isProject then
      count := count + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  if count == 0 then
    throwError "No project declarations were imported"
  logInfo m!"Axiom audit passed for {count} declarations; allowlist: {allowed}"
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
