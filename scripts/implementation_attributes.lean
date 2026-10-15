-- The compiler's implementation attributes on the repository's declarations, read by
-- scripts/external_checkers.py (docs/VERIFICATION.md, "External checkers"). A logical export leaves
-- these attributes out, so the scan of the export cannot see them; this reads them from the
-- environment the build wrote.
--
--   lean --run scripts/implementation_attributes.lean PREFIX... -- MODULE...
--
-- imports the MODULEs and prints one line of JSON: the number of declarations whose module has one of
-- the PREFIXes as a prefix; those of them with an implementation attribute (the compiler's
-- replacement of a definition by other Lean code, or by foreign code); and those marked unsafe or
-- partial, which lean4export leaves out of the export. Exits 1 if any has an implementation attribute.
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (prefixes, modules) := args.span (· != "--")
  let prefixes := prefixes.map String.toName
  let env ← importModules ((modules.drop 1).toArray.map fun m => { module := m.toName }) {}
  let mut count := 0
  let mut attributed : Array Name := #[]
  let mut excluded : Array Name := #[]
  for (c, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[i.toNat]!
    unless prefixes.any (·.isPrefixOf m) do continue
    count := count + 1
    if (Compiler.getImplementedBy? env c).isSome || isExtern env c then attributed := attributed.push c
    if ci.isUnsafe || ci.isPartial then excluded := excluded.push c
  let names (a : Array Name) : Json := toJson ((a.qsort Name.lt).map (·.toString))
  IO.println (Json.compress (Json.mkObj [("prefixes", toJson (prefixes.map (·.toString))),
    ("modules", toJson (modules.drop 1)), ("declarations", toJson count),
    ("attributed", names attributed), ("excluded", names excluded),
    ("excludedCount", toJson excluded.size)]))
  return if attributed.isEmpty then 0 else 1
