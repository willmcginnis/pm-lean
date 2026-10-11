-- Exhaustive axiom audit: every declaration whose name starts with `PM` (theorems, definitions, helpers,
-- models, including `PM.sound`), not just the selection printed by AxiomCheck.lean.
-- Run with `lake env lean AllAxioms.lean`; it reports how many were checked and lists any that use an axiom.
import Lean
import PM
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc c _ =>
    if (`PM).isPrefixOf c && !c.isInternal then acc.push c else acc
  let mut bad : Array (Name × Array Name) := #[]
  for c in names do
    let axs ← liftCoreM (Lean.collectAxioms c)
    if axs.size > 0 then bad := bad.push (c, axs)
  logInfo m!"checked {names.size} declarations under PM; {bad.size} use an axiom: {bad}"
