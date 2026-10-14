-- Axiom audit of every declaration whose name starts with `PM` (theorems, definitions, helpers, models,
-- including `PM.sound`), and of every private declaration of the PM modules (`_private.PM.…`), not just
-- the selection printed by AxiomCheck.lean. Compiler-internal auxiliaries (`match_`, `proof_`, `eq_` …)
-- are reached through the declarations that use them, since `collectAxioms` is transitive.
-- The pinned statements are imported too: their check theorems (`PM.check_pinned_…`) are under `PM`.
-- Run with `lake env lean AllAxioms.lean`; it reports how many were checked and lists any that use an axiom.
import Lean
import PM
import Checks.PinnedStatements
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let pub := env.constants.fold (init := #[]) fun acc c _ =>
    if (`PM).isPrefixOf c && !c.isInternal then acc.push c else acc
  let priv := env.constants.fold (init := #[]) fun acc c _ =>
    if c.toString.startsWith "_private.PM." then acc.push c else acc
  let mut bad : Array (Name × Array Name) := #[]
  for c in pub ++ priv do
    let axs ← liftCoreM (Lean.collectAxioms c)
    if axs.size > 0 then bad := bad.push (c, axs)
  logInfo m!"checked {pub.size} declarations under PM and {priv.size} private PM declarations; {bad.size} use an axiom: {bad}"
