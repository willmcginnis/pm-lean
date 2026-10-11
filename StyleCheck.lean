-- "Both must pass": every PM proposition instantiated under every style (matrix / lowest order ×
-- p. 55 / p. 54) and every named system.
-- Run with `lake env lean StyleCheck.lean`.
--
-- For each PM proposition (`q…`, ✱9–✱20, and the lifted ✱2–✱5 `QL.t…`) and each pair (style, system),
-- the system is substituted for the proposition's parameter `S : Sys`, each class argument
-- (`Reducibility S`, `Comprehension S`) is found by instance search, and the instance is type-checked.
-- A proposition passes in a style when it instantiates in `Sys.full` of that style (PM 1910 as built
-- here). The table also shows the other systems: a proposition that takes no class instantiates in all
-- four; one with `[Reducibility S]` in `Sys.full` and `Sys.reducibility` only.
-- A proposition with no parameter `S`, or one that holds in only some styles, is listed.
import Lean
import PM
open Lean Meta Elab Command PM

/-- A PM proposition: `q…` (✱9–✱20) or `QL.t…` (✱2–✱5 lifted). -/
def isPMProp (n : Name) : Bool :=
  match n with
  | .str (.str .anonymous "PM") s => s.startsWith "q" &&
      ((s.drop 1).startsWith "1" || (s.drop 1).startsWith "9" || (s.drop 1).startsWith "2")
  | .str (.str (.str .anonymous "PM") "QL") _ => true
  | _ => false

/-- Instantiate `c` at the system `sys`: `none` if `c` has no parameter of type `Sys`, else whether
    every class argument was found and the instance type-checks. -/
partial def instAt (c : Name) (sys : Expr) : MetaM (Option Bool) := do
  let e ← mkConstWithFreshMVarLevels c
  let rec go (e ty : Expr) (seen : Bool) : MetaM (Option Bool) := do
    match ty with
    | .forallE _ d b bi =>
      if d.isConstOf ``PM.Sys then go (.app e sys) (b.instantiate1 sys) true
      else if bi.isInstImplicit then
        let d ← instantiateMVars d
        match ← (try some <$> synthInstance d catch _ => pure none) with
        | some inst => go (.app e inst) (b.instantiate1 inst) seen
        | none => return if seen then some false else none
      else
        let m ← mkFreshExprMVar d
        go (.app e m) (b.instantiate1 m) seen
    | _ =>
      if !seen then return none
      try check (← instantiateMVars e); return some true catch _ => return some false
  go e (← inferType e) false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let props := (env.constants.fold (init := #[]) fun acc c _ =>
    if isPMProp c && !c.isInternal then acc.push c else acc).qsort Name.lt
  let styles : List (String × Expr) := [
    ("matrix, p. 55 (primary)", mkApp2 (mkConst ``Style.of) (mkConst ``PredReading.matrix) (mkConst ``RealReading.ownOrder)),
    ("lowest order, p. 55",     mkApp2 (mkConst ``Style.of) (mkConst ``PredReading.lowestOrder) (mkConst ``RealReading.ownOrder)),
    ("matrix, p. 54",           mkApp2 (mkConst ``Style.of) (mkConst ``PredReading.matrix) (mkConst ``RealReading.asArgument)),
    ("lowest order, p. 54",     mkApp2 (mkConst ``Style.of) (mkConst ``PredReading.lowestOrder) (mkConst ``RealReading.asArgument))]
  let systems : List (String × Name) :=
    [("full", ``Sys.full), ("reducibility", ``Sys.reducibility), ("predicative", ``Sys.predicative), ("base", ``Sys.base)]
  let mut noS : Array Name := #[]
  let mut fullFail : Array (Name × String) := #[]
  let mut lines : Array String := #[]
  for (sn, st) in styles do
    let mut row := s!"{sn}:"
    for (yn, y) in systems do
      let sys := mkApp (mkConst y) st
      let mut ok := 0
      for c in props do
        match ← liftTermElabM (instAt c sys) with
        | some true => ok := ok + 1
        | some false => if yn == "full" then fullFail := fullFail.push (c, sn)
        | none => if yn == "full" && sn.startsWith "matrix" then noS := noS.push c
      row := row ++ s!"  {yn} {ok}/{props.size}"
    lines := lines.push row
  logInfo m!"{props.size} PM propositions; instantiated per style and system:\n{"\n".intercalate lines.toList}"
  logInfo m!"PM propositions with no parameter S : Sys: {noS.size} {noS}"
  logInfo m!"PM propositions failing in Sys.full of some style: {fullFail.size} {fullFail}"
