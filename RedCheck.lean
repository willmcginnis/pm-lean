-- Which declarations under `PM` depend on the axiom of reducibility (✱12·1 / ✱12·11, the constructors
-- `PM.QThm.red1` / `PM.QThm.red2`) or on comprehension (`PM.QThm.compr1` / `PM.QThm.compr2`).
-- Run with `lake env lean RedCheck.lean`.
--
-- Like `#print axioms`, this follows the constants used in the type and the value of each declaration,
-- transitively. A proof of `QThm p` that does not reach `red1` or `red2` is a derivation without
-- reducibility. The check over-approximates (anything using the recursor `QThm.rec`, such as `qsound`,
-- reaches every constructor through the recursor's type), so "does not use" is reliable; the check
-- reports whether the constant graph had a cycle, in which case the results would not be exact.
import Lean
import PM
open Lean Elab Command

structure RCState where
  memo : Std.HashMap Name Nat := {}
  cycle : Bool := false

partial def reach (tg : Array Name) (c : Name) : StateT RCState CoreM Nat := do
  if let some v := (← get).memo.get? c then
    if v == 1 <<< tg.size then modify fun s => { s with cycle := true }
    return v % (1 <<< tg.size)
  modify fun s => { s with memo := s.memo.insert c (1 <<< tg.size) }   -- in progress
  let mut m := 0
  for i in [:tg.size] do
    if tg[i]! == c then m := m ||| (1 <<< i)
  if let some ci := (← getEnv).find? c then
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for d in cs do
      m := m ||| (← reach tg d)
  modify fun s => { s with memo := s.memo.insert c m }
  return m

/-- A PM proposition: `q…` (✱9–✱20) or `QL.t…` (✱2–✱5 lifted); not models, rules or metatheorems. -/
def isPMProp (n : Name) : Bool :=
  match n with
  | .str (.str .anonymous "PM") s => s.startsWith "q" &&
      ((s.drop 1).startsWith "1" || (s.drop 1).startsWith "9" || (s.drop 1).startsWith "2")
  | .str (.str (.str .anonymous "PM") "QL") _ => true
  | _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let tg : Array Name := #[`PM.QThm.red1, `PM.QThm.red2, `PM.QThm.compr1, `PM.QThm.compr2]
  let names := (env.constants.fold (init := #[]) fun acc c _ =>
    if (`PM).isPrefixOf c && !c.isInternal then acc.push c else acc).qsort Name.lt
  let (res, st) ← liftCoreM <| (names.mapM fun c => do return (c, ← reach tg c)).run {}
  let props := res.filter fun (c, _) => isPMProp c
  let red := props.filter fun (_, m) => m &&& 3 != 0
  let compr := props.filter fun (_, m) => m &&& 12 != 0
  let allRed := res.filter fun (_, m) => m &&& 3 != 0
  logInfo m!"checked {names.size} declarations under PM ({props.size} PM propositions); constant graph has a cycle: {st.cycle}"
  logInfo m!"{red.size} PM propositions use ✱12·1 or ✱12·11: {red.map (·.1)}"
  logInfo m!"{compr.size} PM propositions use comprehension: {compr.map (·.1)}"
  logInfo m!"other declarations reaching red1/red2: {(allRed.filter fun (c, _) => !isPMProp c).map (·.1)}"
