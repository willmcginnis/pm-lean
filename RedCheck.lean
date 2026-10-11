-- Cross-check of the rule signatures: which declarations under `PM` use the axiom of reducibility
-- (✱12·1 / ✱12·11) or comprehension, found from the proofs, compared with what their signatures ask for.
-- Run with `lake env lean RedCheck.lean`.
--
-- The rules are opt-in: a theorem that uses ✱12·1 / ✱12·11 must take `[Reducibility S]`, one that uses
-- comprehension `[Comprehension S]` (PM/Rules/), and Lean enforces this. This file checks the same
-- thing independently, from the proof terms:
-- - "uses" = the declaration reaches, transitively through the constants of its type and value, the
--   class field `PM.Reducibility.red` (resp. `PM.Comprehension.compr`), which is the only way to obtain
--   `S.red = true` (resp. `S.compr = true`) for an arbitrary system `S`. (The constructors `QThm.red1`
--   etc. are not used as the test: every proof by induction on `QThm` reaches all constructors through
--   the recursor's type.)
-- - "asks" = the class `PM.Reducibility` (resp. `PM.Comprehension`) occurs in the declaration's type.
-- A PM proposition that uses a rule without asking for it, or asks without using it, is reported.
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
  let tg : Array Name := #[`PM.Reducibility.red, `PM.Comprehension.compr]
  let names := (env.constants.fold (init := #[]) fun acc c _ =>
    if (`PM).isPrefixOf c && !c.isInternal then acc.push c else acc).qsort Name.lt
  let (res, st) ← liftCoreM <| (names.mapM fun c => do return (c, ← reach tg c)).run {}
  let asks (c : Name) (cls : Name) : Bool :=
    match env.find? c with
    | some ci => ci.type.getUsedConstants.contains cls
    | none => false
  let props := res.filter fun (c, _) => isPMProp c
  let red := props.filter fun (_, m) => m &&& 1 != 0
  let compr := props.filter fun (_, m) => m &&& 2 != 0
  logInfo m!"checked {names.size} declarations under PM ({props.size} PM propositions); constant graph has a cycle: {st.cycle}"
  logInfo m!"{red.size} PM propositions use ✱12·1 or ✱12·11: {red.map (·.1)}"
  logInfo m!"{compr.size} PM propositions use comprehension: {compr.map (·.1)}"
  let mism := props.filter fun (c, m) =>
    ((m &&& 1 != 0) != asks c `PM.Reducibility) || ((m &&& 2 != 0) != asks c `PM.Comprehension)
  logInfo m!"PM propositions whose signature disagrees with their proof: {mism.size} {mism.map (·.1)}"
  let others := res.filter fun (c, m) => !isPMProp c && m != 0
  let tag (m : Nat) : String := (if m &&& 1 != 0 then "red " else "") ++ (if m &&& 2 != 0 then "compr" else "")
  logInfo m!"other declarations using a rule: {others.map fun (c, m) => (c, tag m)}"
