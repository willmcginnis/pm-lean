-- Cross-check of the rule signatures: which declarations under `PM` use the axiom of reducibility
-- (✱12·1 / ✱12·11) or comprehension, found from the proofs, compared with what their signatures ask for.
-- Run with `lake env lean RedCheck.lean`.
--
-- The rules are opt-in. What Lean enforces is that a rule is enabled in the system: the constructors
-- `QThm.red1`/`red2` take a proof of `S.red = true`, `QThm.compr1`/`compr2` one of `S.compr = true`.
-- That evidence can come from the class (`[Reducibility S]`, `[Comprehension S]`, PM/Rules/) or from
-- any other proof of the equation, e.g. a hypothesis `(h : S.red = true)`. That a theorem using a rule
-- takes the class in its signature is the repository's convention, and this file checks it, from the
-- proof terms, in two ways:
-- - "reaches the class": the declaration reaches, transitively through the constants of its type and
--   value, the class field `PM.Reducibility.red` (resp. `PM.Comprehension.compr`).
-- - "reaches a constructor": the declaration reaches `QThm.red1` or `QThm.red2` (resp. `QThm.compr1`
--   or `QThm.compr2`) transitively through the VALUES of the constants it uses (proof terms, not
--   statements), not looking inside recursors, `casesOn`/`recOn`/`brecOn`/`below`, `noConfusion` or
--   matchers: their types and binder types name every constructor, so every proof by induction on `QThm`
--   would otherwise reach them all. This catches evidence supplied other than by the class, e.g.
--   `QThm.red1 h φ` with an explicit `h : S.red = true`, and any helper lemma that does so.
-- - "uses" = either; "asks" = the class `PM.Reducibility` (resp. `PM.Comprehension`) occurs in the
--   declaration's type.
-- A PM proposition that uses a rule without asking for it, or asks without using it, is reported. The
-- test `RedCheckTest.red_with_explicit_evidence` below calls `QThm.red1` with explicit evidence and no
-- class; the check fails (an error) unless it is flagged.
import Lean
import PM
open Lean Elab Command PM

namespace RedCheckTest
open QF in
/-- The constructor takes equality evidence, not a class argument: this uses ✱12·1 without
    `[Reducibility S]`, and RedCheck must flag it. -/
theorem red_with_explicit_evidence {V : Ty → Type} (S : Sys) (h : S.red = true)
    {a : Ty} (φ : V a → QF V) :
    QThm S (ex (τ := Ty.pred1 a) fun f => fiff φ fun x => .app1 f x) :=
  QThm.red1 h φ
end RedCheckTest

structure RCState where
  memo : Std.HashMap Name Nat := {}
  cycle : Bool := false

/-- Auxiliary declarations whose types or binder types name every constructor of an inductive. -/
def isAuxDecl (env : Environment) (c : Name) : Bool :=
  isAuxRecursor env c || isNoConfusion env c || isRecCore env c || Meta.isMatcherCore env c

/-- The targets in `tg` that `c` reaches, as a bit mask. With `types`, through the constants of types
    and values; without, through values only, skipping auxiliary declarations. -/
partial def reach (types : Bool) (tg : Array Name) (c : Name) : StateT RCState CoreM Nat := do
  if let some v := (← get).memo.get? c then
    if v == 1 <<< tg.size then modify fun s => { s with cycle := true }
    return v % (1 <<< tg.size)
  modify fun s => { s with memo := s.memo.insert c (1 <<< tg.size) }   -- in progress
  let mut m := 0
  for i in [:tg.size] do
    if tg[i]! == c then m := m ||| (1 <<< i)
  let env ← getEnv
  if let some ci := env.find? c then
    if types || !isAuxDecl env c then
      let mut cs := if types then ci.type.getUsedConstants else #[]
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      for d in cs do
        m := m ||| (← reach types tg d)
  modify fun s => { s with memo := s.memo.insert c m }
  return m

/-- A PM proposition: `q…` (✱9–✱20) or `QL.t…` (✱2–✱5 lifted); not models, rules or metatheorems. -/
def isPMProp (n : Name) : Bool :=
  match n with
  | .str (.str .anonymous "PM") s => s.startsWith "q" &&
      ((s.drop 1).startsWith "1" || (s.drop 1).startsWith "9" || (s.drop 1).startsWith "2")
  | .str (.str (.str .anonymous "PM") "QL") _ => true
  | _ => false

/-- Bit 0: reducibility, bit 1: comprehension. -/
def ctorMask (m : Nat) : Nat :=
  (if m &&& 3 != 0 then 1 else 0) ||| (if m &&& 12 != 0 then 2 else 0)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let tgClass : Array Name := #[`PM.Reducibility.red, `PM.Comprehension.compr]
  let tgCtor : Array Name := #[`PM.QThm.red1, `PM.QThm.red2, `PM.QThm.compr1, `PM.QThm.compr2]
  let test := `RedCheckTest.red_with_explicit_evidence
  let names := (env.constants.fold (init := #[]) fun acc c _ =>
    if (`PM).isPrefixOf c && !c.isInternal then acc.push c else acc).qsort Name.lt
  let ((resC, resK), st, stK) ← liftCoreM do
    let (resC, st) ← ((names.push test).mapM fun c => do return (c, ← reach true tgClass c)).run {}
    let (resK, stK) ← ((names.push test).mapM fun c => do
      return (c, ctorMask (← reach false tgCtor c))).run {}
    return ((resC, resK), st, stK)
  let ctorOf (c : Name) : Nat := (resK.find? (·.1 == c)).map (·.2) |>.getD 0
  let classOf (c : Name) : Nat := (resC.find? (·.1 == c)).map (·.2) |>.getD 0
  let resC := resC.filter (·.1 != test)
  let res := resC.map fun (c, m) => (c, m ||| ctorOf c)
  let asks (c : Name) (cls : Name) : Bool :=
    match env.find? c with
    | some ci => ci.type.getUsedConstants.contains cls
    | none => false
  let props := res.filter fun (c, _) => isPMProp c
  let red := props.filter fun (_, m) => m &&& 1 != 0
  let compr := props.filter fun (_, m) => m &&& 2 != 0
  logInfo m!"checked {names.size} declarations under PM ({props.size} PM propositions); constant graph has a cycle: {st.cycle || stK.cycle}"
  logInfo m!"{red.size} PM propositions use ✱12·1 or ✱12·11: {red.map (·.1)}"
  logInfo m!"{compr.size} PM propositions use comprehension: {compr.map (·.1)}"
  -- The two analyses side by side, on the PM propositions.
  let byClass := resC.filter fun (c, _) => isPMProp c
  let differ := byClass.filter fun (c, m) => m != ctorOf c
  logInfo m!"PM propositions: reaching the class / a constructor: reducibility {(byClass.filter (·.2 &&& 1 != 0)).size} / {(byClass.filter fun (c, _) => ctorOf c &&& 1 != 0).size}, comprehension {(byClass.filter (·.2 &&& 2 != 0)).size} / {(byClass.filter fun (c, _) => ctorOf c &&& 2 != 0).size}; the two analyses differ on {differ.size} {differ.map (·.1)}"
  let mism := props.filter fun (c, m) =>
    ((m &&& 1 != 0) != asks c `PM.Reducibility) || ((m &&& 2 != 0) != asks c `PM.Comprehension)
  logInfo m!"PM propositions whose signature disagrees with their proof: {mism.size} {mism.map (·.1)}"
  let others := res.filter fun (c, m) => !isPMProp c && m != 0
  let tag (m : Nat) : String := (if m &&& 1 != 0 then "red " else "") ++ (if m &&& 2 != 0 then "compr" else "")
  logInfo m!"other declarations using a rule: {others.map fun (c, m) => (c, tag m)}"
  -- styles_equiv (PM/StylesEquiv.lean) must use reducibility: its proof replays comprehension by ✱12·1.
  for c in [`PM.restyle, `PM.styles_equiv, `PM.styles_equiv_full, `PM.styles_equiv_real] do
    let m := (resC.find? (·.1 == c)).map (·.2) |>.getD 0
    logInfo m!"{c} uses ✱12·1 / ✱12·11: reaches Reducibility.red: {m &&& 1 != 0}; reaches QThm.red1/red2 through proof terms: {ctorOf c &&& 1 != 0}"
  -- The explicit-evidence test: uses reducibility (through the constructor) and does not ask for it.
  let tm := ctorOf test ||| classOf test
  let flagged := tm &&& 1 != 0 && !asks test `PM.Reducibility
  logInfo m!"{test}: reaches Reducibility.red: {classOf test &&& 1 != 0}; reaches QThm.red1/red2: {ctorOf test &&& 1 != 0}; asks Reducibility: {asks test `PM.Reducibility}; flagged as using reducibility without asking: {flagged}"
  unless flagged do throwError "RedCheck failed to flag {test}"
