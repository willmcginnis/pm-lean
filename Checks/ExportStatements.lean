-- The statements of the declarations that state PM's numbered propositions, as trees, for
-- scripts/export_names.py (which turns them into export names: docs/NAMING.md). Run from the
-- repository root with `lake env lean Checks/ExportStatements.lean`; each line printed is one JSON
-- object `{"name", "module", "vars", "hyps", "concl"}`.
--
-- Printed: every theorem under `PM` whose last name component is a letter `t`, `q` or `f` followed by
-- a digit (scripts/export_names.py picks the ones it exports by module), the constructors of `PM.Thm`
-- (✱1·2–✱1·6), and `PM.sound`, `PM.complete` and `PM.star1_4_variant_not_a_theorem`.
--
-- A tree is the elaborated statement read as written: `{"c": constant, "a": [arguments]}` for an
-- application of a constant (explicit arguments only, and not those that are types), `{"v": name}` for
-- a variable of the statement, `{"b": i}` for the variable bound by the i-th enclosing binder
-- (counted from 1, innermost first), `{"lam": body}` for a function, `{"s": string}` for a string
-- literal, `{"app": head, "a": [...]}` for a variable applied to arguments. Two things are looked
-- through: the judgments (`PM.Thm p`, `PM.QThm S p`, `PM.F9.Thm9 S R p` become the tree of `p`), and
-- the statement definitions `PM.s<N>_<M>` of PM/Statements.lean (replaced by their bodies), so that a
-- tree shows the formula PM prints. Hypotheses (binders whose type is a proposition, instance binders
-- excepted) are listed in `hyps`; a hypothesis `∀ x, A` is printed as `A` with `x` a variable.
import Lean
import PM
open Lean Meta

namespace ExportStatements

def judgments : List Name := [``PM.Thm, ``PM.QThm, ``PM.F9.Thm9]

/-- `PM.s<N>_<M>`: a statement definition of PM/Statements.lean. -/
def isStatementDef (c : Name) : Bool :=
  match c with
  | .str (.str .anonymous "PM") s =>
    s.startsWith "s" && (s.toList[1]?).any Char.isDigit && s.contains '_'
  | _ => false

def jstr (s : String) : String := (Json.str s).compress

partial def tree (bound : List FVarId) (e : Expr) : MetaM String := do
  let e := e.headBeta.consumeMData
  match e with
  | .fvar id =>
    match bound.idxOf? id with
    | some i => return "{\"b\": " ++ toString (i + 1) ++ "}"
    | none => return "{\"v\": " ++ jstr (← id.getUserName).toString ++ "}"
  | .lit (.strVal s) => return "{\"s\": " ++ jstr s ++ "}"
  | .lit (.natVal n) => return "{\"n\": " ++ toString n ++ "}"
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      let body ← tree (x.fvarId! :: bound) (b.instantiate1 x)
      return "{\"lam\": " ++ body ++ "}"
  | .forallE n t b bi =>
    -- a proposition ∀ x, B or A → B inside a statement
    withLocalDecl n bi t fun x => do
      let body ← tree (x.fvarId! :: bound) (b.instantiate1 x)
      if (← isProp t) then
        return "{\"c\": \"Imp\", \"a\": [" ++ (← tree bound t) ++ ", " ++ body ++ "]}"
      return "{\"c\": \"Forall\", \"a\": [{\"lam\": " ++ body ++ "}]}"
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c us := f then
      if judgments.contains c && args.size > 0 then
        return ← tree bound args.back!
      if isStatementDef c then
        let v ← instantiateValueLevelParams (← getConstInfo c) us
        return ← tree bound (v.beta args)
    let finfo ← getFunInfoNArgs f args.size
    let mut parts : Array String := #[]
    for i in [:args.size] do
      let explicit := match finfo.paramInfo[i]? with
        | some p => p.binderInfo.isExplicit
        | none => true
      if !explicit then continue
      let a := args[i]!
      -- types (but not propositions, which are formulas or judgments) and proofs are left out
      if ((← isType a) && !(← isProp a)) || (← isProof a) then continue
      parts := parts.push (← tree bound a)
    let argsJ := "[" ++ ", ".intercalate parts.toList ++ "]"
    match f with
    | .const c _ => return "{\"c\": " ++ jstr c.toString ++ ", \"a\": " ++ argsJ ++ "}"
    | .fvar id =>
      let head := match bound.idxOf? id with
        | some i => "{\"b\": " ++ toString (i + 1) ++ "}"
        | none => ""
      let head ← if head == "" then pure ("{\"v\": " ++ jstr (← id.getUserName).toString ++ "}")
        else pure head
      return "{\"app\": " ++ head ++ ", \"a\": " ++ argsJ ++ "}"
    | _ => return "{\"other\": " ++ jstr (toString (← ppExpr e)) ++ "}"

def statement (c : Name) : MetaM String := do
  let info ← getConstInfo c
  forallTelescope info.type fun xs concl => do
    let mut vars : Array String := #[]
    let mut hyps : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      if (← isProp d.type) then
        -- a hypothesis; ∀ x, A is printed as A
        let h ← forallTelescope d.type fun _ b => tree [] b
        hyps := hyps.push h
      else if !(← isType x) && !(← forallTelescopeReducing d.type fun _ b => pure b.isSort) then
        vars := vars.push (jstr d.userName.toString)
    let env ← getEnv
    let mod := match env.getModuleIdxFor? c with
      | some i => (env.header.moduleNames[i.toNat]!).toString
      | none => ""
    return "{\"name\": " ++ jstr c.toString ++ ", \"module\": " ++ jstr mod ++
      ", \"vars\": [" ++ ", ".intercalate vars.toList ++ "], \"hyps\": [" ++
      ", ".intercalate hyps.toList ++ "], \"concl\": " ++ (← tree [] concl) ++ "}"

/-- A last name component `t`, `q` or `f` followed by a digit. -/
def numbered (c : Name) : Bool :=
  match c with
  | .str _ s => match s.toList with
    | c0 :: c1 :: _ => (c0 == 't' || c0 == 'q' || c0 == 'f') && c1.isDigit
    | _ => false
  | _ => false

def extra : List Name :=
  [``PM.Thm.taut, ``PM.Thm.add, ``PM.Thm.perm, ``PM.Thm.assoc, ``PM.Thm.sum,
   ``PM.sound, ``PM.complete, ``PM.star1_4_variant_not_a_theorem]

def main : MetaM Unit := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (c, info) in env.constants.toList do
    unless (`PM).isPrefixOf c do continue
    unless info matches .thmInfo _ do continue
    if c.isInternal then continue
    if numbered c then names := names.push c
  names := names.qsort (·.toString < ·.toString)
  for c in extra ++ names.toList do
    IO.println (← statement c)

end ExportStatements

#eval ExportStatements.main
