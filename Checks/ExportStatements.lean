-- The statements of the declarations that state PM's numbered propositions, as trees, for
-- scripts/export_names.py (which turns them into export names: docs/NAMING.md). Run from the
-- repository root with `lake env lean Checks/ExportStatements.lean`; each line printed is one JSON
-- object `{"name", "module", "vars", "hyps", "concl"}`.
--
-- Printed: every theorem under `PM` whose last name component is a letter `t`, `q` or `f` followed by
-- a digit (scripts/export_names.py picks the ones it exports by module), every theorem of a module
-- under `PM.Deprecated` (the superseded declarations kept by docs/VERSIONING.md), the constructors of
-- `PM.Thm` (✱1·2–✱1·6), and `PM.sound`, `PM.complete` and `PM.star1_4_variant_not_a_theorem`. A
-- declaration marked `@[deprecated new (since := "…")]` also has `"deprecated": {"new", "since"}`.
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
--
-- For the lock of released names (docs/VERSIONING.md), each statement line also has `canon`, the whole
-- elaborated type in a canonical text (statement definitions unfolded, binder names erased, binder
-- kinds, judgments and universe levels kept), and `deps`, the definitions under `PM` it uses, directly
-- or through other definitions (theorems are not followed). After the statements, one line
-- `{"def", "canon"}` gives each of those definitions' type and value (an inductive type: its type and
-- its constructors' types) in the same canonical text (Checks/Canon.lean, shared with the check of the
-- platform export, scripts/prove2me/verify.py). scripts/export_names.py hashes them.
import Lean
import PM
import Checks.Canon
open Lean Meta PMCanon

namespace ExportStatements

def judgments : List Name := [``PM.Thm, ``PM.QThm, ``PM.F9.Thm9]

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

/-- The module that declares `c` (anonymous if none). -/
def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def statement (c : Name) : MetaM (String × NameSet) := do
  let info ← getConstInfo c
  let ty ← unfoldStatements info.type
  let ds ← deps ty
  let depsJ := ", ".intercalate ((ds.toList.map fun n => jstr n.toString).toArray.qsort (· < ·)).toList
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
    let mod := (moduleOf env c).toString
    let dep := match Linter.deprecatedAttr.getParam? env c with
      | some d => ", \"deprecated\": {\"new\": " ++ jstr ((d.newName?.map toString).getD "") ++
          ", \"since\": " ++ jstr (d.since?.getD "") ++ "}"
      | none => ""
    return ("{\"name\": " ++ jstr c.toString ++ ", \"module\": " ++ jstr mod ++
      ", \"vars\": [" ++ ", ".intercalate vars.toList ++ "], \"hyps\": [" ++
      ", ".intercalate hyps.toList ++ "], \"concl\": " ++ (← tree [] concl) ++
      ", \"canon\": " ++ jstr (canon ty) ++ ", \"deps\": [" ++ depsJ ++ "]" ++ dep ++ "}", ds)

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
    if numbered c || (`PM.Deprecated).isPrefixOf (moduleOf env c) then names := names.push c
  names := names.qsort (·.toString < ·.toString)
  let mut used : NameSet := {}
  for c in extra ++ names.toList do
    let (line, ds) ← statement c
    IO.println line
    used := ds.toList.foldl (·.insert ·) used
  for n in used.toList.toArray.qsort (·.toString < ·.toString) do
    IO.println ("{\"def\": " ++ jstr n.toString ++ ", \"canon\": " ++ jstr (← defCanon n).1 ++ "}")

end ExportStatements

#eval ExportStatements.main
