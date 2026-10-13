-- The canonical text of an elaborated statement or definition, shared by Checks/ExportStatements.lean
-- (which prints the statements of this repository for scripts/export_names.py and the lock of released
-- names, docs/VERSIONING.md) and by the check of exported platform cards (scripts/prove2me/verify.py,
-- which computes the same digests from the uploaded files). It imports Lean only, so that it can be
-- compiled next to the platform's files, which do not import this repository.
import Lean
open Lean Meta

namespace PMCanon

/-- `PM.s<N>_<M>`: a statement definition of PM/Statements.lean. -/
def isStatementDef (c : Name) : Bool :=
  match c with
  | .str (.str .anonymous "PM") s =>
    s.startsWith "s" && (s.toList[1]?).any Char.isDigit && s.contains '_'
  | _ => false

def jstr (s : String) : String := (Json.str s).compress

/-- `e` in a canonical text: de Bruijn indices for bound variables, no binder names. -/
partial def canon : Expr → String
  | .bvar i => s!"#{i}"
  | .sort u => s!"(S {u})"
  | .const n us => s!"(C {n} {us})"
  | .app f a => s!"(A {canon f} {canon a})"
  | .lam _ t b bi => s!"(L{binder bi} {canon t} {canon b})"
  | .forallE _ t b bi => s!"(P{binder bi} {canon t} {canon b})"
  | .letE _ t v b _ => s!"(Z {canon t} {canon v} {canon b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal s) => s!"(T {jstr s})"
  | .mdata _ e => canon e
  | .proj s i e => s!"(J {s} {i} {canon e})"
  | .fvar _ | .mvar _ => "(?)"
where binder : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

/-- `e` with the statement definitions `PM.s<N>_<M>` replaced by their bodies. -/
def unfoldStatements (e : Expr) : MetaM Expr :=
  Core.transform e (pre := fun e => do
    if let .const c us := e.getAppFn then
      if isStatementDef c then
        let v ← instantiateValueLevelParams (← getConstInfo c) us
        return .visit (v.beta e.getAppArgs)
    return .continue)

/-- The constants under `PM` that `e` names, other than theorems. -/
def pmConsts (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  return e.getUsedConstants.filter fun n =>
    (`PM).isPrefixOf n && !(env.find? n matches some (.thmInfo _))

/-- What a definition under `PM` is, in the canonical text, and the constants under `PM` it uses. -/
def defCanon (n : Name) : MetaM (String × Array Name) := do
  match ← getConstInfo n with
  | .defnInfo d => return (s!"def {canon d.type} := {canon d.value}",
      (← pmConsts d.type) ++ (← pmConsts d.value))
  | .inductInfo d =>
    let mut s := s!"inductive {canon d.type}"
    let mut used ← pmConsts d.type
    for k in d.ctors do
      let t := (← getConstInfo k).type
      s := s ++ s!" | {k} : {canon t}"
      used := used ++ (← pmConsts t)
    return (s, used)
  | .ctorInfo d => return (s!"constructor of {d.induct}", #[d.induct])
  | i => return (s!"other {canon i.type}", ← pmConsts i.type)

/-- The definitions under `PM` that `e` uses, directly or through other definitions. -/
partial def deps (e : Expr) : MetaM NameSet := do
  let mut seen : NameSet := {}
  let mut todo := (← pmConsts e).toList
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      todo := (← defCanon n).2.toList ++ todo
  return seen

/-- The canonical text of the statement of `c` (statement definitions unfolded), and the definitions
    under `PM` it uses, sorted. -/
def statementCanon (c : Name) : MetaM (String × Array Name) := do
  let ty ← unfoldStatements (← getConstInfo c).type
  let ds ← deps ty
  return (canon ty, ds.toList.toArray.qsort (·.toString < ·.toString))

end PMCanon
