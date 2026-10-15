-- Types as terms and universe levels in the closure of the PM derivation theorems, the measurement
-- the roadmap's task (e) cites (docs/ROADMAP.md, "The fragment, grounded in ZF"). Run by hand:
--
--   lake env lean scripts/kernel_census/type_as_term.lean
--
-- The set and its closure are the kernel census's (KernelCensus.lean): the derivation theorems are the
-- theorems of the derivation, foundation and metatheory modules, neither notation nor check theorems,
-- whose statement concludes `Thm`, `QThm` or `Thm9` (the census's `proofTheorems`); the closure follows
-- the constants a declaration's type and value name, an inductive type's constructors and recursors,
-- a constructor's type, a recursor's types (the census's `proofClosure`). The module lists below are
-- the census's and must be kept equal to them. For comparison it also gives the set an earlier
-- measurement used: the theorems with those conclusions in the derivation modules alone.
--
-- Measured over the closure: (1) constants whose type binds a type (a binder whose type ends in a sort
-- other than Prop, as `V : Ty → Type`); (2) inductive types with a constructor field that holds a type;
-- (3) universe-polymorphic constants; (4) the repository's constants whose statement binds a type
-- below its leading binders, and those whose value does, after a definition's own parameters; (5) the
-- highest universe level a constant is used at, universe parameters set to 0.
import PM
import Checks.PinnedStatements
open Lean

namespace TypeAsTerm

def derivationModules : List Name := [`PM.Statements, `PM.Replay, `PM.Replay2, `PM.Derived,
  `PM.QuantLift, `PM.Star10, `PM.Star11, `PM.Star12, `PM.Star13, `PM.Star14, `PM.Star20, `PM.Star21,
  `PM.Star22, `PM.Star23, `PM.Star24, `PM.Star25,
  `PM.Chain, `PM.Found9.Base, `PM.Found9.Star9, `PM.Found9.Switch, `PM.Found9.Exch, `PM.Found9.Simul]
def foundationModules : List Name := [`PM.Basic, `PM.Quant, `PM.Rules.Reducibility,
  `PM.Rules.Comprehension, `PM.Found9.Syntax, `PM.Found9.System]
def metatheoryModules : List Name := [`PM.Complete, `PM.Star2, `PM.Systems, `PM.Orders, `PM.Trap,
  `PM.Pred.Curry, `PM.Pred.LowestOrder, `PM.Pred.Matrix, `PM.Pred.RealAsArgument,
  `PM.Pred.RealOwnOrder, `PM.Pred.Styles, `PM.StylesEquiv, `PM.Models.Collapse, `PM.Models.Finite,
  `PM.Found9.ToStar10, `PM.Found9.FromStar10, `PM.Found9.Equiv, `Checks.PinnedStatements]
def derivHeads : List Name := [``PM.Thm, ``PM.QThm, ``PM.F9.Thm9]

def modOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

def isRepo (env : Environment) (c : Name) : Bool :=
  let m := modOf env c
  (`PM).isPrefixOf m || (`Checks).isPrefixOf m

def isCheck (c : Name) : Bool :=
  match c with
  | .str _ s => s.startsWith "check_"
  | _ => false

def isNotation (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => ci.type.getUsedConstants.any fun d => (`Lean).isPrefixOf d
  | none => false

def concludes (ci : ConstantInfo) : Bool :=
  derivHeads.any (ci.type.getForallBody.getAppFn.constName? == some ·)

/-- The constants the census follows from `ci` (KernelCensus.infoOf). -/
def deps (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then ds := ds ++ v.getUsedConstants
  match ci with
  | .quotInfo _ => ds := ds ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, ``Eq]
  | .inductInfo v => ds := ds ++ v.all.toArray ++ (v.all.map mkRecName).toArray ++ v.ctors.toArray
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v => ds := ds ++ v.all.toArray
  | _ => pure ()
  return ds

def closure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      for d in deps ci do unless seen.contains d do todo := todo.push d
  return seen

/-- `e` ends, after its binders, in a sort other than Prop. -/
partial def endsInBigSort : Expr → Bool
  | .forallE _ _ b _ => endsInBigSort b
  | .sort l => !(l.normalize == Level.zero)
  | .mdata _ e => endsInBigSort e
  | _ => false

/-- The binders of `e` whose type ends in a sort other than Prop; with `inPrefix`, not those of its
    leading ∀-binders. -/
partial def bigBinders (e : Expr) (inPrefix : Bool) (acc : Array String := #[]) : Array String :=
  match e with
  | .forallE n t b _ =>
    let acc := if endsInBigSort t && !inPrefix then acc.push s!"{n} : {t}" else acc
    bigBinders b inPrefix (bigBinders t false acc)
  | .lam n t b _ =>
    let acc := if endsInBigSort t then acc.push s!"fun {n} : {t}" else acc
    bigBinders b false (bigBinders t false acc)
  | .app f a => bigBinders a false (bigBinders f false acc)
  | .letE _ t v b _ => bigBinders b false (bigBinders v false (bigBinders t false acc))
  | .mdata _ b | .proj _ _ b => bigBinders b false acc
  | _ => acc

partial def maxLevel (e : Expr) : Nat :=
  let lv (l : Level) : Nat := (l.substParams (fun _ => some Level.zero)).normalize.toNat.getD 0
  match e with
  | .const _ ls => ls.foldl (fun m l => max m (lv l)) 0
  | .sort l => lv l
  | .app f a => max (maxLevel f) (maxLevel a)
  | .lam _ t b _ | .forallE _ t b _ => max (maxLevel t) (maxLevel b)
  | .letE _ t v b _ => max (maxLevel t) (max (maxLevel v) (maxLevel b))
  | .mdata _ b | .proj _ _ b => maxLevel b
  | _ => 0

def sorted (a : Array Name) : List String := ((a.qsort Name.lt).map (·.toString)).toList

end TypeAsTerm

open TypeAsTerm in
/-- The measurements over the closure of `roots`. -/
def report (env : Environment) (label : String) (roots : Array Name) : IO Unit := do
  let cl := closure env roots
  let members := cl.toArray.qsort Name.lt
  IO.println s!"{label}, {roots.size} theorems: closure: {members.size} constants, {(members.filter (isRepo env)).size} of the repository"
  -- (1)
  let typeBinds := members.filter fun c => match env.find? c with
    | some ci => !(bigBinders ci.type false).isEmpty
    | none => false
  IO.println s!"(1) constants whose type binds a type: {typeBinds.size}, {(typeBinds.filter (isRepo env)).size} of the repository"
  -- (2)
  let mut large : Array Name := #[]
  for c in members do
    let some (.inductInfo v) := env.find? c | continue
    for k in v.ctors do
      let some ci := env.find? k | continue
      let mut t := ci.type
      for _ in [:v.numParams] do
        if let .forallE _ _ b _ := t then t := b
      if !(bigBinders t false).isEmpty then
        large := large.push c
        break
  IO.println s!"(2) inductive types with a constructor field that holds a type: {sorted large}"
  -- (3)
  let poly := members.filter fun c => match env.find? c with
    | some ci => !ci.levelParams.isEmpty
    | none => false
  IO.println s!"(3) universe-polymorphic constants: {poly.size}"
  -- (4)
  let mut inStatement : Array Name := #[]
  let mut inValue : Array Name := #[]
  let mut maxLv := 0
  let mut maxAt : Name := .anonymous
  for c in members do
    let some ci := env.find? c | continue
    let v? := ci.value? (allowOpaque := true)
    let m := max (maxLevel ci.type) ((v?.map maxLevel).getD 0)
    if m > maxLv then
      maxLv := m
      maxAt := c
    unless isRepo env c do continue
    unless (bigBinders ci.type true).isEmpty do inStatement := inStatement.push c
    if let some v := v? then
      let mut body := v
      while body.isLambda do body := body.bindingBody!
      unless (bigBinders body false).isEmpty do inValue := inValue.push c
  IO.println s!"(4) repository constants whose statement binds a type below its leading binders: {sorted inStatement}"
  IO.println s!"    whose value binds a type, after a definition's own parameters: {sorted inValue}"
  -- (5)
  IO.println s!"(5) highest universe level used (parameters at 0): {maxLv}, at {maxAt}"

open TypeAsTerm in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut census : Array Name := #[]
  let mut earlier : Array Name := #[]
  for (c, ci) in env.constants.toList do
    let m := modOf env c
    let inGroups := derivationModules.contains m || foundationModules.contains m ||
      metatheoryModules.contains m
    unless inGroups && ci matches .thmInfo _ && concludes ci do continue
    if derivationModules.contains m then earlier := earlier.push c
    unless isNotation env c || isCheck c do census := census.push c
  let tally (cs : Array Name) : List (String × Nat) :=
    (cs.foldl (init := (∅ : Std.HashMap String Nat)) fun m c =>
      m.insert (modOf env c).toString (m.getD (modOf env c).toString 0 + 1)).toList.mergeSort (·.1 < ·.1)
  let onlyCensus := census.filter fun c => !earlier.contains c
  let onlyEarlier := earlier.filter fun c => !census.contains c
  IO.println s!"derivation theorems: {census.size} (the census's set); {earlier.size} in the derivation modules alone"
  IO.println s!"  only in the census's set, by module: {tally onlyCensus}"
  IO.println s!"  only in the other (notation or check theorems): {sorted onlyEarlier}"
  report env "the census's set" census
  report env "the derivation modules alone" earlier
