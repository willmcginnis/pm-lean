-- Kernel census: which features of Lean's kernel the repository relies on. Run by
-- scripts/kernel_census/census.py, which sets PM_CENSUS_OUT (the JSON file this writes) and
-- PM_CENSUS_MODE (`ratchet`: the walk without the meta code's closure; `static`: the walk of every
-- declaration; `full`, the default: also the kernel re-check below); docs/KERNEL_CENSUS.md says what
-- each feature means and how it is measured.
--
-- Static part. Every declaration of the repository's modules is put in one group by its module (the
-- lists below; a module in no list stops the run), notation and meta code by its type, and check
-- theorems (`check_…`, docs/NAMING.md) in a group of their own (census.py refuses a library file with
-- an `example`, which the kernel checks but the environment does not keep). For every
-- declaration, of the repository and of the closure in Lean core of what they use, the walk reads
-- its kind, its universe parameters, its
-- `ConstantInfo` (inductive families: indices, mutual, nested, recursive, structure-like; recursors:
-- K-like, large elimination out of Prop; definitions: safety, reducibility hints, the elaborator's
-- reducibility attribute, the compiler's attributes) and every node of its type and value (sorts and
-- levels, literals, projections, `let`, the constants named). A declaration has a feature when its
-- own type or value shows it ("direct"); a column of the report counts the declarations of a set
-- that have it.
--
-- Dynamic part (`full`). Each theorem, definition and opaque constant of the repository and of the
-- core closure is checked again by the kernel, as a copy under a fresh name, with the kernel's
-- diagnostics on: the kernel then records every constant it unfolds (delta) and every recursor it
-- reduces (iota) while checking. Inductive
-- types, constructors and recursors are not re-checked (a copy would need its whole block renamed).
-- Probes: for each Nat operation the kernel is said to compute on literals, a theorem `op a b = c`
-- with large literals, proved by `Eq.refl`, is checked the same way; the operation is accelerated
-- when the check succeeds without unfolding it.
import Lean
import PM
import Checks.PinnedStatements
import Checks.Canon
open Lean Meta Elab Command

namespace KernelCensus

/-! ## The groups -/

/-- (a) PM's derivations: the statements, the replays, ✱9–✱25 and ✱9 by its own method. -/
def derivationModules : List Name := [`PM.Statements, `PM.Replay, `PM.Replay2, `PM.Derived,
  `PM.QuantLift, `PM.Star10, `PM.Star11, `PM.Star12, `PM.Star13, `PM.Star14, `PM.Star20, `PM.Star21,
  `PM.Star22, `PM.Star23, `PM.Star24, `PM.Star25,
  `PM.Chain, `PM.Found9.Base, `PM.Found9.Star9, `PM.Found9.Switch, `PM.Found9.Exch, `PM.Found9.Simul]

/-- (f) The foundations: the syntaxes and the proof systems the derivations are built in (with their
    soundness theorems, which live in the same files). -/
def foundationModules : List Name := [`PM.Basic, `PM.Quant, `PM.Rules.Reducibility,
  `PM.Rules.Comprehension, `PM.Found9.Syntax, `PM.Found9.System]

/-- (b) The repository's metatheorems, models, styles and pinned statements. -/
def metatheoryModules : List Name := [`PM.Complete, `PM.Star2, `PM.Systems, `PM.Orders, `PM.Trap,
  `PM.Pred.Curry, `PM.Pred.LowestOrder, `PM.Pred.Matrix, `PM.Pred.RealAsArgument,
  `PM.Pred.RealOwnOrder, `PM.Pred.Styles, `PM.StylesEquiv, `PM.Models.Collapse, `PM.Models.Finite,
  `PM.Found9.ToStar10, `PM.Found9.FromStar10, `PM.Found9.Equiv, `Checks.PinnedStatements]

/-- (m) Meta code: programs run by the elaborator or by the tools, part of no proof. -/
def metaModules : List Name := [`PM.Found9.SearchTactic, `Checks.Canon]

/-- Entry files: imports only, no declarations. -/
def entryModules : List Name := [`PM, `PM.Vol1, `PM.Found9]

def isRepoModule (m : Name) : Bool := (`PM).isPrefixOf m || (`Checks).isPrefixOf m

/-- A check theorem (docs/NAMING.md): its last component begins `check_`. Checks are counted apart
    from the group of their module, as their own column. -/
def isCheck (c : Name) : Bool :=
  match c with
  | .str _ s => s.startsWith "check_"
  | _ => false

def groupOf (m : Name) : Option String :=
  if derivationModules.contains m then some "derivations"
  else if foundationModules.contains m then some "foundations"
  else if metatheoryModules.contains m then some "metatheory"
  else if metaModules.contains m then some "meta"
  else if entryModules.contains m then some "entry"
  else none

def modOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

/-! ## Kernel facts named in the report -/

/-- The Nat operations the kernel's type checker is said to compute on literals (GMP-backed); the
    probes below check each one (in Lean 4.34.1, `Nat.log2` is not among them). -/
def natAccelOps : List Name := [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``Nat.pow, ``Nat.log2]

/-- Other constants the kernel knows by name, or that mark a computation done by the kernel. -/
def specialConsts : List Name := [``Nat, ``Nat.zero, ``Nat.succ, ``String, ``Char, ``Eq, ``HEq,
  ``Lean.reduceBool, ``Lean.reduceNat, ``Lean.ofReduceBool, ``Lean.ofReduceNat,
  ``Lean.trustCompiler, ``of_decide_eq_true, ``of_decide_eq_false, ``Decidable.decide]

/-! ## Static features of one declaration -/

structure Info where
  feats : Std.HashSet String := {}
  deps : NameSet := {}

def levelFeats (l : Level) : Array String := Id.run do
  let mut out := #[]
  let rec go : Level → Array String → Array String
    | .zero, a => a
    | .succ l, a => go l a
    | .max l r, a => go r (go l (a.push "level.max"))
    | .imax l r, a => go r (go l (a.push "level.imax"))
    | .param _, a => a.push "level.param"
    | .mvar _, a => a
  out := go l out
  return out

def sortFeat (l : Level) : String :=
  if l.isZero then "sort.Prop"
  else match l.toNat with
    | some 1 => "sort.Type"
    | some _ => "sort.TypeN"
    | none => "sort.poly"

/-- Is `I` an inductive type whose sort is `Prop` (after its parameters and indices)? -/
def inProp (env : Environment) (I : Name) : Bool :=
  match env.find? I with
  | some (.inductInfo v) => match v.type.getForallBody with
    | .sort l => l.isZero
    | _ => false
  | _ => false

/-- A recursor of an inductive in `Prop` that eliminates into every sort: its extra universe
    parameter (the motive's) comes first. -/
def largePropRec? (env : Environment) (r : Name) : Bool :=
  match env.find? r with
  | some (.recInfo v) =>
    match env.find? v.getMajorInduct with
    | some (.inductInfo iv) => inProp env iv.name && v.levelParams.length > iv.levelParams.length
    | _ => false
  | _ => false

/-- Walk an expression once (shared subterms once), adding features and named constants. -/
partial def walk (env : Environment) (e : Expr) : StateT (Std.HashSet Expr) (StateM Info) Unit := do
  if (← get).contains e then return
  modify (·.insert e)
  let add (f : String) : StateT (Std.HashSet Expr) (StateM Info) Unit :=
    modifyThe Info fun i => { i with feats := i.feats.insert f }
  match e with
  | .sort l =>
    add (sortFeat l)
    for f in levelFeats l do add f
  | .const c us =>
    modifyThe Info fun i => { i with deps := i.deps.insert c }
    for u in us do for f in levelFeats u do add f
    if largePropRec? env c then
      if let some u := us.head? then
        unless u.isZero do add "rec.largeElimFromProp.used"
    if let some (.recInfo v) := env.find? c then
      if v.k then add "rec.k.used"
  | .lit (.natVal _) => add "lit.nat"
  | .lit (.strVal _) => add "lit.string"
  | .proj _ _ b => add "expr.proj"; walk env b
  | .letE _ t v b _ => add "expr.let"; walk env t; walk env v; walk env b
  | .app f a => walk env f; walk env a
  | .lam _ t b _ => walk env t; walk env b
  | .forallE _ t b _ => walk env t; walk env b
  | .mdata _ b => walk env b
  | .bvar _ => pure ()
  | .fvar _ | .mvar _ => add "expr.openTerm"

def structureLike (v : InductiveVal) : Bool :=
  v.all.length == 1 && v.ctors.length == 1 && v.numIndices == 0 && !v.isRec

def infoOf (env : Environment) (ci : ConstantInfo) : Info := Id.run do
  let mut fs : Array String := #[]
  let mut deps : NameSet := {}
  let c := ci.name
  unless ci.levelParams.isEmpty do fs := fs.push "decl.universePolymorphic"
  match ci with
  | .axiomInfo _ => fs := fs.push "decl.axiom"
  | .defnInfo v =>
    fs := fs.push "decl.definition"
    fs := fs.push (match v.safety with
      | .safe => "def.safe" | .partial => "def.partial" | .unsafe => "def.unsafeSafety")
    fs := fs.push (match v.hints with
      | .opaque => "def.hints.opaque" | .abbrev => "def.hints.abbrev" | .regular _ => "def.hints.regular")
  | .thmInfo _ => fs := fs.push "decl.theorem"
  | .opaqueInfo v =>
    fs := fs.push "decl.opaque"
    if v.isUnsafe then fs := fs.push "opaque.unsafeFlag"
  | .quotInfo v =>
    fs := fs.push "decl.quotPrimitive"
    for q in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, ``Eq] do deps := deps.insert q
    let _ := v
  | .inductInfo v =>
    fs := fs.push "decl.inductive"
    if v.numIndices > 0 then fs := fs.push "ind.indexed"
    if v.all.length > 1 then fs := fs.push "ind.mutual"
    if v.numNested > 0 then fs := fs.push "ind.nested"
    if v.isRec then fs := fs.push "ind.recursive"
    if v.isReflexive then fs := fs.push "ind.reflexive"
    if v.isUnsafe then fs := fs.push "ind.unsafeFlag"
    if v.numIndices == 0 && v.all.length == 1 && v.numNested == 0 then fs := fs.push "ind.plain"
    if inProp env c then fs := fs.push "ind.prop"
    if structureLike v then
      fs := fs.push "ind.structureLike"
      if let some (.ctorInfo cv) := env.find? v.ctors.head! then
        if cv.numFields == 0 then fs := fs.push "ind.structureLike.noFields"
    for n in v.all do
      deps := deps.insert n
      deps := deps.insert (mkRecName n)
    for n in v.ctors do deps := deps.insert n
  | .ctorInfo v =>
    fs := fs.push "decl.constructor"
    deps := deps.insert v.induct
  | .recInfo v =>
    fs := fs.push "decl.recursor"
    if v.k then fs := fs.push "rec.k"
    if largePropRec? env c then fs := fs.push "rec.largeElimFromProp"
    for n in v.all do deps := deps.insert n
  -- the elaborator's and the compiler's attributes (the kernel reads neither)
  if ci matches .defnInfo _ | .thmInfo _ | .opaqueInfo _ then
    match getReducibilityStatusCore env c with
    | .irreducible => fs := fs.push "attr.irreducible"
    | .reducible => fs := fs.push "attr.reducible"
    | _ => pure ()
  if (Compiler.getImplementedBy? env c).isSome then fs := fs.push "attr.implementedBy"
  if isExtern env c then fs := fs.push "attr.externAttr"
  if (`_unsafe_rec).isSuffixOf c then fs := fs.push "name.unsafeRec"
  -- the nodes of the type and the value
  let value? : Option Expr := match ci with
    | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value
    | _ => none
  let go : StateT (Std.HashSet Expr) (StateM Info) Unit := do
    walk env ci.type
    if let some v := value? then walk env v
  let ((_, _), i) := (go.run {}).run {}
  let mut feats := i.feats
  for f in fs do feats := feats.insert f
  for d in i.deps do
    deps := deps.insert d
    if natAccelOps.contains d then feats := feats.insert s!"nat.op.{d}"
    if specialConsts.contains d then feats := feats.insert s!"const.{d}"
    match env.find? d with
    | some (.quotInfo _) => feats := feats.insert s!"quot.{d}"
    | some (.axiomInfo _) => feats := feats.insert s!"axiom.{d}"
    | _ => pure ()
  return { feats, deps }

/-! ## Closures, columns, the report -/

/-- The static information of `roots` and of everything they reach. -/
def collectInfos (env : Environment) (roots : Array Name) : Except String (Std.HashMap Name Info) := do
  let mut infos : Std.HashMap Name Info := {}
  let mut todo := roots
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if infos.contains c then continue
    let some ci := env.find? c | throw s!"unknown constant {c}"
    let i := infoOf env ci
    infos := infos.insert c i
    for d in i.deps do unless infos.contains d do todo := todo.push d
  return infos

/-- The closure of `roots`, with for each member the declaration through which it was first reached
    (breadth first, so a shortest path). -/
def closureWithParents (infos : Std.HashMap Name Info) (roots : Array Name) :
    Std.HashMap Name Name := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  for r in roots do parent := parent.insert r .anonymous
  let mut layer := roots
  while !layer.isEmpty do
    let mut next := #[]
    for c in layer do
      if let some i := infos.get? c then
        for d in (i.deps.toArray.qsort Name.lt) do
          unless parent.contains d do
            parent := parent.insert d c
            next := next.push d
    layer := next
  return parent

def closure (infos : Std.HashMap Name Info) (roots : Array Name) : NameSet :=
  (closureWithParents infos roots).fold (fun s c _ => s.insert c) {}

/-- The path from a root to `c`. -/
def pathTo (parent : Std.HashMap Name Name) (c : Name) : Array Name := Id.run do
  let mut out := #[c]
  let mut cur := c
  for _ in [:10000] do
    match parent.get? cur with
    | some p => if p.isAnonymous then break else out := out.push p; cur := p
    | none => break
  return out.reverse

/-- Does the type of `c` name a constant of the `Lean` namespace? Then `c` is notation or meta code
    (syntax, macros, elaborators and what Lean generates for them), whatever its module. -/
def isNotation (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => (ci.type.getUsedConstants.any fun d => (`Lean).isPrefixOf d)
  | none => false

/-- Names for examples: the ones written by hand first, then by their text. -/
def exampleOrder (a b : Name) : Bool :=
  if a.isInternalDetail != b.isInternalDetail then !a.isInternalDetail else a.toString < b.toString

def featureTable (infos : Std.HashMap Name Info) (decls : Array Name)
    (parent? : Option (Std.HashMap Name Name) := none) (nEx : Nat := 5) : Json := Id.run do
  let mut byFeat : Std.HashMap String (Array Name) := {}
  for c in decls do
    if let some i := infos.get? c then
      for f in i.feats do byFeat := byFeat.insert f ((byFeat.getD f #[]).push c)
  let keys := byFeat.toArray.map (·.1) |>.qsort (· < ·)
  return Json.mkObj <| keys.toList.map fun f =>
    let cs := (byFeat.getD f #[]).qsort exampleOrder
    let why := match parent? with
      | some p => [("path", toJson ((pathTo p cs[0]!).map (·.toString)))]
      | none => []
    (f, Json.mkObj ([("count", toJson cs.size),
      ("examples", toJson ((cs.extract 0 nEx).map (·.toString)))] ++ why))

/-- Every declaration of `decls` with each feature (all of them, for merging sets across runs). -/
def featureSets (infos : Std.HashMap Name Info) (decls : Array Name) : Json := Id.run do
  let mut byFeat : Std.HashMap String (Array Name) := {}
  for c in decls do
    if let some i := infos.get? c then
      for f in i.feats do byFeat := byFeat.insert f ((byFeat.getD f #[]).push c)
  let keys := byFeat.toArray.map (·.1) |>.qsort (· < ·)
  return Json.mkObj <| keys.toList.map fun f =>
    (f, toJson (((byFeat.getD f #[]).qsort exampleOrder).map (·.toString)))

def kindCounts (env : Environment) (decls : Array Name) : Json := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for c in decls do
    let k := match env.find? c with
      | some (.axiomInfo _) => "axiom" | some (.defnInfo _) => "definition"
      | some (.thmInfo _) => "theorem" | some (.opaqueInfo _) => "opaque"
      | some (.quotInfo _) => "quot" | some (.inductInfo _) => "inductive"
      | some (.ctorInfo _) => "constructor" | some (.recInfo _) => "recursor" | none => "?"
    m := m.insert k (m.getD k 0 + 1)
  return Json.mkObj (m.toList.map fun (k, n) => (k, toJson n))

/-! ## The kernel re-check -/

/-- The renamed copy of a theorem, definition or opaque constant, if it is one the kernel checks. -/
def copyDecl (ci : ConstantInfo) : Option Declaration :=
  let n := ci.name ++ `_kernelCensusCopy
  match ci with
  | .thmInfo v => some (.thmDecl { v with name := n, all := [n] })
  | .defnInfo v =>
    if v.safety matches .safe then some (.defnDecl { v with name := n, all := [n] }) else none
  | .opaqueInfo v => if v.isUnsafe then none else some (.opaqueDecl { v with name := n, all := [n] })
  | _ => none

structure Recheck where
  unfolded : Std.HashMap Name (Array Name) := {}  -- declaration ↦ the constants unfolded
  total : Std.HashMap Name Nat := {}              -- declaration ↦ the number of unfoldings
  failed : Array Name := #[]
  skipped : Array Name := #[]

def recheck (env : Environment) (decls : Array Name) : Recheck := Id.run do
  let opts : Options := maxHeartbeats.set ({} : Options) 0
  let kenv := (env.toKernelEnv.enableDiag true)
  let mut r : Recheck := {}
  for c in decls do
    let some ci := env.find? c | continue
    let some d := copyDecl ci | do r := { r with skipped := r.skipped.push c }; continue
    match Kernel.Environment.addDecl kenv opts d with
    | .ok k' =>
      let m := k'.getDiagnostics.unfoldCounter
      let names := m.toList.map (·.1) |>.toArray
      r := { r with unfolded := r.unfolded.insert c names,
                    total := r.total.insert c (m.foldl (fun a _ n => a + n) 0) }
    | .error _ => r := { r with failed := r.failed.push c }
  return r

/-- What kind of constant the kernel unfolded. -/
def unfoldClasses (env : Environment) (u : Name) : Array String := Id.run do
  let mut out := #[]
  out := out.push (if isRepoModule (modOf env u) then "unfold.repository" else "unfold.core")
  match env.find? u with
  | some (.thmInfo _) => out := out.push "unfold.theorem"
  | some (.defnInfo v) =>
    out := out.push (match v.hints with
      | .opaque => "unfold.hints.opaque" | .abbrev => "unfold.hints.abbrev"
      | .regular _ => "unfold.hints.regular")
  | some (.opaqueInfo _) => out := out.push "unfold.opaque"
  | some (.recInfo _) => out := out.push "unfold.recursor"
  | some (.quotInfo _) => out := out.push "unfold.quot"
  | _ => out := out.push "unfold.other"
  if getReducibilityStatusCore env u matches .irreducible then out := out.push "unfold.attr.irreducible"
  if (Compiler.getImplementedBy? env u).isSome then out := out.push "unfold.attr.implementedBy"
  if isExtern env u then out := out.push "unfold.attr.externAttr"
  if natAccelOps.contains u then out := out.push s!"unfold.nat.op.{u}"
  if [`String, `Char, `ByteArray].any (·.isPrefixOf u) then out := out.push "unfold.stringInternals"
  return out

def unfoldTable (env : Environment) (r : Recheck) (decls : Array Name) : Json := Id.run do
  let mut byFeat : Std.HashMap String (Array Name) := {}
  let mut consts : Std.HashMap String NameSet := {}
  let mut nChecked := 0
  let mut nAny := 0
  for c in decls do
    let some us := r.unfolded.get? c | continue
    nChecked := nChecked + 1
    if !us.isEmpty then nAny := nAny + 1
    let mut fs : Std.HashSet String := {}
    for u in us do
      for f in unfoldClasses env u do
        fs := fs.insert f
        consts := consts.insert f ((consts.getD f {}).insert u)
    for f in fs do byFeat := byFeat.insert f ((byFeat.getD f #[]).push c)
  let keys := byFeat.toArray.map (·.1) |>.qsort (· < ·)
  let heavy := (decls.filterMap fun c => (r.total.get? c).map (c, ·)).qsort
    (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1.toString < b.1.toString))
  let inSet (s : Array Name) := s.filter decls.contains
  return Json.mkObj [
    ("checked", toJson nChecked), ("unfoldedAnything", toJson nAny),
    ("failed", toJson ((inSet r.failed).map (·.toString))),
    ("skipped", toJson (inSet r.skipped).size),
    ("totalUnfoldings", toJson (heavy.foldl (fun a (_, n) => a + n) 0)),
    ("heaviest", toJson ((heavy.extract 0 10).map fun (c, n) => Json.mkObj
      [("decl", toJson c.toString), ("unfoldings", toJson n)])),
    ("features", Json.mkObj <| keys.toList.map fun f =>
      let cs := (byFeat.getD f #[]).qsort exampleOrder
      let us := ((consts.getD f {}).toArray).qsort exampleOrder
      (f, Json.mkObj [("count", toJson cs.size),
        ("examples", toJson ((cs.extract 0 5).map (·.toString))),
        ("constants", toJson us.size),
        ("constantExamples", toJson ((us.extract 0 8).map (·.toString)))]))]

/-- Probes of the kernel's Nat acceleration: `op a b = c` by `Eq.refl`, with large literals. -/
def natProbes (env : Environment) : Json := Id.run do
  let big : Nat := 2 ^ 200 + 12345
  let mid : Nat := 2 ^ 130 + 777
  let cases : List (Name × Nat × Nat × Expr) := [
    (``Nat.add, big, mid, mkRawNatLit (big + mid)), (``Nat.sub, big, mid, mkRawNatLit (big - mid)),
    (``Nat.mul, big, mid, mkRawNatLit (big * mid)), (``Nat.div, big, mid, mkRawNatLit (big / mid)),
    (``Nat.mod, big, mid, mkRawNatLit (big % mid)), (``Nat.gcd, big, mid, mkRawNatLit (Nat.gcd big mid)),
    (``Nat.beq, big, big, mkConst ``Bool.true), (``Nat.ble, mid, big, mkConst ``Bool.true),
    (``Nat.land, big, mid, mkRawNatLit (big &&& mid)), (``Nat.lor, big, mid, mkRawNatLit (big ||| mid)),
    (``Nat.xor, big, mid, mkRawNatLit (big ^^^ mid)),
    (``Nat.shiftLeft, big, 300, mkRawNatLit (big <<< 300)),
    (``Nat.shiftRight, big, 100, mkRawNatLit (big >>> 100)),
    (``Nat.pow, mid, 40, mkRawNatLit (mid ^ 40)), (``Nat.log2, big, 0, mkRawNatLit (Nat.log2 big))]
  let opts : Options := maxHeartbeats.set ({} : Options) 0
  let kenv := env.toKernelEnv.enableDiag true
  let mut out := #[]
  for (op, a, b, res) in cases do
    let lhs := if op == ``Nat.log2 then mkApp (mkConst op) (mkRawNatLit a)
      else mkApp2 (mkConst op) (mkRawNatLit a) (mkRawNatLit b)
    let ty := if op == ``Nat.beq || op == ``Nat.ble then mkConst ``Bool else mkConst ``Nat
    let stmt := mkApp3 (mkConst ``Eq [1]) ty lhs res
    let prf := mkApp2 (mkConst ``Eq.refl [1]) ty lhs
    let n := (`KernelCensus.probe).str op.toString
    let d := Declaration.thmDecl { name := n, levelParams := [], type := stmt, value := prf, all := [n] }
    let (ok, us) : Bool × List String := match Kernel.Environment.addDecl kenv opts d with
      | .ok k' => (true, k'.getDiagnostics.unfoldCounter.toList.map fun (u, _) => u.toString)
      | .error _ => (false, [])
    out := out.push (Json.mkObj [("op", toJson op.toString), ("checked", toJson ok),
      ("unfolded", toJson us), ("accelerated", toJson (ok && !us.contains op.toString))])
  return toJson out

end KernelCensus

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
open KernelCensus in
#eval show CommandElabM Unit from do
  let mode := (← IO.getEnv "PM_CENSUS_MODE").getD "full"
  let path := (← IO.getEnv "PM_CENSUS_OUT").getD ".lake/kernel_census/census.json"
  if let some d := (System.FilePath.mk path).parent then IO.FS.createDirAll d
  let t0 ← IO.monoMsNow
  let env ← getEnv
  -- the repository's declarations, by group; a module of the repository in no group stops the run
  let mut groups : Std.HashMap String (Array Name) := {}
  for (c, _) in env.constants.toList do
    let m := modOf env c
    unless isRepoModule m do continue
    let some g := groupOf m | throwError "module {m} is in no group of the census (scripts/kernel_census/KernelCensus.lean)"
    let g := if g != "entry" && isNotation env c then "meta" else g
    let g := if g != "entry" && g != "meta" && isCheck c then "checks" else g
    groups := groups.insert g ((groups.getD g #[]).push c)
  unless (groups.getD "entry" #[]).isEmpty do
    throwError "entry files declare {groups.getD "entry" #[]}"
  -- every declaration's static information, for everything reachable from the repository (in mode
  -- `ratchet`, not from the meta code: two thirds of the walk, and not needed by the ratchet)
  let walked := (if mode == "ratchet" then ["derivations", "foundations", "metatheory", "checks"]
    else ["derivations", "foundations", "metatheory", "checks", "meta"]).foldl
      (fun a g => a ++ groups.getD g #[]) #[]
  let infos ← match collectInfos env walked with
    | .ok i => pure i
    | .error e => throwError e
  let t1 ← IO.monoMsNow
  let sorted (s : NameSet) : Array Name := s.toArray.qsort Name.lt
  let isRepo (c : Name) : Bool := isRepoModule (modOf env c)
  let gA := groups.getD "derivations" #[]
  let gF := groups.getD "foundations" #[]
  let gB := groups.getD "metatheory" #[]
  let gM := groups.getD "meta" #[]
  let gC := groups.getD "checks" #[]
  let pA := closureWithParents infos gA
  let clA := closure infos gA
  let pAFB := closureWithParents infos (gA ++ gF ++ gB)
  let clAFB := closure infos (gA ++ gF ++ gB)
  let pM := closureWithParents infos gM
  let clM := closure infos gM
  let pC := closureWithParents infos gC
  let clC := closure infos gC
  let core := (sorted clAFB).filter (!isRepo ·)
  let metaCore := (sorted clM).filter fun c => !isRepo c && !clAFB.contains c
  -- the derivation theorems proper: a theorem of the repository concluding `Thm`, `QThm` or `Thm9`
  let derivHeads := [``PM.Thm, ``PM.QThm, ``PM.F9.Thm9]
  let mut proper := #[]
  for c in gA ++ gF ++ gB do
    if let some (.thmInfo v) := env.find? c then
      if derivHeads.any (v.type.getForallBody.getAppFn.constName? == some ·) then proper := proper.push c
  let pP := closureWithParents infos proper
  let clP := closure infos proper
  -- meta code reached from a proof: there should be none
  let gMs : NameSet := gM.foldl (·.insert ·) {}
  let metaReached := (sorted clAFB).filter gMs.contains
  -- axioms: which repository declarations depend on each
  -- (everything from which an axiom is reachable, by the reversed uses)
  let mut usedBy : Std.HashMap Name (Array Name) := {}
  for (c, i) in infos.toList do
    for d in i.deps do usedBy := usedBy.insert d ((usedBy.getD d #[]).push c)
  let axioms := (infos.toList.filterMap fun (c, _) =>
    if env.find? c matches some (.axiomInfo _) then some c else none).toArray.qsort Name.lt
  let mut reaching : Std.HashMap Name NameSet := {}
  for a in axioms do
    let mut seen : NameSet := ({} : NameSet).insert a
    let mut todo := #[a]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      for u in usedBy.getD c #[] do
        unless seen.contains u do
          seen := seen.insert u
          todo := todo.push u
    reaching := reaching.insert a seen
  let users (ds : Array Name) : Std.HashMap Name (Array Name) := Id.run do
    let mut m := {}
    for a in axioms do
      let r := reaching.getD a {}
      let us := (ds.filter r.contains).qsort Name.lt
      unless us.isEmpty do m := m.insert a us
    return m
  let uAFB := users (gA ++ gF ++ gB ++ gC)
  let uM := users gM
  let axNames := ((uAFB.toList ++ uM.toList).map (·.1)).eraseDups.toArray.qsort Name.lt
  let axJson := Json.mkObj <| axNames.toList.map fun a => (a.toString, Json.mkObj [
    ("repository", toJson ((uAFB.getD a #[]).map (·.toString))),
    ("meta", toJson ((uM.getD a #[]).map (·.toString)))])
  -- the columns
  let cols : List (String × Array Name × Option (Std.HashMap Name Name)) := [
    ("derivations", gA, none), ("foundations", gF, none), ("metatheory", gB, none),
    ("core", core, some pAFB), ("derivationClosure", sorted clA, some pA),
    ("proofClosure", sorted clP, some pP), ("checks", gC, none), ("checksClosure", sorted clC, some pC),
    ("meta", gM, none), ("metaCore", metaCore, some pM)]
  let colsJson := cols.map fun (k, ds, p) => (k, Json.mkObj [("declarations", toJson ds.size),
    ("kinds", kindCounts env ds), ("features", featureTable infos ds p)])
  let checksByModule : Std.HashMap String Nat := gC.foldl (init := {}) fun m c =>
    let k := (modOf env c).toString
    m.insert k (m.getD k 0 + 1)
  -- the kernel re-check
  let mut recheckJson := Json.null
  let mut probes := Json.null
  if mode == "full" then
    let r := recheck env (sorted ((sorted clC).foldl (·.insert ·) clAFB))
    recheckJson := Json.mkObj (cols.filterMap fun (k, ds, _) =>
      if k == "meta" || k == "metaCore" then none else some (k, unfoldTable env r ds))
    probes := natProbes env
  let t2 ← IO.monoMsNow
  let j := Json.mkObj [("toolchain", toJson Lean.versionString), ("mode", toJson mode),
    ("modules", Json.mkObj [("derivations", toJson (derivationModules.map (·.toString))),
      ("foundations", toJson (foundationModules.map (·.toString))),
      ("metatheory", toJson (metatheoryModules.map (·.toString))),
      ("meta", toJson (metaModules.map (·.toString))),
      ("entry", toJson (entryModules.map (·.toString)))]),
    ("proofTheorems", toJson proper.size),
    ("checksByModule", Json.mkObj (checksByModule.toList.map fun (m, n) => (m, toJson n))),
    ("closureCore", Json.mkObj [("derivationClosure", toJson ((sorted clA).filter (!isRepo ·)).size),
      ("proofClosure", toJson ((sorted clP).filter (!isRepo ·)).size)]),
    ("metaReached", toJson (metaReached.map (·.toString))),
    ("columns", Json.mkObj colsJson), ("axiomUsers", axJson),
    ("recheck", recheckJson), ("natProbes", probes),
    ("timing", Json.mkObj [("staticMs", toJson (t1 - t0)), ("totalMs", toJson (t2 - t0))])]
  IO.FS.writeFile path (j.pretty 120 ++ "\n")
  logInfo m!"kernel census ({mode}): {gA.size + gF.size + gB.size + gC.size + gM.size} repository declarations ({gC.size} check theorems), {infos.size} walked with their closure; {proper.size} derivation theorems; written to {path}"
