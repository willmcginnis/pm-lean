-- Statement mutation: is each statement tied to its proof? Run by scripts/mutation/mutate.py, which
-- sets PM_MUTATION_MODE (`full` or `quick`) and PM_MUTATION_OUT (a JSON-lines file this writes);
-- docs/STATEMENT_MUTATION.md says what each record means.
--
-- Part 1, unused hypotheses (every theorem of the PM and Checks libraries written in the source, told
-- from what Lean generates by its declaration range, not by its name). A hypothesis is a binder of
-- the statement that is a premise (its type is a proposition), an instance of a class of ours
-- (`[Reducibility S]`), or a variable that occurs nowhere in the rest of the statement (a real variable
-- such as ✱10·25's y, which only asks for an argument to exist). It is unused when the proof term, with
-- the binder instantiated, does not mention it. Two refinements, both only ever turning "used" into
-- "unused": a `have`/`let` whose value is never used does not count, and neither does an argument
-- passed to another theorem in a position that theorem itself does not use (iterated to a fixed point).
-- `shallow` is the plain occurrence test, `deep` the refined one.
--
-- Part 2, statement mutants. For ✱1–✱5 (each `t…`, `pm2_7…` with a statement `Thm (s… p q …)`, and the
-- primitive propositions ✱1·2–✱1·6 against their constructors) and from ✱9 on (`q…`, `QL.t…`, `F9.f…`),
-- a fixed family of one-change mutants of the asserted formula: ∨ ↔ ∧ at one node, an implication
-- replaced by its consequent, ≡ → ⊃ at one node (and ≡ₓ → ⊃ₓ), one subformula negated, one occurrence
-- of a variable replaced by another of the same type (the shape of the ebook's slip in ✱1·4), two
-- variables of the same type exchanged throughout (a renaming: an equivalent statement, kept as a
-- control). For each mutant: whether the original proof term type-checks against it (`Kernel.check` of
-- the proof once, then `Kernel.isDefEq` of its type with the mutant), and whether it is a tautology by
-- the repository's own test `F.isTaut`, evaluated by the kernel (from ✱9 on: of its propositional
-- skeleton, each subformula not built by a connective an atom). The control of each statement is the
-- unchanged formula, rebuilt the way the mutants are; the proof must check against it.
--
-- How the proof's type `pty` is compared with a mutant `mty` (PM_MUTATION_METHOD; the section "How a
-- mutant is compared" of docs/STATEMENT_MUTATION.md has the measurements):
--   direct   `Kernel.isDefEq env {} pty mty`. On the class and relation statements of ✱22–✱25 the
--            kernel's lazy unfolding explores many unfoldings before it concludes "not equal".
--   normal   (the default) `Kernel.isDefEq env {} (nf pty) (nf mty)`, where `nf` applies `Kernel.whnf`
--            at the root and then, recursively, in every argument, under every binder and in every
--            binder type, memoized per statement.
--   both     both, every verdict recorded twice (`mutate.py --compare-methods`); `direct` decides.
-- Why `normal` should give `direct`'s verdict, and how far that is shown (docs/STATEMENT_MUTATION.md
-- has the argument in full). (1) Every step of `nf` replaces a subterm by the kernel's own weak head
-- normal form of it, so `nf t ≡ t`. (2) If `≡` were transitive on the four terms, `pty ≡ mty` iff
-- `nf pty ≡ nf mty`. It is not transitive in general. In the kernel of Lean v4.34.1
-- (src/kernel/type_checker.cpp, inductive.h) the rules that break it, or that compare anything but the
-- two trees, are: proof irrelevance and K-like reduction, which need a proof; eta for structures, which
-- needs an application of a structure's constructor; eta for unit-like types, which needs a term of a
-- unit-like type (after eta for functions, a function into one); and string-literal expansion, which
-- needs an application of `String`'s constructor. `auditNode` checks every subterm of both normal
-- forms for these: every node of the tree, projections and the partial applications of an
-- application's spine included. It decides as the kernel does, which ignores reducibility attributes:
-- "a proof" and "unit-like" are decided on `Kernel.whnf` of the inferred types (the function the
-- kernel's `is_prop` and unit-like eta reduce by), the types inferred at transparency `all`; "a
-- structure's constructor" reads the head of the normal form, already the kernel's whnf. A flagged
-- statement is decided by `direct` (the ✱9 statements of PM/Found9/Star9.lean, whose normal forms
-- contain `Reading.mk`, `PProd.mk` and `PUnit.unit`). A comparison also falls back when a normal form
-- needs more than the bound of steps, or the kernel or the inference of a type reports an error.
-- With a clean audit the kernel compares the two normal forms as trees, up to eta
-- for functions, universe levels and Nat literals against `Nat.zero`/`Nat.succ`. Not shown: that a
-- proof (or constructor, or unit-like term) that `direct` meets only inside a reduction that removes it
-- from both normal forms cannot change its verdict, nor that the kernel's algorithm finds every
-- equality. So this is a conservative syntactic check with a fallback, not a proof of transitivity.
-- `nfSelfTest` plants a case of each kind, the two cases it once missed among them (a proof-valued
-- projection; a proof whose type is a proposition only behind an irreducible definition), and a
-- projection whose type is `PUnit` behind one; the run fails if one is missed. The evidence for the rest: the two methods run side by
-- side (`--compare-methods`) on every statement but ✱25·431 and ✱25·432 (an hour each for `direct`)
-- with identical verdicts on every mutant and control, and a full run of each with identical verdicts
-- on all 16,512 mutants, those two included.
import Lean
import PM
import Checks.PinnedStatements
open Lean Meta Elab Command

/-! Planted cases that Part 1 must classify as marked (it fails otherwise). Lean's unused-variables
    linter sees only the first, fourth and the last two. The last two are named the way Lean names what
    it generates (`eq_…`, a private name): they must not be mistaken for generated declarations. -/
namespace PMMutationTest
open PM
set_option linter.unusedVariables false
/-- unused: a premise the proof never mentions -/
theorem unusedPremise (p : F) (h : Thm (.neg p)) : Thm (F.imp p p) := t2_08 p
/-- unused: the premise feeds only a `have` that is never used -/
theorem deadHave (p : F) (h : Thm p) : Thm (F.imp p p) :=
  have _h2 : Thm (F.or p p) := t2_2 p p |> fun d => Thm.mp h d
  t2_08 p
/-- unused (deep only): the premise is passed to `unusedPremise`, which ignores it -/
theorem passesToUnused (p : F) (h : Thm (.neg p)) : Thm (F.imp p p) := unusedPremise p h
/-- unused: a variable that occurs neither in the statement nor in the proof -/
theorem unusedVariable {V : Ty → Type} {S : Sys} {τ : Ty} (p : QF V) (y : V τ) :
    QThm S (QF.imp p p) := QL.t2_08 p
/-- unused: a class of ours the proof does not need -/
theorem unusedClass {V : Ty → Type} {S : Sys} [Reducibility S] (p : QF V) :
    QThm S (QF.imp p p) := QL.t2_08 p
/-- unused: a premise the proof never mentions, in a theorem named like an equation lemma -/
theorem eq_unusedPremise (n : Nat) (h : True) : n = n := rfl
/-- unused: a premise the proof never mentions, in a private theorem -/
private theorem privateUnusedPremise (p : F) (h : Thm (.neg p)) : Thm (F.imp p p) := t2_08 p
/-- used: the control -/
theorem usedPremise (p q : F) (h : Thm p) (hpq : Thm (F.imp p q)) : Thm q := Thm.mp h hpq
end PMMutationTest

/-! Planted terms for the audit of normal forms (`PMMutation.nfSelfTest`). `witnessLeft` and
    `witnessRight` are equal for the direct comparison: unfolding `pick` on both sides, the two
    proofs of `Acc accRel 0` are equal by proof irrelevance. Their normal forms are not: the
    recursor on the projection `b.proof` is stuck, the one on `Acc.intro` computes `0`. The audit
    must flag the projection, a proof, so that `direct` decides. `unitProjection` is a projection of
    a unit-like type. The `hidden…` cases below are the same behind irreducible definitions. -/
namespace PMNfTest
def accRel (_ _ : Nat) : Prop := False
structure ProofBox : Type where
  proof : Acc accRel 0
noncomputable def pick (h : Acc accRel 0) : Nat :=
  @Acc.rec Nat accRel (fun _ _ => Nat) (fun _ _ _ => 0) 0 h
def witnessLeft : Prop := ∀ b : ProofBox, pick b.proof = 0
def witnessRight : Prop := ∀ _b : ProofBox, pick (Acc.intro 0 (fun _ h => False.elim h)) = 0
structure UnitBox : Type where
  unit : PUnit.{1}
  n : Nat
def unitProjection : UnitBox → PUnit.{1} := fun b => b.unit
/-! The same two cases behind an irreducible definition, which the kernel unfolds: `HiddenProp` is
    `Prop`, so the variable `h` of `hiddenLeft` is a proof; `HiddenUnit` is `PUnit`. -/
def HiddenProp := Prop
def HiddenAcc : HiddenProp := Acc accRel 0
noncomputable def hiddenPick (h : HiddenAcc) : Nat :=
  @Acc.rec Nat accRel (fun _ _ => Nat) (fun _ _ _ => 0) 0 h
def hiddenLeft : Prop := ∀ h : HiddenAcc, hiddenPick h = 0
def hiddenRight : Prop := ∀ _h : HiddenAcc, hiddenPick (Acc.intro 0 (fun _ h => False.elim h)) = 0
attribute [irreducible] HiddenProp
@[irreducible] def HiddenUnit := PUnit.{1}
structure HiddenUnitBox : Type where
  unit : HiddenUnit
  n : Nat
def hiddenUnitProjection : HiddenUnitBox → HiddenUnit := fun b => b.unit
end PMNfTest

namespace PMMutation

/-! ## Common -/

def modOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

def inRepo (m : Name) : Bool := (`PM).isPrefixOf m || (`Checks).isPrefixOf m

/-- Is `c` written in the source? Lean records a declaration range (`declRangeExt`) for every
    declaration elaborated from the text, private theorems and a structure's fields included, and for
    none that it generates (equation lemmas, injectivity, `sizeOf`, matchers, auxiliary proofs …). The
    name does not decide: a theorem of ours may well be called `eq_…`. -/
def isWritten (c : Name) : MetaM Bool := return (← findDeclarationRangesCore? c).isSome

/-- Lean's own mark of a generated declaration, as a cross-check of `isWritten`: a theorem with no
    declaration range must carry one, or the run fails. -/
def generatedMark? (env : Environment) (c : Name) : Option String :=
  if c.isInternal then some "internal name"
  else if isReservedName env c then some "reserved name (equation lemma)"
  else if isAuxRecursor env c || isNoConfusion env c then some "auxiliary recursor"
  else if Meta.isMatcherCore env c || Meta.Match.isMatchEqnTheorem env c then some "matcher"
  else match c with
    | .str p _ =>
      if isAuxRecursor env p then some "equation of an auxiliary recursor"
      else match env.find? p with
        | some (.ctorInfo _) => some "lemma of a constructor (injectivity, size)"
        | some (.inductInfo _) => some "lemma of an inductive type"
        | _ => none
    | _ => none

def jstr (s : String) : Json := Json.str s

/-- Where a declaration is: its file's module, the lines of its name and of its end. -/
def whereOf (c : Name) : MetaM (List (String × Json)) := do
  let m := modOf (← getEnv) c
  match ← findDeclarationRanges? c with
  | some r => return [("module", jstr m.toString), ("line", toJson r.selectionRange.pos.line),
      ("endLine", toJson r.range.endPos.line)]
  | none => return [("module", jstr m.toString), ("line", toJson (0 : Nat)), ("endLine", toJson (0 : Nat))]

/-! ## Part 1: unused hypotheses -/

/-- Positions (in a constant's binder telescope) of hypotheses that its proof does not use. -/
abbrev Ignored := NameMap (Array Nat)

/-- Does the fvar `x` occur in `e`, not counting dead `have`/`let` values and arguments in positions
    the callee ignores? -/
partial def occurs (ig : Ignored) (x : FVarId) (e : Expr) : Bool :=
  if !e.hasFVar then false else
  match e with
  | .fvar y => y == x
  | .mdata _ b => occurs ig x b
  | .proj _ _ b => occurs ig x b
  | .lam _ t b _ => occurs ig x t || occurs ig x b
  | .forallE _ t b _ => occurs ig x t || occurs ig x b
  | .letE _ t v b _ =>
    if b.hasLooseBVar 0 then occurs ig x t || occurs ig x v || occurs ig x b else occurs ig x b
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .lam _ t b _ =>
      -- `(fun y => b) a …`: a `have` in term form; its value counts only if `y` is used
      if b.hasLooseBVar 0 then occurs ig x t || occurs ig x b || args.any (occurs ig x)
      else occurs ig x b || (args.extract 1 args.size).any (occurs ig x)
    | .const c _ =>
      if c == ``letFun && args.size ≥ 4 then
        match args[3]! with
        | .lam _ _ b _ =>
          if b.hasLooseBVar 0 then args.any (occurs ig x)
          else occurs ig x b || (args.extract 4 args.size).any (occurs ig x)
        | _ => args.any (occurs ig x)
      else
        let ign := (ig.find? c).getD #[]
        Id.run do
          for i in [:args.size] do
            if !ign.contains i && occurs ig x args[i]! then return true
          return false
    | _ => occurs ig x f || args.any (occurs ig x)
  | _ => false

inductive Kind | premise | cls | unref
  deriving BEq, Inhabited

def Kind.str : Kind → String
  | .premise => "premise" | .cls => "class" | .unref => "unreferenced variable"

structure Hyp where
  idx : Nat
  name : Name
  kind : Kind
  bi : BinderInfo
  ty : String

def biStr : BinderInfo → String
  | .default => "explicit" | .implicit => "implicit" | .strictImplicit => "strict implicit"
  | .instImplicit => "instance"

def isOurClass (ty : Expr) : Bool :=
  match ty.getAppFn.constName? with
  | some n => (`PM).isPrefixOf n
  | none => false

def hypsOf (type : Expr) : MetaM (Array Hyp) :=
  forallTelescope type fun xs concl => do
    let mut out := #[]
    for i in [:xs.size] do
      let d ← xs[i]!.fvarId!.getDecl
      let mut refd := concl.containsFVar d.fvarId
      for j in [i+1:xs.size] do
        if (← inferType xs[j]!).containsFVar d.fvarId then refd := true
      let tyS := toString (← ppExpr d.type)
      if d.binderInfo.isInstImplicit then
        if isOurClass d.type then out := out.push ⟨i, d.userName, .cls, d.binderInfo, tyS⟩
      else if ← isProp d.type then
        out := out.push ⟨i, d.userName, .premise, d.binderInfo, tyS⟩
      else if !refd then
        out := out.push ⟨i, d.userName, .unref, d.binderInfo, tyS⟩
    return out

def unusedOf (ig : Ignored) (type value : Expr) (hs : Array Hyp) : MetaM (Array Nat) :=
  forallTelescope type fun xs _ => do
    let body := value.beta xs
    return (hs.filter fun h => !occurs ig xs[h.idx]!.fvarId! body).map (·.idx)

def isTest (c : Name) : Bool := (`PMMutationTest).isPrefixOf (privateToUserName c)

def part1 (out : IO.FS.Handle) : MetaM (Nat × Nat × Nat) := do
  let env ← getEnv
  let all := (env.constants.fold (init := #[]) fun acc c ci =>
    match ci with
    | .thmInfo v => if inRepo (modOf env c) || isTest c then acc.push (c, v) else acc
    | _ => acc).qsort (fun a b => Name.lt a.1 b.1)
  -- the theorems written in the source; every other one must carry a mark of a generated declaration
  let mut thms := #[]
  let mut generated : Std.HashMap String Nat := {}
  for (c, v) in all do
    if ← isWritten c then thms := thms.push (c, v)
    else match generatedMark? env c with
      | some why => generated := generated.insert why ((generated.getD why 0) + 1)
      | none => throwError "{c} has no declaration range and no mark of a generated declaration"
  let mut withHyps : Array (Name × TheoremVal × Array Hyp) := #[]
  let mut nh := 0
  for (c, v) in thms do
    let hs ← hypsOf v.type
    nh := nh + hs.size
    unless hs.isEmpty do withHyps := withHyps.push (c, v, hs)
  -- shallow: the plain occurrence test (but dead `have`s skipped); deep: iterate to a fixed point
  let mut shallow : Ignored := {}
  for (c, v, hs) in withHyps do
    let u ← unusedOf {} v.type v.value hs
    unless u.isEmpty do shallow := shallow.insert c u
  let mut ig := shallow
  let mut changed := true
  let mut rounds := 0
  while changed do
    changed := false
    rounds := rounds + 1
    let mut next : Ignored := {}
    for (c, v, hs) in withHyps do
      let u ← unusedOf ig v.type v.value hs
      unless u.isEmpty do next := next.insert c u
      if u.size != ((ig.find? c).getD #[]).size then changed := true
    ig := next
  let mut nflag := 0
  let mut testFlags : Array String := #[]
  for (c, _, hs) in withHyps do
    let d := (ig.find? c).getD #[]
    let s := (shallow.find? c).getD #[]
    for h in hs do
      if d.contains h.idx then
        if isTest c then
          testFlags := testFlags.push s!"{c.componentsRev.head!}:{h.kind.str}:{s.contains h.idx}"
          continue
        nflag := nflag + 1
        let j := Json.mkObj ([("part", jstr "hyp"), ("decl", jstr c.toString)] ++ (← whereOf c) ++ [
          ("binder", jstr h.name.toString), ("index", toJson h.idx), ("kind", jstr h.kind.str),
          ("binderInfo", jstr (biStr h.bi)), ("type", jstr h.ty),
          ("shallow", toJson (s.contains h.idx))])
        out.putStrLn j.compress
  -- every hypothesis considered, with its verdict, for the recompile confirmations
  let mut byKind : Std.HashMap String Nat := {}
  for (c, _, hs) in withHyps do
    if isTest c then continue
    let d := (ig.find? c).getD #[]
    for h in hs do
      byKind := byKind.insert h.kind.str ((byKind.getD h.kind.str 0) + 1)
      let j := Json.mkObj ([("part", jstr "hypAll"), ("decl", jstr c.toString)] ++ (← whereOf c) ++ [
        ("binder", jstr h.name.toString), ("index", toJson h.idx), ("kind", jstr h.kind.str),
        ("binderInfo", jstr (biStr h.bi)), ("type", jstr h.ty), ("unused", toJson (d.contains h.idx))])
      out.putStrLn j.compress
  -- the planted cases: exactly these, with these shallow verdicts
  let expected := #["deadHave:premise:true", "eq_unusedPremise:premise:true",
    "passesToUnused:premise:false", "privateUnusedPremise:premise:true", "unusedClass:class:true",
    "unusedPremise:premise:true", "unusedVariable:unreferenced variable:true"]
  let got := testFlags.qsort (· < ·)
  unless got == expected do
    throwError "Part 1 misclassifies its planted cases: got {got}, expected {expected}"
  let ntest := (withHyps.filter fun (c, _, _) => isTest c).size
  let nhTest := (withHyps.filter fun (c, _, _) => isTest c).foldl (fun a (_, _, hs) => a + hs.size) 0
  let j := Json.mkObj [("part", jstr "hypSummary"),
    ("theorems", toJson ((thms.filter fun (c, _) => !isTest c).size)),
    ("withHypotheses", toJson (withHyps.size - ntest)), ("hypotheses", toJson (nh - nhTest)),
    ("byKind", toJson (byKind.toList.map fun (k, n) => Json.mkObj [(k, toJson n)])),
    ("unused", toJson nflag), ("rounds", toJson rounds), ("plantedFlagged", toJson got),
    ("plantedExpected", toJson expected.size),
    ("generated", toJson (generated.toList.map fun (k, n) => Json.mkObj [(k, toJson n)]))]
  out.putStrLn j.compress
  return ((thms.filter fun (c, _) => !isTest c).size, nh - nhTest, nflag)

/-! ## Part 2: statement mutants -/

/-- The connectives of one syntax: `∨`, `∧`, `⊃`, `≡`, `∼`, and the formal `⊃ₓ`, `≡ₓ`. -/
structure Grp where
  name : String
  orC : Name
  andC : Name
  impC : Name
  iffC : Name
  negC : Name
  fimpC : Option Name := none
  fiffC : Option Name := none

def groups : Array Grp := #[
  { name := "F", orC := ``PM.F.or, andC := ``PM.F.and, impC := ``PM.F.imp, iffC := ``PM.F.iff,
    negC := ``PM.F.neg },
  { name := "QF", orC := ``PM.QF.or, andC := ``PM.QF.and, impC := ``PM.QF.imp, iffC := ``PM.QF.iff,
    negC := ``PM.QF.neg, fimpC := some ``PM.QF.fimp, fiffC := some ``PM.QF.fiff },
  { name := "EF", orC := ``PM.F9.EF.or, andC := ``PM.F9.EF.and, impC := ``PM.F9.EF.imp,
    iffC := ``PM.F9.EF.iff, negC := ``PM.F9.EF.neg },
  { name := "PF", orC := ``PM.F9.PF.or, andC := ``PM.F9.PF.and, impC := ``PM.F9.PF.imp,
    iffC := ``PM.F9.PF.iff, negC := ``PM.F9.PF.neg },
  { name := "Reading", orC := ``PM.F9.Reading.or, andC := ``PM.F9.Reading.and,
    impC := ``PM.F9.Reading.imp, iffC := ``PM.F9.Reading.iff, negC := ``PM.F9.PF.neg },
  { name := "PE", orC := ``PM.F9.PE.or, andC := ``PM.F9.PE.and, impC := ``PM.F9.PE.imp,
    iffC := ``PM.F9.PE.iff, negC := ``PM.F9.PE.neg }]

/-- Nodes that bind a variable (their lambda arguments are formulas) or wrap a formula of another
    syntax. -/
def binderNodes : Array Name := #[``PM.QF.all, ``PM.QF.ex, ``PM.QF.fimp, ``PM.QF.fiff,
  ``PM.F9.PF.all, ``PM.F9.PF.ex, ``PM.F9.PE.all, ``PM.F9.PE.ex]
def wrapNodes : Array Name := #[``PM.F9.PF.el, ``PM.F9.PE.pf]

def arity (n : Name) : MetaM Nat := do
  let rec go : Expr → Nat
    | .forallE _ _ b _ => go b + 1
    | _ => 0
  return go (← getConstInfo n).type

inductive Node
  | conn (g : Grp) (k : Nat)   -- a connective of `g`; its last `k` arguments are formulas
  | binder
  | wrap
  | leaf

def classify (e : Expr) : MetaM Node := do
  let some c := e.getAppFn.constName? | return .leaf
  let n := e.getAppNumArgs
  for g in groups do
    for (d, k) in [(g.orC, 2), (g.andC, 2), (g.impC, 2), (g.iffC, 2), (g.negC, 1)] do
      if c == d && n == (← arity d) then
        -- `PF.neg` is shared by two groups; either serves
        return .conn g k
  if binderNodes.contains c then return .binder
  if wrapNodes.contains c && n == (← arity c) then return .wrap
  return .leaf

def negOfType (e : Expr) : MetaM (Option Name) := do
  let ty ← whnfR (← inferType e)
  match ty.getAppFn.constName? with
  | some ``PM.F => return some ``PM.F.neg
  | some ``PM.QF => return some ``PM.QF.neg
  | some ``PM.F9.EF => return some ``PM.F9.EF.neg
  | some ``PM.F9.PF => return some ``PM.F9.PF.neg
  | some ``PM.F9.PE => return some ``PM.F9.PE.neg
  | _ => return none

def withHead (e : Expr) (c : Name) : Expr :=
  mkAppN (.const c e.getAppFn.constLevels!) e.getAppArgs

/-- The mutants made by one operator at `e` itself. -/
def ownMutants (op : String) (e : Expr) : MetaM (Array Expr) := do
  let some c := e.getAppFn.constName? | do
    if op == "negate" then
      if let some n ← negOfType e then return #[← mkAppM n #[e]]
    return #[]
  match ← classify e with
  | .conn g _ =>
    match op with
    | "orAnd" =>
      if c == g.orC then return #[withHead e g.andC]
      if c == g.andC then return #[withHead e g.orC]
      return #[]
    | "dropAntecedent" => return if c == g.impC then #[e.appArg!] else #[]
    | "iffImp" => return if c == g.iffC then #[withHead e g.impC] else #[]
    | "negate" =>
      if let some n ← negOfType e then return #[← mkAppM n #[e]] else return #[]
    | _ => return #[]
  | _ =>
    match op with
    | "iffImp" =>
      for g in groups do
        if some c == g.fiffC then if let some f := g.fimpC then return #[withHead e f]
      return #[]
    | "negate" =>
      if let some n ← negOfType e then return #[← mkAppM n #[e]] else return #[]
    | _ => return #[]

/-- Every one-change mutant of `e` by the operator `op`. -/
partial def mutantsOf (op : String) (e : Expr) : MetaM (Array Expr) := do
  let mut out ← ownMutants op e
  let args := e.getAppArgs
  let n := args.size
  match ← classify e with
  | .conn _ k =>
    for j in [n - k:n] do
      for m in ← mutantsOf op args[j]! do
        out := out.push (mkAppN e.getAppFn (args.set! j m))
  | .binder =>
    for j in [:n] do
      if args[j]!.isLambda then
        let ms ← lambdaTelescope args[j]! fun ys b => do
          (← mutantsOf op b).mapM (mkLambdaFVars ys ·)
        for m in ms do out := out.push (mkAppN e.getAppFn (args.set! j m))
  | .wrap =>
    for m in ← mutantsOf op args[n-1]! do
      out := out.push (mkAppN e.getAppFn (args.set! (n-1) m))
  | .leaf => pure ()
  return out

/-- The propositional skeleton of a formula as a ✱1–✱5 formula `F`, each maximal subformula that is
    not built by a connective an atom `a0`, `a1`, … (equal subterms, equal atoms). -/
partial def skeleton (e : Expr) : StateT (Array Expr) MetaM Expr := do
  if let .conn g k ← classify e then
    let c := e.getAppFn.constName!
    let args := e.getAppArgs
    let n := args.size
    let fc := if c == g.orC then ``PM.F.or else if c == g.andC then ``PM.F.and
      else if c == g.impC then ``PM.F.imp else if c == g.iffC then ``PM.F.iff else ``PM.F.neg
    if k == 1 then return mkApp (.const fc []) (← skeleton args[n-1]!)
    return mkApp2 (.const fc []) (← skeleton args[n-2]!) (← skeleton args[n-1]!)
  let atoms ← get
  let i := match atoms.findIdx? (· == e) with
    | some i => i
    | none => atoms.size
  if i == atoms.size then set (atoms.push e)
  return mkApp (.const ``PM.F.var []) (mkStrLit s!"a{i}")

/-- A closed ✱1–✱5 formula as a value of `F`. -/
partial def toF (e : Expr) : Option PM.F :=
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``PM.F.var, #[.lit (.strVal s)] => some (.var s)
  | some ``PM.F.neg, #[a] => (toF a).map .neg
  | some ``PM.F.or, #[a, b] => return .or (← toF a) (← toF b)
  | some ``PM.F.and, #[a, b] => return PM.F.and (← toF a) (← toF b)
  | some ``PM.F.imp, #[a, b] => return PM.F.imp (← toF a) (← toF b)
  | some ``PM.F.iff, #[a, b] => return PM.F.iff (← toF a) (← toF b)
  | _, _ => none

/-- The repository's truth-table test `F.isTaut` on a closed formula: evaluated by the kernel (as by
    `decide` in PM/Statements.lean), or with `fast` run as compiled code (the same definition). -/
def taut (fast : Bool) (g : Expr) : MetaM (Option Bool) := do
  if fast then return (toF g).map PM.F.isTaut
  match Kernel.whnf (← getEnv) {} (mkApp (.const ``PM.F.isTaut []) g) with
  | .ok (.const ``Bool.true _) => return some true
  | .ok (.const ``Bool.false _) => return some false
  | _ => return none

/-- Lean source for a ✱1–✱5 formula over the statement's variables. -/
partial def renderF (e : Expr) : MetaM String := do
  if let .fvar f := e then return (← f.getDecl).userName.toString
  let some c := e.getAppFn.constName? | return "?"
  let args := e.getAppArgs
  let bin (s : String) : MetaM String := do
    return s!"({s} {← renderF args[0]!} {← renderF args[1]!})"
  if c == ``PM.F.or then bin "PM.F.or"
  else if c == ``PM.F.and then bin "PM.F.and"
  else if c == ``PM.F.imp then bin "PM.F.imp"
  else if c == ``PM.F.iff then bin "PM.F.iff"
  else if c == ``PM.F.neg then return s!"(PM.F.neg {← renderF args[0]!})"
  else return "?"

def ops : Array String := #["orAnd", "dropAntecedent", "iffImp", "negate"]

/-! ## Comparing a proof's type with a mutant

`direct` asks the kernel `Kernel.isDefEq env {} pty mty` of the two terms as they are. `normal`
first takes each term to its normal form by the kernel's own reductions and asks `Kernel.isDefEq`
of the two normal forms; `both` does the two and records both verdicts. -/

inductive Method | direct | normal | both
  deriving BEq, Inhabited

def Method.ofString : String → Method
  | "direct" => .direct | "both" => .both | _ => .normal

def Method.str : Method → String
  | .direct => "direct" | .normal => "normal" | .both => "both"

/-- What the normal forms contain that could make the kernel's comparison more than a comparison of
    trees: a proof (a subterm whose type is a proposition: proof irrelevance, and the K-like
    reduction of `Eq.rec`), an application of a constructor of a structure (structure eta), a term of
    a type with one constructor and no fields, or a function into one (unit eta). Checked on every
    subterm of every normal form; docs/STATEMENT_MUTATION.md. -/
structure Audit where
  proofs : NameSet := {}
  structCtors : NameSet := {}
  unitLike : NameSet := {}
  nodes : Nat := 0

def Audit.clean (a : Audit) : Bool := a.proofs.isEmpty && a.structCtors.isEmpty && a.unitLike.isEmpty

/-- What the audit flagged, sorted, as written (`projection PMNfTest.ProofBox.1`, not escaped). -/
def namesJson (s : NameSet) : Json := toJson ((s.toArray.map (·.toString (escape := false))).qsort (· < ·))

def Audit.merge (a b : Audit) : Audit :=
  { proofs := b.proofs.foldl (·.insert ·) a.proofs
    structCtors := b.structCtors.foldl (·.insert ·) a.structCtors
    unitLike := b.unitLike.foldl (·.insert ·) a.unitLike
    nodes := a.nodes + b.nodes }

structure NfState where
  /-- the bound on the steps of one normal form -/
  budget : Nat
  cache : Std.HashMap Expr Expr := {}
  canon : Std.HashMap Expr Expr := {}
  seen : Std.HashMap Expr Unit := {}
  steps : Nat := 0
  /-- the bound was reached, or the kernel failed: this term's comparison falls back to `direct` -/
  over : Bool := false
  /-- the subterms of the normal forms of the current statement -/
  audit : Audit := {}
  /-- the subterms of all normal forms of the run -/
  runAudit : Audit := {}

abbrev NfM := StateRefT NfState MetaM

/-- One copy of each normal subterm, so that equal parts of the normal forms are shared. -/
def canonical (e : Expr) : NfM Expr := do
  match (← get).canon[e]? with
  | some r => return r
  | none => modify fun s => { s with canon := s.canon.insert e e }; return e

/-- How a flagged subterm is reported: a constant or a variable by its name, an application by its
    head, a projection by its structure and field (counted from 1), anything else by its kind. -/
partial def nodeName (e : Expr) : MetaM Name := do
  match e with
  | .const c _ => return c
  | .fvar f =>
    let n := match (← getLCtx).find? f with | some d => d.userName | none => f.name
    return .str .anonymous s!"variable {n}"
  | .proj sn i _ => return .str .anonymous s!"projection {sn}.{i + 1}"
  | .app .. => nodeName e.getAppFn
  | .lam .. => return .str .anonymous "fun"
  | _ => return .str .anonymous e.ctorName

/-- The kernel's weak head normal form of `e` in the current context, or none if the kernel fails. -/
def kernelWhnf? (e : Expr) : MetaM (Option Expr) := do
  return (Kernel.whnf (← getEnv) (← getLCtx) e).toOption

/-- Is `ty`, or the result of `ty` under `∀`s, a structure with one constructor, no indices and no
    fields? Every reduction is `Kernel.whnf`. None if the kernel fails. -/
partial def unitLikeType? (ty : Expr) : MetaM (Option Bool) := do
  let some r ← kernelWhnf? ty | return none
  if let .forallE n t b bi := r then
    return ← withLocalDecl n bi t fun x => unitLikeType? (b.instantiate1 x)
  let env ← getEnv
  return some <| match r.getAppFn.constName? with
    | some i => match env.find? i with
      | some (.inductInfo v) => v.ctors.length == 1 && v.numIndices == 0 &&
          (match env.find? v.ctors[0]! with
           | some (.ctorInfo c) => c.numFields == 0
           | _ => false)
      | _ => false
    | none => false

/-- Record what a subterm of a normal form is (each distinct subterm once). Each test decides as the
    kernel would, whatever the reducibility attributes (the kernel ignores them):
    - a proof: the kernel's `is_prop` on its type, i.e. the type's type, reduced by `Kernel.whnf`, is
      a sort whose level is zero up to normalization;
    - unit-like: its type, or the result of its type under `∀`s (a function, which the kernel's eta
      for functions compares at an argument), reduced by `Kernel.whnf`, is a structure with one
      constructor, no indices and no fields (the kernel's eta for unit-like types, which reduces the
      type by its `whnf`);
    - an application of a constructor of a structure (one constructor, no indices, not recursive:
      the kernel's eta for structures). This reads only the head and the environment: the head of a
      normal form is already the kernel's whnf, so a constructor behind a definition has been unfolded.
    The types are inferred by `inferType` at transparency `all`, which unfolds what the kernel unfolds:
    inference only has to produce some type of the subterm (any two are definitionally equal), and
    the decisions above are taken on the kernel's own reduction of it. If inference or the kernel
    fails, the comparison falls back to `direct`. A sort or a `∀` is a type: its type is a sort, so it
    is neither a proof nor unit-like, and it is not an application. After the bound is reached the
    comparison falls back anyway. -/
def auditNode (e : Expr) : NfM Unit := do
  if e.isSort || e.isForall then return
  let s ← get
  if s.over || s.seen.contains e then return
  set { s with seen := s.seen.insert e () }
  let env ← getEnv
  let types ← try
      withTransparency .all do
        let ty ← inferType e
        pure (some (ty, ← inferType ty))
    catch _ => pure none
  let some (ty, tyTy) := types | modify fun s => { s with over := true }
  let some tyTy ← kernelWhnf? tyTy | modify fun s => { s with over := true }
  let isPf := match tyTy with
    | .sort u => u.normalize.isZero
    | _ => false
  let some unit ← unitLikeType? ty | modify fun s => { s with over := true }
  let ctorOfStruct := match e.getAppFn with
    | .const c _ => match env.find? c with
      | some (.ctorInfo v) => match env.find? v.induct with
        | some (.inductInfo i) => i.ctors.length == 1 && i.numIndices == 0 && !i.isRec
        | _ => false
      | _ => false
    | _ => false
  let nm ← nodeName e
  modify fun s => { s with audit := { s.audit with
    nodes := s.audit.nodes + 1
    proofs := if isPf then s.audit.proofs.insert nm else s.audit.proofs
    unitLike := if unit then s.audit.unitLike.insert nm else s.audit.unitLike
    structCtors := if ctorOfStruct then s.audit.structCtors.insert nm else s.audit.structCtors } }

/-- The normal form of `e` by the kernel's reductions: `Kernel.whnf` at the root, then the same in
    every argument, under every binder and in every binder type. Memoized on the term, so a subterm
    met again (a definition's parameter used twice) is normalized once and its result shared. Each
    call that is not a cache hit is a step; past `budget` steps, or if the kernel reports an error,
    `over` is set and the comparison of this term falls back to `direct`.

    Every subterm of the result is audited (`auditNode`), by the constructor of `Expr` it has after
    `Kernel.whnf`:
    - `app` `h a₁ … aₙ`: the application, its head and each partial application `h a₁ … aₖ`
      (0 < k < n), i.e. every `app` node of the spine. The head is a constructor, a variable, a
      constant without a definition (an inductive type, an axiom, a stuck recursor) or a stuck
      projection, whose structure argument is normalized (and audited) in turn; each argument is
      normalized.
    - `lam`: the function; its binder type and its body (under a fresh variable) are normalized.
    - `forallE`: a type, not audited itself; its binder type and body are normalized.
    - `proj`: a stuck projection, audited; its structure argument is normalized.
    - `const`, `fvar`, `lit`: audited. `sort`: a type, not audited.
    - `mdata`, `letE`: `Kernel.whnf` removes metadata and reduces a `let` at the root, so neither is
      met; `bvar`, `mvar`: a closed term under fresh variables has neither. If one were met, the
      comparison would fall back to `direct`. -/
partial def nf (e : Expr) : NfM Expr := do
  let s ← get
  if s.over then return e
  if let some r := s.cache[e]? then return r
  if s.steps ≥ s.budget then
    set { s with over := true }
    return e
  set { s with steps := s.steps + 1 }
  let w ← match Kernel.whnf (← getEnv) (← getLCtx) e with
    | .ok w => pure w
    | .error _ =>
      modify fun s => { s with over := true }
      return e
  let r ← match w with
    | .app .. =>
      -- only a projection's structure argument can reduce further in the head
      let h' ← match w.getAppFn with
        | .proj sn i b => pure (.proj sn i (← nf b))
        | h => pure h
      auditNode h'
      let args ← w.getAppArgs.mapM nf
      -- the partial applications `h' a₁ … aₖ` (k < n) are subterms too
      for k in [1:args.size] do auditNode (mkAppN h' args[:k])
      pure (mkAppN h' args)
    | .lam n t b bi =>
      let t' ← nf t
      withLocalDecl n bi t fun x => do
        let b' ← nf (b.instantiate1 x)
        pure (.lam n t' (b'.abstract #[x]) bi)
    | .forallE n t b bi =>
      let t' ← nf t
      withLocalDecl n bi t fun x => do
        let b' ← nf (b.instantiate1 x)
        pure (.forallE n t' (b'.abstract #[x]) bi)
    | .proj sn i b => pure (.proj sn i (← nf b))
    | .const .. | .fvar .. | .lit .. | .sort .. => pure w
    | .mdata .. | .letE .. | .bvar .. | .mvar .. =>
      modify fun s => { s with over := true }
      pure w
  let r ← canonical r
  auditNode r
  -- after the bound is reached the results are not normal forms: nothing more is cached
  unless (← get).over do modify fun s => { s with cache := s.cache.insert e r }
  return r

/-- The verdict on two normal forms, or none when it is not to be relied on: the mutant's normal form
    was not reached, the kernel reports an error, or the audit of the statement's normal forms is not
    clean. Then `direct` decides. -/
def verdictOnNormalForms (env : Environment) (clean : Bool) (np : Expr) (nm : Option Expr) : Option Bool :=
  if !clean then none else
    nm.bind fun nm => match Kernel.isDefEq env {} np nm with | .ok b => some b | .error _ => none

/-- The normal form of a closed term, or none if the bound is reached or the kernel fails; and the
    steps it took. The cache is kept across calls (the proof's type and all mutants of one statement),
    the count of steps is per term. -/
def nfTop (e : Expr) : NfM (Option Expr × Nat) := do
  modify fun s => { s with steps := 0, over := false }
  let r ← nf e
  let s ← get
  return (if s.over then none else some r, s.steps)

/-- Start a statement: a fresh cache and audit (the run's audit keeps what the last one found). -/
def NfState.next (s : NfState) : NfState :=
  { s with cache := {}, canon := {}, seen := {}, audit := {}, runAudit := s.runAudit.merge s.audit }

/-- The default bound on the steps of one normal form (`PM_MUTATION_NF_BUDGET` sets another). The
    largest normal form of the full run takes a few hundred steps (MEASURED,
    docs/STATEMENT_MUTATION.md): the bound only stops a pathological term. -/
def nfBudgetDefault : Nat := 200000

/-- A witness `l`, `r` (two statements equal for the direct comparison by proof irrelevance, whose
    normal forms are not), compared as `analyse` compares a statement with a mutant: one state for
    both normal forms. The audit must flag the proof `pf`, and the verdict of the comparison as
    `normal` makes it (the audit routes it to `direct`) must be `direct`'s; the run fails otherwise.
    The record also gives the verdict on the normal forms with the audit bypassed. -/
def witnessCheck (l r pf : Name) : MetaM Json := do
  let env ← getEnv
  let l := (← getConstInfo l).value!
  let r := (← getConstInfo r).value!
  let ((nl, _), sw) ← (nfTop l).run { budget := 1000 }
  let ((nr, _), sw) ← (nfTop r).run sw
  let some nl := nl | throwError "the witness's normal form is not reached"
  let direct := match Kernel.isDefEq env {} l r with | .ok b => b | .error _ => false
  let bypassed := verdictOnNormalForms env true nl nr
  let routed := verdictOnNormalForms env sw.audit.clean nl nr
  let verdict := routed.getD direct
  unless sw.audit.proofs.contains pf && verdict == direct do
    throwError "the audit of normal forms misses the planted proof {pf}: proofs \
      {sw.audit.proofs.toList}; verdict {verdict}, direct {direct}"
  return Json.mkObj [("direct", toJson direct), ("normalAuditBypassed", toJson bypassed),
    ("auditClean", toJson sw.audit.clean), ("proofs", namesJson sw.audit.proofs),
    ("verdict", toJson verdict)]

/-- The audit must flag the projection `up` in the normal form of the definition `c` as unit-like. -/
def unitProjectionCheck (c up : Name) : MetaM Json := do
  let ((_, _), su) ← (nfTop (← getConstInfo c).value!).run { budget := 1000 }
  unless su.audit.unitLike.contains up do
    throwError "the audit of normal forms misses the planted unit-like projection {up}: unit-like \
      {su.audit.unitLike.toList}"
  return namesJson su.audit.unitLike

/-- The planted cases of the comparison, which the run fails without, and its record (`selfTest`):
    - the audit must flag a proof (`rfl`, which normalizes to `Eq.refl`), a constructor of a
      structure (`Subtype.mk`) and a term of a unit-like type (`PUnit.unit`);
    - the witness `PMNfTest.witnessLeft`/`witnessRight` (`witnessCheck`): the projection `b.proof`
      must be flagged as a proof and the comparison must take `direct`'s verdict;
    - the same for `PMNfTest.hiddenLeft`/`hiddenRight`, whose proof is the variable `h` of a type
      that is a proposition only behind an irreducible definition;
    - the audit must flag the projections `b.unit` of `PMNfTest.unitProjection` and of
      `PMNfTest.hiddenUnitProjection` (a type that is `PUnit` behind an irreducible definition) as
      unit-like;
    - a bound of three steps must stop a normal form that needs more.
    tests/test_statement_mutation.py pins the record. -/
def nfSelfTest : MetaM Json := do
  let nat := Expr.const ``Nat []
  let planted := mkApp4 (.const ``Prod.mk [Level.zero, Level.zero]) (.const ``PUnit [Level.one]) nat
    (.const ``PUnit.unit [Level.one]) (mkNatLit 1)
  let sub := mkApp4 (.const ``Subtype.mk [Level.one]) nat
    (.lam `n nat (mkApp3 (.const ``Eq [Level.one]) nat (.bvar 0) (mkNatLit 1)) .default)
    (mkNatLit 1) (mkApp2 (.const ``rfl [Level.one]) nat (mkNatLit 1))
  let ((r1, _), s) ← (do let a ← nfTop planted; let _ ← nfTop sub; pure a).run { budget := 1000 }
  unless r1.isSome && s.audit.proofs.contains ``Eq.refl && s.audit.structCtors.contains ``Subtype.mk &&
      s.audit.unitLike.contains ``PUnit.unit do
    throwError "the audit of normal forms misses a planted case: proofs {s.audit.proofs.toList}, \
      structure constructors {s.audit.structCtors.toList}, unit-like {s.audit.unitLike.toList}"
  let ((r2, n), _) ← (nfTop sub).run { budget := 3 }
  unless r2.isNone && n == 3 do throwError "the bound on normal forms does not stop a planted term"
  return Json.mkObj [("part", jstr "selfTest"),
    ("witness", ← witnessCheck ``PMNfTest.witnessLeft ``PMNfTest.witnessRight
      (.str .anonymous s!"projection {``PMNfTest.ProofBox}.1")),
    ("hiddenProofWitness", ← witnessCheck ``PMNfTest.hiddenLeft ``PMNfTest.hiddenRight
      (.str .anonymous "variable h")),
    ("unitProjection", ← unitProjectionCheck ``PMNfTest.unitProjection
      (.str .anonymous s!"projection {``PMNfTest.UnitBox}.1")),
    ("hiddenUnitProjection", ← unitProjectionCheck ``PMNfTest.hiddenUnitProjection
      (.str .anonymous s!"projection {``PMNfTest.HiddenUnitBox}.1"))]

/-- Replace the `k`-th occurrence of the variable `x` by `y` (the state counts occurrences; binder
    types are left alone). -/
partial def replOcc (x y : FVarId) (k : Nat) : Expr → StateM Nat Expr
  | .fvar z => do
    if z != x then return .fvar z
    let n ← get
    set (n + 1)
    return if n == k then .fvar y else .fvar z
  | .app f a => return .app (← replOcc x y k f) (← replOcc x y k a)
  | .lam n t b bi => return .lam n t (← replOcc x y k b) bi
  | .forallE n t b bi => return .forallE n t (← replOcc x y k b) bi
  | .letE n t v b nd => return .letE n t (← replOcc x y k v) (← replOcc x y k b) nd
  | .mdata m b => return .mdata m (← replOcc x y k b)
  | .proj s i b => return .proj s i (← replOcc x y k b)
  | e => return e

/-- Analyse one statement: `stmtTy` is the statement to mutate (for ✱1–✱5 `∀ p …, Thm (s… p …)`),
    `proof` the original proof term. Writes one record per mutant and returns
    (mutants, survivors). -/
def analyse (out : IO.FS.Handle) (label : Name) (pmNum : String) (stmtTy proof : Expr)
    (isF fast : Bool) (meth : Method) (nfs : IO.Ref NfState) : MetaM (Nat × Nat) := do
  let env ← getEnv
  let tc0 ← IO.monoMsNow
  let pty ← match Kernel.check env {} proof with
    | .ok t => pure t
    | .error _ => throwError "kernel rejects the proof of {label}"
  let directOf (mty : Expr) : Bool :=
    match Kernel.isDefEq env {} pty mty with | .ok b => b | .error _ => false
  -- the state of `nf`: its cache and audit are per statement
  nfs.modify NfState.next
  let runNf (e : Expr) : MetaM (Option Expr × Nat) := do
    let (r, s) ← (nfTop e).run (← nfs.get)
    nfs.set s
    return r
  -- the normal form of the proof's type, shared by all comparisons of this statement
  let tn0 ← IO.monoMsNow
  let (npty, nfPty) ← if meth == .direct then pure (none, 0) else runNf pty
  let tn1 ← IO.monoMsNow
  /- the verdict on the normal forms, the steps of the mutant's normal form and the time; none when
     either normal form was not reached, the kernel reports an error, or the audit of this
     statement's normal forms is not clean (then `direct` decides) -/
  let normalOf (mty : Expr) : MetaM (Option Bool × Nat × Nat) := do
    let some np := npty | return (none, 0, 0)
    -- once the audit has flagged something in this statement, `direct` decides all its comparisons
    unless (← nfs.get).audit.clean do return (none, 0, 0)
    let a ← IO.monoMsNow
    let (r, n) ← runNf mty
    let v := verdictOnNormalForms env (← nfs.get).audit.clean np r
    return (v, n, (← IO.monoMsNow) - a)
  forallTelescope stmtTy fun xs concl => do
    let f0 := concl.appArg!
    -- a ✱1–✱5 statement is `Thm (s… p …)`: mutate the formula `s…` stands for
    let f ← if isF then
        match ← unfoldDefinition? f0 with
        | some u => pure u.headBeta
        | none => pure f0
      else pure f0
    /- one comparison: the verdict, the direct and the normal-form verdicts where computed, whether
       it fell back, the steps of the mutant's normal form, the milliseconds of each method -/
    let compare (mty : Expr) : MetaM (Bool × Option Bool × Option Bool × Bool × Nat × Nat × Nat) := do
      let (v, n, nMs) ← if meth == .direct then pure (none, 0, 0) else normalOf mty
      let fb := meth != .direct && v.isNone
      -- `direct` runs for its own sake (`direct`, `both`) or as the fallback
      let a ← IO.monoMsNow
      let d := if meth == .normal && !fb then none else some (directOf mty)
      let b ← IO.monoMsNow
      let verdict := match meth, d, v with
        | .normal, _, some x => x
        | _, some x, _ => x
        | _, none, some x => x
        | _, none, none => false
      return (verdict, d, v, fb, n, b - a, nMs)
    -- control: the unchanged formula, rebuilt the way every mutant is, is accepted
    let (control, controlDirect, controlNormal, controlFb, _, _, _) ←
      compare (← mkForallFVars xs (mkApp concl.appFn! f))
    let mut muts : Array (String × Nat × Expr) := #[]
    for op in ops do
      let ms ← mutantsOf op f
      for i in [:ms.size] do muts := muts.push (op, i, ms[i]!)
    -- two explicit variables of the same type that both occur in the formula: exchanged everywhere
    -- (a renaming, so an equivalent statement), and one occurrence of either replaced by the other
    let mut k := 0
    for i in [:xs.size] do
      for j in [i+1:xs.size] do
        let di ← xs[i]!.fvarId!.getDecl
        let dj ← xs[j]!.fvarId!.getDecl
        if di.binderInfo.isExplicit && dj.binderInfo.isExplicit && (← isDefEq di.type dj.type) &&
            f.containsFVar di.fvarId && f.containsFVar dj.fvarId then
          let m := f.replaceFVars #[xs[i]!, xs[j]!] #[xs[j]!, xs[i]!]
          if m != f then
            muts := muts.push ("swap " ++ di.userName.toString ++ " " ++ dj.userName.toString, k, m)
            k := k + 1
          for (a, b) in [(di, dj), (dj, di)] do
            let (_, n) := (replOcc a.fvarId b.fvarId (1 <<< 30) f).run 0
            for occ in [:n] do
              let (m, _) := (replOcc a.fvarId b.fvarId occ f).run 0
              muts := muts.push (s!"substOcc {a.userName} {b.userName}", occ, m)
    let ground (e : Expr) : MetaM Expr := do
      let vs ← xs.mapM fun x => do
        return mkApp (.const ``PM.F.var []) (mkStrLit (← x.fvarId!.getDecl).userName.toString)
      return e.replaceFVars xs vs
    let mut nsurv := 0
    let tc1 ← IO.monoMsNow
    let mut dMs := 0
    let mut nMs := 0
    let mut tMs := 0
    let mut nfMax := nfPty
    let mut fallbacks := if controlFb then 1 else 0
    let mut disagree := if controlDirect.isSome && controlNormal.isSome && controlDirect != controlNormal
      then 1 else 0
    for (op, i, m) in muts do
      let mty ← mkForallFVars xs (mkApp concl.appFn! m)
      let (surv, sd, sn, fb, steps, ms1, ms2) ← compare mty
      let b ← IO.monoMsNow
      if surv then nsurv := nsurv + 1
      if fb then fallbacks := fallbacks + 1
      if sd.isSome && sn.isSome && sd != sn then disagree := disagree + 1
      nfMax := max nfMax steps
      let (skel, _) ← (skeleton m).run #[]
      let taut ← if isF then taut fast (← ground m)
        else if skel.hasFVar then pure none else taut fast skel
      let c ← IO.monoMsNow
      dMs := dMs + ms1; nMs := nMs + ms2; tMs := tMs + (c - b)
      let src ← if isF then renderF m else pure ""
      let pp ← if fast && !surv then pure "" else do pure (toString (← ppExpr m)).trimAscii.toString
      let both := if meth == .both then
          [("survivesDirect", toJson sd), ("survivesNormal", toJson sn)] else []
      let j := Json.mkObj ([("part", jstr "mut"), ("decl", jstr label.toString),
        ("pm", jstr pmNum), ("op", jstr op), ("i", toJson i), ("survives", toJson surv)] ++ both ++
        [("fallback", toJson fb), ("taut", toJson taut), ("src", jstr src),
        ("mutant", jstr pp)])
      out.putStrLn j.compress
    let srcOrig ← if isF then renderF f else pure ""
    let (skel0, _) ← (skeleton f).run #[]
    let t0 ← if isF then taut fast (← ground f) else if skel0.hasFVar then pure none else taut fast skel0
    let vars ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName.toString
    let j := Json.mkObj ([("part", jstr "stmt"), ("decl", jstr label.toString), ("pm", jstr pmNum)] ++
      (← whereOf label) ++ [("vars", toJson vars), ("stmtDef", jstr (f0.getAppFn.constName?.getD .anonymous).toString),
      ("control", toJson control), ("mutants", toJson muts.size), ("survivors", toJson nsurv),
      ("taut", toJson t0), ("src", jstr srcOrig), ("isF", toJson isF),
      ("checkMs", toJson (tc1 - tc0)), ("defeqMs", toJson dMs), ("tautMs", toJson tMs),
      ("method", jstr meth.str), ("normalMs", toJson (nMs + (tn1 - tn0))), ("normalStepsMax", toJson nfMax),
      ("fallbacks", toJson fallbacks), ("disagreements", toJson disagree)] ++
      (if meth == .both then [("controlDirect", toJson controlDirect), ("controlNormal", toJson controlNormal)]
       else []))
    out.putStrLn j.compress
    return (muts.size, nsurv)

/-- ✱1–✱5 targets: (label, PM number, statement, proof term). -/
def targetsF (only : Option (Array Name) := none) : MetaM (Array (Name × String × Expr × Expr)) := do
  let env ← getEnv
  let mut out := #[]
  -- the primitive propositions ✱1·2–✱1·6, against Thm's constructors
  for (s, c) in [(``PM.s1_2, ``PM.Thm.taut), (``PM.s1_3, ``PM.Thm.add), (``PM.s1_4, ``PM.Thm.perm),
      (``PM.s1_5, ``PM.Thm.assoc), (``PM.s1_6, ``PM.Thm.sum)] do
    let sty ← forallTelescope (← getConstInfo s).type fun xs _ => do
      mkForallFVars xs (mkApp (.const ``PM.Thm []) (mkAppN (.const s []) xs))
    if only.all (·.contains c) then out := out.push (c, (s.toString.drop 4).toString, sty, Expr.const c [])
  -- the whole environment is scanned unless the names are given
  let names := only.getD <| (env.constants.fold (init := #[]) fun acc c ci =>
    match ci with
    | .thmInfo _ => if modOf env c == `PM.Replay || modOf env c == `PM.Replay2 ||
        modOf env c == `PM.Derived then acc.push c else acc
    | _ => acc).qsort Name.lt
  for c in names do
    let ci ← getConstInfo c
    let isStmt ← forallTelescope ci.type fun _ concl => do
      if concl.getAppFn.constName? != some ``PM.Thm then return none
      match concl.appArg!.getAppFn.constName? with
      | some (.str (.str .anonymous "PM") s) =>
        if s.startsWith "s" && (s.drop 1).all (fun ch => ch.isDigit || ch == '_') then return some s
        else return none
      | _ => return none
    if let some s := isStmt then
      out := out.push (c, (s.drop 1).toString, ci.type, Expr.const c [])
  return out

/-- Targets from ✱9 on: the numbered propositions `q…`, `QL.t…`, `F9.f…`. -/
def targetsQ : MetaM (Array (Name × String × Expr × Expr)) := do
  let env ← getEnv
  let isNum (s : String) (p : String) : Bool :=
    let r := (s.drop p.length).toString
    s.startsWith p && r.front.isDigit && r.all (fun ch => ch.isDigit || ch == '_')
  let names := (env.constants.fold (init := #[]) fun acc c ci =>
    match ci with
    | .thmInfo _ =>
      if !inRepo (modOf env c) then acc else
      match c with
      | .str (.str .anonymous "PM") s => if isNum s "q" then acc.push c else acc
      | .str (.str (.str .anonymous "PM") "QL") s => if isNum s "t" then acc.push c else acc
      | .str (.str (.str .anonymous "PM") "F9") s => if isNum s "f" then acc.push c else acc
      | _ => acc
    | _ => acc).qsort Name.lt
  let mut out := #[]
  for c in names do
    let ci ← getConstInfo c
    let ok ← forallTelescope ci.type fun _ concl => do
      return concl.getAppFn.constName? == some ``PM.QThm || concl.getAppFn.constName? == some ``PM.F9.Thm9
    if ok then
      out := out.push (c, "", ci.type, Expr.const c (ci.levelParams.map Level.param))
  return out

/-- The fixed sample of ✱1–✱5 for `--quick`: ✱1·4 (whose mutants include the ebook's slip), ✱1·6, and
    from each of ✱2–✱5 explicit terms and natural-deduction scripts of both replay files. -/
def quickSample : Array Name := #[``PM.Thm.perm, ``PM.Thm.sum, ``PM.t2_06, ``PM.t2_15, ``PM.t2_32, ``PM.t2_74,
  ``PM.t3_43, ``PM.t3_47, ``PM.t4_22, ``PM.t4_7, ``PM.t4_87, ``PM.t5_32, ``PM.t5_75]

end PMMutation

set_option maxHeartbeats 0 in
open PMMutation in
#eval show CommandElabM Unit from do
  let mode := (← IO.getEnv "PM_MUTATION_MODE").getD "quick"
  let path := (← IO.getEnv "PM_MUTATION_OUT").getD ".lake/mutation/out.jsonl"
  if let some d := (System.FilePath.mk path).parent then IO.FS.createDirAll d
  let h ← IO.FS.Handle.mk path .write
  -- the comparison (`normal`, `direct` or `both`), and optionally only some modules or declarations,
  -- or all but some declarations
  let meth := Method.ofString ((← IO.getEnv "PM_MUTATION_METHOD").getD "normal")
  let listOf (v : Option String) : Option (Array Name) :=
    v.bind fun s => if s.isEmpty then none else
      some ((s.splitOn ",").toArray.map fun x => x.trimAscii.toString.toName)
  let modules := listOf (← IO.getEnv "PM_MUTATION_MODULES")
  let only := listOf (← IO.getEnv "PM_MUTATION_ONLY")
  let skip := (listOf (← IO.getEnv "PM_MUTATION_SKIP")).getD #[]
  let budget := ((← IO.getEnv "PM_MUTATION_NF_BUDGET").bind String.toNat?).getD nfBudgetDefault
  let t0 ← IO.monoMsNow
  liftTermElabM do
    let env ← getEnv
    let keep (c : Name) : Bool :=
      modules.all (·.contains (modOf env c)) && only.all (·.contains c) && !skip.contains c
    h.putStrLn (← nfSelfTest).compress
    let nfs ← IO.mkRef ({ budget } : NfState)
    if mode == "full" || mode == "quick" || mode == "hyp" then
      let (nt, nh, nu) ← part1 h
      logInfo m!"hypotheses: {nt} theorems, {nh} hypotheses, {nu} unused"
    let t1 ← IO.monoMsNow
    let tf := (← targetsF (if mode == "quick" then some quickSample else none)).filter (keep ·.1)
    let mut nm := 0
    let mut ns := 0
    if mode != "hyp" then
      for (c, pm, ty, pf) in tf do
        let (a, b) ← analyse h c pm ty pf true (mode == "quick") meth nfs
        nm := nm + a; ns := ns + b
      logInfo m!"✱1–✱5: {tf.size} statements, {nm} mutants, {ns} survivors"
    let t2 ← IO.monoMsNow
    if mode == "full" || mode == "part2" then
      let tq := (← targetsQ).filter (keep ·.1)
      let mut qm := 0
      let mut qs := 0
      for (c, pm, ty, pf) in tq do
        let (a, b) ← analyse h c pm ty pf false false meth nfs
        qm := qm + a; qs := qs + b
      logInfo m!"from ✱9 on: {tq.size} statements, {qm} mutants, {qs} survivors"
    let t3 ← IO.monoMsNow
    let au := (← nfs.get).next.runAudit
    let j := Json.mkObj [("part", jstr "timing"), ("hypMs", toJson (t1 - t0)),
      ("fMs", toJson (t2 - t1)), ("qMs", toJson (t3 - t2)),
      ("method", jstr meth.str), ("nfBudget", toJson budget), ("auditNodes", toJson au.nodes),
      ("auditProofs", namesJson au.proofs), ("auditStructCtors", namesJson au.structCtors),
      ("auditUnitLike", namesJson au.unitLike)]
    h.putStrLn j.compress
  h.flush
