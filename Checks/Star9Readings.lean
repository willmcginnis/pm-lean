-- ✱9 under its four readings (docs/REPAIRS.md): A, the definitions as printed; C, the definitions as
-- printed with Russell's ✱8·13 carried over to ✱9, the working reading; L, ✱9+ (the definitions as
-- printed with ✱9·yy, ✱9·zz and Landini's rule Switch), a published variant; B, the alternative
-- convention, a cross-check. Run from the repository root with
-- `lake env lean Checks/Star9Readings.lean`; scripts/star9_readings.py turns the output into
-- docs/STAR9_READINGS.md, and tests/test_star9_readings.py pins the numbers.
--
-- The readings a theorem holds under are read from its statement: a statement for every reading `R`
-- (a binder of type `PM.F9.Reading`) holds under A, C, L and B, except that a hypothesis
-- `R.defs ≠ .plus` excludes L and a hypothesis `R.rule ≠ .exch` excludes C; otherwise under the
-- readings it names (`Reading.printed` A, `Reading.russell` C, `Reading.withSwitch` L,
-- `Reading.convention` B; written out, `⟨.printed, r⟩` is A for r `.basic`, C for r `.exch`, both for a
-- variable r; `⟨.plus, r⟩` L and `⟨.convention, r⟩` B for r `.basic` or a variable; `⟨d, .exch⟩` C for a
-- variable d; with r `.prenex` none of them). Each line printed is one JSON object.
--
-- Where the exchange rule is used: ✱8·13 (`PM.F9.Thm9.exch`) in C, Switch (`PM.F9.Thm9.switch`) in L.
-- For a declaration, `direct` is the number of occurrences of the reading's rule in its proof term,
-- and `closure` the number of its occurrences in the proof terms of the declaration and of every
-- declaration under `PM` that it uses, directly or through others, each counted once (a lemma used
-- twice, or a lemma defined by recursion, counts the occurrences in its proof term once). A lemma whose
-- statement names readings but not this one is not followed: a lemma stated for every reading reaches
-- it only in another reading's branch. So `closure` counts what the reading's proof can use; it is an
-- upper bound, since a lemma for every reading followed in one branch may be used only in another.
-- Each occurrence of ✱8·13 is listed by the kinds of the two quantifiers it exchanges (`kinds`: "AE"
-- for (x)(∃y), "EE", "EA", "AA"). For a combination of p. 142 the search is run again on the
-- reading's proposition; `steps` is the number of steps of the rule in the proof it finds: each use
-- of a lemma counts that lemma's `closure`.
import Lean
import PM
open Lean Elab Command Meta

namespace Star9Readings

def all4 : Array String := #["A", "C", "L", "B"]

/-- The subterms `Reading.mk d r` of an expression. -/
partial def mks (e : Expr) : Array Expr :=
  let here := if e.isAppOfArity ``PM.F9.Reading.mk 2 then #[e] else #[]
  match e with
  | .app f a => here ++ mks f ++ mks a
  | .lam _ t b _ | .forallE _ t b _ => mks t ++ mks b
  | .letE _ t v b _ => mks t ++ mks v ++ mks b
  | .mdata _ b | .proj _ _ b => mks b
  | _ => here

/-- The readings named in an expression (A, C, L, B). -/
partial def named (e : Expr) : Array String := Id.run do
  let mut out : Array String := #[]
  let add (out : Array String) (r : String) := if out.contains r then out else out.push r
  for c in e.getUsedConstants do
    if c == ``PM.F9.Reading.printed then out := add out "A"
    if c == ``PM.F9.Reading.russell then out := add out "C"
    if c == ``PM.F9.Reading.withSwitch then out := add out "L"
    if c == ``PM.F9.Reading.convention then out := add out "B"
  -- `Reading.mk d r` written out; with the prenex Switch (`r` = `.prenex`) it is none of A, C, L, B
  for m in mks e do
    let args := m.getAppArgs
    let d := args[0]!
    let r := args[1]!
    let basic := r.isConstOf ``PM.F9.Rule.basic
    let exch := r.isConstOf ``PM.F9.Rule.exch
    let var := !(basic || exch || r.isConstOf ``PM.F9.Rule.prenex)
    if d.isConstOf ``PM.F9.Defs.printed then
      if basic || var then out := add out "A"
      if exch || var then out := add out "C"
    else if d.isConstOf ``PM.F9.Defs.plus then
      if basic || var then out := add out "L"
    else if d.isConstOf ``PM.F9.Defs.convention then
      if basic || var then out := add out "B"
    else if exch then out := add out "C"
  return out

/-- The readings under which the theorem `n` holds, read from its statement; empty if there is none. -/
def readingsOf (n : Name) : MetaM (Array String) := do
  let some ci := (← getEnv).find? n | return #[]
  forallTelescope ci.type fun xs body => do
    for x in xs do
      if (← inferType x).isConstOf ``PM.F9.Reading then
        let mut rs := all4
        -- a hypothesis `R.defs ≠ .plus` excludes L, `R.rule ≠ .exch` excludes C
        for y in xs do
          let t ← inferType y
          if t.isAppOf ``Ne && t.getAppArgs.any (·.isConstOf ``PM.F9.Defs.plus) then
            rs := rs.filter (· != "L")
          if t.isAppOf ``Ne && t.getAppArgs.any (·.isConstOf ``PM.F9.Rule.exch) then
            rs := rs.filter (· != "C")
        return rs
    let r := named body
    return all4.filter r.contains

def jstr (a : Array String) : String := "[" ++ ", ".intercalate (a.toList.map (s!"\"{·}\"")) ++ "]"

/-! ## Where the exchange rule is used -/

/-- The rule of a reading: ✱8·13 in C, Switch in L. -/
def ruleOf (r : String) : Name := if r == "C" then ``PM.F9.Thm9.exch else ``PM.F9.Thm9.switch

def kindStr (e : Expr) : String :=
  if e.isConstOf ``Bool.true then "A" else if e.isConstOf ``Bool.false then "E" else "?"

/-- The occurrences of the rule `rule` in an expression, each by the kinds of the two quantifiers it
    exchanges. -/
partial def occ (rule : Name) (e : Expr) : Array String :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let here : Array String :=
      if f.isConstOf rule then
        if rule == ``PM.F9.Thm9.switch then #["AE"]
        else if args.size ≥ 6 then #[kindStr args[4]! ++ kindStr args[5]!] else #["??"]
      else #[]
    let inF := if f.isConst then #[] else occ rule f
    args.foldl (fun acc a => acc ++ occ rule a) (here ++ inF)
  | .const n _ => if n == rule then #["??"] else #[]
  | .lam _ t b _ | .forallE _ t b _ => occ rule t ++ occ rule b
  | .letE _ t v b _ => occ rule t ++ occ rule v ++ occ rule b
  | .mdata _ b | .proj _ _ b => occ rule b
  | _ => #[]

def valueOf (env : Environment) (n : Name) : Option Expr :=
  (env.find? n).bind (·.value? (allowOpaque := true))

/-- Whether a declaration's statement names readings, and not `r`. -/
def otherOnly (r : String) (n : Name) : MetaM Bool := do
  let rs ← readingsOf n
  return !rs.isEmpty && !rs.contains r

/-- The declarations under `PM` that the reading `r`'s use of `n` reaches, `n` included. -/
partial def closureOf (r : String) (n : Name) (seen : Std.HashSet Name := {}) :
    MetaM (Std.HashSet Name) := do
  if seen.contains n then return seen
  let mut s := seen.insert n
  if let some v := valueOf (← getEnv) n then
    for d in v.getUsedConstants do
      if (`PM).isPrefixOf d && !(← otherOnly r d) then s ← closureOf r d s
  return s

def directOf (env : Environment) (r : String) (n : Name) : Array String :=
  ((valueOf env n).map (occ (ruleOf r))).getD #[]

/-- `closure` of a declaration for the reading `r` (its occurrences, by kinds), and the declarations in
    its closure whose own proof terms use the rule. -/
def closureOcc (r : String) (n : Name) : MetaM (Array String × Array Name) := do
  let env ← getEnv
  let mut total : Array String := #[]
  let mut via : Array Name := #[]
  for d in (← closureOf r n).toArray.qsort (·.toString < ·.toString) do
    let k := directOf env r d
    if k.size > 0 then
      total := total ++ k
      via := via.push d
  return (total, via)

/-- Steps of the rule in a proof term: its own occurrences, and for each use of a declaration under
    `PM` that declaration's `closure`. -/
partial def stepsIn (r : String) (e : Expr) : MetaM (Array String) := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let mut acc : Array String := #[]
    if f.isConstOf (ruleOf r) then acc := occ (ruleOf r) (mkAppN f args) |>.extract 0 1
    else acc := acc ++ (← stepsIn r f)
    for a in args do acc := acc ++ (← stepsIn r a)
    return acc
  | .const n _ =>
    if n == ruleOf r then return #["??"]
    else if (`PM).isPrefixOf n then return (← closureOcc r n).1 else return #[]
  | .lam _ t b _ | .forallE _ t b _ => return (← stepsIn r t) ++ (← stepsIn r b)
  | .letE _ t v b _ => return (← stepsIn r t) ++ (← stepsIn r v) ++ (← stepsIn r b)
  | .mdata _ b | .proj _ _ b => stepsIn r b
  | _ => return #[]

/-- Whether a theorem stated for every reading asserts the same proposition under A and under the
    reading given by the constant `c` (the proposition, the last argument of `Thm9 S R`). -/
def sameUnderA (c : Name) (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  forallTelescope ci.type fun xs body => do
    let some r ← xs.findM? fun x => return (← inferType x).isConstOf ``PM.F9.Reading | return false
    unless body.isAppOf ``PM.F9.Thm9 do return false
    let p := body.appArg!
    isDefEq (p.replaceFVar r (mkConst ``PM.F9.Reading.printed)) (p.replaceFVar r (mkConst c))

def readingConst (r : String) : Name :=
  if r == "C" then ``PM.F9.Reading.russell else ``PM.F9.Reading.withSwitch

/-! ## The combinations of p. 142, searched again in C and L -/

def letterStr (i : Nat) (f : Char) : String :=
  let fn := ["φ", "ψ", "χ"][i]!
  match f with
  | 'e' => s!"(.el {["a", "b", "c"][i]!})"
  | 'a' => s!"(.all fun x => .el ({fn} x))"
  | _ => s!"(.ex fun x => .el ({fn} x))"

/-- The term `fun … => (by tac : Thm9 S R ((e1_k p q r).read d))` for a combination. -/
def comboTerm (k : String) (forms : List Char) (reading defs tac : String) : String :=
  let args := " ".intercalate ((forms.zipIdx).map fun (f, i) => letterStr i f)
  "fun (V : PM.Ty → Type) (S : PM.Sys) (τ₁ τ₂ τ₃ : PM.Ty) (φ : V τ₁ → PM.F9.EF V) " ++
  "(ψ : V τ₂ → PM.F9.EF V) (χ : V τ₃ → PM.F9.EF V) (a b c : PM.F9.EF V) (x₁ : V τ₁) (x₂ : V τ₂) " ++
  s!"(x₃ : V τ₃) => (by {tac} : PM.F9.Thm9 S PM.F9.Reading.{reading} ((PM.F9.{k} {args}).read .{defs}))"

/-- Elaborate a term given as text; `none` if it fails (an error, an error placeholder or a hole left). The
    messages of a failed search are discarded. -/
def elabText (s : String) : TermElabM (Option Expr) := do
  let some stx := (Parser.runParserCategory (← getEnv) `term s).toOption | return none
  let msgs ← Core.getMessageLog
  Core.setMessageLog {}
  let saved ← saveState
  let r ← try
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let failed := (← Core.getMessageLog).hasErrors || e.hasSorry || e.hasMVar
      pure (if failed then none else some e)
    catch _ => pure none
  if r.isNone then saved.restore
  Core.setMessageLog msgs
  return r

/-- The two propositions of a combination, as printed and in ✱9+, are the same. -/
def comboSame (k : String) (forms : List Char) : TermElabM Bool := do
  let args := " ".intercalate ((forms.zipIdx).map fun (f, i) => letterStr i f)
  let s := "fun (V : PM.Ty → Type) (τ₁ τ₂ τ₃ : PM.Ty) (φ : V τ₁ → PM.F9.EF V) " ++
    "(ψ : V τ₂ → PM.F9.EF V) (χ : V τ₃ → PM.F9.EF V) (a b c : PM.F9.EF V) => " ++
    s!"((PM.F9.{k} {args}).read .printed, (PM.F9.{k} {args}).read .plus)"
  let some e ← elabText s | return false
  lambdaTelescope e fun _ b => do
    let some (_, _, x, y) := b.app4? ``Prod.mk | return false
    isDefEq x y

end Star9Readings

open Star9Readings in
#eval show CommandElabM Unit from do
  let env ← getEnv
  -- ✱9's numbered propositions and the ✱10 assertions proved in ✱9: the theorem `f9_N` and, where
  -- one reading needs another proof, `f9_N_russell` (C) and `f9_N_switch` (L)
  let ids := ["9_2", "9_21", "9_22", "9_23", "9_24", "9_25", "9_3", "9_31", "9_32", "9_33", "9_34",
    "9_35", "9_36", "9_361", "9_37", "9_371", "9_4", "9_401", "9_41", "9_411", "9_42", "9_421",
    "9_5", "9_501", "9_51", "9_511", "9_52", "9_521", "10_01", "10_1", "10_11", "10_12"]
  for id in ids do
    let mut rs : Array String := #[]
    let mut decls : Array String := #[]
    let mut byR : Std.HashMap String Name := {}
    let mut aDecl : Option Name := none
    for suffix in ["", "_russell", "_switch"] do
      let n := (`PM.F9).str s!"f{id}{suffix}"
      let r ← liftTermElabM (readingsOf n)
      unless r.isEmpty do decls := decls.push s!"f{id}{suffix}"
      for x in r do unless rs.contains x do rs := rs.push x
      for x in r do unless byR.contains x do byR := byR.insert x n
      if r.contains "A" && aDecl.isNone then aDecl := some n
    logInfo m!"\{\"kind\": \"prop\", \"id\": \"*{id.replace "_" "."}\", \"readings\": {jstr (all4.filter rs.contains)}, \"decls\": {jstr decls}}"
    -- where the rule is used in C's and L's proofs, and whether A derives the same proposition
    for rd in ["C", "L"] do
      if let some c := byR[rd]? then
        let (cl, via) ← liftTermElabM (closureOcc rd c)
        let same ← match aDecl with
          | some a => if a == c then liftTermElabM (sameUnderA (readingConst rd) c) else pure false
          | none => pure false
        let viaS := jstr (via.map toString)
        logInfo m!"\{\"kind\": \"use\", \"reading\": \"{rd}\", \"id\": \"*{id.replace "_" "."}\", \"decl\": \"{c}\", \"direct\": {(directOf env rd c).size}, \"closure\": {cl.size}, \"kinds\": {jstr cl}, \"via\": {viaS}, \"underA\": {aDecl.isSome}, \"sameAsA\": {same}}"
  -- theorems whose readings the report states
  for n in [``PM.F9.f9_31_step, ``PM.F9.f9_31_step_plus, ``PM.F9.f9_31_step_convention,
      ``PM.F9.f10_12, ``PM.F9.distrib_convention, ``PM.F9.distrib_switch, ``PM.F9.Rep.distrib,
      ``PM.F9.star9_iff_star10, ``PM.F9.qthm_toF9, ``PM.F9.thm9_toQ, ``PM.F9.thm9_sound,
      ``PM.F9.Rep.toSwitch, ``PM.F9.Thm9.convention_toSwitch, ``PM.F9.switch_q10,
      ``PM.F9.switchStep_q10, ``PM.F9.exchStep_q10, ``PM.F9.switch_not_general,
      ``PM.F9.exch_not_general, ``PM.F9.switch_wide_unsound, ``PM.F9.switch_converse,
      ``PM.F9.switch_russell, ``PM.F9.exch_plus, ``PM.F9.Thm9.russell_toPrenex,
      ``PM.F9.ExchStep.symm, ``PM.F9.inst, ``PM.F9.idt, ``PM.F9.ai] do
    let r ← liftTermElabM (readingsOf n)
    let ok := env.contains n
    let mut parts : Array String := #[]
    for rd in ["C", "L"] do
      let (cl, via) ← liftTermElabM (closureOcc rd n)
      parts := parts.push s!"\"{rd}\": \{\"direct\": {(directOf env rd n).size}, \"closure\": {cl.size}, \"via\": {jstr (via.map toString)}}"
    logInfo m!"\{\"kind\": \"decl\", \"name\": \"{n}\", \"exists\": {ok}, \"readings\": {jstr r}, \"uses\": \{{", ".intercalate parts.toList}}}"
  -- p. 142 for one apparent variable per letter: the combinations each reading leaves open
  let show1 (l : List (List Char)) : String :=
    "[" ++ ", ".intercalate (l.map fun c => s!"\"{String.ofList c}\"") ++ "]"
  for (r, l) in [("A", [PM.F9.Printed.open1_2, PM.F9.Printed.open1_3, PM.F9.Printed.open1_4,
        PM.F9.Printed.open1_5, PM.F9.Printed.open1_6]),
      ("C", [PM.F9.Russell.open1_2, PM.F9.Russell.open1_3, PM.F9.Russell.open1_4,
        PM.F9.Russell.open1_5, PM.F9.Russell.open1_6]),
      ("L", [PM.F9.WithSwitch.open1_2, PM.F9.WithSwitch.open1_3, PM.F9.WithSwitch.open1_4,
        PM.F9.WithSwitch.open1_5, PM.F9.WithSwitch.open1_6]),
      ("B", [PM.F9.Convention.open1_2, PM.F9.Convention.open1_3, PM.F9.Convention.open1_4,
        PM.F9.Convention.open1_5, PM.F9.Convention.open1_6]),
      ("P", [PM.F9.PrenexSwitch.open1_2, PM.F9.PrenexSwitch.open1_3, PM.F9.PrenexSwitch.open1_4,
        PM.F9.PrenexSwitch.open1_5, PM.F9.PrenexSwitch.open1_6])] do
    let parts := (["*1.2", "*1.3", "*1.4", "*1.5", "*1.6"].zip l).map fun (p, o) => s!"\"{p}\": {show1 o}"
    logInfo m!"\{\"kind\": \"simul\", \"reading\": \"{r}\", \"open\": \{{", ".intercalate parts}}}"
  -- each combination of p. 142: found under A's definitions without a rule (the same proposition in A
  -- and C); in C with ✱8·13, in L without and with Switch, with the steps of the rule; and whether
  -- L's proposition is A's
  let close := "first | exact x₁ | exact x₂ | exact x₃"
  for (k, n) in [("e1_2", 1), ("e1_3", 2), ("e1_4", 2), ("e1_5", 3), ("e1_6", 3)] do
    let combos := (List.range (3 ^ n)).map fun i =>
      (List.range n).map fun j => ['e', 'a', 'x'][(i / 3 ^ (n - 1 - j)) % 3]!
    for forms in combos do
      if forms.all (· == 'e') then continue
      let cid := s!"*1.{k.drop 3} {String.ofList forms}"
      let inA ← liftTermElabM <| elabText (comboTerm k forms "printed" "printed" s!"search9 <;> {close}")
      let inC ← liftTermElabM <| elabText (comboTerm k forms "russell" "printed"
        s!"first | (search9 <;> {close}) | (search9r <;> {close}) | exact PM.F9.f9_31_russell φ")
      let plainL ← liftTermElabM <| elabText (comboTerm k forms "withSwitch" "plus" s!"search9 <;> {close}")
      let inL ← liftTermElabM <| elabText (comboTerm k forms "withSwitch" "plus"
        s!"first | (search9s <;> {close}) | exact PM.F9.f9_31_switch φ")
      let same ← liftTermElabM <| comboSame k forms
      let stepsC ← match inC with
        | some e => pure (some (← liftTermElabM (stepsIn "C" e)))
        | none => pure none
      let stepsL ← match inL with
        | some e => pure (toString (← liftTermElabM (stepsIn "L" e)).size)
        | none => pure "null"
      let sC := match stepsC with | some s => toString s.size | none => "null"
      let kC := match stepsC with | some s => jstr s | none => "null"
      logInfo m!"\{\"kind\": \"combo\", \"id\": \"{cid}\", \"provedA\": {inA.isSome}, \"provedC\": {inC.isSome}, \"stepsC\": {sC}, \"kindsC\": {kC}, \"plainL\": {plainL.isSome}, \"provedL\": {inL.isSome}, \"stepsL\": {stepsL}, \"sameAsA\": {same}}"
