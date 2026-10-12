-- Citations against proof terms. Run from the repository root with
-- `lake env lean Checks/LedgerCheck.lean`.
--
-- Three checks, all reading which PM propositions a proof uses from its proof term: the constants of
-- its value, followed transitively through helper declarations under `PM` (`qsyl`, `qandI`, the
-- `Trans` instances, private lemmas, ...), stopping at PM propositions (`QL.tA_B` for ✱A·B in ✱2–✱5,
-- `qA_B` for ✱A·B from ✱9 on; `q10_11_28` is ✱10·11 and ✱10·28; a suffix as in `q14_21_neg` is a
-- form of the numbered proposition).
--
-- 1. PM/Chain.lean: every proposition a docstring cites is used by the proof. A review found that
--    `transIff`'s docstring cited ✱4·22 while its proof (by an earlier helper) never used it. Cited
--    means ✱A·B (✱A·B·C is ✱A·B and ✱A·C), "Syll" (✱2·05 or ✱2·06) and "Comp" (✱3·43), except in
--    the warrant after "tacit:" up to the next ";" or ")" (e.g. "tacit: ✱2·31, pp. 109–110"), which
--    names the passage where PM leaves the step tacit, not a step of the proof.
-- 2. The ledgers data/star11–21_ledger.json: every PM proposition the proof of a row's theorem uses
--    is listed in the row, in cited_used, extra_used, tacit or glue ("Syll" in tacit is ✱2·05 and
--    ✱2·06; "✱10·27/271/28/281" is ✱10·27, ✱10·271, ✱10·28, ✱10·281). A review found ✱10·281
--    missing from two rows (✱14·18, ✱14·203): there a helper carried a step under (∃x) by ✱10·281.
--    So the propositions of the tacit pattern (✱10·11, ✱10·27, ✱10·271, ✱10·28, ✱10·281) count as
--    listed only where the row's own proof term uses them, not where they come from a helper.
--    An equivalence read as an implication (✱4·01 with ✱3·26 or ✱3·27 on (a ⊃ b) . (b ⊃ a), as in
--    `qiffMp`, `qiffMpr`, or written out) is, outside a displayed chain, the rows' tacit
--    "definitions" step, and is not a use; inside one (the `Trans` instances `transIffImp`,
--    `transImpIff`, a ≡ line joined to a ⊃ line) it is chain glue, a use of ✱3·26 that the row
--    lists in glue (docs/FIDELITY.md). Conversely, a row that lists ✱3·26 or ✱3·27 in extra_used
--    or glue must use it in one of these listed ways (Simp on a product that is not an
--    equivalence, or chain glue): reading a ≡ as ⊃ outside a chain is not an extra.
--    Uses awaiting a decision on their row can be put in tests/ledger_unlisted_uses.txt (empty
--    now); they are reported, not failed. A use not in that file fails, and so does an entry of
--    the file that no longer occurs (remove it when the row is fixed).
-- 3. The ledger data/star9f_ledger.json of ✱9's own method (PM/Found9), as check 2 with ✱9's names
--    (below, before the third `#eval`).
-- Each check fails (an error) on any disagreement.
import Lean
import PM
open Lean Elab Command

namespace LedgerCheck

/-- A PM proposition: `PM.q…` with a digit after the `q`, or `PM.QL.…`. -/
def isPMProp (n : Name) : Bool :=
  match n with
  | .str (.str .anonymous "PM") s => s.startsWith "q" && ((s.drop 1).take 1).all Char.isDigit
      && !(s.drop 1).isEmpty
  | .str (.str (.str .anonymous "PM") "QL") _ => true
  | _ => false

/-- The ✱ numbers a PM proposition's name stands for, as ledger ids `*A.B`: `q10_11_28` gives
    `*10.11`, `*10.28`; `QL.t4_22` gives `*4.22`; non-numeric segments end the list. -/
def starsOf (n : Name) : Array String :=
  let s := match n with
    | .str (.str .anonymous "PM") s => (s.drop 1).toString
    | .str (.str (.str .anonymous "PM") "QL") s => if s.startsWith "t" then (s.drop 1).toString else ""
    | _ => ""
  let segs := (s.splitOn "_").takeWhile fun p => !p.isEmpty && p.all Char.isDigit
  match segs with
  | a :: bs => (bs.map fun b => s!"*{a}.{b}").toArray
  | [] => #[]

/-- The declaration of ledger id `*A.B`. -/
def declOf (id : String) : Name :=
  match ((id.drop 1).toString.splitOn ".") with
  | [a, b] => if a.toNat! ≤ 5 then (`PM.QL).str s!"t{a}_{b}" else (`PM).str s!"q{a}_{b}"
  | _ => .anonymous

def isAux (env : Environment) (c : Name) : Bool :=
  isAuxRecursor env c || isNoConfusion env c || isRecCore env c || Meta.isMatcherCore env c

def underPM (c : Name) : Bool := (`PM).isPrefixOf c || c.toString.startsWith "_private.PM."

/-- Is `e` Simp (✱3·26 or ✱3·27) applied to an equivalence, `(a ⊃ b) . (b ⊃ a)` (✱4·01): an
    equivalence read as an implication? -/
def isIffRead (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
    (n == `PM.QL.t3_26 || n == `PM.QL.t3_27) && e.getAppNumArgs == 4 &&
      match e.getArg! 2 |>.getAppFnArgs, e.getArg! 3 |>.getAppFnArgs with
      | (`PM.QF.imp, #[_, a, b]), (`PM.QF.imp, #[_, b', a']) => a == a' && b == b'
      | _, _ => false
  | _ => false

/-- The constants of `e`; with `iffTacit`, leaving out ✱3·26 and ✱3·27 where they read an
    equivalence as an implication (`isIffRead`). -/
partial def constsOf (iffTacit : Bool) (e : Expr) (acc : Array Name) : Array Name :=
  match e with
  | .const n _ => if acc.contains n then acc else acc.push n
  | .app .. =>
    let acc := e.getAppArgs.foldl (fun a x => constsOf iffTacit x a) acc
    if iffTacit && isIffRead e then acc else constsOf iffTacit e.getAppFn acc
  | .lam _ t b _ | .forallE _ t b _ => constsOf iffTacit b (constsOf iffTacit t acc)
  | .letE _ t v b _ => constsOf iffTacit b (constsOf iffTacit v (constsOf iffTacit t acc))
  | .mdata _ e | .proj _ _ e => constsOf iffTacit e acc
  | _ => acc

/-- The `Trans` instances of PM/Chain.lean that join a ≡ line and a ⊃ line in a displayed chain,
    reading the ≡ as ⊃ by ✱3·26: chain glue, so check 2 counts them as a use of ✱3·26. -/
def chainIffReads : Array Name := #[`PM.transIffImp, `PM.transImpIff]

/-- The PM propositions `c`'s value reaches through helpers (not through other PM propositions),
    except those in `skip`; with `within := some r`, only through `r`'s own auxiliary declarations.
    With `iffTacit` (check 2), an equivalence read as an implication is not a use of ✱3·26 or
    ✱3·27, except in the chain instances `chainIffReads`, which count as ✱3·26. -/
partial def reachProps (skip : Array Name) (within : Option Name) (c : Name) (iffTacit := false) :
    StateT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  if let some r := (← get).get? c then return r
  modify (·.insert c #[])   -- in progress
  let env ← getEnv
  let mut out : Array Name := #[]
  if iffTacit && chainIffReads.contains c then
    out := #[`PM.QL.t3_26]
  else if let some ci := env.find? c then
    if let some v := ci.value? (allowOpaque := true) then
      for d in constsOf iffTacit v #[] do
        if d == c then continue
        if isPMProp d then
          unless out.contains d do out := out.push d
        else if underPM d && !isAux env d && !skip.contains d && (within.all (·.isPrefixOf d)) then
          for e in ← reachProps skip within d iffTacit do
            unless out.contains e do out := out.push e
  modify (·.insert c out)
  return out

/-- Citations in a PM/Chain.lean docstring, as ledger ids; "Syll" as `Syll`. -/
def citationsOf (doc : String) : Array String := Id.run do
  -- drop the warrants: from "tacit:" to the next ";" or ")"
  let parts := doc.splitOn "tacit:"
  let mut text := parts.head!
  for p in parts.tail! do
    let rest := p.dropWhile fun ch => ch != ';' && ch != ')'
    text := text ++ rest.toString
  let mut out : Array String := #[]
  if (text.splitOn "Syll").length > 1 then out := out.push "Syll"
  if (text.splitOn "Comp").length > 1 then out := out.push "*3.43"
  let cs := text.toList
  let mut i := 0
  while i < cs.length do
    if cs[i]! == '✱' then
      let mut j := i + 1
      let mut nums : Array String := #[]
      let mut cur := ""
      while j < cs.length &&
          (cs[j]!.isDigit || (cs[j]! == '·' && j + 1 < cs.length && cs[j+1]!.isDigit)) do
        if cs[j]! == '·' then nums := nums.push cur; cur := ""
        else cur := cur.push cs[j]!
        j := j + 1
      nums := nums.push cur
      if h : nums.size ≥ 2 then
        for b in nums.extract 1 nums.size do
          let id := s!"*{nums[0]}.{b}"
          unless out.contains id do out := out.push id
      i := j
    else i := i + 1
  return out

/-- Ledger entries as ids: `*A.B` tokens, with `/`-abbreviations, and "Syll" as ✱2·05, ✱2·06. -/
def idsOfEntry (e : String) : Array String := Id.run do
  let mut out : Array String := #[]
  if e == "Syll" then return #["*2.05", "*2.06"]
  for w in e.splitOn " " do
    if w.startsWith "*" then
      match ((w.drop 1).toString.splitOn ".") with
      | [a, bs] => for b in bs.splitOn "/" do
          let b := (b.takeWhile Char.isDigit).toString
          unless b.isEmpty do out := out.push s!"*{a}.{b}"
      | _ => pure ()
  return out

/-- Helpers whose propositions are the ledgers' tacit "definitions" step, not followed by check 2:
    an equivalence used as either implication, ✱4·01 with Simp (✱3·26, ✱3·27). -/
def tacitRules : Array Name := #[`PM.qiffMp, `PM.qiffMpr]

/-- The baseline of check 2: lines "row proposition …" of tests/ledger_unlisted_uses.txt, `#`
    starting a comment. -/
def readKnown (path : System.FilePath) : IO (Array (String × String)) := do
  let mut out := #[]
  for l in ← IO.FS.lines path do
    match (((l.splitOn "#").head!.splitOn " ").filter (!·.isEmpty)) with
    | id :: u :: _ => out := out.push (id, u)
    | _ => pure ()
  return out

/-- The tacit entry "✱10·11 + ✱10·27/271/28/281 pattern (pp. 161-162)": a step carried under a
    quantifier in the proof itself. -/
def isPattern (e : String) : Bool := (e.splitOn "pattern").length > 1

def strs (j : Json) (k : String) : Array String :=
  (j.getObjValAs? (Array String) k).toOption.getD #[]

end LedgerCheck
open LedgerCheck

#eval show CommandElabM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `PM.Chain | throwError "module PM.Chain not found"
  let decls := (env.constants.fold (init := #[]) fun acc c _ =>
    if env.getModuleIdxFor? c == some idx && !c.isInternal then acc.push c else acc).qsort Name.lt
  let mut checked : Nat := 0
  let mut bad : Array MessageData := #[]
  for c in decls do
    let some doc ← findDocString? env c | continue
    let cited := citationsOf doc
    if cited.isEmpty then continue
    checked := checked + 1
    let used ← liftCoreM ((reachProps #[] none c).run' {})
    let usedIds := used.flatMap starsOf
    for id in cited do
      let ok := if id == "Syll" then usedIds.contains "*2.05" || usedIds.contains "*2.06"
        else usedIds.contains id
      unless ok do bad := bad.push m!"{c}: docstring cites {id}, proof uses {used}"
  logInfo m!"PM/Chain.lean: {checked} declarations whose docstring cites a proposition; {bad.size} citations not used by the proof"
  for b in bad do logError b

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Nat := 0
  let known ← readKnown "tests/ledger_unlisted_uses.txt"
  let mut bad : Array (String × String) := #[]   -- (row, proposition used but not listed)
  let mut via : Array (List Name) := #[]          -- the helpers of the row's proof that bring it in
  let mut missing : Array String := #[]
  let mut iffListed : Array String := #[]          -- ✱3·26 / ✱3·27 listed for a ≡ read as ⊃
  for ch in ["star11", "star12", "star13", "star14", "star20", "star21"] do
    let path := s!"data/{ch}_ledger.json"
    let j ← match Json.parse (← IO.FS.readFile path) with
      | .ok j => pure j
      | .error e => throwError "{path}: {e}"
    let some arr := j.getArr?.toOption | throwError "{path}: not an array"
    for r in arr do
      let some id := (r.getObjValAs? String "id").toOption | throwError "{path}: row without id"
      let c := declOf id
      unless env.contains c do missing := missing.push s!"{id} ({c})"; continue
      rows := rows + 1
      let tacit := (strs r "tacit").filter (!isPattern ·)
      let listed := (["cited_used", "extra_used", "glue"].toArray.flatMap (strs r ·) ++ tacit).flatMap
        idsOfEntry |>.push id
      let pattern := ((strs r "tacit").filter isPattern).flatMap idsOfEntry
      let used ← liftCoreM ((reachProps tacitRules none c true).run' {})
      let direct ← liftCoreM ((reachProps tacitRules (some c) c true).run' {})
      -- ✱3·26 and ✱3·27 listed as extra or glue must be used other than to read a ≡ as ⊃
      for u in ["*3.26", "*3.27"] do
        if (["extra_used", "glue"].toArray.flatMap (strs r ·)).contains u &&
            !(used.flatMap starsOf).contains u then
          iffListed := iffListed.push s!"{id} {u}"
      for d in used do
        let ok (u : String) := listed.contains u || (pattern.contains u && direct.contains d)
        for u in (starsOf d).filter (!ok ·) do
          unless bad.contains (id, u) do
            bad := bad.push (id, u)
            let hs := ((env.find? c).bind (·.value? (allowOpaque := true))).map (·.getUsedConstants)
              |>.getD #[]
            let mut vs : List Name := []
            for h in hs do
              if !isPMProp h && underPM h && (← liftCoreM ((reachProps tacitRules none h true).run' {})).contains d then
                vs := vs ++ [h]
            via := via.push (if direct.contains d then [c] else vs)
  let new := bad.filter (!known.contains ·)
  let stale := known.filter (!bad.contains ·)
  logInfo m!"ledgers: {rows} rows checked against their proofs; {bad.size} propositions used but not listed, of which {bad.size - new.size} in tests/ledger_unlisted_uses.txt"
  unless missing.isEmpty do logInfo m!"rows with no declaration of that name: {missing}"
  for i in [:bad.size] do
    let (id, u) := bad[i]!
    let line := s!"{id} {u}  # through {" ".intercalate (via[i]!.map toString)}"
    unless known.contains (id, u) do logError m!"not listed in its ledger row: {line}"
  for x in iffListed do
    logError m!"{x}: listed in extra_used or glue, but the proof uses it only to read a ≡ as ⊃ outside a chain (tacit)"
  for (id, u) in stale do
    logError m!"{id} {u} is in tests/ledger_unlisted_uses.txt but no longer found; remove the line"

/-! 3. The ledger of ✱9's own method, data/star9f_ledger.json (PM/Found9): the same check as 2, with
  ✱9's names. A row `*9.N` (`*10.N`) is `PM.F9.f9_N` (`PM.F9.f10_N`). The propositions a proof can use
  are the ✱9 theorems `PM.F9.fA_B` and `PM.F9.eA_B` (✱A·B for elementary propositions), the ✱2–✱5
  theorems `PM.tA_B` that `elift` carries to elementary propositions, and the primitive propositions
  of `Thm9`: ✱1·2–✱1·6 (`taut` … `sum`), ✱9·1 (`ex1`), ✱9·11 (`ex2`), ✱9·13 (`gen`). ✱9·12 (`mp`) is
  the rule of inference and, like ✱1·1 in check 2, is not listed. `elift` itself is not followed: it
  replays a ✱1–✱5 derivation, whose proposition the row lists. -/
namespace LedgerCheck

/-- The ledger ids a declaration stands for in ✱9's method; empty if it is not a ✱9 proposition. -/
def stars9Of (n : Name) : Array String :=
  let prims : List (String × String) := [("taut", "*1.2"), ("add", "*1.3"), ("perm", "*1.4"),
    ("assoc", "*1.5"), ("sum", "*1.6"), ("ex1", "*9.1"), ("ex2", "*9.11"), ("gen", "*9.13")]
  match n with
  | .str (.str (.str (.str .anonymous "PM") "F9") "Thm9") c =>
      ((prims.lookup c).map (#[·])).getD #[]
  | .str (.str (.str .anonymous "PM") "F9") s =>
      if s.startsWith "f" || s.startsWith "e" then starsOf ((`PM).str ("q" ++ (s.drop 1).toString))
      else #[]
  | .str (.str .anonymous "PM") s =>
      if s.startsWith "t" then starsOf ((`PM).str ("q" ++ (s.drop 1).toString)) else #[]
  | _ => #[]

/-- The declaration of ledger id `*A.B` in ✱9's method. -/
def declOf9 (id : String) : Name :=
  match ((id.drop 1).toString.splitOn ".") with
  | [a, b] => (`PM.F9).str s!"f{a}_{b}"
  | _ => .anonymous

/-- The ✱9 propositions `c`'s value reaches through helpers, as `reachProps` does for check 2. -/
partial def reachProps9 (c : Name) : StateT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  if let some r := (← get).get? c then return r
  modify (·.insert c #[])
  let env ← getEnv
  let mut out : Array Name := #[]
  if let some ci := env.find? c then
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do
        if d == c then continue
        if !(stars9Of d).isEmpty then
          unless out.contains d do out := out.push d
        else if underPM d && !isAux env d && d != `PM.F9.elift then
          for e in ← reachProps9 d do
            unless out.contains e do out := out.push e
  modify (·.insert c out)
  return out

end LedgerCheck

#eval show CommandElabM Unit from do
  let env ← getEnv
  let path := "data/star9f_ledger.json"
  let j ← match Json.parse (← IO.FS.readFile path) with
    | .ok j => pure j
    | .error e => throwError "{path}: {e}"
  let some arr := j.getArr?.toOption | throwError "{path}: not an array"
  let mut rows : Nat := 0
  let mut bad : Array String := #[]
  let mut missing : Array String := #[]
  let mut notStated : Nat := 0
  let mut opens : Array String := #[]
  for r in arr do
    let some id := (r.getObjValAs? String "id").toOption | throwError "{path}: row without id"
    let c := declOf9 id
    let method := (r.getObjValAs? String "method").toOption
    if method == some "open" then
      -- not proved (the row's note says what is); there must be no declaration of that name
      if env.contains c then logError m!"{id}: method \"open\" but {c} is a theorem"
      opens := opens.push id
      continue
    unless env.contains c do
      -- ✱9·14, ✱9·15, ✱9·131, ✱9·6–✱9·63 are built into the syntax and not stated
      if method == some "not stated" then
        notStated := notStated + 1
      else
        missing := missing.push s!"{id} ({c})"
      continue
    rows := rows + 1
    let listed := (["cited_used", "extra_used", "glue", "tacit"].toArray.flatMap (strs r ·)).flatMap
      idsOfEntry |>.push id
    let used ← liftCoreM ((reachProps9 c).run' {})
    for d in used do
      for u in (stars9Of d).filter (!listed.contains ·) do
        let line := s!"{id} {u}  # {d}"
        unless bad.contains line do bad := bad.push line
  logInfo m!"✱9 ledger: {rows} rows checked against their proofs ({notStated} rows not stated, built into the syntax; {opens.size} open: {opens}); {bad.size} propositions used but not listed"
  unless missing.isEmpty do logError m!"{path}: rows with no declaration of that name: {missing}"
  for b in bad do logError m!"not listed in its ledger row: {b}"
