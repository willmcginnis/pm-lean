/-
Every top-level command of a Lean file, with its syntax kind, for scripts/prove2me/export.py (the
companion of Prove2Me's scripts/extract_sketch_info.lean, which reports declarations only).

Skeleton subtraction must also decide what to do with the other top-level commands —
`namespace`/`end`/`open`/`section`/`variable`, `local notation`, global `macro`/`notation`, `example`,
module docs — and that decision comes from the parser, not from searching the text. This program
re-elaborates one file and prints one JSON line per top-level command:

  {"kind":"cmd","syntaxKind":…,"innerKind":…|null,"isLocal":bool,"declName":…|null,
   "idents":[…],"quotBody":R|null,"userSyntax":[…],"ctors":[…],"start":P,"end":P}

  syntaxKind  the command's syntax node kind (e.g. `Lean.Parser.Command.open`)
  innerKind   for a `Command.declaration`, the kind of the declaration inside it
              (`Lean.Parser.Command.theorem`, `…definition`, `…example`, …); null otherwise
  isLocal     the command carries a `local` attribute kind (`local notation`, `local macro`)
  declName    the declId text, if any (join to Stage 2 by position, not by this)
  idents      for a command that is not a declaration (notation, macro, syntax, …): every identifier in
              its syntax tree, including those inside syntax quotations. A macro whose quotation names a
              theorem must be declared after that theorem (the quotation's identifiers are resolved where
              the macro is defined), so consumers use this to keep such a macro next to the theorems it
              names.
  quotBody    for a `macro` command: the source range of the body of its syntax quotation
              (`(tactic| BODY)`), or null — what a use of the macro expands to
  userSyntax  every syntax node inside the command whose kind is a project kind (name starts with the
              namespace prefix given as second argument, e.g. `PM.tacticIntro_`):
              [{"kind":…,"range":R}] — the use sites of the project's own macros
  ctors       for an `inductive` command, its constructors: [{"name":…,"sig":R}], `sig` the range of
              the constructor's binders and type (`(p : F) : Thm (…)`)
  start/end   the command's source range; P = {"line","col","offset"} (byte offset), R = {"start","end"}

How to run (from a project where the file's imports resolve):
  lake env lean --run extract_commands.lean <File.lean> [namePrefix] > commands.jsonl
-/
import Lean
open Lean Elab Parser

partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else stx.getArgs.findSome? (findKind? · k)

partial def findAll (stx : Syntax) (k : SyntaxNodeKind) : Array Syntax :=
  if stx.getKind == k then #[stx]
  else stx.getArgs.foldl (fun acc a => acc ++ findAll a k) #[]

partial def idents (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.foldl (fun acc a => acc ++ idents a) #[]
  | _ => #[]

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column),
              ("offset", toJson p.byteIdx)]

def rangeJson (fm : FileMap) (stx : Syntax) : Json :=
  match stx.getPos?, stx.getTailPos? with
  | some s, some e => Json.mkObj [("start", posJson fm s), ("end", posJson fm e)]
  | _, _ => Json.null

/-- Nodes whose kind name starts with `pfx` (outermost first; a match is not searched inside). -/
partial def userNodes (pfx : Name) (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ k args =>
    if pfx != .anonymous && pfx.isPrefixOf k then #[stx]
    else args.foldl (fun acc a => acc ++ userNodes pfx a) #[]
  | _ => #[]

/-- The constructors of an `inductive` command: name and the range of its binders and type. -/
def ctorsJson (fm : FileMap) (cmd : Syntax) : Json :=
  Json.arr <| (findAll cmd ``Command.ctor).filterMap fun c =>
    let name? := c.getArgs.findSome? fun a => if a.isIdent then some a.getId else none
    match name?, findKind? c ``Command.optDeclSig with
    | some n, some sig => some (Json.mkObj [("name", Json.str n.toString), ("sig", rangeJson fm sig)])
    | _, _ => none

unsafe def main (args : List String) : IO UInt32 := do
  let some fileName := args[0]?
    | do IO.eprintln "usage: lake env lean --run extract_commands.lean <File.lean> [namePrefix]"
         return 1
  let pfx : Name := (args[1]?.map String.toName).getD .anonymous
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let cmdState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState cmdState
  if s.commandState.messages.hasErrors then
    for msg in s.commandState.messages.toList do
      IO.eprintln (← msg.toString)
    return 1
  let fm := inputCtx.fileMap
  -- the header (imports) as one pseudo-command, so consumers know where the body starts
  if let (some hs, some he) := (header.raw.getPos?, header.raw.getTailPos?) then
    IO.println (Json.mkObj [("kind", "cmd"), ("syntaxKind", "header"), ("innerKind", Json.null),
      ("isLocal", false), ("declName", Json.null),
      ("start", posJson fm hs), ("end", posJson fm he)]).compress
  for cmd in s.commands do
    let some cs := cmd.getPos? | continue
    let some ce := cmd.getTailPos? | continue
    if cmd.getKind == ``Command.eoi then continue
    let decl? := findKind? cmd ``Command.declaration
    let inner := decl?.map fun d => d[1].getKind.toString
    let declId? := (decl?.getD cmd) |> (findKind? · ``Command.declId)
    let isLocal := (findKind? cmd ``Term.local).isSome
    let ids := if decl?.isSome then #[] else (idents cmd).map (·.toString)
    let quot? := if cmd.getKind == ``Command.macro then
        ((findKind? cmd ``Lean.Parser.Tactic.quot).orElse fun _ => findKind? cmd ``Lean.Parser.Term.quot)
      else none
    let quotBody := match quot? with
      | some q => rangeJson fm q[1]
      | none => Json.null
    let uses := (userNodes pfx cmd).map fun u =>
      Json.mkObj [("kind", Json.str u.getKind.toString), ("range", rangeJson fm u)]
    let ctors := if inner == some (``Command.inductive).toString then ctorsJson fm cmd else Json.arr #[]
    IO.println (Json.mkObj [("kind", "cmd"), ("syntaxKind", cmd.getKind.toString),
      ("innerKind", inner.map Json.str |>.getD Json.null),
      ("isLocal", toJson isLocal),
      ("idents", toJson ids),
      ("quotBody", quotBody),
      ("userSyntax", Json.arr uses),
      ("ctors", ctors),
      ("declName", declId?.map (fun d => Json.str d[0].getId.toString) |>.getD Json.null),
      ("start", posJson fm cs), ("end", posJson fm ce)]).compress
  return 0
