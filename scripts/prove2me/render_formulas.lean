/-
Render the statement formulas of ✱1–✱5 (the `PM.s…` definitions of PM/Statements.lean) as LaTeX
and as Unicode text, for the titles and descriptions of exported cards (scripts/prove2me/metadata.py).

The rendering reads the *elaborated* definition bodies (Expr), not the source text, and keeps the
defined connectives as written: `F.imp` ↦ ⊃ (✱1·01), `F.and` ↦ ∧ (PM's dot, ✱3·01),
`F.iff` ↦ ≡ (✱4·01), `F.or` ↦ ∨, `F.neg` ↦ ∼. Every binary subformula is parenthesised (no
precedence or dot conventions are assumed), so the rendering is unambiguous.

Run from a built copy of the repository:  lake env lean <path>/render_formulas.lean
Writes formulas.json there: {"PM.s2_01": {"binders": ["p"], "latex": "…", "text": "…"}, …}
-/
import PM.Statements
import Lean
open Lean Meta

partial def render (latex : Bool) (names : Array String) (e : Expr) : MetaM (String × Bool) := do
  -- returns (rendering, isBinary)
  let e := e.headBeta
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``PM.F.neg, #[a] => do
      let (s, b) ← render latex names a
      let s := if b then s!"({s})" else s
      return (if latex then s!"{"{"}\\sim{"}"} {s}" else s!"∼{s}", false)
  | some c, #[a, b] =>
      let op? : Option (String × String) :=
        if c == ``PM.F.or then some ("\\lor", "∨")
        else if c == ``PM.F.imp then some ("\\supset", "⊃")
        else if c == ``PM.F.and then some ("\\land", "∧")
        else if c == ``PM.F.iff then some ("\\equiv", "≡")
        else none
      match op? with
      | some (l, t) => do
          let (sa, ba) ← render latex names a
          let (sb, bb) ← render latex names b
          let sa := if ba then s!"({sa})" else sa
          let sb := if bb then s!"({sb})" else sb
          return (s!"{sa} {if latex then l else t} {sb}", true)
      | none => throwError "unexpected application {e}"
  | _, _ =>
    match e with
    | .bvar i => return (names[names.size - 1 - i]!, false)
    | _ => match e.getAppFn.constName?, e.getAppArgs with
      | some ``PM.F.var, #[.lit (.strVal s)] => return (s, false)
      | _, _ => throwError "unexpected term {e}"

run_meta do
  let env ← getEnv
  let mut out : Array (String × Json) := #[]
  for (n, ci) in env.constants.toList do
    unless (`PM).isPrefixOf n do continue
    let s := n.toString
    unless s.startsWith "PM.s" && (s.drop 4).all (fun c => c.isDigit || c == '_') do continue
    let some v := ci.value? | continue
    -- peel the lambda binders without instantiating (bvars index into `names`)
    let mut body := v
    let mut names : Array String := #[]
    while body.isLambda do
      names := names.push body.bindingName!.toString
      body := body.bindingBody!
    let (lx, _) ← render true names body
    let (tx, _) ← render false names body
    out := out.push (s, Json.mkObj [("binders", toJson names), ("latex", Json.str lx), ("text", Json.str tx)])
  IO.FS.writeFile "formulas.json" (Json.mkObj out.toList).pretty
  logInfo s!"rendered {out.size} formulas"
