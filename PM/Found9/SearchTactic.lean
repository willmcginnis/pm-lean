import Lean
import PM.Found9.Syntax
/-!
  Meta code for the proof search of PM/Found9/Simul.lean in ✱9+: `merge_split` finds the two parts of
  a merge (`Merge`) for the side condition of Switch (`Sep`). It is not part of any proof: it only
  proposes the parts, and the proof of the merge is then built from `Merge`'s constructors and checked
  by Lean's kernel like every other proof term. It lives outside the `PM` namespace, as the check
  programs do.

  Goal: `∀ x y, Merge (?L x) (?R y) (Z x y)` (or with the parts the other way round). For each x, y
  the proposition Z x y is a prefix of quantifiers over an elementary matrix a ∨ b. The part with x is
  the quantifiers whose variables occur in a, over a; the part with y those whose variables occur in b,
  over b (a quantifier whose variable occurs in neither goes with the first part). It fails if a
  contains y, b contains x, or a quantifier's variable occurs on both sides.
-/
namespace Star9Search
open Lean Meta Elab Tactic

/-- The parts of the merge `C` with `a` free in the first and `b` in the second. -/
partial def split (C a b : Expr) : MetaM (Expr × Expr) := do
  let C ← whnf C
  match C.getAppFnArgs with
  | (``PM.F9.PF.el, #[V, e]) =>
    let e ← whnf e
    match e.getAppFnArgs with
    | (``PM.F9.EF.or, #[_, l, r]) =>
      if l.containsFVar b.fvarId! || r.containsFVar a.fvarId! then
        throwError "merge_split: the matrix does not separate the two variables"
      let el := mkConst ``PM.F9.PF.el
      return (mkApp2 el V l, mkApp2 el V r)
    | _ => throwError "merge_split: the matrix is not a disjunction"
  | (q@``PM.F9.PF.all, #[V, τ, f]) | (q@``PM.F9.PF.ex, #[V, τ, f]) =>
    withLocalDeclD `z (mkApp V τ) fun z => do
      let (P, Q) ← split (mkApp f z).headBeta a b
      let inP := P.containsFVar z.fvarId!
      let inQ := Q.containsFVar z.fvarId!
      if inP && inQ then throwError "merge_split: a quantifier binds a variable of both parts"
      if inQ then return (P, mkApp3 (mkConst q) V τ (← mkLambdaFVars #[z] Q))
      return (mkApp3 (mkConst q) V τ (← mkLambdaFVars #[z] P), Q)
  | _ => throwError "merge_split: not a proposition with its quantifiers in front"

/-- Assign the parts of a merge goal `∀ x y, Merge A B (Z x y)` and leave `Merge A B (Z x y)` with x, y
    introduced, A and B known. -/
elab "merge_split" : tactic => do
  let g ← getMainGoal
  let (#[x, y], g) ← g.introNP 2 | throwError "merge_split: expected two variables"
  replaceMainGoal [g]
  g.withContext do
    let tgt ← instantiateMVars (← whnfR (← g.getType))
    let some (_, A, B, C) := tgt.app4? ``PM.F9.Merge | throwError "merge_split: not a merge"
    let xe := Expr.fvar x
    let ye := Expr.fvar y
    -- the part with x first (`Sep.left`) or the part with y first (`Sep.right`)
    let (first, second) := if A.getAppArgs.any (·.containsFVar x) then (xe, ye) else (ye, xe)
    let (P, Q) ← split C first second
    -- the parts are the holes `?_` that `refine` left for them
    unless ← withAssignableSyntheticOpaque (isDefEq A P) do
      throwError "merge_split: cannot assign the first part"
    unless ← withAssignableSyntheticOpaque (isDefEq B Q) do
      throwError "merge_split: cannot assign the second part"

end Star9Search
