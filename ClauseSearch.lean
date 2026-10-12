-- Search for a two-argument function on which p. 56's second clause and the lowest-order rule disagree
-- (maintainer, 2026-10-11 evening, item (iii)). Run with `lake env lean ClauseSearch.lean`.
--
-- `PM.second_clause_iff_lowestOrder` (PM/Pred/Curry.lean) proves that there is none within this
-- encoding (both partial applications evaluated at `()` in `U`, with the same body order O, so the
-- equivalence is the arithmetic O ≤ a + 1 ∨ O ≤ b + 1 ↔ O ≤ max a b + 1); this file is the concrete
-- search that preceded the proof, kept as a check. It compares the same definitions (`fnOrder`,
-- `fnOrder2`), so it checks the proof, not the encoding: it does not show that the encoding captures
-- PM's "assignment of values", nor anything about other variable families. It
-- enumerates bodies over the one-element family `U` up to depth 2, built from a letter, every
-- application `app1`/`app2` at the function types below, ∼, ∨, and (x) over each type below; and every
-- pair of argument types from the list. For each it compares the clause (fixing one argument gives a
-- predicative function of the other; fixed arguments counted at their own order, p. 55) with the
-- lowest-order rule (order = highest argument order + 1).
import PM
open PM

def tys : List Ty :=
  [.ind, Ty.pred1 .ind, .fn1 .ind 1, Ty.pred1 (Ty.pred1 .ind), .fn1 (Ty.pred1 .ind) 1,
   Ty.pred2 .ind .ind, Ty.pred2 (Ty.pred1 .ind) .ind, .fn2 .ind .ind 1, Ty.pred1 (.fn1 .ind 1)]

def leaves : List (QF U) :=
  [.atom "P" []] ++
  (tys.filterMap fun t => match t with
    | .fn1 a k => some (QF.app1 (V := U) (a := a) (k := k) () ())
    | .fn2 a b k => some (QF.app2 (V := U) (a := a) (b := b) (k := k) () () ())
    | .ind => none)

def forms : Nat → List (QF U)
  | 0 => leaves
  | n + 1 =>
    let f := forms n
    f ++ f.map .neg ++ (f.flatMap fun p => f.map fun q => .or p q) ++
      (tys.flatMap fun t => f.map fun p => QF.all (τ := t) fun _ => p)

def clause (a b : Ty) (p : QF U) : Bool :=
  fnOrder a (fun _ => p) == a.ord + 1 || fnOrder b (fun _ => p) == b.ord + 1

def lowest (a b : Ty) (p : QF U) : Bool :=
  fnOrder2 a b (fun _ _ => p) == max a.ord b.ord + 1

#eval
  let fs := forms 2
  let pairs := tys.flatMap fun a => tys.map fun b => (a, b)
  let bad := pairs.flatMap fun (a, b) => (fs.filter fun p => clause a b p != lowest a b p).map fun _ => (a.ord, b.ord)
  let agreeTrue := pairs.foldl (fun n (a, b) => n + (fs.filter fun p => clause a b p && lowest a b p).length) 0
  s!"{fs.length} bodies x {pairs.length} argument-type pairs = {fs.length * pairs.length} cases; predicative under both: {agreeTrue}; disagreements: {bad.length}"
