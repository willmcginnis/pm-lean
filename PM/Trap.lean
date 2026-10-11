import PM.Star12
import PM.Complete
import PM.Orders
/-!
  Degenerate variable families: a documented negative example (docs/TYPES_DESIGN.md, decision 12 and
  test C3).

  `QThm` is defined for every family `V : Ty → Type`, and ✱10·11 (`gen`) is the rule "if φy is a
  theorem for every y in `V τ`, then (x) . φx is". When `V τ` is not the full range of a type, this
  rule says too much, and together with ✱12·1 everything becomes a theorem at that `V`:
  - `trap_empty`: the type (ι)/1 of predicative functions of individuals is empty. ✱10·11 holds
    vacuously for it, and contradicts ✱12·1.
  - `trap_unit`: every type has one variable (the family `U` used by the order checker). Then all
    predicative functions of individuals are "the same", so φx and ∼φx, both formally equivalent to
    some predicative function by ✱12·1, are equivalent to each other.
  The second example shows that requiring every function type to be non-empty would not repair the
  rule. So this project never presents `QThm` at an arbitrary `V` as PM's system:
  - a PM theorem is a Lean theorem *for every* `V` (all of ✱9–✱20 here), which holds in particular at
    the variables of every structure (`qsound`);
  - consistency is stated at a structure's own variables (`consistent`) and for theorems that hold at
    every `V` (`consistent_all`).
-/
namespace PM
open QF

/-- A family in which (ι)/1, the predicative functions of individuals, is empty. (Written with
    `casesOn`: the equation compiler's version of this match uses `propext`.) -/
def Vbad (τ : Ty) : Type :=
  Ty.casesOn (motive := fun _ => Type) τ Unit
    (fun a k => Ty.casesOn (motive := fun _ => Type) a
      (Nat.casesOn (motive := fun _ => Type) k Empty fun _ => Unit) (fun _ _ => Unit) (fun _ _ _ => Unit))
    (fun _ _ _ => Unit)

/-- At `Vbad` every formula is a theorem. -/
theorem trap_empty (p : QF Vbad) : QThm p :=
  let φ : Vbad .ind → QF Vbad := fun x => .atom "q" [x]
  have h1 := q12_1 φ                                                       -- (∃f) : qx ≡ₓ f!x
  have h2 : QThm (V := Vbad) (.all (τ := Ty.pred1 .ind) fun f =>
      .neg (fiff φ fun x => .app1 f x)) := QThm.gen fun f => nomatch f    -- ✱10·11, vacuously
  QThm.mp h2 (QThm.mp h1 (QL.t2_21 _ p))

/-- `a ≡ b . ⊃ : ∼a ≡ b . ⊃ . p`, a tautology (by the completeness theorem; this is a metatheorem). -/
private def glue : F :=
  F.imp (F.iff (.var "a") (.var "b")) (F.imp (F.iff (F.neg (.var "a")) (.var "b")) (.var "p"))

private theorem glue_thm : Thm glue := complete _ (by decide)

/-- At the one-element family `U` every formula is a theorem. -/
theorem trap_unit (p : QF U) : QThm p :=
  let q : QF U := .atom "q" [()]
  let A : QF U := .app1 (a := .ind) (k := 0) () ()
  -- from (∃f) . P f, P () (every f is ()): ✱10·11 and ✱10·23
  have elim : ∀ P : U (Ty.pred1 .ind) → QF U, QThm (ex P) → QThm (P ()) := fun P h =>
    QThm.mp h (qiffMp (q10_23 P (P ())) |> QThm.mp (q10_11 fun f => QL.t2_08 (P f)))
  have h1 : QThm (iff q A) := QThm.mp (elim _ (q12_1 fun x => .atom "q" [x]))
    (q10_1 (V := U) (fun x => iff (.atom "q" [x]) (.app1 (a := .ind) (k := 0) () x)) ())
  have h2 : QThm (iff (.neg q) A) := QThm.mp (elim _ (q12_1 fun x => .neg (.atom "q" [x])))
    (q10_1 (V := U) (fun x => iff (.neg (.atom "q" [x])) (.app1 (a := .ind) (k := 0) () x)) ())
  QThm.mp h2 (QThm.mp h1 (liftThm glue_thm fun s => if s = "a" then q else if s = "b" then A else p))

end PM
