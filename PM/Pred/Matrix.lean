import PM.Quant
/-!
  "Predicative" as "matrix" (✱12, p. 172), as a style of comprehension: the PRIMARY style
  (Will, 2026-10-11, open question Q1: both readings, the matrix one primary as the more elegant;
  docs/TYPES_DESIGN.md, decision 3).

  ✱12 p. 172: "A function is said to be *predicative* when it is a matrix", and "'Matrix' or
  'predicative function' is a primitive idea"; p. 169: "Let us give the name of *matrix* to any
  function, of however many variables, which does not involve any apparent variables". p. 171: "A
  second-order matrix of one variable will be called a predicative second-order function of one
  variable or a predicative function of a first-order matrix".

  In this style comprehension at a predicative type (`fn1 a 0`, `fn2 a b 0`) accepts only matrices,
  and only of the right order: the matrix test is CONJOINED with the order check (after an external
  review), not put in its place. At non-predicative types (k > 0) it accepts what the order check accepts, as in the
  lowest-order style (PM/Pred/LowestOrder.lean, the alternative). The order check `L` is the reading of
  how real function variables count (PM/Pred/RealOwnOrder.lean, p. 55; PM/Pred/RealAsArgument.lean,
  p. 54).

  The types `pred1 a`, `pred2 a b` are the same in both styles: the values of predicative functions
  form a range that apparent variables run over. The style decides only which formulas comprehension
  turns into such a value without ✱12·1.
-/
namespace PM

/-- A matrix: a formula with no apparent variable (p. 169). Real variables, of any type, may occur. -/
inductive IsMatrix {V : Ty → Type} : QF V → Prop where
  | atom {P : String} {xs : List (V .ind)} : IsMatrix (.atom P xs)
  | app1 {a : Ty} {k : Nat} {f : V (.fn1 a k)} {x : V a} : IsMatrix (.app1 f x)
  | app2 {a b : Ty} {k : Nat} {f : V (.fn2 a b k)} {x : V a} {y : V b} : IsMatrix (.app2 f x y)
  | neg {p : QF V} : IsMatrix p → IsMatrix (.neg p)
  | or {p q : QF V} : IsMatrix p → IsMatrix q → IsMatrix (.or p q)

/-- Comprehension accepts ψ at `fn1 a k` when every value of ψ passes the order check at the order of
    that type and, if the type is predicative (k = 0), is a matrix. Likewise for `fn2 a b k`. -/
def Style.matrix (L : OrderCheck) : Style where
  adm1 := fun {_ a} k ψ => ∀ x, L (ψ x) (Ty.fn1 a k).ord ∧ (k = 0 → IsMatrix (ψ x))
  adm2 := fun {_ a b} k ψ => ∀ x y, L (ψ x y) (Ty.fn2 a b k).ord ∧ (k = 0 → IsMatrix (ψ x y))

end PM
