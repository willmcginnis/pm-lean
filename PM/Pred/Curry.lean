import PM.Orders
import PM.Pred.Matrix
/-!
  Partial application and p. 56's second clause (Will, 2026-10-11 evening, items (ii) and (iii);
  docs/TYPES_DESIGN.md, decisions 3 and 5, questions Q3 and Q4).

  (ii) Currying. φ!x can be seen as a function of the two arguments φ and x, of order 2 (p. 54, p. 170:
  "It will be seen that "φ!x" is a function of two variables, namely φ!ẑ and x"), or, with φ fixed, as a
  function of x alone, which is predicative (p. 55: "if f!(φ!ẑ, x) is φ!x, the assignment of a value to
  φ gives us a predicative function of x"). Will's framing: the same body seen as a two-parameter
  function and as a one-parameter closure, "syntactic sugar"? `curry_order` makes it a checked fact:
  the order of the two-argument function is the larger of the first argument's lowest compatible order
  and the order of the partial application. So the p. 55 reading of a real variable (its own order) is
  exactly partial application, and the golden tests below are PM's examples.

  (iii) p. 56's second clause: "A function of several arguments is predicative if there is one of its
  arguments such that, when the other arguments have values assigned to them, we obtain a predicative
  function of the one undetermined argument." SEARCH for a case in our types where it disagrees with
  the lowest-order rule stated just before it ("if it is of the lowest order compatible with its having
  the arguments it has"). Result: WITHIN THIS ENCODING there is none. `second_clause_iff_lowestOrder`
  proves it for every two-argument body over `U`, and `anyLe_iff_le_maxL` states the same arithmetic
  for any number of arguments. The encoding: "the other arguments have values assigned to them" is
  read as evaluating both partial applications at `()` in the one-element family `U`, so both have the
  same body order O, and the order of the function of argument i, the others fixed, is max (oᵢ + 1) O
  (`fnOrder`). The equivalence then reduces to arithmetic: O ≤ a + 1 ∨ O ≤ b + 1 ↔ O ≤ max a b + 1, i.e.
  the lowest-order rule. ClauseSearch.lean compares the same definitions on enumerated formulas and
  finds no disagreement. This is a fact about this encoding; it does not independently show that the
  encoding captures PM's "assignment of values", nor does it extend to arbitrary variable families. So
  the clause is not added as a style, since within this encoding it would admit the same functions.

  Orders are computed at the one-element family `U`, as in PM/Orders.lean (exact for formulas written
  uniformly in the variable family).
-/
namespace PM

/-- The order of the two-argument function (x̂, ŷ) ↦ ψ(x, y) whose arguments have types `a`, `b`
    (Introduction p. 56: one above the highest order of the arguments, or the order of the body). -/
def fnOrder2 (a b : Ty) (ψ : U a → U b → QF U) : Nat := max (max a.ord b.ord + 1) (ψ () ()).order

private theorem succ_max_le {x y c : Nat} (h1 : x + 1 ≤ c) (h2 : y + 1 ≤ c) : max x y + 1 ≤ c := by
  show (if x ≤ y then y else x) + 1 ≤ c
  split <;> assumption

private theorem max_curry (x y o : Nat) : max (max x y + 1) o = max (x + 1) (max (y + 1) o) :=
  Nat.le_antisymm
    (max_le' (succ_max_le (le_max_left' _ _)
        (Nat.le_trans (le_max_left' _ o) (le_max_right' _ _)))
      (Nat.le_trans (le_max_right' (y + 1) o) (le_max_right' _ _)))
    (max_le' (Nat.le_trans (Nat.succ_le_succ (le_max_left' x y)) (le_max_left' _ _))
      (max_le' (Nat.le_trans (Nat.succ_le_succ (le_max_right' x y)) (le_max_left' _ _))
        (le_max_right' _ _)))

/-- **Currying.** The order of ψ as a function of (φ, x) is the larger of φ's lowest compatible order and
    the order of the partial application x̂ ↦ ψ(φ, x) with φ fixed (φ counted at its own order, p. 55). -/
theorem curry_order (a b : Ty) (ψ : U a → U b → QF U) :
    fnOrder2 a b ψ = max (a.ord + 1) (fnOrder b (ψ ())) :=
  max_curry a.ord b.ord _

/-! Golden tests of the two views (pp. 54, 55, 170). `()` is the fixed φ. -/

/-- The two views of φ!x agree with PM: as a function of (φ!ẑ, x) it has order 2 (pp. 54, 170), and
    partially applied at a fixed φ it is a predicative function of x (p. 55), with `curry_order` linking
    the two: 2 = max (1 + 1) 1. -/
theorem phi_x_two_views :
    fnOrder2 (Ty.pred1 .ind) .ind (fun φ x => .app1 φ x) = 2 ∧
    predicativeP56 .ind ((fun (φ : U (Ty.pred1 .ind)) (x : U .ind) => QF.app1 φ x) ()) = true :=
  ⟨rfl, rfl⟩

/-- φ!x as a function of (φ!ẑ, x): order 2 (pp. 54, 170). -/
example : fnOrder2 (Ty.pred1 .ind) .ind (fun φ x => .app1 φ x) = 2 := rfl
/-- φ!x with φ fixed, as a function of x: predicative, order 1 (p. 55). -/
example : fnOrder .ind ((fun (φ : U (Ty.pred1 .ind)) (x : U .ind) => QF.app1 φ x) ()) = 1 := rfl
/-- p. 55: "if f!(φ!ẑ, x) contains a first-order function as apparent variable, the assignment of a
    value to φ!ẑ gives us a second-order function of x": (ψ) . ψ!x ⊃ φ!x with φ fixed has order 2. -/
example : fnOrder .ind ((fun (φ : U (Ty.pred1 .ind)) (x : U .ind) =>
    QF.all (τ := Ty.pred1 .ind) fun ψ => QF.imp (.app1 ψ x) (.app1 φ x)) ()) = 2 := rfl
/-- … and as a function of (φ, x) it is also of order 2: currying does not lower it. -/
example : fnOrder2 (Ty.pred1 .ind) .ind (fun φ x =>
    QF.all (τ := Ty.pred1 .ind) fun ψ => QF.imp (.app1 ψ x) (.app1 φ x)) = 2 := rfl

/-! ## p. 56's second clause -/

/-- The clause for two arguments, in this encoding: fixing the second argument gives a predicative
    function of the first, or fixing the first gives a predicative function of the second (fixed
    arguments counted at their own order, p. 55). "Assigning a value" is evaluating at `()` in `U`, so
    both partial applications have the same body order. -/
def SecondClause (a b : Ty) (ψ : U a → U b → QF U) : Prop :=
  fnOrder a (fun x => ψ x ()) = a.ord + 1 ∨ fnOrder b (ψ ()) = b.ord + 1

/-- The lowest-order rule for two arguments (p. 56, the sentence before the clause). -/
def LowestOrder2 (a b : Ty) (ψ : U a → U b → QF U) : Prop :=
  fnOrder2 a b ψ = max a.ord b.ord + 1

private theorem max_eq_left_iff {x o : Nat} : max x o = x ↔ o ≤ x :=
  ⟨fun h => h ▸ le_max_right' x o, fun h => Nat.le_antisymm (max_le' (Nat.le_refl x) h) (le_max_left' x o)⟩

private theorem le_max_succ_iff {o x y : Nat} : o ≤ max x y + 1 ↔ o ≤ x + 1 ∨ o ≤ y + 1 := by
  constructor
  · intro h
    change o ≤ (if x ≤ y then y else x) + 1 at h
    split at h
    · exact Or.inr h
    · exact Or.inl h
  · intro h
    cases h with
    | inl h => exact Nat.le_trans h (Nat.succ_le_succ (le_max_left' x y))
    | inr h => exact Nat.le_trans h (Nat.succ_le_succ (le_max_right' x y))

/-- **No case exists within this encoding.** For every two-argument body over `U`, p. 56's second
    clause as encoded by `SecondClause` and the lowest-order rule agree. With O the body order, this is
    the arithmetic (O ≤ a.ord + 1 ∨ O ≤ b.ord + 1) ↔ O ≤ max a.ord b.ord + 1. It does not
    independently show that `SecondClause` captures PM's "assignment of values", nor extend to
    arbitrary variable families. -/
theorem second_clause_iff_lowestOrder (a b : Ty) (ψ : U a → U b → QF U) :
    SecondClause a b ψ ↔ LowestOrder2 a b ψ := by
  show (max (a.ord + 1) (ψ () ()).order = a.ord + 1 ∨ max (b.ord + 1) (ψ () ()).order = b.ord + 1) ↔
    max (max a.ord b.ord + 1) (ψ () ()).order = max a.ord b.ord + 1
  constructor
  · intro h
    apply max_eq_left_iff.mpr
    apply le_max_succ_iff.mpr
    cases h with
    | inl h => exact Or.inl (max_eq_left_iff.mp h)
    | inr h => exact Or.inr (max_eq_left_iff.mp h)
  · intro h
    cases le_max_succ_iff.mp (max_eq_left_iff.mp h) with
    | inl h => exact Or.inl (max_eq_left_iff.mpr h)
    | inr h => exact Or.inr (max_eq_left_iff.mpr h)

/-- The matrix reading of the clause (✱12): being a matrix does not depend on which argument is left
    undetermined, so the clause with "predicative" read as "matrix of the right order" is again the
    matrix test together with the lowest-order rule. -/
theorem second_clause_matrix_iff (a b : Ty) (ψ : U a → U b → QF U) :
    (IsMatrix (ψ () ()) ∧ SecondClause a b ψ) ↔ (IsMatrix (ψ () ()) ∧ LowestOrder2 a b ψ) :=
  ⟨fun ⟨m, h⟩ => ⟨m, (second_clause_iff_lowestOrder a b ψ).mp h⟩,
   fun ⟨m, h⟩ => ⟨m, (second_clause_iff_lowestOrder a b ψ).mpr h⟩⟩

/-! Any number of arguments, as a statement about orders: with argument orders o₀, o₁, … and one body
    order O shared by every partial application (as in the encoding above), "for some i, the function
    of argument i is of order oᵢ + 1" is "O ≤ oᵢ + 1 for some i" (`max_eq_left_iff`), and this is the
    lowest-order rule O ≤ max oᵢ + 1. A pure arithmetic fact; it carries the same encoding assumption. -/

/-- O ≤ oᵢ + 1 for some argument order oᵢ in o₀, o₁, …. -/
def anyLe (O : Nat) : Nat → List Nat → Prop
  | o, [] => O ≤ o + 1
  | o, p :: ps => O ≤ o + 1 ∨ anyLe O p ps

/-- The highest of o₀, o₁, …. -/
def maxL : Nat → List Nat → Nat
  | o, [] => o
  | o, p :: ps => max o (maxL p ps)

theorem anyLe_iff_le_maxL (O : Nat) : (o : Nat) → (os : List Nat) → (anyLe O o os ↔ O ≤ maxL o os + 1)
  | _, [] => Iff.rfl
  | _, p :: ps =>
    ⟨fun h => le_max_succ_iff.mpr (match h with
        | .inl h => .inl h
        | .inr h => .inr ((anyLe_iff_le_maxL O p ps).mp h)),
     fun h => match le_max_succ_iff.mp h with
        | .inl h => .inl h
        | .inr h => .inr ((anyLe_iff_le_maxL O p ps).mpr h)⟩

end PM
