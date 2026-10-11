import PM.Quant
/-!
  The order check `Lvl`, reading p. 55: a real function variable counts with its own order
  (docs/TYPES_DESIGN.md, decision 5).

  Introduction p. 56: "If the highest order of variable occurring in a function, whether as argument or
  as apparent variable, is a function of the nth order, then the function in which it occurs is of the
  n + 1th order". p. 55: "if f!(φ!ẑ, x) is φ!x, the assignment of a value to φ gives us a predicative
  function of x". So a real (free) function variable φ in a formula counts with its own order m, not
  m + 1: with φ fixed, φ!x is a predicative function of x.

  The other reading (p. 54: φ counts as an argument, so φ!x is of order 2) is
  PM/Pred/RealAsArgument.lean.
-/
namespace PM

/-- `Lvl p n`: p may be a value of a function of order n. Each apparent variable has order below n,
    and each function variable applied in p has order at most n: a real variable counts with its own
    order (p. 55). Individuals have order 0, so every formula needs n ≥ 1. -/
inductive Lvl {V : Ty → Type} : QF V → Nat → Prop where
  | atom {P : String} {xs : List (V .ind)} {n : Nat} : 0 < n → Lvl (.atom P xs) n
  | app1 {a : Ty} {k n : Nat} {f : V (.fn1 a k)} {x : V a} : (Ty.fn1 a k).ord ≤ n → Lvl (.app1 f x) n
  | app2 {a b : Ty} {k n : Nat} {f : V (.fn2 a b k)} {x : V a} {y : V b} :
      (Ty.fn2 a b k).ord ≤ n → Lvl (.app2 f x y) n
  | neg {p : QF V} {n : Nat} : Lvl p n → Lvl (.neg p) n
  | or {p q : QF V} {n : Nat} : Lvl p n → Lvl q n → Lvl (.or p q) n
  | all {τ : Ty} {n : Nat} {φ : V τ → QF V} : τ.ord < n → (∀ y, Lvl (φ y) n) → Lvl (.all φ) n

end PM
