import PM.Quant
/-!
  "Predicative" as the lowest order compatible with the arguments (Introduction p. 56), as a style of
  comprehension (docs/TYPES_DESIGN.md, decision 3).

  Introduction p. 56: "We will define a function of one variable as *predicative* when it is of the next
  order above that of its argument, i.e. of the lowest order compatible with its having that argument."
  p. 174 agrees in substance: "for higher types of arguments, predicative functions take the place that
  first-order functions take in respect of individuals".

  In this style comprehension at `fn1 a k` accepts every formula of order at most that of `fn1 a k`;
  at a predicative type (k = 0) that is the lowest order compatible with the argument. The order check
  `L` is the reading of how real function variables count (PM/Pred/RealOwnOrder.lean, p. 55;
  PM/Pred/RealAsArgument.lean, p. 54).

  This is the alternative style. The primary style is the matrix reading (PM/Pred/Matrix.lean).
-/
namespace PM

/-- Comprehension accepts ψ at `fn1 a k` (`fn2 a b k`) when every value of ψ passes the order check
    at the order of that type. -/
def Style.lowestOrder {V : Ty → Type} (L : OrderCheck) : Style V where
  adm1 := fun {a} k ψ => ∀ x, L (ψ x) (Ty.fn1 a k).ord
  adm2 := fun {a b} k ψ => ∀ x y, L (ψ x y) (Ty.fn2 a b k).ord

end PM
