import PM.Star22
/-!
  ✱24: the universal class, the null-class, and the existence of classes (1910 print; numbered items
  pp. 231–240, after the number's summary, pp. 229–230). The print has 73 numbered items: the
  definitions ✱24·01–✱24·03 (p. 231) and 70 propositions, ✱24·1 to ✱24·63.

  The definitions are macros (`@[reducible]`), like ✱20·01 and ✱22·01–✱22·05 (docs/TYPES_DESIGN.md
  decision 9). A class is written by its defining function (PM/Star20.lean), so V, which PM defines as the
  class x̂(x = x), is the function x ↦ x = x, and Λ = −V is ✱22·04's x ↦ x ∼∈ V. ∃!α is a proposition about
  the class α, its definiens with x ∈ α eliminated where it stands (`clsMem x α`, ✱20·01 with the smallest
  scope):
    ✱24·01  V = x̂(x = x)                   Df   (`QF.clsUniv`, `𝐕`)
    ✱24·02  Λ = −V                          Df   (`QF.clsEmpty`, `Λ`)
    ✱24·03  ∃!α . = . (∃x) . x ∈ α          Df   (`QF.clsNonempty α`)
  V and Λ are "ambiguous as to type" (p. 229), like Cls (✱20·03): the type `a` of their members is
  implicit, fixed by the context. ∃!α, "α exists", is not E! of ✱14·02 (p. 229: "This sense of 'existence'
  must not be confused with that defined in ✱14·02").

  Notation (scoped to `PM`): `Λ` is PM's sign. V cannot be a token, since `V` names the variable family of
  every file (`V : Ty → Type`), so it is the bold `𝐕`; and PM's ∃! is not used as a token, since `∃!` is
  Lean's unique existence, so ∃!α is written `clsNonempty α`.
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱24·01 `V = x̂(x = x)` Df: the class whose defining function is x = x (✱13·01). -/
@[reducible] def clsUniv {a : Ty} : V a → QF V := fun x => ident x x
/-- ✱24·02 `Λ = −V` Df -/
@[reducible] def clsEmpty {a : Ty} : V a → QF V := clsCompl clsUniv
/-- ✱24·03 `∃!α . = . (∃x) . x ∈ α` Df -/
@[reducible] def clsNonempty {a : Ty} (α : V a → QF V) : QF V := ex fun x => clsMem x α
end QF

/-! The notations of ✱24 (scoped to `PM`, like those of ✱22): `𝐕` for V (✱24·01) and `Λ` for Λ (✱24·02).
    Each unfolds to the definition it names. -/
/-- `𝐕`: `clsUniv` (✱24·01), PM's V. -/
scoped notation "𝐕" => QF.clsUniv
/-- `Λ`: `clsEmpty` (✱24·02). -/
scoped notation "Λ" => QF.clsEmpty

variable {V : Ty → Type} {S : Sys} {a : Ty}

/-! Checks of the notation: each statement is the definition it names. -/
example : (𝐕 : V a → QF V) = fun x => ident x x := rfl
example : (Λ : V a → QF V) = −𝐕 := rfl
example : (Λ : V a → QF V) = fun x => QF.neg (x ∈ 𝐕) := rfl
example (α : V a → QF V) : clsNonempty α = ex fun x => x ∈ α := rfl

end PM
