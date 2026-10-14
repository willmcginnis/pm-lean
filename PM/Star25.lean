import PM.Star23
import PM.Star24
/-!
  ✱25: the universal relation, the null relation, and the existence of relations (1910 print, pp. 241–243;
  summary p. 241, numbered items pp. 241–243). The print has 73 numbered items: the definitions
  ✱25·01–✱25·03 (p. 241) and 70 propositions, ✱25·1 to ✱25·63, numbered as ✱24's.

  "This number contains the analogues, for relations, of the definitions and propositions of ✱24. Proofs
  will not be given, as they proceed precisely as in ✱24. […] The propositions of this number are much
  less often referred to than those of ✱24, but for the sake of uniformity we have given the analogues
  of all propositions in ✱24, with the same numeration (except for the integral part). All the remarks
  made in ✱24 apply, mutatis mutandis, in the present number" (p. 241).

  The definitions are macros (`@[reducible]`), like ✱23·01–✱23·05 and ✱24·01–✱24·03 (docs/TYPES_DESIGN.md
  decision 9). A relation is written by its defining function, a formula with two holes (PM/Star21.lean),
  so V̇, which PM defines as the relation x̂ŷ(x = x . y = y), is the function (x, y) ↦ x = x . y = y, and
  Λ̇ = ∸V̇ is ✱23·04's (x, y) ↦ ∼{x V̇ y}. ∃̇!R is a proposition about the relation R, its definiens with xRy
  eliminated where it stands (`relHolds x R y`, ✱21·02 with ✱21·01, the smallest scope), and (∃x, y) the
  two-variable quantifier of ✱11·03:
    ✱25·01  V̇ = x̂ŷ(x = x . y = y)            Df   (`QF.relUniv`, `𝐕̇`)
    ✱25·02  Λ̇ = ∸V̇                           Df   (`QF.relEmpty`, `Λ̇`)
    ✱25·03  ∃̇!R . = . (∃x, y) . xRy          Df   (`QF.relNonempty R`)
  V̇ and Λ̇ are ambiguous as to type, like V and Λ: "the relation which holds between any two terms
  whatever of the appropriate types, whatever these may be in the given context" (p. 241). The types `a`,
  `b` of their domain and converse domain are implicit, fixed by the context.

  Notation (scoped to `PM`): `Λ̇` is PM's sign. V̇ is the bold `𝐕̇`, as ✱24's V is `𝐕` (`V` names the variable
  family of every file); PM's ∃̇! is not used as a token, as ∃! is not in ✱24, so ∃̇!R is `relNonempty R`.

  Names: `q25_1` is ✱25·1, and so on. P, Q, R, S, R', S' are relations, as in PM; as in PM/Star23.lean,
  the system of rules is `S`, so PM's relation S is written `S'` in Lean statements, and PM's S' is `S''`;
  the docstrings keep PM's letters. κ is a class of relations (✱25·63).
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱25·01 `V̇ = x̂ŷ(x = x . y = y)` Df: the relation whose defining function is x = x . y = y (✱13·01,
    ✱3·01). -/
@[reducible] def relUniv {a b : Ty} : V a → V b → QF V := fun x y => QF.and (ident x x) (ident y y)
/-- ✱25·02 `Λ̇ = ∸V̇` Df -/
@[reducible] def relEmpty {a b : Ty} : V a → V b → QF V := relCompl relUniv
/-- ✱25·03 `∃̇!R . = . (∃x, y) . xRy` Df -/
@[reducible] def relNonempty {a b : Ty} (R : V a → V b → QF V) : QF V := ex2 fun x y => relHolds x R y
end QF

/-! The notations of ✱25 (scoped to `PM`, like those of ✱23 and ✱24): `𝐕̇` for V̇ (✱25·01) and `Λ̇` for Λ̇
    (✱25·02). Each unfolds to the definition it names. -/
/-- `𝐕̇`: `relUniv` (✱25·01), PM's V̇. -/
scoped notation "𝐕̇" => QF.relUniv
/-- `Λ̇`: `relEmpty` (✱25·02). -/
scoped notation "Λ̇" => QF.relEmpty

variable {V : Ty → Type} {S : Sys} {a b : Ty}

/-! Checks of the notation: each statement is the definition it names. -/
example : (𝐕̇ : V a → V b → QF V) = fun x y => QF.and (ident x x) (ident y y) := rfl
example : (Λ̇ : V a → V b → QF V) = ∸𝐕̇ := rfl
example : (Λ̇ : V a → V b → QF V) = fun x y => QF.neg (relHolds x 𝐕̇ y) := rfl
example (R : V a → V b → QF V) : relNonempty R = ex2 fun x y => relHolds x R y := rfl
/-! ✱24's signs and ✱25's are read apart: Λ and 𝐕 are classes, Λ̇ and 𝐕̇ relations. -/
example : (Λ : V a → QF V) = clsEmpty ∧ (Λ̇ : V a → V b → QF V) = relEmpty := ⟨rfl, rfl⟩
example : (𝐕 : V a → QF V) = clsUniv ∧ (𝐕̇ : V a → V b → QF V) = relUniv := ⟨rfl, rfl⟩

end PM
