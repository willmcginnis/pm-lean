import PM.Quant
/-!
  ✱9's own method (pp. 127–143): the syntax.

  In ✱9 the letters p, q and φx stand for *elementary* propositions, which contain no apparent variable
  (p. 134). (x) . φx and (∃x) . φx are primitive ideas; negation and disjunction of propositions that
  contain apparent variables are not primitive but *defined*, by ✱9·01–✱9·08, so that "the true scope of
  an apparent variable is always the whole of the asserted proposition" (p. 136).

  Representation.
  - `EF V`: elementary formulas over the family `V : Ty → Type` of variables of PM/Quant.lean: a
    predicate letter applied to individual variables (`atom`), a function variable applied to arguments
    (`app1`, `app2`), and the primitive ideas ∼ and ∨ of ✱1 (p. 134: "the primitive ideas and propositions
    of ✱1 as applied to elementary propositions").
  - `PF V`: the propositions of ✱9: an elementary proposition (`el`), (x) . φx (`all`), or (∃x) . φx
    (`ex`), where `φ : V τ → PF V` is a function, as in PM/Quant.lean (higher-order abstract syntax).
    Both quantifiers are primitive. Since φx may itself be (y) . ψ(x, y) or (∃y) . ψ(x, y), a `PF` is a
    prefix of quantifiers in front of an elementary matrix: PM's "(x) : (∃y) . φx ∨ ψy" (✱9·07).
  - `PF.neg` and `PF.or` compute ✱9·01–✱9·08: the definitions move every quantifier to the front.
    Implication, the logical product and equivalence are "transferred unchanged" (p. 136): ✱1·01, ✱3·01
    and ✱4·01 as macros over `PF.neg`, `PF.or`.

  The order of the quantifiers moved to the front. ✱9·03–✱9·08 fix it when one side is elementary or
  each side has one apparent variable; ✱9·07 and ✱9·08 put the universal quantifier first, and PM
  adds: "(The definitions ✱9·07·08 are to apply also when φ and ψ are not both elementary.)" (p. 136).
  For longer prefixes PM says only that "the above definitions can be repeated for successive types"
  (p. 136). `PF.or` repeats them one quantifier at a time, outermost first:
  - a universal quantifier at the front of the left side comes out first (✱9·03, ✱9·07);
  - otherwise a universal quantifier at the front of the right side (✱9·04, ✱9·08);
  - otherwise an existential quantifier at the front of the left side (✱9·05), then of the right
    (✱9·06).
  Two readings of PM's repetition would give different orders: with p = (y) . ψy, ✱9·06 read for this p
  gives "p . ∨ . (∃x) . φx : = . (∃x) : (y) . ψy ∨ φx", while ✱9·07 gives "(y) : (∃x) . ψy ∨ φx". PM's
  note on ✱9·07·08 settles this case for ✱9·07, and `PF.or` follows it: a universal quantifier at the
  front of either side always precedes an existential one. The two orders are equivalent in every
  structure with at least one individual (the quantified variables are distinct and each occurs on one
  side only), but in ✱9 they are different propositions.

  ✱9·14 and ✱9·15 (significance and types, p. 138) are built into the syntax, as in PM/Quant.lean:
  every `φ : V τ → PF V` is a function, and `φ a` with `a : V τ` is a proposition. ✱9·131 (being of the
  same type) is Lean's typing of `V τ`; ✱9·6–✱9·63 are therefore not stated.

  Translations to and from the formulas `QF V` of ✱10's method (PM/Quant.lean): `PF.toQ` writes a ✱9
  proposition with ✱10's primitive ideas ((∃x) . φx as ∼(x) . ∼φx, ✱10·01); `QF.toF9` computes the ✱9
  proposition for which a ✱10 formula stands, reading ∼ and ∨ by ✱9·01–✱9·08.
-/
namespace PM.F9

/-- Elementary formulas (no apparent variable). -/
inductive EF (V : Ty → Type) where
  | atom : String → List (V .ind) → EF V
  | app1 {a : Ty} {k : Nat} : V (.fn1 a k) → V a → EF V
  | app2 {a b : Ty} {k : Nat} : V (.fn2 a b k) → V a → V b → EF V
  | neg  : EF V → EF V
  | or   : EF V → EF V → EF V

namespace EF
variable {V : Ty → Type}
@[reducible] def imp (p q : EF V) : EF V := .or (.neg p) q                    -- ✱1·01
@[reducible] def and (p q : EF V) : EF V := .neg (.or (.neg p) (.neg q))      -- ✱3·01
@[reducible] def iff (p q : EF V) : EF V := EF.and (EF.imp p q) (EF.imp q p)  -- ✱4·01
end EF

/-- The propositions of ✱9: elementary, or (x) . φx, or (∃x) . φx. -/
inductive PF (V : Ty → Type) where
  | el  : EF V → PF V
  | all {τ : Ty} : (V τ → PF V) → PF V
  | ex  {τ : Ty} : (V τ → PF V) → PF V

namespace PF
variable {V : Ty → Type}

/-- Negation (✱9·01, ✱9·02; ✱9·011, ✱9·021 only drop braces): ∼{(x) . φx} . = . (∃x) . ∼φx and
    ∼{(∃x) . φx} . = . (x) . ∼φx; on an elementary proposition, ✱1's primitive ∼. -/
def neg : PF V → PF V
  | .el e  => .el (.neg e)
  | .all φ => .ex fun x => (φ x).neg
  | .ex φ  => .all fun x => (φ x).neg

/-- p ∨ q for an elementary p: ✱9·04 and ✱9·06; ✱1's primitive ∨ if q is elementary too. -/
def orEl (a : EF V) : PF V → PF V
  | .el b  => .el (.or a b)
  | .all ψ => .all fun y => orEl a (ψ y)    -- ✱9·04
  | .ex ψ  => .ex fun y => orEl a (ψ y)     -- ✱9·06

/-- (∃x) . φx . ∨ . q, given `r x q` = φx ∨ q: ✱9·08 if q begins with a universal quantifier, else
    ✱9·05. -/
def orEx {τ : Ty} (r : V τ → PF V → PF V) : PF V → PF V
  | .all ψ => .all fun y => orEx r (ψ y)    -- ✱9·08
  | .el b  => .ex fun x => r x (.el b)      -- ✱9·05
  | .ex ψ  => .ex fun x => r x (.ex ψ)      -- ✱9·05, repeated

/-- Disjunction (✱9·03–✱9·08, repeated for longer prefixes; see the module note). -/
def or : PF V → PF V → PF V
  | .el a, q  => orEl a q
  | .all φ, q => .all fun x => or (φ x) q                -- ✱9·03, ✱9·07
  | .ex φ, q  => orEx (fun x q' => or (φ x) q') q        -- ✱9·05, ✱9·08

@[reducible] def imp (p q : PF V) : PF V := PF.or (PF.neg p) q                    -- ✱1·01
@[reducible] def and (p q : PF V) : PF V := PF.neg (PF.or (PF.neg p) (PF.neg q))  -- ✱3·01
@[reducible] def iff (p q : PF V) : PF V := PF.and (PF.imp p q) (PF.imp q p)      -- ✱4·01

example (a b : EF V) : PF.or (.el a) (.el b) = .el (.or a b) := rfl
example {τ : Ty} (φ : V τ → PF V) (q : PF V) : PF.or (.all φ) q = .all fun x => PF.or (φ x) q := rfl
example {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.or (.ex φ) (.all ψ) = .all fun y => PF.or (.ex φ) (ψ y) := rfl
example {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.or (.ex φ) (.ex ψ) = .ex fun x => PF.or (φ x) (.ex ψ) := rfl

end PF

/-! ## Translations between ✱9's and ✱10's formulas -/

/-- An elementary formula is a formula of ✱10 with the same primitive ideas. -/
def EF.toQ {V : Ty → Type} : EF V → QF V
  | .atom P xs   => .atom P xs
  | .app1 f x    => .app1 f x
  | .app2 f x y  => .app2 f x y
  | .neg e       => .neg e.toQ
  | .or e₁ e₂    => .or e₁.toQ e₂.toQ

/-- A ✱9 proposition written with ✱10's primitive ideas: (∃x) . φx becomes ∼(x) . ∼φx (✱10·01). -/
def PF.toQ {V : Ty → Type} : PF V → QF V
  | .el e  => e.toQ
  | .all φ => .all fun x => (φ x).toQ
  | .ex φ  => QF.ex fun x => (φ x).toQ

/-- The ✱9 proposition for which a ✱10 formula stands: ∼ and ∨ are read by ✱9·01–✱9·08. -/
def _root_.PM.QF.toF9 {V : Ty → Type} : QF V → PF V
  | .atom P xs   => .el (.atom P xs)
  | .app1 f x    => .el (.app1 f x)
  | .app2 f x y  => .el (.app2 f x y)
  | .neg p       => PF.neg p.toF9
  | .or p q      => PF.or p.toF9 q.toF9
  | .all φ       => .all fun x => (φ x).toF9

end PM.F9
