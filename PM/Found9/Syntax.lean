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
  - `PF.neg` and the disjunctions compute ✱9·01–✱9·08: the definitions move every quantifier to the
    front. Implication, the logical product and equivalence are "transferred unchanged" (p. 136): ✱1·01,
    ✱3·01 and ✱4·01 as macros over `PF.neg` and a disjunction (`PF.imp`, `Reading.imp`, …).

  The definitions of disjunction, as printed (pp. 135–136):
    "To define disjunction when one or both of the propositions concerned is of the first order, we
    have to distinguish six cases, as follows:
    ✱9·03. (x) . φx . ∨ . p : = . (x) . φx ∨ p   Df
    ✱9·04. p . ∨ . (x) . φx : = . (x) . p ∨ φx   Df
    ✱9·05. (∃x) . φx . ∨ . p : = . (∃x) . φx ∨ p   Df
    ✱9·06. p . ∨ . (∃x) . φx : = . (∃x) . p ∨ φx   Df
    ✱9·07. (x) . φx . ∨ . (∃y) . ψy : = : (x) : (∃y) . φx ∨ ψy   Df
    ✱9·08. (∃y) . ψy . ∨ . (x) . φx : = : (x) : (∃y) . ψy ∨ φx   Df
    (The definitions ✱9·07·08 are to apply also when φ and ψ are not both elementary functions.)"
  and, after the definitions of implication, product and equivalence: "The above definitions can be
  repeated for successive types, and thus reach propositions of any type." (p. 136)

  Two quantifiers of the same kind. The ✱9 text prints no definition of "(x) . φx . ∨ . (y) . ψy" or
  "(∃x) . φx . ∨ . (∃y) . ψy", but the Introduction does, for elementary φ and ψ (1910 p. 49; second
  edition p. 47; quoted from our transcription of a scan of the 1910 edition): "Similarly we can
  define a disjunction of two universal propositions: "(x) . φx . ∨ . (y) . ψy" will be defined as
  meaning "(x, y) . φx ∨ ψy"". PM's proofs read both cases with the left side's quantifier first:
  the last lines of ✱9·3 read "(x) : φx . ∨ . (y) . φy" as "(x) . φx . ∨ . (y) . φy" [(✱9·03)], and
  those of ✱9·31 read "(∃x) : (∃y) . φx ∨ φy" as "(∃x) . φx . ∨ . (∃y) . φy" [(✱9·05·06)] (p. 140).
  And ✱8 of the second edition (1925, Vol. I, Appendix A, p. 635, page image), which replaces ✱9,
  states the order as a rule: "When the stroke occurs between two propositions which are both of the
  first order, we shall adopt the rule that the above definitions are to be applied first to the one
  on the left, treating the one on the right as if it were elementary, and are then to be applied to
  the one on the right."

  Four readings, all kept (docs/REPAIRS.md; docs/STAR9_READINGS.md):
  - **As printed** (reading A, `PF.orPrinted`): the equations applied to the outermost quantifier of
    each side, and the disjunction left on the right-hand side (φx ∨ p, φx ∨ ψy, …) computed by the same
    definitions. With (x) . φx on one side and (∃y) . ψy on the other, ✱9·07 or ✱9·08 takes out both,
    the universal first, "also when φ and ψ are not both elementary": with φx = (z) . R(x, z) and
    ψy = S(y), "(x) . φx . ∨ . (∃y) . ψy" is (x) : (∃y) : (z) . R(x, z) ∨ S(y). Two quantifiers of the
    same kind: ✱9·03 or ✱9·05 applied with p the other side, treated as if elementary, so the left
    side's quantifier comes out first: PM's last lines of ✱9·3 and ✱9·31, the Introduction for two
    universal quantifiers (1910 p. 49; second edition p. 47), and ✱8's rule quoted above
    (docs/REPAIRS.md, R2). Under it, the step (3)–(4) of PM's proof of ✱9·31, "[(3).(✱9·03·02)]",
    which reads ✱9·03 with p = (∃z) . φz, is not a definitional rewrite (PM/Found9/Star9.lean,
    `f9_31_step`).
  - **As printed + ✱8·13** (reading C, `Reading.russell`, the working reading and the default): the
    same definitions (`PF.orPrinted`) and Russell's rule ✱8·13 of the second edition carried over to
    ✱9 (`ExchStep`, PM/Found9/System.lean; docs/REPAIRS.md, R1). It takes the step (3)–(4) of ✱9·31.
  - **✱9+** (reading L, `PF.orPlus`, `Reading.withSwitch`; Landini's repair (2000), a published
    variant, cross-check): Landini's repaired system (G. Landini, "Quantification Theory in ✱9 of
    *Principia Mathematica*", *History and Philosophy of Logic* 21 (2000) 57–77, p. 64): ✱9·01–✱9·08 as
    printed, with ✱9·03–✱9·06 for a p without apparent variables only, and two definitions for two
    quantifiers of the same kind, taken out together like ✱9·07·08: "✱9·yy (x)Ax ∨ (y)By = df
    (x)(y)(Ax ∨ By)" (anticipated by PM, Introduction, 1910 p. 49; second edition p. 47) and
    "✱9·zz (∃x)Ax ∨ (∃y)By = df (∃x)(∃y)(Ax ∨ By)" (Landini's). L adds Landini's rule Switch
    (PM/Found9/System.lean); under its definitions too the step (3)–(4) of ✱9·31 is not a definitional
    rewrite, and Switch takes it.
  - **The alternative convention** (reading B, `PF.or`; a cross-check, not the default): to write
    p ∨ q with its quantifiers in front, take them out one at a time from the front of p or of q,
    keeping each side's own order: a universal quantifier before an existential one, and of two of the
    same kind, the one in p first. It is a precedence convention of our own, read off the order PM's
    proofs use (✱9·31, line (4); the last lines of ✱9·3 and ✱9·31); every step of ✱9's proofs that PM
    justifies by definitions is a definitional rewrite under it. It departs from the note on ✱9·07·08
    for a function with an apparent variable: the example above is (x) : (z) : (∃y) here. It is kept
    to show that the ambiguity at ✱9·31 is real (a second, independent repair also makes PM's proof go
    through) and as a check that the repairs change nothing else.
  All their definitions agree when one side is elementary or each side has one apparent variable.

  A `Reading` (below) is a choice of definitions and of the rule, if any, added to ✱9's primitive
  propositions: `Reading.printed` (A), `Reading.russell` (C, with ✱8·13), `Reading.withSwitch` (L, ✱9+,
  whose Switch comes with its definitions), `Reading.convention` (B), and `Reading.prenexSwitch` (the
  definitions as printed with the prenex Switch, an earlier repair kept for comparison). The orders that
  the definitions give are equivalent in every structure with at least one individual (the quantified
  variables are distinct and each occurs on one side only), but in ✱9 they are different propositions.
  `PE`, `Merge` and `Prenex` describe the propositions that the definitions could make of an expression
  PM prints, which the prenex Switch passes between; `Sep` describes the side condition of ✱8·13 and of
  Landini's Switch, `ExchStep` and `SwitchStep` their steps.

  ✱9·14 and ✱9·15 (significance and types, p. 138) are built into the syntax, as in PM/Quant.lean:
  every `φ : V τ → PF V` is a function, and `φ a` with `a : V τ` is a proposition. ✱9·131 (being of the
  same type) is Lean's typing of `V τ`; ✱9·6–✱9·63 are therefore not stated.

  Translations to and from the formulas `QF V` of ✱10's method (PM/Quant.lean): `PF.toQ` writes a ✱9
  proposition with ✱10's primitive ideas ((∃x) . φx as ∼(x) . ∼φx, ✱10·01); `QF.toF9 d` computes the ✱9
  proposition for which a ✱10 formula stands, reading ∼ and ∨ by ✱9·01–✱9·08 under the definitions d.
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

/-- Disjunction under the alternative convention (reading B, `docs/REPAIRS.md`, R4: a cross-check,
    not the default). The convention, as an order-of-operations rule: **to write p ∨ q with its
    quantifiers in front, take them out one at a time from the front of p or of q, keeping each side's
    own order: a universal quantifier before an existential one, and of two of the same kind, the one
    in p first.** It is a convention of our own, read off the order PM's own proofs use: line (4) of
    ✱9·31, "[(3).(✱9·03·02)]", and the last lines of ✱9·3 and ✱9·31 (p. 140). It agrees with the
    definitions as printed (`orPrinted`) when one side is elementary or each side has one apparent
    variable, and departs from the note on ✱9·07·08 when one of them is applied to a function with an
    apparent variable: for φx = (z) . R(x, z) and ψy = S(y), "(x) . φx . ∨ . (∃y) . ψy" is
    (x) : (z) : (∃y) here, (x) : (∃y) : (z) as printed. -/
def or : PF V → PF V → PF V
  | .el a, q  => orEl a q                                   -- ✱1, ✱9·04, ✱9·06
  | .all φ, q => .all fun x => or (φ x) q                   -- ✱9·03 (✱9·07): p's universal first
  | .ex φ, q  => orEx (fun x q' => or (φ x) q') q           -- ✱9·05, ✱9·08
where
  /-- (∃x) . φx . ∨ . q, given `r x q` = φx ∨ q: a universal quantifier at the front of q comes out
      first (✱9·08, ✱9·04), otherwise p's existential (✱9·05). -/
  orEx {τ : Ty} (r : V τ → PF V → PF V) : PF V → PF V
    | .all ψ => .all fun y => orEx r (ψ y)
    | .el b  => .ex fun x => r x (.el b)
    | .ex ψ  => .ex fun x => r x (.ex ψ)

/-- Disjunction **as printed** (readings A and C): ✱9·03–✱9·08 applied to the outermost quantifier of
    each side, with ✱9·07·08 "also when φ and ψ are not both elementary functions" (p. 136); for two
    quantifiers of the same kind, which the ✱9 text does not define, ✱9·03 or ✱9·05 with p the other
    side treated as if elementary, so the left side's quantifier first: as PM's last lines of ✱9·3 and
    ✱9·31 cite them, as the Introduction defines two universal ones (1910 p. 49; second edition
    p. 47), and as ✱8 of the second edition orders the elimination (p. 635, page image: "applied
    first to the one on the left, treating the one on the right as if it were elementary";
    docs/REPAIRS.md, R2). Kept, never deleted, so that what PM printed
    stays visible:
    under it the step (3)–(4) of PM's proof of ✱9·31 is not a definitional rewrite (`f9_31_step`). -/
def orPrinted : PF V → PF V → PF V
  | .el a, q        => orEl a q                                               -- ✱1, ✱9·04, ✱9·06
  | .all φ, .el b   => .all fun x => orPrinted (φ x) (.el b)                  -- ✱9·03
  | .all φ, .all ψ  => .all fun x => orPrinted (φ x) (.all ψ)                 -- ✱9·03 repeated (✱9·3)
  | .all φ, .ex ψ   => .all fun x => .ex fun y => orPrinted (φ x) (ψ y)       -- ✱9·07
  | .ex ψ, .el b    => .ex fun y => orPrinted (ψ y) (.el b)                   -- ✱9·05
  | .ex ψ, .ex χ    => .ex fun y => orPrinted (ψ y) (.ex χ)                   -- ✱9·05 repeated (✱9·31)
  | .ex ψ, .all φ   => .all fun x => .ex fun y => orPrinted (ψ y) (φ x)       -- ✱9·08

/-- Disjunction in **✱9+** (reading L; Landini 2000, p. 64): ✱9·03–✱9·06 for a side without apparent
    variables only (`orEl`, and the clauses with `.el b`), ✱9·07·08 as printed, and for two quantifiers
    of the same kind ✱9·yy "(x)Ax ∨ (y)By = df (x)(y)(Ax ∨ By)" and ✱9·zz
    "(∃x)Ax ∨ (∃y)By = df (∃x)(∃y)(Ax ∨ By)". Every clause with two quantified sides takes out the
    outermost quantifier of each, as ✱9·07·08 do, and leaves Ax ∨ By to the same definitions. It agrees
    with `orPrinted` except where both sides begin with quantifiers of the same kind and the left one
    has a further apparent variable: (∃x) : (∃u) . φ(x, u) . ∨ . (∃y) . ψy is (∃x) : (∃y) : (∃u) here,
    (∃x) : (∃u) : (∃y) in A. -/
def orPlus : PF V → PF V → PF V
  | .el a, q        => orEl a q                                               -- ✱1, ✱9·04, ✱9·06
  | .all φ, .el b   => .all fun x => orPlus (φ x) (.el b)                     -- ✱9·03
  | .all φ, .all ψ  => .all fun x => .all fun y => orPlus (φ x) (ψ y)         -- ✱9·yy
  | .all φ, .ex ψ   => .all fun x => .ex fun y => orPlus (φ x) (ψ y)          -- ✱9·07
  | .ex ψ, .el b    => .ex fun y => orPlus (ψ y) (.el b)                      -- ✱9·05
  | .ex ψ, .ex χ    => .ex fun y => .ex fun z => orPlus (ψ y) (χ z)           -- ✱9·zz
  | .ex ψ, .all φ   => .all fun x => .ex fun y => orPlus (ψ y) (φ x)          -- ✱9·08

/-- The kinds of the quantifiers in front (`true` for (x), `false` for (∃x)), reading each apparent
    variable as the given variable of its type. -/
def kinds (d : ∀ τ, V τ) : PF V → List Bool
  | .el _  => []
  | .all φ => true :: kinds d (φ (d _))
  | .ex φ  => false :: kinds d (φ (d _))

@[reducible] def imp (p q : PF V) : PF V := PF.or (PF.neg p) q                    -- ✱1·01
@[reducible] def and (p q : PF V) : PF V := PF.neg (PF.or (PF.neg p) (PF.neg q))  -- ✱3·01
@[reducible] def iff (p q : PF V) : PF V := PF.and (PF.imp p q) (PF.imp q p)      -- ✱4·01

theorem check_convention_or_elementary (a b : EF V) : PF.or (.el a) (.el b) = .el (.or a b) := rfl
theorem check_convention_or_all_left {τ : Ty} (φ : V τ → PF V) (q : PF V) : PF.or (.all φ) q = .all fun x => PF.or (φ x) q := rfl
theorem check_convention_or_universal_first {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.or (.ex φ) (.all ψ) = .all fun y => PF.or (.ex φ) (ψ y) := rfl
theorem check_convention_or_two_exists {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.or (.ex φ) (.ex ψ) = .ex fun x => PF.or (φ x) (.ex ψ) := rfl
theorem check_printed_or_all_ex {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.orPrinted (.all φ) (.ex ψ) = .all fun x => .ex fun y => PF.orPrinted (φ x) (ψ y) := rfl
theorem check_printed_or_ex_all {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.orPrinted (.ex ψ) (.all φ) = .all fun x => .ex fun y => PF.orPrinted (ψ y) (φ x) := rfl
theorem check_landini_or_two_alls {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.orPlus (.all φ) (.all ψ) = .all fun x => .all fun y => PF.orPlus (φ x) (ψ y) := rfl
theorem check_landini_or_two_exists {τ σ : Ty} (φ : V τ → PF V) (ψ : V σ → PF V) :
    PF.orPlus (.ex φ) (.ex ψ) = .ex fun x => .ex fun y => PF.orPlus (φ x) (ψ y) := rfl

end PF

/-! ## Readings

  Which definitions of disjunction a ✱9 system uses, and which rule, if any, it adds to ✱9's primitive
  propositions (docs/REPAIRS.md):
  - A, `Reading.printed`: ✱9·03–✱9·08 as printed (`PF.orPrinted`), no added rule;
  - C, `Reading.russell`: the same definitions and Russell's ✱8·13 carried over to ✱9 (`Rule.exch`,
    PM/Found9/System.lean); the working reading and the default;
  - L, `Reading.withSwitch`: ✱9+, the definitions as printed with ✱9·yy and ✱9·zz (`PF.orPlus`) and
    Landini's rule Switch, which comes with these definitions; a published variant, cross-check;
  - B, `Reading.convention`: the alternative convention (`PF.or`), a cross-check;
  - `Reading.prenexSwitch`: the definitions as printed with the prenex Switch, an earlier repair kept
    for comparison (R5). -/

/-- Which definitions of ∨: as printed (A and C), ✱9+ (L), or the alternative convention (B).
    Landini's rule Switch belongs to ✱9+ and is admitted exactly when the definitions are `.plus`. -/
inductive Defs where
  | printed
  | convention
  | plus

/-- p ∨ q under the given definitions. -/
def PF.disj {V : Ty → Type} : Defs → PF V → PF V → PF V
  | .printed => PF.orPrinted
  | .convention => PF.or
  | .plus => PF.orPlus

/-- The rule a reading adds to ✱9's primitive propositions: none (`basic`), Russell's ✱8·13 carried
    over to ✱9 (`exch`, reading C), or the prenex Switch (`prenex`, R5, kept for comparison). Each is
    gated as comprehension and reducibility are in `Sys`. -/
inductive Rule where
  | basic
  | exch
  | prenex

/-- A reading of ✱9: its definitions of ∨ (with which ✱9+ brings Switch), and the rule it adds. -/
structure Reading where
  defs : Defs
  rule : Rule := .basic

namespace Reading
variable {V : Ty → Type}

/-- Reading A: the definitions as printed. -/
@[reducible] def printed : Reading := ⟨.printed, .basic⟩
/-- Reading C: the definitions as printed with Russell's ✱8·13 carried over; the default. -/
@[reducible] def russell : Reading := ⟨.printed, .exch⟩
/-- Reading L: ✱9+, the definitions as printed with ✱9·yy, ✱9·zz and Switch (Landini 2000); a
    published variant, cross-check. -/
@[reducible] def withSwitch : Reading := ⟨.plus, .basic⟩
/-- Reading B: the alternative convention, a cross-check. -/
@[reducible] def convention : Reading := ⟨.convention, .basic⟩
/-- The definitions as printed with the prenex Switch (R5, kept for comparison). -/
@[reducible] def prenexSwitch : Reading := ⟨.printed, .prenex⟩

@[reducible] def or (R : Reading) (p q : PF V) : PF V := PF.disj R.defs p q
@[reducible] def imp (R : Reading) (p q : PF V) : PF V := R.or (PF.neg p) q                 -- ✱1·01
@[reducible] def and (R : Reading) (p q : PF V) : PF V :=
  PF.neg (R.or (PF.neg p) (PF.neg q))                                                       -- ✱3·01
@[reducible] def iff (R : Reading) (p q : PF V) : PF V := R.and (R.imp p q) (R.imp q p)      -- ✱4·01

theorem check_convention_imp_agrees (p q : PF V) : Reading.convention.imp p q = PF.imp p q := by cases p <;> rfl
end Reading

/-! ## Printed expressions and their prenex forms (for the prenex Switch)

  PM writes "(x) . φx . ∨ . (∃y) . ψy", "(x) : (y) . ∼(φx ∨ φy) . ∨ . (∃z) . φz": ✱9 propositions
  combined by ∼ and ∨, with quantifiers that the definitions then move to the front. `PE V` is such an
  expression; `Prenex t X` says that X is one of the propositions the definitions could make of t:
  the quantifiers of each disjunct taken out in their own order, those of different disjuncts
  interleaved in some order (`Merge`). Each reading's definitions give one of them (`prenex_read`). -/

/-- An expression as PM prints it: a ✱9 proposition, or quantifiers, ∼ and ∨ over expressions. -/
inductive PE (V : Ty → Type) where
  | pf  : PF V → PE V
  | all {τ : Ty} : (V τ → PE V) → PE V
  | ex  {τ : Ty} : (V τ → PE V) → PE V
  | neg : PE V → PE V
  | or  : PE V → PE V → PE V

namespace PE
variable {V : Ty → Type}
@[reducible] def imp (s t : PE V) : PE V := .or (.neg s) t                                 -- ✱1·01
@[reducible] def and (s t : PE V) : PE V := .neg (.or (.neg s) (.neg t))                    -- ✱3·01
@[reducible] def iff (s t : PE V) : PE V := PE.and (PE.imp s t) (PE.imp t s)                 -- ✱4·01

/-- The proposition the definitions `d` make of an expression. -/
def read (d : Defs) : PE V → PF V
  | .pf X    => X
  | .all t   => .all fun x => read d (t x)
  | .ex t    => .ex fun x => read d (t x)
  | .neg t   => PF.neg (read d t)
  | .or s t  => PF.disj d (read d s) (read d t)
end PE

/-- `Merge X Y Z`: Z is X ∨ Y with the quantifiers of X and of Y taken to the front, each side's in its
    own order, the two sides' interleaved in some order, over the matrix (matrix of X) ∨ (matrix of Y).
    The variables that X binds occur in X only, those that Y binds in Y only. -/
inductive Merge {V : Ty → Type} : PF V → PF V → PF V → Prop where
  | el (a b : EF V) : Merge (.el a) (.el b) (.el (.or a b))
  | allL {τ : Ty} {φ : V τ → PF V} {Y : PF V} {Z : V τ → PF V} :
      (∀ x, Merge (φ x) Y (Z x)) → Merge (.all φ) Y (.all Z)
  | exL {τ : Ty} {φ : V τ → PF V} {Y : PF V} {Z : V τ → PF V} :
      (∀ x, Merge (φ x) Y (Z x)) → Merge (.ex φ) Y (.ex Z)
  | allR {τ : Ty} {X : PF V} {ψ : V τ → PF V} {Z : V τ → PF V} :
      (∀ y, Merge X (ψ y) (Z y)) → Merge X (.all ψ) (.all Z)
  | exR {τ : Ty} {X : PF V} {ψ : V τ → PF V} {Z : V τ → PF V} :
      (∀ y, Merge X (ψ y) (Z y)) → Merge X (.ex ψ) (.ex Z)

/-- `Prenex t X`: X is a prenex form of the expression t (see `Merge`). -/
inductive Prenex {V : Ty → Type} : PE V → PF V → Prop where
  | pf (X : PF V) : Prenex (.pf X) X
  | all {τ : Ty} {t : V τ → PE V} {X : V τ → PF V} :
      (∀ x, Prenex (t x) (X x)) → Prenex (.all t) (.all X)
  | ex {τ : Ty} {t : V τ → PE V} {X : V τ → PF V} :
      (∀ x, Prenex (t x) (X x)) → Prenex (.ex t) (.ex X)
  | neg {t : PE V} {X : PF V} : Prenex t X → Prenex (.neg t) (PF.neg X)
  | or {s t : PE V} {X Y Z : PF V} : Prenex s X → Prenex t Y → Merge X Y Z → Prenex (.or s t) Z

section
variable {V : Ty → Type}

theorem merge_orEl (a : EF V) : ∀ Y : PF V, Merge (.el a) Y (PF.orEl a Y)
  | .el b  => .el a b
  | .all ψ => .allR fun y => merge_orEl a (ψ y)
  | .ex ψ  => .exR fun y => merge_orEl a (ψ y)

/-- The definitions as printed take the quantifiers out in one of the orders: `orPrinted` is a merge. -/
theorem merge_orPrinted : ∀ X Y : PF V, Merge X Y (PF.orPrinted X Y)
  | .el a, Y => merge_orEl a Y
  | .all φ, .el b => .allL fun x => merge_orPrinted (φ x) (.el b)
  | .all φ, .all ψ => .allL fun x => merge_orPrinted (φ x) (.all ψ)
  | .all φ, .ex ψ => .allL fun x => .exR fun y => merge_orPrinted (φ x) (ψ y)
  | .ex ψ, .el b => .exL fun y => merge_orPrinted (ψ y) (.el b)
  | .ex ψ, .ex χ => .exL fun y => merge_orPrinted (ψ y) (.ex χ)
  | .ex ψ, .all φ => .allR fun x => .exL fun y => merge_orPrinted (ψ y) (φ x)

/-- `PF.or.orEx` is a merge, given that each φx ∨ q is. -/
theorem merge_orEx {τ : Ty} (φ : V τ → PF V) (ih : ∀ x Y, Merge (φ x) Y (PF.or (φ x) Y)) :
    ∀ Y : PF V, Merge (.ex φ) Y (PF.or.orEx (fun x q => PF.or (φ x) q) Y)
  | .all ψ => .allR fun y => merge_orEx φ ih (ψ y)
  | .el b  => .exL fun x => ih x (.el b)
  | .ex ψ  => .exL fun x => ih x (.ex ψ)

/-- The alternative convention takes the quantifiers out in one of the orders: `PF.or` is a merge. -/
theorem merge_or : ∀ X Y : PF V, Merge X Y (PF.or X Y)
  | .el a, Y => merge_orEl a Y
  | .all φ, Y => .allL fun x => merge_or (φ x) Y
  | .ex φ, Y => merge_orEx φ (fun x => merge_or (φ x)) Y

/-- ✱9+'s definitions take the quantifiers out in one of the orders: `orPlus` is a merge. -/
theorem merge_orPlus : ∀ X Y : PF V, Merge X Y (PF.orPlus X Y)
  | .el a, Y => merge_orEl a Y
  | .all φ, .el b => .allL fun x => merge_orPlus (φ x) (.el b)
  | .all φ, .all ψ => .allL fun x => .allR fun y => merge_orPlus (φ x) (ψ y)
  | .all φ, .ex ψ => .allL fun x => .exR fun y => merge_orPlus (φ x) (ψ y)
  | .ex ψ, .el b => .exL fun y => merge_orPlus (ψ y) (.el b)
  | .ex ψ, .ex χ => .exL fun y => .exR fun z => merge_orPlus (ψ y) (χ z)
  | .ex ψ, .all φ => .allR fun x => .exL fun y => merge_orPlus (ψ y) (φ x)

theorem merge_disj : ∀ (d : Defs) (X Y : PF V), Merge X Y (PF.disj d X Y)
  | .printed => merge_orPrinted
  | .convention => merge_or
  | .plus => merge_orPlus

/-- Each reading's definitions give a prenex form of the expression. -/
theorem prenex_read (d : Defs) : ∀ t : PE V, Prenex t (t.read d)
  | .pf X => .pf X
  | .all t => .all fun x => prenex_read d (t x)
  | .ex t => .ex fun x => prenex_read d (t x)
  | .neg t => .neg (prenex_read d t)
  | .or s t => .or (prenex_read d s) (prenex_read d t) (merge_disj d _ _)
end

/-! ## The steps of Russell's ✱8·13 and of Landini's Switch

  Russell's rule of ✱8 in the second edition (Vol. I, Appendix A, p. 636; page image): "✱8·13. If all
  occurrences of x are separated from all occurrences of y by a certain stroke, we can change the order
  of x and y in the prefix, i.e. we can replace "(y) : (∃x) . φx | ψy" by "(∃x) : (y) . φx | ψy" and
  vice versa. Pp". Carried over to ✱9 (docs/REPAIRS.md, R1): the stroke becomes the ∨ of ✱9's matrix
  (an elementary proposition built with ∼ and ∨); "the prefix" is the prefix of the proposition ✱9's
  definitions make, the quantifiers in front of a `PF`; x and y are two adjacent quantifiers of it, of
  either kind, and the step goes both ways (`ExchStep`). It is a primitive rule, as Russell made it.

  Landini (2000, p. 64) states the rule of ✱9+: "Switch (S): From B[(x)(∃y)Axy] infer B[(∃y)(x)Axy],
  where there is a logical connective in A on one side of which occur all free occurrences of the
  individual variable x and on the other side of which occur all free occurrences of the individual
  variable y." It goes one way, (x)(∃y) to (∃y)(x), inside any context B.

  A formula of ✱9 is a proposition with its quantifiers in front (`PF`): the definitions put every
  apparent variable there. So an occurrence of (x)(∃y)A in one is a tail of it, and the context B is
  the quantifiers before it (`SwitchStep`); for ✱8·13 likewise, the prefix (`ExchStep`). The side
  condition, `Sep`, is the same for both: A is a merge (`Merge`) of a part in which x alone of the two
  is free and a part in which y alone is, in either order: the connective is the ∨ that joins their
  matrices, and each quantifier of A binds a variable of one part only. That last clause is ours:
  neither Russell's wording nor Landini's restricts the quantifiers of A, and read without it the rule
  is unsound (`switch_wide_unsound`, PM/Found9/Equiv.lean; docs/REPAIRS.md, R1). Russell states the
  rule where every function has one variable ("For the present, however, we are not concerned with
  variable functions of two variables", p. 636, page image), where the clause holds of itself. The
  connective is also taken to be the one that joins the two parts, not one deeper inside them (under
  ∼, or beside a part without x and y), though Russell says "It is not necessary for the above
  primitive proposition that the stroke separating x and y should be the principal stroke" (p. xxvi,
  text layer); every use in this repository is of that kind. -/

/-- The side condition on (x)(∃y)A (Landini) or on two adjacent quantifiers (x), (y) of any kinds over
    A (✱8·13 carried over), for x of type τ and y of type σ: A is a merge of a part with x and a part
    with y, in either order, so that the ∨ joining their matrices has every free x on one side and
    every free y on the other. -/
inductive Sep {V : Ty → Type} {τ σ : Ty} : (V τ → V σ → PF V) → Prop where
  | left (L : V τ → PF V) (R : V σ → PF V) {Z : V τ → V σ → PF V} :
      (∀ x y, Merge (L x) (R y) (Z x y)) → Sep Z
  | right (L : V τ → PF V) (R : V σ → PF V) {Z : V τ → V σ → PF V} :
      (∀ x y, Merge (R y) (L x) (Z x y)) → Sep Z

/-- `SwitchStep X Y`: Y is X with one (x)(∃y)A, A as `Sep` asks, turned into (∃y)(x)A, inside the
    quantifiers in front of it. -/
inductive SwitchStep {V : Ty → Type} : PF V → PF V → Prop where
  | here {τ σ : Ty} {Z : V τ → V σ → PF V} :
      Sep Z → SwitchStep (.all fun x => .ex fun y => Z x y) (.ex fun y => .all fun x => Z x y)
  | all {τ : Ty} {φ ψ : V τ → PF V} : (∀ x, SwitchStep (φ x) (ψ x)) → SwitchStep (.all φ) (.all ψ)
  | ex {τ : Ty} {φ ψ : V τ → PF V} : (∀ x, SwitchStep (φ x) (ψ x)) → SwitchStep (.ex φ) (.ex ψ)

/-- A quantifier of the given kind: (x) for `true`, (∃x) for `false`. -/
def PF.qu {V : Ty → Type} {τ : Ty} : Bool → (V τ → PF V) → PF V
  | true, φ => .all φ
  | false, φ => .ex φ

/-- `ExchStep k₁ k₂ X Y`: a step of ✱8·13 carried over to ✱9. Y is X with two adjacent quantifiers of
    its prefix, the first of kind k₁ and binding x, the second of kind k₂ and binding y, put in the
    other order, over an A in which they are separated as `Sep` asks; the quantifiers in front of them
    stay. Each direction of Russell's "and vice versa" is a step (`ExchStep.symm`). The kinds are
    indices, so that each step, in every context, is of the same two kinds. -/
inductive ExchStep {V : Ty → Type} (k₁ k₂ : Bool) : PF V → PF V → Prop where
  | here {τ σ : Ty} {Z : V τ → V σ → PF V} :
      Sep Z → ExchStep k₁ k₂ (PF.qu k₁ fun x => PF.qu k₂ fun y => Z x y)
        (PF.qu k₂ fun y => PF.qu k₁ fun x => Z x y)
  | all {τ : Ty} {φ ψ : V τ → PF V} :
      (∀ x, ExchStep k₁ k₂ (φ x) (ψ x)) → ExchStep k₁ k₂ (.all φ) (.all ψ)
  | ex {τ : Ty} {φ ψ : V τ → PF V} :
      (∀ x, ExchStep k₁ k₂ (φ x) (ψ x)) → ExchStep k₁ k₂ (.ex φ) (.ex ψ)

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

/-- An expression written with ✱10's primitive ideas. -/
def PE.toQ {V : Ty → Type} : PE V → QF V
  | .pf X    => X.toQ
  | .all t   => .all fun x => (t x).toQ
  | .ex t    => QF.ex fun x => (t x).toQ
  | .neg t   => .neg t.toQ
  | .or s t  => .or s.toQ t.toQ

/-- A ✱10 formula as an expression in ✱9's notation. -/
def _root_.PM.QF.toPE {V : Ty → Type} : QF V → PE V
  | .atom P xs   => .pf (.el (.atom P xs))
  | .app1 f x    => .pf (.el (.app1 f x))
  | .app2 f x y  => .pf (.el (.app2 f x y))
  | .neg p       => .neg p.toPE
  | .or p q      => .or p.toPE q.toPE
  | .all φ       => .all fun x => (φ x).toPE

/-- The ✱9 proposition for which a ✱10 formula stands under the definitions `d`: ∼ and ∨ are read by
    ✱9·01–✱9·08: the proposition the definitions make of `QF.toPE` (`prenex_toF9`). -/
def _root_.PM.QF.toF9 {V : Ty → Type} (d : Defs) : QF V → PF V
  | .atom P xs   => .el (.atom P xs)
  | .app1 f x    => .el (.app1 f x)
  | .app2 f x y  => .el (.app2 f x y)
  | .neg p       => PF.neg (p.toF9 d)
  | .or p q      => PF.disj d (p.toF9 d) (q.toF9 d)
  | .all φ       => .all fun x => (φ x).toF9 d

end PM.F9
