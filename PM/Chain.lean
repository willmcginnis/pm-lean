import PM.Star10
/-!
  Chains of ⊃ and ≡ lines, written as Lean `calc` blocks.

  PM displays a chain of implications or equivalences as one line, "⊢ . A . [✱x] ⊃ . B . [✱y] ⊃ . C", and
  a chain under a hypothesis as "⊢ : Hp . ⊃ : A . ≡ . B . [✱x] ≡ . C" (e.g. ✱14·25, p. 192). Lean's standard
  form for such a chain is `calc` with `Trans` instances: each `calc` line is one of PM's lines, with
  PM's citation in a comment, and the step that joins two lines is proved once, in the instance below,
  from PM's own propositions.

  PM's warrant for leaving the joining step tacit:
  - Introduction p. 9 (inference) and the commentary on ✱2·31 (pp. 109–110): a series of implications
    "all asserted" is written "p ⊃ q ⊃ r ⊃ s", the propositions in virtue of which each implication holds
    given in square brackets, and the joining by Syll not written;
  - after ✱4·32 (p. 123): "The use of ✱4·22 will often be tacit, as above. The principle is the same as
    that explained in respect of implication in ✱2·31";
  - under a hypothesis PM sometimes names the joining step: the ✱3 summary (p. 115) ends the proof of
    ✱3·47 by "✱3·43 and ✱3·33", ✱14·17 cites ✱4·22 (p. 188); ✱2·83 (p. 113) is the chaining of
    implications under a common hypothesis.
  The steps that join two asserted lines (Syll, ✱4·22) are tacit throughout (PM/Star11.lean's header).
  The ones that join lines under a hypothesis use, besides these, Comp (✱3·43), ✱2·02 (to put an
  asserted line under the hypothesis), ✱2·83, and Syll in the form ✱2·05 under the hypothesis. The
  ledgers list them per proposition, as `glue`, alongside the fidelity (docs/FIDELITY.md).

  Notation (scoped to `PM`): `A ≡ B` is `⊢ . A ≡ B` and `A ⊃ B` is `⊢ . A ⊃ B`, between formulas;
  `A ≡[H] B` is `⊢ : H . ⊃ : A . ≡ . B` and `A ⊃[H] B` is `⊢ : H . ⊃ : A . ⊃ . B`. Each is a
  definition that unfolds to the `QThm` statement, so no theorem statement changes.
-/
namespace PM
open QF

variable {V : Ty → Type} {S : Sys V}

/-! ## Joining lines under a hypothesis -/

/-- Chaining two ≡ lines under one hypothesis (Comp ✱3·43, ✱4·22). -/
theorem qimpIffTrans {H A B C : QF V} (h1 : QThm S (imp H (iff A B))) (h2 : QThm S (imp H (iff B C))) :
    QThm S (imp H (iff A C)) :=
  qsyl (qcomp h1 h2) (QL.t4_22 A B C)
/-- Chaining a ≡ line under a hypothesis with an asserted ≡ (✱2·02, ✱3·43, ✱4·22). -/
theorem qimpIffTransR {H A B C : QF V} (h1 : QThm S (imp H (iff A B))) (h2 : QThm S (iff B C)) :
    QThm S (imp H (iff A C)) :=
  qimpIffTrans h1 (QThm.mp h2 (QL.t2_02 H _))
/-- An asserted ≡ followed by a ≡ line under a hypothesis (✱2·02, ✱3·43, ✱4·22). -/
theorem qimpIffTransL {H A B C : QF V} (h1 : QThm S (iff A B)) (h2 : QThm S (imp H (iff B C))) :
    QThm S (imp H (iff A C)) :=
  qimpIffTrans (QThm.mp h1 (QL.t2_02 H _)) h2
/-- Chaining two ⊃ lines under one hypothesis (✱2·83). -/
theorem qimpImpTrans {H A B C : QF V} (h1 : QThm S (imp H (imp A B))) (h2 : QThm S (imp H (imp B C))) :
    QThm S (imp H (imp A C)) :=
  QThm.mp h2 (QThm.mp h1 (QL.t2_83 H A B C))
/-- Chaining a ⊃ line under a hypothesis with an asserted ⊃ (Syll ✱2·05). -/
theorem qimpImpTransR {H A B C : QF V} (h1 : QThm S (imp H (imp A B))) (h2 : QThm S (imp B C)) :
    QThm S (imp H (imp A C)) :=
  qsyl h1 (QThm.mp h2 (QL.t2_05 A B C))
/-- Reading the ≡ of a line under a hypothesis from right to left (✱4·21). -/
theorem qimpIffSymm {H A B : QF V} (h : QThm S (imp H (iff A B))) : QThm S (imp H (iff B A)) :=
  qsyl h (qiffMp (QL.t4_21 A B))

/-! ## The lines of a chain as relations -/

/-- `⊢ . A ≡ B`, as a relation between A and B. -/
def QIff (S : Sys V) (A B : QF V) : Prop := QThm S (iff A B)
/-- `⊢ . A ⊃ B`, as a relation between A and B. -/
def QImp (S : Sys V) (A B : QF V) : Prop := QThm S (imp A B)
/-- `⊢ : H . ⊃ : A . ≡ . B`, as a relation between A and B. -/
def QImpIff (S : Sys V) (H A B : QF V) : Prop := QThm S (imp H (iff A B))
/-- `⊢ : H . ⊃ : A . ⊃ . B`, as a relation between A and B. -/
def QImpImp (S : Sys V) (H A B : QF V) : Prop := QThm S (imp H (imp A B))

/-! The notations name the system `S` of the theorem they are used in (every PM theorem here calls
    it `S`), so that each `calc` line is checked in that system: `hygiene false` lets the `S` of the
    notation be that variable. -/
set_option hygiene false in
/-- `A ≡ B`: `⊢ . A ≡ B` (`QIff`). -/
scoped infix:50 " ≡ " => QIff S
set_option hygiene false in
/-- `A ⊃ B`: `⊢ . A ⊃ B` (`QImp`). -/
scoped infix:50 " ⊃ " => QImp S
set_option hygiene false in
/-- `A ≡[H] B`: `⊢ : H . ⊃ : A . ≡ . B` (`QImpIff`). -/
scoped notation:50 A:51 " ≡[" H "] " B:51 => QImpIff S H A B
set_option hygiene false in
/-- `A ⊃[H] B`: `⊢ : H . ⊃ : A . ⊃ . B` (`QImpImp`). -/
scoped notation:50 A:51 " ⊃[" H "] " B:51 => QImpImp S H A B

/-! ## Joining two lines (the `Trans` instances `calc` uses) -/

/-- `A ≡ B`, `B ≡ C` give `A ≡ C` (✱4·22, tacit: p. 123; the two lines joined by ✱3·2). -/
instance transIff : @Trans (QF V) (QF V) (QF V) (QIff S) (QIff S) (QIff S) :=
  ⟨fun h1 h2 => QThm.mp (qandI h1 h2) (QL.t4_22 _ _ _)⟩
/-- `A ⊃ B`, `B ⊃ C` give `A ⊃ C` (Syll, tacit: ✱2·31, pp. 109–110). -/
instance transImp : @Trans (QF V) (QF V) (QF V) (QImp S) (QImp S) (QImp S) := ⟨qsyl⟩
/-- `A ≡ B`, `B ⊃ C` give `A ⊃ C` (the ≡ read as ⊃ by ✱3·26, then Syll). -/
instance transIffImp : @Trans (QF V) (QF V) (QF V) (QIff S) (QImp S) (QImp S) :=
  ⟨fun h1 h2 => qsyl (qiffMp h1) h2⟩
/-- `A ⊃ B`, `B ≡ C` give `A ⊃ C` (the ≡ read as ⊃ by ✱3·26, then Syll). -/
instance transImpIff : @Trans (QF V) (QF V) (QF V) (QImp S) (QIff S) (QImp S) :=
  ⟨fun h1 h2 => qsyl h1 (qiffMp h2)⟩
/-- Under H, `A ≡ B` and `B ≡ C` give `A ≡ C` (Comp ✱3·43, ✱4·22). -/
instance transHIff {H : QF V} : @Trans (QF V) (QF V) (QF V) (QImpIff S H) (QImpIff S H) (QImpIff S H) :=
  ⟨qimpIffTrans⟩
/-- Under H, `A ≡ B`, and the asserted `B ≡ C`, give `A ≡ C` (✱2·02, ✱3·43, ✱4·22). -/
instance transHIffIff {H : QF V} : @Trans (QF V) (QF V) (QF V) (QImpIff S H) (QIff S) (QImpIff S H) :=
  ⟨qimpIffTransR⟩
/-- The asserted `A ≡ B`, and under H `B ≡ C`, give `A ≡ C` under H (✱2·02, ✱3·43, ✱4·22). -/
instance transIffHIff {H : QF V} : @Trans (QF V) (QF V) (QF V) (QIff S) (QImpIff S H) (QImpIff S H) :=
  ⟨qimpIffTransL⟩
/-- Under H, `A ⊃ B` and `B ⊃ C` give `A ⊃ C` (✱2·83). -/
instance transHImp {H : QF V} : @Trans (QF V) (QF V) (QF V) (QImpImp S H) (QImpImp S H) (QImpImp S H) :=
  ⟨qimpImpTrans⟩
/-- Under H, `A ⊃ B`, and the asserted `B ⊃ C`, give `A ⊃ C` (Syll ✱2·05 under H). -/
instance transHImpImp {H : QF V} : @Trans (QF V) (QF V) (QF V) (QImpImp S H) (QImp S) (QImpImp S H) :=
  ⟨qimpImpTransR⟩

end PM
