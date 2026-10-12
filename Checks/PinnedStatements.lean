-- Pinned statements: the exact statements of the propositions and metatheorems whose statement a
-- review once corrected or questioned. Each `example` restates the theorem with its full type and
-- proves it by the theorem itself, so weakening a statement (≡ to ⊃, an added hypothesis, a narrower
-- system, a changed definition it relies on) makes this file, and so `lake build`, fail. A deliberate
-- change of one of these statements must change its pin here too.
import PM
namespace PM
open QF

/-! ## PM's propositions -/

/-- ✱14·32 is printed with ≡ after E!(ιx)(φx) (p. 194). A review found it had been weakened to ⊃,
    since the hint gives only the ⊃ half; it was restored as printed, the converse proved by ✱14·21. -/
example {V : Ty → Type} {S : Sys} [Reducibility S] {α : Ty} (φ χ : V α → QF V) :
    QThm S (iff (exists1 φ) (iff (desc φ fun z => .neg (χ z)) (.neg (desc φ χ)))) :=
  q14_32 φ χ

/-- ✱1·4 (Perm) has `p ∨ p` for `q ∨ p` in the transcription; the check that the variant is not a
    theorem is how the slip was found, and must keep stating the variant exactly. -/
example : ¬ Thm (F.imp (.or (F.var "p") (F.var "q")) (.or (F.var "p") (F.var "p"))) :=
  star1_4_variant_not_a_theorem

/-! ## Claims about the systems, once stated more strongly than proved and now theorems -/

/-- "Same theorems either way" was once an unproved remark (a review found it). With reducibility,
    any two of the four styles derive the same theorems, for either setting of comprehension. -/
example {V : Ty → Type} (c : Bool) (P P' : PredReading) (R R' : RealReading) (p : QF V) :
    QThm (⟨c, true, Style.of P R⟩ : Sys) p ↔ QThm (⟨c, true, Style.of P' R'⟩ : Sys) p :=
  styles_equiv c P P' R R' p
example {V : Ty → Type} (R : RealReading) (p : QF V) :
    QThm (Sys.full (Style.of .matrix R)) p ↔ QThm (Sys.full (Style.of .lowestOrder R)) p :=
  styles_equiv_full R p
example {V : Ty → Type} (P : PredReading) (p : QF V) :
    QThm (Sys.full (Style.of P .ownOrder)) p ↔ QThm (Sys.full (Style.of P .asArgument)) p :=
  styles_equiv_real P p

/-- A review found the styles had been said to differ in whether `realPhi` is derivable; it is a
    theorem of every system, with neither comprehension nor ✱12·1. -/
example {V : Ty → Type} (S : Sys) (φ : V (Ty.pred1 .ind)) :
    QThm S (ex (τ := Ty.pred1 .ind) fun g => fiff (fun x => .app1 φ x) fun x => .app1 g x) :=
  realPhi_every_system S φ

/-- p. 56's second clause and the lowest-order rule agree (within this encoding; the claim was
    qualified after a review). The two definitions are pinned too, since the theorem is only as
    strong as they are. -/
example (a b : Ty) (ψ : U a → U b → QF U) : SecondClause a b ψ ↔ LowestOrder2 a b ψ :=
  second_clause_iff_lowestOrder a b ψ
example (a b : Ty) (ψ : U a → U b → QF U) :
    SecondClause a b ψ = (fnOrder a (fun x => ψ x ()) = a.ord + 1 ∨ fnOrder b (ψ ()) = b.ord + 1) :=
  rfl
example (a b : Ty) (ψ : U a → U b → QF U) :
    LowestOrder2 a b ψ = (fnOrder2 a b ψ = max a.ord b.ord + 1) :=
  rfl

/-- The `q12_1_of_var` claim was limited, after a review, to comprehension and formulas admitted at
    one order k (uniformly order-bounded): the hypotheses `[Comprehension S]` and `hψ` stay. -/
example {V : Ty → Type} {S : Sys} [Comprehension S] {a : Ty} {k : Nat}
    (hvar : ∀ g : V (.fn1 a k),
      QThm S (ex (τ := Ty.pred1 a) fun f => fiff (fun x => .app1 g x) fun x => .app1 f x))
    (ψ : V a → QF V) (hψ : S.style.adm1 k ψ) :
    QThm S (ex (τ := Ty.pred1 a) fun f => fiff ψ fun x => .app1 f x) :=
  q12_1_of_var hvar ψ hψ

/-- A review pointed out that the collapse at `U` needs no ✱12·1: comprehension alone gives it. -/
example {S : Sys} [Comprehension S]
    (hq : S.style.adm1 (V := U) (a := .ind) 0 fun x => .atom "q" [x])
    (hnq : S.style.adm1 (V := U) (a := .ind) 0 fun x => .neg (.atom "q" [x])) (p : QF U) : QThm S p :=
  trap_unit_compr hq hnq p

/-- The matrix test is conjoined with the order check, not put in its place (after a review: φ!x
    with φ of order 2 is a matrix but not of order 1); so the matrix style admits no more than the
    lowest-order style. -/
example (L : OrderCheck) {V : Ty → Type} {a : Ty} (k : Nat) (ψ : V a → QF V) :
    (Style.matrix L).adm1 k ψ = ∀ x, L (ψ x) (Ty.fn1 a k).ord ∧ (k = 0 → IsMatrix (ψ x)) :=
  rfl
example {V : Ty → Type} {c r : Bool} (R : RealReading) {p : QF V}
    (h : QThm ⟨c, r, Style.of .matrix R⟩ p) : QThm ⟨c, r, Style.of .lowestOrder R⟩ p :=
  QThm.matrix_to_lowestOrder R h

/-- A consistency claim must name a structure's own variables (PM/Trap.lean): consistency is at the
    model's family, and for the theorems that hold for every family. -/
example (S : Sys) : ¬ QThm (V := twoModel.den) S (.atom "p" []) := consistent S
example (S : Sys) : ¬ ∀ V : Ty → Type, QThm (V := V) S (.atom "p" []) := consistent_all S

/-! ## ✱9's definitions and the agreement of ✱9's method with ✱10's -/

/-- ✱9·07 "(x) . φx . ∨ . (∃y) . ψy : = : (x) : (∃y) . φx ∨ ψy", which is "to apply also when φ and ψ
    are not both elementary functions" (pp. 135–136). An external review found that ✱9's disjunction
    took every universal quantifier of the left side out first, giving (x) : (z) : (∃y) here; as
    printed, ✱9·07 takes out (x) and (∃y) and leaves φx ∨ ψy, which then gives (z). The printed
    reading is kept as `PF.orPrinted` (reading A). -/
example {V : Ty → Type} :
    F9.PF.orPrinted (V := V) (.all fun x => .all fun z => .el (.atom "R" [x, z]))
      (.ex fun y => .el (.atom "S" [y]))
      = .all fun x => .ex fun y => .all fun z => .el (.or (.atom "R" [x, z]) (.atom "S" [y])) :=
  rfl
/-- ✱9·08 "(∃y) . ψy . ∨ . (x) . φx : = : (x) : (∃y) . ψy ∨ φx", as printed, for the same φ and ψ. -/
example {V : Ty → Type} :
    F9.PF.orPrinted (V := V) (.ex fun y => .el (.atom "S" [y]))
      (.all fun x => .all fun z => .el (.atom "R" [x, z]))
      = .all fun x => .ex fun y => .all fun z => .el (.or (.atom "S" [y]) (.atom "R" [x, z])) :=
  rfl
/-- ✱9+ (reading L, Landini 2000) has ✱9·07 as printed. -/
example {V : Ty → Type} :
    F9.PF.orPlus (V := V) (.all fun x => .all fun z => .el (.atom "R" [x, z]))
      (.ex fun y => .el (.atom "S" [y]))
      = .all fun x => .ex fun y => .all fun z => .el (.or (.atom "R" [x, z]) (.atom "S" [y])) :=
  rfl
/-- ✱9·yy "(x)Ax ∨ (y)By = df (x)(y)(Ax ∨ By)" and ✱9·zz "(∃x)Ax ∨ (∃y)By = df (∃x)(∃y)(Ax ∨ By)" in
    ✱9+: the outermost quantifier of each side, the left one first, then Ax ∨ By. Where the left side
    has a further quantifier this differs from ✱9·03 or ✱9·05 with p the other side, the order of A and
    C, which ✱8 of the second edition states: "applied first to the one on the left, treating the one
    on the right as if it were elementary" (p. 635, page image). -/
example {V : Ty → Type} :
    F9.PF.orPlus (V := V) (.ex fun x => .ex fun u => .el (.atom "R" [x, u]))
      (.ex fun y => .el (.atom "S" [y]))
      = .ex fun x => .ex fun y => .ex fun u => .el (.or (.atom "R" [x, u]) (.atom "S" [y])) :=
  rfl
example {V : Ty → Type} :
    F9.PF.orPrinted (V := V) (.ex fun x => .ex fun u => .el (.atom "R" [x, u]))
      (.ex fun y => .el (.atom "S" [y]))
      = .ex fun x => .ex fun u => .ex fun y => .el (.or (.atom "R" [x, u]) (.atom "S" [y])) :=
  rfl
/-- The alternative convention (reading B, `PF.or`; docs/REPAIRS.md, R4, a cross-check) gives the
    other order, the order of PM's proof of ✱9·31. -/
example {V : Ty → Type} :
    F9.PF.or (V := V) (.all fun x => .all fun z => .el (.atom "R" [x, z]))
      (.ex fun y => .el (.atom "S" [y]))
      = .all fun x => .all fun z => .ex fun y => .el (.or (.atom "R" [x, z]) (.atom "S" [y])) :=
  rfl

/-- The step (3)–(4) of PM's proof of ✱9·31 is not a definitional rewrite under the definitions as
    printed (readings A and C), nor in ✱9+ (L), and is one under the alternative convention (B). -/
example {V : Ty → Type} {τ : Ty} (d : ∀ τ, V τ) (φ : V τ → F9.EF V) :
    (F9.PF.all fun x => F9.Reading.printed.imp (.ex fun y => .el (.or (φ x) (φ y))) (.ex fun z => .el (φ z))) ≠
      F9.Reading.printed.imp (.ex fun x => .ex fun y => .el (.or (φ x) (φ y))) (.ex fun z => .el (φ z)) :=
  F9.f9_31_step d φ
example {V : Ty → Type} {τ : Ty} (d : ∀ τ, V τ) (φ : V τ → F9.EF V) :
    (F9.PF.all fun x => F9.Reading.withSwitch.imp (.ex fun y => .el (.or (φ x) (φ y))) (.ex fun z => .el (φ z))) ≠
      F9.Reading.withSwitch.imp (.ex fun x => .ex fun y => .el (.or (φ x) (φ y))) (.ex fun z => .el (φ z)) :=
  F9.f9_31_step_plus d φ

/-- ✱9·25 (= ✱10·12) for p = (∃u) . χu, not elementary, and φ elementary: under either definitions its
    two sides are the same proposition, (x) : (∃u) . χu ∨ φx, so this instance is Id, with neither
    `Rep` nor a variable of every type. An external review found it against a claim that apparent
    variables in p always make the two sides different propositions. -/
example {V : Ty → Type} {σ τ : Ty} (χ : V σ → F9.EF V) (φ : V τ → F9.EF V) :
    (F9.PF.all fun x => F9.PF.orPrinted (.ex fun u => .el (χ u)) (.el (φ x))) =
      F9.PF.orPrinted (.ex fun u => .el (χ u)) (.all fun x => .el (φ x)) :=
  rfl
example {V : Ty → Type} {σ τ : Ty} (χ : V σ → F9.EF V) (φ : V τ → F9.EF V) :
    (F9.PF.all fun x => F9.PF.orPlus (.ex fun u => .el (χ u)) (.el (φ x))) =
      F9.PF.orPlus (.ex fun u => .el (χ u)) (.all fun x => .el (φ x)) :=
  rfl
example {V : Ty → Type} {σ τ : Ty} (χ : V σ → F9.EF V) (φ : V τ → F9.EF V) :
    (F9.PF.all fun x => F9.PF.or (.ex fun u => .el (χ u)) (.el (φ x))) =
      F9.PF.or (.ex fun u => .el (χ u)) (.all fun x => .el (φ x)) :=
  rfl
example {V : Ty → Type} {S : Sys} {R : F9.Reading} {σ τ : Ty} (χ : V σ → F9.EF V) (φ : V τ → F9.EF V) :
    F9.Thm9 S R (R.imp (.all fun x => R.or (.ex fun u => .el (χ u)) (.el (φ x)))
      (R.or (.ex fun u => .el (χ u)) (.all fun x => .el (φ x)))) := by
  rcases R with ⟨_ | _ | _, _⟩ <;> exact F9.idt _

/-- The working reading C has the definitions as printed and Russell's ✱8·13 carried over (R1);
    Switch is the rule of ✱9+ (reading L): a reading has it exactly when its definitions are ✱9+'s.
    The prenex Switch (R5) is opt-in, and none of A, C, L, B has it. -/
example : F9.Reading.printed.defs ≠ .plus ∧ F9.Reading.russell.defs ≠ .plus ∧
    F9.Reading.convention.defs ≠ .plus ∧ F9.Reading.withSwitch.defs = .plus := ⟨nofun, nofun, nofun, rfl⟩
example : F9.Reading.printed.rule = .basic ∧ F9.Reading.russell.rule = .exch ∧
    F9.Reading.russell.defs = .printed ∧ F9.Reading.withSwitch.rule = .basic ∧
    F9.Reading.convention.rule = .basic ∧ F9.Reading.prenexSwitch.rule = .prenex :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Russell's ✱8·13 (second edition, p. 636, page image): "we can change the order of x and y in the
    prefix ... and vice versa", carried over to ✱9: two adjacent quantifiers of the prefix, of any
    kinds, whose variables the ∨ of the matrix separates (`Sep`), inside the quantifiers in front; a
    primitive rule of C, both ways. -/
example {V : Ty → Type} {S : Sys} {R : F9.Reading} (h : R.rule = .exch) {k₁ k₂ : Bool} {X Y : F9.PF V}
    (hs : F9.ExchStep k₁ k₂ X Y) (hX : F9.Thm9 S R X) : F9.Thm9 S R Y :=
  F9.Thm9.exch h hs hX
example {V : Ty → Type} (k₁ k₂ : Bool) {τ σ : Ty} (L : V τ → F9.PF V) (R : V σ → F9.PF V)
    (Z : V τ → V σ → F9.PF V) (h : ∀ x y, F9.Merge (L x) (R y) (Z x y)) :
    F9.ExchStep k₁ k₂ (F9.PF.qu k₁ fun x => F9.PF.qu k₂ fun y => Z x y)
      (F9.PF.qu k₂ fun y => F9.PF.qu k₁ fun x => Z x y) :=
  .here (.left L R h)
example {V : Ty → Type} {k₁ k₂ : Bool} {X Y : F9.PF V} (h : F9.ExchStep k₁ k₂ X Y) :
    F9.ExchStep k₂ k₁ Y X :=
  h.symm

/-- C and L: Landini's Switch is the direction (x)(∃y) to (∃y)(x) of ✱8·13, so a derived rule of C;
    and every step of ✱8·13 is derivable in ✱9+. -/
example {V : Ty → Type} {X Y : F9.PF V} : F9.SwitchStep X Y ↔ F9.ExchStep true false X Y :=
  ⟨F9.SwitchStep.toExch, F9.ExchStep.toSwitch⟩
example {V : Ty → Type} {S : Sys} (pr : F9.Rule) {k₁ k₂ : Bool} {X Y : F9.PF V}
    (h : F9.ExchStep k₁ k₂ X Y) (hX : F9.Thm9 S ⟨.plus, pr⟩ X) : F9.Thm9 S ⟨.plus, pr⟩ Y :=
  F9.exch_plus pr h hX

/-- ✱9·31 in C, along PM's Dem., the step (3)–(4) taken by ✱8·13. -/
example {V : Ty → Type} {S : Sys} {τ : Ty} (φ : V τ → F9.EF V) :
    F9.Thm9 S F9.Reading.russell (F9.Reading.russell.imp
      (F9.Reading.russell.or (.ex fun x => .el (φ x)) (.ex fun x => .el (φ x))) (.ex fun x => .el (φ x))) :=
  F9.f9_31_russell φ

/-- Landini's Switch (2000, p. 64): "From B[(x)(∃y)Axy] infer B[(∃y)(x)Axy]", one way, inside the
    quantifiers in front, for A that `Sep` admits: a merge of a part with x and a part with y, joined
    by the ∨ of their matrices, in either order. -/
example {V : Ty → Type} {S : Sys} {R : F9.Reading} (h : R.defs = .plus) {X Y : F9.PF V}
    (hs : F9.SwitchStep X Y) (hX : F9.Thm9 S R X) : F9.Thm9 S R Y :=
  F9.Thm9.switch h hs hX
example {V : Ty → Type} {τ σ : Ty} (L : V τ → F9.PF V) (R : V σ → F9.PF V) (Z : V τ → V σ → F9.PF V)
    (h : ∀ x y, F9.Merge (L x) (R y) (Z x y)) :
    F9.SwitchStep (.all fun x => .ex fun y => Z x y) (.ex fun y => .all fun x => Z x y) :=
  .here (.left L R h)

/-- Landini's side condition needs the restriction of `Sep` on the quantifiers of A: read without it,
    Switch takes a theorem to a proposition false where R is identity on two individuals. -/
example (S : Sys) :
    ∃ Z : F9.eqModel.den .ind → F9.eqModel.den .ind → F9.PF F9.eqModel.den,
      F9.SepWide Z ∧ (∀ R : F9.Reading, F9.Thm9 S R (.all fun x => .ex fun y => Z x y)) ∧
      (F9.PF.ex fun y => .all fun x => Z x y).toQ.eval F9.eqModel = false ∧ ¬ F9.Sep Z :=
  F9.switch_wide_unsound S

/-- Neither rule exchanges a quantifier with one in whose scope it stands unless a connective
    separates their variables: (x) : (∃y) . ⊃ . (∃y) : (x) is asserted neither in C nor in L. -/
example (S : Sys) :
    ¬ F9.Thm9 (V := F9.eqModel.den) S F9.Reading.russell
      (F9.Reading.russell.imp (.all fun x => .ex fun y => .el (.atom "R" [x, y]))
        (.ex fun y => .all fun x => .el (.atom "R" [x, y]))) :=
  F9.exch_not_general S
example (S : Sys) :
    ¬ F9.Thm9 (V := F9.eqModel.den) S F9.Reading.withSwitch
      (F9.Reading.withSwitch.imp (.all fun x => .ex fun y => .el (.atom "R" [x, y]))
        (.ex fun y => .all fun x => .el (.atom "R" [x, y]))) :=
  F9.switch_not_general S

/-- The agreement of ✱9's method with ✱10's has two hypotheses, a variable of every type and ✱1·2–✱1·6
    for every ✱9 proposition (`Rep`); an external review asked that both be stated wherever it is
    cited. It holds under every reading, with `Rep` of that reading. -/
example {V : Ty → Type} {S : Sys} {R : F9.Reading} (hV : ∀ τ, Nonempty (V τ)) (hR : F9.Rep S R V)
    (q : QF V) : QThm S q ↔ F9.Thm9 S R (q.toF9 R.defs) :=
  F9.star9_iff_star10 hV hR q

end PM
