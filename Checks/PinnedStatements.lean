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
    printed, ✱9·07 takes out (x) and (∃y) and leaves φx ∨ ψy, which then gives (z). -/
example {V : Ty → Type} :
    F9.PF.or (V := V) (.all fun x => .all fun z => .el (.atom "R" [x, z])) (.ex fun y => .el (.atom "S" [y]))
      = .all fun x => .ex fun y => .all fun z => .el (.or (.atom "R" [x, z]) (.atom "S" [y])) :=
  rfl
/-- ✱9·08 "(∃y) . ψy . ∨ . (x) . φx : = : (x) : (∃y) . ψy ∨ φx", for the same φ and ψ. -/
example {V : Ty → Type} :
    F9.PF.or (V := V) (.ex fun y => .el (.atom "S" [y])) (.all fun x => .all fun z => .el (.atom "R" [x, z]))
      = .all fun x => .ex fun y => .all fun z => .el (.or (.atom "S" [y]) (.atom "R" [x, z])) :=
  rfl
/-- The earlier reading, kept as `PF.orL`, gives the other order. -/
example {V : Ty → Type} :
    F9.PF.orL (V := V) (.all fun x => .all fun z => .el (.atom "R" [x, z])) (.ex fun y => .el (.atom "S" [y]))
      = .all fun x => .all fun z => .ex fun y => .el (.or (.atom "R" [x, z]) (.atom "S" [y])) :=
  rfl

/-- The agreement of ✱9's method with ✱10's has two hypotheses, a variable of every type and ✱1·2–✱1·6
    for every ✱9 proposition (`Rep`); an external review asked that both be stated wherever it is
    cited. -/
example {V : Ty → Type} {S : Sys} (hV : ∀ τ, Nonempty (V τ)) (hR : F9.Rep S V) (q : QF V) :
    QThm S q ↔ F9.Thm9 S q.toF9 :=
  F9.star9_iff_star10 hV hR q

end PM
