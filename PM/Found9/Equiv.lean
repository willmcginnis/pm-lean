import PM.Found9.ToStar10
import PM.Found9.FromStar10
import PM.Models.Finite
/-!
  ✱9's method and ✱10's: the agreement, its semantics, and the assumption that there are individuals.

  - `star9_iff_star10`: for every ✱10 formula q, `QThm S q ↔ Thm9 S R (q.toF9 R.defs)`, in every system
    `S` (every combination of comprehension and reducibility, every style) and under every reading R,
    given that every type has a variable (`hV`) and that ✱1·2–✱1·6 hold for every ✱9 proposition under
    R (`Rep S R`, PM's claim on p. 142).
    The direction from ✱9 to ✱10 needs only `hV` (`thm9_toQ`, PM/Found9/ToStar10.lean).
  - `thm9_sound`, `consistent9`: ✱9's method, under every reading, ✱8·13, Switch and the prenex Switch
    included, is sound in every structure with an individual, and does not assert the letter p.
  - `exch_not_general`, `switch_not_general`: neither ✱8·13 carried over nor Switch is a general
    exchange of quantifiers; with either, ✱9's method does not assert
    (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y).
  - `switch_wide_unsound`: the side condition of Landini's Switch, and of ✱8·13 (the same `Sep`),
    needs our restriction on the quantifiers of A. Read as Landini's words allow, with
    A = (z) . R(x, z) ∨ ∼R(y, z), whose ∨ has every free x on one side and every free y on the other,
    Switch would take a theorem to a proposition false where R is identity on two individuals; so
    `Sep` does not hold for that A. Russell's wording ("all occurrences of x are separated from all
    occurrences of y by a certain stroke") admits the same A, and the same step is one of ✱8·13.
  - `thm9_unsound_empty`: without an individual, ✱9's method asserts a proposition that is false: an
    instance of ✱9·1 whose φ contains an apparent individual variable. In the empty structure there is
    a function of individuals (the empty table), so ✱9·1 applies to it; the definitions ✱9·01, ✱9·05
    then put "(∃w)", w an individual, at the front. ✱10's method is sound there. So `hV` cannot be
    dropped from `thm9_toQ`.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys V} {R : Reading}

/-- **✱9's method and ✱10's alternative method agree** (PM p. 144), in every system `S` and under every
    reading `R` of ✱9: a ✱10 formula is a ✱10 theorem exactly when the ✱9 proposition for which it
    stands under R's definitions is a ✱9 theorem under R. The assumptions: every type has a variable
    (PM's proofs take an individual for granted), and ✱1·2–✱1·6 hold in ✱9 under R for every
    proposition (`Rep S R`, PM's claim on p. 142, not proved here under any reading). -/
theorem star9_iff_star10 (hV : ∀ τ, Nonempty (V τ)) (hR : Rep S R) (q : QF V) :
    QThm S q ↔ Thm9 S R (q.toF9 R.defs) :=
  ⟨qthm_toF9 hV hR, fun h => qiffMpRule (toQ_toF9 hV R.defs q) (thm9_toQ hV h)⟩

/-- In a structure with an individual, every type has a value: a function value is given by `lam1`,
    `lam2` (the structure's abstraction). -/
theorem den_nonempty (M : QModel) (h : Nonempty (M.den .ind)) : ∀ τ, Nonempty (M.den τ)
  | .ind => h
  | .fn1 _ _ => ⟨M.lam1 fun _ => false⟩
  | .fn2 _ _ _ => ⟨M.lam2 fun _ _ => false⟩

/-- Soundness of ✱9's method: in a structure with an individual, every ✱9 theorem is true (read
    through ✱10's primitive ideas, `PF.toQ`), in every system. -/
theorem thm9_sound (M : QModel) (h : Nonempty (M.den .ind)) {S : Sys M.den} {p : PF M.den} (hp : Thm9 S R p) :
    p.toQ.eval M = true :=
  qsound M (thm9_toQ (den_nonempty M h) hp)

/-- Consistency of ✱9's method: the letter p is not a ✱9 theorem (at the variables of `twoModel`), in
    any system. -/
theorem consistent9 (S : Sys twoModel.den) (R : Reading) : ¬ Thm9 S R (.el (.atom "p" [])) :=
  fun h => by have := thm9_sound twoModel ⟨true⟩ h; cases this

/-- Without individuals ✱9's method is unsound: at the variables of `emptyModel` (no individual, one
    function of individuals), ✱9·1 with φf = (w) . Pw (w an individual) asserts a proposition that is
    false there. So it is not a ✱10 theorem: `thm9_toQ` fails without `hV`. -/
theorem thm9_unsound_empty {S : (V : Ty → Type) → Sys V} :
    ¬ ∀ (V : Ty → Type) (p : PF V), Thm9 (S V) R p → QThm (S V) p.toQ := by
  intro h
  have := h emptyModel.den _
    (Thm9.ex1 (τ := Ty.pred1 .ind) (fun _ => .all (τ := .ind) fun w => .el (.atom "P" [w]))
      (emptyModel.lam1 fun _ => false))
  rcases R with ⟨_ | _ | _, _⟩ <;> exact not_qthm_of_countermodel emptyModel rfl this

/-- Two individuals; every letter is identity: R(x, y) holds when x is y. -/
def eqModel : QModel := finModel .bool fun _ xs => !(Bool.xor (xs.headD false) ((xs.drop 1).headD false))

/-- **✱8·13 carried over is not a general exchange of quantifiers.** In reading C, ✱9's method does
    not assert (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y): it is false where R is identity and there
    are two individuals, and with ✱8·13 the method is sound (`thm9_sound`). No ∨ of the matrix R(x, y)
    separates x from y. -/
theorem exch_not_general (S : Sys eqModel.den) :
    ¬ Thm9 S Reading.russell
      (Reading.russell.imp (.all fun x => .ex fun y => .el (.atom "R" [x, y]))
        (.ex fun y => .all fun x => .el (.atom "R" [x, y]))) :=
  fun h => by have := thm9_sound eqModel ⟨true⟩ h; cases this

/-- **Switch is not a general exchange of quantifiers.** In ✱9+ (reading L), ✱9's method does not
    assert (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y): it is false where R is identity and there
    are two individuals, and with Switch the method is sound (`thm9_sound`). Here (∃y) stands in the
    scope of (x), and no connective of R(x, y) has x on one side and y on the other. -/
theorem switch_not_general (S : Sys eqModel.den) :
    ¬ Thm9 S Reading.withSwitch
      (Reading.withSwitch.imp (.all fun x => .ex fun y => .el (.atom "R" [x, y]))
        (.ex fun y => .all fun x => .el (.atom "R" [x, y]))) :=
  fun h => by have := thm9_sound eqModel ⟨true⟩ h; cases this

/-- Landini's side condition on (x)(∃y)A as his words read, without a restriction on the quantifiers of
    A: A is quantifiers over a matrix whose ∨ has every free x on one side and every free y on the
    other; the variables of those quantifiers may occur on both sides. -/
inductive SepWide {V : Ty → Type} {τ σ : Ty} : (V τ → V σ → PF V) → Prop where
  | el (a : V τ → EF V) (b : V σ → EF V) : SepWide fun x y => .el (.or (a x) (b y))
  | all {ρ : Ty} {Z : V ρ → V τ → V σ → PF V} : (∀ z, SepWide (Z z)) →
      SepWide fun x y => .all fun z => Z z x y
  | ex {ρ : Ty} {Z : V ρ → V τ → V σ → PF V} : (∀ z, SepWide (Z z)) →
      SepWide fun x y => .ex fun z => Z z x y

/-- **Switch needs the restriction of `Sep`.** For A = (z) . R(x, z) ∨ ∼R(y, z) the ∨ has every free x
    on its left and every free y on its right (`SepWide`), and (x) : (∃y) : (z) . A is a theorem of ✱9
    under every reading (take y to be x; ✱2·11). But (∃y) : (x) : (z) . A is false where R is identity
    on two individuals (take z to be y and x the other). So Switch read with Landini's words alone is
    unsound, and `Sep`, which asks each quantifier of A to bind a variable of one side only, does not
    hold for this A (else L, which is sound, would assert it). -/
theorem switch_wide_unsound (S : Sys eqModel.den) :
    ∃ Z : eqModel.den .ind → eqModel.den .ind → PF eqModel.den,
      SepWide Z ∧ (∀ R : Reading, Thm9 S R (.all fun x => .ex fun y => Z x y)) ∧
      (PF.ex fun y => .all fun x => Z x y).toQ.eval eqModel = false ∧ ¬ Sep Z := by
  let Z : eqModel.den .ind → eqModel.den .ind → PF eqModel.den := fun x y =>
    .all fun z => .el (.or (.atom "R" [x, z]) (.neg (.atom "R" [y, z])))
  have hfalse : (PF.ex fun y => .all fun x => Z x y).toQ.eval eqModel = false := rfl
  refine ⟨Z, .all fun z => .el (fun x => .atom "R" [x, z]) (fun y => .neg (.atom "R" [y, z])),
    fun R => Thm9.gen fun x => exI x (Thm9.gen fun z =>
      elift (_root_.PM.t2_11 (.var "p")) (esub (.atom "R" [x, z]) (.atom "R" [x, z]) (.atom "R" [x, z]))),
    hfalse, fun hZ => ?_⟩
  have h : Thm9 (V := eqModel.den) S Reading.withSwitch (.ex fun y => .all fun x => Z x y) :=
    Thm9.switch rfl (.here hZ) (Thm9.gen fun x => exI x (Thm9.gen fun z =>
      elift (_root_.PM.t2_11 (.var "p")) (esub (.atom "R" [x, z]) (.atom "R" [x, z]) (.atom "R" [x, z]))))
  have := thm9_sound eqModel ⟨true⟩ h
  rw [hfalse] at this
  cases this

end PM.F9
