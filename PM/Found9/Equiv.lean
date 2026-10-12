import PM.Found9.ToStar10
import PM.Found9.FromStar10
import PM.Models.Finite
/-!
  ✱9's method and ✱10's: the agreement, its semantics, and the assumption that there are individuals.

  - `star9_iff_star10`: for every ✱10 formula q, `QThm S q ↔ Thm9 S q.toF9`, in every system `S`
    (every combination of comprehension and reducibility, every style), given that every type has a
    variable (`hV`) and that ✱1·2–✱1·6 hold for every ✱9 proposition (`Rep`, PM's claim on p. 142).
    The direction from ✱9 to ✱10 needs only `hV` (`thm9_toQ`, PM/Found9/ToStar10.lean).
  - `thm9_sound`, `consistent9`: ✱9's method is sound in every structure with an individual, and does
    not assert the letter p.
  - `thm9_unsound_empty`: without an individual, ✱9's method asserts a proposition that is false: an
    instance of ✱9·1 whose φ contains an apparent individual variable. In the empty structure there is
    a function of individuals (the empty table), so ✱9·1 applies to it; the definitions ✱9·01, ✱9·05
    then put "(∃w)", w an individual, at the front. ✱10's method is sound there. So `hV` cannot be
    dropped from `thm9_toQ`.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys}

/-- **✱9's method and ✱10's alternative method agree** (PM p. 144), in every system `S`: a ✱10
    formula is a ✱10 theorem exactly when the ✱9 proposition for which it stands is a ✱9 theorem. The
    assumptions: every type has a variable (PM's proofs take an individual for granted), and ✱1·2–✱1·6
    hold in ✱9 for every proposition (`Rep`, PM's claim on p. 142, not proved here). -/
theorem star9_iff_star10 (hV : ∀ τ, Nonempty (V τ)) (hR : Rep S V) (q : QF V) :
    QThm S q ↔ Thm9 S q.toF9 :=
  ⟨qthm_toF9 hR, fun h => qiffMpRule (toQ_toF9 hV q) (thm9_toQ hV h)⟩

/-- In a structure with an individual, every type has a value: a function value is given by `lam1`,
    `lam2` (the structure's abstraction). -/
theorem den_nonempty (M : QModel) (h : Nonempty (M.den .ind)) : ∀ τ, Nonempty (M.den τ)
  | .ind => h
  | .fn1 _ _ => ⟨M.lam1 fun _ => false⟩
  | .fn2 _ _ _ => ⟨M.lam2 fun _ _ => false⟩

/-- Soundness of ✱9's method: in a structure with an individual, every ✱9 theorem is true (read
    through ✱10's primitive ideas, `PF.toQ`), in every system. -/
theorem thm9_sound (M : QModel) (h : Nonempty (M.den .ind)) {p : PF M.den} (hp : Thm9 S p) :
    p.toQ.eval M = true :=
  qsound M (thm9_toQ (den_nonempty M h) hp)

/-- Consistency of ✱9's method: the letter p is not a ✱9 theorem (at the variables of `twoModel`), in
    any system. -/
theorem consistent9 (S : Sys) : ¬ Thm9 (V := twoModel.den) S (.el (.atom "p" [])) :=
  fun h => by have := thm9_sound twoModel ⟨true⟩ h; cases this

/-- Without individuals ✱9's method is unsound: at the variables of `emptyModel` (no individual, one
    function of individuals), ✱9·1 with φf = (w) . Pw (w an individual) asserts a proposition that is
    false there. So it is not a ✱10 theorem: `thm9_toQ` fails without `hV`. -/
theorem thm9_unsound_empty {S : Sys} :
    ¬ ∀ (V : Ty → Type) (p : PF V), Thm9 S p → QThm S p.toQ :=
  fun h => not_qthm_of_countermodel emptyModel rfl
    (h emptyModel.den _
      (Thm9.ex1 (τ := Ty.pred1 .ind) (fun _ => .all (τ := .ind) fun w => .el (.atom "P" [w]))
        (emptyModel.lam1 fun _ => false)))

end PM.F9
