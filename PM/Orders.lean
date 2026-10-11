import PM.Quant
import PM.Pred.RealOwnOrder
/-!
  Orders: a decidable order checker and golden tests (docs/TYPES_DESIGN.md, tests F1 and F2).

  The collapse model cannot see orders (`qsound` never uses `Lvl`), so the order discipline is tested
  here, syntactically. A formula is checked at the one-element variable family `U` (every type has the
  single variable `()`), where `Lvl` is decidable: `QF.order p` is the least n with `Lvl p n`
  (`lvl_iff_order`). This is exact for formulas written uniformly in the variable family, which every
  formula of this project is; it is a checking device only. (`QThm` at `U` itself is degenerate:
  PM/Trap.lean.)

  The order of the *function* x̂ ↦ ψx with an argument of type `a` is `fnOrder a ψ`: one above the order
  of the argument, or the order of ψx, whichever is larger (Introduction p. 56: "If the highest order of
  variable occurring in a function, whether as argument or as apparent variable, is a function of the
  nth order, then the function in which it occurs is of the n + 1th order").
-/
namespace PM
open QF

/-- The one-element variable family. -/
abbrev U : Ty → Type := fun _ => Unit

/-- The least n such that `p` may be a value of a function of order n. -/
def QF.order : QF U → Nat
  | .atom _ _ => 1
  | @QF.app1 _ a k _ _ => (Ty.fn1 a k).ord
  | @QF.app2 _ a b k _ _ _ => (Ty.fn2 a b k).ord
  | .neg p => p.order
  | .or p q => max p.order q.order
  | @QF.all _ τ φ => max (τ.ord + 1) (φ ()).order

/-! `max` lemmas proved from `Nat`'s definition of `max` (core's versions use `propext`). -/
private theorem max_le' {a b c : Nat} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c := by
  show (if a ≤ b then b else a) ≤ c
  split <;> assumption
private theorem le_max_left' (a b : Nat) : a ≤ max a b := by
  show a ≤ (if a ≤ b then b else a)
  split
  · assumption
  · exact Nat.le_refl a
private theorem le_max_right' (a b : Nat) : b ≤ max a b := by
  show b ≤ (if a ≤ b then b else a)
  split
  · exact Nat.le_refl b
  · next h => exact Nat.le_of_lt (Nat.lt_of_not_le h)
private theorem max_le_l {a b c : Nat} (h : max a b ≤ c) : a ≤ c := Nat.le_trans (le_max_left' a b) h
private theorem max_le_r {a b c : Nat} (h : max a b ≤ c) : b ≤ c := Nat.le_trans (le_max_right' a b) h

theorem lvl_iff_order (p : QF U) (n : Nat) : Lvl p n ↔ p.order ≤ n := by
  induction p generalizing n with
  | atom P xs => exact ⟨fun h => by cases h; assumption, fun h => .atom h⟩
  | app1 f x => exact ⟨fun h => by cases h; assumption, fun h => .app1 h⟩
  | app2 f x y => exact ⟨fun h => by cases h; assumption, fun h => .app2 h⟩
  | neg p ih => exact ⟨fun h => by cases h; exact (ih n).mp ‹_›, fun h => .neg ((ih n).mpr h)⟩
  | or p q ihp ihq =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with
      | or hp hq => exact max_le' ((ihp n).mp hp) ((ihq n).mp hq)
    · exact .or ((ihp n).mpr (max_le_l h)) ((ihq n).mpr (max_le_r h))
  | all φ ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with
      | all hτ hφ => exact max_le' hτ ((ih () n).mp (hφ ()))
    · exact .all (max_le_l h) fun y => (ih y n).mpr (max_le_r h)

instance (p : QF U) (n : Nat) : Decidable (Lvl p n) :=
  decidable_of_iff _ (lvl_iff_order p n).symm

/-- The order of the function x̂ ↦ ψx whose argument has type `a` (Introduction p. 56). -/
def fnOrder (a : Ty) (ψ : U a → QF U) : Nat := max (a.ord + 1) (ψ ()).order

/-- The function x̂ ↦ ψx is predicative in the sense of Introduction p. 56: "of the lowest order
    compatible with its having that argument". -/
def predicativeP56 (a : Ty) (ψ : U a → QF U) : Bool := fnOrder a ψ == a.ord + 1

/-- The function x̂ ↦ ψx is a matrix (✱12, p. 172: "A function is said to be predicative when it is a
    matrix", i.e. contains no apparent variable). -/
def QF.isMatrix : QF U → Bool
  | .atom _ _ => true
  | .app1 _ _ => true
  | .app2 _ _ _ => true
  | .neg p => p.isMatrix
  | .or p q => p.isMatrix && q.isMatrix
  | .all _ => false

/-! ## Orders of types (Introduction pp. 53–56; ✱12 p. 174: arguments of any order) -/

example : Ty.ind.ord = 0 := rfl
example : (Ty.pred1 .ind).ord = 1 := rfl                     -- φ!x̂, x an individual: first order
example : (Ty.pred1 (Ty.pred1 .ind)).ord = 2 := rfl          -- f!(φ̂!ẑ): second order (p. 55)
example : (Ty.pred2 (Ty.pred1 .ind) .ind).ord = 2 := rfl     -- f!(φ̂!ẑ, x̂) (p. 55)
example : (Ty.fn1 .ind 1).ord = 2 := rfl                     -- a second-order function of individuals
example : (Ty.pred1 (.fn1 .ind 1)).ord = 3 := rfl            -- predicative, of an argument of order 2 (p. 174)

/-! ## Golden tests, Introduction pp. 54–56

  Letters: ψ, χ (atoms) are matrices of individuals; φ, ψ' are first-order functions (`Ty.pred1 .ind`);
  f, g, F are predicative functions of first-order functions. In each test, `()` is the real variable. -/

/-- p. 54: (y) . ψ(x, y) is a first-order function of x. -/
example : fnOrder .ind (fun x => .all fun y => .atom "ψ" [x, y]) = 1 := rfl
/-- p. 54: (y) : (∃z) . χ(x, y, z) is a first-order function of x. -/
example : fnOrder .ind (fun x => .all fun y => ex fun z => .atom "χ" [x, y, z]) = 1 := rfl
/-- p. 54: "φ!x implies φ!a with all possible values of φ" is a function of x but "not a function of the
    form φ!x": it is of order 2. -/
example : fnOrder .ind (fun x => .all (τ := Ty.pred1 .ind) fun φ => imp (.app1 φ x) (.app1 φ ())) = 2 := rfl
example : ¬ Lvl (V := U) (.all (τ := Ty.pred1 .ind) fun φ => imp (.app1 φ ()) (.app1 φ ())) 1 := by decide
/-- p. 55: (φ) . g(φ!ẑ, ψ!ẑ) is a function of ψ!ẑ; of order 2. -/
example : fnOrder (Ty.pred1 .ind)
    (fun ψ' => .all (τ := Ty.pred1 .ind) fun φ =>
      .app2 (a := Ty.pred1 .ind) (b := Ty.pred1 .ind) (k := 0) () φ ψ') = 2 := rfl
/-- p. 55: (x) . F(φ!ẑ, x) is a function of φ!ẑ; of order 2. -/
example : fnOrder (Ty.pred1 .ind)
    (fun φ => .all fun x => .app2 (a := Ty.pred1 .ind) (b := .ind) (k := 0) () φ x) = 2 := rfl
/-- p. 55: (φ) . F(φ!ẑ, x) is a function of x; of order 2, so not predicative (p. 56). -/
example : fnOrder .ind
    (fun x => .all (τ := Ty.pred1 .ind) fun φ => .app2 (a := Ty.pred1 .ind) (b := .ind) (k := 0) () φ x) = 2 := rfl
example : predicativeP56 .ind
    (fun x => .all (τ := Ty.pred1 .ind) fun φ => .app2 (a := Ty.pred1 .ind) (b := .ind) (k := 0) () φ x) = false := rfl
/-- p. 55: f!(φ!ẑ) is a function of φ!ẑ of order 2 (predicative: "predicative functions of first-order
    functions"), and not of order 1. -/
example : fnOrder (Ty.pred1 .ind) (fun φ => .app1 (a := Ty.pred1 .ind) (k := 0) () φ) = 2 := rfl
example : predicativeP56 (Ty.pred1 .ind) (fun φ => .app1 (a := Ty.pred1 .ind) (k := 0) () φ) = true := rfl
example : ¬ Lvl (V := U) (.app1 (a := Ty.pred1 .ind) (k := 0) () ()) 1 := by decide
/-- p. 56: a function of an individual of order 3: (f) . f!(φ!ẑ) . φ!x … with f of order 2 apparent. -/
example : fnOrder .ind (fun x => .all (τ := Ty.pred1 (Ty.pred1 .ind)) fun f =>
    QF.and (.app1 f ()) (.app1 (a := .ind) (k := 0) () x)) = 3 := rfl

/-! ## Golden tests, ✱12 pp. 170–171 -/

/-- p. 170: φ!x is a matrix (no apparent variable). As a function of x it is predicative (p. 55: "the
    assignment of a value to φ gives us a predicative function of x"); as a function of φ!ẑ and x it is
    of order 2, a second-order matrix. -/
example : predicativeP56 .ind (fun x => .app1 (a := .ind) (k := 0) () x) = true := rfl
example : (QF.app1 (V := U) (a := .ind) (k := 0) () ()).isMatrix = true := rfl
example : Lvl (V := U) (.app1 (a := .ind) (k := 0) () ()) (Ty.pred2 (Ty.pred1 .ind) .ind).ord := by decide
/-- p. 170: φ!x ∨ ψ!y, φ!x . ⊃ . ψ!x are matrices of order 1 in x. -/
example : fnOrder .ind (fun x => imp (.app1 (a := .ind) (k := 0) () x) (.app1 (a := .ind) (k := 0) () x)) = 1 := rfl
/-- p. 171 (1): (x) . φ!x is a second-order function of φ!ẑ. By Introduction p. 56 it is predicative
    (order 2 = the lowest order for an argument of order 1); by ✱12 p. 172 it is not, since it is not a
    matrix. This is where the two readings of "predicative" differ (docs/TYPES_DESIGN.md, decision (a)). -/
example : fnOrder (Ty.pred1 .ind) (fun φ => .all fun x => .app1 φ x) = 2 := rfl
example : predicativeP56 (Ty.pred1 .ind) (fun φ => .all fun x => .app1 φ x) = true := rfl
example : (QF.all (V := U) (τ := .ind) fun x => .app1 (a := .ind) (k := 0) () x).isMatrix = false := rfl
/-- p. 171 (1): φ!x . ⊃ₓ . g!x, g constant: a function of φ!ẑ of order 2. -/
example : fnOrder (Ty.pred1 .ind) (fun φ => fimp (fun x => .app1 φ x) fun x => .app1 (a := .ind) (k := 0) () x) = 2 := rfl
/-- p. 171 (3): (φ) . φ!x, (∃φ) . φ!x, φ!x . ⊃_φ . φ!a are functions of the individual x of order 2:
    "Such functions we shall not call predicative". -/
example : fnOrder .ind (fun x => .all (τ := Ty.pred1 .ind) fun φ => .app1 φ x) = 2 := rfl
example : fnOrder .ind (fun x => ex (τ := Ty.pred1 .ind) fun φ => .app1 φ x) = 2 := rfl
example : predicativeP56 .ind (fun x => fimp (τ := Ty.pred1 .ind) (fun φ => .app1 φ x) fun φ => .app1 φ ()) = false := rfl
/-- p. 171 (4): (∃ψ) : φ!x . ≡ . ψ!x, a function of φ!ẑ and x of order 2. -/
example : Lvl (V := U) (ex (τ := Ty.pred1 .ind) fun ψ' => iff (.app1 (a := .ind) (k := 0) () ()) (.app1 ψ' ()))
    (Ty.pred2 (Ty.pred1 .ind) .ind).ord := by decide

/-! ## Comprehension and the check

  In both styles the side condition of comprehension includes `Lvl` (PM/Pred/). The golden tests of
  what each style admits, and where the two differ, are in PM/Pred/Styles.lean. -/

/-- (φ) . φ!x is not of the order of a predicative function of x, so `compr1` cannot give a predicative
    f with f!x ≡ (φ) . φ!x. -/
example : ¬ Lvl (V := U) (.all (τ := Ty.pred1 .ind) fun φ => .app1 φ ()) (Ty.pred1 .ind).ord := by decide

end PM
