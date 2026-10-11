import PM.Pred.RealOwnOrder
import PM.Pred.RealAsArgument
import PM.Pred.LowestOrder
import PM.Pred.Matrix
import PM.Systems
import PM.Star12
import PM.Orders
import PM.Models.Finite
import PM.Models.Collapse
/-!
  The styles of predicativity side by side (Will, 2026-10-11, open question Q1: do both, as a
  deliberate, documented style choice; docs/TYPES_DESIGN.md, decision 3).

  A style is a reading of "predicative" (`PredReading`: ✱12 p. 172 matrix, the primary style; or
  Introduction p. 56 lowest order, the alternative) combined with a reading of how a real function
  variable counts in the order check (`RealReading`: p. 55, at its own order, the default; or p. 54, as
  an argument; Will, 2026-10-11 ~19:00, open question Q3: both as styles). `Style.of P R` is the style;
  `Sys.full (Style.of P R)` etc. are the systems. There are four styles.

  Every PM theorem here is stated for an arbitrary system, so it holds in every style; StyleCheck.lean
  instantiates each one under every style and system and reports the result. The styles change only
  what comprehension accepts at predicative types, so they differ only in systems with comprehension,
  and (`styles_equiv`, PM/StylesEquiv.lean) not at all once reducibility is present. The golden tests at
  the end of this file show exactly where they differ.
-/
namespace PM
open QF

/-- The two readings of "predicative" (decision 3). -/
inductive PredReading where
  /-- ✱12 p. 172: "A function is said to be predicative when it is a matrix" (PM/Pred/Matrix.lean). The
      primary style. -/
  | matrix
  /-- Introduction p. 56: "of the lowest order compatible with its having that argument"
      (PM/Pred/LowestOrder.lean). The alternative style. -/
  | lowestOrder
  deriving DecidableEq

/-- The readings of how a real (free) function variable counts in the order check (decision 5). -/
inductive RealReading where
  /-- p. 55: at its own order (PM/Pred/RealOwnOrder.lean). The default. -/
  | ownOrder
  /-- p. 54: as an argument, raising the order (PM/Pred/RealAsArgument.lean). -/
  | asArgument
  deriving DecidableEq

/-- The order check of a reading. -/
@[reducible] def RealReading.check : RealReading → OrderCheck
  | .ownOrder => Lvl
  | .asArgument => LvlArg

/-- The style with a reading of "predicative" and a reading of real function variables. -/
@[reducible] def Style.of : PredReading → RealReading → Style
  | .matrix, R => Style.matrix R.check
  | .lowestOrder, R => Style.lowestOrder R.check

/-- The primary style: matrix (✱12 p. 172), real variables at their own order (p. 55). -/
abbrev Style.primary : Style := Style.of .matrix .ownOrder
/-- The alternative style: lowest order (Introduction p. 56), real variables at their own order. -/
abbrev Style.alternative : Style := Style.of .lowestOrder .ownOrder

/-- The matrix style admits no more than the lowest-order style (the matrix test is conjoined with the
    same order check). -/
theorem matrix_adm1_le {V : Ty → Type} (R : RealReading) {a : Ty} {k : Nat} (ψ : V a → QF V)
    (h : (Style.of .matrix R).adm1 k ψ) : (Style.of .lowestOrder R).adm1 k ψ :=
  fun x => (h x).1

theorem matrix_adm2_le {V : Ty → Type} (R : RealReading) {a b : Ty} {k : Nat} (ψ : V a → V b → QF V)
    (h : (Style.of .matrix R).adm2 k ψ) : (Style.of .lowestOrder R).adm2 k ψ :=
  fun x y => (h x y).1

/-- So every theorem of a system in the matrix style is a theorem of the same system in the
    lowest-order style. -/
theorem QThm.matrix_to_lowestOrder {V : Ty → Type} {c r : Bool} (R : RealReading) {p : QF V}
    (h : QThm ⟨c, r, Style.of .matrix R⟩ p) : QThm ⟨c, r, Style.of .lowestOrder R⟩ p :=
  QThm.mono (S := ⟨c, r, Style.of .matrix R⟩) (S' := ⟨c, r, Style.of .lowestOrder R⟩) id id (matrix_adm1_le R) (matrix_adm2_le R) h

/-! ## Golden tests: where the two readings of "predicative" differ

  Each test is a formula ψ and a predicative type; "admits" is the comprehension side condition of the
  style. Negative tests are at the one-element variable family `U`. -/

/-- p. 171 (1): (x) . φ!x as a function of φ!ẑ, at the type of predicative functions of first-order
    functions. The lowest-order style admits it (order 2 = the lowest order for an argument of order 1). -/
example : (Style.of .lowestOrder .ownOrder).adm1 (V := U) (a := Ty.pred1 .ind) 0
    (fun φ => .all fun x => .app1 φ x) :=
  fun _ => .all (by decide) fun _ => .app1 (by decide)

/-- p. 171 (1), matrix style: refused, since (x) . φ!x has an apparent variable. -/
example : ¬ (Style.of .matrix .ownOrder).adm1 (V := U) (a := Ty.pred1 .ind) 0
    (fun φ => .all fun x => .app1 φ x) :=
  fun h => nomatch (h ()).2 rfl

/-- p. 171 (1), at a non-predicative type (`fn1 (pred1 ind) 1`, order 3): both styles admit it; the
    matrix test applies only at predicative types. -/
example : (Style.of .matrix .ownOrder).adm1 (V := U) (a := Ty.pred1 .ind) 1
    (fun φ => .all fun x => .app1 φ x) :=
  fun _ => ⟨.all (by decide) fun _ => .app1 (by decide), fun h => nomatch h⟩

/-- p. 54: (y) . ψ(x, y), a first-order function of x. Lowest-order style: predicative. -/
example : (Style.of .lowestOrder .ownOrder).adm1 (V := U) (a := .ind) 0
    (fun x => .all fun y => .atom "ψ" [x, y]) :=
  fun _ => .all (by decide) fun _ => .atom (by decide)

/-- p. 54, matrix style: not predicative (it is first-order but not a matrix). -/
example : ¬ (Style.of .matrix .ownOrder).adm1 (V := U) (a := .ind) 0
    (fun x => .all fun y => .atom "ψ" [x, y]) :=
  fun h => nomatch (h ()).2 rfl

/-- p. 170: φ!x . ⊃ . ψ!x, φ and ψ real first-order functions: a matrix of order 1 in x. Both styles
    admit it. -/
example : (Style.of .matrix .ownOrder).adm1 (V := U) (a := .ind) 0
    (fun x => imp (.app1 (a := .ind) (k := 0) () x) (.app1 (a := .ind) (k := 0) () x)) :=
  fun _ => ⟨.or (.neg (.app1 (by decide))) (.app1 (by decide)), fun _ => .or (.neg .app1) .app1⟩

/-- p. 171 (3): (φ) . φ!x is of order 2 as a function of x: refused by both styles at `pred1 ind`. -/
example : ¬ (Style.of .lowestOrder .ownOrder).adm1 (V := U) (a := .ind) 0
    (fun x => .all (τ := Ty.pred1 .ind) fun φ => .app1 φ x) :=
  fun h => absurd (h ()) (by decide)

/-! ## Golden tests: where the two readings of real function variables differ (p. 55, p. 54)

  φ!x with φ a real (free) first-order function, as a function of x, at the type `pred1 ind`. -/

/-- p. 55: φ!x with φ fixed is a predicative function of x: admitted (both readings of
    "predicative": it is a matrix of order 1). -/
example : (Style.of .matrix .ownOrder).adm1 (V := U) (a := .ind) 0
    (fun x => .app1 (a := .ind) (k := 0) () x) :=
  fun _ => ⟨.app1 (by decide), fun _ => .app1⟩

/-- p. 54: φ counts as an argument, so φ!x is of order 2: refused at `pred1 ind`, in both readings of
    "predicative". -/
example : ¬ (Style.of .lowestOrder .asArgument).adm1 (V := U) (a := .ind) 0
    (fun x => .app1 (a := .ind) (k := 0) () x) :=
  fun h => absurd (h ()) (by decide)
example : ¬ (Style.of .matrix .asArgument).adm1 (V := U) (a := .ind) 0
    (fun x => .app1 (a := .ind) (k := 0) () x) :=
  fun h => absurd (h ()).1 (by decide)

/-- p. 54 at a type one order higher (`fn1 ind 1`, order 2): admitted. -/
example : (Style.of .matrix .asArgument).adm1 (V := U) (a := .ind) 1
    (fun x => .app1 (a := .ind) (k := 0) () x) :=
  fun _ => ⟨.app1 (by decide), fun h => nomatch h⟩

/-- The function's own argument, applied, is admitted in both readings: (x) . φ!x as a function of φ
    (p. 171 (1)) passes the p. 54 order check at order 2 (φ is the argument, not a parameter). -/
example : (Style.of .lowestOrder .asArgument).adm1 (V := U) (a := Ty.pred1 .ind) 0
    (fun φ => .all fun x => .app1 φ x) :=
  fun _ => .all (by decide) fun _ => .app1 (by decide)

/-- The statement (∃g) : φ!x . ≡ₓ . g!x, g predicative, for a real first-order φ. -/
abbrev realPhi {V : Ty → Type} (φ : V (Ty.pred1 .ind)) : QF V :=
  ex (τ := Ty.pred1 .ind) fun g => fiff (fun x => .app1 φ x) fun x => .app1 g x

/-- p. 55 reading, comprehension only (no ✱12·1): `realPhi` holds. P. 55 STYLES ONLY: in the p. 54
    styles comprehension does not admit φ!x at `pred1 ind` (golden tests above); non-derivability there
    is not proved (it needs a model that sees orders). -/
theorem realPhi_ownOrder_predicative {V : Ty → Type} (P : PredReading) (φ : V (Ty.pred1 .ind)) :
    QThm (Sys.predicative (Style.of P .ownOrder)) (realPhi φ) := by
  cases P
  · exact comprehension1 _ fun _ => ⟨.app1 (Nat.le_refl _), fun _ => .app1⟩
  · exact comprehension1 _ fun _ => .app1 (Nat.le_refl _)

/-- With reducibility, `realPhi` holds in every style (✱12·1). -/
theorem realPhi_reducibility {V : Ty → Type} {S : Sys} [Reducibility S] (φ : V (Ty.pred1 .ind)) :
    QThm S (realPhi φ) :=
  q12_1 _

/-! ## Golden theorems: the same statement in the two readings of "predicative"

  (∃f) : (x) . φ!x . ≡_φ . f!(φ!ẑ), f predicative (p. 171 (1)). -/

/-- The statement: a predicative function of first-order functions agreeing with (x) . φ!x. -/
abbrev p171 {V : Ty → Type} : QF V :=
  ex (τ := Ty.pred1 (Ty.pred1 .ind)) fun f => fiff (fun φ => .all fun x => .app1 φ x) fun φ => .app1 f φ

/-- Lowest-order style, comprehension only (no ✱12·1): `p171` holds. LOWEST-ORDER STYLE ONLY: in the
    matrix style comprehension does not admit (x) . φ!x at a predicative type (golden test above). That
    `p171` is not derivable at all in the matrix-style predicative fragment is NOT proved: it needs a
    model that sees orders (test F4). -/
theorem p171_lowestOrder_predicative {V : Ty → Type} :
    QThm (V := V) (Sys.predicative (Style.of .lowestOrder .ownOrder)) p171 :=
  comprehension1 _ fun _ => .all (by decide) fun _ => .app1 (by decide)

/-- With reducibility, `p171` holds in every style (✱12·1), with or without comprehension. -/
theorem p171_reducibility {V : Ty → Type} {S : Sys} [Reducibility S] : QThm (V := V) S p171 :=
  q12_1 _

/-! ## Consistency in every style

  `consistent S` and `consistent_collapse S` hold for every system; here they are instantiated at
  the full system (comprehension and reducibility) of each style. -/

/-- Consistency of the full system in every style, in the finite coded model (no axioms). -/
theorem consistent_of_style (P : PredReading) (R : RealReading) :
    ¬ QThm (V := twoModel.den) (Sys.full (Style.of P R)) (.atom "p" []) :=
  consistent _

/-- Consistency of the full system in every style, in the collapse model (classical axioms). -/
theorem consistent_collapse_of_style (P : PredReading) (R : RealReading) :
    ¬ QThm (V := (QModel.classical Bool fun _ xs => xs.headD false).den) (Sys.full (Style.of P R))
      (.atom "p" []) :=
  consistent_collapse _

end PM
