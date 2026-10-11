import PM.Orders
/-!
  The order check `LvlArg`, reading p. 54: a real (free) function variable counts as an argument, so
  it raises the order (Will, 2026-10-11 ~19:00, open question Q3: both readings as styles, both must
  pass; docs/TYPES_DESIGN.md, decision 5).

  p. 54 and p. 170 treat φ!x as a function of φ as well as of x: "It will be seen that "φ!x" is a
  function of two variables, namely φ!ẑ and x" (p. 170), of order 2 as such (a second-order matrix,
  p. 171). Read that way, a real function variable occurring in a formula is one of its arguments, and
  "the function in which it occurs is of the n + 1th order" (p. 56) when the variable is of order n. So
  φ!x with φ real of order 1 is of order 2, and comprehension at `pred1 ind` refuses it
  (`realPhi_compr_asArgument`, PM/Pred/Styles.lean). The proposition (∃g) : g!x ≡ₓ φ!x is nevertheless
  a theorem of every system, without comprehension or ✱12·1, since φ itself is a witness
  (`realPhi_every_system`): the reading changes which direct comprehension applications are accepted,
  not the derivability of that proposition.

  The other reading (p. 55: φ counts at its own order) is PM/Pred/RealOwnOrder.lean, the default. The
  only difference is the strict inequality for applied function variables. For an apparent variable it
  changes nothing (its quantifier already requires its order to be below n), and neither for the
  function's own argument (whose order is below that of the function's type); it changes the free
  function variables, the parameters.
-/
namespace PM

/-- `LvlArg p n`: p may be a value of a function of order n when every function variable applied in p
    counts as an argument (p. 54): its order is below n. Otherwise as `Lvl`. -/
inductive LvlArg {V : Ty → Type} : QF V → Nat → Prop where
  | atom {P : String} {xs : List (V .ind)} {n : Nat} : 0 < n → LvlArg (.atom P xs) n
  | app1 {a : Ty} {k n : Nat} {f : V (.fn1 a k)} {x : V a} : (Ty.fn1 a k).ord < n → LvlArg (.app1 f x) n
  | app2 {a b : Ty} {k n : Nat} {f : V (.fn2 a b k)} {x : V a} {y : V b} :
      (Ty.fn2 a b k).ord < n → LvlArg (.app2 f x y) n
  | neg {p : QF V} {n : Nat} : LvlArg p n → LvlArg (.neg p) n
  | or {p q : QF V} {n : Nat} : LvlArg p n → LvlArg q n → LvlArg (.or p q) n
  | all {τ : Ty} {n : Nat} {φ : V τ → QF V} : τ.ord < n → (∀ y, LvlArg (φ y) n) → LvlArg (.all φ) n

/-- The least n such that `p` may be a value of a function of order n, in the p. 54 reading. -/
def QF.orderArg : QF U → Nat
  | .atom _ _ => 1
  | @QF.app1 _ a k _ _ => (Ty.fn1 a k).ord + 1
  | @QF.app2 _ a b k _ _ _ => (Ty.fn2 a b k).ord + 1
  | .neg p => p.orderArg
  | .or p q => max p.orderArg q.orderArg
  | @QF.all _ τ φ => max (τ.ord + 1) (φ ()).orderArg

theorem lvlArg_iff_orderArg (p : QF U) (n : Nat) : LvlArg p n ↔ p.orderArg ≤ n := by
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

instance (p : QF U) (n : Nat) : Decidable (LvlArg p n) :=
  decidable_of_iff _ (lvlArg_iff_orderArg p n).symm

/-- The order of the function x̂ ↦ ψx in the p. 54 reading. -/
def fnOrderArg (a : Ty) (ψ : U a → QF U) : Nat := max (a.ord + 1) (ψ ()).orderArg

/-- p. 54: φ!x with φ real, as a function of x, has order 2 in this reading: the same as φ!x as a
    function of (φ, x) (`fnOrder2`, PM/Pred/Curry.lean). -/
example : fnOrderArg .ind (fun x => .app1 (a := .ind) (k := 0) () x) = 2 := rfl

end PM
