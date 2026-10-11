import PM.Star11
import PM.Rules.Reducibility
import PM.Rules.Comprehension
/-!
  ✱12: the hierarchy of types and the axiom of reducibility (1910 print, pp. 168–175).

  ✱12 has no definitions and two numbered propositions, both primitive (p. 174):
    ✱12·1   ⊢ : (∃f) : φx . ≡ₓ . f!x            Pp
    ✱12·11  ⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)  Pp
  Its primitive idea, "'Matrix' or 'predicative function'" (p. 172), is the type `Ty.pred1 a`
  (`Ty.pred2 a b`) of the apparent variable f, the lowest order compatible with the arguments, in both
  styles; which formulas comprehension turns into such a function is the style: matrix (p. 172, the
  primary style) or lowest order (Introduction p. 56), PM/Pred/. ✱12·1 and ✱12·11 have no side
  condition, so they are the same in every style. The rest of ✱12 is prose about types and orders:
  PM/Quant.lean (`Ty`, `Ty.ord`), PM/Pred/ (`Lvl`, `IsMatrix`) and the order tests in PM/Orders.lean.
  docs/TYPES_DESIGN.md gives each reading and its page.

  The primitive propositions are the constructors `QThm.red1` and `QThm.red2`; this file states them
  with PM's macros ≡ₓ (✱10·03, `fiff`) and ≡ₓ,ᵧ (✱11·06, `fiff2`), and proves two checks of the
  reading:
  - `q12_1_var`: ✱12·1 for φ a function *variable* of any order (the shape "φx̂ a function, of any order,
    of an argument x", p. 174, with the order made explicit);
  - `q12_1_of_var`: conversely, the variable form of ✱12·1 plus comprehension at the order of φ gives
    ✱12·1 for every formula φ of that order, without `red1`. So, assuming comprehension, taking φ as a
    schema (a Lean function, like every real function variable of ✱9–✱11) adds nothing beyond "✱12·1 at
    every order" for formulas that are uniformly order-bounded (one order bounds φx for every x);
    exotic HOAS bodies without such a bound are not covered.

  "This assumption with regard to functions is to be made whatever may be the type of their arguments"
  (p. 174): the argument types `a`, `b` are Lean parameters, so each theorem is a schema over types
  (typical ambiguity).
-/
namespace PM
open QF

variable {V : Ty → Type} {S : Sys}

/-- ✱12·1 `⊢ : (∃f) : φx . ≡ₓ . f!x` Pp. φ is a real variable of any order (any formula); f ranges over
    the predicative functions of x's type. -/
theorem q12_1 [Reducibility S] {a : Ty} (φ : V a → QF V) :
    QThm S (ex (τ := Ty.pred1 a) fun f => fiff φ fun x => .app1 f x) :=
  QThm.red1 Reducibility.red φ

/-- ✱12·11 `⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)` Pp. -/
theorem q12_11 [Reducibility S] {a b : Ty} (φ : V a → V b → QF V) :
    QThm S (ex (τ := Ty.pred2 a b) fun f => fiff2 φ fun x y => .app2 f x y) :=
  QThm.red2 Reducibility.red φ

/-- ✱12·1 for a function variable φ of type `fn1 a k` (order `a.ord + 1 + k`): "Let φx̂ be a function,
    of any order, of an argument x" (p. 174). -/
theorem q12_1_var [Reducibility S] {a : Ty} {k : Nat} (φ : V (.fn1 a k)) :
    QThm S (ex (τ := Ty.pred1 a) fun f => fiff (fun x => .app1 φ x) fun x => .app1 f x) :=
  q12_1 fun x => .app1 φ x

/-- ✱12·11 for a function variable φ of type `fn2 a b k`. -/
theorem q12_11_var [Reducibility S] {a b : Ty} {k : Nat} (φ : V (.fn2 a b k)) :
    QThm S (ex (τ := Ty.pred2 a b) fun f => fiff2 (fun x y => .app2 φ x y) fun x y => .app2 f x y) :=
  q12_11 fun x y => .app2 φ x y

/-- The variable form of ✱12·1 at order `a.ord + 1 + k`, with comprehension at that order, gives ✱12·1
    for any formula ψ of that order. Uses `compr1`, not `red1` (RedCheck.lean). From (∃g) : ψx ≡ₓ g x
    (comprehension) and, for each g, (∃f) : g x ≡ₓ f!x (the hypothesis), ✱10·301 joins the two
    equivalences under (∃f) (✱10·11·28) and ✱10·23 removes g. -/
theorem q12_1_of_var [Comprehension S] {a : Ty} {k : Nat}
    (hvar : ∀ g : V (.fn1 a k),
      QThm S (ex (τ := Ty.pred1 a) fun f => fiff (fun x => .app1 g x) fun x => .app1 f x))
    (ψ : V a → QF V) (hψ : S.style.adm1 k ψ) :
    QThm S (ex (τ := Ty.pred1 a) fun f => fiff ψ fun x => .app1 f x) :=
  let G : QF V := ex (τ := Ty.pred1 a) fun f => fiff ψ fun x => .app1 f x
  have step : ∀ g : V (.fn1 a k), QThm S (imp (fiff ψ fun x => .app1 g x) G) := fun g =>
    have h1 : ∀ f : V (Ty.pred1 a), QThm S (imp (fiff ψ fun x => .app1 g x)
        (imp (fiff (fun x => .app1 g x) fun x => .app1 f x) (fiff ψ fun x => .app1 f x))) :=
      fun f => QThm.mp (q10_301 ψ (fun x => .app1 g x) (fun x => .app1 f x)) (QL.t3_3 _ _ _)  -- ✱10·301 . Exp
    have h2 := qsyl (q10_11_21 h1) (q10_28 _ _)                                         -- ✱10·11·21 . ✱10·28
    QThm.mp (hvar g) (QThm.mp h2 (QL.t2_04 _ _ _))                                      -- Comm
  have h6 : QThm S (imp (ex (τ := .fn1 a k) fun g => fiff ψ fun x => .app1 g x) G) :=
    QThm.mp (q10_11 step) (qiffMp (q10_23 _ G))                                         -- ✱10·11·23
  QThm.mp (comprehension1 ψ hψ) h6                                                         -- comprehension

end PM
