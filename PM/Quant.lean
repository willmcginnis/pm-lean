import PM.Basic
/-!
  Principia Mathematica ✱9–✱10: propositions containing apparent variables; with the ramified types,
  comprehension and the axiom of reducibility of ✱12, and the semantics (soundness, consistency).

  This file follows PM's "alternative method" of ✱10 (pp. 143–144): `∼`, `∨` and `(x).φx` are primitive
  for propositions of any order, and the primitive propositions of ✱1 hold for them. ✱10 states:
  "✱10·1 is ✱9·2, ✱10·11 is ✱9·13, ✱10·12 is ✱9·25, ✱10·121 is ✱9·14, and ✱10·122 is ✱9·15. These five
  propositions must all be taken as primitive propositions in the alternative method; on the other hand,
  ✱9·1 and ✱9·11 are not required as primitive propositions in the alternative method." (p. 144)
  See docs/STAR9_DESIGN.md for why this method was chosen over ✱9's.

  Syntax. `QF V` is a formula over a family `V : Ty → Type` of variables, one type of variables for
  each type of argument (`Ty`). An elementary proposition is a predicate letter applied to a list of
  individual variables; `atom "p" []` is a propositional letter. A function φx̂ whose argument has type τ
  is a Lean function `φ : V τ → QF V`, and its value at the variable `y` is `φ y`; `(x).φx` is `.all φ`.
  (This binding style is known as PHOAS. It needs no substitution and no renaming of variables, so the
  apparent variable is "only nominal", as in PM.)

  Types (✱12, pp. 168–175; Introduction pp. 53–56). `Ty` has individuals and the ramified types of
  functions of one and of two arguments, with orders: `fn1 a k` is a function of an argument of type `a`
  whose order is k above the lowest order compatible with that argument (`Ty.ord`, Introduction p. 56);
  `pred1 a = fn1 a 0` is the type of predicative functions φ!x̂ of an `a`. Every theorem of ✱9–✱11 is
  stated for an arbitrary type τ of each apparent variable, so it holds at every one of these types
  (typical ambiguity as Lean parameters). docs/TYPES_DESIGN.md gives each choice and the page it rests on.

  Primitive ideas and definitions:
    ∼, ∨, (x).φx                                     primitive (✱10, alternative method)
    ✱1·01  p ⊃ q . = . ∼p ∨ q                        macro, as in PM/Basic.lean
    ✱3·01, ✱4·01                                     macros, as in PM/Basic.lean
    ✱10·01 (∃x).φx . = . ∼(x).∼φx                    macro `QF.ex`
    ✱10·02 φx ⊃ₓ ψx . = . (x).φx ⊃ ψx                macro `QF.fimp`
    ✱10·03 φx ≡ₓ ψx . = . (x).φx ≡ ψx                macro `QF.fiff`

  Primitive propositions (`QThm`):
    ✱1·1 (= ✱9·12, "what is implied by a true premiss is true"), ✱1·2–✱1·6 for all formulas;
    ✱10·1   ⊢ : (x).φx . ⊃ . φy                       (`QThm.inst`)
    ✱10·11  If φy is true whatever possible argument y may be, then (x).φx is true.   (`QThm.gen`)
    ✱10·12  ⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx  (`QThm.distrib`)
    ✱10·121 (significance of φa for a of the same type as x) and ✱10·122 (if there is a proposition φa
    there is a function φx̂) are built into the syntax: every `φ : V τ → QF V` is a function, and every
    `φ a` with `a : V τ` is a formula.
  Opt-in rules, only in a system `S` that has them (`QThm S`; PM/Rules/, PM/Systems.lean):
    Comprehension at a function type (`QThm.compr1`, `QThm.compr2`; class `Comprehension S`): a formula
    ψx that the system's style admits at a function type determines a function variable of that type
    formally equivalent to it. This is our reading of ✱10·122 together with ✱10·24 at a function type;
    the styles (what is admitted) are the modules under PM/Pred/.
    ✱12·1   ⊢ : (∃f) : φx . ≡ₓ . f!x            Pp (p. 174)   (`QThm.red1`; class `Reducibility S`)
    ✱12·11  ⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)  Pp (p. 174)   (`QThm.red2`)
    φ is a real variable of any order (a Lean function `V a → QF V`, as for every real function variable
    of ✱9–✱11); f is an apparent variable of the predicative type. A theorem that uses a rule takes its
    class in its signature; RedCheck.lean cross-checks this against the proofs.
-/
namespace PM

/-- Types of arguments (✱12; Introduction pp. 53–56). `fn1 a k` is the type of functions of one
    argument of type `a` whose order exceeds the lowest order compatible with that argument by `k`;
    `fn2 a b k` likewise for two arguments. There is no type of propositions (✱12, p. 172: propositions
    "will no longer" occur as variables). -/
inductive Ty where
  | ind : Ty
  | fn1 : Ty → Nat → Ty
  | fn2 : Ty → Ty → Nat → Ty
  deriving DecidableEq

/-- The order of a type (Introduction p. 56): individuals 0; a function one above the highest order of
    its arguments, plus its excess `k`. -/
def Ty.ord : Ty → Nat
  | .ind => 0
  | .fn1 a k => a.ord + 1 + k
  | .fn2 a b k => max a.ord b.ord + 1 + k

/-- The predicative functions of an `a`: "of the next order above that of its argument, i.e. of the
    lowest order compatible with its having that argument" (Introduction p. 56). φ!x̂ in PM. -/
abbrev Ty.pred1 (a : Ty) : Ty := .fn1 a 0
/-- The predicative functions of an `a` and a `b` (the lowest order compatible with both; p. 56). -/
abbrev Ty.pred2 (a b : Ty) : Ty := .fn2 a b 0

/-- Formulas of ✱10 over a family `V` of variables, `V τ` being the variables of type τ. -/
inductive QF (V : Ty → Type) where
  | atom : String → List (V .ind) → QF V
  /-- `app1 f x` is f x (f!x when f is predicative). -/
  | app1 {a : Ty} {k : Nat} : V (.fn1 a k) → V a → QF V
  /-- `app2 f x y` is f(x, y) (f!(x, y) when f is predicative). -/
  | app2 {a b : Ty} {k : Nat} : V (.fn2 a b k) → V a → V b → QF V
  | neg  : QF V → QF V
  | or   : QF V → QF V → QF V
  | all  {τ : Ty} : (V τ → QF V) → QF V

namespace QF
variable {V : Ty → Type}
@[reducible] def imp (p q : QF V) : QF V := .or (.neg p) q                    -- ✱1·01
@[reducible] def and (p q : QF V) : QF V := .neg (.or (.neg p) (.neg q))      -- ✱3·01
@[reducible] def iff (p q : QF V) : QF V := QF.and (QF.imp p q) (QF.imp q p)  -- ✱4·01
@[reducible] def ex {τ : Ty} (φ : V τ → QF V) : QF V := .neg (.all fun x => .neg (φ x))  -- ✱10·01
@[reducible] def fimp {τ : Ty} (φ ψ : V τ → QF V) : QF V := .all fun x => QF.imp (φ x) (ψ x)  -- ✱10·02
@[reducible] def fiff {τ : Ty} (φ ψ : V τ → QF V) : QF V := .all fun x => QF.iff (φ x) (ψ x)  -- ✱10·03
end QF

/-- A style of predicativity over the variables `V`: what comprehension accepts. `adm1 k ψ` holds when
    the formula ψx (x of type `a`) may be taken as the values of a function variable of type `fn1 a k`;
    `adm2 k ψ` likewise for `fn2 a b k`. Each reading of PM's text is its own module under PM/Pred/,
    defined for every `V` (docs/TYPES_DESIGN.md, decisions 3, 5 and 13). -/
structure Style (V : Ty → Type) where
  adm1 : {a : Ty} → Nat → (V a → QF V) → Prop
  adm2 : {a b : Ty} → Nat → (V a → V b → QF V) → Prop

/-- An order check: `L p n` when p may be a value of a function of order n. Two readings of how a
    real function variable counts (p. 55, p. 54) are the modules PM/Pred/RealOwnOrder.lean and
    PM/Pred/RealAsArgument.lean. -/
abbrev OrderCheck : Type 1 := {V : Ty → Type} → QF V → Nat → Prop

/-- A proof system over the variables `V`: which rules beyond ✱1–✱11 it has, and its style of
    predicativity. The rules are opt-in capabilities, each its own module with its PM warrant (PM/Rules/):
    `compr` is comprehension (class `Comprehension S`), `red` the axiom of reducibility ✱12·1, ✱12·11
    (class `Reducibility S`).
    Lean enforces that a rule is enabled: its constructors need a proof of `S.red = true` (resp.
    `S.compr = true`). By convention a theorem that uses a rule gets that proof from the class in its
    signature, which shows the dependency; RedCheck.lean checks the convention. A theorem that uses no
    rule holds in every system. -/
structure Sys (V : Ty → Type) where
  compr : Bool
  red : Bool
  style : Style V

open QF in
/-- Asserted propositions of ✱10's alternative method in the system `S`: ✱1·1–✱1·6, ✱10·1, ✱10·11,
    ✱10·12 always; comprehension at function types if `S.compr`; the axiom of reducibility (✱12·1,
    ✱12·11) if `S.red`. -/
inductive QThm {V : Ty → Type} (S : Sys V) : QF V → Prop where
  | mp      {p q : QF V} : QThm S p → QThm S (imp p q) → QThm S q                 -- ✱1·1, ✱9·12
  | taut    (p : QF V)     : QThm S (imp (.or p p) p)                              -- ✱1·2
  | add     (p q : QF V)   : QThm S (imp q (.or p q))                              -- ✱1·3
  | perm    (p q : QF V)   : QThm S (imp (.or p q) (.or q p))                      -- ✱1·4
  | assoc   (p q r : QF V) : QThm S (imp (.or p (.or q r)) (.or q (.or p r)))      -- ✱1·5
  | sum     (p q r : QF V) : QThm S (imp (imp q r) (imp (.or p q) (.or p r)))      -- ✱1·6
  | inst    {τ : Ty} (φ : V τ → QF V) (y : V τ) : QThm S (imp (.all φ) (φ y))       -- ✱10·1
  | gen     {τ : Ty} {φ : V τ → QF V} : (∀ y, QThm S (φ y)) → QThm S (.all φ)     -- ✱10·11
  | distrib {τ : Ty} (p : QF V) (φ : V τ → QF V) :
      QThm S (imp (.all fun x => .or p (φ x)) (.or p (.all φ)))                    -- ✱10·12
  /-- Comprehension: a formula ψx that the style admits at `fn1 a k` is formally equivalent to some
      function of that type (✱10·122 with ✱10·24; PM/Rules/Comprehension.lean). -/
  | compr1  {a : Ty} {k : Nat} (_ : S.compr = true) (ψ : V a → QF V) (_ : S.style.adm1 k ψ) :
      QThm S (ex (τ := .fn1 a k) fun f => fiff ψ fun x => .app1 f x)
  /-- Comprehension for functions of two arguments. -/
  | compr2  {a b : Ty} {k : Nat} (_ : S.compr = true) (ψ : V a → V b → QF V) (_ : S.style.adm2 k ψ) :
      QThm S (ex (τ := .fn2 a b k) fun f => .all fun x => .all fun y => iff (ψ x y) (.app2 f x y))
  /-- ✱12·1 `⊢ : (∃f) : φx . ≡ₓ . f!x` Pp (p. 174). φ of any order; f predicative
      (PM/Rules/Reducibility.lean). -/
  | red1    {a : Ty} (_ : S.red = true) (φ : V a → QF V) :
      QThm S (ex (τ := Ty.pred1 a) fun f => fiff φ fun x => .app1 f x)
  /-- ✱12·11 `⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)` Pp (p. 174). -/
  | red2    {a b : Ty} (_ : S.red = true) (φ : V a → V b → QF V) :
      QThm S (ex (τ := Ty.pred2 a b) fun f => .all fun x => .all fun y => iff (φ x y) (.app2 f x y))

/-- Monotonicity: a system with more rules, and a style that admits more, proves more. -/
theorem QThm.mono {V : Ty → Type} {S S' : Sys V} (hc : S.compr = true → S'.compr = true)
    (hr : S.red = true → S'.red = true)
    (h1 : ∀ {a : Ty} {k : Nat} (ψ : V a → QF V), S.style.adm1 k ψ → S'.style.adm1 k ψ)
    (h2 : ∀ {a b : Ty} {k : Nat} (ψ : V a → V b → QF V), S.style.adm2 k ψ → S'.style.adm2 k ψ)
    {p : QF V} (h : QThm S p) : QThm S' p := by
  induction h with
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | taut p => exact .taut p
  | add p q => exact .add p q
  | perm p q => exact .perm p q
  | assoc p q r => exact .assoc p q r
  | sum p q r => exact .sum p q r
  | inst φ y => exact .inst φ y
  | gen _ ih => exact .gen ih
  | distrib p φ => exact .distrib p φ
  | compr1 hS ψ hψ => exact .compr1 (hc hS) ψ (h1 ψ hψ)
  | compr2 hS ψ hψ => exact .compr2 (hc hS) ψ (h2 ψ hψ)
  | red1 hS φ => exact .red1 (hr hS) φ
  | red2 hS φ => exact .red2 (hr hS) φ

/-! ## Semantics and soundness

  A structure gives each type a set of values, application of a function value to arguments, and, for
  every Boolean function of the arguments, a value that applies as that function (`lam1`, `lam2`). Such
  structures cannot see orders: `qsound` never uses a style's side condition, so the order discipline is
  tested syntactically (PM/Orders.lean, PM/Pred/), not by a model. Two kinds of structure are built:
  - the collapse model (PM/Models/Collapse.lean): every type of functions is the full function space,
    with classical quantifiers over it; the general model, for any domain of individuals;
  - the finite coded model (PM/Models/Finite.lean): function values are truth tables and every
    quantifier is computed by enumeration, so consistency and the counter-models use no axioms. -/

/-- A structure: values for each type, application and abstraction for function types, a truth
    value for each elementary proposition, and for each type τ the universal quantifier as a Boolean
    oracle `A τ` (`A τ f` is true iff `f` is true of every value of type τ). -/
structure QModel where
  den  : Ty → Type
  R    : String → List (den .ind) → Bool
  ap1  : {a : Ty} → {k : Nat} → den (.fn1 a k) → den a → Bool
  ap2  : {a b : Ty} → {k : Nat} → den (.fn2 a b k) → den a → den b → Bool
  lam1 : {a : Ty} → {k : Nat} → (den a → Bool) → den (.fn1 a k)
  lam2 : {a b : Ty} → {k : Nat} → (den a → den b → Bool) → den (.fn2 a b k)
  ap_lam1 : ∀ {a : Ty} {k : Nat} (g : den a → Bool) (x : den a), ap1 (lam1 (k := k) g) x = g x
  ap_lam2 : ∀ {a b : Ty} {k : Nat} (g : den a → den b → Bool) (x : den a) (y : den b),
    ap2 (lam2 (k := k) g) x y = g x y
  A    : (τ : Ty) → (den τ → Bool) → Bool
  hA   : ∀ τ f, A τ f = true ↔ ∀ d, f d = true

/-- Truth value of a formula whose real variables are already values of the structure. -/
def QF.eval (M : QModel) : QF M.den → Bool
  | .atom P xs    => M.R P xs
  | .app1 f x     => M.ap1 f x
  | .app2 f x y   => M.ap2 f x y
  | .neg p        => !(QF.eval M p)
  | .or p q       => QF.eval M p || QF.eval M q
  | @QF.all _ τ φ => M.A τ (fun d => QF.eval M (φ d))

/-- An existential is true when it has a true instance (the witness used for comprehension and
    ✱12·1 / ✱12·11 in `qsound`). -/
private theorem eval_ex_of (M : QModel) (τ : Ty) (g : M.den τ → Bool) (d : M.den τ)
    (h : g d = true) : (!(M.A τ fun x => !(g x))) = true := by
  cases hA : M.A τ (fun x => !(g x)) with
  | false => rfl
  | true => have := (M.hA _ _).mp hA d; rw [h] at this; cases this

private theorem iff_refl_bool (b : Bool) : (!(!(!b || b) || !(!b || b))) = true := by
  cases b <;> rfl

/-- Soundness: every `QThm S` is true in every structure, at the structure's own variables, for every
    system `S` (every combination of rules and every style). -/
theorem qsound (M : QModel) {S : Sys M.den} {p : QF M.den} (h : QThm S p) : p.eval M = true := by
  induction h with
  | @mp p q _ _ ih1 ih2 =>
    have h2 : (!(p.eval M) || q.eval M) = true := ih2
    rw [ih1] at h2; exact h2
  | taut p =>
    show (!(p.eval M || p.eval M) || p.eval M) = true
    cases p.eval M <;> rfl
  | add p q =>
    show (!(q.eval M) || (p.eval M || q.eval M)) = true
    cases p.eval M <;> cases q.eval M <;> rfl
  | perm p q =>
    show (!(p.eval M || q.eval M) || (q.eval M || p.eval M)) = true
    cases p.eval M <;> cases q.eval M <;> rfl
  | assoc p q r =>
    show (!(p.eval M || (q.eval M || r.eval M)) || (q.eval M || (p.eval M || r.eval M))) = true
    cases p.eval M <;> cases q.eval M <;> cases r.eval M <;> rfl
  | sum p q r =>
    show (!(!(q.eval M) || r.eval M) || (!(p.eval M || q.eval M) || (p.eval M || r.eval M))) = true
    cases p.eval M <;> cases q.eval M <;> cases r.eval M <;> rfl
  | @inst τ φ y =>
    show (!(M.A τ fun d => (φ d).eval M) || (φ y).eval M) = true
    cases hA : M.A τ (fun d => (φ d).eval M) with
    | false => rfl
    | true => rw [(M.hA _ _).mp hA y]; rfl
  | gen _ ih => exact (M.hA _ _).mpr ih
  | @distrib τ p φ =>
    show (!(M.A τ fun d => p.eval M || (φ d).eval M) || (p.eval M || M.A τ fun d => (φ d).eval M)) = true
    cases p.eval M with
    | true =>
      show (!(M.A τ fun d => true || (φ d).eval M) || true) = true
      cases M.A τ (fun d => true || (φ d).eval M) <;> rfl
    | false =>
      show (!(M.A τ fun d => (φ d).eval M) || M.A τ fun d => (φ d).eval M) = true
      cases M.A τ (fun d => (φ d).eval M) <;> rfl
  -- The witness for comprehension and for ✱12·1 / ✱12·11 is the value that applies as x ↦ ⟦φx⟧; its
  -- order is not seen by the structure, and the style's side condition is not used.
  | @compr1 a k _ ψ _ =>
    refine eval_ex_of M (.fn1 a k) _ (M.lam1 fun x => (ψ x).eval M) ((M.hA _ _).mpr fun x => ?_)
    show (!(!(!((ψ x).eval M) || M.ap1 (M.lam1 fun x => (ψ x).eval M) x) ||
      !(!(M.ap1 (M.lam1 fun x => (ψ x).eval M) x) || (ψ x).eval M))) = true
    rw [M.ap_lam1]; exact iff_refl_bool _
  | @compr2 a b k _ ψ _ =>
    refine eval_ex_of M (.fn2 a b k) _ (M.lam2 fun x y => (ψ x y).eval M)
      ((M.hA _ _).mpr fun x => (M.hA _ _).mpr fun y => ?_)
    show (!(!(!((ψ x y).eval M) || M.ap2 (M.lam2 fun x y => (ψ x y).eval M) x y) ||
      !(!(M.ap2 (M.lam2 fun x y => (ψ x y).eval M) x y) || (ψ x y).eval M))) = true
    rw [M.ap_lam2]; exact iff_refl_bool _
  | @red1 a _ φ =>
    refine eval_ex_of M (Ty.pred1 a) _ (M.lam1 fun x => (φ x).eval M) ((M.hA _ _).mpr fun x => ?_)
    show (!(!(!((φ x).eval M) || M.ap1 (M.lam1 fun x => (φ x).eval M) x) ||
      !(!(M.ap1 (M.lam1 fun x => (φ x).eval M) x) || (φ x).eval M))) = true
    rw [M.ap_lam1]; exact iff_refl_bool _
  | @red2 a b _ φ =>
    refine eval_ex_of M (Ty.pred2 a b) _ (M.lam2 fun x y => (φ x y).eval M)
      ((M.hA _ _).mpr fun x => (M.hA _ _).mpr fun y => ?_)
    show (!(!(!((φ x y).eval M) || M.ap2 (M.lam2 fun x y => (φ x y).eval M) x y) ||
      !(!(M.ap2 (M.lam2 fun x y => (φ x y).eval M) x y) || (φ x y).eval M))) = true
    rw [M.ap_lam2]; exact iff_refl_bool _

/-- A formula false in some structure is not a theorem (at that structure's variables), in any system. -/
theorem not_qthm_of_countermodel (M : QModel) {p : QF M.den} (hv : p.eval M = false) {S : Sys M.den} : ¬ QThm S p :=
  fun h => by have := qsound M h; rw [hv] at this; cases this

/-! ## ✱1–✱5 apply to propositions containing apparent variables

  ✱10 (p. 144) assumes "the applicability to propositions containing apparent variables of analogues of
  the primitive ideas and propositions of ✱1, and therefore of their consequences as set forth in
  ✱2—✱5". `liftThm` makes this precise: replacing the propositional variables of a ✱1–✱5 theorem by
  arbitrary formulas of ✱10 gives a ✱10 theorem. PM/QuantLift.lean applies it to all 188 propositions. -/

/-- Replace the propositional variables of a ✱1–✱5 formula by ✱10 formulas. -/
def F.toQ {V : Ty → Type} (σ : String → QF V) : F → QF V
  | .var s  => σ s
  | .neg p  => .neg (F.toQ σ p)
  | .or p q => .or (F.toQ σ p) (F.toQ σ q)

theorem liftThm {V : Ty → Type} {S : Sys V} {p : F} (h : Thm p) (σ : String → QF V) : QThm S (p.toQ σ) := by
  induction h with
  | mp _ _ ih1 ih2 => exact QThm.mp ih1 ih2
  | taut p => exact QThm.taut _
  | add p q => exact QThm.add _ _
  | perm p q => exact QThm.perm _ _
  | assoc p q r => exact QThm.assoc _ _ _
  | sum p q r => exact QThm.sum _ _ _

/-- The substitution p, q, r, s ↦ the given formulas (other letters ↦ p). -/
def subst4 {V : Ty → Type} (p q r s : QF V) : String → QF V :=
  fun x => if x = "q" then q else if x = "r" then r else if x = "s" then s else p

end PM
