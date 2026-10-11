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

/-- A style of predicativity: what comprehension accepts. `adm1 k ψ` holds when the formula ψx (x of
    type `a`) may be taken as the values of a function variable of type `fn1 a k`; `adm2 k ψ` likewise
    for `fn2 a b k`. Each reading of PM's text is its own module under PM/Pred/ (docs/TYPES_DESIGN.md,
    decisions 3 and 5). -/
structure Style where
  adm1 : {V : Ty → Type} → {a : Ty} → Nat → (V a → QF V) → Prop
  adm2 : {V : Ty → Type} → {a b : Ty} → Nat → (V a → V b → QF V) → Prop

/-- An order check: `L p n` when p may be a value of a function of order n. Two readings of how a
    real function variable counts (p. 55, p. 54) are the modules PM/Pred/RealOwnOrder.lean and
    PM/Pred/RealAsArgument.lean. -/
abbrev OrderCheck : Type 1 := {V : Ty → Type} → QF V → Nat → Prop

/-- A proof system: which rules beyond ✱1–✱11 it has, and its style of predicativity. The rules are
    opt-in capabilities, each its own module with its PM warrant (PM/Rules/): `compr` is comprehension
    (class `Comprehension S`), `red` the axiom of reducibility ✱12·1, ✱12·11 (class `Reducibility S`).
    A theorem that uses a rule takes its class in its signature, so Lean enforces and shows the
    dependency; a theorem without such a class holds in every system. -/
structure Sys where
  compr : Bool
  red : Bool
  style : Style

open QF in
/-- Asserted propositions of ✱10's alternative method in the system `S`: ✱1·1–✱1·6, ✱10·1, ✱10·11,
    ✱10·12 always; comprehension at function types if `S.compr`; the axiom of reducibility (✱12·1,
    ✱12·11) if `S.red`. -/
inductive QThm {V : Ty → Type} (S : Sys) : QF V → Prop where
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
theorem QThm.mono {V : Ty → Type} {S S' : Sys} (hc : S.compr = true → S'.compr = true)
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

  The collapse model: a function of any order denotes a Boolean function of its arguments, so all the
  orders of a type denote the same function space. With the axiom of reducibility this is a model of
  PM 1910 (docs/TYPES_DESIGN.md, decision 11). It cannot see orders: `qsound` never uses `Lvl`, so the
  order discipline is tested syntactically (PM/Orders.lean), not by this model. -/

/-- What a variable of each type ranges over, given a domain `D` of individuals. The order is ignored. -/
def Ty.den (D : Type) : Ty → Type
  | .ind => D
  | .fn1 a _ => Ty.den D a → Bool
  | .fn2 a b _ => Ty.den D a → Ty.den D b → Bool

/-- A structure: a domain, a truth value for each elementary proposition, and for each type τ
    the universal quantifier as a Boolean oracle `A τ` (`A τ f` is true iff `f` is true of everything
    of type τ). Every classical structure has such oracles (`classicalAll`); at the type of
    individuals of a finite domain they are computable, which is what the counter-models below use. -/
structure QModel where
  D  : Type
  R  : String → List D → Bool
  A  : (τ : Ty) → (τ.den D → Bool) → Bool
  hA : ∀ τ f, A τ f = true ↔ ∀ d, f d = true

/-- The variable family of a structure: a variable of type τ is an element of `τ.den M.D`. -/
abbrev QModel.den (M : QModel) : Ty → Type := Ty.den M.D

/-- Truth value of a formula whose real variables are already elements of the structure. -/
def QF.eval (M : QModel) : QF M.den → Bool
  | .atom P xs    => M.R P xs
  | .app1 f x     => f x
  | .app2 f x y   => f x y
  | .neg p        => !(QF.eval M p)
  | .or p q       => QF.eval M p || QF.eval M q
  | @QF.all _ τ φ => M.A τ (fun d => QF.eval M (φ d))

/-- An existential is true when it has a true instance (the witness used for comprehension and
    ✱12·1 / ✱12·11 in `qsound`). -/
private theorem eval_ex_of (M : QModel) (τ : Ty) (g : τ.den M.D → Bool) (d : τ.den M.D)
    (h : g d = true) : (!(M.A τ fun x => !(g x))) = true := by
  cases hA : M.A τ (fun x => !(g x)) with
  | false => rfl
  | true => have := (M.hA _ _).mp hA d; rw [h] at this; cases this

private theorem iff_refl_bool (b : Bool) : (!(!(!b || b) || !(!b || b))) = true := by
  cases b <;> rfl

/-- Soundness: every `QThm` is true in every structure, at the structure's own variables. -/
theorem qsound (M : QModel) {S : Sys} {p : QF M.den} (h : QThm S p) : p.eval M = true := by
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
  -- The witness for comprehension and for ✱12·1 / ✱12·11 is the function x ↦ ⟦φx⟧ itself; its
  -- order is forgotten by the collapse, and the `Lvl` condition is not used.
  | @compr1 a k _ ψ _ =>
    exact eval_ex_of M (.fn1 a k) _ (fun x => (ψ x).eval M) ((M.hA _ _).mpr fun x => iff_refl_bool _)
  | @compr2 a b k _ ψ _ =>
    exact eval_ex_of M (.fn2 a b k) _ (fun x y => (ψ x y).eval M)
      ((M.hA _ _).mpr fun x => (M.hA _ _).mpr fun y => iff_refl_bool _)
  | @red1 a _ φ =>
    exact eval_ex_of M (Ty.pred1 a) _ (fun x => (φ x).eval M) ((M.hA _ _).mpr fun x => iff_refl_bool _)
  | @red2 a b _ φ =>
    exact eval_ex_of M (Ty.pred2 a b) _ (fun x y => (φ x y).eval M)
      ((M.hA _ _).mpr fun x => (M.hA _ _).mpr fun y => iff_refl_bool _)

/-- A formula false in some structure is not a theorem (at that structure's variables). -/
theorem not_qthm_of_countermodel (M : QModel) {p : QF M.den} (hv : p.eval M = false) {S : Sys} : ¬ QThm S p :=
  fun h => by have := qsound M h; rw [hv] at this; cases this

/-- The classical universal quantifier over any type, as a Boolean (uses `Classical.propDecidable`). -/
noncomputable def classicalAll {T : Type} (f : T → Bool) : Bool :=
  @decide (∀ d, f d = true) (Classical.propDecidable _)

theorem classicalAll_spec {T : Type} (f : T → Bool) : classicalAll f = true ↔ ∀ d, f d = true :=
  ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
   fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩

/-- Two individuals, `false` and `true`; every letter is true of its first argument, so "φ" holds of
    `true` only. Quantifiers over individuals are computed; over functions they are classical. -/
noncomputable def twoModel : QModel where
  D := Bool
  R := fun _ xs => xs.headD false
  A := fun
    | .ind => fun f => f false && f true
    | _ => classicalAll
  hA := fun τ f => by
    cases τ with
    | ind =>
      constructor
      · intro h (d : Bool)
        change (f false && f true) = true at h
        cases h0 : f false <;> cases h1 : f true <;> rw [h0, h1] at h <;> cases h <;> cases d <;>
          first | exact h0 | exact h1
      · intro h; show (f false && f true) = true; rw [h false, h true]; rfl
    | fn1 => exact classicalAll_spec f
    | fn2 => exact classicalAll_spec f

/-- Consistency: the letter `p` is not a theorem. It is stated at the variables of a structure
    (`twoModel.den`), not at an arbitrary family `V`: `QThm` at an arbitrary `V` can be degenerate (an
    empty or one-element type of functions makes ✱10·11 too strong, and ✱12·1 then contradicts it;
    PM/Trap.lean), so a consistency claim must name a structure's own variables. -/
theorem consistent (S : Sys) : ¬ QThm (V := twoModel.den) S (.atom "p" []) :=
  not_qthm_of_countermodel twoModel rfl

/-- Consistency of the theorems that hold for every family of variables (which is how every PM
    theorem in this project is stated): `p` is not one of them. -/
theorem consistent_all (S : Sys) : ¬ ∀ V : Ty → Type, QThm (V := V) S (.atom "p" []) :=
  fun h => consistent S (h _)

/-- PM p. 137: "⊢ : φy . ⊃ . (x) . φx … means 'However y may be chosen, φy implies (x).φx,' which is in
    general false." It is not a theorem: `twoModel` falsifies it. This is why ✱9·13 / ✱10·11 is a rule
    of inference and not an implication. -/
theorem not_qthm_phiy_imp_all {S : Sys} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → QF V) (y : V .ind), QThm S (QF.imp (φ y) (.all φ)) :=
  fun h => not_qthm_of_countermodel twoModel
    (p := QF.imp (.atom "φ" [true]) (.all fun x => .atom "φ" [x])) rfl
    (h twoModel.den (fun x => .atom "φ" [x]) true)

/-- ✱10·25 cannot be reversed: `(∃x).φx ⊃ (x).φx` is not a theorem. -/
theorem not_qthm_ex_imp_all {S : Sys} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → QF V), QThm S (QF.imp (QF.ex φ) (.all φ)) :=
  fun h => not_qthm_of_countermodel twoModel
    (p := QF.imp (QF.ex fun x => .atom "φ" [x]) (.all fun x => .atom "φ" [x])) rfl
    (h twoModel.den (fun x => .atom "φ" [x]))

/-- The structure with no individuals (functions of individuals still exist: the empty function). -/
noncomputable def emptyModel : QModel where
  D := Empty
  R := fun _ _ => false
  A := fun
    | .ind => fun _ => true
    | _ => classicalAll
  hA := fun τ f => by
    cases τ with
    | ind => exact ⟨fun _ d => Empty.elim d, fun _ => rfl⟩
    | fn1 => exact classicalAll_spec f
    | fn2 => exact classicalAll_spec f

/-- ✱10·25 `(x) . φx . ⊃ . (∃x) . φx` needs an individual: it is false in `emptyModel`. So the Lean
    statement of ✱10·25 (PM/Star10.lean) takes the real variable y that PM's proof uses. -/
theorem not_qthm_all_imp_ex_empty {S : Sys} :
    ¬ ∀ (V : Ty → Type) (φ : V .ind → QF V), QThm S (QF.imp (.all φ) (QF.ex φ)) :=
  fun h => not_qthm_of_countermodel emptyModel
    (p := QF.imp (.all fun x => .atom "φ" [x]) (QF.ex fun x => .atom "φ" [x])) rfl
    (h emptyModel.den (fun x => .atom "φ" [x]))

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

theorem liftThm {V : Ty → Type} {S : Sys} {p : F} (h : Thm p) (σ : String → QF V) : QThm S (p.toQ σ) := by
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
