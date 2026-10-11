import PM.Basic
/-!
  Principia Mathematica ✱9–✱10: propositions containing apparent variables.

  This file follows PM's "alternative method" of ✱10 (pp. 143–144): `∼`, `∨` and `(x).φx` are primitive
  for propositions of any order, and the primitive propositions of ✱1 hold for them. ✱10 states:
  "✱10·1 is ✱9·2, ✱10·11 is ✱9·13, ✱10·12 is ✱9·25, ✱10·121 is ✱9·14, and ✱10·122 is ✱9·15. These five
  propositions must all be taken as primitive propositions in the alternative method; on the other hand,
  ✱9·1 and ✱9·11 are not required as primitive propositions in the alternative method." (p. 144)
  See docs/STAR9_DESIGN.md for why this method was chosen over ✱9's.

  Syntax. `QF V` is a formula over a type `V` of individual variables. An elementary proposition is a
  predicate letter applied to a list of variables; `atom "p" []` is a propositional letter. A function
  φx̂ is a Lean function `φ : V → QF V`, and its value at the variable `y` is `φ y`; `(x).φx` is `.all φ`.
  (This binding style is known as PHOAS. It needs no substitution and no renaming of variables, so the
  apparent variable is "only nominal", as in PM.)

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
    there is a function φx̂) are built into the syntax: there is one type of individuals, every
    `φ : V → QF V` is a function, and every `φ a` is a formula.
-/
namespace PM

/-- Formulas of ✱10 over a type `V` of individual variables. -/
inductive QF (V : Type) where
  | atom : String → List V → QF V
  | neg  : QF V → QF V
  | or   : QF V → QF V → QF V
  | all  : (V → QF V) → QF V

namespace QF
variable {V : Type}
@[reducible] def imp (p q : QF V) : QF V := .or (.neg p) q                    -- ✱1·01
@[reducible] def and (p q : QF V) : QF V := .neg (.or (.neg p) (.neg q))      -- ✱3·01
@[reducible] def iff (p q : QF V) : QF V := QF.and (QF.imp p q) (QF.imp q p)  -- ✱4·01
@[reducible] def ex (φ : V → QF V) : QF V := .neg (.all fun x => .neg (φ x))  -- ✱10·01
@[reducible] def fimp (φ ψ : V → QF V) : QF V := .all fun x => QF.imp (φ x) (ψ x)  -- ✱10·02
@[reducible] def fiff (φ ψ : V → QF V) : QF V := .all fun x => QF.iff (φ x) (ψ x)  -- ✱10·03
end QF

open QF in
/-- Asserted propositions of ✱10's alternative method. -/
inductive QThm {V : Type} : QF V → Prop where
  | mp      {p q : QF V} : QThm p → QThm (imp p q) → QThm q                       -- ✱1·1, ✱9·12
  | taut    (p : QF V)     : QThm (imp (.or p p) p)                                -- ✱1·2
  | add     (p q : QF V)   : QThm (imp q (.or p q))                                -- ✱1·3
  | perm    (p q : QF V)   : QThm (imp (.or p q) (.or q p))                        -- ✱1·4
  | assoc   (p q r : QF V) : QThm (imp (.or p (.or q r)) (.or q (.or p r)))        -- ✱1·5
  | sum     (p q r : QF V) : QThm (imp (imp q r) (imp (.or p q) (.or p r)))        -- ✱1·6
  | inst    (φ : V → QF V) (y : V) : QThm (imp (.all φ) (φ y))                     -- ✱10·1
  | gen     {φ : V → QF V} : (∀ y, QThm (φ y)) → QThm (.all φ)                     -- ✱10·11
  | distrib (p : QF V) (φ : V → QF V) :
      QThm (imp (.all fun x => .or p (φ x)) (.or p (.all φ)))                      -- ✱10·12

/-! ## Semantics and soundness -/

/-- A structure for ✱10: a domain, a truth value for each elementary proposition, and the
    universal quantifier as a Boolean oracle `A` (`A f` is true iff `f` is true of every individual).
    Every classical structure has such an oracle; for a finite domain it is computable, which is
    what the counter-models below use. -/
structure QModel where
  D  : Type
  R  : String → List D → Bool
  A  : (D → Bool) → Bool
  hA : ∀ f, A f = true ↔ ∀ d, f d = true

/-- Truth value of a formula whose real variables are already individuals of the domain. -/
def QF.eval (M : QModel) : QF M.D → Bool
  | .atom P xs => M.R P xs
  | .neg p     => !(QF.eval M p)
  | .or p q    => QF.eval M p || QF.eval M q
  | .all φ     => M.A (fun d => QF.eval M (φ d))

theorem qsound (M : QModel) {p : QF M.D} (h : QThm p) : p.eval M = true := by
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
  | inst φ y =>
    show (!(M.A fun d => (φ d).eval M) || (φ y).eval M) = true
    cases hA : M.A (fun d => (φ d).eval M) with
    | false => rfl
    | true => rw [(M.hA _).mp hA y]; rfl
  | gen _ ih => exact (M.hA _).mpr ih
  | distrib p φ =>
    show (!(M.A fun d => p.eval M || (φ d).eval M) || (p.eval M || M.A fun d => (φ d).eval M)) = true
    cases p.eval M with
    | true =>
      show (!(M.A fun d => true || (φ d).eval M) || true) = true
      cases M.A (fun d => true || (φ d).eval M) <;> rfl
    | false =>
      show (!(M.A fun d => (φ d).eval M) || M.A fun d => (φ d).eval M) = true
      cases M.A (fun d => (φ d).eval M) <;> rfl

/-- A formula false in some structure is not a theorem. -/
theorem not_qthm_of_countermodel (M : QModel) {p : QF M.D} (hv : p.eval M = false) : ¬ QThm p :=
  fun h => by have := qsound M h; rw [hv] at this; cases this

/-- Two individuals, `false` and `true`; every letter is true of its first argument, so "φ" holds of `true` only. -/
def twoModel : QModel where
  D := Bool
  R := fun _ xs => xs.headD false
  A := fun f => f false && f true
  hA := fun f => by
    constructor
    · intro h d
      cases h0 : f false <;> cases h1 : f true <;> rw [h0, h1] at h <;> cases h <;> cases d <;>
        first | exact h0 | exact h1
    · intro h; rw [h false, h true]; rfl

/-- PM p. 137: "⊢ : φy . ⊃ . (x) . φx … means 'However y may be chosen, φy implies (x).φx,' which is in
    general false." It is not a theorem: `twoModel` falsifies it. This is why ✱9·13 / ✱10·11 is a rule
    of inference and not an implication. -/
theorem not_qthm_phiy_imp_all :
    ¬ ∀ (V : Type) (φ : V → QF V) (y : V), QThm (QF.imp (φ y) (.all φ)) :=
  fun h => not_qthm_of_countermodel twoModel (p := QF.imp (.atom "φ" [true]) (.all fun x => .atom "φ" [x]))
    rfl (h twoModel.D (fun x => .atom "φ" [x]) true)

/-- ✱10·25 cannot be reversed: `(∃x).φx ⊃ (x).φx` is not a theorem. -/
theorem not_qthm_ex_imp_all :
    ¬ ∀ (V : Type) (φ : V → QF V), QThm (QF.imp (QF.ex φ) (.all φ)) :=
  fun h => not_qthm_of_countermodel twoModel
    (p := QF.imp (QF.ex fun x => .atom "φ" [x]) (.all fun x => .atom "φ" [x])) rfl
    (h twoModel.D (fun x => .atom "φ" [x]))

/-- The structure with no individuals. -/
def emptyModel : QModel where
  D := Empty
  R := fun _ _ => false
  A := fun _ => true
  hA := fun _ => ⟨fun _ d => Empty.elim d, fun _ => rfl⟩

/-- ✱10·25 `(x) . φx . ⊃ . (∃x) . φx` needs an individual: it is false in `emptyModel`. So the Lean
    statement of ✱10·25 (PM/Star10.lean) takes the real variable y that PM's proof uses. -/
theorem not_qthm_all_imp_ex_empty :
    ¬ ∀ (V : Type) (φ : V → QF V), QThm (QF.imp (.all φ) (QF.ex φ)) :=
  fun h => not_qthm_of_countermodel emptyModel
    (p := QF.imp (.all fun x => .atom "φ" [x]) (QF.ex fun x => .atom "φ" [x])) rfl
    (h emptyModel.D (fun x => .atom "φ" [x]))

/-! ## ✱1–✱5 apply to propositions containing apparent variables

  ✱10 (p. 144) assumes "the applicability to propositions containing apparent variables of analogues of
  the primitive ideas and propositions of ✱1, and therefore of their consequences as set forth in
  ✱2—✱5". `liftThm` makes this precise: replacing the propositional variables of a ✱1–✱5 theorem by
  arbitrary formulas of ✱10 gives a ✱10 theorem. PM/QuantLift.lean applies it to all 188 propositions. -/

/-- Replace the propositional variables of a ✱1–✱5 formula by ✱10 formulas. -/
def F.toQ {V : Type} (σ : String → QF V) : F → QF V
  | .var s  => σ s
  | .neg p  => .neg (F.toQ σ p)
  | .or p q => .or (F.toQ σ p) (F.toQ σ q)

theorem liftThm {V : Type} {p : F} (h : Thm p) (σ : String → QF V) : QThm (p.toQ σ) := by
  induction h with
  | mp _ _ ih1 ih2 => exact QThm.mp ih1 ih2
  | taut p => exact QThm.taut _
  | add p q => exact QThm.add _ _
  | perm p q => exact QThm.perm _ _
  | assoc p q r => exact QThm.assoc _ _ _
  | sum p q r => exact QThm.sum _ _ _

/-- The substitution p, q, r, s ↦ the given formulas (other letters ↦ p). -/
def subst4 {V : Type} (p q r s : QF V) : String → QF V :=
  fun x => if x = "q" then q else if x = "r" then r else if x = "s" then s else p

end PM
