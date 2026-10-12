import PM.Found9.System
import PM.Replay2
/-!
  Tools for ✱9's method, proved from its primitive propositions alone.

  - `elift`: every proposition of ✱1–✱5 holds for elementary propositions (✱9 assumes ✱1 for them,
    p. 134, and ✱2–✱5 are proved from ✱1).
  - The rules that ✱9's definitions make immediate: ∃-introduction (✱9·1 with ✱9·12), and
    ∃-elimination into an elementary p, which is the remark of p. 138 that "(∃x) . φx . ⊃ . p means
    (x) . φx ⊃ p".
  - `ai`: if Y is X with some of its leading universal quantifiers turned into real variables, then
    ⊢ X ⊃ Y. This holds for every proposition X, with or without apparent variables, and gives ✱9·2
    (= ✱10·1) and ✱2·08 (Id) for every proposition. Its proof uses ✱9·1 for a function φ that may
    contain apparent variables (see PM/Found9/System.lean).
  - The converse of ✱9·13 (`allE`: from ⊢ (x) . φx infer ⊢ φy).
  - ✱9·21 and ✱9·22 as rules, for every pair of functions (`allImp`, `exImp`): by ✱9·07·08, which
    "apply also when φ and ψ are not both elementary", (x) . φx . ⊃ . (x) . ψx is
    (y) : (∃x) . φx ⊃ ψy and (∃x) . φx . ⊃ . (∃x) . ψx is (x) : (∃y) . φx ⊃ ψy, so ✱9·13 and ✱9·1
    prove them from φx ⊃ ψx.
  - ✱9·25 (= ✱10·12) for an elementary p: "a mere example of q ⊃ q" (p. 146), the two sides being the
    same proposition by ✱9·04. For a p with apparent variables the two sides can be the same
    proposition or differ (`distrib_sides_ne`); PM/Found9/FromStar10.lean proves it for every p from
    ✱1·2–✱1·6 for every proposition (`Rep`) and a variable of every type.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys}

/-! ## ✱1–✱5 for elementary propositions -/

/-- Replace the propositional variables of a ✱1–✱5 formula by elementary propositions. -/
def _root_.PM.F.toE (σ : String → EF V) : F → EF V
  | .var s  => σ s
  | .neg p  => .neg (F.toE σ p)
  | .or p q => .or (F.toE σ p) (F.toE σ q)

/-- Every ✱1–✱5 theorem holds when its letters are elementary propositions. -/
theorem elift {t : F} (h : Thm t) (σ : String → EF V) : Thm9 S (.el (t.toE σ)) := by
  induction h with
  | mp _ _ ih1 ih2 => exact Thm9.mp ih1 ih2
  | taut p => exact Thm9.taut _
  | add p q => exact Thm9.add _ _
  | perm p q => exact Thm9.perm _ _
  | assoc p q r => exact Thm9.assoc _ _ _
  | sum p q r => exact Thm9.sum _ _ _

/-- The substitution p, q, r ↦ the given elementary propositions (other letters ↦ p). -/
def esub (p q r : EF V) : String → EF V :=
  fun x => if x = "q" then q else if x = "r" then r else p

/-- ✱2·08 (Id) for an elementary proposition. -/
theorem eId (a : EF V) : Thm9 S (.el (EF.imp a a)) := elift (t2_08 (.var "p")) (esub a a a)

/-! ## Rules immediate from the definitions -/

/-- ∃-introduction: ✱9·1 and ✱9·12. -/
theorem exI {τ : Ty} {φ : V τ → PF V} (y : V τ) (h : Thm9 S (φ y)) : Thm9 S (.ex φ) :=
  Thm9.mp h (Thm9.ex1 φ y)

/-- ∃-elimination into an elementary p. By ✱9·02 and ✱9·03, `(∃z) . Kz . ⊃ . p` is the proposition
    `(z) . Kz ⊃ p` (p. 138), so ✱9·13 and ✱9·12 give it. -/
theorem exE {τ : Ty} {K : V τ → PF V} {c : EF V} (h : ∀ z, Thm9 S (imp (K z) (.el c)))
    (he : Thm9 S (.ex K)) : Thm9 S (.el c) :=
  Thm9.mp he (Thm9.gen h)

/-! ## Instantiating leading universal quantifiers -/

/-- `AllInst X Y`: Y is X with some of its leading universal quantifiers turned into real variables. -/
inductive AllInst : PF V → PF V → Prop where
  | refl (X : PF V) : AllInst X X
  | step {τ : Ty} {φ : V τ → PF V} (y : V τ) {Y : PF V} : AllInst (φ y) Y → AllInst (.all φ) Y

theorem AllInst.all_right {X : PF V} {τ : Ty} {ρ : V τ → PF V} (h : AllInst X (.all ρ)) (v : V τ) :
    AllInst X (ρ v) := by
  generalize hY : PF.all ρ = Y at h
  induction h with
  | refl X => subst hY; exact .step v (.refl _)
  | step y _ ih => exact .step y (ih hY)

/-- Whether a proposition begins with a universal quantifier. -/
def isAll : PF V → Bool
  | .all _ => true
  | .el _ => false
  | .ex _ => false

/-- ⊢ X ⊃ Y whenever Y is X with some leading universal quantifiers turned into real variables. When
    both begin with a universal quantifier, ✱9·08 makes `X ⊃ Y` the proposition (z) : (∃x) . ∼φx ∨ ρz:
    the (z) of Y comes first, and ✱9·1 then takes for x the variable that Y has put for it. -/
theorem ai : ∀ (X Y : PF V), AllInst X Y → Thm9 S (imp X Y)
  | .el e, Y, h => by
    cases h with
    | refl => exact eId e
  | .ex φ, Y, h => by
    cases h with
    | refl => exact Thm9.gen fun x => exI x (ai (φ x) (φ x) (.refl _))
  | .all φ, Y, h => by
    cases Y with
    | el b =>
      cases h with
      | step y h => exact exI y (ai (φ y) _ h)
    | ex ρ =>
      cases h with
      | step y h => exact exI y (ai (φ y) _ h)
    | all ρ =>
      refine Thm9.gen fun z => ?_
      cases h with
      | refl => exact exI z (ai (φ z) (φ z) (.refl _))
      | step y h => exact exI y (ai (φ y) _ (h.all_right z))

/-- ✱2·08 (Id) for every proposition. -/
theorem idt (X : PF V) : Thm9 S (imp X X) := ai X X (.refl X)

/-- ✱9·2 `⊢ : (x) . φx . ⊃ . φy` for every function φ (it is ✱10·1). -/
theorem inst {τ : Ty} (φ : V τ → PF V) (y : V τ) : Thm9 S (imp (.all φ) (φ y)) :=
  ai _ _ (.step y (.refl _))

/-- The converse of ✱9·13: from ⊢ (x) . φx infer ⊢ φy. -/
theorem allE {τ : Ty} {φ : V τ → PF V} (h : Thm9 S (.all φ)) (y : V τ) : Thm9 S (φ y) :=
  Thm9.mp h (inst φ y)

/-- ✱9·21 as a rule, for every pair of functions: from ⊢ φx ⊃ ψx for every x infer
    ⊢ (x) . φx . ⊃ . (x) . ψx. By ✱9·01 and ✱9·08 the conclusion is (y) : (∃x) . ∼φx ∨ ψy. -/
theorem allImp {τ : Ty} {φ ψ : V τ → PF V} (h : ∀ x, Thm9 S (imp (φ x) (ψ x))) :
    Thm9 S (imp (.all φ) (.all ψ)) :=
  Thm9.gen fun z => exI z (h z)

/-- ✱9·22 as a rule, for every pair of functions: from ⊢ φx ⊃ ψx for every x infer
    ⊢ (∃x) . φx . ⊃ . (∃x) . ψx. By ✱9·02 and ✱9·07 the conclusion is (x) : (∃y) . ∼φx ∨ ψy. -/
theorem exImp {τ : Ty} {φ ψ : V τ → PF V} (h : ∀ x, Thm9 S (imp (φ x) (ψ x))) :
    Thm9 S (imp (.ex φ) (.ex ψ)) :=
  Thm9.gen fun z => exI z (h z)

/-! ## ✱9·25 for an elementary p -/

/-- ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` for an elementary p and every function φ: by ✱9·04
    the two sides are the same proposition, so it is Id. -/
theorem distribEl (a : EF V) {τ : Ty} (φ : V τ → PF V) :
    Thm9 S (imp (.all fun x => PF.or (.el a) (φ x)) (PF.or (.el a) (.all φ))) :=
  idt _

/-- For a p with apparent variables the two sides of ✱9·25 can be the same proposition (for
    p = (∃u) . χu and φ elementary both are (x) : (∃u) . χu ∨ φx, by ✱9·08 and ✱9·06; pinned in
    Checks/PinnedStatements.lean), and they can differ: for p = (∃u) . χu and φx = (w) . ψ(x, w), with
    χ, ψ elementary, the antecedent is (x) : (w) : (∃u) . χu ∨ ψ(x, w) and the consequent
    (x) : (∃u) : (w) . χu ∨ ψ(x, w) (✱9·08), given a variable of every type. -/
theorem distrib_sides_ne (d : ∀ τ, V τ) {σ τ ρ : Ty} (χ : V σ → EF V) (ψ : V τ → V ρ → EF V) :
    (PF.all fun x => PF.or (.ex fun u => .el (χ u)) (.all fun w => .el (ψ x w))) ≠
      PF.or (.ex fun u => .el (χ u)) (.all fun x => .all fun w => .el (ψ x w)) := by
  intro h
  have h' : [true, true, false] = [true, false, true] := congrArg (PF.kinds d) h
  exact absurd h' (by decide)

end PM.F9
