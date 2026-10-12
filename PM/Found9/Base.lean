import PM.Found9.System
import PM.Replay2
/-!
  Tools for ✱9's method, proved from its primitive propositions alone.

  - `elift`: every proposition of ✱1–✱5 holds for elementary propositions (✱9 assumes ✱1 for them,
    p. 134, and ✱2–✱5 are proved from ✱1).
  - The rules that ✱9's definitions make immediate: ∃-introduction (✱9·1 with ✱9·12), and
    ∃-elimination, which is the remark of p. 138 that "(∃x) . φx . ⊃ . p means (x) . φx ⊃ p".
  - `ai`: if Y is X with some of its leading universal quantifiers turned into real variables, then
    ⊢ X ⊃ Y. This holds for every proposition X, with or without apparent variables, and gives ✱9·2
    (= ✱10·1) and ✱2·08 (Id) for every proposition. Its proof uses ✱9·1 for a function φ that may
    contain apparent variables (see PM/Found9/System.lean).
  - The converse of ✱9·13 (`allE`: from ⊢ (x) . φx infer ⊢ φy), and its use inside a disjunction.
  - ✱9·21 as a rule, for every pair of functions.
  - ✱9·25 (= ✱10·12) for every p and φ. For an elementary p it is "a mere example of q ⊃ q" (p. 146): the
    two sides are the same proposition. For a p that begins with a universal quantifier, the
    definitions put that quantifier first, and the two sides are different propositions.
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

/-- ∃-elimination. By ✱9·02 and ✱9·03, `(∃z) . Kz . ⊃ . C` is the proposition `(z) . Kz ⊃ C` (p. 138),
    so ✱9·13 and ✱9·12 give it. -/
theorem exE {τ : Ty} {K : V τ → PF V} {C : PF V} (h : ∀ z, Thm9 S (imp (K z) C))
    (he : Thm9 S (.ex K)) : Thm9 S C :=
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

/-- ⊢ X ⊃ Y whenever Y is X with some leading universal quantifiers turned into real variables. -/
theorem ai : ∀ (X Y : PF V), AllInst X Y → Thm9 S (imp X Y)
  | .el e, Y, h => by
    cases h with
    | refl => exact eId e
  | .all φ, Y, h => by
    induction Y with
    | el b =>
      cases h with
      | step y h => exact exI y (ai (φ y) _ h)
    | ex ρ _ =>
      cases h with
      | step y h => exact exI y (ai (φ y) _ h)
    | all ρ ih => exact Thm9.gen fun v => ih v (h.all_right v)
  | .ex φ, Y, h => by
    cases h with
    | refl => exact Thm9.gen fun x => Thm9.ex1 φ x

/-- ✱2·08 (Id) for every proposition. -/
theorem idt (X : PF V) : Thm9 S (imp X X) := ai X X (.refl X)

/-- ✱9·2 `⊢ : (x) . φx . ⊃ . φy` for every function φ (it is ✱10·1). -/
theorem inst {τ : Ty} (φ : V τ → PF V) (y : V τ) : Thm9 S (imp (.all φ) (φ y)) :=
  ai _ _ (.step y (.refl _))

/-- The converse of ✱9·13: from ⊢ (x) . φx infer ⊢ φy. -/
theorem allE {τ : Ty} {φ : V τ → PF V} (h : Thm9 S (.all φ)) (y : V τ) : Thm9 S (φ y) :=
  Thm9.mp h (inst φ y)

/-- `allE` in the right half of a disjunction. -/
theorem allE_or : ∀ (E : PF V) {τ : Ty} (ψ : V τ → PF V) (w : V τ),
    Thm9 S (PF.or E (.all ψ)) → Thm9 S (PF.or E (ψ w))
  | .el _, _, _, w, h => allE h w
  | .ex _, _, _, w, h => allE h w
  | .all χ, _, ψ, w, h => Thm9.gen fun u => allE_or (χ u) ψ w (allE h u)

/-- ∃-introduction in the left half of a disjunction. -/
theorem exI_orL {τ : Ty} (C : V τ → PF V) (y : V τ) :
    ∀ D : PF V, Thm9 S (PF.or (C y) D) → Thm9 S (PF.or (.ex C) D)
  | .el b, h => exI (φ := fun x => PF.or (C x) (.el b)) y h
  | .ex ρ, h => exI (φ := fun x => PF.or (C x) (.ex ρ)) y h
  | .all ψ, h => Thm9.gen fun w => exI_orL C y (ψ w) (allE_or (C y) ψ w h)

/-- ✱9·21 as a rule, for every pair of functions: from ⊢ φx ⊃ ψx for every x infer
    ⊢ (x) . φx . ⊃ . (x) . ψx. -/
theorem allImp {τ : Ty} {φ ψ : V τ → PF V} (h : ∀ x, Thm9 S (imp (φ x) (ψ x))) :
    Thm9 S (imp (.all φ) (.all ψ)) :=
  Thm9.gen fun z => exI_orL (fun x => (φ x).neg) z (ψ z) (h z)

/-! ## ✱9·25 for every p and φ -/

/-- If (x) . φx has had leading quantifiers turned into real variables and what is left does not begin
    with one, then (x) was among them. -/
theorem AllInst.of_all {τ : Ty} {φ : V τ → PF V} {R : PF V} (h : AllInst (.all φ) R)
    (hR : isAll R = false) : ∃ x, AllInst (φ x) R := by
  cases h with
  | refl => cases hR
  | step x h => exact ⟨x, h⟩

/-- In `p ∨ (x) . φx`, the quantifier (x) is one of the leading universal quantifiers: once it has been
    turned into a real variable, what is left comes from `p ∨ φx`. -/
theorem allInst_or_all : ∀ (p : PF V) {τ : Ty} (φ : V τ → PF V) (R : PF V),
    AllInst (PF.or p (.all φ)) R → isAll R = false → ∃ x, AllInst (PF.or p (φ x)) R
  | .el a, _, φ, R, h, hR => AllInst.of_all (φ := fun x => PF.or (.el a) (φ x)) h hR
  | .ex χ, _, φ, R, h, hR => AllInst.of_all (φ := fun x => PF.or (.ex χ) (φ x)) h hR
  | .all χ, _, φ, R, h, hR => by
    obtain ⟨u, hu⟩ := AllInst.of_all (φ := fun u => PF.or (χ u) (.all φ)) h hR
    obtain ⟨x, hx⟩ := allInst_or_all (χ u) φ R hu hR
    exact ⟨x, .step (φ := fun u => PF.or (χ u) (φ x)) u hx⟩

/-- ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` for every p and φ (it is ✱10·12). -/
theorem distrib (p : PF V) {τ : Ty} (φ : V τ → PF V) :
    Thm9 S (imp (.all fun x => PF.or p (φ x)) (PF.or p (.all φ))) := by
  suffices H : ∀ R, AllInst (PF.or p (.all φ)) R →
      Thm9 S (PF.or (.ex fun x => (PF.or p (φ x)).neg) R) from H _ (.refl _)
  intro R
  induction R with
  | all ρ ih => exact fun h => Thm9.gen fun v => ih v (h.all_right v)
  | el b =>
    intro h
    obtain ⟨x, hx⟩ := allInst_or_all p φ _ h rfl
    exact exI (φ := fun x => PF.or (PF.or p (φ x)).neg (.el b)) x (ai _ _ hx)
  | ex ρ _ =>
    intro h
    obtain ⟨x, hx⟩ := allInst_or_all p φ _ h rfl
    exact exI (φ := fun x => PF.or (PF.or p (φ x)).neg (.ex ρ)) x (ai _ _ hx)

end PM.F9
