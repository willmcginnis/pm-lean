import PM.Found9.System
import PM.Replay2
/-!
  Tools for ✱9's method, proved from its primitive propositions alone, under each reading of the
  definitions (PM/Found9/Syntax.lean, docs/REPAIRS.md). Where the definitions of ∨ need different
  proofs, a tool is proved for each and stated once for every reading.

  - `elift`: every proposition of ✱1–✱5 holds for elementary propositions (✱9 assumes ✱1 for them,
    p. 134, and ✱2–✱5 are proved from ✱1).
  - The rules that ✱9's definitions make immediate: ∃-introduction (✱9·1 with ✱9·12), and
    ∃-elimination into an elementary p, which is the remark of p. 138 that "(∃x) . φx . ⊃ . p means
    (x) . φx ⊃ p" (into any proposition under the alternative convention, `exE_convention`).
  - `ai`: if Y is X with some of its leading universal quantifiers turned into real variables, then
    ⊢ X ⊃ Y, under the definitions as printed (A, and C without using ✱8·13) and the alternative
    convention. This holds for every proposition X, with or without apparent variables, and gives
    ✱9·2 (= ✱10·1) and ✱2·08 (Id) for every proposition. Its proof uses ✱9·1 for a function φ that
    may contain apparent variables (see PM/Found9/System.lean). In ✱9+ (reading L): Id for every
    proposition from the primitive propositions alone (`idt_plus`), and ✱9·2 for every function with
    Switch (`inst_plus`), which takes the step where ✱9·zz puts an existential quantifier of the
    consequent before the universal one of the antecedent whose variable it needs.
  - The converse of ✱9·13 (`allE`: from ⊢ (x) . φx infer ⊢ φy).
  - ✱9·21 as a rule, for every pair of functions (`allImp`), under every reading; ✱9·22 as a rule
    (`exImp_printed`, `exImp_plus`) under the definitions as printed and in ✱9+, by which
    (∃x) . φx . ⊃ . (∃x) . ψx is (x) : (∃y) . φx ⊃ ψy (✱9·07).
  - ✱9·25 (= ✱10·12) for an elementary p, under every reading: "a mere example of q ⊃ q" (p. 146), the
    two sides being the same proposition by ✱9·04. For every p, under the alternative convention, from
    ✱9's primitive propositions alone (`distrib_convention`). Under the definitions as printed the two
    sides can be the same proposition or differ (`distrib_sides_ne`); PM/Found9/FromStar10.lean proves
    it for every p and every reading from ✱1·2–✱1·6 for every proposition (`Rep`) and a variable of
    every type, and PM/Found9/Switch.lean with the prenex Switch.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys} {R : Reading}

/-! ## ✱1–✱5 for elementary propositions -/

/-- Replace the propositional variables of a ✱1–✱5 formula by elementary propositions. -/
def _root_.PM.F.toE (σ : String → EF V) : F → EF V
  | .var s  => σ s
  | .neg p  => .neg (F.toE σ p)
  | .or p q => .or (F.toE σ p) (F.toE σ q)

/-- Modus ponens for elementary propositions: ✱1·1, with "p ⊃ q" read by ✱1·01 (the same under every
    reading, but a proof for every reading must split on the reading to see it). -/
theorem emp {a b : EF V} (h1 : Thm9 S R (.el a)) (h2 : Thm9 S R (.el (EF.imp a b))) :
    Thm9 S R (.el b) :=
  Thm9.mp h1 (by_defs h2)

/-- Every ✱1–✱5 theorem holds when its letters are elementary propositions. -/
theorem elift {t : F} (h : Thm t) (σ : String → EF V) : Thm9 S R (.el (t.toE σ)) := by
  induction h with
  | mp _ _ ih1 ih2 => exact emp ih1 ih2
  | taut p => exact Thm9.taut _
  | add p q => exact Thm9.add _ _
  | perm p q => exact Thm9.perm _ _
  | assoc p q r => exact Thm9.assoc _ _ _
  | sum p q r => exact Thm9.sum _ _ _

/-- The substitution p, q, r ↦ the given elementary propositions (other letters ↦ p). -/
def esub (p q r : EF V) : String → EF V :=
  fun x => if x = "q" then q else if x = "r" then r else p

/-- ✱2·08 (Id) for an elementary proposition. -/
theorem eId (a : EF V) : Thm9 S R (.el (EF.imp a a)) := elift (t2_08 (.var "p")) (esub a a a)

/-! ## Rules immediate from the definitions -/

/-- ∃-introduction: ✱9·1 and ✱9·12. -/
theorem exI {τ : Ty} {φ : V τ → PF V} (y : V τ) (h : Thm9 S R (φ y)) : Thm9 S R (.ex φ) :=
  Thm9.mp h (Thm9.ex1 φ y)

/-- ∃-elimination into an elementary p. By ✱9·02 and ✱9·03, `(∃z) . Kz . ⊃ . p` is the proposition
    `(z) . Kz ⊃ p` (p. 138), so ✱9·13 and ✱9·12 give it. -/
theorem exE {τ : Ty} {K : V τ → PF V} {c : EF V} (h : ∀ z, Thm9 S R (R.imp (K z) (.el c)))
    (he : Thm9 S R (.ex K)) : Thm9 S R (.el c) :=
  Thm9.mp he (by_defs (Thm9.gen h))

/-- ∃-elimination into any proposition, under the alternative convention: `(∃z) . Kz . ⊃ . C` is
    `(z) . Kz ⊃ C` whatever C is (✱9·03 for every p). -/
theorem exE_convention {sw : Rule} {τ : Ty} {K : V τ → PF V} {C : PF V}
    (h : ∀ z, Thm9 S ⟨.convention, sw⟩ (Reading.imp ⟨.convention, sw⟩ (K z) C))
    (he : Thm9 S ⟨.convention, sw⟩ (.ex K)) : Thm9 S ⟨.convention, sw⟩ C :=
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

/-- `ai` under the definitions as printed. When both begin with a universal quantifier, ✱9·08 makes
    `X ⊃ Y` the proposition (z) : (∃x) . ∼φx ∨ ρz: the (z) of Y comes first, and ✱9·1 then takes for x
    the variable that Y has put for it. -/
theorem ai_printed (sw : Rule) :
    ∀ (X Y : PF V), AllInst X Y → Thm9 S ⟨.printed, sw⟩ (Reading.imp ⟨.printed, sw⟩ X Y)
  | .el e, Y, h => by
    cases h with
    | refl => exact eId e
  | .ex φ, Y, h => by
    cases h with
    | refl => exact Thm9.gen fun x => exI x (ai_printed sw (φ x) (φ x) (.refl _))
  | .all φ, Y, h => by
    cases Y with
    | el b =>
      cases h with
      | step y h => exact exI y (ai_printed sw (φ y) _ h)
    | ex ρ =>
      cases h with
      | step y h => exact exI y (ai_printed sw (φ y) _ h)
    | all ρ =>
      refine Thm9.gen fun z => ?_
      cases h with
      | refl => exact exI z (ai_printed sw (φ z) (φ z) (.refl _))
      | step y h => exact exI y (ai_printed sw (φ y) _ (h.all_right z))

/-- `ai` under the alternative convention: a universal quantifier at the front of Y comes out first
    (✱9·08 with ✱9·04), the antecedent's quantifiers after it. -/
theorem ai_convention (sw : Rule) :
    ∀ (X Y : PF V), AllInst X Y → Thm9 S ⟨.convention, sw⟩ (Reading.imp ⟨.convention, sw⟩ X Y)
  | .el e, Y, h => by
    cases h with
    | refl => exact eId e
  | .all φ, Y, h => by
    induction Y with
    | el b =>
      cases h with
      | step y h => exact exI y (ai_convention sw (φ y) _ h)
    | ex ρ _ =>
      cases h with
      | step y h => exact exI y (ai_convention sw (φ y) _ h)
    | all ρ ih => exact Thm9.gen fun v => ih v (h.all_right v)
  | .ex φ, Y, h => by
    cases h with
    | refl => exact Thm9.gen fun x => Thm9.ex1 φ x

/-- ⊢ X ⊃ Y whenever Y is X with some leading universal quantifiers turned into real variables, under
    the definitions as printed and the alternative convention. In ✱9+ see `idt_plus`, `inst_plus`. -/
theorem ai (hR : R.defs ≠ .plus) (X Y : PF V) (h : AllInst X Y) : Thm9 S R (R.imp X Y) := by
  rcases R with ⟨_ | _ | _, sw⟩
  · exact ai_printed sw X Y h
  · exact ai_convention sw X Y h
  · exact absurd rfl hR

/-! ## Id and ✱9·2 for every proposition in ✱9+ -/

/-- ✱2·08 (Id) for every proposition in ✱9+, from the primitive propositions alone: X ⊃ X takes each
    quantifier of X out together with its dual from ∼X (✱9·07·08), the universal one first, so ✱9·1
    can choose its variable. -/
theorem idt_plus (pr : Rule) : ∀ X : PF V, Thm9 S ⟨.plus, pr⟩ (PF.orPlus (PF.neg X) X)
  | .el e => eId e
  | .all φ => Thm9.gen fun x => exI x (idt_plus pr (φ x))
  | .ex φ => Thm9.gen fun x => exI x (idt_plus pr (φ x))

/-- ✱9·22 as a rule, for every pair of functions, in ✱9+: by ✱9·02 and ✱9·07,
    (∃x) . φx . ⊃ . (∃x) . ψx is (x) : (∃y) . φx ⊃ ψy. -/
theorem exImp_plus {pr : Rule} {τ : Ty} {φ ψ : V τ → PF V}
    (h : ∀ x, Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ (φ x) (ψ x))) :
    Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ (.ex φ) (.ex ψ)) :=
  Thm9.gen fun z => exI z (h z)

/-- In ✱9+, ⊢ (∃x) . φx gives ⊢ (∃x) . ψx when φx and ψx are, for each x, the same proposition. -/
theorem exCongr_plus {pr : Rule} {τ : Ty} {φ ψ : V τ → PF V} (e : ∀ x, φ x = ψ x)
    (h : Thm9 S ⟨.plus, pr⟩ (.ex φ)) : Thm9 S ⟨.plus, pr⟩ (.ex ψ) :=
  Thm9.mp h (exImp_plus fun x =>
    Eq.subst (motive := fun Z => Thm9 S ⟨.plus, pr⟩ (PF.orPlus (PF.neg (φ x)) Z)) (e x)
      (idt_plus pr (φ x)))

/-- What is left of (d) . Nd . ∨ . Y in ✱9+ after its first quantifier (d): ✱9·03, ✱9·yy or ✱9·07
    take out (d) and, with it, the first quantifier of Y (`orPlus_all`). -/
def tailPlus (N : PF V) : PF V → PF V
  | .el b  => PF.orPlus N (.el b)
  | .all ψ => .all fun e => PF.orPlus N (ψ e)
  | .ex ψ  => .ex fun e => PF.orPlus N (ψ e)

theorem orPlus_all {τ : Ty} (N : V τ → PF V) (Y : PF V) :
    PF.orPlus (.all N) Y = .all fun d => tailPlus (N d) Y := by
  cases Y <;> rfl

/-- `tailPlus N Y` is a merge of N and Y: in it every free variable of N is on one side of the ∨ that
    joins the matrices, every free variable of Y on the other (the side condition of Switch). -/
theorem merge_tailPlus (N : PF V) : ∀ Y : PF V, Merge N Y (tailPlus N Y)
  | .el b => merge_orPlus N (.el b)
  | .all ψ => .allR fun e => merge_orPlus N (ψ e)
  | .ex ψ => .exR fun e => merge_orPlus N (ψ e)

/-- In ✱9+, with Switch: ⊢ (∃c) : (∃d) . χd . ⊃ . χc, given ⊢ (what is left of) χd ⊃ χd for each d.
    By ✱9·13 and ✱9·1, ⊢ (d) : (∃c) . χd ⊃ χc, with c the d; ∼χd and χc are joined by the ∨ of the
    definitions, so Switch gives (∃c) : (d), which is the proposition by ✱9·03, ✱9·yy or ✱9·07. -/
theorem exDrinker_plus {pr : Rule} {τ : Ty} (χ : V τ → PF V)
    (h : ∀ d, Thm9 S ⟨.plus, pr⟩ (tailPlus (PF.neg (χ d)) (χ d))) :
    Thm9 S ⟨.plus, pr⟩ (.ex fun c => PF.orPlus (.all fun d => PF.neg (χ d)) (χ c)) :=
  have pre : Thm9 S ⟨.plus, pr⟩ (.all fun d => .ex fun c => tailPlus (PF.neg (χ d)) (χ c)) :=
    Thm9.gen fun d => exI d (h d)
  have sw : Thm9 S ⟨.plus, pr⟩ (.ex fun c => .all fun d => tailPlus (PF.neg (χ d)) (χ c)) :=
    Thm9.switch rfl (.here (.left (fun d => PF.neg (χ d)) χ fun _ _ => merge_tailPlus _ _)) pre
  exCongr_plus (fun c => (orPlus_all (fun d => PF.neg (χ d)) (χ c)).symm) sw

/-- The induction behind `inst_plus`: for every proposition Y, ⊢ (what is left of) Y ⊃ Y, and
    ⊢ (x) . ψx . ⊃ . ψe for every function ψ with ψe = Y. -/
theorem inst_plus_aux (pr : Rule) : ∀ Y : PF V,
    Thm9 S ⟨.plus, pr⟩ (tailPlus (PF.neg Y) Y) ∧
    ∀ {τ : Ty} (ψ : V τ → PF V) (e : V τ), ψ e = Y →
      Thm9 S ⟨.plus, pr⟩ (PF.orPlus (.ex fun f => PF.neg (ψ f)) Y)
  | .el b => ⟨eId b, fun ψ e h => exI e (by
      show Thm9 S _ (PF.orPlus (PF.neg (ψ e)) (.el b)); rw [h]; exact eId b)⟩
  | .all ρ => ⟨Thm9.gen fun e => (inst_plus_aux pr (ρ e)).2 ρ e rfl, fun ψ e h =>
      Thm9.gen fun g => exI e (by
        show Thm9 S _ (PF.orPlus (PF.neg (ψ e)) (ρ g)); rw [h]
        exact (inst_plus_aux pr (ρ g)).2 ρ g rfl)⟩
  | .ex ρ => ⟨exDrinker_plus ρ fun d => (inst_plus_aux pr (ρ d)).1, fun ψ e h =>
      exI e (by
        show Thm9 S _ (.ex fun g => PF.orPlus (PF.neg (ψ e)) (ρ g)); rw [h]
        exact exDrinker_plus ρ fun d => (inst_plus_aux pr (ρ d)).1)⟩

/-- ✱9·2 `⊢ : (x) . φx . ⊃ . φy` for every function φ in ✱9+, with Switch: where ✱9·zz puts an
    existential quantifier of φy before the universal one of ∼(x) . φx whose variable it needs,
    Switch takes the order the proof needs to the one the definitions give (`exDrinker_plus`). -/
theorem inst_plus (pr : Rule) {τ : Ty} (φ : V τ → PF V) (y : V τ) :
    Thm9 S ⟨.plus, pr⟩ (Reading.imp ⟨.plus, pr⟩ (.all φ) (φ y)) :=
  (inst_plus_aux pr (φ y)).2 φ y rfl

/-! ## Id, ✱9·2 and its converse for every proposition, under every reading -/

/-- ✱2·08 (Id) for every proposition. -/
theorem idt (X : PF V) : Thm9 S R (R.imp X X) := by
  rcases R with ⟨_ | _ | _, sw⟩
  · exact ai_printed sw X X (.refl X)
  · exact ai_convention sw X X (.refl X)
  · exact idt_plus sw X

/-- ✱9·2 `⊢ : (x) . φx . ⊃ . φy` for every function φ (it is ✱10·1). -/
theorem inst {τ : Ty} (φ : V τ → PF V) (y : V τ) : Thm9 S R (R.imp (.all φ) (φ y)) := by
  rcases R with ⟨_ | _ | _, sw⟩
  · exact ai_printed sw _ _ (.step y (.refl _))
  · exact ai_convention sw _ _ (.step y (.refl _))
  · exact inst_plus sw φ y

/-- The converse of ✱9·13: from ⊢ (x) . φx infer ⊢ φy. -/
theorem allE {τ : Ty} {φ : V τ → PF V} (h : Thm9 S R (.all φ)) (y : V τ) : Thm9 S R (φ y) :=
  Thm9.mp h (inst φ y)

/-! ## ✱9·21 and ✱9·22 as rules -/

/-- Under the alternative convention, `allE` in the right half of a disjunction. -/
theorem allE_or_convention {sw : Rule} : ∀ (E : PF V) {τ : Ty} (ψ : V τ → PF V) (w : V τ),
    Thm9 S ⟨.convention, sw⟩ (PF.or E (.all ψ)) → Thm9 S ⟨.convention, sw⟩ (PF.or E (ψ w))
  | .el _, _, _, w, h => allE h w
  | .ex _, _, _, w, h => allE h w
  | .all χ, _, ψ, w, h => Thm9.gen fun u => allE_or_convention (χ u) ψ w (allE h u)

/-- Under the alternative convention, ∃-introduction in the left half of a disjunction. -/
theorem exI_or_convention {sw : Rule} {τ : Ty} (C : V τ → PF V) (y : V τ) :
    ∀ D : PF V, Thm9 S ⟨.convention, sw⟩ (PF.or (C y) D) →
      Thm9 S ⟨.convention, sw⟩ (PF.or (.ex C) D)
  | .el b, h => exI (φ := fun x => PF.or (C x) (.el b)) y h
  | .ex ρ, h => exI (φ := fun x => PF.or (C x) (.ex ρ)) y h
  | .all ψ, h => Thm9.gen fun w => exI_or_convention C y (ψ w) (allE_or_convention (C y) ψ w h)

/-- ✱9·21 as a rule, for every pair of functions and every reading: from ⊢ φx ⊃ ψx for every x infer
    ⊢ (x) . φx . ⊃ . (x) . ψx. As printed and in ✱9+, by ✱9·01 and ✱9·08, the conclusion is
    (y) : (∃x) . ∼φx ∨ ψy, and ✱9·13 and ✱9·1 give it directly. -/
theorem allImp {τ : Ty} {φ ψ : V τ → PF V} (h : ∀ x, Thm9 S R (R.imp (φ x) (ψ x))) :
    Thm9 S R (R.imp (.all φ) (.all ψ)) := by
  rcases R with ⟨_ | _ | _, sw⟩
  · exact Thm9.gen fun z => exI z (h z)
  · exact Thm9.gen fun z => exI_or_convention (fun x => (φ x).neg) z (ψ z) (h z)
  · exact Thm9.gen fun z => exI z (h z)

/-- ✱9·22 as a rule, for every pair of functions, under the definitions as printed: from ⊢ φx ⊃ ψx
    for every x infer ⊢ (∃x) . φx . ⊃ . (∃x) . ψx. By ✱9·02 and ✱9·07 the conclusion is
    (x) : (∃y) . ∼φx ∨ ψy. -/
theorem exImp_printed {sw : Rule} {τ : Ty} {φ ψ : V τ → PF V}
    (h : ∀ x, Thm9 S ⟨.printed, sw⟩ (Reading.imp ⟨.printed, sw⟩ (φ x) (ψ x))) :
    Thm9 S ⟨.printed, sw⟩ (Reading.imp ⟨.printed, sw⟩ (.ex φ) (.ex ψ)) :=
  Thm9.gen fun z => exI z (h z)

/-! ## ✱9·25 -/

/-- ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` for an elementary p and every function φ, under
    every reading: by ✱9·04 the two sides are the same proposition, so it is Id. -/
theorem distribEl (a : EF V) {τ : Ty} (φ : V τ → PF V) :
    Thm9 S R (R.imp (.all fun x => R.or (.el a) (φ x)) (R.or (.el a) (.all φ))) :=
  by_defs (idt _)

/-- Under the definitions as printed, the two sides of ✱9·25 for a p with apparent variables can be
    the same proposition (for p = (∃u) . χu and φ elementary both are (x) : (∃u) . χu ∨ φx, by ✱9·08
    and ✱9·06; pinned in Checks/PinnedStatements.lean), and they can differ: for p = (∃u) . χu and
    φx = (w) . ψ(x, w), with χ, ψ elementary, the antecedent is (x) : (w) : (∃u) . χu ∨ ψ(x, w) and the
    consequent (x) : (∃u) : (w) . χu ∨ ψ(x, w) (✱9·08), given a variable of every type. -/
theorem distrib_sides_ne (d : ∀ τ, V τ) {σ τ ρ : Ty} (χ : V σ → EF V) (ψ : V τ → V ρ → EF V) :
    (PF.all fun x => PF.orPrinted (.ex fun u => .el (χ u)) (.all fun w => .el (ψ x w))) ≠
      PF.orPrinted (.ex fun u => .el (χ u)) (.all fun x => .all fun w => .el (ψ x w)) := by
  intro h
  have h' : [true, true, false] = [true, false, true] := congrArg (PF.kinds d) h
  exact absurd h' (by decide)

/-- In ✱9+ (reading L) too, for the same p and φ the two sides of ✱9·25 differ: (x) : (w) : (∃u) and
    (x) : (∃u) : (w), by ✱9·08. -/
theorem distrib_sides_ne_plus (d : ∀ τ, V τ) {σ τ ρ : Ty} (χ : V σ → EF V) (ψ : V τ → V ρ → EF V) :
    (PF.all fun x => PF.orPlus (.ex fun u => .el (χ u)) (.all fun w => .el (ψ x w))) ≠
      PF.orPlus (.ex fun u => .el (χ u)) (.all fun x => .all fun w => .el (ψ x w)) := by
  intro h
  have h' : [true, true, false] = [true, false, true] := congrArg (PF.kinds d) h
  exact absurd h' (by decide)

/-- Under the alternative convention too, the two sides of ✱9·25 for a p with apparent variables can
    differ: for p = (v) . χv and φ elementary, the antecedent is (x) : (v) . χv ∨ φx and the consequent
    (v) : (x) . χv ∨ φx (✱9·03 for every p). Here v is an individual and x a function of individuals,
    so the two first quantifiers range over different types. -/
theorem distrib_sides_ne_convention (χ : V .ind → EF V) (φ : V (Ty.pred1 .ind) → EF V) :
    (PF.all fun x => PF.or (.all fun v => .el (χ v)) (.el (φ x))) ≠
      PF.or (.all fun v => .el (χ v)) (.all fun x => .el (φ x)) := by
  intro h
  injection h with h1
  exact Ty.noConfusion h1

/-- If (x) . φx has had leading quantifiers turned into real variables and what is left does not begin
    with one, then (x) was among them. -/
theorem AllInst.of_all {τ : Ty} {φ : V τ → PF V} {Y : PF V} (h : AllInst (.all φ) Y)
    (hY : isAll Y = false) : ∃ x, AllInst (φ x) Y := by
  cases h with
  | refl => cases hY
  | step x h => exact ⟨x, h⟩

/-- Under the alternative convention, in `p ∨ (x) . φx` the quantifier (x) is one of the leading
    universal quantifiers: once it has been turned into a real variable, what is left comes from
    `p ∨ φx`. -/
theorem allInst_or_all : ∀ (p : PF V) {τ : Ty} (φ : V τ → PF V) (Y : PF V),
    AllInst (PF.or p (.all φ)) Y → isAll Y = false → ∃ x, AllInst (PF.or p (φ x)) Y
  | .el a, _, φ, Y, h, hY => AllInst.of_all (φ := fun x => PF.or (.el a) (φ x)) h hY
  | .ex χ, _, φ, Y, h, hY => AllInst.of_all (φ := fun x => PF.or (.ex χ) (φ x)) h hY
  | .all χ, _, φ, Y, h, hY => by
    obtain ⟨u, hu⟩ := AllInst.of_all (φ := fun u => PF.or (χ u) (.all φ)) h hY
    obtain ⟨x, hx⟩ := allInst_or_all (χ u) φ Y hu hY
    exact ⟨x, .step (φ := fun u => PF.or (χ u) (φ x)) u hx⟩

/-- ✱9·25 `⊢ :. (x) . p ∨ φx . ⊃ : p . ∨ . (x) . φx` (it is ✱10·12) for every p and every function φ,
    under the alternative convention, from ✱9's primitive propositions alone: the definitions put
    every universal quantifier of the consequent first, then ✱9·1 chooses the antecedent's x. -/
theorem distrib_convention {sw : Rule} (p : PF V) {τ : Ty} (φ : V τ → PF V) :
    Thm9 S ⟨.convention, sw⟩ (PF.imp (.all fun x => PF.or p (φ x)) (PF.or p (.all φ))) := by
  suffices H : ∀ Y, AllInst (PF.or p (.all φ)) Y →
      Thm9 S ⟨.convention, sw⟩ (PF.or (.ex fun x => (PF.or p (φ x)).neg) Y) from H _ (.refl _)
  intro Y
  induction Y with
  | all ρ ih => exact fun h => Thm9.gen fun v => ih v (h.all_right v)
  | el b =>
    intro h
    obtain ⟨x, hx⟩ := allInst_or_all p φ _ h rfl
    exact exI (φ := fun x => PF.or (PF.or p (φ x)).neg (.el b)) x (ai_convention sw _ _ hx)
  | ex ρ _ =>
    intro h
    obtain ⟨x, hx⟩ := allInst_or_all p φ _ h rfl
    exact exI (φ := fun x => PF.or (PF.or p (φ x)).neg (.ex ρ)) x (ai_convention sw _ _ hx)

end PM.F9
