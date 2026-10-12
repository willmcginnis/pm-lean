import PM.Found9.Switch
import PM.Found9.SearchTactic
/-!
  PM's claim on p. 142, checked for one apparent variable in each letter, under each reading.

  "We have now completed the proof that, in the primitive propositions of ✱1, any *one* of the
  propositions that occur may be replaced by (x) . φx or (∃x) . φx. It follows that, by merely repeating
  the proofs, we can show that any other of the propositions that occur in these propositions can be
  simultaneously replaced by (x) . ψx or (∃x) . ψx." (p. 142)

  Here each of p, q, r in ✱1·2–✱1·6 is, independently, an elementary proposition, (x) . φx or
  (∃x) . φx with φ elementary (`OneVar`): 70 combinations besides the all-elementary ones. The proofs
  use what the proofs of ✱9·3–✱9·52 use: ✱9·13 for a universal quantifier that the definitions put at
  the front, ✱9·1 for an existential one, and an instance of ✱1·2–✱1·6 for the elementary matrix that
  is left, with a real variable to which ✱9·1 is applied where nothing else is at hand (as in ✱9·33).
  The tactic `search9` applies the first two steps as the definitions ✱9·01–✱9·08 present the
  quantifiers and closes the matrix by an instance of ✱1·2–✱1·6; the real variables that ✱9·1 needs
  are found by unification. The case `x` of ✱1·2 is ✱9·31, which uses ✱9·11. In C (the definitions as
  printed with ✱8·13) the search `search9r` may also take a step of ✱8·13, backwards: where the
  definitions put (∃y) : (x) and the proof needs (x) first, it proves (x) : (∃y) and ✱8·13 gives the
  rest; and where they put two existential quantifiers in the order the proof does not need, it
  exchanges them. In ✱9+ (L) the search `search9s` may take a step of Switch backwards, and exchange two
  existential quantifiers with one step of Switch (`exSwap`).

  The combinations not covered are written as the forms of p, q, r (`a` for (x) . φx, `x` for
  (∃x) . φx, `e` for elementary) and are the lists `open1_2` … `open1_6` of each reading, which the
  theorems exclude by hypothesis (`Checks/Star9Readings.lean` prints them, and measures for each
  combination of C whether ✱8·13 is used, and of L whether Switch is):
  - A, as printed (`Printed`): 50 of 70. Not covered: ✱1·2 `x`; ✱1·3 `aa`; ✱1·4 `aa`, `xx`; ✱1·5
    `aaa`, `aae`, `aax`, `axa`, `xxa`, `xxe`, `xxx`; ✱1·6 `aaa`, `aea`, `axa`, `axe`, `axx`, `xea`,
    `xxa`, `xxe`, `xxx`. In each, the definitions put an existential quantifier before the universal
    one whose variable it needs. For ✱1·3 `aa`: "p ∨ q" is (x) : (y) . φx ∨ ψy, and "q . ⊃ . p ∨ q" is
    (x) : (∃y′) : (y) . ∼ψy′ ∨ φx ∨ ψy (✱9·08), so y′ is chosen before y. ✱1·2 `x` is ✱9·31, whose
    step (3)–(4) is not a definitional rewrite as printed (`f9_31_step`).
  - C, as printed with ✱8·13 (`Russell`): 65 of 70, the 50 of A without ✱8·13 (the same propositions),
    15 with it (docs/STAR9_READINGS.md lists, for each combination, how many steps). Not covered: ✱1·5
    `axa`; ✱1·6 `aaa`, `axa`, `axx`, `xxx`. In ✱1·5 `axa` the quantifiers' order is a cycle: the
    antecedent's (∃) for r precedes its (y) for q, which the consequent's (∃) for q needs, which
    precedes the consequent's (x) for r, which the antecedent's (∃) for r needs. ✱8·13 as formalized
    (its stroke is the ∨ that joins the two parts' matrices, `Sep`) cannot break it.
  - L, ✱9+ (`WithSwitch`): 63 of 70, 48 of them without Switch. Not covered: those of C and ✱1·6
    `xae`, `xax`, which A and C prove and which are other propositions in L (✱9·zz pairs the two sides'
    existential quantifiers).
  - B, the alternative convention (`Convention`): 67 of 70 (66 by the search, ✱1·2 `x` by ✱9·31). Not
    covered: ✱1·6 `axa`, `axe`, `axx`. There "p ∨ q" is (x) : (∃y) by ✱9·07 under either definitions;
    as an antecedent it becomes (∃x) : (y); with r elementary the whole is (x′) : (∃y′) : (∃x) : (y)
    over the matrix, and the (∃y′) from ∼(q ⊃ r) needs the variable of the later (y). A proof by ✱9·13,
    ✱9·1 and ✱9·11 alone chooses every (∃) from variables already introduced, so no such proof exists.
  - The definitions as printed with the prenex Switch (`PrenexSwitch`, R5): 70 of 70. The prenex
    Switch takes each to its prenex form with the universal quantifiers out first (`PE.readU`), where
    the search succeeds; ✱1·2 `x` is ✱9·31 with the prenex Switch (`f9_31_prenex`).
  Whether ✱9's primitive propositions prove the cases not covered under A or B by a longer route
  (modus ponens with propositions that contain apparent variables) is not settled here.
-/
namespace PM.F9
open PF

variable {V : Ty → Type} {S : Sys}

/-- A letter of ✱9·3–✱9·52: an elementary proposition, (x) . φx or (∃x) . φx with φ elementary. -/
inductive OneVar : PF V → Prop where
  | el (e : EF V) : OneVar (.el e)
  | all {τ : Ty} (φ : V τ → EF V) : OneVar (.all fun x => .el (φ x))
  | ex {τ : Ty} (φ : V τ → EF V) : OneVar (.ex fun x => .el (φ x))

/-- Whether a proposition begins with an existential quantifier. -/
def isEx : PF V → Bool
  | .ex _ => true
  | .el _ => false
  | .all _ => false

/-- The form of a letter: `a` for (x) . φx, `x` for (∃x) . φx, `e` otherwise. -/
def form (p : PF V) : Char := if isAll p then 'a' else if isEx p then 'x' else 'e'

/-- ∃-introduction (✱9·1, ✱9·12) with the real variable left to be found. -/
theorem exI' {R : Reading} {τ : Ty} {φ : V τ → PF V} {y : V τ} (h : Thm9 S R (φ y)) :
    Thm9 S R (.ex φ) := exI y h

/-- ✱9·13 for a leading universal quantifier, ✱9·1 for a leading existential one, and an instance of
    ✱1·2–✱1·6 for the elementary matrix. -/
syntax "search9" : tactic
macro_rules
  | `(tactic| search9) => `(tactic| first
      | exact Thm9.taut _ | exact Thm9.add _ _ | exact Thm9.perm _ _
      | exact Thm9.assoc _ _ _ | exact Thm9.sum _ _ _
      | (apply Thm9.gen; intro; search9)
      | (apply exI'; search9))

/-- A step of Switch at the front, backwards: to prove (∃y) : (x) . Z(x, y), prove (x) : (∃y) . Z(x, y),
    where Z(x, y) is a merge of a part with x and a part with y. -/
theorem switchL {pr : Rule} {τ σ : Ty} {L : V τ → PF V} {R : V σ → PF V} {Z : V τ → V σ → PF V}
    (hm : ∀ x y, Merge (L x) (R y) (Z x y)) (h : Thm9 S ⟨.plus, pr⟩ (.all fun x => .ex fun y => Z x y)) :
    Thm9 S ⟨.plus, pr⟩ (.ex fun y => .all fun x => Z x y) :=
  Thm9.switch rfl (.here (.left L R hm)) h

/-- `switchL` with the part with y on the left of the ∨. -/
theorem switchR {pr : Rule} {τ σ : Ty} {L : V τ → PF V} {R : V σ → PF V} {Z : V τ → V σ → PF V}
    (hm : ∀ x y, Merge (R y) (L x) (Z x y)) (h : Thm9 S ⟨.plus, pr⟩ (.all fun x => .ex fun y => Z x y)) :
    Thm9 S ⟨.plus, pr⟩ (.ex fun y => .all fun x => Z x y) :=
  Thm9.switch rfl (.here (.right L R hm)) h

/-- In ✱9+, two existential quantifiers in front may be exchanged, with one step of Switch:
    ⊢ (∃w) : (∃y) . N(y, w) . ⊃ . (∃y) : (∃w) . N(y, w) is, by ✱9·zz and ✱9·07,
    (w) : (∃y′) : (y) : (∃w′) . ∼N(y, w) ∨ N(y′, w′), which Switch gives from
    (w) : (y) : (∃y′) : (∃w′), proved by ✱9·1 with y′ the y and w′ the w. -/
theorem exSwap {pr : Rule} {τ σ : Ty} (N : V τ → V σ → PF V)
    (h : Thm9 S ⟨.plus, pr⟩ (.ex fun w => .ex fun y => N y w)) :
    Thm9 S ⟨.plus, pr⟩ (.ex fun y => .ex fun w => N y w) :=
  Thm9.mp h (Thm9.switch rfl (.all fun w => .here (.left (fun y => PF.neg (N y w))
      (fun y' => .ex fun w' => N y' w') fun _ _ => .exR fun _ => merge_orPlus _ _))
    (Thm9.gen fun w => Thm9.gen fun y => exI y (exI w (idt_plus pr (N y w)))))

/-- A step of ✱8·13 at the front, backwards, in a reading with ✱8·13: to prove (∃y) : (x) . Z(x, y),
    prove (x) : (∃y) . Z(x, y), where Z(x, y) is a merge of a part with x and a part with y. -/
theorem exchL {d : Defs} {τ σ : Ty} {L : V τ → PF V} {R : V σ → PF V} {Z : V τ → V σ → PF V}
    (hm : ∀ x y, Merge (L x) (R y) (Z x y)) (h : Thm9 S ⟨d, .exch⟩ (.all fun x => .ex fun y => Z x y)) :
    Thm9 S ⟨d, .exch⟩ (.ex fun y => .all fun x => Z x y) :=
  Thm9.exch rfl (k₁ := true) (k₂ := false) (.here (.left L R hm)) h

/-- `exchL` with the part with y on the left of the ∨. -/
theorem exchR {d : Defs} {τ σ : Ty} {L : V τ → PF V} {R : V σ → PF V} {Z : V τ → V σ → PF V}
    (hm : ∀ x y, Merge (R y) (L x) (Z x y)) (h : Thm9 S ⟨d, .exch⟩ (.all fun x => .ex fun y => Z x y)) :
    Thm9 S ⟨d, .exch⟩ (.ex fun y => .all fun x => Z x y) :=
  Thm9.exch rfl (k₁ := true) (k₂ := false) (.here (.right L R hm)) h

/-- Two existential quantifiers in front exchanged by one step of ✱8·13: to prove
    (∃y) : (∃w) . N(w, y), prove (∃w) : (∃y) . N(w, y), N(w, y) a merge of a part with w and a part
    with y. -/
theorem exchEL {d : Defs} {τ σ : Ty} {L : V τ → PF V} {R : V σ → PF V} {N : V τ → V σ → PF V}
    (hm : ∀ w y, Merge (L w) (R y) (N w y)) (h : Thm9 S ⟨d, .exch⟩ (.ex fun w => .ex fun y => N w y)) :
    Thm9 S ⟨d, .exch⟩ (.ex fun y => .ex fun w => N w y) :=
  Thm9.exch rfl (k₁ := false) (k₂ := false) (.here (.left L R hm)) h

/-- `exchEL` with the part with y on the left of the ∨. -/
theorem exchER {d : Defs} {τ σ : Ty} {L : V τ → PF V} {R : V σ → PF V} {N : V τ → V σ → PF V}
    (hm : ∀ w y, Merge (R y) (L w) (N w y)) (h : Thm9 S ⟨d, .exch⟩ (.ex fun w => .ex fun y => N w y)) :
    Thm9 S ⟨d, .exch⟩ (.ex fun y => .ex fun w => N w y) :=
  Thm9.exch rfl (k₁ := false) (k₂ := false) (.here (.right L R hm)) h

/-- A merge, found constructor by constructor, once its two parts are known (`merge_split`,
    PM/Found9/SearchTactic.lean). -/
syntax "merge9" : tactic
macro_rules
  | `(tactic| merge9) => `(tactic| first
      | exact Merge.el _ _
      | (refine Merge.allL fun _ => ?_; merge9)
      | (refine Merge.exL fun _ => ?_; merge9)
      | (refine Merge.allR fun _ => ?_; merge9)
      | (refine Merge.exR fun _ => ?_; merge9))

/-- `search9` with, in ✱9+, a step of Switch where the definitions put (∃y) : (x). -/
syntax "search9s" : tactic
macro_rules
  | `(tactic| search9s) => `(tactic| first
      | exact Thm9.taut _ | exact Thm9.add _ _ | exact Thm9.perm _ _
      | exact Thm9.assoc _ _ _ | exact Thm9.sum _ _ _
      | (apply Thm9.gen; intro; search9s)
      | (apply exI'; search9s)
      | (refine switchL (L := ?_) (R := ?_) ?_ ?_; rotate_left 2; (merge_split; merge9); search9s)
      | (refine switchR (L := ?_) (R := ?_) ?_ ?_; rotate_left 2; (merge_split; merge9); search9s)
      | (apply exSwap; apply exI'; search9s))

/-- `search9` with, in a reading with ✱8·13, a step of it where the definitions put (∃y) : (x), or
    where they put two existential quantifiers in the other order than the proof needs. -/
syntax "search9r" : tactic
macro_rules
  | `(tactic| search9r) => `(tactic| first
      | exact Thm9.taut _ | exact Thm9.add _ _ | exact Thm9.perm _ _
      | exact Thm9.assoc _ _ _ | exact Thm9.sum _ _ _
      | (apply Thm9.gen; intro; search9r)
      | (apply exI'; search9r)
      | (refine exchL (L := ?_) (R := ?_) ?_ ?_; rotate_left 2; (merge_split; merge9); search9r)
      | (refine exchR (L := ?_) (R := ?_) ?_ ?_; rotate_left 2; (merge_split; merge9); search9r)
      | (refine exchEL (L := ?_) (R := ?_) ?_ ?_; rotate_left 2; (merge_split; merge9);
          apply exI'; search9r)
      | (refine exchER (L := ?_) (R := ?_) ?_ ?_; rotate_left 2; (merge_split; merge9);
          apply exI'; search9r))

/-! ## The expressions of ✱1·2–✱1·6

  Each theorem below states `(e1_k …).read d`: the proposition that the definitions `d` make of the
  expression of ✱1·k with the letters replaced. -/

/-- ✱1·2 `p ∨ p . ⊃ . p`, ✱1·3 `q . ⊃ . p ∨ q`, ✱1·4 `p ∨ q . ⊃ . q ∨ p`,
    ✱1·5 `p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)`, ✱1·6 `q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r`, as expressions. -/
def e1_2 (p : PF V) : PE V := PE.imp (.or (.pf p) (.pf p)) (.pf p)
def e1_3 (p q : PF V) : PE V := PE.imp (.pf q) (.or (.pf p) (.pf q))
def e1_4 (p q : PF V) : PE V := PE.imp (.or (.pf p) (.pf q)) (.or (.pf q) (.pf p))
def e1_5 (p q r : PF V) : PE V :=
  PE.imp (.or (.pf p) (.or (.pf q) (.pf r))) (.or (.pf q) (.or (.pf p) (.pf r)))
def e1_6 (p q r : PF V) : PE V :=
  PE.imp (PE.imp (.pf q) (.pf r)) (PE.imp (.or (.pf p) (.pf q)) (.or (.pf p) (.pf r)))

/-! ## A: the definitions as printed -/

namespace Printed

def open1_2 : List (List Char) := [['x']]
def open1_3 : List (List Char) := [['a', 'a']]
def open1_4 : List (List Char) := [['a', 'a'], ['x', 'x']]
def open1_5 : List (List Char) := [['a', 'a', 'a'], ['a', 'a', 'e'], ['a', 'a', 'x'], ['a', 'x', 'a'],
  ['x', 'x', 'a'], ['x', 'x', 'e'], ['x', 'x', 'x']]
def open1_6 : List (List Char) := [['a', 'a', 'a'], ['a', 'e', 'a'], ['a', 'x', 'a'], ['a', 'x', 'e'],
  ['a', 'x', 'x'], ['x', 'e', 'a'], ['x', 'x', 'a'], ['x', 'x', 'e'], ['x', 'x', 'x']]

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary or (x) . φx. -/
theorem t1_2 (p : PF V) (hp : OneVar p) (h : open1_2.contains [form p] = false) :
    Thm9 S Reading.printed ((e1_2 p).read .printed) := by
  cases hp <;> first | search9 | exact Bool.noConfusion h

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q`. For p existential it needs a real variable (for q elementary it is
    ✱9·33). -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (h : open1_3.contains [form p, form q] = false) : Thm9 S Reading.printed ((e1_3 p q).read .printed) := by
  cases hp with
  | el a => cases hq <;> search9
  | all φ => cases hq <;> first | search9 | exact Bool.noConfusion h
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq <;> (search9 <;> exact x)

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p`. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (h : open1_4.contains [form p, form q] = false) :
    Thm9 S Reading.printed ((e1_4 p q).read .printed) := by
  cases hp <;> cases hq <;> first | search9 | exact Bool.noConfusion h

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)`. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_5.contains [form p, form q, form r] = false) :
    Thm9 S Reading.printed ((e1_5 p q r).read .printed) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9 | exact Bool.noConfusion h

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r`. -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_6.contains [form p, form q, form r] = false) :
    Thm9 S Reading.printed ((e1_6 p q r).read .printed) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9 | exact Bool.noConfusion h

end Printed

/-! ## C: the definitions as printed with ✱8·13 carried over -/

namespace Russell

def open1_2 : List (List Char) := []
def open1_3 : List (List Char) := []
def open1_4 : List (List Char) := []
def open1_5 : List (List Char) := [['a', 'x', 'a']]
def open1_6 : List (List Char) := [['a', 'a', 'a'], ['a', 'x', 'a'], ['a', 'x', 'x'], ['x', 'x', 'x']]

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary, (x) . φx or (∃x) . φx (the last is ✱9·31, with
    ✱8·13). -/
theorem t1_2 (p : PF V) (hp : OneVar p) (_ : open1_2.contains [form p] = false) :
    Thm9 S Reading.russell ((e1_2 p).read .printed) := by
  cases hp with
  | el e => search9r
  | all φ => search9r
  | ex φ => exact f9_31_russell φ

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q`. For p existential it needs a real variable. -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_3.contains [form p, form q] = false) :
    Thm9 S Reading.russell ((e1_3 p q).read .printed) := by
  cases hp with
  | el a => cases hq <;> search9r
  | all φ => cases hq <;> search9r
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq <;> (search9r <;> exact x)

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p`. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_4.contains [form p, form q] = false) :
    Thm9 S Reading.russell ((e1_4 p q).read .printed) := by
  cases hp <;> cases hq <;> search9r

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)`. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_5.contains [form p, form q, form r] = false) :
    Thm9 S Reading.russell ((e1_5 p q r).read .printed) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9r | exact Bool.noConfusion h

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r`. -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_6.contains [form p, form q, form r] = false) :
    Thm9 S Reading.russell ((e1_6 p q r).read .printed) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9r | exact Bool.noConfusion h

end Russell

/-! ## L: ✱9+, the definitions as printed with ✱9·yy, ✱9·zz and Switch (Landini's repair) -/

namespace WithSwitch

def open1_2 : List (List Char) := []
def open1_3 : List (List Char) := []
def open1_4 : List (List Char) := []
def open1_5 : List (List Char) := [['a', 'x', 'a']]
def open1_6 : List (List Char) := [['a', 'a', 'a'], ['a', 'x', 'a'], ['a', 'x', 'x'], ['x', 'a', 'e'],
  ['x', 'a', 'x'], ['x', 'x', 'x']]

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary, (x) . φx or (∃x) . φx (the last is ✱9·31, with
    Switch). -/
theorem t1_2 (p : PF V) (hp : OneVar p) (_ : open1_2.contains [form p] = false) :
    Thm9 S Reading.withSwitch ((e1_2 p).read .plus) := by
  cases hp with
  | el e => search9s
  | all φ => search9s
  | ex φ => exact f9_31_switch φ

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q`. For p existential it needs a real variable. -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_3.contains [form p, form q] = false) :
    Thm9 S Reading.withSwitch ((e1_3 p q).read .plus) := by
  cases hp with
  | el a => cases hq <;> search9s
  | all φ => cases hq <;> search9s
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq <;> (search9s <;> exact x)

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p`. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_4.contains [form p, form q] = false) :
    Thm9 S Reading.withSwitch ((e1_4 p q).read .plus) := by
  cases hp <;> cases hq <;> search9s

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)`. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_5.contains [form p, form q, form r] = false) :
    Thm9 S Reading.withSwitch ((e1_5 p q r).read .plus) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9s | exact Bool.noConfusion h

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r`. -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_6.contains [form p, form q, form r] = false) :
    Thm9 S Reading.withSwitch ((e1_6 p q r).read .plus) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9s | exact Bool.noConfusion h

end WithSwitch

/-! ## B: the alternative convention -/

namespace Convention

def open1_2 : List (List Char) := []
def open1_3 : List (List Char) := []
def open1_4 : List (List Char) := []
def open1_5 : List (List Char) := []
def open1_6 : List (List Char) := [['a', 'x', 'a'], ['a', 'x', 'e'], ['a', 'x', 'x']]

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary, (x) . φx or (∃x) . φx (the last is ✱9·31). -/
theorem t1_2 (p : PF V) (hp : OneVar p) (_ : open1_2.contains [form p] = false) :
    Thm9 S Reading.convention ((e1_2 p).read .convention) := by
  cases hp with
  | el e => search9
  | all φ => search9
  | ex φ => exact f9_31 φ

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q`. For p existential it needs a real variable. -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_3.contains [form p, form q] = false) :
    Thm9 S Reading.convention ((e1_3 p q).read .convention) := by
  cases hp with
  | el a => cases hq <;> search9
  | all φ => cases hq <;> search9
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq <;> (search9 <;> exact x)

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p`. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_4.contains [form p, form q] = false) :
    Thm9 S Reading.convention ((e1_4 p q).read .convention) := by
  cases hp <;> cases hq <;> search9

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)`. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (_ : open1_5.contains [form p, form q, form r] = false) :
    Thm9 S Reading.convention ((e1_5 p q r).read .convention) := by
  cases hp <;> cases hq <;> cases hr <;> search9

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r`, except p universal with q existential. -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : open1_6.contains [form p, form q, form r] = false) :
    Thm9 S Reading.convention ((e1_6 p q r).read .convention) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9 | exact Bool.noConfusion h

end Convention

/-! ## The definitions as printed, with the prenex Switch (R5, kept for comparison) -/

namespace PrenexSwitch

def open1_2 : List (List Char) := []
def open1_3 : List (List Char) := []
def open1_4 : List (List Char) := []
def open1_5 : List (List Char) := []
def open1_6 : List (List Char) := []

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary, (x) . φx or (∃x) . φx (the last is ✱9·31). -/
theorem t1_2 (p : PF V) (hp : OneVar p) (_ : open1_2.contains [form p] = false) :
    Thm9 S Reading.prenexSwitch ((e1_2 p).read .printed) := by
  cases hp with
  | el e => exact Thm9.ofReadU (e1_2 (.el e)) (by search9)
  | all φ => exact Thm9.ofReadU (e1_2 (.all fun x => .el (φ x))) (by search9)
  | ex φ => exact f9_31_prenex φ

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q`. For p existential it needs a real variable. -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_3.contains [form p, form q] = false) :
    Thm9 S Reading.prenexSwitch ((e1_3 p q).read .printed) := by
  refine Thm9.ofReadU (e1_3 p q) ?_
  cases hp with
  | el a => cases hq <;> search9
  | all φ => cases hq <;> search9
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq <;> (search9 <;> exact x)

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p`. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (_ : open1_4.contains [form p, form q] = false) :
    Thm9 S Reading.prenexSwitch ((e1_4 p q).read .printed) := by
  refine Thm9.ofReadU (e1_4 p q) ?_
  cases hp <;> cases hq <;> search9

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)`. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (_ : open1_5.contains [form p, form q, form r] = false) :
    Thm9 S Reading.prenexSwitch ((e1_5 p q r).read .printed) := by
  refine Thm9.ofReadU (e1_5 p q r) ?_
  cases hp <;> cases hq <;> cases hr <;> search9

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r`. -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (_ : open1_6.contains [form p, form q, form r] = false) :
    Thm9 S Reading.prenexSwitch ((e1_6 p q r).read .printed) := by
  refine Thm9.ofReadU (e1_6 p q r) ?_
  cases hp <;> cases hq <;> cases hr <;> search9

end PrenexSwitch

end PM.F9
