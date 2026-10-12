import PM.Found9.Star9
/-!
  PM's claim on p. 142, checked for one apparent variable in each letter.

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
  are found by unification.

  Result: 50 of the 70 combinations are proved. The 20 not covered, written as the forms of p, q, r
  (`a` for (x) . φx, `x` for (∃x) . φx, `e` for elementary), are excluded by the hypotheses below:
    ✱1·2  p ∨ p . ⊃ . p:                       x
    ✱1·3  q . ⊃ . p ∨ q:                       aa
    ✱1·4  p ∨ q . ⊃ . q ∨ p:                   aa, xx
    ✱1·5  p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r):       aaa, aae, aax, axa, xxa, xxe, xxx
    ✱1·6  q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r:       aaa, aea, axa, axe, axx, xea, xxa, xxe, xxx
  In each, the definitions put an existential quantifier before the universal quantifier whose
  variable it needs. For ✱1·3 with p = (x) . φx, q = (y) . ψy: "p ∨ q" is (x) : (y) . φx ∨ ψy (✱9·03,
  ✱9·04), and "q . ⊃ . p ∨ q" is (x) : (∃y′) : (y) . ∼ψy′ ∨ φx ∨ ψy (✱9·08, ✱9·04): y′ is chosen before
  y. The case `x` of ✱1·2 is ✱9·31, whose own proof does not survive the definitions as printed
  (PM/Found9/Star9.lean, `f9_31_step`). Whether ✱9's primitive propositions prove the 20 by a longer
  route (modus ponens with propositions that contain apparent variables) is not settled here.
  Under the earlier reading of the definitions (`PF.orL`, which applies ✱9·03 and ✱9·05 for every p)
  the same search proves 66 of them, and ✱9·31's Dem. the 67th; the three left were ✱1·6 `axa`,
  `axe`, `axx` (docs/STAR9_FOUNDATION.md).
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
theorem exI' {τ : Ty} {φ : V τ → PF V} {y : V τ} (h : Thm9 S (φ y)) : Thm9 S (.ex φ) := exI y h

/-- ✱9·13 for a leading universal quantifier, ✱9·1 for a leading existential one, and an instance of
    ✱1·2–✱1·6 for the elementary matrix. -/
syntax "search9" : tactic
macro_rules
  | `(tactic| search9) => `(tactic| first
      | exact Thm9.taut _ | exact Thm9.add _ _ | exact Thm9.perm _ _
      | exact Thm9.assoc _ _ _ | exact Thm9.sum _ _ _
      | (apply Thm9.gen; intro; search9)
      | (apply exI'; search9))

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary or (x) . φx. -/
theorem t1_2 (p : PF V) (hp : OneVar p) (h : ['x'].contains (form p) = false) :
    Thm9 S (imp (PF.or p p) p) := by
  cases hp <;> first | search9 | exact Bool.noConfusion h

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q` for p, q each elementary, (x) . φx or (∃x) . φx, except both universal.
    For p existential it needs a real variable (for q elementary it is ✱9·33). -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (h : [['a', 'a']].contains [form p, form q] = false) : Thm9 S (imp q (PF.or p q)) := by
  cases hp with
  | el a => cases hq <;> search9
  | all φ => cases hq <;> first | search9 | exact Bool.noConfusion h
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq <;> (search9 <;> exact x)

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p` for p, q each elementary, (x) . φx or (∃x) . φx, except both of the
    same kind. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q)
    (h : [['a', 'a'], ['x', 'x']].contains [form p, form q] = false) :
    Thm9 S (imp (PF.or p q) (PF.or q p)) := by
  cases hp <;> cases hq <;> first | search9 | exact Bool.noConfusion h

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)` for p, q, r each elementary, (x) . φx or (∃x) . φx,
    except the seven combinations of the module note. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : [['a', 'a', 'a'], ['a', 'a', 'e'], ['a', 'a', 'x'], ['a', 'x', 'a'], ['x', 'x', 'a'],
      ['x', 'x', 'e'], ['x', 'x', 'x']].contains [form p, form q, form r] = false) :
    Thm9 S (imp (PF.or p (PF.or q r)) (PF.or q (PF.or p r))) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9 | exact Bool.noConfusion h

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r` for p, q, r each elementary, (x) . φx or (∃x) . φx,
    except the nine combinations of the module note. -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : [['a', 'a', 'a'], ['a', 'e', 'a'], ['a', 'x', 'a'], ['a', 'x', 'e'], ['a', 'x', 'x'],
      ['x', 'e', 'a'], ['x', 'x', 'a'], ['x', 'x', 'e'], ['x', 'x', 'x']].contains
        [form p, form q, form r] = false) :
    Thm9 S (imp (imp q r) (imp (PF.or p q) (PF.or p r))) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9 | exact Bool.noConfusion h

end PM.F9
