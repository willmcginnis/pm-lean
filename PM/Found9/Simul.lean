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
  is left; ✱9·31 (the one use of ✱9·11) for ✱1·2 with p existential; and, for ✱1·3 with p existential,
  a real variable to which ✱9·1 is applied (as in ✱9·33), since p occurs there only once. The tactic `search9` applies the first two steps
  as the definitions present the quantifiers and closes the matrix by an instance of ✱1·2–✱1·6; the
  real variables that ✱9·1 needs are found by unification.

  Result: 67 of the 70 combinations are proved. The three not covered are ✱1·6
  `q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r` with p = (x) . φx and q = (∃x) . ψx (r any of the three forms):
  `t1_6` excludes them. In these, ✱9·07 puts the universal quantifier of p before the existential of q
  in "p ∨ q"; negated, as the antecedent of an implication, that gives "(∃x) : (y)"; and the
  existential quantifier of ∼(q ⊃ r) comes before the (y) whose variable it needs. No proof by ✱9·13,
  ✱9·1 and ✱9·11 alone exists for them, whatever the order chosen for two quantifiers of the same
  kind (docs/STAR9_FOUNDATION.md); whether ✱9's primitive propositions prove them by a longer route
  (modus ponens with ✱9·1 for a function that contains an apparent variable) is not settled here.
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

/-- ✱1·2 `⊢ : p ∨ p . ⊃ . p` for p elementary, (x) . φx or (∃x) . φx (the last is ✱9·31). -/
theorem t1_2 (p : PF V) (hp : OneVar p) : Thm9 S (imp (PF.or p p) p) := by
  cases hp with
  | el e => exact Thm9.taut e
  | all φ => search9
  | ex φ => exact f9_31 φ

/-- ✱1·3 `⊢ : q . ⊃ . p ∨ q` for p, q each elementary, (x) . φx or (∃x) . φx. For p existential it
    needs a real variable (for q elementary it is ✱9·33). -/
theorem t1_3 (hV : ∀ τ, Nonempty (V τ)) (p q : PF V) (hp : OneVar p) (hq : OneVar q) :
    Thm9 S (imp q (PF.or p q)) := by
  cases hp with
  | el a => cases hq <;> search9
  | all φ => cases hq <;> search9
  | @ex τ φ =>
    refine (hV τ).elim fun x => ?_
    cases hq with
    | el b => exact f9_33 φ b x
    | all ψ => search9 <;> exact x
    | ex ψ => search9 <;> exact x

/-- ✱1·4 `⊢ : p ∨ q . ⊃ . q ∨ p` for p, q each elementary, (x) . φx or (∃x) . φx. -/
theorem t1_4 (p q : PF V) (hp : OneVar p) (hq : OneVar q) :
    Thm9 S (imp (PF.or p q) (PF.or q p)) := by
  cases hp <;> cases hq <;> search9

/-- ✱1·5 `⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)` for p, q, r each elementary, (x) . φx or (∃x) . φx. -/
theorem t1_5 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r) :
    Thm9 S (imp (PF.or p (PF.or q r)) (PF.or q (PF.or p r))) := by
  cases hp <;> cases hq <;> cases hr <;> search9

/-- ✱1·6 `⊢ : q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r` for p, q, r each elementary, (x) . φx or (∃x) . φx,
    except p universal with q existential (see the module note). -/
theorem t1_6 (p q r : PF V) (hp : OneVar p) (hq : OneVar q) (hr : OneVar r)
    (h : ¬ (isAll p = true ∧ isEx q = true)) :
    Thm9 S (imp (imp q r) (imp (PF.or p q) (PF.or p r))) := by
  cases hp <;> cases hq <;> cases hr <;> first | search9 | exact absurd ⟨rfl, rfl⟩ h

end PM.F9
