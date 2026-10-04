/-
  Principia Mathematica ✱1–✱5 — deep embedding.
  Primitive ideas (✱1): negation `∼` and disjunction `∨`; propositional variables.
  Definitions are macros (PM: "= Df" is a typographical convenience, not a proposition):
    ✱1·01  p ⊃ q . = . ∼p ∨ q
    ✱3·01  p . q . = . ∼(∼p ∨ ∼q)
    ✱4·01  p ≡ q . = . p ⊃ q . q ⊃ p
  Primitive propositions: ✱1·1 (inference / modus ponens), ✱1·2 Taut, ✱1·3 Add, ✱1·4 Perm,
  ✱1·5 Assoc, ✱1·6 Sum. Substitution (✱1·11-style use of real variables) is built in by stating
  the axioms as schemas over arbitrary formulas. ✱1·7–✱1·72 (elementary-proposition formation)
  are the well-formedness of `F` itself.
-/
namespace PM

inductive F where
  | var : String → F
  | neg : F → F
  | or  : F → F → F
  deriving DecidableEq, Repr, Inhabited

@[reducible] def F.imp (p q : F) : F := .or (.neg p) q                 -- ✱1·01
@[reducible] def F.and (p q : F) : F := .neg (.or (.neg p) (.neg q))   -- ✱3·01
@[reducible] def F.iff (p q : F) : F := F.and (F.imp p q) (F.imp q p)  -- ✱4·01

inductive Thm : F → Prop where
  | mp    {p q : F} : Thm p → Thm (F.imp p q) → Thm q                                  -- ✱1·1
  | taut  (p : F)       : Thm (F.imp (.or p p) p)                                      -- ✱1·2
  | add   (p q : F)     : Thm (F.imp q (.or p q))                                      -- ✱1·3
  | perm  (p q : F)     : Thm (F.imp (.or p q) (.or q p))                              -- ✱1·4
  | assoc (p q r : F)   : Thm (F.imp (.or p (.or q r)) (.or q (.or p r)))              -- ✱1·5
  | sum   (p q r : F)   : Thm (F.imp (F.imp q r) (F.imp (.or p q) (.or p r)))          -- ✱1·6

/-- Two-valued semantics, for soundness and counter-models. -/
def F.eval (v : String → Bool) : F → Bool
  | .var s  => v s
  | .neg p  => !(p.eval v)
  | .or p q => p.eval v || q.eval v

theorem sound {p : F} (h : Thm p) : ∀ v, p.eval v = true := by
  induction h with
  | mp _ _ ih1 ih2 => intro v; have h1 := ih1 v; have h2 := ih2 v; simp_all [F.eval, F.imp]
  | taut p => intro v; cases hp : p.eval v <;> simp_all [F.eval]
  | add p q => intro v; cases hp : p.eval v <;> cases hq : q.eval v <;> simp_all [F.eval]
  | perm p q => intro v; cases hp : p.eval v <;> cases hq : q.eval v <;> simp_all [F.eval]
  | assoc p q r => intro v; cases hp : p.eval v <;> cases hq : q.eval v <;> cases hr : r.eval v <;> simp_all [F.eval]
  | sum p q r => intro v; cases hp : p.eval v <;> cases hq : q.eval v <;> cases hr : r.eval v <;> simp_all [F.eval]

/-- A formula with a falsifying valuation is not a theorem: this is how a PM-ERROR (or a transcription
    error) gets a machine-checked counter-model. -/
theorem not_thm_of_countermodel {p : F} (v : String → Bool) (hv : p.eval v = false) : ¬ Thm p :=
  fun h => by have := sound h v; simp_all

end PM

namespace PM
/-- Variables of a formula, and a decidable truth-table check (an independent re-implementation of
    dots.py's tautology test, run by Lean's kernel). -/
def F.vars : F → List String
  | .var s => [s]
  | .neg p => p.vars
  | .or p q => (p.vars ++ q.vars).eraseDups

def assignments : List String → List (String → Bool)
  | [] => [fun _ => false]
  | x :: xs => (assignments xs).flatMap fun v => [fun s => if s == x then false else v s, fun s => if s == x then true else v s]

def F.isTaut (p : F) : Bool := (assignments p.vars.eraseDups).all fun v => p.eval v
end PM
