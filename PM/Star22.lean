import PM.Star21
/-!
  ✱22: calculus of classes (1910 print; numbered items pp. 219–225, after the number's summary). The
  print has 79 numbered items: the definitions ✱22·01–✱22·05 (pp. 219–220), ✱22·53 (p. 221) and ✱22·71
  (p. 223), and 72 propositions, ✱22·1 to ✱22·95 (there is no ✱22·67).

  Statements are read from the Gutenberg #78050 transcription of the 1910 print (its formula source),
  not from the scan images; no entry of the text audit's list of errors falls on pp. 219–225. Each
  proof follows PM's Dem. line by line, or uses the propositions of PM's bracketed hint in PM's order;
  the comment on each Lean line gives PM's line or hint. `data/star22_ledger.json` records, per
  proposition, which cited propositions are used and which further ones were needed.

  The definitions are macros (`@[reducible]`), like ✱20·01 (docs/TYPES_DESIGN.md decision 9). A class
  is written by its defining function (PM/Star20.lean), so each operation that PM defines as a class
  x̂(…) is the function x ↦ …, in which every occurrence of α and β is eliminated where it stands
  (x ∈ α is `clsMem x α`, ✱20·01 with the smallest scope):
    ✱22·01  α ⊂ β . = : x ∈ α . ⊃ₓ . x ∈ β               Df   (`QF.clsSubset α β`, `α ⊂ β`)
    ✱22·02  α ∩ β = x̂(x ∈ α . x ∈ β)                     Df   (`QF.clsInter α β`, `α ∩ β`)
    ✱22·03  α ∪ β = x̂(x ∈ α . ∨ . x ∈ β)                 Df   (`QF.clsUnion α β`, `α ∪ β`)
    ✱22·04  −α = x̂(x ∼∈ α)                                Df   (`QF.clsCompl α`, `−α`)
    ✱22·05  α − β = α ∩ −β                                Df   (`QF.clsDiff α β`, `α − β`)
    ✱22·53  α ∩ β ∩ γ = (α ∩ β) ∩ γ                       Df   (`QF.clsInter3`)
    ✱22·71  α ∪ β ∪ γ = (α ∪ β) ∪ γ                       Df   (`QF.clsUnion3`)
  So ✱22·2 `⊢ . α ∩ β = x̂(x ∈ α . x ∈ β)` [✱20·2 . (✱22·02)] is literally ✱20·2. ✱22·01 is a
  definition of a proposition, not of a class; its definiens is the formal implication ✱10·02.

  Most of PM's hints cite one proposition of ✱3–✱5 (✱22·5–✱22·93): the proof carries it under (x) by
  ✱10·11 (with ✱10·271), rewrites each membership by ✱22·33, ✱22·34 or ✱22·35, and gets the identity of
  classes by ✱20·43, as the printed Dem. of ✱22·5, ✱22·68 and ✱22·91 do.

  Steps done silently are those of PM/Star11.lean's header and of PM/Star14.lean's (chaining ⊃ and ≡
  lines under a hypothesis). A displayed chain is a `calc` block, one line per PM line with PM's
  citation (PM/Chain.lean); the propositions that join its lines under a hypothesis are listed per
  proposition as `glue` in the ledger, apart from the fidelity. Any other proposition a proof needs is
  named in its docstring and listed as `extra_used` in the ledger.

  Names: `q22_1` is ✱22·1, and so on. α, β, γ, δ are classes, written by their defining functions
  (formulas with a hole, of any order); `F` is an expression containing a class (✱22·94, ✱22·95).
-/
namespace PM
open QF

namespace QF
variable {V : Ty → Type}
/-- ✱22·01 `α ⊂ β . = : x ∈ α . ⊃ₓ . x ∈ β` Df -/
@[reducible] def clsSubset {a : Ty} (α β : V a → QF V) : QF V := fimp (fun x => clsMem x α) fun x => clsMem x β
/-- ✱22·02 `α ∩ β = x̂(x ∈ α . x ∈ β)` Df: the class whose defining function is x ∈ α . x ∈ β. -/
@[reducible] def clsInter {a : Ty} (α β : V a → QF V) : V a → QF V := fun x => QF.and (clsMem x α) (clsMem x β)
/-- ✱22·03 `α ∪ β = x̂(x ∈ α . ∨ . x ∈ β)` Df -/
@[reducible] def clsUnion {a : Ty} (α β : V a → QF V) : V a → QF V := fun x => .or (clsMem x α) (clsMem x β)
/-- ✱22·04 `−α = x̂(x ∼∈ α)` Df (x ∼∈ α is ✱20·06, `nmem`) -/
@[reducible] def clsCompl {a : Ty} (α : V a → QF V) : V a → QF V := fun x => nmem x α
/-- ✱22·05 `α − β = α ∩ −β` Df -/
@[reducible] def clsDiff {a : Ty} (α β : V a → QF V) : V a → QF V := clsInter α (clsCompl β)
/-- ✱22·53 `α ∩ β ∩ γ = (α ∩ β) ∩ γ` Df -/
@[reducible] def clsInter3 {a : Ty} (α β γ : V a → QF V) : V a → QF V := clsInter (clsInter α β) γ
/-- ✱22·71 `α ∪ β ∪ γ = (α ∪ β) ∪ γ` Df -/
@[reducible] def clsUnion3 {a : Ty} (α β γ : V a → QF V) : V a → QF V := clsUnion (clsUnion α β) γ
end QF

/-! The notations of ✱22 (scoped to `PM`, like `x ∈ α`): `α ⊂ β`, `α ∩ β`, `α ∪ β`, `−α` and `α − β`, with
    PM's minus sign (U+2212), not `-`. Each unfolds to the definition it names. ∩ binds more tightly than
    ∪ and −, and −α most tightly, so `α ∪ β ∩ γ` is α ∪ (β ∩ γ) and `−α ∩ β` is (−α) ∩ β; PM writes the
    brackets, and so do the statements here. -/
/-- `α ⊂ β`: `clsSubset α β` (✱22·01). -/
scoped infix:50 " ⊂ " => QF.clsSubset
/-- `α ∩ β`: `clsInter α β` (✱22·02). -/
scoped infixl:70 " ∩ " => QF.clsInter
/-- `α ∪ β`: `clsUnion α β` (✱22·03). -/
scoped infixl:65 " ∪ " => QF.clsUnion
/-- `−α`: `clsCompl α` (✱22·04). -/
scoped prefix:max "−" => QF.clsCompl
/-- `α − β`: `clsDiff α β` (✱22·05). -/
scoped infixl:65 " − " => QF.clsDiff

variable {V : Ty → Type} {S : Sys} {a : Ty}

/-! Checks of the notation: each statement is the definition it names. -/
example (α β : V a → QF V) : (α ⊂ β) = fimp (fun x => x ∈ α) (fun x => x ∈ β) := rfl
example (α β : V a → QF V) : (α ∩ β) = (fun x => QF.and (x ∈ α) (x ∈ β)) := rfl
example (α β : V a → QF V) : (α ∪ β) = (fun x => QF.or (x ∈ α) (x ∈ β)) := rfl
example (α : V a → QF V) : (−α) = (fun x => QF.neg (x ∈ α)) := rfl
example (α β : V a → QF V) : (α − β) = α ∩ −β := rfl
example (α β γ : V a → QF V) : clsInter3 α β γ = (α ∩ β) ∩ γ := rfl
example (α β γ : V a → QF V) : clsUnion3 α β γ = (α ∪ β) ∪ γ := rfl

end PM
