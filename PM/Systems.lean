import PM.Rules.Comprehension
import PM.Rules.Reducibility
/-!
  Named proof systems: which opt-in rules each has (PM/Rules/), for a given style of predicativity
  (PM/Pred/). Every theorem stated for an arbitrary `S` with no class holds in all of them; a theorem
  with `[Reducibility S]` or `[Comprehension S]` holds in those that provide the instance.

  | System                 | comprehension | ✱12·1, ✱12·11 | what it is |
  |---|---|---|---|
  | `Sys.full st`          | yes | yes | PM 1910 as built here |
  | `Sys.reducibility st`  | no  | yes | PM's own route: every function from ✱12·1 |
  | `Sys.predicative st`   | yes | no  | the predicative fragment (toward the 1925 pass) |
  | `Sys.base st`          | no  | no  | ✱1–✱11 only |
-/
namespace PM

/-- Comprehension and reducibility: PM 1910 as built here. -/
abbrev Sys.full (st : Style) : Sys := ⟨true, true, st⟩
/-- Reducibility without comprehension: PM's own route (its proofs form functions by ✱12·1). -/
abbrev Sys.reducibility (st : Style) : Sys := ⟨false, true, st⟩
/-- Comprehension without reducibility: the predicative fragment. -/
abbrev Sys.predicative (st : Style) : Sys := ⟨true, false, st⟩
/-- Neither rule: ✱1–✱11. -/
abbrev Sys.base (st : Style) : Sys := ⟨false, false, st⟩

instance (st : Style) : Comprehension (Sys.full st) := ⟨rfl⟩
instance (st : Style) : Reducibility (Sys.full st) := ⟨rfl⟩
instance (st : Style) : Reducibility (Sys.reducibility st) := ⟨rfl⟩
instance (st : Style) : Comprehension (Sys.predicative st) := ⟨rfl⟩
/-- Any system written out with `red := true`. -/
instance (c : Bool) (st : Style) : Reducibility ⟨c, true, st⟩ := ⟨rfl⟩

end PM
