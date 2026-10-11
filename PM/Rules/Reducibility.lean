import PM.Quant
/-!
  The axiom of reducibility, ✱12·1 and ✱12·11, as an opt-in rule.

  Warrant (1910 print, p. 174):
    ✱12·1   ⊢ : (∃f) : φx . ≡ₓ . f!x            Pp
    ✱12·11  ⊢ : (∃f) : φ(x, y) . ≡ₓ,ᵧ . f!(x, y)  Pp
  "Every propositional function is equivalent, for all its values, to some predicative function of the
  same argument or arguments" (p. 174), "whatever may be the type of their arguments" (p. 174). PM
  states it for one and two arguments only: "these assumptions are not indispensable for our purpose,
  and are therefore not made in this work" (p. 174).

  The rules are the constructors `QThm.red1` and `QThm.red2`, usable only in a system with `red`.
  By the repository's convention (checked by RedCheck.lean) a theorem that uses them takes
  `[Reducibility S]`; PM/Star12.lean states them with PM's macros as
  `q12_1` and `q12_11`. The 1925 second edition drops this axiom (a later pass); a theorem proved without
  this class holds there too, as far as the other rules agree.
-/
namespace PM

/-- The system `S` has the axiom of reducibility (✱12·1, ✱12·11; p. 174). -/
class Reducibility (S : Sys) : Prop where
  red : S.red = true

end PM
