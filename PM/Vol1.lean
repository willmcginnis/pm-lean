-- ✱1–✱5
import PM.Basic
import PM.Star2
import PM.Statements
import PM.Replay
import PM.Derived
import PM.Replay2
import PM.Complete
-- ✱9–✱11 (no rule beyond ✱1, ✱10)
import PM.Quant
import PM.QuantLift
import PM.Star10
import PM.Star11
-- opt-in rules, each with its PM warrant
import PM.Rules.Comprehension
import PM.Rules.Reducibility
-- styles of predicativity
import PM.Pred.RealOwnOrder
import PM.Pred.RealAsArgument
import PM.Pred.LowestOrder
import PM.Pred.Matrix
import PM.Pred.Styles
import PM.Pred.Curry
import PM.StylesEquiv
import PM.Systems
-- semantics: the general (classical collapse) model and the finite coded model
import PM.Models.Collapse
import PM.Models.Finite
-- ✱12–✱22
import PM.Star12
import PM.Star13
import PM.Star14
import PM.Star20
import PM.Star21
import PM.Star22
-- order checker, golden tests, degenerate families
import PM.Orders
import PM.Trap

/-!
  Entry file for Volume I of Principia Mathematica (1910): ✱1–✱97, as far as built (✱1–✱5, ✱9–✱14,
  ✱20–✱22, all but a few propositions). It imports exactly what the volume uses: the propositional
  part, the quantifier base, the opt-in rules (PM/Rules/), the styles of predicativity (PM/Pred/), the
  named systems, and the semantics. Volumes II and III will get their own entry files (PM/Vol2.lean,
  PM/Vol3.lean).

  Which theorem needs which rule is in its signature (`[Reducibility S]`, `[Comprehension S]`);
  docs/VERIFICATION.md has the table, and RedCheck.lean cross-checks it against the proofs.
-/
