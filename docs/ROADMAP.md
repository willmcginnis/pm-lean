# Roadmap

What this project plans to do next, roughly in order. Status words: **in progress**, **next**, **later**, **someday**. Each item names the PM page or the question it answers. Decisions already taken are in docs/TYPES_DESIGN.md; PM's claims about its own system, and their status, are in docs/PM_CLAIMS.md.

## Checking PM's own claims

- **In progress.** ✱9's foundation built alongside ✱10's, with a theorem that both derive the same results (PM, p. 144: the two methods are alternatives).
- **Next.** Work through docs/PM_CLAIMS.md: every claim checked, or marked with why not.
- **Later.** Every theorem checked under both foundations (✱9's and ✱10's), as StyleCheck does for the predicativity styles, if the cost measured on a trial branch is reasonable.

## Coverage

- **Next.** ✱22–✱24, completing classes.
- **Later.** On to ✱54·43 (p. 379, the step before 1 + 1 = 2) and the end of Vol. I (✱97).
- **Later.** Vol. II, including ✱110·643 (1 + 1 = 2), and Vol. III.
- **Later.** The 1925 second edition: its new Introduction drops the axiom of reducibility, and Appendix A replaces ✱9.
- **After Vol. III.** Gödel's first incompleteness theorem for this encoding of PM. Gödel's 1931 paper was "On formally undecidable propositions of *Principia Mathematica* and related systems"; with PM's arithmetic built (Vols. II–III), the theorem can be checked for PM itself.

## Foundations and independence

- **Later.** A model that sees orders, to show what reducibility adds (that the predicativity styles really differ without it).
- **Decided for now.** ✱14·3 stays a schema (docs/TYPES_DESIGN.md, Q8); a type of propositions (option B), or ✱9's hierarchy of propositions (option C), is revisited if Vols. II–III or the 1925 pass need propositions as variables.
- **Later.** Adequacy: the Lean syntax and derivations correspond exactly to PM's finite formulas and proofs.

## Independent checking

Consistency can only be vouched for by a stronger system, and that system by a stronger one again (Gödel's second incompleteness theorem): that stack is documented, not finished. Checking, by contrast, can be repeated side by side by independent tools, which is where this project spends its effort.

- **Next.** Re-check the whole build with independent implementations of Lean's kernel (for example nanoda in Rust, Lean4Lean in Lean, or Tenet on .NET; see the Lean Kernel Arena) in CI.
- **Later.** Export the PM derivations to Metamath with PM's own primitive propositions as the axioms, and check them with several independent Metamath verifiers. This needs no Lean at all, which is possible because the PM derivations use none of Lean's axioms.

## Cross-checking between foundations

Two different things are meant by "checking both ways", and Gödel separates them:

- **Proofs, both ways: possible.** The same theorem checked in two systems, with proofs translated in each direction (Lean ⟷ Metamath, Metamath's set.mm being ZFC). Each direction catches errors the other might miss.
- **Consistency, both ways: impossible.** If two consistent systems (strong enough for arithmetic) each proved the other consistent, each would in effect prove its own consistency, which the second incompleteness theorem rules out. So every consistency link goes up a step: Lean proves ZFC consistent (it can build a model of ZFC), and ZFC needs added inaccessible cardinals to prove Lean consistent (Carneiro, 2019).

- **Later.** A model of ZFC in Lean, and Lean's metatheory checked in a ZFC-based system with inaccessibles, so that each direction is a checked theorem rather than a paper argument.
- **Later.** Translation of the PM derivations and the relevant set.mm results between Lean and Metamath, re-checked on each side.
- **Later.** A small, readable independent checker written for this project (a Metamath verifier in a few hundred lines), chosen for clarity over speed.

## Last

- Formal correctness of Lean itself: out of scope here, and others are working on it (Lean4Lean). Listed for completeness.
