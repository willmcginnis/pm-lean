# Roadmap

What this project plans to do next, roughly in order. Status words: **in progress**, **next**, **later**, **someday**. Each item names the PM page or the question it answers. Decisions already taken are in docs/TYPES_DESIGN.md; PM's claims about its own system, and their status, are in docs/PM_CLAIMS.md.

## Checking PM's own claims

- **Next.** A normal-form proof of `Rep`: ✱1·2–✱1·6 for every proposition of ✱9's method (PM, p. 142: "by mere repetition of the proofs"). ✱9's foundation is built (`PM/Found9/`, docs/STAR9_FOUNDATION.md), and `star9_iff_star10` makes the agreement of the two methods (p. 144) conditional on `Rep`; a proof would make it unconditional (given an individual). It needs a normal-form theorem for ✱9 derivations, in the style of Herbrand's work on quantification theory.
- **Next.** The three cases of ✱1·6, for one apparent variable per letter, that the methods of ✱9·3–✱9·52 do not reach (p = (x) . φx, q = (∃y) . ψy; docs/PM_CLAIMS.md, A28): a derivation in ✱9's method, or a proof that there is none.
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

Consistency cannot be vouched for from inside: by Gödel's second incompleteness theorem, a consistent, recursively axiomatized theory that interprets enough arithmetic does not prove its own consistency. A consistency proof has to be given in another theory, whose own consistency is then assumed; those links are documented, not finished. Checking, by contrast, can be repeated side by side by independent tools, which is where this project spends its effort.

- **Next.** Re-check the whole build in CI with external checkers of Lean's kernel (see the Lean Kernel Arena): separately written ones such as nanoda (Rust) or Tenet (.NET), and Lean4Lean (Lean), whose own documentation says it follows the C++ kernel closely and is not really an independent implementation, so it guards less against bugs the two share.
- **Later.** Export the PM derivations to Metamath with PM's own primitive propositions as the axioms, and check them with several independent Metamath verifiers. This needs no Lean at all, which is possible because the PM derivations use none of Lean's axioms.

## Cross-checking between foundations

Two different things are meant by "checking both ways", and Gödel separates them:

- **Proofs, both ways: possible.** The same theorem checked in two systems, with proofs translated in each direction (Lean ⟷ Metamath, Metamath's set.mm being ZFC). Each direction catches errors the other might miss.
- **Consistency, both ways: impossible.** Take two consistent, recursively axiomatized systems that each contain enough arithmetic (Peano arithmetic is more than enough). If each proved the other consistent, each would prove its own consistency, which the second incompleteness theorem rules out. So between such systems a consistency proof can go only one way: Lean proves ZFC consistent (it can build a model of ZFC), and in the other direction ZFC with added inaccessible cardinals suffices to prove Lean consistent (Carneiro, 2019, builds a model of Lean's type theory there, with inaccessibles for its universes). That assumption is sufficient; it is not shown to be necessary.

- **Later.** A model of ZFC in Lean, and Lean's metatheory checked in a ZFC-based system with inaccessibles, so that each direction is a checked theorem rather than a paper argument.
- **Later.** Translation of the PM derivations and the relevant set.mm results between Lean and Metamath, re-checked on each side.
- **Later.** A small, readable independent checker written for this project (a Metamath verifier in a few hundred lines), chosen for clarity over speed.

## Last

- Formal correctness of Lean itself: out of scope here, and others are working on it (Lean4Lean). Listed for completeness.
