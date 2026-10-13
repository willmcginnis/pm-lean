# Documentation

| Page | What it covers |
|---|---|
| [PRINCIPLES.md](PRINCIPLES.md) | the project's standing design principles |
| [ROADMAP.md](ROADMAP.md) | the plan: four groups of tasks, each with its status, size, dependencies, the prior work found for it and the reason for its place in the order; the statements about incompleteness and consistency, with their hypotheses; scope. Its tables and the charts in [roadmap/](roadmap/) are generated from [data/roadmap.json](../data/roadmap.json) |
| [PM_CLAIMS.md](PM_CLAIMS.md) | PM's claims about its own system (Introduction, ✱1–✱21), each with its page and its status: checked in Lean, partly checked, assumed, in progress, not attempted, or shown not to hold as stated |
| [PROGRESS.md](PROGRESS.md) | coverage by volume, range and chapter; milestones; the units counted (generated tables) |
| [FIDELITY.md](FIDELITY.md) | how closely the proofs follow PM: labels, glue, the three counts, findings in the text |
| [VERIFICATION.md](VERIFICATION.md) | the check files and their expected output; Lean's axioms; which theorem uses which rule |
| [STATEMENT_MUTATION.md](STATEMENT_MUTATION.md) | a trial: unused hypotheses, and one-change mutants of each statement against its proof term and proof script; results, survivors by category, the two tiers, a recommendation |
| [SEMANTICS.md](SEMANTICS.md) | what soundness and consistency show and do not show; what is not formalized |
| [ARCHITECTURE.md](ARCHITECTURE.md) | the files, chapter by chapter |
| [FORMALIZATION_COMPARISON.md](FORMALIZATION_COMPARISON.md) | a dated survey of the formalizations of PM (CC0) |
| [STAR9_DESIGN.md](STAR9_DESIGN.md) | design note for ✱9–✱11: ✱10's alternative method |
| [REPAIRS.md](REPAIRS.md) | the register of repairs: where the working formalization reads PM other than as printed, what PM printed, why, what depends on it, and the evidence (Russell's ✱8·13 of the second edition carried over to ✱9, the working repair; the left side's quantifier first; Landini's ✱9+, a published variant; our alternative convention, a cross-check; the prenex Switch) |
| [STAR9_READINGS.md](STAR9_READINGS.md) | ✱9 under its four readings (A as printed; C as printed + ✱8·13, the working reading; L, Landini's ✱9+, a cross-check; B, the cross-check): what each derives, and where C uses ✱8·13 and L uses Switch (generated) |
| [STAR9_FOUNDATION.md](STAR9_FOUNDATION.md) | ✱9 by its own method (`PM/Found9/`), its agreement with ✱10 and the assumptions of that agreement, p. 142 for one apparent variable per letter, open questions |
| [CLASSES_OF_CLASSES.md](CLASSES_OF_CLASSES.md) | design note for classes of classes and classes of relations (✱20·03–✱20·081, ✱21·03–✱21·083) |
| [NAMING.md](NAMING.md) | export names for formalization platforms: the rule `PM.star<N>_<M>[_<pmname>][_df\|_rule][_reading_<word>][_v<N>]`, the slots for definitions and rules, the reading words, Lean and Mathlib counterparts as metadata and the criterion for them, the checks |
| [VERSIONING.md](VERSIONING.md) | how exported names, statements and proofs change: permanent names locked to their statements, `_vN` for a new statement, frozen reading meanings, deprecations kept forever, SemVer releases with a Merkle root, worked examples |
| [EXPORT_LOG.md](EXPORT_LOG.md) | the dated public log of exports and export-tooling fixes |
| [TYPES_DESIGN.md](TYPES_DESIGN.md) | design note for ✱12 onward: ramified types, decisions with their pages, acceptance tests, decisions log and open questions |

Elsewhere: [data/README.md](../data/README.md) (ledgers and parsed text), [scripts/README.md](../scripts/README.md)
(regeneration), [tests/README.md](../tests/README.md) (regression tests), [CONTRIBUTING.md](../CONTRIBUTING.md), [CHANGELOG.md](../CHANGELOG.md).
