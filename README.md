# Principia Mathematica in Lean 4

Whitehead & Russell's *Principia Mathematica* (first edition, 1910),
formalized in Lean 4 as a deep embedding.

Companion repository: the
[**Principia Mathematica text audit**](https://github.com/willmcginnis/principia-mathematica-text-audit),
which checks the digital texts of PM against scans of the printed books.

## What this is

PM's formulas are a data type inside Lean, and PM's primitive propositions are the rules
of an embedded proof system. Every PM theorem here is derived from those rules alone:
✱1·1–✱1·6, the primitive propositions of ✱10's alternative method, and from ✱12 on
the axiom of reducibility (✱12·1, ✱12·11). Lean's own logic checks the derivations;
it is not used to prove PM's theorems directly.

PM gives two ways of founding the theory of apparent variables, ✱9's and ✱10's (p. 144).
The repository is built on ✱10's. Beside it, `PM/Found9/` builds ✱9's own method from
✱9's primitive propositions and proves ✱9·2–✱9·52 along PM's lines. ✱9's definitions of
disjunction, as printed, do not support one step of PM's proof of ✱9·31, which cites only
definitions; Landini found this flaw and published a repair (*History and Philosophy of Logic* 21,
2000). The authors' own later fix is Russell's rule ✱8·13 of the second edition (1925, Vol. I,
p. 636, page image): "If all occurrences of x are separated from all occurrences of y by a certain
stroke, we can change the order of x and y in the prefix ... and vice versa." So ✱9 is formalized
under four readings, each registered as a repair or kept as printed ([docs/REPAIRS.md](docs/REPAIRS.md)):
- A, as printed, kept and marked: 27 of the 28 numbered propositions, ✱9·31 open;
- C, as printed + ✱8·13 (working, default): the printed definitions and Russell's ✱8·13 carried
  over to ✱9: all 28. ✱8·13 takes one step of PM's proofs, the step of ✱9·31;
- L, Landini's ✱9+ (a published variant, cross-check): the printed definitions with two for
  quantifiers of the same kind (✱9·yy, from PM's Introduction, 1910 p. 49, second edition p. 47;
  and ✱9·zz) and his rule Switch: all 28;
- B, an alternative convention of our own (cross-check): all 28. It is kept to show that the
  ambiguity at ✱9·31 is real, not as precedent.

The theorem `star9_iff_star10` states that ✱9's method and ✱10's agree. Every ✱9 theorem is a ✱10
theorem, given a variable of every type. The converse holds given ✱1·2–✱1·6 for every ✱9
proposition, which is PM's claim on p. 142 and is not proved. For one apparent variable per letter,
the method of PM's ✱9·3–✱9·52 proves 50, 65, 63 and 67 of the 70 cases under A, C, L and B, 15 of C's
with ✱8·13 ([docs/STAR9_READINGS.md](docs/STAR9_READINGS.md)). In a structure with no individuals, ✱9's method
asserts an instance of ✱9·1 that is false there; ✱10's is sound in every structure. Details:
[docs/STAR9_FOUNDATION.md](docs/STAR9_FOUNDATION.md).

The proofs follow PM's own: one Lean line per line of PM's *Dem.*, or one step per
proposition of its bracketed hint. A ledger records, for each proposition, anything a
proof needs that PM does not cite.

The types are PM's 1910 ramified types, with functions of one and two arguments.

The project's design principles are in [docs/PRINCIPLES.md](docs/PRINCIPLES.md). One of them:
where PM asserts something about its own system (that two methods are equivalent, that proofs
carry over "by merely repeating previous proofs"), the assertion is checked in Lean, not adopted;
[docs/PM_CLAIMS.md](docs/PM_CLAIMS.md) lists these claims and their status. One does not hold as stated: PM's
two definitions of "predicative" (p. 56 and p. 172) disagree on some functions PM writes, though with the
axiom of reducibility they derive the same theorems (row B4). What comes next is in the [roadmap](#roadmap) below and in [docs/ROADMAP.md](docs/ROADMAP.md).

## Status at a glance (2026-10-14, commit `0d7c190`)

| Part of Vol I | Chapters | Numbered assertions proved |
|---|---|---|
| Propositional logic | ✱1–✱5 | 188 of 188 |
| Apparent variables | ✱9, ✱10, ✱11 | 4 of 28 (✱9 in part); 46 of 48; 51 of 51 |
| Types and reducibility | ✱12 | no assertions: ✱12·1, ✱12·11 are rules |
| Identity, descriptions | ✱13, ✱14 | 25 of 25; 47 of 47 (✱14·3 as a schema) |
| Classes, relations | ✱20, ✱21 | 53 of 55; 46 of 48 |
| Calculus of classes, of relations | ✱22, ✱23 | 72 of 72; 72 of 72 |
| Universal class, null-class, existence of classes | ✱24 | 70 of 70 |
| **Vol I** | ✱1–✱97 | **674 of 3,231 (20.9%)** |

Vols II and III are not started.
Per-chapter tables, milestones and the units counted: [docs/PROGRESS.md](docs/PROGRESS.md).
The two ✱10 assertions not counted (✱10·1, ✱10·12) are primitive rules here.
✱9 is counted by ✱10's method; ✱9 by its own method (`PM/Found9/`) is not counted.

Not yet done:

- ✱14·3 as printed: it needs a type of propositions, so it is proved as a schema,
  one theorem per instance;
- apparent classes of classes and their identity, needed from ✱40 on
  ([docs/CLASSES_OF_CLASSES.md](docs/CLASSES_OF_CLASSES.md));
- ✱25 onward; functions of three or more arguments; the 1925 second edition.

## What the proofs establish

- No `sorry`, no `native_decide`, no added axioms.
- Every PM theorem, and the ✱1–✱5 completeness theorem, reports
  "does not depend on any axioms" under `#print axioms`.
- An exhaustive check finds 39 declarations that use Lean's standard axioms.
  None is a PM derivation: they are compiler-generated lemmas (8 of them
  for the syntax of ✱9's method), three propositional metatheorems, and a
  general classical model.
  Details: [docs/VERIFICATION.md](docs/VERIFICATION.md).

The limits matter as much
([docs/SEMANTICS.md](docs/SEMANTICS.md)):

- **No adequacy theorem.** The formula type also contains terms that match
  no finite PM formula. Soundness covers them, but no theorem shows that
  the embedding matches PM's formulas and derivations exactly.
- **Consistency is stated at a model's variables.** At some degenerate
  variable families every formula is derivable (`PM/Trap.lean`).
- **The models forget orders.** The order discipline is checked only
  syntactically, so it is not proved that comprehension without ✱12·1 is weaker.

## Roadmap

<!-- generated:roadmap:start -->
![Roadmap overview: four groups of work (PM itself; checking underneath; comparing across; results about PM) and five milestones (Vol I checked, Vol II checked, Vol III checked, first edition audited, Lean's kernel fragment verified)](docs/roadmap/overview.svg)

The work is split into four groups that run side by side. Each group is split into subgroups, and each subgroup into chapter-sized or stage-sized tasks. Every task starts with a search for prior work. Open a group below to see its tasks. The full plan, including the reason each task waits (a dependency or a choice), the prior work found for it and the tasks that moved, is in [docs/ROADMAP.md](docs/ROADMAP.md), with the [dependency view](docs/ROADMAP.md#dependency-view).

<details>
<summary><b>1. PM itself</b>: Vol I, Vol II, Vol III, the 1925 second edition (4 done, 12 in progress, 21 not started)</summary>

![Group 1, PM itself: its subgroups and tasks](docs/roadmap/group-pm.svg)

- **Vol I (1910)**
  - ✱1–✱5: the theory of deduction: *done*
  - ✱9–✱14: apparent variables, types, identity, descriptions: *in progress*
  - ✱9's method beside ✱10's, shown to derive the same results (p. 144): *in progress*
  - ✱9·31 and the one-variable cases of p. 142: derived by ✱9's method, or shown underivable: *in progress*
  - A normal-form proof of Rep: ✱1·2–✱1·6 for every proposition of ✱9's method (p. 142): *not started*
  - Every theorem checked under both foundations, ✱9's and ✱10's: *not started*
  - ✱20–✱24: classes and relations: *done*
  - ✱25: the universal relation, the null relation, and the existence of relations: *not started*
  - Apparent classes of classes and their identity, needed from ✱40 on: *in progress*
  - Extensionality of every class and relation expression, proved once (pp. 200, 213): *done*
  - ✱30–✱38: the logic of relations: *not started*
  - ✱40–✱56: products and sums of classes; unit classes and couples, to ✱54·43: *not started*
  - ✱60–✱74: sub-classes, relative types; one-many and one-one relations: *not started*
  - ✱80–✱88: selections, with the multiplicative axiom as hypothesis: *not started*
  - ✱90–✱97: inductive relations: *not started*
  - A model that sees orders: what reducibility adds (claim B11): *not started*
- **PM's claims about its own system**
  - Claims checked with their chapters (✱1–✱21): *done*
  - Claims about ✱9's method and its agreement with ✱10's (pp. 133–153): *in progress*
  - Non-derivability and other metatheorems of ✱1–✱11: independence, the witness property, any number of variables: *in progress*
  - Claims about reducibility and orders (pp. 54–62, 171–177): *in progress*
  - Claims about the hierarchy of types (Introduction, ✱12): *in progress*
  - Claims about descriptions left open (✱14): *in progress*
  - Claims about classes and relations: transfer, scope, classes of classes, and the calculus of ✱22–✱25: *in progress*
  - Formulas PM says are not theorems: countervaluations and counter-models: *in progress*
  - Claims about the whole work, checked as the volumes are built: *in progress*
- **Vol II (1912)**
  - Per-item list of Vol II, and its claims listed by reading: *not started*
  - ✱100–✱126 (Part III): cardinal arithmetic, to ✱110·643 (1 + 1 = 2) and inductive cardinals: *not started*
  - ✱150–✱186 (Part IV): relation-arithmetic: *not started*
  - ✱200–✱234 (Part V, first half): series: *not started*
- **Vol III (1913)**
  - Per-item list of Vol III, and its claims listed by reading: *not started*
  - ✱250–✱276 (Part V, continued): well-ordered series, ordinals, compact and continuous series: *not started*
  - ✱300–✱375 (Part VI): quantity: ratios, real numbers, measurement, cyclic families: *not started*
- **1925 second edition**
  - Record the edition differences, and the new Introduction's claims: *not started*
  - ✱8 and Appendix A, in place of ✱9: *not started*
  - Appendix B (✱89, induction without reducibility): locate the failing step and prove a narrower replacement: *not started*
  - Appendix C: truth-functions and extensionality: *not started*
  - Full second-edition pass: *not started, later by choice*

</details>

<details>
<summary><b>2. Checking underneath</b>: independent kernels, Metamath and Rocq, ZFC, Lean's own kernel (1 done, 14 not started)</summary>

![Group 2, Checking underneath: its subgroups and tasks](docs/roadmap/group-under.svg)

- **Independent Lean kernels**
  - Independent Lean kernels re-check the build in CI, one checker per code family: *not started*
- **Metamath and Rocq**
  - A small, readable independent checker written for this project (a Metamath verifier in a few hundred lines), chosen for clarity over speed: *not started*
  - pm.mm for ✱1–✱5, from the finite propositional core, checked by several Metamath verifiers: *not started*
  - pm.mm for ✱9–✱14, from the finite first-order core: binding, substitution, distinct-variable conditions: *not started*
  - pm.mm from ✱20 on, chapter by chapter: *not started*
  - Rocq re-check: our own small checker for our certificate format, proved sound in Rocq: *not started, later by choice*
- **set.mm and ZFC**
  - set.mm: replay ✱1–✱5 inside ZFC: *not started*
  - A model of PM's types in ZFC: each primitive proposition and rule proved true once: *not started*
  - Every exported derivation transferred through the model: *not started*
- **Lean's own kernel**
  - (a) Census of the kernel features the project exercises: *done*
  - (b) Lean in Lean: Lean4Lean re-checks the build: *not started*
  - (c) A restricted checker for that fragment: first existing verified checkers (con-leche), then our own only if needed: *not started*
  - (d) A formal proof that the checker used is correct against a specification of the fragment: *not started*
- **Lean and ZFC: relative consistency**
  - Lean proves Con(ZFC): existing mechanizations cited and re-checked: *not started*
  - ZFC with inaccessibles proves Con(Lean's type theory): existing mechanizations cited and re-checked: *not started*

</details>

<details>
<summary><b>3. Comparing across</b>: other readings of PM, Mathlib, the printed text, formalization platforms (1 done, 5 in progress, 4 not started)</summary>

![Group 3, Comparing across: its subgroups and tasks](docs/roadmap/group-across.svg)

- **Other readings of PM**
  - Compare with set.mm's own PM theorems, chapter by chapter: *not started*
  - Compare other formalizations of PM, number by number: *in progress*
- **Mainstream mathematics (Mathlib), in a separate package**
  - Cardinal arithmetic (✱100–✱126) agrees with Mathlib's Nat and Cardinal: *not started*
  - Relation-numbers (✱150–✱186) agree with Mathlib's order types, and with Ordinal for well-orders: *not started*
  - Series, ordinals and real numbers (Vol III) agree with Mathlib: *not started*
- **The printed text**
  - Vol I and Vol II transcriptions checked against scans; errata reported: *in progress*
  - Vol III transcription proofread and checked against scans: *in progress*
  - ✱1–✱5 as transcribed: every formula parses with the printed dots and is derivable: *in progress*
  - Statement mutation: are statements tied to their proofs and to PM?: *done*
- **Formalization platforms**
  - Export to formalization platforms, with a private pilot on Prove2Me (✱1–✱5): *in progress*

</details>

<details>
<summary><b>4. Results about PM</b>: adequacy, incompleteness, the finitist audit, WKL₀, decision procedures (1 in progress, 17 not started)</summary>

![Group 4, Results about PM: its subgroups and tasks](docs/roadmap/group-about.svg)

- **Finite syntax and adequacy**
  - Adequacy, stage 1: ✱1–✱5, a finite certificate format and both translations: *not started*
  - Adequacy, stage 2: a finite first-order core for ✱9–✱14, with derivations as data, and the easy direction (every core derivation gives a QThm theorem): *not started*
  - Adequacy, stage 2, the converse: from QThm back to the finite core: *not started*
  - Completeness of ✱9's working reading C (the definitions as printed with Russell's ✱8·13): every expression true in every structure is a theorem: *not started*
  - Adequacy, stage 3: classes and beyond: *not started*
- **Incompleteness**
  - PM as a many-sorted first-order theory (the finite core), in a separate package that reuses the Foundation library: *not started*
  - Numbering of the core's formulas and derivations; 'is a derivation of' representable: *not started*
  - Arithmetic interpreted inside the chosen PM theory, with Infinity as hypothesis: Robinson's Q, and IΣ₁ for the library's Gödel–Rosser theorem: *not started*
  - Gödel's first theorem for PM, in the Gödel–Rosser form: *not started, later by choice*
  - Gödel's second theorem for PM: derivability conditions, then Con unprovable: *not started*
- **Finitist audit**
  - Assumption provenance: which results use reducibility, infinity, the multiplicative axiom: *in progress*
  - PRA readings: which results have an arithmetic reading provable in PRA: *not started, later by choice*
  - Complete census of assumptions, all three volumes: *not started*
- **WKL₀**
  - PRA, RCA₀ and WKL₀ as formal systems: *not started, later by choice*
  - WKL₀ is Π⁰₂-conservative over PRA: *not started*
- **Decision procedures**
  - Monadic first-order fragment: *not started, later by choice*
  - Presburger arithmetic (addition only): *not started, later by choice*
  - Tarski: real closed fields: *not started, later by choice*

</details>
<!-- generated:roadmap:end -->

## Build and check

Install the Lean toolchain named in `lean-toolchain` with
[elan](https://github.com/leanprover/elan). There are no other dependencies.

```
lake build                      # builds and checks every file
lake env lean AxiomCheck.lean   # 1361 of 1368 theorems and models use no axioms
lake env lean AllAxioms.lean    # every declaration; lists the 39 that use one
lake env lean RedCheck.lean     # which rules each theorem uses, vs its signature
lake env lean StyleCheck.lean   # every PM proposition, every style and system
python3 data/fidelity_counts.py # fidelity counts from the ledgers
tests/run_all.sh                # the standing checks and the regression tests (not census.py --check or mutate.py --full)
```

The expected output of each check is in [docs/VERIFICATION.md](docs/VERIFICATION.md).

## Where things are

| Path | Contents |
|---|---|
| `PM.lean`, `PM/Vol1.lean` | entry points |
| `PM/Basic.lean`, `PM/Replay*.lean` | ✱1–✱5 |
| `PM/Quant.lean`, `PM/Star10.lean`, `PM/Star11.lean` | ✱9–✱11 |
| `PM/Found9/` | ✱9 by its own method, and its agreement with ✱10 |
| `PM/Star12.lean` … `PM/Star24.lean`, `PM/Rules/`, `PM/Pred/` | ✱12–✱24, rules, styles of predicativity |
| `PM/Models/` | the models: soundness, consistency, counter-models |
| `*.lean` at the root, `Checks/` | the checks |
| `tests/` | regression tests and `run_all.sh` ([tests/README.md](tests/README.md)) |
| `data/` | fidelity ledgers, the parsed Vol I text ([data/README.md](data/README.md)) |
| `scripts/` | statement parser, generators, progress counter ([scripts/README.md](scripts/README.md)) |
| `docs/` | documentation ([index](docs/README.md)) |

A file-by-file guide is in [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md),
and the design notes are
[docs/STAR9_DESIGN.md](docs/STAR9_DESIGN.md) and [docs/TYPES_DESIGN.md](docs/TYPES_DESIGN.md).

## Fidelity in brief

Each ledgered proof is labelled `pm-lines` (only PM's citations and the steps
PM leaves tacit) or `pm-lines+extra` (at least one more proposition, listed
with the reason). Of the 188 ✱2–✱5 proofs, 112 are `pm-lines`, 65 are `pm-lines+extra`, and 11 have
no PM proof to follow. Structural steps PM leaves unstated ("glue")
can be counted either way, so three counts are given for ✱11, ✱13, ✱14 and ✱20–✱24.
See [docs/FIDELITY.md](docs/FIDELITY.md).

Following PM line by line also found things in the text, among them a
transcription slip in ✱1·4 (the transcribed form is not a theorem) and a
dropped citation in ✱4·42, both confirmed against the print by the text audit.

Other formalizations of PM, measured on the same scale:
[docs/FORMALIZATION_COMPARISON.md](docs/FORMALIZATION_COMPARISON.md).

## Credits

- **Project Gutenberg**, whose eBook #78050 (Vol I) gives the page references
  and the statements from ✱12 on (earlier ones were also read against scans
  of the 1910 print). Its volunteers, and the **Distributed Proofreaders**
  volunteers who transcribed the volumes, made a very hard text usable.
- The [text audit](https://github.com/willmcginnis/principia-mathematica-text-audit)
  (same author), which checks that text against scans of the 1910 print.
- The other formalizations of PM, credited in
  [the comparison](docs/FORMALIZATION_COMPARISON.md); in particular Luc Pommeret's
  Lean edition, Landon D. C. Elkind's work, and Metamath's `pm*` theorems.

## Citation

See [CITATION.cff](CITATION.cff) (GitHub's "Cite this repository").
Cite this repository for the formalization, with the commit you used,
and the book for PM itself.

## License

Code, ledgers and documentation are licensed under either of

- the Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE)), or
- the MIT License ([LICENSE-MIT](LICENSE-MIT)),

at your option (SPDX: `MIT OR Apache-2.0`), with one exception:
[docs/FORMALIZATION_COMPARISON.md](docs/FORMALIZATION_COMPARISON.md) is dedicated to the public domain
under CC0 1.0 ([LICENSE-CC0](LICENSE-CC0)). LICENSE-CC0 covers that file only.
The files in `data/` derived from Project Gutenberg's ebooks reproduce
public-domain text; see [data/README.md](data/README.md).
*Principia Mathematica* (1910–1913) is in the public domain in the USA; terms in other countries may differ.
Copies of this work on formalization platforms are under the terms of those platforms; Prove2Me's public
contributions are Apache-2.0, the Apache side of the choice above.
Contributions: [CONTRIBUTING.md](CONTRIBUTING.md).
