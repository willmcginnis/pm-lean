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

The proofs follow PM's own: one Lean line per line of PM's *Dem.*, or one step per
proposition of its bracketed hint. A ledger records, for each proposition, anything a
proof needs that PM does not cite.

The types are PM's 1910 ramified types, with functions of one and two arguments.

## Status at a glance (2026-10-12, commit `27b4f85`)

| Part of Vol I | Chapters | Numbered assertions proved |
|---|---|---|
| Propositional logic | ✱1–✱5 | 188 of 188 |
| Apparent variables | ✱9, ✱10, ✱11 | 4 of 28 (✱9 in part); 46 of 48; 51 of 51 |
| Types and reducibility | ✱12 | no assertions: ✱12·1, ✱12·11 are rules |
| Identity, descriptions | ✱13, ✱14 | 25 of 25; 47 of 47 (✱14·3 as a schema) |
| Classes, relations | ✱20, ✱21 | 53 of 55; 46 of 48 |
| **Vol I** | ✱1–✱97 | **460 of 3,230 (14.2%)** |

Vols II and III are not started.
Per-chapter tables, milestones and the units counted: [docs/PROGRESS.md](docs/PROGRESS.md).
The two ✱10 assertions not counted (✱10·1, ✱10·12) are primitive rules here.

Not yet done:

- ✱14·3 as printed: it needs a type of propositions, so it is proved as a schema,
  one theorem per instance;
- apparent classes of classes and their identity, needed from ✱40 on
  ([docs/CLASSES_OF_CLASSES.md](docs/CLASSES_OF_CLASSES.md));
- ✱22 onward; functions of three or more arguments; the 1925 second edition.

## What the proofs establish

- No `sorry`, no `native_decide`, no added axioms.
- Every PM theorem, and the ✱1–✱5 completeness theorem, reports
  "does not depend on any axioms" under `#print axioms`.
- An exhaustive check finds 25 declarations that use Lean's standard axioms.
  None is a PM derivation: they are compiler-generated lemmas, three
  propositional metatheorems, and a general classical model.
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

## Build and check

Install the Lean toolchain named in `lean-toolchain` with
[elan](https://github.com/leanprover/elan). There are no other dependencies.

```
lake build                      # about 17 s from clean
lake env lean AxiomCheck.lean   # 821 of 825 selected declarations use no axioms
lake env lean AllAxioms.lean    # every declaration; lists the 25 that use one
lake env lean RedCheck.lean     # which rules each theorem uses, vs its signature
lake env lean StyleCheck.lean   # every PM proposition, every style and system
python3 data/fidelity_counts.py # fidelity counts from the ledgers
tests/run_all.sh                # all checks, and the regression tests
```

The expected output of each check is in [docs/VERIFICATION.md](docs/VERIFICATION.md).

## Where things are

| Path | Contents |
|---|---|
| `PM.lean`, `PM/Vol1.lean` | entry points |
| `PM/Basic.lean`, `PM/Replay*.lean` | ✱1–✱5 |
| `PM/Quant.lean`, `PM/Star10.lean`, `PM/Star11.lean` | ✱9–✱11 |
| `PM/Star12.lean` … `PM/Star21.lean`, `PM/Rules/`, `PM/Pred/` | ✱12–✱21, rules, styles of predicativity |
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
can be counted either way, so three counts are given for ✱11, ✱13, ✱14, ✱20 and ✱21.
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

Code, ledgers and documentation are under the MIT License ([LICENSE](LICENSE)),
with one exception: [docs/FORMALIZATION_COMPARISON.md](docs/FORMALIZATION_COMPARISON.md)
is dedicated to the public domain under CC0 1.0 ([LICENSE-CC0](LICENSE-CC0)).
LICENSE-CC0 covers that file only.
The files in `data/` derived from Project Gutenberg's ebooks reproduce
public-domain text; see [data/README.md](data/README.md).
*Principia Mathematica* (1910–1913) is in the public domain in the USA.
Contributions: [CONTRIBUTING.md](CONTRIBUTING.md).
