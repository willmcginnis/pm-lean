# Changelog

Coverage and semantic changes, newest first, from the git history. Commit hashes are given where a change is
one commit. Current counts are in [docs/PROGRESS.md](docs/PROGRESS.md).

## 2026-10-12

- **Repository reorganization.** The README was shortened. New pages: `docs/PROGRESS.md`, `docs/FIDELITY.md`,
  `docs/VERIFICATION.md`, `docs/ARCHITECTURE.md`, `docs/SEMANTICS.md`, and `docs/FORMALIZATION_COMPARISON.md`
  (moved from the text audit's README, still CC0). Also new: `data/README.md`, `scripts/README.md`,
  `CITATION.cff`, `CONTRIBUTING.md`. The generators moved from `data/` to `scripts/`. Statement regeneration
  is now public and reproducible: `scripts/parse_vol1.py`, a self-contained `scripts/gen_lean.py`,
  `data/vol1.jsonl`. Also published: the Vol I item list (`data/vol1_items.json`), the Vol II label list
  (`data/vol2_labels.json`) and the progress counter (`scripts/progress.py`). No proof changed.
- **Three fidelity counts kept** (maintainer's decision; docs/TYPES_DESIGN.md §5, Q7).
- **✱14·3 as a schema** (`aea2007`): its antecedent, with p, q real, is a premise, so it is one theorem per
  f, φ, χ, proved along PM's Dem. `qtfnCongr` proves the premise for every truth-function built by
  ✱1–✱11's processes. All 47 numbered ✱14 propositions are now proved. A type of propositions, needed for the
  printed form, is an open question (Q8).
- **Ledgers** (`ac0cdd1`): `extra_used` no longer lists chain glue or tacit steps, and
  `data/fidelity_counts.py` checks this. The ≡ `Trans` instance of `PM/Chain.lean` is by ✱4·22.
- **✱20 and ✱21** (`1efb323`, `99b4643`, `87e802a`, `26ea05e`): 51 of ✱20's 55 numbered propositions
  and 44 of ✱21's 48 are proved along PM's lines, with ledgers, glue annotations and three fidelity counts.
  ✱20·4, ✱20·41, ✱21·4 and ✱21·41 (classes of classes) are open (Q6). ✱20·631, ✱20·632, ✱21·631 and
  ✱21·632 are built into the syntax.
- **Displayed chains as `calc` blocks** (`3169c1a`): `PM/Chain.lean`, and a `glue` field in the ledgers
  beside `fidelity`.
- **✱14·32 as printed**, with ≡ after E!(ιx)(φx) (`aae43c2`), after an external review.
- **✱13 and ✱14 along PM's lines** (`6bc1b54`, `7e627b9`, `002ccf3`): all 25 numbered ✱13 propositions,
  including ✱13·3, and 46 of the 47 of ✱14. Theorems that use ✱12·1 take `[Reducibility S]`.
- **Fidelity ledgers for ✱12, ✱13, ✱14 and ✱20** (`78a4281`), to the ✱11 standard.

## 2026-10-11

- **Styles of predicativity** (`5274808`, `76d18ca`, `ea63888`, `d27f5f9`): there are two readings of
  "predicative", matrix (p. 172, primary) and lowest order (p. 56), and two of a real function variable
  (p. 55, default; p. 54), so four styles. Every PM theorem is checked under each (`StyleCheck.lean`).
  `styles_equiv`: with reducibility, any two styles derive the same theorems. `realPhi_every_system`.
- **Finite coded model** (`57e8404`): consistency and the five counter-models without Lean axioms.
- **Rules as opt-in modules** (`d40230d`): `QThm S` over a system `Sys`; reducibility and comprehension as
  modules with classes; `RedCheck.lean` cross-checks signatures against proofs.
- **Ramified types (1910)** (`5a6a38b`, `61b81ba`): `Ty` with functions of one and two arguments and their
  orders, ✱12·1/✱12·11 as rules, collapse-model soundness, and first ✱12, ✱13, ✱14, ✱20 results. Design
  note `docs/TYPES_DESIGN.md`. A follow-up (`8a626c7`) applied fixes from an external review.
- **✱11** (`fbe97da`): all 51 assertions and the four rules along PM's lines; ledger
  `data/star11_ledger.json`.
- **Many-sorted formulas** (`bea0bbe`): `QF V` over `V : Ty → Type`; counter-models and consistency at a
  model's own variables.
- **Public release** (`6368067`, `a7ac5b8`): MIT licence, build and check instructions, the exhaustive
  axiom audit (`AllAxioms.lean`), exact fidelity counts and the scope of the ✱9–✱10 semantics.
- **✱9–✱10** (`66a0601`): ✱10's alternative method (`PM/Quant.lean`: syntax, primitives, soundness,
  counter-models), ✱1–✱5 lifted, ✱9's primitives and ✱10·1–✱10·57. Design note `docs/STAR9_DESIGN.md`.

## 2026-10-08

- **✱2–✱5 follow PM's proofs** (`b6cefb8` … `4471b5c`): 74 of the 85 `Replay2` proofs were rewritten to
  follow PM's Dem. lines or hints; ledger `data/replay2_ledger.json`.
- **Proof anomalies** (`3d20959`): ✱4·32, ✱4·42 and ✱4·43 checked against the 1910 print.

## 2026-10-04

- **Baseline** (`e5dfa14` … `7f51c0d`): the deep embedding of ✱1; all ✱2–✱5 statements; 103 replayed
  theorems; derived rules and the remaining 85; the completeness theorem; ledger `data/replay_ledger.json`
  and the statement generator.
