# Changelog

Coverage and semantic changes, newest first, from the git history. Commit hashes are given where a change is
one commit. Current counts are in [docs/PROGRESS.md](docs/PROGRESS.md).

## 2026-10-12

- **The roadmap as nested groups, generated from data.** `data/roadmap.json` holds the plan: four groups (PM
  itself; checking underneath; comparing across; results about PM), their subgroups, and 66 tasks, each with
  status, size, dependencies, order (by dependency, or by choice with the reason) and the prior work found for
  it, with an evidence level for each entry. `scripts/roadmap_chart.py` draws the charts in `docs/roadmap/`
  and writes the roadmap section of the README and the tables of `docs/ROADMAP.md`, filling in counts from
  `docs/PROGRESS.md`, `docs/PM_CLAIMS.md` and the ✱9 ledger; `tests/test_roadmap.py` keeps them in step.
  Changes to the plan: the finite first-order core (adequacy, stage 2) is the gate for pm.mm beyond ✱5, the
  Rocq re-check and incompleteness, because a `QThm` proof is infinitely branching; incompleteness goes
  through a first-order presentation of PM, reusing an existing library in a separate package; the Rocq
  re-check is our own small checker over our own certificates; a verified checker for Lean's kernel fragment
  follows the census directly, starting with existing ones; the Lean–ZFC links are cited and re-checked, not
  rebuilt; Appendix B's goal is to locate the failing step and prove a narrower replacement; Mathlib bridges
  start at ✱100, in a separate package. New tasks: ✱9·31 and the one-variable cases of p. 142, a normal-form
  proof of `Rep`, every theorem under both foundations, the converse of adequacy, and a check that the
  transcribed ✱1–✱5 formulas parse with the printed dots and are derivable. Tasks that moved say why.
  `docs/PRINCIPLES.md`: principles 6 (search prior work first) and 7 (the order is a plan, not a contract).
- **Corrections after a second external review.** PM_CLAIMS A12 is partly checked (27 checked, 22
  partly checked): ✱10·12 is proved in ✱9's method for an elementary p (`f10_12`), and for every p only
  given `Rep` and a variable of every type (`Rep.distrib`); A14 names both hypotheses of `qthm_toF9`.
  For a p with apparent variables the two sides of ✱10·12 can be the same proposition (p = (∃u) . χu,
  φ elementary: pinned by `rfl` in `Checks/PinnedStatements.lean`) or differ (`distrib_sides_ne`); the
  docs had said they always differ. The ✱9·31 finding is stated as what it shows: the cited
  definitional step fails, not that ✱9·31 is false or underivable.
- **✱9·07–✱9·08 as printed** (after an external review; `PM/Found9/Syntax.lean`): ✱9's disjunction
  `PF.or` now applies ✱9·03–✱9·08 to the outermost quantifier of each side, as printed, with ✱9·07·08
  "also when φ and ψ are not both elementary" (pp. 135–136). It had taken every leading universal
  quantifier of the left side out first, so that, for φx = (z) . R(x, z), "(x) . φx . ∨ . (∃y) . ψy" was
  (x) : (z) : (∃y) instead of (x) : (∃y) : (z) (pinned in `Checks/PinnedStatements.lean`). Changed
  results, which correct the entry below: in PM's proof of ✱9·31 the step from line (3) to line (4),
  cited as "[(3).(✱9·03·02)]", is not a definitional rewrite under the printed definitions (it reads
  ✱9·03 where ✱9·07 applies; `f9_31_step`), and no step exchanging quantifiers is cited. So ✱9·31 is
  open: lines (1)–(3) are proved, and whether ✱9's method derives it is not settled (28 numbered ✱9
  propositions, 27 proved). PM_CLAIMS A10 is partly checked; p. 142 for one apparent
  variable per letter: 50 of 70 cases (was 67), the 20 open ones listed in docs/STAR9_FOUNDATION.md §7;
  ✱10·12 is proved in ✱9 for an elementary p, and for every p given `Rep` and a variable of every type
  (`Rep.distrib`), so `qthm_toF9` now takes `hV` as `star9_iff_star10` already did. ✱9·21 and ✱9·22
  are now direct rules for every function. `star9_iff_star10`, `thm9_toQ`, `thm9_sound`, `consistent9`
  and `thm9_unsound_empty` are unchanged. The earlier reading is kept as `PF.orL`, only to state the
  ✱9·31 finding. Ledger rows may now have method `open` (✱9·31).
- **✱9 by its own method** (`PM/Found9/`, docs/STAR9_FOUNDATION.md): ✱9's primitive propositions as
  `Thm9 S`, ✱9·2–✱9·52 along PM's lines, ✱10's primitive propositions proved in ✱9. `star9_iff_star10`:
  every ✱9 theorem is a ✱10 theorem (given a variable of every type), and every ✱10 theorem is a ✱9
  theorem given `Rep`, ✱1·2–✱1·6 for every ✱9 proposition (PM's claim on p. 142, not proved). p. 142 for
  one apparent variable per letter: 67 of 70 cases; the three ✱1·6 cases with p universal and q
  existential are open. Without an individual ✱9's method asserts a false instance of ✱9·1
  (`thm9_unsound_empty`); ✱10's is sound in every structure. PM_CLAIMS: new rows A28, A29; A10, A12
  checked, A11 (use) checked, A15, A17 partly checked; 77 rows. Ledger `data/star9f_ledger.json`, checked
  by `Checks/LedgerCheck.lean` (check 3). AllAxioms: 33 declarations use an axiom (was 25), the 8 new
  ones Lean's `injEq` lemmas of ✱9's syntax; no PM derivation uses one. AxiomCheck now prints every
  public theorem of every file under PM/ (1017).
- **PM's claim of p. 200 checked** (docs/PM_CLAIMS.md, D1): "every proposition about a class expresses an
  extensional property of the determining function of the class". `ClsExpr` (PM/Star20.lean) is the
  expressions of a class that PM's notation forms, and `clsExpr_ext` proves each of them extensional, so the
  analogue of ✱20·3 for classes of classes holds for them with no premise (`qclsExpr20_3`). The same for
  relations, p. 213 (`RelExpr`, `relExpr_ext`, `qrelExpr20_3`). `qcls20_3` keeps its premise for an
  arbitrary Lean function (docs/CLASSES_OF_CLASSES.md). The bare ψx is not an expression PM's notation
  forms about the class, and is extensional anyway (`clsExt_app`, `relExt_app`). ✱20·4 and ✱21·4 keep
  their proofs from the premise version; checks prove the same statements by the premise-free route.
- **Design principles and PM's claims** (`docs/PRINCIPLES.md`, `docs/PM_CLAIMS.md`): the standing principles
  collected on one page, with a new one (maintainer): PM's claims about its own system are checked in Lean,
  not adopted. 75 such claims from the Introduction and ✱1–✱21 are listed with their pages and status.
- **LICENSE-CC0**: the CC0 1.0 legal code, for `docs/FORMALIZATION_COMPARISON.md`.
- **Classes of classes** (maintainer's decision, docs/TYPES_DESIGN.md §5, Q6): ✱20·03, ✱20·08, ✱20·081
  and ✱21·03, ✱21·08–✱21·083 as printed, and ✱20·4, ✱20·41, ✱21·4, ✱21·41 by the analogue of ✱20·3 for
  classes of classes (p. 206). ✱20 is at 53 of 55, ✱21 at 46 of 48 (docs/CLASSES_OF_CLASSES.md).
- **Regression tests** (`tests/`, `Checks/`): one test for each mistake a review has caught; the statements
  once corrected are pinned in the build; `Checks/LedgerCheck.lean` checks citations and ledger rows
  against proof terms; `tests/run_all.sh` runs every check.
- **Ledgers list every proposition a proof uses.** ✱10·21, and the steps carried under an apparent
  variable inside helper lemmas, are listed as under-exists glue; an equivalence read as an implication is
  tacit outside a displayed chain and chain glue inside one (docs/FIDELITY.md). ✱20·11, ✱21·11 and ✱21·21
  become `pm-lines+extra`.
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
