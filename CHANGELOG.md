# Changelog

Coverage and semantic changes, newest first, from the git history. Commit hashes are given where a change is
one commit. Current counts are in [docs/PROGRESS.md](docs/PROGRESS.md).

## 2026-10-13

- **Export release 1.0.0 prepared** (docs/EXPORT_LOG.md), not yet public: PM ✱1–✱5 on Prove2Me, 196
  cards and 4 definition bundles, version **1.0.0+m.7d40537313d3**. `data/export_names.lock` now holds the
  196 names released (`scripts/export_names.py --write-lock --chapters 1-5`, which locks only the chapters
  given and only the readings they use; none here). The Merkle root is built: RFC 6962's tree hash over
  the lock (`--root`), tested against the RFC's test vectors (docs/VERSIONING.md).
  - **The exporter is in the repository**, `scripts/prove2me/`: the platform's files from a commit, built
    with the platform's Lean, with names read from data/export_names.json and counterparts from
    data/naming/counterparts.json; titles and descriptions (each beginning with a DRAFT line); and the
    checks before upload. One check is new: each card's statement and definitions digests, computed from
    the uploaded files, must equal the locked ones. The canonical text of statements moved to
    `Checks/Canon.lean` for that, shared with `Checks/ExportStatements.lean` (whose output is unchanged).
    No credentials or network calls are in the repository.
  - **Definition bundles have their own names**, `PM_core_<words>` (data/naming/definition_bundles.json),
    checked by the new `bundle_names` rule (docs/NAMING.md).
  - **docs/NAMING.md lists the rules proved as theorems** (✱9·12, ✱9·13, ✱10·11, ✱10·13, ✱11·07,
    ✱11·11, ✱11·13, ✱11·311): their names keep `_rule`, PM's classification, and each theorem states the
    rule, with the premisses as hypotheses, not an asserted implication. A test checks the table against
    the export names and the source lines.
  - **docs/VERSIONING.md, rule 7**: a Lean or Mathlib upgrade that changes a statement's canonical text
    without changing its meaning is examined by a person and re-locked in a MAJOR release.
- **A locked replacement keeps its link to the card it replaces.** Found by a release review of the
  export names, before any release. Once a replacement `_v2` was itself locked, the generator dropped
  its `supersedes`, and the next check failed with no change to the source. The link now comes from the
  Lean names whether or not the replacement is locked, so locking is a fixed point: generate,
  `--write-lock`, generate gives the same files. `tests/test_versioning.py` now runs the whole life
  cycle twice (supersede, release, regenerate; then `_v3`), and `tests/test_export_names.py` checks the
  fixed point for the repository and for a chain locked in turn (docs/VERSIONING.md).
- **Counterparts checked against their declarations' types; superseded cards keep their names.** Found by
  a release review of the export names, before any release.
  - **Counterparts.** A counterpart's record was trusted for its formula. Another real declaration with
    its real signature and line (`Or.inl` for ✱1·3), or the signature `NOT A LEAN TYPE`, passed the
    check. Now each record gives the instantiation of the declaration's variables. The 54 Lean core
    counterparts are checked by Lean, in the new `Checks/Counterparts.lean`, generated from the records
    and the exported statements and run by `tests/run_all.sh`. The kernel checks each declaration as a
    proof of PM's formula, and a `#counterpart` command checks that its type is that formula exactly,
    with its printed signature, its variables, and the recorded swaps and specializations. It also
    passes with the pinned Lean v4.33.1. The 14 Mathlib counterparts are checked from source:
    `scripts/export_names.py` reads every signature strictly as a type of the propositional fragment and
    compares it, instantiated, with PM's formula. `--verify-counterparts` also checks the header at the
    pinned line. Compiling the Mathlib ones remains a follow-up (docs/NAMING.md). New:
    `tests/test_counterparts.py`.
  - **Versions.** Adding a row to data/changes.tsv renamed the unchanged locked declaration to `_v2`, and
    declarations moved to `Deprecated/` were not exported. Now a row renames nothing. A superseded
    declaration keeps its Lean name in `PM/Deprecated/<module>.lean` with `@[deprecated]`, and is still
    exported under its locked name and digest, marked deprecated and pointing to its replacement. The
    replacement is the Lean declaration `<name>_v<N>`, exported as `_v<N>` with its own digest.
    `Checks/ExportStatements.lean` prints `PM.Deprecated` and each `@[deprecated]` target. The `versions`
    check requires the row, the attribute and both declarations to agree (docs/VERSIONING.md). New:
    `tests/test_versioning.py` supersedes ✱21·71 end to end in a scratch copy.
- **Export names: PM's number and PM's own name only** (docs/NAMING.md), before any release. A name is
  `PM.star<N>_<M>[_<pmname>][_df|_rule][_reading_<word>][_v<N>]`: no generated descriptor and no Mathlib
  word (✱2·01 is `PM.star2_01_abs`, ✱2·14 `PM.star2_14`); 523 names, the longest 33 characters (was 56).
  The descriptor stays in data/export_names.json as a field for titles and search. New slots `_df` for
  definitions and `_rule` for inference rules (data/naming/slots.json), used now by twelve names (✱9·12,
  ✱9·13, ✱10·01, ✱10·11, ✱10·13, ✱11·07, ✱11·11, ✱11·13, ✱11·311). `_vN` is the last part. Exact Lean and
  Mathlib counterparts of ✱1–✱5 are metadata, data/naming/counterparts.json: 68 records pinned to Lean
  `819816b` and Mathlib `0df444a`, under a structural criterion stated in docs/NAMING.md (only the two
  sides of an equivalence may be swapped; 20 counterparts are classical, 17 swap sides). The lock binds
  meaning: `Checks/ExportStatements.lean` also prints each statement's elaborated type in a canonical text
  and the definitions it uses, data/export_names.json carries a statement digest and a definitions digest,
  and data/export_names.lock (empty until the first release) records them with the reading each card is
  released under; a locked name whose statement or definitions change fails with a pointer to `_vN` and
  data/changes.tsv, and a later change of ✱9's working reading renames nothing locked. Reading meanings
  are append-only once locked (data/naming/readings.lock). Checks for slug uniqueness ignoring case, the
  order of suffixes, the slots, a changes.tsv row for each `_vN`, and the counterparts (pinned commit,
  well-formed file:line, statement equal to the exported one up to the recorded swaps); 33 seeded
  mutations in tests/test_export_names.py. Follows an external review of the naming plan.
- **Licence: `MIT OR Apache-2.0`.** The code, ledgers and documentation are now dual licensed, at the
  user's option, under the MIT License (`LICENSE`, renamed `LICENSE-MIT`, same holder) and the Apache
  License 2.0 (`LICENSE-APACHE`, the text of apache.org, sha256 `cfc7749b…`). docs/FORMALIZATION_COMPARISON.md
  stays CC0 1.0. CITATION.cff gives the SPDX expression. CONTRIBUTING.md has an inbound=outbound clause
  (contributions are dual licensed the same way unless stated otherwise) and a section on questions,
  corrections and proposals (GitHub issues). data/README.md adds, as fact, that terms outside the USA may
  differ (in the UK a joint work's term runs from the death of the last author; Russell died in 1970).
- **Export names** (docs/NAMING.md). Each PM proposition the repository states has an export name for
  formalization platforms, `PM.star<N>_<M>_<descriptor>[_reading_<word>]`: PM's number, PM's own name when
  it gives one (data/naming/pm_names.json, from PM's list of propositions referred to by names), a
  descriptor generated from the elaborated statement in Mathlib's style from a closed vocabulary
  (data/naming/vocabulary.json), and for ✱9 by its own method the reading (data/naming/readings.json:
  A `printed`, C `russell`, L `landini`, B `convention`, P `prenex`). `Checks/ExportStatements.lean` prints
  the statements; `scripts/export_names.py` writes data/export_names.json (523 names: ✱1–✱5 196 with three
  results about the system, 156 marked for review) and checks it: pattern, unique names and platform
  slugs, vocabulary, PM's name first, readings, no top-level `PM_`, and released names frozen in
  data/export_names.lock (empty until the first release). A step of tests/run_all.sh;
  tests/test_export_names.py seeds a mutation for each rule.
- **Versioning of exports** (docs/VERSIONING.md): names permanent and never reused; a new statement is
  `name_vN` and the old card is deprecated; proofs and descriptions change in place; superseded
  declarations kept forever as `@[deprecated]`; SemVer releases (MAJOR an environment move, MINOR cards
  added or superseded, PATCH proofs and documentation) with the Merkle root of the statements as build
  metadata (planned); data/changes.tsv for dated name changes (header only). The first public export will
  be 1.0.0.
- **Export log** (docs/EXPORT_LOG.md): a dated public log, starting with the private pilot of ✱1–✱5
  (2026-10-12).
- **No auto-bound implicits.** `upd_self` (PM/Complete.lean) declares its binder `{b : Bool}`; it was the
  only declaration that relied on an auto-bound implicit, and lakefile.toml now sets `autoImplicit = false`.

## 2026-10-12

- **Roadmap: ✱25, and every claim of PM_CLAIMS.md in a task.** A task for ✱25 (the universal and null
  relations and the existence of relations, pp. 241–243: 3 definitions, 70 assertions, whose proofs PM
  omits as proceeding "precisely as in ✱24"), after ✱20–✱24 and before ✱30–✱38, which cites it. A
  subgroup *PM's claims about its own system* groups the 77 rows of `docs/PM_CLAIMS.md` by the page's
  sections and the kind of work left: the 27 rows checked with their chapters (done), ✱9's method,
  metatheorems of ✱1–✱11, reducibility and orders, the hierarchy of types, descriptions, classes and
  relations, formulas PM says are not theorems, and claims about the whole work; B11 stays with the
  order-seeing model and D1 with extensionality. `scripts/roadmap_chart.py` refuses data in which a row is
  covered by no task or by two, or a task with claims is done while one is open (or not done when all are
  checked); `tests/test_roadmap.py` checks both, with mutations. A subgroup *Formalization platforms*
  under *Comparing across* holds a task for exporting to formalization platforms, in progress: the
  repository stays the source of truth, an exporter generates the platform's definitions, statements and
  solutions from it, and proofs found there are pulled back and re-checked here; the first pilot is a
  private mission for ✱1–✱5 on Prove2Me, whose default environment (Lean v4.33.1) builds the repository
  at e3f64c3 with only the toolchain line edited. docs/ROADMAP.md records as open that PM_CLAIMS.md
  covers the Introduction and ✱1–✱21 only, so the claims of ✱22–✱97 are not yet catalogued.
- **✱9 under four readings; the working reading C is the definitions as printed with Russell's ✱8·13
  carried over to ✱9** (`PM/Found9/`; docs/REPAIRS.md R1–R5, docs/STAR9_READINGS.md,
  docs/STAR9_FOUNDATION.md §4, §10). ✱9's system is now parametrized by a reading `R`: its definitions
  of ∨ (`Defs`) and its rule (`Rule`: `basic`, `exch`, `prenex`). The working reading went B → C
  (Landini's ✱9+) → C (Russell's ✱8·13) the same day, by the maintainer's rulings: the authors' own fix
  ranks first, a published repair second (kept as L), and our own convention is kept as a cross-check
  (B). ✱8·13 is read in the second edition (1925, Vol. I, Appendix A, p. 636, page image of a 1963
  impression): "If all occurrences of x are separated from all occurrences of y by a certain stroke, we
  can change the order of x and y in the prefix, i.e. we can replace "(y) : (∃x) . φx | ψy" by
  "(∃x) : (y) . φx | ψy" and vice versa. Pp".
  - **A** (`Reading.printed`): ✱9·01–✱9·08 as printed (`PF.orPrinted`), kept and marked; with two
    quantifiers of the same kind the left side's first, the order ✱8 states (p. 635) and the
    Introduction defines (1910 p. 49; second edition p. 47) (R2).
  - **C** (`Reading.russell`, the default): A's definitions and ✱8·13 as a primitive rule (`Thm9.exch`,
    `ExchStep`; R1): two adjacent quantifiers of the prefix, of any kinds, separated by the ∨ of the
    matrix (`Sep`), change their order, both ways (`ExchStep.symm`). ✱8·13 is derived in ✱10
    (`exchStep_q10`), so C is sound; it is no general exchange (`exch_not_general`). `Sep` asks each
    quantifier of the matrix to bind a variable of one part only; with the wording alone the rule would
    be unsound (`switch_wide_unsound`).
  - **L** (`Reading.withSwitch`): Landini's ✱9+ (2000, p. 64; the flaw at ✱9·31 in his §4), credited,
    not the default: his definitions ✱9·yy and ✱9·zz (`PF.orPlus`) and his rule Switch (`Thm9.switch`,
    `SwitchStep`; R3). Switch is the (x)(∃y) direction of ✱8·13 (`SwitchStep.toExch`,
    `ExchStep.toSwitch`) and a derived rule of C (`switch_russell`); every step of ✱8·13 is derivable
    in L (`exch_plus`); Switch is derived in ✱10 (`switchStep_q10`).
  - **B** (`Reading.convention`): a precedence convention read off PM's proofs (`PF.or`; R4), kept as a
    cross-check. The prenex Switch, an earlier repair, is kept for comparison (`Reading.prenexSwitch`,
    `Thm9.prenexSwitch`; R5); every theorem of C is one with it (`Thm9.russell_toPrenex`).

  Every proof of ✱9·2–✱9·521 except ✱9·31 is stated once for every reading; each step PM justifies by
  definitions is taken by `by_defs`. Results, measured and pinned (docs/STAR9_READINGS.md,
  `tests/test_star9_readings.py`, generated by `scripts/star9_readings.py` from
  `Checks/Star9Readings.lean`):
  - the 28 numbered ✱9 propositions: 27 under A (✱9·31 open), 28 under C, L and B. In C ✱8·13 takes
    one step of PM's proofs, ✱9·31 (3)–(4) (`f9_31_russell`); in L Switch takes the same step
    (`f9_31_switch`); under B it is a definitional rewrite (`f9_31`);
  - the four ✱10 assertions under every reading;
  - p. 142 for one apparent variable per letter: 50 (A), 65 (C), 63 (L), 67 (B) of 70;
  - ✱10·12 for every p given `Rep` and a variable of every type; under B from the primitive
    propositions (`distrib_convention`); `star9_iff_star10` under every reading, given `Rep` for it.

  Open: whether C and L prove the same expressions; completeness of C (ROADMAP; Landini's §5 as prior
  work). Names: the former `PF.or` is `PF.orPrinted` (A), the former `PF.orL` is `PF.or` (B); `f9_31_3`
  is `f9_31_dem`; `QF.toF9` takes the definitions, `Rep` the reading. New: PM/Found9/Exch.lean,
  Switch.lean, SearchTactic.lean (meta code for the proof search, outside the `PM` namespace),
  docs/REPAIRS.md. PM_CLAIMS A10 is checked under the working reading (28 checked, 21 partly checked);
  A11, A12, A14, A15, A17, A28, A29 give results per reading. The ✱9 ledger check also reads
  `f9_N_russell` and `f9_N_switch`. AllAxioms: 39 axiom users (6 new compiler-generated `injEq`
  lemmas); the AxiomCheck generator now reads `mutual` blocks and `_root_` names.
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
