# Regression tests

One test for each mistake a review has caught, where a test is possible. `tests/run_all.sh` runs them
all with the build and the root checks; `.github/workflows/check.yml` runs it on every push and pull
request. Each test was checked to fail when its mistake is put back.

| Mistake a review found | Guarded by |
|---|---|
| `transIff`'s docstring (PM/Chain.lean) cited ✱4·22, which its proof did not use | `Checks/LedgerCheck.lean`, check 1: every proposition a PM/Chain.lean docstring cites is used by the proof term |
| ✱10·281 was missing from the ledger rows of ✱14·18 and ✱14·203 | `Checks/LedgerCheck.lean`, check 2: every PM proposition a row's proof uses is listed in the row (uses awaiting a decision would go in `ledger_unlisted_uses.txt`, now empty) |
| Rows counted an equivalence read as an implication as an extra (✱3·26, ✱3·27), against the rule that it is tacit outside a chain and chain glue inside one | `Checks/LedgerCheck.lean`, check 2: a chain's ≡-to-⊃ step must be listed as ✱3·26, and ✱3·26 or ✱3·27 may be listed only where the proof uses it on a product that is not an equivalence, or in a chain |
| Ledger rows listed chain glue or their own tacit steps in `extra_used` | `test_fidelity_counts.py`: fidelity_counts.py reports no inconsistent row, and the Fidelity table equals its output |
| Four ledger files lost their final newline | `test_ledger_files.py`: every ledger parses, ends with a newline, and its rows have their ledger's fields |
| ✱14·32 was weakened from ≡ to ⊃ | `Checks/PinnedStatements.lean` (part of `lake build`): the exact statements of the propositions whose statement was corrected |
| Claims stated more strongly than proved (now `styles_equiv`, `realPhi_every_system`, `second_clause_iff_lowestOrder`, ...) | `Checks/PinnedStatements.lean` |
| (the list of axiom users must change only deliberately) | `test_axiom_users.py` against `expected_axiom_users.txt` |
| A count of proved propositions included primitive propositions | `test_proved_counts.py`: the docs' counts per chapter equal the ledgers' |
| data/README.md gave the ✱20 and ✱21 ledgers 51 and 44 rows; they have 53 and 46 | `test_data_readme.py`: the rows (and the rows per category) data/README.md gives for each ledger file equal the file's |
| AxiomCheck.lean's generator listed its files by name, so `PM/Found9/` was not covered; and it ignored `namespace` blocks, printing `ClsExpr.and` as the nonexistent `PM.and` | `test_axiomcheck_coverage.py`: the generator reads every PM/**/*.lean file, every public theorem is printed under its full name, and AxiomCheck.lean is up to date |
| The docs kept the count of axiom users at 25 after eight `injEq` lemmas were added | `test_axiom_users.py`: the count each doc gives (and the number of `injEq` lemmas) equals `expected_axiom_users.txt` |
| PROGRESS.md's paragraph on the checks' unit, written by hand, kept an earlier revision's counts (485, 276, 272, 460) under tables of a later one (629, 420, 416, 604) | `test_progress_units.py`: the paragraph and the tables are what `scripts/progress.py` generates at the commit the tables name, and the total it computes for the working tree is the count RedCheck and StyleCheck print |
| TYPES_DESIGN.md's table of files gave `PM/Star23.lean` 838 lines after the file had grown to 850 | `test_types_design_lines.py`: every line count in that table equals the line count of its file, and every file it names exists |
| A merge left PM_CLAIMS.md's totals inconsistent with its rows | `test_pm_claims_counts.py`: each clause of the Counts paragraph equals a recount of the rows with its status, and every row is counted once |
| ✱9's disjunction did not follow ✱9·07·08 as printed, and under the printed definitions a step of PM's proof of ✱9·31 cited as definitional is not a definitional rewrite | `test_star9_readings.py`: the results under each reading (A as printed; C as printed + ✱8·13, the working reading; L, Landini's ✱9+, a cross-check; B, the cross-check) are pinned, columns in that order; every step of ✱9's proofs that PM justifies by definitions is checked under C except ✱9·31's (3)–(4), which C takes by ✱8·13, and the steps checked under one reading only are exactly the expected one; where C uses ✱8·13 and L uses Switch is pinned; docs/STAR9_READINGS.md is up to date. The definitions, the rules ✱8·13 and Switch, how they relate, and the counterexample to their side condition read without restriction are pinned in `Checks/PinnedStatements.lean` |
| AxiomCheck.lean's generator read a `mutual … end` block as closing the namespace, and `_root_.A.b` as a name in the namespace | `test_axiomcheck_coverage.py` (every public theorem printed under its full name) |
| ✱9's own ledger could list fewer propositions than its proofs use | `Checks/LedgerCheck.lean`, check 3: as check 2, for `data/star9f_ledger.json` |
| LedgerCheck accepted a fabricated citation: ✱5·19 added to the `cited_used` of ✱22·1 passed | `Checks/LedgerCheck.lean`, the reverse check of checks 2 and 3: every entry a row claims as used (`cited_used`, `extra_used`, `glue`) is used by its proof, through helpers; a definition only where a declaration realizing it is referenced, a primitive proposition or the rule where its constructor is applied; claims awaiting a decision would go in `ledger_unused_claims.txt`, now empty. `tests/ledger_negative.sh`: in a scratch copy of the ledgers, ✱5·19 or ✱23·01 added to ✱22·1's `cited_used`, or ✱4·2 removed from it, each makes the check fail with the message naming it |
| (the roadmap's charts and lists must not drift from its data, or from the counts they cite) | `test_roadmap.py`: `scripts/roadmap_chart.py --check` regenerates the charts and the generated text of README.md and docs/ROADMAP.md and finds no difference (it also refuses a *measured* prior-work entry without a pinned source); `scripts/check_svg.py` passes on every chart; every sentence of docs/ROADMAP.md's hand-written prose that uses a gate word (needs, gates, waits for, ...) or a soft word (helps, benefits) carries a `deps:` annotation whose pairs are hard (gates), soft (helps) or absent (not) dependencies in the data, gate wording carrying only gates and soft wording only helps; mutations of the page (helped by → gated by, gates → helps, does not gate → gates, an edge the data lacks, a missing annotation) make the check fail; every row of `docs/PM_CLAIMS.md` is covered by exactly one task, and a task with claims is done exactly when each of its claims is checked, and mutations of the data (a claim left out, given to two tasks, unknown, open in a done task, checked throughout a task not done) make that check fail |
| (export names are permanent once released, so they must follow docs/NAMING.md from the start) | `test_export_names.py`: `scripts/export_names.py --check` passes (data/export_names.json is up to date; pattern, order of the suffixes, PM's name and no other word, slots for definitions and rules, readings, frozen reading meanings, unique names and platform slugs, no top-level `PM_`, the descriptor's vocabulary, the lock of released names, the versions of superseded cards, the counterparts), and 39 mutations, at least one per rule (among them a changed statement and a changed definition under a scratch lock, `_v2` before `_reading_`, a changed reading meaning, a slug collision, a descriptor or a Mathlib word in a name, and malformed or inexact counterparts), each caught by its rule and missed when the rule is switched off; under a scratch lock, a changed Lean statement or definition fails the lock, and a new working reading renames nothing |
| A counterpart was accepted on its record's word: another declaration (`Or.inl` for ✱1·3, with its real signature and line) or a signature `NOT A LEAN TYPE` passed | `test_counterparts.py`: Lean (`Checks/Counterparts.lean`, also a step of run_all.sh) checks each Lean core counterpart's type against PM's formula, and `scripts/export_names.py` reads every signature strictly; each of five false matches (the two found, an equivalence swapped without the record saying so, a `Sort` parameter specialized without it, two variables identified) fails both, and passes again when reverted; a declaration that only unfolds to the formula fails; the header at the pinned line must be the recorded signature (`--verify-counterparts`); and the same check passes with the pinned Lean v4.33.1 when installed |
| Superseding a released card renamed the unchanged original to `_v2`, and declarations moved to `PM/Deprecated/` were not exported | `test_versioning.py`: in a scratch copy, after a release, ✱21·71 is superseded (old declaration to `PM/Deprecated/Star21.lean` with `@[deprecated]`, new one `PM.q21_71_v2`, a row of data/changes.tsv); both names are exported, the old with its locked digest, the new as `_v2`, and every check passes; without the row, or without the old declaration, the check fails. `test_export_names.py`: a row of data/changes.tsv renames nothing |
| Locking a replacement (`_v2`) dropped its link to the card it replaces, so the next check failed with no change to the source | `test_versioning.py`: `_v2` is released, regenerated, locked again and checked, every generated file and the lock byte for byte the same; then superseded by `_v3`, released the same way, the chain of three linked in both directions. `test_export_names.py`: generate, `--write-lock`, generate is a fixed point for the repository under its current lock, and for a chain `_v2`, `_v3` locked in turn |
| The search for forbidden keywords exempted `unsafe def main` in any Lean file under scripts/, not only in scripts/prove2me/extract_commands.lean | `test_forbidden_keywords.py`: on scratch trees outside the repository, `tests/forbidden_keywords.sh` (the step of run_all.sh) passes the exempt line in its own file and finds the same line in four other files under scripts/ and one outside it, and any other `unsafe` line in the exempt file; the repository passes |

`test_statement_mutation.py` guards a tool rather than a past mistake: the source editor of the
statement mutation (`scripts/mutation/mutate.py`, [docs/STATEMENT_MUTATION.md](../docs/STATEMENT_MUTATION.md)),
which replaces one hypothesis by `True` on each binder form the repository uses; the driver's `lake build`
before any analysis, without which it would read proofs older than the sources; and the classes of the
findings listed in `scripts/mutation/expected.json`; and where the tiers run: `--quick` as a step of
`run_all.sh` and as check 0 of `scripts/prove2me/verify.py`, which fails an export if the tool fails or is
missing (shown with stand-in tools) unless `--no-mutation` skips it for a commit without the tool, recorded
as skipped with the reason (and refused for a commit with the tool), and `--full` in
`scripts/release_check.sh`.

`test_regeneration.py` guards the tie of the statements to PM's text, which no proof checks: it runs every
generator (`vol1_items.py`, `gen_lean.py`, `gen_quant_lift.py`, `gen_axiomcheck.py`, `export_names.py`) in
a scratch copy, and each file they write must be the committed one, byte for byte; every Lean file whose
head says it is generated must be listed with its generator. It fails on a line added by hand to each
generated file, and on ✱2·02 changed in `data/vol1.jsonl` without regenerating.

`test_counterparts.py` also checks the Mathlib counterparts' file against its generator, and that the
repository's own Lake project requires nothing. When Mathlib has been fetched into
`Checks/MathlibCounterparts/` (by `scripts/release_check.sh`), it compiles that file against the pinned
Mathlib and requires four false matches, recorded on Mathlib records, to fail it: an equivalence reversed
without the record saying so, another declaration of the same file, a wrong `classical` flag, and two
variables identified. Without Mathlib that part is skipped.

`test_kernel_census.py` is a ratchet rather than a guard against a past mistake: the features of Lean's
kernel that the PM derivations rely on ([docs/KERNEL_CENSUS.md](../docs/KERNEL_CENSUS.md)) must equal
`expected_kernel_features.txt`, so a new one (a quotient, an axiom, a mutual or nested inductive type,
a compiled-only constant reaching a derivation) fails until it is accepted on purpose. The test also checks
the driver's copy of `example`s into theorems and the ratchet's comparison on synthetic input.

Run everything with `tests/run_all.sh` (`SKIP_SLOW=1` leaves out ClauseSearch, about a minute), or
only the Python tests with `python3 -m unittest discover -s tests` once the project is built. The long
checks run before a release are `scripts/release_check.sh`
([docs/VERIFICATION.md](../docs/VERIFICATION.md#before-a-release)): it runs `tests/run_all.sh` first, then
`scripts/mutation/mutate.py --full` (tens of minutes on 8 cores) and the Mathlib counterparts. Run it on
your own machine before an export or a release, not on a time-limited remote.
