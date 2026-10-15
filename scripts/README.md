# Scripts

Python 3 (standard library only). Run from the repository root; every script finds the root from its own
path. Building the Lean project needs none of them: their outputs are committed.

| Script | Reads | Writes |
|---|---|---|
| `parse_vol1.py HTML` | Project Gutenberg eBook #78050, HTML edition | `data/vol1.jsonl` |
| `vol1_items.py` | `data/vol1.jsonl` | `data/vol1_items.json` |
| `gen_lean.py` | `data/vol1.jsonl` | `PM/Statements.lean` |
| `gen_quant_lift.py` | `PM/Statements.lean`, `PM/Replay.lean`, `PM/Replay2.lean` | `PM/QuantLift.lean` |
| `gen_axiomcheck.py` | the PM source files | `AxiomCheck.lean` |
| `star9_readings.py` | the output of `Checks/Star9Readings.lean`, `PM/Found9/Star9.lean` | `docs/STAR9_READINGS.md` (`--check`: exit 1 if it is not up to date) |
| `export_names.py` | the output of `Checks/ExportStatements.lean`; `data/naming/*`, `data/export_names.lock`, `data/changes.tsv`, `data/vol1_items.json` | `data/export_names.json`, `Checks/Counterparts.lean` and `Checks/MathlibCounterparts/MathlibCounterparts.lean` (`--check`: exit 1 if one is not up to date or a name or counterpart breaks a rule of docs/NAMING.md; `--tsv PATH [--chapters 1-5]`: a review table with each formula and counterpart; `--write-lock [--chapters 1-5]`: at a release, adds the names released, and the readings they use, to the locks; `--root`: the Merkle root of the lock, for the release's version; `--verify-counterparts DIR`: checks each counterpart's file and line, and a Mathlib one's header, in local checkouts; `--pm-names HTML`: first rewrites `data/naming/pm_names.json` from Gutenberg eBook #78050) |
| `prove2me/export.py`, `prove2me/metadata.py`, `prove2me/verify.py` | a commit of the repository (`git archive`), built with the platform's Lean; `data/export_names.json`, `data/naming/*`, `data/vol1.jsonl`, the replay ledgers; Prove2Me's two extraction scripts, from a checkout | the files of an export to Prove2Me and their titles and descriptions, in `.lake/prove2me/out/`, and the checks of them with the platform's Lean ([prove2me/README.md](prove2me/README.md)) |
| `progress.py` | the PM files and ledgers at a git commit; `data/vol1_items.json`, `data/vol2_labels.json` | the tables of `docs/PROGRESS.md` and its paragraph on the checks' unit (with `--update`) |
| `roadmap_chart.py` | `data/roadmap.json`; the counts its notes cite, from `docs/PROGRESS.md`, `docs/PM_CLAIMS.md`, `data/star9f_ledger.json`; the `deps:` annotations of `docs/ROADMAP.md` | `docs/roadmap/*.svg` and the generated regions of `README.md` and `docs/ROADMAP.md` (`--check` writes nothing and fails if any differs; both fail if a dependency the prose states disagrees with the data) |
| `mutation/mutate.py --quick` or `--full` | the proof terms, through `mutation/StatementMutation.lean` (after a `lake build` of what it imports); the PM source files; `mutation/expected.json` | nothing tracked (working files in `.lake/mutation/`): reports unused hypotheses and statement mutants that a proof still accepts, and exits 1 on any finding `expected.json` does not list ([docs/STATEMENT_MUTATION.md](../docs/STATEMENT_MUTATION.md)); `--quick` is a step of `tests/run_all.sh` and check 0 of `prove2me/verify.py`, `--full` a step of `release_check.sh` |
| `external_checkers.py` | the `.olean` files of `PM` and `Checks.PinnedStatements` (after a `lake build` of them); lean4export, con-leche and nanoda_lib, cloned at pinned commits and built (needs git, network on the first run, and `cargo`) | nothing tracked (clones, builds, logs and `summary.json` in `.lake/external-checkers/`; the export is deleted after a run that passes unless `--keep-export`): exports the proofs, has con-leche `--verified` and nanoda check them, scans the export for the axioms they must not rest on (names compared as structured names), requires each checker's declaration count to agree with the export's, checks with `implementation_attributes.lean` that no declaration under `PM` or `Checks` has an implementation attribute (which the export leaves out), and runs ten negative controls; exit 1 if any fails ([docs/VERIFICATION.md](../docs/VERIFICATION.md#external-checkers)); a step of `tests/run_all.sh` and, with `--nanoda-upstream require` (nanoda's pin must be upstream's head), of `release_check.sh` |
| `release_check.sh` | everything `tests/run_all.sh` reads, Mathlib at the pinned commit (fetched into `Checks/MathlibCounterparts/.lake/`) | nothing tracked: the checks run before a release, after `tests/run_all.sh` (`SKIP_STANDING=1` leaves it out): `external_checkers.py --nanoda-upstream require`, `mutation/mutate.py --full`, the Mathlib counterparts compiled against the pinned Mathlib, and with `COUNTERPART_SOURCES=DIR` `export_names.py --verify-counterparts DIR` ([docs/VERIFICATION.md](../docs/VERIFICATION.md#before-a-release)) |
| `kernel_census/census.py` | every declaration of the library targets and its closure, through `kernel_census/KernelCensus.lean` (after a `lake build` of what it imports; it refuses a library file with an `example`); `tests/expected_kernel_features.txt`, `tests/expected_axiom_users.txt` | the tables of `docs/KERNEL_CENSUS.md` (`--write`; `--check`: exit 1 if they are not up to date); `--ratchet`: nothing, exit 1 if the kernel features of the PM derivations or the axiom users differ from the expected lists (`--update` rewrites the features); `--levels`: prints the declarations of the closures of D and of (a) used at a universe level above `Type`; working files in `.lake/kernel_census/` ([docs/KERNEL_CENSUS.md](../docs/KERNEL_CENSUS.md)) |
| `lake env lean kernel_census/type_as_term.lean` | the census's derivation theorems and their closure (its module lists, copied, must be kept equal to `KernelCensus.lean`'s) | nothing tracked, run by hand: prints where in the closure a type appears as a term, and the universe levels used, the measurement task (e) of the roadmap cites ([docs/ROADMAP.md](../docs/ROADMAP.md)) |
| `check_svg.py FILE.svg ...` | SVG charts | nothing: checks each is well-formed, has a dark-mode block, and has no overlapping text |
| `count_setmm.py CLONE [COMMIT]` | `set.mm` and `iset.mm` from a git clone of metamath/set.mm, at the commit pinned in `data/roadmap.json` (or COMMIT) | nothing: prints the counts of PM-numbered theorems the roadmap cites (labels matching `pm[0-9]+\.`, `$p` statements only, comments excluded) |

## Getting the source texts

The ebooks are not in this repository. To regenerate from scratch, download the HTML editions from Project
Gutenberg:

- Vol I, eBook #78050: https://www.gutenberg.org/cache/epub/78050/pg78050-images.html
- Vol II, eBook #78255 (only for `data/vol2_labels.json`):
  https://www.gutenberg.org/cache/epub/78255/pg78255-images.html

The committed files were made from copies with these SHA-256 sums:

```
080479efccf705a165c5c7699ea1c66d239c7d639db0a6c12e8a2087ebf44ec9  pg78050-images.html
617238413ccc1dc622a05645554f4aaeb34cbdaf88834e89cbafa7f268dc32cb  pg78255-images.html
```

Ebooks are sometimes revised after release. If your download differs, the parse may differ too. Compare the
outputs with `git diff`.

## Regenerating the statements

```
python3 scripts/parse_vol1.py path/to/pg78050-images.html   # data/vol1.jsonl: records 3449
python3 scripts/vol1_items.py                               # data/vol1_items.json: items 3450
python3 scripts/gen_lean.py                                 # PM/Statements.lean: statements 193
python3 scripts/gen_quant_lift.py                           # PM/QuantLift.lean: 188 theorems lifted
python3 scripts/gen_axiomcheck.py                           # AxiomCheck.lean: 1722 names
git diff --stat                                             # expect no change
lake build
```

From the committed `data/vol1.jsonl`, the last four commands reproduce the committed files byte for byte, and
so does `export_names.py` its three files: `tests/test_regeneration.py` runs them in a scratch copy and fails
if any file differs (a step of `tests/run_all.sh`). The same holds for `parse_vol1.py` with the copy of eBook
#78050 whose SHA-256 sum is given above.

`gen_lean.py` overrides one statement: ✱1·4, where the ebook has `p ∨ p` and the 1910 print has `q ∨ p`
([docs/FIDELITY.md](../docs/FIDELITY.md)). It skips the ✱1 rules stated in words and ✱3·03, which have no
assertion sign; so 193 statements are written for the ✱1–✱5 items that are not definitions. The proofs use
the 188 of ✱2–✱5.

Its dot-notation parser is copied from `scripts/dots.py` of the companion
[text audit](https://github.com/willmcginnis/principia-mathematica-text-audit) (same author, MIT), so the
script needs nothing outside this repository.

## Regenerating the progress tables

```
python3 scripts/progress.py --update                         # docs/PROGRESS.md, from HEAD
python3 scripts/progress.py --ref <commit>                   # print the tables for another commit
python3 scripts/progress.py --vol2-html path/to/pg78255-images.html --update   # also rebuild data/vol2_labels.json
```

`progress.py` reads the Lean files and ledgers from git, not the working tree, so commit first and then
update `docs/PROGRESS.md`. The tables name the commit they were measured at.
