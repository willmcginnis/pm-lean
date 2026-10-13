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
| `export_names.py` | the output of `Checks/ExportStatements.lean`; `data/naming/*.json`, `data/export_names.lock` | `data/export_names.json` (`--check`: exit 1 if it is not up to date or a name breaks a rule of docs/NAMING.md; `--tsv PATH [--chapters 1-5]`: a review table; `--pm-names HTML`: first rewrites `data/naming/pm_names.json` from Gutenberg eBook #78050) |
| `progress.py` | the PM files and ledgers at a git commit; `data/vol1_items.json`, `data/vol2_labels.json` | the tables of `docs/PROGRESS.md` (with `--update`) |
| `roadmap_chart.py` | `data/roadmap.json`; the counts its notes cite, from `docs/PROGRESS.md`, `docs/PM_CLAIMS.md`, `data/star9f_ledger.json`; the `deps:` annotations of `docs/ROADMAP.md` | `docs/roadmap/*.svg` and the generated regions of `README.md` and `docs/ROADMAP.md` (`--check` writes nothing and fails if any differs; both fail if a dependency the prose states disagrees with the data) |
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
python3 scripts/vol1_items.py                               # data/vol1_items.json: items 3449
python3 scripts/gen_lean.py                                 # PM/Statements.lean: statements 193
python3 scripts/gen_quant_lift.py                           # PM/QuantLift.lean: 188 theorems lifted
python3 scripts/gen_axiomcheck.py                           # AxiomCheck.lean: 1017 names
git diff --stat                                             # expect no change
lake build
```

From the committed `data/vol1.jsonl`, the last four commands reproduce the committed files byte for byte. The
same holds for `parse_vol1.py` with the copy of eBook #78050 whose SHA-256 sum is given above.

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
