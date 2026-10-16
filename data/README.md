# Data

| File | What it is | Made by |
|---|---|---|
| `vol1.jsonl` | PM Vol I parsed from Project Gutenberg eBook #78050: one record per numbered item | `scripts/parse_vol1.py` |
| `vol1_items.json` | Vol I's 3,450 numbered items with range, chapter, page and category: the denominators | `scripts/vol1_items.py` |
| `vol2_labels.json` | the distinct ✱100–✱234 labels printed in bold in Project Gutenberg eBook #78255 (Vol II): an upper bound | `scripts/progress.py --vol2-html` |
| `replay_ledger.json` | ✱2–✱5, first ledger: all 188 propositions | by hand, with the proofs |
| `replay2_ledger.json` | ✱2–✱5, second ledger: the 85 proofs of `PM/Replay2.lean` | by hand, with the proofs |
| `star11_ledger.json`, `star12_ledger.json`, `star13_ledger.json`, `star14_ledger.json`, `star20_ledger.json`, `star21_ledger.json`, `star22_ledger.json`, `star23_ledger.json`, `star24_ledger.json`, `star25_ledger.json` | one row per numbered item formalized in that chapter | by hand, with the proofs |
| `roadmap.json` | the roadmap: groups, subgroups and tasks, each with status, size, dependencies, order, prior work and the rows of `docs/PM_CLAIMS.md` it checks, and the repositories whose source the prior work was read in, each at a full commit ([docs/ROADMAP.md](../docs/ROADMAP.md)) | by hand; drawn and listed by `scripts/roadmap_chart.py` |
| `star9f_ledger.json` | ✱9 by its own method (PM/Found9): one row per ✱9 number, and for ✱10·01, ✱10·1, ✱10·11, ✱10·12 proved in ✱9 ([docs/STAR9_FOUNDATION.md](../docs/STAR9_FOUNDATION.md)) | by hand, with the proofs |
| `export_names.json` | the export name of every PM proposition the repository states, with its PM number, PM's name, slot, reading, the digests of its statement and of the definitions it uses, a descriptor for titles and search, and its source ([docs/NAMING.md](../docs/NAMING.md)) | `scripts/export_names.py` |
| `export_names.lock` | export names that have been released, each with its Lean declaration, reading and digests; rows are only added; the 196 names of release 1.0.0 (✱1–✱5 and three results about the system), whose Merkle root `scripts/export_names.py --root` prints ([docs/VERSIONING.md](../docs/VERSIONING.md)) | `scripts/export_names.py --write-lock --chapters 1-5`, at a release |
| `naming/vocabulary.json` | the closed list of words descriptors may use, and the word for each Lean connective | by hand |
| `naming/readings.json` | the closed list of reading words (A `printed`, C `russell`, L `landini`, B `convention`, P `prenex`) | by hand |
| `naming/readings.lock` | the reading words and meanings released, which never change; empty, since release 1.0.0 uses no reading | `scripts/export_names.py --write-lock`, at a release |
| `naming/slots.json` | which items take the `_rule` slot besides Vol I's rules in words: the primitive propositions PM states as rules | by hand |
| `naming/counterparts.json` | the 68 exact Lean and Mathlib counterparts of ✱1–✱5, each with its declaration, signature, the instantiation of its variables, statement, file and line at a pinned commit, whether it is classical or has an equivalence reversed, and how it is checked: the 54 of Lean's core by Lean (`Checks/Counterparts.lean`), the 14 of Mathlib by Lean against the pinned Mathlib (`Checks/MathlibCounterparts/`, before a release) and from their source (metadata, not names) | by hand, from an external review |
| `naming/definition_bundles.json` | the names of the definition bundles an export uploads (`PM_core_<words>`), one per source module, with what each holds ([docs/NAMING.md](../docs/NAMING.md)) | by hand |
| `naming/pm_names.json` | PM's "Alphabetical list of propositions referred to by names" (Vol I front matter, Gutenberg eBook #78050) | `scripts/export_names.py --pm-names` |
| `changes.tsv` | dated changes of export names: a statement superseded by `name_vN` ([docs/VERSIONING.md](../docs/VERSIONING.md)); header only until the first change | by hand, with the change |
| `fidelity_counts.py` | the three fidelity counts per chapter, and consistency checks on the ledgers | — |

The meaning of the labels is in [docs/FIDELITY.md](../docs/FIDELITY.md); how the progress tables use these
files is in [docs/PROGRESS.md](../docs/PROGRESS.md).

## Sources and provenance

`vol1.jsonl`, `vol1_items.json` and `vol2_labels.json` are derived from the HTML editions of Project
Gutenberg eBooks #78050 (*Principia Mathematica*, Vol. I, release date February 26, 2026) and #78255 (Vol. II,
March 20, 2026). These are transcriptions of the 1910 and 1912 printings, prepared by Distributed Proofreaders
volunteers. The derived files reproduce the ebook's statements and proof lines (its LaTeX), its page markers
and its labels. They do not reproduce the ebook's front or back matter, except that `naming/pm_names.json`
reproduces Vol I's list of propositions referred to by names (each name, number and formula).

The ebooks and the 1910–1913 books are in the public domain in the USA. Terms elsewhere may differ: in some
countries copyright runs for a fixed period after an author's death, and for a joint work from the death of
the last surviving author (in the UK, 70 years from the end of that year); Whitehead died in 1947 and Russell
in 1970. If you are outside the USA, check the laws of your country before using these files. The HTML files themselves are not in this repository; see
[scripts/README.md](../scripts/README.md) for where to get them and how to regenerate everything from them.

`vol1.jsonl` records, one JSON object per line, in the order of the text:

| Field | Meaning |
|---|---|
| `id` | label, `*N.M` (PM's ✱N·M) |
| `chapter`, `page` | chapter number; page of the 1910 print, from the ebook's page markers |
| `statement` | the statement's LaTeX, as in the ebook, without a trailing bracketed hint |
| `inline_hint` | the bracketed hint printed after the statement, or `null` |
| `has_dem`, `proof` | whether a *Dem.* follows; its lines as `{hint, formula, label}` |
| `is_def`, `is_pp` | flagged as a definition (Df) or primitive proposition (Pp) by the parser |
| `pos`, `occurrences` | offset of the label in the HTML; how many times the label occurs (the record kept is the one with a proof, hint or flag) |

`vol1_items.json` corrects two of the parser's flags (✱1·11 and ✱3·03 are rules that PM marks Pp), adds ✱24·51
(printed on p. 239; the transcription omits it and prints its Dem. under ✱24·5), and puts each item in one
category: `assertion`, `Df`, `Pp` or `rule/prose` (a rule stated in words, ✱1–✱14 only).
Counts: 3,231 assertions, 186 Df, 19 Pp, 14 rules in words. These counts are "from the Gutenberg text with a
few corrections" in [docs/FORMALIZATION_COMPARISON.md](../docs/FORMALIZATION_COMPARISON.md).

`vol2_labels.json` has 3,901 rows `{chapter, number, page}`: each distinct label in bold, with the page of
its first bold occurrence. Combined labels such as ✱106·4·41·411 count once per number. 3,898 are in
✱100–✱234; the other 3 (✱21·411, ✱55·61, ✱73·63) are references back to Vol I. A label repeated in a
quotation counts once. Definitions are included, and the list has not been checked item by item, so it is
an upper bound on Vol II's assertions, not a count of them.

## The ledgers

There are two schemas.

**`replay_ledger.json`** (188 rows, one per ✱2–✱5 proposition):

| Field | Meaning |
|---|---|
| `id` | `*N.M` |
| `tag` | result of the replay search, or of a later rewrite after PM's lines: `FAITHFUL`, a proof from the propositions PM cites alone (and the steps in `tacit`); `REPAIRED`, one that also needs those in `extra`; `UNRESOLVED`, none found |
| `in_lean` | whether that replay is a theorem of `PM/Replay.lean` (absent for `UNRESOLVED`) |
| `cited` | the propositions PM cites |
| `extra` | propositions used that PM does not cite |
| `tacit` | for a proof rewritten after PM's lines: the steps PM leaves tacit that it uses (`Syll`, `*3.03`), as in `replay2_ledger.json` |
| `uses_unresolved`, `repair_src` | bookkeeping of the search: cited propositions that were themselves unresolved, and where a repair came from |

Counts: 100 `FAITHFUL`, 45 `REPAIRED`, 43 `UNRESOLVED`. `in_lean` is true for 103 rows (94 `FAITHFUL`,
9 `REPAIRED`): the 103 theorems of `PM/Replay.lean`. 22 of the 94 were `REPAIRED` by the search and were
rewritten to follow PM's Dem. or hint (they have `tacit`).

**`replay2_ledger.json` and `star*_ledger.json`** (the second schema):

| Field | Meaning |
|---|---|
| `id` | `*N.M` |
| `page` | page of the 1910 print (`star*` only) |
| `category` | `assertion`, `rule/prose` or `primitive` (`star*` only); `type` in `star9f` for ✱9·131 and ✱9·6–✱9·63, which are Lean's typing and not stated |
| `method` | how the Lean proof is built (`explicit`: a term following PM's lines); in `star9f` also `primitive`, `not stated` (built into the syntax) and `open` (not proved; the note says what is) |
| `pm_text` | what PM prints to follow: `dem`, `hint` or `none`; or `analogue`, the value of the maintainer's ruling 63 (2026-10-14): PM omits the proposition's proof and refers to an analogous earlier number, and our proof follows that analogue's proof, which `note` names and whose citations, translated, are `cited_used` and `cited_unused`. Used for all of ✱23 (whose proofs are those of the analogous propositions of ✱22, p. 226) and all of ✱25 (whose proofs "proceed precisely as in ✱24", p. 241), for the 14 rows of ✱21 where PM prints "Proof as in ✱20·…", and for ✱14·112 (as in ✱14·111) and ✱20·702 (as in ✱20·701) |
| `cited_used`, `cited_unused` | PM's citations that the proof uses, and does not use |
| `extra_used` | propositions used that PM does not cite (not chain glue, not a step in `tacit`) |
| `tacit` | the steps PM leaves tacit throughout that the proof may use silently |
| `fidelity` | `pm-lines`, `pm-lines+extra` or `unchanged` ([docs/FIDELITY.md](../docs/FIDELITY.md)) |
| `reason`, `note` | why each extra is needed; other remarks |
| `glue`, `glue_kind` | propositions used only for structural moves PM leaves unstated, and their kinds (`chain`, `order`, `under-exists`); ✱11, ✱13, ✱14, ✱20, ✱21, ✱22, ✱23, ✱24, ✱25 only |
| `scan_check` | the result of checking the 1910 print (3 rows of `replay2_ledger.json`) |

Rows per file: `replay2` 85; `star11` 55 (51 assertions, 4 rules); `star12` 2 (the primitive propositions
✱12·1, ✱12·11); `star13` 25; `star14` 47; `star20` 53 (51 assertions, 2 rules); `star21` 46 (44
assertions, 2 rules); `star22` 72; `star23` 72; `star24` 70; `star25` 70; `star9f` 43 (32 assertions, 6 primitive propositions, 5 rows on types). (`tests/test_data_readme.py` checks these counts against the files.) The 32 assertions of `star9f` are
the 28 numbered ✱9 propositions and four of ✱10, all proved under the working reading C, the definitions
as printed with Russell's ✱8·13 carried over: 32 of 32 (also under Landini's ✱9+, L; under the
definitions as printed alone, ✱9·31 is not; the row says so, and
[docs/STAR9_READINGS.md](../docs/STAR9_READINGS.md) gives each reading). There is no ledger for ✱9–✱10 by
✱10's method, the one the rest of the repository builds on; `star9f` is ✱9 by its own method.

## Overlap, precedence and how to total

- **✱2–✱5.** `replay2_ledger.json`'s 85 rows are a subset of `replay_ledger.json`'s 188, not a further 85
  propositions. They are the proofs of `PM/Replay2.lean`, the rows whose `in_lean` is not true: 43
  `UNRESOLVED` in the first ledger, 36 `REPAIRED` and 6 `FAITHFUL` (found by the search but not put in
  `PM/Replay.lean`, for example because they use an unresolved proposition). **For these 85,
  `replay2_ledger.json` takes precedence.** For the other 103 (the proofs of `PM/Replay.lean`), use
  `replay_ledger.json`'s `tag`. So:
  - only PM's citations: 94 (`FAITHFUL`, in `PM/Replay.lean`) + 46 (`pm-lines`) = 140;
  - PM's lines plus extras: 9 (`REPAIRED`, in `PM/Replay.lean`) + 39 (`pm-lines+extra`) = 48;
  - no PM proof to follow: none (`unchanged`). 140 + 48 = 188.
- **✱11, ✱20, ✱21, ✱22, ✱24, ✱25.** Count rows with `category` = `assertion` for the assertion tables. The rule rows
  (✱11·07, ✱11·11, ✱11·13, ✱11·311; ✱20·62, ✱20·633; ✱21·62, ✱21·633) are proved too. PM prints ✱11's
  rules in words. ✱20's and ✱21's are numbered with ⊢, so [docs/PROGRESS.md](../docs/PROGRESS.md) counts
  them as assertions, but `data/fidelity_counts.py` leaves them out.
- **✱12.** Its two rows are primitive propositions, rules of the system: neither assertions nor proved
  theorems.
- **✱14.** One row per numbered proposition; the variant `q14_21_neg` has no row of its own.
- **`star9f`.** ✱9 by ✱9's own method (`PM.F9.f9_…`), a second foundation beside the one the other files
  use; its 4 rows for ✱10 are ✱10's propositions proved in ✱9. Its primitive rows (✱9·1–✱9·15) and its
  rows on types (✱9·131, ✱9·6–✱9·63, built into the syntax and not stated) are not assertions, and
  [docs/PROGRESS.md](../docs/PROGRESS.md) does not count it (it counts ✱9 by ✱10's method).
  `Checks/LedgerCheck.lean`, check 3, checks its rows against the proofs, in both directions; `data/fidelity_counts.py` does not
  read it.
- Each `star*` file covers one chapter, and the files do not overlap.

To recompute: `python3 data/fidelity_counts.py` (the three fidelity counts) and `python3 scripts/progress.py`
(stated, proved and followed, per volume, range and chapter).
