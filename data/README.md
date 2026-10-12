# Data

| File | What it is | Made by |
|---|---|---|
| `vol1.jsonl` | PM Vol I parsed from Project Gutenberg eBook #78050: one record per numbered item | `scripts/parse_vol1.py` |
| `vol1_items.json` | Vol I's 3,449 numbered items with range, chapter, page and category: the denominators | `scripts/vol1_items.py` |
| `vol2_labels.json` | the distinct ✱100–✱234 labels printed in bold in Project Gutenberg eBook #78255 (Vol II): an upper bound | `scripts/progress.py --vol2-html` |
| `replay_ledger.json` | ✱2–✱5, first ledger: all 188 propositions | by hand, with the proofs |
| `replay2_ledger.json` | ✱2–✱5, second ledger: the 85 proofs of `PM/Replay2.lean` | by hand, with the proofs |
| `star11_ledger.json`, `star12_ledger.json`, `star13_ledger.json`, `star14_ledger.json`, `star20_ledger.json`, `star21_ledger.json` | one row per numbered item formalized in that chapter | by hand, with the proofs |
| `star9f_ledger.json` | ✱9 by its own method (PM/Found9): one row per ✱9 number, and for ✱10·01, ✱10·1, ✱10·11, ✱10·12 proved in ✱9 ([docs/STAR9_FOUNDATION.md](../docs/STAR9_FOUNDATION.md)) | by hand, with the proofs |
| `fidelity_counts.py` | the three fidelity counts per chapter, and consistency checks on the ledgers | — |

The meaning of the labels is in [docs/FIDELITY.md](../docs/FIDELITY.md); how the progress tables use these
files is in [docs/PROGRESS.md](../docs/PROGRESS.md).

## Sources and provenance

`vol1.jsonl`, `vol1_items.json` and `vol2_labels.json` are derived from the HTML editions of Project
Gutenberg eBooks #78050 (*Principia Mathematica*, Vol. I, release date February 26, 2026) and #78255 (Vol. II,
March 20, 2026). These are transcriptions of the 1910 and 1912 printings, prepared by Distributed Proofreaders
volunteers. The derived files reproduce the ebook's statements and proof lines (its LaTeX), its page markers
and its labels. They do not reproduce the ebook's front or back matter.

The ebooks and the 1910–1913 books are in the public domain in the USA. If you are outside the USA, check the
laws of your country before using these files. The HTML files themselves are not in this repository; see
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

`vol1_items.json` corrects two of the parser's flags (✱1·11 and ✱3·03 are rules that PM marks Pp) and puts
each item in one category: `assertion`, `Df`, `Pp` or `rule/prose` (a rule stated in words, ✱1–✱14 only).
Counts: 3,230 assertions, 186 Df, 19 Pp, 14 rules in words. These counts are "from the Gutenberg text with a
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
| `tag` | result of the replay search: `FAITHFUL`, a proof from the propositions PM cites alone; `REPAIRED`, one that also needs those in `extra`; `UNRESOLVED`, none found |
| `in_lean` | whether that replay is a theorem of `PM/Replay.lean` (absent for `UNRESOLVED`) |
| `cited` | the propositions PM cites |
| `extra` | propositions used that PM does not cite |
| `uses_unresolved`, `repair_src` | bookkeeping of the search: cited propositions that were themselves unresolved, and where a repair came from |

Counts: 78 `FAITHFUL`, 67 `REPAIRED`, 43 `UNRESOLVED`. `in_lean` is true for 103 rows (72 `FAITHFUL`,
31 `REPAIRED`): the 103 theorems of `PM/Replay.lean`.

**`replay2_ledger.json` and `star*_ledger.json`** (the second schema):

| Field | Meaning |
|---|---|
| `id` | `*N.M` |
| `page` | page of the 1910 print (`star*` only) |
| `category` | `assertion`, `rule/prose` or `primitive` (`star*` only); `type` in `star9f` for ✱9·131 and ✱9·6–✱9·63, which are Lean's typing and not stated |
| `method` | how the Lean proof is built (`explicit`: a term following PM's lines); in `star9f` also `primitive`, `not stated` (built into the syntax) and `open` (not proved; the note says what is) |
| `pm_text` | what PM prints to follow: `dem`, `hint` or `none` |
| `cited_used`, `cited_unused` | PM's citations that the proof uses, and does not use |
| `extra_used` | propositions used that PM does not cite (not chain glue, not a step in `tacit`) |
| `tacit` | the steps PM leaves tacit throughout that the proof may use silently |
| `fidelity` | `pm-lines`, `pm-lines+extra` or `unchanged` ([docs/FIDELITY.md](../docs/FIDELITY.md)) |
| `reason`, `note` | why each extra is needed; other remarks |
| `glue`, `glue_kind` | propositions used only for structural moves PM leaves unstated, and their kinds (`chain`, `order`, `under-exists`); ✱11, ✱13, ✱14, ✱20, ✱21 only |
| `scan_check` | the result of checking the 1910 print (3 rows of `replay2_ledger.json`) |

Rows per file: `replay2` 85; `star11` 55 (51 assertions, 4 rules); `star12` 2 (the primitive propositions
✱12·1, ✱12·11); `star13` 25; `star14` 47; `star20` 53 (51 assertions, 2 rules); `star21` 46 (44
assertions, 2 rules); `star9f` 43 (32 assertions, 6 primitive propositions, 5 rows on types). (`tests/test_data_readme.py` checks these counts against the files.) There is no ledger for ✱9–✱10 by
✱10's method, the one the rest of the repository builds on; `star9f` is ✱9 by its own method.

## Overlap, precedence and how to total

- **✱2–✱5.** `replay2_ledger.json`'s 85 rows are a subset of `replay_ledger.json`'s 188, not a further 85
  propositions. They are the proofs of `PM/Replay2.lean`, the rows whose `in_lean` is not true: 43
  `UNRESOLVED` in the first ledger, 36 `REPAIRED` and 6 `FAITHFUL` (found by the search but not put in
  `PM/Replay.lean`, for example because they use an unresolved proposition). **For these 85,
  `replay2_ledger.json` takes precedence.** For the other 103 (the proofs of `PM/Replay.lean`), use
  `replay_ledger.json`'s `tag`. So:
  - only PM's citations: 72 (`FAITHFUL`, in `PM/Replay.lean`) + 40 (`pm-lines`) = 112;
  - PM's lines plus extras: 31 (`REPAIRED`, in `PM/Replay.lean`) + 34 (`pm-lines+extra`) = 65;
  - no PM proof to follow: 11 (`unchanged`). 112 + 65 + 11 = 188.
- **✱11, ✱20, ✱21.** Count rows with `category` = `assertion` for the assertion tables. The rule rows
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
  `Checks/LedgerCheck.lean`, check 3, checks its rows against the proofs; `data/fidelity_counts.py` does not
  read it.
- Each `star*` file covers one chapter, and the files do not overlap.

To recompute: `python3 data/fidelity_counts.py` (the three fidelity counts) and `python3 scripts/progress.py`
(stated, proved and followed, per volume, range and chapter).
