# Fidelity: how closely the proofs follow PM

A proof can be correct without being PM's proof. This page says how each Lean proof is compared with the
proof PM prints, what the labels in the ledgers mean, and how the counts are made. The ledger files and their
fields are described in [data/README.md](../data/README.md); the counts below are re-made by
`python3 data/fidelity_counts.py`.

## The standard

From ✱2 on, proofs follow PM's *Dem.* lines or, where PM prints only a bracketed hint, the propositions of the
hint in PM's order: one Lean line per Dem. line, or one per hinted proposition. Steps that PM leaves tacit
throughout are done silently, and a file header lists them: `PM/Replay2.lean`'s for ✱2–✱5, and
`PM/Star11.lean`'s from ✱11 on (Syll, ✱3·2, ✱4·21, ✱4·22, the definitions, and ✱10·11 with
✱10·27/271/28/281, pp. 161–162). Every other proposition a proof needs is recorded per proposition, in a
ledger, with the reason. ✱9–✱10 name their tacit steps in each docstring.

## The labels

Each ledger row has a `fidelity` field:

- **`pm-lines`**: the proof uses only the propositions PM cites, and the steps PM leaves tacit throughout.
- **`pm-lines+extra`**: it follows PM's lines but also needs at least one proposition PM does not cite.
  `extra_used` lists them and `reason` says why.
- **`unchanged`**: there is no PM proof to follow (the transcription has no Dem. and no hint, or the item is a
  primitive proposition), so the earlier proof is kept.

The ✱2–✱5 ledger of `PM/Replay.lean` is older and uses tags instead: `FAITHFUL` (only the propositions PM
cites) and `REPAIRED` (at least one more, listed in `extra`). See [data/README.md](../data/README.md) for how
it combines with `replay2_ledger.json`.

## Glue

`glue` is a separate field of the ✱11, ✱13, ✱14, ✱20 and ✱21 ledgers. It leaves `fidelity` unchanged and
lists the propositions a proof uses only for structural moves PM leaves unstated, each with its kind
(`glue_kind`):

- **`chain`**: joining the lines of a displayed chain. These are the `Trans` instances of `PM/Chain.lean`:
  ✱4·22 for two ≡ lines; ✱3·43, ✱2·02, ✱2·83 or ✱2·05 under a hypothesis; ✱3·26 where a ≡ line is followed
  by a ⊃ line.
- **`order`**: putting factors, disjuncts, members, antecedents or apparent variables in the order the next
  cited proposition needs (✱4·3, ✱3·22, ✱4·31, ✱4·32, ✱2·04, ✱4·21, ✱11·2, ✱11·23, with ✱4·36 or ✱4·38
  inside such a permutation).
- **`under-exists`**: carrying a step under an apparent variable, (x) or (∃x): ✱10·11 with ✱10·21, ✱10·27,
  ✱10·271, ✱10·28 or ✱10·281, and ✱11·11·34·341. The steps ✱10·11 + ✱10·27/271/28/281 are tacit where a
  row's own proof takes them (pp. 161–162, below); taken inside a helper lemma, or with ✱10·21, which that
  passage does not cover, they are listed as `under-exists` glue.

**PM's warrant** for leaving the first kind unstated: "The use of ✱4·22 will often be tacit" (p. 123), as Syll
is in a chain of implications (✱2·31, pp. 109–110; Introduction p. 9). `PM/Chain.lean`'s header gives these
passages.

The `fidelity` field counts chain glue as tacit and the other glue as extra. So `extra_used` lists neither
chain glue nor a step in the row's `tacit` list; `data/fidelity_counts.py` reports any row that does.

**An equivalence read as an implication.** PM passes from p ≡ q to p ⊃ q (or q ⊃ p) without citing
anything: p ≡ q is (p ⊃ q) . (q ⊃ p) by definition (✱4·01), and Simp (✱3·26, ✱3·27) takes one factor. The
ledgers count this step as follows.
- Outside a displayed chain it is the tacit "definitions" step of every row's `tacit` list, so it is not
  listed. In Lean it is `qiffMp` or `qiffMpr`, or ✱3·26 or ✱3·27 written out on (p ⊃ q) . (q ⊃ p).
- Inside a displayed chain, where a ≡ line is joined to a ⊃ line (the `Trans` instances `transIffImp` and
  `transImpIff` of `PM/Chain.lean`), it is chain glue: ✱3·26 is listed in `glue` with kind `chain`, as for
  ✱14·145 and ✱20·14.
- Simp on any other product (dropping an asserted factor, taking one factor of a hypothesis) is an
  ordinary step, listed in `extra_used` unless PM cites it. If a proof uses ✱3·26 both ways, it is listed
  once, in `extra_used` (✱14·142).

`Checks/LedgerCheck.lean` applies these rules to every row: each proposition a proof uses is listed in its
row, and a row lists ✱3·26 or ✱3·27 as extra or glue only if its proof uses it in one of the listed ways.

## The three counts

Since counting glue one way or the other is a choice, `data/fidelity_counts.py` gives three counts of
`pm-lines` / `pm-lines+extra` for each chapter with a ledger. All three are shown here; that is the
maintainer's decision of 2026-10-12 ([TYPES_DESIGN.md](TYPES_DESIGN.md) §5, Q7).

| Chapter | strict (all glue extra) | as recorded (`fidelity`) | all glue tacit |
|---|---|---|---|
| ✱11 (51) | 34 / 17 | 34 / 17 | 39 / 12 |
| ✱13 (25) | 12 / 13 | 12 / 13 | 16 / 9 |
| ✱14 (47) | 8 / 39 | 9 / 38 | 13 / 34 |
| ✱20 (51) | 18 / 33 | 18 / 33 | 19 / 32 |
| ✱21 (44) | 12 / 32 | 12 / 32 | 14 / 30 |

- ✱11 is counted without its four numbered rules (✱11·07, ✱11·11, ✱11·13, ✱11·311). ✱20 and ✱21 are
  counted without their two rules each (✱20·62, ✱20·633, ✱21·62, ✱21·633, all `pm-lines`).
- The strict count differs from the recorded one only at ✱14·25, whose displayed chain under
  φx ≡ₓ x = b needs ✱3·43 and ✱2·02, which its Dem. does not cite. (✱20·11 and ✱21·11 also have such a
  chain, for a ✱4·86 step, but their ✱10·21 makes them `pm-lines+extra` in both readings.)
- In ✱20 and ✱21 the last column differs from the recorded one at ✱20·11, ✱21·11 and ✱21·21, whose only
  extras are steps carried under an apparent variable (✱10·21, or ✱10·11 with ✱10·27 or ✱10·271 inside a
  helper).

## By chapter

**✱2–✱5** (188 propositions; `replay_ledger.json`, `replay2_ledger.json`).
- 112 proofs use only the propositions PM cites: 72 in `PM/Replay.lean`, 40 in `PM/Replay2.lean`.
- 65 follow PM's proof but need at least one further proposition, each listed: 31 + 34.
- 11 are `unchanged`: the transcription has neither Dem. lines nor a hint for them.

`PM/Replay.lean` replays 103 propositions as explicit `Thm` terms built from PM's own cited propositions.
The other 85 were first proved with derived rules (`PM/Derived.lean`). 74 of these have since been rewritten
in `PM/Replay2.lean` to follow PM's own proof. Of the 40 that are `pm-lines`, 37 also use tacit steps, and 28
follow only a bracketed hint, because PM prints no Dem. lines for them. The 34 `pm-lines+extra` proofs need,
for example:
- Comp (✱3·43) to join two halves into a product or an equivalence;
- Id (✱2·08) for the trivial half `p ⊃ p` of such a join or of a replacement;
- ✱4·11 to remove a double negation inside a larger formula;
- ✱3·22, ✱3·26 or ✱3·27 to swap the halves of an equivalence or take an implication out of it;
- ✱2·31, ✱2·32 or Perm to move brackets or permute a sum, and ✱4·3 to commute a product;
- ✱2·54 to turn `∼p ⊃ q` into `p ∨ q`, and ✱3·47 to replace one factor of a product.

**✱9–✱10.** The proofs follow PM's lines, and each docstring names the steps PM leaves tacit. There is no
per-proposition ledger for ✱9–✱10 by ✱10's method, the method these counts and
[PROGRESS.md](PROGRESS.md) cover, so they count 0 in its "followed PM's lines" column. ✱9 by its own
method (`PM/Found9`) has a ledger, `data/star9f_ledger.json`, which these counts do not read
([STAR9_FOUNDATION.md](STAR9_FOUNDATION.md)).

**✱11** (51 assertions; `star11_ledger.json`). All 51 follow PM's Dem. lines or bracketed hint: 34
`pm-lines`, 17 `pm-lines+extra`. Typical reasons for an extra:
- ✱10·33 or ✱10·35 used with the factors in the other order (✱4·3);
- double negations PM drops silently;
- three hints that cite a proposition that does not give the step (✱11·341, ✱11·371, ✱11·6; see their
  docstrings).

**✱12** (`star12_ledger.json`). The two primitive propositions have no Dem. to follow (`unchanged`).

**✱13, ✱14, ✱20, ✱21** (`star13_ledger.json` … `star21_ledger.json`), as recorded: ✱13 12 / 13 of 25; ✱14
9 / 38 of 47; ✱20 20 / 33 of 53 and ✱21 14 / 32 of 46 (rules included). Typical extras:
- factors commuted (✱3·22, ✱4·3), or a lemma applied to one factor (✱3·45, ✱3·47), where PM's cited
  proposition has them in the other order;
- one factor of a product taken by Simp (✱3·26, ✱3·27), where the product is not an equivalence;
- ✱13·16 to turn y = x into x = y; ✱10·32 for the orientation of ≡ₓ in ✱20;
- ✱10·28 or ✱10·281 (with ✱10·11) to carry a step under (∃b) where PM does not cite them, and ✱10·11
  before an uncited ✱10·23.

**Where the print is unclear,** the docstring says so. For example, ✱14·144 and ✱14·145 cite ✱14·111 where
the unmarked form is ✱14·112, and ✱14·272 cites ✱10·414 for a ✱10·271 step. [ARCHITECTURE.md](ARCHITECTURE.md)
lists these per file.

## Reducibility

Of the 172 formalized ✱13, ✱14, ✱20 and ✱21 propositions (counting one variant of ✱14·21), 133 depend on
✱12·1 or ✱12·11.
- Fifteen cite ✱12·1 or ✱12·11 directly, as PM's proofs do: ✱13·101, ✱14·17, ✱14·171, ✱20·112, ✱20·12,
  ✱20·13, ✱20·151, ✱20·19, ✱20·3, ✱20·703, ✱21·112, ✱21·12, ✱21·13, ✱21·151, ✱21·3.
- ✱20·701 and ✱20·702 use it by their hint.
- The class analogues of ✱10·1 and ✱10·24 (✱20·25, ✱20·53, ✱20·54) and their analogues for relations
  (✱21·53, ✱21·54) also use ✱12·1 or ✱12·11.
- The others depend on it through these and ✱13·101.

Which theorem needs which rule is in [VERIFICATION.md](VERIFICATION.md).

## What the proofs found in the text

Following PM's lines line by line turned up these points. The errata themselves are kept in the
[text audit](https://github.com/willmcginnis/principia-mathematica-text-audit).

- **✱1·4.** Gutenberg #78050 has `p ∨ q . ⊃ . p ∨ p`; the 1910 print has `q ∨ p`. The transcribed form
  is not a theorem: it is false when p is false and q is true, and the system is sound
  (`PM/Star2.lean`, `star1_4_variant_not_a_theorem`). This rests on a checked countervaluation, not on a
  failed proof attempt. It is entry 1 of the text audit's Vol I list, confirmed by its human check.
- **✱4·42** (p. 124). The print cites `⊢ . ✱3·26 .` on line (2); the ebook omits it, so ✱3·26 is PM's
  citation here, not an extra (`replay2_ledger.json`). The text audit's human check confirmed this
  transcription error (2026-10-11); it is in its errata list for Vol I, §4.
- **Apparent slips in the 1910 print itself** (the ebook follows the print):
  - ✱4·32 (p. 123): line (1) cites ✱4·12 for a step that is in fact ✱2·03 taken both ways. Awaiting a
    human check.
  - ✱4·43 (p. 125): ✱2·65 (∼p/p) yields ∼(∼p), but the line prints p. PM drops the double negation
    without citing ✱2·14. Awaiting a human check.
  - ✱10·27 (p. 150): the print cites ✱10·1 for the step that turns y into an apparent variable, which is
    ✱10·11. This is possibly a citation slip. It has not been checked against the 1925 edition.

  No published erratum touches pp. 123–125. The 1925 second edition has not been checked.
