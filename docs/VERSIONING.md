# Versioning of exports

How exported names, statements and proofs change over time, and how export releases are numbered.
The first export release, 1.0.0 (✱1–✱5 on Prove2Me), is public since 2026-10-13: its names are locked,
and it is tagged `export-v1.0.0` on the commit exported ([EXPORT_LOG.md](EXPORT_LOG.md)). The private
pilot of ✱1–✱5 has no version.

## Rules

1. **Names are permanent and never reused**, also across platform environments: once released, a name
   always denotes the same statement. At a release, `scripts/export_names.py --write-lock` adds each name
   released (`--chapters 1-5` for the names of ✱1–✱5 and the results about the system, as in 1.0.0)
   to [data/export_names.lock](../data/export_names.lock) with the Lean declaration it came from, the
   reading it was released under, and two digests (below): of its statement, and of the definitions the
   statement uses. A check fails if a locked name disappears, or if its statement, its definitions or its
   reading change; the message points to `_vN` and data/changes.tsv ([NAMING.md](NAMING.md)). A locked
   name is used whatever the generator would now produce, so a later change of the working reading of ✱9
   renames nothing released.
2. **A new statement gets a new name**, `name_vN` (`_v2`, `_v3`, …), and the old card is deprecated, with the
   reason and the replacement's name in its description. The old card stays importable and stays
   exported, under its name and bound to its original statement digest. `_vN` is the last part of a
   name, after the reading: `PM.star9_31_reading_landini_v2`.
3. **Reading meanings are frozen.** At a release each reading a released name uses (with `--chapters`;
   without it, every reading) has its word and meaning copied to
   [data/naming/readings.lock](../data/naming/readings.lock); readings can be added later, never changed
   or removed. 1.0.0 uses none: ✱1–✱5 have no readings, so its readings lock is empty.
4. **Proofs and descriptions change in place.** A better proof is a new submission for the same card, and
   the old submission is deprecated; a description is edited. Counterparts (data/naming/counterparts.json)
   are description, not name.
5. **Superseded declarations are kept forever** in the repository, under their own Lean names, in
   `PM/Deprecated/`: a superseded declaration of `PM/Star21.lean` goes to `PM/Deprecated/Star21.lean`
   (module `PM.Deprecated.Star21`, imported by `PM.lean`), as a
   `@[deprecated <new declaration> (since := "YYYY-MM-DD")]` declaration that still builds. Its
   replacement is the Lean declaration of the same name with `_v<N>` (`PM.q21_71_v2` replaces
   `PM.q21_71`), in the original module. The folder is created with the first superseded statement.
   `Checks/ExportStatements.lean` prints every declaration of `PM.Deprecated` and each declaration's
   `@[deprecated]` target. The generator gives a locked declaration its locked name wherever it now
   lives. It exports `<lean>_v<N>` as the name of the declaration it replaces with `_v<N>`, and marks the
   old entry `deprecated`, with `superseded_by` and `deprecated_since`, and the new one `supersedes`.
   The links come from the Lean names, so they stay when the replacement is itself locked: locking
   changes no entry (generate, `--write-lock`, generate again gives the same files, byte for byte). A
   replacement superseded in turn moves to `PM/Deprecated/` like any other, so a chain
   `PM.star21_71` → `PM.star21_71_v2` → `PM.star21_71_v3` has each deprecated card pointing to its direct
   replacement (`superseded_by`) and each replacement to the card it replaces (`supersedes`).
6. **Every change of name is dated** in [data/changes.tsv](../data/changes.tsv): `date`, `old`, `new`,
   `reason`, `statement_id` (the new statement's digest, below), one row per card. A row renames nothing:
   the names come from the declarations. The `versions` check requires that the three records agree: the
   row, the `@[deprecated]` attribute, and the two declarations (the old one released and deprecated,
   the new one `_v<N>` with the row's digest, N one more than the old). So a row without a superseded
   declaration fails, and so does a `_v<N>` without its row; a deleted old declaration fails the lock.
   Changes caused by one decision (a definition changed, below) are one generation: one date, one reason,
   one release.
7. **A Lean or Mathlib upgrade is examined by a person and re-locked in a MAJOR release.** The digests are
   of the statement as Lean elaborates it, so a new Lean or Mathlib, in this repository or on a platform,
   can change a statement's canonical text with no change of its meaning (an elaborator detail, a renamed
   internal constant). The lock check then fails for that name, and nothing changes silently: a person
   examines each such statement, and if its meaning is unchanged, re-locks it under the same name (the
   row's two digests replaced; its export name, Lean declaration and reading kept), in a MAJOR release
   whose entry in [EXPORT_LOG.md](EXPORT_LOG.md) lists the names re-locked and why. A statement whose
   meaning did change is superseded instead (rule 2).

## Release numbers

Export releases follow [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html):

| Part | Raised when |
|---|---|
| MAJOR | the export moves to another platform environment (another Lean or Mathlib version) |
| MINOR | cards are added, or statements are superseded (`_vN` plus a deprecation; SemVer: "MUST be incremented if any public API functionality is marked as deprecated") |
| PATCH | only proofs, descriptions or documentation change |

The **build metadata** carries the Merkle root of the released statements (below): `1.4.0+m.<root>`,
`<root>` the first 12 hexadecimal digits. SemVer ignores build metadata for precedence; here it identifies
the content: two releases with the same root export the same statements. 1.0.0 is
**`1.0.0+m.7d40537313d3`** (`python3 scripts/export_names.py --root`).

**Tags** (proposal): an annotated git tag `export-v<MAJOR>.<MINOR>.<PATCH>` on the commit exported, whose
message gives the full version with its root and the platform environment, e.g.
`export-v1.0.0` with message `1.0.0+m.7d40537313d3, Lean v4.33.1`. The root is left out of the tag's name
because `+` in a tag name is awkward in URLs, and because one version never has two roots. Repository tags
for other purposes stay separate. The tag of 1.0.0, `export-v1.0.0` on 2e43991, gives the full version and
the commit that corrected its descriptions before release, not the environment (Lean v4.33.1, recorded in
EXPORT_LOG.md).

### Digests

Built. `Checks/ExportStatements.lean` prints each exported statement's elaborated type in a canonical text
(PM/Statements.lean's statement definitions unfolded, binder names erased, binder kinds, judgments and
universe levels kept) and the definitions under `PM` it uses, directly or through other definitions, each
with its type and value (an inductive type: its constructors). `scripts/export_names.py` records in
data/export_names.json:

- `statement_digest`: the SHA-256 of the statement's canonical text. Renaming a bound variable keeps it;
  any change of formula, hypothesis, judgment or binder order changes it;
- `definitions_digest`: the SHA-256 of the sorted list of the definitions it uses, each by name and the
  SHA-256 of its canonical text. A changed definition changes it for every card that uses the definition.

The `statement_id` of [data/changes.tsv](../data/changes.tsv) is the new statement's `statement_digest`.
The digests are not yet the identity scheme planned below: a definition is named in them, not replaced by
its hash, so renaming a definition changes the digests of the cards that use it, as a changed definition
does. Both are digests of the statement as Lean elaborates it in this repository's environment; an
environment move can change the canonical text with no change of meaning, which then fails the lock
check, to be examined and re-locked by a person (rule 7, a MAJOR release). The canonical text is printed
by [Checks/Canon.lean](../Checks/Canon.lean), which the check of a platform export also uses on the
uploaded files ([scripts/prove2me/](../scripts/prove2me/README.md)): for 1.0.0 the digests computed from
the cards with the platform's Lean v4.33.1 equal those computed here with v4.34.1, for all 196 cards.

### The Merkle root

Built for 1.0.0. The root is the Merkle Tree Hash of [RFC 6962](https://www.rfc-editor.org/rfc/rfc6962#section-2.1)
(the hash tree of Certificate Transparency) over the rows of data/export_names.lock, one leaf per released
name, `<export name>\t<statement_digest>\t<definitions_digest>` in UTF-8, the leaves sorted by export
name: a leaf is hashed as SHA-256(0x00 ‖ leaf), two subtrees as SHA-256(0x01 ‖ left ‖ right), and a
tree of n > 1 leaves splits after the largest power of two less than n. `tests/test_export_names.py`
checks the implementation against the test vectors of Certificate Transparency's reference
implementation (github.com/google/certificate-transparency): the roots of the trees of 1 to 8 leaves in
its tests,
[python/ct/crypto/merkle_test.py](https://github.com/google/certificate-transparency/blob/ab756a77a5f4b49d609b73040fbe710f4e05e0fa/python/ct/crypto/merkle_test.py).
RFC 6962 itself publishes no test vectors. A deprecated name stays in the lock, so it stays a leaf. Proofs are not hashed: a PATCH release keeps the root.

Still planned: a hash of each definition and card computed without its own name and with the hashes of
the definitions it refers to in place of their names (as in Unison), so that a renamed definition changes
no card's hash. Until then the definitions digest names the definitions it covers, and a renamed
definition changes the root as a changed one does.

## Worked examples

**A proof rewritten.** ✱2·01's proof is shortened. The statement is the same, so `PM.star2_01_abs`
keeps its name and its digests; the new proof is submitted and the old submission deprecated. No row in
changes.tsv. Release 1.0.0 → 1.0.1; the root does not change.

**A statement corrected: ✱14·32.** Suppose release 1.0.0 had exported ✱14·32 as the repository once stated
it, with ⊃ after E!(ιx)(φx) where PM prints ≡ (corrected after an external review; CHANGELOG). Once the
Lean statement is corrected, its statement digest differs from the locked one and the check fails:
`PM.star14_32` cannot change, so:

- the old Lean declaration `PM.q14_32` moves unchanged to `PM/Deprecated/Star14.lean` with
  `@[deprecated PM.q14_32_v2 (since := "…")]`; it is still exported as `PM.star14_32`, with its locked
  digest, marked deprecated and superseded by `PM.star14_32_v2`;
- the corrected statement is `PM.q14_32_v2` in `PM/Star14.lean`, exported as a new card
  `PM.star14_32_v2` with its own digest;
- the old card is deprecated on the platform, its description saying "Superseded by PM.star14_32_v2: PM
  prints ≡, not ⊃";
- changes.tsv gets one row: date, `PM.star14_32`, `PM.star14_32_v2`, "statement corrected to PM's ≡", the
  new statement digest;
- release 1.0.0 → 1.1.0, with a new root.

`tests/test_versioning.py` does this end to end for ✱21·71 in a scratch copy of the repository, through
the whole life cycle, twice:

1. release: `--check --write-lock` locks every name;
2. supersede: `PM.q21_71` to `PM/Deprecated/Star21.lean` unchanged, `PM.q21_71_v2` in `PM/Star21.lean`,
   rebuild, the row of changes.tsv; both names are exported, the old one with its digest, the new one as
   `_v2`, and every check passes, the lock included (and fails without the row);
3. release `_v2`: `--check --write-lock`, then regenerate, lock again and check: every generated file and
   the lock are byte for byte the same, and `_v2` still `supersedes` `PM.star21_71`;
4. supersede `_v2` by `PM.q21_71_v3` and release it the same way: the chain of three stays linked, each
   deprecated card to its direct replacement;
5. without the old declarations the check fails.

`tests/test_export_names.py` checks the same fixed point without Lean, for the repository as it is (under
its current lock) and for a chain `_v2`, `_v3` locked in turn.

**A definition changed, rippling to 40 cards.** Suppose ✱20·01, the definition of a class in a context,
must change. The definition gets a new name (`…_v2`), and every card whose statement uses it, directly or
through other definitions, has a new definitions digest: say 40 cards. All 40 get `_v2` names and are
deprecated in one generation: one release (MINOR), one date and one reason on 40 rows of changes.tsv,
and the old definition and the 40 old declarations kept in `PM/Deprecated/` (the old declarations still
use the old definition, so their digests stay). The lock check lists the 40; nobody lists them by hand.

**A platform environment move.** The platform's default environment moves from Lean v4.33.1 to a later
version. The export is re-checked there and every card is uploaded again under the same name with the
same statement: a name is never reused for anything else, so the same name in the new environment is the
same card. Release 1.4.2 → 2.0.0; the root is unchanged if no canonical text changed. A statement whose
canonical text changed with no change of meaning is examined and re-locked (rule 7), which changes the
root, and the log says which. A statement that must change to elaborate in the new environment gets
`_vN` like any other.

## Precedents

Mathlib renames with `@[deprecated new (since := "…")] alias old := new` and deletes deprecations after a
grace period of months; a changed statement cannot be aliased. Metamath set.mm keeps an obsolete statement
as `xxxOLD` for one year and logs renames in a dated table (changes-set.txt: date, old, new, notes), which
changes.tsv follows. Isabelle's AFP asks that entries change "mostly monotone"ly and archives every
version. Go gives an incompatible version a new import path (`/v2`): a new name rather than a changed
meaning. A platform name cannot be renamed or reused, so this project keeps deprecations forever and
writes the version into the name only when the statement changes.
