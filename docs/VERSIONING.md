# Versioning of exports

How exported names, statements and proofs change over time, and how export releases are numbered.
Nothing here has been released yet: the first public export will be 1.0.0. The private pilot of ✱1–✱5
([EXPORT_LOG.md](EXPORT_LOG.md)) has no version.

## Rules

1. **Names are permanent and never reused**, also across platform environments: once released, a name
   always denotes the same statement. At a release, `scripts/export_names.py --write-lock` adds each name
   to [data/export_names.lock](../data/export_names.lock) with the Lean declaration it came from, the
   reading it was released under, and two digests (below): of its statement, and of the definitions the
   statement uses. A check fails if a locked name disappears, or if its statement, its definitions or its
   reading change; the message points to `_vN` and data/changes.tsv ([NAMING.md](NAMING.md)). A locked
   name is used whatever the generator would now produce, so a later change of the working reading of ✱9
   renames nothing released.
2. **A new statement gets a new name**, `name_vN` (`_v2`, `_v3`, …), and the old card is deprecated, with the
   reason and the replacement's name in its description. The old card stays importable. `_vN` is the last
   part of a name, after the reading: `PM.star9_31_reading_landini_v2`.
3. **Reading meanings are frozen.** At a release each reading's word and meaning are copied to
   [data/naming/readings.lock](../data/naming/readings.lock); readings can be added later, never changed
   or removed.
4. **Proofs and descriptions change in place.** A better proof is a new submission for the same card, and
   the old submission is deprecated; a description is edited. Counterparts (data/naming/counterparts.json)
   are description, not name.
5. **Superseded declarations are kept forever** in the repository, in a `Deprecated/` folder, as
   `@[deprecated <new name> (since := "YYYY-MM-DD")]` declarations that still build. The folder is created
   with the first superseded statement; `Checks/ExportStatements.lean` will then print them too, so that
   the lock still finds the old names.
6. **Every change of name is dated** in [data/changes.tsv](../data/changes.tsv): `date`, `old`, `new`,
   `reason`, `statement_id` (the new statement's digest, below), one row per card. The generator follows
   these rows from a locked name to its replacement, and a check requires a row for every `_vN` name.
   Changes caused by one decision (a definition changed, below) are one generation: one date, one reason,
   one release.

## Release numbers

Export releases follow [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html):

| Part | Raised when |
|---|---|
| MAJOR | the export moves to another platform environment (another Lean or Mathlib version) |
| MINOR | cards are added, or statements are superseded (`_vN` plus a deprecation; SemVer: "MUST be incremented if any public API functionality is marked as deprecated") |
| PATCH | only proofs, descriptions or documentation change |

The **build metadata** carries the Merkle root of the exported statements: `1.4.0+m.<root>`, `<root>` the
first 12 hexadecimal digits. SemVer ignores build metadata for precedence; here it identifies the content:
two releases with the same root export the same statements.

**Tags** (proposal): an annotated git tag `export-v<MAJOR>.<MINOR>.<PATCH>` on the commit exported, whose
message gives the full version with its root and the platform environment, e.g.
`export-v1.0.0` with message `1.0.0+m.3f9c0a1b2d4e, Lean v4.33.1`. The root is left out of the tag's name
because `+` in a tag name is awkward in URLs, and because one version never has two roots. Repository tags
for other purposes stay separate.

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
check, to be examined and re-locked by a person (MAJOR release).

### The Merkle root (planned)

Not built yet. The plan:

- each definition and each card has a hash of its canonical statement, computed without its own name and
  with the hashes of the definitions it refers to in place of their names (as in Unison), so that a
  changed definition changes the hash of every card that uses it, and a renamed one changes none;
- the root is the root of a binary Merkle tree whose leaves are the pairs (export name, statement hash),
  sorted by export name. Proofs are not hashed: a PATCH release keeps the root.

## Worked examples

**A proof rewritten.** ✱2·01's proof is shortened. The statement is the same, so `PM.star2_01_abs`
keeps its name and its digests; the new proof is submitted and the old submission deprecated. No row in
changes.tsv. Release 1.0.0 → 1.0.1; the root does not change.

**A statement corrected: ✱14·32.** Suppose release 1.0.0 had exported ✱14·32 as the repository once stated
it, with ⊃ after E!(ιx)(φx) where PM prints ≡ (corrected after an external review; CHANGELOG). Once the
Lean statement is corrected, its statement digest differs from the locked one and the check fails:
`PM.star14_32` cannot change, so:

- a new card `PM.star14_32_v2` states ✱14·32 with ≡;
- the old card is deprecated, its description saying "Superseded by PM.star14_32_v2: PM prints ≡, not ⊃";
- the old Lean declaration moves to `Deprecated/` with `@[deprecated … (since := "…")]`;
- changes.tsv gets one row: date, `PM.star14_32`, `PM.star14_32_v2`, "statement corrected to PM's ≡", the
  new statement digest; the generator then names the corrected declaration `PM.star14_32_v2`;
- release 1.0.0 → 1.1.0, with a new root.

**A definition changed, rippling to 40 cards.** Suppose ✱20·01, the definition of a class in a context,
must change. The definition gets a new name (`…_v2`), and every card whose statement uses it, directly or
through other definitions, has a new definitions digest: say 40 cards. All 40 get `_v2` names and are
deprecated in one generation: one release (MINOR), one date and one reason on 40 rows of changes.tsv,
and the old definition and the 40 old declarations kept in `Deprecated/`. The lock check lists the 40;
nobody lists them by hand.

**A platform environment move.** The platform's default environment moves from Lean v4.33.1 to a later
version. The export is re-checked there and every card is uploaded again under the same name with the
same statement: a name is never reused for anything else, so the same name in the new environment is the
same card. Release 1.4.2 → 2.0.0; the root is unchanged if no statement had to change. A statement that
must change to elaborate in the new environment gets `_vN` like any other.

## Precedents

Mathlib renames with `@[deprecated new (since := "…")] alias old := new` and deletes deprecations after a
grace period of months; a changed statement cannot be aliased. Metamath set.mm keeps an obsolete statement
as `xxxOLD` for one year and logs renames in a dated table (changes-set.txt: date, old, new, notes), which
changes.tsv follows. Isabelle's AFP asks that entries change "mostly monotone"ly and archives every
version. Go gives an incompatible version a new import path (`/v2`): a new name rather than a changed
meaning. A platform name cannot be renamed or reused, so this project keeps deprecations forever and
writes the version into the name only when the statement changes.
