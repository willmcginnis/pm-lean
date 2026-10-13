# Export names

The names under which PM's propositions are exported to formalization platforms (one statement, one
"card"). Inside the repository, Lean keeps its own short names (`t2_01`, `q20_11`, `f9_31_russell`;
[CONTRIBUTING.md](../CONTRIBUTING.md)). An export name is permanent once released
([VERSIONING.md](VERSIONING.md)), so it is chosen by a rule and checked, not by hand.

## The rule

```
PM.star<N>_<M>_<descriptor>[_reading_<word>]
```

1. **PM's number.** ✱N·M is `star<N>_<M>`: ✱2·01 is `star2_01`, ✱9·521 is `star9_521`. PM's numbers
   have no trailing zeros after the point, so the map is one to one.
2. **PM's own name**, lowercased, when PM gives one, right after the number: ✱2·01 Abs is
   `star2_01_abs_…`. The names are those of PM's "Alphabetical list of propositions referred to by
   names" (Vol I, front matter; [data/naming/pm_names.json](../data/naming/pm_names.json)). PM gives one
   name to several numbers (Transp names seven, Syll four, Simp three), so a name never identifies a
   proposition on its own; the number does.
3. **A descriptor of PM's printed statement**, and of nothing else: not of our proof, our reading or our
   encoding. It is generated from the statement's shape in the style of Mathlib's names, then reviewed
   by people (below). Its words come from a closed vocabulary,
   [data/naming/vocabulary.json](../data/naming/vocabulary.json): Mathlib's symbol words (`imp`, `and`,
   `or`, `not`, `iff`, `all`, `exists`, `eq`, `ne`, `mem`), its axiomatic words (`self`, `left`, `right`,
   `comm`), PM's names, and three words for PM's notions Mathlib has no word for (`desc`, `cls`, `rel`).
4. **A reading**, for a statement of ✱9 by its own method, as the last part: `_reading_<word>`, the word
   from a closed list, [data/naming/readings.json](../data/naming/readings.json). All readings of one
   proposition share everything before the suffix.

ASCII snake_case throughout, all under `PM.`. Results about PM's system rather than in it (soundness,
completeness) are `PM.meta_<words>`, named by hand from the same vocabulary.

### Examples

| PM | Printed | Export name |
|---|---|---|
| ✱1·4 Perm | p ∨ q . ⊃ . q ∨ p | `PM.star1_4_perm_or_comm` |
| ✱2·01 Abs | p ⊃ ∼p . ⊃ . ∼p | `PM.star2_01_abs_not_of_imp_not` |
| ✱2·14 | ∼∼p . ⊃ . p | `PM.star2_14_of_not_not` |
| ✱3·26 Simp | p . q . ⊃ . p | `PM.star3_26_simp_left_of_and` |
| ✱3·27 Simp | p . q . ⊃ . q | `PM.star3_27_simp_right_of_and` |
| ✱4·2 | p ≡ p | `PM.star4_2_iff_self` |
| ✱13·15 | x = x | `PM.star13_15_eq_self` |
| ✱9·31, reading C | (∃x) . φx . ∨ . (∃x) . φx : ⊃ . (∃x) . φx | `PM.star9_31_exists_of_exists_or_self_reading_russell` |
| ✱9·31, reading L | the same | `PM.star9_31_exists_of_exists_or_self_reading_landini` |

The full list, with each name's Lean declaration, source file and descriptor, is
[data/export_names.json](../data/export_names.json).

### How the descriptor is generated

`scripts/export_names.py` reads each statement as Lean elaborates it (`Checks/ExportStatements.lean`
prints it as a tree) and reads it left to right:

- each connective gives its word and variables give none: ∼p ∨ p is `not_or`, ∼∼p is `not_not`;
- an asserted implication A ⊃ B is named conclusion first, `B_of_A`; a hypothesis H of the Lean statement
  adds `_of_H` (Mathlib: "the conclusion is stated first");
- an asserted equivalence A ≡ B is `A_iff_B`;
- X ∨ X is `or_self`; A ⊃ B or A ≡ B whose sides are one connective with its operands swapped is
  `or_comm`, `and_comm`; a variable on one side that is the left or right operand of the other side is
  `left` or `right` (`left_of_and`, `or_of_right`).

A descriptor longer than six words is replaced by its shape (the connectives of the top two levels), and
the entry is marked `needs_human`; so are the `meta` names and a statement with no connective. Every name
is reviewed before release: a spot review per chapter, and the maintainer's review before anything is
made public. A reviewed descriptor that differs from the generated one is not yet supported; until it is,
review changes the generator or the vocabulary.

Two names with the same descriptor are possible (✱2·05 and ✱2·06 are both
`syll_imp_imp_imp_of_imp`): the number keeps them apart, and the descriptor is a reading aid, not a key.

### Readings

| Tag | Word | What it is | Why this word |
|---|---|---|---|
| A | `printed` | ✱9's definitions as printed (1910) | says what it is: the text with no repair |
| C | `russell` | the definitions as printed with Russell's ✱8·13 (1925); the working reading | the authors' own repair, so the author's name, as with `landini` |
| L | `landini` | Landini's ✱9+ (2000), a published variant kept as a cross-check | names whose repair it is; the Lean name `withSwitch` names only the mechanism |
| B | `convention` | an alternative convention of this project's, a cross-check | the repository's own word (`Reading.convention`); says it is neither PM's text nor a published repair |
| P | `prenex` | the definitions as printed with this project's prenex Switch (R5) | names the mechanism; it is our construction, with no author to name |

A ✱9 statement proved for every reading is exported under the working reading C, `_reading_russell`.
✱9's and ✱10's propositions stated in ✱10's system (`PM/Star10.lean`) carry no reading.

## Checks

`python3 scripts/export_names.py --check` (a step of `tests/run_all.sh`; tested with seeded mutations in
`tests/test_export_names.py`):

- the pattern above, ASCII, with the number matching the proposition;
- every full name unique, and every platform slug unique (`.` → `_`: a platform module is named after the
  slug, so `PM.star2_01_…` and a top-level `PM_star2_01_…` would collide);
- only vocabulary words after the number;
- PM's name first, when PM gives one, and only then;
- readings only from the closed list, only as the last part;
- no top-level `PM_` names;
- frozen names: every name in [data/export_names.lock](../data/export_names.lock) is still there, unchanged.
  The lock is empty until the first public release fills it;
- data/export_names.json is what the generator produces from the current statements.

## Why

- **Number first.** Every PM formalization surveyed keys on PM's numbers: Metamath set.mm (`pm2.27`;
  "Proofs of theorems from Principia Mathematica often use a special naming convention: 'pm' followed by
  its identifier", us.metamath.org conventions-labels), Neo-Principia and principia-rewrite (`n2_01`,
  `Simp3_26`), l-pommeret's Lean development (`star_2_01`). A Lean name component cannot start with a
  digit, hence a word in front; `star` says which word.
- **PM's names next, descriptor after.** PM's names are fixed text, but cover few propositions; the
  descriptor makes every name readable. Mathlib names a theorem after its statement with a fixed
  dictionary of symbol words ([naming conventions](https://leanprover-community.github.io/contribute/naming.html));
  its descriptors are written by hand and are renamed often (the `not_mem` → `notMem` change touched 696
  files). A platform name cannot be renamed, so ours are generated from a closed vocabulary and reviewed
  once, before release.
- **Readings as words, last.** One prefix per proposition, and a word that says whose reading it is, not a
  letter that needs a key.
