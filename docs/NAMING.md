# Export names

The names under which PM's propositions are exported to formalization platforms (one statement, one
"card"). Inside the repository, Lean keeps its own short names (`t2_01`, `q20_11`, `f9_31_russell`;
[CONTRIBUTING.md](../CONTRIBUTING.md)). An export name is permanent once released
([VERSIONING.md](VERSIONING.md)), so it is chosen by a rule and checked, not by hand.

## The rule

```
PM.star<N>_<M>[_<pmname>][_df|_rule][_reading_<word>][_v<N>]
```

1. **PM's number.** ✱N·M is `star<N>_<M>`: ✱2·01 is `star2_01`, ✱9·521 is `star9_521`. The number is
   kept as PM prints it, as a string: ✱2·01 and ✱2·1 are `star2_01` and `star2_1`.
2. **PM's own name**, lowercased, when PM gives one: ✱2·01 Abs is `PM.star2_01_abs`. The names are those
   of PM's "Alphabetical list of propositions referred to by names" (Vol I, front matter;
   [data/naming/pm_names.json](../data/naming/pm_names.json)). PM gives one name to several numbers
   (Transp names seven, Syll four, Simp three), so a name never identifies a proposition on its own; the
   number does.
3. **Nothing else describes the statement**: no descriptor generated from it and no Mathlib word. A
   readable description belongs in the card's title and description (below).
4. **A slot for what is not an asserted proposition**: `_df` for a definition (PM's Df), `_rule` for an
   inference rule (✱1·1, ✱9·12, …), from [data/naming/slots.json](../data/naming/slots.json). Twelve
   export names use them now, for nine items: the rules ✱9·12, ✱9·13, ✱10·11, ✱10·13, ✱11·07, ✱11·11,
   ✱11·13 and ✱11·311, which the repository proves as theorems about its systems
   ([Rules proved as theorems](#rules-proved-as-theorems)), and the definition ✱10·01 stated under ✱9's
   reading. No other definition or rule is exported yet; when one is, the slot is in its name.
5. **A reading**, for a statement of ✱9 by its own method: `_reading_<word>`, the word from a closed list,
   [data/naming/readings.json](../data/naming/readings.json). All readings of one item share everything
   before the suffix.
6. **A version**, last: `_v<N>` (N ≥ 2) names the replacement of a superseded statement
   ([VERSIONING.md](VERSIONING.md)). Nothing ever follows it.

ASCII snake_case throughout, one component under `PM.`. Results about PM's system rather than in it
(soundness, completeness) are `PM.meta_<words>`, named by hand.

### Examples

| PM | Printed | Export name | Exact counterpart (metadata) |
|---|---|---|---|
| ✱1·4 Perm | p ∨ q . ⊃ . q ∨ p | `PM.star1_4_perm` | `Or.symm` |
| ✱2·01 Abs | p ⊃ ∼p . ⊃ . ∼p | `PM.star2_01_abs` | none found |
| ✱2·14 | ∼∼p . ⊃ . p | `PM.star2_14` | `of_not_not` (classical) |
| ✱2·16 Transp | p ⊃ q . ⊃ . ∼q ⊃ ∼p | `PM.star2_16_transp` | `mt` |
| ✱2·17 Transp | ∼q ⊃ ∼p . ⊃ . p ⊃ q | `PM.star2_17_transp` | `Function.mtr` (classical) |
| ✱3·26 Simp | p . q . ⊃ . p | `PM.star3_26_simp` | `And.left` |
| ✱9·12 | what is implied by a true premiss is true | `PM.star9_12_rule` | |
| ✱10·01, reading C | (∃x) . φx . = . ∼(x) . ∼φx Df | `PM.star10_01_df_reading_russell` | |
| ✱9·31, reading C | (∃x) . φx . ∨ . (∃x) . φx : ⊃ . (∃x) . φx | `PM.star9_31_reading_russell` | |
| ✱9·31, reading L | the same | `PM.star9_31_reading_landini` | |
| ✱9·31, reading L, superseded once | the same, corrected | `PM.star9_31_reading_landini_v2` | |

The full list, with each name's Lean declaration, source file, digests and descriptor, is
[data/export_names.json](../data/export_names.json): 807 names, the longest
`PM.star10_11_rule_reading_russell` (33 characters).

A definition of PM uploaded to a platform as a definition rather than as a card may need a name without
dots (Prove2Me's definition names are `[a-zA-Z_][a-zA-Z0-9_]*`); its slug (`PM_star1_01_df`) is that
name. None is uploaded yet. The Lean infrastructure an export also uploads as definitions is not a
definition of PM, and is named apart ([Definition bundles](#definition-bundles)).

### Rules proved as theorems

PM states some propositions as rules, in words: "if ⊢ φ and ⊢ ψ, then ⊢ φ . ψ" (✱10·13), not an asserted
formula. Their export names keep `_rule`, PM's own classification (data/naming/slots.json), although on a
platform each card is a Lean `theorem`, and in this repository each is proved as one:

| PM | Export name | Lean declaration | Proved |
|---|---|---|---|
| ✱9·12 | `PM.star9_12_rule` | `PM.q9_12`, [PM/Star10.lean:205](../PM/Star10.lean#L205) | the constructor `QThm.mp` (✱1·1, ✱9·12) |
| ✱9·12, reading C | `PM.star9_12_rule_reading_russell` | `PM.F9.f9_12`, [PM/Found9/Star9.lean:47](../PM/Found9/Star9.lean#L47) | the constructor `Thm9.mp` |
| ✱9·13 | `PM.star9_13_rule` | `PM.q9_13`, [PM/Star10.lean:209](../PM/Star10.lean#L209) | the constructor `QThm.gen` (✱10·11) |
| ✱9·13, reading C | `PM.star9_13_rule_reading_russell` | `PM.F9.f9_13`, [PM/Found9/Star9.lean:52](../PM/Found9/Star9.lean#L52) | the constructor `Thm9.gen` |
| ✱10·11 | `PM.star10_11_rule` | `PM.q10_11`, [PM/Star10.lean:44](../PM/Star10.lean#L44) | the constructor `QThm.gen` |
| ✱10·11, reading C | `PM.star10_11_rule_reading_russell` | `PM.F9.f10_11`, [PM/Found9/Star9.lean:481](../PM/Found9/Star9.lean#L481) | the constructor `Thm9.gen` |
| ✱10·13 | `PM.star10_13_rule` | `PM.q10_13`, [PM/Star10.lean:51](../PM/Star10.lean#L51) | derived, as PM does, from ✱2·11, ✱2·32 and ✱9·12 |
| ✱11·07 | `PM.star11_07_rule` | `PM.q11_07`, [PM/Star11.lean:106](../PM/Star11.lean#L106) | derived from ✱11·1 and ✱10·11 (PM takes it as primitive) |
| ✱11·11 | `PM.star11_11_rule` | `PM.q11_11`, [PM/Star11.lean:111](../PM/Star11.lean#L111) | derived: ✱10·11 twice, PM's Dem. |
| ✱11·13 | `PM.star11_13_rule` | `PM.q11_13`, [PM/Star11.lean:122](../PM/Star11.lean#L122) | derived from ✱10·13, as PM says |
| ✱11·311 | `PM.star11_311_rule` | `PM.q11_311`, [PM/Star11.lean:213](../PM/Star11.lean#L213) | derived from ✱10·13 (it repeats ✱11·13) |

Why a rule proved as a theorem is sound:

- **The theorem states the rule, not an asserted formula.** Its hypotheses are the rule's premisses as
  judgments of the system (`QThm S a`: a is an asserted proposition of the system S) and its conclusion is
  the judgment the rule licenses: ✱10·13 is `(ha : QThm S a) (hb : QThm S b) : QThm S (QF.and a b)`. It
  does not assert the implication `⊢ a ⊃ (b ⊃ a . b)` inside the system, which would be a different
  proposition, and no card claims it does.
- **Proving it is more than PM needs.** PM uses a rule as licence for particular steps, each on particular
  asserted propositions. The theorem proves every such step valid at once, for every formula, and, in ✱10's
  system, for every system `S` (no opt-in rule is assumed). Where it is derived (✱10·13, ✱11·07, ✱11·11,
  ✱11·13, ✱11·311), it adds nothing to the system: no constructor, axiom or inference.
- **Where PM takes the rule as primitive and so does the system** (✱9·12, ✱9·13, ✱10·11), the rule is a
  constructor, and the theorem is that constructor under PM's number: it states the rule and derives it from
  nothing weaker. ✱11·07, primitive in PM, is derived here.
- **The name keeps PM's classification visible**, so a reader of a card that is a Lean `theorem` sees from
  `_rule` that PM states it as a rule.

Not exported, so not named yet: ✱1·1 (the constructor `PM.Thm.mp`), ✱1·11, ✱1·7–✱1·72 (formation: the type
of formulas), ✱3·03, ✱9·14 and ✱9·15, and the rules of data/vol1_items.json that no declaration states
under its number. `tests/test_export_names.py` checks this table: it lists exactly the exported `_rule`
names, and each file and line declares the theorem named.

## Definition bundles

An export also uploads the Lean infrastructure its cards need: the formulas and the system of ✱1, the
statement formulas, the derivation layer and the like, one bundle per source module, each a platform
definition. These are not propositions of PM, so they have no PM number and are not export names. Their
names follow their own rule, in [data/naming/definition_bundles.json](../data/naming/definition_bundles.json):

```
PM_core_<word>[_<word>]…
```

lower-case ASCII words that say what the bundle holds, joined by `_`, with no dot (a Prove2Me definition
name is `[a-zA-Z_][a-zA-Z0-9_]*`). `core` keeps them apart from every export name (`PM.star…`, `PM.meta_…`,
whose slugs are `PM_star…` and `PM_meta_…`) and from any name in PM's own style. The export of ✱1–✱5 has four:

| Bundle | Source module | What it holds |
|---|---|---|
| `PM_core_star1_system` | PM/Basic.lean | formulas, the defined connectives, the theorems of ✱1, truth tables |
| `PM_core_statement_formulas` | PM/Statements.lean | the formula of each numbered proposition of ✱2–✱5 |
| `PM_core_hypothetical_derivations` | PM/Derived.lean | derivations under hypotheses (contexts) |
| `PM_core_valuation_literals` | PM/Complete.lean | the literals of a valuation, for completeness |

A bundle name is permanent once released, like an export name; a bundle whose content must change gets a
new name with `_v<N>`, as a card does.

## Outside the name

### Descriptor

Each entry of data/export_names.json keeps the descriptor the generator reads off the statement's shape
in the style of Mathlib's names (`not_of_imp_not` for ✱2·01), from a closed vocabulary,
[data/naming/vocabulary.json](../data/naming/vocabulary.json). It is a search key and a starting point for
a card's title, not part of the name; one longer than six words is cut to the statement's top two levels
and marked `descriptor_needs_human`. It is kept because it costs nothing, is already checked, and gives
every card some words for search, including the ones that have neither a PM name nor a counterpart.

### Counterparts

A Lean or Mathlib declaration that states the same law is recorded as metadata, for the card's title and
description, in [data/naming/counterparts.json](../data/naming/counterparts.json): for ✱1–✱5, 68 of the
193 numbered propositions have one. Each record gives the declaration, its signature, the PM variable each
of its propositional variables is instantiated with (`instantiation`, in the order of its binders), its
statement in PM's variables, the repository, the file and line at the pinned commit, whether its proof is
classical (uses `Classical.choice`), whether and where the two sides of an equivalence are the other way
round, whether a `Sort` parameter is specialized to `Prop`, and how it was checked. The pins are the
platform's environment: Lean
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (v4.33.1) and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, not this repository's toolchain. A later rename upstream
changes nothing here: the record says what the declaration was called at the pin.

**The criterion** (an exact propositional schema counterpart; the exported statements are about PM's
formulas in a deep embedding, so they are never literally a library statement about Lean propositions):

1. Translate PM's formula as displayed, connective for connective: ∼ is `Not`, ∨ `Or`, ⊃ `→`, . `And`,
   ≡ `Iff`. PM's defined connectives are kept, not expanded into ∼ and ∨.
2. Take the declaration's complete elaborated type, with every hypothesis, implicit ones included, in its
   own order.
3. Allow a one-to-one renaming of the propositional variables, and, for a declaration polymorphic in
   `Sort`, the specialization of those sort parameters to propositions.
4. Treat `Not A` and `A → False` as the same.
5. Allow the two sides of an equivalence to be the other way round, and record where. Never reverse an
   implication.
6. Require the two formula trees to be equal after that. No associativity, commutativity, distributivity,
   double negation, currying, reordering of hypotheses, identification of variables, or compound
   formulas substituted for variables.
7. Keep every extra assumption, `[Decidable p]` included; prefer the unconditional classical declaration
   where there is one.
8. Record what the counterpart's proof depends on separately from whether its statement matches.

So `imp_self` is not ✱2·08 (it states `(a → a) ↔ True`; `id` specialized to propositions is), `or_comm` is
not ✱1·4 (an equivalence for an implication; `Or.symm` is), `Function.comp` is ✱2·05 but not ✱2·06 (its
hypotheses come in the other order), and `And.imp` is not ✱3·47 (curried where PM has a conjunction).
That no counterpart is listed is the result of a search of Lean's core and of Mathlib's source, not a proof
that none exists.

**How each record is checked.** The declaration's own type is bound to the statement exported now, not
only the record's account of it:

- **The 54 Lean core counterparts are checked by Lean** (`checked: "lean"`).
  [Checks/Counterparts.lean](../Checks/Counterparts.lean), generated from the records and the exported
  statements, states PM's formula as a schema over propositional variables, translated by the criterion
  (sides of an equivalence swapped only where the record says so), and has the kernel check
  `example : <schema> := @<declaration> <variables>`. Its `#counterpart` command also checks that the
  declaration's type prints as the recorded signature; that the instantiated binders are propositional
  variables, `Sort u` only where the record says `specialized`; that no two get the same variable; and
  that the instantiated type is the schema exactly, with no unfolding (but `A → False` read as `¬A`). It
  runs in `tests/run_all.sh` with this repository's Lean, and was also run with the pinned Lean v4.33.1
  (`819816b`), with the same result; `tests/test_counterparts.py` reruns it with v4.33.1 when that
  toolchain is installed.
- **The 14 Mathlib counterparts are checked by Lean against the pinned Mathlib** (`checked:
  "lean-mathlib"`), and from their source. The repository's own Lake project does not depend on Mathlib;
  [Checks/MathlibCounterparts/](../Checks/MathlibCounterparts/MathlibCounterparts.lean) is a Lake project
  of its own, requiring Mathlib `0df444a` with its Lean v4.33.1, and the default `lake build` does not
  build it. Its one file is generated like Checks/Counterparts.lean and makes the same checks, with two
  differences. A Mathlib record's signature is the header in the source, not the printed type, so it is
  checked against the source (below), not against Lean's printing. And `#classical` checks the record's
  `classical` against the axioms the proof uses, so these records say `classical_from: "axioms"`. All 14
  typecheck. It runs before a release, in `scripts/release_check.sh`
  ([VERIFICATION.md](VERIFICATION.md#before-a-release)), since it needs Mathlib's build (`lake exe cache
  get`, a few GB). Without Mathlib, `scripts/export_names.py --check` still reads each
  recorded signature, the declaration's header as written at the pin, with a strict parser of the
  propositional fragment (Lean's precedences; anything that is not a type over `Prop` variables is
  rejected). For the variables it takes from its section, the record also gives the section's `variable`
  line. The check then instantiates the variables as recorded and compares the result with PM's formula
  under the criterion. `--verify-counterparts DIR`, run against checkouts of the pins (by
  `scripts/release_check.sh` with `COUNTERPART_SOURCES=DIR`), checks that the header at the recorded line
  is the recorded signature, and the `variable` line the recorded one, up to whitespace. `checked:
  "source"` remains for a Mathlib record that is not compiled; none is.

The same strict parser also reads the 54 Lean core signatures, so without Lean the Python check already
rejects a signature that is not a type, or a declaration that does not state PM's formula.

## Readings

| Tag | Word | What it is | Why this word |
|---|---|---|---|
| A | `printed` | ✱9's definitions as printed (1910) | says what it is: the text with no repair |
| C | `russell` | the definitions as printed with Russell's ✱8·13 (1925); the working reading | the authors' own repair, so the author's name, as with `landini` |
| L | `landini` | Landini's ✱9+ (2000), a published variant kept as a cross-check | names whose repair it is; the Lean name `withSwitch` names only the mechanism |
| B | `convention` | an alternative convention of this project's, a cross-check | the repository's own word (`Reading.convention`); says it is neither PM's text nor a published repair |
| P | `prenex` | the definitions as printed with this project's prenex Switch (R5) | names the mechanism; it is our construction, with no author to name |

A ✱9 statement proved for every reading is exported under the working reading C, `_reading_russell`.
✱9's and ✱10's propositions stated in ✱10's system (`PM/Star10.lean`) carry no reading.

Reading meanings are append-only. At a release each reading's word and meaning go into
[data/naming/readings.lock](../data/naming/readings.lock); after that a reading can be added but never
changed or removed, and a word is never reused. The lock of names records the reading each card was
released under, so a statement proved for every reading keeps its name if the working reading changes
later.

## Checks

`python3 scripts/export_names.py --check` (a step of `tests/run_all.sh`; each rule tested with seeded
mutations in `tests/test_export_names.py`):

- `pattern`: the rule above, in lower-case ASCII, with the number matching the proposition;
- `suffix_order`: each optional part at most once and in the order of the rule, so `_v<N>` is last;
- `pm_name_only`: PM's name when PM gives one, and no other word;
- `slots`: `_df` exactly for definitions and `_rule` exactly for inference rules;
- `readings`: readings only from the closed list, only as the suffix;
- `readings_frozen`: the locked readings unchanged;
- `unique_name` and `unique_slug`: every full name unique, and every platform slug (`.` → `_`) ASCII and
  unique, also ignoring case (a platform module is named after the slug, so `PM.star2_01_abs` and a
  top-level `PM_star2_01_abs` would collide);
- `no_top_level`: every name is `PM.` and one component; no top-level `PM_`;
- `vocabulary`: the descriptor only from vocabulary words;
- `lock`: every name in [data/export_names.lock](../data/export_names.lock) still exported, with the same
  statement, definitions and reading ([VERSIONING.md](VERSIONING.md)); empty until the first release;
- `versions`: a superseded card and its replacement are both exported and linked: the `_v<N>` name has
  its row in [data/changes.tsv](../data/changes.tsv), and the old name is released, `@[deprecated]` in
  favour of the new one, and has the same row ([VERSIONING.md](VERSIONING.md));
- `bundle_names`: each definition bundle `PM_core_<words>`, a valid platform definition name, one per source
  module that exists, and unique, also ignoring case, among bundles and against every card's slug;
- `counterparts`: each record pinned to its repository's commit, with a well-formed `file.lean:line`; a
  PM formula equal to the statement exported now; and a signature that, read strictly and instantiated as
  recorded, states that formula under the criterion. No network is needed: `--verify-counterparts DIR`
  checks the files, lines and source headers in local checkouts, by hand. The Lean core ones are also
  checked by Lean (`Checks/Counterparts.lean`, above), and the Mathlib ones against the pinned Mathlib
  before a release (`Checks/MathlibCounterparts/`, above);
- data/export_names.json, Checks/Counterparts.lean and Checks/MathlibCounterparts/MathlibCounterparts.lean
  are what the generator produces from the current statements and records.

## Why

- **Number first, then PM's name.** Every PM formalization surveyed keys on PM's numbers, and the ones
  that use PM's names put them beside the number: Neo-Principia (Rocq: `n2_01`, `Syll2_05`, `Simp3_26`)
  and principia-rewrite (Coq: `Taut1_2`, `Sum1_6`); Metamath set.mm names them `pm` and the number
  (`pm2.27`). A Lean name component cannot start with a digit, hence a word in front; `star` says which.
- **No description in the name.** A platform name cannot be renamed, and a description can go stale or be
  disputed: Mathlib renames its own often (the `not_mem` → `notMem` change touched 696 files), and set.mm
  later renamed many of its pm labels to descriptive words. Prove2Me gives every card a free-text title
  for readability, so that the theorem name need not carry it; the descriptor and the counterparts serve
  the title and description.
- **Readings as words, last but for the version.** One prefix per item, and a word that says whose reading
  it is, not a letter that needs a key.
