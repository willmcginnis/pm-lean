# ✱9 by its own method, and its agreement with ✱10

Tags as in docs/STAR9_DESIGN.md: **[DOC]** is what PM's 1910 text says (printed pages), **[MEAS]** was
run or checked in this repository, **[EST]** is a judgement.

## 1. The question

- The rest of the project uses ✱10's "alternative method" (PM/Quant.lean; docs/STAR9_DESIGN.md says why).
- PM says the two methods are interchangeable. "✱10·1 is ✱9·2, ✱10·11 is ✱9·13, ✱10·12 is ✱9·25,
  ✱10·121 is ✱9·14, and ✱10·122 is ✱9·15. These five propositions must all be taken as primitive
  propositions in the alternative method; on the other hand, ✱9·1 and ✱9·11 are not required." **[DOC] p. 144**
- And: "by merely repeating the proofs", ✱1·2–✱1·6 hold when the letters are replaced by propositions
  with apparent variables, and so all of ✱2–✱5 hold for them. **[DOC] pp. 133, 138, 142**
- The project checks such claims rather than adopting them. PM/Found9/ builds ✱9's method alongside the
  existing foundation (no existing file is changed) and checks the agreement.

## 2. Files

| File | Contents |
|---|---|
| PM/Found9/Syntax.lean | elementary formulas `EF`, ✱9 propositions `PF`, ✱9·01–✱9·08 (`PF.neg`, `PF.or`), translations `PF.toQ`, `QF.toF9` |
| PM/Found9/System.lean | `Thm9 S`: ✱1·2–✱1·6 for elementary propositions, ✱9·1, ✱9·11, ✱9·12, ✱9·13, and the opt-in rules |
| PM/Found9/Base.lean | tools from ✱9's primitives alone: ✱9·2 and Id for every proposition, ✱9·21 and ✱9·22 as rules for every function, ✱9·25 for an elementary p |
| PM/Found9/Star9.lean | ✱9·1–✱9·52 along PM's Dem. lines (of ✱9·31, lines (1)–(3) only: §5); ✱10·01, ✱10·1, ✱10·11, ✱10·12 as ✱9 theorems |
| PM/Found9/Simul.lean | p. 142 for one apparent variable per letter (the `search9` tactic) |
| PM/Found9/ToStar10.lean | every ✱9 theorem is a ✱10 theorem (`thm9_toQ`) |
| PM/Found9/FromStar10.lean | `Rep` (✱1·2–✱1·6 for every ✱9 proposition); given it and a variable of every type, ✱9·25 for every p (`Rep.distrib`) and every ✱10 theorem is a ✱9 theorem (`qthm_toF9`) |
| PM/Found9/Equiv.lean | `star9_iff_star10`; soundness, consistency, failure without individuals |
| data/star9f_ledger.json | one row per ✱9 number (and ✱10·01, ✱10·1, ✱10·11, ✱10·12 in ✱9), in the format of the other ledgers |

Names: `PM.F9.f9_21` is ✱9·21 by ✱9's method; `PM.q9_21` (PM/Star10.lean) is the same proposition by ✱10's.

## 3. Representation

- **Elementary formulas** (`EF V`): predicate letters on individual variables, function variables
  applied to arguments, ∼, ∨. Same atoms as ✱10's `QF V` (PM/Quant.lean), same family `V : Ty → Type` of
  variables. "In what follows the single letters p and q will represent *elementary* propositions, and so
  will "φx," "ψx," etc." **[DOC] p. 134**
- **✱9 propositions** (`PF V`): `el e`, `all φ` ((x) . φx), `ex φ` ((∃x) . φx), with `φ : V τ → PF V` a
  Lean function as in PM/Quant.lean. Both quantifiers are primitive. **[DOC] p. 135**
- **∼ and ∨ are computed**, not primitive: `PF.neg`, `PF.or` move every quantifier to the front, by
  ✱9·01–✱9·08. "The true scope of an apparent variable is always the whole of the asserted proposition."
  **[DOC] p. 136** ⊃, . and ≡ are ✱1·01, ✱3·01, ✱4·01 over them: "transferred unchanged" **[DOC] p. 136**.
- **The definitions of disjunction, as printed.** "To define disjunction when one or both of the
  propositions concerned is of the first order, we have to distinguish six cases, as follows:
  ✱9·03. (x) . φx . ∨ . p : = . (x) . φx ∨ p Df; ✱9·04. p . ∨ . (x) . φx : = . (x) . p ∨ φx Df;
  ✱9·05. (∃x) . φx . ∨ . p : = . (∃x) . φx ∨ p Df; ✱9·06. p . ∨ . (∃x) . φx : = . (∃x) . p ∨ φx Df;
  ✱9·07. (x) . φx . ∨ . (∃y) . ψy : = : (x) : (∃y) . φx ∨ ψy Df; ✱9·08. (∃y) . ψy . ∨ . (x) . φx : = :
  (x) : (∃y) . ψy ∨ φx Df. (The definitions ✱9·07·08 are to apply also when φ and ψ are not both
  elementary functions.)" **[DOC] pp. 135–136**. And: "The above definitions can be repeated for
  successive types, and thus reach propositions of any type." **[DOC] p. 136**
- **`PF.or` applies them as printed**, to the outermost quantifier of each side, and computes the
  disjunction left on the right-hand side (φx ∨ p, φx ∨ ψy, …) by the same definitions. When one side
  begins with (x) and the other with (∃y), ✱9·07 or ✱9·08 takes out both, the universal first, whatever
  φ and ψ contain. With φx = (z) . R(x, z) and ψy = S(y), "(x) . φx . ∨ . (∃y) . ψy" is
  (x) : (∃y) : (z) . R(x, z) ∨ S(y) **[MEAS]** (pinned in Checks/PinnedStatements.lean, with its ✱9·08
  analogue). Until this release `PF.or` took every leading universal quantifier of the left side out
  first, which gives (x) : (z) : (∃y) here; an external review found that this is not what ✱9·07 gives.
  That earlier reading is kept, as `PF.orL`, only to state the finding below; it is not ✱9's
  disjunction.
- **Where the text is silent.** No definition is printed for two quantifiers of the same kind,
  "(x) . φx . ∨ . (y) . ψy" or "(∃x) . φx . ∨ . (∃y) . ψy": ✱9·03 and ✱9·05 are printed for an elementary
  p (p. 134), and "repeated for successive types" does not say which side's quantifier comes first.
  `PF.or` takes the left one first, as PM's proofs do: the last line of ✱9·3 reads
  "(x) : φx . ∨ . (y) . φy" as "(x) . φx . ∨ . (y) . φy" (✱9·03), and the last line of ✱9·31 reads
  "(∃x) : (∃y) . φx ∨ φy" as "(∃x) . φx . ∨ . (∃y) . φy" (✱9·05·06) **[DOC] p. 140**. Every other case is
  fixed by the printed text.
- **Where the text disagrees with itself.** In the proof of ✱9·31, PM goes from line (3),
  "(x) : (∃y) . φx ∨ φy . ⊃ . (∃z) . φz", to line (4), "(∃x) : (∃y) . φx ∨ φy : ⊃ . (∃z) . φz", by
  "[(3).(✱9·03·02)]" **[DOC] p. 140**. That reads "(x) : (y) . ∼(φx ∨ φy) . ∨ . (∃z) . φz" by ✱9·03 with
  p = (∃z) . φz, which gives (x) : (y) : (∃z), line (3). But the left side begins with (x) and the right
  with (∃z), and ✱9·07 applies "also when φ and ψ are not both elementary": it gives
  (x) : (∃z) : (y). So PM's printed definitions and its printed proof give this expression two
  different prenex forms; it has the shape of the review's example, read the other way. **[MEAS]**
  `f9_31_step` proves the two propositions different (given a variable of every type), and
  `f9_31_step_orL` shows that under `PF.orL` they are the same. No single definition of ∨ satisfies
  both ✱9·07's note and ✱9·31's step. `PF.or` follows the definitions. Consequences: §5 (✱9·31), §7.
- The orders that different readings give are equivalent in every structure with at least one
  individual (the quantified variables are distinct and each occurs on one side only). In ✱9 they are
  different propositions, and ✱9's primitive propositions have no rule that moves a quantifier.
- **✱9·14, ✱9·15** (significance, types) are built into the syntax, as ✱10·121, ✱10·122 are in the ✱10
  system: every `φ : V τ → PF V` is a function and `φ a` (`a : V τ`) is a proposition. ✱9·131 and
  ✱9·6–✱9·63 are Lean's typing of `V τ` and are not stated. **[MEAS]**

## 4. The system `Thm9 S`

- ✱1·2–✱1·6 for elementary propositions only (`taut` … `sum`): that they hold for the others is what
  ✱9·3–✱9·52 are for **[DOC] p. 138**.
- ✱9·12 is `mp` for all propositions; ✱9·13 is `gen` (a rule, as ✱10·11 is).
- ✱9·1 and ✱9·11 are stated for every function φ, with or without apparent variables. PM uses ✱9·1 so:
  line (3) of ✱9·21's proof applies it to a function containing (∃y) **[DOC] p. 139**.
- Comprehension and ✱12·1, ✱12·11 are the same gated rules as in `QThm S`, so every `Sys` has a ✱9
  counterpart. ✱12·1 is stated as printed, `(∃f) : φx . ≡ₓ . f!x` **[DOC] p. 174**, with (∃f) primitive.
  The styles of predicativity (PM/Pred/) inspect ✱10 formulas. So ✱9's comprehension rule takes ψ as a
  ✱10 formula, asks the style about it, and asserts the ✱9 proposition that ψ stands for (`QF.toF9`).

## 5. ✱9's own development (PM/Found9/Star9.lean, data/star9f_ledger.json)

- ✱9·2–✱9·521 are 28 propositions. 27 are proved along PM's Dem. lines, with φ, ψ elementary as in ✱9.
  Each line that PM justifies by definitions ("[(4).(✱9·06)]") is stated in its printed form. Lean
  accepts it as the same proposition as the line before, because ✱9·01–✱9·08 are computed.
  **[MEAS]** Every one of these definitional steps checks under `PF.or`, except one: line (4) of ✱9·31.
- **✱9·31 is not proved.** Its lines (1)–(3) are (`f9_31_3`, the one use of ✱9·11); line (4) is not
  the same proposition as line (3) under the printed definitions (§3). As the definitions print it,
  ✱9·31 is (x) : (∃z) : (y) . ∼(φx ∨ φy) ∨ φz. A proof by ✱9·13 and ✱9·1 must choose z before y and needs
  both z = x and z = y, so it needs this (∃z) : (y) proposition twice; ✱9·11 combines two instances of a
  function at real variables only. **[EST]** We have not found a derivation from ✱9's primitive
  propositions, nor shown that there is none. Given `Rep` it is an instance of ✱1·2.
- Ledger: 32 assertions (with ✱10·01, ✱10·1, ✱10·11, ✱10·12), 31 proved, 20 of them on PM's lines with
  nothing extra; ✱9·31's row has method `open`. **[MEAS]**
- Text notes:
  - ✱9·5, ✱9·51, ✱9·52 cite ✱1·6 for line (1), but the line is ✱2·38 (✱1·6 with the disjunctions in the
    other order). **[MEAS]** ✱2·38 holds for elementary propositions, so the step is sound.
  - ✱9·3, line (5), applies ✱9·21 to "φx . ∨ . (y) . φy", which contains an apparent variable, while
    ✱9·21 is proved for elementary functions. The Lean line uses ✱9·21 as a rule for every function
    (`allImp`, PM/Found9/Base.lean). With ✱9·07·08 as printed, "(x) . φx . ⊃ . (x) . ψx" is
    (y) : (∃x) . ∼φx ∨ ψy, so ✱9·13 and ✱9·1 give the rule from φx ⊃ ψx directly; likewise ✱9·22
    (`exImp`). **[MEAS]**
  - ✱9·31, line (4): see §3 and above.
  - ✱9·33 ("Proof as above") cannot copy ✱9·32: the (∃x) analogue of its line (2) is not ✱9·25. The
    reconstruction uses ✱9·1 at a real variable, so the Lean statement takes one. **[MEAS]**
  - ✱10·12 "is a mere example of "q ⊃ q"" by the definitions in ✱9 **[DOC] p. 146**: true for elementary
    p (`f9_25` is Id). For a p with apparent variables the two sides are different propositions.
    **[MEAS]**
- ✱10's primitive propositions as ✱9 theorems:
  - ✱10·1 (`f10_1`) for every function φ;
  - ✱10·11 is ✱9·13;
  - ✱10·12 (`f10_12`) for an elementary p and every function φ. For every p it is `Rep.distrib`
    (PM/Found9/FromStar10.lean), from `Rep` and a variable of every type. ✱9·13 and ✱9·1 alone do not
    reach it the way they did under the earlier reading: with p = (u) . χu and φ elementary it is
    (x) : (u) . χu ∨ φx . ⊃ : (u) : (x) . χu ∨ φx, and ✱9·08 asks for the x of the antecedent before
    the consequent's x has been introduced. Whether ✱9's primitive propositions prove it for every p
    without `Rep` is not settled. **[MEAS]**
  - ✱10·01, "in either case we have ⊢ : (∃x) . φx . ≡ . ∼(x) . ∼φx" **[DOC] p. 145**, for elementary φ (`f10_01`).

  The general ✱10·1 rests on one lemma (`ai`): if Y is X with some leading universal quantifiers turned
  into real variables, then ⊢ X ⊃ Y. It is proved by induction on X from ✱9·13, ✱9·1 (for a φ with
  apparent variables) and Id for elementary propositions. **[MEAS]**

## 6. The agreement

**Theorem `PM.F9.star9_iff_star10`** (PM/Found9/Equiv.lean): for every system `S` and every ✱10
formula q, `QThm S q ↔ Thm9 S q.toF9`. It assumes that every type has a variable (`hV`) and `Rep S V`.
**[MEAS]** No axioms.

- **✱9 ⊆ ✱10, unconditional apart from `hV`** (`thm9_toQ`). Every ✱9 theorem, written with ✱10's
  primitive ideas, is a ✱10 theorem in the same `S`. ✱10 proves each of ✱9's prenex moves (✱10·2,
  ✱10·252, ✱10·253, ✱10·36), and its own ✱9·1 and ✱9·11 (PM/Star10.lean) are reused. **[MEAS]**
- **✱10 ⊆ ✱9, given `Rep` and `hV`** (`qthm_toF9`). Here `Rep S V` is ✱1·2–✱1·6 for every ✱9 proposition: the
  conclusion PM draws on p. 142 ("the propositions of ✱1—✱5 hold when p, q, r are replaced by
  propositions containing any number of apparent variables"). Given it and a variable of every type,
  every primitive of the ✱10 system holds in ✱9: ✱1·1–✱1·6; ✱10·1 and ✱10·11 (without `Rep`); ✱10·12
  (`Rep.distrib`, which uses `Rep` and the variable, §5); and the same gated rules. So, by induction on
  the derivation, every ✱10 theorem does. **[MEAS]**
- **`Rep` is not proved.** PM's ✱9·3–✱9·52 give it for one quantified letter with elementary φ, except
  ✱9·31 (§5). §7 shows how far simultaneous replacement goes. Beyond one apparent variable per letter, PM's "mere
  repetition" does not carry over: the definitions put the quantifiers of a compound proposition in
  orders that PM's proofs do not have, and moving them needs modus ponens through propositions of the
  same size. **[EST]** A proof would need a normal-form theorem for ✱9 derivations, in the style of
  Herbrand's work on quantification theory. That is a separate project.
- **`Rep` under the printed definitions.** `Rep` is stated with `PF.or`, so making `PF.or` follow
  ✱9·07·08 changed the proposition it states. It became harder to reach: **[MEAS]** the direct method
  of §7 proves 50 of the 70 one-variable combinations, against 67 under the earlier reading; ✱9·31 is
  not derived; ✱10·12 for a p with apparent variables now needs `Rep` (§5). **[EST]** It is no less
  plausible: its instances are valid in every structure with an individual, and the two readings
  differ only in the order of independent quantifiers.
- **Individuals.** `hV` cannot be dropped (`thm9_unsound_empty`). In a structure with no individuals,
  take ✱9·1 for φf = (w) . Pw, f a function of individuals (the empty table exists), w an individual.
  ✱9·01 and ✱9·05 put (∃w) at the front, and the proposition is false there; ✱10's method is sound in
  that structure. **[MEAS]** So ✱9's method, unlike ✱10's, presupposes an individual through its
  definitions, not only through proofs that take a real variable (docs/STAR9_DESIGN.md §4).
- **Soundness and consistency of ✱9** (`thm9_sound`, `consistent9`): every ✱9 theorem is true in every
  structure with an individual, and the letter p is not a ✱9 theorem. **[MEAS]** No axioms.

## 7. p. 142 for one apparent variable per letter (PM/Found9/Simul.lean)

- Each of p, q, r in ✱1·2–✱1·6 is an elementary proposition, (x) . φx or (∃x) . φx with φ elementary:
  70 combinations besides the elementary one.
- **[MEAS]** 50 are proved, given a variable of every type for ✱1·3 (`t1_3` takes `hV` and uses it
  when p is existential). The tactic `search9` uses only what ✱9·3–✱9·52 use:
  - ✱9·13 for each leading (x);
  - ✱9·1 for each leading (∃x), the real variable found by unification, or the given one where
    nothing else is at hand (as in ✱9·33);
  - an instance of ✱1·2–✱1·6 for the elementary matrix.
- Not covered (forms of p, q, r: `a` (x) . φx, `x` (∃x) . φx, `e` elementary):
  ✱1·2 `x`; ✱1·3 `aa`; ✱1·4 `aa`, `xx`; ✱1·5 `aaa`, `aae`, `aax`, `axa`, `xxa`, `xxe`, `xxx`;
  ✱1·6 `aaa`, `aea`, `axa`, `axe`, `axx`, `xea`, `xxa`, `xxe`, `xxx`. In each, the definitions put an
  existential quantifier before the universal one whose variable it needs. For ✱1·3 `aa`: "p ∨ q" is
  (x) : (y) . φx ∨ ψy, and "q . ⊃ . p ∨ q" is (x) : (∃y′) : (y) . ∼ψy′ ∨ φx ∨ ψy (✱9·08), so y′ is chosen
  before y. ✱1·2 `x` is ✱9·31 (§5).
- **[MEAS]** Under the earlier reading (`PF.orL`) the same search proves 66, and ✱9·31's Dem. the
  67th; the three left are ✱1·6 `axa`, `axe`, `axx`, which are still not covered. For these the order
  of (x) and (∃y) in p ∨ q is fixed by ✱9·07 under either reading. As an antecedent, p ∨ q becomes
  (∃x) : (y); with r elementary the whole is "(x′) : (∃y′) : (∃x) : (y)" over the matrix, and the
  (∃y′) from ∼(q ⊃ r) needs the variable of the later (y). A proof by ✱9·13, ✱9·1 and ✱9·11 alone
  chooses every (∃) from variables already introduced, so no such proof exists, at any depth of
  ✱9·11. The other 17 come from the order ✱9·07·08 give when a disjunct already contains a quantifier.
- Whether ✱9's primitives prove the 20 by a longer route (modus ponens with ✱9·1 for a function
  that contains an apparent variable) is not settled. **[EST]** The obvious routes need the same step
  again: weakening the matrix under a prefix (∃) (∃) (∀), or using an (∃) (∀) proposition twice.

## 8. Open questions

1. `Rep` (§6): prove it, refute it, or leave the agreement conditional. *As it stands:* the agreement
   is stated conditional on `Rep`; a normal-form proof of `Rep` is listed as a next item in
   [ROADMAP.md](ROADMAP.md).
2. ✱9·31 (§5) and the 20 cases of §7: do ✱9's primitives prove them under the printed definitions? If
   not, PM's claim on p. 142 fails for ✱9's method as printed, already for one apparent variable per
   letter. *As it stands:* an open finding ([PM_CLAIMS.md](PM_CLAIMS.md), A10, A28, partly checked),
   not a failure of PM's claim, since no proof that they are underivable is given.
3. PM's definitions and its proof of ✱9·31 disagree (§3). *As it stands:* `PF.or` follows the
   definitions as printed, and ✱9·31 is left open. Following ✱9·31 instead (`PF.orL`) contradicts
   ✱9·07's note. A rule that exchanges independent quantifiers, if added to ✱9, would make the two
   readings interderivable (§10).
4. Two quantifiers of the same kind (§3) are ordered by a reading, the one PM's proofs of ✱9·3 and ✱9·31
   use. Another reading would give a different `PF.or` and possibly different answers to 1 and 2.
   *As it stands:* the left side's first. ✱1·6 `axa`, `axe`, `axx` do not depend on it.
5. ✱9's comprehension rule takes a ✱10 formula, because the styles of predicativity (`PM/Pred/`) are
   written for ✱10's formulas (§4). *As it stands:* kept; a style written for ✱9's propositions would
   let the rule take a ✱9 function directly.

## 9. Measurements

- Files: PM/Found9/*.lean (1271 lines with PM/Found9.lean), data/star9f_ledger.json; PM.lean imports
  PM/Found9.lean. No file of ✱10's foundation was changed for it. **[MEAS]**
- Each PM/Found9 file checks in under 3 s (PM/Found9/Simul.lean, the slowest, 2.4 s). **[MEAS]**
- `AllAxioms.lean`: 33 declarations use an axiom, against 25 before. The 8 new ones are Lean's
  generated `injEq` lemmas for the constructors of `EF` (5) and `PF` (3), as for every inductive type
  with data. No theorem of PM/Found9 uses an axiom. **[MEAS]**
- `AxiomCheck.lean` prints every public theorem of PM/Found9 (its generator globs every file under PM/);
  each reports "does not depend on any axioms". **[MEAS]**
- `Checks/LedgerCheck.lean`, check 3, checks data/star9f_ledger.json against the proofs: every ✱9
  proposition, ✱2–✱5 theorem (through `elift`) and primitive of `Thm9` a row's proof uses is listed in
  the row. 35 rows, 0 disagreements; the 7 rows of ✱9·14, ✱9·15, ✱9·131, ✱9·6–✱9·63 have no
  declaration, and ✱9·31's row (method `open`) must have none. **[MEAS]**
- RedCheck and StyleCheck read the `q…` theorems of ✱10's method only; the `PM.F9.f…` theorems are not
  among their 485 PM propositions. **[MEAS]**

## 10. Landini (2000)

- G. Landini, "Quantification Theory in ✱9 of *Principia Mathematica*", *History and Philosophy of
  Logic* 21 (2000), pp. 57–77, is reported to find a flaw in ✱9 as printed that needs a minor repair.
  We could not consult the paper for this release, and we do not recall its argument well enough to
  say what that flaw is. So nothing here claims to be, or to answer, Landini's point.
- An external review of this repository reports that Landini's later presentation of ✱9's system adds
  definitions for two quantifiers of the same kind and a rule ("Switch") for exchanging quantifiers.
  *Not checked here.*
- What this formalization shows **[DOC]**, **[MEAS]**: (a) the definitions are silent on two
  quantifiers of the same kind (§3); (b) the definitions, with the note that ✱9·07·08 apply to
  functions that are not elementary, and the proof of ✱9·31 give
  "(x) : (y) . ∼(φx ∨ φy) . ∨ . (∃z) . φz" two different prenex forms (§3, `f9_31_step`); (c) under the
  definitions as printed, ✱9·31 is not derived here, and the direct method proves 50 of the 70 cases
  of §7.
- **[EST]** A rule exchanging independent quantifiers would make the choice in (a) immaterial and
  repair (b): ✱9·31 would follow from PM's line (3). That fits the review's description of Landini's
  later system. Whether it is the flaw and repair of the 2000 paper, and whether the paper also
  concerns (c), cannot be settled without the paper. So this formalization neither meets nor
  sidesteps a flaw that it can identify as Landini's. It shows one place where PM's printed
  definitions and its printed proof disagree, and records how much of p. 142 survives the definitions
  as printed.
