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
| PM/Found9/Base.lean | tools from ✱9's primitives alone: ✱9·2 and Id for every proposition, ✱9·21 as a rule, ✱9·25 for every p |
| PM/Found9/Star9.lean | ✱9·1–✱9·52 along PM's Dem. lines; ✱10·01, ✱10·1, ✱10·11, ✱10·12 as ✱9 theorems |
| PM/Found9/Simul.lean | p. 142 for one apparent variable per letter (the `search9` tactic) |
| PM/Found9/ToStar10.lean | every ✱9 theorem is a ✱10 theorem (`thm9_toQ`) |
| PM/Found9/FromStar10.lean | `Rep` (✱1·2–✱1·6 for every ✱9 proposition) and, given it, every ✱10 theorem is a ✱9 theorem (`qthm_toF9`) |
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
- **Order of the quantifiers moved to the front.** ✱9·03–✱9·08 fix it when one side is elementary or
  each side has one quantifier. ✱9·07 and ✱9·08 put the universal one first, "also when φ and ψ are
  not both elementary" **[DOC] p. 136**. For longer prefixes PM says only that the definitions "can be
  repeated for successive types" **[DOC] p. 136**. Read literally, the repetition is ambiguous. With
  p = (y) . ψy, ✱9·06 gives "(∃x) : (y) . ψy ∨ φx" and ✱9·07 gives "(y) : (∃x) . ψy ∨ φx". `PF.or`
  follows the note on ✱9·07·08: a leading (x) on either side comes out before a leading (∃x). Among
  quantifiers of the same kind the left side's comes first. PM's own proofs fix this: the last line of
  ✱9·3 reads "(x) : φx . ∨ . (y) . φy" as "(x) . φx . ∨ . (y) . φy" (✱9·03), and the last line of ✱9·31
  reads "(∃x) : (∃y) . φx ∨ φy" as "(∃x) . φx . ∨ . (∃y) . φy" (✱9·05·06) **[DOC] p. 140**. The orders
  differ only for quantifiers of the same kind, or for independent ones, and all give equivalent
  propositions when there is an individual. In ✱9 they are different propositions.
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

- ✱9·2–✱9·52 (31 propositions) are proved along PM's Dem. lines, with φ, ψ elementary as in ✱9. Each
  line that PM justifies by definitions ("[(4).(✱9·06)]") is stated in its printed form. Lean accepts it
  as the same proposition as the line before, because ✱9·01–✱9·08 are computed. **[MEAS]** Every one of
  these definitional steps checks under `PF.or`'s order.
- Ledger: 32 assertions (with ✱10·01, ✱10·1, ✱10·11, ✱10·12), 21 on PM's lines with nothing extra. **[MEAS]**
- Text notes:
  - ✱9·5, ✱9·51, ✱9·52 cite ✱1·6 for line (1), but the line is ✱2·38 (✱1·6 with the disjunctions in the
    other order). **[MEAS]** ✱2·38 holds for elementary propositions, so the step is sound.
  - ✱9·3, line (5), applies ✱9·21 to "φx . ∨ . (y) . φy", which contains an apparent variable, while
    ✱9·21 is proved for elementary functions. The Lean line uses ✱9·21 as a rule for every function
    (`allImp`, PM/Found9/Base.lean). **[MEAS]**
  - ✱9·33 ("Proof as above") cannot copy ✱9·32: the (∃x) analogue of its line (2) is not ✱9·25. The
    reconstruction uses ✱9·1 at a real variable, so the Lean statement takes one. **[MEAS]**
  - ✱10·12 "is a mere example of "q ⊃ q"" by the definitions in ✱9 **[DOC] p. 146**: true for elementary
    p (`f9_25` is Id). For a p beginning with (y), the definitions put (y) first, and the two sides
    are different propositions. **[MEAS]**
- ✱10's primitive propositions as ✱9 theorems:
  - ✱10·1 (`f10_1`) and ✱10·12 (`f10_12`) for every function φ and every p;
  - ✱10·11 is ✱9·13;
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
- **✱10 ⊆ ✱9, given `Rep`** (`qthm_toF9`). Here `Rep S V` is ✱1·2–✱1·6 for every ✱9 proposition: the
  conclusion PM draws on p. 142 ("the propositions of ✱1—✱5 hold when p, q, r are replaced by
  propositions containing any number of apparent variables"). Given it, every primitive of the ✱10
  system holds in ✱9: ✱1·1–✱1·6, ✱10·1, ✱10·11, ✱10·12 (the last three without `Rep`), and the same
  gated rules. So, by induction on the derivation, every ✱10 theorem does. **[MEAS]**
- **`Rep` is not proved.** PM's ✱9·3–✱9·52 give it for one quantified letter with elementary φ. §7
  shows how far simultaneous replacement goes. Beyond one apparent variable per letter, PM's "mere
  repetition" does not carry over: the definitions put the quantifiers of a compound proposition in
  orders that PM's proofs do not have, and moving them needs modus ponens through propositions of the
  same size. **[EST]** A proof would need a normal-form theorem for ✱9 derivations, in the style of
  Herbrand's work on quantification theory. That is a separate project.
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
- **[MEAS]** 67 are proved. The tactic `search9` uses only what ✱9·3–✱9·52 use:
  - ✱9·13 for each leading (x);
  - ✱9·1 for each leading (∃x), the real variable found by unification;
  - an instance of ✱1·2–✱1·6 for the elementary matrix;
  - plus ✱9·31 (✱9·11) for ✱1·2 with p existential, and a real variable for ✱1·3 with p existential.
- Not covered: ✱1·6 `q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r` with p = (x) . φx and q = (∃y) . ψy, any r. By
  ✱9·07, p ∨ q is (x) : (∃y) . φx ∨ ψy; as an antecedent it becomes (∃x) : (y). With r elementary, the
  whole is "(x′) : (∃y′) : (∃x) : (y)" over the matrix. The (∃y′), from ∼(q ⊃ r), needs the variable of
  the later (y). A proof by ✱9·13, ✱9·1 and ✱9·11 alone chooses every (∃) from variables already
  introduced, so no such proof exists, at any depth of ✱9·11. The order of (x) and (∃y) here is fixed
  by ✱9·07, so no reading of the same-kind orders removes the case.
- Whether ✱9's primitives prove these three by a longer route (modus ponens with ✱9·1 for a function
  that contains an apparent variable, which asserts propositions of the form
  (∃y) : (∃z) : (y′) . ∼θy ∨ θ′y′) is not settled. **[EST]** The obvious routes need the same step
  again: weakening the matrix under a prefix (∃) (∃) (∀).

## 8. Open questions

1. `Rep` (§6): prove it, refute it, or leave the agreement conditional. *As it stands:* the agreement
   is stated conditional on `Rep`; a normal-form proof of `Rep` is listed as a next item in
   [ROADMAP.md](ROADMAP.md).
2. The three ✱1·6 cases of §7: do ✱9's primitives prove them? If not, PM's claim on p. 142 fails for
   ✱9's method as formalized here, already for one apparent variable per letter. *As it stands:* an
   open finding ([PM_CLAIMS.md](PM_CLAIMS.md), A28, partly checked), not a failure of PM's claim, since
   no proof that they are underivable is given.
3. The order of quantifiers for longer prefixes (§3) is a reading. Another reading of "repeated for
   successive types" (e.g. one in which each stage adds one apparent variable) would give a different
   `PF.or` and possibly different answers to 1 and 2. *As it stands:* (x) before (∃x), and among
   quantifiers of the same kind the left side's first, the order PM's own last lines of ✱9·3 and ✱9·31
   use (§3). The three cases of 2 do not depend on it: the order there is fixed by ✱9·07.
4. ✱9's comprehension rule takes a ✱10 formula, because the styles of predicativity (`PM/Pred/`) are
   written for ✱10's formulas (§4). *As it stands:* kept; a style written for ✱9's propositions would
   let the rule take a ✱9 function directly.

## 9. Measurements

- Files: PM/Found9/*.lean (1158 lines with PM/Found9.lean), data/star9f_ledger.json; PM.lean imports
  PM/Found9.lean. No file of ✱10's foundation was changed for it. **[MEAS]**
- Each PM/Found9 file checks in under 3 s (PM/Found9/Simul.lean, the slowest, 2.3 s). **[MEAS]**
- `AllAxioms.lean`: 33 declarations use an axiom, against 25 before. The 8 new ones are Lean's
  generated `injEq` lemmas for the constructors of `EF` (5) and `PF` (3), as for every inductive type
  with data. No theorem of PM/Found9 uses an axiom. **[MEAS]**
- `AxiomCheck.lean` prints every public theorem of PM/Found9 (its generator globs every file under PM/);
  each reports "does not depend on any axioms". **[MEAS]**
- `Checks/LedgerCheck.lean`, check 3, checks data/star9f_ledger.json against the proofs: every ✱9
  proposition, ✱2–✱5 theorem (through `elift`) and primitive of `Thm9` a row's proof uses is listed in
  the row. 36 rows, 0 disagreements; the 7 rows of ✱9·14, ✱9·15, ✱9·131, ✱9·6–✱9·63 have no
  declaration. **[MEAS]**
- RedCheck and StyleCheck read the `q…` theorems of ✱10's method only; the `PM.F9.f…` theorems are not
  among their 485 PM propositions. **[MEAS]**
