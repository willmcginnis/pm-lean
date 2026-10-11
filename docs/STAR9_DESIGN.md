# ✱9–✱10 in Lean: design note

Tags: **[DOC]** is what PM's 1910 text says (page numbers are the printed pages; scan file =
`scan/djvu{page+22}.jpg`). **[MEAS]** was run or checked in this repo. **[EST]** is a judgement, not
measured.

## 1. How PM ✱9 works

- ✱9 opens Section B; its running head is "Extension of the theory of deduction". **[DOC] p. 135**
- In ✱9, p, q and φx stand for *elementary* propositions (no apparent variables). ✱1's primitive ideas
  and propositions are assumed only for these. **[DOC] p. 134**
- (x).φx and (∃x).φx are primitive ideas. Negation and disjunction of them are *defined*, by moving the
  quantifier to the front: **[DOC] p. 135**
  - ✱9·01 ∼{(x).φx} . = . (∃x).∼φx Df; ✱9·02 ∼{(∃x).φx} . = . (x).∼φx Df.
  - ✱9·011, ✱9·021 only drop the braces.
  - ✱9·03–✱9·06: (x).φx . ∨ . p, p . ∨ . (x).φx, and the same with ∃, are (x).φx ∨ p etc.
  - ✱9·07, ✱9·08: with one ∀ and one ∃, the ∀ is put first.
- So "the true scope of an apparent variable is always the whole of the asserted proposition". **[DOC] p. 136**
- Primitive propositions, "six in number": **[DOC] pp. 136–138**
  - ✱9·1 ⊢ : φx . ⊃ . (∃z) . φz.
  - ✱9·11 ⊢ : φx ∨ φy . ⊃ . (∃z) . φz. Needed because ✱1·2 is not yet available for (∃z).φz.
  - ✱9·12 "What is implied by a true premiss is true" (✱1·1 for the new propositions).
  - ✱9·13 a real variable may be turned into an apparent one (generalization; a rule, not an implication).
  - ✱9·14 if φx is significant and a has the type of x, φa is significant, and vice versa.
  - ✱9·15 if for some a there is a proposition φa, there is a function φx̂, and vice versa.
- The claim: ✱9·2–✱9·52 show that (x).φx and (∃x).φx may replace p, q, r in ✱1·2–✱1·6. "When this has
  been proved, the previous proofs of subsequent propositions in ✱2—✱5 become applicable." **[DOC] p. 138**
- PM warns that this is shown one apparent variable at a time. Mathematical induction may *not* be used
  to get it for any number of apparent variables at this stage. **[DOC] p. 135**

## 2. The alternative method (✱10)

- ✱10 assumes "what has been proved in ✱9, that the propositions of ✱1—✱5 can be applied to such
  propositions as (x).φx and (∃x).φx". **[DOC] p. 143**
- Alternatively, take ∼ and ∨ as primitive for propositions with apparent variables, and assume ✱1's
  primitive propositions for them. Then ✱10·01 (∃x).φx . = . ∼(x).∼φx Df. **[DOC] pp. 143–144**
- "✱10·1 is ✱9·2, ✱10·11 is ✱9·13, ✱10·12 is ✱9·25, ✱10·121 is ✱9·14, and ✱10·122 is ✱9·15. These five
  propositions must all be taken as primitive propositions in the alternative method; on the other hand,
  ✱9·1 and ✱9·11 are not required." **[DOC] p. 144**
- ✱9 itself says its interest is "purely philosophical". Technically one may "regard the primitive
  propositions of ✱1 as applying to propositions of any type, and proceed as in ✱10, where the purely
  technical development is resumed". **[DOC] pp. 134–135**
- ✱10 is the number "very much used throughout the rest of the work". **[DOC] p. 144**
- So, by PM's own remark, ✱10's method can replace ✱9 for the rest of the book.

## 3. Options

### (a) First-order, ✱9's own method

- Syntax: elementary formulas (predicate letters with argument lists, ∼, ∨) under a prefix of ∀/∃.
  ∼ and ∨ on quantified formulas are functions that compute ✱9·01–✱9·08, like the ✱1·01 macro.
- ✱9·1, ✱9·11 are axioms; ✱9·12 is modus ponens; ✱9·13 is a generalization rule; ✱9·14, ✱9·15 are
  built into the syntax (one type of individuals).
- Fidelity: highest. It is ✱9 as written.
- Soundness: by structural induction, as for ✱1. The definitions must be shown to agree with the usual
  semantics of the prenex form. **[EST]** moderate.
- Cost: high. ✱1·2–✱1·6 hold only for elementary formulas. Getting ✱2–✱5 for quantified formulas needs
  ✱9·3–✱9·52 and then a meta-theorem over prefixes of any length. PM forbids that induction at this
  stage (§1); a faithful version would prove it for each fixed prefix length. **[EST]** several days.
- ✱10 then needs: a proof that ✱10·12 is "a mere example of q ⊃ q" (PM p. 146), and the rest of ✱10
  over prenex formulas.

### (b) Second-order / HOL-style

- Propositional functions as Lean functions, with quantification over functions as well as individuals.
- Fidelity: it fits PM's later numbers (✱12, ✱20) better, but it skips ✱9's and ✱10's point, which is
  about one apparent individual variable. Types and the ramified hierarchy would still be missing. **[EST]**
- ✱9·1–✱9·15 become theorems of the host logic or are vacuous. Soundness is easy if the formulas are Lean
  propositions, but then there is no deep embedding and no counter-model test. **[EST]**
- Cost: low for ✱10, but it is a different project (shallow, not deep). **[EST]**

### (c) ✱10's alternative method (chosen)

- Syntax: formulas with ∼, ∨, (x) primitive at every order; ✱10·01–✱10·03 as macros.
- Primitives: ✱1·1–✱1·6 for all formulas, ✱10·1, ✱10·11, ✱10·12. ✱10·121, ✱10·122 built into the syntax.
- ✱9·1 and ✱9·11 become theorems (✱9·1 is ✱10·24). ✱9·2 is ✱10·1, ✱9·13 is ✱10·11, ✱9·25 is ✱10·12.
- Fidelity: this is PM's own alternative, and the one ✱10 is written for (PM gives "alternative method"
  proofs for ✱10·23, ✱10·24, ✱10·252–✱10·253, ✱10·27, ✱10·28, ✱10·34, ✱10·36).
- Soundness: standard Tarski semantics; see §4.
- Cost: low. ✱1–✱5 carry over by one translation lemma (§4). **[MEAS]** see §5.
- What ✱10 then needs: nothing more. For ✱11 (two variables), nested `.all` should be enough. **[EST]**

**Recommendation: (c).** It is PM's own alternative. PM says ✱9's interest is philosophical and that
the technical development resumes in ✱10. It reuses all 188 ✱2–✱5 proofs unchanged. (a) can be added
later as a separate file that proves ✱9's claim for prefixes of fixed length.

## 4. What was built (PM/Quant.lean, PM/QuantLift.lean, PM/Star10.lean)

- `QF V`: formulas over a type `V` of individual variables. `atom "R" [x, y]` is an elementary
  proposition; `atom "p" []` is a propositional letter. `.all φ` is (x).φx, where `φ : V → QF V` is the
  function φx̂ and `φ y` is its value at y.
- This binding style (PHOAS) has no substitution and no variable capture. So ✱10·1 is just
  `(x).φx ⊃ φy`, and ✱10·12's "p does not contain x" holds by construction. **[MEAS]** No substitution
  or freshness lemma was needed.
- ✱10·11 is the rule `(∀ y, QThm (φ y)) → QThm (.all φ)`: "if φy is true whatever possible argument y
  may be". Not the implication φy ⊃ (x).φx, which PM calls "in general false" (p. 137).
- Semantics: a domain, Boolean predicate letters, and ∀ given as a Boolean oracle with its specification.
  `qsound` proves every `QThm` true in every such structure. **[MEAS]** axiom-free.
- Counter-models: φy ⊃ (x).φx and (∃x).φx ⊃ (x).φx fail in a two-element structure; (x).φx ⊃ (∃x).φx
  fails in the empty structure. **[MEAS]**
- `liftThm`: replacing the propositional letters of any ✱1–✱5 theorem by ✱10 formulas gives a ✱10
  theorem. `data/gen_quant_lift.py` writes PM/QuantLift.lean, which restates all 188 ✱2–✱5 propositions
  for ✱10 formulas. **[MEAS]**
- PM/Star10.lean proves ✱9·1, ✱9·11, ✱9·12, ✱9·13, ✱9·2, ✱9·21, ✱9·22, ✱9·23, ✱9·24, ✱9·25 and every
  numbered ✱10 proposition from ✱10·1 to ✱10·57 except ✱10·121, ✱10·122, ✱10·221 (significance rules,
  built into the syntax): 50 ✱10 propositions and 10 ✱9 ones. Proofs follow PM's alternative-method
  lines; steps PM leaves tacit are named in each docstring. **[MEAS]**
- Existence of an individual: PM's proofs of ✱10·25, ✱10·251, ✱10·33, ✱10·34, ✱10·36, ✱10·37 use a real
  variable y. In Lean those statements take `y : V`. Without it they fail (empty structure). **[MEAS]**
  PM's proofs take a real variable for granted, so its logic assumes there is an individual. **[EST]**

## 5. Measurements

- Clean `lake build` of the whole project (13 jobs): 16.1 s and 17.6 s wall in two runs. Star10 and Quant: under 1 s each. **[MEAS]**
- `AxiomCheck.lean` (generated by `data/gen_axiomcheck.py`): 460 names, all "does not depend on any
  axioms". No sorry, no native_decide, no axiom declarations. **[MEAS]**
- Size: PM/Quant.lean 195 lines, PM/Star10.lean 501, PM/QuantLift.lean 578 (generated). **[MEAS]**

## 6. Text notes (no review items added)

- vol1.jsonl drops the opening "(" of ✱9·03, ✱9·05, ✱9·07, ✱9·08 and ✱10·01 (the print has it).
- vol1.jsonl's "statements" for ✱9·12–✱9·15, ✱9·131, ✱10·11, ✱10·121, ✱10·122, ✱10·13, ✱10·221 are
  prose in the print; Lean follows the scan.
- ✱10·311: vol1.jsonl has "(x)φx.χx"; the print has "(x) : φx . χx". Same meaning here.
- ✱10·542: the print omits the ✱ before the number.
- ✱10·27 (p. 150): the print cites "[✱10·1]" for the line that turns y into an apparent variable. That
  step is ✱10·11. The Lean proof uses ✱10·11. Possibly a PM slip; not checked against the 1925 edition.

## 7. Next

- ✱11 (two apparent variables): same `QF`; ✱11's definitions as macros, nested `.all`.
- ✱12–✱14 (predicative functions, identity, descriptions) need a decision on function variables; that
  is where option (b)'s ideas come in.
- Optional: option (a) as a separate file, proving ✱9·3–✱9·52 for one quantifier.
