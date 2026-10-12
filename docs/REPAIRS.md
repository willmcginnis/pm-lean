# Repairs: where the working formalization reads PM other than as printed

A register in the manner of a transcriber's notes. What PM printed stays in the repository and is
clearly marked. Where the working product needs a different reading to work, the repair is explicit,
recorded here, and reversible. Each entry gives:
- what PM printed, with its page;
- what we read it as;
- why;
- what depends on it;
- the evidence: **[MEAS]** measured in this repository, **[DOC]** documented in the literature (with
  what we have and have not read), **[EST]** a judgement.

Smaller points, such as transcription errors and apparent slips in the 1910 print that the proofs
turned up, are listed in [FIDELITY.md](FIDELITY.md) ("What the proofs found in the text") and in the
ledgers' tags. They are not repairs of the system, so they are not repeated here.

| # | Repair | Where | Default |
|---|---|---|---|
| R1 | Russell's ✱8·13 carried over to ✱9: the working repair of ✱9 (reading C) | `Thm9.exch`, `ExchStep`, `Sep` (PM/Found9/System.lean, Syntax.lean) | on, in C |
| R2 | Two quantifiers of the same kind: the left side's first (✱8's order of elimination; Introduction, 1910 p. 49; second edition p. 47) | `PF.orPrinted` (A, C), `PF.or` (B) | in A, C and B |
| R3 | Landini's ✱9+ (Switch, ✱9·yy, ✱9·zz): a published variant, cross-check (reading L) | `Thm9.switch`, `SwitchStep`, `PF.orPlus`, `Reading.withSwitch` | off (L only) |
| R4 | An alternative convention for ✱9's disjunction (reading B): cross-check, not the working repair | `PF.or`, `Reading.convention` | off (B only) |
| R5 | The prenex Switch: our earlier repair, kept for comparison | `Thm9.prenexSwitch`, `Reading.prenexSwitch` | off (opt-in) |

The results under each reading are generated in [STAR9_READINGS.md](STAR9_READINGS.md), columns in this
order:
- A, as printed: the definitions as printed (with R2 for two quantifiers of the same kind, which ✱9's
  text does not define);
- C, as printed + ✱8·13 (working, default): the same definitions, with R1;
- L, Landini's ✱9+ (published variant, cross-check): R3;
- B, alternative convention (cross-check): R4 (with R2).

Quotations from the second edition (1925) are from Vol. I of a 1963 impression (Internet Archive item
principia-mathematica_l2o7Ic0GMLeSLqcPnq, described as a photographic reprint of the 1925 text; that
it is one is documented there, not checked by us against a 1925 printing). Each is marked as read from
the **page image** or from the archive's OCR **text layer**.

## The flaw these repair

**What PM printed** (pp. 135–136), the definitions of disjunction for propositions with apparent
variables:

> ✱9·03. (x) . φx . ∨ . p : = . (x) . φx ∨ p Df
> ✱9·04. p . ∨ . (x) . φx : = . (x) . p ∨ φx Df
> ✱9·05. (∃x) . φx . ∨ . p : = . (∃x) . φx ∨ p Df
> ✱9·06. p . ∨ . (∃x) . φx : = . (∃x) . p ∨ φx Df
> ✱9·07. (x) . φx . ∨ . (∃y) . ψy : = : (x) : (∃y) . φx ∨ ψy Df
> ✱9·08. (∃y) . ψy . ∨ . (x) . φx : = : (x) : (∃y) . ψy ∨ φx Df
> (The definitions ✱9·07·08 are to apply also when φ and ψ are not both elementary functions.)

Here p is elementary (p. 134). Then: "The above definitions can be repeated for successive types, and
thus reach propositions of any type" (p. 136). In the proof of ✱9·31 (p. 140), PM passes from line (3),
"(x) : (∃y) . φx ∨ φy . ⊃ . (∃z) . φz", to line (4), "(∃x) : (∃y) . φx ∨ φy : ⊃ . (∃z) . φz", by
"[(3).(✱9·03·02)]": by definitions alone.

**The conflict.** Expanded, line (4) is "(x) : (y) . ∼(φx ∨ φy) . ∨ . (∃z) . φz". PM's step reads it by
✱9·03 with p = (∃z) . φz, which gives (x) : (y) : (∃z), line (3). But its left side begins with (x)
and its right side with (∃z), and the note says ✱9·07 applies "also when φ and ψ are not both
elementary". ✱9·07 gives (x) : (∃z) : (y). Under the definitions as printed, the two lines are
different propositions (**[MEAS]** `f9_31_step`, PM/Found9/Star9.lean, given a variable of every type).

**Whose finding.** Landini published it: "Unique among all the demonstrations of ✱9, this one
misapplies the definition ✱9.03" (G. Landini, "Quantification Theory in ✱9 of *Principia
Mathematica*", *History and Philosophy of Logic* 21(1) (2000), 57–77, §4, pp. 63–64,
doi:10.1080/01445340050044646) **[DOC]**, read in full. This repository's contribution is a
machine-checked confirmation: of the 48 steps of ✱9's proofs that PM justifies by definitions, 47 are
definitional rewrites under the definitions as printed, and the one that is not is this step of ✱9·31
**[MEAS]**. [STAR9_FOUNDATION.md](STAR9_FOUNDATION.md) §5 relates Landini's line numbers to PM's: this
step is his 4→5.

## R1. Russell's ✱8·13 carried over to ✱9 (the working repair, reading C)

**What PM printed.** ✱9 (1910) has no rule that changes the order of quantifiers. Its primitive
propositions are ✱9·1, ✱9·11, ✱9·12, ✱9·13 (and ✱9·14, ✱9·15 on types), pp. 136–138. The second
edition (1925) replaces ✱9 by a new ✱8 in Appendix A ("This chapter is to replace ✱9 of the text",
footnote, p. 635, page image; "The new chapter ✱8 (given in Appendix A) should replace ✱9 in Principia
Mathematica", Introduction to the Second Edition, p. xxv, text layer), and ✱8 has the rule, verbatim
(Vol. I, Appendix A, p. 636, page image) **[DOC]**:

> ✱8·13. If all occurrences of x are separated from all occurrences of y by a certain stroke, we can
> change the order of x and y in the prefix, i.e. we can replace "(y) : (∃x) . φx | ψy" by
> "(∃x) : (y) . φx | ψy" and vice versa. Pp

On the same page, before the primitive propositions (page image): "Thus in order to be able to change
the order of "(∃x)" and "(y)," it is sufficient (though not always necessary) that the matrix should
contain some part of the form φx | ψy, and that x and y should not occur in any other part of the
matrix. (This part may of course be the whole matrix.) We assume the legitimacy of this interchange by
a primitive proposition, and in practice arrange to have all the ∃-prefixes as far to the right as
possible, because this facilitates proofs." The Introduction to the Second Edition (p. xxv, text
layer): "The order of the variables in the prefix is indifferent whenever the occurrences of one
variable are all on one side of a certain stroke, while those of the other are all on the other side
of it", and (p. xxvi, text layer) "It is not necessary for the above primitive proposition that the
stroke separating x and y should be the principal stroke". ✱8's method (p. 637, text layer): "We
first apply the definitions until the whole asserted proposition is brought into the form of a matrix
with a prefix. If necessary, we apply ✱8·13 to change the order of the variables in the prefix."

**What we read it as** (reading C, `Reading.russell`, the default): ✱9·01–✱9·08 as printed, R2 for two
quantifiers of the same kind, and ✱8·13 carried over to ✱9 as a primitive rule (`Thm9.exch`, admitted
when `R.rule = .exch`). The carry-over is our transposition, not the authors' text **[EST]**:
- **The stroke** becomes the connective of ✱9's matrix: ✱9's matrix is an elementary proposition built
  with ∼ and ∨ (p. 134), where ✱8's is built with the stroke. "All occurrences of x are separated from
  all occurrences of y by a certain stroke" becomes: the matrix is a ∨ with every occurrence of x on one
  side and every occurrence of y on the other (`Sep`).
- **"The prefix"** is the prefix of the prenex form that ✱9's definitions give: the quantifiers in front
  of a `PF`, since ✱9·01–✱9·08 put every apparent variable there (p. 136: "the true scope of an apparent
  variable is always the whole of the asserted proposition").
- **"Change the order of x and y"**: x and y are adjacent in the prefix, as in Russell's example, and
  of any kinds; Russell's statement is general ("the order of the variables in the prefix is
  indifferent"), his example is (y) and (∃x). The quantifiers before them stay (`ExchStep`).
- **Both directions**: "and vice versa" (`ExchStep.symm` **[MEAS]**).
- **A primitive rule** (Pp), as Russell made it.
- **All types**: Russell states ✱8 for individual variables; here x and y may be of any type, as ✱9's
  definitions "can be repeated for successive types" (p. 136).

Two points of reading, each marked:
- **A restriction, needed for soundness.** Each quantifier after x and y binds a variable of one side
  only. Neither Russell's wording nor Landini's says this. Read without it, take
  A = (z) . R(x, z) ∨ ∼R(y, z): the ∨ has every x on one side and every y on the other,
  (x) : (∃y) : (z) . A is a theorem (y the x, ✱2·11), and exchanging (x) and (∃y) gives
  (∃y) : (x) : (z) . A, which is false where R is identity on two individuals **[MEAS]**
  (`switch_wide_unsound`, PM/Found9/Equiv.lean, pinned; stated for Switch, whose step this is too).
  Russell states ✱8·13 where every function has one variable ("For the present, however, we are not
  concerned with variable functions of two variables", p. 636, page image), so there the restriction
  holds of itself **[EST]**.
- **A narrowing.** The separating ∨ is the one that joins the two parts' matrices. Russell admits a
  stroke that is not the principal one (p. xxvi, quoted above); that is not formalized, since its
  derivation in ✱10 needs a normal form for formulas with one occurrence of a subformula. It might
  cover some of the 5 combinations of p. 142 left open in C (STAR9_FOUNDATION.md §7) **[EST]**.

**Is it the rule Switch we already had?** In part, and that part is reused, not rebuilt **[MEAS]**:
Landini's Switch (R3) is exactly the direction (x)(∃y) to (∃y)(x) of ✱8·13 carried over
(`SwitchStep.toExch`, `ExchStep.toSwitch`, pinned), with the same side condition `Sep` and the same
context, the prefix. ✱8·13 adds the converse direction and the exchange of two quantifiers of the
same kind, as primitive. So it is a new constructor of `Thm9` beside `switch`, sharing `Sep`; Switch
stays as L's rule.

**Why this repair.** It is the authors' own fix: Russell's rule for the chapter that replaces ✱9, as
he stated it. It leaves the printed definitions ✱9·01–✱9·08 alone; the printed ✱9·07 and ✱9·08
consistently put the universal quantifier first, a deliberate pattern rather than a slip. Landini
noted the connection (2000, §6, pp. 75–76, quoting ✱8·13: "This suggests that Russell himself had
noticed the flaw of the original ✱9"); we have now read ✱8·13 in the second edition itself. Landini's
✱9+ is attractive because it comes with a completeness proof, but this project proves such guarantees
itself, so his repair is kept as a checked variant (R3), not preferred for it. Maintainer's ruling,
2026-10-12.

**Status.** Working reading and default. **[MEAS]**:
- ✱8·13 is derivable by ✱10's method (`exchStep_q10`, PM/Found9/ToStar10.lean): before and after a
  step the proposition is a merge of the same two parts, and ✱10 proves each merge equivalent to their
  disjunction, given a variable of every type. So every theorem of C is a ✱10 theorem (`thm9_toQ`), and
  C is sound in every structure with an individual (`thm9_sound`).
- It is no general exchange (`exch_not_general`): C does not assert
  (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y).
- Every theorem of C is a theorem of the definitions as printed with the prenex Switch (R5), the same
  proposition (`Thm9.russell_toPrenex`).
- Relation to L (R3): Landini's Switch is a derived rule of C (`switch_russell`), and every step of
  ✱8·13 is derivable in L (`exch_plus`).
- Completeness of C (Russell's rule) is not proved; it is ours to prove, with Landini's completeness
  proof for ✱9+ (2000, §5) as prior work ([ROADMAP.md](ROADMAP.md)).

**What depends on it** (reading C). **[MEAS]**, from [STAR9_READINGS.md](STAR9_READINGS.md), "Where the
exchange rule is used":
- one step of PM's own proofs: ✱9·31 (3)–(4) (`f9_31_russell`), an exchange of (y) and (∃z); the other
  27 numbered propositions and the four ✱10 assertions are derived without it, the same propositions as
  under A (C has A's definitions);
- p. 142 for one apparent variable per letter: 15 of the 65 combinations C proves (1 to 2 steps each:
  16 exchanges of (x)(∃y), 3 of (∃x)(∃y)).

**Reversible.** ✱8·13 is one constructor of `Thm9`, gated by the reading; A, L and B do not have it.

## R2. Two quantifiers of the same kind: the left side's first

**What PM printed.** ✱9 prints no definition of "(x) . φx . ∨ . (y) . ψy" or
"(∃x) . φx . ∨ . (∃y) . ψy"; ✱9·03 and ✱9·05 are printed for an elementary p. The Introduction does
define the first, for elementary φ, ψ (1910 p. 49; second edition p. 47; quoted from our
transcription of a scan of the 1910 edition): "Similarly we can define a disjunction of two universal
propositions: "(x) . φx . ∨ . (y) . ψy" will be defined as meaning "(x, y) . φx ∨ ψy"" **[DOC]**. PM's
own proofs read both cases with the left side first: the last lines of ✱9·3
("(x) : φx . ∨ . (y) . φy" read as "(x) . φx . ∨ . (y) . φy" [(✱9·03)]) and of ✱9·31
("(∃x) : (∃y) . φx ∨ φy" read as "(∃x) . φx . ∨ . (∃y) . φy" [(✱9·05·06)]), p. 140. And the second
edition states the order as a rule for ✱8 (Vol. I, Appendix A, p. 635, page image) **[DOC]**:

> When the stroke occurs between two propositions which are both of the first order, we shall adopt the
> rule that the above definitions are to be applied first to the one on the left, treating the one on
> the right as if it were elementary, and are then to be applied to the one on the right. Thus
> {(x) . φx} | {(y) . ψy} . = : (∃x) : φx | {(y) . ψy} : = : (∃x) : (∃y) . (φx | ψy).

(also in the Introduction to the Second Edition, p. xxv, text layer: "we shall adopt the convention
that the one on the left is to be eliminated first, treating the one on the right as if it were
elementary"). ✱8's example has two existential quantifiers: the authors' own order for the
existential–existential case is the left side's first.

**What we read it as** (A and C, `PF.orPrinted`; B, `PF.or`). ✱9·03 or ✱9·05 with p the other side,
treated as if elementary, so the left side's quantifier comes out first; the definitions are then
applied again. For sides with one apparent variable each this is the Introduction's definition
(1910 p. 49; second edition p. 47), ✱8's rule and PM's last lines. One point of transposition
**[EST]**: ✱8 eliminates the whole of the left proposition first; in ✱9, once the left side's first
quantifier is out, the printed ✱9·07·08 apply again where the next two quantifiers are of different
kinds ("also when φ and ψ are not both elementary"). So for a left side (∃x) : (y) : (∃u) and a right
side (∃z), ✱9's definitions give (∃x) : (y) : (∃z) : (∃u), ✱8's whole-left order
(∃x) : (y) : (∃u) : (∃z). In C the two differ by one step of ✱8·13 (an exchange of (∃z) and (∃u), which the ∨ separates).

**Why.** The authors' own order, stated as a rule in the second edition, and the order of PM's own
proofs; not Landini's ✱9·zz, which has no counterpart in PM (R3).

**What depends on it.** The propositions of A, C and B whose disjunctions have two leading quantifiers
of the same kind with a further quantifier on the left. Landini's ✱9·yy and ✱9·zz (R3) are the other
choice: of the 70 combinations of p. 142, 5 are different propositions in L and in A or C **[MEAS]**.

**Reversible.** `PF.orPrinted` and `PF.or` are single definitions; L's `PF.orPlus` is kept.

## R3. Landini's ✱9+: Switch with ✱9·yy and ✱9·zz (reading L; a published variant, cross-check)

**What it is** (reading L, `Reading.withSwitch`). Landini's repaired system ✱9+ (2000, p. 64)
**[DOC]**: ✱9·01–✱9·08 as printed, with ✱9·03–✱9·06 for a side without apparent variables only, two
definitions for two quantifiers of the same kind,

> ✱9.yy (x)Ax ∨ (y)By = df (x)(y)(Ax ∨ By)
> ✱9.zz (∃x)Ax ∨ (∃y)By = df (∃x)(∃y)(Ax ∨ By)

(`PF.orPlus`; ✱9·yy is the Introduction's definition (1910 p. 49; second edition p. 47), which
Landini says Whitehead and Russell "anticipated" but which "never made an appearance in Principia's
formal statement of the system of ✱9"; ✱9·zz has no counterpart in PM and is his; each takes out the
outermost quantifier of each side), and the rule

> Switch (S): From B[(x)(∃y)Axy] infer B[(∃y)(x)Axy], where there is a logical connective in A on one
> side of which occur all free occurrences of the individual variable x and on the other side of which
> occur all free occurrences of the individual variable y.

It goes one way. It is formalized as `Thm9.switch` (PM/Found9/System.lean), admitted exactly when the
definitions are ✱9+'s (`R.defs = .plus`). A formula of ✱9 has its quantifiers in front, so an
occurrence of (x)(∃y)A in one is a tail of it and B is the quantifiers before it (`SwitchStep`); the
side condition is `Sep`, with the restriction and the narrowing of R1 (Landini's own use of the rule,
in ✱9·31, satisfies the restriction; whether the paper restricts A elsewhere is to be checked against
the full text, STAR9_FOUNDATION.md §8), and for variables of all types. "Without ✱9.yy and ✱9.zz,
however, definitions dfs(P)p would be ambiguous" (Landini, p. 64).

**Why it is kept, and why it is not the default.** It is a published repair, credited to Landini, who
also found the flaw (§4), and it comes with his proof that ✱9+ is complete for first-order logic
without identity (§5). It is not the authors' own fix, and it replaces the authors' order for two
quantifiers of the same kind (R2) with ✱9·zz. Its completeness proof is not a reason to prefer it: the
project proves such guarantees itself (R1, Status). It is kept as a checked variant: a second,
independently published repair through which PM's proofs go.

**Status and relation to C.** **[MEAS]**:
- Switch is derivable by ✱10's method (`switchStep_q10`); L is sound in every structure with an
  individual (`thm9_sound`); Switch is no general exchange (`switch_not_general`).
- Switch is the direction (x)(∃y) to (∃y)(x) of ✱8·13 (`SwitchStep.toExch`, `ExchStep.toSwitch`), so it
  is a derived rule of C (`switch_russell`).
- Every step of ✱8·13 is derivable in L (`exch_plus`): (x)(∃y) to (∃y)(x) is Switch; the converse is
  derived without Switch (`exch_imp_plus_ea`, as `switch_converse`; Landini derives it as dr(S*) from
  Switch, his T1 and MP2, §5); the exchange of two universal or two existential quantifiers takes one
  step of Switch (`exch_imp_plus_aa`, `exch_imp_plus_ee`). None of these three needs the side condition.
- Open: whether C and L prove the same expressions, each in the order its definitions give; their
  definitions make different propositions of one expression where two quantifiers of the same kind
  meet (R2).

**What depends on it** (L only). **[MEAS]**: ✱9·31 by Switch (`f9_31_switch`); ✱10·1 for every function
(`inst_plus`, through `exDrinker_plus`), where ✱9·zz puts an existential quantifier of φy before the
universal one whose variable it needs; p. 142, 63 of 70 combinations, 15 with Switch.

**Reversible.** Switch is one constructor of `Thm9`, gated by L's definitions; `PF.orPlus` is one
definition. No result of C depends on them.

## R4. An alternative convention (reading B): a cross-check, not the working repair

**What it is** (reading B, `PF.or`, `Reading.convention`). A precedence convention of our own,
stated like an order-of-operations rule:

> To write p ∨ q with its quantifiers in front, take them out one at a time from the front of p or of
> q, keeping each side's own order: a universal quantifier before an existential one, and of two of the
> same kind, the one in p first.

It is read off PM's proofs: line (4) of ✱9·31, and the last lines of ✱9·3 and ✱9·31 (p. 140; R2). Under
it the step of ✱9·31 is a definitional rewrite (`f9_31_step_convention`). It agrees with ✱9·03–✱9·08 as
printed whenever one side is elementary or each side has one apparent variable, and departs from them in
the case the note on ✱9·07·08 covers: for φx = (z) . R(x, z) and ψy = S(y), "(x) . φx . ∨ . (∃y) . ψy" is
(x) : (z) : (∃y) . R(x, z) ∨ S(y) under B and (x) : (∃y) : (z) as printed (both pinned).

**Why it is kept, and why it is not the default.** It is a repair of our own construction, not the
authors' and not precedent; it overrides the consistent pattern of the printed ✱9·07·08 with a
convention. It is kept as a cross-check:
- it shows that the ambiguity at ✱9·31 is real: a second, independent way of reading the text also
  makes PM's proof go through (every step PM justifies by definitions is a definitional rewrite under B,
  **[MEAS]**, 48 of 48);
- where B and C agree, neither repair changes anything beyond ✱9·31: both derive the 28 numbered
  propositions and the four ✱10 assertions along PM's lines **[MEAS]**.

**What it gives** (B only). **[MEAS]**: ✱9·31 by definitions (`f9_31`); p. 142, 67 of 70
(`Convention.t1_2` …); ✱10·12 for every p from the primitive propositions (`distrib_convention`).

**Reversible.** `PF.or` and `Reading.convention` are kept; no result of C depends on them.

## R5. The prenex Switch (our earlier repair, kept for comparison)

**What it is** (`Thm9.prenexSwitch`, opt-in by `R.rule = .prenex`; `Reading.prenexSwitch` is the
definitions as printed with it). Our own rule, an earlier reading C of this repository:

> If X and Y are two prenex forms of the same expression t, then from ⊢ X infer ⊢ Y.

An *expression* (`PE`) is what PM prints: ✱9 propositions combined by ∼, ∨ and quantifiers. A *prenex
form* of it (`Prenex`) takes the quantifiers to the front, those of each disjunct in their own order,
those of different disjuncts interleaved in any order (`Merge`).

**How it differs from ✱8·13 (R1) and Switch (R3).** It moves a quantifier past several at once, and it
reorders the quantifiers of the disjuncts of a nested expression, where ✱8·13 and Switch move only
quantifiers of parts joined at the matrix. A step of ✱8·13 or of Switch at the front is a step of it
(`exch_here_prenex`, `switch_here_prenex`), and every theorem of C is a theorem with it
(`Thm9.russell_toPrenex`) **[MEAS]**. Whether C or L derives it is open: it is sound, so Landini's
completeness theorem for ✱9+ (2000, §5) **[DOC]**, if right, gives its first-order instances in L; we
have not formalized that.

**Why kept.** For comparison: it is derivable in ✱10 (`switch_q10`) and sound, and with it every theorem
of B is a theorem of the definitions as printed (`Thm9.convention_toSwitch`), `Rep` for B gives `Rep`
there (`Rep.toSwitch`), ✱10·12 holds for every p without `Rep` (`distrib_switch`), and p. 142 has all 70
combinations (`PrenexSwitch.t1_2` …) **[MEAS]**. It is not the working repair: it is our construction,
broader than the authors' rule or Landini's.

**Reversible.** Off unless a reading sets it; none of A, C, L, B does.

## Literature

- **[DOC], read.** Landini (2000), above: the flaw (§4), ✱9+ (p. 64), completeness of ✱9+ for
  first-order logic without identity (§5), and ✱8 of the second edition (§6). Short quotations only.
- **[DOC], read.** ✱8 of the second edition (1925), Vol. I, Appendix A, pp. 635–637, and the
  Introduction to the Second Edition, pp. xxv–xxvi, in the 1963 impression described above: ✱8·13 and
  the order of elimination from the page images, the Introduction from the text layer.
- **[DOC], reported, not read.** G. Landini, "Will the real *Principia Mathematica* please stand up?
  Reflections on the formal logic of the *Principia*", in R. Monk and A. Palmer (eds.), *Bertrand
  Russell and the Origins of Analytical Philosophy* (Thoemmes, 1996), pp. 314–315, is reported to add
  the same definitions and Switch.
- The finding that the earlier disjunction of this repository did not follow ✱9·07·08 as printed came
  from an external review.
