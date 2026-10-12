# ✱9 by its own method, and its agreement with ✱10

Tags as in docs/STAR9_DESIGN.md: **[DOC]** is what a text says (PM's 1910 printed pages, the second
edition's, or a paper we have read), **[MEAS]** was run or checked in this repository, **[EST]** is a
judgement.

## 1. The question

- The rest of the project uses ✱10's "alternative method" (PM/Quant.lean; docs/STAR9_DESIGN.md says why).
- PM says the two methods are interchangeable. "✱10·1 is ✱9·2, ✱10·11 is ✱9·13, ✱10·12 is ✱9·25,
  ✱10·121 is ✱9·14, and ✱10·122 is ✱9·15. These five propositions must all be taken as primitive
  propositions in the alternative method; on the other hand, ✱9·1 and ✱9·11 are not required." **[DOC] p. 144**
- And: "by merely repeating the proofs", ✱1·2–✱1·6 hold when the letters are replaced by propositions
  with apparent variables, and so all of ✱2–✱5 hold for them. **[DOC] pp. 133, 138, 142**
- The project checks such claims rather than adopting them. PM/Found9/ builds ✱9's method alongside the
  existing foundation (no file of ✱10's foundation is changed) and checks the agreement.
- ✱9's definitions of disjunction, as printed, do not support one step of PM's own proof of ✱9·31
  (§3). Landini found this flaw and published a repair (2000, §4; §10 below). The authors' own later
  fix is a rule of the second edition, ✱8·13 (1925; §10). So ✱9 is formalized under four readings:
  - **A, as printed**: the definitions as printed, kept so that what PM printed stays visible;
  - **C, as printed + ✱8·13** (the working reading, the default): the same definitions and Russell's
    rule ✱8·13 of the second edition, carried over to ✱9;
  - **L, Landini's ✱9+** (a published variant, cross-check): the definitions as printed with two
    definitions for quantifiers of the same kind (✱9·yy, anticipated by PM in the Introduction,
    1910 p. 49, second edition p. 47; and ✱9·zz) and his rule Switch;
  - **B, alternative convention** (a cross-check): a precedence convention of our own, read off PM's
    proofs. It is kept because it shows that the ambiguity at ✱9·31 is real (a second, independent
    way of reading the text also makes PM's proof go through), and because where B and C agree,
    neither repair changes anything beyond ✱9·31. It is not the default and not precedent.

  [REPAIRS.md](REPAIRS.md) registers the repairs (R1–R5) and [STAR9_READINGS.md](STAR9_READINGS.md)
  gives the results under each reading, generated from the Lean statements, with where C uses ✱8·13
  and L uses Switch.

## 2. Files

| File | Contents |
|---|---|
| PM/Found9/Syntax.lean | elementary formulas `EF`, ✱9 propositions `PF`, ✱9·01–✱9·08 (`PF.neg`; `PF.orPrinted` as printed, `PF.orPlus` ✱9+, `PF.or` the alternative convention), readings (`Reading`, `Rule`), printed expressions and their prenex forms (`PE`, `Merge`, `Prenex`), the steps of ✱8·13 and of Switch (`Sep`, `ExchStep`, `SwitchStep`), translations `PF.toQ`, `QF.toF9` |
| PM/Found9/System.lean | `Thm9 S R`: ✱1·2–✱1·6 for elementary propositions, ✱9·1, ✱9·11, ✱9·12, ✱9·13, ✱8·13 carried over (the rule of C), Switch (the rule of ✱9+), the opt-in rules (the prenex Switch among them); `by_defs` |
| PM/Found9/Base.lean | tools from ✱9's primitives, for every reading: ✱9·2 and Id for every proposition (in L, ✱9·2 with Switch: `inst_plus`), ✱9·21 as a rule for every function, ✱9·25 for an elementary p; ✱9·22 as a rule as printed and in L; ✱9·25 for every p under B (`distrib_convention`) |
| PM/Found9/Star9.lean | ✱9·1–✱9·52 along PM's Dem. lines, for every reading except ✱9·31 (C: `f9_31_russell`; L: `f9_31_switch`; B: `f9_31`); ✱10·01, ✱10·1, ✱10·11, ✱10·12 as ✱9 theorems |
| PM/Found9/Switch.lean | the converse of Switch in L (`switch_converse`); a step of Switch at the front is a step of the prenex Switch (`switch_here_prenex`); with the prenex Switch, every reading's theorems (`Thm9.toSwitch`), ✱10·12 for every p (`distrib_switch`), the prenex form with universal quantifiers first (`PE.readU`) |
| PM/Found9/Exch.lean | ✱8·13 and the other rules: "and vice versa" (`ExchStep.symm`); Switch is its (x)(∃y) direction and a derived rule of C (`switch_russell`); every step of it is derivable in L (`exch_plus`); every theorem of C is one with the prenex Switch (`Thm9.russell_toPrenex`) |
| PM/Found9/SearchTactic.lean | `merge_split`, meta code for the proof search in C and L: it proposes the two parts of a merge for the side condition `Sep`; the proof is built from `Merge`'s constructors |
| PM/Found9/Simul.lean | p. 142 for one apparent variable per letter, under A, C, L and B and with the prenex Switch (the `search9`, `search9r` and `search9s` tactics) |
| PM/Found9/ToStar10.lean | every ✱9 theorem is a ✱10 theorem, under every reading (`thm9_toQ`); ✱8·13, Switch and the prenex Switch are derivable in ✱10 (`exchStep_q10`, `switchStep_q10`, `switch_q10`) |
| PM/Found9/FromStar10.lean | `Rep S R V` (✱1·2–✱1·6 for every ✱9 proposition under R); given it and a variable of every type, ✱9·25 for every p (`Rep.distrib`) and every ✱10 theorem is a ✱9 theorem (`qthm_toF9`) |
| PM/Found9/Equiv.lean | `star9_iff_star10`; soundness, consistency, failure without individuals; neither ✱8·13 nor Switch is a general exchange, and their side condition needs our restriction (`switch_wide_unsound`) |
| data/star9f_ledger.json | one row per ✱9 number (and ✱10·01, ✱10·1, ✱10·11, ✱10·12 in ✱9), in the format of the other ledgers; for ✱9·31 the check reads C's proof, L's and B's |
| Checks/Star9Readings.lean, scripts/star9_readings.py | the results under each reading, read from the Lean statements, and where C uses ✱8·13 and L uses Switch; docs/STAR9_READINGS.md |

Names: `PM.F9.f9_21` is ✱9·21 by ✱9's method; `PM.q9_21` (PM/Star10.lean) is the same proposition by ✱10's.

## 3. Representation

- **Elementary formulas** (`EF V`): predicate letters on individual variables, function variables
  applied to arguments, ∼, ∨. Same atoms as ✱10's `QF V` (PM/Quant.lean), same family `V : Ty → Type` of
  variables. "In what follows the single letters p and q will represent *elementary* propositions, and so
  will "φx," "ψx," etc." **[DOC] p. 134**
- **✱9 propositions** (`PF V`): `el e`, `all φ` ((x) . φx), `ex φ` ((∃x) . φx), with `φ : V τ → PF V` a
  Lean function as in PM/Quant.lean. Both quantifiers are primitive. **[DOC] p. 135**
- **∼ and ∨ are computed**, not primitive: `PF.neg` and the disjunction move every quantifier to the
  front, by ✱9·01–✱9·08. "The true scope of an apparent variable is always the whole of the asserted
  proposition." **[DOC] p. 136** ⊃, . and ≡ are ✱1·01, ✱3·01, ✱4·01 over them: "transferred unchanged"
  **[DOC] p. 136**.
- **The definitions of disjunction, as printed.** "To define disjunction when one or both of the
  propositions concerned is of the first order, we have to distinguish six cases, as follows:
  ✱9·03. (x) . φx . ∨ . p : = . (x) . φx ∨ p Df; ✱9·04. p . ∨ . (x) . φx : = . (x) . p ∨ φx Df;
  ✱9·05. (∃x) . φx . ∨ . p : = . (∃x) . φx ∨ p Df; ✱9·06. p . ∨ . (∃x) . φx : = . (∃x) . p ∨ φx Df;
  ✱9·07. (x) . φx . ∨ . (∃y) . ψy : = : (x) : (∃y) . φx ∨ ψy Df; ✱9·08. (∃y) . ψy . ∨ . (x) . φx : = :
  (x) : (∃y) . ψy ∨ φx Df. (The definitions ✱9·07·08 are to apply also when φ and ψ are not both
  elementary functions.)" **[DOC] pp. 135–136**. And: "The above definitions can be repeated for
  successive types, and thus reach propositions of any type." **[DOC] p. 136**
- **Two quantifiers of the same kind.** ✱9's text prints no definition of "(x) . φx . ∨ . (y) . ψy" or
  "(∃x) . φx . ∨ . (∃y) . ψy". The Introduction does, for two universal propositions with φ, ψ
  elementary (1910 p. 49; second edition p. 47; quoted from our transcription of a scan of the 1910
  edition): "Similarly we can define a disjunction of two universal propositions:
  "(x) . φx . ∨ . (y) . ψy" will be defined as meaning "(x, y) . φx ∨ ψy," i.e. "either φx is always true
  or ψy is always true" is to mean "φx or ψy is always true."" **[DOC] Introduction, 1910 p. 49;
  second edition p. 47** PM's proofs read both cases with the left side's quantifier first: the
  last line of ✱9·3 reads "(x) : φx . ∨ . (y) . φy" as "(x) . φx . ∨ . (y) . φy" (✱9·03), and the last
  line of ✱9·31 reads "(∃x) : (∃y) . φx ∨ φy" as "(∃x) . φx . ∨ . (∃y) . φy" (✱9·05·06)
  **[DOC] p. 140**. The second edition states the order as a rule for ✱8: "When the stroke occurs
  between two propositions which are both of the first order, we shall adopt the rule that the above
  definitions are to be applied first to the one on the left, treating the one on the right as if it
  were elementary, and are then to be applied to the one on the right" **[DOC] 2nd ed., Vol. I,
  p. 635, page image** (R2). For sides with one apparent variable each, all four readings below agree
  with these.
- **Reading A, as printed** (`PF.orPrinted`, `Reading.printed`): the equations applied to the outermost
  quantifier of each side; the disjunction left on the right-hand side (φx ∨ p, φx ∨ ψy, …) computed by
  the same definitions. When one side begins with (x) and the other with (∃y), ✱9·07 or ✱9·08 takes
  out both, the universal first, whatever φ and ψ contain. With φx = (z) . R(x, z) and ψy = S(y),
  "(x) . φx . ∨ . (∃y) . ψy" is (x) : (∃y) : (z) . R(x, z) ∨ S(y) **[MEAS]** (pinned in
  Checks/PinnedStatements.lean, with its ✱9·08 analogue). An external review found that the earlier
  disjunction of this repository did not follow this. Two quantifiers of the same kind: ✱9·03 or ✱9·05
  with p the other side, treated as if elementary (R2), so the left side's quantifier comes out first.
- **Where a step cited as definitional is not one, as printed.** In the proof of ✱9·31, PM goes from
  line (3), "(x) : (∃y) . φx ∨ φy . ⊃ . (∃z) . φz", to line (4), "(∃x) : (∃y) . φx ∨ φy : ⊃ . (∃z) . φz",
  by "[(3).(✱9·03·02)]" **[DOC] p. 140**: by definitions alone, with no step that exchanges quantifiers.
  That reads "(x) : (y) . ∼(φx ∨ φy) . ∨ . (∃z) . φz" by ✱9·03 with p = (∃z) . φz, which gives
  (x) : (y) : (∃z), line (3). But the left side begins with (x) and the right with (∃z), and ✱9·07
  applies "also when φ and ψ are not both elementary": it gives (x) : (∃z) : (y). **[MEAS]**
  `f9_31_step` proves the two propositions different under the definitions as printed (A and C),
  `f9_31_step_plus` under L's (given a variable of every type). Landini published this finding (2000,
  §4): "Unique among all the demonstrations of ✱9, this one misapplies the definition ✱9.03"
  **[DOC]**; the Lean check confirms it, and §5 relates his line numbers to PM's.
- **Reading C, as printed + ✱8·13** (`Reading.russell`, the default; R1 in [REPAIRS.md](REPAIRS.md)): A's
  definitions, unchanged, and Russell's rule ✱8·13 carried over to ✱9 (§4). Every proposition of C is
  the proposition A makes of the same expression.
- **Reading L, ✱9+** (`PF.orPlus`, `Reading.withSwitch`; R3, a published variant, cross-check):
  Landini's repaired system (2000, p. 64) **[DOC]**. ✱9·03–✱9·06 apply to a side without apparent
  variables only, ✱9·07·08 as printed, and for two quantifiers of the same kind
  "✱9.yy (x)Ax ∨ (y)By = df (x)(y)(Ax ∨ By)" and "✱9.zz (∃x)Ax ∨ (∃y)By = df (∃x)(∃y)(Ax ∨ By)": like
  ✱9·07·08, each takes out the outermost quantifier of each side. ✱9·yy is the Introduction's
  definition (1910 p. 49; second edition p. 47), which Landini says Whitehead and Russell
  "anticipated" in the Introduction but which "never made an appearance in Principia's formal
  statement of the system of ✱9"; ✱9·zz is his. L agrees with A and C except where both sides begin
  with quantifiers of the same kind and the left has a further one:
  (∃x) : (∃u) . φ(x, u) . ∨ . (∃y) . ψy is (∃x) : (∃y) : (∃u) in L and (∃x) : (∃u) : (∃y) in A and C
  (pinned). L's rule, Switch, is in §4.
- **Reading B, the alternative convention** (`PF.or`, `Reading.convention`; R4, a cross-check): *to
  write p ∨ q with its quantifiers in front, take them out one at a time from the front of p or of q,
  keeping each side's own order: a universal quantifier before an existential one, and of two of the
  same kind, the one in p first.* It is a convention of our own, read off the order PM's proofs use.
  Under it the step of ✱9·31 is a definitional rewrite (`f9_31_step_convention`, by `rfl`). It agrees
  with A when one side is elementary or each side has one apparent variable. The example above is
  (x) : (z) : (∃y) under B. Why it is kept: §1.
- The orders that different definitions give are equivalent in every structure with at least one
  individual (the quantified variables are distinct and each occurs on one side only). In ✱9 they are
  different propositions, and without ✱8·13 or Switch ✱9's primitive propositions have no rule that
  moves a quantifier.
- **Printed expressions** (`PE V`): ✱9 propositions combined by ∼, ∨ and quantifiers, as PM prints
  them before the definitions apply. `Prenex t X`: X is one of the propositions the definitions could
  make of t. The quantifiers of each disjunct keep their own order; those of different disjuncts are
  interleaved in some order (`Merge`). Each reading's definitions give one (`prenex_read`).
- **✱9·14, ✱9·15** (significance, types) are built into the syntax, as ✱10·121, ✱10·122 are in the ✱10
  system: every `φ : V τ → PF V` is a function and `φ a` (`a : V τ`) is a proposition. ✱9·131 and
  ✱9·6–✱9·63 are Lean's typing of `V τ` and are not stated. **[MEAS]**

## 4. The system `Thm9 S R`

- `R : Reading` is the definitions of ∨ (as printed, L's or B's) and the rule it adds, if any
  (`Rule`: ✱8·13 in C, or the prenex Switch). `R.imp`, `R.or`, `R.iff` are ✱1·01, ∨, ✱4·01 under its
  definitions.
- ✱1·2–✱1·6 for elementary propositions only (`taut` … `sum`): that they hold for the others is what
  ✱9·3–✱9·52 are for **[DOC] p. 138**.
- ✱9·12 is `mp` for all propositions; ✱9·13 is `gen` (a rule, as ✱10·11 is).
- ✱9·1 and ✱9·11 are stated for every function φ, with or without apparent variables. PM uses ✱9·1 so:
  line (3) of ✱9·21's proof applies it to a function containing (∃y) **[DOC] p. 139**.
- Comprehension and ✱12·1, ✱12·11 are the same gated rules as in `QThm S`, so every `Sys` has a ✱9
  counterpart. ✱12·1 is stated as printed, `(∃f) : φx . ≡ₓ . f!x` **[DOC] p. 174**, with (∃f) primitive.
  The styles of predicativity (PM/Pred/) inspect ✱10 formulas. So ✱9's comprehension rule takes ψ as a
  ✱10 formula, asks the style about it, and asserts the ✱9 proposition that ψ stands for (`QF.toF9`).
- **✱8·13 carried over** (`exch`, the rule of C, admitted when `R.rule = .exch`; R1). Russell's rule:
  "✱8·13. If all occurrences of x are separated from all occurrences of y by a certain stroke, we can
  change the order of x and y in the prefix, i.e. we can replace "(y) : (∃x) . φx | ψy" by
  "(∃x) : (y) . φx | ψy" and vice versa. Pp" **[DOC] 2nd ed., Vol. I, Appendix A, p. 636, page image**.
  Carried over (our transposition, R1): the stroke is the ∨ of ✱9's matrix, the prefix the quantifiers
  ✱9's definitions put in front, x and y two adjacent quantifiers of any kinds, both directions
  (`ExchStep`, `ExchStep.symm`), a primitive rule. The side condition is `Sep`: the proposition under
  the two quantifiers is a merge (`Merge`) of a part in which x alone is free and a part in which y
  alone is, in either order. Three points, registered in R1:
  - each further quantifier binds a variable of one part only. Neither Russell's wording nor
    Landini's says this, and without it the rule is unsound (`switch_wide_unsound`, §6) **[MEAS]**;
    Russell states ✱8·13 where every function has one variable (p. 636), where it holds of itself;
  - the ∨ is the one that joins the two parts' matrices; Russell admits a stroke that is not the
    principal one (p. xxvi), which is not formalized (§7, §8);
  - the variables may be of any type, not only individuals, as ✱9's definitions are "repeated for
    successive types" (p. 136).
  ✱10 derives it (`exchStep_q10`), and it is no general exchange (`exch_not_general`).
- **Switch** (`switch`, the rule of ✱9+, admitted exactly when `R.defs = .plus`; R3). Landini states it:
  "Switch (S): From B[(x)(∃y)Axy] infer B[(∃y)(x)Axy], where there is a logical connective in A on one
  side of which occur all free occurrences of the individual variable x and on the other side of which
  occur all free occurrences of the individual variable y." **[DOC] Landini 2000, p. 64** One
  direction only. A formula of ✱9 has its quantifiers in front, so an occurrence of (x)(∃y)A is a tail
  of it and B is the quantifiers before it (`SwitchStep`). The side condition is the same `Sep`, with
  the same three points. ✱10 derives it (`switchStep_q10`). Its converse is derived in L without
  Switch (`switch_converse`).
- **✱8·13 and Switch** (PM/Found9/Exch.lean) **[MEAS]**. A step of Switch is a step of ✱8·13 from
  (x)(∃y) to (∃y)(x), and conversely (`SwitchStep.toExch`, `ExchStep.toSwitch`): so Switch is a derived
  rule of C (`switch_russell`). Every step of ✱8·13 is derivable in L (`exch_plus`): (x)(∃y) to (∃y)(x)
  by Switch; (∃x)(y) to (y)(∃x) without it (`exch_imp_plus_ea`); two universal or two existential
  quantifiers with one step of Switch (`exch_imp_plus_aa`, `exch_imp_plus_ee`). The two rules thus
  derive each other in each other's systems. The systems still differ, in their definitions for two
  quantifiers of the same kind (§3); whether they prove the same expressions is open (§8).
- **The prenex Switch** (`prenexSwitch`, when `R.rule = .prenex`; off by default, gated like
  comprehension and reducibility; R5): if X and Y are two prenex forms of the same expression, from
  ⊢ X infer ⊢ Y. Our earlier repair, kept for comparison. It moves a quantifier past several at once,
  and reorders the quantifiers of the disjuncts of a nested expression; a step of ✱8·13 or of Switch at
  the front is one of its steps (`exch_here_prenex`, `switch_here_prenex`), and every theorem of C is a
  theorem with it (`Thm9.russell_toPrenex`). Whether C or ✱9+ derives it is open: Landini's
  completeness theorem (§10), if right, gives its first-order instances in L, since it is sound. The
  gates are in the reading rather than in `Sys`, which is shared with ✱10's method; there all three
  rules are theorems (`exchStep_q10`, `switchStep_q10`, `switch_q10`).
- **`by_defs`**: a proof stated for every reading cannot use ✱9·03–✱9·08 silently, since `R.or` does
  not compute until the reading is known. Each step PM justifies by definitions is taken by
  `by_defs`, which checks it under the definitions as printed (A and C), L's and B's.

## 5. ✱9's own development (PM/Found9/Star9.lean, data/star9f_ledger.json)

- ✱9·2–✱9·521 are 28 numbered ✱9 propositions, proved along PM's Dem. lines, with φ, ψ elementary as
  in ✱9. Each line that PM justifies by definitions ("[(4).(✱9·06)]") is stated in its printed form,
  and Lean accepts it as the same proposition as the line before.
- **[MEAS]** By reading ([STAR9_READINGS.md](STAR9_READINGS.md)):
  - C: 28 of 28; ✱9·31 with its step (3)–(4) by ✱8·13 (`f9_31_russell`), the only step of PM's
    proofs that ✱8·13 takes. The other 27 are derived without it, each the same proposition as under
    A.
  - A: 27 of 28. Every proof except ✱9·31's is stated for every reading. Of the 48 lines that cite a
    definition, 47 are checked under all three definitions.
  - L: 28 of 28; ✱9·31 with the same step by Switch (`f9_31_switch`).
  - B: 28 of 28.
- **✱9·31 under each reading.**
  - Lines (1)–(3) (`f9_31_dem`, the one use of ✱9·11) and the last step (`f9_31_last`) hold under
    every reading.
  - C: line (3) to line (4) is not a definitional rewrite (`f9_31_step`). Line (3) is
    (x) : (y) : (∃z), line (4) (x) : (∃z) : (y). In "∼(φx ∨ φy) ∨ φz" the ∨ separates all occurrences of
    y from all occurrences of z, so ✱8·13 changes the order of (y) and (∃z) inside (x).
  - L: not a definitional rewrite either (`f9_31_step_plus`), the same two propositions; Switch takes
    (y) : (∃z) to (∃z) : (y) inside (x): that is Landini's repair.
  - A: it is not a definitional rewrite (§3), and PM cites no other step. As printed, ✱9·31 is
    (x) : (∃z) : (y) . ∼(φx ∨ φy) ∨ φz. A proof by ✱9·13 and ✱9·1 must choose z before y and needs both
    z = x and z = y, so it needs this (∃z) : (y) proposition twice; ✱9·11 combines two instances of a
    function at real variables only. **[EST]** We have not found a derivation under A from ✱9's
    primitive propositions, nor shown that there is none: that is open. Read in a structure with an
    individual, the proposition is true (for each x take z with φz if there is one, any z otherwise),
    and given `Rep` it is an instance of ✱1·2.
  - B: line (3) to line (4) is a definitional rewrite (`f9_31`).
- **Landini's line numbers and PM's.** Landini writes ✱9·31's proof in six lines **[DOC] (2000, §4)**:
  1 "Ax v Ay .⊃. (∃z)Az" (✱9.11); 2 its (y) (UG); 3 "(∃y)(Ax v Ay) ⊃ (∃z)Az" (2, ✱9.02, ✱9.03); 4 its (x)
  (UG); 5 "(∃x)(∃y)(Ax v Ay) ⊃ (∃z)Az" (4, ✱9.02, ✱9.03, df(⊃)); 6 the proposition (5, ✱9.05, ✱9.06).
  PM's line (1), cited "✱9·11·13", is his 1 and 2; PM's (2) is his 3, PM's (3) his 4, PM's (4) his 5,
  and PM's last line his 6. He finds two misapplications of ✱9·03, 2→3 and 4→5, and repairs 2→3 when A
  is quantifier-free, by ✱9·06, UG and ✱9·07, "But one cannot similarly correct the move from line 4 to
  line 5." **[MEAS]** Our one disagreeing step, PM's (3)–(4), is his 4→5. His 2→3, PM's (1)–(2), does
  not show up as a failing step here, because Lean checks a definitional step as "the same proposition
  as the line before", not by the definitions cited: with φ elementary, line (1) is (y) : (∃z) by
  ✱9·06, and line (2) is (y) : (∃z) by ✱9·02 and ✱9·07, the same proposition under all three
  definitions. The citation of ✱9·03 there is a misapplication, as Landini says, but of the citation,
  not of the step; his repair of it uses the same definitions.
- Ledger: 28 numbered ✱9 propositions, 28 proved in C; with the four ✱10 assertions (✱10·01, ✱10·1,
  ✱10·11, ✱10·12), 32 of 32 proved. For ✱9·31 the ledger check reads C's proof (`f9_31_russell`), L's
  (`f9_31_switch`) and B's (`f9_31`); its row says how the readings differ. **[MEAS]**
- Text notes:
  - ✱9·5, ✱9·51, ✱9·52 cite ✱1·6 for line (1), but the line is ✱2·38 (✱1·6 with the disjunctions in the
    other order). **[MEAS]** ✱2·38 holds for elementary propositions, so the step is sound.
  - ✱9·3, line (5), applies ✱9·21 to "φx . ∨ . (y) . φy", which contains an apparent variable, while
    ✱9·21 is proved for elementary functions. The Lean line uses ✱9·21 as a rule for every function
    (`allImp`, PM/Found9/Base.lean, for every reading), whose premiss is line (4) with x real, taken
    from (2) by the same definitions. As printed (A and C) and in L, "(x) . φx . ⊃ . (x) . ψx" is
    (y) : (∃x) . ∼φx ∨ ψy by ✱9·08, so ✱9·13 and ✱9·1 give the rule from φx ⊃ ψx directly. Under B
    the proof also uses ∃-introduction inside a disjunction (`exI_or_convention`). **[MEAS]**
  - ✱9·31, line (4): see §3 and above.
  - ✱9·33 ("Proof as above") cannot copy ✱9·32: the (∃x) analogue of its line (2) is not ✱9·25. The
    reconstruction uses ✱9·1 at a real variable, so the Lean statement takes one. **[MEAS]**
  - PM's "(1).✱9·1.(✱9·06)" and "(2).✱9·13.(✱9·04)" in ✱9·5 and ✱9·501 each combine a rule with a
    definition; the Lean line takes the rule, then the definition by `by_defs`.
  - ✱10·12 "is a mere example of "q ⊃ q"" by the definitions in ✱9 **[DOC] p. 146**: true for elementary
    p (`f9_25` is Id), under every reading. For a p with apparent variables the two sides can be the
    same proposition or differ. For p = (∃u) . χu and φ elementary both are (x) : (∃u) . χu ∨ φx,
    under each definitions (pinned by `rfl` in Checks/PinnedStatements.lean), so that instance is Id
    as well. As printed, for p = (∃u) . χu and φx = (w) . ψ(x, w) they are (x) : (w) : (∃u) and
    (x) : (∃u) : (w) over the same matrix (`distrib_sides_ne`, PM/Found9/Base.lean). **[MEAS]**
- ✱10's primitive propositions as ✱9 theorems:
  - ✱10·1 (`f10_1`) for every function φ, under every reading. In A and C its proof uses no rule
    that moves a quantifier (`ai_printed`). In L it uses Switch (`inst_plus`, through
    `exDrinker_plus`): where ✱9·zz puts an existential quantifier of φy before the universal one of
    ∼(x) . φx whose variable it needs, ✱9·13 and ✱9·1 prove the other order and Switch gives the one
    the definitions give. For elementary φ (✱9·2) it does not. **[MEAS]**
  - ✱10·11 is ✱9·13;
  - ✱10·12 (`f10_12`) for an elementary p and every function φ, under every reading. For every p:
    - A, C and L: given `Rep` and a variable of every type (`Rep.distrib`,
      PM/Found9/FromStar10.lean). Those are assumptions of the proof for every p, not of each
      instance: an instance whose two sides are the same proposition, as for p = (∃u) . χu above, is
      Id and needs neither. ✱9·13 and ✱9·1 alone do not reach it as they do under B. With p = (u) . χu
      and φ elementary it is (x) : (u) . χu ∨ φx . ⊃ : (u) : (x) . χu ∨ φx, and ✱9·08 asks for the x
      of the antecedent before the consequent's x has been introduced. Whether ✱9's primitive
      propositions (with ✱8·13 in C, Switch in L) prove it for every p without `Rep` is not settled.
      **[MEAS]**
    - B: from the primitive propositions (`distrib_convention`). The definitions put every universal
      quantifier of the consequent first, then ✱9·1 chooses the antecedent's x.
    - With the prenex Switch: `distrib_switch`.
  - ✱10·01, "in either case we have ⊢ : (∃x) . φx . ≡ . ∼(x) . ∼φx" **[DOC] p. 145**, for elementary φ
    (`f10_01`), under every reading; in L its four quantifiers come out in the order ✱9·yy and ✱9·zz
    give, (x) : (x′) : (∃y) : (∃y′), and the proof takes them so (`f10_01_pre`).

  The general ✱10·1 rests, as printed and under B, on one lemma (`ai`): if Y is X with some leading
  universal quantifiers turned into real variables, then ⊢ X ⊃ Y. It is proved by induction on X from
  ✱9·13, ✱9·1 (for a φ with apparent variables) and Id for elementary propositions, once for each
  definition of ∨ (`ai_printed`, `ai_convention`). In L, Id for every proposition is proved without
  Switch (`idt_plus`) and ✱9·2 with it (`inst_plus`); `ai` itself is stated for A, C and B. **[MEAS]**

## 6. The agreement

**Theorem `PM.F9.star9_iff_star10`** (PM/Found9/Equiv.lean): for every system `S`, every reading `R`
and every ✱10 formula q, `QThm S q ↔ Thm9 S R (q.toF9 R.defs)`. It assumes that every type has a
variable (`hV`) and `Rep S R V`. **[MEAS]** No axioms.

- **✱9 ⊆ ✱10, unconditional apart from `hV`** (`thm9_toQ`), under every reading. Every ✱9 theorem,
  written with ✱10's primitive ideas, is a ✱10 theorem in the same `S`. ✱10 proves each of ✱9's prenex
  moves (✱10·2, ✱10·252, ✱10·253, ✱10·36): every way of taking the quantifiers of a disjunction to the
  front (`toQ_merge`), so every reading's definitions of ∨; a step of ✱8·13 (`exchStep_q10`: before and
  after it the proposition is a merge of the same two parts, and each merge is, in ✱10, their
  disjunction); a step of Switch (`switchStep_q10`); and the prenex Switch (`switch_q10`). Its own
  ✱9·1 and ✱9·11 (PM/Star10.lean) are reused. **[MEAS]**
- **✱10 ⊆ ✱9, given `Rep` and `hV`** (`qthm_toF9`), under every reading. Here `Rep S R V` is
  ✱1·2–✱1·6 for every ✱9 proposition under R: the conclusion PM draws on p. 142 ("the propositions of
  ✱1—✱5 hold when p, q, r are replaced by propositions containing any number of apparent variables").
  Given it and a variable of every type, every primitive of the ✱10 system holds in ✱9:
  - ✱1·1–✱1·6;
  - ✱10·1 and ✱10·11 (without `Rep`; in L ✱10·1 uses Switch, in C it uses no rule);
  - ✱10·12 (`Rep.distrib`; under B and with the prenex Switch also without `Rep`, §5);
  - the same gated rules.

  So, by induction on the derivation, every ✱10 theorem does. **[MEAS]**
- **`Rep` is not proved**, under any reading. PM's ✱9·3–✱9·52 give it for one quantified letter with
  elementary φ (except ✱9·31 under A, §5). §7 shows how far simultaneous replacement goes.
  `Rep` for B gives `Rep` with the prenex Switch (`Rep.toSwitch`).
  Beyond one apparent variable per letter, PM's "mere repetition" does not carry over: the
  definitions put the quantifiers of a compound proposition in orders that PM's proofs do not have,
  and moving them needs modus ponens through propositions of the same size. **[EST]** A proof would
  need a normal-form theorem for ✱9 derivations, in the style of Herbrand's work on quantification
  theory, or a completeness theorem: Landini proves ✱9+ complete for first-order logic without
  identity (2000, §5) **[DOC]**, which, if right, gives `Rep`'s first-order instances in L.
  Completeness of C, with Russell's rule, is ours to prove, with Landini's proof as prior work; we
  have not formalized either ([ROADMAP.md](ROADMAP.md)).
- **`Rep` under each reading.** `Rep` states a different proposition under each definitions of ∨.
  **[MEAS]** The direct method of §7 proves:
  - 50 of the 70 one-variable combinations under A;
  - 65 in C (50 without ✱8·13, the same as A's, and 15 with it);
  - 63 in L (48 without Switch, 15 with it);
  - 67 under B;
  - all 70 with the prenex Switch.

  **[EST]** It is no less plausible under A: its instances are valid in every structure with an
  individual, and the readings differ only in the order of independent quantifiers.
- **Individuals.** `hV` cannot be dropped (`thm9_unsound_empty`, every reading). In a structure with
  no individuals, take ✱9·1 for φf = (w) . Pw, f a function of individuals (the empty table exists),
  w an individual. ✱9·01 and ✱9·05 put (∃w) at the front, and the proposition is false there; ✱10's
  method is sound in that structure. **[MEAS]** So ✱9's method, unlike ✱10's, presupposes an
  individual through its definitions, not only through proofs that take a real variable
  (docs/STAR9_DESIGN.md §4).
- **Soundness and consistency of ✱9** (`thm9_sound`, `consistent9`), under every reading, ✱8·13,
  Switch and the prenex Switch included: every ✱9 theorem is true in every structure with an
  individual, and the letter p is not a ✱9 theorem. **[MEAS]** No axioms.
- **Neither rule is a general exchange** (`exch_not_general`, `switch_not_general`). Neither C nor L
  asserts (x) : (∃y) . R(x, y) : ⊃ : (∃y) : (x) . R(x, y): it is false where R is identity on two
  individuals. **[MEAS]**
- **The side condition needs our restriction** (`switch_wide_unsound`). Take
  A = (z) . R(x, z) ∨ ∼R(y, z): its ∨ has every free x on one side and every free y on the other, as
  Landini's wording asks and Russell's ("all occurrences of x are separated from all occurrences of y
  by a certain stroke") admits, but the quantified z occurs on both sides. (x) : (∃y) : (z) . A is a
  theorem under every reading (y the x, ✱2·11); read with the wording alone, Switch, or ✱8·13, would
  give (∃y) : (x) : (z) . A, false where R is identity on two individuals (take z the y and x the
  other). So `Sep` asks each quantifier of A to bind a variable of one side only, and does not hold for
  this A. **[MEAS]** Our notes quote Switch as stated on p. 64; whether Landini's paper restricts A
  elsewhere (for example in its definition of the formulas the rule applies to) is to be checked
  against the full text (§8).

## 7. p. 142 for one apparent variable per letter (PM/Found9/Simul.lean)

- Each of p, q, r in ✱1·2–✱1·6 is an elementary proposition, (x) . φx or (∃x) . φx with φ elementary:
  70 combinations besides the elementary one. Each theorem states the proposition that a reading's
  definitions make of the expression of ✱1·k (`e1_2` … `e1_6`).
- The tactic `search9` uses only what ✱9·3–✱9·52 use:
  - ✱9·13 for each leading (x);
  - ✱9·1 for each leading (∃x), the real variable found by unification, or the given one where
    nothing else is at hand (as in ✱9·33; `t1_3` takes a variable of every type);
  - an instance of ✱1·2–✱1·6 for the elementary matrix.

  In C, `search9r` may also take a step of ✱8·13 backwards: to prove (∃y) : (x) . Z it proves
  (x) : (∃y) . Z, where Z is a merge of a part with x and a part with y (`exchL`, `exchR`; the parts are
  proposed by `merge_split`), or it exchanges two leading existential quantifiers whose variables the
  ∨ separates (`exchEL`, `exchER`). In L, `search9s` does the same with Switch (`switchL`, `switchR`),
  and exchanges two leading existential quantifiers with one step of Switch (`exSwap`). Each tries
  every step without the rule first, so a combination proved without the rule is proved without it.
- **[MEAS] A, as printed: 50 proved.** Not covered (forms of p, q, r: `a` (x) . φx, `x` (∃x) . φx,
  `e` elementary):
  - ✱1·2 `x`;
  - ✱1·3 `aa`;
  - ✱1·4 `aa`, `xx`;
  - ✱1·5 `aaa`, `aae`, `aax`, `axa`, `xxa`, `xxe`, `xxx`;
  - ✱1·6 `aaa`, `aea`, `axa`, `axe`, `axx`, `xea`, `xxa`, `xxe`, `xxx`.

  In each, the definitions put an existential quantifier before the universal one whose variable it
  needs. For ✱1·3 `aa`: "p ∨ q" is (x) : (y) . φx ∨ ψy, and "q . ⊃ . p ∨ q" is
  (x) : (∃y′) : (y) . ∼ψy′ ∨ φx ∨ ψy (✱9·08), so y′ is chosen before y. ✱1·2 `x` is ✱9·31 (§5).
- **[MEAS] C, as printed + ✱8·13: 65 proved**: A's 50 without ✱8·13, and 15 with it (1 or 2 steps
  each: 16 exchanges of (x)(∃y), 3 of (∃x)(∃y); ✱1·2 `x` is ✱9·31). Not covered: ✱1·5 `axa`; ✱1·6
  `aaa`, `axa`, `axx`, `xxx`. In ✱1·5 `axa` the order of the quantifiers is a cycle: the antecedent's ∃
  for r must precede its ∀ for q, that ∀ must precede the consequent's ∃ for q, which precedes its ∀ for
  r, which must precede the antecedent's ∃ for r. **[EST]** Breaking it needs an exchange at a
  connective inside one side, whose remaining quantifiers bind variables outside both of its sides,
  which `Sep` does not admit (§4); we have not analysed the four of ✱1·6 one by one.
- **[MEAS] L, ✱9+: 63 proved**, 48 without Switch and 15 with it (1 to 3 steps each). Not covered:
  C's five, and ✱1·6 `xae`, `xax`, which A and C prove and which are different propositions in L
  (✱9·zz takes the sides' existential quantifiers out in pairs). The search's details per combination
  are in [STAR9_READINGS.md](STAR9_READINGS.md).
- **[MEAS] B, the alternative convention: 67 proved** (66 by the search, ✱1·2 `x` by ✱9·31). The three
  left are ✱1·6 `axa`, `axe`, `axx`. Here the order of (x) and (∃y) in p ∨ q is fixed by ✱9·07 under
  each definitions. As an antecedent, p ∨ q becomes (∃x) : (y); with r elementary the whole is
  "(x′) : (∃y′) : (∃x) : (y)" over the matrix, and the (∃y′) from ∼(q ⊃ r) needs the variable of the
  later (y). A proof by ✱9·13, ✱9·1 and ✱9·11 alone chooses every (∃) from variables already
  introduced, so no such proof exists, at any depth of ✱9·11.
- **[MEAS] With the prenex Switch (R5): 70 proved.** It takes each to the prenex form of its expression
  with the universal quantifiers out as early as possible (`PE.readU`). There every (∃) comes after the
  (x)s, and the search succeeds; ✱1·2 `x` is ✱9·31 with the prenex Switch.
- Whether ✱9's primitives (with ✱8·13 in C, Switch in L) prove the cases left under A, C, L and B by a
  longer route (modus ponens with ✱9·1 for a function that contains an apparent variable) is not
  settled. **[EST]** The obvious routes need the same step again: weakening the matrix under a prefix
  (∃) (∃) (∀), or using an (∃) (∀) proposition twice. For L, Landini's completeness theorem (§10), if
  right, gives the seven when the variables are individuals; for C, completeness is ours to prove.

## 8. Open questions

1. `Rep` (§6): prove it, refute it, or leave the agreement conditional, under each reading. *As it
   stands:* the agreement is stated conditional on `Rep`; a normal-form proof of `Rep`, with Landini's
   completeness proof for ✱9+ (§10) as prior work, is listed as a next item in [ROADMAP.md](ROADMAP.md),
   with the completeness of C.
2. Under A, ✱9·31 (§5) and the 20 cases of §7; in C, the 5 cases; in L, the 7; under B, the 3 cases of
   ✱1·6: do ✱9's primitives (with the reading's rule) prove them? If not, PM's claim on p. 142 fails for
   ✱9's method as printed, already for one apparent variable per letter. *As it stands:* open
   ([PM_CLAIMS.md](PM_CLAIMS.md), A10, A28, partly checked).
3. One step of PM's proof of ✱9·31, cited as definitional, is not a definitional rewrite under the
   definitions as printed (§3; Landini 2000, §4). *As it stands:* repaired with the authors' own rule,
   ✱8·13 of the second edition, carried over (C, R1); Landini's ✱9+ is kept as a checked variant (L,
   R3). A is kept and its results are reported beside the others; B is kept as a cross-check (R4)
   ([STAR9_READINGS.md](STAR9_READINGS.md)).
4. ✱8·13 and Switch as formalized (§4): their connective is the one that joins the two parts.
   Russell admits a stroke that is not the principal one (p. xxvi) and Landini's wording a connective
   deeper inside A, which might cover some of the cases of §7. *As it stands:* not formalized; its
   derivation in ✱10 needs a normal form for formulas with one occurrence of a subformula. Also to
   check against Landini's paper: whether it restricts A where our formalization must
   (`switch_wide_unsound`).
5. Two quantifiers of the same kind (§3): A, C and B take the left side's quantifier first, as ✱8 of
   the second edition orders the elimination and the Introduction defines it (1910 p. 49; second
   edition p. 47; R2); L has ✱9·yy and ✱9·zz (R3).
   *As it stands:* each reading's choice is pinned, and the results of each are measured.
6. Do C and L prove the same expressions, each in the order its definitions give? *As it stands:*
   each rule is derivable in the other's system (`switch_russell`, `exch_plus`); whether the theorems
   correspond is open.
7. Is the prenex Switch (R5) derivable in C or in ✱9+? *As it stands:* open; a step of ✱8·13 or of
   Switch at the front is one of its steps (`exch_here_prenex`, `switch_here_prenex`), and every theorem
   of C is a theorem with it (`Thm9.russell_toPrenex`); the converse is not shown.
8. ✱9's comprehension rule takes a ✱10 formula, because the styles of predicativity (`PM/Pred/`) are
   written for ✱10's formulas (§4). *As it stands:* kept; a style written for ✱9's propositions would
   let the rule take a ✱9 function directly.

## 9. Measurements

- Files: PM/Found9/*.lean (3033 lines with PM/Found9.lean), data/star9f_ledger.json; PM.lean imports
  PM/Found9.lean. No file of ✱10's foundation was changed for it. **[MEAS]**
- Each PM/Found9 file checks in under 11 s (PM/Found9/Simul.lean, the slowest, 10.8 s, searching five
  readings; the others under 2 s). **[MEAS]**
- `AllAxioms.lean`: 39 declarations use an axiom. The 14 of ✱9's syntax are Lean's generated
  `injEq` lemmas, as for every inductive type with data:
  - `EF` (5), `PF` (3);
  - `PE` (5) and `Reading` (1), new with the readings.

  No theorem of PM/Found9 uses an axiom. The meta code of PM/Found9/SearchTactic.lean is outside the
  `PM` namespace and is part of no proof. **[MEAS]**
- `AxiomCheck.lean` prints every public theorem of PM/Found9 (its generator globs every file under
  PM/, and reads `mutual` blocks and `_root_` names); each reports "does not depend on any axioms".
  **[MEAS]**
- `Checks/LedgerCheck.lean`, check 3, checks data/star9f_ledger.json against the proofs: every ✱9
  proposition, ✱2–✱5 theorem (through `elift`) and primitive of `Thm9` a row's proof uses is listed in
  the row. 36 rows, 0 disagreements, none open. The 7 rows of ✱9·14, ✱9·15, ✱9·131, ✱9·6–✱9·63 have
  no declaration. **[MEAS]**
- `Checks/Star9Readings.lean` and `tests/test_star9_readings.py`: the results of each reading, read
  from the statements; the 48 definitional steps of PM/Found9/Star9.lean; and where C uses ✱8·13 and
  L uses Switch (STAR9_READINGS.md, "Where the exchange rule is used"). **[MEAS]**
- RedCheck and StyleCheck read the `q…` theorems of ✱10's method only; the `PM.F9.f…` theorems are not
  among their 485 PM propositions. **[MEAS]**

## 10. ✱8·13 of the second edition, and Landini (2000)

**✱8 of the second edition.** *Principia Mathematica*, second edition (1925), Vol. I, read in a 1963
impression (Internet Archive item principia-mathematica_l2o7Ic0GMLeSLqcPnq, described as a
photographic reprint of the 1925 text; documented there, not checked by us against a 1925 printing).
**[DOC]**

- ✱8 replaces ✱9: "This chapter is to replace ✱9 of the text" (Appendix A, p. 635, footnote, page
  image); "The new chapter ✱8 (given in Appendix A) should replace ✱9 in Principia Mathematica"
  (Introduction to the Second Edition, p. xxv, text layer). It is built on the stroke, with ✱8·01–✱8·013
  for taking a quantifier out of one side, the rule that the left side is eliminated first (p. 635,
  page image; R2), and the primitive propositions ✱8·1, ✱8·11, ✱8·12, ✱8·13 (p. 636).
- ✱8·13, verbatim (p. 636, page image): "If all occurrences of x are separated from all occurrences of
  y by a certain stroke, we can change the order of x and y in the prefix, i.e. we can replace
  "(y) : (∃x) . φx | ψy" by "(∃x) : (y) . φx | ψy" and vice versa. Pp". On the same page: "We assume
  the legitimacy of this interchange by a primitive proposition, and in practice arrange to have all
  the ∃-prefixes as far to the right as possible, because this facilitates proofs." And p. xxv (text
  layer): "The order of the variables in the prefix is indifferent whenever the occurrences of one
  variable are all on one side of a certain stroke, while those of the other are all on the other side
  of it."
- Reading C carries ✱8·13 over to ✱9 (§4, R1). It is the authors' own repair, for the system that
  replaces ✱9; we do not claim that ✱9 intended it, and the carry-over is our transposition. ✱8 itself
  (the stroke, its definitions and its other primitive propositions) is not formalized.

**Landini (2000).** G. Landini, "Quantification Theory in ✱9 of *Principia Mathematica*", *History and
Philosophy of Logic* 21(1) (2000), 57–77, doi:10.1080/01445340050044646. Read in full (2026-10-12);
short quotations only. Landini cites PM by the pages of the second edition (Cambridge, 1962). **[DOC]**

- **The flaw is his.** §4, "The flaw of Principia's ✱9" (pp. 63–64): "Unique among all the
  demonstrations of ✱9, this one [✱9·31] misapplies the definition ✱9.03." He finds two
  misapplications, repairs one, and says the other cannot be repaired the same way (§5 above relates
  his lines to PM's). The step of ✱9·31 that this repository's checks flag is his 4→5.
- **✱9+ is his.** The system ✱9+ (p. 64): ✱9's language and rules with the two definitions ✱9.yy and
  ✱9.zz and the rule Switch, quoted in §3 and §4. He says Whitehead and Russell "anticipated the need
  of ✱9.yy in their introduction to the first edition" (p. 47, his page, which is the second
  edition's; 1910 p. 49), that "Without ✱9.yy and ✱9.zz, however, definitions dfs(P)p would be
  ambiguous", and that Russell "misconstrued definitions dfs(P)p and applied them to cases where p
  contains quantifiers". He does not say that ✱9 intended Switch. Reading L is his ✱9+, formalized
  with the points of §4 (R3).
- **Completeness.** §5 (pp. 64–75) proves ✱9+ semantically complete for predicate logic without
  identity, through a Russellian prenex normal form, with derived rules (among them dr(S*), the
  converse of Switch, from Switch, his T1 and MP2) and theorem schemata T1–T12. Prior work for `Rep`,
  for the completeness of C and for the open cases (§6–§8); not formalized here.
- **✱8 of the second edition, as he quotes it** (§6, pp. 75–76): "a stronger inference rule for
  switching quantifiers: Rule(✱8.13) From B[(x)(∃y)Axy] infer B[(∃y)(x)Axy], and vice versa, provided
  that every free occurrence of x in A is on one side and every free occurrence of y in A is on the
  other side of a stroke." Landini: "This suggests that Russell himself had noticed the flaw of the
  original ✱9." His paraphrase agrees with the rule as printed (quoted above).
- **What this repository adds** **[MEAS]**: a machine-checked confirmation of the flaw (of the 48
  steps of ✱9's proofs that PM justifies by definitions, 47 are definitional rewrites under the
  definitions as printed; the one that is not is in ✱9·31, `f9_31_step`); ✱8·13 carried over to ✱9 and
  ✱9+ both formalized, each rule derived in ✱10 and shown sound, and each derivable in the other's
  system; the measured use of each rule (one step of PM's proofs in both; ✱10·1 for every function in L
  only; 15 of the 70 combinations of p. 142 in each); the coverage of p. 142 for one apparent variable
  per letter under each reading; and the finding that the side condition, as worded by Landini (and
  by Russell), needs a restriction on the quantifiers of A to be sound (`switch_wide_unsound`).
- G. Landini, "Will the real *Principia Mathematica* please stand up? Reflections on the formal logic
  of the *Principia*", in R. Monk and A. Palmer (eds.), *Bertrand Russell and the Origins of Analytical
  Philosophy* (Thoemmes, 1996), pp. 314–315, is reported to add the same definitions and Switch. Not
  read here.
