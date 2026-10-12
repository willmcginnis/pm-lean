# Roadmap

What this project plans to do, how the pieces depend on each other, which tasks wait for others and why,
and what is already known about each from prior work. PM's claims about its own system, and their status,
are in [PM_CLAIMS.md](PM_CLAIMS.md); decisions already taken are in [TYPES_DESIGN.md](TYPES_DESIGN.md);
measured progress is in [PROGRESS.md](PROGRESS.md). This page was last revised on 2026-10-12, with the
statuses of commit `efbb89d`; the counts in it are read from PROGRESS.md and PM_CLAIMS.md when it is
generated, not copied by hand.

![Roadmap overview: four groups of work and five milestones](roadmap/overview.svg)

## Principles

**Search prior work first.** Before any task is started, and as the first step of every task, prior work
is searched in depth: existing formalizations (Lean, Rocq/Coq, Isabelle, HOL, Metamath, Mizar, Agda),
papers, theses, talks and repositories. Several independent search and deep-research tools are used and
their findings compared. An earlier search found a formalization of PM that had gone much further than
expected, so this is not a formality. The search saves work, gives ideas, shows early whether a task is
easy, hard or a dead end, and gives independent work to check ours against. Findings are recorded per
task: what exists, how far it got, its license, and whether its ideas can be reused. Code is never copied
from unlicensed repositories; ideas only. The searches are cheap and independent of each other, so all of
them can run now, ahead of the work they inform. The search is not a separate task: it opens every task.
What the searches so far found is listed under each subgroup below.

**Check PM's claims.** When PM asserts something about its own system (that two methods are equivalent,
that proofs carry over "by merely repeating previous proofs", that a construction "covers all the cases"),
the assertion is treated as a theorem to check in Lean, not an assumption to adopt. Each claim is listed in
[PM_CLAIMS.md](PM_CLAIMS.md) with its page and status, and is checked when its chapter is reached. A claim
found not to hold as stated is a result, recorded as such.

**One source, many checkers.** PM is formalized once, here, in Lean, and that development is the single
source. Other foundations do not get their own rewrite of PM: they receive the same derivations through an
automatic export and check them, as one carefully written program can be compiled by several independent
compilers. Work below the Lean development checks it; it does not replace it. Several checkers can all
accept a wrongly translated statement, so the translation itself is also checked (adequacy, below).

**The order is a plan, not a contract.** Work moves when it fits better elsewhere or costs little, and the
reason is recorded. Small tasks that are independent of the rest are done early. A task placed later than
its dependencies require says so (*by choice*, with the reason), and a task that has moved says where it
was and why ([Tasks that moved](#tasks-that-moved)).

## How the plan is organized

The work is in four **groups** that run side by side:

1. **PM itself**: the text, volume by volume and chapter by chapter, with PM's claims checked as each
   chapter is reached; and the 1925 second edition.
2. **Checking underneath**: the same derivations re-checked by independent Lean kernels, by Metamath and
   Rocq checkers, and in ZFC; and Lean's own kernel, verified for the fragment this project uses.
3. **Comparing across**: the same statements compared with other readings of PM, with mainstream
   mathematics (Mathlib), and with the printed text.
4. **Results about PM**: adequacy, incompleteness, the finitist audit, WKL₀ and decision procedures.

Each group is split into **subgroups**, and each subgroup into **tasks** the size of a chapter block or of
one stage of a larger piece of work. For each task the plan gives:

- its **status**: done, in progress or not started, read from the repository;
- its **size**: S (days to a few weeks), M (weeks to a few months) or L (several months or more), with the
  reason;
- what it **needs**: the tasks whose results it cannot do without. These are the **gates**: arrows between
  particular tasks, not walls between phases;
- what it is **helped by**: tasks that make it easier (shared tools, comparisons, experience) but are not
  required;
- its **order**: *by dependency* if it is placed as early as what it needs allows, or *by choice* if it is
  placed later than that, with the reason;
- the **prior work** found for it, with what the search found it good for (*reuse*: licensed code or data
  to import or depend on; *ideas*: read it, write our own; *check against*: an independent result to
  compare with; *nothing found*; *not yet searched*) and an evidence level for each entry: *measured* (its
  source was read at a pinned commit; nothing was built unless said), *documented* (a paper or README says
  so), *unverified* (reported, not checked), or *from memory* (listed before the search reached this
  task). "Not found" means not found by the searches so far, not that nothing exists.

A few **milestones** mark the plan's progress, each named by what is true when it is reached:

<!-- generated:milestones:start -->
| Milestone | True when |
|---|---|
| Vol I checked | Every numbered assertion of ✱1–✱97 is derived from PM's primitive propositions, or listed with the reason it is not; every Vol I claim in PM_CLAIMS.md is checked or marked with why not. |
| Vol II checked | The same for ✱100–✱234: every assertion derived or listed with the reason; every Vol II claim checked or marked. |
| Vol III checked | The same for Vol III (✱250–✱375), read from its proofread transcription. |
| First edition audited | Vols I–III checked; the transcriptions of all three volumes checked against scans of the print; the census of which results use reducibility, infinity or the multiplicative axiom complete; the statement comparisons with set.mm and with other formalizations of PM complete. |
| Lean's kernel fragment verified | The kernel features this project exercises are listed; a checker with a machine-checked correctness theorem for that fragment (an existing one, or our own restricted checker) re-checks the build; and what that theorem covers, and what it does not, is stated. |
<!-- generated:milestones:end -->

## The plan

The tables, lists and charts on this page and in the README are generated from one data file,
[data/roadmap.json](../data/roadmap.json), by [scripts/roadmap_chart.py](../scripts/roadmap_chart.py)
(see [Maintaining this page](#maintaining-this-page)).

<!-- generated:plan:start -->
### 1. PM itself

Formalize the text, volume by volume and chapter by chapter, and check PM's claims about its own system as each chapter is reached.

![Group 1, PM itself: its subgroups and tasks](roadmap/group-pm.svg)

#### Vol I (1910)

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| ✱1–✱5: the theory of deduction | done. 188 of 188 assertions proved from ✱1·1–✱1·6; complete for two-valued truth tables (PM_CLAIMS A1: checked). | M: 188 assertions with ledgers and a completeness theorem; finished. | nothing | nothing | by dependency |
| ✱9–✱14: apparent variables, types, identity, descriptions | in progress. By ✱10's method: ✱10 46 of 48, ✱11 51 of 51, ✱13 25 of 25, ✱14 47 of 47, ✱9 4 of 28. ✱14·3 is proved as a schema; a type of propositions is revisited if Vols II–III or the 1925 pass need propositions as variables (TYPES_DESIGN.md, Q8). ✱9 by its own method is the next three tasks. | M: 199 assertions, 173 of 199 proved by ✱10's method; what is left is ✱9's own method. | nothing | ✱9 beside ✱10 | by dependency |
| ✱9's method beside ✱10's, shown to derive the same results (p. 144) | in progress. Built (PM/Found9, docs/STAR9_FOUNDATION.md): 27 of 28 numbered ✱9 propositions proved by ✱9's own method, along PM's lines; ✱9·31 is open. `star9_iff_star10` makes the agreement conditional on Rep (✱1·2–✱1·6 for every ✱9 proposition) and on a variable of every type (PM_CLAIMS A29: partly checked). | M: A second set of primitive propositions, ✱9's development and an equivalence theorem. | nothing | nothing | by dependency |
| ✱9·31 and the one-variable cases of p. 142: derived by ✱9's method, or shown underivable | in progress. ✱9·31's lines (1)–(3) are proved; line (4), cited as definitional, is not a definitional rewrite under the definitions as printed, and no other step is cited. 50 of the 70 cases are proved (PM_CLAIMS A10, A28: partly checked). Separate work considers ✱9 as printed beside a repaired ✱9 (docs/STAR9_FOUNDATION.md §8, §10); a repair is kept as a marked repair and does not replace the printed reading. | M: One proposition and 20 cases of ✱1·2–✱1·6 for one apparent variable per letter; a proof of underivability would need a model of ✱9's method. | nothing | ✱9 beside ✱10 | by dependency |
| A normal-form proof of Rep: ✱1·2–✱1·6 for every proposition of ✱9's method (p. 142) | not started. With it, the agreement of the two methods (p. 144) rests only on a variable of every type. For the variables of a structure (`QModel.den`) an individual gives a value of every type (`den_nonempty`); for an arbitrary family of variables it does not, so there that assumption stays as stated. | L: A normal-form theorem for ✱9 derivations, in the style of Herbrand's work on quantification theory. | nothing | ✱9·31 as printed | by dependency |
| Every theorem checked under both foundations, ✱9's and ✱10's | not started | M: As StyleCheck does for the predicativity styles; done if the cost measured on a trial branch is reasonable. | Rep | ✱9 beside ✱10 | by dependency |
| ✱20–✱24: classes and relations | in progress. ✱20 53 of 55 and ✱21 46 of 48 proved: done, the rest being ✱20·631·632 and ✱21·631·632, about significance, which are built into the syntax. ✱22–✱24 next. | M: 316 assertions; ✱20 and ✱21 are done, ✱22–✱24 are a calculus of classes and relations. | nothing | ✱9–✱14 | by dependency |
| Apparent classes of classes and their identity, needed from ✱40 on | in progress. Decided (literal reading of ✱20·08) and built for the definitions and ✱20·4, ✱21·4; apparent classes of classes not yet (docs/CLASSES_OF_CLASSES.md). | M: A second layer of the class construction, built as printed (✱20·08), with its identity. | nothing | ✱20–✱24 | by dependency |
| Extensionality of every class and relation expression, proved once (pp. 200, 213) | done. PM_CLAIMS D1: checked, for the expressions PM's notation forms (`clsExpr_ext`, `relExpr_ext`). For a Lean function that uses the class otherwise, which PM's notation cannot form, the premise remains. | M: A general theorem over the expressions PM's notation forms, replacing an explicit premise. | nothing | ✱20–✱24 | by dependency |
| ✱30–✱38: the logic of relations | not started | M: Descriptive functions, converses, domains, relative products; mostly short proofs. | ✱20–✱24 | nothing | by dependency |
| ✱40–✱56: products and sums of classes; unit classes and couples, to ✱54·43 | not started | L: Classes of classes throughout; ✱54·43 is the step before 1 + 1 = 2. | ✱30–✱38, classes of classes | nothing | by dependency |
| ✱60–✱74: sub-classes, relative types; one-many and one-one relations | not started | L: Typical ambiguity and relative types become central here. | ✱40–✱56 | nothing | by dependency |
| ✱80–✱88: selections, with the multiplicative axiom as hypothesis | not started | M: Selections and ✱88's multiplicative axiom, carried as an explicit hypothesis as PM states it. | ✱60–✱74 | nothing | by dependency |
| ✱90–✱97: inductive relations | not started | L: The ancestral and induction in ramified types; the base for Vol II and Appendix B. | ✱60–✱74 | ✱80–✱88 | by dependency |
| A model that sees orders: what reducibility adds (claim B11) | not started. The present models forget orders. | M: A new model in which the predicativity styles can differ without ✱12·1. | nothing | ✱9–✱14 | by dependency |

Prior work:

- **✱1–✱5** (check against). Done many times elsewhere; only this project and l-pommeret/Principia-Mathematica use PM's own ✱1 rules (docs/FORMALIZATION_COMPARISON.md). Metamath set.mm: about 220 theorems pm1.* to pm5.*, CC0 (*measured*); Metamath pmproofs.txt, ✱2–✱5 by condensed detachment, CC0 (*documented*); principia-rewrite (Coq, shallow, GPL-3.0): a comparison only (*measured*).
- **✱9–✱14** (check against, ideas). l-pommeret/Principia-Mathematica (Lean 4): a deep ramified layer, ✱9 26 of 28 and ✱10 34 of 35 by our count; no license, so ideas only (*measured*); Metamath set.mm: about 50 PM-numbered ✱10–✱14 theorems, CC0 (*measured*); Neo-Principia (Rocq): shallow (*measured*); Wang (1960): the predicate part of ✱10–✱14 is a decidable fragment (*documented*).
- **✱9 beside ✱10** (ideas, check against). Faithful ✱9 is reported hard. Landini (2000), 'Quantification theory in ✱9 of Principia Mathematica': reported to find a flaw in ✱9 as printed, repaired by a minor change (*documented*); Urquhart (2016), on ✱9 and ✱10 (*documented*); Holmes's SML code (2002–04): a partial proof checker for ramified type theory loaded with PM's ✱1 and ✱9/✱10 axioms, under a permissive notice (*measured*).
- **✱9·31 as printed** (ideas). Landini (2000), as above; a later presentation of ✱9 by Landini is reported to add a rule exchanging quantifiers (*unverified*).
- **Rep** (not yet searched).
- **both foundations** (not yet searched).
- **✱20–✱24** (ideas, check against). A shallow embedding is known to have stalled here. Neo-Principia (Rocq): ✱20 with 78 admitted steps; its own audit names the scope of incomplete symbols and host equality hiding reducibility as the blockers (MIT): a failure report to learn from (*measured*); l-pommeret/Principia-Mathematica: 183 statements and 128 proofs over ✱20–✱56 (our count) (*measured*); Holmes: polymorphic typing for PM's classes (*documented*).
- **classes of classes** (not yet searched).
- **extensionality** (not yet searched).
- **✱30–✱38** (ideas). Landini, 'Note on Principia's ✱38 on operations' (*documented*); l-pommeret/Principia-Mathematica: proofs into this range (*from memory*).
- **✱40–✱56** (check against). Metamath set.mm: pm54.43, with its own note on the translation (*measured*); l-pommeret/Principia-Mathematica: proofs into ✱56 (*measured*).
- **✱60–✱74** (ideas). l-pommeret/Principia-Mathematica: deep to about ✱70, then shallow (*measured*); PM-MATS dependency graph of both editions: all rights reserved, so consulted for ordering only (*measured*).
- **✱80–✱88** (ideas). PM-MATS dependency graph: consulted for ordering only (*measured*).
- **✱90–✱97** (ideas). PM-MATS dependency graph: consulted for ordering only (*measured*).
- **order-seeing model** (ideas). An extensional model proves consistency but cannot show that reducibility adds strength; that needs a model that sees orders. Reported research-level. Mares (2007): a semantics validating reducibility (*documented*); Fitch (1938), Lorenzen (1951): consistency of ramified PM without reducibility (*documented*); Kamareddine, Laan and Nederpelt: a modern reconstruction of PM's ramified types (*from memory*).

#### Vol II (1912)

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Per-item list of Vol II, and its claims listed by reading | not started. Only an upper bound on Vol II's labels exists (data/vol2_labels.json). | S: Reading and parsing; no proofs. | nothing | Vol I–II text | by dependency |
| ✱100–✱126 (Part III): cardinal arithmetic, to ✱110·643 (1 + 1 = 2) and inductive cardinals | not started | L: PM's cardinal numbers, their arithmetic, finite and infinite; Infinity (✱120·03) as hypothesis. | ✱80–✱88, ✱90–✱97 | Vol II list | by dependency |
| ✱150–✱186 (Part IV): relation-arithmetic | not started. Which Part III propositions it cites is to be measured from the citation graph. | L: Ordinal similarity and relation-numbers, with their arithmetic. | ✱90–✱97 | ✱100–✱126 | by dependency |
| ✱200–✱234 (Part V, first half): series | not started | L: Series, sections, limits; the base for Vol III. | ✱90–✱97 | ✱150–✱186 | by dependency |

Prior work:

- **Vol II list** (check against). PM-MATS citation graph: counts only, no copying (all rights reserved) (*measured*).
- **✱100–✱126** (ideas). No deep formalization found. Burgess and Hazen (1998): elementary arithmetic inside ramified PM with infinity, without reducibility (*documented*); l-pommeret/Principia-Mathematica: ✱110 shallowly, through Lean's sets (*documented*); Metamath set.mm theorem pm110.643 (*from memory*).
- **✱150–✱186** (nothing found).
- **✱200–✱234** (nothing found).

#### Vol III (1913)

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Per-item list of Vol III, and its claims listed by reading | not started | S: Reading and parsing; no proofs. | Vol III text | nothing | by dependency |
| ✱250–✱276 (Part V, continued): well-ordered series, ordinals, compact and continuous series | not started | L: Well-ordering, transfinite ordinals and the order theory PM's reals use. | ✱150–✱186, ✱200–✱234, Vol III text | Vol III list | by dependency |
| ✱300–✱375 (Part VI): quantity: ratios, real numbers, measurement, cyclic families | not started | L: PM's own theory of quantity, little studied and not formalized as far as known. | ✱200–✱234, Vol III text | ✱250–✱276, Vol III list | by dependency |

Prior work:

- **Vol III list** (nothing found).
- **✱250–✱276** (nothing found). l-pommeret/Principia-Mathematica: shallow declarations; ✱260 as a list of strings (*documented*).
- **✱300–✱375** (nothing found). Gandon, Russell's Unknown Logicism (2012), on PM's Part VI (*from memory*).

#### 1925 second edition

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Record the edition differences, and the new Introduction's claims | not started | S: A list from reading, no proofs. | nothing | nothing | by dependency |
| ✱8 and Appendix A, in place of ✱9 | not started | M: A second quantification theory, compared with ✱9 and ✱10. | ✱9 beside ✱10 | finite core, edition differences | by dependency |
| Appendix B (✱89, induction without reducibility): locate the failing step and prove a narrower replacement | not started | M: The argument is a known dead end as stated: the step that fails (reported around ✱89·16) is located, and a narrower replacement is proved, or a countermodel to the step is given. | ✱90–✱97 | edition differences | by dependency |
| Appendix C: truth-functions and extensionality | not started | M: Builds on the truth-function results of ✱14 and the extensionality work. | ✱9–✱14 | extensionality, edition differences | by dependency |
| Full second-edition pass | not started | L: The revised calculus carried through the volumes, as a second pass. | edition differences, ✱8 and Appendix A, Appendix B, Appendix C | nothing | by choice, after ✱250–✱276, ✱300–✱375. After Vol III, as a second pass over a finished first edition. |

Prior work:

- **edition differences** (ideas). Linsky, The Evolution of Principia Mathematica (2011) (*documented*); PM-MATS covers both editions (*documented*).
- **✱8 and Appendix A** (ideas). No mechanization found. ✱8 and Appendix A are treated together; a treatment with the stroke alone misses the change to quantification. Hazen and Davoren (2000), 'Russell's 1925 logic': both editions reconstructed (*documented*); a paper on ✱8 and the empty domain (History and Philosophy of Logic) (*documented*).
- **Appendix B** (ideas). Gödel (1944), 'Russell's mathematical logic': the objection to ✱89 (*documented*); Myhill (1974): no collapse at any finite order (*documented*); Hazen (2004): the reconstruction does not validate induction (*documented*); Landini (1996): defends a reconstruction (*documented*).
- **Appendix C** (ideas). Nothing mechanized found. Hazen, on the 1925 Introduction and Appendix C; Russell concedes losses there (*documented*).
- **second-edition pass** (nothing found).

### 2. Checking underneath

One source, many checkers: the same derivations re-checked by independent kernels, by Metamath and Rocq checkers, and in ZFC; and Lean's own kernel verified for the fragment the project uses.

![Group 2, Checking underneath: its subgroups and tasks](roadmap/group-under.svg)

#### Independent Lean kernels

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Independent Lean kernels re-check the build in CI, one checker per code family | not started. CI today builds and runs the project's own checks only. | S: Existing checkers on the pinned toolchain: the official kernel, one checker of the nanoda family, con-leche (with a machine-checked theorem about what it accepts), and Tenet or eink0rn (separately written). | nothing | nothing | by dependency |

Prior work:

- **kernels in CI** (reuse). lean4lean and other checkers that follow the C++ kernel add little independence. Lean Kernel Arena: 26 checkers in about 7 lineages, a negative-test corpus, run on this project's toolchain (*measured*); nanoda (Rust, Apache-2.0) (*measured*); Tenet (C#, MIT/Apache-2.0) (*measured*); con-leche (Lean, Apache-2.0): accepts only the three standard axioms (*measured*); a kernel bug caught by nanoda in July 2026, and a nanoda bug fixed a week earlier: pin current versions (*documented*).

#### Metamath and Rocq

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| pm.mm for ✱1–✱5, from the finite propositional core, checked by several Metamath verifiers | not started | S: Propositional formulas need no binding; the core's certificates are written out as Metamath; small verifiers of a few hundred lines each. | adequacy ✱1–✱5 | nothing | by dependency |
| pm.mm for ✱9–✱14, from the finite first-order core: binding, substitution, distinct-variable conditions | not started. A Metamath proof is finite and a `QThm` proof is not (`QThm.gen` has one premise for every variable), so pm.mm is built from the core, not exported from `QThm`. | M: Quantifiers and types need distinct-variable conditions and type checking in Metamath. | pm.mm ✱1–✱5, finite core | nothing | by dependency |
| pm.mm from ✱20 on, chapter by chapter | not started | M: Defined notation for classes and relations; then incremental per chapter. | pm.mm ✱9–✱14, adequacy from ✱20 | nothing | by dependency |
| Rocq re-check: our own small checker for our certificate format, proved sound in Rocq | not started | M: No ready tool of the strength wanted: moderate for ✱1–✱5, hard for ✱9–✱14 (side conditions, orders). The result states that proofs, not only statements, were checked. | finite core | nothing | by choice, after pm.mm ✱9–✱14. The maintainer's order: after pm.mm, so the certificate format is settled on one consumer before a second is added. |

Prior work:

- **pm.mm ✱1–✱5** (ideas, reuse). Metamath nf.mm, which opens by taking PM's ✱1·2–✱5·75 as its base; hol.mm, iset.mm (all CC0): database conventions to reuse (*measured*); AML-Formalization: a proof-of-concept exporter from a deep embedding in Coq to Metamath (LGPL-2.1) (*measured*); metamath.exe, metamath-knife, mmverify.py, checkmm (*from memory*).
- **pm.mm ✱9–✱14** (ideas). Carneiro, conversion of HOL Light proofs into Metamath (2016) (*documented*); hol.mm: types as terms (CC0) (*measured*).
- **pm.mm from ✱20** (not yet searched).
- **Rocq re-check** (ideas). rocq-lean-import (LGPL-2.1, alpha): runs Rocq with definitional UIP and without universe checks for some inductives; an optional extra, reported as such (*measured*); Metamatix, a Metamath checker in Rocq: its soundness file is empty (*measured*); LRAT (two certified checkers for one format) and SMTCoq: the pattern to follow (*documented*); coq-hol-light ships its theorems as Rocq axioms: why the result must say proofs were checked (*measured*); MetaRocq, for trusting Rocq itself (*measured*).

#### set.mm and ZFC

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| set.mm: replay ✱1–✱5 inside ZFC | not started | S: set.mm already proves PM's propositional primitives; a link file. | pm.mm ✱1–✱5 | nothing | by dependency |
| A model of PM's types in ZFC: each primitive proposition and rule proved true once | not started | L: A model of ramified types with reducibility, and a soundness induction. | finite core | order-seeing model | by dependency |
| Every exported derivation transferred through the model | not started | M: Automatic once the model and the quantified export exist. | ZFC model of PM's types, pm.mm ✱9–✱14 | pm.mm from ✱20 | by dependency |

Prior work:

- **set.mm replay ✱1–✱5** (reuse, check against). Metamath set.mm: 281 pm* labels, CC0 (*measured*); Carneiro's embedding of hol.mm in set.mm, as the template (*documented*).
- **ZFC model of PM's types** (ideas). With reducibility, an extensional model: moderate; with infinity: hard. Mares (2007); Fitch (1938); Lorenzen (1951) (*documented*); Isabelle AFP Q0_Metatheory and HOL_in_HOL_Deep: semantics, soundness and consistency for simple types (*documented*); Flypitch: a deep-embedded theory with a model, in Lean (*measured*).
- **transfer through the model** (not yet searched).

#### Lean's own kernel

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| (a) Census of the kernel features the project exercises | not started. The axiom reports already show that no PM derivation uses propext, Quot.sound or Classical.choice. | S: An instrumented re-check of the build, extending the axiom reports. The questions that decide stage (c): does the development, with what it imports, use nested inductives, or Nat and String literals (the orders of types use Nat, atoms use String)? | nothing | nothing | by dependency |
| (b) Lean in Lean: Lean4Lean re-checks the build | not started. Lean4Lean itself is others' work, in progress. Its README says it follows the C++ kernel closely and is not really an independent implementation. | M: Others' implementation; our part is running it on this project and reading its scope. | nothing | kernels in CI | by dependency |
| (c) A restricted checker for that fragment: first existing verified checkers (con-leche), then our own only if needed | not started | M: First re-check the build with con-leche, and with metalean's slow checker if our literals are acceptable to it. Our own restricted checker (for example over a literal-free re-encoding) only if they do not serve. | kernel census | Lean4Lean run | by dependency |
| (d) A formal proof that the checker used is correct against a specification of the fragment | not started | L: For an existing checker: read and audit its specification and theorem, and say what it does not cover (neither con-leche's nor metalean's covers the executable driver). For our own: a refinement proof, research-scale. | restricted checker | Lean4Lean run | by dependency |

Prior work:

- **kernel census** (reuse). Lean Kernel Arena descriptors: which features each checker declines (*measured*).
- **Lean4Lean run** (reuse). Used as a checker; not described as verification. Lean4Lean (Apache-2.0): checks Mathlib; its metatheory is partial (inductive types not yet specified) (*measured*).
- **restricted checker** (reuse, check against). con-leche (Apache-2.0): a full checker with a machine-checked theorem that every environment it accepts has a set model (*measured*); metalean (Apache-2.0): a verified checker for an idealised Lean type theory; its slow checker declines Nat and String literals and nested inductives, so it probably declines this development as it is (*measured*); mini-kernel, canonical-min: small, unverified (*measured*).
- **checker correctness proof** (reuse, check against). metalean: soundness against its own typing specification; consistency relative to ZFC with ω inaccessibles, its only axiom (*measured*); con-leche: `model_exists` (*measured*); MetaCoq's verified checker for Coq (*from memory*).

#### Lean and ZFC: relative consistency

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Lean proves Con(ZFC): existing mechanizations cited and re-checked | not started | S: Existing proofs are re-built on a pinned toolchain; the task states what each proves, for which encoding of ZFC. | nothing | nothing | by dependency |
| ZFC with inaccessibles proves Con(Lean's type theory): existing mechanizations cited and re-checked | not started | S: Existing proofs are re-built on a pinned toolchain; the task states, for each, in which system it is proved, from which hypotheses, and for which type theory. | nothing | Lean proves Con(ZFC), Lean4Lean run | by dependency |

Prior work:

- **Lean proves Con(ZFC)** (check against, reuse). Flypitch (Lean 3, Apache-2.0): `ZFC_is_consistent` for its encoded ZFC; a Lean 4 port exists (*measured*); Mathlib's ZFSet (*documented*).
- **ZFC + inaccessibles proves Con(Lean)** (check against, reuse). Carneiro, The Type Theory of Lean (2019): a paper proof for Lean 3 from ZFC with n inaccessibles; its repository has no license (*documented*); con-leche: `model_exists`, every environment it accepts has a set model (*measured*); metalean: `consistency`, relative to ZFC with ω inaccessibles, for an idealised type theory (*measured*); lean4lean-model: its main theorem is still `sorry` (*measured*); Werner, 'Sets in types, types in sets' (1997), for Coq (*from memory*).

### 3. Comparing across

The same statements compared with other readings of PM, with mainstream mathematics, and with the printed text.

![Group 3, Comparing across: its subgroups and tasks](roadmap/group-across.svg)

#### Other readings of PM

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Compare with set.mm's own PM theorems, chapter by chapter | not started. set.mm is listed in the formalization comparison but not measured. | S: Statement-level matching by PM number; a few hundred theorems. | nothing | ✱20–✱24 | by dependency |
| Compare other formalizations of PM, number by number | in progress. docs/FORMALIZATION_COMPARISON.md measures several projects; one of them (Neo-Principia) has changed since, so its row is to be measured again. | S: Statement-level comparison on the survey's common scale. | nothing | nothing | by dependency |

Prior work:

- **set.mm comparison** (check against). 281 pm* labels in set.mm and 198 in iset.mm (CC0), reaching ✱10–✱14 and ✱54, not only ✱1–✱5 (*measured*).
- **other formalizations** (check against). docs/FORMALIZATION_COMPARISON.md is itself the survey. l-pommeret/Principia-Mathematica unchanged since it was measured (*measured*); the Agda PM development's ✱9 does not build as published (a missing module) (*measured*); Lacrimae-Angeli: ✱1 only, no license (*measured*).

#### Mainstream mathematics (Mathlib), in a separate package

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Cardinal arithmetic (✱100–✱126) agrees with Mathlib's Nat and Cardinal | not started. A semantic agreement, not a conservativity result about the proof system, and labelled so. | M: The first bridge, with the package: theorems about the collapse model's denotations; typical ambiguity as a family of bridges that commute with type raising. | ✱100–✱126 | ZFC model of PM's types | by dependency |
| Relation-numbers (✱150–✱186) agree with Mathlib's order types, and with Ordinal for well-orders | not started | M: PM's relation-numbers cover relations that are not well-orders; Mathlib's Ordinal covers well-orders only. | ✱150–✱186, Mathlib: cardinals | nothing | by dependency |
| Series, ordinals and real numbers (Vol III) agree with Mathlib | not started | M: Order types, ordinals and PM's reals mapped to Mathlib's; the last step is easy once a complete ordered field is in hand. | ✱250–✱276, ✱300–✱375, Mathlib: cardinals | Mathlib: relation-numbers | by dependency |

Prior work:

- **Mathlib: cardinals** (ideas, reuse). No bridge from any historical or type-theoretic system to Mathlib found. Mathlib: `Cardinal.eq`, `mk_sum`, `mk_prod`, `lift_mk_eq` (*measured*); ZFLean (Apache-2.0): isomorphisms of products, powersets and function spaces (*measured*).
- **Mathlib: relation-numbers** (ideas). Mathlib: `RelIso`, `Ordinal.type_eq` (well-orders only) (*measured*).
- **Mathlib: series and reals** (ideas, reuse). Mathlib: `inducedOrderRingIso` (*measured*); Spivak Lean (Apache-2.0): Dedekind cuts made a field, then `isoFun_eq_inducedOrderRingIso` (*measured*).

#### The printed text

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Vol I and Vol II transcriptions checked against scans; errata reported | in progress. Companion text audit; errata prepared, awaiting the scan check and reporting. | M: Errata are prepared; each needs a check against the scan. | nothing | nothing | by dependency |
| Vol III transcription proofread and checked against scans | in progress. At Distributed Proofreaders (companion text audit). | M: Volunteer proofreading under way; then the same scan checks. | nothing | nothing | by dependency |
| ✱1–✱5 as transcribed: every formula parses with the printed dots and is derivable | in progress. PM/Statements.lean was generated from the transcription by a dot parser (scripts/gen_lean.py), and ✱1·4 and ✱4·42 were found this way; not yet a standing check. It catches underivable transcriptions only: a derivable formula can still be mistranscribed. | S: The dot parser and the completeness theorem exist; the task runs them on the raw transcription as a standing check and reports each failure to the text audit. | nothing | Vol I–II text | by dependency |

Prior work:

- **Vol I–II text** (ideas, check against). No tool found that certifies formula transcriptions against scans. Gerrata (MIT): transcription against scans, the same architecture (*measured*); PM-MATS: counts only (all rights reserved) (*measured*); Project Gutenberg eBooks #78050 (Vol I) and #78255 (Vol II) (*from memory*).
- **Vol III text** (ideas). Distributed Proofreaders' LaTeX workflow (*documented*).
- **dots check** (nothing found). The text audit sets PM's dots aside; this check is what the formalization adds.

### 4. Results about PM

Metatheorems about the formalized system: adequacy, incompleteness, the finitist audit, WKL₀ and decision procedures.

![Group 4, Results about PM: its subgroups and tasks](roadmap/group-about.svg)

#### Finite syntax and adequacy

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Adequacy, stage 1: ✱1–✱5, a finite certificate format and both translations | not started | S: Propositional formulas are already finite; the work is the certificate format and both translations. | nothing | nothing | by dependency |
| Adequacy, stage 2: a finite first-order core for ✱9–✱14, with derivations as data, and the easy direction (every core derivation gives a QThm theorem) | not started. Today `QF` binds with Lean functions and `QThm.gen` takes one premise for every variable, so a `QThm` proof is not a finite object (docs/SEMANTICS.md). The core is the source for pm.mm beyond ✱5, the Rocq re-check and incompleteness. | M: Finite syntax with named or de Bruijn variables, types and orders; finite derivations; a translation into QF and soundness at every V. | adequacy ✱1–✱5 | ✱9 beside ✱10 | by dependency |
| Adequacy, stage 2, the converse: from QThm back to the finite core | not started. Three ways, to be chosen before incompleteness starts: (a) a restricted QThm whose formulas are all well-formed; (b) the theorems needed re-derived in the core; (c) full conservativity. | L: Exotic intermediate formulas, the infinitary generalization rule and order side conditions; no precedent found. Possibly research-level. | finite core | nothing | by dependency |
| Adequacy, stage 3: classes and beyond | not started | M: Defined notation, classes of classes, and whatever the later volumes add (for example functions of three or more arguments), on stage 2's core. | finite core | classes of classes, ✱20–✱24 | by dependency |

Prior work:

- **adequacy ✱1–✱5** (nothing found). Propositional formulas have no binders; none needed.
- **finite core** (ideas). Two independent searches recommend this architecture: a finite core as the source of truth, related to the present encoding by a proved translation. FormalizedFormalLogic/Foundation (Apache-2.0): locally nameless first-order formulas (*measured*); HOL_in_HOL_Deep (BSD): a locally nameless deep embedding (*documented*); lean-hoas: in Lean, a parametric encoding does not exclude exotic terms; no license, ideas only (*measured*); Grenrus (2025, Agda): a well-formedness predicate and a proved round trip between de Bruijn and parametric terms; no license (*measured*); Hybrid (Isabelle): an encoding over de Bruijn terms with an admissibility predicate and adequacy results (*documented*); nothing for ramified types, or for derivations with an infinitary generalization rule (*unverified*).
- **converse** (ideas). Chlipala's well-formedness predicate for parametric syntax (*documented*).
- **adequacy from ✱20** (nothing found).

#### Incompleteness

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| PM as a many-sorted first-order theory (the finite core), in a separate package that reuses the Foundation library | not started | M: The core presented as a first-order theory in Foundation's sense; Foundation brings Mathlib and classical axioms, so it stays out of the core package. | finite core | nothing | by dependency |
| Numbering of the core's formulas and derivations; 'is a derivation of' representable | not started | M: Standard arithmetization, taken from Foundation where its encoding fits. | first-order PM | adequacy from ✱20 | by dependency |
| Robinson's Q interpreted inside the chosen PM theory, with Infinity as hypothesis | not started. PM's cardinal route (✱100–✱126) is the default; a shorter internal interpretation may exist. | L: Every axiom of Q proved inside the theory, with typical ambiguity resolved to one type. | ✱100–✱126 | numbering | by dependency |
| Gödel's first theorem for PM, in the Gödel–Rosser form | not started | L: The diagonal argument is reused; the work is representability inside PM's own arithmetic for the first-order presentation. | first-order PM, numbering, Q interpreted | converse, adequacy from ✱20 | by choice, after ✱250–✱276, ✱300–✱375. The maintainer's priority: the theorem after Vol III. Not a dependency: nothing in Vol III feeds it. |
| Gödel's second theorem for PM: derivability conditions, then Con unprovable | not started | L: The derivability conditions for PM's provability predicate need induction inside the theory. | Gödel I, ✱90–✱97 | nothing | by dependency |

Prior work:

- **first-order PM** (reuse). Foundation's theorems are stated for first-order theories, hence the first-order presentation. Foundation (Lean 4, Apache-2.0): the first theorem for Δ₁, Σ₁-sound theories containing R₀; Gödel–Rosser for any encodable first-order theory; the second theorem for consistent Δ₁ theories containing IΣ₁, with the derivability conditions proved; no `sorry` in its incompleteness part (not built) (*measured*).
- **numbering** (reuse). Foundation, as above (*measured*); Paulson, Gödel's theorems in Isabelle/HOL (hereditarily finite sets) (*documented*).
- **Q interpreted** (ideas). Without the axiom of infinity PM has a finite model, so this route needs infinity. Burgess and Hazen (1998): arithmetic in ramified PM (*documented*).
- **Gödel I** (reuse, ideas). Nothing for any type theory or for PM. Foundation, as above (*measured*); O'Connor (Coq, MIT): essential incompleteness of arithmetic (*measured*); Popescu and Traytel: abstract, syntax-independent formalization in Isabelle (*documented*).
- **Gödel II** (ideas). Because a too-weak specification of the provability predicate is reported to have given a spurious second theorem, the predicate's adequacy is stated here as an explicit theorem. Foundation: the second theorem over IΣ₁, with the derivability conditions proved (*measured*); Paulson; Popescu and Traytel (*documented*); O'Connor's Coq development assumes two of the derivability conditions (*measured*); a reported case where a too-weak specification of the provability predicate gave a spurious second theorem (*documented*).

#### Finitist audit

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Assumption provenance: which results use reducibility, infinity, the multiplicative axiom | in progress. Reducibility tags exist for ✱1–✱21 of ✱10's method (RedCheck.lean); ✱9's own method is not yet among them; infinity and choice are added as the volumes reach them. | S: Extends RedCheck and AllAxioms, which exist; kept up per chapter. | nothing | nothing | by dependency |
| PRA readings: which results have an arithmetic reading provable in PRA | not started | L: A formal PRA, a translation of PM statements, and a PRA proof or certified reduction for each. | assumption tags, PRA, RCA₀, WKL₀ | Π⁰₂-conservativity, Mathlib: relation-numbers, numbering | by choice, after ✱250–✱276, ✱300–✱375. The maintainer's order: alongside incompleteness. Not a dependency on it. |
| Complete census of assumptions, all three volumes | not started | S: Collected from the per-chapter tags. | assumption tags, ✱100–✱126, ✱150–✱186, ✱200–✱234, ✱250–✱276, ✱300–✱375 | nothing | by dependency |

Prior work:

- **assumption tags** (ideas). set.mm's per-theorem axiom usage lists (*from memory*).
- **PRA readings** (ideas). Tags of rule use do not certify provability in PRA. No PRA object theory in Lean found; Foundation has IΣ₀ and IΣ₁ (*measured*); Tait, 'Finitism' (1981) (*documented*).
- **assumption census** (not yet searched).

#### WKL₀

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| PRA, RCA₀ and WKL₀ as formal systems | not started | M: Their own syntax and proof systems, separate from PM's. | nothing | nothing | by choice, after Gödel I. The maintainer's order: after incompleteness. Nothing in PM's volumes is needed. |
| WKL₀ is Π⁰₂-conservative over PRA | not started | L: A substantial proof (Friedman; Sieg; Simpson), not formalized as far as known. | PRA, RCA₀, WKL₀ | nothing | by dependency |

Prior work:

- **PRA, RCA₀, WKL₀** (ideas). reverse-mathlib (Lean 4, Apache-2.0): ω-model facts and one syntactic result, kept apart (*measured*); Simpson, Subsystems of Second Order Arithmetic (*from memory*).
- **Π⁰₂-conservativity** (ideas). A first formal proof would be new. Not mechanized anywhere found (*unverified*); Sieg (1985), the syntactic route; Simpson (1988) (*documented*); Simpson credits the result to Friedman's 1977 communication to Harrington (*documented*).

#### Decision procedures

| Task | Status | Size | Needs | Helped by | Order |
|---|---|---|---|---|---|
| Monadic first-order fragment | not started. Prior work searched (below); the build comes with the other decision procedures. The fragment: one type of individuals, one-place predicate variables of that type, quantifiers over individuals only. | M: Known algorithm; the work is producing PM derivations for the restricted fragment. | finite core | ✱9–✱14 | by choice, after PRA, RCA₀, WKL₀. The maintainer's order: built with the other decision procedures, after WKL₀ is started. |
| Presburger arithmetic (addition only) | not started | M: Proof-producing procedures exist elsewhere; the target is PM's interpreted addition. | ✱100–✱126 | Q interpreted | by choice, after PRA, RCA₀, WKL₀. Same reason as the monadic procedure. |
| Tarski: real closed fields | not started | L: Real quantifier elimination is hard to make proof-producing. | ✱300–✱375 | nothing | by choice, after PRA, RCA₀, WKL₀. Same reason as the monadic procedure. |

Prior work:

- **monadic** (ideas, check against). What is new here: validity over arbitrary domains, PM's convention on the empty domain, and producing PM derivations. Coq library of undecidability proofs (MPL-2.0): decides finite satisfiability for monadic signatures (*measured*); Orlandelli and Tesi (2024): a syntactic decision procedure; models of size at most 2^k (*documented*); Löwenheim (1915); Behmann (1922) (*from memory*).
- **Presburger** (ideas). Nipkow, linear quantifier elimination (Isabelle, BSD) (*documented*); Théry (Coq, LGPL-2.1) (*measured*); Lean's `omega` is not a decision procedure, so not relied on for metatheory (*measured*).
- **Tarski** (ideas, reuse). Cohen and Mahboubi (Coq, CeCILL-B) (*measured*); Rocq CAD, `cylindrical_decomposition` (LGPL-3.0) (*measured*); Sturm–Tarski theorems in Lean (Apache-2.0; no quantifier elimination) (*measured*); McLaughlin and Harrison (HOL Light, proof-producing) (*documented*).
<!-- generated:plan:end -->

## What runs now, what waits, and why

### Now, in parallel

Every task under way, and every task whose gates are all done and that is not held back by choice:

<!-- generated:now:start -->
- **PM itself.** Under way: ✱9–✱14; ✱9 beside ✱10; ✱9·31 as printed; ✱20–✱24; classes of classes. Can start: Rep; order-seeing model; Vol II list; edition differences.
- **Checking underneath.** Can start: kernels in CI; kernel census; Lean4Lean run; Lean proves Con(ZFC); ZFC + inaccessibles proves Con(Lean).
- **Comparing across.** Under way: other formalizations; Vol I–II text; Vol III text; dots check. Can start: set.mm comparison.
- **Results about PM.** Under way: assumption tags. Can start: adequacy ✱1–✱5.
<!-- generated:now:end -->

The prior-work searches for every task run now too.

The groundwork that several tasks share starts now: a finite syntax for PM's formulas and proofs, and
adequacy in stages (✱1–✱5, then ✱9–✱14, then classes and beyond). The second stage builds a finite
first-order core, with derivations as data, and proves the easy direction: every derivation in the core
gives a theorem of the present embedding. The present derivations cannot be numbered or exported as they
are, because `QThm.gen` takes one premise for every variable, so a `QThm` proof is infinitely branching.
pm.mm beyond ✱5, the Rocq re-check, the model of PM's types in ZFC and the incompleteness work are all built
on the core.

With one maintainer, the limit is not how many tasks could start but how many decisions and reviews one
person can make. So one principal task on PM's text and one bounded support task are in review at a time;
searches, mappings and isolated proofs are prepared alongside; changes to shared interfaces are made one at
a time; long builds run against pinned commits; and coherent changes are released together. Decisions are
batched, and where an open choice is cheap to build both ways, both are built and both must pass, as the
project already does for the readings of "predicative".

### Waits for a dependency

These are the gates; the dependency view below shows every one.

- **The volumes, chapter by chapter.** ✱20–✱24 → ✱30–✱38 → ✱40–✱56 (which also needs apparent classes of
  classes) → ✱60–✱74 → ✱80–✱88 and ✱90–✱97 → Vol II's Parts III–V → Vol III, which also needs its
  proofread transcription. Dependencies are on the chapters actually cited, not on whole volumes.
- **✱9's own method.** Checking every theorem under both foundations needs the normal-form proof of Rep.
- **The finite core.** pm.mm for ✱1–✱5 needs the first stage of adequacy. The second stage (the finite
  first-order core) gates pm.mm beyond ✱5, the Rocq re-check, the model of PM's types in ZFC, the
  first-order presentation of PM for incompleteness, ✱8's comparison with ✱9 (through ✱9 beside ✱10) and
  the monadic decision procedure; pm.mm from ✱20 on needs the third stage.
- **The exports.** The set.mm replay needs pm.mm for ✱1–✱5; transferring every derivation through the ZFC
  model needs both the model and the quantified export.
- **Incompleteness.** The first theorem needs the first-order presentation, the numbering, and an
  interpretation of Robinson's Q inside the chosen PM theory, which needs Vol II's cardinal arithmetic
  (✱100–✱126). Nothing in Vol III feeds it. The second theorem needs the first, and induction inside the
  theory (✱90–✱97).
- **Decision procedures that produce PM derivations.** Monadic: the finite core. Presburger: PM's addition
  (✱100–✱126). Tarski: PM's real numbers (✱300–✱375). Studying the algorithms needs none of these.
- **The 1925 edition.** ✱8 and Appendix A need ✱9 beside ✱10; Appendix B needs Vol I's induction
  (✱90–✱97); Appendix C needs the truth-function results of ✱9–✱14.
- **Lean's kernel.** The census, then the re-check by a verified checker (an existing one first), then the
  correctness proof, or the audit of an existing one.
- **Comparisons with Mathlib**, from ✱100 on, after the chapters they compare; the **complete assumption
  census**, after all three volumes; the **PRA readings**, after a formal PRA.

### Waits by choice

The maintainer's order of priorities: the three volumes first, with PM's claims checked in each; then
incompleteness, with the finitist audit alongside; then WKL₀ and the decision procedures. Where that places
a task later than its dependencies require, the task is marked *by choice*:

<!-- generated:choice:start -->
| Task | Placed after | Why |
|---|---|---|
| Full second-edition pass | ✱250–✱276, ✱300–✱375 | After Vol III, as a second pass over a finished first edition. |
| Rocq re-check: our own small checker for our certificate format, proved sound in Rocq | pm.mm ✱9–✱14 | The maintainer's order: after pm.mm, so the certificate format is settled on one consumer before a second is added. |
| Gödel's first theorem for PM, in the Gödel–Rosser form | ✱250–✱276, ✱300–✱375 | The maintainer's priority: the theorem after Vol III. Not a dependency: nothing in Vol III feeds it. |
| PRA readings: which results have an arithmetic reading provable in PRA | ✱250–✱276, ✱300–✱375 | The maintainer's order: alongside incompleteness. Not a dependency on it. |
| PRA, RCA₀ and WKL₀ as formal systems | Gödel I | The maintainer's order: after incompleteness. Nothing in PM's volumes is needed. |
| Monadic first-order fragment | PRA, RCA₀, WKL₀ | The maintainer's order: built with the other decision procedures, after WKL₀ is started. |
| Presburger arithmetic (addition only) | PRA, RCA₀, WKL₀ | Same reason as the monadic procedure. |
| Tarski: real closed fields | PRA, RCA₀, WKL₀ | Same reason as the monadic procedure. |
<!-- generated:choice:end -->

Nothing else is held back: any task whose dependencies are met and that is not listed here can start.

### Tasks that moved

The order is a plan, not a contract. When a task moves, it keeps a note of where it was and why:

<!-- generated:moves:start -->
| Task | Before | Why it moved |
|---|---|---|
| Rocq re-check: our own small checker for our certificate format, proved sound in Rocq | Needed pm.mm for ✱1–✱5 and re-checked exported derivation trees. | It now checks the finite core's certificates, so it waits for adequacy stage 2. Existing routes from Lean into Rocq weaken the check (definitional UIP, universe checks switched off), and no verified Metamath checker in Rocq was found, so the checker is our own. |
| (c) A restricted checker for that fragment: first existing verified checkers (con-leche), then our own only if needed | Last, by choice: after Π⁰₂-conservativity and Tarski. | The maintainer's decision: a side task right after the census. Existing verified checkers make its first step small. |
| Lean proves Con(ZFC): existing mechanizations cited and re-checked | Build our own, after Gödel I, by choice. | Mechanizations exist, so citing and re-checking them is small; small, independent work goes early. |
| ZFC with inaccessibles proves Con(Lean's type theory): existing mechanizations cited and re-checked | Build our own, after Gödel I, by choice. | Two mechanizations for actual checkers exist, so citing and re-checking them is small; small, independent work goes early. |
| Cardinal arithmetic (✱100–✱126) agrees with Mathlib's Nat and Cardinal | The first bridge was classes, relations and ✱54·43, after ✱40–✱56. | Bridges start at ✱100, where PM's cardinals start, and go through the collapse model, which already reads function types as Lean function spaces; reading classes there becomes part of this bridge. They live in a separate package that depends on Mathlib, because the core depends on nothing. |
<!-- generated:moves:end -->

### What would change the order

Some findings would bring foundational work forward before more dependent proofs pile up: adequacy
failing for some part of the embedding, or its converse direction turning out to need more than a
restricted form of `QThm`; ✱9's questions (Rep, ✱9·31) staying open; a claim of PM turning out false;
class or relation interfaces that do not fit the later volumes; churn in the checkers or the toolchain. A
claim that fails is a valid result of the audit, not a reason to stop.

## Dependency view

Every task in its group's column, at the level of its longest chain of hard dependencies (level 0 needs
nothing else). A solid arrow points from a task to one that needs it; a dashed arrow, to one placed after
it by choice. The image is large; open it on its own to read it at full size.

![Dependency view: every task, the hard dependencies between them, and the placements by choice](roadmap/deps.svg)

## Incompleteness, consistency and related statements

Each statement below is given with its hypotheses. Where the plan has a task to check one in Lean, it says
so.

**Gödel's first theorem for PM (Gödel–Rosser form).** Let T_H be a specified, effectively axiomatized
theory: the chosen PM calculus, with finite formulas, finite derivations and a decidable proof relation,
together with explicit hypotheses H. If T_H interprets Robinson arithmetic Q and T_H is consistent, then
some sentence is neither provable nor refutable in T_H. For PM's own cardinal numbers, Q's axiom that
successor is injective holds only given the axiom of infinity, so H includes it, as PM's ✱120·03 states it
as a hypothesis. Gödel's original argument draws the same conclusion from the stronger hypothesis of
ω-consistency; a reproduction of that argument states that hypothesis. Gödel's 1931 system P was a
PM-style typed logic with Peano's axioms for the natural numbers, not this repository's encoding. The plan
presents T_H as a many-sorted first-order theory, the finite core, so that an existing library's proofs of
the theorem (stated for first-order theories) can be reused; that library stays in a separate package.

What does not suffice: interpreting PM's formulas in Lean's natural numbers from outside, or adding Peano's
axioms to PM, shows nothing about PM without them; the interpretation's obligations must be proved inside
T_H. The present Lean embedding is not itself an effective presentation (its quantifier constructors take
Lean functions, and its generalization rule has one premise for every variable), which is why adequacy and
the numbering come first. An export that preserves provability does not carry unprovability back to the
embedding, which may prove more.

The theorem is conditional on the consistency of T_H. The finite model in this repository shows the
encoding consistent at the model's variables; it does not establish the consistency of a theory that
includes the axiom of infinity.

**Gödel's second theorem.** Consistency cannot be vouched for from inside: by Gödel's second incompleteness
theorem, a consistent, recursively axiomatized theory that interprets enough arithmetic does not prove its
own consistency. In more detail: if a theory T is consistent and effectively axiomatized, and its standard
provability predicate satisfies the Hilbert–Bernays–Löb derivability conditions (as it does when T
contains, or suitably interprets, enough arithmetic; IΣ₁ suffices), then T does not prove its own
consistency statement Con(T). For PM, the derivability conditions must be proved for T_H's provability
predicate under its interpretation of arithmetic, which needs induction inside T_H; that is why it is a
separate, later task. A consistency proof has to be given in another theory, whose own consistency is then
assumed; those links are documented, not finished. Checking, by contrast, can be repeated side by side by
independent tools, which is where this project spends its effort.

**Checking both ways, and consistency both ways.** Two different things are meant by "checking both
ways", and Gödel separates them:

- **Proofs, both ways: possible.** The same theorem checked in two systems, with proofs translated in each
  direction (Lean ⟷ Metamath, Metamath's set.mm being ZFC). Each direction catches errors the other might
  miss.
- **Consistency, both ways: impossible.** Take two consistent, recursively axiomatized systems that each
  contain enough arithmetic (Peano arithmetic is more than enough). If each proved the other consistent,
  each would prove its own consistency, which the second incompleteness theorem rules out. So between such
  systems a consistency proof can go only one way: Lean proves ZFC consistent (it can build a model of
  ZFC), and in the other direction ZFC with added inaccessible cardinals suffices to prove Lean consistent
  (Carneiro, 2019, builds a model of Lean's type theory there, with inaccessibles for its universes). That
  assumption is sufficient; it is not shown to be necessary.

In more detail: let S and T be effectively axiomatized theories, with T consistent and containing enough
arithmetic for the second theorem and for formalized Σ₁-completeness (IΣ₁ suffices), and S interpreting Q.
If S proves Con(T), then T does not prove Con(S). (T proves the true Σ₁ sentence "S proves Con(T)", and
proves that if T were inconsistent, S would prove that too; so from Con(S), T would derive Con(T).)

**Lean and ZFC.** Lean's type theory, with its standard axioms and universes, can construct a model of ZFC;
with a formal syntax of ZFC and a soundness theorem, this becomes a Lean proof of Con(ZFC). In the other
direction, ZFC together with countably many inaccessible cardinals suffices to build a model of Lean's type
theory, and so to prove it consistent (Carneiro, 2019, for the type theory specified there). That
assumption is sufficient; it is not shown to be necessary. By the previous paragraph, once Lean proves
Con(ZFC), ZFC itself, if consistent, does not prove the consistency of Lean's type theory. Both links are
relative consistency results; neither shows any of these systems consistent outright. Mechanized proofs of
both directions exist (listed with the tasks above), so the tasks cite them, re-check them on a pinned
toolchain, and state exactly what each proves: in which system, from which hypotheses, for which type
theory, and how many universe levels.

A model of Lean's type theory is a model of a calculus; it does not verify the program that checks proofs.
That is the separate work on Lean's kernel, which in turn does not need a ZFC model.

**Lean's kernel.** The whole build is re-checked by external checkers of Lean's kernel (see the Lean Kernel
Arena), one per code family: separately written ones such as nanoda (Rust) or Tenet (.NET), and con-leche,
which has a machine-checked theorem that every environment it accepts has a set model. Lean4Lean (Lean) is also useful, but its own documentation says it follows the C++ kernel
closely and is not really an independent implementation, so it guards less against bugs the two share;
separately written checkers guard more. The plan verifies the kernel in four stages: (a) a census of the
kernel features this project exercises; (b) Lean4Lean run on the build; (c) a re-check by a checker
restricted to that fragment, starting with existing verified checkers and writing our own only if they do
not serve; (d) a formal proof that the checker used is correct against a specification of the fragment, or,
for an existing checker, an audit of its proof and of what it does not cover. Stages (c) and (d) follow the
census directly. What the project does not use (quotient types, `propext`, `Quot.sound`,
`Classical.choice`, Mathlib) is not part of the fragment; the axiom reports already show that no PM
derivation uses these three axioms.

**WKL₀ and PRA.** RCA₀ is the usual base system of reverse mathematics; WKL₀ adds weak König's lemma.
WKL₀ is Π⁰₂-conservative over primitive recursive arithmetic (PRA): every Π⁰₂ sentence of arithmetic that
WKL₀ proves, PRA proves. The result is for Π⁰₂ sentences, not for all sentences.

**The finitist audit.** A tag that records which rules a proof uses shows that this proof uses them; it
shows neither that the assumption is necessary nor that the result is provable in PRA. A PRA claim needs
an arithmetic reading of the statement and a PRA proof or a certified reduction.

**Reducibility, infinity and choice.** PM prints the axioms of reducibility, ✱12·1 and ✱12·11, as
primitive propositions. The axiom of infinity (✱120·03) and the multiplicative axiom (✱88) are not
assumed; PM carries them as hypotheses where they are used, and so does this project. The repository also
makes reducibility an explicit, selectable rule, so that the tags can show which results use it.

**The 1925 edition.** Its new Introduction explores doing without the axiom of reducibility, and Russell
discusses there what is then lost. Appendix B argues for induction without reducibility; steps of its proof
(✱89·12, ✱89·16) are disputed, and the argument is reported to fail as stated. The task is to locate the
step that fails and prove a narrower replacement, not to promise a reconstruction of the whole.

**Decision procedures.** Each produces ordinary PM derivations that the kernel checks, which requires PM
derivations of the fragment's axioms and inference steps. The monadic fragment is defined as a restricted
first-order fragment: variables range over one type of individuals, predicate letters are one-place
predicates of that type, and there is no quantification over functions; "one-place functions" alone would
not delimit it, since PM's language is higher-order. Presburger arithmetic is the first-order theory of
the natural numbers with addition only. Tarski's procedure decides the first-order theory of real closed
fields; it does not decide statements of real analysis in general. Propositional logic already has a
decision procedure in effect: a truth-table test plus the completeness theorem for ✱1–✱5 turns every
tautology into a derivation.

**Mathlib.** The bridges to Mathlib are semantic agreements (PM's notions, read in a model, agree with
Mathlib's), not results about PM's proof system, and they are labelled so. They live in a separate package
that depends on Mathlib; the core depends on nothing.

## What is established

From [PROGRESS.md](PROGRESS.md), [PM_CLAIMS.md](PM_CLAIMS.md), [STAR9_FOUNDATION.md](STAR9_FOUNDATION.md)
and [VERIFICATION.md](VERIFICATION.md):

<!-- generated:established:start -->
- ✱1–✱5: 188 of 188 numbered assertions derived from ✱1·1–✱1·6, and ✱1–✱5 complete for two-valued truth tables.
- Vol I: 460 of 3,230 numbered assertions proved (✱1–✱5 from ✱1·1–✱1·6; from ✱9 on, from the primitive propositions of ✱10's method and ✱12·1, ✱12·11), as counted in docs/PROGRESS.md at commit `27b4f85`. Vols II and III are not started.
- ✱9 by its own method (PM/Found9): 27 of 28 numbered ✱9 propositions proved; ✱9·31 is open under the definitions as printed. Every ✱9 theorem is a ✱10 theorem given a variable of every type; the converse is proved given Rep and a variable of every type.
- Every class and relation expression that PM's notation forms is extensional (pp. 200, 213).
- No PM derivation depends on any Lean axiom; consistency is shown in a finite model, at the model's variables.
- PM's claims, with their status, are in PM_CLAIMS.md. Of the 77 rows: 27 checked (C2 as a schema, D1 for the expressions PM's notation forms); 3 checked for ✱10's method, with ✱9's in progress; 22 partly checked, and 2 more partly checked with the rest in progress; 1 does not hold as stated (B4); 3 assumed; 1 checked for one part and not attempted for the other (A11); 18 not attempted.
- Known limits: no adequacy theorem yet (the formula type has terms that match no finite PM formula, and a `QThm` proof is not a finite object); the models forget orders.
<!-- generated:established:end -->

## Scope

The project formalizes the first edition of *Principia Mathematica* (1910–1913) in Lean, checks PM's
claims about its own system, checks the result with independent tools, and studies the results about PM
listed above; the 1925 second edition follows as a second pass.

Out of scope:

- The halting problem, P versus NP, and any attempt to prove the consistency of PM, Lean or ZFC outright.
  The first is proved unsolvable (Turing, 1936); the third is ruled out by Gödel's second incompleteness
  theorem for any system of the kind stated above; the second is an open problem this project does not
  address. What the project does instead is check proofs, check PM's claims, and record which assumptions
  each result rests on.
- Cryptography, and claims about it.
- New mathematics beyond PM itself: the aim is to check what Whitehead and Russell wrote, not to extend it.
- Rewriting PM separately for each foundation (see "One source, many checkers").
- Lean as a whole: only the kernel fragment this project exercises is verified here, not features or
  library axioms it does not use.

## Maintaining this page

The plan's data is [data/roadmap.json](../data/roadmap.json). After editing it, or after the counts in
PROGRESS.md or PM_CLAIMS.md change, run

```
python3 scripts/roadmap_chart.py          # the charts in docs/roadmap/ and every generated region here and in the README
python3 scripts/check_svg.py docs/roadmap/*.svg   # an independent check of the charts
```

`tests/test_roadmap.py` runs `python3 scripts/roadmap_chart.py --check` and `check_svg.py`, and fails if a
committed chart or generated region differs from what the data gives. The chart script refuses to write a
chart in which two labels overlap or a label leaves its box, and checks that every dependency names an
existing task, that there is no cycle, that every task placed *by choice* really is later than its
dependencies require, that every prior-work entry has an evidence level, and that every move records where
the task was and why. Text between `<!-- generated:… -->` markers is overwritten; edit the rest by hand.
