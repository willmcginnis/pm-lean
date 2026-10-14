# Design principles

The standing principles of this project. Each was first stated in a design note or decision, linked below;
this page collects them. When a choice is not settled by them, it is put to the maintainer and recorded in
the decisions log ([TYPES_DESIGN.md](TYPES_DESIGN.md) §5).

## 1. Faithful to the 1910 print, with page citations

The text formalized is the first edition of *Principia Mathematica* (Vol. I, 1910), not the 1925 second
edition. Every design choice that rests on PM cites the page of the 1910 print that warrants it.

- Statements are read from the print, through the Gutenberg transcription checked against scans of the print
  by the companion text audit. Where the transcription and the print differ, the print is followed and the
  difference is reported (✱1·4, ✱4·42, ✱23·02; [FIDELITY.md](FIDELITY.md)).
- Proofs follow PM's own: one Lean line per line of a *Dem.*, or one step per proposition of a bracketed
  hint. What a proof needs beyond that is recorded, not silently supplied ([FIDELITY.md](FIDELITY.md)).
- Apparent slips in the print itself are reported, not corrected in silence ([FIDELITY.md](FIDELITY.md)).
- Pages are cited as `p. 194` or `pp. 194–195` ([CONTRIBUTING.md](../CONTRIBUTING.md)).

## 2. Explicit is better than implicit

Nothing a proof relies on is left for the reader to infer. Where a structural step recurs, it is folded into
a named lemma or a `calc` chain, so that it is stated once and visible wherever it is used, not hidden.

- Every PM proposition a proof uses is listed in its ledger row: PM's citations, the steps PM leaves tacit
  (named in each row and in the file headers), glue, and every other proposition with the reason.
  `Checks/LedgerCheck.lean` checks this against the proof terms ([FIDELITY.md](FIDELITY.md)).
- Displayed chains are `calc` blocks, one line per PM line, joined by `Trans` instances proved once
  (`PM/Chain.lean`). Each layer of eliminating a class of classes is one named lemma
  ([CLASSES_OF_CLASSES.md](CLASSES_OF_CLASSES.md)).
- Where an option is explicit and another implicit, the explicit one is taken: classes of classes are built
  as printed, not by typical ambiguity (decision Q6), and a step that the tacit pattern of pp. 161–162 does
  not cover is listed in the row, not added to the pattern.

## 3. Open choices are built both ways, and both must pass

Where PM's text admits two readings and the maintainer has not chosen between them, both are built, and every
theorem is required to pass under each.

- "Predicative" has two definitions (p. 56 and p. 172), and a real function variable's order two readings
  (p. 55 and p. 54). They make four styles; every PM proposition is checked under all four
  (`StyleCheck.lean`), consistency is proved for each, and `styles_equiv` shows that with reducibility they
  derive the same theorems ([TYPES_DESIGN.md](TYPES_DESIGN.md), decisions 3 and 5; §5, Q1 and Q3). The two
  definitions do not pick out the same functions ([PM_CLAIMS.md](PM_CLAIMS.md), B4).
- When the maintainer decides, the decision and its date go into the decisions log, and the options that
  were weighed stay recorded there.

## 4. Every rule a proof uses is visible

A reader can tell from a theorem which of PM's rules its proof uses, and nothing else is assumed.

- PM's primitive propositions are the rules of an embedded proof system, not Lean axioms. There is no `sorry`,
  no `native_decide` and no added axiom, and every PM theorem reports "does not depend on any axioms"
  ([VERIFICATION.md](VERIFICATION.md)).
- The rules beyond ✱1–✱11, the axiom of reducibility and comprehension, are opt-in: a theorem that uses one
  takes its class in its signature, and `RedCheck.lean` checks the signatures against the proofs.
  Comprehension, which no numbered PM proposition uses, is kept and "marked for what it is for"
  ([TYPES_DESIGN.md](TYPES_DESIGN.md), decision 13; §5, Q2).

## 5. Check PM's claims

Added 2026-10-12 (maintainer).

When PM asserts something about its own system (that two methods are equivalent, that proofs carry over "by
merely repeating previous proofs", that one hierarchy "can be derived" from another, that a construction
"covers all the cases"), we treat the assertion as a theorem to check in Lean, not an assumption to adopt.
Each such claim is listed in [PM_CLAIMS.md](PM_CLAIMS.md) with its page and status.

- A claim that is built into the formalization rather than proved is marked **assumed**, with the reason
  (for example, PM's extension of the axiom of reducibility to functions of functions is built in: ✱12·1
  is a rule at every type).
- A claim the formalization cannot yet reach is marked **not attempted**, not quietly adopted.
- A claim shown to fail is marked **does not hold as stated**, with what holds instead (for example, PM's
  two definitions of "predicative", p. 56 and p. 172, disagree on (y) . ψ(x, y), a first-order function of x;
  with reducibility they still derive the same theorems).

## 6. Search prior work first

Added 2026-10-12 (maintainer).

Before any task is started, and as the first step of every task, prior work is searched in depth: existing
formalizations (Lean, Rocq/Coq, Isabelle, HOL, Metamath, Mizar, Agda), papers, theses, talks and
repositories. Several independent search tools are used and their findings compared. An earlier search
found a formalization of PM that had gone much further than expected.

- The purposes: to save work, to get ideas, to learn early whether a task is easy, hard or a dead end, and
  to have independent work to check ours against.
- Findings are recorded per task, in [ROADMAP.md](ROADMAP.md): what exists, how far it got, its license,
  whether it can be reused, and how well each finding is established (measured from the source, documented
  in a paper or README, or unverified). "Not found" means not found by the searches so far.
- Code is never copied from unlicensed repositories; ideas only.
- The searches are cheap and independent of each other, so they run ahead of the work they inform.

## 7. The order is a plan, not a contract

Added 2026-10-12 (maintainer).

Work moves when it fits better elsewhere or costs little, and the reason is recorded.

- A task that is small, or independent of the rest, is done early rather than in its place in the plan.
- A task placed later than its dependencies require is marked *by choice*, with the reason, so that a
  choice is not mistaken for a dependency.
- When a task moves, [ROADMAP.md](ROADMAP.md) records where it was and why
  ([data/roadmap.json](../data/roadmap.json), field `moved`).
