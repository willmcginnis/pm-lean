# Statement mutation: are statements tied to their proofs and to PM?

A trial (rulings of 2026-10-13: tiered checks; the statement-mutation trial). Its results decide which
parts become standing checks; none is in `tests/run_all.sh` yet.

Lean's kernel checks every proof, so mutating a proof teaches nothing. What a kernel check does not show is
that the statement says what it should. A statement can be weaker than intended (a premise it does not
need, or one its proof never uses) or wrong in a way a proof can still reach. This trial asks two
questions:

- **Is each statement tied to its proof?** Change the statement a little. If the original proof still
  goes through, the proof does not depend on the part that changed.
- **Is each statement tied to PM's text?** For ✱1–✱5 the statements are generated from the transcription
  (`scripts/gen_lean.py`), and `PM/Statements.lean` checks each one with a truth table. A misreading that
  is still a tautology passes that check. The question is whether anything else would catch it.

## What it checks

`scripts/mutation/StatementMutation.lean` is a Lean meta-program over the proof terms.
`scripts/mutation/mutate.py` runs it and does the recompilations.

**Part 1: unused hypotheses (every theorem in the `PM` and `Checks` libraries).** A hypothesis is any one of
these:

- a premise (a binder whose type is a proposition);
- an instance of one of our classes (`[Reducibility S]`, `[Comprehension S]`);
- a variable that occurs nowhere else in the statement, such as ✱10·25's `y`, which only asks for an
  argument to exist.

Typeclass arguments of Lean's own (`Decidable` …) are left out. A hypothesis is *unused* when the proof
term, with the binder instantiated, does not mention it. Two refinements can only turn "used" into
"unused":

- a `have` or `let` whose value is never used does not count;
- neither does an argument passed to another theorem in a position that theorem does not use. This is
  computed for all theorems together, to a fixed point.

The check plants five cases of its own (a plain unused premise, one feeding only a dead `have`, one passed
only to the first, an unused variable, an unused class) and one used premise. It fails unless it flags
exactly those five. Lean's unused-variables linter flags only two of them: the plain premise and the
variable.

**Part 1, recompiled (`--full`).** Each hypothesis of a theorem proved by tactics, and every 25th of the
others, is replaced by `True` (a class argument is removed) in a copy of its source file. The copy is cut
after the theorem and compiled. A tactic proof can find another route where the term analysis sees a use.

**Part 2: statement mutants.** The targets are:

- **✱1–✱5:** every `t…` and `pm2_7…` theorem with a statement `Thm (s… p q …)`, and ✱1·2–✱1·6 against
  `Thm`'s constructors. The definition `s…` is unfolded, and its formula is mutated.
- **✱9–✱21:** the numbered propositions `q…`, `QL.t…` and `F9.f…`.

Each statement gets a fixed family of one-change mutants:

| Operator | What changes |
|---|---|
| `orAnd` | ∨ ↔ ∧ at one node |
| `dropAntecedent` | an implication replaced by its consequent |
| `iffImp` | ≡ → ⊃ at one node (and ≡ₓ → ⊃ₓ) |
| `negate` | one subformula negated |
| `substOcc` | one occurrence of a variable replaced by another of the same type. This is the shape of the ebook's slip in ✱1·4, `q ∨ p` read as `p ∨ p` ([FIDELITY.md](FIDELITY.md)) |
| `swap` | two variables of the same type exchanged throughout: a renaming of a schema, so the same proposition. Kept as a control |

Each mutant gets two results:

- **Does the original proof term check against it?** `Kernel.check` infers the proof's type once, and
  `Kernel.isDefEq` compares it with the mutant.
- **Is it a tautology?** This uses the repository's own test `F.isTaut`, evaluated by the kernel. For
  ✱9–✱21 the test is run on the propositional skeleton: each subformula not built by a connective
  (`(x).φx`, `φx`, …) becomes an atom.

The control for each statement is the unchanged formula, rebuilt the way mutants are. The proof must check
against it. A second seeded case is the ebook's ✱1·4: it must turn up among ✱1·4's mutants, not be a
tautology, and be rejected.

**Part 2, re-elaborated (`--full`, ✱1–✱5).** A proof *term* is tied to its statement almost by
construction. A proof *script* is not: `by decide`, a decision procedure or `complete` would prove any
tautology. So each ✱1–✱5 mutant that is a tautology is compiled with the original proof script, with the
statement's definition `s…` replaced by the mutant. So is every 10th mutant that is not a tautology, and
the unchanged statement as a control.

Only a tautology can have a proof at all, since ✱1–✱5 is sound (`PM.sound`). The tautological mutants are
therefore exactly the ones a proof by decision procedure could still prove.

## Results

Results are from the full run on the commit that adds this page.

**Part 1.** No unused hypotheses: 1134 theorems, 661 hypotheses (459 premises, 174 class arguments, 28
unreferenced variables), and 0 unused, by both the plain and the refined test. The five planted cases
are flagged.

Recompiled: 171 hypotheses were replaced by `True` (151 in tactic proofs, 20 sampled from term proofs),
and none of the copies compiles. A sample of the failures was read, to make sure each fails for the
expected reason inside the theorem.

26 hypotheses cannot be edited in the source, so the term analysis is their only check:

- 11 anonymous premises of an arrow type `A → B`: 7 in `PM/Complete.lean`, 4 in `PM/Found9/Base.lean`;
- 15 hygienic names that a macro generates, in `PM/Found9/Simul.lean`.

**Part 2, against the original proof term.**

| | Statements | Mutants | Tautologies (✱9–✱21: skeleton) | Accepted by the proof term |
|---|---|---|---|---|
| ✱1–✱5 | 198 | 4668 | 1186 | 0 |
| ✱9–✱21 | 517 (293 `q…`, 188 `QL.t…`, 36 `F9.f…`) | 8043 | 1247 | 0 |

Mutants by operator, with the number that are tautologies:

| Operator | ✱1–✱5 mutants | tautologies | ✱9–✱21 mutants | skeleton tautologies |
|---|---|---|---|---|
| `orAnd` | 303 | 77 | 485 | 82 |
| `dropAntecedent` | 371 | 107 | 550 | 103 |
| `iffImp` | 133 | 97 | 367 | 97 |
| `negate` | 1982 | 60 | 3606 | 70 |
| `substOcc` | 1529 | 495 | 2459 | 566 |
| `swap` | 350 | 350 | 576 | 329 |

Every control checks. The seeded ✱1·4 slip is `substOcc q p #1` of ✱1·4: not a tautology, and rejected.

**Part 2, re-elaborated.** All 193 controls compile. Of the 1155 tautological mutants, 14 compile, and none
of the 439 sampled non-tautologies does. The 14 are all `swap`s, in eight natural-deduction proofs: ✱4·7,
✱4·71, ✱4·72, ✱4·78, ✱4·79, ✱5·71, ✱5·74 and ✱5·75 (`PM/Replay2.lean`). These scripts (`ofPf <| by
unfold s…; split_iff; …`) name their hypotheses by position (`hy n`) and name no formula. So they prove the
statement under any renaming of its variables, which is the same proposition. Every other re-elaborated
mutant of the same eight fails.

### Survivors by category

| Category | Meaning | Found |
|---|---|---|
| harmless: PM's own superfluous premise | an unused hypothesis that PM's statement also has (cite the page) | none |
| our transcription weaker or stronger than PM | an unused hypothesis PM does not have, or a mutant accepted because our statement says less than PM's | none |
| a proof that does not use what it claims | an unused hypothesis the docstring or ledger says is used | none |
| decision procedure instead of PM's derivation | a tautological, non-renaming mutant whose proof script still compiles | none |
| equivalent mutant | a renaming (`swap`), or a mutant definitionally equal to the statement | 14, all script-level `swap`s (above) |

Findings that have been examined are listed, with their category, in `scripts/mutation/expected.json`.
Anything else makes the run fail, and so does an entry that `--full` no longer finds.

### What a survivor would mean

- **An unused hypothesis.** The theorem holds without it. Either PM's statement has the premise too
  (harmless; the page should be cited), or our transcription added it (weaker than PM), or a docstring or
  ledger row claims a use the proof does not make.
- **A mutant accepted by the proof term.** The mutant is definitionally equal to the statement: the
  operator produced an equivalent formula, or the statement's definition is looser than it reads.
- **A tautological, non-renaming mutant accepted by the proof script.** The script decides the formula
  rather than following PM's derivation. That is a fidelity question for the proof, not a wrong statement.
- **A non-tautology accepted by anything.** Soundness is broken. This is an alarm.

### What this says about the tie to PM's text

Leaving out the renamings, 836 one-change mutants of ✱1–✱5 are tautologies. A misreading of that shape
would pass `PM/Statements.lean`'s truth-table test. Every one is rejected by the replayed proof, at the
term level and at the script level. The replays follow PM's cited propositions, so such a misreading would
have broken its replay.

What ties the statement to the printed text itself is the generator from `data/vol1.jsonl`. The committed
files are reproduced byte for byte ([scripts/README.md](../scripts/README.md)), but no test checks that.
Mutation cannot check it either.

For ✱9–✱21 the statements are written by hand, with PM's formula quoted in each docstring. This trial
does not compare them with the text.

No fidelity problem was found.

## How to run

```
python3 scripts/mutation/mutate.py --quick   # under 10 s
python3 scripts/mutation/mutate.py --full    # about 9 min on 8 cores (--jobs N)
```

`--quick` runs Part 1 on every theorem, and Part 2 against the proof term for a fixed sample of 13 ✱1–✱5
statements: ✱1·4, ✱1·6, ✱2·06, ✱2·15, ✱2·32, ✱2·74, ✱3·43, ✱3·47, ✱4·22, ✱4·7, ✱4·87, ✱5·32 and ✱5·75.
These are explicit terms and natural-deduction scripts from both replay files, plus the seeded ✱1·4.
Here `F.isTaut` runs as compiled code rather than in the kernel. It is the same definition, and on the
sample it gives the same verdict on all 469 mutants. The run measured 7 s: Part 1 took 4.4 s, the sample
0.2 s, and the rest is Lean's start-up. The sample could grow at little cost.

`--full` runs everything above. It measured 551 s with 8 parallel jobs, on a shared machine:

- the meta-program, 183 s;
- re-elaboration, 60 s;
- hypothesis recompilation, 308 s.

Both modes exit 1 on any finding not in `expected.json`, or if a control, a planted case or the seeded
case fails. Working files go to `.lake/mutation/`.

## Recommendation (for a ruling)

- **Standing in `--quick`**, on the export path before an upload, and possibly in `tests/run_all.sh`:
  Part 1 on every theorem (self-checking through its planted cases) and the 13 sampled statements. It
  takes 7 s, and it fails on a new unused hypothesis.
- **Standing in `--full`**, run locally before an export release: all of Part 2 and the re-elaboration.
  The re-elaboration is the part that can tell a proof by PM's derivation from a proof by decision.
- **Hypothesis recompilation: optional.** It found nothing beyond the term analysis, at about 5 minutes.
  It could be kept for tactic proofs only, or dropped.
- **Separately:** a test that `gen_lean.py` and `gen_quant_lift.py` reproduce `PM/Statements.lean` and
  `PM/QuantLift.lean`. This is the link to PM's text that mutation cannot check.
