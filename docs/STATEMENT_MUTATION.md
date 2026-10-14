# Statement mutation: are statements tied to their proofs and to PM?

A trial (rulings of 2026-10-13: tiered checks; the statement-mutation trial), now standing in two tiers
(the maintainer's ruling on checks: the full suite runs on our own machines, a small fast subset on
time-limited remotes and on the export path). `--quick` is a step of `tests/run_all.sh` and a check an
export must pass before upload; `--full` is part of `scripts/release_check.sh` ([Where it
runs](#where-it-runs)).

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

**Part 1: unused hypotheses (every theorem in the `PM` and `Checks` libraries).** That means every
theorem written in the source, private ones and Prop-valued structure fields included. Lean records a
declaration range for each of these and for nothing it generates itself (equation lemmas, injectivity
and `sizeOf` lemmas, auxiliary proofs …). The check uses that range, not the name, to tell the two
apart, since a theorem of ours may well be called `eq_…`. As a cross-check, every theorem without a
range must carry one of Lean's own marks of a generated declaration (an internal or reserved name, an
auxiliary recursor or matcher, or a lemma attached to a constructor or an inductive type). If any does
not, the run fails.

A hypothesis is any one of these:

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

The check plants seven cases of its own and one used premise, and fails unless it flags exactly those
seven. The seven are:

- a plain unused premise;
- one feeding only a dead `have`;
- one passed only to the first;
- an unused variable;
- an unused class;
- a plain unused premise in a theorem named like an equation lemma (`eq_…`);
- a plain unused premise in a private theorem.

The last two are named the way Lean names what it generates, so they would be lost if generated
declarations were told apart by name. Lean's unused-variables linter flags four of the seven: the three
plain premises and the variable.

**Part 1, recompiled (`--full`).** Each hypothesis of a theorem proved by tactics, and every 25th of the
others, is replaced by `True` (a class argument is removed) in a copy of its source file. The copy is cut
after the theorem and compiled. A tactic proof can find another route where the term analysis sees a use.

**Part 2: statement mutants.** The targets are:

- **✱1–✱5:** every `t…` and `pm2_7…` theorem with a statement `Thm (s… p q …)`, and ✱1·2–✱1·6 against
  `Thm`'s constructors. The definition `s…` is unfolded, and its formula is mutated.
- **From ✱9 on** (✱9–✱25 so far): the numbered propositions `q…`, `QL.t…` and `F9.f…`.

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
- **Is it a tautology?** This uses the repository's own test `F.isTaut`, evaluated by the kernel. From
  ✱9 on the test is run on the propositional skeleton: each subformula not built by a connective
  (`(x).φx`, `φx`, …) becomes an atom.

The control for each statement is the unchanged formula, rebuilt the way mutants are. The proof must check
against it. A second seeded case is the ebook's ✱1·4: it must turn up among ✱1·4's mutants, not be a
tautology, and be rejected.

**Part 2, re-elaborated (`--full`, ✱1–✱5).** A proof *term* is tied to its statement almost by
construction. A proof *script* is not: `by decide`, a decision procedure or `complete` would prove any
tautology. So each ✱1–✱5 mutant that is a tautology is compiled with the original proof script, with the
statement's definition `s…` replaced by the mutant. So is every 10th mutant that is not a tautology, and
the unchanged statement as a control. The primitive propositions ✱1·2–✱1·6 are left out. Their proofs
are `Thm`'s constructors, whose type is the statement itself, and there is no script to re-elaborate.
Their mutants are checked against the proof term only.

Only a tautology can have a proof at all, since ✱1–✱5 is sound (`PM.sound`). The tautological mutants are
therefore exactly the ones a proof by decision procedure could still prove.

## Results

Results are from the full run of 2026-10-14 (`scripts/release_check.sh`), with ✱22, ✱23 and ✱24 included.

**Part 1.** No unused hypotheses: 1389 theorems, 919 hypotheses (494 premises, 390 class arguments, 35
unreferenced variables), and 0 unused, by both the plain and the refined test. The seven planted cases
are flagged. Left out as generated by Lean: 179 theorems, each with one of Lean's marks (101 lemmas of
constructors, 17 of inductive types, 7 equations of auxiliary recursors, 4 reserved equation-lemma names,
50 internal names).

A first version of the check told generated theorems apart by name, and it was wrong both ways. It
left out 22 theorems written in the source: 10 private theorems and 12 Prop-valued structure fields. It
also counted 9 generated ones (`brecOn.eq`, `ofNat_ctorIdx`). It reported 1134 theorems and 661
hypotheses. Before publication, a release review found a handwritten `eq_…` theorem with an unused premise
that the check passed over, and the fix found the rest. None of the 22 has an unused hypothesis.

Recompiled: 186 hypotheses were replaced by `True` (156 in tactic proofs, 30 sampled from term proofs),
and none of the copies compiles. A sample of the failures was read, to make sure each fails for the
expected reason inside the theorem.

26 hypotheses cannot be edited in the source, so the term analysis is their only check:

- 11 anonymous premises of an arrow type `A → B`: 7 in `PM/Complete.lean`, 4 in `PM/Found9/Base.lean`;
- 15 hygienic names that a macro generates, in `PM/Found9/Simul.lean`.

**Part 2, against the original proof term.**

| | Statements | Mutants | Tautologies (from ✱9 on: skeleton) | Accepted by the proof term |
|---|---|---|---|---|
| ✱1–✱5 | 198 | 4668 | 1186 | 0 |
| ✱9–✱24 | 731 (507 `q…`, 188 `QL.t…`, 36 `F9.f…`) | 10790 | 1273 | 0 |

Mutants by operator, with the number that are tautologies:

| Operator | ✱1–✱5 mutants | tautologies | ✱9–✱24 mutants | skeleton tautologies |
|---|---|---|---|---|
| `orAnd` | 303 | 77 | 547 | 82 |
| `dropAntecedent` | 371 | 107 | 617 | 103 |
| `iffImp` | 133 | 97 | 441 | 97 |
| `negate` | 1982 | 60 | 4253 | 70 |
| `substOcc` | 1529 | 495 | 4022 | 592 |
| `swap` | 350 | 350 | 910 | 329 |

Every control checks. The seeded ✱1·4 slip is `substOcc q p #1` of ✱1·4: not a tautology, and rejected.

**Part 2, re-elaborated.** All 193 controls compile. Of the 1155 tautological mutants, 14 compile, and none
of the 439 sampled non-tautologies does. The 14 are all `swap`s, in eight natural-deduction proofs: ✱4·7,
✱4·71, ✱4·72, ✱4·78, ✱4·79, ✱5·71, ✱5·74 and ✱5·75 (`PM/Replay2.lean`). These scripts (`ofPf <| by
unfold s…; split_iff; …`) name their hypotheses by position (`hy n`) and name no formula. So they prove the
statement under any renaming of its variables, which is the same proposition. Every other re-elaborated
mutant of the same eight fails.

Not re-elaborated: the 31 tautological mutants of the primitive propositions ✱1·2–✱1·6 (23 of them not
renamings). These propositions are `Thm`'s constructors and have no script. The 1155 and the 31 make up
all 1186 tautological mutants of ✱1–✱5.

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
would pass `PM/Statements.lean`'s truth-table test. Every one is rejected by the proof term. For the 813
mutants of statements proved in the replay files, the proof script rejects them too. The replays follow
PM's cited propositions, so such a misreading would have broken its replay.

The other 23 are mutants of the primitive propositions ✱1·2–✱1·6. They have no script, so the term
check is their only check here. That check ties each constructor to the definition `s1_…` it is declared
with, and to nothing more: no replay derives a primitive proposition.

What ties the statement to the printed text itself is the generator from `data/vol1.jsonl`. Mutation
cannot check that. `tests/test_regeneration.py` does: it runs the generators in a scratch copy and
requires `PM/Statements.lean`, `PM/QuantLift.lean` and every other generated file to come out byte for
byte as committed. It fails on a line added by hand to any of them, and on a formula of `data/vol1.jsonl`
changed without regenerating.

From ✱9 on the statements are written by hand, with PM's formula quoted in each docstring. This trial
does not compare them with the text.

No fidelity problem was found.

## How to run

```
python3 scripts/mutation/mutate.py --quick   # about 10 s idle, under a minute loaded; in tests/run_all.sh
python3 scripts/mutation/mutate.py --full    # tens of minutes on 8 cores (--jobs N); in scripts/release_check.sh
```

Both modes first run `lake build` on the modules the meta-program imports (`PM`, `Checks.PinnedStatements`).
The meta-program reads proofs from the build, so without that step a run after an edit would analyse the
proofs as they were at the last build. On an up-to-date tree the step takes about a second. If the build
fails, the run stops before analysing anything. `tests/test_statement_mutation.py` checks this order
without running Lean. To check it end to end, append the following to `PM/Derived.lean` and run `--quick`
without building first:

```
theorem eq_self_with_premise (n : Nat) (h : True) : n = n := rfl
```

The run rebuilds `PM/Derived.lean`, reports `eq_self_with_premise:h` as a NEW unused hypothesis, and
exits 1. Remove the line afterwards.

`--quick` runs Part 1 on every theorem, and Part 2 against the proof term for a fixed sample of 13 ✱1–✱5
statements: ✱1·4, ✱1·6, ✱2·06, ✱2·15, ✱2·32, ✱2·74, ✱3·43, ✱3·47, ✱4·22, ✱4·7, ✱4·87, ✱5·32 and ✱5·75.
These are explicit terms and natural-deduction scripts from both replay files, plus the seeded ✱1·4.
Here `F.isTaut` runs as compiled code rather than in the kernel. It is the same definition, and on the
sample it gives the same verdict on all 469 mutants. The run measured 8 s: Part 1 took 4.6 s, the sample
0.2 s, the build step under a second, and the rest is Lean's start-up. The sample could grow at little cost.

`--full` runs everything above. With ✱22–✱24 it measured 1708 s with 8 parallel jobs, on a machine
shared with other jobs (before ✱22–✱24, 524 s on a less loaded machine):

- the meta-program, 1277 s: Part 1 5 s, the ✱1–✱5 statements 63 s, the statements from ✱9 on 1206 s
  (175 s for the whole meta-program before);
- re-elaboration, 74 s (54 s);
- hypothesis recompilation, 356 s (295 s).

Both modes exit 1 on any finding not in `expected.json`, or if a control, a planted case or the seeded
case fails. Working files go to `.lake/mutation/`.

## Where it runs

The trial ended with a recommendation. The maintainer's ruling on checks settles where each tier runs:
long checks on our own machines, a small, fast subset on time-limited remotes and on the export path.
What is wired now:

- **`--quick` is standing**, in two places.
  - It is a step of `tests/run_all.sh`, so it runs on every push in CI. It covers
    Part 1 on every theorem (self-checking through its planted cases) and the 13 sampled statements, and
    it fails on a new unused hypothesis. It measured 8 s on an idle machine and 30–40 s on a loaded
    shared one, nearly all of it in the build step and Lean's start-up.
  - It is check 0 of `scripts/prove2me/verify.py`, the checks an export must pass before upload
    ([scripts/prove2me/README.md](../scripts/prove2me/README.md)). It runs on the copy of the commit
    exported, built with the platform's Lean v4.33.1, with that commit's own tool. It gives the same
    counts there as with the repository's Lean, and it fails on the planted unused hypothesis above. A
    commit older than the tool fails the check rather than skipping it, unless `--no-mutation` is given
    (for re-checking such a commit, for example the 1.0.0 export). Then the report records that the check
    was skipped and why, and for a commit that has the tool the option fails the check.
- **`--full` runs before a release**, in `scripts/release_check.sh`, with the other long checks
  ([VERIFICATION.md](VERIFICATION.md#before-a-release)). That means all of Part 2 and the
  re-elaboration. The re-elaboration is the part that can tell a proof by PM's derivation from a proof by
  decision.
- **Hypothesis recompilation is still part of `--full`.** The recommendation called it optional: it
  found nothing beyond the term analysis, at 5 to 8 minutes (356 s in the last run). Keeping it for tactic proofs only, or
  dropping it, awaits a ruling. Until then it stays in, since it costs only time on our own machines.
- **The link to PM's text** that mutation cannot check is now `tests/test_regeneration.py`, a test in
  `tests/run_all.sh` ([above](#what-this-says-about-the-tie-to-pms-text)).
