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

## Measured code

The figures below of the comparison on normal forms (the latest full run, the side-by-side check, the
times by chapter, and `--quick` by both methods) were measured on 2026-10-14 on the Lean code and
scripts of commit `10fb7d0`, the audit of every subterm included. The full run and the first part of
the side-by-side check finished that day; its other two parts, and `--quick` by both methods, after
midnight, on 2026-10-15. The earlier full run, which compared by `direct`, is that of the Lean code and
scripts of `07f82e0`.

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
  the kernel's `Kernel.isDefEq` compares it with the mutant, after both are brought to normal form by
  the kernel's own reductions ([below](#how-a-mutant-is-compared)).
- **Is it a tautology?** This uses the repository's own test `F.isTaut`, evaluated by the kernel. From
  ✱9 on the test is run on the propositional skeleton: each subformula not built by a connective
  (`(x).φx`, `φx`, …) becomes an atom.

The control for each statement is the unchanged formula, rebuilt the way mutants are. The proof must check
against it. A second seeded case is the ebook's ✱1·4: it must turn up among ✱1·4's mutants, not be a
tautology, and be rejected.

### How a mutant is compared

The question for each mutant is whether the proof's type and the mutant are definitionally equal. The
kernel decides it. There are two ways to ask it (`--method`; `normal` is the default):

- **`direct`**: `Kernel.isDefEq` on the two terms as they are, the tool's only method until 2026-10-14. On
  the class and relation statements of ✱22–✱25 it is slow and memory-hungry: the statement and the
  mutant differ at one place deep inside nested definitions, and the kernel's lazy unfolding tries
  many unfoldings before it concludes "not equal". The full run with ✱25 that compared this way, on the
  Lean code of `07f82e0`, took 9142 s, 8519 s of it in these comparisons, and `/usr/bin/time` reported a
  maximum resident set of about 22 GiB (MEASURED, 2026-10-14; [below](#how-to-run)). ✱25·431 alone
  spent 3452 s comparing its 24 mutants.
- **`normal`**: each term is first brought to its normal form, and `Kernel.isDefEq` compares the two
  normal forms. The normal form is computed by the kernel's own `Kernel.whnf`, applied at the root and
  then, recursively, in every argument, under every binder (with a fresh local variable, abstracted
  again afterwards) and in every binder type. The work is memoized for each statement: a subterm met
  again, such as a definition's parameter used twice, is normalized once, and equal results are kept
  as one shared copy. The proof's type is normalized once for all of its mutants.

**Why the verdicts should be the same, and how far this is shown.**

1. Every step replaces a subterm by its weak head normal form, which the kernel reaches from it by its
   own reductions: β, δ, ι (with the K-like rule, and eta for structures on a recursor's major
   premise), ζ, projections, quotients, and the rules for Nat and String literals. So the two are
   definitionally equal. Definitional equality is a congruence (it holds under application and under
   binders), so each normal form is definitionally equal to its term.
2. If definitional equality were transitive on the four terms (the proof's type, the mutant, and their
   normal forms), the proof's type would equal the mutant exactly when their normal forms are equal.
   The kernel decides both questions, so it would give both the same verdict.

Lean's definitional equality is not transitive in general. These are the rules of its kernel (v4.34.1,
`src/kernel/type_checker.cpp` and `src/kernel/inductive.h`) that can break transitivity, or that
compare anything but the two trees, and what each needs in the terms compared:

| Rule (kernel function) | What it does | Needs, in the terms compared |
|---|---|---|
| proof irrelevance (`is_def_eq_proof_irrel`) | any two proofs of the same proposition are equal | a proof: a term whose type is a proposition |
| K-like reduction (`to_cnstr_when_K`) | a recursor of `Eq` (or any K-like type) computes on any proof of `a = a`, not only on `Eq.refl a` | a proof: the recursor's major premise (K-like types are propositions) |
| eta for structures (`try_eta_struct`) | `S.mk t.1 … t.n` equals `t` | an application of the constructor of a structure (one constructor, no indices, not recursive) |
| eta for unit-like types (`is_def_eq_unit_like`) | any two terms of a structure with no fields are equal | a term of a unit-like type, or, after eta for functions, a function into one |
| string literals (`try_string_lit_expansion`) | a literal equals `String`'s constructor applied to its contents | an application of `String`'s constructor, a structure's constructor |

The kernel's other rules are eta for functions, universe levels up to normalization, a Nat literal
against `Nat.zero` and `Nat.succ` (`is_def_eq_offset`), the Nat operations on literals (`reduce_nat`),
the shortcut that reduces a closed term compared with `Bool.true`, and lazy unfolding. Each identifies a
term with one it reduces to, or decides by the same reductions `nf` performs. None is known to break
transitivity, and the argument assumes that none does.

The audit once missed a case. A release review found this witness, now one of the planted cases
(`PMNfTest` in `scripts/mutation/StatementMutation.lean`):

```
def accRel (_ _ : Nat) : Prop := False
structure ProofBox : Type where
  proof : Acc accRel 0
noncomputable def pick (h : Acc accRel 0) : Nat :=
  @Acc.rec Nat accRel (fun _ _ => Nat) (fun _ _ _ => 0) 0 h
def witnessLeft : Prop := ∀ b : ProofBox, pick b.proof = 0
def witnessRight : Prop := ∀ _b : ProofBox, pick (Acc.intro 0 (fun _ h => False.elim h)) = 0
```

`direct` says the two are equal: it unfolds `pick` on both sides, and the two proofs of `Acc accRel 0`
are equal by proof irrelevance. Their normal forms are not equal: the recursor on `b.proof`, a stuck
projection, does not compute, and the one on `Acc.intro` computes `0`. So `pick b.proof ≡ pick
(Acc.intro …)` by proof irrelevance and `pick (Acc.intro …) ≡ 0` by ι, but `pick b.proof ≢ 0`. The
audit then checked only the heads of applications and the constants and variables standing alone. The
proof `b.proof` is a projection, so the audit was clean, and the comparison on normal forms would have
said "not equal" where `direct` says "equal". With the audit bypassed the two comparisons still
disagree on it; with the audit, it flags the projection, `direct` decides, and they agree.

So the run checks the normal forms for what the table needs:

- **The audit.** Every subterm of both normal forms is checked, each distinct subterm once. Is it a
  proof, that is, is its type a proposition (the level of the type's sort zero up to normalization, as
  the kernel's `is_prop` tests it)? Is its type a unit-like type, or, under its `∀`s, the type of a
  function into one? Is it an application of a constructor of a structure? By the constructor of
  `Expr` a subterm has after `Kernel.whnf`:
  - an application (`app`): the application and its head are checked. The head is a constructor, a
    variable, a constant without a definition (an inductive type, an axiom, a stuck recursor) or a stuck
    projection. A projection's structure argument and every argument are normalized and checked in turn;
  - a function (`lam`): checked; its binder type and its body (under a fresh variable) in turn;
  - a projection (`proj`), stuck because its structure argument is not a constructor application:
    checked, the projection itself and then its structure argument;
  - a constant (`const`), a variable (`fvar`), a literal (`lit`): checked;
  - a `∀` (`forallE`) and a sort (`sort`): types, whose type is a sort, so neither a proof nor
    unit-like nor an application; their binder types and bodies are checked;
  - metadata (`mdata`) and `let` (`letE`): `Kernel.whnf` removes metadata and reduces a `let` at the
    root, so neither survives; a loose bound variable (`bvar`) or a metavariable (`mvar`) cannot occur
    in a closed term opened with fresh variables. If one were met, the comparison would fall back.
- **The response.** If anything in a statement's normal forms is flagged, every comparison of that
  statement is decided by `direct` instead, and the normal forms of its remaining mutants are not
  computed. Such a finding costs time, never the verdict.
- **What the audit shows, and what it does not.** With a clean audit the two normal forms contain
  nothing the table needs, at any position, and every subterm is in weak head normal form. So the
  kernel's comparison of the two normal forms takes the trees apart in step and compares them as
  trees, up to the other rules above. Two things are not shown. First, that a proof, a constructor or a
  unit-like term that `direct` meets only inside a reduction that removes it from both normal forms
  (an ι step or a projection taken on both sides) cannot change `direct`'s verdict. Second, that the
  kernel's algorithm finds every equality of its own relation; both methods rely on it. So this is a
  conservative syntactic check with a fallback, not a proof of transitivity. The side-by-side check
  below is the evidence for the rest.
- **The result** (MEASURED, the full run under [How to run](#how-to-run), [measured
  code](#measured-code)). Nothing is flagged from ✱10 on, nor in ✱1–✱5, among 1,767,312 subterms
  checked. The 36 statements of ✱9 (`F9.f…`, PM/Found9/Star9.lean) are flagged: their normal forms
  contain `Reading.mk` (a reading of ✱9 is a structure) and `PProd.mk` and `PUnit.unit` (from Lean's
  compilation of the recursive definitions they unfold to). No proof is flagged anywhere. All 488 of
  their mutants, and 34 of their 36 controls, are decided by `direct`, which takes 0.3 s for them.
- **The planted cases.** The run fails unless the audit flags a proof (`rfl`, which normalizes to
  `Eq.refl`), a structure constructor (`Subtype.mk`), a unit-like term (`PUnit.unit`), the witness's
  projection `b.proof` as a proof, and a projection of a unit-like type (`PMNfTest.unitProjection`), and
  unless the comparison of the witness takes `direct`'s verdict. The run records the witness (record
  `selfTest`: `direct` true, the normal forms with the audit bypassed false, the projection flagged, the
  verdict true), the report prints it, and `tests/test_statement_mutation.py` pins the record. A copy of
  the tool whose audit leaves out projections fails on the witness (checked 2026-10-14).

**The bound.** A comparison also falls back to `direct` in two other cases. One is a normal form that
needs more than 200,000 steps, where a step is a call of `Kernel.whnf` on a term not met before in the
statement. The other is a kernel error. No verdict therefore depends on the bound. The bound counts
steps rather than seconds, so the fallbacks are the same from run to run. The largest normal form of
the full run needs 968 steps (✱25·491), and no comparison reaches the bound. A planted case checks that a
bound of three steps stops a term needing more. `PM_MUTATION_NF_BUDGET` sets another bound.

**The check that the verdicts are the same** (MEASURED, on the Lean code and scripts of `10fb7d0`, the
code of the full run under [How to run](#how-to-run); [measured code](#measured-code)).
`mutate.py --compare-methods` runs both methods on every mutant and records both verdicts. It fails if
they differ anywhere. It ran in three parts:

| Statements | Mutants | Disagreements | Decided by `direct` (audit) | `direct` | `normal` | Memory |
|---|---|---|---|---|---|---|
| ✱1–✱22 (787 statements) | 13,556 | 0 | 522 (✱9) | 70.3 s | 28.2 s | 1.43 GiB |
| ✱23–✱24 (142) | 1,902 | 0 | 0 | 945.8 s | 115.5 s | 5.36 GiB |
| ✱25, all but ✱25·431 and ✱25·432 (68) | 1,006 | 0 | 0 | 755.9 s | 126.1 s | 3.20 GiB |

The columns `direct` and `normal` give each method's comparison time in the same run, `normal` with the
audit of every subterm; memory is the run's maximum resident set (`/usr/bin/time -v`), nearly all of it
`direct`'s. The controls agree too. All of ✱1–✱24 was compared: 929 statements and 15,458 mutants.
✱25·431 and ✱25·432 were left out of this check (`--skip`) because `direct` takes about an hour on each.

They are covered by the records of the two full runs instead. One is the earlier full run on the Lean
code and scripts of `07f82e0`, which compared by `direct`. The other is the full run by `normal` on
`10fb7d0` described under [How to run](#how-to-run). The two give the same verdict on every mutant:
16,512 mutants of 999 statements, the 48 of ✱25·431 and ✱25·432 among them. They also agree on every
control, every tautology result and every printed mutant. Their records differ only in Part 1: the
later run has the 30 hypotheses of the check theorems, and three hypotheses whose types changed with
ruling 64 ([Results](#results)).

Every mutant compared in these checks is rejected by both methods, and every control is accepted by
both. So the agreement on "accepted" rests on the 999 controls, since no mutant is accepted.

`tests/test_statement_mutation.py` reruns the side-by-side check on a fixed sample of 16 statements, one
from each module with mutants (about 20 s). That test is part of `tests/run_all.sh`.

**Time by chapter** (MEASURED, [measured code](#measured-code)). The time spent comparing, normal forms
and their audit included:

| | `direct` | `normal` |
|---|---|---|
| ✱22 | 69 s | 11.3 s |
| ✱23 | 262 s | 14.0 s |
| ✱24 | 683 s | 101.6 s |
| ✱25, all but ✱25·431 and ✱25·432 | 756 s | 126.1 s |
| ✱25·431 | 3452 s | 1.7 s |
| ✱25·432 | 3282 s | 1.8 s |

The rows for ✱22–✱25 come from the side-by-side check above. Those for ✱25·431 and ✱25·432 come from
the records of the two full runs, `direct` from the earlier one (Lean code and scripts of `07f82e0`) and
`normal` from the latest (`10fb7d0`). Most of `normal`'s time is now the audit, which infers the type of
every subterm of every normal form: before the audit covered every subterm (code of `6aba237`, the same
day), the comparisons of the full run took 45 s in all, against 276 s now. In the latest full run the
statements from ✱9 on spent 274 s in their comparisons and 151 s in the tautology test (`F.isTaut` in
the kernel).

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

Results are from the latest full run (`mutate.py --full`, 2026-10-14, on the Lean code and scripts of
`10fb7d0`; [measured code](#measured-code)), comparing on normal forms, with ✱1–✱25 included. It ran to
completion and exited 0: "statement mutation: no unexpected finding". It took 14 min 59 s with 8 jobs
([below](#how-to-run)). The earlier full run, which compared by `direct` on the Lean code and scripts of
`07f82e0`, found the same in Part 2 and in the re-elaboration, record for record; in Part 1 it counted
fewer theorems and recompiled a slightly different set of hypotheses (below).

**Part 1.** No unused hypotheses: 1784 theorems, 1039 hypotheses (520 premises, 478 class arguments, 41
unreferenced variables), and 0 unused, by both the plain and the refined test. The 313 check theorems are
among them; they were `example`s in the earlier run, which counted 1471 theorems and 1009 hypotheses, the
30 more hypotheses being those of the check theorems. The seven planted cases are flagged. Left out as
generated by Lean: 183 theorems, each with one of Lean's marks (101 lemmas of constructors, 17 of
inductive types, 7 equations of auxiliary recursors, 4 reserved equation-lemma names, 54 internal names).

A first version of the check told generated theorems apart by name, and it was wrong both ways. It
left out 22 theorems written in the source: 10 private theorems and 12 Prop-valued structure fields. It
also counted 9 generated ones (`brecOn.eq`, `ofNat_ctorIdx`). It reported 1134 theorems and 661
hypotheses. Before publication, a release review found a handwritten `eq_…` theorem with an unused premise
that the check passed over, and the fix found the rest. None of the 22 has an unused hypothesis.

Recompiled: 188 hypotheses were replaced by `True` (153 in tactic proofs, 35 sampled from term proofs),
and none of the copies compiles. In an earlier run a sample of the failures was read, to make sure each
fails for the expected reason inside the theorem. The earlier full run recompiled 190 (158 and 32): five
hypotheses of `PM.Pf.hy`, `qclsEqCongr` and `qrelEqCongr` counted as in tactic proofs while their premise
was filled in by a tactic (`:= by …`), which it no longer is ([KERNEL_CENSUS.md](KERNEL_CENSUS.md)), and
the longer list of term-proof hypotheses moves the every-25th sample.

26 of the hypotheses chosen cannot be edited in the source, so the term analysis is their only check:

- 11 anonymous premises of an arrow type `A → B`: 7 in `PM/Complete.lean`, 4 in `PM/Found9/Base.lean`;
- 15 hygienic names that a macro generates, in `PM/Found9/Simul.lean`.

The earlier run's sample also took the structure argument `self` of a Prop-valued field,
`PM.F9.Rep.assoc` in `PM/Found9/FromStar10.lean`, which cannot be edited either (27 in all).

**Part 2, against the original proof term.**

| | Statements | Mutants | Tautologies (from ✱9 on: skeleton) | Accepted by the proof term |
|---|---|---|---|---|
| ✱1–✱5 | 198 | 4668 | 1186 | 0 |
| ✱9–✱25 | 801 (577 `q…`, 188 `QL.t…`, 36 `F9.f…`) | 11844 | 1275 | 0 |

Mutants by operator, with the number that are tautologies:

| Operator | ✱1–✱5 mutants | tautologies | ✱9–✱25 mutants | skeleton tautologies |
|---|---|---|---|---|
| `orAnd` | 303 | 77 | 577 | 82 |
| `dropAntecedent` | 371 | 107 | 645 | 103 |
| `iffImp` | 133 | 97 | 473 | 97 |
| `negate` | 1982 | 60 | 4514 | 70 |
| `substOcc` | 1529 | 495 | 4619 | 594 |
| `swap` | 350 | 350 | 1016 | 329 |

Every control checks. The seeded ✱1·4 slip is `substOcc q p #1` of ✱1·4: not a tautology, and rejected.

**Part 2, re-elaborated.** All 193 controls compile. Of the 1155 tautological mutants, 14 compile, and none
of the 439 sampled non-tautologies does. The 14 are all `swap`s, in eight natural-deduction proofs: ✱4·7,
✱4·71, ✱4·72, ✱4·78, ✱4·79, ✱5·71, ✱5·74 and ✱5·75 (`PM/Replay2.lean`). These scripts (`ofPf <| by
unfold s…; split_iff; …`) name their hypotheses by position (`hy n rfl`) and name no formula. So they prove the
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
python3 scripts/mutation/mutate.py --full    # about 15 minutes with 8 jobs, see below (--jobs N); in scripts/release_check.sh
python3 scripts/mutation/mutate.py --compare-methods [--modules M,…] [--only D,…] [--skip D,…]
```

`--method direct` makes `--quick` or `--full` compare the old way ([How a mutant is
compared](#how-a-mutant-is-compared)). `--compare-methods` runs Part 2 with both comparisons on every
mutant and exits 1 if they differ anywhere. It runs on all of Part 2 or on the given modules or
declarations, and it takes as long as `direct` does (see the table there).

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

`--quick` runs Part 1 on every theorem (on the current tree 1784 theorems, the 313 check theorems
included, and 1039 hypotheses: 520 premises, 478 class arguments, 41 unreferenced variables; 0 unused),
and Part 2 against the proof term for a fixed sample of 13 ✱1–✱5 statements: ✱1·4, ✱1·6, ✱2·06, ✱2·15, ✱2·32, ✱2·74, ✱3·43, ✱3·47, ✱4·22, ✱4·7, ✱4·87, ✱5·32 and ✱5·75.
These are explicit terms and natural-deduction scripts from both replay files, plus the seeded ✱1·4.
Here `F.isTaut` runs as compiled code rather than in the kernel. It is the same definition, and on the
sample it gives the same verdict on all 469 mutants. The run measured 8 s: Part 1 took 4.6 s, the sample
0.2 s, the build step under a second, and the rest is Lean's start-up. The sample could grow at little cost.
With the comparison by normal forms the output of `--quick` is unchanged: run with `--method normal` and
with `--method direct`, it gives the same 1523 records apart from the fields that record the method, the
times and the fallbacks (10 s and 9 s; [measured code](#measured-code)).

`--full` runs everything above. With ✱1–✱25, comparing on normal forms, it measured 899 s, 14 min 59 s,
with `--jobs 8` (the default on an 8-core machine; [measured code](#measured-code)). These are the
figures of one run, not a bound:

- the meta-program, 531 s: Part 1 5 s, the ✱1–✱5 statements 65 s, the statements from ✱9 on 455 s;
- re-elaboration, 60 s;
- hypothesis recompilation, 308 s.

The kernel's comparisons of each proof's type with its mutants, normal forms and their audit included,
took 276 s (3 s for ✱1–✱5, 274 s from ✱9 on), and the tautology tests 200 s (49 s and 151 s). The
meta-program is a single process; `--jobs` applies only to the recompilations. For the whole run
`/usr/bin/time -v` reported a maximum resident set of 1,551,856 kB (about 1.48 GiB) and 370% CPU.
Before the audit covered every subterm, the same run on the code of `6aba237` measured 979 s, of which
360 s in the meta-program and 45 s in the comparisons, and 1,204,916 kB.

The earlier full run compared by `direct` ([How a mutant is compared](#how-a-mutant-is-compared)). With
✱1–✱25 it measured 9142 s, 2 h 32 min, on 2026-10-14, on the Lean code and scripts of commit `07f82e0`.
The machine was shared with other jobs for part of the run, so the figures are those of one run, not a
bound:

- the meta-program, 8763 s: Part 1 5 s, the ✱1–✱5 statements 64 s, the statements from ✱9 on 8691 s
  (99% of the meta-program);
- re-elaboration, 72 s;
- hypothesis recompilation, 307 s.

Nearly all of that time went to the kernel's definitional-equality comparisons of each proof's type with
its mutants (`Kernel.isDefEq`): 8519 s, 97% of the meta-program. That time grows steeply with the nesting
of the class and relation definitions the statements are built from. By chapter, with the latest run's
comparisons on normal forms for contrast:

| | ✱1–✱21 | ✱22 | ✱23 | ✱24 | ✱25 |
|---|---|---|---|---|---|
| comparisons by `direct` (earlier run) | under 2 s | 70 s | 276 s | 689 s | 7482 s |
| comparisons on normal forms (latest run, `10fb7d0`) | 18 s | 11 s | 14 s | 102 s | 131 s |

On the small statements of ✱1–✱21 computing and auditing the normal forms costs more than the direct
comparison saves. ✱9 takes 1.3 s of the 18 s: once a statement's audit has flagged something, the normal
forms of its remaining mutants are not computed.

A few statements took most of it, each with 6 to 52 mutants: ✱25·431 3452 s and ✱25·432 3282 s
(together 77% of the meta-program), ✱24·431 260 s, ✱24·432 241 s, ✱25·491 206 s, ✱25·493 166 s,
✱25·44 94 s, ✱23·93 71 s. The skeleton tautology tests of the statements from ✱9 on took 142 s.

For that whole run, `/usr/bin/time -v` reported a maximum resident set of 23,093,504 kB (about 22 GiB),
247 million major page faults and 118% CPU.

Before ✱25 the run comparing by `direct` took 1708 s with ✱1–✱24 on a shared machine (2026-10-14), and
524 s before ✱22–✱24 on a less loaded one.

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
  decision. With ✱25 it measured 14 min 59 s with 8 jobs, comparing on normal forms (2 h 32 min the
  earlier way; [measured code](#measured-code), above), and it runs on our own machines only.
- **Hypothesis recompilation stays part of `--full`** (the maintainer's ruling 68, 2026-10-14). The
  recommendation called it optional: it found nothing beyond the term analysis, at 5 to 9 minutes (308 s
  in the latest run with ✱25, 521 s in the one before it). It costs only time on our own machines.
- **The link to PM's text** that mutation cannot check is now `tests/test_regeneration.py`, a test in
  `tests/run_all.sh` ([above](#what-this-says-about-the-tie-to-pms-text)).
