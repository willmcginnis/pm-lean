# Verification: what the checks show

The proofs are checked by Lean's kernel when the project is built. This page covers what the extra check
files report, which Lean axioms are used and by what, and which theorem uses which of PM's rules. Figures are
for the commit named in [PROGRESS.md](PROGRESS.md).

## Commands and expected results

Requires the Lean toolchain named in `lean-toolchain` (install it with
[elan](https://github.com/leanprover/elan)); the proofs need nothing else. The external checkers, a step
of `tests/run_all.sh`, also need git, network access on their first run and Rust's `cargo`
([below](#external-checkers)).

| Command | Expected result |
|---|---|
| `lake build` | builds every file, and the pinned statements of `Checks/PinnedStatements.lean`, with no errors (54 jobs) |
| `lake env lean AxiomCheck.lean` | 1722 declarations, every public theorem of every file under `PM/` (check theorems included) and the models; 1715 report "does not depend on any axioms", the other 7 are the three propositional metatheorems and the four declarations of the classical collapse model (below) |
| `lake env lean AllAxioms.lean` | every declaration under `PM` (3097, with the check theorems of Checks/PinnedStatements.lean) and the 31 private declarations of the PM modules; it lists the 40 that use one of Lean's axioms |
| `lake env lean RedCheck.lean` | which declarations use ✱12·1 / ✱12·11 or comprehension, from the proofs, compared with the signatures: 0 disagreements among the 770 PM propositions. It must flag its own test `RedCheckTest.red_with_explicit_evidence`, and fails if it does not |
| `lake env lean StyleCheck.lean` | every PM proposition instantiated under every style and named system: 770 of 770 pass in `Sys.full` of all four styles |
| `lake env lean ClauseSearch.lean` | p. 56's second clause compared with the lowest-order rule on 2,784,780 cases: no disagreement (about 1 min) |
| `python3 data/fidelity_counts.py` | the three fidelity counts per chapter ([FIDELITY.md](FIDELITY.md)); any other line it prints is an inconsistency in a ledger |
| `lake env lean Checks/LedgerCheck.lean` | citations against proof terms: every proposition a `PM/Chain.lean` docstring cites is used by its proof (15 declarations), every PM proposition the proof of a ✱11–✱25 ledger row uses is listed in the row (512 rows), and, conversely, every proposition the row claims as used (`cited_used`, `extra_used`, `glue`) is used by the proof, through helpers (a definition counts where a declaration realizing it is referenced, a primitive proposition where its constructor is applied); the same both ways for the ledger of ✱9's own method, `data/star9f_ledger.json` (36 rows with a proof, for the working reading C and, for ✱9·31, also L and the cross-check B; 7 more are built into the syntax); 0 disagreements, and nothing left unresolved in `tests/ledger_unlisted_uses.txt` or `tests/ledger_unused_claims.txt`. `tests/ledger_negative.sh` (a step of run_all.sh) checks that a fabricated claim, a fabricated definition and a removed use each make it fail. The ✱2–✱5 ledgers are not checked against the proofs |
| `lake env lean Checks/Star9Readings.lean` | ✱9 under its four readings (A as printed; C as printed + ✱8·13, the working reading; L, Landini's ✱9+, a cross-check; B, the cross-check): for each ✱9 proposition the readings under which it is derived, read from the Lean statements, the cases of p. 142 each leaves open, and where C's proofs use ✱8·13 and L's use Switch (occurrences of `Thm9.exch` and `Thm9.switch` in the proof terms, ✱8·13's by the kinds of the quantifiers it exchanges; each combination of p. 142 searched again without and with the rule); `scripts/star9_readings.py` writes them to [STAR9_READINGS.md](STAR9_READINGS.md), and `tests/test_star9_readings.py` pins them |
| `python3 scripts/mutation/mutate.py --quick` | the quick tier of the statement mutation ([STATEMENT_MUTATION.md](STATEMENT_MUTATION.md)), a step of `run_all.sh` and a check an export must pass before upload; runs `lake build` first: no unused hypothesis in the 1784 theorems written in the source (the 313 check theorems included), the seven planted cases flagged; no proof term of 13 sampled ✱1–✱5 statements accepts any of their 469 one-change mutants; about 10 s on an idle machine |
| `python3 scripts/mutation/mutate.py --full` | before a release (below): the same for all 198 ✱1–✱5 statements and every one from ✱9 on (801, and 16,512 mutants in all, with ✱25), with hypotheses replaced by `True` and recompiled, and the proof scripts re-elaborated against every tautological mutant of the ✱1–✱5 statements proved in the replay files (all but ✱1·2–✱1·6, `Thm`'s constructors, which have no script); only the 14 renamings listed in `scripts/mutation/expected.json` survive; the kernel compares each proof's type with each mutant on normal forms ([STATEMENT_MUTATION.md](STATEMENT_MUTATION.md#how-a-mutant-is-compared)); 11 min 43 s with ✱25 and 8 jobs on an otherwise idle machine, with a maximum resident set of about 1.94 GiB for any one process (2026-10-15, on the Lean code and scripts of `608ba9d`, [STATEMENT_MUTATION.md](STATEMENT_MUTATION.md#measured-code); 2 h 32 min and about 22 GiB comparing the earlier way, on the Lean code and scripts of `07f82e0`; [STATEMENT_MUTATION.md](STATEMENT_MUTATION.md#how-to-run)) |
| `python3 scripts/kernel_census/census.py --ratchet` | the features of Lean's kernel that the PM derivations and their closure use equal `tests/expected_kernel_features.txt`, and the axiom users equal `tests/expected_axiom_users.txt` ([KERNEL_CENSUS.md](KERNEL_CENSUS.md)); about 15 s, run by `tests/test_kernel_census.py` |
| `python3 scripts/kernel_census/census.py --check` | the full kernel census (the static walk of every declaration and its closure; the kernel's re-check of each theorem, definition and opaque constant, with its unfoldings recorded, inductive types, constructors, recursors and `partial` or `unsafe` definitions excepted; the check theorems included) agrees with the tables of [KERNEL_CENSUS.md](KERNEL_CENSUS.md); about 80 s, not part of `run_all.sh` |
| `python3 scripts/external_checkers.py` | the proofs re-checked by two kernels independent of Lean's, con-leche and nanoda, on an export of `PM` and `Checks.PinnedStatements`, with a scan of the export and six negative controls ([below](#external-checkers)); a step of `run_all.sh`; the first run fetches and builds the tools (about 3 min), later runs take about 2.5 min |
| `tests/run_all.sh` | the regression tests of [tests/](../tests/README.md) and all of the above but `mutate.py --full` and `census.py --check` (`SKIP_SLOW=1` leaves out ClauseSearch, `SKIP_EXTERNAL=1` the external checkers); ends with "all checks passed" |
| `scripts/release_check.sh` | before a release (below): `tests/run_all.sh`, then the checks that run only before a release; ends with "all release checks passed" |

`AxiomCheck.lean` is generated by `scripts/gen_axiomcheck.py` ([scripts/README.md](../scripts/README.md)).
It covers every public theorem of every file under `PM/`, found by globbing, with its namespace (the ✱2–✱5
theorems, `complete`, ✱9–✱25, ✱9's own foundation in `PM/Found9/`, the rule, style and model modules), and
the definitions of the models; `tests/test_axiomcheck_coverage.py` checks that it is up to date, and
`tests/test_regeneration.py` that it and every other generated file are their generator's output, byte
for byte. The "770 PM
propositions" of RedCheck and StyleCheck are the `q…` theorems of ✱9–✱25 by ✱10's method and the 188
lifted copies of ✱2–✱5 (`PM.QL.t…`; ✱9's own method, `PM.F9.f…`, is not among them), a different unit from
the assertions counted in [PROGRESS.md](PROGRESS.md); that page defines both and sorts the 770 into its units.

The repository contains no `sorry`, no `native_decide`, no `axiom` declaration, and no `unsafe`,
`implemented_by` or `extern`, with one exception outside the library: the export tool
`scripts/prove2me/extract_commands.lean`, which no Lean file imports, declares `unsafe def main`, because
Lean requires unsafe code to enable initializers before it re-elaborates a file. `tests/run_all.sh`
allows exactly that line.

### Before a release

Checks that take long, or need what the repository does not depend on, run on our own machines before a
release (an export to Prove2Me, or a release of the repository), not on every push.
`scripts/release_check.sh` runs them all, after every standing check of `tests/run_all.sh`
(`SKIP_STANDING=1` leaves those out):

| Check | Expected result |
|---|---|
| `python3 scripts/external_checkers.py --nanoda-upstream require` | as in `run_all.sh` ([below](#external-checkers)), and nanoda's pin must be the head of its repository; the standing checks run without this step (`SKIP_EXTERNAL=1`), so it runs once |
| `python3 scripts/mutation/mutate.py --full` | as above; 703 s, 11 min 43 s, with ✱25 and 8 jobs on an otherwise idle machine, and about 1.94 GiB of memory for any one process (2026-10-15, on the Lean code and scripts of `608ba9d`, [STATEMENT_MUTATION.md](STATEMENT_MUTATION.md#measured-code)); "statement mutation: no unexpected finding". `mutate.py --compare-methods` (not part of the release check) runs both comparisons side by side and must report no disagreement; it takes as long as the earlier comparison ([STATEMENT_MUTATION.md](STATEMENT_MUTATION.md#how-a-mutant-is-compared)) |
| `lake exe cache get`, then `lake env lean MathlibCounterparts.lean`, in `Checks/MathlibCounterparts/` | the 14 Mathlib counterparts of ✱1–✱5 (data/naming/counterparts.json) compiled against Mathlib `0df444a` with its Lean v4.33.1: each states PM's formula exactly, by the criterion of [NAMING.md](NAMING.md#counterparts), and its `classical` flag matches the axioms its proof uses; prints "Mathlib counterparts: 14 checked by Lean against Mathlib 0df444a". A Lake project of its own, so the repository's `lake build` needs no Mathlib; the first `lake exe cache get` downloads Mathlib's build, a few GB |
| with `COUNTERPART_SOURCES=DIR`: `python3 scripts/export_names.py --check --verify-counterparts DIR` | each counterpart's file and line, and a Mathlib one's header and `variable` line, in checkouts of the pins at `DIR/<repository>-<commit>` |

An export also runs its own checks before upload, with the platform's Lean
([scripts/prove2me/README.md](../scripts/prove2me/README.md)); the quick tier of the statement mutation is
the first of them.

## External checkers

Lean's own kernel checks every proof when the project is built. `scripts/external_checkers.py` exports
the proofs and has them checked again by two kernels written independently of it, so that a proof
accepted only because of a bug in Lean's kernel would have to get past both as well. It is a step of
`tests/run_all.sh` and of `scripts/release_check.sh`, and exits nonzero unless every part below passes.

### The tools and their versions

All three are fetched from their repositories at pinned commits and built by the script, in
`.lake/external-checkers/` (not tracked).

| Tool | Repository, pinned commit | What it is |
|---|---|---|
| lean4export | `leanprover/lean4export` at `076e8e5` (tag v4.34.0; export format 3.1.0) | Lean's exporter: reads the `.olean` files the build wrote and writes every declaration as JSON lines. Built with this repository's toolchain (Lean v4.34.1), which the script writes over the tag's `lean-toolchain` |
| con-leche | `leanprover/con-leche` at `c26f793` (2026-10-14), built with its own toolchain, Lean v4.35.0-rc3 | a kernel written in Lean, with its own term representation, run with `--verified`: the mode with the extra comparisons its consistency proof relies on |
| nanoda | `ammkrn/nanoda_lib` at `e0d76f5` (crate version 0.4.23), built with `cargo build --release --locked` (measured with rustc 1.99.0) | a kernel written in Rust |

Ruling 69 asks for pinned versions, with nanoda kept current. `--nanoda-upstream require`, which the release
check passes, fails unless the pin is the head of nanoda's repository (or if that repository cannot be
reached); the standing checks only report it. On 2026-10-15 `e0d76f5` was the head.

### What is exported

`lean4export PM Checks.PinnedStatements`, run under `lake env` after `lake build PM
Checks.PinnedStatements`: every constant of the environment that importing those two modules gives,
except names Lean marks internal (exported anyway where another declaration uses them). That is the whole
library under `PM/`, the pinned statements and their check theorems, and everything they import from
Lean's own library, which is checked too: of the 167,603 declarations, 3,225 are named in `PM`, the
rest are Lean's (`Lean` 59,127, `Std` 42,340, private names 34,065, ...). Not exported: `Checks/Canon.lean`,
the root check files (`RedCheck.lean`, ...), and the meta-programs under `scripts/`. The export is
deterministic: its SHA-256 at `8dbf6e2` is `0ad60837b4b3fb7a029582399ac41c5a29f25a6d15e5aeefab69bba4893094df`
(766,638,582 bytes), the same as at `6b95af9`, whose `PM/`, `Checks/`, lakefile and toolchain are the same,
and as an export of `6b95af9` made earlier in another environment.

### The axiom policy, and the scan

Lean's core library declares seven axioms, so every export contains them, used or not: the three standard
ones (`propext`, `Quot.sound`, `Classical.choice`), `sorryAx`, and `Lean.trustCompiler`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, through which a proof can rest on compiled code.

- con-leche accepts only the three standard axioms; it skips the declaration of `sorryAx` but rejects a
  use of it, and replaces the other three by definitions of the same type (DOCUMENTED, its README).
- nanoda cannot be run with unpermitted axioms as a hard error on such an export: it then stops on the
  declaration of `sorryAx`. With the hard error off, an axiom not permitted is skipped and is an error
  only where a declaration uses it; but `Lean.trustCompiler` must then be permitted, because the bodies of
  two opaque core constants, `Lean.reduceBool` and `Lean.reduceNat`, name it, and without it nanoda
  panics (MEASURED; upstream issue ammkrn/nanoda_lib#53). An opaque body never unfolds, so admitting it
  there admits no proof that rests on compiled code. nanoda is therefore run with `propext`,
  `Quot.sound`, `Classical.choice` and `Lean.trustCompiler` permitted and the hard error off.
- So that this configuration hides nothing, the script scans the export itself, and fails unless: the
  only axioms declared are those seven; no declaration's type, value or recursor rules name `sorryAx`,
  `Lean.ofReduceBool` or `Lean.ofReduceNat`, directly or through an expression; and only
  `Lean.reduceBool` and `Lean.reduceNat` name `Lean.trustCompiler`. Since every declaration of the export
  is scanned, one that reaches such an axiom through another constant is caught at that constant.

### Negative controls

Each rule is seeded with a fault (ruling 59), every run: a small module is compiled, the closure of its
one theorem exported, and each checker named must reject it.

| Control | Must reject it | What happens (MEASURED, 2026-10-15) |
|---|---|---|
| `theorem bad_sorry : False := sorry` | con-leche, nanoda, the scan | con-leche: "use of the sorryAx axiom"; nanoda panics on the skipped `sorryAx`; the scan: `sorryAx` named |
| a stray `axiom stray_axiom : False`, used | con-leche, nanoda, the scan | con-leche: "non-standard axiom"; nanoda panics on it; the scan: an axiom not among the seven |
| `theorem … : 2 + 2 = 4 := by native_decide` | the scan | in Lean v4.34 `native_decide` declares an auxiliary axiom; all three reject it as a stray axiom |
| a use of `Lean.ofReduceBool` | the scan | con-leche accepts it (it replaces the axiom by a definition); nanoda panics on the skipped axiom |
| a use of `Lean.ofReduceNat` | the scan | the same |
| a use of `Lean.trustCompiler` | the scan | con-leche and nanoda accept it; the scan rejects it |

nanoda's rejections are panics (exit 101), not error reports. `tests/test_external_checkers.py` checks
the scan's rules on small hand-written exports, one fault per rule, without running a checker, and
that both scripts run the step.

### Figures

MEASURED on 2026-10-15 on the code of `8dbf6e2` (the script as committed with this section), 4 threads
for each checker, the commands niced, on a machine with 8 cores: the last run started at a load average
of 0.05, which the checkers' own threads raised to about 2.9. The builds are from the first run.
Peak memory is the maximum resident set of the step's process tree.

| Step | Result | Wall time | Peak memory |
|---|---|---|---|
| build lean4export, con-leche, nanoda (first run only) | built | 8 s, 2 min 47 s, 18 s | 0.97 GiB, 0.94 GiB, 0.31 GiB |
| export | 167,603 declarations, sha256 above | 42 s | 1.71 GiB |
| con-leche `--verified` | accepted 167,603 declarations | 41 s | 0.74 GiB |
| nanoda | 175,574 declarations, no typechecker error | 32 s | 0.93 GiB |
| the scan | the seven axioms declared; `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` named by none; `Lean.trustCompiler` only by `Lean.reduceBool` and `Lean.reduceNat` | 29 s | 0.22 GiB |
| the six negative controls | each rejected as required | 8 s | 0.59 GiB |
| the whole run, tools built | passes | 2 min 34 s (load 0.05 at the start, 2.03 at the end) | 1.71 GiB |
| the whole run, first (tools built in it) | passes but for one control, since changed | 5 min 56 s (load 0.08 at the start, 2.19 at the end) | 1.71 GiB |

nanoda counts an inductive declaration's types, constructors and recursors separately and leaves out the
axioms it skips: the export has 175,577 declarations counted that way, less `sorryAx`,
`Lean.ofReduceBool` and `Lean.ofReduceNat`. con-leche's count, like the scan's, is one per declaration
of the export.

### What these checks show, and what they do not

They show that two kernels other than Lean's, one written in Lean and one in Rust, accept every
declaration of the export, PM's proofs and the pinned statements among them, under the axiom policy
above; and that no declaration of the export rests on `sorryAx` or on compiled code.

They do not show:

- that the statements say what PM says: that is the business of the pinned statements, the ledgers and
  [FIDELITY.md](FIDELITY.md). Both checkers check the export they are given;
- that the export is faithful to the proofs: lean4export runs on Lean's own runtime and reads the
  `.olean` files Lean's elaborator wrote. A fault there is shared by both checkers;
- that con-leche is consistent. Its repository proves, in Lean, that every environment it accepts in
  `--verified` mode has a model in a set theory, ZF without infinity or choice together with an ω-chain of
  Grothendieck universes, so that it accepts no proof of `False` (DOCUMENTED, its README; we build the
  checker, not that proof, and have not checked it). That set theory is stronger than ZF; grounding the
  fragment the derivations use in ZF itself is on the roadmap. Its arithmetic on numerals uses Lean's
  runtime (DOCUMENTED);
- anything of the kind for nanoda, which has no such proof; it reports its rejections by panicking;
- anything about the declarations not exported (above).

## Lean's axioms

Every PM theorem (✱2–✱5 and ✱9–✱25, and ✱9 by its own method in `PM/Found9/`) and the completeness theorem
`complete` report "does not depend on any axioms" under `#print axioms`. PM's primitive propositions are not
Lean axioms: they are the rules of the embedded proof systems (`Thm`, `QThm`, and `Thm9` for ✱9's method).

The exhaustive check (`AllAxioms.lean`) finds 40 declarations that use Lean's standard axioms. None of them is
a PM derivation, an axiom-free consistency theorem or a counter-model.

- *Compiler-generated* (`propext` only): 29 `injEq` lemmas, and a `Repr` instance and its function (for
  printing formulas). Lean generates an `injEq` lemma for each constructor with arguments of an inductive
  type; 14 of them are for the syntax of ✱9's method: `PM.F9.EF` (5), `PM.F9.PF` (3), the printed
  expressions `PM.F9.PE` (5) of the prenex Switch, and the structure `PM.F9.Reading` (1). No theorem of
  `PM/Found9/` uses an axiom, `star9_iff_star10`, `thm9_sound`, `consistent9`, `exch_not_general`,
  `switch_not_general` and `switch_wide_unsound` included. The meta code of `PM/Found9/SearchTactic.lean` (namespace
  `Star9Search`, outside `PM`) proposes the parts of a merge to the proof search and is part of no proof.
- *Propositional metatheorems* (`propext`, `Quot.sound`): `PM.sound`, `PM.not_thm_of_countermodel` and
  `PM.star1_4_variant_not_a_theorem`; and the check theorem that pins the last one's statement,
  `PM.check_pinned_star1_4_variant` (Checks/PinnedStatements.lean), which is proved by it.
- *The general (classical) collapse model* (`propext`, `Classical.choice`, `Quot.sound`): `classicalAll`, its
  specification and `QModel.classical`, which give classical quantifiers over arbitrary function spaces, for
  any domain of individuals; and `consistent_collapse`, `consistent_collapse_of_style`, which evaluate in it.
  The same consistency statements are proved without axioms in the finite model.

The ✱9–✱21 soundness theorem `PM.qsound` uses no axioms, and neither do `consistent`, `consistent_all` and
the five counter-models. They are proved in a finite coded model (`PM/Models/Finite.lean`), in which function
values are truth tables and every quantifier is computed by enumeration. What consistency means here, and what
it does not, is in [SEMANTICS.md](SEMANTICS.md).

## Which theorem needs which rule

The proof system `QThm S` has PM's rules beyond ✱1–✱11 as opt-in modules
([ARCHITECTURE.md](ARCHITECTURE.md)). A theorem that uses a rule takes its class in its signature
(`[Reducibility S]`, `[Comprehension S]`). That this is so is the repository's convention, and `RedCheck.lean`
checks it from the proofs, including evidence passed in any other way (such as an explicit hypothesis
`h : S.red = true`). The table is from the signatures; RedCheck finds the same from the proofs, with 0
disagreements.

| Rule | Theorems that take it |
|---|---|
| none (hold in every system) | all 188 lifted ✱2–✱5 (`QL.t…`); all of ✱9–✱11; ✱13·1, ✱13·15, ✱13·17, ✱13·18, ✱13·19; ✱14·1, ✱14·101, ✱14·11, ✱14·111, ✱14·112, ✱14·113, ✱14·121, ✱14·18, ✱14·201, ✱14·21, `q14_21_neg`, ✱14·24, ✱14·271, ✱14·272, ✱14·28, ✱14·34; ✱20·1, ✱20·11, ✱20·111, ✱20·6, ✱20·61, ✱20·62, ✱20·63, ✱20·633, ✱20·64; ✱21·1, ✱21·11, ✱21·111, ✱21·6, ✱21·61, ✱21·62, ✱21·63, ✱21·633, ✱21·64; ✱22·1, ✱22·4, ✱22·42, ✱22·44, ✱22·441, ✱22·46; ✱23·1, ✱23·4, ✱23·42, ✱23·44, ✱23·441, ✱23·46; ✱24·5, ✱24·58; ✱25·5, ✱25·58 |
| `Reducibility` (✱12·1, ✱12·11) | `q12_1`, `q12_11`, `q12_1_var`, `q12_11_var`; ✱13·101, ✱13·11, ✱13·12, ✱13·13, ✱13·14, ✱13·16, ✱13·171, ✱13·172, ✱13·181, ✱13·182, ✱13·183, ✱13·191–✱13·196, ✱13·21, ✱13·22, ✱13·3; ✱14·12, ✱14·122, ✱14·123, ✱14·124, ✱14·13, ✱14·131, ✱14·14, ✱14·142, ✱14·144, ✱14·145, ✱14·15, ✱14·16, ✱14·17, ✱14·171, ✱14·2, ✱14·202–✱14·205, ✱14·22, ✱14·23, ✱14·241, ✱14·242, ✱14·25, ✱14·26, ✱14·27, ✱14·3, ✱14·31, ✱14·32, ✱14·33, ✱14·331, ✱14·332; ✱20·112–✱20·59, ✱20·7–✱20·81; ✱21·112–✱21·58, ✱21·7–✱21·71; the other 66 of ✱22's 72, the other 66 of ✱23's 72, the other 68 of ✱24's 70 and the other 68 of ✱25's 70, and the variant `q23_45_iff`; `trap_empty`, `trap_unit` |
| `Comprehension` | `q12_1_of_var` (and the rule statements `comprehension1`, `comprehension2`) |

RedCheck counts 406 PM propositions that use ✱12·1 or ✱12·11 and 1 that uses comprehension, the helper
`q12_1_of_var` (not a numbered PM proposition). Besides the rule's own statements, 9 declarations that are
not PM propositions (metatheorems about the system, the trap and the styles of predicativity) also use
comprehension.
