# Contributing

Issues and pull requests are welcome: a proof that follows PM more closely, a new proposition, a ledger
correction, or a mistake in the documentation. Errors in the digital texts of PM (the Gutenberg or
Distributed Proofreaders transcriptions) belong in the companion
[text audit](https://github.com/willmcginnis/principia-mathematica-text-audit) instead. Please do not paste
the unpublished Distributed Proofreaders text of Vol III into issues.

The project's design principles are in [docs/PRINCIPLES.md](docs/PRINCIPLES.md). If a proposition you
formalize comes with a claim of PM's about its own system ("by merely repeating previous proofs", "can be
proved in each particular case"), add it to [docs/PM_CLAIMS.md](docs/PM_CLAIMS.md) with its status.

## The rules a proof must keep

- No `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `extern`.
- PM theorems are derived in the embedded system (`Thm` for ✱1–✱5, `QThm S` from ✱9 on), from PM's own
  primitive propositions. They must report "does not depend on any axioms".
- State every theorem for an arbitrary family `V` and system `S : Sys V`. If it uses ✱12·1 or ✱12·11, take
  `[Reducibility S]` in its signature; if it uses comprehension, take `[Comprehension S]`. Do not pass the
  evidence any other way (for example as `h : S.red = true`): `RedCheck.lean` flags that.
- Follow PM's proof. Write one Lean line per *Dem.* line, or one step per proposition of PM's bracketed hint,
  in PM's order. Write displayed chains as `calc` blocks (`PM/Chain.lean`), one line per PM line, with PM's
  citation in a comment. Use silently only the steps PM leaves tacit, as listed in the file header.

## Naming and source references

The names below are the repository's own. Names for export to formalization platforms
(`PM.star2_01_abs_not_of_imp_not`) are generated from these by `scripts/export_names.py`; see
[docs/NAMING.md](docs/NAMING.md).

- ✱N·M is `tN_M` for ✱2–✱5 (namespace `PM`, statements `sN_M` in `PM/Statements.lean`) and `qN_M` from ✱9
  on. For example ✱20·11 is `q20_11` and ✱14·21's variant is `q14_21_neg`. Helpers that are not PM items
  get descriptive names (`qiffCongrRImp`), or a suffix after the number (`q12_1_var`).
  `scripts/progress.py` counts a theorem as stating a PM item only by these names.
- A check that is not a PM item (a tautology, a notation, a pinned statement) is a theorem
  `check_<words>`, never an `example` ([docs/NAMING.md](docs/NAMING.md#check-theorems)).
- The docstring starts with the label and PM's statement, then says what the proof does where PM is silent:
  `/-- ✱20·11 ⊢ :. ψx . ≡ₓ . χx : ⊃ : … . ✱4·86 for the second member … -/`.
- Cite pages of the **1910 print** of Vol I (Vol II: 1912), as `p. 194` or `pp. 194–195`. The page
  markers of Gutenberg eBook #78050 follow the print. Quote PM exactly when a reading rests on its words.
- Where the print looks wrong (a citation that does not give the step, a dropped double negation), say so in
  the docstring rather than silently fixing it, and say what the proof uses instead.

## Ledgers

Each numbered item formalized from ✱11 on has one row in `data/starNN_ledger.json`; ✱2–✱5 are in
`replay_ledger.json` and `replay2_ledger.json`. The fields are described in [data/README.md](data/README.md)
and the labels in [docs/FIDELITY.md](docs/FIDELITY.md). When you add or change a proof:

- list PM's citations the proof uses (`cited_used`) and does not use (`cited_unused`);
- list every other proposition it needs in `extra_used`, with the reason in `reason`, unless it is chain
  glue or a step in the row's `tacit` list (an equivalence read as an implication outside a chain is
  tacit; see docs/FIDELITY.md);
- list structural steps in `glue` with their `glue_kind` (`chain`, `order`, `under-exists`);
- set `fidelity`: `pm-lines` if `extra_used` is empty, otherwise `pm-lines+extra` (`unchanged` if there is
  no PM proof to follow);
- keep the file's formatting, with a newline at the end.

## Before you open a pull request

```
lake build                       # no errors
lake env lean AxiomCheck.lean    # the new theorems report "does not depend on any axioms"
lake env lean AllAxioms.lean     # still 40 declarations using an axiom, none of them a PM derivation
lake env lean RedCheck.lean      # 0 disagreements between signatures and proofs
lake env lean StyleCheck.lean    # every PM proposition passes in Sys.full of all four styles
python3 data/fidelity_counts.py  # only the count lines, no inconsistency lines
lake env lean Checks/LedgerCheck.lean  # every proposition a proof uses is listed in its ledger row, and every claimed use is made
lake env lean Checks/Star9Readings.lean  # ✱9 under its four readings (scripts/star9_readings.py writes docs/STAR9_READINGS.md)
tests/run_all.sh                 # all of the above, ClauseSearch, the quick statement mutation and the regression tests
```

Before a release, the maintainer also runs `scripts/release_check.sh` ([docs/VERIFICATION.md](docs/VERIFICATION.md#before-a-release)):
the full statement mutation and the Mathlib counterparts, which take longer and download Mathlib.

If you add theorems, also run `python3 scripts/gen_axiomcheck.py`, so that `AxiomCheck.lean` covers them.
After committing, run `python3 scripts/progress.py --update` to refresh `docs/PROGRESS.md`. Update the counts
in `README.md` and `docs/FIDELITY.md` if they change, and add a line to `CHANGELOG.md`. Do not edit
generated files (`PM/Statements.lean`, `PM/QuantLift.lean`, `AxiomCheck.lean`, the counterpart checks) by
hand; `tests/test_regeneration.py` fails if one differs from its generator's output. See
[scripts/README.md](scripts/README.md).

## Questions, corrections and proposals

Open a GitHub issue: a question about a proof or a reading, a correction to a statement, a name or a
document, or a proposal (a new export, a change of convention). Proposals that would change an export name
or a released statement follow [docs/VERSIONING.md](docs/VERSIONING.md).

## License

The repository is licensed under either of the Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
or the MIT License ([LICENSE-MIT](LICENSE-MIT)), at your option; `docs/FORMALIZATION_COMPARISON.md` is
dedicated to the public domain under CC0 1.0 ([LICENSE-CC0](LICENSE-CC0)).

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work
by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms
or conditions. Contributions to `docs/FORMALIZATION_COMPARISON.md` are dedicated to the public domain under
CC0 1.0, as that document is.
