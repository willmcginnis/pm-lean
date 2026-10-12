# Contributing

Issues and pull requests are welcome: a proof that follows PM more closely, a new proposition, a ledger
correction, or a mistake in the documentation. Errors in the digital texts of PM (the Gutenberg or
Distributed Proofreaders transcriptions) belong in the companion
[text audit](https://github.com/willmcginnis/principia-mathematica-text-audit) instead. Please do not paste
the unpublished Distributed Proofreaders text of Vol III into issues.

## The rules a proof must keep

- No `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `extern`.
- PM theorems are derived in the embedded system (`Thm` for ✱1–✱5, `QThm S` from ✱9 on), from PM's own
  primitive propositions. They must report "does not depend on any axioms".
- State every theorem for an arbitrary system `S : Sys` (and family `V`). If it uses ✱12·1 or ✱12·11, take
  `[Reducibility S]` in its signature; if it uses comprehension, take `[Comprehension S]`. Do not pass the
  evidence any other way (for example as `h : S.red = true`): `RedCheck.lean` flags that.
- Follow PM's proof. Write one Lean line per *Dem.* line, or one step per proposition of PM's bracketed hint,
  in PM's order. Write displayed chains as `calc` blocks (`PM/Chain.lean`), one line per PM line, with PM's
  citation in a comment. Use silently only the steps PM leaves tacit, as listed in the file header.

## Naming and source references

- ✱N·M is `tN_M` for ✱2–✱5 (namespace `PM`, statements `sN_M` in `PM/Statements.lean`) and `qN_M` from ✱9
  on. For example ✱20·11 is `q20_11` and ✱14·21's variant is `q14_21_neg`. Helpers that are not PM items
  get descriptive names (`qiffCongrRImp`), or a suffix after the number (`q12_1_var`).
  `scripts/progress.py` counts a theorem as stating a PM item only by these names.
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
lake env lean AllAxioms.lean     # still 25 declarations using an axiom, none of them a PM derivation
lake env lean RedCheck.lean      # 0 disagreements between signatures and proofs
lake env lean StyleCheck.lean    # every PM proposition passes in Sys.full of all four styles
python3 data/fidelity_counts.py  # only the count lines, no inconsistency lines
lake env lean Checks/LedgerCheck.lean  # every proposition a proof uses is listed in its ledger row
tests/run_all.sh                 # all of the above, ClauseSearch and the regression tests
```

If you add theorems, also run `python3 scripts/gen_axiomcheck.py`, so that `AxiomCheck.lean` covers them.
After committing, run `python3 scripts/progress.py --update` to refresh `docs/PROGRESS.md`. Update the counts
in `README.md` and `docs/FIDELITY.md` if they change, and add a line to `CHANGELOG.md`. Do not edit
generated files (`PM/Statements.lean`, `PM/QuantLift.lean`, `AxiomCheck.lean`) by hand; see
[scripts/README.md](scripts/README.md).

By contributing you agree that your contribution is licensed under the repository's MIT License, except
that contributions to `docs/FORMALIZATION_COMPARISON.md` are dedicated to the public domain under CC0 1.0
(`LICENSE-CC0`), as that document is.
