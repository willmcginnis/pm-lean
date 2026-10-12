# Regression tests

One test for each mistake a review has caught, where a test is possible. `tests/run_all.sh` runs them
all with the build and the root checks; `.github/workflows/check.yml` runs it on every push and pull
request. Each test was checked to fail when its mistake is put back.

| Mistake a review found | Guarded by |
|---|---|
| `transIff`'s docstring (PM/Chain.lean) cited ✱4·22, which its proof did not use | `Checks/LedgerCheck.lean`, check 1: every proposition a PM/Chain.lean docstring cites is used by the proof term |
| ✱10·281 was missing from the ledger rows of ✱14·18 and ✱14·203 | `Checks/LedgerCheck.lean`, check 2: every PM proposition a row's proof uses is listed in the row (uses awaiting a decision would go in `ledger_unlisted_uses.txt`, now empty) |
| Rows counted an equivalence read as an implication as an extra (✱3·26, ✱3·27), against the rule that it is tacit outside a chain and chain glue inside one | `Checks/LedgerCheck.lean`, check 2: a chain's ≡-to-⊃ step must be listed as ✱3·26, and ✱3·26 or ✱3·27 may be listed only where the proof uses it on a product that is not an equivalence, or in a chain |
| Ledger rows listed chain glue or their own tacit steps in `extra_used` | `test_fidelity_counts.py`: fidelity_counts.py reports no inconsistent row, and the Fidelity table equals its output |
| Four ledger files lost their final newline | `test_ledger_files.py`: every ledger parses, ends with a newline, and its rows have their ledger's fields |
| ✱14·32 was weakened from ≡ to ⊃ | `Checks/PinnedStatements.lean` (part of `lake build`): the exact statements of the propositions whose statement was corrected |
| Claims stated more strongly than proved (now `styles_equiv`, `realPhi_every_system`, `second_clause_iff_lowestOrder`, ...) | `Checks/PinnedStatements.lean` |
| (the list of axiom users must change only deliberately) | `test_axiom_users.py` against `expected_axiom_users.txt` |
| A count of proved propositions included primitive propositions | `test_proved_counts.py`: the docs' counts per chapter equal the ledgers' |

Run everything with `tests/run_all.sh` (`SKIP_SLOW=1` leaves out ClauseSearch, about a minute), or
only the Python tests with `python3 -m unittest discover -s tests` once the project is built.
