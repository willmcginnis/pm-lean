#!/usr/bin/env bash
# Every check of the repository, from its root: the build (with the pinned statements of
# Checks/PinnedStatements.lean), a search for sorry / native_decide / added axioms, the root checks
# (RedCheck, StyleCheck, ClauseSearch), the citation and ledger check (Checks/LedgerCheck.lean), ✱9's
# readings (Checks/Star9Readings.lean), the export names (scripts/export_names.py --check), the Lean
# core counterparts of ✱1–✱5 (Checks/Counterparts.lean), and the Python tests in tests/ (which also run
# AllAxioms.lean, AxiomCheck.lean and fidelity_counts.py). Exits nonzero if any of them fails.
#
#   tests/run_all.sh            everything (ClauseSearch takes about a minute)
#   SKIP_SLOW=1 tests/run_all.sh  without ClauseSearch
set -uo pipefail
cd "$(dirname "$0")/.."

failed=()
step() { echo; echo "== $1"; }
fail() { echo "FAILED: $1"; failed+=("$1"); }

# Run a Lean file; fail if lean fails or if the output lacks each of the given patterns.
lean_check() {
  local file=$1; shift
  step "$file"
  local out
  if ! out=$(lake env lean "$file" 2>&1); then echo "$out"; fail "$file"; return; fi
  echo "$out" | cut -c1-200 | head -n 20
  for pat in "$@"; do
    grep -qE -- "$pat" <<<"$out" || fail "$file: expected output matching '$pat'"
  done
}

step "lake build"
lake build 2>&1 | tail -n 3
[ "${PIPESTATUS[0]}" -eq 0 ] || fail "lake build"

step "no sorry, native_decide, axiom, unsafe, implemented_by or extern"
# One exception, by its exact line: a Lean program under scripts/ that is run with `lean --run` and never
# imported (scripts/prove2me/extract_commands.lean) may declare `unsafe def main`, since Lean requires
# unsafe code to enable initializers before it re-elaborates a file. Nothing else in it is exempt.
hits=$(grep -rnE --include='*.lean' --exclude-dir=.lake \
    '\b(sorry|native_decide|implemented_by|extern)\b|^\s*((private|protected|noncomputable|partial)\s+)*(unsafe\s|axiom\s+[^[:space:]]+\s*[:({[])' . \
  | grep -vE '^\./scripts/[^:]+\.lean:[0-9]+:unsafe def main \(args : List String\) : IO UInt32 := do$')
if [ -n "$hits" ]; then
  echo "$hits"
  fail "forbidden keyword"
else
  echo "none"
fi

lean_check RedCheck.lean 'signature disagrees with their proof: 0 ' 'flagged as using reducibility without asking: true'
lean_check StyleCheck.lean 'no parameter S : Sys: 0 ' 'failing in Sys.full of some style: 0 '
if [ -z "${SKIP_SLOW:-}" ]; then
  lean_check ClauseSearch.lean 'disagreements: 0"'
fi
lean_check Checks/LedgerCheck.lean '; 0 citations not used by the proof' \
  'ledgers: [0-9]+ rows checked against their proofs; 0 propositions used but not listed' \
  '✱9 ledger: [0-9]+ rows checked .*; 0 propositions used but not listed'

lean_check Checks/Star9Readings.lean '"kind": "simul", "reading": "C"'

step "export names (docs/NAMING.md)"
python3 scripts/export_names.py --check || fail "export names"

lean_check Checks/Counterparts.lean 'counterparts: 54 checked by Lean'

step "Python tests"
python3 -m unittest discover -s tests -v || fail "Python tests"

echo
if [ ${#failed[@]} -eq 0 ]; then
  echo "all checks passed"
else
  printf 'failed: %s\n' "${failed[@]}"
  exit 1
fi
