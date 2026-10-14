#!/usr/bin/env bash
# The checks run before a release, from the repository's root: the long ones, which do not run on every
# push (docs/VERIFICATION.md, "Before a release"). First every standing check (tests/run_all.sh), then
#   - the full statement mutation (scripts/mutation/mutate.py --full, docs/STATEMENT_MUTATION.md): all
#     statements of ✱1–✱5 and from ✱9 on, the proof scripts re-elaborated, hypotheses recompiled; tens
#     of minutes on 8 cores;
#   - the Mathlib counterparts compiled against the pinned Mathlib (Checks/MathlibCounterparts/, a Lake
#     project of its own; `lake exe cache get` downloads Mathlib's build, a few GB, the first time);
#   - with COUNTERPART_SOURCES=DIR, each counterpart's file, line and source header in checkouts of the
#     pins, DIR/<repository>-<commit> (scripts/export_names.py --verify-counterparts).
# Exits nonzero if any of them fails.
#
#   scripts/release_check.sh                    everything
#   SKIP_STANDING=1 scripts/release_check.sh    without tests/run_all.sh
set -uo pipefail
cd "$(dirname "$0")/.."

failed=()
step() { echo; echo "== $1"; }
fail() { echo "FAILED: $1"; failed+=("$1"); }

if [ -z "${SKIP_STANDING:-}" ]; then
  step "standing checks (tests/run_all.sh)"
  bash tests/run_all.sh || fail "tests/run_all.sh"
fi

step "statement mutation, full (docs/STATEMENT_MUTATION.md)"
python3 scripts/mutation/mutate.py --full || fail "statement mutation --full"

step "Mathlib counterparts against the pinned Mathlib (Checks/MathlibCounterparts/)"
python3 scripts/export_names.py --check >/dev/null || fail "Checks/MathlibCounterparts/MathlibCounterparts.lean is not up to date"
if (cd Checks/MathlibCounterparts && lake exe cache get); then
  out=$(cd Checks/MathlibCounterparts && lake env lean MathlibCounterparts.lean 2>&1)
  rc=$?
  echo "$out" | cut -c1-200 | head -n 20
  [ "$rc" -eq 0 ] || fail "Checks/MathlibCounterparts/MathlibCounterparts.lean"
  grep -qE 'Mathlib counterparts: 14 checked by Lean against Mathlib 0df444a' <<<"$out" \
    || fail "Checks/MathlibCounterparts/MathlibCounterparts.lean: expected 14 counterparts checked"
else
  fail "lake exe cache get (Checks/MathlibCounterparts)"
fi

if [ -n "${COUNTERPART_SOURCES:-}" ]; then
  step "counterpart sources in $COUNTERPART_SOURCES"
  python3 scripts/export_names.py --check --verify-counterparts "$COUNTERPART_SOURCES" || fail "counterpart sources"
fi

echo
if [ ${#failed[@]} -eq 0 ]; then
  echo "all release checks passed"
else
  printf 'failed: %s\n' "${failed[@]}"
  exit 1
fi
