#!/usr/bin/env bash
# Negative tests of Checks/LedgerCheck.lean. In a scratch copy of the ledgers (data/*_ledger.json) and
# of its two baseline files (tests/ledger_unlisted_uses.txt, tests/ledger_unused_claims.txt), each of
# these edits must make the check fail, with the message that names the edit:
#   - a fabricated claim: *5.19 added to the cited_used of *22.1 (the reverse check of check 2);
#   - a fabricated definition: *23.01 added there (the reverse check: no realizer of it is referenced);
#   - a removed use: *4.2 removed from the cited_used of *22.1 (check 2).
# The check reads its files relative to the working directory, so it is run in the scratch directory
# with the repository's build (`lake -d`). Exits nonzero if an edit is not caught.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
failed=0

# case NAME EDIT EXPECTED: EDIT is Python run on the list of rows `rows` of data/star22_ledger.json
case_() {
  local name=$1 edit=$2 expected=$3
  local tmp
  tmp=$(mktemp -d)
  mkdir -p "$tmp/data" "$tmp/tests"
  cp "$root"/data/*_ledger.json "$tmp/data/"
  cp "$root/tests/ledger_unlisted_uses.txt" "$root/tests/ledger_unused_claims.txt" "$tmp/tests/"
  cp "$root/lean-toolchain" "$tmp/"   # elan picks the toolchain from the working directory
  python3 - "$tmp/data/star22_ledger.json" "$edit" <<'EOF'
import json, sys
path, edit = sys.argv[1], sys.argv[2]
rows = json.load(open(path))
row = next(r for r in rows if r["id"] == "*22.1")
exec(edit)
json.dump(rows, open(path, "w"), indent=1, ensure_ascii=False)
EOF
  local out rc
  out=$(cd "$tmp" && lake -d "$root" env lean "$root/Checks/LedgerCheck.lean" 2>&1)
  rc=$?
  if [ "$rc" -ne 0 ] && grep -qF -- "$expected" <<<"$out"; then
    echo "ok: $name fails the check ($expected)"
  else
    echo "NOT CAUGHT: $name (exit $rc)"
    echo "$out" | head -n 20
    failed=1
  fi
  rm -rf "$tmp"
}

case_ "a fabricated claim (*5.19 in *22.1's cited_used)" \
  'row["cited_used"].append("*5.19")' \
  "claimed in cited_used of its ledger row but not used by the proof: star22 *22.1 *5.19"
case_ "a fabricated definition (*23.01, realized by QF.relSubset, in *22.1's cited_used)" \
  'row["cited_used"].append("*23.01")' \
  "claimed in cited_used of its ledger row but not used by the proof: star22 *22.1 *23.01"
case_ "a removed use (*4.2 taken out of *22.1)" \
  'row["cited_used"].remove("*4.2")' \
  "not listed in its ledger row: *22.1 *4.2"

exit $failed
