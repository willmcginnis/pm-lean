#!/usr/bin/env bash
# The search for sorry, native_decide, axiom, unsafe, implemented_by and extern in every Lean file under
# DIR (default: the repository root), outside .lake. Prints the lines found and exits 1, or prints "none".
#
#   tests/forbidden_keywords.sh [DIR]
#
# One exception, by its path and its exact line: scripts/prove2me/extract_commands.lean, a Lean program
# run with `lean --run` and never imported, may declare `unsafe def main`, since Lean requires unsafe
# code to enable initializers before it re-elaborates a file. The same line in any other file, and any
# other line of that file, is found like any other.
set -uo pipefail
cd "${1:-$(dirname "$0")/..}" || exit 2

hits=$(grep -rnE --include='*.lean' --exclude-dir=.lake \
    '\b(sorry|native_decide|implemented_by|extern)\b|^\s*((private|protected|noncomputable|partial)\s+)*(unsafe\s|axiom\s+[^[:space:]]+\s*[:({[])' . \
  | grep -vE '^\./scripts/prove2me/extract_commands\.lean:[0-9]+:unsafe def main \(args : List String\) : IO UInt32 := do$')
if [ -n "$hits" ]; then
  echo "$hits"
  exit 1
fi
echo "none"
