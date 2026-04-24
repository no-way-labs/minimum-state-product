#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

pattern='^import LeanMn\.LowerBound\.Archive'

if command -v rg >/dev/null 2>&1; then
  if rg -n "$pattern" LeanMn/LowerBound -g '!**/Archive/**'; then
    echo "lint_no_archive_import: live LowerBound file imports Archive" >&2
    exit 1
  fi
else
  matches="$(
    find LeanMn/LowerBound -type f -name '*.lean' ! -path 'LeanMn/LowerBound/Archive/*' -print0 |
      xargs -0 grep -nE "$pattern" || true
  )"
  if [ -n "$matches" ]; then
    printf '%s\n' "$matches"
    echo "lint_no_archive_import: live LowerBound file imports Archive" >&2
    exit 1
  fi
fi

echo "lint_no_archive_import: ok"
