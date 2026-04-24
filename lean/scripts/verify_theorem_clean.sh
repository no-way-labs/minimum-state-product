#!/bin/zsh
set -eu

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PATTERN='/bin/lean|/bin/lake|lake build|lean-language-server'
LOG="/tmp/verify_theorem_clean.log"

pids="$(pgrep -f "$PATTERN" 2>/dev/null || true)"
if [ -n "$pids" ]; then
  kill $pids 2>/dev/null || true
  sleep 1
fi

cd "$ROOT"
set +e
perl -e 'alarm shift; exec @ARGV' 180 \
  lake build LeanMn.LowerBound.Theorem >"$LOG" 2>&1
rc=$?
set -e

grep -E "sorry|error" "$LOG" | head -10

if [ $rc -ne 0 ] && ! grep -qE "sorry|error" "$LOG"; then
  echo "error: verify_theorem_clean.sh timed out or failed before emitting sorry/error lines" >&2
  exit $rc
fi
