#!/bin/bash
# Full n=6 sub-threshold SMT sweep with sym-break.
# Run from the repo root (STAGE).
cd "$(dirname "$0")/../.." || exit 1
for ms in 2,2,2,2,2,6 2,2,2,2,3,4 2,2,2,2,2,7 2,2,2,2,3,5 2,2,2,2,2,8 2,2,2,2,4,4; do
    echo "==== $ms ===="
    python3 docs/m5rel/smt_relaxed_n5_n6.py \
        --ms "$ms" --sym-break --timeout 3600 --quiet 2>&1 | grep -E "product|Verdict:"
done
echo "DONE"
