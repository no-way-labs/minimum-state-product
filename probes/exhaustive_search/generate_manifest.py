#!/usr/bin/env python3
"""Generate the coverage manifest (C1, C2 records) for
Appendix C of the paper.

Writes `coverage_manifest.json` adjacent to this script. Downstream
search-driver runs augment this manifest with C3 (candidate good
cycles), C4 (partial rule tables), and per-certificate rejection
streams; those fields are tagged 'pending_full_search' here.

The manifest format is specified in App~C.5 (sec:app-c-certificate).

Usage:
    python3 generate_manifest.py              # writes coverage_manifest.json
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from multiset_enum import c1_c2_manifest, mn_connected  # type: ignore


def build_manifest():
    per_n = {}
    for n in range(3, 10):
        per_n[str(n)] = c1_c2_manifest(n)
    # Totals (for cross-reference with Table 9):
    totals = {
        "n_values":          [3, 4, 5, 6, 7, 8, 9],
        "M_n_connected":     [mn_connected(n) for n in range(3, 10)],
        "multisets_below":   [per_n[str(n)]["multiset_count"] for n in range(3, 10)],
        "D_n_orbit_reps":    [per_n[str(n)]["orientations_count"] for n in range(3, 10)],
    }
    manifest = {
        "schema_version": 1,
        "description": (
            "Coverage manifest for App C of paper2. Populates C1 "
            "(state-count coverage) and C2 (processor-orientation coverage) "
            "deterministically from the integer-product constraint and D_n "
            "action. C3, C4, and rejection certificates are populated by "
            "the search driver and are marked 'pending_full_search' until "
            "the full run completes."
        ),
        "totals": totals,
        "per_n": per_n,
        "c3_candidate_good_cycles": "pending_full_search",
        "c4_partial_rule_tables":   "pending_full_search",
        "rej_by_pruning":           "pending_full_search",
        "rej_by_verifier":          "pending_full_search",
        "driver_hash":              "pending_full_search",
        "independent_verifier_hash": "pending_full_search",
        "wall_clock_seconds":       "pending_full_search",
    }
    payload_bytes = json.dumps(
        {k: v for k, v in manifest.items() if k != "manifest_hash"},
        sort_keys=True,
    ).encode()
    manifest["manifest_hash"] = hashlib.sha256(payload_bytes).hexdigest()[:16]
    return manifest


def main():
    manifest = build_manifest()
    out_path = os.path.join(HERE, "coverage_manifest.json")
    with open(out_path, "w") as f:
        json.dump(manifest, f, indent=2)
    size = os.path.getsize(out_path)
    print(f"Wrote {out_path} ({size} bytes)")
    print(f"  schema_version      : {manifest['schema_version']}")
    print(f"  n covered           : 3..9")
    print(f"  multisets_below     : {manifest['totals']['multisets_below']}")
    print(f"  D_n orbit reps      : {manifest['totals']['D_n_orbit_reps']}")
    print(f"  manifest_hash       : {manifest['manifest_hash']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
