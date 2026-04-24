#!/usr/bin/env python3
"""Standalone verifier for the Farkas certificate bundle.

Usage:  python3 farkas_verify.py farkas_certificates.json

For each record in the bundle, re-checks the Farkas witness:
    for every edge (s, t) in E_lift,  topo_order[t] > topo_order[s].

This is purely combinatorial — no LP solver, no external deps beyond
Python stdlib. A referee can run this on any machine in seconds and
verify the infeasibility claims without trusting the original solver
or this project's Python stack.

Exit code = number of records that fail certificate verification.
"""

from __future__ import annotations

import json
import sys


def verify_one(rec):
    y = rec["topo_order"]
    E = rec["E_lift"]
    violations = []
    for (s, t) in E:
        if not (y[t] > y[s]):
            violations.append((s, t, y[s], y[t]))
            if len(violations) >= 5:
                break
    return violations


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 farkas_verify.py <farkas_certificates.json>")
        return 2
    path = sys.argv[1]
    with open(path) as f:
        bundle = json.load(f)
    recs = bundle["records"]
    n_pass = 0
    n_fail = 0
    for r in recs:
        name = r.get("name", "?")
        n = r.get("n")
        L = r.get("L")
        nV = r.get("nV_lift")
        nE = r.get("nE_lift")
        if r.get("error"):
            print(f"  [SKIP] {name} n={n}: extraction error — {r['error']}")
            n_fail += 1
            continue
        violations = verify_one(r)
        if not violations:
            print(f"  [PASS] {name} n={n} L={L} |V|={nV} |E|={nE}: "
                  f"{nE} edges all strict-monotone under topo_order.")
            n_pass += 1
        else:
            print(f"  [FAIL] {name} n={n}: {len(violations)} edges violate "
                  f"topo order (showing up to 5):")
            for (s, t, ys, yt) in violations:
                print(f"     edge {s}→{t}: y[{s}]={ys}, y[{t}]={yt} "
                      f"(expected y[{t}] > y[{s}])")
            n_fail += 1
    print()
    print(f"  {n_pass} pass, {n_fail} fail, {len(recs)} total")
    return n_fail


if __name__ == "__main__":
    sys.exit(main())
