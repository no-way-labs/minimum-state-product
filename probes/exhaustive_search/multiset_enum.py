#!/usr/bin/env python3
"""Deterministic multiset + dihedral-orbit enumeration for the
App-C exhaustive search.

Populates the proof-critical C1 (state-count coverage) and C2
(processor-orientation coverage) records of the coverage manifest.
These counts are derivable from the integer-product constraint and
the D_n action alone; they are thus reproducible bit-for-bit by any
referee and used as the canonical reference against which the search
driver's own enumeration is audited.

Usage:
    python3 multiset_enum.py <n>         # prints C1 + C2 for this n
    python3 multiset_enum.py --all       # prints C1 + C2 for n=3..9

Output fields per n:
    • multisets_below_target : exhaustive list of sorted multisets
      with each entry ≥ 2 and product strictly less than M_n
    • multiset_count         : |multisets_below_target|
    • orientations_count     : Σ |D_n-orbit reps| over all multisets
    • per_multiset_orbits    : per-multiset list of orientation reps
    • rehash                 : SHA-256 of the above payload
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from itertools import permutations


def mn_connected(n: int) -> int:
    """Connected-model M_n value per Theorem 5 of the paper."""
    if n <= 2:
        return 0
    if n == 3:
        return 8
    if n == 4:
        return 24
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_multisets(n: int, max_product: int):
    """All sorted multisets on n positive integers ≥ 2 with prod < max_product."""
    out = []

    def rec(i, prev, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        remaining = n - i
        lo = max(2, prev)
        for m in range(lo, max_product + 1):
            new_prod = prod * m
            if new_prod * (lo ** (remaining - 1)) >= max_product and remaining > 1:
                # Even if the rest is all lo, we're above threshold. But lo may
                # later have to be ≥ m, so min-rem floor is m^{remaining-1}.
                pass
            if new_prod >= max_product and remaining == 1:
                break
            if new_prod * (m ** (remaining - 1)) >= max_product:
                break
            prefix.append(m)
            rec(i + 1, m, prefix, new_prod)
            prefix.pop()

    rec(0, 2, [], 1)
    return out


def dihedral_orbits(multiset):
    """All orderings of the multiset modulo D_n = rotation + reflection.
    Returns a sorted list of canonical-min-lex representatives."""
    n = len(multiset)
    seen = set()
    reps = []
    for perm in set(permutations(multiset)):
        rots = [perm[i:] + perm[:i] for i in range(n)]
        refls = [tuple(reversed(r)) for r in rots]
        canon = min(rots + refls)
        if canon not in seen:
            seen.add(canon)
            reps.append(canon)
    reps.sort()
    return reps


def c1_c2_manifest(n: int) -> dict:
    m_target = mn_connected(n)
    multisets = enumerate_multisets(n, m_target)
    per_multiset = []
    total_orientations = 0
    for ms in multisets:
        orbits = dihedral_orbits(ms)
        per_multiset.append({
            "multiset": list(ms),
            "product": int(_prod(ms)),
            "n_orientations": len(orbits),
            "orbit_representatives": [list(o) for o in orbits],
        })
        total_orientations += len(orbits)
    payload = {
        "n": n,
        "M_n_connected": m_target,
        "multiset_count": len(multisets),
        "orientations_count": total_orientations,
        "per_multiset": per_multiset,
    }
    payload_bytes = json.dumps(
        {k: v for k, v in payload.items() if k != "rehash"},
        sort_keys=True,
    ).encode()
    payload["rehash"] = hashlib.sha256(payload_bytes).hexdigest()[:16]
    return payload


def _prod(xs):
    p = 1
    for x in xs:
        p *= x
    return p


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("n", nargs="?", type=int, default=None)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--compact", action="store_true",
                        help="Drop per-multiset orbit lists")
    args = parser.parse_args()

    if args.all:
        ns = list(range(3, 10))
    elif args.n is not None:
        ns = [args.n]
    else:
        parser.error("specify n or --all")

    print(f"{'n':>3} {'M_n':>6} {'multisets':>9} {'orbit_reps':>10} "
          f"{'rehash':>16}")
    for n in ns:
        m = c1_c2_manifest(n)
        print(f"{n:>3} {m['M_n_connected']:>6} {m['multiset_count']:>9} "
              f"{m['orientations_count']:>10} {m['rehash']:>16}")


if __name__ == "__main__":
    main()
