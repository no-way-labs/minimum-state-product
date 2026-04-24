#!/usr/bin/env python3
"""Strengthening #10 — finite-computation verification of the two
observations that rule out ARG's 1985 LCM bound as the mechanism for
the n = 9 phase transition.

Shipped as an executable reference implementation for the paper's
§5.3 (sec:lower-arg). The paper's prose statement is verified here
against the stored witness data, so a referee can check the claim by
running this script.

Observations (quoted from §5.3):

  (1) Scope. The small-n absorber witnesses use adjacent binary
      positions, hence lie outside ARG's non-adjacency hypothesis.

  (2) Insensitivity. On the non-adjacent orientations of
      {2^3, 4, 3^(n-4)} at n ∈ {8, 9}, each of four LCM functionals
      (global, per-arc-min, per-arc-max, block-product) takes values
      in identical or nested sets between n = 8 and n = 9.

The verdict strings hard-coded in the paper — {12}, {3}, {4, 12},
{36, 108} ⊂ {36, 108, 324} — are the expected outputs of this script.

Usage:
    python3 arg_lcm_finite_checks.py          # runs both observations
    python3 arg_lcm_finite_checks.py --json   # writes arg_lcm_checks.json
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from collections import Counter, defaultdict
from itertools import permutations
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
DOCS_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "..", "docs"))
sys.path.insert(0, DOCS_DIR)

import verify_witnesses as vw  # type: ignore


# ----------------------------------------------------------------------
# Observation (1) — adjacency of binary positions in every stored witness
# ----------------------------------------------------------------------

def cyclic_adjacent_binary_pairs(ms):
    """Return the list of cyclically-adjacent binary pairs (i, (i+1) mod n)."""
    n = len(ms)
    pairs = []
    for i in range(n):
        if ms[i] == 2 and ms[(i + 1) % n] == 2:
            pairs.append((i, (i + 1) % n))
    return pairs


def run_observation_1():
    print("=" * 72)
    print("Observation (1) — adjacency of binary positions")
    print("=" * 72)
    witnesses = [
        ("w4opt", vw.witness_n4opt),
        ("w5", vw.witness_n5),
        ("w6", vw.witness_n6),
        ("w7", vw.witness_n7),
        ("w8", vw.witness_n8),
    ]
    rows = []
    all_pass = True
    for name, fn in witnesses:
        ms, _rules = fn()
        ms = list(ms)
        pairs = cyclic_adjacent_binary_pairs(ms)
        binaries = [i for i, m in enumerate(ms) if m == 2]
        has_adj = len(pairs) > 0
        tag = "PASS" if has_adj else "FAIL"
        if not has_adj:
            all_pass = False
        print(f"  [{tag}] {name}: ms={ms} binaries@{binaries} "
              f"cyclic-adj-pairs={pairs}")
        rows.append({
            "name": name, "ms": ms, "binaries": binaries,
            "adjacent_pairs": pairs, "has_adjacent_binary_pair": has_adj,
        })
    verdict = {
        "observation": 1,
        "claim": ("Every stored n ∈ {4opt, 5, 6, 7, 8} sharp witness "
                  "has ≥1 cyclically adjacent binary pair."),
        "all_pass": all_pass,
        "witness_rows": rows,
    }
    print(f"\n  Verdict: {'CONFIRMED' if all_pass else 'REFUTED'}")
    return verdict


# ----------------------------------------------------------------------
# Observation (2) — LCM-functional insensitivity on {2^3, 4, 3^{n-4}}
# ----------------------------------------------------------------------

def _lcm(a, b):
    return a * b // gcd(a, b) if a and b else max(a, b)


def _lcm_of(values):
    r = 1
    for v in values:
        r = _lcm(r, v)
    return r


def is_non_adjacent_binary(ms):
    n = len(ms)
    bin_pos = [i for i, m in enumerate(ms) if m == 2]
    if len(bin_pos) < 2:
        return True
    for i in range(len(bin_pos)):
        a = bin_pos[i]
        b = bin_pos[(i + 1) % len(bin_pos)]
        if (b - a) % n == 1 or (a - b) % n == 1:
            return False
    return True


def non_adjacent_orientations(sorted_ms):
    """All cyclic orderings of sorted_ms with non-adjacent binaries, taken
    up to dihedral symmetry."""
    n = len(sorted_ms)
    seen_canon = set()
    out = []
    for perm in set(permutations(sorted_ms)):
        if not is_non_adjacent_binary(list(perm)):
            continue
        rots = [perm[i:] + perm[:i] for i in range(n)]
        refls = [tuple(reversed(r)) for r in rots]
        canon = min(rots + refls)
        if canon not in seen_canon:
            seen_canon.add(canon)
            out.append(canon)
    return out


def lcm_functionals(ms):
    """Compute the four 'LCM of block state counts' readings.

    We interpret 'blocks' as maximal non-binary runs between binary
    positions on the ring. Each block is a list of state counts (all
    ≥ 3). The four functionals:

      - global       : LCM over ALL block entries pooled together.
      - per-arc-min  : LCM over each block's min entry, then LCM those.
      - per-arc-max  : LCM over each block's max entry, then LCM those.
      - block-product: product of block state counts per arc
                       (then the set of arc-products across blocks).
    """
    n = len(ms)
    bin_pos = [i for i, m in enumerate(ms) if m == 2]
    if not bin_pos:
        return None
    blocks = []
    for i in range(len(bin_pos)):
        start = (bin_pos[i] + 1) % n
        end = bin_pos[(i + 1) % len(bin_pos)]
        block = []
        j = start
        while j != end:
            block.append(ms[j])
            j = (j + 1) % n
        blocks.append(block)
    blocks_nonempty = [b for b in blocks if b]
    if not blocks_nonempty:
        return None
    all_entries = [v for b in blocks_nonempty for v in b]
    per_arc_min = [min(b) for b in blocks_nonempty]
    per_arc_max = [max(b) for b in blocks_nonempty]
    arc_products = [__import__("math").prod(b) for b in blocks_nonempty]
    return {
        "global_lcm":       _lcm_of(all_entries),
        "per_arc_min_lcm":  _lcm_of(per_arc_min),
        "per_arc_max_lcm":  _lcm_of(per_arc_max),
        "block_products":   sorted(set(arc_products)),
    }


def run_observation_2():
    print("\n" + "=" * 72)
    print("Observation (2) — LCM-functional insensitivity on "
          "{2^3, 4, 3^{n-4}} non-adjacent orientations")
    print("=" * 72)
    # Multisets for n=8 and n=9
    multisets = {
        8: (2, 2, 2, 3, 3, 3, 3, 4),  # {2^3, 4, 3^4}
        9: (2, 2, 2, 3, 3, 3, 3, 3, 4),  # {2^3, 4, 3^5}
    }
    per_n = {}
    for n, mset in multisets.items():
        orientations = non_adjacent_orientations(mset)
        stats = defaultdict(set)
        print(f"\n  n={n}, multiset={sorted(mset)}, "
              f"non-adjacent orientations: {len(orientations)}")
        for ms in orientations:
            lcms = lcm_functionals(list(ms))
            if lcms is None:
                continue
            stats["global_lcm"].add(lcms["global_lcm"])
            stats["per_arc_min_lcm"].add(lcms["per_arc_min_lcm"])
            stats["per_arc_max_lcm"].add(lcms["per_arc_max_lcm"])
            for p in lcms["block_products"]:
                stats["block_products"].add(p)
        per_n[n] = {k: sorted(v) for k, v in stats.items()}
        for k, v in per_n[n].items():
            print(f"    {k}: {v}")

    # Match paper's claim: sets at n=8 vs n=9
    claims = {
        "global_lcm":      "equal at n=8 and n=9",
        "per_arc_min_lcm": "equal at n=8 and n=9",
        "per_arc_max_lcm": "equal at n=8 and n=9",
        "block_products":  "n=8 subset ⊂ n=9",
    }
    verdicts = {}
    for k in claims:
        v8 = set(per_n[8][k])
        v9 = set(per_n[9][k])
        if k == "block_products":
            ok = v8.issubset(v9)
            verdict_str = (f"n=8:{sorted(v8)} ⊂ n=9:{sorted(v9)}" if ok
                           else f"n=8:{sorted(v8)} ⊄ n=9:{sorted(v9)} FAIL")
        else:
            ok = v8 == v9
            verdict_str = (f"n=8:{sorted(v8)} = n=9:{sorted(v9)}" if ok
                           else f"n=8:{sorted(v8)} ≠ n=9:{sorted(v9)} FAIL")
        verdicts[k] = {"ok": ok, "n8": sorted(v8), "n9": sorted(v9),
                       "claim": claims[k], "verdict": verdict_str}
        print(f"\n  [{'PASS' if ok else 'FAIL'}] {k}: {verdict_str}")
    all_pass = all(v["ok"] for v in verdicts.values())
    verdict = {
        "observation": 2,
        "claim": ("On non-adjacent orientations of {2^3, 4, 3^{n-4}}, "
                  "each LCM functional is constant or nested between n=8 and n=9."),
        "per_n_stats": per_n,
        "per_functional_verdicts": verdicts,
        "all_pass": all_pass,
    }
    print(f"\n  Verdict: {'CONFIRMED' if all_pass else 'REFUTED'}")
    return verdict


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true",
                        help="write arg_lcm_checks.json with full output")
    args = parser.parse_args()

    obs1 = run_observation_1()
    obs2 = run_observation_2()

    print("\n" + "=" * 72)
    overall = obs1["all_pass"] and obs2["all_pass"]
    print("OVERALL: " + ("CONFIRMED" if overall else "REFUTED"))
    print("  Observation (1) scope:        "
          + ("CONFIRMED" if obs1["all_pass"] else "REFUTED"))
    print("  Observation (2) insensitivity: "
          + ("CONFIRMED" if obs2["all_pass"] else "REFUTED"))
    print("=" * 72)

    if args.json:
        out_path = os.path.join(HERE, "arg_lcm_checks.json")
        with open(out_path, "w") as f:
            json.dump({"observation_1": obs1, "observation_2": obs2,
                       "overall_confirmed": overall}, f, indent=2)
        print(f"\nWrote {out_path}")

    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
