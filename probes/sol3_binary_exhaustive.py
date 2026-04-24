#!/usr/bin/env python3
"""sol3_binary_exhaustive.py — Exhaustive search over binary proc rules at 8748.

Strategy: Fix Sol 3 rules for all ternary processors. Then exhaustively
search over the binary processors' rule tables (small: 12 entries each).

For ms=(2,2,3,3,3,3,3,3,3):
- P0 (bottom): m=2, L∈{0,1,2}, S∈{0,1}, R∈{0,1} → 12 entries, each ∈{0,1}
- P1 (middle): m=2, L∈{0,1}, S∈{0,1}, R∈{0,1,2} → 12 entries, each ∈{0,1}
- P2-P7: ternary middle, Sol 3 rules
- P8: ternary top, Sol 3 rules

Total search: 2^12 × 2^12 = 16.7M — too large for brute force.
But with pre-filtering (liveness on configs where no ternary proc is privileged),
we can massively prune.

Approach:
1. Pre-compute ternary privileges for all 8748 configs
2. For each config where no ternary proc is privileged, at least one binary must be
3. This constrains the binary rules → prune search space
4. After pruning, enumerate remaining combos and check convergence
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

import time
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system


def sol3_middle(L, S, R):
    if (S + 1) % 3 == L:
        return L
    if (S + 1) % 3 == R:
        return R
    return S


def sol3_top(L, S, R):
    if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
        return (L % 3 + 1) % 3
    return S


def sol3_bottom_ternary(L, S, R):
    if (S + 1) % 3 == R:
        return (S - 1) % 3
    return S


def main():
    n = 9
    ms = [2, 2, 3, 3, 3, 3, 3, 3, 3]
    product = 1
    for m in ms:
        product *= m

    print("=" * 70)
    print(f"EXHAUSTIVE BINARY RULE SEARCH AT PRODUCT {product}")
    print(f"ms = {ms}")
    print("=" * 70)

    t0 = time.time()

    # Build all configs
    all_configs = list(cartesian(*(range(m) for m in ms)))
    print(f"Total configs: {len(all_configs)}")

    # Pre-compute ternary processor privileges for all configs
    # Ternary procs: P2-P7 (middle), P8 (top)
    ternary_fs = {
        2: sol3_middle, 3: sol3_middle, 4: sol3_middle,
        5: sol3_middle, 6: sol3_middle, 7: sol3_middle,
        8: sol3_top,
    }

    ternary_priv = {}  # config -> set of privileged ternary procs
    for c in all_configs:
        privs = set()
        for i in [2, 3, 4, 5, 6, 7, 8]:
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if ternary_fs[i](L, S, R) != S:
                privs.add(i)
        ternary_priv[c] = privs

    # Configs where NO ternary proc is privileged → binary must cover
    no_ternary = [c for c in all_configs if len(ternary_priv[c]) == 0]
    print(f"Configs with no ternary privilege: {len(no_ternary)}")

    # For these configs, at least one of P0 or P1 must be privileged
    # P0: L = c[8] (ternary, 0-2), S = c[0] (binary, 0-1), R = c[1] (binary, 0-1)
    # P1: L = c[0] (binary, 0-1), S = c[1] (binary, 0-1), R = c[2] (ternary, 0-2)

    # Extract the (L,S,R) tuples that need at least one binary privileged
    must_cover = []
    for c in no_ternary:
        # P0 entry: (c[8], c[0], c[1])
        p0_key = (c[8], c[0], c[1])
        # P1 entry: (c[0], c[1], c[2])
        p1_key = (c[0], c[1], c[2])
        must_cover.append((p0_key, p1_key))

    print(f"Coverage constraints: {len(must_cover)}")

    # P0 entries: (L, S, R) where L ∈ {0,1,2}, S ∈ {0,1}, R ∈ {0,1}
    # Each entry f0(L,S,R) ∈ {0,1}. Privileged if f0 ≠ S.
    # f0(L,S,R) = 1-S means privileged, f0(L,S,R) = S means not privileged.

    p0_entries = [(L, S, R) for L in range(3) for S in range(2) for R in range(2)]
    p1_entries = [(L, S, R) for L in range(2) for S in range(2) for R in range(3)]

    print(f"P0 entries: {len(p0_entries)} (each binary choice)")
    print(f"P1 entries: {len(p1_entries)} (each binary choice)")

    # For each entry, "privileged" means f(L,S,R) = 1-S
    # We represent each rule as a bitmask: bit i = 1 means entry i is privileged
    # P0: 12 entries → 2^12 = 4096 possible rules
    # P1: 12 entries → 2^12 = 4096 possible rules

    # For each must_cover pair, at least one of (P0 privileged at p0_key) or
    # (P1 privileged at p1_key) must be true.
    # P0 privileged at (L,S,R) ↔ f0(L,S,R) = 1-S ↔ bit(p0_idx) = 1
    # P1 privileged at (L,S,R) ↔ f1(L,S,R) = 1-S ↔ bit(p1_idx) = 1

    p0_idx = {k: i for i, k in enumerate(p0_entries)}
    p1_idx = {k: i for i, k in enumerate(p1_entries)}

    # Build constraint: for each must_cover pair, p0_bit OR p1_bit
    cover_constraints = []
    for p0_key, p1_key in must_cover:
        cover_constraints.append((p0_idx[p0_key], p1_idx[p1_key]))

    # Deduplicate
    cover_constraints = list(set(cover_constraints))
    print(f"Unique coverage constraints: {len(cover_constraints)}")

    # Filter P0 rules: for each P0 bitmask, check which P1 bits are forced
    # This is a constraint satisfaction problem on 24 bits
    # But 4096 × 4096 = 16M is still manageable with fast inner loop

    # Let's be smarter: for each P0 rule, compute which P1 entries MUST be privileged
    # (those where P0 is NOT privileged at the corresponding must_cover config)
    print(f"\nEnumerating P0 rules...")

    valid_combos = []
    n_p0_valid = 0

    for p0_mask in range(1 << 12):
        # For this P0 rule, which P1 entries are forced?
        p1_forced_bits = set()
        for p0_bit, p1_bit in cover_constraints:
            if not (p0_mask & (1 << p0_bit)):
                # P0 is NOT privileged → P1 MUST be privileged
                p1_forced_bits.add(p1_bit)

        # P1 must have all forced bits set (and can freely set others)
        p1_forced_mask = 0
        for b in p1_forced_bits:
            p1_forced_mask |= (1 << b)

        # Count valid P1 rules: those that have all forced bits set
        n_free = 12 - len(p1_forced_bits)
        n_valid_p1 = 1 << n_free  # 2^(free bits)

        if n_valid_p1 > 0:
            n_p0_valid += 1
            # Don't store all — just enumerate later
            valid_combos.append((p0_mask, p1_forced_mask, n_free))

        if (p0_mask + 1) % 1000 == 0:
            print(f"  P0 rule {p0_mask + 1}/4096, valid so far: {n_p0_valid}")

    total_valid = sum(1 << nf for _, _, nf in valid_combos)
    print(f"\nValid P0 rules: {n_p0_valid}/4096")
    print(f"Total valid (P0, P1) combos: {total_valid}")

    # Now verify each valid combo
    # For speed, pre-compute the ternary successor map
    print(f"\nPre-computing ternary transitions...")
    # For each non-good config, compute ternary successors
    # (We'll need this for convergence checking)

    # Actually, let's just enumerate combos and verify with verify_system
    # But 16M is too many. Let me be smarter.

    # Pre-filter: check if the good-set structure makes sense
    # For verify_system, we need ALL 5 properties. The bottleneck is convergence.
    # Let's do a faster pre-check: build the full rule table, find single-privilege
    # configs, check if they form a cycle, then check convergence.

    # But even this is O(8748) per combo...
    # With total_valid combos, this could be too slow.

    if total_valid > 100000:
        print(f"\n  Too many combos ({total_valid}). Trying structured sub-search...")
        # Use Sol 3 v1 adaptation for the binary procs as a starting point
        # and perturb locally

        # Sol 3 v1 for P0 (bottom, m=2):
        # f(L,S,R) = (S-1)%2 if (S+1)%2 == R%2
        # = 1-S if (S+1)%2 == R%2
        # = 1-S if S = R (when R ∈ {0,1}: (0+1)%2=1==R%2 ↔ R%2=1 ↔ R=1;
        #   (1+1)%2=0==R%2 ↔ R%2=0 ↔ R=0. So privileged when (S+1)%2 == R mod 2.)
        base_p0 = 0
        for idx, (L, S, R) in enumerate(p0_entries):
            if (S + 1) % 2 == R % 2:
                base_p0 |= (1 << idx)

        # Sol 3 v1 for P1 (middle, m=2):
        # f(L,S,R) = L%2 if (S+1)%2 == L%2
        # else R%2 if (S+1)%2 == R%2
        # else S
        base_p1 = 0
        for idx, (L, S, R) in enumerate(p1_entries):
            if (S + 1) % 2 == L % 2:
                base_p1 |= (1 << idx)
            elif (S + 1) % 2 == R % 2:
                base_p1 |= (1 << idx)

        print(f"\n  Base P0 mask: {bin(base_p0)}")
        print(f"  Base P1 mask: {bin(base_p1)}")

        # Try Hamming distance 1, 2, 3 perturbations from base
        best_result = None
        for dist in range(5):
            print(f"\n  Searching Hamming distance {dist} from Sol 3 v1...")
            found = False

            if dist == 0:
                combos_to_try = [(base_p0, base_p1)]
            else:
                # Generate all masks at distance dist from base
                combos_to_try = []
                # Perturb P0 with 0..dist bits, P1 with dist-k bits
                from itertools import combinations
                for k in range(dist + 1):
                    p0_flips = list(combinations(range(12), k))
                    p1_flips = list(combinations(range(12), dist - k))
                    for p0f in p0_flips:
                        p0m = base_p0
                        for b in p0f:
                            p0m ^= (1 << b)
                        for p1f in p1_flips:
                            p1m = base_p1
                            for b in p1f:
                                p1m ^= (1 << b)
                            combos_to_try.append((p0m, p1m))

            print(f"    Combos to try: {len(combos_to_try)}")

            n_tested = 0
            n_liveness_pass = 0
            for p0m, p1m in combos_to_try:
                n_tested += 1

                # Check liveness (all must_cover satisfied)
                liveness_ok = True
                for p0_bit, p1_bit in cover_constraints:
                    if not ((p0m & (1 << p0_bit)) or (p1m & (1 << p1_bit))):
                        liveness_ok = False
                        break
                if not liveness_ok:
                    continue
                n_liveness_pass += 1

                # Build rule table and verify
                def make_p0(mask):
                    def f(L, S, R):
                        idx = p0_idx[(L, S, R)]
                        if mask & (1 << idx):
                            return 1 - S
                        return S
                    return f

                def make_p1(mask):
                    def f(L, S, R):
                        idx = p1_idx[(L, S, R)]
                        if mask & (1 << idx):
                            return 1 - S
                        return S
                    return f

                fs = [make_p0(p0m), make_p1(p1m)]
                for i in range(2, 8):
                    fs.append(sol3_middle)
                fs.append(sol3_top)

                result = verify_system(ms, fs)
                if result.get('valid', False):
                    print(f"\n    *** VALID SYSTEM FOUND at distance {dist}! ***")
                    print(f"    P0 mask: {bin(p0m)}")
                    print(f"    P1 mask: {bin(p1m)}")
                    props = result.get('properties', {})
                    for k, v in props.items():
                        print(f"      {k}: {v}")
                    found = True
                    best_result = result
                    break

            print(f"    Tested: {n_tested}, liveness pass: {n_liveness_pass}")

            if found:
                break

        if best_result:
            elapsed = time.time() - t0
            print(f"\n  Total time: {elapsed:.1f}s")
        else:
            print(f"\n  No valid system found within Hamming distance 4.")
            elapsed = time.time() - t0
            print(f"  Total time: {elapsed:.1f}s")

    else:
        # Few enough to enumerate all
        print(f"\n  Enumerating all {total_valid} valid combos...")
        n_tested = 0
        for p0_mask, p1_forced, n_free in valid_combos:
            # Enumerate P1 rules with forced bits set
            free_bits = [b for b in range(12) if not (p1_forced & (1 << b))]
            for fb_mask in range(1 << n_free):
                p1_mask = p1_forced
                for j, b in enumerate(free_bits):
                    if fb_mask & (1 << j):
                        p1_mask |= (1 << b)

                n_tested += 1

                # Build and verify
                def make_p0(mask):
                    def f(L, S, R):
                        idx = p0_idx[(L, S, R)]
                        if mask & (1 << idx):
                            return 1 - S
                        return S
                    return f

                def make_p1(mask):
                    def f(L, S, R):
                        idx = p1_idx[(L, S, R)]
                        if mask & (1 << idx):
                            return 1 - S
                        return S
                    return f

                fs = [make_p0(p0_mask), make_p1(p1_mask)]
                for i in range(2, 8):
                    fs.append(sol3_middle)
                fs.append(sol3_top)

                result = verify_system(ms, fs)
                if result.get('valid', False):
                    print(f"\n  *** VALID SYSTEM FOUND! ***")
                    props = result.get('properties', {})
                    for k, v in props.items():
                        print(f"    {k}: {v}")
                    break

                if n_tested % 10000 == 0:
                    elapsed = time.time() - t0
                    print(f"  Tested {n_tested}/{total_valid} ({elapsed:.1f}s)")
            else:
                continue
            break


if __name__ == "__main__":
    main()
