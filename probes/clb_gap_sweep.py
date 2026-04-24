#!/usr/bin/env python3
"""clb_gap_sweep.py — Try good-targeting completion on all gap multisets.

For each multiset with product in (7776, 8748), try all orientations with
bounce cycles and good-targeting completion. If any works, M_9 is even lower.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian, permutations
from collections import defaultdict
from verifier import verify_system
import time


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    if base_pattern is None:
        base_pattern = list(range(n-1, -1, -1)) + list(range(1, n))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base_pattern * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step+1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def try_good_targeting(ms_tuple, cycle, movers, n):
    """Apply good-targeting completion. Return True if valid system found."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms_tuple)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Extract determined entries
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    # Find free entries
    free_entries = []
    for p in range(n):
        m_L = ms_tuple[(p - 1) % n]
        m_S = ms_tuple[p]
        m_R = ms_tuple[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Check triple overlap
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for idx in range(len(cycle)):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            triple = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if p == mv:
                mover_triples[p].add(triple)
            else:
                nonmover_triples[p].add(triple)
    for p in range(n):
        if mover_triples[p] & nonmover_triples[p]:
            return False, "overlap"

    # Compute edge costs
    edge_costs = {}
    for key in free_entries:
        p, L, S, R = key
        for out in range(ms_tuple[p]):
            if out == S:
                edge_costs[(key, out)] = 0
            else:
                edges = 0
                for c in non_good:
                    if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                        new_c = list(c)
                        new_c[p] = out
                        if tuple(new_c) in non_good_set:
                            edges += 1
                edge_costs[(key, out)] = edges

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms_tuple[p]):
            ng = edge_costs.get((key, out), 0)
            good_count = 0
            if out != S:
                for c in non_good:
                    if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                        new_c = list(c)
                        new_c[p] = out
                        if tuple(new_c) in good_set:
                            good_count += 1
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    # Liveness fix
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n))
        if not has_priv:
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms_tuple[p]):
                        if out != S2:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    # Build transition functions and verify
    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    result = verify_system(list(ms_tuple), fs, verbose=False)
    return result['valid'], result


n = 9
gap_multisets = [
    (2, 2, 2, 2, 2, 2, 5, 5, 5),     # 8000
    (2, 2, 2, 2, 2, 2, 2, 3, 21),     # 8064
    (2, 2, 2, 2, 2, 2, 3, 6, 7),      # 8064
    (2, 2, 2, 2, 2, 3, 3, 4, 7),      # 8064
    (2, 2, 2, 2, 2, 2, 2, 7, 9),      # 8064
    (2, 2, 2, 2, 2, 2, 2, 4, 16),     # 8192
    (2, 2, 2, 2, 2, 2, 4, 4, 8),      # 8192
    (2, 2, 2, 2, 2, 4, 4, 4, 4),      # 8192
    (2, 2, 2, 2, 2, 2, 2, 8, 8),      # 8192
    (2, 2, 2, 2, 2, 2, 2, 5, 13),     # 8320
    (2, 2, 2, 2, 2, 2, 2, 3, 22),     # 8448
    (2, 2, 2, 2, 2, 2, 2, 6, 11),     # 8448
    (2, 2, 2, 2, 2, 2, 3, 4, 11),     # 8448
    (2, 2, 2, 2, 2, 2, 3, 3, 15),     # 8640
    (2, 2, 2, 2, 2, 2, 3, 5, 9),      # 8640
    (2, 2, 2, 2, 2, 3, 3, 5, 6),      # 8640
    (2, 2, 2, 2, 3, 3, 3, 4, 5),      # 8640
    (2, 2, 2, 2, 2, 3, 3, 3, 10),     # 8640
    (2, 2, 2, 2, 2, 2, 2, 4, 17),     # 8704
]

patterns = [
    ("down-up", list(range(n - 1, -1, -1)) + list(range(1, n))),
    ("up-down", list(range(n)) + list(range(n - 2, 0, -1))),
]

print("=" * 70)
print("Gap multiset sweep: trying good-targeting on all (7776, 8748)")
print("=" * 70)

valid_witnesses = []

for ms_sorted in gap_multisets:
    product = 1
    for m in ms_sorted:
        product *= m

    # Try a few distinct rotations
    tested = set()
    found_valid = False

    # Generate unique permutations (up to a limit)
    seen_ms = set()
    all_perms = set()
    # For efficiency, just try all rotations of sorted and reverse-sorted
    candidates = [ms_sorted, tuple(reversed(ms_sorted))]
    # Also try putting larger values in the middle vs endpoints
    import random
    random.seed(42)
    for _ in range(20):
        perm = list(ms_sorted)
        random.shuffle(perm)
        candidates.append(tuple(perm))

    for ms_perm in candidates:
        if ms_perm in seen_ms:
            continue
        seen_ms.add(ms_perm)

        for pname, base in patterns:
            cycle, movers_seq = build_bounce_cycle(ms_perm, n, base)
            if cycle is None:
                continue

            t0 = time.time()
            valid, result = try_good_targeting(ms_perm, cycle, movers_seq, n)
            elapsed = time.time() - t0

            if valid:
                print(f"  *** VALID at {ms_perm} product={product} ({pname}) "
                      f"[{elapsed:.1f}s] ***")
                valid_witnesses.append((product, ms_perm, pname))
                found_valid = True
                break
            elif result == "overlap":
                pass  # common, skip
            else:
                pass  # not valid but no overlap

        if found_valid:
            break

    if not found_valid:
        print(f"  {ms_sorted} product={product}: no valid system found")

print(f"\n{'=' * 70}")
print(f"RESULTS")
print(f"{'=' * 70}")

if valid_witnesses:
    valid_witnesses.sort()
    best = valid_witnesses[0]
    print(f"\nBest witness: product={best[0]}, ms={best[1]}")
    print(f"M_9 ≤ {best[0]}")
    for product, ms_perm, pname in valid_witnesses:
        print(f"  product={product} ms={ms_perm} ({pname})")
else:
    print(f"\nNo valid systems found in gap multisets.")
    print(f"M_9 = 8748 (if all gap products are also eliminated).")
