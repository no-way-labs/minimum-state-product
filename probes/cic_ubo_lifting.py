#!/usr/bin/env python3
"""CIC Exploration 7: UBO Lifting — does binary overlap extend to full space?

The UBO theorem gives an overlap in the binary subspace projection for any
walk through 3 consecutive binary processors. But does this overlap create
a CONTRADICTION in the full configuration space?

At n=4 with 1 non-binary processor: overlap doesn't kill (valid systems exist).
At n=9 with 6+ non-binary processors: overlap might kill (no valid systems found).

Question: Is there an n threshold above which UBO overlap always extends?

Key insight: The overlap gives a pair of steps (k1, k2) where binary processor
p_mid sees the same (L_bin, R_bin) in both a mover and non-mover context.
In the full space, the non-binary neighbors of p_mid may differ between k1 and k2.
If they DO differ, the overlap is in different "full neighborhoods" and doesn't
create a contradiction.

For the overlap to create a contradiction, the FULL neighborhood (including
non-binary parts) must be the same at both steps. This is guaranteed by the
sweep structure (waterfall) but not by arbitrary walks.

This script checks: at what n does the UBO overlap start killing ALL cycles
(not just sweeps)?
"""

from itertools import product as iproduct
from collections import Counter
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))


def enumerate_good_cycles(ms, n, max_cycles=100, max_time=15.0):
    """Enumerate good cycles via DFS."""
    t0 = time.time()
    product_val = 1
    for m in ms:
        product_val *= m
    if product_val > 500:
        return []

    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []

    for start_idx in range(min(len(all_configs), product_val)):
        if time.time() - t0 > max_time:
            break
        start = all_configs[start_idx]
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 300000:
            if time.time() - t0 > max_time:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue
                    new_det = dict(det)
                    consistent = True
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si
                    if not consistent:
                        continue
                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    if new_config == start and len(path) >= n:
                        me_ok = True
                        for idx in range(len(path)):
                            c = path[idx]
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle_tup = tuple(path)
                            if cycle_tup not in [tuple(c)
                                                  for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if new_config not in set(path) and len(path) < 5 * n:
                        stack.append((
                            new_config,
                            path + [new_config],
                            new_det,
                            movers + [p]
                        ))
    return cycles


def complete_and_verify(cycle, movers, det, ms, n):
    """Complete a good cycle to a full system and verify."""
    from verifier import verify_system
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            good_count = 0
            ng_count = 0
            for c in non_good:
                if (c[(p - 1) % n] == L and c[p] == S
                        and c[(p + 1) % n] == R):
                    new_c = list(c)
                    new_c[p] = out
                    nc = tuple(new_c)
                    if nc in good_set:
                        good_count += 1
                    elif nc in non_good_set:
                        ng_count += 1
            if out != S:
                if (good_count > best_good or
                        (good_count == best_good and ng_count < best_ng)):
                    best_out = out
                    best_good = good_count
                    best_ng = ng_count
        comp[key] = best_out

    fs = []
    for p in range(n):
        t = {}
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    t[(L, S, R)] = comp.get((p, L, S, R), S)
        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

    return verify_system(ms, fs)


# ============================================================
# Check: at what n do sub-threshold systems with 3 consecutive
# binary cease to exist?
# ============================================================
print("=" * 70)
print("SUB-THRESHOLD VALID SYSTEMS WITH 3 CONSECUTIVE BINARY")
print("=" * 70)

# For each n, try ms with 3 consecutive binary at positions 0,1,2
# and one non-binary (ternary or larger) at remaining positions
results = []

for n in range(4, 9):
    threshold = 4 * (3 ** (n - 2))
    # ms = (2, 2, 2, m, m, ..., m) where m chosen to be sub-threshold
    # Need product = 8 * m^(n-3) < 4 * 3^(n-2)
    # m^(n-3) < 3^(n-2) / 2
    # For m=3: 3^(n-3) < 3^(n-2)/2 = 3^(n-3)*3/2. Always true.
    # So ms = (2,2,2,3,...,3) has product 8*3^(n-3) = 8/3 * 3^(n-2)

    ms_ternary = tuple([2, 2, 2] + [3] * (n - 3))
    prod = 1
    for m in ms_ternary:
        prod *= m

    print(f"\nn={n}: ms={list(ms_ternary)}, product={prod}, "
          f"threshold={threshold}")
    print(f"  Sub-threshold: {prod < threshold}")

    if prod > 500:
        print(f"  Product too large for exhaustive search")
        continue

    cycles = enumerate_good_cycles(ms_ternary, n, max_cycles=50,
                                    max_time=30.0)
    print(f"  Candidate cycles: {len(cycles)}")

    valid_count = 0
    for cycle, movers, det in cycles:
        result = complete_and_verify(cycle, movers, det, ms_ternary, n)
        if result.get('valid', False):
            valid_count += 1

    print(f"  Valid systems: {valid_count}")
    results.append((n, list(ms_ternary), prod, threshold, len(cycles),
                     valid_count))

    # Also try with quaternary
    if n >= 5:
        ms_quat = tuple([2, 2, 2] + [4] + [3] * (n - 4))
        prod_q = 1
        for m in ms_quat:
            prod_q *= m
        if prod_q < threshold and prod_q <= 500:
            print(f"\n  Also: ms={list(ms_quat)}, product={prod_q}")
            cycles_q = enumerate_good_cycles(ms_quat, n, max_cycles=50,
                                              max_time=15.0)
            valid_q = 0
            for cycle, movers, det in cycles_q:
                result = complete_and_verify(cycle, movers, det,
                                             ms_quat, n)
                if result.get('valid', False):
                    valid_q += 1
            print(f"  Candidate cycles: {len(cycles_q)}, "
                  f"Valid: {valid_q}")

# ============================================================
# Check: NON-consecutive binary at small n
# ============================================================
print(f"\n{'=' * 70}")
print("NON-CONSECUTIVE BINARY AT SMALL n")
print("=" * 70)

non_consec_systems = [
    # n=4, binary at 0 and 2 (non-consecutive)
    (4, (2, 3, 2, 3)),   # product 36
    (4, (2, 4, 2, 3)),   # product 48
    # n=5, binary at 0, 2, 4 (non-consecutive)
    (5, (2, 3, 2, 3, 2)),  # product 72
    (5, (2, 3, 2, 3, 3)),  # product 108
    (5, (2, 4, 2, 3, 2)),  # product 96
    # n=5, binary at 0, 3 (gap of 2)
    (5, (2, 3, 3, 2, 3)),  # product 108
]

for n, ms in non_consec_systems:
    prod = 1
    for m in ms:
        prod *= m
    threshold = 4 * (3 ** (n - 2))
    k = sum(1 for m in ms if m == 2)
    bin_pos = [i for i, m in enumerate(ms) if m == 2]

    if prod > 500:
        print(f"\n  n={n}, ms={list(ms)}: product {prod} too large")
        continue

    cycles = enumerate_good_cycles(ms, n, max_cycles=50, max_time=15.0)
    valid_count = 0
    for cycle, movers, det in cycles:
        result = complete_and_verify(cycle, movers, det, ms, n)
        if result.get('valid', False):
            valid_count += 1

    print(f"\n  n={n}, ms={list(ms)}, product={prod}, threshold={threshold}")
    print(f"  k={k} binary at {bin_pos}")
    print(f"  Candidate cycles: {len(cycles)}, Valid: {valid_count}")


# ============================================================
# Summary
# ============================================================
print(f"\n{'=' * 70}")
print("SUMMARY: SUB-THRESHOLD VALID SYSTEMS vs n")
print("=" * 70)

for n, ms, prod, threshold, cycles, valid in results:
    status = "EXISTS" if valid > 0 else "NONE"
    print(f"  n={n}: ms={str(ms):25s} prod={prod:5d} "
          f"threshold={threshold:5d} valid={valid:3d} [{status}]")

print("""
If valid systems DISAPPEAR at some n = n*:
  → For n >= n*, shadow argument covers everything (even non-sweep)
  → The "complexity" of walks can't overcome the product constraint
  → M_n = 4·3^(n-2) proof is complete for n >= n*

If valid systems persist at all n:
  → Need a different approach for non-sweep cycles
  → The proof has a genuine analytical gap
""")
