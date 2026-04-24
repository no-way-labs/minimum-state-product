#!/usr/bin/env python3
"""clb_binary_2cycle.py — The Binary 2-Cycle Lemma and its consequences.

KEY INSIGHT: For a binary processor p (m_p=2), if both (L,0,R) and (L,1,R)
are toggle triples (f_p maps 0→1 and 1→0), then configs differing only at p
form 2-cycles. For convergence, at least one of each pair must be in the good
cycle. This severely constrains the good cycle length.

This is the fundamental reason why 2+ binary processors are fatal at n≥9.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
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


n = 9

# ============================================================
# Part 1: The Binary 2-Cycle Lemma — formal statement and proof
# ============================================================

print("=" * 70)
print("Part 1: Binary 2-Cycle Lemma")
print("=" * 70)

print("""
LEMMA (Binary 2-Cycle): Let p be a binary processor (m_p = 2) in a valid
self-stabilizing system. Let (L, R) be a fixed assignment of p's neighbors.
If BOTH triples (L, 0, R) and (L, 1, R) are mover triples for p, then
for every assignment of "remote" positions (all positions except p-1, p, p+1),
at least one of the two configs (with p=0 or p=1) must be in the good cycle.

PROOF: If both triples are mover triples, then:
  f_p(L, 0, R) = 1  (toggle: only option since m_p=2 and f≠S)
  f_p(L, 1, R) = 0  (toggle: only option since m_p=2 and f≠S)

For configs c = (remote, L, 0, R) and c' = (remote, L, 1, R):
  - Processor p is privileged at both c and c'
  - p moves c to c' (0→1) and c' to c (1→0)
  - This is a 2-cycle in the transition graph

For convergence, the non-good transition graph must be acyclic.
So at least one of c, c' must be in the good cycle. QED.

COROLLARY: For each "double toggle" (L,R) pair, the good cycle must contain
at least N_remote configs, where N_remote = product / (m_{p-1} * m_p * m_{p+1}).
""")

# ============================================================
# Part 2: Verify the lemma on our endpoint binary cycle
# ============================================================

print("=" * 70)
print("Part 2: Verify on endpoint binary bounce cycle")
print("=" * 70)

ms = (2, 3, 3, 3, 3, 3, 3, 3, 2)
up_down = list(range(n)) + list(range(n-2, 0, -1))
cycle, movers = build_bounce_cycle(ms, n, up_down)
good_set = set(cycle)
all_configs = list(cartesian(*(range(m) for m in ms)))
non_good_set = set(c for c in all_configs if c not in good_set)

# Extract mover triples
mover_triples = defaultdict(set)
for idx in range(len(cycle)):
    c = cycle[idx]
    mover = movers[idx]
    L = c[(mover - 1) % n]
    S = c[mover]
    R = c[(mover + 1) % n]
    mover_triples[mover].add((L, S, R))

print("Mover triples from good cycle:")
for p in [0, 8]:
    print(f"  P{p}: {sorted(mover_triples[p])}")

# Check which (L,R) patterns have BOTH triples as mover
print("\nDouble-toggle analysis:")
for p in [0, 8]:
    m_L = ms[(p - 1) % n]
    m_R = ms[(p + 1) % n]
    print(f"\n  P{p} (m_L={m_L}, m_R={m_R}):")
    for L in range(m_L):
        for R in range(m_R):
            t0 = (L, 0, R)
            t1 = (L, 1, R)
            mt0 = t0 in mover_triples[p]
            mt1 = t1 in mover_triples[p]
            if mt0 and mt1:
                status = "DOUBLE TOGGLE ⚠"
            elif mt0 or mt1:
                status = "single toggle"
            else:
                status = "no toggle"
            print(f"    (L={L},R={R}): ({t0}={'M' if mt0 else '-'}, {t1}={'M' if mt1 else '-'}) {status}")

# ============================================================
# Part 3: Check SCCs — are they caused by binary 2-cycles?
# ============================================================

print("\n" + "=" * 70)
print("Part 3: Are SCCs in max-privilege completion caused by 2-cycles?")
print("=" * 70)

# Build max-privilege completion
det = {}
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx + 1) % len(cycle)]
    mover = movers[idx]
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        if p == mover:
            det[key] = c_next[p]
        else:
            det[key] = S

comp_max = dict(det)
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
                    choices = [v for v in range(ms[p]) if v != S]
                    comp_max[key] = choices[0] if choices else S

# For each free entry at a binary processor, check if it creates a double toggle
print("\nFree entries at binary processors:")
binary_double_toggles = []
for key in free_entries:
    p, L, S, R = key
    if ms[p] != 2:
        continue
    other_S = 1 - S
    partner_key = (p, L, other_S, R)
    partner_is_toggle = comp_max.get(partner_key, other_S) != other_S
    this_is_toggle = comp_max.get(key, S) != S

    if this_is_toggle and partner_is_toggle:
        binary_double_toggles.append((p, L, R))
        # Count 2-cycles this creates
        twocycles = 0
        for c in all_configs:
            if c[(p - 1) % n] == L and c[p] == 0 and c[(p + 1) % n] == R:
                c0 = c
                c1 = tuple(c[j] if j != p else 1 for j in range(n))
                if c0 in non_good_set and c1 in non_good_set:
                    twocycles += 1
        print(f"  P{p} ({L},*,{R}): double toggle, {twocycles} 2-cycles in non-good")

# Count total 2-cycles from binary double toggles
total_binary_2cycles = 0
for p, L, R in binary_double_toggles:
    for c in all_configs:
        if c[(p - 1) % n] == L and c[p] == 0 and c[(p + 1) % n] == R:
            c1 = tuple(c[j] if j != p else 1 for j in range(n))
            if c in non_good_set and c1 in non_good_set:
                total_binary_2cycles += 1

print(f"\nTotal binary 2-cycles: {total_binary_2cycles}")

# Also check ternary processors for 2-cycles
ternary_2cycles = 0
for key in free_entries:
    p, L, S, R = key
    if ms[p] == 2:
        continue
    new_S = comp_max[key]
    if new_S == S:
        continue
    # Check if reverse transition also exists
    reverse_key = (p, L, new_S, R)
    reverse_output = comp_max.get(reverse_key, new_S)
    if reverse_output == S:
        # Found a 2-cycle pattern at ternary processor
        for c in all_configs:
            if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                c_next = tuple(c[j] if j != p else new_S for j in range(n))
                if c in non_good_set and c_next in non_good_set:
                    ternary_2cycles += 1
                    break  # just count patterns, not configs

print(f"Ternary 2-cycle patterns: {ternary_2cycles}")

# ============================================================
# Part 4: The cycle length lower bound
# ============================================================

print("\n" + "=" * 70)
print("Part 4: Cycle length lower bound from Binary 2-Cycle Lemma")
print("=" * 70)

# For ms=(2,2,3,3,3,3,3,3,3), how long must the cycle be?
ms_adj = (2, 2, 3, 3, 3, 3, 3, 3, 3)
product = 8748
print(f"ms = {ms_adj}, product = {product}")

for p in [0, 1]:  # binary positions
    m_L = ms_adj[(p - 1) % n]
    m_S = ms_adj[p]
    m_R = ms_adj[(p + 1) % n]
    T = m_L * m_S * m_R
    n_patterns = m_L * m_R
    configs_per = product // T

    print(f"\nP{p}: {T} triples = {n_patterns} (L,R) patterns × 2 states")
    print(f"  Configs per triple: {configs_per}")
    print(f"  Max single-toggle coverage: {n_patterns} × {configs_per} = "
          f"{n_patterns * configs_per} ({n_patterns * configs_per / product * 100:.0f}%)")
    print(f"  Each double-toggle pattern forces {configs_per} good cycle configs")

# For the endpoint binary case:
ms_end = (2, 3, 3, 3, 3, 3, 3, 3, 2)
product_end = 8748
print(f"\nms = {ms_end}, product = {product_end}")

for p in [0, 8]:
    m_L = ms_end[(p - 1) % n]
    m_S = ms_end[p]
    m_R = ms_end[(p + 1) % n]
    T = m_L * m_S * m_R
    n_patterns = m_L * m_R
    configs_per = product_end // T

    print(f"\nP{p}: {T} triples = {n_patterns} (L,R) patterns × 2 states")
    print(f"  Configs per triple: {configs_per}")
    print(f"  Max single-toggle coverage: {n_patterns} × {configs_per} = "
          f"{n_patterns * configs_per} ({n_patterns * configs_per / product_end * 100:.0f}%)")
    print(f"  Each double-toggle pattern forces {configs_per} good cycle configs")

# ============================================================
# Part 5: Can ternary processors cover the gap?
# ============================================================

print("\n" + "=" * 70)
print("Part 5: Ternary coverage gap analysis")
print("=" * 70)

# For each possible "good cycle triple partition," compute:
# 1. How many configs are NOT covered by ternary processors alone
# 2. How many of those can be covered by single toggles at binary
# 3. How many need double toggles (expensive)

# For a cycle of length L at ms=(2,3,3,3,3,3,3,3,2):
# Each ternary P_i has ~L/9 mover triples and ~8L/9 non-mover triples
# from the cycle, plus T_i - (mover + nonmover) free triples.

# The CRITICAL computation: for each (L,R) pattern at binary P0,
# how many configs with that pattern are NOT covered by P1-P8?

ms_test = ms_end  # endpoint binary
print(f"Testing ms = {ms_test}")

# For the ACTUAL bounce cycle, compute uncovered configs per (L,R) pattern
# First, identify what triples at each ternary processor are determined

# Already have det from above. Build the triple partition.
det_triples_cycle = defaultdict(lambda: {'mover': set(), 'nonmover': set()})
for idx in range(len(cycle)):
    c = cycle[idx]
    mover = movers[idx]
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        triple = (L, S, R)
        if p == mover:
            det_triples_cycle[p]['mover'].add(triple)
        else:
            det_triples_cycle[p]['nonmover'].add(triple)

# For each config, check if it's covered by ternary processors' MOVER triples only
ternary_covered = set()
for c in all_configs:
    for p in range(1, 8):  # P1-P7 are ternary
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        triple = (L, S, R)
        if triple in det_triples_cycle[p]['mover']:
            ternary_covered.add(c)
            break

print(f"\nConfigs covered by ternary mover triples alone: {len(ternary_covered)}")
print(f"Configs NOT covered: {len(all_configs) - len(ternary_covered)}")

# Break down uncovered by binary (P0, P8) pattern
uncovered = set(all_configs) - ternary_covered
uncov_by_pattern = defaultdict(int)
for c in uncovered:
    uncov_by_pattern[(c[0], c[8])] += 1

print(f"\nUncovered configs by (P0, P8) state:")
for (p0, p8), count in sorted(uncov_by_pattern.items()):
    in_good = sum(1 for c in uncovered if c[0] == p0 and c[8] == p8 and c in good_set)
    print(f"  (P0={p0}, P8={p8}): {count} uncovered, {in_good} in good cycle")

# How many uncovered configs can be saved by P0's cycle mover triples?
p0_saved = 0
for c in uncovered:
    L = c[(0 - 1) % n]
    S = c[0]
    R = c[(0 + 1) % n]
    if (L, S, R) in det_triples_cycle[0]['mover']:
        p0_saved += 1

p8_saved = 0
for c in uncovered:
    L = c[(8 - 1) % n]
    S = c[8]
    R = c[(8 + 1) % n]
    if (L, S, R) in det_triples_cycle[8]['mover']:
        p8_saved += 1

print(f"\nOf {len(uncovered)} uncovered configs:")
print(f"  Saved by P0 cycle mover triples: {p0_saved}")
print(f"  Saved by P8 cycle mover triples: {p8_saved}")

# What about free triples at binary processors (single toggle)?
free_binary_triples = defaultdict(set)
for key in free_entries:
    p, L, S, R = key
    if ms_test[p] == 2:
        free_binary_triples[p].add((L, S, R))

print(f"\nFree triples at binary processors:")
for p in [0, 8]:
    print(f"  P{p}: {len(free_binary_triples[p])} free triples: {sorted(free_binary_triples[p])}")

# For each free triple at P0/P8, compute:
# 1. How many uncovered configs it would save (as single toggle)
# 2. Whether its partner triple is also free (enabling double toggle)
print(f"\nFree triple analysis:")
for p in [0, 8]:
    m_L = ms_test[(p - 1) % n]
    m_R = ms_test[(p + 1) % n]
    for triple in sorted(free_binary_triples[p]):
        L, S, R = triple
        partner = (L, 1 - S, R)
        partner_free = partner in free_binary_triples[p]
        partner_mover = partner in det_triples_cycle[p]['mover']
        partner_nonmover = partner in det_triples_cycle[p]['nonmover']

        # Count uncovered configs this would save
        saves = 0
        for c in uncovered:
            if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                saves += 1

        # If partner is also free and we make both toggle, how many 2-cycles?
        twocycles = 0
        if partner_free:
            for c in all_configs:
                if (c[(p - 1) % n] == L and c[p] == 0 and c[(p + 1) % n] == R
                        and c not in good_set):
                    c1 = tuple(c[j] if j != p else 1 for j in range(n))
                    if c1 not in good_set:
                        twocycles += 1

        status = "partner: "
        if partner_free:
            status += f"FREE → double toggle creates {twocycles} 2-cycles"
        elif partner_mover:
            status += "MOVER → single toggle OK (no 2-cycle)"
        elif partner_nonmover:
            status += "NONMOVER → single toggle OK"

        print(f"  P{p} ({L},{S},{R}): saves {saves} uncovered. {status}")

# ============================================================
# Part 6: The PUNCHLINE — total accounting
# ============================================================

print(f"\n{'=' * 70}")
print(f"Part 6: Total accounting — why product 8748 fails")
print(f"{'=' * 70}")

# Compute: if we use ALL safe toggles (single toggles only),
# how many configs remain uncovered?

safe_toggles = {}  # free entries that can safely be made toggle
for key in free_entries:
    p, L, S, R = key
    if ms_test[p] != 2:
        # Ternary: any free entry can potentially be toggle
        # (no involution constraint — but need to check for 2-cycles with ternary)
        safe_toggles[key] = True
        continue

    # Binary: check if partner triple is also free
    partner_triple = (L, 1 - S, R)
    if partner_triple in free_binary_triples[p]:
        # Both free → double toggle creates 2-cycles → NOT safe
        safe_toggles[key] = False
    else:
        # Partner is determined → single toggle is safe
        safe_toggles[key] = True

safe_count = sum(1 for v in safe_toggles.values() if v)
unsafe_count = sum(1 for v in safe_toggles.values() if not v)
print(f"Free entries: {len(free_entries)}")
print(f"  Safe to toggle: {safe_count}")
print(f"  Unsafe (binary double toggle): {unsafe_count}")

# Build completion with all safe toggles activated
comp_safe = dict(det)
for key in free_entries:
    p, L, S, R = key
    if safe_toggles.get(key, False):
        choices = [v for v in range(ms_test[p]) if v != S]
        comp_safe[key] = choices[0] if choices else S
    else:
        comp_safe[key] = S  # non-privileged

# Check liveness
dead_safe = []
for c in all_configs:
    has_priv = False
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        key = (p, L, S, R)
        if comp_safe.get(key, S) != S:
            has_priv = True
            break
    if not has_priv:
        dead_safe.append(c)

print(f"\nDead configs under safe-only completion: {len(dead_safe)}")
if dead_safe:
    print(f"These configs can ONLY be saved by binary double toggles.")
    print(f"But double toggles create 2-cycles.")
    print(f"So these configs have NO escape — liveness is IMPOSSIBLE")
    print(f"without creating convergence violations.")

    # Are these dead configs actually covered only by unsafe binary entries?
    for c in dead_safe[:5]:
        saviors = []
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if key in free_entries or key not in det:
                saviors.append((p, key, safe_toggles.get(key, 'determined')))
        print(f"  {''.join(str(x) for x in c)}: "
              f"saviors = {[(p, safe) for p, _, safe in saviors if safe is not True]}")
