#!/usr/bin/env python3
"""CIC Exploration 6: What cycle types exist at/near threshold products?

Key question: For systems with ≥3 binary and product near 4·3^(n-2),
are all good cycles sweeps/bounces, or do other walk types appear?

If only sweeps/bounces appear: shadow argument covers everything.
If other walks appear at threshold: need to understand what changes
as product drops below threshold.

Strategy:
1. At n=4, enumerate ALL valid systems at product = threshold = 36
2. Classify their good cycles
3. Check if non-sweep/non-bounce cycles exist
4. Check products just BELOW threshold
"""

from itertools import product as iproduct
from collections import Counter
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


def build_all_transition_fns(ms, n):
    """Build all possible transition functions for given ms.
    Returns generator of (fs_list) where each fs_list is a list of callables."""
    # For each processor, enumerate all possible transition tables
    choices_per_proc = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        # Each entry (L, S, R) -> output in range(m_S)
        entries = [(L, S, R) for L in range(m_L)
                   for S in range(m_S) for R in range(m_R)]
        # Number of possible tables = m_S^(m_L * m_S * m_R)
        num_entries = len(entries)
        total_tables = ms[p] ** num_entries
        choices_per_proc.append((entries, num_entries, total_tables))

    # Total combinations
    total = 1
    for _, _, t in choices_per_proc:
        total *= t

    return total, choices_per_proc


def extract_good_cycle(result):
    """Extract good cycle and movers from verify_system result."""
    if not result.get('valid', False):
        return None, None
    cycle = result.get('cycle', [])
    if not cycle:
        return None, None
    n = len(cycle[0])
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) == 1:
            movers.append(diffs[0])
        else:
            movers.append(-1)
    return cycle, movers


def classify_cycle_type(movers, n):
    """Classify mover pattern."""
    if not movers or -1 in movers:
        return "unknown"

    # Check sweep
    sweep = list(range(n))
    L = len(movers)
    if L % n == 0 and movers == sweep * (L // n):
        return "sweep"

    # Check reverse sweep
    rev_sweep = list(range(n - 1, -1, -1))
    if L % n == 0 and movers == rev_sweep * (L // n):
        return "rev_sweep"

    # Check bounce (forward)
    bounce = list(range(n)) + list(range(n - 2, 0, -1))
    for r in range(1, 10):
        prefix = (bounce * r)[:L]
        if len(prefix) == L and movers == prefix:
            return "bounce"

    # Check reverse bounce
    rev_bounce = list(range(n - 1, -1, -1)) + list(range(1, n - 1))
    for r in range(1, 10):
        prefix = (rev_bounce * r)[:L]
        if len(prefix) == L and movers == prefix:
            return "rev_bounce"

    # Check self-loops
    has_self = any(movers[i] == movers[(i + 1) % L] for i in range(L))

    # Check direction changes
    dirs = []
    for i in range(L):
        d = (movers[(i + 1) % L] - movers[i]) % n
        if d <= n // 2:
            dirs.append(d)
        else:
            dirs.append(d - n)

    dir_changes = sum(1 for i in range(len(dirs))
                      if dirs[i] != dirs[(i + 1) % len(dirs)])

    if has_self:
        return f"walk_selfloop_L{L}_dc{dir_changes}"
    return f"walk_L{L}_dc{dir_changes}"


# ============================================================
# Test 1: n=4 threshold (ms=(2,3,3,2), product=36)
# ============================================================
print("=" * 70)
print("n=4 THRESHOLD: ALL VALID SYSTEMS FOR ms=(2,3,3,2)")
print("=" * 70)

n = 4
ms = (2, 3, 3, 2)

# Enumerate ALL valid systems by trying all transition functions
# Product = 36, small enough for exhaustive enumeration
# But the number of possible transition functions is huge:
# Each proc p has m_L * m_S * m_R entries, each with m_S choices
# P0: 2*2*3=12 entries, 2^12=4096 choices
# P1: 2*3*3=18 entries, 3^18=387M choices → too many!

# Instead, enumerate using cycle-first approach:
# 1. Enumerate all possible good cycles
# 2. Complete each to a system
# 3. Check validity

# Actually, let's use verifier on systematically constructed systems
# For small n, try good-targeting with different cycle types

from cic_mnu_validity import enumerate_good_cycles, check_mnu

print("\nEnumerating good cycles...")
cycles = enumerate_good_cycles(ms, n, max_cycles=500, max_time=120.0)
print(f"Found {len(cycles)} candidate good cycles")

# Classify and complete
type_counts = Counter()
type_valid_counts = Counter()
type_mnu = {}  # type -> (ok, fail)

for cycle, movers, det in cycles:
    ctype = classify_cycle_type(movers, n)
    type_counts[ctype] += 1

    violations = check_mnu(cycle, movers, n)
    has_mnu = len(violations) == 0

    if ctype not in type_mnu:
        type_mnu[ctype] = [0, 0]
    if has_mnu:
        type_mnu[ctype][0] += 1
    else:
        type_mnu[ctype][1] += 1

print(f"\nCycle type distribution:")
for ctype, cnt in sorted(type_counts.items(), key=lambda x: -x[1]):
    ok, fail = type_mnu.get(ctype, [0, 0])
    print(f"  {ctype:40s}  count={cnt:4d}  MNU: {ok} OK, {fail} FAIL")


# ============================================================
# Test 2: n=4 SUB-threshold systems
# ============================================================
print(f"\n{'=' * 70}")
print("n=4 SUB-THRESHOLD: VALID SYSTEMS WITH product < 36")
print("=" * 70)

# Possible ms with product < 36, n=4:
# (2,2,2,4) = 32, (2,2,4,2) = 32, etc.
# (2,2,2,3) = 24
# (2,2,3,2) = 24
# (2,3,2,2) = 24
# (3,2,2,2) = 24
# (2,2,2,2) = 16
sub_threshold_systems = [
    (2, 2, 2, 4),
    (2, 2, 4, 2),
    (2, 4, 2, 2),
    (4, 2, 2, 2),
    (2, 2, 2, 3),
    (2, 2, 3, 2),
    (2, 3, 2, 2),
    (3, 2, 2, 2),
    (2, 2, 2, 2),
]

for ms_sub in sub_threshold_systems:
    n_sub = len(ms_sub)
    prod = 1
    for m in ms_sub:
        prod *= m
    k = sum(1 for m in ms_sub if m == 2)

    cycles = enumerate_good_cycles(ms_sub, n_sub, max_cycles=50,
                                    max_time=10.0)
    print(f"\n  ms={list(ms_sub)}, product={prod}, k={k} binary:"
          f" {len(cycles)} candidate cycles")

    if cycles:
        valid_count = 0
        for cycle, movers, det in cycles:
            from cic_mnu_validity import complete_and_verify
            result = complete_and_verify(cycle, movers, det, ms_sub, n_sub)
            if result.get('valid', False):
                valid_count += 1
                ctype = classify_cycle_type(movers, n_sub)
                violations = check_mnu(cycle, movers, n_sub)
                print(f"    VALID: type={ctype}, L={len(cycle)}, "
                      f"MNU={'OK' if not violations else 'FAIL'}")
                print(f"           movers={movers}")
        if valid_count == 0:
            print(f"    No valid systems (0/{len(cycles)} completions valid)")


# ============================================================
# Test 3: n=5 at threshold (ms=(2,3,3,3,2), product=108)
# ============================================================
print(f"\n{'=' * 70}")
print("n=5 THRESHOLD: ms=(2,3,3,3,2), product=108")
print("=" * 70)

n5 = 5
ms5 = (2, 3, 3, 3, 2)

# CLB bounce cycle
from cic_nonsweep_mnu import build_clb_system
ms_clb, cycle_clb, movers_clb, _ = build_clb_system(n5)
if cycle_clb:
    ctype = classify_cycle_type(movers_clb, n5)
    violations = check_mnu(cycle_clb, movers_clb, n5)
    print(f"\n  CLB bounce: type={ctype}, L={len(cycle_clb)}, "
          f"MNU={'OK' if not violations else 'FAIL'}")

# Search for other cycles
print("\n  Searching for other good cycles (DFS)...")
cycles5 = enumerate_good_cycles(ms5, n5, max_cycles=50, max_time=30.0)
print(f"  Found {len(cycles5)} candidate cycles")

for cycle, movers, det in cycles5[:10]:
    ctype = classify_cycle_type(movers, n5)
    violations = check_mnu(cycle, movers, n5)
    from cic_mnu_validity import complete_and_verify
    result = complete_and_verify(cycle, movers, det, ms5, n5)
    valid = result.get('valid', False)
    print(f"    {ctype}: L={len(cycle)}, MNU={'OK' if not violations else 'FAIL'}"
          f", valid={valid}")


# ============================================================
# Summary
# ============================================================
print(f"\n{'=' * 70}")
print("SUMMARY: CYCLE TYPES AT THRESHOLD vs SUB-THRESHOLD")
print("=" * 70)
print("""
Key question: Do non-sweep/non-bounce cycles exist at sub-threshold products?

If NO: The shadow argument (sweep/bounce MNU) covers all cases.
       Lower bound M_n >= 4·3^(n-2) follows for all n >= 9.

If YES: Need a different killing argument for non-sweep/non-bounce cycles.
        The forced SCC approach doesn't work (0 SCCs from cycle entries).
        Would need entry-count or completion impossibility argument.
""")
