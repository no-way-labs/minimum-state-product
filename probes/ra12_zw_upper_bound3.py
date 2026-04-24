#!/usr/bin/env python3
"""
RA12 Part 3: Debug - what cycles ARE we finding?
Also: directly test with known valid system witnesses.
"""

from itertools import product as cprod
from collections import defaultdict, Counter
import random

def get_good_configs_and_cycles(n, ms, tables):
    """Get good configs and follow trajectories to find cycles."""
    ranges = [range(m) for m in ms]
    good = {}
    for c in cprod(*ranges):
        priv = []
        for p in range(n):
            l = c[(p-1) % n]
            s = c[p]
            r = c[(p+1) % n]
            new_s = tables[p][(l, s, r)]
            if new_s != s:
                priv.append(p)
        if len(priv) == 1:
            good[c] = priv[0]
    return good

def follow_trajectory(good, start, n):
    """Follow deterministic trajectory from start config."""
    path = []
    movers = []
    c = start
    visited = set()

    while True:
        if c not in good:
            return None  # hit non-good config
        if c in visited:
            if c == start and len(path) > 0:
                return (path, movers)
            else:
                return None  # revisited non-start
        visited.add(c)
        path.append(c)
        p = good[c]
        movers.append(p)

        c_next = list(c)
        # No tables needed — just need to know what the transition function gives
        # But we DO need the table to compute the next config.
        return None  # Can't continue without tables

def find_cycles_with_tables(n, ms, tables, max_cycles=100):
    """Find all good cycles for given tables."""
    good = get_good_configs_and_cycles(n, ms, tables)

    visited_global = set()
    cycles = []

    for start in good:
        if start in visited_global:
            continue

        path = []
        movers = []
        c = start
        visited = set()

        while True:
            if c not in good:
                # Not a good config; mark all visited as dead
                for cfg in path:
                    visited_global.add(cfg)
                break
            if c in visited:
                if c == start and len(path) > 0:
                    cycles.append((path, movers))
                    for cfg in path:
                        visited_global.add(cfg)
                else:
                    for cfg in path:
                        visited_global.add(cfg)
                break
            visited.add(c)
            path.append(c)
            p = good[c]
            movers.append(p)

            c_next = list(c)
            l = c[(p-1) % n]
            s = c[p]
            r = c[(p+1) % n]
            c_next[p] = tables[p][(l, s, r)]
            c = tuple(c_next)

        if len(cycles) >= max_cycles:
            break

    return cycles

def analyze_cycle(n, configs, movers):
    """Analyze a cycle."""
    L = len(configs)
    fc = [0] * n
    for m in movers:
        fc[m] += 1

    cw = ccw = stay = jump = 0
    for i in range(L):
        p_curr = movers[i]
        p_next = movers[(i+1) % L]
        diff = (p_next - p_curr) % n
        if diff == 1: cw += 1
        elif diff == n - 1: ccw += 1
        elif diff == 0: stay += 1
        else: jump += 1

    total_disp = sum(((movers[(i+1)%L] - movers[i] + n//2) % n - n//2) for i in range(L))

    return {'L': L, 'fc': fc, 'cw': cw, 'ccw': ccw, 'stay': stay, 'jump': jump,
            'disp': total_disp, 'zw': total_disp == 0,
            'has_safe': any(f == 0 for f in fc)}

# Test with random systems
random.seed(42)

def test_systems(n, ms, num_trials=10000, label=""):
    print(f"\n{'='*70}")
    print(f"TESTING: n={n}, ms={ms}, {label}")
    print(f"{'='*70}")

    total_cycles = 0
    all_infos = []
    zw_infos = []
    zw_nosafe_infos = []

    for trial in range(num_trials):
        tables = []
        for p in range(n):
            m = ms[p]
            m_left = ms[(p-1) % n]
            m_right = ms[(p+1) % n]
            t = {}
            for l in range(m_left):
                for s in range(m):
                    for r in range(m_right):
                        t[(l, s, r)] = random.randint(0, m-1)
            tables.append(t)

        cycles = find_cycles_with_tables(n, ms, tables)
        for path, movers in cycles:
            info = analyze_cycle(n, path, movers)
            all_infos.append(info)
            if info['zw']:
                zw_infos.append(info)
                if not info['has_safe'] and info['cw'] > 0:
                    zw_nosafe_infos.append(info)

    print(f"Total cycles found: {len(all_infos)}")
    if all_infos:
        lengths = Counter(c['L'] for c in all_infos)
        print(f"Length distribution: {dict(sorted(lengths.items()))}")

        disp_dist = Counter(c['disp'] for c in all_infos)
        print(f"Displacement distribution (top 10): {dict(sorted(disp_dist.most_common(10)))}")

    print(f"Zero-winding cycles: {len(zw_infos)}")
    if zw_infos:
        zw_lengths = Counter(c['L'] for c in zw_infos)
        print(f"  Length distribution: {dict(sorted(zw_lengths.items()))}")
        zw_safe = Counter(c['has_safe'] for c in zw_infos)
        print(f"  Has safe proc: {dict(zw_safe)}")

    print(f"ZW + no safe + cw > 0: {len(zw_nosafe_infos)}")
    if zw_nosafe_infos:
        for info in zw_nosafe_infos[:5]:
            print(f"  L={info['L']}, fc={info['fc']}, cw={info['cw']}, ccw={info['ccw']}, stay={info['stay']}, jump={info['jump']}")

    return all_infos, zw_infos, zw_nosafe_infos

# Small n first
test_systems(5, [2,2,2,3,3], 50000, "product=72, sub-threshold")
test_systems(5, [2,2,2,3,4], 50000, "product=96 = M_5, sub-threshold")

# What about non-binary-heavy systems?
test_systems(5, [3,3,3,3,3], 50000, "all ternary (for comparison)")

# Try n=4 which is smaller
test_systems(4, [2,2,3,3], 50000, "n=4, product=36, sub-threshold")
test_systems(4, [2,2,2,3], 50000, "n=4, product=24, 3 binary")

# Key question: are zero-winding cycles just very rare, or impossible?
# The lower bound proof ASSUMES a ZW good cycle exists and derives a contradiction.
# So maybe at sub-threshold product with ≥3 binary, ZW good cycles DON'T EXIST!
# That would mean the whole CL ≤ 2n question is vacuously true.
# But the Lean proof structure goes: assume ZW cycle → derive fc=2 → entry conflict → False.
# So ZW cycles might exist at supra-threshold products.

# Let me check: at THRESHOLD product, do ZW cycles exist?
print("\n\n" + "="*70)
print("CHECKING: Do ZW good cycles exist at threshold product?")
print("="*70)
test_systems(5, [2,3,3,3,3], 50000, "n=5, product=162 > 108=threshold")
test_systems(5, [3,3,3,3,4], 50000, "n=5, product=324 > threshold")
