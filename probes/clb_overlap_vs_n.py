#!/usr/bin/env python3
"""clb_overlap_vs_n.py — Does the overlap argument hold for n < 9?

For n=5..8, valid 2-binary systems EXIST (the optimal M_n witness has 3 binary).
So overlap-free cycles must exist for n ≤ 8.
When does the overlap become unavoidable?

Also: check sweep cycles (not just bounce) for overlap.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian


def build_uniform_sweep(n, ms, nb_val=1):
    """Build uniform sweep cycle [0,1,...,n-1,0,1,...,n-1]."""
    config = [0] * n
    cycle = [tuple(config)]
    for proc in range(n):
        config = list(cycle[-1])
        config[proc] = 1 if ms[proc] == 2 else nb_val
        cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    return cycle


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


def get_movers(cycle, n):
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [k for k in range(n) if c[k] != c_next[k]]
        if len(diffs) != 1:
            return None
        movers.append(diffs[0])
    return movers


def check_overlap(cycle, movers, n):
    """Return dict: proc -> set of overlapping triples."""
    overlaps = {}
    for p in range(n):
        mover_set = set()
        nonmover_set = set()
        for idx in range(len(cycle)):
            c = cycle[idx]
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if movers[idx] == p:
                mover_set.add(triple)
            else:
                nonmover_set.add(triple)
        ovlp = mover_set & nonmover_set
        if ovlp:
            overlaps[p] = ovlp
    return overlaps


# ============================================================
# Test sweep cycles for overlap across n values
# ============================================================

print("="*70)
print("SWEEP CYCLE OVERLAP ANALYSIS")
print("="*70)

for n in range(5, 13):
    ms_3bin = tuple([2]*3 + [3]*(n-3))
    ms_2bin = tuple([2]*2 + [3]*(n-2))
    ms_1bin = tuple([2] + [3]*(n-1))

    for ms, desc in [(ms_3bin, "3-bin"), (ms_2bin, "2-bin"), (ms_1bin, "1-bin")]:
        cycle = build_uniform_sweep(n, ms)
        movers = get_movers(cycle, n)
        if movers is None:
            print(f"  n={n} {desc}: sweep cycle invalid")
            continue
        overlaps = check_overlap(cycle, movers, n)
        if overlaps:
            procs = sorted(overlaps.keys())
            print(f"  n={n} {desc} ms={ms}: sweep len={len(cycle)}, "
                  f"OVERLAP at P{procs}")
        else:
            print(f"  n={n} {desc} ms={ms}: sweep len={len(cycle)}, CLEAN")


# ============================================================
# Test bounce cycles for overlap across n values
# ============================================================

print("\n" + "="*70)
print("BOUNCE CYCLE OVERLAP ANALYSIS")
print("="*70)

bounce_patterns = {
    "down-up": lambda n: list(range(n-1,-1,-1)) + list(range(1,n)),
    "up-down": lambda n: list(range(n)) + list(range(n-2,0,-1)),
}

for n in range(5, 13):
    ms_2bin_adj = tuple([2]*2 + [3]*(n-2))
    ms_2bin_end = tuple([2] + [3]*(n-2) + [2])
    ms_1bin = tuple([2] + [3]*(n-1))

    print(f"\nn={n}:")
    for ms, desc in [(ms_1bin, "1-bin"), (ms_2bin_adj, "2-bin-adj"),
                      (ms_2bin_end, "2-bin-end")]:
        for pname, pfn in bounce_patterns.items():
            base = pfn(n)
            cycle, movers = build_bounce_cycle(ms, n, base)
            if cycle is None:
                continue
            overlaps = check_overlap(cycle, movers, n)
            status = f"OVERLAP at P{sorted(overlaps.keys())}" if overlaps else "CLEAN"
            print(f"  {desc} {pname}: len={len(cycle)}, {status}")


# ============================================================
# Key analysis: for 2-binary adjacent, at what n does overlap start?
# ============================================================

print("\n" + "="*70)
print("PHASE TRANSITION: When does 2-binary adjacent overlap start?")
print("="*70)

for n in range(4, 15):
    ms = tuple([2]*2 + [3]*(n-2))
    any_clean = False

    for pname, pfn in bounce_patterns.items():
        base = pfn(n)
        cycle, movers = build_bounce_cycle(ms, n, base)
        if cycle is None:
            continue
        overlaps = check_overlap(cycle, movers, n)
        if not overlaps:
            any_clean = True
            print(f"  n={n}: {pname} CLEAN (len={len(cycle)})")
            break

    if not any_clean:
        # Try more patterns
        found = False
        extra_patterns = [
            list(range(n-1,-1,-1)) + list(range(1,n)) + list(range(n-2,0,-1)),
            list(range(n)) + list(range(n-2,0,-1)) + list(range(1,n)),
        ]
        for base in extra_patterns:
            cycle, movers = build_bounce_cycle(ms, n, base)
            if cycle is None:
                continue
            overlaps = check_overlap(cycle, movers, n)
            if not overlaps:
                found = True
                print(f"  n={n}: extended pattern CLEAN (len={len(cycle)})")
                break

        if not found:
            # Check all rotations too
            tested_orientations = set()
            for rot in range(n):
                ms_rot = tuple(ms[(i+rot)%n] for i in range(n))
                if ms_rot in tested_orientations:
                    continue
                tested_orientations.add(ms_rot)

                for pname, pfn in bounce_patterns.items():
                    base = pfn(n)
                    cycle, movers = build_bounce_cycle(ms_rot, n, base)
                    if cycle is None:
                        continue
                    overlaps = check_overlap(cycle, movers, n)
                    if not overlaps:
                        found = True
                        print(f"  n={n}: rot {rot} {pname} CLEAN (len={len(cycle)})")
                        break
                if found:
                    break

            if not found:
                print(f"  n={n}: ALL OVERLAP (tested {len(tested_orientations)} orientations)")


# ============================================================
# Understand WHY overlap happens — the "blind spot" analysis
# ============================================================

print("\n" + "="*70)
print("BLIND SPOT ANALYSIS: Which processor overlaps and why?")
print("="*70)

for n in [7, 8, 9, 10, 11]:
    ms = tuple([2]*2 + [3]*(n-2))
    cycle, movers = build_bounce_cycle(ms, n,
                                        list(range(n-1,-1,-1)) + list(range(1,n)))
    if cycle is None:
        print(f"n={n}: no cycle")
        continue

    overlaps = check_overlap(cycle, movers, n)
    if overlaps:
        ovlp_procs = sorted(overlaps.keys())
        # For each overlapping proc, find the cause
        for p in ovlp_procs:
            for triple in overlaps[p]:
                # Find the mover and non-mover positions
                mover_steps = []
                nonmover_steps = []
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    t = (c[(p-1)%n], c[p], c[(p+1)%n])
                    if t == triple:
                        if movers[idx] == p:
                            mover_steps.append(idx)
                        else:
                            nonmover_steps.append(idx)

                # Find what differs between the configs
                for mi in mover_steps:
                    for ni in nonmover_steps:
                        cm = cycle[mi]
                        cn = cycle[ni]
                        diffs = [j for j in range(n) if cm[j] != cn[j]]
                        distances = [min(abs(j-p), n-abs(j-p)) for j in diffs]
                        print(f"  n={n} P{p} triple={triple}: mover@{mi} vs nonmover@{ni}")
                        print(f"    Diff positions: {diffs} (distances from P{p}: {distances})")
                        print(f"    Mover at nonmover step: P{movers[ni]}")
                        break
                    break
        print()
    else:
        print(f"n={n}: CLEAN")
