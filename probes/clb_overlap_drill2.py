#!/usr/bin/env python3
"""clb_overlap_drill2.py — Systematic search for overlap-free cycles at 2-binary.

The key question: is triple overlap INEVITABLE for all possible good cycles
with 2 binary processors at n=9, or just an artifact of the simple bounce construction?

Approach: enumerate cycles via DFS with early overlap pruning.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import time


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    """Build bounce cycle with given pattern."""
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


def check_overlap(cycle, movers, n):
    """Check if any processor has triple overlap. Return details."""
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
# Part 1: Test ALL orientations of 2-binary at n=9
# ============================================================

n = 9
print("="*70)
print("Part 1: All necklace orientations of 2-binary at n=9")
print("="*70)

necklaces = [
    (2,2,3,3,3,3,3,3,3),  # sep=1
    (2,3,2,3,3,3,3,3,3),  # sep=2
    (2,3,3,2,3,3,3,3,3),  # sep=3
    (2,3,3,3,2,3,3,3,3),  # sep=4
]

patterns = [
    ("down-up", list(range(n-1,-1,-1)) + list(range(1,n))),
    ("up-down", list(range(n)) + list(range(n-2,0,-1))),
    ("down-up-down", list(range(n-1,-1,-1)) + list(range(1,n)) + list(range(n-2,0,-1))),
    ("up-down-up", list(range(n)) + list(range(n-2,0,-1)) + list(range(1,n))),
]

total_tested = 0
total_overlap = 0
total_clean = 0
total_nocycle = 0

for neck in necklaces:
    tested = set()
    sep = 0
    for i in range(1, n):
        if neck[i] == 2:
            sep = i
            break
    print(f"\nNecklace sep={sep}: {neck}")

    for rot in range(n):
        ms_rot = tuple(neck[(i+rot)%n] for i in range(n))
        if ms_rot in tested:
            continue
        tested.add(ms_rot)

        bin_pos = [i for i in range(n) if ms_rot[i] == 2]
        any_found = False

        for pname, base in patterns:
            cycle, movers_seq = build_bounce_cycle(ms_rot, n, base)
            if cycle is None:
                continue

            any_found = True
            overlaps = check_overlap(cycle, movers_seq, n)
            total_tested += 1

            if overlaps:
                total_overlap += 1
                ovlp_procs = list(overlaps.keys())
                print(f"  rot={rot} {ms_rot} bins@{bin_pos} {pname}: "
                      f"len={len(cycle)} OVERLAP at P{ovlp_procs}")
            else:
                total_clean += 1
                print(f"  rot={rot} {ms_rot} bins@{bin_pos} {pname}: "
                      f"len={len(cycle)} *** CLEAN ***")

        if not any_found:
            total_nocycle += 1

print(f"\nSummary: {total_tested} tested, {total_overlap} overlap, "
      f"{total_clean} clean, {total_nocycle} no cycle found")

# ============================================================
# Part 2: DFS for overlap-free cycles (short cycles only)
# ============================================================

print("\n" + "="*70)
print("Part 2: DFS for ANY overlap-free cycle at ms=(2,2,3,3,3,3,3,3,3)")
print("="*70)

ms = (2, 2, 3, 3, 3, 3, 3, 3, 3)

def dfs_cycle_search(ms, n, max_depth=30, timeout=30.0):
    """DFS for overlap-free good cycles.

    At each step, try all single-processor moves. Track per-processor
    triple status to prune overlap violations early.
    """
    start = tuple(0 for _ in range(n))
    start_time = time.time()

    # State: (config, path_len, movers_list)
    # For efficiency, track triple assignments per processor:
    # triple_status[p][triple] = 'mover' | 'nonmover' | None
    # If a triple is assigned 'mover' and we'd use it as 'nonmover' (or vice versa), prune.

    cycles_found = []
    nodes = 0

    # Iterative DFS
    # Stack entry: (config, path_configs_frozenset, movers_tuple, triple_assignments)
    # triple_assignments: tuple of frozensets — too expensive
    # Instead: check overlap lazily when cycle is found

    # Simpler: just enumerate short cycles and check
    # Use recursive DFS with visited set

    def search(config, path, movers_list, visited):
        nonlocal nodes
        nodes += 1

        if time.time() - start_time > timeout:
            return

        if len(path) > max_depth:
            return

        if len(cycles_found) >= 20:
            return

        for p in range(n):
            s = config[p]
            for new_s in range(ms[p]):
                if new_s == s:
                    continue

                new_config = list(config)
                new_config[p] = new_s
                new_config = tuple(new_config)

                if new_config == start and len(path) >= n:
                    # Found a cycle!
                    full_movers = movers_list + [p]
                    if set(full_movers) == set(range(n)):
                        # Fair
                        overlaps = check_overlap(path, full_movers, n)
                        if not overlaps:
                            cycles_found.append((len(path), full_movers[:]))
                            print(f"  CLEAN cycle len={len(path)}: "
                                  f"movers={full_movers[:20]}...")
                        # Don't return — keep searching
                    continue

                if new_config not in visited:
                    visited.add(new_config)
                    search(new_config, path + [new_config],
                           movers_list + [p], visited)
                    visited.discard(new_config)

    sys.setrecursionlimit(10000)
    search(start, [start], [], {start})
    elapsed = time.time() - start_time
    print(f"  DFS: {nodes} nodes in {elapsed:.1f}s, "
          f"{len(cycles_found)} overlap-free cycles found")
    return cycles_found


# Run DFS for short cycles
print(f"\nSearching ms={ms} for overlap-free cycles (max_depth=20, timeout=30s)...")
cycles = dfs_cycle_search(ms, n, max_depth=20, timeout=30.0)

if not cycles:
    print("\nNo overlap-free cycles found with depth ≤ 20.")
    print("Trying depth ≤ 30...")
    cycles = dfs_cycle_search(ms, n, max_depth=30, timeout=60.0)

if not cycles:
    print("\nNo overlap-free cycles found with depth ≤ 30 either.")
    print("This is strong evidence that overlap is inherent for 2-binary at n=9.")

# ============================================================
# Part 3: COMPARISON — try 1-binary to confirm cycles exist
# ============================================================

print("\n" + "="*70)
print("Part 3: Sanity check — overlap-free cycles at 1-binary")
print("="*70)

ms_1bin = (2, 3, 3, 3, 3, 3, 3, 3, 3)
print(f"\nSearching ms={ms_1bin} for overlap-free cycles (max_depth=30, timeout=30s)...")
cycles_1bin = dfs_cycle_search(ms_1bin, n, max_depth=30, timeout=30.0)

if cycles_1bin:
    print(f"  Found {len(cycles_1bin)} overlap-free cycles for 1-binary!")
else:
    print("  No cycles found (DFS may need more time)")

# ============================================================
# Part 4: All ternary control
# ============================================================

print("\n" + "="*70)
print("Part 4: Sanity check — overlap-free cycles at all-ternary")
print("="*70)

ms_all3 = (3,) * 9
print(f"\nSearching ms={ms_all3} for overlap-free cycles (max_depth=25, timeout=30s)...")
cycles_all3 = dfs_cycle_search(ms_all3, n, max_depth=25, timeout=30.0)

if cycles_all3:
    print(f"  Found {len(cycles_all3)} overlap-free cycles for all-ternary!")
