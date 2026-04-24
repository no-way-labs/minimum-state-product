#!/usr/bin/env python3
"""
RA6 Investigation 1+3: Can sweep cycles exist on mixed rings?

Tests whether sweep (all-CW or all-CCW) good cycles can exist on
mixed binary+ternary rings, and at what cycle length.

Key questions:
- CL=2n sweep: ternary procs fire 2x, doesn't close for 3-cycle f.
- CL=6n sweep: ternary fire 6x (div by 3), binary fire 6x (div by 2). Closes.
- Does 6n sweep have entry conflict?
- What about 4n, 3n sweeps?
"""
from itertools import product as iproduct
from collections import defaultdict

def check_sweep_closure(ms, n, num_passes):
    """Check if a num_passes-sweep closes for given ms.
    Each proc fires num_passes times. Returns True if all procs return to 0."""
    for p in range(n):
        # After firing num_passes times: (0 + num_passes) % ms[p]
        if num_passes % ms[p] != 0:
            return False
    return True

def build_sweep_cycle(ms, n, num_passes, direction=1):
    """Build a sweep cycle: direction=1 for CW, -1 for CCW.
    Movers: pass k visits procs in order 0,1,...,n-1 (CW) or n-1,...,0 (CCW).
    Total CL = num_passes * n."""
    word = []
    for k in range(num_passes):
        if direction == 1:
            word.extend(range(n))
        else:
            word.extend(range(n-1, -1, -1))
    return word

def check_entry_conflict(word, ms, n):
    """Check if the good cycle has entry conflict.
    Build configs using incrementing transition, check mover/nonmover overlap."""
    L = len(word)
    # Build configs
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)

    # Check closure
    if configs[-1] != configs[0]:
        return None, "NOT CLOSED"

    # Check distinct
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None, f"NOT DISTINCT ({len(config_set)} unique out of {L})"

    good = [tuple(c) for c in configs[:L]]

    # Collect mover and nonmover triples
    mover_triples = defaultdict(set)   # proc -> set of (L,S,R) when mover
    nonmover_triples = defaultdict(set) # proc -> set of (L,S,R) when nonmover

    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            Lp = (j-1) % n
            Rp = (j+1) % n
            triple = (c[Lp], c[j], c[Rp])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)

    # Entry conflict: same (L,S,R) appears as both mover and nonmover
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap

    return conflicts, "OK"

def main():
    print("RA6 Investigation 1+3: Sweep Cycles on Mixed Rings")
    print("=" * 70)

    # Test multisets
    test_cases = [
        ([2,3,2,3,2,3,3,3,3], "3 non-consec binary"),
        ([2,3,3,2,3,3,2,3,3], "3 non-consec binary v2"),
        ([3,2,3,3,2,3,3,2,3], "3 non-consec binary v3"),
        ([2,2,2,3,3,3,3,3,3], "3 consec binary (ref)"),
        ([2,2,2,2,2,2,2,2,2], "all binary (ref)"),
    ]

    print("\n--- PART A: Sweep closure check ---")
    for ms, label in test_cases:
        n = len(ms)
        print(f"\nms={ms}  ({label})")
        for passes in range(1, 13):
            closes = check_sweep_closure(ms, n, passes)
            if closes:
                print(f"  {passes}-sweep (CL={passes*n}): CLOSES")

    print("\n--- PART B: Entry conflict in closing sweeps ---")
    for ms, label in test_cases:
        n = len(ms)
        print(f"\nms={ms}  ({label})")
        for passes in range(1, 13):
            if not check_sweep_closure(ms, n, passes):
                continue
            word = build_sweep_cycle(ms, n, passes, direction=1)
            conflicts, status = check_entry_conflict(word, ms, n)
            if status != "OK":
                print(f"  {passes}-sweep CW (CL={passes*n}): {status}")
                continue
            if conflicts:
                nc = len(conflicts)
                total_overlaps = sum(len(v) for v in conflicts.values())
                print(f"  {passes}-sweep CW (CL={passes*n}): EC at {nc} procs, {total_overlaps} overlapping triples")
            else:
                print(f"  {passes}-sweep CW (CL={passes*n}): NO EC *** COUNTEREXAMPLE ***")

    print("\n--- PART C: Both directions ---")
    for ms, label in test_cases:
        n = len(ms)
        if all(m == 2 for m in ms):
            # Already know all-binary works
            continue
        print(f"\nms={ms}  ({label})")
        for passes in range(1, 13):
            if not check_sweep_closure(ms, n, passes):
                continue
            for d, dname in [(1, "CW"), (-1, "CCW")]:
                word = build_sweep_cycle(ms, n, passes, direction=d)
                conflicts, status = check_entry_conflict(word, ms, n)
                if status != "OK":
                    continue
                if not conflicts:
                    print(f"  {passes}-sweep {dname}: NO EC *** COUNTEREXAMPLE ***")
                else:
                    nc = len(conflicts)
                    print(f"  {passes}-sweep {dname}: EC at {nc} procs")

    print("\n--- PART D: Why ternary breaks 2-sweep ---")
    print("Analyzing which procs cause closure failure in 2-sweep on mixed rings")
    ms = [2,3,2,3,2,3,3,3,3]
    n = len(ms)
    word = build_sweep_cycle(ms, n, 2, direction=1)
    configs = [[0]*n]
    for t in range(len(word)):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    final = configs[-1]
    print(f"ms={ms}")
    print(f"After 2-sweep, final config: {final}")
    for p in range(n):
        if final[p] != 0:
            print(f"  Proc {p} (m={ms[p]}): final={final[p]} (needs {ms[p]-final[p]} more fires to close)")

    print("\n--- PART E: Minimum sweep passes for each multiset ---")
    for ms, label in test_cases:
        n = len(ms)
        from math import lcm
        min_passes = 1
        for m in ms:
            min_passes = lcm(min_passes, m)
        print(f"ms={ms} ({label}): min passes = LCM({set(ms)}) = {min_passes}, min CL = {min_passes*n}")

    print("\nDone.")

if __name__ == "__main__":
    main()
