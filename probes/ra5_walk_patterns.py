"""
ra5_walk_patterns.py — Enumerate ring-adjacent walk patterns involving 3 adjacent processors.

Key question: Under ring-adjacency, when the walk visits all 3 of {p, p+1, p+2},
what mover subsequences are possible within/around this 3-arc?

We work modulo translation, so the 3-arc is {0, 1, 2}.
"""

from itertools import product
from collections import defaultdict


def ring_dist(a, b, n):
    """Ring distance between processors a and b on ring of size n."""
    d = abs(a - b)
    return min(d, n - d)


def enumerate_ra_walks(n, max_len=30):
    """
    Enumerate all ring-adjacent mover sequences of length up to max_len on ring of n procs
    where all of {0,1,2} fire at least once.

    Returns set of mover tuples.
    """
    # BFS over mover sequences
    results = []
    # Start from any processor
    for start in range(n):
        # BFS: (mover_seq, fired_set)
        queue = [([start], {start})]
        while queue:
            new_queue = []
            for seq, fired in queue:
                if fired >= {0, 1, 2}:
                    results.append(tuple(seq))
                    continue
                if len(seq) >= max_len:
                    continue
                last = seq[-1]
                for nxt in range(n):
                    if ring_dist(last, nxt, n) <= 1:
                        new_seq = seq + [nxt]
                        new_fired = fired | {nxt}
                        new_queue.append((new_seq, new_fired))
            queue = new_queue
    return results


def enumerate_local_patterns(max_len=12):
    """
    Focus on mover subsequences restricted to {0, 1, 2} (ignoring escapes to -1 or 3).
    Under ring-adjacency, from 0 you can go to 0 or 1 (staying in arc) or n-1 (leaving).
    From 1 you can go to 0, 1, or 2.
    From 2 you can go to 1, 2, or 3 (leaving).

    Within the 3-arc {0,1,2}, enumerate all ring-adjacent sequences that visit all 3.
    """
    # Adjacency within {0,1,2}: 0-1, 1-2 (linear, not ring — these are 3 ADJACENT procs on a bigger ring)
    adj = {0: [0, 1], 1: [0, 1, 2], 2: [1, 2]}

    results = set()
    for start in [0, 1, 2]:
        queue = [([start], {start})]
        while queue:
            new_queue = []
            for seq, fired in queue:
                if fired == {0, 1, 2}:
                    results.add(tuple(seq))
                    # Also continue to find longer patterns
                    if len(seq) < max_len:
                        last = seq[-1]
                        for nxt in adj[last]:
                            new_queue.append((seq + [nxt], fired | {nxt}))
                elif len(seq) < max_len:
                    last = seq[-1]
                    for nxt in adj[last]:
                        new_queue.append((seq + [nxt], fired | {nxt}))
            queue = new_queue

    return results


def classify_minimal_patterns():
    """
    Find MINIMAL patterns: shortest ring-adjacent sequences within {0,1,2}
    that visit all three, for each starting processor.
    """
    adj = {0: [0, 1], 1: [0, 1, 2], 2: [1, 2]}

    for start in [0, 1, 2]:
        print(f"\n=== Starting from processor {start} ===")
        queue = [([start], {start})]
        found = []
        min_len = None
        while queue:
            new_queue = []
            for seq, fired in queue:
                if fired == {0, 1, 2}:
                    if min_len is None:
                        min_len = len(seq)
                    if len(seq) == min_len:
                        found.append(tuple(seq))
                    continue
                if min_len is not None and len(seq) >= min_len:
                    continue
                last = seq[-1]
                for nxt in adj[last]:
                    new_queue.append((seq + [nxt], fired | {nxt}))
            queue = new_queue

        print(f"  Minimum length: {min_len}")
        print(f"  Count: {len(found)}")
        for p in sorted(found):
            print(f"    {list(p)}")


def analyze_arc_sojourn_patterns():
    """
    The walk doesn't have to STAY in the 3-arc. It can leave and return.
    But while it's in the arc, the local pattern must be ring-adjacent.

    Key insight: When the walk enters the 3-arc, what are the possible
    "sojourn" patterns (consecutive steps within {0,1,2})?

    Entry points: the walk can enter from the left (arriving at 0 from n-1)
    or from the right (arriving at 2 from 3), or from 1 (arriving from 0 or 2).

    Actually on the bigger ring, the 3-arc is {p, p+1, p+2}. Adjacent to it
    are p-1 (left of p) and p+3 (right of p+2). Under ring-adjacency:
    - From p-1, can go to p (enter left)
    - From p+3, can go to p+2 (enter right)
    - From p, can go to p-1 (exit left)
    - From p+2, can go to p+3 (exit right)
    """
    print("\n=== Arc Sojourn Analysis ===")
    print("Entry from left → proc 0, Entry from right → proc 2")
    print("Exit left from proc 0, Exit right from proc 2")
    print()

    # Within the arc, adjacency is linear: 0↔1↔2
    # We track sojourns: maximal consecutive subsequences within {0,1,2}
    # A sojourn starts at 0 (entered from left) or 2 (entered from right)
    # or at 1 (if first step is in arc)
    # A sojourn ends when leaving: from 0 (exit left) or from 2 (exit right)

    # For the 3-arc obstruction: we need all 3 to fire.
    # This can happen in one sojourn or across multiple sojourns.

    # Case 1: Single sojourn covers all 3
    # Must enter, visit 0, 1, and 2, then exit
    print("Case 1: Single sojourn covers all 3 processors")
    adj = {0: [1], 1: [0, 2], 2: [1]}  # strict moves only (no self-loops for now)

    for entry in [0, 2]:
        patterns = set()
        queue = [([entry], {entry})]
        while queue:
            new_queue = []
            for seq, fired in queue:
                if fired == {0, 1, 2}:
                    patterns.add(tuple(seq))
                    # Continue to find patterns that exit
                    if len(seq) < 10:
                        last = seq[-1]
                        for nxt in adj[last]:
                            new_queue.append((seq + [nxt], fired | {nxt}))
                elif len(seq) < 10:
                    last = seq[-1]
                    for nxt in adj[last]:
                        new_queue.append((seq + [nxt], fired | {nxt}))
            queue = new_queue

        # Filter patterns that end at an exit point (0 or 2)
        exitable = [p for p in patterns if p[-1] in [0, 2]]
        print(f"\n  Entry at {entry}, exitable patterns (up to len 10):")
        by_len = defaultdict(list)
        for p in sorted(exitable, key=len):
            by_len[len(p)].append(p)
        for l in sorted(by_len):
            print(f"    Length {l}: {len(by_len[l])} patterns")
            if len(by_len[l]) <= 8:
                for p in by_len[l]:
                    print(f"      {list(p)}")


def analyze_fire_counts():
    """
    For the 3-arc {0,1,2}: how many times does each processor fire
    in minimal covering patterns?

    Key insight: processor 1 (middle) fires at least once.
    Processors 0 and 2 fire at least once.
    What are the minimum and typical fire counts?
    """
    print("\n=== Fire Count Analysis ===")
    # Allow self-loops (firing same proc twice in a row)
    adj = {0: [0, 1], 1: [0, 1, 2], 2: [1, 2]}

    patterns = set()
    for start in [0, 1, 2]:
        queue = [([start], {start})]
        while queue:
            new_queue = []
            for seq, fired in queue:
                if fired == {0, 1, 2}:
                    patterns.add(tuple(seq))
                    if len(seq) < 8:
                        last = seq[-1]
                        for nxt in adj[last]:
                            new_queue.append((seq + [nxt], fired | {nxt}))
                elif len(seq) < 8:
                    last = seq[-1]
                    for nxt in adj[last]:
                        new_queue.append((seq + [nxt], fired | {nxt}))
            queue = new_queue

    print(f"Total patterns (up to length 8): {len(patterns)}")

    # For each pattern, count fires at each processor
    fire_count_dist = defaultdict(int)
    for pat in patterns:
        counts = (pat.count(0), pat.count(1), pat.count(2))
        fire_count_dist[counts] += 1

    print("\nFire count distributions (fires_at_0, fires_at_1, fires_at_2) -> # patterns:")
    for counts in sorted(fire_count_dist):
        print(f"  {counts}: {fire_count_dist[counts]}")


def key_structural_observation():
    """
    THE KEY OBSERVATION:

    Under ring-adjacency within the 3-arc {0, 1, 2}:
    - From 0: next can be 0 or 1 (can't reach 2 directly)
    - From 1: next can be 0, 1, or 2
    - From 2: next can be 1 or 2 (can't reach 0 directly)

    So to visit all 3: the walk MUST pass through 1 to go between 0 and 2.

    Processor 1 is the BOTTLENECK. It must fire every time the walk transitions
    between the 0-side and the 2-side.

    If 0 fires f0 times and 2 fires f2 times, how many times must 1 fire?
    """
    print("\n=== Key Structural Observation ===")
    print("Processor 1 is the bottleneck between 0 and 2.")
    print()
    print("The walk on {0,1,2} is a path on the graph 0—1—2.")
    print("Every transition between 0-side and 2-side passes through 1.")
    print()

    # The walk is a sequence on {0,1,2} where consecutive elements differ by ≤1.
    # If we project to {L, M, R} where L=0, M=1, R=2:
    # The walk oscillates: ...L, M, R, M, L, M, R, ...
    # (with possible stutters: L, L, M, M, R, R, etc.)

    # Key: between consecutive fires of different endpoints (0→2 or 2→0),
    # processor 1 must fire at least once.

    print("Between any fire of 0 and the next fire of 2 (or vice versa),")
    print("processor 1 must fire at least once.")
    print()

    # Let's think about what happens at processor 1's boundary triple.
    # Triple at proc 1 = (config[0], config[1], config[2]).
    # This changes when 0, 1, or 2 fires.
    # At MOVER steps for 1: config[1] changes (the S component).
    # At NON-MOVER steps (0 or 2 fires): config[0] or config[2] changes.

    print("At processor 1's MOVER step: S = config[1] (before change)")
    print("At processor 1's NON-MOVER step: S = config[1] (unchanged)")
    print()
    print("Critical: config[1] only changes at processor 1's mover steps.")
    print("Between two consecutive p1-fires, config[1] is CONSTANT.")
    print()
    print("So the S-component of the boundary triple at proc 1 is:")
    print("  - At mover steps: the value BEFORE the change")
    print("  - Between mover steps: the value AFTER the previous change")
    print("  - Before FIRST mover step: the INITIAL value = same as at first mover step")
    print()
    print("==> MATCH: The initial value of config[1] appears at:")
    print("    1. All non-mover steps BEFORE proc 1's first fire")
    print("    2. The first mover step of proc 1")
    print("    So S-component matches between first mover step and all prior non-mover steps!")


if __name__ == "__main__":
    classify_minimal_patterns()
    analyze_arc_sojourn_patterns()
    analyze_fire_counts()
    key_structural_observation()
