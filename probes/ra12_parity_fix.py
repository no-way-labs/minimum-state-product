#!/usr/bin/env python3
"""
RA12: Fix parity analysis. For ODD n, ring parity does NOT strictly alternate
because moving -1 from 0 wraps to n-1 which has same parity as 0.

The correct analysis: on Z_n with n odd, every step (+1 or -1) changes
parity EXCEPT the wrap-around steps. Actually:
  p -> p+1 mod n: always flips parity (since |1| is odd)
  p -> p-1 mod n: if p > 0, parity flips. If p = 0, goes to n-1.
    For n odd: n-1 is even. 0 is even. Same parity. NO FLIP.

Wait, let me reconsider. (p-1) mod n for general p:
  p=0: n-1. Parity of n-1 = (n-1)%2.
  p>0: p-1. Parity = (p-1)%2 = 1-p%2.

For n=9 (odd): (n-1)%2 = 0 = 0%2. So 0->8 is same parity.
Similarly: (p+1) mod n for p=n-1=8: 0. (n-1)%2 = 0, 0%2 = 0. Same parity.

So BOTH directions at the wrap point preserve parity!
  8 -> 0 (+1 direction): 8%2=0, 0%2=0. Same parity.
  0 -> 8 (-1 direction): 0%2=0, 8%2=0. Same parity.

This means: for n=9 (odd), crossing the "seam" between 0 and 8
does NOT change parity. The parity constraint is:
  parity flips at every step EXCEPT steps that cross the 0-8 boundary.

This is actually simpler: think of the walk on Z (not Z_n).
On Z, every step of +/-1 flips parity. The walk on Z_n is the
walk on Z taken mod n. The parity constraint on Z_n depends on
how many times the walk wraps around.

BETTER APPROACH: Just check computationally whether walks exist.
The previous enumeration already showed 0 walks for asymmetric placements.
The question is: is it a fundamental impossibility or just a search depth issue?

Let me try a different approach: relax the fc constraint and check which
fc vectors are achievable.
"""

import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def find_achievable_fc(n, ms, max_steps=30):
    """For a walk of exactly L steps on the n-ring, what fc vectors are achievable
    such that fc[p] is a multiple of ms[p]?"""
    # This is too expensive for large L. Instead, let's check small multiples.
    results = {}
    for mult in [1, 2, 3]:
        target = tuple(mult * ms[p] for p in range(n))
        L = sum(target)
        if L > max_steps:
            results[mult] = f"L={L} too long"
            continue

        # Count walks
        count = [0]

        def dfs(path, fc):
            if count[0] >= 1:
                return
            pos = path[-1]
            step = len(path)
            if step == L:
                nxt = path[0]
                if abs(pos - nxt) % n in (1, n - 1):
                    if all(fc[p] == target[p] for p in range(n)):
                        count[0] += 1
                return
            remaining = L - step
            needed = sum(max(0, target[p] - fc[p]) for p in range(n))
            if needed > remaining:
                return
            for d in [1, -1]:
                nxt = (pos + d) % n
                if fc[nxt] < target[nxt]:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs(path, fc)
                    path.pop()
                    fc[nxt] -= 1

        for p0 in range(n):
            if count[0] >= 1:
                break
            fc = [0] * n
            fc[p0] = 1
            dfs([p0], fc)

        results[mult] = f"L={L}, exists={count[0]>0}"
    return results


def check_walk_existence_fast(n, ms, mult=1, timeout=30):
    """Quick check if walks exist for given fc multiplier."""
    target = [mult * ms[p] for p in range(n)]
    L = sum(target)
    found = [False]
    t0 = time.time()

    def dfs(path, fc):
        if found[0] or time.time() - t0 > timeout:
            return
        pos = path[-1]
        step = len(path)
        if step == L:
            nxt = path[0]
            if abs(pos - nxt) % n in (1, n - 1):
                if all(fc[p] == target[p] for p in range(n)):
                    found[0] = True
            return
        remaining = L - step
        needed = sum(max(0, target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < target[nxt]:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1

    for p0 in range(n):
        if found[0]:
            break
        fc = [0] * n
        fc[p0] = 1
        dfs([p0], fc)

    return found[0], time.time() - t0


def main():
    n = 9

    print("=" * 70)
    print("RA12: Walk existence check for all placements")
    print("=" * 70)

    placements = [
        ((0, 2, 4), "(2,2,5)"),
        ((0, 2, 5), "(2,3,4)"),
        ((0, 2, 6), "(2,4,3)"),
        ((0, 3, 6), "(3,3,3)"),
    ]

    for pos, label in placements:
        ms = make_ms(n, pos)
        print(f"\nPlacement {label}: pos={pos}, ms={ms}")

        for mult in [1, 2]:
            target = [mult * ms[p] for p in range(n)]
            L = sum(target)
            if L > 50:
                print(f"  mult={mult}: L={L} (too long for exhaustive search)")
                continue
            exists, elapsed = check_walk_existence_fast(n, ms, mult, timeout=60)
            print(f"  mult={mult}: L={L}, walks_exist={exists} ({elapsed:.1f}s)")

    # For the asymmetric placements that have 0 walks at mult=1,
    # try to understand WHY.
    print(f"\n{'='*70}")
    print("WHY no walks for (2,2,5)?")
    print(f"{'='*70}")

    ms = make_ms(n, (0, 2, 4))
    print(f"ms={ms}")
    print(f"Binary at 0, 2, 4 (all even)")
    print(f"Ternary at 1, 3, 5, 6, 7, 8")
    print(f"fc needed: P0=2, P1=3, P2=2, P3=3, P4=2, P5=3, P6=3, P7=3, P8=3")
    print(f"Total = 24")

    # The walk must visit P5,P6,P7,P8 (4 consecutive ternary) 3 times each.
    # Between P4 and P5 there's the boundary binary->ternary.
    # Between P8 and P0 there's the boundary ternary->binary.
    # To reach P5-P8 from the binary cluster, the walk must traverse this arc.
    # Each traversal of the 4-proc arc uses 3-4 steps.
    # 12 visits to 4 procs requires at least 3 traversals (6 crossings).
    # But the walk also needs to visit P0-P4 the right number of times.

    # Let me check a simpler property: is the fc vector achievable
    # by ANY ring walk (ignoring wrap-around)?
    print(f"\nReachability check: can a path on Z_9 visit each proc the right # of times?")
    print(f"This is always possible -- it's a graph connectivity issue, not parity.")
    print(f"The issue must be the WRAP-ADJACENCY constraint (word[23] adj to word[0]).")

    # The wrap-adjacency is the key constraint. Without it, walks always exist
    # (just traverse the ring back and forth). With it, we need the walk to
    # form a closed loop, and the fc constraint must be compatible.

    # For n=9, odd ring, the walk is equivalent to a closed walk on the ring
    # of length 24 where each step goes +1 or -1, and the total
    # displacement is +/-1 (for wrap-adjacency).
    # Actually wait -- wrap-adjacency means word[-1] and word[0] are adjacent.
    # This is the same as: the path word[0], word[1], ..., word[23], word[0]
    # forms a walk of length 25 where the last step is also +/-1.
    # So the total displacement in 24 steps is 0 (since we return to start?).
    # NO -- we don't return to start. We return to a NEIGHBOR of start.
    # So displacement after 24 steps = +/-1 (mod 9).

    # For (2,2,5): binary at {0,2,4}, each visited 2 times.
    # Ternary at {1,3,5,6,7,8}, each visited 3 times.
    # Total displacement = sum of all step directions.
    # Each visit to a proc p contributes to the displacement based on
    # the direction when entering and leaving p.

    # Actually, the total displacement is simply word[23] - word[0] mod 9.
    # This must be +/-1 mod 9.

    # The constraint is:
    # Given fc[p] for each p, does there exist a walk of length 24 on Z_9
    # starting at some p0, with each proc visited fc[p] times, and
    # ending at p0 +/- 1?

    # This is a non-trivial combinatorial problem. Let me check specific cases.

    # For (2,4,3), ms=[2,3,2,3,3,3,2,3,3], binary at {0,2,6}
    # This also had 0 walks. But parity was "FEASIBLE".
    # Let me check it more carefully.

    print(f"\n{'='*70}")
    print("Deep check for (2,4,3): ms=[2,3,2,3,3,3,2,3,3]")
    print(f"{'='*70}")

    ms243 = make_ms(n, (0, 2, 6))
    exists, elapsed = check_walk_existence_fast(n, ms243, 1, timeout=120)
    print(f"mult=1, L=24: exists={exists} ({elapsed:.1f}s)")

    # Try mult=2 for asymmetric placements
    print(f"\n{'='*70}")
    print("Double-length walk search (may be slow)")
    print(f"{'='*70}")

    for pos, label in placements[:3]:
        ms = make_ms(n, pos)
        exists, elapsed = check_walk_existence_fast(n, ms, 2, timeout=120)
        print(f"{label}: mult=2, L={2*sum(ms)}, exists={exists} ({elapsed:.1f}s)")


if __name__ == "__main__":
    main()
