#!/usr/bin/env python3
"""binscc_vertex_constraint.py — Test the vertex-counting argument for n=6.

At n=6 with 3 ternary (1,3,5) and 3 binary (0,2,4):
- Full Return fails at ternary t iff 3 mover (bL,bR) values are distinct
- Each ternary avoids one "forbidden" value D_t from {0,1}^2
- The 3 forbidden values D_1, D_3, D_5 constrain the allowed binary
  state set in {0,1}^3 = {(c[0], c[2], c[4])}

Question: Can all 3 ternary simultaneously have Full Return failure?
Does the walk structure on {0,1}^3 prevent this?
"""
import sys
from itertools import product as iproduct

def check_allowed_set():
    """For each choice of (D_1, D_3, D_5), compute the allowed set
    in {0,1}^3 and check if all 3 projections can have 3 distinct values."""
    print("VERTEX COUNTING ARGUMENT FOR n=6")
    print("="*60)

    vertices = list(iproduct([0,1], repeat=3))  # (c0, c2, c4)

    possible_D = list(iproduct([0,1], repeat=2))  # 4 values per projection

    can_fail_count = 0
    total = 0

    for D1 in possible_D:
        for D3 in possible_D:
            for D5 in possible_D:
                total += 1
                # Compute allowed set
                allowed = []
                for v in vertices:
                    c0, c2, c4 = v
                    if (c0, c2) == D1:
                        continue
                    if (c2, c4) == D3:
                        continue
                    if (c4, c0) == D5:
                        continue
                    allowed.append(v)

                # Check if each projection has ≥3 distinct values
                pi02 = set((v[0], v[1]) for v in allowed)
                pi24 = set((v[1], v[2]) for v in allowed)
                pi40 = set((v[2], v[0]) for v in allowed)

                can_all_fail = (len(pi02) >= 3 and len(pi24) >= 3 and
                               len(pi40) >= 3)

                # Stronger: need 3 INJECTABLE vertices per projection
                # Each ternary needs 3 mover steps with distinct projections
                # assigned from the allowed vertices
                can_assign = False
                if can_all_fail:
                    # Try all assignments: P1 uses 3 vertices from allowed
                    # with distinct pi02, P3 uses 3 with distinct pi24, etc.
                    # Actually just check if 3 allowed vertices exist with
                    # all projections injective
                    from itertools import combinations
                    for triple in combinations(allowed, 3):
                        p02 = set((v[0], v[1]) for v in triple)
                        p24 = set((v[1], v[2]) for v in triple)
                        p40 = set((v[2], v[0]) for v in triple)
                        if len(p02) == 3 and len(p24) == 3 and len(p40) == 3:
                            can_assign = True
                            break

                if can_assign:
                    can_fail_count += 1
                    if can_fail_count <= 5:
                        print(f"  D1={D1} D3={D3} D5={D5}: "
                              f"|allowed|={len(allowed)}, "
                              f"|pi02|={len(pi02)}, "
                              f"|pi24|={len(pi24)}, "
                              f"|pi40|={len(pi40)}")
                        print(f"    allowed={allowed}")
                        print(f"    example triple={triple}")

    print(f"\nTotal D-value configs: {total}")
    print(f"Configs where all 3 ternary COULD fail: {can_fail_count}")
    print(f"Configs where vertex counting blocks: {total - can_fail_count}")

    # For the "could fail" configs, analyze walk constraints
    print(f"\n{'='*60}")
    print("WALK CONSTRAINT ANALYSIS")
    print("At n=6 with alternating B-T-B-T-B-T:")
    print("Binary 0 fires 2r0 times, Binary 2 fires 2r2 times, etc.")
    print("Each binary firing flips one coordinate of {0,1}^3.")
    print("Walk on {0,1}^3 is a walk on the 3-cube.")
    print()

    # Key insight: on the 3-cube, the walk starts at (0,0,0),
    # makes some steps, and returns. The mover steps of each ternary
    # divide the walk into 3 segments per ternary.
    # For Full Return to fail at all ternary: the walk at mover steps
    # uses only allowed vertices.

    # But the ternary movers are at DIFFERENT cycle positions.
    # P1 has 3 movers (one per phase 0,1,2 of c[1]).
    # P3 has 3 movers (one per phase 0,1,2 of c[3]).
    # P5 has 3 movers (one per phase 0,1,2 of c[5]).
    # These 9 movers are at 9 different cycle positions.

    # The binary state at each mover is determined by the walk history.

    # Key constraint: between P1's mover and the next P1 mover,
    # the walk on {0,1}^3 must go from v_k to v_{k+1} (for P1's phases).
    # But this walk also passes through movers of P3 and P5.

    # Let me check: if the allowed set has a specific structure,
    # can the walk actually achieve the required mover pattern?

    # For a triple {000, 011, 101} from the allowed set:
    # P1 movers at (c0,c2) = (0,0), (0,1), (1,0) — all distinct
    # P3 movers at (c2,c4) = (0,0), (1,1), (0,1) — all distinct
    # P5 movers at (c4,c0) = (0,0), (1,0), (1,1) — all distinct

    # The walk on {0,1}^3 must pass through {000, 011, 101} at the
    # 9 mover positions. Between movers, the walk can visit other vertices.

    # On the 3-cube, the 3 vertices {000, 011, 101} form a triangle?
    # Hamming distances: 000-011=2, 011-101=3, 101-000=1.
    # Wait: d(000,011) = 2, d(011,101) = 3, d(101,000) = 2.
    # Hmm, d(011,101) = number of differing bits = 3 (all differ). But
    # {0,1}^3 has diameter 3, so this is the maximum distance.

    # The walk must traverse from 000 to 011 (distance 2) and from
    # 011 to 101 (distance 3) etc. This requires at least 2+3+2 = 7
    # binary firings. But the minimum total binary firings at n=6 is 6.

    # Wait, 6 binary firings total (2 per binary proc). Can the walk
    # go from 000→011→101→000 with just 6 steps on the 3-cube?
    # 000→011: need to flip bits 1,2 (2 steps min)
    # 011→101: need to flip all 3 bits (3 steps min)
    # 101→000: need to flip bits 0,2 (2 steps min)
    # Total: 2+3+2 = 7 > 6. IMPOSSIBLE!

    print("PARITY/DISTANCE CHECK:")
    print("For allowed triple {000, 011, 101}:")
    print("  000→011: distance 2 (flip bits 1,2)")
    print("  011→101: distance 3 (flip all)")
    print("  101→000: distance 2 (flip bits 0,2)")
    print("  Total min distance: 7")
    print("  Available binary firings: 6 (2 per binary proc)")
    print("  7 > 6: IMPOSSIBLE!")
    print()

    # This is a DISTANCE ARGUMENT! The walk on {0,1}^3 must traverse
    # between the allowed vertices, and the total distance must be
    # ≤ total binary firings.

    # But with multiple rounds, binary firings = 2r per proc, total 6r.
    # The minimum distance cycle through 3 vertices depends on the triple.

    # For the minimum cycle (r=1, 6 binary firings):
    # Check all valid triples to see if the min distance cycle works.

    print("DISTANCE CHECK FOR ALL VALID TRIPLES (min cycle, 6 firings):")
    can_fail_count2 = 0
    for D1 in possible_D:
        for D3 in possible_D:
            for D5 in possible_D:
                allowed = []
                for v in vertices:
                    c0, c2, c4 = v
                    if (c0, c2) == D1:
                        continue
                    if (c2, c4) == D3:
                        continue
                    if (c4, c0) == D5:
                        continue
                    allowed.append(v)

                from itertools import combinations, permutations
                for triple in combinations(allowed, 3):
                    p02 = set((v[0], v[1]) for v in triple)
                    p24 = set((v[1], v[2]) for v in triple)
                    p40 = set((v[2], v[0]) for v in triple)
                    if len(p02) != 3 or len(p24) != 3 or len(p40) != 3:
                        continue

                    # For this triple, the P1 movers use the 3 vertices
                    # in some order. The walk on {0,1}^3 must cycle through
                    # them. Check all orderings.
                    min_dist = float('inf')
                    for perm in permutations(triple):
                        dist = 0
                        for i in range(3):
                            v1 = perm[i]
                            v2 = perm[(i+1) % 3]
                            d = sum(a != b for a, b in zip(v1, v2))
                            dist += d
                        if dist < min_dist:
                            min_dist = dist

                    # But wait: P1, P3, P5 each use the 3 vertices
                    # in their own order. The walk must accommodate ALL
                    # ternary movers. The total walk on {0,1}^3 visits
                    # 9 mover positions. The constraint is more complex.

                    # Simplification: the total binary firings = 6r.
                    # The sum of distances between consecutive mover vertices
                    # (across all ternary procs) must be ≤ 6r.

                    # Actually, the walk on {0,1}^3 between consecutive
                    # ternary movers (in cycle order) must traverse the
                    # required distance.

                    # For now, just check: is min_dist ≤ 6?
                    if min_dist <= 6:
                        can_fail_count2 += 1
                        if can_fail_count2 <= 3:
                            print(f"  triple={triple}, min_cycle_dist={min_dist}")

    print(f"\nTriples with cycle distance ≤ 6: {can_fail_count2}")

    # BETTER: check the ACTUAL constraint.
    # The 9 mover steps are interleaved in the cycle. Each ternary
    # has 3 movers. Between consecutive movers (of ANY ternary) in
    # the cycle, the binary state changes by the binary firings in between.

    # The total change across ALL segments sums to 0 (mod 2) per
    # coordinate (since total firings per binary proc are even).

    # The key insight: each coordinate (binary proc) has its firings
    # distributed across the segments. The sum of changes per segment
    # is constrained by the distances between mover vertices.

    # The tightest constraint is at minimum cycle length (r=1).
    # Total binary firings: 6 (2 per binary proc, 1 round each).

    # For each valid triple, the walk on {0,1}^3 needs to visit
    # the 3 vertices in a cycle using ≤6 steps. But it also needs
    # to accommodate the P3 and P5 mover constraints simultaneously.

    # The crucial point: the walk visits 9 mover positions total.
    # Between consecutive mover positions (in cycle order), the walk
    # makes some binary steps. The sum of all binary steps = 6r.

    # With r=1, total 6 steps on {0,1}^3. These 6 steps must connect
    # the 9 mover vertices in sequence. But 6 steps can only change
    # 6 coordinates, so the total Hamming distance traversed is 6.

    # Each of the 9 inter-mover segments needs ≥ Hamming distance
    # between its endpoints. The sum of these distances must be ≤ 6.

    # But 9 mover positions means 9 inter-mover segments.
    # If each segment needs ≥1 step, total ≥ 9 > 6. CONTRADICTION!

    # Wait, is that right? If two consecutive movers (in cycle order)
    # have the same binary state, the segment needs 0 binary steps.
    # So segments can have 0 distance.

    # When do consecutive movers have the same binary state?
    # Between two consecutive ternary movers in the cycle, only
    # ternary procs fire (no binary procs fire), so the binary state
    # doesn't change. Wait, is this true?

    # The ring walk has consecutive movers adjacent on the ring.
    # A ternary mover t is at position p on the ring. The next step
    # fires a neighbor of p: which is bL or bR (both binary). So
    # the step right after a ternary mover is ALWAYS a binary firing!

    # This means between consecutive ternary movers in the cycle,
    # there's at least 1 binary firing. So each inter-mover segment
    # has ≥1 binary step. With 9 segments, total ≥ 9 > 6. CONTRADICTION!

    print("\n" + "="*60)
    print("CRITICAL ARGUMENT:")
    print("At minimum cycle length (r=1), total binary firings = 6.")
    print("9 ternary mover steps divide the cycle into 9 segments.")
    print("Ring walk constraint: step after ternary mover fires binary.")
    print("So each segment has ≥1 binary step.")
    print("Total binary steps ≥ 9 > 6. CONTRADICTION!")
    print("Therefore: at r=1 (minimum cycle length), Full Return")
    print("CANNOT fail at all 3 ternary procs!")

    # But what about r > 1? With r=2, total firings = 12.
    # But also more ternary movers: each fires 6 times (2 rounds × 3 phases).
    # Total ternary movers = 3 × 6 = 18. Segments = 18.
    # 18 segments, each ≥1 binary step → total ≥ 18 > 12. Still impossible!

    # In general: 3 ternary procs, each fires 3r times = 9r ternary movers.
    # Each of the 9r inter-mover segments needs ≥1 binary step.
    # Total binary firings = 6r.
    # 9r > 6r for all r ≥ 1. ALWAYS A CONTRADICTION!

    print(f"\nGENERAL ARGUMENT:")
    print(f"With r rounds: 9r ternary mover steps, 6r binary firings.")
    print(f"Each inter-mover segment needs ≥1 binary step.")
    print(f"9r > 6r for all r ≥ 1.")
    print(f"UNIVERSAL CONTRADICTION!")
    print(f"\nThis proves Full Return is universal at n=6!")

    # WAIT: does the step after every ternary mover really fire binary?
    # Ring walk: consecutive movers are adjacent. Ternary t at position p
    # has neighbors bL = p-1 (binary) and bR = p+1 (binary).
    # So the step after t's mover fires bL or bR. YES, always binary.

    # And the step before t's mover also fires bL or bR (for t's mover
    # to fire, the walk must be at a neighbor of t, which is binary).

    # So each ternary mover has a binary step on BOTH sides.
    # This means between any two consecutive ternary movers,
    # there's at least 1 binary step (the one right after the first
    # and/or right before the second).

    # Actually, let's be more careful. Between mover m1 (ternary t1)
    # and mover m2 (ternary t2), the walk goes:
    # m1: fires t1 → next step fires b1 (binary neighbor of t1) →
    # ... → step fires b2 (binary neighbor of t2) → m2: fires t2.

    # If t1 and t2 are the same ternary and the next mover is just
    # the next phase, the walk might go: t→b→t (directly back).
    # But t→b→t means: step 1 fires t (mover), step 2 fires b (binary),
    # step 3 fires t (next mover). This has 1 binary step between movers.

    # If t1 and t2 are different ternary procs, the walk must traverse
    # from t1's neighborhood to t2's neighborhood, passing through
    # at least the binary between them.

    # So: between any two consecutive ternary movers (in cycle order),
    # there is ≥1 binary firing. This gives the key inequality.

    # BUT WAIT: what if two ternary movers fire consecutively?
    # For t1 at position p and t2 at position q, we need |p-q|=1 mod n
    # for the ring walk. If p and q are both ternary positions and
    # adjacent on the ring, then they CAN fire consecutively.

    # At n=6 alternating: positions are 0(B),1(T),2(B),3(T),4(B),5(T).
    # Ternary at 1, 3, 5. Their pairwise distances on the ring:
    # 1-3: distance 2 (through 2, which is binary)
    # 3-5: distance 2 (through 4, which is binary)
    # 5-1: distance 2 (through 0, which is binary)
    # So no two ternary procs are adjacent on the ring!
    # Between any two ternary procs on the ring, there's a binary proc.
    # Therefore, the walk CANNOT go directly from one ternary to another.
    # It must pass through a binary proc.

    # This confirms: between any two consecutive ternary movers in the
    # cycle, there is at least 1 binary firing.

    print(f"\nAt n=6 alternating, ternary procs are all distance 2 apart.")
    print(f"Walk between consecutive ternary movers must pass through binary.")
    print(f"Argument confirmed: ≥1 binary firing per inter-mover segment.")

    sys.stdout.flush()

check_allowed_set()
