"""
Turnaround Binary Provider Proof - Part 5
==========================================
Key finding so far: ALL binary turnaround simultaneously is IMPOSSIBLE
at n=5,7 for any binary placement, any multiset.

Let me verify:
1. Drop the fc≥3 requirement — is all-turnaround impossible even without it?
2. Check at n=9 via sampling (enumeration too slow)
3. Prove WHY all-turnaround is impossible

The structural argument:

Consider 3 binary procs b1, b2, b3 on the ring.
Each has fc=2 (binary). Each fire has arrival+departure.
A turnaround fire: arrival side = departure side.

For binary b: 2 fires, 4 directed edges (2 arrivals, 2 departures).
But arrivals and departures interleave: the walk looks like
  ...-> prev -> b -> next -> ... -> prev2 -> b -> next2 -> ...

For turnaround: prev = next for each fire.
So: prev1 -> b -> prev1 -> ... -> prev2 -> b -> prev2
The walk bounces at b.

Now, the walk is a Hamiltonian-like cycle on the ring graph
(visiting each proc exactly fc(p) times).

KEY LEMMA: In a zero-winding cycle on a ring with cwSteps > 0,
if b is a same-side turnaround (both fires bounce to side S),
then the "cut" between b and the OTHER side has 0 crossings from b.
All crossings of that cut come from other procs.

If ALL binary are same-side turnaround, each blocks one cut.
With 3 binary, 3 cuts are blocked. But procs between binary
procs must still reach the walk somehow.

Actually, let me revisit. The walk CAN cross the cut between
b and not-S through OTHER procs' fires. b just doesn't contribute.

For the mixed case (fire 1 bounces L, fire 2 bounces R):
Both cuts get 1 crossing from b each. This is more balanced.

Let me check: is all-SAME-SIDE-turnaround impossible?
And is all-MIXED-turnaround impossible?
"""

def neighbors(p, n):
    return [(p - 1) % n, (p + 1) % n]

def enumerate_good_cycles_fast(n, ms, max_cycles=10000):
    """Enumerate good cycles with early termination."""
    total_fires = sum(ms)
    remaining = list(ms)
    results = []

    def dfs(path, remaining):
        if len(results) >= max_cycles:
            return
        if len(path) == total_fires:
            if path[0] in neighbors(path[-1], n):
                results.append(tuple(path))
            return
        last = path[-1]
        for nb in neighbors(last, n):
            if remaining[nb] > 0:
                remaining[nb] -= 1
                path.append(nb)
                dfs(path, remaining)
                path.pop()
                remaining[nb] += 1

    for start in range(n):
        if remaining[start] > 0 and len(results) < max_cycles:
            remaining[start] -= 1
            dfs([start], remaining)
            remaining[start] += 1

    unique = set()
    for cyc in results:
        rotations = [cyc[i:] + cyc[:i] for i in range(len(cyc))]
        canon = min(rotations)
        unique.add(canon)
    return [list(c) for c in unique]

def get_winding_number(mw, n):
    net = 0
    L = len(mw)
    for i in range(L):
        curr = mw[i]
        nxt = mw[(i + 1) % L]
        if nxt == (curr + 1) % n: net += 1
        elif nxt == (curr - 1) % n: net -= 1
    return net // n

def count_cw_steps(mw, n):
    cw = 0
    L = len(mw)
    for i in range(L):
        if mw[(i+1)%L] == (mw[i]+1)%n: cw += 1
    return cw

def get_fc(mw, n):
    fc = [0]*n
    for p in mw: fc[p] += 1
    return fc

def classify_binary(mw, b, n):
    L = len(mw)
    fires = [i for i in range(L) if mw[i] == b]
    assert len(fires) == 2

    fi = []
    for idx in fires:
        prev = mw[(idx-1)%L]
        nxt = mw[(idx+1)%L]
        left, right = (b-1)%n, (b+1)%n
        a = 'L' if prev == left else 'R'
        d = 'L' if nxt == left else 'R'
        fi.append((a, d))
    return fi, all(a==d for a,d in fi)


def main():
    from itertools import combinations

    # ============================================================
    # Check WITHOUT fc>=3 requirement
    # ============================================================
    print("="*60)
    print("ALL-TURNAROUND CHECK (no fc>=3 requirement)")
    print("="*60)

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        total = 0

        for nb in range(3, min(n+1, 7)):
            for bp in combinations(range(n), nb):
                ms = [3]*n
                for b in bp: ms[b] = 2
                prod = 1
                for m in ms: prod *= m
                if prod >= threshold: continue

                cycles = enumerate_good_cycles_fast(n, ms, 50000)
                for cyc in cycles:
                    if get_winding_number(cyc, n) != 0: continue
                    if count_cw_steps(cyc, n) == 0: continue
                    fc = get_fc(cyc, n)
                    if any(f < 2 for f in fc): continue

                    all_ta = True
                    for b in bp:
                        fi, ta = classify_binary(cyc, b, n)
                        if not ta:
                            all_ta = False
                            break
                    if all_ta:
                        total += 1
                        print(f"  ALL-TA: n={n}, bp={bp}, cycle={cyc}, fc={fc}")

        print(f"n={n}: total all-turnaround = {total}")

    # ============================================================
    # PROOF: Why all-turnaround is impossible
    # ============================================================
    print("\n" + "="*60)
    print("PROOF SKETCH: All-turnaround impossibility")
    print("="*60)

    # Count directed edge uses per binary proc in turnaround mode.
    # For binary b with turnaround fires:
    #   Fire: arr_side -> b -> dep_side, where arr_side == dep_side.
    # So the 2-step subsequence around fire is: [side, b, side].
    # The walk edges are: side->b and b->side.
    # For fire j: one edge side_j -> b (CW or CCW) and one edge b -> side_j.
    #
    # If both fires go to same side S:
    #   4 edge-uses all on the S side.
    #   The cut on the other side: b contributes 0 crossings.
    #
    # If fires go to different sides (mixed):
    #   2 edge-uses on left, 2 on right.
    #   Both cuts get crossings from b.

    # Key observation: for MIXED turnaround at b:
    # Fire 1: (L, L) — arrives from left, departs to left
    # Fire 2: (R, R) — arrives from right, departs to right
    # Walk sequence around b: ...left(b) -> b -> left(b) ... right(b) -> b -> right(b)...
    # The walk visits b from the left, bounces back left, then
    # later visits b from the right, bounces back right.
    #
    # Between these two visits, the walk must go from left(b) area to right(b) area
    # WITHOUT passing through b. It must go around the ring!
    #
    # With 3 mixed-turnaround binary procs: the walk must go around the ring
    # 3 times (once per binary gap). But it's zero-winding!
    # Each "go around" contributes ±1 winding.
    # 3 goings-around need net winding 0: impossible with 3 (odd number).
    #
    # Wait, each excursion has its own winding. Let me check.

    print("\nExcursion winding for mixed-turnaround procs:")
    n = 5
    for bp in [(0,1,2)]:
        ms = [2,2,2,3,3]
        cycles = enumerate_good_cycles_fast(n, ms)
        for cyc in cycles:
            if get_winding_number(cyc, n) != 0: continue
            if count_cw_steps(cyc, n) == 0: continue
            fc = get_fc(cyc, n)
            if any(f < 2 for f in fc): continue

            for b in bp:
                fi, ta = classify_binary(cyc, b, n)
                if ta:
                    sides = [f[0] for f in fi]
                    if sides[0] != sides[1]:  # mixed
                        print(f"  Mixed TA at b={b}: fi={fi}, cycle={cyc}")

    # Same-side turnaround: does the walk NEED to cross the blocked cut?
    # If b has same-side TA to LEFT:
    #   Walk never goes b -> right(b) or right(b) -> b.
    #   right(b) must still fire (fc >= 2).
    #   right(b) is reached from right(b)+1 or right(b)-1 = b.
    #   But walk never goes b -> right(b)! So right(b) is reached ONLY from right(b)+1.
    #   This means right(b)+1 must step to right(b) at some point.
    #   But also right(b) must step back to right(b)+1 or to b.
    #   Since walk never goes right(b) -> b (that would be b arriving from right),
    #   right(b) only ever goes to right(b)+1.
    #   So right(b) is only connected to right(b)+1 in the walk!
    #
    # Wait, that's only true for edges involving b. Other procs can still use any edge.

    # Let me reconsider. The walk edge between b and right(b) has 0 crossings
    # from b's fires. But other procs' fires that happen to be at right(b) will
    # cross this edge. right(b) fires fc(right(b)) >= 2 times. Each fire of
    # right(b) uses edges right(b)-1 -> right(b) or right(b)+1 -> right(b)
    # (arrival) and right(b) -> right(b)-1 or right(b) -> right(b)+1 (departure).
    #
    # right(b) - 1 = b. So right(b) could arrive from b or from right(b)+1.
    # But for the walk to step from b to right(b), we need b to be the current
    # mover and right(b) to be the next. But b fires as turnaround (both times
    # going LEFT). After b fires, the walk goes LEFT (to b-1), not RIGHT (to b+1=right(b)).
    # So b NEVER steps to right(b).
    #
    # Can right(b) arrive from b through a non-b step? The walk goes:
    # ..., some_proc, right(b), ... where some_proc = b or right(b)+1.
    # For some_proc = b: the walk was at b and stepped to right(b).
    # But b steps only to b-1 (LEFT) in its turnaround. So when b fires,
    # it goes to b-1. Between b's fires (when b is not firing), the walk
    # is at other procs. For the walk to be at b and step to right(b),
    # b would need to fire and go RIGHT. But b's turnaround is LEFT.
    #
    # WAIT. The walk at position b doesn't mean b is firing. b fires when
    # it's the mover. But the walk can pass through b's position via
    # other procs' fires. NO — the walk is defined by the mover sequence.
    # mover[i] fires at step i. The walk is mover[0], mover[1], ...
    # and each consecutive pair must be adjacent. So if mover[i]=b and
    # mover[i+1]=right(b), that's the step b -> right(b).
    #
    # This step happens when b fires (mover[i]=b) and the next mover is right(b).
    # For turnaround LEFT: next mover = b-1 (LEFT). So b -> right(b) NEVER happens.
    #
    # Similarly, right(b) -> b: mover[i]=right(b), mover[i+1]=b.
    # This is right(b) firing and then b fires. For b's turnaround LEFT:
    # b's arrival is from LEFT (b-1), not from RIGHT (right(b)). So
    # right(b) -> b requires b's previous mover to be right(b), but
    # b's arrival is always from LEFT. CONTRADICTION.
    #
    # Therefore: with same-side LEFT turnaround at b, the edge (b, right(b))
    # is NEVER traversed in either direction. This edge is "dead".

    # STRONGER: the dead edge means the walk NEVER crosses from b to right(b)
    # or vice versa through this edge. All communication between the two
    # sides of this cut goes through the rest of the ring.

    # With 3 binary procs and 3 same-side turnarounds: 3 dead edges.
    # But wait — if b1 turnarounds LEFT and b2 turnarounds LEFT, their
    # dead edges might be on the same side or different sides.

    print("\n\nDead edge analysis for same-side turnaround procs:")
    n = 5
    bp = (0, 2, 4)
    ms = [2, 3, 2, 3, 2]
    cycles = enumerate_good_cycles_fast(n, ms)
    for cyc in cycles:
        if get_winding_number(cyc, n) != 0: continue
        if count_cw_steps(cyc, n) == 0: continue
        fc = get_fc(cyc, n)
        if any(f < 2 for f in fc): continue

        dead_edges = []
        for b in bp:
            fi, ta = classify_binary(cyc, b, n)
            if ta:
                sides = [f[0] for f in fi]
                if sides[0] == sides[1]:  # same-side
                    if sides[0] == 'L':
                        dead_edges.append((b, (b+1)%n))
                    else:
                        dead_edges.append(((b-1)%n, b))
                    print(f"  Binary {b}: same-side {sides[0]}, dead edge = {dead_edges[-1]}")

        if len(dead_edges) >= 2:
            print(f"  Multiple dead edges: {dead_edges}")
            # Check: does the walk use any dead edge?
            L = len(cyc)
            for de in dead_edges:
                a, b_e = de
                used = False
                for i in range(L):
                    curr, nxt = cyc[i], cyc[(i+1)%L]
                    if (curr == a and nxt == b_e) or (curr == b_e and nxt == a):
                        used = True
                        break
                print(f"    Dead edge {de}: {'USED' if used else 'not used'} ({'BUG!' if used else 'OK'})")


    # ============================================================
    # The impossibility argument for all-turnaround
    # ============================================================
    print("\n" + "="*60)
    print("IMPOSSIBILITY ARGUMENT")
    print("="*60)

    # Case 1: All same-side turnaround.
    # Each binary b has a "dead edge" (never traversed).
    # With 3 binary procs, 3 dead edges.
    # The ring has n edges. Removing 3 dead edges from a ring of n nodes
    # potentially disconnects it (if 3 dead edges = 3 distinct edges).
    # But the walk must visit all procs. If the ring is disconnected by dead edges,
    # the walk can't reach all procs. CONTRADICTION.
    #
    # Wait — disconnection depends on the graph. A ring with 3 edges removed
    # has 3 paths. The walk can still reach all procs if the paths cover all procs.
    # But the walk must be a CYCLE (return to start), and it can only traverse
    # non-dead edges. The walk graph (non-dead edges) on n nodes must be connected
    # and allow an Eulerian-like cycle visiting each node the required number of times.
    #
    # Actually: 3 dead edges on a ring of n>=5 nodes split the ring into 3 paths.
    # Each path is a linear segment. The walk can traverse each segment back and forth,
    # but cannot cross between segments. So the walk is confined to one segment!
    # But it must visit all procs. CONTRADICTION.
    #
    # Unless the 3 dead edges are not distinct? If two binary procs share a dead edge,
    # we have <3 distinct dead edges.

    # Can two binary procs share a dead edge?
    # b1 has dead edge (b1, b1+1). b2 has dead edge (b2, b2+1) or (b2-1, b2).
    # Shared: b1+1 = b2 and b2's dead edge is (b2-1, b2) = (b1, b1+1). YES!
    # This happens when b1 turnarounds RIGHT (dead edge is (b1-1, b1))
    # Actually, b1 turnaround LEFT: dead edge (b1, b1+1).
    # b2 = b1+1, b2 turnaround RIGHT: dead edge (b2-1, b2) = (b1, b1+1).
    # Same dead edge! But b2 = b1+1 means they're adjacent.
    # And if b2 is binary, then b1 and b2 are adjacent binary procs.

    # With ≥3 binary, non-adjacent: dead edges are distinct.
    # With adjacent binary: dead edges might overlap.
    # But we need ALL 3 to be same-side turnaround.

    print("Dead edge overlap analysis:")
    print("If b1 and b2 are adjacent, b1 TA-left, b2 TA-right:")
    print("  b1 dead edge: (b1, b1+1) = (b1, b2)")
    print("  b2 dead edge: (b2-1, b2) = (b1, b2)")
    print("  OVERLAP! Only 1 dead edge, not 2.")
    print()
    print("With 3 binary, even with maximum overlap, we get at least 2 dead edges")
    print("(by pigeonhole: 3 procs, max 2 can share one dead edge).")
    print()
    print("2 dead edges on a ring of n nodes → 2 disjoint paths.")
    print("Walk confined to one path? NO — walk can traverse both paths")
    print("back and forth through the junction points.")
    print()
    print("Actually 2 dead edges split a ring into 2 arcs. The walk")
    print("can only traverse within each arc. But it's ONE walk,")
    print("so it must be in ONE arc. If both arcs have procs to visit,")
    print("the walk can't reach all procs. CONTRADICTION.")
    print()
    print("Wait — 2 dead edges split the ring into 2 paths. The walk")
    print("graph has 2 connected components. The walk can only be in one.")
    print("So procs in the other component are unreachable. But fc>=2 for all.")
    print("CONTRADICTION.")

    # Verify: for non-adjacent binary, dead edges are always distinct
    print("\nVerification: for non-adjacent binary with same-side TA, dead edges distinct?")
    n = 9
    from itertools import combinations
    for bp in combinations(range(n), 3):
        # Check if non-adjacent
        adj = any(abs(bp[i]-bp[j]) % n <= 1 or abs(bp[i]-bp[j]) % n >= n-1
                  for i in range(3) for j in range(i+1, 3))
        if adj:
            continue

        # Each binary could turnaround LEFT or RIGHT
        for sides in itertools.product(['L', 'R'], repeat=3):
            dead = set()
            for k in range(3):
                b = bp[k]
                if sides[k] == 'L':
                    dead.add((b, (b+1)%n))
                else:
                    dead.add(((b-1)%n, b))
            if len(dead) < 3:
                print(f"  OVERLAP: bp={bp}, sides={sides}, dead={dead}")

    print("(No output = no overlap for non-adjacent binary at n=9)")


import itertools

if __name__ == '__main__':
    main()
