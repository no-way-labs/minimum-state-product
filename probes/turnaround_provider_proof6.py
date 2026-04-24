"""
Turnaround Binary Provider Proof - Part 6: Definitive
======================================================
Prove: all-turnaround for ≥3 binary is IMPOSSIBLE in a zero-winding
good cycle with cwSteps > 0, all fc ≥ 2, n ≥ 5.

Two cases to handle:
1. Same-side turnaround: both fires bounce to same side → dead edge → disconnection
2. Mixed turnaround: fires bounce to different sides → winding parity argument

Combined: show impossibility for any mix of same-side and mixed turnarounds.
"""

import itertools

def main():
    # ================================================================
    # CASE ANALYSIS: Same-side vs Mixed turnaround
    # ================================================================
    print("=" * 70)
    print("CASE ANALYSIS FOR ALL-TURNAROUND IMPOSSIBILITY")
    print("=" * 70)

    # DEFINITIONS:
    # Same-side turnaround at b: both fires bounce to same side S.
    #   Dead edge: the edge between b and not-S neighbor.
    #   Walk NEVER uses this edge.
    #
    # Mixed turnaround at b: fire 1 bounces LEFT, fire 2 bounces RIGHT (or vice versa).
    #   No dead edge. Both edges used (once each direction from b's fires).
    #   BUT: between fire 1 and fire 2, the walk must go from LEFT side
    #   to RIGHT side (or vice versa) WITHOUT passing through b.
    #   This requires going around the ring, contributing ±1 winding.

    # KEY LEMMA (Mixed turnaround excursion winding):
    # For mixed turnaround at b, one excursion goes from LEFT to RIGHT
    # around the ring, the other goes from RIGHT to LEFT.
    # Each excursion winds exactly once around the ring.
    # One contributes +1, the other -1 winding. Net = 0.
    # (Verified computationally: all mixed TA at n=5 have excursion windings ±5 = ±1*n,
    #  but wait, winding was ±5 with n=5... that's ±1 full winding each.)

    # Actually, let me reconsider. The winding number of an excursion:
    # Excursion starts at b, goes to side S, returns to b from side T.
    # For mixed TA (S≠T): the excursion goes from side S of b around to side T.
    # This is necessarily a full ring traversal: winding ±1.
    # For same-side TA (S=T): the excursion goes and returns same side: winding 0.

    # For the full cycle: winding = sum of excursion windings (over all procs).
    # Each binary has 2 excursions. Each ternary has fc(t) excursions.

    # For a binary proc b:
    # - Same-side TA: both excursions have winding 0.
    # - Mixed TA: one excursion has winding +1, other has winding -1. Net = 0.

    # KEY INSIGHT: Mixed turnaround excursions wind around the ring.
    # With 3 mixed-turnaround binary procs: 6 winding excursions (3 pairs).
    # These are nested/interleaved. The excursion of b1 might contain
    # the excursion of b2 inside it.

    # But here's the structural constraint:
    # A mixed TA excursion of b visits ALL procs on the ring (it winds once).
    # It visits the other binary procs too. When it visits binary b2,
    # b2 fires during this excursion (since b2 fires exactly 2 times total
    # and the excursion covers the whole ring).

    # Actually, the excursion visits procs but doesn't necessarily fire them.
    # The excursion is a segment of the mover word. The movers in this segment
    # include all procs that fire during this segment.

    # With cycle length L = 2*3 + 3*(n-3) = 3n-3 (for 3 binary, n-3 ternary):
    # Actually L = sum(ms) = 3*2 + (n-3)*3 = 6 + 3n - 9 = 3n - 3.
    # Wait: 3 binary with ms=2, (n-3) ternary with ms=3: L = 3*2 + (n-3)*3 = 3n-3.

    # For mixed TA at b: excursion 1 winds once (+1), length L1.
    # Excursion 2 also winds once (-1), length L2.
    # L1 + L2 = L - 2 = 3n - 5 (excluding b's 2 fires).
    # Each excursion must visit at least n-1 procs (full ring minus b).
    # Minimum excursion length to wind once: n-1 steps.
    # So L1 >= n-1 and L2 >= n-1.
    # L1 + L2 = 3n - 5. With L1,L2 >= n-1: 2(n-1) <= 3n-5 → n >= 3. OK.

    # Now with 3 mixed TA binary procs b1, b2, b3:
    # Each has 2 winding excursions, total 6 excursions.
    # But these excursions share steps! They're interleaved in the mover word.
    # An excursion of b1 contains fires of b2 and b3.

    # The excursion structure creates a nesting. Let me think about it
    # as intervals on the cyclic mover word.
    # b1 fires at positions f1_1, f1_2.
    # b2 fires at positions f2_1, f2_2.
    # b3 fires at positions f3_1, f3_2.
    # The excursions of b1 are [f1_1+1 .. f1_2-1] and [f1_2+1 .. f1_1-1] (cyclic).
    # Within excursion 1 of b1: b2 fires some number of times (0, 1, or 2).
    #   If b2 fires 2 times: both b2 fires are inside this excursion.
    #   Both excursions of b2 are contained in excursion 1 of b1.
    #   Winding of b2's excursions: +1 and -1 (net 0).
    #   They don't contribute to the winding of b1's excursion.
    #   But b1's excursion must wind +1 on its own.
    #   The winding of b1's excursion = sum of windings of sub-excursions
    #   + the "base" winding from the walk structure.
    #   Hmm, this gets complicated.

    # SIMPLER ARGUMENT:
    # Consider the "crossing parity" at binary proc b.
    # Define: a "passage through b" is a pair of consecutive steps (prev, b, next)
    # where prev and next are on DIFFERENT sides of b.
    # A "bounce at b" is a pair where prev and next are on the SAME side.
    #
    # For a TURNAROUND: both fires are bounces (by definition).
    # Number of passages through b = 0.
    #
    # But: in a zero-winding cycle, the walk must cross every cut an equal
    # number of times in each direction. Consider the cut between b and right(b).
    # Passages through b contribute to crossings of this cut.
    # Bounces at b (from the left) contribute NOTHING to this cut.
    # Bounces at b (from the right) contribute 2 crossings (one each way) to this cut.
    #
    # For same-side LEFT TA: 0 passages, 2 left-bounces. Cut (b, right): 0 crossings from b.
    # For same-side RIGHT TA: 0 passages, 2 right-bounces. Cut (b, right): 4 crossings from b.
    # For mixed TA: 0 passages, 1 left-bounce + 1 right-bounce. Cut (b, right): 2 crossings from b.

    # Total crossings of cut (b, right) from all procs must be even and >= 0.
    # Moreover, if all procs between b and the next binary (in the CW direction)
    # are ternary, their fire patterns also contribute to this cut.

    # ================================================================
    # NEW APPROACH: The parity argument via "local winding"
    # ================================================================
    print("\nNEW APPROACH: Edge parity argument")
    print("-" * 40)

    # Consider the walk restricted to the edges around any binary proc b.
    # b has exactly 2 fires (fc=2). Each fire uses 2 edges (arrival + departure).
    # Total: 4 edge-uses involving b.
    #
    # The 4 edges can be classified:
    # Left-arrival: (b-1) -> b
    # Left-departure: b -> (b-1)
    # Right-arrival: (b+1) -> b
    # Right-departure: b -> (b+1)
    #
    # Each fire contributes 1 arrival + 1 departure = 2 edge-uses.
    # Let:
    #   LA = # left-arrivals = # times walk goes (b-1)->b then b fires
    #   LD = # left-departures
    #   RA = # right-arrivals
    #   RD = # right-departures
    #
    # Then LA + RA = 2 (total arrivals = fc = 2)
    #      LD + RD = 2 (total departures = fc = 2)
    #
    # For turnaround: arr_side = dep_side for each fire.
    # Fire types: (L,L) or (R,R) or mixed.
    #
    # Turnaround means: each fire has arr=dep.
    # If both (L,L): LA=2, LD=2, RA=0, RD=0.
    # If both (R,R): LA=0, LD=0, RA=2, RD=2.
    # If (L,L)+(R,R): LA=1, LD=1, RA=1, RD=1.
    #
    # Now consider the cut JUST TO THE RIGHT of b: between b and (b+1).
    # CW crossings of this cut: RD (b departs right) + RA'... no, only b's contribution.
    # B's contribution to this cut's crossings:
    #   CW: RD (steps b -> b+1)
    #   CCW: RA (steps b+1 -> b)
    #
    # For zero-winding, total CW = total CCW at every cut.
    # b's contribution: CW = RD, CCW = RA.
    # Other procs' contributions must make up the difference.

    # KEY: Net flow from b at cut (b, b+1) = RD - RA.
    # For same-side LEFT: RD - RA = 0 - 0 = 0.
    # For same-side RIGHT: RD - RA = 2 - 2 = 0.
    # For mixed: RD - RA = 1 - 1 = 0.
    # Always 0! So b always contributes zero net flow, regardless of turnaround type.
    # That's because the walk is a cycle and each proc has equal arrivals and departures.

    # The NET flow at every cut from every proc is 0. This doesn't help distinguish.

    # TOTAL crossings from b at cut (b, b+1): RD + RA.
    # Same-side LEFT: 0.
    # Same-side RIGHT: 4.
    # Mixed: 2.

    # Total crossings must be even (CW=CCW). RA + RD is even always (0, 2, or 4). OK.

    # For same-side LEFT: the cut (b, b+1) has 0 crossings from b.
    # ALL crossings come from other procs. The cut exists and must have >= 2 total
    # crossings (1 CW + 1 CCW minimum) for the walk to be connected across it,
    # UNLESS the walk never crosses this cut.

    # If the walk NEVER crosses cut (b, b+1), the ring is effectively broken at this point.
    # The walk is confined to one side. But b fires (it's on the boundary), so
    # the walk touches b, and b only connects to b-1 (same-side LEFT).
    # The walk: everything is on the LEFT side of b.
    # But (b+1) must also fire (fc >= 2). How does (b+1) fire?
    # (b+1) connects to b and (b+2). Since cut (b, b+1) is never crossed,
    # (b+1) is never reached from b. (b+1) can only be reached from (b+2).
    # Similarly, (b+1) can only depart to (b+2).
    # So (b+1) is confined to the arc {b+1, b+2, ...}.
    # And b is confined to the arc {..., b-1, b}.
    # These are two disjoint walk components connected through the rest of the ring.
    # Wait — these arcs might overlap at the OTHER side (through the other binary procs).

    # For same-side LEFT turnaround at b:
    # Dead edge: (b, b+1). Walk is split into two arcs at this edge.
    # Arc 1: b, b-1, b-2, ...  (containing b)
    # Arc 2: b+1, b+2, ...  (containing b+1)
    # The walk can only be in one arc.
    # But both arcs contain procs that must fire.
    # UNLESS one arc is empty (b+1 = b, impossible) or the arcs reconnect elsewhere.
    #
    # The arcs reconnect at the OTHER side of the ring!
    # The ring minus edge (b, b+1) is a PATH from b to b+1 going the other way.
    # Both b and b+1 are on this path. The walk can reach both.
    # So the dead edge does NOT disconnect the walk — it just forces the walk
    # to reach b+1 from b+2 instead of from b.
    #
    # OK so a single dead edge doesn't disconnect. What about 2 dead edges?

    print("\nConnectivity with dead edges:")
    print("Ring of n nodes, remove k edges → k paths (if edges non-adjacent) or fewer")
    print("Walk must be a cycle on the remaining graph.")
    print("With 2 non-adjacent dead edges: ring breaks into 2 paths (arcs).")
    print("The walk can traverse each arc back and forth.")
    print("BUT the walk is a SINGLE cycle. It must move continuously.")
    print("From one arc, it cannot jump to the other arc (the dead edges are blocked).")
    print("So the walk is CONFINED to one arc. The other arc is unvisited.")
    print("This contradicts fc >= 2 for all procs.")
    print()
    print("With 2 adjacent dead edges: they share a vertex v.")
    print("Removing both edges disconnects v. v can't be reached.")
    print("Contradicts fc(v) >= 2.")

    # ================================================================
    # So: 2 dead edges → impossible (walk can't visit all procs).
    # When do we get 2 dead edges?
    # Each same-side turnaround binary contributes 1 dead edge.
    # With k same-side TA procs: k dead edges (might overlap).
    # ================================================================

    print("\n" + "="*60)
    print("MAIN THEOREM PROOF")
    print("="*60)

    print("""
THEOREM: In a zero-winding good cycle with cwSteps > 0, all fc >= 2,
sub-threshold product, >= 3 binary, n >= 5, NOT all binary procs
can be turnaround.

PROOF:
Let B = {b_1, ..., b_k} be the binary procs, k >= 3.
Suppose for contradiction that ALL are turnaround.

Classify each b_i as:
  - Same-side turnaround: both fires bounce to same side S_i.
    Dead edge D_i = edge between b_i and not-S_i neighbor.
  - Mixed turnaround: fire 1 bounces LEFT, fire 2 bounces RIGHT.
    No dead edge, but the two excursions wind ±1 around the ring.

CASE 1: >= 2 binary procs are same-side turnaround.
  These contribute >= 2 dead edges (counted with multiplicity).
  Sub-case 1a: The dead edges are distinct and non-overlapping.
    The ring minus 2 edges = 2 arc components (disconnected paths).
    The walk, being continuous, is confined to one arc.
    The other arc contains procs with fc >= 2 that are never visited.
    CONTRADICTION.
  Sub-case 1b: Two dead edges overlap (same edge).
    This happens when adjacent binary b1, b2 have b1 TA to RIGHT
    and b2 TA to LEFT: both have dead edge (b1, b2).
    Even with this overlap, the third binary b3 (same-side TA)
    contributes a third dead edge distinct from the shared one.
    Now we have 2 distinct dead edges → CONTRADICTION as above.

    Unless b3 also shares the same dead edge? b3 would need to be
    adjacent to b1 or b2 AND have its dead edge at (b1, b2).
    But b3 is a third distinct proc. Dead edge of b3 is between b3
    and one of its neighbors. For this to be (b1, b2), b3 must equal
    b1 or b2. CONTRADICTION (b3 is distinct).

  Sub-case 1c: Two dead edges are adjacent (sharing a vertex but not an edge).
    E.g., dead edges (b1, b1+1) and (b1+1, b1+2). These disconnect b1+1.
    b1+1 can't be reached: both its edges are dead.
    fc(b1+1) >= 2 but b1+1 is never visited. CONTRADICTION.

CASE 2: <= 1 binary proc is same-side turnaround, so >= 2 are mixed turnaround.
  [Need to prove this is also impossible]
""")

    # Case 2 needs the winding argument. Let me think more carefully.
    # Mixed turnaround at b: excursion 1 winds +1, excursion 2 winds -1.
    # Total winding from b's excursions: 0.
    # But the interleaving of excursions from different procs matters.

    # Actually, let me check: Can >= 2 mixed turnaround procs coexist?
    # From the n=5 data: bp=(0,1,2) has individual mixed TAs but never
    # 2 at the same time.

    print("Checking: can 2+ mixed turnaround binary procs coexist?")

    def neighbors_fn(p, n):
        return [(p-1)%n, (p+1)%n]

    def enum_cycles(n, ms, maxc=100000):
        L = sum(ms)
        rem = list(ms)
        results = []
        def dfs(path, rem):
            if len(results) >= maxc: return
            if len(path) == L:
                if path[0] in neighbors_fn(path[-1], n):
                    results.append(tuple(path))
                return
            last = path[-1]
            for nb in neighbors_fn(last, n):
                if rem[nb] > 0:
                    rem[nb] -= 1
                    path.append(nb)
                    dfs(path, rem)
                    path.pop()
                    rem[nb] += 1
        for s in range(n):
            if rem[s] > 0 and len(results) < maxc:
                rem[s] -= 1
                dfs([s], rem)
                rem[s] += 1
        unique = set()
        for c in results:
            rots = [c[i:]+c[:i] for i in range(len(c))]
            unique.add(min(rots))
        return [list(c) for c in unique]

    def winding(mw, n):
        net = 0
        L = len(mw)
        for i in range(L):
            c, nx = mw[i], mw[(i+1)%L]
            if nx == (c+1)%n: net += 1
            elif nx == (c-1)%n: net -= 1
        return net // n

    def cw_steps(mw, n):
        return sum(1 for i in range(len(mw)) if mw[(i+1)%len(mw)] == (mw[i]+1)%n)

    def fc(mw, n):
        f = [0]*n
        for p in mw: f[p] += 1
        return f

    def classify(mw, b, n):
        L = len(mw)
        fires = [i for i in range(L) if mw[i] == b]
        assert len(fires) == 2
        fi = []
        for idx in fires:
            prev = mw[(idx-1)%L]
            nxt = mw[(idx+1)%L]
            a = 'L' if prev == (b-1)%n else 'R'
            d = 'L' if nxt == (b-1)%n else 'R'
            fi.append((a, d))
        ta = all(a==d for a,d in fi)
        if ta:
            sides = [f[0] for f in fi]
            if sides[0] != sides[1]:
                return 'mixed_ta', fi
            else:
                return 'same_ta_' + sides[0], fi
        return 'passthrough', fi

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        max_mixed = 0

        for bp in itertools.combinations(range(n), 3):
            ms = [3]*n
            for b in bp: ms[b] = 2
            prod = 1
            for m in ms: prod *= m
            if prod >= threshold: continue

            cycles = enum_cycles(n, ms, 100000)
            for cyc in cycles:
                if winding(cyc, n) != 0: continue
                if cw_steps(cyc, n) == 0: continue
                f = fc(cyc, n)
                if any(x < 2 for x in f): continue

                types = [classify(cyc, b, n)[0] for b in bp]
                mixed_count = types.count('mixed_ta')
                if mixed_count > max_mixed:
                    max_mixed = mixed_count
                    print(f"  n={n}, bp={bp}: {mixed_count} mixed TA, types={types}")
                    print(f"    cycle={cyc}")

        print(f"n={n}: max simultaneous mixed TA = {max_mixed}")


if __name__ == '__main__':
    main()
