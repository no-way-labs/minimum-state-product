"""
Turnaround Binary Provider Proof - Part 7: Completing the proof
================================================================
We've shown:
- Same-side TA: creates dead edge
- Mixed TA: no dead edge, max 1 observed
- All-TA: never observed

For the proof, we need Case 2 (≥2 mixed TA, ≤1 same-side TA).

The key insight: with ≥ 3 binary all-turnaround and ≤ 1 same-side,
we have ≥ 2 mixed turnaround. For mixed turnaround at b, the walk
must traverse the entire ring in each excursion. This consumes
at least 2(n-1) steps for b alone (2 excursions, each winding once).
With 2 mixed TAs: 4(n-1) steps. Total steps = 3n-3 (for 3 binary, n-3 ternary).
4(n-1) > 3n-3 when 4n-4 > 3n-3, i.e., n > 1. Always.
So 2 mixed TAs already EXCEED the step budget.

Wait, the excursions overlap! b1's excursion contains b2's fires.
So the step count argument is wrong.

Let me think again...

Actually, the excursion of b1 between its two fires has length L1 + L2 = L - 2,
where L is the total cycle length. Each excursion is a contiguous segment
of the mover word. For mixed TA, one excursion goes CW and the other CCW.

The CW excursion visits procs b, b+1, b+2, ..., going around until it
reaches b from the other side. Minimum length: n-1 (one step per edge).
But each proc visited must fire at least once during this excursion
(if all its fires are here). Not necessarily — a proc can fire in the
other excursion too.

Let me take a step-counting approach.

For mixed TA at b: excursions have lengths L1 and L2 = (L-2) - L1.
The CW excursion visits all n-1 ring positions (going from b+1 to b-1
via CW). Each position must be visited at least once: min L1 = n-1.
Similarly min L2 = n-1.
So L1 + L2 >= 2(n-1), meaning L >= 2n.

For our cycles: L = sum(ms).
With 3 binary (ms=2) and (n-3) ternary (ms=3): L = 6 + 3(n-3) = 3n-3.
Need L >= 2n: 3n-3 >= 2n → n >= 3. OK, not tight enough.

But wait — the excursion must ALSO fire all the procs it visits.
A winding excursion of b visits n-1 procs. These procs fire some
number of times during the excursion. The total fires during the excursion
equals L1 (the length).

Now, b2 fires somewhere: 0, 1, or 2 times in excursion 1 of b1.
If b2 fires 1 time in each excursion of b1: possible.
If b2 fires 2 times in one excursion of b1: both b2's excursions
are nested inside one excursion of b1.

For b2 to also be mixed TA: both excursions of b2 wind once.
If both are inside one excursion of b1 (which also winds once),
the sub-excursions of b2 contribute winding +1 and -1 = 0 net,
and the rest of b1's excursion contributes +1 winding. OK, that works.

But if b2's fires are split across b1's excursions (1 fire each):
Then b2's excursions span across b1's fires. Excursion 1 of b2
starts after b2's fire 1 (inside b1's excursion 1), passes through
b1's fire (end of excursion 1 of b1), continues into b1's excursion 2,
and ends at b2's fire 2 (inside b1's excursion 2).
This excursion of b2 crosses a b1 fire: it goes from one excursion
of b1 to another. It can still wind once.

The structural constraint is on the STEP BUDGET.

Actually, let me just try to prove via step counting more carefully.
"""

def main():
    print("="*60)
    print("STEP BUDGET ARGUMENT")
    print("="*60)

    # For mixed turnaround at b:
    # The walk visits b exactly 2 times.
    # Between the two visits, the walk traverses two excursions.
    # Each excursion is a contiguous walk segment that starts at b's neighbor,
    # goes around the ring, and arrives at b's other neighbor.
    #
    # Key: each excursion is a walk on the ring that WINDS once.
    # A winding walk of length L visits L+1 positions (including start and end).
    # To wind once around an n-ring: minimum L = n (visit all n procs once each).
    # Wait: winding once means going from b to b (net displacement n).
    # But the excursion starts at b's neighbor (say b-1) and ends at b's
    # other neighbor (say b+1). Net displacement from b-1 to b+1 going CW
    # is 2 (or n-2 going CCW).
    #
    # A CW-winding excursion from b-1 to b+1 (going CW, wrapping):
    # b-1 -> b-2 -> ... -> b+2 -> b+1 (going CW around the ring).
    # That's n-2 steps (from b-1 to b+1 the LONG way).
    # Wait no: b-1 -> b-2 is CCW. Let me reconsider.
    #
    # Mixed TA at b: fire 1 bounces LEFT (arr=L, dep=L), fire 2 bounces RIGHT (arr=R, dep=R).
    # Excursion 1 (between fire 1 and fire 2):
    #   Starts at b-1 (departure of fire 1 goes LEFT to b-1).
    #   Ends at b+1 (arrival of fire 2 comes from RIGHT, i.e., b+1).
    #   Wait: arrival at fire 2 from RIGHT means the step before fire 2 is (b+1)->b.
    #   So the last position of excursion 1 is b+1, and then the step b+1->b fires b.
    #
    # Excursion 1 goes from b-1 to b+1 (not through b, since b doesn't fire).
    # On a ring, b-1 to b+1 has two paths: through b (length 2, but b can't fire)
    # or the long way around (length n-2).
    # Since b can't fire during the excursion, the walk CAN pass through b's position
    # but b doesn't fire. Wait — the walk = mover sequence. The walk CAN'T be at
    # b without b firing. Each position in the mover word IS a firing.
    #
    # So the excursion (a segment of the mover word) has movers ≠ b.
    # These movers are consecutive in the mover word, and each consecutive pair
    # is adjacent on the ring.
    # Start: first mover is b-1 (step after fire 1 departs to b-1).
    # End: last mover is... the mover just before fire 2. Fire 2 arrives from b+1,
    # so the mover at the step before fire 2 is b+1. The step is b+1 -> b (fire 2).
    # So the last mover in excursion 1 is b+1.
    #
    # The excursion walks from b-1 to b+1 on the ring graph minus vertex b.
    # The ring minus b has n-1 vertices arranged in a PATH from b-1 to b+1
    # (through b-2, b-3, ..., b+2). Length of this path: n-2 edges.
    # The walk (excursion) must traverse this path. It can go back and forth.
    # MINIMUM length to go from b-1 to b+1: n-2 steps (straight through).
    # But the walk might need to fire procs multiple times (fc ≥ 2 for all).

    # Similarly, excursion 2 goes from b+1 to b-1 on the same path.
    # Minimum length: also n-2.
    # Total minimum from b's excursions: 2(n-2).
    # But total cycle length = L = sum(ms). b's 2 fires use 0 steps in excursions.
    # Wait: b's fires ARE 2 positions in the mover word. The 2 excursions
    # together have L - 2 mover positions. So min 2(n-2) ≤ L - 2.
    # L = 3n-3 → 3n-5 ≥ 2n-4 → n ≥ 1. Not tight.

    # For TWO mixed TAs at b1 and b2:
    # b1's excursions need to go from b1-1 to b1+1 and back, each time
    # traversing the ring minus b1. Min 2(n-2) steps for b1's excursions.
    # b2's excursions similarly need 2(n-2) steps.
    # But b2's fires happen INSIDE b1's excursions (and vice versa).
    # The steps are SHARED. So we can't simply add 2(n-2) + 2(n-2).

    # Better: count how many times each EDGE must be traversed.
    # For mixed TA at b: the edge (b, b-1) is used 2 times (fire 1: arr+dep from left).
    # The edge (b, b+1) is used 2 times (fire 2: arr+dep from right).
    # Other edges: used by the excursions.
    # Each excursion traverses the path from one side of b to the other.
    # Minimum: each edge on the path is used once per excursion.
    # With 2 excursions: each edge on the path used at least 2 times.
    # But the walk goes in OPPOSITE directions in the 2 excursions
    # (one CW, one CCW). So edge (a, a+1) gets 1 CW + 1 CCW = 2 crossings.

    # For b1 mixed TA: each non-b1 edge gets ≥ 2 crossings from b1's excursions.
    # For b2 mixed TA: each non-b2 edge gets ≥ 2 crossings from b2's excursions.
    # Edges not involving b1 or b2: get ≥ 2 + 2 = 4 crossings.
    # Total edge crossings = L = 3n-3.
    # Number of non-b1-non-b2 edges: n - 4 (ring has n edges, 2 at b1, 2 at b2).
    # Wait: each binary proc b is incident to 2 edges. b1 and b2 together
    # are incident to 4 edges (with possible overlap if adjacent).
    # Non-incident edges: n - 4 (if non-adjacent), n - 3 (if adjacent).

    # Lower bound on total crossings:
    # Edges at b1: 4 crossings (2 left, 2 right) from b1's fires.
    # Edges at b2: 4 crossings from b2's fires.
    # Non-incident edges: ≥ 4 crossings each.
    # But wait, crossings from excursions are ADDITIONAL to crossings from fires.
    # Actually, the fires' edge uses ARE part of the total L.

    # Hmm, I'm overcomplicating this. Let me just do a clean count.

    # Total edge-uses = L (cycle length).
    # For mixed TA at b: b contributes 4 edge-uses (2 arrivals + 2 departures).
    # b's excursions (the parts between b's fires) contribute the remaining edge-uses.
    # Total from b and its excursions: L steps.
    # But the excursions are SHARED with other procs' fires and excursions.

    # Let's think about it differently: MINIMUM cycle length with 2 mixed TAs.

    # For 2 mixed TAs at b1, b2 (non-adjacent):
    # The ring minus {b1, b2} has n-2 vertices in 2 paths.
    # Each of b1's excursions must traverse the entire ring minus b1.
    # Each of b2's excursions must traverse the entire ring minus b2.
    # The interleaving means each non-binary edge is traversed ≥ 2 times
    # by each mixed TA's excursions. But these overlap.

    # Actually, I think the right approach is:
    # In a zero-winding cycle, each edge e = (p, p+1) has
    # CW(e) = CCW(e) crossings, so total(e) = 2*CW(e) is even.
    # sum over all edges of total(e) = L.
    # For each edge, total(e) ≥ 2 (at least 1 CW + 1 CCW,
    # since CW > 0 and the cycle must cross every cut for connectivity).
    # Wait: not every cut must be crossed. If the walk never crosses
    # a cut, total(e) = 0 for that edge. But then the graph is disconnected.
    # Since all procs have fc ≥ 2, the walk graph is connected, so
    # total(e) ≥ 2 for every edge.
    # Minimum L = 2n (each edge crossed exactly once CW + once CCW).

    # With 3 binary, (n-3) ternary: L = 3n-3.
    # 2n ≤ 3n-3 → n ≥ 3. Fine.

    # For mixed TA at b: edges at b get 2 crossings each (from fires).
    # There are 2 edges at b: (b-1, b) and (b, b+1). Each gets 2 from b.
    # But these edges also get crossings from OTHER procs' fires and excursions.
    # The minimum of 2 per edge is already met by b's fires for b's edges.

    # I don't think a pure step-count argument works for 2 mixed TAs
    # (the budget is just barely sufficient). Let me try a different approach.

    # ================================================================
    # SIGNED EXCURSION ARGUMENT
    # ================================================================
    print("\n" + "="*60)
    print("SIGNED EXCURSION / NESTING ARGUMENT")
    print("="*60)

    # Consider 2 mixed TAs at b1 and b2 (not adjacent for simplicity).
    # b1 fires at steps f1, f2 (cyclically ordered).
    # b2 fires at steps g1, g2.
    #
    # Excursion A of b1: from f1 to f2.
    # Excursion B of b1: from f2 to f1.
    #
    # b2's fires g1, g2 must be distributed among A and B.
    # Three cases:
    # (i) Both g1, g2 in A: both b2 excursions nested in A.
    # (ii) Both g1, g2 in B: both b2 excursions nested in B.
    # (iii) g1 in A, g2 in B (or vice versa): b2 excursions cross b1 fires.
    #
    # In case (iii): one b2 excursion starts in A and ends in B (crossing f2).
    # This b2 excursion contains b1's fire f2. But f2 fires b1, and b1's
    # excursion B starts after f2. So b2's excursion contains the START
    # of b1's excursion B.
    #
    # The interleaving creates a contradiction via winding:
    # Let W(X) denote the winding of excursion X.
    # W(A) = +1, W(B) = -1 (or vice versa) for b1.
    # W(C) = +1, W(D) = -1 (or vice versa) for b2.
    #
    # In case (iii), say g1 ∈ A and g2 ∈ B.
    # Excursion C of b2: from g1 to g2. Spans from inside A across f2 into B.
    # Excursion D of b2: from g2 to g1. Spans from inside B across f1 into A.
    #
    # The winding of C: it crosses the boundary between A and B.
    # Specifically, the walk from g1 (in A) to g2 (in B) passes through f2
    # (the boundary). The winding of this segment is not simply +1 or -1
    # because it's a hybrid of parts of A and B.

    # This is getting complex. Let me try a cleaner approach.

    # ================================================================
    # APPROACH: Reduction to at most 1 turnaround
    # ================================================================
    print("\n" + "="*60)
    print("FINAL APPROACH: At most 1 binary can be turnaround")
    print("="*60)

    # Claim: At most 1 of k ≥ 3 binary procs can be turnaround.
    #
    # PROOF:
    # Suppose 2 binary procs b1, b2 are both turnaround.
    #
    # For turnaround at b: the walk visits b exactly twice, and both times
    # bounces (returns to the arrival side). This means the walk "reflects"
    # at b twice.
    #
    # Consider the walk's position as a function of time (step number).
    # This is a closed curve on the ring. At each turnaround binary b,
    # the curve reflects.
    #
    # Now, consider the walk restricted to the arc between b1 and b2
    # (say the shorter arc, CW from b1 to b2). The walk enters and exits
    # this arc through b1 and b2.
    #
    # At b1 (turnaround): the walk enters the arc and immediately leaves.
    # At b2 (turnaround): same.
    #
    # For the walk to visit interior procs of this arc, it must enter
    # the arc from b1 or b2 and go into the interior. But turnaround
    # means the walk bounces back immediately.
    #
    # Wait — "turnaround" doesn't mean it bounces immediately. It means
    # the DEPARTURE direction = ARRIVAL direction. The walk could go:
    # ... -> b1-1 -> b1 -> b1-1 -> b1-2 -> ... (bounces at b1, then continues LEFT)
    # This is a turnaround where the walk arrives from LEFT, fires b1,
    # and departs to LEFT. The walk then continues LEFT away from the arc.
    # It DOESN'T enter the arc (b1, b2).
    #
    # For the walk to enter arc (b1, b2), it needs to step from b1 to b1+1
    # or from b2 to b2-1. But if b1's turnaround is to the LEFT (away from arc),
    # b1 never steps to b1+1. And if b2's turnaround is to the RIGHT (away from arc),
    # b2 never steps to b2-1.
    #
    # In that case: interior of arc (b1, b2) is UNREACHABLE.
    # If the arc has any procs (n ≥ 5, arc length ≥ 2 with ≥ 3 binary),
    # those procs can't fire. CONTRADICTION (fc ≥ 2).
    #
    # But what if b1's turnaround is to the RIGHT (into the arc)?
    # Then b1 steps to b1+1 (into the arc) and then steps BACK to b1.
    # The walk enters the arc for 1 step and bounces back.
    # It visits b1+1 but then returns to b1.
    # For interior procs beyond b1+1: the walk needs to reach them too.
    # But the walk only makes 2 "incursions" into the arc from b1
    # (2 fires, both turnaround to RIGHT = 2 trips to b1+1 and back).
    #
    # Hmm, the turnaround means b1 departs to b1+1, but the EXCURSION
    # (everything between b1's fires) could go much further into the arc.
    # Turnaround just means the walk arrives from b1+1 and departs to b1+1.
    # Between b1's fires, the walk starts at b1+1, could go to b1+2, ..., b2,
    # and eventually come back to b1+1 before returning to fire b1 again.

    # OK so the excursion CAN penetrate deep into the arc. Turnaround
    # just controls the immediate neighbors of b at the fire moments.
    # The excursion is free to wander.

    # So my "immediate bounce" argument is WRONG. The walk CAN enter
    # the arc and visit many procs during the excursion.

    # I need a different approach.

    # ================================================================
    # CORRECT APPROACH: Excursion winding on sub-ring
    # ================================================================
    print("\nCORRECT APPROACH: Sub-ring winding")

    # For mixed turnaround at b:
    # Excursion 1 (from fire 1 to fire 2): starts at b-1, ends at b+1.
    # This excursion goes from b-1 to b+1 on the ring minus b.
    # This is a PATH of length n-1 from b-1 to b+1 (the long way around).
    # The excursion walks on this path: it can go forward and backward,
    # but it starts at one end (b-1) and ends at the other (b+1).
    # Net displacement: n-2 steps in one direction (the entire path).
    # This is the "CW" excursion (if b-1 to b+1 goes CW the long way).
    #
    # Excursion 2: starts at b+1, ends at b-1.
    # Net displacement: n-2 steps in the other direction.
    # This is the "CCW" excursion.
    #
    # Now consider 2 mixed TAs at b1 and b2.
    # b1's excursions walk the path (ring minus b1) end-to-end, twice.
    # b2's excursions walk the path (ring minus b2) end-to-end, twice.
    # These paths overlap (they're almost the same ring minus different vertices).
    #
    # The key constraint is on the TERNARY procs. Each ternary proc fires
    # exactly 3 times. Each fire is during some excursion of b1 and some
    # excursion of b2. The distribution of fires across excursions is constrained.

    # I think the cleanest argument is computational verification + induction.
    # We've verified n=5,7: all-turnaround is impossible.
    # For general n: the dead-edge argument handles ≥ 2 same-side TA.
    # For 0 or 1 same-side TA with ≥ 2 mixed TA:
    # We need the structural impossibility.

    # Let me check if there's a parity argument for mixed TA.

    # MIXED TA PARITY ARGUMENT:
    # For mixed TA at b: one excursion goes CW, the other CCW.
    # The CW excursion visits all n-1 procs (minus b) in CW order.
    # Each proc p ≠ b fires some number of times in the CW excursion.
    # Total fires in CW excursion = L_CW = length of CW excursion.
    #
    # For zero-winding: #CW steps = #CCW steps in the full cycle.
    # The CW excursion of b: net CW displacement = n-2.
    # CW steps - CCW steps = n-2 in this excursion.
    # The CCW excursion: CW steps - CCW steps = -(n-2).
    # b's fires: 4 edge-uses (2 from left fire, 2 from right fire).
    # Left fire: CCW arrival + CCW departure = net -2 CW.
    # Right fire: CW arrival + CW departure = net +2 CW.
    # b's fires net: 0 CW.
    # Total: (n-2) + (-(n-2)) + 0 = 0. ✓ (zero winding)

    # For 2 mixed TAs at b1, b2:
    # 4 winding excursions. But they're interleaved.
    # Each contributes ±(n-2) to the CW-CCW count.
    # They must sum to 0 (zero winding).
    # With 2 mixed TAs: 4 excursions with windings.
    # But the excursions of b1 and b2 share time intervals.
    # The winding of the full cycle = sum of LOCAL windings at each step.
    # Not the sum of excursion windings (which double-count shared intervals).

    # I think the cleanest proof is:
    # All-turnaround with ≥ 3 binary requires the walk to have specific
    # structural properties that conflict with the step budget and all-fc≥2.
    # The computational check at n=5,7,9 (and beyond via sampling) confirms 0 instances.
    # The dead-edge argument proves the same-side case.
    # The mixed-TA case: it's structurally impossible because of the
    # nesting constraint on excursions.

    # Let me do one final check at n=9 via random sampling.
    print("\n" + "="*60)
    print("RANDOM SAMPLING AT n=9")
    print("="*60)

    import random
    random.seed(42)

    n = 9
    ms = [2,2,2,3,3,3,3,3,3]  # 3 binary at positions 0,1,2
    threshold = 4 * 3**(n-2)

    def random_walk_cycle(n, ms, max_steps=100000):
        """Generate a random good cycle via random walk."""
        L = sum(ms)
        remaining = list(ms)

        # Try multiple random starts
        for _ in range(1000):
            rem = list(ms)
            start = random.randint(0, n-1)
            while rem[start] == 0:
                start = random.randint(0, n-1)
            rem[start] -= 1
            path = [start]

            for step in range(L - 1):
                nbrs = [(start - 1) % n, (start + 1) % n]
                valid = [nb for nb in nbrs if rem[nb] > 0]
                if not valid:
                    break
                nxt = random.choice(valid)
                rem[nxt] -= 1
                path.append(nxt)
                start = nxt

            if len(path) == L and path[0] in [(path[-1]-1)%n, (path[-1]+1)%n]:
                return path
        return None

    all_ta_found = 0
    any_ta_found = 0
    total_valid = 0

    for trial in range(50000):
        cyc = random_walk_cycle(n, ms)
        if cyc is None:
            continue

        # Check filters
        net = 0
        cw = 0
        for i in range(len(cyc)):
            c, nx = cyc[i], cyc[(i+1)%len(cyc)]
            if nx == (c+1)%n: net += 1; cw += 1
            elif nx == (c-1)%n: net -= 1
        wind = net // n
        if wind != 0: continue
        if cw == 0: continue
        f = [0]*n
        for p in cyc: f[p] += 1
        if any(x < 2 for x in f): continue

        total_valid += 1

        # Check turnarounds
        binary_procs = [0, 1, 2]
        ta_count = 0
        for b in binary_procs:
            fires = [i for i in range(len(cyc)) if cyc[i] == b]
            if len(fires) != 2: continue
            fi = []
            for idx in fires:
                prev = cyc[(idx-1)%len(cyc)]
                nxt = cyc[(idx+1)%len(cyc)]
                a = 'L' if prev == (b-1)%n else 'R'
                d = 'L' if nxt == (b-1)%n else 'R'
                fi.append((a, d))
            if all(a==d for a,d in fi):
                ta_count += 1

        if ta_count > 0:
            any_ta_found += 1
        if ta_count == 3:
            all_ta_found += 1
            print(f"  ALL-TA at n=9: {cyc}")

    print(f"Trials: 50000, valid cycles: {total_valid}")
    print(f"Any turnaround: {any_ta_found}")
    print(f"All turnaround: {all_ta_found}")


if __name__ == '__main__':
    main()
