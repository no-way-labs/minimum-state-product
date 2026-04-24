"""
Turnaround Binary Provider Proof - Part 3
==========================================
Key finding: ALL-turnaround is impossible at n=5,7.
Let's prove this structurally and check at n=9.

Also: let's understand the parity/winding constraint that prevents
all-turnaround.

Observation from data:
- Non-consecutive binary (0,1,3) and (0,2,4) DO have 2 turnaround + 1 passthrough
- Consecutive binary (0,1,2) has at most 1 turnaround + 2 passthrough
- But NEVER all 3 turnaround

Why? Consider the walk as a path on the ring.
A turnaround at b means: walk arrives from side X, fires b, goes back to X.
The walk "bounces" at b.

If ALL binary are turnaround, each binary is a "bounce point".
The walk bounces at every binary proc.

With 3 binary procs on a ring of n procs, the ring is divided into
arcs between consecutive binary procs. If all binary bounce, the walk
is confined to arcs — it can't cross any binary proc.

But wait — "turnaround" means BOTH fires bounce. Between fire 1 and fire 2,
the walk goes to one side and comes back. Between fire 2 and fire 1 (wrapping),
the walk ALSO goes to one side and comes back.

If both excursions go to the SAME side, the walk never crosses b at all.
If excursions go to DIFFERENT sides (mixed turnaround), the walk still bounces
each time but alternates sides.

Key question: can the walk reach all procs if all binary are bouncing?
"""

from itertools import combinations

def neighbors(p, n):
    return [(p - 1) % n, (p + 1) % n]

def enumerate_good_cycles(n, ms):
    total_fires = sum(ms)
    remaining = list(ms)
    results = []

    def dfs(path, remaining):
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
        if remaining[start] > 0:
            remaining[start] -= 1
            dfs([start], remaining)
            remaining[start] += 1

    unique = set()
    for cyc in results:
        rotations = [cyc[i:] + cyc[:i] for i in range(len(cyc))]
        canon = min(rotations)
        unique.add(canon)
    return [list(c) for c in unique]

def get_winding_number(mover_word, n):
    net = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n:
            net += 1
        elif nxt == (curr - 1) % n:
            net -= 1
    return net // n

def count_cw_steps(mover_word, n):
    cw = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n:
            cw += 1
    return cw

def get_firing_counts(mover_word, n):
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    return fc

def classify_binary_firing(mover_word, b, n):
    L = len(mover_word)
    fires = [i for i in range(L) if mover_word[i] == b]
    assert len(fires) == 2

    fire_info = []
    for idx in fires:
        prev_mover = mover_word[(idx - 1) % L]
        next_mover = mover_word[(idx + 1) % L]
        left, right = (b - 1) % n, (b + 1) % n
        arr = 'L' if prev_mover == left else ('R' if prev_mover == right else '?')
        dep = 'L' if next_mover == left else ('R' if next_mover == right else '?')
        fire_info.append((arr, dep))

    is_turnaround = all(arr == dep for arr, dep in fire_info)
    return {'fires': fires, 'fire_info': fire_info, 'turnaround': is_turnaround}


def signed_step(mover_word, i, n):
    """Return +1 for CW step, -1 for CCW step at position i."""
    L = len(mover_word)
    curr = mover_word[i]
    nxt = mover_word[(i + 1) % L]
    if nxt == (curr + 1) % n:
        return +1
    elif nxt == (curr - 1) % n:
        return -1
    return 0


def analyze_crossing(mover_word, b, n):
    """
    Analyze how many times the walk crosses proc b going CW vs CCW.
    A crossing CW at b: step from b to (b+1).
    A crossing CCW at b: step from b to (b-1).
    Also: step from (b+1) to b (arriving from right) or (b-1) to b (arriving from left).

    Net crossing = (CW crossings) - (CCW crossings).
    For zero-winding cycle, sum of net crossings at all cuts = 0.
    But each proc individually can have nonzero net crossing.
    """
    L = len(mover_word)
    left = (b - 1) % n
    right = (b + 1) % n

    # Count directed edges through the "cut" between b and right
    # CW: b -> right
    # CCW: right -> b
    cw_cross = 0
    ccw_cross = 0
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if curr == b and nxt == right:
            cw_cross += 1
        if curr == right and nxt == b:
            ccw_cross += 1

    return cw_cross, ccw_cross, cw_cross - ccw_cross


def main():
    print("=" * 70)
    print("WHY ALL-TURNAROUND IS IMPOSSIBLE")
    print("=" * 70)

    # Key insight: count directed crossings at each binary proc
    # A turnaround binary b has both fires going to same side.
    # So all edges involving b go to one side.
    # Net crossing through the cut at b's other side = 0 from b's perspective.
    # But other procs' edges might cross that cut.

    # More precisely: for a cycle, the walk makes steps.
    # Each step crosses one "edge" of the ring.
    # For zero winding: #CW_steps - #CCW_steps = 0 globally.
    # For each edge (p, p+1): net_flow = #(p->p+1) - #(p+1->p) is the same for all edges.
    # In a zero-winding cycle, net_flow = 0 for every edge.

    # Now, turnaround at b means:
    # Fire 1: prev=X, next=X (both on same side)
    # Fire 2: prev=Y, next=Y (both on same side)
    # If X=Y=L: the edges involving b are: ?->b (from left), b->? (to left)
    #   So edges b-1 -> b and b -> b-1 are used.
    #   Edges b -> b+1 and b+1 -> b are NOT used (from b's fires).
    # If X=Y=R: edges b -> b+1 and b+1 -> b are used, b-1 and b not used from b.
    # If X=L, Y=R (mixed turnaround): some edges on each side.

    # For the edge between b and right(b):
    # If both excursions go LEFT: b contributes 0 crossings of this edge.
    # The net flow through this edge must still be 0.
    # So other procs must balance any crossings.

    # But here's the constraint: the WALK is a connected path on the ring.
    # If b never crosses to right(b), then the walk, starting from some position,
    # can only reach procs on one side of b through b.
    # To reach the other side, it must go all the way around.
    # With MULTIPLE turnaround binary procs, the walk gets boxed in.

    print("\nChecking net flow through each edge for turnaround cycles:")
    n = 5
    for bp in [(0,1,2), (0,1,3), (0,2,4)]:
        ms = [3] * n
        for b in bp:
            ms[b] = 2

        cycles = enumerate_good_cycles(n, ms)
        filtered = []
        for cyc in cycles:
            winding = get_winding_number(cyc, n)
            if winding != 0: continue
            cw = count_cw_steps(cyc, n)
            if cw == 0: continue
            fc = get_firing_counts(cyc, n)
            if any(f < 2 for f in fc): continue
            filtered.append(cyc)

        print(f"\nbp={bp}, ms={ms}, filtered: {len(filtered)}")

        for cyc in filtered:
            fc = get_firing_counts(cyc, n)
            ta_info = {}
            for b in bp:
                info = classify_binary_firing(cyc, b, n)
                ta_info[b] = info

            ta_count = sum(1 for b in bp if ta_info[b]['turnaround'])
            if ta_count < 2:
                continue

            print(f"  Cycle {cyc}, fc={fc}, ta_count={ta_count}")
            for b in bp:
                marker = "TA" if ta_info[b]['turnaround'] else "PT"
                print(f"    Binary {b} [{marker}]: {ta_info[b]['fire_info']}")

            # Show net flow through every edge
            L = len(cyc)
            for e in range(n):
                cw_cross, ccw_cross, net = analyze_crossing(cyc, e, n)
                print(f"    Edge {e}->{(e+1)%n}: CW={cw_cross}, CCW={ccw_cross}, net={net}")

    # ============================================================
    # PARITY ARGUMENT
    # ============================================================
    print("\n\n" + "=" * 70)
    print("PARITY / CROSSING ARGUMENT")
    print("=" * 70)

    # For a binary proc b with turnaround to side S:
    # b contributes 2 crossings of edge (b, S_neighbor) and 0 crossings of other edge.
    # Specifically:
    # If turnaround to LEFT: both fires have prev=L, next=L
    #   So edges (b-1)->b and b->(b-1) each get +1 crossing.
    #   Net flow through edge (b-1,b) is 0 from b's fires (1 each direction).
    #   Edge (b, b+1): 0 crossings from b.

    # Wait, let me re-examine. "Turnaround to LEFT" means:
    # Fire: arrives from LEFT (prev = b-1), departs to LEFT (next = b-1)
    # So the step BEFORE fire is b-1 -> b (arriving)
    # The step AFTER fire is b -> b-1 (departing)
    # Both fires: 2x (b-1 -> b) and 2x (b -> b-1)
    # Net flow through edge (b-1, b): 2 - 2 = 0. OK.
    # But: b-1 appears 4 times in edges involving b!
    # Meanwhile, edge (b, b+1): 0 crossings from b's fires.

    # For zero-winding, edge (b, b+1) has net flow 0.
    # But ALL crossings of this edge come from OTHER procs' fires.
    # Those procs can be on either side.

    # The key constraint: each fire of b-1 contributes exactly 2 edges.
    # If b-1 fires f times, it contributes 2f edges total.
    # Some go to b, some go to b-2.

    # Let me count more carefully what turnaround means for the walk path.
    print("\nDetailed walk path around turnaround binary procs:")

    n = 5
    bp = (0, 2, 4)
    ms = [2, 3, 2, 3, 2]
    cycles = enumerate_good_cycles(n, ms)
    filtered = []
    for cyc in cycles:
        winding = get_winding_number(cyc, n)
        if winding != 0: continue
        cw = count_cw_steps(cyc, n)
        if cw == 0: continue
        fc = get_firing_counts(cyc, n)
        if any(f < 2 for f in fc): continue
        filtered.append(cyc)

    for cyc in filtered:
        fc = get_firing_counts(cyc, n)
        print(f"\nCycle {cyc}, fc={fc}")
        L = len(cyc)
        for b in bp:
            info = classify_binary_firing(cyc, b, n)
            marker = "TA" if info['turnaround'] else "PT"
            # For turnaround, show which sides
            if info['turnaround']:
                sides = [fi[0] for fi in info['fire_info']]
                print(f"  Binary {b} [{marker}]: sides={sides}")
            else:
                print(f"  Binary {b} [{marker}]: {info['fire_info']}")

        # Show the walk as a sequence of positions
        print(f"  Walk: ", end="")
        for i in range(L):
            step = signed_step(cyc, i, n)
            arrow = "→" if step == 1 else "←"
            print(f"{cyc[i]}{arrow}", end="")
        print(f"{cyc[0]}")


    # ============================================================
    # THE KEY QUESTION: Can we prove all-turnaround is impossible?
    # ============================================================
    print("\n\n" + "=" * 70)
    print("ALL-TURNAROUND IMPOSSIBILITY CHECK")
    print("=" * 70)

    # Let's check EVERY possible n from 5 to 9
    # For n>=8, enumeration is too slow. Let's try n=5,7 (odd) and argue.

    # Actually, let me think about this differently.
    # For a turnaround binary b:
    # - Both fires bounce to the same side: "same-side turnaround"
    # - Both fires bounce but to different sides: "mixed turnaround"
    #   (fire 1: arrive L depart L, fire 2: arrive R depart R)

    # For same-side turnaround (say both LEFT):
    # The walk path at b looks like: ...->b-1->b->b-1->...->b-1->b->b-1->...
    # b is visited exactly twice, both times from the left.
    # right(b) is NEVER adjacent to b in the walk.

    # For mixed turnaround:
    # Fire 1: ->b-1->b->b-1-> (bounce left)
    # Fire 2: ->b+1->b->b+1-> (bounce right)
    # Now both sides are visited!

    # So the real question is: same-side turnaround vs mixed turnaround.

    # Let's check what types we see:
    print("\nTurnaround subtypes at n=5:")
    n = 5
    for bp in [(0,1,2), (0,1,3), (0,2,4)]:
        ms = [3] * n
        for b in bp: ms[b] = 2

        cycles = enumerate_good_cycles(n, ms)
        filtered = []
        for cyc in cycles:
            winding = get_winding_number(cyc, n)
            if winding != 0: continue
            cw = count_cw_steps(cyc, n)
            if cw == 0: continue
            fc = get_firing_counts(cyc, n)
            if any(f < 2 for f in fc): continue
            filtered.append(cyc)

        same_side_count = 0
        mixed_count = 0

        for cyc in filtered:
            for b in bp:
                info = classify_binary_firing(cyc, b, n)
                if info['turnaround']:
                    sides = [fi[0] for fi in info['fire_info']]
                    if sides[0] == sides[1]:
                        same_side_count += 1
                    else:
                        mixed_count += 1

        print(f"  bp={bp}: same_side_ta={same_side_count}, mixed_ta={mixed_count}")


    # ============================================================
    # For n=7: check more carefully
    # ============================================================
    print("\nTurnaround subtypes at n=7:")
    n = 7
    for bp in [(0,1,2), (0,2,4), (0,1,4), (0,3,5)]:
        ms = [3] * n
        for b in bp: ms[b] = 2

        cycles = enumerate_good_cycles(n, ms)
        filtered = []
        for cyc in cycles:
            winding = get_winding_number(cyc, n)
            if winding != 0: continue
            cw = count_cw_steps(cyc, n)
            if cw == 0: continue
            fc = get_firing_counts(cyc, n)
            if any(f < 2 for f in fc): continue
            filtered.append(cyc)

        same_side_count = 0
        mixed_count = 0
        all_ta_same = 0
        all_ta_mixed = 0

        for cyc in filtered:
            ta_types = []
            for b in bp:
                info = classify_binary_firing(cyc, b, n)
                if info['turnaround']:
                    sides = [fi[0] for fi in info['fire_info']]
                    ta_types.append('same' if sides[0] == sides[1] else 'mixed')
                    if sides[0] == sides[1]:
                        same_side_count += 1
                    else:
                        mixed_count += 1
                else:
                    ta_types.append('pt')

            if all(t != 'pt' for t in ta_types):
                if all(t == 'same' for t in ta_types):
                    all_ta_same += 1
                else:
                    all_ta_mixed += 1

        print(f"  bp={bp}: same_side={same_side_count}, mixed={mixed_count}, all_ta_same={all_ta_same}, all_ta_mixed={all_ta_mixed}")


if __name__ == '__main__':
    main()
