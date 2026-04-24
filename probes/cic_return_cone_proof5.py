#!/usr/bin/env python3
"""
CIC Exploration 11e: ALL fair words are pure sweeps?!

The previous test found ZERO non-sweep fair words for any Case 3c configuration.
This means ALL fair adjacent cyclic words with k>=3 non-adjacent binary are sweeps.

Possible theorem: On C_n with k >= 3 pairwise non-adjacent binary processors,
every fair adjacent cyclic mover word is a pure sweep.

If true, this is an incredibly clean result: Shadow theorem kills all sweeps,
so Case 3c is dead by Shadow alone. No need for return cones or binary-bounce.

Verify with larger max_L to rule out length-bound artifacts.
Also: prove this analytically.
"""

from collections import Counter


def is_pure_sweep(word, n):
    """All steps same direction."""
    L = len(word)
    fwd = all((word[(i+1) % L] - word[i]) % n == 1 for i in range(L))
    bwd = all((word[i] - word[(i+1) % L]) % n == 1 for i in range(L))
    return fwd or bwd


def verify_all_sweeps(n, gap_sizes, max_L):
    """Check if ALL fair adjacent cyclic words are pure sweeps."""
    k = len(gap_sizes)
    binary_positions = []
    pos = 0
    for i in range(k):
        binary_positions.append(pos)
        pos += 1 + gap_sizes[i]
    assert pos == n

    binary_set = set(binary_positions)

    total = 0
    sweeps = 0
    nonsweep = []

    def dfs(word, move_counts):
        nonlocal total, sweeps
        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in move_counts):
                    if all(move_counts[b] % 2 == 0 for b in binary_positions):
                        total += 1
                        if is_pure_sweep(word, n):
                            sweeps += 1
                        else:
                            nonsweep.append(list(word))
                            if len(nonsweep) <= 2:
                                print(f"  NON-SWEEP: {word}")

        for next_p in [(current - 1) % n, (current + 1) % n]:
            move_counts[next_p] += 1
            word.append(next_p)
            dfs(word, move_counts)
            word.pop()
            move_counts[next_p] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    pct = 100 * sweeps / total if total > 0 else 0
    print(f"n={n} gaps={gap_sizes}: {total} fair words, {sweeps} sweeps ({pct:.0f}%), {len(nonsweep)} non-sweep")
    return len(nonsweep)


def verify_without_binary_constraint(n, max_L):
    """For comparison: check without binary constraint (no binary parity)."""
    total = 0
    sweeps = 0

    def dfs(word, move_counts):
        nonlocal total, sweeps
        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in move_counts):
                    total += 1
                    if is_pure_sweep(word, n):
                        sweeps += 1

        for next_p in [(current - 1) % n, (current + 1) % n]:
            move_counts[next_p] += 1
            word.append(next_p)
            dfs(word, move_counts)
            word.pop()
            move_counts[next_p] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    pct = 100 * sweeps / total if total > 0 else 0
    print(f"n={n} NO BINARY: {total} fair words, {sweeps} sweeps ({pct:.1f}%)")
    return total - sweeps


def analyze_why():
    """
    WHY are all fair Case 3c words pure sweeps?

    Key insight: binary proc has exactly 2 neighbors, both non-binary (non-adjacent).
    Binary proc b fires even times. The walk visits b, does stuff, visits b again.
    Each visit enters from one side and exits to one side.

    For a FAIR walk: every proc moves >= 2 times.
    Binary proc b: moves >= 2, even. Minimum 2.

    Consider the walk restricted to a gap arc: b_i -- t_1 -- ... -- t_g -- b_{i+1}
    The walk enters this arc from b_i or b_{i+1} and exits similarly.

    CLAIM: With k >= 3 non-adjacent binary on C_n, a fair adjacent cyclic walk
    must be a pure sweep.

    Proof sketch:
    - The walk visits every processor (fairness).
    - On C_n, the walk is adjacent (steps ±1 on the ring).
    - Consider the "direction" of each step: clockwise (+1) or counter-clockwise (-1).
    - For the walk to NOT be a pure sweep, it must change direction at some point.
    - A direction change means: w_t, w_{t+1}, w_{t+2} with w_{t+2} = w_t.
      I.e., the walk goes from a to a+1 to a (bouncing).
      At the bounce point w_{t+1}, the walk reverses direction.

    - BINARY CONSTRAINT: At a binary proc b, moves(b) is even.
      If the walk bounces at b, then b moves twice at that point (once going in,
      once going out). But the bounce is: arrive at b (b fires), leave same direction,
      arrive at b again immediately? No, a bounce at b means:
      w_t = b-1, w_{t+1} = b, w_{t+2} = b-1. Or w_t = b+1, w_{t+1} = b, w_{t+2} = b+1.
      So b fires once at the bounce. The bounce itself is fine for binary.

    - The issue is: with k >= 3 non-adjacent binary, the ring is divided into k arcs.
      A bounce walk must enter each arc and explore it.
      After exploring an arc, to reach the next arc, the walk must cross a binary proc.
      But binary procs are endpoints of arcs.

    - For fairness: every proc in every arc must be visited >= 2 times.
      For binary parity: each binary proc is visited an even number of times.

    - Think about what non-sweep means for the walk:
      The walk must reverse direction. Each reversal creates a "bounce" at some processor.
      The processors at which bounces occur play a special role.

    - KEY: In a non-sweep walk, the walk enters an arc, traverses it (visiting internal procs),
      bounces, and comes back. To visit internal procs >= 2 times, the walk must
      traverse the arc at least twice. This means crossing the endpoint binary procs
      at least 4 times (enter/exit twice each side).

    - Wait, this alone doesn't prevent non-sweep walks from existing. The original
      bounce cycle (CLB construction) is a non-sweep walk that works fine for 2 binary.
      But it requires a specific product budget.

    Actually, let me just check: does the all-sweep property hold even WITHOUT the
    binary parity constraint? Maybe it's a property of the ring+gap structure alone.
    """
    print("\n" + "=" * 70)
    print("Analysis: Are ALL fair words sweeps even without binary parity?")
    print("=" * 70)

    # Without binary constraint: pure adjacency + fairness on C_n
    for n in range(4, 9):
        verify_without_binary_constraint(n, max_L=min(3*n+4, 28))

    print("\n" + "=" * 70)
    print("Analysis: Verify with larger max_L")
    print("=" * 70)

    # With binary constraint, larger L
    verify_all_sweeps(6, [1, 1, 1], max_L=30)
    verify_all_sweeps(7, [1, 1, 2], max_L=28)
    verify_all_sweeps(7, [1, 2, 1], max_L=28)

    print("\n" + "=" * 70)
    print("Analysis: Even number of binary check")
    print("=" * 70)

    # With only 2 binary (not Case 3c), do non-sweeps exist?
    # ms = (2,T,T,...,T,2): 2 binary at positions 0 and some other
    # CLB bounce cycle exists here, so non-sweeps should be possible.

    # 2 binary, non-adjacent
    n = 5
    binary_pos_2 = [0, 2]
    binary_set_2 = set(binary_pos_2)

    total2 = 0
    sweeps2 = 0
    nonsweep2 = 0

    def dfs2(word, mc):
        nonlocal total2, sweeps2, nonsweep2
        L = len(word)
        if L > 20:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0 for b in binary_pos_2):
                        total2 += 1
                        if is_pure_sweep(word, n):
                            sweeps2 += 1
                        else:
                            nonsweep2 += 1

        for np_ in [(current - 1) % n, (current + 1) % n]:
            mc[np_] += 1
            word.append(np_)
            dfs2(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs2([0], mc)

    print(f"n={n}, k=2, binary={binary_pos_2}: {total2} fair, {sweeps2} sweeps, {nonsweep2} non-sweep")

    # 2 binary, adjacent
    n = 6
    binary_pos_2a = [0, 1]
    total2a = 0
    sweeps2a = 0
    nonsweep2a = 0

    def dfs2a(word, mc):
        nonlocal total2a, sweeps2a, nonsweep2a
        L = len(word)
        if L > 20:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0 for b in binary_pos_2a):
                        total2a += 1
                        if is_pure_sweep(word, n):
                            sweeps2a += 1
                        else:
                            nonsweep2a += 1

        for np_ in [(current - 1) % n, (current + 1) % n]:
            mc[np_] += 1
            word.append(np_)
            dfs2a(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs2a([0], mc)

    print(f"n={n}, k=2 (adjacent), binary={binary_pos_2a}: {total2a} fair, {sweeps2a} sweeps, {nonsweep2a} non-sweep")

    # 1 binary
    n = 5
    binary_pos_1 = [0]
    total1 = 0
    sweeps1 = 0
    nonsweep1 = 0

    def dfs1(word, mc):
        nonlocal total1, sweeps1, nonsweep1
        L = len(word)
        if L > 20:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0 for b in binary_pos_1):
                        total1 += 1
                        if is_pure_sweep(word, n):
                            sweeps1 += 1
                        else:
                            nonsweep1 += 1

        for np_ in [(current - 1) % n, (current + 1) % n]:
            mc[np_] += 1
            word.append(np_)
            dfs1(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs1([0], mc)

    print(f"n={n}, k=1, binary={binary_pos_1}: {total1} fair, {sweeps1} sweeps, {nonsweep1} non-sweep")


def sweep_only_proof():
    """
    Attempt to prove: with k >= 3 non-adjacent binary on C_n,
    every fair adjacent cyclic word is a pure sweep.

    Proof attempt:

    Consider a fair adjacent cyclic word w on C_n. Let B = {b_1, ..., b_k}
    be the binary processors (k >= 3, pairwise non-adjacent).

    Step 1: The word has a well-defined winding number W.
    All edge counts have parity W mod 2.

    Step 2: For binary b_i, moves(b_i) is even >= 2.
    edge_L(b_i) + edge_R(b_i) = 2 * moves(b_i).
    Both edges have parity W mod 2.

    Step 3: Consider consecutive binary procs b_i, b_{i+1} with gap g_i >= 1.
    The gap arc has g_i non-binary procs and g_i + 1 edges.
    Let the gap edges be e_0 (adjacent to b_i), e_1, ..., e_{g_i} (adjacent to b_{i+1}).
    All have the same parity (W mod 2).

    Step 4: Each interior proc t_j (j = 1, ..., g_i) in the gap has:
    e_{j-1} + e_j = 2 * moves(t_j) >= 4.

    Step 5: The binary endpoint b_i has edges in two arcs.
    In the current arc: edge e_0.
    In the adjacent arc: some edge e'.
    e_0 + e' = 2 * moves(b_i).

    Step 6: If W = 0 (zero winding), all edges are even.
    The walk bounces back and forth. To visit all procs, it must reach into every gap.

    Actually, I think the key insight is about BOUNCING and binary parity.

    LEMMA: In a fair adjacent cyclic walk on C_n with k >= 3 non-adjacent binary,
    the walk never reverses direction at a non-binary processor.

    Proof: Suppose the walk reverses at t_j (a non-binary proc in some gap).
    Then w_{s-1} = t_j - 1, w_s = t_j, w_{s+1} = t_j - 1 (or symmetric).
    This means at time s, the walk is at t_j and goes back.

    Wait, this doesn't directly lead to a contradiction. Many walks reverse at
    non-binary procs (the CLB bounce cycle does this).

    Let me think differently. The key property might be:

    CLAIM: With k >= 3 non-adjacent binary, every fair walk has |W| >= 2.
    And every walk with |W| >= 2 and binary parity is a pure sweep.

    Wait, that's not right either. |W| >= 2 doesn't force pure sweep.

    Let me think about it more carefully by examining the walk structure.

    For a pure sweep of winding W: L = |W| * n. All edges = |W|.
    moves(p) = |W| for all p. Binary parity: |W| even.
    So sweeps have W = ±2, ±4, ±6, ...

    For a NON-sweep walk: the walk changes direction at some point.
    At the reversal point p: the walk goes ... p-1, p, p-1 ... (or symmetric).
    This creates a "bump" at p.

    Now, consider the effect on edge counts:
    Reversal at p going left: adds 1 to edge(p-1,p) (arrival) and 1 to edge(p-1,p) (departure).
    So edge(p-1,p) increases by 2 compared to a sweep.
    But edge(p,p+1) doesn't get traversed during this bump.

    The total effect: some edges get extra traversals, some get fewer.
    For the walk to be fair and have binary parity:
    - fairness: all procs >= 2 moves
    - binary parity: binary procs even moves

    The constraint is that every reversal changes the edge count profile
    in a way that must still satisfy all parity constraints.

    A single reversal at p:
    - adds 2 to the edge on one side (the side it bounces from)
    - the walk must eventually compensate on the other side
    - this compensation requires additional reversals
    """
    print("\n" + "=" * 70)
    print("PROOF ANALYSIS")
    print("=" * 70)

    # Check: do non-sweep words exist with FEWER binary processors?
    # Previous check showed:
    # k=1, n=5: many non-sweeps
    # k=2, n=5: check

    # The critical question: WHY does k >= 3 force pure sweep?

    # Let's examine what non-sweep words look like for k=2:
    n = 6
    binary_positions = [0, 3]  # 2 non-adjacent binary
    binary_set = set(binary_positions)

    print(f"\nk=2 non-sweep examples (n={n}, binary={binary_positions}):")

    total = 0
    sweeps = 0
    ns_examples = []

    def dfs(word, mc):
        nonlocal total, sweeps
        L = len(word)
        if L > 20:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0 for b in binary_positions):
                        total += 1
                        if is_pure_sweep(word, n):
                            sweeps += 1
                        else:
                            if len(ns_examples) < 5:
                                ns_examples.append(list(word))

        for np_ in [(current - 1) % n, (current + 1) % n]:
            mc[np_] += 1
            word.append(np_)
            dfs(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    print(f"  Total: {total}, Sweeps: {sweeps}, Non-sweep: {total - sweeps}")
    for w in ns_examples:
        mc_w = Counter(w)
        W = sum(1 if (w[(i+1)%len(w)]-w[i])%n == 1 else -1 for i in range(len(w)))
        print(f"  {w} W={W} moves={dict(sorted(mc_w.items()))}")

    # Now understand: with k=2, the ring has 2 gaps, both >= 1.
    # A bounce walk can go: sweep one direction, then bounce at the far end,
    # and sweep back. This visits all procs and has the right parities.

    # With k=3: 3 gaps. A bounce walk would need to enter all 3 gaps.
    # But each entrance/exit crosses a binary proc. Binary procs need even moves.
    # The question is whether the traversal pattern forces pure sweep.

    # HYPOTHESIS: With k >= 3 non-adjacent binary, any fair walk has W = 0 mod n
    # (i.e., is a pure sweep with winding number |W| >= 2 or exactly 0).
    # But W=0 is possible for non-sweeps (bounces).

    # Actually the data shows: NO non-sweeps at all. So the constraint is even stronger.
    # It's not just W that's constrained; the walk MUST be a pure sweep.

    # Let me try to prove it by examining gap structure.
    # With k >= 3, gaps g_1, ..., g_k (each >= 1), sum = n-k.

    # Consider a gap of size 1: b_i -- t -- b_{i+1}.
    # t has both neighbors binary. For t to have moves >= 2:
    # the walk must visit t >= 2 times. Each visit enters from b_i or b_{i+1}
    # and exits to b_i or b_{i+1}. So each visit of t crosses 2 edges
    # (entry and exit), both of which touch t.
    # edge(b_i, t) + edge(t, b_{i+1}) = 2 * moves(t) >= 4.
    # Both have parity W mod 2.

    # For binary b_i: edge from the OTHER arc + edge(b_i, t) = 2 * moves(b_i).
    # For binary b_{i+1}: edge(t, b_{i+1}) + edge from other arc = 2 * moves(b_{i+1}).

    # In a pure sweep with |W| = 2: every edge = 2. moves(p) = 2 for all p. ✓

    # In a non-sweep walk: some edges > 2, some < 2 (or = 0).
    # All edges have same parity. If parity = 0 (W even): edges in {0, 2, 4, ...}.
    # For fairness: moves(p) >= 2 means edge_L + edge_R >= 4.
    # An edge = 0 means the walk never crosses it. But then the proc on
    # the "far" side of that edge is unreachable! Unless the walk reaches
    # it from the other side (going around the ring).

    # With k >= 3 gaps, each gap has edges. If ANY edge has count 0,
    # the ring is disconnected (for the walk). The procs on one side of
    # the zero edge must be reached from the other direction.
    # But with k >= 3 binary procs, the ring has k arcs. A zero edge in one arc
    # forces all procs in that arc (on the far side) to be reached from other arcs.
    # This is possible but requires the walk to go all the way around the ring.

    # For W even with a zero edge: the walk goes around the ring, using k-1 arcs
    # to reach all procs. But each binary proc gets extra traversals.
    # The total L increases significantly.

    # WAIT. Maybe the simpler argument is about WINDING NUMBER:
    # With k >= 3 non-adjacent binary, W must be even (binary parity forces all edges even).
    # Wait no: if W is odd, edges are odd. That's fine too.

    # Let me check: is it true that all fair words (with binary parity) on C_n
    # with k >= 3 non-adjacent binary have even winding number?

    # From the data: all fair words are sweeps with W = ±2m (even).
    # For pure sweeps: W = ±2, ±4, ±6, ...
    # So yes, W is even for all observed words.

    # Can W be odd? Edge counts all odd. Binary b: edge_L + edge_R even (2*moves, moves even).
    # Both odd, sum even. ✓. Possible.
    # But can we get a fair walk with W odd?
    # L = sum of edges = sum of n odd numbers = n (mod 2).
    # For n even: L even. For n odd: L odd.
    # L = sum of moves. Binary moves all even. Non-binary moves: no constraint.
    # n=6, k=3, gaps=(1,1,1): n even. L even. All procs even-moves (binary are even).
    # Non-binary: moves = (e_L + e_R)/2. Both edges odd. Sum = even. moves = even!
    # So ALL procs have even moves. L = sum of even = even. ✓
    # But this doesn't prevent W odd. It prevents... hmm.

    # Actually, for ANY proc p on C_n with k >= 3 non-adjacent binary:
    # p is either binary (moves even) or has at least one binary neighbor.
    # If p is non-binary but adjacent to binary b: p's edges both have parity W.
    # moves(p) = (e_L + e_R) / 2. If W even: both even, moves = integer. If W odd: both odd,
    # moves = (odd+odd)/2 = even/2 = integer. But we need moves(p) >= 2.
    # With W odd: moves(p) = even/2... wait, odd + odd = even, so yes integer.
    # moves(p) could be any integer >= 2. No additional parity constraint on non-binary.

    # OK so I haven't found a clean argument yet for why all fair words are sweeps.
    # Let me try a different approach.

    print("\n" + "=" * 70)
    print("TESTING: k=3 but with gaps > 1 between some binary")
    print("=" * 70)

    # k=2, various n
    for n_val in [5, 6, 7]:
        verify_all_sweeps_general(n_val, 2, max_L=20)

    # k=3, various n
    for n_val in [6, 7, 8]:
        verify_all_sweeps_general(n_val, 3, max_L=20)


def verify_all_sweeps_general(n, k, max_L):
    """Check for ANY arrangement of k non-adjacent binary, all fair words are sweeps."""
    from itertools import combinations

    # Generate all valid placements of k non-adjacent binary on C_n
    valid_placements = []
    for combo in combinations(range(n), k):
        # Check pairwise non-adjacency
        ok = True
        for i in range(k):
            for j in range(i+1, k):
                diff = min(abs(combo[i]-combo[j]), n - abs(combo[i]-combo[j]))
                if diff <= 1:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            valid_placements.append(combo)

    if not valid_placements:
        print(f"n={n}, k={k}: No valid placements (impossible)")
        return

    # Just test the first placement (others are related by rotation)
    bp = list(valid_placements[0])
    bs = set(bp)

    total = 0
    sweeps = 0

    def dfs(word, mc):
        nonlocal total, sweeps
        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0 for b in bp):
                        total += 1
                        if is_pure_sweep(word, n):
                            sweeps += 1

        for np_ in [(current - 1) % n, (current + 1) % n]:
            mc[np_] += 1
            word.append(np_)
            dfs(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    ns = total - sweeps
    print(f"n={n}, k={k}, binary={bp}: {total} fair, {sweeps} sweeps, {ns} non-sweep {'✓' if ns == 0 else '✗'}")


if __name__ == "__main__":
    analyze_why()
    sweep_only_proof()
