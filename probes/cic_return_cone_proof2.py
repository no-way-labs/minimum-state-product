#!/usr/bin/env python3
"""
CIC Exploration 11b: Debug survivors and refine the argument.

The survivors from the walk-level check need analysis:
1. Are they actual valid mover words (proper edge labeling)?
2. Do they have return cones we missed?
3. What other mechanism kills them?

Also: the winding-number parity claim needs checking.
"""

from collections import Counter

def analyze_word(word, n, binary_positions):
    """Detailed analysis of a mover word."""
    L = len(word)
    is_binary = set(binary_positions)

    # Edge counts
    edge_counts = {}
    for i in range(L):
        a, b = word[i], word[(i+1) % L]
        e = (min(a, b), max(a, b))
        if abs(a - b) > 1:  # ring edge (0, n-1)
            e = (0, n-1)
        edge_counts[e] = edge_counts.get(e, 0) + 1

    # Move counts
    move_counts = Counter(word)

    # Winding number
    # Sum of steps: +1 for clockwise, -1 for counter-clockwise
    winding = 0
    for i in range(L):
        diff = word[(i+1) % L] - word[i]
        if diff == 1 or diff == -(n-1):
            winding += 1
        elif diff == -1 or diff == n-1:
            winding -= 1
    W = winding // n if winding % n == 0 else winding / n

    # Singleton edges
    singletons = [(e, c) for e, c in edge_counts.items() if c == 1]

    print(f"\nWord: {word}")
    print(f"L={L}, n={n}")
    print(f"Move counts: {dict(sorted(move_counts.items()))}")
    print(f"Edge counts: {dict(sorted(edge_counts.items()))}")
    print(f"Winding raw: {winding}, W={W}")
    print(f"Singletons: {singletons}")

    # Check binary parity
    for b in binary_positions:
        mc = move_counts.get(b, 0)
        print(f"  Binary {b}: moves={mc}, even={'✓' if mc % 2 == 0 else '✗'}")

    # Check return cone
    # A return cone is an interval [t,u) where the movers form a contiguous segment S,
    # every proc in S is untouched before t, frozen after u.
    # In a cyclic word, "before t" and "after u" are relative to the cyclic ordering.
    has_cone = check_return_cone(word, n)
    print(f"Return cone: {'YES' if has_cone else 'NO'}")

    # Check binary-bounce (Tool 3) more carefully
    has_bb = check_binary_bounce_v2(word, n, binary_positions)
    print(f"Binary-bounce: {'YES' if has_bb else 'NO'}")

    return has_cone, has_bb


def check_return_cone(word, n):
    """
    Check if cyclic word has a nontrivial return cone.

    Return cone [t,u): movers in [t,u) form contiguous segment S,
    every proc in S is untouched before t (in cyclic sense) and frozen after u.

    In a cyclic word: "before t" means the portion of the word from u to t (going around).
    "after u" means the portion from u to t.
    Wait, for a cyclic word [t,u) is an interval on the circle.
    "Before t" = the complement interval [u, t).
    Untouched before t: proc not in word[u..t-1].
    Frozen after u: proc not in word[u..t-1].
    Same thing! So the condition is: every proc in S does NOT appear in [u, t).
    I.e., all appearances of procs in S are within [t, u).

    For this to be nontrivial: S has >= 1 proc, and [t,u) is a proper subinterval.
    """
    L = len(word)

    # For each contiguous segment S of processors:
    for start_proc in range(n):
        for seg_len in range(1, n):  # length of segment
            S = set((start_proc + i) % n for i in range(seg_len))
            if len(S) == n:
                continue  # trivial

            # Find all positions where movers are in S
            positions_in_S = [t for t in range(L) if word[t] in S]
            if not positions_in_S:
                continue

            # Check if these positions form a contiguous interval on the circle
            # Sort positions and check for a gap
            positions_in_S.sort()

            # Check all possible "start" points of the interval
            for gap_idx in range(len(positions_in_S)):
                # The interval starts after the gap
                # Gap is between positions_in_S[gap_idx-1] and positions_in_S[gap_idx]
                t = positions_in_S[gap_idx]
                u = (positions_in_S[gap_idx - 1] + 1) % L

                # Check that all positions in [t, u) (cyclically) are exactly positions_in_S
                interval_len = (u - t) % L
                if interval_len == 0:
                    interval_len = L
                interval_positions = set((t + i) % L for i in range(interval_len))

                if set(positions_in_S) == interval_positions:
                    # Valid return cone! Check movers form contiguous S
                    movers_in_interval = set(word[p] for p in interval_positions)
                    if movers_in_interval == S:
                        # Check S is contiguous on the ring
                        # (already guaranteed by construction)
                        if interval_len < L:  # nontrivial
                            return True

    return False


def check_binary_bounce_v2(word, n, binary_positions):
    """
    Improved binary-bounce check.

    Tool 3: times t < u such that:
    - p is not mover at t
    - p IS mover at u
    - p doesn't move in [t,u)
    - one neighbor q doesn't move in [t,u)
    - other neighbor b is binary, moves exactly twice in [t,u)

    Note: [t,u) is a LINEAR interval (not cyclic). But in a cyclic word,
    we should consider all cyclic intervals.
    """
    L = len(word)
    is_binary = set(binary_positions)

    # For each proc p adjacent to a binary proc b:
    for b in binary_positions:
        for p in [(b-1) % n, (b+1) % n]:
            if p in is_binary:
                continue

            q = (2*p - b) % n  # other neighbor of p

            # Find all positions where p appears (p is the mover)
            p_positions = [i for i in range(L) if word[i] == p]
            if len(p_positions) < 1:
                continue

            # For each position u where p moves:
            for u in p_positions:
                # Consider intervals [t, u) going backward from u
                # Start from u-1 and extend backward
                t = (u - 1) % L
                b_count = 0
                q_found = False
                p_found = False
                steps = 0

                while steps < L - 1:
                    mover = word[t]
                    if mover == p:
                        break  # hit another p move
                    if mover == q:
                        q_found = True
                        break
                    if mover == b:
                        b_count += 1
                    t = (t - 1) % L
                    steps += 1

                if not q_found and not p_found and b_count == 2:
                    return True

                # Also try with q as the non-moving neighbor on the OTHER side
                # (already covered by iterating over both neighbors of b)

    # Also check: for each non-binary proc p, check if there's a binary bounce
    # even if p is not adjacent to the binary proc in question.
    # Tool 3 says: p has a neighbor b (binary) and neighbor q.
    # We need q frozen, b bouncing twice, p frozen then moves.
    # Already covered above.

    return False


def check_return_cone_fast(word, n):
    """
    Faster return cone check using first/last appearance.

    For a contiguous segment S, all its appearances must be in a contiguous
    cyclic interval. Equivalently: the complement of S's appearance set
    must be contiguous on the circle of times.

    Optimization: instead of checking all segments, use the "first and last"
    appearance of each processor.
    """
    L = len(word)

    # For each processor, record positions where it appears
    proc_positions = {p: [] for p in range(n)}
    for t in range(L):
        proc_positions[word[t]].append(t)

    # For each contiguous segment S:
    for start in range(n):
        for length in range(1, n):
            S = [(start + i) % n for i in range(length)]
            if length >= n:
                continue

            # All positions of procs in S
            all_pos = []
            for p in S:
                all_pos.extend(proc_positions[p])

            if not all_pos:
                continue

            all_pos.sort()

            # Check if they form a contiguous cyclic interval
            # Find the largest gap between consecutive positions (cyclically)
            max_gap = 0
            max_gap_start = 0
            for i in range(len(all_pos)):
                next_pos = all_pos[(i + 1) % len(all_pos)]
                if i + 1 < len(all_pos):
                    gap = next_pos - all_pos[i] - 1
                else:
                    gap = (all_pos[0] + L) - all_pos[-1] - 1
                if gap > max_gap:
                    max_gap = gap
                    max_gap_start = i

            # If the rest of the positions (total - gap) equals len(all_pos) as a contiguous block
            if max_gap > 0 and len(all_pos) < L:
                # The complement occupies max_gap time steps
                # All positions of S are in a block of L - max_gap steps
                # This IS a return cone of length L - max_gap
                return True, S

    return False, None


def main():
    print("CIC Exploration 11b: Survivor Analysis")
    print("=" * 70)

    # n=6, k=3, gaps=(1,1,1): BTBTBT, binary at 0,2,4
    n = 6
    binary_positions = [0, 2, 4]

    survivors_6 = [
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1],  # double sweep
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5],  # sweep + bounce
        [0, 5, 4, 3, 2, 1, 0, 1, 0, 1],
        [0, 1, 0, 1, 0, 5, 0, 5, 0, 1, 0, 5],
        [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5],  # double sweep forward
    ]

    print(f"\n--- Analyzing n={n} survivors ---")
    for w in survivors_6:
        analyze_word(w, n, binary_positions)

    # The double sweep [0,5,4,3,2,1,0,5,4,3,2,1] has W = -2 (two full backwards traversals)
    # All edges have count 2 (even). No singletons. No return cone.
    # What kills this word?

    # Let's check: does this word actually represent a valid good cycle?
    # In the seeded model (start from all-zeros), each proc starts at 0.
    # The movers change state. For a seeded cycle to close, final config = initial.
    # The word 0,5,4,3,2,1,0,5,4,3,2,1 means each proc fires exactly twice.
    # Binary procs fire twice (even ✓). After two firings, binary returns to 0. ✓
    # Ternary procs fire twice. After two firings, ternary state could be 0,1,2.
    # For the cycle to close: proc p at state 0 must return to state 0 after 2 firings.
    # Each firing increments (or changes) the state. If the transition function
    # maps: 0 -> a -> 0, need a 2-cycle. For ternary: 0->1->0 or 0->2->0.
    # This is consistent, so the word CAN represent a good cycle.

    # But the Return Cone Lemma checks something different.
    # "every processor in S is untouched before t" — in the seeded model,
    # untouched means state = 0 (initial state).
    # "frozen after u" — doesn't fire again, so state stays fixed.
    # If state at u = state at t = 0, then C_t = C_u.

    # For the double sweep: each proc fires at two distinct times.
    # There's no contiguous segment where all procs' firings are confined to an interval.
    # (Each proc fires once in the first sweep and once in the second sweep.)

    # So the Return Cone Lemma genuinely doesn't apply.
    # And the binary-bounce doesn't apply.
    # But this word IS actually killed by a DIFFERENT mechanism?

    # WAIT. Let me reconsider. This is a mover WORD, not a mover SEQUENCE.
    # The cyclic word [0,5,4,3,2,1,0,5,4,3,2,1] of length 12.
    # This means: mover at time 0 is proc 0, time 1 is proc 5, ..., time 11 is proc 1.
    # Then time 12 = time 0 (cyclic): mover is proc 0 again.
    # The edge between time 11 (mover=1) and time 0 (mover=0): |1-0|=1. Adjacent. ✓

    # For this to be a valid good cycle in the seeded model:
    # Config C_0 = (0,0,0,0,0,0). Only proc 0 fires (because C_0 is a "good" config
    # where proc 0 is enabled but others aren't, meaning... wait.
    # In Dijkstra's model, a "good" config has exactly one enabled proc (token holder).
    # Proc p is enabled iff it differs from its predecessor (p-1 in the ring?
    # or its left neighbor? depends on convention).

    # Actually, the specific transition rules determine which proc is enabled.
    # The mover word just says WHICH proc fires at each step.
    # For it to be a valid good cycle: at each step, exactly the designated proc
    # must be enabled (have a token).

    # The point is: the WORD describes the sequence of movers. Whether an actual
    # transition system can realize this word is the question. The tools (Return Cone,
    # Binary-Bounce) are obstructions to realizability.

    # If a word survives both tools, it MIGHT still be unrealizable, but by a
    # different mechanism. Our goal is to show Tools 2+3 suffice for ALL words.
    # If they don't, we need an additional tool.

    print("\n" + "=" * 70)
    print("CRITICAL FINDING: Some words survive Tools 2 and 3.")
    print("The double-sweep (W=±2) is the simplest survivor.")
    print("Need to understand what ELSE kills these words.")
    print("=" * 70)

    # Let's check if the survivors have return cones by using the CORRECT definition.
    # The original Return Cone Lemma (GLB Expl 51) uses the SEEDED model:
    # processors in S have state 0 at time t (untouched) and state 0 at time u (frozen after u).
    # This only works when S's procs start at 0 AND return to 0.
    # For the double-sweep, each proc fires twice. If the firing sequence is
    # 0 -> a -> 0 (ternary), then state at time t (after 0 firings) = 0,
    # and state at time u (after 2 firings) = 0. So C_t = C_u IF all procs
    # in S fire 0 or 2 times in [t,u).

    # WAIT. The Return Cone definition says:
    # "every proc in S is untouched before t" = hasn't fired before t
    # "every proc in S is frozen after u" = doesn't fire after u
    # This means: ALL of S's firings occur in [t,u).
    # At time t: all procs in S at state 0 (haven't fired).
    # At time u: all procs in S at state 0 (fired some even number of times for binary,
    #   returned to 0 for ternary IF they fire a multiple of 3 times,
    #   OR the problem is that ternary procs don't necessarily return to 0 after k firings).

    # HOLD ON. Re-reading the Return Cone Lemma:
    # "processors in S have state 0 at time t because they have not moved yet"
    # "processors in S also have state 0 at time u because they never move again
    #  before the cycle closes to C_0 = 0^n"
    # So the state at u is determined by: proc hasn't moved since last firing,
    # AND the cycle eventually closes to C_0 = 0^n, AND proc doesn't move after u.
    # So state at u = state when the cycle closes = 0. ✓

    # KEY: This only works in the SEEDED model where C_0 = 0^n.
    # The state at u (after S's last firing) persists until the cycle closes.
    # If the cycle closes to C_0 = 0^n, then state at close = 0.
    # Since S doesn't fire after u, state at u = state at close = 0.

    # So for the double-sweep on C_6: no contiguous segment S has all firings
    # confined to a subinterval. Each proc fires twice, once in each sweep.
    # So no return cone.

    # WHAT KILLS THE DOUBLE-SWEEP?
    # The double-sweep has W = -2 (or +2). All edges have count 2.
    # In the seeded model, C_0 = (0,0,0,0,0,0).
    # After the first sweep (0,5,4,3,2,1): each proc fires once.
    # C_6 depends on transition rules.
    # After the second sweep (0,5,4,3,2,1): each proc fires again.
    # C_12 must = C_0 for a cycle.

    # For this to be a valid good cycle: each configuration C_0, ..., C_{11} must
    # have exactly one enabled processor (the designated mover).

    # The first survivor [0,5,4,3,2,1,0,5,4,3,2,1] is a W=2 sweep.
    # But are W=2 words even POSSIBLE as good cycles for sub-threshold products?
    # For a sweep cycle, the product must accommodate the cycle structure.
    # Sweep cycles are killed by the SHADOW cycle theorem (from our earlier work).

    # AH! Sweep cycles are already killed by the Shadow Cycle Mirror Theorem!
    # The shadow theorem applies to uniform sweep cycles.
    # The double-sweep IS a sweep cycle. So it's killed by SHADOW, not by Tools 2/3.

    # The tools (Return Cone + Binary-Bounce) are for NON-SWEEP cycles.
    # GLB's work on Case 3c is specifically about the non-sweep regime.

    # So the correct theorem statement is:
    # "Every fair adjacent mover word that is NOT a sweep is killed by Tool 2 or Tool 3."
    # OR: "Every Case 3c word is killed by Shadow (if sweep) or Tools 2/3 (if non-sweep)."

    # But wait: are ALL survivors sweeps? Let me check.

    print("\n" + "=" * 70)
    print("Checking if survivors are all sweep-type words...")
    print("=" * 70)

    def is_sweep_word(word, n):
        """Check if word is a uniform sweep (all steps in same direction, possibly wrapping)."""
        L = len(word)
        forward = 0
        backward = 0
        for i in range(L):
            diff = (word[(i+1)%L] - word[i]) % n
            if diff == 1:
                forward += 1
            elif diff == n-1:
                backward += 1
            else:
                return False, 0
        if forward == L:
            return True, forward // n  # winding number
        if backward == L:
            return True, -(backward // n)
        return False, 0

    def classify_word(word, n):
        """Classify word as sweep, bounce, or mixed."""
        L = len(word)
        # Check sweep
        is_s, w = is_sweep_word(word, n)
        if is_s:
            return f"sweep (W={w})"

        # Check winding number
        winding = 0
        for i in range(L):
            diff = (word[(i+1)%L] - word[i]) % n
            if diff == 1:
                winding += 1
            elif diff == n-1:
                winding -= 1
        W = winding

        return f"mixed (W_raw={W})"

    # Regenerate survivors for n=6
    print(f"\nSample survivors from n=6, gaps=(1,1,1):")
    survivors_sample = [
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 1, 0, 1],
        [0, 1, 0, 1, 0, 5, 0, 5, 0, 1, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 4, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 0, 5, 4, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 4, 5, 4, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 0, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 0, 1, 0, 1],
        [0, 5, 4, 3, 2, 1, 0, 1, 0, 1, 0, 5, 0, 5],
    ]

    for w in survivors_sample:
        cl = classify_word(w, 6)
        # Check edges
        edge_counts = Counter()
        for i in range(len(w)):
            a, b = w[i], w[(i+1) % len(w)]
            e = tuple(sorted([a, b]))
            if abs(a-b) > 1:
                e = (0, n-1)
            edge_counts[e] += 1
        singletons = sum(1 for c in edge_counts.values() if c == 1)
        # Check which procs are NOT visited
        visited = set(w)
        unvisited = set(range(6)) - visited
        print(f"  {w}: {cl}, L={len(w)}, S={singletons}, edges={dict(sorted(edge_counts.items()))}, unvisited={unvisited}")

    # LOOK AT THIS: [0, 5, 4, 3, 2, 1, 0, 5, 0, 5]
    # This visits procs {0,1,2,3,4,5} — all visited. L=10.
    # Procs 1,2,3,4 each appear once. NOT FAIR (fairness requires >= 2).
    # Wait, let me recheck my fairness constraint in the original code.

    print("\n" + "=" * 70)
    print("RECHECKING FAIRNESS...")
    print("=" * 70)
    for w in survivors_sample:
        mc = Counter(w)
        fair = all(mc.get(p, 0) >= 2 for p in range(6))
        binary_ok = all(mc.get(b, 0) % 2 == 0 for b in [0, 2, 4])
        print(f"  {w}: moves={dict(sorted(mc.items()))}, fair={fair}, binary_ok={binary_ok}")

    # [0, 5, 4, 3, 2, 1, 0, 5, 0, 5]: moves={0:3, 1:1, 2:1, 3:1, 4:1, 5:3}
    # Procs 1,2,3,4 each move only 1 time. NOT FAIR.
    # So this word should have been filtered out. Bug in my original code?

    # Let me check: in the DFS, "fair = all(c >= 2 for c in move_counts)"
    # move_counts is indexed by proc. So it should catch this.
    # But wait, maybe the word [0,5,0,5] was generated differently.
    # Let me recheck with the actual code.

    # Actually, the first script might have a bug. Let me check the survivor
    # [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1] which has each proc appearing exactly 2 times.
    w = [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1]
    mc = Counter(w)
    print(f"\nDouble sweep: moves={dict(sorted(mc.items()))}")
    print(f"  Fair: {all(mc.get(p,0) >= 2 for p in range(6))}")
    print(f"  Binary parity: {all(mc.get(b,0) % 2 == 0 for b in [0,2,4])}")

    # This IS fair. Each proc moves exactly 2 times. Binary parity OK.
    # So it's a legitimate survivor of Tools 2/3.
    # But it's a sweep word, which is killed by the Shadow theorem separately.

    # Let me re-run the original code with correct fairness check and see what
    # non-sweep survivors exist.

    print("\n" + "=" * 70)
    print("CHECKING: Are ALL Tool 2/3 survivors sweep-type words?")
    print("=" * 70)

    # Check the ACTUAL survivors from the DFS (from the first script's output)
    actual_survivors = [
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1],
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 4, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 0, 5, 4, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 4, 5, 4, 5],
    ]

    for w in actual_survivors:
        mc = Counter(w)
        fair = all(mc.get(p, 0) >= 2 for p in range(6))
        is_s, wn = is_sweep_word(w, 6)

        # Compute winding
        winding = 0
        for i in range(len(w)):
            diff = (w[(i+1)%len(w)] - w[i]) % 6
            if diff == 1:
                winding += 1
            elif diff == 5:
                winding -= 1

        print(f"  {w}")
        print(f"    L={len(w)}, moves={dict(sorted(mc.items()))}, fair={fair}")
        print(f"    sweep={is_s}, winding={winding}")
        if not fair:
            print(f"    *** NOT FAIR — should have been filtered ***")

    # I suspect many survivors are not fair. The DFS might have a bug.
    # Let me check the DFS code: the move_counts array is updated correctly?
    # In the DFS: visited[0] = 1, then each extension increments visited[next_pos].
    # The word is [0, next1, next2, ...]. So visited counts appearances of each proc.
    # Closure check: |current - word[0]| == 1. Then word + [word[0]] forms the cyclic word?
    # No, the word itself IS the cyclic sequence. The closure step is just checking
    # that the last element is adjacent to the first. The word itself contains
    # all the movers INCLUDING the first element.
    # Move counts: each position in the word is a mover.
    # But wait: in a cyclic mover word of length L, each of the L movers fires.
    # The word [0,5,4,3,2,1,0,5,0,5] has L=10. Procs 0,5,4,3,2,1,0,5,0,5.
    # Proc 0 appears at positions 0,6,8: 3 times.
    # Proc 5 appears at positions 1,7,9: 3 times.
    # Proc 4 at position 2: 1 time.
    # Procs 1,2,3 at positions 5,4,3: 1 each.
    # So procs 1,2,3,4 each move 1 time. NOT fair.
    # This should have been caught by "all(c >= 2 for c in move_counts)".
    # Unless move_counts is indexed differently.

    # In the DFS code: move_counts = [0]*n, move_counts[0] = 1.
    # But the fairness check is: all(c >= 2 for c in move_counts).
    # This checks if EVERY proc (including unvisited ones) has count >= 2.
    # Unvisited procs have count 0, so they FAIL the check.
    # So [0,5,0,5] (which doesn't visit 1,2,3,4) would fail fairness.
    # That means [0,5,4,3,2,1,0,5,0,5] visits all procs:
    # move_counts = [3,1,1,1,1,3]. Procs 1,2,3,4 have count 1 < 2. FAIL.
    # So this word should NOT be a survivor. Something is wrong.

    # WAIT. Maybe the code ISN'T outputting [0,5,4,3,2,1,0,5,0,5] as a survivor.
    # The output showed "SURVIVOR: [0, 5, 4, 3, 2, 1, 0, 5, 0, 5]" but these
    # were DURING the DFS (printed when first found), not necessarily from
    # the final survivors list. Let me look at the output more carefully.

    # The output says "SURVIVOR:" during DFS + "*** 1402 SURVIVORS FOUND ***"
    # followed by a list. The [0,5,4,3,2,1,0,5,0,5] appears at line 4 of
    # the "during DFS" output. So it IS a survivor.

    # But it's NOT fair (proc 1 moves only once). So there's a BUG in the fairness check.

    # AH I SEE THE BUG. In the DFS, the word starts at 0, and the move_counts
    # includes the starting proc. But the CLOSURE check tests adjacency between
    # the last element and the first. The word represents the CYCLIC mover word
    # [w_0, w_1, ..., w_{L-1}] where w_0 is the first element.
    # The word [0,5,4,3,2,1,0,5,0,5] has 10 elements.
    # Edge from w_9=5 to w_0=0: |5-0| = 5 = n-1. That's the ring edge (0,5). Adjacent. ✓
    # But procs 1,2,3,4 each appear once (not twice).
    #
    # So the bug is: the word [0,5,4,3,2,1,0,5,0,5] passes the fairness check
    # in the code but shouldn't.
    # move_counts in DFS: starts at [1,0,0,0,0,0] (proc 0 counted).
    # After extending to 5: [1,0,0,0,0,1]. Then 4: [1,0,0,0,1,1]. etc.
    # After building [0,5,4,3,2,1,0,5,0,5]:
    #   0: 3, 5: 3, 4: 1, 3: 1, 2: 1, 1: 1.
    # all(c >= 2 for c in [3,1,1,1,1,3]) → False. Should NOT pass.

    # So maybe the DFS code is actually correct and this word is NOT in survivors.
    # But the output showed "SURVIVOR:" for it. Let me look at the output again.
    # No wait, the output showed:
    # "SURVIVOR: [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 4, 5, 4, 5]"  (length 14)
    # "SURVIVOR: [0, 5, 4, 3, 2, 1, 0, 5, 0, 5]" was NOT in the output!
    # Let me re-read the output. The actual survivors listed were:
    # [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1]  (length 12)
    # [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 4, 5, 0, 5]  (length 14)
    # etc.

    # OK so the [0,5,0,5] short one was not an actual survivor. My mistake.
    # The shortest survivor is [0,5,4,3,2,1,0,5,4,3,2,1] (the double sweep, L=12).

    # Let me now check if ALL listed survivors are sweep-type.
    print("\n" + "=" * 70)
    print("Checking actual survivors from first run output:")
    print("=" * 70)

    real_survivors = [
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1],
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 4, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 4, 5, 0, 5, 4, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5],  # L=10, check fairness
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 4, 5, 4, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 0, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 5, 0, 5, 0, 1, 0, 1],
        [0, 5, 4, 3, 2, 1, 0, 1, 0, 1],  # L=10
        [0, 5, 4, 3, 2, 1, 0, 1, 0, 1, 0, 5, 0, 5],
        [0, 5, 4, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 5],
    ]

    for w in real_survivors:
        mc = Counter(w)
        fair = all(mc.get(p, 0) >= 2 for p in range(6))
        winding = 0
        for i in range(len(w)):
            diff = (w[(i+1)%len(w)] - w[i]) % 6
            if diff == 1:
                winding += 1
            elif diff == 5:
                winding -= 1
        # Edge parity
        edge_counts = Counter()
        for i in range(len(w)):
            a, b_val = w[i], w[(i+1) % len(w)]
            e = tuple(sorted([a, b_val]))
            if abs(a-b_val) > 1:
                e = (0, 5)
            edge_counts[e] += 1
        parities = set(c % 2 for c in edge_counts.values())
        zeros = sum(1 for p in range(6) if mc.get(p,0) == 0)

        print(f"  {w}")
        print(f"    L={len(w)}, fair={fair}, W={winding}, edge_parities={parities}")
        if not fair:
            miss = [p for p in range(6) if mc.get(p,0) < 2]
            print(f"    *** NOT FAIR: procs {miss} have moves < 2 ***")
            print(f"    *** BUG IN ORIGINAL CODE ***")


if __name__ == "__main__":
    main()
