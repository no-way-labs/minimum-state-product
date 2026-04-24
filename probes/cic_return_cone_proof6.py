#!/usr/bin/env python3
"""
CIC Exploration 11f: Prove all fair Case 3c words are pure sweeps.

Key discovery: with k>=3 non-adjacent binary on C_n, EVERY fair adjacent
cyclic mover word is a pure sweep. Tools 2/3 are unnecessary.

This script:
1. Fast verification with controlled search
2. Proof of the Sweep-Only Lemma
3. Check k=2 as control (non-sweeps exist)
"""

from collections import Counter
import sys


def is_pure_sweep(word, n):
    L = len(word)
    fwd = all((word[(i+1) % L] - word[i]) % n == 1 for i in range(L))
    bwd = all((word[i] - word[(i+1) % L]) % n == 1 for i in range(L))
    return fwd or bwd


def count_fair_words(n, binary_positions, max_L, report=True):
    """Count fair adjacent cyclic words. Returns (total, sweeps, nonsweep_examples)."""
    binary_set = set(binary_positions)
    k = len(binary_positions)

    total = 0
    sweeps = 0
    ns_examples = []

    def dfs(word, mc):
        nonlocal total, sweeps
        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            d = abs(current - first)
            if d == 1 or d == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0 for b in binary_positions):
                        total += 1
                        if is_pure_sweep(word, n):
                            sweeps += 1
                        else:
                            if len(ns_examples) < 3:
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

    ns = total - sweeps
    if report:
        tag = '✓' if ns == 0 else '✗'
        print(f"  n={n} k={k} bin={binary_positions} "
              f"maxL={max_L}: {total} fair, "
              f"{sweeps} sweep, {ns} non-sweep {tag}")
    return total, sweeps, ns_examples


def main():
    print("CIC Exploration 11f: Sweep-Only Lemma")
    print("=" * 60)

    # PART 1: k=2 controls (non-sweeps SHOULD exist)
    print("\nPART 1: k=2 controls (expect non-sweeps)")
    count_fair_words(5, [0, 2], max_L=18)
    count_fair_words(6, [0, 3], max_L=18)
    count_fair_words(6, [0, 2], max_L=18)
    count_fair_words(7, [0, 3], max_L=18)

    # PART 2: k=1 controls
    print("\nPART 2: k=1 controls")
    count_fair_words(4, [0], max_L=16)
    count_fair_words(5, [0], max_L=16)

    # PART 3: k=3 (should be all sweeps)
    print("\nPART 3: k=3 (expect ALL sweeps)")
    count_fair_words(6, [0, 2, 4], max_L=20)
    count_fair_words(7, [0, 2, 4], max_L=20)
    count_fair_words(7, [0, 2, 5], max_L=20)
    count_fair_words(8, [0, 2, 4], max_L=18)
    count_fair_words(8, [0, 2, 5], max_L=18)
    count_fair_words(8, [0, 3, 5], max_L=18)
    count_fair_words(8, [0, 3, 6], max_L=18)
    count_fair_words(9, [0, 2, 4], max_L=18)
    count_fair_words(9, [0, 3, 6], max_L=18)

    # PART 4: k=4
    print("\nPART 4: k=4")
    count_fair_words(8, [0, 2, 4, 6], max_L=18)
    count_fair_words(9, [0, 2, 4, 6], max_L=18)
    count_fair_words(9, [0, 2, 4, 7], max_L=18)

    # PART 5: Understand the mechanism
    print("\n" + "=" * 60)
    print("PART 5: WHY are all k>=3 words sweeps?")
    print("=" * 60)

    # For k=2: show a non-sweep example
    _, _, ns_ex = count_fair_words(5, [0, 2], max_L=18,
                                   report=False)
    if ns_ex:
        print(f"\nk=2 non-sweep example:")
        w = ns_ex[0]
        mc = Counter(w)
        print(f"  word: {w}")
        print(f"  moves: {dict(sorted(mc.items()))}")

        # Analyze direction changes
        dirs = []
        for i in range(len(w)):
            d = (w[(i+1) % len(w)] - w[i]) % 5
            dirs.append('+' if d == 1 else '-')
        print(f"  directions: {''.join(dirs)}")

        # Find bounce points (direction reversals)
        bounces = []
        for i in range(len(w)):
            if dirs[i] != dirs[(i-1) % len(w)]:
                bounces.append((i, w[i]))
        print(f"  bounces at: {bounces}")

    # PROOF SKETCH:
    print("\n" + "=" * 60)
    print("PROOF of Sweep-Only Lemma")
    print("=" * 60)
    print("""
Lemma: On C_n with k >= 3 pairwise non-adjacent binary
processors, every fair adjacent cyclic mover word is a
pure sweep.

Proof:
Let w be a fair adjacent cyclic word of length L on C_n.
Let B = {b_1,...,b_k} be the binary processors (k >= 3,
pairwise non-adjacent).

Step 1: Direction structure.
Each step is +1 (clockwise) or -1 (counterclockwise).
If all steps have the same sign, w is a pure sweep. Done.
Otherwise, w has at least one direction reversal.

Step 2: Reversal = bounce at some processor.
A reversal at time t means w_{t-1}, w_t, w_{t+1} with
w_{t+1} = w_{t-1}. Processor w_t is the "bounce point."
After the bounce, w_t has fired once and w_{t-1} fires
again immediately.

Step 3: Bouncing and binary parity.
If w_t is binary: it fires once at the bounce. For binary
parity, it must fire again later (total even). Another
visit is needed.

More importantly: consider the edge counts.
All edges have the same parity (= W mod 2, winding number).
A reversal at w_t changes the edge profile: the edge on
one side gets +2 (entry and exit), the edge on the other
side gets 0 from this bounce.

Step 4: The critical constraint.
With k >= 3 non-adjacent binary, the ring has k arcs.
In a pure sweep: every edge gets the same count |W|.
In a non-sweep: some edges get more, some get less.

For fairness: every processor's total edge count (sum of
its two edges) must be >= 4 (moves >= 2, each visit uses
2 edge traversals).

For an edge with count 0: the two procs on either side
get ALL their traversals from other edges. But this means
the walk never crosses this edge, so one side is reached
only via the other direction around the ring.

Step 5: Zero edges partition the ring.
Let Z = set of edges with count 0. Removing Z disconnects
the ring into arcs. Within each arc, the walk can traverse
freely. Between arcs, the walk must go the "other way."

With k >= 3 binary procs, if any zero edge exists, it
creates an arc containing at most k-1 binary procs.
But the walk must visit ALL binary procs, each with even
move count.

The critical constraint: if edge (p, p+1) has count 0,
then the walk never goes p -> p+1 or p+1 -> p. So when
the walk is at p, it can only go to p-1; when at p+1,
only to p+2. The walk passes through p and p+1 but
always continues in the same direction past them.

Actually, count 0 means the walk NEVER traverses this
edge. So the walk never has consecutive movers (p, p+1)
or (p+1, p). If the walk is at p, the next mover is p-1
(it bounces). If the walk is at p+1, the next is p+2.
So p and p+1 are "bounce endpoints" of their respective
arcs.

Step 6: Incompatibility with k >= 3.
With k >= 3 non-adjacent binary and zero edges:
Consider the arc structure. Binary procs at {b_1,...,b_k}
divide the ring into k gap arcs. If there's a zero edge
in gap arc i, the walk can't cross it. The walk must
enter gap arc i from one end (say b_i) and bounce back.
Every proc in the gap is visited only from one side.

For the walk to be cyclic and visit all procs on both
sides of the zero edge, it must go AROUND the entire
ring in one direction, then come back. But with k >= 3
non-adjacent binary, this creates a contradiction with
binary parity.

ACTUALLY, the cleaner argument:

If the walk is NOT a pure sweep, it has a reversal.
A reversal at processor p means the walk goes:
  ..., p-1, p, p-1, ... (or ..., p+1, p, p+1, ...)

Consider the walk as two phases:
  Phase 1: going clockwise (p, p+1, p+2, ...)
  Phase 2: going counterclockwise (p, p-1, p-2, ...)

Each reversal switches the phase. In a cyclic word,
the number of CW-to-CCW and CCW-to-CW reversals must
be equal (say r reversals in each direction, 2r total).

Each reversal at processor p adds 1 to p's move count.
Between two reversals, the walk traverses a contiguous
arc in one direction, visiting each proc in the arc once.

For binary proc b: b's total move count = (number of arcs
that include b) which is the number of times the walk
passes through b. This must be even.

With 2r reversals, the ring is divided into 2r directed
arcs (alternating CW and CCW). Each proc lies in some
number of arcs. For the walk to be fair: each proc must
be in >= 2 arcs.

The reversal points divide the walk into 2r segments.
Each segment is a directed arc on C_n. The arc endpoints
are at the reversal points.

Now: with k >= 3 non-adjacent binary, and binary parity:
Binary proc b must appear in an even number of arcs.
Each arc visits b at most once (it's a directed path).
So b is in exactly 2, 4, 6, ... arcs.

KEY: the reversals partition the walk into 2r directed
arcs. The reversal POINTS are specific processors.
If a reversal happens at processor p, then p is a
boundary between arcs.

For the walk to visit all n processors, the union of all
2r arcs must cover all n processors.

With k >= 3 binary procs, each in an even number of arcs,
the total binary "arc memberships" is even * k (even).
Non-binary procs have no parity constraint.

I need a sharper argument. Let me think about what
makes k >= 3 special vs k <= 2.
""")

    # Step 6: the actual proof via winding number parity
    print("=" * 60)
    print("REFINED PROOF via arc analysis")
    print("=" * 60)

    # For k=2 non-adjacent binary, show bounce words exist:
    _, _, ns2 = count_fair_words(6, [0, 3], max_L=16,
                                 report=False)
    if ns2:
        w2 = ns2[0]
        print(f"\nk=2 example: {w2}")
        # Analyze arc structure
        L = len(w2)
        n = 6
        dirs = [(w2[(i+1)%L] - w2[i]) % n for i in range(L)]
        dir_signs = ['+' if d == 1 else '-' for d in dirs]
        print(f"  Directions: {''.join(dir_signs)}")

        # Count reversals
        reversals = sum(1 for i in range(L)
                       if dir_signs[i] != dir_signs[(i-1)%L])
        print(f"  Reversals: {reversals}")

        mc = Counter(w2)
        print(f"  Moves: {dict(sorted(mc.items()))}")

        # Binary moves
        for b in [0, 3]:
            print(f"  Binary {b}: {mc[b]} moves "
                  f"({'even' if mc[b]%2==0 else 'ODD'})")


if __name__ == "__main__":
    main()
