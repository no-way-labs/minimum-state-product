#!/usr/bin/env python3
"""
Debug: Why can't we find sorry-pattern sequences?

The sorry pattern requires:
  1. Phase starts at t's neighbor (lt=0 or rt=2)
  2. First lt fire at fL, with mover at fL-1 = llt=8
  3. First rt fire at fR, with mover at fR-1 = rrt=3
  4. All consecutive movers ring-adjacent

Let's trace: if we start at rt=2 (so lt hasn't fired yet):
  Path to reach llt=8 without firing lt=0:
  2 -> 3 -> 4 -> 5 -> 6 -> 7 -> 8 (llt) -> then next = 0 (lt) ✓
  (since 8 adj to 0 in ring of 9, dist=1)

  So fL-1 = position of 8, fL = position of 0. Mover at fL-1 = 8 = llt ✓

  But then we also need rrt=3 before first rt fire.
  If we started at rt=2, then first_rt = 0 (the very first step).
  We need mover at fR-1 = rrt=3... but fR=0 means fR-1 = -1, before the phase.

  WAIT: If first_rt is at position 0 (the first step), then fR-1 is step a-1,
  which is the previous t-fire. That's t=1, not rrt=3.

  So we need to delay the first rt fire too!

  Option: start at rt=2 (first rt fire at pos 0)... that fails.
  Option: start at lt=0 (first lt fire at pos 0)... then first_lt = 0,
    fL-1 = a-1 = t. Need fL-1 = llt=8. t=1 ≠ 8. Fails.

  So NEITHER lt nor rt can fire first! We need to start with something else
  adj to t... but adj to t=1 is only 0 and 2 (lt and rt).

  CONCLUSION: The sorry pattern as stated is IMPOSSIBLE for the first step
  of the phase, because the first mover must be lt or rt, and the step
  before it (the t-fire) is t, not llt or rrt.

  Unless... the first step ISN'T lt or rt. But it must be ring-adj to t.
  For n=9, t=1: neighbors are 0 and 2. So yes, it MUST be lt or rt.

  The sorry pattern must mean something different. Let me re-read the problem.
"""

# Re-reading the problem statement:
# "left²(t) fires at step fL-1 (immediately before the first left(t) fire at fL)"
#
# This means: within the phase [a, s), the first lt fire is at step fL.
# The step fL-1 (one before) has mover = llt.
#
# For this to be within the phase, we need fL >= a+1 (so fL-1 >= a).
# At step a, the mover must be adj to t. So mover at a ∈ {lt, rt}.
#
# If mover at a = rt, then first_rt = a. But we need first_rt to also have
# rrt before it. first_rt = a means fR = a, fR-1 = a-1 (= previous t fire).
# That's t, not rrt.
#
# UNLESS the sorry pattern only requires ONE of the two (llt before first lt
# OR rrt before first rt), not both simultaneously.
#
# Or... maybe the sorry case is that the BACKWARD SCAN from fL extends
# past llt. Meaning: we check mover at fL-1, and if it's llt, we try to
# use mk_ec_left. But mk_ec_left needs a "gap" (no llt/lt/t fires) between
# some non-mover step v and fL. If llt fires at fL-1, there's no gap.
#
# Let me re-read more carefully...
#
# "The sorry situation: The Lean proof tries to show that mixed phases produce
# entry conflict. It succeeds when there's a GAP between the last left²(t) fire
# and the first left(t) fire. It gets STUCK when:
# - left²(t) fires at step fL-1"
#
# So the sorry is about what happens INSIDE the mixed phase. Let me think about
# what sequences ARE possible:
#
# Start: mover at a ∈ {lt, rt}.
# Case 1: start at rt=2. Then first_rt = a. For first_lt at fL > a:
#   Path from 2: 2 -> 3 -> 4 -> ... -> 8 -> 0 (= lt).
#   So movers are: [2, 3, 4, 5, 6, 7, 8, 0, ...].
#   mover at fL-1 = 8 = llt. ✓ Sorry pattern for the L side!
#
#   For the R side: first_rt = a = step 0. mover at fR-1 = t (outside phase).
#   The sorry only requires the L side to be stuck.
#
# Case 2: start at lt=0. Then first_lt = a. For first_rt at fR > a:
#   Path from 0: 0 -> 8 -> 7 -> 6 -> 5 -> 4 -> 3 -> 2 (= rt).
#   mover at fR-1 = 3 = rrt. ✓ Sorry pattern for the R side!
#
# So the sorry pattern is ONE-SIDED, not both-sided simultaneously.
# Let me re-enumerate.

def ring_adj(a, b, n):
    d = min((a - b) % n, (b - a) % n)
    return d == 1

def enumerate_sorry_L(n, t, max_len=20, max_results=5000):
    """Sorry-L: start at rt, walk to llt, then lt fires. Mixed = need both L and R."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n

    results = []

    def dfs(seq, first_lt, first_rt):
        if len(seq) > max_len or len(results) >= max_results:
            return

        last = seq[-1]

        # Try ending with t
        if ring_adj(last, t, n) and first_lt is not None and first_rt is not None:
            # Check sorry-L pattern: mover at first_lt - 1 = llt
            if first_lt >= 1 and seq[first_lt - 1] == llt:
                results.append(list(seq) + [t])

        # Extend
        for nxt in range(n):
            if nxt == t:
                continue
            if not ring_adj(last, nxt, n):
                continue

            new_fL = first_lt if first_lt is not None else (len(seq) if nxt == lt else None)
            new_fR = first_rt if first_rt is not None else (len(seq) if nxt == rt else None)

            dfs(seq + [nxt], new_fL, new_fR)

    # Start at rt (first_rt = 0)
    dfs([rt], None, 0)
    # Start at lt (first_lt = 0, need first_lt >= 1 for sorry-L -> skip)

    return results

def enumerate_sorry_R(n, t, max_len=20, max_results=5000):
    """Sorry-R: start at lt, walk to rrt, then rt fires."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n

    results = []

    def dfs(seq, first_lt, first_rt):
        if len(seq) > max_len or len(results) >= max_results:
            return

        last = seq[-1]

        # Try ending with t
        if ring_adj(last, t, n) and first_lt is not None and first_rt is not None:
            # Check sorry-R: mover at first_rt - 1 = rrt
            if first_rt >= 1 and seq[first_rt - 1] == rrt:
                results.append(list(seq) + [t])

        for nxt in range(n):
            if nxt == t:
                continue
            if not ring_adj(last, nxt, n):
                continue

            new_fL = first_lt if first_lt is not None else (len(seq) if nxt == lt else None)
            new_fR = first_rt if first_rt is not None else (len(seq) if nxt == rt else None)

            dfs(seq + [nxt], new_fL, new_fR)

    # Start at lt (first_lt = 0)
    dfs([lt], 0, None)

    return results

def main():
    n = 9
    t = 1
    lt = 0; rt = 2; llt = 8; rrt = 3
    ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]

    name_map = {0: 'L', 1: 'T', 2: 'R', 3: 'RR', 4: '4', 5: '5', 6: '6', 7: '7', 8: 'LL'}

    print(f"n={n}, t={t}, lt={lt}, rt={rt}, llt={llt}, rrt={rrt}")
    print()

    print("=== Sorry-L sequences (start at R, walk CW to LL, then L fires) ===")
    seqs_L = enumerate_sorry_L(n, t, max_len=16, max_results=5000)
    print(f"Found {len(seqs_L)} sequences")

    from collections import defaultdict
    len_counts = defaultdict(int)
    for s in seqs_L:
        len_counts[len(s)] += 1
    for l in sorted(len_counts):
        print(f"  len={l}: {len_counts[l]}")

    shortest_L = min(len(s) for s in seqs_L) if seqs_L else 0
    for s in [s for s in seqs_L if len(s) == shortest_L][:10]:
        print(f"  {' '.join(name_map.get(m, str(m)) for m in s)}")

    print()
    print("=== Sorry-R sequences (start at L, walk CCW to RR, then R fires) ===")
    seqs_R = enumerate_sorry_R(n, t, max_len=16, max_results=5000)
    print(f"Found {len(seqs_R)} sequences")

    len_counts = defaultdict(int)
    for s in seqs_R:
        len_counts[len(s)] += 1
    for l in sorted(len_counts):
        print(f"  len={l}: {len_counts[l]}")

    shortest_R = min(len(s) for s in seqs_R) if seqs_R else 0
    for s in [s for s in seqs_R if len(s) == shortest_R][:10]:
        print(f"  {' '.join(name_map.get(m, str(m)) for m in s)}")


if __name__ == '__main__':
    main()
