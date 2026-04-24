"""
RA12 v3: Analytical investigation of sorry 5 — odd-parity residual.

The sorry is in consecutive_binary_isolated_false' which has hypothesis n >= 9.

Key insight: the proof structure is:
  by_cases hparity : (both neighbors have even parity in gap)
  · Even case: done by isolated_minGap_ec_of_parity_match
  · Odd case: sorry  <-- THIS IS THE SORRY

The negated parity condition (push_neg) gives:
  NOT (pfc(i, a+1) % 2 = pfc(i, b) % 2 AND pfc(rri, a+1) % 2 = pfc(rri, b) % 2)
which means:
  pfc(i, a+1) % 2 ≠ pfc(i, b) % 2 OR pfc(rri, a+1) % 2 ≠ pfc(rri, b) % 2

i.e., at least one of the two binary neighbors has ODD fire count in the gap (a, b).

Question: does this case even arise? Or can we derive False from the hypotheses
alone (making the case vacuous)?

ANALYTICAL ARGUMENT:

The MinFiringGap for ri has gap g = b - a >= 2.
Between steps a+1 and b-1 (inclusive), there are g-1 steps.
At step a: mover = ri
At step b: mover = ri
Steps a+1, ..., b-1: movers ≠ ri (no ri-fires between)

The step right after ri fires (step a+1) must have a mover that is a neighbor of ri
(by locality of movers in a good cycle: next mover is left, self, or right of previous).
Since ri just fired at step a, step a+1's mover ∈ {left(ri), ri, right(ri)} = {i, ri, rri}.
But ri doesn't fire at a+1 (gap >= 2). So mover at a+1 is i or rri.

Similarly, the step right before b: the mover at b is ri, so the mover at b-1 must be
a neighbor of ri's mover at b... wait, this is about the PREVIOUS mover being a neighbor
of the CURRENT mover. Actually: mover at step k+1 ∈ {left, self, right} of mover at step k.

So mover(a+1) ∈ {i, ri, rri} and mover(a+1) ≠ ri -> mover(a+1) ∈ {i, rri}.

This means: the fire count of i or rri in the gap [a+1, b) is at least 1
(whoever fires at step a+1 contributes 1).

Now: the MinFiringGap is the MINIMUM over ALL consecutive firing pairs of ri.
If there are fc >= 2 firings of ri, there are fc consecutive pairs (cyclically).
The MinFiringGap picks the smallest gap.

For the min gap to have odd parity for a neighbor: that neighbor fires an odd
number of times in a gap of size g-1 steps (at most g-1 fires of that neighbor).

KEY QUESTION: With the MINIMUM gap, can a binary neighbor fire an odd number of times?

The total fire count of proc i (binary) is EVEN. Let's say ri fires at steps
a_1, a_2, ..., a_fc (in order). The gaps are [a_1, a_2), [a_2, a_3), ..., [a_fc, a_1 + L).
The total fires of proc i across ALL gaps sums to fc(i), which is even.

If there are an even number of gaps (fc is even), each gap contributes some fire count
of i. The sum is even. If each gap has the same parity, they're all even or all odd.
With even number of odd values: sum is even. OK.
With even number of even values: sum is even. OK.

If there are an odd number of gaps (fc is odd): binary fire count of ri is even,
but fc = number of gaps. If fc is odd, we have an odd number of gap-fire-counts
summing to an even total. This means an odd number of them are odd... so at least one
gap has odd parity. BUT the MinFiringGap might not be THAT gap.

Hmm, this is getting complicated. Let me just enumerate computationally.

Actually, let me reconsider. The n >= 9 hypothesis means we're dealing with large
rings. Let me check n=5, 7, 9 computationally using a proper good-cycle enumeration
that doesn't rely on fixed transition functions.
"""

import itertools
from collections import Counter, defaultdict

def check_odd_parity_with_mover_words(n, ms):
    """
    Enumerate mover words and check which ones satisfy all conditions.

    For each mover word:
    1. Binary fire counts even
    2. All procs fire (hfull)
    3. ri has isolated firings, fc >= 2
    4. Some mover outside binary triple
    5. MinFiringGap has gap >= 2
    6. At least one neighbor has odd parity in min gap

    For qualifying mover words, check if a config sequence EXISTS without EC.
    (If EC is forced at a binary proc by the mover word, it's forced regardless
    of ternary transitions.)
    """
    binary_pos = [0, 1, 2]
    ri = 1
    i_pos = 0
    rri_pos = 2
    L_target = None  # will try various lengths

    print(f"\nn={n}, ms={ms}")
    print(f"Binary triple at 0, 1, 2")

    # For n=5: min cycle length with all constraints
    # Binary: each fires even >= 2. Min 2 each -> 6 binary fires.
    # Ternary: each fires >= 1. Min 1 each -> n-3 ternary fires.
    # Total: 6 + (n-3) = n+3.

    # But ternary must return to initial. With context-dependent:
    # min ternary fires = 2 (as analyzed). So total >= 6 + 2*(n-3) = 2n.
    # For n=5: >= 10. For n=7: >= 14. For n=9: >= 18.

    # Actually, min ternary fires for return: with m=3, can return with 2 fires
    # (e.g., +1 then +2 = +3 ≡ 0 mod 3). OR with 3 fires (all +1).
    # But hfull requires >= 1 fire per proc.
    # With 2 fires per ternary: total = 6 + 2*(n-3) = 2n.

    # But we also need proc-level consistency for the FULL config sequence.
    # Let me just enumerate short mover words.

    min_L = n + 3  # absolute minimum: 3 binary × 2 + (n-3) ternary × 1
    max_L = min(2 * n + 4, 22)  # reasonable bound

    total_words = 0
    qualifying_words = 0
    odd_parity_words = 0

    for L in range(min_L, max_L + 1):
        print(f"  Length L={L}...", end=" ", flush=True)
        count_L = 0

        # Enumerate mover words of length L over {0, ..., n-1}
        # with locality constraint: mover[k+1] ∈ {mover[k]-1, mover[k], mover[k]+1} mod n
        # and cyclic: mover[0] ∈ {mover[L-1]-1, mover[L-1], mover[L-1]+1} mod n

        # This is too many even with locality. Let me use DFS.

        # State: (position in word, current mover, fire counts tuple)
        # Prune: fire counts must be achievable

        from functools import lru_cache

        # Use iterative DFS
        stack = []
        # Start with first mover = any proc
        for first_mover in range(n):
            fc = [0] * n
            fc[first_mover] = 1
            stack.append((1, first_mover, first_mover, tuple(fc), (first_mover,)))

        while stack:
            pos, prev_mover, first_mover, fc_tuple, word = stack.pop()

            if pos == L:
                # Check cyclic locality: first_mover ∈ neighbors of prev_mover
                if abs(first_mover - prev_mover) % n > 1 and abs(first_mover - prev_mover) % n < n - 1:
                    continue

                fc = list(fc_tuple)

                # Check constraints
                # Binary fire counts even
                if any(fc[b] % 2 != 0 for b in binary_pos):
                    continue
                # hfull
                if any(fc[p] == 0 for p in range(n)):
                    continue
                # Some mover outside triple
                if all(w in binary_pos for w in word):
                    continue
                # ri fc >= 2
                if fc[ri] < 2:
                    continue

                total_words += 1

                # Check isolated firings of ri
                ri_steps = [k for k in range(L) if word[k] == ri]
                isolated = True
                for k in ri_steps:
                    next_k = (k + 1) % L
                    if word[next_k] == ri:
                        isolated = False
                        break
                if not isolated:
                    continue

                qualifying_words += 1

                # Find MinFiringGap
                gaps = []
                for idx in range(len(ri_steps)):
                    a = ri_steps[idx]
                    b = ri_steps[(idx + 1) % len(ri_steps)]
                    if b > a:
                        gap = b - a
                    else:
                        gap = (L - a) + b
                    gaps.append((a, b, gap))

                min_gap_val = min(g for _, _, g in gaps)
                if min_gap_val < 2:
                    continue

                min_pair = [(a, b, g) for a, b, g in gaps if g == min_gap_val][0]
                a_step, b_step, gap = min_pair

                # Count neighbor fires in gap
                left_fires = 0
                right_fires = 0
                for k_off in range(1, gap):
                    step = (a_step + k_off) % L
                    if word[step] == i_pos:
                        left_fires += 1
                    if word[step] == rri_pos:
                        right_fires += 1

                if left_fires % 2 == 0 and right_fires % 2 == 0:
                    continue  # even parity, handled

                odd_parity_words += 1
                count_L += 1

                # Check EC at binary procs (binary values fully determined by mover word)
                # Context at proc p (binary) at step k:
                # val(p, k) = pfc(p, k) % 2 (assuming initial = 0)
                # Context = (val(left_p, k), val(p, k), val(right_p, k))

                pfc = [[0] * (L + 1) for _ in range(n)]
                for k in range(L):
                    for p in range(n):
                        pfc[p][k + 1] = pfc[p][k] + (1 if word[k] == p else 0)

                # Check EC at ri=1 (all-binary neighborhood)
                mover_ctx_ri = set()
                nonmover_ctx_ri = set()
                for k in range(L):
                    ctx = (pfc[0][k] % 2, pfc[1][k] % 2, pfc[2][k] % 2)
                    if word[k] == ri:
                        mover_ctx_ri.add(ctx)
                    else:
                        nonmover_ctx_ri.add(ctx)

                ec_at_ri = bool(mover_ctx_ri & nonmover_ctx_ri)

                if ec_at_ri:
                    continue  # EC at ri, covered

                # Check EC at i=0 and rri=2
                # proc 0: left = n-1 (ternary), right = 1 (binary)
                # proc 2: left = 1 (binary), right = 3 (ternary)
                # Ternary neighbors have FREEDOM -> adversary can avoid EC

                # So EC might only be at binary procs where all 3 context components
                # are binary. Only ri=1 has all-binary (L,S,R).
                # Procs 0 and 2 have one ternary neighbor each -> adversary controls ternary.

                # So if no EC at ri, the adversary CAN potentially avoid EC at 0 and 2
                # by choosing ternary values carefully.

                # What about EC at ternary procs?
                # Ternary proc p: context (L,S,R). S is ternary (adversary chooses),
                # L and R could be binary or ternary.
                # The adversary controls S AND (for ternary L,R) those values too.
                # So the adversary can potentially avoid EC at ternary procs.

                # CONCLUSION: If no EC at ri, the odd-parity case might be
                # non-trivially satisfiable.

                if odd_parity_words <= 20 or (odd_parity_words <= 100 and not ec_at_ri):
                    print(f"\n    ODD WORD (no EC at ri): L={L}, word={word}")
                    print(f"      ri fires at: {ri_steps}, gap=({a_step},{b_step},{gap})")
                    print(f"      L_fires={left_fires}, R_fires={right_fires}")
                    print(f"      ri mover contexts: {mover_ctx_ri}")
                    print(f"      ri nonmover contexts: {nonmover_ctx_ri}")

                continue

            # Extend word by one step
            # Next mover must be neighbor of prev_mover
            for next_mover in [(prev_mover - 1) % n, prev_mover, (prev_mover + 1) % n]:
                fc = list(fc_tuple)
                fc[next_mover] += 1
                # Prune: can we still satisfy constraints in remaining steps?
                remaining = L - pos - 1
                # Need enough remaining for unfired procs
                unfired = sum(1 for p in range(n) if fc[p] == 0)
                # Very rough: need at least unfired more steps
                # (actually locality makes this harder but let's keep it simple)
                if unfired > remaining + 1:  # +1 for current step
                    continue
                # Binary fire count parity: at end, need even. With remaining steps,
                # need fc[b] + (future fires of b) to be even.
                # Can check: is it possible?
                feasible = True
                for b in binary_pos:
                    if pos == L - 1:  # this is the last step
                        if fc[b] % 2 != 0:
                            feasible = False
                            break
                if not feasible:
                    continue

                stack.append((pos + 1, next_mover, first_mover, tuple(fc), word + (next_mover,)))

        print(f"odd_parity={count_L}")

    print(f"\nSummary for n={n}:")
    print(f"  Total valid mover words: {total_words}")
    print(f"  With isolated ri firings: {qualifying_words}")
    print(f"  Odd-parity residual: {odd_parity_words}")

    return odd_parity_words

if __name__ == '__main__':
    # Start with n=5
    count5 = check_odd_parity_with_mover_words(5, [2, 2, 2, 3, 3])

    if count5 > 0:
        print("\n*** Odd-parity case is NON-VACUOUS at n=5! ***")
        print("Now checking n=7...")
        count7 = check_odd_parity_with_mover_words(7, [2, 2, 2, 3, 3, 3, 3])
    else:
        print("\n*** Odd-parity case is VACUOUS at n=5! ***")
        print("Checking n=7 to confirm pattern...")
        count7 = check_odd_parity_with_mover_words(7, [2, 2, 2, 3, 3, 3, 3])
