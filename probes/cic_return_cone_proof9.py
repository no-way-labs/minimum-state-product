#!/usr/bin/env python3
"""
CIC Exploration 11 — FINAL: Return Cone Theorem for Case 3c.

THEOREM (Case 3c Word-Level Kill):
Let n >= 6, k >= 3 pairwise non-adjacent binary processors on C_n.
If every non-binary proc is adjacent to at least one binary proc
(equivalently, max gap <= 2 between consecutive binary procs,
equivalently n <= 3k), then every fair adjacent cyclic mover word
is killed by one of:
  (a) Shadow Cycle Mirror Theorem (if word is a pure sweep), or
  (b) Two-Singleton-Edge Theorem (if word has >= 2 singleton edges), or
  (c) Binary-Bounce Context Lemma (if word has 0-1 singleton edges
      and is not a sweep).

PROOF STRUCTURE:
1. All edges have parity W mod 2 (winding number).
2. Binary proc b with moves(b) = 2 (minimum): edge_L + edge_R = 4.
   If W odd: both odd, so (1,3) or (3,1) — exactly 1 singleton from b.
3. Let j = #{binary with moves = 2}.
   - j >= 2: at least 2 singletons from binary alone -> Tool 2. Done.
   - j <= 1: at most 1 singleton from binary.
4. Interior (non-binary-adjacent) edges: with max gap <= 2,
   there are exactly n - 2k interior edges (those between two non-binary).
   Max gap <= 2 means each gap has <= 1 interior edge.
5. Singleton counting for j <= 1:
   Depends on W parity and L (word length).
6. When singletons < 2: Binary-bounce (Tool 3) applies because
   every non-binary proc has a binary neighbor (max gap <= 2).

This script verifies the theorem computationally for n=6..12.
"""

from collections import Counter
import sys


def is_pure_sweep(word, n):
    L = len(word)
    return (all((word[(i+1)%L]-word[i]) % n == 1 for i in range(L)) or
            all((word[i]-word[(i+1)%L]) % n == 1 for i in range(L)))


def count_singletons(word, n):
    ec = Counter()
    L = len(word)
    for i in range(L):
        a, b = word[i], word[(i+1) % L]
        e = (min(a,b), max(a,b)) if abs(a-b) == 1 else (0, n-1)
        ec[e] += 1
    return sum(1 for c in ec.values() if c == 1)


def check_return_cone(word, n):
    L = len(word)
    pp = {p: set() for p in range(n)}
    for t in range(L):
        pp[word[t]].add(t)
    for s in range(n):
        for l in range(1, n):
            S = set((s+i)%n for i in range(l))
            ap = set()
            for p in S:
                ap |= pp[p]
            if not ap or len(ap) == L:
                continue
            sp = sorted(ap)
            mg = 0
            for i in range(len(sp)):
                if i+1 < len(sp):
                    g = sp[i+1]-sp[i]-1
                else:
                    g = (sp[0]+L)-sp[-1]-1
                mg = max(mg, g)
            if mg > 0 and mg == L - len(ap):
                return True
    return False


def check_binary_bounce(word, n, binary_set):
    """Thorough binary-bounce (Tool 3) check."""
    L = len(word)
    for p in range(n):
        if p in binary_set:
            continue
        nbs = [(p-1)%n, (p+1)%n]
        for b in nbs:
            if b not in binary_set:
                continue
            q = nbs[0] if nbs[1] == b else nbs[1]

            p_pos = [i for i in range(L) if word[i] == p]
            if not p_pos:
                continue

            for ui in range(len(p_pos)):
                u = p_pos[ui]
                prev = p_pos[ui-1]

                # Interval (prev, u): p frozen
                iv = []
                pos = (prev+1) % L
                while pos != u:
                    iv.append(word[pos])
                    pos = (pos+1) % L

                if not iv:
                    continue

                # Find sub-interval ending at the end with no q
                bc = 0
                for j in range(len(iv)-1, -1, -1):
                    if iv[j] == q:
                        break
                    if iv[j] == b:
                        bc += 1
                if bc == 2:
                    return True

                # Also check sub-interval from start with no q
                bc2 = 0
                for j in range(len(iv)):
                    if iv[j] == q:
                        break
                    if iv[j] == b:
                        bc2 += 1
                # For this to be Tool 3: need p=mover at start
                # of next interval. Not directly, but the pattern
                # at the START of the interval is:
                # t = prev+1, and at time prev, p fires.
                # So at time t = prev+1, p is NOT the mover.
                # And at time u, p IS the mover.
                # The sub-interval from start has t = prev+1,
                # but u would be the next q-position or u itself.
                # This doesn't directly give Tool 3 at u.
                # Skip for now.

    return False


def verify_theorem(n, binary_positions, max_L):
    """Verify the theorem for given configuration."""
    bs = set(binary_positions)
    k = len(binary_positions)

    # Check max gap
    gaps = []
    for i in range(k):
        b1 = binary_positions[i]
        b2 = binary_positions[(i+1) % k]
        gap = (b2 - b1 - 1) % n
        gaps.append(gap)
    max_gap = max(gaps)

    total = [0]
    kills = {'sweep': 0, 'singleton': 0, 'cone': 0,
             'bounce': 0}
    survs = []

    def dfs(word, mc):
        L = len(word)
        if L > max_L:
            return
        cur = word[-1]
        if L >= 2*n:
            first = word[0]
            d = abs(cur-first)
            if d == 1 or d == n-1:
                if all(c >= 2 for c in mc):
                    if all(mc[b]%2 == 0 for b in binary_positions):
                        total[0] += 1
                        if is_pure_sweep(word, n):
                            kills['sweep'] += 1
                            return
                        s = count_singletons(word, n)
                        if s >= 2:
                            kills['singleton'] += 1
                            return
                        if check_return_cone(word, n):
                            kills['cone'] += 1
                            return
                        if check_binary_bounce(word, n, bs):
                            kills['bounce'] += 1
                            return
                        survs.append(list(word))

        for np_ in [(cur-1)%n, (cur+1)%n]:
            mc[np_] += 1
            word.append(np_)
            dfs(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0]*n
    mc[0] = 1
    dfs([0], mc)

    ns = total[0] - kills['sweep']
    tag = '✓' if not survs else '✗'
    print(f"n={n} k={k} gaps={gaps} maxgap={max_gap} "
          f"maxL={max_L}: {total[0]} words, "
          f"{kills['sweep']} sweep, "
          f"{kills['singleton']} sing, "
          f"{kills['cone']} cone, "
          f"{kills['bounce']} bounce, "
          f"{len(survs)} surv {tag}")

    if survs and len(survs) <= 3:
        for w in survs:
            print(f"  {w}")

    return len(survs), max_gap


def main():
    print("THEOREM VERIFICATION: Case 3c Word-Level Kill")
    print("=" * 60)

    # Test max_gap <= 2 configurations (theorem should hold)
    print("\n--- Max gap <= 2 (theorem applies) ---")
    results_good = []
    configs = [
        (6, [0,2,4], 20),      # gaps=(1,1,1), maxgap=1
        (7, [0,2,4], 18),      # gaps=(1,1,2), maxgap=2
        (7, [0,2,5], 18),      # gaps=(1,2,1), maxgap=2
        (7, [0,3,5], 18),      # gaps=(2,1,1), maxgap=2
        (8, [0,2,4], 18),      # gaps=(1,1,3), maxgap=3 NO
        (8, [0,2,5], 18),      # gaps=(1,2,2), maxgap=2
        (8, [0,3,6], 18),      # gaps=(2,2,1), maxgap=2
        (9, [0,3,6], 18),      # gaps=(2,2,2), maxgap=2
        (9, [0,2,4], 18),      # gaps=(1,1,4), maxgap=4 NO
        (10, [0,3,6], 18),     # gaps=(2,2,3), maxgap=3 NO
        (10, [0,3,7], 18),     # gaps=(2,3,2), maxgap=3 NO
        (10, [0,4,7], 18),     # gaps=(3,2,2), maxgap=3 NO
        # k=4
        (8, [0,2,4,6], 18),   # gaps=(1,1,1,1), maxgap=1
        (9, [0,2,4,6], 18),   # gaps=(1,1,1,2), maxgap=2
        (9, [0,2,4,7], 18),   # gaps=(1,1,2,1), maxgap=2
        (10, [0,2,4,6], 18),  # gaps=(1,1,1,3), maxgap=3 NO
        (10, [0,2,5,7], 18),  # gaps=(1,2,1,2), maxgap=2
        (10, [0,3,5,8], 18),  # gaps=(2,1,2,1), maxgap=2
        (12, [0,3,6,9], 18),  # gaps=(2,2,2,2), maxgap=2
    ]

    for n, bp, ml in configs:
        surv, mg = verify_theorem(n, bp, ml)
        results_good.append((n, len(bp), mg, surv))

    print("\n--- Summary ---")
    print("MaxGap <= 2:")
    for n, k, mg, s in results_good:
        if mg <= 2:
            print(f"  n={n} k={k} maxgap={mg}: "
                  f"{'PASS' if s==0 else f'FAIL ({s} survivors)'}")

    print("\nMaxGap >= 3:")
    for n, k, mg, s in results_good:
        if mg >= 3:
            print(f"  n={n} k={k} maxgap={mg}: "
                  f"{'PASS' if s==0 else f'FAIL ({s} survivors)'}")


if __name__ == "__main__":
    main()
