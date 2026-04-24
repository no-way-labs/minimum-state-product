"""
RA12 v4: Efficient investigation of sorry 5.

Key realization: we only need to check whether the odd-parity residual case
can arise, and if so, whether EC at ri=1 (the all-binary proc) is forced.

The parity context at ri is fully determined by the mover word:
  ctx(ri, k) = (pfc(0,k)%2, pfc(1,k)%2, pfc(2,k)%2) ∈ {0,1}³

EC at ri means: some ctx appears at both a mover step and a non-mover step.

APPROACH: enumerate mover words using locality constraint (next mover is neighbor
of current mover) as a walk on the ring graph. Use DFS with aggressive pruning.

Focus on SMALL examples first (n=5), then check if the odd-parity case exists at all.
If it exists, check EC at ri. If EC at ri is not forced, then the mechanism must
be elsewhere and we need further investigation.

IMPORTANT STRUCTURAL OBSERVATION:
The Lean theorem has hypothesis n >= 9. But mover-word structure is similar for all n.
If odd-parity is vacuous at n=5, it's not necessarily vacuous at n=9.
Conversely, if it's non-vacuous at n=5, the mechanism found there may generalize.

Let me first check: is the walk structure constraining enough to force even parity?
"""

import sys
from collections import Counter

def check_odd_parity_n5():
    """
    n=5, ms=[2,2,2,3,3], binary at {0,1,2}.
    ri=1. Neighbors: i=0, rri=2.

    Enumerate mover words with:
    1. Locality: mover[k+1] ∈ {mover[k]-1, mover[k], mover[k]+1} mod 5
    2. Binary fire counts even
    3. hfull: all procs fire >= 1
    4. ri fires >= 2, isolated
    5. Some mover outside {0,1,2}

    Check: does any qualifying word have odd parity in its MinFiringGap?
    """
    n = 5
    ri = 1

    results = []

    for L in range(8, 21):
        count = [0, 0, 0]  # [qualifying, odd_parity, odd_no_ec_at_ri]

        # DFS over mover words
        # State: (step, prev_mover, fire_counts, word, ri_last_fire_step)

        def dfs(step, prev, fc, word):
            if step == L:
                # Check cyclic locality
                first = word[0]
                if abs(first - prev) % n > 1 and abs(first - prev) % n < n - 1:
                    return

                # Constraints
                if any(fc[b] % 2 != 0 for b in [0, 1, 2]):
                    return
                if any(fc[p] == 0 for p in range(n)):
                    return
                if fc[ri] < 2:
                    return
                if all(p < 3 for p in word):
                    return

                # Isolated firings of ri
                ri_steps = [k for k in range(L) if word[k] == ri]
                for k in ri_steps:
                    if word[(k+1) % L] == ri:
                        return

                count[0] += 1

                # MinFiringGap
                gaps = []
                for idx in range(len(ri_steps)):
                    a = ri_steps[idx]
                    b = ri_steps[(idx+1) % len(ri_steps)]
                    g = (b - a) % L
                    if g == 0:
                        g = L
                    gaps.append((a, b, g))

                min_g = min(g for _, _, g in gaps)
                if min_g < 2:
                    return

                # Check parity in min gap
                for a, b, g in gaps:
                    if g != min_g:
                        continue
                    lf = 0
                    rf = 0
                    for off in range(1, g):
                        s = (a + off) % L
                        if word[s] == 0:
                            lf += 1
                        if word[s] == 2:
                            rf += 1

                    if lf % 2 != 0 or rf % 2 != 0:
                        count[1] += 1

                        # Check EC at ri
                        pfc = [[0]*(L+1) for _ in range(3)]
                        for k in range(L):
                            for p in range(3):
                                pfc[p][k+1] = pfc[p][k] + (1 if word[k] == p else 0)

                        mctx = set()
                        nctx = set()
                        for k in range(L):
                            c = (pfc[0][k]%2, pfc[1][k]%2, pfc[2][k]%2)
                            if word[k] == ri:
                                mctx.add(c)
                            else:
                                nctx.add(c)

                        if not (mctx & nctx):
                            count[2] += 1
                            if count[2] <= 5:
                                print(f"  ODD, no EC at ri: L={L}, word={list(word)}")
                                print(f"    gap=({a},{b},{g}), Lf={lf}, Rf={rf}")
                                print(f"    mover ctx: {mctx}, nonmover ctx: {nctx}")

                    break  # only check first min gap

                return

            # Pruning
            remaining = L - step
            unfired = sum(1 for p in range(n) if fc[p] == 0)
            if unfired > remaining:
                return

            for next_m in [(prev-1) % n, prev, (prev+1) % n]:
                fc[next_m] += 1
                word.append(next_m)
                dfs(step + 1, next_m, fc, word)
                word.pop()
                fc[next_m] -= 1

        for start in range(n):
            fc = [0] * n
            fc[start] = 1
            dfs(1, start, fc, [start])

        print(f"L={L}: qualifying={count[0]}, odd_parity={count[1]}, "
              f"odd_no_ec_at_ri={count[2]}")
        results.append((L, count[0], count[1], count[2]))

    return results

def check_odd_parity_n7():
    """Same for n=7. Limit lengths more aggressively."""
    n = 7
    ri = 1

    for L in range(10, 17):
        count = [0, 0, 0]

        def dfs(step, prev, fc, word):
            if step == L:
                first = word[0]
                diff = abs(first - prev) % n
                if diff > 1 and diff < n - 1:
                    return
                if any(fc[b] % 2 != 0 for b in [0, 1, 2]):
                    return
                if any(fc[p] == 0 for p in range(n)):
                    return
                if fc[ri] < 2:
                    return
                if all(p < 3 for p in word):
                    return

                ri_steps = [k for k in range(L) if word[k] == ri]
                for k in ri_steps:
                    if word[(k+1) % L] == ri:
                        return

                count[0] += 1

                gaps = []
                for idx in range(len(ri_steps)):
                    a = ri_steps[idx]
                    b = ri_steps[(idx+1) % len(ri_steps)]
                    g = (b - a) % L
                    if g == 0:
                        g = L
                    gaps.append((a, b, g))

                min_g = min(g for _, _, g in gaps)
                if min_g < 2:
                    return

                for a, b, g in gaps:
                    if g != min_g:
                        continue
                    lf = rf = 0
                    for off in range(1, g):
                        s = (a + off) % L
                        if word[s] == 0:
                            lf += 1
                        if word[s] == 2:
                            rf += 1

                    if lf % 2 != 0 or rf % 2 != 0:
                        count[1] += 1

                        pfc = [[0]*(L+1) for _ in range(3)]
                        for k in range(L):
                            for p in range(3):
                                pfc[p][k+1] = pfc[p][k] + (1 if word[k] == p else 0)

                        mctx = set()
                        nctx = set()
                        for k in range(L):
                            c = (pfc[0][k]%2, pfc[1][k]%2, pfc[2][k]%2)
                            if word[k] == ri:
                                mctx.add(c)
                            else:
                                nctx.add(c)

                        if not (mctx & nctx):
                            count[2] += 1
                            if count[2] <= 3:
                                print(f"  ODD, no EC at ri: L={L}, word={list(word)}")
                                print(f"    gap=({a},{b},{g}), Lf={lf}, Rf={rf}")

                    break

                return

            remaining = L - step
            unfired = sum(1 for p in range(n) if fc[p] == 0)
            if unfired > remaining:
                return

            for next_m in [(prev-1) % n, prev, (prev+1) % n]:
                fc[next_m] += 1
                word.append(next_m)
                dfs(step + 1, next_m, fc, word)
                word.pop()
                fc[next_m] -= 1

        for start in range(n):
            fc = [0] * n
            fc[start] = 1
            dfs(1, start, fc, [start])

        print(f"n=7, L={L}: qualifying={count[0]}, odd_parity={count[1]}, "
              f"odd_no_ec_at_ri={count[2]}")

if __name__ == '__main__':
    sys.setrecursionlimit(100000)

    print("=" * 60)
    print("SORRY 5: Odd-parity residual investigation")
    print("=" * 60)

    print("\n--- n=5, ms=[2,2,2,3,3] ---")
    results5 = check_odd_parity_n5()

    total_odd = sum(r[2] for r in results5)
    total_odd_no_ec = sum(r[3] for r in results5)
    print(f"\nTotal odd-parity words (n=5): {total_odd}")
    print(f"Total odd without EC at ri: {total_odd_no_ec}")

    if total_odd == 0:
        print(">>> ODD-PARITY IS VACUOUS at n=5!")
    elif total_odd_no_ec == 0:
        print(">>> ALL odd-parity words have EC at ri at n=5!")
    else:
        print(f">>> {total_odd_no_ec} words need EC elsewhere")

    print("\n--- n=7, ms=[2,2,2,3,3,3,3] ---")
    check_odd_parity_n7()
