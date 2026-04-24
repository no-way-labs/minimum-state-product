#!/usr/bin/env python3
"""
RA12: Analyze WHY asymmetric placements have no min-length walks.

For a ring walk of length L on n procs, starting at P_s:
- Each step moves +1 or -1 on the ring.
- fc[p] = number of times P_p appears in the walk.
- For a valid good cycle: each fc[p] is a multiple of ms[p].
- Wrap-adjacency: word[L-1] and word[0] are ring-adjacent.

Key constraint: the walk visits specific procs specific numbers of times.
The walk is a path on Z_n that returns near its start.

For a walk starting at s with displacement d = word[L-1] - word[0],
the positions visited are s, s+d_1, s+d_1+d_2, ... where each d_i = +/-1.
The position at step t is: s + sum(d_1..d_t).

The number of times proc p is visited equals the number of t where
s + sum(d_1..d_t) = p (mod n).

This is a combinatorial constraint. Let me check if there's a parity
or residue obstruction.
"""

import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def check_walk_existence(n, ms):
    """Check if min-length walks exist by trying all starting positions."""
    total_len = sum(ms)
    found = 0

    for p0 in range(n):
        count = [0]

        def dfs(path, fc):
            if count[0] > 0:
                return  # just need existence
            pos = path[-1]
            step = len(path)
            if step == total_len:
                nxt = path[0]
                if abs(pos - nxt) % n in (1, n - 1):
                    if all(fc[p] == ms[p] for p in range(n)):
                        count[0] += 1
                return
            remaining = total_len - step
            needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
            if needed > remaining:
                return
            for d in [1, -1]:
                nxt = (pos + d) % n
                if fc[nxt] < ms[nxt]:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs(path, fc)
                    path.pop()
                    fc[nxt] -= 1

        fc = [0] * n
        fc[p0] = 1
        dfs([p0], fc)
        if count[0] > 0:
            found += 1

    return found


def analyze_parity(n, ms):
    """Analyze the parity structure of the walk.

    Consider a walk of length L. At each step, the walker is at some
    position. The position has a parity (even/odd).

    If the walk has L steps, starting at position p0:
    - After step 1: p0 +/- 1 (different parity from p0)
    - After step 2: p0, p0+2, p0-2 (same parity as p0)
    - ...
    - After step t: same parity as p0 iff t is even.

    So the positions at even steps have the same parity as p0,
    and positions at odd steps have opposite parity.

    For fc[p] = ms[p], we need:
    - Number of even-step visits to p = number of odd-step visits to p
      ... not exactly, but they must sum to ms[p].

    Let E = set of procs with same parity as p0.
    Let O = set of procs with different parity from p0.

    At even steps (including step 0), walker is in E.
    At odd steps, walker is in O.
    Total even steps: ceil(L/2) or floor(L/2)+1.
    Total odd steps: floor(L/2).

    For L=24: 13 even-step positions (steps 0,2,...,22,24 but 24 wraps),
    actually step 0 counts, steps 1..23 complete the walk.
    Wait, the walk has L=24 positions: word[0]..word[23].
    word[0] is at step 0 (even), word[1] at step 1 (odd), etc.

    Positions at even indices: word[0], word[2], ..., word[22] = 12 positions.
    These must all have same parity as word[0].
    Positions at odd indices: word[1], word[3], ..., word[23] = 12 positions.
    These must all have different parity from word[0].

    So: sum of fc[p] for p with same parity as p0 = 12
    And: sum of fc[p] for p with different parity from p0 = 12.
    """
    L = sum(ms)
    even_count = L // 2  # positions at even indices
    odd_count = L - even_count  # positions at odd indices

    print(f"  L={L}, even_indices={even_count}, odd_indices={odd_count}")

    # For each starting parity:
    for start_parity in [0, 1]:
        even_procs = [p for p in range(n) if p % 2 == start_parity]
        odd_procs = [p for p in range(n) if p % 2 != start_parity]

        sum_even = sum(ms[p] for p in even_procs)
        sum_odd = sum(ms[p] for p in odd_procs)

        # Positions at even indices must be in even_procs.
        # Positions at odd indices must be in odd_procs.
        # So sum of fc for even_procs = even_count = 12.
        # And sum of fc for odd_procs = odd_count = 12.

        print(f"  Start parity {start_parity}:")
        print(f"    Even procs {even_procs}: need total fc = {even_count}, "
              f"actual sum(ms) = {sum_even}")
        print(f"    Odd procs {odd_procs}: need total fc = {odd_count}, "
              f"actual sum(ms) = {sum_odd}")

        if sum_even == even_count and sum_odd == odd_count:
            print(f"    => FEASIBLE")
        else:
            print(f"    => INFEASIBLE ({sum_even} != {even_count} or "
                  f"{sum_odd} != {odd_count})")


def main():
    n = 9
    threshold = 4 * (3 ** 7)

    print("=" * 70)
    print("RA12: Parity analysis of walk existence")
    print("=" * 70)

    placements = [
        ((0, 2, 4), "(2,2,5)"),
        ((0, 2, 5), "(2,3,4)"),
        ((0, 2, 6), "(2,4,3)"),
        ((0, 3, 6), "(3,3,3)"),
    ]

    for pos, label in placements:
        ms = make_ms(n, pos)
        print(f"\nPlacement {label}: pos={pos}, ms={ms}")
        analyze_parity(n, ms)

    # The key insight: for a ring walk, positions at step t have parity
    # (start_position + t) % 2 (since each step changes parity).
    # So positions at even steps have start parity, odd steps have opposite.
    # fc[p] counts how many times p appears = (appearances at even steps) +
    #   (appearances at odd steps).
    # But appearances at even steps are 0 if p has wrong parity for even steps!
    # Wait, no -- p appears at step t only if the walker is at p at step t.
    # The walker at step t is at some position with parity (p0 + t) % 2.
    # So if p has parity (p0 + t) % 2, p CAN be visited at step t.
    # But p can ONLY be visited at steps with the right parity.
    # This means: fc[p] counts only from steps where t has same parity as
    # (p - p0) mod 2.

    # For n=9 (odd):
    # If p0 is even, even-step procs = {0,2,4,6,8}, odd-step procs = {1,3,5,7}
    # 12 even steps must all visit even procs, 12 odd steps must all visit odd procs.
    # Total even-proc visits = 12, total odd-proc visits = 12.

    # For (3,3,3): ms=[2,3,3,2,3,3,2,3,3], binary at {0,3,6}
    # Even procs: {0,2,4,6,8}, ms = [2,3,3,3,3] -> sum = 14
    # Odd procs: {1,3,5,7}, ms = [3,2,3,3] -> sum = 11
    # But we need: even visits = 12, odd visits = 12.
    # Hmm, 14 != 12 and 11 != 12. But (3,3,3) HAS walks!

    # Wait, I made an error. The parity of which procs can be visited
    # depends on the starting proc AND n being even or odd.

    # For n odd (n=9): moving +1 or -1 always changes position mod 2.
    # So at step t, position parity = (p0 + t) mod 2.
    # fc[p] only counts steps where (p0 + t) mod 2 = p mod 2,
    # i.e., t mod 2 = (p - p0) mod 2.

    # For p0=0 (even):
    #   Even procs visited at even steps: 12 visits among {0,2,4,6,8}
    #   Odd procs visited at odd steps: 12 visits among {1,3,5,7}
    #   Need: sum(ms[p] for p even) = 12 and sum(ms[p] for p odd) = 12.

    # But for (3,3,3) with p0=0:
    #   Even procs {0,2,4,6,8}: ms = [2,3,3,2,3] = 13
    #   Odd procs {1,3,5,7}: ms = [3,2,3,3] = 11
    #   13 != 12 and 11 != 12 -> IMPOSSIBLE starting at P0?!

    # But we found 68 walks! Let me re-examine...

    # Ah wait, for n=9, the walk doesn't strictly alternate parity.
    # n=9 is ODD. Moving from pos p to p+1: new parity is (p+1)%2 = 1-p%2.
    # Moving from p to p-1 (= p+8 mod 9): new parity is (p+8)%2 = p%2.
    # WAIT: (p-1) mod 9 has parity (p-1)%2 = 1 - p%2. Same as +1.
    # So every step DOES flip parity. The analysis holds.

    # But then how does (3,3,3) have walks?
    # Let me recount. ms = [2,3,3,2,3,3,2,3,3] for binary at 0,3,6.

    print(f"\n{'='*70}")
    print("DETAILED PARITY CHECK for (3,3,3)")
    print(f"{'='*70}")

    ms_sym = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    for p0 in range(n):
        even_need = 0
        odd_need = 0
        for p in range(n):
            if (p - p0) % 2 == 0:
                even_need += ms_sym[p]
            else:
                odd_need += ms_sym[p]
        L = sum(ms_sym)  # 24
        even_steps = (L + 1) // 2  # 12 (steps 0,2,...,22)
        odd_steps = L // 2  # 12 (steps 1,3,...,23)

        feasible = (even_need == even_steps and odd_need == odd_steps)
        if feasible:
            print(f"  p0={p0}: even_need={even_need}, odd_need={odd_need} -> FEASIBLE")
        else:
            print(f"  p0={p0}: even_need={even_need}, odd_need={odd_need} -> INFEASIBLE")

    print(f"\nDETAILED PARITY CHECK for (2,2,5)")
    ms_asym = [2, 3, 2, 3, 2, 3, 3, 3, 3]
    for p0 in range(n):
        even_need = 0
        odd_need = 0
        for p in range(n):
            if (p - p0) % 2 == 0:
                even_need += ms_asym[p]
            else:
                odd_need += ms_asym[p]
        L = sum(ms_asym)
        even_steps = (L + 1) // 2  # 12
        odd_steps = L // 2  # 12
        feasible = (even_need == even_steps and odd_need == odd_steps)
        if feasible:
            print(f"  p0={p0}: even_need={even_need}, odd_need={odd_need} -> FEASIBLE")

    # Also check if walks with fc = 2*ms exist (length 48)
    print(f"\n{'='*70}")
    print("DOUBLE-LENGTH WALKS (fc = 2*ms)")
    print(f"{'='*70}")

    for pos, label in placements[:3]:  # asymmetric only
        ms = make_ms(n, pos)
        target_fc = [2 * ms[p] for p in range(n)]
        L = sum(target_fc)
        print(f"\n{label}: ms={ms}, L={L}")

        for p0 in range(n):
            even_need = 0
            odd_need = 0
            for p in range(n):
                if (p - p0) % 2 == 0:
                    even_need += target_fc[p]
                else:
                    odd_need += target_fc[p]
            even_steps = (L + 1) // 2  # 24
            odd_steps = L // 2  # 24
            feasible = (even_need == even_steps and odd_need == odd_steps)
            if feasible:
                print(f"  p0={p0}: FEASIBLE at L={L}")

    # Check fc = 3*ms (length 72)
    print(f"\nTRIPLE-LENGTH WALKS (fc = 3*ms)")
    for pos, label in placements[:3]:
        ms = make_ms(n, pos)
        target_fc = [3 * ms[p] for p in range(n)]
        L = sum(target_fc)
        feasible_any = False
        for p0 in range(n):
            even_need = sum(target_fc[p] for p in range(n) if (p - p0) % 2 == 0)
            odd_need = sum(target_fc[p] for p in range(n) if (p - p0) % 2 != 0)
            even_steps = (L + 1) // 2
            odd_steps = L // 2
            if even_need == even_steps and odd_need == odd_steps:
                feasible_any = True
                break
        print(f"  {label}: L={L}, feasible={feasible_any}")


if __name__ == "__main__":
    main()
