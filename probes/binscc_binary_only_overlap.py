#!/usr/bin/env python3
"""binscc_binary_only_overlap.py — Binary-only overlap is TF-independent.

CRITICAL INSIGHT: When binary processor P fires, S → 1-S (flip) regardless
of the transition function. So binary states in any cycle are determined
solely by the mover word.

BUT: binary processor contexts (L, S, R) include neighbor states. If a
neighbor is non-binary, its states depend on the transition function.
So binary overlap at NON-CONSECUTIVE binary is NOT TF-independent.

For CONSECUTIVE binary P_{i-1}, P_i, P_{i+1}: all three context components
are binary, so P_i's overlap is TF-independent → UBO works unconditionally.

For NON-CONSECUTIVE binary: only S is fixed, L and R may vary.

HOWEVER: The binary STATE component (S ∈ {0,1}) IS fixed. We can check
a weaker condition: "S-overlap" — same (L, S, R) with same S as mover
and nonmover. If S_mover ≠ S_nonmover, there's no conflict even with
overlap. But binary always flips, so mover entry is (L, S, R) → 1-S.
If nonmover has (L, S, R) → S, then S ≠ 1-S, giving conflict.

Wait — the point is that L and R vary with TF, so the SAME mover word
produces DIFFERENT contexts at binary P depending on TF of non-binary neighbors.

Let me quantify: for each mover word, what's the range of possible binary
overlap outcomes as non-binary TFs vary?
"""

from itertools import product as iproduct
from collections import Counter
import sys
import time


def enumerate_mover_words_smart(ms, n, max_length):
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]
    results = []
    start_config = tuple(0 for _ in range(n))
    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return
        if len(word) >= sum(ms) and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fire_counts[p]) for p in range(n)
                     if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(current_config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1
            word.append(nxt)
            dfs(word, new_counts, new_config)
            word.pop()
    for p in range(n):
        first = list(start_config)
        first[p] = (first[p] + 1) % ms[p]
        first = tuple(first)
        dfs([p], [1 if i == p else 0 for i in range(n)], first)
    return results


def check_binary_overlap_binary_component(ms, n, mover_word):
    """Check overlap considering only that binary S is determined by mover word.

    For binary processor P at position p:
    - S at step i = (number of times P fired in steps 0..i-1) mod 2
    - This is fixed regardless of TF

    Mover steps for P: the set of i where mover_word[i] = p
    S_mover = {S_i : mover_word[i] = p} — the set of binary states when P fires
    S_nonmover = {S_i : mover_word[i] ≠ p} — the set of binary states when P doesn't

    If S_mover ∩ S_nonmover = ∅ → no overlap possible at P (regardless of L, R)
    If S_mover ∩ S_nonmover ≠ ∅ → overlap MIGHT exist (depends on L, R)
    """
    ell = len(mover_word)

    # Compute binary states (fixed by mover word)
    fire_counts = [0] * n
    states = []
    for i in range(ell):
        # Binary state at position p before step i
        s = {}
        for p in range(n):
            if ms[p] == 2:
                s[p] = fire_counts[p] % 2
        states.append(s)
        fire_counts[mover_word[i]] += 1

    # Check S-overlap at each binary processor
    for p in range(n):
        if ms[p] != 2:
            continue
        s_mover = set()
        s_nonmover = set()
        for i in range(ell):
            if mover_word[i] == p:
                s_mover.add(states[i][p])
            else:
                s_nonmover.add(states[i][p])

        # If both 0 and 1 appear in mover AND nonmover, then for any TF,
        # some (L, S, R) will have the same S in both roles.
        # But we need the same FULL context (L, S, R), not just S.
        if s_mover & s_nonmover:
            pass  # potential overlap, but not guaranteed

    # Check if ALL binary processors have S-disjoint mover/nonmover
    all_s_disjoint = True
    for p in range(n):
        if ms[p] != 2:
            continue
        s_mover = set()
        s_nonmover = set()
        for i in range(ell):
            if mover_word[i] == p:
                s_mover.add(states[i][p])
            else:
                s_nonmover.add(states[i][p])
        if s_mover & s_nonmover:
            all_s_disjoint = False
            break

    return all_s_disjoint


def check_overlap_incrementing(ms, n, mover_word):
    """Standard overlap check with incrementing transitions."""
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None, None
    if len(set(configs[:ell])) != ell:
        return None, None

    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return None, None
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return None, None

    # Check overlap at binary procs only
    bin_overlap = False
    for p in range(n):
        if ms[p] != 2:
            continue
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(ell):
            c = configs[i]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover_word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            bin_overlap = True
            break

    # Check overlap at all procs
    all_overlap = False
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(ell):
            c = configs[i]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover_word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            all_overlap = True
            break

    return bin_overlap, all_overlap


def main():
    print("=" * 70)
    print("BINARY S-COMPONENT OVERLAP ANALYSIS")
    print("=" * 70)
    print("""
For binary P at position p:
  S at step i = (fire count of P up to i) mod 2  [FIXED by mover word]
  L, R = neighbor states [VARY with non-binary TF]

S-disjoint: S_mover ∩ S_nonmover = ∅
  → NO overlap possible at P, regardless of TF
S-overlap: same S value appears in both mover and nonmover steps
  → overlap MIGHT exist, depends on what L,R values co-occur
""")

    for n in [5, 6]:
        print(f"\n{'='*60}")
        print(f"n={n}")
        print("="*60)

        # Pure {2,3}
        ms_base = [2, 2, 2] + [3] * (n - 3)
        seen = set()
        non_consec = []
        for perm in set(__import__('itertools').permutations(tuple(sorted(ms_base)))):
            has_3c = False
            for i in range(n):
                if perm[i] == 2 and perm[(i+1)%n] == 2 and perm[(i+2)%n] == 2:
                    has_3c = True
                    break
            if has_3c:
                continue
            rots = [perm[i:] + perm[:i] for i in range(n)]
            refl = perm[::-1]
            ref_rots = [refl[i:] + refl[:i] for i in range(n)]
            canon = min(rots + ref_rots)
            if canon not in seen:
                seen.add(canon)
                non_consec.append(canon)

        print(f"\n--- Pure {{2,3}}: {len(non_consec)} non-consec orientations ---")

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            max_len = 3 * n + 4
            words = enumerate_mover_words_smart(ms, n, max_len)

            total = 0
            s_disjoint = 0  # NO possible binary overlap
            bin_inc_overlap = 0  # binary overlap with incrementing
            nonbin_inc_overlap = 0  # no binary overlap but non-binary overlap with incrementing
            no_inc_overlap = 0  # no overlap at all with incrementing

            for word in words:
                result = check_overlap_incrementing(ms, n, word)
                if result[0] is None:
                    continue
                total += 1
                bin_ov, all_ov = result

                s_disj = check_binary_overlap_binary_component(ms, n, word)

                if bin_ov:
                    bin_inc_overlap += 1
                elif all_ov:
                    nonbin_inc_overlap += 1
                else:
                    no_inc_overlap += 1

                if s_disj:
                    s_disjoint += 1

            print(f"  ms={ms_tuple}: {total} valid cycles")
            print(f"    Binary overlap (incrementing): {bin_inc_overlap}")
            print(f"    Non-binary only overlap (inc): {nonbin_inc_overlap}")
            print(f"    No overlap (incrementing):     {no_inc_overlap}")
            print(f"    S-disjoint (TF-independent):   {s_disjoint}")
            print(f"    S-overlapping at all binary:   {total - s_disjoint}")
            sys.stdout.flush()

        # Mixed {2,3,4}
        ms_base = [2, 2, 2, 4] + [3] * (n - 4)
        seen = set()
        non_consec_m = []
        for perm in set(__import__('itertools').permutations(tuple(sorted(ms_base)))):
            has_3c = False
            for i in range(n):
                if perm[i] == 2 and perm[(i+1)%n] == 2 and perm[(i+2)%n] == 2:
                    has_3c = True
                    break
            if has_3c:
                continue
            rots = [perm[i:] + perm[:i] for i in range(n)]
            refl = perm[::-1]
            ref_rots = [refl[i:] + refl[:i] for i in range(n)]
            canon = min(rots + ref_rots)
            if canon not in seen:
                seen.add(canon)
                non_consec_m.append(canon)

        print(f"\n--- Mixed {{2,3,4}}: {len(non_consec_m)} non-consec orientations ---")

        for ms_tuple in non_consec_m:
            ms = list(ms_tuple)
            max_len = 3 * n + 4
            words = enumerate_mover_words_smart(ms, n, max_len)

            total = 0
            s_disjoint = 0
            bin_inc_overlap = 0
            nonbin_inc_overlap = 0
            no_inc_overlap = 0

            for word in words:
                result = check_overlap_incrementing(ms, n, word)
                if result[0] is None:
                    continue
                total += 1
                bin_ov, all_ov = result

                s_disj = check_binary_overlap_binary_component(ms, n, word)

                if bin_ov:
                    bin_inc_overlap += 1
                elif all_ov:
                    nonbin_inc_overlap += 1
                else:
                    no_inc_overlap += 1

                if s_disj:
                    s_disjoint += 1

            print(f"  ms={ms_tuple}: {total} valid cycles")
            print(f"    Binary overlap (incrementing): {bin_inc_overlap}")
            print(f"    Non-binary only overlap (inc): {nonbin_inc_overlap}")
            print(f"    No overlap (incrementing):     {no_inc_overlap}")
            print(f"    S-disjoint (TF-independent):   {s_disjoint}")
            sys.stdout.flush()


if __name__ == "__main__":
    main()
