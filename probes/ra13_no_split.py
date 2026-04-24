#!/usr/bin/env python3
"""
RA13 Part 3: Why binary neighbor fires can't split (1,1) across t's two phases.

When t is binary (fc=2) with binary neighbor b (fc=2):
- Between t-fire-1 and t-fire-2: b fires J times
- Between t-fire-2 and t-fire-1: b fires 2-J times
- We observe J in {0, 2}, never J=1.

WHY? Let's prove this structurally.

Walk constraint: the walk moves on a ring Z_n. At each step it moves +1 or -1.
The walk visits t exactly twice (positions where word[i]=t).
The walk visits b exactly twice (positions where word[i]=b).
b is adjacent to t: b = t+1 or b = t-1.

CLAIM: If both t and b are binary (fc=2) and adjacent, then in any ring walk,
b's two fires are in the SAME phase of t (not split across phases).

PROOF ATTEMPT:
Consider b = t+1 (WLOG). The walk is at position t at times s1, s2.
Between s1 and s2, the walk visits b either 0 or 2 times.

Key observation: The walk visits procs in ORDER along the ring. To go from t
to any proc p > t+1 (beyond b), the walk MUST pass through b. Similarly,
to return from p to t, it must pass through b again.

So if the walk visits ANY proc beyond b in one phase, it visits b at least twice
in that phase. Since b fires only 2 total, the other phase gets 0 b-fires.

If the walk visits NO proc beyond b in one phase: it stays in {t-1, t-2, ...}
(the other side). Then b fires 0 in that phase, 2 in the other.

The only way to get b firing exactly 1 time in a phase: the walk goes from t
to b in one phase, then from b ... doesn't return through b before t fires again.
But: if the walk is at b, to get back to t it goes b -> t (1 step). So the walk
could go: t -> b -> t. That uses 1 b-fire and then t fires (using 1 t-fire).

Wait, that seems possible! t -> b -> t is: fire t, fire b, fire t. Between
t-fire-1 and t-fire-2, b fires once. Between t-fire-2 and t-fire-1 (wrap), b
fires once. That's (1,1)!

But does this happen in our constrained setting? Let me check: does the
walk constraint + ZW + fc>=3 somewhere PREVENT the (1,1) pattern?

Let me look directly: when t is binary with binary neighbor b, can we have
the walk go t,b,t,...,b,...? (i.e., tbXXbXXt interleaving)

Actually wait. The walk goes: ..., t, b, ..., t, ..., b, ...
This means between t-fire-1 and t-fire-2: b fires once (the b right after t-fire-1).
Between t-fire-2 and t-fire-1: b fires once (the b after some wandering).

For this to happen: after firing b (adjacent to t), the walk must go AWAY from t
(to t+2, t+3, ...) and then come back to t for t-fire-2. Then after t-fire-2,
go away from b, eventually get to b again, and cycle back.

IS THIS ACTUALLY IMPOSSIBLE for ZW cycles with >=3 binary and sub-threshold product?

Let me check computationally: are there ANY ring walks (ignoring good-cycle constraints)
where t and b are adjacent binary procs with (1,1) interleaving?
"""

import time
from itertools import permutations
from collections import Counter


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
    return cw, ccw


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1:
                return
            if any(f < 2 for f in fc):
                return
            if all(f <= 2 for f in fc):
                return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw:
                return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining:
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2:
                continue
            if fc[nxt] >= 2 * ms[nxt]:
                continue
            fc[nxt] += 1
            path.append(nxt)
            dfs(path, fc)
            path.pop()
            fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in results:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def generate_subthreshold_multisets(n, threshold):
    results = []
    max_state = min(threshold // (2 ** (n - 1)) + 1, 10)
    def gen(pos, min_val, current, prod):
        if pos == n:
            if prod < threshold:
                num_bin = sum(1 for m in current if m == 2)
                if num_bin >= 3:
                    results.append(tuple(current))
            return
        remaining = n - pos
        for m in range(max(2, min_val), max_state + 1):
            new_prod = prod * m
            if new_prod >= threshold:
                break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2:
                    break
            gen(pos + 1, m, current + [m], new_prod)
    gen(0, 2, [], 1)
    return results


def get_all_ring_placements(sorted_ms, n):
    seen = set()
    results = []
    for perm in set(permutations(sorted_ms)):
        best = perm
        for i in range(n):
            rot = perm[i:] + perm[:i]
            if rot < best:
                best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best:
                best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def check_split_interleaving(word, n, ms):
    """Check if ANY pair of adjacent binary procs have (1,1) interleaving."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    for t in range(n):
        if ms[t] != 2 or fc[t] != 2:
            continue
        for b in [(t-1) % n, (t+1) % n]:
            if ms[b] != 2 or fc[b] != 2:
                continue
            # Check interleaving
            t_fires = [i for i, x in enumerate(word) if x == t]
            b_fires = [i for i, x in enumerate(word) if x == b]
            if len(t_fires) != 2 or len(b_fires) != 2:
                continue
            t0, t1 = t_fires
            # Count b-fires between t0 and t1
            b_between = 0
            for bf in b_fires:
                # bf is between t0 and t1 if (bf - t0) % L is in (0, gap)
                gap = (t1 - t0) % L
                pos = (bf - t0) % L
                if 0 < pos < gap:
                    b_between += 1
            if b_between == 1:
                return True, t, b
    return False, None, None


def main():
    print("RA13 Part 3: (1,1) Split Investigation")
    print("=" * 70)

    total_words = 0
    split_words = 0
    split_examples = []

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        for sorted_ms in sorted_multisets:
            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                max_len = min(sum(ms), 4 * n)
                min_len = 2 * n + 1
                for cycle_len in range(min_len, max_len + 1):
                    walks = _enumerate_walks_dfs(n, cycle_len, ms)
                    for w in walks:
                        total_words += 1
                        has_split, t, b = check_split_interleaving(w, n, ms)
                        if has_split:
                            split_words += 1
                            if len(split_examples) < 10:
                                fc = [0] * n
                                for p in w:
                                    fc[p] += 1
                                split_examples.append({
                                    'n': n, 'ms': list(ms), 'word': list(w),
                                    'fc': list(fc), 't': t, 'b': b
                                })

    print(f"\n  Total ZW words: {total_words}")
    print(f"  Words with (1,1) split: {split_words}")
    if split_examples:
        print(f"\n  SPLIT EXAMPLES (unexpectedly exist):")
        for ex in split_examples:
            print(f"    n={ex['n']}, ms={ex['ms']}, t={ex['t']}, b={ex['b']}")
            print(f"    word={ex['word']}, fc={ex['fc']}")
    else:
        print(f"\n  NO (1,1) SPLITS FOUND — confirms universal (0,2)/(2,0) pattern")

    # Part B: Now look at the ACTUAL provider selection more carefully.
    # The provider doesn't need to be binary. It needs:
    # - Some phase with J=0 and K>=2 and binary active neighbor
    # - OR K=0 and J>=2 and binary active neighbor
    # This can be ANY proc, not just binary.
    #
    # For non-binary t (fc_t >= 3): t has >= 3 phases.
    # Binary neighbor b has fc_b = 2 fires across >= 3 phases.
    # By pigeonhole: at least fc_t - fc_b >= 1 phases have 0 b-fires.
    # But we need a phase with 0 on one side and >= 2 on the other.
    # That's harder.
    #
    # Actually, the dominant case is t binary. Let me check: when t is non-binary,
    # what's the mechanism?

    print("\n\n" + "=" * 70)
    print("Part B: Non-binary provider mechanism")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        nb_count = 0
        nb_mechanism = Counter()

        for sorted_ms in sorted_multisets:
            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                max_len = min(sum(ms), 4 * n)
                min_len = 2 * n + 1
                for cycle_len in range(min_len, max_len + 1):
                    walks = _enumerate_walks_dfs(n, cycle_len, ms)
                    for w in walks:
                        fc = [0] * n
                        for p in w:
                            fc[p] += 1

                        # Find first binary provider
                        found_binary_prov = False
                        for p in range(n):
                            if fc[p] < 2 or ms[p] != 2:
                                continue
                            left_p = (p - 1) % n
                            right_p = (p + 1) % n
                            L = len(w)
                            fire_steps = [t for t in range(L) if w[t] == p]
                            phases_lr = []
                            for idx in range(len(fire_steps)):
                                s = fire_steps[idx]
                                a = fire_steps[(idx - 1) % len(fire_steps)]
                                J = K = 0
                                t_step = (a + 1) % L
                                while t_step != s:
                                    if w[t_step] == left_p:
                                        J += 1
                                    if w[t_step] == right_p:
                                        K += 1
                                    t_step = (t_step + 1) % L
                                phases_lr.append((J, K))
                            for J, K in phases_lr:
                                if J == 0 and K >= 2 and ms[right_p] == 2:
                                    found_binary_prov = True
                                    break
                                if K == 0 and J >= 2 and ms[left_p] == 2:
                                    found_binary_prov = True
                                    break
                            if found_binary_prov:
                                break

                        if not found_binary_prov:
                            # Must use non-binary provider
                            nb_count += 1
                            # Find it
                            for p in range(n):
                                if fc[p] < 2:
                                    continue
                                left_p = (p - 1) % n
                                right_p = (p + 1) % n
                                L = len(w)
                                fire_steps = [t for t in range(L) if w[t] == p]
                                phases_lr = []
                                for idx in range(len(fire_steps)):
                                    s = fire_steps[idx]
                                    a = fire_steps[(idx - 1) % len(fire_steps)]
                                    J = K = 0
                                    t_step = (a + 1) % L
                                    while t_step != s:
                                        if w[t_step] == left_p:
                                            J += 1
                                        if w[t_step] == right_p:
                                            K += 1
                                        t_step = (t_step + 1) % L
                                    phases_lr.append((J, K))
                                found = False
                                for J, K in phases_lr:
                                    if J == 0 and K >= 2 and ms[right_p] == 2:
                                        nb_mechanism[(ms[p], fc[p], ms[left_p], fc[left_p],
                                                       ms[right_p], fc[right_p], K)] += 1
                                        found = True
                                        break
                                    if K == 0 and J >= 2 and ms[left_p] == 2:
                                        nb_mechanism[(ms[p], fc[p], ms[right_p], fc[right_p],
                                                       ms[left_p], fc[left_p], J)] += 1
                                        found = True
                                        break
                                if found:
                                    break

        print(f"  Words needing non-binary provider: {nb_count}")
        for mech, cnt in nb_mechanism.most_common(10):
            print(f"    (m_t, fc_t, m_silent, fc_silent, m_active, fc_active, active_fires) = {mech}: {cnt}")

    # Part C: Can we ALWAYS find a binary provider? Or do some words require
    # non-binary providers?
    print("\n\n" + "=" * 70)
    print("SUMMARY: Provider Selection Rule")
    print("=" * 70)


if __name__ == "__main__":
    main()
