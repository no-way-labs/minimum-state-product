#!/usr/bin/env python3
"""
RA13 Part 5: Definitive provider selection rule.

From Parts 1-4 we know:
- Provider exists 100% of the time
- active_fires always = 2 = fc_active (binary neighbor dumps ALL fires in one phase)
- Provider is binary ~90% of the time, but can be non-binary
- The "silent fires = 0" is NOT from pigeonhole (gap often negative)
- (1,1) splits exist at some binary pairs but not all

The theorem we want to prove:

  For any ZW word with >=3 binary, all fc>=2, some fc>=3, sub-threshold product:
  There exists proc t and a phase of t where:
    - One neighbor of t is binary with fires >= 2 (active side)
    - The other neighbor fires 0 (silent side)

APPROACH: Instead of trying to characterize WHICH proc, let me try a COUNTING
argument on the GLOBAL level.

Key observation: the active neighbor is always binary with fc=2, and ALL its
fires fall in one phase. This means: the binary proc b fires 2 times, and both
fires are in the SAME phase of some neighbor t.

For this to work, t must be adjacent to b, and t's firing pattern must "bracket"
both of b's fires (both b-fires between two consecutive t-fires).

Let me check: For EACH binary proc b with fc=2, look at both neighbors.
Is there always a neighbor t where both b-fires fall in one phase of t?

If YES: then t is the provider (with b as active side). We just need the OTHER
side of t to fire 0 in that phase.

Actually, let me approach differently. Let me check the SIMPLEST possible
selection rule:

RULE: Pick any binary proc b with fc_b = 2. Look at both neighbors t1, t2.
For at least one of them, both b-fires fall in one phase. Pick that one as t.
The other neighbor of t is the silent side (fires 0 in that phase).

Is this always true?
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


def b_fires_in_t_phases(word, n, t, b):
    """For proc t with its fire times, count how b's fires distribute across t's phases."""
    L = len(word)
    t_fires = [i for i, x in enumerate(word) if x == t]
    b_fires = [i for i, x in enumerate(word) if x == b]
    fc_t = len(t_fires)
    if fc_t == 0:
        return []
    dist = []
    for idx in range(fc_t):
        start = t_fires[idx]
        end = t_fires[(idx + 1) % fc_t]
        # Count b-fires strictly between start and end
        cnt = 0
        for bf in b_fires:
            pos = (bf - start) % L
            gap = (end - start) % L
            if 0 < pos < gap:
                cnt += 1
        dist.append(cnt)
    return dist


def other_fires_in_phase(word, n, t, active_neighbor, phase_idx):
    """Count fires of the OTHER neighbor (not active) in the given phase of t."""
    L = len(word)
    t_fires = [i for i, x in enumerate(word) if x == t]
    fc_t = len(t_fires)

    left_t = (t - 1) % n
    right_t = (t + 1) % n
    silent_neighbor = left_t if active_neighbor == right_t else right_t

    start = t_fires[(phase_idx - 1) % fc_t]
    end = t_fires[phase_idx]

    cnt = 0
    s = (start + 1) % L
    while s != end:
        if word[s] == silent_neighbor:
            cnt += 1
        s = (s + 1) % L
    return cnt, silent_neighbor


def main():
    print("RA13 Part 5: Definitive Provider Rule")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total_words = 0

        # Strategy A: For each binary b, look at each neighbor t.
        # Check if all of b's fires fall in one phase of t.
        # If yes AND other side fires 0 in that phase: provider found.
        strat_a_success = 0
        strat_a_fail = 0

        # When A fails: is there STILL a provider via the general search?
        general_provider_found = 0
        truly_no_provider = 0

        # Track: for the provider (t), is t the fc>=3 proc?
        provider_is_binary = 0
        provider_is_nonbinary = 0

        # Key: does active_fires always = fc_active?
        af_equals_fc = 0
        af_less_fc = 0

        # Track which fc_t values work
        fc_t_dist = Counter()

        # The crucial question: does the BOUNDARY binary (at edge of binary run)
        # always work?
        boundary_binary_works = 0
        boundary_binary_fails = 0

        fail_examples = []

        for sorted_ms in sorted_multisets:
            if time.time() - t0 > 300 and n == 9:
                print(f"  TIME LIMIT at {time.time()-t0:.0f}s")
                break
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
                        L = len(w)
                        total_words += 1

                        # Find ALL binary procs
                        binary_procs = [p for p in range(n) if ms[p] == 2]

                        # Strategy A: for each binary b, check each neighbor
                        found_provider = False
                        for b in binary_procs:
                            if fc[b] != 2:
                                continue
                            for t in [(b - 1) % n, (b + 1) % n]:
                                if fc[t] < 2:
                                    continue
                                dist = b_fires_in_t_phases(w, n, t, b)
                                # Find a phase with ALL of b's fires (= fc[b])
                                for pi, cnt in enumerate(dist):
                                    if cnt == fc[b]:
                                        # Check silent side
                                        silent_cnt, silent_p = other_fires_in_phase(w, n, t, b, pi)
                                        if silent_cnt == 0:
                                            found_provider = True
                                            if ms[t] == 2:
                                                provider_is_binary += 1
                                            else:
                                                provider_is_nonbinary += 1
                                            fc_t_dist[fc[t]] += 1
                                            af_equals_fc += 1

                                            # Is t at boundary of binary run?
                                            other_side = (t - 1) % n if b == (t + 1) % n else (t + 1) % n
                                            if ms[other_side] != 2 or ms[t] != 2:
                                                boundary_binary_works += 1
                                            break
                                    elif cnt > 0 and cnt < fc[b]:
                                        af_less_fc += 1
                                if found_provider:
                                    break
                            if found_provider:
                                break

                        if found_provider:
                            strat_a_success += 1
                        else:
                            strat_a_fail += 1
                            # General search
                            gen_found = False
                            for p in range(n):
                                if fc[p] < 2:
                                    continue
                                left_p = (p - 1) % n
                                right_p = (p + 1) % n
                                fire_steps = [i for i, x in enumerate(w) if x == p]
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
                                    if J == 0 and K >= 2 and ms[right_p] == 2:
                                        gen_found = True
                                        break
                                    if K == 0 and J >= 2 and ms[left_p] == 2:
                                        gen_found = True
                                        break
                                if gen_found:
                                    break
                            if gen_found:
                                general_provider_found += 1
                            else:
                                truly_no_provider += 1
                                if len(fail_examples) < 5:
                                    fail_examples.append({
                                        'ms': list(ms), 'word': list(w), 'fc': list(fc)
                                    })

        elapsed = time.time() - t0
        print(f"  ({elapsed:.1f}s)")
        print(f"\n  Total ZW words: {total_words}")
        print(f"  Strategy A (binary-centric) success: {strat_a_success} ({100*strat_a_success/max(1,total_words):.1f}%)")
        print(f"  Strategy A fail: {strat_a_fail}")
        print(f"    -> General search found: {general_provider_found}")
        print(f"    -> Truly no provider: {truly_no_provider}")

        print(f"\n  Provider is binary (m_t=2): {provider_is_binary}")
        print(f"  Provider is non-binary: {provider_is_nonbinary}")

        print(f"\n  active_fires = fc_active: {af_equals_fc}")
        print(f"  active_fires < fc_active: {af_less_fc}")

        print(f"\n  fc_t distribution: {dict(fc_t_dist.most_common())}")

        print(f"\n  Boundary binary works: {boundary_binary_works}")
        print(f"  Boundary binary fails (interior): {provider_is_binary + provider_is_nonbinary - boundary_binary_works}")

        if fail_examples:
            print(f"\n  FAIL EXAMPLES:")
            for ex in fail_examples:
                print(f"    ms={ex['ms']}, fc={ex['fc']}, word={ex['word']}")


if __name__ == "__main__":
    main()
