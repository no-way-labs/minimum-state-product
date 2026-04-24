#!/usr/bin/env python3
"""
RA13 Part 2: WHY do the binary active neighbor's fires cluster?

Key finding from Part 1:
- Provider t typically has fc_t=2, m_t=2 (binary, fires exactly 2 times)
- Active neighbor b is binary, fc_b=2
- ALL of b's fires (=2) land in ONE of t's 2 phases
- Silent neighbor s fires 0 in that same phase

So t has 2 phases. b fires 2 times. Both b-fires land in one phase.
This means: between t's 1st and 2nd firing, b fires 2 times AND s fires 0.

WHY? This is about the walk structure on the ring.

Key insight: t and b are ADJACENT (b is t's neighbor). If the walk is at t,
it must go to t-1 or t+1 next. If it goes to b, then b fires. For b to fire
twice before t fires again, the walk must go t -> b -> ... -> b -> t.

Let me investigate:
1. The walk segment between t's two firings
2. Why b fires 2 times in one segment and 0 in the other
3. What makes the silent side silent

Also: the critical question is whether this is a CONSEQUENCE of the
walk being on a ring with specific structural constraints, or just an
empirical observation.

HYPOTHESIS: When t is binary (fc=2) with a binary neighbor b (fc=2),
the walk between t's firings must visit b. Since the walk is a ring walk,
between two consecutive fires of t, the walk goes "out" from t toward b
and comes back. If it goes far enough to visit b twice (there and back),
b fires 2 in that segment. The other segment gets 0 b-fires.

Let me verify and characterize the walk segments.
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


def analyze_phases(word, n, q):
    L = len(word)
    left_q = (q - 1) % n
    right_q = (q + 1) % n
    fire_steps = [t for t in range(L) if word[t] == q]
    fc_q = len(fire_steps)
    if fc_q == 0:
        return []
    phases = []
    for idx in range(fc_q):
        s = fire_steps[idx]
        a = fire_steps[(idx - 1) % fc_q]
        J = K = 0
        t_step = (a + 1) % L
        while t_step != s:
            if word[t_step] == left_q:
                J += 1
            if word[t_step] == right_q:
                K += 1
            t_step = (t_step + 1) % L
        phases.append((J, K))
    return phases


def get_phase_segments(word, n, q):
    """Return the actual word segments between consecutive fires of q."""
    L = len(word)
    fire_steps = [t for t in range(L) if word[t] == q]
    fc_q = len(fire_steps)
    if fc_q == 0:
        return []
    segments = []
    for idx in range(fc_q):
        s = fire_steps[idx]  # current fire
        a = fire_steps[(idx - 1) % fc_q]  # previous fire
        seg = []
        t_step = (a + 1) % L
        while t_step != s:
            seg.append(word[t_step])
            t_step = (t_step + 1) % L
        segments.append(seg)
    return segments


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


def main():
    print("RA13 Part 2: Clustering Reason Analysis")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        # For EACH provider, look at:
        # 1. The two phases of t (when fc_t=2)
        # 2. The walk segment in the "active" phase (where b fires 2)
        # 3. The walk segment in the "silent" phase (where b fires 0 AND s fires 0)
        # 4. What's the walk pattern?

        # Key question: Is t always BETWEEN two binary procs (binary triple)?
        # Or can t be at a binary-ternary boundary?

        # Track: segment lengths
        active_seg_len = Counter()
        silent_seg_len = Counter()

        # Track: which procs fire in the active vs silent segment
        # Does the active segment ONLY contain b-firings and procs beyond b?
        active_content = Counter()  # "b_only", "b_and_beyond", "mixed"

        # Track: does the walk in the active phase go through t to b?
        # I.e., the walk reaches b from t's side?
        walk_direction = Counter()

        # Critical: when fc_t=2 and fc_b=2, where do the two t-fires and two b-fires
        # interleave in the word?
        interleave_pattern = Counter()

        # Track: fc_t value for providers
        provider_fc = Counter()

        # For fc_t >= 3 providers: which phase has the 0-silent/2-active?
        fc3_phase_position = Counter()  # which of the fc_t phases

        # NEW: detailed segment anatomy for first few examples
        examples = []

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

                        # Find first provider
                        for p in range(n):
                            if fc[p] < 2:
                                continue
                            left_p = (p - 1) % n
                            right_p = (p + 1) % n
                            phases = analyze_phases(w, n, p)
                            found_prov = False
                            for pi, (J, K) in enumerate(phases):
                                if J == 0 and K >= 2 and ms[right_p] == 2:
                                    prov_t = p
                                    active_p = right_p
                                    silent_p = left_p
                                    active_fire_ct = K
                                    silent_fire_ct = J
                                    active_phase_idx = pi
                                    found_prov = True
                                    break
                                if K == 0 and J >= 2 and ms[left_p] == 2:
                                    prov_t = p
                                    active_p = left_p
                                    silent_p = right_p
                                    active_fire_ct = J
                                    silent_fire_ct = K
                                    active_phase_idx = pi
                                    found_prov = True
                                    break
                            if found_prov:
                                break

                        if not found_prov:
                            continue

                        provider_fc[fc[prov_t]] += 1

                        # Get segments
                        segments = get_phase_segments(w, n, prov_t)
                        if active_phase_idx < len(segments):
                            active_seg = segments[active_phase_idx]
                            active_seg_len[len(active_seg)] += 1

                            # Check what's in active segment
                            seg_procs = set(active_seg)
                            if seg_procs == {active_p}:
                                active_content["b_only"] += 1
                            elif active_p in seg_procs:
                                active_content["b_and_others"] += 1
                            else:
                                active_content["no_b"] += 1

                        # Interleaving when fc_t=2
                        if fc[prov_t] == 2:
                            t_fires = [i for i, x in enumerate(w) if x == prov_t]
                            b_fires = [i for i, x in enumerate(w) if x == active_p]
                            # How many b-fires between t_fires[0] and t_fires[1]?
                            if len(t_fires) == 2 and len(b_fires) == 2:
                                t0f, t1f = t_fires
                                b_between_01 = sum(1 for bf in b_fires
                                                   if (bf - t0f) % len(w) > 0
                                                   and (bf - t0f) % len(w) < (t1f - t0f) % len(w))
                                b_between_10 = len(b_fires) - b_between_01
                                interleave_pattern[(b_between_01, b_between_10)] += 1

                        # Examples
                        if len(examples) < 10:
                            examples.append({
                                'n': n, 'ms': list(ms), 'word': list(w), 'fc': list(fc),
                                'prov_t': prov_t, 'active_p': active_p, 'silent_p': silent_p,
                                'm_t': ms[prov_t], 'm_active': ms[active_p], 'm_silent': ms[silent_p],
                                'fc_t': fc[prov_t], 'fc_active': fc[active_p], 'fc_silent': fc[silent_p],
                                'active_fire_ct': active_fire_ct,
                                'phases': phases,
                            })

        elapsed = time.time() - t0
        print(f"\n  Results ({elapsed:.1f}s):")

        print(f"\n  Provider fc distribution:")
        for f, cnt in provider_fc.most_common():
            print(f"    fc_t={f}: {cnt}")

        print(f"\n  Active segment length:")
        for sl, cnt in active_seg_len.most_common(10):
            print(f"    len={sl}: {cnt}")

        print(f"\n  Active segment content:")
        for c, cnt in active_content.most_common():
            print(f"    {c}: {cnt}")

        print(f"\n  Interleaving pattern (b_fires in phase1, b_fires in phase2):")
        for pat, cnt in interleave_pattern.most_common():
            print(f"    {pat}: {cnt}")

        print(f"\n  Examples:")
        for ex in examples[:5]:
            print(f"    ms={ex['ms']}, word={ex['word']}")
            print(f"      fc={ex['fc']}")
            print(f"      t={ex['prov_t']}(m={ex['m_t']},fc={ex['fc_t']}), "
                  f"active={ex['active_p']}(m={ex['m_active']},fc={ex['fc_active']}), "
                  f"silent={ex['silent_p']}(m={ex['m_silent']},fc={ex['fc_silent']})")
            print(f"      phases of t: {ex['phases']}")
            print(f"      active_fire_ct={ex['active_fire_ct']}")


    # Part 3: The real question — WHY does clustering happen?
    print("\n\n" + "=" * 70)
    print("ANALYSIS: WHY CLUSTERING?")
    print("=" * 70)
    print("""
The dominant case: t is binary (m_t=2, fc_t=2), active neighbor b is binary (fc_b=2).

t fires exactly twice. Between t's 1st and 2nd fire, b fires either 0 or 2 times.
Between t's 2nd and 1st fire (wrap-around), b fires the complementary amount.

The interleaving pattern is (0,2) or (2,0): b's fires NEVER split 1-1 across
t's two phases.

WHY? This is the key question. Consider:
- t and b are adjacent on the ring
- Both are binary (fire exactly 2 times each in the cycle)
- The walk is on a ring graph

Between two consecutive fires of t, the walk must visit adjacent procs.
Since t is binary, the walk visits t exactly twice. The walk enters t from
one side, then leaves to the same or other side.

For a ZERO-WINDING cycle: the walk returns to its start with equal CW and CCW
steps. This forces a "bouncing" pattern.

CRITICAL INSIGHT: When t is binary (fc=2), between t's two firings, the walk
explores one "arm" of the ring from t. If b is on that arm, b fires in that
segment. If b is on the OTHER arm, b fires in the other segment.

But b is ADJACENT to t! So b is on BOTH arms. The question is: does the walk
visit b in BOTH segments, or just one?

Since b is binary (fc=2), and b is adjacent to t: the walk MUST pass through b
to reach any proc beyond b. If the walk goes t -> b -> beyond -> b -> t in one
segment, b fires 2 times. In the other segment, b fires 0 times (the walk goes
to t's other side).

This is exactly the (0,2)/(2,0) pattern we see!

But WAIT: can the walk go t -> b -> t -> (other side) -> ... -> t?
No — t fires only twice, so after t -> b -> t, that's already t's 2nd fire.
The segment IS t -> b -> ... -> b -> t (going through b and back).

So the structural reason is:
1. Binary procs fire exactly 2 times
2. Adjacent binary procs are connected
3. In one of t's two phases, the walk goes toward b and back, consuming
   both of b's fires
4. In the other phase, b fires 0 times (walk goes away from b)

For the silent side: if s is the non-b neighbor of t, s fires 0 in the
b-active phase because the walk goes TOWARD b (away from s) in that phase.
""")


if __name__ == "__main__":
    main()
