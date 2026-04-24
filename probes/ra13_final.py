#!/usr/bin/env python3
"""
RA13 FINAL: Complete provider characterization and proof sketch.

The provider theorem:
  In any ZW good cycle (cw>0, all fc>=2, some fc>=3, >=3 binary, sub-threshold):
  There exists proc t with a phase where:
    - One side fires 0 (silent)
    - Other side is binary with ALL its fires (=2, even) in this phase (active)

KEY FINDINGS from earlier parts:
1. active_fires always = fc_active = 2 (the binary neighbor dumps ALL fires)
2. Provider is typically binary (fc=2) but can be non-binary
3. Silent side fires 0 NOT by pigeonhole but by walk structure

THIS SCRIPT: Verify the full theorem + characterize the selection rule.
"""

import time
from itertools import permutations
from collections import Counter


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1: cw += 1
        elif diff == n - 1: ccw += 1
    return cw, ccw


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1: return
            if any(f < 2 for f in fc): return
            if all(f <= 2 for f in fc): return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw: return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining: return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2: continue
            if fc[nxt] >= 2 * ms[nxt]: continue
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
            if rot < best: best = rot
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
            if new_prod >= threshold: break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2: break
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
            if rot < best: best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best: best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def find_provider_general(word, n, ms, fc):
    """General search for provider proc."""
    L = len(word)
    for p in range(n):
        if fc[p] < 2: continue
        left_p = (p - 1) % n
        right_p = (p + 1) % n
        fire_steps = [i for i, x in enumerate(word) if x == p]
        for idx in range(len(fire_steps)):
            s = fire_steps[idx]
            a = fire_steps[(idx - 1) % len(fire_steps)]
            J = K = 0
            t_step = (a + 1) % L
            while t_step != s:
                if word[t_step] == left_p: J += 1
                if word[t_step] == right_p: K += 1
                t_step = (t_step + 1) % L
            if J == 0 and K >= 2 and ms[right_p] == 2:
                return p, idx, right_p, left_p, K
            if K == 0 and J >= 2 and ms[left_p] == 2:
                return p, idx, left_p, right_p, J
    return None


def find_provider_binary_centric(word, n, ms, fc):
    """Binary-centric search: for each binary b, look at neighbors."""
    L = len(word)
    binary_procs = [p for p in range(n) if ms[p] == 2 and fc[p] == 2]
    for b in binary_procs:
        b_fires = [i for i, x in enumerate(word) if x == b]
        for t in [(b-1)%n, (b+1)%n]:
            if fc[t] < 2: continue
            t_fires = [i for i, x in enumerate(word) if x == t]
            fc_t = len(t_fires)
            other = (t-1)%n if b == (t+1)%n else (t+1)%n
            o_fires = [i for i, x in enumerate(word) if x == other]
            for idx in range(fc_t):
                start = t_fires[(idx-1) % fc_t]
                end = t_fires[idx]
                gap = (end - start) % L
                b_in = sum(1 for bf in b_fires if 0 < (bf - start) % L < gap)
                o_in = sum(1 for of_ in o_fires if 0 < (of_ - start) % L < gap)
                if b_in == fc[b] and o_in == 0:
                    return t, idx, b, other, b_in
    return None


def main():
    print("RA13 FINAL: Provider Theorem Verification")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*70}")
        print(f"  n = {n}")
        print(f"{'='*70}")
        t0 = time.time()

        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total = 0
        general_found = 0
        binary_centric_found = 0
        both_found = 0
        general_only = 0
        binary_only = 0
        neither = 0

        # Provider characterization
        prov_m_t = Counter()
        prov_fc_t = Counter()
        prov_is_adjacent_to_binary = 0
        prov_active_fires = Counter()

        # KEY: relationship between t and its neighbors
        # t -> active (binary, fc=2) -> silent
        prov_arch = Counter()  # (m_t, m_silent)

        # Does fc(t) > fc(silent) ever hold? (Would enable pigeonhole)
        pigeonhole_applies = 0
        pigeonhole_fails = 0

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
                        for p in w: fc[p] += 1
                        total += 1

                        g = find_provider_general(w, n, ms, fc)
                        b = find_provider_binary_centric(w, n, ms, fc)

                        if g: general_found += 1
                        if b: binary_centric_found += 1
                        if g and b: both_found += 1
                        if g and not b: general_only += 1
                        if b and not g: binary_only += 1
                        if not g and not b: neither += 1

                        # Use general result for characterization
                        if g:
                            t_proc, phase_idx, active_p, silent_p, af = g
                            prov_m_t[ms[t_proc]] += 1
                            prov_fc_t[fc[t_proc]] += 1
                            prov_active_fires[af] += 1
                            prov_arch[(ms[t_proc], ms[silent_p])] += 1
                            if fc[t_proc] > fc[silent_p]:
                                pigeonhole_applies += 1
                            else:
                                pigeonhole_fails += 1

        elapsed = time.time() - t0
        print(f"  ({elapsed:.1f}s)")
        print(f"\n  Total ZW words: {total}")
        print(f"  General search found: {general_found} ({100*general_found/max(1,total):.1f}%)")
        print(f"  Binary-centric found: {binary_centric_found} ({100*binary_centric_found/max(1,total):.1f}%)")
        print(f"  Both found: {both_found}")
        print(f"  General only: {general_only}")
        print(f"  Binary only: {binary_only}")
        print(f"  Neither: {neither}")

        print(f"\n  Provider m_t: {dict(prov_m_t.most_common())}")
        print(f"  Provider fc_t: {dict(prov_fc_t.most_common())}")
        print(f"  Active fires: {dict(prov_active_fires.most_common())}")
        print(f"  Provider arch (m_t, m_silent): {dict(prov_arch.most_common(10))}")
        print(f"  Pigeonhole applies (fc_t > fc_silent): {pigeonhole_applies}")
        print(f"  Pigeonhole fails (fc_t <= fc_silent): {pigeonhole_fails}")


if __name__ == "__main__":
    main()
