#!/usr/bin/env python3
"""
RA13 Boundary: Is the provider always at a binary-ternary boundary?

With >=3 binary procs on a ring, there must exist at least one "boundary pair":
a binary proc b adjacent to a non-binary proc s. If we use b as the active
neighbor and some t as the provider, then s is the silent side.

KEY QUESTION: Is there always a boundary binary b such that:
  - Some neighbor t has both b-fires in one phase
  - The other neighbor of t fires 0 in that phase

MORE PRECISELY: Consider boundary pair (b, s) where b is binary, s is non-binary,
and b and s are adjacent. Let t = the OTHER neighbor of b (on the non-s side).
Then t is also binary (part of the binary run).
- Does t always have a phase where b fires 2 (ALL) and s fires 0?

Wait, s is not a neighbor of t unless t = b. Let me reconsider.

The ring: ... s - b - t - ...  (s non-binary, b binary, t binary)
Provider = b, active = t (binary neighbor), silent = s (non-binary neighbor)
Phase of b where: t fires 2 (all) and s fires 0.

OR: Provider = t, active = b (binary neighbor), silent = next-after-t
Phase of t where: b fires 2 (all) and next-after-t fires 0.

Let me check both configurations.
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


def check_boundary_provider(word, n, ms, fc):
    """Check if boundary binary proc provides the phase structure."""
    L = len(word)
    # Find boundary binary procs: binary b adjacent to non-binary s
    for b in range(n):
        if ms[b] != 2 or fc[b] != 2:
            continue
        for side in [-1, 1]:
            s = (b + side) % n  # potential silent side (non-binary neighbor)
            t = (b - side) % n  # the other side of b (potential provider)
            if ms[s] == 2:
                continue  # s must be non-binary for boundary
            # Now: provider = b, active = some binary neighbor, silent = s
            # But wait: t (the other neighbor of b) might not be binary.
            # Let me just check: is there a phase of b where t fires ALL its fires
            # and s fires 0? No — t is the active side, not s.
            # Actually the setup is:
            #   provider = b
            #   active neighbor = t (should be binary with fc=2)
            #   silent neighbor = s (fires 0 in this phase)
            if ms[t] != 2:
                continue
            # Check: phase of b where t fires fc[t] (=2) and s fires 0
            b_fires = [i for i, x in enumerate(word) if x == b]
            t_fires_list = [i for i, x in enumerate(word) if x == t]
            s_fires_list = [i for i, x in enumerate(word) if x == s]
            for idx in range(len(b_fires)):
                start = b_fires[(idx - 1) % len(b_fires)]
                end = b_fires[idx]
                gap = (end - start) % L
                t_in = sum(1 for tf in t_fires_list if 0 < (tf - start) % L < gap)
                s_in = sum(1 for sf in s_fires_list if 0 < (sf - start) % L < gap)
                if t_in == fc[t] and s_in == 0:
                    return True, b, t, s
    return False, None, None, None


def check_any_boundary(word, n, ms, fc):
    """More general: any binary b at boundary, ANY neighbor as provider."""
    L = len(word)
    for b in range(n):
        if ms[b] != 2 or fc[b] != 2:
            continue
        b_fires = [i for i, x in enumerate(word) if x == b]
        # For each neighbor t of b
        for t in [(b-1)%n, (b+1)%n]:
            if fc[t] < 2:
                continue
            t_fires = [i for i, x in enumerate(word) if x == t]
            other = (t-1)%n if b == (t+1)%n else (t+1)%n
            o_fires = [i for i, x in enumerate(word) if x == other]
            for idx in range(len(t_fires)):
                start = t_fires[(idx-1)%len(t_fires)]
                end = t_fires[idx]
                gap = (end - start) % L
                b_in = sum(1 for bf in b_fires if 0 < (bf - start) % L < gap)
                o_in = sum(1 for of_ in o_fires if 0 < (of_ - start) % L < gap)
                if b_in == fc[b] and o_in == 0:
                    return True, t, b, other
    return False, None, None, None


def main():
    print("RA13 Boundary: Boundary Provider Analysis")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n  n = {n}")
        t0 = time.time()
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total = 0
        boundary_prov_found = 0
        boundary_any_found = 0

        for sorted_ms in sorted_multisets:
            if time.time() - t0 > 300 and n == 9:
                print(f"  TIME LIMIT")
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
                        ok1, _, _, _ = check_boundary_provider(w, n, ms, fc)
                        if ok1: boundary_prov_found += 1
                        ok2, _, _, _ = check_any_boundary(w, n, ms, fc)
                        if ok2: boundary_any_found += 1

        elapsed = time.time() - t0
        print(f"  ({elapsed:.1f}s) Total: {total}")
        print(f"  Boundary provider (b at boundary, t=other binary neighbor): "
              f"{boundary_prov_found} ({100*boundary_prov_found/max(1,total):.1f}%)")
        print(f"  Any boundary binary (b is boundary, any neighbor as provider): "
              f"{boundary_any_found} ({100*boundary_any_found/max(1,total):.1f}%)")


main()
