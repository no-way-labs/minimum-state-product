#!/usr/bin/env python3
"""
RA12: Provider detail when both-binary fails.

When the provider doesn't have BOTH neighbors binary, what does it look like?
The provider has one binary neighbor (active side) and one non-binary neighbor
(silent side). This means:
- Active: binary fires >= 2
- Silent: ternary fires 0

For phase_dispatch_ec: we need the active neighbor to be binary (yes) AND
the silent neighbor to be binary (for the dispatch proof)?

Actually: phase_dispatch_ec just needs the active neighbor's fires to create
a mover/non-mover overlap. The silent side doesn't matter for that.

Let me check what m_silent is when both-binary fails.
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
        t = (a + 1) % L
        while t != s:
            if word[t] == left_q:
                J += 1
            if word[t] == right_q:
                K += 1
            t = (t + 1) % L
        phases.append((J, K))
    return phases


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
    print("RA12: Provider Detail Analysis")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        # Track provider architecture
        provider_arch = Counter()  # (m_p, m_silent, m_active, active_fires)

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

                        # Find first any-binary provider
                        for p in range(n):
                            if fc[p] < 2:
                                continue
                            lp = (p - 1) % n
                            rp = (p + 1) % n
                            phases = analyze_phases(w, n, p)
                            found = False
                            for J, K in phases:
                                if J == 0 and K >= 2 and ms[rp] == 2:
                                    arch = (ms[p], ms[lp], ms[rp], K)
                                    provider_arch[arch] += 1
                                    found = True
                                    break
                                if K == 0 and J >= 2 and ms[lp] == 2:
                                    arch = (ms[p], ms[rp], ms[lp], J)
                                    provider_arch[arch] += 1
                                    found = True
                                    break
                            if found:
                                break

        print(f"  Provider architectures (m_p, m_silent, m_active, active_fires):")
        for arch, cnt in provider_arch.most_common():
            m_p, m_silent, m_active, af = arch
            print(f"    m_p={m_p}, m_silent={m_silent}, m_active={m_active}(binary), "
                  f"active_fires={af}: {cnt}")

    print("\n\nKEY: The provider always has m_active=2 (binary active neighbor).")
    print("The silent side can be binary (m_silent=2) or ternary (m_silent=3+).")
    print("For phase_dispatch_ec: only the active side matters.")
    print("  Active is binary, fires >= 2 (= ALL its fires) in one phase.")
    print("  This means the binary neighbor goes through its complete state cycle")
    print("  (0->1->0) between two fires of the provider.")
    print("  At the second fire of binary, it returns to state 0.")
    print("  The provider's state is preserved (binary fired, not provider).")
    print("  -> Entry conflict: binary's mover context at first fire = non-mover")
    print("     context at second fire (or vice versa).")


if __name__ == "__main__":
    main()
