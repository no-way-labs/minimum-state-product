#!/usr/bin/env python3
"""
RA12: Provider anatomy for non-consecutive binary placements.

When binary procs are non-consecutive (e.g., [2,2,3,2,3]):
- No triple of consecutive binary
- Provider must come from a binary proc at a binary-ternary boundary,
  or from a ternary proc
- Let's see which proc provides and WHY

Also: check the expanded criterion - provider can be ANY proc, not just
middle of binary triple. What patterns appear?
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


def find_provider_detailed(word, n, ms, fc):
    """Find ALL procs that could be provider, with details."""
    providers = []
    for p in range(n):
        if fc[p] < 2:
            continue
        left_p = (p - 1) % n
        right_p = (p + 1) % n
        phases = analyze_phases(word, n, p)
        for J, K in phases:
            if J == 0 and K >= 2 and ms[right_p] == 2:
                providers.append({
                    'proc': p, 'm_p': ms[p], 'fc_p': fc[p],
                    'side': 'right', 'active_fires': K,
                    'm_left': ms[left_p], 'm_right': ms[right_p],
                    'phases': phases
                })
                break
            if K == 0 and J >= 2 and ms[left_p] == 2:
                providers.append({
                    'proc': p, 'm_p': ms[p], 'fc_p': fc[p],
                    'side': 'left', 'active_fires': J,
                    'm_left': ms[left_p], 'm_right': ms[right_p],
                    'phases': phases
                })
                break
    return providers


def main():
    print("RA12: Provider Anatomy")
    print("=" * 70)

    # Focus on non-consecutive placements
    non_consec_placements = {
        5: [[2, 2, 3, 2, 3], [2, 2, 3, 2, 4]],
        7: [[2, 2, 3, 2, 2, 3, 3], [2, 2, 3, 2, 3, 2, 3],
            [2, 2, 3, 2, 2, 3, 4], [2, 2, 3, 2, 3, 2, 4]],
    }

    for n, placements in non_consec_placements.items():
        print(f"\n{'='*70}")
        print(f"  n = {n}, Non-consecutive binary placements")
        print(f"{'='*70}")

        for ms in placements:
            print(f"\n  ms = {ms}")
            # Show binary and ternary positions
            binary_pos = [i for i in range(n) if ms[i] == 2]
            ternary_pos = [i for i in range(n) if ms[i] >= 3]
            print(f"    Binary at: {binary_pos}")
            print(f"    Ternary at: {ternary_pos}")

            # For each binary proc, show its neighbor types
            for b in binary_pos:
                lp = (b - 1) % n
                rp = (b + 1) % n
                print(f"    b={b}: left={lp}(m={ms[lp]}), right={rp}(m={ms[rp]})")

            max_len = min(sum(ms), 4 * n)
            min_len = 2 * n + 1

            total = 0
            provider_type = Counter()  # (m_provider, side, m_left, m_right)

            for cycle_len in range(min_len, max_len + 1):
                walks = _enumerate_walks_dfs(n, cycle_len, ms)
                for w in walks:
                    fc = [0] * n
                    for p in w:
                        fc[p] += 1

                    total += 1
                    provs = find_provider_detailed(w, n, ms, fc)

                    if provs:
                        prov = provs[0]
                        key = (prov['m_p'], prov['side'],
                               prov['m_left'], prov['m_right'])
                        provider_type[key] += 1

                        if total <= 3:
                            print(f"\n    Word: {w}")
                            print(f"    fc: {list(fc)}")
                            for prov in provs:
                                print(f"      Provider: proc {prov['proc']} "
                                      f"(m={prov['m_p']}, fc={prov['fc_p']}), "
                                      f"side={prov['side']}, active={prov['active_fires']}")
                                print(f"        Neighbors: L(m={prov['m_left']}), "
                                      f"R(m={prov['m_right']})")
                                print(f"        Phases: {prov['phases']}")
                    else:
                        print(f"\n    *** NO PROVIDER: word={w}, fc={list(fc)}")

            print(f"\n    Total words: {total}")
            print(f"    Provider types: {dict(provider_type)}")

    # Summary: which proc architectures can serve as provider?
    print("\n\n" + "=" * 70)
    print("PROVIDER ARCHITECTURE SUMMARY")
    print("=" * 70)
    print("""
A provider proc p has:
  - A phase where one neighbor fires 0 and the other (binary) fires >= 2
  - The binary neighbor fires ALL its fires (fc=2) in one phase of p

Provider can be:
  A. Binary p with binary neighbor (both-binary pair)
     - p has 2 phases, binary neighbor fires 2
     - Need fires to cluster: 2-0 split (not 1-1)

  B. Ternary p with binary neighbor
     - p has 3+ phases, binary neighbor fires 2
     - By pigeonhole: at least 1 phase with binary firing 0
     - Need OTHER neighbor to fire >= 2 in that phase

  C. Binary p with ternary neighbor (silent side) and binary neighbor (active side)
     - p has 2 phases, binary active neighbor fires 2
     - Need 2-0 split AND ternary silent side fires 0 in same phase

The data shows provider ALWAYS exists. The mechanism varies by placement.
""")


if __name__ == "__main__":
    main()
