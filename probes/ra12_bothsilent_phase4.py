#!/usr/bin/env python3
"""
RA12 Part 4: Why both-silent is impossible + why binary-one-sided always exists.

PROVEN FACTS from Parts 1-3:
1. (0,0) phase NEVER exists at ANY proc (0% rate, n=5 and n=7).
2. Every cycle has EC (100%).
3. Q5 = 100%: every ZW cycle with fc>=3 has SOME proc with a binary-neighbor
   one-sided >=2 phase.

This script investigates the STRUCTURAL reasons:

A. Why no (0,0): In a ZW cycle, adjacent movers. Between two firings of q,
   the mover must traverse through q's neighborhood. At least one neighbor
   fires. So J + K >= 1 for EVERY phase. No both-silent possible.

   Wait - the phase interval is BETWEEN two consecutive q-fires. Since the
   mover is adjacent-stepping, between fire_step[i-1] and fire_step[i],
   the mover walks from q to q. The first step after q fires goes to q+1 or
   q-1 (adjacent). The last step before q fires again comes from q+1 or q-1.
   So at least one neighbor fires in the interval. J+K >= 1 ALWAYS.

   Actually: between two q-fires, the walk goes q -> ... -> q. Since the walk
   is a sequence of adjacent steps, right after q fires the mover goes to a
   neighbor of q. Right before q fires again, the mover comes from a neighbor
   of q. So at minimum, one of the neighbors fires once in the interval.

   More precisely: the step BEFORE q fires has the mover at q-1 or q+1.
   The step AFTER the previous q-fire has the mover at q-1 or q+1.
   So J+K >= 2 actually? No - the first step after q fires at step a is
   word[a+1] which must be adjacent to q. Then the mover might go q+1, q, q-1
   but wait, q fires at a, not at a+1. Let me think again.

   word[a] = q (q fires at step a). word[a+1] must differ from q by 1 (adj).
   So word[a+1] is q-1 or q+1. Similarly, word[s] = q fires at step s,
   word[s-1] must be q-1 or q+1.

   So in the interval (a, s), the FIRST mover word[a+1] is a neighbor of q,
   and the LAST mover word[s-1] might or might not be (s-1 = a+1 is possible
   if the interval has length 2, meaning word = ...q, nbr, q...).

   Actually word[a+1] could be word[a]+1 or word[a]-1, so yes it's a neighbor
   of q. This neighbor fires once. If the interval has more steps, the walk
   continues elsewhere and comes back to q. The step at s-1 (right before q fires)
   must be adjacent to q, so word[s-1] is a neighbor of q (but could be same
   as word[a+1]).

   Summary: J + K >= 1 (the first mover after q's fire is a neighbor).
   If interval length >= 2: J + K >= 2 (first and last movers are neighbors).
   But they could be the SAME neighbor: e.g., both = left, so J >= 2, K = 0.
   Or both different: J >= 1, K >= 1.

   This proves (0,0) is IMPOSSIBLE for any phase with interval length >= 1.
   And every phase has interval length >= 1 (since fc(each proc) >= 2, there
   are at least 2n steps but only fc(q) phases at q).

B. Binary-neighbor one-sided >=2:
   The ternary proc pair (they're always adjacent in sorted multisets at the
   ring boundary). One ternary fires 3 times. Its binary neighbor fires 2 times.

   Actually let me just verify the structural argument directly.
"""

from itertools import product as iproduct
from collections import Counter
import time


def enumerate_state_sequences(m, k):
    if k == 0:
        return [[0]]
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


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


def analyze_phases_detailed(word, n, q):
    """Return phases with step-level detail."""
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
        interval_steps = []
        t = (a + 1) % L
        while t != s:
            interval_steps.append(word[t])
            if word[t] == left_q:
                J += 1
            if word[t] == right_q:
                K += 1
            t = (t + 1) % L
        phases.append({
            'J': J, 'K': K, 'interval': interval_steps,
            'first_mover': interval_steps[0] if interval_steps else None,
            'last_mover': interval_steps[-1] if interval_steps else None,
            'length': len(interval_steps)
        })
    return phases


def build_configs(word, n, combo, fc):
    L = len(word)
    fire_count = [0] * n
    configs = [tuple(combo[p][0] for p in range(n))]
    for t in range(L):
        mover = word[t]
        fire_count[mover] += 1
        new_config = list(configs[-1])
        new_config[mover] = combo[mover][fire_count[mover]]
        configs.append(tuple(new_config))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]


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


def main():
    print("RA12 Part 4: Structural Analysis")
    print("=" * 70)

    # Verify: J+K >= 1 always (adjacent mover argument)
    print("\n=== A: Verify J+K >= 1 for all phases ===")

    for n in [5, 7]:
        print(f"\n  n = {n}")
        threshold = 4 * (3 ** (n - 2))
        multisets = generate_subthreshold_multisets(n, threshold)
        t0 = time.time()

        min_jk = float('inf')
        min_interval_len = float('inf')
        total_phases = 0
        jk_1_count = 0
        jk_ge2_count = 0
        first_eq_last = 0  # first and last mover in interval are same neighbor
        first_neq_last = 0

        # Also track: when J+K == 1, what's the interval structure?
        jk1_structures = Counter()

        for ms in multisets:
            if time.time() - t0 > 60:
                break
            max_len = min(sum(ms), 4 * n)
            min_len = 2 * n + 1
            for cycle_len in range(min_len, max_len + 1):
                walks = _enumerate_walks_dfs(n, cycle_len, ms)
                for w in walks:
                    fc = [0] * n
                    for p in w:
                        fc[p] += 1
                    proc_seqs = {}
                    feasible = True
                    for p in range(n):
                        seqs = enumerate_state_sequences(ms[p], fc[p])
                        if not seqs:
                            feasible = False
                            break
                        proc_seqs[p] = seqs
                    if not feasible:
                        continue
                    # Just check walk structure (word-level), no need for state seqs
                    for q in range(n):
                        if fc[q] < 3:
                            continue
                        phases = analyze_phases_detailed(w, n, q)
                        for ph in phases:
                            total_phases += 1
                            jk = ph['J'] + ph['K']
                            if jk < min_jk:
                                min_jk = jk
                            if ph['length'] < min_interval_len:
                                min_interval_len = ph['length']
                            if jk == 1:
                                jk_1_count += 1
                                jk1_structures[ph['length']] += 1
                            elif jk >= 2:
                                jk_ge2_count += 1
                            if ph['first_mover'] is not None and ph['last_mover'] is not None:
                                if ph['first_mover'] == ph['last_mover']:
                                    first_eq_last += 1
                                else:
                                    first_neq_last += 1
                    break  # only need one combo for word-level analysis

        print(f"    Total phases: {total_phases}")
        print(f"    Min J+K: {min_jk}")
        print(f"    Min interval length: {min_interval_len}")
        print(f"    J+K = 1: {jk_1_count} ({100*jk_1_count/max(1,total_phases):.1f}%)")
        print(f"    J+K >= 2: {jk_ge2_count} ({100*jk_ge2_count/max(1,total_phases):.1f}%)")
        print(f"    First == Last neighbor: {first_eq_last}")
        print(f"    First != Last neighbor: {first_neq_last}")
        print(f"    J+K=1 by interval length: {dict(jk1_structures.most_common(5))}")

    # B: Why binary-one-sided always exists at cycle level
    print("\n\n=== B: Binary-one-sided >=2 at ternary-binary boundary ===")
    print("Structural argument:")
    print("  - Multiset has >= 3 binary and some ternary procs")
    print("  - On the ring, ternary procs are adjacent to some binary procs")
    print("  - A ternary proc q with fc(q)=3 has 3 phases")
    print("  - Its binary neighbor b with fc(b)=2 fires in at most 2 of q's 3 phases")
    print("  - So at least 1 phase has b firing 0 times (left or right silent)")
    print("  - The OTHER neighbor fires >= 1 in that phase (J+K>=1)")
    print("  - But does the other neighbor fire >= 2?")
    print()
    print("  Not necessarily from counting alone. But the data says YES universally.")
    print("  Let's check the interval structure of the silent-side phase.")

    print("\n=== C: Detailed phase structure at ternary-binary boundary ===")

    n = 5
    threshold = 4 * (3 ** (n - 2))
    multisets = generate_subthreshold_multisets(n, threshold)

    for ms in multisets:
        max_len = min(sum(ms), 4 * n)
        min_len = 2 * n + 1
        for cycle_len in range(min_len, max_len + 1):
            walks = _enumerate_walks_dfs(n, cycle_len, ms)
            for w in walks:
                fc = [0] * n
                for p in w:
                    fc[p] += 1
                # Find ternary procs adjacent to binary
                for q in range(n):
                    if ms[q] < 3 or fc[q] < 3:
                        continue
                    left_q = (q - 1) % n
                    right_q = (q + 1) % n
                    if ms[left_q] == 2 or ms[right_q] == 2:
                        phases = analyze_phases_detailed(w, n, q)
                        print(f"\n  ms={list(ms)}, word={w}")
                        print(f"  q={q}(m={ms[q]},fc={fc[q]}), "
                              f"left={left_q}(m={ms[left_q]},fc={fc[left_q]}), "
                              f"right={right_q}(m={ms[right_q]},fc={fc[right_q]})")
                        for i, ph in enumerate(phases):
                            print(f"    Phase {i}: J={ph['J']}, K={ph['K']}, "
                                  f"len={ph['length']}, interval={ph['interval']}")
                        break  # one example per word
                break  # one example per length
        break  # one multiset

    # D: The REAL question - can we prove this analytically?
    print("\n\n=== D: Analytical path ===")
    print("KEY INSIGHT: In ZW cycles, the walk must visit both sides of any proc.")
    print("For fc(q)=3 ternary with binary neighbor b:")
    print("  - b fires 2 times total")
    print("  - q fires 3 times, creating 3 phases")
    print("  - By pigeonhole, b fires 0 in at least 1 phase (3 phases, 2 fires)")
    print("  - In that b-silent phase, the walk starts from q, goes to other side,")
    print("    MUST cross through the other neighbor at least twice (ZW constraint)")
    print("    to come back to q.")
    print()
    print("Wait - that's not obviously true. Let's check what happens in the")
    print("b-silent phase more carefully.")
    print()

    # E: In the b-silent phase, what does the walk look like?
    print("=== E: Walk structure in b-silent phase ===")

    n = 5
    threshold = 4 * (3 ** (n - 2))
    multisets = generate_subthreshold_multisets(n, threshold)

    # Collect: for the b-silent phase (J=0 or K=0), what's the other side's fire count?
    other_side_fires = Counter()
    b_silent_details = []

    for ms in multisets:
        max_len = min(sum(ms), 4 * n)
        min_len = 2 * n + 1
        for cycle_len in range(min_len, max_len + 1):
            walks = _enumerate_walks_dfs(n, cycle_len, ms)
            for w in walks:
                fc = [0] * n
                for p in w:
                    fc[p] += 1
                for q in range(n):
                    if ms[q] < 3 or fc[q] < 3:
                        continue
                    left_q = (q - 1) % n
                    right_q = (q + 1) % n
                    phases = analyze_phases_detailed(w, n, q)

                    for ph in phases:
                        if ph['J'] == 0 and ms[left_q] == 2:
                            other_side_fires[ph['K']] += 1
                            if ph['K'] < 2 and len(b_silent_details) < 5:
                                b_silent_details.append({
                                    'ms': list(ms), 'word': w, 'q': q,
                                    'phase': ph, 'fc': list(fc)
                                })
                        if ph['K'] == 0 and ms[right_q] == 2:
                            other_side_fires[ph['J']] += 1
                            if ph['J'] < 2 and len(b_silent_details) < 5:
                                b_silent_details.append({
                                    'ms': list(ms), 'word': w, 'q': q,
                                    'phase': ph, 'fc': list(fc)
                                })

    print(f"  Other-side fire count distribution in b-silent phases:")
    for k, cnt in sorted(other_side_fires.items()):
        print(f"    Other fires = {k}: {cnt}")

    if b_silent_details:
        print(f"\n  Examples where other side fires < 2:")
        for d in b_silent_details:
            print(f"    ms={d['ms']}, q={d['q']}, phase={d['phase']}")

    # F: Now the critical insight - what if the other side fires exactly 1?
    # Then we have (0, 1) or (1, 0) phase. This is normalForm, which needs
    # palindromic_phase_ec and callbacks.
    # BUT: we showed Q5 = 100% at cycle level. So there's ALWAYS another proc
    # with a one-sided >=2 phase with binary neighbor.
    # The question: is this a different ternary proc, or the same one?

    print("\n\n=== F: Which proc provides the binary-neighbor one-sided >=2? ===")

    for n in [5]:
        threshold = 4 * (3 ** (n - 2))
        multisets = generate_subthreshold_multisets(n, threshold)

        # For each cycle, which proc(s) have binary-neighbor one-sided >=2?
        provider_is_fc3 = 0
        provider_is_fc2 = 0
        provider_stats = Counter()

        for ms in multisets:
            max_len = min(sum(ms), 4 * n)
            min_len = 2 * n + 1
            for cycle_len in range(min_len, max_len + 1):
                walks = _enumerate_walks_dfs(n, cycle_len, ms)
                for w in walks:
                    fc = [0] * n
                    for p in w:
                        fc[p] += 1

                    providers = []
                    for p in range(n):
                        if fc[p] < 2:
                            continue
                        left_p = (p - 1) % n
                        right_p = (p + 1) % n
                        phases = analyze_phases_detailed(w, n, p)
                        for ph in phases:
                            if (ph['J'] == 0 and ph['K'] >= 2 and ms[right_p] == 2) or \
                               (ph['K'] == 0 and ph['J'] >= 2 and ms[left_p] == 2):
                                providers.append((p, fc[p], ms[p]))
                                break

                    for p, fcp, mp in providers:
                        if fcp >= 3:
                            provider_is_fc3 += 1
                        else:
                            provider_is_fc2 += 1
                        provider_stats[(fcp, mp)] += 1

        print(f"\n  n={n}: Provider proc stats:")
        print(f"    fc>=3: {provider_is_fc3}")
        print(f"    fc=2:  {provider_is_fc2}")
        print(f"    By (fc, m): {dict(provider_stats)}")


if __name__ == "__main__":
    main()
