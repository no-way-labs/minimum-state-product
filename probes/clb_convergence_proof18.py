#!/usr/bin/env python3
"""
CONVERGENCE PROOF 18: Novel potential functions
================================================

Test conceptually clean potential functions:
1. Hamming distance to nearest good config
2. Wave boundary count (# adjacent pairs with different values)
3. "Displacement" sum: Σ |c[i] - target_i(L,R)|
4. # positions NOT at target value (= # privileged positions)
5. Lexicographic distance to nearest good config
6. Config "energy" based on table structure
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import Counter


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    good_list = list(good_set)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    transitions = []
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    nt = len(transitions)
    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad, {len(good_list)} good, {nt} transitions")
    print(f"{'=' * 70}")

    # ═══════════════════════════════════════════════════════════
    # Potential 1: Hamming distance to nearest good config
    # ═══════════════════════════════════════════════════════════
    def hamming(a, b):
        return sum(1 for x, y in zip(a, b) if x != y)

    ham_cache = {}
    for c in bad_list:
        ham_cache[c] = min(hamming(c, g) for g in good_list)

    v1 = sum(1 for c, cp, i in transitions
             if ham_cache[c] <= ham_cache.get(cp, 0))
    pct1 = 100 * v1 / nt
    print(f"  Hamming to nearest good: {v1} violations ({pct1:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 2: Wave boundary count
    # ═══════════════════════════════════════════════════════════
    def wave_boundaries(c):
        return sum(1 for i in range(n) if c[i] != c[(i + 1) % n])

    v2 = sum(1 for c, cp, i in transitions
             if wave_boundaries(c) <= wave_boundaries(cp))
    pct2 = 100 * v2 / nt
    print(f"  Wave boundaries: {v2} violations ({pct2:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 3: # privileged positions (= # not at target)
    # ═══════════════════════════════════════════════════════════
    def n_priv(c):
        return sum(1 for i in range(n)
                   if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i])

    v3 = sum(1 for c, cp, i in transitions if n_priv(c) <= n_priv(cp))
    pct3 = 100 * v3 / nt
    print(f"  # privileged: {v3} violations ({pct3:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 4: "Target displacement" = Σ |c[i] - target_i|
    # ═══════════════════════════════════════════════════════════
    def target_disp(c):
        total = 0
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            target = fs[i](L, S, R)
            total += abs(S - target)
        return total

    v4 = sum(1 for c, cp, i in transitions
             if target_disp(c) <= target_disp(cp))
    pct4 = 100 * v4 / nt
    print(f"  Target displacement: {v4} violations ({pct4:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 5: (Hamming, #priv) lex
    # ═══════════════════════════════════════════════════════════
    v5 = sum(1 for c, cp, i in transitions
             if (ham_cache[c], n_priv(c)) <= (ham_cache.get(cp, 0), n_priv(cp)))
    pct5 = 100 * v5 / nt
    print(f"  (Hamming, #priv) lex: {v5} violations ({pct5:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 6: Weighted Hamming (weight by position distance from boundary)
    # ═══════════════════════════════════════════════════════════
    def weighted_hamming(c):
        best = float('inf')
        for g in good_list:
            d = sum((1 + min(i, n-1-i)) for i in range(n) if c[i] != g[i])
            best = min(best, d)
        return best

    wh_cache = {}
    for c in bad_list:
        wh_cache[c] = weighted_hamming(c)
    v6 = sum(1 for c, cp, i in transitions
             if wh_cache[c] <= wh_cache.get(cp, 0))
    pct6 = 100 * v6 / nt
    print(f"  Weighted Hamming: {v6} violations ({pct6:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 7: "Good matching" — for each position, does c[i]
    # match ANY good config that agrees with c on neighbors?
    # ═══════════════════════════════════════════════════════════
    def good_match_count(c):
        count = 0
        for i in range(n):
            L = c[(i - 1) % n]
            R = c[(i + 1) % n]
            target = fs[i](L, c[i], R)  # what i would move to
            if target == c[i]:  # i is settled
                count += 1
        return count

    v7 = sum(1 for c, cp, i in transitions
             if good_match_count(c) >= good_match_count(cp))
    pct7 = 100 * v7 / nt
    print(f"  Settled count (want increase): {v7} violations ({pct7:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 8: Value sum Σ c[i]
    # ═══════════════════════════════════════════════════════════
    v8 = sum(1 for c, cp, i in transitions if sum(c) <= sum(cp))
    pct8 = 100 * v8 / nt
    print(f"  Value sum: {v8} violations ({pct8:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 9: "Config fingerprint" based on sorted values
    # ═══════════════════════════════════════════════════════════
    def config_signature(c):
        return tuple(sorted(c, reverse=True))
    v9 = sum(1 for c, cp, i in transitions
             if config_signature(c) <= config_signature(cp))
    pct9 = 100 * v9 / nt
    print(f"  Sorted config values: {v9} violations ({pct9:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Potential 10: Combined (Hamming, wave_boundaries, #priv) lex
    # ═══════════════════════════════════════════════════════════
    v10 = sum(1 for c, cp, i in transitions
              if (ham_cache[c], wave_boundaries(c), n_priv(c))
              <= (ham_cache.get(cp, 0), wave_boundaries(cp), n_priv(cp)))
    pct10 = 100 * v10 / nt
    print(f"  (Ham, WB, #priv) lex: {v10} violations ({pct10:.1f}%)")

    # ═══════════════════════════════════════════════════════════
    # Best candidate details
    # ═══════════════════════════════════════════════════════════
    potentials = {
        'Hamming': (v1, ham_cache),
        '#priv': (v3, {c: n_priv(c) for c in bad_list}),
        'WB': (v2, {c: wave_boundaries(c) for c in bad_list}),
        'target_disp': (v4, {c: target_disp(c) for c in bad_list}),
    }

    best_name = min(potentials, key=lambda k: potentials[k][0])
    best_v, best_cache = potentials[best_name]

    if 0 < best_v <= 30:
        print(f"\n  Best single potential: '{best_name}' ({best_v} violations)")
        viol_list = [(c, cp, i) for c, cp, i in transitions
                     if best_cache[c] <= best_cache.get(cp, 0)]
        mover_counts = Counter(i for _, _, i in viol_list)
        print(f"    By mover: {dict(sorted(mover_counts.items()))}")
        for c, cp, i in viol_list[:10]:
            print(f"    c={c} →[{i}]→ {cp}: {best_cache[c]} -> {best_cache.get(cp, '?')}")

    # ═══════════════════════════════════════════════════════════
    # COMBINED: Check if Hamming violations and #priv violations overlap
    # ═══════════════════════════════════════════════════════════
    ham_viols = set((c, cp) for c, cp, i in transitions
                    if ham_cache[c] <= ham_cache.get(cp, 0))
    priv_viols = set((c, cp) for c, cp, i in transitions
                     if n_priv(c) <= n_priv(cp))
    wb_viols = set((c, cp) for c, cp, i in transitions
                   if wave_boundaries(c) <= wave_boundaries(cp))
    td_viols = set((c, cp) for c, cp, i in transitions
                   if target_disp(c) <= target_disp(cp))

    print(f"\n  Overlap analysis:")
    print(f"    Hamming ∩ #priv: {len(ham_viols & priv_viols)}")
    print(f"    Hamming ∩ WB: {len(ham_viols & wb_viols)}")
    print(f"    Hamming ∩ target_disp: {len(ham_viols & td_viols)}")
    print(f"    #priv ∩ WB: {len(priv_viols & wb_viols)}")
    print(f"    ALL FOUR: {len(ham_viols & priv_viols & wb_viols & td_viols)}")
    if len(ham_viols & priv_viols & wb_viols & td_viols) == 0:
        print(f"    *** ZERO overlap of all four! Combined lex might work!")


if __name__ == '__main__':
    for nv in [5, 6, 7, 8]:
        analyze(nv)
