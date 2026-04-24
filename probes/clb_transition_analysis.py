#!/usr/bin/env python3
"""clb_transition_analysis.py — Characterize transition tables from good-targeting.

For n=9..12, analyze the transition functions produced by the construction:
1. Do middle ternary processors get the same table (after canonical relabeling)?
2. Is there a simple rule describing most free entries?
3. How do the n-3 liveness fixes distribute across processors?
"""

import sys
import os
import time

sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict


def build_system(n):
    """Build the good-targeting system for n processors. Return tables."""
    ms = tuple([2] + [3] * (n - 2) + [2])
    product_val = 4 * (3 ** (n - 2))

    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return None
        visited.add(nc)
        cycle.append(nc)

    if movers is None:
        return None

    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    free_entries = []
    free_set = set()
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)
                        free_set.add(key)

    # Pre-index
    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if key in free_set:
                triple_index[key].append(c)

    # Good-targeting
    edge_costs = {}
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        matching = triple_index.get(key, [])
        best_out = S
        best_good = 0
        best_ng = 0
        for out in range(ms[p]):
            if out == S:
                edge_costs[(key, out)] = 0
                continue
            good_count = 0
            ng_count = 0
            for c in matching:
                new_c_t = c[:p] + (out,) + c[p + 1:]
                if new_c_t in good_set:
                    good_count += 1
                elif new_c_t in non_good_set:
                    ng_count += 1
            edge_costs[(key, out)] = ng_count
            if good_count > best_good or (good_count == best_good and ng_count < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng_count
        comp[key] = best_out

    # Liveness fix — track which entries get fixed
    liveness_fix_entries = []
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val
                liveness_fix_entries.append((best_key, best_out_val, c))

    return {
        'n': n, 'ms': ms, 'comp': comp, 'det': det,
        'free_entries': free_entries, 'free_set': free_set,
        'cycle': cycle, 'movers': movers, 'good_set': good_set,
        'liveness_fix_entries': liveness_fix_entries,
    }


def analyze_tables(sys_data):
    n = sys_data['n']
    ms = sys_data['ms']
    comp = sys_data['comp']
    det = sys_data['det']
    free_set = sys_data['free_set']
    liveness_fixes = sys_data['liveness_fix_entries']

    print(f"\n{'=' * 70}")
    print(f"n={n}: ms={ms}, product={4 * 3 ** (n - 2)}")
    print(f"{'=' * 70}")

    # 1. Dump transition tables per processor
    print(f"\n--- Transition tables ---")
    tables = {}
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        table = {}
        priv_count = 0
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    out = comp.get((p, L, S, R), S)
                    table[(L, S, R)] = out
                    if out != S:
                        priv_count += 1
        tables[p] = table
        is_det = sum(1 for key in table if (p, key[0], key[1], key[2]) in det)
        is_free = sum(1 for key in table if (p, key[0], key[1], key[2]) in free_set)
        priv_free = sum(1 for key in table
                        if (p, key[0], key[1], key[2]) in free_set
                        and table[key] != key[1])
        print(f"  P{p} (m={m_S}, neighbors={m_L},{m_R}): "
              f"{priv_count}/{m_L * m_S * m_R} privileged, "
              f"det={is_det}, free={is_free}, priv_free={priv_free}")

    # 2. Check if middle processors have identical tables
    print(f"\n--- Middle processor comparison ---")
    # Middle processors: positions 2 to n-3 (all have m=3, neighbors 3,3)
    if n >= 7:
        middle_range = range(2, n - 2)
        ref_p = 2
        ref_table = tables[ref_p]
        for p in middle_range:
            if p == ref_p:
                continue
            same = all(tables[p][k] == ref_table[k] for k in ref_table)
            if same:
                print(f"  P{p} == P{ref_p}: IDENTICAL")
            else:
                diffs = [(k, ref_table[k], tables[p][k])
                         for k in ref_table if tables[p][k] != ref_table[k]]
                print(f"  P{p} vs P{ref_p}: {len(diffs)} differences")
                for k, v1, v2 in diffs[:5]:
                    print(f"    ({k[0]},{k[1]},{k[2]}): P{ref_p}={v1}, P{p}={v2}")

    # 3. Classify free entries by rule
    print(f"\n--- Free entry classification ---")
    rules = defaultdict(int)
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in free_set:
                        continue
                    out = comp[key]
                    if out == S:
                        rules['identity'] += 1
                    elif out == L:
                        rules['copy_L'] += 1
                    elif out == R:
                        rules['copy_R'] += 1
                    elif out == (S + 1) % m_S:
                        rules['inc_mod'] += 1
                    elif out == (S - 1) % m_S:
                        rules['dec_mod'] += 1
                    elif out == (L + 1) % m_S:
                        rules['L_plus_1'] += 1
                    elif out == (R + 1) % m_S:
                        rules['R_plus_1'] += 1
                    else:
                        rules[f'other({out})'] += 1

    total_free = sum(rules.values())
    for rule, count in sorted(rules.items(), key=lambda x: -x[1]):
        print(f"  {rule}: {count} ({count / total_free * 100:.1f}%)")

    # 4. Liveness fix distribution
    print(f"\n--- Liveness fixes ---")
    fix_by_proc = defaultdict(int)
    for key, out_val, dead_config in liveness_fixes:
        fix_by_proc[key[0]] += 1
        print(f"  Fix: P{key[0]}({key[1]},{key[2]},{key[3]})={out_val}, "
              f"dead={''.join(str(x) for x in dead_config)}")
    print(f"  By processor: {dict(sorted(fix_by_proc.items()))}")

    # 5. Privileged entries: which free entries become privileged?
    print(f"\n--- Privileged free entries by processor ---")
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        priv_free = []
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key in free_set and comp[key] != S:
                        priv_free.append((L, S, R, comp[key]))
        if priv_free:
            print(f"  P{p}: {len(priv_free)} privileged free entries")
            for L, S, R, out in priv_free:
                print(f"    f({L},{S},{R})={out}")


if __name__ == "__main__":
    for n_val in [9, 10, 11, 12]:
        t0 = time.time()
        data = build_system(n_val)
        if data is None:
            print(f"n={n_val}: construction failed")
            continue
        print(f"Built n={n_val} in {time.time() - t0:.1f}s")
        analyze_tables(data)
