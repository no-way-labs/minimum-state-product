#!/usr/bin/env python3
"""Analyze dead configs and good config structure.

Key questions:
1. What are the n-3 dead configs? Is there a pattern?
2. What is the structure of the good set (cycle + tail)?
3. Which processor gets the liveness fix at each dead config?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict


def build_bounce_cycle(ms, n):
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step + 1]
        if nc in visited:
            raise RuntimeError("Revisited")
        visited.add(nc)
        cycle.append(nc)
    raise RuntimeError("Cycle didn't close")


def build_greedy(n):
    ms = tuple([2] + [3] * (n - 2) + [2])
    cycle, movers = build_bounce_cycle(ms, n)
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good_set = set(c for c in all_configs if c not in good_set)

    config_index = defaultdict(list)
    for c in all_configs:
        if c not in good_set:
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                config_index[(p, L, S, R)].append(c)

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

    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = 0
        matching = config_index[(p, L, S, R)]
        for out in range(ms[p]):
            ng = 0
            good_count = 0
            if out != S:
                for c in matching:
                    new_c = tuple(c[j] if j != p else out for j in range(n))
                    if new_c in good_set:
                        good_count += 1
                    elif new_c in non_good_set:
                        ng += 1
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    return ms, comp, det, cycle, movers, free_entries, all_configs


def find_dead_configs(ms, comp, all_configs, n):
    dead = []
    for c in all_configs:
        has_priv = False
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            if comp.get((p, L, S, R), S) != S:
                has_priv = True
                break
        if not has_priv:
            dead.append(c)
    return dead


def main():
    print("DEAD CONFIG ANALYSIS")
    print("=" * 80)

    for nv in range(4, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break

        ms, comp, det, cycle, movers, free_entries, all_configs = build_greedy(nv)
        n = nv
        dead = find_dead_configs(ms, comp, all_configs, n)

        print(f"\nn={nv}: {len(dead)} dead configs")
        for c in dead:
            # Show the config as a string with each proc value
            c_str = ','.join(str(x) for x in c)
            # Which procs are boundary? P0 and P_{n-1}
            # Show d-vector: d_i = (c_{i+1} - c_i) % 3 for ternary
            d_vec = []
            for i in range(n):
                d_vec.append((c[(i + 1) % n] - c[i]) % 3)
            d_str = ','.join(str(d) for d in d_vec)
            print(f"  ({c_str})  d=({d_str})")

            # For each proc, show why it's not privileged
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                out = comp.get(key, S)
                is_det = key in det
                print(f"    P{p}: f({L},{S},{R})={out} {'D' if is_det else 'F'} "
                      f"{'PRIV' if out != S else 'stay'}")

    # Look for pattern in dead configs
    print("\n\nPATTERN SEARCH")
    print("-" * 60)
    for nv in range(4, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        ms, comp, det, cycle, movers, free_entries, all_configs = build_greedy(nv)
        dead = find_dead_configs(ms, comp, all_configs, nv)
        print(f"n={nv}: dead = {[tuple(c) for c in dead]}")


if __name__ == "__main__":
    main()
