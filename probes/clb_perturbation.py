#!/usr/bin/env python3
"""clb_perturbation.py — Explore the boundary of failure.

Test what perturbations break the construction:
1. Different tiebreakers (minimize total edges vs non-good->non-good)
2. Different free entry processing orders
3. Different bounce cycle patterns
4. How many valid completions exist?
"""

import sys
import os
import time
import random
from collections import defaultdict

sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


def build_bounce_cycle(ms, n, pattern):
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = pattern * (n + 5)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step + 1]
        if nc in visited:
            return None, None
        visited.add(nc)
        cycle.append(nc)
    return None, None


def build_completion(ms, n, cycle, movers, strategy='good_targeting',
                     entry_order='default', seed=42):
    """Build completion with specified strategy and entry order."""
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
            det[key] = c_next[p] if p == mv else S

    free_entries = []
    free_set = set()
    for p in range(n):
        for L in range(ms[(p - 1) % n]):
            for S in range(ms[p]):
                for R in range(ms[(p + 1) % n]):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)
                        free_set.add(key)

    # Pre-index
    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in free_set:
                triple_index[key].append(c)

    # Reorder entries
    if entry_order == 'default':
        ordered = list(free_entries)
    elif entry_order == 'reverse':
        ordered = list(reversed(free_entries))
    elif entry_order == 'random':
        ordered = list(free_entries)
        random.seed(seed)
        random.shuffle(ordered)
    elif entry_order == 'by_matching':
        ordered = sorted(free_entries,
                         key=lambda k: len(triple_index.get(k, [])),
                         reverse=True)
    else:
        ordered = list(free_entries)

    # Compute edge costs
    edge_costs = {}
    comp = dict(det)

    for key in ordered:
        p, L, S, R = key
        matching = triple_index.get(key, [])

        if strategy == 'good_targeting':
            best_out = S
            best_good = 0
            best_ng = 0
            for out in range(ms[p]):
                if out == S:
                    edge_costs[(key, out)] = 0
                    continue
                gc = ng = 0
                for c in matching:
                    t = c[:p] + (out,) + c[p + 1:]
                    if t in good_set:
                        gc += 1
                    elif t in non_good_set:
                        ng += 1
                edge_costs[(key, out)] = ng
                if gc > best_good or (gc == best_good and ng < best_ng):
                    best_out = out
                    best_good = gc
                    best_ng = ng
            comp[key] = best_out

        elif strategy == 'min_edges_only':
            # Only minimize non-good->non-good edges, ignore good targeting
            best_out = S
            best_ng = 0
            for out in range(ms[p]):
                if out == S:
                    edge_costs[(key, out)] = 0
                    continue
                ng = sum(1 for c in matching
                         if c[:p] + (out,) + c[p + 1:] in non_good_set)
                edge_costs[(key, out)] = ng
                if ng < best_ng or (ng == best_ng and out < best_out):
                    best_out = out
                    best_ng = ng
            comp[key] = best_out

        elif strategy == 'good_only':
            # Only maximize good targeting, ignore edge cost
            best_out = S
            best_good = 0
            for out in range(ms[p]):
                if out == S:
                    edge_costs[(key, out)] = 0
                    continue
                gc = sum(1 for c in matching
                         if c[:p] + (out,) + c[p + 1:] in good_set)
                edge_costs[(key, out)] = 0
                if gc > best_good:
                    best_out = out
                    best_good = gc
            comp[key] = best_out

        elif strategy == 'identity':
            # All free entries = identity (no privilege)
            comp[key] = S
            for out in range(ms[p]):
                edge_costs[(key, out)] = 0

        elif strategy == 'random':
            random.seed(seed + hash(key))
            choices = list(range(ms[p]))
            comp[key] = random.choice(choices)
            for out in range(ms[p]):
                edge_costs[(key, out)] = 0

    # Liveness fix
    fixes = 0
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n))
        if not has_priv:
            best_key = None
            best_cost = float('inf')
            best_val = None
            for p in range(n):
                key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if key not in det:
                    for out in range(ms[p]):
                        if out != c[p]:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_val = out
            if best_key:
                comp[best_key] = best_val
                fixes += 1

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return list(ms), fs, fixes


if __name__ == "__main__":
    n = 9
    ms = tuple([2] + [3] * (n - 2) + [2])

    print("=" * 70)
    print(f"Perturbation analysis: n={n}, ms={ms}")
    print("=" * 70)

    # === Test 1: Different strategies ===
    print(f"\n--- Test 1: Different completion strategies ---")
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    cycle, movers = build_bounce_cycle(ms, n, up_down)

    strategies = ['good_targeting', 'min_edges_only', 'good_only',
                  'identity', 'random']
    for strat in strategies:
        t0 = time.time()
        ms_list, fs, fixes = build_completion(
            ms, n, cycle, movers, strategy=strat)
        result = verify_system(ms_list, fs, verbose=False)
        elapsed = time.time() - t0
        status = 'VALID' if result['valid'] else 'FAILED'
        info = ''
        if result['valid']:
            info = f"good={len(result['good_configs'])}"
        else:
            for k, (ok, msg) in result.get('properties', {}).items():
                if not ok:
                    info = f"{k}: {msg}"
                    break
        print(f"  {strat:20s}: {status} ({info}) [{elapsed:.1f}s]")

    # === Test 2: Different entry orderings ===
    print(f"\n--- Test 2: Different entry orderings ---")
    orderings = ['default', 'reverse', 'by_matching']
    for _ in range(5):
        orderings.append('random')

    for i, order in enumerate(orderings):
        seed = 42 + i
        t0 = time.time()
        ms_list, fs, fixes = build_completion(
            ms, n, cycle, movers, strategy='good_targeting',
            entry_order=order, seed=seed)
        result = verify_system(ms_list, fs, verbose=False)
        elapsed = time.time() - t0
        status = 'VALID' if result['valid'] else 'FAILED'
        info = ''
        if result['valid']:
            info = f"good={len(result['good_configs'])}, fixes={fixes}"
        else:
            for k, (ok, msg) in result.get('properties', {}).items():
                if not ok:
                    info = f"{k}: {msg}"
                    break
        tag = f"{order}(seed={seed})" if order == 'random' else order
        print(f"  {tag:25s}: {status} ({info}) [{elapsed:.1f}s]")

    # === Test 3: Different bounce patterns ===
    print(f"\n--- Test 3: Different bounce patterns ---")
    patterns = {
        'up-down [0..n-1,n-2..1]': list(range(n)) + list(range(n - 2, 0, -1)),
        'down-up [n-1..0,1..n-2]': list(range(n - 1, -1, -1)) + list(range(1, n - 1)),
        'up-down-full [0..n-1,n-2..0]': list(range(n)) + list(range(n - 2, -1, -1)),
        'up-down-skip [0..n-1,n-3..1]': list(range(n)) + list(range(n - 3, 0, -1)),
    }

    for pname, pattern in patterns.items():
        cyc, mvrs = build_bounce_cycle(ms, n, pattern)
        if cyc is None:
            print(f"  {pname:40s}: cycle didn't close")
            continue
        t0 = time.time()
        ms_list, fs, fixes = build_completion(
            ms, n, cyc, mvrs, strategy='good_targeting')
        result = verify_system(ms_list, fs, verbose=False)
        elapsed = time.time() - t0
        status = 'VALID' if result['valid'] else 'FAILED'
        info = ''
        if result['valid']:
            info = f"cycle={len(cyc)}, good={len(result['good_configs'])}"
        else:
            for k, (ok, msg) in result.get('properties', {}).items():
                if not ok:
                    info = f"{k}: {msg}"
                    break
        print(f"  {pname:40s}: {status} ({info}) [{elapsed:.1f}s]")

    # === Test 4: How many valid completions? ===
    print(f"\n--- Test 4: Random good-targeting variants ---")
    # Try many random orderings and count valid ones
    valid_count = 0
    total_trials = 50
    for trial in range(total_trials):
        ms_list, fs, fixes = build_completion(
            ms, n, cycle, movers, strategy='good_targeting',
            entry_order='random', seed=trial * 137)
        result = verify_system(ms_list, fs, verbose=False)
        if result['valid']:
            valid_count += 1
    print(f"  Random orderings: {valid_count}/{total_trials} valid "
          f"({valid_count / total_trials * 100:.0f}%)")

    # === Test 5: Multi-n pattern check ===
    print(f"\n--- Test 5: Strategy comparison across n ---")
    for n_val in [5, 7, 9, 11]:
        ms_val = tuple([2] + [3] * (n_val - 2) + [2])
        up_down_val = list(range(n_val)) + list(range(n_val - 2, 0, -1))
        cyc_val, mvrs_val = build_bounce_cycle(ms_val, n_val, up_down_val)
        if cyc_val is None:
            continue
        print(f"\n  n={n_val}:")
        for strat in ['good_targeting', 'good_only', 'min_edges_only']:
            ms_list, fs, fixes = build_completion(
                ms_val, n_val, cyc_val, mvrs_val, strategy=strat)
            result = verify_system(ms_list, fs, verbose=False)
            status = 'VALID' if result['valid'] else 'FAILED'
            print(f"    {strat:20s}: {status}")
