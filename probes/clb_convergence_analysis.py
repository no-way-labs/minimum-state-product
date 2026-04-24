#!/usr/bin/env python3
"""clb_convergence_analysis.py — Study convergence structure.

For each n=5..13:
1. Maximum convergence path length (longest chain bad -> good)
2. Average convergence path length
3. Which bad configs are hardest to converge?
4. Distribution of convergence depths
5. Look for potential functions
"""

import sys
import os
import time
from collections import defaultdict

sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian


def build_system(n):
    ms = tuple([2] + [3] * (n - 2) + [2])
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
    non_good_set = set(c for c in all_configs if c not in good_set)

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

    triple_index = defaultdict(list)
    non_good = [c for c in all_configs if c not in good_set]
    for c in non_good:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in free_set:
                triple_index[key].append(c)

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

    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n))
        if not has_priv:
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if key not in det:
                    for out in range(ms[p]):
                        if out != c[p]:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]

    # Find verified good set
    from verifier import verify_system
    result = verify_system(list(ms), fs, verbose=False)
    if not result['valid']:
        return None

    return {
        'n': n, 'ms': ms, 'fs': fs, 'comp': comp,
        'good_set': result['good_configs'],
        'cycle': result['cycle'],
        'all_configs': all_configs,
    }


def analyze_convergence(sys_data):
    n = sys_data['n']
    ms = sys_data['ms']
    fs = sys_data['fs']
    good_set = sys_data['good_set']
    all_configs = sys_data['all_configs']

    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)

    print(f"\nn={n}: {len(bad_configs)} bad configs, {len(good_set)} good")

    # Compute convergence depth for each bad config
    # depth[c] = min steps to reach good (under worst-case daemon)
    # = max over all successors of (1 + depth[successor])
    # This is the "worst-case convergence time"

    # Alternative: BFS from good boundary (configs that have a
    # direct transition to good). Work backwards.

    # For each bad config, compute ALL successors
    bad_succs = {}
    for c in bad_configs:
        succs = []
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            new_S = fs[p](L, S, R)
            if new_S != S:
                new_c = c[:p] + (new_S,) + c[p + 1:]
                succs.append(new_c)
        bad_succs[c] = succs

    # Split successors into good and bad
    bad_bad_succs = {}  # successors that stay in bad
    reaches_good = {}  # True if some successor goes to good
    for c in bad_configs:
        bb = [s for s in bad_succs[c] if s in bad_set]
        bg = [s for s in bad_succs[c] if s in good_set]
        bad_bad_succs[c] = bb
        reaches_good[c] = len(bg) > 0

    # Worst-case depth: max over all bad successors of (1 + depth[succ])
    # Computed via iterative fixpoint
    depth = {}  # c -> worst-case steps to reach good

    # Initialize: configs with no bad successors have depth 1
    # (they must reach good in 1 step)
    changed = True
    iteration = 0
    while changed:
        changed = False
        for c in bad_configs:
            if c in depth:
                continue
            bbs = bad_bad_succs[c]
            if len(bbs) == 0:
                # All successors go to good
                depth[c] = 1
                changed = True
            elif all(s in depth for s in bbs):
                # Worst case: daemon picks the longest bad successor
                d = max(depth[s] for s in bbs) + 1
                depth[c] = d
                changed = True
        iteration += 1

    if len(depth) != len(bad_configs):
        print(f"  WARNING: {len(bad_configs) - len(depth)} configs without depth!")
        return

    depths = list(depth.values())
    max_depth = max(depths)
    avg_depth = sum(depths) / len(depths)
    median_depth = sorted(depths)[len(depths) // 2]

    print(f"  Worst-case convergence depth:")
    print(f"    Max: {max_depth}")
    print(f"    Average: {avg_depth:.2f}")
    print(f"    Median: {median_depth}")

    # Depth distribution
    dist = defaultdict(int)
    for d in depths:
        dist[d] += 1
    print(f"  Depth distribution:")
    for d in sorted(dist.keys()):
        bar = '#' * min(50, dist[d] * 50 // max(dist.values()))
        print(f"    depth={d:3d}: {dist[d]:7d} configs {bar}")

    # Hardest configs (largest depth)
    hardest = sorted(depth.items(), key=lambda x: -x[1])[:5]
    print(f"  Hardest configs (largest worst-case depth):")
    for c, d in hardest:
        print(f"    {''.join(str(x) for x in c)}: depth={d}")

    # Best-case depth (minimum over daemon choices)
    best_depth = {}
    changed = True
    while changed:
        changed = False
        for c in bad_configs:
            if c in best_depth:
                continue
            bbs = bad_bad_succs[c]
            if len(bbs) == 0:
                best_depth[c] = 1
                changed = True
            else:
                # Best case: try bad successors that have been resolved
                resolved = [s for s in bbs if s in best_depth]
                if resolved:
                    # Best case: daemon picks shortest, or goes to good
                    d = min(best_depth[s] for s in resolved) + 1
                    if reaches_good[c]:
                        d = 1
                    best_depth[c] = d
                    changed = True
                elif reaches_good[c]:
                    best_depth[c] = 1
                    changed = True

    if len(best_depth) == len(bad_configs):
        best_depths = list(best_depth.values())
        print(f"  Best-case convergence depth:")
        print(f"    Max: {max(best_depths)}, Avg: {sum(best_depths) / len(best_depths):.2f}")

    # Potential function analysis
    # Check if sum of states is monotonically decreasing
    print(f"\n  Potential function analysis:")
    # Try: Hamming distance to nearest good config
    # Try: sum of states
    # Try: some weighted combination

    potentials = {
        'sum': lambda c: sum(c),
        'max': lambda c: max(c),
        'hamming_zero': lambda c: sum(1 for x in c if x != 0),
    }

    for pname, pfn in potentials.items():
        violations = 0
        total_transitions = 0
        for c in bad_configs:
            pc = pfn(c)
            for s in bad_succs[c]:
                ps = pfn(s)
                total_transitions += 1
                if s in bad_set and ps >= pc:
                    violations += 1
        pct = violations / total_transitions * 100 if total_transitions > 0 else 0
        print(f"    {pname}: {violations}/{total_transitions} non-decreasing "
              f"({pct:.1f}%)")

    return {
        'max_depth': max_depth,
        'avg_depth': avg_depth,
        'median_depth': median_depth,
    }


if __name__ == "__main__":
    results = []
    for n_val in range(5, 14):
        t0 = time.time()
        data = build_system(n_val)
        if data is None:
            print(f"n={n_val}: construction failed")
            continue
        build_time = time.time() - t0
        print(f"Built n={n_val} in {build_time:.1f}s")
        r = analyze_convergence(data)
        if r:
            r['n'] = n_val
            results.append(r)
        print(f"  Analysis time: {time.time() - t0 - build_time:.1f}s")

    # Summary
    print(f"\n{'=' * 70}")
    print("CONVERGENCE DEPTH SUMMARY")
    print(f"{'=' * 70}")
    print(f"{'n':>3} {'max_depth':>10} {'avg_depth':>10} {'median':>10}")
    for r in results:
        print(f"{r['n']:>3} {r['max_depth']:>10} {r['avg_depth']:>10.2f} "
              f"{r['median_depth']:>10}")

    # Check for patterns
    print(f"\nMax depth pattern check:")
    for r in results:
        nv = r['n']
        md = r['max_depth']
        print(f"  n={nv}: max_depth={md}, "
              f"n^2={nv ** 2}, 2n={2 * nv}, 3n={3 * nv}")
