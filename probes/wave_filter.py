"""
Wave-filter analysis for self-stabilizing token rings.

DEK's intuition (Haddad-Knuth p.76): one wants processors that filter
k-waves down to ceil(k/2)-waves on every lap around the ring. The floor
version goes dead; the ceiling version is the hard direction.

A "wave" is a contiguous run of privileged processors. In a bad configuration,
there may be multiple waves circulating. Self-stabilization requires that
waves merge/annihilate until only one token remains.

This module:
1. Analyzes wave structure in configurations
2. Tracks wave evolution through transitions
3. Studies how different state counts affect wave dynamics
"""

import itertools
from typing import List, Tuple, Set, Dict
from collections import Counter, defaultdict
from verifier import verify_system, privileged_set, apply_move


def wave_analysis(config: Tuple[int, ...], fs: List, ms: List[int]) -> dict:
    """
    Analyze the wave structure of a configuration.

    A "wave" is a maximal contiguous run of privileged processors.
    """
    n = len(ms)
    priv = privileged_set(config, fs, ms)
    priv_set = set(priv)

    if not priv:
        return {'num_waves': 0, 'waves': [], 'num_privileged': 0}

    # Find contiguous runs of privileged processors (on the ring)
    waves = []
    visited = set()

    for start in priv:
        if start in visited:
            continue
        # Extend the wave
        wave = [start]
        visited.add(start)
        # Extend right
        pos = (start + 1) % n
        while pos in priv_set and pos not in visited:
            wave.append(pos)
            visited.add(pos)
            pos = (pos + 1) % n
        # Extend left
        pos = (start - 1) % n
        while pos in priv_set and pos not in visited:
            wave.insert(0, pos)
            visited.add(pos)
            pos = (pos - 1) % n
        waves.append(wave)

    return {
        'num_waves': len(waves),
        'waves': waves,
        'wave_sizes': [len(w) for w in waves],
        'num_privileged': len(priv),
    }


def trace_wave_evolution(config: Tuple[int, ...], fs: List, ms: List[int],
                         max_steps: int = 100) -> list:
    """
    Trace how waves evolve under daemon choices.

    For each step, show the wave structure before and after a move.
    Uses round-robin daemon (each privileged processor moves in order).
    """
    n = len(ms)
    trace = []
    current = config
    seen = set()

    for step in range(max_steps):
        if current in seen:
            trace.append(('CYCLE', current))
            break
        seen.add(current)

        wa = wave_analysis(current, fs, ms)
        priv = privileged_set(current, fs, ms)

        if len(priv) == 1:
            trace.append(('GOOD', current, wa))
            break

        # Move the first privileged processor (deterministic for analysis)
        mover = priv[0]
        next_config = apply_move(current, mover, fs, ms)
        trace.append(('MOVE', current, wa, mover, next_config))
        current = next_config

    return trace


def wave_statistics(ms: List[int], fs: List, verbose: bool = True) -> dict:
    """
    Compute wave statistics across all configurations.
    """
    n = len(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    stats = {
        'wave_count_dist': Counter(),
        'priv_count_dist': Counter(),
        'total_configs': len(configs),
    }

    for c in configs:
        wa = wave_analysis(c, fs, ms)
        stats['wave_count_dist'][wa['num_waves']] += 1
        stats['priv_count_dist'][wa['num_privileged']] += 1

    if verbose:
        print(f"Wave statistics for ms={ms}:")
        print(f"  Total configs: {stats['total_configs']}")
        print(f"  Wave count distribution:")
        for k in sorted(stats['wave_count_dist'].keys()):
            cnt = stats['wave_count_dist'][k]
            print(f"    {k} waves: {cnt} configs ({100*cnt/stats['total_configs']:.1f}%)")
        print(f"  Privileged count distribution:")
        for k in sorted(stats['priv_count_dist'].keys()):
            cnt = stats['priv_count_dist'][k]
            print(f"    {k} privileged: {cnt} configs ({100*cnt/stats['total_configs']:.1f}%)")

    return stats


def convergence_depth(ms: List[int], fs: List, verbose: bool = True) -> dict:
    """
    For each bad config, compute the worst-case number of steps to reach
    a good config (convergence time).
    """
    n = len(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))
    result = verify_system(ms, fs)

    if not result['valid']:
        return {'valid': False}

    good_set = result['good_configs']
    bad_configs = [c for c in configs if c not in good_set]

    # BFS from good configs backwards through the nondeterministic transition graph
    # to find the depth of each bad config
    depth = {c: 0 for c in good_set}
    frontier = list(good_set)

    # Build reverse transition graph: for each config, what configs can reach it?
    # Forward: from c, privileged processor i can move to c'
    reverse = defaultdict(set)
    for c in configs:
        priv = privileged_set(c, fs, ms)
        for i in priv:
            c_next = apply_move(c, i, fs, ms)
            reverse[c_next].add(c)

    # For convergence depth, we need the WORST case.
    # A bad config c has depth = 1 + max(depth(successor)) over all its possible successors
    # But some successors might be good (depth 0).
    # Actually, convergence depth should be: max over all daemon strategies of path length.

    # Compute via backward BFS: depth[c] = min distance from c to any good config
    # under best daemon. For worst daemon: max over successor depths + 1.

    # Let's compute worst-case depth via dynamic programming on the DAG.
    # Since there are no bad cycles, the bad-config graph is a DAG.

    # Topological sort of bad configs
    # Forward edges: from c, each privileged processor gives a successor
    forward = defaultdict(list)
    for c in bad_configs:
        priv = privileged_set(c, fs, ms)
        for i in priv:
            c_next = apply_move(c, i, fs, ms)
            forward[c].append(c_next)

    # Worst-case depth: for each bad config, the maximum over all successors
    # of (1 + worst_depth(successor)), where good configs have depth 0.
    worst_depth = {c: 0 for c in good_set}
    # Process in reverse topological order
    # Since no bad cycles, we can compute iteratively
    changed = True
    for c in bad_configs:
        worst_depth[c] = 0  # Initialize

    for _ in range(len(bad_configs) + 1):
        changed = False
        for c in bad_configs:
            max_d = 0
            for succ in forward[c]:
                d = worst_depth.get(succ, 0) + 1
                max_d = max(max_d, d)
            if max_d != worst_depth[c]:
                worst_depth[c] = max_d
                changed = True
        if not changed:
            break

    bad_depths = {c: worst_depth[c] for c in bad_configs}
    max_depth = max(bad_depths.values()) if bad_depths else 0

    if verbose:
        print(f"Convergence analysis for ms={ms}:")
        print(f"  Good configs: {len(good_set)}")
        print(f"  Bad configs: {len(bad_configs)}")
        print(f"  Max convergence depth (worst daemon): {max_depth}")
        depth_dist = Counter(bad_depths.values())
        for d in sorted(depth_dist.keys()):
            print(f"    Depth {d}: {depth_dist[d]} configs")

    return {
        'max_depth': max_depth,
        'depth_dist': depth_dist,
        'bad_depths': bad_depths,
    }


if __name__ == "__main__":
    from targeted_search import dijkstra_s3_bottom, dijkstra_s3_top, dijkstra_s3_middle

    print("=" * 60)
    print("WAVE-FILTER ANALYSIS")
    print("=" * 60)

    # Analyze Dijkstra Solution 3 for n=5
    print("\n--- Dijkstra S3, n=5, ms=(3,3,3,3,3) ---")
    ms_s3 = [3, 3, 3, 3, 3]
    fs_s3 = [dijkstra_s3_bottom] + [dijkstra_s3_middle] * 3 + [dijkstra_s3_top]
    wave_statistics(ms_s3, fs_s3)
    conv = convergence_depth(ms_s3, fs_s3)

    # Analyze the product-96 system
    print("\n--- Product 96 system, n=5, ms=(2,2,2,3,4) ---")
    # Reconstruct the verified system
    ms_96 = [2, 2, 2, 3, 4]
    f_vals = {}
    f_vals.update({(0,0,0,0):1, (0,0,0,1):0, (0,0,1,0):1, (0,0,1,1):1,
                   (0,1,0,0):0, (0,1,0,1):0, (0,1,1,0):0, (0,1,1,1):0,
                   (0,2,0,0):0, (0,2,0,1):0, (0,2,1,0):0, (0,2,1,1):0,
                   (0,3,0,0):0, (0,3,0,1):0, (0,3,1,0):0, (0,3,1,1):0})
    f_vals.update({(1,0,0,0):0, (1,0,0,1):0, (1,0,1,0):0, (1,0,1,1):0,
                   (1,1,0,0):1, (1,1,0,1):1, (1,1,1,0):1, (1,1,1,1):1})
    f_vals.update({(2,0,0,0):0, (2,0,0,1):0, (2,0,0,2):1, (2,0,1,0):1, (2,0,1,1):0, (2,0,1,2):1,
                   (2,1,0,0):1, (2,1,0,1):0, (2,1,0,2):0, (2,1,1,0):1, (2,1,1,1):1, (2,1,1,2):0})
    f_vals.update({
        (3,0,0,0):0, (3,0,0,1):0, (3,0,0,2):1, (3,0,0,3):0,
        (3,0,1,0):1, (3,0,1,1):2, (3,0,1,2):1, (3,0,1,3):0,
        (3,0,2,0):0, (3,0,2,1):2, (3,0,2,2):2, (3,0,2,3):2,
        (3,1,0,0):1, (3,1,0,1):0, (3,1,0,2):2, (3,1,0,3):0,
        (3,1,1,0):1, (3,1,1,1):1, (3,1,1,2):1, (3,1,1,3):1,
        (3,1,2,0):2, (3,1,2,1):0, (3,1,2,2):2, (3,1,2,3):1})
    f_vals.update({
        (4,0,0,0):0, (4,0,0,1):0, (4,0,1,0):2, (4,0,1,1):1,
        (4,0,2,0):2, (4,0,2,1):2, (4,0,3,0):0, (4,0,3,1):1,
        (4,1,0,0):0, (4,1,0,1):1, (4,1,1,0):1, (4,1,1,1):1,
        (4,1,2,0):1, (4,1,2,1):0, (4,1,3,0):3, (4,1,3,1):0,
        (4,2,0,0):0, (4,2,0,1):0, (4,2,1,0):1, (4,2,1,1):1,
        (4,2,2,0):3, (4,2,2,1):0, (4,2,3,0):3, (4,2,3,1):0})

    def make_f(proc, vals):
        def f(L, S, R):
            return vals[(proc, L, S, R)]
        return f

    fs_96 = [make_f(i, f_vals) for i in range(5)]
    wave_statistics(ms_96, fs_96)
    conv_96 = convergence_depth(ms_96, fs_96)

    # Compare wave filtering behavior
    print("\n--- Wave filtering comparison ---")
    print("How many waves does each system have on average?")
    print("How quickly do waves merge?")

    # Trace a few high-wave configs through the S3 system
    print("\n--- Example wave traces (S3, n=5) ---")
    configs = list(itertools.product(*(range(3) for _ in range(5))))
    high_wave = [c for c in configs if wave_analysis(c, fs_s3, ms_s3)['num_waves'] >= 3]
    if high_wave:
        for c in high_wave[:2]:
            wa = wave_analysis(c, fs_s3, ms_s3)
            print(f"\n  Config {c}: {wa['num_waves']} waves, sizes={wa['wave_sizes']}")
            trace = trace_wave_evolution(c, fs_s3, ms_s3, max_steps=20)
            for entry in trace:
                if entry[0] == 'MOVE':
                    _, cfg, wa_info, mover, next_cfg = entry
                    print(f"    {cfg} [{wa_info['num_waves']}w] -> P{mover} -> {next_cfg}")
                elif entry[0] == 'GOOD':
                    _, cfg, wa_info = entry
                    print(f"    {cfg} [GOOD, 1 token]")
                elif entry[0] == 'CYCLE':
                    _, cfg = entry
                    print(f"    CYCLE at {cfg}")
