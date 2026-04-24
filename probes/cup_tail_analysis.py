#!/usr/bin/env python3
"""CUP: Analyze tail structure — good configs NOT on the cycle."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict


def sol3_v1_rules(ms, n):
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def get_privileged(c, fs, n):
    priv = []
    for i in range(n):
        L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(c, i, fs, n):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    lst = list(c); lst[i] = fs[i](L, S, R); return tuple(lst)


def analyze_tails(n):
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    cycle_set = set(result['cycle'])
    tail_set = good_set - cycle_set

    print(f"\nn={n}: cycle={len(cycle_set)}, tails={len(tail_set)}, "
          f"good={len(good_set)}, expected_tails={5*n-8}")

    # Build successor map for good configs
    succ_map = {}
    for c in good_set:
        priv = get_privileged(c, fs, n)
        assert len(priv) == 1, f"Bad privilege count {len(priv)} for good config {c}"
        succ_map[c] = (apply_move(c, priv[0], fs, n), priv[0])

    # Build tree structure: for each tail config, trace to cycle
    tail_depths = {}
    for c in tail_set:
        path = [c]
        cur = c
        while cur not in cycle_set:
            cur, _ = succ_map[cur]
            path.append(cur)
        tail_depths[c] = len(path) - 1  # steps to reach cycle

    max_depth = max(tail_depths.values()) if tail_depths else 0
    print(f"  Max tail depth: {max_depth}")

    # Print tail configs grouped by depth
    by_depth = defaultdict(list)
    for c, d in tail_depths.items():
        by_depth[d].append(c)

    for d in sorted(by_depth.keys()):
        configs = by_depth[d]
        print(f"  Depth {d}: {len(configs)} configs")
        if n <= 6:
            for c in sorted(configs):
                priv = get_privileged(c, fs, n)
                succ, mover = succ_map[c]
                on_cycle = "→cycle" if succ in cycle_set else f"→tail_d{tail_depths.get(succ, '?')}"
                print(f"    {c} P{mover}→ {succ} {on_cycle}")

    # Characterize tail configs: what patterns do they have?
    # Check if tail configs are "step functions" with 2 values
    print(f"\n  Tail config patterns:")
    patterns = defaultdict(list)
    for c in tail_set:
        # Check if step function (single boundary in interior)
        vals = sorted(set(c))
        nvals = len(vals)
        # Count boundaries (adjacent different values, linear not circular)
        linear_boundaries = sum(1 for i in range(n-1) if c[i] != c[i+1])
        ring_boundaries = linear_boundaries + (1 if c[n-1] != c[0] else 0)
        key = f"vals={nvals},lin_bnd={linear_boundaries},ring_bnd={ring_boundaries}"
        patterns[key].append(c)

    for key in sorted(patterns.keys()):
        configs = patterns[key]
        print(f"    {key}: {len(configs)} configs")
        if len(configs) <= 5 and n <= 6:
            for c in sorted(configs):
                print(f"      {c}")


def verify_tail_count_formula(max_n=13):
    """Verify: tail count = 5n-8 for n >= 4."""
    print("="*60)
    print("TAIL COUNT FORMULA VERIFICATION")
    print("="*60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        assert result['valid']
        cycle_len = result['cycle_length']
        good_count = len(result['good_configs'])
        tail_count = good_count - cycle_len
        expected = 5 * n - 8
        ok = tail_count == expected
        print(f"  n={n}: tails={tail_count}, expected 5n-8={expected} {'✓' if ok else '✗'}")


if __name__ == "__main__":
    verify_tail_count_formula(13)
    for n in [3, 4, 5, 6]:
        analyze_tails(n)
