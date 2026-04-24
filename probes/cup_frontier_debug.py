#!/usr/bin/env python3
"""Debug: verify that middle moves always give frontier change 0 or -2.
If -1 appears, trace the exact case."""

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


def get_d_vector(c, n):
    """Return d[0..n-1] where d[i] = (c[(i+1)%n] - c[i]) % 3."""
    return tuple((c[(i+1)%n] - c[i]) % 3 for i in range(n))


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1)%n] - c[i]) % 3 != 0)


def debug_middle_moves(n):
    """Find and trace all middle moves with frontier change != 0, -2."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    configs = list(cartesian(*(range(m) for m in ms)))

    anomalous = []
    for c in configs:
        priv = get_privileged(c, fs, n)
        for p in priv:
            if p == 0 or p == n - 1:
                continue  # skip bottom/top
            succ = apply_move(c, p, fs, n)
            fc_before = frontier_count(c, n)
            fc_after = frontier_count(succ, n)
            delta = fc_after - fc_before
            if delta not in (0, -2):
                d_before = get_d_vector(c, n)
                d_after = get_d_vector(succ, n)
                anomalous.append((c, p, succ, delta, d_before, d_after))

    if anomalous:
        print(f"n={n}: {len(anomalous)} anomalous middle moves (Δ not in {{0, -2}}):")
        for c, p, s, delta, db, da in anomalous[:10]:
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            new_S = s[p]
            print(f"  {c} P{p} (L={L},S={S},R={R})→S'={new_S} → {s}")
            print(f"    d_before={db}, d_after={da}, Δfrontiers={delta}")
            # Show which positions changed
            for i in range(n):
                if db[i] != da[i]:
                    print(f"    d[{i}]: {db[i]} → {da[i]}")
    else:
        print(f"n={n}: All middle moves have Δ ∈ {{0, -2}}. ✓")


def analyze_bottom_top_detailed(n):
    """For bottom/top, analyze frontier change patterns in detail.
    Key: what is the d-vector pattern around the boundary?"""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    print(f"\nn={n}: Detailed bottom/top analysis")

    for mtype, midx in [("BOTTOM", 0), ("TOP", n-1)]:
        cases = defaultdict(list)
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            if midx not in priv:
                continue
            succ = apply_move(c, midx, fs, n)
            fc_b = frontier_count(c, n)
            fc_a = frontier_count(succ, n)
            delta = fc_a - fc_b
            d_b = get_d_vector(c, n)
            d_a = get_d_vector(succ, n)

            # Characterize the local d-pattern around boundary
            if midx == 0:
                # Bottom: affects d_{n-1} and d_0
                local = (d_b[n-1], d_b[0])
                local_a = (d_a[n-1], d_a[0])
            else:
                # Top: affects d_{n-2} and d_{n-1}
                local = (d_b[n-2], d_b[n-1])
                local_a = (d_a[n-2], d_a[n-1])

            cases[(mtype, delta, local, local_a)].append(c)

        print(f"\n  {mtype} move patterns:")
        for (mt, delta, local, local_a), cfgs in sorted(cases.items()):
            print(f"    Δ={delta:+d}: local {local} → {local_a}: {len(cfgs)} cases")
            if len(cfgs) <= 3 and n <= 6:
                for c in cfgs:
                    d = get_d_vector(c, n)
                    print(f"      {c}  d={d}")


def study_bad_cycle_obstruction(n):
    """Try to find what prevents bad cycles.
    In a bad cycle, the total frontier change must be 0.
    Middle moves give 0 or -2.
    So bottom/top must compensate with positive changes.
    But each bottom/top move is bounded.

    Key insight: in any bad cycle, count the TYPES of moves.
    Let m_mid = number of middle moves, m_bot = bottom moves, m_top = top moves.
    Total frontier change: Σ Δ_i = 0.

    Middle: each gives 0 or -2. So total from middle ≤ 0.
    For total to be 0: total from bottom/top must be ≥ 0.
    But bottom gives at most +2 per move (creating 2 frontiers).
    Top gives exactly +2 per move that creates (and 0 for non-creating).
    """
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build bad→bad graph
    bad_graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                bad_graph[c].append((p, succ))

    # Check: is there ANY cycle in bad→bad graph?
    # Use DFS-based cycle detection
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in bad_set}
    cycle_found = False

    def dfs(v):
        nonlocal cycle_found
        color[v] = GRAY
        for p, w in bad_graph[v]:
            if color[w] == GRAY:
                cycle_found = True
                return
            if color[w] == WHITE:
                dfs(w)
                if cycle_found:
                    return
        color[v] = BLACK

    sys.setrecursionlimit(100000)
    for c in bad_set:
        if color[c] == WHITE:
            dfs(c)
            if cycle_found:
                break

    if cycle_found:
        print(f"n={n}: BAD CYCLE EXISTS! System is NOT self-stabilizing!")
    else:
        print(f"n={n}: No bad cycles. ✓")

    # Also check: for each bad config, is there at least one exit to good?
    has_exit = 0
    no_exit = []
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        exits = False
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in good_set:
                exits = True
                break
        if exits:
            has_exit += 1
        else:
            no_exit.append(c)

    print(f"  {has_exit}/{len(bad_set)} bad configs have direct exit to good.")
    if no_exit:
        print(f"  {len(no_exit)} configs with NO direct exit (all moves → bad):")
        if len(no_exit) <= 10:
            for c in sorted(no_exit):
                for p, s in bad_graph[c]:
                    print(f"    {c} P{p}→ {s}")


def find_longest_bad_chain(n):
    """Find the longest path in the bad→bad DAG (it's a DAG since no cycles)."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build bad→bad graph
    bad_graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                bad_graph[c].append((p, succ))

    # Topological sort + longest path
    # First compute in-degrees
    in_degree = defaultdict(int)
    for c in bad_set:
        if c not in in_degree:
            in_degree[c] = 0
        for p, s in bad_graph[c]:
            in_degree[s] += 1

    # BFS topological sort
    from collections import deque
    queue = deque()
    for c in bad_set:
        if in_degree[c] == 0:
            queue.append(c)

    longest = {}
    order = []
    while queue:
        c = queue.popleft()
        order.append(c)
        if c not in longest:
            longest[c] = 0
        for p, s in bad_graph[c]:
            longest[s] = max(longest.get(s, 0), longest[c] + 1)
            in_degree[s] -= 1
            if in_degree[s] == 0:
                queue.append(s)

    if longest:
        max_len = max(longest.values())
        max_configs = [c for c, l in longest.items() if l == max_len]
        print(f"\nn={n}: Longest bad→bad chain: {max_len}")
        print(f"  Deepest configs: {len(max_configs)}")
        if max_configs and n <= 6:
            for c in sorted(max_configs)[:5]:
                d = get_d_vector(c, n)
                print(f"    {c} d={d}")


if __name__ == "__main__":
    print("=" * 60)
    print("MIDDLE MOVE ANOMALY CHECK")
    print("=" * 60)
    for nv in [3, 4, 5, 6]:
        debug_middle_moves(nv)

    print("\n" + "=" * 60)
    print("BAD CYCLE OBSTRUCTION ANALYSIS")
    print("=" * 60)
    for nv in range(3, 10):
        study_bad_cycle_obstruction(nv)

    print("\n" + "=" * 60)
    print("LONGEST BAD→BAD CHAINS")
    print("=" * 60)
    for nv in range(3, 10):
        find_longest_bad_chain(nv)

    print("\n" + "=" * 60)
    print("DETAILED BOTTOM/TOP PATTERNS")
    print("=" * 60)
    for nv in [4, 5]:
        analyze_bottom_top_detailed(nv)
