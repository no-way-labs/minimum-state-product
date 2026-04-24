#!/usr/bin/env python3
"""CUP: Prove no bad cycles exist.

Approach: Decompose into cases based on which boundary moves the cycle contains.
1. No top, no bottom → only middle → fc strictly decreases → no cycle.
2. No top, yes bottom → frontier propagation + bottom reflection → contradicts fc balance.
3. Yes top → top reset constrains cycle structure → contradicts return to start.
"""

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


def frontier_count(c, n):
    return sum(1 for i in range(n) if (c[(i+1) % n] - c[i]) % 3 != 0)


def get_d_vector(c, n):
    return tuple((c[(i+1)%n] - c[i]) % 3 for i in range(n))


# ========= CASE 1: Middle-only cycle impossible =========

def verify_case1(max_n=10):
    """Case 1: If only middle moves, fc strictly decreases.
    Proof: Middle moves give Δfc ∈ {-2, -1, 0}.
    For cycle: Σ Δfc = 0, so ALL middle moves must be Δfc=0 (shift).
    But in shift-only: every bad config has ≥1 middle privilege (Lemma 6),
    and all frontiers propagate toward boundaries. After O(n) shifts,
    at least one frontier reaches a boundary position (0 or n-2) where
    no middle can process it. Since Lemma 6 requires ≥1 middle privilege,
    there must be ≥1 interior frontier. But shifting moves interior frontiers
    to boundaries, eventually emptying the interior → contradiction.

    Actually, can a middle proc create a new interior frontier while
    shifting one? Yes (shifts create a frontier at the new position).
    So the interior doesn't empty.

    Let me just verify computationally: are there middle-only bad→bad cycles?
    """
    print("=" * 60)
    print("CASE 1: Middle-only cycles")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # Build middle-only bad→bad graph
        graph = defaultdict(list)
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            middle_priv = [p for p in priv if 1 <= p <= n-2]
            for p in middle_priv:
                succ = apply_move(c, p, fs, n)
                if succ in bad_set:
                    graph[c].append(succ)

        # Check for cycles via DFS
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in bad_set}
        has_cycle = False

        def dfs(v):
            nonlocal has_cycle
            color[v] = GRAY
            for w in graph[v]:
                if color[w] == GRAY:
                    has_cycle = True
                    return
                if color[w] == WHITE:
                    dfs(w)
                    if has_cycle:
                        return
            color[v] = BLACK

        sys.setrecursionlimit(100000)
        for c in bad_set:
            if color[c] == WHITE:
                dfs(c)
                if has_cycle:
                    break

        print(f"  n={n}: middle-only cycles: {'EXIST!' if has_cycle else 'NONE ✓'}")


# ========= CASE 2: No-top cycles =========

def verify_case2(max_n=10):
    """Case 2: Cycles with middle + bottom only (no top).
    Check if there are any cycles in the (middle+bottom)-only bad→bad graph."""
    print("\n" + "=" * 60)
    print("CASE 2: Middle+bottom only cycles (no top)")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # Build (middle+bottom)-only bad→bad graph
        graph = defaultdict(list)
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            non_top = [p for p in priv if p != n-1]
            for p in non_top:
                succ = apply_move(c, p, fs, n)
                if succ in bad_set:
                    graph[c].append(succ)

        # Check for cycles
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in bad_set}
        has_cycle = False

        def dfs(v):
            nonlocal has_cycle
            color[v] = GRAY
            for w in graph[v]:
                if color[w] == GRAY:
                    has_cycle = True
                    return
                if color[w] == WHITE:
                    dfs(w)
                    if has_cycle:
                        return
            color[v] = BLACK

        sys.setrecursionlimit(100000)
        for c in bad_set:
            if color[c] == WHITE:
                dfs(c)
                if has_cycle:
                    break

        print(f"  n={n}: mid+bot only cycles: {'EXIST!' if has_cycle else 'NONE ✓'}")


# ========= CASE 3: No-bottom cycles =========

def verify_case3(max_n=10):
    """Case 3: Cycles with middle + top only (no bottom)."""
    print("\n" + "=" * 60)
    print("CASE 3: Middle+top only cycles (no bottom)")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # Build (middle+top)-only bad→bad graph
        graph = defaultdict(list)
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            non_bot = [p for p in priv if p != 0]
            for p in non_bot:
                succ = apply_move(c, p, fs, n)
                if succ in bad_set:
                    graph[c].append(succ)

        # Check for cycles
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {c: WHITE for c in bad_set}
        has_cycle = False

        def dfs(v):
            nonlocal has_cycle
            color[v] = GRAY
            for w in graph[v]:
                if color[w] == GRAY:
                    has_cycle = True
                    return
                if color[w] == WHITE:
                    dfs(w)
                    if has_cycle:
                        return
            color[v] = BLACK

        sys.setrecursionlimit(100000)
        for c in bad_set:
            if color[c] == WHITE:
                dfs(c)
                if has_cycle:
                    break

        print(f"  n={n}: mid+top only cycles: {'EXIST!' if has_cycle else 'NONE ✓'}")


# ========= ANALYZE: What fraction of bad→bad transitions involve each proc? =========

def analyze_transition_types(max_n=9):
    """For each bad→bad transition, what move type is it?
    Key question: can the daemon avoid all middle-annihilation moves indefinitely?"""
    print("\n" + "=" * 60)
    print("BAD→BAD TRANSITION TYPE ANALYSIS")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        total_bad_bad = 0
        by_type = defaultdict(int)

        for c in bad_set:
            priv = get_privileged(c, fs, n)
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in bad_set:
                    total_bad_bad += 1
                    fc_b = frontier_count(c, n)
                    fc_a = frontier_count(succ, n)
                    delta = fc_a - fc_b
                    mtype = "BOT" if p == 0 else ("TOP" if p == n-1 else "MID")
                    by_type[(mtype, delta)] += 1

        print(f"\n  n={n}: {total_bad_bad} bad→bad transitions")
        for key in sorted(by_type.keys()):
            mtype, delta = key
            frac = by_type[key] / total_bad_bad * 100 if total_bad_bad > 0 else 0
            print(f"    {mtype} Δfc={delta:+d}: {by_type[key]:5d} ({frac:5.1f}%)")


def check_fc_decreasing_path(max_n=9):
    """For each bad config, find the SHORTEST path (any daemon) to a config with strictly fewer frontiers.
    This is the minimum number of steps needed for fc to decrease."""
    print("\n" + "=" * 60)
    print("SHORTEST PATH TO FRONTIER DECREASE")
    print("=" * 60)
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1_rules(ms, n)
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(configs) - good_set

        # For each bad config c with frontier count fc:
        # BFS to find min steps to reach ANY config c' with fc(c') < fc(c).
        # This uses the HELPFUL daemon (best case).
        max_steps_to_decrease = 0
        hard_configs = []

        for c in bad_set:
            fc = frontier_count(c, n)
            if fc == 0:
                continue

            # BFS from c
            visited = {c}
            frontier_bfs = [c]
            depth = 0
            found = False

            while frontier_bfs and depth < 3 * n:
                depth += 1
                next_frontier = []
                for cur in frontier_bfs:
                    priv = get_privileged(cur, fs, n)
                    for p in priv:
                        succ = apply_move(cur, p, fs, n)
                        if succ in visited:
                            continue
                        fc_s = frontier_count(succ, n)
                        if fc_s < fc:
                            found = True
                            break
                        if succ in good_set:
                            found = True
                            break
                        visited.add(succ)
                        next_frontier.append(succ)
                    if found:
                        break
                if found:
                    break
                frontier_bfs = next_frontier

            if found:
                if depth > max_steps_to_decrease:
                    max_steps_to_decrease = depth
                    hard_configs = [(c, fc, depth)]
                elif depth == max_steps_to_decrease:
                    hard_configs.append((c, fc, depth))
            else:
                hard_configs.append((c, fc, -1))

        print(f"  n={n}: max steps to fc decrease (helpful daemon): {max_steps_to_decrease}")
        if hard_configs and n <= 6:
            for c, fc, d in hard_configs[:3]:
                dv = get_d_vector(c, n)
                print(f"    {c} fc={fc} d={dv} steps={d}")


if __name__ == "__main__":
    verify_case1(10)
    verify_case2(10)
    verify_case3(10)
    analyze_transition_types(8)
    check_fc_decreasing_path(9)
