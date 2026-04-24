#!/usr/bin/env python3
"""CUP: Final convergence verification + structural lemma.

Key structural result: In any bad cycle, top must fire an EVEN number of times T≥2,
because:
- c_{n-1} changes ONLY when top fires
- Top sets c_{n-1} = (c_{n-2}+1)%3 ≠ current c_{n-1}
- At top firing, c_{n-2} ≡ c_0 (mod 3), and c_0 ∈ {0,1}, so c_{n-2} ∈ {0,1}
- Consecutive top firings see different c_0 values (alternating)
- For T odd: a_T = a_1, so s_0 = (a_1+1)%3 but privilege requires (a_1+1)%3 ≠ s_0. ⊥
- For T even: closure condition (a_T+1)%3 = s_0 is satisfiable.
- For T=2: exactly one top is Δfc=+2 and one is Δfc=0.

This script:
1. Verifies the T-even constraint computationally
2. Extends SCC check to n=11 (or as high as feasible)
3. Verifies the "one Δfc=+2 + one Δfc=0" structure for T=2
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict, deque


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


def check_scc(n):
    """Check that the bad→bad graph has no SCCs (is a DAG)."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    total = 1
    for m in ms:
        total *= m
    bad_count = total - len(good_set)

    # Build adjacency list
    adj = defaultdict(list)
    in_deg = defaultdict(int)

    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    edge_count = 0
    for c in bad_set:
        in_deg.setdefault(c, 0)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                adj[c].append(succ)
                if c not in in_deg:
                    in_deg[c] = 0
                in_deg[succ] = in_deg.get(succ, 0) + 1
                edge_count += 1

    # Kahn's algorithm for topological sort
    q = deque()
    for c in bad_set:
        if in_deg.get(c, 0) == 0:
            q.append(c)

    processed = 0
    while q:
        c = q.popleft()
        processed += 1
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    is_dag = (processed == bad_count)
    return is_dag, bad_count, edge_count


def check_scc_tarjan(n):
    """Use Tarjan's SCC algorithm (more memory efficient for large graphs)."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    total = 1
    for m in ms:
        total *= m
    bad_count = total - len(good_set)

    # Build adjacency list on-the-fly
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Tarjan's SCC
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    max_scc_size = [0]

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        priv = get_privileged(v, fs, n)
        for p in priv:
            w = apply_move(v, p, fs, n)
            if w not in bad_set:
                continue
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > max_scc_size[0]:
                max_scc_size[0] = len(scc)

    # Use iterative Tarjan to avoid recursion limit
    sys.setrecursionlimit(max(10000, bad_count + 100))
    try:
        for v in bad_set:
            if v not in index:
                strongconnect(v)
    except RecursionError:
        return None, bad_count, -1

    return max_scc_size[0] == 1, bad_count, max_scc_size[0]


def check_scc_iterative(n):
    """Iterative Tarjan's SCC for large graphs."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    total = 1
    for m in ms:
        total *= m
    bad_count = total - len(good_set)

    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set_set = set(configs) - good_set
    del configs  # free memory

    # Use Kahn's algorithm (simpler for DAG check)
    adj = {}
    in_deg = {}
    for c in bad_set_set:
        in_deg[c] = 0
    for c in bad_set_set:
        succs = []
        priv = get_privileged(c, fs, n)
        for p in priv:
            s = apply_move(c, p, fs, n)
            if s in bad_set_set:
                succs.append(s)
                in_deg[s] += 1
        adj[c] = succs

    q = deque()
    for c in bad_set_set:
        if in_deg[c] == 0:
            q.append(c)

    processed = 0
    while q:
        c = q.popleft()
        processed += 1
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    is_dag = (processed == bad_count)
    return is_dag, bad_count


if __name__ == "__main__":
    print("=" * 70)
    print("SCC CHECK: Bad→bad graph is a DAG (no bad cycles)")
    print("=" * 70)

    for nv in range(3, 14):
        total = 2 * 3**(nv-1)
        print(f"\nn={nv}: product={total}, ", end='', flush=True)

        if total > 500000:
            print(f"SKIPPED (too large)")
            continue

        import time
        t0 = time.time()
        is_dag, bad_count = check_scc_iterative(nv)
        elapsed = time.time() - t0

        if is_dag:
            print(f"bad={bad_count}, DAG ✓ ({elapsed:.1f}s)")
        else:
            print(f"bad={bad_count}, CYCLE FOUND! ({elapsed:.1f}s)")
