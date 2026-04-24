#!/usr/bin/env python3
"""CUP: Investigate convergence proof strategies.

Key insight: X = sum(c_i) mod 3 changes by {1,2} at every step.
Can we use this + other invariants to rule out bad cycles?
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


def find_bad_sccs(n):
    """Find strongly connected components in the bad config graph."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']

    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Build nondeterministic transition graph on bad configs
    graph = defaultdict(list)
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            if succ in bad_set:
                graph[c].append(succ)

    # Tarjan's SCC
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        index[v] = lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w in graph[v]:
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
            if len(scc) > 1:
                sccs.append(scc)

    for v in bad_set:
        if v not in index:
            strongconnect(v)

    return sccs


def analyze_convergence_via_ranking(n):
    """For each bad config, compute the WORST-CASE distance to good set.
    This is the maximum over all daemon strategies of the number of steps.
    Use backwards induction."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']

    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    # Worst-case convergence time via backwards induction
    # For each bad config c, rank(c) = max over privileged moves p of:
    #   1 if apply(c,p) is good
    #   1 + rank(apply(c,p)) if apply(c,p) is bad
    # We compute iteratively: start with configs where ALL moves lead to good

    rank = {}
    changed = True
    iteration = 0
    while changed and iteration < 100:
        changed = False
        for c in bad_set:
            if c in rank:
                continue
            priv = get_privileged(c, fs, n)
            worst = 0
            all_resolved = True
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    steps = 1
                elif succ in rank:
                    steps = 1 + rank[succ]
                else:
                    all_resolved = False
                    break
                worst = max(worst, steps)
            if all_resolved:
                rank[c] = worst
                changed = True
        iteration += 1

    unranked = bad_set - set(rank.keys())
    if unranked:
        print(f"n={n}: {len(unranked)} unranked bad configs (BAD CYCLES!)")
        return None
    else:
        max_rank = max(rank.values()) if rank else 0
        print(f"n={n}: All {len(bad_set)} bad configs converge. "
              f"Max rank={max_rank}, product={2*3**(n-1)}")
        return max_rank


def study_max_rank_configs(n):
    """Study the structure of configs with maximum rank."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    rank = {}
    changed = True
    while changed:
        changed = False
        for c in bad_set:
            if c in rank:
                continue
            priv = get_privileged(c, fs, n)
            worst = 0
            all_resolved = True
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    steps = 1
                elif succ in rank:
                    steps = 1 + rank[succ]
                else:
                    all_resolved = False
                    break
                worst = max(worst, steps)
            if all_resolved:
                rank[c] = worst
                changed = True

    max_r = max(rank.values())
    max_configs = [c for c, r in rank.items() if r == max_r]

    print(f"\nn={n}: Max rank = {max_r}, achieved by {len(max_configs)} configs:")
    for c in sorted(max_configs):
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            s_rank = 'G' if succ in good_set else rank.get(succ, '?')
            print(f"  {c} P{p}→ {succ} (rank {s_rank})")


def check_rank_formula(max_n=10):
    """Check if max convergence rank follows a pattern."""
    print("Convergence rank by n:")
    ranks = []
    for n in range(3, max_n + 1):
        r = analyze_convergence_via_ranking(n)
        if r is not None:
            ranks.append((n, r))

    print("\nMax rank pattern:")
    for n, r in ranks:
        print(f"  n={n}: max_rank={r}, 2n-3={2*n-3}, n^2={n*n}")


if __name__ == "__main__":
    check_rank_formula(9)

    for n in [3, 4, 5]:
        study_max_rank_configs(n)
