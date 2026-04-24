#!/usr/bin/env python3
"""CUP: Trace convergence structure of Sol 3 v1 for small n.

For each bad config, find ALL possible successor paths and identify
the potential function structure.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system
from collections import defaultdict


def sol3_v1_rules(ms, n):
    """Return (fs, priv_fn, move_fn) for Sol 3 v1."""
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
            new_L = L % m_i
            new_R = R % m_i
            if (S + 1) % m_i == new_L:
                return new_L
            if (S + 1) % m_i == new_R:
                return new_R
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
        L = c[(i-1) % n]
        S = c[i]
        R = c[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(c, i, fs, n):
    L = c[(i-1) % n]
    S = c[i]
    R = c[(i+1) % n]
    new_s = fs[i](L, S, R)
    lst = list(c)
    lst[i] = new_s
    return tuple(lst)


def count_fronts(c, n):
    """Count disagreements (fronts) around the ring."""
    count = 0
    for i in range(n):
        if c[i] != c[(i+1) % n]:
            count += 1
    return count


def front_types(c, n):
    """Return list of (position, type) for each front."""
    fronts = []
    for i in range(n):
        d = (c[(i+1) % n] - c[i]) % 3
        if d != 0:
            fronts.append((i, d))
    return fronts


def analyze_convergence(n):
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)

    # Verify system
    result = verify_system(ms, fs)
    assert result['valid'], f"System invalid for n={n}!"
    good_set = result['good_configs']
    cycle = result['cycle']

    # All configs
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    print(f"\nn={n}: {len(configs)} total, {len(good_set)} good, {len(bad_set)} bad")

    # For each bad config, trace convergence
    # Compute worst-case convergence time (max over daemon choices)
    # Build the bad-config graph
    max_steps = {}  # config -> worst-case steps to reach good

    # Iterative computation: start from bad configs adjacent to good
    queue = []
    for c in bad_set:
        priv = get_privileged(c, fs, n)
        all_good = all(apply_move(c, p, fs, n) in good_set for p in priv)
        if all_good:
            max_steps[c] = 1
            queue.append(c)

    # BFS layers
    layer = 1
    while queue:
        next_queue = []
        for c in bad_set:
            if c in max_steps:
                continue
            priv = get_privileged(c, fs, n)
            all_resolved = True
            worst = 0
            for p in priv:
                succ = apply_move(c, p, fs, n)
                if succ in good_set:
                    pass  # this choice reaches good in 1 step
                elif succ in max_steps:
                    worst = max(worst, max_steps[succ] + 1)
                else:
                    all_resolved = False
                    break
            if all_resolved:
                max_steps[c] = worst if worst > 0 else 1
                next_queue.append(c)
        queue = next_queue
        layer += 1
        if layer > len(bad_set) + 5:
            break

    unresolved = bad_set - set(max_steps.keys())
    if unresolved:
        print(f"  WARNING: {len(unresolved)} unresolved bad configs (bad cycles?)")
    else:
        worst = max(max_steps.values()) if max_steps else 0
        print(f"  All bad configs converge. Worst-case steps: {worst}")

    # Print bad configs sorted by convergence time
    if n <= 5 and len(bad_set) <= 50:
        print(f"\n  Bad configs (sorted by worst-case steps):")
        for c in sorted(bad_set, key=lambda c: max_steps.get(c, 999)):
            steps = max_steps.get(c, '?')
            priv = get_privileged(c, fs, n)
            fronts = count_fronts(c, n)
            ftypes = front_types(c, n)
            succs = [(p, apply_move(c, p, fs, n)) for p in priv]
            succ_info = [f"P{p}→{'G' if s in good_set else str(max_steps.get(s,'?'))}"
                         for p, s in succs]
            print(f"    {c} steps={steps} fronts={fronts} types={ftypes} "
                  f"priv={priv} -> {', '.join(succ_info)}")

    # Analyze front count distribution
    front_dist = defaultdict(list)
    for c in bad_set:
        f = count_fronts(c, n)
        front_dist[f].append(c)

    print(f"\n  Front count distribution (bad configs):")
    for f in sorted(front_dist.keys()):
        configs_f = front_dist[f]
        if configs_f:
            avg_steps = sum(max_steps.get(c, 0) for c in configs_f) / len(configs_f)
            max_s = max(max_steps.get(c, 0) for c in configs_f)
            print(f"    {f} fronts: {len(configs_f)} configs, "
                  f"avg steps={avg_steps:.1f}, max steps={max_s}")

    # Check if front count is non-increasing for every move
    front_increases = []
    for c in bad_set:
        f_c = count_fronts(c, n)
        priv = get_privileged(c, fs, n)
        for p in priv:
            succ = apply_move(c, p, fs, n)
            f_s = count_fronts(succ, n)
            if f_s > f_c:
                front_increases.append((c, p, succ, f_c, f_s))

    if front_increases:
        print(f"\n  Front count INCREASES ({len(front_increases)} cases):")
        for c, p, s, fc, fs_val in front_increases[:10]:
            print(f"    {c} (fronts={fc}) --P{p}--> {s} (fronts={fs_val})")
    else:
        print(f"\n  Front count is non-increasing for all bad config moves!")


def analyze_potential_functions(n):
    """Try various potential functions and check monotonicity."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(configs) - good_set

    print(f"\n{'='*60}")
    print(f"POTENTIAL FUNCTION ANALYSIS for n={n}")
    print(f"{'='*60}")

    # Potential 1: Number of fronts
    # (already checked above)

    # Potential 2: Sum of |c_i - c_{i-1}| (non-circular)
    def phi_diff_sum(c):
        return sum(abs(c[i] - c[i-1]) for i in range(1, n))

    # Potential 3: Number of distinct values
    def phi_distinct(c):
        return len(set(c))

    # Potential 4: Lexicographic (fronts, then position-weighted front sum)
    def phi_lex(c):
        fronts = count_fronts(c, n)
        weighted = sum(i * (1 if c[i] != c[(i+1)%n] else 0) for i in range(n))
        return (fronts, weighted)

    # Potential 5: (fronts, sum of c_i)
    def phi_fronts_sum(c):
        return (count_fronts(c, n), sum(c))

    # Potential 6: max distance between agreeing neighbors
    # (how "spread out" the disagreements are)

    potentials = {
        'diff_sum': phi_diff_sum,
        'distinct': phi_distinct,
        'lex(fronts,pos_weight)': phi_lex,
        'lex(fronts,sum)': phi_fronts_sum,
    }

    for name, phi in potentials.items():
        increases = 0
        total_moves = 0
        for c in bad_set:
            priv = get_privileged(c, fs, n)
            for p in priv:
                succ = apply_move(c, p, fs, n)
                total_moves += 1
                if phi(succ) >= phi(c):
                    if phi(succ) > phi(c):
                        increases += 1
                    elif succ not in good_set:
                        increases += 1  # same value, still bad

        print(f"  {name}: {increases}/{total_moves} non-decreasing moves from bad configs")


if __name__ == "__main__":
    for n in [3, 4, 5]:
        analyze_convergence(n)

    for n in [3, 4, 5]:
        analyze_potential_functions(n)
