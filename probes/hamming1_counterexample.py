"""
THOROUGH search for counterexamples to H-1 Uniqueness.

A valid self-stabilizing system requires ALL 5 Dijkstra properties:
1. Liveness: every config has >= 1 privileged
2. Mutual exclusion: good configs have exactly 1 privileged
3. Closure: good -> good
4. Convergence: no bad cycle
5. Fairness: all procs fire in the good cycle

The abstract cycle with non-adj H-1 from trial 95 failed CLOSURE.
Need to search more carefully.
"""

import itertools, random
from math import gcd
from functools import reduce

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)

def hamming_distance(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)

def verify_full(ms, fs):
    """Full verification of self-stabilization properties."""
    n = len(ms)
    configs = all_configs(ms)

    # Privilege map
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    # Liveness
    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return None, "liveness_fail"

    # Good configs
    good = [c for c in configs if len(priv_map[c]) == 1]

    # Closure + extract cycle
    good_set = set(good)
    successor = {}
    for c in good:
        mover = priv_map[c][0]
        nxt = apply_move(c, mover, fs, ms)
        if nxt not in good_set:
            return None, "closure_fail"
        successor[c] = (nxt, mover)

    # Find cycle
    start = good[0]
    cycle = []
    current = start
    seen = set()
    while current not in seen:
        seen.add(current)
        nxt, mover = successor[current]
        cycle.append((current, mover))
        current = nxt

    if current != start or len(cycle) != len(good):
        return None, "cycle_incomplete"

    # Convergence: no cycle among bad configs
    bad_set = set(configs) - good_set
    # For each bad config, check if there's a cycle
    # Use: for every privileged proc, fire it and check
    # A bad cycle exists if we can loop among bad configs
    visited_global = set()
    for start_bad in bad_set:
        if start_bad in visited_global:
            continue
        # DFS checking all possible firing paths
        stack = [(start_bad, frozenset([start_bad]))]
        while stack:
            c, path = stack.pop()
            visited_global.add(c)
            for p in priv_map[c]:
                nxt = apply_move(c, p, fs, ms)
                if nxt in good_set:
                    continue
                if nxt in path:
                    return None, "bad_cycle"
                if nxt not in visited_global:
                    stack.append((nxt, path | {nxt}))

    # Fairness
    movers = {m for _, m in cycle}
    if len(movers) != n:
        return None, "fairness_fail"

    # Fire counts
    fc = [0]*n
    for _, m in cycle:
        fc[m] += 1

    return cycle, fc

# ============================================================
# Search with MULTIPLE abstract cycles
# ============================================================

ms_test = [2, 3, 3]
n = 3
CL = sum(ms_test)

def enumerate_mover_words(ms):
    base = []
    for i in range(len(ms)):
        base.extend([i]*ms[i])
    return set(itertools.permutations(base))

mover_words = list(enumerate_mover_words(ms_test))
all_cfgs = list(itertools.product(range(2), range(3), range(3)))

print(f"ms = {ms_test}, n = {n}, CL = {CL}")
print(f"Total mover words: {len(mover_words)}")
print(f"Searching for valid systems with non-adjacent H-1 pairs...")

# Strategy: for each abstract cycle with non-adj H-1, try many completions
# and fully verify each.

random.seed(42)
total_cycles_checked = 0
total_completions_tried = 0
valid_counterexamples = 0

# First, collect a sample of abstract cycles with non-adj H-1
nonadj_cycles = []

for word in mover_words:
    for start in all_cfgs:
        stack = [(0, start, [start])]
        while stack:
            step, current, path = stack.pop()
            if step == CL:
                if current == start and len(set(path[:CL])) == CL:
                    configs = path[:CL]
                    has_nonadj = False
                    for j in range(CL):
                        for k in range(j+1, CL):
                            if hamming_distance(configs[j], configs[k]) == 1:
                                d = k - j
                                if 1 < d < CL - 1:
                                    has_nonadj = True
                                    break
                        if has_nonadj:
                            break
                    if has_nonadj:
                        nonadj_cycles.append((word, configs))
                continue
            mover = word[step]
            for new_val in range(ms_test[mover]):
                if new_val != current[mover]:
                    new_cfg = list(current)
                    new_cfg[mover] = new_val
                    stack.append((step+1, tuple(new_cfg), path + [tuple(new_cfg)]))

print(f"Found {len(nonadj_cycles)} abstract cycles with non-adj H-1")

# Deduplicate by cycle content
unique_nonadj = {}
for word, configs in nonadj_cycles:
    key = (word, tuple(configs))
    unique_nonadj[key] = (word, configs)

print(f"Unique: {len(unique_nonadj)}")

# For each unique cycle, try completions
MAX_TRIES_PER_CYCLE = 1000
cycles_with_consistent_tf = 0

for idx, (key, (word, configs)) in enumerate(unique_nonadj.items()):
    if idx >= 200:  # Check first 200 unique cycles
        break

    # Build partial tables
    tables = [{} for _ in range(n)]
    consistent = True
    for s in range(CL):
        c = configs[s]
        m = word[s]
        c_next = configs[(s+1) % CL]
        for i in range(n):
            Li = c[(i-1)%n]
            Si = c[i]
            Ri = c[(i+1)%n]
            ctx = (Li, Si, Ri)
            req = c_next[i] if i == m else Si
            if ctx in tables[i]:
                if tables[i][ctx] != req:
                    consistent = False
                    break
            else:
                tables[i][ctx] = req
        if not consistent:
            break

    if not consistent:
        continue

    cycles_with_consistent_tf += 1
    total_cycles_checked += 1

    # Get free contexts
    free_ctxs = []
    for i in range(n):
        L_range = ms_test[(i-1)%n]
        S_range = ms_test[i]
        R_range = ms_test[(i+1)%n]
        free = [(L,S,R) for L in range(L_range) for S in range(S_range)
                for R in range(R_range) if (L,S,R) not in tables[i]]
        free_ctxs.append(free)

    # Try random completions
    for trial in range(MAX_TRIES_PER_CYCLE):
        total_completions_tried += 1
        full_tables = [dict(t) for t in tables]
        for i in range(n):
            for ctx in free_ctxs[i]:
                full_tables[i][ctx] = random.randint(0, ms_test[i]-1)

        def make_f(table):
            def f(L,S,R): return table[(L,S,R)]
            return f
        fs = [make_f(full_tables[i]) for i in range(n)]

        result, info = verify_full(ms_test, fs)
        if result is not None:
            cycle = result
            fc = info
            # Check if THIS system has non-adj H-1
            cycle_configs = [c for c, m in cycle]
            has_nonadj = False
            for j in range(len(cycle)):
                for k in range(j+1, len(cycle)):
                    if hamming_distance(cycle_configs[j], cycle_configs[k]) == 1:
                        d = k - j
                        if 1 < d < len(cycle) - 1:
                            has_nonadj = True
                            break
                if has_nonadj:
                    break

            if has_nonadj:
                valid_counterexamples += 1
                print(f"\n*** VALID COUNTEREXAMPLE FOUND ***")
                print(f"  Abstract cycle index: {idx}")
                print(f"  Word: {word}")
                print(f"  Configs: {configs}")
                print(f"  System's actual good cycle:")
                for s, (c, m) in enumerate(cycle):
                    print(f"    step {s}: {c} mover={m}")
                print(f"  Fire counts: {fc}")
                print(f"  fc = m_i: {all(fc[i] == ms_test[i] for i in range(n))}")
                print(f"  gcd: {reduce(gcd, ms_test)}")

                # Show the non-adj H-1 pairs
                for j in range(len(cycle)):
                    for k in range(j+1, len(cycle)):
                        if hamming_distance(cycle_configs[j], cycle_configs[k]) == 1:
                            d = k - j
                            if 1 < d < len(cycle) - 1:
                                p = [i for i in range(n) if cycle_configs[j][i] != cycle_configs[k][i]][0]
                                print(f"  Non-adj H-1: j={j},k={k},p={p},d={d}")
                break  # Found one, move to next cycle

    if idx % 50 == 0:
        print(f"  Checked {idx+1} cycles, {total_completions_tried} completions, "
              f"{valid_counterexamples} counterexamples")

print(f"\n{'='*70}")
print(f"RESULTS:")
print(f"  TF-consistent cycles checked: {cycles_with_consistent_tf}")
print(f"  Total completions tried: {total_completions_tried}")
print(f"  Valid counterexamples: {valid_counterexamples}")

if valid_counterexamples == 0:
    print("\n  NO VALID COUNTEREXAMPLE FOUND.")
    print("  The H-1 Uniqueness Lemma appears TRUE for self-stabilizing systems,")
    print("  but the proof needs self-stabilization (liveness + closure + convergence)")
    print("  as an essential ingredient — the abstract cycle argument is insufficient.")
