#!/usr/bin/env python3
"""binscc_mixed_nonsweep_scc.py — Do non-sweep cycles on mixed systems have mover-entry SCC?

For non-consecutive binary mixed systems at sub-threshold products,
verify that ALL good cycles (including non-sweep) have mover entries
that create bad SCC among non-good configs.

This extends the Forced Mover-Entry SCC (CIC Expl 8) to mixed multisets.
"""

from itertools import product as iproduct
from collections import Counter
import sys
import time


def enumerate_mover_words_smart(ms, n, max_length):
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]
    results = []
    start_config = tuple(0 for _ in range(n))
    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fire_counts[p]) for p in range(n)
                     if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(current_config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1
            word.append(nxt)
            dfs(word, new_counts, new_config)
            word.pop()
    for p in range(n):
        first = list(start_config)
        first[p] = (first[p] + 1) % ms[p]
        first = tuple(first)
        dfs([p], [1 if i == p else 0 for i in range(n)], first)
    return results


def build_cycle(ms, n, mover_word):
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    for p in range(n):
        if fc[p] == 0 or fc[p] % ms[p] != 0:
            return None
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return None
    return configs[:ell]


def check_mover_entry_scc(cycle, ms, n):
    """Check if MOVER entries alone create a bad SCC among non-good configs.

    Extract only mover entries (where proc fires), build forced transition
    graph on non-good configs, check for SCC.
    """
    ell = len(cycle)
    good_set = set(cycle)

    # Extract mover entries only
    mover_det = {}
    has_conflict = False
    for i in range(ell):
        c = cycle[i]
        c_next = cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None, 'invalid'
        mover = diffs[0]
        L = c[(mover-1)%n]; S = c[mover]; R = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, L, S, R)
        if key in mover_det and mover_det[key] != S_new:
            has_conflict = True
        mover_det[key] = S_new

    if has_conflict:
        return True, 'conflict'  # conflict = blocked

    # Also include nonmover entries (identity) for completeness
    full_det = dict(mover_det)
    for i in range(ell):
        c = cycle[i]
        c_next = cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        mover = diffs[0]
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in full_det and full_det[key2] != Sj:
                    has_conflict = True
                full_det[key2] = Sj

    if has_conflict:
        return True, 'full_conflict'

    # Build forced transition graph using MOVER entries only on non-good configs
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # For each non-good config, find forced moves (from mover entries)
    adj = {}  # config -> list of successor configs
    for c in non_good:
        succs = []
        for j in range(n):
            Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
            key = (j, Lj, Sj, Rj)
            if key in mover_det and mover_det[key] != Sj:
                new_c = list(c)
                new_c[j] = mover_det[key]
                new_c = tuple(new_c)
                if new_c in non_good_set:
                    succs.append(new_c)
        adj[c] = succs

    # Find SCC using Tarjan's algorithm
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in adj.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    for v in non_good:
        if v not in index:
            strongconnect(v)

    has_scc = len(sccs) > 0
    return has_scc, 'scc' if has_scc else 'no_scc'


def main():
    print("=" * 70)
    print("MOVER-ENTRY SCC ON MIXED NON-CONSECUTIVE BINARY SYSTEMS")
    print("=" * 70)
    print()

    test_configs = [
        # Non-consecutive at sub-threshold
        (5, [2, 3, 2, 3, 2], 72, "pure, non-consec"),
        (5, [2, 4, 2, 3, 2], 96, "MIXED, non-consec"),
        (5, [2, 3, 2, 4, 2], 96, "MIXED, non-consec"),
        # Consecutive (comparison)
        (5, [2, 2, 2, 3, 3], 72, "pure, consec"),
        (5, [2, 2, 2, 3, 4], 96, "MIXED, consec"),
    ]

    for n, ms, prod, label in test_configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms} prod={prod} [{label}]")
        print(f"{'='*60}")
        sys.stdout.flush()

        t0 = time.time()
        max_len = 3 * n + 6
        words = enumerate_mover_words_smart(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} mover words ({t1-t0:.1f}s)")

        stats = Counter()
        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            stats['valid'] += 1

            has_block, reason = check_mover_entry_scc(cycle, ms, n)
            if has_block is None:
                stats['invalid'] += 1
            elif has_block:
                stats[f'blocked_{reason}'] += 1
            else:
                stats[f'unblocked_{reason}'] += 1

        elapsed = time.time() - t0
        print(f"  Valid: {stats['valid']}")
        print(f"  Breakdown: {dict(stats)}")
        blocked = sum(v for k, v in stats.items() if k.startswith('blocked'))
        unblocked = sum(v for k, v in stats.items() if k.startswith('unblocked'))
        print(f"  Blocked: {blocked}, Unblocked: {unblocked}")
        if unblocked == 0 and stats['valid'] > 0:
            print(f"  ★ ALL {stats['valid']} cycles blocked by mover-entry mechanism ({elapsed:.1f}s)")
        elif unblocked > 0:
            print(f"  !! {unblocked} unblocked ({elapsed:.1f}s)")

        sys.stdout.flush()

    print(f"\n{'='*70}")
    print("CONCLUSION")
    print("=" * 70)
    sys.stdout.flush()


if __name__ == "__main__":
    main()
