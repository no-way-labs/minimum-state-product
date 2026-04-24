#!/usr/bin/env python3
"""
CIC Exploration 12d: SCC Structure Analysis for Single-Wiggle Words.

From 12c: MOVER entries alone always create SCC (100% at n=7,8,9).
Now: understand WHY. Dig into:
1. SCC size and structure
2. Which mover entries are "critical" (SCC disappears without them)
3. Pattern across state sequence choices
4. Larger n test
5. Different binary placements
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def generate_wiggle_words(n, binary_positions):
    """Generate single-wiggle words."""
    binary_set = set(binary_positions)
    words = set()
    for direction in [+1, -1]:
        base = [(i * direction) % n for i in range(2 * n)]
        for insert_pos in range(2 * n):
            p = base[insert_pos]
            next_p = base[(insert_pos + 1) % (2 * n)]
            step = (next_p - p) % n
            if step == 1:
                bounce = (p - 1) % n
            elif step == n - 1:
                bounce = (p + 1) % n
            else:
                continue
            if p in binary_set or bounce in binary_set:
                continue
            word = list(base[:insert_pos + 1]) + [bounce, p] + list(base[insert_pos + 1:])
            L = len(word)
            valid = True
            for i in range(L):
                diff = abs(word[i] - word[(i + 1) % L])
                if diff != 1 and diff != n - 1:
                    valid = False
                    break
            if not valid:
                continue
            mc = Counter(word)
            if not all(mc.get(q, 0) >= 2 for q in range(n)):
                continue
            if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                continue
            min_idx = word.index(min(word))
            rotated = word[min_idx:] + word[:min_idx]
            words.add(tuple(rotated))
    return [list(w) for w in sorted(words)]


def get_fire_counts(word, n):
    fc = [0] * n
    for p in word:
        fc[p] += 1
    return fc


def enumerate_state_sequences(n, ms, fire_counts):
    proc_sequences = {}
    for p in range(n):
        m = ms[p]
        k = fire_counts[p]
        seqs = []
        def dfs_seq(seq, remaining, m_val=m):
            if remaining == 0:
                if seq[-1] == 0:
                    seqs.append(list(seq))
                return
            current = seq[-1]
            for next_val in range(m_val):
                if next_val != current:
                    if remaining == 1 and next_val != 0:
                        continue
                    seq.append(next_val)
                    dfs_seq(seq, remaining - 1, m_val)
                    seq.pop()
        dfs_seq([0], k)
        proc_sequences[p] = seqs
    return proc_sequences


def compute_configs(word, n, ms, state_seqs):
    L = len(word)
    fc = [0] * n
    configs = []
    config = tuple(state_seqs[p][0] for p in range(n))
    configs.append(config)
    for t in range(L):
        mover = word[t]
        fc[mover] += 1
        config = tuple(state_seqs[p][fc[p]] for p in range(n))
        configs.append(config)
    return configs


def check_valid_cycle(configs, L):
    if configs[-1] != configs[0]:
        return False
    return len(set(configs[:L])) == L


def check_scc_tarjan_with_detail(ms, n, good_set, required):
    """Tarjan SCC with details about the SCC structure."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = set(c for c in all_configs if c not in good_set)

    adj = defaultdict(set)
    edge_labels = {}  # (src, dst) -> (proc, new_val)
    for config in non_good:
        for j in range(n):
            Lj = config[(j-1) % n]
            Sj = config[j]
            Rj = config[(j+1) % n]
            key = (j, Lj, Sj, Rj)
            if key in required and required[key] != Sj:
                new_config = list(config)
                new_config[j] = required[key]
                new_config = tuple(new_config)
                if new_config in non_good:
                    adj[config].add(new_config)
                    edge_labels[(config, new_config)] = (j, required[key])

    # Tarjan
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    sys.setrecursionlimit(100000)

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj.get(v, set()):
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

    for v in non_good:
        if v not in index:
            strongconnect(v)

    return sccs, adj, edge_labels


def main():
    print("CIC Exploration 12d: SCC Structure Analysis")
    print("=" * 70)

    # PART 1: SCC sizes and structure
    print("\nPART 1: SCC Sizes and Structure")
    print("-" * 70)

    configs = [
        (7, [0, 2, 4], [2, 3, 2, 3, 2, 3, 3]),
        (8, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3]),
        (9, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ]

    for n, bp, ms in configs:
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        w = words[0]
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        seq_lists = [proc_seqs[p] for p in range(n)]

        product_total = 1
        for m in ms:
            product_total *= m

        print(f"\n  n={n} bp={bp} word={w}")
        print(f"  Product={product_total}, L={len(w)}")

        # Take first valid combo
        for combo in iproduct(*seq_lists):
            state_seqs = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, state_seqs)
            L = len(w)
            if not check_valid_cycle(cfgs, L):
                continue

            cycle_configs = cfgs[:L]
            good_set = set(cycle_configs)

            # Extract mover entries
            mover_entries = {}
            for i in range(L):
                c = cycle_configs[i]
                c_next = cycle_configs[(i + 1) % L]
                mover = w[i]
                key = (mover, c[(mover-1)%n], c[mover], c[(mover+1)%n])
                mover_entries[key] = c_next[mover]

            sccs, adj, edge_labels = check_scc_tarjan_with_detail(
                ms, n, good_set, mover_entries)

            n_non_good = product_total - len(good_set)
            print(f"  Good: {len(good_set)}, Non-good: {n_non_good}")
            print(f"  SCCs: {len(sccs)}, sizes: {sorted([len(s) for s in sccs], reverse=True)[:10]}")

            # Show the smallest SCC in detail
            if sccs:
                smallest = min(sccs, key=len)
                print(f"\n  Smallest SCC ({len(smallest)} configs):")
                for c in sorted(smallest)[:8]:
                    # Show which procs are forced to transition
                    forced = []
                    for j in range(n):
                        key = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                        if key in mover_entries and mover_entries[key] != c[j]:
                            forced.append(f"{j}:{c[j]}→{mover_entries[key]}")
                    print(f"    {c} → forced: {forced}")
                if len(smallest) > 8:
                    print(f"    ... ({len(smallest) - 8} more)")

            # Which procs' entries create the SCC edges?
            scc_edge_procs = Counter()
            scc_set = set()
            for scc in sccs:
                scc_set.update(scc)
            for c in scc_set:
                for c2 in adj.get(c, set()):
                    if c2 in scc_set and (c, c2) in edge_labels:
                        scc_edge_procs[edge_labels[(c, c2)][0]] += 1

            print(f"\n  SCC edge procs: {dict(sorted(scc_edge_procs.items()))}")
            for p, count in sorted(scc_edge_procs.items()):
                ptype = 'B' if ms[p] == 2 else 'T'
                print(f"    Proc {p} ({ptype}): {count} SCC edges")

            # Critical entry analysis: remove each mover entry and check if SCC persists
            print(f"\n  Critical entry analysis:")
            for key, val in sorted(mover_entries.items()):
                reduced = dict(mover_entries)
                del reduced[key]
                sccs_r, _, _ = check_scc_tarjan_with_detail(ms, n, good_set, reduced)
                if not sccs_r:
                    p = key[0]
                    ptype = 'B' if ms[p] == 2 else 'T'
                    print(f"    CRITICAL: proc={p}({ptype}) entry={key}→{val}")

            break  # just first combo

    # PART 2: Pattern across state sequences
    print("\n\nPART 2: SCC Pattern Across State Sequences")
    print("-" * 70)

    n, bp, ms = 7, [0, 2, 4], [2, 3, 2, 3, 2, 3, 3]
    words = generate_wiggle_words(n, bp)
    w = words[0]
    fc = get_fire_counts(w, n)
    proc_seqs = enumerate_state_sequences(n, ms, fc)
    seq_lists = [proc_seqs[p] for p in range(n)]

    print(f"  n={n} word={w}")

    for combo in iproduct(*seq_lists):
        state_seqs = {p: combo[p] for p in range(n)}
        cfgs = compute_configs(w, n, ms, state_seqs)
        L = len(w)
        if not check_valid_cycle(cfgs, L):
            continue

        cycle_configs = cfgs[:L]
        good_set = set(cycle_configs)

        mover_entries = {}
        for i in range(L):
            c = cycle_configs[i]
            c_next = cycle_configs[(i + 1) % L]
            mover = w[i]
            key = (mover, c[(mover-1)%n], c[mover], c[(mover+1)%n])
            mover_entries[key] = c_next[mover]

        sccs, _, _ = check_scc_tarjan_with_detail(ms, n, good_set, mover_entries)

        seq_desc = tuple(tuple(combo[p]) for p in range(n) if ms[p] > 2)
        sizes = sorted([len(s) for s in sccs], reverse=True)
        print(f"  seqs={seq_desc}: {len(sccs)} SCCs, sizes={sizes[:5]}")

    # PART 3: More binary placements
    print("\n\nPART 3: Different Binary Placements")
    print("-" * 70)

    test_configs = [
        (6, [0, 2, 4]),
        (7, [0, 2, 4]),
        (7, [0, 2, 5]),
        (7, [0, 3, 5]),
        (8, [0, 2, 5]),
        (8, [0, 3, 6]),
        (8, [0, 2, 4, 6]),
        (9, [0, 2, 4, 6]),
        (9, [0, 3, 6]),
        (10, [0, 3, 6]),
        (10, [0, 4, 7]),
        (10, [0, 3, 6, 9]),  # k=4, gaps=(2,2,2,0) - not valid since adjacent
        (10, [0, 2, 5, 7]),  # k=4
        (11, [0, 4, 8]),
        (12, [0, 4, 8]),
    ]

    for n, bp in test_configs:
        # Check non-adjacency
        bp_set = set(bp)
        non_adj = True
        for b in bp:
            if (b + 1) % n in bp_set or (b - 1) % n in bp_set:
                non_adj = False
                break
        if not non_adj:
            continue

        ms = [2 if i in bp_set else 3 for i in range(n)]
        words = generate_wiggle_words(n, bp)
        if not words:
            print(f"  n={n} bp={bp}: 0 wiggle words")
            continue

        total_valid = 0
        total_scc_mover = 0

        for w in words:
            fc = get_fire_counts(w, n)
            proc_seqs = enumerate_state_sequences(n, ms, fc)
            seq_lists = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*seq_lists):
                state_seqs = {p: combo[p] for p in range(n)}
                cfgs = compute_configs(w, n, ms, state_seqs)
                L = len(w)
                if not check_valid_cycle(cfgs, L):
                    continue
                total_valid += 1

                cycle_configs = cfgs[:L]
                good_set = set(cycle_configs)

                mover_entries = {}
                for i in range(L):
                    c = cycle_configs[i]
                    c_next = cycle_configs[(i + 1) % L]
                    mover = w[i]
                    key = (mover, c[(mover-1)%n], c[mover], c[(mover+1)%n])
                    mover_entries[key] = c_next[mover]

                sccs, _, _ = check_scc_tarjan_with_detail(ms, n, good_set, mover_entries)
                if sccs:
                    total_scc_mover += 1

        tag = '✓' if total_scc_mover == total_valid and total_valid > 0 else '✗'
        print(f"  n={n} k={len(bp)} bp={bp}: {total_scc_mover}/{total_valid} "
              f"mover-SCC {tag}")

    # PART 4: What about quaternary?
    print("\n\nPART 4: Quaternary Non-Binary States")
    print("-" * 70)

    # Test with m=4 for non-binary
    for n, bp in [(7, [0, 2, 4]), (8, [0, 3, 6])]:
        bp_set = set(bp)
        ms_ternary = [2 if i in bp_set else 3 for i in range(n)]
        ms_quaternary = [2 if i in bp_set else 4 for i in range(n)]

        for ms, label in [(ms_ternary, "ternary"), (ms_quaternary, "quaternary")]:
            words = generate_wiggle_words(n, bp)
            if not words:
                continue

            total_valid = 0
            total_scc = 0

            for w in words:
                fc = get_fire_counts(w, n)
                proc_seqs = enumerate_state_sequences(n, ms, fc)
                seq_lists = [proc_seqs[p] for p in range(n)]

                for combo in iproduct(*seq_lists):
                    state_seqs = {p: combo[p] for p in range(n)}
                    cfgs = compute_configs(w, n, ms, state_seqs)
                    L = len(w)
                    if not check_valid_cycle(cfgs, L):
                        continue
                    total_valid += 1

                    cycle_configs = cfgs[:L]
                    good_set = set(cycle_configs)

                    mover_entries = {}
                    for i in range(L):
                        c = cycle_configs[i]
                        c_next = cycle_configs[(i + 1) % L]
                        mover = w[i]
                        key = (mover, c[(mover-1)%n], c[mover], c[(mover+1)%n])
                        mover_entries[key] = c_next[mover]

                    sccs, _, _ = check_scc_tarjan_with_detail(ms, n, good_set, mover_entries)
                    if sccs:
                        total_scc += 1

            tag = '✓' if total_scc == total_valid and total_valid > 0 else '✗'
            print(f"  n={n} bp={bp} {label}: {total_scc}/{total_valid} {tag}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
