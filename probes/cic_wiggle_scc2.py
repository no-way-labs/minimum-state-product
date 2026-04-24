#!/usr/bin/env python3
"""
CIC Exploration 12b: Forced SCC for single-wiggle words.

Approach from binscc_mover_entry_scc.py adapted to wiggle words:
1. Trace configs through the seeded cycle (incrementing transitions)
2. Extract mover entries: forced (L,S,R) → S' for each firing
3. Extract non-mover entries: forced (L,S,R) → S (stay)
4. Build forced transition graph on non-good configs
5. Check for SCC (cycle among non-good configs)

Key question: do BINARY mover entries alone create SCC?
If yes: transition-function-independent → analytical proof.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def generate_wiggle_words(n, binary_positions):
    """Generate single-wiggle words (|W|=2 sweep + one bounce)."""
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

            # Verify adjacency
            valid = True
            for i in range(L):
                diff = abs(word[i] - word[(i + 1) % L])
                if diff != 1 and diff != n - 1:
                    valid = False
                    break
            if not valid:
                continue

            # Verify fairness and binary parity
            mc = Counter(word)
            if not all(mc.get(q, 0) >= 2 for q in range(n)):
                continue
            if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                continue

            # Normalize by rotation
            min_idx = word.index(min(word))
            rotated = word[min_idx:] + word[:min_idx]
            words.add(tuple(rotated))

    return [list(w) for w in sorted(words)]


def analyze_cycle_scc(ms, n, word, verbose=False):
    """
    Trace the word through incrementing configs and check for forced SCC.

    Returns dict with SCC results or None if cycle is invalid.
    """
    L = len(word)

    # Trace config sequence
    config = tuple(0 for _ in range(n))
    configs = [config]

    for t in range(L):
        mover = word[t]
        c = list(config)
        c[mover] = (c[mover] + 1) % ms[mover]
        config = tuple(c)
        configs.append(config)

    # Check cycle closes
    if configs[-1] != configs[0]:
        if verbose:
            print(f"  Cycle doesn't close: {configs[-1]} != {configs[0]}")
        return None

    # Check all configs distinct (valid good cycle)
    cycle_configs = configs[:L]
    if len(set(cycle_configs)) != L:
        if verbose:
            dups = [c for c in cycle_configs if cycle_configs.count(c) > 1]
            print(f"  Duplicate configs: {len(set(cycle_configs))}/{L}")
        return None

    good_set = set(cycle_configs)

    # Check adjacency
    for i in range(L):
        diff = abs(word[i] - word[(i + 1) % L])
        if diff != 1 and diff != n - 1:
            return None

    # Check overlap (same (L,S,R) as mover and non-mover at same proc)
    overlap_procs = []
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(L):
            c = cycle_configs[i]
            ctx = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        overlap = mover_ctx & nonmover_ctx
        if overlap:
            overlap_procs.append(p)

    # Extract entries
    mover_entries = {}
    nonmover_entries = {}
    all_entries = {}
    binary_mover_entries = {}
    nonbin_mover_entries = {}

    for i in range(L):
        c = cycle_configs[i]
        c_next = cycle_configs[(i + 1) % L]
        mover = word[i]

        # Mover entry
        Li = c[(mover - 1) % n]
        Si = c[mover]
        Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        mover_entries[key] = S_new
        all_entries[key] = S_new
        if ms[mover] == 2:
            binary_mover_entries[key] = S_new
        else:
            nonbin_mover_entries[key] = S_new

        # Non-mover entries
        for j in range(n):
            if j != mover:
                Lj = c[(j - 1) % n]
                Sj = c[j]
                Rj = c[(j + 1) % n]
                key2 = (j, Lj, Sj, Rj)
                nonmover_entries[key2] = Sj
                all_entries[key2] = Sj

    # Check SCC with different entry sets
    results = {
        'word': word,
        'L': L,
        'overlap_procs': overlap_procs,
        'n_mover': len(mover_entries),
        'n_nonmover': len(nonmover_entries),
        'n_all': len(all_entries),
        'n_binary_mover': len(binary_mover_entries),
        'n_nonbin_mover': len(nonbin_mover_entries),
    }

    if overlap_procs:
        results['has_overlap'] = True
        results['scc_all'] = True  # overlap → immediate contradiction
        results['scc_mover'] = True
        results['scc_binary_mover'] = True
        return results

    results['has_overlap'] = False
    results['scc_all'] = check_scc(ms, n, good_set, all_entries)
    results['scc_mover'] = check_scc(ms, n, good_set, mover_entries)
    results['scc_nonmover'] = check_scc(ms, n, good_set, nonmover_entries)
    results['scc_binary_mover'] = check_scc(ms, n, good_set, binary_mover_entries)
    results['scc_nonbin_mover'] = check_scc(ms, n, good_set, nonbin_mover_entries)

    return results


def check_scc(ms, n, good_set, required):
    """Check if required entries create an SCC among non-good configs."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        config = start
        visited = {}
        for step in range(len(non_good) + 10):
            if config in good_set:
                break
            if config in visited:
                return True  # cycle found
            visited[config] = step

            # Find forced transitions: entries where required[key] != current state
            forced = []
            for j in range(n):
                Lj = config[(j - 1) % n]
                Sj = config[j]
                Rj = config[(j + 1) % n]
                key = (j, Lj, Sj, Rj)
                if key in required and required[key] != Sj:
                    forced.append((j, required[key]))

            if not forced:
                break

            # Apply first forced transition that stays in non-good
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                break

    return False


def check_scc_thorough(ms, n, good_set, required):
    """
    More thorough SCC check: try ALL possible orderings of forced transitions.
    Return True if ANY ordering creates a cycle.
    """
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = set(c for c in all_configs if c not in good_set)

    # Build adjacency: for each non-good config, find all forced successors
    adj = defaultdict(set)
    for config in non_good:
        forced = []
        for j in range(n):
            Lj = config[(j - 1) % n]
            Sj = config[j]
            Rj = config[(j + 1) % n]
            key = (j, Lj, Sj, Rj)
            if key in required and required[key] != Sj:
                new_config = list(config)
                new_config[j] = required[key]
                new_config = tuple(new_config)
                if new_config in non_good:
                    adj[config].add(new_config)

    # Tarjan's SCC algorithm
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

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

    return len(sccs) > 0, sccs


def main():
    print("CIC Exploration 12b: Forced SCC for Single-Wiggle Words")
    print("=" * 70)

    # PART 1: Small n — check SCC with incrementing transitions
    print("\nPART 1: SCC Analysis (incrementing transitions)")
    print("-" * 70)

    configs_to_test = [
        # (n, binary_positions, ms)
        (6, [0, 2, 4], [2, 3, 2, 3, 2, 3]),
        (7, [0, 2, 4], [2, 3, 2, 3, 2, 3, 3]),
        (7, [0, 2, 5], [2, 3, 2, 3, 3, 2, 3]),
        (7, [0, 3, 5], [2, 3, 3, 2, 3, 2, 3]),
        (8, [0, 2, 5], [2, 3, 2, 3, 3, 2, 3, 3]),
        (8, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3]),
        (9, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ]

    all_results = []

    for n, bp, ms in configs_to_test:
        words = generate_wiggle_words(n, bp)
        if not words:
            print(f"  n={n} bp={bp}: 0 wiggle words")
            continue

        total = len(words)
        overlap = 0
        scc_all = 0
        scc_mover = 0
        scc_binary = 0
        scc_nonbin = 0
        valid = 0
        invalid = 0
        details = []

        for w in words:
            r = analyze_cycle_scc(ms, n, w)
            if r is None:
                invalid += 1
                continue
            valid += 1

            if r['has_overlap']:
                overlap += 1
            if r['scc_all']:
                scc_all += 1
            if r['scc_mover']:
                scc_mover += 1
            if r.get('scc_binary_mover', False):
                scc_binary += 1
            if r.get('scc_nonbin_mover', False):
                scc_nonbin += 1
            details.append(r)

        pct = lambda x: f"{100 * x / valid:.0f}%" if valid > 0 else "N/A"
        print(f"\n  n={n} bp={bp} ms={ms}")
        print(f"    Words: {total} generated, {valid} valid cycles, {invalid} invalid")
        print(f"    Overlap: {overlap}/{valid} ({pct(overlap)})")
        print(f"    SCC (all entries): {scc_all}/{valid} ({pct(scc_all)})")
        print(f"    SCC (mover only): {scc_mover}/{valid} ({pct(scc_mover)})")
        print(f"    SCC (binary mover): {scc_binary}/{valid} ({pct(scc_binary)})")
        print(f"    SCC (non-bin mover): {scc_nonbin}/{valid} ({pct(scc_nonbin)})")

        all_results.append({
            'n': n, 'bp': bp, 'valid': valid,
            'overlap': overlap, 'scc_all': scc_all,
            'scc_mover': scc_mover, 'scc_binary': scc_binary,
        })

        # Show first few details
        for r in details[:2]:
            if not r['has_overlap']:
                print(f"    Detail: L={r['L']}, entries: mover={r['n_mover']} "
                      f"(bin={r['n_binary_mover']}, nonbin={r['n_nonbin_mover']}), "
                      f"SCC={r['scc_all']}")

    # PART 2: Thorough SCC (Tarjan) for valid words
    print("\n\nPART 2: Thorough SCC (Tarjan's algorithm)")
    print("-" * 70)

    for n, bp, ms in configs_to_test[:4]:
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        total_valid = 0
        total_scc_tarjan = 0
        total_scc_binary_tarjan = 0
        max_scc_size = 0

        for w in words:
            r = analyze_cycle_scc(ms, n, w)
            if r is None or r['has_overlap']:
                if r and r['has_overlap']:
                    total_valid += 1
                    total_scc_tarjan += 1
                    total_scc_binary_tarjan += 1
                continue
            total_valid += 1

            # Extract entries for Tarjan
            config = tuple(0 for _ in range(n))
            configs_list = [config]
            for t in range(len(w)):
                c = list(config)
                c[w[t]] = (c[w[t]] + 1) % ms[w[t]]
                config = tuple(c)
                configs_list.append(config)
            good_set = set(configs_list[:len(w)])

            # All entries
            all_ent = {}
            bin_mover_ent = {}
            for i in range(len(w)):
                c = configs_list[i]
                c_next = configs_list[(i + 1) % len(w)]
                mover = w[i]
                Li = c[(mover - 1) % n]
                Si = c[mover]
                Ri = c[(mover + 1) % n]
                key = (mover, Li, Si, Ri)
                all_ent[key] = c_next[mover]
                if ms[mover] == 2:
                    bin_mover_ent[key] = c_next[mover]
                for j in range(n):
                    if j != mover:
                        key2 = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                        all_ent[key2] = c[j]

            has_scc, sccs = check_scc_thorough(ms, n, good_set, all_ent)
            if has_scc:
                total_scc_tarjan += 1
                for scc in sccs:
                    max_scc_size = max(max_scc_size, len(scc))

            has_scc_bin, sccs_bin = check_scc_thorough(ms, n, good_set, bin_mover_ent)
            if has_scc_bin:
                total_scc_binary_tarjan += 1

        pct2 = lambda x: f"{100*x/total_valid:.0f}%" if total_valid > 0 else "N/A"
        print(f"  n={n} bp={bp}: valid={total_valid}, "
              f"SCC_all={total_scc_tarjan} ({pct2(total_scc_tarjan)}), "
              f"SCC_bin={total_scc_binary_tarjan} ({pct2(total_scc_binary_tarjan)}), "
              f"max_scc={max_scc_size}")

    # PART 3: What exactly are the mover entries?
    print("\n\nPART 3: Mover Entry Structure for Single-Wiggle Words")
    print("-" * 70)

    # Focus on n=7, bp=[0,2,4], ms=[2,3,2,3,2,3,3]
    n, bp, ms = 7, [0, 2, 4], [2, 3, 2, 3, 2, 3, 3]
    words = generate_wiggle_words(n, bp)

    for w in words[:4]:
        print(f"\n  Word: {w}")
        config = tuple(0 for _ in range(n))
        configs_list = [config]
        for t in range(len(w)):
            c = list(config)
            c[w[t]] = (c[w[t]] + 1) % ms[w[t]]
            config = tuple(c)
            configs_list.append(config)

        if configs_list[-1] != configs_list[0]:
            print("  (Cycle doesn't close)")
            continue
        if len(set(configs_list[:len(w)])) != len(w):
            print("  (Duplicate configs)")
            continue

        good_set = set(configs_list[:len(w)])
        print(f"  Configs: {len(good_set)} good out of {sum(ms[i] for i in range(n))} ... "
              f"total = {1}", end="")
        total_c = 1
        for m in ms:
            total_c *= m
        print(f" ... product = {total_c}")

        # Show step-by-step
        for t in range(len(w)):
            c = configs_list[t]
            mover = w[t]
            L_val = c[(mover-1)%n]
            S_val = c[mover]
            R_val = c[(mover+1)%n]
            S_new = configs_list[(t+1)%len(w)][mover]
            m_type = 'B' if ms[mover] == 2 else 'T'
            print(f"    t={t:2d}: mover={mover}({m_type}) "
                  f"ctx=({L_val},{S_val},{R_val})→{S_new} "
                  f"config={c}")

    # PART 4: Exploration 11 actual survivors
    print("\n\nPART 4: Exploration 11 Survivors — Full SCC Analysis")
    print("-" * 70)

    test_cases = [
        # (word, n, binary_positions, ms)
        ([0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 2, 1],
         9, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        ([0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1],
         9, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        ([0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 3, 2, 1],
         9, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        ([0, 7, 6, 5, 4, 3, 2, 1, 0, 7, 6, 5, 4, 5, 4, 3, 2, 1],
         8, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3]),
    ]

    for w, n_val, bp_val, ms_val in test_cases:
        mc = Counter(w)
        fair = all(mc.get(p, 0) >= 2 for p in range(n_val))
        bpar = all(mc.get(b, 0) % 2 == 0 for b in bp_val)
        if not (fair and bpar):
            print(f"  SKIP (not fair/bpar): {w[:10]}...")
            continue

        r = analyze_cycle_scc(ms_val, n_val, w, verbose=True)
        if r is None:
            print(f"  n={n_val} {w[:15]}... INVALID CYCLE")
            continue

        print(f"  n={n_val} {w[:15]}...")
        print(f"    Overlap: {r['overlap_procs']}")
        print(f"    SCC_all={r['scc_all']}, SCC_mover={r['scc_mover']}, "
              f"SCC_binary={r.get('scc_binary_mover', '?')}")

        # Also Tarjan for detail
        if not r['has_overlap']:
            config = tuple(0 for _ in range(n_val))
            configs_list = [config]
            for t in range(len(w)):
                c = list(config)
                c[w[t]] = (c[w[t]] + 1) % ms_val[w[t]]
                config = tuple(c)
                configs_list.append(config)
            good_set = set(configs_list[:len(w)])

            all_ent = {}
            bin_ent = {}
            for i in range(len(w)):
                c = configs_list[i]
                c_next = configs_list[(i+1)%len(w)]
                mover = w[i]
                key = (mover, c[(mover-1)%n_val], c[mover], c[(mover+1)%n_val])
                all_ent[key] = c_next[mover]
                if ms_val[mover] == 2:
                    bin_ent[key] = c_next[mover]
                for j in range(n_val):
                    if j != mover:
                        key2 = (j, c[(j-1)%n_val], c[j], c[(j+1)%n_val])
                        all_ent[key2] = c[j]

            has_scc, sccs = check_scc_thorough(ms_val, n_val, good_set, all_ent)
            if has_scc:
                print(f"    Tarjan: {len(sccs)} SCC(s), sizes={[len(s) for s in sccs[:5]]}")
            else:
                print(f"    Tarjan: NO SCC found!")

            has_scc_b, sccs_b = check_scc_thorough(ms_val, n_val, good_set, bin_ent)
            if has_scc_b:
                print(f"    Binary-only Tarjan: {len(sccs_b)} SCC(s), sizes={[len(s) for s in sccs_b[:5]]}")
            else:
                print(f"    Binary-only Tarjan: NO SCC")

    # PART 5: Universal check — ALL valid wiggle words create SCC?
    print("\n\nPART 5: Universal SCC Summary")
    print("-" * 70)

    for n, bp, ms in configs_to_test:
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        valid = 0
        blocked = 0  # overlap or SCC
        for w in words:
            r = analyze_cycle_scc(ms, n, w)
            if r is None:
                continue
            valid += 1
            if r['has_overlap'] or r['scc_all']:
                blocked += 1

        tag = '✓' if blocked == valid and valid > 0 else '✗'
        print(f"  n={n} bp={bp}: {blocked}/{valid} blocked {tag}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
