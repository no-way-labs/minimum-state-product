#!/usr/bin/env python3
"""binscc_shadow_comprehensive.py — Shadow universality across ALL sub-threshold multisets.

For each n and each sub-threshold multiset with 3 consecutive binary,
check if EVERY valid cycle is blocked by conflict, shadow, or P1 overlap.
"""

from collections import Counter
from itertools import product as iproduct
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


def check_cycle(ms, n, mover_word):
    """Check if cycle is blocked. Returns (is_valid, obstruction_type)."""
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return False, None
    if len(set(configs[:ell])) != ell:
        return False, None
    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, None
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, None

    configs_cycle = configs[:ell]

    # P1 overlap (binary procs at 0,1,2)
    p1_mover = set()
    p1_nonmover = set()
    for i in range(ell):
        v = (configs_cycle[i][0], configs_cycle[i][1], configs_cycle[i][2])
        if mover_word[i] == 1:
            p1_mover.add(v)
        else:
            p1_nonmover.add(v)
    if p1_mover & p1_nonmover:
        return True, 'p1_overlap'

    # Entry conflicts
    required = {}
    has_conflict = False
    for i in range(ell):
        c = configs_cycle[i]
        c_next = configs_cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            has_conflict = True
            break
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            has_conflict = True
            break
        required[key] = S_new
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in required and required[key2] != Sj:
                    has_conflict = True
                    break
                required[key2] = Sj
        if has_conflict:
            break

    if has_conflict:
        return True, 'conflict'

    # Full overlap at all processors (with incrementing)
    any_overlap = False
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(ell):
            c = configs_cycle[i]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover_word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            any_overlap = True
            break

    # Shadow check
    good_set = set(configs_cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    has_shadow = False
    for start in non_good:
        config = start
        visited = {}
        for step in range(300):
            if config in good_set:
                break
            if config in visited:
                has_shadow = True
                break
            visited[config] = step
            forced = []
            for j in range(n):
                Lj = config[(j-1)%n]; Sj = config[j]; Rj = config[(j+1)%n]
                key = (j, Lj, Sj, Rj)
                if key in required and required[key] != Sj:
                    forced.append((j, required[key]))
            if not forced:
                break
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
        if has_shadow:
            break

    if has_shadow:
        return True, 'shadow'
    if any_overlap:
        return True, 'overlap_only'
    return True, 'CLEAN'


def gen_sub_threshold_multisets(n, threshold):
    """Generate all multisets (2,2,2,m3,...,m_{n-1}) with product < threshold."""
    non_bin = n - 3
    max_non_bin_prod = threshold // 8  # product = 8 * prod(m3,...,m_{n-1})
    ms_list = []

    def gen(depth, remaining_prod, current, min_val):
        if depth == non_bin:
            ms_list.append([2, 2, 2] + current)
            return
        for m in range(min_val, remaining_prod + 1):
            # Check if remaining positions can achieve product < threshold
            remaining_depth = non_bin - depth - 1
            if remaining_depth == 0:
                if m < remaining_prod:
                    ms_list.append([2, 2, 2] + current + [m])
            else:
                # Each remaining >= m, so prod >= m^remaining_depth
                # Need m * remaining_prod_for_rest < remaining_prod
                new_remaining = remaining_prod // m
                if new_remaining >= m:  # at least one more factor >= m
                    gen(depth + 1, new_remaining, current + [m], m)

    # Actually simpler: just enumerate directly for small n
    if non_bin == 2:  # n=5
        for m3 in range(3, max_non_bin_prod + 1):
            for m4 in range(m3, max_non_bin_prod // m3 + 1):
                if 8 * m3 * m4 < threshold:
                    ms_list.append([2, 2, 2, m3, m4])
    elif non_bin == 3:  # n=6
        for m3 in range(3, max_non_bin_prod + 1):
            for m4 in range(m3, max_non_bin_prod // m3 + 1):
                remain = max_non_bin_prod // (m3 * m4)
                for m5 in range(m4, remain + 1):
                    if 8 * m3 * m4 * m5 < threshold:
                        ms_list.append([2, 2, 2, m3, m4, m5])
    elif non_bin == 4:  # n=7
        for m3 in range(3, max_non_bin_prod + 1):
            for m4 in range(m3, max_non_bin_prod // m3 + 1):
                for m5 in range(m4, max_non_bin_prod // (m3 * m4) + 1):
                    remain = max_non_bin_prod // (m3 * m4 * m5)
                    for m6 in range(m5, remain + 1):
                        if 8 * m3 * m4 * m5 * m6 < threshold:
                            ms_list.append([2, 2, 2, m3, m4, m5, m6])
    return ms_list


def main():
    print("=" * 70)
    print("SHADOW UNIVERSALITY — COMPREHENSIVE SUB-THRESHOLD SWEEP")
    print("=" * 70)
    print()

    thresholds = {5: 96, 6: 288, 7: 864}

    for n in [5, 6, 7]:
        threshold = thresholds[n]
        ms_list = gen_sub_threshold_multisets(n, threshold)

        print(f"\n{'='*60}")
        print(f"  n={n}: threshold M_{n}={threshold}, {len(ms_list)} sub-threshold multisets")
        print(f"{'='*60}")

        all_universal = True
        for ms in ms_list:
            prod = 1
            for m in ms:
                prod *= m

            max_len = 3 * n + 6
            t0 = time.time()
            words = enumerate_mover_words_smart(ms, n, max_len)

            obstruction_counts = Counter()
            valid = 0
            for word in words:
                is_valid, obstruction = check_cycle(ms, n, word)
                if not is_valid:
                    continue
                valid += 1
                obstruction_counts[obstruction] += 1

            elapsed = time.time() - t0
            clean = obstruction_counts.get('CLEAN', 0)
            status = "★ ALL BLOCKED" if clean == 0 and valid > 0 else f"!! {clean} CLEAN !!"
            if valid == 0:
                status = "(no valid cycles)"

            print(f"  ms={tuple(ms)} prod={prod}: {valid} valid, "
                  f"p1={obstruction_counts.get('p1_overlap',0)} "
                  f"conf={obstruction_counts.get('conflict',0)} "
                  f"shad={obstruction_counts.get('shadow',0)} "
                  f"ovl={obstruction_counts.get('overlap_only',0)} "
                  f"clean={clean} → {status} ({elapsed:.1f}s)")

            if clean > 0:
                all_universal = False

            sys.stdout.flush()

        if all_universal:
            print(f"\n  ★★ n={n}: SHADOW UNIVERSALITY CONFIRMED for ALL {len(ms_list)} multisets! ★★")
        else:
            print(f"\n  !! n={n}: shadow universality FAILS for some multisets")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
