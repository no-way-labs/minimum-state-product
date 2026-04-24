#!/usr/bin/env python3
"""binscc_shadow_universality.py — Do ALL sub-threshold cycles have shadows?

Test the key conjecture: at sub-threshold product with 3 consecutive binary,
EVERY valid good cycle (regardless of overlap status) is blocked by either:
  (a) entry conflict (transition inconsistency), or
  (b) shadow cycle (forced bad SCC from determined entries)

If true, this closes Case 3a without needing overlap arguments.
"""

from collections import Counter, defaultdict
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


def full_analysis(ms, n, mover_word):
    """Complete analysis: overlap at all procs + entry conflicts + shadow check.

    Returns dict with all info, or None if cycle invalid.
    """
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
    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return None
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return None

    configs_cycle = configs[:ell]

    # P1 overlap (transition-independent)
    bp0, bp1, bp2 = 0, 1, 2
    p1_mover = set()
    p1_nonmover = set()
    for i in range(ell):
        v = (configs_cycle[i][bp0], configs_cycle[i][bp1], configs_cycle[i][bp2])
        if mover_word[i] == bp1:
            p1_mover.add(v)
        else:
            p1_nonmover.add(v)
    has_p1_overlap = bool(p1_mover & p1_nonmover)

    # Full overlap at all processors
    per_proc_overlap = {}
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
        overlap = mover_ctx & nonmover_ctx
        per_proc_overlap[p] = bool(overlap)

    any_overlap = any(per_proc_overlap[p] for p in range(n))

    # Determined entries and conflict check
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
        return {
            'has_p1_overlap': has_p1_overlap,
            'per_proc_overlap': per_proc_overlap,
            'any_overlap': any_overlap,
            'has_conflict': True,
            'has_shadow': None,
            'obstruction': 'conflict',
        }

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

    total_entries = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))

    obstruction = 'shadow' if has_shadow else ('overlap' if any_overlap else 'NONE')

    return {
        'has_p1_overlap': has_p1_overlap,
        'per_proc_overlap': per_proc_overlap,
        'any_overlap': any_overlap,
        'has_conflict': False,
        'has_shadow': has_shadow,
        'obstruction': obstruction,
        'det_entries': len(required),
        'total_entries': total_entries,
    }


def main():
    print("=" * 70)
    print("SHADOW UNIVERSALITY — ALL sub-threshold cycles with 3 consec binary")
    print("=" * 70)
    print("Question: does EVERY valid cycle have conflict or shadow?")
    print("If yes → Case 3a closed without overlap arguments.")
    print()

    test_cases = [
        (5, [2, 2, 2, 3, 3], "n=5 prod=72 sub-M_5=96"),
        (7, [2, 2, 2, 3, 3, 3, 3], "n=7 prod=648 sub-M_7=864"),
    ]

    for n, ms, label in test_cases:
        prod = 1
        for m in ms:
            prod *= m

        max_len = 3 * n + 6
        print(f"\n{'='*60}")
        print(f"  {label}  (max_len={max_len})")
        print(f"{'='*60}")
        sys.stdout.flush()

        t0 = time.time()
        words = enumerate_mover_words_smart(ms, n, max_len)
        t1 = time.time()
        print(f"  Enumerated {len(words)} mover words in {t1-t0:.1f}s")
        sys.stdout.flush()

        # Categorize all valid cycles
        stats = {
            'valid': 0,
            'p1_overlap': 0,
            'p1_free': 0,
            'p1_free_any_overlap': 0,
            'p1_free_no_overlap': 0,
            'conflict': 0,
            'shadow': 0,
            'overlap_only': 0,  # overlap but no conflict/shadow
            'clean': 0,  # NO obstruction at all!
        }

        obstruction_dist = Counter()
        unblocked = []

        for idx, word in enumerate(words):
            result = full_analysis(ms, n, word)
            if result is None:
                continue
            stats['valid'] += 1

            if result['has_p1_overlap']:
                stats['p1_overlap'] += 1
                obstruction_dist['p1_overlap'] += 1
                continue

            stats['p1_free'] += 1

            if result['any_overlap']:
                stats['p1_free_any_overlap'] += 1
            else:
                stats['p1_free_no_overlap'] += 1

            if result['has_conflict']:
                stats['conflict'] += 1
                obstruction_dist['conflict'] += 1
            elif result['has_shadow']:
                stats['shadow'] += 1
                obstruction_dist['shadow'] += 1
            elif result['any_overlap']:
                stats['overlap_only'] += 1
                obstruction_dist['overlap_only'] += 1
            else:
                stats['clean'] += 1
                obstruction_dist['NONE'] += 1
                if len(unblocked) < 5:
                    unblocked.append((word, result))

            if stats['valid'] % 2000 == 0:
                elapsed = time.time() - t0
                print(f"    ... {stats['valid']} valid cycles processed ({elapsed:.1f}s)", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Results ({elapsed:.1f}s):")
        print(f"    Valid cycles: {stats['valid']}")
        print(f"    P1 overlap (transition-indep): {stats['p1_overlap']}")
        print(f"    P1-free: {stats['p1_free']}")
        print(f"      with some overlap: {stats['p1_free_any_overlap']}")
        print(f"      fully overlap-free: {stats['p1_free_no_overlap']}")
        print(f"    Blocked by conflict: {stats['conflict']}")
        print(f"    Blocked by shadow: {stats['shadow']}")
        print(f"    Blocked by overlap only: {stats['overlap_only']}")
        print(f"    UNBLOCKED (no obstruction): {stats['clean']}")

        if stats['clean'] == 0 and stats['valid'] > 0:
            print(f"\n  ★★ ALL {stats['valid']} cycles blocked! Shadow universality holds! ★★")
        elif stats['clean'] > 0:
            print(f"\n  !! {stats['clean']} cycles have NO obstruction !!")
            for word, result in unblocked:
                print(f"    word={word}")
                print(f"    det_entries={result['det_entries']}/{result['total_entries']}")

        print(f"\n  Obstruction distribution: {dict(obstruction_dist)}")
        sys.stdout.flush()

    # Also test at n=6 where P1 kills everything
    print(f"\n{'='*60}")
    print(f"  n=6 verification: P1 overlap kills all?")
    print(f"{'='*60}")
    n, ms = 6, [2, 2, 2, 3, 3, 3]
    max_len = 3 * n + 6
    t0 = time.time()
    words = enumerate_mover_words_smart(ms, n, max_len)
    valid = 0
    p1_ovl = 0
    for word in words:
        result = full_analysis(ms, n, word)
        if result is None:
            continue
        valid += 1
        if result['has_p1_overlap']:
            p1_ovl += 1
    elapsed = time.time() - t0
    print(f"  {valid} valid, {p1_ovl} P1-overlap ({elapsed:.1f}s)")
    if valid == p1_ovl:
        print(f"  ★ ALL killed by P1 overlap alone")
    else:
        print(f"  {valid - p1_ovl} survive P1")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
