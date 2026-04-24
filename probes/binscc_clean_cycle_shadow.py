#!/usr/bin/env python3
"""binscc_clean_cycle_shadow.py — Do clean (overlap-free) non-consecutive
cycles have shadows?

If every clean cycle also creates a shadow → theorem holds (shadow blocks
all cycles, not just sweeps).
"""

from itertools import product as iproduct
from collections import Counter
import time
import sys


def check_overlap_for_mover_word(ms, n, mover_word):
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    if configs[-1] != configs[0]:
        return False, False, None, None

    if len(set(configs[:ell])) != ell:
        return False, False, None, None

    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return False, False, None, None

    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return False, False, None, None

    for p in range(n):
        if ms[p] != 2:
            continue
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(ell):
            c = configs[i]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover_word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True, True, p, configs[:ell]

    return True, False, None, configs[:ell]


def check_shadow_for_cycle(configs, ms, n):
    """Check if the cycle's determined entries create a shadow."""
    ell = len(configs)
    good_set = set(configs)

    # Build determined entries
    required = {}
    for idx in range(ell):
        c = configs[idx]
        c_next = configs[(idx + 1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None, "bad cycle"
        mover = diffs[0]

        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return None, "mover conflict"
        required[key] = S_new

        for i in range(n):
            if i != mover:
                Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return None, "nonmover conflict"
                required[key2] = Si2

    # Check for shadow: try boundary configs
    for gc in configs:
        for i in range(n):
            for v in range(ms[i]):
                if v == gc[i]:
                    continue
                bc = list(gc)
                bc[i] = v
                bc = tuple(bc)
                if bc in good_set:
                    continue

                config = bc
                visited = {}
                path = []
                for step in range(300):
                    if config in good_set:
                        break
                    if config in visited:
                        return path[visited[config]:], "shadow"
                    visited[config] = step
                    path.append(config)
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

    return None, "no shadow"


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


def main():
    print("=" * 70)
    print("CLEAN CYCLE SHADOW TEST")
    print("=" * 70)
    print("Do overlap-free cycles with non-consecutive binary have shadows?")
    print()

    for n in [5, 6]:
        for ms_label, ms_base in [
            ("pure {2,3}", [2, 2, 2] + [3] * (n - 3)),
            ("mixed {2,3,4}", [2, 2, 2, 4] + [3] * (n - 4)) if n >= 5 else None,
        ]:
            if ms_base is None:
                continue

            # Generate non-consecutive orientations
            seen = set()
            non_consec = []
            for perm in set(__import__('itertools').permutations(tuple(sorted(ms_base)))):
                has_3_consec = False
                for i in range(n):
                    if perm[i] == 2 and perm[(i+1)%n] == 2 and perm[(i+2)%n] == 2:
                        has_3_consec = True
                        break
                if has_3_consec:
                    continue
                rotations = [perm[i:] + perm[:i] for i in range(n)]
                reflected = perm[::-1]
                ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
                canonical = min(rotations + ref_rotations)
                if canonical not in seen:
                    seen.add(canonical)
                    non_consec.append(canonical)

            print(f"\n--- n={n}, {ms_label}, {len(non_consec)} non-consec orientations ---")

            total_clean = 0
            total_shadow = 0
            total_conflict = 0
            total_no_shadow = 0

            for ms_tuple in non_consec:
                ms = list(ms_tuple)
                max_len = 3 * n + 4

                t0 = time.time()
                words = enumerate_mover_words_smart(ms, n, max_len)

                ms_clean = 0
                ms_shadow = 0
                ms_conflict = 0
                ms_no_shadow = 0
                sample_no_shadow = []

                for word in words:
                    is_valid, has_ovlp, proc, configs = check_overlap_for_mover_word(ms, n, word)
                    if not is_valid or has_ovlp:
                        continue

                    # This is a clean (overlap-free) cycle
                    ms_clean += 1
                    shadow, status = check_shadow_for_cycle(configs, ms, n)

                    if status == "mover conflict" or status == "nonmover conflict":
                        ms_conflict += 1
                    elif status == "shadow":
                        ms_shadow += 1
                    else:
                        ms_no_shadow += 1
                        if len(sample_no_shadow) < 3:
                            sample_no_shadow.append(word)

                elapsed = time.time() - t0
                total_clean += ms_clean
                total_shadow += ms_shadow
                total_conflict += ms_conflict
                total_no_shadow += ms_no_shadow

                if ms_clean > 0:
                    status_str = "ALL BLOCKED" if ms_no_shadow == 0 else f"{ms_no_shadow} SURVIVING"
                    print(f"  ms={ms_tuple}: {ms_clean} clean cycles → "
                          f"{ms_conflict} conflict, {ms_shadow} shadow, "
                          f"{ms_no_shadow} no-shadow → {status_str} ({elapsed:.1f}s)")

                    for w in sample_no_shadow:
                        print(f"    SURVIVING: {w}")
                sys.stdout.flush()

            print(f"\n  TOTAL: {total_clean} clean cycles → "
                  f"{total_conflict} conflict + {total_shadow} shadow + "
                  f"{total_no_shadow} no-shadow")

            if total_no_shadow == 0 and total_clean > 0:
                print(f"  ★ ALL CLEAN CYCLES BLOCKED (by conflict or shadow)")
            else:
                print(f"  ✗ {total_no_shadow} SURVIVING CLEAN CYCLES")


if __name__ == "__main__":
    main()
