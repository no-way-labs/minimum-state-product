#!/usr/bin/env python3
"""binscc_survivor_analysis.py — Analyze surviving clean cycles from shadow test.

90 cycles at n=6 ms=(2,2,3,3,2,4) survived:
  - No mover/nonmover overlap at any binary processor
  - No entry conflicts
  - No shadow cycle found by boundary search

Question: is the boundary search incomplete, or are these genuine survivors?
Do a FULL shadow search over ALL non-good configs.
Also check: do these surviving cycles actually form good sets that could
be part of a valid system?
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


def build_determined_entries(configs, ms, n):
    """Build determined entries from a cycle."""
    ell = len(configs)
    required = {}
    for idx in range(ell):
        c = configs[idx]
        c_next = configs[(idx + 1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return None  # conflict
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
                key2 = (i, Li2, Si2, Ri2)
                if key2 in required and required[key2] != Si2:
                    return None  # conflict
                required[key2] = Si2
    return required


def full_shadow_search(configs, required, ms, n):
    """Full shadow search: try ALL non-good configs."""
    good_set = set(configs)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        config = start
        visited = {}
        path = []
        for step in range(500):
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


def boundary_shadow_search(configs, required, ms, n):
    """Boundary search: only try configs 1-flip from good set."""
    good_set = set(configs)

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


def main():
    print("=" * 70)
    print("SURVIVOR ANALYSIS: Full vs boundary shadow search")
    print("=" * 70)

    # ================================================================
    # Part 1: The surviving case n=6, ms=(2,2,3,3,2,4)
    # ================================================================
    ms = [2, 2, 3, 3, 2, 4]
    n = 6
    max_len = 3 * n + 4

    print(f"\nms={tuple(ms)}, n={n}, product={2*2*3*3*2*4}")
    print(f"Total state space: {2*2*3*3*2*4} configs")

    t0 = time.time()
    words = enumerate_mover_words_smart(ms, n, max_len)
    print(f"Enumerated {len(words)} mover words in {time.time()-t0:.1f}s")

    # Find clean (no overlap) cycles
    clean_cycles = []
    for word in words:
        is_valid, has_ovlp, proc, configs = check_overlap_for_mover_word(ms, n, word)
        if not is_valid or has_ovlp:
            continue
        required = build_determined_entries(configs, ms, n)
        if required is None:
            continue  # has conflict
        clean_cycles.append((word, configs, required))

    print(f"Clean cycles (no overlap, no conflict): {len(clean_cycles)}")
    sys.stdout.flush()

    if not clean_cycles:
        print("No clean cycles — all blocked!")
        return

    # Full shadow search on first few
    print(f"\n--- Full shadow search on {min(10, len(clean_cycles))} clean cycles ---")

    full_shadow_count = 0
    full_no_shadow = 0
    boundary_shadow_count = 0
    boundary_no_shadow = 0

    for idx, (word, configs, required) in enumerate(clean_cycles[:10]):
        # Full search
        shadow_f, status_f = full_shadow_search(configs, required, ms, n)
        # Boundary search
        shadow_b, status_b = boundary_shadow_search(configs, required, ms, n)

        f_result = "SHADOW" if status_f == "shadow" else "no shadow"
        b_result = "SHADOW" if status_b == "shadow" else "no shadow"

        if status_f == "shadow":
            full_shadow_count += 1
        else:
            full_no_shadow += 1
        if status_b == "shadow":
            boundary_shadow_count += 1
        else:
            boundary_no_shadow += 1

        match = "MATCH" if f_result == b_result else "MISMATCH"
        print(f"  Cycle {idx}: full={f_result}, boundary={b_result} → {match}")

        if f_result != b_result:
            print(f"    Word: {word}")
            if shadow_f:
                print(f"    Full shadow (len={len(shadow_f)}): {shadow_f[:3]}...")

        sys.stdout.flush()

    print(f"\nFull: {full_shadow_count} shadow, {full_no_shadow} no shadow")
    print(f"Boundary: {boundary_shadow_count} shadow, {boundary_no_shadow} no shadow")

    # ================================================================
    # Part 2: For genuine survivors, analyze structure
    # ================================================================
    if full_no_shadow > 0:
        print(f"\n{'='*70}")
        print("GENUINE SURVIVORS — detailed analysis")
        print("="*70)

        for idx, (word, configs, required) in enumerate(clean_cycles[:20]):
            shadow_f, status_f = full_shadow_search(configs, required, ms, n)
            if status_f == "shadow":
                continue

            print(f"\nSurvivor: word={word}")
            print(f"  Length: {len(word)}, fire counts: {Counter(word)}")
            print(f"  Determined entries: {len(required)}")

            # Count total possible entries
            total_entries = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
            print(f"  Total entries: {total_entries}")
            print(f"  Fill rate: {100*len(required)/total_entries:.1f}%")

            # Count free entries
            free_mover = 0
            free_nonmover = 0
            for i in range(n):
                for L in range(ms[(i-1)%n]):
                    for S in range(ms[i]):
                        for R in range(ms[(i+1)%n]):
                            key = (i, L, S, R)
                            if key not in required:
                                free_mover += 1
                            # As nonmover entry, it's determined if required[key] == S
                            # and free otherwise
                            if key in required and required[key] == S:
                                pass  # nonmover determined (stay)
                            elif key not in required:
                                free_nonmover += 1

            print(f"  Free entries (undetermined): {free_mover}")

            # Show configs
            for i, c in enumerate(configs[:8]):
                c_next = configs[(i+1) % len(configs)]
                diffs = [j for j in range(n) if c[j] != c_next[j]]
                mover = diffs[0] if len(diffs) == 1 else -1
                print(f"    c_{i} = {c}  (mover={mover})")
            if len(configs) > 8:
                print(f"    ... ({len(configs)} total)")

            # Check: how many non-good configs have forced moves?
            good_set = set(configs)
            all_configs = list(iproduct(*[range(m) for m in ms]))
            non_good = [c for c in all_configs if c not in good_set]

            forced_count = 0
            stuck_count = 0
            escape_count = 0

            for config in non_good:
                forced = []
                for j in range(n):
                    Lj = config[(j-1)%n]; Sj = config[j]; Rj = config[(j+1)%n]
                    key = (j, Lj, Sj, Rj)
                    if key in required and required[key] != Sj:
                        forced.append((j, required[key]))

                if forced:
                    forced_count += 1
                    # Check if any forced move leads outside good set
                    any_escape = False
                    for proc, new_val in forced:
                        new_config = list(config)
                        new_config[proc] = new_val
                        new_config = tuple(new_config)
                        if new_config not in good_set:
                            any_escape = True
                            break
                    if any_escape:
                        escape_count += 1
                    else:
                        stuck_count += 1
                        # All forced moves go INTO good set — no shadow possible from here

            print(f"  Non-good configs: {len(non_good)}")
            print(f"    With forced moves: {forced_count}")
            print(f"    Forced but all→good: {stuck_count} (no shadow possible)")
            print(f"    Forced with escape: {escape_count} (potential shadow)")
            print(f"    No forced moves: {len(non_good) - forced_count} (free)")

            sys.stdout.flush()

    # ================================================================
    # Part 3: Pure {2,3} — are all clean cycles blocked?
    # ================================================================
    print(f"\n{'='*70}")
    print("PURE {2,3}: Full shadow search on clean cycles")
    print("="*70)

    for test_n in [5, 6]:
        ms_base = [2, 2, 2] + [3] * (test_n - 3)
        seen = set()
        non_consec = []
        for perm in set(__import__('itertools').permutations(tuple(sorted(ms_base)))):
            has_3_consec = False
            for i in range(test_n):
                if perm[i] == 2 and perm[(i+1)%test_n] == 2 and perm[(i+2)%test_n] == 2:
                    has_3_consec = True
                    break
            if has_3_consec:
                continue
            rotations = [perm[i:] + perm[:i] for i in range(test_n)]
            reflected = perm[::-1]
            ref_rotations = [reflected[i:] + reflected[:i] for i in range(test_n)]
            canonical = min(rotations + ref_rotations)
            if canonical not in seen:
                seen.add(canonical)
                non_consec.append(canonical)

        total_clean = 0
        total_conflict = 0
        total_shadow_full = 0
        total_surviving = 0

        for ms_tuple in non_consec:
            ms_test = list(ms_tuple)
            max_l = 3 * test_n + 4
            words = enumerate_mover_words_smart(ms_test, test_n, max_l)

            for word in words:
                is_valid, has_ovlp, proc, configs = check_overlap_for_mover_word(ms_test, test_n, word)
                if not is_valid or has_ovlp:
                    continue

                required = build_determined_entries(configs, ms_test, test_n)
                if required is None:
                    total_conflict += 1
                    continue

                total_clean += 1

                # Full shadow search
                shadow, status = full_shadow_search(configs, required, ms_test, test_n)
                if status == "shadow":
                    total_shadow_full += 1
                else:
                    total_surviving += 1
                    if total_surviving <= 3:
                        print(f"  SURVIVING: n={test_n} ms={ms_tuple} word={word}")

        print(f"  n={test_n}: {total_clean} clean (no overlap, no conflict)")
        print(f"    → {total_shadow_full} full shadow + {total_surviving} surviving")
        if total_surviving == 0:
            print(f"    ★ ALL BLOCKED")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
