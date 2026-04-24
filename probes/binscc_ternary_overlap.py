#!/usr/bin/env python3
"""binscc_ternary_overlap.py — Where do the 48 fully overlap-free cycles fail?

48 cycles at n=5 ms=(2,2,2,3,3) avoid overlap at ALL binary processors
(P0, P1, P2) with incrementing transitions. But no valid system exists
at product 72. What blocks them?

Hypothesis: overlap at TERNARY processors P3 or P4.
Check: do all 48 have ternary overlap with incrementing?
Then: with general transitions, can ternary overlap be avoided simultaneously
with binary separation?
"""

from collections import defaultdict
import sys


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


def full_overlap_analysis(ms, n, mover_word):
    """Check overlap at ALL processors and return detailed per-proc info."""
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

    per_proc = {}
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(ell):
            c = configs[i]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if mover_word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        overlap = mover_ctx & nonmover_ctx
        per_proc[p] = {
            'mover': mover_ctx,
            'nonmover': nonmover_ctx,
            'overlap': overlap,
            'has_overlap': bool(overlap),
        }

    return per_proc, configs[:ell]


def main():
    n = 5
    ms = [2, 2, 2, 3, 3]

    print("=" * 70)
    print(f"TERNARY OVERLAP ANALYSIS: n={n} ms={tuple(ms)} prod=72")
    print("=" * 70)

    max_len = 3 * n + 6
    words = enumerate_mover_words_smart(ms, n, max_len)

    # Find P1-free cycles with no binary overlap
    binary_free_cycles = []

    for word in words:
        result = full_overlap_analysis(ms, n, word)
        if result is None:
            continue
        per_proc, configs = result

        # Check binary overlap
        binary_overlap = any(per_proc[p]['has_overlap'] for p in [0, 1, 2])
        if binary_overlap:
            continue

        # This cycle has no binary overlap. Check ternary.
        ternary_overlap = [p for p in [3, 4] if per_proc[p]['has_overlap']]
        any_overlap = any(per_proc[p]['has_overlap'] for p in range(n))

        binary_free_cycles.append((word, per_proc, configs, ternary_overlap, any_overlap))

    print(f"\n{len(binary_free_cycles)} cycles with NO binary overlap (P0,P1,P2 clean)")

    # Categorize by ternary overlap
    p3_only = sum(1 for _, _, _, to, _ in binary_free_cycles if to == [3])
    p4_only = sum(1 for _, _, _, to, _ in binary_free_cycles if to == [4])
    both = sum(1 for _, _, _, to, _ in binary_free_cycles if set(to) == {3, 4})
    neither = sum(1 for _, _, _, to, _ in binary_free_cycles if not to)

    print(f"  P3 overlap only: {p3_only}")
    print(f"  P4 overlap only: {p4_only}")
    print(f"  Both P3,P4 overlap: {both}")
    print(f"  NO overlap at any proc: {neither}")

    if neither > 0:
        print(f"\n  ★★ {neither} cycles have NO OVERLAP AT ANY PROCESSOR!")
        print("  These must be blocked by SCC, shadow, conflict, or non-convergence.")

    # Show details of overlap-free cycles
    for idx, (word, per_proc, configs, ternary_overlap, any_overlap) in enumerate(binary_free_cycles):
        if any_overlap:
            continue  # skip cycles with overlap, focus on fully clean

        print(f"\n  FULLY CLEAN cycle #{idx}: {word}")
        print(f"    Length: {len(word)}")
        for p in range(n):
            pp = per_proc[p]
            print(f"    P{p} (m={ms[p]}): mover={sorted(pp['mover'])}, "
                  f"nonmover_size={len(pp['nonmover'])}, overlap={'NONE' if not pp['overlap'] else pp['overlap']}")

        # Check determined entries and conflicts
        required = {}
        has_conflict = False
        for i in range(len(configs)):
            c = configs[i]
            c_next = configs[(i+1) % len(configs)]
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
            print(f"    → HAS ENTRY CONFLICT ← (blocked)")
        else:
            total_entries = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
            print(f"    Determined entries: {len(required)}/{total_entries} ({100*len(required)/total_entries:.0f}%)")

            # Check shadow
            good_set = set(configs)
            from itertools import product as iproduct
            all_configs = list(iproduct(*[range(m) for m in ms]))
            non_good = [c for c in all_configs if c not in good_set]

            has_shadow = False
            for start in non_good:
                config = start
                visited = {}
                path = []
                for step in range(200):
                    if config in good_set:
                        break
                    if config in visited:
                        has_shadow = True
                        break
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
                if has_shadow:
                    break

            if has_shadow:
                print(f"    → HAS SHADOW CYCLE ← (blocked)")
            else:
                print(f"    → NO SHADOW, NO CONFLICT ← genuine survivor candidate!")

        if idx >= 15:  # limit output
            break

    sys.stdout.flush()


if __name__ == "__main__":
    main()
