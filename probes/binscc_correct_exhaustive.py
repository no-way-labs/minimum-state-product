#!/usr/bin/env python3
"""binscc_correct_exhaustive.py — CORRECTLY enumerate all valid transition assignments.

Bug in earlier scripts: used incrementing current values to enumerate choices.
With non-incrementing transitions, current values at each step depend on
previous choices. Must enumerate recursively or use proc-level modes.

Correct approach: at each non-binary mover step, choose target ≠ ACTUAL current.
Build configs dynamically. Check cycle closure + distinctness.
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


def enumerate_valid_cycles_recursive(ms, n, mover_word):
    """CORRECTLY enumerate all valid cycles by choosing transitions dynamically.

    At each non-binary mover step, try all target values ≠ current.
    Binary steps always flip. Check consistency: same context must give same target.
    """
    ell = len(mover_word)
    start = tuple(0 for _ in range(n))
    results = []

    def dfs(step, configs, transition_map):
        """Build configs step by step. transition_map: (proc, L, S, R) → target."""
        if step == ell:
            # Check cycle closure
            if configs[-1] == start and len(set(configs[:-1])) == ell:
                results.append(list(configs[:-1]))
            return

        current = configs[-1]
        p = mover_word[step]
        L = current[(p-1) % n]
        S = current[p]
        R = current[(p+1) % n]
        ctx = (p, L, S, R)

        if ms[p] == 2:
            # Binary: forced flip
            new_val = 1 - S
            new_config = list(current)
            new_config[p] = new_val
            new_config = tuple(new_config)

            # Check consistency
            if ctx in transition_map:
                if transition_map[ctx] != new_val:
                    return  # Inconsistent
            new_map = dict(transition_map)
            new_map[ctx] = new_val

            # Also add nonmover entries
            conflict = False
            for j in range(n):
                if j != p:
                    Lj = current[(j-1)%n]; Sj = current[j]; Rj = current[(j+1)%n]
                    ctx_j = (j, Lj, Sj, Rj)
                    if ctx_j in new_map:
                        if new_map[ctx_j] != Sj:
                            conflict = True
                            break
                    else:
                        new_map[ctx_j] = Sj
            if conflict:
                return

            dfs(step + 1, configs + [new_config], new_map)
        else:
            # Non-binary: try all target values ≠ S
            for new_val in range(ms[p]):
                if new_val == S:
                    continue  # Must change state

                # Check consistency
                if ctx in transition_map:
                    if transition_map[ctx] != new_val:
                        continue  # Inconsistent with earlier choice
                new_map = dict(transition_map)
                new_map[ctx] = new_val

                new_config = list(current)
                new_config[p] = new_val
                new_config = tuple(new_config)

                # Check nonmover consistency
                conflict = False
                for j in range(n):
                    if j != p:
                        Lj = current[(j-1)%n]; Sj = current[j]; Rj = current[(j+1)%n]
                        ctx_j = (j, Lj, Sj, Rj)
                        if ctx_j in new_map:
                            if new_map[ctx_j] != Sj:
                                conflict = True
                                break
                        else:
                            new_map[ctx_j] = Sj
                if conflict:
                    continue

                dfs(step + 1, configs + [new_config], new_map)

    dfs(0, [start], {})
    return results


def check_obstruction(ms, n, configs, mover_word):
    """Check if cycle has overlap or shadow."""
    ell = len(mover_word)

    # Full overlap
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
        if mover_ctx & nonmover_ctx:
            return 'overlap'

    # Entries + shadow
    required = {}
    for i in range(ell):
        c = configs[i]
        c_next = configs[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return 'invalid'
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        required[key] = S_new
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                required[key2] = Sj

    good_set = set(configs)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        config = start
        visited = {}
        for step in range(300):
            if config in good_set:
                break
            if config in visited:
                return 'shadow'
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

    return 'clean'


def main():
    n = 5
    ms = [2, 2, 2, 3, 3]
    print("=" * 70)
    print(f"CORRECT EXHAUSTIVE TEST: n={n} ms={tuple(ms)}")
    print("=" * 70)
    print("Using RECURSIVE enumeration with dynamic current values")
    print("and transition-map consistency checking.\n")

    max_len = 3 * n + 6
    t0 = time.time()
    words = enumerate_mover_words_smart(ms, n, max_len)
    print(f"Enumerated {len(words)} mover words in {time.time()-t0:.1f}s")

    # Find P1-free words
    p1_free_words = []
    for word in words:
        ell = len(word)
        configs = [tuple(0 for _ in range(n))]
        valid = True
        for i in range(ell):
            p = word[i]
            c = list(configs[-1])
            c[p] = (c[p] + 1) % ms[p]
            configs.append(tuple(c))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:ell])) != ell:
            continue
        fire_counts = [0] * n
        for p in word:
            fire_counts[p] += 1
        for p in range(n):
            if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
                valid = False
                break
        if not valid:
            continue
        for i in range(ell):
            p1 = word[i]
            p2 = word[(i+1) % ell]
            diff = abs(p1 - p2)
            if diff != 1 and diff != n - 1:
                valid = False
                break
        if not valid:
            continue

        p1_mover = set()
        p1_nonmover = set()
        for i in range(ell):
            v = (configs[i][0], configs[i][1], configs[i][2])
            if word[i] == 1:
                p1_mover.add(v)
            else:
                p1_nonmover.add(v)
        if not (p1_mover & p1_nonmover):
            p1_free_words.append(word)

    print(f"{len(p1_free_words)} P1-free mover words")
    sys.stdout.flush()

    # For each, recursively enumerate ALL valid cycles
    grand_total = Counter()
    n_assignments_per_word = Counter()
    all_blocked = True

    for word_idx, word in enumerate(p1_free_words):
        t1 = time.time()
        valid_cycles = enumerate_valid_cycles_recursive(ms, n, word)
        t2 = time.time()

        word_results = Counter()
        for configs in valid_cycles:
            obstruction = check_obstruction(ms, n, configs, word)
            word_results[obstruction] += 1
            grand_total[obstruction] += 1

        n_valid = len(valid_cycles)
        n_assignments_per_word[n_valid] += 1
        clean = word_results.get('clean', 0)

        if clean > 0:
            all_blocked = False
            print(f"  !! Word {word_idx}: {word}")
            print(f"     {n_valid} valid, clean={clean}: {dict(word_results)}")

        if word_idx < 6 or n_valid != 1:
            print(f"  Word {word_idx}: {word} → {n_valid} valid assignments, {dict(word_results)} ({t2-t1:.2f}s)")

        if (word_idx + 1) % 50 == 0:
            print(f"  ... {word_idx+1}/{len(p1_free_words)} processed")
        sys.stdout.flush()

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"RESULTS ({elapsed:.1f}s):")
    print(f"  P1-free mover words: {len(p1_free_words)}")
    print(f"  Valid assignments per word: {dict(n_assignments_per_word)}")
    print(f"  Total valid assignments: {sum(grand_total.values())}")
    print(f"  Obstruction distribution: {dict(grand_total)}")

    if all_blocked:
        print(f"\n  ★★ ALL valid assignments BLOCKED! ★★")
    else:
        print(f"\n  !! Some clean assignments found")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
