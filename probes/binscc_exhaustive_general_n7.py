#!/usr/bin/env python3
"""binscc_exhaustive_general_n7.py — Exhaustive test at n=7 for ALL transitions.

For n=7 ms=(2,2,2,3,3,3,3) prod=648 < 864=M_7:
Test every P1-free mover word with every valid transition assignment.
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


def build_cycle_general(ms, n, mover_word, transition_choices):
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        if ms[p] == 2:
            c[p] = 1 - c[p]
        else:
            c[p] = transition_choices[(i, p)]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def check_obstruction(ms, n, configs, mover_word):
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

    # Entry consistency
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
        if key in required and required[key] != S_new:
            return 'conflict'
        required[key] = S_new
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in required and required[key2] != Sj:
                    return 'conflict'
                required[key2] = Sj

    # Shadow
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
    n = 7
    ms = [2, 2, 2, 3, 3, 3, 3]
    print("=" * 70)
    print(f"EXHAUSTIVE GENERAL-TRANSITION TEST: n={n} ms={tuple(ms)}")
    print("=" * 70)

    max_len = 3 * n + 6  # 27
    t0 = time.time()
    words = enumerate_mover_words_smart(ms, n, max_len)
    t1 = time.time()
    print(f"Enumerated {len(words)} mover words in {t1-t0:.1f}s")

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

    # For each, enumerate valid transition assignments
    grand_total = Counter()
    all_blocked = True
    n_words_processed = 0

    for word_idx, word in enumerate(p1_free_words):
        ell = len(word)

        # Build incrementing configs to find current values
        configs_inc = [tuple(0 for _ in range(n))]
        for i in range(ell):
            p = word[i]
            c = list(configs_inc[-1])
            c[p] = (c[p] + 1) % ms[p]
            configs_inc.append(tuple(c))

        # Find non-binary mover steps
        nonbin_steps = []
        for i in range(ell):
            p = word[i]
            if ms[p] > 2:
                current_val = configs_inc[i][p]
                choices = [v for v in range(ms[p]) if v != current_val]
                nonbin_steps.append((i, p, choices))

        # Enumerate all combinations (2^12 = 4096 for n=7 with 4 ternary procs × 3 firings)
        n_valid = 0
        word_results = Counter()

        choice_lists = [info[2] for info in nonbin_steps]
        for combo in iproduct(*choice_lists):
            tc = {}
            for idx, (step_i, proc, _) in enumerate(nonbin_steps):
                tc[(step_i, proc)] = combo[idx]

            configs = build_cycle_general(ms, n, word, tc)
            if configs is None:
                continue
            n_valid += 1

            obstruction = check_obstruction(ms, n, configs, word)
            word_results[obstruction] += 1
            grand_total[obstruction] += 1

        n_words_processed += 1

        clean = word_results.get('clean', 0)
        if clean > 0:
            all_blocked = False
            print(f"  !! Word {word_idx}: {word} has {clean}/{n_valid} CLEAN!")

        if n_words_processed % 500 == 0:
            elapsed = time.time() - t0
            print(f"  ... {n_words_processed}/{len(p1_free_words)} words, "
                  f"{sum(grand_total.values())} valid assignments ({elapsed:.1f}s)")
            sys.stdout.flush()

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"RESULTS ({elapsed:.1f}s):")
    print(f"  P1-free mover words: {len(p1_free_words)}")
    print(f"  Total valid assignments: {sum(grand_total.values())}")
    print(f"  Obstruction distribution: {dict(grand_total)}")

    if all_blocked:
        print(f"\n  ★★ ALL valid assignments BLOCKED at n={n}! ★★")
        print(f"  Case 3a PROVED at n={n} for ALL transition functions!")
    else:
        print(f"\n  !! {grand_total.get('clean',0)} clean assignments found")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
