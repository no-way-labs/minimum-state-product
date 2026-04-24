#!/usr/bin/env python3
"""binscc_exhaustive_general.py — Exhaustive general-transition test for Case 3a.

For EVERY P1-free mover word at n=5:
  For EVERY valid non-binary transition assignment:
    Check: overlap → conflict? Shadow? Clean?

If ZERO clean across all words × all assignments → Case 3a proved for n=5!
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
    """Build cycle with general transitions. transition_choices[(step,proc)] = new_value."""
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
    """Check for overlap, conflict, or shadow. Returns obstruction type."""
    ell = len(mover_word)

    # Full overlap at all processors
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
            return 'overlap'  # overlap → conflict (transition-independent proof)

    # No overlap. Check entry consistency and shadow.
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

    # Shadow check
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

    return 'clean'  # NO obstruction!


def enumerate_valid_assignments(ms, n, mover_word):
    """Enumerate all valid (cycle-closing, distinct) non-binary transition assignments."""
    ell = len(mover_word)

    # Identify non-binary mover steps
    nonbin_steps = []
    # Build incrementing config to know current values
    configs_inc = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs_inc[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs_inc.append(tuple(c))

    for i in range(ell):
        p = mover_word[i]
        if ms[p] > 2:
            current_val = configs_inc[i][p]
            choices = [v for v in range(ms[p]) if v != current_val]
            nonbin_steps.append((i, p, current_val, choices))

    if not nonbin_steps:
        return [{}]

    valid = []
    choice_lists = [info[3] for info in nonbin_steps]
    for combo in iproduct(*choice_lists):
        tc = {}
        for idx, (step_i, proc, _, _) in enumerate(nonbin_steps):
            tc[(step_i, proc)] = combo[idx]
        # Check if produces valid cycle
        configs = build_cycle_general(ms, n, mover_word, tc)
        if configs is not None:
            valid.append((tc, configs))

    return valid


def main():
    n = 5
    ms = [2, 2, 2, 3, 3]
    print("=" * 70)
    print(f"EXHAUSTIVE GENERAL-TRANSITION TEST: n={n} ms={tuple(ms)}")
    print("=" * 70)
    print("Testing ALL valid transition assignments for ALL P1-free mover words")
    print()

    max_len = 3 * n + 6
    t0 = time.time()
    words = enumerate_mover_words_smart(ms, n, max_len)
    print(f"Enumerated {len(words)} mover words in {time.time()-t0:.1f}s")

    # Find P1-free mover words
    p1_free_words = []
    for word in words:
        configs_inc = [tuple(0 for _ in range(n))]
        ell = len(word)
        valid = True
        for i in range(ell):
            p = word[i]
            c = list(configs_inc[-1])
            c[p] = (c[p] + 1) % ms[p]
            configs_inc.append(tuple(c))
        if configs_inc[-1] != configs_inc[0]:
            continue
        if len(set(configs_inc[:ell])) != ell:
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

        # P1 overlap check (transition-independent)
        p1_mover = set()
        p1_nonmover = set()
        for i in range(ell):
            v = (configs_inc[i][0], configs_inc[i][1], configs_inc[i][2])
            if word[i] == 1:
                p1_mover.add(v)
            else:
                p1_nonmover.add(v)
        if not (p1_mover & p1_nonmover):
            p1_free_words.append(word)

    print(f"\n{len(p1_free_words)} P1-free mover words")

    # For each, enumerate all valid transition assignments
    grand_total_valid = 0
    grand_total_obstruction = Counter()
    all_blocked = True
    clean_examples = []

    for word_idx, word in enumerate(p1_free_words):
        valid_assignments = enumerate_valid_assignments(ms, n, word)

        word_results = Counter()
        for tc, configs in valid_assignments:
            obstruction = check_obstruction(ms, n, configs, word)
            word_results[obstruction] += 1
            grand_total_obstruction[obstruction] += 1

        grand_total_valid += len(valid_assignments)

        clean = word_results.get('clean', 0)
        if clean > 0:
            all_blocked = False
            if len(clean_examples) < 5:
                clean_examples.append((word, clean, len(valid_assignments)))
            print(f"  !! Word {word_idx}: {word} has {clean}/{len(valid_assignments)} CLEAN assignments!")

        if (word_idx + 1) % 50 == 0:
            elapsed = time.time() - t0
            print(f"  ... processed {word_idx+1}/{len(p1_free_words)} P1-free words ({elapsed:.1f}s)")
            sys.stdout.flush()

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"RESULTS ({elapsed:.1f}s):")
    print(f"  P1-free mover words: {len(p1_free_words)}")
    print(f"  Total valid transition assignments: {grand_total_valid}")
    print(f"  Obstruction distribution: {dict(grand_total_obstruction)}")

    if all_blocked:
        print(f"\n  ★★ ALL {grand_total_valid} valid assignments are BLOCKED! ★★")
        print(f"  Case 3a PROVED at n=5 for ALL transition functions!")
    else:
        print(f"\n  !! {grand_total_obstruction.get('clean',0)} clean assignments found")
        for word, clean, total in clean_examples:
            print(f"    word={word}: {clean}/{total} clean")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
