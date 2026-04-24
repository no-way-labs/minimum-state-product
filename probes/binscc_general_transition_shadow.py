#!/usr/bin/env python3
"""binscc_general_transition_shadow.py — Do shadows persist for ALL transition functions?

The key question: for P1-free, overlap-free cycles at sub-threshold product,
does EVERY possible non-binary transition assignment create shadows?

At n=5 ms=(2,2,2,3,3):
- Binary procs always flip (transition forced)
- Ternary procs P3,P4 can transition to ANY value ≠ current (2 choices each firing)
- With 3 firings per ternary proc, there are 2^3 × 2^3 = 64 possible assignments per cycle
- If ALL 64 create shadows → shadow universality is transition-independent!
"""

from itertools import product as iproduct
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


def build_cycle_configs_incrementing(ms, n, mover_word):
    """Build config sequence with incrementing transitions. Returns configs or None."""
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
    return configs[:ell]


def check_p1_overlap(configs, mover_word):
    """Check P1 (middle binary) overlap."""
    ell = len(mover_word)
    p1_mover = set()
    p1_nonmover = set()
    for i in range(ell):
        v = (configs[i][0], configs[i][1], configs[i][2])
        if mover_word[i] == 1:
            p1_mover.add(v)
        else:
            p1_nonmover.add(v)
    return bool(p1_mover & p1_nonmover)


def check_full_overlap(ms, n, configs, mover_word):
    """Check overlap at ALL processors."""
    ell = len(mover_word)
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
            return True
    return False


def build_cycle_general(ms, n, mover_word, transition_choices):
    """Build cycle with general transition choices for non-binary processors.

    transition_choices: dict mapping (step_index, proc) -> target_value
    for non-binary mover steps.

    Returns (configs, valid) where valid means cycle closes with distinct configs.
    """
    ell = len(mover_word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        if ms[p] == 2:
            # Binary: always flip
            c[p] = 1 - c[p]
        else:
            # Non-binary: use provided choice
            c[p] = transition_choices[(i, p)]
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

    return configs[:ell]


def has_shadow(ms, n, configs, mover_word):
    """Check if determined entries create shadow cycle."""
    ell = len(mover_word)

    # Extract determined entries
    required = {}
    has_conflict = False
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
        if has_conflict:
            break

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

    return 'none'  # no shadow found


def enumerate_transition_choices(ms, n, mover_word):
    """Enumerate all valid transition choices for non-binary mover steps.

    For each non-binary mover step, the processor can transition to any
    value != current value. Returns list of dicts.
    """
    # First, build the incrementing config sequence to know current values
    configs_inc = build_cycle_configs_incrementing(ms, n, mover_word)
    if configs_inc is None:
        return []

    # Find non-binary mover steps and their choices
    ell = len(mover_word)
    nonbin_steps = []
    for i in range(ell):
        p = mover_word[i]
        if ms[p] > 2:
            current_val = configs_inc[i][p]
            choices = [v for v in range(ms[p]) if v != current_val]
            nonbin_steps.append((i, p, current_val, choices))

    # Enumerate all combinations
    if not nonbin_steps:
        return [{}]  # no non-binary steps, only one option (binary flips)

    all_choices = []
    choice_lists = [step_info[3] for step_info in nonbin_steps]

    for combo in iproduct(*choice_lists):
        tc = {}
        for idx, (step_i, proc, _, _) in enumerate(nonbin_steps):
            tc[(step_i, proc)] = combo[idx]
        all_choices.append(tc)

    return all_choices


def main():
    n = 5
    ms = [2, 2, 2, 3, 3]
    print("=" * 70)
    print(f"GENERAL TRANSITION SHADOW TEST: n={n} ms={tuple(ms)}")
    print("=" * 70)
    print("For each P1-free, overlap-free cycle (incrementing):")
    print("  Try ALL non-binary transition assignments")
    print("  Check: does EVERY assignment yield conflict or shadow?")
    print()

    max_len = 3 * n + 6
    words = enumerate_mover_words_smart(ms, n, max_len)

    # First find the P1-free, overlap-free cycles with incrementing
    target_cycles = []
    for word in words:
        configs = build_cycle_configs_incrementing(ms, n, word)
        if configs is None:
            continue
        if check_p1_overlap(configs, word):
            continue
        if check_full_overlap(ms, n, configs, word):
            continue
        target_cycles.append(word)

    print(f"Found {len(target_cycles)} fully overlap-free cycles with incrementing")
    print()

    # For each, enumerate all transition choices
    all_blocked = True
    for cycle_idx, word in enumerate(target_cycles):
        choices = enumerate_transition_choices(ms, n, word)
        n_choices = len(choices)

        results = {'shadow': 0, 'conflict': 0, 'none': 0, 'invalid_cycle': 0}
        clean_examples = []

        for tc in choices:
            # Build cycle with this transition choice
            configs = build_cycle_general(ms, n, word, tc)
            if configs is None:
                results['invalid_cycle'] += 1
                continue

            # Check P1 overlap (same for all transition choices - cube walk unchanged)
            # Actually cube walk IS unchanged since binary procs always flip
            # and the cube is (c_0,c_1,c_2) which are all binary
            # But wait - non-binary transitions change c_3,c_4 which DON'T affect cube
            # So P1 overlap is same → already checked above

            # Check full overlap
            has_ovl = check_full_overlap(ms, n, configs, word)

            # Check shadow/conflict
            result = has_shadow(ms, n, configs, word)
            results[result] += 1

            if result == 'none' and not has_ovl:
                if len(clean_examples) < 3:
                    clean_examples.append((tc, configs))

        clean = results['none']
        status = "★ ALL BLOCKED" if clean == 0 else f"!! {clean} CLEAN !!"
        print(f"Cycle {cycle_idx}: word={word}")
        print(f"  {n_choices} transition choices: "
              f"shadow={results['shadow']} conflict={results['conflict']} "
              f"invalid={results['invalid_cycle']} clean={results['none']} → {status}")

        if clean > 0:
            all_blocked = False
            for tc, configs in clean_examples:
                print(f"  CLEAN example: tc={tc}")
                print(f"    configs: {configs[:4]}...")

    print()
    if all_blocked:
        print("★★ ALL transition choices for ALL overlap-free cycles create obstructions! ★★")
        print("Shadow universality is TRANSITION-INDEPENDENT!")
    else:
        print("!! Some transition choices escape obstructions")

    # Also test P1-free cycles WITH overlap (to see if entry conflicts remain)
    print(f"\n{'='*70}")
    print("P1-FREE CYCLES WITH OVERLAP — general transition test")
    print("="*70)

    overlap_cycles = []
    for word in words:
        configs = build_cycle_configs_incrementing(ms, n, word)
        if configs is None:
            continue
        if check_p1_overlap(configs, word):
            continue
        if not check_full_overlap(ms, n, configs, word):
            continue  # only keep those WITH overlap
        overlap_cycles.append(word)

    print(f"\n{len(overlap_cycles)} P1-free cycles WITH overlap (incrementing)")
    print("Testing first 20...")

    n_tested = 0
    n_all_blocked = 0
    n_some_clean = 0

    for word in overlap_cycles[:20]:
        choices = enumerate_transition_choices(ms, n, word)
        clean = 0
        total_valid = 0
        for tc in choices:
            configs = build_cycle_general(ms, n, word, tc)
            if configs is None:
                continue
            total_valid += 1
            result = has_shadow(ms, n, configs, word)
            has_ovl = check_full_overlap(ms, n, configs, word)
            if result == 'none' and not has_ovl:
                clean += 1
        n_tested += 1
        if clean == 0:
            n_all_blocked += 1
        else:
            n_some_clean += 1
            print(f"  word={word}: {clean}/{total_valid} CLEAN")

    print(f"\n{n_tested} tested: {n_all_blocked} all blocked, {n_some_clean} have clean assignments")
    sys.stdout.flush()


if __name__ == "__main__":
    main()
