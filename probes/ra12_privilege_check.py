#!/usr/bin/env python3
"""
RA12: Privilege check for sweep good cycles with non-consecutive binary.

Claim: For sweep good cycle with non-consecutive binary, isolated firings,
n >= 9, sub-threshold, >=3 binary: every config c not in gc.configs has
at least one privileged processor.

Test at n=9 ms=[2,3,3,2,3,3,2,3,3] and n=7 with appropriate multisets.

For each sweep word x state-sequence combo:
1. Build forced transition entries from the good cycle
2. Fill free entries with "stay" (most conservative)
3. Enumerate ALL configs, check privilege for non-good configs
4. Also test random completions
"""

from itertools import product as iproduct
import random
import sys


def enumerate_sweep_words(n):
    """Generate all sweep words (CW and CCW) of length 2n."""
    words = []
    # CW sweep: 0,1,2,...,n-1,n-2,...,1 (then repeat)
    # A sweep visits each proc exactly twice
    # CW: 0,1,2,...,n-1, n-2,n-3,...,1, 0 but that's wrong
    # Actually a sweep word of length 2n visits each proc exactly 2 times
    # CW sweep: 0,1,2,...,n-1,0,1,...,n-1 (pure CW) — no, that's fc=2 each
    # Wait: a sweep is when all moves go in one direction
    # CW: positions 0,1,2,...,n-1,0,1,...,n-1 (go around twice)
    cw = list(range(n)) + list(range(n))  # Each proc fires exactly 2 times
    # But that's not right either. Let me think about what "sweep" means.
    # A sweep word has all direction increments the same.
    # For length 2n with fc=2 each: CW sweep = [0,1,2,...,n-1,0,1,...,n-1]
    # CCW sweep = [0,n-1,n-2,...,1,0,n-1,...,1]

    # Actually from the code above, is_sweep checks:
    # dirs = [(word[(i+1)%L] - word[i]) % n for i in range(L)]
    # all(d==1) or all(d==n-1)
    # For CW: each step goes +1 mod n, so word = [0,1,2,...,n-1,0,1,...,n-1]
    # For CCW: each step goes -1 mod n, so word = [0,n-1,n-2,...,1,0,n-1,...,1]

    cw_word = [(i % n) for i in range(2 * n)]
    ccw_word = [((-i) % n) for i in range(2 * n)]

    # All rotations give different sweep words
    cw_words = set()
    ccw_words = set()
    for r in range(2 * n):
        cw_rot = tuple(cw_word[(r + i) % (2 * n)] for i in range(2 * n))
        ccw_rot = tuple(ccw_word[(r + i) % (2 * n)] for i in range(2 * n))
        cw_words.add(cw_rot)
        ccw_words.add(ccw_rot)

    # But many rotations are the same word. For a CW sweep [0,1,...,n-1,0,1,...,n-1],
    # rotation by k gives [k,k+1,...,k-1,k,k+1,...,k-1] which has n distinct rotations
    # (period n). Similarly for CCW.
    # But we also need to consider different starting positions.
    # Actually for our purposes, different rotations give different good cycles
    # (different starting config). But the forced entries might differ.
    # For thoroughness, let's keep all distinct rotations.

    # Actually, the claim is about "8 sweep words". Let me think:
    # For n=9, CW has period n=9 (9 distinct rotations out of 18),
    # CCW has period n=9 (9 distinct rotations out of 18).
    # But the problem says "8 sweep words". Maybe it means starting at each
    # of the n positions for both directions? But n=9 gives 18...
    # Let me just use all distinct CW and CCW rotations.
    # Actually wait — maybe "8 sweep words" refers to n=9 with 8 = 2^3
    # state-sequence combinations? No, the claim says "8 sweep words × 64 combos".
    #
    # Hmm, maybe "sweep words" here means different orderings consistent with
    # non-consecutive binary placement? Let me just enumerate all sweep words
    # and test them all.

    all_words = list(cw_words | ccw_words)
    return all_words


def enumerate_state_sequences(m, k):
    """All sequences of length k+1 starting and ending at 0,
    with consecutive values different, all values in range(m)."""
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_good_cycle(word, n, ms, combo):
    """Build the good cycle configs from word + state sequences.
    combo[p] is the state sequence for proc p.
    Returns list of L configs (the good cycle), or None if invalid."""
    L = len(word)
    fc = [0] * n

    # Build configs step by step
    configs = [tuple(combo[p][0] for p in range(n))]
    for t in range(L):
        fc[word[t]] += 1
        configs.append(tuple(combo[p][fc[p]] for p in range(n)))

    # Check cycle closure
    if configs[-1] != configs[0]:
        return None
    # Check distinctness
    good = configs[:L]
    if len(set(good)) != L:
        return None
    return good


def extract_forced_entries(word, n, ms, good):
    """Extract forced transition entries from a good cycle.
    Returns dict: (proc, L, S, R) -> new_value for mover entries,
    and set of (proc, L, S, R) that must stay (non-mover entries)."""
    L = len(word)
    forced = {}  # (proc, L_val, S_val, R_val) -> new_S
    stay = set()  # (proc, L_val, S_val, R_val) that must map to S

    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        mover = word[t]

        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            key = (j, c[Lp], c[j], c[Rp])

            if j == mover:
                forced[key] = cn[j]
            else:
                stay.add(key)

    return forced, stay


def build_transition_tables(n, ms, forced, stay_set, mode='stay'):
    """Build complete transition tables.
    mode='stay': free entries map to S (identity/stay)
    mode='random': free entries map to random value != S (maximizes privilege)
    Returns list of dicts: tables[proc][(L,S,R)] -> new_S
    """
    tables = [{} for _ in range(n)]

    # First fill forced entries
    for (proc, L, S, R), new_S in forced.items():
        tables[proc][(L, S, R)] = new_S

    # Fill stay entries (non-mover: must stay)
    for (proc, L, S, R) in stay_set:
        key = (L, S, R)
        if key in tables[proc]:
            # Already set by forced — check consistency
            if tables[proc][key] != S:
                pass  # This is the entry conflict case; mover wins
        else:
            tables[proc][key] = S

    # Fill remaining free entries
    for proc in range(n):
        m = ms[proc]
        for L_val in range(ms[(proc - 1) % n]):
            for S_val in range(m):
                for R_val in range(ms[(proc + 1) % n]):
                    key = (L_val, S_val, R_val)
                    if key not in tables[proc]:
                        if mode == 'stay':
                            tables[proc][key] = S_val
                        elif mode == 'random':
                            # Random different value (creates privilege)
                            choices = [v for v in range(m) if v != S_val]
                            if choices:
                                tables[proc][key] = random.choice(choices)
                            else:
                                tables[proc][key] = S_val
                        elif mode == 'random_mixed':
                            # 50% stay, 50% change
                            if random.random() < 0.5:
                                tables[proc][key] = S_val
                            else:
                                choices = [v for v in range(m) if v != S_val]
                                if choices:
                                    tables[proc][key] = random.choice(choices)
                                else:
                                    tables[proc][key] = S_val

    return tables


def count_privileged(config, tables, n, ms):
    """Count number of privileged processors in config."""
    count = 0
    for j in range(n):
        L_val = config[(j - 1) % n]
        S_val = config[j]
        R_val = config[(j + 1) % n]
        new_S = tables[j][(L_val, S_val, R_val)]
        if new_S != S_val:
            count += 1
    return count


def check_privilege_for_cycle(word, n, ms, good, mode='stay'):
    """Check if all non-good configs have at least one privileged proc."""
    forced, stay_set = extract_forced_entries(word, n, ms, good)
    tables = build_transition_tables(n, ms, forced, stay_set, mode=mode)

    good_set = set(good)
    total_configs = 1
    for m in ms:
        total_configs *= m

    dead_configs = []
    non_good_count = 0

    for config in iproduct(*(range(m) for m in ms)):
        if config in good_set:
            continue
        non_good_count += 1
        priv = count_privileged(config, tables, n, ms)
        if priv == 0:
            dead_configs.append(config)

    return non_good_count, dead_configs


def run_test(n, ms, label):
    """Run the full test for given n and ms."""
    print(f"\n{'='*70}")
    print(f"Testing {label}: n={n}, ms={ms}")
    print(f"Total configs = {eval('*'.join(str(m) for m in ms))}")
    print(f"{'='*70}")

    # Check non-consecutive binary
    binary_pos = [i for i in range(n) if ms[i] == 2]
    print(f"Binary positions: {binary_pos}")
    for i in range(len(binary_pos)):
        for j in range(i+1, len(binary_pos)):
            if abs(binary_pos[i] - binary_pos[j]) == 1 or \
               abs(binary_pos[i] - binary_pos[j]) == n - 1:
                print(f"  WARNING: binary at {binary_pos[i]} and {binary_pos[j]} are adjacent!")

    sweep_words = enumerate_sweep_words(n)
    print(f"Number of distinct sweep words: {len(sweep_words)}")

    # State sequences per proc
    total_combos_per_word = 1
    for p in range(n):
        seqs = enumerate_state_sequences(ms[p], 2)  # fc=2 for sweep
        print(f"  Proc {p} (m={ms[p]}): {len(seqs)} state sequences")
        total_combos_per_word *= len(seqs)
    print(f"Total combos per word: {total_combos_per_word}")

    # Test all sweep words × combos with "stay" completion
    total_instances = 0
    total_valid = 0
    total_dead_any = 0
    worst_dead = 0
    worst_dead_configs = []
    worst_info = None

    all_proc_seqs = [enumerate_state_sequences(ms[p], 2) for p in range(n)]

    for wi, word in enumerate(sweep_words):
        for combo in iproduct(*all_proc_seqs):
            total_instances += 1
            good = build_good_cycle(list(word), n, ms, combo)
            if good is None:
                continue
            total_valid += 1

            non_good, dead = check_privilege_for_cycle(list(word), n, ms, good, mode='stay')

            if dead:
                total_dead_any += 1
                if len(dead) > worst_dead:
                    worst_dead = len(dead)
                    worst_dead_configs = dead[:5]
                    worst_info = (word, combo, non_good, len(dead))

        if (wi + 1) % 2 == 0:
            print(f"  Processed {wi+1}/{len(sweep_words)} words, "
                  f"{total_valid} valid cycles so far, "
                  f"{total_dead_any} with dead configs")

    print(f"\n--- STAY COMPLETION RESULTS ---")
    print(f"Total instances: {total_instances}")
    print(f"Valid good cycles: {total_valid}")
    print(f"Cycles with dead (0-privilege) configs: {total_dead_any}")
    print(f"Worst case: {worst_dead} dead configs")

    if worst_dead_configs:
        print(f"\nSample dead configs:")
        for dc in worst_dead_configs[:5]:
            print(f"  {dc}")
        if worst_info:
            print(f"  From word={worst_info[0][:6]}..., "
                  f"non-good={worst_info[2]}, dead={worst_info[3]}")

    # Now test with random completions (10 trials per valid cycle, sample)
    print(f"\n--- RANDOM COMPLETION TEST (sampling) ---")
    random.seed(42)
    random_dead_any = 0
    random_trials = 0

    # Sample up to 200 valid cycles
    sample_words = sweep_words[:4]  # Use fewer words for random test
    for word in sample_words:
        for combo in iproduct(*all_proc_seqs):
            good = build_good_cycle(list(word), n, ms, combo)
            if good is None:
                continue

            for trial in range(10):
                random_trials += 1
                non_good, dead = check_privilege_for_cycle(
                    list(word), n, ms, good, mode='random_mixed')
                if dead:
                    random_dead_any += 1

    print(f"Random trials: {random_trials}")
    print(f"Trials with dead configs: {random_dead_any}")

    return total_dead_any == 0


def main():
    print("RA12: Privilege Check for Sweep + Non-Consecutive Binary")
    print("=" * 70)

    # n=7 test first (smaller, faster)
    # Non-consecutive binary in a ring of 7: e.g., positions 0,2,4
    n7_ms = [2, 3, 2, 3, 2, 3, 3]
    result_n7 = run_test(7, n7_ms, "n=7 non-consecutive binary")

    # n=9 main test
    n9_ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    result_n9 = run_test(9, n9_ms, "n=9 stuttered sweep")

    print(f"\n{'='*70}")
    print(f"FINAL VERDICT")
    print(f"{'='*70}")
    print(f"n=7: {'TRUE (no dead configs)' if result_n7 else 'FALSE (dead configs exist)'}")
    print(f"n=9: {'TRUE (no dead configs)' if result_n9 else 'FALSE (dead configs exist)'}")

    if result_n7 and result_n9:
        print("\nCLAIM: TRUE for sweep context with non-consecutive binary")
    else:
        print("\nCLAIM: FALSE — dead fixed points exist even in sweep context")


if __name__ == '__main__':
    main()
