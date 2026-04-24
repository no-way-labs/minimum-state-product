#!/usr/bin/env python3
"""
RA12 v2: Refined privilege check.

The "stay" completion trivially creates dead fixed points (every config where
all procs see a free entry is dead). The real question is:

1. Can we find ANY completion of free entries that has no dead configs (liveness)?
2. Among forced entries only, do any configs have ALL contexts forced to stay?

Key insight: a config c has 0 privilege iff for ALL procs j,
  tables[j](c[j-1], c[j], c[j+1]) = c[j].
With forced entries, some (L,S,R) tuples are forced to change (mover entries
where new_S != S). If a config hits ANY such forced entry, it has privilege
regardless of how we complete free entries.

So the "worst case" dead configs are those where EVERY proc's context
either: (a) is a forced stay (non-mover entry), or (b) is a free entry.
For these, the "stay" completion makes them dead, and any other completion
can rescue them.

The claim should really be: "for any completion, all non-good configs have
privilege" — which requires that every non-good config hits at least one
forced mover entry where new_S != S.

Let's check THAT.
"""

from itertools import product as iproduct
import sys


def enumerate_state_sequences(m, k):
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
    L = len(word)
    fc = [0] * n
    configs = [tuple(combo[p][0] for p in range(n))]
    for t in range(L):
        fc[word[t]] += 1
        configs.append(tuple(combo[p][fc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None
    good = configs[:L]
    if len(set(good)) != L:
        return None
    return good


def check_forced_privilege(word, n, ms, good):
    """Check: for every non-good config, does it hit at least one
    forced mover entry where new_S != S?

    If yes: that config has privilege regardless of completion.
    If no: a "stay" completion makes it dead.

    Returns (non_good_count, forced_dead_count, sample_dead)
    """
    L = len(word)
    good_set = set(good)

    # Collect forced mover entries where value changes
    # These are (proc, L, S, R) -> new_S where new_S != S
    forced_change = {}  # (proc, L, S, R) -> new_S (where new_S != S)
    forced_stay_mover = set()  # mover entries where new_S == S (shouldn't happen in sweep)

    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        mover = word[t]

        # Mover entry
        Lp = (mover - 1) % n
        Rp = (mover + 1) % n
        key = (mover, c[Lp], c[mover], c[Rp])
        new_S = cn[mover]
        if new_S != c[mover]:
            forced_change[key] = new_S
        else:
            forced_stay_mover.add(key)

    # For each non-good config, check if it hits any forced_change entry
    non_good = 0
    forced_dead = 0
    sample_dead = []

    for config in iproduct(*(range(m) for m in ms)):
        if config in good_set:
            continue
        non_good += 1

        has_forced_privilege = False
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            key = (j, config[Lp], config[j], config[Rp])
            if key in forced_change:
                has_forced_privilege = True
                break

        if not has_forced_privilege:
            forced_dead += 1
            if len(sample_dead) < 5:
                sample_dead.append(config)

    return non_good, forced_dead, sample_dead


def run_test(n, ms, label):
    print(f"\n{'='*70}")
    print(f"Testing {label}: n={n}, ms={ms}")
    product = 1
    for m in ms:
        product *= m
    print(f"Total configs = {product}, Good cycle length = {2*n}")
    print(f"{'='*70}")

    binary_pos = [i for i in range(n) if ms[i] == 2]
    print(f"Binary positions: {binary_pos}")

    # Enumerate sweep words
    cw_word = [(i % n) for i in range(2 * n)]
    ccw_word = [((-i) % n) for i in range(2 * n)]
    sweep_words = set()
    for r in range(2 * n):
        sweep_words.add(tuple(cw_word[(r + i) % (2 * n)] for i in range(2 * n)))
        sweep_words.add(tuple(ccw_word[(r + i) % (2 * n)] for i in range(2 * n)))
    sweep_words = list(sweep_words)
    print(f"Distinct sweep words: {len(sweep_words)}")

    all_proc_seqs = [enumerate_state_sequences(ms[p], 2) for p in range(n)]
    total_combos = 1
    for seqs in all_proc_seqs:
        total_combos *= len(seqs)
    print(f"State-sequence combos per word: {total_combos}")

    total_valid = 0
    total_with_forced_dead = 0
    min_forced_dead = float('inf')
    max_forced_dead = 0
    worst_sample = []
    best_info = None

    # Count forced_change entries per instance
    forced_change_counts = []

    for wi, word in enumerate(sweep_words):
        for combo in iproduct(*all_proc_seqs):
            good = build_good_cycle(list(word), n, ms, combo)
            if good is None:
                continue
            total_valid += 1

            non_good, forced_dead, sample = check_forced_privilege(
                list(word), n, ms, good)

            if forced_dead > 0:
                total_with_forced_dead += 1

            if forced_dead > max_forced_dead:
                max_forced_dead = forced_dead
                worst_sample = sample

            if forced_dead < min_forced_dead:
                min_forced_dead = forced_dead
                best_info = (word, combo, non_good, forced_dead)

    print(f"\n--- RESULTS ---")
    print(f"Valid good cycles: {total_valid}")
    print(f"Cycles with forced-dead configs: {total_with_forced_dead} / {total_valid}")
    print(f"Min forced-dead configs across all cycles: {min_forced_dead}")
    print(f"Max forced-dead configs across all cycles: {max_forced_dead}")

    if worst_sample:
        print(f"\nSample worst-case dead configs:")
        for dc in worst_sample:
            print(f"  {dc}")

    if best_info:
        print(f"\nBest cycle (fewest forced-dead):")
        print(f"  Word: {best_info[0][:8]}...")
        print(f"  Non-good: {best_info[2]}, Forced-dead: {best_info[3]}")

    # Analysis: how many forced-change entries does a typical sweep cycle have?
    print(f"\n--- FORCED ENTRY ANALYSIS ---")
    word = sweep_words[0]
    combo = list(iproduct(*all_proc_seqs))[0]
    good = build_good_cycle(list(word), n, ms, combo)
    if good:
        L = len(word)
        forced_change = set()
        all_contexts = set()
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            mover = word[t]
            Lp = (mover - 1) % n
            Rp = (mover + 1) % n
            key = (mover, c[Lp], c[mover], c[Rp])
            new_S = cn[mover]
            if new_S != c[mover]:
                forced_change.add(key)

        # Total possible contexts
        total_contexts = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
        print(f"Forced-change entries in sample cycle: {len(forced_change)}")
        print(f"Total possible context entries: {total_contexts}")
        print(f"Coverage: {len(forced_change)/total_contexts*100:.1f}%")

        # How many configs are ALL-free (no proc hits any forced entry)?
        # This is the set of configs where every proc sees a free context.
        # These are exactly the "forced-dead" configs.

    return total_with_forced_dead == 0


def main():
    print("RA12 v2: Forced Privilege Check")
    print("(Can 'stay' completion create dead configs?)")
    print("=" * 70)

    # n=5 (fast sanity check)
    print("\n>>> n=5 <<<")
    run_test(5, [2, 3, 2, 3, 2], "n=5 non-consec binary")

    # n=7
    print("\n>>> n=7 <<<")
    run_test(7, [2, 3, 2, 3, 2, 3, 3], "n=7 non-consec binary")

    # n=9
    print("\n>>> n=9 <<<")
    run_test(9, [2, 3, 3, 2, 3, 3, 2, 3, 3], "n=9 stuttered sweep")

    print(f"\n{'='*70}")
    print("INTERPRETATION:")
    print("If forced-dead > 0: a 'stay' completion creates dead fixed points.")
    print("The CLAIM is FALSE: not every non-good config is forced-privileged.")
    print("However, a smarter completion CAN rescue these configs.")
    print("The claim needs the completion to be part of a valid system,")
    print("not arbitrary.")


if __name__ == '__main__':
    main()
