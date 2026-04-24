#!/usr/bin/env python3
"""binscc_mover_entry_scc.py — Do MOVER entries alone create bad SCCs?

For overlap-free cycles, test if the shadow comes from mover entries only
(not nonmover entries). If yes, the obstruction is intrinsic to the
mover word and can't be avoided by any transition function choice.

Also: test with ONLY nonmover entries to see if they alone suffice.
This tells us which entries are essential for the shadow.
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


def check_scc_with_entries(ms, n, good_configs, required):
    """Check if the given determined entries create a bad SCC among non-good configs."""
    good_set = set(good_configs)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        config = start
        visited = {}
        for step in range(300):
            if config in good_set:
                break
            if config in visited:
                return True  # shadow/SCC found
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

    return False


def analyze_cycle(ms, n, mover_word):
    """Analyze a cycle and return entry sets + SCC results."""
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

    # P1 overlap
    p1_mover = set()
    p1_nonmover = set()
    for i in range(ell):
        v = (configs_cycle[i][0], configs_cycle[i][1], configs_cycle[i][2])
        if mover_word[i] == 1:
            p1_mover.add(v)
        else:
            p1_nonmover.add(v)
    if p1_mover & p1_nonmover:
        return {'type': 'p1_overlap'}

    # Full overlap
    any_overlap = False
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
        if mover_ctx & nonmover_ctx:
            any_overlap = True
            break

    if any_overlap:
        return {'type': 'has_overlap'}

    # This is a P1-free, overlap-free cycle. Extract entries.
    mover_entries = {}  # entries from mover steps: f(L,S,R) = S'
    nonmover_entries = {}  # entries from nonmover steps: f(L,S,R) = S
    all_entries = {}

    for i in range(ell):
        c = configs_cycle[i]
        c_next = configs_cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]

        # Mover entry
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        mover_entries[key] = S_new
        all_entries[key] = S_new

        # Nonmover entries
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                nonmover_entries[key2] = Sj
                all_entries[key2] = Sj

    # Check SCC with different entry sets
    scc_all = check_scc_with_entries(ms, n, configs_cycle, all_entries)
    scc_mover = check_scc_with_entries(ms, n, configs_cycle, mover_entries)
    scc_nonmover = check_scc_with_entries(ms, n, configs_cycle, nonmover_entries)

    # Also check mover entries for binary procs only
    binary_mover = {k: v for k, v in mover_entries.items() if ms[k[0]] == 2}
    scc_binary_mover = check_scc_with_entries(ms, n, configs_cycle, binary_mover)

    # And mover entries for non-binary procs only
    nonbin_mover = {k: v for k, v in mover_entries.items() if ms[k[0]] > 2}
    scc_nonbin_mover = check_scc_with_entries(ms, n, configs_cycle, nonbin_mover)

    return {
        'type': 'overlap_free',
        'mover_entries': len(mover_entries),
        'nonmover_entries': len(nonmover_entries),
        'all_entries': len(all_entries),
        'scc_all': scc_all,
        'scc_mover': scc_mover,
        'scc_nonmover': scc_nonmover,
        'scc_binary_mover': scc_binary_mover,
        'scc_nonbin_mover': scc_nonbin_mover,
    }


def main():
    for n, ms, label in [
        (5, [2, 2, 2, 3, 3], "n=5 prod=72"),
        (7, [2, 2, 2, 3, 3, 3, 3], "n=7 prod=648"),
    ]:
        print(f"\n{'='*70}")
        print(f"MOVER-ENTRY SCC ANALYSIS: {label}")
        print(f"{'='*70}")

        max_len = 3 * n + 6
        t0 = time.time()
        words = enumerate_mover_words_smart(ms, n, max_len)
        print(f"Enumerated {len(words)} words in {time.time()-t0:.1f}s")

        overlap_free = []
        for word in words:
            result = analyze_cycle(ms, n, word)
            if result is None:
                continue
            if result['type'] == 'overlap_free':
                overlap_free.append((word, result))

        print(f"\n{len(overlap_free)} overlap-free, P1-free cycles")

        # Statistics
        scc_all = sum(1 for _, r in overlap_free if r['scc_all'])
        scc_mover = sum(1 for _, r in overlap_free if r['scc_mover'])
        scc_nonmover = sum(1 for _, r in overlap_free if r['scc_nonmover'])
        scc_binary = sum(1 for _, r in overlap_free if r['scc_binary_mover'])
        scc_nonbin = sum(1 for _, r in overlap_free if r['scc_nonbin_mover'])

        print(f"\nSCC creation by entry set:")
        print(f"  All entries:          {scc_all}/{len(overlap_free)} ({100*scc_all/len(overlap_free) if overlap_free else 0:.0f}%)")
        print(f"  Mover entries only:   {scc_mover}/{len(overlap_free)} ({100*scc_mover/len(overlap_free) if overlap_free else 0:.0f}%)")
        print(f"  Nonmover entries only: {scc_nonmover}/{len(overlap_free)} ({100*scc_nonmover/len(overlap_free) if overlap_free else 0:.0f}%)")
        print(f"  Binary mover only:    {scc_binary}/{len(overlap_free)} ({100*scc_binary/len(overlap_free) if overlap_free else 0:.0f}%)")
        print(f"  Non-binary mover only: {scc_nonbin}/{len(overlap_free)} ({100*scc_nonbin/len(overlap_free) if overlap_free else 0:.0f}%)")

        if scc_mover == len(overlap_free):
            print(f"\n  ★ MOVER ENTRIES ALONE always create SCC!")
            print(f"  → Obstruction is intrinsic to mover word, transition-independent!")
        elif scc_binary == len(overlap_free):
            print(f"\n  ★ BINARY MOVER ENTRIES alone always create SCC!")

        # Entry counts
        if overlap_free:
            total_entries = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
            avg_mover = sum(r['mover_entries'] for _, r in overlap_free) / len(overlap_free)
            avg_nonmover = sum(r['nonmover_entries'] for _, r in overlap_free) / len(overlap_free)
            avg_all = sum(r['all_entries'] for _, r in overlap_free) / len(overlap_free)
            print(f"\n  Entry counts (avg over {len(overlap_free)} cycles):")
            print(f"    Mover entries: {avg_mover:.0f}")
            print(f"    Nonmover entries: {avg_nonmover:.0f}")
            print(f"    All entries: {avg_all:.0f} / {total_entries} total ({100*avg_all/total_entries:.0f}%)")

        # Show details for first few
        for word, r in overlap_free[:3]:
            print(f"\n  Word: {word}")
            print(f"    Mover: {r['mover_entries']}, Nonmover: {r['nonmover_entries']}, "
                  f"All: {r['all_entries']}")
            print(f"    SCC: all={r['scc_all']}, mover={r['scc_mover']}, "
                  f"nonmover={r['scc_nonmover']}, binary={r['scc_binary_mover']}, "
                  f"nonbin={r['scc_nonbin_mover']}")

        sys.stdout.flush()

    print(f"\n{'='*70}")
    print("INTERPRETATION")
    print("="*70)
    print("""
If mover entries alone create SCC:
  → The shadow is forced by the mover word structure
  → No transition function can avoid it
  → Combined with P1 overlap (transition-independent) and
    overlap→conflict (inevitable for incrementing):
    ALL sub-threshold cycles with 3 consec binary are blocked

If only all entries (mover + nonmover) create SCC:
  → Non-incrementing transitions might avoid the shadow
  → Need to check: does the mover word admit any valid
    non-incrementing config sequence that avoids shadow?
""")


if __name__ == "__main__":
    main()
