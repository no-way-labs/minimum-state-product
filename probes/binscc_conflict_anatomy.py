#!/usr/bin/env python3
"""binscc_conflict_anatomy.py — WHY does overlap → conflict?

For P1-free cycles WITH overlap: does the overlap itself cause the conflict?
I.e., is the conflicting entry always at an overlapping context?

Also: analyze the structure of shadow-blocked cycles.
What entries cause the shadow? Are they always at specific positions?
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
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


def detailed_analysis(ms, n, mover_word):
    """Detailed conflict/shadow analysis."""
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

    # Per-proc overlap
    overlap_procs = []
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
            overlap_procs.append(p)

    # Entry analysis
    required = {}
    conflict_entry = None
    for i in range(ell):
        c = configs_cycle[i]
        c_next = configs_cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            conflict_entry = (key, required[key], S_new, 'mover')
            break
        required[key] = S_new
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in required and required[key2] != Sj:
                    conflict_entry = (key2, required[key2], Sj, 'nonmover')
                    break
                required[key2] = Sj
        if conflict_entry:
            break

    if conflict_entry:
        entry_key, val1, val2, source = conflict_entry
        proc = entry_key[0]
        # Is this proc in the overlap set?
        overlap_related = proc in overlap_procs

        return {
            'type': 'conflict',
            'overlap_procs': overlap_procs,
            'conflict_proc': proc,
            'conflict_key': entry_key,
            'conflict_vals': (val1, val2),
            'conflict_source': source,
            'overlap_related': overlap_related,
        }

    # Shadow analysis
    good_set = set(configs_cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    shadow_cycle = None
    for start in non_good:
        config = start
        visited = {}
        path = []
        for step in range(300):
            if config in good_set:
                break
            if config in visited:
                # Found shadow cycle
                cycle_start = visited[config]
                shadow_cycle = path[cycle_start:]
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
        if shadow_cycle:
            break

    if shadow_cycle:
        # Analyze which entries drive the shadow
        shadow_movers = []
        for i in range(len(shadow_cycle)):
            c = shadow_cycle[i]
            c_next = shadow_cycle[(i+1) % len(shadow_cycle)]
            for j in range(n):
                if c[j] != c_next[j]:
                    shadow_movers.append(j)
                    break

        return {
            'type': 'shadow',
            'overlap_procs': overlap_procs,
            'shadow_len': len(shadow_cycle),
            'shadow_movers': shadow_movers,
            'det_entries': len(required),
            'total_entries': sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n)),
        }

    return {
        'type': 'clean',
        'overlap_procs': overlap_procs,
        'det_entries': len(required),
        'total_entries': sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n)),
    }


def main():
    for n, ms, label in [
        (5, [2, 2, 2, 3, 3], "n=5 prod=72"),
        (7, [2, 2, 2, 3, 3, 3, 3], "n=7 prod=648"),
    ]:
        print(f"\n{'='*70}")
        print(f"CONFLICT/SHADOW ANATOMY: {label}")
        print(f"{'='*70}")

        max_len = 3 * n + 6
        words = enumerate_mover_words_smart(ms, n, max_len)

        # Conflict analysis for overlap cycles
        conflict_at_overlap_proc = 0
        conflict_not_at_overlap_proc = 0
        conflict_source_dist = Counter()
        conflict_proc_dist = Counter()

        # Shadow analysis
        shadow_len_dist = Counter()
        shadow_mover_dist = Counter()
        shadow_det_pct = []

        type_dist = Counter()
        total_valid = 0

        for word in words:
            result = detailed_analysis(ms, n, word)
            if result is None:
                continue
            total_valid += 1
            type_dist[result['type']] += 1

            if result['type'] == 'conflict':
                if result['overlap_related']:
                    conflict_at_overlap_proc += 1
                else:
                    conflict_not_at_overlap_proc += 1
                conflict_source_dist[result['conflict_source']] += 1
                conflict_proc_dist[result['conflict_proc']] += 1

            elif result['type'] == 'shadow':
                shadow_len_dist[result['shadow_len']] += 1
                for m in result['shadow_movers']:
                    shadow_mover_dist[m] += 1
                shadow_det_pct.append(100 * result['det_entries'] / result['total_entries'])

        print(f"\n{total_valid} valid cycles")
        print(f"Type distribution: {dict(type_dist)}")

        if conflict_at_overlap_proc + conflict_not_at_overlap_proc > 0:
            print(f"\nCONFLICT ANATOMY:")
            print(f"  Conflict at overlapping processor: {conflict_at_overlap_proc}")
            print(f"  Conflict NOT at overlapping proc: {conflict_not_at_overlap_proc}")
            print(f"  Conflict source: {dict(conflict_source_dist)}")
            print(f"  Conflict processor: {dict(conflict_proc_dist)}")

            # Key question: is the conflict ALWAYS due to overlap?
            # I.e., is the conflicting entry always at a proc with overlap?
            if conflict_not_at_overlap_proc == 0:
                print(f"  → Conflict is ALWAYS at an overlapping processor!")
            else:
                pct = 100 * conflict_at_overlap_proc / (conflict_at_overlap_proc + conflict_not_at_overlap_proc)
                print(f"  → {pct:.1f}% of conflicts at overlapping proc")

        if shadow_len_dist:
            print(f"\nSHADOW ANATOMY:")
            print(f"  Shadow lengths: {dict(shadow_len_dist)}")
            print(f"  Shadow movers: {dict(shadow_mover_dist)}")
            if shadow_det_pct:
                print(f"  Determined entries: {min(shadow_det_pct):.0f}%-{max(shadow_det_pct):.0f}% "
                      f"(mean {sum(shadow_det_pct)/len(shadow_det_pct):.0f}%)")

        sys.stdout.flush()


if __name__ == "__main__":
    main()
