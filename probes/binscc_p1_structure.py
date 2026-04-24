#!/usr/bin/env python3
"""binscc_p1_structure.py — Structural analysis of P1-overlap-free cycles.

At n=5, 234 cycles survive P1 overlap. What's their structure?
Key: P1 mover vertices are always "complementary" pairs.
Can we prove that at n >= 6, the ring constraints force P1 overlap?
"""

from collections import Counter
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


def analyze_p1_free_cycles(ms, n, mover_word, bp0=0, bp1=1, bp2=2):
    """Detailed analysis of a cycle's P1 structure."""
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

    # Cube walk
    cube_walk = [(configs[i][bp0], configs[i][bp1], configs[i][bp2]) for i in range(ell)]

    # P1 mover/nonmover
    p1_mover_v = set()
    p1_nonmover_v = set()
    p1_mover_steps = []
    p1_nonmover_steps = []
    stay_steps = []

    for i in range(ell):
        v = cube_walk[i]
        if mover_word[i] == bp1:
            p1_mover_v.add(v)
            p1_mover_steps.append(i)
        else:
            p1_nonmover_v.add(v)
            p1_nonmover_steps.append(i)
            if mover_word[i] not in (bp0, bp1, bp2):
                stay_steps.append(i)

    has_p1_overlap = bool(p1_mover_v & p1_nonmover_v)

    # Analyze transition pattern around P1 firings
    # After P1 fires at step i, what happens next?
    p1_after = []
    for i in p1_mover_steps:
        next_mover = mover_word[(i+1) % ell]
        p1_after.append(next_mover)

    # Before P1 fires, what happened?
    p1_before = []
    for i in p1_mover_steps:
        prev_mover = mover_word[(i-1) % ell]
        p1_before.append(prev_mover)

    # "Entry" pattern: how does the walk enter the non-binary region?
    # Track: last binary step before a non-binary block, first binary step after
    nonbin_entries = []  # (entry_vertex, exit_vertex, length)
    in_nonbin = False
    entry_step = None
    for i in range(2 * ell):  # wrap around
        idx = i % ell
        if mover_word[idx] in (bp0, bp1, bp2):
            if in_nonbin:
                exit_v = cube_walk[idx]
                nonbin_entries.append((cube_walk[entry_step], exit_v, idx - entry_step))
                in_nonbin = False
        else:
            if not in_nonbin:
                entry_step = idx
                in_nonbin = True

    return {
        'has_p1_overlap': has_p1_overlap,
        'p1_mover_v': p1_mover_v,
        'p1_nonmover_v': p1_nonmover_v,
        'p1_fires': fire_counts[bp1],
        'stay_steps': len(stay_steps),
        'stay_vertices': set(cube_walk[i] for i in stay_steps),
        'cube_vertices': set(cube_walk),
        'p1_after': p1_after,
        'p1_before': p1_before,
        'nonbin_entries': nonbin_entries[:10],  # limit
    }


def main():
    print("=" * 70)
    print("STRUCTURE OF P1-OVERLAP-FREE CYCLES")
    print("=" * 70)

    # n=5 sub-threshold
    n = 5
    ms = [2, 2, 2, 3, 3]
    max_len = 3 * n + 6
    words = enumerate_mover_words_smart(ms, n, max_len)

    p1_free = []
    mover_vertex_patterns = Counter()

    for word in words:
        result = analyze_p1_free_cycles(ms, n, word)
        if result is None:
            continue
        if result['has_p1_overlap']:
            continue
        p1_free.append((word, result))
        key = tuple(sorted(result['p1_mover_v']))
        mover_vertex_patterns[key] += 1

    print(f"\nn=5, ms=(2,2,2,3,3): {len(p1_free)} P1-overlap-free cycles")
    print(f"\nP1 mover vertex patterns:")
    for pattern, count in mover_vertex_patterns.most_common():
        print(f"  {pattern}: {count} cycles")

    # Detailed analysis of each pattern
    print(f"\nDetailed analysis by P1 mover vertex pattern:")
    for pattern in sorted(mover_vertex_patterns.keys()):
        cycles = [(w, r) for w, r in p1_free
                  if tuple(sorted(r['p1_mover_v'])) == pattern]
        print(f"\n  P1 mover = {pattern} ({len(cycles)} cycles):")

        # Check properties of these cycles
        p1_fires_dist = Counter(r['p1_fires'] for _, r in cycles)
        stay_dist = Counter(r['stay_steps'] for _, r in cycles)
        cube_sizes = Counter(len(r['cube_vertices']) for _, r in cycles)

        print(f"    P1 fire counts: {dict(p1_fires_dist)}")
        print(f"    Non-binary stay counts: {dict(stay_dist)}")
        print(f"    Cube vertex counts: {dict(cube_sizes)}")

        # After P1 fires, where does walk go?
        after_dist = Counter()
        before_dist = Counter()
        for _, r in cycles:
            for a in r['p1_after']:
                after_dist[a] += 1
            for b in r['p1_before']:
                before_dist[b] += 1
        print(f"    After P1 fires, next mover: {dict(after_dist)}")
        print(f"    Before P1 fires, prev mover: {dict(before_dist)}")

        # Stay vertices vs P1 mover vertices
        stay_v_dist = Counter()
        for _, r in cycles:
            for v in r['stay_vertices']:
                stay_v_dist[v] += 1
        print(f"    Stay vertices: {dict(stay_v_dist)}")
        # Check: which vertices are NEVER stay?
        all_cube = set()
        for _, r in cycles:
            all_cube.update(r['cube_vertices'])
        never_stay = all_cube - set(stay_v_dist.keys())
        print(f"    Never-stay vertices: {sorted(never_stay)}")

        # Show examples
        for word, r in cycles[:2]:
            print(f"    Example: {word}")
            print(f"      cube={sorted(r['cube_vertices'])}, "
                  f"stay_v={sorted(r['stay_vertices'])}")

    # KEY QUESTION: why does n=6 kill all?
    print(f"\n{'='*70}")
    print("WHY n=6 KILLS ALL: stay step counting")
    print("="*70)

    for n_test in [5, 6]:
        ms_test = [2, 2, 2] + [3] * (n_test - 3)
        max_len_t = 3 * n_test + 6
        words_t = enumerate_mover_words_smart(ms_test, n_test, max_len_t)

        min_stays = float('inf')
        max_stays = 0
        all_valid = 0

        for word in words_t:
            result = analyze_p1_free_cycles(ms_test, n_test, word)
            if result is None:
                continue
            all_valid += 1
            stays = result['stay_steps']
            min_stays = min(min_stays, stays)
            max_stays = max(max_stays, stays)

        print(f"\n  n={n_test}: {all_valid} valid cycles")
        print(f"    Stay steps range: [{min_stays}, {max_stays}]")
        print(f"    With P1 firing ≥2 times at ≤k vertices,")
        print(f"    {min_stays}+ stays must fit in ≤6 non-P1-mover vertices")

    # CONJECTURE: for n >= 6, min_stays >= 6 forces P1 overlap
    # because 6+ stays in 6 vertices means at least one vertex
    # gets a stay AND is a P1-mover... unless stays perfectly avoid

    # Actually the argument needs: every 2-vertex subset M of {0,1}^3
    # has a stay hitting it. I.e., the stay vertices cover ALL possible
    # 2-element P1-mover sets.

    print(f"\n{'='*70}")
    print("COVERAGE ARGUMENT: can stays avoid ALL possible 2-vertex P1-mover sets?")
    print("="*70)

    from itertools import combinations

    for n_test in [5, 6]:
        ms_test = [2, 2, 2] + [3] * (n_test - 3)
        max_len_t = 3 * n_test + 6
        words_t = enumerate_mover_words_smart(ms_test, n_test, max_len_t)

        # For each valid cycle, check: which 2-vertex subsets does the stay set avoid?
        avoidable_by_any = set()  # 2-vertex sets that SOME cycle's stays avoid

        for word in words_t:
            result = analyze_p1_free_cycles(ms_test, n_test, word)
            if result is None:
                continue
            stay_v = result['stay_vertices']
            # Which 2-vertex subsets are disjoint from stay_v?
            for pair in combinations(sorted(set((a,b,c) for a in range(2)
                                                 for b in range(2)
                                                 for c in range(2))), 2):
                if pair[0] not in stay_v and pair[1] not in stay_v:
                    avoidable_by_any.add(pair)

        n_pairs = len(list(combinations(range(8), 2)))
        print(f"\n  n={n_test}: {len(avoidable_by_any)}/{n_pairs} 2-vertex P1-mover sets "
              f"can be avoided by stays in SOME cycle")
        if avoidable_by_any:
            for pair in sorted(avoidable_by_any):
                print(f"    avoidable: {pair}")
        else:
            print(f"    NO 2-vertex set avoidable → P1 overlap unavoidable! ★")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
