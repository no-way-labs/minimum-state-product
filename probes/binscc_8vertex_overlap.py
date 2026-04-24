#!/usr/bin/env python3
"""binscc_8vertex_overlap.py — Does visiting all 8 cube vertices force FULL-CONTEXT overlap?

Key question: UBO proves 2D-projection overlap for all {0,1}^3 walks.
But 2D ≠ full context (c_{n-1}, c_0, c_1) because c_{n-1} can be non-binary.

M_5=96 witness avoids overlap by visiting only 6/8 vertices.
If visiting all 8 forces full-context overlap, we just need to show
sub-threshold products force all 8 vertices.

Test: enumerate mover words for ms with 3 consecutive binary,
check which visit all 8 cube vertices, and whether those have
full-context overlap.
"""

from itertools import product as iproduct
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


def analyze_cycle(ms, n, mover_word):
    """Build cycle configs and analyze cube vertex coverage + overlap."""
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

    # Find consecutive binary processors (first group of 3)
    bin_procs = [i for i in range(n) if ms[i] == 2]
    consec_triple = None
    for i in range(len(bin_procs)):
        p0 = bin_procs[i]
        p1 = (p0 + 1) % n
        p2 = (p0 + 2) % n
        if ms[p1] == 2 and ms[p2] == 2:
            consec_triple = (p0, p1, p2)
            break
    if consec_triple is None:
        return None

    bp0, bp1, bp2 = consec_triple

    # Cube vertices visited
    cube_vertices = set()
    for c in configs[:ell]:
        cube_vertices.add((c[bp0], c[bp1], c[bp2]))

    # Full-context overlap at each binary processor
    overlap_procs = []
    for p in [bp0, bp1, bp2]:
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
            overlap_procs.append(p)

    # 2D-projection overlap (what UBO checks)
    proj_overlap_procs = []
    for p in [bp0, bp1, bp2]:
        # P0: proj = (c_0, c_1), P1: proj = (c_0, c_1, c_2) = full cube, P2: proj = (c_1, c_2)
        mover_proj = set()
        nonmover_proj = set()
        for i in range(ell):
            c = configs[i]
            if p == bp0:
                proj = (c[bp0], c[bp1])
            elif p == bp1:
                proj = (c[bp0], c[bp1], c[bp2])
            else:  # bp2
                proj = (c[bp1], c[bp2])
            if mover_word[i] == p:
                mover_proj.add(proj)
            else:
                nonmover_proj.add(proj)
        if mover_proj & nonmover_proj:
            proj_overlap_procs.append(p)

    return {
        'configs': configs[:ell],
        'cube_vertices': cube_vertices,
        'n_cube_vertices': len(cube_vertices),
        'overlap_procs': overlap_procs,
        'has_full_overlap': len(overlap_procs) > 0,
        'proj_overlap_procs': proj_overlap_procs,
        'has_proj_overlap': len(proj_overlap_procs) > 0,
    }


def main():
    print("=" * 70)
    print("8-VERTEX OVERLAP TEST")
    print("Does visiting all 8 cube vertices force FULL-CONTEXT overlap?")
    print("=" * 70)

    # Test various ms with 3 consecutive binary
    test_cases = [
        # (n, ms, label)
        (5, [2, 2, 2, 3, 3], "n=5 {2^3,3^2} prod=72"),
        (5, [2, 2, 2, 3, 4], "n=5 {2^3,3,4} prod=96"),
        (6, [2, 2, 2, 3, 3, 3], "n=6 {2^3,3^3} prod=216"),
        (6, [2, 2, 2, 3, 3, 4], "n=6 {2^3,3^2,4} prod=288"),
        (7, [2, 2, 2, 3, 3, 3, 3], "n=7 {2^3,3^4} prod=648"),
        (7, [2, 2, 2, 3, 3, 3, 4], "n=7 {2^3,3^3,4} prod=864"),
    ]

    for n, ms, label in test_cases:
        max_len = 3 * n + 6  # generous bound
        words = enumerate_mover_words_smart(ms, n, max_len)

        by_vertices = {}  # n_vertices -> (total, full_overlap, proj_overlap)
        sample_8v_clean = []  # samples with 8 vertices but no full overlap

        for word in words:
            result = analyze_cycle(ms, n, word)
            if result is None:
                continue

            nv = result['n_cube_vertices']
            if nv not in by_vertices:
                by_vertices[nv] = [0, 0, 0]
            by_vertices[nv][0] += 1
            if result['has_full_overlap']:
                by_vertices[nv][1] += 1
            if result['has_proj_overlap']:
                by_vertices[nv][2] += 1

            if nv == 8 and not result['has_full_overlap'] and len(sample_8v_clean) < 3:
                sample_8v_clean.append((word, result))

        print(f"\n--- {label} ---")
        print(f"  {len(words)} mover words enumerated")
        for nv in sorted(by_vertices.keys()):
            total, full_ovl, proj_ovl = by_vertices[nv]
            print(f"  {nv} vertices: {total} cycles, "
                  f"{full_ovl} full-overlap ({100*full_ovl/total:.0f}%), "
                  f"{proj_ovl} proj-overlap ({100*proj_ovl/total:.0f}%)")

        if sample_8v_clean:
            print(f"  ** {len(sample_8v_clean)} examples: 8 vertices, NO full-context overlap **")
            for word, result in sample_8v_clean[:1]:
                print(f"     Word: {word}")
                print(f"     Cube vertices: {sorted(result['cube_vertices'])}")
                print(f"     Overlap procs (full): {result['overlap_procs']}")
                print(f"     Overlap procs (proj): {result['proj_overlap_procs']}")

                # Show the mover/nonmover contexts at each binary proc
                configs = result['configs']
                bp0, bp1, bp2 = 0, 1, 2  # consecutive binary
                for p in [bp0, bp1, bp2]:
                    mover_ctx = set()
                    nonmover_ctx = set()
                    for i in range(len(word)):
                        c = configs[i]
                        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                        if word[i] == p:
                            mover_ctx.add(ctx)
                        else:
                            nonmover_ctx.add(ctx)
                    print(f"     P{p}: mover={sorted(mover_ctx)}, nonmover={sorted(nonmover_ctx)}")
                    ovl = mover_ctx & nonmover_ctx
                    if ovl:
                        print(f"          OVERLAP: {sorted(ovl)}")
                    else:
                        print(f"          separated by non-binary neighbor")
        elif 8 in by_vertices:
            full_rate = by_vertices[8][1] / by_vertices[8][0]
            if full_rate == 1.0:
                print(f"  ★ ALL 8-vertex cycles have FULL-CONTEXT overlap!")
            else:
                print(f"  8-vertex full-overlap rate: {full_rate:.4f}")
        sys.stdout.flush()

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print("="*70)
    print("If 8-vertex → full overlap for ALL sub-threshold ms,")
    print("then lower bound reduces to: sub-threshold ⇒ all 8 vertices.")


if __name__ == "__main__":
    main()
