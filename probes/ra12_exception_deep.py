#!/usr/bin/env python3
"""
RA12: Deep analysis of the 8 EC-free walks for (3,3,3) placement at n=9.

Questions:
1. What do these 8 walks look like? (symmetry, structure)
2. Do they have shadow cycles?
3. Can they be completed to valid self-stabilizing systems?
4. Are these walks also EC-free at smaller n with similar placements?
"""

from itertools import product as iproduct
from collections import Counter
import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


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


def enumerate_walks(n, ms):
    total_len = sum(ms)
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == total_len:
            nxt = path[0]
            if abs(pos - nxt) % n in (1, n - 1):
                if all(fc[p] == ms[p] for p in range(n)):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    for p0 in range(n):
        fc = [0] * n
        fc[p0] = 1
        dfs([p0], fc)
    unique = set()
    result = []
    for w in walks:
        ell = len(w)
        best = w
        for i in range(ell):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(w)
    return result


def has_ec(word, n, ms, combo):
    """Check if (word, state-seq combo) has entry conflict."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    good = configs[:L]
    for j in range(n):
        Lp = (j - 1) % n
        Rp = (j + 1) % n
        mover_ctxs = set()
        nonmover_ctxs = set()
        for t in range(L):
            ctx = (good[t][Lp], good[t][j], good[t][Rp])
            if word[t] == j:
                next_val = good[(t + 1) % L][j]
                if next_val != ctx[1]:
                    mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False


def find_ec_free_walks(n, ms):
    """Find walks where ALL state-seq combos are EC-free."""
    walks = enumerate_walks(n, ms)
    ec_free = []
    for word in walks:
        proc_seqs = {p: enumerate_state_sequences(ms[p], ms[p]) for p in range(n)}
        sl = [proc_seqs[p] for p in range(n)]
        all_free = True
        valid_count = 0
        for combo in iproduct(*sl):
            result = has_ec(word, n, ms, combo)
            if result is None:
                continue
            valid_count += 1
            if result:
                all_free = False
                break
        if all_free and valid_count > 0:
            ec_free.append((word, valid_count))
    return walks, ec_free


def walk_direction_string(word, n):
    """Show the direction at each step."""
    L = len(word)
    dirs = []
    for i in range(L):
        d = (word[(i + 1) % L] - word[i]) % n
        if d == 1:
            dirs.append('+')
        elif d == n - 1:
            dirs.append('-')
        else:
            dirs.append('?')
    return ''.join(dirs)


def walk_relative_form(word, n):
    """Express walk as sequence of relative moves."""
    L = len(word)
    moves = []
    for i in range(L):
        d = (word[(i + 1) % L] - word[i]) % n
        if d == 1:
            moves.append('+1')
        elif d == n - 1:
            moves.append('-1')
    return moves


def check_shadow(word, n, ms):
    """Check if this walk has a shadow cycle (another good cycle using
    the same configs in a different order with a parallel mover sequence).

    For the shadow cycle check, we use the incrementing transition and
    check if there exists a config permutation that yields a valid shadow.
    """
    L = len(word)
    # Build configs with incrementing transition
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return False, "not a cycle"
    good = configs[:L]
    if len(set(good)) != L:
        return False, "not distinct"

    # Check if the config set contains a shadow cycle
    # A shadow cycle uses the same configs but with different movers
    # This is complex to check in general; let's check a simpler property:
    # Does the cycle have the "uniform escape" property that allows shadow?

    # Simple check: for each config, can we determine a unique mover?
    # If yes, no shadow is possible with different movers.
    config_to_mover = {}
    for t in range(L):
        c = good[t]
        if c in config_to_mover:
            if config_to_mover[c] != word[t]:
                return True, "config appears with different movers"
        else:
            config_to_mover[c] = word[t]

    return False, "all configs have unique movers"


def main():
    n = 9
    ms = make_ms(n, (0, 3, 6))
    threshold = 4 * (3 ** 7)
    product = 1
    for m in ms:
        product *= m

    print("=" * 70)
    print(f"RA12: Deep analysis of EC-free walks")
    print(f"n={n}, ms={ms}, product={product}, threshold={threshold}")
    print(f"Binary at: {[i for i in range(n) if ms[i] == 2]}")
    print("=" * 70)

    walks, ec_free = find_ec_free_walks(n, ms)
    print(f"\nTotal walks: {len(walks)}")
    print(f"EC-free walks (all combos): {len(ec_free)}")

    # Show each EC-free walk
    print(f"\n{'='*70}")
    print("EC-FREE WALKS:")
    print(f"{'='*70}")

    for i, (word, valid_count) in enumerate(ec_free):
        dirs = walk_direction_string(word, n)
        print(f"\nWalk {i+1}: {list(word)}")
        print(f"  Directions: {dirs}")
        print(f"  Valid combos: {valid_count}")

        # Show direction changes
        changes = []
        for j in range(len(word)):
            d1 = (word[(j+1) % len(word)] - word[j]) % n
            d2 = (word[(j+2) % len(word)] - word[(j+1) % len(word)]) % n
            if d1 != d2:
                changes.append((j, word[j], '+' if d1 == 1 else '-',
                               '+' if d2 == 1 else '-'))

        print(f"  Turn points ({len(changes)}): ", end="")
        for j, pos, d1, d2 in changes:
            print(f"step {j}(P{pos}:{d1}->{d2}) ", end="")
        print()

        # Check shadow
        has_shadow, reason = check_shadow(word, n, ms)
        print(f"  Shadow: {has_shadow} ({reason})")

    # Look for structural patterns
    print(f"\n{'='*70}")
    print("STRUCTURAL ANALYSIS")
    print(f"{'='*70}")

    # Are all EC-free walks related by rotation/reflection?
    print("\nDirection sequences:")
    dir_seqs = set()
    for word, _ in ec_free:
        ds = walk_direction_string(word, n)
        dir_seqs.add(ds)
        print(f"  {ds}")
    print(f"Distinct direction sequences: {len(dir_seqs)}")

    # Check: which procs are at turn points?
    print("\nTurn-point processors:")
    for word, _ in ec_free:
        L = len(word)
        turns = []
        for j in range(L):
            d1 = (word[(j+1) % L] - word[j]) % n
            d2 = (word[(j+2) % L] - word[(j+1) % L]) % n
            if d1 != d2:
                turns.append(word[(j+1) % L])
        print(f"  Turn procs: {turns}")

    # Cross-check with n=6, ms=[2,3,2,3,2,3] (alternating, non-consecutive)
    print(f"\n{'='*70}")
    print("COMPARISON: n=6, ms=[2,3,2,3,2,3] (alternating, gaps=(2,2,2))")
    print(f"{'='*70}")

    n6 = 6
    ms6 = [2, 3, 2, 3, 2, 3]
    walks6, ec_free6 = find_ec_free_walks(n6, ms6)
    print(f"Total walks: {len(walks6)}")
    print(f"EC-free walks: {len(ec_free6)}")
    for word, vc in ec_free6:
        dirs = walk_direction_string(word, n6)
        print(f"  {list(word)}, dirs={dirs}, valid={vc}")

    # Cross-check with n=7, non-consecutive 3-binary
    print(f"\n{'='*70}")
    print("COMPARISON: n=7, ms=[2,3,2,3,2,3,3] (gaps=(2,2,3))")
    print(f"{'='*70}")

    n7 = 7
    ms7 = [2, 3, 2, 3, 2, 3, 3]
    walks7, ec_free7 = find_ec_free_walks(n7, ms7)
    print(f"Total walks: {len(walks7)}")
    print(f"EC-free walks: {len(ec_free7)}")
    for word, vc in ec_free7:
        dirs = walk_direction_string(word, n7)
        print(f"  {list(word)}, dirs={dirs}, valid={vc}")

    # Also check n=5, non-consecutive
    print(f"\n{'='*70}")
    print("COMPARISON: n=5, non-consecutive binary placements")
    print(f"{'='*70}")

    for n5 in [5]:
        # Non-consecutive 3-binary on 5-ring: only possible with gaps (2,2,1)?
        # No, gaps >= 1, sum=5-3=2? No, sum of gaps = 5, each >= 2 (non-consecutive)
        # 3 gaps each >= 2, sum >= 6 > 5. IMPOSSIBLE for n=5.
        # So 3 non-consecutive binary on n=5 is impossible.
        # What about 2 non-consecutive binary?
        ms5a = [2, 3, 2, 3, 3]  # binary at 0,2, gap 2,3
        walks5, ec_free5 = find_ec_free_walks(n5, ms5a)
        print(f"n=5, ms={ms5a}: walks={len(walks5)}, EC-free={len(ec_free5)}")

    # n=8 non-consecutive
    print(f"\n{'='*70}")
    print("COMPARISON: n=8, non-consecutive 3-binary")
    print(f"{'='*70}")

    # Gaps sum to 8, each >= 2. Possible: (2,2,4), (2,3,3), (2,4,2), (3,2,3), (3,3,2), (4,2,2)
    # Up to rotation: (2,2,4), (2,3,3), (3,3,2) ...
    from itertools import combinations as combos

    def canonical(positions, n):
        best = None
        for r in range(n):
            rotated = tuple(sorted((p + r) % n for p in positions))
            if best is None or rotated < best:
                best = rotated
        return best

    def is_nonconsec(positions, n):
        for i in range(len(positions)):
            for j in range(i + 1, len(positions)):
                if abs(positions[i] - positions[j]) % n in (1, n - 1):
                    return False
        return True

    n8 = 8
    seen = set()
    for combo in combos(range(n8), 3):
        if not is_nonconsec(combo, n8):
            continue
        c = canonical(combo, n8)
        if c in seen:
            continue
        seen.add(c)
        ms8 = make_ms(n8, c)
        positions = sorted(c)
        gaps = [(positions[(i+1)%3] - positions[i]) % n8 for i in range(3)]
        t0 = time.time()
        walks8, ec_free8 = find_ec_free_walks(n8, ms8)
        t1 = time.time()
        status = "ALL EC" if not ec_free8 else f"{len(ec_free8)} EC-FREE"
        print(f"  n=8, pos={c}, gaps={tuple(gaps)}, ms={ms8}: "
              f"walks={len(walks8)}, {status} ({t1-t0:.1f}s)")
        if ec_free8:
            for word, vc in ec_free8[:2]:
                print(f"    EC-free walk: {list(word)[:10]}...")


if __name__ == "__main__":
    main()
