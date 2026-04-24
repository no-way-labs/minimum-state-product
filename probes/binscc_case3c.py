#!/usr/bin/env python3
"""binscc_case3c.py — Close Case 3c: 3 non-consecutive binary + quaternary.

The only 3-binary multiset with m_i ≥ 4 below 4·3^(n-2) is:
  ms = (2,2,2,4,3,...,3): product = 32·3^(n-4) < 4·3^(n-2) = 12·3^(n-3)

For consecutive binary placements: UBO applies (walk-on-cube doesn't depend
on non-binary processors). Already handled.

For non-consecutive binary placements: need to verify overlap.

Strategy: For each non-consecutive 3-binary orientation of {2^3, 4, 3^{n-4}},
check if ALL good cycles have mover/nonmover overlap at some binary processor.
"""

from itertools import product as cartesian
from collections import Counter
import sys


def generate_necklaces(ms_sorted, n):
    """Generate topologically distinct ring orientations of a multiset."""
    from itertools import permutations

    ms_tuple = tuple(ms_sorted)
    seen = set()
    results = []

    for perm in permutations(ms_tuple):
        # Normalize: take min over rotations and reflections
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = perm[::-1]
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canonical = min(rotations + ref_rotations)
        if canonical not in seen:
            seen.add(canonical)
            results.append(perm)

    return results


def has_3_consecutive_binary(ms):
    """Check if ms has 3 consecutive binary processors on the ring."""
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def check_overlap_at_binary(ms, cycle_configs, cycle_movers):
    """Check if any binary processor has mover/nonmover overlap.

    cycle_configs: list of configs (tuples of length n)
    cycle_movers: list of mover positions (which processor fires)

    For each binary processor p:
      mover_contexts = {(c[p-1], c[p], c[p+1]) : step i where movers[i] == p}
      nonmover_contexts = {(c[p-1], c[p], c[p+1]) : step i where movers[i] != p}
      overlap iff mover_contexts ∩ nonmover_contexts ≠ ∅
    """
    n = len(ms)
    ell = len(cycle_configs)

    for p in range(n):
        if ms[p] != 2:
            continue

        mover_ctx = set()
        nonmover_ctx = set()

        for i in range(ell):
            c = cycle_configs[i]
            ctx = (c[(p-1) % n], c[p], c[(p+1) % n])

            if cycle_movers[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)

        if mover_ctx & nonmover_ctx:
            return True, p

    return False, None


def generate_good_cycles(ms, max_length=None):
    """Generate all good cycles for a given ms using BFS/DFS.

    A good cycle is a sequence of configs c_0, c_1, ..., c_{ℓ-1} where:
    - Each c_{i+1} differs from c_i by exactly one flip at the mover position
    - Mover at step i is ring-adjacent to mover at step i-1
    - Each processor fires ≡ 0 mod m_p times and ≥ 1 time (fairness)
    - All configs are distinct
    - c_ℓ = c_0 (cycle closure)

    This is computationally expensive. For small n, use direct enumeration.
    For larger n, use the mover word approach.
    """
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    # Ring adjacency
    ring_adj = set()
    for p in range(n):
        ring_adj.add((p, (p+1) % n))
        ring_adj.add(((p+1) % n, p))

    if max_length is None:
        max_length = 4 * n

    # Start config: all zeros
    start = tuple(0 for _ in range(n))

    # DFS to find cycles
    cycles_found = []

    def fire(config, p):
        """Fire processor p: flip c[p] to next state."""
        c = list(config)
        c[p] = (c[p] + 1) % ms[p]
        return tuple(c)

    def dfs(path, movers, fire_counts, visited):
        if len(path) > max_length:
            return

        current = path[-1]
        last_mover = movers[-1] if movers else None

        # Try each ring-adjacent processor
        for p in range(n):
            if last_mover is not None and (last_mover, p) not in ring_adj:
                continue

            next_config = fire(current, p)
            new_counts = list(fire_counts)
            new_counts[p] += 1

            # Check if we've closed the cycle
            if next_config == start and len(path) >= 6:
                # Check fairness: each fires ≡ 0 mod m_p and ≥ 1
                fair = True
                for q in range(n):
                    if new_counts[q] == 0 or new_counts[q] % ms[q] != 0:
                        fair = False
                        break
                if fair:
                    cycles_found.append((list(path), list(movers) + [p]))
                continue

            if next_config in visited:
                continue

            visited.add(next_config)
            path.append(next_config)
            movers.append(p)

            dfs(path, movers, new_counts, visited)

            path.pop()
            movers.pop()
            visited.remove(next_config)

    # Start DFS from each possible first mover
    for p in range(n):
        first_config = fire(start, p)
        if first_config == start:
            continue
        visited = {start, first_config}
        dfs([start, first_config], [p], [1 if i == p else 0 for i in range(n)], visited)

    return cycles_found


def check_overlap_mover_word(ms, mover_word):
    """Given a mover word (sequence of processor indices), construct the
    cycle starting from all-zeros and check overlap.

    Returns (has_overlap, proc) or (None, None) if cycle doesn't close.
    """
    n = len(ms)
    ell = len(mover_word)

    # Build cycle
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = mover_word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))

    # Check closure
    if configs[-1] != configs[0]:
        return None, None, "not closed"

    # Check distinctness
    if len(set(configs[:ell])) != ell:
        return None, None, "not distinct"

    # Check fairness
    fire_counts = [0] * n
    for p in mover_word:
        fire_counts[p] += 1
    for p in range(n):
        if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
            return None, None, "not fair"

    # Check ring adjacency
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        if abs(p1 - p2) != 1 and abs(p1 - p2) != n-1:
            return None, None, "not ring-adjacent"

    # Check overlap
    has_ovlp, proc = check_overlap_at_binary(ms, configs[:ell], mover_word)
    return has_ovlp, proc, "ok"


def enumerate_mover_words(ms, max_length):
    """Enumerate all ring-adjacent mover words that close and are fair."""
    n = len(ms)

    ring_adj_list = {}
    for p in range(n):
        ring_adj_list[p] = [(p-1) % n, (p+1) % n]

    results = []

    def dfs(word, fire_counts, current_config, start_config):
        if len(word) > max_length:
            return

        # Check closure
        if len(word) >= 6 and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return

        # Extend
        last = word[-1]
        for nxt in ring_adj_list[last]:
            new_config = list(current_config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)

            new_counts = list(fire_counts)
            new_counts[nxt] += 1

            word.append(nxt)
            dfs(word, new_counts, new_config, start_config)
            word.pop()

    start = tuple(0 for _ in range(n))
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        first = tuple(first)
        dfs([p], [1 if i == p else 0 for i in range(n)], first, start)

    return results


def main():
    print("=" * 70)
    print("CASE 3c: 3 Non-Consecutive Binary + Quaternary")
    print("=" * 70)

    # ================================================================
    # Part 1: Scope the problem
    # ================================================================
    print("\n--- Part 1: Problem scope ---")
    print("""
Multisets with product < 4·3^(n-2) and exactly 3 binary:
  - Pure {2,3}: 8·3^(n-3) ≈ 2.67·3^(n-2) < 4·3^(n-2). Handled.
  - {2^3, 4, 3^(n-4)}: 32·3^(n-4) ≈ 3.56·3^(n-2) < 4·3^(n-2). THE GAP.
  - {2^3, 5, 3^(n-4)}: 40·3^(n-4) ≈ 4.44·3^(n-2) > 4·3^(n-2). Above bound.

So only {2^3, 4, 3^(n-4)} needs handling.

Consecutive binary → UBO applies (walk-on-cube, n-independent).
Non-consecutive binary → NEED TO VERIFY.
""")

    # ================================================================
    # Part 2: Small n verification
    # ================================================================
    print("--- Part 2: Small n verification ---\n")

    for n in [5, 6, 7]:
        ms_base = [2,2,2,4] + [3]*(n-4)
        necklaces = generate_necklaces(ms_base, n)

        non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]
        consec = [ms for ms in necklaces if has_3_consecutive_binary(ms)]

        print(f"n={n}: {len(necklaces)} total orientations, "
              f"{len(consec)} consecutive, {len(non_consec)} non-consecutive")

        # For small n, enumerate all mover words
        total_cycles = 0
        total_overlap = 0
        total_clean = 0

        for ms_tuple in non_consec:
            ms = list(ms_tuple)
            words = enumerate_mover_words(ms, max_length=3*n+2)

            ms_cycles = 0
            ms_overlap = 0

            for word in words:
                has_ovlp, proc, status = check_overlap_mover_word(ms, word)
                if status != "ok":
                    continue

                ms_cycles += 1
                if has_ovlp:
                    ms_overlap += 1

            total_cycles += ms_cycles
            total_overlap += ms_overlap

            if ms_cycles > 0 and ms_overlap < ms_cycles:
                clean = ms_cycles - ms_overlap
                total_clean += clean
                print(f"  ms={ms_tuple}: {ms_cycles} cycles, "
                      f"{ms_overlap} overlap, {clean} CLEAN")

        if total_clean == 0 and total_cycles > 0:
            print(f"  ★ n={n}: ALL {total_cycles} cycles on {len(non_consec)} "
                  f"non-consec orientations have overlap")
        elif total_cycles == 0:
            print(f"  n={n}: no fair cycles found (expected for small n)")

    # ================================================================
    # Part 3: n=9 verification (the critical case)
    # ================================================================
    print(f"\n{'=' * 70}")
    print("Part 3: n=9 verification")
    print("=" * 70)

    n = 9
    ms_base = [2,2,2,4] + [3]*5
    necklaces = generate_necklaces(ms_base, n)
    non_consec = [ms for ms in necklaces if not has_3_consecutive_binary(ms)]

    print(f"\nn={n}: {len(necklaces)} total orientations, "
          f"{len(non_consec)} non-consecutive")

    # For n=9, enumerate_mover_words is too expensive.
    # Instead, use the bounce/sweep patterns and check overlap directly.

    # Bounce pattern: up-down (0,1,2,...,n-1,n-2,...,1)
    def make_bounce(n, direction='up'):
        if direction == 'up':
            return list(range(n)) + list(range(n-2, 0, -1))
        else:
            return list(range(n-1, -1, -1)) + list(range(1, n-1))

    # Check bounce cycles for each non-consecutive orientation
    for ms_tuple in non_consec[:20]:
        ms = list(ms_tuple)

        # Try different cycle patterns
        for pattern_name, base_pattern in [
            ("up-down", make_bounce(n, 'up')),
            ("down-up", make_bounce(n, 'down')),
        ]:
            # Repeat the base pattern enough times for fairness
            for repeats in range(1, 8):
                word = base_pattern * repeats
                has_ovlp, proc, status = check_overlap_mover_word(ms, word)
                if status == "ok":
                    ovlp_str = f"P{proc} overlap" if has_ovlp else "CLEAN"
                    if not has_ovlp:
                        print(f"  ms={ms_tuple}, {pattern_name}×{repeats}: {ovlp_str} ★★★")
                    break  # found a fair cycle

    # Also try sweep pattern
    for ms_tuple in non_consec[:5]:
        ms = list(ms_tuple)
        sweep_fwd = list(range(n)) * 4  # forward sweep repeated
        sweep_rev = list(range(n-1, -1, -1)) * 4

        for name, word in [("fwd-sweep", sweep_fwd), ("rev-sweep", sweep_rev)]:
            # Trim to find a fair closing
            for trim_len in range(3*n-2, 5*n):
                if trim_len > len(word):
                    break
                w = word[:trim_len]
                has_ovlp, proc, status = check_overlap_mover_word(ms, w)
                if status == "ok":
                    ovlp_str = f"P{proc}" if has_ovlp else "CLEAN ★★★"
                    print(f"  ms={ms_tuple}, {name} len={trim_len}: {ovlp_str}")
                    break


if __name__ == "__main__":
    main()
