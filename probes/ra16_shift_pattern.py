#!/usr/bin/env python3
"""
RA16d: Characterize the binary shift pattern for shadow disjointness.

From RA16c: every no-EC sweep cycle has a binary-only shift producing
a disjoint shadow. The shift always seems to be {0, 4} at n=7 and n=9.

Questions:
1. Which SUBSETS of binary procs work? Is it always the non-adjacent pair?
2. Does flipping ALL 3 binary procs work? Just 1? Just 2?
3. Is the working subset always the same pair, or does it depend on the cycle?
4. What's the structure: can we predict WHICH pair works from the cycle topology?
5. The critical test: does the shadow cycle also satisfy disjointness at ALL
   positions (not just globally distinct + disjoint from good)?

Also: the shadow needs to be a valid CYCLE (each shadow config has exactly one
privileged proc, and the shadow successor is the next shadow config). Check this.
"""
from itertools import combinations
from collections import Counter, defaultdict
import time


def total_displacement(word, n):
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def has_3_consecutive_binary(ms):
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=120):
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    def dfs(word, fc):
        if time.time() - t0 > timeout:
            return
        if len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0]*n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)

    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def build_configs_all_trans(word, ms, n):
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)
    results = []
    for trans_bits in range(1 << n_tern):
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1
        configs = [[0]*n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue
        results.append((trans_dir.copy(), [tuple(c) for c in configs[:L]]))
    return results


def find_ec_at_proc(word, configs, n, j):
    L = len(word)
    mt = set()
    nmt = set()
    for t in range(L):
        c = configs[t]
        triple = (c[(j-1)%n], c[j], c[(j+1)%n])
        if word[t] == j:
            mt.add(triple)
        else:
            nmt.add(triple)
    return mt & nmt


def has_any_ec(word, configs, ms, n):
    for j in range(n):
        if find_ec_at_proc(word, configs, n, j):
            return True
    return False


def shadow_with_offset(configs, ms, n, offset_map):
    shadow = []
    for c in configs:
        sc = list(c)
        for p in range(n):
            sc[p] = (sc[p] + offset_map.get(p, 0)) % ms[p]
        shadow.append(tuple(sc))
    return shadow


def check_shadow_ec(word, shadow_configs, ms, n):
    """Check if the SHADOW cycle itself has EC (same mover word, shifted configs)."""
    for j in range(n):
        overlap = find_ec_at_proc(word, shadow_configs, n, j)
        if overlap:
            return True, j, overlap
    return False, None, None


def main():
    print("RA16d: Binary Shift Pattern Analysis")
    print("="*70)

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n = {n}, threshold = {threshold}")
        print(f"{'='*70}")

        seen = set()
        all_cases = []
        for nb in range(3, n+1):
            nt = n - nb
            prod = (2**nb) * (3**nt)
            if prod >= threshold:
                continue
            for bin_combo in combinations(range(n), nb):
                bins_set = set(bin_combo)
                ms = [2 if p in bins_set else 3 for p in range(n)]
                if has_3_consecutive_binary(ms):
                    continue
                product = 1
                for m in ms:
                    product *= m
                if product >= threshold:
                    continue
                ms_rotations = [tuple(ms[(r+i)%n] for i in range(n)) for r in range(n)]
                canon_ms = min(ms_rotations)
                if canon_ms not in seen:
                    seen.add(canon_ms)
                    all_cases.append((canon_ms, ms))

        working_subsets = Counter()
        shadow_ec_total = 0
        no_ec_total = 0

        for canon_ms, ms in all_cases:
            max_len = sum(ms)
            words = enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=90)
            unique_words = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique_words:
                    unique_words[c] = w

            sweep_words = [w for w in unique_words.values()
                           if total_displacement(list(w), n) is not None
                           and abs(total_displacement(list(w), n)) >= 2*n]

            if not sweep_words:
                continue

            bins = sorted(p for p in range(n) if ms[p] == 2)
            nb = len(bins)

            print(f"\n--- ms={list(ms)}, bins={bins} ---")

            for w in sweep_words:
                for trans_dir, configs in build_configs_all_trans(w, ms, n):
                    if has_any_ec(w, configs, ms, n):
                        continue

                    no_ec_total += 1

                    # Test ALL subsets of binary procs for shift
                    config_set = set(configs)
                    L = len(w)

                    print_detail = (no_ec_total <= 2)
                    if print_detail:
                        print(f"\n  Cycle #{no_ec_total}: trans={trans_dir}")

                    for r in range(1, nb+1):
                        for subset in combinations(bins, r):
                            offset_map = {b: 1 for b in subset}
                            shadow = shadow_with_offset(configs, ms, n, offset_map)
                            shadow_set = set(shadow)
                            overlap = len(shadow_set & config_set)
                            distinct = len(shadow_set) == L

                            disjoint = (overlap == 0)
                            if print_detail:
                                print(f"    shift {sorted(subset)}: "
                                      f"disjoint={disjoint}, distinct={distinct}, "
                                      f"overlap={overlap}")

                            if disjoint and distinct:
                                working_subsets[tuple(sorted(subset))] += 1

                                # Check if shadow cycle has EC
                                has_sec, sec_proc, sec_overlap = check_shadow_ec(
                                    w, shadow, ms, n)
                                if has_sec:
                                    shadow_ec_total += 1
                                    if print_detail:
                                        print(f"      SHADOW HAS EC at proc {sec_proc}: "
                                              f"{sec_overlap}")

        print(f"\n{'='*70}")
        print(f"SHIFT SUBSET ANALYSIS for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC cycles: {no_ec_total}")
        print(f"\nWorking binary subsets (subset -> count):")
        for subset, cnt in sorted(working_subsets.items(), key=lambda x: -x[1]):
            print(f"  {list(subset)}: {cnt}")
        print(f"\nShadow cycles with EC: {shadow_ec_total}/{no_ec_total}")

        # Adjacency analysis of working subsets
        print(f"\nAdjacency pattern of working subsets:")
        for subset, cnt in sorted(working_subsets.items()):
            adj_pairs = sum(1 for i in range(len(subset))
                           for j in range(i+1, len(subset))
                           if abs(subset[i] - subset[j]) % n in (1, n-1))
            all_nonadj = (adj_pairs == 0)
            has_adj = (adj_pairs > 0)
            print(f"  {list(subset)}: adj_pairs={adj_pairs}, "
                  f"all_nonadj={all_nonadj}")


if __name__ == '__main__':
    main()
