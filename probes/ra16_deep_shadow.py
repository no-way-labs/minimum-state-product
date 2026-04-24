#!/usr/bin/env python3
"""
RA16c: Deep investigation of the no-EC, no-simple-shadow sweep cycles.

KEY OBSERVATION from RA16b: at each binary proc b, the shadow (flip b)
has 4/18 configs that ARE in the good cycle (n=7) or 4/24 (n=9).
That is: ~78% of shadow configs are NOT in the cycle, but ~22% are.

Questions:
1. WHICH configs overlap? Are they always at the SAME positions?
2. Does the PROVED shadow cycle theorem (which uses a specific permutation sigma)
   apply here? That theorem shifts ALL binary procs simultaneously.
3. What about the full waterfall/MNU approach?
4. Is there a DIFFERENT obstruction that works?

Alternative: the existing proved approach for non-consecutive binary uses
SHADOW cycles based on the universal sweep shadow construction (CIC Expl 6+)
which shifts ALL configs, not just flipping one binary. Let me check that.
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


def shadow_shift_all_binary(configs, ms, n):
    """Shift ALL binary procs by +1 simultaneously."""
    bins = [p for p in range(n) if ms[p] == 2]
    shadow = []
    for c in configs:
        sc = list(c)
        for b in bins:
            sc[b] = (sc[b] + 1) % 2
        shadow.append(tuple(sc))
    return shadow


def shadow_with_offset(configs, ms, n, offset_map):
    """Apply arbitrary offset to each proc."""
    shadow = []
    for c in configs:
        sc = list(c)
        for p in range(n):
            sc[p] = (sc[p] + offset_map.get(p, 0)) % ms[p]
        shadow.append(tuple(sc))
    return shadow


def check_mnu_waterfall(word, configs, ms, n):
    """Check MNU (Mover Non-mover Uniqueness) waterfall.

    For each proc p, and each mover step t where word[t]=p:
    the config at step t should have a unique (L,S,R) triple
    among ALL non-mover appearances of p.

    MNU means: mover triples ∩ nonmover triples = empty at every proc.
    This IS exactly the absence of entry conflict.

    So MNU fails iff EC exists. Which we already know fails.
    The shadow approach needs something else.
    """
    pass


def analyze_overlap_positions(word, configs, ms, n, shadow_configs):
    """For configs that appear in both good cycle and shadow, find positions."""
    L = len(word)
    config_set = set(configs)
    shadow_set = set(shadow_configs)
    overlap = config_set & shadow_set

    if not overlap:
        return {'overlap_count': 0}

    # For each overlapping config, find its position in good cycle and shadow
    good_positions = {}
    shadow_positions = {}
    for c in overlap:
        good_positions[c] = [t for t in range(L) if configs[t] == c]
        shadow_positions[c] = [t for t in range(L) if shadow_configs[t] == c]

    return {
        'overlap_count': len(overlap),
        'overlap_configs': overlap,
        'good_positions': good_positions,
        'shadow_positions': shadow_positions,
    }


def check_universal_shadow(word, configs, ms, n):
    """Try the UNIVERSAL shadow construction from CIC exploration.

    The proved shadow cycle theorem for uniform sweeps uses a specific
    permutation sigma that maps step t to step sigma(t), shifting configs.

    For sweep word w with displacement -2n (CCW sweep):
    sigma(0) = n-4, sigma(1) = n-1, sigma(2) = 0,
    sigma(k) = k-2 for 3 <= k <= n-3,
    sigma(n-2) = n-2, sigma(n-1) = n-3.

    But this was proved for UNIFORM sweeps (each proc fires exactly m_p
    times, the word goes CW then CCW in clean passes).

    These no-EC cycles have turnarounds (stuttered sweeps), so the
    uniform sigma may not apply directly.

    Let me check: what IS the mover word structure?
    """
    L = len(word)
    fc = Counter(word)
    disp = total_displacement(list(word), n)

    # Check if it's a uniform sweep
    is_uniform = True
    # Uniform sweep: visits each proc exactly m_p times, with clean CW then CCW passes
    # Actually, for these no-EC cycles, the structure is a stuttered sweep

    return {
        'displacement': disp,
        'fc': dict(fc),
        'is_uniform': is_uniform,
    }


def try_all_shifts(word, configs, ms, n):
    """Try ALL possible constant shifts of configs and check disjointness.

    For each possible offset vector (d_0, d_1, ..., d_{n-1}) where
    0 <= d_p < m_p, check if shifted configs are disjoint from good cycle.

    Only need to try shifts where at least one binary proc is shifted by 1.
    """
    L = len(word)
    config_set = set(configs)
    bins = [p for p in range(n) if ms[p] == 2]

    # Try shifts of binary procs only (ternary shift adds complexity)
    best_shifts = []

    # Enumerate: each binary can be shifted by 0 or 1, each ternary by 0,1,2
    # But total space is 2^nb * 3^nt which can be large.
    # Start with binary-only shifts.
    nb = len(bins)
    terns = [p for p in range(n) if ms[p] == 3]
    nt = len(terns)

    # Binary-only shifts (exclude all-zero)
    for bin_bits in range(1, 1 << nb):
        offset_map = {}
        for idx, b in enumerate(bins):
            if (bin_bits >> idx) & 1:
                offset_map[b] = 1
        shadow = shadow_with_offset(configs, ms, n, offset_map)
        shadow_set = set(shadow)
        overlap = len(shadow_set & config_set)
        distinct = len(shadow_set) == L
        if overlap == 0 and distinct:
            which_bins = [bins[idx] for idx in range(nb) if (bin_bits >> idx) & 1]
            best_shifts.append(('binary-only', which_bins, offset_map))

    # If no binary-only shift works, try binary+ternary
    if not best_shifts and nt <= 6:
        for bin_bits in range(1, 1 << nb):
            for tern_bits in range(3 ** nt):
                offset_map = {}
                for idx, b in enumerate(bins):
                    if (bin_bits >> idx) & 1:
                        offset_map[b] = 1
                tb = tern_bits
                for idx, t in enumerate(terns):
                    offset_map[t] = tb % 3
                    tb //= 3
                shadow = shadow_with_offset(configs, ms, n, offset_map)
                shadow_set = set(shadow)
                overlap = len(shadow_set & config_set)
                distinct = len(shadow_set) == L
                if overlap == 0 and distinct:
                    best_shifts.append(('mixed', None, offset_map))
                    break  # one is enough
            if best_shifts:
                break

    return best_shifts


def main():
    print("RA16c: Deep Shadow Investigation")
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

        no_ec_total = 0
        shift_found = 0
        shift_not_found = 0
        shift_types = Counter()

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

            for w in sweep_words:
                for trans_dir, configs in build_configs_all_trans(w, ms, n):
                    if has_any_ec(w, configs, ms, n):
                        continue

                    no_ec_total += 1

                    # Try all possible shifts
                    shifts = try_all_shifts(w, configs, ms, n)
                    if shifts:
                        shift_found += 1
                        shift_types[shifts[0][0]] += 1

                        if no_ec_total <= 3:
                            print(f"\n  Example {no_ec_total}: ms={list(ms)}")
                            print(f"    word={list(w)}")
                            print(f"    Working shift: type={shifts[0][0]}, "
                                  f"offset={shifts[0][2]}")
                    else:
                        shift_not_found += 1
                        if shift_not_found <= 3:
                            print(f"\n  NO SHIFT FOUND: ms={list(ms)}")
                            print(f"    word={list(w)}")
                            print(f"    trans_dir={trans_dir}")
                            # Show overlap for all-binary-flip
                            bins = [p for p in range(n) if ms[p] == 2]
                            all_bin_shadow = shadow_shift_all_binary(configs, ms, n)
                            config_set = set(configs)
                            overlap = set(all_bin_shadow) & config_set
                            print(f"    All-binary-flip overlap: {len(overlap)}/{len(configs)}")
                            for oc in sorted(overlap)[:5]:
                                gc_pos = [t for t in range(len(configs)) if configs[t] == oc]
                                sc_pos = [t for t in range(len(configs)) if all_bin_shadow[t] == oc]
                                print(f"      config {oc}: good@{gc_pos}, shadow@{sc_pos}")

        print(f"\n{'='*70}")
        print(f"SHIFT SEARCH SUMMARY for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC sweep cycles: {no_ec_total}")
        print(f"  Shift found (disjoint shadow): {shift_found}")
        print(f"  No shift found: {shift_not_found}")
        print(f"  Shift types: {dict(shift_types)}")
        if shift_not_found == 0 and no_ec_total > 0:
            print(f"  *** SOME constant shift always produces disjoint shadow ***")


if __name__ == '__main__':
    main()
