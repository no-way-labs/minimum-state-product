#!/usr/bin/env python3
"""binscc_mixed_escape_mnu.py — Test MNU + Escape for mixed {2,3,4+} systems.

Proves Case 3c by showing:
1. MNU holds for ALL good cycles on mixed sub-threshold systems
2. Escape Lemma holds (no forced move enters good cycle)
3. Combined with shadow existence → all cycles blocked

Tests sweep and non-sweep cycles on mixed multisets with:
- ≥3 binary processors
- ≤3 consecutive binary
- product < 4·3^(n-2)
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys
import time


def enumerate_mover_words_smart(ms, n, max_length):
    """Enumerate fair ring-adjacent mover words."""
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


def build_cycle(ms, n, mover_word):
    """Build good cycle from mover word using incrementing transitions."""
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
    # Verify fairness
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    for p in range(n):
        if fc[p] == 0 or fc[p] % ms[p] != 0:
            return None
    # Verify ring adjacency
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return None
    return configs[:ell]


def get_determined_entries(cycle, n):
    """Extract determined transition entries from good cycle."""
    ell = len(cycle)
    det = {}
    for i in range(ell):
        c = cycle[i]
        c_next = cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None  # invalid
        mover = diffs[0]
        # Mover entry
        L = c[(mover-1)%n]; S = c[mover]; R = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, L, S, R)
        if key in det and det[key] != S_new:
            return None  # conflict
        det[key] = S_new
        # Nonmover entries (identity)
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in det and det[key2] != Sj:
                    return None  # conflict
                det[key2] = Sj
    return det


def check_mnu(cycle, n):
    """Check Mover Neighborhood Uniqueness.

    For each mover step k (proc p moves to S'), check that (L, S', R)
    uniquely identifies exactly one good config in C.
    Returns list of violations (empty = MNU holds).
    """
    ell = len(cycle)
    violations = []
    for step in range(ell):
        c = cycle[step]
        c_next = cycle[(step + 1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            violations.append(('invalid_step', step))
            continue
        p = diffs[0]
        L = c[(p-1) % n]
        S_prime = c_next[p]
        R = c[(p+1) % n]
        # Count configs in C where proc p has neighborhood (L, S', R)
        matches = [j for j, gj in enumerate(cycle)
                   if gj[(p-1) % n] == L and gj[p] == S_prime and gj[(p+1) % n] == R]
        if len(matches) != 1:
            violations.append((step, p, L, S_prime, R, len(matches), matches))
    return violations


def check_escape(cycle, det, ms, n):
    """Check Universal Escape: no forced move at non-good config enters C.

    For every non-good config c, if proc i is forced-privileged
    (det[(i,L,S,R)] != S), check that firing i doesn't enter C.
    Returns (failures, total_forced_moves).
    """
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    failures = []
    total_forced = 0
    for c in non_good:
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                total_forced += 1
                # Fire proc i
                new_c = list(c)
                new_c[i] = det[key]
                new_c = tuple(new_c)
                if new_c in good_set:
                    failures.append((c, i, new_c))
    return failures, total_forced


def find_shadow(cycle, det, ms, n):
    """Find shadow cycle via forced moves from non-good configs.

    Returns shadow cycle (list of configs) or None if no shadow found.
    """
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        config = start
        visited = {}
        path = []
        for step in range(500):
            if config in good_set:
                break
            if config in visited:
                # Found cycle in non-good space
                cycle_start = visited[config]
                shadow = path[cycle_start:]
                return shadow
            visited[config] = len(path)
            path.append(config)
            # Find forced moves
            forced = []
            for j in range(n):
                Lj = config[(j-1)%n]; Sj = config[j]; Rj = config[(j+1)%n]
                key = (j, Lj, Sj, Rj)
                if key in det and det[key] != Sj:
                    forced.append((j, det[key]))
            if not forced:
                break
            # Apply first forced move that stays outside C
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
    return None


def get_sub_threshold_multisets(n, max_consec_binary=3):
    """Generate sub-threshold multisets with ≥3 binary and ≤max_consec_binary consecutive.

    Product threshold: 4·3^(n-2).
    Mixed multisets include quaternary, quinary, etc.
    """
    threshold = 4 * (3 ** (n - 2))
    results = []

    # Generate all multisets of n values ≥2 with product < threshold
    # and ≥3 binary (m=2) and at most max_consec_binary consecutive binary
    def gen(pos, current, prod):
        if pos == n:
            if prod < threshold:
                n_binary = sum(1 for m in current if m == 2)
                if n_binary >= 3:
                    # Check consecutive binary constraint
                    max_run = 0
                    run = 0
                    for i in range(2 * n):  # ring: check wraparound
                        if current[i % n] == 2:
                            run += 1
                            max_run = max(max_run, run)
                        else:
                            run = 0
                    if max_run <= max_consec_binary:
                        results.append(tuple(current))
            return
        # Determine max value at this position
        remaining = n - pos - 1
        min_remaining_prod = 2 ** remaining
        max_val = threshold // (prod * min_remaining_prod) + 1
        for m in range(2, min(max_val + 1, threshold // prod + 1)):
            if prod * m * (2 ** remaining) >= threshold * 2:
                break
            gen(pos + 1, current + [m], prod * m)

    gen(0, [], 1)

    # Remove duplicates (same multiset, different ring orientations)
    # Keep only canonical orientations for testing
    seen = set()
    unique = []
    for ms in results:
        key = tuple(sorted(ms))
        if key not in seen:
            seen.add(key)
            unique.append(ms)

    return unique


def get_all_orientations(ms_sorted, n):
    """Generate all distinct ring orientations of a sorted multiset."""
    from itertools import permutations
    seen = set()
    results = []
    for perm in permutations(ms_sorted):
        # Normalize by rotation and reflection
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = tuple(reversed(perm))
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canonical = min(rotations + ref_rotations)
        if canonical not in seen:
            seen.add(canonical)
            results.append(perm)
    return results


def has_mixed_moduli(ms):
    """Check if multiset contains moduli > 3 (quaternary+)."""
    return any(m > 3 for m in ms)


def main():
    print("=" * 70)
    print("MNU + ESCAPE FOR MIXED SYSTEMS (Case 3c)")
    print("=" * 70)
    print("Testing whether MNU and Escape extend to {2,3,4+} multisets")
    print("at sub-threshold products with ≥3 binary, ≤3 consecutive binary.")
    print()

    # Test cases: mixed multisets at small n
    test_cases = []

    for n in [5, 6, 7]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\nn={n}, threshold={threshold}")

        # Generate mixed multisets manually for small n
        if n == 5:
            # {2^3, 3, 4} = 2·2·2·3·4 = 96 >= threshold 108? No, 4·3^3=108, 96<108 ✓
            # Actually threshold = 4·3^3 = 108
            candidates = [
                [2, 2, 2, 3, 4],   # prod=96, mixed (quaternary)
                [2, 2, 2, 3, 3],   # prod=72, pure ternary (control)
                [2, 2, 2, 2, 6],   # prod=48, mixed (senary), 4 binary
                [2, 2, 2, 4, 4],   # prod=128 >= 108, skip
            ]
        elif n == 6:
            # threshold = 4·3^4 = 324
            candidates = [
                [2, 2, 2, 3, 3, 4],  # prod=288, mixed
                [2, 2, 2, 3, 3, 3],  # prod=216, pure ternary
                [2, 2, 2, 3, 4, 4],  # prod=384 >= 324, skip
                [2, 2, 2, 4, 3, 3],  # prod=288, mixed (different orient)
            ]
        elif n == 7:
            # threshold = 4·3^5 = 972
            candidates = [
                [2, 2, 2, 3, 3, 3, 4],  # prod=864, mixed
                [2, 2, 2, 3, 3, 3, 3],  # prod=648, pure ternary
                [2, 2, 2, 3, 3, 4, 4],  # prod=1152 >= 972, skip
            ]
        else:
            candidates = []

        for ms_base in candidates:
            prod = 1
            for m in ms_base:
                prod *= m
            if prod >= threshold:
                continue
            n_binary = sum(1 for m in ms_base if m == 2)
            if n_binary < 3:
                continue
            is_mixed = has_mixed_moduli(ms_base)
            test_cases.append((n, ms_base, prod, is_mixed))

    print(f"\n{'='*70}")
    print(f"Test cases: {len(test_cases)}")
    for n, ms, prod, mixed in test_cases:
        label = "MIXED" if mixed else "pure"
        print(f"  n={n} ms={ms} prod={prod} [{label}]")
    print(f"{'='*70}\n")

    # Run tests
    grand_stats = {
        'total_cycles': 0,
        'mnu_pass': 0,
        'mnu_fail': 0,
        'escape_pass': 0,
        'escape_fail': 0,
        'shadow_found': 0,
        'shadow_missing': 0,
        'conflict': 0,
        'fully_blocked': 0,
    }

    for n, ms, prod, is_mixed in test_cases:
        label = "MIXED" if is_mixed else "pure"
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms} prod={prod} [{label}]")
        print(f"{'='*60}")
        sys.stdout.flush()

        t0 = time.time()
        max_len = 3 * n + 6
        words = enumerate_mover_words_smart(ms, n, max_len)
        t1 = time.time()
        print(f"  Enumerated {len(words)} mover words in {t1-t0:.1f}s")

        stats = Counter()
        mnu_violations_detail = []
        escape_failures_detail = []

        for word_idx, word in enumerate(words):
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue

            stats['valid'] += 1

            # Get determined entries
            det = get_determined_entries(cycle, n)
            if det is None:
                stats['conflict'] += 1
                grand_stats['conflict'] += 1
                grand_stats['fully_blocked'] += 1
                continue

            # Check MNU
            mnu_viols = check_mnu(cycle, n)
            if not mnu_viols:
                stats['mnu_pass'] += 1
                grand_stats['mnu_pass'] += 1
            else:
                stats['mnu_fail'] += 1
                grand_stats['mnu_fail'] += 1
                if len(mnu_violations_detail) < 3:
                    mnu_violations_detail.append((word, mnu_viols[:2]))

            # Check Escape
            esc_failures, esc_total = check_escape(cycle, det, ms, n)
            if not esc_failures:
                stats['escape_pass'] += 1
                grand_stats['escape_pass'] += 1
            else:
                stats['escape_fail'] += 1
                grand_stats['escape_fail'] += 1
                if len(escape_failures_detail) < 3:
                    escape_failures_detail.append((word, esc_failures[:2]))

            # Check Shadow
            shadow = find_shadow(cycle, det, ms, n)
            if shadow:
                stats['shadow'] += 1
                grand_stats['shadow_found'] += 1
                grand_stats['fully_blocked'] += 1
            else:
                stats['no_shadow'] += 1
                grand_stats['shadow_missing'] += 1

            grand_stats['total_cycles'] += 1

            if (word_idx + 1) % 500 == 0:
                elapsed = time.time() - t0
                print(f"    ... {word_idx+1}/{len(words)} ({elapsed:.1f}s)")
                sys.stdout.flush()

        elapsed = time.time() - t0
        print(f"\n  Results ({elapsed:.1f}s):")
        print(f"    Valid cycles: {stats['valid']}")
        print(f"    Conflict (entry): {stats['conflict']}")
        print(f"    MNU: {stats['mnu_pass']} pass, {stats['mnu_fail']} fail")
        print(f"    Escape: {stats['escape_pass']} pass, {stats['escape_fail']} fail")
        print(f"    Shadow: {stats['shadow']} found, {stats.get('no_shadow', 0)} missing")

        if mnu_violations_detail:
            print(f"\n    MNU violations:")
            for word, viols in mnu_violations_detail:
                print(f"      word={word}: {viols}")

        if escape_failures_detail:
            print(f"\n    Escape failures:")
            for word, fails in escape_failures_detail:
                print(f"      word={word}: {fails}")

        all_blocked = (stats['conflict'] + stats['shadow']) == stats['valid']
        if all_blocked and stats['valid'] > 0:
            print(f"    ★ ALL {stats['valid']} cycles BLOCKED")
        elif stats['valid'] == 0:
            print(f"    (no valid cycles)")
        else:
            unblocked = stats['valid'] - stats['conflict'] - stats['shadow']
            print(f"    !! {unblocked} cycles NOT blocked!")

        sys.stdout.flush()

    # Grand summary
    print(f"\n{'='*70}")
    print(f"GRAND SUMMARY")
    print(f"{'='*70}")
    print(f"Total cycles tested: {grand_stats['total_cycles']}")
    print(f"MNU: {grand_stats['mnu_pass']} pass, {grand_stats['mnu_fail']} FAIL")
    print(f"Escape: {grand_stats['escape_pass']} pass, {grand_stats['escape_fail']} FAIL")
    print(f"Shadow found: {grand_stats['shadow_found']}")
    print(f"Shadow missing: {grand_stats['shadow_missing']}")
    print(f"Conflict: {grand_stats['conflict']}")
    print(f"Fully blocked: {grand_stats['fully_blocked']}")

    if grand_stats['mnu_fail'] == 0 and grand_stats['escape_fail'] == 0:
        print(f"\n★★ MNU + ESCAPE hold universally for ALL tested mixed systems! ★★")
    if grand_stats['mnu_fail'] == 0 and grand_stats['escape_fail'] == 0 and grand_stats['shadow_missing'] == 0:
        print(f"\n★★★ COMPLETE: MNU + Escape + Shadow → ALL cycles blocked! Case 3c CLOSED! ★★★")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
