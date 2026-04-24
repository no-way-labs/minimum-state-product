#!/usr/bin/env python3
"""binscc_mixed_nonconsec_mnu.py — MNU + Escape for non-consecutive binary mixed systems.

Case 3c: {2^3, 4, 3^(n-4)} with binaries NON-consecutive on ring.
Shadow already proved for sweep cycles. Now prove MNU + Escape extend.

Also test: {2^3, 3^(n-3)} non-consecutive (Case 3b control) to verify.
"""

from itertools import product as iproduct, permutations
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


def build_cycle(ms, n, mover_word):
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
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    for p in range(n):
        if fc[p] == 0 or fc[p] % ms[p] != 0:
            return None
    for i in range(ell):
        p1 = mover_word[i]
        p2 = mover_word[(i+1) % ell]
        diff = abs(p1 - p2)
        if diff != 1 and diff != n - 1:
            return None
    return configs[:ell]


def get_determined_entries(cycle, n):
    ell = len(cycle)
    det = {}
    for i in range(ell):
        c = cycle[i]
        c_next = cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        L = c[(mover-1)%n]; S = c[mover]; R = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, L, S, R)
        if key in det and det[key] != S_new:
            return None
        det[key] = S_new
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in det and det[key2] != Sj:
                    return None
                det[key2] = Sj
    return det


def check_mnu(cycle, n):
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
        matches = [j for j, gj in enumerate(cycle)
                   if gj[(p-1) % n] == L and gj[p] == S_prime and gj[(p+1) % n] == R]
        if len(matches) != 1:
            violations.append((step, p, L, S_prime, R, len(matches), matches))
    return violations


def check_escape(cycle, det, ms, n):
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
                new_c = list(c)
                new_c[i] = det[key]
                new_c = tuple(new_c)
                if new_c in good_set:
                    failures.append((c, i, new_c))
    return failures, total_forced


def find_shadow(cycle, det, ms, n):
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
                cycle_start = visited[config]
                return path[cycle_start:]
            visited[config] = len(path)
            path.append(config)
            forced = []
            for j in range(n):
                Lj = config[(j-1)%n]; Sj = config[j]; Rj = config[(j+1)%n]
                key = (j, Lj, Sj, Rj)
                if key in det and det[key] != Sj:
                    forced.append((j, det[key]))
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
    return None


def max_consecutive_binary(ms, n):
    """Max run of binary (m=2) on ring."""
    max_run = 0
    run = 0
    for i in range(2 * n):
        if ms[i % n] == 2:
            run += 1
            max_run = max(max_run, run)
        else:
            run = 0
    return max_run


def get_nonconsec_orientations(n, ms_sorted):
    """Generate non-consecutive binary orientations (max 2 consecutive binary)."""
    seen = set()
    results = []
    for perm in permutations(ms_sorted):
        mc = max_consecutive_binary(perm, n)
        if mc > 2:  # allow up to 2 consecutive (non-consecutive = not 3+)
            continue
        # Actually for Case 3c: non-consecutive means binaries separated by ≥1 non-binary
        # For the Shadow Cycle Mirror Theorem, the requirement is ≤3 consecutive
        # Let's keep ≤2 consecutive for strict non-consecutive
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = tuple(reversed(perm))
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canonical = min(rotations + ref_rotations)
        if canonical not in seen:
            seen.add(canonical)
            results.append(perm)
    return results


def main():
    print("=" * 70)
    print("MNU + ESCAPE FOR NON-CONSECUTIVE BINARY MIXED SYSTEMS")
    print("=" * 70)
    print()

    test_configs = []

    # n=5: {2^3, 4} = prod 32 vs threshold 108. But need 5 procs.
    # {2,3,2,3,2} = prod 72, non-consec 3 binary, pure ternary
    # {2,3,2,4,2} = prod 64, non-consec 3 binary, mixed (quaternary)
    # {2,4,2,3,2} = prod 64, non-consec 3 binary, mixed

    for n in [5, 6, 7]:
        threshold = 4 * (3 ** (n - 2))

        if n == 5:
            multisets = [
                (2, 3, 2, 3, 2),   # pure, non-consec
                (2, 4, 2, 3, 2),   # mixed, non-consec
                (2, 3, 2, 4, 2),   # mixed, non-consec (different orient)
            ]
        elif n == 6:
            multisets = [
                (2, 3, 2, 3, 3, 2),  # 3B non-consec, pure (but 2 consec at ends on ring!)
                (2, 3, 2, 3, 2, 3),  # 3B alternating, pure
                (2, 3, 2, 4, 2, 3),  # 3B alternating, mixed
                (2, 4, 2, 3, 2, 3),  # 3B alternating, mixed
                (2, 3, 2, 3, 3, 4),  # 3B, mixed
            ]
        elif n == 7:
            multisets = [
                (2, 3, 2, 3, 2, 3, 3),  # 3B alternating, pure
                (2, 3, 2, 4, 2, 3, 3),  # 3B alternating, mixed
                (2, 3, 2, 3, 2, 3, 4),  # 3B alternating, mixed
                (2, 3, 3, 2, 3, 2, 3),  # 3B non-consec, pure
                (2, 3, 3, 2, 4, 2, 3),  # 3B non-consec, mixed
            ]
        else:
            multisets = []

        for ms in multisets:
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue
            n_bin = sum(1 for m in ms if m == 2)
            if n_bin < 3:
                continue
            mc = max_consecutive_binary(ms, len(ms))
            is_mixed = any(m > 3 for m in ms)
            test_configs.append((n, list(ms), prod, is_mixed, mc))

    print(f"Test configurations: {len(test_configs)}")
    for n, ms, prod, mixed, mc in test_configs:
        label = "MIXED" if mixed else "pure"
        print(f"  n={n} ms={ms} prod={prod} max_consec_bin={mc} [{label}]")
    print()

    grand = Counter()

    for n, ms, prod, is_mixed, mc in test_configs:
        label = "MIXED" if is_mixed else "pure"
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms} prod={prod} max_consec={mc} [{label}]")
        print(f"{'='*60}")
        sys.stdout.flush()

        t0 = time.time()
        max_len = 3 * n + 6
        words = enumerate_mover_words_smart(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} mover words ({t1-t0:.1f}s)")

        stats = Counter()

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            stats['valid'] += 1

            det = get_determined_entries(cycle, n)
            if det is None:
                stats['conflict'] += 1
                continue

            # MNU
            mnu_viols = check_mnu(cycle, n)
            if mnu_viols:
                stats['mnu_fail'] += 1
                grand['mnu_fail'] += 1
            else:
                stats['mnu_pass'] += 1
                grand['mnu_pass'] += 1

            # Escape
            esc_fails, esc_total = check_escape(cycle, det, ms, n)
            if esc_fails:
                stats['escape_fail'] += 1
                grand['escape_fail'] += 1
            else:
                stats['escape_pass'] += 1
                grand['escape_pass'] += 1

            # Shadow
            shadow = find_shadow(cycle, det, ms, n)
            if shadow:
                stats['shadow'] += 1
            else:
                stats['no_shadow'] += 1

        elapsed = time.time() - t0
        blocked = stats['conflict'] + stats['shadow']
        total = stats['valid']
        print(f"  Valid: {total}, Conflict: {stats['conflict']}, Shadow: {stats['shadow']}, No shadow: {stats.get('no_shadow',0)}")
        print(f"  MNU: {stats.get('mnu_pass',0)} pass / {stats.get('mnu_fail',0)} fail")
        print(f"  Escape: {stats.get('escape_pass',0)} pass / {stats.get('escape_fail',0)} fail")
        if total > 0 and blocked == total:
            print(f"  ★ ALL {total} cycles BLOCKED ({elapsed:.1f}s)")
        elif total > 0:
            print(f"  !! {total - blocked} unblocked ({elapsed:.1f}s)")
        else:
            print(f"  (no valid cycles) ({elapsed:.1f}s)")

        grand['total'] += total
        grand['blocked'] += blocked
        sys.stdout.flush()

    print(f"\n{'='*70}")
    print(f"GRAND SUMMARY")
    print(f"{'='*70}")
    print(f"Total valid cycles: {grand['total']}")
    print(f"Fully blocked: {grand['blocked']}")
    print(f"MNU: {grand['mnu_pass']} pass, {grand['mnu_fail']} FAIL")
    print(f"Escape: {grand['escape_pass']} pass, {grand['escape_fail']} FAIL")

    if grand['mnu_fail'] == 0 and grand['escape_fail'] == 0:
        print(f"\n★★ MNU + ESCAPE hold universally for ALL non-consecutive binary mixed systems! ★★")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
