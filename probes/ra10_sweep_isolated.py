#!/usr/bin/env python3
"""
RA10: Investigate sweep cycles with isolated binary firings.

Goal: find a DIRECT proof that sweep + sub-threshold + ≥3 non-consecutive binary → False,
without recursion through binary_ring_impossibility.

Key properties of sweep cycles:
- |totalDisplacement| ≥ 2n (mover walk wraps ring ≥2 times)
- Every processor fires ≥ 2 times (from edgeNetFlow ≥ 2)
- Binary processors fire an even number of times (≥2)

"Isolated firings" at binary proc p means MinFiringGap ≥ 2:
between consecutive fires of p, the mover visits at least 2 other positions.

Investigation plan:
1. Enumerate sweep mover words at small n with ≥3 non-consecutive binary
2. Check which have valid good cycles (incrementing transition)
3. For those: check entry conflict — where, and via what mechanism?
4. Look for a direct argument from sweep structure.
"""
from collections import defaultdict
from itertools import product as iproduct
import time
import sys


def total_displacement(word, n):
    """Compute total displacement (signed) of mover walk on ring of size n."""
    disp = 0
    for i in range(len(word) - 1):
        diff = (word[i+1] - word[i]) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None  # not ring-adjacent
    # Close the cycle: last → first
    diff = (word[0] - word[-1]) % n
    if diff == 1:
        disp += 1
    elif diff == n - 1:
        disp -= 1
    else:
        return None
    return disp


def is_sweep(word, n):
    """Check if |totalDisplacement| ≥ 2n."""
    d = total_displacement(word, n)
    if d is None:
        return False
    return abs(d) >= 2 * n


def fire_counts(word, n):
    """Return fire count per processor."""
    fc = [0] * n
    for p in word:
        fc[p] += 1
    return fc


def min_firing_gap(word, p):
    """Minimum gap between consecutive firings of p in cyclic word.
    Gap = number of intervening steps (not counting the firing itself)."""
    positions = [i for i, x in enumerate(word) if x == p]
    if len(positions) < 2:
        return float('inf')
    L = len(word)
    min_gap = L  # worst case
    for i in range(len(positions)):
        j = (i + 1) % len(positions)
        if j == 0:
            gap = (positions[j] + L - positions[i]) - 1
        else:
            gap = positions[j] - positions[i] - 1
        min_gap = min(min_gap, gap)
    return min_gap


def check_good_cycle(word, ms, n):
    """Check if word gives valid good cycle with incrementing transition."""
    L = len(word)
    configs = [[0] * n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return False, None
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return False, None
    return True, configs[:L]


def find_entry_conflicts(word, ms, n, configs):
    """Find all entry conflicts. Return list of (processor, triple)."""
    L = len(word)
    conflicts = []
    for j in range(n):
        mt_triples = set()
        nmt_triples = set()
        for t in range(L):
            c = tuple(configs[t])
            triple = (c[(j - 1) % n], c[j], c[(j + 1) % n])
            if word[t] == j:
                mt_triples.add(triple)
            else:
                nmt_triples.add(triple)
        overlap = mt_triples & nmt_triples
        if overlap:
            conflicts.append((j, overlap))
    return conflicts


def binary_positions(ms):
    """Return set of positions with ms[p] == 2."""
    return {p for p, m in enumerate(ms) if m == 2}


def has_3_nonconsec_binary(ms, n):
    """Check if ≥3 binary processors, no 3 consecutive."""
    bins = binary_positions(ms)
    if len(bins) < 3:
        return False
    # Check no 3 consecutive
    for i in range(n):
        if i in bins and (i + 1) % n in bins and (i + 2) % n in bins:
            return False
    return True


def enumerate_sweep_words_dfs(n, ms, max_results=500, timeout=60):
    """Enumerate ring-adjacent mover words that are sweeps (|disp| ≥ 2n)."""
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout:
            return
        if len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                # Check ring-adjacency of closing step
                diff = (word[0] - word[-1]) % n
                if diff in (1, n - 1):
                    if is_sweep(word, n):
                        results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)

    return results


def canonicalize(word):
    """Canonical rotation of cyclic word."""
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def main():
    print("RA10: Sweep + Isolated Binary Firings Investigation")
    print("=" * 70)

    # Start small: n=5 with 3 non-consecutive binary
    # Sub-threshold for n=5: product < 4*3^3 = 108
    # ms with ≥3 binary, non-consecutive, product < 108:
    # e.g., [2,3,2,3,2] product=72, 3 binary at {0,2,4}, non-consecutive on ring of 5
    # But on n=5 ring: 0,2,4 — check: 0-1 gap 1, 2-3 gap 1, 4-0 gap 1. No 3 consecutive.

    test_cases = [
        # n=5: sub-threshold < 108
        (5, [2, 3, 2, 3, 2], "n=5, binary at {0,2,4}"),
        (5, [3, 2, 3, 2, 2], "n=5, binary at {1,3,4}"),  # 3,4 consecutive but no triple
        # n=6: sub-threshold < 324
        (6, [2, 3, 2, 3, 2, 3], "n=6, binary at {0,2,4}"),
        (6, [2, 3, 2, 3, 3, 2], "n=6, binary at {0,2,5}"),
        # n=7: sub-threshold < 972
        (7, [2, 3, 2, 3, 2, 3, 3], "n=7, binary at {0,2,4}"),
        (7, [2, 3, 2, 3, 3, 2, 3], "n=7, binary at {0,2,5}"),
    ]

    for n, ms, label in test_cases:
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * (3 ** (n - 2))
        bins = binary_positions(ms)
        print(f"\n{'='*70}")
        print(f"{label}")
        print(f"  ms={ms}, product={product}, threshold={threshold}, sub={product < threshold}")
        print(f"  Binary at: {sorted(bins)}")
        print(f"  3 non-consec: {has_3_nonconsec_binary(ms, n)}")
        print(f"  CL={sum(ms)}")

        if product >= threshold:
            print(f"  SKIP: not sub-threshold")
            continue

        t0 = time.time()
        words = enumerate_sweep_words_dfs(n, ms, max_results=2000, timeout=30)
        t1 = time.time()

        # Deduplicate
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        print(f"  Found {len(unique)} unique sweep words in {t1-t0:.1f}s")

        if not unique:
            print(f"  >>> NO SWEEP WORDS EXIST — structural impossibility?")
            continue

        n_valid = 0
        n_ec = 0
        n_iso = 0  # isolated binary firings
        ec_at_binary = 0
        ec_at_nonbinary = 0
        ec_details = []

        for w in unique.values():
            ok, configs = check_good_cycle(list(w), ms, n)
            if not ok:
                continue
            n_valid += 1

            # Check isolated firings at binary processors
            has_isolated = False
            for p in bins:
                gap = min_firing_gap(list(w), p)
                fc_p = fire_counts(list(w), n)[p]
                if fc_p >= 2 and gap >= 2:
                    has_isolated = True
                    break

            if has_isolated:
                n_iso += 1

            # Check entry conflict
            ecs = find_entry_conflicts(list(w), ms, n, configs)
            if ecs:
                n_ec += 1
                for proc, triples in ecs:
                    if proc in bins:
                        ec_at_binary += 1
                    else:
                        ec_at_nonbinary += 1
                if n_valid <= 5:
                    disp = total_displacement(list(w), n)
                    ec_details.append((list(w), disp, ecs, has_isolated))

        print(f"  Valid good cycles: {n_valid}")
        if n_valid > 0:
            print(f"  With isolated binary firings: {n_iso}/{n_valid}")
            print(f"  With entry conflict: {n_ec}/{n_valid}")
            print(f"  EC at binary proc: {ec_at_binary}")
            print(f"  EC at non-binary: {ec_at_nonbinary}")
            if n_ec < n_valid:
                print(f"  *** WARNING: {n_valid - n_ec} CONFLICT-FREE sweep cycles! ***")
            else:
                print(f"  >>> ALL have EC <<<")

        for w, disp, ecs, iso in ec_details[:3]:
            print(f"\n  Example: word={w[:20]}... disp={disp}, isolated={iso}")
            for proc, triples in ecs[:2]:
                print(f"    EC at proc {proc} (binary={proc in bins}): {list(triples)[:2]}")

    print(f"\n{'='*70}")
    print("PHASE 2: Direct argument analysis")
    print("="*70)

    # For each sweep cycle found, analyze the structure more deeply:
    # Can we show EC from just: sweep + binary + fc≥2?
    # Key insight: sweep means the walk wraps ≥2 times.
    # At a binary proc p with fc(p) = 2 (minimum for binary in sweep):
    # the mover fires at p exactly twice. Between these two firings,
    # the mover walks away and comes back (gap ≥ 1).
    #
    # For isolated (gap ≥ 2): mover fires p, moves away, visits at least
    # 2 other procs, then fires p again.
    #
    # The boundary triple at p is (c[left(p)], c[p], c[right(p)]).
    # At first firing: triple is T1. After firing: c[p] flips (binary).
    # At second firing: triple is T2. After firing: c[p] flips back.
    #
    # Between the two firings, p is a non-mover. The triple at p changes
    # as left(p) and right(p) fire (if they do between the two firings of p).
    #
    # For EC at p: we need some T appearing as both mover and non-mover triple.

    # Let's check: for isolated binary firings, what's the relationship
    # between the two mover triples?

    print("\nPHASE 2a: Mover triple analysis at isolated binary procs")
    print("-" * 60)

    for n, ms, label in test_cases:
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * (3 ** (n - 2))
        if product >= threshold:
            continue

        bins = binary_positions(ms)
        words = enumerate_sweep_words_dfs(n, ms, max_results=500, timeout=15)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        found_any = False
        for w in unique.values():
            ok, configs = check_good_cycle(list(w), ms, n)
            if not ok:
                continue
            if not found_any:
                print(f"\n{label}")
                found_any = True

            wl = list(w)
            L = len(wl)
            disp = total_displacement(wl, n)

            for p in sorted(bins):
                fc_p = fire_counts(wl, n)[p]
                gap = min_firing_gap(wl, p)
                if fc_p < 2:
                    continue

                # Find firing positions of p
                fire_pos = [i for i, x in enumerate(wl) if x == p]

                # Get mover triples at each firing
                mover_triples = []
                for t in fire_pos:
                    c = tuple(configs[t])
                    triple = (c[(p - 1) % n], c[p], c[(p + 1) % n])
                    mover_triples.append(triple)

                # Get non-mover triples at p (all steps where p is not mover)
                nm_triples = set()
                for t in range(L):
                    if wl[t] != p:
                        c = tuple(configs[t])
                        triple = (c[(p - 1) % n], c[p], c[(p + 1) % n])
                        nm_triples.add(triple)

                # Check overlap
                m_set = set(mover_triples)
                overlap = m_set & nm_triples

                if not found_any or fc_p == 2:
                    print(f"  p={p} fc={fc_p} gap={gap} "
                          f"mover_triples={mover_triples} "
                          f"overlap={'YES' if overlap else 'no'}")

            if found_any:
                break  # just show first example

    print(f"\n{'='*70}")
    print("PHASE 3: Sweep structure — can sweep alone force EC?")
    print("=" * 70)
    print("""
Key observation about sweep cycles (|disp| ≥ 2n):
The mover walk wraps around the ring ≥2 complete times.

For a binary proc p with fc(p)=2 in a sweep with disp=2n:
- The walk goes CW around the ring twice (all same direction for uniform sweep)
- p fires once in the first wrap, once in the second
- Between the two firings: the walk traverses every processor at least once
  (since it makes a full wrap)
- So left(p) and right(p) both fire between p's firings

Now: at p's first firing, the mover triple is (L1, S1, R1).
After firing: c[p] flips: (L1, 1-S1, R1).
Then left(p) fires at some point, changing L. Right(p) fires, changing R.
Eventually p fires again with triple (L2, S2, R2).
Since c[p] was flipped once (by p's first fire) and not fired again
(fc(p)=2, this is the second fire), S2 = 1-S1.

After p's second fire: c[p] = 1-(1-S1) = S1. Restored.

The question is whether some triple (L, S, R) seen as non-mover
matches one of the two mover triples (L1, S1, R1) or (L2, 1-S1, R2).
""")

    # Deep analysis: for each binary proc in sweep, track the full
    # triple trajectory
    print("PHASE 3a: Triple trajectory at binary proc in sweep")
    print("-" * 60)

    for n, ms, label in [(5, [2, 3, 2, 3, 2], "n=5")]:
        bins = binary_positions(ms)
        words = enumerate_sweep_words_dfs(n, ms, max_results=100, timeout=10)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        count = 0
        for w in unique.values():
            ok, configs = check_good_cycle(list(w), ms, n)
            if not ok:
                continue
            count += 1
            if count > 3:
                break

            wl = list(w)
            L = len(wl)
            disp = total_displacement(wl, n)
            print(f"\n  word={wl}, disp={disp}")

            for p in sorted(bins):
                triples_over_time = []
                for t in range(L):
                    c = tuple(configs[t])
                    triple = (c[(p - 1) % n], c[p], c[(p + 1) % n])
                    is_mover = (wl[t] == p)
                    triples_over_time.append((t, wl[t], triple, is_mover))

                fire_pos = [i for i, x in enumerate(wl) if x == p]
                print(f"  proc {p} (binary, fc={len(fire_pos)}, gap={min_firing_gap(wl, p)}):")
                for t, mover, triple, is_m in triples_over_time:
                    marker = " <<< MOVER" if is_m else ""
                    print(f"    t={t:2d} mover={mover} triple={triple}{marker}")

    # PHASE 4: The big question — do ALL sweep cycles with ≥3 non-consec binary
    # have entry conflicts, even without the isolated firings condition?
    print(f"\n{'='*70}")
    print("PHASE 4: Universal EC for sweep + ≥3 non-consec binary")
    print("=" * 70)

    total_sweep = 0
    total_ec = 0
    total_no_ec = 0

    for n, ms, label in test_cases:
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * (3 ** (n - 2))
        if product >= threshold:
            continue
        if not has_3_nonconsec_binary(ms, n):
            continue

        bins = binary_positions(ms)
        words = enumerate_sweep_words_dfs(n, ms, max_results=2000, timeout=30)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        n_valid = 0
        n_ec = 0
        for w in unique.values():
            ok, configs = check_good_cycle(list(w), ms, n)
            if not ok:
                continue
            n_valid += 1
            ecs = find_entry_conflicts(list(w), ms, n, configs)
            if ecs:
                n_ec += 1
            else:
                print(f"  NO EC: {label}, word={list(w)[:20]}...")

        total_sweep += n_valid
        total_ec += n_ec
        total_no_ec += n_valid - n_ec
        if n_valid > 0:
            print(f"  {label}: {n_ec}/{n_valid} have EC")

    print(f"\nGrand total: {total_ec}/{total_sweep} sweep cycles have EC")
    if total_no_ec == 0:
        print(">>> ALL sweep cycles have entry conflict! <<<")
    else:
        print(f"*** {total_no_ec} sweep cycles WITHOUT entry conflict ***")

    # PHASE 5: Check with non-incrementing transitions too
    print(f"\n{'='*70}")
    print("PHASE 5: Non-incrementing transitions at ternary procs")
    print("=" * 70)
    print("For binary procs: only inc (0→1→0) makes sense with fc=2.")
    print("For ternary procs: inc (0→1→2→0) or dec (0→2→1→0).")
    print("Checking all combinations...")

    for n, ms, label in [(5, [2, 3, 2, 3, 2], "n=5 [2,3,2,3,2]")]:
        bins = binary_positions(ms)
        ternary = [p for p in range(n) if ms[p] == 3]
        n_tern = len(ternary)

        words = enumerate_sweep_words_dfs(n, ms, max_results=500, timeout=15)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        print(f"\n{label}: {len(unique)} unique sweep words, {n_tern} ternary procs")

        total_combos = 0
        total_valid = 0
        total_ec_count = 0

        for w in unique.values():
            wl = list(w)
            L = len(wl)

            # Try all 2^(n_tern) transition direction combos
            for trans_bits in range(1 << n_tern):
                # Build transition: 0=inc, 1=dec for each ternary
                trans = {}
                for idx, p in enumerate(ternary):
                    if (trans_bits >> idx) & 1:
                        trans[p] = 'dec'  # 0→2→1→0
                    else:
                        trans[p] = 'inc'  # 0→1→2→0
                for p in bins:
                    trans[p] = 'inc'  # binary: only inc

                # Build configs
                configs = [[0] * n]
                for t in range(L):
                    c = list(configs[-1])
                    p = wl[t]
                    if trans[p] == 'inc':
                        c[p] = (c[p] + 1) % ms[p]
                    else:
                        c[p] = (c[p] - 1) % ms[p]
                    configs.append(c)

                total_combos += 1

                if configs[-1] != configs[0]:
                    continue
                config_set = set(tuple(c) for c in configs[:L])
                if len(config_set) != L:
                    continue

                total_valid += 1

                # Check EC
                ecs = find_entry_conflicts(wl, ms, n, configs[:L])
                if ecs:
                    total_ec_count += 1
                else:
                    print(f"  NO EC: word={wl[:15]}... trans={trans}")

        print(f"  Combos checked: {total_combos}")
        print(f"  Valid good cycles: {total_valid}")
        print(f"  With EC: {total_ec_count}/{total_valid}")
        if total_ec_count == total_valid and total_valid > 0:
            print(f"  >>> ALL have EC (across all transition modes) <<<")


if __name__ == '__main__':
    main()
