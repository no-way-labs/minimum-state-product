"""
Provider existence proof via walk reversal structure.

Theorem: In a zero-winding good cycle with cwStepCount > 0, no safe processor,
sub-threshold product, >=3 non-consecutive binary, n >= 9, all fc >= 2, and
some proc q with fc(q) >= 3:

There exists a proc t and a TernaryPhase at t where:
- One neighbor of t fires 0 times in the phase (silent side)
- The other neighbor of t is binary with even fire count >= 2 (active side)

APPROACH: Walk reversal + arc decomposition.

The mover word W = (w_0, w_1, ..., w_{L-1}) is a closed walk on Z_n (the ring).
Zero winding with cw > 0 means the walk has both CW and CCW steps, with net
displacement 0.

Key definitions:
- A REVERSAL at step i means the walk changes direction:
  w_{i-1} -> w_i goes one way, w_i -> w_{i+1} goes the other.
  Equivalently, w_{i+1} = w_{i-1} (the walk bounces).
- An EXCURSION from proc p is a maximal contiguous segment of the walk
  between two consecutive firings of p.
- A ONE-SIDED EXCURSION stays entirely on one side of p on the ring.

THE PROOF:

Lemma 1 (Reversal decomposition): A zero-winding walk with cw > 0 decomposes
into alternating CW and CCW ARCS. Each arc is a monotone traversal of
consecutive ring positions. Between consecutive arcs is a reversal point.

Lemma 2 (Reversal creates one-sided phase): At a reversal point r, the walk
visits r, goes into an arc on one side, returns to r. If the arc is small
enough (doesn't wrap around), the entire excursion stays on one side of r.

Lemma 3 (Binary reversal gives provider): If the reversal is AT or ADJACENT TO
a binary proc b, then between b's consecutive firings that bracket the
excursion:
  - b fires (enters excursion), walk goes to one side, returns, b fires (exits)
  - The neighbor on the excursion side fires >= 0 times
  - The neighbor on the NON-excursion side fires 0 times (walk never reaches it)
  This is the provider: t = neighbor on non-excursion side, with b as the
  active binary neighbor and the other neighbor as silent.

Lemma 4 (Some reversal involves binary): With >= 3 binary procs on the ring
and reversals distributed around the ring, at least one reversal point is
adjacent to a binary proc. (Pigeonhole: >= 2 reversals, >= 3 binary on ring
of n >= 9, binary are non-consecutive so they're spread out.)

Actually, the correct approach is simpler. Let me think again.

NEW APPROACH: Arc decomposition + ternary arc interior.

The walk decomposes into CW arcs and CCW arcs. Each arc traverses some
consecutive procs on the ring. Between binary procs there are TERNARY ARCS
(since binary are non-consecutive).

Key observation: Consider any two consecutive firings of the SAME binary proc b.
Between these two firings, the walk starts at b, goes somewhere, comes back to b.
This is an excursion.

Claim: With >= 3 non-consecutive binary and some fc >= 3, there exists a binary
proc b and two consecutive firings of b such that the excursion between them
stays entirely on one side.

Why? If b fires >= 4 times, it has >= 3 excursions. Each excursion goes either
left or right from b. So either >= 2 go left or >= 2 go right.

But actually, even for b with fc=2: the two firings partition the cycle into
two excursions. Zero winding means one goes CW and one goes CCW. Under ZW, if
both excursions visit ALL procs, the walk wraps around twice — but sub-threshold
product limits the total cycle length, making this impossible for n >= 9.

Let me just verify computationally first.
"""

import itertools
from collections import defaultdict


def is_sub_threshold(ms):
    """Product < 4 * 3^(n-2)"""
    n = len(ms)
    prod = 1
    for m in ms:
        prod *= m
    return prod < 4 * (3 ** (n - 2))


def has_ge3_binary(ms):
    return sum(1 for m in ms if m == 2) >= 3


def binary_non_consecutive(ms):
    """Check that no 3 consecutive are all binary."""
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def enumerate_good_cycles(ms, fs):
    """Find all good cycles for a given system."""
    from verifier import all_configs, privileged_set, apply_move

    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    # Find good configs (exactly 1 privileged)
    good_configs = set()
    for c in configs:
        if len(priv_map[c]) == 1:
            good_configs.add(c)

    if not good_configs:
        return []

    # Build good-config successor graph
    succ = {}
    for c in good_configs:
        priv = priv_map[c]
        assert len(priv) == 1
        p = priv[0]
        c2 = apply_move(c, p, fs, ms)
        if c2 in good_configs:
            succ[c] = (c2, p)

    # Find the cycle (should be unique in a valid system)
    if not succ:
        return []

    start = next(iter(succ))
    visited = []
    current = start
    seen = set()
    while current not in seen:
        seen.add(current)
        if current not in succ:
            return []
        c2, p = succ[current]
        visited.append((current, p))
        current = c2

    # Find the cycle
    cycle_start = current
    cycle = []
    found = False
    for i, (c, p) in enumerate(visited):
        if c == cycle_start:
            found = True
        if found:
            cycle.append((c, p))
            if len(cycle) > 1 and c == cycle_start:
                break

    # Trim: cycle should end when we return to start
    # Actually, rebuild properly
    cycle = []
    current = cycle_start
    while True:
        c2, p = succ[current]
        cycle.append((current, p))
        current = c2
        if current == cycle_start:
            break

    return [cycle]


def analyze_walk(cycle, ms):
    """Analyze a good cycle's walk properties."""
    n = len(ms)
    L = len(cycle)

    # Mover word
    movers = [p for (c, p) in cycle]

    # Fire counts
    fc = [0] * n
    for m in movers:
        fc[m] += 1

    # Winding: displacement at each step
    # CW step: mover[i+1] = mover[i] + 1 mod n
    # CCW step: mover[i+1] = mover[i] - 1 mod n
    cw_count = 0
    ccw_count = 0
    stay_count = 0
    total_disp = 0
    for i in range(L):
        curr = movers[i]
        nxt = movers[(i + 1) % L]
        diff = (nxt - curr) % n
        if diff == 1:
            cw_count += 1
            total_disp += 1
        elif diff == n - 1:
            ccw_count += 1
            total_disp -= 1
        else:
            stay_count += 1  # Jump (shouldn't happen in proper walk)

    zero_winding = (total_disp % n == 0) and (abs(total_disp) < 2 * n)

    # Safe processor check
    has_safe = False
    fired_or_neighbor = set()
    for m in movers:
        fired_or_neighbor.add(m)
        fired_or_neighbor.add((m - 1) % n)
        fired_or_neighbor.add((m + 1) % n)
    has_safe = len(fired_or_neighbor) < n

    return {
        'movers': movers,
        'fc': fc,
        'cw': cw_count,
        'ccw': ccw_count,
        'stay': stay_count,
        'total_disp': total_disp,
        'zero_winding': zero_winding,
        'has_safe': has_safe,
        'L': L,
    }


def find_ternary_phases(movers, ms, n):
    """Find all TernaryPhase instances for each proc."""
    L = len(movers)
    phases = []

    for t in range(n):
        # Find all steps where t fires
        fire_steps = [i for i in range(L) if movers[i] == t]
        if len(fire_steps) < 1:
            continue

        # For each firing step s, find the latest a < s where t is not mover
        for s in fire_steps:
            # Find all non-mover steps before s
            for a in range(s - 1, -1, -1):
                if movers[a] != t:
                    # Check t doesn't fire in (a, s)
                    no_fire = all(movers[k] != t for k in range(a + 1, s))
                    if no_fire:
                        phases.append((t, a, s))
                    break

    return phases


def check_provider_exists(movers, ms, n):
    """Check if a provider TernaryPhase exists.

    A provider is a proc t and phase (a, s) where:
    - One neighbor fires 0 times in [a, s) (silent side)
    - Other neighbor is binary with even fire count >= 2 in [a, s) (active side)
    """
    L = len(movers)
    phases = find_ternary_phases(movers, ms, n)

    for (t, a, s) in phases:
        left_t = (t - 1) % n
        right_t = (t + 1) % n

        # Count fires in [a, s)
        left_fires = sum(1 for k in range(a, s) if movers[k] == left_t)
        right_fires = sum(1 for k in range(a, s) if movers[k] == right_t)

        # Check: left silent, right active binary even >= 2
        if left_fires == 0 and ms[right_t] == 2 and right_fires >= 2 and right_fires % 2 == 0:
            return True, (t, a, s, 'left_silent', right_fires)

        # Check: right silent, left active binary even >= 2
        if right_fires == 0 and ms[left_t] == 2 and left_fires >= 2 and left_fires % 2 == 0:
            return True, (t, a, s, 'right_silent', left_fires)

    return False, None


def generate_all_mover_words(n, L, ring_walk=True):
    """Generate all valid mover words of length L on ring Z_n.

    If ring_walk=True, consecutive movers must be adjacent (differ by +-1 mod n).
    """
    if L == 0:
        yield []
        return

    for start in range(n):
        yield from _extend_word([start], n, L, ring_walk)


def _extend_word(word, n, L, ring_walk):
    if len(word) == L:
        yield word[:]
        return

    last = word[-1]
    if ring_walk:
        # Next must be adjacent
        for nxt in [(last - 1) % n, last, (last + 1) % n]:
            word.append(nxt)
            yield from _extend_word(word, n, L, ring_walk)
            word.pop()
    else:
        for nxt in range(n):
            word.append(nxt)
            yield from _extend_word(word, n, L, ring_walk)
            word.pop()


def exhaustive_check_small():
    """Exhaustive check at small n with specific ms vectors."""

    # Test at n=5 with ms = (2, 3, 2, 3, 2) — 3 non-consecutive binary
    # Sub-threshold: product = 72 < 4*27 = 108
    test_cases = [
        # (n, ms, description)
        (5, [2, 3, 2, 3, 2], "3 non-consec binary, n=5"),
        (5, [2, 3, 3, 2, 3], "2 non-consec binary (not enough)"),
    ]

    # Instead of exhaustive word generation (too slow for large L),
    # use the structure: zero-winding walks with specific fc constraints

    # Approach: enumerate walk words directly for small cycle lengths

    for n, ms, desc in test_cases:
        if not has_ge3_binary(ms) or not binary_non_consecutive(ms):
            print(f"Skipping {desc}: doesn't meet binary criteria")
            continue

        if not is_sub_threshold(ms):
            print(f"Skipping {desc}: not sub-threshold")
            continue

        print(f"\n=== {desc}: n={n}, ms={ms} ===")

        # Try cycle lengths from 2n to 3n
        for L in range(2 * n, 3 * n + 1):
            found_any = False
            counter_examples = 0
            total_valid = 0

            for word in generate_all_mover_words(n, L, ring_walk=True):
                # Check zero winding
                disp = 0
                cw = 0
                for i in range(L):
                    nxt = word[(i + 1) % L]
                    diff = (nxt - word[i]) % n
                    if diff == 1:
                        disp += 1
                        cw += 1
                    elif diff == n - 1:
                        disp -= 1

                if disp != 0:
                    continue
                if cw == 0:
                    continue

                # Check fc >= 2 for all
                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if any(f < 2 for f in fc):
                    continue

                # Check some fc >= 3
                if max(fc) < 3:
                    continue

                # Check no safe proc
                touched = set()
                for m in word:
                    touched.add(m)
                    touched.add((m - 1) % n)
                    touched.add((m + 1) % n)
                if len(touched) < n:
                    continue

                total_valid += 1

                # Check provider exists
                found, info = check_provider_exists(word, ms, n)
                if not found:
                    counter_examples += 1
                    if counter_examples <= 3:
                        print(f"  COUNTER-EXAMPLE at L={L}: word={word}, fc={fc}")

            if total_valid > 0:
                print(f"  L={L}: {total_valid} valid walks, {counter_examples} without provider")


def focused_reversal_check():
    """Check the reversal-based provider argument.

    In a ZW walk with cw > 0, there are reversals. At each reversal,
    the walk bounces. We check whether reversals create providers.
    """
    print("\n=== Reversal-based provider check ===")

    # n=5, ms=(2,3,2,3,2): binary at 0,2,4 (non-consecutive)
    n = 5
    ms = [2, 3, 2, 3, 2]

    # Generate ZW walks with cw > 0, all fc >= 2, some fc >= 3
    total = 0
    provider_found = 0
    reversal_provider = 0

    for L in range(2 * n, 4 * n + 1):
        for word in generate_all_mover_words(n, L, ring_walk=True):
            # Closing condition: word must be a cycle (last -> first adjacent)
            first = word[0]
            last = word[-1]
            if abs((first - last) % n) != 1 and abs((first - last) % n) != n - 1 and first != last:
                continue

            # Zero winding check
            disp = 0
            cw = 0
            for i in range(L):
                nxt = word[(i + 1) % L]
                diff = (nxt - word[i]) % n
                if diff == 1:
                    disp += 1
                    cw += 1
                elif diff == n - 1:
                    disp -= 1

            if disp != 0 or cw == 0:
                continue

            fc = [0] * n
            for m in word:
                fc[m] += 1
            if any(f < 2 for f in fc):
                continue
            if max(fc) < 3:
                continue

            touched = set()
            for m in word:
                touched.add(m)
                touched.add((m - 1) % n)
                touched.add((m + 1) % n)
            if len(touched) < n:
                continue

            total += 1

            found, info = check_provider_exists(word, ms, n)
            if found:
                provider_found += 1
            else:
                print(f"  NO PROVIDER: L={L}, word={word}, fc={fc}")

    print(f"Total valid ZW walks: {total}")
    print(f"Provider found: {provider_found}")
    print(f"Missing: {total - provider_found}")


def smart_reversal_analysis():
    """Analyze reversal structure in ZW walks.

    For each ZW walk, identify:
    1. Reversal points (direction changes)
    2. Excursions from each binary proc
    3. Whether any excursion is one-sided
    """
    print("\n=== Smart reversal analysis ===")

    n = 5
    ms = [2, 3, 2, 3, 2]
    binary_procs = [i for i in range(n) if ms[i] == 2]

    total = 0
    has_one_sided = 0
    provider_from_one_sided = 0

    for L in range(2 * n, 3 * n + 1):
        for word in generate_all_mover_words(n, L, ring_walk=True):
            # ZW with cw > 0
            disp = 0
            cw = 0
            for i in range(L):
                nxt = word[(i + 1) % L]
                diff = (nxt - word[i]) % n
                if diff == 1:
                    disp += 1
                    cw += 1
                elif diff == n - 1:
                    disp -= 1
            if disp != 0 or cw == 0:
                continue

            fc = [0] * n
            for m in word:
                fc[m] += 1
            if any(f < 2 for f in fc):
                continue
            if max(fc) < 3:
                continue

            touched = set()
            for m in word:
                touched.add(m)
                touched.add((m-1)%n)
                touched.add((m+1)%n)
            if len(touched) < n:
                continue

            total += 1

            # Find excursions from each binary proc
            found_one_sided_excursion = False
            for b in binary_procs:
                fire_steps = [i for i in range(L) if word[i] == b]
                if len(fire_steps) < 2:
                    continue

                # Check each pair of consecutive firings
                for idx in range(len(fire_steps)):
                    s1 = fire_steps[idx]
                    s2 = fire_steps[(idx + 1) % len(fire_steps)]

                    if s2 <= s1:
                        s2 += L  # wrap around

                    # Excursion: steps s1+1 to s2-1
                    excursion = []
                    for k in range(s1 + 1, s2):
                        excursion.append(word[k % L])

                    if not excursion:
                        continue

                    # Check one-sided: all procs in excursion on one side of b
                    left_side = set()
                    right_side = set()
                    # CW from b: b+1, b+2, ..., up to half ring
                    for d in range(1, n):
                        p = (b + d) % n
                        right_side.add(p)
                    for d in range(1, n):
                        p = (b - d) % n
                        left_side.add(p)

                    exc_set = set(excursion)

                    if exc_set <= left_side:
                        found_one_sided_excursion = True
                        # Check if this creates a provider
                        # The excursion goes left from b
                        # right neighbor of b = (b+1)%n doesn't fire
                        t = (b + 1) % n  # neighbor on non-excursion side
                        # t's phase: between s1 and s2, t doesn't fire
                        t_fires_in_exc = sum(1 for p in excursion if p == t)
                        # Actually t IS on the non-excursion side, so it shouldn't fire
                        # unless the excursion includes it... check
                        if t not in exc_set:
                            # t doesn't fire in excursion.
                            # Now check: is this a valid TernaryPhase for some proc?
                            pass

                    if exc_set <= right_side:
                        found_one_sided_excursion = True

            if found_one_sided_excursion:
                has_one_sided += 1

            # Also check provider
            found, _ = check_provider_exists(word, ms, n)
            if found:
                provider_from_one_sided += 1

    print(f"Total valid walks: {total}")
    print(f"Has one-sided excursion: {has_one_sided}")
    print(f"Provider found: {provider_from_one_sided}")


if __name__ == "__main__":
    import sys
    sys.path.insert(0, './claude')

    # Quick sanity check
    print("=== Provider existence verification ===")
    exhaustive_check_small()
