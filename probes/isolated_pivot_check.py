#!/usr/bin/env python3
"""
Check: At n=9..12, do any sub-threshold rings with an "isolated" sandwiched
ternary pivot (both second-neighbors binary, but neither left^3(t) nor
right^3(t) is sandwiched) exist? If so, what are their geometries?

Definitions:
- Sub-threshold: product(m_i) < 4 * 3^(n-2)
- Sandwiched ternary pivot t: m(t) >= 3, m(t-1) = 2, m(t+1) = 2
- Both second-neighbors binary: m(t-2) = 2, m(t+2) = 2
- Isolated: left^3(t) = t-3 is NOT sandwiched AND right^3(t) = t+3 is NOT sandwiched
  - t-3 sandwiched iff m(t-3) >= 3 AND m(t-4) = 2 AND m(t-2) = 2
    We know m(t-2) = 2, so t-3 sandwiched iff m(t-3) >= 3 AND m(t-4) = 2
  - Similarly t+3 sandwiched iff m(t+3) >= 3 AND m(t+4) = 2
  - Isolated means: NOT(m(t-3)>=3 AND m(t-4)=2) AND NOT(m(t+3)>=3 AND m(t+4)=2)

For isolated pivots, we also check:
- Can P (fireCount of pivot) = 2? (happens when m_t = 3 and fc=2, or m_t=2 impossible since m_t>=3)
  Actually P = fireCount(t) in a good cycle. For sub-threshold with hfc2, P >= 2.
  P = m_t in a minimum-length cycle (each proc fires exactly m_t times? No, fires enough to cycle).
  Actually fireCount = m_t for each processor in a minimum good cycle.
  So P = m_t. If m_t = 3, P = 3. If m_t = 2... but m_t >= 3 for pivot.
  Wait: P >= 2 from hfc2. And P = m_t in minimum cycle. So P = m_t >= 3.

  Hmm, but the question says "P = 2 is problematic." Let me re-examine.
  Actually fireCount can be any value >= 2 depending on the cycle, not necessarily = m_t.
  In the formal proof, we consider arbitrary good cycles with fc >= 2 at every processor.
  So P = fireCount(t) could be exactly 2 even if m_t = 3.

Let me just enumerate the geometries first.
"""

from itertools import combinations_with_replacement, permutations
from collections import Counter
import sys

def threshold(n):
    """4 * 3^(n-2)"""
    return 4 * (3 ** (n - 2))

def product(ms):
    p = 1
    for m in ms:
        p *= m
    return p

def get_multisets(n, thresh):
    """
    Enumerate all multisets of n values >= 2 with product < thresh.
    At least 3 binary (from counting lemma: if <= 2 binary, product >= 4*3^(n-2)).
    """
    # We need at least 3 entries = 2
    # Maximum single entry: thresh // 2^(n-1) ... but let's just enumerate
    # For n=9, thresh=8748. Max single value with rest=2: 8748/2^8 = 34.17 -> 34
    # For n=12, thresh=708588. Max single value: 708588/2^11 = 345.99 -> 345

    max_val = thresh // (2 ** (n - 1))

    results = []
    # Generate multisets as sorted tuples
    # Use recursive enumeration
    def enumerate_ms(remaining, min_val, current, cur_prod):
        if remaining == 0:
            if cur_prod < thresh:
                results.append(tuple(current))
            return
        max_v = min(max_val, thresh // (cur_prod * (2 ** (remaining - 1))))
        if max_v < min_val:
            return
        for v in range(min_val, max_v + 1):
            new_prod = cur_prod * v
            if new_prod * (2 ** (remaining - 1)) >= thresh:
                break
            enumerate_ms(remaining - 1, v, current + [v], new_prod)

    enumerate_ms(n, 2, [], 1)

    # Filter: need at least 3 binary
    results = [ms for ms in results if ms.count(2) >= 3]
    return results

def get_ring_arrangements(ms_tuple, n):
    """
    Get all distinct ring arrangements (up to rotation and reflection? No -
    we consider labeled rings, so all permutations matter, but we only need
    distinct circular arrangements).

    Actually for checking existence, we need all distinct circular arrangements.
    A circular arrangement is a permutation up to cyclic rotation.
    """
    # Generate all unique permutations, then deduplicate by cyclic rotation
    seen = set()
    arrangements = []

    counts = Counter(ms_tuple)
    elements = list(ms_tuple)

    for perm in set(permutations(elements)):
        # Canonical form: minimum rotation
        canonical = min(perm[i:] + perm[:i] for i in range(n))
        if canonical not in seen:
            seen.add(canonical)
            arrangements.append(perm)

    return arrangements

def check_ring(ring, n):
    """
    For a ring arrangement, find all sandwiched ternary pivots with both
    second-neighbors binary and check isolation.

    Returns list of (pivot_index, local_signature, is_isolated, isolation_reason)
    """
    results = []
    for t in range(n):
        m_t = ring[t]
        if m_t < 3:
            continue

        # Check sandwiched: left and right neighbors are binary
        lft = ring[(t - 1) % n]
        rgt = ring[(t + 1) % n]
        if lft != 2 or rgt != 2:
            continue

        # Check both second-neighbors binary
        lft2 = ring[(t - 2) % n]
        rgt2 = ring[(t + 2) % n]
        if lft2 != 2 or rgt2 != 2:
            continue

        # Now check isolation
        # left^3(t) = t-3. Sandwiched iff m(t-3) >= 3 AND m(t-4) = 2
        lft3 = ring[(t - 3) % n]
        lft4 = ring[(t - 4) % n]
        left3_sandwiched = (lft3 >= 3 and lft4 == 2)

        # right^3(t) = t+3. Sandwiched iff m(t+3) >= 3 AND m(t+4) = 2
        rgt3 = ring[(t + 3) % n]
        rgt4 = ring[(t + 4) % n]
        right3_sandwiched = (rgt3 >= 3 and rgt4 == 2)

        is_isolated = not left3_sandwiched and not right3_sandwiched

        # Local signature: (m_{t-4}, m_{t-3}, m_{t-2}, m_{t-1}, m_t, m_{t+1}, m_{t+2}, m_{t+3}, m_{t+4})
        local_sig = tuple(ring[(t + d) % n] for d in range(-4, 5))

        reason = ""
        if not is_isolated:
            if left3_sandwiched and right3_sandwiched:
                reason = "both sides sandwiched"
            elif left3_sandwiched:
                reason = "left3 sandwiched"
            else:
                reason = "right3 sandwiched"
        else:
            # Why not sandwiched on each side
            left_reason = f"m(t-3)={lft3}<3" if lft3 < 3 else f"m(t-4)={lft4}!=2"
            right_reason = f"m(t+3)={rgt3}<3" if rgt3 < 3 else f"m(t+4)={rgt4}!=2"
            reason = f"left: {left_reason}, right: {right_reason}"

        results.append({
            'pivot': t,
            'local_sig': local_sig,
            'is_isolated': is_isolated,
            'reason': reason,
            'm_t': m_t,
        })

    return results

def main():
    for n in range(9, 13):
        thresh = threshold(n)
        print(f"\n{'='*70}")
        print(f"n = {n}, threshold = {thresh}")
        print(f"{'='*70}")

        multisets = get_multisets(n, thresh)
        print(f"Sub-threshold multisets with >=3 binary: {len(multisets)}")

        total_rings = 0
        total_pivots = 0  # sandwiched with binary 2nd-neighbors
        total_isolated = 0
        isolated_examples = []
        non_isolated_count = 0

        # Track unique local signatures
        isolated_sigs = Counter()
        non_isolated_sigs = Counter()

        for ms in multisets:
            arrangements = get_ring_arrangements(ms, n)

            for ring in arrangements:
                total_rings += 1
                pivot_results = check_ring(ring, n)

                for pr in pivot_results:
                    total_pivots += 1
                    sig = pr['local_sig']

                    if pr['is_isolated']:
                        total_isolated += 1
                        isolated_sigs[sig] += 1
                        if len(isolated_examples) < 20:
                            isolated_examples.append((ring, pr))
                    else:
                        non_isolated_count += 1
                        non_isolated_sigs[sig] += 1

        print(f"Total distinct ring arrangements: {total_rings}")
        print(f"Total sandwiched pivots with binary 2nd-neighbors: {total_pivots}")
        print(f"  Non-isolated (left^3 or right^3 sandwiched): {non_isolated_count}")
        print(f"  ISOLATED: {total_isolated}")

        if total_isolated > 0:
            print(f"\n  Unique isolated local signatures: {len(isolated_sigs)}")
            for sig, count in isolated_sigs.most_common(30):
                # sig = (m_{t-4}, m_{t-3}, m_{t-2}, m_{t-1}, m_t, m_{t+1}, m_{t+2}, m_{t+3}, m_{t+4})
                print(f"    {sig}  (count={count})")
                # Analyze: why is left^3 not sandwiched?
                # left^3 = t-3: m(t-3)=sig[1], m(t-4)=sig[0]
                # right^3 = t+3: m(t+3)=sig[7], m(t+4)=sig[8]

            print(f"\n  First isolated examples:")
            for ring, pr in isolated_examples[:10]:
                print(f"    ring={ring}, pivot={pr['pivot']}, m_t={pr['m_t']}, "
                      f"sig={pr['local_sig']}, reason={pr['reason']}")

        if total_isolated > 0:
            # Deeper analysis: what are the m_t values for isolated pivots?
            mt_counts = Counter()
            for sig, count in isolated_sigs.items():
                mt_counts[sig[4]] += count
            print(f"\n  m_t distribution for isolated pivots:")
            for mt, count in sorted(mt_counts.items()):
                print(f"    m_t={mt}: {count} cases")
                # If m_t = 3, P = fireCount could be 2 in some cycles
                # If m_t >= 4, P >= 2 still, but layer 1 pigeonhole:
                #   fireCount(2nd-neighbor) = 2 < P needs P >= 3
                #   P = 2 is still possible regardless of m_t

            # Check: for isolated pivots, what are m(t-3), m(t-4), m(t+3), m(t+4)?
            print(f"\n  Boundary values for isolated pivots:")
            boundary_patterns = Counter()
            for sig, count in isolated_sigs.items():
                # sig = (m_{t-4}, m_{t-3}, 2, 2, m_t, 2, 2, m_{t+3}, m_{t+4})
                bp = (sig[0], sig[1], sig[7], sig[8])  # (m_{t-4}, m_{t-3}, m_{t+3}, m_{t+4})
                boundary_patterns[bp] += count
            for bp, count in boundary_patterns.most_common(20):
                l4, l3, r3, r4 = bp
                # left3 not sandwiched: l3 < 3 OR l4 != 2
                # right3 not sandwiched: r3 < 3 OR r4 != 2
                left_why = "l3 binary" if l3 < 3 else f"l4={l4}>=3"
                right_why = "r3 binary" if r3 < 3 else f"r4={r4}>=3"
                print(f"    (m_{{t-4}}={l4}, m_{{t-3}}={l3}, m_{{t+3}}={r3}, m_{{t+4}}={r4})"
                      f"  count={count}  [{left_why}, {right_why}]")

        # Summary for isDominoesOrContaminated question
        if total_isolated > 0:
            print(f"\n  === isDominoesOrContaminated analysis ===")
            print(f"  For isolated pivots, Layer 1 (nested phase pigeonhole) needs P >= 3.")
            print(f"  P = fireCount(t) >= 2 from hfc2.")
            print(f"  If P >= 3: Layer 1 works (2 < 3). No dominoes/contaminated needed.")
            print(f"  If P = 2: Layer 1 fails. Need layers 2-3.")
            print(f"  Layer 2 (within-phase EC): fails only in 'tight' phases.")
            print(f"  Layer 3 (binary recovery): fails only when J is odd.")
            print(f"  Remaining: tight + J odd + moverAt(a) = 2nd-neighbor.")
            print(f"  In isolated case: left^3(t) has non-sandwiched geometry.")
            print(f"  This means left^3(t) either: (a) is binary itself, or")
            print(f"  (b) has m>=3 but left^4(t) has m>=3 (not sandwiched).")

            # Count case (a) vs (b) for left and right
            case_a_left = sum(c for sig, c in isolated_sigs.items() if sig[1] < 3)
            case_b_left = sum(c for sig, c in isolated_sigs.items() if sig[1] >= 3)
            case_a_right = sum(c for sig, c in isolated_sigs.items() if sig[7] < 3)
            case_b_right = sum(c for sig, c in isolated_sigs.items() if sig[7] >= 3)
            print(f"\n  Left^3(t): binary={case_a_left}, ternary+non-sandwiched={case_b_left}")
            print(f"  Right^3(t): binary={case_a_right}, ternary+non-sandwiched={case_b_right}")

            # If left^3 is binary (case a): we have 5+ consecutive binary around the pivot
            # Pattern: ..., 2, 2, 2, 2, m_t, 2, 2, ...
            # This means left^3 = binary, so we have at least 4 binary on the left side
            five_consec = sum(c for sig, c in isolated_sigs.items()
                           if sig[1] < 3 and sig[7] < 3)
            print(f"  Both sides binary (5+ consecutive binary around pivot): {five_consec}")

if __name__ == '__main__':
    main()
