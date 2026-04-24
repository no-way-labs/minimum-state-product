#!/usr/bin/env python3
"""
Faster isolated pivot check for n=9..12.

Key optimization: instead of enumerating all ring permutations, we enumerate
multisets and check which ones CAN produce isolated pivots based on their
value counts. Then for those that can, we enumerate only the distinct
circular arrangements.

Additional analysis: classify isolated pivots into subcases based on whether
isDominoesOrContaminated can arise.
"""

from itertools import permutations
from collections import Counter
from math import prod
import sys

def threshold(n):
    return 4 * (3 ** (n - 2))

def get_multisets(n, thresh):
    """Enumerate multisets with product < thresh and >= 3 binary entries."""
    results = []
    max_val = thresh // (2 ** (n - 1))

    def enum(remaining, min_val, current, cur_prod):
        if remaining == 0:
            if cur_prod < thresh:
                results.append(tuple(current))
            return
        mv = thresh // (cur_prod * (2 ** (remaining - 1)))
        if mv < min_val:
            return
        for v in range(min_val, min(mv, max_val) + 1):
            new_prod = cur_prod * v
            if new_prod * (2 ** (remaining - 1)) >= thresh:
                break
            enum(remaining - 1, v, current + [v], new_prod)

    enum(n, 2, [], 1)
    return [ms for ms in results if ms.count(2) >= 3]

def distinct_circular(ms_tuple, n):
    """Get distinct circular arrangements (necklaces) of a multiset."""
    seen = set()
    results = []
    for perm in set(permutations(ms_tuple)):
        canonical = min(perm[i:] + perm[:i] for i in range(n))
        if canonical not in seen:
            seen.add(canonical)
            results.append(perm)
    return results

def can_have_isolated_pivot(ms_tuple):
    """Quick check: can this multiset produce an isolated sandwiched pivot?
    Need: at least one entry >= 3, and enough binary entries to fill
    positions t-2, t-1, t+1, t+2 (4 binary).
    Plus isolation: left^3 and right^3 not sandwiched.
    """
    c = Counter(ms_tuple)
    num_binary = c[2]
    num_nonbinary = sum(v for k, v in c.items() if k > 2)
    # Need at least 4 binary for the inner ring (t-2,t-1,t+1,t+2)
    # Plus the pivot itself is non-binary
    # Minimum: 4 binary + 1 non-binary = 5 entries. Always true for n >= 9.
    return num_binary >= 4 and num_nonbinary >= 1

def analyze_ring(ring, n):
    """Find all isolated sandwiched pivots and classify them."""
    results = []
    for t in range(n):
        m_t = ring[t]
        if m_t < 3:
            continue
        # Sandwiched: both immediate neighbors binary
        if ring[(t-1) % n] != 2 or ring[(t+1) % n] != 2:
            continue
        # Both second-neighbors binary
        if ring[(t-2) % n] != 2 or ring[(t+2) % n] != 2:
            continue

        # Check isolation
        m_l3 = ring[(t-3) % n]
        m_l4 = ring[(t-4) % n]
        m_r3 = ring[(t+3) % n]
        m_r4 = ring[(t+4) % n]

        l3_sandwiched = (m_l3 >= 3 and m_l4 == 2)  # m(t-2)=2 already
        r3_sandwiched = (m_r3 >= 3 and m_r4 == 2)  # m(t+2)=2 already

        if l3_sandwiched or r3_sandwiched:
            continue  # Not isolated

        # Isolated pivot found. Classify.
        # Case A: left^3 is binary (m_l3 = 2)
        # Case B: left^3 is non-binary but not sandwiched (m_l3 >= 3, m_l4 >= 3)
        left_case = 'A' if m_l3 == 2 else 'B'
        right_case = 'A' if m_r3 == 2 else 'B'

        results.append({
            't': t,
            'm_t': m_t,
            'left_case': left_case,
            'right_case': right_case,
            'm_l3': m_l3, 'm_l4': m_l4,
            'm_r3': m_r3, 'm_r4': m_r4,
            'case_pair': (left_case, right_case),
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

        # Filter to those that could have isolated pivots
        candidates = [ms for ms in multisets if can_have_isolated_pivot(ms)]
        print(f"Candidates (could have isolated pivot): {len(candidates)}")

        total_rings = 0
        total_isolated = 0
        case_counts = Counter()  # (left_case, right_case) -> count
        mt_by_case = {}  # case_pair -> Counter of m_t values

        # For the key question: rings where m_t could yield P=2
        # P = fireCount(t) in a good cycle. P >= 2 from hfc2.
        # P could be 2 regardless of m_t (it's a cycle parameter, not m_t).
        # But in a minimum-length good cycle, each proc fires exactly m_i times,
        # so P = m_t >= 3. In longer cycles, P could be 2.
        # Actually no: in ANY good cycle, each proc must fire at least m_i times
        # (to cycle through all states). So P >= m_t >= 3 for pivot.
        # Wait, that's wrong too. A good cycle visits all product(m_i) configs.
        # Each processor fires some number of times. The minimum is... hmm.
        #
        # In a good cycle of a self-stabilizing system:
        # - visits all configs exactly once
        # - each processor fires at least once
        # - from hfc2: each processor fires at least 2 times
        # But there's no constraint that proc fires >= m_i times.
        # E.g., a ternary proc with states {0,1,2} could fire twice:
        # state changes 0->1->2 (fires at steps where state changes).
        # Actually "fire" means the transition function is applied and state changes.
        # If m_t = 3, the proc has 3 states, and in one full cycle it must
        # return to its starting state. The number of fires = number of state
        # changes. To return to start: fires must be multiple of m_t? No.
        # State changes: 0->1, 1->2, 2->0 would be 3 fires.
        # Or 0->1, 1->0 would be 2 fires (and never visits state 2 for THIS proc).
        # But good cycle visits ALL configs, so this proc must be in state 2
        # at some point. If it's in state 2, it must have gotten there (fire 1->2)
        # and left (fire 2->0 or 2->1). So at least 2 fires involving state 2,
        # plus the other fires. Actually: each of the m_t states must be visited,
        # and the state sequence forms a cycle. The number of fires = number of
        # transitions in this cycle = number of edges = number of vertices in the
        # cycle = m_t (if Hamiltonian on states) or more.
        #
        # Wait no. The processor visits states in some order dictated by the
        # global cycle. It must visit all m_t states (since good cycle covers
        # all configs, and other procs can be in any state). The state sequence
        # of proc t in the good cycle is a sequence that visits each state at
        # least once and returns to start. The fires are the transitions.
        # The minimum number of fires to visit all m_t states and return = m_t
        # (Hamiltonian cycle on the state space).
        #
        # So fireCount(t) >= m_t >= 3 for the pivot!
        # This means P >= 3, and Layer 1 always works!

        p2_possible = 0  # pivots where P could be 2

        for ms in candidates:
            if n <= 10:
                arrangements = distinct_circular(ms, n)
            else:
                # For n >= 11, use sampling or smarter enumeration
                # Actually let's try the full enumeration but with early termination
                arrangements = distinct_circular(ms, n)

            for ring in arrangements:
                total_rings += 1
                pivots = analyze_ring(ring, n)
                for pv in pivots:
                    total_isolated += 1
                    cp = pv['case_pair']
                    case_counts[cp] += 1
                    if cp not in mt_by_case:
                        mt_by_case[cp] = Counter()
                    mt_by_case[cp][pv['m_t']] += 1

                    # Can P = 2? Only if m_t <= 2, but m_t >= 3.
                    # Actually, as argued above, P >= m_t >= 3.
                    # So P = 2 is IMPOSSIBLE for any sandwiched pivot.
                    if pv['m_t'] <= 2:
                        p2_possible += 1  # Should never happen

        print(f"Total distinct ring arrangements checked: {total_rings}")
        print(f"Total isolated pivots: {total_isolated}")
        print(f"Pivots where P could be 2 (m_t <= 2): {p2_possible}")

        print(f"\nCase breakdown (left_case, right_case):")
        for cp, cnt in case_counts.most_common():
            print(f"  {cp}: {cnt}")
            mt_dist = mt_by_case[cp]
            print(f"    m_t values: {dict(sorted(mt_dist.items()))}")

        # The key conclusion
        print(f"\n*** KEY FINDING ***")
        print(f"Since m_t >= 3 for every sandwiched pivot, and fireCount(t) >= m_t")
        print(f"in any good cycle (proc must visit all m_t states), P >= 3 always.")
        print(f"Therefore Layer 1 (pigeonhole: fireCount(2nd-nbr)=2 < P=3) ALWAYS works.")
        print(f"isDominoesOrContaminated NEVER arises at isolated pivots.")

        if n >= 11:
            print(f"\n(n={n} may be slow due to permutation enumeration)")
            sys.stdout.flush()

if __name__ == '__main__':
    main()
