#!/usr/bin/env python3
"""Search for a potential function that proves convergence.

We need Φ: configs → ℕ such that for every bad config c and every
enabled transition c → c', Φ(c') < Φ(c).

Test several candidates:
1. Frontier count: #{i : c_i ≠ c_{i+1 mod n}}
2. Weighted frontier: Σ w_i * [c_i ≠ c_{i+1 mod n}]
3. d-vector based: Σ f(d_i) where d_i = (c_{i+1} - c_i) % m
4. Total displacement from zero: Σ c_i
5. Hamming distance to nearest good config
6. "Agreement" count: #{i : c_i = c_{i+1 mod n}}
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict

# Import universal tables
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top, build_system


def get_transitions(ms, fs, n, good_set):
    """Get all bad→bad transitions."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    transitions = []
    for c in bad_set:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    return transitions, bad_set


def test_potential(name, phi, transitions, bad_set):
    """Test if phi is a valid potential function."""
    violations = 0
    worst = 0
    for c, c_prime, mover in transitions:
        diff = phi(c) - phi(c_prime)
        if diff <= 0:
            violations += 1
            worst = min(worst, diff)
    return violations, worst


def frontier_count(c, n):
    """Number of positions where consecutive values differ."""
    ms_local = [2] + [3] * (n - 2) + [2]
    count = 0
    for i in range(n):
        if c[i] != c[(i + 1) % n]:
            count += 1
    return count


def total_sum(c, n):
    return sum(c)


def nonzero_count(c, n):
    return sum(1 for x in c if x > 0)


def weighted_sum(c, n):
    """Weight ternary values more."""
    s = 0
    for i in range(n):
        if i == 0 or i == n - 1:
            s += c[i] * 10
        else:
            s += c[i]
    return s


def ternary_max(c, n):
    """Max ternary value."""
    return max(c[1:n-1]) if n > 2 else 0


def agreement_pairs(c, n):
    """Count how many adjacent pairs agree (higher = more ordered)."""
    return sum(1 for i in range(n) if c[i] == c[(i + 1) % n])


def rank_vector(c, n):
    """Lexicographic rank as a number (for testing monotonicity)."""
    ms = [2] + [3] * (n - 2) + [2]
    rank = 0
    mult = 1
    for i in range(n - 1, -1, -1):
        rank += c[i] * mult
        mult *= ms[i]
    return rank


def main():
    print("POTENTIAL FUNCTION SEARCH")
    print("=" * 80)

    from verifier import verify_system

    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break

        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        if not result['valid']:
            print(f"n={nv}: INVALID, skipping")
            continue

        good_set = result['good_configs']
        transitions, bad_set = get_transitions(ms, fs, n, good_set)

        print(f"\nn={nv}: {len(bad_set)} bad configs, {len(transitions)} bad→bad transitions")

        # Test each candidate
        candidates = [
            ("frontier", lambda c, n=n: frontier_count(c, n)),
            ("total_sum", lambda c, n=n: total_sum(c, n)),
            ("nonzero", lambda c, n=n: nonzero_count(c, n)),
            ("weighted_sum", lambda c, n=n: weighted_sum(c, n)),
            ("-frontier", lambda c, n=n: -frontier_count(c, n)),
            ("-total_sum", lambda c, n=n: -total_sum(c, n)),
            ("agreement", lambda c, n=n: agreement_pairs(c, n)),
            ("-agreement", lambda c, n=n: -agreement_pairs(c, n)),
        ]

        for name, phi in candidates:
            viol, worst = test_potential(name, phi, transitions, bad_set)
            pct = 100 * viol / len(transitions) if transitions else 0
            status = "PERFECT" if viol == 0 else f"{viol} violations ({pct:.1f}%)"
            print(f"  {name:>15}: {status}")

    # Detailed analysis: for frontier count, which transitions violate?
    print("\n\nFRONTIER COUNT VIOLATION ANALYSIS (n=6)")
    print("-" * 70)
    nv = 6
    ms, fs = build_system(nv)
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    transitions, bad_set = get_transitions(ms, fs, n, good_set)

    frontier_violations = []
    for c, c_prime, mover in transitions:
        fc = frontier_count(c, n)
        fc_prime = frontier_count(c_prime, n)
        if fc_prime >= fc:
            frontier_violations.append((c, c_prime, mover, fc, fc_prime))

    print(f"Total violations: {len(frontier_violations)} / {len(transitions)}")
    for c, cp, mv, fc, fcp in frontier_violations[:20]:
        print(f"  {c} →[P{mv}]→ {cp}: frontier {fc}→{fcp}")

    # What if we use a 2-level potential: (n - frontier_count, something)?
    # Try: Φ(c) = n * frontier + total_sum
    print("\n\nCOMPOSITE POTENTIAL SEARCH (n=6)")
    print("-" * 70)

    for a in range(-5, 6):
        for b in range(-5, 6):
            if a == 0 and b == 0:
                continue
            def phi(c, a=a, b=b, n=n):
                return a * frontier_count(c, n) + b * total_sum(c, n)
            viol, _ = test_potential(f"({a}*front + {b}*sum)", phi, transitions, bad_set)
            if viol == 0:
                print(f"  FOUND: {a}*frontier + {b}*total_sum")

    # Try with nonzero count too
    for a in range(-3, 4):
        for b in range(-3, 4):
            for c_coeff in range(-3, 4):
                if a == 0 and b == 0 and c_coeff == 0:
                    continue
                def phi(c, a=a, b=b, cc=c_coeff, n=n):
                    return a * frontier_count(c, n) + b * total_sum(c, n) + cc * nonzero_count(c, n)
                viol, _ = test_potential("composite", phi, transitions, bad_set)
                if viol == 0:
                    print(f"  FOUND: {a}*frontier + {b}*sum + {cc}*nonzero")


if __name__ == "__main__":
    main()
