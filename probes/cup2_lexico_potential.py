#!/usr/bin/env python3
"""Search for lexicographic potential functions for convergence proof.

Instead of Φ: configs → ℤ, try multi-level potentials:
  Φ(c) = (φ₁(c), φ₂(c), ...) with lexicographic comparison.

Also try: can we partition transitions into "levels" where
each level has a simple decreasing quantity?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, Counter
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system


def frontier_count(c, n):
    return sum(1 for i in range(n) if c[i] != c[(i + 1) % n])


def total_sum(c, n):
    return sum(c)


def ternary_sum(c, n):
    return sum(c[1:n-1])


def max_run_of_same(c, n):
    """Length of longest run of identical consecutive values."""
    best = 1
    current = 1
    for i in range(1, n):
        if c[i] == c[i-1]:
            current += 1
            best = max(best, current)
        else:
            current = 1
    # Also check wrap-around
    if c[0] == c[n-1]:
        # Count run from end wrapping to start
        run_end = 0
        for i in range(n-1, -1, -1):
            if c[i] == c[n-1]:
                run_end += 1
            else:
                break
        run_start = 0
        for i in range(n):
            if c[i] == c[0]:
                run_start += 1
            else:
                break
        best = max(best, run_end + run_start)
    return best


def transition_type(c, cp, mover, fs, n):
    """Classify a transition by what happens at the mover."""
    old_val = c[mover]
    new_val = cp[mover]
    L = c[(mover - 1) % n]
    R = c[(mover + 1) % n]
    return (mover, old_val, new_val, L, R)


def main():
    print("LEXICOGRAPHIC POTENTIAL & TRANSITION CLASSIFICATION")
    print("=" * 90)

    for nv in [5, 6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        if not result['valid']:
            continue
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Collect all transitions
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

        print(f"\nn={nv}: {len(bad_set)} bad, {len(transitions)} bad→bad transitions")

        # Classify transitions by (direction of change, which table)
        type_counts = Counter()
        for c, cp, mv in transitions:
            old_v = c[mv]
            new_v = cp[mv]
            if mv == 0:
                tbl = "bot"
            elif mv == 1:
                tbl = "low"
            elif mv < n - 2:
                tbl = "mid"
            elif mv == n - 2:
                tbl = "high"
            else:
                tbl = "top"
            direction = new_v - old_v
            type_counts[(tbl, old_v, new_v)] += 1

        print("  Transition types (table, old→new, count):")
        for k in sorted(type_counts.keys()):
            tbl, old_v, new_v = k
            print(f"    {tbl:>4} {old_v}→{new_v}: {type_counts[k]}")

        # Key question: for each transition type, does frontier always change
        # in a predictable direction?
        print("\n  Frontier change by transition type:")
        for k in sorted(type_counts.keys()):
            tbl, old_v, new_v = k
            fcs = []
            for c, cp, mv in transitions:
                if c[mv] == old_v and cp[mv] == new_v:
                    mt = "bot" if mv == 0 else "low" if mv == 1 else \
                         "mid" if mv < n - 2 else "high" if mv == n - 2 else "top"
                    if mt == tbl:
                        fcs.append(frontier_count(cp, n) - frontier_count(c, n))
            if fcs:
                print(f"    {tbl:>4} {old_v}→{new_v}: "
                      f"min={min(fcs):+d} max={max(fcs):+d} avg={sum(fcs)/len(fcs):+.2f}")

        # Try: (frontier_count, -ternary_sum) as lexicographic potential
        # i.e. Φ(c) = (frontier(c), -ternary_sum(c)) with lex comparison
        # c > c' iff frontier(c) > frontier(c') OR
        #            (frontier(c) == frontier(c') AND ternary_sum(c) < ternary_sum(c'))
        print(f"\n  Testing lexicographic potentials:")
        for name, phi1, phi2 in [
            ("(front, -sum)", lambda c: frontier_count(c, n), lambda c: -total_sum(c, n)),
            ("(front, sum)", lambda c: frontier_count(c, n), lambda c: total_sum(c, n)),
            ("(-front, -sum)", lambda c: -frontier_count(c, n), lambda c: -total_sum(c, n)),
            ("(-front, sum)", lambda c: -frontier_count(c, n), lambda c: total_sum(c, n)),
            ("(sum, front)", lambda c: total_sum(c, n), lambda c: frontier_count(c, n)),
            ("(-sum, front)", lambda c: -total_sum(c, n), lambda c: frontier_count(c, n)),
            ("(front, -maxrun)", lambda c: frontier_count(c, n), lambda c: -max_run_of_same(c, n)),
        ]:
            viol = 0
            for c, cp, mv in transitions:
                p1c, p2c = phi1(c), phi2(c)
                p1cp, p2cp = phi1(cp), phi2(cp)
                if (p1c, p2c) <= (p1cp, p2cp):
                    viol += 1
            pct = 100 * viol / len(transitions) if transitions else 0
            status = "PERFECT" if viol == 0 else f"{viol} violations ({pct:.1f}%)"
            print(f"    {name:>20}: {status}")

    # Detailed: which transitions violate the best candidate?
    print("\n\nDETAILED VIOLATION ANALYSIS (n=6, (front, -sum))")
    print("-" * 70)
    nv = 6
    ms, fs = build_system(nv)
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)
    transitions = []
    for c in bad_set:
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c); lst[i] = new_S; succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    violations = []
    for c, cp, mv in transitions:
        fc = frontier_count(c, n)
        fcp = frontier_count(cp, n)
        sc = total_sum(c, n)
        scp = total_sum(cp, n)
        if (fc, -sc) <= (fcp, -scp):
            violations.append((c, cp, mv, fc, fcp, sc, scp))

    print(f"Violations: {len(violations)} / {len(transitions)}")
    for c, cp, mv, fc, fcp, sc, scp in violations[:15]:
        print(f"  {c} →[P{mv}]→ {cp}: front {fc}→{fcp}, sum {sc}→{scp}")

    # What about a 3-level potential?
    # (frontier, -sum, something)
    print("\n\n3-LEVEL LEXICOGRAPHIC SEARCH (n=6)")
    print("-" * 70)

    # First collect the (front=, sum=) violations
    front_sum_viol = [(c, cp, mv) for c, cp, mv, fc, fcp, sc, scp in violations]
    if front_sum_viol:
        print(f"Need to break {len(front_sum_viol)} ties")
        # Try various third components
        for name3, phi3 in [
            ("ternary_sum", lambda c: ternary_sum(c, n)),
            ("-ternary_sum", lambda c: -ternary_sum(c, n)),
            ("nonzero", lambda c: sum(1 for x in c if x > 0)),
            ("-nonzero", lambda c: -sum(1 for x in c if x > 0)),
            ("maxrun", lambda c: max_run_of_same(c, n)),
            ("-maxrun", lambda c: -max_run_of_same(c, n)),
            ("binary_sum", lambda c: c[0] + c[n-1]),
            ("-binary_sum", lambda c: -(c[0] + c[n-1])),
        ]:
            viol3 = sum(1 for c, cp, mv in front_sum_viol if phi3(c) <= phi3(cp))
            print(f"  {name3:>15}: {viol3} remaining violations")


if __name__ == "__main__":
    main()
