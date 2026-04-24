#!/usr/bin/env python3
"""
Verify the CORRECTED interior potential measure for CUP-2 convergence.

Key fix: extend disagree range to include position n-3 (rightmost 6-tuple position).

Measure M(c) = (total_disagree, sum_distances) compared lexicographically.
- Disagree range: {3, 4, ..., n-3}
- Firing range (interior): {3, 4, ..., n-4}
- ld(j) = 1 if c[j] != c[j-1], else 0
- Right-shifting types: {(0,2), (1,0), (2,1)} where TMid(a,b,b)=a
- Left-shifting types: {(1,2), (2,0)} where TMid(a,a,b)=b
- Non-shifting: {(0,1)}
- dist(j) for right-shifting: (n-4) - j
- dist(j) for left-shifting: j - 3
- dist(j) for non-shifting: n
"""

import itertools

# CUP-2 Tables
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,
        (1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
        (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,
        (1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,
        (1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,
         (1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,
        (2,0,1):1,(2,1,0):1,(2,1,1):1}

RIGHT_SHIFTING = {(0,2), (1,0), (2,1)}
LEFT_SHIFTING = {(1,2), (2,0)}
NON_SHIFTING = {(0,1)}


def fire(c, j, n):
    """Apply CUP-2 transition at position j, return new config or None if no change."""
    L, S, R = c[j-1], c[j], c[(j+1) % n]
    if j == 0:
        new_val = TBot[(c[n-1], c[0], c[1])]
    elif j == 1:
        new_val = TLow[(c[0], c[1], c[2])]
    elif j == n-2:
        new_val = THigh[(c[n-3], c[n-2], c[n-1])]
    elif j == n-1:
        new_val = TTop[(c[n-2], c[n-1], c[0])]
    else:
        new_val = TMid[(L, S, R)]
    if new_val == S:
        return None
    cp = list(c)
    cp[j] = new_val
    return tuple(cp)


def compute_measure(c, n):
    """Compute M(c) = (total_disagree, sum_distances) over disagree range {3,...,n-3}."""
    total_disagree = 0
    sum_distances = 0
    for j in range(3, n-2):  # j = 3, 4, ..., n-3
        if c[j] != c[j-1]:
            total_disagree += 1
            tp = (c[j-1], c[j])
            if tp in RIGHT_SHIFTING:
                d = (n-4) - j
            elif tp in LEFT_SHIFTING:
                d = j - 3
            elif tp in NON_SHIFTING:
                d = n
            else:
                # Shouldn't happen: all (a,b) with a!=b covered
                d = n
            sum_distances += d
    return (total_disagree, sum_distances)


def compute_measure_alt(c, n):
    """Alternative measure: weight by distance to boundary heading toward."""
    total_disagree = 0
    sum_distances = 0
    for j in range(3, n-2):  # j = 3, 4, ..., n-3
        if c[j] != c[j-1]:
            total_disagree += 1
            tp = (c[j-1], c[j])
            if tp in RIGHT_SHIFTING:
                d = n - j  # distance to right boundary
            elif tp in LEFT_SHIFTING:
                d = j  # distance to left boundary
            elif tp in NON_SHIFTING:
                d = n
            else:
                d = n
            sum_distances += d
    return (total_disagree, sum_distances)


def verify_n(n, use_alt=False):
    """Verify measure strictly decreases for all interior fires at size n."""
    measure_fn = compute_measure_alt if use_alt else compute_measure

    # State space: positions 0..n-1, each in {0,1,2} except P0 in {0,1}
    # P0: binary (0,1), P1..P_{n-2}: ternary (0,1,2), P_{n-1}: binary (0,1)
    # Actually ms = (2, 3, 3, ..., 3, 2)

    states = []
    # P0 in {0,1}, P1..P_{n-2} in {0,1,2}, P_{n-1} in {0,1}
    ranges = []
    for i in range(n):
        if i == 0 or i == n-1:
            ranges.append(range(2))
        else:
            ranges.append(range(3))

    total_fires = 0
    violations = 0
    violation_examples = []

    for c in itertools.product(*ranges):
        # Try each interior firing position
        for j in range(3, n-3):  # j = 3, 4, ..., n-4
            cp = fire(c, j, n)
            if cp is None:
                continue  # no change, skip

            total_fires += 1
            m_before = measure_fn(c, n)
            m_after = measure_fn(cp, n)

            if m_after >= m_before:
                violations += 1
                if len(violation_examples) < 3:
                    violation_examples.append((c, j, cp, m_before, m_after))

    return total_fires, violations, violation_examples


def main():
    print("=" * 70)
    print("INTERIOR MEASURE VERIFICATION (v2 — extended disagree range)")
    print("=" * 70)
    print()
    print("Disagree range: {3, ..., n-3}")
    print("Firing range:   {3, ..., n-4}")
    print("Right-shifting: (0,2), (1,0), (2,1)  dist = (n-4) - j")
    print("Left-shifting:  (1,2), (2,0)          dist = j - 3")
    print("Non-shifting:   (0,1)                  dist = n")
    print()

    all_pass = True
    results = {}

    for n in [9, 10, 11, 12]:
        print(f"--- n = {n} ---")
        total_fires, violations, examples = verify_n(n)
        results[n] = (total_fires, violations, examples)

        if violations == 0:
            print(f"  Total fires checked: {total_fires}")
            print(f"  Violations: 0  *** PASS ***")
        else:
            all_pass = False
            print(f"  Total fires checked: {total_fires}")
            print(f"  Violations: {violations}  *** FAIL ***")
            for i, (c, j, cp, mb, ma) in enumerate(examples):
                print(f"  Example {i+1}:")
                print(f"    c  = {list(c)}")
                print(f"    fire pos j = {j}")
                print(f"    c' = {list(cp)}")
                print(f"    M(c)  = {mb}")
                print(f"    M(c') = {ma}")
                # Show disagree details
                print(f"    Disagree details (range 3..{n-3}):")
                for k in range(3, n-2):
                    if c[k] != c[k-1]:
                        tp = (c[k-1], c[k])
                        cat = "R" if tp in RIGHT_SHIFTING else ("L" if tp in LEFT_SHIFTING else "N")
                        print(f"      pos {k}: ({c[k-1]},{c[k]}) {cat}", end="")
                        if k == j or k == j+1:
                            print(" <-- affected by fire", end="")
                        print()
                print(f"    After fire:")
                for k in range(3, n-2):
                    if cp[k] != cp[k-1]:
                        tp = (cp[k-1], cp[k])
                        cat = "R" if tp in RIGHT_SHIFTING else ("L" if tp in LEFT_SHIFTING else "N")
                        print(f"      pos {k}: ({cp[k-1]},{cp[k]}) {cat}")
        print()

    print()
    if all_pass:
        print("=" * 70)
        print("ALL PASSED — measure strictly decreases for all interior fires")
        print("=" * 70)
        return

    # If there were violations, try alternative measure
    print("=" * 70)
    print("TRYING ALTERNATIVE MEASURE")
    print("Right-shifting dist = n - j, Left-shifting dist = j")
    print("=" * 70)
    print()

    all_pass_alt = True
    for n in [9, 10, 11, 12]:
        print(f"--- n = {n} (alt) ---")
        total_fires, violations, examples = verify_n(n, use_alt=True)

        if violations == 0:
            print(f"  Total fires checked: {total_fires}")
            print(f"  Violations: 0  *** PASS ***")
        else:
            all_pass_alt = False
            print(f"  Total fires checked: {total_fires}")
            print(f"  Violations: {violations}  *** FAIL ***")
            for i, (c, j, cp, mb, ma) in enumerate(examples):
                print(f"  Example {i+1}:")
                print(f"    c  = {list(c)}")
                print(f"    fire pos j = {j}")
                print(f"    c' = {list(cp)}")
                print(f"    M(c)  = {mb}")
                print(f"    M(c') = {ma}")
        print()

    if all_pass_alt:
        print("=" * 70)
        print("ALTERNATIVE MEASURE PASSED for all n")
        print("=" * 70)
    else:
        print("=" * 70)
        print("ALTERNATIVE MEASURE ALSO FAILED")
        print("=" * 70)


if __name__ == "__main__":
    main()
