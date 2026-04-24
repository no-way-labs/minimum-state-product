#!/usr/bin/env python3
"""
check_gap_parity.py — Gap parity analysis at min-gap edges in sub-threshold systems.

For sub-threshold systems with ms=(2,3,...,3,2) (product < 4*3^(n-2)),
we analyze good cycles to find paired crossings (CW then CCW at same edge)
and measure the gap between them.

Key questions:
1. At each edge with paired crossings, what is the minimum gap? Is it always even?
2. Is there always an edge with EVEN gap >= 2?
3. Distribution of gaps across edges?
4. Can the minimum gap be odd (specifically 1 or 3)?
5. Under "no safe processor" hypothesis, what's the minimum gap?

The gap b-a at a paired crossing corresponds to the fire count of right(p)
between steps a+1 and b inclusive. For binary right(p), value is preserved
iff fire count (= gap) is even.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict

# Import build_system from cup2_theorem
from cup2_theorem import build_system

def all_configs(ms):
    return list(cartesian(*(range(m) for m in ms)))

def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i - 1) % n]
        S = config[i]
        R = config[(i + 1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)

def find_good_cycle(ms, fs, n):
    """Find the good cycle by starting from the all-zeros config and following
    the unique privileged processor."""
    start = tuple([0] * n)
    config = start
    cycle_configs = [config]
    cycle_movers = []

    while True:
        priv = privileged_set(config, fs, ms)
        if len(priv) != 1:
            # Not in good cycle if multiple privileged
            return None, None
        mover = priv[0]
        cycle_movers.append(mover)
        config = apply_move(config, mover, fs, ms)
        if config == start:
            break
        cycle_configs.append(config)

    return cycle_configs, cycle_movers

def step_direction(mover_prev, mover_curr, n):
    """Determine step direction: 'cw' if mover moves right, 'ccw' if left, 'stay' if same."""
    if mover_curr == (mover_prev + 1) % n:
        return 'cw'
    elif mover_curr == (mover_prev - 1) % n:
        return 'ccw'
    elif mover_curr == mover_prev:
        return 'stay'
    else:
        return 'jump'  # shouldn't happen in well-formed cycles

def analyze_crossings(cycle_configs, cycle_movers, n):
    """Find all edge crossings and paired crossings with gaps.

    An edge (p, right(p)) where right(p) = (p+1)%n is crossed:
    - CW at step k if moverAt(k) = p and stepDir(k) = cw
      (i.e., moverAt(k+1) = p+1)
    - CCW at step k if moverAt(k) = (p+1)%n and stepDir(k) = ccw
      (i.e., moverAt(k+1) = p)

    A paired crossing at edge (p, p+1) is a CW crossing at step a followed
    by a CCW crossing at step b with no other crossings of this edge in (a,b).
    """
    L = len(cycle_movers)

    # Compute step directions
    # stepDir at step k: how mover moves from step k to step k+1
    # moverAt(k) = cycle_movers[k]
    # moverAt(k+1) = cycle_movers[(k+1) % L]
    dirs = []
    for k in range(L):
        dirs.append(step_direction(cycle_movers[k], cycle_movers[(k+1) % L], n))

    # Find crossings for each edge
    # Edge e = (p, (p+1)%n)
    edge_crossings = defaultdict(list)  # edge_p -> [(step, 'cw'/'ccw')]

    for k in range(L):
        p = cycle_movers[k]
        d = dirs[k]
        if d == 'cw':
            # CW crossing of edge (p, (p+1)%n)
            edge_crossings[p].append((k, 'cw'))
        elif d == 'ccw':
            # CCW crossing of edge ((p-1)%n, p)
            edge_crossings[(p - 1) % n].append((k, 'ccw'))

    return edge_crossings, dirs

def find_paired_crossings(edge_crossings, L):
    """For each edge, find all opposite-direction paired crossings with their gaps.

    A paired crossing is (a, b) where a is CW, b is CCW (or vice versa),
    a < b, and no other crossing of this edge exists in (a, b).
    """
    paired = {}  # edge_p -> [(a, b, gap, type)]

    for p, crossings in edge_crossings.items():
        if len(crossings) < 2:
            continue

        # Sort by step index
        crossings_sorted = sorted(crossings, key=lambda x: x[0])

        pairs = []
        # Find consecutive pairs that are opposite direction
        for i in range(len(crossings_sorted)):
            step_a, dir_a = crossings_sorted[i]
            # Look at the next crossing (wrapping)
            j = (i + 1) % len(crossings_sorted)
            step_b, dir_b = crossings_sorted[j]

            if dir_a != dir_b:
                # Opposite direction pair
                if step_b > step_a:
                    gap = step_b - step_a
                else:
                    gap = step_b + L - step_a  # wrap around

                pair_type = f"{dir_a}->{dir_b}"
                pairs.append((step_a, step_b, gap, pair_type))

        if pairs:
            paired[p] = pairs

    return paired

def has_safe_processor(cycle_movers, n):
    """Check if there's a processor q such that q, left(q), right(q) are never movers."""
    mover_set = set(cycle_movers)
    for q in range(n):
        if q not in mover_set and (q-1)%n not in mover_set and (q+1)%n not in mover_set:
            return True, q
    return False, None

def analyze_system(n, verbose=True):
    """Full analysis for a given n."""
    ms, fs = build_system(n)
    cycle_configs, cycle_movers = find_good_cycle(ms, fs, n)

    if cycle_configs is None:
        print(f"n={n}: Could not find good cycle from all-zeros")
        return None

    L = len(cycle_movers)
    if verbose:
        print(f"\n{'='*70}")
        print(f"n={n}, ms={ms}, product={eval('*'.join(str(m) for m in ms))}")
        print(f"Good cycle length: {L}")
        print(f"Movers: {cycle_movers}")

    # Check for safe processor
    safe, safe_q = has_safe_processor(cycle_movers, n)
    if verbose:
        if safe:
            print(f"Safe processor exists: q={safe_q} (not relevant for entry conflict)")
        else:
            print(f"No safe processor (good — this is the hard case)")

    # Find crossings
    edge_crossings, dirs = analyze_crossings(cycle_configs, cycle_movers, n)

    if verbose:
        print(f"\nStep directions: {dirs}")
        print(f"\nEdge crossings:")
        for p in sorted(edge_crossings.keys()):
            crossings = edge_crossings[p]
            print(f"  Edge ({p}, {(p+1)%n}): {crossings}")

    # Find paired crossings
    paired = find_paired_crossings(edge_crossings, L)

    if verbose:
        print(f"\nPaired crossings (opposite direction):")
        for p in sorted(paired.keys()):
            for a, b, gap, ptype in paired[p]:
                right_p = (p + 1) % n
                is_binary_right = (ms[right_p] == 2)
                parity = "EVEN" if gap % 2 == 0 else "ODD"
                print(f"  Edge ({p}, {right_p}): steps ({a}, {b}), gap={gap} [{parity}], "
                      f"type={ptype}, right_binary={is_binary_right}")

    # Analysis: minimum gap across all edges
    all_gaps = []
    binary_right_gaps = []
    for p, pairs in paired.items():
        for a, b, gap, ptype in pairs:
            right_p = (p + 1) % n
            all_gaps.append((gap, p, right_p, a, b, ptype))
            if ms[right_p] == 2:
                binary_right_gaps.append((gap, p, right_p, a, b, ptype))

    if verbose and all_gaps:
        min_gap = min(g[0] for g in all_gaps)
        print(f"\nGap analysis:")
        print(f"  All gaps: {sorted(g[0] for g in all_gaps)}")
        print(f"  Min gap: {min_gap} ({'EVEN' if min_gap % 2 == 0 else 'ODD'})")

        even_gaps = [g for g in all_gaps if g[0] % 2 == 0]
        odd_gaps = [g for g in all_gaps if g[0] % 2 != 0]
        print(f"  Even gaps: {sorted(g[0] for g in even_gaps)}")
        print(f"  Odd gaps: {sorted(g[0] for g in odd_gaps)}")

        if binary_right_gaps:
            print(f"\n  Binary-right gaps: {sorted(g[0] for g in binary_right_gaps)}")
            even_binary = [g for g in binary_right_gaps if g[0] % 2 == 0]
            print(f"  Even binary-right gaps: {sorted(g[0] for g in even_binary)}")
            if even_binary:
                print(f"  => EXISTS edge with binary right(p) and even gap! Entry conflict available.")
            else:
                print(f"  => NO edge with binary right(p) and even gap.")

    # Also check: for the min-gap edge, what is right(p)?
    if all_gaps:
        min_gap_entry = min(all_gaps, key=lambda g: g[0])
        gap, p, rp, a, b, ptype = min_gap_entry
        if verbose:
            print(f"\n  Min-gap edge: ({p}, {rp}), gap={gap}, right_binary={ms[rp]==2}")
            print(f"    p fires at steps: {[k for k in range(L) if cycle_movers[k] == p]}")
            print(f"    right(p) fires at steps: {[k for k in range(L) if cycle_movers[k] == rp]}")

    # Check p's firing pattern around the crossing
    if verbose and all_gaps:
        print(f"\n  Detailed mover sequence around min-gap crossing:")
        gap, p, rp, a, b, ptype = min_gap_entry
        for k in range(max(0, a-2), min(L, b+3)):
            m = cycle_movers[k]
            d = dirs[k] if k < L else '?'
            marker = ""
            if k == a:
                marker = " <-- CW crossing of edge"
            elif k == b:
                marker = " <-- CCW crossing of edge"
            print(f"    step {k}: mover={m}, dir={d}{marker}")

    return {
        'n': n, 'L': L, 'safe': safe, 'safe_q': safe_q,
        'all_gaps': all_gaps, 'binary_right_gaps': binary_right_gaps,
        'paired': paired, 'edge_crossings': edge_crossings,
        'cycle_movers': cycle_movers, 'ms': ms,
    }


def check_all_good_cycles(n, verbose=True):
    """For small n, enumerate ALL good cycles (not just from all-zeros)
    and check gap parity for each."""
    ms, fs = build_system(n)
    configs = all_configs(ms)

    # Find all good configs (exactly 1 privileged)
    good_set = set()
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            good_set.add(c)

    if verbose:
        print(f"\nn={n}: {len(good_set)} good configs")

    # Find all good cycles by following transitions
    visited = set()
    cycles = []

    for start in good_set:
        if start in visited:
            continue

        path = [start]
        path_set = {start}
        config = start
        movers = []

        while True:
            priv = privileged_set(config, fs, ms)
            assert len(priv) == 1
            mover = priv[0]
            movers.append(mover)
            config = apply_move(config, mover, fs, ms)

            if config == start:
                # Found a cycle
                for c in path:
                    visited.add(c)
                cycles.append((path, movers))
                break
            elif config in path_set:
                # Rho-shaped path, find the cycle part
                idx = path.index(config)
                cycle_path = path[idx:]
                cycle_movers = movers[idx:]
                for c in path:
                    visited.add(c)
                cycles.append((cycle_path, cycle_movers))
                break
            else:
                path.append(config)
                path_set.add(config)

    if verbose:
        print(f"Found {len(cycles)} good cycle(s)")

    return cycles


def exhaustive_sub_threshold_check(n, verbose=True):
    """Check ALL sub-threshold multisets (not just CUP-2) for gap parity.
    For small n only (n=5,6)."""
    from verifier import verify_system as vs

    if verbose:
        print(f"\n{'='*70}")
        print(f"EXHAUSTIVE sub-threshold check for n={n}")

    # Generate all multisets with product < 4*3^(n-2) and >= 3 binary procs
    threshold = 4 * (3 ** (n - 2))

    # For n=5: threshold = 108. Product must be < 108 with all m_i >= 2.
    # For n=6: threshold = 324.

    # Find all valid multisets
    max_m = threshold  # upper bound on any single state count

    def gen_ms(pos, remaining_product, current_ms):
        if pos == n:
            if remaining_product == 1:
                yield tuple(current_ms)
            return

        min_m = 2
        max_m_here = min(remaining_product, threshold - 1)  # product must stay < threshold

        for m in range(min_m, max_m_here + 1):
            if remaining_product % m == 0:
                # For sorted generation (avoid duplicates), require non-decreasing
                if pos > 0 and m < current_ms[-1]:
                    continue
                yield from gen_ms(pos + 1, remaining_product // m, current_ms + [m])

    # Actually, let's just enumerate products and factorizations
    results = []

    from itertools import combinations_with_replacement

    # Generate candidate state counts
    candidates = list(range(2, threshold))

    # For efficiency, just try all sorted tuples with product < threshold
    count = 0
    found_odd_min_gap = False

    # Simpler approach: enumerate products
    for product in range(2**n, threshold):
        # Find all factorizations into n factors >= 2
        factorizations = find_factorizations(product, n)
        for ms_sorted in factorizations:
            # Check >= 3 binary
            binary_count = sum(1 for m in ms_sorted if m == 2)
            if binary_count < 3:
                continue

            # Try all permutations (actually, for ring systems,
            # we need to try all distinct circular permutations)
            from itertools import permutations
            seen_perms = set()
            for perm in permutations(ms_sorted):
                # Normalize circular permutation
                min_rot = min(perm[i:] + perm[:i] for i in range(n))
                if min_rot in seen_perms:
                    continue
                seen_perms.add(min_rot)
                ms_list = list(perm)

                # This is getting complex. Skip for now and focus on CUP-2.
                count += 1

    if verbose:
        print(f"  Would need to check {count} distinct ring placements")
        print(f"  (Skipping full enumeration — CUP-2 analysis is primary)")


def find_factorizations(product, n, min_factor=2):
    """Find all sorted factorizations of product into exactly n factors >= min_factor."""
    if n == 1:
        if product >= min_factor:
            return [(product,)]
        return []

    result = []
    # First factor ranges from min_factor to product^(1/n) (roughly)
    for f in range(min_factor, product + 1):
        if product % f != 0:
            continue
        remaining = product // f
        if remaining < min_factor ** (n - 1):
            continue
        # The remaining (n-1) factors must each be >= f (sorted)
        for rest in find_factorizations(remaining, n - 1, f):
            result.append((f,) + rest)

    return result


def deep_analysis_p_fires(n, verbose=True):
    """Deep analysis: at the min-gap crossing, how does p fire?

    From the task description:
    - At step a: p fires CW (mover=p, direction=cw)
    - Between a+1 and b-1: mover is at right(p), stays
    - At step b: right(p) fires CCW
    - At step b+1: p fires (from right(p) going CCW to p)

    So p fires at a and b+1 (not in between).
    Fire count of p in [a, b+1] = 2 (even!)

    And right(p) fires at steps a+1, a+2, ..., b (staying, then CCW)
    Fire count of right(p) = b - a
    """
    ms, fs = build_system(n)
    cycle_configs, cycle_movers = find_good_cycle(ms, fs, n)
    L = len(cycle_movers)

    # Compute step directions
    dirs = []
    for k in range(L):
        dirs.append(step_direction(cycle_movers[k], cycle_movers[(k+1) % L], n))

    if verbose:
        print(f"\n{'='*70}")
        print(f"DEEP ANALYSIS: p's firing pattern at min-gap crossing, n={n}")

    edge_crossings, _ = analyze_crossings(cycle_configs, cycle_movers, n)
    paired = find_paired_crossings(edge_crossings, L)

    # For each paired crossing, verify the "only stays" claim
    for p in sorted(paired.keys()):
        for a, b, gap, ptype in paired[p]:
            if 'cw->ccw' not in ptype:
                continue
            right_p = (p + 1) % n

            # Check: between a+1 and b-1, is mover always right(p)?
            all_right_p = True
            mover_seq = []
            for k in range(a + 1, b):
                m = cycle_movers[k % L]
                mover_seq.append(m)
                if m != right_p:
                    all_right_p = False

            # Check: are all intermediate directions "stay"?
            all_stay = all(dirs[k % L] == 'stay' for k in range(a + 1, b))

            # Check: at step b, mover is right(p) going CCW
            mover_b = cycle_movers[b % L]
            dir_b = dirs[b % L]

            # Check: at step b+1, mover should be p
            if b + 1 < L:
                mover_b1 = cycle_movers[(b + 1) % L]
            else:
                mover_b1 = cycle_movers[(b + 1) % L]

            # p's fire count between a and b+1
            p_fires = sum(1 for k in range(a, b + 2) if cycle_movers[k % L] == p)
            rp_fires = sum(1 for k in range(a + 1, b + 1) if cycle_movers[k % L] == right_p)

            if verbose:
                print(f"\n  Edge ({p}, {right_p}), crossing ({a}, {b}), gap={gap}, type={ptype}")
                print(f"    Mover sequence [a..b+1]: ", end="")
                for k in range(a, b + 2):
                    m = cycle_movers[k % L]
                    d = dirs[k % L]
                    print(f"{m}({d}) ", end="")
                print()
                print(f"    All intermediate movers = right(p)={right_p}? {all_right_p}")
                print(f"    All intermediate dirs = stay? {all_stay}")
                print(f"    mover[b]={mover_b}, dir[b]={dir_b}")
                print(f"    mover[b+1]={mover_b1}")
                print(f"    p fires {p_fires} times in [a, b+1]")
                print(f"    right(p) fires {rp_fires} times in [a+1, b]")
                print(f"    gap = {gap}, parity = {'EVEN' if gap % 2 == 0 else 'ODD'}")

                if ms[right_p] == 2:
                    print(f"    right(p) is BINARY: value preserved iff gap even => {'YES' if gap % 2 == 0 else 'NO'}")
                if ms[p] == 2:
                    print(f"    p is BINARY: fires {p_fires} times => value preserved iff even => {'YES' if p_fires % 2 == 0 else 'NO'}")


def check_all_sub_threshold_multisets_small(n, verbose=True):
    """For small n, check ALL sub-threshold multisets with >= 3 binary.
    Build ALL valid systems and check their good cycles for gap parity."""

    from verifier import verify_system as vs
    from itertools import permutations

    threshold = 4 * (3 ** (n - 2))

    if verbose:
        print(f"\n{'='*70}")
        print(f"ALL sub-threshold multisets for n={n}, threshold={threshold}")

    # Find factorizations
    all_ms = set()
    for product in range(2**n, threshold):
        for factors in find_factorizations(product, n):
            binary_count = sum(1 for f in factors if f == 2)
            if binary_count >= 3:
                # Try all distinct circular arrangements
                for perm in set(permutations(factors)):
                    # Normalize to smallest circular rotation
                    rotations = [perm[i:] + perm[:i] for i in range(n)]
                    min_rot = min(rotations)
                    # Also consider reverse (ring is undirected)
                    rev = perm[::-1]
                    rev_rotations = [rev[i:] + rev[:i] for i in range(n)]
                    min_rev = min(rev_rotations)
                    canonical = min(min_rot, min_rev)
                    all_ms.add(canonical)

    if verbose:
        print(f"Found {len(all_ms)} distinct ring arrangements")

    # For each, we need a valid system. CUP-2 only works for ms=(2,3,...,3,2).
    # For other multisets, we'd need to search. Just check CUP-2 compatible ones.
    cup2_compatible = []
    other = []
    for ms_tuple in sorted(all_ms):
        ms_list = list(ms_tuple)
        if ms_list[0] == 2 and ms_list[-1] == 2 and all(m == 3 for m in ms_list[1:-1]):
            cup2_compatible.append(ms_tuple)
        else:
            other.append(ms_tuple)

    if verbose:
        print(f"CUP-2 compatible: {len(cup2_compatible)}")
        print(f"Other arrangements: {len(other)}")
        if other and len(other) <= 20:
            for ms_tuple in other[:20]:
                print(f"  {ms_tuple}, product={eval('*'.join(str(m) for m in ms_tuple))}")


def main():
    print("=" * 70)
    print("GAP PARITY ANALYSIS AT MIN-GAP EDGES")
    print("=" * 70)

    # Question 1-4: Analyze CUP-2 systems for n=5..11
    summary = {}
    for n in range(5, 14):
        result = analyze_system(n, verbose=(n <= 8))
        if result:
            all_gaps = result['all_gaps']
            if all_gaps:
                gaps = sorted(g[0] for g in all_gaps)
                min_gap = min(gaps)
                even_count = sum(1 for g in gaps if g % 2 == 0)
                odd_count = sum(1 for g in gaps if g % 2 != 0)
                binary_even = sum(1 for g in result['binary_right_gaps'] if g[0] % 2 == 0)
                summary[n] = {
                    'gaps': gaps,
                    'min_gap': min_gap,
                    'min_parity': 'EVEN' if min_gap % 2 == 0 else 'ODD',
                    'even_count': even_count,
                    'odd_count': odd_count,
                    'binary_even_count': binary_even,
                    'safe': result['safe'],
                }

    print(f"\n{'='*70}")
    print("SUMMARY TABLE")
    print(f"{'='*70}")
    print(f"{'n':>4} {'L':>4} {'safe':>5} {'gaps':>30} {'min':>4} {'par':>5} {'#even':>5} {'#odd':>5} {'bin_even':>8}")
    print("-" * 70)
    for n in sorted(summary.keys()):
        s = summary[n]
        print(f"{n:>4} {3*n-2:>4} {str(s['safe']):>5} {str(s['gaps']):>30} {s['min_gap']:>4} {s['min_parity']:>5} "
              f"{s['even_count']:>5} {s['odd_count']:>5} {s['binary_even_count']:>8}")

    # Deep analysis
    for n in [5, 6, 7, 8, 9]:
        deep_analysis_p_fires(n, verbose=True)

    # For small n, check all sub-threshold multisets
    for n in [5]:
        check_all_sub_threshold_multisets_small(n, verbose=True)

    # Key insight analysis
    print(f"\n{'='*70}")
    print("KEY INSIGHT ANALYSIS")
    print(f"{'='*70}")
    print("""
At the globally-minimum-gap paired crossing (a, b) at edge (p, right(p)):

1. From MinGap.lean: right(p) does NOT fire CW between a and b.
2. No CCW fire either (would be a crossing, contradicting "no crossings in (a,b)").
3. So right(p) can only STAY between a+1 and b-1.
4. This means the mover is stuck at right(p) from a+1 to b-1.
5. At step b, right(p) fires CCW (the paired crossing).
6. Fire count of right(p) in [a+1, b] = b - a = gap.

For binary right(p): value preserved iff gap is even.

Additionally:
7. p fires at step a (CW crossing) and at step b+1 (mover returns to p).
8. p does NOT fire between a and b+1 (mover is at right(p) the whole time).
9. Fire count of p in [a, b+1] = 2 (always even!).
10. So p's value is ALWAYS preserved (regardless of gap parity).

This means:
- L (= left(proc)) is preserved: p fires twice
- S (= proc itself) is preserved: proc doesn't fire between the two observation steps
- R (= right(proc)) is preserved iff gap is EVEN and right(proc) is binary

The question is: can we CHOOSE the edge so that right(p) is binary AND gap is even?
Or: can we use p's guaranteed preservation differently?

ALTERNATIVE: The BAFArcAdj structure uses proc (interior processor) where:
- cwNeighborStep: right(proc) fires CW (proc is non-mover)
- ccwProcStep: proc fires CCW (proc is mover)
- The (L,S,R) at proc must match at both steps.
- R = right(proc)'s value must be preserved.

In our min-gap setting, the "proc" in BAFArcAdj corresponds to right(p),
and right(proc) = right(right(p)).

Wait — let me reconsider the mapping...
""")


if __name__ == '__main__':
    main()
