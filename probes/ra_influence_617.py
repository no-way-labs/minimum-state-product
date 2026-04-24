#!/usr/bin/env python3
"""
Verify the 617 boundary transitions against the PhiFull formula.

Now that we know PhiFull(c) = fc(c) + 1{c[0]=1, c[1]=2, c[n-1]=1},
a boundary transition c -> c' (via firing a boundary proc) preserves
PhiFull iff it preserves fc + delta.

This means:
  fc(c') + delta(c') = fc(c) + delta(c)

where delta(c) = 1{c[0]=1, c[1]=2, c[n-1]=1}.

The boundary transitions change boundary positions only (positions 0,1,2,n-3,n-2,n-1).
For a bad-to-bad TP-preserving boundary move:
  PhiFull-preserving iff  delta_fc + delta_delta = 0
where delta_fc = fc(c') - fc(c), delta_delta = delta(c') - delta(c).

Since delta is in {0,1}, delta_delta is in {-1, 0, 1}.

Let's verify the 617 count and check that the formula correctly classifies them.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict

sys.stdout.reconfigure(line_buffering=True)

# ── CUP-2 tables ────────────────────────────────────────────────────────
T_low = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):0, (1,0,2):0,
    (1,1,0):0, (1,1,1):1, (1,1,2):0,
}
T_high = {
    (0,0,0):0, (0,0,1):0, (0,1,0):0, (0,1,1):0,
    (0,2,0):0, (0,2,1):0, (1,0,0):0, (1,0,1):1,
    (1,1,0):0, (1,1,1):1, (1,2,0):0, (1,2,1):1,
}
T_mid = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (0,2,0):2, (0,2,1):0, (0,2,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (1,2,0):2, (1,2,1):1, (1,2,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
    (2,2,0):2, (2,2,1):0, (2,2,2):2,
}
T_lo_adj = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):1, (0,1,1):0, (0,1,2):0,
    (1,0,0):0, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):1,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
}
T_hi_adj = {
    (0,0,0):0, (0,0,1):0, (0,1,0):1, (0,1,1):0,
    (0,2,0):2, (0,2,1):0, (1,0,0):0, (1,0,1):1,
    (1,1,0):1, (1,1,1):1, (1,2,0):2, (1,2,1):1,
    (2,0,0):0, (2,0,1):0, (2,1,0):1, (2,1,1):0,
    (2,2,0):2, (2,2,1):0,
}

def cup2_output(n, c, i):
    S, L, R = c[i], c[(i-1)%n], c[(i+1)%n]
    if i == 0: return T_low.get((S, L, R), S)
    elif i == n-1: return T_high.get((S, L, R), S)
    elif i == 1: return T_lo_adj.get((S, L, R), S)
    elif i == n-2: return T_hi_adj.get((S, L, R), S)
    else: return T_mid.get((S, L, R), S)

def is_privileged(n, c, i):
    return cup2_output(n, c, i) != c[i]

def fire(n, c, i):
    lst = list(c)
    lst[i] = cup2_output(n, c, i)
    return tuple(lst)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def modulus(i, n):
    return 2 if i == 0 or i == n-1 else 3

def all_configs(n):
    return list(cartesian(*(range(modulus(i, n)) for i in range(n))))

def tp_invariant(c, n):
    e2, i21, ew = 0, 0, 0
    for j in range(2, n-2):
        if c[j] == 2:
            r = c[(j+1)%n]
            if r == 0 or r == 1:
                e2 += 1; ew += j
                if r == 1: i21 += 1
    return (e2, i21, ew)

def build_good_set(n):
    configs = all_configs(n)
    return {c for c in configs if sum(1 for i in range(n) if is_privileged(n, c, i)) == 1}

def phi_full_formula(c, n):
    """PhiFull via the discovered formula."""
    fv = fc(c, n)
    delta = 1 if (c[0] == 1 and c[1] == 2 and c[n-1] == 1) else 0
    return fv + delta

def boundary_6(c, n):
    return c[:3] + c[n-3:]

def main():
    print("=" * 70)
    print("617 BOUNDARY TRANSITION VERIFICATION")
    print("=" * 70)

    # For each n, count boundary transitions where PhiFull is preserved
    # A "boundary transition" fires a processor at position 0, 1, 2, n-3, n-2, or n-1
    # We count (boundary_6(c), fired_pos) -> boundary_6(c') transitions
    # that are:
    #   1. bad-to-bad
    #   2. TP-preserving
    #   3. PhiFull-preserving
    # grouped by (boundary_6_before, boundary_6_after)

    for n in [9, 10, 11, 12]:
        t0 = time.time()
        configs = all_configs(n)
        good = build_good_set(n)
        bad_set = set(c for c in configs if c not in good)

        # Boundary positions
        boundary_pos = {0, 1, 2, n-3, n-2, n-1}

        # Collect boundary transitions as 6-tuple pairs
        phi_pres_transitions = set()  # (b6_before, b6_after) PhiFull-preserving
        phi_drop_transitions = set()  # PhiFull-dropping
        formula_pres = set()
        formula_drop = set()

        for c in bad_set:
            tp_c = tp_invariant(c, n)
            for p in boundary_pos:
                if not is_privileged(n, c, p):
                    continue
                d = fire(n, c, p)
                if d not in bad_set:
                    continue
                if tp_invariant(d, n) != tp_c:
                    continue

                b6_c = boundary_6(c, n)
                b6_d = boundary_6(d, n)

                # Actual PhiFull check
                phi_c = phi_full_formula(c, n)
                phi_d = phi_full_formula(d, n)

                if phi_c == phi_d:
                    phi_pres_transitions.add((b6_c, b6_d))
                    formula_pres.add((b6_c, b6_d))
                else:
                    phi_drop_transitions.add((b6_c, b6_d))
                    formula_drop.add((b6_c, b6_d))

        elapsed = time.time() - t0
        print(f"\n  n={n}: {len(phi_pres_transitions)} PhiFull-preserving, "
              f"{len(phi_drop_transitions)} PhiFull-dropping, "
              f"total {len(phi_pres_transitions) + len(phi_drop_transitions)} ({elapsed:.1f}s)")

    # Now show the formula in action: for a boundary transition (b6_src, b6_dst),
    # PhiFull is preserved iff delta_fc(interior) + delta_delta = 0
    # where delta_delta = delta(b6_dst) - delta(b6_src)
    # and delta_fc = fc_boundary_change (which depends on b6_src, b6_dst, and the
    # two interior neighbors c[3] and c[n-4])

    print(f"\n{'─'*60}")
    print("FORMULA-BASED CLASSIFICATION")
    print(f"{'─'*60}")

    n = 11
    configs = all_configs(n)
    good = build_good_set(n)
    bad_set = set(c for c in configs if c not in good)
    boundary_pos = {0, 1, 2, n-3, n-2, n-1}

    # For each boundary transition, check if PhiFull preservation depends on interior
    # Group by (b6_src, b6_dst): does PhiFull preservation always agree?
    transition_phi = defaultdict(set)  # (b6_src, b6_dst) -> set of (phi_preserved: bool)

    for c in bad_set:
        tp_c = tp_invariant(c, n)
        for p in boundary_pos:
            if not is_privileged(n, c, p): continue
            d = fire(n, c, p)
            if d not in bad_set: continue
            if tp_invariant(d, n) != tp_c: continue

            b6_c = boundary_6(c, n)
            b6_d = boundary_6(d, n)
            phi_c = phi_full_formula(c, n)
            phi_d = phi_full_formula(d, n)
            preserved = (phi_c == phi_d)
            transition_phi[(b6_c, b6_d)].add(preserved)

    # Check: does the boundary transition type determine PhiFull preservation?
    ambiguous = {k: v for k, v in transition_phi.items() if len(v) > 1}
    print(f"\n  Total (b6_src, b6_dst) transition types: {len(transition_phi)}")
    preserving = sum(1 for v in transition_phi.values() if v == {True})
    dropping = sum(1 for v in transition_phi.values() if v == {False})
    both = sum(1 for v in transition_phi.values() if len(v) > 1)
    print(f"  Always preserving: {preserving}")
    print(f"  Always dropping: {dropping}")
    print(f"  Ambiguous (depends on interior): {both}")

    if both > 0:
        print(f"\n  AMBIGUOUS transitions:")
        for (b6_c, b6_d), vals in sorted(ambiguous.items())[:10]:
            # Show examples of preserving and dropping
            pres_count = 0
            drop_count = 0
            for c in bad_set:
                if boundary_6(c, n) != b6_c: continue
                tp_c = tp_invariant(c, n)
                for p in boundary_pos:
                    if not is_privileged(n, c, p): continue
                    d = fire(n, c, p)
                    if d not in bad_set: continue
                    if tp_invariant(d, n) != tp_c: continue
                    if boundary_6(d, n) != b6_d: continue
                    phi_c = phi_full_formula(c, n)
                    phi_d = phi_full_formula(d, n)
                    if phi_c == phi_d:
                        pres_count += 1
                    else:
                        drop_count += 1
            print(f"    {b6_c} -> {b6_d}: {pres_count} preserving, {drop_count} dropping")
    else:
        print(f"\n  PhiFull preservation is COMPLETELY determined by (b6_src, b6_dst)")
        print(f"  This means the 617/481 split is exactly a property of 6-tuple transitions,")
        print(f"  no interior information needed!")

    # Compute analytically: for boundary transition, delta_fc at the boundary
    # The fc pairs affected by boundary positions are:
    # (n-1, 0), (0, 1), (1, 2), (2, 3), (n-4, n-3), (n-3, n-2), (n-2, n-1)
    # Of these, (2, 3) and (n-4, n-3) involve one interior position.
    # When we fire a boundary proc, fc changes at the affected pairs.
    # But fc is a GLOBAL quantity, so the fc change involves these boundary pairs
    # plus potentially pairs (2,3) and (n-4,n-3) which depend on interior.
    # However, firing a boundary proc doesn't change interior values, so:
    #   - (2, 3): c[2] vs c[3]. If we fire position 2, c[2] changes but c[3] doesn't.
    #     The fc change at (2,3) depends on c[3] which is interior.
    # This means fc change DOES depend on interior (via c[3] and c[n-4]).
    # But PhiFull = fc + delta, and delta changes only based on boundary.
    # So PhiFull change = fc_change + delta_change.
    # For PhiFull to be always-preserved or always-dropped for a given (b6_src, b6_dst),
    # it must be that fc_change is ALSO determined by (b6_src, b6_dst) —
    # which happens when the fired proc doesn't change positions adjacent to interior,
    # OR when the interior neighbor value doesn't matter for the fc calculation.

    # Let's check: which transitions fire position 2 or n-3?
    print(f"\n{'─'*60}")
    print("WHICH BOUNDARY POSITIONS GET FIRED?")
    print(f"{'─'*60}")

    fire_pos_dist = defaultdict(int)
    for c in bad_set:
        tp_c = tp_invariant(c, n)
        for p in boundary_pos:
            if not is_privileged(n, c, p): continue
            d = fire(n, c, p)
            if d not in bad_set: continue
            if tp_invariant(d, n) != tp_c: continue
            fire_pos_dist[p] += 1

    for p in sorted(fire_pos_dist):
        print(f"  Position {p}: {fire_pos_dist[p]} TP-preserving bad-to-bad fires")

    # Check: for fires at position 2 and n-3, does fc_change depend on interior?
    print(f"\n  For position 2 fires:")
    pos2_fc = defaultdict(set)  # (b6_src, b6_dst) -> set of fc changes
    for c in bad_set:
        if not is_privileged(n, c, 2): continue
        d = fire(n, c, 2)
        if d not in bad_set: continue
        tp_c = tp_invariant(c, n)
        if tp_invariant(d, n) != tp_c: continue
        b6_c = boundary_6(c, n)
        b6_d = boundary_6(d, n)
        delta_fc = fc(d, n) - fc(c, n)
        pos2_fc[(b6_c, b6_d)].add(delta_fc)

    varying = {k: v for k, v in pos2_fc.items() if len(v) > 1}
    print(f"  {len(pos2_fc)} (b6_src, b6_dst) pairs for pos 2")
    print(f"  {len(varying)} have variable fc_change (depend on c[3])")
    for k, v in list(varying.items())[:3]:
        print(f"    {k[0]} -> {k[1]}: fc changes in {sorted(v)}")

if __name__ == "__main__":
    main()
