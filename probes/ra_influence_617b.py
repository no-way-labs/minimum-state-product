#!/usr/bin/env python3
"""
Recount the 617 transitions with position info.

The 617 PhiFull-preserving transitions should be counted as
(b6_src, fired_position, b6_dst) triples, matching the Lean definition.
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
    fv = fc(c, n)
    delta = 1 if (c[0] == 1 and c[1] == 2 and c[n-1] == 1) else 0
    return fv + delta

def boundary_6(c, n):
    return c[:3] + c[n-3:]

def main():
    print("=" * 70)
    print("617 TRANSITION RECOUNT")
    print("=" * 70)

    for n in [9, 10, 11, 12, 13]:
        t0 = time.time()
        configs = all_configs(n)
        good = build_good_set(n)
        bad_set = set(c for c in configs if c not in good)
        boundary_pos = {0, 1, 2, n-3, n-2, n-1}

        # Count as (b6_src, position, b6_dst) triples
        phi_pres_triples = set()
        phi_drop_triples = set()

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

                # Normalize position: map to canonical {0, 1, 2, n-3, n-2, n-1}
                # Actually, the Lean code uses positions 0..5 for the 6 boundary positions
                # Let me use the position index relative to boundary
                if p <= 2:
                    bp = p
                else:
                    bp = p - (n - 6)  # maps n-3->3, n-2->4, n-1->5

                triple = (b6_c, bp, b6_d)
                if phi_c == phi_d:
                    phi_pres_triples.add(triple)
                else:
                    phi_drop_triples.add(triple)

        elapsed = time.time() - t0
        total = len(phi_pres_triples) + len(phi_drop_triples)
        print(f"  n={n}: {len(phi_pres_triples)} PhiFull-pres + {len(phi_drop_triples)} PhiFull-drop = {total} triples ({elapsed:.1f}s)")

    # Also try counting as (b6_src, b6_dst) edges (undirected by position)
    print(f"\n  As (b6_src, b6_dst) pairs (no position):")
    for n in [9, 10, 11, 12]:
        configs = all_configs(n)
        good = build_good_set(n)
        bad_set = set(c for c in configs if c not in good)
        boundary_pos = {0, 1, 2, n-3, n-2, n-1}

        pres_pairs = set()
        drop_pairs = set()

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

                if phi_c == phi_d:
                    pres_pairs.add((b6_c, b6_d))
                else:
                    drop_pairs.add((b6_c, b6_d))

        print(f"    n={n}: {len(pres_pairs)} pres + {len(drop_pairs)} drop = {len(pres_pairs)+len(drop_pairs)} pairs")

    # Try yet another counting: maybe it's (b6_src, fired_boundary_position)
    # where the fired position maps to one of the 6 boundary slots
    print(f"\n  As (b6_src, boundary_slot) pairs:")
    for n in [9, 10, 11, 12]:
        configs = all_configs(n)
        good = build_good_set(n)
        bad_set = set(c for c in configs if c not in good)
        boundary_pos_list = [0, 1, 2, n-3, n-2, n-1]

        pres_sp = set()
        drop_sp = set()

        for c in bad_set:
            tp_c = tp_invariant(c, n)
            for p in boundary_pos_list:
                if not is_privileged(n, c, p): continue
                d = fire(n, c, p)
                if d not in bad_set: continue
                if tp_invariant(d, n) != tp_c: continue

                b6_c = boundary_6(c, n)
                phi_c = phi_full_formula(c, n)
                phi_d = phi_full_formula(d, n)

                if p <= 2:
                    bp = p
                else:
                    bp = p - (n - 6)

                if phi_c == phi_d:
                    pres_sp.add((b6_c, bp))
                else:
                    drop_sp.add((b6_c, bp))

        print(f"    n={n}: {len(pres_sp)} pres + {len(drop_sp)} drop = {len(pres_sp)+len(drop_sp)} (src, pos) pairs")

    # The 617 might also include non-boundary (interior) moves that preserve
    # the boundary 6-tuple. Interior moves always preserve the boundary.
    # Let me also count interior TP-preserving bad-to-bad transitions.
    print(f"\n  Including INTERIOR moves (boundary-preserving by definition):")
    for n in [9, 10, 11]:
        configs = all_configs(n)
        good = build_good_set(n)
        bad_set = set(c for c in configs if c not in good)
        boundary_pos = {0, 1, 2, n-3, n-2, n-1}

        # Count (b6, fired_pos) types for ALL positions
        pres_all = set()
        drop_all = set()

        for c in bad_set:
            tp_c = tp_invariant(c, n)
            for p in range(n):
                if not is_privileged(n, c, p): continue
                d = fire(n, c, p)
                if d not in bad_set: continue
                if tp_invariant(d, n) != tp_c: continue

                b6_c = boundary_6(c, n)
                b6_d = boundary_6(d, n)

                phi_c = phi_full_formula(c, n)
                phi_d = phi_full_formula(d, n)

                if p in boundary_pos:
                    if p <= 2: bp = p
                    else: bp = p - (n - 6)
                else:
                    bp = -1  # interior

                if phi_c == phi_d:
                    pres_all.add((b6_c, bp, b6_d))
                else:
                    drop_all.add((b6_c, bp, b6_d))

        # Interior moves never change boundary, and PhiFull = fc + delta
        # where delta depends on boundary only. If boundary unchanged and fc unchanged,
        # then PhiFull unchanged. But interior moves CAN change fc!
        # fc changes if the interior move affects a frontier pair involving the fired position.
        print(f"    n={n}: {len(pres_all)} pres + {len(drop_all)} drop = {len(pres_all)+len(drop_all)} total (b6, pos_type, b6') triples")

    # Let's look at the Lean side for the definition of sixTupleEdge
    print(f"\n{'─'*60}")
    print("CHECKING 617 DEFINITION")
    print(f"{'─'*60}")

    # The Lean code's sixTupleEdge checks: for a transition from b6_src to b6_dst,
    # is this a DAG edge (i.e., lexicographically decreasing)?
    # The 617 are the PhiFull-preserving boundary transitions that form a DAG.
    # Actually, looking at the gen_phi_active_base.py more carefully:
    # activeCheck checks whether:
    #   1. Not privileged -> true
    #   2. Good src or dst -> true
    #   3. Boundary unchanged -> true (interior move)
    #   4. No deep copy pair in dst -> true
    #   5. PhiFull not preserved -> true (PhiFull drops, which is good)
    #   6. TP not preserved -> true
    #   7. Otherwise -> check sixTupleEdge (must be a DAG edge)
    #
    # So the 617 are the transitions that reach step 7 AND pass.
    # These are: privileged, bad-to-bad, boundary-changing, has-deep-copy-pair,
    # PhiFull-preserving, TP-preserving transitions that are DAG edges.
    #
    # The "617" vs "481" split is about WHICH boundary transitions are in the DAG.
    # Not all 617 are PhiFull-preserving — they're all PhiFull-preserving AND
    # need to be in the 6-tuple DAG.

    # Since PhiFull = fc + delta and delta depends only on boundary,
    # the PhiFull-preserving condition for boundary transitions is:
    #   fc(d) + delta(d) = fc(c) + delta(c)
    # For boundary moves, fc_change depends on boundary + c[3] and c[n-4]
    # (the interior neighbors of the boundary).
    # But we showed that (b6_src, b6_dst) determines PhiFull preservation.
    # This means fc_change is also determined by (b6_src, b6_dst) for boundary moves.

    # The key insight: for a boundary move firing position p,
    # the fc change at pairs (2,3) and (n-4,n-3) depends on c[3]/c[n-4].
    # But these pairs' fc contribution is: (c[2]!=c[3]) and (c[n-4]!=c[n-3]).
    # Firing position 2 changes c[2], so the pair (2,3) changes.
    # The old contribution is (old_c2 != c[3]), new is (new_c2 != c[3]).
    # This depends on c[3]! So how can it be boundary-determined?
    # Answer: it IS boundary-determined because b6 includes c[2] but not c[3],
    # and the fc change at (2,3) depends on whether both old and new c[2] values
    # differ from c[3]. Since c[3] can be anything, the fc change at (2,3)
    # could be -1, 0, or +1 depending on c[3].
    # BUT we showed empirically that PhiFull preservation is determined by (b6_src, b6_dst).
    # This means: the fc change at (2,3) is ALWAYS the same sign regardless of c[3],
    # OR the delta compensation cancels it.
    # Let me check this more carefully.

    n = 11
    configs = all_configs(n)
    good = build_good_set(n)
    bad_set = set(c for c in configs if c not in good)

    # For position 2 fires, check fc change at pair (2,3)
    print(f"\n  n={n}: Position 2 fires, fc change at pair (2,3):")
    pair23_by_trans = defaultdict(set)
    for c in bad_set:
        if not is_privileged(n, c, 2): continue
        d = fire(n, c, 2)
        if d not in bad_set: continue
        tp_c = tp_invariant(c, n)
        if tp_invariant(d, n) != tp_c: continue

        b6_c = boundary_6(c, n)
        b6_d = boundary_6(d, n)

        # fc change at pair (2,3)
        old_23 = 1 if c[2] != c[3] else 0
        new_23 = 1 if d[2] != c[3] else 0  # c[3] unchanged
        delta_23 = new_23 - old_23

        pair23_by_trans[(b6_c, b6_d)].add(delta_23)

    varying23 = {k: v for k, v in pair23_by_trans.items() if len(v) > 1}
    print(f"  {len(pair23_by_trans)} transitions, {len(varying23)} with variable pair (2,3) change")
    for k, v in list(varying23.items())[:5]:
        print(f"    {k[0]} -> {k[1]}: delta_23 in {sorted(v)}")

    # Now check total fc change
    total_fc_by_trans = defaultdict(set)
    for c in bad_set:
        if not is_privileged(n, c, 2): continue
        d = fire(n, c, 2)
        if d not in bad_set: continue
        tp_c = tp_invariant(c, n)
        if tp_invariant(d, n) != tp_c: continue

        b6_c = boundary_6(c, n)
        b6_d = boundary_6(d, n)
        delta_fc = fc(d, n) - fc(c, n)
        total_fc_by_trans[(b6_c, b6_d)].add(delta_fc)

    varying_fc = {k: v for k, v in total_fc_by_trans.items() if len(v) > 1}
    print(f"  Total fc change: {len(total_fc_by_trans)} transitions, {len(varying_fc)} with variable total fc")
    for k, v in list(varying_fc.items())[:5]:
        print(f"    {k[0]} -> {k[1]}: delta_fc in {sorted(v)}")

    # Check the same for position n-3 fires
    print(f"\n  Position {n-3} fires, fc change at pair ({n-4},{n-3}):")
    pair_by_trans = defaultdict(set)
    for c in bad_set:
        p = n - 3
        if not is_privileged(n, c, p): continue
        d = fire(n, c, p)
        if d not in bad_set: continue
        tp_c = tp_invariant(c, n)
        if tp_invariant(d, n) != tp_c: continue

        b6_c = boundary_6(c, n)
        b6_d = boundary_6(d, n)

        old_pair = 1 if c[n-4] != c[n-3] else 0
        new_pair = 1 if c[n-4] != d[n-3] else 0
        delta_pair = new_pair - old_pair
        pair_by_trans[(b6_c, b6_d)].add(delta_pair)

    varying_pair = {k: v for k, v in pair_by_trans.items() if len(v) > 1}
    print(f"  {len(pair_by_trans)} transitions, {len(varying_pair)} with variable pair change")

    total_fc_by_trans2 = defaultdict(set)
    for c in bad_set:
        p = n - 3
        if not is_privileged(n, c, p): continue
        d = fire(n, c, p)
        if d not in bad_set: continue
        tp_c = tp_invariant(c, n)
        if tp_invariant(d, n) != tp_c: continue

        b6_c = boundary_6(c, n)
        b6_d = boundary_6(d, n)
        delta_fc = fc(d, n) - fc(c, n)
        total_fc_by_trans2[(b6_c, b6_d)].add(delta_fc)

    varying_fc2 = {k: v for k, v in total_fc_by_trans2.items() if len(v) > 1}
    print(f"  Total fc change: {len(total_fc_by_trans2)} transitions, {len(varying_fc2)} with variable total fc")
    for k, v in list(varying_fc2.items())[:5]:
        print(f"    {k[0]} -> {k[1]}: delta_fc in {sorted(v)}")

if __name__ == "__main__":
    main()
