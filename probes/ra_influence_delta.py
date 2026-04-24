#!/usr/bin/env python3
"""
Characterize the 27 boundary 6-tuples with delta=1.

PhiFull(c) = fc(c) + delta(boundary_6(c))
where delta is 0 or 1, depending ONLY on the boundary 6-tuple.
Delta=1 for exactly 27 of the 324 boundary 6-tuples.

This script identifies the pattern and proves the mechanism.
"""

import sys
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

def compute_phi_full(n):
    configs = all_configs(n)
    good = build_good_set(n)
    bad = [c for c in configs if c not in good]
    bad_set = set(bad)
    phi = {c: (0 if c in good else fc(c, n)) for c in configs}
    tp_edges = defaultdict(list)
    for c in bad:
        tp_c = tp_invariant(c, n)
        for i in range(n):
            if not is_privileged(n, c, i): continue
            d = fire(n, c, i)
            if d not in bad_set: continue
            if tp_invariant(d, n) == tp_c:
                tp_edges[c].append(d)
    for _ in range(3*n):
        changed = False
        for c in bad:
            old = phi[c]
            best = fc(c, n)
            for d in tp_edges[c]:
                if phi[d] > best: best = phi[d]
            if best > old: phi[c] = best; changed = True
        if not changed: break
    return phi, good, tp_edges

def boundary_6(c, n):
    return c[:3] + c[n-3:]

def main():
    print("=" * 70)
    print("DELTA=1 BOUNDARY 6-TUPLE CHARACTERIZATION")
    print("=" * 70)

    n = 11  # use n=11 as reference
    phi, good, tp_edges = compute_phi_full(n)
    bad = [c for c in phi if c not in good]

    # Build delta table
    delta_table = {}
    for c in bad:
        b6 = boundary_6(c, n)
        fv = fc(c, n)
        pv = phi[c]
        delta = pv - fv
        if b6 in delta_table:
            assert delta_table[b6] == delta
        delta_table[b6] = delta

    delta1 = sorted(b6 for b6, d in delta_table.items() if d == 1)
    delta0 = sorted(b6 for b6, d in delta_table.items() if d == 0)

    print(f"\nAll 27 boundary 6-tuples with delta=1:")
    print(f"  Format: (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])")
    for b6 in delta1:
        print(f"  {b6}")

    # Pattern analysis
    print(f"\n{'─'*60}")
    print("PATTERN ANALYSIS")
    print(f"{'─'*60}")

    # c[0] values in delta=1
    c0_vals = set(b6[0] for b6 in delta1)
    c1_vals = set(b6[1] for b6 in delta1)
    c2_vals = set(b6[2] for b6 in delta1)
    cn3_vals = set(b6[3] for b6 in delta1)
    cn2_vals = set(b6[4] for b6 in delta1)
    cn1_vals = set(b6[5] for b6 in delta1)

    print(f"  c[0] values: {sorted(c0_vals)}")
    print(f"  c[1] values: {sorted(c1_vals)}")
    print(f"  c[2] values: {sorted(c2_vals)}")
    print(f"  c[n-3] values: {sorted(cn3_vals)}")
    print(f"  c[n-2] values: {sorted(cn2_vals)}")
    print(f"  c[n-1] values: {sorted(cn1_vals)}")

    # Check: is delta=1 iff c[0]=1 and c[1]=2 and c[2]=0?
    left_pattern = all(b6[0] == 1 and b6[1] == 2 and b6[2] == 0 for b6 in delta1)
    print(f"\n  All delta=1 have c[0]=1, c[1]=2, c[2]=0? {left_pattern}")

    # What about the right side?
    right_vals = sorted(set((b6[3], b6[4], b6[5]) for b6 in delta1))
    print(f"  Right side (c[n-3], c[n-2], c[n-1]) values for delta=1: {right_vals}")

    # Check: c[n-1] always = 1?
    cn1_check = all(b6[5] == 1 for b6 in delta1)
    print(f"  c[n-1]=1 for all delta=1? {cn1_check}")

    # So delta=1 iff c[0]=1 and c[1]=2 and c[2]=0 and c[n-1]=1 and (c[n-3], c[n-2]) arbitrary?
    # c[n-3] in {0,1,2} and c[n-2] in {0,1,2} => 9 combos. With above left = 9 right = 3*3 = 9 -> 9? No, there are 27.
    # Wait: c[n-3] in {0,1,2}, c[n-2] in {0,1,2} -> 9 combos.
    # But delta1 has 27 entries and left has (1,2,0), right has 27/1 = 27 right-side patterns?
    # Actually there's only 1 left pattern and 27 entries, so right side has 27 patterns.
    # But c[n-3] has 3 vals, c[n-2] has 3 vals, c[n-1] has 1 val -> 9 combos. That's 9, not 27.
    # Let me recount.
    print(f"\n  Number of delta=1 tuples: {len(delta1)}")
    # Group by left side
    by_left = defaultdict(list)
    for b6 in delta1:
        by_left[(b6[0], b6[1], b6[2])].append((b6[3], b6[4], b6[5]))
    for left, rights in sorted(by_left.items()):
        print(f"  Left {left}: {len(rights)} right patterns = {sorted(rights)}")

    # Hmm, c[n-1] might not always be 1. Let me double check.
    print(f"\n  Explicit check of c[n-1]:")
    for b6 in delta1:
        if b6[5] != 1:
            print(f"    EXCEPTION: {b6}")

    # Check if the condition is simply c[0]=1 and c[n-1]=1
    check_01 = all(b6[0] == 1 and b6[5] == 1 for b6 in delta1)
    print(f"\n  All delta=1 have c[0]=1, c[n-1]=1? {check_01}")

    # How about: delta=1 iff c[0]=1, c[1]=2, c[2]=0, c[n-1]=1?
    condition = lambda b6: b6[0] == 1 and b6[1] == 2 and b6[2] == 0 and b6[5] == 1
    predicted_delta1 = sorted(b6 for b6 in delta_table if condition(b6))
    print(f"\n  Predicted by c[0]=1,c[1]=2,c[2]=0,c[n-1]=1: {len(predicted_delta1)} tuples")
    print(f"  Actual: {len(delta1)} tuples")
    if set(predicted_delta1) == set(delta1):
        print(f"  MATCH!")
    else:
        extra = set(predicted_delta1) - set(delta1)
        missing = set(delta1) - set(predicted_delta1)
        print(f"  Extra: {extra}")
        print(f"  Missing: {missing}")

    # The mechanism: what TP-preserving move creates the +1 fc?
    print(f"\n{'─'*60}")
    print("MECHANISM ANALYSIS")
    print(f"{'─'*60}")
    print("For configs with delta=1, find the TP-reachable config with fc+1:")

    # Find a config with delta=1 and trace the path
    delta1_configs = [c for c in bad if delta_table.get(boundary_6(c, n)) == 1]
    # Sort by fc to find simplest examples
    delta1_configs.sort(key=lambda c: fc(c, n))

    for c in delta1_configs[:5]:
        fv = fc(c, n)
        pv = phi[c]
        print(f"\n  c = {c}")
        print(f"  fc = {fv}, PhiFull = {pv}")
        print(f"  boundary = {boundary_6(c, n)}")

        # Find the one-step TP neighbor with higher fc
        for d in tp_edges[c]:
            fd = fc(d, n)
            if fd > fv:
                print(f"  -> d = {d}")
                print(f"     fc(d) = {fd}")
                # Which position changed?
                diffs = [j for j in range(n) if c[j] != d[j]]
                print(f"     Changed positions: {diffs}")
                for j in diffs:
                    print(f"       pos {j}: {c[j]} -> {d[j]}")
                break

    # Understand the global pattern
    print(f"\n{'─'*60}")
    print("WHAT POSITION FIRES TO GET +1 FC?")
    print(f"{'─'*60}")

    fire_pos_counts = defaultdict(int)
    for c in delta1_configs:
        fv = fc(c, n)
        for d in tp_edges[c]:
            if fc(d, n) > fv:
                diffs = [j for j in range(n) if c[j] != d[j]]
                for j in diffs:
                    fire_pos_counts[j] += 1
                break

    print(f"  Fire position distribution: {dict(sorted(fire_pos_counts.items()))}")

    # Check: is it always position 2 (or position n-3)?
    # i.e., the boundary-adjacent position
    print(f"\n  Is the fired position always boundary-adjacent (pos 2 or n-3)?")
    all_ba = all(
        any(j in {2, n-3} for j in
            [j2 for j2 in range(n) if c[j2] != d[j2]])
        for c in delta1_configs
        for d in [next((d for d in tp_edges[c] if fc(d, n) > fc(c, n)), None)]
        if d is not None
    )
    print(f"  {all_ba}")

    # Verify formula: delta = 1 iff c[0]=1 and c[1]=2 and c[2]=0 and c[n-1]=1
    # across all n
    print(f"\n{'─'*60}")
    print("CROSS-n FORMULA VERIFICATION")
    print(f"{'─'*60}")

    for nv in [9, 10, 11, 12, 13]:
        phi_n, good_n, _ = compute_phi_full(nv)
        bad_n = [c for c in phi_n if c not in good_n]

        # Check formula
        correct = 0
        wrong = 0
        for c in bad_n:
            b6 = boundary_6(c, nv)
            predicted = 1 if (b6[0] == 1 and b6[1] == 2 and b6[2] == 0 and b6[5] == 1) else 0
            actual_delta = phi_n[c] - fc(c, nv)
            if predicted == actual_delta:
                correct += 1
            else:
                wrong += 1
                if wrong <= 3:
                    print(f"  n={nv} WRONG: c={c}, b6={b6}, fc={fc(c,nv)}, PhiFull={phi_n[c]}, predicted_delta={predicted}")

        print(f"  n={nv}: {correct} correct, {wrong} wrong")

if __name__ == "__main__":
    main()
