#!/usr/bin/env python3
"""
Check: among CF (constant-FutureFc) bad steps firing at interior positions,
how many preserve TP and fc, preserve TP but change fc, or change TP.

CUP-2 system for n=9 (and n=5 for comparison).

TP invariant from Lean:
  exp2_bit(n, j, a, b) = 1 if 2<=j and j+2<n and a==2 and b!=2, else 0
  int21_bit(n, j, a, b) = 1 if 2<=j and j+2<n and a==2 and b==1, else 0
  exp2_count = sum over j of exp2_bit(n, j, c[j], c[(j+1)%n])
  int21_count = sum over j of int21_bit(n, j, c[j], c[(j+1)%n])
  exp2_weight = sum over j of j * exp2_bit(n, j, c[j], c[(j+1)%n])
  TP = (exp2_count, int21_count, exp2_weight)
"""

from itertools import product as iterproduct
from collections import defaultdict

# ── Transition tables ──
TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
        (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
        (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
        (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
        (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
         (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,
        (1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}


def get_table(n, i):
    if i == 0:
        return TBot
    elif i == 1:
        return TLow
    elif i == n - 2:
        return THigh
    elif i == n - 1:
        return TTop
    else:
        return TMid


def all_configs(n):
    """Generate all configs: c[0],c[n-1] in {0,1}, c[1..n-2] in {0,1,2}."""
    ranges = []
    for i in range(n):
        if i == 0 or i == n - 1:
            ranges.append(range(2))
        else:
            ranges.append(range(3))
    for vals in iterproduct(*ranges):
        yield list(vals)


def fire_value(n, c, i):
    """Compute f(c[i-1], c[i], c[i+1]) for position i."""
    L = c[(i - 1) % n]
    S = c[i]
    R = c[(i + 1) % n]
    table = get_table(n, i)
    return table[(L, S, R)]


def privileged_positions(n, c):
    """Return set of privileged positions."""
    priv = set()
    for i in range(n):
        if fire_value(n, c, i) != c[i]:
            priv.add(i)
    return priv


def fc(n, c):
    return len(privileged_positions(n, c))


def move(n, c, i):
    """Fire position i, return new config."""
    c2 = list(c)
    c2[i] = fire_value(n, c, i)
    return c2


def exp2_bit(n, j, a, b):
    """1 if 2<=j and j+2<n and a==2 and b!=2, else 0."""
    if 2 <= j and j + 2 < n and a == 2 and b != 2:
        return 1
    return 0


def int21_bit(n, j, a, b):
    """1 if 2<=j and j+2<n and a==2 and b==1, else 0."""
    if 2 <= j and j + 2 < n and a == 2 and b == 1:
        return 1
    return 0


def compute_tp(n, c):
    """
    Compute TP invariant = (exp2_count, int21_count, exp2_weight).
    exp2_bit and int21_bit use c[j] and c[(j+1) % n].
    """
    exp2_count = 0
    int21_count = 0
    exp2_weight = 0
    for j in range(n):
        a = c[j]
        b = c[(j + 1) % n]
        e = exp2_bit(n, j, a, b)
        exp2_count += e
        int21_count += int21_bit(n, j, a, b)
        exp2_weight += j * e
    return (exp2_count, int21_count, exp2_weight)


def tp_le(tp1, tp2):
    """Lexicographic <=."""
    return tp1 <= tp2  # Python tuple comparison is lexicographic


def analyze(n):
    print(f"\n{'='*60}")
    print(f"  Analysis for n = {n}")
    print(f"{'='*60}")

    # Enumerate all configs, compute fc
    configs = list(all_configs(n))
    config_to_idx = {}
    for idx, c in enumerate(configs):
        config_to_idx[tuple(c)] = idx

    total = len(configs)
    fc_vals = [fc(n, c) for c in configs]
    bad_configs = [i for i in range(total) if fc_vals[i] > 0]
    good_configs = [i for i in range(total) if fc_vals[i] == 0]

    print(f"Total configs: {total}")
    print(f"Good (fc=0): {len(good_configs)}")
    print(f"Bad (fc>0):  {len(bad_configs)}")

    # Enumerate all bad steps
    bad_steps = []  # (src_idx, dst_idx, fire_pos)
    for src_idx in bad_configs:
        c = configs[src_idx]
        for i in privileged_positions(n, c):
            c2 = move(n, c, i)
            dst_idx = config_to_idx[tuple(c2)]
            if fc_vals[dst_idx] > 0:  # c' is also bad
                bad_steps.append((src_idx, dst_idx, i))

    print(f"Total bad steps: {len(bad_steps)}")

    # Compute FutureFc via fixpoint
    future_fc = list(fc_vals)
    changed = True
    iters = 0
    while changed:
        changed = False
        iters += 1
        for src, dst, pos in bad_steps:
            if future_fc[src] < future_fc[dst]:
                future_fc[src] = future_fc[dst]
                changed = True

    print(f"FutureFc fixpoint converged in {iters} iterations")

    # Interior positions: 3 <= i <= n-3
    interior_lo = 3
    interior_hi = n - 3

    if interior_hi < interior_lo:
        print(f"No interior positions for n={n} (range [{interior_lo}..{interior_hi}] is empty)")
        return

    # Check TP monotonicity on ALL bad steps
    tp_increase_count = 0
    tp_increase_examples = []
    for src, dst, pos in bad_steps:
        c = configs[src]
        c2 = configs[dst]
        tp_b = compute_tp(n, c)
        tp_a = compute_tp(n, c2)
        if tp_a > tp_b:
            tp_increase_count += 1
            if len(tp_increase_examples) < 3:
                tp_increase_examples.append((c, c2, pos, tp_b, tp_a))
    print(f"\nTP monotonicity on ALL bad steps: {tp_increase_count} increases")
    if tp_increase_examples:
        for c, c2, pos, tp_b, tp_a in tp_increase_examples:
            print(f"  fire pos={pos}: TP {tp_b} -> {tp_a}")
            print(f"    c  = {c}")
            print(f"    c' = {c2}")

    # Check TP monotonicity on CF steps only
    tp_increase_cf = 0
    for src, dst, pos in bad_steps:
        if future_fc[src] != future_fc[dst]:
            continue
        c = configs[src]
        c2 = configs[dst]
        tp_b = compute_tp(n, c)
        tp_a = compute_tp(n, c2)
        if tp_a > tp_b:
            tp_increase_cf += 1
    print(f"TP monotonicity on CF steps: {tp_increase_cf} increases")

    # Check TP monotonicity on CF interior steps only
    tp_increase_cf_interior = 0
    tp_increase_cf_interior_examples = []
    for src, dst, pos in bad_steps:
        if future_fc[src] != future_fc[dst]:
            continue
        if not (interior_lo <= pos <= interior_hi):
            continue
        c = configs[src]
        c2 = configs[dst]
        tp_b = compute_tp(n, c)
        tp_a = compute_tp(n, c2)
        if tp_a > tp_b:
            tp_increase_cf_interior += 1
            if len(tp_increase_cf_interior_examples) < 5:
                tp_increase_cf_interior_examples.append(
                    (c, c2, pos, tp_b, tp_a, fc_vals[src], fc_vals[dst], future_fc[src]))
    print(f"TP monotonicity on CF interior steps: {tp_increase_cf_interior} increases")
    if tp_increase_cf_interior_examples:
        for c, c2, pos, tp_b, tp_a, fc_b, fc_a, ffc in tp_increase_cf_interior_examples:
            print(f"  fire pos={pos}: TP {tp_b}->{tp_a}, fc {fc_b}->{fc_a}, FutureFc={ffc}")
            print(f"    c  = {c}")
            print(f"    c' = {c2}")

    # Now classify CF interior steps
    cf_interior_tp_down = 0
    cf_interior_tp_same_fc_same = 0
    cf_interior_tp_same_fc_changed = 0
    cf_interior_tp_up = 0

    cf_boundary_count = 0
    cf_total = 0

    gap_examples = []

    for src, dst, pos in bad_steps:
        if future_fc[src] != future_fc[dst]:
            continue
        cf_total += 1

        if not (interior_lo <= pos <= interior_hi):
            cf_boundary_count += 1
            continue

        c = configs[src]
        c2 = configs[dst]
        tp_before = compute_tp(n, c)
        tp_after = compute_tp(n, c2)
        fc_before = fc_vals[src]
        fc_after = fc_vals[dst]

        if tp_after < tp_before:
            cf_interior_tp_down += 1
        elif tp_after == tp_before:
            if fc_after == fc_before:
                cf_interior_tp_same_fc_same += 1
            else:
                cf_interior_tp_same_fc_changed += 1
                if len(gap_examples) < 10:
                    gap_examples.append((c, c2, pos, fc_before, fc_after,
                                         future_fc[src], tp_before, tp_after))
        else:
            cf_interior_tp_up += 1

    cf_interior_total = cf_interior_tp_down + cf_interior_tp_same_fc_same + cf_interior_tp_same_fc_changed + cf_interior_tp_up

    print(f"\nCF steps total: {cf_total}")
    print(f"  CF boundary (pos not in [{interior_lo}..{interior_hi}]): {cf_boundary_count}")
    print(f"  CF interior (pos in [{interior_lo}..{interior_hi}]):     {cf_interior_total}")
    print(f"    TP decreased:              {cf_interior_tp_down}")
    print(f"    TP preserved, fc preserved: {cf_interior_tp_same_fc_same}")
    print(f"    TP preserved, fc CHANGED:   {cf_interior_tp_same_fc_changed}  *** GAP ***")
    print(f"    TP INCREASED:               {cf_interior_tp_up}")

    if gap_examples:
        print(f"\n  Gap examples (first {len(gap_examples)}):")
        for c, c2, pos, fc_b, fc_a, ffc, tp_b, tp_a in gap_examples:
            print(f"    fire pos={pos}: fc {fc_b}->{fc_a}, FutureFc={ffc}, TP {tp_b}->{tp_a}")
            print(f"      c  = {c}")
            print(f"      c' = {c2}")

    # Distribution of FutureFc
    ffc_dist = defaultdict(int)
    for i in bad_configs:
        ffc_dist[future_fc[i]] += 1
    print(f"\nFutureFc distribution among bad configs:")
    for k in sorted(ffc_dist.keys()):
        print(f"  FutureFc={k}: {ffc_dist[k]} configs")


# Verify the Lean counterexample first
print("=== Verifying Lean counterexample ===")
# Config [0, 2, 1, 1, 0] at n=5, fire pos 2 (TMid)
n = 5
c_ce = [0, 2, 1, 1, 0]
tp_before = compute_tp(n, c_ce)
c_after = move(n, c_ce, 2)
tp_after = compute_tp(n, c_after)
print(f"  n=5, c={c_ce}, fire pos=2")
print(f"  c' = {c_after}")
print(f"  TP before = {tp_before}")
print(f"  TP after  = {tp_after}")
print(f"  TP increased? {tp_after > tp_before}")
print()

# Run for n=5 and n=9
for n_val in [5, 9]:
    analyze(n_val)
