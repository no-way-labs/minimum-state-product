#!/usr/bin/env python3
"""
PhiFull = f(boundary_6, fc) — determine the exact formula.

From ra_influence_deep.py: PhiFull is exactly determined by the pair
(boundary_6tuple, fc) at n=9,10,11,12. This script:
1. Extracts the full lookup table (boundary_6, fc) -> PhiFull
2. Checks n-independence: is the table the same at every n?
3. Finds the formula: PhiFull = fc + delta where delta depends only on boundary_6
4. Verifies at n=13 for confidence
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

    return phi, good

def boundary_6(c, n):
    return c[:3] + c[n-3:]

# ── Main: extract and compare lookup tables ──────────────────────────────
def main():
    print("=" * 70)
    print("PhiFull = f(boundary_6, fc) — FORMULA EXTRACTION")
    print("=" * 70)

    # For each n, build the table (b6, fc_val) -> PhiFull
    tables = {}
    for n in [9, 10, 11, 12, 13]:
        t0 = time.time()
        print(f"\nn={n}...", end=" ", flush=True)
        phi, good = compute_phi_full(n)
        bad = [c for c in phi if c not in good]

        table = {}
        for c in bad:
            b6 = boundary_6(c, n)
            fv = fc(c, n)
            pv = phi[c]
            key = (b6, fv)
            if key in table:
                assert table[key] == pv, f"CONFLICT at n={n}: {key} -> {table[key]} vs {pv}"
            table[key] = pv

        tables[n] = table
        elapsed = time.time() - t0
        print(f"{len(table)} entries, {elapsed:.1f}s")

    # Compare tables across n values
    print(f"\n{'─'*60}")
    print("TABLE COMPARISON")
    print(f"{'─'*60}")

    # The tables have different (b6, fc) keys because fc range differs.
    # Common keys are those where the boundary configs exist at all n
    # and the fc value is achievable at all n.
    n_vals = sorted(tables.keys())
    for i in range(len(n_vals) - 1):
        n1, n2 = n_vals[i], n_vals[i+1]
        t1, t2 = tables[n1], tables[n2]
        common = set(t1.keys()) & set(t2.keys())
        agree = sum(1 for k in common if t1[k] == t2[k])
        disagree = [(k, t1[k], t2[k]) for k in common if t1[k] != t2[k]]
        print(f"  n={n1} vs n={n2}: {len(common)} common keys, {agree} agree, {len(disagree)} disagree")
        if disagree:
            for k, v1, v2 in disagree[:5]:
                print(f"    DISAGREE: {k} -> {v1} vs {v2}")

    # Check if PhiFull = fc + delta(b6)
    print(f"\n{'─'*60}")
    print("PhiFull = fc + delta(b6)?")
    print(f"{'─'*60}")

    for n in n_vals:
        delta_table = {}
        consistent = True
        for (b6, fv), pv in tables[n].items():
            d = pv - fv
            if b6 in delta_table:
                if delta_table[b6] != d:
                    consistent = False
                    break
            delta_table[b6] = d

        if consistent:
            print(f"  n={n}: YES, delta depends only on b6 ({len(delta_table)} entries)")
            # Show the delta table
            delta_vals = sorted(set(delta_table.values()))
            print(f"    Delta values: {delta_vals}")
            for dv in delta_vals:
                count = sum(1 for v in delta_table.values() if v == dv)
                examples = [b6 for b6, v in delta_table.items() if v == dv][:3]
                print(f"    delta={dv}: {count} boundary tuples, e.g. {examples}")
        else:
            print(f"  n={n}: NO, delta is not a function of b6 alone")
            # Try: delta depends on (b6, fc range)
            # Show examples where delta varies for same b6
            delta_by_b6 = defaultdict(set)
            for (b6, fv), pv in tables[n].items():
                delta_by_b6[b6].add(pv - fv)
            varying = {b6: deltas for b6, deltas in delta_by_b6.items() if len(deltas) > 1}
            print(f"    {len(varying)} boundary tuples have varying delta")
            for b6 in list(varying)[:5]:
                entries = [(fv, pv) for (b, fv), pv in tables[n].items() if b == b6]
                entries.sort()
                print(f"    b6={b6}:")
                for fv, pv in entries:
                    print(f"      fc={fv} -> PhiFull={pv} (delta={pv-fv})")

    # Check if delta(b6) depends on whether b6 has "adjacent equal" or fc contribution
    print(f"\n{'─'*60}")
    print("DELTA PATTERN ANALYSIS")
    print(f"{'─'*60}")

    n = 11  # use n=11 as reference
    for (b6, fv), pv in sorted(tables[n].items()):
        delta = pv - fv

    # For each b6, compute boundary fc contribution and delta
    b6_info = {}
    for (b6, fv), pv in tables[n].items():
        if b6 not in b6_info:
            # boundary fc contribution: count adjacent-different pairs in boundary region
            # Pairs: (b6[0],b6[1]), (b6[1],b6[2]), and (b6[3],b6[4]), (b6[4],b6[5])
            # Plus the cross-boundary pairs: (b6[2], ??) and (??, b6[3])
            # where ?? depends on the interior
            b_fc = 0
            # Actually: the "boundary fc contribution" at the boundary positions
            # Position 0-1 pair: b6[0] vs b6[1]
            # Position 1-2 pair: b6[1] vs b6[2]
            # Position (n-3)-(n-2) pair: b6[3] vs b6[4]
            # Position (n-2)-(n-1) pair: b6[4] vs b6[5]
            # Position (n-1)-0 pair (wrap): b6[5] vs b6[0]
            b_fc_fixed = 0
            if b6[0] != b6[1]: b_fc_fixed += 1
            if b6[1] != b6[2]: b_fc_fixed += 1
            if b6[3] != b6[4]: b_fc_fixed += 1
            if b6[4] != b6[5]: b_fc_fixed += 1
            if b6[5] != b6[0]: b_fc_fixed += 1  # wrap-around
            b6_info[b6] = {'b_fc_fixed': b_fc_fixed, 'deltas': defaultdict(set)}
        b6_info[b6]['deltas'][fv].add(pv - fv)

    # Now check: is delta = f(b_fc_fixed)?
    print(f"\n  n={n}: delta vs b_fc_fixed")
    delta_by_bfc = defaultdict(set)
    for b6, info in b6_info.items():
        for fv, deltas in info['deltas'].items():
            for d in deltas:
                delta_by_bfc[info['b_fc_fixed']].add(d)
    for bfc in sorted(delta_by_bfc):
        print(f"    b_fc_fixed={bfc}: delta in {sorted(delta_by_bfc[bfc])}")

    # Check: is there a formula PhiFull = fc + 1 when fc < n, PhiFull = n when fc = n?
    print(f"\n{'─'*60}")
    print("PhiFull EXACT VALUES")
    print(f"{'─'*60}")
    for n in n_vals:
        print(f"\n  n={n}:")
        for (b6, fv), pv in sorted(tables[n].items()):
            if pv != fv:
                delta = pv - fv
                print(f"    b6={b6}, fc={fv}, PhiFull={pv}, delta={delta}")
                # Only print first 20 non-trivial entries
                if sum(1 for (b, f), p in tables[n].items() if p != f and (b, f) <= (b6, fv)) > 20:
                    remaining = sum(1 for (b, f), p in tables[n].items() if p != f and (b, f) > (b6, fv))
                    print(f"    ... {remaining} more non-trivial entries")
                    break

if __name__ == "__main__":
    main()
