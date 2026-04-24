#!/usr/bin/env python3
"""
Deep investigation of PhiFull influence depth.

Key insight from ra_influence_depth.py: achiever depth is always 0.
This means PhiFull-achieving configs only differ from the start in
boundary positions. So the question is: what boundary fc values are
TP-reachable from a given config?

Hypothesis: PhiFull(c) depends on the boundary 6-tuple + some simple
function of the interior (like fc contribution from the interior, or
the number of deep copy pairs).

Let's figure out exactly what that function is.
"""

import sys, time
from itertools import product as cartesian
from collections import defaultdict

sys.stdout.reconfigure(line_buffering=True)

# ── CUP-2 tables (same as ra_influence_depth.py) ────────────────────────
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

# ── Interior feature analysis ────────────────────────────────────────────

def interior_fc(c, n):
    """fc contribution from INTERIOR pairs only (pairs entirely within [3..n-4])."""
    count = 0
    for j in range(3, n-4):
        if c[j] != c[j+1]:
            count += 1
    return count

def deep_copy_pairs(c, n):
    """Count positions j in [3..n-4] where c[j] == c[j-1] or c[j] == c[j+1]."""
    count = 0
    for j in range(3, n-4):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            count += 1
    return count

def no_deep_copy_pair(c, n):
    """True if no adjacent equal pair in the deep interior [4..n-4]."""
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            return False
    return True

def interior_signature(c, n):
    """Full interior content: c[3..n-4]."""
    return c[3:n-3]

def boundary_8tuple(c, n):
    """Extended boundary: first 4 and last 4."""
    return c[:4] + c[n-4:]

def boundary_6tuple(c, n):
    return c[:3] + c[n-3:]

def main():
    print("=" * 70)
    print("DEEP PhiFull INFLUENCE ANALYSIS")
    print("=" * 70)

    for n in [9, 10, 11, 12]:
        t0 = time.time()
        print(f"\n{'─'*60}")
        print(f"n = {n}")
        print(f"{'─'*60}")

        phi, good, tp_edges = compute_phi_full(n)
        bad = [c for c in phi if c not in good and phi[c] is not None]
        print(f"  {len(bad)} bad configs, elapsed {time.time()-t0:.1f}s")

        # Test 1: Does PhiFull depend only on (boundary_6, interior_fc)?
        print(f"\n  Test: PhiFull = f(boundary_6, interior_fc)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), interior_fc(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")
            worst = max(amb, key=lambda k: max(amb[k]) - min(amb[k]))
            print(f"    Worst: {worst} -> {sorted(amb[worst])}")

        # Test 2: Does PhiFull depend on (boundary_6, #deep_copy_pairs)?
        print(f"\n  Test: PhiFull = f(boundary_6, #DCP)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), deep_copy_pairs(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        # Test 3: Does PhiFull depend on (boundary_6, noDeepCopyPair)?
        print(f"\n  Test: PhiFull = f(boundary_6, noDeepCopyPair)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), no_deep_copy_pair(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")
            # For the ambiguous ones, show what distinguishes them
            for k, vals in sorted(amb.items())[:3]:
                b6, ndcp = k
                matching = [c for c in bad if boundary_6tuple(c, n) == b6 and no_deep_copy_pair(c, n) == ndcp]
                by_phi = defaultdict(list)
                for c in matching:
                    by_phi[phi[c]].append(c)
                print(f"    Example: b6={b6}, ndcp={ndcp}")
                for pv, cfgs in sorted(by_phi.items()):
                    print(f"      PhiFull={pv}: {len(cfgs)} configs, e.g. {cfgs[0]}")

        # Test 4: Does PhiFull depend on (boundary_6, tp_invariant)?
        print(f"\n  Test: PhiFull = f(boundary_6, tp_invariant)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), tp_invariant(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        # Test 5: fc itself — what's the relationship between fc and PhiFull?
        print(f"\n  Test: PhiFull = f(fc)?")
        groups = defaultdict(set)
        for c in bad:
            groups[fc(c, n)].add(phi[c])
        for fv in sorted(groups):
            print(f"    fc={fv}: PhiFull in {sorted(groups[fv])}")

        # Test 6: Does PhiFull depend on (boundary_6, fc)?
        print(f"\n  Test: PhiFull = f(boundary_6, fc)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), fc(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        # Test 7: What is the simplest feature X such that (boundary_6, X) determines PhiFull?
        # Try: X = has_any_copy_pair (whether c[j]==c[j+1] anywhere in deep interior)
        print(f"\n  Test: PhiFull = f(boundary_6, has_interior_copy_pair)?")
        groups = defaultdict(set)
        for c in bad:
            has_cp = any(c[j] == c[j+1] for j in range(3, n-4))
            key = (boundary_6tuple(c, n), has_cp)
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        # Test 8: (boundary_8, has_interior_copy_pair)
        print(f"\n  Test: PhiFull = f(boundary_8, has_interior_copy_pair)?")
        groups = defaultdict(set)
        for c in bad:
            has_cp = any(c[j] == c[j+1] for j in range(4, n-5))
            key = (boundary_8tuple(c, n), has_cp)
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        # TEST 9: The key question: is PhiFull determined by (boundary_6, fc, noDeepCopyPair)?
        print(f"\n  Test: PhiFull = f(boundary_6, fc, noDeepCopyPair)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), fc(c, n), no_deep_copy_pair(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        # TEST 10: (boundary_6, fc, tp_invariant)?
        print(f"\n  Test: PhiFull = f(boundary_6, fc, tp_invariant)?")
        groups = defaultdict(set)
        for c in bad:
            key = (boundary_6tuple(c, n), fc(c, n), tp_invariant(c, n))
            groups[key].add(phi[c])
        amb = {k: v for k, v in groups.items() if len(v) > 1}
        if not amb:
            print(f"    YES — {len(groups)} groups, all unique PhiFull")
        else:
            print(f"    NO — {len(amb)} ambiguous groups")

        elapsed = time.time() - t0
        print(f"\n  Total elapsed: {elapsed:.1f}s")

if __name__ == "__main__":
    main()
