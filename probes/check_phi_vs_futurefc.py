#!/usr/bin/env python3
"""Compare the TP-based potential phi with FutureFc.
If they're equal, the 617-edge DAG is valid for FutureFc-preserving steps.
If they differ, there's a fundamental issue in the Lean formalization."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def fire(ms, fs, c, n, i):
    L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
    out = fs[i](L, S, R)
    if out == S:
        return None
    lst = list(c); lst[i] = out
    return tuple(lst)

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)
def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)
def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)
def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)

for n in range(7, 13):
    ms, fs = build_system(n)
    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Build good set
    good_set = set()
    cur = list(tuple([0]*n))
    good_set.add(tuple(cur))
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(ms, fs, tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good_set.add(tuple(cur))

    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Build bad-step adjacency
    adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)

    # Compute FutureFc (max reachable fc via bad steps)
    ff = {c: fc(c, n) for c in bad_list}
    for _ in range(len(bad_list) + 1):
        changed = False
        for c in bad_list:
            for s in adj[c]:
                if ff[s] > ff[c]:
                    ff[c] = ff[s]
                    changed = True
        if not changed:
            break

    # Compute TP-based potential
    # TP edges: bad steps preserving exp2_count, int_21, exp2_weight
    tp_fwd = defaultdict(list)
    for c in bad_list:
        e2c = exp2_count(c, n)
        i21c = int_21(c, n)
        ewc = exp2_weight(c, n)
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is not None and new in bad_set:
                e2s = exp2_count(new, n)
                i21s = int_21(new, n)
                ews = exp2_weight(new, n)
                if e2s == e2c and i21s == i21c and ews == ewc:
                    dfc = fc(new, n) - fc(c, n)
                    tp_fwd[c].append((new, dfc))

    # g = max gain in fc achievable via TP steps
    g = {c: 0 for c in bad_list}
    for _ in range(2 * n + 5):
        changed = False
        for c in bad_list:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]:
                    g[c] = new_g
                    changed = True
        if not changed:
            break

    phi = {c: fc(c, n) + g[c] for c in bad_list}

    # Compare
    match = sum(1 for c in bad_list if phi[c] == ff[c])
    mismatch = sum(1 for c in bad_list if phi[c] != ff[c])

    # Detailed mismatch analysis
    mismatch_details = []
    for c in bad_list:
        if phi[c] != ff[c]:
            mismatch_details.append((c, phi[c], ff[c]))

    print(f"n={n}: {len(bad_list)} bad, match={match}, mismatch={mismatch}")
    if mismatch > 0:
        print(f"  phi vs ff: {sorted(set((d[1], d[2]) for d in mismatch_details[:20]))[:10]}")
        # Check if phi <= ff always
        phi_le_ff = all(phi[c] <= ff[c] for c in bad_list)
        phi_ge_ff = all(phi[c] >= ff[c] for c in bad_list)
        print(f"  phi <= ff always: {phi_le_ff}, phi >= ff always: {phi_ge_ff}")

    # Now check: CF-boundary transitions under BOTH definitions
    cf_ff_bnd_edges = set()
    cf_phi_bnd_edges = set()
    for c in bad_list:
        for i in range(n):
            new = fire(ms, fs, c, n, i)
            if new is None or new not in bad_set:
                continue
            if not (i <= 2 or i >= n-3):
                continue
            s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            s6s = (new[0], new[1], new[2], new[n-3], new[n-2], new[n-1])
            if s6c == s6s:
                continue
            if ff[new] == ff[c]:
                cf_ff_bnd_edges.add((s6c, s6s))
            if phi[new] == phi[c]:
                cf_phi_bnd_edges.add((s6c, s6s))

    only_ff = cf_ff_bnd_edges - cf_phi_bnd_edges
    only_phi = cf_phi_bnd_edges - cf_ff_bnd_edges
    common = cf_ff_bnd_edges & cf_phi_bnd_edges
    print(f"  CF boundary 6-tuple edges: ff={len(cf_ff_bnd_edges)}, phi={len(cf_phi_bnd_edges)}")
    print(f"  common={len(common)}, only-ff={len(only_ff)}, only-phi={len(only_phi)}")
    if only_ff:
        print(f"  Only in ff-CF: {sorted(only_ff)[:5]}")
    print()
