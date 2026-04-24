#!/usr/bin/env python3
"""Precise FutureFc computation using iterative fixed-point.
Then check: does every CF step preserve or increase fc?"""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def get_ms(n):
    ms = [3]*n; ms[0] = 2; ms[n-1] = 2; return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def frontierBitVal(a, b):
    return 0 if a == b else 1

def fc(config, n):
    return sum(frontierBitVal(config[j], config[(j+1)%n]) for j in range(n))

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    return tuple(list(config[:i]) + [new_S] + list(config[i+1:]))

def build_good_set(n):
    """Build good cycle by three-phase wavefront."""
    config = tuple([0] * n)
    good = {config}
    cur = list(config)
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good.add(tuple(cur))
    return good

def compute_future_fc_precise(n, good_set):
    """Compute FutureFc using Bellman-Ford style fixed-point on the SCC DAG."""
    ms = get_ms(n)
    from itertools import product as iproduct
    all_configs = list(iproduct(*[range(m) for m in ms]))
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)

    # Build adjacency
    adj = {}
    for c in bad_configs:
        adj[c] = []
        for i in range(n):
            new = fire(c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)

    # Initialize FutureFc = fc for each config
    ff = {c: fc(c, n) for c in bad_configs}

    # Iterate until convergence
    changed = True
    iterations = 0
    while changed:
        changed = False
        iterations += 1
        for c in bad_configs:
            for s in adj[c]:
                if ff[s] > ff[c]:
                    ff[c] = ff[s]
                    changed = True
        if iterations > len(bad_configs):
            print("  WARNING: too many iterations, possible bug")
            break

    return ff

for n in [5, 6, 7, 8, 9]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    ms = get_ms(n)
    good_set = build_good_set(n)
    bad_set = set()
    from itertools import product as iproduct
    for c in iproduct(*[range(m) for m in ms]):
        if c not in good_set:
            bad_set.add(c)
    print(f"  Bad configs: {len(bad_set)}, Good: {len(good_set)}")

    ff = compute_future_fc_precise(n, good_set)

    # Distribution of FutureFc
    from collections import Counter
    ff_dist = Counter(ff.values())
    print(f"  FutureFc distribution: {sorted(ff_dist.items())}")

    # Check CF steps (FutureFc preserved) for fc direction
    fc_dec_cf = 0
    fc_inc_cf = 0
    fc_eq_cf = 0
    total_cf = 0
    total_bad_steps = 0

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            total_bad_steps += 1
            if ff[new] == ff[c]:  # CF step
                total_cf += 1
                old_fc = fc(c, n)
                new_fc = fc(new, n)
                if new_fc < old_fc:
                    fc_dec_cf += 1
                elif new_fc > old_fc:
                    fc_inc_cf += 1
                else:
                    fc_eq_cf += 1

    print(f"  Bad steps: {total_bad_steps}, CF steps: {total_cf}")
    print(f"  CF fc-decrease: {fc_dec_cf}, fc-preserved: {fc_eq_cf}, fc-increase: {fc_inc_cf}")

    # Key check: among CF steps with fc-decrease, what's the nonneg measure change?
    if fc_dec_cf > 0:
        print(f"\n  Analyzing CF fc-decrease steps:")
        examples = 0
        for c in bad_set:
            for i in range(n):
                new = fire(c, n, i)
                if new is None or new not in bad_set:
                    continue
                if ff[new] != ff[c]:
                    continue
                old_fc = fc(c, n)
                new_fc = fc(new, n)
                if new_fc >= old_fc:
                    continue
                # This is a CF fc-decrease step
                examples += 1
                if examples <= 5:
                    print(f"    {c} fire {i} -> {new}")
                    print(f"      fc: {old_fc}->{new_fc}, FF={ff[c]}")
                    # What do the neighbors look like?
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    new_S = get_trans(n, i, L, S, R)
                    print(f"      (L,S,R)=({L},{S},{R})->({L},{new_S},{R})")
